import LeanMal.reader
import LeanMal.printer
import LeanMal.core

universe u

def makeFn (env: Env) (args : List Types) : IO (Env × Types) := do
  if args.length < 2 then throw (IO.userError "unexpected syntax")
  else
    let p := args[0]!
    let body := args[1]!
    let params := match p with
      | Types.vecVal x => Types.listVal (toList x)
      | _ => p
    let newfn := Fun.userDefined env.increment params body
    return (env, Types.funcVal newfn)

def splitOnAmpersand (input : List String) : (List String × List String) :=
  let rec loop (acc1 : List String) (rest : List String) : (List String × List String) :=
    match rest with
    | []         => (acc1, [])  -- If no "&" found, second list is empty
    | "&" :: xs  => match xs with
      | [] => (acc1, [])  -- If "&" is the last element, second list is empty
      | y :: _ => (acc1, [y])  -- Add the next element after "&" to the second list
    | x :: xs    => loop (acc1 ++ [x]) xs  -- Accumulate elements before "&"
  loop [] input

mutual
  partial def evalTypes (env : Env) (ast : Types) : IO (Env × Types) := do
    if getDebugEval env then IO.println s!"EVAL:{pr_str true ast}"
    match ast with
    | Types.symbolVal v   => match env.get (KeyType.strKey v) with
      | some (_, vi) => return (env, vi)
      | none => throw (IO.userError s!"'{v}' not found")
    | Types.listVal el    => (evalList env el)
    | Types.vecVal el     => (evalVec env (toList el))
    | Types.dictVal el    => (evalDict env el)
    | x                   => return (env, x)

  partial def evalFunc (env: Env) (head : Types) (args : List Types) : IO (Env × Types) := do
    let (env2, fn) ← evalTypes env head
    let (_, res) ← evalFuncVal env2 fn args
    return (env, res)

  partial def evalFuncVal (env: Env) (fn: Types) (args: List Types) : IO (Env × Types) := do
    -- first execute each function argument - reduce computation
    let (newEnv, results) ← evalFuncArgs env args
    match fn with
      | Types.funcVal v      => match v with
        | Fun.builtin name => evalFnNative newEnv name results
        | Fun.userDefined fref params body =>
          let allkeys: List String := match params with
            | Types.listVal v => v.map fun x => x.toString false
            | _               => []
          let (keys, variadic) := splitOnAmpersand allkeys
          let normalArgs := results.take keys.length
          let variadicArg := results.drop keys.length
          let argVals := normalArgs ++ [Types.listVal variadicArg]
          let argsLevel := if fref.getLevel >= newEnv.getLevel then fref.getLevel + 1 else newEnv.getLevel + 1

          let argsDict := (buildDict argsLevel (keys ++ variadic) argVals)
          let merged := (newEnv.merge fref).mergeDict argsLevel argsDict

          evalTypes merged body
        | Fun.macroFn _ _ _ => throw (IO.userError "macro not implemented")
      | _ => throw (IO.userError s!"`unexpected token, expected: function`")


  partial def evalList (env: Env) (lst : List Types) : IO (Env × Types) := do
    if List.length lst == 0 then return (env, Types.listVal lst)
    else
      let head := lst[0]!
      match lst[0]! with
      | Types.symbolVal v => match v with
        | "def!" => evalDefn env (lst.drop 1)
        | "let*" => evalLet env (lst.drop 1)
        | "do" => evalDo env (lst.drop 1)
        | "if" => evalIf env (lst.drop 1)
        | "fn*" => makeFn env (lst.drop 1)
        | _ => evalFunc env head (lst.drop 1)
      | _ => evalFunc env head (lst.drop 1)

  partial def evalVec (env: Env) (elems : List Types) : IO (Env × Types) := do
    let (newEnv, results) ← evalFuncArgs env elems
    return (newEnv, Types.vecVal (listToVec results))

  partial def evalDict (env: Env) (lst : Dict) : IO (Env × Types) := do
    let (newEnv, newDict) ← evalDictInner env lst
    return (newEnv, Types.dictVal newDict)

  partial def evalDictInner (env: Env) (lst : Dict) : IO (Env × Dict) := do
    match lst with
      | Dict.empty => return (env, lst)
      | Dict.insert k _ v restDict =>
        let (newEnv, newVal) ← evalTypes env v
        let (updatedEnv, updatedDict) ← evalDictInner newEnv restDict
        let newDict := Dict.insert k 0 newVal updatedDict
        return (updatedEnv, newDict)

  partial def evalFuncArgs (env: Env) (args: List Types) : IO (Env × List Types) :=
    args.foldlM (fun (res : Env × List Types) (x : Types) => do
      let (r, acc) := res
      let (updatedenv, res) ← evalTypes r x
      return (updatedenv, acc ++ [res])
    ) (env, [])

  partial def evalDefn (env: Env) (args : List Types) : IO (Env × Types) := do
    if args.length < 2 then throw (IO.userError "def! unexpected syntax")
    else
      let key := args[0]!
      let body := args[1]!
      let (newEnv, value) ← (evalTypes env body)
      match key with
        | Types.symbolVal v =>
          let refResult := newEnv.add (KeyType.strKey v) env.getLevel value
          return (refResult, value)
        | _ => throw (IO.userError s!"def! unexpected token, expected: symbol")

  partial def evalLet (env: Env) (args : List Types) : IO (Env × Types) := do
    if args.length < 2 then throw (IO.userError "let*: unexpected syntax")
    else
      let pairs := args[0]!
      let body := args[1]!
      let newEnv ← match pairs with
      | Types.listVal v => evalLetArgs env.increment v
      | Types.vecVal v => evalLetArgs env.increment (toList v)
      | _ => throw (IO.userError s!"unexpected token type: ${pairs.toString true}, expected: list or vector")

      let (_, result) ← evalTypes newEnv body
      return (env, result)

  partial def evalLetArgs (env: Env) (args : List Types) : IO Env := do
    match args with
    | [] => return env
    | [_] => throw (IO.userError "let*: unexpected syntax")
    | x :: y :: rest =>
      match x with
      | Types.symbolVal key =>
        let (updatedEnv, value) ← evalTypes env y
        evalLetArgs (updatedEnv.add (KeyType.strKey key) env.getLevel value) rest
      | _ => throw (IO.userError "let*: unexpected syntax")

  partial def evalDo (env: Env) (args : List Types) : IO (Env × Types) := do
    -- only return last computation result
    let (newEnv, results) ← evalFuncArgs env args
    if results.length == 0 then return (newEnv, Types.Nil)
    else return (newEnv, results[results.length - 1]!)

  partial def evalIf (env: Env) (args : List Types) : IO (Env × Types) := do
    if args.length < 2 then throw (IO.userError "unexpected syntax")
    else
      let condition := args[0]!
      let thenExpr := args[1]!
      let hasElse := args.length > 2

      let (newEnv, condResp) ← evalTypes env condition
      let cond := match condResp with
      | Types.boolVal v => v
      | Types.Nil => false
      | _ => true
      if cond then evalTypes newEnv thenExpr
      else if hasElse then evalTypes newEnv args[2]!
      else return (newEnv, Types.Nil)

  partial def evalFnNative (env : Env) (name: String) (results: List Types): IO (Env × Types) := do
    match name with
    | "+" => sum env results
    | "-" => sub env results
    | "*" => mul env results
    | "/" => div env results
    | "<" => lt env results
    | "<=" => lte env results
    | ">" => gt env results
    | ">=" => gte env results
    | "=" => eq env results false
    | "prn" => prnFunc env results
    | "pr-str" => prStrFunc env results
    | "str" => strFunc env results
    | "println" => printlnFunc env results
    | "list" => return (env, Types.listVal results)
    | "count" => countFunc env results
    | _ => match results with
        | [x] => match x with
          | Types.listVal x => match name with
            | "list?" => return (env, Types.boolVal true)
            | "empty?" => return (env, Types.boolVal (x.length == 0))
            | _ => return (env, Types.boolVal false)
          | Types.vecVal x => match name with
            | "empty?" => return (env, Types.boolVal ((toList x).length == 0))
            | _ => return (env, Types.boolVal false)
          | _   => return (env, Types.boolVal false)
        | _   => throw (IO.userError s!"'{name}' not found")
end

def READ (input : String): Except String Types :=
  read_str.{u} input

def PRINT (ast : Types): String :=
  pr_str true ast

def rep (env: Env) (input : String): IO (Env × String) := do
  match READ.{u} input with
  | Except.ok result =>
    try
      let (newenv, res) ← evalTypes env result
      return (newenv, PRINT res)
    catch
      | e => return (env, s!"Error: {e}")
  | Except.error err => return (env, s!"Parsing failed: {err}")

def loadMalFns (env: Env) (fndefs: List String): IO (Env × String) := do
  fndefs.foldlM (fun (res : Env × String) fndef => do
    let (ref, msg) := res
    let (newref, newmsg) ← rep.{u} ref fndef
    return (newref, s!"{msg}¬{newmsg}")
  ) (env, "")

def fnDefs: List String := [
    "(def! not (fn* (a) (if a false true)))",
  ]

def main : IO Unit := do
  let (env0, _) ← loadMalFns.{u} (loadFnNativeAll (Env.data 0 Dict.empty)) fnDefs
  let mut env := env0
  let mut donext := true
  while donext do
    IO.print "user> "
    let stdin ← IO.getStdin
    let input ← stdin.getLine
    let value := input.trim
    if value = "exit" then
      donext := false
      IO.println "Exiting REPL."
    if value.isEmpty then
      donext := false
    else
      let (newenv, val) ← rep.{u} env value
      IO.println val
      env := newenv