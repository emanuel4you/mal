require! LiveScript

require! 'prelude-ls': {map, fold}
require! './builtins.ls': {DO, NIL, truthy, is-seq}
require! './printer.ls': {pr-str}
require! './env': {create-env, bind-value}

{Lambda, MalList, MalVec, MalMap} = require './types.ls'

SPECIALS = <[ do let let* def! def fn* fn defn if or and ]>

evaluate = (env, ast) -> switch ast.type
    | \SYM => env[ast.value] or throw new Error "Undefined symbol: #{ ast.value }"
    | \LIST => new MalList map (eval-mal env), ast.value
    | \VEC => new MalVec map (eval-mal env), ast.value
    | \MAP => new MalMap [[(eval-mal env, k), (eval-mal env, ast.get(k))] for k in ast.keys()]
    | otherwise => ast

export eval-mal = (env, ast) --> while true
    return (evaluate env, ast) if ast.type isnt \LIST
    if is-macro ast
        [env, ast] = expand-macro env, ast
    else
        [form, ...args] = ast.value
        throw new Error("Empty call") unless form?
        switch form.value
            | 'def!', 'def' => return do-def env, args
            | 'fn', 'fn*' => return do-fn env, args
            | 'defn' => return do-defn env, args
            | 'or' => return do-or env, args
            | 'and' => return do-and env, args
            | 'let', 'let*' => [env, ast] = do-let env, args
            | 'do' => ast = do-do env, args
            | 'if' => ast = do-if env, args # should be macro
            | _ => 
                # Here we must be evaluating a call.
                application = evaluate env, ast
                [fn, ...args] = application.value
                if fn.type is \BUILTIN
                    return fn.fn args # Cannot thunk.
                else if fn.type is \LAMBDA
                    [env, ast] = [(fn.closure args), (wrap-do fn.body)]
                else
                    throw new Error "Tried to call non-callable: #{ pr-str fn }"

do-defn = (env, [name, ...fn-def]) -> do-def env, [name, (do-fn env, fn-def)]

is-macro = -> false

do-or = (env, exprs) ->
    return NIL unless exprs.length
    for e in exprs
        v = eval-mal env, e
        return v if truthy v
    return v

do-and = (env, [e, ...es]) ->
    combine = (a, b) -> if truthy a then (eval-mal env, b) else a
    fold combine, (eval-mal env, e), es

do-fn = (env, [names, ...bodies]) ->
    unless is-seq names
        throw new Error "Names must be a sequence, got: #{ pr-str names }"
    new Lambda env, names.value.slice(), bodies

do-if = (env, [test, when-true, when-false]:forms) ->
    unless forms.length in [2, 3]
        throw new Error "Expected 2 or 3 arguments to if, got #{ forms.length }"
    when-false ?= NIL
    ret = eval-mal env, test
    if (truthy ret) then when-true else when-false

do-def = (env, [key, value]:forms) ->
    unless forms.length is 2
        throw new Error "Expected 2 arguments to def, got #{ forms.length }"
    bind-value env, key, eval-mal env, value

wrap-do = (bodies) -> new MalList [DO].concat bodies

# Returns a new environment and a do-wrapped body.
do-let = (outer, [bindings, ...bodies]) ->
    env = create-env outer
    unless is-seq bindings
        throw new Error "Bindings must be a sequence, got: #{ pr-str bindings }"
    if bindings.value.length % 2
        throw new Error "There must be an even number of bindings"

    for i in [0 til bindings.value.length - 1 by 2]
        do-def env, [bindings.value[i], bindings.value[i + 1]]

    [env, (wrap-do bodies)]

do-do = (env, [...heads, last]) ->
    for body in heads
        ret = eval-mal env, body
    return last

