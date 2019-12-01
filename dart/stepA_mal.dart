import 'dart:io';

import 'core.dart';
import 'env.dart';
import 'printer.dart' as printer;
import 'reader.dart' as reader;
import 'types.dart';

final Env replEnv = Env();

void setupEnv(List<String> argv) {
  ns.forEach((sym, fun) => replEnv.set(sym, fun));

  replEnv.set(MalSymbol('eval'),
      MalBuiltin((List<MalType> args) => EVAL(args.single, replEnv)));

  replEnv.set(
      MalSymbol('*ARGV*'), MalList(argv.map((s) => MalString(s)).toList()));

  replEnv.set(MalSymbol('*host-language*'), MalString('dart'));

  rep('(def! not (fn* (a) (if a false true)))');
  rep("(def! load-file "
      "  (fn* (f) (eval (read-string (str \"(do \" (slurp f) \"\nnil)\")))))");
  rep("(defmacro! cond "
      "  (fn* (& xs) (if (> (count xs) 0) "
      "    (list 'if (first xs) "
      "      (if (> (count xs) 1) "
      "          (nth xs 1) "
      "          (throw \"odd number of forms to cond\")) "
      "      (cons 'cond (rest (rest xs)))))))");
}

/// Returns `true` if [ast] is a macro call.
///
/// This checks that [ast] is a list whose first element is a symbol that refers
/// to a function in the current [env] that is a macro.
bool isMacroCall(MalType ast, Env env) {
  if (ast is MalList) {
    if (ast.isNotEmpty && ast.first is MalSymbol) {
      try {
        var value = env.get(ast.first);
        if (value is MalCallable) {
          return value.isMacro;
        }
      } on NotFoundException {
        return false;
      }
    }
  }
  return false;
}

MalType macroexpand(MalType ast, Env env) {
  while (isMacroCall(ast, env)) {
    var macroSymbol = (ast as MalList).first;
    var macro = env.get(macroSymbol) as MalCallable;
    ast = macro((ast as MalList).sublist(1));
  }
  return ast;
}

MalType quasiquote(MalType ast) {
  bool isPair(MalType ast) {
    return ast is MalIterable && ast.isNotEmpty;
  }

  if (!isPair(ast)) {
    return MalList([MalSymbol("quote"), ast]);
  } else {
    var list = ast as MalIterable;
    if (list.first == MalSymbol("unquote")) {
      return list[1];
    } else if (isPair(list.first) &&
        (list.first as MalIterable).first == MalSymbol("splice-unquote")) {
      return MalList([
        MalSymbol("concat"),
        (list.first as MalIterable)[1],
        quasiquote(MalList(list.sublist(1)))
      ]);
    } else {
      return MalList([
        MalSymbol("cons"),
        quasiquote(list[0]),
        quasiquote(MalList(list.sublist(1)))
      ]);
    }
  }
}

MalType READ(String x) => reader.read_str(x);

MalType eval_ast(MalType ast, Env env) {
  if (ast is MalSymbol) {
    return env.get(ast);
  } else if (ast is MalList) {
    return MalList(ast.elements.map((x) => EVAL(x, env)).toList());
  } else if (ast is MalVector) {
    return MalVector(ast.elements.map((x) => EVAL(x, env)).toList());
  } else if (ast is MalHashMap) {
    var newMap = Map<MalType, MalType>.from(ast.value);
    for (var key in newMap.keys) {
      newMap[key] = EVAL(newMap[key], env);
    }
    return MalHashMap(newMap);
  } else {
    return ast;
  }
}

MalType EVAL(MalType ast, Env env) {
  while (true) {
    if (ast is! MalList) {
      return eval_ast(ast, env);
    } else {
      if ((ast as MalList).elements.isEmpty) {
        return ast;
      } else {
        ast = macroexpand(ast, env);
        if (ast is! MalList) return eval_ast(ast, env);
        if ((ast as MalList).isEmpty) return ast;

        var list = ast as MalList;

        if (list.elements.first is MalSymbol) {
          var symbol = list.elements.first as MalSymbol;
          var args = list.elements.sublist(1);
          if (symbol.value == "def!") {
            MalSymbol key = args.first;
            MalType value = EVAL(args[1], env);
            env.set(key, value);
            return value;
          } else if (symbol.value == "defmacro!") {
            MalSymbol key = args.first;
            MalClosure macro = EVAL(args[1], env) as MalClosure;
            macro.isMacro = true;
            env.set(key, macro);
            return macro;
          } else if (symbol.value == "let*") {
            // TODO(het): If elements.length is not even, give helpful error
            Iterable<List<MalType>> pairs(List<MalType> elements) sync* {
              for (var i = 0; i < elements.length; i += 2) {
                yield [elements[i], elements[i + 1]];
              }
            }

            var newEnv = Env(env);
            MalIterable bindings = args.first;
            for (var pair in pairs(bindings.elements)) {
              MalSymbol key = pair[0];
              MalType value = EVAL(pair[1], newEnv);
              newEnv.set(key, value);
            }
            ast = args[1];
            env = newEnv;
            continue;
          } else if (symbol.value == "do") {
            eval_ast(MalList(args.sublist(0, args.length - 1)), env);
            ast = args.last;
            continue;
          } else if (symbol.value == "if") {
            var condition = EVAL(args[0], env);
            if (condition is MalNil ||
                condition is MalBool && condition.value == false) {
              // False side of branch
              if (args.length < 3) {
                return MalNil();
              }
              ast = args[2];
              continue;
            } else {
              // True side of branch
              ast = args[1];
              continue;
            }
          } else if (symbol.value == "fn*") {
            var params = (args[0] as MalIterable)
                .elements
                .map((e) => e as MalSymbol)
                .toList();
            return MalClosure(
                params,
                args[1],
                env,
                (List<MalType> funcArgs) =>
                    EVAL(args[1], Env(env, params, funcArgs)));
          } else if (symbol.value == "quote") {
            return args.single;
          } else if (symbol.value == "quasiquote") {
            ast = quasiquote(args.first);
            continue;
          } else if (symbol.value == 'macroexpand') {
            return macroexpand(args.first, env);
          } else if (symbol.value == 'try*') {
            var body = args.first;
            if (args.length < 2) {
              ast = EVAL(body, env);
              continue;
            }
            var catchClause = args[1] as MalList;
            try {
              ast = EVAL(body, env);
            } catch (e) {
              assert((catchClause.first as MalSymbol).value == 'catch*');
              var exceptionSymbol = catchClause[1] as MalSymbol;
              var catchBody = catchClause[2];
              MalType exceptionValue;
              if (e is MalException) {
                exceptionValue = e.value;
              } else if (e is reader.ParseException) {
                exceptionValue = MalString(e.message);
              } else {
                exceptionValue = MalString(e.toString());
              }
              var newEnv = Env(env, [exceptionSymbol], [exceptionValue]);
              ast = EVAL(catchBody, newEnv);
            }
            continue;
          }
        }
        var newAst = eval_ast(ast, env) as MalList;
        var f = newAst.elements.first;
        var args = newAst.elements.sublist(1);
        if (f is MalBuiltin) {
          return f.call(args);
        } else if (f is MalClosure) {
          ast = f.ast;
          env = Env(f.env, f.params, args);
          continue;
        } else {
          throw 'bad!';
        }
      }
    }
  }
}

String PRINT(MalType x) => printer.pr_str(x);

String rep(String x) {
  return PRINT(EVAL(READ(x), replEnv));
}

const prompt = 'user> ';
main(List<String> args) {
  setupEnv(args.isEmpty ? const <String>[] : args.sublist(1));
  if (args.isNotEmpty) {
    rep("(load-file \"${args.first}\")");
    return;
  }
  rep("(println (str \"Mal [\" *host-language* \"]\"))");
  while (true) {
    stdout.write(prompt);
    var input = stdin.readLineSync();
    if (input == null) return;
    var output;
    try {
      output = rep(input);
    } on reader.ParseException catch (e) {
      stdout.writeln("Error: '${e.message}'");
      continue;
    } on NotFoundException catch (e) {
      stdout.writeln("Error: '${e.value}' not found");
      continue;
    } on MalException catch (e) {
      stdout.writeln("Error: ${printer.pr_str(e.value)}");
      continue;
    } on reader.NoInputException {
      continue;
    }
    stdout.writeln(output);
  }
}
