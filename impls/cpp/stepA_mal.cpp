#include "MAL.h"

#include "Environment.h"
#include "ReadLine.h"
#include "Types.h"

#include <iostream>
#include <memory>

malValuePtr READ(const String& input);
String PRINT(malValuePtr ast);
static void installFunctions(malEnvPtr env);
//  Installs functions, macros and constants implemented in MAL.

static void makeArgv(malEnvPtr env, int argc, char* argv[]);
static String safeRep(const String& input, malEnvPtr env);
static malValuePtr quasiquote(malValuePtr obj);

static ReadLine s_readLine("~/.mal-history");

static malEnvPtr replEnv(new malEnv);

int main(int argc, char* argv[])
{
    String prompt = "user> ";
    String input;
    installCore(replEnv);
    installFunctions(replEnv);
    makeArgv(replEnv, argc - 2, argv + 2);
    if (argc > 1) {
        String filename = escape(argv[1]);
        safeRep(STRF("(load-file %s)", filename.c_str()), replEnv);
        return 0;
    }
    rep("(println (str \"Mal [\" *host-language* \"]\"))", replEnv);
    while (s_readLine.get(prompt, input)) {
        String out = safeRep(input, replEnv);
        if (out.length() > 0)
            std::cout << out << "\n";
    }
    return 0;
}

static String safeRep(const String& input, malEnvPtr env)
{
    try {
        return rep(input, env);
    }
    catch (malEmptyInputException&) {
        return String();
    }
    catch (malValuePtr& mv) {
        return "Error: " + mv->print(true);
    }
    catch (String& s) {
        return "Error: " + s;
    };
}

static void makeArgv(malEnvPtr env, int argc, char* argv[])
{
    malValueVec* args = new malValueVec();
    for (int i = 0; i < argc; i++) {
        args->push_back(mal::string(argv[i]));
    }
    env->set("*ARGV*", mal::list(args));
}

String rep(const String& input, malEnvPtr env)
{
    return PRINT(EVAL(READ(input), env));
}

malValuePtr READ(const String& input)
{
    return readStr(input);
}

malValuePtr EVAL(malValuePtr ast, malEnvPtr env)
{
    if (!env) {
        env = replEnv;
    }
    while (1) {

       const malEnvPtr dbgenv = env->find("DEBUG-EVAL");
       if (dbgenv && dbgenv->get("DEBUG-EVAL")->isTrue()) {
           std::cout << "EVAL: " << PRINT(ast) << "\n";
       }

        const malList* list = DYNAMIC_CAST(malList, ast);
        if (!list || (list->count() == 0)) {
            return ast->eval(env);
        }

        // From here on down we are evaluating a non-empty list.
        // First handle the special forms.
        if (const malSymbol* symbol = DYNAMIC_CAST(malSymbol, list->item(0))) {
            String special = symbol->value();
            int argCount = list->count() - 1;

            if (special == "and") {
                checkArgsAtLeast("and", 2, argCount);
                int value = 0;
                for (int i = 1; i < argCount+1; i++) {
                    if (EVAL(list->item(i), env)->isTrue()) {
                        value |= 1;
                    }
                    else {
                        value |= 2;
                    }
                }
                return value == 3 ? mal::falseValue() : mal::trueValue();
            }

            if (special == "bound?" || special == "boundp") {
                checkArgsIs(special.c_str(), 1, argCount);
                {
                    if (list->item(1)->print(true).compare("nil") == 0) {
                        return special == "bound?" ? mal::falseValue() : mal::nilValue();
                    }
                    else {
                            malEnvPtr sym = env->find(list->item(1)->print(true));
                            if(!sym) {
                                return special == "bound?" ? mal::falseValue() : mal::nilValue();
                            }
                    }
                    return mal::trueValue();
                }
            }

            if (special == "def!" || special == "setq") {
                MAL_CHECK(checkArgsAtLeast(special.c_str(), 2, argCount) % 2 == 0, "def!: missing odd number");
                int i;
                for (i = 1; i < argCount - 2; i += 2) {
                    const malSymbol* id = VALUE_CAST(malSymbol, list->item(i));
                    env->set(id->value(), EVAL(list->item(i+1), env));
                }
                const malSymbol* id = VALUE_CAST(malSymbol, list->item(i));
                return env->set(id->value(), EVAL(list->item(i+1), env));
            }

            if (special == "defmacro!") {
                checkArgsIs("defmacro!", 2, argCount);

                const malSymbol* id = VALUE_CAST(malSymbol, list->item(1));
                malValuePtr body = EVAL(list->item(2), env);
                const malLambda* lambda = VALUE_CAST(malLambda, body);
                return env->set(id->value(), mal::macro(*lambda));
            }

            if (special == "do" || special == "progn") {
                checkArgsAtLeast(special.c_str(), 1, argCount);

                for (int i = 1; i < argCount; i++) {
                    EVAL(list->item(i), env);
                }
                ast = list->item(argCount);
                continue; // TCO
            }

            if (special == "fn*" || special == "lambda") {
                checkArgsIs(special.c_str(), 2, argCount);

                const malSequence* bindings =
                    VALUE_CAST(malSequence, list->item(1));
                StringVec params;
                for (int i = 0; i < bindings->count(); i++) {
                    const malSymbol* sym =
                        VALUE_CAST(malSymbol, bindings->item(i));
                    params.push_back(sym->value());
                }

                return mal::lambda(params, list->item(2), env);
            }

            if (special == "if") {
                checkArgsBetween("if", 2, 3, argCount);

                bool isTrue = EVAL(list->item(1), env)->isTrue();
                if (!isTrue && (argCount == 2)) {
                    return mal::nilValue();
                }
                ast = list->item(isTrue ? 2 : 3);
                continue; // TCO
            }

            if (special == "let*") {
                checkArgsIs("let*", 2, argCount);
                const malSequence* bindings =
                    VALUE_CAST(malSequence, list->item(1));
                int count = checkArgsEven("let*", bindings->count());
                malEnvPtr inner(new malEnv(env));
                for (int i = 0; i < count; i += 2) {
                    const malSymbol* var =
                        VALUE_CAST(malSymbol, bindings->item(i));
                    inner->set(var->value(), EVAL(bindings->item(i+1), inner));
                }
                ast = list->item(2);
                env = inner;
                continue; // TCO
            }

            if (special == "minus?" || special == "minusp" ) {
                checkArgsIs(special.c_str(), 1, argCount);
                if (EVAL(list->item(1), env)->type() == MALTYPE::REAL) {
                    malDouble* val = VALUE_CAST(malDouble, EVAL(list->item(1), env));
                    if (special == "minus?") {
                        return mal::boolean(val->value() < 0.0);
                    }
                    else {
                        return val->value() < 0 ? mal::trueValue() : mal::nilValue();
                    }
                }
                else if (EVAL(list->item(1), env)->type() == MALTYPE::INT) {
                    malInteger* val = VALUE_CAST(malInteger, EVAL(list->item(1), env));
                    if (special == "minus?") {
                        return mal::boolean(val->value() < 0);
                    }
                    else {
                        return val->value() < 0 ? mal::trueValue() : mal::nilValue();
                    }
                }
                else {
                        return special == "minus?" ? mal::falseValue() : mal::nilValue();
                }
            }

            if (special == "number?" || special == "numberp") {
                checkArgsIs(special.c_str(), 1, argCount);

                if (special == "number?") {
                    return mal::boolean(DYNAMIC_CAST(malInteger, EVAL(list->item(1), env)) ||
                                        DYNAMIC_CAST(malDouble, EVAL(list->item(1), env)));
                }
                else {
                    return (DYNAMIC_CAST(malInteger, EVAL(list->item(1), env)) ||
                            DYNAMIC_CAST(malDouble, EVAL(list->item(1), env))) ? mal::trueValue() : mal::nilValue();
                }
            }

            if (special == "or") {
                checkArgsAtLeast("or", 2, argCount);
                int value = 0;
                for (int i = 1; i < argCount+1; i++) {
                    if (EVAL(list->item(i), env)->isTrue()) {
                        value |= 1;
                    }
                    else {
                        value |= 2;
                    }
                }
                return value == 3 ? mal::trueValue() : mal::falseValue();
            }

            if (special == "quasiquote") {
                checkArgsIs("quasiquote", 1, argCount);
                ast = quasiquote(list->item(1));
                continue; // TCO
            }

            if (special == "quote") {
                checkArgsIs("quote", 1, argCount);
                return list->item(1);
            }

            if (special == "repeat") {
                checkArgsIs("repeat*", 2, argCount);
                const malInteger* loop = VALUE_CAST(malInteger, list->item(1));
                for (int i = 1; i < loop->value(); i++) {
                    EVAL(list->item(argCount), env);
                }
                ast = list->item(argCount);
                continue; // TCO
            }

            if (special == "set") {
                checkArgsIs("set", 2, argCount);
                const malSymbol* id = new malSymbol(list->item(1)->print(true));
                return env->set(id->value(), EVAL(list->item(2), env));
            }

            if (special == "try*") {
                malValuePtr tryBody = list->item(1);

                if (argCount == 1) {
                    ast = tryBody;
                    continue; // TCO
                }
                checkArgsIs("try*", 2, argCount);
                const malList* catchBlock = VALUE_CAST(malList, list->item(2));

                checkArgsIs("catch*", 2, catchBlock->count() - 1);
                MAL_CHECK(VALUE_CAST(malSymbol,
                    catchBlock->item(0))->value() == "catch*",
                    "catch block must begin with catch*");

                // We don't need excSym at this scope, but we want to check
                // that the catch block is valid always, not just in case of
                // an exception.
                const malSymbol* excSym =
                    VALUE_CAST(malSymbol, catchBlock->item(1));

                malValuePtr excVal;

                try {
                    return EVAL(tryBody, env);
                }
                catch(String& s) {
                    excVal = mal::string(s);
                }
                catch (malEmptyInputException&) {
                    // Not an error, continue as if we got nil
                    ast = mal::nilValue();
                }
                catch(malValuePtr& o) {
                    excVal = o;
                };

                if (excVal) {
                    // we got some exception
                    env = malEnvPtr(new malEnv(env));
                    env->set(excSym->value(), excVal);
                    ast = catchBlock->item(2);
                }
                continue; // TCO
            }

            if (special == "while") {
                checkArgsIs("while", 2, argCount);

                malValuePtr loop = list->item(1);
                malValuePtr loopBody = list->item(argCount);

                while (1) {
                    loopBody = EVAL(list->item(argCount), env);
                    loop = EVAL(list->item(1), env);

                    if (!loop->isTrue()) {
                        ast = loopBody;
                        break;
                    }
                }
                continue; // TCO
            }
            if (special == "zero?" || special == "zerop") {
                                checkArgsIs(special.c_str(), 1, argCount);
                if (EVAL(list->item(1), env)->type() == MALTYPE::REAL) {
                    malDouble* val = VALUE_CAST(malDouble, EVAL(list->item(1), env));
                    if (special == "zero?") {
                        return mal::boolean(val->value() == 0.0);
                    }
                    else {
                        return val->value() == 0 ? mal::trueValue() : mal::nilValue();
                    }
                }
                else if (EVAL(list->item(1), env)->type() == MALTYPE::INT) {
                    malInteger* val = VALUE_CAST(malInteger, EVAL(list->item(1), env));
                    if (special == "zero?") {
                        return mal::boolean(val->value() == 0);
                    }
                    else {
                        return val->value() == 0 ? mal::trueValue() : mal::nilValue();
                    }
                }
                else {
                        return special == "zero?" ? mal::falseValue() : mal::nilValue();
                }
            }
        }

        // Now we're left with the case of a regular list to be evaluated.
        malValuePtr op = EVAL(list->item(0), env);
        if (const malLambda* lambda = DYNAMIC_CAST(malLambda, op)) {
            if (lambda->isMacro()) {
                ast = lambda->apply(list->begin()+1, list->end());
                continue; // TCO
            }
            malValueVec* items = STATIC_CAST(malList, list->rest())->evalItems(env);
            ast = lambda->getBody();
            env = lambda->makeEnv(items->begin(), items->end());
            continue; // TCO
        }
        else {
            malValueVec* items = STATIC_CAST(malList, list->rest())->evalItems(env);
            return APPLY(op, items->begin(), items->end());
        }
    }
}

String PRINT(malValuePtr ast)
{
    return ast->print(true);
}

malValuePtr APPLY(malValuePtr op, malValueIter argsBegin, malValueIter argsEnd)
{
    const malApplicable* handler = DYNAMIC_CAST(malApplicable, op);
    MAL_CHECK(handler != NULL,
              "\"%s\" is not applicable", op->print(true).c_str());

    return handler->apply(argsBegin, argsEnd);
}

static bool isSymbol(malValuePtr obj, const String& text)
{
    const malSymbol* sym = DYNAMIC_CAST(malSymbol, obj);
    return sym && (sym->value() == text);
}

//  Return arg when ast matches ('sym, arg), else NULL.
static malValuePtr starts_with(const malValuePtr ast, const char* sym)
{
    const malList* list = DYNAMIC_CAST(malList, ast);
    if (!list || list->isEmpty() || !isSymbol(list->item(0), sym))
        return NULL;
    checkArgsIs(sym, 1, list->count() - 1);
    return list->item(1);
}

static malValuePtr quasiquote(malValuePtr obj)
{
    if (DYNAMIC_CAST(malSymbol, obj) || DYNAMIC_CAST(malHash, obj))
        return mal::list(mal::symbol("quote"), obj);

    const malSequence* seq = DYNAMIC_CAST(malSequence, obj);
    if (!seq)
        return obj;

    const malValuePtr unquoted = starts_with(obj, "unquote");
    if (unquoted)
        return unquoted;

    malValuePtr res = mal::list(new malValueVec(0));
    for (int i=seq->count()-1; 0<=i; i--) {
        const malValuePtr elt     = seq->item(i);
        const malValuePtr spl_unq = starts_with(elt, "splice-unquote");
        if (spl_unq)
            res = mal::list(mal::symbol("concat"), spl_unq, res);
         else
            res = mal::list(mal::symbol("cons"), quasiquote(elt), res);
    }
    if (DYNAMIC_CAST(malVector, obj))
        res = mal::list(mal::symbol("vec"), res);
    return res;
}

static const char* malFunctionTable[] = {
    "(defmacro! cond (fn* (& xs) (if (> (count xs) 0) (list 'if (first xs) (if (> (count xs) 1) (nth xs 1) (throw \"odd number of forms to cond\")) (cons 'cond (rest (rest xs)))))))",
    "(def! not (fn* (cond) (if cond false true)))",
    "(def! load-file (fn* (filename) \
        (eval (read-string (str \"(do \" (slurp filename) \"\nnil)\")))))",
    "(def! *host-language* \"C++\")",
    "(def! append concat)",
    "(def! car first)",
    "(def! strcat str)",
    "(def! type type?)",
    "(def! def! defn)",
    "(def! defmacro! defmacro)",
    "(def! fn* fn)",
    "(def! EOF -1)",
};

static void installFunctions(malEnvPtr env) {
    for (auto &function : malFunctionTable) {
        rep(function, env);
    }
}

// Added to keep the linker happy at step A
malValuePtr readline(const String& prompt)
{
    String input;
    if (s_readLine.get(prompt, input)) {
        return mal::string(input);
    }
    return mal::nilValue();
}

