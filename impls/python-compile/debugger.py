from loguru import logger
logger.remove()

def DEBUG (switch="on"):
    if switch:
        logger.add(sys.stderr, level="DEBUG")
        logger.info("Debugger Activated (loguru)!")
    else:
        logger.remove()

def TEST ():
    logger.info("Running tests..")
    assert(EVAL(READ("nil"), repl_env) == None)
    assert(EVAL(READ("true"), repl_env) == True)
    assert(EVAL(READ("false"), repl_env) == False)
    assert(EVAL(READ("123"), repl_env) == 123)
    assert(EVAL(READ("\"This is a string.\""), repl_env) == "This is a string.")
    assert(EVAL(READ("()"), repl_env) == [])
    assert(EVAL(READ("(+ 1 1)"), repl_env) == 2)
    assert(EVAL(READ("(+ (* 2 (+ 3 4)) 1))"), repl_env) == 15)
    assert(EVAL(READ("(+)"), repl_env) == 0)
    assert(EVAL(READ("(-)"), repl_env) == 0)
    assert(EVAL(READ("(- 9)"), repl_env) == -9)
    assert(EVAL(READ("(- 9 2)"), repl_env) == 7)
    assert(EVAL(READ("(*)"), repl_env) == 1)
    assert(EVAL(READ("(let* (a 3 b 4) (+ a b))"), repl_env) == 7)
    assert(EVAL(READ("(let* (a 3 b 4) (+ a (let* (b 0) b)))"), repl_env) == 3)
    assert(EVAL(READ("(let* (a 3 b a) b)"), repl_env) == 3)
    assert(EVAL(READ("(let* (a 3 b a) (let* (a b a a) 3))"), repl_env) == 3)
    assert(EVAL(READ("(do (def! x 1) (def! y 2) (+ x y))"), repl_env) == 3)
    assert(EVAL(READ("(do (def! x 8) x (def! y 9) (let* (y x x y) x))"), repl_env) == 8)
    assert(EVAL(READ("(if          )"), repl_env) == None)
    assert(EVAL(READ("(if 0        )"), repl_env) == None)
    assert(EVAL(READ("(if 0     1  )"), repl_env) == 1)
    assert(EVAL(READ("(if 0     1 2)"), repl_env) == 1)
    assert(EVAL(READ("(if nil   1 2)"), repl_env) == 2)
    assert(EVAL(READ("(if nil   1  )"), repl_env) == None)
    assert(EVAL(READ("(if false 1 2)"), repl_env) == 2)
    assert(EVAL(READ("(if (if false 0 nil) 1 2)"), repl_env) == 2)
    assert(EVAL(READ("(do (def! f (fn* () a)) (def! a 9) (let* (a 0) (f)))"), repl_env) == 9) # NOTE Is this desirable?
    assert(EVAL(READ("((fn* (a) a) 7)"), repl_env) == 7)
    assert(EVAL(READ("((fn* (a) (* (a) (a))) (fn* (a) 3))"), repl_env) == 9)
    assert(EVAL(READ("((fn* (a b) (* (a b) b)) (fn* (a) (+ 2 a)) 7)"), repl_env) == 63)
    assert(EVAL(READ("((let* (a 10000 b -2) (fn* (a c) (+ a b c))) 1 1)"), repl_env) == 0)
    def expect_infinite_loop (lisp_code):
        try:
            EVAL(READ(lisp_code), repl_env)
        except RecursionError:
            pass
        else:
            raise Exception("Should have given an infinite loop.")
    expect_infinite_loop("((fn* (a) (a a)) (fn* (a) (a a)))")
    expect_infinite_loop("(let* (f (fn* (a) (a a))) (f f))")
    expect_infinite_loop("(do (def! f (fn* (a) (a a))) (def! g f) (g g))")
    expect_infinite_loop("(let* (f (fn* (a) (a a)) g f) (g g))")
    assert(types._function_Q(EVAL(READ("(eval +)"), repl_env)))
    assert(EVAL(READ("(eval (list + 1))"), repl_env) == 1)
    assert(EVAL(READ("(let* (x (atom 3)) (atom? x))"), repl_env) == True)
    assert(EVAL(READ("(let* (x (atom 3)) (deref x))"), repl_env) == 3)
    assert(EVAL(READ("(let* (x (atom 3)) @x)"), repl_env) == 3)
    assert(EVAL(READ("(let* (x (atom 3)) (do (swap! x (fn* (n) (+ 1 n))) (deref x)))"), repl_env) == 4)
    assert(EVAL(READ("(let* (x (atom 3)) (do (reset! x 9) (deref x)))"), repl_env) == 9)
    assert(EVAL(READ("(quote (1 2 3))"), repl_env) == [1, 2, 3])
    assert(EVAL(READ("'(1 2 3)"), repl_env) == [1, 2, 3])
    assert(EVAL(READ("'+"), repl_env) == "+")
    assert(EVAL(READ("\"+\""), repl_env) == "+")
    assert(EVAL(READ("(= '+ \"+\")"), repl_env) == False)
    assert(EVAL(READ("(cond true 1 false 2 true 3)"), repl_env) == 1)
    assert(EVAL(READ("(cond false 1 false 2 true 3)"), repl_env) == 3)
    assert(EVAL(READ("(cond false 1 false 2 false 3)"), repl_env) == None)
    assert(EVAL(READ("(do (def! x 1) (def! f (fn* () (do (def! x 2) (let* (x 3) (g))))) (def! g (fn* () x)) (g))"), repl_env) == 1)
    assert(EVAL(READ("(do (def! x 1) (def! f (fn* () (do (def! x 2) (def! g (fn* () x)) (let* (x 3) (g))))) (f))"), repl_env) == 2)
    logger.info("All tests passed!")
    print("All tests passed!")
