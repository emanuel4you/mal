GET "libhdr"
GET "malhdr"

GET "readline.b"
GET "types.b"

LET READ(x) = x

LET EVAL(x) = x

LET PRINT(x) = x

LET rep(x) = PRINT(EVAL(READ(x)))

LET repl() BE
{ LET prompt = str_bcpl2mal("user> ")
  { LET line = readline(prompt)
    IF line = nil THEN BREAK
    writes(@rep(line)!str_data)
    newline()
  } REPEAT
}

LET start() = VALOF
{ LET ch = 0
  init_types()
  ch := rdch() REPEATUNTIL ch = '*n' // Consume command-line args
  wrch('*n') // Terminate prompt printed by Cintsys
  repl()
  RESULTIS 0
}

// Dummy version of throwf() because step 0 doesn't include printer.b
LET throwf(msg, A) BE throw(str_bcpl2mal(msg))
