GET "libhdr"
GET "malhdr"

// A Reader is just a pointer to a (variable) pointer to the head of
// a list of strings.

LET reader_peek(rdr) = (!rdr)!lst_first

LET reader_next(rdr) = VALOF
{ LET tok = reader_peek(rdr)
  !rdr := (!rdr)!lst_rest
  RESULTIS tok
}

LET tokenize(s) = VALOF
{ LET tokens, tailp = empty, @tokens
  LET sd = s + str_data
  LET tokstart, token = ?, ?
  FOR p = 1 TO s!str_len DO
  { tokstart := p
    // Within this SWITCHON command, use LOOP to ignore input, or ENDCASE to
    // emit a token.
    SWITCHON sd%p INTO
    { CASE ' ': CASE '*t': CASE '*n': CASE ',': LOOP // Inter-token whitespace
      CASE '~': // Maybe ~@
        IF p < s!str_len & sd%(p+1) = '@' THEN p := p + 1 // FALLTHROUGH
      CASE '[': CASE ']': CASE '{': CASE '}': CASE '(': CASE ')': CASE '*'':
      CASE '`': CASE '^': CASE '@': // Single-character token
        ENDCASE
      CASE ';': // Comment
        p := p + 1 REPEATUNTIL p > s!str_len | sd%p = '*n'
        LOOP
      CASE '*"': // String
        p := p + (sd%p = '\' -> 2, 1) REPEATUNTIL p > s!str_len | sd%p = '*"'
        ENDCASE
      DEFAULT: // Symbol, keyword, or number
        WHILE p < s!str_len DO
        { p := p + 1
	  SWITCHON sd%p INTO
          { CASE ' ': CASE '*t': CASE '*n': CASE ',':
            CASE '[': CASE ']': CASE '{': CASE '}': CASE '(': CASE ')':
            CASE '*'': CASE '`': CASE '~': CASE '^': CASE '@': CASE '*"':
            CASE ';':
              p := p - 1; BREAK
          }
        }
        ENDCASE
    }
    // At this point, tokstart points to the first character of the token,
    // and p points to the last character.
    token := str_substr(s, tokstart, p + 1)
    !tailp := cons(token, empty)
    tailp := @(!tailp)!lst_rest
  }
  RESULTIS tokens
}

// This is for reading into a string, as opposed to read_str, which is
// for reading from a string.
LET read_string(token) = VALOF
{ LET i, o, out = 2, 0, ?
  WHILE i < token!str_len DO
  { IF (token + str_data)%i = '\' THEN i := i + 1
    i, o := i + 1, o + 1
  }
  UNLESS i = token!str_len & (token + str_data)%i = '*"' DO
    throw(str_bcpl2mal("unbalanced quotes"))
  out := alloc_str(o)
  i, o := 2,  1
  WHILE i < token!str_len DO
  { LET ch = (token + str_data)%i
    IF ch = '\' THEN
    { i := i + 1
      ch := (token + str_data)%i
      IF ch = 'n' THEN ch := '*n'
    }
    (out + str_data)%o := ch
    i, o := i + 1, o + 1
  }
  str_setlen(out, o - 1)
  RESULTIS out
}

LET read_keyword(token) = as_kwd(str_substr(token, 2, token!str_len + 1))

LET read_number_maybe(token) = VALOF
{ LET sd, start, negative, acc = token + str_data, 1, FALSE, 0
  IF sd%1 = '-' THEN
  { IF token!str_len = 1 THEN RESULTIS nil
    negative := TRUE
    start := 2
  }
  FOR i = start TO token!str_len DO
  { acc := acc * 10
    SWITCHON sd%i INTO
    { CASE '0': ENDCASE
      CASE '1': acc := acc + 1; ENDCASE
      CASE '2': acc := acc + 2; ENDCASE
      CASE '3': acc := acc + 3; ENDCASE
      CASE '4': acc := acc + 4; ENDCASE
      CASE '5': acc := acc + 5; ENDCASE
      CASE '6': acc := acc + 6; ENDCASE
      CASE '7': acc := acc + 7; ENDCASE
      CASE '8': acc := acc + 8; ENDCASE
      CASE '9': acc := acc + 9; ENDCASE
      DEFAULT: RESULTIS nil
    }
  }
  IF negative THEN acc := -acc
  RESULTIS alloc_int(acc)
}

LET read_atom(rdr) = VALOF
{ LET token, maybenum = reader_next(rdr), ?
  IF (token + str_data)%1 = '*"' THEN RESULTIS read_string(token)
  IF (token + str_data)%1 = ':' THEN RESULTIS read_keyword(token)
  maybenum := read_number_maybe(token)
  UNLESS maybenum = nil RESULTIS maybenum
  IF str_eq_const(token, "nil")   RESULTIS nil
  IF str_eq_const(token, "true")  RESULTIS mtrue
  IF str_eq_const(token, "false") RESULTIS mfalse
  RESULTIS as_sym(token)
}

LET read_list(rdr) = VALOF
{ reader_next(rdr) // Skip leading '('
  RESULTIS read_list_tail(rdr)
}

AND read_list_tail(rdr) = VALOF
  TEST (reader_peek(rdr) + str_data)%1 = ')' THEN
  { reader_next(rdr)
    RESULTIS empty
  } ELSE {
    LET first = read_form(rdr)
    LET rest = read_list_tail(rdr)
    RESULTIS cons(first, rest)
  }

AND read_vec(rdr) = VALOF
{ reader_next(rdr) // Skip leading '['
  RESULTIS read_vec_tail(rdr, 0)
}

AND read_vec_tail(rdr, len) = VALOF
  TEST (reader_peek(rdr) + str_data)%1 = ']' THEN
  { reader_next(rdr)
    RESULTIS alloc_vec(len)
  } ELSE {
    LET first = read_form(rdr)
    LET vec = read_vec_tail(rdr, len + 1)
    (vec + vec_data)!len := first
    RESULTIS vec
  }

AND read_hm(rdr) = VALOF
{ LET map = empty_hashmap
  reader_next(rdr) // Skip leading '{'
  { LET key, value = ?, ?
    IF (reader_peek(rdr) + str_data)%1 = '}' THEN { reader_next(rdr); BREAK }
    key := read_form(rdr)
    IF (reader_peek(rdr) + str_data)%1 = '}' THEN
      throw(str_bcpl2mal("odd number of elements in literal hash-map"))
    value := read_form(rdr)
    map := hm_set(map, key, value)
  } REPEAT
  RESULTIS map
}

AND read_macro(rdr, name) = VALOF
{ LET first, rest = as_sym(str_bcpl2mal(name)), ?
  reader_next(rdr) // skip macro character
  rest := cons(read_form(rdr), empty)
  RESULTIS cons(first, rest)
}

AND read_with_meta(rdr) = VALOF
{ LET rest = ?
  reader_next(rdr) // skip '^'
  rest := cons(read_form(rdr), empty)
  rest := cons(read_form(rdr), rest)
  RESULTIS cons(as_sym(str_bcpl2mal("with-meta")), rest)
}

AND read_form(rdr) = VALOF
{ LET token = reader_peek(rdr)
  UNLESS type OF token = t_str DO
    throw(str_bcpl2mal("unexpected end of input"))
  SWITCHON (token + str_data)%1 INTO
  { CASE '(': RESULTIS read_list(rdr)
    CASE ')': throw(str_bcpl2mal("unbalanced parentheses"))
    CASE '[': RESULTIS read_vec(rdr)
    CASE ']': throw(str_bcpl2mal("unbalanced brackets"))
    CASE '{': RESULTIS read_hm(rdr)
    CASE '}': throw(str_bcpl2mal("unbalanced braces"))
    CASE '*'': RESULTIS read_macro(rdr, "quote")
    CASE '`': RESULTIS read_macro(rdr, "quasiquote")
    CASE '~':
      IF token!str_len = 2 THEN RESULTIS read_macro(rdr, "splice-unquote")
      RESULTIS read_macro(rdr, "unquote")
    CASE '@': RESULTIS read_macro(rdr, "deref")
    CASE '^': RESULTIS read_with_meta(rdr)
    DEFAULT: RESULTIS read_atom(rdr)
  }
}

LET read_str(s) = VALOF
{ LET tokens = tokenize(s)
  LET rdr = @tokens
  RESULTIS read_form(rdr)
}
