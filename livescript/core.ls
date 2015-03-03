require! LiveScript

require! 'prelude-ls': {join, sum, all, fold, fold1, map}
require! './types.ls': {string, Builtin, Lambda, MalList, MalVec}
require! './builtins.ls': {NIL, is-number, is-nil, is-seq, mal-eql}
require! './printer.ls': {str, pr-str}

export ns = {}

bool = (value) -> type: \BOOL, value: value
int = (value) -> type: \INT, value: value
float = (value) -> type: \FLOAT, value: value

ns.list = new Builtin (elems) -> new MalList elems

ns['list?'] = new Builtin ([x]) -> bool x.type is \LIST

ns['empty?'] = new Builtin ([x]) ->
    | is-nil x => bool true
    | is-seq x => bool x.value.length is 0
    | _ => throw new Error 'Not a sequence'

ns['nil?'] = new Builtin ([x]) -> bool is-nil x

ns['count'] = new Builtin ([x]) ->
    | is-nil x => int 0
    | is-seq x => int x.value.length
    | _ => throw new Error 'Not a sequence'

ns['='] = new Builtin ([x, ...xs]:args) ->
    throw new Error 'Expected at least two arguments' unless args.length > 1
    bool all (-> mal-eql x, it), xs

ns['conj'] = new Builtin ([x, xs]:args) ->
    throw new Error 'Two arguments expected' unless args.length is 2
    throw new Error 'Collection must be sequence' unless is-seq xs
    elems = [x] ++ xs.value
    switch xs.type
        | \VEC => new MalVec elems
        | \LIST => new MalList elems

ns['name'] = new Builtin ([x]:args) ->
    throw new Error 'One argument expected' unless args.length is 1
    throw new Error 'Not a keyword' unless x.type is \KEYWORD
    {type: \STRING, value: x.name}

ns['get'] = new Builtin ([m, k]:args) ->
    throw new Error 'Two arguments expected' unless args.length is 2
    throw new Error 'Not a map' unless m.type is \MAP
    (m.get k) or NIL

ns['has-key?'] = new Builtin ([m, k]:args) ->
    throw new Error 'Two arguments expected' unless args.length is 2
    throw new Error 'Not a map' unless m.type is \MAP
    bool (m.get k)?

assoc-num-op = (op, zero, toMal) -> new Builtin (nums) ->
    throw new Error 'Expected at least two numbers' unless nums.length > 1
    throw new Error "Expected numbers" unless all is-number nums
    toMal fold op, zero, (map (.value),  nums)

int-op = (op, zero) -> assoc-num-op op, zero, int

comparator = (test) -> new Builtin ([x, ...xs]:nums) ->
    throw new Error 'Expected at least two numbers' unless nums.length > 1
    throw new Error "Expected numbers" unless all is-number nums
    init = {val: x, ret: true}
    f = ({val: a, ret}, b) -> val: b, ret: (ret and (test a.value, b.value))
    bool (.ret) fold f, init, xs

ns['<'] = comparator (<)
ns['<='] = comparator (<=)
ns['>'] = comparator (>)
ns['>='] = comparator (>=)
ns['+'] = int-op (+), 0
ns['*'] = int-op (*), 1
ns['/'] = new Builtin ([x, y]) ->
    if x.type is \INT and y.type is \INT
        int Math.round x.value / y.value
    else
        float x.value / y.value

ns['-'] = new Builtin ([x, ...ys]:args) ->
    val = x.value - sum map (.value), ys
    if all (-> it.type is \INT), args
        int val
    else
        float val

ns['print'] = new Builtin (exprs) ->
    for e in exprs
        process.stdout.write str e
    NIL

ns['println'] = new Builtin (exprs) ->
    console.log join '',  (map str, exprs)
    NIL

ns['pr-str'] = new Builtin string . (join ' ') . (map pr-str)

ns['str'] = new Builtin string . (join '') . (map str)

ns['prn'] = new Builtin (exprs) ->
    console.log join ' ',  (map pr-str, exprs)
    NIL

