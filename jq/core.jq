include "utils";
include "printer";

def core_identify:
    {
        "env": {
            kind: "fn",
            function: "env",
            inputs: 0
        },
        "prn": {
            kind: "fn",
            function: "prn",
            inputs: -1
        },
        "pr-str": {
            kind: "fn",
            function: "pr-str",
            inputs: -1
        },
        "str": {
            kind: "fn",
            function: "str",
            inputs: -1
        },
        "println": {
            kind: "fn",
            function: "println",
            inputs: -1
        },
        "list": {
            kind: "fn",
            function: "list",
            inputs: -1
        },
        "list?": {
            kind: "fn",
            function: "list?",
            inputs: 1
        },
        "empty?": {
            kind: "fn",
            function: "empty?",
            inputs: 1
        },
        "count": {
            kind: "fn",
            function: "count",
            inputs: 1
        },
        "=": {
            kind: "fn",
            function: "=",
            inputs: 2
        },
        "<": {
            kind: "fn",
            function: "<",
            inputs: 2
        },
        "<=": {
            kind: "fn",
            function: "<=",
            inputs: 2
        },
        ">": {
            kind: "fn",
            function: ">",
            inputs: 2
        },
        ">=": {
            kind: "fn",
            function: ">=",
            inputs: 2
        },
    };

def vec2list(obj):
    if obj.kind == "list" then
        obj.value | map(vec2list(.)) | wrap("list")
    else 
    if obj.kind == "vector" then
        obj.value | map(vec2list(.)) | wrap("list")
    else 
        obj
    end end;

def core_interp(arguments; env):
    (
        select(.function == "number_add") |
        arguments | map(.value) | .[0] + .[1] | wrap("number")
    ) // (
        select(.function == "number_sub") |
        arguments | map(.value) | .[0] - .[1] | wrap("number")
    ) // (
        select(.function == "number_mul") |
        arguments | map(.value) | .[0] * .[1] | wrap("number")
    ) // (
        select(.function == "number_div") |
        arguments | map(.value) | .[0] / .[1] | wrap("number")
    ) // (
        select(.function == "env") |
        env | tojson | wrap("string")
    ) // (
        select(.function == "prn") |
        arguments | map(pr_str({readable: true})) | join(" ") | _print | null | wrap("nil")
    ) // (
        select(.function == "pr-str") |
        arguments | map(pr_str({readable: true})) | join(" ") |  wrap("string")
    ) // (
        select(.function == "str") |
        arguments | map(pr_str({readable: false})) | join("") |  wrap("string")
    ) // (
        select(.function == "println") |
        arguments | map(pr_str({readable: false})) | join(" ") | _print | null | wrap("nil")
    ) // (
        select(.function == "list") |
        arguments | wrap("list")
    ) // (
        select(.function == "list?") | null | wrap(arguments | first.kind == "list" | tostring)
    ) // (
        select(.function == "empty?") | null | wrap(arguments|first.value | length == 0 | tostring)
    ) // (
        select(.function == "count") | arguments|first.value | length | wrap("number")
    ) // (
        select(.function == "=") | null | wrap(vec2list(arguments[0]) == vec2list(arguments[1]) | tostring)
    ) // (
        select(.function == "<") | null | wrap(arguments[0].value < arguments[1].value | tostring)
    ) // (
        select(.function == "<=") | null | wrap(arguments[0].value <= arguments[1].value | tostring)
    ) // (
        select(.function == ">") | null | wrap(arguments[0].value > arguments[1].value | tostring)
    ) // (
        select(.function == ">=") | null | wrap(arguments[0].value >= arguments[1].value | tostring)
    ) // jqmal_error("Unknown native function \(.function)");