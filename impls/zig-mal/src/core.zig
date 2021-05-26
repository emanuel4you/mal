const std = @import("std");
const Allocator = std.mem.Allocator;

const printer = @import("./printer.zig");
const printJoin = printer.printJoin;
const types = @import("./types.zig");
const MalType = types.MalType;
const MalValue = types.MalValue;
const Number = MalType.Number;
const Primitive = MalValue.Function.Primitive;
const Error = Primitive.Error;

pub fn add(a: Number, b: Number) Number {
    return a + b;
}

pub fn subtract(a: Number, b: Number) Number {
    return a - b;
}

pub fn multiply(a: Number, b: Number) Number {
    return a * b;
}

pub fn divide(a: Number, b: Number) Number {
    // TODO: use std.math.divFloor/divTrunc for runtime errors instead of
    // undefined behavior when dividing by zero
    return @divFloor(a, b);
}

pub fn lessThan(a: Number, b: Number) bool {
    return a < b;
}

pub fn lessOrEqual(a: Number, b: Number) bool {
    return a <= b;
}

pub fn greaterThan(a: Number, b: Number) bool {
    return a > b;
}

pub fn greaterOrEqual(a: Number, b: Number) bool {
    return a >= b;
}

pub fn list(allocator: *Allocator, params: MalValue.List) Error!*MalValue {
    var result_ptr = try allocator.create(MalValue);
    result_ptr.* = MalValue{ .list = params };
    return result_ptr;
}

pub fn is_list(param: *const MalValue) bool {
    return param.* == .list;
}

// TODO: per the guide this should be defined in Mal itself using rep()
pub fn not(param: *const MalValue) bool {
    return !param.isTruthy();
}

pub fn is_nil(param: *const MalValue) bool {
    return param.* == .mal_type and param.mal_type == .atom and param.mal_type.atom == .nil;
}

pub fn is_empty(param: *const MalValue) bool {
    return count(param) == 0;
}

pub fn count(param: *const MalValue) Number {
    if (is_list(param))
        return @intCast(Number, param.list.items.len)
    else if (is_nil(param))
        return 0
    else
        // TODO: error if not list?
        return -1;
}

pub fn eql(a: *const MalValue, b: *const MalValue) bool {
    return a.equals(b);
}

pub fn pr_str(allocator: *Allocator, args: MalValue.List) Error!*MalValue {
    var result_ptr = try allocator.create(MalValue);
    result_ptr.* = MalValue.makeString(try printJoin(allocator, "", args, true));
    return result_ptr;
}

pub fn str(allocator: *Allocator, args: MalValue.List) Error!*MalValue {
    var result_ptr = try allocator.create(MalValue);
    result_ptr.* = MalValue.makeString(try printJoin(allocator, "", args, false));
    return result_ptr;
}

pub fn prn(allocator: *Allocator, args: MalValue.List) Error!*MalValue {
    const string = try printJoin(allocator, " ", args, true);
    defer allocator.free(string);

    const stdout = std.io.getStdOut().writer();
    try stdout.print("{s}\n", .{string});

    // TODO: this shouldn't need to allocate
    var result_ptr = try allocator.create(MalValue);
    result_ptr.* = MalValue{ .mal_type = .{ .atom = .nil } };
    return result_ptr;
}

pub fn println(allocator: *Allocator, args: MalValue.List) Error!*MalValue {
    const string = try printJoin(allocator, " ", args, false);
    defer allocator.free(string);

    const stdout = std.io.getStdOut().writer();
    try stdout.print("{s}\n", .{string});

    // TODO: this shouldn't need to allocate
    var result_ptr = try allocator.create(MalValue);
    result_ptr.* = MalValue{ .mal_type = .{ .atom = .nil } };
    return result_ptr;
}

pub const ns = .{
    .@"+" = Primitive.make(add),
    .@"-" = Primitive.make(subtract),
    .@"*" = Primitive.make(multiply),
    .@"/" = Primitive.make(divide),
    .@"<" = Primitive.make(lessThan),
    .@"<=" = Primitive.make(lessOrEqual),
    .@">" = Primitive.make(greaterThan),
    .@">=" = Primitive.make(greaterOrEqual),
    .@"=" = Primitive.make(eql),
    .@"list" = Primitive.make(list),
    .@"list?" = Primitive.make(is_list),
    .@"empty?" = Primitive.make(is_empty),
    .@"nil?" = Primitive.make(is_nil),
    .@"not" = Primitive.make(not),
    .@"count" = Primitive.make(count),
    .@"pr-str" = Primitive.make(pr_str),
    .@"str" = Primitive.make(str),
    .@"prn" = Primitive.make(prn),
    .@"println" = Primitive.make(println),
};