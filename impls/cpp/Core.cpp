#include "MAL.h"
#include "Environment.h"
#include "StaticList.h"
#include "Types.h"

#include <chrono>
#include <fstream>
#include <iostream>
#include <stdio.h>
#include <unistd.h>
#include <sys/select.h>
#include <termios.h>
#include <sys/ioctl.h>

/* temp defined */
#include <regex>

typedef std::regex Regex;

static const Regex intRegex("^[-+]?\\d+$");
static const Regex floatRegex("^[+-]?\\d+[.]{1}\\d+$");
static const Regex floatPointRegex("[.]{1}\\d+$");

#include <math.h>
#include <cmath>

#define REL "1.0"
#define VERSION_STR(rel) "MAL LISP [C++] " rel " (en)"
#define VERSION VERSION_STR(REL)

#define CHECK_ARGS_IS(expected) \
    checkArgsIs(name.c_str(), expected, \
                  std::distance(argsBegin, argsEnd))

#define CHECK_ARGS_BETWEEN(min, max) \
    checkArgsBetween(name.c_str(), min, max, \
                       std::distance(argsBegin, argsEnd))

#define CHECK_ARGS_AT_LEAST(expected) \
    checkArgsAtLeast(name.c_str(), expected, \
                        std::distance(argsBegin, argsEnd))

#define FLOAT_PTR \
    (argsBegin->ptr()->type() == MALTYPE::REAL)

#define INT_PTR \
    (argsBegin->ptr()->type() == MALTYPE::INT)

#define NIL_PTR \
    (argsBegin->ptr()->print(true).compare("nil") == 0)

bool argsHasFloat(malValueIter argsBegin, malValueIter argsEnd)
{
    for (auto it = argsBegin; it != argsEnd; ++it) {
        if (FLOAT_PTR) {
            return true;
        }
    }
    return false;
}

#define ARGS_HAS_FLOAT \
    argsHasFloat(argsBegin, argsEnd)

#define CHECK_ARG_IS_NUMBER \
    MAL_CONSTAND_FAIL_CHECK(argsBegin->ptr(), "nil", "number?") \
    MAL_CONSTAND_FAIL_CHECK(argsBegin->ptr(), "false", "number?") \
    MAL_CONSTAND_FAIL_CHECK(argsBegin->ptr(), "true", "number?") \
    if (!(argsBegin->ptr()->type() == MALTYPE::REAL) && \
        !(argsBegin->ptr()->type() == MALTYPE::INT)) { \
        std::cout << (int) argsBegin->ptr()->type() << std::endl; \
        MAL_TYPE_FAIL(argsBegin->ptr(), "number?") \
    }

#define MALTYPE_ERR_STR(name, prog) \
        const malValuePtr type = mal::type(name->type()); \
        const String typeError = "'" + String(prog) + "': type is " + type->print(true);

#define ERROR_STR_TYPE(name, prog) \
    "'" prog "': type is " name

#define MAL_TYPE_FAIL(name, nameType) \
    MALTYPE_ERR_STR(name, nameType) \
    MAL_FAIL(typeError.c_str());

#define MAL_CONSTAND_FAIL_CHECK(name, c, nameType) MAL_CHECK(!(name->print(true).compare(c) == 0), ERROR_STR_TYPE(c, nameType));

#define CHECK_IS_NUMBER(name) \
    MAL_CONSTAND_FAIL_CHECK(name, "nil", "number?") \
    MAL_CONSTAND_FAIL_CHECK(name, "false", "number?") \
    MAL_CONSTAND_FAIL_CHECK(name, "true", "number?") \
    if (!(name->type() == MALTYPE::INT) || !(name->type() == MALTYPE::INT)) { \
        MAL_TYPE_FAIL(name, "number?") \
    }

#define CHECK_IS_INT(name) \
    MAL_CONSTAND_FAIL_CHECK(name, "nil", "number?") \
    MAL_CONSTAND_FAIL_CHECK(name, "false", "number?") \
    MAL_CONSTAND_FAIL_CHECK(name, "true", "number?") \
    if (!(name->type() == MALTYPE::INT)) { \
        MAL_TYPE_FAIL(name, "number?") \
    }

#define FLOAT_PTR (argsBegin->ptr()->type() == MALTYPE::REAL)

#define INT_PTR (argsBegin->ptr()->type() == MALTYPE::INT)

#define NIL_PTR (argsBegin->ptr()->print(true).compare("nil") == 0)

#define AG_INT(name) \
    CHECK_ARG_IS_NUMBER \
    malInteger* name = VALUE_CAST(malInteger, *argsBegin++)

#define ADD_INT_VAL(val) \
    CHECK_ARG_IS_NUMBER \
    malInteger val = dynamic_cast<malInteger*>(argsBegin->ptr());

#define ADD_FLOAT_VAL(val) \
    CHECK_ARG_IS_NUMBER \
    malDouble val = dynamic_cast<malDouble*>(argsBegin->ptr());

#define ADD_LIST_VAL(val) \
    malList val = dynamic_cast<malList*>(argsBegin->ptr());

#define SET_INT_VAL(opr, checkDivByZero) \
    ADD_INT_VAL(*intVal) \
    intValue = intValue opr intVal->value(); \
    if (checkDivByZero) { \
        MAL_CHECK(intVal->value() != 0, "Division by zero"); }

#define SET_FLOAT_VAL(opr, checkDivByZero) \
    if (FLOAT_PTR) \
    { \
        ADD_FLOAT_VAL(*floatVal) \
        floatValue = floatValue opr floatVal->value(); \
        if (checkDivByZero) { \
            MAL_CHECK(floatVal->value() != 0.0, "Division by zero"); } \
    } \
    else \
    { \
        ADD_INT_VAL(*intVal) \
        floatValue = floatValue opr double(intVal->value()); \
        if (checkDivByZero) { \
            MAL_CHECK(intVal->value() != 0, "Division by zero"); } \
    }

static String printValues(malValueIter begin, malValueIter end,
                           const String& sep, bool readably);

static int countValues(malValueIter begin, malValueIter end);

static StaticList<malBuiltIn*> handlers;

#define ARG(type, name) type* name = VALUE_CAST(type, *argsBegin++)

#define FUNCNAME(uniq) builtIn ## uniq
#define HRECNAME(uniq) handler ## uniq
#define BUILTIN_DEF(uniq, symbol) \
    static malBuiltIn::ApplyFunc FUNCNAME(uniq); \
    static StaticList<malBuiltIn*>::Node HRECNAME(uniq) \
        (handlers, new malBuiltIn(symbol, FUNCNAME(uniq))); \
    malValuePtr FUNCNAME(uniq)(const String& name, \
        malValueIter argsBegin, malValueIter argsEnd)

#define BUILTIN(symbol)  BUILTIN_DEF(__LINE__, symbol)

#define BUILTIN_ISA(symbol, type) \
    BUILTIN(symbol) { \
        CHECK_ARGS_IS(1); \
        return mal::boolean(DYNAMIC_CAST(type, *argsBegin)); \
    }

#define BUILTIN_IS(op, constant) \
    BUILTIN(op) { \
        CHECK_ARGS_IS(1); \
        return mal::boolean(*argsBegin == mal::constant()); \
    }

#define BUILTIN_INTOP(op, checkDivByZero) \
    BUILTIN(#op) { \
        BUILTIN_VAL(op, checkDivByZero); \
        }

#define BUILTIN_VAL(opr, checkDivByZero) \
    CHECK_ARGS_AT_LEAST(2); \
    if (ARGS_HAS_FLOAT) { \
        BUILTIN_FLOAT_VAL(opr, checkDivByZero) \
    } else { \
        BUILTIN_INT_VAL(opr, checkDivByZero) \
    }

#define BUILTIN_FLOAT_VAL(opr, checkDivByZero) \
    [[maybe_unused]] double floatValue = 0; \
    SET_FLOAT_VAL(+, false); \
    argsBegin++; \
    do { \
        SET_FLOAT_VAL(opr, checkDivByZero); \
        argsBegin++; \
    } while (argsBegin != argsEnd); \
    return mal::mdouble(floatValue);

#define BUILTIN_INT_VAL(opr, checkDivByZero) \
    [[maybe_unused]] int64_t intValue = 0; \
    SET_INT_VAL(+, false); \
    argsBegin++; \
    do { \
        SET_INT_VAL(opr, checkDivByZero); \
        argsBegin++; \
    } while (argsBegin != argsEnd); \
    return mal::integer(intValue);

#define BUILTIN_FUNCTION(foo) \
    CHECK_ARGS_IS(1); \
    if (FLOAT_PTR) { \
        ADD_FLOAT_VAL(*lhs) \
        return mal::mdouble(foo(lhs->value())); } \
    else { \
        ADD_INT_VAL(*lhs) \
        return mal::mdouble(foo(lhs->value())); }

#define BUILTIN_OP_COMPARE(opr) \
    CHECK_ARGS_IS(2); \
    if (ARGS_HAS_FLOAT) { \
        if (FLOAT_PTR) { \
            ADD_FLOAT_VAL(*floatRhs) \
            argsBegin++; \
            if (FLOAT_PTR) { \
                ADD_FLOAT_VAL(*floatLhs) \
                return mal::boolean(floatRhs->value() opr floatLhs->value()); } \
            else { \
               ADD_INT_VAL(*intLhs) \
               return mal::boolean(floatRhs->value() opr double(intLhs->value())); } } \
        else { \
            ADD_INT_VAL(*intRhs) \
            argsBegin++; \
            ADD_FLOAT_VAL(*floatLhs) \
            return mal::boolean(double(intRhs->value()) opr floatLhs->value()); } } \
    else { \
        ADD_INT_VAL(*intRhs) \
        argsBegin++; \
        ADD_INT_VAL(*intLhs) \
        return mal::boolean(intRhs->value() opr intLhs->value()); }

// helper foo to cast integer (64 bit) type to char (8 bit) type
unsigned char itoa64(const int64_t &sign)
{
    int64_t bit64[8];
    unsigned char result = 0;

    if(sign < 0)
    {
        std::cout << "Warning: out of char value!" << std::endl;
        return result;
    }

    for (int i = 0; i < 8; i++)
    {
        bit64[i] = (sign >> i) & 1;
        if (bit64[i])
        {
            result |= 1 << i;
        }
    }
    return result;
}

int kbhit()
{
    static const int STDIN = 0;
    static bool initialized = false;

    if (! initialized) {
        // Use termios to turn off line buffering
        termios term;
        tcgetattr(STDIN, &term);
        term.c_lflag &= ~ICANON;
        tcsetattr(STDIN, TCSANOW, &term);
        setbuf(stdin, NULL);
        initialized = true;
    }

    int bytesWaiting;
    ioctl(STDIN, FIONREAD, &bytesWaiting);
    return bytesWaiting;
}

bool compareNat(const String& a, const String& b)
{
    //std::cout << a << " " << b << std::endl;
    if (a.empty()) {
        return true;
    }
    if (b.empty()) {
        return false;
    }
    if (std::isdigit(a[0]) && !std::isdigit(b[0])) {
        return false;
    }
    if (!std::isdigit(a[0]) && std::isdigit(b[0])) {
        return false;
    }
    if (!std::isdigit(a[0]) && !std::isdigit(b[0])) {
        //std::cout << "HIT no dig" << std::endl;
        if (a[0] == '.' &&
            b[0] == '.' &&
            a.size() > 1 &&
            b.size() > 1) {
            return (std::toupper(a[1]) < std::toupper(b[1]));
        }

        if (std::toupper(a[0]) == std::toupper(b[0])) {
            return compareNat(a.substr(1), b.substr(1));
        }
        return (std::toupper(a[0]) < std::toupper(b[0]));
    }

    // Both strings begin with digit --> parse both numbers
    std::istringstream issa(a);
    std::istringstream issb(b);
    int ia, ib;
    issa >> ia;
    issb >> ib;
    if (ia != ib)
        return ia < ib;

    // Numbers are the same --> remove numbers and recurse
    String anew, bnew;
    std::getline(issa, anew);
    std::getline(issb, bnew);
    return (compareNat(anew, bnew));
}

template <typename TP>
std::time_t to_time_t(TP tp)
{
    using namespace std::chrono;
    auto sctp = time_point_cast<system_clock::duration>(tp - TP::clock::now()
              + system_clock::now());
    return system_clock::to_time_t(sctp);
}

BUILTIN_ISA("atom?",        malAtom);
BUILTIN_ISA("double?",      malDouble);
BUILTIN_ISA("file?",        malFile);
BUILTIN_ISA("integer?",     malInteger);
BUILTIN_ISA("keyword?",     malKeyword);
BUILTIN_ISA("list?",        malList);
BUILTIN_ISA("map?",         malHash);
BUILTIN_ISA("sequential?",  malSequence);
BUILTIN_ISA("string?",      malString);
BUILTIN_ISA("symbol?",      malSymbol);
BUILTIN_ISA("vector?",      malVector);

BUILTIN_INTOP(+,            false);
BUILTIN_INTOP(/,            true);
BUILTIN_INTOP(*,            false);

BUILTIN_IS("true?",         trueValue);
BUILTIN_IS("false?",        falseValue);
BUILTIN_IS("nil?",          nilValue);

BUILTIN("-")
{
    if (CHECK_ARGS_AT_LEAST(1) == 1)
    {
        if (FLOAT_PTR)
        {
            ADD_FLOAT_VAL(*lhs)
            return mal::mdouble(-lhs->value());
        }
        else
        {
            ADD_INT_VAL(*lhs)
            return mal::integer(-lhs->value());
        }
    }
    CHECK_ARGS_AT_LEAST(2);
    if (ARGS_HAS_FLOAT) {
        BUILTIN_FLOAT_VAL(-, false);
    } else {
        BUILTIN_INT_VAL(-, false);
    }
}

BUILTIN("%")
{
    CHECK_ARGS_AT_LEAST(2);
    if (ARGS_HAS_FLOAT) {
        return mal::nilValue();
    } else {
        BUILTIN_INT_VAL(%, false);
    }
}

BUILTIN("<=")
{
    BUILTIN_OP_COMPARE(<=);
}

BUILTIN(">=")
{
    BUILTIN_OP_COMPARE(>=);
}

BUILTIN("<")
{
    BUILTIN_OP_COMPARE(<);
}

BUILTIN(">")
{
    BUILTIN_OP_COMPARE(>);
}

BUILTIN("=")
{
    CHECK_ARGS_IS(2);
    const malValue* lhs = (*argsBegin++).ptr();
    const malValue* rhs = (*argsBegin++).ptr();

    return mal::boolean(lhs->isEqualTo(rhs));
}

BUILTIN("/=")
{
    CHECK_ARGS_IS(2);
    const malValue* lhs = (*argsBegin++).ptr();
    const malValue* rhs = (*argsBegin++).ptr();

    return mal::boolean(!lhs->isEqualTo(rhs));
}

BUILTIN("~ ")
{
    if (FLOAT_PTR)
    {
        return mal::nilValue();
    }
    else
    {
        ADD_INT_VAL(*lhs)
        return mal::integer(~lhs->value());
    }
}

BUILTIN("1+")
{
    CHECK_ARGS_IS(1);
    if (FLOAT_PTR)
    {
        ADD_FLOAT_VAL(*lhs)
        return mal::mdouble(lhs->value()+1);
    }
    else
    {
        ADD_INT_VAL(*lhs)
        return mal::integer(lhs->value()+1);
    }
}

BUILTIN("1-")
{
    CHECK_ARGS_IS(1);
    if (FLOAT_PTR)
    {
        ADD_FLOAT_VAL(*lhs)
        return mal::mdouble(lhs->value()-1);
    }
    else
    {
        ADD_INT_VAL(*lhs)
        return mal::integer(lhs->value()-1);
    }
}

BUILTIN("abs")
{
    CHECK_ARGS_IS(1);
    if (FLOAT_PTR)
    {
        ADD_FLOAT_VAL(*lhs)
        return mal::mdouble(abs(lhs->value()));
    }
    else
    {
        ADD_INT_VAL(*lhs)
        return mal::integer(abs(lhs->value()));
    }
}

BUILTIN("apply")
{
    CHECK_ARGS_AT_LEAST(2);
    malValuePtr op = *argsBegin++; // this gets checked in APPLY

    // Copy the first N-1 arguments in.
    malValueVec args(argsBegin, argsEnd-1);

    // Then append the argument as a list.
    const malSequence* lastArg = VALUE_CAST(malSequence, *(argsEnd-1));
    for (int i = 0; i < lastArg->count(); i++) {
        args.push_back(lastArg->item(i));
    }

    return APPLY(op, args.begin(), args.end());
}

BUILTIN("ascii")
{
    CHECK_ARGS_IS(1);
    const malValuePtr arg = *argsBegin++;

    if (const malString* s = DYNAMIC_CAST(malString, arg))
    {
        return mal::integer(int(s->value().c_str()[0]));
    }

    return mal::integer(0);
}

BUILTIN("assoc")
{
    CHECK_ARGS_AT_LEAST(1);
    ARG(malHash, hash);

    return hash->assoc(argsBegin, argsEnd);
}

BUILTIN("atan")
{
    BUILTIN_FUNCTION(atan);
}

BUILTIN("atof")
{
    CHECK_ARGS_IS(1);
    const malValuePtr arg = *argsBegin++;

    if (const malString* s = DYNAMIC_CAST(malString, arg))
    {
        if(std::regex_match(s->value().c_str(), intRegex) ||
            std::regex_match(s->value().c_str(), floatRegex))
            {
                return mal::mdouble(atof(s->value().c_str()));
            }
    }
    return mal::mdouble(0);
}

BUILTIN("atoi")
{
    CHECK_ARGS_IS(1);
    const malValuePtr arg = *argsBegin++;

    if (const malString* s = DYNAMIC_CAST(malString, arg))
    {
        if (std::regex_match(s->value().c_str(), intRegex))
        {
            return mal::integer(atoi(s->value().c_str()));
        }
        if (std::regex_match(s->value().c_str(), floatRegex))
        {
            return mal::integer(atoi(std::regex_replace(s->value().c_str(),
                                                        floatPointRegex, "").c_str()));
        }
    }
    return mal::integer(0);
}

BUILTIN("atom")
{
    CHECK_ARGS_IS(1);

    return mal::atom(*argsBegin);
}

BUILTIN("boolean?")
{
    CHECK_ARGS_IS(1);
    {
        return mal::boolean(argsBegin->ptr()->type() == MALTYPE::BOOLEAN);
    }
}

#if 0
BUILTIN("car")
{
    CHECK_ARGS_IS(1);
    ARG(malSequence, seq);

    MAL_CHECK(0 < seq->count(), "Index out of range");

    return seq->first();
}
#endif
BUILTIN("cadr")
{
    CHECK_ARGS_IS(1);
    ARG(malSequence, seq);

    MAL_CHECK(1 < seq->count(), "Index out of range");

    return seq->item(1);
}

BUILTIN("caddr")
{
    CHECK_ARGS_IS(1);
    ARG(malSequence, seq);

    MAL_CHECK(2 < seq->count(), "Index out of range");

    return seq->item(2);
}
#if 0
BUILTIN("cdr")
{
    CHECK_ARGS_IS(1);
    if (*argsBegin == mal::nilValue()) {
        return mal::list(new malValueVec(0));
    }
    ARG(malSequence, seq);
    return seq->rest();
}
#endif

BUILTIN("chr")
{
    CHECK_ARGS_IS(1);
    unsigned char sign = 0;

    if (FLOAT_PTR)
    {
        ADD_FLOAT_VAL(*lhs)
        auto sign64 = static_cast<std::int64_t>(lhs->value());
        sign = itoa64(sign64);
    }
    else
    {
        ADD_INT_VAL(*lhs)
        sign = itoa64(lhs->value());
    }

    return mal::string(String(1 , sign));
}

BUILTIN("close")
{
    CHECK_ARGS_IS(1);
    ARG(malFile, pf);

    return pf->close();
}

BUILTIN("concat")
{
    int count = 0;
    for (auto it = argsBegin; it != argsEnd; ++it) {
        const malSequence* seq = VALUE_CAST(malSequence, *it);
        count += seq->count();
    }

    malValueVec* items = new malValueVec(count);
    int offset = 0;
    for (auto it = argsBegin; it != argsEnd; ++it) {
        const malSequence* seq = STATIC_CAST(malSequence, *it);
        std::copy(seq->begin(), seq->end(), items->begin() + offset);
        offset += seq->count();
    }

    return mal::list(items);
}

BUILTIN("conj")
{
    CHECK_ARGS_AT_LEAST(1);
    ARG(malSequence, seq);

    return seq->conj(argsBegin, argsEnd);
}

BUILTIN("cons")
{
    CHECK_ARGS_IS(2);
    malValuePtr first = *argsBegin++;
    ARG(malSequence, rest);

    malValueVec* items = new malValueVec(1 + rest->count());
    items->at(0) = first;
    std::copy(rest->begin(), rest->end(), items->begin() + 1);

    return mal::list(items);
}

BUILTIN("contains?")
{
    CHECK_ARGS_IS(2);
    if (*argsBegin == mal::nilValue()) {
        return *argsBegin;
    }
    ARG(malHash, hash);
    return mal::boolean(hash->contains(*argsBegin));
}

BUILTIN("cos")
{
    BUILTIN_FUNCTION(cos);
}

BUILTIN("count")
{
    CHECK_ARGS_IS(1);
    if (*argsBegin == mal::nilValue()) {
        return mal::integer(0);
    }

    ARG(malSequence, seq);
    return mal::integer(seq->count());
}

BUILTIN("deref")
{
    CHECK_ARGS_IS(1);
    ARG(malAtom, atom);

    return atom->deref();
}

BUILTIN("dissoc")
{
    CHECK_ARGS_AT_LEAST(1);
    ARG(malHash, hash);

    return hash->dissoc(argsBegin, argsEnd);
}

BUILTIN("empty?")
{
    CHECK_ARGS_IS(1);
    ARG(malSequence, seq);

    return mal::boolean(seq->isEmpty());
}

BUILTIN("eval")
{
    CHECK_ARGS_IS(1);
    return EVAL(*argsBegin, NULL);
}

BUILTIN("exit")
{
    CHECK_ARGS_IS(0);
    exit(EXIT_SUCCESS);
}

BUILTIN("exp")
{
    BUILTIN_FUNCTION(exp);
}

BUILTIN("expt")
{
    CHECK_ARGS_IS(2);

    if (FLOAT_PTR)
    {
        ADD_FLOAT_VAL(*lhs)
        argsBegin++;
        if (FLOAT_PTR)
        {
            ADD_FLOAT_VAL(*rhs)
            return mal::mdouble(pow(lhs->value(),
                                    rhs->value()));
        }
        else
        {
            ADD_INT_VAL(*rhs)
            return mal::mdouble(pow(lhs->value(),
                                    double(rhs->value())));
        }
    }
    else
    {
        ADD_INT_VAL(*lhs)
        argsBegin++;
        if (FLOAT_PTR)
        {
            ADD_FLOAT_VAL(*rhs)
            return mal::mdouble(pow(double(lhs->value()),
                                    rhs->value()));
        }
        else
        {
            ADD_INT_VAL(*rhs)
            auto result = static_cast<std::int64_t>(pow(double(lhs->value()),
                                    double(rhs->value())));
            return mal::integer(result);
        }
    }
}

BUILTIN("first")
{
    CHECK_ARGS_IS(1);
    if (*argsBegin == mal::nilValue()) {
        return mal::nilValue();
    }
    ARG(malSequence, seq);
    return seq->first();
}

BUILTIN("float")
{
    CHECK_ARGS_IS(1);

    if (FLOAT_PTR)
    {
        ADD_FLOAT_VAL(*lhs)
        return mal::mdouble(lhs->value());
    }
    else
    {
        ADD_INT_VAL(*lhs)
        return mal::mdouble(double(lhs->value()));
    }
}

BUILTIN("fn?")
{
    CHECK_ARGS_IS(1);
    malValuePtr arg = *argsBegin++;

    // Lambdas are functions, unless they're macros.
    if (const malLambda* lambda = DYNAMIC_CAST(malLambda, arg)) {
        return mal::boolean(!lambda->isMacro());
    }
    // Builtins are functions.
    return mal::boolean(DYNAMIC_CAST(malBuiltIn, arg));
}

BUILTIN("get")
{
    CHECK_ARGS_IS(2);
    if (*argsBegin == mal::nilValue()) {
        return *argsBegin;
    }
    ARG(malHash, hash);
    return hash->get(*argsBegin);
}

BUILTIN("hash-map")
{
    return mal::hash(argsBegin, argsEnd, true);
}

BUILTIN("keys")
{
    CHECK_ARGS_IS(1);
    ARG(malHash, hash);
    return hash->keys();
}

BUILTIN("keyword")
{
    CHECK_ARGS_IS(1);
    const malValuePtr arg = *argsBegin++;
    if (malKeyword* s = DYNAMIC_CAST(malKeyword, arg))
      return s;
    if (const malString* s = DYNAMIC_CAST(malString, arg))
      return mal::keyword(":" + s->value());
    MAL_FAIL("keyword expects a keyword or string");
}

BUILTIN("last")
{
    CHECK_ARGS_IS(1);
    ARG(malSequence, seq);

    MAL_CHECK(0 < seq->count(), "Index out of range");
    return seq->item(seq->count()-1);
}

BUILTIN("list")
{
    return mal::list(argsBegin, argsEnd);
}

BUILTIN("macro?")
{
    CHECK_ARGS_IS(1);

    // Macros are implemented as lambdas, with a special flag.
    const malLambda* lambda = DYNAMIC_CAST(malLambda, *argsBegin);
    return mal::boolean((lambda != NULL) && lambda->isMacro());
}

BUILTIN("map")
{
    CHECK_ARGS_IS(2);
    malValuePtr op = *argsBegin++; // this gets checked in APPLY
    ARG(malSequence, source);

    const int length = source->count();
    malValueVec* items = new malValueVec(length);
    auto it = source->begin();
    for (int i = 0; i < length; i++) {
      items->at(i) = APPLY(op, it+i, it+i+1);
    }

    return  mal::list(items);
}

BUILTIN("max")
{
    int count = CHECK_ARGS_AT_LEAST(1);
    bool hasFloat = ARGS_HAS_FLOAT;
    bool unset = true;
    [[maybe_unused]] double floatValue = 0;
    [[maybe_unused]] int64_t intValue = 0;


    if (count == 1)
    {
        if (hasFloat) {
            ADD_FLOAT_VAL(*floatVal);
            floatValue = floatVal->value();
            return mal::mdouble(floatValue);
        }
        else {
            ADD_INT_VAL(*intVal);
            intValue = intVal->value();
            return mal::integer(intValue);
        }
    }

    if (hasFloat) {
        do {
            if (FLOAT_PTR) {
                if (unset) {
                    unset = false;
                    ADD_FLOAT_VAL(*floatVal);
                    floatValue = floatVal->value();
                }
                else {
                    ADD_FLOAT_VAL(*floatVal)
                    if (floatVal->value() > floatValue) {
                        floatValue = floatVal->value();
                    }
                }
            }
            else {
                if (unset) {
                    unset = false;
                    ADD_INT_VAL(*intVal);
                    floatValue = double(intVal->value());
                }
                else {
                    ADD_INT_VAL(*intVal);
                    if (intVal->value() > floatValue)
                    {
                        floatValue = double(intVal->value());
                    }
                }
            }
            argsBegin++;
        } while (argsBegin != argsEnd);
        return mal::mdouble(floatValue);
    } else {
        ADD_INT_VAL(*intVal);
        intValue = intVal->value();
        argsBegin++;
        do {
            ADD_INT_VAL(*intVal);
            if (intVal->value() > intValue)
            {
                intValue = intVal->value();
            }
            argsBegin++;
        } while (argsBegin != argsEnd);
        return mal::integer(intValue);
    }
}

BUILTIN("meta")
{
    CHECK_ARGS_IS(1);
    malValuePtr obj = *argsBegin++;

    return obj->meta();
}

BUILTIN("min")
{
    int count = CHECK_ARGS_AT_LEAST(1);
    bool hasFloat = ARGS_HAS_FLOAT;
    bool unset = true;
    [[maybe_unused]] double floatValue = 0;
    [[maybe_unused]] int64_t intValue = 0;

    if (count == 1)
    {
        if (hasFloat) {
            ADD_FLOAT_VAL(*floatVal);
            floatValue = floatVal->value();
            return mal::mdouble(floatValue);
        }
        else {
            ADD_INT_VAL(*intVal);
            intValue = intVal->value();
            return mal::integer(intValue);
        }
    }

    if (hasFloat) {
        do {
            if (FLOAT_PTR) {
                if (unset) {
                    unset = false;
                    ADD_FLOAT_VAL(*floatVal);
                    floatValue = floatVal->value();
                }
                else {
                    ADD_FLOAT_VAL(*floatVal)
                    if (floatVal->value() < floatValue) {
                        floatValue = floatVal->value();
                    }
                }
            }
            else {
                if (unset) {
                    unset = false;
                    ADD_INT_VAL(*intVal);
                    floatValue = double(intVal->value());
                }
                else {
                    ADD_INT_VAL(*intVal);
                    if (intVal->value() < floatValue) {
                        floatValue = double(intVal->value());
                    }
                }
            }
            argsBegin++;
        } while (argsBegin != argsEnd);
        return mal::mdouble(floatValue);
    } else {
        ADD_INT_VAL(*intVal);
        intValue = intVal->value();
        argsBegin++;
        do {
            ADD_INT_VAL(*intVal);
            if (intVal->value() < intValue) {
                intValue = intVal->value();
            }
            argsBegin++;
        } while (argsBegin != argsEnd);
        return mal::integer(intValue);
    }
}

BUILTIN("minus?")
{
    CHECK_ARGS_IS(1);

    if (FLOAT_PTR)
    {
        ADD_FLOAT_VAL(*lhs)
        return mal::boolean(lhs->value() < 0.0);
    }
    else
    {
        ADD_INT_VAL(*lhs)
        return mal::boolean(lhs->value() < 0);
    }
}

BUILTIN("number?")
{
    CHECK_ARGS_IS(1);
    return mal::boolean(DYNAMIC_CAST(malInteger, *argsBegin)
                    || DYNAMIC_CAST(malDouble, *argsBegin));
}

BUILTIN("nth")
{
    // twisted parameter for both LISPs!
    CHECK_ARGS_IS(2);
    int i;

    if(INT_PTR)
    {
        AG_INT(index);
        ARG(malSequence, seq);
        i = index->value();
        MAL_CHECK(i >= 0 && i < seq->count(), "Index out of range");
        return seq->item(i);
    }
    else {
        ARG(malSequence, seq);
        AG_INT(index);
        i = index->value();
        MAL_CHECK(i >= 0 && i < seq->count(), "Index out of range");
        return seq->item(i);
    }
}

BUILTIN("open")
{
    CHECK_ARGS_IS(2);
    ARG(malString, filename);
    ARG(malString, m);
    const char mode = std::tolower(m->value().c_str()[0]);
    malFile* pf = new malFile(filename->value().c_str(), mode);

    return pf->open();
}

BUILTIN("polar")
{
    CHECK_ARGS_IS(3);
    double angle = 0;
    double dist = 0;
    double x = 0;
    double y = 0;
    [[maybe_unused]] double z = 0;

    ARG(malSequence, seq);

    if (FLOAT_PTR) {
        ADD_FLOAT_VAL(*floatAngle)
        angle = floatAngle->value();
    }
    else
    {
        ADD_INT_VAL(*intAngle)
        angle = double(intAngle->value());
    }
    if (FLOAT_PTR) {
        ADD_FLOAT_VAL(*floatDist)
        dist = floatDist->value();
    }
    else
    {
        ADD_INT_VAL(*intDist)
        dist = double(intDist->value());
    }

    if(seq->count() == 2)
    {
        CHECK_IS_NUMBER(seq->item(0))
        if (seq->item(0)->type() == MALTYPE::INT)
        {
            const malInteger* intX = VALUE_CAST(malInteger, seq->item(0));
            x = double(intX->value());
        }
        if (seq->item(0)->type() == MALTYPE::REAL)
        {
            const malDouble* floatX = VALUE_CAST(malDouble, seq->item(0));
            x = floatX->value();
        }
        CHECK_IS_NUMBER(seq->item(1))
        if (seq->item(1)->type() == MALTYPE::INT)
        {
            const malInteger* intY = VALUE_CAST(malInteger, seq->item(1));
            y = double(intY->value());
        }
        if (seq->item(1)->type() == MALTYPE::REAL)
        {
            const malDouble* floatY = VALUE_CAST(malDouble, seq->item(1));
            y = floatY->value();
        }

        malValueVec* items = new malValueVec(2);
        items->at(0) = mal::mdouble(x + dist * sin(angle));
        items->at(1) = mal::mdouble(y + dist * cos(angle));
        return mal::list(items);
    }

    if(seq->count() == 3)
    {
        if (seq->item(0)->type() == MALTYPE::INT)
        {
            const malInteger* intX = VALUE_CAST(malInteger, seq->item(0));
            x = double(intX->value());
        }
        if (seq->item(0)->type() == MALTYPE::REAL)
        {
            const malDouble* floatX = VALUE_CAST(malDouble, seq->item(0));
            x = floatX->value();
        }
        CHECK_IS_NUMBER(seq->item(1))
        if (seq->item(1)->type() == MALTYPE::INT)
        {
            const malInteger* intY = VALUE_CAST(malInteger, seq->item(1));
            y = double(intY->value());
        }
        if (seq->item(1)->type() == MALTYPE::REAL)
        {
            const malDouble* floatY = VALUE_CAST(malDouble, seq->item(1));
            y = floatY->value();
        }
        CHECK_IS_NUMBER(seq->item(2))
        if (seq->item(2)->type() == MALTYPE::INT)
        {
            const malInteger* intY = VALUE_CAST(malInteger, seq->item(2));
            z = double(intY->value());
        }
        if (seq->item(2)->type() == MALTYPE::REAL)
        {
            const malDouble* floatY = VALUE_CAST(malDouble, seq->item(2));
            z = floatY->value();
        }
        malValueVec* items = new malValueVec(3);
        items->at(0) = mal::mdouble(x + dist * sin(angle));
        items->at(1) = mal::mdouble(y + dist * cos(angle));
        items->at(2) = mal::mdouble(z);
        return mal::list(items);
    }
    return mal::nilValue();
}

BUILTIN("pr-str")
{
    return mal::string(printValues(argsBegin, argsEnd, " ", true));
}

BUILTIN("println")
{
    std::cout << printValues(argsBegin, argsEnd, " ", false) << "\n";
    return mal::nilValue();
}

BUILTIN("prn")
{
    std::cout << printValues(argsBegin, argsEnd, " ", true) << "\n";
    return mal::nilValue();
}

BUILTIN("read-string")
{
    CHECK_ARGS_IS(1);
    ARG(malString, str);

    return readStr(str->value());
}

BUILTIN("read-line")
{
    if (!CHECK_ARGS_AT_LEAST(0))
    {
        String str;
        std::getline(std::cin, str);
        return mal::string(str);
    }
    ARG(malFile, pf);

    return pf->readLine();
}

BUILTIN("read-char")
{
    if (!CHECK_ARGS_AT_LEAST(0))
    {
        unsigned char c = 0;
        while (! kbhit())
        {
            fflush(stdout);
            c=getchar();
            break;
        }
        std::cout << std::endl;
        return mal::integer(int(c));
    }
    ARG(malFile, pf);

    return pf->readChar();
}

BUILTIN("readline")
{
    CHECK_ARGS_IS(1);
    ARG(malString, str);

    return readline(str->value());
}

BUILTIN("reset!")
{
    CHECK_ARGS_IS(2);
    ARG(malAtom, atom);
    return atom->reset(*argsBegin);
}

BUILTIN("rest")
{
    CHECK_ARGS_IS(1);
    if (*argsBegin == mal::nilValue()) {
        return mal::list(new malValueVec(0));
    }
    ARG(malSequence, seq);
    return seq->rest();
}

BUILTIN("reverse")
{
    CHECK_ARGS_IS(1);
    if (*argsBegin == mal::nilValue()) {
        return mal::list(new malValueVec(0));
    }
    ARG(malSequence, seq);
    return seq->reverse(seq->begin(), seq->end());
}

BUILTIN("seq")
{
    CHECK_ARGS_IS(1);
    malValuePtr arg = *argsBegin++;
    if (arg == mal::nilValue()) {
        return mal::nilValue();
    }
    if (const malSequence* seq = DYNAMIC_CAST(malSequence, arg)) {
        return seq->isEmpty() ? mal::nilValue()
                              : mal::list(seq->begin(), seq->end());
    }
    if (const malString* strVal = DYNAMIC_CAST(malString, arg)) {
        const String str = strVal->value();
        int length = str.length();
        if (length == 0)
            return mal::nilValue();

        malValueVec* items = new malValueVec(length);
        for (int i = 0; i < length; i++) {
            (*items)[i] = mal::string(str.substr(i, 1));
        }
        return mal::list(items);
    }
    MAL_FAIL("%s is not a string or sequence", arg->print(true).c_str());
}

BUILTIN("sin")
{
    BUILTIN_FUNCTION(sin);
}

BUILTIN("slurp")
{
    CHECK_ARGS_IS(1);
    ARG(malString, filename);

    std::ios_base::openmode openmode =
        std::ios::ate | std::ios::in | std::ios::binary;
    std::ifstream file(filename->value().c_str(), openmode);
    MAL_CHECK(!file.fail(), "Cannot open %s", filename->value().c_str());

    String data;
    data.reserve(file.tellg());
    file.seekg(0, std::ios::beg);
    data.append(std::istreambuf_iterator<char>(file.rdbuf()),
                std::istreambuf_iterator<char>());

    return mal::string(data);
}

BUILTIN("sqrt")
{
    BUILTIN_FUNCTION(sqrt);
}

BUILTIN("startapp")
{
    int count = CHECK_ARGS_AT_LEAST(1);
    ARG(malString, com);
    String command = com->value();

    if (count > 1)
    {
        ARG(malString, para);
        command += " ";
        command += para->value();
    }

    if (system(command.c_str()))
    {
        return mal::nilValue();
    }
    return mal::integer(count);
}

BUILTIN("str")
{
    return mal::string(printValues(argsBegin, argsEnd, "", false));
}

BUILTIN("strcase")
{
    int count = CHECK_ARGS_AT_LEAST(1);
    ARG(malString, str);
    String trans = str->value();

    if (count > 1)
    {
        ARG(malConstant, boolVal);
        if (boolVal->isTrue())
        {
            std::transform(trans.begin(), trans.end(), trans.begin(),
                   [](unsigned char c){ return std::tolower(c); });
            return mal::string(trans);
        }
    }

    std::transform(trans.begin(), trans.end(), trans.begin(),
                   [](unsigned char c){ return std::toupper(c); });

    return mal::string(trans);
}

BUILTIN("strlen")
{
    return mal::integer(countValues(argsBegin, argsEnd));
}

BUILTIN("substr")
{
    int count = CHECK_ARGS_AT_LEAST(2);
    ARG(malString, s);
    AG_INT(start);
    int startPos = (int)start->value();

    if (s)
    {
        String bla = s->value();
        if (startPos > (int)bla.size()+1) {
            startPos = (int)bla.size()+1;
        }

        if (count > 2)
        {
            AG_INT(size);
            return mal::string(bla.substr(startPos-1, size->value()));
        }
        else
        {
                return mal::string(bla.substr(startPos-1, bla.size()));
        }
    }

    return mal::string(String(""));
}

BUILTIN("swap!")
{
    CHECK_ARGS_AT_LEAST(2);
    ARG(malAtom, atom);

    malValuePtr op = *argsBegin++; // this gets checked in APPLY

    malValueVec args(1 + argsEnd - argsBegin);
    args[0] = atom->deref();
    std::copy(argsBegin, argsEnd, args.begin() + 1);

    malValuePtr value = APPLY(op, args.begin(), args.end());
    return atom->reset(value);
}

BUILTIN("symbol")
{
    CHECK_ARGS_IS(1);
    ARG(malString, token);
    return mal::symbol(token->value());
}

BUILTIN("tan")
{
    BUILTIN_FUNCTION(tan);
}

BUILTIN("throw")
{
    CHECK_ARGS_IS(1);
    throw *argsBegin;
}

BUILTIN("time-ms")
{
    CHECK_ARGS_IS(0);

    using namespace std::chrono;
    milliseconds ms = duration_cast<milliseconds>(
        high_resolution_clock::now().time_since_epoch()
    );

    return mal::integer(ms.count());
}

BUILTIN("type?")
{
    CHECK_ARGS_IS(1);

    if (argsBegin->ptr()->print(true).compare("nil") == 0) {
        return mal::nilValue();
    }

    return mal::type(argsBegin->ptr()->type());
}

BUILTIN("vals")
{
    CHECK_ARGS_IS(1);
    ARG(malHash, hash);
    return hash->values();
}

BUILTIN("vec")
{
    CHECK_ARGS_IS(1);
    ARG(malSequence, s);
    return mal::vector(s->begin(), s->end());
}

BUILTIN("vector")
{
    return mal::vector(argsBegin, argsEnd);
}

BUILTIN("ver")
{
    return mal::string(VERSION);
}

BUILTIN("vl-directory-files")
{
    int count = CHECK_ARGS_AT_LEAST(0);
    int len = 0;
    String path = "./";
    malValueVec* items;
    std::vector<std::filesystem::path> sorted_by_name;

    if (count > 0) {
        std::cout << "count > 0" << std::endl;
        ARG(malString, directory);
        path = directory->value();
        if (!std::filesystem::exists(path.c_str())) {
            return mal::nilValue();
        }
        if (count > 1 && (NIL_PTR || INT_PTR) && !(count == 2 && (NIL_PTR || INT_PTR))) {
            std::cout << "count > 1 && NIL_PTR" << std::endl;
            if (NIL_PTR) {
                argsBegin++;
            }
            // pattern + dirs
            AG_INT(directories);
            switch(directories->value())
            {
                case -1:
                    for (const auto & entry : std::filesystem::directory_iterator(path.c_str())) {
                        if (std::filesystem::is_directory(entry.path()))
                        {
                            sorted_by_name.push_back(entry.path().filename());
                            len++;
                        }
                    }
                    break;
                case 0:
                    for (const auto & entry : std::filesystem::directory_iterator(path.c_str())) {
                        sorted_by_name.push_back(entry.path());
                        len++;
                    }
                    break;
                case 1:
                    for (const auto & entry : std::filesystem::directory_iterator(path.c_str())) {
                        if (!std::filesystem::is_directory(entry.path()))
                        {
                            sorted_by_name.push_back(entry.path().filename());
                            len++;
                        }
                    }
                    break;
                default: {}
            }
        }
        else if (count > 1 && !(count == 2 && (NIL_PTR || INT_PTR))) {
            std::cout << "count > 1 && !(count == 2 && (NIL_PTR || INT_PTR))" << std::endl;
            ARG(malString, pattern);
            int dir = 3;
            if (count > 2) {
                AG_INT(directories2);
                dir = directories2->value();
                if (dir > 1 || dir < -1) {
                    dir = 0;
                }
            }
            // pattern
            bool hasExt = false;
            bool hasName = false;
            String pat = pattern->value();
            int asterix = (int) pat.find_last_of("*");
            if (asterix != -1 && (int) pat.size() >= asterix) {
                hasExt = true;
            }
            if (asterix != -1 && (int) pat.size() >= asterix && pat.size() > pat.substr(asterix+1).size() ) {
                hasName = true;
            }
            for (const auto & entry : std::filesystem::directory_iterator(path.c_str())) {
                if (!std::filesystem::is_directory(entry.path()) &&
                    hasExt &&
                    hasName &&
                    (dir == 3 || dir == 1)) {
                    if ((int)entry.path().filename().string().find(pat.substr(asterix+1)) != -1 &&
                        (int)entry.path().filename().string().find(pat.substr(0, asterix)) != -1) {
                        sorted_by_name.push_back(entry.path().filename());
                        len++;
                    }
                }
                if (!std::filesystem::is_directory(entry.path()) && !hasExt &&
                    (int)entry.path().filename().string().find(pat) != -1 && (dir == 3 || dir == 1)) {
                    sorted_by_name.push_back(entry.path().filename());
                    len++;
                }
                if (std::filesystem::is_directory(entry.path()) && !hasExt &&
                    (int)entry.path().filename().string().find(pat) != -1  && dir == -1) {
                    sorted_by_name.push_back(entry.path().filename());
                    len++;
                }
                if ((int)entry.path().string().find(pat) != -1 && dir == 0) {
                    sorted_by_name.push_back(entry.path());
                    len++;
                }
            }
        }
        else {
            std::cout << "else directory" << std::endl;
            // directory
            for (const auto & entry : std::filesystem::directory_iterator(path.c_str())) {
                if (!std::filesystem::is_directory(entry.path()))
                {
                    sorted_by_name.push_back(entry.path().filename());
                    len++;
                }
            }
        }
    }
    else {
        std::cout << "else current directory" << std::endl;
        // current directory
        for (const auto & entry : std::filesystem::directory_iterator(path.c_str())) {
            if (!std::filesystem::is_directory(entry.path()))
            {
                sorted_by_name.push_back(entry.path().filename());
                len++;
            }
        }
    }
    std::sort(sorted_by_name.begin(), sorted_by_name.end(), compareNat);
    items = new malValueVec(len);
    len = 0;
    for (const auto & filename : sorted_by_name) {
        items->at(len) = mal::string(filename);
        len++;
    }
    return items->size() ? mal::list(items) : mal::nilValue();
}

BUILTIN("vl-file-copy")
{
    int count = CHECK_ARGS_AT_LEAST(2);
    ARG(malString, source);
    ARG(malString, dest);

    if (count == 3 && argsBegin->ptr()->isTrue()) {

        std::ofstream of;
        std::ios_base::openmode openmode =
            std::ios::ate | std::ios::in | std::ios::binary;
        std::ifstream file(source->value().c_str(), openmode);

        if (file.fail()) {
            return mal::nilValue();
        }

        String data;
        data.reserve(file.tellg());
        file.seekg(0, std::ios::beg);
        data.append(std::istreambuf_iterator<char>(file.rdbuf()), std::istreambuf_iterator<char>());

        of.open(dest->value(), std::ios::app);
        if (!of) {
            return mal::nilValue();
        }
        else {
            of << data;
            of.close();
            return mal::integer(sizeof source->value());
        }
    }

    std::error_code err;
    std::filesystem::copy(source->value(), dest->value(), std::filesystem::copy_options::update_existing, err);
    if (err) {
        return mal::nilValue();
    }
    return mal::integer(sizeof source->value());
}

BUILTIN("vl-file-delete")
{
    CHECK_ARGS_IS(1);
    ARG(malString, path);
    if (!std::filesystem::exists(path->value().c_str())) {
        return mal::nilValue();
    }
    if (std::filesystem::remove(path->value().c_str()))
    {
        return mal::trueValue();
    }
    return mal::nilValue();
}

BUILTIN("vl-file-directory-p")
{
    CHECK_ARGS_IS(1);
    ARG(malString, path);
    const std::filesystem::directory_entry dir(path->value().c_str());
    if (std::filesystem::exists(path->value().c_str()) &&
        dir.is_directory()) {
        return mal::trueValue();
    }
    return mal::nilValue();
}

BUILTIN("vl-file-rename")
{
    CHECK_ARGS_IS(2);
    ARG(malString, path);
    ARG(malString, newName);
    if (!std::filesystem::exists(path->value().c_str())) {
        return mal::nilValue();
    }
    std::error_code err;
    std::filesystem::rename(path->value().c_str(), newName->value().c_str(), err);
    if (err) {
        return mal::nilValue();
    }
    return mal::trueValue();
}

BUILTIN("vl-file-size")
{
    CHECK_ARGS_IS(1);
    ARG(malString, path);
    if (!std::filesystem::exists(path->value().c_str())) {
        return mal::nilValue();
    }
    if (!std::filesystem::is_directory(path->value().c_str())) {
        return mal::string("0");
    }
    try {
        [[maybe_unused]] auto size = std::filesystem::file_size(path->value().c_str());
        char str[50];
        sprintf(str, "%ld", size);
        return mal::string(str);
    }
    catch (std::filesystem::filesystem_error&) {}
    return mal::nilValue();
}

BUILTIN("vl-file-systime")
{
    CHECK_ARGS_IS(1);
    ARG(malString, path);
    if (!std::filesystem::exists(path->value().c_str())) {
        return mal::nilValue();
    }

    std::filesystem::file_time_type ftime = std::filesystem::last_write_time(path->value().c_str());
    std::time_t cftime = to_time_t(ftime); // assuming system_clock

    char buffer[64];
    int J,M,W,D,h,m,s;

    if (strftime(buffer, sizeof buffer, "%Y %m %w %e %I %M %S", std::localtime(&cftime))) {
        sscanf (buffer,"%d %d %d %d %d %d %d",&J,&M,&W,&D,&h,&m,&s);

        malValueVec* items = new malValueVec(6);
        items->at(0) = new malInteger(J);
        items->at(1) = new malInteger(M);
        items->at(2) = new malInteger(W);
        items->at(3) = new malInteger(D);
        items->at(4) = new malInteger(m);
        items->at(5) = new malInteger(s);
        return mal::list(items);
    }
    return mal::nilValue();
}

BUILTIN("vl-filename-base")
{
    CHECK_ARGS_IS(1);
    ARG(malString, path);

    const std::filesystem::path p(path->value());
    return mal::string(p.stem());
}

BUILTIN("vl-filename-directory")
{
    CHECK_ARGS_IS(1);
    ARG(malString, path);

    const std::filesystem::path p(path->value());
    if (!p.has_extension()) {
        return mal::string(path->value());
    }

    const auto directory = std::filesystem::path{ p }.parent_path().string();
    return mal::string(directory);
}

BUILTIN("vl-filename-extension")
{
    CHECK_ARGS_IS(1);
    ARG(malString, path);

    const std::filesystem::path p(path->value());
    if (!p.has_extension()) {
        return mal::nilValue();
    }

    return mal::string(p.extension());
}

BUILTIN("vl-mkdir")
{
    CHECK_ARGS_IS(1);
    ARG(malString, dir);

    if(std::filesystem::create_directory(dir->value())) {
        return mal::trueValue();
    }
    return mal::nilValue();
}

BUILTIN("with-meta")
{
    CHECK_ARGS_IS(2);
    malValuePtr obj  = *argsBegin++;
    malValuePtr meta = *argsBegin++;
    return obj->withMeta(meta);
}

BUILTIN("write-line")
{
    int count = CHECK_ARGS_AT_LEAST(1);
    ARG(malString, str);

    if (count == 1)
    {
        return mal::string(str->value());
    }

    ARG(malFile, pf);

    return pf->writeLine(str->value());
}

BUILTIN("write-char")
{
    int count = CHECK_ARGS_AT_LEAST(1);
    AG_INT(c);

    std::cout << itoa64(c->value()) << std::endl;

    if (count == 1)
    {
        return mal::integer(c->value());
    }

    ARG(malFile, pf);

    return pf->writeChar(itoa64(c->value()));
}

BUILTIN("zero?")
{
    CHECK_ARGS_IS(1);

    if (FLOAT_PTR)
    {
        ADD_FLOAT_VAL(*lhs)
        return mal::boolean(lhs->value() == 0.0);
    }
    else
    {
        ADD_INT_VAL(*lhs)
        return mal::boolean(lhs->value() == 0);
    }
}

void installCore(malEnvPtr env) {
    for (auto it = handlers.begin(), end = handlers.end(); it != end; ++it) {
        malBuiltIn* handler = *it;
        env->set(handler->name(), handler);
    }
}

static String printValues(malValueIter begin, malValueIter end,
                          const String& sep, bool readably)
{
    String out;

    if (begin != end) {
        out += (*begin)->print(readably);
        ++begin;
    }

    for ( ; begin != end; ++begin) {
        out += sep;
        out += (*begin)->print(readably);
    }

    return out;
}

static int countValues(malValueIter begin, malValueIter end)
{
    int result = 0;

    if (begin != end) {
        result += (*begin)->print(true).length() -2;
        ++begin;
    }

    for ( ; begin != end; ++begin) {
        result += (*begin)->print(true).length() -2;
    }

    return result;
}
