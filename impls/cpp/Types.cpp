#include "Debug.h"
#include "Environment.h"
#include "Types.h"

#include <iostream>
#include <algorithm>
#include <memory>
#include <typeinfo>
#include <math.h>

namespace mal {
    malValuePtr atom(malValuePtr value) {
        return malValuePtr(new malAtom(value));
    };

    malValuePtr boolean(bool value) {
        return value ? trueValue() : falseValue();
    }

    malValuePtr type(MALTYPE type) {
        switch(type) {
            case MALTYPE::ATOM:
                return typeAtom();
            case MALTYPE::BUILTIN:
                return typeBuiltin();
            case MALTYPE::FILE:
                return typeFile();
            case MALTYPE::INT:
                return typeInteger();
            case MALTYPE::LIST:
                return typeList();
            case MALTYPE::MAP:
                return typeMap();
            case MALTYPE::REAL:
                return typeReal();
            case MALTYPE::STR:
                return typeString();
            case MALTYPE::SYM:
                return typeSymbol();
            case MALTYPE::VEC:
                return typeVector();
            case MALTYPE::KEYW:
                return typeKeword();
            default:
                return typeUndef();
        }
    }

    malValuePtr builtin(const String& name, malBuiltIn::ApplyFunc handler) {
        return malValuePtr(new malBuiltIn(name, handler));
    };

    malValuePtr builtin(bool eval, const String& name) {
        return malValuePtr(new malBuiltIn(eval, name));
    };

    malValuePtr falseValue() {
        static malValuePtr c(new malConstant("false"));
        return malValuePtr(c);
    };

    malValuePtr file(const char *path, const char &mode)
    {
        return malValuePtr(new malFile(path, mode));
    };

    malValuePtr hash(const malHash::Map& map) {
        return malValuePtr(new malHash(map));
    }

    malValuePtr hash(malValueIter argsBegin, malValueIter argsEnd,
                     bool isEvaluated) {
        return malValuePtr(new malHash(argsBegin, argsEnd, isEvaluated));
    }

    malValuePtr integer(int64_t value) {
        return malValuePtr(new malInteger(value));
    };

    malValuePtr integer(const String& token) {
        return integer(std::stoi(token));
    };

    malValuePtr keyword(const String& token) {
        return malValuePtr(new malKeyword(token));
    };

    malValuePtr lambda(const StringVec& bindings,
                       malValuePtr body, malEnvPtr env) {
        return malValuePtr(new malLambda(bindings, body, env));
    }

    malValuePtr list(malValueVec* items) {
        return malValuePtr(new malList(items));
    };

    malValuePtr list(malValueIter begin, malValueIter end) {
        return malValuePtr(new malList(begin, end));
    };

    malValuePtr list(malValuePtr a) {
        malValueVec* items = new malValueVec(1);
        items->at(0) = a;
        return malValuePtr(new malList(items));
    }

    malValuePtr list(malValuePtr a, malValuePtr b) {
        malValueVec* items = new malValueVec(2);
        items->at(0) = a;
        items->at(1) = b;
        return malValuePtr(new malList(items));
    }

    malValuePtr list(malValuePtr a, malValuePtr b, malValuePtr c) {
        malValueVec* items = new malValueVec(3);
        items->at(0) = a;
        items->at(1) = b;
        items->at(2) = c;
        return malValuePtr(new malList(items));
    }

    malValuePtr macro(const malLambda& lambda) {
        return malValuePtr(new malLambda(lambda, true));
    };

    malValuePtr nilValue() {
        static malValuePtr c(new malConstant("nil"));
        return malValuePtr(c);
    };

    malValuePtr nullValue() {
        static malValuePtr c(new malConstant(""));
        return malValuePtr(c);
    };

    malValuePtr mdouble(double value)
    {
        return malValuePtr(new malDouble(value));
    };

    malValuePtr mdouble(const String& token)
    {
        return mdouble(std::stof(token));
    };

    malValuePtr piValue() {
        static malValuePtr c(new malDouble(M_PI));
        return malValuePtr(c);
    };

    malValuePtr string(const String& token) {
        return malValuePtr(new malString(token));
    }

    malValuePtr symbol(const String& token) {
        return malValuePtr(new malSymbol(token));
    };

    malValuePtr trueValue() {
        static malValuePtr c(new malConstant("true"));
        return malValuePtr(c);
    };

    malValuePtr typeAtom() {
        static malValuePtr c(new malConstant("ATOM"));
        return malValuePtr(c);
    };
    malValuePtr typeBuiltin() {
        static malValuePtr c(new malConstant("SUBR"));
        return malValuePtr(c);
    };
    malValuePtr typeFile() {
        static malValuePtr c(new malConstant("FILE"));
        return malValuePtr(c);
    };
    malValuePtr typeInteger() {
        static malValuePtr c(new malConstant("INT"));
        return malValuePtr(c);
    };
    malValuePtr typeList() {
        static malValuePtr c(new malConstant("LIST"));
        return malValuePtr(c);
    };
    malValuePtr typeMap() {
        static malValuePtr c(new malConstant("MAP"));
        return malValuePtr(c);
    };
    malValuePtr typeReal() {
        static malValuePtr c(new malConstant("REAL"));
        return malValuePtr(c);
    };
    malValuePtr typeString() {
        static malValuePtr c(new malConstant("STR"));
        return malValuePtr(c);
    };
    malValuePtr typeSymbol() {
        static malValuePtr c(new malConstant("SYM"));
        return malValuePtr(c);
    };
    malValuePtr typeUndef() {
        static malValuePtr c(new malConstant("UNDEF"));
        return malValuePtr(c);
    };
    malValuePtr typeVector() {
        static malValuePtr c(new malConstant("VEC"));
        return malValuePtr(c);
    };
    malValuePtr typeKeword() {
        static malValuePtr c(new malConstant("KEYW"));
        return malValuePtr(c);
    };

    malValuePtr vector(malValueVec* items) {
        return malValuePtr(new malVector(items));
    };

    malValuePtr vector(malValueIter begin, malValueIter end) {
        return malValuePtr(new malVector(begin, end));
    };
};

malValuePtr malBuiltIn::apply(malValueIter argsBegin,
                              malValueIter argsEnd) const
{
    return m_handler(m_name, argsBegin, argsEnd);
}

static String makeHashKey(malValuePtr key)
{
    if (const malString* skey = DYNAMIC_CAST(malString, key)) {
        return skey->print(true);
    }
    else if (const malKeyword* kkey = DYNAMIC_CAST(malKeyword, key)) {
        return kkey->print(true);
    }
    MAL_FAIL("'%s' is not a string or keyword", key->print(true).c_str());
}

static malHash::Map addToMap(malHash::Map& map,
    malValueIter argsBegin, malValueIter argsEnd)
{
    // This is intended to be called with pre-evaluated arguments.
    for (auto it = argsBegin; it != argsEnd; ++it) {
        String key = makeHashKey(*it++);
        map[key] = *it;
    }

    return map;
}

static malHash::Map createMap(malValueIter argsBegin, malValueIter argsEnd)
{
    MAL_CHECK(std::distance(argsBegin, argsEnd) % 2 == 0,
            "hash-map requires an even-sized list");

    malHash::Map map;
    return addToMap(map, argsBegin, argsEnd);
}

malHash::malHash(malValueIter argsBegin, malValueIter argsEnd, bool isEvaluated)
: m_map(createMap(argsBegin, argsEnd))
, m_isEvaluated(isEvaluated)
{

}

malHash::malHash(const malHash::Map& map)
: m_map(map)
, m_isEvaluated(true)
{

}

malValuePtr
malHash::assoc(malValueIter argsBegin, malValueIter argsEnd) const
{
    MAL_CHECK(std::distance(argsBegin, argsEnd) % 2 == 0,
            "assoc requires an even-sized list");

    malHash::Map map(m_map);
    return mal::hash(addToMap(map, argsBegin, argsEnd));
}

bool malHash::contains(malValuePtr key) const
{
    auto it = m_map.find(makeHashKey(key));
    return it != m_map.end();
}

malValuePtr
malHash::dissoc(malValueIter argsBegin, malValueIter argsEnd) const
{
    malHash::Map map(m_map);
    for (auto it = argsBegin; it != argsEnd; ++it) {
        String key = makeHashKey(*it);
        map.erase(key);
    }
    return mal::hash(map);
}

malValuePtr malHash::eval(malEnvPtr env)
{
    if (m_isEvaluated) {
        return malValuePtr(this);
    }

    malHash::Map map;
    for (auto it = m_map.begin(), end = m_map.end(); it != end; ++it) {
        map[it->first] = EVAL(it->second, env);
    }
    return mal::hash(map);
}

malValuePtr malHash::get(malValuePtr key) const
{
    auto it = m_map.find(makeHashKey(key));
    return it == m_map.end() ? mal::nilValue() : it->second;
}

malValuePtr malHash::keys() const
{
    malValueVec* keys = new malValueVec();
    keys->reserve(m_map.size());
    for (auto it = m_map.begin(), end = m_map.end(); it != end; ++it) {
        if (it->first[0] == '"') {
            keys->push_back(mal::string(unescape(it->first)));
        }
        else {
            keys->push_back(mal::keyword(it->first));
        }
    }
    return mal::list(keys);
}

malValuePtr malHash::values() const
{
    malValueVec* keys = new malValueVec();
    keys->reserve(m_map.size());
    for (auto it = m_map.begin(), end = m_map.end(); it != end; ++it) {
        keys->push_back(it->second);
    }
    return mal::list(keys);
}

String malHash::print(bool readably) const
{
    String s = "{";

    auto it = m_map.begin(), end = m_map.end();
    if (it != end) {
        s += it->first + " " + it->second->print(readably);
        ++it;
    }
    for ( ; it != end; ++it) {
        s += " " + it->first + " " + it->second->print(readably);
    }

    return s + "}";
}

bool malHash::doIsEqualTo(const malValue* rhs) const
{
    const malHash::Map& r_map = static_cast<const malHash*>(rhs)->m_map;
    if (m_map.size() != r_map.size()) {
        return false;
    }

    for (auto it0 = m_map.begin(), end0 = m_map.end(), it1 = r_map.begin();
         it0 != end0; ++it0, ++it1) {

        if (it0->first != it1->first) {
            return false;
        }
        if (!it0->second->isEqualTo(it1->second.ptr())) {
            return false;
        }
    }
    return true;
}

malLambda::malLambda(const StringVec& bindings,
                     malValuePtr body, malEnvPtr env)
: m_bindings(bindings)
, m_body(body)
, m_env(env)
, m_isMacro(false)
{

}

malLambda::malLambda(const malLambda& that, malValuePtr meta)
: malApplicable(meta)
, m_bindings(that.m_bindings)
, m_body(that.m_body)
, m_env(that.m_env)
, m_isMacro(that.m_isMacro)
{

}

malLambda::malLambda(const malLambda& that, bool isMacro)
: malApplicable(that.m_meta)
, m_bindings(that.m_bindings)
, m_body(that.m_body)
, m_env(that.m_env)
, m_isMacro(isMacro)
{

}

malValuePtr malLambda::apply(malValueIter argsBegin,
                             malValueIter argsEnd) const
{
    return EVAL(m_body, makeEnv(argsBegin, argsEnd));
}

malValuePtr malLambda::doWithMeta(malValuePtr meta) const
{
    return new malLambda(*this, meta);
}

malEnvPtr malLambda::makeEnv(malValueIter argsBegin, malValueIter argsEnd) const
{
    return malEnvPtr(new malEnv(m_env, m_bindings, argsBegin, argsEnd));
}

malValuePtr malList::conj(malValueIter argsBegin,
                          malValueIter argsEnd) const
{
    int oldItemCount = std::distance(begin(), end());
    int newItemCount = std::distance(argsBegin, argsEnd);

    malValueVec* items = new malValueVec(oldItemCount + newItemCount);
    std::reverse_copy(argsBegin, argsEnd, items->begin());
    std::copy(begin(), end(), items->begin() + newItemCount);

    return mal::list(items);
}

malValuePtr malList::eval(malEnvPtr env)
{
    // Note, this isn't actually called since the TCO updates, but
    // is required for the earlier steps, so don't get rid of it.
    if (count() == 0) {
        return malValuePtr(this);
    }

    std::unique_ptr<malValueVec> items(evalItems(env));
    auto it = items->begin();
    malValuePtr op = *it;
    return APPLY(op, ++it, items->end());
}

String malList::print(bool readably) const
{
    return '(' + malSequence::print(readably) + ')';
}

malValuePtr malValue::eval(malEnvPtr env)
{
    // Default case of eval is just to return the object itself.
    return malValuePtr(this);
}

bool malValue::isEqualTo(const malValue* rhs) const
{
    // Special-case. Vectors and Lists can be compared.
    bool matchingTypes = (typeid(*this) == typeid(*rhs)) ||
        (dynamic_cast<const malSequence*>(this) &&
         dynamic_cast<const malSequence*>(rhs))          ||
        (dynamic_cast<const malInteger*>(this) &&
         dynamic_cast<const malDouble*>(rhs))          ||
        (dynamic_cast<const malDouble*>(this) &&
         dynamic_cast<const malInteger*>(rhs));

    return matchingTypes && doIsEqualTo(rhs);
}

bool malValue::isTrue() const
{
    return (this != mal::falseValue().ptr())
        && (this != mal::nilValue().ptr());
}

malValuePtr malValue::meta() const
{
    return m_meta.ptr() == NULL ? mal::nilValue() : m_meta;
}

malValuePtr malValue::withMeta(malValuePtr meta) const
{
    return doWithMeta(meta);
}

malSequence::malSequence(malValueVec* items)
: m_items(items)
{

}

malSequence::malSequence(malValueIter begin, malValueIter end)
: m_items(new malValueVec(begin, end))
{

}

malSequence::malSequence(const malSequence& that, malValuePtr meta)
: malValue(meta)
, m_items(new malValueVec(*(that.m_items)))
{

}

malSequence::~malSequence()
{
    delete m_items;
}

bool malSequence::doIsEqualTo(const malValue* rhs) const
{
    const malSequence* rhsSeq = static_cast<const malSequence*>(rhs);
    if (count() != rhsSeq->count()) {
        return false;
    }

    for (malValueIter it0 = m_items->begin(),
                      it1 = rhsSeq->begin(),
                      end = m_items->end(); it0 != end; ++it0, ++it1) {

        if (! (*it0)->isEqualTo((*it1).ptr())) {
            return false;
        }
    }
    return true;
}

malValueVec* malSequence::evalItems(malEnvPtr env) const
{
    malValueVec* items = new malValueVec;;
    items->reserve(count());
    for (auto it = m_items->begin(), end = m_items->end(); it != end; ++it) {
        items->push_back(EVAL(*it, env));
    }
    return items;
}

malValuePtr malSequence::first() const
{
    return count() == 0 ? mal::nilValue() : item(0);
}

String malSequence::print(bool readably) const
{
    String str;
    auto end = m_items->cend();
    auto it = m_items->cbegin();
    if (it != end) {
        str += (*it)->print(readably);
        ++it;
    }
    for ( ; it != end; ++it) {
        str += " ";
        str += (*it)->print(readably);
    }
    return str;
}

bool malSequence::isDotted() const
{
    return ((count() == 3) && (m_items->at(1)->print(true).compare(".") == 0)) ? true : false;
}

malValuePtr malSequence::rest() const
{
    malValueIter start = (count() > 0) ? begin() + 1 : end();
    return mal::list(start, end());
}

malValuePtr malSequence::dotted() const
{
    return isDotted() == true ? item(2) : mal::nilValue();
}

malValuePtr malSequence::reverse(malValueIter argsBegin, malValueIter argsEnd) const
{
    malValueVec* items = new malValueVec(std::distance(argsBegin, argsEnd));
    std::reverse_copy(argsBegin, argsEnd, items->begin());
    return mal::list(items);
}

String malString::escapedValue() const
{
    return escape(value());
}

String malString::print(bool readably) const
{
    return readably ? escapedValue() : value();
}

malValuePtr malSymbol::eval(malEnvPtr env)
{
    return env->get(value());
}

malValuePtr malVector::conj(malValueIter argsBegin,
                            malValueIter argsEnd) const
{
    int oldItemCount = std::distance(begin(), end());
    int newItemCount = std::distance(argsBegin, argsEnd);

    malValueVec* items = new malValueVec(oldItemCount + newItemCount);
    std::copy(begin(), end(), items->begin());
    std::copy(argsBegin, argsEnd, items->begin() + oldItemCount);

    return mal::vector(items);
}

malValuePtr malVector::eval(malEnvPtr env)
{
    return mal::vector(evalItems(env));
}

String malVector::print(bool readably) const
{
    return '[' + malSequence::print(readably) + ']';
}

bool malInteger::doIsEqualTo(const malValue* rhs) const
{
    return m_value == static_cast<const malInteger*>(rhs)->m_value
    || double(m_value) == static_cast<const malDouble*>(rhs)->value();
}

bool malDouble::doIsEqualTo(const malValue* rhs) const
{
    return m_value == static_cast<const malDouble*>(rhs)->m_value
    || m_value == double(static_cast<const malInteger*>(rhs)->value());
}

malValuePtr malFile::open()
{
    switch(m_mode)
    {
        case 'w':
            m_value = fopen(m_path.c_str(), "w");
            break;

        case 'r':
            m_value = fopen(m_path.c_str(), "r");
            break;

        case 'a':
            m_value = fopen(m_path.c_str(), "a");
            break;
        default:
            return mal::nilValue();
    }

    if (m_value == NULL)
    {
        return mal::nilValue();
    }
    return this;
}

malValuePtr malFile::close()
{
    MAL_CHECK(fclose(m_value) == 0,
              "i/o can not close file");
    return mal::nilValue();
}

malValuePtr malFile::writeLine (const String &line)
{
    MAL_CHECK(fprintf(m_value, "%s\n", line.c_str()) > 0,
              "i/o can not write to file");

    return mal::string(line);
}

malValuePtr malFile::writeChar(const char &c)
{
    MAL_CHECK(fputc(c, m_value) > -1,
              "i/o can not write to file");
    return mal::integer(c);
}

malValuePtr malFile::readLine()
{
    char buf[8192];
    if (fgets(buf, sizeof(buf), m_value))
    {
         return mal::string(buf);
    }
    return mal::nilValue();
}

malValuePtr malFile::readChar()
{
    return mal::integer(fgetc(m_value));
}

