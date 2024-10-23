#include "Environment.h"
#include "Types.h"

#include <iostream>
#include <algorithm>

malEnv::malEnv(malEnvPtr outer)
: m_outer(outer)
{
    TRACE_ENV("Creating malEnv %p, outer=%p\n", this, m_outer.ptr());
}

malEnv::malEnv(malEnvPtr outer, const StringVec& bindings,
               malValueIter argsBegin, malValueIter argsEnd)
: m_outer(outer)
{
    TRACE_ENV("Creating malEnv %p, outer=%p\n", this, m_outer.ptr());
    setLamdaMode(true);
    int n = bindings.size();

    auto it = argsBegin;
    int currArg = 0;
    for (int i = 0; i < n; i++) {
        currArg = i;
        if (bindings[i] == "&" ||
            bindings[i] == "/"
        ) {
            MAL_CHECK(i <= n - 2, "There must be one parameter after the &");
            currArg++;
            break;
        }
        MAL_CHECK(it != argsEnd, "Not enough parameters");
        set(bindings[i], *it);
        ++it;
    }
    MAL_CHECK(it == argsEnd, "Too many parameters");

    for (int i = currArg; i < n; i++) {
        m_bindings.push_back(bindings[i]);
        set(bindings[i], mal::nilValue());
    }
}

malEnv::~malEnv()
{
    TRACE_ENV("Destroying malEnv %p, outer=%p\n", this, m_outer.ptr());
}

malEnvPtr malEnv::find(const String& symbol)
{
    for (malEnvPtr env = this; env; env = env->m_outer) {
        if (env->m_map.find(symbol) != env->m_map.end()) {
            return env;
        }
    }
    return NULL;
}

malValuePtr malEnv::get(const String& symbol)
{
    for (malEnvPtr env = this; env; env = env->m_outer) {
        auto it = env->m_map.find(symbol);
        if (it != env->m_map.end()) {
            return it->second;
        }
    }
    MAL_FAIL("'%s' not found", symbol.c_str());
}

malValuePtr malEnv::set(const String& symbol, malValuePtr value)
{
    if (isLamda()) {
        for (auto &it : m_bindings) {
            if (symbol == it) {
                m_map[symbol] = value;
                return value;
            }
        }
        m_outer.ptr()->set(symbol, value);
    }
    else {
        m_map[symbol] = value;
    }
    return value;
}

malEnvPtr malEnv::getRoot()
{
    // Work our way down the the global environment.
    for (malEnvPtr env = this; ; env = env->m_outer) {
        if (!env->m_outer) {
            return env;
        }
    }
}
