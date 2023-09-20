#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include "types.h"

MalValue *new_value(enum MalValueType valueType)
{
    MalValue *value = malloc(sizeof(MalValue));
    value->valueType = valueType;
    value->value = NULL;

    return value;
}

MalValue *make_value(enum MalValueType valueType, char *value)
{
    MalValue *mal_value = new_value(valueType);
    mal_value->value = value;

    return mal_value;
}

MalValue *make_list()
{
    return new_value(MAL_LIST);
}

MalValue *make_vector()
{
    return new_value(MAL_VECTOR);
}

MalValue *make_string(char *value)
{
    MalValue *_value = new_value(MAL_STRING);
    size_t len = strlen(value);
    char *result = calloc(len, sizeof(char));

    for (int i = 0, j = 0; i < len; i++, j++)
    {
        if (value[i] == '\\')
        {
            switch (value[i + 1])
            {
            case '\\':
                result[j] = '\\';
                i++;
                break;

            case 'n':
                result[j] = '\n';
                i++;
                break;

            case '"':
                result[j] = '"';
                i++;
                break;

            default:
                result[j] = value[i + 1];
                break;
            }
        }
        else
        {
            result[j] = value[i];
        }
    }

    _value->value = result;
    return _value;
}

void push(MalValue *list, MalValue *value)
{
    assert(list->valueType == MAL_LIST || list->valueType == MAL_VECTOR);

    if (list->list == NULL)
    {
        list->list = malloc(sizeof(MalCell));
        list->list->cdr = NULL;
        list->list->value = value;
        return;
    }

    MalCell *cell = list->list;

    while (cell->cdr != NULL)
    {
        cell = cell->cdr;
    }

    cell->cdr = malloc(sizeof(MalCell));
    cell->cdr->cdr = NULL;
    cell->cdr->value = value;
}