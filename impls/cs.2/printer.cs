using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace mal
{
    class printer
    {
        static Dictionary<char, string> ESCAPE = new Dictionary<char, string>()
        {
            {'\n', "\\n"}, {'"', "\\\""}, {'\\', "\\\\"}
        };

        public static string pr_str(MalType malType, bool print_readably = false)
        {
            if (malType is MalList)
            {
                MalList malList = (MalList)malType;
                string closingBracket = (malList.openingBracket == "(") ? ")" : "]";
                List<string> strings = malList.items.Select(it => pr_str(it, print_readably)).ToList();
                string joined = string.Join(" ", strings);
                return string.Format("{0}{1}{2}", malList.openingBracket, joined, closingBracket);
            }
            else if (malType is MalInteger)
            {
                return ((MalInteger)malType).value.ToString();
            }
            else if (malType is MalSymbol)
            {
                return ((MalSymbol)malType).value.ToString();
            }
            else if (malType is MalString)
            {
                if (print_readably)
                {
                    string value = ((MalString)malType).value;
                    StringBuilder output = new StringBuilder();
                    foreach (char c in value)
                    {
                        output.Append(ESCAPE.GetValueOrDefault(c, c.ToString()));
                    }
                    return string.Format("\"{0}\"", output.ToString());
                }
                else
                {
                    return ((MalString)malType).value;
                }
            }
            else if (malType is MalHashmap)
            {
                MalHashmap hashMap = (MalHashmap)malType;
                List<string> strings = new List<string>();
                foreach (var keyValuePair in hashMap.values)
                {
                    strings.Add(pr_str(keyValuePair.Key, true));
                    strings.Add(pr_str(keyValuePair.Value, true));
                }
                string joined = string.Join(" ", strings);
                return string.Format("{0}{1}{2}", "{", joined, "}");
            }
            else if (malType is MalKeyword)
            {
                return ((MalKeyword)malType).name;
            }
            else if (malType is MalFunction)
            {
                return "#<function>";
            }
            else if (malType is MalBoolean)
            {
                return ((MalBoolean)malType).value ? "true" : "false";
            }
            else if (malType is MalNil)
            {
                return "nil";
            }
            else
            {
                throw new Exception(string.Format("Unknown type to print: {0}", malType.ToString()));
            }
        }

    }
}