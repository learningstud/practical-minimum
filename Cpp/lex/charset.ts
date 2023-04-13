type basic_source_character_set =
    | " " | "\t" | "\v" | "\f" | "\n"

    | "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m"
    | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z"

    | "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" | "K" | "L" | "M"
    | "N" | "O" | "P" | "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X" | "Y" | "Z"

    | "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"

    | "_" | "{" | "}" | "[" | "]" | "#" | "(" | ")" | "<" | ">" | "%" | ":" | ";"
    | "." | "?" | "*" | "+" | "-" | "/" | "^" | "&" | "|" | "~" | "!" | "=" | ","
    | "\\" | '"' | "'"

type hexadecimal_digit =
    | "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
    | "a" | "b" | "c" | "d" | "e" | "f"
    | "A" | "B" | "C" | "D" | "E" | "F"

type hex_quad = string
    // `${hexadecimal_digit}${hexadecimal_digit}${hexadecimal_digit}${hexadecimal_digit}`
    // [hexadecimal_digit, hexadecimal_digit, hexadecimal_digit, hexadecimal_digit]

type universal_character_name =
    | `\\u${hex_quad}`
    | `\\U${hex_quad}${hex_quad}`