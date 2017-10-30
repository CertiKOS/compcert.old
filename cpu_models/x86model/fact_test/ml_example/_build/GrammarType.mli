open ParserArg

type __ = Obj.t

type char_p = X86_PARSER_ARG.char_p

val char_dec : X86_PARSER_ARG.char_p -> X86_PARSER_ARG.char_p -> bool

type user_type = X86_PARSER_ARG.user_type

type token_id = X86_PARSER_ARG.token_id

val num_tokens : X86_PARSER_ARG.token_id

val token_id_to_chars : X86_PARSER_ARG.token_id -> X86_PARSER_ARG.char_p list

type coq_type =
| Unit_t
| Char_t
| Void_t
| Pair_t of coq_type * coq_type
| Sum_t of coq_type * coq_type
| List_t of coq_type
| Option_t of coq_type
| User_t of user_type

type interp = __
