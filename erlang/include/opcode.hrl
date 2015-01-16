% OPCODE CONSTANTS
%
-define(RET,       16#00).
-define(EX,        16#01).
-define(JUMP,      16#02).
-define(CALL,      16#03).

-define(NEXT,      16#05).
-define(IF,        16#06).
-define(MINUSIF,   16#07).
-define(FETCHP,    16#08).
-define(FETCH_PLUS,16#09).
-define(FETCHB,    16#0a).
-define(FETCH,     16#0b).
-define(STOREP,    16#0c).
-define(STORE_PLUS,16#0d).
-define(STOREB,    16#0e).
-define(STORE,     16#0f).
-define(MULTIPLY,  16#10).
-define(SHL,       16#11).
-define(SHR,       16#12).
-define(NOT,       16#13).
-define(PLUS,      16#14).
-define(AND,       16#15).
-define(OR,        16#16).
-define(DROP,      16#17).
-define(DUP,       16#18).
-define(POP,       16#19).
-define(OVER,      16#1a).
-define(A,         16#1b).
-define(NOP,       16#1c).
-define(PUSH,      16#1d).
-define(BSTORE,    16#1e).
-define(ASTORE,    16#1f).
