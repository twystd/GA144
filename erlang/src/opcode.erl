-module(opcode).

% EXPORTS

-export([opcode/1]).
-export([to_string/1]).

% INCLUDES

-include    ("include/opcode.hrl").
-include_lib("eunit/include/eunit.hrl").

% DEFINES

% API

%% @doc Translates a 5 bit value into the equivalent internal op-code
%%      representation.
opcode(16#00) -> ?RET;
opcode(16#02) -> ?JUMP;
opcode(16#03) -> ?CALL;
opcode(16#08) -> ?FETCHP;
opcode(16#0a) -> ?FETCHB;
opcode(16#0e) -> ?STOREB;
opcode(16#0f) -> ?STORE;
opcode(16#11) -> ?SHL;
opcode(16#14) -> ?PLUS;
opcode(16#18) -> ?DUP;
opcode(16#1c) -> ?NOP;
opcode(16#1e) -> ?BSTORE;
opcode(16#1f) -> ?ASTORE;
opcode(X)     -> ?debugFmt("UNKNOWN CODE: ~p~n",[X]), unknown.     

%% @doc Utility function to translate an op-code into a readable string.
%%
to_string(?RET)    -> "RET";
to_string(?JUMP)   -> "JUMP";
to_string(?CALL)   -> "CALL";
to_string(?FETCHP) -> "FETCH-P";
to_string(?FETCHB) -> "FETCH-B";
to_string(?STOREB) -> "STORE-B";
to_string(?STORE)  -> "STORE";
to_string(?SHL)    -> "SHL";
to_string(?PLUS)   -> "PLUS";
to_string(?DUP)    -> "DUP";
to_string(?NOP)    -> "NOP";
to_string(?BSTORE) -> "B-STORE";
to_string(?ASTORE) -> "A-STORE";
to_string(_X)      -> "???".     
