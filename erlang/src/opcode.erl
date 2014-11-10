-module(opcode).

% EXPORTS

-export([opcode/1]).
-export([to_string/1]).

% INCLUDES

-include    ("include/opcode.hrl").
-include_lib("eunit/include/eunit.hrl").

% DEFINES

% API

opcode(16#08) ->
   ?FETCHP;

opcode(16#0a) ->
   ?FETCHB;

opcode(16#0e) ->
   ?STOREB;

opcode(16#1c) ->
   ?NOP;

opcode(16#14) ->
   ?PLUS;

opcode(16#1e) ->
   ?BSTORE;

opcode(X) ->
   ?debugFmt("UKNOWN CODE: ~p~n",[X]),
   unknown.     


to_string(?FETCHP) ->
   "FETCH-P";

to_string(?FETCHB) ->
   "FETCH-B";

to_string(?STOREB) ->
   "STORE-B";

to_string(?NOP) ->
   "NOP";

to_string(?PLUS) ->
   "PLUS";

to_string(?BSTORE) ->
   "B-STORE";

to_string(_) ->
   "???".     

% EUNIT TESTS
