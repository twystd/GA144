-module(opcode).

% EXPORTS

-export([opcode/1]).

% INCLUDES

-include    ("include/opcode.hrl").
-include_lib("eunit/include/eunit.hrl").

% DEFINES

% API

opcode(16#08) ->
   ?FETCHP;

opcode(16#1c) ->
   ?NOP;

opcode(16#1e) ->
   ?BSTORE;

opcode(_) ->
   unknown.     

% EUNIT TESTS
