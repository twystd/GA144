-module(verify).

% EXPORTS

-export([compare/2]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% API

compare(Expected,Trace) ->
   ?debugFmt("EXPECTED: ~p",[Expected]),
   ?debugFmt("TRACE:    ~p",[Trace]),
   compare_impl(Expected,Trace).

compare_impl([],[]) ->
   ?debugMsg("VERIFY/OK"),
   ok;

compare_impl([H|Expected],[H|Trace]) ->
   compare_impl(Expected,Trace);

compare_impl([X|_],[Y|_]) ->
   io:format(user,"VERIFY/??  EXPECTED:~p  ACTUAL:~p",[X,Y]),
   { failed,{expected,X},{actual,Y}};

compare_impl(X,Y) ->
   io:format(user,"VERIFY/??  EXPECTED:~p  ACTUAL:~p",[X,Y]),
   { failed,{expected,X},{actual,Y}}.
