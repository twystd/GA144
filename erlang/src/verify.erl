-module(verify).

% EXPORTS

-export([compare/2,compare/3]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% API

compare(Expected,Trace) ->
   compare(Expected,Trace,noprint).

compare(Expected,Trace,print) ->
   ?debugFmt("EXPECTED: ~p",[Expected]),
   ?debugFmt("TRACE:    ~p",[Trace]),
   compare_impl(Expected,Trace,print);

compare(Expected,Trace,_) ->
   compare_impl(Expected,Trace,noprint).

compare_impl([],[],print) ->
   ?debugMsg("VERIFY/OK"),
   ok;

compare_impl([],[],_) ->
   ok;

compare_impl([H|Expected],[H|Trace],Print) ->
   compare_impl(Expected,Trace,Print);

compare_impl([X|_],[Y|_],print) ->
   io:format(user,"VERIFY/??  EXPECTED:~p  ACTUAL:~p",[X,Y]),
   { failed,{expected,X},{actual,Y}};

compare_impl([X|_],[Y|_],_) ->
   { failed,{expected,X},{actual,Y}};

compare_impl(X,Y,print) ->
   io:format(user,"VERIFY/??  EXPECTED:~p  ACTUAL:~p",[X,Y]),
   { failed,{expected,X},{actual,Y}};

compare_impl(X,Y,_) ->
   io:format(user,"VERIFY/??  EXPECTED:~p  ACTUAL:~p",[X,Y]),
   { failed,{expected,X},{actual,Y}}.
