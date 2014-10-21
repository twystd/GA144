-module(verify).

% EXPORTS

-export([compare/2,compare/3]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% API

compare(Expected,Trace) ->
   compare(Expected,Trace,noprint).

compare(Expected,Trace,print) ->
   ?debugFmt("EXPECTED: ~p~n",[Expected]),
   ?debugFmt("TRACE:    ~p~n",[Trace]),
   compare_impl(Expected,Trace,print);

compare(Expected,Trace,_) ->
   compare_impl(Expected,Trace,noprint).

compare_impl([],[],print) ->
   ?debugMsg("VERIFY/OK"),
   ok;

compare_impl([],[],_) ->
   ok;

compare_impl([X|_],[],print) ->
   io:format(user,"VERIFY/?  EXPECTED:~p  ACTUAL:~p~n",[X,none]),
   { failed,{expected,X},{actual,none}};

compare_impl([X|_],[],_) ->
   { failed,{expected,X},{actual,none}};

compare_impl([],[Y|_],print) ->
   io:format(user,"VERIFY/?  EXPECTED:~p  ACTUAL:~p~n",[none,Y]),
   { failed,{expected,none},{actual,Y}};

compare_impl([],[Y|_],_) ->
   { failed,{expected,none},{actual,Y}};

compare_impl([H|Expected],[H|Trace],Print) ->
   compare_impl(Expected,Trace,Print);

compare_impl([X|_],[Y|_],print) ->
   io:format(user,"VERIFY/?  EXPECTED:~p  ACTUAL:~p~n",[X,Y]),
   { failed,{expected,X},{actual,Y}};

compare_impl([X|_],[Y|_],_) ->
   { failed,{expected,X},{actual,Y}};

compare_impl(X,Y,print) ->
   io:format(user,"VERIFY/?  EXPECTED:~p  ACTUAL:~p~n",[X,Y]),
   { failed,{expected,X},{actual,Y}};

compare_impl(X,Y,_) ->
   io:format(user,"VERIFY/?  EXPECTED:~p  ACTUAL:~p~n",[X,Y]),
   { failed,{expected,X},{actual,Y}}.
