-module(util).

% EXPORTS

-export([is_registered/1,unregister/1]).

% API

is_registered(ID) ->
   is_registered(ID,whereis(ID)).

is_registered(_,undefined) ->
   false;

is_registered(_,_) ->
   true.

unregister(ID) ->
   unregister(ID,whereis(ID)).

unregister(_,undefined) ->
   ok;

unregister(ID,_) ->
   erlang:unregister(ID).
