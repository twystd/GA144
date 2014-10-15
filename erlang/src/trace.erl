-module(trace).

% EXPORTS
%
-export([start/0,stop/0]).
-export([trace/2,snapshot/0]).
-export([run/0]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% RECORDS

% API

start() ->
   start(is_registered()).

start(true) ->
   ok;

start(_) ->
   PID = spawn(trace,run,[]),
   register(trace,PID),
   ok.

stop() ->
   stop(is_registered()).

stop(true) ->
   trace ! {stop,self()},
   wait(stop);

stop(_) ->
   [].

trace(Event,Data) ->
   trace(is_registered(),Event,Data).

trace(true,Event,Data) ->
   trace ! {trace,{Event,Data}},
   ok;

trace(_,_,_) ->
   ignored.

snapshot() ->
   snapshot(is_registered()).

snapshot(true) ->
   trace ! {snapshot,self()},
   wait(snapshot);

snapshot(_) ->
   [].

% INTERNAL

is_registered() ->
   lists:foldl(fun(X,A) -> 
                  case X of 
                     trace -> true;
                    _else  -> A
                     end
               end,false,registered()).  

wait(Event) ->
   receive 
      {Event,Snapshot} ->
         Snapshot;

      _any ->
         wait(Event)
   end.

run() ->
   loop([]).

loop(Trace) ->
   receive
      {stop,PID} ->
         unregister(trace),
         PID ! {stop,lists:reverse(Trace)},
         ok;

      {trace,Event} ->
         loop([Event | Trace]);

      {snapshot,PID} ->
         PID ! {snapshot,lists:reverse(Trace)},
         loop(Trace);

       _any ->
         loop(Trace)
   end.
