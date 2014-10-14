-module(trace).

% EXPORTS
%
-export([start/0,stop/0]).
-export([trace/2]).
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
   trace ! stop;

stop(_) ->
   ok.

trace(Event,Data) ->
   trace(is_registered(),Event,Data).

trace(true,Event,Data) ->
   trace ! {trace,{Event,Data}},
   ok;

trace(_,_,_) ->
   ignored.

% INTERNAL

is_registered() ->
   lists:foldl(fun(X,A) -> 
                  case X of 
                     trace -> true;
                    _else  -> A
                     end
               end,false,registered()).  

run() ->
   loop().

loop() ->
   receive
      stop ->
         unregister(trace),
         ok;

      {trace,Event} ->
         ?debugFmt("TRACE  ~p",[Event]),
         loop();

       _any ->
         loop()
   end.
