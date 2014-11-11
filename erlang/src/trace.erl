-module(trace).

% EXPORTS
%
-export([start/0,stop/0]).
-export([trace/2,snapshot/0]).
-export([extract/2]).
-export([trace/3]).
-export([run/0]).

% INCLUDES

-include    ("include/f18A.hrl").
-include    ("include/opcode.hrl").
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
   trace_impl(is_registered(),Event,Data).

trace_impl(true,Event,Data) ->
   trace ! {trace,{Event,Data}},
   ok;

trace_impl(_,_,_) ->
   ignored.


snapshot() ->
   snapshot(is_registered()).

snapshot(true) ->
   trace ! {snapshot,self()},
   wait(snapshot);

snapshot(_) ->
   [].

extract(Trace,ID) ->
   F = fun(R,A) ->
         case R of
            {f18A,{ID,X}} ->
               [X | A];

            _else -> 
               A
            end
         end,

   lists:reverse(lists:foldl(F,[],Trace)).

%% @doc Extracts the CPU trace information relevant to an opcode. 
%%
trace(f18A,?FETCHP,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,{fetchp,{t,CPU#cpu.t}}});

trace(f18A,?FETCHB,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,{fetchb,{t,CPU#cpu.t}}});     

trace(f18A,?STOREB,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,{storeb,{b,CPU#cpu.b},{t,CPU#cpu.t}}});     

trace(f18A,?PLUS,CPU) ->
   S = CPU#cpu.s,
   T = CPU#cpu.t,   
   trace(f18A,{ CPU#cpu.id,{plus,{s,S},{t,T}}});

trace(f18A,?BSTORE,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,{bstore,{b,CPU#cpu.b}}});     

trace(f18A,?NOP,CPU) ->
   trace(f18A,{ CPU#cpu.id,nop });

trace(f18A,_,CPU) ->
   trace(f18A,{ CPU#cpu.id,unknown }).

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
