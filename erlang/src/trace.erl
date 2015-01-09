-module(trace).

% EXPORTS
%
-export([start/0,stop/0]).
-export([trace/2,snapshot/0]).
-export([extract/2,extract/3]).
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
            {ID,X} ->
               [X | A];

            _else -> 
               A
            end
         end,

   lists:reverse(lists:foldl(F,[],Trace)).

extract(Trace,f18A,ID) ->
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
trace(f18A,?RET,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,{ret,{p,CPU#cpu.p},{r,CPU#cpu.r},{rs,CPU#cpu.rs},{i,CPU#cpu.i}}});

trace(f18A,?JUMP,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,{jump,{p,CPU#cpu.p}}});

trace(f18A,?CALL,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,{call,{p,CPU#cpu.p}}});

trace(f18A,?FETCHP,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,{fetchp,{t,CPU#cpu.t}}});

trace(f18A,?FETCHB,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,{fetchb,{t,CPU#cpu.t}}});     

trace(f18A,?STORE_PLUS,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,{store_plus,{a,CPU#cpu.a},{t,CPU#cpu.t}}});     

trace(f18A,?STOREB,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,{storeb,{b,CPU#cpu.b},{t,CPU#cpu.t}}});     

trace(f18A,?STORE,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,{store,{a,CPU#cpu.a},{t,CPU#cpu.t}}});     

trace(f18A,?MULTIPLY,CPU) ->
   T = CPU#cpu.t,   
   trace(f18A,{ CPU#cpu.id,{multiply,{t,T}}});

trace(f18A,?SHL,CPU) ->
   T = CPU#cpu.t,   
   trace(f18A,{ CPU#cpu.id,{shl,{t,T}}});

trace(f18A,?SHR,CPU) ->
   T = CPU#cpu.t,   
   trace(f18A,{ CPU#cpu.id,{shr,{t,T}}});

trace(f18A,?NOT,CPU) ->
   T = CPU#cpu.t,   
   trace(f18A,{ CPU#cpu.id,{'not',{t,T}}});

trace(f18A,?PLUS,CPU) ->
   S = CPU#cpu.s,
   T = CPU#cpu.t,   
   trace(f18A,{ CPU#cpu.id,{plus,{s,S},{t,T}}});

trace(f18A,?AND,CPU) ->
   S = CPU#cpu.s,
   T = CPU#cpu.t,   
   trace(f18A,{ CPU#cpu.id,{'and',{t,T},{s,S},{ds,CPU#cpu.ds}}});

trace(f18A,?OR,CPU) ->
   S = CPU#cpu.s,
   T = CPU#cpu.t,   
   trace(f18A,{ CPU#cpu.id,{'or',{t,T},{s,S},{ds,CPU#cpu.ds}}});

trace(f18A,?DROP,CPU) ->
   S = CPU#cpu.s,
   T = CPU#cpu.t,   
   trace(f18A,{ CPU#cpu.id,{drop,{t,T},{s,S},{ds,CPU#cpu.ds}}});

trace(f18A,?DUP,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,dup});     

trace(f18A,?POP,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,pop});     

trace(f18A,?OVER,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,over});

trace(f18A,?A,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,a});

trace(f18A,?NOP,CPU) ->
   trace(f18A,{ CPU#cpu.id,nop });

trace(f18A,?PUSH,CPU) ->
   trace(f18A,{ CPU#cpu.id,push });

trace(f18A,?BSTORE,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,{bstore,{b,CPU#cpu.b}}});     

trace(f18A,?ASTORE,CPU) ->
   trace:trace(f18A,{ CPU#cpu.id,{astore,{a,CPU#cpu.a}}});     

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
