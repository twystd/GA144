-module(f18A).

% EXPORTS

-export([create/3]).
-export([reset/1,step/1,go/1,stop/1]).
-export([run/1]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% RECORDS

-record(node,{ id,
               pid
             }).

-record(cpu,{ id,
              channel,
              program,
              pc
            }).

% DEFINES

-define(TAG,"F18A").

% API

create(ID,Channel,Program) ->
   CPU = #cpu{ id = ID,
               channel = Channel,
               program = Program,
               pc      = 0
             },

   PID = spawn(f18A,run,[CPU]),

   #node{ id  = ID,
          pid = PID
        }.

reset(Node) ->
   Node#node.pid ! reset,
   ok.

step(Node) ->
   Node#node.pid ! step,
   ok.

go(Node) ->
   Node#node.pid ! go,
   ok.

stop(Node) ->
   Node#node.pid ! stop,
   ok.

% INTERNAL

run(CPU) ->
   loop(CPU).

loop(CPU) ->
   receive
      stop ->
         log:info(?TAG,"STOP"),
         stopped;

      reset ->
         log:info(?TAG,"RESET"),
         loop(CPU#cpu{pc= 0});

      step ->
         log:info(?TAG,"STEP"),
         loop(exec(CPU));

      _any ->
         ?debugFmt("F18A: ~p",[_any]),
         loop(CPU)
      end.

exec(CPU) ->
  ?debugFmt("*** CPU: ~p",[CPU]),
  PC = CPU#cpu.pc + 1,
  CPU#cpu{pc=PC}.

% EUNIT TESTS

step_test() ->
   Ch    = channel:create(1),
   ProgA = [ nop,write,write,write ],
   A     = create(1,Ch,ProgA),
   reset(A),
   step(A),
   step(A),
   step(A),
   stop(A).
