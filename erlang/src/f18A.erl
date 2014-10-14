-module(f18A).

% EXPORTS

-export([create/3]).
-export([reset/1,go/1]).
-export([step/1,step/2]).
-export([stop/1,stop/2]).
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
               pc      = 1
             },

   PID = spawn(f18A,run,[CPU]),

   #node{ id  = ID,
          pid = PID
        }.

reset(Node) ->
   Node#node.pid ! reset,
   ok.

step(Node) ->
   step(Node,nowait).

step(Node,wait) ->
   Node#node.pid ! { step,self() },
   wait(stepped);

step(Node,_) ->
   Node#node.pid ! step,
   ok.

go(Node) ->
   Node#node.pid ! go,
   ok.

stop(Node) ->
  stop(Node,nowait).

stop(Node,wait) ->
   Node#node.pid ! { stop,self() },
   wait(stopped);

stop(Node,_) ->
   Node#node.pid ! stop,
   ok.

wait(Event) ->
   receive 
      stopped ->
          ok;

      _ ->
         wait(Event)
   end.

% INTERNAL

run(CPU) ->
   loop(CPU).

loop(CPU) ->
   receive
      reset ->
         log:info(?TAG,"RESET"),
         trace:trace(f18A,{ CPU#cpu.id,reset}),     
         loop(CPU#cpu{pc=1});

      step ->
         log:info(?TAG,"STEP"),
         loop(exec(CPU));

      {step,PID} ->
         log:info(?TAG,"STEP"),
         PID ! stepped,
         loop(exec(CPU));

      stop ->
         log:info(?TAG,"STOP"),
         trace:trace(f18A,{ CPU#cpu.id,stop}),     
         stopped;

      {stop,PID} ->
         log:info(?TAG,"STOP"),
         trace:trace(f18A,{ CPU#cpu.id,stop}),     
         PID ! stopped,
         stopped;

      go ->
         log:info(?TAG,"GO"),
         loop(CPU);

      _any ->
         ?debugFmt("F18A: ~p",[_any]),
         loop(CPU)
      end.

exec(CPU) ->
   PC     = CPU#cpu.pc,     
   OpCode = lists:nth(PC,CPU#cpu.program),
   exec(CPU,OpCode).

exec(CPU,nop) ->
   log:info(?TAG,"NOP"),     
   trace:trace(f18A,CPU),     
   PC  = CPU#cpu.pc + 1,
   CPU#cpu{pc=PC};

exec(CPU,{write,Word}) ->
   log:info(?TAG,"WRITE"),
   trace:trace(f18A,CPU),
   M = self(),     
   spawn(fun() ->
            channel:write(CPU#cpu.channel,Word),
            M ! written
         end,[]),

   case exec_wait(written) of
      ok ->
         log:debug(?TAG,"EXEC_WAIT/OK"),
         PC  = CPU#cpu.pc + 1,
         CPU#cpu{pc=PC};

      stop ->
         log:debug(?TAG,"EXEC_WAIT/STOP"),
         stop;

      {stop,PID} ->
         log:debug(?TAG,"EXEC_WAIT/STOP:PID"),
         {stop,PID}
      end;    
   
exec(CPU,OpCode) ->
   log:warn(?TAG,"UNIMPLEMENTED OPCODE: ~p~n",[OpCode]),
   PC  = CPU#cpu.pc + 1,
   CPU#cpu{pc=PC}.

exec_wait(Event) ->
   receive
      Event ->
         ok;

      stop ->
         stop;

      {stop,PID} ->
         {stop,PID};

      _else ->
         exec_wait(Event)
      end.

% EUNIT TESTS

write_testx() ->
   M    = self(),
   Ch   = channel:create(1),
   Prog = [ {write,678} ],
   F18A = create(1,Ch,Prog),

   spawn(fun() -> 
            reset(F18A),
            step (F18A),
            stop (F18A),
            M ! { a,ok } 
         end),

   spawn(fun() -> 
            M ! { b,channel:read (Ch) } 
         end),

   ?assertEqual({ok,{ok,678}},wait(undefined,undefined)).

step_test() ->
   trace:start(),
   Ch   = channel:create(1),
   Prog = [ {write,123} ],
   F18A = create(1,Ch,Prog),
   reset(F18A),
   step (F18A),
   stop (F18A,wait),
   trace:stop().

wait({a,X},{b,Y}) ->
   {X,Y};

wait(X,Y) ->
   receive 
      { a,A } ->
         wait({a,A},Y);

      { b,B } ->
         wait(X,{b,B});

      _any ->
         wait(X,Y)
   end.

