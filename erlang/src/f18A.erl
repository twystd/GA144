-module(f18A).

% EXPORTS

-export([create/3]).
-export([reset/1,reset/2]).
-export([go/1]).
-export([stop/1,stop/2]).
-export([step/1,step/2]).
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

%% @doc Initialises an F18A node and starts the internal instruction 
%%      execution process.
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

%% @doc Issues a RESET command to the F18A node and returns immediately.
%%
reset(F18A) ->
   F18A#node.pid ! reset.

reset(F18A,wait) ->
   F18A#node.pid ! {reset,self() },
   reset_wait().

reset_wait() ->
   receive
      reset -> ok;
      _     -> reset_wait()
   end.
  
 
%% @doc Issues a STEP command to the F18A node and returns immediately.
%%
step(F18A) ->
   F18A#node.pid ! step.

step(F18A,wait) ->
   F18A#node.pid ! { step,self() },
   step_wait().

step_wait() ->
   receive
      step -> ok;
      _    -> step_wait()
   end.


%% @doc Issues a GO command to the F18A node and returns immediately.
%%
go(F18A) ->
   F18A#node.pid ! go,
   ok.


%% @doc Issues a STOP command to the F18A node and returns immediately.
%%
stop(F18A) ->
   F18A#node.pid ! stop.

stop(F18A,wait) ->
   F18A#node.pid ! { stop,self() },
   stop_wait().

stop_wait() ->
   receive
      stopped -> ok;
      _       -> stop_wait()
   end.

% INTERNAL

run(CPU) ->
   loop({run,CPU}).

loop({stop,_CPU}) ->
   stopped;

loop({error,_CPU}) ->
   stopped;

loop({run,CPU}) ->
   receive
      reset ->
         log:info(?TAG,"RESET"),
         trace:trace(f18A,{ CPU#cpu.id,reset}),     
         loop({run,CPU#cpu{pc=1}});

      {reset,PID} ->
         log:info(?TAG,"RESET/W"),
         trace:trace(f18A,{ CPU#cpu.id,reset}),     
         PID ! reset,
         loop({run,CPU#cpu{pc=1}});

      step ->
         log:info(?TAG,"STEP"),
         loop(step_impl(CPU));

      {step,PID} ->
         log:info(?TAG,"STEP/W"),
         Next = step_impl(CPU),
         PID ! step,
         loop(Next);

      stop ->
         log:info(?TAG,"STOP"),
         trace:trace(f18A,{ CPU#cpu.id,stop}),     
         stopped;

      {stop,PID} ->
         log:info(?TAG,"STOP/W"),
         trace:trace(f18A,{ CPU#cpu.id,stop}),     
         PID ! stopped,
         stopped;

      go ->
         log:info(?TAG,"GO"),
         loop({run,CPU});

      _any ->
         ?debugFmt("??? F18A: ~p",[_any]),
         loop({run,CPU})
      end.

step_impl(CPU) ->
   case exec(CPU) of
      {ok,CPUX} ->
         {run,CPUX};

      {stop,PID} ->
         trace:trace(f18A,{ CPU#cpu.id,stop}),     
         PID ! stopped,
         {stop,CPU};

      _any ->   
         log:error(?TAG,"STEP/? : ~p",[_any]),
         {error,CPU}
   end.

exec(CPU) ->
   PC     = CPU#cpu.pc,     
   OpCode = lists:nth(PC,CPU#cpu.program),
   exec(CPU,OpCode).

exec(CPU,nop) ->
   log:info(?TAG,"NOP"),     
   trace:trace(f18A,{ CPU#cpu.id,nop }),     
   PC  = CPU#cpu.pc + 1,
   {ok,CPU#cpu{pc=PC}};

exec(CPU,read) ->
   read(CPU);

exec(CPU,{write,Word}) ->
   write(CPU,Word);
   
exec(CPU,OpCode) ->
   log:warn(?TAG,"UNIMPLEMENTED OPCODE: ~p~n",[OpCode]),
   PC  = CPU#cpu.pc + 1,
   {ok,CPU#cpu{pc=PC}}.

% READ

read(CPU) ->
   log:info(?TAG,"READ"),
   trace:trace(f18A,{ CPU#cpu.id,read}),     
   M  = self(),
   Ch = CPU#cpu.channel,
   spawn(fun() -> X = channel:read(Ch),M ! {read,X} end),
   read_wait(CPU).    

read_wait(CPU) ->
   receive
      {read,{ok,Word}} -> 
         trace:trace(f18A,{ CPU#cpu.id,read,{ok,Word}}),     
         PC = CPU#cpu.pc + 1,
         {ok,CPU#cpu{pc = PC }};

      step ->
         read_wait(CPU);

      {stop,PID} ->
         {stop,PID};

      _any ->
         log:warn(?TAG,"READ/? ~p",[_any]),
         {error,_any}
   end.
   

% WRITE

write(CPU,Word) ->
   log:info(?TAG,"WRITE"),
   trace:trace(f18A,{ CPU#cpu.id,write,Word }),     
   M  = self(),
   Ch = CPU#cpu.channel,
   spawn(fun() -> channel:write(Ch,Word),M ! write_ok end),
   write_wait(CPU).    
   
write_wait(CPU) ->
   receive
      write_ok -> 
         trace:trace(f18A,{ CPU#cpu.id,write,ok }),     
         PC = CPU#cpu.pc + 1,
         {ok,CPU#cpu{pc = PC }};

      step ->
         write_wait(CPU);

      {stop,PID} ->
         {stop,PID};

      _any ->
         log:warn(?TAG,"WRITE/? ~p",[_any]),
         {error,_any}
   end.
   
