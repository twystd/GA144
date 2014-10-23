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

-record(cpu,{ id,
              channel,
              program,
              pc,
              fifo
            }).

% DEFINES

-define(TAG,"F18A").

% API

%% @doc Initialises an F18A node and starts the internal instruction 
%%      execution process.
create(ID,Channel,Program) ->
   start(ID,#cpu{ id      = ID,
                  channel = Channel,
                  program = Program,
                  pc      = 1
                }).

start(ID,CPU) ->
   start(ID,CPU,util:is_registered(ID)),
   ID.

start(ID,CPU,true) ->
   unregister(ID),
   register  (ID,spawn(f18A,run,[CPU]));

start(ID,CPU,_) ->
   register(ID,spawn(f18A,run,[CPU])).

%% @doc Issues a RESET command to the F18A node and returns immediately.
%%
reset(F18A) ->
   F18A ! reset.

reset(F18A,wait) ->
   F18A ! {reset,self() },
   reset_wait().

reset_wait() ->
   receive
      reset -> ok;
      _     -> reset_wait()
   end.
  
 
%% @doc Issues a STEP command to the F18A node and returns immediately.
%%
step(F18A) ->
   F18A ! step.

step(F18A,wait) ->
   F18A ! { step,self() },
   step_wait().

step_wait() ->
   receive
      step -> ok;
      _    -> step_wait()
   end.


%% @doc Issues a GO command to the F18A node and returns immediately.
%%
go(F18A) ->
   F18A ! go,
   ok.


%% @doc Issues a STOP command to the F18A node and returns immediately.
%%
stop(F18A) ->
   F18A ! stop,
   ok.

stop(F18A,wait) ->
   F18A ! { stop,self() },
   stop_wait().

stop_wait() ->
   receive
      stopped -> 
         ok;

      {error,Reason} ->
         {error,Reason};

      _any -> 
         stop_wait()
   end.

% INTERNAL

run(CPU) ->
   loop({run,CPU}).

loop({stop,_CPU}) ->
   stopped;

loop({error,CPU}) ->
   unregister(CPU#cpu.id),
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
         unregister (CPU#cpu.id),
         stopped;

      {stop,PID} ->
         log:info(?TAG,"STOP/W"),
         trace:trace(f18A,{ CPU#cpu.id,stop}),     
         unregister(CPU#cpu.id),
         PID ! stopped,
         stopped;

      go ->
         log:info(?TAG,"GO"),
         loop({run,CPU});

      {Ch,write,Word} ->
         loop({run,CPU#cpu{fifo={Ch,Word}
                          }
              });

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

      {error,Reason} ->
         log:error(?TAG,"OOOOPS/ : ~p",[Reason]),
         {error,CPU};

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
   log:info   (?TAG,"READ"),
   trace:trace(f18A,{ CPU#cpu.id,read}),     
   read(CPU);

exec(CPU,{write,Word}) ->
   log:info   (?TAG,"WRITE"),
   trace:trace(f18A,{ CPU#cpu.id,write,Word }),     
   write(CPU,Word);
   
exec(CPU,OpCode) ->
   log:warn(?TAG,"UNIMPLEMENTED OPCODE: ~p~n",[OpCode]),
   PC  = CPU#cpu.pc + 1,
   {ok,CPU#cpu{pc=PC}}.

% READ

read(CPU) ->
   Word = CPU#cpu.fifo,
   read(CPU,Word).

read(CPU,undefined) ->  
   read_wait(CPU);

read(CPU,{Ch,Word}) ->
   ID   = CPU#cpu.id,
   Ch   = CPU#cpu.channel,
   trace:trace(f18A,{ CPU#cpu.id,read,{ok,Word}}),     
   Ch ! { ID,read,ok },
   PC = CPU#cpu.pc + 1,
   {ok,CPU#cpu{ pc = PC,
                fifo = undefined
               }}.
 
read_wait(CPU) ->
   ID = CPU#cpu.id,
   Ch = CPU#cpu.channel,
   receive
      {Ch,write,Word} -> 
         trace:trace(f18A,{ CPU#cpu.id,read,{ok,Word}}),     
         Ch ! { ID,read,ok },
         PC = CPU#cpu.pc + 1,
         {ok,CPU#cpu{pc = PC }};

      step ->
         read(CPU);

      {stop,PID} ->
         {stop,PID};

      _any ->
         log:warn(?TAG,"READ/? ~p",[_any]),
         {error,_any}
   end.
   

% WRITE

write(CPU,Word) ->
   ID = CPU#cpu.id,
   Ch = CPU#cpu.channel,
   try
      Ch ! { ID,write,Word },
      write_wait(CPU)
   catch
      error:badarg ->
         log:error(?TAG,"~p:WRITE to invalid node ~p",[ID,Ch]),   
         {error,invalid_peer};

      C:X ->
         log:error(?TAG,"~p:WRITE ~p failed ~p:~p",[ID,Ch,C,X]),   
         {error,{C,X}}
   end.
   
write_wait(CPU) ->
   Ch = CPU#cpu.channel,
   receive
      { Ch,read,ok } -> 
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

% EUNIT TESTS
