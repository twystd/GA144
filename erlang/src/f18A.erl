-module(f18A).

% EXPORTS

-export([create/3]).
-export([reset/1]).
-export([go/1,go/2]).
-export([stop/1,stop/2]).
-export([step/1,step/2]).
-export([run/1]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% RECORDS

-record(cpu,{ id,
              channel,
              program,
              p,
              i
            }).

% DEFINES

-define(TAG,"F18A").
-define(NOP,16#1c).

% API

%% @doc Initialises an F18A node and starts the internal instruction 
%%      execution process.
create(ID,Channel,Program) ->
   start(ID,#cpu{ id      = ID,
                  channel = Channel,
                  program = Program,
                  p       = 0,
                  i       = []
                }).

start(ID,CPU) ->
   start(ID,CPU,util:is_registered(ID)),
   ID.

start(ID,CPU,true) ->
   unregister(ID),
   register  (ID,spawn(f18A,run,[CPU]));

start(ID,CPU,_) ->
   register(ID,spawn(f18A,run,[CPU])).

%% @doc Issues a RESET command to the F18A node and waits for completion.
%%
reset(F18A) ->
   F18A ! {reset,self() },
   receive
      reset -> ok
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

go(F18A,wait) ->
   F18A ! { go,self() },
   go_wait().

go_wait() ->
   receive
      gone -> ok;
      _    -> go_wait()
   end.


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

loop({eof,_CPU}) ->
   stopped;

loop({error,CPU}) ->
   unregister(CPU#cpu.id),
   stopped;

loop({run,CPU}) ->
   receive
      reset ->
         log:info(?TAG,"RESET"),
         trace:trace(f18A,{ CPU#cpu.id,reset}),     
         loop(reset_impl(CPU));

      {reset,PID} ->
         log:info(?TAG,"RESET/W"),
         trace:trace(f18A,{ CPU#cpu.id,reset}),     
         Next = reset_impl(CPU),
         PID ! reset,
         loop(Next);

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
         loop(go_impl(CPU));

      {go,PID} ->
         log:info(?TAG,"GO/W"),
         Next = go_impl(CPU),
         PID ! gone,
         loop(Next)

      end.

reset_impl(CPU) ->
   receive
      _any ->
         reset_impl(CPU)

   after 100 ->   
      {run,CPU#cpu{ p  = 0,
                    i  = []
                  }}
   end.         

step_impl(CPU) ->
   case exec(CPU) of
      {ok,CPUX} ->
         {run,CPUX};

      eof ->
         trace:trace(f18A,{ CPU#cpu.id,eof}),     
         {eof,CPU};
   
      {stop,PID} ->
         trace:trace(f18A,{ CPU#cpu.id,stop}),     
         PID ! stopped,
         {stop,CPU};

      {error,Reason} ->
         log:error(?TAG,"OOOOPS/ : ~p",[Reason]),
         {error,CPU}

%      _any ->   
%         log:error(?TAG,"STEP/? : ~p",[_any]),
%         {error,CPU}
   end.

go_impl(CPU) ->
   case exec(CPU) of 
      {ok,CPUX} ->
         go_impl(CPUX);

      eof ->
         trace:trace(f18A,{ CPU#cpu.id,eof}),     
         {eof,CPU};
   
      {stop,PID} ->
         trace:trace(f18A,{ CPU#cpu.id,stop}),     
         PID ! stopped,
         {stop,CPU};

      {error,Reason} ->
         log:error(?TAG,"OOOOPS/ : ~p",[Reason]),
         {error,CPU}
   
%      _any ->   
%         log:error(?TAG,"GO/? : ~p",[_any]),
%         {error,CPU}
   end.


exec(CPU) ->
   I = CPU#cpu.i,      
   exec(CPU,I).

exec(CPU,[]) ->
   P = CPU#cpu.p,     
   case load_next(CPU) of
        {ok,I} ->
            exec(CPU#cpu{ p = P + 1,
                          i = I
                        });

         eof ->
            eof
   end;

exec(CPU,[H|T]) ->
   exec_impl(CPU#cpu{ i=T },H).

exec_impl(CPU,?NOP) ->
   log:info(?TAG,"NOP"),     
   trace:trace(f18A,{ CPU#cpu.id,nop }),     
   {ok,CPU};

exec_impl(CPU,nop) ->
   log:info(?TAG,"NOP"),     
   trace:trace(f18A,{ CPU#cpu.id,nop }),     
   {ok,CPU};

exec_impl(CPU,read) ->
   log:info   (?TAG,"READ"),
   trace:trace(f18A,{ CPU#cpu.id,read}),     
   read(CPU);

exec_impl(CPU,{write,Word}) ->
   log:info   (?TAG,"WRITE"),
   trace:trace(f18A,{ CPU#cpu.id,{write,Word}}),     
   write(CPU,Word);
  
exec_impl(_CPU,{error,Reason}) ->
   log:error(?TAG,"INVALID OPERATION ~p~n",[Reason]),
   {error,Reason};

exec_impl(CPU,OpCode) ->
   log:warn(?TAG,"UNIMPLEMENTED OPCODE: ~p~n",[OpCode]),
   {ok,CPU}.

% INSTRUCTION LOADER

load_next(CPU) ->
   Program = CPU#cpu.program,
   P       = CPU#cpu.p,     
   load_next(Program,P).

load_next(Program,Address) when Address < length(Program) ->
   { ok,decode(lists:nth(Address+1,Program)) };

load_next(_Program,_Address) ->
   eof.

% OPCODE DECODER

decode(Word) when is_integer(Word) ->
   [ decode(Word bxor 16#15555,0),
     decode(Word bxor 16#15555,1),
     decode(Word bxor 16#15555,2),
     decode(Word bxor 16#15555,3)
   ];

decode(Word) ->
   [ Word ].

decode(Word,0) ->
   (Word bsr 13) band 16#001F;

decode(Word,1) ->
   (Word bsr 8) band 16#001F;

decode(Word,2) ->
   (Word bsr 3) band 16#001F;

decode(Word,3) ->
   (Word bsl 2) band 16#001F.

% READ

read(CPU) ->
   ID = CPU#cpu.id,
   Ch = CPU#cpu.channel,
   receive
      {Ch,write,Word} -> 
         trace:trace(f18A,{ CPU#cpu.id,{read,Word}}),     
         Ch ! { ID,read,ok },
         {ok,CPU};

      step ->
         read(CPU);

      {stop,PID} ->
         {stop,PID}

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
         trace:trace(f18A,{ CPU#cpu.id,{write,ok}}),     
         {ok,CPU};

      step ->
         write_wait(CPU);

      {stop,PID} ->
         {stop,PID}
   end.

% EUNIT TESTS
