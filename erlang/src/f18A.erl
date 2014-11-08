-module(f18A).

% EXPORTS

-export([create/3]).
-export([reset/1]).
-export([go/1,go/2]).
-export([stop/1,stop/2]).
-export([step/1,step/2]).
-export([breakpoint/2]).

% FOR INTERNAL USE ONLY
-export([run/1]).

% INCLUDES

-include    ("include/f18A.hrl").
-include    ("include/opcode.hrl").
-include_lib("eunit/include/eunit.hrl").

% DEFINES

-define(TAG,  "F18A").
-define(RIGHT,16#1d5).

% API

%% @doc Initialises an F18A node and starts the internal instruction 
%%      execution process.
create(ID,Channel,Program) ->
   start(ID,#cpu{ id      = ID,
                  channel = Channel,
                  rom     = Program,
                  ram     = Program,
                  io      = [],
                  p       = 0,
                  a       = 0,
                  b       = 16#100,
                  i       = [],
                  t       = 0
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

%% @doc Sets a breakpoint for the program counter.
%%
breakpoint(F18A,Address) ->
   F18A ! {breakpoint,Address},
   ok.

% INTERNAL

run(CPU) ->
   loop({run,CPU}).

loop({stop,_CPU}) ->
   stopped;

loop({breakpoint,_CPU}) ->
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
         loop(Next);

      {breakpoint,Address} ->
         Breakpoints = [ Address|CPU#cpu.breakpoints],          
         loop({run,CPU#cpu{ breakpoints = Breakpoints
                          }})

      end.

reset_impl(CPU) ->
   receive
      _any ->
         reset_impl(CPU)

   after 100 ->   
      {run,CPU#cpu{ p = 0,
                    a = 0,
                    b = 16#100,
                    i = [],
                    t = 0
                  }}
   end.         

step_impl(CPU) ->
   case exec(CPU) of
      {ok,CPUX} ->
         {run,CPUX};

      breakpoint ->
         {breakpoint,CPU};

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
   end.

go_impl(CPU) ->
   case exec(CPU) of 
      {ok,CPUX} ->
         go_impl(CPUX);

      breakpoint ->
         {breakpoint,CPU};

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

         breakpoint ->
           breakpoint;

         eof ->
            eof
   end;

exec(CPU,[H|T]) ->
   exec_impl(CPU#cpu{ i=T },H).

% 16#08  @p  fetch P
exec_impl(CPU,?FETCHP) ->
   P    = CPU#cpu.p,     
   CPUX = CPU#cpu{ p = P + 1,
                   t = read(CPU,P)
                 }, 
   trace(?FETCHP,CPUX),
   {ok,CPUX};

% 16#0a  @b  fetch B
exec_impl(CPU,?FETCHB) ->
   log:info(?TAG,"FETCH-B"),     
   B = CPU#cpu.b,     
   T = read(CPU,B),
   trace:trace(f18A,{ CPU#cpu.id,{fetchb,{t,T}}}),     
   {ok,CPU#cpu{ t = T
              }};

% 16#0e  !b  store B
exec_impl(CPU,?STOREB) ->
   log:info(?TAG,"STORE-B"),     
   B = CPU#cpu.b,     
   T = CPU#cpu.t,
   write(CPU,B,T),
   trace:trace(f18A,{ CPU#cpu.id,{storeb,{b,B},{t,T}}}),     
   {ok,CPU#cpu{ t = T
              }};

% 16#1c  .   nop
exec_impl(CPU,?NOP) ->
   trace(?NOP,CPU),     
   {ok,CPU};

% 16#1e  b!  b-store
exec_impl(CPU,?BSTORE) ->
   log:info(?TAG,"B-STORE"),     
   B = CPU#cpu.t,     
   trace:trace(f18A,{ CPU#cpu.id,{bstore,{b,B}}}),     
   {ok,CPU#cpu{ b = B
              }};

% INTERIM STUFF - REMOVE
exec_impl(CPU,nop) ->
   log:info(?TAG,"NOP"),     
   trace:trace(f18A,{ CPU#cpu.id,nop }),     
   {ok,CPU};

% INTERIM STUFF - REMOVE
exec_impl(CPU,read) ->
   log:info   (?TAG,"READ"),
   trace:trace(f18A,{ CPU#cpu.id,read}),     
   channel_read(CPU);

% INTERIM STUFF - REMOVE
exec_impl(CPU,{write,Word}) ->
   log:info   (?TAG,"WRITE"),
   trace:trace(f18A,{ CPU#cpu.id,{write,Word}}),     
   channel_write(CPU,Word);
  
exec_impl(_CPU,{error,Reason}) ->
   log:error(?TAG,"INVALID OPERATION ~p~n",[Reason]),
   {error,Reason};

exec_impl(CPU,OpCode) ->
   log:warn(?TAG,"UNIMPLEMENTED OPCODE: ~p~n",[OpCode]),
   {ok,CPU}.

% INSTRUCTION LOADER
%
load_next(CPU) ->
   P           = CPU#cpu.p,     
   Breakpoints = CPU#cpu.breakpoints,
   F           = fun(X) -> P =:= X end,
   case lists:any(F,Breakpoints) of
        true ->
             breakpoint;

        _else ->
             load_next_impl(read(CPU,P))
        end.

load_next_impl(eof) ->
   eof;

load_next_impl(Word) ->
   { ok,decode(Word) }.

% OPCODE DECODER
%
decode(Word) when is_integer(Word) ->
   [ decode(Word bxor 16#15555,0),
     decode(Word bxor 16#15555,1),
     decode(Word bxor 16#15555,2),
     decode(Word bxor 16#15555,3)
   ];

decode(Word) ->
   [ Word ].

decode(Word,0) ->
   opcode:opcode((Word bsr 13) band 16#001F);

decode(Word,1) ->
   opcode:opcode((Word bsr 8) band 16#001F);

decode(Word,2) ->
   opcode:opcode((Word bsr 3) band 16#001F);

decode(Word,3) ->
   opcode:opcode((Word bsl 2) band 16#001F).

% READ
%

read(CPU,Addr) when Addr < 16#40 ->
   read_mem(CPU#cpu.ram,Addr);

read(CPU,Addr) when Addr < 16#80 ->
   read_mem(CPU#cpu.ram,Addr-16#40);

read(CPU,Addr) when Addr < 16#C0 ->
   read_mem(CPU#cpu.rom,Addr-16#80);

read(CPU,Addr) when Addr < 16#100 ->
   read_mem(CPU#cpu.rom,Addr-16#C0);

read(CPU,?RIGHT) ->
   Ch = CPU#cpu.channel,
   read_channel(CPU,Ch);

read(CPU,Addr) when Addr < 16#200 ->
   read_mem(CPU#cpu.io,Addr-16#100).

read_mem(Mem,Addr) when Addr < length(Mem) ->
   lists:nth(Addr+1,Mem);

read_mem(_Mem,_Addr) ->
   eof.

read_channel(CPU,Ch) ->
   ID = CPU#cpu.id,
   receive
      {Ch,write,Word} -> 
         Ch ! { ID,read,ok },
         Word;

      step ->
         read_channel(CPU,Ch);

      {stop,PID} ->
         {stop,PID}

   end.

% WRITE

write(CPU,?RIGHT,Word) ->
   Ch = CPU#cpu.channel,
   write_channel(CPU,Ch,Word).

write_channel(CPU,Ch,Word) ->
   ID = CPU#cpu.id,
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
         ok;

      step ->
         write_wait(CPU);

      {stop,PID} ->
         {stop,PID}
   end.

	
% CHANNEL READ

channel_read(CPU) ->
   ID = CPU#cpu.id,
   Ch = CPU#cpu.channel,
   receive
      {Ch,write,Word} -> 
         trace:trace(f18A,{ CPU#cpu.id,{read,Word}}),     
         Ch ! { ID,read,ok },
         {ok,CPU};

      step ->
         channel_read(CPU);

      {stop,PID} ->
         {stop,PID}

   end.
   

% CHANNEL WRITE

channel_write(CPU,Word) ->
   ID = CPU#cpu.id,
   Ch = CPU#cpu.channel,
   try
      Ch ! { ID,write,Word },
      channel_write_wait(CPU)
   catch
      error:badarg ->
         log:error(?TAG,"~p:WRITE to invalid node ~p",[ID,Ch]),   
         {error,invalid_peer};

      C:X ->
         log:error(?TAG,"~p:WRITE ~p failed ~p:~p",[ID,Ch,C,X]),   
         {error,{C,X}}
   end.
   
channel_write_wait(CPU) ->
   Ch = CPU#cpu.channel,
   receive
      { Ch,read,ok } -> 
         trace:trace(f18A,{ CPU#cpu.id,{write,ok}}),     
         {ok,CPU};

      step ->
         channel_write_wait(CPU);

      {stop,PID} ->
         {stop,PID}
   end.

% UTILITY FUNCTIONS
% 
trace(OpCode,CPU) ->
   log:info   (?TAG,opcode:to_string(OpCode)),     
   trace:trace(f18A,OpCode,CPU).
   
% EUNIT TESTS
