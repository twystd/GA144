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
   RAM = array:from_list(Program),
   start(ID,#cpu{ id      = ID,
                  channel = Channel,
                  rom     = array:new(64),
                  ram     = RAM,
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
   exec_impl(H,CPU#cpu{ i=T }).

% 16#00  ;   ret
exec_impl(?RET,CPU) ->
   P      = CPU#cpu.r,
   {R,RS} = pop(CPU#cpu.rs),     
   CPUX   = CPU#cpu{ p  = P,
                     r  = R,
                     rs = RS,
                     i  = []
                   }, 
   trace(?RET,CPUX),
   {ok,CPUX};

% 16#02  name ;   jump
exec_impl({?JUMP,Addr},CPU) ->
   P    = Addr,
   CPUX = CPU#cpu{ p  = P
                 }, 
   trace(?JUMP,CPUX),
   {ok,CPUX};


% 16#08  @p  fetch P
exec_impl(?FETCHP,CPU) ->
   P = CPU#cpu.p,     
   case read(CPU,P) of
        {ok,T} ->
   	   CPUX = CPU#cpu{ p = P + 1,
                           t = T
                 	 }, 
   	   trace(?FETCHP,CPUX),
   	   {ok,CPUX};
    
        Other ->
            Other
	end;

% 16#0a  @b  fetch B
exec_impl(?FETCHB,CPU) ->
   log:info(?TAG,"FETCH-B"),     
   B = CPU#cpu.b,     
   case read(CPU,B) of
        {ok,T} ->
    	    CPUX = CPU#cpu{ t = T
                          },

   	    trace(?FETCHB,CPUX),
   	    {ok,CPUX};

        Other ->
            Other
	end;

% 16#0e  !b  store B
exec_impl(?STOREB,CPU) ->
   log:info(?TAG,"STORE-B"),     
   B = CPU#cpu.b,     
   T = CPU#cpu.t,
   S = CPU#cpu.s,
   case write(CPU,B,T) of 
        {ok,RAM} ->
              {SX,DSX} = pop(CPU#cpu.ds),     
  	      CPUX     = CPU#cpu{ t   = S,
                                  s   = SX,
                                  ds  = DSX,
                                  ram = RAM },
	         trace(?STOREB,CPUX),
   	      {ok,CPUX};

	     Other ->
            Other
  	     end;

% 16#14  +   plus
exec_impl(?PLUS,CPU) ->
   T  = CPU#cpu.t band 16#3ffff,   
   S  = CPU#cpu.s band 16#3ffff,
   DS = CPU#cpu.ds,
   C  = CPU#cpu.carry,
   R  = case (CPU#cpu.p band 16#0200) of
 	     16#0200 ->
	 	 (S + T + C) band 16#3ffff;
 
             _else ->
                 (S + T) band 16#3ffff
             end,

   {SX,DSX} = pop(DS),

   CPUX = CPU#cpu{ t  = R,
                   s  = SX,
                   ds = DSX
                 },

   trace(?PLUS,CPUX),     
   {ok,CPUX};

% 16#18  dup
exec_impl(?DUP,CPU) ->
   T    = CPU#cpu.t,
   S    = CPU#cpu.s,
   DS   = CPU#cpu.ds,
   CPUX = CPU#cpu{ s  = T,
                   ds = push(DS,S)
                 },
   trace(?DUP,CPUX),     
   {ok,CPUX};

% 16#1c  .   nop
exec_impl(?NOP,CPU) ->
   trace(?NOP,CPU),     
   {ok,CPU};

% 16#1e  b!  b-store
exec_impl(?BSTORE,CPU) ->
   B = CPU#cpu.t,     
   CPUX = CPU#cpu{ b = B
                 },
   trace(?BSTORE,CPUX),
   {ok,CPUX};

exec_impl({error,Reason},_CPU) ->
   log:error(?TAG,"INVALID OPERATION ~p~n",[Reason]),
   {error,Reason};

exec_impl(OpCode,CPU) ->
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

load_next_impl({ok,Word}) ->
   { ok,decode(Word) };

load_next_impl(eof) ->
   eof;

load_next_impl(_) ->
   error.

% OPCODE DECODER
%
decode(Word) ->
   WordX                   = Word bxor 16#15555,
   <<S0:5,S1:5,S2:5,S3:3>> = <<WordX:18>>,
   decode(opcode:opcode(S0),
          opcode:opcode(S1),
          opcode:opcode(S2),
          opcode:opcode(S3 bsl 2),
          Word band 16#03ff,
          Word band 16#00ff,
          Word band 16#0003).

decode(?JUMP,_,_,_,Addr0,_,_) ->
   [{?JUMP,Addr0}];

decode(S0,?JUMP,_,_,_,Addr1,_) ->
   [S0,{?JUMP,Addr1}];

decode(S0,S1,?JUMP,_,_,_,Addr2) ->
   [S0,S1,{?JUMP,Addr2}];

decode(S0,S1,S2,S3,_,_,_) ->
   [ S0,S1,S2,S3 ].

% READ

read(CPU,Addr) when Addr < 16#40 ->
   read_mem(CPU#cpu.ram,Addr);

read(CPU,Addr) when Addr < 16#80 ->
   read_mem(CPU#cpu.ram,Addr band 16#3f);

read(CPU,Addr) when Addr < 16#C0 ->
   read_mem(CPU#cpu.rom,Addr band 16#3f);

read(CPU,Addr) when Addr < 16#100 ->
   read_mem(CPU#cpu.rom,Addr band 16#3f);

read(CPU,?RIGHT) ->
   Ch = CPU#cpu.channel,
   read_channel(CPU,Ch);

read(CPU,Addr) when Addr < 16#200 ->
   read_mem(CPU#cpu.io,Addr-16#100).

read_mem(Mem,Addr) ->
   read_mem(Mem,Addr,array:size(Mem)).

read_mem(Mem,Addr,N) when Addr < N ->
   { ok,array:get(Addr,Mem) };

read_mem(_Mem,_Addr,_N) ->
   eof.

read_channel(CPU,Ch) ->
   ID = CPU#cpu.id,
   receive
      {Ch,write,Word} -> 
         Ch ! { ID,read,ok },
         {ok,Word};

      step ->
         read_channel(CPU,Ch);

      {stop,PID} ->
         {stop,PID}
   end.

% WRITE

write(CPU,Addr,Word) when Addr < 16#40 ->
   write_mem(CPU#cpu.ram,Addr,Word);

write(CPU,Addr,Word) when Addr < 16#80 ->
   write_mem(CPU#cpu.ram,Addr band 16#3f,Word);

% TODO - CHECK WHAT HAPPENS ON SIMULATOR/EMULATOR
write(_CPU,Addr,_Word) when Addr < 16#C0 ->
   ignore; 

% TODO - CHECK WHAT HAPPENS ON SIMULATOR/EMULATOR
write(_CPU,Addr,_Word) when Addr < 16#100 ->
   ignore; 

write(CPU,?RIGHT,Word) ->
   Ch = CPU#cpu.channel,
   write_channel(CPU,Ch,Word).

write_mem(Mem,Addr,Word) ->
   write_mem(Mem,Addr,Word,array:size(Mem)).

write_mem(Mem,Addr,Word,N) when Addr < N ->
   trace:trace(f18A,{n001,{write,Addr,Word}}),     
   { ok,array:set(Addr,Word,Mem) };

write_mem(_Mem,_Addr,_Word,_N) ->
   eof.

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
         {ok,CPU#cpu.ram};

      step ->
         write_wait(CPU);

      {stop,PID} ->
         {stop,PID}
   end.

% STACK HANDLING

push(DS,S) ->
   lists:droplast([S|DS]).

pop([W0,W1,W2,W3,W4,W5,W6,W7]) ->
   {W0,[W1,W2,W3,W4,W5,W6,W7,W0]}.

% UTILITY FUNCTIONS
% 
trace(OpCode,CPU) ->
   log:info   (?TAG,opcode:to_string(OpCode)),     
   trace:trace(f18A,OpCode,CPU).
   
% EUNIT TESTS

decode_test() ->
   ?assertEqual([{?JUMP,16#03}],decode(16#11403)).

ret_test() ->
   P  = 1,
   R  = 2,
   RS = [3,4,5,6,7,8,9,10],
   I  = [ ?NOP,?NOP,?NOP,?NOP ],
   {ok,CPU} = exec_impl(?RET,#cpu{p=P,r=R,rs=RS,i=I}),
   assert([{p,R},{r,3},{rs,[4,5,6,7,8,9,10,3]},{i,[]}],CPU).

jump_test() ->
   P = 16#0a9,
   {ok,CPU} = exec_impl({?JUMP,16#03},#cpu{p=P}),
   assert([{p,16#03}],CPU).

storeb_test() ->
   S   = 9,
   T   = 678,
   B   = 16#004,
   RAM = array:new(64,[{default,0}]),
   DS  = [1,2,3,4,5,6,7,8],
   {ok,CPU} = exec_impl(?STOREB,#cpu{b=B,t=T,s=S,ds=DS,ram=RAM}),
   assert([{ram,4,678},{t,S},{s,1},{ds,[2,3,4,5,6,7,8,1]}],CPU).

nop_test() ->
   A = 1,
   B = 2,
   T = 3,
   S = 4,
   {ok,CPU} = exec_impl(?NOP,#cpu{a=A,b=B,t=T,s=S}),
   assert([{a,A},{b,B},{t,T},{s,S}],CPU).

plus_test() ->
   plus_test_impl(16#0000,1,       2,       0,3),
   plus_test_impl(16#0000,16#3ffff,16#3fffe,0,16#3fffd),
   plus_test_impl(16#0000,16#3ffff,16#00001,0,0),

   plus_test_impl(16#0200,1,       2,       0,3),
   plus_test_impl(16#0200,16#3ffff,16#3fffe,0,16#3fffd),
   plus_test_impl(16#0200,16#3ffff,16#00001,0,0),

   plus_test_impl(16#0200,1,       2,       1,4),
   plus_test_impl(16#0200,16#3ffff,16#3fffe,1,16#3fffe),
   plus_test_impl(16#0200,16#3ffff,16#00001,1,1).

plus_test_impl(P,T,S,C,R) ->
   DS  = [3,4,5,6,7,8,9,10],
   DSX = [4,5,6,7,8,9,10,3],
   {ok,CPU} = exec_impl(?PLUS,#cpu{ p=P,
                                    t=T,
                                    s=S,
                                    ds=DS,
                                    carry=C }),
   assert([{t,R},{s,3},{ds,DSX}],CPU).

dup_test() ->
   {ok,CPU} = exec_impl(?DUP,#cpu{t=1,
                                  s=2,
                                  ds=[3,4,5,6,7,8,9,10]}),

   ?assertEqual(1,CPU#cpu.t),
   ?assertEqual(1,CPU#cpu.s),
   ?assertEqual([2,3,4,5,6,7,8,9],CPU#cpu.ds).

assert ([],_CPU) ->
   ok;

assert([{p,X}|T],CPU) ->
   ?assertEqual(X,CPU#cpu.p),
   assert(T,CPU);

assert([{r,X}|T],CPU) ->
   ?assertEqual(X,CPU#cpu.r),
   assert(T,CPU);

assert([{i,X}|T],CPU) ->
   ?assertEqual(X,CPU#cpu.i),
   assert(T,CPU);

assert([{a,X}|T],CPU) ->
   ?assertEqual(X,CPU#cpu.a),
   assert(T,CPU);

assert([{b,X}|T],CPU) ->
   ?assertEqual(X,CPU#cpu.b),
   assert(T,CPU);

assert([{s,X}|T],CPU) ->
   ?assertEqual(X,CPU#cpu.s),
   assert(T,CPU);

assert([{t,X}|T],CPU) ->
   ?assertEqual(X,CPU#cpu.t),
   assert(T,CPU);

assert([{rs,X}|T],CPU) ->
   ?assertEqual(X,CPU#cpu.rs),
   assert(T,CPU);

assert([{ds,X}|T],CPU) ->
   ?assertEqual(X,CPU#cpu.ds),
   assert(T,CPU);

assert([{ram,Addr,Word}|T],CPU) ->
   ?assertEqual(Word,array:get(Addr,CPU#cpu.ram)),
   assert(T,CPU);

assert([_|T],CPU) ->
   assert(T,CPU).


