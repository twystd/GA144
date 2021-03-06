-module(f18A).

% EXPORTS

-export([create/4,create/5,create/6]).
-export([reset/1]).
-export([go/1,go/2]).
-export([break/1]).
-export([stop/1,stop/2]).
-export([step/1,step/2]).
-export([breakpoint/2]).
-export([peek/2]).
-export([probe/2]).

% FOR INTERNAL USE ONLY
-export([run/1]).

% INCLUDES

-include    ("include/f18A.hrl").
-include    ("include/opcode.hrl").
-include_lib("eunit/include/eunit.hrl").

% DEFINES

-define(TAG,  "F18A").
-define(RIGHT,16#1d5).
-define(LEFT, 16#175).
-define(UP,   16#145).
-define(DOWN, 16#115).

% API

%% @doc Initialises an F18A node and starts the internal instruction 
%%      execution process.
create(ID,Channels,ROM,RAM) ->
    create(undefined, ID, Channels, ROM, RAM, yes).

create(GA144,ID,Channels,ROM,RAM) ->
    create(GA144, ID, Channels, ROM, RAM, yes).

create(GA144,ID,{Left,Right,Up,Down},ROM,RAM,Log) ->
   start(ID,#cpu{ ga144   = GA144,
                  id      = ID,
                  channel = #channels{left=Left, right=Right,up=Up,down=Down},
                  rom     = ROM,
                  ram     = RAM,
                  io      = [],
                  p       = 16#0a9,
                  a       = 0,
                  b       = 16#100,
                  i       = [],
                  im      = [],
                  t       = 0,

                  log = Log
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
   step_wait();

step(F18A,PID) ->
   F18A ! { step,PID }.

step_wait() ->
   receive
      {_ID,step} ->
         ok;

      _ -> 
         step_wait()
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

%% @doc Issues a BREAK command to the F18A node and returns immediately.
%%
break(F18A) ->
   F18A ! break,
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

%% @doc Sets a breakpoint for the program counter.
%%
breakpoint(F18A,Address) ->
   F18A ! {breakpoint,Address},
   ok.

%% @doc Inserts a probe into the exec loop.
%%
probe(F18A,Probe) ->
   F18A ! {probe,Probe},
   ok.

%% @doc Returns the internal state of a CPU register.
%% 
peek(F18A,Register) ->
   F18A ! {peek,Register,self()},
   receive
      { peek,V} -> V
   end.

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
         trace:trace(f18A,{ CPU#cpu.id,reset}),     
         loop(reset_impl(CPU));

      {reset,PID} ->
         trace:trace(f18A,{ CPU#cpu.id,reset}),     
         Next = reset_impl(CPU),
         PID ! reset,
         loop(Next);

      step ->
         loop(step_impl(CPU));

      {step,PID} ->
         Next = step_impl(CPU),
         PID ! {CPU#cpu.id,step},
         loop(Next);

      stop ->
         trace:trace(f18A,{ CPU#cpu.id,stop}),     
         unregister (CPU#cpu.id),
         stopped;

      {stop,PID} ->
         trace:trace(f18A,{ CPU#cpu.id,stop}),     
         unregister(CPU#cpu.id),
         PID ! stopped,
         stopped;

      go ->
         loop(go_impl(CPU));

      {go,PID} ->
         Next = go_impl(CPU),
         PID ! gone,
         loop(Next);

      break ->
         loop({run,CPU});

      {breakpoint,Address} ->
         Breakpoints = [ Address|CPU#cpu.breakpoints],          
         loop({run,CPU#cpu{ breakpoints = Breakpoints
                          }});

      {probe,Probe} ->
         loop({run,CPU#cpu{ probes = [Probe|CPU#cpu.probes]          
                          }});

      {peek,Register,PID} ->
         PID ! {peek,peek_impl(CPU,Register)},
         loop({run,CPU})

      end.

peek_impl(CPU,t) ->
   CPU#cpu.t;

peek_impl(CPU,s) ->
   CPU#cpu.s;

peek_impl(CPU,ds) ->
   CPU#cpu.ds;

peek_impl(_,_) ->
   unknown.

reset_impl(CPU) ->
   receive
      _any ->
         reset_impl(CPU)

   after 100 ->   
      {run,CPU#cpu{ p = 16#0a9,
                    i = [],
                    a = 0,
                    b = 16#100,
                    t = 0,
                    s = 0
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
           receive
               break ->
                    {run,CPU}

           after 0 ->
                go_impl(CPUX)
           end;
 
       break ->
           {run,CPU};

       {breakpoint,CPUX} ->
           {breakpoint,CPUX};

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
   P           = CPU#cpu.p,     
   Breakpoints = CPU#cpu.breakpoints,
   F           = fun(X) -> P =:= X end,
   Break       = lists:any(F,Breakpoints),

   case {load(CPU,P),Break} of
        {{ok,I},true} ->
           { breakpoint,CPU#cpu{ p  = P + 1,
                                 i  = I,
                                 im = I
                               }};

        {{ok,I},_} ->
           exec(CPU#cpu{ p  = P + 1,
                         i  = I,
                         im = I
                       });
        {eof,_} ->
            eof
   end;

exec(CPU,[H|T]) ->
    debug(H,CPU,CPU#cpu.log),
    case exec_impl(H,CPU#cpu{ i=T }) of
     	   {ok,CPUX} ->
   	       trace(H,CPUX,CPU#cpu.log),
           lists:foreach(fun(Probe) -> 
                                 Probe(CPUX)
                         end,
                         CPUX#cpu.probes),
   	       {ok,CPUX};

         Other ->
	          Other
	  end.

% 16#00  ;   ret
exec_impl(?RET,CPU) ->
   P    = CPU#cpu.r,
   CPUX = pop(rs,CPU),     
   {ok,CPUX#cpu{ p = P,
                 i = []
               }}; 

% 16#01  ex 
exec_impl(?EX,CPU) ->
   P = CPU#cpu.p,
   R = CPU#cpu.r,
   {ok,CPU#cpu{ p = R,
                r = P,
                i = []
              }}; 

% 16#02  name ; jump
exec_impl({?JUMP,Addr,Mask},CPU) ->
   P = CPU#cpu.p,
   {ok,CPU#cpu{ p = ((P band Mask) bor Addr),
                i = []
              }}; 

% 16#03  name  call
exec_impl({?CALL,Addr,Mask},CPU) ->
   P    = CPU#cpu.p,
   CPUX = push(rs,CPU),
   {ok,CPUX#cpu{ p = ((P band Mask) bor Addr),
                 r = P,
                 i = []
	       }}; 

% 16#04  unext
exec_impl(?UNEXT,CPU) ->
   IM = CPU#cpu.im,
   R  = CPU#cpu.r,
   case R of 
       0 ->
           CPUX = pop(rs,CPU),
           {ok,CPUX#cpu{ i = []
                       }};
       _else ->
           {ok,CPU#cpu{ r = R-1,
                        i = IM
                      }}
   end; 


% 16#05  next
exec_impl({?NEXT,Addr,Mask},CPU) ->
   P    = CPU#cpu.p,
   R    = CPU#cpu.r,
   case R of 
       0 ->
           CPUX = pop(rs,CPU),
           {ok,CPUX#cpu{ p = P+1,
                         i = []
                       }};
       _else ->
           {ok,CPU#cpu{ p = ((P band Mask) bor Addr),
                        r  = R-1,
                        i = []
                      }}
   end; 

% 16#06  if
exec_impl({?IF,Addr,Mask},CPU) ->
   P = CPU#cpu.p,
   T = CPU#cpu.t,
   case T of 
       0 ->
           {ok,CPU#cpu{ p = ((P band Mask) bor Addr),
                        i = []
                      }};
       _else ->
           {ok,CPU#cpu{ p = P+1,
                        i = []
                      }}
   end; 

% 16#07  minus-if
exec_impl({?MINUSIF,Addr,Mask},CPU) ->
   P = CPU#cpu.p,
   T = CPU#cpu.t,
   <<TS:1,_/bitstring>> = <<T:18>>,
   case TS of 
       0 ->
           {ok,CPU#cpu{ p = ((P band Mask) bor Addr),
                        i = []
                      }};
       _else ->
           {ok,CPU#cpu{ p = P+1,
                        i = []
                      }}
   end; 

% 16#08  @p  fetch P
exec_impl(?FETCHP,CPU) ->
   P    = CPU#cpu.p,     
   CPUX = push(ds,CPU),
   case read(CPUX,P) of
        {ok,T} ->
   	    {ok,CPUX#cpu{ p = inc(P),
                      t = T
                      }};
        Other ->
            Other
	end;


% 16#09  @+  fetch-plus
exec_impl(?FETCH_PLUS,CPU) ->
   A    = CPU#cpu.a,     
   CPUX = push(ds,CPU),
   case read(CPUX,A) of
        {ok,T} ->
   	    {ok,CPUX#cpu{ a = inc(A),
                          t = T
                        }};
        Other ->
            Other
	end;

% 16#0a  @b  fetch B
exec_impl(?FETCHB,CPU) ->
   B    = CPU#cpu.b,     
   CPUX = push(ds,CPU),
   case read(CPUX,B) of
        {ok,T} ->
   	      {ok,CPUX#cpu{ t = T
                        }};
        Other ->
            Other
	end;

% 16#0b  @  fetch
exec_impl(?FETCH,CPU) ->
   A    = CPU#cpu.a,     
   CPUX = push(ds,CPU),
   case read(CPUX,A) of
        {ok,T} ->
   	      {ok,CPUX#cpu{ t = T
                        }};
        Other ->
            Other
	end;

% 16#0c  !  store  P
exec_impl(?STOREP,CPU) ->
   P = CPU#cpu.p,     
   T = CPU#cpu.t,
   case write(CPU,P,T) of 
        {ok,ram,Mem} ->
            {ok,pop(ds,
                    CPU#cpu{ p=inc(P),
                             ram=Mem 
                           },
                    CPU#cpu.s)};

        {ok,rom,Mem} ->
            {ok,pop(ds,
                    CPU#cpu{ p=inc(P),
                             rom=Mem 
                           },
                    CPU#cpu.s)};


        Other ->
            Other
       end;

% 16#0d  !  store_plus
exec_impl(?STORE_PLUS,CPU) ->
   A = CPU#cpu.a,     
   T = CPU#cpu.t,
   case write(CPU,A,T) of 
        {ok,ram,Mem} ->
            {ok,pop(ds,
                    CPU#cpu{ a=inc(A),
                             ram=Mem 
                           },
                    CPU#cpu.s)};

        {ok,rom,Mem} ->
            {ok,pop(ds,
                    CPU#cpu{ a=inc(A),
                             rom=Mem 
                           },
                    CPU#cpu.s)};

        Other ->
            Other
       end;


% 16#0e  !b  store B
exec_impl(?STOREB,CPU) ->
   B = CPU#cpu.b,     
   T = CPU#cpu.t,
   case write(CPU,B,T) of 
        {ok,ram,Mem} ->
            {ok,pop(ds,CPU#cpu{ ram = Mem },CPU#cpu.s)};

        {ok,rom,Mem} ->
            {ok,pop(ds,CPU#cpu{ rom = Mem },CPU#cpu.s)};

        Other ->
            Other
       end;

% 16#0f  !  store
exec_impl(?STORE,CPU) ->
   A = CPU#cpu.a,     
   T = CPU#cpu.t,
   case write(CPU,A,T) of 
        {ok,ram,Mem} ->
            {ok,pop(ds,CPU#cpu{ ram = Mem },CPU#cpu.s)};

        {ok,rom,Mem} ->
            {ok,pop(ds,CPU#cpu{ rom = Mem },CPU#cpu.s)};

        Other ->
            Other
       end;

% 16#10  multiply
exec_impl(?MULTIPLY,CPU) ->
   A = CPU#cpu.a,
   P = CPU#cpu.p,
   <<_:17,A0:1>>        = <<A:18>>,
   <<P9:1,_/bitstring>> = <<P:10>>,

   case {A0,P9} of
	{0,_} -> 
	    T = CPU#cpu.t,
   	    T0  = T band 16#00001,   
   	    T17 = T band 16#20000,   
            {ok,CPU#cpu{ a = ((A bsr 1) bor (T0 bsl 17)) band 16#3ffff,
                         t = ((T bsr 1) bor T17) band 16#3ffff
                       }};

        {_,0} -> 
	    T = CPU#cpu.t + CPU#cpu.s,
  	    T0  = T band 16#00001,   
 	    T17 = T band 16#20000,   
            {ok,CPU#cpu{ a = ((A bsr 1) bor (T0 bsl 17)) band 16#3ffff,
                         t = ((T bsr 1) bor T17) band 16#3ffff
                       }};

        {_,_} -> 
	    T   = CPU#cpu.t + CPU#cpu.s + CPU#cpu.carry,
  	    T0  = T band 16#00001,   
 	    T17 = T band 16#20000,   
            {ok,CPU#cpu{ a     = ((A bsr 1) bor (T0 bsl 17)) band 16#3ffff,
                         t     = ((T bsr 1) bor T17) band 16#3ffff,
                         carry = T17 bsr 17
                       }}
        end;

% 16#11  2*   shl
exec_impl(?SHL,CPU) ->
   TS = CPU#cpu.t band 16#20000,   
   TV = CPU#cpu.t band 16#1ffff,   
   {ok,CPU#cpu{t = ((TV bsl 1) band 16#1ffff) bor TS
              }};


% 16#12  2/   shr
exec_impl(?SHR,CPU) ->
   TS = CPU#cpu.t band 16#20000,   
   TV = CPU#cpu.t band 16#3ffff,   
   {ok,CPU#cpu{t = ((TV bsr 1) band 16#1ffff) bor TS
              }};


% 16#13  -    not
exec_impl(?NOT,CPU) ->
   T = CPU#cpu.t band 16#3ffff,   
   {ok,CPU#cpu{t = ((bnot T) band 16#3ffff)
              }};

% 16#14  +   plus
exec_impl(?PLUS,CPU) ->
   T  = CPU#cpu.t band 16#3ffff,   
   S  = CPU#cpu.s band 16#3ffff,
   C  = CPU#cpu.carry,
   case (CPU#cpu.p band 16#0200) of
        16#0200 ->
    	    X    = (S + T + C) band 16#3ffff,
            CX   = (X band 16#3ffff) bsr 17,
            CPUX = pop(ds,CPU,X),
            {ok,CPUX#cpu{carry = CX
                        }};
 
        _else ->
            X = (S + T) band 16#3ffff,
            {ok,pop(ds,CPU,X)} 
         end;


% 16#15  and
exec_impl(?AND,CPU) ->
   T = CPU#cpu.t,
   S = CPU#cpu.s,
   {ok,pop(ds,CPU,(T band S) band 16#3ffff)};


% 16#16  or
exec_impl(?OR,CPU) ->
   T = CPU#cpu.t,
   S = CPU#cpu.s,
   {ok,pop(ds,CPU,(T bxor S) band 16#3ffff)};

% 16#17  drop
exec_impl(?DROP,CPU) ->
   S = CPU#cpu.s,
   {ok,pop(ds,CPU,S)};

% 16#18  dup
exec_impl(?DUP,CPU) ->
   {ok,push(ds,CPU)};

% 16#19  pop
exec_impl(?POP,CPU) ->
   R    = CPU#cpu.r,
   CPUX = push(ds,pop(rs,CPU)),
   {ok,CPUX#cpu{ t = R 
               }};

% 16#1a  over
exec_impl(?OVER,CPU) ->
   T    = CPU#cpu.t,
   S    = CPU#cpu.s,
   CPUX = push(ds,CPU),
   {ok,CPUX#cpu{ t = S,
                 s = T
               }};

% 16#1b  a
exec_impl(?A,CPU) ->
   A    = CPU#cpu.a,
   CPUX = push(ds,CPU),
   {ok,CPUX#cpu{ t = A
               }};

% 16#1c  .   nop
exec_impl(?NOP,CPU) ->
   {ok,CPU};

% 16#1d  push
exec_impl(?PUSH,CPU) ->
   T    = CPU#cpu.t,
   S    = CPU#cpu.s,
   CPUX = push(rs,pop(ds,CPU,S)),
   {ok,CPUX#cpu{ r = T 
               }};

% 16#1e  b!  b-store
exec_impl(?BSTORE,CPU) ->
   S = CPU#cpu.s,
   T = CPU#cpu.t,
   X = pop(ds,CPU,S),
   {ok,X#cpu{ b = T
            }};

% 16#1f  a!  a-store
exec_impl(?ASTORE,CPU) ->
   S = CPU#cpu.s,
   T = CPU#cpu.t,
   X = pop(ds,CPU,S),
   {ok,X#cpu{ a = T
            }};


exec_impl({error,Reason},_CPU) ->
   log:error(?TAG,"INVALID OPERATION ~p~n",[Reason]),
   {error,Reason};

exec_impl(OpCode,CPU) ->
   log:warn(?TAG,"UNIMPLEMENTED OPCODE: ~p~n",[OpCode]),
   {ok,CPU}.

% INSTRUCTION LOADER
%
load(CPU,P) ->
   load_impl(read(CPU,P)).

load_impl({ok,Word}) ->
   { ok,decode(Word) };

load_impl(eof) ->
   eof;

load_impl(_) ->
   error.

% OPCODE DECODER
%
decode(Word) ->
   W             = Word bxor 16#15555,
   <<S0:5,_:13>> = <<W:18>>,
   decode(opcode:opcode(S0),Word).

decode(?JUMP,Word) ->
   [{?JUMP,Word band 16#03ff,16#0000}];

decode(?CALL,Word) ->
   [{?CALL,Word band 16#03ff,16#0000}];

decode(?NEXT,Word) ->
   [{?NEXT,Word band 16#03ff,16#0000}];

decode(?IF,Word) ->
   [{?IF,Word band 16#03ff,16#0000}];

decode(?MINUSIF,Word) ->
   [{?MINUSIF,Word band 16#03ff,16#0000}];

decode(I0,Word) ->
   W            = Word bxor 16#15555,
   <<S1:5,_:8>> = <<W:13>>,
   decode(I0,opcode:opcode(S1),Word).

decode(I0,?JUMP,Word) ->
   [I0,{?JUMP,Word band 16#0ff,16#300}];

decode(I0,?CALL,Word) ->
   [I0,{?CALL,Word band 16#0ff,16#300}];

decode(I0,?NEXT,Word) ->
   [I0,{?NEXT,Word band 16#0ff,16#300}];

decode(I0,?IF,Word) ->
   [I0,{?IF,Word band 16#0ff,16#300}];

decode(I0,?MINUSIF,Word) ->
   [I0,{?MINUSIF,Word band 16#0ff,16#300}];

decode(I0,I1,Word) ->
   W            = Word bxor 16#15555,
   <<S2:5,_:3>> = <<W:8>>,
   decode(I0,I1,opcode:opcode(S2),Word).

decode(I0,I1,?JUMP,Word) ->
   [I0,I1,{?JUMP,Word band 16#007,16#3f8}];

decode(I0,I1,?CALL,Word) ->
   [I0,I1,{?CALL,Word band 16#007,16#3f8}];

decode(I0,I1,?NEXT,Word) ->
   [I0,I1,{?NEXT,Word band 16#007,16#3f8}];

decode(I0,I1,?IF,Word) ->
   [I0,I1,{?IF,Word band 16#007,16#3f8}];

decode(I0,I1,?MINUSIF,Word) ->
   [I0,I1,{?MINUSIF,Word band 16#007,16#3f8}];

decode(I0,I1,I2,Word) ->
   W        = Word bxor 16#15555,
   <<S3:3>> = <<W:3>>,
   [ I0,I1,I2,opcode:opcode(S3 bsl 2) ].

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
   read_channel(CPU,CPU#cpu.channel#channels.right);

read(CPU,?LEFT) ->
   read_channel(CPU,CPU#cpu.channel#channels.left);

read(CPU,?UP) ->
   read_channel(CPU,CPU#cpu.channel#channels.up);

read(CPU,?DOWN) ->
   read_channel(CPU,CPU#cpu.channel#channels.down);

read(CPU,Addr) when Addr < 16#200 ->
   read_mem(CPU#cpu.io,Addr-16#100).

read_mem(Mem,Addr) ->
   read_mem(Mem,Addr,array:size(Mem)).

read_mem(Mem,Addr,N) when Addr < N ->
   { ok,array:get(Addr,Mem) };

read_mem(_Mem,_Addr,_N) ->
   eof.

read_channel(CPU,Ch) ->
   notify   (CPU,reading),
   read_wait(CPU,Ch). 

read_wait(CPU,Ch) ->
    ID = CPU#cpu.id,   

    receive
        {Ch,write,Word} -> 
            Ch ! { ID,read,ok },
            {ok,Word};

        step ->
            read_channel(CPU,Ch);

        {step,PID} ->
   	        debug(read,CPU,CPU#cpu.log),
            PID ! {ID,step},
            read_wait(CPU,Ch);

        break ->
            break;

        {stop,PID} ->
            {stop,PID}
    end.

% WRITE

write(CPU,Addr,Word) when Addr < 16#40 ->
   write_mem(ram,CPU#cpu.ram,Addr,Word);

write(CPU,Addr,Word) when Addr < 16#80 ->
   write_mem(ram,CPU#cpu.ram,Addr band 16#3f,Word);

% TODO - CHECK WHAT HAPPENS ON SIMULATOR/EMULATOR
write(CPU,Addr,Word) when Addr < 16#C0 ->
   write_mem(rom,CPU#cpu.rom,Addr band 16#3f,Word);

% TODO - CHECK WHAT HAPPENS ON SIMULATOR/EMULATOR
write(CPU,Addr,Word) when Addr < 16#100 ->
   write_mem(rom,CPU#cpu.rom,Addr band 16#3f,Word);

write(CPU,?RIGHT,Word) ->
   write_channel(CPU,
                 CPU#cpu.channel#channels.right,
                 Word);

write(CPU,?LEFT,Word) ->
   write_channel(CPU,
                 CPU#cpu.channel#channels.left,
                 Word);

write(CPU,?UP,Word) ->
   write_channel(CPU,
                 CPU#cpu.channel#channels.up,
                 Word);

write(CPU,?DOWN,Word) ->
   write_channel(CPU,
                 CPU#cpu.channel#channels.down,
                 Word).

write_mem(Region,Mem,Addr,Word) ->
   write_mem(Region,Mem,Addr,Word,array:size(Mem)).

% TODO - FIX ARRAY SIZE AT 64
write_mem(Region,Mem,Addr,Word,N) when Addr < N ->
   { ok,Region,array:set(Addr,Word,Mem) };

write_mem(_Region,_Mem,_Addr,_Word,_N) ->
   eof.

write_channel(CPU,Ch,Word) ->
   write_channel(CPU,Ch,Word,util:is_registered(Ch)).

write_channel(CPU,Ch,Word,_) ->
   notify(CPU,writing),

   ID = CPU#cpu.id,
   try
      Ch ! { ID,write,Word },
      write_wait(CPU,Ch)
   catch
      error:badarg ->
         log:error(?TAG,"~p:WRITE to invalid node ~p",[ID,Ch]),   
         {error,invalid_peer};

      C:X ->
         log:error(?TAG,"~p:WRITE ~p failed ~p:~p",[ID,Ch,C,X]),   
         {error,{C,X}}
   end.
   
% write_channel(CPU,Ch,Word,_) ->
%    log:info(?TAG,"(~p:WRITE to unconnected node ~p)",[CPU#cpu.id,Ch]),   
%    {ok,CPU#cpu.ram}.

write_wait(CPU,Channel) ->
    ID = CPU#cpu.id,
    receive
        { Channel,read,ok } -> 
            {ok,ram,CPU#cpu.ram};

        step ->
            write_wait(CPU,Channel);

        {step,PID} ->
   	        debug(write,CPU,CPU#cpu.log),
            PID ! {ID,step},
            write_wait(CPU,Channel);

        break ->
            break;

       {stop,PID} ->
           {stop,PID}
    end.

% INCREMENT

inc(N) when N < 16#80  ->  (N + 1) rem 16#80;
inc(N) when N < 16#100 -> ((N + 1) rem 16#80) + 16#80;
inc(N) -> N.

% PUSH

push(ds,CPU) ->
   T          = CPU#cpu.t,
   S          = CPU#cpu.s,
   {SP,Stack} = CPU#cpu.ds,
   SPx        = (SP + 7) rem 8, 
   CPU#cpu{ s  = T,
            ds = {SPx,array:set(SPx,S,Stack)}
          };

push(rs,CPU) ->
   R          = CPU#cpu.r,
   {SP,Stack} = CPU#cpu.rs,
   SPx        = (SP + 7) rem 8, 
   CPU#cpu{ rs = {SPx,array:set(SPx,R,Stack)}
          }.

% POP

pop(ds,CPU,T) ->
   {SP,Stack} = CPU#cpu.ds,
   SPx        = (SP + 9) rem 8, 
   CPU#cpu{ t  = T,
            s  = array:get(SP,Stack),
            ds = {SPx,Stack}
          }.

pop(rs,CPU) ->
   {SP,Stack} = CPU#cpu.rs,
   SPx        = (SP + 9) rem 8, 
   CPU#cpu{ r  = array:get(SP,Stack),
            rs = {SPx,Stack}
          }.

% UTILITY FUNCTIONS
% 
notify(CPU,Msg) ->
   ID    = CPU#cpu.id,
   GA144 = CPU#cpu.ga144,

   case GA144 of
      undefined ->
         ok;

      PID ->
         PID ! {ID,Msg},
         ok
   end.

debug(_,_,no) ->
   ok;

debug({?JUMP,Addr,Mask},CPU,_) ->
   P = CPU#cpu.p,
   D = (P band Mask) bor Addr,
   log:debug  (?TAG,io_lib:format("~p: ~s ~p",[CPU#cpu.id,opcode:to_string(?JUMP),D]));

debug({?CALL,Addr,Mask},CPU,_) ->
   P = CPU#cpu.p,
   D = (P band Mask) bor Addr,
   log:debug  (?TAG,io_lib:format("~p: ~s ~p",[CPU#cpu.id,opcode:to_string(?CALL),D]));

debug(read,CPU,_) ->
   log:debug  (?TAG,io_lib:format("~p: ~s",[CPU#cpu.id,"<READ>"]));

debug(write,CPU,_) ->
   log:debug  (?TAG,io_lib:format("~p: ~s",[CPU#cpu.id,"<WRITE>"]));

debug(OpCode,CPU,_) ->
   log:debug  (?TAG,io_lib:format("~p: ~s",[CPU#cpu.id,opcode:to_string(OpCode)])).
   

trace(_,_,no) ->
   ok;

trace({?JUMP,_,_},CPU,_) ->
%  log:debug  (?TAG,io_lib:format("~p: ~s ~p",[CPU#cpu.id,opcode:to_string(?JUMP),CPU#cpu.p])),
   trace:trace(f18A,?JUMP,CPU);

trace({?CALL,_,_},CPU,_) ->
%  log:debug  (?TAG,io_lib:format("~p: ~s ~p",[CPU#cpu.id,opcode:to_string(?CALL),CPU#cpu.p])),
   trace:trace(f18A,?CALL,CPU);

trace(OpCode,CPU,_) ->
%  log:debug  (?TAG,io_lib:format("~p: ~s",[CPU#cpu.id,opcode:to_string(OpCode)])),
   trace:trace(f18A,OpCode,CPU).
   
% EUNIT TESTS

decode_test() ->
   ?assertEqual([{?JUMP,16#003,16#000}],decode(16#11403)),
   ?assertEqual([{?JUMP,16#000,16#000}],decode(16#11400)),
   ?assertEqual([{?JUMP,16#3ff,16#000}],decode(16#117ff)),

   ?assertEqual([?NOP,{?JUMP,16#003,16#300}],decode(16#2d703)),
   ?assertEqual([?NOP,{?JUMP,16#000,16#300}],decode(16#2d700)),
   ?assertEqual([?NOP,{?JUMP,16#0ff,16#300}],decode(16#2d7ff)),

   ?assertEqual([?NOP,?NOP,{?JUMP,16#03,16#3f8}],decode(16#2c943)),
   ?assertEqual([?NOP,?NOP,{?JUMP,16#00,16#3f8}],decode(16#2c940)),
   ?assertEqual([?NOP,?NOP,{?JUMP,16#07,16#3f8}],decode(16#2c947)),

   ?assertEqual([{?CALL,16#003,16#000}],decode(16#13403)),
   ?assertEqual([{?CALL,16#000,16#000}],decode(16#13400)),
   ?assertEqual([{?CALL,16#3ff,16#000}],decode(16#137ff)),

   ?assertEqual([?NOP,{?CALL,16#003,16#300}],decode(16#2d603)),
   ?assertEqual([?NOP,{?CALL,16#000,16#300}],decode(16#2d600)),
   ?assertEqual([?NOP,{?CALL,16#0ff,16#300}],decode(16#2d6ff)),

   ?assertEqual([?NOP,?NOP,{?CALL,16#03,16#3f8}],decode(16#2c94b)),
   ?assertEqual([?NOP,?NOP,{?CALL,16#00,16#3f8}],decode(16#2c948)),
   ?assertEqual([?NOP,?NOP,{?CALL,16#07,16#3f8}],decode(16#2c94f)),

   ?assertEqual([{?NEXT,16#003,16#000}],decode(16#1f403)),
   ?assertEqual([{?NEXT,16#000,16#000}],decode(16#1f400)),
   ?assertEqual([{?NEXT,16#3ff,16#000}],decode(16#1f7ff)),

   ?assertEqual([{?IF,16#003,16#000}],decode(16#18403)),
   ?assertEqual([{?IF,16#000,16#000}],decode(16#18400)),
   ?assertEqual([{?IF,16#3ff,16#000}],decode(16#187ff)),

   ?assertEqual([{?MINUSIF,16#003,16#000}],decode(16#1a003)),
   ?assertEqual([{?MINUSIF,16#000,16#000}],decode(16#1a000)),
   ?assertEqual([{?MINUSIF,16#3ff,16#000}],decode(16#1a7ff)),

   ?assertEqual([?NOP,?NOP,?NOP,?NOP],decode(16#2c9b2)),
   ?assertEqual([?NOP,?NOP,?NOP,?DUP],decode(16#2c9b3)),
   ?assertEqual([?NOP,?NOP,?DUP,?NOP],decode(16#2c992)),
   ?assertEqual([?NOP,?DUP,?NOP,?NOP],decode(16#2cdb2)),
   ?assertEqual([?DUP,?NOP,?NOP,?NOP],decode(16#249b2)).

push_ds_test() ->
   assert([{ds,{7,[1,2,3,4,5,6,7,0]}}],push(ds,#cpu{s=0,ds={0,array:from_list([1,2,3,4,5,6,7,8])}})),
   assert([{ds,{0,[0,2,3,4,5,6,7,8]}}],push(ds,#cpu{s=0,ds={1,array:from_list([1,2,3,4,5,6,7,8])}})),
   assert([{ds,{1,[1,0,3,4,5,6,7,8]}}],push(ds,#cpu{s=0,ds={2,array:from_list([1,2,3,4,5,6,7,8])}})),
   assert([{ds,{2,[1,2,0,4,5,6,7,8]}}],push(ds,#cpu{s=0,ds={3,array:from_list([1,2,3,4,5,6,7,8])}})),
   assert([{ds,{3,[1,2,3,0,5,6,7,8]}}],push(ds,#cpu{s=0,ds={4,array:from_list([1,2,3,4,5,6,7,8])}})),
   assert([{ds,{4,[1,2,3,4,0,6,7,8]}}],push(ds,#cpu{s=0,ds={5,array:from_list([1,2,3,4,5,6,7,8])}})),
   assert([{ds,{5,[1,2,3,4,5,0,7,8]}}],push(ds,#cpu{s=0,ds={6,array:from_list([1,2,3,4,5,6,7,8])}})),
   assert([{ds,{6,[1,2,3,4,5,6,0,8]}}],push(ds,#cpu{s=0,ds={7,array:from_list([1,2,3,4,5,6,7,8])}})).

push_rs_test() ->
   assert([{rs,{7,[1,2,3,4,5,6,7,0]}}],push(rs,#cpu{s=0,rs={0,array:from_list([1,2,3,4,5,6,7,8])}})),
   assert([{rs,{0,[0,2,3,4,5,6,7,8]}}],push(rs,#cpu{s=0,rs={1,array:from_list([1,2,3,4,5,6,7,8])}})),
   assert([{rs,{1,[1,0,3,4,5,6,7,8]}}],push(rs,#cpu{s=0,rs={2,array:from_list([1,2,3,4,5,6,7,8])}})),
   assert([{rs,{2,[1,2,0,4,5,6,7,8]}}],push(rs,#cpu{s=0,rs={3,array:from_list([1,2,3,4,5,6,7,8])}})),
   assert([{rs,{3,[1,2,3,0,5,6,7,8]}}],push(rs,#cpu{s=0,rs={4,array:from_list([1,2,3,4,5,6,7,8])}})),
   assert([{rs,{4,[1,2,3,4,0,6,7,8]}}],push(rs,#cpu{s=0,rs={5,array:from_list([1,2,3,4,5,6,7,8])}})),
   assert([{rs,{5,[1,2,3,4,5,0,7,8]}}],push(rs,#cpu{s=0,rs={6,array:from_list([1,2,3,4,5,6,7,8])}})),
   assert([{rs,{6,[1,2,3,4,5,6,0,8]}}],push(rs,#cpu{s=0,rs={7,array:from_list([1,2,3,4,5,6,7,8])}})).

-define(TEST_POPDS,[ { [{t,16#3ffff},{s,0},{ds,0,[1,2,3,4,5,6,7,8]}],[{t,0},{s,1},{ds,1,[1,2,3,4,5,6,7,8]}]},
                     { [{t,16#3ffff},{s,0},{ds,1,[1,2,3,4,5,6,7,8]}],[{t,0},{s,2},{ds,2,[1,2,3,4,5,6,7,8]}]},
                     { [{t,16#3ffff},{s,0},{ds,2,[1,2,3,4,5,6,7,8]}],[{t,0},{s,3},{ds,3,[1,2,3,4,5,6,7,8]}]},
                     { [{t,16#3ffff},{s,0},{ds,3,[1,2,3,4,5,6,7,8]}],[{t,0},{s,4},{ds,4,[1,2,3,4,5,6,7,8]}]},
                     { [{t,16#3ffff},{s,0},{ds,4,[1,2,3,4,5,6,7,8]}],[{t,0},{s,5},{ds,5,[1,2,3,4,5,6,7,8]}]},
                     { [{t,16#3ffff},{s,0},{ds,5,[1,2,3,4,5,6,7,8]}],[{t,0},{s,6},{ds,6,[1,2,3,4,5,6,7,8]}]},
                     { [{t,16#3ffff},{s,0},{ds,6,[1,2,3,4,5,6,7,8]}],[{t,0},{s,7},{ds,7,[1,2,3,4,5,6,7,8]}]},
                     { [{t,16#3ffff},{s,0},{ds,7,[1,2,3,4,5,6,7,8]}],[{t,0},{s,8},{ds,0,[1,2,3,4,5,6,7,8]}]}
                   ]).


-define(TEST_POPRS,[ { [{r,0},{rs,0,[1,2,3,4,5,6,7,8]}],[{r,1},{rs,1,[1,2,3,4,5,6,7,8]}]},
                     { [{r,0},{rs,1,[1,2,3,4,5,6,7,8]}],[{r,2},{rs,2,[1,2,3,4,5,6,7,8]}]},
                     { [{r,0},{rs,2,[1,2,3,4,5,6,7,8]}],[{r,3},{rs,3,[1,2,3,4,5,6,7,8]}]},
                     { [{r,0},{rs,3,[1,2,3,4,5,6,7,8]}],[{r,4},{rs,4,[1,2,3,4,5,6,7,8]}]},
                     { [{r,0},{rs,4,[1,2,3,4,5,6,7,8]}],[{r,5},{rs,5,[1,2,3,4,5,6,7,8]}]},
                     { [{r,0},{rs,5,[1,2,3,4,5,6,7,8]}],[{r,6},{rs,6,[1,2,3,4,5,6,7,8]}]},
                     { [{r,0},{rs,6,[1,2,3,4,5,6,7,8]}],[{r,7},{rs,7,[1,2,3,4,5,6,7,8]}]},
                     { [{r,0},{rs,7,[1,2,3,4,5,6,7,8]}],[{r,8},{rs,0,[1,2,3,4,5,6,7,8]}]}
                   ]).

pop_ds_test() ->
    lists:foreach(fun({Initial,Final}) -> 
                          CPU = test_cpu(),
                          I   = test_init(CPU,Initial),
                          F   = test_init(CPU,Final),
                          X   = pop(ds,I,0),
                          test_verify(F,X)
                  end,
                  ?TEST_POPDS).

pop_rs_test() ->
    lists:foreach(fun({Initial,Final}) -> 
                          CPU = test_cpu(),
                          I   = test_init(CPU,Initial),
                          F   = test_init(CPU,Final),
                          X   = pop(rs,I),
                          test_verify(F,X)
                  end,
                  ?TEST_POPRS).

-define(TEST_RET,[{?RET,
                   [{p,1},{r,2},{rs,0,[3,4,5,6,7,8,9,10]},{i,[?NOP,?NOP,?NOP,?NOP]}],
                   [{p,2},{r,3},{rs,1,[3,4,5,6,7,8,9,10]},{i,[]}] }
                 ]).

-define(TEST_EX,[{?EX,
                   [{p,16#0a9},{r,16#03}],
                   [{p,16#003},{r,16#0a9}]} 
                 ]).

-define(TEST_UNEXT,[{?UNEXT,
                     [{r,16#000},{rs,0,[1,2,3,4,5,6,7,8]},{i,[?NOP,?NOP,?NOP,?NOP]},{im,[?RET,?RET,?RET,?RET]}],
                     [{r,1},     {rs,1,[1,2,3,4,5,6,7,8]},{i,[]},                   {im,[?RET,?RET,?RET,?RET]}]},

                    {?UNEXT,
                     [{r,3},{rs,0,[1,2,3,4,5,6,7,8]},{i,[?UNEXT]},               {im,[?NOP,?NOP,?NOP,?UNEXT]}],
                     [{r,2},{rs,0,[1,2,3,4,5,6,7,8]},{i,[?NOP,?NOP,?NOP,?UNEXT]},{im,[?NOP,?NOP,?NOP,?UNEXT]}]}
                  ]). 

-define(TEST_NEXT,[{{?NEXT,16#03,16#0000},
                    [{p,16#0a9},{r,16#000},{rs,0,[1,2,3,4,5,6,7,8]},{i,[?RET,?RET,?RET,?RET]}],
                    [{p,16#0aa},{r,1},     {rs,1,[1,2,3,4,5,6,7,8]},{i,[]}] },

                   {{?NEXT,16#03,16#0000},
                    [{p,16#0a9},{r,16#001},{rs,0,[1,2,3,4,5,6,7,8]},{i,[?RET,?RET,?RET,?RET]}],
                    [{p,16#003},{r,0},     {rs,0,[1,2,3,4,5,6,7,8]},{i,[]}] }
                  ]). 

-define(TEST_IF,[{{?IF,16#03,16#0000},
                  [{p,16#0a9},{t,1},{i,[?RET,?RET,?RET,?RET]}],
                  [{p,16#0aa},{t,1},{i,[]}] },

                 {{?IF,16#03,16#0000},
                  [{p,16#0a9},{t,0},{i,[?RET,?RET,?RET,?RET]}],
                  [{p,16#003},{t,0},{i,[]}] }
                ]). 

-define(TEST_MINUSIF,[{{?MINUSIF,16#03,16#0000},
                       [{p,16#0a9},{t,1},{i,[?RET,?RET,?RET,?RET]}],
                       [{p,16#003},{t,1},{i,[]}] },

                      {{?MINUSIF,16#03,16#0000},
                       [{p,16#0a9},{t,0},{i,[?RET,?RET,?RET,?RET]}],
                       [{p,16#003},{t,0},{i,[]}] },

                      {{?MINUSIF,16#03,16#0000},
                       [{p,16#0a9},{t,16#20000},{i,[?RET,?RET,?RET,?RET]}],
                       [{p,16#0aa},{t,16#20000},{i,[]}] }
                     ]). 

-define(TEST_JUMP,[{{?JUMP,16#03,16#0000},
                    [{p,16#0a9},{i,[?RET,?RET,?RET,?RET]}],
                    [{p,16#003},{i,[]}] } 
                  ]).

-define(TEST_CALL,[{{?CALL,16#03,16#0000},
                    [{p,16#0a9},{r,16#000},{rs,0,[1,2,3,4,5,6,7,8]},{i,[?RET,?RET,?RET,?RET]}],
                    [{p,16#003},{r,16#0a9},{rs,7,[1,2,3,4,5,6,7,0]},{i,[]}] }
                  ]). 

% TODO: ADD TESTS FOR I/O
-define(TEST_FETCHP,[{?FETCHP,
                      [{ram,15,678},{p,15},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{ram,15,678},{p,16},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]},

                     {?FETCHP,
                      [{ram,0,678},{p,0},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{ram,0,678},{p,1},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]},

                     {?FETCHP,
                      [{ram,16#3f,678},{p,16#3f},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{ram,16#3f,678},{p,16#40},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]},

                     {?FETCHP,
                      [{ram,16#3f,678},{p,16#7f},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{ram,16#3f,678},{p,16#00},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]},

                     {?FETCHP,
                      [{rom,15,876},{p,16#8f},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{rom,15,876},{p,16#90},{t,876},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]},

                     {?FETCHP,
                      [{rom,0,678},{p,16#80},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{rom,0,678},{p,16#81},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]},

                     {?FETCHP,
                      [{rom,16#3f,678},{p,16#bf},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{rom,16#3f,678},{p,16#c0},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]},

                     {?FETCHP,
                      [{rom,16#3f,678},{p,16#ff},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{rom,16#3f,678},{p,16#80},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]}
                    ]).

% TODO: ADD TESTS FOR I/O
-define(TEST_FETCH_PLUS,[{?FETCH_PLUS,
                          [{ram,15,678},{a,15},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                          [{ram,15,678},{a,16},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]},

                         {?FETCH_PLUS,
                          [{ram,0,678},{a,0},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                          [{ram,0,678},{a,1},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]},

                         {?FETCH_PLUS,
                          [{ram,16#3f,678},{a,16#3f},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                          [{ram,16#3f,678},{a,16#40},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]},

                         {?FETCH_PLUS,
                          [{ram,16#3f,678},{a,16#7f},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                          [{ram,16#3f,678},{a,16#00},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]},

                         {?FETCH_PLUS,
                          [{rom,15,876},{a,16#8f},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                          [{rom,15,876},{a,16#90},{t,876},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]},

                         {?FETCH_PLUS,
                          [{rom,0,678},{a,16#80},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                          [{rom,0,678},{a,16#81},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]},

                         {?FETCH_PLUS,
                          [{rom,16#3f,678},{a,16#bf},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                          [{rom,16#3f,678},{a,16#c0},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]},

                         {?FETCH_PLUS,
                          [{rom,16#3f,678},{a,16#ff},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                          [{rom,16#3f,678},{a,16#80},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]}
                        ]).

-define(TEST_FETCHB,[{?FETCHB,
                     [{ram,15,678},{b,15},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                     [{ram,15,678},{b,15},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]}
                   ]).

-define(TEST_FETCH,[{?FETCH,
                     [{ram,15,678},{a,15},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                     [{ram,15,678},{a,15},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]}
                   ]).

% TODO: ADD TESTS FOR I/O
-define(TEST_STOREP,[{?STOREP,
                      [{ram,0,0},{p,0},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{ram,0,1},{p,1},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]},

                     {?STOREP,
                      [{ram,16#3f,0},{p,16#3f},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{ram,16#3f,1},{p,16#40},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]},

                     {?STOREP,
                      [{ram,16#3f,0},{p,16#7f},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{ram,16#3f,1},{p,16#00},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]},

                     {?STOREP,
                      [{rom,15,0},{p,16#8f},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{rom,15,1},{p,16#90},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]},

                     {?STOREP,
                      [{rom,0,0},{p,16#80},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{rom,0,1},{p,16#81},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]},

                     {?STOREP,
                      [{rom,16#3f,0},{p,16#bf},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{rom,16#3f,1},{p,16#c0},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]},

                     {?STOREP,
                      [{rom,16#3f,0},{p,16#ff},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                      [{rom,16#3f,1},{p,16#80},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]}
                    ]).

% TODO: ADD TESTS FOR I/O
-define(TEST_STORE_PLUS,[{?STORE_PLUS,
                         [{ram,0,0},{a,0},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                         [{ram,0,1},{a,1},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]},

                         {?STORE_PLUS,
                          [{ram,16#3f,0},{a,16#3f},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                          [{ram,16#3f,1},{a,16#40},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]},
    
                         {?STORE_PLUS,
                          [{ram,16#3f,0},{a,16#7f},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                          [{ram,16#3f,1},{a,16#00},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]},
    
                         {?STORE_PLUS,
                          [{rom,15,0},{a,16#8f},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                          [{rom,15,1},{a,16#90},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]},
    
                         {?STORE_PLUS,
                          [{rom,0,0},{a,16#80},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                          [{rom,0,1},{a,16#81},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]},
    
                         {?STORE_PLUS,
                          [{rom,16#3f,0},{a,16#bf},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                          [{rom,16#3f,1},{a,16#c0},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]},
    
                         {?STORE_PLUS,
                          [{rom,16#3f,0},{a,16#ff},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                          [{rom,16#3f,1},{a,16#80},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]}
                        ]).
    

-define(TEST_STOREB,[{?STOREB,
                      [{ram,4,0},  {b,4},{t,678},{s,9},{ds,0,[1,2,3,4,5,6,7,8]}],
                      [{ram,4,678},{b,4},{t,9},{s,1},{ds,1,[1,2,3,4,5,6,7,8]}]}
                    ]).

-define(TEST_STORE,[{?STORE,
                     [{ram,0,0},{a,0},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                     [{ram,0,1},{a,0},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]}
                   ]).

-define(TEST_MULTIPLY,[ {?MULTIPLY,[{p,16#00},{a,0},{t,0}],[{p,16#00},{a,16#00000},{t,0}]},
                        {?MULTIPLY,[{p,16#00},{a,0},{t,1}],[{p,16#00},{a,16#20000},{t,0}]},
                        {?MULTIPLY,[{p,16#00},{a,0},{t,2}],[{p,16#00},{a,16#00000},{t,1}]},
                        {?MULTIPLY,[{p,16#00},{a,0},{t,16#20000}],[{p,16#00},{a,16#00000},{t,16#30000}]},
                        {?MULTIPLY,[{p,16#00},{a,0},{t,16#20001}],[{p,16#00},{a,16#20000},{t,16#30000}]},
                        {?MULTIPLY,[{p,16#00},{a,0},{t,16#20002}],[{p,16#00},{a,16#00000},{t,16#30001}]},

                        {?MULTIPLY,[{p,16#00},{a,2},{t,0}],[{p,16#00},{a,16#00001},{t,0}]},
                        {?MULTIPLY,[{p,16#00},{a,2},{t,1}],[{p,16#00},{a,16#20001},{t,0}]},
                        {?MULTIPLY,[{p,16#00},{a,2},{t,2}],[{p,16#00},{a,16#00001},{t,1}]},
                        {?MULTIPLY,[{p,16#00},{a,2},{t,16#20000}],[{p,16#00},{a,16#00001},{t,16#30000}]},
                        {?MULTIPLY,[{p,16#00},{a,2},{t,16#20001}],[{p,16#00},{a,16#20001},{t,16#30000}]},
                        {?MULTIPLY,[{p,16#00},{a,2},{t,16#20002}],[{p,16#00},{a,16#00001},{t,16#30001}]},

                        {?MULTIPLY,[{p,16#00},{a,1},{t,0},       {s,0}],[{p,16#00},{a,16#00000},{t,0},       {s,0}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,1},       {s,0}],[{p,16#00},{a,16#20000},{t,0},       {s,0}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,2},       {s,0}],[{p,16#00},{a,16#00000},{t,1},       {s,0}]},

                        {?MULTIPLY,[{p,16#00},{a,1},{t,0},       {s,1}],[{p,16#00},{a,16#20000},{t,0},       {s,1}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,1},       {s,1}],[{p,16#00},{a,16#00000},{t,1},       {s,1}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,2},       {s,1}],[{p,16#00},{a,16#20000},{t,1},       {s,1}]},

                        {?MULTIPLY,[{p,16#00},{a,1},{t,0},       {s,2}],[{p,16#00},{a,16#00000},{t,1},       {s,2}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,1},       {s,2}],[{p,16#00},{a,16#20000},{t,1},       {s,2}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,2},       {s,2}],[{p,16#00},{a,16#00000},{t,2},       {s,2}]},

                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20000},{s,0}],[{p,16#00},{a,16#00000},{t,16#30000},{s,0}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20001},{s,0}],[{p,16#00},{a,16#20000},{t,16#30000},{s,0}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20002},{s,0}],[{p,16#00},{a,16#00000},{t,16#30001},{s,0}]},

                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20000},{s,1}],[{p,16#00},{a,16#20000},{t,16#30000},{s,1}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20001},{s,1}],[{p,16#00},{a,16#00000},{t,16#30001},{s,1}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20002},{s,1}],[{p,16#00},{a,16#20000},{t,16#30001},{s,1}]},

                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20000},{s,2}],[{p,16#00},{a,16#00000},{t,16#30001},{s,2}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20001},{s,2}],[{p,16#00},{a,16#20000},{t,16#30001},{s,2}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20002},{s,2}],[{p,16#00},{a,16#00000},{t,16#30002},{s,2}]},

                        {?MULTIPLY,[{p,16#00},{a,3},{t,0},       {s,0}],[{p,16#00},{a,16#00001},{t,0},       {s,0}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,1},       {s,0}],[{p,16#00},{a,16#20001},{t,0},       {s,0}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,2},       {s,0}],[{p,16#00},{a,16#00001},{t,1},       {s,0}]},

                        {?MULTIPLY,[{p,16#00},{a,3},{t,0},       {s,1}],[{p,16#00},{a,16#20001},{t,0},       {s,1}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,1},       {s,1}],[{p,16#00},{a,16#00001},{t,1},       {s,1}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,2},       {s,1}],[{p,16#00},{a,16#20001},{t,1},       {s,1}]},

                        {?MULTIPLY,[{p,16#00},{a,3},{t,0},       {s,2}],[{p,16#00},{a,16#00001},{t,1},       {s,2}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,1},       {s,2}],[{p,16#00},{a,16#20001},{t,1},       {s,2}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,2},       {s,2}],[{p,16#00},{a,16#00001},{t,2},       {s,2}]},

                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20000},{s,0}],[{p,16#00},{a,16#00001},{t,16#30000},{s,0}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20001},{s,0}],[{p,16#00},{a,16#20001},{t,16#30000},{s,0}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20002},{s,0}],[{p,16#00},{a,16#00001},{t,16#30001},{s,0}]},

                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20000},{s,1}],[{p,16#00},{a,16#20001},{t,16#30000},{s,1}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20001},{s,1}],[{p,16#00},{a,16#00001},{t,16#30001},{s,1}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20002},{s,1}],[{p,16#00},{a,16#20001},{t,16#30001},{s,1}]},

                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20000},{s,2}],[{p,16#00},{a,16#00001},{t,16#30001},{s,2}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20001},{s,2}],[{p,16#00},{a,16#20001},{t,16#30001},{s,2}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20002},{s,2}],[{p,16#00},{a,16#00001},{t,16#30002},{s,2}]},

                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20000},{s,16#20000}],[{p,16#00},{a,16#00000},{t,16#20000},{s,16#20000}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20001},{s,16#20000}],[{p,16#00},{a,16#20000},{t,16#20000},{s,16#20000}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20002},{s,16#20000}],[{p,16#00},{a,16#00000},{t,16#20001},{s,16#20000}]},

                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20000},{s,16#20001}],[{p,16#00},{a,16#20000},{t,16#20000},{s,16#20001}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20001},{s,16#20001}],[{p,16#00},{a,16#00000},{t,16#20001},{s,16#20001}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20002},{s,16#20001}],[{p,16#00},{a,16#20000},{t,16#20001},{s,16#20001}]},

                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20000},{s,16#20002}],[{p,16#00},{a,16#00000},{t,16#20001},{s,16#20002}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20001},{s,16#20002}],[{p,16#00},{a,16#20000},{t,16#20001},{s,16#20002}]},
                        {?MULTIPLY,[{p,16#00},{a,1},{t,16#20002},{s,16#20002}],[{p,16#00},{a,16#00000},{t,16#20002},{s,16#20002}]},

                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20000},{s,16#20000}],[{p,16#00},{a,16#00001},{t,16#20000},{s,16#20000}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20001},{s,16#20000}],[{p,16#00},{a,16#20001},{t,16#20000},{s,16#20000}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20002},{s,16#20000}],[{p,16#00},{a,16#00001},{t,16#20001},{s,16#20000}]},

                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20000},{s,16#20001}],[{p,16#00},{a,16#20001},{t,16#20000},{s,16#20001}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20001},{s,16#20001}],[{p,16#00},{a,16#00001},{t,16#20001},{s,16#20001}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20002},{s,16#20001}],[{p,16#00},{a,16#20001},{t,16#20001},{s,16#20001}]},

                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20000},{s,16#20002}],[{p,16#00},{a,16#00001},{t,16#20001},{s,16#20002}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20001},{s,16#20002}],[{p,16#00},{a,16#20001},{t,16#20001},{s,16#20002}]},
                        {?MULTIPLY,[{p,16#00},{a,3},{t,16#20002},{s,16#20002}],[{p,16#00},{a,16#00001},{t,16#20002},{s,16#20002}]},

                        {?MULTIPLY, [{p,16#200},{a,1},{t,0},{s,0},{carry,0}], [{p,16#200},{a,0},{t,0},{s,0},{carry,0}]},
                        {?MULTIPLY, [{p,16#200},{a,1},{t,0},{s,0},{carry,1}], [{p,16#200},{a,16#20000},{t,0},{s,0},{carry,0}]},
                        {?MULTIPLY, [{p,16#200},{a,1},{t,1},{s,0},{carry,1}], [{p,16#200},{a,0},       {t,1},{s,0},{carry,0}]},
                        {?MULTIPLY, [{p,16#200},{a,1},{t,2},{s,0},{carry,1}], [{p,16#200},{a,16#20000},{t,1},{s,0},{carry,0}]},

                        {?MULTIPLY, [{p,16#200},{a,1},{t,0},{s,1},{carry,1}], [{p,16#200},{a,0},       {t,1},{s,1},{carry,0}]},
                        {?MULTIPLY, [{p,16#200},{a,1},{t,1},{s,1},{carry,1}], [{p,16#200},{a,16#20000},{t,1},{s,1},{carry,0}]},
                        {?MULTIPLY, [{p,16#200},{a,1},{t,2},{s,1},{carry,1}], [{p,16#200},{a,0},       {t,2},{s,1},{carry,0}]},

                        {?MULTIPLY, [{p,16#200},{a,1},{t,0},{s,2},{carry,1}], [{p,16#200},{a,16#20000},{t,1},{s,2},{carry,0}]},
                        {?MULTIPLY, [{p,16#200},{a,1},{t,1},{s,2},{carry,1}], [{p,16#200},{a,0},       {t,2},{s,2},{carry,0}]},
                        {?MULTIPLY, [{p,16#200},{a,1},{t,2},{s,2},{carry,1}], [{p,16#200},{a,16#20000},{t,2},{s,2},{carry,0}]},

                        {?MULTIPLY,[{p,16#200},{a,1},{t,16#20000},{s,0},{carry,0}],[{p,16#200},{a,0},       {t,16#30000},{s,0},{carry,1}]},
                        {?MULTIPLY,[{p,16#200},{a,1},{t,16#20001},{s,0},{carry,0}],[{p,16#200},{a,16#20000},{t,16#30000},{s,0},{carry,1}]},
                        {?MULTIPLY,[{p,16#200},{a,1},{t,16#20002},{s,0},{carry,0}],[{p,16#200},{a,0},       {t,16#30001},{s,0},{carry,1}]}
                      ]).

-define(TEST_SHL,[ {?SHL,[{t,16#00001}],[{t,16#00002}]},
                   {?SHL,[{t,16#00002}],[{t,16#00004}]},
                   {?SHL,[{t,16#00004}],[{t,16#00008}]},
                   {?SHL,[{t,16#00008}],[{t,16#00010}]},
                   {?SHL,[{t,16#00010}],[{t,16#00020}]},
                   {?SHL,[{t,16#00020}],[{t,16#00040}]},
                   {?SHL,[{t,16#00040}],[{t,16#00080}]},
                   {?SHL,[{t,16#00080}],[{t,16#00100}]},
                   {?SHL,[{t,16#00100}],[{t,16#00200}]},
                   {?SHL,[{t,16#00200}],[{t,16#00400}]},
                   {?SHL,[{t,16#00400}],[{t,16#00800}]},
                   {?SHL,[{t,16#00800}],[{t,16#01000}]},
                   {?SHL,[{t,16#01000}],[{t,16#02000}]},
                   {?SHL,[{t,16#02000}],[{t,16#04000}]},
                   {?SHL,[{t,16#04000}],[{t,16#08000}]},
                   {?SHL,[{t,16#08000}],[{t,16#10000}]},
                   {?SHL,[{t,16#10000}],[{t,16#00000}]},

                   {?SHL,[{t,16#20000}],[{t,16#20000}]},
                   {?SHL,[{t,16#3ffff}],[{t,16#3fffe}]},
                   {?SHL,[{t,16#30000}],[{t,16#20000}]}
                 ]).


-define(TEST_SHR,[ {?SHR,[{t,16#00001}],[{t,16#00000}]},
                   {?SHR,[{t,16#00002}],[{t,16#00001}]},
                   {?SHR,[{t,16#00004}],[{t,16#00002}]},
                   {?SHR,[{t,16#00008}],[{t,16#00004}]},
                   {?SHR,[{t,16#00010}],[{t,16#00008}]},
                   {?SHR,[{t,16#00020}],[{t,16#00010}]},
                   {?SHR,[{t,16#00040}],[{t,16#00020}]},
                   {?SHR,[{t,16#00080}],[{t,16#00040}]},
                   {?SHR,[{t,16#00100}],[{t,16#00080}]},
                   {?SHR,[{t,16#00200}],[{t,16#00100}]},
                   {?SHR,[{t,16#00400}],[{t,16#00200}]},
                   {?SHR,[{t,16#00800}],[{t,16#00400}]},
                   {?SHR,[{t,16#01000}],[{t,16#00800}]},
                   {?SHR,[{t,16#02000}],[{t,16#01000}]},
                   {?SHR,[{t,16#04000}],[{t,16#02000}]},
                   {?SHR,[{t,16#08000}],[{t,16#04000}]},
                   {?SHR,[{t,16#10000}],[{t,16#08000}]},

                   {?SHR,[{t,16#20000}],[{t,16#30000}]},
                   {?SHR,[{t,16#3fffe}],[{t,16#3ffff}]},
                   {?SHR,[{t,16#30000}],[{t,16#38000}]}
                 ]).


-define(TEST_NOT,[ {?NOT,[{t,16#00000}],[{t,16#3ffff}]},
                   {?NOT,[{t,16#15555}],[{t,16#2aaaa}]},
                   {?NOT,[{t,16#2aaaa}],[{t,16#15555}]},
                   {?NOT,[{t,16#3ffff}],[{t,16#00000}]}
                 ]).

-define(TEST_PLUS,[ {?PLUS,
                     [{p,16#0000},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]},{carry,0}],
                     [{p,16#0000},{t,3},{s,3},{ds,1,[3,4,5,6,7,8,9,10]},{carry,0}]},

                    {?PLUS,
                     [{p,16#0000},{t,16#3ffff},{s,16#3fffe},{ds,0,[3,4,5,6,7,8,9,10]},{carry,0}],
                     [{p,16#0000},{t,16#3fffd},{s,3},       {ds,1,[3,4,5,6,7,8,9,10]}]},

                    {?PLUS,
                     [{p,16#0000},{t,16#3ffff},{s,1},{ds,0,[3,4,5,6,7,8,9,10]},{carry,0}],
                     [{p,16#0000},{t,16#00000},{s,3},{ds,1,[3,4,5,6,7,8,9,10]},{carry,0}]},

                    {?PLUS,
                     [{p,16#0000},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]},{carry,1}],
                     [{p,16#0000},{t,3},{s,3},{ds,1,[3,4,5,6,7,8,9,10]},{carry,1}]},

                    {?PLUS,
                     [{p,16#0000},{t,16#3ffff},{s,16#3fffe},{ds,0,[3,4,5,6,7,8,9,10]},{carry,1}],
                     [{p,16#0000},{t,16#3fffd},{s,3},       {ds,1,[3,4,5,6,7,8,9,10]},{carry,1}]},

                    {?PLUS,
                     [{p,16#0000},{t,16#3ffff},{s,1},{ds,0,[3,4,5,6,7,8,9,10]},{carry,1}],
                     [{p,16#0000},{t,16#00000},{s,3},{ds,1,[3,4,5,6,7,8,9,10]},{carry,1}]},

                    {?PLUS,
                     [{p,16#0200},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]},{carry,0}],
                     [{p,16#0200},{t,3},{s,3},{ds,1,[3,4,5,6,7,8,9,10]},{carry,0}]},

                    {?PLUS,
                     [{p,16#0200},{t,16#3ffff},{s,16#3fffe},{ds,0,[3,4,5,6,7,8,9,10]},{carry,0}],
                     [{p,16#0200},{t,16#3fffd},{s,3},       {ds,1,[3,4,5,6,7,8,9,10]},{carry,1}]},

                    {?PLUS,
                     [{p,16#0200},{t,16#3ffff},{s,1},{ds,0,[3,4,5,6,7,8,9,10]},{carry,0}],
                     [{p,16#0200},{t,16#00000},{s,3},{ds,1,[3,4,5,6,7,8,9,10]},{carry,0}]},

                    {?PLUS,
                     [{p,16#0200},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]},{carry,1}],
                     [{p,16#0200},{t,4},{s,3},{ds,1,[3,4,5,6,7,8,9,10]},{carry,0}]},

                    {?PLUS,
                     [{p,16#0200},{t,16#3ffff},{s,16#3fffe},{ds,0,[3,4,5,6,7,8,9,10]},{carry,1}],
                     [{p,16#0200},{t,16#3fffe},{s,3},       {ds,1,[3,4,5,6,7,8,9,10]},{carry,1}]},

                    {?PLUS,
                     [{p,16#0200},{t,16#3ffff},{s,1},{ds,0,[3,4,5,6,7,8,9,10]},{carry,1}],
                     [{p,16#0200},{t,1},       {s,3},{ds,1,[3,4,5,6,7,8,9,10]},{carry,0}]}
                  ]).

-define(TEST_AND,[ {?AND,
                    [{t,16#00000},{s,16#00000},{ds,0,[1,2,3,4,5,6,7,8]}],
                    [{t,16#00000},{s,1},       {ds,1,[1,2,3,4,5,6,7,8]}]},

                   {?AND,
                    [{t,16#3ffff},{s,16#00000},{ds,0,[1,2,3,4,5,6,7,8]}],
                    [{t,16#00000},{s,1},       {ds,1,[1,2,3,4,5,6,7,8]}]},

                   {?AND,
                    [{t,16#00000},{s,16#3ffff},{ds,0,[1,2,3,4,5,6,7,8]}],
                    [{t,16#00000},{s,1},       {ds,1,[1,2,3,4,5,6,7,8]}]},

                   {?AND,
                    [{t,16#3ffff},{s,16#3ffff},{ds,0,[1,2,3,4,5,6,7,8]}],
                    [{t,16#3ffff},{s,1},       {ds,1,[1,2,3,4,5,6,7,8]}]},

                   {?AND,
                    [{t,16#3ffff},{s,16#15555},{ds,0,[1,2,3,4,5,6,7,8]}],
                    [{t,16#15555},{s,1},       {ds,1,[1,2,3,4,5,6,7,8]}]},

                   {?AND,
                    [{t,16#15555},{s,16#3ffff},{ds,0,[1,2,3,4,5,6,7,8]}],
                    [{t,16#15555},{s,1},       {ds,1,[1,2,3,4,5,6,7,8]}]}
                 ]).

-define(TEST_OR,[ {?OR,
                    [{t,16#00000},{s,16#00000},{ds,0,[1,2,3,4,5,6,7,8]}],
                    [{t,16#00000},{s,1},       {ds,1,[1,2,3,4,5,6,7,8]}]},

                   {?OR,
                    [{t,16#3ffff},{s,16#00000},{ds,0,[1,2,3,4,5,6,7,8]}],
                    [{t,16#3ffff},{s,1},       {ds,1,[1,2,3,4,5,6,7,8]}]},

                   {?OR,
                    [{t,16#00000},{s,16#3ffff},{ds,0,[1,2,3,4,5,6,7,8]}],
                    [{t,16#3ffff},{s,1},       {ds,1,[1,2,3,4,5,6,7,8]}]},

                   {?OR,
                    [{t,16#3ffff},{s,16#3ffff},{ds,0,[1,2,3,4,5,6,7,8]}],
                    [{t,16#00000},{s,1},       {ds,1,[1,2,3,4,5,6,7,8]}]},

                   {?OR,
                    [{t,16#3ffff},{s,16#15555},{ds,0,[1,2,3,4,5,6,7,8]}],
                    [{t,16#2aaaa},{s,1},       {ds,1,[1,2,3,4,5,6,7,8]}]},

                   {?OR,
                    [{t,16#15555},{s,16#3ffff},{ds,0,[1,2,3,4,5,6,7,8]}],
                    [{t,16#2aaaa},{s,1},       {ds,1,[1,2,3,4,5,6,7,8]}]}
                 ]).

-define(TEST_DROP,[ {?DROP,
                    [{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                    [{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]
                   } ]).

-define(TEST_DUP,[ {?DUP,
                    [{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                    [{t,1},{s,1},{ds,7,[3,4,5,6,7,8,9,2 ]}]
                   } ]).

-define(TEST_POP,[ {?POP,
                    [{r,1}, {t,2},{s,3},{ds,0,[4,5,6,7,8,9,10,11]},{rs,0,[12,13,14,15,16,17,18,19]}],
                    [{r,12},{t,1},{s,2},{ds,7,[4,5,6,7,8,9,10,3 ]},{rs,1,[12,13,14,15,16,17,18,19]}]
                   } ]).

-define(TEST_OVER,[ {?OVER,
                    [{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                    [{t,2},{s,1},{ds,7,[3,4,5,6,7,8,9,2 ]}]
                   } ]).

-define(TEST_A,[ {?A,
                  [{a,1},{t,2},{s,3},{ds,0,[4,5,6,7,8,9,10,11]}],
                  [{a,1},{t,1},{s,2},{ds,7,[4,5,6,7,8,9,10,3 ]}]
                 } ]).

-define(TEST_NOP,[ {?NOP,
                    [],
                    []
                   } ]).

-define(TEST_PUSH,[ {?PUSH,
                    [{r,1},{t,2},{s,3},{ds,0,[4,5,6,7,8,9,10,11]},{rs,0,[12,13,14,15,16,17,18,19]}],
                    [{r,2},{t,3},{s,4},{ds,1,[4,5,6,7,8,9,10,11]},{rs,7,[12,13,14,15,16,17,18,1 ]}]
                   } ]).

-define(TEST_BSTORE,[ {?BSTORE,
                       [{b,0},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                       [{b,1},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]
                      }]).

-define(TEST_ASTORE,[ {?ASTORE,
                       [{a,0},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                       [{a,1},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]
                      }]).

-define(RND,   random:uniform(16#40000) - 1).
-define(RND(N),random:uniform(N+1) - 1).

ret_test()       -> test_opcode(?TEST_RET).
ex_test()        -> test_opcode(?TEST_EX).
jump_test()      -> test_opcode(?TEST_JUMP).
call_test()      -> test_opcode(?TEST_CALL).
unext_test()     -> test_opcode(?TEST_UNEXT).
next_test()      -> test_opcode(?TEST_NEXT).
if_test()        -> test_opcode(?TEST_IF).
minusif_test()   -> test_opcode(?TEST_MINUSIF).
fetchp_test()    -> test_opcode(?TEST_FETCHP).
fetchplus_test() -> test_opcode(?TEST_FETCH_PLUS).
fetchb_test()    -> test_opcode(?TEST_FETCHB).
fetch_test()     -> test_opcode(?TEST_FETCH).
storep_test()    -> test_opcode(?TEST_STOREP).
storeplus_test() -> test_opcode(?TEST_STORE_PLUS).
storeb_test()    -> test_opcode(?TEST_STOREB).
store_test()     -> test_opcode(?TEST_STORE).
multiply_test()  -> test_opcode(?TEST_MULTIPLY).
shl_test()       -> test_opcode(?TEST_SHL).
shr_test()       -> test_opcode(?TEST_SHR).
not_test()       -> test_opcode(?TEST_NOT).
plus_test()      -> test_opcode(?TEST_PLUS).
and_test()       -> test_opcode(?TEST_AND).
or_test()        -> test_opcode(?TEST_OR).
drop_test()      -> test_opcode(?TEST_DROP).
dup_test()       -> test_opcode(?TEST_DUP).
pop_test()       -> test_opcode(?TEST_POP).
over_test()      -> test_opcode(?TEST_OVER).
a_test()         -> test_opcode(?TEST_A).
nop_test()       -> test_opcode(?TEST_NOP).
push_test()      -> test_opcode(?TEST_PUSH).
bstore_test()    -> test_opcode(?TEST_BSTORE).
astore_test()    -> test_opcode(?TEST_ASTORE).

test_opcode([]) ->
   ok;

test_opcode([{OpCode,Initial,Final} | T]) ->
   test_opcode(OpCode,Initial,Final),
   test_opcode(T).

test_opcode(OpCode,Initial,Final) ->
   CPU    = test_cpu(),
   I      = test_init(CPU,Initial),
   F      = test_init(CPU,Final),
   {ok,X} = exec_impl(OpCode,I), 
   test_verify(F,X).

test_cpu() ->
   random:seed(now()),
   #cpu{ a  = ?RND,
         b  = ?RND,
         t  = ?RND,
         s  = ?RND,
         ds = {?RND(7),array:from_list([?RND,?RND,?RND,?RND,?RND,?RND,?RND,?RND])},
         rs = {?RND(7),array:from_list([?RND,?RND,?RND,?RND,?RND,?RND,?RND,?RND])}
       }.

test_init(CPU,[])             -> CPU;
test_init(CPU,[{p,X}     |T]) -> test_init(CPU#cpu{p=X},T);
test_init(CPU,[{carry,X} |T]) -> test_init(CPU#cpu{carry=X},T);
test_init(CPU,[{r,X}     |T]) -> test_init(CPU#cpu{r=X},T);
test_init(CPU,[{a,X}     |T]) -> test_init(CPU#cpu{a=X},T);
test_init(CPU,[{b,X}     |T]) -> test_init(CPU#cpu{b=X},T);
test_init(CPU,[{t,X}     |T]) -> test_init(CPU#cpu{t=X},T);
test_init(CPU,[{s,X}     |T]) -> test_init(CPU#cpu{s=X},T);
test_init(CPU,[{i,X}     |T]) -> test_init(CPU#cpu{i=X},T);
test_init(CPU,[{im,X}    |T]) -> test_init(CPU#cpu{im=X},T);
test_init(CPU,[{ds,X,Y}  |T]) -> test_init(CPU#cpu{ds={X,array:from_list(Y)}},T);
test_init(CPU,[{rs,X,Y}  |T]) -> test_init(CPU#cpu{rs={X,array:from_list(Y)}},T);
test_init(CPU,[{ram,A,W} |T]) -> test_init(CPU#cpu{ram=array:set(A,W,CPU#cpu.ram)},T);
test_init(CPU,[{rom,A,W} |T]) -> test_init(CPU#cpu{rom=array:set(A,W,CPU#cpu.rom)},T).

test_verify(Expected,Actual) ->
%  ?debugFmt("EXPECTED: ~p",[Expected]),
%  ?debugFmt("ACTUAL:   ~p",[Actual]),
   ?assertEqual(Expected,Actual).

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

assert([{rs,{SP,Stack}}|T],CPU) ->
   ?assertEqual({SP,array:from_list(Stack)},CPU#cpu.rs),
   assert(T,CPU);

assert([{ds,{SP,Stack}}|T],CPU) ->
   ?assertEqual({SP,array:from_list(Stack)},CPU#cpu.ds),
   assert(T,CPU);

assert([{ram,Addr,Word}|T],CPU) ->
   ?assertEqual(Word,array:get(Addr,CPU#cpu.ram)),
   assert(T,CPU);

assert([{rom,Addr,Word}|T],CPU) ->
   ?assertEqual(Word,array:get(Addr,CPU#cpu.rom)),
   assert(T,CPU);

assert([X|T],CPU) ->
   ?debugFmt("*** WARNING: UNIMPLEMENTED ASSERT (~p)",[X]),
   assert(T,CPU).


