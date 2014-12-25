-module(f18A).

% EXPORTS

-export([create/4,create/5]).
-export([reset/1]).
-export([go/1,go/2]).
-export([stop/1,stop/2]).
-export([step/1,step/2]).
-export([breakpoint/2]).
-export([peek/2]).

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
    create(ID,
           Channels,
           ROM,
           RAM,
           yes).

create(ID,{Left,Right,Up,Down},ROM,RAM,Log) ->
   start(ID,#cpu{ id      = ID,
                  channel = #channels{left=Left, right=Right,up=Up,down=Down},
                  rom     = ROM,
                  ram     = RAM,
                  io      = [],
                  p       = 16#0a9,
                  a       = 0,
                  b       = 16#100,
                  i       = [],
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
         PID ! step,
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

      {breakpoint,Address} ->
         Breakpoints = [ Address|CPU#cpu.breakpoints],          
         loop({run,CPU#cpu{ breakpoints = Breakpoints
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
         go_impl(CPUX);

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
           { breakpoint,CPU#cpu{ p = P + 1,
                                 i = I
                               }};

        {{ok,I},_} ->
           exec(CPU#cpu{ p = P + 1,
                         i = I
                       });
        {eof,_} ->
            eof
   end;

exec(CPU,[H|T]) ->
   case exec_impl(H,CPU#cpu{ i=T }) of
   	{ok,CPUX} ->
   	    trace(H,CPUX,CPU#cpu.log),
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

% 16#02  name; jump
exec_impl({?JUMP,Addr,Mask},CPU) ->
   P = CPU#cpu.p,
   {ok,CPU#cpu{ p = ((P band Mask) bor Addr)
              }}; 


% 16#03  name  call
exec_impl({?CALL,Addr,Mask},CPU) ->
   P    = CPU#cpu.p,
   CPUX = push(rs,CPU),
   {ok,CPUX#cpu{ p = ((P band Mask) bor Addr),
                 r = P,
                 i = [] 
	       }}; 

% 16#08  @p  fetch P
exec_impl(?FETCHP,CPU) ->
   P    = CPU#cpu.p,     
   CPUX = push(ds,CPU),
   case read(CPUX,P) of
        {ok,T} ->
   	    {ok,CPUX#cpu{ p = P + 1,
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

% 16#0e  !b  store B
exec_impl(?STOREB,CPU) ->
   B = CPU#cpu.b,     
   T = CPU#cpu.t,
   case write(CPU,B,T) of 
        {ok,RAM} ->
            {ok,pop(ds,CPU#cpu{ ram = RAM },CPU#cpu.s)};

        Other ->
            Other
       end;


% 16#0f  !  store
exec_impl(?STORE,CPU) ->
   A = CPU#cpu.a,     
   T = CPU#cpu.t,
   case write(CPU,A,T) of 
        {ok,RAM} ->
            {ok,pop(ds,CPU#cpu{ ram = RAM },CPU#cpu.s)};

        Other ->
            Other
       end;

% 16#11  2*   shl
exec_impl(?SHL,CPU) ->
   T = CPU#cpu.t band 16#3ffff,   
   {ok,CPU#cpu{t = ((T bsl 1) band 16#3ffff)
              }};


% 16#14  +   plus
exec_impl(?PLUS,CPU) ->
   T  = CPU#cpu.t band 16#3ffff,   
   S  = CPU#cpu.s band 16#3ffff,
   C  = CPU#cpu.carry,
   R  = case (CPU#cpu.p band 16#0200) of
 	     16#0200 ->
	 	 (S + T + C) band 16#3ffff;
 
             _else ->
                 (S + T) band 16#3ffff
             end,

   {ok,pop(ds,CPU,R)};

% 16#18  dup
exec_impl(?DUP,CPU) ->
   {ok,push(ds,CPU)};

% 16#1c  .   nop
exec_impl(?NOP,CPU) ->
   {ok,CPU};

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

decode(I0,Word) ->
   W            = Word bxor 16#15555,
   <<S1:5,_:8>> = <<W:13>>,
   decode(I0,opcode:opcode(S1),Word).

decode(I0,?JUMP,Word) ->
   [I0,{?JUMP,Word band 16#0ff,16#300}];

decode(I0,?CALL,Word) ->
   [I0,{?CALL,Word band 16#0ff,16#300}];

decode(I0,I1,Word) ->
   W            = Word bxor 16#15555,
   <<S2:5,_:3>> = <<W:8>>,
   decode(I0,I1,opcode:opcode(S2),Word).

decode(I0,I1,?JUMP,Word) ->
   [I0,I1,{?JUMP,Word band 16#007,16#3f8}];

decode(I0,I1,?CALL,Word) ->
   [I0,I1,{?CALL,Word band 16#007,16#3f8}];

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

write_mem(Mem,Addr,Word) ->
   write_mem(Mem,Addr,Word,array:size(Mem)).

% TODO - FIX ARRAY SIZE AT 64
write_mem(Mem,Addr,Word,N) when Addr < N ->
   { ok,array:set(Addr,Word,Mem) };

write_mem(_Mem,_Addr,_Word,_N) ->
   eof.

write_channel(CPU,Ch,Word) ->
   write_channel(CPU,Ch,Word,util:is_registered(Ch)).

write_channel(CPU,Ch,Word,_) ->
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
   receive
      { Channel,read,ok } -> 
         {ok,CPU#cpu.ram};

      step ->
         write_wait(CPU,Channel);

      {stop,PID} ->
         {stop,PID}
   end.

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
trace(_,_,no) ->
   ok;

trace({?JUMP,_,_},CPU,_) ->
   log:debug  (?TAG,io_lib:format("~s ~p",[opcode:to_string(?JUMP),CPU#cpu.p])),
   trace:trace(f18A,?JUMP,CPU);

trace({?CALL,_,_},CPU,_) ->
   log:debug  (?TAG,io_lib:format("~s ~p",[opcode:to_string(?CALL),CPU#cpu.p])),
   trace:trace(f18A,?CALL,CPU);

trace(OpCode,CPU,_) ->
   log:debug  (?TAG,opcode:to_string(OpCode)),     
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

pop_ds_test() ->
   Stack = array:from_list([1,2,3,4,5,6,7,8]),
   assert([{t,0},{s,1},{ds,{1,[1,2,3,4,5,6,7,8]}}],pop(ds,#cpu{t=16#3ffff,s=0,ds={0,Stack}},0)),
   assert([{t,0},{s,2},{ds,{2,[1,2,3,4,5,6,7,8]}}],pop(ds,#cpu{t=16#3ffff,s=0,ds={1,Stack}},0)),
   assert([{t,0},{s,3},{ds,{3,[1,2,3,4,5,6,7,8]}}],pop(ds,#cpu{t=16#3ffff,s=0,ds={2,Stack}},0)),
   assert([{t,0},{s,4},{ds,{4,[1,2,3,4,5,6,7,8]}}],pop(ds,#cpu{t=16#3ffff,s=0,ds={3,Stack}},0)),
   assert([{t,0},{s,5},{ds,{5,[1,2,3,4,5,6,7,8]}}],pop(ds,#cpu{t=16#3ffff,s=0,ds={4,Stack}},0)),
   assert([{t,0},{s,6},{ds,{6,[1,2,3,4,5,6,7,8]}}],pop(ds,#cpu{t=16#3ffff,s=0,ds={5,Stack}},0)),
   assert([{t,0},{s,7},{ds,{7,[1,2,3,4,5,6,7,8]}}],pop(ds,#cpu{t=16#3ffff,s=0,ds={6,Stack}},0)),
   assert([{t,0},{s,8},{ds,{0,[1,2,3,4,5,6,7,8]}}],pop(ds,#cpu{t=16#3ffff,s=0,ds={7,Stack}},0)).

pop_rs_test() ->
   Stack = array:from_list([1,2,3,4,5,6,7,8]),
   assert([{r,1},{rs,{1,[1,2,3,4,5,6,7,8]}}],pop(rs,#cpu{r=0,rs={0,Stack}})),
   assert([{r,2},{rs,{2,[1,2,3,4,5,6,7,8]}}],pop(rs,#cpu{r=0,rs={1,Stack}})),
   assert([{r,3},{rs,{3,[1,2,3,4,5,6,7,8]}}],pop(rs,#cpu{r=0,rs={2,Stack}})),
   assert([{r,4},{rs,{4,[1,2,3,4,5,6,7,8]}}],pop(rs,#cpu{r=0,rs={3,Stack}})),
   assert([{r,5},{rs,{5,[1,2,3,4,5,6,7,8]}}],pop(rs,#cpu{r=0,rs={4,Stack}})),
   assert([{r,6},{rs,{6,[1,2,3,4,5,6,7,8]}}],pop(rs,#cpu{r=0,rs={5,Stack}})),
   assert([{r,7},{rs,{7,[1,2,3,4,5,6,7,8]}}],pop(rs,#cpu{r=0,rs={6,Stack}})),
   assert([{r,8},{rs,{0,[1,2,3,4,5,6,7,8]}}],pop(rs,#cpu{r=0,rs={7,Stack}})).

ret_test() ->
   P  = 1,
   R  = 2,
   RS = {0,array:from_list([3,4,5,6,7,8,9,10])},
   I  = [ ?NOP,?NOP,?NOP,?NOP ],
   {ok,CPU} = exec_impl(?RET,#cpu{p=P,r=R,rs=RS,i=I}),
   assert([{p,R},{r,3},{rs,{1,[3,4,5,6,7,8,9,10]}},{i,[]}],CPU).

jump_test() ->
   P = 16#0a9,
   {ok,CPU} = exec_impl({?JUMP,16#03,16#0000},#cpu{p=P}),
   assert([{p,16#03}],CPU).

call_test() ->
   P   = 16#0a9,
   R   = 16#000,
   RS  = {0,array:from_list([1,2,3,4,5,6,7,8])},
   RAM = array:from_list([16#2c9b2,16#2c9b2,16#2c9b2,16#2c9b2,16#2c9b2,16#2c9b2]),
   I   = [ ?RET,?RET,?RET,?RET ],
   {ok,CPU} = exec_impl({?CALL,16#03,16#0000},#cpu{p=P,r=R,rs=RS,i=I,ram=RAM}),
   assert([{p,16#03},{r,16#0a9},{rs,{7,[1,2,3,4,5,6,7,0]}},{i,[]}],CPU).

storeb_test() ->
   S   = 9,
   T   = 678,
   B   = 16#004,
   RAM = array:new(64,[{default,0}]),
   DS  = {0,array:from_list([1,2,3,4,5,6,7,8])},
   {ok,CPU} = exec_impl(?STOREB,#cpu{b=B,
                                     t=T,
                                     s=S,
                                     ds=DS,
                                     ram=RAM}),
   assert([{ram,4,678},{t,S},{s,1},{ds,{1,[1,2,3,4,5,6,7,8]}}],CPU).

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
   DS  = {0,array:from_list([3,4,5,6,7,8,9,10])},
   {ok,CPU} = exec_impl(?PLUS,#cpu{ p=P,
                                    t=T,
                                    s=S,
                                    ds=DS,
                                    carry=C }),
   assert([{t,R},{s,3},{ds,{1,[3,4,5,6,7,8,9,10]}}],CPU).


-define(TEST_FETCHP,[{?FETCHP,
                     [{ram,15,678},{p,15},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                     [{ram,15,678},{p,16},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]}
                   ]).

-define(TEST_FETCHB,[{?FETCHB,
                     [{ram,15,678},{b,15},{t,1},  {s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                     [{ram,15,678},{b,15},{t,678},{s,1},{ds,7,[3,4,5,6,7,8,9,2]}]}
                   ]).

-define(TEST_STORE,[{?STORE,
                     [{ram,0,0},{a,0},{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                     [{ram,0,1},{a,0},{t,2},{s,3},{ds,1,[3,4,5,6,7,8,9,10]}]}
                   ]).

-define(TEST_SHL,[ {?SHL,[{t,16#00001}],[{t,16#00002}]},
                   {?SHL,[{t,16#00002}],[{t,16#00004}]},
                   {?SHL,[{t,16#00004}],[{t,16#00008}]},
                   {?SHL,[{t,16#00008}],[{t,16#00010}]},
                   {?SHL,[{t,16#10000}],[{t,16#20000}]},
                   {?SHL,[{t,16#20000}],[{t,16#00000}]}
                 ]).

-define(TEST_DUP,[ {?DUP,
                    [{t,1},{s,2},{ds,0,[3,4,5,6,7,8,9,10]}],
                    [{t,1},{s,1},{ds,7,[3,4,5,6,7,8,9,2 ]}]
                   } ]).

-define(TEST_NOP,[ {?NOP,
                    [],
                    []
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

fetchp_test() -> test_opcode(?TEST_FETCHP).
fetchb_test() -> test_opcode(?TEST_FETCHB).
store_test()  -> test_opcode(?TEST_STORE).
shl_test()    -> test_opcode(?TEST_SHL).
dup_test()    -> test_opcode(?TEST_DUP).
nop_test()    -> test_opcode(?TEST_NOP).
bstore_test() -> test_opcode(?TEST_BSTORE).
astore_test() -> test_opcode(?TEST_ASTORE).

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
         ds = {?RND(8),[?RND,?RND,?RND,?RND,?RND,?RND,?RND,?RND]}
       }.

test_init(CPU,[])            -> CPU;
test_init(CPU,[{p,X}    |T]) -> test_init(CPU#cpu{p=X},T);
test_init(CPU,[{a,X}    |T]) -> test_init(CPU#cpu{a=X},T);
test_init(CPU,[{b,X}    |T]) -> test_init(CPU#cpu{b=X},T);
test_init(CPU,[{t,X}    |T]) -> test_init(CPU#cpu{t=X},T);
test_init(CPU,[{s,X}    |T]) -> test_init(CPU#cpu{s=X},T);
test_init(CPU,[{ds,X,Y} |T]) -> test_init(CPU#cpu{ds={X,array:from_list(Y)}},T);
test_init(CPU,[{ram,A,W}|T]) -> test_init(CPU#cpu{ram=array:set(A,W,CPU#cpu.ram)},T).

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

assert([X|T],CPU) ->
   ?debugFmt("*** WARNING: UNIMPLEMENTED ASSERT (~p)",[X]),
   assert(T,CPU).


