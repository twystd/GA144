-module(ga144).

% EXPORTS

-export([init/1,reset/1,go/1,stop/1,break/1,step/1,step/2]).
-export([probe/3]).


% INCLUDES

-include    ("include/f18A.hrl").
-include    ("include/opcode.hrl").
-include_lib("eunit/include/eunit.hrl").

% RECORDS

-record(ga144,{ nodes=[]
              }).

% API

init(Nodes) ->
   init(#ga144{},Nodes).

init(GA144,[]) ->
   GA144;

init(GA144,[{ID,BinFile}|T]) ->
   Node = f18A:create(self(),
                      nodeid(ID),
                      {left(ID),right(ID),up(ID),down(ID)},
                      util:read_rom(BinFile),     
                      util:read_ram(BinFile)),

   init(GA144#ga144{ nodes = [ Node | GA144#ga144.nodes ]
                   }, T).


reset(GA144) ->
   reset(GA144,GA144#ga144.nodes).

reset(_GA144,[]) ->
   ok;

reset(GA144,[F18A|T]) ->
   f18A:reset(F18A),
   reset(GA144,T).

step(GA144) ->
   step(GA144,1).

step(GA144,N) ->
   step(GA144,N,1).

step(_GA144,0,_) ->
   ok;

step(GA144,N,Step) ->
   ?debugFmt("--- STEP ~p",[Step]),
   lists:foreach(fun(F18A) -> 
                       f18A:step(F18A,self()) 
                 end,GA144#ga144.nodes),
   step_wait(GA144#ga144.nodes),
   step     (GA144,N-1,Step+1).

step_wait([]) ->
   ok;

step_wait(L) ->
   receive
      {Node,step} ->
         step_wait(lists:delete(Node,L));

      {Node,reading} ->
         step_wait(lists:delete(Node,L));

      {Node,writing} ->
         step_wait(lists:delete(Node,L))

   after 1000 ->
         ?debugFmt("TIMEOUT: ~p",[L]),
         ok
   end.

go(GA144) ->
   F = fun(F18A) -> f18A:go  (F18A)      end,
   lists:foreach(F,GA144#ga144.nodes).

stop(GA144) ->
   F = fun(F18A) -> f18A:stop(F18A,wait) end,
   lists:foreach(F,GA144#ga144.nodes).

break(GA144) ->
   lists:foreach(fun(F18A) -> f18A:break(F18A) end,
                 GA144#ga144.nodes).

probe(GA144,Node,Probe) ->
   lists:foreach(fun(F18A) -> probe_impl(F18A,nodeid(Node),Probe) end,
                 GA144#ga144.nodes).

probe_impl(F18A,F18A,Probe) ->
   f18A:probe(F18A,Probe);

probe_impl(_,_,_) ->
   ok.

% UTILITY

nodeid(ID) ->
   list_to_atom(string:concat("n",integer_to_list(ID))).

left(ID) when ID rem 2 =:= 0 -> nodeid(ID-1);
left(ID) -> nodeid(ID+1).

right(ID) when ID rem 2 =:= 0 -> nodeid(ID+1);
right(ID) -> nodeid(ID-1).

up(ID) when (ID div 100) rem 2 =:= 0 -> nodeid(ID-100);
up(ID) -> nodeid(ID+100).

down(ID) when (ID div 100) rem 2 =:= 0 -> nodeid(ID+100);
down(ID) -> nodeid(ID-100).


% EUNIT

hccforth_step_test() ->
    M = self(),
    L = spawn(fun() -> peek(M,undefined) end),
    P = fun(CPU) ->
             T      = CPU#cpu.t,  
             S      = CPU#cpu.s, 
             {I,DS} = CPU#cpu.ds,
             DSX    = rotate(array:to_list(DS),I),
             L ! {peek,lists:append([T,S],DSX)}
       end,

   GA144 = init([{404,"../cucumber/404.bin"},
                 {405,"../cucumber/405.bin"},
                 {406,"../cucumber/406.bin"},
                 {505,"../cucumber/505.bin"}
                ]),

   probe(GA144,505,P),
   reset(GA144),
   step (GA144,97),

   L ! stop,
   R = receive 
           {peek,X} -> X 
       end, 
   ?debugMsg("--OK"),
   ?assertEqual([41,36,31,26,21,0,0,0,0,0],R),
   ok.

hccforth_go_test() ->
    M = self(),
    L = spawn(fun() -> peek(M,undefined) end),
    P = fun(CPU) ->
             T      = CPU#cpu.t,  
             S      = CPU#cpu.s, 
             {I,DS} = CPU#cpu.ds,
             DSX    = rotate(array:to_list(DS),I),
             L ! {peek,lists:append([T,S],DSX)},
             
             case T of 
                 41 ->
                     M ! break;

                 _else ->
                     ok
             end
       end,

   GA144 = init([{404,"../cucumber/404.bin"},
                 {405,"../cucumber/405.bin"},
                 {406,"../cucumber/406.bin"},
                 {505,"../cucumber/505.bin"}
                ]),

   probe(GA144,505,P),
   reset(GA144),
   go   (GA144),

   X = receive
           break ->
               break(GA144),
               timer:sleep(100),
               ok

        after 500 ->
             timeout
        end,

   stop(GA144),

   L ! stop,
   R = receive 
           {peek,V} -> 
               V

       after 100 ->
            none     
       end, 

   ?assertEqual(ok,X),
   ?assertEqual([41,36,31,26,21,0,0,0,0,0],R),
   ?debugMsg("--OK"),
   ok.

peek(M,X) ->
    receive 
        {peek,DS} ->
            peek(M,DS);

        stop ->
            M ! {peek,X}
    end.



rotate(L, 0) -> L;
rotate([],_) -> [];
rotate(L, N) -> {H,T} = lists:split(N,L), lists:append(T,H).

