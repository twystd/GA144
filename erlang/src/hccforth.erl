-module(hccforth).

% EXPORTS

-export([step/0,go/0]).


% INCLUDES

-include("include/f18A.hrl").

% RECORDS

% API

step() ->
    M = self(),
    L = spawn(fun() -> peek(M,undefined) end),
    P = fun(CPU) ->
             T      = CPU#cpu.t,  
             S      = CPU#cpu.s, 
             {I,DS} = CPU#cpu.ds,
             DSX    = rotate(array:to_list(DS),I),
             L ! {peek,lists:append([T,S],DSX)}
       end,

   GA144 = ga144:init([{404,"../cucumber/404.bin"},
                       {405,"../cucumber/405.bin"},
                       {406,"../cucumber/406.bin"},
                       {505,"../cucumber/505.bin"}
                      ]),

   ga144:probe(GA144,505,P),
   ga144:reset(GA144),
   ga144:step (GA144,97),

   L ! stop,
   receive 
        {peek,X} -> X 
   end. 

go() ->
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

   GA144 = ga144:init([{404,"../cucumber/404.bin"},
                       {405,"../cucumber/405.bin"},
                       {406,"../cucumber/406.bin"},
                       {505,"../cucumber/505.bin"}
                      ]),

   ga144:probe(GA144,505,P),
   ga144:reset(GA144),
   ga144:go   (GA144),

   receive
       break ->
           ga144:break(GA144),
           timer:sleep(100),
           ok

       after 500 ->
             timeout
       end,

   ga144:stop(GA144),

   L ! stop,
   receive 
      {peek,V} -> 
            V

      after 100 ->
            none     
      end. 

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

