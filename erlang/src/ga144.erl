-module(ga144).

% EXPORTS

-export([init/1,reset/1,step/1,step/2]).


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
   Node = f18A:create(nodeid(ID),
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
   step_nodes(GA144,GA144#ga144.nodes),
   step(GA144,N-1,Step+1).

step_nodes(_GA144,[]) ->
   ok;

step_nodes(GA144,[F18A|T]) ->
   f18A:step(F18A),
   step_nodes(GA144,T).

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

hccforth_test() ->
   GA144 = init([{404,"../cucumber/404.bin"},
                 {405,"../cucumber/405.bin"},
                 {406,"../cucumber/406.bin"},
                 {505,"../cucumber/505.bin"}
                ]),
   reset(GA144),
   step (GA144,50),
   ok.

