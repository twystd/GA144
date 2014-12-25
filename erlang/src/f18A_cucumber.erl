-module(f18A_cucumber).

% EXPORTS

-export([setup/0,teardown/1,step/3]).

% EXPORTS for erlang:apply(...)

-export([initialise/3,get/2,put/3,listened/2,peek/4,reset/2,stepping/3,verify/1]).

% INCLUDES

-include    ("include/f18A.hrl").
-include_lib("eunit/include/eunit.hrl").

% DEFINES

-define(TAG,"F18A").
-define(STEPS,[ {given,"^Node ([0-9]{3}) is initialised from (.*)$",         initialise },
                {'and',"Node XXX listening on (RIGHT|LEFT|UP|DOWN)",         get        },
                {'and',"Node XXX writes \\[(.*?)\\] to (RIGHT|LEFT|UP|DOWN)",put        },
                {'and',"Node ([0-9]{3}) is reset",                           reset      },
                {'and',"Node ([0-9]{3}) is stepped ([0-9]+) (?:time|times)", stepping   },
                {then, "Node XXX should have received \\[(.*?)\\]",          listened   },
                {then, "Node ([0-9]{3}) (T|S) should be ([0-9]+)",           peek       },
                {then, "Node ([0-9]{3}) (DS) should be \\[(.*?)\\]",         peek       }
              ]).

% RECORDS
%
-record(context,{ node
                }).
% CUCUMBER

setup() ->
%   trace:start(),
    #context{ 
            }.

teardown(Context) ->
    teardown(node,Context#context.node),
%   ?debugFmt("** TRACE: ~p",[trace:stop()]),
    ok.

teardown(node,undefined) ->
   ok;

teardown(node,Node) ->
   f18A:stop(Node). 


step(Context,Type,Condition) ->
    F = fun({T,Step,Function},L) ->
           case {T,re:run(Condition,Step,[{capture,all_but_first,list}])} of
               {Type,{match,Args}} -> 
                   [{Function,Args} | L ];
                _else ->
                   L
           end
        end,

    case lists:foldl(F,[],?STEPS) of
         [] ->
            throw({error,string:join(["No matching step implementation for '", Condition,"'"],"")});

         Steps ->
            exec(Context,Steps)
    end.

exec(Context,[]) ->
    Context;

exec(Context,[{Function,Args} | T ]) ->
    exec(apply(f18A_cucumber,Function,[Context | Args]),T).

% INTERNAL

initialise(Context,Node,File) ->
    trace:trace(scenario,initialise),
    NodeID   = nodeid(Node),
    RAM      = util:read_ram(File),     
    ROM      = util:read_rom(File),     
    F18A     = f18A:create(NodeID,{left,right,up,down},ROM,RAM,no),
    Context#context{ node = F18A
                   }.

get(Context,Port) ->
   Dest = list_to_atom(string:to_lower(Port)),
   M    = self(),
   util:unregister(Dest),
   register(Dest,spawn(fun() ->
                          L = read(Dest),
                          M ! {rx,L}
                       end)),

   Context.

put(Context,List,Port) ->
   Src  = list_to_atom(string:to_lower(Port)),
   Dest = Context#context.node,
   Data = [ list_to_integer(X) || X <- string:tokens(List,",")],
   M    = self(),

   util:unregister(Src),
   register(Src,spawn(fun() ->
                          L = write(Src,Dest,Data),
                          M ! {rx,L}
                      end)),

   Context.

listened(Context,List) ->
    Expected = [ list_to_integer(X) || X <- string:tokens(List,",")],
    trace:trace(scenario,verify),
    stop(left),
    stop(right),
    stop(up),
    stop(down),
    compare(Expected,receive {rx,L} -> L end),
    Context.

peek(Context,_Node,"T",Word) ->
    E = list_to_integer(Word),
    T = f18A:peek(Context#context.node,t),
    ?assertEqual(E,T),
    Context;

peek(Context,_Node,"S",Word) ->
    E = list_to_integer(Word),
    S = f18A:peek(Context#context.node,s),
    ?assertEqual(E,S),
    Context;

peek(Context,_Node,"DS",List) ->
    Expected = [ list_to_integer(X) || X <- string:tokens(List,",")],
    {I,DS}   = f18A:peek(Context#context.node,ds),
    DSX      = rotate(array:to_list(DS),I),
    compare(Expected,DSX),
    Context.

verify(Context) ->
    trace:trace(scenario,verify),
    Context.

reset(Context,_Node) ->
    trace:trace(scenario,reset),
    f18A:reset(Context#context.node),
    Context.

stepping(Context,Node,Count) ->
    N = list_to_integer(Count),
    trace:trace(scenario,step),
    F18A = Context#context.node,
    stepping(f18A,F18A,Node,N),
    Context.

stepping(f18A,_F18A,_,0) ->
   ok;

stepping(f18A,F18A,_Node,N) ->
   f18A:step(F18A,wait),
   stepping(f18A,F18A,_Node,N-1).

read(Dest) ->
   read(Dest,[]).

read(Dest,L) ->
   receive
      {F18A,write,X} ->
         F18A ! { Dest,read,ok },
         read(Dest,[X|L]);

      _else ->
         lists:reverse(L)
   end.

write(_Src,_Node,[]) ->
   ok;

write(Src,Dest,[Word|T]) ->
   Dest ! {Src,write,Word},
   receive
      {_Node,read,ok} ->
         write(Src,Dest,T);
      
      _else ->
         ok
   end.
   

% UTILITY

nodeid(Node) ->
    list_to_atom(string:concat("n",Node)).

rotate(L, 0) -> L;
rotate([],_) -> [];
rotate(L, N) -> {H,T} = lists:split(N,L), lists:append(T,H).

compare(Expected,Expected) ->
    ok;

compare(Expected,Actual) ->
    throw({compare,{expected,Expected},{actual,Actual}}).
    
stop(PID) ->
   stop(PID,util:is_registered(PID)).

stop(PID,true) ->
   PID ! stop;

stop(_,_) ->
   ok.

