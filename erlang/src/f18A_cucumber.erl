-module(f18A_cucumber).

% EXPORTS

-export([setup/0,teardown/1,step/3]).

% EXPORTS for erlang:apply(...)

-export([initialise/3,listen/2,listened/2,reset/2,stepping/3,verify/1]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% DEFINES

-define(TAG,"F18A").
-define(STEPS,[ {given,"^Node ([0-9]{3}) is initialised from (.*)$",initialise },
                {'and',"Node XXX listening on (RIGHT|LEFT)",        listen     },
                {'and',"Node ([0-9]{3}) is reset",                  reset      },
                {'and',"Node ([0-9]{3}) is stepped ([0-9]+) times", stepping   },
                {then, "Node XXX should have received (.*)",        listened   }
              ]).

% RECORDS
%
-record(context,{ node
                }).
% CUCUMBER

setup() ->
    #context{ 
            }.

teardown(Context) ->
    f18A:stop(Context#context.node), 
    ok.

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
    NodeID = nodeid(Node),
    RAM    = util:read_ram(File),     
    ROM    = util:read_rom(File),     
    F18A   = f18A:create(NodeID,nxxx,ROM,RAM),
    Context#context{ node = F18A }.

listen(Context,_Port) ->
    M = self(),
    util:unregister(nxxx),
    register(nxxx,spawn(fun() ->
                           L = read(),
                           M ! {rx,L}
                        end)),

    Context.

listened(Context,List) ->
    Expected = [ list_to_integer(X) || X <- string:tokens(List,",")],
    trace:trace(scenario,verify),
    nxxx ! stop,
    compare(Expected,receive {rx,L} -> L end),
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

read() ->
   read([]).

read(L) ->
   receive
      {F18A,write,X} ->
         F18A ! { nxxx,read,ok },
         read([X|L]);

      _else ->
         lists:reverse(L)
   end.

% UTILITY

nodeid(Node) ->
    list_to_atom(string:concat("n",Node)).

compare(Expected,Expected) ->
    ok;

compare(Expected,Actual) ->
    throw({compare,{expected,Expected},{actual,Actual}}).
    
