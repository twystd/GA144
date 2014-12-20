-module(f18A_cucumber).

% EXPORTS

-export([setup/0,teardown/1,step/3]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% DEFINES

-define(TAG,"F18A").
-define(HCCFORTH,"../cucumber/hccforth.feature").

-define(FEATURE,[ "Feature: hcc!forth tutorial - node 404",
                  "         Runs the code for node 404 from the hcc!forth colorforth tutorial",
                  "",
                  "Scenario: N404", 
                  "   Given  Node 404 is initialised from ../cucumber/N404.bin",
                  "     And  Node XXX listening on RIGHT",
                  "     And  Node 404 is reset",
                  "     And  Node 404 is stepped 19 times",
                  "    Then  Trace should match N404.trace",
                  "     And  Node XXX should have received [6,8]"
                ]).

-record(context,{ node
                }).
% CUCUMBER

setup() ->
    #context{ 
            }.

teardown(Context) ->
    f18A:stop(Context#context.node), 
    ok.

step(Context,given,Condition) ->
    initialise(Context,re:run(Condition,"^Node ([0-9]{3}) is initialised from (.*)$",[{capture,all_but_first,list}]));

step(Context,'and',"Node XXX listening on RIGHT") ->
    listen(Context);

step(Context,'and',"Node 404 is reset") ->
    reset(Context);

step(Context,'and',"Node 404 is stepped 19 times") ->
    step_impl(Context,32);

step(Context,then,"Trace should match N404.trace") ->
    verify(Context);

step(Context,'and',"Node XXX should have received [6,8]") ->
    nxxx ! stop,
    ?assertEqual([6,8],receive {rx,L} -> L end),
    Context.


% INTERNAL

initialise(Context,{match,[Node,File]}) ->
    trace:trace(scenario,initialise),
    NodeID = nodeid(Node),
    RAM    = util:read_ram(File),     
    ROM    = util:read_rom(File),     
    F18A   = f18A:create(NodeID,nxxx,ROM,RAM),
    Context#context{ node = F18A }.

listen(Context) ->
    M = self(),
    util:unregister(nxxx),
    register(nxxx,spawn(fun() ->
                           L = read(),
                           M ! {rx,L}
                        end)),

    Context.

verify(Context) ->
    trace:trace(scenario,verify),
    Context.

reset(Context) ->
    trace:trace(scenario,reset),
    f18A:reset(Context#context.node),
    Context.

step_impl(Context,N) ->
    trace:trace(scenario,step),
    F18A = Context#context.node,
    step_impl(f18A,F18A,N),
    Context.

step_impl(f18A,_F18A,0) ->
   ok;

step_impl(f18A,F18A,N) ->
   f18A:step(F18A,wait),
   step_impl(f18A,F18A,N-1).

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

% EUNIT TESTS

n404_feature_test() ->
   log:info(?TAG,"N404 FEATURE TEST"),
   trace:stop (),
   trace:start(),
   cucumber:run(f18A_cucumber,{strings,?FEATURE}),

   Trace = trace:stop(),
   T2    = trace:extract(Trace,scenario),

   ?assertEqual([initialise,reset,step,verify],T2).

n404_file_test() ->
   log:info(?TAG,"N404 FILE TEST"),
   trace:stop (),
   trace:start(),
   cucumber:run(f18A_cucumber,{file,?HCCFORTH}),

   Trace = trace:stop(),
   T2    = trace:extract(Trace,scenario),

   ?assertEqual([initialise,reset,step,verify],T2).

