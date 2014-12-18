-module(f18A_cucumber).

% EXPORTS

-export([setup/0,teardown/1,step/3]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% DEFINES

-define(TAG,"F18A").
-define(FEATURE,[ "Feature: hcc!forth tutorial - node 406",
                  "         Runs the code for node 406 from the hcc!forth colorforth tutorial",
                  "",
                  "Scenario: N406", 
                  "   Given  Node 406 is initialised from ../cucumber/N406.bin",
                  "     And  Node 406 is reset",
                  "     And  Node 406 is stepped 5 times",
                  "    Then  Trace should match N406.trace"
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

step(Context,'and',"Node 406 is reset") ->
    reset(Context);

step(Context,'and',"Node 406 is stepped 5 times") ->
    step5(Context);

step(Context,then,"Trace should match N406.trace") ->
    verify(Context).

% INTERNAL

initialise(Context,{match,[_Node,_File]}) ->
    trace:trace(scenario2,n406_initialise),
    RAM  = util:read_ram("../cucumber/N404.bin"),     
    ROM  = util:read_rom("../cucumber/N404.bin"),     
    F18A = f18A:create(n406,n000,ROM,RAM),
    Context#context{ node = F18A }.

reset(Context) ->
    trace:trace(scenario2,n406_reset),
    f18A:reset(Context#context.node),
    Context.

step5(Context) ->
    trace:trace(scenario2,n406_step),
    F18A = Context#context.node,
    f18A:step(F18A,wait),
    f18A:step(F18A,wait),
    f18A:step(F18A,wait),
    f18A:step(F18A,wait),
    f18A:step(F18A,wait),
    Context.

verify(Context) ->
    trace:trace(scenario2,n406_verify),
    Context.

% EUNIT TESTS

n404_test() ->
   log:info(?TAG,"N404 TEST"),
   trace:stop (),
   trace:start(),
   cucumber:run(f18A_cucumber,{strings,?FEATURE}),

   Trace = trace:stop(),
   T     = trace:extract(Trace,f18A,n406),
   T2    = trace:extract(Trace,scenario2),

   ?debugFmt("TRACE: ~p",[T]),
   ?assertEqual([n406_initialise,n406_reset,n406_step,n406_verify],T2).

