-module(f18A_cucumber).

% EXPORTS

-export([step/2]).

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

% CUCUMBER

step(given,Condition) ->
   given(re:run(Condition,"^Node ([0-9]{3}) is initialised from (.*)$",[{capture,all_but_first,list}]));

step('and',"Node 406 is reset") ->
    trace:trace(scenario2,n406_reset);

step('and',"Node 406 is stepped 5 times") ->
    trace:trace(scenario2,n406_step);

step(then,"Trace should match N406.trace") ->
    trace:trace(scenario2,n406_verify).

% INTERNAL

given({match,[Node,File]}) ->
    trace:trace(scenario2,n406_initialise).


% EUNIT TESTS

n406_test() ->
   log:info(?TAG,"N406 TEST"),
   trace:stop (),
   trace:start(),
   cucumber:run(f18A_cucumber,{strings,?FEATURE}),

   Trace = trace:stop(),
   T2    = trace:extract(Trace,scenario2),

   ?assertEqual([n406_initialise,n406_reset,n406_step,n406_verify],T2).

