-module(cucumber_tests).

% EXPORTS

-export([step/1]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% DEFINES

-define(TAG,"CUCUMBER").
-define(FEATURE,[ "Feature: Cucumber Feature Test",
                  "         Test feature for the cucumber unit test",
                  "",
                  "Scenario: Scenario 1", 
                  "   Given  Node 404 is initialised",
                  "     And  Node 404 is reset",
                  "     And  Node 404 is stepped 5 times",
                  "    Then  Trace should match N404.trace",
                  "",
                  "Scenario: Scenario 2",
                  "   Given  Node 406 is initialised",
                  "     And  Node 406 is reset",
                  "     And  Node 406 is stepped 5 times",
                  "    Then  Trace should match N406.trace"
                ]).

% CUCUMBER

step({given,"Node 404 is initialised"}) ->
    trace:trace(scenario1,n404_initialise);

step({'and',"Node 404 is reset"}) ->
    trace:trace(scenario1,n404_reset);

step({'and',"Node 404 is stepped 5 times"}) ->
    trace:trace(scenario1,n404_step);

step({then,"Trace should match N404.trace"}) ->
    trace:trace(scenario1,n404_verify);

step({given,"Node 406 is initialised"}) ->
    trace:trace(scenario2,n406_initialise);

step({'and',"Node 406 is reset"}) ->
    trace:trace(scenario2,n406_reset);

step({'and',"Node 406 is stepped 5 times"}) ->
    trace:trace(scenario2,n406_step);

step({then,"Trace should match N406.trace"}) ->
    trace:trace(scenario2,n406_verify).

% EUNIT TESTS

feature_test() ->
   log:info(?TAG,"FEATURE TEST"),
   trace:stop (),
   trace:start(),
   cucumber:run(cucumber_tests,{strings,?FEATURE}),

   Trace = trace:stop(),
   T1    = trace:extract(Trace,scenario1),
   T2    = trace:extract(Trace,scenario2),

   ?assertEqual([n404_initialise,n404_reset,n404_step,n404_verify],T1),
   ?assertEqual([n406_initialise,n406_reset,n406_step,n406_verify],T2).

f18A_test() ->
   cucumber:run(f18A_cucumber,{file,"../cucumber/hccforth.feature"}).        




