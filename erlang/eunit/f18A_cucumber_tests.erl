-module(f18A_cucumber_tests).

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
                  "     And  Node 404 is stepped 32 times",
                  "    Then  Node XXX should have received 6,8"
                ]).

% EUNIT TESTS

feature_test() ->
   log:info(?TAG,"N404 FEATURE TEST"),
   trace:stop (),
   trace:start(),
   cucumber:run(f18A_cucumber,{strings,?FEATURE}),

   Trace = trace:stop(),
   T2    = trace:extract(Trace,scenario),

   ?assertEqual([initialise,reset,step,verify],T2).

file_test() ->
   log:info(?TAG,"N404 FILE TEST"),
   trace:stop (),
   trace:start(),
   cucumber:run(f18A_cucumber,{file,?HCCFORTH}),

   Trace = trace:stop(),
   T2    = trace:extract(Trace,scenario),

   ?assertEqual([initialise,reset,step,verify],T2).

