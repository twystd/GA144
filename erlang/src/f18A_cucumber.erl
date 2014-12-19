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
                  "     And  Node 000 listening on RIGHT",
                  "     And  Node 406 is reset",
                  "     And  Node 406 is stepped 19 times",
                  "    Then  Trace should match N406.trace",
                  "     And  Node 000 should have received [6,8]"
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

step(Context,'and',"Node 000 listening on RIGHT") ->
    listen(Context);

step(Context,'and',"Node 406 is reset") ->
    reset(Context);

step(Context,'and',"Node 406 is stepped 19 times") ->
    step_impl(Context,32);

step(Context,then,"Trace should match N406.trace") ->
    verify(Context);

step(Context,'and',"Node 000 should have received [6,8]") ->
    n000 ! stop,
    ?assertEqual([6,8],receive {rx,L} -> L end),
    Context.


% INTERNAL

initialise(Context,{match,[_Node,_File]}) ->
    trace:trace(scenario2,n406_initialise),
    RAM  = util:read_ram("../cucumber/N404.bin"),     
    ROM  = util:read_rom("../cucumber/N404.bin"),     
    F18A = f18A:create(n406,n000,ROM,RAM),
    Context#context{ node = F18A }.

listen(Context) ->
    M = self(),
    util:unregister(n000),
    register(n000,spawn(fun() ->
                           L = read(),
                           M ! {rx,L}
                        end)),

    Context.

verify(Context) ->
    trace:trace(scenario2,n406_verify),
    Context.

reset(Context) ->
    trace:trace(scenario2,n406_reset),
    f18A:reset(Context#context.node),
    Context.

step_impl(Context,N) ->
    trace:trace(scenario2,n406_step),
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
         F18A ! { n000,read,ok },
         read([X|L]);

      _else ->
         lists:reverse(L)
   end.

% EUNIT TESTS

n404_test() ->
   log:info(?TAG,"N404 TEST"),
   trace:stop (),
   trace:start(),
   cucumber:run(f18A_cucumber,{strings,?FEATURE}),

   Trace = trace:stop(),
   T2    = trace:extract(Trace,scenario2),

   ?assertEqual([n406_initialise,n406_reset,n406_step,n406_verify],T2).

