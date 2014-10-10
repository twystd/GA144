-module(channel_tests).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% EUNIT TESTS

close_test() ->
   Channel = channel:create(666),
   ?assertEqual(closed,channel:close(Channel)).

write_then_read_test() ->
   Channel = channel:create(666),
   M       = self(),
   spawn(fun() ->                   M ! { a,channel:write(Channel,123) } end),
   spawn(fun() -> timer:sleep(250), M ! { b,channel:read (Channel)     } end),
   ?assertEqual({ok,{ok,123}},wait(undefined,undefined)),
   ?assertEqual(closed,channel:close(Channel)).

read_then_write_test() ->
   Channel = channel:create(666),
   M       = self(),
   spawn(fun() ->                   M ! { a,channel:read (Channel)     } end),
   spawn(fun() -> timer:sleep(250), M ! { b,channel:write(Channel,123) } end),
   ?assertEqual({{ok,123},ok},wait(undefined,undefined)),
   ?assertEqual(closed,channel:close(Channel)).

write_then_close_test() ->
   Channel = channel:create(666),
   M       = self(),
   spawn(fun() ->                   M ! { a,channel:write(Channel,123) } end),
   spawn(fun() -> timer:sleep(250), M ! { b,channel:close(Channel)     } end),
   ?assertEqual({closed,closed},wait(undefined,undefined)).

read_then_close_test() ->
   Channel = channel:create(666),
   M       = self(),
   spawn(fun() ->                   M ! { a,channel:read (Channel) } end),
   spawn(fun() -> timer:sleep(250), M ! { b,channel:close(Channel) } end),
   ?assertEqual({closed,closed},wait(undefined,undefined)).
   
write_read_write_read_test() ->
   Channel = channel:create(666),
   M       = self(),
   spawn(fun() -> W1 = channel:write(Channel,123), W2 = channel:write(Channel,456), M ! { a,{W1,W2} } end),
   spawn(fun() -> R1 = channel:read (Channel),     R2 = channel:read (Channel),     M ! { b,{R1,R2} } end),
   ?assertEqual({{ok,ok},{{ok,123},{ok,456}}},wait(undefined,undefined)),
   ?assertEqual(closed,channel:close(Channel)).

wait({a,X},{b,Y}) ->
   {X,Y};

wait(X,Y) ->
   receive 
      { a,A } ->
         wait({a,A},Y);

      { b,B } ->
         wait(X,{b,B});

      _any ->
         wait(X,Y)
   end.

