-module(channel).

-export([create/1,write/2,read/1,read/2,close/1]).
-export([loop/1]).

-include_lib("eunit/include/eunit.hrl").

-record(channel,{ id,
                  pid,
                  state
                }).

-record(state,{ id,
                state,
                word
              }).
 
% API

create(ID) ->
   PID = spawn(channel,loop,[#state{ id=ID,
                                     state=idle
                                   }]),
   #channel{ id  = ID,
             pid = PID,
             state = idle
           }.
  
write(Channel,Value) ->
   Channel#channel.pid ! { write,Value}.

read(Channel) ->
   Channel#channel.pid ! { read,self() },
   read_with_timeout(Channel#channel.id,infinity).

read(Channel,Timeout) ->
   Channel#channel.pid ! { read,self() },
   read_with_timeout(Channel#channel.id,Timeout).

read_with_timeout(ID,Timeout) ->
   receive
      { read,{channel,ID},Word } ->
         { ok,Word };

   _any ->
      read_with_timeout(ID,Timeout)

   after Timeout ->
      timeout
   end.

close(Channel) ->
   Channel#channel.pid ! close,
   Channel#channel{ state=closed
                  }.

% INTERNAL

loop(State) ->
   receive
      close ->
         ok;

      { write,Value } ->
         loop(State#state{ word=Value
                         });

      {read,PID } ->
         PID ! { read,{channel,State#state.id},State#state.word },
         loop(State);

      _any ->
         loop(State)
   end.

% EUNIT TESTS

close_test() ->
   Channel = create(666),
   X       = close(Channel),
   ?assertEqual(closed,X#channel.state).

write_then_read_test() ->
   Channel = create(666),
   write(Channel,123),
   R       = read (Channel,1000),
   close(Channel),
   ?assertEqual({ok,123},R).
