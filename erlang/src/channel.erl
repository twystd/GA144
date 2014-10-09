-module(channel).

% EXPORTS

-export([create/1]).
-export([write/2,write/3]).
-export([read/1,read/2]).
-export([close/1,close/2]).
-export([loop/1]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% RECORD DEFINITIONS

-record(channel,{ id,
                  pid
                }).

-record(state,{ id,
                state,
                word
              }).
 
% API

%% @doc Spawns a channel process and returns a 'channel' record for
%%      use with read, write and close.
create(ID) ->
   PID = spawn(channel,loop,[#state{ id=ID,
                                     state=idle
                                   }]),
   #channel{ id  = ID,
             pid = PID
           }.
  
%% @doc Writes the value to the channel and waits for the value to be 'read'.
%%
write(Channel,Value) ->
   write_with_timeout(Channel,Value,infinity).

%% @doc Writes the value to the channel and waits for the value to be 'read'.
%%
write(Channel,Value,Timeout) ->
   write_with_timeout(Channel,Value,Timeout).

%% @doc Sends a 'write' message to the channel process and waits for acknowledgement.
%%
write_with_timeout(Channel,Value,Timeout) ->
   ID  = Channel#channel.id,
   PID = Channel#channel.pid,
   PID ! { write,Value,self() },
   write_wait(ID,Timeout).

%% @doc Wait loop for a 'written' reply from the channel process.
%%
write_wait(ID,Timeout) ->
   receive
      { written,{channel,ID} } ->
         ok;

      _any ->
         write_wait(ID,Timeout)

   after Timeout ->
      timeout
   end.

%% @doc Reads a value from the channel, waiting for a 'write' if necessary.
%%
read(Channel) ->
   read_with_timeout(Channel,infinity).

%% @doc Reads a value from the channel, waiting for a 'write' if necessary.
%%
read(Channel,Timeout) ->
   read_with_timeout(Channel,Timeout).

%% @doc Sends a 'read' message to the channel process and returns the value
%%      received.
read_with_timeout(Channel,Timeout) ->
   ID  = Channel#channel.id,
   PID = Channel#channel.pid,
   PID !  { read,self() },
   read_wait(ID,Timeout).

%% @doc Wait loop for a 'read' reply from the channel process.
%%
read_wait(ID,Timeout) ->
   receive
      { read,{channel,ID},Word } ->
         { ok,Word };

   _any ->
      read_wait(ID,Timeout)

   after Timeout ->
      timeout
   end.

%% @doc Closes the channel, returning once the channel has been closed.
%%
close(Channel) ->
   close_with_timeout(Channel,infinity).

%% @doc Closes the channel, returning once the channel has been closed.
%%
close(Channel,Timeout) ->
   close_with_timeout(Channel,Timeout).

%% @doc Sends a 'close' message to the channel process and waits for acknowledgment.
%%
close_with_timeout(Channel,Timeout) ->
   ID  = Channel#channel.id,
   PID = Channel#channel.pid,
   PID ! { close,self() },
   close_wait(ID,Timeout).

%% @doc Wait loop for a 'closed' reply from the channel process.
%%
close_wait(ID,Timeout) ->
   receive
      { closed,{channel,ID}} ->
         closed;

      _any ->
         close_wait(ID,Timeout)

      after Timeout ->
         timeout
      end.

% INTERNAL

loop(State) ->
   ID   = State#state.id,
   Word = State#state.word,

   receive
      { close,PID } ->
         PID ! { closed,{channel,ID} },
         closed;

      { write,Value,PID } ->
         case State#state.state of 
            { read_wait,READER } ->
               READER ! { read,   {channel,ID},Value },
               PID    ! { written,{channel,ID}       },
               loop(State#state{ state = idle,
                                 word  = undefined });
               
            _else ->
               PID ! { written,{channel,ID} },
               loop(State#state{ word=Value })
            end;


      {read,PID } ->
         case Word of
            undefined -> 
               loop(State#state{ state={read_wait,PID} 
                               });

            _else -> 
               PID ! { read,{channel,ID},Word },
               loop(State)
            end;

      _any ->
         loop(State)
   end.

% EUNIT TESTS

close_test() ->
   Channel = create(666),
   ?assertEqual(closed,close(Channel)).

write_then_read_test() ->
   Channel = create(666),
   ?assertEqual(ok,write(Channel,123)),
   ?assertEqual({ok,123},read (Channel)),
   ?assertEqual(closed,close(Channel)).

read_then_write_test() ->
   Channel = create(666),
   M       = self(),
   spawn(fun() -> M ! { read, read (Channel)     } end),
   spawn(fun() -> M ! { write,write(Channel,123) } end),
   ?assertEqual({ok,{ok,123}},wait(undefined,undefined)).
 
wait({write,W},{read,R}) ->
   {W,R};
 
wait(W,R) ->
   receive 
      { read,RV } ->
         wait(W,{read,RV});

      { write,WV } ->
         wait({write,WV},R);

      _any ->
         wait(W,R)
   end.

