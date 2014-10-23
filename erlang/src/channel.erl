-module(channel).

% EXPORTS

-export([create/1]).
-export([write/2]).
-export([read/1]).
-export([close/1]).
-export([run/1]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% RECORD DEFINITIONS

% API

%% @spec create(ID::integer) -> {id,pid}
%% @doc  Spawns a channel process and returns a 'channel' record for
%%       use with read, write and close.
create(ID) ->
   util:unregister(ID),
   register       (ID,spawn(channel,run,[ID])),
   ID.
  
%% @spec write(Channel::channel,Word::integer) -> ok | closed
%% @doc  Writes the value to the channel and waits for the value to be 'read'.
%%
write(Channel,Word) ->
   write_with_timeout(Channel,Word,infinity).

%% @spec write_with_timeout(Channel::channel,Word::integer,Timeout::integer) -> ok | timeout | closed
%% @doc  Sends a 'write' message to the channel process and waits for acknowledgement.
%%
write_with_timeout(Channel,Value,Timeout) ->
   Channel ! { write,Value,self() },
   write_wait(Channel,Timeout).

%% @doc Wait loop for a 'written' reply from the channel process.
%%
write_wait(Channel,Timeout) ->
   receive
      { written,{channel,Channel} } ->
         ok;

      { closed,{channel,Channel} } ->
         closed;

      _any ->
         write_wait(Channel,Timeout)

   after Timeout ->
      timeout
   end.

%% @doc Reads a value from the channel, waiting for a 'write' if necessary.
%%
read(Channel) ->
   read_with_timeout(Channel,infinity).

%% @doc Sends a 'read' message to the channel process and returns the value
%%      received.
read_with_timeout(Channel,Timeout) ->
   Channel !  { read,self() },
   read_wait(Channel,Timeout).

%% @doc Wait loop for a 'read' reply from the channel process.
%%
read_wait(Channel,Timeout) ->
   receive
      { read,{channel,Channel},Word } ->
         { ok,Word };

      { closed,{channel,Channel} } ->
         closed;

   _any ->
      read_wait(Channel,Timeout)

   after Timeout ->
      timeout
   end.

%% @doc Closes the channel, returning once the channel has been closed.
%%
close(Channel) ->
   close_with_timeout(Channel,infinity).

%% @doc Sends a 'close' message to the channel process and waits for acknowledgment.
%%
close_with_timeout(Channel,Timeout) ->
   Channel ! { close,self() },
   close_wait(Channel,Timeout).

%% @doc Wait loop for a 'closed' reply from the channel process.
%%
close_wait(Channel,Timeout) ->
   receive
      { closed,{channel,Channel}} ->
         closed;

      _any ->
         close_wait(Channel,Timeout)

      after Timeout ->
         timeout
      end.

% INTERNAL

%% @doc Internal function used for spawning a channel process. 
%%      (INTERNAL USE ONLY)
run(Channel) ->
   loop(Channel,idle).

loop(Channel,idle) ->
   receive
      { close,PID } ->
         PID ! { closed,{channel,Channel} };

      { write,Word,WRITER } ->
         loop(Channel,{ write_pending,Word,WRITER}); 

      { read,READER } ->
         loop(Channel,{ read_pending,READER }); 

      _any ->
         loop(Channel,idle)
   end;

loop(Channel,{write_pending,Word,WRITER}) ->
   receive
      { close,PID } ->
         WRITER ! { closed,{channel,Channel} },
         PID    ! { closed,{channel,Channel} };

      { read,READER } ->
         WRITER ! { written,{channel,Channel}      },
         READER ! { read,   {channel,Channel},Word },
         loop(Channel,idle);

      _any ->
         loop(Channel,{write_pending,Word,WRITER})
   end;

loop(Channel,{read_pending,READER}) ->
   receive
      { close,PID } ->
         READER ! { closed,{channel,Channel} },
         PID    ! { closed,{channel,Channel} };

      { write,Word,WRITER } ->
         READER ! { read,   {channel,Channel},Word },
         WRITER ! { written,{channel,Channel}      },
         loop(Channel,idle);

      _any ->
         loop(Channel,{read_pending,READER})
   end.

