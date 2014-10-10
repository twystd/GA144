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

-record(channel,{ id,
                  pid
                }).

% API

%% @spec create(ID::integer) -> {id,pid}
%% @doc  Spawns a channel process and returns a 'channel' record for
%%       use with read, write and close.
create(ID) ->
   PID = spawn(channel,run,[ID]),
   #channel{ id  = ID,
             pid = PID
           }.
  
%% @spec write(Channel::channel,Word::integer) -> ok | closed
%% @doc  Writes the value to the channel and waits for the value to be 'read'.
%%
write(Channel,Word) ->
   write_with_timeout(Channel,Word,infinity).

%% @spec write_with_timeout(Channel::channel,Word::integer,Timeout::integer) -> ok | timeout | closed
%% @doc  Sends a 'write' message to the channel process and waits for acknowledgement.
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

      { closed,{channel,ID} } ->
         closed;

      _any ->
         write_wait(ID,Timeout)

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

      { closed,{channel,ID} } ->
         closed;

   _any ->
      read_wait(ID,Timeout)

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

%% @doc Internal function used for spawning a channel process. 
%%      (INTERNAL USE ONLY)
run(ID) ->
   loop(ID,idle).

loop(ID,idle) ->
   receive
      { close,PID } ->
         PID ! { closed,{channel,ID} };

      { write,Word,WRITER } ->
         loop(ID,{ write_pending,Word,WRITER}); 

      { read,READER } ->
         loop(ID,{ read_pending,READER }); 

      _any ->
         loop(ID,idle)
   end;

loop(ID,{write_pending,Word,WRITER}) ->
   receive
      { close,PID } ->
         WRITER ! { closed,{channel,ID} },
         PID    ! { closed,{channel,ID} };

      { read,READER } ->
         WRITER ! { written,{channel,ID}      },
         READER ! { read,   {channel,ID},Word },
         loop(ID,idle);

      _any ->
         loop(ID,{write_pending,Word,WRITER})
   end;

loop(ID,{read_pending,READER}) ->
   receive
      { close,PID } ->
         READER ! { closed,{channel,ID} },
         PID    ! { closed,{channel,ID} };

      { write,Word,WRITER } ->
         READER ! { read,   {channel,ID},Word },
         WRITER ! { written,{channel,ID}      },
         loop(ID,idle);

      _any ->
         loop(ID,{read_pending,READER})
   end.

