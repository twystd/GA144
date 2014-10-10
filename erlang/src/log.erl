-module(log).

% EXPORTS

-export([debug/2]).
-export([info/2]).
-export([warn/2]).
-export([error/2]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% API

debug(Tag,Msg) ->
   ?debugFmt("DEBUG: ~s  ~s",[Tag,Msg]).

info(Tag,Msg) ->
   ?debugFmt("INFO:  ~s  ~s",[Tag,Msg]).

warn(Tag,Msg) ->
   ?debugFmt("WARN:  ~s  ~s",[Tag,Msg]).

error(Tag,Msg) ->
   ?debugFmt("ERROR: ~s  ~s",[Tag,Msg]).
