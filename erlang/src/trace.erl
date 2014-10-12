-module(trace).

% EXPORTS
%
-export([trace/2]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").


trace(ID,Msg) ->
   ?debugFmt("TRACE: ~p ~p",[ID,Msg]).


