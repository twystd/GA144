-module(util).

% EXPORTS

-export([is_registered/1,unregister/1]).
-export([read_bin_file/1]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% API

is_registered(ID) ->
   is_registered(ID,whereis(ID)).

is_registered(_,undefined) ->
   false;

is_registered(_,_) ->
   true.

unregister(ID) ->
   unregister(ID,whereis(ID)).

unregister(_,undefined) ->
   ok;

unregister(ID,_) ->
   erlang:unregister(ID).


read_bin_file(FilePath) ->
   {ok,File} = file:open(FilePath,[read]),     
   Mem       = parse_file(File),
   file:close(File),

   {{ram,make_ram(Mem)},
    {rom,make_rom(Mem)}
   }.

parse_file(File) ->
   parse_file(File,{0,[]}).     

parse_file(File,{Org,Mem}) ->
   case file:read_line(File) of     
        {ok,Line} ->
            parse_file(File,parse_line(Line,{Org,Mem}));       

        eof ->
            lists:reverse(Mem);

        {error,Reason} ->
            {error,Reason}
        end.       

parse_line(Line,{Org,Mem}) ->
   case re:run(Line,"ORG\s+([a-fA-F0-9]{4})",[{capture,all_but_first,list}]) of
        {match,Address} ->           
           {list_to_integer(lists:flatten(Address),16),Mem};

        _else ->
           case re:run(Line,"\s*([a0fA-F0-9]{5})",[{capture,all_but_first,list}]) of
                   {match,Word} ->
                       {Org + 1,[{Org,list_to_integer(lists:flatten(Word),16)} | Mem]};

                   _else ->
                       {Org,Mem}
                 end    
        end.        

make_ram(Mem) ->
   make_ram(Mem,array:new(64,[{default,16#00000}])).

make_ram([],RAM) ->
   RAM;

make_ram([{Address,Word}|T],RAM) when Address < 64 ->
   make_ram(T,array:set(Address,Word,RAM));

make_ram([_|T],RAM) ->
   make_ram(T,RAM).

make_rom(Mem) ->
   make_rom(Mem,array:new(64,[{default,16#13400}])).

make_rom([],ROM) ->
   ROM;

make_rom([{Address,Word}|T],ROM) when (Address >= 128) and (Address < 192) ->
   make_rom(T,array:set(Address-128,Word,ROM));

make_rom([_|T],ROM) ->
   make_rom(T,ROM).

