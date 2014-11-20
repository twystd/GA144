-module(sync).

-export([start/0,stop/0,hook/2]).
-export([run/0]).

-include_lib("kernel/include/file.hrl").

start()->
   start(is_registered()).

start(true) ->
   ok;

start(_) ->
   PID = spawn(sync,run,[]),
   register(sync,PID),
   ok.

stop() ->
   stop(is_registered()).

stop(true) ->
   sync ! stop,
   ok;

stop(_) ->
   ok.

hook(Module,Fun) ->
   sync ! {hook,{Module,Fun}},
   ok.

is_registered() ->
   lists:foldl(fun(X,A) ->
                  case X of
                     sync -> true;
                    _else -> A
                  end
               end,false,registered()).
                           
run() ->
   make:all([load]),
   loop    (files(),none).

loop(Files,Hook) ->
   receive
      {hook,F} ->
        loop(Files,F);

      stop ->
         unregister(sync)

      after 1000 ->
         loop(resync(Files,Hook),Hook)
      end.

resync(Files,Hook) ->
   Lookup   = dict:from_list(Files),
   SrcFiles = files(),
   
   F = fun({FileName,Timestamp},List) ->
          case dict:find(FileName,Lookup) of
               {ok,LastTimestamp} ->
                       T1 = calendar:datetime_to_gregorian_seconds(Timestamp),
                       T2 = calendar:datetime_to_gregorian_seconds(LastTimestamp),
                       if 
                           T1 > T2 -> 
                              [FileName|List];
                          true ->
                              List
                         end;

               _else ->
                       [FileName | List]
               end
       end,
 
   Modified = lists:foldl(F,[],SrcFiles),

   if 
     length(Modified) > 0 ->
         case make:all([load]) of 
            up_to_date ->
               hooks(Hook);
    
            _else ->
               oops()
         end;
           
     true ->
         ok
     end,
   SrcFiles.

files() ->
   F = fun(X) ->
          case re:run(X,"^[a-zA-Z0-9_]+\.erl$") of
               {match,_} -> 
                       true;
               _else ->
                       false
          end
       end,

   G = fun(X) ->
          {ok,Info} = file:read_file_info(filename:join("src",X)),
          Info#file_info.mtime
       end,

   H = fun(X) ->
          {ok,Info} = file:read_file_info(filename:join("eunit",X)),
          Info#file_info.mtime
       end,

   {ok,Src  } = file:list_dir("./src"),
   {ok,Tests} = file:list_dir("./eunit"),

   lists:append([ { X,G(X) } || X <- lists:filter(F,Src)   ],
                [ { X,H(X) } || X <- lists:filter(F,Tests) ]).

hooks(none) ->
   ok;

hooks({Module,Fun}) ->
   io:format("... running hook ~p:~p~n",[Module,Fun]),     
   spawn(Module,Fun,[]),
   ok;

hooks(Hook) ->
   io:format("... can't run hook ~p~n",[Hook]),     
   ok.

oops() ->
   ok.

