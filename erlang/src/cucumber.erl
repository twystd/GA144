-module(cucumber).

-export([run/2]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% RECORDS

-record(feature,{ feature,
                  scenarios=[]
                }).

-record(scenario,{ scenario,
                   steps=[],
                   tags=[]
                 }).

-record(step,{ type,
               description
             }).

% DEFINES

-define(TAG,"CUCUMBER").


% API

run(Module,{strings,Lines}) ->
   feature(Module,parse(Lines));

run(Module,{file,File}) ->
   feature(Module,read_feature_file(File)).

feature(Module,Feature) ->
   log:info(?TAG,"Runinng feature '~s'",[Feature#feature.feature]),
   Context = scenario(Module,
                      apply(Module,setup,[]),
                      Feature#feature.scenarios),
   apply(Module,teardown,[Context]).

scenario(_,Context,[]) ->
    Context;

scenario(Module,Context,[Scenario|T]) ->
   Tags = Scenario#scenario.tags,
   F    = fun(X) -> X =:= ignore end,
   case lists:any(F,Tags) of
        true ->
           log:info(?TAG,"Scenario: '~s' (IGNORED)",[Scenario#scenario.scenario]),
           scenario(Module,Context,T);

        _else ->
           log:info(?TAG,"Scenario: '~s'",[Scenario#scenario.scenario]),
           try
               Context2 = steps(Module,Context,Scenario#scenario.steps),
               scenario(Module,Context2,T)
           catch
               {error,X} ->
               log:error(?TAG,X),
               throw({error,X})
            end
   end.

steps(_,Context,[]) ->
    log:info(?TAG,"OK"),
    Context;

steps(Module,Context,[Step|T]) ->
    Type = Step#step.type,
    Description = Step#step.description,
    log:info(?TAG,"Step: ~-7.5s ~s",[Type,Description]),
    steps(Module,
          apply(Module,step,[Context,Type,Description]),
          T).

% INTERNAL

read_feature_file(FilePath) ->
   {ok,File} = file:open(FilePath,[read]),
   read_feature_file(File,[]).

read_feature_file(File,Lines) ->
   case file:read_line(File) of     
        {ok,Line} ->
            read_feature_file(File,[Line|Lines]);

        eof ->
            file:close(File),
            parse(lists:reverse(Lines));

        {error,Reason} ->
            file:close(File),
            {error,Reason}
        end.       


parse([]) ->
   { error,"Invalid feature" };

parse([Line|T]) ->
    case re:run(Line,"^Feature:\s*(.*)\s*$",[{capture,all_but_first,list}]) of
        {match,Description} ->           
            parse(#feature{feature = Description},T);

        _else ->
            parse(T)
        end.        

parse(Feature,Lines) ->
    Feature#feature{ scenarios = parse_feature(Lines,Feature#feature.scenarios,[])
                   }.

parse_feature([],Scenarios,_) ->
    lists:reverse(Scenarios);

parse_feature([Line|T],Scenarios,Tags) ->
    case parse_line(Line) of
        {tag,ignore} ->
            parse_feature(T,Scenarios,[ignore | Tags]);

        {scenario,Description} ->           
            parse_scenario(T,
                           [ #scenario{scenario=Description,
                                       tags=Tags
                                      } | Scenarios
                           ],
                           []);

        _else ->
            parse_feature(T,Scenarios,Tags)
        end.        

parse_scenario([],Scenarios,_Tags) ->
    [ #scenario{ scenario = X#scenario.scenario,
                 steps = lists:reverse(X#scenario.steps),
                 tags = X#scenario.tags
               } || X <- lists:reverse(Scenarios) ];

parse_scenario([Line|T],Scenarios,Tags) ->
    case parse_line(Line) of
        {tag,ignore} ->
            parse_scenario(T,Scenarios,[ignore | Tags]);

         {scenario,Description} ->           
             parse_scenario(T,
                            [ #scenario{scenario=Description,
                                        tags=Tags} | Scenarios 
                            ],
                            []);

         {step,Type,Text} ->
             [Scenario | R ] = Scenarios,
              Steps           = Scenario#scenario.steps,
              Step            = parse_step(Type,Text),
              parse_scenario(T,
                             [ Scenario#scenario { steps=[Step | Steps] } | R],
                             []);

         _else ->
              parse_scenario(T,Scenarios,Tags)
        end.        

parse_step("Given",Description) ->
    #step{type=given,
          description=Description 
         };

parse_step("And",Description) ->
    #step{type='and',
          description=Description 
         };

parse_step("Then",Description) ->
    #step{type=then,
          description=Description 
         }.

parse_line(Line) ->
    case re:run(Line,"^\s*Scenario:\s*(.*)\s*$",[{capture,all_but_first,list}]) of
        {match,Description} ->           
          {scenario,Description};

        _else ->
            case re:run(Line,"^\s*(Given|And|Then)\s+(.*)\s*$",[{capture,all_but_first,list}]) of
               {match,[Type,Text]} ->           
                  {step,Type,Text};

               _else2 ->
                  case re:run(Line,"^\s*(@ignore).*$",[{capture,all_but_first,list}]) of
                     {match,["@ignore"]} ->
                        {tag,ignore};

                     _else3 ->
                        unknown
                  end
            end
        end.        

