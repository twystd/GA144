-module(cucumber).

-export([run/2]).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% RECORDS

-record(feature,{ feature,
                  scenarios = []
                }).

-record(scenario,{ scenario,
                   steps = []
                 }).

-record(step,{ type,
               description
             }).

% DEFINES

-define(TAG,"CUCUMBER").


% API

run(Module,{strings,Lines}) ->
   Feature = parse(Lines),
   log:info(?TAG,"Runinng feature '~s'",[Feature#feature.feature]),
   scenario(Module,Feature#feature.scenarios);

run(Module,{file,File}) ->
   Feature = read_feature_file(File),
   log:info(?TAG,"Runinng feature '~s'",[Feature#feature.feature]),
   scenario(Module,Feature#feature.scenarios).

scenario(_,[]) ->
    ok;

scenario(Module,[Scenario|T]) ->
    log:info(?TAG,"Scenario: '~s'",[Scenario#scenario.scenario]),
    steps(Module,Scenario#scenario.steps),
    scenario(Module,T).

steps(_,[]) ->
    ok;

steps(Module,[Step|T]) ->
    Type = Step#step.type,
    Description = Step#step.description,
    log:info(?TAG,"Step: ~-7.5s ~s",[Type,Description]),
    apply(Module,step,[Type,Description]),
    steps(Module,T).

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
    Feature#feature{ scenarios = parse_feature(Lines,Feature#feature.scenarios)
                   }.

parse_feature([],Scenarios) ->
    lists:reverse(Scenarios);

parse_feature([Line|T],Scenarios) ->
    case re:run(Line,"^Scenario:\s*(.*)\s*$",[{capture,all_but_first,list}]) of
        {match,Description} ->           
            parse_scenario(T,[ #scenario{scenario=Description} | Scenarios]);

        _else ->
            parse_feature(T,Scenarios)
        end.        

parse_scenario([],Scenarios) ->
    [ #scenario{ scenario = X#scenario.scenario,
                 steps = lists:reverse(X#scenario.steps)
               } || X <- lists:reverse(Scenarios) ];

parse_scenario([Line|T],Scenarios) ->
    case re:run(Line,"^Scenario:\s*(.*)\s*$",[{capture,all_but_first,list}]) of
        {match,Description} ->           
            parse_scenario(T,[ #scenario{scenario=Description} | Scenarios ]);

        _else ->
            case re:run(Line,"^\s*(Given|And|Then)\s+(.*)\s*$",[{capture,all_but_first,list}]) of
                {match,[Type,Text]} ->           
                    [Scenario | R ] = Scenarios,
                    Steps           = Scenario#scenario.steps,
                    Step            = parse_step(Type,Text),
                    parse_scenario(T,[ Scenario#scenario { steps=[Step | Steps]
                                                         } | R]);

                _else ->
                    parse_scenario(T,Scenarios)
                end
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

% EUNIT
