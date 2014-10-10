ERLC    = erlc
FLAGS   = -I include -o ./ebin 
SRC     = src
EBIN    = ebin
EDOC    = edoc
MODULES = channel
BEAM    = $(patsubst %,$(EBIN)/%.beam,$(MODULES))

ga144: $(BEAM)

$(EBIN)/%.beam: $(SRC)/%.erl
	$(ERLC) $(FLAGS) $<

clean:
	rm -rf $(EBIN)/*
	rm -rf $(EDOC)/*

docs:	
	cp overview.edoc $(EDOC)
	erl -noshell -run edoc_run files "['src/channel.erl']" "[{dir,'edoc'}]"

run:	
	erl -pa $(EBIN)

