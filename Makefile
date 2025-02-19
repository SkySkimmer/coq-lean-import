MAKE_OPTS:= --no-builtin-rules

TEST_GOALS:=$(filter test%, $(MAKECMDGOALS))

.PHONY: submake
submake: Makefile.rocq
	$(MAKE) $(MAKE_OPTS) -f Makefile.rocq $(filter-out test%, $(MAKECMDGOALS))
	+$(if $(TEST_GOALS),$(MAKE) $(MAKE_OPTS) -C tests $(patsubst tests/%,%,$(filter-out test, $(TEST_GOALS))))

Makefile.rocq: _CoqProject
	$(COQBIN)rocq makefile -f $< -o $@

%:: submake ;

# known sources

Makefile: ;

_CoqProject: ;
