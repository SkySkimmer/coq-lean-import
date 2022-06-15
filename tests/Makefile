MAKE_OPTS:= --no-builtin-rules

.PHONY: submake
submake: Makefile.coq
	$(MAKE) $(MAKE_OPTS) -f Makefile.coq $(filter-out test%, $(MAKECMDGOALS))

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@

%:: submake ;

# known sources

Makefile: ;

_CoqProject: ;
