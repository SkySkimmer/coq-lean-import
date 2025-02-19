MAKE_OPTS:= --no-builtin-rules

.PHONY: submake
submake: Makefile.rocq
	$(MAKE) $(MAKE_OPTS) -f Makefile.rocq $(MAKECMDGOALS)

Makefile.rocq: _CoqProject
	$(COQBIN)rocq makefile -f $< -o $@

%:: submake ;

# known sources

Makefile: ;

_CoqProject: ;
