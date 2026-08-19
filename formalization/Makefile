# Rocq 9.x. The binaries were renamed at 9.0: `rocq makefile` / `rocq compile`
# replace `coq_makefile` / `coqc`.
ROCQ ?= rocq
COQMAKEFILE := Makefile.rocq

all: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	$(ROCQ) makefile -f _CoqProject -o $(COQMAKEFILE)

# The gate. Three things, any of which would make the catalog worthless:
# an admitted proof, a proof closed via an axiom, or a build failure.
check: all
	@! grep -rnE '\b(Admitted|admit)\b' theories --include='*.v' \
	  || (echo "FAIL: admitted proofs above" && false)
	@echo "OK: no admitted proofs"
	@sh tools/check_axioms.sh

clean:
	@if [ -f $(COQMAKEFILE) ]; then $(MAKE) -f $(COQMAKEFILE) cleanall; fi
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

.PHONY: all check clean
