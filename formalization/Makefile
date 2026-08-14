COQMAKEFILE := Makefile.coq

all: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)

# Fails loudly if any Admitted/admit survived. The catalog is only worth
# reading if every entry it points at is actually proved.
check: all
	@! grep -rnE '\b(Admitted|admit)\b' theories --include='*.v' \
	  || (echo "FAIL: admitted proofs above" && false)
	@echo "OK: all proofs closed"

clean:
	@if [ -f $(COQMAKEFILE) ]; then $(MAKE) -f $(COQMAKEFILE) cleanall; fi
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

.PHONY: all check clean
