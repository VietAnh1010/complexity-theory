# Rocq 9.x. The binaries were renamed at 9.0: `rocq makefile` / `rocq compile`
# replace `coq_makefile` / `coqc`.
ROCQ ?= rocq
COQMAKEFILE := Makefile.rocq

all: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	$(ROCQ) makefile -f _CoqProject -o $(COQMAKEFILE)

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
