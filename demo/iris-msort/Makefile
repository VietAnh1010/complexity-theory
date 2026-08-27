DEPS_LIB := $(CURDIR)/_deps/lib

# If setup.sh installed std++ and Iris into a local prefix, use it; otherwise
# fall back to whatever is installed system-wide (or in the opam switch).
ifneq ($(wildcard $(DEPS_LIB)),)
ifeq ($(COQPATH),)
export COQPATH := $(DEPS_LIB)
else
export COQPATH := $(DEPS_LIB):$(COQPATH)
endif
endif

all: Makefile.coq
	+@$(MAKE) -f Makefile.coq all

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	+@if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	@rm -f Makefile.coq Makefile.coq.conf

.PHONY: all clean
