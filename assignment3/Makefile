.DEFAULT_GOAL := invoke-coqmakefile

RocqMakefile: Makefile _RocqProject
	$(COQBIN)coq_makefile -f _RocqProject -o RocqMakefile

invoke-coqmakefile: RocqMakefile
	$(MAKE) -f RocqMakefile

clean: RocqMakefile
	$(MAKE) -f RocqMakefile clean

.PHONY: invoke-coqmakefile
