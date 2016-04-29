all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: Make
ifeq ($(USE_GIT_SUBMODULES),yes)
	$(COQBIN)coq_makefile -f Make -o Makefile.coq -R qarith-stern-brocot QArithSternBrocot
else
	$(COQBIN)coq_makefile -f Make -o Makefile.coq -R `coqtop -where`/user-contrib/QArithSternBrocot QArithSternBrocot
endif

%: Makefile.coq
	+make -f Makefile.coq $@

.PHONY: all clean
