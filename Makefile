all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: Make
	if [ -z $(DSTROOT) ]; then \
		$(COQBIN)coq_makefile -R qarith-stern-brocot QArithSternBrocot -f Make -o Makefile.coq; \
	else \
		$(COQBIN)coq_makefile -R $(DSTROOT)$(COQLIBINSTALL)/QArithSternBrocot QArithSternBrocot -f Make -o Makefile.coq; \
	fi

%: Makefile.coq
	+make -f Makefile.coq $@

.PHONY: all clean
