# Configuration
OCAMLC=ocamlc
COQC=$(COQBIN)coqc

##############################################################################
# usage:
# make          launch the tests
# make clean    clean temp files
##############################################################################

COQ_TESTS=pc12.v coqextrcommand.v
TESTS=add.v imp.v fibo.v so.v odd.v tuples.v extrcommand.v
COQC_FILE=$(shell which $(COQC))
ML_TESTS=$(subst .v,.ml,$(TESTS))
ML_TESTS_OBJ=$(subst .v,.cmo,$(TESTS))

all: $(ML_TESTS) test coq_test

%.ml: %.v $(COQC)
	$(COQC) $< >$@

%.cmo: %.ml
	$(OCAMLC) -c $<

tester.cmo: tester.ml $(ML_TESTS_OBJ)
	$(OCAMLC) -c $<

tester: $(ML_TESTS_OBJ) tester.cmo
	$(OCAMLC) -o $@ $^

.PHONY: clean test coq_test

test: tester
	./tester

coq_test:
	python test_coq_files.py $(COQC) $(COQ_TESTS)

clean:
	rm -f $(ML_TESTS) *.cmo *.cmi *.vo *.glob tester

