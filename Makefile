COQ_PROJECT := _CoqProject
COQ_MAKEFILE := coq_makefile
COQ_MAKEFILE_OUT := Makefile.coq

all: $(COQ_MAKEFILE_OUT)
	$(MAKE) -f $(COQ_MAKEFILE_OUT)

$(COQ_MAKEFILE_OUT): $(COQ_PROJECT)
	$(COQ_MAKEFILE) -f $(COQ_PROJECT) -o $(COQ_MAKEFILE_OUT)

clean:
	@if [ -f $(COQ_MAKEFILE_OUT) ]; then $(MAKE) -f $(COQ_MAKEFILE_OUT) clean; fi
	rm -f $(COQ_MAKEFILE_OUT) Makefile.coq.conf

.PHONY: all clean
