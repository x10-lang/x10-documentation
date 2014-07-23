#
#  (C) Copyright IBM Corporation 2013-2014.
#

MODULES := \
	Assoc \
	Assoc2 \
	Auxiliary \
	Auxiliary2 \
	CopyObj \
	CopyVal \
	ECtxt \
	EvalExprProps \
	EvalStmtProps \
	Expr \
	ExprProps \
	ExprSemantics \
	GloballyReachable \
	Heap \
	HeapEvolve \
	HeapIso \
	HeapIsoReach \
	HeapIsoReachExt \
	ListUtil \
	ListUtil2 \
	ListVector \
	Reachable \
	ResilientSemantics \
	ResilientSemanticsProps \
	Stmt \
	StmtProps \
	Syntax \
	Semantics \
	TransitionLabels \
	Util \
	Value \
	WfUtil \

FILES := $(MODULES:%=%.v)

all: coq

release: clean_release
	@mkdir release
	cp $(FILES) release/
	cp Makefile index.html release/
	zip -r artifact92.zip release
	@echo "md5 checksum for artifact92.zip"
	@md5 -r artifact92.zip

coq: Makefile.coq
	@$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	@coq_makefile $(FILES) -o Makefile.coq

clean:: Makefile.coq clean_release
	@$(MAKE) -f Makefile.coq clean
	@rm -f Makefile.coq

clean_release: 
	@rm -rf release artifact92.zip

.PHONY: coq clean clean_release release

