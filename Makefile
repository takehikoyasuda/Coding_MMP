.PHONY: install docs docs-clean examples examples-page site test test-core test-slow test-upstreams status

DOCDIR := doc-build
DOCINDEX := $(DOCDIR)/share/doc/Macaulay2/MMPComputation/html/index.html

# The manual, built in place instead of into the user's Macaulay2 directory the
# way `make install` does, so that it can be read without installing anything
# and published from CI.  The two dependencies still have to be installed
# first: documentation examples run in fresh Macaulay2 processes whose working
# directory is not this repository, so they cannot reach the pinned sources by
# path.  They go in without their own documentation, which is built in their own
# repositories.  All three go into the same prefix: the examples of the
# installed MMPComputation no longer sit next to the submodule sources, so they
# fall back to loading the dependencies by name, and they have to be findable
# where the package being installed is.  The default prefix is not usable --
# on a Debian or Ubuntu Macaulay2 it is the system one and not writable.
#
# Each recipe passes one unbroken line to the shell on purpose.  A
# backslash-newline inside a single-quoted M2 expression is not portable: GNU
# make 3.81, as shipped on macOS, joins those lines before handing the recipe to
# the shell, while make 4.x leaves the backslash in place, where single quotes
# stop the shell from removing it and M2 stops with "syntax error at '\'".
docs:
	rm -rf $(DOCDIR)
	M2 --no-readline --stop -q -e 'installPackage("SteinFactorization", FileName => "third_party/SteinFactorizationM2/SteinFactorization.m2", InstallPrefix => "$(CURDIR)/$(DOCDIR)/", MakeDocumentation => false, RunExamples => false); exit 0'
	M2 --no-readline --stop -q -e 'installPackage("FlipComputation", FileName => "third_party/flip-computation/FlipComputation.m2", InstallPrefix => "$(CURDIR)/$(DOCDIR)/", MakeDocumentation => false, RunExamples => false); exit 0'
	M2 --no-readline --stop -q -e 'installPackage("MMPComputation", FileName => "MMPComputation.m2", InstallPrefix => "$(CURDIR)/$(DOCDIR)/", RerunExamples => true, RemakeAllDocumentation => true, IgnoreExampleErrors => false, MakeInfo => false); exit 0'
	@echo
	@echo "file://$(CURDIR)/$(DOCINDEX)"

docs-clean:
	rm -rf $(DOCDIR)

# The worked-examples page published beside the manual.  `examples` re-runs
# every example in Macaulay2 and rewrites its transcript and timing.
# `examples-page` only inlines what is already recorded.  CI does both on every
# push, so the committed transcripts are for reading, not for publishing.
examples:
	./examples/run.sh

# The page links Style/doc.css and Style/katex relatively, the way the site
# serves them, so opening a bare html file in the repository root would show it
# unstyled with the mathematics as raw TeX.  The preview directory gets a copy
# of Macaulay2's Style tree beside the page, which is what `make site` does for
# the published one.
examples-page:
	./examples/build-page.py preview/examples.html
	rm -rf preview/Style
	cp -RL "$$(M2 --no-readline -q -e 'print prefixDirectory; exit 0' < /dev/null | tail -1)share/Macaulay2/Style" preview/Style
	find preview -type l -delete
	@echo
	@echo "file://$(CURDIR)/preview/examples.html"

# The published site exactly as CI assembles it, for looking at before pushing.
site: docs examples-page
	.github/make-site.sh $(DOCDIR)/share/doc/Macaulay2/MMPComputation/html site MMPComputation https://github.com/takehikoyasuda/Coding_MMP preview/examples.html
	@echo "file://$(CURDIR)/site/examples.html"

install:
	M2 --no-readline --stop -q -e 'installPackage("SteinFactorization",FileName=>"third_party/SteinFactorizationM2/SteinFactorization.m2",MakeDocumentation=>false,RunExamples=>false); exit 0'
	M2 --no-readline --stop -q -e 'installPackage("FlipComputation",FileName=>"third_party/flip-computation/FlipComputation.m2",MakeDocumentation=>false,RunExamples=>false); exit 0'
	M2 --no-readline --stop -q -e 'installPackage("MMPComputation",FileName=>"MMPComputation.m2"); exit 0'

test: test-core test-upstreams

test-core:
	M2 --no-readline --stop -q tests/nefness.m2
	M2 --no-readline --stop -q tests/contraction.m2
	M2 --no-readline --stop -q tests/relative-model.m2
	M2 --no-readline --stop -q tests/multigraded-nefness.m2
	M2 --no-readline --stop -q tests/multigraded-skew-cartier.m2
	M2 --no-readline --stop -q tests/multigraded-section-representatives.m2
	M2 --no-readline --stop -q tests/bpf-class-degree-fastpath.m2
	M2 --no-readline --stop -q tests/canonical-seed-bpf-fastpath.m2
	M2 --no-readline --stop -q tests/cartier-index-fastpath.m2
	M2 --no-readline --stop -q tests/threshold-cost-aware-search.m2
	M2 --no-readline --stop -q tests/multigraded-mmp-driver.m2
	M2 --no-readline --stop -q tests/negative-curve-witness-multigraded.m2

# Not part of test-core: dominated by mmpStepRecordData's
# contractionSmallnessData call, which takes on the order of 15 minutes of
# cpu time (see tests/bl-p-p3-two-step-mmp.m2's header comment).
test-slow:
	M2 --no-readline --stop -q tests/bl-p-p3-two-step-mmp.m2

test-upstreams:
	./scripts/test-upstreams.sh

status:
	@git submodule status
