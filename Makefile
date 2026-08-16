.PHONY: install test test-core test-slow test-upstreams status

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
