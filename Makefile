.PHONY: test test-core test-slow test-upstreams status

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
