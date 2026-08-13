.PHONY: test test-core test-upstreams status

test: test-core test-upstreams

test-core:
	M2 --no-readline --stop -q tests/nefness.m2
	M2 --no-readline --stop -q tests/contraction.m2
	M2 --no-readline --stop -q tests/relative-model.m2
	M2 --no-readline --stop -q tests/multigraded-nefness.m2
	M2 --no-readline --stop -q tests/multigraded-skew-cartier.m2

test-upstreams:
	./scripts/test-upstreams.sh

status:
	@git submodule status
