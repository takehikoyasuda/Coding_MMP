.PHONY: test test-upstreams status

test: test-upstreams

test-upstreams:
	./scripts/test-upstreams.sh

status:
	@git submodule status
