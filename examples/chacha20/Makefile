.PHONY: default lean clean
default:
	make -C proofs/fstar/extraction

lean:
	cargo hax into lean --aeneas-args="-core-models-lib"
	(cd proofs/lean && \
		elan default v4.30.0-rc2 && \
		lake exe cache get && \
		lake build)

clean:
	rm -f proofs/fstar/extraction/.depend
	rm -f proofs/fstar/extraction/*.fst
	-find proofs/lean/Chacha20/Extraction -type f ! -name FunsExternal.lean -delete
	-cd proofs/lean && lake clean
