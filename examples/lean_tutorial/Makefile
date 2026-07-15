.PHONY: default legacy-lean lean clean

default: lean

legacy-lean:
	cargo hax into legacy-lean
	(cd proofs/legacy-lean && \
   elan default v4.29.0-rc1 && \
   lake build)

lean:
	cargo hax into lean --aeneas-args="-core-models-lib"
	(cd proofs/lean && \
		elan default v4.30.0-rc2 && \
		lake exe cache get && \
		lake build)

clean:
	-rm -f proofs/legacy-lean/extraction/lean_tutorial.lean
	-cd proofs/legacy-lean && lake clean
	-find proofs/lean/LeanTutorial/Extraction -type f ! -name FunsExternal.lean -delete
	-cd proofs/lean && lake clean
