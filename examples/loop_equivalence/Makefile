.PHONY: default clean
default:
	cargo hax into lean --aeneas-args="-core-models-lib"
	sed -i \
		'/^open Aeneas /c\open core_models Aeneas\nopen Aeneas.Std hiding namespace core alloc\nopen Result ControlFlow Error' \
		proofs/lean/LoopEquivalence/Extraction/Funs.lean
	sed -i \
		's/import Aeneas/import CoreModels/' \
		proofs/lean/LoopEquivalence/Extraction/Funs.lean
	(cd proofs/lean && \
   elan default v4.30.0-rc2 && \
   lake exe cache get && \
   lake build)

clean:
	-cd proofs/lean && lake clean
