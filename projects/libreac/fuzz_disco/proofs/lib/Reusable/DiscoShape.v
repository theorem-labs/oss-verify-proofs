(* fuzz_disco's library shape for the ASan side, as a named constant that a core file can declare with
   `#[local] Existing Instance disco_lib_shape.` in place of cgif_file_fuzzer's ff_lib_shape (lib/YI0a.v). It is the
   shape of the released agreement (lib/DiscoAgree.v:25, AgreeShape.ag_shape ZTraceSpec.checksum_shape), so the trace
   set SPECX of the ASan obligations is the plain realization's (lib/A/DiscoAsanTop.v disco_shape, the same term). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require ZTraceSpec AgreeShape.
(* Removes the plain checksum_shape instances (Reusable/PlainHintsOff.v), so that in a core file that declares
   disco_lib_shape as its local instance, a lib_shape argument left to search is disco_lib_shape and nothing else. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require PlainHintsOff.

Definition disco_lib_shape : lib_shape := AgreeShape.ag_shape ZTraceSpec.checksum_shape.
