(** * HaltsUFO — example_flush_fuzzer UBSan halts over the filtered run (twin of [HaltsFL.zc_halts_ubsan])

    [HaltsFL.zc_halts_ubsan] proved the may-fail statement over the patch-04 spec.  Here the same tree
    facts ([ZTopC.ubsan_tree_okC_L], unchanged text) give the forced-only core through
    [HaltsTopFO.halts_core_of_trees], exactly as tier 0's [HaltsFO.zc_halts_plain_core] does for the
    plain build. *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import TopLevel HaltsTopFO ZTopC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import ImgFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import ExFlushIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import ModelInvC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PlainU0 Require Import UImg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ITree.Exc.
Open Scope Z_scope.

Section Halts.
Variable FM : flush_model.
Variable FK : fkit.

Theorem zc_halts_ubsan_core :
  ubsan_implC_stmt FM ->
  halts_core alloc_forced_cfg source_alloc_limit AnyExit.codes (mkImage usegs u_init_pc u_phdrs).
Proof.
  intros HU.
  apply (halts_core_of_trees usegs u_init_pc u_phdrs (tU FM)
           (epost (fun (_ : unit) (_ : machine_state) => True)) AnyExit.codes nexit_any_exit_fo).
  intros en inp Hve Hvi.
  exact (ubsan_tree_okC_L FM FK HU source_alloc_limit lim_p en inp Hve (valid_input_either_of_valid_input _ Hvi)).
Qed.

End Halts.
