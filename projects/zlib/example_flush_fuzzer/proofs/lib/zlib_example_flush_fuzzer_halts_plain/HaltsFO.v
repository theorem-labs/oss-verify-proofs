(** * HaltsFO — example_flush_fuzzer plain halts over the filtered run (twin of [HaltsFL])

    [HaltsFL.zc_halts_plain] proved the may-fail statement over the patch-04 spec.  Here the same tree
    facts ([ZTopC.plain_tree_okC], unchanged text) give the forced-only core through
    [HaltsTopFO.halts_core_of_trees]; the UBSan build is not part of tier 0. *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import TopLevel HaltsTopFO ZTopC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import ImgFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import ExFlushIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import ModelInvC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ITree.Exc.
Open Scope Z_scope.

Section Halts.
Variable FM : flush_model.
Variable FK : fkit.

Theorem zc_halts_plain_core :
  plain_implC_stmt FM ->
  halts_core alloc_forced_cfg source_alloc_limit AnyExit.codes (mkImage psegs p_init_pc p_phdrs).
Proof.
  intros HP.
  apply (halts_core_of_trees psegs p_init_pc p_phdrs (tP FM)
           (epost (fun (_ : unit) (_ : machine_state) => True)) AnyExit.codes nexit_any_exit_fo).
  intros en inp Hve Hvi.
  exact (plain_tree_okC FM FK HP source_alloc_limit lim_p en inp Hve (valid_input_either_of_valid_input _ Hvi)).
Qed.

End Halts.
