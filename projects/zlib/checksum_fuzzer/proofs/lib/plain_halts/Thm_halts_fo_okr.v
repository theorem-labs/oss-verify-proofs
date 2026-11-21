(** * plain_halts.Thm_halts_fo_okr: checksum_fuzzer plain halts with status 0 or 2, forced-only

    As [plain_halts_any_exit.FO.Thm_halts_fo], with the exit set [Exits.ok_or_refused]: [FOCore] moves the
    may-fail result [Thm_checksum_halts_okr.halts_plain_okr] onto every spurious-failure configuration, and the
    release shell is the [budget] cell at [forced_only_cfg]. *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Core Require Shapes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts Require Thm_checksum_halts_okr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition img : Image :=
  mkImage Src_zlib_checksum_fuzzer_repro.M.loaded_segments Src_zlib_checksum_fuzzer_repro.M.init_pc Src_zlib_checksum_fuzzer_repro.M.phdrs.

(** The core: halting with status 0 or 2 under every configuration, no budget premise. *)
Theorem halts_plain_okr_core : forall cfg, halts_core cfg source_alloc_limit OSSVerify.Core.Shapes.Exits.ok_or_refused img.
Proof.
  intros cfg. apply halts_core_of_halts_allowed_may_fail.
  exact (OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts.Thm_checksum_halts_okr.halts_plain_okr).
Qed.

Theorem halts_plain_okr_forced_only :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source OSSVerify.Core.Shapes.Exits.ok_or_refused img.
Proof. apply halts_allowed_T_scfg_budgets_of_core, halts_plain_okr_core. Qed.
