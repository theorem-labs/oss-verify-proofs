(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from projects/jsoncons/fuzz_bigint/proofs/lib/BigintAsanFinal.v and BigintTopA.v at theorem-labs/oss-verify-proofs@c5665593c2d8: as0_tgt_closed proves as0_tgt_stmt cfg0 by the as0_tgt_of_run and as0_realizes_spec_run steps of BigintTopA.v:90-93 (with the run's binders sdf, kb and execfn, and the eapply closed by first [eassumption | reflexivity], which also fixes the CONFIG_RSEQ flag of As0MainPhaseA), from the icpt layout art_IL, BUDGET0 and the as0_lib_closed, as0_drv_closed and as0_usage_closed lemmas, which are read from lib/BigintAsanFinal.v (Required) and passed with the arguments that lib/BigintTopInstA.v passes; the halts shape around it is that of projects/jsoncons/fuzz_ubjson_parser_max/proofs/lib/UbjsonPmHaltsA.v (top_asan_closed and ubjson_pm_halts_asan), with the theorem renamed bigint_pm_halts_asan, which gives bigint_pm_halts_asan_of_top the fact sc_alloc cfg0 = false by eq_refl; the lemmas sit in Section FPX_1 with a local Existing Instance PropExec.fx0. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import HeapIface HeapIfaceA IcptIfaceA LibIface LibIfaceA ArtIfaceInst BigintFinal As0MainPhaseA As0InstA BigintTopA BigintTopInstA
  L5TopA As0LibOkA As0DrvMain As0DiagArms As0UsageEntry As0UsageArm BigintAsanFinal.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus Require Import CorpusShape CorpusSpec CorpusHalts CorpusHaltsTop.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

Lemma as0_tgt_closed : as0_tgt_stmt cfg0.
Proof.
  apply as0_tgt_of_run.
  intros sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn Hsp Hbrk Hmb Hva Hve Hfit Hlau Hvl Huid Hhw Hvfs.
  eapply (as0_realizes_spec_run cfg0 eq_refl eq_refl art_L art_C art_IL LayA0 L5TOPA.TopLSA BUDGET0 BUDGET0_lo BUDGET0_hi
            (as0_inst_ok cfg0 BUDGET0 eq_refl) (as0_free_null cfg0 BUDGET0) (as0_h4e BUDGET0)
            (as0_icpt_ok cfg0 art_IL BUDGET0 art_IL_ok) as0_lib_closed (as0_dla_ok cfg0 art_IL art_IL_ok)
            (as0_drv_consts art_IL art_IL_ok) as0_drv_closed as0_usage_closed);
    first [eassumption | reflexivity].
Qed.

Lemma top_asan_closed : top_asan cfg0 target_alloc_limit.
Proof. exact as0_tgt_closed. Qed.

Theorem bigint_pm_halts_asan :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. exact (bigint_pm_halts_asan_of_top cfg0 target_alloc_limit lim_source_le_target eq_refl top_asan_closed). Qed.

End FPX_1.
