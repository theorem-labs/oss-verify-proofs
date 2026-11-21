(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from projects/jsoncons/fuzz_bigint/proofs/lib/BigintBothFinal.v and BigintTopAB0.v at theorem-labs/oss-verify-proofs@c5665593c2d8: as0_tgt_closed proves as0_tgt_stmt cfg0 by the as0_tgt_of_run and as0_realizes_spec_run steps of BigintTopAB0.v:91-94 (with the run's binders sdf, kb and execfn, and the eapply closed by first [eassumption | reflexivity], which also fixes the CONFIG_RSEQ flag of Bo0MainPhaseA), from the icpt layout art_IL, BUDGET0 and the as0_lib_closed, as0_drv_closed and as0_usage_closed lemmas, which are read from lib/BigintBothFinal.v (Required) and passed with the arguments that lib/BigintTopInstAB0.v passes; the halts shape around it is that of projects/jsoncons/fuzz_ubjson_parser_max/proofs/lib/UbjsonPmHaltsB.v (top_both_closed and ubjson_pm_halts_both), with the theorem renamed bigint_pm_halts_both, which gives bigint_pm_halts_both_of_top the fact sc_alloc cfg0 = false by eq_refl; the lemmas sit in Section FPX_1 with a local Existing Instance PropExec.fx0. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import HeapIface HeapIfaceA IcptIfaceAB0 LibIface LibIfaceA BrtIfaceInst BigintFinal Bo0MainPhaseA Bo0InstA BigintTopAB0 BigintTopInstAB0
  L5TopAB0 Bo0LibOkA Bo0DrvMain Bo0DiagArms Bo0UsageEntry Bo0UsageArm BigintBothFinal.
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

Lemma top_both_closed : top_both cfg0 target_alloc_limit.
Proof. exact as0_tgt_closed. Qed.

Theorem bigint_pm_halts_both :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof. exact (bigint_pm_halts_both_of_top cfg0 target_alloc_limit lim_source_le_target eq_refl top_both_closed). Qed.

End FPX_1.
