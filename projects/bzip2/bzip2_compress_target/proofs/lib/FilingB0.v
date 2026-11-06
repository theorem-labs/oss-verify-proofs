(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import Spec04 ThmCompressAsan JoinCanon HarnModelN.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil FilingA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Prog Canon.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require RT_iface RT_state RT_rep RT_facts0 RT_artfacts RT_closed RT_liveprim RT_globals RT_io TopA_io D_defs L_libA L_harn_defs TopA_harn.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require B0_b2bc_K B0_b2bc_top B0F_b2bd_K B0F_b2bd_top.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition AF_B : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__.art_facts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__.RTA := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_artfacts.TwinB__.rta_art_facts.
Definition RC_B : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__.rt_contracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__.RTA := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_closed.TwinB__.rta_contracts_closed.
Definition AF_PRIM_B : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__.af_live_primary OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__.RTA := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__.rta_live_primary_af.
Definition AF_DRV_B : forall Σ m, OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__.ART OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__.RTA Σ m -> OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__.drv_consts m := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA_io.TwinB__.rta_drv AF_B OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_io.TwinB__.rta_io.

Lemma aceil_link_B : forall Σ m, OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__.ART OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__.RTA Σ m ->
  @ACeil.alloc_ceiling (ACeil.aceil_of_sp (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__.rt_sp0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__.RTA Σ)) = OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__.rt_sp0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__.RTA Σ - OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__.STACK_WIN.
Proof.
  intros Σ m H. destruct (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_facts0.TwinB__.rta_sp0 Σ m H) as (W & A). exact (ACeil.aceil_of_sp_exact _ W A).
Qed.

Lemma rtw_B : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__.round_trip_weak enc_okN dec_okN.
Proof. exact round_trip_weak_N. Qed.

(* [comment removed for export] *)
Theorem B2BC_B : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__.b2bc_cps OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__.RTA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A enc_okN.
Proof. exact (B0_b2bc_top.b2bc_cps_B0_K OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__.RTA RC_B AF_PRIM_B AF_DRV_B aceil_link_B). Qed.

(* [comment removed for export] *)
Theorem B2BD_B : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__.b2bd_cps OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__.RTA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A dec_okN.
Proof. exact (B0F_b2bd_top.b2bd_cps_B0_K OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__.RTA RC_B AF_PRIM_B aceil_link_B AF_DRV_B). Qed.

Theorem tgt_both : tgt_side04 B0img.
Proof. apply FilingA0.tgt_side04_of_canon. exact (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA_harn.TwinB__.canon_B0_of_lib enc_okN dec_okN B2BC_B B2BD_B rtw_B). Qed.

Theorem compress_both_san : strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target S0img B0img.
Proof. exact (join_san B0img tgt_both). Qed.

