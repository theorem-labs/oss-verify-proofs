(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import Spec04 ThmCompressAsan JoinCanon HarnModelN.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Prog Canon.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require RT_iface RT_state RT_rep RT_facts0 RT_artfacts RT_closed RT_liveprim RT_io TopA_io D_defs L_libA L_harn_defs TopA_harn.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require A0_b2bc_K A0_b2bc_top A0F_b2bd_K A0F_b2bd_top2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition AF_A : K.A.RT_iface.art_facts K.A.RT_rep.RTA := K.A.RT_artfacts.rta_art_facts.
Definition RC_A : K.A.RT_iface.rt_contracts K.A.RT_rep.RTA := K.A.RT_closed.rta_contracts_closed.
Definition AF_PRIM_A : K.A.RT_liveprim.af_live_primary K.A.RT_rep.RTA := K.A.RT_liveprim.rta_live_primary_af.
Definition AF_DRV_A : forall Σ m, K.A.RT_iface.ART K.A.RT_rep.RTA Σ m -> K.A.D_defs.drv_consts m := K.A.TopA_io.rta_drv AF_A K.A.RT_io.rta_io.

Lemma aceil_link_A : forall Σ m, K.A.RT_iface.ART K.A.RT_rep.RTA Σ m ->
  @ACeil.alloc_ceiling (ACeil.aceil_of_sp (K.A.RT_iface.rt_sp0 K.A.RT_rep.RTA Σ)) = K.A.RT_iface.rt_sp0 K.A.RT_rep.RTA Σ - K.A.RT_iface.STACK_WIN.
Proof.
  intros Σ m H. destruct (K.A.RT_facts0.rta_sp0 Σ m H) as (W & A). exact (ACeil.aceil_of_sp_exact _ W A).
Qed.

(* [comment removed for export] *)
Lemma rtw_A : K.A.L_harn_defs.round_trip_weak enc_okN dec_okN.
Proof. exact round_trip_weak_N. Qed.

Lemma tgt_side04_of_canon : forall timg,
  (forall en inp, valid_entry timg en inp -> valid_input_either inp ->
     trace_equiv (bh_traces (Run.run_scfg (Run.alloc_only_cfg false) timg target_alloc_limit en inp)) (K.Spec.Canon.canonT (K.Spec.Prog.argv_Z (in_argv inp)) (in_fs inp))
     /\ ~ bh_errors (Run.run_scfg (Run.alloc_only_cfg false) timg target_alloc_limit en inp)) ->
  tgt_side04 timg.
Proof.
  intros timg H en inp He Hi. destruct (H en inp He (valid_input_either_of_valid_input inp Hi)) as [TE NE].
  split; [exact NE|]. intro tr. rewrite (TE tr). exact (canon_spec04 (in_argv inp) (in_fs inp) tr).
Qed.

(* [comment removed for export] *)
Theorem B2BC_A : K.A.L_harn_defs.b2bc_cps K.A.RT_rep.RTA K.A.L_libA.LIB_A enc_okN.
Proof. exact (A0_b2bc_top.b2bc_cps_A0_K K.A.RT_rep.RTA RC_A AF_PRIM_A AF_DRV_A aceil_link_A). Qed.

(* [comment removed for export] *)
Theorem B2BD_A : K.A.L_harn_defs.b2bd_cps K.A.RT_rep.RTA K.A.L_libA.LIB_A dec_okN.
Proof. exact (A0F_b2bd_top2.b2bd_cps_A0_K K.A.RT_rep.RTA RC_A AF_PRIM_A aceil_link_A AF_DRV_A). Qed.

(* [comment removed for export] *)
Theorem tgt_asan : tgt_side04 A0img.
Proof. apply tgt_side04_of_canon. exact (K.A.TopA_harn.canon_A0_of_lib enc_okN dec_okN B2BC_A B2BD_A rtw_A). Qed.

(* [comment removed for export] *)
Theorem compress_asan_san : strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target S0img A0img.
Proof. exact (join_san A0img tgt_asan). Qed.
