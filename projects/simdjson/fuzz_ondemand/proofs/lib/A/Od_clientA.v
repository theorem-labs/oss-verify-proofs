(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Ceiling RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import StartupHSAsan.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed
  RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_contracts RT_contracts2 RT_malsec RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin
  RT_freeFin RT_dsec RT_drain_rhead RT_freeP RT_artfacts RT_rtf RT_cli RT_livefresh D_defs D_libiface D_client
  Sj_rtf Sj_new Sj_stage1 Sj_num_iface Sj_num_adefs Sj_num_fc_stmt Sj_num_fc_top6 Sj_num_closed
  Atp_h_defsA Atp_h_vkitA Atp_h_emplA Atp_h_destroyA Atp_activewA Atp_activeA Atp_handoffA
  Od_hkit0A Od_defsA Od_cpsA Od_topA Od_createA Od_setcapA Od_setmdA Od_deldtorA Od_fromchA Od_cliA Od_splitintoA Od_s1zA
  Od_errx_defsA Od_errxA Od_setup_defsA Od_setup_defs2A Od_setupw4A Od_setupdA Od_handA Od_setupA Od_closedA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition rta_rc : rt_contracts RTA :=
  rta_contracts (refill_ok fixed_commit_ok) (mal_core_sec grant_node_ok fixed_commit_pab_ok)
    (rta_free (drain_ok rhead_empty_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok (free_pass_ok munmap_ok madvise_ok)).
Definition rta_rc2 : rt_contracts2 RTA :=
  rta_contracts2 (refill_ok fixed_commit_ok) (mal_core_sec grant_node_ok fixed_commit_pab_ok)
    (rta_free (drain_ok rhead_empty_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok (free_pass_ok munmap_ok madvise_ok)).
Definition rta_rtf : rt_contracts_f RTA := rtf_of_rt RTA rta_rc.

Definition rta_dela : del_cps RTA e_delarr := delarr_ok RTA rta_art_facts (rf_free RTA rta_rtf).
Definition rta_del1 : del_cps RTA e_del := del_ok RTA rta_art_facts (rf_free RTA rta_rtf).

Theorem rta_dtor : deldtor_cps RTA.
Proof. exact (deldtor_ok RTA rta_art_facts rta_dela rta_del1). Qed.
Theorem rta_vdes : vdestroy_cpsA RTA.
Proof. exact (vdestroy_ok RTA rta_art_facts rta_rtf (rc2_annotate RTA rta_rc2)). Qed.

Lemma rta_fca : forall PMc, fdfs_only PMc -> mat_stable PMc -> fca_stmt RTA PMc.
Proof. exact (fca_closed RTA rta_art_facts rta_rtf). Qed.
Lemma rta_fromch : forall PMc, fdfs_only PMc -> mat_stable PMc -> fromcha_stmt RTA PMc.
Proof. exact (fromcha_ok RTA rta_art_facts (ffa_closed RTA rta_art_facts rta_fca)). Qed.

Definition rta_new1 : new_cps RTA e_new_nt := new_nt_ok RTA rta_art_facts (rf_malloc RTA rta_rtf).
Definition rta_newa : new_cps RTA e_newarr_nt := newarr_nt_ok RTA rta_art_facts (rf_malloc RTA rta_rtf).

Theorem rta_spl0 : splitinto_cps0A RTA.
Proof. exact (splitinto0_closed RTA rta_art_facts rta_rtf rta_rc2). Qed.
Theorem rta_empl : empl_cpsA RTA.
Proof. exact (empl_ok RTA rta_art_facts rta_rtf (rc2_annotate RTA rta_rc2)). Qed.
Theorem rta_getact : getact_cps RTA.
Proof. exact (getact_ok RTA rta_art_facts). Qed.
Theorem rta_create : create_cps RTA.
Proof.
  exact (create_ok RTA rta_art_facts rta_new1 (rf_asan_memset RTA rta_rtf)
           (setcap_ok RTA rta_art_facts rta_newa (fun Σ m HA => rta_got_nothrow Σ m HA))
           (setmd_ok RTA rta_art_facts rta_newa (fun Σ m HA => rta_got_nothrow Σ m HA))
           (fun Σ m HA => rta_got_nothrow Σ m HA) (fun Σ m HA => rta_vt_dpi Σ m HA)).
Qed.
Theorem rta_stage1 : stage1_cps RTA.
Proof. exact (stage1_ok RTA rta_art_facts (rf_asan_memcpy RTA rta_rtf)). Qed.
Theorem rta_stage1z : stage1z_cps RTA.
Proof. exact (stage1z_ok RTA rta_art_facts (rf_asan_memcpy RTA rta_rtf)). Qed.

Lemma rta_errx : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_errx_stmt RTA sj_lib PMc.
Proof.
  intros PMc FDO MST.
  exact (od_errx RTA sj_lib sj_lib_loc rta_art_facts PMc FDO MST rta_rtf rta_dela rta_dtor rta_vdes (fun Σ m HA => rta_vt_dpi Σ m HA)).
Qed.

Lemma HANDOVER : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_handover_stmt RTA sj_lib PMc.
Proof.
  intros PMc _ _.
  exact (od_handover RTA sj_lib PMc rta_art_facts (fun Σ m HA => rta_vt_dpi Σ m HA) (fun Σ m HA => rta_got_tabs Σ m HA)).
Qed.

Lemma SETUP : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_setup_stmt RTA sj_lib PMc.
Proof.
  exact (od_setup RTA rta_art_facts rta_rtf rta_newa rta_spl0 rta_empl rta_getact rta_create rta_stage1 rta_stage1z
           (fun Σ m HA => rta_got_nothrow Σ m HA) (fun Σ m HA => rta_vt_dpi Σ m HA) (fun Σ m HA => rta_vt_impl Σ m HA) rta_errx HANDOVER).
Qed.

Theorem rta_fuzz_one_od : fuzz_one_cps RTA sj_lib.
Proof.
  exact (fuzz_one_closed_odA RTA sj_lib rta_art_facts sj_lib_loc rta_rtf rta_dela rta_dtor rta_vdes
           (fun Σ m HA => rta_vt_dpi Σ m HA) (fun Σ m HA => rta_got_tabs Σ m HA) rta_fromch SETUP).
Qed.

Definition client_od : client_A :=
  mkClientA sj_lib sj_lib_loc hs_lib_ok
    (fun A nx0 LIMIT SINV argH FS0 H1 H2 H3 E ch R FULL model HC A' HA' HT => hs_lib_gen A nx0 LIMIT SINV argH FS0 H1 H2 H3 E ch R FULL model HC A' HA' HT)
    (fun _ => rta_fuzz_one_od).

Lemma client_od_hs : forall h ch, HS_asan h = Some ch -> cl_hs_ok client_od ch = true.
Proof. intros h ch H. exact (HS_lib_ok h ch H). Qed.
