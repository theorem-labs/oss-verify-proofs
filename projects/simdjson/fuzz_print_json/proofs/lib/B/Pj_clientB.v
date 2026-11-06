(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjTape.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import StartupHSBoth.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.B Require Import Layout RT_iface RT_iface2 RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed
  RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_contracts RT_contracts2 RT_malsec RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin
  RT_freeFin RT_dsec RT_drain_rhead RT_freeP RT_artfacts RT_rtf RT_cli RT_livefresh D_defs D_kit D_libiface D_client
  Sj_rtf Sj_new Sj_stage1_iface Sj_stage1 Sj_h_alloc Sj_h_dtor Sj_h_deldtor Sj_stage2_iface Sj_stage2_world Sj_stage2_closed Sj_num_iface Sj_num_bdefs Sj_num_fc_stmt Sj_num_fc_closed Sj_num_closed
  Sj_stage2_numaw Sj_stage2_numow Sj_stage2_numrw
  Atp_fzwA Atp_parseA Atp_createA Atp_setcapA Sj_h_setmd Atp_activewA Atp_activeA Atp_handoffA
  RT_iface3 RT_stackmalloc3w
  Pj_defsA Pj_hdefsA Pj_os_defsA Pj_cliA Pj_mciA Pj_mciRTA Pj_loc_topA Pj_os_dtorA Pj_os_xsputnA Pj_os_ctorA Pj_os_padA Pj_os_putA Pj_growA
  RT_iface4 RT_stackmalloc1z Pj_ser_objkA Pj_ser_okey1A Pj_ser_okey2A Pj_ser_closedA Pj_sfA Pj_tocharsA_defs Pj_fmtB Pj_dboxB Pj_tocharsA
  Pj_pidwA Pj_pdtor2A Pj_pidA Pj_lftoi3A Pj_topA Pj_handoffA.
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

Definition rta_new1 : new_cps RTA e_new_nt := new_nt_ok RTA rta_art_facts (rf_malloc RTA rta_rtf).
Definition rta_newa : new_cps RTA e_newarr_nt := newarr_nt_ok RTA rta_art_facts (rf_malloc RTA rta_rtf).
Definition rta_dela : del_cps RTA e_delarr := delarr_ok RTA rta_art_facts (rf_free RTA rta_rtf).
Definition rta_del1 : del_cps RTA e_del := del_ok RTA rta_art_facts (rf_free RTA rta_rtf).

Lemma rta_fcb : forall PMc, fdfs_only PMc -> mat_stable PMc -> fcb_stmt RTA PMc.
Proof. exact (fcb_closed RTA rta_art_facts rta_rtf). Qed.
Lemma rta_slowfa : slowfa_cps RTA.
Proof. exact (slowfa_closed RTA rta_art_facts rta_rtf rta_fcb). Qed.
Lemma rta_pffa : pffa_cps RTA.
Proof. exact (pffa_closed RTA rta_art_facts rta_rtf rta_fcb). Qed.
Theorem rta_numa : numa_stmt RTA.
Proof. exact (numa_world RTA rta_art_facts rta_slowfa rta_pffa). Qed.
Theorem rta_numo : numo_stmt RTA.
Proof. exact (numo_world RTA rta_art_facts rta_slowfa rta_pffa). Qed.
Theorem rta_rootnum : rootnum_stmt RTA.
Proof. exact (rootnum_world RTA rta_art_facts rta_rtf rta_slowfa rta_pffa (fun Σ m HA => rta_got_nothrow Σ m HA) rta_live_fresh). Qed.
Theorem rta_stage2at : stage2at_cps RTA.
Proof. exact (stage2at_closed RTA rta_art_facts rta_rtf rta_numa rta_numo rta_rootnum). Qed.
Theorem rta_stage1 : stage1_cps RTA.
Proof. exact (stage1_ok RTA rta_art_facts (rf_asan_memcpy RTA rta_rtf)). Qed.

Theorem rta_parse : parse_cps RTA.
Proof. exact (parse_ok RTA rta_art_facts rta_stage1 rta_stage2at). Qed.
Theorem rta_create : create_cps RTA.
Proof.
  exact (create_ok RTA rta_art_facts rta_new1 (rf_asan_memset RTA rta_rtf)
           (setcap_ok RTA rta_art_facts rta_newa (fun Σ m HA => rta_got_nothrow Σ m HA))
           (setmd_ok RTA rta_art_facts rta_newa (fun Σ m HA => rta_got_nothrow Σ m HA))
           (fun Σ m HA => rta_got_nothrow Σ m HA) (fun Σ m HA => rta_vt_dpi Σ m HA)).
Qed.
Theorem rta_alloc : allocate_cps RTA.
Proof. exact (allocate_ok RTA rta_art_facts rta_newa (fun Σ m HA => rta_got_nothrow Σ m HA)). Qed.

Theorem rta_docd : docdtor_cps RTA.
Proof. exact (docdtor_ok RTA rta_art_facts rta_dela). Qed.
Theorem rta_deld : deldtor_cps RTA.
Proof. exact (deldtor_ok RTA rta_art_facts rta_dela rta_del1). Qed.

Theorem rta_loc : forall PMc, loc_get_cpsA RTA PMc.
Proof. intros PMc. pose proof (loc_get_okA RTA rta_art_facts rta_rc rta_memcmp_inner PMc) as H. unfold loc_get_cpsA in *. intros; eapply H; eassumption. Qed.
Theorem rta_iosd : forall PMc, iosdtor_cpsA RTA PMc OSIOSA.
Proof. intros PMc. pose proof (iosdtor_cpsA_proof RTA rta_art_facts rta_rc PMc) as H. unfold iosdtor_cpsA in *. intros; eapply H; eassumption. Qed.

Definition rta_grow : forall PMc, fdfs_only PMc -> mat_stable PMc -> grow_cpsA RTA PMc := grow_okA RTA rta_art_facts rta_rc.
Theorem rta_ctor : forall PMc, ctor_cpsA RTA PMc OSFRESHA.
Proof.
  intros PMc. pose proof (fun FDO MST => ctor_okA RTA rta_art_facts rta_rc PMc FDO MST (fun Σ m HA => rta_os_ro Σ m HA) (rta_loc PMc)) as H.
  unfold ctor_cpsA in *. intros; eapply H; eassumption.
Qed.
Theorem rta_put : forall PMc, put_cpsA RTA PMc OSFRESHA OSUSEDA.
Proof.
  intros PMc. pose proof (fun FDO MST => put_ok_fullA RTA rta_art_facts rta_rc rta_rc2 PMc FDO MST (fun Σ m HA => rta_os_ro Σ m HA)) as H.
  unfold put_cpsA in *. intros; eapply H; eassumption.
Qed.

Definition rta_tochars : forall PMc, fdfs_only PMc -> mat_stable PMc -> tochars_cpsA RTA PMc :=
  fun PMc FDO MST => tochars_okB RTA rta_art_facts rta_rc PMc FDO MST
                       (dbox_okB RTA rta_art_facts rta_rc rta_stack_malloc_1z PMc FDO MST) (fmt_okB RTA rta_art_facts rta_rc PMc FDO MST).
Definition rta_okey1 : forall PMc, fdfs_only PMc -> mat_stable PMc -> okey1_stmtA RTA PMc :=
  fun PMc FDO MST => okey1_okA RTA rta_art_facts rta_rc PMc FDO MST (rta_grow PMc FDO MST).
Definition rta_okey2 : forall PMc, fdfs_only PMc -> mat_stable PMc -> okey2_stmtA RTA PMc :=
  fun PMc FDO MST => okey2_okA RTA rta_art_facts rta_rc PMc FDO MST (rta_grow PMc FDO MST).
Theorem rta_ser : forall PMc, ser_cpsA RTA PMc TAPE_MAX_DEPTH.
Proof.
  intros PMc. pose proof (fun FDO MST => ser_closedA RTA rta_art_facts rta_rc rta_rc2 rta_stack_malloc_3w rta_stack_malloc_1z PMc FDO MST
                                          (rta_grow PMc FDO MST) (rta_tochars PMc FDO MST) (rta_okey1 PMc FDO MST) (rta_okey2 PMc FDO MST) TAPE_MAX_DEPTH) as H.
  unfold ser_cpsA in *. intros; eapply H; eassumption.
Qed.

Theorem rta_fuzz_one_pj : fuzz_one_cps RTA pj_lib.
Proof.
  exact (fuzz_one_pjB RTA rta_art_facts rta_rc (pdone2 RTA) (pdtor2_ok RTA rta_art_facts rta_dela rta_docd rta_deld (fun Σ m HA => rta_vt_dpi Σ m HA))
           (pdone2_fp RTA rta_art_facts)
           (pj_pid_okA RTA rta_art_facts rta_rtf rta_parse rta_alloc rta_create rta_newa
              (fun Σ m HA => rta_got_nothrow Σ m HA) (fun Σ m HA => rta_vt_dpi Σ m HA) (fun Σ m HA => rta_vt_impl Σ m HA))
           (fun PMc => pj_okarm_okA RTA rta_art_facts rta_rc PMc OSFRESHA OSUSEDA OSIOSA OSFRESHA_loc OSUSEDA_imp OSUSEDA_ios
              (fun Σ m HA => rta_os_ro Σ m HA) (rta_ctor PMc) (rta_ser PMc) (rta_put PMc) locdtor_evtA_proof (rta_iosd PMc))).
Qed.

Definition client_pj : client_B :=
  mkClientB pj_lib pj_lib_loc hs_libj_ok
    (fun A nx0 LIMIT SINV argH FS0 H1 H2 H3 E ch R FULL model HC A' HA' HT =>
       match hs_libj_gen A nx0 LIMIT SINV argH FS0 H1 H2 H3 E ch R FULL model HC A' HA' HT with
       | conj L (conj B W) => conj L (conj (or_introl B) W) end)
    (fun _ => rta_fuzz_one_pj).

Lemma client_pj_hs : forall h ch, HS_both h = Some ch -> hs_libj_ok ch = true.
Proof. intros h ch H. exact (HS_libj_ok h ch H). Qed.