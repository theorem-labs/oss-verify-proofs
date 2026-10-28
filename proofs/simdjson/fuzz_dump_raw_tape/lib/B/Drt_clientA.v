(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjTape.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_state RT_rep RT_artfacts RT_rtf RT_cli RT_livefresh RT_contracts RT_contracts2 TopA_iodefs D_defs D_kit D_clx D_libiface D_auxv Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_stage1_iface Sj_stage1 Sj_h_alloc Sj_h_dtor Sj_h_deldtor Sj_h_setmd Sj_stage2_iface Sj_stage2_world Sj_stage2_closed Sj_num_iface Sj_num_bdefs Sj_num_fc_stmt Sj_num_fc_closed Sj_num_closed Sj_stage2_numaw Sj_stage2_numow Sj_stage2_numrw Atp_fzwA Atp_parseA Atp_createA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_pidiA Atp_pid1A Atp_pidA Pj_defsA Pj_os_defsA Pj_hdefsA Pj_os_ctorA Pj_os_dtorA Pj_loc_topA Pj_mciRTA Pj_pdtor2A Pj_pidA El_defsA El_dumpA Drt_hdefsA Drt_okarmA Drt_topA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GWf.
Open Scope Z_scope.

Lemma cli_os_ro : forall m, cli_ro m -> pj_os_roA m.
Proof. intros m H. unfold pj_os_roA. split; [| split; [| split]]; (apply (cli_ro_at m); [exact H| cli_in]). Qed.
Lemma rta_os_ro : forall Σ m, ART RTA Σ m -> pj_os_roA m.
Proof. intros Σ m HA. exact (cli_os_ro m (rta_cli_ro Σ m HA)). Qed.

Section ClientDrt.

Hypothesis SM3 : drt_sm3_contract RTA.

Definition rta_af : art_facts RTA := rta_art_facts.
Definition rta_rc : rt_contracts RTA := el_RC.
Definition rta_rtf : rt_contracts_f RTA := rtf_of_rt RTA rta_rc.

Definition rta_new1 : new_cps RTA e_new_nt := new_nt_ok RTA rta_af (rf_malloc RTA rta_rtf).
Definition rta_newa : new_cps RTA e_newarr_nt := newarr_nt_ok RTA rta_af (rf_malloc RTA rta_rtf).
Definition rta_dela : del_cps RTA e_delarr := delarr_ok RTA rta_af (rf_free RTA rta_rtf).
Definition rta_del1 : del_cps RTA e_del := del_ok RTA rta_af (rf_free RTA rta_rtf).

Lemma rta_fcb : forall PMc, fdfs_only PMc -> mat_stable PMc -> fcb_stmt RTA PMc.
Proof. exact (fcb_closed RTA rta_af rta_rtf). Qed.
Lemma rta_slowfa : slowfa_cps RTA.
Proof. exact (slowfa_closed RTA rta_af rta_rtf rta_fcb). Qed.
Lemma rta_pffa : pffa_cps RTA.
Proof. exact (pffa_closed RTA rta_af rta_rtf rta_fcb). Qed.
Lemma rta_numa : numa_stmt RTA.
Proof. exact (numa_world RTA rta_af rta_slowfa rta_pffa). Qed.
Lemma rta_numo : numo_stmt RTA.
Proof. exact (numo_world RTA rta_af rta_slowfa rta_pffa). Qed.
Lemma rta_rootnum : rootnum_stmt RTA.
Proof. exact (rootnum_world RTA rta_af rta_rtf rta_slowfa rta_pffa (fun Σ m HA => rta_got_nothrow Σ m HA) rta_live_fresh). Qed.
Lemma rta_stage2at : stage2at_cps RTA.
Proof. exact (stage2at_closed RTA rta_af rta_rtf rta_numa rta_numo rta_rootnum). Qed.
Lemma rta_stage1 : stage1_cps RTA.
Proof. exact (stage1_ok RTA rta_af (rf_asan_memcpy RTA rta_rtf)). Qed.
Lemma rta_parse : parse_cps RTA.
Proof. exact (parse_ok RTA rta_af rta_stage1 rta_stage2at). Qed.
Lemma rta_create : create_cps RTA.
Proof.
  exact (create_ok RTA rta_af rta_new1 (rf_asan_memset RTA rta_rtf)
           (setcap_ok RTA rta_af rta_newa (fun Σ m HA => rta_got_nothrow Σ m HA))
           (setmd_ok RTA rta_af rta_newa (fun Σ m HA => rta_got_nothrow Σ m HA))
           (fun Σ m HA => rta_got_nothrow Σ m HA) (fun Σ m HA => rta_vt_dpi Σ m HA)).
Qed.
Lemma rta_alloc : allocate_cps RTA.
Proof. exact (allocate_ok RTA rta_af rta_newa (fun Σ m HA => rta_got_nothrow Σ m HA)). Qed.
Lemma rta_docd : docdtor_cps RTA.
Proof. exact (docdtor_ok RTA rta_af rta_dela). Qed.
Lemma rta_deld : deldtor_cps RTA.
Proof. exact (deldtor_ok RTA rta_af rta_dela rta_del1). Qed.

Lemma rta_pid : pj_pid_cpsA RTA (pj_libA sj_lib) (pdone2 RTA).
Proof.
  exact (pj_pid_okA RTA rta_af rta_rtf rta_parse rta_alloc rta_create rta_newa
           (fun Σ m HA => rta_got_nothrow Σ m HA) (fun Σ m HA => rta_vt_dpi Σ m HA) (fun Σ m HA => rta_vt_impl Σ m HA)).
Qed.
Lemma rta_pdtor : pdtor_cps RTA (pdone2 RTA).
Proof. exact (pdtor2_ok RTA rta_af rta_dela rta_docd rta_deld (fun Σ m HA => rta_vt_dpi Σ m HA)). Qed.

Theorem rta_loc : forall PMc, loc_get_cpsA RTA PMc.
Proof. intros PMc. pose proof (loc_get_okA RTA rta_af rta_rc rta_memcmp_inner PMc) as H. unfold loc_get_cpsA in *. intros; eapply H; eassumption. Qed.
Theorem rta_ctor : forall PMc, ctor_cpsA RTA PMc OSFRESHA.
Proof.
  intros PMc. pose proof (fun FDO MST => ctor_okA RTA rta_af rta_rc PMc FDO MST rta_os_ro (rta_loc PMc)) as H.
  unfold ctor_cpsA in *. intros; eapply H; eassumption.
Qed.
Theorem rta_iosd : forall PMc, iosdtor_cpsA RTA PMc OSIOSA.
Proof. intros PMc. pose proof (fun FDO MST => iosdtor_cpsA_proof RTA rta_af rta_rc PMc FDO MST) as H. unfold iosdtor_cpsA in *. intros; eapply H; eassumption. Qed.

Theorem rta_okarm : forall PMc, drt_okarm_cpsA RTA PMc.
Proof. intros PMc. exact (drt_okarm_okA RTA rta_af PMc rta_os_ro (rta_ctor PMc) (el_dump PMc) locdtor_evtA_proof (rta_iosd PMc)). Qed.

Theorem rta_fuzz_one_drt : fuzz_one_cps_drt RTA el_libA.
Proof.
  exact (fuzz_one_drtA RTA rta_af rta_rc SM3 (pdone2 RTA) rta_pdtor (pdone2_fp RTA rta_af) rta_pid rta_okarm).
Qed.
End ClientDrt.
