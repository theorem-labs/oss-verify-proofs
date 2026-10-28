(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_state RT_rep RT_stackmalloc RT_stackmalloc2 RT_smgc RT_artfacts TopA_iodefs RT_io RT_cli El_defsA El_os_defsA El_ins_ifaceA El_np_boolA Dmp_insbA Dmp_hdefsA Dmp_pj_ifaceA Dmp_rtkA Dmp_pjA D_client Dmp_clrecA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GWf.

Lemma np_bool_vt_rta : forall Σ m, ART RTA Σ m -> ro_cells bsegs m 0x16cb98 [C8 (Z_to_bv 64 EL_NP_BOOL_A)].
Proof. intros Σ m HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_sm2 : stack_malloc2_contract RTA.
Proof. exact (rta_stack_malloc_2 smgc2_proof). Qed.

Theorem pj_rootA_rta : forall PMc, pj_root_cpsA RTA PMc.
Proof.
  intros PMc. unfold pj_root_cpsA. intros until m. intros FDO MST.
  revert Σ K E OS q fO kO ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  pose proof (pj_rootA RTA rta_art_facts rta_sm2 PMc FDO MST (rta_put PMc FDO MST) (rta_ins_b PMc FDO MST np_bool_vt_rta)
                (rta_ins_l PMc FDO MST) (rta_ins_ul PMc FDO MST) (rta_ins_d PMc FDO MST)) as H.
  unfold pj_root_cpsA in H. intros. eapply H; eassumption.
Qed.

Definition client_dmp_closed : client_B := client_dmp pj_rootA_rta.
