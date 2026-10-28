(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface5 RT_state RT_rep RT_refillstmt TopA_iodefs RT_io RT_win RT_noret RT_artfacts RT_alignedalloc RT_strncasecmp. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_libiface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import El_defsA El_sitesA El_throw_siteA El_sitesXB El_clientA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.
Open Scope Z_scope.

Definition el_win : rt_win RTA := mkRTW (@RTA GWf) ARTW_A rta_noret_enter rta_noret_again rta_unwind_icpt w_tls_A w_facts_A w_rc_A w_rc2_A w_exit_A.
Definition el_RC5 (RF : refill_stmt) : rt_contracts5 RTA := mkRTC5 RTA (rta_aligned_alloc RF) rta_strncasecmp rta_strncasecmp0 el_win.

Definition el_WA (RF : refill_stmt) : Z -> rts RTA -> mem -> Prop := ARTW RTA (rc5_win RTA (el_RC5 RF)).

Lemma w_io_ro_A : forall c Σ m, ARTW_A c Σ m -> io_ro_ok m.
Proof. intros c Σ m H. exact (proj1 (proj2 (@rta_io (GWt c) Σ m H))). Qed.

Section Rec.
Hypothesis RF : refill_stmt.
Hypothesis DUMP : forall PMc, dump_cpsA RTA PMc.

Definition X22 (RC2 : rt_contracts2 RTA) : forall PMc pcs, throw_siteB RTA PMc (el_WA RF) 22 pcs :=
  fun PMc pcs => throw_site22B RTA rta_art_facts (rc2_rt RTA RC2) (rc5_aligned_alloc RTA (el_RC5 RF)) (rc5_win RTA (el_RC5 RF)) PMc (fun c Σ m H => w_io_ro_A c Σ m H) pcs.
Definition X23 (RC2 : rt_contracts2 RTA) : forall PMc, throw_siteB RTA PMc (el_WA RF) 23 0xb2fb4 :=
  fun PMc => throw_site23B RTA rta_art_facts (rc2_rt RTA RC2) (rc5_aligned_alloc RTA (el_RC5 RF)) (rc5_win RTA (el_RC5 RF)) PMc (fun c Σ m H => w_io_ro_A c Σ m H).
Definition X24 (RC2 : rt_contracts2 RTA) : forall PMc, throw_siteB RTA PMc (el_WA RF) 24 EL_SITE_END_B :=
  fun PMc => throw_site24B RTA rta_art_facts (rc2_rt RTA RC2) (rc5_aligned_alloc RTA (el_RC5 RF)) (rc5_win RTA (el_RC5 RF)) PMc (fun c Σ m H => w_io_ro_A c Σ m H).

Theorem el_cl_fuzz : rt_contracts2 RTA -> fuzz_one_cps RTA el_libA.
Proof.
  intros RC2. exact (rta_fuzz_one_el RC2 (el_RC5 RF) (fun c Σ m H => w_cli_ro_A c Σ m H) (X22 RC2) (X23 RC2) (X24 RC2) DUMP).
Qed.
End Rec.
