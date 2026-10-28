(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_iface5 RT_state RT_rep R_fs_defs RT_stackmalloc RT_stackmalloc1 RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin RT_freeFin RT_freelift RT_dsec RT_drain_rhead RT_freeP RT_iclifts RT_iclifts3 RT_iclifts4 RT_iclifts_t2 RT_iclift0 RT_icliftmv RT_setshadow RT_stackfree5 RT_artfacts TopA_iodefs RT_cli RT_tlsga.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition ARTW_A (c : Z) : rtsA -> mem -> Prop := @ART_A (GWt c).

Section Window.
Variable c : Z.
#[local] Instance GWw : GW := GWt c.

Let S1 : rt_sig := RTA.
Let S2 : rt_sig := rt_sigW (@RTA GWf) (ARTW_A c).

Remark sig_ART : ART S2 = ART S1. Proof. reflexivity. Qed.
Remark sig_credit : forall Σ, rt_credit S2 Σ = 0. Proof. reflexivity. Qed.

Lemma w_malloc : malloc_contract S2.
Proof. red. intros. exfalso. cbn [rt_credit S2 rt_sigW] in *. unfold mcost, DCOST in *. destruct (_ <=? 64512); lia. Qed.
Lemma w_stack_malloc : forall k, stack_malloc_contract S2 k.
Proof. red. intros. exfalso. cbn [rt_credit S2 rt_sigW] in *. lia. Qed.
Lemma w_stack_malloc1 : stack_malloc1_contract S2.
Proof. red. intros. exfalso. cbn [rt_credit S2 rt_sigW] in *. lia. Qed.

Lemma w_free_of : free_contract S1 -> free_contract S2.
Proof.
  intros H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo FDO MST HIN HA0 HTP ART0 MI0 CALL UW.
  eapply cps_conseq; [exact (H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo FDO MST HIN HA0 HTP ART0 MI0 CALL UW) | intros c0 X; exact X|].
  intros cf (Σ' & v & HQ & E1 & E2 & E3 & E4). exists Σ', v. split; [exact HQ|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3 | reflexivity].
Qed.
Lemma w_stack_free_of : forall k, stack_free_contract S1 k -> stack_free_contract S2 k.
Proof.
  intros k H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f fr lo FDO MST HK HA0 HTP HFR ART0 MI0 CALL.
  eapply cps_conseq; [exact (H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f fr lo FDO MST HK HA0 HTP HFR ART0 MI0 CALL) | intros c0 X; exact X|].
  intros cf (Σ' & v & HQ & E1 & E2 & E3 & E4). exists Σ', v. split; [exact HQ|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3 | reflexivity].
Qed.

Lemma w_facts_of : art_facts S1 -> art_facts S2.
Proof.
  intros AF. destruct AF. split; try assumption.

  intros Σ m f k fr HA E. destruct (af_frame_release Σ m f k fr HA E) as (Σ' & fl & R1 & R2 & R3 & R4 & R5 & R6).
  exists Σ', fl. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
  intros m' MU WM RW. destruct (R6 m' MU WM RW) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [reflexivity|]. split; [exact A6 | exact A7].
Qed.

Let w_free1 : free_contract S1 :=
  rta_free (drain_ok rhead_empty_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok (free_pass_ok munmap_ok madvise_ok).

Definition w_rc_A : rt_contracts S2 :=
  mkRTC S2 w_malloc (w_free_of w_free1) rta_free_null
        rta_memcpy rta_asan_memcpy rta_memset rta_asan_memset rta_asan_memmove rta_memchr rta_strlen rta_strnlen rta_memcmp
        (w_stack_malloc 4) (w_stack_malloc 5) (w_stack_free_of 5 rta_stack_free_5) rta_set_shadow (w_facts_of rta_art_facts).
Definition w_rc2_A : rt_contracts2 S2 :=
  mkRTC2 S2 w_rc_A w_stack_malloc1 rta_memmove2 rta_memcmp_wide rta_memcmp_zero.
Definition w_facts_A : art_facts S2 := w_facts_of rta_art_facts.

Definition w_tls_A : tls_get_addr_icontract S2 := rta_tls_get_addr.

Lemma w_exit_A : forall Σ m, ARTW_A c Σ m -> rt_frames (@RTA GWf) Σ = [] -> ART (@RTA GWf) Σ m /\ rt_credit (@RTA GWf) Σ = c.
Proof.
  intros Σ m HA FR. cbn [rt_frames rt_credit RTA ART] in *. unfold rtA_frames, rtA_credit in *. unfold ARTW_A in HA.
  destruct HA as (WF & CR & PR & CA & CH & SE & QU & DE & FS & IA & SH & VI).
  destruct FS as (((g & G1 & G2 & G3) & OFL) & FREST).
  assert (EC : credit Σ = c) by (exact (G3 eq_refl)).
  split; [|exact EC].
  apply (@ART_intro GWf); try assumption.
  unfold fs_rep. lazy zeta. split; [|exact FREST]. split; [|exact OFL]. exists g. split; [exact G1|]. split; [intros _ _; exact FR | intros X; discriminate X].
Qed.

Lemma w_cli_ro_A : forall Σ m, ARTW_A c Σ m -> cli_ro m.
Proof. intros Σ m HA. exact (rta_cli_ro Σ m HA). Qed.

End Window.

Definition noret_enter_stmt : Prop := forall c, handle_no_return_contract (@RTA GWf) (fun Σ m => ART (@RTA GWf) Σ m /\ rt_credit (@RTA GWf) Σ = c) (ARTW_A c).
Definition noret_again_stmt : Prop := forall c, handle_no_return_contract (@RTA GWf) (ARTW_A c) (ARTW_A c).
Definition unwind_icpt_stmt : Prop := forall c, unwind_raise_stmt (@RTA GWf) (ARTW_A c) (ARTW_A c).

Theorem rta_win : noret_enter_stmt -> noret_again_stmt -> unwind_icpt_stmt -> rt_win (@RTA GWf).
Proof.
  intros NE NA UW. exact (mkRTW (@RTA GWf) ARTW_A NE NA UW w_tls_A w_facts_A w_rc_A w_rc2_A w_exit_A).
Qed.
