(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_thread R_tlsgetaddr R_tlsga2 RT_iface RT_iface5 D_defs I_lift RT_state RT_rep RT_facts0 RT_facts RT_artfacts R_fs_defs RT_stackmalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem rta_tls_get_addr : tls_get_addr_icontract RTA.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p lo
    FDO MST -> -> P0 P8 PSP PTOP TI ART0 MI0 CALL.
  intros T cf Hc Hk.
  pose proof (af_sp0_range RTA rta_art_facts Σ m ART0) as SP0R. pose proof (af_sp0_win RTA rta_art_facts Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0 in *.
  destruct (sm_pre Σ m 0%nat lo ART0 ltac:(right; left; reflexivity) LOW) as (_ & _ & _ & _ & _ & _ & _ & _ & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & _ & _ & HLO & _ & HD & HDL & HX & HXL & HT & HTL).
  set (usp := bv_unsigned sp) in *.
  assert (W1 : evt bsegs (frame_post ra sp gp (Z_to_bv 64 0x6abde8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dtv1_val [(usp - 176, usp)] lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x6abde8) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_tls_get_addr m)).
  { unfold entry_st.
    exact (tls_get_addr_p_spec ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             p (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te TI P0 PSP ltac:(ul) TGA TC TT HD HDL Hdb HX HXL HT HTL ST
             ltac:(ul) ltac:(ul) MI0). }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (asta_evt' RTA rta_art_facts Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  destruct (ASTA_unpack RTA Σ _ _ c1 Hc1) as (ms1 & PO & Hc1').
  unfold frame_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST').
  destruct (icpt_after RTA rta_art_facts Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; ul. }
  { intros i Hi. lia. }
  exists (Z_to_bv 64 dtv1_val).
  unfold icpt_postF. eapply (ASTA_conseq RTA); [exact Hc1'|]. intros ms <-.
  exists m'. split; [do 15 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES| exact I].
Qed.

End GWIN.
