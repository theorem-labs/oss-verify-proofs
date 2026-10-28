(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ITree Nodes Decode SysStep ImageA RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import I_lkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s I_consts I_qck RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import I_memchrw I_lift F_memcmp I_memcmpw I_memcmp I_memcmp0.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_state RT_rep RT_facts RT_artfacts RT_icfacts R_isPoisoned RT_iclifts RT_cli RT_iclifts4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Section Lift0.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_CMP : forall Σ m, ART RT Σ m -> icells_cmp m /\ m2s_cells m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Theorem memcmp_zero_lift : memcmp_zero_icontract RT.
Proof using AF RIP AF_CMP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST -> ART0 MI0 CALL.
  intros T cf Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  set (p := bv_unsigned a0). set (q := bv_unsigned a1).
  assert (EA0 : a0 = Z_to_bv 64 p) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (EA1 : a1 = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range 64 a0) as PR. pose proof (bv_unsigned_in_range 64 a1) as QR.
  unfold bv_modulus in PR, QR. cbn in PR, QR. fold p in PR. fold q in QR.
  destruct (AF_CMP Σ m ART0) as (ICC & M2S).
  assert (W1 : evt asegs (cmp_post0 ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 4640 lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memcmp m)).
  { unfold entry_st, e_memcmp. rewrite ESP.
    pose proof (ibcmp0_spec RIP) as IB. unfold cmp_fn0 in IB.
    apply IB with (p := p) (q := q) (lo := lo); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul; try ul; try assumption. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & PO & Hc1').
  unfold cmp_post0 in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST').
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; ul. }
  { intros i Hi. lia. }
  unfold icpt_postF. eapply (ASTA_conseq RT); [exact Hc1'|]. intros ms <-.
  exists m'. split; [rewrite ESP; do 15 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES| exact I].
Qed.

End Lift0.

Theorem rta_memcmp_zero : memcmp_zero_icontract RTA.
Proof. exact (memcmp_zero_lift RTA rta_art_facts rip_proof rta_cmp). Qed.

End GWIN.
