(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ITree Nodes Decode SysStep ImageA RzCPS NodesA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import I_lkit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s I_consts I_qck RT_iface RT_state RT_rep RT_facts RT_artfacts RT_icfacts D_defs D_kit D_clx I_lift I_strncmpw I_strncmpw3 I_strncmp I_strncmp0w Fz_icpt0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section Lift0.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_SC : forall Σ m, ART RT Σ m -> icells_sc m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Theorem strncmp0_lift : strncmp0_icontract RT.
Proof using AF AF_SC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p1 p2 lo
    FDO MST -> -> -> ART0 MI0 CALL.
  intros T c Hc Hk.
  pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 p1)) as P1. pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 p2)) as P2.
  unfold bv_modulus in P1, P2. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul] in P1, P2.
  rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 p1)), <- (Z_to_bv_bv_unsigned (Z_to_bv 64 p2)) in Hc.
  set (q1 := bv_unsigned (Z_to_bv 64 p1)) in *. set (q2 := bv_unsigned (Z_to_bv 64 p2)) in *. clearbody q1 q2.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (AF_SC Σ m ART0) as ISC.
  assert (W1 : evt asegs (istrncmp_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q1) (Z_to_bv 64 q2) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_strncmp m)).
  { unfold entry_st, e_strncmp. rewrite ESP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lstep.
    apply istrncmp0_spec with (p1 := q1) (p2 := q2); try reflexivity; try assumption;
      rewrite ?(unsigned_lit usp) by ul; try ul; try assumption. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_post. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold istrncmp_post in PO.
  destruct PO as (u0 & u1 & u2 & b3 & b4 & b5 & b6 & b7 & b8 & b9 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST').
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]. injection E as <- <-. right; ul. }
  { intros i Hi. lia. }
  exists m'. split; [rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES| exact I].
Qed.
End Lift0.

(* [comment removed for export] *)
Theorem rta_strncmp0 : strncmp0_icontract RTA.
Proof. exact (strncmp0_lift RTA rta_art_facts (fun Σ m HA => rta_icells_sc Σ m HA)). Qed.
