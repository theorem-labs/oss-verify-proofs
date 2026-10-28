(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes Decode SysStep ImageA RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import I_lkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_small R_m2s I_consts I_qck RT_iface D_defs D_kit D_clx I_memcpyw I_memsetw I_memchrw I_strnlenw I_read I_lift I_strlenw I_strlen I_amemsetw I_amemcpy I_ammovew I_ammove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section Lift3.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_IC : forall Σ m, ART RT Σ m -> icells m /\ icells_ms m /\ icells_mc m /\ icells_sn m /\ m2s_cells m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Theorem asan_memmove_lift : memmove_icontract RT.
Proof using AF RIP AF_IC AF_SHW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s bs lo
    FDO MST -> -> -> D0 S0 NB BS CSRC CDST ART0 MI0 CALL.
  intros T c Hc Hk.
  set (n := Z.of_nat (length bs)) in *.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_IC Σ m ART0) as (IC & _ & _ & _ & M2S).
  destruct CSRC as (CS & SEPS). destruct CDST as (CD & DCL & DWR).
  assert (CHS : chk_ok m s n) by (apply (chk_ok_of RT AF_SHW Σ m s n ART0); [lia| exact CS]).
  assert (CHD : chk_ok m d n) by (apply (chk_ok_of RT AF_SHW Σ m d n ART0); [lia| exact CD]).
  assert (SEPD : n = 0 \/ d + n <= lo \/ usp <= d).
  { destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right].
    destruct (range_side d n lo usp); [| ul| lia| right; lia| left; lia].
    intros i Hi. destruct (aclient_split RT AF Σ m usp (d + i) ART0 (DCL i Hi)); [left; lia| right; ul]. }
  assert (RS : n = 0 \/ s + n <= 2^47).
  { destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CHS as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (RD : n = 0 \/ d + n <= 2^47).
  { destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CHD as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (W1 : evt bsegs (ammove_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d bs lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_asan_memmove m)).
  { unfold entry_st, e_asan_memmove. rewrite ESP.
    apply (ammove_spec RIP) with (s := s); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul; try ul;
      try assumption. }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_postF. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold ammove_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & DC).
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ d n ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; [left; lia| right; ul]. }
  { intros i Hi. apply DCL. exact Hi. }
  exists m'. split; [rewrite ESP; do 15 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES|].
  exact DC.
Qed.

End Lift3.
