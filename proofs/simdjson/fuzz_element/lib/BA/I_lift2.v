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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s I_consts I_qck RT_iface D_defs D_kit D_clx. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import I_memcpyw I_memsetw I_memchrw I_strnlenw I_read I_lift I_strlenw I_strlen I_amemsetw I_amemcpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section Lift2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_IC : forall Σ m, ART RT Σ m -> icells m /\ icells_ms m /\ icells_mc m /\ icells_sn m /\ m2s_cells m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis AF_SL : forall Σ m, ART RT Σ m -> icells_sl m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Theorem strlen_lift : strlen_icontract RT.
Proof using AF RIP AF_IC AF_SHW AF_SL.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s str slack lo
    FDO MST -> BUF NZ L40 PAD S0 SEPB CSRC ART0 MI0 CALL.
  intros T cf Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_IC Σ m ART0) as (_ & _ & _ & ICS & M2S).
  pose proof (AF_SL Σ m ART0) as ISL.
  destruct CSRC as (CS & SEPS).
  assert (CHS : chk_ok m s (Z.of_nat (length str) + 1)) by (apply (chk_ok_of RT AF_SHW Σ m s _ ART0); [lia| exact CS]).
  assert (RS : s + Z.of_nat (length str) + 1 <= 2^47).
  { destruct CHS as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (W1 : evt asegs (istrlen_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.of_nat (length str)) lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_strlen m)).
  { unfold entry_st, e_strlen. rewrite ESP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lstep.
    apply (istrlen_spec RIP) with (s := s) (slack := slack); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul;
      try ul; try assumption. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_postF. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold istrlen_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST').
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; ul. }
  { intros i Hi. lia. }
  exists m'. split; [rewrite ESP; do 15 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES| exact I].
Qed.

Theorem asan_memset_lift : memset_icontract RT e_asan_memset.
Proof using AF RIP AF_IC AF_SHW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n c lo
    FDO MST -> -> -> D0 N0 CDST ART0 MI0 CALL.
  intros T cf Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_IC Σ m ART0) as (_ & ICS & _ & _ & M2S).
  destruct CDST as (CD & DCL & DWR).
  assert (CHD : chk_ok m d n) by (apply (chk_ok_of RT AF_SHW Σ m d n ART0); [lia| exact CD]).
  destruct (wr_at_rw_CB m d n DWR ltac:(lia)) as (junk & DST).
  assert (SEPD : n = 0 \/ d + n <= lo \/ usp <= d).
  { destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right].
    destruct (range_side d n lo usp); [| ul| lia| right; lia| left; lia].
    intros i Hi. destruct (aclient_split RT AF Σ m usp (d + i) ART0 (DCL i Hi)); [left; lia| right; ul]. }
  assert (RD : d + n <= 2^47).
  { destruct (Z.eq_dec n 0) as [E|NE]; [lia|]. destruct CHD as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  pose proof (bv_unsigned_in_range 8 c) as CR. unfold bv_modulus in CR. change (2 ^ Z.of_N 8) with 256 in CR.
  assert (W1 : evt asegs (amemset_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d (bv_unsigned c) n lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 (bv_unsigned c)) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_asan_memset m)).
  { unfold entry_st, e_asan_memset. rewrite ESP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    apply (amemset_spec RIP) with (junk := junk); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul; try ul;
      try assumption. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_postF. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold amemset_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & DC).
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ d n ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; [left; lia| right; ul]. }
  { intros i Hi. apply DCL. exact Hi. }
  exists m'. split; [rewrite ESP; do 15 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES|].
  rewrite byte_mod_id in DC.
  destruct DC as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB.
Qed.

Theorem asan_memcpy_lift : memcpy_icontract RT e_asan_memcpy.
Proof using AF RIP AF_IC AF_SHW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s bs lo
    FDO MST -> -> -> D0 S0 NB BS CSRC CDST OV ART0 MI0 CALL.
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
  destruct (wr_at_rw_CB m d n DWR ltac:(lia)) as (junk & DST).
  unfold n in DST. rewrite Nat2Z.id in DST.
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
  assert (W1 : evt asegs (amemcpy_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d s bs lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_asan_memcpy m)).
  { unfold entry_st, e_asan_memcpy. rewrite ESP.
    apply (amemcpy_spec RIP) with (junk := junk); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul; try ul;
      try assumption. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_postF. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold amemcpy_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & DC & SC).
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ d n ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; [left; lia| right; ul]. }
  { intros i Hi. apply DCL. exact Hi. }
  exists m'. split; [rewrite ESP; do 15 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES|].
  destruct DC as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB.
Qed.

End Lift2.
