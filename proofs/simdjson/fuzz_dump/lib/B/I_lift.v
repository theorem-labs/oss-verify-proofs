(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s I_consts I_qck I_lkit RT_iface D_defs D_kit D_clx I_read I_memcpyw I_memcpy I_memsetw I_memchrw I_strnlenw I_strnlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Lemma range_side : forall d n lo usp, (forall i, 0 <= i < n -> usp <= d + i \/ d + i < lo) -> lo < usp -> 0 < n ->
  usp <= d \/ d + n <= lo.
Proof.
  intros d n lo usp H Hlu Hn. destruct (Z_le_gt_dec usp d) as [L|L]; [left; exact L| right].
  destruct (H 0 ltac:(lia)) as [E|E]; [lia|].
  destruct (Z_le_gt_dec (d + n) lo) as [L2|L2]; [exact L2|].
  destruct (H (lo - d) ltac:(lia)) as [E2|E2]; lia.
Qed.

Section Lift.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_IC : forall Σ m, ART RT Σ m -> icells m /\ icells_ms m /\ icells_mc m /\ icells_sn m /\ m2s_cells m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Lemma PMc_mat_stable : forall Σ PMc, mat_stable PMc -> mat_stable (fun mo => ARTM RT Σ mo /\ PMc mo).
Proof using AF. intros Σ PMc H. apply mat_stable_and; [exact (af_mat_stable RT AF Σ)| exact H]. Qed.

Lemma asta_evt' : forall Σ PMc Pm Q, mat_stable PMc -> (forall ms, Pm ms -> evt bsegs Q ms) ->
  cps bsegs (ASTA RT Σ PMc Pm) (ASTA RT Σ PMc Q).
Proof using AF.
  intros Σ PMc Pm Q HM H. unfold ASTA.
  apply (ast_evt bsegs SEGTOP_A asegs_wx asegs_below); [apply PMc_mat_stable; exact HM| exact H].
Qed.

Lemma chk_ok_of : forall Σ m p n, ART RT Σ m -> 0 <= n <= 2^40 -> (0 < n -> acc bsegs m p n /\ rng_class RT Σ p n) ->
  chk_ok m p n.
Proof using AF_SHW.
  intros Σ m p n ART0 Hn H. destruct (Z.eq_dec n 0) as [->|NZ].
  - split; [intros i Hi; lia| split; [intros Hc; lia| intros Hc; lia]].
  - destruct (H ltac:(lia)) as (AC & RC). destruct (AF_SHW Σ m p n ART0 ltac:(lia) RC) as (QW & RIM).
    split; [exact AC| split; [exact QW| intros _; split; [exact RIM| lia]]].
Qed.

Lemma icpt_after : forall Σ m m' usp lo (W : list (Z * Z)) d n,
  ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo <= usp -> usp <= USTACK_TOP ->
  munch W m m' -> wmono bsegs m m' ->
  (forall x, in_ranges W x -> (d <= x < d + n) \/ (lo <= x < usp)) ->
  (forall i, 0 <= i < n -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp (d + i)) ->
  ART RT Σ m' /\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) usp d n m m'.
Proof using AF.
  intros Σ m m' usp lo W d n ART0 L1 L2 L3 MU WM HW HD. split.
  - apply (af_frame RT AF Σ m m' lo ART0 L1); [| exact WM].
    intros a Ha. apply MU. apply outside_of_not_in_ranges'. intros Hin. destruct (HW _ Hin) as [Hd|Hs].
    + apply Ha. assert (E : bv_unsigned a = d + (bv_unsigned a - d)) by lia. rewrite E.
      specialize (HD (bv_unsigned a - d) ltac:(lia)).
      destruct HD as [H|[H|[H|[H|H]]]]; [left; lia| right; left; exact H| right; right; left; exact H
                                          | right; right; right; left; exact H| right; right; right; right; exact H].
    + apply Ha. left. ul.
  - intros a Ha Hout. apply MU. apply outside_of_not_in_ranges'. intros Hin. destruct (HW _ Hin) as [Hd|Hs]; [exact (Hout Hd)|].
    destruct (aclient_split RT AF Σ m usp _ ART0 Ha); ul.
Qed.

Theorem memcpy_lift : memcpy_icontract RT e_memcpy.
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
  assert (CHS : chk_ok m s n) by (apply (chk_ok_of Σ m s n ART0); [lia| exact CS]).
  assert (CHD : chk_ok m d n) by (apply (chk_ok_of Σ m d n ART0); [lia| exact CD]).
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
  assert (W1 : evt bsegs (imemcpy_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d s bs lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memcpy m)).
  { unfold entry_st, e_memcpy. rewrite ESP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    lstep.
    apply (imemcpy_spec RIP) with (junk := junk); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul; try ul;
      try assumption. }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt' Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_postF. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold imemcpy_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & DC & SC).
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after Σ m m' usp lo _ d n ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; [left; lia| right; ul]. }
  { intros i Hi. apply DCL. exact Hi. }
  exists m'. split; [rewrite ESP; do 15 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES|].
  destruct DC as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB.
Qed.

Lemma byte_mod_id : forall c : byte, Z_to_bv 8 (bv_unsigned c mod 256) = c.
Proof.
  intros c. pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  rewrite Z.mod_small by lia. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Theorem memset_lift : memset_icontract RT e_memset.
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
  assert (CHD : chk_ok m d n) by (apply (chk_ok_of Σ m d n ART0); [lia| exact CD]).
  destruct (wr_at_rw_CB m d n DWR ltac:(lia)) as (junk & DST).
  assert (SEPD : n = 0 \/ d + n <= lo \/ usp <= d).
  { destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right].
    destruct (range_side d n lo usp); [| ul| lia| right; lia| left; lia].
    intros i Hi. destruct (aclient_split RT AF Σ m usp (d + i) ART0 (DCL i Hi)); [left; lia| right; ul]. }
  assert (RD : d + n <= 2^47).
  { destruct (Z.eq_dec n 0) as [E|NE]; [lia|]. destruct CHD as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  pose proof (bv_unsigned_in_range 8 c) as CR. unfold bv_modulus in CR. change (2 ^ Z.of_N 8) with 256 in CR.
  assert (W1 : evt bsegs (imemset_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d (bv_unsigned c) n lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 (bv_unsigned c)) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memset m)).
  { unfold entry_st, e_memset. rewrite ESP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    lstep.
    apply (imemset_spec RIP) with (junk := junk); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul; try ul;
      try assumption. }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (asta_evt' Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_postF. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold imemset_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & DC).
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after Σ m m' usp lo _ d n ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; [left; lia| right; ul]. }
  { intros i Hi. apply DCL. exact Hi. }
  exists m'. split; [rewrite ESP; do 15 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES|].
  rewrite byte_mod_id in DC.
  destruct DC as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB.
Qed.

Theorem memchr_lift : memchr_icontract RT.
Proof using AF RIP AF_IC AF_SHW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s cz n buf lo
    FDO MST -> -> -> S0 HC N0 BUF OK SEPB CSRC ART0 MI0 CALL.
  intros T cf Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_IC Σ m ART0) as (_ & _ & ICM & _ & M2S).
  destruct CSRC as (CS & SEPS).
  assert (CHB : 0 <= memchr_chk cz n buf <= n).
  { unfold memchr_chk. destruct (find_byte cz (firstn (Z.to_nat n) buf)) as [i|] eqn:FB; [| lia].
    destruct (find_byte_Some _ _ _ FB) as (Hi & _). rewrite length_firstn in Hi. lia. }
  assert (CHS : chk_ok m s (memchr_chk cz n buf)) by (apply (chk_ok_of Σ m s _ ART0); [lia| exact CS]).
  assert (RS : s + memchr_chk cz n buf <= 2^47).
  { destruct (Z.eq_dec (memchr_chk cz n buf) 0) as [E|NE]; [lia|]. destruct CHS as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (W1 : evt bsegs (imemchr_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memchr_res s cz n buf) lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 cz) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memchr m)).
  { unfold entry_st, e_memchr. rewrite ESP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    lstep.
    apply (imemchr_spec RIP); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul; try ul; try assumption. }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (asta_evt' Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_postF. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold imemchr_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST').
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; ul. }
  { intros i Hi. lia. }
  exists m'. split; [rewrite ESP; do 15 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES| exact I].
Qed.

Theorem strnlen_lift : strnlen_icontract RT.
Proof using AF RIP AF_IC AF_SHW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s n buf lo
    FDO MST -> -> S0 N0 BUF OK SEPB CSRC ART0 MI0 CALL.
  intros T cf Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_IC Σ m ART0) as (_ & _ & _ & ICS & M2S).
  destruct CSRC as (CS & SEPS).
  assert (CHB : 0 <= strnlen_chk n buf <= n).
  { unfold strnlen_chk, memchr_chk. destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:FB; [| lia].
    destruct (find_byte_Some _ _ _ FB) as (Hi & _). rewrite length_firstn in Hi. lia. }
  assert (CHS : chk_ok m s (strnlen_chk n buf)) by (apply (chk_ok_of Σ m s _ ART0); [lia| exact CS]).
  assert (RS : s + strnlen_chk n buf <= 2^47).
  { destruct (Z.eq_dec (strnlen_chk n buf) 0) as [E|NE]; [lia|]. destruct CHS as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (W1 : evt bsegs (istrnlen_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (strnlen_res n buf) lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_strnlen m)).
  { unfold entry_st, e_strnlen. rewrite ESP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    lstep.
    apply (istrnlen_spec RIP) with (s := s); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul; try ul; try assumption. }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (asta_evt' Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_postF. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold istrnlen_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST').
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; ul. }
  { intros i Hi. lia. }
  exists m'. split; [rewrite ESP; do 15 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES| exact I].
Qed.

End Lift.
