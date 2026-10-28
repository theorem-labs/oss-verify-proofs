(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread I_consts I_qck I_lkit RT_iface D_defs D_kit D_clx I_read I_memcpyw I_lift RT_iface_pem I_memcmpw I_memcmp I_strcpy I_amemmove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Lemma mcmp_res_eq : forall b1 b2, mcmp_res b1 b2 = memcmp_res b1 b2.
Proof. induction b1 as [|x r IH]; intros [|y r2]; cbn; reflexivity. Qed.

Section LiftPem.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_M2S : forall Σ m, ART RT Σ m -> m2s_cells m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis AF_MC : forall Σ m, ART RT Σ m -> icells_mcmp m.
Hypothesis AF_SC : forall Σ m, ART RT Σ m -> icells_scpy m.
Hypothesis AF_ICM : forall Σ m, ART RT Σ m -> icells m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Theorem memcmp_lift : memcmp_icontract RT.
Proof using AF RIP AF_M2S AF_SHW AF_MC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p1 p2 b1 b2 lo
    FDO MST -> -> -> HL NB P1 P2 B1 B2 CSRC1 CSRC2 ART0 MI0 CALL.
  intros T c Hc Hk.
  set (n := Z.of_nat (length b1)) in *.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (AF_M2S Σ m ART0) as M2S.
  pose proof (AF_MC Σ m ART0) as IMC.
  destruct CSRC1 as (CS1 & SEP1). destruct CSRC2 as (CS2 & SEP2).
  assert (CH1 : chk_ok m p1 n) by (apply (chk_ok_of RT AF_SHW Σ m p1 n ART0); [lia| exact CS1]).
  assert (CH2 : chk_ok m p2 n) by (apply (chk_ok_of RT AF_SHW Σ m p2 n ART0); [lia| exact CS2]).
  assert (R1 : p1 + n <= 2^47).
  { destruct (Z.eq_dec n 0) as [E|NE]; [lia|]. destruct CH1 as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (R2 : p2 + n <= 2^47).
  { destruct (Z.eq_dec n 0) as [E|NE]; [lia|]. destruct CH2 as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (W1 : evt asegs (frame_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (mcmp_res b1 b2)
                            [(bv_unsigned (Z_to_bv 64 usp) - 4560, bv_unsigned (Z_to_bv 64 usp))] lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memcmp m)).
  { unfold entry_st, e_memcmp. rewrite ESP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lstep.
    pose proof (ibcmp_spec RIP) as IB. unfold real_cmp_stmt in IB.
    pose proof (IB ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p1 p2 b1 b2 lo
                  eq_refl eq_refl eq_refl) as IB2.
    rewrite (unsigned_lit usp) in IB2 by ul.
    apply IB2; try ul; try assumption.
    unfold cmp_pre. fold n. repeat (split; [first [assumption | lia | ul]|]). exact IMC. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_post. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold frame_post in PO.
  destruct PO as (u0 & u1 & u2 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST').
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; ul. }
  { intros i Hi. lia. }
  exists m'. split; [rewrite ESP, <- mcmp_res_eq; do 16 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES| exact I].
Qed.

Theorem strcpy_lift : strcpy_icontract RT.
Proof using AF RIP AF_M2S AF_SHW AF_SC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s str slack lo
    FDO MST -> -> SRC NZ LH SLK S0 D0 SEPS CSRC CDST OV ART0 MI0 CALL.
  intros T c Hc Hk.
  set (len := Z.of_nat (length str)) in *.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (AF_M2S Σ m ART0) as M2S. pose proof (AF_SC Σ m ART0) as ISC.
  destruct CSRC as (CS & _). destruct CDST as (CD & DCL & DWR).
  assert (CHS : chk_ok m s (len + 1)) by (apply (chk_ok_of RT AF_SHW Σ m s _ ART0); [lia| exact CS]).
  assert (CHD : chk_ok m d (len + 1)) by (apply (chk_ok_of RT AF_SHW Σ m d _ ART0); [lia| exact CD]).
  destruct (wr_at_rw_CB m d (len + 1) DWR ltac:(lia)) as (junk & DST).
  replace (Z.to_nat (len + 1)) with (S (length str)) in DST by lia.
  assert (SEPD : d + len + 1 <= lo \/ usp <= d).
  { destruct (range_side d (len + 1) lo usp); [| ul| lia| right; lia| left; lia].
    intros i Hi. destruct (aclient_split RT AF Σ m usp (d + i) ART0 (DCL i Hi)); [left; lia| right; ul]. }
  assert (RS : s + len + 1 + 8 <= 2^47).
  { destruct CHS as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (RD : d + len + 1 <= 2^47).
  { destruct CHD as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  (* [comment removed for export] *)
  set (k := (- (s + len + 1)) mod 8) in *.
  assert (K7 : 0 <= k < 8) by (unfold k; apply Z.mod_pos_bound; lia).
  set (slack' := firstn (Z.to_nat k) slack).
  assert (LS' : Z.of_nat (length slack') = k) by (unfold slack'; rewrite length_firstn; lia).
  assert (SRC' : bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack')).
  { assert (E : str ++ Z_to_bv 8 0 :: slack = (str ++ Z_to_bv 8 0 :: slack') ++ skipn (Z.to_nat k) slack)
      by (rewrite <- app_assoc; cbn [app]; unfold slack'; rewrite firstn_skipn; reflexivity).
    rewrite E in SRC. apply bytes_at_app in SRC. exact (proj1 SRC). }
  assert (W1 : evt asegs (istrcpy_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d str lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_strcpy m)).
  { unfold entry_st, e_strcpy. rewrite ESP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lstep.
    apply (istrcpy_spec RIP) with (s := s) (slack := slack') (junk := junk); try reflexivity; fold len; rewrite ?LS', ?(unsigned_lit usp) by ul;
      try ul; try assumption; fold k; try lia. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_post. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold istrcpy_post in PO.
  destruct PO as (u0 & u1 & u2 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & DC).
  rewrite (unsigned_lit usp) in MU, ST' by ul. fold len in MU.
  destruct (icpt_after RT AF Σ m m' usp lo _ d (len + 1) ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; [left; lia| right; ul]. }
  { intros i Hi. apply DCL. exact Hi. }
  exists m'. split; [rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES|].
  destruct DC as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB.
Qed.

Lemma rng_class_sub : forall Σ s n s' n', rng_class RT Σ s n -> s <= s' -> s' + n' <= s + n -> rng_class RT Σ s' n'.
Proof.
  intros Σ s n s' n' [(p & k & Hin & H1 & H2)|[(f & k & Hin & H1 & H2)|[(H1 & H2)|(H1 & H2)]]] L1 L2.
  - left. exists p, k. split; [exact Hin| lia].
  - right. left. exists f, k. split; [exact Hin| lia].
  - right. right. left. lia.
  - right. right. right. lia.
Qed.

Theorem asan_memmove_lift : memmove_icontract RT e_asan_memmove.
Proof using AF RIP AF_M2S AF_SHW AF_ICM.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d off n blk lo
    FDO MST -> -> -> D0 O0 N0 ON LB BLK CSRC CDST ART0 MI0 CALL.
  intros T c Hc Hk.
  set (L := Z.of_nat (length blk)) in *.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (AF_M2S Σ m ART0) as M2S. pose proof (AF_ICM Σ m ART0) as ICM.
  destruct CSRC as (CS & _). destruct CDST as (CD & DCL & DWR).
  destruct (CD ltac:(lia)) as (ACH & RCH).
  assert (CHS : chk_ok m (d + off) n) by (apply (chk_ok_of RT AF_SHW Σ m _ n ART0); [lia| exact CS]).
  assert (CHD : chk_ok m d n).
  { apply (chk_ok_of RT AF_SHW Σ m d n ART0); [lia|]. intros Hn. split.
    - intros i Hi. apply ACH. lia.
    - apply (rng_class_sub Σ d L d n RCH); lia. }
  assert (SEPD : d + L <= lo \/ usp <= d).
  { destruct (range_side d L lo usp); [| ul| lia| right; lia| left; lia].
    intros i Hi. destruct (aclient_split RT AF Σ m usp (d + i) ART0 (DCL i Hi)); [left; lia| right; ul]. }
  assert (RD : d + L <= 2^47).
  { destruct (AF_SHW Σ m d L ART0 ltac:(lia) RCH) as (_ & RIM).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (BLKC : rw_cells asegs m d [CB (length blk) blk]).
  { split; [split; [cbn; split; [reflexivity| exact I]|]; cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BLK|].
    cbn [cells_size csize]. rewrite Nat.add_0_r. exact DWR. }
  assert (W1 : evt asegs (amemmove_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d off n blk lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 (d + off)) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_asan_memmove m)).
  { unfold entry_st, e_asan_memmove. rewrite ESP.
    apply (amemmove_spec RIP); try reflexivity; fold L; rewrite ?(unsigned_lit usp) by ul; try ul; try assumption; try lia. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_post. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold amemmove_post in PO.
  destruct PO as (u0 & u1 & u2 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & DC).
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ d L ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; [left; lia| right; ul]. }
  { intros i Hi. apply DCL. exact Hi. }
  exists m'. split; [rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES|].
  destruct DC as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB.
Qed.

End LiftPem.
