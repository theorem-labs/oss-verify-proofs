(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TUB Require Import DgWalkB_u DgWalkB2_u.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DGB3.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.

Local Notation SP0 := (DgWalkB_u.SP0 sp).
Hypothesis BUFR : (4096 <= buf /\ buf + 21 <= 2^47)%Z.
Hypothesis SPR0 : (2^40 <= SP0 /\ SP0 + 8 <= 2^47)%Z.
Hypothesis KL : lenp = (kp + 4)%Z.
Hypothesis KS : (SP0 + 8 <= kp /\ kp + 8 <= 2^47)%Z.
Hypothesis KA : (kp mod 4 = 0)%Z.
Hypothesis SEP_B : (buf + 21 <= SP0 - 64 \/ SP0 + 8 <= buf)%Z.
Hypothesis SEP_BK : (buf + 21 <= kp \/ lenp + 4 <= buf)%Z.

Local Notation DG_W := (DgWalkB_u.DG_W sp buf lenp kp).
Local Notation dg_post := (DgWalkB_u.dg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf lenp kp).
Local Notation dg_mem := (DgWalkB_u.dg_mem ra sp s0 s1 s2 s3 s4 s5 s6 m0 buf lenp kp).
Local Notation L x := (x ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf lenp kp BUFR SPR0 KL KS KA SEP_B SEP_BK).
Local Notation dg_weed1 := (L DgWalkB_u.dg_weed1).
Local Notation dg_rw1_loop := (L DgWalkB_u.dg_rw1_loop).
Local Notation dg_l2exit := (L DgWalkB_u.dg_l2exit).
Local Notation dg_loop2 := (L DgWalkB2_u.dg_loop2).
Local Notation dg_rw1_entry := (L DgWalkB2_u.dg_rw1_entry).
Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DgWalkB_u.DG_W in MU.

Lemma dg_l1_k1 : forall (p1 len p2 D s Wp1 Ks : Z) s1' a0' a5' s2' s3' s4' s5' s6' (m : word -> option byte) (bs : list byte),
  dg_mem m len Ks bs -> (0 <= len <= 2)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (0 <= p1 < 10)%Z -> (0 <= p2 < 2 ^ s)%Z -> (2 <= D < 2 ^ 64)%Z ->
  (len = 0 -> p1 * 2 ^ s + p2 = Wp1 /\ D <= Wp1 /\ 8 <= p1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) (Z_to_bv 64 p2) (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) s1'
                                  a0' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 1) (Z_to_bv 64 1) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                                  (Z_to_bv 64 (2 ^ s - 1)) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 p1))
                              F (Z_to_bv 64 0x449ec) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KsR Hs Hp1 Hp2 HD Hinv.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).
  unfold DgWalkB_u.SP0 in *.
  assert (BODY : forall s2x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) (Z_to_bv 64 p2) (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) (Z_to_bv 64 p1)
              a0' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 1) (Z_to_bv 64 1) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
              s2x s3' s4' s5' s6' s7 s8 s9 s10 s11
              (Z_to_bv 64 (2 ^ s - 1)) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 p1))
         F (Z_to_bv 64 0x44a00) fc None m (seg_rom rsegs))).
  { intros s2x.
    do 2 zs1. zbf. do 3 zs1. zbf. do 4 zs1. zbf. do 5 zs1.
    if_cases Kx; [zify_cond Kx; ub_norm_in Kx; cbv in Kx; discriminate | ].
    zs1. zbf.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_store_ok rsegs mm buf bs len (Z_to_bv 64 (buf + len)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK end.
    zs1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 ?v))) _) =>
      replace (write_to_mem mm (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 v))) with (write_to_mem mm (wa (buf + len)) [Z_to_bv 8 v]) by (f_equal; symmetry; apply le1_lit);
      pose proof (u8arr_write rsegs mm buf bs len (Z_to_bv 8 v) BU ltac:(lia)) as BU'
    end.
    clear BU; store_done.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HM2 : dg_mem mm (len + 1) Ks (upd bs (Z.to_nat len) (Z_to_bv 8 (p1 + 48))))
        by (unfold DgWalkB_u.dg_mem; split; [exact ST|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact BU'|];
            split; [rewrite upd_length; exact BL|]; split; [exact LE | exact KC]) end.
    do 5 zs1.
    rewrite !Z.mul_1_r, !Z.sub_diag, !Z.shiftl_0_l, !Z.add_0_l.
    if_cases Kr; zify_cond Kr; ub_norm_in Kr.
    - eapply (dg_rw1_entry D p2 1 2 s (len + 1) Ks); [exact HM2 | lia | lia | lia | lia | lia | lia | lia].
    - do 5 zs1. zbf.
      do 3 zs1.
      eapply (dg_loop2 (Z.to_nat (17 - 0)) 0 p2 D s (len + 1) Ks); [reflexivity | exact HM2 | lia | lia | lia | lia | lia | rewrite Z.pow_0_r; lia]. }
  do 3 zs1. rewrite v_divuw_small by lia. rewrite Z.div_1_r.
  if_cases Kq; zify_cond Kq.
  - apply BODY.
  - do 2 zs1. zbf. apply BODY.
Qed.

Lemma dg_l1_k2 : forall (p1 len p2 D s Wp1 Ks : Z) s1' a0' a5' s2' s3' s4' s5' s6' (m : word -> option byte) (bs : list byte),
  dg_mem m len Ks bs -> (0 <= len <= 1)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (0 <= p1 < 100)%Z -> (0 <= p2 < 2 ^ s)%Z -> (2 <= D < 2 ^ 64)%Z ->
  (len = 0 -> p1 * 2 ^ s + p2 = Wp1 /\ D <= Wp1 /\ 8 <= p1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) (Z_to_bv 64 p2) (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) s1'
                                  a0' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 1) (Z_to_bv 64 10) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                                  (Z_to_bv 64 (2 ^ s - 1)) (Z_to_bv 64 3) (Z_to_bv 64 1) (Z_to_bv 64 p1))
                              F (Z_to_bv 64 0x449ec) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KsR Hs Hp1 Hp2 HD Hinv.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound p1 10 ltac:(lia)) as Hpm.
  assert (Hprod : (0 <= p1 mod 10 * 2 ^ s <= 9 * 2 ^ s)%Z) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
  unfold DgWalkB_u.SP0 in *.
  assert (BODY : forall s2x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) (Z_to_bv 64 p2) (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) (Z_to_bv 64 (p1 / 10))
              a0' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 1) (Z_to_bv 64 10) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
              s2x s3' s4' s5' s6' s7 s8 s9 s10 s11
              (Z_to_bv 64 (2 ^ s - 1)) (Z_to_bv 64 3) (Z_to_bv 64 1) (Z_to_bv 64 p1))
         F (Z_to_bv 64 0x44a00) fc None m (seg_rom rsegs))).
  { intros s2x.
    do 2 zs1. zbf. do 3 zs1. zbf. do 4 zs1. zbf. do 5 zs1.
    if_cases Kx; [zify_cond Kx; ub_norm_in Kx; cbv in Kx; discriminate | ].
    zs1. zbf.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_store_ok rsegs mm buf bs len (Z_to_bv 64 (buf + len)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK end.
    zs1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 ?v))) _) =>
      replace (write_to_mem mm (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 v))) with (write_to_mem mm (wa (buf + len)) [Z_to_bv 8 v]) by (f_equal; symmetry; apply le1_lit);
      pose proof (u8arr_write rsegs mm buf bs len (Z_to_bv 8 v) BU ltac:(lia)) as BU'
    end.
    clear BU; store_done.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HM2 : dg_mem mm (len + 1) Ks (upd bs (Z.to_nat len) (Z_to_bv 8 (p1 / 10 + 48))))
        by (unfold DgWalkB_u.dg_mem; split; [exact ST|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact BU'|];
            split; [rewrite upd_length; exact BL|]; split; [exact LE | exact KC]) end.
    do 5 zs1.
    replace (p1 - p1 / 10 * 10)%Z with (p1 mod 10)%Z by (rewrite (Z.mod_eq p1 10) by lia; ring).
    rewrite (Z.mod_small s 64) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    if_cases Kr; zify_cond Kr; ub_norm_in Kr.
    - eapply (dg_rw1_entry D (p1 mod 10 * 2 ^ s + p2) 10 3 s (len + 1) Ks); [exact HM2 | lia | lia | lia | lia | lia | lia | lia].
    - do 5 zs1. zbt.
      eapply (dg_l1_k1 (p1 mod 10) (len + 1) p2 D s Wp1 Ks); [exact HM2 | lia | lia | lia | lia | lia | lia | lia]. }
  do 3 zs1. rewrite v_divuw_small by lia.
  if_cases Kq; zify_cond Kq.
  - apply BODY.
  - do 2 zs1. if_cases Kz; zify_cond Kz.
    + destruct (Hinv ltac:(lia)) as (Hw & HDw & H8).
      assert (Hp1s : (0 <= p1 * 2 ^ s <= 9 * 2 ^ s)%Z) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
      do 5 zs1.
      replace (p1 - p1 / 10 * 10)%Z with (p1 mod 10)%Z by (rewrite (Z.mod_eq p1 10) by lia; ring).
      rewrite (Z.mod_small p1 10) by lia.
      rewrite (Z.mod_small s 64) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      if_cases Kr; zify_cond Kr; ub_norm_in Kr; [lia | ].
      do 5 zs1. zbt.
      eapply (dg_l1_k1 p1 len p2 D s Wp1 Ks); [exact HM0 | lia | lia | lia | lia | lia | lia | intros _; lia].
    + apply BODY.
Qed.

End DGB3.
