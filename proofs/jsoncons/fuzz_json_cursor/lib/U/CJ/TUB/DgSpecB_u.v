(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TUB Require Import DgWalkB_u DgWalkB2_u DgL1B_u.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DGB4.
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
Local Notation dg_l1_k2 := (L DgL1B_u.dg_l1_k2).
Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DgWalkB_u.DG_W in MU.

Lemma dg_l1_k3 : forall (p1 len p2 D s Wp1 Ks : Z) s1' a0' a5' s2' s3' s4' s5' s6' (m : word -> option byte) (bs : list byte),
  dg_mem m len Ks bs -> (0 <= len <= 0)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (0 <= p1 < 256)%Z -> (0 <= p2 < 2 ^ s)%Z -> (2 <= D < 2 ^ 64)%Z ->
  (len = 0 -> p1 * 2 ^ s + p2 = Wp1 /\ D <= Wp1 /\ 8 <= p1)%Z -> (p1 * 2 ^ s + p2 < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) (Z_to_bv 64 p2) (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) s1'
                                  a0' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 1) (Z_to_bv 64 100) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                                  (Z_to_bv 64 (2 ^ s - 1)) (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 p1))
                              F (Z_to_bv 64 0x449ec) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KsR Hs Hp1 Hp2 HD Hinv HX.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound p1 100 ltac:(lia)) as Hpm.
  assert (Hprod : (0 <= p1 mod 100 * 2 ^ s <= p1 * 2 ^ s)%Z)
    by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; [lia | apply Z.mod_le; lia]]).
  unfold DgWalkB_u.SP0 in *.
  do 3 zs1. rewrite v_divuw_small by lia.
  if_cases Kq; zify_cond Kq.
  - do 2 zs1. zbf. do 3 zs1. zbf. do 4 zs1. zbf. do 5 zs1.
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
      assert (HM2 : dg_mem mm (len + 1) Ks (upd bs (Z.to_nat len) (Z_to_bv 8 (p1 / 100 + 48))))
        by (unfold DgWalkB_u.dg_mem; split; [exact ST|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact BU'|];
            split; [rewrite upd_length; exact BL|]; split; [exact LE | exact KC]) end.
    do 5 zs1.
    replace (p1 - p1 / 100 * 100)%Z with (p1 mod 100)%Z by (rewrite (Z.mod_eq p1 100) by lia; ring).
    rewrite (Z.mod_small s 64) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    if_cases Kr; zify_cond Kr; ub_norm_in Kr.
    + eapply (dg_rw1_entry D (p1 mod 100 * 2 ^ s + p2) 100 4 s (len + 1) Ks); [exact HM2 | lia | lia | lia | lia | lia | lia | lia].
    + do 5 zs1. zbt.
      eapply (dg_l1_k2 (p1 mod 100) (len + 1) p2 D s Wp1 Ks); [exact HM2 | lia | lia | lia | lia | lia | lia | lia].
  - do 2 zs1. zbt.
    destruct (Hinv ltac:(lia)) as (Hw & HDw & H8).
    do 5 zs1.
    replace (p1 - p1 / 100 * 100)%Z with (p1 mod 100)%Z by (rewrite (Z.mod_eq p1 100) by lia; ring).
    rewrite (Z.mod_small p1 100) by lia.
    rewrite (Z.mod_small s 64) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    if_cases Kr; zify_cond Kr; ub_norm_in Kr; [lia | ].
    do 5 zs1. zbt.
    eapply (dg_l1_k2 p1 len p2 D s Wp1 Ks); [exact HM0 | lia | lia | lia | lia | lia | lia | intros _; lia].
Qed.

Lemma swrap32_neg : forall s, (0 < s <= 2 ^ 31)%Z -> bv_swrap 32 (4294967296 - s + 0) = (- s)%Z.
Proof.
  intros s H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  replace (4294967296 - s + 0 + 2 ^ 31)%Z with ((2 ^ 31 - s) + 1 * 2 ^ 32)%Z by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma negmod64 : forall s, (0 < s < 2 ^ 64)%Z -> ((- s) mod 18446744073709551616 = 18446744073709551616 - s)%Z.
Proof. intros s H. rewrite <- (Z.mod_add (- s) 1) by lia. rewrite Z.mod_small by lia. lia. Qed.
Lemma swrap32_sub64 : forall s, (- 2 ^ 31 <= s < 2 ^ 31)%Z -> bv_swrap 32 (s - 18446744073709551616) = s.
Proof.
  intros s H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  replace (s - 18446744073709551616 + 2 ^ 31)%Z with ((s + 2 ^ 31) + (- 4294967296) * 2 ^ 32)%Z by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma zbv_sub64 : forall x, Z_to_bv 64 (x - 18446744073709551616) = Z_to_bv 64 x.
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  replace (x - 18446744073709551616)%Z with (x + (-1) * 18446744073709551616)%Z by lia. apply Z.mod_add. lia.
Qed.

Lemma dg_spec : forall t0 t1 t2 t3 t4 t5 t6 (m : word -> option byte) (Wm dW dP s Ks : Z) (bs : list byte) lj,
  (56 <= s <= 59)%Z -> (1 <= Wm)%Z -> (0 <= dW)%Z -> (0 <= dP)%Z -> (Wm + dW + dP <= 2 ^ 64 - 2)%Z -> (2 ^ 62 <= Wm + dW + dP + 1)%Z ->
  (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  stk rsegs m (SP0 - 64) SP0 -> rw_cells rsegs m SP0 [C8 (Z_to_bv 64 kp)] ->
  u8arr rsegs m buf bs -> length bs = 21%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 (Z_to_bv 64 Ks)] ->
  mem_inv rsegs m -> m = m0 ->
  evt rsegs (dg_post Ks) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Wm) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 (Wm + dW)) (Z_to_bv 64 (2 ^ 32 - s))
                                  (Z_to_bv 64 (Wm + dW + dP)) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x44940) fc None m (seg_rom rsegs)).
Proof using All.
  intros until lj. intros Hs HWm HdW HdP Hsum HWp HKs ST KPc BU BL LE KC MI ->.
  pose proof (munch_refl DG_W m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).
  unfold DgWalkB_u.DG_W in MU. unfold DgWalkB_u.SP0 in *.
  carve_frame 64%nat ST.
  do 12 zs1. zbf. zs1. zbf. do 2 zs1. zbf. zs1. zbf. do 3 zs1.
  rewrite ?(swrap32_neg s) by lia.
  rewrite ?(negmod64 s) by lia.
  replace (0 - (18446744073709551616 - s))%Z with (s - 18446744073709551616)%Z by lia.
  rewrite ?(swrap32_sub64 s) by lia.
  if_cases Kng; [zify_cond Kng; rewrite <- (Z.mod_add (s - 18446744073709551616) 1) in Kng by lia; rewrite Z.mod_small in Kng by lia; lia | ].
  rewrite zbv_sub64.
  do 3 zs1. zbf. zs1. zbf. do 2 zs1. zbf. do 18 zs1.
  replace (0 <? buf)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  rewrite (Z.mod_small s 64) by lia.
  rewrite Z.shiftl_1_l. rewrite (Z.mod_small (2 ^ s + -1)) by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (Z.land (2 ^ s + -1) (Wm + dW + dP + 1)) with ((Wm + dW + dP + 1) mod 2 ^ s)%Z
    by (rewrite Z.land_comm; replace (2 ^ s + -1)%Z with (Z.ones s) by (rewrite Z.ones_equiv; lia); rewrite Z.land_ones by lia; reflexivity).
  replace (Z_to_bv 64 (bv_unsigned sp + -64)) with (Z_to_bv 64 (bv_unsigned sp - 64)) by (f_equal; lia).
  replace (2 ^ s + -1)%Z with (2 ^ s - 1)%Z by lia.
  set (Wp1 := (Wm + dW + dP + 1)%Z).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HM : dg_mem mm 0 Ks bs) by
      (unfold DgWalkB_u.dg_mem, DgWalkB_u.DG_W, DgWalkB_u.SP0; replace (bv_unsigned sp - 64)%Z with (bv_unsigned sp + -64)%Z by lia;
       split; [exact ST|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact BU|];
       split; [exact BL|]; split; [exact LE | exact KC]) end.
  pose proof (Z.div_mod Wp1 (2 ^ s) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound Wp1 (2 ^ s) ltac:(lia)) as MB.
  assert (P1lo : (8 <= Wp1 / 2 ^ s)%Z).
  { apply Z.div_le_lower_bound; [lia|]. assert (8 * 2 ^ s <= 8 * 2 ^ 59)%Z by lia. lia. }
  assert (P1hi : (Wp1 / 2 ^ s < 256)%Z) by (apply Z.div_lt_upper_bound; lia).
  eapply (dg_l1_k3 (Wp1 / 2 ^ s) 0 (Wp1 mod 2 ^ s) (Wm + dW + dP - Wm + 2) s Wp1 Ks); [exact HM | lia | lia | lia | lia | lia | lia | | lia].
  intros _. split; [lia | split; lia].
Qed.

End DGB4.
