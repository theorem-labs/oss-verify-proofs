(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TUB Require Import DgWalkB_u.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DGB2.
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
Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DgWalkB_u.DG_W in MU.

Lemma dg_loop2 : forall (n : nat) (i p2 D s len Ks : Z) s0' s1' a0' a4' s2' s3' s4' s5' s6' t4' (m : word -> option byte) (bs : list byte),
  Z.to_nat (17 - i) = n ->
  dg_mem m len Ks bs -> (1 <= len <= 3 + i)%Z -> (0 <= i <= 17)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (D <= p2 < 2 ^ s)%Z -> (2 * 10 ^ i <= D)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) (Z_to_bv 64 p2) s0' s1'
                                  a0' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 1) a4' (Z_to_bv 64 (10 ^ i)) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                                  (Z_to_bv 64 (2 ^ s - 1)) t4' (Z_to_bv 64 10) (Z_to_bv 64 (- i)))
                              F (Z_to_bv 64 0x44a74) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros i p2 D s len Ks s0' s1' a0' a4' s2' s3' s4' s5' s6' t4' m bs Hn HM LR IR KsR Hs HP HD.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).
  assert (H10 : (1 <= 10 ^ i < 2 ^ 58)%Z) by (pose proof (Z.pow_pos_nonneg 10 i ltac:(lia) ltac:(lia)); lia).
  set (dd := ((p2 * 10) ≫ (s mod 64))%Z).
  assert (Hdd : (0 <= dd < 10)%Z).
  { unfold dd. rewrite (Z.mod_small s 64) by lia. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (BODY : forall a1x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) (Z_to_bv 64 (p2 * 10)) (Z_to_bv 64 dd) (Z_to_bv 64 dd)
              a0' a1x (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 1) (Z_to_bv 64 (10 ^ i)) (Z_to_bv 64 (10 ^ i)) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
              s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
              (Z_to_bv 64 (2 ^ s - 1)) (Z_to_bv 64 D) (Z_to_bv 64 10) (Z_to_bv 64 (- i)))
         F (Z_to_bv 64 0x44a94) fc None m (seg_rom rsegs))).
  { intros a1x.
    do 2 zs1. zbf. do 3 zs1. zbf. do 4 zs1. zbf. do 5 zs1. zbf. zs1. zbf.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (u8arr_store_ok rsegs mm buf bs len (Z_to_bv 64 (buf + len)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK end.
    zstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 ?v))) _) =>
      replace (write_to_mem mm (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 v))) with (write_to_mem mm (wa (buf + len)) [Z_to_bv 8 v]) by (f_equal; symmetry; apply le1_lit);
      pose proof (u8arr_write rsegs mm buf bs len (Z_to_bv 8 v) BU ltac:(lia)) as BU'
    end.
    clear BU; store_done.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HM2 : dg_mem mm (len + 1) Ks (upd bs (Z.to_nat len) (Z_to_bv 8 (dd + 48))))
    end.
    { unfold DgWalkB_u.dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU'|].
      split; [rewrite upd_length; exact BL|]. split; [exact LE | exact KC]. }
    do 2 zs1. zbf.
    do 5 zs1.
    assert (HLm : (Z.land (p2 * 10) (2 ^ s - 1) < 2 ^ s)%Z)
      by (replace (2 ^ s - 1)%Z with (Z.ones s) by (rewrite Z.ones_equiv; lia); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    assert (HL0 : (0 <= Z.land (p2 * 10) (2 ^ s - 1))%Z) by (apply Z.land_nonneg; lia).
    if_cases Kx3; zify_cond Kx3.
    - assert (Hi1 : (i + 1 <= 17)%Z).
      { destruct (Z_le_gt_dec (i + 1) 17) as [?|Hg]; [lia|]. assert (H18 : (10 ^ 18 <= 10 ^ (i + 1))%Z) by (apply Z.pow_le_mono_r; lia).
        rewrite Z.pow_add_r in * by lia. lia. }
      replace (Z_to_bv 64 (10 ^ i * 10)) with (Z_to_bv 64 (10 ^ (i + 1))) by (f_equal; rewrite Z.pow_add_r by lia; lia).
      replace (Z_to_bv 64 (- i + -1)) with (Z_to_bv 64 (- (i + 1))) by (f_equal; lia).
      eapply (IH (Z.to_nat (17 - (i + 1)))); [lia | reflexivity | exact HM2 | lia | lia | lia | lia | lia | rewrite Z.pow_add_r by lia; lia].
    - replace (Z_to_bv 64 (D * 10)) with (Z_to_bv 64 (10 * D)) by (f_equal; lia).
      eapply dg_l2exit; [exact HM2 | lia | lia | lia | lia | lia | lia]. }
  do 6 zs1.
  replace (bv_swrap 32 ((p2 * 10) ≫ (s mod 64) + 0)) with dd by (unfold dd in *; rewrite Z.add_0_r; symmetry; apply swrap32_small; lia).
  fold dd.
  if_cases Kx1.
  - apply BODY.
  - zs1. zs1. zbf. apply BODY.
Qed.

Lemma dg_rw1_entry : forall (D r dv cnt s len Ks : Z) t2' t3' t6' a0' a2' a5' s2' s3' s4' s5' s6' (m : word -> option byte) (bs : list byte),
  dg_mem m len Ks bs -> (1 <= len <= 3)%Z -> (2 <= cnt <= 4)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (dv = 1 \/ dv = 10 \/ dv = 100)%Z -> (56 <= s <= 59)%Z -> (0 <= r < D)%Z -> (D < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) t2' (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) (Z_to_bv 64 r)
                                  a0' (Z_to_bv 64 D) a2' (Z_to_bv 64 1) (Z_to_bv 64 dv) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                                  t3' (Z_to_bv 64 cnt) (Z_to_bv 64 1) t6')
                              F (Z_to_bv 64 0x44bbc) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR KsR Hdv Hs Hr HD.
  pose proof HM as HM0. dg_mem_intro HM.
  zs1. zbf.
  zs1. zs1. zbf.
  do 5 zs1. zbf.
  zs1.
  assert (KC' : rw_cells rsegs m1 kp [C4 (Z_to_bv 64 (Ks + (cnt - 2)))]) by (replace (Ks + (cnt - 2))%Z with (Ks + (cnt + -2))%Z by lia; exact KC).
  assert (HM1 : dg_mem m1 len (Ks + (cnt - 2)) bs).
  { unfold DgWalkB_u.dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU|].
    split; [exact BL|]. split; [exact LE | exact KC']. }
  zs1.
  set (tk := ((dv ≪ (s mod 64)) mod 2 ^ 64)%Z).
  assert (Htk : (1 <= tk < 2 ^ 64)%Z).
  { assert (Hc : (s = 56 \/ s = 57 \/ s = 58 \/ s = 59)%Z) by lia. unfold tk.
    destruct Hdv as [-> | [-> | ->]]; destruct Hc as [-> | [-> | [-> | ->]]]; vm_compute; split; congruence. }
  replace (Z_to_bv 64 (dv ≪ (s mod 64))) with (Z_to_bv 64 tk) by (unfold tk; apply Z_to_bv_mod64).
  do 3 zs1. if_cases Kw1.
  - zs1. eapply dg_weed1; [exact HM1 | lia | lia].
  - zs1. if_cases Kw2; zify_cond Kw2.
    + zs1. eapply dg_weed1; [exact HM1 | lia | lia].
    + do 12 zs1.
      ub_norm.
      replace (len + -1 + buf)%Z with (buf + len + -1)%Z by lia.
      eapply (dg_rw1_loop (Z.to_nat (D - r)) D r tk len); [reflexivity | exact HM1 | lia | lia | lia | lia | | lia].
      revert Kw2; unfold tk; rewrite ?Z.mod_small by lia; intros Kw2; lia.
Qed.

End DGB2.
