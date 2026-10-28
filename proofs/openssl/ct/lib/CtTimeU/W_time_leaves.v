(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtSizes CtWire.   (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
Definition leaf16_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) (r : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma ossl_ascii_isdigit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo c : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  (- 2^31 <= c < 2^31)%Z -> a0 = Z_to_bv 64 c ->
  evt ctusegs (leaf16_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (Z_to_bv 64 (if (48 <=? c) && (c <=? 57) then 1 else 0)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OSSL_ASCII_ISDIGIT) fc None m (seg_rom ctusegs)).
Proof.
  intros until c. intros ST MI GLO LO Hc ->. unfold GLOBALS_TOP in GLO. unfold OSSL_ASCII_ISDIGIT in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  zstep. zstep.
  setreg 10%Z (Z_to_bv 64 (if (48 <=? c) && (c <=? 57) then 1 else 0))
    ltac:(f_equal; rewrite zb_b2z_if, !land64;
          assert (E2 : 2^64 = 18446744073709551616) by reflexivity; assert (E1 : 2^31 = 2147483648) by reflexivity;
          rewrite swrap32_mod64;
          destruct (Z_le_gt_dec (- 2^31) (c - 48)) as [G|G];
          [ rewrite swrap32_small by lia;
            destruct (Z_le_gt_dec 48 c) as [G2|G2];
            [ rewrite mod64_small by lia; destruct (Z.leb_spec 48 c); destruct (Z.leb_spec c 57); destruct (Z.ltb_spec (c + -48) 10); cbn [andb]; first [reflexivity| lia]
            | rewrite mod64_neg by lia; destruct (Z.leb_spec 48 c); destruct (Z.ltb_spec (c + -48 + 2^64) 10); cbn [andb]; first [reflexivity| lia] ]
          | destruct (swrap32_congr (c + -48)) as [k Hk]; pose proof (swrap32_range (c + -48)) as RG; rewrite Hk in RG |- *;
            assert (k = 1) by lia; subst k; rewrite mod64_small by lia;
            destruct (Z.leb_spec 48 c); destruct (Z.ltb_spec (c + -48 + 1 * 2^32) 10); cbn [andb]; first [reflexivity| lia] ]).
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
Qed.

(* [comment removed for export] *)
Lemma ASN1_STRING_get_length_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A len : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  (0 < A /\ (A + 24 <= lo \/ bv_unsigned sp <= A))%Z -> (A mod 8 = 0)%Z ->
  ro_cells ctusegs m (A + ASO_LENGTH) [C4 (Z_to_bv 64 len)] -> (0 <= len < 2^31)%Z ->
  a0 = Z_to_bv 64 A ->
  evt ctusegs (leaf16_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (Z_to_bv 64 len))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASN1_STRING_GET_LENGTH) fc None m (seg_rom ctusegs)).
Proof.
  intros until len. intros ST MI GLO LO HA ALA HL Hlen ->. unfold GLOBALS_TOP in GLO. unfold ASN1_STRING_GET_LENGTH, ASO_LENGTH in *.
  rewrite Z.add_0_r in HL.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPA : A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) by lia.
  carve_frame 16%nat ST. do 4 zstep.
  zstep. let C := fresh "C" in if_cases C;
    [exfalso; zify_cond C; pose proof (ro_cells_bound _ _ _ _ HL) as HB; cbn in HB; rewrite ?land64, ?Z.mod_small in C by lia; lia | clear C].
  zstep. zstep. let C := fresh "C" in if_cases C;
    [exfalso; zify_cond C; change 7 with (Z.ones 3) in C; rewrite Z.land_ones in C by lia; change (2^3) with 8 in C; apply C;
     pose proof (ro_cells_bound _ _ _ _ HL) as HB; cbn in HB; rewrite ?land64, ?(Z.mod_small A (2^64)) by lia; exact ALA | clear C].
  zstep. setreg 10%Z (Z_to_bv 64 len) ltac:(symmetry; apply sx32_small; lia).
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
Qed.

(* [comment removed for export] *)
Lemma ASN1_STRING_get0_data_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A : Z) (d : word),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  (0 < A /\ (A + 24 <= lo \/ bv_unsigned sp <= A))%Z -> (A mod 8 = 0)%Z ->
  ro_cells ctusegs m (A + ASO_DATA) [C8 d] ->
  a0 = Z_to_bv 64 A ->
  evt ctusegs (leaf16_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m d)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASN1_STRING_GET0_DATA) fc None m (seg_rom ctusegs)).
Proof.
  intros until d. intros ST MI GLO LO HA ALA HD ->. unfold GLOBALS_TOP in GLO. unfold ASN1_STRING_GET0_DATA, ASO_DATA in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPA : A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) by lia.
  carve_frame 16%nat ST. do 4 zstep.
  zstep. let C := fresh "C" in if_cases C;
    [exfalso; zify_cond C; pose proof (ro_cells_bound _ _ _ _ HD) as HB; cbn in HB; rewrite ?land64, ?Z.mod_small in C by lia; lia | clear C].
  zstep. zstep. let C := fresh "C" in if_cases C;
    [exfalso; zify_cond C; change 7 with (Z.ones 3) in C; rewrite Z.land_ones in C by lia; change (2^3) with 8 in C; apply C;
     pose proof (ro_cells_bound _ _ _ _ HD) as HB; cbn in HB; rewrite ?land64, ?(Z.mod_small A (2^64)) by lia; exact ALA | clear C].
  zstep.
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
Qed.

End WithCeiling.
