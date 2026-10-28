(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog CtSizes.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma ossl_ascii_isdigit_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo c : Z),
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  (- 2^31 <= c < 2^31)%Z -> a0 = Z_to_bv 64 c ->
  evt ctasegs (leaf16A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (Z_to_bv 64 (if (48 <=? c) && (c <=? 57) then 1 else 0)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OSSL_ASCII_ISDIGIT_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until c. intros ST MI CEIL LO Hc ->. unfold OSSL_ASCII_ISDIGIT_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
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
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold leaf16A_post, leafA_post. do 14 eexists. eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption. exact I.
Qed.

(* [comment removed for export] *)
Lemma ASN1_STRING_get_length_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (lo : Z) (xb : bptr) (A len ty d fl : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  In (xb, A, ASN1_STRING_SIZE) (OW ++ LB) -> A mod 8 = 0 ->
  rw_cells ctasegs m A (asn1_string_cells len ty d fl) -> (0 <= len < 2^31)%Z ->
  a0 = Z_to_bv 64 A ->
  evt ctasegs (leaf16A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (Z_to_bv 64 len))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASN1_STRING_GET_LENGTH_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until fl. intros HEAP ST MI CEIL LO HIN AL8 HX Hlen ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  ablock HEAP HIN ACC OFF.
  unfold ASN1_STRING_GET_LENGTH_A, ASN1_STRING_SIZE, SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPX : A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) by alia.
  unfold asn1_string_cells in HX. unfold MallocRep.wz, u32 in HX.
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  zstep. setreg 10%Z (Z_to_bv 64 len) ltac:(symmetry; first [apply sx32_small; lia | rewrite sx32_mod32 by lia; reflexivity]).
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold leaf16A_post, leafA_post. do 14 eexists. eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption. exact I.
Qed.

(* [comment removed for export] *)
Lemma ASN1_STRING_get0_data_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (lo : Z) (xb : bptr) (A len ty d fl : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  In (xb, A, ASN1_STRING_SIZE) (OW ++ LB) -> A mod 8 = 0 ->
  rw_cells ctasegs m A (asn1_string_cells len ty d fl) -> (0 <= d < 2^64)%Z ->
  a0 = Z_to_bv 64 A ->
  evt ctasegs (leaf16A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (Z_to_bv 64 d))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASN1_STRING_GET0_DATA_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until fl. intros HEAP ST MI CEIL LO HIN AL8 HX Hd ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  ablock HEAP HIN ACC OFF.
  unfold ASN1_STRING_GET0_DATA_A, ASN1_STRING_SIZE, SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPX : A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) by alia.
  unfold asn1_string_cells in HX. unfold MallocRep.wz, u32 in HX.
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  zstep. setreg 10%Z (Z_to_bv 64 d) ltac:(symmetry; rewrite ?land64_small by lia; reflexivity).
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold leaf16A_post, leafA_post. do 14 eexists. eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption. exact I.
Qed.

End WithRT.
