(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk HeapIfaceA BigLinkBase BigLinkGlue L5Defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5ACHK.
Section WithSegs.
Variable segs : list Segment.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) (only parsing).

Lemma reg_ne (i j : nat) : (i < 32)%nat -> (j < 32)%nat -> i <> j -> (Z_to_bv 5 (Z.of_nat i) : bv 5) <> Z_to_bv 5 (Z.of_nat j).
Proof.
  intros Hi Hj Hn E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 5) with 32 in E. rewrite !Z.mod_small in E by lia. lia.
Qed.

Lemma reg_ne0 (i : nat) : (0 < i < 32)%nat -> (Z_to_bv 5 (Z.of_nat i) : bv 5) <> (0%bv : bv 5).
Proof.
  intros Hi E. apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 5) with 32 in E. rewrite Z.mod_small in E by lia. change (bv_unsigned (0%bv : bv 5)) with 0 in E. lia.
Qed.

Lemma getr_x0 (R : bvmap 5 word) : getr R (Z_to_bv 5 (Z.of_nat 0)) = Z_to_bv 64 0.
Proof. unfold getr. replace (Z_to_bv 5 (Z.of_nat 0)) with (0%bv : bv 5) by (apply bv_eq; reflexivity). rewrite bv_eqb_refl. reflexivity. Qed.

Theorem asan_chk1 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte)
        (pc SLOW : Z) (rt ra ru : nat) (w1 w2 w3 w4 : bv 32) (i2 i4 : bv 13) (a : Z) :
  fetch_word segs (Z_to_bv 64 pc) = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (Load SZ1 true (reg rt) (reg rt) 0%bv, 4%Z) ->
  fetch_word segs (Z_to_bv 64 (pc + 4)) = Some w2 -> is_ecall w2 = false -> decode_any w2 = Some (Branch BC_NE (reg rt) (reg 0) i2, 4%Z) ->
  pc + 4 + bv_signed i2 = SLOW ->
  fetch_word segs (Z_to_bv 64 SLOW) = Some w3 -> is_ecall w3 = false -> decode_any w3 = Some (OpImm ALU_AND (reg ru) (reg ra) 7%bv, 4%Z) ->
  fetch_word segs (Z_to_bv 64 (SLOW + 4)) = Some w4 -> is_ecall w4 = false -> decode_any w4 = Some (Branch BC_LT (reg ru) (reg rt) i4, 4%Z) ->
  SLOW + 4 + bv_signed i4 = pc + 8 ->
  (0 < rt < 32)%nat -> (0 < ru < 32)%nat -> (ra < 32)%nat -> rt <> ru -> ra <> rt ->
  0 <= pc /\ pc + 8 < 2 ^ 64 -> 0 <= SLOW /\ SLOW + 8 < 2 ^ 64 ->
  getr R (reg rt) = Z_to_bv 64 (S a) -> getr R (reg ra) = Z_to_bv 64 a -> 0 <= a < 2 ^ 47 ->
  aacc M a 1 ->
  exists R', msteps segs (st fx R pc M) (st fx R' (pc + 8) M)
             /\ (forall k, (k < 32)%nat -> k <> rt -> k <> ru -> getr R' (reg k) = getr R (reg k)).
Proof.
  intros F1 E1 D1 F2 E2 D2 T2 F3 E3 D3 F4 E4 D4 T4 Hrt Hru Hra Hne Hne2 Hpc Hsl Grt Gra Ha ACC.
  assert (SR : 0 <= S a < 2 ^ 64). { unfold S, SB. split. apply Z.add_nonneg_nonneg. apply Z.div_pos; lia. lia.
    assert (a / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia). lia. }
  destruct (ACC a ltac:(lia)) as [Z0 | (v & Bv & Hv & Hm)].
  - (* [comment removed for export] *)
    exists (regupd R (reg rt) (v_lb (Z_to_bv 8 0))). split.
    + eapply mst_step. reflexivity.
      { rewrite (step_lb segs R _ M (seg_rom segs) w1 (reg rt) (reg rt) 0%bv (Z_to_bv 8 0) F1 E1 D1).
        2:{ rewrite Grt. unfold v_addi. change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r, BG.unsigned_lit by lia. cbn [rdn].
            unfold byte_at in Z0. rewrite Z0. reflexivity. }
        rewrite (bv_eqb_neq _ _ (reg_ne0 rt Hrt)). reflexivity. }
      eapply mst_step. reflexivity.
      { unfold v_addi. rewrite BG.unsigned_lit by lia.
        rewrite (step_bne_ft segs _ _ M (seg_rom segs) w2 (reg rt) (reg 0) i2 F2 E2 D2). reflexivity.
        unfold c_eq. rewrite getr_same by (apply reg_ne0; lia). rewrite getr_x0. unfold v_lb. replace (bv_signed (Z_to_bv 8 0)) with 0 by reflexivity. apply bv_eqb_refl. }
      unfold v_addi. rewrite BG.unsigned_lit by lia. replace (pc + 4 + 4) with (pc + 8) by lia. apply mst_refl.
    + intros k Hk K1 K2. apply getr_other. apply reg_ne; lia.
  - (* [comment removed for export] *)
    set (R1 := regupd R (reg rt) (v_lb (Z_to_bv 8 v))).
    set (R2 := regupd R1 (reg ru) (v_andi (getr R1 (reg ra)) (bv_signed (7%bv : bv 12)))).
    assert (LBv : v_lb (Z_to_bv 8 v) = Z_to_bv 64 v).
    { unfold v_lb. f_equal. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
      rewrite Z.mod_small by lia. lia. }
    assert (G1rt : getr R1 (reg rt) = Z_to_bv 64 v). { unfold R1. rewrite getr_same by (apply reg_ne0; lia). exact LBv. }
    assert (G1ra : getr R1 (reg ra) = Z_to_bv 64 a).
    { unfold R1. rewrite getr_other by (apply reg_ne; lia). exact Gra. }
    assert (ANDv : v_andi (Z_to_bv 64 a) (bv_signed (7%bv : bv 12)) = Z_to_bv 64 (a mod 8)).
    { unfold v_andi. change (bv_signed (7%bv : bv 12)) with 7. change (bv_wrap 64 7) with 7. rewrite BG.unsigned_lit by lia.
      change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. }
    exists R2. split.
    + eapply mst_step. reflexivity.
      { rewrite (step_lb segs R _ M (seg_rom segs) w1 (reg rt) (reg rt) 0%bv (Z_to_bv 8 v) F1 E1 D1).
        2:{ rewrite Grt. unfold v_addi. change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r, BG.unsigned_lit by lia. cbn [rdn].
            unfold byte_at in Bv. rewrite Bv. reflexivity. }
        rewrite (bv_eqb_neq _ _ (reg_ne0 rt Hrt)). reflexivity. }
      eapply mst_step. reflexivity.
      { unfold v_addi. rewrite BG.unsigned_lit by lia.
        rewrite (step_bne_tk segs _ _ M (seg_rom segs) w2 (reg rt) (reg 0) i2 F2 E2 D2). unfold btgt, v_addi. rewrite BG.unsigned_lit by lia. rewrite T2. reflexivity.
        unfold c_eq. fold R1. rewrite G1rt. rewrite getr_x0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
        rewrite !BG.unsigned_lit in E by lia. lia. }
      eapply mst_step. reflexivity.
      { fold R1. rewrite (step_andi_at segs R1 (Z_to_bv 64 SLOW) M (seg_rom segs) w3 (reg ru) (reg ra) 7%bv _ F3 E3 D3 (bv_eqb_neq _ _ (reg_ne0 ru Hru)) eq_refl). reflexivity. }
      eapply mst_step. reflexivity.
      { fold R2. unfold v_addi. rewrite BG.unsigned_lit by lia.
        rewrite (step_blt_tk segs R2 _ M (seg_rom segs) w4 (reg ru) (reg rt) i4 F4 E4 D4). unfold btgt, v_addi. rewrite BG.unsigned_lit by lia. rewrite T4. reflexivity.
        unfold c_lts, bv_lts. unfold R2. rewrite getr_same by (apply reg_ne0; lia). rewrite getr_other by (apply reg_ne; lia). rewrite G1rt, G1ra, ANDv.
        rewrite !Z_to_bv_signed. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
        rewrite !Z.mod_small by lia. apply Z.ltb_lt. pose proof (Z.mod_pos_bound a 8). lia. }
      apply mst_refl.
    + intros k Hk K1 K2. unfold R2, R1. rewrite getr_other by (apply reg_ne; lia). rewrite getr_other by (apply reg_ne; lia). reflexivity.
Qed.
End WithSegs.
End L5ACHK.
