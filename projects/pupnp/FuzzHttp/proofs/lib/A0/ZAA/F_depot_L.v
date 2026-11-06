(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import ADepot ATacA F_imemcpy.
Import ListNotations.
Open Scope Z_scope.

Lemma land_low_shiftl : forall x y k, 0 <= k -> 0 <= x < 2^k -> Z.land x (Z.shiftl y k) = 0.
Proof.
  intros x y k Hk Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k).
  - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
  - destruct (Z.eq_dec x 0) as [->|]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia|]. apply Z.lt_le_trans with k; [apply Z.log2_lt_pow2; lia| lia].
Qed.
Lemma lor_shiftl_add : forall x y k, 0 <= k -> 0 <= x < 2^k -> 0 <= y -> Z.lor x (Z.shiftl y k) = x + 2^k * y.
Proof.
  intros x y k Hk Hx Hy. pose proof (land_low_shiftl x y k Hk Hx) as L0.
  rewrite <- Z.lxor_lor by exact L0. rewrite <- (Z.add_nocarry_lxor _ _ L0). rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.
Lemma lor_high31 : forall v, 0 <= v < 2^31 -> Z.lor v 18446744071562067968 = v + 18446744071562067968.
Proof.
  intros v Hv. change 18446744071562067968 with (Z.shiftl 8589934591 31). rewrite lor_shiftl_add by lia. reflexivity.
Qed.
Lemma le4_mod32 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> a mod 2^32 = b mod 2^32 -> le4 (wz a) = le4 (wz b).
Proof.
  intros a b Ha Hb E. unfold le4. rewrite !unsigned_lit by lia.
  rewrite <- (Z_to_le_bytes_mod 4 a 32) by (cbn; lia). rewrite <- (Z_to_le_bytes_mod 4 b 32) by (cbn; lia). rewrite E. reflexivity.
Qed.
Lemma recell_C4 : forall m A a b, rw_cells asegs m A [C4 (wz a)] -> le4 (wz b) = le4 (wz a) -> rw_cells asegs m A [C4 (wz b)].
Proof. intros m A a b H E. apply (rw_cells_recell asegs m A [] (C4 (wz a)) (C4 (wz b)) [] H I); [cbn; exact E| reflexivity]. Qed.

Section LK.
  Context {HC : HasCeiling}.
  Variables (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q P v : Z) (m0 : mem).

  Definition lock_post (lo : Z) : machine_state -> Prop :=
    fun ms' => exists a2 m', ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz v) (wz 0) a2 (wz v) (wz 0) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(q - 48, q); (P, P + 4)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' P [C4 (wz (v + 2^31))] /\ stk asegs m' lo q.

  #[using="Type"] Lemma lock_spec : forall lo a1 a2 a3 a4,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 48 -> q mod 16 = 0 -> q <= 2^47 ->
    rw_cells asegs m0 P [C4 (wz v)] -> 0 <= v < 2^31 -> P mod 4 = 0 -> 0 <= P -> P + 4 <= alloc_ceiling ->
    mem_inv asegs m0 ->
    evt asegs (lock_post lo)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x78cc8) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo a1 a2 a3 a4 ST CLO LO AL QH CP RV P4 P0 PC MI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl [(q - 48, q); (P, P + 4)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 48%nat ST. rewrite !E in *.
    do 6 sstep.
    zstep. zstep. zstep. zstep.
    zstep.
    rewrite (sx32_lit v) by lia.
    zstep. if_cases KS; zify_cond KS. 2:{ exfalso. revert KS RV. clear. intros. rewrite ?unsigned_lit in KS by lia. lia. }
    zstep.
    assert (AMO : amo_aligned AW (Z_to_bv 64 P) = true) by (apply amo_aligned_intro_w; lia).
    amo_step_h AMO.
    rewrite (sx32_lit v) by lia.
    zstep. if_cases K1; zify_cond K1. { exfalso. revert K1 RV. clear. intros. rewrite ?unsigned_lit in K1 by lia. lia. }
    amo_step_h AMO.
    match goal with H : rw_cells asegs ?mm P [C4 ?x] |- _ =>
      apply (recell_C4 _ P _ (v + 2^31)) in H; [| apply le4_mod32; [lia| rewrite lor_high31 by lia; lia| rewrite lor_high31 by lia; change (2^31) with 2147483648; change (2^32) with 4294967296; lia]] end.
    zstep. if_cases K2; zify_cond K2. { exfalso. revert K2. clear. intros K2. rewrite ?unsigned_lit in K2 by lia. lia. }
    zstep. if_cases K3; zify_cond K3. 2:{ exfalso. revert K3 RV. clear. intros. rewrite ?unsigned_lit in K3 by lia. lia. }
    do 5 zstep. zstep. replace (q + -48 + 48) with q by lia. zstep.
    release_frame FR ST q.
    apply evt_done. unfold lock_post. eexists _, _. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try eassumption.
  Qed.
End LK.

Lemma shl44_shr41 : forall t, 0 <= t < 2^20 -> Z.shiftr (Z.shiftl t 44 mod 18446744073709551616) 41 = 8 * t.
Proof.
  intros t Ht. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (change 18446744073709551616 with (2^20 * 2^44); nia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^44) with (8 * 2^41). rewrite Z.mul_assoc. rewrite Z.div_mul by lia. lia.
Qed.

Section AL.
  Context {HC : HasCeiling}.
  Variables (ra gp tp t2 s0 s1 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q SS0v total cnt IDXP : Z) (m0 : mem).

  Definition ssalloc_post (lo : Z) (stw : word) : machine_state -> Prop :=
    fun ms' => exists a4 t0 t1 m', ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz (SS0v + 8 * total)) (wz SSA) (wz SSA) a3 a4 (wz cnt) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(q - 16, q); (SSA, SSA + 8); (IDXP, IDXP + 8)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' SSA [C8 (wz (total + cnt))] /\ rw_cells asegs m' SSD [C8 (wz SS0v); C4 stw]
      /\ rw_cells asegs m' IDXP [C8 (wz total)] /\ stk asegs m' lo q.

  #[using="Type"] Lemma ssalloc_spec : forall lo (stw ij : word) t0 t1 a4 a5,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 16 -> q mod 16 = 0 -> q <= 2^47 ->
    rw_cells asegs m0 SSA [C8 (wz total)] -> rw_cells asegs m0 SSD [C8 (wz SS0v); C4 stw] ->
    rw_cells asegs m0 IDXP [C8 ij] -> q <= IDXP -> IDXP + 8 <= 2^47 ->
    0 <= total -> 1 <= cnt -> total + cnt <= 2^20 -> 0 < SS0v -> SS0v + 2^23 <= 2^47 ->
    mem_inv asegs m0 ->
    evt asegs (ssalloc_post lo stw)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz SSA) (wz cnt) (wz IDXP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x7605c) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo stw ij t0 t1 a4 a5 ST CLO LO AL QH CT CD CI IQ IH T0 C1 TB S0P S0H MI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl [(q - 16, q); (SSA, SSA + 8); (IDXP, IDXP + 8)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 16%nat ST. rewrite !E in *.
    do 3 sstep.
    zstep. zstep.
    amo_step.
    match goal with H : rw_cells asegs ?mm SSA [C8 (amo_val _ _ _)] |- _ => cbn [amo_val] in H; rewrite lit_add_lit in H end.
    zstep.
    zstep.
    replace (Z.shiftr total 20) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
    zstep. zstep.
    replace (Z.shiftr (cnt + -1 + total) 20) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
    zstep. if_cases K1; zify_cond K1. { exfalso. revert K1. clear. intros K1. rewrite ?unsigned_lit in K1 by lia. lia. }
    zstep.
    replace (Z.shiftr total 32) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
    zstep. if_cases K2; zify_cond K2. 2:{ exfalso. revert K2. clear. intros K2. rewrite ?unsigned_lit in K2 by lia. lia. }
    sstep.
    zstep. zstep.
    change (Z.shiftl 0 4) with 0. replace (SSA + 0) with SSA by lia.
    zstep.
    zstep. if_cases K3; zify_cond K3. { exfalso. revert K3 S0P S0H. clear. intros. rewrite ?unsigned_lit in K3 by lia. lia. }
    zstep. zstep.
    rewrite (shl44_shr41 total) by lia.
    zstep.
    do 2 zstep. zstep. replace (q + -16 + 16) with q by lia. zstep.
    release_frame FR ST q.
    apply evt_done. unfold ssalloc_post. eexists _, _, _, _. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try eassumption.
  Qed.
End AL.

