(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac SFModel Ubs ZBridge.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition sa_hdr (lv pad top ne nodes : word) : list cell := [C4 lv; C4 pad; C8 top; C8 ne; C8 nodes].

Lemma sa_slot : forall n, 0 <= n < 16 -> bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 n)) 15)) ≪ 3 = 8 * n.
Proof.
  intros n Hn. rewrite (unsigned_lit n) by lia. change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
  rewrite Z.mod_small by lia. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

(* [comment removed for export] *)
Definition T_sa_get_leaf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo n LV NODES : Z) (pad top ne v : word),
    ro_cells usegs m (bv_unsigned a0) (sa_hdr (Z_to_bv 64 LV) pad top ne (Z_to_bv 64 NODES)) -> bv_unsigned a0 <> 0 -> bv_unsigned a0 mod 8 = 0 ->
    a1 = Z_to_bv 64 n -> 0 <= n < 16 -> n <= bv_unsigned top -> bv_unsigned ne <> 0 -> 0 <= LV < 2 -> 0 < NODES < 2 ^ 64 -> NODES mod 8 = 0 ->
    ro_cells usegs m (NODES + 8 * n) [C8 v] ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 ->
    (bv_unsigned a0 + 32 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (NODES + 8 * n + 8 <= lo \/ bv_unsigned sp <= NODES + 8 * n) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (a1' a2' a3' a4' a5' a6' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xf12e8) fc None m (seg_rom usegs)).

Theorem T_sa_get_leaf_proof : T_sa_get_leaf_stmt.
Proof.
  unfold T_sa_get_leaf_stmt, sa_hdr. intros until v. intros HC A0 AAL -> HN HT HNE HLV HNO NAL VC ST LO0 LO S1 S2 MI.
  pose proof (ro_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (ro_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 top) as RTOP. unfold bv_modulus in RTOP. cbn in RTOP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Sp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Sp) by (unfold Sp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (Pn := NODES + 8 * n) in *.
  assert (SW : forall z, - 2147483648 <= z < 2147483648 -> bv_swrap 32 z = z)
    by (clear; intros z Hz; change (bv_swrap 32 z) with ((z + 2147483648) mod 4294967296 - 2147483648); rewrite Z.mod_small by lia; lia).
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
  zstep. zstep. ubs_if.
  zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
  zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  zstep. rewrite (t_sx32_small LV) by lia.
  zstep. rewrite SW by lia.
  zstep. if_cases K3; zify_cond K3; signed_lits_in K3. { exfalso. lia. }
  zstep. zstep. if_cases K4; zify_cond K4. { exfalso. lia. }
  zstep. if_cases K5; zify_cond K5.
  2:{ exfalso. assert (HL : LV = 0 \/ LV = 1) by lia.
      destruct HL as [HL|HL]; rewrite HL in K6, K7; cbv in K6, K7; [discriminate K7 | discriminate K6]. }
  zstep. if_cases K8; zify_cond K8. { exfalso. lia. }
  assert (SL60 : forall k, 0 <= k < 16 -> Z.land (k ≪ 60) 18446744073709551615 ≫ 57 = 8 * k).
  { clear. intros k Hk. rewrite Z.shiftl_mul_pow2 by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
    rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 60) with (2 ^ 57 * 8).
    replace (k * (2 ^ 57 * 8)) with (8 * k * 2 ^ 57) by lia. rewrite Z.div_mul by lia. lia. }
  do 2 zstep. rewrite (SL60 n HN).
  zstep. zstep. if_cases K9; zify_cond K9. { exfalso. rewrite zb_lxor_ones in K9 by lia. lia. }
  zstep. zstep. zstep. ubs_if.
  fold Pn. assert (HPn : 0 <= Pn) by lia. clearbody Pn.
  zstep.
  do 4 zstep.
  th_release FR (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Definition T_sa_get_empty_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (lv pad top nodes : word),
    ro_cells usegs m (bv_unsigned a0) (sa_hdr lv pad top (Z_to_bv 64 0) nodes) -> bv_unsigned a0 <> 0 -> bv_unsigned a0 mod 8 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 ->
    (bv_unsigned a0 + 32 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xf12e8) fc None m (seg_rom usegs)).

Theorem T_sa_get_empty_proof : T_sa_get_empty_stmt.
Proof.
  unfold T_sa_get_empty_stmt, sa_hdr. intros until nodes. intros HC A0 AAL ST LO0 LO S1 MI.
  pose proof (ro_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Sp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Sp) by (unfold Sp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
  zstep. zstep. ubs_if.
  zstep. zstep. th_if_lit.
  do 2 zstep.
  do 4 zstep.
  th_release FR (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Definition sa_delta (val old : word) : Z :=
  if bv_eqb val (Z_to_bv 64 0) then (if bv_eqb old (Z_to_bv 64 0) then 0 else -1) else (if bv_eqb old (Z_to_bv 64 0) then 1 else 0).

Definition T_sa_set_leaf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SA n NODES : Z) (pad top ne oldv : word),
    a0 = Z_to_bv 64 SA -> 0 < SA -> SA mod 8 = 0 -> a1 = Z_to_bv 64 n -> 0 <= n < 16 ->
    rw_cells usegs m SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 NODES)) -> 0 < NODES < 2 ^ 64 -> NODES mod 8 = 0 ->
    rw_cells usegs m (NODES + 8 * n) [C8 oldv] ->
    (SA + 32 <= NODES + 8 * n \/ NODES + 8 * n + 8 <= SA) ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 96 ->
    (SA + 32 <= lo \/ bv_unsigned sp <= SA) ->
    (NODES + 8 * n + 8 <= lo \/ bv_unsigned sp <= NODES + 8 * n) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (a1' a2' : word) (top' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (SA + 8, SA + 24); (NODES + 8 * n, NODES + 8 * n + 8)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ bv_unsigned top' = Z.max (bv_unsigned top) n
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 (bv_unsigned ne + sa_delta a2 oldv)) (Z_to_bv 64 NODES))
                 /\ rw_cells usegs m' (NODES + 8 * n) [C8 a2])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xf13bc) fc None m (seg_rom usegs)).

Theorem T_sa_set_leaf_proof : T_sa_set_leaf_stmt.
Proof.
  unfold T_sa_set_leaf_stmt, sa_hdr. intros until oldv. intros -> HSA HSAA -> HN HC HNO NAL VC SEP ST LO0 LO S1 S2 MI.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (rw_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 top) as RTOP. unfold bv_modulus in RTOP. cbn in RTOP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (SA + 8, SA + 24); (NODES + 8 * n, NODES + 8 * n + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  set (Pn := NODES + 8 * n) in *.
  assert (HPn : 0 <= Pn) by (unfold Pn; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ ?Q _ =>
  assert (TAIL : forall (topw y10 : word) (mc : mem) (jb : list byte),
    rw_cells usegs mc SA [C4 (Z_to_bv 64 1); C4 pad; C8 topw; C8 ne; C8 (Z_to_bv 64 NODES)] -> rw_cells usegs mc Pn [C8 oldv] ->
    rw_cells usegs mc (bv_unsigned sp + -96) [CB 8 jb; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mc lo (bv_unsigned sp + -96) -> mem_inv usegs mc ->
    munch [(bv_unsigned sp + -96, bv_unsigned sp); (SA + 8, SA + 24); (Pn, Pn + 8)]%Z m mc -> wmono usegs m mc ->
    bv_unsigned topw = Z.max (bv_unsigned top) n ->
    evt usegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp a2 y10 (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 SA) (Z_to_bv 64 n) s4 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xf1494) fc None mc (seg_rom usegs))) end.
  { intros topw y10 mc jb HCc VCc FRc STc MIc MUc WMc HTOP. clear HC VC ST MI MU WM.
    assert (EPn : Pn = NODES + 8 * n) by reflexivity. clearbody Pn.
    cbv beta delta [mkR].
    do 2 ths. ths. if_cases KL2; zify_cond KL2; signed_lits_in KL2. 2:{ exfalso. lia. }
    do 3 ths.
    assert (ESL : Z_to_bv 64 (NODES + bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 n)) 15)) ≪ 3) = Z_to_bv 64 Pn)
      by (rewrite (sa_slot n HN), EPn; reflexivity).
    rewrite ESL. clear ESL.
    ths. if_cases KW; zify_cond KW. { exfalso. lia. }
    do 3 ths. ths. if_cases KZ; zify_cond KZ.
    { exfalso. rewrite (proj2 (Z.ltb_lt 0 NODES)), (proj2 (Z.ltb_ge Pn 1)) in KZ by lia. cbv in KZ. discriminate KZ. }
    do 3 ths.
    ths.
    unfold sa_delta.
    destruct (bv_eqb a2 (Z_to_bv 64 0)) eqn:EV; cbv iota.
    - ths. if_cases KA; zify_cond KA.
      { exfalso. rewrite (ubs_land7 Pn), (proj2 (Z.ltb_lt 0 NODES)) in KA by lia. cbv in KA. discriminate KA. }
      ths. ths. destruct (bv_eqb oldv (Z_to_bv 64 0)) eqn:EO; cbv iota.
      + do 2 ths. do 13 ths.
        th_release FRc (bv_unsigned sp).
        finish; eassumption.
      + do 4 ths. do 2 ths. do 13 ths.
        th_release FRc (bv_unsigned sp).
        finish; eassumption.
    - ths. if_cases KB; zify_cond KB.
      { exfalso. rewrite (ubs_land7 Pn), (proj2 (Z.ltb_lt 0 NODES)) in KB by lia. cbv in KB. discriminate KB. }
      ths. ths. destruct (bv_eqb oldv (Z_to_bv 64 0)) eqn:EO; cbv beta iota delta [negb].
      + do 2 ths. do 3 ths. do 2 ths. do 13 ths.
        th_release FRc (bv_unsigned sp).
        finish; eassumption.
      + do 2 ths. do 13 ths.
        th_release FRc (bv_unsigned sp).
        finish; eassumption. }
  th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 13 ths.
  ths. if_cases K0; zify_cond K0. { exfalso. lia. }
  do 5 ths.
  ths. if_cases K16; zify_cond K16. 2:{ exfalso. lia. }
  ths. ths. ubs_if.
  ths. rewrite (t_sx32_small 1) by lia.
  ths. if_cases KL; zify_cond KL; signed_lits_in KL. 2:{ exfalso. lia. }
  ths.
  ths. if_cases KT; zify_cond KT.
  - eapply TAIL; try eassumption. lia.
  - ths. eapply TAIL; try eassumption. rewrite unsigned_lit by lia. lia.
Qed.



(* [comment removed for export] *)
Definition T_sa_set_mid_stmt : Prop :=
  forall (x1 gp tp t0 t1 t2 x8 val a0 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SP SA n NODES : Z) (pad top ne oldv rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o : word) (jb : list byte),
    0 <= n < 16 -> 0 < SA ->
    rw_cells usegs m SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 NODES)) -> 0 < NODES < 2 ^ 64 -> NODES mod 8 = 0 ->
    rw_cells usegs m (NODES + 8 * n) [C8 oldv] ->
    (SA + 32 <= NODES + 8 * n \/ NODES + 8 * n + 8 <= SA) ->
    rw_cells usegs m (SP + -96) [CB 8 jb; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
    stk usegs m lo (SP + -96) -> 0 <= lo -> lo <= SP - 96 -> SP < 2 ^ 64 ->
    (SA + 32 <= lo \/ SP <= SA) ->
    (NODES + 8 * n + 8 <= lo \/ SP <= NODES + 8 * n) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (a1' a2' : word) (top' : word) (m' : mem),
                 ms' = MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1o (Z_to_bv 64 1) a1' a2' a3 a4 a5 a6 a7 s2o s3o s4o s5o s6o s7o s8o s9o s10 s11 t3 t4 t5 t6)
                          F (ret_pc rao) fc None m' (seg_rom usegs)
                 /\ munch [(SP - 96, SP); (SA + 8, SA + 24); (NODES + 8 * n, NODES + 8 * n + 8)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ bv_unsigned top' = Z.max (bv_unsigned top) n
                 /\ stk usegs m' lo SP
                 /\ rw_cells usegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 (bv_unsigned ne + sa_delta val oldv)) (Z_to_bv 64 NODES))
                 /\ rw_cells usegs m' (NODES + 8 * n) [C8 val])
        (MS (mkR x1 (Z_to_bv 64 (SP + -96)) gp tp t0 t1 t2 x8 val a0 (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SA) (Z_to_bv 64 n) s4 (Z_to_bv 64 1)
                 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xf1488) fc None m (seg_rom usegs)).

Theorem T_sa_set_mid_proof : T_sa_set_mid_stmt.
Proof.
  unfold T_sa_set_mid_stmt, sa_hdr. intros until jb. intros HN HSA HC HNO NAL VC SEP FR ST LO0 LO SPH S1 S2 MI.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (rw_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (bv_unsigned_in_range 64 top) as RTOP. unfold bv_modulus in RTOP. cbn in RTOP.
  pose proof (munch_refl [(SP - 96, SP); (SA + 8, SA + 24); (NODES + 8 * n, NODES + 8 * n + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  set (Pn := NODES + 8 * n) in *.
  assert (HPn : 0 <= Pn) by (unfold Pn; lia).
  lazymatch goal with |- evt _ ?Q _ =>
  assert (TAIL : forall (topw y10 : word) (mc : mem),
    rw_cells usegs mc SA [C4 (Z_to_bv 64 1); C4 pad; C8 topw; C8 ne; C8 (Z_to_bv 64 NODES)] -> rw_cells usegs mc Pn [C8 oldv] ->
    rw_cells usegs mc (SP + -96) [CB 8 jb; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
    stk usegs mc lo (SP + -96) -> mem_inv usegs mc ->
    munch [(SP - 96, SP); (SA + 8, SA + 24); (Pn, Pn + 8)]%Z m mc -> wmono usegs m mc ->
    bv_unsigned topw = Z.max (bv_unsigned top) n ->
    evt usegs Q (MS (mkR x1 (Z_to_bv 64 (SP + -96)) gp tp t0 t1 t2 x8 val y10 (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 SA) (Z_to_bv 64 n) s4 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xf1494) fc None mc (seg_rom usegs))) end.
  { intros topw y10 mc HCc VCc FRc STc MIc MUc WMc HTOP. clear HC VC ST MI MU WM FR.
    assert (EPn : Pn = NODES + 8 * n) by reflexivity. clearbody Pn.
    cbv beta delta [mkR].
    do 2 ths. ths. if_cases KL2; zify_cond KL2; signed_lits_in KL2. 2:{ exfalso. lia. }
    do 3 ths.
    assert (ESL : Z_to_bv 64 (NODES + bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 n)) 15)) ≪ 3) = Z_to_bv 64 Pn)
      by (rewrite (sa_slot n HN), EPn; reflexivity).
    rewrite ESL. clear ESL.
    ths. if_cases KW; zify_cond KW. { exfalso. lia. }
    do 3 ths. ths. if_cases KZ; zify_cond KZ.
    { exfalso. rewrite (proj2 (Z.ltb_lt 0 NODES)), (proj2 (Z.ltb_ge Pn 1)) in KZ by lia. cbv in KZ. discriminate KZ. }
    do 3 ths.
    ths.
    unfold sa_delta.
    destruct (bv_eqb val (Z_to_bv 64 0)) eqn:EV; cbv iota.
    - ths. if_cases KA; zify_cond KA.
      { exfalso. rewrite (ubs_land7 Pn), (proj2 (Z.ltb_lt 0 NODES)) in KA by lia. cbv in KA. discriminate KA. }
      ths. ths. destruct (bv_eqb oldv (Z_to_bv 64 0)) eqn:EO; cbv iota.
      + do 2 ths. do 13 ths.
        th_release FRc SP.
        finish; eassumption.
      + do 4 ths. do 2 ths. do 13 ths.
        th_release FRc SP.
        finish; eassumption.
    - ths. if_cases KB; zify_cond KB.
      { exfalso. rewrite (ubs_land7 Pn), (proj2 (Z.ltb_lt 0 NODES)) in KB by lia. cbv in KB. discriminate KB. }
      ths. ths. destruct (bv_eqb oldv (Z_to_bv 64 0)) eqn:EO; cbv beta iota delta [negb].
      + do 2 ths. do 3 ths. do 2 ths. do 13 ths.
        th_release FRc SP.
        finish; eassumption.
      + do 2 ths. do 13 ths.
        th_release FRc SP.
        finish; eassumption. }
  cbv beta delta [mkR].
  ths.
  ths. if_cases KT; zify_cond KT.
  - eapply TAIL; try eassumption. lia.
  - ths. eapply TAIL; try eassumption. rewrite unsigned_lit by lia. lia.
Qed.
