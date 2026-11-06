(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatSim StepTac WalkTac StartupTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section GrayLib.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma tset_same_id : forall {A} (p : positive) (x : A) (t : tree A), tget p t = Some x -> tset p x t = t.
Proof.
  intros A p. induction p as [p IH|p IH|]; intros x [|l v r] H; cbn in *; try discriminate.
  - f_equal. apply IH, H.
  - f_equal. apply IH, H.
  - subst v. reflexivity.
Qed.

Definition reg_present (regs : bvmap 5 word) (r : reg) : Prop := bvmap_get r regs <> None.

Lemma regupd_get_id : forall regs (r : reg), reg_present regs r -> regupd regs r (reg_get regs r) = regs.
Proof.
  intros regs r Hp. unfold reg_present in Hp. unfold regupd, bvmap_set, reg_get.
  destruct (bvmap_get r regs) as [v|] eqn:E; [|contradiction].
  apply tset_same_id. exact E.
Qed.

Lemma reg_present_upd_same : forall regs (r : reg) v, reg_present (regupd regs r v) r.
Proof. intros. unfold reg_present, regupd. rewrite bvmap_get_set_same. discriminate. Qed.

Lemma reg_present_upd_other : forall regs (r r' : reg) v, reg_present regs r -> reg_present (regupd regs r' v) r.
Proof.
  intros regs r r' v H. unfold reg_present, regupd in *.
  destruct (bv_eq_dec 5 r' r) as [->|Hne]; [rewrite bvmap_get_set_same; discriminate|].
  rewrite bvmap_get_set_other by exact Hne. exact H.
Qed.

(* [comment removed for export] *)
Definition vsel (c : bool) (a b : word) : word := if c then a else b.

Lemma diamond_mv : forall segs regs (pc pc1 pc2 : word) mem rom w1 w2 c (r1 r2 ra rb : reg) (i8 : bv 13) (i0 : bv 12),
  fetch_word segs pc = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (Branch c r1 r2 i8, 4%Z) ->
  fetch_word segs pc1 = Some w2 -> is_ecall w2 = false -> decode_any w2 = Some (OpImm ALU_ADD ra rb i0, 4%Z) ->
  v_addi pc 4 = pc1 -> v_addi pc1 4 = pc2 -> btgt pc (bv_signed i8) = pc2 -> bv_signed i0 = 0%Z ->
  ra <> 0 -> reg_present regs ra -> forall v1 v2 va vb : word, getr regs r1 = v1 -> getr regs r2 = v2 -> getr regs ra = va -> getr regs rb = vb ->
  msteps segs (mkst regs pc mem rom)
              (mkst (regupd regs ra (vsel (branch_taken c v1 v2) va vb)) pc2 mem rom).
Proof.
  intros segs regs pc pc1 pc2 mem rom w1 w2 c r1 r2 ra rb i8 i0 F1 E1 D1 F2 E2 D2 P1 P2 PB I0 Hra Hpres v1 v2 va vb <- <- <- <-.
  destruct (branch_taken c (getr regs r1) (getr regs r2)) eqn:BT; unfold vsel.
  - (* [comment removed for export] *)
    rewrite (getr_nz regs ra Hra), (regupd_get_id regs ra Hpres).
    eapply mst_step; [reflexivity | | apply mst_refl].
    rewrite (step_branch_tk_gen segs regs pc mem rom w1 c r1 r2 i8 F1 E1 D1 BT). rewrite PB. reflexivity.
  - eapply mst_step; [reflexivity | apply (step_branch_ft_gen segs regs pc mem rom w1 c r1 r2 i8 F1 E1 D1 BT) |].
    rewrite P1.
    eapply mst_step; [reflexivity | apply (step_addi segs regs pc1 mem rom w2 ra rb i0 F2 E2 D2) |].
    rewrite (bv_eqb_neq ra 0 Hra), I0, P2.
    replace (v_addi (getr regs rb) 0) with (getr regs rb); [apply mst_refl|].
    unfold v_addi. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma diamond_mv_j : forall segs regs (pc pc1 pc2 tgt : word) mem rom w1 w2 w3 c (r1 r2 ra rb : reg) (iT : bv 13) (i0 : bv 12) (iJ : bv 21),
  fetch_word segs pc = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (Branch c r1 r2 iT, 4%Z) ->
  fetch_word segs pc1 = Some w2 -> is_ecall w2 = false -> decode_any w2 = Some (OpImm ALU_ADD ra rb i0, 4%Z) ->
  fetch_word segs pc2 = Some w3 -> is_ecall w3 = false -> decode_any w3 = Some (Jal 0 iJ, 4%Z) ->
  v_addi pc 4 = pc1 -> v_addi pc1 4 = pc2 -> btgt pc (bv_signed iT) = tgt -> btgt pc2 (bv_signed iJ) = tgt -> bv_signed i0 = 0%Z ->
  ra <> 0 -> reg_present regs ra -> forall v1 v2 va vb : word, getr regs r1 = v1 -> getr regs r2 = v2 -> getr regs ra = va -> getr regs rb = vb ->
  msteps segs (mkst regs pc mem rom)
              (mkst (regupd regs ra (vsel (branch_taken c v1 v2) va vb)) tgt mem rom).
Proof.
  intros segs regs pc pc1 pc2 tgt mem rom w1 w2 w3 c r1 r2 ra rb iT i0 iJ F1 E1 D1 F2 E2 D2 F3 E3 D3 P1 P2 PB PJ I0 Hra Hpres v1 v2 va vb <- <- <- <-.
  destruct (branch_taken c (getr regs r1) (getr regs r2)) eqn:BT; unfold vsel.
  - rewrite (getr_nz regs ra Hra), (regupd_get_id regs ra Hpres).
    eapply mst_step; [reflexivity | | apply mst_refl].
    rewrite (step_branch_tk_gen segs regs pc mem rom w1 c r1 r2 iT F1 E1 D1 BT). rewrite PB. reflexivity.
  - eapply mst_step; [reflexivity | apply (step_branch_ft_gen segs regs pc mem rom w1 c r1 r2 iT F1 E1 D1 BT) |].
    rewrite P1.
    eapply mst_step; [reflexivity | apply (step_addi segs regs pc1 mem rom w2 ra rb i0 F2 E2 D2) |].
    rewrite (bv_eqb_neq ra 0 Hra), I0, P2.
    replace (v_addi (getr regs rb) 0) with (getr regs rb)
      by (unfold v_addi; rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned).
    eapply mst_step; [reflexivity | apply (step_jal_x0 segs _ pc2 mem rom w3 iJ F3 E3 D3) |].
    rewrite PJ. apply mst_refl.
Qed.

(* [comment removed for export] *)
Definition xo (j : Z) : Z := (j - j mod 4 + (3 - j mod 4))%Z.

Lemma xo_bound : forall j n : Z, (0 <= j < 4 * n)%Z -> (0 <= xo j < 4 * n)%Z.
Proof.
  intros j n Hj. unfold xo.
  pose proof (Z.div_mod j 4 ltac:(lia)) as E. pose proof (Z.mod_pos_bound j 4 ltac:(lia)) as R.
  set (q := (j / 4)%Z) in *. set (r := (j mod 4)%Z) in *. clearbody q r. lia.
Qed.

Lemma xor3_xo : forall base j : Z, (0 <= base)%Z -> (base mod 4 = 0)%Z -> (0 <= j)%Z -> (base + j < 2 ^ 64)%Z ->
  v_xori (Z_to_bv 64 (base + j)) 3 = Z_to_bv 64 (base + xo j).
Proof.
  intros base j Hb Hm Hj Hp. rewrite zbv_xori3 by lia. f_equal. unfold xo.
  assert (E : ((base + j) mod 4 = j mod 4)%Z).
  { rewrite Z.add_mod by lia. rewrite Hm, Z.add_0_l. apply Z.mod_mod. lia. }
  rewrite E. lia.
Qed.

(* [comment removed for export] *)
Lemma xor_seqz_ne : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> a <> b ->
  v_sltiu (v_xor (Z_to_bv 64 a) (Z_to_bv 64 b)) 1 = Z_to_bv 64 0.
Proof.
  intros a b Ha Hb Hne. unfold v_sltiu, v_xor. rewrite (u_Z2bv a), (u_Z2bv b) by lia.
  pose proof (Z_lxor_range a b Ha Hb) as R. rewrite u_Z2bv by lia.
  change (bv_wrap 64 1) with 1%Z.
  destruct (Z.ltb_spec (Z.lxor a b) 1) as [L|L]; [|reflexivity].
  exfalso. apply Hne. apply Z.lxor_eq. lia.
Qed.

(* [comment removed for export] *)
Lemma zbv_neg : forall a : Z, (1 <= a < 2 ^ 64)%Z -> v_sub (Z_to_bv 64 0) (Z_to_bv 64 a) = Z_to_bv 64 (2 ^ 64 - a).
Proof.
  intros a Ha. rewrite zbv_sub. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z.
  replace (0 - a)%Z with ((2 ^ 64 - a) + (-1) * 2 ^ 64)%Z by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sel_block : forall segs regs mem rom (pc pc1 pc2 pc3 pc5 pc6 pc7 pc8 pc9 pc10 : word)
    w0 w1 w2 w3 w5 w6 w7 w8 w9 c1 c2 c3 c4 c5 (p1 q1 p2 q2 p3 q3 X Y Z T B LIM : reg)
    (i1 i2 i3 i4 i5 : bv 13) (k1 k2 m1 m2 : bv 12),
  fetch_word segs pc = Some w0 -> is_ecall w0 = false -> decode_any w0 = Some (Branch c1 p1 q1 i1, 4%Z) ->
  fetch_word segs pc1 = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (Branch c2 p2 q2 i2, 4%Z) ->
  fetch_word segs pc2 = Some w2 -> is_ecall w2 = false -> decode_any w2 = Some (OpImm ALU_ADD T B k1, 4%Z) ->
  fetch_word segs pc3 = Some w3 -> is_ecall w3 = false -> decode_any w3 = Some (Branch c4 T LIM i4, 4%Z) ->
  fetch_word segs pc5 = Some w5 -> is_ecall w5 = false -> decode_any w5 = Some (OpImm ALU_ADD X Y m1, 4%Z) ->
  fetch_word segs pc6 = Some w6 -> is_ecall w6 = false -> decode_any w6 = Some (Branch c3 p3 q3 i3, 4%Z) ->
  fetch_word segs pc7 = Some w7 -> is_ecall w7 = false -> decode_any w7 = Some (OpImm ALU_ADD Z X m2, 4%Z) ->
  fetch_word segs pc8 = Some w8 -> is_ecall w8 = false -> decode_any w8 = Some (OpImm ALU_ADD T B k2, 4%Z) ->
  fetch_word segs pc9 = Some w9 -> is_ecall w9 = false -> decode_any w9 = Some (Branch c5 T LIM i5, 4%Z) ->
  v_addi pc 4 = pc1 -> v_addi pc1 4 = pc2 -> v_addi pc2 4 = pc3 -> v_addi pc5 4 = pc6 -> v_addi pc6 4 = pc7 ->
  v_addi pc7 4 = pc8 -> v_addi pc8 4 = pc9 -> v_addi pc9 4 = pc10 ->
  btgt pc (bv_signed i1) = pc5 -> btgt pc1 (bv_signed i2) = pc7 -> btgt pc3 (bv_signed i4) = pc10 -> btgt pc6 (bv_signed i3) = pc2 ->
  bv_signed m1 = 0%Z -> bv_signed m2 = 0%Z -> bv_signed k2 = bv_signed k1 ->
  X <> 0 -> Z <> 0 -> T <> 0 -> Z <> X -> T <> X -> T <> Z -> B <> X -> B <> Z -> LIM <> X -> LIM <> Z -> LIM <> T ->
  p3 <> X -> q3 <> X ->
  reg_present regs X -> reg_present regs Z ->
  forall v1 u1 v2 u2 v3 u3 vx vy vz vB vL t : word,
  getr regs p1 = v1 -> getr regs q1 = u1 -> getr regs p2 = v2 -> getr regs q2 = u2 -> getr regs p3 = v3 -> getr regs q3 = u3 ->
  getr regs X = vx -> getr regs Y = vy -> getr regs Z = vz -> getr regs B = vB -> getr regs LIM = vL ->
  v_addi vB (bv_signed k1) = t -> branch_taken c4 t vL = true -> branch_taken c5 t vL = false ->
  msteps segs (mkst regs pc mem rom)
    (mkst (regupd (regupd (regupd regs X (vsel (branch_taken c1 v1 u1) vy vx))
                          Z (if branch_taken c1 v1 u1 then vsel (branch_taken c3 v3 u3) vz vy else vsel (branch_taken c2 v2 u2) vx vz))
                  T t) pc10 mem rom).
Proof.
  intros segs regs mem rom pc pc1 pc2 pc3 pc5 pc6 pc7 pc8 pc9 pc10 w0 w1 w2 w3 w5 w6 w7 w8 w9 c1 c2 c3 c4 c5
         p1 q1 p2 q2 p3 q3 X Y Z T B LIM i1 i2 i3 i4 i5 k1 k2 m1 m2
         F0 E0 D0 F1 E1 D1 F2 E2 D2 F3 E3 D3 F5 E5 D5 F6 E6 D6 F7 E7 D7 F8 E8 D8 F9 E9 D9
         P1 P2 P3 P6 P7 P8 P9 P10 T1 T2 T4 T3 M1 M2 K12
         HX HZ HT HZX HTX HTZ HBX HBZ HLX HLZ HLT Hp3 Hq3 PX PZ
         v1 u1 v2 u2 v3 u3 vx vy vz vB vL t G1 G1' G2 G2' G3 G3' GX GY GZ GB GL Et C4 C5.
  assert (MV0 : forall x : word, v_addi x 0 = x) by (intros x; unfold v_addi; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  assert (TAIL2 : forall R, getr R B = vB -> getr R LIM = vL ->
            msteps segs (mkst R pc2 mem rom) (mkst (regupd R T t) pc10 mem rom)).
  { intros R RB RL.
    eapply mst_step; [reflexivity | apply (step_addi segs R pc2 mem rom w2 T B k1 F2 E2 D2) |].
    rewrite (bv_eqb_neq T 0 HT), RB, Et, P3.
    eapply mst_step; [reflexivity | | apply mst_refl].
    rewrite (step_branch_tk_gen segs _ pc3 mem rom w3 c4 T LIM i4 F3 E3 D3); [rewrite T4; reflexivity|].
    rewrite (getr_same R T t HT), (getr_other R T t LIM HLT), RL. exact C4. }
  assert (TAIL7 : forall R, getr R B = vB -> getr R LIM = vL ->
            msteps segs (mkst R pc7 mem rom) (mkst (regupd (regupd R Z (getr R X)) T t) pc10 mem rom)).
  { intros R RB RL.
    eapply mst_step; [reflexivity | apply (step_addi segs R pc7 mem rom w7 Z X m2 F7 E7 D7) |].
    rewrite (bv_eqb_neq Z 0 HZ), M2, MV0, P8.
    eapply mst_step; [reflexivity | apply (step_addi segs _ pc8 mem rom w8 T B k2 F8 E8 D8) |].
    rewrite (bv_eqb_neq T 0 HT), K12, (getr_other R Z _ B HBZ), RB, Et, P9.
    eapply mst_step; [reflexivity | | apply mst_refl].
    rewrite (step_branch_ft_gen segs _ pc9 mem rom w9 c5 T LIM i5 F9 E9 D9); [rewrite P10; reflexivity|].
    rewrite (getr_same _ T t HT), (getr_other _ T t LIM HLT), (getr_other R Z _ LIM HLZ), RL. exact C5. }
  rewrite <- G1, <- G1', <- G2, <- G2', <- G3, <- G3'.
  destruct (branch_taken c1 (getr regs p1) (getr regs q1)) eqn:B1; unfold vsel at 1.
  - (* [comment removed for export] *)
    eapply mst_step; [reflexivity | |].
    { rewrite (step_branch_tk_gen segs regs pc mem rom w0 c1 p1 q1 i1 F0 E0 D0 B1). rewrite T1. reflexivity. }
    eapply mst_step; [reflexivity | apply (step_addi segs regs pc5 mem rom w5 X Y m1 F5 E5 D5) |].
    rewrite (bv_eqb_neq X 0 HX), M1, MV0, GY, P6.
    set (R1 := regupd regs X vy).
    assert (R1B : getr R1 B = vB) by (unfold R1; rewrite (getr_other regs X vy B HBX); exact GB).
    assert (R1L : getr R1 LIM = vL) by (unfold R1; rewrite (getr_other regs X vy LIM HLX); exact GL).
    assert (R1X : getr R1 X = vy) by (unfold R1; apply getr_same; exact HX).
    assert (R1Z : getr R1 Z = vz) by (unfold R1; rewrite (getr_other regs X vy Z HZX); exact GZ).
    assert (B3E : branch_taken c3 (getr R1 p3) (getr R1 q3) = branch_taken c3 (getr regs p3) (getr regs q3))
      by (unfold R1; rewrite (getr_other regs X vy p3 Hp3), (getr_other regs X vy q3 Hq3); reflexivity).
    destruct (branch_taken c3 (getr regs p3) (getr regs q3)) eqn:B3; unfold vsel.
    + eapply mst_step; [reflexivity | |].
      { rewrite (step_branch_tk_gen segs R1 pc6 mem rom w6 c3 p3 q3 i3 F6 E6 D6 B3E). rewrite T3. reflexivity. }
      replace (regupd R1 Z vz) with R1; [exact (TAIL2 R1 R1B R1L)|].
      symmetry. rewrite <- R1Z, (getr_nz R1 Z HZ). apply regupd_get_id. unfold R1. apply reg_present_upd_other. exact PZ.
    + eapply mst_step; [reflexivity | apply (step_branch_ft_gen segs R1 pc6 mem rom w6 c3 p3 q3 i3 F6 E6 D6 B3E) |].
      rewrite P7. pose proof (TAIL7 R1 R1B R1L) as TL. rewrite R1X in TL. exact TL.
  - eapply mst_step; [reflexivity | apply (step_branch_ft_gen segs regs pc mem rom w0 c1 p1 q1 i1 F0 E0 D0 B1) |].
    rewrite P1.
    replace (regupd regs X vx) with regs
      by (symmetry; rewrite <- GX, (getr_nz regs X HX); apply regupd_get_id; exact PX).
    destruct (branch_taken c2 (getr regs p2) (getr regs q2)) eqn:B2; unfold vsel.
    + eapply mst_step; [reflexivity | |].
      { rewrite (step_branch_tk_gen segs regs pc1 mem rom w1 c2 p2 q2 i2 F1 E1 D1 B2). rewrite T2. reflexivity. }
      pose proof (TAIL7 regs GB GL) as TL. rewrite GX in TL. exact TL.
    + eapply mst_step; [reflexivity | apply (step_branch_ft_gen segs regs pc1 mem rom w1 c2 p2 q2 i2 F1 E1 D1 B2) |].
      rewrite P2.
      replace (regupd regs Z vz) with regs
        by (symmetry; rewrite <- GZ, (getr_nz regs Z HZ); apply regupd_get_id; exact PZ).
      exact (TAIL2 regs GB GL).
Qed.

(* [comment removed for export] *)
Lemma bv_signed_Zs : forall a : Z, (- 2 ^ 63 <= a < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 a) = a.
Proof.
  intros a Ha. rewrite Z_to_bv_signed. apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63)%Z. lia.
Qed.

Lemma c_lts_Zs : forall a b : Z, (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof. intros a b Ha Hb. unfold c_lts, bv_lts. rewrite !bv_signed_Zs by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma and_srai63_np : forall x : Z, (- 2 ^ 63 <= x <= 0)%Z ->
  v_and (v_srai (Z_to_bv 64 x) 63) (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold v_srai. rewrite bv_signed_Zs by lia. rewrite Z.shiftr_div_pow2 by lia.
  destruct (Z.eq_dec x 0) as [->|NZ].
  - change (0 / 2 ^ 63)%Z with 0%Z. unfold v_and. rewrite u_Z2bv by lia. rewrite Z.land_0_l. reflexivity.
  - replace (x / 2 ^ 63)%Z with (-1)%Z.
    + unfold v_and. pose proof (u64_range (Z_to_bv 64 x)) as Hy.
      replace (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64) by (rewrite u_Z2bv_mod; reflexivity).
      rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. apply Z_to_bv_bv_unsigned.
    + apply Z.div_unique with (r := (x + 2 ^ 63)%Z); lia.
Qed.

(* [comment removed for export] *)
Lemma c_eq_Zs : forall a b : Z, (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b)%Z.
Proof.
  intros a b Ha Hb. unfold c_eq. destruct (Z.eqb_spec a b) as [->|NE]; [apply bv_eqb_refl|].
  apply bv_eqb_neq. intros E. apply NE. rewrite <- (bv_signed_Zs a Ha), <- (bv_signed_Zs b Hb), E. reflexivity.
Qed.

End GrayLib.

(* [comment removed for export] *)
Ltac gray_pcs := first [ reflexivity | apply bv_eq; reflexivity | (apply bv_eq; vm_compute; reflexivity) ].
Ltac gray_presence := repeat first [ apply reg_present_upd_same | apply reg_present_upd_other ]; assumption.
Ltac stepDIA F1 D1 F2 D2 :=
  eapply msteps_trans;
  [ eapply (diamond_mv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 eq_refl D1 F2 eq_refl D2);
    [ gray_pcs | gray_pcs | gray_pcs | reflexivity | discriminate | gray_presence | gres; reflexivity | gres; reflexivity | gres; reflexivity | gres; reflexivity ] | norm_pc ].
Ltac stepDIAJ F1 D1 F2 D2 F3 D3 :=
  eapply msteps_trans;
  [ eapply (diamond_mv_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 eq_refl D1 F2 eq_refl D2 F3 eq_refl D3);
    [ gray_pcs | gray_pcs | gray_pcs | gray_pcs | reflexivity | discriminate | gray_presence | gres; reflexivity | gres; reflexivity | gres; reflexivity | gres; reflexivity ] | norm_pc ].

(* [comment removed for export] *)
Ltac sel_guard :=
  cbn [branch_taken];
  lazymatch goal with
  | |- negb (bv_ltu ?a ?b) = true => change (negb (c_ltu a b) = true); rewrite c_ltu_Z by lia; apply Bool.negb_true_iff, Z.ltb_ge; lia
  | |- bv_ltu ?a ?b = false => change (c_ltu a b = false); rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia
  end.
Ltac stepSEL F0 D0 F1 D1 F2 D2 F3 D3 F5 D5 F6 D6 F7 D7 F8 D8 F9 D9 tv :=
  eapply msteps_trans;
  [ eapply sel_block with (t := tv);
    [ exact F0 | reflexivity | exact D0 | exact F1 | reflexivity | exact D1 | exact F2 | reflexivity | exact D2
    | exact F3 | reflexivity | exact D3 | exact F5 | reflexivity | exact D5 | exact F6 | reflexivity | exact D6
    | exact F7 | reflexivity | exact D7 | exact F8 | reflexivity | exact D8 | exact F9 | reflexivity | exact D9
    | gray_pcs | gray_pcs | gray_pcs | gray_pcs | gray_pcs | gray_pcs | gray_pcs | gray_pcs
    | gray_pcs | gray_pcs | gray_pcs | gray_pcs
    | reflexivity | reflexivity | reflexivity
    | discriminate | discriminate | discriminate | discriminate | discriminate | discriminate | discriminate | discriminate
    | discriminate | discriminate | discriminate | discriminate | discriminate
    | gray_presence | gray_presence
    | gres; reflexivity | gres; reflexivity | gres; reflexivity | gres; reflexivity | gres; reflexivity | gres; reflexivity
    | gres; reflexivity | gres; reflexivity | gres; reflexivity | gres; pin; reflexivity | gres; pin; reflexivity
    | imm_norm; rewrite ?zbv_addi; first [reflexivity | f_equal; lia] | sel_guard | sel_guard ]
  | norm_pc ].
