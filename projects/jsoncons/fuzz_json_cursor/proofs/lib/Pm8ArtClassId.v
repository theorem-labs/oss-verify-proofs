(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac As0StepLib As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_5d000_5e000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Lemma art_brute_eq : forall (f g : Z -> word) (lo : Z) (n : Z),
  forallb (fun z => bv_eqb (f z) (g z)) (AsanTab.zrange lo n) = true ->
  forall z, (lo <= z < lo + n)%Z -> f z = g z.
Proof.
  intros f g lo n H z Hz. rewrite forallb_forall in H.
  assert (Hin : In z (AsanTab.zrange lo n)) by (unfold AsanTab.zrange; apply AsanTab.in_ziota; rewrite Z2Nat.id; lia).
  specialize (H z Hin). cbn beta in H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Ltac art_step F D :=
  stepn F D;
  try (lazymatch goal with
       | |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ =>
           lazymatch v with
           | Z_to_bv 64 ?z => is_Z_lit z
           | _ => let x := fresh "x" in remember v as x
           end
       end).

Section FPX. Context {fx : PropExec.FPState}.

Definition art_cid_w (s : word) : word :=
  let x1 := (v_srli s (1)%Z) in
  let x2 := (v_or s x1) in
  let x3 := (v_srli x2 (2)%Z) in
  let x4 := (v_or x2 x3) in
  let x5 := (v_srli x4 (4)%Z) in
  let x6 := (v_or x4 x5) in
  let x7 := (v_srli x6 (8)%Z) in
  let x8 := (v_or x6 x7) in
  let x9 := (v_srli x8 (16)%Z) in
  let x10 := (v_or x8 x9) in
  let x11 := (v_srli x10 (32)%Z) in
  let x12 := (v_or x10 x11) in
  let x13 := (v_xori x12 (-1)%Z) in
  let x14 := (v_srli x13 (1)%Z) in
  let x15 := (v_and x14 (Z_to_bv 64 6148914691236517205)) in
  let x16 := (v_sub x13 x15) in
  let x17 := (v_and x16 (Z_to_bv 64 3689348814741910323)) in
  let x18 := (v_srli x16 (2)%Z) in
  let x19 := (v_and x18 (Z_to_bv 64 3689348814741910323)) in
  let x20 := (v_add x17 x19) in
  let x21 := (v_srli x20 (4)%Z) in
  let x22 := (v_add x20 x21) in
  let x23 := (v_and x22 (Z_to_bv 64 1085102592571150095)) in
  let x24 := (v_mul x23 (Z_to_bv 64 72340172838076673)) in
  let x25 := (v_srli x24 (56)%Z) in
  let x26 := (v_subw (Z_to_bv 64 62) x25) in
  let x27 := (v_slli x25 (1)%Z) in
  let x28 := (v_srl s x26) in
  let x29 := (v_sllw (Z_to_bv 64 18446744073709551615) x26) in
  let x30 := (v_xori x27 (126)%Z) in
  let x31 := (v_andi x28 (1)%Z) in
  let x32 := (v_xori x29 (-1)%Z) in
  let x33 := (v_and s x32) in
  let x34 := (v_or x30 x31) in
  let x35 := (v_sltu (Z_to_bv 64 0) x33) in
  let x36 := (v_add x34 x35) in
  let x37 := (v_addi x36 (-2)%Z) in
  x37.

Definition art_cid_z (u : Z) : Z :=
  let y1 := ((Z.shiftr u 1) mod 18446744073709551616) in
  let y2 := ((Z.lor u y1) mod 18446744073709551616) in
  let y3 := ((Z.shiftr y2 2) mod 18446744073709551616) in
  let y4 := ((Z.lor y2 y3) mod 18446744073709551616) in
  let y5 := ((Z.shiftr y4 4) mod 18446744073709551616) in
  let y6 := ((Z.lor y4 y5) mod 18446744073709551616) in
  let y7 := ((Z.shiftr y6 8) mod 18446744073709551616) in
  let y8 := ((Z.lor y6 y7) mod 18446744073709551616) in
  let y9 := ((Z.shiftr y8 16) mod 18446744073709551616) in
  let y10 := ((Z.lor y8 y9) mod 18446744073709551616) in
  let y11 := ((Z.shiftr y10 32) mod 18446744073709551616) in
  let y12 := ((Z.lor y10 y11) mod 18446744073709551616) in
  let y13 := ((Z.lxor y12 ((-1) mod 18446744073709551616)) mod 18446744073709551616) in
  let y14 := ((Z.shiftr y13 1) mod 18446744073709551616) in
  let y15 := ((Z.land y14 (6148914691236517205 mod 18446744073709551616)) mod 18446744073709551616) in
  let y16 := ((y13 - y15) mod 18446744073709551616) in
  let y17 := ((Z.land y16 (3689348814741910323 mod 18446744073709551616)) mod 18446744073709551616) in
  let y18 := ((Z.shiftr y16 2) mod 18446744073709551616) in
  let y19 := ((Z.land y18 (3689348814741910323 mod 18446744073709551616)) mod 18446744073709551616) in
  let y20 := ((y17 + y19) mod 18446744073709551616) in
  let y21 := ((Z.shiftr y20 4) mod 18446744073709551616) in
  let y22 := ((y20 + y21) mod 18446744073709551616) in
  let y23 := ((Z.land y22 (1085102592571150095 mod 18446744073709551616)) mod 18446744073709551616) in
  let y24 := ((y23 * (72340172838076673 mod 18446744073709551616)) mod 18446744073709551616) in
  let y25 := ((Z.shiftr y24 56) mod 18446744073709551616) in
  let y26 := ((((((62 mod 18446744073709551616) - y25) + 4294967296 `div` 2) mod 4294967296 - 4294967296 `div` 2)) mod 18446744073709551616) in
  let y27 := ((Z.shiftl y25 1) mod 18446744073709551616) in
  let y28 := ((Z.shiftr u (y26 mod 64)) mod 18446744073709551616) in
  let y29 := (((((Z.shiftl (18446744073709551615 mod 18446744073709551616) (y26 mod 32)) + 4294967296 `div` 2) mod 4294967296 - 4294967296 `div` 2)) mod 18446744073709551616) in
  let y30 := ((Z.lxor y27 ((126) mod 18446744073709551616)) mod 18446744073709551616) in
  let y31 := ((Z.land y28 ((1) mod 18446744073709551616)) mod 18446744073709551616) in
  let y32 := ((Z.lxor y29 ((-1) mod 18446744073709551616)) mod 18446744073709551616) in
  let y33 := ((Z.land u y32) mod 18446744073709551616) in
  let y34 := ((Z.lor y30 y31) mod 18446744073709551616) in
  let y35 := (if ((0 mod 18446744073709551616) <? y33) then (1 mod 18446744073709551616) else (0 mod 18446744073709551616)) in
  let y36 := ((y34 + y35) mod 18446744073709551616) in
  let y37 := ((y36 + (-2)) mod 18446744073709551616) in
  y37.

Lemma art_u_if : forall (b : bool) (x y : word), bv_unsigned (if b then x else y) = (if b then bv_unsigned x else bv_unsigned y).
Proof. intros [|] x y; reflexivity. Qed.

Lemma art_cid_wz : forall s, bv_unsigned (art_cid_w s) = art_cid_z (bv_unsigned s).
Proof.
  intros s. unfold art_cid_w, art_cid_z. cbv zeta.
  unfold v_srli, v_slli, v_or, v_and, v_xori, v_andi, v_addi, v_add, v_sub, v_mul, v_subw, v_srl, v_sllw, v_sltu, c_ltu, bv_ltu.
  rewrite ?art_u_if. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus.
  change (bv_modulus 64) with 18446744073709551616%Z. change (bv_modulus 32) with 4294967296%Z.
  reflexivity.
Qed.

Definition art_zr8 : list Z := map (fun i => 8 * i)%Z (AsanTab.zrange 65 8128).

Lemma art_cid_z_ok : forallb (fun z => Z.eqb (art_cid_z z) (AsanTab.class_id z)) art_zr8 = true.
Proof.
  lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end.
Qed.

Lemma art_cid_w_ok : forall z, (513 <= z <= 65536)%Z -> (z mod 8 = 0)%Z -> art_cid_w (Z_to_bv 64 z) = Z_to_bv 64 (AsanTab.class_id z).
Proof.
  intros z Hz H8. apply bv_eq. rewrite art_cid_wz, !Z_to_bv_unsigned.
  pose proof art_cid_z_ok as H. rewrite forallb_forall in H.
  assert (Hin : In z art_zr8).
  { unfold art_zr8. apply in_map_iff. exists (z / 8)%Z. split; [|unfold AsanTab.zrange; apply AsanTab.in_ziota; lia].
    pose proof (Z.div_mod z 8 ltac:(lia)). lia. }
  specialize (H z Hin). cbn beta in H. apply Z.eqb_eq in H.
  pose proof (AsanTab.class_id_ok z ltac:(lia)) as (Hc & _).
  unfold bv_wrap. rewrite !Z.mod_small by (change (bv_modulus 64) with (2^64)%Z; lia). exact H.
Qed.

Definition art_cid_kept (r : reg) : Prop :=
  r <> 8%bv /\ r <> 12%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv /\ r <> 5%bv /\ r <> 6%bv.

Lemma art_classid_hi_run : forall regs (M rom : word -> option byte) (s : word),
  getr regs 14 = s ->
  exists regs',
    msteps ASEGS (mkst regs (0x5dc6c : word) M rom) (mkst regs' (0x5dd48 : word) M rom)
    /\ getr regs' 8 = art_cid_w s
    /\ (forall r : reg, art_cid_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom s H14.
  pose (x1 := (v_srli s (1)%Z)). assert (E1 : x1 = (v_srli s (1)%Z)) by reflexivity. clearbody x1.
  pose (x2 := (v_or s x1)). assert (E2 : x2 = (v_or s x1)) by reflexivity. clearbody x2.
  pose (x3 := (v_srli x2 (2)%Z)). assert (E3 : x3 = (v_srli x2 (2)%Z)) by reflexivity. clearbody x3.
  pose (x4 := (v_or x2 x3)). assert (E4 : x4 = (v_or x2 x3)) by reflexivity. clearbody x4.
  pose (x5 := (v_srli x4 (4)%Z)). assert (E5 : x5 = (v_srli x4 (4)%Z)) by reflexivity. clearbody x5.
  pose (x6 := (v_or x4 x5)). assert (E6 : x6 = (v_or x4 x5)) by reflexivity. clearbody x6.
  pose (x7 := (v_srli x6 (8)%Z)). assert (E7 : x7 = (v_srli x6 (8)%Z)) by reflexivity. clearbody x7.
  pose (x8 := (v_or x6 x7)). assert (E8 : x8 = (v_or x6 x7)) by reflexivity. clearbody x8.
  pose (x9 := (v_srli x8 (16)%Z)). assert (E9 : x9 = (v_srli x8 (16)%Z)) by reflexivity. clearbody x9.
  pose (x10 := (v_or x8 x9)). assert (E10 : x10 = (v_or x8 x9)) by reflexivity. clearbody x10.
  pose (x11 := (v_srli x10 (32)%Z)). assert (E11 : x11 = (v_srli x10 (32)%Z)) by reflexivity. clearbody x11.
  pose (x12 := (v_or x10 x11)). assert (E12 : x12 = (v_or x10 x11)) by reflexivity. clearbody x12.
  pose (x13 := (v_xori x12 (-1)%Z)). assert (E13 : x13 = (v_xori x12 (-1)%Z)) by reflexivity. clearbody x13.
  pose (x14 := (v_srli x13 (1)%Z)). assert (E14 : x14 = (v_srli x13 (1)%Z)) by reflexivity. clearbody x14.
  pose (x15 := (v_and x14 (Z_to_bv 64 6148914691236517205))). assert (E15 : x15 = (v_and x14 (Z_to_bv 64 6148914691236517205))) by reflexivity. clearbody x15.
  pose (x16 := (v_sub x13 x15)). assert (E16 : x16 = (v_sub x13 x15)) by reflexivity. clearbody x16.
  pose (x17 := (v_and x16 (Z_to_bv 64 3689348814741910323))). assert (E17 : x17 = (v_and x16 (Z_to_bv 64 3689348814741910323))) by reflexivity. clearbody x17.
  pose (x18 := (v_srli x16 (2)%Z)). assert (E18 : x18 = (v_srli x16 (2)%Z)) by reflexivity. clearbody x18.
  pose (x19 := (v_and x18 (Z_to_bv 64 3689348814741910323))). assert (E19 : x19 = (v_and x18 (Z_to_bv 64 3689348814741910323))) by reflexivity. clearbody x19.
  pose (x20 := (v_add x17 x19)). assert (E20 : x20 = (v_add x17 x19)) by reflexivity. clearbody x20.
  pose (x21 := (v_srli x20 (4)%Z)). assert (E21 : x21 = (v_srli x20 (4)%Z)) by reflexivity. clearbody x21.
  pose (x22 := (v_add x20 x21)). assert (E22 : x22 = (v_add x20 x21)) by reflexivity. clearbody x22.
  pose (x23 := (v_and x22 (Z_to_bv 64 1085102592571150095))). assert (E23 : x23 = (v_and x22 (Z_to_bv 64 1085102592571150095))) by reflexivity. clearbody x23.
  pose (x24 := (v_mul x23 (Z_to_bv 64 72340172838076673))). assert (E24 : x24 = (v_mul x23 (Z_to_bv 64 72340172838076673))) by reflexivity. clearbody x24.
  pose (x25 := (v_srli x24 (56)%Z)). assert (E25 : x25 = (v_srli x24 (56)%Z)) by reflexivity. clearbody x25.
  pose (x26 := (v_subw (Z_to_bv 64 62) x25)). assert (E26 : x26 = (v_subw (Z_to_bv 64 62) x25)) by reflexivity. clearbody x26.
  pose (x27 := (v_slli x25 (1)%Z)). assert (E27 : x27 = (v_slli x25 (1)%Z)) by reflexivity. clearbody x27.
  pose (x28 := (v_srl s x26)). assert (E28 : x28 = (v_srl s x26)) by reflexivity. clearbody x28.
  pose (x29 := (v_sllw (Z_to_bv 64 18446744073709551615) x26)). assert (E29 : x29 = (v_sllw (Z_to_bv 64 18446744073709551615) x26)) by reflexivity. clearbody x29.
  pose (x30 := (v_xori x27 (126)%Z)). assert (E30 : x30 = (v_xori x27 (126)%Z)) by reflexivity. clearbody x30.
  pose (x31 := (v_andi x28 (1)%Z)). assert (E31 : x31 = (v_andi x28 (1)%Z)) by reflexivity. clearbody x31.
  pose (x32 := (v_xori x29 (-1)%Z)). assert (E32 : x32 = (v_xori x29 (-1)%Z)) by reflexivity. clearbody x32.
  pose (x33 := (v_and s x32)). assert (E33 : x33 = (v_and s x32)) by reflexivity. clearbody x33.
  pose (x34 := (v_or x30 x31)). assert (E34 : x34 = (v_or x30 x31)) by reflexivity. clearbody x34.
  pose (x35 := (v_sltu (Z_to_bv 64 0) x33)). assert (E35 : x35 = (v_sltu (Z_to_bv 64 0) x33)) by reflexivity. clearbody x35.
  pose (x36 := (v_add x34 x35)). assert (E36 : x36 = (v_add x34 x35)) by reflexivity. clearbody x36.
  pose (x37 := (v_addi x36 (-2)%Z)). assert (E37 : x37 = (v_addi x36 (-2)%Z)) by reflexivity. clearbody x37.
  eexists. split; [|split].
  - rwH.
      stepn F_5dc1c D_5dc1c. rwH. rewrite <- E1.
      stepn F_5dc20 D_5dc20.
      stepn F_5dc24 D_5dc24.
      stepn F_5dc28 D_5dc28.
      stepn F_5dc2c D_5dc2c.
      stepn F_5dc30 D_5dc30. rwH. rewrite <- E2.
      stepn F_5dc34 D_5dc34.
      stepn F_5dc38 D_5dc38.
      stepn F_5dc3c D_5dc3c.
      stepn F_5dc40 D_5dc40.
      stepn F_5dc44 D_5dc44. rwH. rewrite <- E3.
      stepn F_5dc48 D_5dc48. rwH. rewrite <- E4.
      stepn F_5dc4c D_5dc4c.
      stepn F_5dc50 D_5dc50.
      stepn F_5dc54 D_5dc54.
      stepn F_5dc58 D_5dc58.
      stepn F_5dc5c D_5dc5c.
      stepn F_5dc60 D_5dc60.
      stepn F_5dc64 D_5dc64.
      stepn F_5dc68 D_5dc68.
      stepn F_5dc6c D_5dc6c. rwH. rewrite <- E5.
      stepn F_5dc70 D_5dc70. rwH. rewrite <- E6.
      stepn F_5dc74 D_5dc74. rwH. rewrite <- E7.
      stepn F_5dc78 D_5dc78. rwH. rewrite <- E8.
      stepn F_5dc7c D_5dc7c. rwH. rewrite <- E9.
      stepn F_5dc80 D_5dc80. rwH. rewrite <- E10.
      stepn F_5dc84 D_5dc84. rwH. rewrite <- E11.
      stepn F_5dc88 D_5dc88. rwH. rewrite <- E12.
      stepn F_5dc8c D_5dc8c. rwH. rewrite <- E13.
      stepn F_5dc90 D_5dc90. rwH. rewrite <- E14.
      stepn F_5dc94 D_5dc94. rwH. rewrite <- E15.
      stepn F_5dc98 D_5dc98. rwH. rewrite <- E16.
      stepn F_5dc9c D_5dc9c. rwH. rewrite <- E17.
      stepn F_5dca0 D_5dca0. rwH. rewrite <- E18.
      stepn F_5dca4 D_5dca4. rwH. rewrite <- E19.
      stepn F_5dca8 D_5dca8. rwH. rewrite <- E20.
      stepn F_5dcac D_5dcac. rwH. rewrite <- E21.
      stepn F_5dcb0 D_5dcb0. rwH. rewrite <- E22.
      stepn F_5dcb4 D_5dcb4.
      stepn F_5dcb8 D_5dcb8. rwH. rewrite <- E23.
      stepn F_5dcbc D_5dcbc.
      stepn F_5dcc0 D_5dcc0. rwH. rewrite <- E24.
      stepn F_5dcc4 D_5dcc4. rwH. rewrite <- E25.
      stepn F_5dcc8 D_5dcc8. rwH. rewrite <- E26.
      stepn F_5dccc D_5dccc. rwH. rewrite <- E27.
      stepn F_5dcd0 D_5dcd0. rwH. rewrite <- E28.
      stepn F_5dcd4 D_5dcd4. rwH. rewrite <- E29.
      stepn F_5dcd8 D_5dcd8. rwH. rewrite <- E30.
      stepn F_5dcdc D_5dcdc. rwH. rewrite <- E31.
      stepn F_5dce0 D_5dce0. rwH. rewrite <- E32.
      stepn F_5dce4 D_5dce4. rwH. rewrite <- E33.
      stepn F_5dce8 D_5dce8. rwH. rewrite <- E34.
      stepn F_5dcec D_5dcec. rwH. rewrite <- E35.
      stepn F_5dcf0 D_5dcf0. rwH. rewrite <- E36.
      stepn F_5dcf4 D_5dcf4. rwH. rewrite <- E37.
      apply mst_refl.
  - gres. subst. reflexivity.
  - intros r (H8 & H12 & H14' & H15 & H16 & H17 & H5 & H6). gres.
    repeat (rewrite getr_other by (first [exact H8|exact H12|exact H14'|exact H15|exact H16|exact H17|exact H5|exact H6|
      (intros E; first [apply H8|apply H12|apply H14'|apply H15|apply H16|apply H17|apply H5|apply H6]; exact (eq_sym E))])).
    reflexivity.
Qed.
End FPX.
