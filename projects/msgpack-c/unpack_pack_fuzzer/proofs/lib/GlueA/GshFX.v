(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import GshC.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS CtrLib GshC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GshFX.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Lemma load1_lit : forall E st ms mo a z,
  St.st_ok segs OPS E st ms mo -> do_load segs st a 1%uint63 false = inl (Some (VL z)) ->
  rb segs (ms_mem ms) (bv_unsigned (den E a)) = Some (Z_to_bv 8 (w2Z z)) /\ 0 <= w2Z z < 256.
Proof.
  intros E st ms mo a z HS H.
  assert (W1 : wok 1%uint63) by (left; reflexivity).
  destruct (do_load_sound segs OPS E st ms mo a 1%uint63 false (VL z) HS W1 H) as (bs & Len & OV & Dv).
  change (Z.to_nat (to_Z 1%uint63)) with 1%nat in Len, OV. change (to_Z 1%uint63) with 1 in Dv.
  destruct bs as [|b [|]]; try discriminate Len.
  assert (RB : rb segs (ms_mem ms) (bv_unsigned (den E a)) = Some b).
  { rewrite rb_unfold, Z_to_bv_bv_unsigned. cbn [ov_read_bytes] in OV.
    destruct (match ms_mem ms (den E a) with Some b0 => Some b0 | None => match memory_read segs (den E a) 1 with Some (b0 :: _) => Some b0 | _ => None end end) as [b0|]; [|discriminate OV].
    cbn in OV. injection OV as <-. reflexivity. }
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  assert (EZ : w2Z z = bv_unsigned b).
  { rewrite <- (bytes_val_ext_word false 1 [b] eq_refl ltac:(lia)) in Dv. unfold bytes_val in Dv. cbn [den] in Dv. unfold wbv in Dv.
    assert (EB : bytes_le_to_Z [b] = bv_unsigned b) by (rewrite bytes_le_to_Z_cons; cbn; lia).
    rewrite EB, (ext_Z_small_id false 1 (bv_unsigned b)) in Dv; [| lia| unfold two64; lia| change (2 ^ (8 * 1 - 0)) with 256; lia].
    apply (f_equal bv_unsigned) in Dv. rewrite !Z_to_bv_unsigned in Dv.
    pose proof (w2Z_range z) as RZ.
    rewrite (bv_wrap_small 64 (w2Z z)) in Dv by (rewrite bv_modulus_64; exact RZ).
    rewrite (bv_wrap_small 64 (bv_unsigned b)) in Dv by (rewrite bv_modulus_64; unfold two64; lia). exact Dv. }
  rewrite EZ. split; [| lia]. rewrite RB. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma den_lit : forall E (c : int), bv_unsigned (den E (VL (wlit c))) = to_Z c.
Proof.
  intros E c. cbn [den]. unfold wbv, w2Z, wlit. cbn [wt wl]. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof (to_Z_bounded c) as B. rewrite bv_modulus_64. unfold two64. change wB with (2 ^ 63) in B. lia.
Qed.

Lemma add_small : forall a i : int, to_Z a + to_Z i < 2 ^ 62 -> to_Z (PrimInt63.add a i) = to_Z a + to_Z i.
Proof.
  intros a i H. rewrite Uint63.add_spec. apply Z.mod_small. pose proof (to_Z_bounded a). pose proof (to_Z_bounded i). change wB with (2 ^ 63). lia.
Qed.

Lemma scan_nul_sound : forall fuel st a i len E ms mo,
  St.st_ok segs OPS E st ms mo -> scan_nul segs fuel st a i = Some len -> to_Z a + to_Z i + Z.of_nat fuel < 2 ^ 62 ->
  to_Z i <= to_Z len < to_Z i + Z.of_nat fuel
  /\ (forall j, to_Z i <= j < to_Z len -> exists b, rb segs (ms_mem ms) (to_Z a + j) = Some b /\ b <> Z_to_bv 8 0)
  /\ rb segs (ms_mem ms) (to_Z a + to_Z len) = Some (Z_to_bv 8 0).
Proof.
  induction fuel as [|f IH]; intros st a i len E ms mo HS H B; cbn [scan_nul] in H; [discriminate H|].
  destruct (do_load segs st (VL (wlit (PrimInt63.add a i))) 1%uint63 false) as [[v|]|] eqn:DL; try discriminate H.
  destruct v as [z| | | | | | | | | |]; try discriminate H.
  destruct (load1_lit E st ms mo _ z HS DL) as [RB RZ]. rewrite den_lit, (add_small a i ltac:(lia)) in RB.
  destruct (weqb z wzero) eqn:Q.
  - injection H as <-. apply weqb_eq in Q. subst z. change (w2Z wzero) with 0 in RB.
    split; [lia|]. split; [intros j Hj; lia| exact RB].
  - assert (I1 : to_Z (PrimInt63.add i 1%uint63) = to_Z i + 1) by (apply (add_small i 1%uint63); change (to_Z 1%uint63) with 1; pose proof (to_Z_bounded a); lia).
    destruct (IH st a (PrimInt63.add i 1%uint63) len E ms mo HS H ltac:(rewrite I1; lia)) as (L1 & NZ & ZR). rewrite I1 in L1, NZ.
    split; [lia|]. split; [| exact ZR].
    intros j Hj. destruct (Z.eq_dec j (to_Z i)) as [->|NE]; [| apply NZ; lia].
    exists (Z_to_bv 8 (w2Z z)). split; [exact RB|]. intros X.
    assert (W0 : w2Z z = 0).
    { apply (f_equal bv_unsigned) in X. rewrite !Z_to_bv_unsigned in X. rewrite bv_wrap_small in X by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia).
      exact X. }
    assert (ZE : z = wzero).
    { destruct z as [t l]. unfold w2Z in W0. cbn [wt wl] in W0. pose proof (to_Z_bounded l) as BL. destruct t; [unfold two63 in W0; lia|].
      unfold wzero. f_equal. apply to_Z_inj. change (to_Z 0%uint63) with 0. lia. }
    rewrite ZE in Q. change (weqb wzero wzero) with true in Q. discriminate Q.
Qed.

Lemma lit_loads_sound : forall fuel st a E ms mo,
  St.st_ok segs OPS E st ms mo -> lit_loads segs fuel st a = true -> to_Z a + Z.of_nat fuel < 2 ^ 62 ->
  forall j, 0 <= j < Z.of_nat fuel -> rb segs (ms_mem ms) (to_Z a + j) <> None.
Proof.
  induction fuel as [|f IH]; intros st a E ms mo HS H B j Hj; [lia|]. cbn [lit_loads] in H.
  destruct (do_load segs st (VL (wlit a)) 1%uint63 false) as [[v|]|] eqn:DL; try discriminate H.
  destruct v as [z| | | | | | | | | |]; try discriminate H.
  destruct (load1_lit E st ms mo _ z HS DL) as [RB _]. rewrite den_lit in RB.
  destruct (Z.eq_dec j 0) as [->|NE]; [rewrite Z.add_0_r, RB; discriminate|].
  assert (I1 : to_Z (PrimInt63.add a 1%uint63) = to_Z a + 1) by (apply (add_small a 1%uint63); change (to_Z 1%uint63) with 1; lia).
  pose proof (IH st (PrimInt63.add a 1%uint63) E ms mo HS H ltac:(rewrite I1; lia) (j - 1) ltac:(lia)) as X. rewrite I1 in X.
  replace (to_Z a + 1 + (j - 1)) with (to_Z a + j) in X by lia. exact X.
Qed.
End WithSegs.
End GshFX.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import GshC.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS CtrLib GshC.TwinB.GshC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GshFX.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Lemma load1_lit : forall E st ms mo a z,
  St.st_ok segs OPS E st ms mo -> do_load segs st a 1%uint63 false = inl (Some (VL z)) ->
  rb segs (ms_mem ms) (bv_unsigned (den E a)) = Some (Z_to_bv 8 (w2Z z)) /\ 0 <= w2Z z < 256.
Proof.
  intros E st ms mo a z HS H.
  assert (W1 : wok 1%uint63) by (left; reflexivity).
  destruct (do_load_sound segs OPS E st ms mo a 1%uint63 false (VL z) HS W1 H) as (bs & Len & OV & Dv).
  change (Z.to_nat (to_Z 1%uint63)) with 1%nat in Len, OV. change (to_Z 1%uint63) with 1 in Dv.
  destruct bs as [|b [|]]; try discriminate Len.
  assert (RB : rb segs (ms_mem ms) (bv_unsigned (den E a)) = Some b).
  { rewrite rb_unfold, Z_to_bv_bv_unsigned. cbn [ov_read_bytes] in OV.
    destruct (match ms_mem ms (den E a) with Some b0 => Some b0 | None => match memory_read segs (den E a) 1 with Some (b0 :: _) => Some b0 | _ => None end end) as [b0|]; [|discriminate OV].
    cbn in OV. injection OV as <-. reflexivity. }
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  assert (EZ : w2Z z = bv_unsigned b).
  { rewrite <- (bytes_val_ext_word false 1 [b] eq_refl ltac:(lia)) in Dv. unfold bytes_val in Dv. cbn [den] in Dv. unfold wbv in Dv.
    assert (EB : bytes_le_to_Z [b] = bv_unsigned b) by (rewrite bytes_le_to_Z_cons; cbn; lia).
    rewrite EB, (ext_Z_small_id false 1 (bv_unsigned b)) in Dv; [| lia| unfold two64; lia| change (2 ^ (8 * 1 - 0)) with 256; lia].
    apply (f_equal bv_unsigned) in Dv. rewrite !Z_to_bv_unsigned in Dv.
    pose proof (w2Z_range z) as RZ.
    rewrite (bv_wrap_small 64 (w2Z z)) in Dv by (rewrite bv_modulus_64; exact RZ).
    rewrite (bv_wrap_small 64 (bv_unsigned b)) in Dv by (rewrite bv_modulus_64; unfold two64; lia). exact Dv. }
  rewrite EZ. split; [| lia]. rewrite RB. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma den_lit : forall E (c : int), bv_unsigned (den E (VL (wlit c))) = to_Z c.
Proof.
  intros E c. cbn [den]. unfold wbv, w2Z, wlit. cbn [wt wl]. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof (to_Z_bounded c) as B. rewrite bv_modulus_64. unfold two64. change wB with (2 ^ 63) in B. lia.
Qed.

Lemma add_small : forall a i : int, to_Z a + to_Z i < 2 ^ 62 -> to_Z (PrimInt63.add a i) = to_Z a + to_Z i.
Proof.
  intros a i H. rewrite Uint63.add_spec. apply Z.mod_small. pose proof (to_Z_bounded a). pose proof (to_Z_bounded i). change wB with (2 ^ 63). lia.
Qed.

Lemma scan_nul_sound : forall fuel st a i len E ms mo,
  St.st_ok segs OPS E st ms mo -> scan_nul segs fuel st a i = Some len -> to_Z a + to_Z i + Z.of_nat fuel < 2 ^ 62 ->
  to_Z i <= to_Z len < to_Z i + Z.of_nat fuel
  /\ (forall j, to_Z i <= j < to_Z len -> exists b, rb segs (ms_mem ms) (to_Z a + j) = Some b /\ b <> Z_to_bv 8 0)
  /\ rb segs (ms_mem ms) (to_Z a + to_Z len) = Some (Z_to_bv 8 0).
Proof.
  induction fuel as [|f IH]; intros st a i len E ms mo HS H B; cbn [scan_nul] in H; [discriminate H|].
  destruct (do_load segs st (VL (wlit (PrimInt63.add a i))) 1%uint63 false) as [[v|]|] eqn:DL; try discriminate H.
  destruct v as [z| | | | | | | | | |]; try discriminate H.
  destruct (load1_lit E st ms mo _ z HS DL) as [RB RZ]. rewrite den_lit, (add_small a i ltac:(lia)) in RB.
  destruct (weqb z wzero) eqn:Q.
  - injection H as <-. apply weqb_eq in Q. subst z. change (w2Z wzero) with 0 in RB.
    split; [lia|]. split; [intros j Hj; lia| exact RB].
  - assert (I1 : to_Z (PrimInt63.add i 1%uint63) = to_Z i + 1) by (apply (add_small i 1%uint63); change (to_Z 1%uint63) with 1; pose proof (to_Z_bounded a); lia).
    destruct (IH st a (PrimInt63.add i 1%uint63) len E ms mo HS H ltac:(rewrite I1; lia)) as (L1 & NZ & ZR). rewrite I1 in L1, NZ.
    split; [lia|]. split; [| exact ZR].
    intros j Hj. destruct (Z.eq_dec j (to_Z i)) as [->|NE]; [| apply NZ; lia].
    exists (Z_to_bv 8 (w2Z z)). split; [exact RB|]. intros X.
    assert (W0 : w2Z z = 0).
    { apply (f_equal bv_unsigned) in X. rewrite !Z_to_bv_unsigned in X. rewrite bv_wrap_small in X by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia).
      exact X. }
    assert (ZE : z = wzero).
    { destruct z as [t l]. unfold w2Z in W0. cbn [wt wl] in W0. pose proof (to_Z_bounded l) as BL. destruct t; [unfold two63 in W0; lia|].
      unfold wzero. f_equal. apply to_Z_inj. change (to_Z 0%uint63) with 0. lia. }
    rewrite ZE in Q. change (weqb wzero wzero) with true in Q. discriminate Q.
Qed.

Lemma lit_loads_sound : forall fuel st a E ms mo,
  St.st_ok segs OPS E st ms mo -> lit_loads segs fuel st a = true -> to_Z a + Z.of_nat fuel < 2 ^ 62 ->
  forall j, 0 <= j < Z.of_nat fuel -> rb segs (ms_mem ms) (to_Z a + j) <> None.
Proof.
  induction fuel as [|f IH]; intros st a E ms mo HS H B j Hj; [lia|]. cbn [lit_loads] in H.
  destruct (do_load segs st (VL (wlit a)) 1%uint63 false) as [[v|]|] eqn:DL; try discriminate H.
  destruct v as [z| | | | | | | | | |]; try discriminate H.
  destruct (load1_lit E st ms mo _ z HS DL) as [RB _]. rewrite den_lit in RB.
  destruct (Z.eq_dec j 0) as [->|NE]; [rewrite Z.add_0_r, RB; discriminate|].
  assert (I1 : to_Z (PrimInt63.add a 1%uint63) = to_Z a + 1) by (apply (add_small a 1%uint63); change (to_Z 1%uint63) with 1; lia).
  pose proof (IH st (PrimInt63.add a 1%uint63) E ms mo HS H ltac:(rewrite I1; lia) (j - 1) ltac:(lia)) as X. rewrite I1 in X.
  replace (to_Z a + 1 + (j - 1)) with (to_Z a + j) in X by lia. exact X.
Qed.
End WithSegs.
End GshFX.
End TwinB.
