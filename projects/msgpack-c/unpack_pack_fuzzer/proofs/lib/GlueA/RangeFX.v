(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require CopyFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RangeC.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS CtrLib RangeC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module RangeFX.

Lemma w2Zs_wadd_lit : forall o (n : int) k0 k1, okey o = Some k0 -> okey (wadd o (wlit n)) = Some k1 -> 0 <= to_Z n <= 2 ^ 32 ->
  w2Zs (wadd o (wlit n)) = w2Zs o + to_Z n.
Proof.
  intros o n k0 k1 H0 H1 Hn. destruct (okey_sound _ _ H0) as [E0 R0]. destruct (okey_sound _ _ H1) as [E1 R1].
  rewrite E0 in R0. rewrite E1 in R1. change (- two63 / 2) with (- 2 ^ 62) in *. change (two63 / 2) with (2 ^ 62) in *.
  pose proof (wadd_ok o (wlit n)) as WA. rewrite wlit_ok in WA.
  rewrite !w2Zs_eq in *. pose proof (w2Z_range o) as RO. pose proof (w2Z_range (wadd o (wlit n))) as RA. unfold two64 in *.
  destruct (wt o), (wt (wadd o (wlit n))); Z.div_mod_to_equations; lia.
Qed.

Lemma in_region_sound : forall E r o len, in_region r o len = true -> 0 <= to_Z len <= 2 ^ 32 ->
  loZ r <= w2Zs o /\ w2Zs o + to_Z len <= hiZ E r /\ - 2 ^ 62 <= w2Zs o < 2 ^ 62.
Proof.
  intros E r o len H Hl. unfold in_region in H.
  destruct (okey o) as [k0|] eqn:K0; [|discriminate H]. destruct (okey (wadd o (wlit len))) as [k1|] eqn:K1; [|discriminate H].
  destruct (rg_hi r) as [hi| | | | | | | | | |] eqn:RH; try discriminate H.
  destruct (okey hi) as [kh|] eqn:KH; [| apply andb_prop in H as [_ H]; discriminate H].
  repeat match type of H with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in H as [H X] end.
  apply negb_true_iff in Q0. rewrite kleb_keyZ in H, Q1, Q. apply Z.leb_le in H, Q1, Q.
  destruct (okey_sound _ _ K0) as [E0 R0]. destruct (okey_sound _ _ K1) as [E1 R1]. destruct (okey_sound _ _ KH) as [EH RHr].
  rewrite (w2Zs_wadd_lit o len k0 k1 K0 K1 Hl) in E1.
  assert (HZ : hiZ E r = w2Zs hi).
  { unfold hiZ. rewrite RH. cbn [den]. rewrite wbv_unsigned, w2Zs_eq, Q0. lia. }
  change (- two63 / 2) with (- 2 ^ 62) in *. change (two63 / 2) with (2 ^ 62) in *. unfold loZ. rewrite HZ. unfold St.keyZ in *. lia.
Qed.

Lemma in_region_end : forall r o len, in_region r o len = true -> 0 <= to_Z len <= 2 ^ 32 ->
  w2Zs (wadd o (wlit len)) = w2Zs o + to_Z len.
Proof.
  intros r o len H Hl. unfold in_region in H.
  destruct (okey o) as [k0|] eqn:K0; [|discriminate H]. destruct (okey (wadd o (wlit len))) as [k1|] eqn:K1; [|discriminate H].
  exact (w2Zs_wadd_lit o len k0 k1 K0 K1 Hl).
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.

Lemma den_add1 : forall E a, den E (sv_alu ALU_ADD a (VL (wlit 1%uint63))) = (den E a + Z_to_bv 64 1)%bv.
Proof. intros E a. rewrite den_sv_alu. cbn [alu64 alu den]. unfold wbv. rewrite wlit_ok. reflexivity. Qed.

Lemma zero_loads_sound : forall fuel st p E ms mo,
  St.st_ok segs OPS E st ms mo -> zero_loads segs fuel st p = true ->
  forall j, 0 <= j < Z.of_nat fuel -> rb segs (ms_mem ms) (bv_unsigned (den E p) + j) = Some (Z_to_bv 8 0).
Proof.
  induction fuel as [|fuel IH]; intros st p E ms mo HS H j Hj; [lia|].
  cbn [zero_loads] in H.
  destruct (do_load segs st p 1%uint63 false) as [[v|]|] eqn:DL; try discriminate H.
  destruct v as [z| | | | | | | | | |]; try discriminate H. apply andb_prop in H as [HZ H]. apply weqb_eq in HZ. subst z.
  destruct (CopyFX.CopyFX.load1_where segs OPS E st ms mo p (VL wzero) HS DL) as (k & b & _ & _ & B1 & RB & SB & _).
  assert (B0 : b = Z_to_bv 8 0).
  { cbn [den] in SB. change (store_bytes 1%uint63 (wbv wzero)) with [Z_to_bv 8 0] in SB. injection SB as <-. reflexivity. }
  subst b. destruct (Z.eq_dec j 0) as [->|NZ]; [rewrite Z.add_0_r; exact RB|].
  pose proof (IH st (sv_alu ALU_ADD p (VL (wlit 1%uint63))) E ms mo HS H (j - 1) ltac:(lia)) as X.
  rewrite den_add1, bv_add_unsigned in X. change (bv_unsigned (Z_to_bv 64 1)) with 1 in X.
  pose proof (bv_unsigned_in_range _ (den E p)) as RP. unfold bv_modulus in RP.
  rewrite bv_wrap_small in X by (unfold bv_modulus, two64 in *; lia).
  replace (bv_unsigned (den E p) + 1 + (j - 1)) with (bv_unsigned (den E p) + j) in X by lia. exact X.
Qed.

Lemma shad_den : forall (X : word), bv_unsigned X < 2 ^ 47 ->
  bv_unsigned (alu64 ALU_ADD (alu64 ALU_SRL X (wbv (wlit 3%uint63))) (wbv SBw)) = 2147450880 + bv_unsigned X / 8.
Proof.
  intros X HX. cbn [alu64 alu]. rewrite bv_add_unsigned, bv_shiftr_unsigned.
  change (bv_unsigned (bv_and (wbv (wlit 3%uint63)) (Z_to_bv 64 63))) with 3.
  change (bv_unsigned (wbv SBw)) with 2147450880.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (bv_unsigned_in_range _ X) as RX. unfold bv_modulus in RX.
  rewrite bv_wrap_small; [lia|]. unfold bv_modulus. pose proof (Z.div_pos (bv_unsigned X) 8). Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_zero_sound : forall st k o len E ms mo,
  St.st_ok segs OPS E st ms mo -> shadow_zero segs st k o len = true -> 0 <= to_Z len ->
  let A := bv_unsigned (den E (VP k o)) in A < 2 ^ 47 ->
  forall G, A <= 8 * G + 7 -> 8 * G < A + to_Z len -> rb segs (ms_mem ms) (2147450880 + G) = Some (Z_to_bv 8 0).
Proof.
  intros st k o len E ms mo HS H Hl A HA G G1 G2. unfold shadow_zero in H.
  destruct (shadow_fold (s_facts st) (VAlu ALU_SRL (VP k o) (VL (wlit 3%uint63))) (VL SBw)) as [p|] eqn:SF; [|discriminate H].
  pose proof (shadow_fold_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) _ _ _ SF) as DP.
  cbn [den] in DP. fold (den E (VP k o)) in DP.
  assert (EP : bv_unsigned (den E p) = 2147450880 + A / 8) by (rewrite DP; apply shad_den; exact HA).
  pose proof (bv_unsigned_in_range _ (den E (VP k o))) as RA. fold A in RA.
  pose proof (zero_loads_sound _ st p E ms mo HS H (G - A / 8)) as X. rewrite EP in X.
  replace (2147450880 + A / 8 + (G - A / 8)) with (2147450880 + G) in X by lia. apply X.
  unfold shadow_zero_need. destruct (aligned (s_facts st) (VP k o) 3%uint63) eqn:AL.
  -
    pose proof (aligned_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) (VP k o) 3%uint63 AL ltac:(change (to_Z 3%uint63) with 3; lia)) as MA.
    change (2 ^ to_Z 3%uint63) with 8 in MA. fold A in MA.
    rewrite Z2Nat.id by (apply Z.div_pos; lia). Z.div_mod_to_equations. lia.
  - rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia). change (Z.of_nat 1) with 1.
    Z.div_mod_to_equations. lia.
Qed.

Lemma byte_of_lit : forall (E : env) (z : w64) (b : byte), store_bytes 1%uint63 (den E (VL z)) = [b] -> w2Z z < 256 -> bv_unsigned b = w2Z z.
Proof.
  intros E z b SB HZ. rewrite <- store_bytes_8 in SB. cbn [den] in SB.
  unfold Z_to_le_bytes in SB. cbn in SB. injection SB as <-.
  rewrite Z_to_bv_unsigned. rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  rewrite wbv_unsigned. pose proof (w2Z_range z) as R.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma gran_loads_sound : forall fuel need st p E ms mo,
  St.st_ok segs OPS E st ms mo -> gran_loads segs fuel need st p = true ->
  forall j, 0 <= j < Z.of_nat fuel -> exists b, rb segs (ms_mem ms) (bv_unsigned (den E p) + j) = Some b /\
     (bv_unsigned b = 0 \/ (j = Z.of_nat fuel - 1 /\ to_Z need <= bv_unsigned b <= 7)).
Proof.
  induction fuel as [|fuel IH]; intros need st p E ms mo HS H j Hj; [lia|].
  cbn [gran_loads] in H.
  destruct (do_load segs st p 1%uint63 false) as [[v|]|] eqn:DL; try discriminate H.
  destruct v as [z| | | | | | | | | |]; try discriminate H. apply andb_prop in H as [HZ H].
  destruct (CopyFX.CopyFX.load1_where segs OPS E st ms mo p (VL z) HS DL) as (k & b & _ & _ & B1 & RB & SB & _).
  destruct (Z.eq_dec j 0) as [->|NZ].
  - rewrite Z.add_0_r. exists b. split; [exact RB|].
    apply orb_prop in HZ. destruct HZ as [HZ|HZ].
    + left. apply weqb_eq in HZ. subst z. apply (byte_of_lit E wzero b SB). change (w2Z wzero) with 0. lia.
    + right. destruct fuel as [|f']; [| discriminate HZ].
      apply andb_prop in HZ as [HZ L7]. apply andb_prop in HZ as [WT LN]. apply negb_true_iff in WT.
      apply Uint63.leb_spec in L7, LN. change (to_Z 7%uint63) with 7 in L7.
      assert (EZ : w2Z z = to_Z (wl z)) by (unfold w2Z; rewrite WT; lia).
      rewrite (byte_of_lit E z b SB) by lia. cbn [Z.of_nat]. lia.
  - destruct (IH need st (sv_alu ALU_ADD p (VL (wlit 1%uint63))) E ms mo HS H (j - 1) ltac:(lia)) as (b' & RB' & GB).
    rewrite den_add1, bv_add_unsigned in RB'. change (bv_unsigned (Z_to_bv 64 1)) with 1 in RB'.
    pose proof (bv_unsigned_in_range _ (den E p)) as RP. unfold bv_modulus in RP.
    rewrite bv_wrap_small in RB' by (unfold bv_modulus, two64 in *; lia).
    replace (bv_unsigned (den E p) + 1 + (j - 1)) with (bv_unsigned (den E p) + j) in RB' by lia.
    exists b'. split; [exact RB'|]. destruct GB as [G0|[GJ GN]]; [left; exact G0| right; split; [lia| exact GN]].
Qed.

Lemma shadow_ok_x_sound : forall st k o len E ms mo,
  St.st_ok segs OPS E st ms mo -> shadow_ok_x segs st k o len = true -> 1 <= to_Z len <= 2 ^ 40 ->
  let A := bv_unsigned (ev E k) + w2Z o in A < 2 ^ 47 ->
  forall G, A <= 8 * G + 7 -> 8 * G < A + to_Z len ->
    exists b, rb segs (ms_mem ms) (2147450880 + G) = Some b /\ (bv_unsigned b = 0 \/ (Z.min (8 * G + 8) (A + to_Z len) - 8 * G <= bv_unsigned b <= 7)).
Proof.
  intros st k o len E ms mo HS H Hl A HA G G1 G2. unfold shadow_ok_x in H. cbv zeta in H.
  apply andb_prop in H as [H GL]. apply andb_prop in H as [AL WT]. apply negb_true_iff in WT.
  destruct (shadow_fold (s_facts st) (VAlu ALU_SRL (VP k o) (VL (wlit 3%uint63))) (VL SBw)) as [p|] eqn:SF; [|discriminate GL].
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  pose proof (shadow_fold_sound E (s_facts st) Hfs _ _ _ SF) as DP. cbn [den] in DP. fold (den E (VP k o)) in DP.
  pose proof (aligned_sound E _ Hfs _ _ AL ltac:(change (to_Z 3%uint63) with 3; lia)) as AL8. change (2 ^ to_Z 3%uint63) with 8 in AL8.
  assert (EO : w2Z o = to_Z (wl o)) by (unfold w2Z; rewrite WT; lia).
  pose proof (bv_unsigned_in_range _ (ev E k)) as RK. unfold bv_modulus in RK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RK.
  pose proof (w2Z_range o) as RO.
  assert (DVK : bv_unsigned (den E (VP k wzero)) = bv_unsigned (ev E k)).
  { rewrite den_VP. change (w2Zs wzero) with 0. rewrite Z.add_0_r. apply Z.mod_small. unfold two64. lia. }
  rewrite DVK in AL8.
  assert (DVA : bv_unsigned (den E (VP k o)) = A).
  { rewrite den_VP. rewrite w2Zs_eq, WT. unfold A. rewrite Z.sub_0_r. apply Z.mod_small. unfold two64, A in *. lia. }
  assert (EP : bv_unsigned (den E p) = 2147450880 + A / 8) by (rewrite DP; rewrite <- DVA; apply shad_den; rewrite DVA; exact HA).

  pose proof (land_mk (wl o) 3%uint63 ltac:(change (to_Z 3%uint63) with 3; lia)) as LM.
  change (PrimInt63.sub (PrimInt63.lsl 1 3) 1)%uint63 with 7%uint63 in LM. change (2 ^ to_Z 3%uint63) with 8 in LM.
  set (r8 := PrimInt63.land (wl o) 7%uint63) in *.
  assert (R8 : to_Z r8 = A mod 8).
  { rewrite LM, <- EO. unfold A. rewrite Z.add_mod, AL8 by lia. rewrite Z.add_0_l, Z.mod_mod by lia. reflexivity. }
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as RM.
  set (tot := PrimInt63.add r8 len) in *.
  assert (TOT : to_Z tot = A mod 8 + to_Z len).
  { unfold tot. rewrite Uint63.add_spec, R8. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  set (need := PrimInt63.add (PrimInt63.land (PrimInt63.sub tot 1%uint63) 7%uint63) 1%uint63) in *.
  assert (NEED : to_Z need = (A mod 8 + to_Z len - 1) mod 8 + 1).
  { unfold need. pose proof (land_mk (PrimInt63.sub tot 1%uint63) 3%uint63 ltac:(change (to_Z 3%uint63) with 3; lia)) as LM2.
    change (PrimInt63.sub (PrimInt63.lsl 1 3) 1)%uint63 with 7%uint63 in LM2. change (2 ^ to_Z 3%uint63) with 8 in LM2.
    rewrite Uint63.add_spec, LM2, Uint63.sub_spec, TOT. change (to_Z 1%uint63) with 1.
    rewrite (Z.mod_small (A mod 8 + to_Z len - 1)) by (change wB with (2 ^ 63); lia).
    pose proof (Z.mod_pos_bound (A mod 8 + to_Z len - 1) 8 ltac:(lia)). apply Z.mod_small. change wB with (2 ^ 63). lia. }
  set (cnt := Z.to_nat ((to_Z tot + 7) / 8)) in *.
  assert (CNT : Z.of_nat cnt = (A mod 8 + to_Z len + 7) / 8).
  { unfold cnt. rewrite TOT. apply Z2Nat.id. apply Z.div_pos; lia. }
  assert (JR : 0 <= G - A / 8 < Z.of_nat cnt) by (rewrite CNT; Z.div_mod_to_equations; lia).
  destruct (gran_loads_sound cnt need st p E ms mo HS GL (G - A / 8) JR) as (b & RB & GB).
  rewrite EP in RB. replace (2147450880 + A / 8 + (G - A / 8)) with (2147450880 + G) in RB by lia.
  exists b. split; [exact RB|]. destruct GB as [G0|[GJ GN]]; [left; exact G0| right].
  rewrite NEED in GN. rewrite CNT in GJ.
  assert (LAST : 8 * G + 8 >= A + to_Z len) by (Z.div_mod_to_equations; lia).
  rewrite Z.min_r by lia. split; [| lia].
  assert (EQN : (A mod 8 + to_Z len - 1) mod 8 + 1 = A + to_Z len - 8 * G) by (Z.div_mod_to_equations; lia).
  lia.
Qed.
End WithSegs.
End RangeFX.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import RangeC.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS CtrLib RangeC.TwinB.RangeC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module RangeFX.

Lemma w2Zs_wadd_lit : forall o (n : int) k0 k1, okey o = Some k0 -> okey (wadd o (wlit n)) = Some k1 -> 0 <= to_Z n <= 2 ^ 32 ->
  w2Zs (wadd o (wlit n)) = w2Zs o + to_Z n.
Proof.
  intros o n k0 k1 H0 H1 Hn. destruct (okey_sound _ _ H0) as [E0 R0]. destruct (okey_sound _ _ H1) as [E1 R1].
  rewrite E0 in R0. rewrite E1 in R1. change (- two63 / 2) with (- 2 ^ 62) in *. change (two63 / 2) with (2 ^ 62) in *.
  pose proof (wadd_ok o (wlit n)) as WA. rewrite wlit_ok in WA.
  rewrite !w2Zs_eq in *. pose proof (w2Z_range o) as RO. pose proof (w2Z_range (wadd o (wlit n))) as RA. unfold two64 in *.
  destruct (wt o), (wt (wadd o (wlit n))); Z.div_mod_to_equations; lia.
Qed.

Lemma in_region_sound : forall E r o len, in_region r o len = true -> 0 <= to_Z len <= 2 ^ 32 ->
  loZ r <= w2Zs o /\ w2Zs o + to_Z len <= hiZ E r /\ - 2 ^ 62 <= w2Zs o < 2 ^ 62.
Proof.
  intros E r o len H Hl. unfold in_region in H.
  destruct (okey o) as [k0|] eqn:K0; [|discriminate H]. destruct (okey (wadd o (wlit len))) as [k1|] eqn:K1; [|discriminate H].
  destruct (rg_hi r) as [hi| | | | | | | | | |] eqn:RH; try discriminate H.
  destruct (okey hi) as [kh|] eqn:KH; [| apply andb_prop in H as [_ H]; discriminate H].
  repeat match type of H with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in H as [H X] end.
  apply negb_true_iff in Q0. rewrite kleb_keyZ in H, Q1, Q. apply Z.leb_le in H, Q1, Q.
  destruct (okey_sound _ _ K0) as [E0 R0]. destruct (okey_sound _ _ K1) as [E1 R1]. destruct (okey_sound _ _ KH) as [EH RHr].
  rewrite (w2Zs_wadd_lit o len k0 k1 K0 K1 Hl) in E1.
  assert (HZ : hiZ E r = w2Zs hi).
  { unfold hiZ. rewrite RH. cbn [den]. rewrite wbv_unsigned, w2Zs_eq, Q0. lia. }
  change (- two63 / 2) with (- 2 ^ 62) in *. change (two63 / 2) with (2 ^ 62) in *. unfold loZ. rewrite HZ. unfold St.keyZ in *. lia.
Qed.

Lemma in_region_end : forall r o len, in_region r o len = true -> 0 <= to_Z len <= 2 ^ 32 ->
  w2Zs (wadd o (wlit len)) = w2Zs o + to_Z len.
Proof.
  intros r o len H Hl. unfold in_region in H.
  destruct (okey o) as [k0|] eqn:K0; [|discriminate H]. destruct (okey (wadd o (wlit len))) as [k1|] eqn:K1; [|discriminate H].
  exact (w2Zs_wadd_lit o len k0 k1 K0 K1 Hl).
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.

Lemma den_add1 : forall E a, den E (sv_alu ALU_ADD a (VL (wlit 1%uint63))) = (den E a + Z_to_bv 64 1)%bv.
Proof. intros E a. rewrite den_sv_alu. cbn [alu64 alu den]. unfold wbv. rewrite wlit_ok. reflexivity. Qed.

Lemma zero_loads_sound : forall fuel st p E ms mo,
  St.st_ok segs OPS E st ms mo -> zero_loads segs fuel st p = true ->
  forall j, 0 <= j < Z.of_nat fuel -> rb segs (ms_mem ms) (bv_unsigned (den E p) + j) = Some (Z_to_bv 8 0).
Proof.
  induction fuel as [|fuel IH]; intros st p E ms mo HS H j Hj; [lia|].
  cbn [zero_loads] in H.
  destruct (do_load segs st p 1%uint63 false) as [[v|]|] eqn:DL; try discriminate H.
  destruct v as [z| | | | | | | | | |]; try discriminate H. apply andb_prop in H as [HZ H]. apply weqb_eq in HZ. subst z.
  destruct (CopyFX.CopyFX.load1_where segs OPS E st ms mo p (VL wzero) HS DL) as (k & b & _ & _ & B1 & RB & SB & _).
  assert (B0 : b = Z_to_bv 8 0).
  { cbn [den] in SB. change (store_bytes 1%uint63 (wbv wzero)) with [Z_to_bv 8 0] in SB. injection SB as <-. reflexivity. }
  subst b. destruct (Z.eq_dec j 0) as [->|NZ]; [rewrite Z.add_0_r; exact RB|].
  pose proof (IH st (sv_alu ALU_ADD p (VL (wlit 1%uint63))) E ms mo HS H (j - 1) ltac:(lia)) as X.
  rewrite den_add1, bv_add_unsigned in X. change (bv_unsigned (Z_to_bv 64 1)) with 1 in X.
  pose proof (bv_unsigned_in_range _ (den E p)) as RP. unfold bv_modulus in RP.
  rewrite bv_wrap_small in X by (unfold bv_modulus, two64 in *; lia).
  replace (bv_unsigned (den E p) + 1 + (j - 1)) with (bv_unsigned (den E p) + j) in X by lia. exact X.
Qed.

Lemma shad_den : forall (X : word), bv_unsigned X < 2 ^ 47 ->
  bv_unsigned (alu64 ALU_ADD (alu64 ALU_SRL X (wbv (wlit 3%uint63))) (wbv SBw)) = 2147450880 + bv_unsigned X / 8.
Proof.
  intros X HX. cbn [alu64 alu]. rewrite bv_add_unsigned, bv_shiftr_unsigned.
  change (bv_unsigned (bv_and (wbv (wlit 3%uint63)) (Z_to_bv 64 63))) with 3.
  change (bv_unsigned (wbv SBw)) with 2147450880.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (bv_unsigned_in_range _ X) as RX. unfold bv_modulus in RX.
  rewrite bv_wrap_small; [lia|]. unfold bv_modulus. pose proof (Z.div_pos (bv_unsigned X) 8). Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_zero_sound : forall st k o len E ms mo,
  St.st_ok segs OPS E st ms mo -> shadow_zero segs st k o len = true -> 0 <= to_Z len ->
  let A := bv_unsigned (den E (VP k o)) in A < 2 ^ 47 ->
  forall G, A <= 8 * G + 7 -> 8 * G < A + to_Z len -> rb segs (ms_mem ms) (2147450880 + G) = Some (Z_to_bv 8 0).
Proof.
  intros st k o len E ms mo HS H Hl A HA G G1 G2. unfold shadow_zero in H.
  destruct (shadow_fold (s_facts st) (VAlu ALU_SRL (VP k o) (VL (wlit 3%uint63))) (VL SBw)) as [p|] eqn:SF; [|discriminate H].
  pose proof (shadow_fold_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) _ _ _ SF) as DP.
  cbn [den] in DP. fold (den E (VP k o)) in DP.
  assert (EP : bv_unsigned (den E p) = 2147450880 + A / 8) by (rewrite DP; apply shad_den; exact HA).
  pose proof (bv_unsigned_in_range _ (den E (VP k o))) as RA. fold A in RA.
  pose proof (zero_loads_sound _ st p E ms mo HS H (G - A / 8)) as X. rewrite EP in X.
  replace (2147450880 + A / 8 + (G - A / 8)) with (2147450880 + G) in X by lia. apply X.
  unfold shadow_zero_need. destruct (aligned (s_facts st) (VP k o) 3%uint63) eqn:AL.
  -
    pose proof (aligned_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) (VP k o) 3%uint63 AL ltac:(change (to_Z 3%uint63) with 3; lia)) as MA.
    change (2 ^ to_Z 3%uint63) with 8 in MA. fold A in MA.
    rewrite Z2Nat.id by (apply Z.div_pos; lia). Z.div_mod_to_equations. lia.
  - rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia). change (Z.of_nat 1) with 1.
    Z.div_mod_to_equations. lia.
Qed.

Lemma byte_of_lit : forall (E : env) (z : w64) (b : byte), store_bytes 1%uint63 (den E (VL z)) = [b] -> w2Z z < 256 -> bv_unsigned b = w2Z z.
Proof.
  intros E z b SB HZ. rewrite <- store_bytes_8 in SB. cbn [den] in SB.
  unfold Z_to_le_bytes in SB. cbn in SB. injection SB as <-.
  rewrite Z_to_bv_unsigned. rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  rewrite wbv_unsigned. pose proof (w2Z_range z) as R.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma gran_loads_sound : forall fuel need st p E ms mo,
  St.st_ok segs OPS E st ms mo -> gran_loads segs fuel need st p = true ->
  forall j, 0 <= j < Z.of_nat fuel -> exists b, rb segs (ms_mem ms) (bv_unsigned (den E p) + j) = Some b /\
     (bv_unsigned b = 0 \/ (j = Z.of_nat fuel - 1 /\ to_Z need <= bv_unsigned b <= 7)).
Proof.
  induction fuel as [|fuel IH]; intros need st p E ms mo HS H j Hj; [lia|].
  cbn [gran_loads] in H.
  destruct (do_load segs st p 1%uint63 false) as [[v|]|] eqn:DL; try discriminate H.
  destruct v as [z| | | | | | | | | |]; try discriminate H. apply andb_prop in H as [HZ H].
  destruct (CopyFX.CopyFX.load1_where segs OPS E st ms mo p (VL z) HS DL) as (k & b & _ & _ & B1 & RB & SB & _).
  destruct (Z.eq_dec j 0) as [->|NZ].
  - rewrite Z.add_0_r. exists b. split; [exact RB|].
    apply orb_prop in HZ. destruct HZ as [HZ|HZ].
    + left. apply weqb_eq in HZ. subst z. apply (byte_of_lit E wzero b SB). change (w2Z wzero) with 0. lia.
    + right. destruct fuel as [|f']; [| discriminate HZ].
      apply andb_prop in HZ as [HZ L7]. apply andb_prop in HZ as [WT LN]. apply negb_true_iff in WT.
      apply Uint63.leb_spec in L7, LN. change (to_Z 7%uint63) with 7 in L7.
      assert (EZ : w2Z z = to_Z (wl z)) by (unfold w2Z; rewrite WT; lia).
      rewrite (byte_of_lit E z b SB) by lia. cbn [Z.of_nat]. lia.
  - destruct (IH need st (sv_alu ALU_ADD p (VL (wlit 1%uint63))) E ms mo HS H (j - 1) ltac:(lia)) as (b' & RB' & GB).
    rewrite den_add1, bv_add_unsigned in RB'. change (bv_unsigned (Z_to_bv 64 1)) with 1 in RB'.
    pose proof (bv_unsigned_in_range _ (den E p)) as RP. unfold bv_modulus in RP.
    rewrite bv_wrap_small in RB' by (unfold bv_modulus, two64 in *; lia).
    replace (bv_unsigned (den E p) + 1 + (j - 1)) with (bv_unsigned (den E p) + j) in RB' by lia.
    exists b'. split; [exact RB'|]. destruct GB as [G0|[GJ GN]]; [left; exact G0| right; split; [lia| exact GN]].
Qed.

Lemma shadow_ok_x_sound : forall st k o len E ms mo,
  St.st_ok segs OPS E st ms mo -> shadow_ok_x segs st k o len = true -> 1 <= to_Z len <= 2 ^ 40 ->
  let A := bv_unsigned (ev E k) + w2Z o in A < 2 ^ 47 ->
  forall G, A <= 8 * G + 7 -> 8 * G < A + to_Z len ->
    exists b, rb segs (ms_mem ms) (2147450880 + G) = Some b /\ (bv_unsigned b = 0 \/ (Z.min (8 * G + 8) (A + to_Z len) - 8 * G <= bv_unsigned b <= 7)).
Proof.
  intros st k o len E ms mo HS H Hl A HA G G1 G2. unfold shadow_ok_x in H. cbv zeta in H.
  apply andb_prop in H as [H GL]. apply andb_prop in H as [AL WT]. apply negb_true_iff in WT.
  destruct (shadow_fold (s_facts st) (VAlu ALU_SRL (VP k o) (VL (wlit 3%uint63))) (VL SBw)) as [p|] eqn:SF; [|discriminate GL].
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  pose proof (shadow_fold_sound E (s_facts st) Hfs _ _ _ SF) as DP. cbn [den] in DP. fold (den E (VP k o)) in DP.
  pose proof (aligned_sound E _ Hfs _ _ AL ltac:(change (to_Z 3%uint63) with 3; lia)) as AL8. change (2 ^ to_Z 3%uint63) with 8 in AL8.
  assert (EO : w2Z o = to_Z (wl o)) by (unfold w2Z; rewrite WT; lia).
  pose proof (bv_unsigned_in_range _ (ev E k)) as RK. unfold bv_modulus in RK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RK.
  pose proof (w2Z_range o) as RO.
  assert (DVK : bv_unsigned (den E (VP k wzero)) = bv_unsigned (ev E k)).
  { rewrite den_VP. change (w2Zs wzero) with 0. rewrite Z.add_0_r. apply Z.mod_small. unfold two64. lia. }
  rewrite DVK in AL8.
  assert (DVA : bv_unsigned (den E (VP k o)) = A).
  { rewrite den_VP. rewrite w2Zs_eq, WT. unfold A. rewrite Z.sub_0_r. apply Z.mod_small. unfold two64, A in *. lia. }
  assert (EP : bv_unsigned (den E p) = 2147450880 + A / 8) by (rewrite DP; rewrite <- DVA; apply shad_den; rewrite DVA; exact HA).

  pose proof (land_mk (wl o) 3%uint63 ltac:(change (to_Z 3%uint63) with 3; lia)) as LM.
  change (PrimInt63.sub (PrimInt63.lsl 1 3) 1)%uint63 with 7%uint63 in LM. change (2 ^ to_Z 3%uint63) with 8 in LM.
  set (r8 := PrimInt63.land (wl o) 7%uint63) in *.
  assert (R8 : to_Z r8 = A mod 8).
  { rewrite LM, <- EO. unfold A. rewrite Z.add_mod, AL8 by lia. rewrite Z.add_0_l, Z.mod_mod by lia. reflexivity. }
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as RM.
  set (tot := PrimInt63.add r8 len) in *.
  assert (TOT : to_Z tot = A mod 8 + to_Z len).
  { unfold tot. rewrite Uint63.add_spec, R8. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  set (need := PrimInt63.add (PrimInt63.land (PrimInt63.sub tot 1%uint63) 7%uint63) 1%uint63) in *.
  assert (NEED : to_Z need = (A mod 8 + to_Z len - 1) mod 8 + 1).
  { unfold need. pose proof (land_mk (PrimInt63.sub tot 1%uint63) 3%uint63 ltac:(change (to_Z 3%uint63) with 3; lia)) as LM2.
    change (PrimInt63.sub (PrimInt63.lsl 1 3) 1)%uint63 with 7%uint63 in LM2. change (2 ^ to_Z 3%uint63) with 8 in LM2.
    rewrite Uint63.add_spec, LM2, Uint63.sub_spec, TOT. change (to_Z 1%uint63) with 1.
    rewrite (Z.mod_small (A mod 8 + to_Z len - 1)) by (change wB with (2 ^ 63); lia).
    pose proof (Z.mod_pos_bound (A mod 8 + to_Z len - 1) 8 ltac:(lia)). apply Z.mod_small. change wB with (2 ^ 63). lia. }
  set (cnt := Z.to_nat ((to_Z tot + 7) / 8)) in *.
  assert (CNT : Z.of_nat cnt = (A mod 8 + to_Z len + 7) / 8).
  { unfold cnt. rewrite TOT. apply Z2Nat.id. apply Z.div_pos; lia. }
  assert (JR : 0 <= G - A / 8 < Z.of_nat cnt) by (rewrite CNT; Z.div_mod_to_equations; lia).
  destruct (gran_loads_sound cnt need st p E ms mo HS GL (G - A / 8) JR) as (b & RB & GB).
  rewrite EP in RB. replace (2147450880 + A / 8 + (G - A / 8)) with (2147450880 + G) in RB by lia.
  exists b. split; [exact RB|]. destruct GB as [G0|[GJ GN]]; [left; exact G0| right].
  rewrite NEED in GN. rewrite CNT in GJ.
  assert (LAST : 8 * G + 8 >= A + to_Z len) by (Z.div_mod_to_equations; lia).
  rewrite Z.min_r by lia. split; [| lia].
  assert (EQN : (A mod 8 + to_Z len - 1) mod 8 + 1 = A + to_Z len - 8 * G) by (Z.div_mod_to_equations; lia).
  lia.
Qed.
End WithSegs.
End RangeFX.
End TwinB.
