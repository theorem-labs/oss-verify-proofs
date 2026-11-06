(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS TR.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module KF.

Definition KF_BIGZ : Z := 4611686018427387904 + 1048576.
Definition KF_BIG : w64 := wlit 4611686018428436480%uint63.
Definition kids_facts (cnt ptr : sv) : list fact :=
  [FULe cnt ptr; FULe (VAlu ALU_ADD ptr (VMd M_MUL cnt (VL (wlit 48%uint63)))) (VL KF_BIG); FULe ptr (VL KF_BIG)].

Lemma kids_pure : forall bm z t,
  tree_wf bm z t ->
  (forall p sz, in_zone z p sz -> 0 <= sz -> 4104 <= p /\ p + sz <= 4611686018427387904) ->
  0 <= obj_cnt t <= 1000 /\ (obj_cnt t <= obj_ptr t) /\ 0 <= obj_ptr t /\ obj_ptr t + 48 * obj_cnt t <= KF_BIGZ.
Proof.
  intros bm z t TW ZB. unfold KF_BIGZ.
  destruct t as [| b | u | i | f | f | p n | p n | p n | p kids | p kids]; cbn [obj_cnt obj_ptr]; cbn [tree_wf] in TW; unfold LIMIT in *; try lia.
  - destruct TW as (TWn & TWz & TWnz). destruct (Z.eq_dec p 0) as [PZ|PNZ]; [pose proof (TWz PZ); lia|].
    destruct (TWnz PNZ) as [TWin _]. pose proof (ZB _ _ TWin ltac:(lia)). lia.
  - destruct TW as (TWn & TWz & TWnz). destruct (Z.eq_dec p 0) as [PZ|PNZ]; [pose proof (TWz PZ); lia|].
    destruct (TWnz PNZ) as [TWin _]. pose proof (ZB _ _ TWin ltac:(lia)). lia.
  - destruct TW as (TWn & TWn1 & TWp & TWin & _). pose proof (ZB _ _ TWin ltac:(lia)). lia.
  - destruct TW as (TWl & TWe & TWk & _). pose proof (Zle_0_nat (length kids)) as LN.
    destruct kids as [|k0 ks]; [rewrite (proj1 TWe eq_refl); cbn [length Z.of_nat]; lia|].
    destruct (TWk ltac:(discriminate)) as [_ TWin]. pose proof (ZB _ _ TWin ltac:(unfold OBJ_SIZE; lia)). unfold OBJ_SIZE in *. lia.
  - destruct TW as (TWev & TWl & TWe & TWk & _). pose proof (Zle_0_nat (length kids)) as LN.
    pose proof (Z.div_pos (Z.of_nat (length kids)) 2 LN ltac:(lia)) as DP.
    pose proof (Z.mul_div_le (Z.of_nat (length kids)) 2 ltac:(lia)) as MD.
    destruct kids as [|k0 ks]; [rewrite (proj1 TWe eq_refl); cbn [length Z.of_nat]; change (0 / 2) with 0; lia|].
    destruct (TWk ltac:(discriminate)) as [_ TWin]. pose proof (ZB _ _ TWin ltac:(unfold OBJ_SIZE; lia)). unfold OBJ_SIZE in *. lia.
Qed.

Lemma kids_facts_sound : forall E cnt ptr c p,
  bv_unsigned (den E cnt) = c -> bv_unsigned (den E ptr) = p ->
  0 <= c <= 1000 -> c <= p -> 0 <= p -> p + 48 * c <= KF_BIGZ ->
  Forall (fact_holds E) (kids_facts cnt ptr).
Proof.
  intros E cnt ptr c p HC HP RC I1 P0 I2. unfold kids_facts, KF_BIGZ in *. pose proof two64_eq as T64.
  constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fact_holds].
  - rewrite HC, HP. exact I1.
  - change (den E (VAlu ALU_ADD ptr (VMd M_MUL cnt (VL (wlit 48%uint63))))) with (bv_add (den E ptr) (bv_mul (den E cnt) (den E (VL (wlit 48%uint63))))).
    rewrite bv_add_unsigned, bv_mul_unsigned, HC, HP, !den_VL. unfold KF_BIG. rewrite !wlit_ok.
    change (to_Z 48%uint63) with 48. change (to_Z 4611686018428436480%uint63) with 4611686018428436480.
    unfold bv_wrap. rewrite bv_modulus_64. rewrite (Z.mod_small (c * 48)) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite HP, den_VL. unfold KF_BIG. rewrite wlit_ok. change (to_Z 4611686018428436480%uint63) with 4611686018428436480. lia.
Qed.

End KF.
