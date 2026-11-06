(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition M64 : Z := 2^64.
Definition M64m1 : Z := 0xffffffffffffffff.
Definition c55 : Z := 0x5555555555555555.
Definition c33 : Z := 0x3333333333333333.
Definition c0f : Z := 0x0f0f0f0f0f0f0f0f.
Definition c01 : Z := 0x0101010101010101.

(* [comment removed for export] *)
Definition swar_smear (sz : Z) : Z :=
  let a1 := Z.lor sz (Z.shiftr sz 1) in
  let a2 := Z.lor a1 (Z.shiftr a1 2) in
  let a3 := Z.lor a2 (Z.shiftr a2 4) in
  let a4 := Z.lor a3 (Z.shiftr a3 8) in
  let a5 := Z.lor a4 (Z.shiftr a4 16) in
  Z.lor a5 (Z.shiftr a5 32).
(* [comment removed for export] *)
Definition swar_pz (sm : Z) : Z :=
  let na := Z.lxor sm M64m1 in
  let b := (na - Z.land (Z.shiftr na 1) c55) mod M64 in
  let c := Z.land b c33 + Z.land (Z.shiftr b 2) c33 in
  (Z.land ((c + Z.shiftr (c mod M64) 4) mod M64) c0f * c01) mod M64.
(* [comment removed for export] *)
Definition swar_cls (sz pz : Z) : Z :=
  let z := Z.shiftr pz 56 in
  let sh := bv_swrap 32 (62 - z) mod M64 in
  Z.lor (Z.lxor ((Z.shiftl z 1) mod M64) 126) (Z.land (Z.shiftr sz (sh mod 64)) 1)
  + Z.b2z (0 <? Z.land sz (Z.lxor ((bv_swrap 32 (Z.shiftl M64m1 (sh mod 32))) mod M64) M64m1)) + -2.
Definition swar_class (sz : Z) : Z := swar_cls sz (swar_pz (swar_smear sz)).

(* [comment removed for export] *)
Fixpoint zall (f : Z -> bool) (z : Z) (n : nat) : bool :=
  match n with O => true | S n' => if f z then zall f (z + 1) n' else false end.
Lemma zall_spec : forall f n z, zall f z n = true -> forall s, z <= s < z + Z.of_nat n -> f s = true.
Proof.
  induction n as [|n IH]; intros z H s Hs; [lia|]. cbn [zall] in H.
  destruct (f z) eqn:Fz; [|discriminate]. destruct (Z.eq_dec s z) as [->|NE]; [exact Fz|].
  apply (IH (z + 1) H). lia.
Qed.

(* [comment removed for export] *)
Lemma smear_check : zall (fun s => swar_smear s =? 2 ^ (Z.log2 s + 1) - 1) 513 (Z.to_nat 65024) = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition pz_of (l : Z) : Z := swar_pz (2 ^ (l + 1) - 1).
Definition pz_tab : list Z := map pz_of [9; 10; 11; 12; 13; 14; 15; 16].
Definition pz_msb (l : Z) : Z := nth (Z.to_nat (l - 9)) pz_tab 0.
(* [comment removed for export] *)
Lemma cls_check : zall (fun s => swar_cls s (pz_msb (Z.log2 s)) =? class_id s) 513 (Z.to_nat 65024) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.   (* [comment removed for export] *)

Lemma pz_msb_eq : forall l, 9 <= l <= 16 -> pz_msb l = swar_pz (2 ^ (l + 1) - 1).
Proof.
  intros l Hl.
  assert (C : l = 9 \/ l = 10 \/ l = 11 \/ l = 12 \/ l = 13 \/ l = 14 \/ l = 15 \/ l = 16) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

Theorem swar_class_ok : forall s, kMidSize < s <= kMaxSize -> swar_class s = class_id s.
Proof.
  intros s Hs. unfold kMidSize, kMaxSize in Hs.
  assert (R : 513 <= s < 513 + Z.of_nat (Z.to_nat 65024)) by lia.
  pose proof (zall_spec _ _ _ smear_check s R) as A. pose proof (zall_spec _ _ _ cls_check s R) as B. cbn beta in A, B.
  apply Z.eqb_eq in A. apply Z.eqb_eq in B.
  assert (L : 9 <= Z.log2 s <= 16).
  { split; [change 9 with (Z.log2 513)| change 16 with (Z.log2 65536)]; apply Z.log2_le_mono; lia. }
  rewrite (pz_msb_eq _ L), <- A in B. exact B.
Qed.
