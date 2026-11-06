(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From Corelib Require Import PrimString PrimStringAxioms.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AsanHexScan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition zchunk_ok (s : PrimString.string) (off len : int) : bool :=
  match PrimString.compare (PrimString.sub s off len) (PrimString.make len 48%uint63) with Eq => true | _ => false end.

Lemma c63_compare_eq : forall c1 c2 : int, PrimInt63.compare c1 c2 = Eq <-> c1 = c2.
Proof.
  intros c1 c2. rewrite Uint63.compare_spec. rewrite Z.compare_eq_iff. split; [apply to_Z_inj | intros ->; reflexivity].
Qed.

Lemma zchunk_get : forall s off len, zchunk_ok s off len = true ->
  to_Z len <= to_Z PrimString.max_length -> to_Z off + to_Z len < wB ->
  forall j : int, to_Z j < to_Z len -> PrimString.get s (off + j)%uint63 = 48%uint63.
Proof.
  intros s off len H Hmax Hno j Hj. unfold zchunk_ok in H.
  assert (WB : wB = 9223372036854775808) by reflexivity.
  destruct (PrimString.compare (PrimString.sub s off len) (PrimString.make len 48%uint63)) eqn:E; try discriminate.
  rewrite PrimStringAxioms.compare_spec in E. apply (List.list_compare_refl _ c63_compare_eq) in E.
  rewrite PrimStringAxioms.sub_spec, PrimStringAxioms.make_spec in E.
  pose proof (to_Z_bounded off) as Boff. pose proof (to_Z_bounded len) as Blen. pose proof (to_Z_bounded j) as Bj.
  replace (Nat.min (Z.to_nat (to_Z len)) (Z.to_nat (to_Z PrimString.max_length))) with (Z.to_nat (to_Z len)) in E by lia.
  change (PrimInt63.land 48 255)%uint63 with 48%uint63 in E.
  rewrite PrimStringAxioms.get_spec.
  assert (EJ : Z.to_nat (to_Z (off + j)) = (Z.to_nat (to_Z off) + Z.to_nat (to_Z j))%nat).
  { rewrite Uint63.add_spec, Z.mod_small by lia. lia. }
  rewrite EJ. rewrite <- (List.nth_skipn (Z.to_nat (to_Z off))).
  assert (NF : forall (A : Type) (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d).
  { intros A l. induction l as [|a l IH]; intros n i d Hi; [destruct n; destruct i; reflexivity|].
    destruct n; [lia|]. destruct i; [reflexivity|]. cbn. apply IH. lia. }
  rewrite <- (NF _ _ (Z.to_nat (to_Z len))) by lia. rewrite E.
  apply List.nth_repeat_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma hex_zero_fast : forall (s : PrimString.string) (n1 cnt : N),
  zchunk_ok s (of_Z (2 * Z.of_N n1)) (of_Z (2 * Z.of_N cnt)) = true ->
  2 * Z.of_N (n1 + cnt) <= to_Z (PrimString.length s) ->
  2 * Z.of_N cnt <= to_Z PrimString.max_length ->
  forall i : N, (n1 <= i < n1 + cnt)%N -> hex_byte_at s i = Some (Z_to_bv 8 0).
Proof.
  intros s n1 cnt H Hlen Hmax i Hi.
  assert (WB : wB = 9223372036854775808) by reflexivity.
  pose proof (to_Z_bounded (PrimString.length s)) as BL. pose proof (to_Z_bounded PrimString.max_length) as BM.
  assert (Eoff : to_Z (of_Z (2 * Z.of_N n1)) = 2 * Z.of_N n1) by (rewrite of_Z_spec; apply Z.mod_small; lia).
  assert (Ecnt : to_Z (of_Z (2 * Z.of_N cnt)) = 2 * Z.of_N cnt) by (rewrite of_Z_spec; apply Z.mod_small; lia).
  pose proof (zchunk_get s _ _ H ltac:(rewrite Ecnt; lia) ltac:(rewrite Eoff, Ecnt; lia)) as G.
  assert (G0 : PrimString.get s (of_Z (Z.of_N (2 * i))) = 48%uint63).
  { replace (of_Z (Z.of_N (2 * i))) with (of_Z (2 * Z.of_N n1) + of_Z (2 * Z.of_N (i - n1)))%uint63.
    - apply G. rewrite Ecnt. rewrite of_Z_spec, Z.mod_small by lia. lia.
    - apply to_Z_inj. rewrite Uint63.add_spec, !of_Z_spec. rewrite !(Z.mod_small (2 * _)) by lia. rewrite !Z.mod_small by lia. lia. }
  assert (G1 : PrimString.get s (of_Z (Z.of_N (2 * i + 1))) = 48%uint63).
  { replace (of_Z (Z.of_N (2 * i + 1))) with (of_Z (2 * Z.of_N n1) + of_Z (2 * Z.of_N (i - n1) + 1))%uint63.
    - apply G. rewrite Ecnt. rewrite of_Z_spec, Z.mod_small by lia. lia.
    - apply to_Z_inj. rewrite Uint63.add_spec, !of_Z_spec. rewrite !(Z.mod_small (2 * _)) by lia. rewrite !Z.mod_small by lia. lia. }
  assert (B : Uint63.ltb (of_Z (Z.of_N (2 * i + 1))) (PrimString.length s) = true).
  { apply Uint63.ltb_spec. rewrite of_Z_spec, Z.mod_small by lia. lia. }
  unfold hex_byte_at. cbv zeta. rewrite B, G0, G1. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma segment_byte_at_some_pw : forall s (n1 n : N) (off : N),
  scanN s 64 0 n1 = true ->
  (forall i : N, (n1 <= i < n)%N -> hex_byte_at s i = Some (Z_to_bv 8 0)) ->
  (n <= Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N ->
  (Z.of_N off < Z.of_N n)%Z ->
  segment_byte_at [s] off <> None.
Proof.
  intros s n1 n off Hs Hz Hn Hoff. cbn [segment_byte_at].
  replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true by (symmetry; apply N.ltb_lt; lia).
  destruct (N.lt_ge_cases off n1) as [Hl|Hge].
  - pose proof (scanN_sound s 64 0 n1 Hs off Hl) as X. rewrite N.add_0_l in X. exact X.
  - rewrite (Hz off ltac:(lia)). discriminate.
Qed.
