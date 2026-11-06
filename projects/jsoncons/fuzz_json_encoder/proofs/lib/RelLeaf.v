(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore AsanPlanSound L5Defs.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RLF.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Link.
Variable segs : list MemImageType.Segment.

Lemma rdn_one_inv : forall (mem : word -> option byte) (a : word) b bs,
  rdn segs mem a 1 = Some bs -> mem a = Some b -> bs = [b].
Proof.
  intros mem a b bs H Hm. cbn [rdn] in H. rewrite Hm in H. cbn in H. congruence.
Qed.

(* [comment removed for export] *)
Lemma blob_byte : forall E (M : word -> option byte) (ab : saddr) (n : expr) (k : nat) (a : saddr) (v : expr) (i : Z),
  kentry_ok segs E M (KBlob ab n k) ->
  kentry_ok segs E M (KWord a 1 v) ->
  estart E a = estart E ab + i -> 0 <= i < elenZ E n ->
  word_to_le_bytes 1 (edenot E v) = [nth (Z.to_nat i) (eb E k) (Z_to_bv 8 0)].
Proof.
  intros E M ab n k a v i (Fb & Hlen & Hb) (Hw & Fa & Hr) Hi Hir.
  pose proof (Hb i Hir) as Hm. rewrite <- Hi in Hm.
  assert (Ha : adenot E a = Z_to_bv 64 (estart E a)).
  { unfold adenot, v_addi, estart. destruct a as [base off]; cbn [a_base a_off]. reflexivity. }
  rewrite Ha in Hr. exact (rdn_one_inv M _ _ _ Hr Hm).
Qed.

(* [comment removed for export] *)
Lemma blob_byte_Z : forall E (M : word -> option byte) (ab : saddr) (n : expr) (k : nat) (a : saddr) (v : nat) (i : Z) (w : list Z),
  kentry_ok segs E M (KBlob ab n k) ->
  kentry_ok segs E M (KWord a 1 (EVar v)) ->
  kentry_ok segs E M (KRange (EVar v) 0 255) ->
  eb E k = map (Z_to_bv 8) w -> Forall (fun b => 0 <= b <= 255) w ->
  estart E a = estart E ab + i -> 0 <= i < elenZ E n ->
  bv_unsigned (ev E v) = nth (Z.to_nat i) w 0.
Proof.
  intros E M ab n k a v i w HB HW (Hlo & Hhi) Heb Hw Hi Hir.
  pose proof (blob_byte E M ab n k a (EVar v) i HB HW Hi Hir) as L. cbn [edenot] in L, Hlo, Hhi.
  destruct HB as (_ & Hlen & _). rewrite Heb, length_map in Hlen.
  assert (Hin : (Z.to_nat i < length w)%nat) by lia.
  rewrite Heb in L.
  (* [comment removed for export] *)
  assert (W1 : word_to_le_bytes 1 (ev E v) = [Z_to_bv 8 (bv_unsigned (ev E v))]).
  { unfold word_to_le_bytes. cbn. f_equal. }
  rewrite W1 in L.
  assert (N : nth (Z.to_nat i) (map (Z_to_bv 8) w) (Z_to_bv 8 0) = Z_to_bv 8 (nth (Z.to_nat i) w 0)).
  { clear -Hin. revert Hin. generalize (Z.to_nat i) as j. induction w as [|x r IH]; intros [|j] Hj; cbn in *; try lia; [reflexivity | apply IH; lia]. }
  rewrite N in L. apply (f_equal (hd (Z_to_bv 8 0))) in L. cbn [hd] in L.
  pose proof (proj1 (Forall_forall _ _) Hw (nth (Z.to_nat i) w 0) (nth_In w 0 Hin)) as Hb.
  apply (f_equal bv_unsigned) in L. rewrite !Z_to_bv_unsigned in L.
  unfold bv_wrap in L. replace (bv_modulus 8) with 256 in L by reflexivity. cbn beta in Hb. rewrite !Z.mod_small in L by lia. exact L.
Qed.
End Link.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition E_nil : env := Env (fun _ => Z_to_bv 64 0) (fun _ => []).
(* [comment removed for export] *)
Fixpoint closed_but (bv : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.eqb n bv
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => closed_but bv a && closed_but bv b
  | EExt _ _ _ a => closed_but bv a
  | EBlob _ _ _ _ => false
  end.
Lemma edenot_closed_but : forall bv e E E', closed_but bv e = true -> ev E bv = ev E' bv -> edenot E e = edenot E' e.
Proof.
  intros bv e E E' H Hv. induction e; cbn [edenot closed_but] in *;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity).
  - reflexivity.
  - apply Nat.eqb_eq in H. subst. exact Hv.
  - rewrite (IHe H). reflexivity.
  - discriminate H.
Qed.
(* [comment removed for export] *)
Definition fact_okb (bv : nat) (b : Z) (k : kentry) : bool :=
  match k with
  | KRange e lo hi => if closed_but bv e then let v := bv_unsigned (edenot E_nil (APC.esubst bv (ELit b) e)) in (lo <=? v) && (v <=? hi) else true
  | _ => true
  end.
Definition byte_adm (bv : nat) (cells : list kentry) (b : Z) : bool := forallb (fact_okb bv b) cells.
Fixpoint forall_b (lo : Z) (n : nat) (f : Z -> bool) : bool :=
  match n with O => true | S n' => f lo && forall_b (lo + 1) n' f end.
Definition all_bytes (f : Z -> bool) : bool := forall_b 0 256 f.
Lemma forall_b_sound : forall n lo f b, forall_b lo n f = true -> lo <= b < lo + Z.of_nat n -> f b = true.
Proof.
  induction n as [|n IH]; intros lo f b H Hb; [lia|]. cbn [forall_b] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec b lo) as [->|NE]; [exact H1|]. apply (IH (lo + 1) f b H2). lia.
Qed.
Lemma all_bytes_sound : forall f b, all_bytes f = true -> 0 <= b <= 255 -> f b = true.
Proof. intros f b H Hb. apply (forall_b_sound 256 0 f b H). lia. Qed.
(* [comment removed for export] *)
Lemma fact_okb_sound : forall segs bv E M b k, kentry_ok segs E M k -> ev E bv = Z_to_bv 64 b -> fact_okb bv b k = true.
Proof.
  intros segs bv E M b k Hk Hv. destruct k; cbn [fact_okb]; try reflexivity.
  destruct (closed_but bv e) eqn:C; [|reflexivity]. cbn [kentry_ok] in Hk. destruct Hk as [H1 H2].
  rewrite APS.esubst_denot. cbn [edenot].
  rewrite (edenot_closed_but bv e (APS.upd E_nil bv (Z_to_bv 64 b)) E C) by (unfold APS.upd; cbn; rewrite Nat.eqb_refl; symmetry; exact Hv).
  apply andb_true_intro. split; apply Z.leb_le; assumption.
Qed.
Lemma byte_adm_sound : forall segs bv E M b cells, know_ok segs E M cells -> ev E bv = Z_to_bv 64 b -> byte_adm bv cells b = true.
Proof.
  intros segs bv E M b cells HK Hv. unfold byte_adm. apply forallb_forall. intros k Hk.
  exact (fact_okb_sound segs bv E M b k (proj1 (Forall_forall _ _) HK k Hk) Hv).
Qed.
(* [comment removed for export] *)
Lemma adm_check_sound : forall segs bv E M cells (chk : Z -> bool),
  all_bytes (fun b => negb (byte_adm bv cells b) || chk b) = true ->
  know_ok segs E M cells -> 0 <= bv_unsigned (ev E bv) <= 255 -> chk (bv_unsigned (ev E bv)) = true.
Proof.
  intros segs bv E M cells chk H HK Hr.
  pose proof (all_bytes_sound _ _ H Hr) as Q. cbn beta in Q.
  rewrite (byte_adm_sound segs bv E M (bv_unsigned (ev E bv)) cells HK) in Q; [exact Q|]. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Uniq.
Variable segs : list MemImageType.Segment.
Lemma u8_at_mod : forall (M : word -> option byte) a b b', L5.u8_at segs M a b -> L5.u8_at segs M a b' -> b mod 256 = b' mod 256.
Proof.
  intros M a b b' H H'. unfold L5.u8_at in *. rewrite H in H'.
  assert (E : Z_to_bv 8 b = Z_to_bv 8 b') by congruence.
  apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. exact E.
Qed.
Lemma bytes_at_mod : forall (M : word -> option byte) a l1 l2, L5.bytes_at segs M a l1 -> L5.bytes_at segs M a l2 -> length l1 = length l2 ->
  forall n, (n < length l1)%nat -> (nth n l1 0) mod 256 = (nth n l2 0) mod 256.
Proof. intros M a l1 l2 H1 H2 L n Hn. exact (u8_at_mod M _ _ _ (H1 n Hn) (H2 n ltac:(rewrite <- L; exact Hn))). Qed.
Lemma bytes_at_small_eq : forall (M : word -> option byte) a l1 l2, L5.bytes_at segs M a l1 -> L5.bytes_at segs M a l2 -> length l1 = length l2 ->
  Forall (fun b => 0 <= b <= 255) l1 -> Forall (fun b => 0 <= b <= 255) l2 -> l1 = l2.
Proof.
  intros M a l1 l2 H1 H2 L F1 F2. apply (nth_ext _ _ 0 0 L). intros n Hn.
  pose proof (bytes_at_mod M a l1 l2 H1 H2 L n Hn) as E. assert (Hn2 : (n < length l2)%nat) by (rewrite <- L; exact Hn).
  pose proof (proj1 (Forall_forall _ _) F1 _ (nth_In l1 0 Hn)) as R1. pose proof (proj1 (Forall_forall _ _) F2 _ (nth_In l2 0 Hn2)) as R2.
  cbn beta in R1, R2. rewrite !Z.mod_small in E by lia. exact E.
Qed.
(* [comment removed for export] *)
End Uniq.
End RLF.
