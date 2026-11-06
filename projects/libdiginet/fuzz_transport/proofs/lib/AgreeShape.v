(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/AgreeShape.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_transport; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_transport.lib. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import AllocSlots AllocRoom SlotAgree.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require AgreeZlib.
Local Open Scope Z_scope.

Definition ag_room (b : sbound) (n : Z) : Prop := sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAP_AG.

Definition ag_shape (S : lib_shape) : lib_shape := {|
  LIBK := @LIBK S;
  LIBK_ext := @LIBK_ext S;
  lib_delta := fun _ b => b;
  lib_room := ag_room |}.

Lemma ag_LIBK : forall S pl fs K, @LIBK (ag_shape S) pl fs K = @LIBK S pl fs K.
Proof. reflexivity. Qed.

Lemma ag_delta : forall S n b, @lib_delta (ag_shape S) n b = b.
Proof. reflexivity. Qed.

Lemma ag_room_calls : forall S n k, @room_calls (ag_shape S) n k U.AgreeZlib.SBD_AG.
Proof.
  intros S n k. induction k as [|k IH]; cbn [room_calls]; [exact I|]. split; [|exact IH].
  cbn. unfold ag_room, U.AgreeZlib.SBD_AG. cbn [sb_live sb_bytes sb_cap]. unfold CAP_AG.
  change (2 ^ 28) with 268435456. repeat split; lia.
Qed.

Lemma ag_room_cg : forall S b n, @lib_room (ag_shape S) b n ->
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG.
Proof. intros S b n (H1 & H2 & H3). cbn in *. unfold CAP_AG in *. lia. Qed.

Lemma ag_room_g : forall S b n, @lib_room (ag_shape S) b n ->
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX.
Proof. intros S b n (H1 & H2 & H3). cbn in *. unfold CAP_AG, CAPMAX in *. lia. Qed.
