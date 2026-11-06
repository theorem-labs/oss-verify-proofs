(* Pure list facts the string walks' answers share (strncmp, lib/B/Rt/RtLStrncmp.v; strncasecmp, lib/A/FMspec_str.v):
   a byte's value, a C string as the walk sees it (its bytes and then one NUL), and the walk's byte list read on
   the byte values. No program module; lib/A/FMspec_str.v re-exports this file. *)
(* Relocated to plugin-hostd/fuzz_command from omx-clap-core/fuzz_manifest's program-free split
   (proofs/omx-clap-core/fuzz_manifest/lib/A/FMspec_strn.v), unchanged. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.

(* a C string as the walk sees it: its bytes and then one NUL, nowhere else *)
Definition nul_last (m : list Z) : Prop :=
  exists l, m = l ++ [0] /\ Forall (fun c => c <> 0) l /\ Forall (fun c => 0 <= c < 256) l.

Lemma nul_last_cons : forall x r, nul_last (x :: r) -> x = 0 -> r = [].
Proof.
  intros x r (l & Hm & Hnz & _) Hx. subst x.
  destruct l as [|a l]; cbn in Hm.
  - congruence.
  - exfalso. inversion Hnz as [|? ? Hz _]; subst. apply Hz. congruence.
Qed.

Lemma nul_last_hd_range : forall x r, nul_last (x :: r) -> 0 <= x < 256.
Proof.
  intros x r (l & Hm & Hnz & Hr).
  destruct l as [|a l]; cbn in Hm.
  - assert (x = 0) by congruence. lia.
  - inversion Hr as [|? ? Ha _]; subst. assert (x = a) by congruence. lia.
Qed.

Lemma nul_last_tl : forall x r, nul_last (x :: r) -> x <> 0 -> nul_last r.
Proof.
  intros x r (l & Hm & Hnz & Hr) Hx.
  destruct l as [|a l]; cbn in Hm.
  - exfalso. apply Hx. congruence.
  - inversion Hnz as [|? ? _ Hnz']; subst. inversion Hr as [|? ? _ Hr']; subst.
    exists l. split; [congruence | split; [exact Hnz' | exact Hr']].
Qed.

(* the walk's answer on byte lists is the Z-level one on their values *)
Lemma nth_error_map_nth : forall (m : list Z) (i : nat),
  (i < length m)%nat -> nth_error (map (Z_to_bv 8) m) i = Some (Z_to_bv 8 (nth i m 0)).
Proof.
  intros m i Hi. rewrite nth_error_map.
  destruct (nth_error m i) as [v|] eqn:E.
  - cbn [option_map]. rewrite (nth_error_nth m i 0 E). reflexivity.
  - apply nth_error_None in E. lia.
Qed.

Lemma u8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. lia.
Qed.
