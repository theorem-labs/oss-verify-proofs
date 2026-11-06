(* Reply image row img-errnonst-A (a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record); CF-UNIT-HYPS.md:36 (sha256 77b3f94c95d2; internal record)).
   errno_nstatic_t at reply image A, as a CLOSED lemma over the unit's own TfibSyms tables (lib/A/AD2l.v TfibB:
   as_errno := TFIB_ERRNO :26, as_owned_static := Tfib_owned_static :37, both lib/A/AF0m.v).
   The cf layer's name is not in this tree yet, so the statement is the UNFOLDED text of
     Definition errno_nstatic_t (YGcfInstErrno.v:90, F1)  =
     forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B)   at B := TfibB.
   Proof pattern: cgif's errno_nstatic_cgif (YGcfInstErrnocgif.v:44 @ bdbe5c2a7e55), which destructs the owned list
   entry by entry; here one vm_compute decides "no owned range meets [errno, errno + 4)" for the whole list, with the
   kernel cast recorded (whole-goal vm_compute; reflexivity). Author: a Theorem Labs lane. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0m AD2l.
Import ListNotations.
Local Open Scope Z_scope.

(* r meets the four errno bytes [e, e + 4) *)
Definition meets4 (e : Z) (r : Z * Z) : bool := (fst r <? e + 4) && (e <? fst r + snd r).

Lemma nstatic_of_check : forall (owned : list (Z * Z)) (e : Z),
  existsb (meets4 e) owned = false ->
  forall a, e <= a < e + 4 -> ~ Exists (in_zr a) owned.
Proof.
  intros owned e H a Ha Hx. apply Exists_exists in Hx. destruct Hx as [r [Hin Hz]].
  assert (Hm : meets4 e r = true).
  { unfold meets4, in_zr in *. apply andb_true_intro. split; apply Z.ltb_lt; lia. }
  assert (existsb (meets4 e) owned = true) by (apply existsb_exists; eauto). congruence.
Qed.

Lemma errno_nstatic_check_A : existsb (meets4 (as_errno TfibB)) (as_owned_static TfibB) = false.
Proof. vm_compute. reflexivity. Qed.

Theorem errno_nstatic_A :
  forall a, as_errno TfibB <= a < as_errno TfibB + 4 -> ~ Exists (in_zr a) (as_owned_static TfibB).
Proof. exact (nstatic_of_check _ _ errno_nstatic_check_A). Qed.

Print Assumptions errno_nstatic_A.
