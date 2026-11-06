(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Fixpoint in_ivsb (W : list (Z * Z)) (x : Z) : bool :=
  match W with
  | [] => false
  | (lo, hi) :: W' => ((lo <=? x) && (x <? hi)) || in_ivsb W' x
  end.

Lemma in_ivsb_false_outside : forall W x, in_ivsb W x = false <-> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [tauto|].
  rewrite Bool.orb_false_iff, <- IH. rewrite Bool.andb_false_iff, Z.leb_gt, Z.ltb_ge. split.
  - intros [H1 H2]. split; [lia| exact H2].
  - intros [H1 H2]. split; [lia| exact H2].
Qed.

Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto. Qed.

Definition mmix (W1 : list (Z * Z)) (m m' : word -> option byte) : word -> option byte :=
  fun x => if in_ivsb W1 (bv_unsigned x) then m' x else m x.

Theorem munch_split : forall W1 W2 m m',
  munch (W1 ++ W2) m m' -> wmono asegs m m' ->
  exists m1, munch W1 m m1 /\ wmono asegs m m1 /\ munch W2 m1 m' /\ wmono asegs m1 m'.
Proof.
  intros W1 W2 m m' MU WM. exists (mmix W1 m m').
  assert (WV : forall (mm : word -> option byte) x, wview asegs mm x <> None <-> (mm x <> None \/ wview asegs (fun _ => None) x <> None)).
  { intros mm x. unfold wview. destruct (mm x); [split; [intros _; left; discriminate| intros _; discriminate]|]. tauto. }
  split; [| split; [| split]].
  - intros x Hx. unfold mmix. destruct (in_ivsb W1 (bv_unsigned x)) eqn:E; [| reflexivity].
    apply in_ivsb_false_outside in Hx. congruence.
  - intros x Hx. apply (proj2 (WV _ x)). unfold mmix. destruct (in_ivsb W1 (bv_unsigned x)); [exact (proj1 (WV m' x) (WM x Hx))| exact (proj1 (WV m x) Hx)].
  - intros x Hx. unfold mmix. destruct (in_ivsb W1 (bv_unsigned x)) eqn:E; [reflexivity|].
    apply MU. apply outside_app. split; [apply in_ivsb_false_outside; exact E| exact Hx].
  - intros x Hx. apply (proj1 (WV _ x)) in Hx. unfold mmix in Hx. destruct (in_ivsb W1 (bv_unsigned x)) eqn:E.
    + exact (proj2 (WV m' x) Hx).
    + apply WM. exact (proj2 (WV m x) Hx).
Qed.

(* [comment removed for export] *)
Lemma munch_regroup : forall W W' m m', (forall iv, In iv W -> In iv W') -> munch W m m' -> munch W' m m'.
Proof.
  intros W W' m m' SUB MU. eapply munch_weaken; [| exact MU]. intros x Hx.
  assert (G : forall V x, outside V x <-> forall iv, In iv V -> ~ (fst iv <= x < snd iv)).
  { intros V y. induction V as [|[lo hi] V IH]; cbn; [split; [intros _ iv []| intros; exact I]|].
    rewrite IH. split.
    - intros [H1 H2] iv [<-|Hiv]; [exact H1| exact (H2 iv Hiv)].
    - intros H. split; [exact (H (lo, hi) (or_introl eq_refl))| intros iv Hiv; exact (H iv (or_intror Hiv))]. }
  apply G. intros iv Hiv. apply (proj1 (G W' x) Hx). apply SUB. exact Hiv.
Qed.


End CeilWrap.
