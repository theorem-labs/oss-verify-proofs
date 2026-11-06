(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import List.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5STree5STREE~~~~~~05stree37Corelib4Init5Logicka2eq04SRet05sbind04SVis04steqka3iff05strel37Corelib4Init9Datatypeso94prod99OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5STree5STREE5ERUNS~~~~~~q85erunso94Noneo96optiono93fsto93snd" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Set Implicit Arguments.

Section STREE.
Variable E : Type.   (* [comment removed for export] *)
Variable A : Type.   (* [comment removed for export] *)

Inductive stree (R : Type) : Type :=
| SRet (r : R)
| SVis (e : E) (k : A -> stree R).

Arguments SRet {R} r.
Arguments SVis {R} e k.

Fixpoint sbind (R S : Type) (t : stree R) (f : R -> stree S) {struct t} : stree S :=
  match t with
  | SRet r => f r
  | SVis e k => SVis e (fun a => sbind (k a) f)
  end.

Lemma sbind_ret_l : ltac2:(zQ "40!k3!le!m3!m9>1RT>1ST>1r^2>1f>0^3@1$0^3@3$1@1$0^3@4$3^4^3@2$2^4^2^1@1^1^2").
Proof. reflexivity. Qed.

Lemma sbind_vis : ltac2:(zQ "40!k3!n0!m9!le>1RT>1ST>1e?1E>1k>0?1A@1$0^4>1f>0^4@1$0^4@3$3@1$0^4@4$2^5^4@3$1^5^3^2^1@3$1^4^3\1a?1A@4$2^6^5@1^3^1^2").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Inductive steq (R : Type) : stree R -> stree R -> Prop :=
| steq_ret : forall r, steq (SRet r) (SRet r)
| steq_vis : forall e k1 k2, (forall a, steq (k1 a) (k2 a)) -> steq (SVis e k1) (SVis e k2).

Lemma steq_refl : ltac2:(zQ "20!n6!k3>1RT>1t@1$1^1@3$0^2^1^1").
Proof. induction t; constructor; auto. Qed.

Lemma sbind_assoc : ltac2:(zQ "30!m9!k3!n6>1RT>1ST>1TT>1t@1$1^3>1f>0^4@1$1^4>1g>0^4@1$1^4@3$2^4@4$0^5^4@4$0^6^5^3^2^1@4$0^6^4^3\1r^6@4$0^6^5@1^3^1^2").
Proof. induction t; intros; simpl. apply steq_refl. constructor; auto. Qed.

(* [comment removed for export] *)
Definition smap : ltac2:(zQ "10!k3>1RT>1ST>1f>0^2^2>1t@1$0^3@1$0^3") := ltac2:(zQ "30!m3!m9!k3\1RT\1ST\1f>0^2^2\1t@1$2^3@4$1^4^3^1\1r^4@2$0^4@1^3^1").

(* [comment removed for export] *)
Inductive strel (R1 R2 : Type) (RR : R1 -> R2 -> Prop) : stree R1 -> stree R2 -> Prop :=
| strel_ret : forall r1 r2, RR r1 r2 -> strel RR (SRet r1) (SRet r2)
| strel_vis : forall e k1 k2, (forall a, strel RR (k1 a) (k2 a)) -> strel RR (SVis e k1) (SVis e k2).

Lemma strel_eq_steq : ltac2:(zQ "50!k3!le!nc!n6!o2>1RT>2t1@1$0^1>2t2@1$0^2@2$2@5$4^3^3@1$1^3^2^1@3$3^3^2^1").
Proof.
  split.
  - induction 1; subst; constructor; auto.
  - induction 1; constructor; auto.
Qed.

Lemma strel_sbind : ltac2:(zQ "30!k3!o2!m9>2R1T>2R2T>2S1T>2S2T>2RR>0^4>0^4P>2SS>0^3>0^3P>2t1@1$0^6>2t2@1$0^6>2f1>0^8@1$0^7>2f2>0^8@1$0^7>0@5$1^a^9^6^4^3>0>2r1^b>2r2^b>0@2^9^2^1@5$1^c^b^9@1^6^3@1^5^2@5$1^a^9^7@4$2^c^a^6^4@4$2^b^9^5^3").
Proof. induction 1; intros; simpl; auto. constructor; auto. Qed.

Lemma strel_trans_eq : ltac2:(zQ "30!k3!o2!le>2R1T>2R2T>2RR>0^2>0^2P>2t1@1$0^3>2t2@1$0^3>2t3@1$0^4>0@5$1^6^5^4^3^2>0@5$1^6^6@1$2^6^3^2@5$1^8^7^6^5^3").
Proof.
  intros R1 R2 RR t1 t2 t3 H; revert t3; induction H; intros t3 Ht; inversion Ht; subst.
  - constructor; auto.
  - constructor; eauto.
Qed.

(* [comment removed for export] *)
Section ERUNS.
Variable O : Type.
Variable sel : ltac2:(zQ "10!hg0>0?1O>0?1E@1$0?1A").
Variable upd : ltac2:(zQ "00>0?1O>0?1E>0?1A?1O").

Fixpoint eruns (R : Type) (o : O) (t : stree R) {struct t} : stree (O * R) :=
  match t with
  | SRet r => SRet (o, r)
  | SVis e k =>
      match sel o e with
      | Some a => eruns (upd o e a) (k a)
      | None => SVis e (fun a => eruns (upd o e a) (k a))
      end
  end.

Lemma eruns_vis_keep : ltac2:(zQ "70!q1!le!v1!n0!k3!v9!hg0>1RT>1o?1O>1e?1E>1k>0?1A@1$4^4>0@3$1@1$6?1A@2?3sel^3^2@1$5?1A@3$1@1$4@2$0?1O^5@3$2^5^4@3$3^5^3^2@3$3@2$0?1O^5^3\1a?1A@3$2^6@3?3upd^5^4^1@1^3^1").
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma eruns_sbind : ltac2:(zQ "70!q1!v1!m9!k3!hg9!hgf!n6>1RT>1ST>1o?1O>1t@1$3^3>1g>0^4@1$3^4@3$6@2$0?1O^4@3$1^4^3@4$2^5^4^2^1@4$2@2$0?1O^5@2$0?1O^4@3$1^5^3^2\1x@2$0?1O^5@3$1^5@3$4?1O^6^1@1^2@3$5?1O^6^1").
Proof.
  intros R S o t; revert o; induction t; intros; simpl.
  - apply steq_refl.
  - destruct (sel o e); simpl; auto. constructor; auto.
Qed.
End ERUNS.

(* [comment removed for export] *)
Section RUN.
Variable O : Type.
Variable oracle : ltac2:(zQ "10!q1>0?1O>0?1E@2$0?1A?1O").

Fixpoint srun (R : Type) (o : O) (t : stree R) {struct t} : list (E * A) * O * R :=
  match t with
  | SRet r => (nil, o, r)
  | SVis e k =>
      let (a, o1) := oracle o e in
      let '(tr, o2, r) := srun o1 (k a) in
      ((e, a) :: tr, o2, r)
  end.
End RUN.

(* [comment removed for export] *)
Definition srun0 (f : E -> A) (R : Type) (t : stree R) : list (E * A) * R :=
  let '(tr, _, r) := srun (fun (_ : unit) e => (f e, tt)) tt t in (tr, r).

End STREE.

Arguments SRet {E A R} r.
Arguments SVis {E A R} e k.
Arguments sbind {E A R S} t f.
Arguments smap {E A R S} f t.
Arguments steq {E A R} _ _.
Arguments strel {E A R1 R2} RR _ _.
Arguments eruns {E A O} sel upd {R} o t.
Arguments srun {E A O} oracle {R} o t.
Arguments srun0 {E A} f {R} t.

Declare Scope stree_scope.
Notation "x <-- c1 ;; c2" := (sbind c1 (fun x => c2))
  (at level 65, c1 at next level, right associativity) : stree_scope.
Notation "' pat <-- c1 ;; c2" := (sbind c1 (fun x__ => match x__ with pat => c2 end))
  (at level 65, pat pattern, c1 at next level, right associativity) : stree_scope.
(* [comment removed for export] *)
