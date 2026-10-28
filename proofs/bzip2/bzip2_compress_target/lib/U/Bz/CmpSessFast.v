(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
Import ListNotations.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Frame.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpSess.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac inside_pick :=
  lazymatch goal with
  | |- (?lo <= ?a /\ _ <= _) \/ _ =>
      first [ (let b1 := CmpSess.sep_base lo in let b2 := CmpSess.sep_base a in CmpSess.sep_same b1 b2); left; split; lia
            | right; inside_pick ]
  | |- (?lo <= ?a /\ _ <= _) =>
      (let b1 := CmpSess.sep_base lo in let b2 := CmpSess.sep_base a in CmpSess.sep_same b1 b2); split; lia
  end.

(* [comment removed for export] *)
Fixpoint fp_in (lo hi : Z) (Wq : list ivl) : Prop :=
  match Wq with [] => False | (lo', hi') :: Wq' => (lo' <= lo /\ hi <= hi') \/ fp_in lo hi Wq' end.
Fixpoint fp_incl (W Wq : list ivl) : Prop :=
  match W with [] => True | (lo, hi) :: W' => fp_in lo hi Wq /\ fp_incl W' Wq end.
Lemma outside_fp_in : forall Wq lo hi x, outside Wq x -> fp_in lo hi Wq -> ~ (lo <= x < hi).
Proof.
  induction Wq as [|[lo' hi'] Wq IH]; intros lo hi x HO HI; cbn [fp_in outside] in *; [contradiction|].
  destruct HO as [HO1 HO2]. destruct HI as [[H1 H2]|HI]; [lia| exact (IH lo hi x HO2 HI)].
Qed.
Lemma outside_incl : forall W Wq x, outside Wq x -> fp_incl W Wq -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros Wq x HO HI; cbn [fp_incl outside] in *; [exact I|].
  destruct HI as [HI1 HI2]. split; [exact (outside_fp_in Wq lo hi x HO HI1)| exact (IH Wq x HO HI2)].
Qed.

Ltac fp_ivls T :=
  lazymatch T with
  | ~ (?lo <= _ < ?hi) /\ ?R => let r := fp_ivls R in constr:(@cons ivl (lo, hi) r)
  | True => constr:(@nil ivl)
  end.
Ltac fp_in_tac :=
  hnf;
  lazymatch goal with
  | |- (?lo' <= ?lo /\ _ <= _) \/ _ =>
      first [ (let b1 := CmpSess.sep_base lo' in let b2 := CmpSess.sep_base lo in CmpSess.sep_same b1 b2); left; split; lia
            | right; fp_in_tac ]
  end.
Ltac fp_incl_tac :=
  lazymatch goal with
  | |- fp_incl _ _ => first [ exact I | split; [ fp_in_tac | fp_incl_tac ] ]
  end.
Ltac outside_tac :=
  lazymatch goal with
  | |- Frame.outside ?W ?x =>
      match goal with
      | H : Frame.outside ?Wq x |- _ => apply (outside_incl W Wq x H); fp_incl_tac
      | H : ~ (_ <= x < _) /\ _ |- _ =>
          let T := type of H in let Wq := fp_ivls T in apply (outside_incl W Wq x H); fp_incl_tac
      end
  end.

Ltac slia_sep_fast :=
  lazymatch goal with
  | |- True => exact I
  | |- (_ <= _ \/ _ <= _) /\ _ => split; [ first [ CmpSess.sep_tac | lia ] | slia_sep_fast ]
  | |- (_ <= _ \/ _ <= _) => first [ CmpSess.sep_tac | lia ]
  | |- (_ <= _ /\ _ <= _) \/ _ => first [ inside_pick | CmpSess.slia_sep ]
  | |- Frame.outside _ _ => first [ outside_tac | CmpSess.slia_sep ]
  | |- Frame.disjoint_from _ _ _ =>
      (* [comment removed for export] *)
      first [ exact I | split; [ first [ CmpSess.sep_tac | lia ] | slia_sep_fast ] | CmpSess.slia_sep ]
  | |- _ => CmpSess.slia_sep
  end.
