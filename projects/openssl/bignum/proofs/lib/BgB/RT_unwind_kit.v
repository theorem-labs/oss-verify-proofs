(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Mem Frame Cells Step Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface SitePaths.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition paths_from (f : Z) : list (list Z) :=
  match find (fun e => fst e =? f) PATHS with Some e => snd e | None => [] end.

Definition site_ctx (f : Z) (ras : list Z) : Prop := forall p, In p (paths_from f) -> In (p ++ ras) SITE_TRACES.

Definition path_memb (p : list Z) (l : list (list Z)) : bool := existsb (site_eqb p) l.

Lemma path_memb_In : forall p l, path_memb p l = true -> In p l.
Proof. intros p l H. unfold path_memb in H. apply existsb_exists in H as (t & Hin & E). apply site_eqb_eq in E. subst t. exact Hin. Qed.

Definition site_ctxb (f : Z) (ras : list Z) : bool := forallb (fun p => site_memb (p ++ ras)) (paths_from f).

Lemma site_ctx_root : forall f ras, site_ctxb f ras = true -> site_ctx f ras.
Proof. intros f ras H p Hp. apply site_memb_In. exact (proj1 (forallb_forall _ _) H p Hp). Qed.

Definition call_edgeb (f r g : Z) : bool := forallb (fun p => path_memb (p ++ [r]) (paths_from f)) (paths_from g).

Lemma site_ctx_call : forall f r g ras, call_edgeb f r g = true -> site_ctx f ras -> site_ctx g (r :: ras).
Proof.
  intros f r g ras H HF p Hp. pose proof (proj1 (forallb_forall _ _) H p Hp) as X. cbv beta in X. apply path_memb_In in X.
  pose proof (HF _ X) as Y. rewrite <- app_assoc in Y. exact Y.
Qed.

Definition tail_edgeb (f g : Z) : bool := forallb (fun p => path_memb p (paths_from f)) (paths_from g).

Lemma site_ctx_tail : forall f g ras, tail_edgeb f g = true -> site_ctx f ras -> site_ctx g ras.
Proof. intros f g ras H HF p Hp. apply HF. apply path_memb_In. exact (proj1 (forallb_forall _ _) H p Hp). Qed.

Definition leaf_edgeb (f r : Z) : bool := path_memb [r] (paths_from f).

Lemma site_ctx_leaf : forall f r ras, leaf_edgeb f r = true -> site_ctx f ras -> In (r :: ras) SITE_TRACES.
Proof. intros f r ras H HF. apply path_memb_In in H. exact (HF _ H). Qed.

Definition leaf_tailb (f : Z) : bool := path_memb [] (paths_from f).

Lemma site_ctx_leaf_tail : forall f ras, leaf_tailb f = true -> site_ctx f ras -> In ras SITE_TRACES.
Proof. intros f ras H HF. apply path_memb_In in H. exact (HF _ H). Qed.

