(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg SpinAlg AxSymExec3 AsanPlanCore CxPlan CxPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxAcctShape CxNodesLibE.
Import ListNotations.
Import AX2. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Definition xn_plus (f g : nat -> list expr -> acs -> option acs) : nat -> list expr -> acs -> option acs :=
  fun id args cs => match f id args cs with Some r => Some r | None => g id args cs end.
Definition xe_plus (f g : nat -> list expr -> acs -> option (Z * list spiece * acs)) : nat -> list expr -> acs -> option (Z * list spiece * acs) :=
  fun id args cs => match f id args cs with Some r => Some r | None => g id args cs end.
Definition xb_plus (f g : nat -> list expr -> acs -> option (acs * acs)) : nat -> list expr -> acs -> option (acs * acs) :=
  fun id args cs => match f id args cs with Some r => Some r | None => g id args cs end.

Section Plus.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable ISP : Z.
  Variable FS0 : Fs.Fs.

  Lemma node1_stmt_plus : forall pre (f g : acs -> option acs),
    node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 pre f ->
    node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 pre g ->
    node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 pre (fun cs => match f cs with Some r => Some r | None => g cs end).
  Proof.
    intros pre f g Hf Hg cs cs' E R FULL model T HC Hpre Hn Hk.
    destruct (f cs) as [r|] eqn:Ef.
    - injection Hn as ->. exact (Hf cs cs' E R FULL model T HC Hpre Ef Hk).
    - exact (Hg cs cs' E R FULL model T HC Hpre Hn Hk).
  Qed.

  Theorem ext_stmt_plus : forall f g,
    ext_stmt SEGS A nx0 LIMIT f SINV argH ISP FS0 -> ext_stmt SEGS A nx0 LIMIT g SINV argH ISP FS0 ->
    ext_stmt SEGS A nx0 LIMIT (xn_plus f g) SINV argH ISP FS0.
  Proof. intros f g Hf Hg id args. unfold xn_plus. apply node1_stmt_plus; [apply Hf | apply Hg]. Qed.

  Theorem emit_stmt_plus : forall f g,
    emit_stmt SEGS A nx0 LIMIT f SINV argH ISP FS0 -> emit_stmt SEGS A nx0 LIMIT g SINV argH ISP FS0 ->
    emit_stmt SEGS A nx0 LIMIT (xe_plus f g) SINV argH ISP FS0.
  Proof.
    intros f g Hf Hg id args cs fd ps cs' E R FULL model T HC Hn HT Hk. unfold xe_plus in Hn.
    destruct (f id args cs) as [r|] eqn:Ef.
    - rewrite Hn in Ef. exact (Hf id args cs fd ps cs' E R FULL model T HC Ef HT Hk).
    - exact (Hg id args cs fd ps cs' E R FULL model T HC Hn HT Hk).
  Qed.

  Theorem ext2_stmt_plus : forall f g,
    ext2_stmt SEGS A nx0 LIMIT f SINV argH ISP FS0 -> ext2_stmt SEGS A nx0 LIMIT g SINV argH ISP FS0 ->
    ext2_stmt SEGS A nx0 LIMIT (xb_plus f g) SINV argH ISP FS0.
  Proof.
    intros f g Hf Hg id args cs csa csb E R FULL model TA TB HC Hn HA HB. unfold xb_plus in Hn.
    destruct (f id args cs) as [r|] eqn:Ef.
    - rewrite Hn in Ef. exact (Hf id args cs csa csb E R FULL model TA TB HC Ef HA HB).
    - exact (Hg id args cs csa csb E R FULL model TA TB HC Hn HA HB).
  Qed.
End Plus.
