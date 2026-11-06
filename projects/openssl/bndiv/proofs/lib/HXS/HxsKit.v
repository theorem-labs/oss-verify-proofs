(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import MState Mem Exec Frame.
From OSSVerify.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxToolkit HxQuery HxLearn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition hval_eqb (a b : hval) : bool :=
  match a, b with
  | VC x, VC y => w_eqb x y
  | VP t o, VP t' o' => (t =? t')%uint63 && w_eqb o o'
  | VU, VU => true
  | _, _ => false
  end.

Lemma hval_eqb_eq (a b : hval) : hval_eqb a b = true -> a = b.
Proof.
  destruct a as [x|t o| |], b as [y|t' o'| |]; cbn; intros H; try discriminate; try reflexivity.
  - apply w_eqb_true_iff in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2]. apply Uint63.eqb_spec in H1. apply w_eqb_true_iff in H2. subst. reflexivity.
Qed.

Lemma pword_scalar (rho : valuation) (t : int) (x : word) : rho t = bv_unsigned x -> pword rho t w_zero = x.
Proof. intros E. unfold pword. rewrite E. change (wZ w_zero) with 0. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Section Kit.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma literal_region_ok (rho : valuation) (t : int) (rg : region) (m : word -> option byte) (lo : int) (ks : list kb) (bs : list byte) :
  rg_abs rg = Some lo -> num_ok (to_Z lo) rg = true ->
  Forall2 (kb_ok rho) ks bs -> bytes_at segs m (to_Z lo) bs -> Z.of_nat (length bs) = to_Z (rg_size rg) ->
  (rg_wr rg = true -> wr_at segs m (to_Z lo) (to_Z (rg_size rg))) ->
  learn_check segs rg [(0, ks)] 0 (Z.to_nat (to_Z (rg_size rg))) = true ->
  region_ok segs rho t rg m.
Proof.
  intros Ea Hn HF Hb Hl Hwr Hck. unfold num_ok in Hn.
  apply andb_prop in Hn as [Hn N7]. apply andb_prop in Hn as [Hn N6]. apply andb_prop in Hn as [Hn N5]. apply andb_prop in Hn as [Hn N4].
  apply andb_prop in Hn as [Hn N3]. apply andb_prop in Hn as [N1 N2].
  apply Z.ltb_lt in N1, N2, N3, N6. apply Z.leb_le in N4, N5. apply Z.eqb_eq in N7.
  assert (Eb : rbase rho t rg = to_Z lo) by (unfold rbase; rewrite Ea; reflexivity).
  apply (region_ok_learn segs rho t rg m [(0, ks)]); rewrite ?Eb; try assumption.
  - intros i Hi. apply (bytes_at_mapped segs m (to_Z lo) bs Hb). lia.
  - intros X i Hi. destruct (Hwr X) as (_ & _ & W). exact (W i Hi).
  - constructor; [|constructor]. exists bs. cbn [fst snd]. rewrite Z.add_0_r. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma unknown_region_ok (rho : valuation) (t : int) (lo n al : int) (d : nat) (m : word -> option byte) :
  num_ok (to_Z lo) (RG (Some lo) n al true DUnk d IEmpty) = true -> stk segs m (to_Z lo) (to_Z lo + to_Z n) ->
  region_ok segs rho t (RG (Some lo) n al true DUnk d IEmpty) m.
Proof.
  intros Hn (_ & _ & Hs). unfold num_ok in Hn. cbn [rg_size rg_d rg_al] in Hn.
  apply andb_prop in Hn as [Hn N7]. apply andb_prop in Hn as [Hn N6]. apply andb_prop in Hn as [Hn N5]. apply andb_prop in Hn as [Hn N4].
  apply andb_prop in Hn as [Hn N3]. apply andb_prop in Hn as [N1 N2].
  apply Z.ltb_lt in N1, N2, N3, N6. apply Z.leb_le in N4, N5. apply Z.eqb_eq in N7.
  apply (region_ok_fresh segs rho t (Some lo) n al true d m); unfold rbase; cbn [rg_abs]; try assumption.
  intros i Hi. destruct (Hs (to_Z lo + i) ltac:(lia)) as [Hw Hb]. split; [exact Hb | intros _; exact Hw].
Qed.

End Kit.
