(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List String Ascii.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Cli Require Import CliVerdict CliSpecG.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxMem AxZZ AxState AxSys AxJoin AxJoinSound AxEntryRel.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxModelRel AsanWShape.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Export AxFinalK.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition pieces_eqb (a b : list piece) : bool := list_eqb piece_eqb a b.

Lemma pieces_val_app_intro (ρ : valuation) (l1 l2 : list piece) (o1 o2 : list byte) :
  pieces_val ρ l1 o1 -> pieces_val ρ l2 o2 -> pieces_val ρ (l1 ++ l2) (o1 ++ o2).
Proof.
  revert o1. induction l1 as [|p l1 IH]; intros o1 H1 H2; cbn [app pieces_val] in *.
  - subst o1. exact H2.
  - destruct p as [b|k].
    + destruct H1 as (y & o' & -> & Hy & H'). exists y, (o' ++ o2). split; [reflexivity|]. split; [exact Hy | exact (IH o' H' H2)].
    + destruct H1 as (o' & -> & H'). exists (o' ++ o2). split; [rewrite app_assoc; reflexivity | exact (IH o' H' H2)].
Qed.

Definition lit_bytes (bs : list byte) : list piece := map (fun b => PB (BL (of_Z (bv_unsigned b)))) bs.
Definition lit_pieces (s : string) : list piece := lit_bytes (s2b s).

Definition nl_str : string := String (ascii_of_nat 10) EmptyString.

Definition pat_usage : list piece := lit_pieces "usage: " ++ [PS 0] ++ lit_pieces (" INPUT" ++ nl_str).

Definition KT_usage (fs0 : Fs.Fs) (ρ : valuation) (o : list byte) : TSet := KDer (t_die (msg_usage (dec_str 0 ρ)) fs0) o.

Definition pin0 (s : store) (k : Z) : bool :=
  match lrange s (lvar (lenvar k) 1) with Some (lo, hi) => (lo =? 0) &&& (hi =? 0) | None => false end.

Fixpoint drop_empty (s : store) (pat : list piece) : list piece :=
  match pat with
  | [] => []
  | PS k :: r => if pin0 s k then drop_empty s r else PS k :: drop_empty s r
  | p :: r => p :: drop_empty s r
  end.

Definition pieces_match (s : store) (out pat : list piece) : bool := pieces_eqb out pat ||| pieces_eqb out (drop_empty s pat).

Definition final_ok (segs : list Segment) (pat : list piece) (A : AST) : bool :=
  match xlit (aget (a_regs A) 17%uint63), xlit (aget (a_regs A) 10%uint63) with
  | Some x, Some y =>
      (x =? 94) && (y =? 2) && pieces_match (a_facts A) (am_out (a_model A)) pat &&
      match fetch_word segs (wbv (a_pc A)) with Some w => is_ecall w | None => false end
  | _, _ => false
  end.

Section FinalGen.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.

Notation RR ρ := (R segs amodel (MR segs fs0 ρ) LIM ρ).

End FinalGen.

