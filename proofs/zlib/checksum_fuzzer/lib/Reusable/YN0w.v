(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02 YK1j YK0v YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0b YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0u YO15 YO10 YO12 YO14 YO0t YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN02 YN2b YN25 YN26
YN2a YN2q YN2o YN0b YN07 YN0a YN08
YN0t YN2u YN2t YN0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable B : malloc_syms.
Definition nt_goal (fuel : nat) X U L A g i am regs mem md : Prop :=
Inv X (Some (g, i)) U A -> usedX X A g am -> (forall c, 0 <= U c) ->
((am_prev am, am_next am) <> (None, None) -> active_hd A (am_sc am) <> Some g -> am_freed am <> 0) ->
(fneed (am_sc am) <= fuel)%nat -> bounded A ->
nt_pre B X fuel L A regs mem md g i ->
mreal (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 (pc_nontrivial_free (ms_pcs B))) mem (seg_rom (ms_segs B))) md)
(nontrivial_free fuel g i A)
(nt_post B X fuel L A regs mem md).
Lemma ntfree_hyp_iff : ntfree_hyp B <-> forall fuel X U L A g i am regs mem md, nt_goal fuel X U L A g i am regs mem md.
Proof. unfold ntfree_hyp, nt_goal. split; intros H; intros; eapply H; eauto. Qed.
Definition ntA_hyp : Prop :=
forall fuel,
(forall X U L A g i am regs mem md, nt_goal fuel X U L A g i am regs mem md) ->
forall X U L A g i am regs mem md,
nt_C1 A g i am = true -> nt_goal (S fuel) X U L A g i am regs mem md.
End b.
Theorem src0_ntfree_of_A : ntA_hyp B1 -> ntfree_hyp B1.
Proof.
intros HA. apply (proj2 (ntfree_hyp_iff B1)). intros fuel. induction fuel as [|fuel IH].
- intros X U L A g i am regs mem md HI Hu HU HR2g Hf HB NPRE. exfalso.
unfold fneed in Hf. destruct (am_sc am <? 48) eqn:E; [apply Z.ltb_lt in E|]; lia.
- intros X U L A g i am regs mem md HI Hu HU HR2g Hf HB NPRE.
destruct (nt_C1 A g i am) eqn:HC1; [exact (HA fuel IH X U L A g i am regs mem md HC1 HI Hu HU HR2g Hf HB NPRE)|].
destruct (ntB_cases X U A g i am HI Hu HR2g HC1) as (pM & vM & h & hp & ah & ahp & Hval & PF & VF).
pose proof NPRE as (_ & _ & _ & _ & _ & ST & _). destruct (st_guard _ _ ST) as [gv Hgv].
set (p := match pM with MP0 => P0 | MP1V1 => P1V1 | MP1V2 => P1V2 | MP2V2 => P2V2 end).
set (v := match vM with MVB1 => VB1 | MVB2 => VB2 | MVB3 => VB3 | MVB4a => VB4a | MVB4b => VB4b end).
assert (Ep : toMp p = pM) by (destruct pM; reflexivity). assert (Ev : toMv v = vM) by (destruct vM; reflexivity).
rewrite <- Ep in PF, Hval. rewrite <- Ev in VF, Hval. rewrite <- validB_M in Hval.
assert (HI2 : Inv X None U (A' A g i am v h hp ah ahp)).
{ pose proof (nontrivial_free_spec (S fuel) X U A g i am _ HI Hu HU HR2g Hf (fun r H => H)) as T.
rewrite (nt_tree_B X U fuel L A g i am regs p v h hp ah ahp HI Hu HC1 Hval VF) in T. exact (proj1 T). }
exact (ntB_mreal X U fuel L A g i am regs mem md gv p v h hp ah ahp HI Hu HB NPRE Hgv HC1 Hval PF VF HI2).
Qed.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
