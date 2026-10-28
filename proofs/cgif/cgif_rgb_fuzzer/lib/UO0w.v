(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK15 YK0o YQ0k YN06 YK0s YN02 YK1j YK0v YK1a.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09 YP0a YP0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YP0j YP0g YP0h YP0i YP0q YP0m YP0o YP10 YP0v YP0x YP0z YP0n YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YO02 YO2f YO29 YO2a
YO2e YO2u YO2s UO0c UO08 UO0b UO09
UO0t YO2y YO2x UO0k.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
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
Theorem ubs2_ntfree_of_A : ntA_hyp B1 -> ntfree_hyp B1.
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
