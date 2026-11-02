(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0w.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0k.
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
