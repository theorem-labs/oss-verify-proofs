(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0b.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YG0b.v (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_headamp. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YG0b.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK16 YK0n YK11 YK0h YK0i YK14 YK1c YK0v YK02 YK0p YK15.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK0y YK1b YK00 YK01 YK13 YP0n YK04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import YK05_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import YA0n_w YA05_w YA09_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK0g.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import YA08_w YA00_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK0c YK0e YK0f YK09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import YA0c_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import YA0e_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import YG0n_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05 YK06.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c.
Section K.
Definition MWF (md : Model) : Prop := model_ivs_wf md /\ seps (vm_maps (m_vmmaps md)).
Lemma pairwise_seps : forall l,
pairwise (fun p q : word * word => bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p)) l <-> seps l.
Proof.
induction l as [|x l IH]; cbn.
- split; [intros _; constructor | intros _; exact I].
- split.
+ intros [F P]. constructor; [| apply IH; exact P]. apply Forall_impl with (2 := F). intros q Hq. exact Hq.
+ intros Hs. inversion Hs as [| p l' F P]; subst. split; [| apply IH; exact P]. apply Forall_impl with (2 := F). intros q Hq. exact Hq.
Qed.
Lemma amwf_MWF : forall md, amwf_ivs md <-> MWF md.
Proof.
intros md. unfold amwf_ivs, MWF, model_ivs_wf, ivs_wf, iv_wf, B, YK0g.S. rewrite pairwise_seps. tauto.
Qed.
End K.
End c.
