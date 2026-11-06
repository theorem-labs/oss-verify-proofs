(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk RefMemcpyLib.
Import ListNotations.
Open Scope bv_scope.

Lemma in_regs_dec : forall (r : reg) (l : list reg),
  existsb (fun x => bv_eqb x r) l = true -> In r l.
Proof.
  intros r l H. apply existsb_exists in H as (x & Hx & E).
  unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. subst x. exact Hx.
Qed.
Lemma not_in_regs_dec : forall (r : reg) (l : list reg),
  forallb (fun x => negb (bv_eqb x r)) l = true -> ~ In r l.
Proof.
  intros r l H Hin. pose proof (proj1 (forallb_forall _ _) H r Hin) as H'. cbn beta in H'.
  rewrite bv_eqb_refl in H'. discriminate H'.
Qed.
Ltac RefMemcpyLib.kept_reg ::= first [ apply in_regs_dec; reflexivity | cbv [callee_kept In]; intuition congruence ].
Ltac RefMemcpyLib.not_kept ::= first [ apply not_in_regs_dec; reflexivity | cbv; intuition discriminate ].
Ltac kept_reg := RefMemcpyLib.kept_reg.
Ltac not_kept := RefMemcpyLib.not_kept.
