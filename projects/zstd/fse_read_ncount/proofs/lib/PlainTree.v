(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prog ModelInv ModelOK ImgFacts.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg.
Require OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain.PlainClosed.
Theorem plain_tree_ok_L : forall L, 2^31 <= L ->
tree_ok psegs p_init_pc p_phdrs L
(Prog.prog psegs PREAD_STAGE) (epost (fun (_ : unit) (_ : machine_state) => True)).
Proof.
intros L HL en inp Hen Hinp. split.
- exact (Plain.PlainClosed.plain_impl_closed en inp Hen Hinp).
- exact (prog_model_ok_plain_L L PREAD_STAGE en inp HL Hen Hinp).
Qed.
