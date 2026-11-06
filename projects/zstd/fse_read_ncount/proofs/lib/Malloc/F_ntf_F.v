(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast MallocTree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocKit_B MallocModel_B F_ntf_B F_ntf_C.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocKit_B3.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Definition seq_st (ns sc : Z) (st : mstate) : mstate := record_seq sc (upd_ctx (set_seq ns) st).
#[using="Type"] Lemma fm_facts_ctx : forall st f g,
c_free_meta_head (f (s_ctx st)) = c_free_meta_head (s_ctx st) -> fm_facts st g -> fm_facts (upd_ctx f st) g.
Proof. intros st f g E H hd Hh. unfold ctx in *. cbn [upd_ctx s_ctx] in Hh. rewrite E in Hh. exact (H hd Hh). Qed.
#[using="Type"] Lemma seq_range_test sc : 0 <= sc <= 63 ->
(31 < Z.land (sc + -7) 18446744073709551615 <-> sc_in_seq_range sc = false).
Proof.
intros Hsc. change 18446744073709551615 with (Z.ones 64). Local Ltac2 Set LiaHints.tbl := fun () => "0070=11607978867.424928565455.735499738491.351215454381.763585092465.467626325467.78931373598.4 00000100<00=00F00N00S00ZSS1L1H2H02H1SS2H02GE1HS3Hsc2GES3HscS3Hsc1L".
rewrite Z.land_ones by lia.
unfold sc_in_seq_range.
destruct (Z.lt_ge_cases sc 7) as [L|GE].
- replace ((sc + -7) mod 2 ^ 64) with (sc + -7 + 2^64).
2:{ symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia. }
destruct (Z.leb_spec 7 sc); destruct (Z.ltb_spec sc 39); cbn; split; intros; try reflexivity; try lia.
- rewrite Z.mod_small by lia.
destruct (Z.leb_spec 7 sc); destruct (Z.ltb_spec sc 39); cbn; split; intros; try reflexivity; try discriminate; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma unmap_seqs_empty st : unmap_seqs (upd_ctx (fun c => set_unmap_seq_map ∅ c) st) = zeros 32.
Proof. reflexivity. Qed.
End CANSEC1.
