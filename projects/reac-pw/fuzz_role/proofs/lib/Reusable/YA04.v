(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA04.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YA04.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_role. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK15 YK18 YK00 YK04 YK05 YK0c YK0e YK0f YK09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YA0c YA0e.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
Section a.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable TOP : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Definition OBL_mmap2 : Prop := mm2_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 (node_mmap2g A nx0 LIMIT).
Definition OBL_mmapin : Prop := forall hole : bool, mm3_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 (node_mmapin_g A LIMIT hole).
Definition OBL_mmapin2 : Prop := mm2_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 (node_mmapin2_g A LIMIT).
Definition OBL_mprotect2 : Prop := mm2_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 (node_mprotect2g A LIMIT).
Definition OBL_brk2 : Prop := brk2_stmt SEGS A nx0 LIMIT TOP SINV argH FS0.
Definition OBL_sys : Prop := forall y : snode, sys_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 y.
Definition OBL_exit : Prop := exit_stmt SEGS A LIMIT TOP SINV argH FS0.
Definition OBL_all : Prop := OBL_mmap2 /\ OBL_mmapin /\ OBL_mprotect2 /\ OBL_brk2 /\ OBL_sys /\ OBL_exit.
Lemma OBL_mmap2_unfold :
OBL_mmap2 <->
forall cs csa csb E R FULL model TB,
cs_ok SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model ->
is_ecall_at SEGS cs = true ->
node_mmap2g A nx0 LIMIT cs = Some (csa, csb) ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
cs_ok SEGS A LIMIT TOP SINV argH FS0 E' csb R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg_of SEGS R' (pc csb) FULL' model') TB) ->
srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) TB.
Proof. unfold OBL_mmap2, mm2_stmt. tauto. Qed.
End a.
