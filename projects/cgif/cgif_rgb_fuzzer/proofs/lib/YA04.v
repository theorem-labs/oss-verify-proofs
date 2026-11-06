(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK15 YK18 YK00 YK05 YK06 YK0d YK0f YK0g YK0a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA0c YA0e.
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

End a.
