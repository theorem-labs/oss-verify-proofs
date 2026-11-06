(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "memb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "MFree"; "mslot"; "set_metas"; "sptr"; "st_metas"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb"; "zmetas"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition zmeta (X : list sptr) (q : sptr) (x : mslot) : mslot := ltac2:(tb__ "0|1|
S0S4L_;S2Vq;VX;A2S3S1S6A1M0G0A2Vx;X0x2").
Fixpoint zmetas (X : list sptr) (l : list (sptr * mslot)) : list (sptr * mslot) :=
  match l with [] => [] | (q, x) :: t => (q, zmeta X q x) :: zmetas X t end.
Definition zomb (X : list sptr) (s : astate) : astate := ltac2:(tb__ "0|0|
S5S8VX;S7Vs;A1A2Vs;A2").
