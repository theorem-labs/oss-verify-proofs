(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Definition EHEAD1n (cx : cctx) (g : eg) (e : est) (v : Z) : list cell := removelast (EHEAD1 cx g e) ++ [C4 (Z_to_bv 64 v)].
(* [comment removed for export] *)
Definition g_mtf_on (g : eg) : eg := EG (g_aie g) (g_sort g) true (g_bs g) (g_zbits g).
(* [comment removed for export] *)
Definition gm_e (e : est) : est := fst (generateMTFValues e znew).

Section WithSegs.
  Variables (cx : cctx) (segs : list Segment).
  Notation E := (c_E cx). Notation J := (c_J cx).
  (* [comment removed for export] *)
  Definition ememN (g : eg) (e : est) (v : Z) (m : word -> option byte) : Prop :=
    rw_cells segs m E (EHEAD1n cx g e v) /\
    u8arr segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) /\
    u8arr segs m (E + 384) (ovb (e_unseqToSeq e) (jseg J 384 256) 256) /\
    rw_cells segs m (E + 640) (EHEAD2 cx g e) /\
    u32arr segs m (E + 672) (ovw (e_mtfFreq e) (jseg J 672 1032) 258) /\
    u8arr segs m (E + 1704) (ovb (e_selector e) (jseg J 1704 18002) 18002) /\
    u8arr segs m (E + 19706) (ovb (e_selectorMtf e) (jseg J 19706 18002) 18002) /\
    u8arr segs m (E + 37708) (ovb (e_len e) (jseg J 37708 1548) 1548) /\
    u32arr segs m (E + 39256) (ovw (e_code e) (jseg J 39256 6192) 1548) /\
    u32arr segs m (E + 45448) (ovw (e_rfreq e) (jseg J 45448 6192) 1548) /\
    u32arr segs m (E + 51640) (ovw (e_len_pack e) (jseg J 51640 4128) 1032).
End WithSegs.

(* [comment removed for export] *)
Definition genMTF_W (cx : cctx) (ylo yhi : Z) : list (Z * Z) :=
  [(c_E cx, c_E cx + ESTATE_SIZE); (c_A1 cx, c_A1 cx + ARR1_SIZE); (ylo, yhi)].

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.
(* [comment removed for export] *)
