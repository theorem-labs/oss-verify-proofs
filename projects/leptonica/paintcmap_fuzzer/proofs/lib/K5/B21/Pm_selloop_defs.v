(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition SEL_HEAD : Z := 0x93f04.     (* [comment removed for export] *)
Definition SEL_EXIT : Z := 0x93ed8.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sel_exit (sp gp tp t2 s0 s1 a3 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (data rsz : Z) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' a0' a1' a2' a6' s9' s10' s11' t6' : word) (m' : mem),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3 a4 a5 a6' a7 s2 s3 s4 s5 s6 s7 s8 s9' s10' s11' t3 t4 t5 t6')
             F (Z_to_bv 64 SEL_EXIT) fc None m' (seg_rom asegs)
    /\ munch [(data, data + rsz)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

(* [comment removed for export] *)
Definition sel_rows_stmt : Prop :=
  forall (ra sp gp tp t0 t1 s0 a0 a1 a6 s2 s3 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s1v fr data w h d wpl idx : Z) (c24 c32 : word) (bs : list byte),
    In d [1; 2; 4; 8] -> 0 < w <= 20000 -> 0 < h <= 20000 -> wpl = (w * d + 31) / 32 -> 0 < 4 * (wpl * h) <= 0x4000000 ->
    0 <= idx <= 256 ->
    (* [comment removed for export] *)
    0 < data -> data mod 16 = 0 -> data + 4 * (wpl * h) <= 2^47 ->
    (data + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
    (data + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= data) ->
    u8arr asegs m data bs -> Z.of_nat (length bs) = 4 * (wpl * h) -> acc asegs m data (4 * (wpl * h)) ->
    (* [comment removed for export] *)
    0 < fr -> fr mod 64 = 0 -> fr + 256 <= 2^47 -> (fr + 256 <= data \/ data + 4 * (wpl * h) <= fr) ->
    0 < s1v -> s1v mod 16 = 0 -> s1v + 64 <= 2^47 -> data + 4 * (wpl * h) <= s1v ->
    rw_cells asegs m (fr + 32) [C4 (Z_to_bv 64 w)] -> rw_cells asegs m (fr + 48) [C4 (Z_to_bv 64 h)] ->
    rw_cells asegs m (fr + 64) [C4 (Z_to_bv 64 278)] -> rw_cells asegs m (fr + 128) [C4 (Z_to_bv 64 idx)] ->
    rw_cells asegs m (s1v + 16)
      [C8 (Z_to_bv 64 (fr + 64)); C8 c24; C8 c32; C8 (Z_to_bv 64 (fr + 48)); C8 (Z_to_bv 64 (fr + 128)); C8 (Z_to_bv 64 2)] ->
    mem_inv asegs m ->
    evt asegs
      (sel_exit sp gp tp (Z_to_bv 64 4) s0 (Z_to_bv 64 s1v) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 1) (Z_to_bv 64 2)
                s2 s3 (Z_to_bv 64 d) (Z_to_bv 64 data) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 399)
                (Z_to_bv 64 wpl) (Z_to_bv 64 84) (Z_to_bv 64 8) F fc m data (4 * (wpl * h)))
      (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 4) s0 (Z_to_bv 64 s1v) a0 a1 (Z_to_bv 64 35) (Z_to_bv 64 1) (Z_to_bv 64 3)
               (Z_to_bv 64 1) a6 (Z_to_bv 64 2) s2 s3 (Z_to_bv 64 d) (Z_to_bv 64 data) (Z_to_bv 64 (fr + 32))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 399) s9 s10 s11 (Z_to_bv 64 wpl) (Z_to_bv 64 84) (Z_to_bv 64 8) t6)
          F (Z_to_bv 64 SEL_HEAD) fc None m (seg_rom asegs)).
