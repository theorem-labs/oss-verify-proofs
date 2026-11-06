(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Exec MState Frame Mem Cells Step.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanSortModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module HSS.
#[local] Notation W z := (Z_to_bv 64 z) (only parsing).

Section Stmt.
Variable segs : list Segment.
Variable entry : Z.

(* [comment removed for export] *)
Definition rec_at (m : word -> option byte) (tab : Z) (es : list HSM.rec) (j : Z) : Prop :=
  Step.rw_cells segs m (tab + 16 * j) [Cells.C8 (W (fst (HSM.get es j))); Cells.C8 (W (snd (HSM.get es j)))].

Definition walk_stmt : Prop :=
  forall (tab n : Z) (es : list HSM.rec) (RA : Z)
    (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  Z.of_nat (length es) = n -> 2 <= n <= 2 ^ 16 ->
  Forall (fun e => 0 <= fst e < 2 ^ 64 /\ 0 <= snd e < 2 ^ 64) es ->
  (forall j, 0 <= j < n -> rec_at m tab es j) ->
  0 < tab -> tab + 16 * n <= 2 ^ 47 -> tab mod 8 = 0 ->
  0 <= RA < 2 ^ 47 -> RA mod 2 = 0 ->
  Mem.mem_inv segs m ->
  Exec.evt segs (fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' : word) (m' : word -> option byte),
      ms' = MState.MS (Frame.mkR (W RA) sp gp tp t0' t1' t2' s0 s1 (W tab) a1' a2' a3' a4' a5' a6' a7'
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                      F (W RA) fc None m' (seg_rom segs)
      /\ Frame.munch [(tab, tab + 16 * n)] m m' /\ Frame.wmono segs m m' /\ Mem.mem_inv segs m'
      /\ (forall j, 0 <= j < n -> rec_at m' tab (HSM.hsort es) j))
    (MState.MS (Frame.mkR (W RA) sp gp tp t0 t1 t2 s0 s1 (W tab) (W n) a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (W entry) fc None m (seg_rom segs)).
End Stmt.
End HSS.
