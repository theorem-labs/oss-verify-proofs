(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require SFModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_ibase R_small F_memset X_atexit X_gdefs X_unregi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac showpc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc" pc end.

Notation LLA := 0x6eed88%Z (only parsing).       (* [comment removed for export] *)

Lemma lla_this_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  mem_inv asegs m ->
  evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LLA) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1cf6d0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI.
  do 3 zstep. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lla_alloc16_spec : forall (SP : Z) ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo lend cur : Z),
  a0 = Z_to_bv 64 LLA -> a1 = Z_to_bv 64 16 ->
  stk asegs m lo SP -> lo <= SP - 32 -> SEGTOP_A <= lo -> SP < 2 ^ 63 ->
  ro_cells asegs m 0x5a7830 [C8 (Z_to_bv 64 8)] ->
  rw_cells asegs m LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 cur)] ->
  0 <= cur -> cur + 16 <= lend -> lend < 2 ^ 63 ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 cur) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(SP - 32, SP); (LLA + 8, LLA + 16)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo SP
      /\ rw_cells asegs m' LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 (cur + 16))])
    (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1cf6dc) fc None m (seg_rom asegs)).
Proof.
  intros until cur. intros -> -> ST LO LOLO SPH AL CELL C0 ROOM LE MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(SP - 32, SP); (0x6eed88 + 8, 0x6eed88 + 16)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 32%nat ST.
  xsteps_to 0x1cf724%Z.
  xstep.
  replace (negb (bv_lts (Z_to_bv 64 (lend - cur)) (Z_to_bv 64 16))) with true
    by (symmetry; unfold bv_lts; rewrite (SFModel.signed_of_Z (lend - cur)) by lia; change (bv_signed (Z_to_bv 64 16)) with 16; apply negb_true_iff, Z.ltb_ge; lia).
  cbv iota.
  xsteps_to 0x1cf7a0%Z.
  xstep.
  replace (bv_lts (Z_to_bv 64 (lend - cur)) (Z_to_bv 64 16)) with false
    by (symmetry; unfold bv_lts; rewrite (SFModel.signed_of_Z (lend - cur)) by lia; change (bv_signed (Z_to_bv 64 16)) with 16; apply Z.ltb_ge; lia).
  cbv iota.
  xsteps_to 0x1cf7c0%Z.
  replace (SP + -32 + 32) with SP by lia.
  release_frame FR ST SP.
  xstep.
  sys_finish.
Qed.
