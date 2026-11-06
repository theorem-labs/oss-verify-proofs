(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small R_m2s I_consts I_qck RT_iface D_defs D_kit D_libiface I_lift X_atexit L_hkit L_harn_defs.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_consts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_qck.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_atexit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma hz_wD_err : forall (usp spa Fr d n zb rc : Z)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  -9 <= rc < 0 -> 0 <= zb < 2^64 ->
  evt bsegs (fun ms =>
      ms = entry_st (Z_to_bv 64 0x81514) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 zb)
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) (Z_to_bv 64 zb) s8
             (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6 F fc e_free m)
    (MS (mkR (Z_to_bv 64 RA_B2BC) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 RA_B2BC)) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros RC ZB.
  unfold entry_st, e_free, RA_B2BC in *.
  replace (ret_pc (Z_to_bv 64 0x814a4)) with (Z_to_bv 64 0x814a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  lstep.
  assert (NZ : bv_unsigned (Z_to_bv 64 rc) <> 0).
  { replace (Z_to_bv 64 rc) with (Z_to_bv 64 (rc + 2^64)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity).
    rewrite unsigned_lit by lia. lia. }
  assert (BRF : bv_eqb (Z_to_bv 64 rc) z64 = false) by (unfold bv_eqb; apply Z.eqb_neq; change (bv_unsigned z64) with 0; exact NZ).
  rewrite BRF. cbv iota.
  lstep. lstep. lstep. lstep.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hz_wD : forall (usp spa Fr d n zb : Z) (j6 : list byte)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x62b000 <= Fr -> Fr + 64 < 2^47 -> 0 <= n < 2^26 -> 0 <= zb < 2^64 ->
  rw_cells bsegs m (Fr + 48) [CB 8 j6] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (j7 : list byte),
      ms = entry_st (Z_to_bv 64 0x814c8) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 (2 * n))
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 (Z_to_bv 64 (Fr + 48))
             (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6 F fc e_malloc m'
      /\ munch [(Fr + 48, Fr + 56)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (Fr + 48) [C4 (Z_to_bv 64 (2 * n)); CB 4 j7])
    (MS (mkR (Z_to_bv 64 RA_B2BC) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 RA_B2BC)) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FH N0 ZB NOUT MI.
  unfold entry_st, e_malloc, RA_B2BC in *.
  replace (ret_pc (Z_to_bv 64 0x814a4)) with (Z_to_bv 64 0x814a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (munch_refl [(Fr + 48, Fr + 56)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [4; 4]%nat) in NOUT; [| reflexivity]. cbn [mk_CB_cells app] in NOUT.
  lstep. if_true.
  lstep. lstep. lstep. lstep. lstep. lstep.
  assert (E2 : n ≪ 1 = 2 * n) by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite E2 in *.
  rewrite (Z.mod_small (2 * n) 18446744073709551616) by lia. rewrite (Z.mod_small (2 * n) 4294967296) by lia.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact NOUT.
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_small R_m2s I_consts I_qck RT_iface D_defs D_kit D_libiface I_lift X_atexit
  L_hkit L_harn_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma hz_wD_err : forall (usp spa Fr d n zb rc : Z)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  -9 <= rc < 0 -> 0 <= zb < 2^64 ->
  evt asegs (fun ms =>
      ms = entry_st (Z_to_bv 64 0x81ac8) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 zb)
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) (Z_to_bv 64 zb) s8
             (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6 F fc e_free m)
    (MS (mkR (Z_to_bv 64 RA_B2BC) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 RA_B2BC)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros RC ZB.
  unfold entry_st, e_free, RA_B2BC in *.
  replace (ret_pc (Z_to_bv 64 0x81a58)) with (Z_to_bv 64 0x81a58) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  lstep.
  assert (NZ : bv_unsigned (Z_to_bv 64 rc) <> 0).
  { replace (Z_to_bv 64 rc) with (Z_to_bv 64 (rc + 2^64)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity).
    rewrite unsigned_lit by lia. lia. }
  assert (BRF : bv_eqb (Z_to_bv 64 rc) z64 = false) by (unfold bv_eqb; apply Z.eqb_neq; change (bv_unsigned z64) with 0; exact NZ).
  rewrite BRF. cbv iota.
  lstep. lstep. lstep. lstep.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hz_wD : forall (usp spa Fr d n zb : Z) (j6 : list byte)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x61e000 <= Fr -> Fr + 64 < 2^47 -> 0 <= n < 2^26 -> 0 <= zb < 2^64 ->
  rw_cells asegs m (Fr + 48) [CB 8 j6] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem) (j7 : list byte),
      ms = entry_st (Z_to_bv 64 0x81a7c) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 (2 * n))
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 (Z_to_bv 64 (Fr + 48))
             (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6 F fc e_malloc m'
      /\ munch [(Fr + 48, Fr + 56)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (Fr + 48) [C4 (Z_to_bv 64 (2 * n)); CB 4 j7])
    (MS (mkR (Z_to_bv 64 RA_B2BC) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 RA_B2BC)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH N0 ZB NOUT MI.
  unfold entry_st, e_malloc, RA_B2BC in *.
  replace (ret_pc (Z_to_bv 64 0x81a58)) with (Z_to_bv 64 0x81a58) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (munch_refl [(Fr + 48, Fr + 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [4; 4]%nat) in NOUT; [| reflexivity]. cbn [mk_CB_cells app] in NOUT.
  lstep. if_true.
  lstep. lstep. lstep. lstep. lstep. lstep.
  assert (E2 : n ≪ 1 = 2 * n) by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite E2 in *.
  rewrite (Z.mod_small (2 * n) 18446744073709551616) by lia. rewrite (Z.mod_small (2 * n) 4294967296) by lia.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact NOUT.
Qed.
