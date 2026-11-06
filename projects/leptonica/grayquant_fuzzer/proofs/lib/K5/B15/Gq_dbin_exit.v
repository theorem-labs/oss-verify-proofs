(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition dbin_exit_W (fr : Z) : list (Z * Z) := [(fr, fr + 8); (fr / 8 + SHB, fr / 8 + SHB + 32)].
(* [comment removed for export] *)
Definition dbin_sh_f5 : list cell := [C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11))].

(* [comment removed for export] *)
Definition dbin_exit_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (fr : Z) : machine_state -> Prop :=
  fun ms' => exists m' : mem,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (-11)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 fr) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (fr / 8 + SHB)) s10 (Z_to_bv 64 fr) t3 t4 t5 t6)
             F (Z_to_bv 64 0x9df68) fc None m' (seg_rom asegs)
    /\ munch (dbin_exit_W fr) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' fr [C8 (Z_to_bv 64 0x45e0360e)]
    /\ rw_cells asegs m' (fr / 8 + SHB) dbin_sh_f5.

(* [comment removed for export] *)
Lemma dbin_sh_recell32 : forall (m : mem) A shc, rw_cells asegs m A shc -> cells_size shc = 32%nat ->
  rw_cells asegs m A [CB 32 (cells_bytes shc)].
Proof.
  intros m A shc H S. pose proof H as [[W _] _].
  apply (rw_cells_recell m A shc); [exact H| cbn; split; [rewrite (cells_bytes_length shc W); exact S| exact I]| cbn; rewrite app_nil_r; reflexivity| cbn; rewrite S; reflexivity].
Qed.

Lemma dbin_exit_x1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 t3 t4 t5 t6 a1 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (fr : Z) (w0 : word) (shc : list cell),
  0 < fr -> fr mod 64 = 0 -> fr + 256 <= 2^47 ->
  rw_cells asegs m fr [C8 w0] -> rw_cells asegs m (fr / 8 + SHB) shc -> cells_size shc = 32%nat -> mem_inv asegs m ->
  evt asegs (dbin_exit_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 t3 t4 t5 t6 F fc m fr)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 fr) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (fr / 8 + SHB)) s10 (Z_to_bv 64 fr) t3 t4 t5 t6)
        F (Z_to_bv 64 0x9debc) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 t3 t4 t5 t6 a1 F fc m fr w0 shc FR0 FR64 FRHI FRM FSH0 SHL MI.
  pose proof (dbin_sh_recell32 m _ shc FSH0 SHL) as FSH. clear FSH0. set (sh := cells_bytes shc) in FSH. clearbody sh.
  unfold SHB in *.
  pose proof (munch_refl (dbin_exit_W fr) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold dbin_exit_W, SHB in MU.
  Time lwalk [0x9df68].
  apply evt_done. unfold dbin_exit_post. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
  unfold dbin_sh_f5. assumption.
Qed.
