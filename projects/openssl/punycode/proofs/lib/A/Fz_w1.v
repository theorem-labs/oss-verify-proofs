(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Layout Shadow R_small R_m2s I_consts RT_iface D_defs D_kit D_libiface X_atexit Fz_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma fz_wA0 : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 96 -> 0x7fff7f800000 <= lo -> usp < 2^63 -> usp mod 32 = 0 -> client_consts m -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (u0 u1 u2 a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 : word),
      ms = entry_st (Z_to_bv 64 0x1f314c) (Z_to_bv 64 (usp + -96)) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96))
             (Z_to_bv 64 192) a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 n) (Z_to_bv 64 d) s5 s6 s7 (Z_to_bv 64 SHB) s9 s10 s11 u3 u4 u5 u6
             F fc (e_stack_malloc 2) m1
      /\ munch [(usp - 96, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -96)
      /\ rw_cells asegs m1 (usp + -96) (fz_frame s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO LOS SPH S32 CC MI.
  destruct CC as (G1 & G2 & G3 & G4).
  unfold entry_st, e_fuzz, e_stack_malloc, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar,
    g_detect_stack_use_after_return, fz_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 96, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  carve_frame 96%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  lstep. do 13 lstep. lstep.
  lstep. rewrite (land_m32 (usp + -96)) by lia. replace (32 * ((usp + -96) / 32)) with (usp + -96) by (Z.div_mod_to_equations; lia).
  xsteps_to 0x1a671c%Z.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR].
Qed.

(* [comment removed for export] *)
Lemma fz_wA16 : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 112 -> 0x7fff7f800000 <= lo -> usp < 2^63 -> usp mod 32 = 16 -> client_consts m -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (u0 u1 u2 a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 : word) (jg0 jg1 : list byte),
      ms = entry_st (Z_to_bv 64 0x1f314c) (Z_to_bv 64 (usp + -112)) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -112))
             (Z_to_bv 64 192) a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 n) (Z_to_bv 64 d) s5 s6 s7 (Z_to_bv 64 SHB) s9 s10 s11 u3 u4 u5 u6
             F fc (e_stack_malloc 2) m1
      /\ munch [(usp - 112, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -112)
      /\ rw_cells asegs m1 (usp + -112) (CB 8 jg0 :: CB 8 jg1 :: fz_frame s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO LOS SPH S32 CC MI.
  destruct CC as (G1 & G2 & G3 & G4).
  unfold entry_st, e_fuzz, e_stack_malloc, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar,
    g_detect_stack_use_after_return, fz_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 112, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  carve_frame 112%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  lstep. do 13 lstep. lstep.
  lstep. rewrite (land_m32 (usp + -96)) by lia. replace (32 * ((usp + -96) / 32)) with (usp + -112) by (Z.div_mod_to_equations; lia).
  xsteps_to 0x1a671c%Z.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR].
Qed.
