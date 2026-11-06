(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit
  R_small R_m2s R_thread I_consts I_qck I_ikit F_atof_kit I_strchr_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma istrchr_c32 : istrchr_stmt 32 0 LITSEPS.
Proof. schr_intro. cwalk (@nil Z). schr_tail. Qed.
Lemma istrchr_c9 : istrchr_stmt 9 1 (LITSEPS + 1).
Proof. schr_intro. cwalk (@nil Z). schr_tail. Qed.
Lemma istrchr_c10 : istrchr_stmt 10 2 (LITSEPS + 2).
Proof. schr_intro. cwalk (@nil Z). schr_tail. Qed.
Lemma istrchr_c44 : istrchr_stmt 44 3 (LITSEPS + 3).
Proof. schr_intro. cwalk (@nil Z). schr_tail. Qed.

(* [comment removed for export] *)
Lemma istrchr_other : forall c, 1 <= c <= 255 -> c <> 32 -> c <> 9 -> c <> 10 -> c <> 44 -> istrchr_stmt c 4 0.
Proof.
  intros c C0 C32 C9 C10 C44. schr_intro.
  assert (LC : Z.land c 255 = c) by (apply land255; lia).
  cwalk (@nil Z). rewrite ?LC.       (* [comment removed for export] *)
  cwalk (@nil Z). rewrite ?LC. rewrite Z.lxor_0_l.
  replace (0 <? c) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [Z.b2z]. change ((1 + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l.
  cwalk (@nil Z). schr_tail.
Qed.

(* [comment removed for export] *)
Theorem istrchr_spec : forall (c : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo : Z),
  1 <= c <= 255 ->
  icells_schr m -> acc asegs m LITSEPS 5 -> qc_words m LITSEPS 5 ->
  mem_inv asegs m -> stk asegs m lo usp ->
  lo + ISTRCHR_DEPTH <= usp -> usp <= 2^47 -> usp mod 16 = 0 -> 0x10007fff8000 <= lo ->
  evt asegs (frame_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (schr_res c) [(usp - ISTRCHR_DEPTH, usp)] lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LITSEPS) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 F_STRCHR) fc None m (seg_rom asegs)).
Proof.
  intros c ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp lo
    C0 IC AC QW MI ST LO UHI SAL LOH.
  destruct (QW ltac:(lia)) as (w1 & _ & W1 & _).
  fold SEPS_SHW in W1.
  assert (SHB : forall i, 0 <= i < 5 -> exists b, bytes_at asegs m SEPS_SHB [b] /\ sh_ok b (LITSEPS + i)).
  { intros i Hi. destruct (AC i Hi) as (b & Hb & Ok). exists b. split; [| exact Ok].
    replace SEPS_SHB with (shad (LITSEPS + i)); [exact Hb|]. unfold SEPS_SHB, shad, SHB, LITSEPS. Z.div_mod_to_equations. lia. }
  unfold schr_res.
  destruct (Z.eqb_spec c 32) as [->|N32].
  { destruct (SHB 0 ltac:(lia)) as (b & SB & SOK).
    exact (istrchr_c32 ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp lo w1 b
             IC W1 SB SOK MI ST LO UHI SAL LOH). }
  destruct (Z.eqb_spec c 9) as [->|N9].
  { destruct (SHB 1 ltac:(lia)) as (b & SB & SOK).
    exact (istrchr_c9 ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp lo w1 b
             IC W1 SB SOK MI ST LO UHI SAL LOH). }
  destruct (Z.eqb_spec c 10) as [->|N10].
  { destruct (SHB 2 ltac:(lia)) as (b & SB & SOK).
    exact (istrchr_c10 ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp lo w1 b
             IC W1 SB SOK MI ST LO UHI SAL LOH). }
  destruct (Z.eqb_spec c 44) as [->|N44].
  { destruct (SHB 3 ltac:(lia)) as (b & SB & SOK).
    exact (istrchr_c44 ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp lo w1 b
             IC W1 SB SOK MI ST LO UHI SAL LOH). }
  destruct (SHB 4 ltac:(lia)) as (b & SB & SOK).
  exact (istrchr_other c C0 N32 N9 N10 N44 ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp lo w1 b
           IC W1 SB SOK MI ST LO UHI SAL LOH).
Qed.
