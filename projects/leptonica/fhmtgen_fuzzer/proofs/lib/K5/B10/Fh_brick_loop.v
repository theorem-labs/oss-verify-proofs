(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition brick_cols_exit (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (r sx : Z) : machine_state -> Prop :=
  fun ms' => exists (a1' t3' t4' t5' t6' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0xaf4e8) fc None m' (seg_rom asegs)
    /\ munch [(r, r + 4 * sx)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' r ws' /\ Z.of_nat (length ws') = sx.

Lemma brick_cols : forall (k : nat) (j : Z)
    (ra sp gp tp t5 t6 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc (m : mem)
    (r sx : Z) (ws : list word),
  Z.of_nat k = sx - j -> 0 <= j -> (1 <= k)%nat -> 0 < sx <= 6 ->
  0 < r -> r mod 8 = 0 -> r + 4 * sx <= 2^47 -> (r + 4 * sx <= 0x7fff7000 \/ 0x10007fff8000 <= r) ->
  (r + 4 * sx <= 0x10000 \/ SEGTOP_A <= r) ->
  u32arr asegs m r ws -> Z.of_nat (length ws) = sx -> acc asegs m r (4 * sx) -> mem_inv asegs m ->
  evt asegs (brick_cols_exit ra sp gp tp (Z_to_bv 64 r) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 SHB) s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m r sx)
    (MS (mkR ra sp gp tp (Z_to_bv 64 r) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 SHB) s1 a0 (Z_to_bv 64 (r + 4 * j)) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (sx - j)) (Z_to_bv 64 (r + 4 * j)) t5 t6)
        F (Z_to_bv 64 0xaf540) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t5 t6 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m r sx ws
    HK HJ HK1 HSX R0 R8 RHI RSH RSEG UA UAL ACC MI.
  { lia. }
  unfold SEGTOP_A in *.
  pose proof (munch_refl [(r, r + 4 * sx)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xaf564].
  arr_sw r j (r + 4 * j).
  lwalk [0xaf540; 0xaf4e8].
  destruct k as [|k].
  - brF. lwalk [0xaf4e8].
    apply evt_done. unfold brick_cols_exit. do 5 eexists. exists m0, aws. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UA| exact UAL].
  - brT.
    replace (r + 4 * j + 4) with (r + 4 * (j + 1)) by lia. replace (sx - j + -1) with (sx - (j + 1)) by lia.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (ws := aws); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold brick_cols_exit in PO |- *.
      destruct PO as (t0' & t1' & t2' & a1' & a7' & m' & ws' & E & MU' & WM' & R).
      exists t0', t1', t2', a1', a7', m', ws'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.
