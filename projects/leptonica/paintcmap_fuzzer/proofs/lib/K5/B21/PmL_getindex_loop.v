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
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition GIDX_HEAD : Z := 0x92938.
Definition GIDX_FOUND : Z := 0x92a5c.
Definition GIDX_NOTFOUND : Z := 0x92a4c.

(* [comment removed for export] *)
Definition gidx_st (pc : Z) (ra sp gp tp t0 s1 a0 a1 a2 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (arr : Z)
    (t1' t2' s0' a5' a6' t4' t6' : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra sp gp tp t0 t1' t2' s0' s1 a0 a1 a2 a3 a4 a5' a6' (Z_to_bv 64 SHB) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 arr) t4' (Z_to_bv 64 1) t6')
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Definition gidx_exit (ra sp gp tp t0 s1 a0 a1 a2 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (arr : Z) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists (i' : Z) (t2' s0' a5' a6' t4' t6' : word),
    (0 <= i' < n /\ ms' = gidx_st GIDX_FOUND ra sp gp tp t0 s1 a0 a1 a2 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 arr
                                 (Z_to_bv 64 i') t2' s0' a5' a6' t4' t6' F fc m)
    \/ ms' = gidx_st GIDX_NOTFOUND ra sp gp tp t0 s1 a0 a1 a2 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 arr
                     (Z_to_bv 64 i') t2' s0' a5' a6' t4' t6' F fc m.

Lemma gidx_loop : forall (k : nat) (i : Z)
    (ra sp gp tp t0 s0 s1 a0 a1 a2 a3 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) F fc (m : mem)
    (arr na n : Z) (bs : list byte),
  Z.of_nat k = n - i -> 0 <= i -> (1 <= k)%nat -> 4 * n <= na -> n <= 2^20 ->
  0 < arr -> arr mod 8 = 0 -> arr + na <= 2^47 -> (arr + na <= 0x7fff7000 \/ 0x10007fff8000 <= arr) ->
  bytes_at asegs m arr bs -> Z.of_nat (length bs) = na -> acc asegs m arr na -> mem_inv asegs m ->
  evt asegs (gidx_exit ra sp gp tp t0 s1 a0 a1 a2 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 arr F fc m n)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 i) (Z_to_bv 64 (n - i)) s0 s1 a0 a1 a2 a3 a4 (Z_to_bv 64 (arr + 4 * i)) a6 (Z_to_bv 64 SHB)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 arr) (Z_to_bv 64 (arr + 4 * i + 2)) (Z_to_bv 64 1) t6)
        F (Z_to_bv 64 GIDX_HEAD) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp t0 s0 s1 a0 a1 a2 a3 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m arr na n bs
    HK HI HK1 HN NB A0 A8 AHI ASH HB HBL ACC MI.
  { lia. }
  unfold GIDX_HEAD.
  (* [comment removed for export] *)
  assert (NEXT : forall (s0' a6' t6' : word),
    evt asegs (gidx_exit ra sp gp tp t0 s1 a0 a1 a2 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 arr F fc m n)
      (MS (mkR ra sp gp tp t0 (Z_to_bv 64 i) (Z_to_bv 64 (n - i)) s0' s1 a0 a1 a2 a3 a4 (Z_to_bv 64 (arr + 4 * i)) a6' (Z_to_bv 64 SHB)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 arr) (Z_to_bv 64 (arr + 4 * i + 2)) (Z_to_bv 64 1) t6')
          F (Z_to_bv 64 0x92924) fc None m (seg_rom asegs))).
  { intros. lwalk [0x92938; 0x92a4c].
    replace (arr + 4 * i + 4) with (arr + 4 * (i + 1)) by lia. replace (arr + 4 * i + 6) with (arr + 4 * (i + 1) + 2) by lia.
    replace (n - i + -1) with (n - (i + 1)) by lia.
    destruct k as [|k].
    - assert (EI : n - (i + 1) = 0) by lia. rewrite EI.
      brT. apply evt_done. unfold gidx_exit, gidx_st, GIDX_NOTFOUND. exists (i + 1). do 6 eexists. right. reflexivity.
    - brF. eapply (IH (i + 1)) with (bs := bs) (na := na); try eassumption; try lia. }
  lwalk (@nil Z).
  destruct (bytes_at_read1 m arr bs (4 * i + 2) HB ltac:(lia)) as (bR & RR).
  replace (arr + (4 * i + 2)) with (arr + 4 * i + 2) in RR by lia.
  lstep. clear RR. lwalk (@nil Z).
  if_cases Hc1; clear Hc1; [apply NEXT|].
  lwalk (@nil Z).
  destruct (bytes_at_read1 m arr bs (4 * i + 1) HB ltac:(lia)) as (bG & RG).
  replace (arr + (4 * i + 1)) with (arr + 4 * i + 2 + -1) in RG by lia.
  lstep. clear RG. lwalk (@nil Z).
  if_cases Hc2; clear Hc2; [apply NEXT|].
  lwalk (@nil Z).
  destruct (bytes_at_read1 m arr bs (4 * i) HB ltac:(lia)) as (bB & RB).
  replace (arr + 4 * i) with (arr + 4 * i + 2 + -2) in RB by lia.
  lstep. clear RB. lwalk (@nil Z).
  if_cases Hc3; clear Hc3; [apply NEXT|].
  lwalk [0x92a5c].
  apply evt_done. unfold gidx_exit, gidx_st, GIDX_FOUND. exists i. do 6 eexists. left. split; [lia| reflexivity].
Qed.
