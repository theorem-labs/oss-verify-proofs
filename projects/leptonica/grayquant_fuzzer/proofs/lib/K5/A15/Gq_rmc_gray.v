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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Ed_fpkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition gray_exit (ra sp gp tp s0 s1 a0 s2 s3 s5 s6 s7 s8 s9 s10 s11 t6 : word) (m : mem) (gm : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
             F' (Z_to_bv 64 0x9b188) (frm_clear fc') None m' (seg_rom asegs)
    /\ munch [(gm, gm + 1024)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

Lemma gray_loop : forall (k : nat) (i : Z)
    (ra sp gp tp t1 t2 s0 s1 a0 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (rmap gmap bmap gm n : Z) (rs gs bs ws : list word),
  Z.of_nat k = n - i -> 0 <= i -> (1 <= k)%nat -> n <= 256 ->
  u32arr asegs m rmap rs -> Z.of_nat (length rs) = n -> acc asegs m rmap (4 * n) ->
  0 < rmap -> rmap mod 8 = 0 -> rmap + 4 * n <= 2^47 -> (rmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= rmap) -> (rmap + 4 * n <= 0x10000 \/ SEGTOP_A <= rmap) ->
  u32arr asegs m gmap gs -> Z.of_nat (length gs) = n -> acc asegs m gmap (4 * n) ->
  0 < gmap -> gmap mod 8 = 0 -> gmap + 4 * n <= 2^47 -> (gmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= gmap) -> (gmap + 4 * n <= 0x10000 \/ SEGTOP_A <= gmap) ->
  u32arr asegs m bmap bs -> Z.of_nat (length bs) = n -> acc asegs m bmap (4 * n) ->
  0 < bmap -> bmap mod 8 = 0 -> bmap + 4 * n <= 2^47 -> (bmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= bmap) -> (bmap + 4 * n <= 0x10000 \/ SEGTOP_A <= bmap) ->
  u32arr asegs m gm ws -> Z.of_nat (length ws) = 256 -> acc asegs m gm 1024 ->
  0 < gm -> gm mod 8 = 0 -> gm + 1024 <= 2^47 -> (gm + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= gm) -> (gm + 1024 <= 0x10000 \/ SEGTOP_A <= gm) ->
  (gm + 1024 <= rmap \/ rmap + 4 * n <= gm) -> (gm + 1024 <= gmap \/ gmap + 4 * n <= gm) -> (gm + 1024 <= bmap \/ bmap + 4 * n <= gm) ->
  mem_inv asegs m ->
  evt asegs (gray_exit ra sp gp tp s0 s1 a0 (Z_to_bv 64 SHB) s3 s5 s6 s7 s8 s9 s10 s11 t6 m gm)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (gm + 4 * i)) t1 t2 s0 s1 a0
             (Z_to_bv 64 (rmap + 4 * i)) (Z_to_bv 64 (gmap + 4 * i)) (Z_to_bv 64 (bmap + 4 * i)) (Z_to_bv 64 (gm + 4 * i))
             (Z_to_bv 64 (rmap + 4 * i)) (Z_to_bv 64 (gmap + 4 * i)) (Z_to_bv 64 (bmap + 4 * i))
             (Z_to_bv 64 SHB) s3 (Z_to_bv 64 (n - i)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9b0a4) (frm_clear fc) None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp t1 t2 s0 s1 a0 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m rmap gmap bmap gm n rs gs bs ws
    HK HI HK1 HN
    UAR UARL ACCR R0 R8 RHI RSH RSEG UAG UAGL ACCG G0 G8 GHI GSH GSEG UAB UABL ACCB B0 B8 BHI BSH BSEG UAW UAWL ACCW W0 W8 WHI WSH WSEG
    SWR SWG SWB MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl [(gm, gm + 1024)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  lwalk [0x9b0c0; 0x9b188].
  destruct (u32arr_nth rs i ltac:(lia)) as (rv & NTHR).
  pose proof (u32arr_read asegs m rmap rs i rv _ UAR NTHR ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9b0d4; 0x9b188].
  destruct (u32arr_nth gs i ltac:(lia)) as (gv & NTHG).
  pose proof (u32arr_read asegs m gmap gs i gv _ UAG NTHG ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9b0e8; 0x9b188].
  destruct (u32arr_nth bs i ltac:(lia)) as (bv0 & NTHB).
  pose proof (u32arr_read asegs m bmap bs i bv0 _ UAB NTHB ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9b0f0; 0x9b188].
  lwalk [0x9b130; 0x9b188].        (* [comment removed for export] *)
  unpark WSH. unpark SWR. unpark SWG. unpark SWB.
  arr_sw gm i (gm + 4 * i).
  park WSH. park SWR. park SWG. park SWB.
  lwalk [0x9b0a4; 0x9b140; 0x9b188].
  destruct k as [|k].
  - assert (EI : n - i + -1 = 0) by lia. rewrite EI.
    brF. lwalk [0x9b188].
    apply evt_done. unfold gray_exit. do 15 eexists. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM| exact MI].
  - brT.
    replace (rmap + 4 * i + 4) with (rmap + 4 * (i + 1)) by lia.
    replace (gmap + 4 * i + 4) with (gmap + 4 * (i + 1)) by lia.
    replace (bmap + 4 * i + 4) with (bmap + 4 * (i + 1)) by lia.
    replace (gm + 4 * i + 4) with (gm + 4 * (i + 1)) by lia.
    replace (n - i + -1) with (n - (i + 1)) by lia.
    eapply evt_cut.
    + eapply (IH (i + 1)) with (n := n); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold gray_exit in PO |- *.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & F' & fc' & m' & E & MU' & WM' & MI').
      exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', F', fc', m'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact MI'].
Qed.
