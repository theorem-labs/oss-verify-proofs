(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx X_atexit D_trpro.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Import ListNotations.
Open Scope Z_scope.

Lemma wr_at_app' : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app' : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app' by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma rw_cells_addr : forall segs m A A' cs, rw_cells segs m A cs -> A = A' -> rw_cells segs m A' cs.
Proof. intros segs m A A' cs H <-. exact H. Qed.
Lemma stk_addr : forall segs m lo hi hi', stk segs m lo hi -> hi = hi' -> stk segs m lo hi'.
Proof. intros segs m lo hi hi' H <-. exact H. Qed.

(* [comment removed for export] *)
Lemma tr_copy_walk : forall (sp owned : Z) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  0 < owned < 2^64 -> mem_inv asegs m ->
  evt asegs (eq (entry_st (Z_to_bv 64 0x8c124) (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1
                          (Z_to_bv 64 owned) s1 s0 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6 F fc e_memcpy m))
    (MS (mkR (Z_to_bv 64 0x8c110) (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 owned)
             a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c110) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros Ho MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EO : bv_unsigned (Z_to_bv 64 owned) = owned) by (apply unsigned_lit; lia).
  step. if_false. do 4 step.
  apply evt_done. unfold entry_st. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tr_copy_ret_walk : forall (sp owned : Z) (gp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte) (fl : byte),
  rw_cells asegs m TR_INIT [C1 fl] -> mem_inv asegs m ->
  evt asegs (fun ms' => exists m' : word -> option byte,
                 ms' = entry_st (Z_to_bv 64 0x8c178) (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 (Z_to_bv 64 owned)
                          (Z_to_bv 64 owned) s0 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_BASE) s5 (Z_to_bv 64 0) (Z_to_bv 64 (-2))
                          s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fuzz m'
       /\ munch [(TR_INIT, TR_INIT + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' TR_INIT [C1 (Z_to_bv 8 1)])
    (MS (mkR (Z_to_bv 64 0x8c124) (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 v
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_BASE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c124)
        fc None m (seg_rom asegs)).
Proof.
  intros until fl. intros FL MI.
  pose proof (munch_refl [(TR_INIT, TR_INIT + 1)] m) as MU. unfold TR_INIT in MU. pose proof (wmono_refl asegs m) as WM.
  unfold TR_INIT in FL. unfold TR_BASE.
  do 9 lstep.
  apply evt_done. eexists. split; [unfold entry_st; cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma tr_fuzz_ret_walk : forall (sp : Z) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte) (lo : Z) (fl : byte),
  stk asegs m lo sp -> SEGTOP_A <= lo -> lo + 0x1000 <= sp -> sp mod 16 = 0 -> sp < 2^47 ->
  rw_cells asegs m TR_INIT [C1 fl] -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : word -> option byte) junk,
                 ms' = entry_st (Z_to_bv 64 0x8c270) (Z_to_bv 64 (sp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1
                          (Z_to_bv 64 FMT_emit) (Z_to_bv 64 (sp - 80 + 24)) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) (Z_to_bv 64 TR_BASE) s5 s6 s7
                          s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vprintf m'
       /\ munch [(sp - 80, sp); (TR_INIT, TR_INIT + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (sp - 80) [C8 (Z_to_bv 64 (sp - 80 + 24)); C8 (Z_to_bv 64 0x8c188); CB 8 junk]
       /\ rw_cells asegs m' (sp - 80 + 24) [C8 (Z_to_bv 64 0)]
       /\ rw_cells asegs m' (sp - 80 + 32) [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]
       /\ stk asegs m' lo (sp - 80)
       /\ rw_cells asegs m' TR_INIT [C1 (Z_to_bv 8 0)])
    (MS (mkR (Z_to_bv 64 0x8c178) (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 0)
             a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 TR_BASE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c178) fc None m (seg_rom asegs)).
Proof.
  intros until fl. intros ST SL LO U16 UT FL MI.
  pose proof ST as (STa & STb & _). unfold SEGTOP_A in SL.
  pose proof (munch_refl [(sp - 80, sp); (TR_INIT, TR_INIT + 1)] m) as MU. unfold TR_INIT in MU. pose proof (wmono_refl asegs m) as WM.
  unfold TR_INIT in FL. unfold TR_BASE.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  do 4 lstep.
  carve_frame 80%nat ST.
  do 15 lstep.
  apply evt_done. do 2 eexists. split.
  { unfold entry_st, FMT_emit. replace (sp - 80 + 24) with (sp + -56) by lia. replace (sp - 80) with (sp + -80) by lia. cbv delta [mkR]. reflexivity. }
  replace (sp - 80) with (sp + -80) by lia.
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  change [C8 (Z_to_bv 64 (sp + -56)); C8 (Z_to_bv 64 0x8c188); CB 8 (firstn 8 (firstn 40 (skipn 16 junk))); C8 (Z_to_bv 64 0);
          C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]
    with ([C8 (Z_to_bv 64 (sp + -56)); C8 (Z_to_bv 64 0x8c188); CB 8 (firstn 8 (firstn 40 (skipn 16 junk)))]
          ++ [C8 (Z_to_bv 64 0)] ++ [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]) in FR.
  apply rw_cells_app' in FR. destruct FR as [FR1 FR2]. apply rw_cells_app' in FR2. destruct FR2 as [FR2 FR3].
  cbn [cells_size csize Nat.add] in FR2, FR3.
  replace (sp + -80 + Z.of_nat 24 + Z.of_nat 8) with (sp + -80 + 32) in FR3 by lia.
  replace (sp + -80 + Z.of_nat 24) with (sp + -80 + 24) in FR2 by lia.
  split; [eapply rw_cells_addr; [| reflexivity]; replace (sp + -80 + 24) with (sp + -56) by lia; exact FR1|].
  split; [eapply rw_cells_addr; [exact FR2| lia]|]. split; [eapply rw_cells_addr; [exact FR3| lia]|]. split; [exact ST| assumption].
Qed.


Lemma tr_emit_ret_walk : forall (sp k : Z) (gp t0 t1 t2 s0 s1 v a1 a2' a3' a4' a5' a6' a7' s2 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (a2 a3 a4 a5 a6 a7 : word) F fc (m : word -> option byte) (lo : Z) junk,
  stk asegs m lo (sp - 80) -> SEGTOP_A <= lo -> lo + 0x1000 <= sp -> sp mod 16 = 0 -> sp < 2^47 -> 1 <= k <= 4 ->
  rw_cells asegs m (sp - 80) [C8 (Z_to_bv 64 (sp - 80 + 24)); C8 (Z_to_bv 64 0x8c188); CB 8 junk] ->
  rw_cells asegs m (sp - 80 + 24) [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (sp - 80 + 32) [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
  rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : word -> option byte) (s3' : word),
                 ((1 < k /\ ms' = entry_st (Z_to_bv 64 0x8c178) (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1
                          s1 s0 a2' a3' a4' a5' a6' a7' s2 s3' (Z_to_bv 64 TR_BASE) (Z_to_bv 64 (k - 1)) (Z_to_bv 64 0) (Z_to_bv 64 (-2))
                          s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fuzz m'
                   /\ rw_cells asegs m' TR_INIT [C1 (Z_to_bv 8 1)])
                   \/ (k = 1 /\ ms' = entry_st (Z_to_bv 64 0x8c1a4) (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1
                          s2 a1 a2' a3' a4' a5' a6' a7' s2 s3' (Z_to_bv 64 TR_BASE) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-2))
                          s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m'
                   /\ rw_cells asegs m' TR_INIT [C1 (Z_to_bv 8 0)]))
                 /\ munch [(TR_INIT, TR_INIT + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo sp)
    (MS (mkR (Z_to_bv 64 0x8c270) (Z_to_bv 64 (sp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 v
             a1 a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 0) (Z_to_bv 64 TR_BASE) (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2))
             s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c270) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST SL LO U16 UT Hk FR1 FR2 FR3 FL MI.
  pose proof ST as (STa & STb & _). unfold SEGTOP_A in SL.
  pose proof (munch_refl [(TR_INIT, TR_INIT + 1)] m) as MU. unfold TR_INIT in MU. pose proof (wmono_refl asegs m) as WM.
  unfold TR_INIT in FL. unfold TR_BASE.
  assert (EU : bv_unsigned (Z_to_bv 64 (sp - 80)) = sp - 80) by (apply unsigned_lit; lia).
  assert (FR : rw_cells asegs m (sp - 80) ([C8 (Z_to_bv 64 (sp - 80 + 24)); C8 (Z_to_bv 64 0x8c188); CB 8 junk] ++ [C8 (Z_to_bv 64 0)]
                                            ++ [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7])).
  { apply rw_cells_app'. split; [exact FR1|]. apply rw_cells_app'.
    pose proof (rw_cells_bound asegs m _ _ FR1) as B1. cbn [cells_size csize Nat.add] in B1.
    split; [eapply rw_cells_addr; [exact FR2| cbn; lia]| eapply rw_cells_addr; [exact FR3| cbn; lia]]. }
  clear FR1 FR2 FR3. cbn [app] in FR.
  pose proof (stk_release asegs m lo (sp - 80) _ ST FR ltac:(lia)) as ST'. cbn [cells_size csize Nat.add] in ST'.
  replace (sp - 80 + Z.of_nat 80) with sp in ST' by lia. clear ST.
  lstep. lstep. lstep. replace (sp - 80 + 80) with sp by lia.
  lstep. lstep. if_true.
  assert (EK : bv_swrap 32 (k + -1) = k - 1).
  { apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. }
  lstep. rewrite EK.
  assert (EK1 : bv_unsigned (Z_to_bv 64 (k - 1)) = k - 1) by (apply unsigned_lit; lia).
  destruct (Z.eq_dec k 1) as [K1|K1].
  - lstep. if_false. do 2 lstep.
    apply evt_done. do 2 eexists. split; [right; split; [exact K1| split; [unfold entry_st; replace (k - 1) with 0 by lia; cbv delta [mkR]; reflexivity| exact FL]]|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST'].
  - lstep. if_true. do 5 lstep.
    apply evt_done. do 2 eexists. split; [left; split; [lia| split; [unfold entry_st; cbv delta [mkR]; reflexivity| eassumption]]|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
Qed.

Lemma tr_free_ret_walk : forall (sp : Z) (gp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (c0 c1 c2 c3 c4 c5 c6 c7 : word) F fc (m : word -> option byte) (lo : Z),
  stk asegs m lo (sp - 80) -> SEGTOP_A <= lo -> lo + 0x1000 <= sp -> sp mod 16 = 0 -> sp < 2^47 ->
  tr_frame m sp (Z_to_bv 64 0x8bf50) c0 c1 c2 c3 c4 c5 c6 c7 -> mem_inv asegs m ->
  evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x8bf50) (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 c0 c1 (Z_to_bv 64 0)
                                      a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x8bf50) fc None m (seg_rom asegs)
                       /\ stk asegs m lo sp)
    (MS (mkR (Z_to_bv 64 0x8c1a4) (Z_to_bv 64 (sp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 v
             a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c1a4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST SL LO U16 UT (junk & FR) MI.
  pose proof ST as (STa & STb & _). unfold SEGTOP_A in SL.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (sp - 80)) = sp - 80) by (apply unsigned_lit; lia).
  do 14 lstep.
  release_frame FR ST sp.
  apply evt_done. split; [| exact ST].
  replace (sp - 80 + 80) with sp by lia. cbv delta [mkR]. reflexivity.
Qed.
