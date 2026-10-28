(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs Atp_h_find.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Sj_hkitB Atp_h_defsA Atp_h_vkitA Atp_h_vkit2A Atp_h_findA Atp_h_pushA Atp_h_pushcA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition sf_saved (s3 s2 s1 s0 ra : word) : list cell := [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition sf_locals (j0 : list byte) (t1 t2 a1 a2 : cell) : list cell := [CB 8 j0; t1; t2; a1; a2].

Definition sl_st (usp V pos : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rax : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state :=
  MS (mkR rax (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 ATPA_SEP) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 pos) (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4a40) fc None m (seg_rom asegs).

Lemma sw1 : forall (usp V D L lo : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 80 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 <= V < 2^64 -> 0 <= D < 2^64 -> 0 <= L < 2^64 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (j0 j1 j2 j3 j4 : list byte),
      ms = entry_st (Z_to_bv 64 0xb4a0c) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 L) (Z_to_bv 64 V) (Z_to_bv 64 0) (Z_to_bv 64 24)
             a3 a4 a5 a6 a7 (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_asan_memset m1
      /\ munch [(usp - 80, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -80)
      /\ rw_cells asegs m1 (usp + -80) (sf_locals j0 (CB 8 j1) (CB 8 j2) (CB 8 j3) (CB 8 j4))
      /\ rw_cells asegs m1 (usp + -40) (sf_saved s3 s2 s1 s0 ra))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 D) (Z_to_bv 64 L) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc ATPA_SPLIT m).
Proof.
  intros until m. intros ST LO GLO SPH VV DD LL MI.
  unfold entry_st, ATPA_SPLIT, e_asan_memset, sf_locals, sf_saved in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 80, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 80%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3; c4] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  replace (usp + -80 + Z.of_nat 40) with (usp + -40) in FRs by lia.
  apply evt_done. do 6 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl| exact FRs].
Qed.

Lemma sw2 : forall (usp V D L lo : Z) (j0 j1 j2 j3 j4 : list byte) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo (usp + -80) -> lo <= usp - 80 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 <= D < 2^64 -> 0 <= L < 2^64 ->
  rw_cells asegs m (usp + -80) (sf_locals j0 (CB 8 j1) (CB 8 j2) (CB 8 j3) (CB 8 j4)) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0xb4a2c) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 L) (Z_to_bv 64 (usp + -56)) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 4)
             (Z_to_bv 64 0) a4 a5 a6 a7 (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ATPA_FIND m1
      /\ munch [(usp - 80, usp - 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -80)
      /\ rw_cells asegs m1 (usp + -80) (sf_locals j0 (CB 8 j1) (CB 8 j2) (C8 (Z_to_bv 64 D)) (C8 (Z_to_bv 64 L))))
    (MS (mkR (Z_to_bv 64 0xb4a0c) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 L) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4a0c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH DD LL FRl MI.
  unfold entry_st, ATPA_FIND, ATPA_SEP, sf_locals in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 80, usp - 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FRl].
Qed.

Lemma sw3_none : forall (usp V : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1x s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= V < 2^64 -> 0 <= usp - 80 -> usp < 2^63 ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb4aac) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 V) s1x (Z_to_bv 64 V) (Z_to_bv 64 (usp + -56))
                 a2 a3 a4 a5 a6 a7 s2x (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ATPA_PUSHC m))
    (MS (mkR (Z_to_bv 64 0xb4a2c) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 V) s1x (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
             s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4a2c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros VV U0 UH. unfold entry_st, ATPA_PUSHC.
  zstep. zstep. if_true. zstep. zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma sw3_some : forall (usp V pos : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1x s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= pos < 2^63 ->
  evt asegs (eq (sl_st usp V pos gp tp t0 t1 t2 (Z_to_bv 64 0x23a38) a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 0xb4a2c) F fc m))
    (MS (mkR (Z_to_bv 64 0xb4a2c) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 V) s1x (Z_to_bv 64 pos) a1 a2 a3 a4 a5 a6 a7
             s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4a2c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros POS. unfold sl_st, ATPA_SEP.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K]. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma sw_body : forall (usp V Do Lo pos : Z) (j0 : list byte) (c1 c2 : cell)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rax : word) F fc (m : mem),
  0 <= usp - 80 -> usp < 2^63 -> 0 <= Do -> Do + Lo < 2^63 -> 0 <= pos <= Lo -> csize c1 = 8%nat -> csize c2 = 8%nat ->
  rw_cells asegs m (usp + -80) (sf_locals j0 c1 c2 (C8 (Z_to_bv 64 Do)) (C8 (Z_to_bv 64 Lo))) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0xb4a64) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 V) (Z_to_bv 64 (usp + -72))
             a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pos) (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ATPA_PUSHR m1
      /\ munch [(usp - 72, usp - 56)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (usp + -80) (sf_locals j0 (C8 (Z_to_bv 64 Do)) (C8 (Z_to_bv 64 pos)) (C8 (Z_to_bv 64 Do)) (C8 (Z_to_bv 64 Lo))))
    (sl_st usp V pos gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rax F fc m).
Proof.
  intros until m. intros U0 UH D0 DL POS C1 C2 FRl MI.
  unfold sl_st, entry_st, ATPA_PUSHR, ATPA_SEP, sf_locals in *.
  pose proof (munch_refl [(usp - 72, usp - 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct c1; cbn in C1; try discriminate; subst. all: destruct c2; cbn in C2; try discriminate; subst.
  all: zstep; zstep.
  all: if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  all: zstep; zstep; zstep; zstep; zstep; zstep; zstep.
  all: apply evt_done; eexists; split; [cbv delta [mkR]; reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [eassumption| eassumption].
Qed.

Lemma sw_adv : forall (usp V Do Lo pos lo : Z) (j0 : list byte)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo (usp + -80) -> lo <= usp - 80 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 <= Do -> Do + Lo < 2^63 -> 0 <= pos -> pos + 4 <= Lo ->
  rw_cells asegs m (usp + -80) (sf_locals j0 (C8 (Z_to_bv 64 Do)) (C8 (Z_to_bv 64 pos)) (C8 (Z_to_bv 64 Do)) (C8 (Z_to_bv 64 Lo))) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0xb4a98) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 (usp + -56)) (Z_to_bv 64 ATPA_SEP)
             (Z_to_bv 64 4) (Z_to_bv 64 0) a4 a5 a6 a7 (Z_to_bv 64 (pos + 4)) (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ATPA_FIND m1
      /\ munch [(usp - 56, usp - 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -80)
      /\ rw_cells asegs m1 (usp + -80) (sf_locals j0 (C8 (Z_to_bv 64 Do)) (C8 (Z_to_bv 64 pos)) (C8 (Z_to_bv 64 (Do + (pos + 4)))) (C8 (Z_to_bv 64 (Lo - (pos + 4))))))
    (MS (mkR (Z_to_bv 64 0xb4a64) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 ATPA_SEP) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 pos) (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4a64) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH D0 DL P0 PL FRl MI.
  unfold entry_st, ATPA_FIND, ATPA_SEP, sf_locals in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 56, usp - 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; replace (Lo + - (pos + 4)) with (Lo - (pos + 4)) by lia; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| eassumption].
Qed.

Lemma sw_test_some : forall (usp V pos : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= pos < 2^63 ->
  evt asegs (eq (sl_st usp V pos gp tp t0 t1 t2 (Z_to_bv 64 pos) a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 0xb4a98) F fc m))
    (MS (mkR (Z_to_bv 64 0xb4a98) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 pos) a1 a2 a3 a4 a5 a6 a7
             s2x (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4a98) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros POS. unfold sl_st, ATPA_SEP.
  zstep. zstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma sw_test_none : forall (usp V : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= V < 2^64 -> 0 <= usp - 80 -> usp < 2^63 ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb4aac) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 V) (Z_to_bv 64 (usp + -56))
                 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ATPA_PUSHC m))
    (MS (mkR (Z_to_bv 64 0xb4a98) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
             s2x (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4a98) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros VV U0 UH. unfold entry_st, ATPA_PUSHC, ATPA_SEP.
  zstep. zstep. if_false. zstep. zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma sw_epi : forall (usp lo : Z) (loc : list cell) (gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s3c s2c s1c s0c rac : word) F fc (m : mem),
  stk asegs m lo (usp + -80) -> lo <= usp - 80 -> 0x6ca000 <= lo -> usp < 2^63 -> Z.of_nat (cells_size loc) = 40 ->
  rw_cells asegs m (usp + -80) loc -> rw_cells asegs m (usp + -40) (sf_saved s3c s2c s1c s0c rac) -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c a0 a1 a2 a3 a4 a5 a6 a7 s2c s3c s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (ret_pc rac) fc None m (seg_rom asegs) /\ stk asegs m lo usp)
    (MS (mkR (Z_to_bv 64 0xb4aac) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb4aac) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH LOC FRl FRs MI. unfold sf_saved in FRs. pose proof ST as (STa & STb & _).
  zstep. zstep. zstep. zstep. zstep. release_frame FRl ST (usp + -40). release_frame FRs ST usp. zstep. zstep.
  apply evt_done. split; [cbv delta [mkR]; reflexivity| exact ST].
Qed.

Lemma poffs_of_bound4 : forall o all, (4 * (length (poffs_of o all) - 1) <= length all)%nat.
Proof.
  intros o all. remember (length all) as n eqn:En. revert o all En.
  induction n as [n IHn] using (well_founded_induction Wf_nat.lt_wf); intros o all En.
  rewrite poffs_of_unfold. destruct (find_sep all) as [pos|] eqn:E; [| cbn; lia]. cbn [length].
  pose proof (find_sep_spec _ _ E) as HP.
  specialize (IHn (length (skipn (pos + 4) all)) ltac:(rewrite length_skipn; lia) (o + pos + 4)%nat (skipn (pos + 4) all) eq_refl).
  rewrite length_skipn in IHn. pose proof (poffs_of_nonnil (o + pos + 4) (skipn (pos + 4) all)) as NN.
  destruct (poffs_of (o + pos + 4) (skipn (pos + 4) all)) as [|e r]; [congruence|]. cbn [length] in *. lia.
Qed.

Lemma vcost_pushes_mono : forall a b, vcost_pushes a 0 0 <= vcost_pushes (a + b) 0 0.
Proof.
  intros a b. induction b as [|b IH]; [rewrite Nat.add_0_r; lia|].
  rewrite Nat.add_succ_r, vcost_pushes_snoc.
  pose proof (vcap_iter_inv (a + b) 0 0 ltac:(lia) ltac:(lia)) as VI.
  pose proof (vcost_push_nonneg (vcap_iter (a + b) 0 0) (0 + Z.of_nat (a + b)) ltac:(lia)). lia.
Qed.

Lemma map_pview_snoc : forall D done (o n : Z), 0 <= o -> 0 <= n ->
  map (pview D) done ++ [(D + o, n)] = map (pview D) (done ++ [(Z.to_nat o, Z.to_nat n)]).
Proof. intros D done o n Ho Hn. rewrite map_app. cbn [map]. f_equal. unfold pview. cbn [fst snd]. rewrite !Z2Nat.id by lia. reflexivity. Qed.

Section Split.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis FIND : find_cpsA RT.
Hypothesis PUSHR : push_cpsA RT ATPA_PUSHR.
Hypothesis PUSHC : push_cpsA RT ATPA_PUSHC.

Local Ltac ul := unfold ATPA_SPLIT_STACK, ATPA_PUSH_STACK, ATPA_FIND_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition sp_inv (Σ Σi : rts RT) (m0 m1 : mem) (usp lo V D : Z) (d : list Z) (done : list (nat * nat)) (Ai o : Z) (j0 : list byte) (c1 c2 : cell)
    (s3c s2c s1c s0c rac : word) : Prop :=
  ART RT Σi m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -80)
  /\ rw_cells asegs m1 (usp + -80) (sf_locals j0 c1 c2 (C8 (Z_to_bv 64 (D + o))) (C8 (Z_to_bv 64 (zlength d - o))))
  /\ csize c1 = 8%nat /\ csize c2 = 8%nat
  /\ rw_cells asegs m1 (usp + -40) (sf_saved s3c s2c s1c s0c rac)
  /\ bytes_at asegs m1 D (to_bytes d) /\ fobj RT Σi m1 V 24
  /\ vrepA m1 V Ai (vcap_iter (length done) 0 0) (Z.of_nat (length done)) (map (pview D) done)
  /\ vliveA (rt_live RT Σi) Ai (vcap_iter (length done) 0 0) (Z.of_nat (length done)) (rt_live RT Σ)
  /\ rt_frames RT Σi = rt_frames RT Σ /\ rt_sp0 RT Σi = rt_sp0 RT Σ
  /\ rt_credit RT Σ - vcost_pushes (length done) 0 0 <= rt_credit RT Σi
  /\ (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside [(V, V + 24)] (bv_unsigned a) -> m1 a = m0 a).

Definition sp_static (Σ : rts RT) (PMc : Model -> Prop) (usp lo V D pk nk : Z) (d : list Z) : Prop :=
  fdfs_only PMc /\ mat_stable PMc /\ Forall (fun c => 0 <= c < 256) d /\ 1 <= zlength d < 2^26 /\ 0 < D
  /\ In (pk, nk) (rt_live RT Σ) /\ pk <= D /\ D + zlength d <= pk + nk /\ (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n)
  /\ Z.of_nat (length (rt_live RT Σ)) + 4 <= LIVE_MAX /\ vcost_pushes (length (poffs d)) 0 0 <= rt_credit RT Σ
  /\ rt_sp0 RT Σ - STACK_WIN <= lo /\ lo + ATPA_SPLIT_STACK <= usp /\ usp + 16 <= USTACK_TOP /\ usp mod 16 = 0
  /\ 0 < V /\ V + 24 <= lo.

Lemma split_tail : forall (Σ Σi : rts RT) PMc (T : TSet) (usp lo V D pk nk : Z) (d : list Z) (m0 m1 : mem) (done : list (nat * nat)) (Ai o : Z) (j0 : list byte) (ca cb : cell)
    (gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s2x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s1x s3c s2c s1c s0c rac : word) F fc (c : config),
  sp_static Σ PMc usp lo V D pk nk d -> tp = Z_to_bv 64 0x6a7e68 ->
  sp_inv Σ Σi m0 m1 usp lo V D d done Ai o j0 ca cb s3c s2c s1c s0c rac ->
  0 <= o <= zlength d -> poffs d = done ++ [(Z.to_nat o, Z.to_nat (zlength d - o))] -> frm0 fc ->
  (forall c', split_postA RT Σ PMc rac (Z_to_bv 64 usp) gp tp s0c s1c s2c s3c s4 s5 s6 s7 s8 s9 s10 s11 lo V D d (rt_live RT Σ) m0 c' /\ cfrm0 c' -> realizes asegs c' T) ->
  ASTA RT Σi PMc (eq (entry_st (Z_to_bv 64 0xb4aac) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 V) s1x (Z_to_bv 64 V) (Z_to_bv 64 (usp + -56))
                        a2 a3 a4 a5 a6 a7 s2x (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ATPA_PUSHC m1)) c ->
  realizes asegs c T.
Proof using AF PUSHC.
  intros until c. intros (FDO & MST & LBYT & LL & D0 & INK & PK1 & PK2 & LPOS & LVB & CRB & LOW & LOR & SPT & SPA & V0 & VLO) ETP
    (ART1 & MI1 & ST1 & FRl1 & C1 & C2 & FRs1 & PB1 & FOBJ1 & VR1 & VL1 & FRS1 & SP1 & CR1 & PRES1) OR PRE FRM Hk Hc. subst tp.
  pose proof (af_sp0_range RT AF Σi m1 ART1) as SP0R. pose proof (af_sp0_win RT AF Σi m1 ART1) as SP0W.
  set (n := length done) in *. set (L := zlength d) in *. unfold zlength in L.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -80)) = usp + -80) by (apply unsigned_lit; ul).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; ul).
  assert (LP : length (poffs d) = S n) by (rewrite PRE, length_app; cbn; lia).
  assert (PB4' : (4 * (length (poffs d) - 1) <= length d)%nat).
  { destruct d as [|x d'] eqn:Ed; [subst L; cbn in *; lia|]. rewrite poffs_eq. apply poffs_of_bound4. }

  pose proof FRl1 as X1. unfold sf_locals in X1.
  lazymatch type of X1 with rw_cells _ _ _ [?e0; ?e1; ?e2; ?e3; ?e4] => change [e0; e1; e2; e3; e4] with ([e0; e1; e2] ++ [e3; e4]) in X1 end.
  apply Sj_stage1_kit.rw_cells_app in X1. destruct X1 as [_ X1]. cbn [cells_size csize Nat.add] in X1. rewrite C1, C2 in X1. cbn [Nat.add] in X1.
  replace (usp + -80 + Z.of_nat 24) with (usp + -56) in X1 by lia.
  pose proof VR1 as (ELS & SZC & CAPB & A0 & AH & SV & BLK).
  apply (PUSHC Σi PMc (Z_to_bv 64 0xb4aac) (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 V) s1x (Z_to_bv 64 V) (Z_to_bv 64 (usp + -56))
           a2 a3 a4 a5 a6 a7 s2x (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 V (usp + -56) Ai (vcap_iter n 0 0) (Z.of_nat n) (D + o) (L - o)
           (map (pview D) done) (rt_live RT Σ) lo FDO MST eq_refl eq_refl eq_refl VR1 VL1 LPOS ltac:(lia) X1 FOBJ1);
    [rewrite EU2; lia| ul| clear - SPA; Z.div_mod_to_equations; lia| exact LVB| | exact ART1| exact MI1| rewrite EU2; exact ST1| rewrite SP1; exact LOW| rewrite EU2; ul| rewrite EU2; ul
    | rewrite EU2; replace (usp + -80) with (usp + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact SPA| exact FRM
    | split; [exact Hc| apply (cfrm0_of_asta RT Σi PMc (eq _) c Hc); intros ms0 <-; exact FRM] |].
  { pose proof (vcost_pushes_mono (S n) (length (poffs d) - S n)) as VM. replace (S n + (length (poffs d) - S n))%nat with (length (poffs d)) in VM by lia.
    rewrite vcost_pushes_snoc, Z.add_0_l in VM. lia. }
  intros c2 ((Σ2 & A2 & Hc2 & VL2 & FRS2 & SP2 & CR2) & FC2).
  destruct (ASTA_unpack_f RT Σ2 _ _ c2 Hc2 FC2) as (ms2 & (r2 & m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & VR2) & FRM2 & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xb4aac) in Hc2' by lia.
  assert (AG12 : forall a : word, usp - 80 <= bv_unsigned a < usp -> m2 a = m1 a).
  { intros a Ha. apply PRES2; [left; ul|]. cbn [outside]. split; [ul| exact I]. }
  assert (FRl2 : rw_cells asegs m2 (usp + -80) (sf_locals j0 ca cb (C8 (Z_to_bv 64 (D + o))) (C8 (Z_to_bv 64 (L - o))))).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FRl1). intros a Ha. apply AG12. unfold sf_locals in Ha. cbn [cells_size csize Nat.add] in Ha. rewrite C1, C2 in Ha. cbn in Ha. lia. }
  assert (FRs2 : rw_cells asegs m2 (usp + -40) (sf_saved s3c s2c s1c s0c rac)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FRs1). intros a Ha. apply AG12. unfold sf_saved in Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
  pose proof (sw_epi usp lo (sf_locals j0 ca cb (C8 (Z_to_bv 64 (D + o))) (C8 (Z_to_bv 64 (L - o)))) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 V) s1x r2 b1 b2 b3 b4 b5 b6 b7 s2x (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                s3c s2c s1c s0c rac F2 fc2 m2 ST2 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(unfold sf_locals; cbn [cells_size csize Nat.add]; rewrite C1, C2; reflexivity) FRl2 FRs2 MI2) as W.
  lazymatch type of W with evt asegs _ ?X0 => assert (W' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W) end. clear W.
  apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ2 PMc _ _ MST W') Hc2'). clear W'. intros c3 Hc3.
  apply Hk. split; [| apply (cfrm0_of_asta RT Σ2 PMc _ c3 Hc3); intros ms0 [E _]; rewrite E; exact FRM2].
  exists Σ2, A2. rewrite !EU.
  assert (EV : vcap_after (vcap_iter n 0 0) (Z.of_nat n) = vcap_iter (length (poffs d)) 0 0) by (rewrite LP, vcap_iter_S, Z.add_0_l; reflexivity).
  assert (EN : Z.of_nat n + 1 = zlength (poffs d)) by (unfold zlength; rewrite LP; lia).
  split; [| split; [| split; [rewrite FRS2; exact FRS1| split; [rewrite SP2; exact SP1|]]]].
  - eapply ASTA_conseq; [exact Hc3|]. intros ms [-> ST3]. exists r2, m2. split; [unfold ret_st; do 16 eexists; reflexivity|].
    split; [split; [exact ART2| split; [exact MI2| exact ST3]]|].
    split.
    + intros a Ha Hout. rewrite (PRES2 a); [exact (PRES1 a Ha Hout)| apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| intros e He; rewrite FRS1; exact He| lia]| exact Hout].
    + rewrite <- EV, <- EN. rewrite PRE. rewrite <- (map_pview_snoc D done o (L - o)) by lia. exact VR2.
  - rewrite <- EV, <- EN. exact VL2.
  - rewrite LP, vcost_pushes_snoc, Z.add_0_l. lia.
Qed.

Lemma vrepA_agree_nw : forall (m m' : mem) V A cap size els,
  vrepA m V A cap size els -> agree_on (fun x => V <= x < V + 24 \/ A <= x < A + 16 * size) m m' -> vrepA m' V A cap size els.
Proof.
  intros m m' V A cap size els (E & R & C & A0 & AH & SV & BLK) AG. unfold vrepA.
  split; [exact E|]. split; [exact R|]. split; [exact C|]. split; [exact A0|]. split; [exact AH|]. split.
  - apply (rw_cells_agree_nw asegs m m' _ _ SV). eapply agree_sub; [exact AG|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
  - destruct BLK as [L|(C1 & A16 & AP & BE)]; [left; exact L| right]. split; [exact C1|]. split; [exact A16|]. split; [exact AP|].
    apply (rw_cells_agree_nw asegs m m' _ _ BE). eapply agree_sub; [exact AG|]. intros x Hx. rewrite velts_size in Hx. cbv beta. unfold zlength in E.
    rewrite length_map in E || idtac. lia.
Qed.

Lemma split_loop : forall (k : nat) (Σ Σi : rts RT) PMc (T : TSet) (usp lo V D pk nk : Z) (d : list Z) (m0 m1 : mem) (done : list (nat * nat)) (Ai o pos : Z)
    (j0 : list byte) (ca cb : cell)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rax s3c s2c s1c s0c rac : word) F fc (c : config),
  sp_static Σ PMc usp lo V D pk nk d -> tp = Z_to_bv 64 0x6a7e68 ->
  zlength d - o <= Z.of_nat k ->
  sp_inv Σ Σi m0 m1 usp lo V D d done Ai o j0 ca cb s3c s2c s1c s0c rac ->
  0 <= o -> find_sep (skipn (Z.to_nat o) d) = Some (Z.to_nat pos) -> 0 <= pos ->
  poffs d = done ++ poffs_of (Z.to_nat o) (skipn (Z.to_nat o) d) -> frm0 fc ->
  (forall c', split_postA RT Σ PMc rac (Z_to_bv 64 usp) gp tp s0c s1c s2c s3c s4 s5 s6 s7 s8 s9 s10 s11 lo V D d (rt_live RT Σ) m0 c' /\ cfrm0 c' -> realizes asegs c' T) ->
  ASTA RT Σi PMc (eq (sl_st usp V pos gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rax F fc m1)) c ->
  realizes asegs c T.
Proof using AF FIND PUSHR PUSHC.
  induction k as [|k IH]; intros Σ Σi PMc T usp lo V D pk nk d m0 m1 done Ai o pos j0 ca cb gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rax
    s3c s2c s1c s0c rac F fc c STAT ETP HK INV1 O0 FS P0 PRE FRM Hk Hc.
  { exfalso. pose proof (find_sep_spec _ _ FS) as X. rewrite length_skipn in X. unfold zlength in HK. lia. }
  pose proof STAT as (FDO & MST & LBYT & LL & D0 & INK & PK1 & PK2 & LPOS & LVB & CRB & LOW & LOR & SPT & SPA & V0 & VLO).
  destruct INV1 as (ART1 & MI1 & ST1 & FRl1 & C1 & C2 & FRs1 & PB1 & FOBJ1 & VR1 & VL1 & FRS1 & SP1 & CR1 & PRES1). subst tp.
  pose proof (af_sp0_range RT AF Σi m1 ART1) as SP0R. pose proof (af_sp0_win RT AF Σi m1 ART1) as SP0W.
  assert (INKi : In (pk, nk) (rt_live RT Σi)) by (rewrite VL1; apply in_or_app; right; exact INK).
  pose proof (af_live_range RT AF Σi m1 pk nk ART1 INKi) as (K0 & K1 & _).
  pose proof FOBJ1 as (V8 & _ & (f & kf & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σi m1 f kf ART1 INF) as (F0 & F1 & FSZ & _).
  pose proof (af_frames_range RT AF Σi m1 f kf ART1 INF) as (_ & _ & _ & FLV). pose proof (FLV pk nk INKi) as DJV.
  set (n := length done) in *. set (L := zlength d) in *. unfold zlength in L.
  pose proof (find_sep_spec _ _ FS) as PSB. rewrite length_skipn in PSB.
  assert (POS : o + pos + 4 <= L) by lia.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -80)) = usp + -80) by (apply unsigned_lit; ul).
  assert (LBL : length (to_bytes d) = length d) by apply to_bytes_length_a.

  assert (PRE' : poffs d = (done ++ [(Z.to_nat o, Z.to_nat pos)]) ++ poffs_of (Z.to_nat (o + pos + 4)) (skipn (Z.to_nat (o + pos + 4)) d)).
  { rewrite PRE, (poffs_of_unfold (Z.to_nat o)), FS, <- app_assoc. cbn [app]. f_equal. f_equal. f_equal; [lia|]. rewrite skipn_skipn. f_equal. lia. }
  assert (LPn : (S n < length (poffs d))%nat).
  { rewrite PRE', length_app, length_app. cbn [length]. pose proof (poffs_of_nonnil (Z.to_nat (o + pos + 4)) (skipn (Z.to_nat (o + pos + 4)) d)) as NN.
    destruct (poffs_of (Z.to_nat (o + pos + 4)) (skipn (Z.to_nat (o + pos + 4)) d)); [congruence| cbn; lia]. }
  assert (PB4' : (4 * (length (poffs d) - 1) <= length d)%nat).
  { destruct d as [|x d'] eqn:Ed; [subst L; cbn in *; lia|]. rewrite poffs_eq. apply poffs_of_bound4. }
  pose proof VR1 as (ELS & SZC & CAPB & A0 & AH & SV & BLK).

  pose proof (sw_body usp V (D + o) (L - o) pos j0 ca cb gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rax F fc m1
                ltac:(ul) ltac:(ul) ltac:(lia) ltac:(ul) ltac:(lia) C1 C2 FRl1 MI1) as W1.
  lazymatch type of W1 with evt asegs _ ?X0 => assert (W1' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W1) end. clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σi PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σi _ _ c1 Hc1) as (ms1 & (m1' & -> & MU1 & WM1 & MI1' & FRl1') & Hc1'). clear Hc1.
  assert (FPT : fp_client RT Σi lo [(usp - 72, usp - 56)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (LOWi : rt_sp0 RT Σi - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
  pose proof (art_fp_client RT AF Σi m1 m1' lo _ ART1 LOWi FPT MU1 WM1) as ART1'.
  pose proof (fobj_munch RT AF Σi m1 m1' lo _ V 24 ART1 LOWi FPT MU1 FOBJ1) as FOBJ1'.

  assert (BLKR : forall x, Ai <= x < Ai + 16 * Z.of_nat n -> x < lo).
  { intros x Hx. destruct BLK as [(CC & AZ)|(CC & _ & _ & _)].
    - pose proof (vcap_iter_inv n 0 0 ltac:(lia) ltac:(lia)). lia.
    - assert (INA : In (Ai, 16 * Z.of_nat n) (rt_live RT Σi)).
      { rewrite VL1. apply in_or_app. left. unfold vblockA. replace (vcap_iter n 0 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). apply ann_block_vis. }
      pose proof (af_live_range RT AF Σi m1 _ _ ART1 INA). lia. }
  assert (VR1' : vrepA m1' V Ai (vcap_iter n 0 0) (Z.of_nat n) (map (pview D) done)).
  { apply (vrepA_agree_nw m1 m1' _ _ _ _ _ VR1). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. split; [| exact I].
    destruct Hx as [Hx|Hx]; [ul| pose proof (BLKR x Hx); ul]. }
  pose proof FRl1' as X1. unfold sf_locals in X1.
  lazymatch type of X1 with rw_cells _ _ _ [?e0; ?e1; ?e2; ?e3; ?e4] => change [e0; e1; e2; e3; e4] with ([e0] ++ [e1; e2] ++ [e3; e4]) in X1 end.
  apply Sj_stage1_kit.rw_cells_app in X1. destruct X1 as [_ X1]. apply Sj_stage1_kit.rw_cells_app in X1. destruct X1 as [X1 _]. cbn [cells_size csize Nat.add] in X1.
  replace (usp + -80 + Z.of_nat 8) with (usp + -72) in X1 by lia.

  apply (PUSHR Σi PMc (Z_to_bv 64 0xb4a64) (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 V) (Z_to_bv 64 (usp + -72))
           a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pos) (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1' V (usp + -72) Ai (vcap_iter n 0 0) (Z.of_nat n) (D + o) pos
           (map (pview D) done) (rt_live RT Σ) lo FDO MST eq_refl eq_refl eq_refl VR1' VL1 LPOS ltac:(lia) X1 FOBJ1');
    [rewrite EU2; lia| ul| clear - SPA; Z.div_mod_to_equations; lia| exact LVB| | exact ART1'| exact MI1'| | rewrite SP1; exact LOW| rewrite EU2; ul| rewrite EU2; ul
    | rewrite EU2; replace (usp + -80) with (usp + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact SPA| exact FRM
    | split; [exact Hc1'| apply (cfrm0_of_asta RT Σi PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  { pose proof (vcost_pushes_mono (S n) (length (poffs d) - S n)) as VM. replace (S n + (length (poffs d) - S n))%nat with (length (poffs d)) in VM by lia.
    rewrite vcost_pushes_snoc, Z.add_0_l in VM. lia. }
  { rewrite EU2. apply (stk_agree asegs m1 m1' _ _ ST1); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. split; [ul| exact I]. }
  intros c2 ((Σ2 & A2 & Hc2 & VL2 & FRS2 & SP2 & CR2) & FC2).
  destruct (ASTA_unpack_f RT Σ2 _ _ c2 Hc2 FC2) as (ms2 & (r2 & m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & VR2) & FRM2 & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xb4a64) in Hc2' by lia.
  assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2, SP1; exact LOW).
  assert (AG2 : forall a : word, usp - 80 <= bv_unsigned a < usp -> m2 a = m1' a).
  { intros a Ha. apply PRES2; [left; ul|]. cbn [outside]. split; [ul| exact I]. }
  assert (FRl2 : rw_cells asegs m2 (usp + -80) (sf_locals j0 (C8 (Z_to_bv 64 (D + o))) (C8 (Z_to_bv 64 pos)) (C8 (Z_to_bv 64 (D + o))) (C8 (Z_to_bv 64 (L - o))))).
  { apply (rw_cells_agree_nw asegs m1' m2 _ _ FRl1'). intros a Ha. apply AG2. unfold sf_locals in Ha. cbn [cells_size csize Nat.add] in Ha. lia. }

  pose proof (sw_adv usp V (D + o) (L - o) pos lo j0 gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 r2 b1 b2 b3 b4 b5 b6 b7 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2
                ST2 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) ltac:(ul) P0 ltac:(lia) FRl2 MI2) as W2.
  lazymatch type of W2 with evt asegs _ ?X0 => assert (W2' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W2) end. clear W2.
  apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ2 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
  destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & ST3 & FRl3) & Hc3'). clear Hc3.
  set (o' := o + pos + 4) in *.
  replace (D + o + (pos + 4)) with (D + o') in FRl3 by lia. replace (L - o - (pos + 4)) with (L - o') in FRl3 by lia.
  assert (FPA : fp_client RT Σ2 lo [(usp - 56, usp - 40)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  pose proof (art_fp_client RT AF Σ2 m2 m3 lo _ ART2 LOW2 FPA MU3 WM3) as ART3.

  assert (INK2 : In (pk, nk) (rt_live RT Σ2)) by (rewrite VL2; apply in_or_app; right; exact INK).
  assert (PB3 : bytes_at asegs m3 D (to_bytes d)).
  { apply (bytes_at_agree asegs m1 m3 _ _ PB1). intros a Ha. rewrite LBL in Ha.
    rewrite (MU3 a); [| cbn [outside]; split; [ul| exact I]]. rewrite (PRES2 a); [| right; right; left; exists pk, nk; split; [exact INK| lia]| cbn [outside]; split; [lia| exact I]].
    apply MU1. cbn [outside]. split; [ul| exact I]. }
  pose proof FRl3 as X3. unfold sf_locals in X3.
  lazymatch type of X3 with rw_cells _ _ _ [?e0; ?e1; ?e2; ?e3; ?e4] => change [e0; e1; e2; e3; e4] with ([e0; e1; e2] ++ [e3; e4]) in X3 end.
  apply Sj_stage1_kit.rw_cells_app in X3. destruct X3 as [_ X3]. cbn [cells_size csize Nat.add] in X3. replace (usp + -80 + Z.of_nat 24) with (usp + -56) in X3 by lia.
  assert (PBo : bytes_at asegs m3 (D + o') (to_bytes (skipn (Z.to_nat o') d))).
  { unfold to_bytes. rewrite <- List.skipn_map. fold (to_bytes d). replace (D + o') with (D + Z.of_nat (Z.to_nat o')) by lia. apply bytes_at_skipn_a; [exact PB3| lia]. }
  assert (EL' : zlength (skipn (Z.to_nat o') d) = L - o') by (unfold zlength; rewrite length_skipn; lia). rewrite <- EL' in X3.
  apply (FIND Σ2 PMc (Z_to_bv 64 0xb4a98) (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 V) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 (usp + -56)) (Z_to_bv 64 ATPA_SEP)
           (Z_to_bv 64 4) (Z_to_bv 64 0) b4 b5 b6 b7 (Z_to_bv 64 (pos + 4)) (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 (usp + -56) (D + o')
           (skipn (Z.to_nat o') d) lo FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(rewrite EU2; lia) ltac:(ul) ltac:(clear - SPA; Z.div_mod_to_equations; lia) X3 PBo
           ltac:(apply Forall_skipn'; exact LBYT) ltac:(lia) ltac:(exists pk, nk; split; [exact INK2| rewrite EL'; lia]) ART3 MI3);
    [rewrite EU2; exact ST3| exact LOW2| rewrite EU2; ul| rewrite EU2; ul| rewrite EU2; replace (usp + -80) with (usp + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact SPA| exact FRM2
    | split; [exact Hc3'| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM2] |].
  intros c4 (Hc4 & FC4).
  destruct (ASTA_unpack_f RT Σ2 _ _ c4 Hc4 FC4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4) & FRM4 & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  cbn [ms_fcsr] in FRM4. rewrite EU2 in ST4, PRES4. rewrite (ret_pc_even 0xb4a98) in Hc4' by lia.
  assert (AG4 : forall a : word, usp - 80 <= bv_unsigned a < usp -> m4 a = m3 a) by (intros a Ha; apply PRES4; [left; ul| exact I]).
  assert (FRl4 : rw_cells asegs m4 (usp + -80) (sf_locals j0 (C8 (Z_to_bv 64 (D + o))) (C8 (Z_to_bv 64 pos)) (C8 (Z_to_bv 64 (D + o'))) (C8 (Z_to_bv 64 (L - o'))))).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ FRl3). intros a Ha. apply AG4. unfold sf_locals in Ha. cbn [cells_size csize Nat.add] in Ha. lia. }

  assert (INV4 : sp_inv Σ Σ2 m0 m4 usp lo V D d (done ++ [(Z.to_nat o, Z.to_nat pos)]) A2 o' j0 (C8 (Z_to_bv 64 (D + o))) (C8 (Z_to_bv 64 pos)) s3c s2c s1c s0c rac).
  { assert (AGS : agree_on (fun x => usp - 40 <= x < usp) m1 m4).
    { intros a Ha. cbv beta in Ha. rewrite (AG4 a) by lia. rewrite (MU3 a); [| cbn [outside]; split; [lia| exact I]]. rewrite (AG2 a) by lia. apply MU1. cbn [outside]. split; [lia| exact I]. }
    pose proof VR2 as (ELS2 & SZC2 & CAPB2 & A02 & AH2 & SV2 & BLK2).
    assert (INF2 : In (f, kf) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
    pose proof (af_frames_range RT AF Σ2 m2 f kf ART2 INF2) as (_ & _ & _ & FLV2).
    assert (BLK2R : forall x, A2 <= x < A2 + 16 * (Z.of_nat n + 1) -> x < lo /\ (forall sp', aclient (rt_live RT Σ2) (rt_frames RT Σ2) sp' x)).
    { intros x Hx. destruct BLK2 as [(CC & AZ)|(CC & _ & _ & _)]; [pose proof (vcap_after_ge (vcap_iter n 0 0) (Z.of_nat n) ltac:(lia)); lia|].
      assert (INA : In (A2, 16 * (Z.of_nat n + 1)) (rt_live RT Σ2)).
      { rewrite VL2. apply in_or_app. left. unfold vblockA. replace (vcap_after (vcap_iter n 0 0) (Z.of_nat n) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). apply ann_block_vis. }
      pose proof (af_live_range RT AF Σ2 m2 _ _ ART2 INA). split; [lia|]. intros sp'. right; right; left. exists A2, (16 * (Z.of_nat n + 1)). split; [exact INA| lia]. }
    unfold sp_inv. split; [exact ART4|]. split; [exact MI4|]. split; [exact ST4|]. split; [unfold L in FRl4; exact FRl4|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply (rw_cells_agree_nw asegs m1 m4 _ _ FRs1); eapply agree_sub; [exact AGS|]; intros x Hx; unfold sf_saved in Hx; cbn [cells_size csize Nat.add] in Hx; cbv beta; lia|].
    split; [apply (bytes_at_agree asegs m3 m4 _ _ PB3); intros a Ha; apply PRES4; [right; right; left; exists pk, nk; split; [exact INK2| rewrite LBL in Ha; lia]| exact I]|].
    split. { apply (fobj_pres RT AF Σ2 Σ2 (rt_live RT Σ2) (usp + -80) m3 m4 V 24 ART3); [| intros a Ha; apply PRES4; [exact Ha| exact I]| reflexivity].
             apply (fobj_munch RT AF Σ2 m2 m3 lo _ V 24 ART2 LOW2 FPA MU3).
             exact (fobj_pres_fpc RT AF Σi Σ2 _ _ lo _ m1' m2 V 24 ART1' FOBJ1' PRES2 FRS2 LOWi ltac:(constructor; [right; right; exists f, kf; cbn [fst snd]; split; [exact INF| lia]| constructor])). }
    split. { rewrite length_app. cbn [length]. replace (n + 1)%nat with (S n) by lia. rewrite vcap_iter_S, Z.add_0_l. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
             rewrite <- (map_pview_snoc D done o pos) by lia.
             apply (vrepA_agree_nw m2 m4 _ _ _ _ _ VR2). intros a Ha. cbv beta in Ha. destruct Ha as [Ha|Ha].
             - rewrite (PRES4 a); [| right; right; right; left; exists f, kf; split; [exact INF2| lia]| exact I]. apply MU3. cbn [outside]. split; [ul| exact I].
             - destruct (BLK2R _ Ha) as [XL XC]. rewrite (PRES4 a); [| apply XC| exact I]. apply MU3. cbn [outside]. split; [ul| exact I]. }
    split. { rewrite length_app. cbn [length]. replace (n + 1)%nat with (S n) by lia. rewrite vcap_iter_S, Z.add_0_l. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. exact VL2. }
    split; [rewrite FRS2; exact FRS1|]. split; [rewrite SP2; exact SP1|].
    split. { rewrite length_app. cbn [length]. replace (n + 1)%nat with (S n) by lia. rewrite vcost_pushes_snoc, Z.add_0_l. lia. }
    intros a Ha Hout.
    assert (HaI : aclient (rt_live RT Σi) (rt_frames RT Σi) usp (bv_unsigned a)).
    { rewrite VL1, FRS1. apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia]. }
    pose proof (aclient_split_c RT AF Σi m1 usp (bv_unsigned a) ART1 HaI) as SPL. rewrite SP1 in SPL.
    rewrite (PRES4 a); [| rewrite VL2, FRS2, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia]| exact I].
    rewrite (MU3 a); [| cbn [outside]; split; [ul| exact I]].
    rewrite (PRES2 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| intros e He; rewrite FRS1; exact He| lia]| exact Hout].
    rewrite (MU1 a); [| cbn [outside]; split; [ul| exact I]]. exact (PRES1 a Ha Hout). }
  clear AG4 FRl4 PB3 PBo X3 FRl3 AG2 FRl2 X1 VR1' FRl1' FRl1 PRES1 PRES2 MU1 MU3 WM1 WM3.

  destruct (find_sep (skipn (Z.to_nat o') d)) as [p2|] eqn:FS2.
  -
    pose proof (find_sep_spec _ _ FS2) as P2B. rewrite length_skipn in P2B.
    replace (find_resA (skipn (Z.to_nat o') d)) with (Z.of_nat p2) in Hc4' by (unfold find_resA; rewrite FS2; reflexivity).
    pose proof (sw_test_some usp V (Z.of_nat p2) gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 (pos + 4)) s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F4 fc4 m4 ltac:(lia)) as W4.
    lazymatch type of W4 with evt asegs _ ?X0 => assert (W4' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W4) end. clear W4.
    apply (cps_realizes asegs _ _ _ c4 (asta_evt_c RT AF Σ2 PMc _ _ MST W4') Hc4'). clear W4'. intros c5 Hc5.
    apply (IH Σ Σ2 PMc T usp lo V D pk nk d m0 m4 (done ++ [(Z.to_nat o, Z.to_nat pos)]) A2 o' (Z.of_nat p2) j0 (C8 (Z_to_bv 64 (D + o))) (C8 (Z_to_bv 64 pos))
             gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 (Z_to_bv 64 (Z.of_nat p2)) d1 d2 d3 d4 d5 d6 d7 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 (Z_to_bv 64 0xb4a98) s3c s2c s1c s0c rac F4 fc4 c5
             STAT eq_refl ltac:(subst L; unfold zlength in *; lia) INV4 ltac:(lia) ltac:(rewrite Nat2Z.id; exact FS2) ltac:(lia) PRE' FRM4 Hk Hc5).
  -
    replace (find_resA (skipn (Z.to_nat o') d)) with (-1) in Hc4' by (unfold find_resA; rewrite FS2; reflexivity).
    pose proof (sw_test_none usp V gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 (pos + 4)) s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F4 fc4 m4 ltac:(ul) ltac:(ul) ltac:(ul)) as W4.
    lazymatch type of W4 with evt asegs _ ?X0 => assert (W4' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W4) end. clear W4.
    apply (cps_realizes asegs _ _ _ c4 (asta_evt_c RT AF Σ2 PMc _ _ MST W4') Hc4'). clear W4'. intros c5 Hc5.
    assert (PRE'' : poffs d = (done ++ [(Z.to_nat o, Z.to_nat pos)]) ++ [(Z.to_nat o', Z.to_nat (zlength d - o'))]).
    { rewrite PRE', (poffs_of_unfold (Z.to_nat o')), FS2. f_equal. f_equal. f_equal. rewrite length_skipn. subst L. unfold zlength. lia. }
    exact (split_tail Σ Σ2 PMc T usp lo V D pk nk d m0 m4 (done ++ [(Z.to_nat o, Z.to_nat pos)]) A2 o' j0 (C8 (Z_to_bv 64 (D + o))) (C8 (Z_to_bv 64 pos))
             gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 (Z_to_bv 64 ATPA_SEP) s3c s2c s1c s0c rac F4 fc4 c5
             STAT eq_refl INV4 ltac:(subst L; unfold zlength in *; lia) PRE'' FRM4 Hk Hc5).
Qed.

Theorem split_ok : split_cpsA RT.
Proof using AF RTF FIND PUSHR PUSHC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V D d jv lo
    FDO MST -> -> -> -> DNE PB LBYT LL INLV LPOS FOBJ0 VJ LVB CRB ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP in Hk.
  destruct INLV as (pk & nk & INK & PK1 & PK2).
  pose proof (af_live_range RT AF Σ m pk nk ART0 INK) as (K0 & K1 & _).
  pose proof FOBJ0 as (V8 & _ & (f & kf & INF & FLO & FHI) & SHB0). change ((24 + 7) / 8) with 3 in FHI, SHB0.
  pose proof (fframe_ranges RT AF Σ m f kf ART0 INF) as (F0 & F1 & FSZ & _).
  pose proof (af_frames_range RT AF Σ m f kf ART0 INF) as (_ & _ & _ & FLV). pose proof (FLV pk nk INK) as DJV.
  set (L := zlength d) in *. unfold zlength in L.
  assert (L1 : 1 <= L) by (destruct d; [congruence| subst L; cbn; lia]).
  assert (LBL : length (to_bytes d) = length d) by apply to_bytes_length_a.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -80)) = usp + -80) by (apply unsigned_lit; ul).
  assert (STAT : sp_static Σ PMc usp lo V D pk nk d).
  { unfold sp_static. repeat match goal with |- _ /\ _ => split end; try assumption; try lia; subst L; unfold zlength; lia. }

  assert (FPC : fp_client RT Σ lo [(usp - 80, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  pose proof (sw1 usp V D L lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt asegs _ ?X0 => assert (W1' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W1) end. clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & j0 & j1 & j2 & j3 & j4 & -> & MU1 & WM1 & MI1 & ST1 & FRl1 & FRs1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ V 24 ART0 LOW FPC MU1 FOBJ0) as FOBJ1.
  assert (VJ1 : rw_cells asegs m1 V [CB 24 jv]).
  { apply (rw_cells_agree asegs m m1 _ _ VJ); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [ul| exact I]. }

  pose proof FOBJ1 as (_ & _ & _ & SHB1).
  apply ((rf_asan_memset RT RTF) Σ PMc (Z_to_bv 64 0xb4a0c) (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 L)
           (Z_to_bv 64 V) (Z_to_bv 64 0) (Z_to_bv 64 24) a3 a4 a5 a6 a7 (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 V 24 (Z_to_bv 8 0) lo FDO MST eq_refl eq_refl eq_refl ltac:(ul) ltac:(lia));
    [| exact ART1| exact MI1| | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  { unfold checked_dst. rewrite EU2. split; [| split; [| exact (rw_cells_wr_at asegs m1 V _ 24 VJ1 ltac:(cbn; lia))]].
    - intros _. split; [exact (acc_zero_run asegs m1 V 3 V8 ltac:(lia) SHB1)|]. right; left. exists f, kf. split; [exact INF| lia].
    - intros i Hi. right; right; right; left. exists f, kf. split; [exact INF| lia]. }
  { unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul|]. replace (usp + -80) with (usp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact SPA. }
  intros c2 (Hc2 & FC2).
  destruct (ASTA_unpack_f RT Σ _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2) & FRM2 & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xb4a0c) in Hc2' by lia.
  assert (CLV : forall sp' x, V <= x < V + 24 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) by (intros sp' x Hx; right; right; right; left; exists f, kf; split; [exact INF| lia]).
  assert (VR2 : vrepA m2 V 0 0 0 []).
  { unfold vrepA. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [| left; split; reflexivity].
    change (0 + 16 * 0) with 0. apply rw_cells_of_bytes; [cbn; repeat split; exact I| exact BY2|].
    cbn [cells_size csize Nat.add]. apply (wr_at_transport asegs m1 m2 V 24 (rw_cells_wr_at asegs m1 V _ 24 VJ1 ltac:(cbn; lia)) WM2). }
  assert (FRl2 : rw_cells asegs m2 (usp + -80) (sf_locals j0 (CB 8 j1) (CB 8 j2) (CB 8 j3) (CB 8 j4))).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FRl1). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2). intros x Hx. unfold sf_locals in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; lia| ul]. }

  pose proof (sw2 usp V D L lo j0 j1 j2 j3 j4 gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 V) b1 b2 b3 b4 b5 b6 b7 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2
                ST2 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) FRl2 MI2) as W2.
  lazymatch type of W2 with evt asegs _ ?X0 => assert (W2' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W2) end. clear W2.
  apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & ST3 & FRl3) & Hc3'). clear Hc3.
  assert (FPA : fp_client RT Σ lo [(usp - 80, usp - 40)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  pose proof (art_fp_client RT AF Σ m2 m3 lo _ ART2 LOW FPA MU3 WM3) as ART3.
  assert (PB3 : bytes_at asegs m3 D (to_bytes d)).
  { apply (bytes_at_agree asegs m m3 _ _ PB). intros a Ha. rewrite LBL in Ha.
    rewrite (MU3 a); [| cbn [outside]; split; [ul| exact I]]. rewrite (PRES2 a); [| right; right; left; exists pk, nk; split; [exact INK| lia]| lia].
    apply MU1. cbn [outside]. split; [ul| exact I]. }
  pose proof FRl3 as X3. unfold sf_locals in X3.
  lazymatch type of X3 with rw_cells _ _ _ [?e0; ?e1; ?e2; ?e3; ?e4] => change [e0; e1; e2; e3; e4] with ([e0; e1; e2] ++ [e3; e4]) in X3 end.
  apply Sj_stage1_kit.rw_cells_app in X3. destruct X3 as [_ X3]. cbn [cells_size csize Nat.add] in X3. replace (usp + -80 + Z.of_nat 24) with (usp + -56) in X3 by lia.
  unfold L in X3.
  apply (FIND Σ PMc (Z_to_bv 64 0xb4a2c) (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 V) (Z_to_bv 64 L) (Z_to_bv 64 (usp + -56)) (Z_to_bv 64 ATPA_SEP)
           (Z_to_bv 64 4) (Z_to_bv 64 0) b4 b5 b6 b7 (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 (usp + -56) D d lo
           FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(rewrite EU2; lia) ltac:(ul) ltac:(clear - SPA; Z.div_mod_to_equations; lia) X3 PB3 LBYT ltac:(subst L; unfold zlength in *; lia)
           ltac:(exists pk, nk; split; [exact INK| subst L; unfold zlength in *; lia]) ART3 MI3);
    [rewrite EU2; exact ST3| exact LOW| rewrite EU2; ul| rewrite EU2; ul| rewrite EU2; replace (usp + -80) with (usp + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact SPA| exact FRM2
    | split; [exact Hc3'| apply (cfrm0_of_asta RT Σ PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM2] |].
  intros c4 (Hc4 & FC4).
  destruct (ASTA_unpack_f RT Σ _ _ c4 Hc4 FC4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4) & FRM4 & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  cbn [ms_fcsr] in FRM4. rewrite EU2 in ST4, PRES4. rewrite (ret_pc_even 0xb4a2c) in Hc4' by lia.

  assert (INV4 : sp_inv Σ Σ m m4 usp lo V D d [] 0 0 j0 (CB 8 j1) (CB 8 j2) s3 s2 s1 s0 ra).
  { unfold sp_inv. cbn [length vcap_iter Z.of_nat map vcost_pushes]. rewrite Z.add_0_r, Z.sub_0_r, Z.sub_0_r.
    split; [exact ART4|]. split; [exact MI4|]. split; [exact ST4|].
    split; [apply (rw_cells_agree_nw asegs m3 m4 _ _ FRl3); intros a Ha; apply PRES4; [left; unfold sf_locals in Ha; cbn [cells_size csize Nat.add] in Ha; ul| exact I]|].
    split; [reflexivity|]. split; [reflexivity|].
    split. { apply (rw_cells_agree_nw asegs m1 m4 _ _ FRs1). intros a Ha. unfold sf_saved in Ha. cbn [cells_size csize Nat.add] in Ha.
             rewrite (PRES4 a); [| left; ul| exact I]. rewrite (MU3 a); [| cbn [outside]; split; [lia| exact I]]. apply PRES2; [left; ul| ul]. }
    split; [apply (bytes_at_agree asegs m3 m4 _ _ PB3); intros a Ha; apply PRES4; [right; right; left; exists pk, nk; split; [exact INK| rewrite LBL in Ha; lia]| exact I]|].
    split. { apply (fobj_pres RT AF Σ Σ (rt_live RT Σ) (usp + -80) m3 m4 V 24 ART3); [| intros a Ha; apply PRES4; [exact Ha| exact I]| reflexivity].
             apply (fobj_munch RT AF Σ m2 m3 lo _ V 24 ART2 LOW FPA MU3).
             apply (fobj_agree RT AF Σ Σ m1 m2 V 24 ART1 FOBJ1 eq_refl). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2). intros x Hx. cbv beta in Hx. change ((24 + 7) / 8) with 3 in Hx.
             pose proof (af_fshadow_apart RT AF Σ m1 f kf ART1 INF) as [_ XF]. destruct (XF f kf INF) as [E|E]; pose proof (fobj_shadow_range RT AF Σ m1 V 24 ART1 FOBJ1) as (f' & c' & IN' & S1 & S2 & _).
             - split; [right; right; right; right; exists f', c'; split; [exact IN'| change ((24 + 7) / 8) with 3 in S2; lia]|]. unfold shad in *. lia.
             - split; [right; right; right; right; exists f', c'; split; [exact IN'| change ((24 + 7) / 8) with 3 in S2; lia]|]. unfold shad in *. lia. }
    split. { apply (vrepA_agree_nw m2 m4 _ _ _ _ _ VR2). intros a Ha. cbv beta in Ha. destruct Ha as [Ha|Ha]; [| lia].
             rewrite (PRES4 a); [| apply CLV; lia| exact I]. apply MU3. cbn [outside]. split; [ul| exact I]. }
    split; [unfold vliveA, vblockA; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    intros a Ha Hout. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL. cbn [outside] in Hout. destruct Hout as [HO _].
    rewrite (PRES4 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); auto; lia| exact I]. rewrite (MU3 a); [| cbn [outside]; split; [ul| exact I]].
    rewrite (PRES2 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); auto; lia| lia]. apply MU1. cbn [outside]. split; [ul| exact I]. }
  clear PRES4 FRl3 X3 PB3 MU3 FRl2 PRES2 VR2 BY2 FRl1 FRs1 VJ1 MU1.
  assert (PEQ : poffs d = poffs_of 0 d) by (rewrite poffs_eq; destruct d; [congruence| reflexivity]).
  destruct (find_sep d) as [p0|] eqn:FS0.
  -
    pose proof (find_sep_spec _ _ FS0) as P0B.
    replace (find_resA d) with (Z.of_nat p0) in Hc4' by (unfold find_resA; rewrite FS0; reflexivity).
    pose proof (sw3_some usp V (Z.of_nat p0) gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 L) (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F4 fc4 m4 ltac:(lia)) as W4.
    lazymatch type of W4 with evt asegs _ ?X0 => assert (W4' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W4) end. clear W4.
    apply (cps_realizes asegs _ _ _ c4 (asta_evt_c RT AF Σ PMc _ _ MST W4') Hc4'). clear W4'. intros c5 Hc5.
    apply (split_loop (S (length d)) Σ Σ PMc T usp lo V D pk nk d m m4 [] 0 0 (Z.of_nat p0) j0 (CB 8 j1) (CB 8 j2)
             gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 (Z_to_bv 64 0x23a38) d1 d2 d3 d4 d5 d6 d7 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 (Z_to_bv 64 0xb4a2c) s3 s2 s1 s0 ra F4 fc4 c5
             STAT eq_refl ltac:(subst L; unfold zlength in *; lia) INV4 ltac:(lia) ltac:(cbn [Z.to_nat skipn]; rewrite Nat2Z.id; exact FS0) ltac:(lia) ltac:(cbn [Z.to_nat skipn app]; exact PEQ) FRM4 Hk Hc5).
  -
    replace (find_resA d) with (-1) in Hc4' by (unfold find_resA; rewrite FS0; reflexivity).
    pose proof (sw3_none usp V gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 L) (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F4 fc4 m4 ltac:(ul) ltac:(ul) ltac:(ul)) as W4.
    lazymatch type of W4 with evt asegs _ ?X0 => assert (W4' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W4) end. clear W4.
    apply (cps_realizes asegs _ _ _ c4 (asta_evt_c RT AF Σ PMc _ _ MST W4') Hc4'). clear W4'. intros c5 Hc5.
    assert (PRE : poffs d = [] ++ [(Z.to_nat 0, Z.to_nat (zlength d - 0))]).
    { rewrite PEQ, (poffs_of_unfold 0), FS0. cbn [app]. f_equal. f_equal. unfold zlength. lia. }
    exact (split_tail Σ Σ PMc T usp lo V D pk nk d m m4 [] 0 0 j0 (CB 8 j1) (CB 8 j2)
             gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 D) s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 (Z_to_bv 64 L) s3 s2 s1 s0 ra F4 fc4 c5
             STAT eq_refl INV4 ltac:(subst L; unfold zlength in *; lia) PRE FRM4 Hk Hc5).
Qed.
End Split.
