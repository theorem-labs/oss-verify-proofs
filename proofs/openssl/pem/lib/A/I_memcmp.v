(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit I_pck D_kit I_ikit I_strncmpw Str_memcmp I_memcmpw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Theorem musl_memcmp_real : real_cmp_stmt 0x5264b0 0.
Proof.
  unfold real_cmp_stmt. intros until lo. intros -> -> -> PRE ST LO LOLO SPH MI.
  destruct PRE as (HL & NB & P1 & P2 & R1 & R2 & B1 & B2 & _).
  assert (EU1 : bv_unsigned (Z_to_bv 64 p1) = p1) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 p2) = p2) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 (Z.of_nat (length b1))) = Z.of_nat (length b1)) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { apply (memcmp_proof ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b1 b2 (mcmp_res b1 b2) MI).
    - rewrite EU1. exact B1.
    - rewrite EU2. exact B2.
    - rewrite EUn, Nat2Z.id. exact (mcmp_walk_res b1 b2 HL). }
  intros ms' (a1' & a2' & a3' & a4' & ->).
  unfold frame_post. do 15 eexists. split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI| exact ST].
Qed.

Notation IMEMCMP_DEPTH := 2320%Z (only parsing).     (* [comment removed for export] *)
Notation IBCMP_DEPTH := 4560%Z (only parsing).       (* [comment removed for export] *)

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Theorem imemcmp_spec : real_cmp_stmt 0x1aee08 IMEMCMP_DEPTH.
Proof using RIP.
  unfold real_cmp_stmt. intros until lo. intros -> -> -> PRE ST LO LOLO SPH MI.
  unfold kHighShadowEnd in *.
  set (n := Z.of_nat (length b1)) in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 2320, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  pose proof PRE as (HL & NB & P1 & P2 & R1 & R2 & _ & _ & S1 & S2 & _ & _ & _ & IC).
  assert (PRE0 : keep (cmp_pre m p1 p2 b1 b2 usp lo)) by exact PRE. clear PRE.
  pose proof IC as (G70 & G2 & RP & SHC & AI & F1 & F2).
  carve_frame 48%nat ST.
  do 8 lstep.
  lstep.
  call asan_inited_spec; [exact AI| assumption|].
  lstep. if_false.
  do 3 lstep.
  lstep.
  call try_init_spec; [exact AI| rewrite EU2; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2 in H; rename H into ST2 end.
  do 2 lstep. lstep. if_false.
  do 5 lstep. lstep.
  pose proof (mcc_spec RIP 0x5264b0 0 ltac:(split; [lia| reflexivity]) ltac:(lia) musl_memcmp_real) as MCC.
  change (2192 + Z.max 80 0) with 2272 in MCC. unfold mcc_stmt in MCC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (cmp_pre_munch m mm p1 p2 b1 b2 usp (usp + -48) lo _ _ PRE0 MU WM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold kHighShadowEnd; lia)) as PRE1 end.
  rewrite <- EU2 in PRE1.
  call MCC; [reflexivity| reflexivity| reflexivity| reflexivity| exact PRE1| rewrite EU2; exact ST2| rewrite EU2; lia| unfold kHighShadowEnd; lia| rewrite EU2; lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2 in H; rename H into ST3 end.
  do 5 lstep.
  release_frame FR ST3 usp.
  lstep.
  unfold frame_post. sys_finish.
  rewrite EU. exact ST3.
Qed.

(* [comment removed for export] *)
Theorem bcmp_stub_spec : real_cmp_stmt 0x5263dc IMEMCMP_DEPTH.
Proof using RIP.
  unfold real_cmp_stmt. intros until lo. intros -> -> -> PRE ST LO LOLO SPH MI.
  pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lstep.
  lstep.
  eapply imemcmp_spec; try reflexivity; eassumption.
Qed.

(* [comment removed for export] *)
Theorem ibcmp_spec : real_cmp_stmt 0x1aeec4 IBCMP_DEPTH.
Proof using RIP.
  unfold real_cmp_stmt. intros until lo. intros -> -> -> PRE ST LO LOLO SPH MI.
  unfold kHighShadowEnd in *.
  set (n := Z.of_nat (length b1)) in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 4560, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  pose proof PRE as (HL & NB & P1 & P2 & R1 & R2 & _ & _ & S1 & S2 & _ & _ & _ & IC).
  assert (PRE0 : keep (cmp_pre m p1 p2 b1 b2 usp lo)) by exact PRE. clear PRE.
  pose proof IC as (G70 & G2 & RP & SHC & AI & F1 & F2).
  carve_frame 48%nat ST.
  do 8 lstep.
  lstep.
  call asan_inited_spec; [exact AI| assumption|].
  lstep. if_false.
  do 3 lstep.
  lstep.
  call try_init_spec; [exact AI| rewrite EU2; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2 in H; rename H into ST2 end.
  do 2 lstep. lstep. if_false.
  do 5 lstep. lstep.
  pose proof (mcc_spec RIP 0x5263dc 2320 ltac:(split; [lia| reflexivity]) ltac:(lia) bcmp_stub_spec) as MCC.
  change (2192 + Z.max 80 2320) with 4512 in MCC. unfold mcc_stmt in MCC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (cmp_pre_munch m mm p1 p2 b1 b2 usp (usp + -48) lo _ _ PRE0 MU WM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold kHighShadowEnd; lia)) as PRE1 end.
  rewrite <- EU2 in PRE1.
  call MCC; [reflexivity| reflexivity| reflexivity| reflexivity| exact PRE1| rewrite EU2; exact ST2| rewrite EU2; lia| unfold kHighShadowEnd; lia| rewrite EU2; lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2 in H; rename H into ST3 end.
  do 5 lstep.
  release_frame FR ST3 usp.
  lstep.
  unfold frame_post. sys_finish.
  rewrite EU. exact ST3.
Qed.

End WithRIP.
