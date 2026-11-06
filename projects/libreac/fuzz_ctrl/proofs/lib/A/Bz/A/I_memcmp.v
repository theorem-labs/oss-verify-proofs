(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A Require Import Shadow IcptSpec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit I_musl I_memcmpw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Theorem musl_memcmp_real (MCMP : memcmp_stmt) : real_cmp_stmt 0x97bdc 0.
Proof.
  unfold real_cmp_stmt. intros until lo. intros -> -> -> PRE HB ST LO LOLO SPH MI.
  destruct PRE as (L1 & L2 & HM & N0 & P1 & P2 & R1 & R2 & B1 & B2 & _).
  assert (EU1 : bv_unsigned (Z_to_bv 64 p1) = p1) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 p2) = p2) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { apply (MCMP ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b1 b2 v).
    - rewrite EU1. exact B1.
    - rewrite EU2. exact B2.
    - rewrite EUn. exact HM.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI').
  unfold frame_post. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; intros; cbn [outside]; exact I|].
  split; [exact WM|]. split; [exact MI'|].
  apply (stk_agree asegs m m' _ _ ST); [| exact WM].
  apply (agree_of_munch _ _ _ _ MU). intros; cbn [outside]; exact I.
Qed.

Notation IMEMCMP_DEPTH := 2320%Z (only parsing).     (* [comment removed for export] *)
Notation IBCMP_DEPTH := 4560%Z (only parsing).       (* [comment removed for export] *)

Section WithRIP.
Hypothesis RIP : rip_stmt.
Hypothesis MCMP : memcmp_stmt.

(* [comment removed for export] *)
Theorem imemcmp_spec : real_cmp_stmt 0x43fc0 IMEMCMP_DEPTH.
Proof using RIP MCMP.
  unfold real_cmp_stmt. intros until lo. intros -> -> -> PRE HB ST LO LOLO SPH MI.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 2320, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  pose proof PRE as (L1 & L2 & HM & N0 & P1 & P2 & R1 & R2 & _ & _ & S1 & S2 & _ & _ & _ & IC).
  assert (PRE0 : keep (cmp_pre m p1 p2 n b1 b2 v usp bot)) by exact PRE. clear PRE.
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
  pose proof (mcc_spec RIP 0x97bdc 0 ltac:(split; [lia| reflexivity]) ltac:(lia) (musl_memcmp_real MCMP)) as MCC.
  change (2192 + Z.max 80 0) with 2272 in MCC. unfold mcc_stmt in MCC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (cmp_pre_munch m mm p1 p2 n b1 b2 v usp (usp + -48) bot _ _ PRE0 MU WM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold kHighShadowEnd; lia)) as PRE1 end.
  rewrite <- EU2 in PRE1.
  call MCC; [reflexivity| reflexivity| reflexivity| reflexivity| exact PRE1| rewrite EU2; lia| rewrite EU2; exact ST2| rewrite EU2; lia
            | unfold kHighShadowEnd; lia| rewrite EU2; lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2 in H; rename H into ST3 end.
  do 5 lstep.
  release_frame FR ST3 usp.
  lstep.
  unfold frame_post. sys_finish.
  rewrite EU. exact ST3.
Qed.

(* [comment removed for export] *)
Theorem bcmp_stub_spec : real_cmp_stmt 0x97b0c IMEMCMP_DEPTH.
Proof using RIP MCMP.
  unfold real_cmp_stmt. intros until lo. intros -> -> -> PRE HB ST LO LOLO SPH MI.
  pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lstep.
  lstep.
  eapply imemcmp_spec; [reflexivity| reflexivity| reflexivity| exact PRE| exact HB| exact ST| exact LO| exact LOLO| exact SPH| exact MI].
Qed.

(* [comment removed for export] *)
Definition bcmp_cell (m : mem) : Prop := ro_cells asegs m 0xa17f0 [C8 (Z_to_bv 64 0x97b0c)].

Theorem ibcmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 n : Z) (b1 b2 : list byte) (v bot lo : Z),
  bcmp_cell m ->
  a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 n ->
  cmp_pre m p1 p2 n b1 b2 v (bv_unsigned sp) bot -> bot <= bv_unsigned sp - IBCMP_DEPTH ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - IBCMP_DEPTH -> kHighShadowEnd < lo -> bv_unsigned sp < 2^63 -> mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v [(bv_unsigned sp - IBCMP_DEPTH, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4407c) fc None m (seg_rom asegs)).
Proof using RIP MCMP.
  intros until lo. intros RB -> -> -> PRE HB ST LO LOLO SPH MI.
  unfold bcmp_cell in RB.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 4560, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  pose proof PRE as (L1 & L2 & HM & N0 & P1 & P2 & R1 & R2 & _ & _ & S1 & S2 & _ & _ & _ & IC).
  assert (PRE0 : keep (cmp_pre m p1 p2 n b1 b2 v usp bot)) by exact PRE. clear PRE.
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
  pose proof (mcc_spec RIP 0x97b0c 2320 ltac:(split; [lia| reflexivity]) ltac:(lia) bcmp_stub_spec) as MCC.
  change (2192 + Z.max 80 2320) with 4512 in MCC. unfold mcc_stmt in MCC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (cmp_pre_munch m mm p1 p2 n b1 b2 v usp (usp + -48) bot _ _ PRE0 MU WM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold kHighShadowEnd; lia)) as PRE1 end.
  rewrite <- EU2 in PRE1.
  call MCC; [reflexivity| reflexivity| reflexivity| reflexivity| exact PRE1| rewrite EU2; lia| rewrite EU2; exact ST2| rewrite EU2; lia
            | unfold kHighShadowEnd; lia| rewrite EU2; lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2 in H; rename H into ST3 end.
  do 5 lstep.
  release_frame FR ST3 usp.
  lstep.
  unfold frame_post. sys_finish.
  rewrite EU. exact ST3.
Qed.

End WithRIP.
