(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import F_memset Pj_steps Pj_loc_defs Pj_loc_kit Pj_loc_get Pj_os_kit.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Ubsan.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Definition F_LOCALE_CTOR : Z := 0xaba40.
Definition F_IOS_INIT : Z := 0x843d8.
Definition LOC_IMP : Z := 0xf4388.

Lemma locale_ctor_specS : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo D : Z) (j : list byte),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z -> (0x117000 <= lo)%Z ->
  LOCB m -> rw_cells usegs m D [CB 8 j] -> (0 <= D)%Z -> (D + 8 <= 0xf3d88 \/ 0xf4c38 <= D)%Z -> (D + 8 <= 0x117000)%Z -> mem_inv usegs m ->
  evt usegs (locale_ctor_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo D 32 [] m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_LOCALE_CTOR) fc None m (seg_rom usegs)).
Proof.
  intros until j. intros ST LO LOLO LB DST D0 DSEP DHI MI.
  unfold F_LOCALE_CTOR in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (D, D + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  destruct LB as (j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & j10 & j11 & j12 & j13 & j14 & j15 & LB). unfold locb_cells in LB.
  carve_frame 32%nat ST.
  do 11 lstep.
  if_false.
  do 4 lstep.
  if_true.
  do 6 lstep.
  release_frame FR ST (bv_unsigned sp).
  unfold locale_ctor_post. sys_finish.
  exists j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13, j14, j15. assumption.
Qed.

Definition iosb_cells (vp : word) (sb : Z) : list cell :=
  [C8 vp; C4 (Z_to_bv 64 0x1002); C4 z64  ; C8 (Z_to_bv 64 6); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 (if (sb =? 0)%Z then 1 else 0)); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 sb); C8 (Z_to_bv 64 LOC_IMP); CB 80 (repeat (Z_to_bv 8 0) 80)].

Definition ios_base_init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo B sb : Z) (vp : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 136)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ LOCB m'
    /\ (exists (jv jp : list byte), rw_cells usegs m' B
          [CB 8 jv; C4 (Z_to_bv 64 4098); CB 4 jp; C8 (Z_to_bv 64 6); C8 z64; C4 (Z_to_bv 64 (Z.b2z (sb <? 1)%Z)); C4 z64; C8 (Z_to_bv 64 sb);
           C8 (Z_to_bv 64 LOC_IMP); CB 80 (repeat (Z_to_bv 8 0) 80)]).

Lemma ios_base_init_specS : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo B sb : Z) (junk : list byte),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z -> (0x117000 <= lo)%Z ->
  LOCB m -> rw_cells usegs m B [CB 136 junk] -> (0 <= B)%Z -> (B + 136 <= 0xf3d88 \/ 0xf4c38 <= B)%Z -> (B + 136 <= 0x117000)%Z ->
  (0 <= sb < 2^64)%Z -> mem_inv usegs m ->
  evt usegs (ios_base_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo B sb (Z_to_bv 64 0) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 sb) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_IOS_INIT) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros ST LO LOLO LB OSR B0 BSEP BHI SB MI.
  unfold F_IOS_INIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 136)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 136)]%Z m) as MUF. pose proof (wmono_refl usegs m) as WMF.

  apply (rw_cells_split_CB usegs _ _ [] 136 junk [] [8; 4; 4; 8; 8; 4; 4; 8; 8; 80]%nat) in OSR; [|reflexivity].
  cbn [mk_CB_cells app] in OSR. forget_junk OSR.
  carve_frame 16%nat ST.
  do 18 lstep.
  lstep.
  takeZ OSR 9%nat (B + 56)%Z P0. rename OSR into MS2.
  call_sp (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (B + 56) 0 80 _)%Z; [exact MS2 | assumption | lia | lia | lia | lia |].
  rename POST into MS2. change (Z.to_nat 80) with 80%nat in MS2. change (0 mod 256)%Z with 0%Z in MS2.
  glueZ P0 MS2. rename P0 into OSR.
  do 4 lstep.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  takeZ OSR 8%nat (B + 48)%Z P0. takeZ OSR 1%nat (B + 56)%Z LOC2.
  lazymatch type of MUF with munch ?W ?m0 ?m1 =>
    assert (LB2 : LOCB m1) by (apply (LOCB_transport W m0 m1 LB MUF WMF); cbv [disjoint_from fst snd]; repeat split; lia) end.
  clear LB MUF WMF.
  call (locale_ctor_specS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (B + 48)%Z);
    [exact ST | lia | lia | exact LB2 | exact LOC2 | lia | lia | lia | assumption |].
  rename POST into LB.
  apply evt_done. unfold ios_base_init_post, LOC_IMP. sys_finish.
  eexists _, _. glueZ P0 PC0. glueZ P0 OSR. exact P0.
Qed.

Definition iosb_cellsZ (vp : word) (sb : Z) : list cell :=
  [C8 vp; C4 (Z_to_bv 64 4098); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 6); C8 z64; C4 (Z_to_bv 64 (Z.b2z (sb <? 1)%Z)); C4 z64; C8 (Z_to_bv 64 sb);
   C8 (Z_to_bv 64 LOC_IMP); CB 80 (repeat (Z_to_bv 8 0) 80)].
Definition ios_base_init_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo B sb : Z) (vp : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 136)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ LOCB m'
    /\ rw_cells usegs m' B (iosb_cellsZ vp sb).

Lemma ios_base_init_specZ : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo B sb : Z) (vp : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z -> (0x117000 <= lo)%Z ->
  LOCB m -> rw_cells usegs m B [C8 vp; CB 128 (repeat (Z_to_bv 8 0) 128)] -> (0 <= B)%Z -> (B + 136 <= 0xf3d88 \/ 0xf4c38 <= B)%Z -> (B + 136 <= 0x117000)%Z ->
  (0 <= sb < 2^64)%Z -> mem_inv usegs m ->
  evt usegs (ios_base_init_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo B sb vp m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 sb) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_IOS_INIT) fc None m (seg_rom usegs)).
Proof.
  intros until vp. intros ST LO LOLO LB OSR B0 BSEP BHI SB MI.
  unfold F_IOS_INIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 136)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 136)]%Z m) as MUF. pose proof (wmono_refl usegs m) as WMF.

  apply (rw_cells_split_CB usegs _ _ [C8 vp] 128 _ [] [4; 4; 8; 8; 4; 4; 8; 8; 80]%nat) in OSR; [|reflexivity].
  cbv [mk_CB_cells app firstn skipn repeat] in OSR.
  carve_frame 16%nat ST.
  do 18 lstep.
  lstep.
  takeZ OSR 9%nat (B + 56)%Z P0. rename OSR into MS2.
  call_sp (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (B + 56) 0 80 _)%Z; [exact MS2 | assumption | lia | lia | lia | lia |].
  rename POST into MS2. change (Z.to_nat 80) with 80%nat in MS2. change (0 mod 256)%Z with 0%Z in MS2.
  glueZ P0 MS2. rename P0 into OSR.
  do 4 lstep.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  takeZ OSR 8%nat (B + 48)%Z P0. takeZ OSR 1%nat (B + 56)%Z LOC2.
  lazymatch type of MUF with munch ?W ?m0 ?m1 =>
    assert (LB2 : LOCB m1) by (apply (LOCB_transport W m0 m1 LB MUF WMF); cbv [disjoint_from fst snd]; repeat split; lia) end.
  clear LB MUF WMF.
  call (locale_ctor_specS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (B + 48)%Z);
    [exact ST | lia | lia | exact LB2 | exact LOC2 | lia | lia | lia | assumption |].
  rename POST into LB.
  apply evt_done. unfold ios_base_init_postZ, iosb_cellsZ, LOC_IMP. sys_finish.
  glueZ P0 PC0. glueZ P0 OSR. exact P0.
Qed.

