(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ARep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_aensure.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AKit AKit2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation MAYBE_STACK := 80 (only parsing).
Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition maybe_entry : Z := 0x3fdbc.

Definition maybe_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - MAYBE_STACK, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma maybe_release_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (c lo nf mfa au mu : Z) (w80 w88 : word),
  let RI := aregion_info L c in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MAYBE_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 0 ->
  m3_cells L m ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 80) [C8 w80] -> rw_cells asegs m (RI + 88) [C8 w88] ->
  1 <= c < K_NUM_CLASSES ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 ->
  evtF asegs RNG (maybe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 maybe_entry) fc None m (seg_rom asegs)).
Proof.
  intros until w88. cbv zeta.
  intros ST CEIL LO MI -> -> -> MC REG R80 R88 HC SP1 SP2 RIMG RSTK RRI.
  pose proof MC as MC0. destruct MC0 as (_ & RC & _ & _ & _ & _ & _ & ISB & IREL & ISE & IPRE).
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & _). clear MC RC ISB IPRE.
  unfold AINSTANCE, K_NUM_CLASSES, K_SPACE_SIZE, K_SPACE_EXTRA, maybe_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128)
    by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 80%nat ST.
  do 10 step.
  do 4 step.
  step.
  step. zstep.

  Ltac tail RIE SP1 SP2 HC :=
    step; step; step;
    zstep;
    lazymatch type of RIE with ?ri = _ =>
      setreg 22%Z (Z_to_bv 64 ri) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia)
    end;
    step; if_lit;
    step;
    zstep;
    step;
    let K1 := fresh "K" in
    if_cases K1;
    [
      step; step; zstep; zstep;
      step;
      let K2 := fresh "K" in
      if_cases K2;
      [ do 11 step
      | step; if_lit;
        step;
        step; if_lit;
        do 11 step ]
    | do 12 step ].
  step. if_cases K31; zify_cond K31.
  -
    step. step.
    tail RIE SP1 SP2 HC.
    all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
  - step.
    step. if_cases K16; zify_cond K16.
    +
      do 9 zstep.
      tail RIE SP1 SP2 HC.
      all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
    + zstep. step.
      tail RIE SP1 SP2 HC.
      all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import AProto.TwinB ABase.TwinB ARep.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import F_aensure.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AKit.TwinB AKit2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation MAYBE_STACK := 80 (only parsing).
Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition maybe_entry : Z := 0x4074c.

Definition maybe_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - MAYBE_STACK, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma maybe_release_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (c lo nf mfa au mu : Z) (w80 w88 : word),
  let RI := aregion_info L c in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MAYBE_STACK ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 0 ->
  m3_cells L m ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 80) [C8 w80] -> rw_cells bsegs m (RI + 88) [C8 w88] ->
  1 <= c < K_NUM_CLASSES ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 ->
  evtF bsegs RNG (maybe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 maybe_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until w88. cbv zeta.
  intros ST CEIL LO MI -> -> -> MC REG R80 R88 HC SP1 SP2 RIMG RSTK RRI.
  pose proof MC as MC0. destruct MC0 as (_ & RC & _ & _ & _ & _ & _ & ISB & IREL & ISE & IPRE).
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & _). clear MC RC ISB IPRE.
  unfold AINSTANCE, K_NUM_CLASSES, K_SPACE_SIZE, K_SPACE_EXTRA, maybe_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128)
    by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 80%nat ST.
  do 10 step.
  do 4 step.
  step.
  step. zstep.

  Ltac tail RIE SP1 SP2 HC :=
    step; step; step;
    zstep;
    lazymatch type of RIE with ?ri = _ =>
      setreg 22%Z (Z_to_bv 64 ri) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia)
    end;
    step; if_lit;
    step;
    zstep;
    step;
    let K1 := fresh "K" in
    if_cases K1;
    [
      step; step; zstep; zstep;
      step;
      let K2 := fresh "K" in
      if_cases K2;
      [ do 11 step
      | step; if_lit;
        step;
        step; if_lit;
        do 11 step ]
    | do 12 step ].
  step. if_cases K31; zify_cond K31.
  -
    step. step.
    tail RIE SP1 SP2 HC.
    all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
  - step.
    step. if_cases K16; zify_cond K16.
    +
      do 9 zstep.
      tail RIE SP1 SP2 HC.
      all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
    + zstep. step.
      tail RIE SP1 SP2 HC.
      all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
Qed.
End CANSEC1.
End TwinB.
