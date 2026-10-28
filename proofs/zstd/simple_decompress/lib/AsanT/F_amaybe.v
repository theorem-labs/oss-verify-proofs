(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ARep F_apoison F_ammap F_aensure.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation MAYBE_STACK := 80 (only parsing).
Section CANSEC1. Context {rc : runConstT}.
Definition maybe_entry : Z := 0x36938.

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
  do 10 step.                                                  (* [comment removed for export] *)
  do 4 step.                                                   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac tail RIE SP1 SP2 HC :=
    step; step; step;                                          (* [comment removed for export] *)
    zstep;                                                     (* [comment removed for export] *)
    lazymatch type of RIE with ?ri = _ =>
      setreg 22%Z (Z_to_bv 64 ri) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia)
    end;
    step; if_lit;                                              (* [comment removed for export] *)
    step;                                                      (* [comment removed for export] *)
    zstep;                                                     (* [comment removed for export] *)
    step;
    let K1 := fresh "K" in
    if_cases K1;
    [ (* [comment removed for export] *)
      step; step; zstep; zstep;                                (* [comment removed for export] *)
      step;
      let K2 := fresh "K" in
      if_cases K2;
      [ do 11 step                                             (* [comment removed for export] *)
      | step; if_lit;                                          (* [comment removed for export] *)
        step;                                                  (* [comment removed for export] *)
        step; if_lit;                                          (* [comment removed for export] *)
        do 11 step ]
    | do 12 step ].                                            (* [comment removed for export] *)
  step. if_cases K31; zify_cond K31.
  - (* [comment removed for export] *)
    step. step.                                                (* [comment removed for export] *)
    tail RIE SP1 SP2 HC.
    all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
  - step.                                                      (* [comment removed for export] *)
    step. if_cases K16; zify_cond K16.
    + (* [comment removed for export] *)
      do 9 zstep.
      tail RIE SP1 SP2 HC.
      all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
    + zstep. step.                                             (* [comment removed for export] *)
      tail RIE SP1 SP2 HC.
      all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
Qed.
End CANSEC1.
