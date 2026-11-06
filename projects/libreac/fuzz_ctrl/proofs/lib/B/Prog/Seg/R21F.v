(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1421 of its 1489 lines of code are new or changed and 943 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R21.v; 223 of its 396 lines of code are new or changed and 1316 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R21.v r21_a5c_next, r21_a5c_last, r21_latch_next, r21_latch_last, r21_p1_evt_n,
     r21_p1_evt, r21_tail_evt at a working branch 3803efccea0
     (blob 54812916d1e4a55c3dac312e07f10606976d0d30);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r21_a5c_next_of_F, r21_a5c_last_of_F, r21_latch_next_of_F, r21_latch_last_of_F (evtF_evt + rng_all)
     re-derive the source statements R21.v:284-305, :307-326, :221-251, :253-280 verbatim; the split stretches
     r21_p1_pre_F re-runs R21.v:505-512 (the stretch of r21_p1_evt_n :475-554 and of r21_p1_evt :557-610 up to the
     meta_fill_f8 entry) and r21_tail_pre_F re-runs R21.v:392-422 (the stretch of r21_tail_evt :330-471 up to the
     wrapper_strcmp entry). *)
(* rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcReply RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth RcEmit RcDecl RcParseLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import strcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_set_shadow_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot RHelp RtmB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R21.
(* Last: StepF's step / if_true (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF ExecF_all StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.
Module ASS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_set_shadow_c.

(* The store hook of R21.v (`sb s8,k(s3)`: le1 v is [Z_to_bv 8 (bv_unsigned v)] by conversion), on the
   four-argument evtF goal pattern; StepF's norm_lit_store_bytes knows only the literal stores
   (pilot fix (2) of RECIPE.md (a working note, not in this delivery)). *)
Local Ltac fix_lit_storeF :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) => change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]
  | _ => idtac
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::=
  fix_lit_storeF; norm_lit_store_bytes;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

(* ---- the latch from its own cut 0x81ac0 (seg_R21_a5c): addiw s6,s6,1; li a0,7; bne. No memory access, so no
   rng premise. ---- *)

Lemma r21_a5c_next_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bz : Z),
    s6 = Z_to_bv 64 bz -> 0 <= bz <= 5 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x816ec) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3v /\ getr R 20 = s4 /\ getr R 21 = s5 /\
         getr R 22 = Z_to_bv 64 (bz + 1) /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\ getr R 27 = s11 /\ m' = m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bz -> Hb.
  step. step. step.                                (* 81ac0 addiw ; 81ac4 li a0,7 ; 81ac8 bne *)
  rewrite ?(MState.unsigned_lit bz) by lia. rewrite ?R21.r21_swrap32 by lia. rewrite ?R21.r21_bv_eqb by lia.
  if_true.
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  do 15 (split; [reflexivity|]). reflexivity.
Qed.

Lemma r21_a5c_last_F : forall (RNG : footprint) (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    s6 = Z_to_bv 64 6 ->
    (forall (a0' s6' : word),
       evtF rsegs RNG Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x81b00) fc None m (seg_rom rsegs))) ->
    evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m -> HK.
  step. step. step.                                (* 81ac0 addiw ; 81ac4 li a0,7 ; 81ac8 bne *)
  rewrite ?(MState.unsigned_lit 6) by lia. rewrite ?R21.r21_swrap32 by lia. rewrite ?R21.r21_bv_eqb by lia.
  if_false.
  step.                                            (* 81acc j 81b00 *)
  eapply HK.
Qed.

(* ---- the latch 0x81aa0 .. 0x81ac8: the eight frame shadow stores S(fr) + 296 .. 312, then the branch ---- *)

Lemma r21_latch_next_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bz : Z) (junk : list byte),
    s6 = Z_to_bv 64 bz -> 0 <= bz <= 5 ->
    rw_cells rsegs m (bv_unsigned s3v + 296) [CB 17 junk] ->
    stk rsegs m (bv_unsigned s3v + 296) (bv_unsigned s3v + 313) ->
    rng RNG (bv_unsigned s3v + 296) 17 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x816ec) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3v /\ getr R 20 = s4 /\ getr R 21 = s5 /\
         getr R 22 = Z_to_bv 64 (bz + 1) /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\ getr R 27 = s11 /\
         munch [(bv_unsigned s3v + 296, bv_unsigned s3v + 313)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' (bv_unsigned s3v + 296) (bv_unsigned s3v + 313))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81aa0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bz junk -> Hb RW ST Rsh.
  pose proof (rw_cells_bound _ _ _ _ RW) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (munch_refl [(bv_unsigned s3v + 296, bv_unsigned s3v + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step. step. step. step.   (* 81aa0 .. 81abc : the eight shadow stores *)
  step. step. step.                                (* 81ac0 addiw ; 81ac4 li a0,7 ; 81ac8 bne *)
  rewrite ?(MState.unsigned_lit bz) by lia. rewrite ?R21.r21_swrap32 by lia. rewrite ?R21.r21_bv_eqb by lia.
  if_true.
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  do 15 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM | exact ST].
Qed.

Lemma r21_latch_last_F : forall (RNG : footprint) (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    s6 = Z_to_bv 64 6 ->
    rw_cells rsegs m (bv_unsigned s3v + 296) [CB 17 junk] ->
    stk rsegs m (bv_unsigned s3v + 296) (bv_unsigned s3v + 313) ->
    rng RNG (bv_unsigned s3v + 296) 17 ->
    (forall (a0' s6' : word) (m' : word -> option byte),
       munch [(bv_unsigned s3v + 296, bv_unsigned s3v + 313)] m m' -> wmono rsegs m m' ->
       stk rsegs m' (bv_unsigned s3v + 296) (bv_unsigned s3v + 313) ->
       evtF rsegs RNG Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x81b00) fc None m' (seg_rom rsegs))) ->
    evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81aa0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk -> RW ST Rsh HK.
  pose proof (rw_cells_bound _ _ _ _ RW) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (munch_refl [(bv_unsigned s3v + 296, bv_unsigned s3v + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step. step. step. step.   (* 81aa0 .. 81abc : the eight shadow stores *)
  step. step. step.                                (* 81ac0 addiw ; 81ac4 li a0,7 ; 81ac8 bne *)
  rewrite ?(MState.unsigned_lit 6) by lia. rewrite ?R21.r21_swrap32 by lia. rewrite ?R21.r21_bv_eqb by lia.
  if_false.
  step.                                            (* 81acc j 81b00 *)
  eapply HK; [exact MU | exact WM | exact ST].
Qed.

(* ---- the auditor's compare lemmas: the source statements, verbatim, from the _F forms at RNG_all ---- *)

Lemma r21_a5c_next_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bz : Z),
    s6 = Z_to_bv 64 bz -> 0 <= bz <= 5 ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x816ec) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3v /\ getr R 20 = s4 /\ getr R 21 = s5 /\
         getr R 22 = Z_to_bv 64 (bz + 1) /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\ getr R 27 = s11 /\ m' = m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac0) fc None m (seg_rom rsegs)).
Proof.
  intros. eapply (evtF_evt rsegs RNG_all). eapply r21_a5c_next_F; eassumption.
Qed.
Definition r21_a5c_next_src_check : ltac:(let T := type of R21.r21_a5c_next in exact T) := r21_a5c_next_of_F.

Lemma r21_a5c_last_of_F : forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    s6 = Z_to_bv 64 6 ->
    (forall (a0' s6' : word),
       evt rsegs Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x81b00) fc None m (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac0) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Hs6 HK.
  eapply evtF_evt with (RNG := RNG_all).
  eapply r21_a5c_last_F; [exact Hs6|].
  intros a0' s6'. apply evt_evtF_all. apply HK.
Qed.
Definition r21_a5c_last_src_check : ltac:(let T := type of R21.r21_a5c_last in exact T) := r21_a5c_last_of_F.

Lemma r21_latch_next_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bz : Z) (junk : list byte),
    s6 = Z_to_bv 64 bz -> 0 <= bz <= 5 ->
    rw_cells rsegs m (bv_unsigned s3v + 296) [CB 17 junk] ->
    stk rsegs m (bv_unsigned s3v + 296) (bv_unsigned s3v + 313) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x816ec) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3v /\ getr R 20 = s4 /\ getr R 21 = s5 /\
         getr R 22 = Z_to_bv 64 (bz + 1) /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\ getr R 27 = s11 /\
         munch [(bv_unsigned s3v + 296, bv_unsigned s3v + 313)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' (bv_unsigned s3v + 296) (bv_unsigned s3v + 313))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81aa0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bz junk Hs6 Hb RW ST.
  pose proof (rw_cells_bound _ _ _ _ RW) as HB. cbn [cells_size csize Nat.add] in HB.
  eapply evtF_evt. eapply r21_latch_next_F; try eassumption.
  apply rng_all; lia.
Qed.
Definition r21_latch_next_src_check : ltac:(let T := type of R21.r21_latch_next in exact T) := r21_latch_next_of_F.

Lemma r21_latch_last_of_F : forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    s6 = Z_to_bv 64 6 ->
    rw_cells rsegs m (bv_unsigned s3v + 296) [CB 17 junk] ->
    stk rsegs m (bv_unsigned s3v + 296) (bv_unsigned s3v + 313) ->
    (forall (a0' s6' : word) (m' : word -> option byte),
       munch [(bv_unsigned s3v + 296, bv_unsigned s3v + 313)] m m' -> wmono rsegs m m' ->
       stk rsegs m' (bv_unsigned s3v + 296) (bv_unsigned s3v + 313) ->
       evt rsegs Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x81b00) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81aa0) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk Hs6 RW ST HK.
  pose proof (rw_cells_bound _ _ _ _ RW) as HB. cbn [cells_size csize Nat.add] in HB.
  eapply evtF_evt with (RNG := RNG_all).
  eapply r21_latch_last_F; [exact Hs6 | exact RW | exact ST | apply rng_all; lia |].
  intros a0' s6' m' MU WM ST'. apply evt_evtF_all. apply HK; assumption.
Qed.
Definition r21_latch_last_src_check : ltac:(let T := type of R21.r21_latch_last in exact T) := r21_latch_last_of_F.

(* ---- the has_identity_record = 0 path 0x81c60 .. the meta_fill_f8 entry (the P1 suffix) ----
   r21_p1_evt_n (R21.v:475-554) and r21_p1_evt (:557-610) call meta_fill_f8 and end AT its return pc 0x81ca8, so
   the split leaves one stretch: 0x81c60 up to the callee entry 0x55144 with ra = 0x81ca8. r21_p1_evt is
   r21_p1_evt_n on MemNorm.normalize (R21.v:580-609), so this one stretch serves both runs; the post state of Q
   carries exactly the facts the source fed to the asan_set_shadow_f8 contract (R21.v:513-533). *)

Lemma r21_p1_pre_F : forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Q : Z) (junk : list byte),
    s1 = Z_to_bv 64 A ->
    AC.GT <= bv_unsigned s3v -> bv_unsigned s3v + 392 <= A -> A + 448 <= 2 ^ 64 ->
    bv_unsigned s3v <= Q -> Q + 187 <= bv_unsigned s3v + 291 ->
    (forall i, 0 <= i < 392 -> in_shadow (bv_unsigned s3v + i)) ->
    rw_cells rsegs m (bv_unsigned s3v + 272) [CB 19 junk] ->
    stk rsegs m (bv_unsigned s3v) (bv_unsigned s3v + 392) ->
    bytes_at rsegs m (A + 8) (le8 (Z_to_bv 64 Q)) ->
    mem_inv rsegs m -> asan_cells m ->
    rng RNG (bv_unsigned s3v + 272) 19 -> rng RNG (A + 8) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m1 : word -> option byte) (junkQ : list byte),
         ms' = MS R F (Z_to_bv 64 ASS.ASAN_SET_SHADOW_F8) fc None m1 (seg_rom rsegs) /\
         getr R 1 = Z_to_bv 64 0x81ca8 /\ getr R 10 = Z_to_bv 64 Q /\ getr R 11 = Z_to_bv 64 187 /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3v /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         munch [(bv_unsigned s3v, bv_unsigned s3v + 291)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 (bv_unsigned s3v) (bv_unsigned s3v + 392) /\
         rw_cells rsegs m1 Q [CB 187 junkQ] /\ asan_cells m1 /\ mem_inv rsegs m1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Q junk -> HSgt HSA HA1 HQ1 HQ2 Hsh RW ST R8 HMI HAC Rgsh Rg8.
  unfold AC.GT in HSgt.
  pose proof (rw_cells_bound _ _ _ _ RW) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (bv_unsigned_in_range 64 s3v) as HS3r. change (bv_modulus 64) with (2 ^ 64) in HS3r.
  pose proof (munch_refl [(bv_unsigned s3v, bv_unsigned s3v + 291)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.                                         (* 81c60 li s2,-8 *)
  step. step. step. step. step. step. step.     (* 81c64 .. 81c98 : the 14 shadow stores *)
  step. step. step. step. step. step. step.
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => tryif constr_eq mm m1 then idtac else rename mm into m1
  end.
  pose proof (rh_rdn m1 (A + 8) _ 8 R8 (length_le8 _)) as RD16.
  step. step. step.                             (* 81c9c li a1,187 ; 81ca0 ld a0,8(s1) ; 81ca4 jal *)
  (* the 187 bytes [Q, Q + 187) as a cell run (R21.v:513-526) *)
  assert (HstkQ : stk rsegs m1 Q (Q + 187)).
  { destruct ST as (S0 & S1 & SH). split; [lia|]. split; [lia|]. intros a Ha. apply SH. lia. }
  destruct (rh_bytes_of_present 187%nat m1 Q ltac:(lia) ltac:(lia)) as (junkQ & HjQ & HjQl).
  { intros k Hk. destruct HstkQ as (_ & _ & SH). exact (proj2 (SH (Q + Z.of_nat k) ltac:(lia))). }
  assert (RWQ : rw_cells rsegs m1 Q [CB 187 junkQ]).
  { rewrite <- HjQl. apply rh_rwc_CB; [exact HjQ|]. rewrite HjQl.
    split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct HstkQ as (_ & _ & SH). exact (proj1 (SH (Q + i) ltac:(lia))). }
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  apply evtF_done. do 3 eexists. split; [reflexivity|].
  do 13 (split; [first [ reflexivity | f_equal; lia ]|]).
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|].
  split; [exact RWQ|]. split; [exact HAC1 | exact HMI].
Qed.

(* ---- the tail 0x81b00 .. the wrapper_strcmp entry (b = 6) ----
   r21_tail_evt (R21.v:330-471) calls wrapper_strcmp on the h <> 0 arm and ends AT its return pc 0x81c58, so the
   split leaves one stretch: 0x81b00 to the callee entry 0x42aa0 with ra = 0x81c58. The h = 0 arm reaches no call
   and keeps the source's own continuation premise, in evtF form.
   The rng premises follow the arms (auditor a Theorem Labs lane, 2026-10-29 09:00Z, and a Theorem Labs lane's S5 items; measured on
   the image's disassembly 0x81b00 .. 0x81c58).  Everything before `beqz a0,0x81c60` at 0x81c0c is read on both arms;
   after it falls through (h <> 0) the run reads three more places.  Both arms: of the id_rt record at S5, S5 + 0 .. 1
   (lhu 0x81b34), S5 + 2 (lbu 0x81b04), S5 + 22 .. 27 (lhu 0x81b74, 0x81ba4, 0x81bd4) and S5 + 36 (lbu 0x81b50), so the
   unguarded rows are [S5, S5 + 3), [S5 + 22, S5 + 28) and [S5 + 36, S5 + 37) (S5 + 3 .. 19, 21 and 28 .. 35 are read on
   no arm); of the row words [mr + 266, mr + 288), only [mr + 266, mr + 274) (lhu at 0x81b40, 0x81b80, 0x81bb0, 0x81be0;
   mr + 274 .. mr + 279 are read on no arm).  h <> 0 only: S5 + 20 (lbu 0x81c14), the shadow byte of mr + 280 (lbu
   0x81c30) and the name pointer [mr + 280, mr + 288) (ld a1,0(a0) at 0x81c3c); those three rng premises are guarded
   by h <> 0, so the lemma can be used with a footprint that does not cover them on the h = 0 arm.  The value premise
   on that shadow byte (K280) is guarded by h <> 0 too (auditor a Theorem Labs lane, 2026-10-29 10:38Z): the h = 0 arm never
   reads it. *)

Local Ltac r21F_shfix :=
  repeat match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?x)) 3] => rewrite (MState.unsigned_lit x) by lia
  end.

Local Ltac r21F_beq_refl :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true; [cbv iota | symmetry; apply R21.r21_eqb_refl]
  end.

Lemma r21_tail_pre_F :
  forall (RNG : footprint) (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv lo A S5 mr fw maj mnr pat h nm : Z) (sx : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= spv < 2 ^ 64 -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= S5 -> S5 + 38 <= 2 ^ 64 ->
    0 <= mr -> mr + 296 <= 2 ^ 63 -> 0 <= h < 2 ^ 32 ->
    ov_read_bytes rsegs m (wa (A + 144)) 8 = Some (le8 (Z_to_bv 64 S5)) ->
    ov_read_bytes rsegs m (wa (A + 32)) 8 = Some (le8 (Z_to_bv 64 0)) ->
    ov_read_bytes rsegs m (wa (A + 272)) 8 = Some (le8 (Z_to_bv 64 mr)) ->
    ov_read_bytes rsegs m (wa (S5 + 2)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 266) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 268) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 270) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 272) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 56) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    (h <> 0 -> ov_read_bytes rsegs m (wa (Z.shiftr (mr + 280) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0]) ->
    ov_read_bytes rsegs m (wa S5) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (mr + 266)) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (S5 + 36)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (S5 + 22)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (mr + 268)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (S5 + 24)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (mr + 270)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (S5 + 26)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 272)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 56)) 4 = Some (le4 (Z_to_bv 64 h)) ->
    (h <> 0 ->
       ov_read_bytes rsegs m (wa (S5 + 20)) 1 = Some [Z_to_bv 8 1] /\
       ov_read_bytes rsegs m (wa (mr + 280)) 8 = Some (le8 (Z_to_bv 64 nm)) /\ 0 < nm < 2 ^ 64 /\
       bytes_at rsegs m (S5 + 3) (sx ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) sx /\
       bytes_at rsegs m nm (sx ++ [Z_to_bv 8 0]) /\
       Z.of_nat (strcmp_k sx sx) + 1 <= 2^40 /\
       addressable m (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       end_in_app (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       addressable m nm (Z.of_nat (strcmp_k sx sx) + 1) /\ end_in_app nm (Z.of_nat (strcmp_k sx sx) + 1) /\
       app_mem (S5 + 3 + 7) /\ app_mem (nm + 7) /\
       stk rsegs m lo spv /\ lo + STRCMP_WRAP_K <= spv /\ HIGHMEM_BEG <= lo /\ spv <= APPMEM_END /\
       (S5 + 3 + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= S5 + 3) /\
       (nm + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= nm) /\
       asan_cells m /\ shadow_rw m /\ MN.ro_agree rsegs m /\
       bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
       bytes_at rsegs m (CF + 250) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 245) [Z_to_bv 8 0]) ->
    rng RNG (A + 32) 8 -> rng RNG (A + 144) 8 -> rng RNG (A + 272) 8 ->
    rng RNG S5 3 -> rng RNG (S5 + 22) 6 -> rng RNG (S5 + 36) 1 -> rng RNG (mr + 56) 4 -> rng RNG (mr + 266) 8 ->
    rng RNG (Z.shiftr (mr + 266) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 268) 3 + ASAN_K) 1 ->
    rng RNG (Z.shiftr (mr + 270) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 272) 3 + ASAN_K) 1 ->
    rng RNG (Z.shiftr (mr + 56) 3 + ASAN_K) 1 ->
    (h <> 0 -> rng RNG (S5 + 20) 1 /\ rng RNG (mr + 280) 8 /\ rng RNG (Z.shiftr (mr + 280) 3 + ASAN_K) 1) ->
    (h = 0 -> forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word), a0' = Z_to_bv 64 0 ->
       evtF rsegs RNG Q
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs))) ->
    (h <> 0 -> forall R : bvmap 5 word,
       getr R 1 = Z_to_bv 64 0x81c58 -> getr R 10 = Z_to_bv 64 (S5 + 3) -> getr R 11 = Z_to_bv 64 nm ->
       getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
       getr R 19 = s3 -> getr R 21 = s5 -> getr R 22 = s6 -> getr R 23 = s7 -> getr R 24 = s8 ->
       getr R 25 = s9 -> getr R 26 = s10 ->
       Q (MS R F (Z_to_bv 64 STRCMP_WRAP) fc None m (seg_rom rsegs))) ->
    evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b00) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv lo A S5 mr fw maj mnr pat h nm sx -> -> -> Hsp HA0 HA1 HS0 HS1 Hm0 Hm1 Hh
    R144 R32 R272 R2 K266 K268 K270 K272 K56 K280 R0 M266 R36 R22 M268 R24 M270 R26 M272 M56 HN
    Rg32 Rg144 Rg272 RgS5 RgS22 RgS36 Rgm56 Rgm266 RgK266 RgK268 RgK270 RgK272 RgK56 GHN K0 Kbf.
  step. step. step. if_true.                    (* 81b00 ld 144; 81b04 lbu 2; 81b08 bnez *)
  step. step. if_true.                          (* 81b10 ld 32; 81b14 beqz *)
  step. step. step. step. r21F_shfix.           (* 81b1c ld 272; addi 266; srli; add *)
  step. step. step. step. if_true.              (* 81b2c lb; 81b30 ld 144; 81b34 lhu 0; 81b38 beqz *)
  step. step. r21F_beq_refl.                    (* 81b40 lhu; 81b44 beq *)
  step. step. step. if_true.                    (* 81b4c ld 144; 81b50 lbu 36; 81b54 bnez *)
  step. step. step. step. r21F_shfix.           (* 81b5c ld 272; addi 268; srli; add *)
  step. step. step. step. if_true.              (* 81b6c lb; 81b70 ld 144; 81b74 lhu 22; 81b78 beqz *)
  step. step. r21F_beq_refl.                    (* 81b80 lhu; 81b84 beq *)
  step. step. step. step. r21F_shfix.           (* 81b8c ld 272; addi 270; srli; add *)
  step. step. step. step. if_true.              (* 81b9c lb; 81ba0 ld 144; 81ba4 lhu 24; 81ba8 beqz *)
  step. step. r21F_beq_refl.                    (* 81bb0 lhu; 81bb4 beq *)
  step. step. step. step. r21F_shfix.           (* 81bbc ld 272; addi 272; srli; add *)
  step. step. step. step. if_true.              (* 81bcc lb; 81bd0 ld 144; 81bd4 lhu 26; 81bd8 beqz *)
  step. step. r21F_beq_refl.                    (* 81be0 lhu; 81be4 beq *)
  step. step. step. step. r21F_shfix.           (* 81bec ld 272; addi 56; srli; add *)
  step. step. if_true.                          (* 81bfc lb; 81c00 beqz *)
  step. step.                                   (* 81c08 lw; 81c0c beqz a0,81c60 *)
  destruct (Z.eq_dec h 0) as [E0 | E0].
  - if_true_by (eq_trans (R21.r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_eq h 0) E0)).
    eapply (K0 E0).
    exact (R21.r21_eqb_eq _ _ (eq_trans (R21.r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_eq h 0) E0))).
  - if_false_by (eq_trans (R21.r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_neq h 0) E0)).
    destruct (HN E0) as (R20 & R280 & Hnm & HS1x & HS0x & HS2x & HK & HAX & HEX & HAY & HEY & HX7 & HY7 &
                         HST & HLO & HHM & HAE & HSEPx & HSEPy & HAC & HSW & HMIx & HGOT & HCF1 & HCF2).
    destruct (GHN E0) as (RgS20 & Rgm280 & RgK280). specialize (K280 E0).
    step. step. step. if_true.                  (* 81c10 ld 144; 81c14 lbu 20; 81c18 bnez *)
    step. step. step. step. r21F_shfix.         (* 81c20 ld 272; addi 280; srli; add *)
    step. step. if_true.                        (* 81c30 lbu (check); 81c34 beqz *)
    step. step. step. step.                     (* 81c3c ld a1,0(a0); 81c40 ld 144; 81c44 addi 3; 81c48 bnez *)
    if_true_by (f_equal negb (R21.r21_eqb0 nm Hnm)).
    step.                                       (* 81c54 jal wrapper_strcmp *)
    apply evtF_done.
    apply (Kbf E0); first [ reflexivity | f_equal; lia ].
Qed.
