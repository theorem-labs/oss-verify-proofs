(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section Exit.
  Variable E : s2env.
  Hypothesis OK : env_ok E.

  Lemma s2_exit : forall err x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    s2_errok E err ->
    MEMX E fc m1 ->
    evt usegs (s2_post E)
      (MS (mkR x1 (wz (e_SP E)) (e_gp E) (e_tp E) x5 x6 x7 x8 x9 (wz err) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4be14) fc None m1 (seg_rom usegs)).
  Proof using OK.
    intros until m1. intros HE H.
    assert (HE64 : (0 <= err < 64)%Z) by (destruct HE as [HE1 | [-> _]]; lia).
    destruct OK. unfold S2_STACK in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    s2_open_memx H.
    do 15 step.
    release_frame FR ST (bv_unsigned (e_sp E)).
    apply evt_done. unfold s2_post.
    do 18 eexists. split; [reflexivity|].
    split; [rewrite u64_small by lia; lia|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|].
    split; [eexists; exact IMPL|]. split; [exact DOCC|]. split; [exact IDXA|]. split; [exact BUFRO|].
    split; [exact TAPEW|]. split; [exact SBUFW|].
    split; [eexists; split; [exact OCA|exact OCL]|].
    split; [eexists; split; [exact IAA|exact IAL]|].
    split; [exact ST|].
    destruct TIMG as (T1 & T2 & T3 & T4 & _ & _ & SB).
    destruct HE as [HF | [-> HOKT]]; [left; unfold s2_fail; rewrite u64_small by lia; exact HF | right; split; [reflexivity|]].
    exists (e_tws E), (e_sbs E). split; [exact T1|]. split; [exact T2|]. split; [exact HOKT|]. split; [exact SB|]. split; [exact T3|exact T4].
  Qed.
End Exit.
