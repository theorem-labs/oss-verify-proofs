(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi Zpa.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zwd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section Exit.
  Variable E : s2env.
  Hypothesis OK : env_ok E.

  Lemma s2_exit : forall x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMX E fc m1 -> (s2_fail x9 \/ (x9 = Z_to_bv 64 0 /\ tape_ok (e_tws E) (e_sbs E))) ->
    evt psegs (s2_post E)
      (MS (mkR x1 (wz (e_SP E)) (e_gp E) (e_tp E) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x2d2c8) fc None m1 (seg_rom psegs)).
  Proof using OK.
    intros until m1. intros H HRES.
    destruct OK. unfold S2_STACK in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    s2_open_memx H.
    do 16 step.
    release_frame FR ST (bv_unsigned (e_sp E)).
    apply evt_done. unfold s2_post.
    do 18 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|].
    split; [eexists; exact IMPL|]. split; [exact DOCC|]. split; [exact IDXA|]. split; [exact BUFRO|].
    split; [exact TAPEW|]. split; [exact SBUFW|].
    split; [eexists; split; [exact OCA|exact OCL]|].
    split; [eexists; split; [exact IAA|exact IAL]|].
    split; [exact ST|].
    destruct TIMG as (T1 & T2 & T3 & T4 & _ & _ & SB).
    destruct HRES as [HF | [-> HOKT]]; [left; exact HF | right; split; [reflexivity|]].
    exists (e_tws E), (e_sbs E). split; [exact T1|]. split; [exact T2|]. split; [exact HOKT|]. split; [exact SB|]. split; [exact T3|exact T4].
  Qed.
End Exit.
