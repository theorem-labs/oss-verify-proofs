(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_no_overread.v, with its module paths and module names changed; 23 of its 47 lines of code are new or changed and 828 lines of the source are left out. *)
(* check_lookup_contract (fuzz_lock.ubsan, 0x12e34) from the walk of lib/U/Prog/cl_walk.v with Run := SR: the run
   lemmas are crt_runA / crt_runN (U cno_glue.v), malloc and free are the U kit's malloc_contract / free_contract, and
   malloc's budget is room_slots. Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i YL01 YL00 YO10.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require MState Mem Frame Exec Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import memcpy_c rp_lock_lookup_c rp_lock_lookup
  strlen_c memchr_c bcmp_c number_c check_no_overread_c check_no_overread check_lookup_c cno_glue cno_segs cl_segs RpLib cl_walk.
Import ListNotations.
Local Open Scope Z_scope.

Section CL.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALPC : ms_malloc B = CNO_MALLOC.
Hypothesis FREEPC : ms_free B = CNO_FREE.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CT : ctx_owned B API.
Hypothesis MALLOC : malloc_contract B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis MC : memcpy_contract.
Hypothesis SLC : strlen_contract.
Hypothesis MCH : memchr_contract.
Hypothesis BC : bcmp_contract.


Theorem check_lookup_holds : check_lookup_contract B API.
Proof.
  intros L A regs mem md t n pa k rate T P SL b _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19
    H20 H21 H22 H23.
  assert (RB : forall c (R' Q' : config -> Prop), SR (ms_segs B) c R' -> (forall c', R' c' -> SR (ms_segs B) c' Q') ->
            SR (ms_segs B) c Q') by (intros c R' Q' HR HK; eapply SR_bind; [exact HR | exact HK]).
  assert (RR : forall c (Q' : config -> Prop), Q' c -> SR (ms_segs B) c Q') by (intros c Q' HQ; apply SR_ret; exact HQ).
  pose proof (cl_nb_bounds n ltac:(lia)) as NB.
  assert (RM : room_slots b (cl_nb n)) by (apply room_slots_big; lia).
  eapply cl_entry with (Run := SR (ms_segs B)) (Room := room_slots); try eassumption.
  all: first
    [ intros fx' regs' pc mem' md' Q' P' Hh Hl HE HQ HK; exact (crt_runA (fx := fx') B SEGS regs' pc mem' md' Q' P' Hh Hl HE HQ HK)
    | intros regs' pc mem' md' Q' P' Hh Hl Hro HE HQ HK; exact (crt_runN B SEGS regs' pc mem' md' Q' P' Hh Hl Hro HE HQ HK)
    | intros L' A' regs' mem' md' n' b' Hp Hr Hn Hs Hm; exact (MALLOC L' A' regs' mem' md' n' b' Hp Hr Hn Hs Hm)
    | intros fx' L' A' regs' mem' md' p n' b' Hp Hr Hi Hg Hs; exact (FREE fx' L' A' regs' mem' md' p n' b' Hp Hr Hi Hg Hs) ].
Qed.

End CL.
