(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the discharge of lib/B/W_contract.v's rg_place record at image B's pinned
   placement PB_fr, its start-up instance TfibB (lib/B/YD2l.v) and RG := fr_RG (= fr_globals_b), with no hypothesis:
   the image-B twin of lib/A/W_rg_place.v together with the RG5 / RGO / RGP_c discharge in image A's top.
   - The geometry (g_lock / g_nsrc / g_src = A_OBJ 3 / 4 / 5, their alignments, and the five relay ranges apart from
     A_OBJ 0 / 6 / 30 and TfibB's as_uar_cell) is decided by vm_compute on the pinned placement; no address numeral
     is written here.
   - The five relay ranges (rg_rng) are bytes of G_fr_obj, the program's 20 objects (rng_cover_zr, decided), so
     lib/B/W_LLVMFuzzerTestOneInput_G.v's instance facts give the rest: c_img (in the image), c_obj_unowned (not
     an owned static of TfibB, from YF0m's ts_owned), c_obj_noerr (not errno's cell) and, for g_lock and g_nsrc,
     c_glob_wr (writable in every memory).
   - Their premises are TfibB's start-up facts: TfibB_syms (lib/B/YD2l.v) for c_obj_unowned, and errno's place
     as_errno TfibB = TFIB_ERRNO_B from YF0m's ts_errno at TfibB_syms (B's top_x discharges HEV the same way). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_G.
(* the start-up instance TfibB and its TfibSyms witness; YF0m's ts_errno is cited qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section b.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* rg_place at TfibB / fr_RG, the type of B top_x's Section hypothesis RGP_x *)
Lemma fr_rg_place_b : rg_place TfibB fr_RG.
Proof.
  (* errno's place at TfibB (_G.v's premise HEV), from the start-up instance *)
  assert (HEV : as_errno TfibB = TFIB_ERRNO_B) by (rewrite (YF0m.ts_errno TfibB TfibB_syms); reflexivity).
  (* the five relay ranges as a range list, and each is a byte range of G_fr_obj (decided) *)
  assert (RG5 : forall a, rg_rng fr_RG a -> inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4); (rg_src fr_RG, 8);
      (rg_wake fr_RG + 4, 4); (rg_s fr_RG, 4 * ASRC)] a).
  { intros a Ha. unfold rg_rng in Ha. unfold inG.
    destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]];
      repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact (conj (proj1 Ha) (proj2 Ha))
                    | apply Exists_cons_tl]). }
  assert (RGO : forall a, inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4); (rg_src fr_RG, 8); (rg_wake fr_RG + 4, 4);
      (rg_s fr_RG, 4 * ASRC)] a -> inG G_fr_obj a).
  { apply inG_sub.
    repeat (apply Forall_cons; [intros a Ha; revert a Ha; apply rng_cover_zr; vm_compute; reflexivity|]).
    apply Forall_nil. }
  unfold rg_place.
  (* the A_OBJ equalities and the alignments, on the pinned placement *)
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  (* in the image, not an owned static, not errno: _G.v's facts about the 20 objects *)
  split.
  { intros a Ha. pose proof (RGO a (RG5 a Ha)) as Ho.
    exact (conj (c_img TfibB HEV a (obj_c TfibB a Ho))
      (conj (c_obj_unowned TfibB TfibB_syms a Ho) (c_obj_noerr TfibB HEV a Ho))). }
  (* g_lock and g_nsrc writable in every memory: _G.v's c_glob_wr at G_fr_c *)
  split.
  { intros Hh m a Ha _.
    assert (Hr : rg_rng fr_RG a) by (unfold rg_rng; destruct Ha as [Ha|Ha]; [left | right; left]; exact Ha).
    exact (c_glob_wr TfibB HEV Hh m a (obj_c TfibB a (RGO a (RG5 a Hr)))). }
  (* apart from A_OBJ 0 / 6 / 30 and the uar cell (decided) *)
  intros a Ha. pose proof (RG5 a Ha) as H5.
  split; [|split; [|split]]; revert H5; apply apart_of_b; vm_compute; reflexivity.
Qed.
End b.
