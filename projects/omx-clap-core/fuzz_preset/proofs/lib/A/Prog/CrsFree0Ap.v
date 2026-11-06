(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v, with its module paths and module names changed; 671 of its 740 lines of code are new or changed and 859 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/CrsKitAp.v; 14 of its 44 lines of code are new or changed and 710 lines of the source are left out. *)
(* fuzz_preset, image A' (the #102 pins): ONE SHARED INTERIM PREMISE of the walk of check_reject_clean_starved,
   fuzz_free (NULL). KIT-OWNED INTERIM (a Theorem Labs lane's decision, 2026-10-29): it is tfuzz_free_specX (lib/A/PRH_FnAlloc.v
   blob 83fe93bc86e2 :252-301, the #102 kit tip of record decff67d721f) restricted to p = 0, and is
   replaced by that text once a Theorem Labs lane guards the text's entry position with p <> 0.
   WHY. decff's tpj_write_specX (PRH_FnWriter.v blob 2b497bc72172 :689-691) gives the model-run position after a
   pj_write only under prh_granted, so after a REFUSED grow (ran' = 1, q = 0) no position is known; tfuzz_free_specX
   asks iface_room_pos at entry on EVERY arm, p = 0 included, so the walk cannot meet it at the fuzz_free (q) that follows
   a refused whole write (W1 0x8234c, Z 0x82530) or at F (0x82408).
   TRUE BY fuzz_free (alloc.c :118-119): `if (!p) return;` - a NULL free makes no allocator call and writes nothing, so
   it needs no room position and no live-set bound, and states neither.
   THE RESTRICTION, and nothing else: p := 0 (`getr regs 10 = w64 0`); the entry premise iface_room_pos and the model
   run's binders (rp_sm .. rp_hist) are dropped; the post's three position conjuncts (the p = 0 keep, the p <> 0 HFr
   advance and the p <> 0 bulk step) are dropped; the class-24 bound `ccnt24 S <= L24 + DRV` is dropped at entry and in
   the post (after a refused write no position is known, so crs_cnt24's route to the bound is closed; a NULL free never
   calls free_cf, and S' = S keeps whatever bound S had); the free's block n and its premise `p = 0 \/ In (p, n) Lam`
   are dropped (true at p = 0); the post's last disjunction is its p = 0 arm (the p <> 0 arm is vacuous at p = 0). Every
   other premise and conjunct is the text's, in its order and spelling: fpre, room_live_cf S, the trace in the universe,
   the ledger (with g_most / g_own_ran_out), the footprint [] (the text's `if p =? 0 then [] else ..`), room_live_cf S'.
   A walk takes it as ONE premise `HT_fuzz_free0 : forall fx', crs_free0 (fx := fx') B ARx`, quantified over the float
   state as the callee texts are, placed right after HT_fuzz_free.
   rule 24: proves no function (kind: interim premise statement of the walk of check_reject_clean_starved; reuse search:
   `proof-index check_reject_clean_starved 0x82160`, the internal file index-crcs-Aprime.out, and an internal record
   of that lookup; CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A or lib/B, its
   released rows were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan Proof.v existed for
   check_reject_clean_starved). Written new. This file proves nothing: it STATES.
   Inputs: pin A' asan sha256 1be0f53d96cb9d6c (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1);
   listing lib/A/Listing_prog.v blob 7ed1529926bd + lib/A/PAImg_prog.v blob 505a51ff7d08; kit lib/A/Prog/CrsKitAp.v
   (cold/h-w6u-rep-crsa2-v3 df14c8cd3eb9, blob 03dab244d6e6). No numeral is an address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import CrsKitAp.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
#[local] Notation PA := (PI_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* tfuzz_free_specX at p = 0 (header) *)
Definition crs_free0 : Prop :=
  forall most own,
  forall ly S Hp W regs mem md ch Lam peak cnt fail ran,
  fpre (PA := PA) B ARx STK_fuzz_free ly S Hp W regs mem md ch -> room_live_cf S ->
  In (call_trace ly (pc_free_ra0 (as_code B)) regs ch) (as_universe B) ->
  getr regs 10 = w64 0 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr SEGS W (cfg_at SEGS (pa_sigma AS_fuzz_free) regs mem md)
    (fpostm (PA := PA) B ARx SK STK_fuzz_free [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\
       (S' = S /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
        prh_ledger (PA := PA) B ly' S' Hp' W' mem' Lam peak cnt fail ran most own))).

End f.
End d.
