(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0n.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YP0n.v, with its module paths and module names changed; 967 of its 1043 lines of code are new or changed and 1914 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Cno102B_Base.v; 58 of its 93 lines of code are new or changed and 1008 lines of the source are left out. *)
(* fuzz_preset, image B' (asan-ubsan, harness fix #102: pin sha256 d663f82d7f488d30, twin c90d4fa54d43160b): the
   INTERFACE of check_no_overread's top (row R7-7 of a Theorem Labs lane's internal file PART7-ROWS.md; a Theorem Labs lane,
   family lead a Theorem Labs lane): the composition step cnbt_seq and the segment interfaces the top takes as Section hypotheses
   or cites, in the contract's cuts. Moved here unchanged from lib/B/Prog/Cno102B_Top.v (blob 767ddd7a9e06, same Section
   context, names and implicit arguments) so that a segment file can state its lemma in the top's interface and the top
   can cite it: lib/B/Prog/Cno102B_E9.v proves cnb_seg_end : cnbt_endP and Requires this file, and Cno102B_Top.v Requires
   both.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma; the top's segment interfaces).
   INPUTS: the contract lib/B/Prog/Cno102B_Base.v on the kit's cut (cnb_pre CTX0 D, without DW; the cuts cnb_at_read1 /
   read2 / read3, the exits cnb_ex_pn1 .. cnb_ex_free, cnb_ex_ret); lane CnoB102f's lib/B/Prog/Cno102B_F.v (CB9's start
   cut cnb_at_end).
   THE INTERFACES (each generic in the memory invariant P, the internal file lane-102.md form: srr_inv_call across a call,
   srr_inv_mn where an exit or a callee needs memnorm): cnbt_read1P / cnbt_read2P / cnbt_read3P (CB4 / CB5 / CB6, lane
   CnoB102rR, each with the three exits of its guard), cnbt_endP (CB9, with srr_inv_mn: its exit cnb_ex_ret is the
   m-form post fpostFbm, at wle' SEGS RZ_cf).
   THE FREE / REALLOC MOVE: a free or a realloc of a live block can hide shadow again, so a walk whose run crosses one
   concludes SRr' SEGS RZ_cf (YA0nH.v), not SRr. CB9 starts at cnb_at_end, after the frees: its journal from the entry
   is at wle' SEGS RZ_cf, and the engine's R-form runners carry that relation into the step relation, so cnbt_endP
   concludes SRr' SEGS RZ_cf. cnbt_seq (plain SRr) composes the segments before the first free.
   No numeral. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
(* YK06 is NOT imported: its plain alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
(* the step relation over the re-hide zone (SRr', YA0nH.v) and the fixed zone RZ_cf (YGcfRehidePost.v) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YGcallx YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_Base Cno102B_F.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance prh_room_live_a8.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).

(* one segment after another: the first one's exit cut and P at its memory start the second *)
Lemma cnbt_seq : forall (W : world SEGS) c (R Q : world SEGS -> config -> Prop) (P : (word -> option byte) -> Prop),
  SRr SEGS W c (fun W' c' => R W' c' /\ P (ms_mem (cfg_ms c'))) ->
  (forall W' c', R W' c' -> P (ms_mem (cfg_ms c')) -> SRr SEGS W' c' Q) ->
  SRr SEGS W c Q.
Proof.
intros W c R Q P H1 H2. apply (SRr_bind SEGS W c _ Q H1). intros W' c' _ [HR HP]. exact (H2 W' c' HR HP).
Qed.

Section f.
Variable B : asyms.
(* the walk's allocator relation, the cf instance (CnoB102f's ARcfx, Cno102B_F.v; every segment file's) *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Variables (CTX0 : list (list Z)).

(* CB4 Read1, CNB_READ1 -> the first parse_noting call state, reading 1 skipped, or the free cut (g_own_ran_out set) *)
Definition cnbt_read1P : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0,
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnb_at_read1 (fx := fx) (SK := SK) B ARcfx D fxk ly S Hp W regs mem md k r1 r2 r3 own0 -> P mem ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc CNB_READ1) regs mem md)
    (fun W' c' => (cnb_ex_pn1 (fx := fx) (SK := SK) B ARcfx D W' c' \/
                   cnb_ex_read2 (fx := fx) (SK := SK) B ARcfx D W' c' \/
                   cnb_ex_free (fx := fx) (SK := SK) B ARcfx D W' c') /\ P (ms_mem (cfg_ms c'))).
(* CB5 Read2, CNB_READ2 -> the second call state, reading 2 skipped, or the free cut *)
Definition cnbt_read2P : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1,
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnb_at_read2 (fx := fx) (SK := SK) B ARcfx D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1 ->
  P mem ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc CNB_READ2) regs mem md)
    (fun W' c' => (cnb_ex_pn2 (fx := fx) (SK := SK) B ARcfx D W' c' \/
                   cnb_ex_read3 (fx := fx) (SK := SK) B ARcfx D W' c' \/
                   cnb_ex_free (fx := fx) (SK := SK) B ARcfx D W' c') /\ P (ms_mem (cfg_ms c'))).
(* CB6 Read3, CNB_READ3 -> the third call state, reading 3 skipped (the compare), or the free cut *)
Definition cnbt_read3P : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnb_at_read3 (fx := fx) (SK := SK) B ARcfx D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2
    o1 o2 ->
  P mem ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc CNB_READ3) regs mem md)
    (fun W' c' => (cnb_ex_pn3 (fx := fx) (SK := SK) B ARcfx D W' c' \/
                   cnb_ex_cmp (fx := fx) (SK := SK) B ARcfx D W' c' \/
                   cnb_ex_free (fx := fx) (SK := SK) B ARcfx D W' c') /\ P (ms_mem (cfg_ms c'))).
(* CB9 End, CNB_END (CnoB102f's cut cnb_at_end, after the frees) -> the function's return: set_shadow_f5, the fake
   frame released, the epilogue, a0 = s8 = r; its exit the contract's cnb_ex_ret (the text's post), at SRr' SEGS
   RZ_cf *)
Definition cnbt_endP : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P -> srr_inv_mn SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r ownl,
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnb_at_end (fx := fx) B SK D fxk ly S Hp W regs mem md k Lam peak cnt ran r ownl -> P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc CNB_END) regs mem md)
    (fun W' c' => cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D W' c' /\ P (ms_mem (cfg_ms c'))).

End f.
End d.
