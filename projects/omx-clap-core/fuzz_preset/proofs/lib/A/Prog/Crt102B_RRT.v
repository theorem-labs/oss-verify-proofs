(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Loop_kitQ.v, with its module paths and module names changed; 1634 of its 1673 lines of code are new or changed and 157 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): this row runs at the world-relation
   contract (the internal file WLE-CONTRACT.md): every journal is ajournal_xwR / ajournal_xR at R := YA0nH.wle' SEGS
   YGcfRehidePost.RZ_cf (AJW / AJ below), every step statement is YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf, TAIL / REWR /
   crtb_rtt_call / crtb_at_T / _R2 / _R1 / _M / crtb_rrt conclude SRr', the call rule is YCbqGwild.aj_call_xbF_spR at R
   (round_trip_text's text posts fpostFbm, already at wle'), the branches paj_branchR at R, the live stack at the call
   YGcallStackUp.astack_up_at_xwR, the room YCbqGwild.ajournal_xw_roomR. round_trip_text's new premise
   `(length rp_os <= 4)%nat` is the Section hypothesis HOS4. *)
(* fuzz_preset, row CRT-B-RRT [T2] of FREE-PIECES-102 Part 7a: check_round_trip on IMAGE B'
   (asan-ubsan d663f82d7f488d30, twin c90d4fa54d43160b), segment R1, R2, T: from the cut M (+0x194) through the two
   round_trip_text calls to the cut U (+0x1ec), with the three exits C1 / C2 / C3 into the join J (+0x348).
   Against the contract text tcheck_round_trip_specX (lib/A/PRH_FnCheck.v), citing tround_trip_text_specX at both calls.

   INPUTS OF RECORD (taken by path, as Crt102Glue.v's header):
   - pins: A' asan 1be0f53d96cb9d6c (twin bff8519bbe3ea0e4), B' asan-ubsan d663f82d7f488d30 (twin c90d4fa54d43160b).
   - base: the crt lane head 71a8716672850d3cc31b00bbc497633106293cac (the landing kit cut
     7cdbb61b5fa0 merged into ed827ae6a6ae, with the lane's DW drop), merged on this row's head f4b4f2dba93 (on
     6bb495fd9c56): the glue predicates are Prop Records (read here by projection, built by named literal);
     crt_at_J_B's r = 0 field and its r = 0 arm's ORDERED free list of copy; crt_at_U_B's copy_cap (pj_hdrR form) and
     copy_fo (the kit's pj_set entry premise shape); crt_pos carries the strtod tie and the consumer window; the bridge
     Crt102Glue.crt_copy_cap_of_ncap48. The texts at the cut (PRH_FnCheck.v): round_trip_text's run is KEYED on
     ReaderRes.jr_strtod (no rp_sm binder, no `rp_sm = jr_strtod` premise; so the glue's names are taken at rp_sm :=
     ReaderRes.jr_strtod here), it takes its window prh_cons_from and the wild room `wild_room (as_universe B) []
     (prh_wk F_round_trip_text) (st_depot S)`, its post is BUDGETED (fpostFbm .. (wbudget [] (prh_wk
     F_round_trip_text))) and states `r = 0` (THE r = 1 ARM IS DEAD: C1 and C2 are unreachable), and its copy arm
     states the read-back's block sizes up to permutation, copy's ORDERED free list (FREEORD-COPY) and its
     capacities (CAP, PRH_Reader.pj_ncapR). The A' twin of this file is Crt102Arms.v (the template of this re-cut).
     lib/Reusable/YImgTop.v blob d2a97d3111ce.
   - listing of record: commit d42e123915ae, lib/B/Listing_prog.v 8bcc2c9e7809 and
     lib/B/PAImg_prog.v (PI_prog_B, PL_prog_B); check_round_trip at B_prog_slot 1111 (0x82828 = B_prog_base + CRT_PC_B).
   - build route pins102: the zfb-targets script dc6f8f60073340be, FACTS 8f3e7e1a07f1,
     PAU pau-preset-102.
   - rule 24: re-point of this row's own proof (proof-index check_round_trip / crtb_rrt / crt_at_U_B_copy_fo,
     index v5 2026-10-30T01:54:20Z; the row's saved lookup outputs): crtb_rrt's one
     unreleased hit is this file (commit 584e0622b04e), crt_at_U_B_copy_fo has none.
    Structure only (no premise relocated) from the old-framework donor lib/A/Prog/check_round_trip.v at commit 8fdc81e94c63.

   AT THE RECORD B' INSTANCE: PI_prog_B / PL_prog_B of lib/B/PAImg_prog.v (which builds on the record IMG_TOP_B,
   lib/Reusable/YImgTop.v blob d2a97d3111ce from commit a9548e31002a). The two instance facts
   the walk reads are lemmas here, not hypotheses: crtb_base (pa_val A_TEXT = B_prog_base, by computation) and
   S1ImgB.v's pst_not_ro_B (alloc.c's statics lie in no read-only byte).

   THE SEGMENT LEMMA is crtb_rrt (T1's post at M, with the room position crt_pos Sc (round_trip ReaderRes.jr_strtod
   t) -> the run reaches QF), over the Section hypotheses: LAWS (the engine's allocator laws at ARx), RTT
   (round_trip_text's contract text, at every float state; walked in its own walk), the text's own premises of
   tcheck_round_trip_specX it reads (HPRE .. HFR, the entry wild room HWR0 and the live stack HUP0, verbatim at the
   cut), and the two boundaries it ends in, TAIL (crt_at_J_B at J, the join's segment) and REWR (crt_at_U_B at U, the
   rewrite's segment).
   STATUS (kb round: the glue Crt102Glue.v gives crt_live its budget kb, with its journal at a budget WS and
   `wbudget [] kb WS`, and QF the text's budgeted post at wbudget [] (prh_wk F_check_round_trip)): every lemma is
   Qed. crtb_at_M (M -> QF, given rtt1's post in the form crtb_rtt_Q_k0 and crtb_wild_budget), crtb_at_R1,
   crtb_at_R2, crtb_at_T and crtb_rtt_call are restated at the forced budgets (M and rtt1 at kb 0, rtt2 at kb 32 =
   prh_wk F_round_trip_text, R2 / T / U_B at 64, J_B at 66 = prh_wk F_check_round_trip). crtb_wild_budget is restated
   in the kb form (the twin of Crt102Arms.arms_wild_budget) and crtb_wild_budget_goal discharges it from HWR0; crtb_rrt
   carries the text's post into crtb_rtt_Q_k0 from the cut's own conjuncts (FREEORD-COPY verbatim; CAP's cap
   word, the first conjunct of pj_ncapR's object clause) and closes with crtb_wild_budget_goal. The one budget STEP UP
   is C3 (t not an object, after rtt2): 64 -> 66 by crtb_live_mono (crtb_kb_C3_lt: a real step). round_trip_text's
   last premise at the kit text 4b8f95c0455c, astack_up_x at the callee's sp, is given at both calls from HUP0
   through the journal from the entry (YGcallStackUp.astack_up_at_x, as Crt102Arms.arms_rtt_call).
   C1 / C2 (rtt1 / rtt2 returned 1) are UNREACHABLE by the text's dead r = 1 arm; C3 lands in crt_at_J_B's r = 0 arm,
   the object case in crt_at_U_B. rtt1's post is used in the text's own form (crtb_rtt_Q). The call rule is
   crtb_rtt_call over YCbqGwild.aj_call_xbF_sp, the caller's journal at the live state's budget WS0: round_trip_text
   cited under its request bound RQA_rtt t p <= most (from the text's own RQA_crt t <= most by Crt102Model's
   cm_rqa_rtt0 / 1), at the call's position, with its run events and consumer window from ck_rtt_evs_supply /
   crtb_cons_split.
   COPY'S BLOCKS at the r = 0 boundaries (C3's crt_at_J_B, U's crt_at_U_B): crtb_tblk_perm turns the text's size
   permutation `Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (ttrace t)))` into `Permutation (map (fun b =>
   snd b + cf_head) Db) (tblk t)`: the reader's live set with heads is rd_blocks (ttrace t) (crtb_hlive_lsz), and
   PresetReqAtNoMiss.ttrace_blocks ties that to tblk t.

   THE WORDS (lib/B/Listing_prog.v, slots 1212 .. 1234 and 1265 .. 1266 of B_prog_listing; offsets from the entry):
   M  +0x194 0xb0513 `mv a0, s6` (doc), +0x198 0x593 `li a1, 0`, +0x19c 0xa0613 `mv a2, s4` (&copy),
      +0x1a0 `jal round_trip_text` (RTT1).
   R1 +0x1a4 0x50663 `beqz a0, +0x1b0`; +0x1a8 0x100a93 `li s5, 1`, +0x1ac 0x19c0006f `j +0x348` (C1: J, r = 1);
      +0x1b0 0x100593 `li a1, 1`, +0x1b4 0x100a93 `li s5, 1`, +0x1b8 0xb0513 `mv a0, s6`, +0x1bc 0x613 `li a2, 0`,
      +0x1c0 `jal round_trip_text` (RTT2).
   R2 +0x1c4 0x18051263 `bnez a0, +0x348` (C2: J, r = s5 = 1).
   T  +0x1c8 0x7b7513 `andi a0, s6, 7`, +0x1cc 0x64051263 `bnez a0, +0x810` (UBSan's alignment trap),
      +0x1d0 0x3b5593 `srli a1, s6, 3`, +0x1d4 0x1b585b3 `add a1, a1, s11`, +0x1d8 0x58583 `lb a1, 0(a1)`,
      +0x1dc 0x62059c63 `bnez a1, +0x814` (ASan's report), +0x1e0 0xb2503 `lw a0, 0(s6)` (doc->type),
      +0x1e4 0x600593 `li a1, 6`, +0x1e8 0x8b51063 `bne a0, a1, +0x268`.
   U  +0x1ec 0x90223 `sb zero, 4(s2)`: the continuation (crt_at_U_B).
   C3 +0x268 0xa93 `li s5, 0`, +0x26c 0xdc0006f `j +0x348` (J, r = 0).

   NUMERALS. DERIVED: the cut offsets (Crt102Img's CRT_*_OFF_B, 4 * the slot inside the function), the realigned sp
   (CRT_sp1), shadow_addr. LENGTH: 224 (CRT_OFF_COPY), 56 (struct pj), 4 (the type word), 8 / 16 (words, alignment),
   512 (fs_frame_bytes 3), 240 (pi_frame), 2 ^ 44 / 2 ^ 47 / 2 ^ 64 (shadow, stack, word bounds). WORD: 6
   (PJ_OBJECT), 0 / 1 (the pretty flag, the return values). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcfTreeVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetFreeFo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
(* kb round: Crt102Kit's image-free AJW runners (crt_run_xw_inv / crt_run_to_xw_inv), used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Kit.
(* the re-hiding move's world relation and step relation (YA0nH), its step lemmas (YSRrG), the
   zone (YGcfRehidePost.RZ_cf), used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* PART 1, image-free. The tree predicates (a represented tree is freeable by pj_free to its depth, and deeper),
   the header word of a node, the float-register keep, a word read back, and the writer's tree visibility at any
   ARx state: transcribed from Crt102Arms (lib/A/Prog/Crt102Arms.v arms_fshape_mono .. crt_tree_vis_keep,
   itself from an earlier walk's H5CrtS7.v; an A' file whose Section fixes image A', so not Required here); the same
   bodies over PRH_Reader.v's R predicates. *)
Section rd.
Variable segs : list Segment.

Lemma crtb_fshape_mono : forall m lblk (Pi Pi' : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop) p D,
  (forall ks kids keys n Di, Pi ks kids keys n Di -> Pi' ks kids keys n Di) ->
  pj_fshapeR segs m lblk Pi p D -> pj_fshapeR segs m lblk Pi' p D.
Proof.
intros m lblk Pi Pi' p D H (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6).
split; [exact Hn|]. split; [exact Ha|]. exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. exact (H _ _ _ _ _ H6).
Qed.
Lemma crtb_pf_items_mono : forall m lblk (P Q : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall a D1, P a D1 -> Q a D1) -> pf_itemsR segs m lblk P ks a ka n D -> pf_itemsR segs m lblk Q ks a ka n D.
Proof.
intros m lblk P Q ks n. induction n as [|n IH]; intros a ka D H Hp; cbn [pf_itemsR] in *; [exact Hp|].
destruct Hp as (Dk & D1 & D2 & E & Hk & HP & HR). exists Dk, D1, D2.
split; [exact E|]. split; [exact Hk|]. split; [exact (H a D1 HP) | exact (IH (a + 56) (ka + 8) D2 H HR)].
Qed.
Lemma crtb_fd_succ : forall m lblk d p D, pj_fdR segs m lblk d p D -> pj_fdR segs m lblk (Datatypes.S d) p D.
Proof.
intros m lblk d. induction d as [|d IH]; intros p D H; cbn [pj_fdR] in H |- *.
- eapply (crtb_fshape_mono m lblk); [|exact H]. intros ks kids keys n Di (En & EDi). cbv beta. subst n Di. exact eq_refl.
- eapply (crtb_fshape_mono m lblk); [|exact H]. intros ks kids keys n Di Hi. cbv beta in Hi |- *.
  apply (crtb_pf_items_mono m lblk (pj_fdR segs m lblk d)); [|exact Hi]. intros a D1 H1. exact (IH a D1 H1).
Qed.
Lemma crtb_fd_mono : forall m lblk d d' p D, (d <= d')%nat -> pj_fdR segs m lblk d p D -> pj_fdR segs m lblk d' p D.
Proof. intros m lblk d d' p D Hle. induction Hle as [|d' Hle IH]; intros H; [exact H|]. apply crtb_fd_succ. apply IH. exact H. Qed.
Lemma crtb_items_pf : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, In u l -> P a u D1 -> Q a D1) ->
  pj_itemsR P a l D -> pf_itemsR segs m lblk Q false a ka (length l) D.
Proof.
intros m lblk P Q l. induction l as [|u r IH]; intros a ka D H Hl; cbn [pj_itemsR pf_itemsR length] in *; [exact Hl|].
destruct Hl as (D1 & D2 & E & HP & HR). exists [], D1, D2.
split; [exact E|]. split; [exact eq_refl|]. split; [apply (H a u D1); [left; reflexivity | exact HP]|].
apply IH; [intros a' v D3 Hv HP3; apply (H a' v D3); [right; exact Hv | exact HP3] | exact HR].
Qed.
Lemma crtb_mems_pf : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, (exists nm, In (nm, u) l) -> P a u D1 -> Q a D1) ->
  pj_memsR segs m lblk P a ka l D -> pf_itemsR segs m lblk Q true a ka (length l) D.
Proof.
intros m lblk P Q l. induction l as [|[nm u] r IH]; intros a ka D H Hl; cbn [pj_memsR pf_itemsR length] in *; [exact Hl|].
destruct Hl as (x & k & D1 & D2 & E & Hx & (Hb & _) & HP & HR). exists [(x, k)], D1, D2.
split; [exact E|].
split; [unfold pj_keyR; exists x; split; [exact Hx | right; exists k; split; [exact Hb | reflexivity]]|].
split; [apply (H a u D1); [exists nm; left; reflexivity | exact HP]|].
apply IH; [intros a' v D3 (nm' & Hv) HP3; apply (H a' v D3); [exists nm'; right; exact Hv | exact HP3] | exact HR].
Qed.
Lemma crtb_nodeR_fd : forall t m lblk p D, pj_nodeR segs m lblk p t D -> pj_fdR segs m lblk (PjTree.depth t) p D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; intros m lblk p D H;
  cbn [pj_nodeR] in H.
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JNull), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JFalse), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JTrue), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag (PjTree.JNum txt bits)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
  split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag (PjTree.JStr s)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
  split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  remember (PjTree.depth (PjTree.JArr items)) as dd eqn:Edd. destruct dd as [|d']; [cbn [PjTree.depth] in Edd; discriminate|].
  cbn [pj_fdR]. unfold pj_fshapeR. split; [exact Hn|]. split; [exact Ha|].
  assert (HI : pf_itemsR segs m lblk (pj_fdR segs m lblk d') false kids keys (Z.to_nat n) Di).
  { rewrite En, Nat2Z.id. apply (crtb_items_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
    intros a u D1 Hu HP. rewrite Forall_forall in IH. apply (crtb_fd_mono m lblk (PjTree.depth u)); [|exact (IH u Hu m lblk a D1 HP)].
    pose proof (PjTree.depth_item items u Hu). lia. }
  destruct Hcap as [(Hc0 & Hk0)|(Hc0 & Hl)].
  + subst cap. exists (PjTree.tag (PjTree.JArr items)), num, str, kids, keys, n, 0, false, [], [], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|]. split; [left; split; [exact Ek | split; reflexivity]|].
    split; [subst D; cbn; apply Permutation_refl|]. exact HI.
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    exists (PjTree.tag (PjTree.JArr items)), num, str, kids, keys, n, cap, false, [], [(kids, 56 * cap)], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [right; exists (56 * cap); split; [exact Hl | split; [lia | reflexivity]]|].
    split; [left; split; [exact Ek | split; reflexivity]|]. split; [subst D; cbn [app]; apply Permutation_refl|]. exact HI.
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
  remember (PjTree.depth (PjTree.JObj members)) as dd eqn:Edd. destruct dd as [|d']; [cbn [PjTree.depth] in Edd; discriminate|].
  cbn [pj_fdR]. unfold pj_fshapeR. split; [exact Hn|]. split; [exact Ha|].
  destruct Hcap as [(Hc0 & Hk0 & Hy0)|(Hc0 & L0 & L1)].
  + subst cap. destruct members as [|mb members]; cbn [length] in En; [|lia]. cbn [pj_memsR] in Hi.
    exists (PjTree.tag (PjTree.JObj [])), num, str, kids, keys, n, 0, false, [], [], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|]. split; [left; split; [exact Hy0 | split; reflexivity]|].
    split; [subst D; cbn; apply Permutation_refl|]. cbv beta. replace (Z.to_nat n) with 0%nat by lia. exact Hi.
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    exists (PjTree.tag (PjTree.JObj members)), num, str, kids, keys, n, cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [right; exists (56 * cap); split; [exact L0 | split; [lia | reflexivity]]|].
    split; [right; split; [reflexivity | exists (8 * cap); split; [exact L1 | split; [lia | reflexivity]]]|].
    split; [subst D; cbn [app]; apply Permutation_refl|].
    cbv beta. rewrite En, Nat2Z.id. apply (crtb_mems_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
    intros a u D1 (nm & Hu) HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
    apply (crtb_fd_mono m lblk (PjTree.depth u)); [|exact (IH m lblk a D1 HP)]. pose proof (PjTree.depth_member members nm u Hu). lia.
Qed.
(* the header word of a node is its tag (pj_nodeR's pj_hdrR clause) *)
Lemma crtb_node_hdr : forall m lblk p t D, pj_nodeR segs m lblk p t D -> rd_u32 segs m p (PjTree.tag t).
Proof.
intros m lblk p t D H.
destruct t; cbn [pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & n & cap & (_ & Hty & _) & _);
exact Hty.
Qed.
(* the block predicate of a tree may grow: a tree over lblk is a tree over any lblk' containing it (a callee that
   keeps the ledger up to permutation keeps every tree over it) *)
Lemma crtb_itemsR_mono : forall (P Q : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D,
  (forall a u D1, In u l -> P a u D1 -> Q a u D1) -> pj_itemsR P a l D -> pj_itemsR Q a l D.
Proof.
intros P Q l. induction l as [|u r IH]; intros a D H Hl; cbn [pj_itemsR] in *; [exact Hl|].
destruct Hl as (D1 & D2 & E & HP & HR). exists D1, D2.
split; [exact E|]. split; [apply H; [left; reflexivity | exact HP]|].
apply IH; [intros a' v D3 Hv HP3; apply H; [right; exact Hv | exact HP3] | exact HR].
Qed.
Lemma crtb_memsR_mono : forall m lblk lblk' (P Q : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  (forall a k, lblk a k -> lblk' a k) ->
  (forall a u D1, (exists nm, In (nm, u) l) -> P a u D1 -> Q a u D1) ->
  pj_memsR segs m lblk P a ka l D -> pj_memsR segs m lblk' Q a ka l D.
Proof.
intros m lblk lblk' P Q l. induction l as [|[nm u] r IH]; intros a ka D HL H Hl; cbn [pj_memsR] in *; [exact Hl|].
destruct Hl as (x0 & k & D1 & D2 & E & Hx & (Hb & Hc) & HP & HR). exists x0, k, D1, D2.
split; [exact E|]. split; [exact Hx|]. split; [split; [exact (HL _ _ Hb) | exact Hc]|].
split; [apply H; [exists nm; left; reflexivity | exact HP]|].
apply IH; [exact HL | intros a' v D3 (nm' & Hv) HP3; apply H; [exists nm'; right; exact Hv | exact HP3] | exact HR].
Qed.
Lemma crtb_nodeR_lblk : forall t m lblk lblk' p D, (forall a k, lblk a k -> lblk' a k) ->
  pj_nodeR segs m lblk p t D -> pj_nodeR segs m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; intros m lblk lblk' p D HL H;
  cbn [pj_nodeR] in H |- *.
- exact H.
- exact H.
- exact H.
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & k & (Hb & Hc) & ED).
  split; [exact Hn|]. split; [exact Ha|]. exists num, str, kids, keys, n, cap.
  split; [exact Hh|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [split; [exact (HL _ _ Hb) | exact Hc] | exact ED].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E2 & E3 & E4 & E5 & k & (Hb & Hc) & ED).
  split; [exact Hn|]. split; [exact Ha|]. exists num, str, kids, keys, n, cap.
  split; [exact Hh|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [split; [exact (HL _ _ Hb) | exact Hc] | exact ED].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Hn|]. split; [exact Ha|]. exists num, str, kids, keys, n, cap.
  split; [exact Hh|]. split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split; [destruct Hcap as [Hcap | (Hcap & Hk)]; [left; exact Hcap | right; split; [exact Hcap | exact (HL _ _ Hk)]]|].
  exists Di. split; [exact ED|].
  apply (crtb_itemsR_mono (pj_nodeR segs m lblk)); [|exact Hi].
  intros a u D1 Hu HP. rewrite Forall_forall in IH. exact (IH u Hu m lblk lblk' a D1 HL HP).
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Hn|]. split; [exact Ha|]. exists num, str, kids, keys, n, cap.
  split; [exact Hh|]. split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split; [destruct Hcap as [Hcap | (Hcap & Hk & Hy)];
    [left; exact Hcap | right; split; [exact Hcap | split; [exact (HL _ _ Hk) | exact (HL _ _ Hy)]]]|].
  exists Di. split; [exact ED|].
  apply (crtb_memsR_mono m lblk lblk' (pj_nodeR segs m lblk)); [exact HL | |exact Hi].
  intros a u D1 (nm & Hu) HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
  exact (IH m lblk lblk' a D1 HL HP).
Qed.
End rd.

(* the callee-saved float registers kept twice are kept *)
Lemma crtb_fregs_trans : forall f1 f2 f3, fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.

(* a word read back through the view *)
Lemma crtb_rdword_of_val_mem : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* ---- the model's event lists (PresetReqAt.v 379c33e9e482, PRH_FnCheck.v's ck_rtt_evs); duplicates of Crt102Arms'
   arms_ck_rtt_nz / arms_rt_tail / arms_tail_nobj / arms_tree_J_nobj (image-free; the A' file is not Required here) *)
(* round_trip_text's list with a copy is the model's rt_text; without one it adds back's free *)
Lemma crtb_ck_rtt_nz : forall sm t p c, c <> 0 -> ck_rtt_evs sm t p c = PresetReqAt.rt_text sm t p.
Proof. intros sm t p c Hc. unfold ck_rtt_evs. rewrite (proj2 (Z.eqb_neq c 0) Hc). apply app_nil_r. Qed.
(* round_trip is the first call's list, the second call's (back's free included), and the tail: the rewrite and
   pj_free (&copy) for an object, pj_free (&copy) otherwise - Crt102Glue's crt_evs_U / crt_evs_J *)
Lemma crtb_rt_tail : forall sm t, PresetReqAt.round_trip sm t =
  (PresetReqAt.rt_text sm t false ++ ck_rtt_evs sm t true 0) ++
  match t with PjTree.JObj ms => crt_evs_U (rp_sm := sm) ms | _ => crt_evs_J (t := t) end.
Proof.
intros sm t. unfold PresetReqAt.round_trip, ck_rtt_evs, crt_evs_U, crt_evs_J. rewrite Z.eqb_refl.
rewrite <- !app_assoc. destruct t; reflexivity.
Qed.
Lemma crtb_tail_nobj : forall sm t, (forall ms, t <> PjTree.JObj ms) ->
  match t with PjTree.JObj ms => crt_evs_U (rp_sm := sm) ms | _ => crt_evs_J (t := t) end = crt_evs_J (t := t).
Proof. intros sm t Hn. destruct t; try reflexivity. exfalso. exact (Hn members eq_refl). Qed.
(* the tree copy holds at J for a non-object is t itself (Crt102Glue's crt_tree_J) *)
Lemma crtb_tree_J_nobj : forall t, (forall ms, t <> PjTree.JObj ms) -> crt_tree_J (t := t) = t.
Proof. intros t Hn. destruct t; try reflexivity. exfalso. exact (Hn members eq_refl). Qed.

(* ---- the read-back's blocks against tblk UP TO PERMUTATION, from the sizes round_trip_text's r = 0 arm states
   (`Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (ttrace t)))`): with the allocator's head the reader's
   live set is exactly rd_blocks of the trace (crtb_hlive_lsz, by the event-for-event match of lsz_ev and hstep), and
   PresetReqAtNoMiss.ttrace_blocks (f949715d7a12:794) ties that to tblk t up to permutation. This is
   crt_at_J_B's r = 0 block field and crt_at_U_B_copy_tblk. ---- *)
Lemma crtb_rm1_map : forall k s,
  PresetReqAt.rm1 (Z.of_nat k + PresetReqAt.HEAD) (map (fun n => Z.of_nat n + PresetReqAt.HEAD) s) =
  map (fun n => Z.of_nat n + PresetReqAt.HEAD) (ReaderRes.rm1n k s).
Proof.
intros k s. induction s as [|y s IH]; cbn [PresetReqAt.rm1 ReaderRes.rm1n map]; [reflexivity|].
destruct (Nat.eqb_spec y k) as [->|Hne].
- rewrite Z.eqb_refl. reflexivity.
- rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbn [map]. rewrite IH. reflexivity.
Qed.
Lemma crtb_hlive_lsz : forall tr s,
  PresetReqAt.hlive_from (map (fun n => Z.of_nat n + PresetReqAt.HEAD) s) (PresetReqAt.rd_hevs tr) =
  map (fun n => Z.of_nat n + PresetReqAt.HEAD) (fold_left ReaderRes.lsz_ev tr s).
Proof.
induction tr as [|e tr IH]; intros s; [reflexivity|].
unfold PresetReqAt.rd_hevs, PresetReqAt.hlive_from in *. cbn [flat_map fold_left].
rewrite fold_left_app. rewrite <- IH. f_equal.
destruct e as [m|[|j] m|m|m]; cbn [PresetReqAt.rd_hev ReaderRes.lsz_ev fold_left PresetReqAt.hstep map];
  try reflexivity.
- f_equal. exact (crtb_rm1_map (Datatypes.S j) s).
- exact (crtb_rm1_map m s).
Qed.
Lemma crtb_tblk_perm : forall (Db : list (Z * Z)) t,
  @cf_head CfParams_preset = PresetReqAt.HEAD ->
  Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) ->
  Permutation (map (fun b => snd b + @cf_head CfParams_preset) Db) (PresetReqAtNoMiss.tblk t).
Proof.
intros Db t Eh HP. rewrite Eh.
apply (Permutation_trans (l' := PresetReqAt.rd_blocks (PjRoundTrip.ttrace t))); [|apply PresetReqAtNoMiss.ttrace_blocks].
unfold PresetReqAt.rd_blocks, PresetReqAt.hlive, ReaderRes.lsz.
change (@nil Z) with (map (fun n => Z.of_nat n + PresetReqAt.HEAD) (@nil nat)).
rewrite crtb_hlive_lsz.
replace (map (fun b => snd b + PresetReqAt.HEAD) Db) with (map (fun z => z + PresetReqAt.HEAD) (map snd Db))
  by (rewrite map_map; reflexivity).
replace (map (fun n => Z.of_nat n + PresetReqAt.HEAD) (fold_left ReaderRes.lsz_ev (PjRoundTrip.ttrace t) []))
  with (map (fun z => z + PresetReqAt.HEAD) (map Z.of_nat (fold_left ReaderRes.lsz_ev (PjRoundTrip.ttrace t) [])))
  by (rewrite map_map; reflexivity).
apply Permutation_map. exact HP.
Qed.

(* the writer's tree visibility at any ARx state, per harness block the ledger lists (the walk's ruling:
   derivable, no lane hypothesis) *)
Section tv. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {PI : PrhImg}.
#[local] Existing Instance CfParams_preset.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.

Lemma crtb_tree_vis_keep : forall ly S Hp W mem md Lamc peakc cntc failc ranc mostc ownc Dt,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lamc peakc cntc failc ranc mostc ownc ->
  (forall bk, In bk Dt -> In bk Lamc) ->
  (forall a k, In (a, k) Dt -> 4096 <= a /\ 0 <= k < 2 ^ 32 /\ (a + k + 7) / 8 * 8 <= YM05.alloc_ceiling /\
     amem_range a ((a + k + 7) / 8 * 8 - a)) ->
  PRH_FnWriter.prhWriter_tree_vis W mem Dt.
Proof.
intros ly S Hp W mem md Lamc peakc cntc failc ranc mostc ownc Dt HAR HL HDt HP a k Hin.
destruct (HP a k Hin) as (H4096 & Hk & Hceil & Hamr).
pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly S Hp W mem Lamc peakc cntc failc ranc mostc ownc HL)
  (a, k) (HDt _ Hin))
  as (Hk0 & Hab & Hhp & H16 & Hhd).
cbn [fst snd] in Hk0, Hab, Hhp, H16.
assert (Hh0 : @cf_head CfParams_preset = 16) by reflexivity.
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & _ & _ & Hpres & _).
assert (Hrq : req_size (k + cf_head) = k + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
destruct (alx_hshadow segs B ARx LAWS ly S Hp W mem md _ _ HAR Hab Hhp) as [Hbs Hhull].
rewrite Hrq in Hbs, Hhull, Hpres. replace (a - cf_head + cf_head) with a in Hbs, Hhull by lia.
replace (k + cf_head - cf_head) with k in Hbs, Hhull by lia.
split; [exact H4096|]. split; [exact Hk|]. split; [exact Hceil|]. split; [exact Hamr|].
split; [exact (block_shadow_range (aview segs (w_H W) mem) SHADOW_OFF a k a k Hbs ltac:(lia) ltac:(lia))|].
split; [intros Hkp; apply Hhull; lia|].
intros x Hx. destruct (Z_lt_le_dec x (a + k)) as [Hlt|Hge].
- destruct (proj1 (Hpres x ltac:(lia))) as (Hh & bb & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
- apply (alx_blocks_tail segs B ARx LAWS ly S Hp W mem md _ _ x HAR Hab). rewrite Hrq.
  replace (a - cf_head + (k + cf_head)) with (a + k) by lia. lia.
Qed.
End tv.

(* ======================================================================================================== *)
(* PART 2, IMAGE B' at the record instance PI_prog_B *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
Context {SK : YI16.sink_head} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_B.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
(* S10Env's TE / ts_* take {L} {PA : PAImg L} with L fixed by no argument; A's PI_prog_A is also a global instance
   here (through Crt102Img), so the B' record instance is made the first choice inside this section *)
#[local] Existing Instance PI_prog_B | 0.
#[local] Existing Instance PL_prog_B | 0.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).
#[local] Notation STKR := (@STK_round_trip_text prh_img_B).

(* the instance's text base is the listing's (lib/B/PAImg_prog.v:379-380), by computation *)
Lemma crtb_base : BASE = B_prog_base.
Proof. vm_compute. reflexivity. Qed.

(* ---- the B' image facts this segment reads (Crt102Img.v's B' tables, by computation) ---- *)
(* the stack budget of round_trip_text called at the realigned sp: pi_frame is 240 (crt_frame_B) and
   STK_round_trip_text + pi_frame <= STK_check_round_trip (crt_stk_B) *)
Lemma crtb_stk : 0 <= STKR /\ STKR + 240 <= STKC.
Proof.
pose proof crt_stk_B as (_ & _ & _ & H & _). pose proof crt_stk_nonneg_B as (_ & H0 & _).
pose proof crt_frame_B as (_ & _ & _ & _ & Hf). rewrite Hf in H. unfold CRT_FRAME, CRT_ALIGN in H. lia.
Qed.
Lemma crtb_fp : @pi_fp prh_img_B F_check_round_trip = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crtb_rets : @pi_call_rets prh_img_B F_check_round_trip F_round_trip_text =
  [BASE + (CRT_PC_B + CRT_R1_OFF_B); BASE + (CRT_PC_B + CRT_R2_OFF_B)].
Proof. rewrite crtb_base. exact (proj1 crt_img_B). Qed.
(* the return sites of the two calls: text addresses, below the ceiling, the listed call returns *)
Lemma crtb_ret : forall off, off = CRT_R1_OFF_B \/ off = CRT_R2_OFF_B ->
  4096 <= BASE + (CRT_PC_B + off) < 2 ^ 31 /\ (CRT_PC_B + off) mod 2 = 0 /\ 0 <= CRT_PC_B + off < 2 ^ 40 /\
  In (BASE + (CRT_PC_B + off)) (@pi_call_rets prh_img_B F_check_round_trip F_round_trip_text).
Proof.
intros off [-> | ->]; rewrite crtb_rets, crtb_base;
  (split; [split; vm_compute; first [discriminate | reflexivity]|]);
  (split; [vm_compute; reflexivity|]); (split; [split; vm_compute; first [discriminate | reflexivity]|]).
- left. reflexivity.
- right. left. reflexivity.
Qed.

(* a context's one-element prefix is a context (prh_ctx is prefix-closed by its definition) *)
Lemma crtb_ctx_head : forall CTX0 F r rest, prh_ctx (PI := prh_img_B) CTX0 F (r :: rest) -> prh_ctx (PI := prh_img_B) CTX0 F [r].
Proof.
intros CTX0 F r rest (c & j & HR & E). exists c, 1%nat. split; [exact HR|].
destruct j as [|j]; [discriminate E|]. destruct c as [|c0 c]; [discriminate E|]. cbn [firstn] in E |- *.
injection E as E1 _. rewrite E1. reflexivity.
Qed.

(* a frame-pointer chain survives a memory change that keeps every word at or above lo (H2H5's H5CrtS1.v
   crt_fpchain_keep, as Crt102Arms' arms_fpchain_keep) *)
Lemma crtb_fpchain_keep : forall (r1 r2 : reader) lo top ch bp,
  (forall a, lo <= a -> a < top -> rdword r2 a = rdword r1 a) ->
  lo + 16 <= bp -> bp <= top ->
  fpchain (rdword r1) bp top ch -> fpchain (rdword r2) bp top ch.
Proof.
intros r1 r2 lo top ch. induction ch as [|[[fp ra] nfp] ch IH]; intros bp Hkeep Hbp Hbt H.
- cbn [fpchain] in *. destruct H as (r & Hr & Hb). exists r. rewrite (Hkeep (bp - 8)) by lia. auto.
- cbn [fpchain] in *. destruct H as (E1 & E2 & E3 & E4 & E5 & E6).
  split; [exact E1|]. split; [exact E2|].
  split; [rewrite (Hkeep (fp - 8)) by lia; exact E3|].
  split; [rewrite (Hkeep (fp - 16)) by lia; exact E4|].
  split; [exact E5|].
  destruct (bad_next fp top nfp) eqn:Eb; [exact E6|].
  unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb1 _].
  apply orb_false_iff in Eb1 as [Eb11 Eb12].
  apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12.
  apply (IH nfp Hkeep); [lia | lia | exact E6].
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the world relation of every journal below (the glue's crt_live_journal's and QF's) *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the journal at a wild-trace budget WS (YCbqG.v ajournal_xwR at RZW; AJ is it at WS = []) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).
(* the allocator laws at hl = cf_head (the engine fold's 18 fields; projections by name only) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Variable CTX0 : list (list Z).
(* round_trip_text's text (the contract text, lib/A/PRH_FnCheck.v at the landing cut 71a8716672:1172-1301; walked in
   its own walk), at ANY float state: rtt2 is entered at the float state rtt1 returned in (aj_call_xbF_sp's fx'), so
   the text is taken at every fxk *)
Hypothesis RTT : forall fxk : YK11.FPState,
  @tround_trip_text_specX fxk rc ci CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK CTX0.

Section g.
(* ---- the entry: tcheck_round_trip_specX's binders and the premises this segment uses (each is the text's own) ---- *)
Variables (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (doc : Z) (t : PjTree.jv) (D : list (Z * Z))
  (x : list Z) (Lam : list (Z * Z)) (peak cnt ran most : Z).
#[local] Notation sp0 := (spZ regs).
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HMN : YAkMemnorm.memnorm SEGS mem.
Hypothesis HCL : prh_univ_closure B CTX0.
Hypothesis HCTX : prh_ctx CTX0 F_check_round_trip (raZ regs :: spine ch).
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
Hypothesis HREAD : ck_read x = Some t.
Hypothesis HLENX : Z.of_nat (length x) <= 3 * 2 ^ 20.
Hypothesis HWL0 : PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x).
Hypothesis HWL1 : PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54.
Hypothesis HCNT : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis HRAN : ran = 0.
Hypothesis HRQA : RQA_crt t <= most.
Hypothesis HLIVE : blocks_bytes S + LIVE_check_round_trip t <= LIVE_MAX.
Hypothesis HRQ : RQ_crt t + cf_head < cf_malloc_max.
Hypothesis HFR : Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_round_trip.
(* the text's wild room at entry (PRH_FnCheck.v:1366, kb round): 66 = prh_wk F_check_round_trip fresh wild slots, of
   which each round_trip_text call takes prh_wk F_round_trip_text = 32; read only by crtb_wild_budget_goal *)
Hypothesis HWR0 : YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_round_trip) (st_depot S).
(* round_trip_text's text asks `(length rp_os <= 4)%nat` (its run has at most 4 calls, DRAFT; PRH_FnCheck.v
   tround_trip_text_specX); the callee's rp_os is this walk's. check_round_trip's own text premise (PRH_FnCheck.v:2363)
   gives it at the top *)
Hypothesis HOS4 : (length rp_os <= 4)%nat.
(* the live real stack above the entry sp (the text's last premise at the 4b8f95c0455c kit text, PRH_FnCheck.v:1390,
   unguarded); read only at the round_trip_text calls (crtb_rtt_call), whose text takes it at the callee's sp *)
Hypothesis HUP0 : YGcallStackUp.astack_up_x SEGS ly W (spZ regs) mem.

(* the glue's names at this walk's binders *)
#[local] Notation LIVE := (crt_live (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
  (B := B) (ARx := ARx)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (most := most)).
#[local] Notation ATJ := (crt_at_J_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := ReaderRes.jr_strtod) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i)
  (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation ATU := (crt_at_U_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := ReaderRes.jr_strtod) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i)
  (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation QFF := (QF (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := ReaderRes.jr_strtod) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i)
  (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation CPOS := (crt_pos (rp_sm := ReaderRes.jr_strtod) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i)
  (rp_H0 := rp_H0) (t := t)).
#[local] Notation EVSJ := (crt_evs_J (t := t)).
#[local] Notation EVSU := (crt_evs_U (rp_sm := ReaderRes.jr_strtod)).
#[local] Notation CFG := (crt_cfg (rc := rc) (L := B_prog_listing) (PA := PA) (CRT_PC := CRT_PC_B)).
#[local] Notation DREGS := (crt_dregs_B (regs := regs) (doc := doc)).
#[local] Notation SAVED := (crt_saved (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs)).
#[local] Notation SP1 := (CRT_sp1 (regs := regs)).
#[local] Notation COPYZ := (crt_copy_zero (rc := rc) (L := B_prog_listing) (PA := PA)).
#[local] Notation COPYT := (crt_copy_tree (rc := rc) (L := B_prog_listing) (PA := PA)).

(* ---- the two boundaries this segment ends in: the join J (+0x348) and the head of the inlined rewrite U
   (+0x1ec), each the next segment's lemma (Crt102Glue.v's crt_at_J_B / crt_at_U_B, frozen) ---- *)
Hypothesis TAIL : forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  ATJ fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_J_OFF_B rg memc mdc) QFF.
Hypothesis REWR : forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms,
  ATU fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_U_OFF_B rg memc mdc) QFF.

(* ---- the realigned sp: 224 or 240 bytes below the entry sp, 32-aligned ---- *)
Lemma crtb_sp1 : SP1 mod 32 = 0 /\ sp0 - 240 <= SP1 <= sp0 - 224 /\ 0 <= SP1.
Proof.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO & Hhi & Hrac & HFZ0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof crtb_stk as (S1 & S2).
unfold CRT_sp1, CRT_FRAME, CRT_ALIGN. pose proof (Z.mul_div_le (sp0 - 224) 32 ltac:(lia)).
pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)). pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)).
assert ((sp0 - 224) mod 32 = 0 \/ (sp0 - 224) mod 32 = 16).
{ apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. lia. }
split; [apply Z.mod_mul; lia|]. split; [lia|]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia.
Qed.

(* ---- the document's home is a live fake frame of the entry, so its 56 bytes stay addressable at every state the
   journal from the entry reaches (FP = []: the frame clause keeps the frame's shadow) ---- *)
Lemma crtb_home_keep : forall own lyc Sc Hpc Wc memc mdc kj WS,
  AJW STKC sp0 [] ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kj WS -> ck_obj_home lyc Sc Wc memc doc.
Proof.
intros own lyc Sc Hpc Wc memc mdc kj WS HJ.
pose proof HPRE as ((HAR & _ & _ & _ & _ & _ & _ & _ & _) & _ & _ & _ & _).
pose proof HTREE as (_ & _ & _ & Hd8 & (cid & pos & Hfin & Hfa1 & Hfa2) & HRA).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & F4 & _).
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR Hly) as (_ & Efa & _).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfin) as (F32 & _).
split; [exact Hd8|]. split.
- exists cid, pos. rewrite Efa. split; [rewrite Hfrs; apply in_or_app; right; exact Hfin|]. split; lia.
- intros a Ha. destruct (HRA a Ha) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr. apply (F4 cid pos); [exact Hfin | right | apply inFP_nil].
  unfold in_zr, shadow_addr. cbn [fst snd].
  assert (E8 : (frame_addr ly cid pos + fs_frame_bytes cid) / 8 = frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8).
  { apply Z.mod_divide in F32; [|lia]. destruct F32 as [q Hq]. rewrite Hq.
    replace (q * 32 + fs_frame_bytes cid) with (fs_frame_bytes cid + (4 * q) * 8) by lia. rewrite Z.div_add by lia.
    replace (q * 32) with ((4 * q) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (Hd : (doc + 56) / 8 = doc / 8 + 7).
  { apply Z.mod_divide in Hd8; [|lia]. destruct Hd8 as [q Hq]. rewrite Hq.
    replace (q * 8 + 56) with ((q + 7) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
  pose proof (Z.div_le_mono (frame_addr ly cid pos) a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono a (doc + 55) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (doc + 56) (frame_addr ly cid pos + fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)).
  assert ((doc + 55) / 8 = doc / 8 + 6).
  { apply Z.mod_divide in Hd8; [|lia]. destruct Hd8 as [q Hq]. rewrite Hq.
    replace (q * 8 + 55) with (7 + (q + 6) * 8) by lia. rewrite Z.div_add by lia. rewrite Z.div_mul by lia. cbn. lia. }
  lia.
Qed.

(* ---- the document's tree as round_trip_text asks it (ck_tree_ok) at any live state ---- *)
Lemma crtb_tree_ok : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kbg,
  LIVE kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc -> ck_tree_ok lyc Sc Lamc Wc memc doc t D.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kbg HL.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_doc HSD) as HND.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HTREE as (_ & _ & HTV & _).
split; [exact HND|]. split; [exact HDL|]. split; [|exact (crtb_home_keep _ _ _ _ _ _ _ _ _ HJ)].
apply (crtb_tree_vis_keep B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc SIZE_MAXZ ranc most ownc D (proj1 HJ) HLED
  HDL).
intros a k Hin. destruct (HTV a k Hin) as (H1 & H2 & H3 & H4 & _). auto.
Qed.

(* ---- the frame-pointer chain at a call made at the realigned sp with s0 = the entry sp ---- *)
Lemma crtb_chain : forall own lyc Sc Hpc Wc memc mdc kj WS,
  AJW STKC sp0 [] ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kj WS -> SAVED Wc memc ->
  exists ch1, achain lyc (aview SEGS (w_H Wc) memc) SP1 sp0 ch1 /\
    (ch1 = [] \/ ch1 = (sp0, raZ regs, s0Z regs) :: ch).
Proof.
intros own lyc Sc Hpc Wc memc mdc kj WS HJ HSV.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO & Hhi & Hrac & HFZ0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
destruct crtb_sp1 as (Hs32 & Hs1 & Hs0).
assert (H8 : sp0 mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. exists (2 * q). lia. }
pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hr1. change (bv_modulus 64) with (2 ^ 64) in Hr1.
pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hr8. change (bv_modulus 64) with (2 ^ 64) in Hr8.
assert (Hw1 : rdword (aview SEGS (w_H Wc) memc) (sp0 - 8) = Some (raZ regs)).
{ apply crtb_rdword_of_val_mem; [|unfold raZ; lia]. exact (HSV 0%nat ltac:(lia)). }
assert (Hw8 : rdword (aview SEGS (w_H Wc) memc) (sp0 - 16) = Some (s0Z regs)).
{ apply crtb_rdword_of_val_mem; [|unfold s0Z; lia]. exact (HSV 1%nat ltac:(lia)). }
destruct (Z_le_gt_dec (ly_top lyc - 16) sp0) as [Hbad|Hgood].
- exists []. split; [|left; reflexivity]. left. split; [right; left; exact Hbad | reflexivity].
- exists ((sp0, raZ regs, s0Z regs) :: ch). split; [|right; reflexivity]. right.
  split; [lia|]. split; [lia|]. split; [exact H8|].
  assert (Hkeep : forall a, sp0 <= a -> a < ly_top ly ->
            rdword (aview SEGS (w_H Wc) memc) a = rdword (aview SEGS (w_H W) mem) a).
  { intros a Ha Hat. apply ts_rdword_keep. intros j Hj. apply F1; lia. }
  split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact H8|].
    split; [exact Hw1|]. split; [exact Hw8|]. split; [exact Hra4|].
    destruct (bad_next sp0 (ly_top lyc) (s0Z regs)) eqn:Eb.
    * destruct Hch as [[_ Hnil] | (Hge & Hlt & Hm8 & _ & _)]; [exact Hnil|].
      exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
      apply orb_true_iff in Eb as [Eb1 | Eb2].
      { apply orb_true_iff in Eb1 as [Eb11 | Eb12].
        - apply Z.leb_le in Eb11. lia.
        - apply Z.leb_le in Eb12. lia. }
      { apply negb_true_iff, Z.eqb_neq in Eb2. exact (Eb2 Hm8). }
    * destruct Hch as [[Hb _] | (Hge & Hlt & Hm8 & Hfp & _)].
      { exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
        apply orb_false_iff in Eb as [Eb1 Eb2]. apply orb_false_iff in Eb1 as [Eb11 Eb12].
        apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12. apply negb_false_iff, Z.eqb_eq in Eb2.
        destruct Hb as [Hb | [Hb | Hb]]; lia. }
      rewrite Etop. apply (crtb_fpchain_keep (aview SEGS (w_H W) mem) (aview SEGS (w_H Wc) memc) sp0);
        [exact Hkeep | lia | lia | exact Hfp].
  + apply Forall_cons; [cbn [fst snd]; lia|].
    destruct Hch as [[_ Hnil] | (_ & _ & _ & _ & HFa)]; [rewrite Hnil; apply Forall_nil|].
    eapply Forall_impl; [|exact HFa]. cbv beta. intros r Hr. lia.
Qed.

(* ---- round_trip_text's post at a call from a live state: the text's own Q (tround_trip_text_specX's post,
   PRH_FnCheck.v at the landing cut 71a8716672:1241-1301) at the call's binders, VERBATIM (the text's local
   `rdW W mem` is `mrestrict (w_H W) mem`; the run's strtod model is ReaderRes.jr_strtod, the text's keying); the
   call rule hands it over as fQmn of it. `rpi` is the call's position. THE r = 1 ARM IS DEAD (`r = 0 /\` in front,
   the text's statement under its entry premise prh_cons_from); the r = 0 arm gives the room at the EXACT advance by
   the call's own list and, with a copy, the read-back's block sizes up to permutation (against the reader's own
   list rd_blocks (rtr jr_strtod [] (wdoc t p)), under CFHEAD-16), copy's ORDERED free list at every depth bound
   (FREEORD-COPY, :1290-1293) and copy's capacities (CAP, PRH_Reader.pj_ncapR, :1301). This segment reads copy's
   blocks against tblk through the size permutation (crtb_tblk_perm) ---- *)
Definition crtb_rtt_Q (rpi : nat) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (Lamc : list (Z * Z)) (peakc cntc ranc copy : Z) (p : bool)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\ exists Lam' peak' cnt' ran' own',
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
       peakc <= peak' /\
       pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') doc t D /\
       exists r, getr regs' 10 = w64 r /\
         r = 0 /\
         ((r = 1 /\ (own' = 1 \/ ran' = 1) /\ Permutation Lam' Lamc /\ Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\
           cntc <= cnt' <= cntc + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\
           (copy <> 0 -> forall a, copy <= a < copy + 56 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H Wc) memc a)) \/
          (r = 0 /\ own' = 0 /\
           cnt' = cntc + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\ ran' = ranc /\
           (exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os
              (rpi + length (ck_rtt_evs ReaderRes.jr_strtod t p copy))%nat rp_H0 hist' S') /\
           (copy = 0 -> Permutation Lam' Lamc /\ Permutation (ablocks B ly' S') (ablocks B lyc Sc)) /\
           (copy <> 0 ->
              exists Db, Permutation Lam' (Db ++ Lamc) /\
                (forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B lyc Sc)) /\
                Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) /\
                (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) Db)
                   (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod [] (WriterValue.wdoc t p)))) /\
                (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
                   exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') nn copy Db F /\
                     map (fun b => snd b + cf_head) F =
                       PresetReqAt.pj_frees ReaderRes.jr_strtod [] (WriterValue.wdoc t p)) /\
                Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) /\
                Permutation (ablocks B ly' S') (ablocks B lyc Sc ++ ck_hblks Db) /\
                pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') copy t Db /\
                pj_ncapR SEGS (mrestrict (w_H W') mem') copy t))).

(* ---- THE SAME POST IN THE FORM crtb_at_M READS (the B' twin of Crt102Arms.arms_rtt_Q_k0): inside the copy <> 0
   existential the text's conjuncts in crtb_at_M's order, the free order (FREEORD-COPY, the text's conjunct verbatim)
   moved after pj_nodeR, and CAP read as the cap word of an object, `rd_u64 (copy + 48) (ncap |ms|)` - the FIRST
   conjunct of the object clause of PRH_Reader.pj_ncapR (PRH_Reader.v:247), the premise of the glue's bridge
   Crt102Glue.crt_copy_cap_of_ncap48 (crt_at_U_B_copy_cap). With PresetFreeFo.pj_frees_wdoc_t the free order is fo t
   (crtb_fo_of_frees), the source of crt_at_U_B_copy_fo and of crt_at_J_B's r = 0 free-order field at C3. crtb_rrt
   carries crtb_rtt_Q into this form conjunct by conjunct ---- *)
Definition crtb_rtt_Q_k0 (rpi : nat) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (Lamc : list (Z * Z)) (peakc cntc ranc copy : Z) (p : bool)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\ exists Lam' peak' cnt' ran' own',
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
       peakc <= peak' /\
       pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') doc t D /\
       exists r, getr regs' 10 = w64 r /\
         r = 0 /\
         ((r = 1 /\ (own' = 1 \/ ran' = 1) /\ Permutation Lam' Lamc /\ Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\
           cntc <= cnt' <= cntc + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\
           (copy <> 0 -> forall a, copy <= a < copy + 56 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H Wc) memc a)) \/
          (r = 0 /\ own' = 0 /\
           cnt' = cntc + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\ ran' = ranc /\
           (exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os
              (rpi + length (ck_rtt_evs ReaderRes.jr_strtod t p copy))%nat rp_H0 hist' S') /\
           (copy = 0 -> Permutation Lam' Lamc /\ Permutation (ablocks B ly' S') (ablocks B lyc Sc)) /\
           (copy <> 0 ->
              exists Db, Permutation Lam' (Db ++ Lamc) /\
                (forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B lyc Sc)) /\
                Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) /\
                (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) Db)
                   (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod [] (WriterValue.wdoc t p)))) /\
                Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) /\
                Permutation (ablocks B ly' S') (ablocks B lyc Sc ++ ck_hblks Db) /\
                pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') copy t Db /\
                (* FREEORD-COPY, the text's conjunct verbatim (its local abbreviation rdW W' mem' written out) *)
                (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
                   exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') nn copy Db F /\
                     map (fun b => snd b + cf_head) F =
                       PresetReqAt.pj_frees ReaderRes.jr_strtod [] (WriterValue.wdoc t p)) /\
                (* CAP's cap word (pj_ncapR's object clause, first conjunct) *)
                (forall ms, t = PjTree.JObj ms ->
                   rd_u64 SEGS (mrestrict (w_H W') mem') (copy + 48) (Z.of_nat (PresetReqAt.ncap (length ms))))))).

(* ---- copy's free list against fo t at every depth bound, from the FREEORD-COPY form: cf_head = HEAD (16 = 16, the
   preset's parameter) and PresetFreeFo.pj_frees_wdoc_t (pj_wf t: pj_free's list of the tree the reader
   builds from the writer's text of t is fo t) - Crt102Arms' arms_fo_of_frees ---- *)
Lemma crtb_fo_of_frees : forall (m : word -> option byte) lblk p Db, PjRoundTrip.pj_wf ReaderRes.jr_strtod t ->
  (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
     exists F, PRH_PjOrder.pj_foR SEGS m lblk nn p Db F /\
       map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod [] (WriterValue.wdoc t false)) ->
  forall nn, (PjTree.depth t <= nn)%nat ->
    exists F, PRH_PjOrder.pj_foR SEGS m lblk nn p Db F /\ map (fun b => snd b + cf_head) F = PresetReqAt.fo t.
Proof.
intros m lblk p Db Hw H nn Hd. destruct (H eq_refl nn Hd) as (F & HF & HM).
exists F. split; [exact HF|]. rewrite HM. exact (PresetFreeFo.pj_frees_wdoc_t ReaderRes.jr_strtod t false Hw).
Qed.

(* ---- the room position on the r = 0 path (Crt102Glue's crt_pos, a Record read by name, at rp_sm :=
   ReaderRes.jr_strtod, the cut's keying: its strtod tie crt_pos_strtod is then eq_refl). At M it is the whole of
   round_trip (pre = []); after both calls returned 0 it is round_trip's tail: crt_evs_U for an object, crt_evs_J
   otherwise. crt_pos carries the consumer window prh_cons_from, split at each call like the run premise (Crt102Arms'
   arms_pos_entry / arms_cons_split / arms_pos_tail / arms_pos_U / arms_pos_J at B''s binders) ---- *)
Lemma crtb_pos_entry : forall Sc, CPOS Sc (PresetReqAt.round_trip ReaderRes.jr_strtod t) ->
  exists hist, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 hist Sc /\
    prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (PresetReqAt.round_trip ReaderRes.jr_strtod t) /\
    PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i
      (length (PresetReqAt.round_trip ReaderRes.jr_strtod t)).
Proof.
intros Sc HP.
destruct (crt_pos_ex HP) as (pre & hist & HA).
pose proof (crt_pos_split HA) as E. pose proof (crt_pos_room HA) as HI.
pose proof (crt_pos_run HA) as HR. pose proof (crt_pos_cons HA) as HC.
assert (Hl : length pre = 0%nat).
{ pose proof (f_equal (@length _) E) as El. rewrite length_app in El. lia. }
rewrite Hl, Nat.add_0_r in HI, HR, HC. exists hist. split; [exact HI|]. split; [exact HR | exact HC].
Qed.
(* the consumer window of the two calls: round_trip's first piece (rtt1, copy <> 0) and second (rtt2, copy = 0) *)
Lemma crtb_cons_split : forall c, c <> 0 ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i
    (length (PresetReqAt.round_trip ReaderRes.jr_strtod t)) ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i (length (ck_rtt_evs ReaderRes.jr_strtod t false c)) /\
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os (rp_i + length (ck_rtt_evs ReaderRes.jr_strtod t false c))
    (length (ck_rtt_evs ReaderRes.jr_strtod t true 0)).
Proof.
intros c Hc HC. rewrite (crtb_ck_rtt_nz ReaderRes.jr_strtod t false c Hc).
rewrite (crtb_rt_tail ReaderRes.jr_strtod t), !length_app in HC.
apply (proj1 (PRH_Base.prh_cons_from_app_iff _ _ _ _ _ _)) in HC as [HC1 _].
exact (proj1 (PRH_Base.prh_cons_from_app_iff _ _ _ _ _ _) HC1).
Qed.
Lemma crtb_pos_tail : forall S2 hist,
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (PresetReqAt.round_trip ReaderRes.jr_strtod t) ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i
    (length (PresetReqAt.round_trip ReaderRes.jr_strtod t)) ->
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os
    (rp_i + length (PresetReqAt.rt_text ReaderRes.jr_strtod t false) +
     length (ck_rtt_evs ReaderRes.jr_strtod t true 0))%nat rp_H0 hist S2 ->
  CPOS S2 (match t with PjTree.JObj ms => EVSU ms | _ => EVSJ end).
Proof.
intros S2 hist HR HC HI.
pose proof (crtb_rt_tail ReaderRes.jr_strtod t) as E.
rewrite E in HR, HC. apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in HR as [_ HR].
rewrite length_app in HC. apply (proj1 (PRH_Base.prh_cons_from_app_iff _ _ _ _ _ _)) in HC as [_ HC].
refine {| crt_pos_strtod := eq_refl; crt_pos_ex := _ |}.
exists (PresetReqAt.rt_text ReaderRes.jr_strtod t false ++ ck_rtt_evs ReaderRes.jr_strtod t true 0), hist.
refine {| crt_pos_split := E; crt_pos_room := _; crt_pos_run := HR; crt_pos_cons := HC |}.
rewrite length_app, Nat.add_assoc. exact HI.
Qed.
Lemma crtb_pos_U : forall S2 hist ms, t = PjTree.JObj ms ->
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (PresetReqAt.round_trip ReaderRes.jr_strtod t) ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i
    (length (PresetReqAt.round_trip ReaderRes.jr_strtod t)) ->
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os
    (rp_i + length (PresetReqAt.rt_text ReaderRes.jr_strtod t false) +
     length (ck_rtt_evs ReaderRes.jr_strtod t true 0))%nat rp_H0 hist S2 ->
  CPOS S2 (EVSU ms).
Proof.
intros S2 hist ms Et HR HC HI. pose proof (crtb_pos_tail S2 hist HR HC HI) as H.
assert (E : match t with PjTree.JObj ms0 => EVSU ms0 | _ => EVSJ end = EVSU ms) by (rewrite Et; reflexivity).
rewrite E in H. exact H.
Qed.
Lemma crtb_pos_J : forall S2 hist, (forall ms, t <> PjTree.JObj ms) ->
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (PresetReqAt.round_trip ReaderRes.jr_strtod t) ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i
    (length (PresetReqAt.round_trip ReaderRes.jr_strtod t)) ->
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os
    (rp_i + length (PresetReqAt.rt_text ReaderRes.jr_strtod t false) +
     length (ck_rtt_evs ReaderRes.jr_strtod t true 0))%nat rp_H0 hist S2 ->
  CPOS S2 EVSJ.
Proof.
intros S2 hist Hn HR HC HI. pose proof (crtb_pos_tail S2 hist HR HC HI) as H.
rewrite (crtb_tail_nobj ReaderRes.jr_strtod t Hn) in H. exact H.
Qed.

(* the class-3 frame's facts at a live state *)
Lemma crtb_frame_facts : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kbg,
  LIVE kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  let F := frame_addr lyc CRT_CID pos in
  In (CRT_CID, pos) (frames Sc) /\ F mod 32 = 0 /\ 4096 <= F /\ F + 512 <= YM05.alloc_ceiling /\ in_app F 512 /\
  (forall a, F <= a < F + 512 -> apresent (w_H Wc) memc a /\ ~ aowned B lyc Sc a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H Wc) memc (shadow_addr F + i)).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kbg HL F.
destruct (crt_live_journal HL) as (? & (HARc & _) & _).
pose proof (crt_frame_listed (crt_live_frame HL)) as Hin3.
destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin3) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin3) as (F32 & Fapp & Ffr & Fsh).
change (fs_frame_bytes CRT_CID) with 512 in *. change (512 / 8) with 64 in Fsh.
split; [exact Hin3|]. split; [exact F32|]. split; [exact Fb1|]. split; [exact Fb2|]. split; [exact Fapp|].
split; [exact Ffr|]. intros i Hi. exact (proj1 (Fsh i Hi)).
Qed.

(* ---- THE WILD BUDGET AT A round_trip_text CALL, the B' TWIN of Crt102Arms.arms_wild_budget, RESTATED AT THE kb
   ROUND (owner: the contract texts). The cut's text (PRH_FnCheck.v:1216) asks at the call the room `wild_room
   (as_universe B) [] (prh_wk F_round_trip_text) (st_depot Sc)` and posts fpostFbm .. (wbudget [] (prh_wk
   F_round_trip_text)) (:1256): through YCbqGwild.aj_call_xbF_sp the caller's journal after the call is at WS0 ++ WS1,
   WS0 the live state's budget and `wbudget [] (prh_wk F_round_trip_text) WS1` the call's. The glue's crt_live carries
   its budget kb and its journal at a budget WS with `wbudget [] kb WS` (Crt102Glue.v crt_live_journal), so this Prop
   states, at every live state at a kb that leaves the call its 32 (kb + 32 <= 66 = prh_wk F_check_round_trip: rtt1 at
   kb = 0, rtt2 at kb = 32), the room the text asks and the landing of the composed journal at kb + 32. It is the
   premise of crtb_rtt_call and of every lemma that reaches it (crtb_at_R1, crtb_at_M), and it is DISCHARGED below by
   crtb_wild_budget_goal (Qed) from the text's entry room HWR0 (YCbqGwild.ajournal_xw_room, wild_room_le, wbudget_app).
   ---- *)
Definition crtb_wild_budget : Prop :=
  forall (kb : nat) lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc,
  LIVE kb lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 ran ->
  (kb + prh_wk F_round_trip_text <= prh_wk F_check_round_trip)%nat ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_round_trip_text) (st_depot Sc) /\
  (forall ly2 S2 Hp2 W2 mem2 md2 k1 (WS0 WS1 : list (list Z)),
     YCbqGwild.wbudget [] kb WS0 ->
     YCbqGwild.wbudget [] (prh_wk F_round_trip_text) WS1 ->
     AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) (WS0 ++ WS1) ->
     exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS /\
       YCbqGwild.wbudget [] (kb + prh_wk F_round_trip_text) WS).

(* the per-boundary arithmetic (prh_wk F_check_round_trip = 66 = 32 + 32 + 2, PRH_Base.v:151-160; Crt102Arms'
   arms_kb_rtt1 / arms_kb_rtt2): rtt1 at kb = 0 and rtt2 at kb = 32 each leave the call its 32; U's 64 is within J's
   66 *)
Lemma crtb_kb_rtt1 : (0 + prh_wk F_round_trip_text <= prh_wk F_check_round_trip)%nat.
Proof. cbn. lia. Qed.
Lemma crtb_kb_rtt2 : (prh_wk F_round_trip_text + prh_wk F_round_trip_text <= prh_wk F_check_round_trip)%nat.
Proof. cbn. lia. Qed.

(* the live state at a budget kb is a live state at every larger budget (wbudget is an upper bound; Crt102Arms'
   arms_live_mono at B''s binders) *)
Lemma crtb_live_mono : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kb kb',
  LIVE kb lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc -> (kb <= kb')%nat ->
  LIVE kb' lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kb kb' HL Hk.
destruct (crt_live_journal HL) as (WS & HJ & HB).
exact {| crt_live_journal := ex_intro _ WS (conj HJ (Nat.le_trans _ _ _ HB Hk)); crt_live_side := crt_live_side HL;
         crt_live_lam_perm := crt_live_lam_perm HL; crt_live_blocks_perm := crt_live_blocks_perm HL;
         crt_live_dx_apart := crt_live_dx_apart HL; crt_live_saved := crt_live_saved HL;
         crt_live_frame := crt_live_frame HL; crt_live_fspill := crt_live_fspill HL;
         crt_live_copy_open := crt_live_copy_open HL; crt_live_copy_hull := crt_live_copy_hull HL;
         crt_live_memnorm := crt_live_memnorm HL |}.
Qed.
(* THE C3 STEP (t not an object, after rtt2): the live state is at 64 = 32 + 32 and J_B is at 66; the step is a real
   step up (64 < 66), not an identity, and crtb_live_mono with crtb_kb_rtt2 makes it *)
Lemma crtb_kb_C3_lt : (prh_wk F_round_trip_text + prh_wk F_round_trip_text < prh_wk F_check_round_trip)%nat.
Proof. cbn. lia. Qed.
Lemma crtb_kb_C3_ne : (prh_wk F_round_trip_text + prh_wk F_round_trip_text <> prh_wk F_check_round_trip)%nat.
Proof. cbn. lia. Qed.

(* ---- THE round_trip_text CALL, from the state a run leaves at `jal round_trip_text` (B' +0x1a0 and +0x1c0): the
   live state with the call next, the argument registers, and the per-call model bounds, each given by the caller
   from the text's own premises (Crt102Model.v). Over YCbqGwild.v's aj_call_xbF_sp (the text's post is budgeted at
   the cut), the caller's journal at the live state's budget WS0 (crt_live at kb); the call's room and the landing of
   the composed journal at kb + 32 are crtb_wild_budget, its first premise. Crt102Arms' arms_rtt_call with B''s
   registers (crt_dregs_B) and image. ---- *)
Lemma crtb_rtt_call : crtb_wild_budget -> forall (fxk : YK11.FPState) (pretty copy off : Z) Wc E ss ms mdc lyc Sc
    Hpc kj pos Dx Lamc peakc cntc rpi rph (kb : nat),
  frm_zero (@YK11.fp_csr fxk) ->
  @st_ok SEGS fxk E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_round_trip_text ->
  LIVE kb lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc 0 ran ->
  (kb + prh_wk F_round_trip_text <= prh_wk F_check_round_trip)%nat ->
  DREGS (ms_regs ms) (frame_addr lyc CRT_CID pos) ->
  getr (ms_regs ms) 10 = w64 doc -> getr (ms_regs ms) 11 = w64 pretty -> getr (ms_regs ms) 12 = w64 copy ->
  (pretty = 0 \/ pretty = 1) ->
  (off = CRT_R1_OFF_B \/ off = CRT_R2_OFF_B) -> getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + off)) ->
  (copy = 0 \/ copy = frame_addr lyc CRT_CID pos + CRT_OFF_COPY) ->
  cntc < 2 ^ 62 ->
  RQA_rtt t (negb (pretty =? 0)) <= most ->
  blocks_bytes Sc + LIVE_round_trip_text t (negb (pretty =? 0)) <= LIVE_MAX ->
  RQ_rtt t (negb (pretty =? 0)) + cf_head < cf_malloc_max ->
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os rpi rp_H0 rph Sc ->
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rpi (ck_rtt_evs ReaderRes.jr_strtod t (negb (pretty =? 0)) copy) ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rpi
    (length (ck_rtt_evs ReaderRes.jr_strtod t (negb (pretty =? 0)) copy)) ->
  (forall (fx' : YK11.FPState) ly2 S2 Hp2 W2 regs2 mem2 md2 k1 WS WS1,
     frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
     AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS ->
     YCbqGwild.wbudget [] (kb + prh_wk F_round_trip_text) WS ->
     AJW STKR SP1 (if copy =? 0 then [] else [(copy, copy + 56)]) lyc Sc Hpc Wc (ms_mem ms) mdc []
       ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
     aregs_preserved (ms_regs ms) regs2 ->
     crtb_rtt_Q rpi lyc Sc Wc (ms_mem ms) Lamc peakc cntc ran copy (negb (pretty =? 0)) ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     (YAkMemnorm.memnorm SEGS (ms_mem ms) -> YAkMemnorm.memnorm SEGS mem2) ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
       (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + (CRT_PC_B + off))) mem2 (YK11.seg_rom SEGS)) md2) QFF) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms mdc) QFF.
Proof.
intros HGAP fxk pretty copy off Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc rpi rph kb HFZ HS Hrv Hpcs HL Hkb
  HDR Ha0 Ha1 Ha2 Hpr Hoff Hra Hcopy Hcnt HRQAr HLIVEr HRQr HRP HRUN HCONS HK.
destruct (HGAP kb lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc HL Hkb) as [HWR HLAND].
destruct (crt_live_journal HL) as (WS0 & HJ & HB0). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_saved HL) as HSV. pose proof (crt_live_copy_open HL) as HCS.
pose proof (crt_live_copy_hull HL) as HCH. pose proof (crt_live_memnorm HL) as HMNc.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_room HSD) as HROOM.
pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_dregs_B_bregs HDR) as HBR.
pose proof (crt_bregs_B_sp HBR) as R2. pose proof (crt_bregs_B_gp HBR) as R3.
pose proof (crt_bregs_B_tp HBR) as R4. pose proof (crt_bregs_B_s0 HBR) as R8.
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO0 & Hhi & Hrac & HFZ0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof crtb_stk as (HS0 & HS1). destruct crtb_sp1 as (Hs32 & Hs1 & Hs0).
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _).
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
destruct (crtb_frame_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL) as (Hin3 & F32 & Fb1 & Fb2 & Fapp & Ffr & Fsh).
cbv zeta in Fb1, Fb2, Fapp, Ffr, Fsh, F32.
set (F := frame_addr lyc CRT_CID pos) in *.
destruct (crtb_ret off Hoff) as (Hr1 & Hr2 & Hr3 & Hr4).
destruct (crtb_chain _ _ _ _ _ _ _ _ _ HJ HSV) as (ch1 & Hch1 & Ech1).
set (o := SP1 - sp0).
assert (Hspz : spZ (ms_regs ms) = SP1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hspz' : spZ (ms_regs ms) = sp0 + o) by (rewrite Hspz; unfold o; lia).
assert (Hs0z : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
assert (Hraz : raZ (ms_regs ms) = BASE + (CRT_PC_B + off)) by (unfold raZ; rewrite Hra; apply unsigned_lit_small; lia).
(* the document is at or above 4096 (its home frame is a live frame of the entry) *)
assert (Hdoc0 : doc <> 0).
{ pose proof HTREE as (_ & _ & _ & _ & (cid & pos' & Hfin & Hfa1 & _) & _).
  destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos' HAR Hfin) as (Hf1 & _). lia. }
(* the model premises, from the text's own *)
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ refine (@YCbqGwild.aj_call_xbF_spR fxk rc SK SEGS B PST ARx cf_head LAWS (@pa_segs_low rc B_prog_listing PA)
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)
    Wc E ss ms STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc mdc kj WS0 STKR
    (if copy =? 0 then [] else [(copy, copy + 56)]) o (getr (ms_regs ms) 1) ch1
    (YCbqGwild.wbudget [] (prh_wk F_round_trip_text)) _ HS Hrv HJ Hspz' _ _ HS0 _ _ _ eq_refl _ _ _ _ _).
  - unfold o. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. apply Z.mod_divide in Hs32; [|lia].
    destruct Hs32 as [q' Hq']. apply Z.mod_divide; [lia|]. exists (2 * q' - q). lia.
  - unfold o. lia.
  - unfold o. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - rewrite Hra. apply (ret_ok_codeptr_v (PI := PA)); [exact Hr3 | exact Hr2].
  - rewrite Hra, unsigned_lit_small by lia. lia.
  - replace (sp0 + o) with SP1 by (unfold o; lia). rewrite Hs0z. exact Hch1.
  - (* the callee: round_trip_text's text at the call's binders *)
    intros HPRE1. rewrite Hpcs.
    pose proof HPRE1 as (_ & _ & _ & _ & _ & Hstk1 & _ & _ & _).
    pose proof Hstk1 as (_ & _ & Hceil1 & Hslo1 & _ & _ & _ & _ & _).
    assert (Hhi1 : spZ (ms_regs ms) + 64 <= ly_stk_hi lyc) by (rewrite Hspz, Eshi; lia).
    assert (Hrac1 : raZ (ms_regs ms) < YM05.alloc_ceiling) by (rewrite Hraz; lia).
    assert (HCTX1 : prh_ctx CTX0 F_round_trip_text (raZ (ms_regs ms) :: spine ch1)).
    { pose proof (prh_ctx_call CTX0 F_check_round_trip F_round_trip_text _ _ HCTX (eq_ind_r (fun r => In r _) Hr4 Hraz))
        as Hc. rewrite crtb_fp in Hc.
      destruct Ech1 as [-> | ->]; [exact (crtb_ctx_head _ _ _ _ Hc) | exact Hc]. }
    assert (HCOPY : copy = 0 \/ (copy <> 0 /\ copy mod 8 = 0 /\
      ck_out_ok B STKR lyc Sc Wc (ms_regs ms) (ms_mem ms) copy 56 /\ (copy + 56 <= doc \/ doc + 56 <= copy))).
    { destruct Hcopy as [-> | ->]; [left; reflexivity|]. right.
      split; [unfold CRT_OFF_COPY; lia|]. split; [unfold CRT_OFF_COPY; apply Z.mod_divide in F32; [|lia];
        destruct F32 as [q Hq]; apply Z.mod_divide; [lia|]; exists (4 * q + 28); lia|].
      split; [split|].
      - exists CRT_CID, pos. split; [exact Hin3|]. change (fs_frame_bytes CRT_CID) with 512. unfold CRT_OFF_COPY. lia.
      - unfold CRT_OFF_COPY. split; [lia|]. split; [lia|].
        split; [unfold in_app, amem_range, kLowShadowBeg in *; unfold ASAN_CEIL in Fapp; lia|].
        split; [intros a Ha; destruct (Ffr a ltac:(lia)) as (Hp1 & Hp2); split; [apply apresent_writable; exact Hp1|];
          split; [exact Hp2 | rewrite Hspz; lia]|].
        split; [exact HCS | intros _; exact HCH].
      - (* copy is in the class-3 frame, the document in a frame of the entry: the frames are apart *)
        pose proof HTREE as (_ & _ & _ & _ & (cid & pos' & Hfin & Hfa1 & Hfa2) & _).
        destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR HLYc) as (_ & Efa & _).
        destruct (alx_sep SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms) mdc HARc) as (Hsep & _).
        apply pairwise_app_l in Hsep as [_ Hsep]. rewrite HFRc in Hsep. cbn [app map pairwise] in Hsep.
        destruct Hsep as (Hsep & _). rewrite Forall_map in Hsep.
        pose proof (proj1 (Forall_forall _ _) Hsep (cid, pos') Hfin) as Hd. cbn [fst snd] in Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite (Efa cid pos') in Hd.
        change (fs_frame_bytes CRT_CID) with 512 in Hd. unfold CRT_OFF_COPY. fold F in Hd. lia. }
    assert (HFRS : Z.of_nat (length (frames Sc)) <= ck_FRAMES_CAP - FR_round_trip_text).
    { rewrite HFRc. cbn [app length]. pose proof (cm_frames_before (length (frames S)) HFR). lia. }
    (* THE LIVE REAL STACK ABOVE THE CALLEE'S sp (the text's last premise at the 4b8f95c0455c kit text,
       PRH_FnCheck.v:1241): from check_round_trip's own entry fact HUP0 through the journal from the entry at its budget
       (YGcallStackUp.astack_up_at_xwR at RZW, which reads no depot and no world conjunct), the callee's sp SP1 inside
       the entry's window (crtb_sp1, crtb_stk); as Crt102Arms.arms_rtt_call. The measured witness
       rtt_up_at_call_B (RttStackUpB.v at commit 5208cc4f6eb0, a file not in this tree) is the same step; it is
       done here at the walk's binders, not Required *)
    assert (HUPc : YGcallStackUp.astack_up_x SEGS lyc Wc (spZ (ms_regs ms)) (ms_mem ms)).
    { rewrite Hspz. pose proof crtb_stk as (Sk0 & Sk1). pose proof crtb_sp1 as (_ & (Sp1 & Sp2) & _).
      pose proof (YGcallStackUp.astack_up_at_xwR SEGS B PST ARx (@pa_segs_low rc B_prog_listing PA) RZW STKC sp0 []
        ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc (ms_mem ms) mdc kj WS0 SP1 STKR HJ HUP0 ltac:(lia) Sk0
        ltac:(lia)) as Hd.
      intros a Ha. apply Hd. lia. }
    exact (RTT fxk rp_x rp_os rpi rp_H0 rph lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 doc pretty copy t D
      Lamc peakc cntc ran most (conj HPRE1 (conj HRO (conj Hhi1 (conj Hrac1 HFZ)))) (HMNc HMN) HCL HCTX1 Ha0 Ha1 Ha2 Hpr
      Hdoc0
      (crtb_tree_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL) (cm_in_wf x t HIN) (cm_in_depth32 x t HIN) (cm_in_wlen x t _ HIN)
      HCOPY HLED Hcnt HRUN HRAN HRQAr HLIVEr HRQr HFRS HROOM HRP HFZ HOS4 HWR HCONS HUPc).
  - (* the callee's footprint: copy's window, a slot of the frame this function took *)
    intros a Hfa. destruct (Z.eqb_spec copy 0) as [E0|E0].
    + exfalso. exact (inFP_nil a Hfa).
    + apply inFP_cons in Hfa as [Hfa | Hfa]; [|exfalso; exact (inFP_nil a Hfa)].
      right; right; left. exists (CRT_CID, pos). split; [left; reflexivity|].
      unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes CRT_CID) with 512.
      destruct Hcopy as [-> | ->]; [lia|]. fold F. unfold CRT_OFF_COPY in Hfa. lia. }
cbv beta. intros W2 c2 _
  (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ2 & HFK2 & HPW & HJ2 & HJ1 & HP & HQ & HMN2).
replace (sp0 + o) with SP1 in HJ1 by (unfold o; lia).
(* the composed journal (at WS0 ++ WS1) at the budget kb + 32: crtb_wild_budget's landing *)
destruct (HLAND ly2 S2 Hp2 W2 mem2 md2 k1 WS0 WS1 HB0 HPW HJ2) as (WS & HJ2a & HBa).
rewrite Hra. exact (HK fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 WS WS1 HFZ2 HFK2 HJ2a HBa HJ1 HP HQ HMN2).
Qed.

(* ---- the live state after a round_trip_text call (Crt102Arms' arms_live_after at B''s image) ---- *)
Lemma crtb_live_after : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc copy
    ly2 S2 Hp2 W2 mem2 md2 k1 Dx' Lam2 peak2 cnt2 own2 ran2 kbg kbg' WS WS1,
  LIVE kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (copy = 0 \/ copy = frame_addr lyc CRT_CID pos + CRT_OFF_COPY) ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS ->
  YCbqGwild.wbudget [] kbg' WS ->
  AJW STKR SP1 (if copy =? 0 then [] else [(copy, copy + 56)]) lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1
    WS1 ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  room_live_cf S2 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 most own2 -> peakc <= peak2 ->
  pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) doc t D ->
  (forall bk, In bk Lamc -> In bk Lam2) ->
  Permutation Lam2 (Dx' ++ Lam) -> Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks Dx') ->
  (forall bk, In bk Dx' -> ~ In bk D) ->
  LIVE kbg' ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Dx' Lam2 peak2 cnt2 own2 ran2.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc copy ly2 S2 Hp2 W2 mem2 md2 k1 Dx' Lam2 peak2 cnt2
  own2 ran2 kbg kbg' WS WS1 HL Hcopy HJ2 HB2 HJ1 HMN12 HROOM2 HLED2 Hpk2 HND2 HLam HPm2 HPab2 HDap2.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_saved HL) as HSV. pose proof (crt_live_frame HL) as HFRM.
pose proof (crt_live_fspill HL) as HSP. pose proof (crt_live_copy_open HL) as HCS.
pose proof (crt_live_copy_hull HL) as HCH. pose proof (crt_live_memnorm HL) as HMNc.
pose proof (crt_side_peak HSD) as Hpk. pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & _).
pose proof HJ1 as (HAR2 & HLY1 & _ & _ & _ & HFR1 & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof HLY1 as (_ & _ & _ & _ & _ & EFF & _ & _ & Etop & Eslo & Eshi & _).
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO0 & Hhi & Hrac & HFZ0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof crtb_stk as (HS0 & HS1). destruct crtb_sp1 as (Hs32 & Hs1 & Hs0).
destruct (crtb_frame_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL) as (Hin3 & F32 & Fb1 & Fb2 & Fapp & Ffr & Fsh).
cbv zeta in Fb1, Fb2, Fapp, Ffr, Fsh, F32.
destruct (alx_layout SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc ly2 HARc HLY1) as (_ & Efa & _).
assert (EF : frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos) by apply Efa.
assert (EFL : flag_addr ly2 CRT_CID pos = flag_addr lyc CRT_CID pos) by (unfold flag_addr; rewrite EFF; reflexivity).
pose proof (crt_frame_flag_word HFRM) as Hflag.
set (F := frame_addr lyc CRT_CID pos) in *.
(* the call's footprint is copy's window or nothing *)
assert (HnFP : forall a, inFP (if copy =? 0 then [] else [(copy, copy + 56)]) a -> F + 224 <= a < F + 280).
{ intros a Ha. destruct (Z.eqb_spec copy 0) as [E0|E0]; [exfalso; exact (inFP_nil a Ha)|].
  apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
  destruct Hcopy as [-> | ->]; [lia|]. unfold CRT_OFF_COPY in Ha. lia. }
(* every byte at or above the realigned sp is above the callee's window: kept *)
assert (Kst : forall a, SP1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply G1; lia. }
(* the class-3 frame's bytes and shadow off copy's window: kept by the frame clause *)
assert (Kfr : forall a, (F <= a < F + 512 \/ shadow_addr F <= a < shadow_addr F + 64) -> ~ (F + 224 <= a < F + 280) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. apply (G4 CRT_CID pos a Hin3).
  - unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes CRT_CID) with 512. change (512 / 8) with 64. fold F. lia.
  - intros Hf. exact (Hn (HnFP a Hf)). }
(* copy's shadow bytes lie in the frame's shadow, far from copy's own window *)
assert (Hsh : forall s, shadow_addr (F + CRT_OFF_COPY) / 8 * 8 <= s < shadow_addr (F + CRT_OFF_COPY + 56 - 1) / 8 * 8 + 8 ->
  shadow_addr F <= s < shadow_addr F + 64 /\ ~ (F + 224 <= s < F + 280)).
{ intros s Hs. unfold shadow_addr, CRT_OFF_COPY in *. unfold in_app, kLowShadowBeg, ASAN_CEIL in Fapp.
  unfold SHADOW_OFF in *. split; lia. }
refine {| crt_live_journal := ex_intro _ WS (conj HJ2 HB2); crt_live_side := _; crt_live_lam_perm := HPm2;
          crt_live_blocks_perm := HPab2; crt_live_dx_apart := HDap2; crt_live_saved := _;
          crt_live_frame := _; crt_live_fspill := _; crt_live_copy_open := _; crt_live_copy_hull := _;
          crt_live_memnorm := _ |}.
{ refine {| crt_side_ledger := HLED2; crt_side_peak := _; crt_side_room := HROOM2; crt_side_arodata := _;
            crt_side_doc := HND2; crt_side_doc_blocks := _ |}.
  - lia.
  - intros a Hro Hno Her. rewrite (G3 a); [exact (HRO a Hro Hno Her) | | exact Hno | exact Her | |].
    + destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
    + intros Hps. exact (pst_not_ro_B a Hps Hro).
    + apply fp_spares_closed. apply sink_closed_pos. destruct (Z.eqb_spec copy 0) as [E0|E0]; [constructor|].
      constructor; [cbn [fst]; destruct Hcopy as [-> | ->]; [lia | unfold CRT_OFF_COPY; lia] | constructor].
  - intros bk Hbk; apply HLam; apply HDL; exact Hbk. }
{ intros j Hj. eapply ts_vm_av; [|exact (HSV j Hj)]. intros i Hi. apply Kst. lia. }
{ refine {| crt_frame_listed := _; crt_frame_flag_word := _; crt_frame_present := _ |}.
  - rewrite HFR1; exact Hin3.
  - rewrite EF, EFL. rewrite <- Hflag. apply ts_rdword_keep. intros j Hj. fold F. apply Kfr; [left | ];
      change (fs_frame_bytes CRT_CID) with 512; lia.
  - intros a Ha. rewrite EF in Ha.
    assert (Hin2 : In (CRT_CID, pos) (frames S2)) by (rewrite HFR1; exact Hin3).
    destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 CRT_CID pos HAR2 Hin2) as (_ & _ & Ffr2 & _).
    rewrite EF in Ffr2. exact (proj1 (Ffr2 a Ha)). }
{ unfold crt_spill. rewrite EF. eapply ts_vm_av; [|exact HSP]. intros i Hi. apply Kst. unfold CRT_SP_F. lia. }
{ rewrite EF. intros a Ha. destruct (HCS a Ha) as (s & Hs & Hok). exists s. split; [|exact Hok]. rewrite <- Hs.
  fold F in Ha |- *. unfold CRT_OFF_COPY in Ha. apply Kfr.
  - right. unfold shadow_of_addr, shadow_addr. unfold SHADOW_OFF. lia.
  - unfold shadow_of_addr. unfold in_app, kLowShadowBeg, ASAN_CEIL in Fapp. unfold SHADOW_OFF in *. lia. }
{ rewrite EF. intros s Hs. fold F in Hs |- *. destruct (Hsh s Hs) as [H1 H2]. rewrite (Kfr s (or_intror H1) H2).
  exact (HCH s Hs). }
intros Hm. exact (HMN12 (HMNc Hm)).
Qed.

(* ======================================================================================================== *)
(* ---- the runs of this segment write no memory: a run's frame over regions with no write window keeps every
   byte ---- *)
Lemma crtb_frame_ro : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> m' = m.
Proof.
intros E rs m m' H Hro. apply functional_extensionality. intros xw. apply H. intros (r & Hr & Ha).
rewrite Forall_forall in Hro. specialize (Hro r Hr). lia.
Qed.
(* the live state at the same memory with the journal a run leaves (Crt102Arms' arms_live_md at B''s binders; the
   run keeps the budget) *)
Lemma crtb_live_same : forall lyc Sc Hpc Wc memc mdc mdc' kj pos Dx Lamc peakc cntc ownc ranc kbg WS,
  LIVE kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc' kj WS ->
  YCbqGwild.wbudget [] kbg WS ->
  LIVE kbg lyc Sc Hpc Wc memc mdc' kj pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc mdc mdc' kj pos Dx Lamc peakc cntc ownc ranc kbg WS HL HJ HB.
exact {| crt_live_journal := ex_intro _ WS (conj HJ HB); crt_live_side := crt_live_side HL;
         crt_live_lam_perm := crt_live_lam_perm HL; crt_live_blocks_perm := crt_live_blocks_perm HL;
         crt_live_dx_apart := crt_live_dx_apart HL; crt_live_saved := crt_live_saved HL;
         crt_live_frame := crt_live_frame HL; crt_live_fspill := crt_live_fspill HL;
         crt_live_copy_open := crt_live_copy_open HL; crt_live_copy_hull := crt_live_copy_hull HL;
         crt_live_memnorm := crt_live_memnorm HL |}.
Qed.

(* ---- the document: its home (ck_obj_home), its bounds, its shadow byte and its type word at a live state ---- *)
Lemma crtb_doc_home : 4096 <= doc /\ doc + 56 <= YM05.alloc_ceiling /\ in_app doc 56 /\ doc mod 8 = 0.
Proof.
pose proof HPRE as ((HAR & _ & _ & _ & _ & _ & _ & _ & _) & _ & _ & _ & _).
pose proof HTREE as (_ & _ & _ & (Hd8 & (cid & pos' & Hin & H1 & H2) & _)).
destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md cid pos' HAR Hin) as (Fb1 & Fb2 & Fb3).
split; [lia|]. split; [lia|]. split; [|exact Hd8].
apply (in_app_sub _ _ _ _ Fb3); lia.
Qed.
Lemma crtb_doc_bytes : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kbg,
  LIVE kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (shadow_addr doc) 1 0 /\
  val_mem SEGS (mrestrict (w_H Wc) memc) doc 4 (PjTree.tag t).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kbg HL.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_side_doc (crt_live_side HL)) as HND.
pose proof crtb_doc_home as (Hd1 & Hd2 & Hd3 & Hd4).
destruct (crtb_home_keep _ _ _ _ _ _ _ _ _ HJ) as (_ & _ & HRA).
split.
- destruct (HRA (doc + 7) ltac:(lia)) as (s & Hs & Hok).
  assert (E7 : shadow_of_addr SHADOW_OFF (doc + 7) = shadow_addr doc).
  { unfold shadow_of_addr, shadow_addr. f_equal. apply Z.mod_divide in Hd4; [|lia]. destruct Hd4 as [q Hq]. subst doc.
    rewrite Z.div_mul by lia. replace (q * 8 + 7) with (7 + q * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  rewrite E7 in Hs.
  assert (Hs0 : s = 0).
  { destruct Hok as [Hok | Hok]; [exact Hok|]. exfalso.
    assert ((doc + 7) mod 8 = 7) by (rewrite Z.add_mod by lia; rewrite Hd4; reflexivity). lia. }
  subst s. exact (ts_vm1_of_aview _ _ _ _ Hs).
- exact (proj2 (crtb_node_hdr SEGS _ _ _ _ _ HND)).
Qed.

(* ---- the symbolic states the segment's runs start from. At M, R1, R2: no region, no fact (the runs there read no
   memory). At T: the shadow byte of doc (atom 64 = shadow_addr doc, aliased to `(s6 >> 3) + s11`, holding 0) and
   doc's type word (base s6, holding atom 65 = the tree's tag), s6 8-aligned (UBSan's `andi a0, s6, 7` test) ---- *)
Definition crtb_ss0 (pc : Z) : sstate := mkSS pc cur_atoms [] None (mkFacts [] [] []).
Definition crtb_ssT : sstate := mkSS (CRT_PC_B + CRT_T_OFF_B) cur_atoms
  [ YP09.mkRegion (Some 64%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
    YP09.mkRegion (Some (xr 22)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 65 0))] ] None
  (mkFacts [(xr 22, mkAF 4096 (2 ^ 47) 3); (xr 27, mkAF SHADOW_OFF SHADOW_OFF 0);
            (64%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0); (65%nat, mkAF 0 6 0)] []
     [(SAlu ALU_ADD (SAlu ALU_SRL (SOff (xr 22) 0) (SLit 3)) (SOff (xr 27) 0), SOff 64 0)]).

Lemma crtb_ss0_entry : forall (fxk : YK11.FPState) pc (Wc : world SEGS) memc rg,
  st_ok_pi SEGS VAL (TE regs rg []) (crtb_ss0 pc)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk pc Wc memc rg. split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
- apply te_regs_ok.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint]. exact I.
- split; [exact I | split; exact I].
Qed.

Lemma crtb_ssT_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg,
  getr rg 22 = w64 doc -> getr rg 27 = w64 SHADOW_OFF ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (shadow_addr doc) 1 0 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) doc 4 (PjTree.tag t) ->
  st_ok_pi SEGS VAL (TE regs rg [w64 (shadow_addr doc); w64 (PjTree.tag t)]) crtb_ssT
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_T_OFF_B))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg [w64 (shadow_addr doc); w64 (PjTree.tag t)]) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg R22 R27 Hsh Hty.
pose proof crtb_doc_home as (Hd1 & Hd2 & Hd3 & Hd4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof (cm_tag_range t) as Htg.
set (E := TE regs rg [w64 (shadow_addr doc); w64 (PjTree.tag t)]).
assert (Hshr : SHADOW_OFF <= shadow_addr doc <= SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (X22 : bv_unsigned (ew E (xr 22)) = doc).
{ unfold E, xr. rewrite (te_cur regs rg _ 22%bv 22) by reflexivity. rewrite R22. apply unsigned_lit_small. lia. }
assert (X27 : bv_unsigned (ew E (xr 27)) = SHADOW_OFF).
{ unfold E, xr. rewrite (te_cur regs rg _ 27%bv 27) by reflexivity. rewrite R27. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (E64 : ew E 64 = w64 (shadow_addr doc)) by exact (te_more_lt regs rg _ 0 ltac:(lia)).
assert (E65 : ew E 65 = w64 (PjTree.tag t)) by exact (te_more_lt regs rg _ 1 ltac:(lia)).
assert (X64 : bv_unsigned (ew E 64) = shadow_addr doc).
{ rewrite E64. apply unsigned_lit_small. unfold SHADOW_OFF in *. lia. }
assert (X65 : bv_unsigned (ew E 65) = PjTree.tag t) by (rewrite E65; apply unsigned_lit_small; lia).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE regs rg [w64 (shadow_addr doc); w64 (PjTree.tag t)]) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ 64 (shadow_addr doc)); [exact X64 | unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia
      | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Hsh.
  + apply (ts_rok E _ (xr 22) doc); [exact X22 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 0 4 (SOff 65 0) (PjTree.tag t));
      [cbn [sv_denot]; rewrite E65, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Hty.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X64, X22.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X22, X27, X64, X65.
    change (2 ^ 3) with 8. change (2 ^ 0) with 1. unfold SHADOW_OFF in *. repeat split; try lia.
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply (ts_alias_shadow E (xr 22) (xr 27) 64 doc X22 X27 X64). lia.
Qed.

(* a register the run did not write *)
Ltac crtb_keep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.
(* every region of a segment state has no write window *)
Ltac crtb_ro := cbn [ss_mem crtb_ssT crtb_ss0 add_cond]; repeat constructor; cbn [YP09.r_whi YP09.r_wlo]; lia.

(* ---- the registers a boundary names on B' (crt_dregs_B: crt_bregs_B's eleven and doc in s6), kept across a call
   (aregs_preserved) or by a run that does not write them: Crt102Arms' arms_dregs_pres / arms_dregs_eq at B''s
   registers (sp gp tp s0 s1 s2 s4 s3 s7 s9 s11, s6), read by projection and built by named literal ---- *)
Definition CRTB_DREGS : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 27]%bv.
Lemma crtb_dregs_pres : forall rg rg' F, DREGS rg F -> aregs_preserved rg rg' -> DREGS rg' F.
Proof.
intros rg rg' F HDR HP.
pose proof (crt_dregs_B_bregs HDR) as HBR.
refine {| crt_dregs_B_bregs := _; crt_dregs_B_s6 := _ |}.
- refine {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _; crt_bregs_B_s0 := _; crt_bregs_B_s1 := _;
            crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _; crt_bregs_B_s7 := _; crt_bregs_B_s9 := _;
            crt_bregs_B_s11 := _ |}.
  + rewrite (ts_ap rg rg' 2%bv HP) by ts_cs. exact (crt_bregs_B_sp HBR).
  + rewrite (ts_ap rg rg' 3%bv HP) by ts_cs. exact (crt_bregs_B_gp HBR).
  + rewrite (ts_ap rg rg' 4%bv HP) by ts_cs. exact (crt_bregs_B_tp HBR).
  + rewrite (ts_ap rg rg' 8%bv HP) by ts_cs. exact (crt_bregs_B_s0 HBR).
  + rewrite (ts_ap rg rg' 9%bv HP) by ts_cs. exact (crt_bregs_B_s1 HBR).
  + rewrite (ts_ap rg rg' 18%bv HP) by ts_cs. exact (crt_bregs_B_s2 HBR).
  + rewrite (ts_ap rg rg' 20%bv HP) by ts_cs. exact (crt_bregs_B_s4 HBR).
  + rewrite (ts_ap rg rg' 19%bv HP) by ts_cs. exact (crt_bregs_B_s3 HBR).
  + rewrite (ts_ap rg rg' 23%bv HP) by ts_cs. exact (crt_bregs_B_s7 HBR).
  + rewrite (ts_ap rg rg' 25%bv HP) by ts_cs. exact (crt_bregs_B_s9 HBR).
  + rewrite (ts_ap rg rg' 27%bv HP) by ts_cs. exact (crt_bregs_B_s11 HBR).
- rewrite (ts_ap rg rg' 22%bv HP) by ts_cs. exact (crt_dregs_B_s6 HDR).
Qed.
Lemma crtb_dregs_eq : forall rg rg' F, DREGS rg F -> (forall r, In r CRTB_DREGS -> getr rg' r = getr rg r) ->
  DREGS rg' F.
Proof.
intros rg rg' F HDR HK.
pose proof (crt_dregs_B_bregs HDR) as HBR. unfold CRTB_DREGS in HK.
refine {| crt_dregs_B_bregs := _; crt_dregs_B_s6 := _ |}.
- refine {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _; crt_bregs_B_s0 := _; crt_bregs_B_s1 := _;
            crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _; crt_bregs_B_s7 := _; crt_bregs_B_s9 := _;
            crt_bregs_B_s11 := _ |}.
  + rewrite (HK 2%bv) by (cbn [In]; tauto). exact (crt_bregs_B_sp HBR).
  + rewrite (HK 3%bv) by (cbn [In]; tauto). exact (crt_bregs_B_gp HBR).
  + rewrite (HK 4%bv) by (cbn [In]; tauto). exact (crt_bregs_B_tp HBR).
  + rewrite (HK 8%bv) by (cbn [In]; tauto). exact (crt_bregs_B_s0 HBR).
  + rewrite (HK 9%bv) by (cbn [In]; tauto). exact (crt_bregs_B_s1 HBR).
  + rewrite (HK 18%bv) by (cbn [In]; tauto). exact (crt_bregs_B_s2 HBR).
  + rewrite (HK 20%bv) by (cbn [In]; tauto). exact (crt_bregs_B_s4 HBR).
  + rewrite (HK 19%bv) by (cbn [In]; tauto). exact (crt_bregs_B_s3 HBR).
  + rewrite (HK 23%bv) by (cbn [In]; tauto). exact (crt_bregs_B_s7 HBR).
  + rewrite (HK 25%bv) by (cbn [In]; tauto). exact (crt_bregs_B_s9 HBR).
  + rewrite (HK 27%bv) by (cbn [In]; tauto). exact (crt_bregs_B_s11 HBR).
- rewrite (HK 22%bv) by (cbn [In]; tauto). exact (crt_dregs_B_s6 HDR).
Qed.

(* ---- T (+0x1c8 .. +0x1e8): UBSan's alignment test of doc (passes: doc is 8-aligned), ASan's shadow test of
   doc->type (passes: doc's 56 bytes are addressable, so its first granule's shadow is 0), `lw a0, 0(s6)` the tag,
   `bne a0, 6`: on 6 the fall-through U (+0x1ec, crt_at_U_B), otherwise C3 (+0x268: `li s5, 0`, `j J`). Both exits
   are r = 0 ones: the room position after both calls (rtt2's exact advance, `hist2` below), copy's blocks against
   tblk UP TO PERMUTATION (crtb_tblk_perm, from rtt1's size permutation), copy's ORDERED free list at every depth bound
   (C3's J field at nn := DOC_D; U's crt_at_U_B_copy_fo) and, at U, copy's cap word, which gives crt_at_U_B_copy_cap
   by the glue's bridge Crt102Glue.crt_copy_cap_of_ncap48. The live state is at 64 = 32 + 32 (both calls spent):
   U_B takes it at 64, J_B at 66, so C3 steps up by crtb_live_mono (crtb_kb_rtt2) ---- *)
Lemma crtb_at_T : forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg,
  frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
  LIVE (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc 0
    ran ->
  DREGS rg (frame_addr lyc CRT_CID pos) ->
  COPYT Wc memc Lamc (frame_addr lyc CRT_CID pos) t Db ->
  (forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) ->
  Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) ->
  Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) ->
  cntc = cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) +
         PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t) ->
  (forall nn, (PjTree.depth t <= nn)%nat -> exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) nn
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Db F /\ map (fun b => snd b + cf_head) F = PresetReqAt.fo t) ->
  (forall ms, t = PjTree.JObj ms -> rd_u64 SEGS (mrestrict (w_H Wc) memc)
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY + 48) (Z.of_nat (PresetReqAt.ncap (length ms)))) ->
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (PresetReqAt.round_trip ReaderRes.jr_strtod t) ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i
    (length (PresetReqAt.round_trip ReaderRes.jr_strtod t)) ->
  (exists hist2, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os
     (rp_i + length (PresetReqAt.rt_text ReaderRes.jr_strtod t false) +
      length (ck_rtt_evs ReaderRes.jr_strtod t true 0))%nat rp_H0 hist2 Sc) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_T_OFF_B rg memc mdc) QFF.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg HFZ HFK HL HDR HCT HFRESH HPERM HLEN HCNTc HFO HN48
  HRUN0 HCONS0 (hist2 & HIFC2).
pose proof (crtb_tblk_perm Db t eq_refl HPERM) as HTB.
destruct (crt_live_journal HL) as (WS & HJ & HB). pose proof (crt_live_memnorm HL) as HMNc.
pose proof (crt_dregs_B_s6 HDR) as R22. pose proof (crt_bregs_B_s11 (crt_dregs_B_bregs HDR)) as R27.
destruct (crtb_doc_bytes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL) as [Hsh Hty].
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
destruct (crtb_ssT_entry fxk Wc memc rg R22 R27 Hsh Hty) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [w64 (shadow_addr doc); w64 (PjTree.tag t)])) by apply te_env.
assert (E65 : ew (TE regs rg [w64 (shadow_addr doc); w64 (PjTree.tag t)]) 65 = w64 (PjTree.tag t))
  by exact (te_more_lt regs rg _ 1 ltac:(lia)).
pose proof (cm_tag_range t) as Htg.
pose proof HMNc as HPM.
(* the runs carry the journal at its budget WS (Crt102Kit's AJW runners) *)
pose (RUN := @Crt102Kit.crt_run_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS).
pose (RUNTO := @Crt102Kit.crt_run_to_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS).
pose (BR := YSRrG.paj_branchR (PI := PA) RZW).
unfold crt_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM (2 ^ 63, 2 ^ 63).
{ awr_ok_tac. }
pose proof HF as HF1. clear HF HFr HG.
apply crtb_frame_ro in HF1; [|crtb_ro]. cbn [ms_mem mkst] in HF1. rename ms into msM.
psrr_branch_tok RUN BR HS SHOK (2 ^ 63, 2 ^ 63).
- (* doc->type <> 6: C3, `li s5, 0` and the join *)
  rewrite branch_ne_U, (U_atom _ 65 (PjTree.tag t) E65), U_SLit in Hc by lia.
  rewrite (zcanon_id 6) in Hc by (unfold M64; lia). apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (2 ^ 63, 2 ^ 63) (CRT_PC_B + CRT_J_OFF_B).
  { awr_ok_tac. }
  pose proof HF as HF2. clear HF HFr HG.
  apply crtb_frame_ro in HF2; [|crtb_ro]. cbn [ms_mem mkst] in HF2.
  pmkst HS.
  assert (KR : forall rr : bv 5, In rr CRTB_DREGS -> getr (ms_regs ms) rr = getr rg rr).
  { intros rr Hr. unfold CRTB_DREGS in Hr. cbv [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [crtb_keep HS |]). destruct Hr. }
  prreg HS (21%bv : bv 5) R21.
  lazymatch goal with |- context [{| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |}] =>
    change n with (CRT_PC_B + CRT_J_OFF_B) end.
  rewrite HF2, HF1 in HJ, HPM |- *.
  apply (TAIL fxk lyc Sc Hpc Wc memc _ kj pos Lamc peakc cntc 0 ran Db (ms_regs ms) 0).
  (* J_B's budget: THE C3 STEP UP, 64 -> 66 = prh_wk F_check_round_trip (crtb_live_mono, crtb_kb_rtt2) *)
  refine {| crt_at_J_B_live := crtb_live_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (crtb_live_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ HB) crtb_kb_rtt2; crt_at_J_B_frm_zero := HFZ;
            crt_at_J_B_fregs := HFK; crt_at_J_B_bregs := crt_dregs_B_bregs (crtb_dregs_eq rg (ms_regs ms) _ HDR KR);
            crt_at_J_B_ret := _; crt_at_J_B_copy_fd := _; crt_at_J_B_r0 := eq_refl; crt_at_J_B_count := _ |}.
  + rewrite R21. reflexivity.
  + exact (crtb_fd_mono SEGS _ _ _ _ _ _ (cm_in_depth_doc x t HIN) (crtb_nodeR_fd SEGS t _ _ _ _ HCT)).
  + (* the count: both calls exact, no object term (cm_arm_C3); the room position: round_trip's tail, pj_free (&copy)
       (crtb_pos_J); copy's tree is t (crt_tree_J of a non-object), its blocks against tblk t up to permutation, its
       ordered free list at the field's depth DOC_D (the every-depth form at nn := DOC_D, depth t <= DOC_D by
       Crt102Model.cm_in_depth_doc), its depth below DOC_D *)
    exists 0. split; [lia|]. split; [intros ms0 _ _; reflexivity|]. right.
    rewrite (crtb_tree_J_nobj t (cm_tag_nobj t Hc)).
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite HCNTc; exact (cm_arm_C3 t 0 cnt _ _ (cm_tag_nobj t Hc) eq_refl eq_refl)|].
    split; [exact (crtb_pos_J Sc hist2 (cm_tag_nobj t Hc) HRUN0 HCONS0 HIFC2)|].
    split; [exact HCT|]. split; [exact HTB|].
    split; [exact (HFO DOC_D (cm_in_depth_doc x t HIN))|]. exact (cm_in_depth_doc x t HIN).
- (* doc->type = 6: the fall-through U, the head of the inlined round_trip_rewrite *)
  rewrite branch_ne_U, (U_atom _ 65 (PjTree.tag t) E65), U_SLit in Hc by lia.
  rewrite (zcanon_id 6) in Hc by (unfold M64; lia). apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  destruct (cm_tag_obj t Hc) as [msx Etx].
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (2 ^ 63, 2 ^ 63) (CRT_PC_B + CRT_U_OFF_B).
  { awr_ok_tac. }
  pose proof HF as HF2. clear HF HFr HG.
  apply crtb_frame_ro in HF2; [|crtb_ro]. cbn [ms_mem mkst] in HF2.
  pmkst HS.
  assert (KR : forall rr : bv 5, In rr CRTB_DREGS -> getr (ms_regs ms) rr = getr rg rr).
  { intros rr Hr. unfold CRTB_DREGS in Hr. cbv [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [crtb_keep HS |]). destruct Hr. }
  lazymatch goal with |- context [{| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |}] =>
    change n with (CRT_PC_B + CRT_U_OFF_B) end.
  rewrite HF2, HF1 in HJ, HPM |- *.
  pose proof (crtb_live_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ HB) as HL'.
  apply (REWR fxk lyc Sc Hpc Wc memc _ kj pos Db Lamc peakc cntc (ms_regs ms) msx).
  refine {| crt_at_U_B_live := HL'; crt_at_U_B_frm_zero := HFZ; crt_at_U_B_fregs := HFK;
            crt_at_U_B_dregs := crtb_dregs_eq rg (ms_regs ms) _ HDR KR; crt_at_U_B_obj := Etx;
            crt_at_U_B_tree_ok := crtb_tree_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL';
            crt_at_U_B_copy := HCT; crt_at_U_B_db_fresh := HFRESH; crt_at_U_B_db_lsz := HPERM;
            crt_at_U_B_db_nlive := HLEN; crt_at_U_B_cnt := HCNTc;
            (* the room position after both calls: the rewrite and pj_free (&copy) are left (crtb_pos_U) *)
            crt_at_U_B_pos := crtb_pos_U Sc hist2 msx Etx HRUN0 HCONS0 HIFC2;
            (* copy's blocks against tblk t up to permutation (crtb_tblk_perm) *)
            crt_at_U_B_copy_tblk := HTB;
            (* copy's header cap: its cap word (rtt1's CAP, kept across rtt2) through the glue's bridge *)
            crt_at_U_B_copy_cap := fun ty num str kids keys n cap Hh =>
              crt_copy_cap_of_ncap48 SEGS (w_H Wc) memc _ msx ty num str kids keys n cap (HN48 msx Etx) Hh;
            (* copy's ordered free list at every depth bound (rtt1's FREEORD-COPY, kept across rtt2); t = JObj msx *)
            crt_at_U_B_copy_fo := _ |}.
  intros _ nn Hd. rewrite <- Etx in Hd |- *. exact (HFO nn Hd).
Qed.

(* ---- copy's footprint across rtt2 (copy = NULL, so FP = []): the journal keeps copy's node (the frame clause: a slot
   of the class-3 frame) and the bytes of its blocks Db (the block clause: harness blocks live at both ends, by the two
   ledgers). Both directions of the byte agreement: forward over the tree's whole footprint (writable after: the frame
   and the blocks are present at the new state), backward over the 56-byte node (writable before: the frame is
   present at the old state). Crt102Arms' arms_copy_agree at B''s live state ---- *)
Lemma crtb_copy_agree : forall lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1
    ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2 kb1 kb2 WS1,
  LIVE kb1 lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ->
  LIVE kb2 ly2 S2 Hp2 W2 mem2 md2' (kj + k1) pos Db Lam2 peak2 cnt2 own2 ran2 ->
  AJW STKR SP1 [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos /\
  (forall a k, prh_lin Lam1 a k -> prh_lin Lam2 a k) /\
  (forall bk, In bk Db -> In bk Lam2) /\
  pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2)
    (pj_footR (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Db) /\
  pj_agreeR SEGS (mrestrict (w_H W2) mem2) (mrestrict (w_H Wc) memc)
    (fun y => frame_addr lyc CRT_CID pos + CRT_OFF_COPY <= y < frame_addr lyc CRT_CID pos + CRT_OFF_COPY + 56).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2
  kb1 kb2 WS1 HL1 HL2 HJ1.
destruct (crt_live_journal HL1) as (WSj & HJ & HBj). pose proof (crt_live_lam_perm HL1) as HPm1.
pose proof (crt_frame_present (crt_live_frame HL1)) as Hfp1.
pose proof (crt_side_ledger (crt_live_side HL1)) as HLED1.
destruct (crt_live_journal HL2) as (? & (HAR2 & _) & _). pose proof (crt_live_lam_perm HL2) as HPm2.
pose proof (crt_frame_present (crt_live_frame HL2)) as Hfp2.
pose proof (crt_side_ledger (crt_live_side HL2)) as HLED2.
pose proof HJ1 as (_ & HLY1 & _ & _ & _ & _ & _ & _ & _ & G2 & _ & G4 & _).
destruct (alx_layout SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc ly2 (proj1 HJ) HLY1) as (_ & Efa & _).
destruct (crtb_frame_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL1) as (Hin3 & _).
rewrite (Efa CRT_CID pos) in Hfp2.
assert (HDL : forall bk, In bk Db -> In bk Lam1 /\ In bk Lam2).
{ intros bk Hbk. split; [apply (Permutation_in _ (Permutation_sym HPm1)) | apply (Permutation_in _ (Permutation_sym HPm2))];
  apply in_or_app; left; exact Hbk. }
assert (Kfr : forall y, frame_addr lyc CRT_CID pos + CRT_OFF_COPY <= y < frame_addr lyc CRT_CID pos + CRT_OFF_COPY + 56 ->
  aview SEGS (w_H W2) mem2 y = aview SEGS (w_H Wc) memc y).
{ intros y Hy. apply (G4 CRT_CID pos y Hin3); [|apply inFP_nil].
  left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes CRT_CID) with 512. unfold CRT_OFF_COPY in Hy. lia. }
split; [exact (Efa CRT_CID pos)|].
split.
{ intros a k Hk. unfold prh_lin in *. apply (Permutation_in _ (Permutation_sym HPm2)).
  apply (Permutation_in _ HPm1) in Hk. exact Hk. }
split; [intros bk Hbk; exact (proj2 (HDL bk Hbk))|].
split.
- intros y Hy. destruct Hy as [Hy | ([a k] & Hb & Hy)].
  + split.
    * apply (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2). exact (Kfr y Hy).
    * intros _. apply apresent_writable. apply Hfp2. change (fs_frame_bytes CRT_CID) with 512. unfold CRT_OFF_COPY in Hy. lia.
  + unfold pj_holdsR in Hy. cbn [fst snd] in Hy. destruct (HDL _ Hb) as [Hb1 Hb2].
    pose proof (proj1 (Forall_forall _ _)
      (prh_ledger_blocks B lyc Sc Hpc Wc memc Lam1 peak1 cnt1 SIZE_MAXZ ran1 most own1 HLED1) _ Hb1)
      as (Hk0 & Hab1 & Hhp1 & H161 & Hhd1). cbn [fst snd] in Hk0, Hab1.
    pose proof (proj1 (Forall_forall _ _)
      (prh_ledger_blocks B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 most own2 HLED2) _ Hb2)
      as (Hk02 & Hab2 & Hhp2 & H162 & Hhd2). cbn [fst snd] in Hab2.
    change (@cf_head CfParams_preset) with 16 in Hab1, Hab2.
    assert (Hrq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
    split.
    * apply (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2).
      replace y with ((a - 16) + (y - a + 16)) by lia. apply (G2 _ _ _ Hab1 Hab2); [rewrite Hrq; lia | apply inFP_nil].
    * intros _. apply apresent_writable.
      destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 _ _ _ HAR2 Hab2) as (_ & _ & _ & _ & Hpres & _).
      rewrite Hrq in Hpres. exact (proj1 (Hpres y ltac:(lia))).
- intros y Hy. split.
  + apply (mbyte_of_aview SEGS (w_H W2) (w_H Wc) mem2 memc). symmetry. exact (Kfr y Hy).
  + intros _. apply apresent_writable. apply Hfp1. change (fs_frame_bytes CRT_CID) with 512. unfold CRT_OFF_COPY in Hy. lia.
Qed.

(* ---- copy's compact tree across rtt2 - this is how crt_copy_tree survives the second call ---- *)
Lemma crtb_copy_keep : forall lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1
    ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2 kb1 kb2 WS1,
  LIVE kb1 lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ->
  LIVE kb2 ly2 S2 Hp2 W2 mem2 md2' (kj + k1) pos Db Lam2 peak2 cnt2 own2 ran2 ->
  AJW STKR SP1 [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  COPYT Wc memc Lam1 (frame_addr lyc CRT_CID pos) t Db ->
  COPYT W2 mem2 Lam2 (frame_addr ly2 CRT_CID pos) t Db.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2
  kb1 kb2 WS1 HL1 HL2 HJ1 HCT.
destruct (crtb_copy_agree lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ly2 S2 Hp2 W2 mem2 md2 md2' k1
  Lam2 peak2 cnt2 own2 ran2 kb1 kb2 WS1 HL1 HL2 HJ1) as (EF & Hlin & _ & Hag & _).
unfold crt_copy_tree in *. rewrite EF.
apply (crtb_nodeR_lblk SEGS t _ (prh_lin Lam1)); [exact Hlin|].
exact (pj_nodeR_frame SEGS t _ _ (prh_lin Lam1) _ Db HCT Hag).
Qed.

(* ---- copy's ordered free list across rtt2, at every depth bound nn above dd (PRH_PjOrder.pj_foR_frame over the same
   agreement) ---- *)
Lemma crtb_fo_keep : forall lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1
    ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2 (dd : nat) (Fo : list Z) kb1 kb2 WS1,
  LIVE kb1 lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ->
  LIVE kb2 ly2 S2 Hp2 W2 mem2 md2' (kj + k1) pos Db Lam2 peak2 cnt2 own2 ran2 ->
  AJW STKR SP1 [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall nn, (dd <= nn)%nat -> exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lam1) nn
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Db F /\ map (fun b => snd b + cf_head) F = Fo) ->
  forall nn, (dd <= nn)%nat -> exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) nn
     (frame_addr ly2 CRT_CID pos + CRT_OFF_COPY) Db F /\ map (fun b => snd b + cf_head) F = Fo.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2
  dd Fo kb1 kb2 WS1 HL1 HL2 HJ1 HFO nn Hnn.
destruct (HFO nn Hnn) as (Fc & HFo & HM).
destruct (crtb_copy_agree lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ly2 S2 Hp2 W2 mem2 md2 md2' k1
  Lam2 peak2 cnt2 own2 ran2 kb1 kb2 WS1 HL1 HL2 HJ1) as (EF & _ & HDL2 & Hag & _).
rewrite EF. exists Fc. split; [|exact HM].
apply (PRH_PjOrder.pj_foR_frame SEGS nn _ _ (prh_lin Lam1) (prh_lin Lam2) _ Db Fc HFo); [|exact Hag].
intros a k Hin. unfold prh_lin. exact (HDL2 (a, k) Hin).
Qed.

(* ---- copy's cap word across rtt2: its eight bytes are bytes 48 .. 55 of copy's node, which the forward agreement
   keeps (PRH_Reader.rd_u64_frame) ---- *)
Lemma crtb_n48_keep : forall lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1
    ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2 (N : Z) kb1 kb2 WS1,
  LIVE kb1 lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ->
  LIVE kb2 ly2 S2 Hp2 W2 mem2 md2' (kj + k1) pos Db Lam2 peak2 cnt2 own2 ran2 ->
  AJW STKR SP1 [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY + 48) N ->
  rd_u64 SEGS (mrestrict (w_H W2) mem2) (frame_addr ly2 CRT_CID pos + CRT_OFF_COPY + 48) N.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2
  N kb1 kb2 WS1 HL1 HL2 HJ1 HN.
destruct (crtb_copy_agree lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ly2 S2 Hp2 W2 mem2 md2 md2' k1
  Lam2 peak2 cnt2 own2 ran2 kb1 kb2 WS1 HL1 HL2 HJ1) as (EF & _ & _ & Hag & _).
rewrite EF. apply (rd_u64_frame SEGS _ _ _ N HN).
intros y Hy.
assert (Hf : pj_footR (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Db y) by (left; lia).
exact (proj1 (Hag y Hf)).
Qed.

(* ---- R2 (+0x1c4): `bnez a0, J` after rtt2. a0 <> 0 (C2) is UNREACHABLE: rtt2 returned 0 by tround_trip_text_specX's
   dead r = 1 arm (its post states r = 0 under its entry premise prh_cons_from). a0 = 0: on to T, with copy's tree,
   blocks, ordered free list and cap word; the live state at 64 = 32 + 32 (both calls spent) ---- *)
Lemma crtb_at_R2 : forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg r2,
  frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
  LIVE (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc 0
    ran ->
  DREGS rg (frame_addr lyc CRT_CID pos) -> getr rg 10 = w64 r2 -> r2 = 0 ->
  COPYT Wc memc Lamc (frame_addr lyc CRT_CID pos) t Db ->
  (forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) ->
  Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) ->
  Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) ->
  cntc = cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) +
         PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t) ->
  (forall nn, (PjTree.depth t <= nn)%nat -> exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) nn
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Db F /\ map (fun b => snd b + cf_head) F = PresetReqAt.fo t) ->
  (forall ms, t = PjTree.JObj ms -> rd_u64 SEGS (mrestrict (w_H Wc) memc)
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY + 48) (Z.of_nat (PresetReqAt.ncap (length ms)))) ->
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (PresetReqAt.round_trip ReaderRes.jr_strtod t) ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i
    (length (PresetReqAt.round_trip ReaderRes.jr_strtod t)) ->
  (exists hist2, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os
     (rp_i + length (PresetReqAt.rt_text ReaderRes.jr_strtod t false) +
      length (ck_rtt_evs ReaderRes.jr_strtod t true 0))%nat rp_H0 hist2 Sc) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_R2_OFF_B rg memc mdc) QFF.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg r2 HFZ HFK HL HDR R10 Er2 HCT HFRESH HPERM HLEN
  HCNTc HFO HN48 HRUN0 HCONS0 HPOS2.
subst r2.
destruct (crt_live_journal HL) as (WS & HJ & HB). pose proof (crt_live_memnorm HL) as HMNc.
destruct (crtb_ss0_entry fxk (CRT_PC_B + CRT_R2_OFF_B) Wc memc rg) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
assert (E10 : ew (TE regs rg []) (xr 10) = w64 0).
{ unfold xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. exact R10. }
pose proof HMNc as HPM.
(* the runs carry the journal at its budget WS (Crt102Kit's AJW runners) *)
pose (RUNTO := @Crt102Kit.crt_run_to_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS).
pose (RUN := @Crt102Kit.crt_run_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS).
pose (BR := YSRrG.paj_branchR (PI := PA) RZW).
unfold crt_cfg.
psrr_branch_tok RUN BR HS SHOK (2 ^ 63, 2 ^ 63).
- (* a0 <> 0: C2, UNREACHABLE - rtt2 returned 0 (r2 = 0, the text's dead r = 1 arm) *)
  rewrite branch_ne_U, (U_atom _ 42 0 E10), U_SLit in Hc by lia.
  rewrite (zcanon_id 0) in Hc by (unfold M64; lia). apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  exfalso. exact (Hc eq_refl).
- (* a0 = 0: on to T *)
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (2 ^ 63, 2 ^ 63) (CRT_PC_B + CRT_T_OFF_B).
  { awr_ok_tac. }
  pose proof HF as HF2. clear HF HFr HG.
  apply crtb_frame_ro in HF2; [|crtb_ro]. cbn [ms_mem mkst] in HF2.
  pmkst HS.
  assert (KR : forall rr : bv 5, In rr CRTB_DREGS -> getr (ms_regs ms) rr = getr rg rr).
  { intros rr Hr. unfold CRTB_DREGS in Hr. cbv [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [crtb_keep HS |]). destruct Hr. }
  lazymatch goal with |- context [{| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |}] =>
    change n with (CRT_PC_B + CRT_T_OFF_B) end.
  rewrite HF2 in HJ, HPM |- *.
  exact (crtb_at_T fxk lyc Sc Hpc Wc memc _ kj pos Db Lamc peakc cntc (ms_regs ms) HFZ HFK
    (crtb_live_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ HB) (crtb_dregs_eq rg (ms_regs ms) _ HDR KR) HCT HFRESH
    HPERM HLEN HCNTc HFO HN48 HRUN0 HCONS0 HPOS2).
Qed.

(* ---- R1 (+0x1a4): `beqz a0, +0x1b0` after rtt1. a0 <> 0 (C1) is UNREACHABLE: rtt1 returned 0 by the text's dead
   r = 1 arm. a0 = 0: `li a1, 1`, `li s5, 1`, `mv a0, s6`, `li a2, 0`, rtt2 (doc, 1, NULL) at +0x1c0, then R2. rtt2 is
   made at the position rtt1's exact advance left (`hist1`), with round_trip's second piece as its run events and its
   consumer window (ck_rtt_evs_supply / crtb_cons_split, from the run premise and the window crt_pos carries); copy's
   tree, ordered free list and cap word cross it (crtb_copy_keep / crtb_fo_keep / crtb_n48_keep). The call is
   crtb_rtt_call, so this lemma takes its premise crtb_wild_budget. The live state is at 32 = prh_wk
   F_round_trip_text (rtt1 spent); rtt2 is made at kb = 32 (crtb_kb_rtt2) and lands at 64 ---- *)
Lemma crtb_at_R1 : crtb_wild_budget -> forall fxk lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc rg r1,
  frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
  LIVE (prh_wk F_round_trip_text) lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 ran ->
  DREGS rg (frame_addr lyc CRT_CID pos) -> getr rg 10 = w64 r1 -> r1 = 0 ->
  cntc = cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) ->
  COPYT Wc memc Lamc (frame_addr lyc CRT_CID pos) t Dx ->
  (forall a k, In (a, k) Dx -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) ->
  Permutation (map snd Dx) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) ->
  Z.of_nat (length Dx) = ReaderRes.nlive (PjRoundTrip.ttrace t) ->
  (forall nn, (PjTree.depth t <= nn)%nat -> exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) nn
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dx F /\ map (fun b => snd b + cf_head) F = PresetReqAt.fo t) ->
  (forall ms, t = PjTree.JObj ms -> rd_u64 SEGS (mrestrict (w_H Wc) memc)
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY + 48) (Z.of_nat (PresetReqAt.ncap (length ms)))) ->
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (PresetReqAt.round_trip ReaderRes.jr_strtod t) ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i
    (length (PresetReqAt.round_trip ReaderRes.jr_strtod t)) ->
  (exists hist1, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os
     (rp_i + length (PresetReqAt.rt_text ReaderRes.jr_strtod t false))%nat rp_H0 hist1 Sc) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_R1_OFF_B rg memc mdc) QFF.
Proof.
intros HGAP fxk lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc rg r1 HFZ HFK HL HDR R10 Er1 Hcnt HCT HFRESH HPERM
  HLEN HFO HN48 HRUN0 HCONS0 (hist1 & HIFC1).
subst r1.
destruct (crt_live_journal HL) as (WS & HJ & HB). pose proof (crt_live_lam_perm HL) as HPm.
pose proof (crt_live_blocks_perm HL) as HPab. pose proof (crt_live_dx_apart HL) as HDap.
pose proof (crt_live_memnorm HL) as HMNc.
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
destruct (crtb_ss0_entry fxk (CRT_PC_B + CRT_R1_OFF_B) Wc memc rg) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
assert (E10 : ew (TE regs rg []) (xr 10) = w64 0).
{ unfold xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. exact R10. }
pose proof HMNc as HPM.
(* the runs carry the journal at its budget WS (Crt102Kit's AJW runners) *)
pose (RUNTO := @Crt102Kit.crt_run_to_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS).
pose (RUN := @Crt102Kit.crt_run_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS).
pose (BR := YSRrG.paj_branchR (PI := PA) RZW).
unfold crt_cfg.
psrr_branch_tok RUN BR HS SHOK (2 ^ 63, 2 ^ 63).
- (* a0 = 0: rtt1 returned 0; rtt2 (doc, 1, NULL) *)
  assert (Hc0 : frame_addr lyc CRT_CID pos + CRT_OFF_COPY <> 0).
  { destruct (crtb_frame_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL) as (_ & _ & Fb1 & _). cbv zeta in Fb1.
    unfold CRT_OFF_COPY. lia. }
  (* rtt2's run events and consumer window: round_trip's second piece, after rtt1's (the copy pointer is not NULL) *)
  pose proof (proj2 (ck_rtt_evs_supply ReaderRes.jr_strtod rp_x rp_os rp_i t _ Hc0 HRUN0)) as HRUN2.
  pose proof (proj2 (crtb_cons_split _ Hc0 HCONS0)) as HCONS2.
  rewrite (crtb_ck_rtt_nz ReaderRes.jr_strtod t false _ Hc0) in HRUN2, HCONS2.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM (2 ^ 63, 2 ^ 63).
  { awr_ok_tac. }
  pose proof HF as HF2. clear HF HFr HG.
  apply crtb_frame_ro in HF2; [|crtb_ro]. cbn [ms_mem mkst] in HF2.
  assert (KR : forall rr : bv 5, In rr CRTB_DREGS -> getr (ms_regs ms) rr = getr rg rr).
  { intros rr Hr. unfold CRTB_DREGS in Hr. cbv [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [crtb_keep HS |]). destruct Hr. }
  assert (Ra0 : getr (ms_regs ms) 10 = getr rg 22) by crtb_keep HS.
  prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
  pose proof (crtb_dregs_eq rg (ms_regs ms) _ HDR KR) as HDR'.
  lazymatch goal with |- context [{| cfg_ms := _; cfg_model := ?mdq |}] =>
    assert (HL' : LIVE (prh_wk F_round_trip_text) lyc Sc Hpc Wc (ms_mem ms) mdq kj pos Dx Lamc peakc cntc 0 ran)
      by (rewrite HF2; apply (crtb_live_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WS HL);
          [rewrite <- HF2; exact HJ | exact HB]) end.
  (* rtt2 at kb = prh_wk F_round_trip_text: 32 + 32 <= 66 *)
  apply (crtb_rtt_call HGAP fxk 1 0 CRT_R2_OFF_B Wc _ _ ms _ lyc Sc Hpc kj pos Dx Lamc peakc cntc
    (rp_i + length (PresetReqAt.rt_text ReaderRes.jr_strtod t false))%nat hist1 (prh_wk F_round_trip_text) HFZ HS
    eq_refl eq_refl HL' crtb_kb_rtt2 HDR').
  + rewrite Ra0. exact (crt_dregs_B_s6 HDR).
  + rewrite Ra1. reflexivity.
  + rewrite Ra2. reflexivity.
  + right. reflexivity.
  + right. reflexivity.
  + rewrite Rra. reflexivity.
  + left. reflexivity.
  + pose proof (cm_pre1 t 0 ltac:(lia)). pose proof (cm_in_count x t 0 HIN ltac:(lia)). lia.
  + exact (cm_rqa_rtt1 t most HRQA).
  + rewrite (blocks_bytes_bsum B lyc Sc), (bsum_perm _ _ HPab), bsum_app, <- (blocks_bytes_bsum B ly S).
    change (negb (1 =? 0)) with true.
    pose proof (cm_live_rtt1_copy t Dx (cm_in_wf x t HIN) HPERM HLEN). lia.
  + exact (cm_rq_rtt1 t HRQ).
  + exact HIFC1.
  + exact HRUN2.
  + exact HCONS2.
  + intros fx' ly3 S3 Hp3 W3 regs3 mem3 md3 k1 WS3 WS31 HFZ3 HFK3 HJ3 HB3 HJ1 HP HQ HMN3.
    rewrite HF2 in HJ1, HMN3, HL'.
    (* rtt2's post, the text's own form (crtb_rtt_Q at copy = 0), opened by named conjuncts: the r = 1 arm is dead
       (HR0 : r2 = 0) *)
    destruct HQ as (HROOM3 & Lam3 & peak3 & cnt3 & ran3 & own3 & HLED3 & Hpk3 & HND3 & r2 & R10' & HR0 & Harm2).
    destruct Harm2 as [(Er2 & Hown3 & HPL3' & HPab3' & Hc3' & Hkeep3)
                      | (Er2 & Hown3 & Hc3 & Hran3 & Hpos3 & Hc00 & Hcopy3)]; [exfalso; lia|].
    destruct (Hc00 eq_refl) as [HPL3 HPab3].
    subst own3 ran3.
    pose proof HJ1 as (_ & HLY1 & _).
    destruct (crt_live_journal HL') as (? & (HARl & _) & _).
    destruct (alx_layout SEGS B ARx LAWS lyc Sc Hpc Wc memc _ ly3 HARl HLY1) as (_ & Efa & _).
    assert (HL3 : LIVE (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat ly3 S3 Hp3 W3 mem3 md3 (kj + k1) pos
      Dx Lam3 peak3 cnt3 0 ran).
    { apply (crtb_live_after lyc Sc Hpc Wc memc _ kj pos Dx Lamc peakc cntc 0 ran 0 ly3 S3 Hp3 W3 mem3 md3 k1 Dx
        Lam3 peak3 cnt3 0 ran _ _ _ _ HL' (or_introl eq_refl) HJ3 HB3 HJ1 HMN3 HROOM3 HLED3 Hpk3 HND3).
      - intros bk Hbk. exact (Permutation_in _ (Permutation_sym HPL3) Hbk).
      - exact (perm_trans HPL3 HPm).
      - exact (perm_trans HPab3 HPab).
      - exact HDap. }
    pose proof (crtb_copy_keep lyc Sc Hpc Wc memc _ kj pos Dx Lamc peakc cntc 0 ran ly3 S3 Hp3 W3 mem3 md3 md3 k1
      Lam3 peak3 cnt3 0 ran _ _ _ HL' HL3 HJ1 HCT) as HCT3.
    pose proof (crtb_fo_keep lyc Sc Hpc Wc memc _ kj pos Dx Lamc peakc cntc 0 ran ly3 S3 Hp3 W3 mem3 md3 md3 k1
      Lam3 peak3 cnt3 0 ran (PjTree.depth t) _ _ _ _ HL' HL3 HJ1 HFO) as HFO3.
    assert (HN483 : forall ms, t = PjTree.JObj ms -> rd_u64 SEGS (mrestrict (w_H W3) mem3)
      (frame_addr ly3 CRT_CID pos + CRT_OFF_COPY + 48) (Z.of_nat (PresetReqAt.ncap (length ms)))).
    { intros mso Et. exact (crtb_n48_keep lyc Sc Hpc Wc memc _ kj pos Dx Lamc peakc cntc 0 ran ly3 S3 Hp3 W3 mem3 md3
        md3 k1 Lam3 peak3 cnt3 0 ran _ _ _ _ HL' HL3 HJ1 (HN48 mso Et)). }
    assert (HDR3 : DREGS regs3 (frame_addr ly3 CRT_CID pos)) by (rewrite Efa; exact (crtb_dregs_pres _ _ _ HDR' HP)).
    refine (crtb_at_R2 fx' ly3 S3 Hp3 W3 mem3 md3 (kj + k1) pos Dx Lam3 peak3 cnt3 regs3 r2 HFZ3
      (crtb_fregs_trans _ _ _ HFK HFK3) HL3 HDR3 R10' HR0 HCT3 HFRESH HPERM HLEN _ HFO3 HN483 HRUN0 HCONS0 Hpos3).
    rewrite Hc3, Hcnt. reflexivity.
- (* a0 <> 0: C1, UNREACHABLE - rtt1 returned 0 (r1 = 0, the text's dead r = 1 arm) *)
  rewrite branch_eq_U, (U_atom _ 42 0 E10), U_SLit in Hc by lia.
  rewrite (zcanon_id 0) in Hc by (unfold M64; lia). apply Z.eqb_neq in Hc.
  exfalso. exact (Hc eq_refl).
Qed.

(* ======================================================================================================== *)
(* ---- M (+0x194): `mv a0, s6`, `li a1, 0`, `mv a2, s4`, rtt1 (doc, 0, &copy) at +0x1a0, then R1; from T1's post at M
   -- crt_live at kb = 0 with no block beyond the entry's (Dx = []), the entry's ledger, own = 0, crt_dregs_B, copy the
   zero tree, the copy shadow (crt_live's), and the room position with the whole of round_trip to come (crt_pos Sc
   (round_trip ReaderRes.jr_strtod t), with the consumer window) -- the run reaches QF through crt_at_U_B at U
   (+0x1ec) or crt_at_J_B at J (+0x348) on C3 (Section hypotheses REWR and TAIL). rtt1 is made at kb = 0
   (crtb_kb_rtt1) and lands at 32. Its two last premises: the bridge from rtt1's post in the TEXT's form (crtb_rtt_Q)
   to the form this proof reads (crtb_rtt_Q_k0), which crtb_rrt proves conjunct by conjunct from the cut's text, and
   crtb_wild_budget (the premise of crtb_rtt_call, both calls), which crtb_rrt gives by crtb_wild_budget_goal
   (Crt102Arms' arms_at_M at B''s image) ---- *)
Lemma crtb_at_M : forall fxk lyc Sc Hpc Wc memc mdc kj pos rg,
  frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
  LIVE 0%nat lyc Sc Hpc Wc memc mdc kj pos [] Lam peak cnt 0 ran ->
  DREGS rg (frame_addr lyc CRT_CID pos) ->
  COPYZ Wc memc (frame_addr lyc CRT_CID pos) ->
  CPOS Sc (PresetReqAt.round_trip ReaderRes.jr_strtod t) ->
  (forall ly' S' Hp' W' regs' mem' md',
     crtb_rtt_Q rp_i lyc Sc Wc memc Lam peak cnt ran (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) false
       ly' S' Hp' W' regs' mem' md' ->
     crtb_rtt_Q_k0 rp_i lyc Sc Wc memc Lam peak cnt ran (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) false
       ly' S' Hp' W' regs' mem' md') ->
  crtb_wild_budget ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_M_OFF_B rg memc mdc) QFF.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos rg HFZ HFK HL HDR HZ HPOS HBRIDGE HGAP.
destruct (crtb_pos_entry Sc HPOS) as (hist0 & HIFC0 & HRUN0 & HCONS0).
destruct (crt_live_journal HL) as (WS0 & HJ & HB0). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_blocks_perm HL) as HPab. pose proof (crt_live_memnorm HL) as HMNc.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
destruct (crtb_frame_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL) as (Hin3 & F32 & Fb1 & Fb2 & Fapp & Ffr & Fsh).
cbv zeta in Fb1.
(* rtt1's run events and consumer window: round_trip's first piece (ck_rtt_evs_supply / crtb_cons_split, from the run
   premise and the window crt_pos carries) *)
assert (Hc0 : frame_addr lyc CRT_CID pos + CRT_OFF_COPY <> 0) by (unfold CRT_OFF_COPY; lia).
pose proof (proj1 (ck_rtt_evs_supply ReaderRes.jr_strtod rp_x rp_os rp_i t _ Hc0 HRUN0)) as HRUN1.
pose proof (proj1 (crtb_cons_split _ Hc0 HCONS0)) as HCONS1.
destruct (crtb_ss0_entry fxk (CRT_PC_B + CRT_M_OFF_B) Wc memc rg) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
pose proof HMNc as HPM.
(* the run carries the journal at its budget WS0 (Crt102Kit's AJW runner) *)
pose (RUN := @Crt102Kit.crt_run_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS0).
unfold crt_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM (2 ^ 63, 2 ^ 63).
{ awr_ok_tac. }
pose proof HF as HF2. clear HF HFr HG.
apply crtb_frame_ro in HF2; [|crtb_ro]. cbn [ms_mem mkst] in HF2.
assert (KR : forall rr : bv 5, In rr CRTB_DREGS -> getr (ms_regs ms) rr = getr rg rr).
{ intros rr Hr. unfold CRTB_DREGS in Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [crtb_keep HS |]). destruct Hr. }
assert (Ra0 : getr (ms_regs ms) 10 = getr rg 22) by crtb_keep HS.
assert (Ra2 : getr (ms_regs ms) 12 = getr rg 20) by crtb_keep HS.
prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra.
pose proof (crtb_dregs_eq rg (ms_regs ms) _ HDR KR) as HDR'.
lazymatch goal with |- context [{| cfg_ms := _; cfg_model := ?mdq |}] =>
  assert (HL' : LIVE 0%nat lyc Sc Hpc Wc (ms_mem ms) mdq kj pos [] Lam peak cnt 0 ran)
    by (rewrite HF2; apply (crtb_live_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WS0 HL);
        [rewrite <- HF2; exact HJ | exact HB0]) end.
(* rtt1 at kb = 0 (M at 0): 0 + 32 <= 66 *)
apply (crtb_rtt_call HGAP fxk 0 (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) CRT_R1_OFF_B Wc _ _ ms _ lyc Sc Hpc kj
  pos [] Lam peak cnt rp_i hist0 0%nat HFZ HS eq_refl eq_refl HL' crtb_kb_rtt1 HDR').
- rewrite Ra0. exact (crt_dregs_B_s6 HDR).
- rewrite Ra1. reflexivity.
- rewrite Ra2. exact (crt_bregs_B_s4 (crt_dregs_B_bregs HDR)).
- left. reflexivity.
- left. reflexivity.
- rewrite Rra. reflexivity.
- right. reflexivity.
- lia.
- (* THE REQUEST BOUND of round_trip_text (doc, 0): Crt102Model.cm_rqa_rtt0, from the text's own RQA_crt t <= most *)
  exact (cm_rqa_rtt0 t most HRQA).
- rewrite (blocks_bytes_bsum B lyc Sc), (bsum_perm _ _ HPab), bsum_app, <- (blocks_bytes_bsum B ly S).
  cbn [ck_hblks map YCbq.bsum fold_right]. change (negb (0 =? 0)) with false.
  pose proof (cm_live_rtt0 t (blocks_bytes S) (blocks_bytes S) HLIVE ltac:(lia)). lia.
- exact (cm_rq_rtt0 t HRQ).
- exact HIFC0.
- exact HRUN1.
- exact HCONS1.
- intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 WS WS1 HFZ2 HFK2 HJ2 HB2 HJ1 HP HQ HMN2.
  rewrite HF2 in HJ1, HQ, HMN2, HL'.
  (* rtt1's post as crtb_rtt_Q_k0 (the bridge), opened by named conjuncts: the r = 1 arm is dead (HR0 : r1 = 0) *)
  pose proof (HBRIDGE _ _ _ _ _ _ _ HQ) as HQ0.
  destruct HQ0 as (HROOM2 & Lam2 & peak2 & cnt2 & ran2 & own2 & HLED2 & Hpk2 & HND2 & r1 & R10' & HR0 & Harm1).
  destruct Harm1 as [(Er & Hown2 & HPL2' & HPab2' & Hcnt2' & Hkeep)
                    | (Er & Hown2 & Hcnt2 & Hran2 & Hpos1 & Hz0 & Hcopy)]; [exfalso; lia|].
  subst own2 ran2.
  (* rtt1 returned 0: copy holds the compact read-back tree over Db, its ordered free list, its cap word *)
  destruct (Hcopy Hc0) as (Db & HPL2 & HFR2 & HPERM2 & HRB2 & HLEN2 & HPab2 & HCT2 & HFR1 & HN48).
  pose proof (crtb_fo_of_frees _ _ _ Db (cm_in_wf x t HIN) HFR1) as HFO1.
  pose proof HJ1 as (_ & HLY1 & _).
  destruct (crt_live_journal HL') as (? & (HARl & _) & _).
  destruct (alx_layout SEGS B ARx LAWS lyc Sc Hpc Wc memc _ ly2 HARl HLY1) as (_ & Efa & _).
  assert (HDR2 : DREGS regs2 (frame_addr ly2 CRT_CID pos)) by (rewrite Efa; exact (crtb_dregs_pres _ _ _ HDR' HP)).
  cbn [ck_hblks map] in HPab. rewrite app_nil_r in HPab.
  destruct Hpos1 as (hist1 & HIFC1). change (negb (0 =? 0)) with false in HIFC1.
  rewrite (crtb_ck_rtt_nz ReaderRes.jr_strtod t false _ Hc0) in HIFC1.
  assert (HFRESH : forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)).
  { intros a k Hb Hin. apply (HFR2 a k Hb). apply (Permutation_in _ (Permutation_sym HPab)). exact Hin. }
  assert (HL2 : LIVE (prh_wk F_round_trip_text) ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Db Lam2 peak2 cnt2 0 ran).
  { apply (crtb_live_after lyc Sc Hpc Wc memc _ kj pos [] Lam peak cnt 0 ran
      (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) ly2 S2 Hp2 W2 mem2 md2 k1 Db Lam2 peak2 cnt2 0 ran _ _ _ _ HL'
      (or_intror eq_refl) HJ2 HB2 HJ1 HMN2 HROOM2 HLED2 Hpk2 HND2).
    - intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL2)). apply in_or_app. right. exact Hbk.
    - exact HPL2.
    - exact (perm_trans HPab2 (Permutation_app_tail _ HPab)).
    - intros [a k] Hb HbD. pose proof (HDL _ HbD) as HbL.
      destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lam peak cnt SIZE_MAXZ ran a k most 0 HLED HbL)
        as (Hk0 & Hab & Hhp & H16 & Hhd).
      exact (HFR2 a k Hb Hab). }
  rewrite <- (Efa CRT_CID pos) in HCT2, HFO1, HN48.
  exact (crtb_at_R1 HGAP fx' ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Db Lam2 peak2 cnt2 regs2 r1 HFZ2
    (crtb_fregs_trans _ _ _ HFK HFK2) HL2 HDR2 R10' HR0 Hcnt2 HCT2 HFRESH HPERM2 HLEN2 HFO1 HN48 HRUN0 HCONS0
    (ex_intro _ hist1 HIFC1)).
Qed.

(* ---- THE WILD BUDGET, DISCHARGED (kb round; Crt102Arms' arms_wild_budget_goal at B''s binders): crtb_wild_budget
   from the text's entry room HWR0 (PRH_FnCheck.v:1366). The room: the live state's journal is at a budget WS with
   wfresh [] WS <= kb, so the entry room 66 leaves 66 - wfresh [] WS >= 66 - kb >= 32 at Sc
   (YCbqGwild.ajournal_xw_room, wild_room_le). The landing: the call rule's journal at WS0 ++ WS1 is at the budget
   kb + 32 (YCbqGwild.wbudget_app). ---- *)
Lemma crtb_wild_budget_goal : crtb_wild_budget.
Proof using HWR0.
unfold crtb_wild_budget. intros kb lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc HL Hkb.
destruct (crt_live_journal HL) as (WS & HJ & HB). unfold YCbqGwild.wbudget in HB. split.
- apply (YCbqGwild.wild_room_le _ _ (prh_wk F_check_round_trip - YCbqGwild.wfresh [] WS)); [clear - HB Hkb; lia|].
  eapply YCbqGwild.ajournal_xw_roomR; [exact HJ | exact HWR0 | clear - HB Hkb; lia].
- intros ly2 S2 Hp2 W2 mem2 md2 k1 WS0 WS1 HB0 HB1 HJ2. exists (WS0 ++ WS1). split; [exact HJ2|].
  exact (YCbqGwild.wbudget_app [] kb (prh_wk F_round_trip_text) WS0 WS1 HB0 HB1).
Qed.

(* ======================================================================================================== *)
(* ---- THE SEGMENT LEMMA, row CRT-B-RRT [T2]: from T1's post at M (+0x194, crt_live at kb = 0) the run reaches QF
   through crt_at_U_B at U (+0x1ec) or crt_at_J_B at J (+0x348) on C3. crtb_at_M (Qed) carries M to QF given rtt1's
   post in the form it reads and crtb_wild_budget. This proof carries the text's post (crtb_rtt_Q, the cut's
   tround_trip_text_specX) into that form conjunct by conjunct, the two copy-arm facts from the cut's own conjuncts:
   FREEORD-COPY verbatim (PRH_FnCheck.v 71a8716672:1290-1293) and CAP's cap word as the first conjunct of
   pj_ncapR's object clause (:1301; PRH_Reader.v:247), and gives crtb_wild_budget by crtb_wild_budget_goal. CLOSED
   (kb round). ---- *)
Lemma crtb_rrt : forall fxk lyc Sc Hpc Wc memc mdc kj pos rg,
  frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
  LIVE 0%nat lyc Sc Hpc Wc memc mdc kj pos [] Lam peak cnt 0 ran ->
  DREGS rg (frame_addr lyc CRT_CID pos) ->
  COPYZ Wc memc (frame_addr lyc CRT_CID pos) ->
  CPOS Sc (PresetReqAt.round_trip ReaderRes.jr_strtod t) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_M_OFF_B rg memc mdc) QFF.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos rg HFZ HFK HL HDR HZ HPOS.
apply (crtb_at_M fxk lyc Sc Hpc Wc memc mdc kj pos rg HFZ HFK HL HDR HZ HPOS).
- (* rtt1's post in the text's form, carried conjunct by conjunct into the form crtb_at_M reads *)
  intros ly' S' Hp' W' regs' mem' md' HQ. unfold crtb_rtt_Q_k0. cbv beta.
  destruct HQ as (HR & Lam' & peak' & cnt' & ran' & own' & HLd & Hpk & HNd & r & H10 & Hr0 & Harm).
  split; [exact HR|]. exists Lam', peak', cnt', ran', own'. split; [exact HLd|]. split; [exact Hpk|].
  split; [exact HNd|]. exists r. split; [exact H10|]. split; [exact Hr0|].
  destruct Harm as [H1 | (Er & Ho & Ec & Era & Hpos & Hz0 & Hcopy)]; [left; exact H1 | right].
  split; [exact Er|]. split; [exact Ho|]. split; [exact Ec|]. split; [exact Era|]. split; [exact Hpos|].
  split; [exact Hz0|].
  (* the copy arm's nine conjuncts at the cut, one name each (PRH_FnCheck.v 71a8716672:1265-1301) *)
  intros Hnz. destruct (Hcopy Hnz) as (Db & HPm & Hfr & Hlsz & HRB & HFO & Hnl & HPab & HNd2 & HNC).
  exists Db. split; [exact HPm|]. split; [exact Hfr|]. split; [exact Hlsz|]. split; [exact HRB|].
  split; [exact Hnl|]. split; [exact HPab|]. split; [exact HNd2|].
  (* FREEORD-COPY: the text's free-order conjunct (:1290-1293), the same term *)
  split; [exact HFO|].
  (* CAP's cap word: pj_ncapR at an object is its cap word and its kids' clause (PRH_Reader.v:247-249) *)
  intros ms Et. rewrite Et in HNC. cbn [pj_ncapR] in HNC. destruct HNC as [HCAPW HKIDS]. exact HCAPW.
- (* the wild budget: crtb_wild_budget_goal (from the text's entry room HWR0), the premise of crtb_rtt_call at both
     calls *)
  exact crtb_wild_budget_goal.
Qed.

End g.
End f.
End w.

Print Assumptions crtb_at_M.
(* kb round: the wild budget is discharged, so the segment lemma and its named item are constants (Qed) *)
Check crtb_rrt.
Check crtb_wild_budget_goal.
Print Assumptions crtb_rrt.
Print Assumptions crtb_wild_budget_goal.
