(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: THE SIDE-STACK KIT of the image-A walks. The journal steps a walk of one of link's own
   functions takes at its side-stack calls (frame_alloc_<c>, frame_release_<c>, meta_fill_<v>) and at the inline
   release of a frame of class <= 7, all over the caller's program-global journal `ajournal_gx G XO OUT` of
   lib/A/W_journalG.v (link-a/form/FORM.md (internal record, sha256 13aeff774164) sections 0 and 4.2), and the Post of a
   function that takes and releases one side frame inside the call.

   Every statement here is generic: it names the runtime contract (a Section hypothesis or a premise of the lemma)
   and no address of link. The runtime contracts and their discharge at image A:
     astack_malloc_realizes segs B c      (Reusable/YG0d.v)       classes 0, 1, 3, 4: lib/A/AF0s.v, StackMalloc0.v,
                                                                   lib/A/Rt/StackSideInst.v link_stack_malloc_3 / _4
     astack_malloc_sz_realizes segs B pc c (Reusable/AsStackSz.v)  classes 8, 9: StackSideInst.v link_stack_malloc_8 / _9
     astack_free_realizes segs B pc c     (Reusable/StackFreeDef.v) classes 8, 9: link_stack_free_8 / _9
     aset_shadow_realizes segs B pc v     (Reusable/SetShadowDef.v) lib/A/Rt/SetShadow.v link_set_shadow_00 / _f5 / _f8
   The model laws, the side-stack progress law and the release law of the donor's steps are not hypotheses here: the
   first follows from the journal's AR (`am_universe`, YG05.v model_laws_ok), the second is YG05.v
   stack_malloc_progress, the third YG0t.v astack_free_law_ok. The only extra hypothesis is `api_env segs B` of the
   two frame_alloc steps (the donor's call_effect_journal); a walk has it as LinkPaLib.v `pal_env` of its PALib B.

   Section k (journal steps; Hypotheses LAWS, segs_low; every lemma takes them, `Proof using All`):
   - ajournal_gx_after_write_st: link_ajkit.v's ajournal_gx_after_write for a step that may change the side stack
     (S' with S' = Sc but for the side stack, own2) and write runtime-owned application bytes (the flag byte).
   - ajournal_gx_flag_write: the journal after a store of 0 to the flag byte of the frame at the head of own (the
     inline release, YG0d.v astack_free_law), with the other written bytes ones the journal admits.
   - aj_gx_stack_free_at (c): frame_release_<c> over astack_free_realizes, the ajournal_gx form of
     Reusable/StackFreeJournal.v:166 aj_stack_free_at.
   - aj_gx_set_shadow_at (e): meta_fill_<v> over aset_shadow_realizes, destination in an own side frame's shadow.
   - ajw_kept_call / aframe_shadow_kept_call: a byte the journal lets a callee write, and the shadow of a byte of a
     side frame of Sc, keep their values across a runtime call that gives acall_kept and the raw clause (a), (b).
   - the kept-clause algebra a walk composes its steps with: akept_refl, akept_mono, akept_of_acall_kept, akept_step
     (a step that keeps every byte outside X), akept_trans / akept_trans_ly (a callee's akept at a later allocator
     state, at the same layout or at another layout of the journal: aj_gx_frame_addr);
     ashadow_kept_AR (the heap-block shadow is fixed by AR at both ends); aside_rng and akept_drop_side (the taken
     frame's bytes, its shadow and its flag byte are not bytes akept speaks of); aj_gx_const_cells (the switch cell
     is 1, the fallback arm after `beqz` on it is dead); aj_gx_present (the window is present); aj_gx_awr_frame (a
     byte of an own side frame or of its shadow is one the journal admits: the write obligation of a run).
   - apost_side_gen (f): the Post (link_amem.v apost) of a function that takes and releases one side frame inside the
     call, the LinkWalk.v apost_leaf analogue, at any end layout and world; apost_side: at the call's.
   - apost_leaf_AR: LinkWalk.v apost_leaf without its premise that E lies below SHADOW_OFF (the heap-block shadow
     clause from ashadow_kept_AR), for a leaf whose write set lies in high application memory (a side frame).
   Section m (Hypothesis errno_low : api_env segs B as well):
   - aj_gx_stack_malloc_at (a): frame_alloc_<c> over astack_malloc_realizes (classes <= 7), lifting YC85G.v:296
     aj_stack_malloc_atS.
   - aj_stack_malloc_sz_atS: the donor-journal step over astack_malloc_sz_realizes, ported from
     plugin-hostd/fuzz_command lib/A/Prog/answer_s0.v:180-242 (origin/ossv/recipes; cgif_rgb_fuzzer lib/YC05.v:143 over
     cgif_file_fuzzer's journal), module names and acall_kept_of_journal's arguments as on link.
   - aj_gx_stack_malloc_sz_at (b): its ajournal_gx form (classes 8, 9: kernel, nl_talk).
   Section pe (the PLAIN symbolic engine over ajournal_gx; a run whose stores reach the shadow band, which the token
   engine's sh_static_ok refuses, e.g. the inline poisoning of a class-1 / class-3 frame's shadow):
   - SRr_chain_AJX, SRr_run_pi_AJX, SRr_run_to_pi_AJX, SRr_run_pi_AJX_call, SRr_run_to_pi_AJX_call: pcap's
     SRr_run_pi_AJ (PcapFrame.v) / SRr_run_pi_AJ_call (YC45.v) over ajournal_gx (W_journalG.v ajournal_gx_exec).
   - aj_gx_flag_store_pi / aj_gx_flag_store_to_pi (d): pcap's PcapFrame.v:459 aj_flag_store_pi over ajournal_gx.
   Section g: the instances at LINK's listing (as LinkWalk.v Section g): paj_run_plain_x, paj_run_to_plain_x,
   paj_run_call_plain_x, paj_run_to_call_plain_x, paj_flag_plain_x, paj_flag_to_plain_x.
   Outside the sections: aside_room arithmetic (aside_room_In, aside_room_take, aside_room_sub, aside_room_frames,
   aside_room_push) and the side-stack-only state updates (set_fs_trans, set_fs_of_exists, stack_free_state_set_fs,
   ablocks_set_fs).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YG0p YG08.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import AsStackSz StackFreeDef StackFreeJournal SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG05 YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC85G.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem link_ajkit LinkWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   The side stack's room (link_amem.v aside_room) and the side-stack-only state updates
   ========================================================================== *)

Lemma aside_room_In : forall S SIDE c d, aside_room S SIDE -> In (c, d) SIDE -> count_cid c (frames S) + d <= fs_frames c.
Proof. intros S SIDE c d H Hin. unfold aside_room in H. rewrite Forall_forall in H. exact (H (c, d) Hin). Qed.

(* A (class, depth) entry with depth >= 1 is the room frame_alloc_<class> asks (astack_malloc_realizes). *)
Lemma aside_room_take : forall S SIDE c d, aside_room S SIDE -> In (c, d) SIDE -> 1 <= d ->
  count_cid c (frames S) < fs_frames c.
Proof. intros S SIDE c d H Hin Hd. pose proof (aside_room_In S SIDE c d H Hin). lia. Qed.

(* A callee at the same side stack that needs no more than the caller has. *)
Lemma aside_room_sub : forall S SIDE SIDE',
  (forall c d', In (c, d') SIDE' -> exists d, In (c, d) SIDE /\ d' <= d) -> aside_room S SIDE -> aside_room S SIDE'.
Proof.
intros S SIDE SIDE' Hs H. unfold aside_room in *. rewrite Forall_forall in *. intros [c d'] Hin. cbn [fst snd].
destruct (Hs c d' Hin) as (d & Hd & Hle). pose proof (H (c, d) Hd) as Hc. cbn [fst snd] in Hc. lia.
Qed.

Lemma aside_room_frames : forall S S' SIDE, frames S' = frames S -> aside_room S SIDE -> aside_room S' SIDE.
Proof. intros S S' SIDE E H. unfold aside_room in *. rewrite E. exact H. Qed.

(* After a frame of class c is taken: a callee's room SIDE' fits in the caller's SIDE, one frame of class c fewer. *)
Lemma aside_room_push : forall S S' SIDE SIDE' c p,
  frames S' = (c, p) :: frames S -> aside_room S SIDE ->
  (forall c' d', In (c', d') SIDE' -> exists d, In (c', d) SIDE /\ d' + (if c =? c' then 1 else 0) <= d) ->
  aside_room S' SIDE'.
Proof.
intros S S' SIDE SIDE' c p Hf H Hs. unfold aside_room in *. rewrite Forall_forall in *. intros [c' d'] Hin. cbn [fst snd].
destruct (Hs c' d' Hin) as (d & Hd & Hle). pose proof (H (c', d) Hd) as Hc. cbn [fst snd] in Hc.
rewrite Hf. cbn [count_cid]. destruct (c =? c'); lia.
Qed.

Lemma set_fs_trans : forall S1 S2 Sc, S1 = set_fs (st_fs S1) Sc -> S2 = set_fs (st_fs S2) S1 -> S2 = set_fs (st_fs S2) Sc.
Proof. intros S1 S2 Sc H1 H2. transitivity (set_fs (st_fs S2) S1); [exact H2|]. rewrite H1 at 1. reflexivity. Qed.

Lemma set_fs_of_exists : forall S2 Sc, (exists f, S2 = set_fs f Sc) -> S2 = set_fs (st_fs S2) Sc.
Proof. intros S2 Sc (f & ->). reflexivity. Qed.

Lemma stack_free_state_set_fs : forall cid pos S, stack_free_state cid pos S = set_fs (st_fs (stack_free_state cid pos S)) S.
Proof. intros cid pos S. reflexivity. Qed.

Lemma ablocks_set_fs : forall B ly f S, ablocks B ly (set_fs f S) = ablocks B ly S.
Proof. intros B ly f S. unfold ablocks. rewrite blocks_set_fs. reflexivity. Qed.

(* The run status of a plain run that stopped at no call and no ecall (pcap PcapFrame.v pi_plain_stop). *)
Definition pi_plain_stop {psym : Type} (st : prun_status psym) : Prop :=
  match st with PRS_running | PRS_stopped _ => True | _ => False end.

(* The bytes of a side frame that are not bytes akept speaks of once the frame is released: the frame, its shadow,
   and its flag byte. *)
Definition aside_rng (ly : alayout) (cid pos a : Z) : Prop :=
  in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) \/
  a = flag_addr ly cid pos.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit argument, as in link_amem.v, link_ajkit.v and LinkWalk.v. *)
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

(* ==========================================================================
   Section k: the journal steps
   ========================================================================== *)
Section k.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* The donor journal inside ajournal_gx, at a call whose window [spZ regsT - w, spZ regsT) lies inside the journal's
   window, with the offset of the call's sp from the inner journal's sp0 + XO. *)
Lemma aj_gx_unpack : forall G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k (regsT : bvmap 5 word) w,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  0 <= w -> spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - w -> spZ regsT <= sp0 ->
  exists memS, ajournal segs B (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc W memc mdc k /\
    gagree G (w_H W0) mem memS /\
    (forall a, sp0 <= a < sp0 + XO -> ~ inFP OUT a -> aview segs (w_H W) memc a = aview segs (w_H W0) mem a) /\
    0 <= STK /\ 0 <= XO /\
    spZ regsT = sp0 + XO + (spZ regsT - (sp0 + XO)) /\ (spZ regsT - (sp0 + XO)) mod 16 = 0 /\
    spZ regsT - (sp0 + XO) <= 0 /\ w - (spZ regsT - (sp0 + XO)) <= STK + XO /\
    alloc_ceiling <= sp0 - STK /\ sp0 + XO <= 2 ^ 47.
Proof using SK LAWS segs_low.
intros G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsT w (HSTK & HXO & (memS & HJ & Hag) & Hout)
  Hw H16 Hlo Hhi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
exists memS. split; [exact HJ|]. split; [exact Hag|]. split; [exact Hout|].
split; [exact HSTK|]. split; [exact HXO|]. split; [lia|].
split; [rewrite Zminus_mod, H16, Hal; reflexivity|].
split; [lia|]. split; [lia|]. split; lia.
Qed.

(* link_ajkit.v's ajournal_gx_after_write for a step that may change the side stack (S' is Sc but for st_fs, with
   frames own2 ++ frames S) and may write runtime-owned application bytes outside the image (a frame's flag byte),
   besides the bytes the journal admits. *)
Lemma ajournal_gx_after_write_st : forall G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc'
    (Wr : Z -> Prop) S' own2,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) \/
     inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO) \/
     (aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)) ->
  AR segs B lyc S' Wc memc' mdc' ->
  ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc ->
  frames S' = own2 ++ frames S -> qtight S' ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own2 lyc S' Wc memc' mdc' k.
Proof using SK LAWS segs_low.
intros G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr S' own2
  HG HJX Heqw Hgr Hsame HW HAR' Eab' Esecs' Hnev' Hfrs' HQT'.
destruct HJX as (HSTK & HXO & (memS & HJ & Hag) & Hout).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _ & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HGlow : forall a, inG G a -> 0 <= a < kLowMemEnd) by (intros a Ha; exact (segs_low a (proj1 (HG a Ha)))).
set (memG := fun x : word => if inGb G (bv_unsigned x) then memc' x else memc x).
assert (EG : forall x, inGb G (bv_unsigned x) = true -> memG x = memc' x)
  by (intros x Hx; unfold memG; rewrite Hx; reflexivity).
assert (EN : forall x, inGb G (bv_unsigned x) = false -> memG x = memc x)
  by (intros x Hx; unfold memG; rewrite Hx; reflexivity).
assert (Hgr1 : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memG)).
{ intros x Hx. unfold mrestrict in Hx |- *. destruct (w_H Wc x) eqn:Eh; [exact Hx|].
  destruct (inGb G (bv_unsigned x)) eqn:Eg; [rewrite (EG x Eg) | rewrite (EN x Eg); exact Hx].
  destruct (memc x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
  assert (Hp : apresent (w_H Wc) memc (bv_unsigned x)).
  { unfold apresent. rewrite Z_to_bv_bv_unsigned. split; [exact Eh | exists b; exact Em]. }
  destruct (Hgr _ Hp) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. congruence. }
pose proof (ajournal_rebase segs B LAWS segs_low G (STK + XO) (sp0 + XO) FP ly S W memS md own lyc Sc Wc memc mdc k
  memG HG HJ EN Hgr1) as HJ1.
assert (HJ2 : ajournal segs B (STK + XO) (sp0 + XO) FP ly S W (gover G memS memG) md own2 lyc S' Wc memc' mdc' k).
{ eapply (ajournal_after_write segs B LAWS segs_low (STK + XO) (sp0 + XO) FP ly S W (gover G memS memG) md own
    lyc Sc Wc memG mdc k memc' mdc' (fun a => Wr a /\ ~ inG G a) S' own2 HJ1).
  - intros a Ha Hna. destruct (inGb G (bv_unsigned (Z_to_bv 64 a))) eqn:Eg.
    + apply aview_eq_of. unfold mrestrict. rewrite (EG _ Eg). reflexivity.
    + assert (HnG : ~ inG G a).
      { intros HGa. rewrite unsigned_lit_small in Eg by lia. apply inGb_false in Eg. exact (Eg HGa). }
      rewrite (Heqw a Ha (fun HWa => Hna (conj HWa HnG))).
      symmetry. apply aview_eq_of. unfold mrestrict. rewrite (EN _ Eg). reflexivity.
  - intros a Hp. destruct (inGb G (bv_unsigned (Z_to_bv 64 a))) eqn:Eg.
    + destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- (EG _ Eg). exact Hb.
    + apply Hgr. destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- (EN _ Eg). exact Hb.
  - exact Hsame.
  - intros a [HWa HnG]. destruct (HW a HWa) as [[Haw _] | [HGa | [[_ Hwin] | Hown]]].
    + left. destruct Haw as [Hs | Hrest]; [left; lia | right; exact Hrest].
    + exfalso. exact (HnG HGa).
    + left. left. lia.
    + right. exact Hown.
  - exact HAR'.
  - exact Eab'.
  - exact Esecs'.
  - exact Hnev'.
  - exact Hfrs'.
  - exact HQT'. }
eapply ajournal_gx_pack; [exact HSTK | exact HXO | exact HJ2 | |].
- intros x Hg. unfold mrestrict, gover. rewrite Hg. exact (Hag x Hg).
- intros a Ha Hno.
  assert (HnW : ~ Wr a).
  { intros HWa. destruct (HW a HWa) as [[_ Hn] | [HGa | [[Ho _] | (Ho & _ & _)]]].
    + exact (Hn Ha).
    + pose proof (HGlow a HGa). lia.
    + exact (Hno Ho).
    + pose proof (al_owned_low _ _ LAWS _ _ _ _ _ a HAR Ho). lia. }
  rewrite (Heqw a ltac:(lia) HnW). exact (Hout a Ha Hno).
Qed.

(* THE INLINE RELEASE of the frame at the head of own (class <= 7: a store of 0 to its flag byte through the word
   frame_alloc left at F + fs_frame_bytes cid - 8): pcap's PcapFrame.v:459 aj_flag_store_pi, at the level of the
   journal. The step writes the bytes Wr, each one the journal admits or the flag byte, keeps every hidden byte, and
   leaves 0 in the flag byte. YG0d.v astack_free_law (YG0t.v astack_free_law_ok) gives AR at the release state. *)
Lemma ajournal_gx_flag_write : forall G XO OUT STK sp0 FP ly S W0 mem md own' lyc Sc W memc mdc k cid pos memc' mdc'
    (Wr : Z -> Prop),
  gx_ok segs B G -> 0 <= cid ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memc mdc k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H W) memc' a = aview segs (w_H W) memc a) ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc') ->
  (forall x : word, w_H W x = true -> memc' x = memc x) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a /\ ~ (sp0 <= a < sp0 + XO)) \/
     inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO) \/ a = flag_addr lyc cid pos) ->
  aview segs (w_H W) memc' (flag_addr lyc cid pos) = Some 0 ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W memc' mdc' k.
Proof using SK LAWS segs_low.
intros G XO OUT STK sp0 FP ly S W0 mem md own' lyc Sc W memc mdc k cid pos memc' mdc' Wr
  HG Hcid HJX Heqw Hgrw Hhid Hsame HW Hflag0.
pose proof HJX as (HSTK & HXO & (memS & HJ & _) & _).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & _ & _ & _ & _ & _ & _ & Hstatic & _ & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_flag _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hfp & Hfo & Hfapp & Hflc).
assert (Hfr_rng : app_addr (flag_addr lyc cid pos) /\ ~ in_img segs (flag_addr lyc cid pos)).
{ split; [apply (in_app_addr _ _ _ Hfapp); lia|].
  exact (proj2 (al_client_img _ _ LAWS lyc Sc W memc mdc (flag_addr lyc cid pos) HAR
    (or_intror (or_intror (ex_intro _ cid (ex_intro _ pos (conj Hin eq_refl))))))). }
pose proof (YG05.model_laws_ok (as_universe B) (am_universe _ _ _ _ (proj1 HAR))) as ML.
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (ml_stack_free _ ML Sc cid pos HWF Hin) as (HWF2 & l1 & l2 & E1 & E2).
assert (El1 : l1 = []).
{ destruct l1 as [|f l1']; [reflexivity|]. exfalso.
  rewrite Hfrs in E1. cbn in E1. injection E1 as <- E1'.
  pose proof (sep_frames_pos segs B LAWS lyc Sc W memc mdc (cid, pos) (cid, pos) [] l1' l2 HAR
    ltac:(rewrite Hfrs; cbn; rewrite E1'; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. pose proof (fs_frame_bytes_pos cid Hcid). lia. }
subst l1. cbn in E1, E2. rewrite Hfrs in E1. cbn in E1. injection E1 as E1.
pose proof (same_but_materialized_wvb mdc mdc' Hsame) as Emd.
assert (HAR' : AR segs B lyc (stack_free_state cid pos Sc) W memc' mdc').
{ apply (YG0t.astack_free_law_ok segs B lyc Sc W memc mdc memc' mdc' cid pos HAR Hin).
  - exact Hflag0.
  - intros a Ha Ho Hne. apply Heqw; [exact Ha|]. intros HWa.
    destruct (HW a HWa) as [[Hw _] | [HGa | [[_ Hwin] | Hfl]]].
    + assert (Hw' : awr_byte (STK + XO) (sp0 + XO) FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a)
        by (destruct Hw as [Hs | Hrest]; [left; lia | right; exact Hrest]).
      exact (proj1 (awr_byte_cases segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw') Ho).
    + destruct (HG a HGa) as [Hi Hns]. exact (Hns (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR Hi) Ho)).
    + pose proof (al_owned_low _ _ LAWS _ _ _ _ _ a HAR Ho). lia.
    + exact (Hne Hfl).
  - intros a Hv. eapply aview_keeps_vis; [exact Hgrw | exact Hv].
  - rewrite Emd. destruct mdc as [fd [maps lazy mat] io fs proc lim tm]; reflexivity.
  - rewrite Emd. destruct mdc as [fd [maps lazy mat] io fs proc lim tm]; reflexivity.
  - rewrite Emd. destruct mdc as [fd [maps lazy mat] io fs proc lim tm]; reflexivity.
  - intros a _ Hh. exact (Hhid _ Hh). }
apply (ajournal_gx_after_write_st G XO OUT STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memc mdc k
  memc' mdc' Wr (stack_free_state cid pos Sc) own' HG HJX Heqw).
- intros a Ha. eapply apresent_grows; [exact Hgrw | exact Ha].
- exact Hsame.
- intros a Ha. destruct (HW a Ha) as [H | [H | [H | ->]]].
  + left. exact H.
  + right. left. exact H.
  + right. right. left. exact H.
  + right. right. right. split; [exact Hfo | exact Hfr_rng].
- exact HAR'.
- unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
- reflexivity.
- cbn. lia.
- etransitivity; [exact E2 | symmetry; exact E1].
- apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
Qed.

(* The donor-journal step of frame_release_<c>: Reusable/StackFreeJournal.v:166 aj_stack_free_at with the model laws
   derived from the journal's AR, and the post also giving the contract's same_but_materialized. *)
Lemma aj_stack_free_atM : forall pc cid, astack_free_realizes segs B pc cid -> 0 <= cid ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own' lyc Sc mdc k pos n (o : Z) raw,
  ajournal segs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memT mdc k ->
  getr regsT 10 = w64 (frame_addr lyc cid pos) -> getr regsT 11 = w64 n -> 8 <= n <= fs_frame_bytes cid -> n mod 8 = 0 ->
  rdword (aview segs (w_H W) memT) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal segs B STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (forall i, 0 <= i < sf_span cid n -> aview segs (w_H W) mem2 (shadow_addr (frame_addr lyc cid pos) + i) = Some 0xf5) /\
       (forall a, 0 <= a < 2 ^ 64 ->
          ~ (shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + sf_span cid n) ->
          a <> flag_addr lyc cid pos -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a) /\
       same_but_materialized mdc md2).
Proof using SK LAWS segs_low.
intros pc cid ASFR Hcid W regsT memT STK sp0 FP ly S W0 mem md own' lyc Sc mdc k pos n o raw
  HJ Ha0 Ha1 Hn Hn8 Htrail Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof (YG05.model_laws_ok (as_universe B) (am_universe _ _ _ _ (proj1 HAR))) as ML.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memT mdc k regsT o); try eassumption.
  rewrite Hra. exact Hraw. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_flag _ _ LAWS lyc Sc W memT mdc cid pos HAR Hin) as (_ & Hfo & Hfapp & _).
assert (Hfr_rng : app_addr (flag_addr lyc cid pos) /\ ~ in_img segs (flag_addr lyc cid pos)).
{ split; [apply (in_app_addr _ _ _ Hfapp); zlia|].
  exact (proj2 (al_client_img _ _ LAWS lyc Sc W memT mdc (flag_addr lyc cid pos) HAR
    (or_intror (or_intror (ex_intro _ cid (ex_intro _ pos (conj Hin eq_refl))))))). }
destruct (frames_bounds segs B LAWS lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
assert (Hspan : sf_span cid n <= fs_frame_bytes cid / 8).
{ unfold sf_span. destruct (cid <=? 6); [zlia | apply Z.div_le_mono; zlia]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (ml_stack_free _ ML Sc cid pos HWF Hin) as (HWF2 & l1 & l2 & E1 & E2).
assert (El1 : l1 = []).
{ destruct l1 as [|f l1']; [reflexivity|]. exfalso.
  rewrite Hfrs in E1. cbn in E1. injection E1 as <- E1'.
  pose proof (sep_frames_pos segs B LAWS lyc Sc W memT mdc (cid, pos) (cid, pos) [] l1' l2 HAR
    ltac:(rewrite Hfrs; cbn; rewrite E1'; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. pose proof (fs_frame_bytes_pos cid Hcid). zlia. }
subst l1. cbn in E1, E2. rewrite Hfrs in E1. cbn in E1. injection E1 as E1.
eapply SRr_mono.
{ exact (ASFR lyc Sc W regsT memT mdc pos n HPRE Hin Ha0 Ha1 Hn Hn8 Htrail). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr, Hpres2.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write_win segs B LAWS segs_low STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memT mdc k
    mem2 md2
    (fun a => (shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + sf_span cid n)
      \/ a = flag_addr lyc cid pos \/ (sp0 + o - ESTACK <= a < sp0 + o))
    (stack_free_state cid pos Sc) own' HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right; left | right; right]; exact H'.
  - intros a Ha Hp. destruct (Z_lt_ge_dec a (sp0 + o - ESTACK)) as [Hlo|Hlo];
    [|destruct (Z_lt_ge_dec a (sp0 + o)) as [Hhi|Hhi]].
    + eapply (apresent_transfer segs); [zlia | intros Hi; pose proof (segs_low a Hi); zlia | | exact Hp].
      apply Hfr; [zlia | zlia | | zlia]. intros ->. destruct Hfr_rng as [Happ _]. zlia.
    + apply Hpres2. zlia.
    + eapply (apresent_transfer segs); [zlia | intros Hi; pose proof (segs_low a Hi); zlia | | exact Hp].
      apply Hfr; [zlia | zlia | | zlia]. intros ->. destruct Hfr_rng as [Happ _]. zlia.
  - exact Hsame.
  - intros a [Ha | [-> | Ha]].
    + left. right. right. right. exists cid, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. zlia.
    + right. split; [exact Hfo | exact Hfr_rng].
    + left. left. zlia.
  - exact HAR2.
  - unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
  - reflexivity.
  - cbn. zlia.
  - etransitivity; [exact E2 | symmetry; exact E1].
  - apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [exact HP|]. split; [exact Heff|]. split; [exact Hfr|]. split; [exact Hpres2 | exact Hsame].
Qed.

(* (c) FRAME_RELEASE_<c> ON THE JOURNAL: aj_stack_free_atM (Reusable/StackFreeJournal.v:166 aj_stack_free_at) over
   ajournal_gx. The
   frame is the head of own; the journal comes back at own' and stack_free_state cid pos Sc. The call's window is
   stated from its sp, as link_ajkit.v's lifts do. The last clause (presence above the allocator's ceiling) is what
   akept_step asks of a step. *)
Lemma aj_gx_stack_free_at : forall pc cid, astack_free_realizes segs B pc cid -> 0 <= cid ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own' lyc Sc mdc k pos n raw,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memT mdc k ->
  getr regsT 10 = w64 (frame_addr lyc cid pos) -> getr regsT 11 = w64 n -> 8 <= n <= fs_frame_bytes cid -> n mod 8 = 0 ->
  rdword (aview segs (w_H W) memT) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (forall i, 0 <= i < sf_span cid n ->
          aview segs (w_H W) mem2 (shadow_addr (frame_addr lyc cid pos) + i) = Some 0xf5) /\
       (forall a, 0 <= a < 2 ^ 64 ->
          ~ (shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + sf_span cid n) ->
          a <> flag_addr lyc cid pos -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, spZ regsT - ESTACK <= a < spZ regsT -> apresent (w_H W) mem2 a) /\
       (forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
       same_but_materialized mdc md2).
Proof using SK LAWS segs_low.
intros pc cid ASFR Hcid G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own' lyc Sc mdc k pos n raw
  HJX Ha0 Ha1 Hn Hn8 Htrail H16 Hlo Hhi Hgp Htp Hra Hraw.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (aj_gx_unpack G XO OUT STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memT mdc k regsT ESTACK HJX
  ltac:(lia) H16 Hlo Hhi) as (memS & HJ & Hag & Hout & HSTK & HXO & Hsp & Ho16 & Ho0 & Hob & Hceil & H47).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds segs B LAWS lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
destruct (al_flag _ _ LAWS lyc Sc W memT mdc cid pos HAR Hin) as (_ & _ & _ & Hflc).
pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfb0) as Hse.
assert (Hspan : sf_span cid n <= fs_frame_bytes cid / 8).
{ unfold sf_span. destruct (cid <=? 6); [lia | apply Z.div_le_mono; lia]. }
eapply SRr_mono.
{ exact (aj_stack_free_atM pc cid ASFR Hcid W regsT memT (STK + XO) (sp0 + XO) FP ly S W0 memS
    md own' lyc Sc mdc k pos n (spZ regsT - (sp0 + XO)) raw HJ Ha0 Ha1 Hn Hn8 Htrail Hsp Ho16 Ho0 Hob Hgp Htp Hra Hraw). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Heff & Hfr & Hpw & Hsm).
rewrite <- Hsp in Hfr, Hpw.
assert (Hkeep : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a).
{ intros a Ha Hw. apply Hfr; [lia | lia | intros ->; lia | exact Hw]. }
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split.
{ eapply ajournal_gx_pack; [exact HSTK | exact HXO | exact HJ2 | exact Hag |].
  intros a Ha Hno. rewrite (Hkeep a ltac:(lia) ltac:(lia)). exact (Hout a Ha Hno). }
split; [exact HP|]. split; [exact Heff|]. split; [exact Hfr|]. split; [exact Hpw|]. split; [|exact Hsm].
intros a Ha Hp.
destruct (Z_lt_le_dec a (spZ regsT - ESTACK)) as [H1|H1]; [|destruct (Z_lt_le_dec a (spZ regsT)) as [H2|H2]].
- eapply (apresent_transfer segs); [lia | intros Hi; pose proof (segs_low a Hi); lia | apply Hkeep; lia | exact Hp].
- apply Hpw. lia.
- eapply (apresent_transfer segs); [lia | intros Hi; pose proof (segs_low a Hi); lia | apply Hkeep; lia | exact Hp].
Qed.

(* (e) META_FILL_<v> ON THE JOURNAL: aset_shadow_realizes (Reusable/SetShadowDef.v) with destination bytes in the
   shadow of a side frame the journal's owner took (In (cid, pos) own): the ajournal_gx form of cgif_rgb_fuzzer
   lib/YC05.v:206 aj_set_shadow_at, through link_ajkit.v ajournal_gx_after_write (the shadow bytes are awr_bytes:
   in_frames). The entry writes no stack: its window is ESTACK only through ecall_pre. *)
Lemma aj_gx_set_shadow_at : forall pc v, aset_shadow_realizes segs B pc v ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n raw,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  In (cid, pos) own ->
  getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
  shadow_addr (frame_addr lyc cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (forall i, 0 <= i < n -> aview segs (w_H W) mem2 (q + i) = Some v) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
       same_but_materialized mdc md2).
Proof using SK LAWS segs_low.
intros pc v ASS G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n raw
  HG HJX Hown Ha0 Ha1 Hn Hq1 Hq2 H16 Hlo Hhi Hgp Htp Hra Hraw.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (aj_gx_ecall_pre SK segs B ESTACK G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT HJX
  ltac:(lia) H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as (HPRE & _ & _).
destruct (aj_gx_unpack G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT ESTACK HJX
  ltac:(lia) H16 Hlo Hhi) as (memS & HJ & _ & _ & HSTK & HXO & _ & _ & _ & _ & Hceil & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds segs B LAWS lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfb0) as Hse.
eapply SRr_mono; [exact (ASS lyc Sc W regsT memT mdc cid pos q n HPRE Hin Ha0 Ha1 Hn Hq1 Hq2)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & _ & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ apply (ajournal_gx_after_write SK segs B LAWS segs_low G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k
    mem2 md2 (fun a => q <= a < q + n) HG HJX).
  - intros a Ha Hna. exact (Hfr a Ha Hna).
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha. left. split; [|lia].
    right. right. right. exists cid, pos. split; [exact Hown|]. right. unfold in_zr. cbn [fst snd]. lia.
  - exact HAR2. }
split; [exact HP|]. split; [exact Heff|]. split; [exact Hfr|]. split; [exact Hpres2 | exact Hsame].
Qed.

(* The const cells AR fixes at every state of the journal (YG0d.v AR_const_law): the side-stack switch cell holds 1
   (so the real-stack fallback arm after `beqz` on it is never taken), and the shadow base cell holds SHADOW_OFF. *)
Lemma aj_gx_const_cells : forall G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k ->
  YG0n.rd32 (aview segs (w_H W') mem') (as_uar_cell B) 1 /\
  rdword (aview segs (w_H W') mem') (as_got_uar B) = Some (as_uar_cell B) /\
  rdword (aview segs (w_H W') mem') (as_shadow_cell B) = Some SHADOW_OFF /\
  rdword (aview segs (w_H W') mem') (as_got_shadow B) = Some (as_shadow_cell B).
Proof using SK LAWS segs_low.
intros G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJ & _) & _).
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (A1 & A2 & A3 & A4).
split; [exact A2|]. split; [exact A4|]. split; [exact A1 | exact A3].
Qed.

(* Every byte of the journal's window is present. *)
Lemma aj_gx_present : forall G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof using SK LAWS segs_low.
intros G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k (_ & HXO & (memS & HJ & _) & _) a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. lia.
Qed.

(* A byte of a side frame the journal's owner took (In (cid, pos) own), or of that frame's shadow, is a byte the
   journal lets a run or a callee write: awr_byte's in_frames (YCbq.v:343-346), and it lies below the allocator's
   ceiling, so outside the out-cell window [sp0, sp0 + XO). The per-byte obligation of awr_ok_x (W_journalG.v:259)
   and link_amem.v ajw for the frame's own stores and for its inline shadow poisoning. *)
Lemma aj_gx_awr_frame : forall G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k cid pos a,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  In (cid, pos) own ->
  in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO).
Proof using SK LAWS segs_low.
intros G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k cid pos a HJX Hown Ha.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJX as (HSTK & HXO & (memS & HJ & _) & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & _).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4 & Hfc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
split.
- right. right. right. exists cid, pos. split; [exact Hown|].
  destruct Ha as [Ha | Ha]; [left | right]; exact Ha.
- unfold frame_rng, in_zr in Ha. cbn [fst snd] in Ha. destruct Ha as [Ha | Ha]; lia.
Qed.

(* ------------------------------------------------------------------------
   The kept clause (link_amem.v akept) along a walk
   ------------------------------------------------------------------------ *)

Lemma akept_refl : forall lyc Sc W memc slo shi (E : Z -> Prop),
  (forall a, slo <= a < shi -> apresent (w_H W) memc a) -> akept segs B lyc Sc W memc W memc slo shi E.
Proof using SK LAWS segs_low.
intros lyc Sc W memc slo shi E Hp.
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros a _ _ Ha; exact Ha | exact Hp].
Qed.

Lemma akept_mono : forall lyc Sc W memc W2 mem2 slo shi (E1 E2 : Z -> Prop),
  akept segs B lyc Sc W memc W2 mem2 slo shi E1 -> (forall a, E1 a -> E2 a) ->
  akept segs B lyc Sc W memc W2 mem2 slo shi E2.
Proof using SK LAWS segs_low.
intros lyc Sc W memc W2 mem2 slo shi E1 E2 (K1 & K2 & K3 & K4 & K5 & K6) HE.
split; [intros a Ha Hw HnE; exact (K1 a Ha Hw (fun H => HnE (HE a H)))|].
split; [intros b m i Hb Hi HnE; exact (K2 b m i Hb Hi (fun H => HnE (HE _ H)))|].
split; [intros a Hi Hns He HnE; exact (K3 a Hi Hns He (fun H => HnE (HE a H)))|].
split; [intros c p a Hin Hr HnE; exact (K4 c p a Hin Hr (fun H => HnE (HE a H)))|].
split; [exact K5 | exact K6].
Qed.

(* The kept clause a runtime step gives (YCbq.v acall_kept, e.g. the frame_alloc steps (a), (b)). *)
Lemma akept_of_acall_kept : forall lyc Sc W memc W2 mem2 slo shi (Eh E : Z -> Prop),
  acall_kept segs B lyc Sc W memc W2 mem2 slo shi Eh -> (forall a, Eh a -> E a) ->
  akept segs B lyc Sc W memc W2 mem2 slo shi E.
Proof using SK LAWS segs_low.
intros lyc Sc W memc W2 mem2 slo shi Eh E (K1 & K2 & K3 & K4 & K5 & K6) HE.
split; [intros a Ha Hw _; exact (K1 a Ha Hw)|].
split; [intros b m i Hb Hi HnE; exact (K2 b m i Hb Hi (fun H => HnE (HE _ H)))|].
split; [intros a Hi Hns He _; exact (K3 a Hi Hns He)|].
split; [intros c p a Hin Hr HnE; exact (K4 c p a Hin Hr (fun H => HnE (HE a H)))|].
split; [exact K5 | exact K6].
Qed.

(* A byte the caller's journal lets a callee write (link_amem.v ajw) and that lies outside a runtime call's window
   keeps its value across the call, when the call gives YCbq.v acall_kept with no exception and the contract's raw
   clause (every byte runtime-owned neither before nor after, outside the window, is unchanged; the frame_alloc
   lifts (a), (b) give both). A byte of G is kept by the raw clause: G bytes are image bytes outside the runtime's
   statics, so not runtime-owned (AR_owned_image_law) at either end. *)
Lemma ajw_kept_call : forall G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k S2 W2 mem2 md2 slo shi a,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  AR segs B lyc S2 W2 mem2 md2 ->
  alloc_ceiling <= slo ->
  acall_kept segs B lyc Sc W memT W2 mem2 slo shi (fun _ => False) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B lyc S2 a -> ~ (slo <= a < shi) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memT a) ->
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a -> ~ (slo <= a < shi) ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) memT a.
Proof using SK LAWS segs_low.
intros G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k S2 W2 mem2 md2 slo shi a
  HG HJX HAR2 Hslo (K1 & K2 & K3 & K4 & K5 & K6) Hraw Ha Hw.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJX as (HSTK & HXO & (memS & HJ & _) & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo' & Hshi' & H47 & _).
destruct Ha as [[Haw Hnout] | [HGa | [Hout Hwin]]].
- destruct Haw as [Hs | [(Hfp & b & m & Hbm & Hr) | [(b & m & Hbm & _ & Hr) | (cid & pos & Hown & Hr)]]].
  + apply K1; [lia | exact Hw].
  + replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hbm); [lia | exact (fun H => H)].
  + replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hbm); [lia | exact (fun H => H)].
  + assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
    exact (K4 cid pos a Hin Hr (fun H => H)).
- destruct (HG a HGa) as [Hi Hns]. pose proof (segs_low a Hi) as Hal.
  apply Hraw; [lia | | | exact Hw].
  + intros Ho. exact (Hns (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR Hi) Ho)).
  + intros Ho. exact (Hns (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR2 Hi) Ho)).
- apply K1; [lia | exact Hw].
Qed.

(* The shadow byte of a byte of a side frame of Sc keeps its value across a call that gives acall_kept (its frame
   clause covers the frame's shadow). *)
Lemma aframe_shadow_kept_call : forall lyc Sc W memT mdc W2 mem2 slo shi (Eh : Z -> Prop) cid pos a,
  AR segs B lyc Sc W memT mdc -> In (cid, pos) (frames Sc) -> 0 <= cid ->
  acall_kept segs B lyc Sc W memT W2 mem2 slo shi Eh -> ~ Eh (shadow_addr a) ->
  frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid ->
  aview segs (w_H W2) mem2 (shadow_addr a) = aview segs (w_H W) memT (shadow_addr a).
Proof using SK LAWS segs_low.
intros lyc Sc W memT mdc W2 mem2 slo shi Eh cid pos a HAR Hin Hcid (_ & _ & _ & K4 & _) HnE Ha.
destruct (al_frames _ _ LAWS lyc Sc W memT mdc cid pos HAR Hin) as (Hf32 & _ & _ & _).
assert (Hfs8 : fs_frame_bytes cid mod 8 = 0).
{ unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
  replace (64 * 2 ^ cid) with (8 * 2 ^ cid * 8) by ring. apply Z_mod_mult. }
apply (K4 cid pos (shadow_addr a) Hin); [|exact HnE].
right. unfold in_zr, shadow_addr. cbn [fst snd]. lia.
Qed.

(* A step that keeps every byte outside X (a symbolic run: its written regions; a checked copy or fill: its
   destination and its window; meta_fill: its destination; frame_release: the frame's shadow, its flag byte and its
   window) and the presence of the bytes above the allocator's ceiling. X goes into the exception set or the window. *)
Lemma akept_step : forall lyc Sc W memc mdc W1 m1 W2 m2 slo shi (E1 E2 X : Z -> Prop),
  AR segs B lyc Sc W memc mdc -> alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  akept segs B lyc Sc W memc W1 m1 slo shi E1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) ->
  (forall a, E1 a -> E2 a) -> (forall a, X a -> E2 a \/ slo <= a < shi) ->
  akept segs B lyc Sc W memc W2 m2 slo shi E2.
Proof using SK LAWS segs_low.
intros lyc Sc W memc mdc W1 m1 W2 m2 slo shi E1 E2 X HAR Hslo Hshi (K1 & K2 & K3 & K4 & K5 & K6) UN Hpr HE12 HX.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (Hlow : forall a, 0 <= a < 2 ^ 64 -> a < alloc_ceiling -> ~ E2 a ->
  aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a).
{ intros a Ha Hlt HnE. apply UN; [exact Ha|]. intros HXa. destruct (HX a HXa) as [H|H]; [exact (HnE H) | lia]. }
split.
{ intros a Ha Hw HnE. rewrite <- (K1 a Ha Hw (fun H => HnE (HE12 a H))). apply UN; [lia|].
  intros HXa. destruct (HX a HXa) as [H|H]; [exact (HnE H) | exact (Hw H)]. }
split.
{ intros b m i Hb Hi HnE. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
  rewrite <- (K2 b m i Hb Hi (fun H => HnE (HE12 _ H))). apply Hlow; [lia | lia | exact HnE]. }
split.
{ intros a Hi Hns He HnE. pose proof (segs_low a Hi) as Hal.
  rewrite <- (K3 a Hi Hns He (fun H => HnE (HE12 a H))). apply Hlow; [lia | lia | exact HnE]. }
split.
{ intros c p a Hin Hr HnE.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c p HAR Hin) as (Hf4 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg c) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc c p) ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc c p + fs_frame_bytes c) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc c p) (fs_frame_bytes c) Hnn) as Hse.
  rewrite <- (K4 c p a Hin Hr (fun H => HnE (HE12 a H))).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  apply Hlow; [destruct Hr; lia | destruct Hr; lia | exact HnE]. }
split.
{ intros a Ha Hw Hp. apply Hpr; [lia | exact (K5 a Ha Hw Hp)]. }
intros a Ha. apply Hpr; [lia | exact (K6 a Ha)].
Qed.

(* A callee's kept clause, stated at the callee's call state lyc S1 (a later allocator state of the same layout
   whose blocks and frames include the caller's: e.g. after the caller took its side frame), composes with the
   caller's. *)
Lemma akept_trans : forall lyc Sc W memc S1 W1 m1 W2 m2 slo shi slo1 shi1 (E1 Ec E2 : Z -> Prop),
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  akept segs B lyc Sc W memc W1 m1 slo shi E1 ->
  akept segs B lyc S1 W1 m1 W2 m2 slo1 shi1 Ec ->
  slo <= slo1 -> shi1 <= shi ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B lyc S1)) ->
  (forall f, In f (frames Sc) -> In f (frames S1)) ->
  (forall a, E1 a -> E2 a) -> (forall a, Ec a -> E2 a) ->
  akept segs B lyc Sc W memc W2 m2 slo shi E2.
Proof using SK LAWS segs_low.
intros lyc Sc W memc S1 W1 m1 W2 m2 slo shi slo1 shi1 E1 Ec E2 Hslo Hshi
  (K1 & K2 & K3 & K4 & K5 & K6) (L1 & L2 & L3 & L4 & L5 & L6) Hs1 Hs2 Hbl Hfr H1 H2.
split.
{ intros a Ha Hw HnE. rewrite (L1 a Ha ltac:(lia) (fun H => HnE (H2 a H))). exact (K1 a Ha Hw (fun H => HnE (H1 a H))). }
split.
{ intros b m i Hb Hi HnE. rewrite (L2 b m i (Hbl b m Hb) Hi (fun H => HnE (H2 _ H))).
  exact (K2 b m i Hb Hi (fun H => HnE (H1 _ H))). }
split.
{ intros a Hi Hns He HnE. rewrite (L3 a Hi Hns He (fun H => HnE (H2 a H))). exact (K3 a Hi Hns He (fun H => HnE (H1 a H))). }
split.
{ intros c p a Hin Hr HnE. rewrite (L4 c p a (Hfr _ Hin) Hr (fun H => HnE (H2 a H))).
  exact (K4 c p a Hin Hr (fun H => HnE (H1 a H))). }
split.
{ intros a Ha Hw Hp. exact (L5 a Ha ltac:(lia) (K5 a Ha Hw Hp)). }
intros a Ha. destruct (Z_lt_le_dec a slo1) as [Hl|Hl]; [|destruct (Z_lt_le_dec a shi1) as [Hh|Hh]].
- exact (L5 a ltac:(lia) ltac:(lia) (K6 a Ha)).
- exact (L6 a ltac:(lia)).
- exact (L5 a ltac:(lia) ltac:(lia) (K6 a Ha)).
Qed.

(* akept_trans for a callee whose call state is at another layout ly1 of the same journal (an own callee's post
   returns at its existential layout): its frames sit at the same addresses (aj_gx_frame_addr). *)
Lemma akept_trans_ly : forall lyc Sc W memc ly1 S1 W1 m1 W2 m2 slo shi slo1 shi1 (E1 Ec E2 : Z -> Prop),
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  akept segs B lyc Sc W memc W1 m1 slo shi E1 ->
  akept segs B ly1 S1 W1 m1 W2 m2 slo1 shi1 Ec ->
  slo <= slo1 -> shi1 <= shi ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly1 S1)) ->
  (forall f, In f (frames Sc) -> In f (frames S1)) ->
  (forall c p, frame_addr ly1 c p = frame_addr lyc c p) ->
  (forall a, E1 a -> E2 a) -> (forall a, Ec a -> E2 a) ->
  akept segs B lyc Sc W memc W2 m2 slo shi E2.
Proof using SK LAWS segs_low.
intros lyc Sc W memc ly1 S1 W1 m1 W2 m2 slo shi slo1 shi1 E1 Ec E2 Hslo Hshi
  (K1 & K2 & K3 & K4 & K5 & K6) (L1 & L2 & L3 & L4 & L5 & L6) Hs1 Hs2 Hbl Hfr Hfa H1 H2.
split.
{ intros a Ha Hw HnE. rewrite (L1 a Ha ltac:(lia) (fun H => HnE (H2 a H))). exact (K1 a Ha Hw (fun H => HnE (H1 a H))). }
split.
{ intros b m i Hb Hi HnE. rewrite (L2 b m i (Hbl b m Hb) Hi (fun H => HnE (H2 _ H))).
  exact (K2 b m i Hb Hi (fun H => HnE (H1 _ H))). }
split.
{ intros a Hi Hns He HnE. rewrite (L3 a Hi Hns He (fun H => HnE (H2 a H))). exact (K3 a Hi Hns He (fun H => HnE (H1 a H))). }
split.
{ intros c p a Hin Hr HnE.
  assert (Hr1 : in_zr a (frame_rng ly1 (c, p)) \/ in_zr a (shadow_addr (frame_addr ly1 c p), fs_frame_bytes c / 8)).
  { unfold frame_rng. cbn [fst snd]. rewrite (Hfa c p). exact Hr. }
  rewrite (L4 c p a (Hfr _ Hin) Hr1 (fun H => HnE (H2 a H))).
  exact (K4 c p a Hin Hr (fun H => HnE (H1 a H))). }
split.
{ intros a Ha Hw Hp. exact (L5 a Ha ltac:(lia) (K5 a Ha Hw Hp)). }
intros a Ha. destruct (Z_lt_le_dec a slo1) as [Hl|Hl]; [|destruct (Z_lt_le_dec a shi1) as [Hh|Hh]].
- exact (L5 a ltac:(lia) ltac:(lia) (K6 a Ha)).
- exact (L6 a ltac:(lia)).
- exact (L5 a ltac:(lia) ltac:(lia) (K6 a Ha)).
Qed.

(* Every layout of a journal places the side frames and their flag bytes where the journal's start layout does. *)
Lemma aj_gx_frame_addr : forall G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k c p,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k ->
  frame_addr ly' c p = frame_addr ly c p /\ flag_addr ly' c p = flag_addr ly c p.
Proof using SK LAWS segs_low.
intros G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k c p (_ & _ & (memS & HJ & _) & _).
pose proof HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
unfold frame_addr, flag_addr. rewrite EF. split; reflexivity.
Qed.

(* THE HEAP-BLOCK SHADOW across any stretch of the journal: AR fixes the shadow of every heap block (YG0d.v
   AR_shadow_law: block_shadow), so a block present at both ends has the same shadow at both ends. *)
Lemma ashadow_kept_AR : forall lyc Sc ly2 S2 W memc mdc W2 mem2 md2,
  AR segs B lyc Sc W memc mdc -> AR segs B ly2 S2 W2 mem2 md2 ->
  ashadow_kept segs B lyc Sc ly2 S2 W memc W2 mem2.
Proof using SK LAWS segs_low.
intros lyc Sc ly2 S2 W memc mdc W2 mem2 md2 HAR HAR2 b m a Hin Hin2 Ha.
destruct (al_shadow _ _ LAWS _ _ _ _ _ b m HAR Hin) as [(Hb8 & Hn0 & HS1) _].
destruct (al_shadow _ _ LAWS _ _ _ _ _ b m HAR2 Hin2) as [(_ & _ & HS2) _].
assert (Ei : shadow_addr a = shadow_of_addr SHADOW_OFF b + (a / 8 - b / 8)).
{ unfold shadow_addr, shadow_of_addr. lia. }
assert (Hi : 0 <= a / 8 - b / 8 < (req_size m + 7) / 8).
{ assert (b / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (a / 8 < b / 8 + (req_size m + 7) / 8).
  { pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Hb8, Z.add_0_r in Db.
    assert (Ea : a / 8 = b / 8 + (a - b) / 8).
    { rewrite Db at 1. replace (8 * (b / 8) + (a - b)) with ((a - b) + (b / 8) * 8) by lia.
      rewrite Db. replace (a - 8 * (b / 8)) with ((a - 8 * (b / 8))) by lia.
      rewrite <- Db. replace a with ((a - b) + b / 8 * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
    rewrite Ea. assert ((a - b) / 8 < (req_size m + 7) / 8) by (apply Z.div_lt_upper_bound; [lia|]; pose proof (Z.mul_div_le (req_size m + 7) 8); pose proof (Z.mod_pos_bound (req_size m + 7) 8); pose proof (Z.div_mod (req_size m + 7) 8); lia).
    lia. }
  lia. }
rewrite Ei, (HS1 _ Hi), (HS2 _ Hi). reflexivity.
Qed.

(* A byte of a side frame (aside_rng) lies below the allocator's ceiling and outside the image. *)
Lemma aside_rng_low : forall lyc S1 W1 mem1 md1 cid pos a,
  AR segs B lyc S1 W1 mem1 md1 -> In (cid, pos) (frames S1) -> aside_rng lyc cid pos a ->
  a < alloc_ceiling /\ ~ in_img segs a.
Proof using SK LAWS segs_low.
intros lyc S1 W1 mem1 md1 cid pos a HAR Hin Hs.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (frames_bounds segs B LAWS lyc S1 W1 mem1 md1 cid pos HAR Hin) as (Hf4 & Hfc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
destruct Hs as [Hr | [Hr | ->]].
- unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. split; [lia|].
  exact (frm_img segs B LAWS lyc S1 W1 mem1 md1 cid pos a HAR Hin Hr).
- unfold in_zr in Hr. cbn [fst snd] in Hr. split; [lia|]. intros Hi. pose proof (segs_low a Hi). lia.
- destruct (al_flag _ _ LAWS lyc S1 W1 mem1 md1 cid pos HAR Hin) as (_ & _ & _ & Hflc). split; [exact Hflc|].
  exact (proj2 (al_client_img _ _ LAWS lyc S1 W1 mem1 md1 (flag_addr lyc cid pos) HAR
    (or_intror (or_intror (ex_intro _ cid (ex_intro _ pos (conj Hin eq_refl))))))).
Qed.

(* The bytes of a frame taken after the call (frames S1 = (cid, pos) :: frames Sc) are none of the bytes akept speaks
   of: not above the ceiling, not in a heap block, not in the image, not in a frame of Sc nor in its shadow. So an
   akept whose exception set also names them gives the akept without them. *)
Lemma akept_drop_side : forall lyc Sc W memc W2 mem2 slo shi (E : Z -> Prop) S1 W1 mem1 md1 cid pos,
  AR segs B lyc S1 W1 mem1 md1 -> frames S1 = (cid, pos) :: frames Sc -> ablocks B lyc S1 = ablocks B lyc Sc ->
  akept segs B lyc Sc W memc W2 mem2 slo shi (fun a => E a \/ aside_rng lyc cid pos a) ->
  akept segs B lyc Sc W memc W2 mem2 slo shi E.
Proof using SK LAWS segs_low.
intros lyc Sc W memc W2 mem2 slo shi E S1 W1 mem1 md1 cid pos HAR1 Hfrs1 Eab1 (K1 & K2 & K3 & K4 & K5 & K6).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (Hin1 : In (cid, pos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
pose proof (aside_rng_low lyc S1 W1 mem1 md1 cid pos) as Hlow.
destruct (frames_bounds segs B LAWS lyc S1 W1 mem1 md1 cid pos HAR1 Hin1) as (Hf4 & Hfc & _).
destruct (al_frames _ _ LAWS lyc S1 W1 mem1 md1 cid pos HAR1 Hin1) as (_ & Happ & _ & _).
destruct (al_flag _ _ LAWS lyc S1 W1 mem1 md1 cid pos HAR1 Hin1) as (_ & Hfo & _ & _).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
split.
{ intros a Ha Hw HnE. apply K1; [exact Ha | exact Hw |].
  intros [HE'|Hs]; [exact (HnE HE') | pose proof (proj1 (Hlow a HAR1 Hin1 Hs)); lia]. }
split.
{ intros b m i Hb Hi HnE. apply (K2 b m i Hb Hi). intros [HE'|Hs]; [exact (HnE HE')|].
  assert (Hb1 : In (b, m) (ablocks B lyc S1)) by (rewrite Eab1; exact Hb).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hb1) as (_ & H4096 & Hbc & Hbapp & Hpo & _ & _).
  assert (Hrq : 0 <= i < req_size m) by exact Hi.
  destruct Hs as [Hr | [Hr | Hr]].
  - pose proof (sep_block_frame segs B LAWS lyc S1 W1 mem1 md1 b m cid pos HAR1 Hb1 Hin1) as Hd.
    unfold zdisjoint, in_zr, frame_rng in Hd, Hr. cbn [fst snd] in Hd, Hr. lia.
  - pose proof (in_app_addr _ _ (b + i) Hbapp ltac:(lia)) as Hap. unfold app_addr in Hap.
    unfold in_zr in Hr. cbn [fst snd] in Hr. unfold kLowShadowBeg, ASAN_CEIL in Hap. lia.
  - exact (proj2 (Hpo (b + i) ltac:(lia)) (eq_ind_r (fun x => aowned B lyc S1 x) Hfo Hr)). }
split.
{ intros a Hi Hns He HnE. apply K3; [exact Hi | exact Hns | exact He |].
  intros [HE'|Hs]; [exact (HnE HE') | exact (proj2 (Hlow a HAR1 Hin1 Hs) Hi)]. }
split.
{ intros c p a Hin Hr HnE. apply (K4 c p a Hin Hr). intros [HE'|Hs]; [exact (HnE HE')|].
  assert (Hin' : In (c, p) (frames S1)) by (rewrite Hfrs1; right; exact Hin).
  apply in_split in Hin as (l2 & l3 & El).
  pose proof (sep_frames_pos segs B LAWS lyc S1 W1 mem1 md1 (cid, pos) (c, p) [] l2 l3 HAR1
    ltac:(rewrite Hfrs1, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
  destruct (frames_bounds segs B LAWS lyc S1 W1 mem1 md1 c p HAR1 Hin') as (Hf4' & Hfc' & _).
  destruct (al_frames _ _ LAWS lyc S1 W1 mem1 md1 c p HAR1 Hin') as (_ & Happ' & Hfb' & Hfsh').
  pose proof (fs_frame_bytes_nonneg c) as Hnn'.
  pose proof (shadow_addr_bounds (frame_addr lyc c p) ltac:(lia)) as Hsb1'.
  pose proof (shadow_addr_bounds (frame_addr lyc c p + fs_frame_bytes c) ltac:(lia)) as Hsb2'.
  pose proof (shadow_range_end (frame_addr lyc c p) (fs_frame_bytes c) Hnn') as Hse'.
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  destruct Hs as [Hs | [Hs | Hs]]; unfold in_zr, frame_rng in Hs; cbn [fst snd] in Hs.
  - destruct Hr as [Hr | Hr].
    + lia.
    + pose proof (in_app_addr _ _ a Happ ltac:(lia)) as Hap. unfold app_addr, kLowShadowBeg, ASAN_CEIL in Hap. lia.
  - destruct Hr as [Hr | Hr].
    + pose proof (in_app_addr _ _ a Happ' ltac:(lia)) as Hap. unfold app_addr, kLowShadowBeg, ASAN_CEIL in Hap. lia.
    + destruct Hd as [Hd | Hd].
      * pose proof (shadow_mono _ _ Hd). lia.
      * pose proof (shadow_mono _ _ Hd). lia.
  - subst a. destruct Hr as [Hr | Hr].
    + exact (proj2 (Hfb' _ Hr) Hfo).
    + specialize (Hfsh' (flag_addr lyc cid pos - shadow_addr (frame_addr lyc c p)) ltac:(lia)).
      replace (shadow_addr (frame_addr lyc c p) + (flag_addr lyc cid pos - shadow_addr (frame_addr lyc c p)))
        with (flag_addr lyc cid pos) in Hfsh' by lia.
      exact (proj2 Hfsh' Hfo). }
split; [exact K5 | exact K6].
Qed.

(* (f) THE POST OF A FUNCTION THAT TAKES AND RELEASES ONE SIDE FRAME inside the call (link_amem.v apost; the
   LinkWalk.v apost_leaf analogue). The end journal is at the call's own, at any layout ly2 and world W2 (own
   callees' posts return the journal at their own existential layout and world), its state S2 (frames S2 = frames Sc
   follows from the two journals); S1 is any state at which the frame (cid, pos) was live on top of Sc's frames with
   Sc's blocks (the state frame_alloc returned); the kept clause the walk carries excepts E and the taken frame's
   bytes, its shadow and its flag byte (aside_rng), which apost does not except: they are not frames of Sc. The
   heap-block shadow clause comes from the two journals' AR (ashadow_kept_AR). For aleaf's Q, S2 = set_fs (st_fs S2)
   Sc follows from set_fs_trans / set_fs_of_exists / stack_free_state_set_fs, and the block Permutation from
   ablocks_set_fs. *)
Lemma apost_side_gen : forall (K EV : Z) (E : Z -> Prop) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs regs2 : bvmap 5 word) ly2 S2 W2 mem2 md2 k2 cid pos S1 W1 mem1 md1
    (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k2 ->
  k2 <= k + EV ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  aregs_preserved regs regs2 ->
  AR segs B lyc S1 W1 mem1 md1 -> frames S1 = (cid, pos) :: frames Sc -> ablocks B lyc S1 = ablocks B lyc Sc ->
  akept segs B lyc Sc W memc W2 mem2 (spZ regs - K) (spZ regs) (fun a => E a \/ aside_rng lyc cid pos a) ->
  Q ly2 S2 W2 regs2 mem2 md2 ->
  apost SK segs B K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q
    W2 (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2).
Proof using SK LAWS segs_low.
intros K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 ly2 S2 W2 mem2 md2 k2 cid pos
  S1 W1 mem1 md1 Q HJ HJ2 Hk2 Hfds Hfs HP HAR1 Hfrs1 Eab1 HK HQ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _ & _ & _ & _ & Hfrs2 & _).
exists ly2, S2, regs2, mem2, md2.
split; [reflexivity|].
split; [eapply ajournal_gx_mono_k; [exact HJ2 | exact Hk2]|].
split; [exact HP|].
split; [rewrite Hfrs2, Hfrs; reflexivity|].
split; [exact Hfds|]. split; [exact Hfs|].
split; [exact (akept_drop_side lyc Sc W memc W2 mem2 (spZ regs - K) (spZ regs) E S1 W1 mem1 md1 cid pos HAR1 Hfrs1 Eab1 HK)|].
split; [exact (ashadow_kept_AR lyc Sc ly2 S2 W memc mdc W2 mem2 md2 HAR HAR2)|].
exact HQ.
Qed.

(* apost_side_gen at the call's layout and world. *)
Lemma apost_side : forall (K EV : Z) (E : Z -> Prop) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs regs2 : bvmap 5 word) S2 mem2 md2 k2 cid pos S1 W1 mem1 md1
    (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc S2 W mem2 md2 k2 ->
  k2 <= k + EV ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  aregs_preserved regs regs2 ->
  AR segs B lyc S1 W1 mem1 md1 -> frames S1 = (cid, pos) :: frames Sc -> ablocks B lyc S1 = ablocks B lyc Sc ->
  akept segs B lyc Sc W memc W mem2 (spZ regs - K) (spZ regs) (fun a => E a \/ aside_rng lyc cid pos a) ->
  Q lyc S2 W regs2 mem2 md2 ->
  apost SK segs B K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2).
Proof using SK LAWS segs_low.
intros K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 S2 mem2 md2 k2 cid pos
  S1 W1 mem1 md1 Q.
exact (apost_side_gen K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 lyc S2 W mem2 md2 k2
  cid pos S1 W1 mem1 md1 Q).
Qed.

(* LinkWalk.v apost_leaf without its premise on E (`forall x, E x -> x < SHADOW_OFF`): the heap-block shadow clause
   comes from AR at both ends of the journal (ashadow_kept_AR), so a write set E may hold any bytes, e.g. a buffer in
   a side frame in high application memory. *)
Lemma apost_leaf_AR : forall (K EV : Z) (E : Z -> Prop) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs regs2 : bvmap 5 word) mem2 md2
    (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  0 <= EV -> sp0 - STK <= spZ regs - K -> spZ regs - K <= spZ regs ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  aregs_preserved regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) -> ~ E a ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  (forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem2 a) ->
  Q lyc Sc W regs2 mem2 md2 ->
  apost SK segs B K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2).
Proof using SK LAWS segs_low.
intros K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 Q
  HJ HJ2 HEV Hlo Hwin Hfds Hfs HP UN Hgrow Hpw HQ.
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & _).
pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof (proj1 HJi2) as HAR2.
exists lyc, Sc, regs2, mem2, md2.
split; [reflexivity|].
split; [eapply ajournal_gx_mono_k; [exact HJ2 | lia]|].
split; [exact HP|]. split; [reflexivity|].
split; [exact Hfds|]. split; [exact Hfs|].
split; [exact (akept_run segs B LAWS segs_low lyc Sc W memc mdc W mem2 (spZ regs - K) (spZ regs) E HAR ltac:(lia) Hwin
  UN Hgrow Hpw)|].
split; [exact (ashadow_kept_AR lyc Sc lyc Sc W memc mdc W mem2 md2 HAR HAR2)|].
exact HQ.
Qed.

(* ------------------------------------------------------------------------
   Section m: the two frame_alloc steps (they take api_env, as the donor's call_effect_journal does)
   ------------------------------------------------------------------------ *)
Section m.
Hypothesis errno_low : api_env segs B.

(* The donor-journal step of frame_alloc_<c> over astack_malloc_realizes: YC85G.v:296 aj_stack_malloc_atS with the
   model laws and the progress law derived from the journal's AR and YG05.v, the post without the call's inner journal
   and with the contract's same_but_materialized. *)
Lemma aj_stack_malloc_atM : forall cid, astack_malloc_realizes segs B cid -> 0 <= cid <= 10 ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
  ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  count_cid cid (frames Sc) < fs_frames cid ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc (as_code B) cid)) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal segs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
       ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
       st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
       zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
       rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
       acall_kept segs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) /\
       (exists f, S2 = set_fs f Sc) /\ same_but_materialized mdc md2 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B lyc S2 a -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof using SK LAWS segs_low errno_low.
intros cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
  HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (YG05.model_laws_ok (as_universe B) (am_universe _ _ _ _ (proj1 HAR))) as ML.
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
  all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
  split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
  split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (YG05.stack_malloc_progress (as_universe B) Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
pose proof (ml_stack_malloc _ ML Sc cid HWF Hcid) as HTOK.
destruct (atok_apath _ _ _ [] (PFake cid pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal segs B ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
{ eapply (call_effect_journal segs B LAWS segs_low errno_low ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2
    (fun _ => False) [] [(cid, pos)] 0);
  [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2 | exact HAR
  | exact HstkC | cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | ].
  - intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
  - intros p m i Hp Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp.
  - rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
  eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
split; [exact Hnev2|]. split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hflag|].
rewrite Hsp' in HJ1. split; [| split; [exists f; exact ES2 | split; [exact Hsame | exact Hfr]]].
eapply (acall_kept_of_journal segs B segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.

(* (a) FRAME_ALLOC_<c> ON THE JOURNAL, classes whose entry the runtime contract astack_malloc_realizes covers
   (classes <= 7; on link 0, 1, 3, 4; generic in cid): aj_stack_malloc_atM (YC85G.v:296 aj_stack_malloc_atS) over
   ajournal_gx. The entry's pc is free, with
   its code-record equation (pc_stack_malloc (as_code B) cid = pc), so a walk's jal target unifies. The post holds
   the frame's address, its bounds (frames_bounds: the frame address is >= 4096, so the real-stack fallback arm after
   `bnez` on it is dead), its zeroed shadow, the flag-address word, and the kept clause of the call. *)
Lemma aj_gx_stack_malloc_at : forall cid, astack_malloc_realizes segs B cid -> 0 <= cid <= 10 ->
  forall pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw,
  pc_stack_malloc (as_code B) cid = pc ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  count_cid cid (frames Sc) < fs_frames cid ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
       ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
       st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\ (exists f, S2 = set_fs f Sc) /\
       4096 <= frame_addr lyc cid pos /\ frame_addr lyc cid pos + fs_frame_bytes cid <= alloc_ceiling /\
       zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
       rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
       acall_kept segs B lyc Sc W memT W mem2 (spZ regsT - ESTACK) (spZ regsT) (fun _ => False) /\
       same_but_materialized mdc md2 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B lyc S2 a -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof using SK LAWS segs_low errno_low.
intros cid ASM Hcid pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw
  Hpc HJX H16 Hlo Hhi Hgp Htp Hra Hraw Hcnt.
assert (ESTACK = 4096) as Hes by reflexivity.
destruct (aj_gx_unpack G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT ESTACK HJX
  ltac:(lia) H16 Hlo Hhi) as (memS & HJ & Hag & Hout & HSTK & HXO & Hsp & Ho16 & Ho0 & Hob & Hceil & H47).
subst pc.
eapply SRr_mono.
{ exact (aj_stack_malloc_atM cid ASM Hcid W regsT memT (STK + XO) (sp0 + XO)
    FP ly S W0 memS md own lyc Sc mdc k (spZ regsT - (sp0 + XO)) raw HJ Hsp Ho16 Ho0 Hob Hgp Htp Hra Hraw Hcnt). }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP & Hres & Eab & Hfrs2 & Hfresh & Hnev & Hbb
  & Hz & Hflag & HK & Hf & Hsm & Hkraw).
rewrite <- Hsp in HK.
pose proof (proj1 HJ2) as HAR2.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds segs B LAWS lyc S2 W mem2 md2 cid pos HAR2 Hin2) as (HF4096 & HFceil & _).
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos. split; [reflexivity|].
split.
{ eapply ajournal_gx_pack; [exact HSTK | exact HXO | exact HJ2 | exact Hag |].
  intros a Ha Hno. rewrite <- (Hout a Ha Hno). destruct HK as (K1 & _). apply K1; lia. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
split; [exact Hnev|]. split; [exact Hbb|]. split; [exact Hf|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [exact Hz|]. split; [exact Hflag|]. split; [exact HK|]. split; [exact Hsm | exact Hkraw].
Qed.

(* The donor-journal step of frame_alloc_<c> over astack_malloc_sz_realizes (Reusable/AsStackSz.v: the runtime
   zeroes the shadow of the n bytes a0 asks for). Ported from plugin-hostd/fuzz_command lib/A/Prog/answer_s0.v:180-242
   aj_stack_malloc_sz_atS (origin/ossv/recipes), itself cgif_rgb_fuzzer lib/YC05.v:143 aj_stack_malloc_sz_at over
   cgif_file_fuzzer's journal: the statement is the donor's; in the proof the model laws and the progress law are
   derived from the journal's AR and YG05.v instead of being Section hypotheses, acall_kept_of_journal takes link's
   arguments (as YC85G.v:356), and the post also gives the contract's same_but_materialized (so a walk keeps the
   descriptors and the file system, link_amem.v apost). *)
Lemma aj_stack_malloc_sz_atM : forall pc cid, astack_malloc_sz_realizes segs B pc cid -> 0 <= cid <= 10 ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw n,
  ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 n -> 8 <= n <= fs_frame_bytes cid -> n mod 8 = 0 ->
  count_cid cid (frames Sc) < fs_frames cid ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal segs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
       ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
       st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
       zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) n /\
       rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
       acall_kept segs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) /\
       (exists f, S2 = set_fs f Sc) /\ same_but_materialized mdc md2 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B lyc S2 a -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof using SK LAWS segs_low errno_low.
intros pc cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw n
  HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Ha0 Hn Hn8 Hcnt.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (YG05.model_laws_ok (as_universe B) (am_universe _ _ _ _ (proj1 HAR))) as ML.
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
  all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
  split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
  split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (YG05.stack_malloc_progress (as_universe B) Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
pose proof (ml_stack_malloc _ ML Sc cid HWF Hcid) as HTOK.
destruct (atok_apath _ _ _ [] (PFake cid pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 n HPRE Ha0 Hn Hn8 Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal segs B ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
{ eapply (call_effect_journal segs B LAWS segs_low errno_low ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2
    (fun _ => False) [] [(cid, pos)] 0);
  [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2 | exact HAR
  | exact HstkC | cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | ].
  - intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
  - intros p m i Hp Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp.
  - rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
  eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
split; [exact Hnev2|]. split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hflag|].
rewrite Hsp' in HJ1. split; [| split; [exists f; exact ES2 | split; [exact Hsame | exact Hfr]]].
eapply (acall_kept_of_journal segs B segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.

(* (b) FRAME_ALLOC_<c> ON THE JOURNAL over astack_malloc_sz_realizes (classes 8, 9: kernel's frame_alloc_8, nl_talk's
   frame_alloc_9): aj_stack_malloc_sz_atM over ajournal_gx, the same post as (a) with the n zeroed shadow bytes. *)
Lemma aj_gx_stack_malloc_sz_at : forall pc cid, astack_malloc_sz_realizes segs B pc cid -> 0 <= cid <= 10 ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw n,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 n -> 8 <= n <= fs_frame_bytes cid -> n mod 8 = 0 ->
  count_cid cid (frames Sc) < fs_frames cid ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
       ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
       st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\ (exists f, S2 = set_fs f Sc) /\
       4096 <= frame_addr lyc cid pos /\ frame_addr lyc cid pos + fs_frame_bytes cid <= alloc_ceiling /\
       zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) n /\
       rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
       acall_kept segs B lyc Sc W memT W mem2 (spZ regsT - ESTACK) (spZ regsT) (fun _ => False) /\
       same_but_materialized mdc md2 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B lyc S2 a -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof using SK LAWS segs_low errno_low.
intros pc cid ASM Hcid G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw n
  HJX H16 Hlo Hhi Hgp Htp Hra Hraw Ha0 Hn Hn8 Hcnt.
assert (ESTACK = 4096) as Hes by reflexivity.
destruct (aj_gx_unpack G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT ESTACK HJX
  ltac:(lia) H16 Hlo Hhi) as (memS & HJ & Hag & Hout & HSTK & HXO & Hsp & Ho16 & Ho0 & Hob & Hceil & H47).
eapply SRr_mono.
{ exact (aj_stack_malloc_sz_atM pc cid ASM Hcid W regsT memT (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc mdc k
    (spZ regsT - (sp0 + XO)) raw n HJ Hsp Ho16 Ho0 Hob Hgp Htp Hra Hraw Ha0 Hn Hn8 Hcnt). }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP & Hres & Eab & Hfrs2 & Hfresh & Hnev & Hbb
  & Hz & Hflag & HK & Hf & Hsm & Hkraw).
rewrite <- Hsp in HK.
pose proof (proj1 HJ2) as HAR2.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds segs B LAWS lyc S2 W mem2 md2 cid pos HAR2 Hin2) as (HF4096 & HFceil & _).
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos. split; [reflexivity|].
split.
{ eapply ajournal_gx_pack; [exact HSTK | exact HXO | exact HJ2 | exact Hag |].
  intros a Ha Hno. rewrite <- (Hout a Ha Hno). destruct HK as (K1 & _). apply K1; lia. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
split; [exact Hnev|]. split; [exact Hbb|]. split; [exact Hf|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [exact Hz|]. split; [exact Hflag|]. split; [exact HK|]. split; [exact Hsm | exact Hkraw].
Qed.
End m.
End k.

(* ==========================================================================
   Section pe: the PLAIN engine over ajournal_gx, and the inline release in a run
   ========================================================================== *)
Section pe.
Variable psym : Type.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable fetch : Z -> option Z.
Variable val : nat -> Z.
Variable sigma : psym -> Z.
Variable listing : ptable psym.
Variable tpi0 : ptree psym.
Hypothesis Hfetch : forall pc w, fetch pc = Some w -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Hypothesis Hcert : pi_check psym fetch val sigma listing = true.
Hypothesis HB : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ val A_TEXT mod 4 = 0.
Variable A_LIM : nat.
Hypothesis HLIM0 : (A_TEXT < A_LIM)%nat.
Hypothesis HLIM : forallb (pinstr_atoms_ltb A_LIM) listing = true.
Hypothesis Htpi : ptree_of_list listing = tpi0.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok segs B G.
Variable XO : Z.
Variable OUT : list (Z * Z).

(* After a run: the caller's continuation at the run's end state (an absolute sstate ss'). *)
Definition run_post_AJX (W : world segs) (E : env) (ss ss' : sstate) (ms : machine_state) (STK sp0 : Z)
    (FP : list (Z * Z)) ly S W0 mem md own lyc Sc (mdc : Model) (k : Z) (Q : world segs -> config -> Prop) : Prop :=
  forall ms' mat',
  st_ok segs E ss' (restrict (w_H W) ms') ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
(* The same at a listing-relative end state (st_ok_pi). *)
Definition run_post_pi_AJX (W : world segs) (E : env) (ss ss' : sstate) (ms : machine_state) (STK sp0 : Z)
    (FP : list (Z * Z)) ly S W0 mem md own lyc Sc (mdc : Model) (k : Z) (Q : world segs -> config -> Prop) : Prop :=
  forall ms' mat',
  st_ok_pi segs val E ss' (restrict (w_H W) ms') ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.

(* Reusable/YCbq.v:2216 SRr_chain_AJ over ajournal_gx (W_journalG.v SRr_chain_pi_tok_AJX without the tokens). *)
Lemma SRr_chain_AJX : forall W E ss ss' ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
  msteps segs (restrict (w_H W) ms) msr' ->
  st_ok segs E ss' msr' ->
  frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok_x E (ss_mem ss) G XO OUT STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  run_post_AJX W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
  SRr segs W (mkCfg ms mdc) Q.
Proof using All.
intros W E ss ss' ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q Hms HS' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- eapply (ajournal_gx_exec segs B LAWS segs_low G XO OUT) with (Wr := in_wrange E (ss_mem ss));
  [exact HG | exact HJ | | | | | exact Hwr].
  + rewrite Hmm. exact Hfr.
  + rewrite Hmm. exact Hgr.
  + intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
  + rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.

(* pcap PcapFrame.v:422 SRr_run_pi_AJ over ajournal_gx. *)
Lemma SRr_run_pi_AJX : forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
  img_env val A_LIM E ->
  st_ok_pi segs val E ss (restrict (w_H W) ms) ->
  sym_runN_pi tpi0 n ss = (ss', st) -> pi_plain_stop st ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok_x E (ss_mem ss) G XO OUT STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  run_post_pi_AJX W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
  SRr segs W (mkCfg ms mdc) Q.
Proof using All.
intros W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
unfold sym_runN_pi in Hrun. rewrite <- Htpi in Hrun.
destruct (PaRun.sym_run_pi_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM
  _ E ss ss' st _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
eapply (SRr_chain_AJX W E (abs_ss val ss) (abs_ss val ss') ms msr');
[ exact Hms | | destruct ss; exact Hfr | exact HJ | destruct ss; exact Hwr | ].
- destruct st; cbn [PaRun.prun_post] in HP; first [exact HP | destruct Hst].
- intros ms' mat' HS' HJ' HF HF' HGr. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HGr].
Qed.

Lemma SRr_run_to_pi_AJX : forall W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
  img_env val A_LIM E ->
  st_ok_pi segs val E ss (restrict (w_H W) ms) ->
  sym_run_toN_pi tpi0 n stop ss = (ss', st) -> pi_plain_stop st ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok_x E (ss_mem ss) G XO OUT STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  run_post_pi_AJX W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
  SRr segs W (mkCfg ms mdc) Q.
Proof using All.
intros W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
unfold sym_run_toN_pi in Hrun. rewrite <- Htpi in Hrun.
destruct (PaRun.sym_run_to_pi_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM
  _ stop E ss ss' st _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
eapply (SRr_chain_AJX W E (abs_ss val ss) (abs_ss val ss') ms msr');
[ exact Hms | | destruct ss; exact Hfr | exact HJ | destruct ss; exact Hwr | ].
- destruct st; cbn [PaRun.prun_post] in HP; first [exact HP | destruct Hst].
- intros ms' mat' HS' HJ' HF HF' HGr. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HGr].
Qed.

(* pcap YC45.v:41 SRr_run_pi_AJ_call over ajournal_gx: a run that stops at a call of s, at the callee's entry. *)
Lemma SRr_run_pi_AJX_call : forall W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
  img_env val A_LIM E ->
  st_ok_pi segs val E ss (restrict (w_H W) ms) ->
  sym_runN_pi tpi0 n ss = (ss', PRS_call s) ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok_x E (ss_mem ss) G XO OUT STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  run_post_AJX W E ss (setpc ss' (sigma s)) ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
  SRr segs W (mkCfg ms mdc) Q.
Proof using All.
intros W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HE HS Hrun HJ Hwr Hk.
unfold sym_runN_pi in Hrun. rewrite <- Htpi in Hrun.
destruct (PaRun.sym_run_pi_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM
  _ E ss ss' (PRS_call s) _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
cbn [PaRun.prun_post] in HP.
eapply (SRr_chain_AJX W E (abs_ss val ss) (setpc ss' (sigma s)) ms msr');
[ exact Hms | exact HP | destruct ss; exact Hfr | exact HJ | destruct ss; exact Hwr | ].
intros ms' mat' HS' HJ' HF HF' HGr. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HGr].
Qed.

Lemma SRr_run_to_pi_AJX_call : forall W n stop E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
  img_env val A_LIM E ->
  st_ok_pi segs val E ss (restrict (w_H W) ms) ->
  sym_run_toN_pi tpi0 n stop ss = (ss', PRS_call s) ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok_x E (ss_mem ss) G XO OUT STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  run_post_AJX W E ss (setpc ss' (sigma s)) ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
  SRr segs W (mkCfg ms mdc) Q.
Proof using All.
intros W n stop E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HE HS Hrun HJ Hwr Hk.
unfold sym_run_toN_pi in Hrun. rewrite <- Htpi in Hrun.
destruct (PaRun.sym_run_to_pi_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM
  _ stop E ss ss' (PRS_call s) _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
cbn [PaRun.prun_post] in HP.
eapply (SRr_chain_AJX W E (abs_ss val ss) (setpc ss' (sigma s)) ms msr');
[ exact Hms | exact HP | destruct ss; exact Hfr | exact HJ | destruct ss; exact Hwr | ].
intros ms' mat' HS' HJ' HF HF' HGr. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HGr].
Qed.

(* The step of a run whose stores are bytes the journal admits and the flag byte of the frame at the head of own,
   which the run leaves 0: the journal loses the frame (ajournal_gx_flag_write). *)
Lemma aj_gx_flag_run : forall W E ss ss' ms msr' STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q,
  msteps segs (restrict (w_H W) ms) msr' ->
  st_ok segs E ss' msr' ->
  frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k ->
  0 <= cid ->
  (forall a, in_wrange E (ss_mem ss) a ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a /\ ~ (sp0 <= a < sp0 + XO)) \/
     inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO) \/ a = flag_addr lyc cid pos) ->
  mbyte segs (ms_mem msr') (flag_addr lyc cid pos) = Some (Z_to_bv 8 0) ->
  run_post_AJX W E ss ss' ms STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) mdc k Q ->
  SRr segs W (mkCfg ms mdc) Q.
Proof using All.
intros W E ss ss' ms msr' STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q Hms HS' Hfr HJX Hcid Hwr Hflag0 Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
set (memc' := ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) in *.
assert (Hfr' : forall x : word, ~ in_wrange E (ss_mem ss) (bv_unsigned x) ->
  mrestrict (w_H W) memc' x = mrestrict (w_H W) (ms_mem ms) x) by (subst memc'; rewrite Hmm; exact Hfr).
assert (Hgr' : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) memc')) by (subst memc'; rewrite Hmm; exact Hgr).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E (ss_mem ss) a ->
  aview segs (w_H W) memc' a = aview segs (w_H W) (ms_mem ms) a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr'. rewrite unsigned_lit_small by lia. exact HWa. }
assert (Hsame' : same_but_materialized mdc (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame. }
assert (Hflag : aview segs (w_H W) memc' (flag_addr lyc cid pos) = Some 0).
{ unfold aview. subst memc'. rewrite Hmm. rewrite Hflag0. reflexivity. }
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- apply (ajournal_gx_flag_write segs B LAWS segs_low G XO OUT STK sp0 FP ly S W0 mem md own' lyc Sc W (ms_mem ms) mdc k
    cid pos memc' _ (in_wrange E (ss_mem ss)) HG Hcid HJX Heqw Hgr').
  + intros x Hx. subst memc'. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
  + exact Hsame'.
  + exact Hwr.
  + exact Hflag.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- exact Hfr'.
- exact Hgr'.
Qed.

(* (d) THE INLINE RELEASE IN A RUN: pcap's PcapFrame.v:459 aj_flag_store_pi over ajournal_gx, on the plain engine. The
   run's stores are bytes the journal admits (with own = (cid, pos) :: own') and the frame's flag byte (the `sb zero`
   through the word frame_alloc left at F + fs_frame_bytes cid - 8); the run's end state holds 0 in the flag byte; the
   continuation gets the journal at own' and stack_free_state cid pos Sc. *)
Lemma aj_gx_flag_store_pi : forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q,
  img_env val A_LIM E ->
  st_ok_pi segs val E ss (restrict (w_H W) ms) ->
  sym_runN_pi tpi0 n ss = (ss', st) -> pi_plain_stop st ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k ->
  0 <= cid ->
  (forall a, in_wrange E (ss_mem ss) a ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a /\ ~ (sp0 <= a < sp0 + XO)) \/
     inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO) \/ a = flag_addr lyc cid pos) ->
  (forall msr, st_ok_pi segs val E ss' msr -> mbyte segs (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
  run_post_pi_AJX W E ss ss' ms STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) mdc k Q ->
  SRr segs W (mkCfg ms mdc) Q.
Proof using All.
intros W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q HE HS Hrun Hst HJX Hcid Hwr Hflag0 Hk.
unfold sym_runN_pi in Hrun. rewrite <- Htpi in Hrun.
destruct (PaRun.sym_run_pi_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM
  _ E ss ss' st _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
assert (HS' : st_ok_pi segs val E ss' msr') by (destruct st; cbn [PaRun.prun_post] in HP; first [exact HP | destruct Hst]).
eapply (aj_gx_flag_run W E (abs_ss val ss) (abs_ss val ss') ms msr');
[ exact Hms | exact HS' | destruct ss; exact Hfr | exact HJX | exact Hcid | destruct ss; exact Hwr
| exact (Hflag0 msr' HS') | ].
intros ms' mat' HS2 HJ' HF HF' HGr. apply (Hk ms' mat' HS2 HJ'); destruct ss; first [exact HF | exact HF' | exact HGr].
Qed.

Lemma aj_gx_flag_store_to_pi : forall W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q,
  img_env val A_LIM E ->
  st_ok_pi segs val E ss (restrict (w_H W) ms) ->
  sym_run_toN_pi tpi0 n stop ss = (ss', st) -> pi_plain_stop st ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k ->
  0 <= cid ->
  (forall a, in_wrange E (ss_mem ss) a ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a /\ ~ (sp0 <= a < sp0 + XO)) \/
     inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO) \/ a = flag_addr lyc cid pos) ->
  (forall msr, st_ok_pi segs val E ss' msr -> mbyte segs (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
  run_post_pi_AJX W E ss ss' ms STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) mdc k Q ->
  SRr segs W (mkCfg ms mdc) Q.
Proof using All.
intros W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q HE HS Hrun Hst HJX Hcid Hwr Hflag0 Hk.
unfold sym_run_toN_pi in Hrun. rewrite <- Htpi in Hrun.
destruct (PaRun.sym_run_to_pi_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM
  _ stop E ss ss' st _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
assert (HS' : st_ok_pi segs val E ss' msr') by (destruct st; cbn [PaRun.prun_post] in HP; first [exact HP | destruct Hst]).
eapply (aj_gx_flag_run W E (abs_ss val ss) (abs_ss val ss') ms msr');
[ exact Hms | exact HS' | destruct ss; exact Hfr | exact HJX | exact Hcid | destruct ss; exact Hwr
| exact (Hflag0 msr' HS') | ].
intros ms' mat' HS2 HJ' HF HF' HGr. apply (Hk ms' mat' HS2 HJ'); destruct ss; first [exact HF | exact HF' | exact HGr].
Qed.
End pe.

(* ==========================================================================
   Section g: the instances at LINK's listing (LinkSyms.lsym, LinkPa PAListing / PAImg), as LinkWalk.v Section g
   ========================================================================== *)
Section g.
Context {L : ptable lsym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.

Definition paj_run_plain_x (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
SRr_run_pi_AJX lsym pa_segs B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L pl_tpi
pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_tpi_eq G HG XO OUT.
Definition paj_run_to_plain_x (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
SRr_run_to_pi_AJX lsym pa_segs B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L pl_tpi
pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_tpi_eq G HG XO OUT.
Definition paj_run_call_plain_x (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
SRr_run_pi_AJX_call lsym pa_segs B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L pl_tpi
pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_tpi_eq G HG XO OUT.
Definition paj_run_to_call_plain_x (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
SRr_run_to_pi_AJX_call lsym pa_segs B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L pl_tpi
pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_tpi_eq G HG XO OUT.
Definition paj_flag_plain_x (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
aj_gx_flag_store_pi lsym pa_segs B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L pl_tpi
pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_tpi_eq G HG XO OUT.
Definition paj_flag_to_plain_x (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
aj_gx_flag_store_to_pi lsym pa_segs B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L pl_tpi
pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_tpi_eq G HG XO OUT.
End g.
End a.
