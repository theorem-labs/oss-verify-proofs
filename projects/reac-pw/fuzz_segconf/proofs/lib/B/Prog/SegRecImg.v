(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CmdRecImg.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; Cmd*/cmd_* -> Seg*/seg_*; the Require of RtPFShared / RtPFCmd it does not use left out; the program statics are fuzz_segconf's one range (A_LONGL); the stack guard 0x6045d8 -> 0x5ff078; musl's word-loop constants 0x10358..0x10378 -> [SegInstA.memchr_loA, SegInstA.memchr_hiA) (0x10350, 0x10370). *)
(* Modified by Theorem Labs, 2026-10: the image-B twin of lib/A/Prog/SegRecImg.v (commit 4f361f065164): module paths and image B's values. *)
(* The image group of the per-binary facts of fuzz_command.asan: a heap string's word tail (cmd_heap_tail_vis), the
   program's statics apart from the runtime's (cmd_prog_unowned), RtDefs' read-only view from arodata_okP
   (cmd_rom_view_on), and the image facts of the pinned image (cmd_img_facts_tfib, by the closed checks of
   CmdRecImgChk.v). The shadow lemmas cmd_addressable_chk, cmd_hull_vis_chk, cmd_aread_ok_chk are in CmdRecBase.v,
   which every group requires. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YM05 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YF0m YB1v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YE2k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegImg SegPgBase SegBase SegRo SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegRecBase SegRecImgChk.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* Every lemma below is closed over exactly `segs B LAWS HB`, the [IMG] ones over `segs B LAWS HB IMG`
   (the Section form of the per-binary facts' statements). *)
Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HB : SegBSyms B.
(* the core's AR_block_word_vis (lib/Reusable/YG0d_tail.v:57) at the word of [e] *)
Lemma seg_heap_tail_vis : forall ly S (W : world segs) mem md p n e, AR segs B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis segs W mem e.
Proof using LAWS HB.
intros ly S W mem md p n e HAR Hin He a Ha. exact (AR_block_word_vis segs B ly S W mem md p n e a HAR Hin He ltac:(lia)).
Qed.
Hypothesis IMG : seg_img_facts segs B.
(* G_REC_UNOWNED: g_rec, record.spill and g_quitting are image bytes outside the runtime's owned ranges and the
   errno cell *)
Lemma seg_prog_unowned : forall a, inFP seg_PG a ->
in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof using LAWS HB IMG.
intros a Ha. split; [exact (cif_prog_img _ _ IMG a Ha)|].
destruct Ha as (r & Hr & Ha). rewrite (ts_owned B HB), (ts_errno B HB). split.
- apply (crf_disj_notin (fst r, snd r - fst r)); [exact (proj1 (forallb_forall _ _) crf_pg_sep r Hr) | unfold in_zr; cbn [fst snd]; lia].
- intros He. pose proof (proj1 (forallb_forall _ _) crf_pg_noerrno r Hr) as Hd. cbn beta in Hd.
  unfold zr_disjointb in Hd. cbn [fst snd] in Hd. apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
Qed.
(* RtDefs' rt_rom_view is the ROM disjunct of arodata_okP, for any RLO RHI. The proof is the check_reply_answer walk's
   rt_rom_view_of_aro (an earlier version of lib/A/Prog/check_reply_answer_k.v:329-330). *)
Lemma seg_rom_view_on : forall RLO RHI (W : world segs) mem,
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) -> rt_rom_view segs B W mem.
Proof using LAWS HB IMG.
intros RLO RHI W mem HR a Hrom Ho He. apply HR; [left; exact Hrom | exact Ho | exact He].
Qed.
(* the shared snprintf / sprintf contracts' read-only premise at a call site (the unowned half,
   rt_rom_view; the contracts read the runtime-owned read-only bytes off AR themselves), from arodata_okP. The names and
   arguments are the ones the call sites use (one lemma per contract, as before) *)
Lemma seg_consts_view_snp : forall RLO RHI (W : world segs) mem,
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) -> rt_rom_view segs B W mem.
Proof using LAWS HB IMG. exact seg_rom_view_on. Qed.
Lemma seg_consts_view_sp : forall RLO RHI (W : world segs) mem,
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) -> rt_rom_view segs B W mem.
Proof using LAWS HB IMG. exact seg_rom_view_on. Qed.
End img.

(** * The image facts of the pinned image *)
(* every byte of a read-only segment has an image byte *)
Lemma crf_tfib_rom_some : forall a, in_rom tfibsegs a -> seg_rom tfibsegs (Z_to_bv 64 a) <> None.
Proof.
intros a (s & Hs & Hw & Ha). pose proof (proj1 (forallb_forall _ _) crf_rom_all s Hs) as Hb. cbn beta in Hb.
rewrite Hw in Hb. cbv beta iota in Hb. apply crf_some_ok.
apply (crf_zallt_ok _ _ _ Hb). rewrite N_nat_Z. lia.
Qed.
Lemma seg_img_facts_tfib : forall B, SegBSyms B -> @seg_img_facts YE2k.tfib_sink_head tfibsegs B.
Proof.
intros B HB. constructor.
- apply seg_ro_in_of. intros a Ha. apply Exists_exists in Ha as (r & Hr & Ha). cbv beta.
  pose proof (proj1 (forallb_forall _ _) crf_ro_objs_sep r Hr) as Hb. apply andb_prop in Hb as [H1 H2].
  rewrite (ts_owned B HB), (ts_errno B HB). split; [exact (crf_disj_notin r _ a H1 Ha)|].
  intros He. unfold zr_disjointb in H2. cbn [fst snd] in H2. unfold in_zr in Ha.
  apply orb_prop in H2 as [H2|H2]; apply Z.leb_le in H2; lia.
- apply seg_ro_in_of. intros a Ha. apply Exists_exists in Ha as (r & Hr & Ha).
  exact (crf_img_rangeb_ok tfibsegs r a (proj1 (forallb_forall _ _) crf_ro_objs_img r Hr) Ha).
- apply seg_ro_in_of. intros a Ha. apply Exists_exists in Ha as (r & Hr & Ha).
  exact (crf_ro_rangeb_ok tfibsegs _ _ r a (proj1 (forallb_forall _ _) crf_ro_objs_ro r Hr) Ha).
- intros e He. apply crf_bytes_b_ok. exact (proj1 (forallb_forall _ _) crf_ro_image_chk e He).
- intros e a He Ha. apply crf_rom_b_ok.
  pose proof (proj1 (forallb_forall _ _) crf_tails_chk e He) as Hb. cbn beta in Hb.
  apply (crf_zallt_ok _ _ (e + 1) Hb). pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
  rewrite Z2Nat.id by lia. lia.
- exact crf_tfib_rom_some.
- intros a (r & Hr & Ha).
  apply (crf_img_rangeb_ok tfibsegs (fst r, snd r - fst r) a); [exact (proj1 (forallb_forall _ _) crf_pg_img r Hr) | unfold in_zr; cbn [fst snd]; lia].
- intros a (r & Hr & Ha) Hro. pose proof (crf_ro_endb_ok tfibsegs a crf_tfib_ro_end Hro) as E.
  unfold seg_PG, A_LONGL in Hr.
  destruct Hr as [<-|[]]; cbn [fst snd] in Ha; lia.
- intros a Ha. rewrite (ts_errno B HB) in Ha. apply crf_some_ok.
  exact (crf_zallf_ok _ 4 TFIB_ERRNO crf_tfib_errno_rom a ltac:(lia)).
- exact seg_relro_img.
- intros a Ha. pose proof (crf_ro_endb_ok tfibsegs a crf_tfib_ro_end Ha) as E.
  change (a < YE2k.A_ofl_head). unfold YE2k.A_ofl_head. lia.
- intros a Ha. exact (crf_ro_endb_ok tfibsegs a crf_tfib_ro_end Ha).
- intros a Ha. apply crf_some_ok. exact (crf_zallf_ok _ 8 0x5ff838 crf_tfib_guard_rom a ltac:(lia)).
- intros e a [(s & Hs & Hw & He) | He] Ha.
  + pose proof (proj1 (forallb_forall _ _) crf_seg_al s Hs) as Hal. cbn beta in Hal.
    apply andb_prop in Hal as [A1 A2]. apply Z.eqb_eq in A1. apply Z.eqb_eq in A2.
    apply crf_tfib_rom_some. exists s. split; [exact Hs | split; [exact Hw|]].
    clear - A1 A2 He Ha. Z.div_mod_to_equations. lia.
  + apply crf_some_ok. apply (crf_zallt_ok _ _ _ crf_relro_some).
    unfold SEG_RLO, SEG_RHI in *. rewrite Z2Nat.id by lia. clear - He Ha. Z.div_mod_to_equations. lia.
- intros a Ha. apply crf_rom_b_ok. exact (crf_zallt_ok _ _ _ crf_snl_rom a ltac:(unfold SegInstB.memchr_loA, SegInstB.memchr_hiA in *; cbn; lia)).
Qed.
(* the name the entry function's walk carries for the strnlen constants' read-only bytes *)
Lemma seg_snl_rom {SK : YI16.sink_head} : forall segs B, @seg_img_facts SK segs B ->
  forall a, SegInstB.memchr_loA <= a < SegInstB.memchr_hiA -> in_rom segs a.
Proof. intros segs B IMG. exact (cif_snl_rom segs B IMG). Qed.
Print Assumptions seg_heap_tail_vis.
Print Assumptions seg_prog_unowned.
Print Assumptions seg_rom_view_on.
Print Assumptions seg_img_facts_tfib.
