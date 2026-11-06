(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the IMAGE B (fs.asan-ubsan, UBSan trap mode) walk of parse_value against
   lib/B/FSH_Fn_reader.v parse_value_spec (CTX-free; the text of a working branch 035561e0fd4 = a working branch
   311139dc663: skip_ws_spec's post keeps [sp, ot) but [q, q + 8), parse_value_spec's k = 0 arm
   `q = spZ regs + 8 /\ raZ regs <= q`; both rulings a Theorem Labs lane and after the k = 0 gap report): the
   COMPOSITION, parse_value_holds : parse_value_spec tfibsegs B k (stages: FSW_parse_value.v; decode table:
   FSW_parse_value_tbl.v).
   rule 24 (lane brief (internal path), CONFIRM a Theorem Labs lane): proves function
   parse_value - fuzz_state image B asan-ubsan, entry 0x82fcc, level-indexed k = 0..2, narrow success form. Reuse search
   (run by a Theorem Labs lane, verbatim in the lane brief), the three result lines:
     proof-index: parse_value: 14 named, 35 by address, 0 related, 13 released lemma(s), an earlier delivery 58 named and 794
       name(s) holding it, 17 UNRELEASED working-branch file(s) in the lemma index, 0 UNRELEASED hit(s) on live working heads
     proof-index: parse_value_spec: 0 named, 0 by address, 0 related, 6 released lemma(s), 0 by file name, an earlier delivery 51
       named and 12 name(s) holding it, 2 UNRELEASED working-branch file(s) in the lemma index, 0 UNRELEASED hit(s) on live
       working heads
     proof-index: 0x82fcc: 0 named, 0 by address, 0 related, 0 released lemma(s), 0 by file name, an earlier delivery 0 named and
       0 name(s) holding it, 0 UNRELEASED working-branch file(s) in the lemma index, 105 UNRELEASED hit(s) on live working heads
   Port source (Lookup result): ported from a working branch 75e39a1f41d:proofs/omx-clap-core/fuzz_state/lib/
   B/Prog/{parse_value_disp,PvStr,PvItems,PvJoin,PvStep,PvHolds,ParseUnit}.v (COMPLETE old-form image-B walk of
   parse_value: entry/fake frame/skip_ws call pv_pro + pv_disp, parse_string arm pv_str_ok, parse_items arm pv_items_ok,
   epilogue pv_join + pvs_none, composition parse_value_step / parse_value_holds_b; all Qed, no admit), restated against
   parse_value_spec's frame lemma by lemma, NOT Required, NOT bridged; new-frame shape from image A's walk
   a working branch (ebb53c68f7d .. 00c6d1886e6: lib/A/FSH_parse_value.v pv_grant / pv_resume_sm /
   pv_seg0 / pv_sm / pv_epi / pv_strcall, lib/A/FSW_parse_value_calls.v pvc_objcall), copied and re-measured for B. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value_holds.v, with its module paths, module names and addresses changed; 579 of its 702 lines of code are new or changed and 2034 lines of the source are left out. *)
(* parse_value's OBJECT ARM as one segment (fs.asan, pf.c:283-298): from pv_front's object-arm hand-over at 0x831a0
   (the dispatch byte 123) to parse_value's return, into fpostU with parse_value_spec k's post for u = JObj ms.
   The chain: FSW_parse_value_calls.pvc_obj0 (0x831a0 -> A_parse_items), the parse_items call (pvc_objcall', below),
   FSH_parse_value.pv_obj1 (0x832f8 -> 0x83318) and FSH_parse_value.pv_epi (0x83318 -> ret).
   A lemma file for a Theorem Labs lane's composition (rule 24: no function proved here; parse_value's CONFIRM is
   a Theorem Labs lane's lookup/confirm-resume-2.md, the function theorem parse_value_holds is a Theorem Labs lane's).
   pvc_objcall' is pvc_objcall with one fact more: the frame's flag word at F + 56 (the flag address the epilogue
   reads, pv_epi's premise `val_mem ... (F + 56) 8 FL`) is carried across parse_items through the callee's journal
   (its frame clause keeps parse_value's own fake frame (0, pos), off the callee's FP). pvc_objcall's continuation
   gives the composed journal only, whose frame clause covers frames S, not the own frame; pv_strcall has the same
   gap for the string arm.
   The premises of pv_objarm (a Theorem Labs lane's specification, 2026-10-29T10:45Z, and the three hand-over facts it
   accepted later that day): parse_value_spec k's entry premises that the arm uses, pv_front's object-arm hand-over, the
   sp of the arm (register 2), the keep from the entry memory to the arm memory over [s, ot) (for the post's
   wkeep), the entry data carried to the arm (pj_in_ok at p + |ws|, rd_text, pobj, pj_zero, fs_glob at S2 and the
   arm memory), and the two frame-chain premises pvc_objcall takes, at the arm memory. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_frame FSW_ret FSH_Fn_reader FSW_rd
FSW_parse_value_tbl FSH_Fn_entry FSH_Fn_alloc FSW_K3 FSW_parse_string FSH_parse_value FSW_parse_value_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterValue PjIn PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YG0s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved.
   YI14 is required (not imported) so that the second probe names a loaded class. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

(* ================= memory-change helpers ================= *)
Section PO. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* the machine's view through w_H depends on the restricted memory only, also after unpoison *)
Lemma pvo_aview_ext : forall (H : word -> bool) U (m m' : word -> option byte),
  (forall x, mrestrict H m' x = mrestrict H m x) ->
  aview tfibsegs H (unpoison U m') = aview tfibsegs H (unpoison U m) /\ aview tfibsegs H m' = aview tfibsegs H m.
Proof.
intros H U m m' E.
assert (E1 : mrestrict H (unpoison U m') = mrestrict H (unpoison U m)).
{ apply functional_extensionality. intros x. specialize (E x). unfold mrestrict, unpoison in *.
  revert E. destruct (H x); intros E; [reflexivity|].
  destruct (in_ush U (bv_unsigned x)); [reflexivity | exact E]. }
assert (E2 : mrestrict H m' = mrestrict H m) by (apply functional_extensionality; exact E).
unfold aview. rewrite E1, E2. split; reflexivity.
Qed.

Lemma pvo_aview_pt : forall (H : word -> bool) (m m' : word -> option byte) a,
  mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' a E. unfold aview, mbyte. rewrite E. reflexivity. Qed.

Lemma pvo_val_tr : forall (m m' : word -> option byte) a n v,
  (forall j, (j < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat j)) = m (Z_to_bv 64 (a + Z.of_nat j))) ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof. intros m m' a n v E Hv j Hj. unfold mbyte. rewrite (E j Hj). exact (Hv j Hj). Qed.

(* struct pj_in and the text, read at their own bytes only *)
Lemma pvo_in_tr : forall (m m' : word -> option byte) q text len p d tb,
  (forall a, q <= a < q + 24 \/ text <= a < text + len -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  PjIn.pj_in_ok tfibsegs m q text len p d tb -> PjIn.pj_in_ok tfibsegs m' q text len p d tb.
Proof.
intros m m' q text len p d tb E HIN.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
destruct HIN as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
refine (conj _ (conj _ (conj _ (conj _ (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj _ (conj H11 H12))))))))))).
- destruct H1 as (A0 & A1 & A2). split; [exact A0|]. split; [exact A1|]. intros i Hi.
  rewrite <- (A2 i Hi). rewrite OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.length_le8 in Hi.
  unfold OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.mrd,
    OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.wa.
  rewrite E by lia. reflexivity.
- destruct H2 as (A0 & A1 & A2). split; [exact A0|]. split; [exact A1|]. intros i Hi.
  rewrite <- (A2 i Hi). rewrite OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.length_le8 in Hi.
  unfold OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.mrd,
    OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.wa.
  rewrite E by lia. reflexivity.
- destruct H3 as (A0 & A1 & A2). split; [exact A0|]. split; [exact A1|]. intros i Hi.
  rewrite <- (A2 i Hi). rewrite OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.length_le4 in Hi.
  unfold OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.mrd,
    OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.wa.
  rewrite E by lia. reflexivity.
- destruct H4 as (A0 & A1 & A2). split; [exact A0|]. split; [exact A1|]. intros i Hi.
  pose proof (A2 i Hi) as Hw.
  unfold OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.wa, wview in *.
  rewrite E by lia. exact Hw.
- destruct H10 as (A0 & A1 & A2). split; [exact A0|]. split; [exact A1|]. intros i Hi.
  rewrite <- (A2 i Hi).
  unfold OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.mrd,
    OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.wa.
  rewrite E by lia. reflexivity.
Qed.

(* the reader block's head word, read at its own bytes only, across a state with the same blocks *)
Lemma pvo_rblock_tr : forall ly S S' (W : world tfibsegs) mx md (m m' : word -> option byte) p n,
  AR tfibsegs B ly S W mx md -> ablocks B ly S' = ablocks B ly S ->
  (forall z, p - HEAD <= z < p - 8 -> mrestrict (w_H W) m' (Z_to_bv 64 z) = mrestrict (w_H W) m (Z_to_bv 64 z)) ->
  fs_rblock tfibsegs B ly S W m p n -> fs_rblock tfibsegs B ly S' W m' p n.
Proof.
intros ly S S' W mx md m m' p n HAR Eab E Hb. pose proof Hb as (Hin & Hal & Hn & Hv).
split; [rewrite Eab; exact Hin|]. split; [exact Hal|]. split; [exact Hn|].
apply (pvo_val_tr (mrestrict (w_H W) m)); [|exact Hv].
intros j Hj. apply E. unfold HEAD. lia.
Qed.

(* a reader tree, read at v's 56 bytes and its blocks only, across a state with the same blocks *)
Lemma pvo_rtree_tr : forall ly S S' (W : world tfibsegs) mx md (m m' : word -> option byte) v t D,
  AR tfibsegs B ly S W mx md -> ablocks B ly S' = ablocks B ly S ->
  (forall z, 0 <= z < 2 ^ 64 -> (v <= z < v + 56 \/ exists a k, In (a, k) D /\ a - HEAD <= z < a + k) ->
     mrestrict (w_H W) m' (Z_to_bv 64 z) = mrestrict (w_H W) m (Z_to_bv 64 z)) ->
  rtree tfibsegs B ly S W m v t D -> rtree tfibsegs B ly S' W m' v t D.
Proof.
intros ly S S' W mx md m m' v t D HAR Eab E (HN & HB & HI).
split; [|split; [|exact HI]].
- apply (PjStruct.pj_node_frame tfibsegs t (mrestrict (w_H W) m) (fun a k => In (a, k) D)
    (mrestrict (w_H W) m') (fun a k => In (a, k) D) v D HN); [intros a k Hak; exact Hak|].
  intros x Hx.
  assert (Ex : x = Z_to_bv 64 (bv_unsigned x)) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite Ex. apply E; [exact (u64_range x)|].
  destruct Hx as [Hx|((a & k) & Hb & Hx)]; [left; exact Hx|].
  right. exists a, k. split; [exact Hb|]. unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx. unfold HEAD. lia.
- intros a k Hak.
  destruct (fsw_rblock_low B ly S W mx md m a k HAR (HB a k Hak)) as (L1 & L2).
  pose proof asan_consts as (C1 & _).
  apply (pvo_rblock_tr ly S S' W mx md m m' a k HAR Eab); [|exact (HB a k Hak)].
  pose proof (HB a k Hak) as (_ & _ & Hk0 & _).
  intros z Hz. apply E; [unfold HEAD in *; lia|]. right. exists a, k. split; [exact Hak | lia].
Qed.

(* the frames after the release of the frame pushed last *)
Lemma pvo_frames_free : forall S3 S pos, frames S3 = (0, pos) :: frames S ->
  frames (stack_free_state 0 pos S3) = frames S.
Proof.
intros S3 S pos H. change (frames (stack_free_state 0 pos S3)) with (del_pos (frames S3) 0 pos).
rewrite H. cbn [del_pos]. rewrite !Z.eqb_refl. reflexivity.
Qed.

(* fuzz/alloc.c's statics are no read-only byte (FSW_put_grow_tail.v pgt_pstat_not_ro, restated: that file is
   another lane's) *)
Lemma pvo_pstat_not_ro : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
assert (HC : forallb (fun r => forallb (fun sg => seg_writable sg || (snd r <=? Z.of_N (seg_base sg))
                                  || (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? fst r)) tfibsegs
                               && ((snd r <=? FS_RLO) || (FS_RHI <=? fst r))) FS_PSTAT_FP = true)
  by (vm_compute; reflexivity).
intros a Hro (r & Hr & Ha). rewrite forallb_forall in HC. specialize (HC r Hr).
apply andb_prop in HC as [HC1 HC2].
destruct Hro as [(sg & Hsg & Hw & Hin) | Hrl].
- rewrite forallb_forall in HC1. specialize (HC1 sg Hsg). rewrite Hw in HC1. cbn [orb] in HC1.
  apply orb_prop in HC1 as [HC1 | HC1]; apply Z.leb_le in HC1; lia.
- apply orb_prop in HC2 as [HC2 | HC2]; apply Z.leb_le in HC2; lia.
Qed.

(* bytes of a live frame of the caller, outside the callee's footprint, keep their value across the callee
   (FSH_check_reject_clean_starved.v crcs_val_keep_call, restated: that file is another lane's walk) *)
Lemma pvo_val_keep_call : forall STKc sp1 FPc lyc Sc Uc (W : world tfibsegs) memC mdC ly' S' U' W' mem' md' kc cid pos
    a n v,
  ajournal tfibsegs B STKc sp1 FPc lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memC mdC -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  In (cid, pos) (frames Sc) -> 0 <= cid ->
  frame_addr lyc cid pos <= a -> a + Z.of_nat n <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  (forall x, a <= x < a + Z.of_nat n -> ~ inFP FPc x) ->
  val_mem tfibsegs (mrestrict (w_H W) memC) a n v -> val_mem tfibsegs (mrestrict (w_H W') mem') a n v.
Proof.
intros STKc sp1 FPc lyc Sc Uc W memC mdC ly' S' U' W' mem' md' kc cid pos a n v HJc HARUc OK' PO' Hin Hc0 Hlo Hhi
  HnFP HV k Hk.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJc as (HAR' & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & F4 & _).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact HAR' | split; [exact OK' | exact PO']]).
pose proof (ARU_AR tfibsegs B lyc Sc Uc W memC mdC HARUc) as HARc.
assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hin).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (EA : frame_addr ly' cid pos = frame_addr lyc cid pos) by (unfold frame_addr; rewrite EF; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc W (unpoison Uc memC) mdC cid pos HARc Hin) as (_ & _ & Hfc & _).
destruct (al_frames _ _ LAWS ly' S' W' (unpoison U' mem') md' cid pos HAR' Hin') as (_ & _ & Hf' & _).
destruct (frames_bounds tfibsegs B LAWS lyc Sc W (unpoison Uc memC) mdC cid pos HARc Hin) as (H4096 & Hceil & _).
pose proof asan_consts as (C1 & _).
set (x := a + Z.of_nat k).
assert (Hx : frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid) by (subst x; lia).
rewrite <- (HV k Hk). apply (mbyte_of_aview tfibsegs). fold x.
rewrite <- (aview_at tfibsegs (w_H W') (unpoison U' mem') mem' x).
2:{ apply (fsw_unpoison_notowned B ly' S' U' W' mem' md' x HARU'); [lia|].
    rewrite EA in Hf'. exact (proj2 (Hf' x Hx)). }
rewrite (F4 cid pos x Hin (or_introl Hx) (HnFP x ltac:(subst x; lia))).
apply (aview_at tfibsegs).
apply (fsw_unpoison_notowned B lyc Sc Uc W memC mdC x HARUc); [lia|]. exact (proj2 (Hfc x Hx)).
Qed.

(* the bytes the epilogue writes (pv_epi's pe_wr: the frame (0, pos), its shadow, its flag byte) are none of: a byte
   at or above alloc_ceiling, an image byte, a byte of a live block, a byte of another live frame *)
Lemma pvo_off_pe : forall ly S (W : world tfibsegs) m md pos l a,
  AR tfibsegs B ly S W m md -> frames S = (0, pos) :: l ->
  (alloc_ceiling <= a \/ in_img tfibsegs a \/
   (exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
   (exists cid pos', In (cid, pos') l /\ frame_addr ly cid pos' <= a < frame_addr ly cid pos' + fs_frame_bytes cid)) ->
  ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) a.
Proof.
intros ly S W m md pos l a HAR Hfr Ha.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _ & C3 & _).
assert (Hin : In (0, pos) (frames S)) by (rewrite Hfr; left; reflexivity).
destruct (al_frames _ _ LAWS ly S W m md 0 pos HAR Hin) as (HF32 & HFapp & HFb & HFsh).
destruct (frames_bounds tfibsegs B LAWS ly S W m md 0 pos HAR Hin) as (HF4096 & HFc & _).
destruct (al_flag _ _ LAWS ly S W m md 0 pos HAR Hin) as (HFLp & HFLo & HFLapp & HFLc).
change (fs_frame_bytes 0) with 64 in *.
unfold pe_wr.
destruct Ha as [Ha | [Ha | [(b & n & Hb & Ha) | (cid & pos' & Hc & Ha)]]].
- intros [H | [H | H]]; [lia | | lia].
  unfold SHADOW_OFF in H. Z.div_mod_to_equations. lia.
- pose proof (fs_segs_img a Ha) as Hl.
  intros [H | [H | H]].
  + exact (proj2 (al_client_img _ _ LAWS ly S W m md a HAR
      (or_intror (or_introl (ex_intro _ 0 (ex_intro _ pos (conj Hin H)))))) Ha).
  + unfold FS_IMG_END, SHADOW_OFF in *. lia.
  + subst a. exact (proj2 (al_client_img _ _ LAWS ly S W m md (flag_addr ly 0 pos) HAR
      (or_intror (or_intror (ex_intro _ 0 (ex_intro _ pos (conj Hin eq_refl)))))) Ha).
- destruct (al_blocks _ _ LAWS ly S W m md b n HAR Hb) as (_ & _ & _ & Bapp & Bown & _).
  pose proof (sep_block_frame tfibsegs B LAWS ly S W m md b n 0 pos HAR Hb Hin) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. change (fs_frame_bytes 0) with 64 in D.
  pose proof (in_app_addr _ _ a Bapp Ha) as Aa.
  intros [H | [H | H]]; [lia | | ].
  + unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
  + subst a. exact (proj2 (Bown _ Ha) HFLo).
- assert (Hc' : In (cid, pos') (frames S)) by (rewrite Hfr; right; exact Hc).
  destruct (al_frames _ _ LAWS ly S W m md cid pos' HAR Hc') as (_ & Capp & Cb & _).
  destruct (al_sep tfibsegs B LAWS ly S W m md HAR) as (PS & _).
  destruct (YG0s.pairwise_app_inv zdisjoint _ _ PS) as (_ & PF & _).
  rewrite Hfr in PF. cbn [map pairwise fst snd] in PF. destruct PF as (PF1 & _).
  rewrite Forall_forall in PF1.
  pose proof (PF1 _ (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ (cid, pos') Hc)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. change (fs_frame_bytes 0) with 64 in D.
  pose proof (in_app_addr _ _ a Capp Ha) as Aa.
  intros [H | [H | H]]; [lia | | ].
  + unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
  + subst a. exact (proj2 (Cb _ Ha) HFLo).
Qed.

(* a shadow byte of an application byte below alloc_ceiling outside the frame (0, pos) is no byte the epilogue writes *)
Lemma pvo_shadow_off : forall ly S (W : world tfibsegs) m md pos x,
  AR tfibsegs B ly S W m md -> In (0, pos) (frames S) -> 0 <= x < alloc_ceiling ->
  ~ (frame_addr ly 0 pos <= x < frame_addr ly 0 pos + 64) ->
  ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) (shadow_of_addr SHADOW_OFF x).
Proof.
intros ly S W m md pos x HAR Hin Hx Hn.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _ & C3 & _).
destruct (al_frames _ _ LAWS ly S W m md 0 pos HAR Hin) as (HF32 & HFapp & _ & _).
destruct (frames_bounds tfibsegs B LAWS ly S W m md 0 pos HAR Hin) as (HF4096 & HFc & _).
destruct (al_flag _ _ LAWS ly S W m md 0 pos HAR Hin) as (_ & _ & HFLapp & HFLc).
change (fs_frame_bytes 0) with 64 in *.
unfold pe_wr, shadow_of_addr.
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
intros [H | [H | H]]; Z.div_mod_to_equations; lia.
Qed.

(* the text after the white-space run ws *)
Lemma pvo_skipn_map : forall {X Y : Type} (f : X -> Y) n l, skipn n (map f l) = map f (skipn n l).
Proof. intros X Y f n. induction n as [|n IH]; intros [|x l]; cbn; auto. Qed.
Lemma pvo_rest_at : forall tb text p (ws wt rest : list Z), text <= p ->
  ReaderRes.rest_at tb text p = ws ++ wt ++ rest ->
  ReaderRes.rest_at tb text (p + Z.of_nat (length ws)) = wt ++ rest.
Proof.
intros tb text p ws wt rest Hp H. unfold ReaderRes.rest_at, ReaderRes.zb in *.
replace (Z.to_nat (p + Z.of_nat (length ws) - text)) with (length ws + Z.to_nat (p - text))%nat by lia.
rewrite <- skipn_skipn, <- pvo_skipn_map, H. clear.
induction ws as [|w ws IH]; cbn [length skipn app]; [reflexivity | exact IH].
Qed.
End PO.

(* ================= the parse_items call, carrying the frame's flag word ================= *)
Section OA. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the fake-frame kit's unit laws pv_epi takes (FSH_parse_value.v Section EP2) *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
(* parse_value's level; the callee parse_items at level k (owner: the Theorem Labs lane) *)
Variable k : nat.
Hypothesis PI : @parse_items_spec fx rc SK tfibsegs B k.

(* FSW_parse_value_calls.pvc_objcall with the flag word added: the premise `val_mem ... (F + 56) 8 FL` with F + 56 ..
   F + 64 off the callee's FP, and the same fact at the return (the callee's journal keeps the bytes of parse_value's
   own fake frame (0, pos), a frame of the callee's start state S2, off its FP: pvo_val_keep_call). Otherwise the
   statement and the proof are pvc_objcall's. *)
Lemma pvc_objcall' : forall STK ot FP ly S S2 U (W : world tfibsegs) mem md regsC memC mdC pos q s sp1 v text len p
    (tb : list byte) tcap (ms : list (list Z * PjTree.jv)) (pr : bool) (rest : list Z) live peak cnt fail FL
    (Qp : world tfibsegs -> config -> Prop),
  let tr := PjRoundTrip.ttrace (PjTree.JObj ms) in
  let wt := concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k)) in
  (k <= 1)%nat ->
  spZ regsC = sp1 -> YK11.getr regsC 10%bv = Z_to_bv 64 q -> YK11.getr regsC 11%bv = Z_to_bv 64 v ->
  YK11.getr regsC 12%bv = Z_to_bv 64 1 -> YK11.getr regsC 1%bv = Z_to_bv 64 0x832f8 ->
  YK11.getr regsC 3%bv = w64 (as_gp B) -> YK11.getr regsC 4%bv = w64 (as_tp B) ->
  YK11.getr regsC 8%bv = Z_to_bv 64 s -> 0 <= s < 2 ^ 64 ->
  sp1 mod 16 = 0 -> ot - STK <= sp1 - STK_parse_items (1 - k) -> sp1 <= ot -> sp1 + 16 <= q ->
  (exists ch0, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) sp1 s ch0) ->
  (exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) sp1 q chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memC) ->
  FSupoisonU.fs_heads B ly S2 U ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k) ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) memC) q text len p (Z.of_nat k) tb ->
  rd_win tfibsegs regsC ly W memC q ot ->
  rd_text tfibsegs B ly S2 W memC text len tcap ->
  ReaderRes.rest_at tb text p = wt ++ rest ->
  FSDocStrs.fs_doc_values (PjTree.JObj ms) -> FSDocStrs.fs_doc_strings (PjTree.JObj ms) ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj ms) -> (PjTree.depth (PjTree.JObj ms) <= 2 - k)%nat ->
  pobj tfibsegs B ly S2 W memC v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) memC) v ->
  (v + 56 <= sp1 - STK_parse_items (1 - k) \/ ot <= v) -> (v + 56 <= text - HEAD \/ text + tcap <= v) ->
  fs_glob tfibsegs W memC live peak cnt fail -> quiet cnt fail (Z.of_nat (length tr)) ->
  rd_sizes_ok tr -> live + rd_live tr < 2 ^ 64 ->
  st_nev S2 + rd_ev tr <= EV_MAX -> blocks_bytes S2 + rd_live tr <= LIVE_MAX ->
  ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U memC) mdC 0 ->
  ARU tfibsegs B ly S2 U W memC mdC ->
  (forall a, inFP ([(v, v + 56)] ++ FS_PSTAT_FP) a -> inFP FP a) ->
  (* ADDED: the frame's flag word at the call, its 8 bytes off the callee's FP *)
  val_mem tfibsegs (mrestrict (w_H W) memC) (frame_addr ly 0 pos + 56) 8 FL ->
  (forall x, frame_addr ly 0 pos + 56 <= x < frame_addr ly 0 pos + 64 -> ~ inFP ([(v, v + 56)] ++ FS_PSTAT_FP) x) ->
  (forall ly2 S3 W2 regs2 mem2 md2 (D Da : list (Z * Z)),
     Permutation Da D ->
     ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly2 S3 W2
       (unpoison (U ++ rd_heads Da) mem2) md2 (rd_ev tr) ->
     ARU tfibsegs B ly2 S3 (U ++ rd_heads Da) W2 mem2 md2 ->
     aregs_preserved regsC regs2 ->
     Forall (fun r => YK11.getr regs2 r = YK11.getr regsC r) [8; 9; 18; 20; 23; 24; 26]%bv ->
     YK11.getr regs2 10%bv = w64 0 ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) mem2) q text len (p + Z.of_nat (length wt)) (Z.of_nat k) tb ->
     wkeep tfibsegs W W2 memC mem2 sp1 ot q 24 ->
     Permutation (ablocks B ly2 S3) (ablocks B ly S2 ++ rd_hblocks D) ->
     rtree tfibsegs B ly2 S3 W2 mem2 v (PjTree.JObj ms) D -> rd_sum D = PjGrammar.held tr ->
     (length D <= length tr)%nat ->
     pobj tfibsegs B ly2 S3 W2 mem2 v -> rd_text tfibsegs B ly2 S3 W2 mem2 text len tcap ->
     (exists peak', peak <= peak' /\
        fs_glob tfibsegs W2 mem2 (live + PjGrammar.held tr) peak' (cnt + Z.of_nat (length tr)) fail) ->
     (* ADDED: the flag word at the return *)
     val_mem tfibsegs (mrestrict (w_H W2) mem2) (frame_addr ly 0 pos + 56) 8 FL ->
     SRr tfibsegs W2 (YG0d.cfg_at tfibsegs 0x832f8 regs2 mem2 md2) Qp) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regsC memC mdC) Qp.
Proof.
intros STK ot FP ly S S2 U W mem md regsC memC mdC pos q s sp1 v text len p tb tcap ms pr rest live peak cnt fail FL Qp
  tr wt Hk Csp C10 C11 C12 C1 C3 C4 C8 Hs64 Hal16 Hwin Hsp1ot Hq16 HCH0 HCHq HRO FH Hfr0 HIN HWIN HTX Hrest Hvals
  Hstrs Hwf Hdep HPo HZo Hvst Hvtx HGL Hquiet Hsz Hlive Hnev Hbb HJ HARU HFPv HVFL HNFL K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1a & _).
destruct HCH0 as [ch0 HCH0q].
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). cbn [app] in Hfrs.
assert (Hk01 : (1 - k = 0 \/ 1 - k = 1)%nat) by lia.
assert (HSTK0 : 0 <= STK_parse_items (1 - k)) by (destruct Hk01 as [E | E]; rewrite E; vm_compute; discriminate).
assert (HPREc : fpreU tfibsegs B (STK_parse_items (1 - k)) ly S2 U W regsC memC mdC ch0).
{ apply (fsw_fpreU_atFP B STK ot FP ly S U W (unpoison U mem) md [(0, pos)] ly S2 W memC mdC 0 regsC
    (STK_parse_items (1 - k)) (sp1 - ot) ch0 HJ HARU HRO);
    [rewrite Csp; lia | | lia | exact HSTK0 | lia | rewrite C1; vm_compute; reflexivity | | rewrite C3; reflexivity
     | rewrite C4; reflexivity |].
  - assert (Hot16 : ot mod 16 = 0) by (pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _);
      exact (proj1 Hstk)).
    rewrite Zminus_mod, Hal16, Hot16. reflexivity.
  - unfold raZ. rewrite C1. rewrite (unsigned_lit_small 0x832f8) by lia. lia.
  - unfold s0Z. rewrite Csp, C8, (unsigned_lit_small s) by lia. exact HCH0q. }
assert (HFR : Z.of_nat (length (frames S2)) <= FRL_parse_value (Z.of_nat k + 1))
  by (rewrite Hfrs; cbn [length]; unfold FRL_parse_value in *; lia).
assert (HCHq' : exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) (spZ regsC) q chq /\
  Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq)
  by (rewrite Csp; exact HCHq).
assert (Hsp16 : spZ regsC + 16 <= q) by (rewrite Csp; exact Hq16).
assert (Hvst' : v + 56 <= spZ regsC - STK_parse_items (1 - k) \/ ot <= v) by (rewrite Csp; exact Hvst).
eapply SRr_bind.
{ exact (PI ly S2 U W regsC memC mdC ch0 q ot v text len p tb tcap ms pr rest live peak cnt fail
    Hk HPREc FH HFR C10 C11 C12 HIN HWIN Hsp16 HCHq' HTX Hrest Hvals Hstrs Hwf Hdep HPo HZo Hvst' Hvtx HGL
    Hquiet Hsz Hlive Hnev Hbb). }
cbv beta. intros W' c' _ (D & Da & HDa & (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ')).
destruct HQ' as (Q10 & QIN & QWK & QPERM & QT & QSUM & QLEN & QPO & QTX & QGL).
subst c'. rewrite C1.
(* ADDED: the flag word across the callee (its journal's frame clause, (0, pos) a frame of S2) *)
assert (VFL' : val_mem tfibsegs (mrestrict (w_H W') mem') (frame_addr ly 0 pos + 56) 8 FL).
{ apply (pvo_val_keep_call B _ _ _ ly S2 U W memC mdC ly' S' (U ++ rd_heads Da) W' mem' md' _ 0 pos
    (frame_addr ly 0 pos + 56) 8 FL HJc HARU OK' PO'); [rewrite Hfrs; left; reflexivity | lia | lia | | | exact HVFL].
  - change (fs_frame_bytes 0) with 64. change (Z.of_nat 8) with 8. lia.
  - intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HNFL. lia. }
assert (HJ2 : ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md ([] ++ [(0, pos)]) ly' S' W'
  (unpoison (U ++ rd_heads Da) mem') md' (0 + rd_ev tr)).
{ apply (fsw_ajournal_sub5 B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U memC) mdC 0
    (STK_parse_items (1 - k) + (ot - spZ regsC)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) [] ly' S' W'
    (unpoison (U ++ rd_heads Da) mem') md' (rd_ev tr) HJ HJc); [rewrite Csp; lia | lia |].
  intros a Ha. pose proof (HFPv a Ha) as HaFP.
  destruct Ha as ((rlo, rhi) & Hr & Har). cbn [fst snd] in Har.
  apply in_app_or in Hr as [Hr | Hr].
  - cbn [In] in Hr. destruct Hr as [E | []]. injection E as <- <-.
    destruct HPo as [[((cid & pos' & Hcp & _ & _ & H1 & H2) & _) | ((b & m & Hb & H1 & H2) & _)] _].
    + rewrite Hfrs in Hcp. cbn [In] in Hcp. destruct Hcp as [E | Hcp].
      * injection E as <- <-. right; right; right; left.
        exists 0, pos. split; [left; reflexivity | left; unfold in_zr; cbn [fst snd]; lia].
      * right; right; right; right. split; [exact HaFP|].
        exists cid, pos'. split; [exact Hcp | unfold in_zr, frame_rng; cbn [fst snd]; lia].
    + left. split; [exact HaFP|]. exists b, m. split; [exact Hb | unfold HEAD in H1; lia].
  - right; right; left. split; [exact HaFP | exact (pvc_pstat_img a (ex_intro _ (rlo, rhi) (conj Hr Har)))]. }
cbn [app] in HJ2. rewrite Z.add_0_l in HJ2.
assert (HARU2 : ARU tfibsegs B ly' S' (U ++ rd_heads Da) W' mem' md')
  by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
assert (REGS : Forall (fun r => YK11.getr regs' r = YK11.getr regsC r) [8; 9; 18; 20; 23; 24; 26]%bv).
{ repeat (apply Forall_cons; [apply (fsw_pres regsC regs' _ HP); pv_cs|]). apply Forall_nil. }
rewrite Csp in QWK.
exact (K ly' S' W' regs' mem' md' D Da HDa HJ2 HARU2 HP REGS Q10 QIN QWK QPERM QT QSUM QLEN QPO QTX QGL VFL').
Qed.

(* ================= the object arm: pv_front's hand-over at 0x831a0 -> parse_value's post ================= *)
Lemma pv_objarm : forall ly S U (W : world tfibsegs) regs mem md ch q ot v text len p (tb : list byte) tcap
    (ms : list (list Z * PjTree.jv)) (pr : bool) (ws rest : list Z) live peak cnt fail S2 pos ms' mdx',
  let tr := PjRoundTrip.ttrace (PjTree.JObj ms) in
  let wt := concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k)) in
  (* parse_value_spec k's entry premises the arm uses (u = JObj ms) *)
  (k <= 2)%nat ->
  fpreU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k) ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p (Z.of_nat k) tb -> rd_win tfibsegs regs ly W mem q ot ->
  ReaderRes.rest_at tb text p = ws ++ wt ++ rest ->
  (forall x, In x (PjTree.JObj ms :: FSDocStrs.jv_vals (PjTree.JObj ms)) -> FSDocStrs.str_or_obj x) ->
  FSDocStrs.fs_doc_strings (PjTree.JObj ms) ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj ms) -> (PjTree.depth (PjTree.JObj ms) <= 2 - k)%nat ->
  pobj tfibsegs B ly S W mem v ->
  (v + 56 <= spZ regs - STK_parse_value (2 - k) \/ ot <= v) -> (v + 56 <= text - HEAD \/ text + tcap <= v) ->
  quiet cnt fail (Z.of_nat (length tr)) -> rd_sizes_ok tr -> live + rd_live tr < 2 ^ 64 ->
  st_nev S + rd_ev tr <= EV_MAX -> blocks_bytes S + rd_live tr <= LIVE_MAX ->
  (* pv_front's object-arm hand-over (its continuation with b0 = 123) *)
  In (0, pos) (frames S2) -> frames S2 = (0, pos) :: frames S ->
  ablocks B ly S2 = ablocks B ly S -> st_nev S2 = st_nev S -> blocks_bytes S2 = blocks_bytes S ->
  ms' = mkst (ms_regs ms') (Z_to_bv 64 0x831a0) (ms_mem ms') (seg_rom tfibsegs) ->
  YK11.getr (ms_regs ms') 8%bv = Z_to_bv 64 (spZ regs) ->
  YK11.getr (ms_regs ms') 9%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) ->
  YK11.getr (ms_regs ms') 18%bv = Z_to_bv 64 (frame_addr ly 0 pos) ->
  YK11.getr (ms_regs ms') 19%bv = Z_to_bv 64 v ->
  YK11.getr (ms_regs ms') 20%bv = Z_to_bv 64 q ->
  YK11.getr (ms_regs ms') 23%bv = Z_to_bv 64 SHADOW_OFF ->
  YK11.getr (ms_regs ms') 24%bv = Z_to_bv 64 (SHADOW_OFF + frame_addr ly 0 pos / 8) ->
  YK11.getr (ms_regs ms') 26%bv = Z_to_bv 64 (frame_addr ly 0 pos) ->
  YK11.getr (ms_regs ms') 3%bv = YK11.getr regs 3%bv ->
  YK11.getr (ms_regs ms') 4%bv = YK11.getr regs 4%bv ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms')) q 8 (p + Z.of_nat (length ws)) ->
  pv_inv (mrestrict (w_H W) (ms_mem ms')) regs (spZ regs) (frame_addr ly 0 pos) (flag_addr ly 0 pos) q
    (text + len) (p + Z.of_nat (length ws)) [123] ->
  ajournal tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W
    (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem ms')) mdx' 0 ->
  ARU tfibsegs B ly S2 U W (ms_mem ms') mdx' ->
  (* the hand-over's three additions (a Theorem Labs lane accepted, 2026-10-29): the arm's sp, the keep from the entry memory
     over [s, ot), the entry data carried to the arm *)
  YK11.getr (ms_regs ms') 2%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) ->
  wkeep tfibsegs W W mem (ms_mem ms') (spZ regs) ot q 24 ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) (ms_mem ms')) q text len (p + Z.of_nat (length ws)) (Z.of_nat k) tb ->
  rd_text tfibsegs B ly S2 W (ms_mem ms') text len tcap ->
  pobj tfibsegs B ly S2 W (ms_mem ms') v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) (ms_mem ms')) v ->
  fs_glob tfibsegs W (ms_mem ms') live peak cnt fail ->
  (* the two frame-chain premises of the parse_items call, at the arm memory (a Theorem Labs lane discharges them) *)
  (exists ch0, achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem ms'))) (32 * ((spZ regs - 160) / 32))
     (spZ regs) ch0) ->
  (exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem ms'))) (32 * ((spZ regs - 160) / 32)) q chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq) ->
  SRr tfibsegs W (mkCfg ms' mdx')
    (fun W' c' => exists D Da,
       Permutation Da D /\
       fpostU tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U W
         mem md (rd_ev tr) (U ++ rd_heads Da)
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10%bv = w64 0 /\
            PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len
              (p + Z.of_nat (length ws) + Z.of_nat (length wt)) (Z.of_nat k) tb /\
            wkeep tfibsegs W W' mem mem' (spZ regs) ot q 24 /\
            Permutation (ablocks B ly' S') (ablocks B ly S ++ rd_hblocks D) /\
            rtree tfibsegs B ly' S' W' mem' v (PjTree.JObj ms) D /\ rd_sum D = PjGrammar.held tr /\
            (length D <= length tr)%nat /\
            pobj tfibsegs B ly' S' W' mem' v /\
            rd_text tfibsegs B ly' S' W' mem' text len tcap /\
            (exists peak', peak <= peak' /\
               fs_glob tfibsegs W' mem' (live + PjGrammar.held tr) peak' (cnt + Z.of_nat (length tr)) fail)) W' c').
Proof.
intros ly S U W regs mem md ch q ot v text len p tb tcap ms pr ws rest live peak cnt fail S2 pos ms' mdx' tr wt
  Hk HPRE FH Hfr0 HIN0 HWIN Hrest Hvals Hstrs Hwf Hdep HPo0 Hvst Hvtx Hquiet Hsz Hlive Hnev Hbb
  Hin0 Hfrs2 Hab2 Hnev2 Hbb2 Hshape R8 R9 R18 R19 R20 R23 R24 R26 R3 R4 Vq0 HINV HJ HARU
  R2 HWK HIN HTX HPo HZo HGL HCH0 HCHq.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HPREU & HRO). pose proof HPREU as (HAPRE & OK0 & PO0).
pose proof HAPRE as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & _).
assert (HARU0 : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR0 | split; [exact OK0 | exact PO0]]).
pose proof (fsw_sp B _ ly S U W regs mem md ch HPREU) as (Hal16 & Hceil & H47 & HSTK0).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
pose proof Hstk as (_ & _ & Hlo0 & Hslo & Hshi & H47' & _ & _ & Htop2).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN0) as (_ & _ & _ & (Htp1 & Htp2) & _).
assert (Hk1 : (k <= 1)%nat) by (cbn [PjTree.depth] in Hdep; lia).
assert (FSd : STK_parse_items (1 - k) + 255 <= STK_parse_value (2 - k)).
{ assert (Hk01 : (k = 0 \/ k = 1)%nat) by lia. destruct Hk01 as [E | E]; rewrite E; vm_compute; discriminate. }
pose proof (pv_stk k Hk) as FS4.
pose proof (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR0 HPo0) as (Hv4096 & Hvc).
(* v's place at the entry (pobj's two arms): a frame of frames S or a live block *)
assert (LOC : (exists cid pos', In (cid, pos') (frames S) /\ 0 <= cid /\ frame_addr ly cid pos' mod 8 = 0 /\
                 frame_addr ly cid pos' <= v /\ v + 56 <= frame_addr ly cid pos' + fs_frame_bytes cid) \/
              (exists b m, In (b, m) (ablocks B ly S) /\ b + HEAD <= v /\ v + 56 <= b + req_size m)).
{ destruct HPo0 as [[(Hf & _) | (Hb & _)] _]; [left; exact Hf | right; exact Hb]. }
assert (Hv8 : v mod 8 = 0) by (destruct HPo0 as [[(_ & H & _) | (_ & H & _)] _]; exact H).
(* ---- 0x831a0 -> the callee's entry A_parse_items (pvc_obj0) ---- *)
rewrite Hshape.
apply (pvc_obj0 B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S S2 U W mem md
  (ms_regs ms') (ms_mem ms') mdx' pos q v _ R19 R20 HJ HARU).
intros msC mdC HshC C10 C11 C12 C1c HPC HJC HARUC KEEPC.
assert (EQM : mrestrict (w_H W) (ms_mem msC) = mrestrict (w_H W) (ms_mem ms'))
  by (apply functional_extensionality; exact KEEPC).
destruct (pvo_aview_ext (w_H W) U (ms_mem ms') (ms_mem msC) KEEPC) as (EAU & EAV).
assert (P2 : YK11.getr (ms_regs msC) 2%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)))
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 2%bv HPC ltac:(pv_cs)); exact R2).
assert (P3 : YK11.getr (ms_regs msC) 3%bv = YK11.getr regs 3%bv)
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 3%bv HPC ltac:(pv_cs)); exact R3).
assert (P4 : YK11.getr (ms_regs msC) 4%bv = YK11.getr regs 4%bv)
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 4%bv HPC ltac:(pv_cs)); exact R4).
assert (P8 : YK11.getr (ms_regs msC) 8%bv = Z_to_bv 64 (spZ regs))
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 8%bv HPC ltac:(pv_cs)); exact R8).
assert (P18 : YK11.getr (ms_regs msC) 18%bv = Z_to_bv 64 (frame_addr ly 0 pos))
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 18%bv HPC ltac:(pv_cs)); exact R18).
assert (P24 : YK11.getr (ms_regs msC) 24%bv = Z_to_bv 64 (SHADOW_OFF + frame_addr ly 0 pos / 8))
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 24%bv HPC ltac:(pv_cs)); exact R24).
assert (P26 : YK11.getr (ms_regs msC) 26%bv = Z_to_bv 64 (frame_addr ly 0 pos))
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 26%bv HPC ltac:(pv_cs)); exact R26).
assert (Hs64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; exact (u64_range _)).
assert (Csp : spZ (ms_regs msC) = 32 * ((spZ regs - 160) / 32)).
{ unfold spZ at 1. rewrite P2. apply unsigned_lit_small. lia. }
(* ---- the parse_items call (pvc_objcall') ---- *)
rewrite HshC.
change (mkCfg (mkst (ms_regs msC) (Z_to_bv 64 A_parse_items) (ms_mem msC) (seg_rom tfibsegs)) mdC)
  with (YG0d.cfg_at tfibsegs A_parse_items (ms_regs msC) (ms_mem msC) mdC).
assert (HROC : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (ms_mem msC))).
{ pose proof HARUC as (_ & OKC & POC).
  apply (arodata_kept_own B _ _ _ ly S U W mem md [(0, pos)] ly S2 U W (ms_mem msC) mdC 0 HJC HARU0 OKC POC).
  - apply sink_closed_pos. unfold FS_PSTAT_FP. cbn [app]. repeat constructor; cbn [fst]; lia.
  - intros a Hro (r & Hr & Ha). apply in_app_or in Hr as [Hr | Hr].
    + destruct Hr as [<- | []]. cbn [fst snd] in Ha.
      refine (proj2 (al_client_img _ _ LAWS ly S W (unpoison U mem) md a HAR0 _) (fsw_roP_img a Hro)).
      destruct LOC as [(cid & pos' & Hc & _ & _ & H1 & H2) | (b & m & Hb & H1 & H2)].
      * right; left. exists cid, pos'. split; [exact Hc | lia].
      * left. exists b, m. split; [exact Hb | unfold HEAD in H1; lia].
    + exact (pvo_pstat_not_ro a Hro (ex_intro _ r (conj Hr Ha))).
  - exact HRO. }
assert (FH2 : FSupoisonU.fs_heads B ly S2 U).
{ intros r Hr. destruct (FH r Hr) as (H1 & m & H2 & H3). split; [exact H1|]. exists m. rewrite Hab2. auto. }
assert (HWINC : rd_win tfibsegs (ms_regs msC) ly W (ms_mem msC) q ot).
{ split; [rewrite Csp; lia|]. split; [exact Hq24|]. split; [exact Hot16|]. split; [exact Hotly|].
  intros a Ha. rewrite Csp in Ha.
  pose proof HJC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresC & _).
  apply (fsw_apresent_unpoison B ly S2 U W (ms_mem msC) mdC a HARUC); [unfold kHighMemBeg; lia|].
  apply HpresC. lia. }
assert (HPoC : pobj tfibsegs B ly S2 W (ms_mem msC) v).
{ unfold pobj, fs_afobj in HPo |- *. rewrite EAV, EQM. exact HPo. }
assert (HTXC : rd_text tfibsegs B ly S2 W (ms_mem msC) text len tcap).
{ unfold rd_text, fs_rblock in HTX |- *. rewrite EQM. exact HTX. }
assert (HGLC : fs_glob tfibsegs W (ms_mem msC) live peak cnt fail).
{ unfold fs_glob, fs_glob_at in HGL |- *. rewrite EQM. exact HGL. }
assert (VFLC : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msC)) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos)).
{ rewrite EQM. destruct HINV as (_ & VFL0 & _). exact VFL0. }
(* v's bytes and the statics are off the frame (0, pos) at S2 *)
assert (NFP : forall x, frame_addr ly 0 pos + 56 <= x < frame_addr ly 0 pos + 64 ->
  ~ inFP ([(v, v + 56)] ++ FS_PSTAT_FP) x).
{ intros x Hx (r & Hr & Ha).
  pose proof (ARU_AR tfibsegs B ly S2 U W (ms_mem msC) mdC HARUC) as HAR2.
  apply in_app_or in Hr as [Hr | Hr].
  - destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (pvo_off_pe B ly S2 W (unpoison U (ms_mem msC)) mdC pos (frames S) x HAR2 Hfrs2); [|unfold pe_wr; left; lia].
    right; right. destruct LOC as [(cid & pos' & Hc & _ & _ & H1 & H2) | (b & m & Hb & H1 & H2)].
    + right. exists cid, pos'. split; [exact Hc | lia].
    + left. exists b, m. split; [rewrite Hab2; exact Hb | unfold HEAD in H1; lia].
  - apply (pvo_off_pe B ly S2 W (unpoison U (ms_mem msC)) mdC pos (frames S) x HAR2 Hfrs2);
      [right; left; exact (pvc_pstat_img x (ex_intro _ r (conj Hr Ha))) | unfold pe_wr; left; lia]. }
apply (pvc_objcall' (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S S2 U W mem md
  (ms_regs msC) (ms_mem msC) mdC pos q (spZ regs) (32 * ((spZ regs - 160) / 32)) v text len (p + Z.of_nat (length ws))
  tb tcap ms pr rest live peak cnt fail (flag_addr ly 0 pos) _ Hk1 Csp C10 C11 C12 C1c).
1: { rewrite P3. exact Hgp. }
1: { rewrite P4. exact Htp. }
1: { exact P8. }
1: { exact Hs64. }
1: { lia. }
1: { lia. }
1: { lia. }
1: { lia. }
1: { rewrite EAU. exact HCH0. }
1: { rewrite EAU. exact HCHq. }
1: { exact HROC. }
1: { exact FH2. }
1: { exact Hfr0. }
1: { rewrite EQM. exact HIN. }
1: { exact HWINC. }
1: { exact HTXC. }
1: { exact (pvo_rest_at tb text p ws wt rest Htp1 Hrest). }
1: { exact Hvals. }
1: { exact Hstrs. }
1: { exact Hwf. }
1: { exact Hdep. }
1: { exact HPoC. }
1: { rewrite EQM. exact HZo. }
1: { destruct Hvst as [Hvst | Hvst]; [left; lia | right; exact Hvst]. }
1: { exact Hvtx. }
1: { exact HGLC. }
1: { exact Hquiet. }
1: { exact Hsz. }
1: { exact Hlive. }
1: { rewrite Hnev2. exact Hnev. }
1: { rewrite Hbb2. exact Hbb. }
1: { exact HJC. }
1: { exact HARUC. }
1: { intros a Ha. exact Ha. }
1: { exact VFLC. }
1: { exact NFP. }
intros ly2 S3 W2 regs2 mem2 md2 D Da HDa HJ2 HARU2 HP2 REGS2 Q10 QIN QWK QPERM QT QSUM QLEN QPO QTX QGL VFL2.
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & Hfrs3 & _). cbn [app] in Hfrs3.
destruct (al_layout tfibsegs B LAWS ly S W (unpoison U mem) md ly2 HAR0 Hly2) as (_ & HFA & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
assert (EFL : flag_addr ly2 0 pos = flag_addr ly 0 pos) by (unfold flag_addr; rewrite EF; reflexivity).
assert (Hin3 : In (0, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (Hab3 : forall b m, In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly2 S3)).
{ intros b m Hb. apply (Permutation_in _ (Permutation_sym QPERM)). apply in_or_app. left. rewrite Hab2. exact Hb. }
(* ---- 0x832f8 -> the epilogue 0x83318 (pv_obj1) ---- *)
change (YG0d.cfg_at tfibsegs 0x832f8 regs2 mem2 md2)
  with (mkCfg (mkst regs2 (Z_to_bv 64 0x832f8) mem2 (seg_rom tfibsegs)) md2).
apply (pv_obj1 B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S U W mem md
  (rd_ev tr) ly2 S3 (U ++ rd_heads Da) W2 regs2 mem2 md2 pos 0 _ Q10 ltac:(lia) HJ2 HARU2).
intros ms3 md3 Hsh3 G21 G3 G4 G8 G9 G18 G19 G20 G23 G24 G26 HJ3 HARU3 KEEP3.
rewrite Hsh3.
assert (EQ3 : mrestrict (w_H W2) (ms_mem ms3) = mrestrict (w_H W2) mem2)
  by (apply functional_extensionality; exact KEEP3).
assert (E8 : YK11.getr (ms_regs ms3) 8%bv = Z_to_bv 64 (spZ regs))
  by (rewrite G8, (fsw_pres (ms_regs msC) regs2 8%bv HP2 ltac:(pv_cs)); exact P8).
assert (E18 : YK11.getr (ms_regs ms3) 18%bv = Z_to_bv 64 (frame_addr ly2 0 pos))
  by (rewrite HFA, G18, (fsw_pres (ms_regs msC) regs2 18%bv HP2 ltac:(pv_cs)); exact P18).
assert (E24 : YK11.getr (ms_regs ms3) 24%bv = Z_to_bv 64 (SHADOW_OFF + frame_addr ly2 0 pos / 8))
  by (rewrite HFA, G24, (fsw_pres (ms_regs msC) regs2 24%bv HP2 ltac:(pv_cs)); exact P24).
assert (E26 : YK11.getr (ms_regs ms3) 26%bv = Z_to_bv 64 (frame_addr ly2 0 pos))
  by (rewrite HFA, G26, (fsw_pres (ms_regs msC) regs2 26%bv HP2 ltac:(pv_cs)); exact P26).
assert (E3 : YK11.getr (ms_regs ms3) 3%bv = YK11.getr regs 3%bv)
  by (rewrite G3, (fsw_pres (ms_regs msC) regs2 3%bv HP2 ltac:(pv_cs)); exact P3).
assert (E4 : YK11.getr (ms_regs ms3) 4%bv = YK11.getr regs 4%bv)
  by (rewrite G4, (fsw_pres (ms_regs msC) regs2 4%bv HP2 ltac:(pv_cs)); exact P4).
(* the thirteen saved words: at the arm (pv_inv), across parse_items (its wkeep over [sp1, ot) off [q, q + 24)) *)
assert (Vsv : pv_saved_ok (mrestrict (w_H W2) (ms_mem ms3)) (spZ regs) regs).
{ rewrite EQ3. destruct HINV as (Vsv0 & _). intros j Hj kk Hkk.
  rewrite (proj1 (QWK (spZ regs - 8 * (Z.of_nat j + 1) + Z.of_nat kk) ltac:(lia) ltac:(lia))).
  rewrite EQM. exact (Vsv0 j Hj kk Hkk). }
assert (Vfl : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms3)) (frame_addr ly2 0 pos + 56) 8 (flag_addr ly2 0 pos)).
{ rewrite EQ3, HFA, EFL. exact VFL2. }
(* ---- 0x83318 -> ret (pv_epi), into parse_value_spec k's post ---- *)
eapply SRr_mono; cycle 1.
{ intros W' c' _ HX. exists D, Da. split; [exact HDa | exact HX]. }
apply (pv_epi B ML ASF FFL (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S U W mem md
  (rd_ev tr) ly2 S3 (U ++ rd_heads Da) W2 regs (ms_regs ms3) (ms_mem ms3) md3 pos (spZ regs) 0 []
  _ Hin3 E8 E18 E24 E26 G21 E3 E4 eq_refl Hret).
1: { lia. }
1: { exact Hal16. }
1: { rewrite Elo. lia. }
1: { rewrite Ehi. lia. }
1: { rewrite Ehi. exact H47'. }
1: { rewrite Elo. exact Hlo0. }
1: { lia. }
1: { exact Vsv. }
1: { exact Vfl. }
1: { exact HJ3. }
1: { exact HARU3. }
intros mat regsf memf Hf10 KEEPf. cbv beta.
rewrite HFA, EFL in KEEPf.
assert (KEEPF : forall x : word, ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) (bv_unsigned x) ->
  mrestrict (w_H W2) memf x = mrestrict (w_H W2) mem2 x) by (intros x Hx; rewrite (KEEPf x Hx), EQ3; reflexivity).
assert (KZ : forall z, 0 <= z < 2 ^ 64 -> ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) z ->
  mrestrict (w_H W2) memf (Z_to_bv 64 z) = mrestrict (w_H W2) mem2 (Z_to_bv 64 z)).
{ intros z Hz Hn. apply KEEPF. rewrite unsigned_lit_small by lia. exact Hn. }
assert (OFF : forall z, (alloc_ceiling <= z \/ in_img tfibsegs z \/
    (exists b n, In (b, n) (ablocks B ly2 S3) /\ b <= z < b + req_size n) \/
    (exists cid pos', In (cid, pos') (frames S) /\
       frame_addr ly cid pos' <= z < frame_addr ly cid pos' + fs_frame_bytes cid)) ->
  ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) z).
{ intros z Hz. rewrite <- (HFA 0 pos), <- EFL.
  apply (pvo_off_pe B ly2 S3 W2 (unpoison (U ++ rd_heads Da) mem2) md2 pos (frames S) z HAR2 Hfrs3).
  destruct Hz as [Hz | [Hz | [Hz | (cid & pos' & Hc & Hz)]]];
    [left; exact Hz | right; left; exact Hz | right; right; left; exact Hz |].
  right; right; right. exists cid, pos'. rewrite (HFA cid pos'). split; [exact Hc | exact Hz]. }
assert (VOFF : forall z, v <= z < v + 56 -> ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) z).
{ intros z Hz. apply OFF. right; right.
  destruct LOC as [(cid & pos' & Hc & _ & _ & H1 & H2) | (b & m & Hb & H1 & H2)].
  - right. exists cid, pos'. split; [exact Hc | lia].
  - left. exists b, m. split; [exact (Hab3 b m Hb) | unfold HEAD in H1; lia]. }
assert (BOFF : forall b n z, In (b, n) (ablocks B ly2 S3) -> b <= z < b + req_size n ->
  mrestrict (w_H W2) memf (Z_to_bv 64 z) = mrestrict (w_H W2) mem2 (Z_to_bv 64 z)).
{ intros b n z Hb Hz.
  destruct (fsw_ablock_low B ly2 S3 W2 _ md2 b n HAR2 Hb) as (L1 & L2 & _).
  apply KZ; [lia|]. apply OFF. right; right; left. exists b, n. split; [exact Hb | exact Hz]. }
split; [exact Hf10|].
split.
{ (* struct pj_in and the text: stack bytes and the text block's bytes *)
  apply (pvo_in_tr (mrestrict (w_H W2) mem2)); [|exact QIN].
  pose proof QTX as (_ & (HinT & _ & Htc & _) & Hlt).
  pose proof (req_size_pos (tcap + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
  intros a [Ha | Ha].
  - apply KZ; [lia|]. apply OFF. left. lia.
  - apply (BOFF (text - HEAD) (tcap + HEAD) a HinT). unfold HEAD in *. lia. }
split.
{ (* the window [s, ot) off [q, q + 24): the entry keep, the callee's wkeep, the epilogue writes below the stack *)
  intros a Ha Hq. pose proof (QWK a ltac:(lia) Hq) as (QW1 & QW2). pose proof (HWK a Ha Hq) as (HW1 & HW2).
  assert (E1 : mrestrict (w_H W2) memf (Z_to_bv 64 a) = mrestrict (w_H W2) mem2 (Z_to_bv 64 a))
    by (apply KZ; [lia | apply OFF; left; lia]).
  split.
  - transitivity (mbyte tfibsegs (mrestrict (w_H W2) mem2) a); [unfold mbyte; rewrite E1; reflexivity|].
    rewrite QW1, EQM. exact HW1.
  - split; intros Hw.
    + apply (writable_at_eq tfibsegs (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) memf) a E1).
      apply QW2. rewrite EQM. apply HW2. exact Hw.
    + apply HW2. rewrite <- EQM. apply QW2.
      exact (writable_at_eq tfibsegs (mrestrict (w_H W2) memf) (mrestrict (w_H W2) mem2) a (eq_sym E1) Hw). }
split.
{ change (ablocks B ly2 (stack_free_state 0 pos S3)) with (ablocks B ly2 S3). rewrite <- Hab2. exact QPERM. }
split.
{ apply (pvo_rtree_tr B ly2 S3 (stack_free_state 0 pos S3) W2 (unpoison (U ++ rd_heads Da) mem2) md2 mem2 memf v
    (PjTree.JObj ms) D HAR2 eq_refl); [|exact QT].
  intros z Hz [Hv | (a & kk & Hak & Ha)]; [apply KZ; [exact Hz | exact (VOFF z Hv)]|].
  pose proof QT as (_ & QB & QI). destruct (QB a kk Hak) as (Hin & _ & Hk0 & _).
  pose proof (req_size_pos (kk + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
  apply (BOFF (a - HEAD) (kk + HEAD) z Hin). unfold HEAD in *. lia. }
split; [exact QSUM|].
split; [exact QLEN|].
split.
{ (* pobj: the place from the entry, the shadow and the writability from the callee's post, kept by the epilogue *)
  assert (Hfr' : frames (stack_free_state 0 pos S3) = frames S) by exact (pvo_frames_free S3 S pos Hfrs3).
  destruct QPO as [QPl QPw]. split.
  - assert (RA : range_addressable (aview tfibsegs (w_H W2) memf) SHADOW_OFF v 56).
    { assert (RA2 : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF v 56)
        by (destruct QPl as [(_ & _ & Hr) | (_ & _ & Hr)]; exact Hr).
      intros x Hx. destruct (RA2 x Hx) as (sv & Esv & Hok). exists sv. split; [|exact Hok].
      rewrite <- Esv. apply pvo_aview_pt. apply KZ.
      - unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia.
      - rewrite <- (HFA 0 pos), <- EFL.
        apply (pvo_shadow_off B ly2 S3 W2 (unpoison (U ++ rd_heads Da) mem2) md2 pos x HAR2 Hin3); [lia|].
        rewrite (HFA 0 pos). intros Hx'. apply (VOFF x Hx). unfold pe_wr. left. exact Hx'. }
    destruct LOC as [(cid & pos' & Hc & Hc0 & H8 & H1 & H2) | (b & m & Hb & H1 & H2)]; [left | right].
    + split; [|split; [exact Hv8 | exact RA]]. exists cid, pos'. rewrite (HFA cid pos'), Hfr'.
      split; [exact Hc|]. split; [exact Hc0|]. split; [exact H8|]. lia.
    + split; [|split; [exact Hv8 | exact RA]]. exists b, m. split; [exact (Hab3 b m Hb) | lia].
  - intros i Hi. apply (writable_at_eq tfibsegs (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) memf) (v + i));
      [|exact (QPw i Hi)].
    apply KZ; [lia | apply VOFF; lia]. }
split.
{ (* the text: the block's head word *)
  destruct QTX as (Ht & QRB & Hlt). split; [exact Ht|]. split; [|exact Hlt].
  apply (pvo_rblock_tr B ly2 S3 (stack_free_state 0 pos S3) W2 (unpoison (U ++ rd_heads Da) mem2) md2 mem2 memf
    text tcap HAR2 eq_refl); [|exact QRB].
  pose proof QRB as (HinT & _ & Htc & _).
  pose proof (req_size_pos (tcap + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
  intros z Hz. apply (BOFF (text - HEAD) (tcap + HEAD) z HinT). unfold HEAD in *. lia. }
{ (* fuzz/alloc.c's statics: image bytes *)
  destruct QGL as (peak' & Hpk & QG). exists peak'. split; [exact Hpk|].
  assert (GK : forall g, 659456 <= g -> g + 8 <= 6279168 -> forall j, (j < 8)%nat ->
    mrestrict (w_H W2) memf (Z_to_bv 64 (g + Z.of_nat j)) = mrestrict (w_H W2) mem2 (Z_to_bv 64 (g + Z.of_nat j))).
  { intros g H1 H2 j Hj. apply KZ; [lia|]. apply OFF. right; left. apply pvc_img. lia. }
  unfold fs_glob, fs_glob_at in QG |- *. destruct QG as (V1 & V2 & V3 & V4 & Rest).
  split; [exact (pvo_val_tr _ _ _ _ _ (GK G_LIVE ltac:(unfold G_LIVE; lia) ltac:(unfold G_LIVE; lia)) V1)|].
  split; [exact (pvo_val_tr _ _ _ _ _ (GK G_PEAK ltac:(unfold G_PEAK; lia) ltac:(unfold G_PEAK; lia)) V2)|].
  split; [exact (pvo_val_tr _ _ _ _ _ (GK G_COUNT ltac:(unfold G_COUNT; lia) ltac:(unfold G_COUNT; lia)) V3)|].
  split; [exact (pvo_val_tr _ _ _ _ _ (GK G_FAIL ltac:(unfold G_FAIL; lia) ltac:(unfold G_FAIL; lia)) V4)|].
  exact Rest. }
Qed.
End OA.
