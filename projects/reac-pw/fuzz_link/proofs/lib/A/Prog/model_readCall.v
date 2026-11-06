(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 216 of its 255 lines of code are new or changed and 1266 lines of the source are left out. *)
(* model_read on image A: what a callee of its walk (index_of, talk) is given at its call, from what the walk kept
   since the entry (an akept clause with the side frame and a few written bytes excepted): g_nl's bytes, the
   read-only image, a read-set byte's 8-byte granule. The heap-block and image facts are those of
   lib/A/Prog/model_writeCut.v, names prefixed mr_.
   Proves no function (kind: segment lemma of model_read's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkCall LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c index_of_c talk_c model_readDefs LinkWalkWseg LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AE7f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YN2j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB13.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.reac_pw.fuzz_link.images Require Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section tv. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

Lemma mr_chunk_tail_in_ajunk : forall ly S k, In k (st_chunks S) ->
  In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S).
Proof.
  intros ly S k Hk. unfold ajunk. right. right.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_flat_map. exists k. split; [exact Hk|].
  unfold chunk_junk. cbv zeta.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
Qed.

Lemma mr_chunk_room_mod16 : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) ->
  (ck_extent k - ck_rz k) mod 16 = 0.
Proof.
  intros ly S rd k M Hk.
  pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & RZ & _ & _ & G).
  assert (EX : ck_extent k mod 16 = 0).
  { destruct (ck_beg k) as [|off|r o|c q]; try solve [destruct G].
    - cbv zeta in G. destruct G as (Gc & _ & _ & Gext & _).
      pose proof (class_ok (prim_class off) ltac:(lia)) as (_ & K2 & _). rewrite Gext.
      apply Z.mod_divide in K2 as [q K2]; [|lia]. rewrite K2. replace (q * 32) with ((q * 2) * 16) by lia.
      apply Z.mod_mul. lia.
    - destruct G as (_ & Hp & _ & Gext & _). pose proof (secondary_geometry (ck_req k)) as SG.
      pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & _ & Hn & _).
      destruct (SG ltac:(lia) Hp) as (_ & _ & _ & _ & S5 & _). rewrite Gext.
      apply Z.mod_divide in S5 as [q S5]; [|unfold kPage; lia]. rewrite S5. unfold kPage.
      replace (q * 4096 - 4096) with ((q * 256 - 256) * 16) by lia. apply Z.mod_mul. lia. }
  apply Z.mod_divide in EX as [a EX]; [|lia]. apply Z.mod_divide in RZ as [b RZ]; [|lia].
  rewrite EX, RZ. replace (a * 16 - b * 16) with ((a - b) * 16) by lia. apply Z.mod_mul. lia.
Qed.

(* srm_blk_tail_vis16 at the block's byte size `req_size n` (which a zero request makes 1) *)
Lemma mr_blk_tail_vis : forall ly S (W : world segs) mem md p n a,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p + req_size n <= a < p + round_up (req_size n) 16 -> aview segs (w_H W) mem a <> None.
Proof.
  intros ly S W mem md p n a (M & _) Hb Ha.
  unfold ablocks, blocks in Hb. apply in_map_iff in Hb as ([u r] & Eb & Hb). cbn [fst snd] in Eb.
  injection Eb as Ep En.
  apply in_map_iff in Hb as (k & Ek & Hk). injection Ek as Eu Er. subst u r.
  apply filter_In in Hk as [Hk _].
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & UA & _ & _ & Hn & HX & _).
  pose proof (mr_chunk_room_mod16 ly S _ k M Hk) as R16.
  assert (CN : ck_n k = req_size n)
    by (unfold ck_n, req_size; destruct (Z.eqb_spec (ck_req k) 0); destruct (Z.eqb_spec n 0); lia).
  assert (N1 : 1 <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  assert (RU : round_up (req_size n) 16 <= ck_extent k - ck_rz k).
  { apply round_up_le; [lia | | exact R16]. rewrite <- CN. unfold ck_n in *. lia. }
  pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ M) _ (mr_chunk_tail_in_ajunk ly S k Hk)) as V.
  unfold range_vis in V. cbn [fst snd] in V. rewrite CN in V.
  rewrite aeval_aoff in V by (intros e'; destruct (ck_beg k); cbn; discriminate).
  change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
  replace a with (ck_base B ly k + (ck_rz k + req_size n) + (a - (ck_base B ly k + (ck_rz k + req_size n)))) by lia.
  apply V. rewrite <- Ep, UA in Ha. lia.
Qed.
End tv.

(* g_nl lies inside one loaded segment of image A, and meets no runtime static (see
   reac_link_alias_writeHead.v aw_gnl_in_image_b / aw_gnl_static_b) *)
Lemma mr_gnl_in_image_b :
  existsb (relro_in_seg LA_G_NL (LA_G_NL + NK_SIZE)) Asan.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mr_gnl_static_b :
  forallb (fun r => (fst r + snd r <=? LA_G_NL) || (LA_G_NL + NK_SIZE <=? fst r)) AF0m.Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

(* the image's end is page aligned *)
Lemma mr_img_end_al : pcap_img_end mod 8 = 0.
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.

Lemma mr_aview_present : forall H (m : word -> option byte) a, apresent H m a -> aview pa_segs H m a <> None.
Proof.
  intros H m a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.

Lemma mr_rom_vis : forall H (m : word -> option byte) a, 0x10000 <= a < pcap_img_end -> aview pa_segs H m a <> None.
Proof.
  intros H m a Ha. rewrite HSEGS. pose proof (AB13.tfib_rom_all a Ha) as Hr.
  unfold aview, mbyte. destruct (mrestrict H m (Z_to_bv 64 a)) as [b|]; cbn [option_map]; [discriminate|].
  destruct (seg_rom tfibsegs (Z_to_bv 64 a)) eqn:E; cbn [option_map]; [discriminate|].
  exfalso. exact (Hr eq_refl).
Qed.

(* g_nl's bytes are image bytes outside the runtime's statics and errno *)
Lemma mr_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
  in_img pa_segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. split; [|split].
  - rewrite HSEGS. destruct (proj1 (existsb_exists _ _) mr_gnl_in_image_b) as (s & Hin & H).
    unfold relro_in_seg in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H3.
    exists s. split; [exact Hin | lia].
  - rewrite (AF0m.ts_owned B TB). intros HE. apply Exists_exists in HE as (r & Hr & Hz).
    pose proof (proj1 (forallb_forall _ _) mr_gnl_static_b r Hr) as Hb. cbv beta in Hb.
    apply orb_true_iff in Hb. unfold in_zr in Hz.
    destruct Hb as [Hb | Hb]; apply Z.leb_le in Hb; unfold LA_G_NL, NK_SIZE in *; lia.
  - rewrite (AF0m.ts_errno B TB). unfold AF0m.TFIB_ERRNO, LA_G_NL, NK_SIZE in *. lia.
Qed.



(* the bytes of a side frame the walk took: not image bytes, and below the allocator's ceiling *)
Lemma mr_aside_facts : forall lyc S1 (W1 : world pa_segs) m1 md1 pos,
  AR pa_segs B lyc S1 W1 m1 md1 -> In (1, pos) (frames S1) ->
  forall a, aside_rng lyc 1 pos a -> ~ in_img pa_segs a /\ a < alloc_ceiling.
Proof.
  intros lyc S1 W1 m1 md1 pos HAR Hin a Ha.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (frames_bounds pa_segs B LAWS lyc S1 W1 m1 md1 1 pos HAR Hin) as (HF4 & HFc & HFapp).
  destruct (al_flag _ _ LAWS _ _ _ _ _ 1 pos HAR Hin) as (_ & _ & _ & HFLc).
  pose proof (proj1 alloc_ceiling_val) as HCE.
  change (fs_frame_bytes 1) with 128 in *.
  destruct Ha as [Hf | [Hs | Hl]].
  - unfold in_zr, frame_rng in Hf. cbn [fst snd] in Hf. change (fs_frame_bytes 1) with 128 in Hf.
    assert (Hr : frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + fs_frame_bytes 1)
      by (change (fs_frame_bytes 1) with 128; lia).
    split; [|lia].
    exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR
      (or_intror (or_introl (ex_intro _ 1 (ex_intro _ pos (conj Hin Hr))))))).
  - unfold in_zr, shadow_addr in Hs. cbn [fst snd] in Hs. change (fs_frame_bytes 1 / 8) with 16 in Hs.
    assert (HF8 : frame_addr lyc 1 pos / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
    split.
    + intros Hi. pose proof (pa_img_range a Hi) as Hr. rewrite img_end_val in Hr.
      pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)).
      unfold SHADOW_OFF in Hs. lia.
    + unfold SHADOW_OFF in Hs. lia.
  - subst a. split; [|exact HFLc].
    exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ _ HAR
      (or_intror (or_intror (ex_intro _ 1 (ex_intro _ pos (conj Hin eq_refl))))))).
Qed.

(* g_nl at a later memory the kept clause reaches *)
Lemma mr_gnl_view_k : forall lyc Sc (W : world pa_segs) memc (W2 : world pa_segs) m2 slo shi (Ex : Z -> Prop) a,
  akept pa_segs B lyc Sc W memc W2 m2 slo shi Ex ->
  LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ Ex a ->
  aview pa_segs (w_H W2) m2 a = aview pa_segs (w_H W) memc a.
Proof.
  intros lyc Sc W memc W2 m2 slo shi Ex a (_ & _ & K3 & _) Ha HE.
  destruct (mr_gnl_img a Ha) as (Hi & Hno & Herr). exact (K3 a Hi Hno Herr HE).
Qed.

(* the read-only image at a later memory: the empty relro window *)
Lemma mr_arodata_k : forall rlo rhi lyc Sc (W : world pa_segs) memc (W2 : world pa_segs) m2 slo shi
    (Ex Wr : Z -> Prop) S1 (W1 : world pa_segs) m1 md1 pos,
  arodata_okP pa_segs rlo rhi B (aview pa_segs (w_H W) memc) ->
  akept pa_segs B lyc Sc W memc W2 m2 slo shi Ex ->
  AR pa_segs B lyc S1 W1 m1 md1 -> In (1, pos) (frames S1) ->
  (forall a, Ex a -> aside_rng lyc 1 pos a \/ Wr a) ->
  (forall a, Wr a -> ~ in_roP pa_segs rlo rhi a) ->
  arodata_okP pa_segs 0 0 B (aview pa_segs (w_H W2) m2).
Proof.
  intros rlo rhi lyc Sc W memc W2 m2 slo shi Ex Wr S1 W1 m1 md1 pos HROD HK HAR1 Hin1 HEx HWr a Hro Hno Herr.
  destruct Hro as [(s & Hs & Hw & Hr) | Hr]; [|lia].
  assert (Hi : in_img pa_segs a) by (exists s; split; [exact Hs | exact Hr]).
  destruct HK as (_ & _ & K3 & _).
  rewrite (K3 a Hi Hno Herr).
  - apply HROD; [left; exists s; split; [exact Hs | split; [exact Hw | exact Hr]] | exact Hno | exact Herr].
  - intros HE. destruct (HEx a HE) as [Hs' | HW].
    + exact (proj1 (mr_aside_facts lyc S1 W1 m1 md1 pos HAR1 Hin1 a Hs') Hi).
    + apply (HWr a HW). left. exists s. split; [exact Hs | split; [exact Hw | exact Hr]].
Qed.

(* a byte after a read-set byte, in its 8-byte granule, visible at the call, is visible at a later memory the kept
   clause reaches (model_writeCut.v mw_tail_at, over an akept clause) *)
Lemma mr_tail_vis_k : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world pa_segs) memc mdc k
    ly2 S2 (W2 : world pa_segs) m2 md2 slo shi (Ex X : Z -> Prop) S1 (W1 : world pa_segs) m1 md1 pos x a,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  AR pa_segs B ly2 S2 W2 m2 md2 ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
  akept pa_segs B lyc Sc W memc W2 m2 slo shi Ex ->
  AR pa_segs B lyc S1 W1 m1 md1 -> frames S1 = (1, pos) :: frames Sc -> ~ In (1, pos) (frames Sc) ->
  (forall y, Ex y -> aside_rng lyc 1 pos y \/ X y) ->
  (forall y, X y -> aview pa_segs (w_H W2) m2 y = Some 0) ->
  slo mod 8 = 0 -> shi mod 8 = 0 ->
  akb pa_segs B lyc Sc slo shi x -> 0 <= x -> x < a < x - x mod 8 + 8 ->
  aview pa_segs (w_H W) memc a <> None -> aview pa_segs (w_H W2) m2 a <> None.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 W2 m2 md2 slo shi Ex X S1 W1 m1 md1
    pos x a HJ HAR2 Hbl HK HAR1 Hfrs1 Hnin HEx HX0 Hslo Hshi HAKB Hx0 Ha Hv.
  destruct (classic (X a)) as [HXa | HnX]; [rewrite (HX0 a HXa); discriminate|].
  assert (Hin1 : In (1, pos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
  pose proof HAR1 as [M1 _].
  destruct (frame_facts B lyc S1 _ 1 pos M1 Hin1) as (Hc1 & Hp1 & _).
  assert (HnE : forall y, ~ aside_rng lyc 1 pos y -> ~ X y -> ~ Ex y)
    by (intros y Hns Hnx HE; destruct (HEx y HE) as [Hq | Hq]; [exact (Hns Hq) | exact (Hnx Hq)]).
  assert (NSs : forall y, sclass pa_segs B lyc Sc y -> ~ aside_rng lyc 1 pos y).
  { intros y Hy. eapply sclass_not_side; first [exact LAWS | exact TB | exact pa_img_range | exact HJ | lia
                                                | exact Hnin | exact Hy]. }
  pose proof (pa_wx) as _.
  destruct (ajournal_gx_row SK pa_segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Hlo & Hhi & _).
  pose proof (ajournal_gx_AR pa_segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hxm.
  destruct HK as (K1 & K2 & K3 & K4 & _).
  destruct HAKB as [(H1 & H2) | [(b & m & Hin & Hr) | [(H1 & H2 & H3) | (c & q & Hin & Hr)]]].
  - (* the stack row: akept's clause 1 *)
    assert (Hna : ~ (slo <= a < shi)).
    { intros Hw. apply H2. pose proof (Z.mod_pos_bound slo 8 ltac:(lia)). pose proof (Z.mod_pos_bound shi 8 ltac:(lia)).
      pose proof (Z_div_mod_eq_full slo 8). pose proof (Z_div_mod_eq_full shi 8). pose proof (Z_div_mod_eq_full x 8).
      lia. }
    rewrite (K1 a); [exact Hv | lia | exact Hna |].
    apply HnE; [|exact HnX]. intros Hs.
    pose proof (mr_aside_facts lyc S1 W1 m1 md1 pos HAR1 Hin1 a Hs) as (_ & Hc). lia.
  - (* a heap block of the call *)
    destruct (Z_lt_ge_dec a (b + req_size m)) as [Hlt | Hge].
    + replace a with (b + (a - b)) by lia.
      rewrite (K2 b m (a - b) Hin ltac:(lia)); [replace (b + (a - b)) with a by lia; exact Hv|].
      replace (b + (a - b)) with a by lia.
      apply HnE; [|exact HnX]. apply NSs. right; left. exists b, m. split; [exact Hin | lia].
    + destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin) as (Hb16 & _ & _ & _ & _ & _ & Hmn).
      apply (mr_blk_tail_vis pa_segs B ly2 S2 W2 m2 md2 b m a HAR2 (Hbl b m Hin)).
      split; [lia|]. unfold round_up.
      assert (Hrs : 1 <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
      pose proof (Z.div_mod (req_size m + 16 - 1) 16 ltac:(lia)) as Hd.
      pose proof (Z.mod_pos_bound (req_size m + 16 - 1) 16 ltac:(lia)) as Hdm.
      lia.
  - (* an image byte: the image file has every byte of the granule *)
    pose proof (pa_img_range x H1) as Hxi. pose proof mr_img_end_al as Hal.
    apply mr_rom_vis. lia.
  - (* a side frame of the caller *)
    pose proof (frame_al64 pa_segs B lyc Sc W memc mdc c q HARc Hin) as (Hfa64 & Hfb64 & _).
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
    assert (Hra : in_zr a (frame_rng lyc (c, q))) by (unfold in_zr, frame_rng; cbn [fst snd]; lia).
    rewrite (K4 c q a Hin (or_introl Hra)); [exact Hv|].
    apply HnE; [|exact HnX]. apply NSs. right; right; right. exists c, q. split; [exact Hin|].
    unfold in_zr, frame_rng in Hra. cbn [fst snd] in Hra. exact Hra.
Qed.

End b.
End a.
