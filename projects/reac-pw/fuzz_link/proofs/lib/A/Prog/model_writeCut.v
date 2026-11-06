(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 297 of its 339 lines of code are new or changed and 1038 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readDefs.v, with its module paths and module names changed; 328 of its 367 lines of code are new or changed and 300 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100) on image A: the entry Pre's facts restated at a cut of the walk (cut interface
   lib/A/Prog/model_writeDefs.v), for the cuts before talk (exception set NoX: only the side frame the call took):
   - mw_cut_facts / mw_side_facts: the AR states at the call and at the cut, the inclusions between them, and the
     side frame's bounds;
   - mw_view_akb: a read-set byte (akb at the call) has its value of the call (akept_akb_gx and akb_not_side);
   - mw_shadow_at: the shadow facts of a read-set range (LinkWalkShadow.v shadow_transport_akb);
   - mw_tail_at: a byte after a read-set byte in its 8-byte granule that is visible at the call is visible at the cut
     (stack row: akept's clause 1; heap block: akept's block clause or the chunk's junk (mw_blk_tail_vis, after
     srm_blk_tail_vis16 of lib/A/Prog/reac_served_markKitAt.v); image: the image file (AB13.v
     tfib_rom_all); side frame of the caller: akept's frame clause);
   - mw_arodata0: `arodata_okP SEGS 0 0 B` at the cut (the read-only segments; the own callees' contracts hold at
     every rlo rhi, so the walk calls them at the empty relro window), and the runtime's `rt_rom_view`;
   - mw_gnl_img / mw_gnl_view: g_nl's bytes are image bytes the cut keeps.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB13.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LinkWalk LinkWalkPi LinkWalkSide LinkWalkCall LinkWalkShadow PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c model_write_c model_writeDefs model_writeKit model_writeStep.
From OSSVerify.reac_pw.fuzz_link.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the bytes past a heap block, to the next multiple of 16 of its size, are visible at every AR state ---- *)
Section tv. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

Lemma mw_chunk_tail_in_ajunk : forall ly S k, In k (st_chunks S) ->
  In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S).
Proof.
  intros ly S k Hk. unfold ajunk. right. right.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_flat_map. exists k. split; [exact Hk|].
  unfold chunk_junk. cbv zeta.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
Qed.

Lemma mw_chunk_room_mod16 : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) ->
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
Lemma mw_blk_tail_vis : forall ly S (W : world segs) mem md p n a,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p + req_size n <= a < p + round_up (req_size n) 16 -> aview segs (w_H W) mem a <> None.
Proof.
  intros ly S W mem md p n a (M & _) Hb Ha.
  unfold ablocks, blocks in Hb. apply in_map_iff in Hb as ([u r] & Eb & Hb). cbn [fst snd] in Eb.
  injection Eb as Ep En.
  apply in_map_iff in Hb as (k & Ek & Hk). injection Ek as Eu Er. subst u r.
  apply filter_In in Hk as [Hk _].
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & UA & _ & _ & Hn & HX & _).
  pose proof (mw_chunk_room_mod16 ly S _ k M Hk) as R16.
  assert (CN : ck_n k = req_size n)
    by (unfold ck_n, req_size; destruct (Z.eqb_spec (ck_req k) 0); destruct (Z.eqb_spec n 0); lia).
  assert (N1 : 1 <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  assert (RU : round_up (req_size n) 16 <= ck_extent k - ck_rz k).
  { apply round_up_le; [lia | | exact R16]. rewrite <- CN. unfold ck_n in *. lia. }
  pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ M) _ (mw_chunk_tail_in_ajunk ly S k Hk)) as V.
  unfold range_vis in V. cbn [fst snd] in V. rewrite CN in V.
  rewrite aeval_aoff in V by (intros e'; destruct (ck_beg k); cbn; discriminate).
  change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
  replace a with (ck_base B ly k + (ck_rz k + req_size n) + (a - (ck_base B ly k + (ck_rz k + req_size n)))) by lia.
  apply V. rewrite <- Ep, UA in Ha. lia.
Qed.
End tv.

(* g_nl lies inside one loaded segment of image A, and meets no runtime static (see
   reac_link_alias_writeHead.v aw_gnl_in_image_b / aw_gnl_static_b) *)
Lemma mw_gnl_in_image_b :
  existsb (relro_in_seg LA_G_NL (LA_G_NL + NK_SIZE)) Asan.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mw_gnl_static_b :
  forallb (fun r => (fst r + snd r <=? LA_G_NL) || (LA_G_NL + NK_SIZE <=? fst r)) AF0m.Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

(* the image's end is page aligned *)
Lemma mw_img_end_al : pcap_img_end mod 8 = 0.
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Set Default Proof Using "All".

Lemma mw_aview_present : forall H (m : word -> option byte) a, apresent H m a -> aview SEGS H m a <> None.
Proof.
  intros H m a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.

Lemma mw_rom_vis : forall H (m : word -> option byte) a, 0x10000 <= a < pcap_img_end -> aview SEGS H m a <> None.
Proof.
  intros H m a Ha. rewrite HSEGS. pose proof (AB13.tfib_rom_all a Ha) as Hr.
  unfold aview, mbyte. destruct (mrestrict H m (Z_to_bv 64 a)) as [b|]; cbn [option_map]; [discriminate|].
  destruct (seg_rom tfibsegs (Z_to_bv 64 a)) eqn:E; cbn [option_map]; [discriminate|].
  exfalso. exact (Hr eq_refl).
Qed.

(* g_nl's bytes are image bytes outside the runtime's statics and errno *)
Lemma mw_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. split; [|split].
  - rewrite HSEGS. destruct (proj1 (existsb_exists _ _) mw_gnl_in_image_b) as (s & Hin & H).
    unfold relro_in_seg in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H3.
    exists s. split; [exact Hin | lia].
  - rewrite (AF0m.ts_owned B TB). intros HE. apply Exists_exists in HE as (r & Hr & Hz).
    pose proof (proj1 (forallb_forall _ _) mw_gnl_static_b r Hr) as Hb. cbv beta in Hb.
    apply orb_true_iff in Hb. unfold in_zr in Hz.
    destruct Hb as [Hb | Hb]; apply Z.leb_le in Hb; unfold LA_G_NL, NK_SIZE in *; lia.
  - rewrite (AF0m.ts_errno B TB). unfold AF0m.TFIB_ERRNO, LA_G_NL, NK_SIZE in *. lia.
Qed.

(* ---- the states of a cut, and their relation to the call's ---- *)
Lemma mw_cut_facts : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3,
  mw_pre SK B cx -> mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  AR SEGS B (mw_lyc cx) (mw_Sc cx) (mw_W cx) (mw_memc cx) (mw_mdc cx) /\
  AR SEGS B ly3 S3 W3 (ms_mem ms3) md3 /\
  (forall b m, In (b, m) (ablocks B (mw_lyc cx) (mw_Sc cx)) -> In (b, m) (ablocks B ly3 S3)) /\
  (forall f, In f (frames (mw_Sc cx)) -> In f (frames S3)) /\
  (forall c q, frame_addr ly3 c q = frame_addr (mw_lyc cx) c q) /\
  ly_stk_lo ly3 = ly_stk_lo (mw_lyc cx) /\ ly_stk_hi ly3 = ly_stk_hi (mw_lyc cx) /\
  In (MW_CID, fpos) (frames S3) /\ 0 <= fpos < fs_frames MW_CID /\ ~ In (MW_CID, fpos) (frames (mw_Sc cx)) /\
  alloc_ceiling <= ly_stk_lo (mw_lyc cx) /\ ly_stk_hi (mw_lyc cx) <= 2 ^ 47.
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 HPX HB.
  pose proof (mw_pre_jc SK B cx HPX) as HJc.
  pose proof HB as HB0. unfold mw_base in HB0. cbv zeta in HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & HJ3 & Hfrs3 & Hnin & Hfpos & _ & Hperm & _ & Hfa & _).
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HARc.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  pose proof HJc as Rc. apply (aj_stk_row_eq SK SEGS B) in Rc.
  pose proof HJ3 as R3. apply (aj_stk_row_eq SK SEGS B) in R3.
  destruct (ajournal_gx_row SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (Hlo & Hhi & _).
  split; [exact HARc|]. split; [exact HAR3|].
  split; [intros b m Hbm; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hbm]|].
  split; [intros f Hf; rewrite Hfrs3; right; exact Hf|].
  split; [exact Hfa|].
  split; [rewrite (proj1 R3), (proj1 Rc); reflexivity|].
  split; [rewrite (proj2 R3), (proj2 Rc); reflexivity|].
  split; [rewrite Hfrs3; left; reflexivity|].
  split; [exact Hfpos|]. split; [exact Hnin|]. split; lia.
Qed.

Lemma mw_side_facts : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3,
  mw_pre SK B cx -> mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  4096 <= mw_F cx fpos /\ mw_F cx fpos + MW_FB <= alloc_ceiling /\ mw_F cx fpos mod 64 = 0 /\
  (mw_F cx fpos + MW_FB <= kLowMemEnd \/ kHighMemBeg <= mw_F cx fpos) /\
  mw_FL cx fpos < alloc_ceiling /\ (mw_FL cx fpos + 1 <= kLowMemEnd \/ kHighMemBeg <= mw_FL cx fpos) /\
  mw_SH cx fpos = shadow_addr (mw_F cx fpos) /\
  frame_addr ly3 MW_CID fpos = mw_F cx fpos /\ flag_addr ly3 MW_CID fpos = mw_FL cx fpos /\
  (forall a, mw_F cx fpos <= a < mw_F cx fpos + MW_FB -> apresent (w_H W3) (ms_mem ms3) a /\ ~ in_img SEGS a) /\
  (forall a, mw_SH cx fpos <= a < mw_SH cx fpos + MW_SHN -> apresent (w_H W3) (ms_mem ms3) a) /\
  apresent (w_H W3) (ms_mem ms3) (mw_FL cx fpos) /\ ~ in_img SEGS (mw_FL cx fpos).
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 HPX HB.
  destruct (mw_cut_facts cx fpos X ly3 S3 W3 ms3 md3 HPX HB)
    as (HARc & HAR3 & Hbl & Hfr & Hfa & _ & _ & Hin3 & _ & _ & _ & _).
  pose proof HB as HB0. unfold mw_base in HB0. cbv zeta in HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & HJ3 & _).
  pose proof (mw_pre_jc SK B cx HPX) as HJc.
  assert (EFL : flag_addr ly3 MW_CID fpos = mw_FL cx fpos).
  { unfold mw_FL. rewrite (proj2 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      MW_CID fpos HJ3)).
    rewrite (proj2 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MW_CID fpos HJc)).
    reflexivity. }
  assert (EF : frame_addr ly3 MW_CID fpos = mw_F cx fpos) by (rewrite Hfa; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 MW_CID fpos HAR3 Hin3) as (HF4096 & HFceil & HFapp).
  rewrite EF in HF4096, HFceil, HFapp. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 MW_CID fpos HAR3 Hin3) as (HFa64 & _ & _).
  rewrite EF in HFa64.
  destruct (al_frames _ _ LAWS _ _ _ _ _ MW_CID fpos HAR3 Hin3) as (_ & _ & HFpres & HFSpres).
  rewrite EF in HFpres, HFSpres.
  destruct (al_flag _ _ LAWS _ _ _ _ _ MW_CID fpos HAR3 Hin3) as (HFLpres & _ & HFLapp & HFLceil).
  rewrite EFL in HFLpres, HFLapp, HFLceil. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
  assert (Hci : forall a, (exists cid pos, In (cid, pos) (frames S3) /\
                   frame_addr ly3 cid pos <= a < frame_addr ly3 cid pos + fs_frame_bytes cid) -> ~ in_img SEGS a).
  { intros a Ha. exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR3 (or_intror (or_introl Ha)))). }
  assert (Hcf : ~ in_img SEGS (mw_FL cx fpos)).
  { rewrite <- EFL. exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ _ HAR3
      (or_intror (or_intror (ex_intro _ MW_CID (ex_intro _ fpos (conj Hin3 eq_refl))))))). }
  change (fs_frame_bytes MW_CID) with 1024 in *. change (1024 / 8) with 128 in HFSpres.
  unfold MW_FB, MW_SHN.
  split; [exact HF4096|]. split; [exact HFceil|]. split; [exact HFa64|].
  split; [unfold kLowMemEnd, kHighMemBeg in *; lia|].
  split; [exact HFLceil|]. split; [unfold kLowMemEnd, kHighMemBeg in *; lia|].
  split; [reflexivity|]. split; [exact EF|]. split; [exact EFL|].
  split.
  { intros a Ha. split; [exact (proj1 (HFpres a Ha))|].
    apply Hci. exists MW_CID, fpos. split; [exact Hin3|]. rewrite EF. change (fs_frame_bytes MW_CID) with 1024. exact Ha. }
  split.
  { intros a Ha. destruct (HFSpres (a - shadow_addr (mw_F cx fpos))) as (Hp & _).
    { unfold mw_SH, shadow_addr in *. lia. }
    replace (shadow_addr (mw_F cx fpos) + (a - shadow_addr (mw_F cx fpos))) with a in Hp by lia. exact Hp. }
  split; [exact HFLpres | exact Hcf].
Qed.

(* every byte at or above the allocator's ceiling is outside the side frame this call took *)
Lemma mw_not_side_hi : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3 a,
  mw_pre SK B cx -> mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  alloc_ceiling <= a -> ~ aside_rng (mw_lyc cx) MW_CID fpos a.
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 a HPX HB Ha.
  destruct (mw_side_facts cx fpos X ly3 S3 W3 ms3 md3 HPX HB)
    as (F1 & F2 & F3 & F4 & FL1 & FL2 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold mw_F, mw_FL, MW_FB in *.
  intros [Hf | [Hs | Hl]].
  - unfold in_zr, frame_rng in Hf. cbn [fst snd] in Hf. change (fs_frame_bytes MW_CID) with 1024 in Hf. lia.
  - unfold in_zr, shadow_addr in Hs. cbn [fst snd] in Hs. change (fs_frame_bytes MW_CID / 8) with 128 in Hs.
    unfold SHADOW_OFF in Hs. unfold kLowMemEnd, kHighMemBeg in *. lia.
  - lia.
Qed.

(* ---- a read-set byte at the cut ---- *)
Lemma mw_view_akb : forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 a,
  mw_pre SK B cx -> mw_base SK B cx fpos NoX ly3 S3 W3 ms3 md3 ->
  akb SEGS B (mw_lyc cx) (mw_Sc cx) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) a ->
  aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (mw_W cx)) (mw_memc cx) a.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 a HPX HB HAKB.
  pose proof (mw_pre_jc SK B cx HPX) as HJc.
  destruct (mw_cut_facts cx fpos NoX ly3 S3 W3 ms3 md3 HPX HB) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfpos & Hnin & _).
  eapply (akept_akb_gx SK SEGS B); [exact HJc | exact (mw_base_kept SK B cx fpos NoX ly3 S3 W3 ms3 md3 HB) | exact HAKB |].
  intros [[] | HS]. revert HS.
  pose proof (@pa_img_range _ link_listing PI) as HIMG.
  eapply (akb_not_side SK SEGS B); try eassumption. unfold MW_CID; lia.
Qed.

Lemma mw_fmiss : forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3,
  mw_pre SK B cx -> mw_base SK B cx fpos NoX ly3 S3 W3 ms3 md3 ->
  fmiss (mw_lyc cx) (mw_Sc cx) (fun a => NoX a \/ aside_rng (mw_lyc cx) MW_CID fpos a).
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 HPX HB.
  destruct (mw_cut_facts cx fpos NoX ly3 S3 W3 ms3 md3 HPX HB) as (HARc & _ & _ & _ & _ & _ & _ & _ & Hfpos & Hnin & _).
  apply fmiss_or.
  - intros c q s _ _ [].
  - exact (fmiss_side SEGS B _ _ (mw_W cx) (mw_memc cx) (mw_mdc cx) MW_CID fpos HARc
             ltac:(unfold MW_CID; lia) Hfpos Hnin).
Qed.

(* the shadow facts of a read-set range, from the call to the cut *)
Lemma mw_shadow_at : forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 p n,
  mw_pre SK B cx -> mw_base SK B cx fpos NoX ly3 S3 W3 ms3 md3 -> 0 < n ->
  (forall a, p <= a < p + n -> akb SEGS B (mw_lyc cx) (mw_Sc cx) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) a) ->
  range_addressable (aview SEGS (w_H (mw_W cx)) (mw_memc cx)) SHADOW_OFF p n ->
  shadow_hull_vis (aview SEGS (w_H (mw_W cx)) (mw_memc cx)) p n ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF p n /\
  shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms3)) p n.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 p n HPX HB Hn Hakb Hra Hhv.
  destruct (mw_cut_facts cx fpos NoX ly3 S3 W3 ms3 md3 HPX HB)
    as (HARc & HAR3 & Hbl & _ & _ & Elo & Ehi & _).
  apply (shadow_transport_akb SEGS B LAWS TB pa_img_range (mw_lyc cx) (mw_Sc cx) (mw_W cx) (mw_memc cx)
           (mw_mdc cx) ly3 S3 W3 (ms_mem ms3) md3
           (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) _ p n HARc HAR3 Elo Ehi Hbl
           (mw_base_kept SK B cx fpos NoX ly3 S3 W3 ms3 md3 HB)
           (mw_fmiss cx fpos ly3 S3 W3 ms3 md3 HPX HB) Hn Hakb Hra Hhv).
Qed.

(* a byte after a read-set byte, in its 8-byte granule, visible at the call, is visible at the cut *)
Lemma mw_tail_at : forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 x a,
  mw_pre SK B cx -> mw_base SK B cx fpos NoX ly3 S3 W3 ms3 md3 ->
  akb SEGS B (mw_lyc cx) (mw_Sc cx) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) x ->
  0 <= x -> x < a < x - x mod 8 + 8 ->
  aview SEGS (w_H (mw_W cx)) (mw_memc cx) a <> None ->
  aview SEGS (w_H W3) (ms_mem ms3) a <> None.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 x a HPX HB HAKB Hx0 Ha Hv.
  destruct (mw_cut_facts cx fpos NoX ly3 S3 W3 ms3 md3 HPX HB)
    as (HARc & HAR3 & Hbl & Hfr & Hfa & Elo & Ehi & _ & _ & _ & Hceil & H47).
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as (Hsp1 & Hsp2 & Hsp3 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity.
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hxm.
  pose proof (mw_base_kept SK B cx fpos NoX ly3 S3 W3 ms3 md3 HB) as (K1 & K2 & K3 & K4 & _).
  destruct HAKB as [(H1 & H2) | [(b & m & Hin & Hr) | [(H1 & H2 & H3) | (c & q & Hin & Hr)]]].
  - (* the stack row: akept's clause 1 *)
    rewrite (K1 a); [exact Hv | lia | |].
    + rewrite HK in H2 |- *. intros Hw. apply H2. split; lia.
    + intros [[] | Hs]. exact (mw_not_side_hi cx fpos NoX ly3 S3 W3 ms3 md3 a HPX HB ltac:(lia) Hs).
  - (* a heap block of the call *)
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin) as (Hb16 & _ & _ & _ & _ & _ & Hmn).
    destruct (Z_lt_ge_dec a (b + req_size m)) as [Hlt | Hge].
    + rewrite (mw_view_akb cx fpos ly3 S3 W3 ms3 md3 a HPX HB); [exact Hv|].
      right; left. exists b, m. split; [exact Hin | lia].
    + apply (mw_blk_tail_vis SEGS B ly3 S3 W3 (ms_mem ms3) md3 b m a HAR3 (Hbl b m Hin)).
      split; [lia|]. unfold round_up.
      assert (Hrs : 1 <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
      pose proof (Z.div_mod (req_size m + 16 - 1) 16 ltac:(lia)) as Hd.
      pose proof (Z.mod_pos_bound (req_size m + 16 - 1) 16 ltac:(lia)) as Hdm.
      lia.
  - (* an image byte: the image file has every byte of the granule *)
    pose proof (pa_img_range x H1) as Hxi. pose proof mw_img_end_al as Hal.
    apply mw_rom_vis. lia.
  - (* a side frame of the caller *)
    pose proof (frame_al64 SEGS B (mw_lyc cx) (mw_Sc cx) (mw_W cx) (mw_memc cx) (mw_mdc cx) c q HARc Hin)
      as (Hfa64 & Hfb64 & _).
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
    rewrite (mw_view_akb cx fpos ly3 S3 W3 ms3 md3 a HPX HB); [exact Hv|].
    right; right; right. exists c, q. split; [exact Hin|].
    unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.

(* ---- the read-only image at the cut: the empty relro window ---- *)
Lemma mw_arodata0 : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3,
  mw_pre SK B cx -> mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> mw_E cx a) ->
  arodata_okP SEGS 0 0 B (aview SEGS (w_H W3) (ms_mem ms3)).
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 HPX HB HX a Hro Hno Herr.
  pose proof HPX as ((_ & _ & HROD & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnro) & _ & _).
  destruct Hro as [(s & Hs & Hw & Hr) | Hr]; [|lia].
  assert (Hi : in_img SEGS a) by (exists s; split; [exact Hs | exact Hr]).
  pose proof (mw_base_kept SK B cx fpos X ly3 S3 W3 ms3 md3 HB) as (_ & _ & K3 & _).
  pose proof (pa_segs_low a Hi) as Hlow.
  rewrite (K3 a Hi Hno Herr).
  - apply HROD; [left; exists s; split; [exact Hs | split; [exact Hw | exact Hr]] | exact Hno | exact Herr].
  - intros [HXa | Hs'].
    + apply (Hnro a (HX a HXa)). left. exists s. split; [exact Hs | split; [exact Hw | exact Hr]].
    + destruct (mw_side_facts cx fpos X ly3 S3 W3 ms3 md3 HPX HB)
        as (F1 & _ & _ & _ & _ & _ & _ & _ & _ & HFi & _ & _ & HFLi).
      destruct Hs' as [Hf | [Hsh | Hl]].
      * unfold in_zr, frame_rng in Hf. cbn [fst snd] in Hf. change (fs_frame_bytes MW_CID) with MW_FB in Hf.
        exact (proj2 (HFi a Hf) Hi).
      * unfold in_zr, shadow_addr in Hsh. cbn [fst snd] in Hsh. unfold mw_F in F1.
        unfold SHADOW_OFF, kLowMemEnd in *. lia.
      * subst a. exact (HFLi Hi).
Qed.

Lemma mw_rtrom : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3,
  mw_pre SK B cx -> mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> mw_E cx a) ->
  rt_rom_view SEGS B W3 (ms_mem ms3).
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 HPX HB HX a Hrom Hno Herr.
  apply (mw_arodata0 cx fpos X ly3 S3 W3 ms3 md3 HPX HB HX a); [left; exact Hrom | exact Hno | exact Herr].
Qed.

(* ---- g_nl at the cut ---- *)
Lemma mw_gnl_view : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3 a,
  mw_pre SK B cx -> mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> mw_E cx a) ->
  LA_G_NL <= a < LA_G_NL + NK_SIZE ->
  aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (mw_W cx)) (mw_memc cx) a.
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 a HPX HB HX Ha.
  destruct (mw_gnl_img a Ha) as (Hi & Hno & Herr).
  pose proof (mw_base_kept SK B cx fpos X ly3 S3 W3 ms3 md3 HB) as (_ & _ & K3 & _).
  apply (K3 a Hi Hno Herr).
  intros [HXa | Hs].
  - destruct (mw_blk_facts SK B cx a HPX (HX a HXa)) as (_ & _ & Hm & _).
    pose proof HPX as (_ & _ & (mbs & kbs & tab & nm & al & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & Hgnl & _)).
    unfold apart_gnl, mw_m in *. lia.
  - pose proof (pa_segs_low a Hi) as Hlow.
    destruct (mw_side_facts cx fpos X ly3 S3 W3 ms3 md3 HPX HB)
      as (F1 & _ & _ & _ & _ & _ & _ & _ & _ & HFi & _ & _ & HFLi).
    destruct Hs as [Hf | [Hsh | Hl]].
    + unfold in_zr, frame_rng in Hf. cbn [fst snd] in Hf. change (fs_frame_bytes MW_CID) with MW_FB in Hf.
      exact (proj2 (HFi a Hf) Hi).
    + unfold in_zr, shadow_addr in Hsh. cbn [fst snd] in Hsh. unfold mw_F in F1.
      unfold SHADOW_OFF, kLowMemEnd in *. lia.
    + subst a. exact (HFLi Hi).
Qed.

End b.
End a.
