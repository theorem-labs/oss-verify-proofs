(* TransportGNotice: the notice-call kit of the G-form caller-journal walks of image A (lib/A/W_journalG.v ajournal_gx
   over lib/A/TransportG.v G_HARNESS) that take a side-stack frame of their own and call notice (notice_cg.v) from it.
   It holds the one copy of the generic lemmas of AW59's MonNtcKit.v (h-hreply-s5-p7, 39e1ef73279e) and of AW54's
   SlostNtcKit.v (h-rw-man-11, de73930eb03a). Where the two overlapped, AW59's lemma is the one kept: SlostNtcKit.v's
   sn_ra_zero was frame_ra_zero, sn_hull_in frame_hull_vis (with the empty range too) and sn_tframe a case of
   trans_tframe_at_kept_gx. MonNtcKit.v's dk_kept_nfz_gw is TransportGFrame.v's, Required here. Nothing here names the
   function that calls notice, a register of a particular function or an image address.
   - garr8_of_aview: a list of bytes read off the view, in garr8's form. Ported: cgif_file_fuzzer lib/A/ACey.v
     garr8_of_aview (origin/ossv/recipes c5e779efe8c9; the same statement up to binder names), proved from this unit's
     AE2y.v val_mem1_of_aview.
   - garr8_of_put: the bytes a store of n bytes of v leaves (val_mem), read as garr8 of TWorld.v put n v (the form in
     which a notice's fields are compared with the bytes of check_state_data_cg.v trans_ntc_at).
   - frame_ra_zero, frame_hull_vis: the addressability and the shadow hull of a range of a 64-aligned side-stack frame,
     from the frame's shadow bytes (decode_rd_ok of a notice the caller builds in its frame).
   - trans_src_ok_kept_gx, trans_tframe_at_kept_gx: DgnTransportCg.v trans_src_ok / check_state_data_cg.v
     trans_tframe_at carried from the walk's entry to the call of notice, a later state with more frames (the own
     frame), from the walk's running acall_kept_g and gx_kept_ex (G outside the written range), for every length of
     the range, the empty one included.
   - aview_of_val_mem1, chunk_zero_aview, chunks_zero_aview: a byte a run's region leaves, read off the view.
     aview_of_val_mem1 is ported: omx-clap-core fuzz_manifest lib/A/FMpoisonW.v aview_of_val_mem1
     (origin/ossv/recipes c5e779efe8c9; the same statement up to binder names).
   - notice_wr_G: every byte notice stores (notice_cg.v notice_wr) is a byte of G. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AE2y TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 2. Bytes, addressability and the shadow hull of a frame range       *)
(* ------------------------------------------------------------------ *)

Section b. Context {rc : YM05.RunCeil}.

(* A list of bytes read off the view, in garr8's form. *)
Lemma garr8_of_aview : forall H (m : word -> option byte) base (l : list Z),
  (forall j, (j < length l)%nat -> aview tfibsegs H m (base + Z.of_nat j) = Some (nth j l 0)) ->
  garr8 tfibsegs (mrestrict H m) base l.
Proof.
intros H m base l Hv j Hj.
destruct (aview_byte tfibsegs H m _ _ (Hv j Hj)) as (b & _ & _ & Hr).
exact (conj (AE2y.val_mem1_of_aview H m _ _ (Hv j Hj)) Hr).
Qed.

(* The bytes a store of n bytes of v leaves, read as garr8 of put n v. *)
Lemma garr8_of_put : forall (segs : list Segment) (mem : word -> option byte) a (n : nat) v,
  val_mem segs mem a n v -> garr8 segs mem a (map DSpec.bz (TW.put n v)).
Proof.
intros segs mem a n v H j Hj. rewrite length_map, TWL.length_put in Hj.
assert (E : nth j (map DSpec.bz (TW.put n v)) 0 = YO0f.le_byte v n j).
{ rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) by (rewrite length_map, TWL.length_put; exact Hj).
  rewrite map_nth. unfold DSpec.bz. apply tw_le_byte_put. exact Hj. }
assert (R : 0 <= YO0f.le_byte v n j < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
rewrite E. split; [|exact R].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (tw_le_byte1 _ R). exact (H j Hj).
Qed.

(* A range of an 8-aligned frame whose granules lo .. hi - 1 have the shadow byte 0 is addressable. *)
Lemma frame_ra_zero : forall (rd : Z -> option Z) F q n lo hi,
  0 <= F -> F mod 8 = 0 -> F + 8 * lo <= q -> q + n <= F + 8 * hi ->
  (forall i, lo <= i < hi -> rd (SHADOW_OFF + F / 8 + i) = Some 0) ->
  range_addressable rd SHADOW_OFF q n.
Proof.
intros rd F q n lo hi HF0 HF8 Hlo Hhi HZ x Hx.
exists 0. split; [|left; reflexivity].
unfold shadow_of_addr.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
set (f := F / 8) in *.
assert (Ex : x / 8 = f + (x - F) / 8).
{ replace x with (f * 8 + (x - F)) at 1 by lia. apply Z.div_add_l. lia. }
rewrite Ex, Z.add_assoc. apply HZ. split.
- apply Z.div_le_lower_bound; lia.
- apply Z.div_lt_upper_bound; lia.
Qed.

(* The shadow hull of a non-empty range of a 64-aligned frame of fs bytes (fs a multiple of 64) lies in the frame's
   fs / 8 shadow bytes (YG0s.v hull_inside). *)
Lemma frame_hull_vis : forall (rd : Z -> option Z) F fs q n,
  0 <= F -> F mod 64 = 0 -> fs mod 64 = 0 -> F <= q -> 1 <= n -> q + n <= F + fs ->
  (forall i, 0 <= i < fs / 8 -> rd (shadow_addr F + i) <> None) ->
  shadow_hull_vis rd q n.
Proof.
intros rd F fs q n HF0 HF64 Hfs64 H1 Hn H2 HV s Hs.
assert (Hhi : (F + fs) mod 64 = 0) by (rewrite Z.add_mod, HF64, Hfs64 by lia; reflexivity).
destruct (YG0s.hull_inside F (F + fs) q n s HF64 Hhi HF0 H1 H2 Hn Hs) as (g & Hg8 & Hgr & ->).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
pose proof (Z.div_mod fs 64 ltac:(lia)) as DS. rewrite Hfs64, Z.add_0_r in DS.
pose proof (Z.div_mod g 8 ltac:(lia)) as DG. rewrite Hg8, Z.add_0_r in DG.
assert (EF : F / 8 = 8 * (F / 64)) by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (ES : fs / 8 = 8 * (fs / 64)) by (rewrite DS at 1; replace (64 * (fs / 64)) with ((8 * (fs / 64)) * 8) by lia; apply Z.div_mul; lia).
replace (shadow_addr g) with (shadow_addr F + (g / 8 - F / 8)) by (unfold shadow_addr; lia).
apply HV. lia.
Qed.
End b.

(* ------------------------------------------------------------------ *)
(* 3. trans_src_ok and trans_tframe_at at a later state of the walk    *)
(* ------------------------------------------------------------------ *)

Section c. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* DgnTransportCg.v trans_src_ok_acall_g from the walk's own facts: the call state (lyc, Sc) and a later state
   (ly2, S2) whose blocks and frames contain the call's at the same addresses; the walk's acall_kept_g and gx_kept_ex
   over its written range E, which misses the range and the shadow band. The range's bytes are kept (a heap block:
   the block clause; FAKE: the frame clause; G: gx_kept_ex; the machine stack: the clause above alloc_ceiling;
   TRANS_RO_RD: the image clause); decode_rd_ok at the later memory: for a non-empty range as trans_src_ok_kept
   gives it, for the empty range from its shadow hull at the later state (a frame's shadow bytes are present there;
   trans_sh_any; the machine stack's zero shadow), with ly_stk_lo lyc < ly_stk_hi lyc. *)
Lemma trans_src_ok_kept_gx : trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world tfibsegs) memc mdc ly2 S2 (W2 : world tfibsegs) mem2 md2 slo shi (E : Z -> Prop) q n,
  @AR rc tfibsegs B lyc Sc W memc mdc -> @AR rc tfibsegs B ly2 S2 W2 mem2 md2 ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  (forall f, In f (frames Sc) -> In f (frames S2)) ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc -> ly_stk_lo lyc < ly_stk_hi lyc ->
  acall_kept_g tfibsegs B TG.G_HARNESS lyc Sc W memc W2 mem2 slo shi E ->
  gx_kept_ex tfibsegs TG.G_HARNESS E W memc W2 mem2 ->
  (forall a, q <= a < q + n -> ~ E a) -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok B lyc Sc W memc q n -> 0 <= n ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) memc a).
Proof.
intros HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2 Hbl Hfr Hfa Elo Ehi Hstk
  (K1 & K2 & K3 & K4 & _) HGK HnE HnEs Hoff Hs Hn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KS : forall cid pos s, In (cid, pos) (frames Sc) ->
   in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
   aview tfibsegs (w_H W2) mem2 s = aview tfibsegs (w_H W) memc s).
{ intros cid pos s Hin Hs'. apply (K4 cid pos s Hin (or_intror Hs')). apply HnEs.
  destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
  unfold in_zr in Hs'. cbn [fst snd] in Hs'.
  unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
assert (KV : forall a, q <= a < q + n -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) memc a).
{ intros a Ha. destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
    replace a with (bA + (a - bA)) by lia.
    apply (K2 bA nA (a - bA) Hin ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
  - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
    + apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
    + exact (HGK a (HG a Ha) (HnE a Ha)).
    + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2]. apply K1; lia.
    + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
      apply (K3 a (trans_ro_img a Ra)); [|exact Ho | exact He].
      intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ra) as Rb.
      unfold TransportG.G_HARNESS_LO in Gh. lia. }
split; [|exact KV].
destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
{ left. exists bA, nA. split; [exact (Hbl _ Hin) | lia]. }
assert (Hrd2 : decode_rd_ok W2 mem2 q n).
{ destruct (Z.eq_dec n 0) as [En | Hn0].
  - subst n. destruct Hrd as (_ & _ & _ & R4 & R5 & R6).
    assert (HH : shadow_hull_vis (aview tfibsegs (w_H W2) mem2) q 0).
    { destruct HL as [(cid & pos & Hin & F1 & F2) | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
      - assert (Hin2 : In (cid, pos) (frames S2)) by exact (Hfr _ Hin).
        destruct (dkg_frame_al64 tfibsegs B ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (A1 & A2 & A3).
        destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (_ & _ & _ & HSh).
        destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (G1 & G2 & _).
        rewrite Hfa in A1, HSh, G1, G2.
        set (x := if q <? frame_addr lyc cid pos + fs_frame_bytes cid then q else q - 1).
        assert (Hx : frame_addr lyc cid pos <= x /\ x + 1 <= frame_addr lyc cid pos + fs_frame_bytes cid /\
                     x <= q /\ q <= x + 1).
        { unfold x. destruct (Z.ltb_spec q (frame_addr lyc cid pos + fs_frame_bytes cid)); lia. }
        apply (trans_hull_sub _ x 1 q 0); [|lia|lia].
        apply (frame_hull_vis _ (frame_addr lyc cid pos) (fs_frame_bytes cid) x 1); try lia.
        intros i Hi. apply aview_some_of_apresent. exact (proj1 (HSh i Hi)).
      - exact (proj2 (Hsh ly2 S2 W2 mem2 md2 HAR2)).
      - set (x := if ly_stk_lo lyc <? q then q - 1 else q).
        assert (Hx : ly_stk_lo lyc <= x /\ x + 1 <= ly_stk_hi lyc /\ x <= q /\ q <= x + 1).
        { unfold x. destruct (Z.ltb_spec (ly_stk_lo lyc) q); lia. }
        apply (trans_hull_sub _ x 1 q 0); [|lia|lia].
        exact (proj2 (stack_zshadow_ra B ly2 S2 W2 mem2 md2 x 1 HAR2 ltac:(lia) ltac:(rewrite Elo; lia)
          ltac:(rewrite Ehi; lia))).
      - exact (proj2 (Hsh ly2 S2 W2 mem2 md2 HAR2)). }
    split; [intros a Ha; lia|]. split; [intros x Hx; lia|]. split; [exact HH|]. exact (conj R4 (conj R5 R6)).
  - assert (Hnp : 0 < n) by lia.
    destruct HL as [HF | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
    + apply (decode_rd_ok_fake_kept B LAWS lyc Sc W W2 memc mem2 mdc q n HAR HF Hrd Hnp KV).
      intros cid pos s Hin Hs'. exact (KS cid pos s Hin Hs').
    + destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
    + destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 q n HAR2 Hnp ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia))
        as [Ha Hh].
      exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
    + destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh). }
exact (trans_src_ok_inner B lyc Sc W memc ly2 S2 W2 mem2 q n Hbl Hfr Hfa Elo Ehi Hrd2 (or_intror (conj HL Hrd))).
Qed.

(* check_state_data_cg.v trans_tframe_at at a later state and a callee's window inside the walk's: the frame's bytes
   are not in the written range, its placement is carried by trans_src_ok_kept_gx. *)
Lemma trans_tframe_at_kept_gx : trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world tfibsegs) memc mdc ly2 S2 (W2 : world tfibsegs) mem2 md2 (E : Z -> Prop)
    (regs regs2 : bvmap 5 word) K K2 (TF : option TI.tframe),
  @AR rc tfibsegs B lyc Sc W memc mdc -> @AR rc tfibsegs B ly2 S2 W2 mem2 md2 ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  (forall f, In f (frames Sc) -> In f (frames S2)) ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc -> ly_stk_lo lyc < ly_stk_hi lyc ->
  acall_kept_g tfibsegs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - K) (spZ regs) E ->
  gx_kept_ex tfibsegs TG.G_HARNESS E W memc W2 mem2 ->
  (forall fr, TF = Some fr ->
     forall a, TI.tf_addr fr <= a < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) -> ~ E a) ->
  (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  spZ regs - K <= spZ regs2 - K2 -> spZ regs2 <= spZ regs ->
  trans_tframe_at B lyc Sc W memc regs K TF -> trans_tframe_at B ly2 S2 W2 mem2 regs2 K2 TF.
Proof.
intros HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 E regs regs2 K K2 TF HAR HAR2 Hbl Hfr Hfa Elo Ehi Hstk
  HK HGK HnE HnEs Hw1 Hw2 HTF.
destruct TF as [fr|]; [|exact I].
destruct HTF as (H0 & Hg & Hs & Ho).
destruct (trans_src_ok_kept_gx HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 (spZ regs - K) (spZ regs) E
  (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))) HAR HAR2 Hbl Hfr Hfa Elo Ehi Hstk HK HGK (HnE fr eq_refl) HnEs
  Ho Hs (Nat2Z.is_nonneg _)) as [Hs2 KV].
split; [exact H0|]. split.
- apply (garr8_frame tfibsegs _ _ _ _ Hg). intros a Ha. rewrite length_map in Ha.
  apply mbyte_of_aview. exact (KV a Ha).
- split; [exact Hs2|]. unfold decode_off_win in *. lia.
Qed.
End c.

(* ------------------------------------------------------------------ *)
(* 4. A byte of a run's region, read off the view                      *)
(* ------------------------------------------------------------------ *)

Section w. Context {rc : YM05.RunCeil}.
Lemma aview_of_val_mem1 : forall H (m : word -> option byte) a v,
  val_mem tfibsegs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview tfibsegs H m a = Some v.
Proof.
intros H m a v Hv Hr. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256 Hr), (Z.mod_small v 256 Hr).
unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.

Lemma chunk_zero_aview : forall E H (m : word -> option byte) base off,
  YP09.chunk_ok tfibsegs E (mrestrict H m) base (YP09.mkChunk off (CVal 1 (SLit 0))) ->
  aview tfibsegs H m (base + off) = Some 0.
Proof.
intros E H m base off Hc.
pose proof (val_of_chunk_any tfibsegs E (mrestrict H m) base off 1 (SLit 0) Hc ltac:(lia)) as Hv.
replace (bv_unsigned (sv_denot E (SLit 0)) mod 2 ^ (8 * Z.of_N 1)) with 0 in Hv by reflexivity.
exact (aview_of_val_mem1 H m _ 0 Hv ltac:(lia)).
Qed.

Lemma chunks_zero_aview : forall E H (m : word -> option byte) base cs off,
  Forall (YP09.chunk_ok tfibsegs E (mrestrict H m) base) cs -> In (YP09.mkChunk off (CVal 1 (SLit 0))) cs ->
  aview tfibsegs H m (base + off) = Some 0.
Proof.
intros E H m base cs off HF Hin. rewrite Forall_forall in HF. exact (chunk_zero_aview E H m base off (HF _ Hin)).
Qed.
End w.

(* ------------------------------------------------------------------ *)
(* 5. notice's stores                                                  *)
(* ------------------------------------------------------------------ *)

(* Every byte notice stores, of every kind, is a byte of GOT's or M's payload, bytes of G. *)
Lemma notice_wr_G : forall Bw n a, notice_wr Bw n a -> inG TG.G_HARNESS a.
Proof.
intros Bw n a H.
assert (HG : forall b k, In (b, k) TG.G_HARNESS -> b <= a < b + k -> inG TG.G_HARNESS a)
  by (intros b k Hin Hr; unfold inG; apply Exists_exists; exists (b, k);
      split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
pose proof (TMAP_A_in_G _ _ _ TMAP_A_GOT) as Gg. pose proof (TMAP_A_in_G _ _ _ TMAP_A_M) as Gm.
unfold notice_wr, twa_fld in H.
unfold TW.A_GOT_t_state, TW.GOT_t_ESZ, TC.TRANS_MAX, TW.A_GOT_n, TW.A_GOT_acked, TW.A_M_fly_on, TW.A_GOT_desk,
  TW.A_GOT_ndata, TW.A_GOT_foreign in H.
destruct H as [(_ & [(Hn & Ha) | Ha]) | [(_ & Ha) | [(_ & Ha) | [(_ & Ha) | [(_ & Ha) | (_ & Ha)]]]]];
  [apply (HG _ _ Gg) | apply (HG _ _ Gg) | apply (HG _ _ Gg) | apply (HG _ _ Gm) | apply (HG _ _ Gg)
  | apply (HG _ _ Gg) | apply (HG _ _ Gg)]; unfold TW.SZ_GOT, TW.SZ_M; lia.
Qed.
