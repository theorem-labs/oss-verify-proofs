(* TransportGNoticeB: image B's twin of lib/A/Prog/TransportGNotice.v, the notice-call kit of the G-form caller-journal
   walks (lib/A/W_journalG.v ajournal_gx over lib/B/TransportGB.v G_HARNESS_B) that take a side-stack frame of their own
   and call notice (lib/B/Prog/notice_cg.v) from it. Nothing here names the function that calls notice, a register of
   a particular function or an image address.
   Each lemma has A's name and A's statement read at image B: image B's segments (lib/B/YB1v.v tfibsegs), its G
   (TransportGB.v G_HARNESS_B), its call kit (lib/B/Prog/DgnTransportBCg.v trans_src_ok, decode_rd_ok, ...), its
   trans_tframe_at (lib/B/Prog/check_state_data_cg.v), its notice_wr (lib/B/Prog/notice_cg.v, fields by
   lib/B/Prog/m_set_cg.v twb_fld) and its world table (lib/B/Prog/TWorldB.v TMAP_B); the proofs are A's at those names.
   - garr8_of_aview, aview_of_val_mem1, chunk_zero_aview, chunks_zero_aview: bytes of a run's region read off the view
     (A's are stated at image A's tfibsegs). aview_of_val_mem1 and garr8_of_aview are ports, as A's are (A's header).
   - trans_src_ok_kept_gx, trans_tframe_at_kept_gx: trans_src_ok / trans_tframe_at carried from the walk's entry to the
     call of notice, a later state with more frames (the own frame), from the running acall_kept_g and gx_kept_ex.
   - notice_wr_G: every byte notice stores is a byte of G_HARNESS_B.
   The image-free lemmas of A's kit are Required from lib/A/Prog/TransportGNotice.v, not restated: garr8_of_put,
   frame_ra_zero, frame_hull_vis (used here as TGNA.frame_hull_vis). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TGNA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGNotice.
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
destruct (aview_byte tfibsegs H m _ _ (Hv j Hj)) as (b & Hb & Ev & Hr).
split; [|exact Hr].
(* the one byte, as lib/B/YE2y.v val_mem1_of_aview states it (that file and YE36.v belong to the unbuilt interim core
   of this base, so the step is taken here) *)
intros k Hk. replace k with 0%nat by lia. rewrite Z.add_0_r. rewrite Hb. f_equal.
rewrite (le_byte_small _ 1 0) by (cbn; lia). cbn [Nat.mul Z.of_nat Z.mul]. rewrite Z.shiftr_0_r.
rewrite Ev. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
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
  acall_kept_g tfibsegs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 slo shi E ->
  gx_kept_ex tfibsegs TG.G_HARNESS_B E W memc W2 mem2 ->
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
      unfold TransportGB.G_HARNESS_B_LO in Gh. lia. }
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
        apply (TGNA.frame_hull_vis _ (frame_addr lyc cid pos) (fs_frame_bytes cid) x 1); try lia.
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
  acall_kept_g tfibsegs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - K) (spZ regs) E ->
  gx_kept_ex tfibsegs TG.G_HARNESS_B E W memc W2 mem2 ->
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
Lemma notice_wr_G : forall Bw n a, notice_wr Bw n a -> inG TG.G_HARNESS_B a.
Proof.
intros Bw n a H.
assert (HG : forall b k, In (b, k) TG.G_HARNESS_B -> b <= a < b + k -> inG TG.G_HARNESS_B a)
  by (intros b k Hin Hr; unfold inG; apply Exists_exists; exists (b, k);
      split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
pose proof (TMAP_B_in_G _ _ _ TMAP_B_GOT) as Gg. pose proof (TMAP_B_in_G _ _ _ TMAP_B_M) as Gm.
unfold notice_wr, twb_fld in H.
unfold TW.A_GOT_t_state, TW.GOT_t_ESZ, TC.TRANS_MAX, TW.A_GOT_n, TW.A_GOT_acked, TW.A_M_fly_on, TW.A_GOT_desk,
  TW.A_GOT_ndata, TW.A_GOT_foreign in H.
destruct H as [(_ & [(Hn & Ha) | Ha]) | [(_ & Ha) | [(_ & Ha) | [(_ & Ha) | [(_ & Ha) | (_ & Ha)]]]]];
  [apply (HG _ _ Gg) | apply (HG _ _ Gg) | apply (HG _ _ Gg) | apply (HG _ _ Gm) | apply (HG _ _ Gg)
  | apply (HG _ _ Gg) | apply (HG _ _ Gg)]; unfold TW.SZ_GOT, TW.SZ_M; lia.
Qed.
