(* check_latest_sent_seg_cj: the caller-journal helpers of the ASan image-A walk of check_latest_sent
   (lib/A/Prog/check_latest_sent_cg.v). Each is about the G journal of lib/A/W_journalG.v and the world
   relation of lib/A/Prog/TWorldG.v; none of them steps the machine.
     - cls_tw_raw / cls_tw_av: the world relation read at the walk's image view (aview) and at the machine's
       view (check_state_wake_c.v csw_view) are the same relation, because every payload byte of TMAP_A is a
       byte of G_HARNESS, hence an image byte, which no world hides;
     - cls_jexec: the G journal carried across one footprint run of the walk, from the run's munch and growth
       facts and the placement of every byte the run writes (W_journalG.v ajournal_gx_exec);
     - cls_bcmp: the bcmp wrapper's contract (YG0d.v abcmp_realizes) read at the walk's G journal, through
       YCbq.v aj_bcmp_at and TransportGCg.v gx_call_leaf. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0s YK0o YM05 YK04 YA0i YA0n YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportAddr DgnTransportImg DgnTransportCg TransportGCg TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_latest_sent_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TGJ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TWJ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TCJ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.

(* ------------------------------------------------------------------ *)
(* the world at the image view and at the machine view                 *)
(* ------------------------------------------------------------------ *)

(* every payload byte of TMAP_A is a byte of G_HARNESS *)
Lemma cls_tw_in_G : forall x, tw_in TMAP_A x -> inG TGJ.G_HARNESS x.
Proof.
  intros x (o & b & n & Hin & Hx).
  pose proof (TMAP_A_in_G o b n Hin) as HG.
  unfold inG. apply Exists_exists. exists (b, n). split; [exact HG|].
  unfold in_zr. cbn [fst snd]. lia.
Qed.

Section cjw.
Variable B : asyms.
Hypothesis HGX : gx_ok tfibsegs B TGJ.G_HARNESS.

(* a payload byte is an image byte, so no world hides it *)
Lemma cls_vis : forall (W : world tfibsegs) x, tw_in TMAP_A x -> w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx.
  pose proof (proj1 (HGX x (cls_tw_in_G x Hx))) as Hi.
  apply (hidden_not_img tfibsegs W (Z_to_bv 64 x)).
  assert (Hr : 0 <= x < 2 ^ 64).
  { destruct Hx as (o & b & n & Hin & Hb).
    pose proof (tw_row TMAP_A o b n TMAP_A_ok Hin) as (_ & _ & _ & H1 & H2). lia. }
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Hi.
Qed.

(* the two views agree on every payload byte *)
Lemma cls_view_eq : forall (W : world tfibsegs) (m : word -> option byte) x, tw_in TMAP_A x ->
  aview tfibsegs (w_H W) m x = csw_view m x.
Proof.
  intros W m x Hx. unfold csw_view, aview, YP09.mbyte, mrestrict, mrd, wa.
  rewrite (cls_vis W x Hx). reflexivity.
Qed.

Lemma cls_tw_raw : forall (W : world tfibsegs) (m : word -> option byte) Bw,
  tw_at TMAP_A (aview tfibsegs (w_H W) m) Bw -> tw_at TMAP_A (csw_view m) Bw.
Proof.
  intros W m Bw H. apply (tw_kept TMAP_A (aview tfibsegs (w_H W) m) (csw_view m) Bw H).
  intros x Hx. symmetry. exact (cls_view_eq W m x Hx).
Qed.

Lemma cls_tw_av : forall (W : world tfibsegs) (m : word -> option byte) Bw,
  tw_at TMAP_A (csw_view m) Bw -> tw_at TMAP_A (aview tfibsegs (w_H W) m) Bw.
Proof.
  intros W m Bw H. apply (tw_kept TMAP_A (csw_view m) (aview tfibsegs (w_H W) m) Bw H).
  intros x Hx. exact (cls_view_eq W m x Hx).
Qed.

End cjw.

(* ------------------------------------------------------------------ *)
(* the G journal across one run of the walk, and across the bcmp call  *)
(* ------------------------------------------------------------------ *)

Section cjj. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis HGX : gx_ok tfibsegs B TGJ.G_HARNESS.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head tfibsegs B).

(* The G journal after a run of the walk's own code: the run wrote only bytes of Wr, each of them a byte the
   journal may change (an awr_byte that is present, or a byte of G), and it only added bytes. *)
Lemma cls_jexec :
  forall STK sp0 FP ly S (W0 : world tfibsegs) mem0 md0 own lyc Sc (W : world tfibsegs)
         (m m' : word -> option byte) mdc mdc' k (Wr : Z -> Prop),
  ajournal_gx TGJ.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m mdc k ->
  (forall z : word, ~ Wr (bv_unsigned z) -> m' z = m z) ->
  (forall z : word, m z <> None -> m' z <> None) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) m a)
     \/ inG TGJ.G_HARNESS a) ->
  ajournal_gx TGJ.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m' mdc' k.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m m' mdc mdc' k Wr HJ Hfr Hgr Hsame HW.
  apply (@ajournal_gx_exec rc tfib_sink_head tfibsegs B LAWS transport_segs_low
           TGJ.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m mdc k m' mdc' Wr HGX HJ).
  - intros z Hz. unfold mrestrict. rewrite (Hfr z Hz). reflexivity.
  - intros z Hz. unfold mrestrict in *. destruct (w_H W z) eqn:E; [exact Hz | exact (Hgr z Hz)].
  - intros z Hh. apply Hfr. intros HWz.
    destruct (HW (bv_unsigned z) HWz) as [(_ & Hp) | Hg].
    + destruct Hp as (Hhid & _). rewrite Z_to_bv_bv_unsigned in Hhid. rewrite Hhid in Hh. discriminate.
    + pose proof (proj1 (HGX (bv_unsigned z) Hg)) as Hi.
      rewrite (hidden_not_img tfibsegs W z Hi) in Hh. discriminate.
  - exact Hsame.
  - intros a Ha. destruct (HW a Ha) as [(Hw & _) | Hg];
      [left; split; [exact Hw | lia] | right; left; exact Hg].
Qed.

(* The bcmp wrapper's contract, read at the walk's own G journal (TransportGCg.v gx_call_leaf over YCbq.v
   aj_bcmp_at): the journal and every byte outside the wrapper's own stack window are kept, and a0 is 0 exactly
   when the two ranges hold the same bytes. *)
Lemma cls_bcmp :
  forall (STK sp0 : Z) FP ly S (W0 : world tfibsegs) mem0 md0 own lyc Sc (W : world tfibsegs)
         (memT : word -> option byte) mdc k (regsT : bvmap 5 word) (x y n o : Z) (raw : word),
  @abcmp_realizes fx rc tfibsegs B (transport_sigma TS___interceptor_trampoline_bcmp) ->
  ajournal_gx TGJ.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k ->
  YK11.getr regsT 10 = w64 x -> YK11.getr regsT 11 = w64 y -> YK11.getr regsT 12 = w64 n ->
  0 <= n < 2 ^ 32 -> 0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  src_ok tfibsegs W regsT memT x n -> src_ok tfibsegs W regsT memT y n ->
  (forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  (forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  amem_range x n -> amem_range y n ->
  range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) x n) ->
  range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF y n ->
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) y n) ->
  SRr tfibsegs W
    (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp)) memT
              (YK11.seg_rom tfibsegs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (@YK11.mkst fx regs2 raw mem2 (YK11.seg_rom tfibsegs)) md2 /\
       ajournal_gx TGJ.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       (exists v : word, aregs_preserved regsT regs2 /\ YK11.getr regs2 10 = v /\
          (v = w64 0 <-> forall i, 0 <= i < n ->
             aview tfibsegs (w_H W) memT (x + i) = aview tfibsegs (w_H W) memT (y + i)) /\
          (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
             aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
          (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a))).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k regsT x y n o raw
    AM HJ H10 H11 H12 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw
    Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
  apply (@gx_call_leaf fx rc tfib_sink_head tfibsegs B TGJ.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own
           lyc Sc W memT mdc k _ raw _ HJ).
  intros memS HJi.
  eapply SRr_mono.
  { exact (@aj_bcmp_at fx rc tfib_sink_head tfibsegs B LAWS transport_segs_low
             (transport_sigma TS___interceptor_trampoline_bcmp) AM W regsT memT STK sp0 FP ly S W0 memS md0 own
             lyc Sc mdc k x y n o raw HJi H10 H11 H12 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw
             Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & Hc & HJ2 & HP & Hres & Hcmp & Hfr2 & Hpres2).
  split; [reflexivity|]. exists regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|].
  exists v. split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr2 | exact Hpres2].
Qed.

End cjj.

(* ------------------------------------------------------------------ *)
(* what the walk keeps, at the memory the out cell is read back in     *)
(* ------------------------------------------------------------------ *)

Section cjk. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis HGX : gx_ok tfibsegs B TGJ.G_HARNESS.

Lemma cls_gover_mem : forall outs (ma mb : word -> option byte) a, 0 <= a < 2 ^ 64 ->
  gover outs ma mb (Z_to_bv 64 a) = if inGb outs a then mb (Z_to_bv 64 a) else ma (Z_to_bv 64 a).
Proof.
  intros outs ma mb a Ha. unfold gover.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma cls_gover_in : forall outs (H : word -> bool) (ma mb : word -> option byte) a,
  0 <= a < 2 ^ 64 -> inG outs a -> aview tfibsegs H (gover outs ma mb) a = aview tfibsegs H mb a.
Proof.
  intros outs H ma mb a Ha Hin. apply aview_eq_of. unfold mrestrict.
  rewrite (cls_gover_mem outs ma mb a Ha), (proj2 (inGb_spec outs a) Hin). reflexivity.
Qed.

(* every byte the walk stores that is not the caller's int at dp is a byte of a harness global *)
Lemma cls_wr_G : forall dp a, cls_wr dp a -> ~ (dp <= a < dp + 4) -> inG TGJ.G_HARNESS a.
Proof.
  intros dp a Hw Hn. unfold inG. apply Exists_exists.
  destruct Hw as [(s & Hs & Hf) | [Hf | [Hf | Hf]]].
  - exists (TA_g_cmd, TWJ.SZ_g_cmd). split.
    + exact (TMAP_A_in_G _ _ _ TMAP_A_g_cmd).
    + unfold twa_fld, TWJ.A_Cmd_st, TWJ.OFF_g_cmd, TA_g_cmd, TWJ.SZ_g_cmd in *.
      unfold TCJ.CMDS_MAX in Hs. unfold in_zr. cbn [fst snd]. lia.
  - exists (TA_g_q, TWJ.SZ_g_q). split.
    + exact (TMAP_A_in_G _ _ _ TMAP_A_g_q).
    + unfold twa_fld, TWJ.OFF_g_q, TA_g_q, TWJ.SZ_g_q in *. unfold in_zr. cbn [fst snd]. lia.
  - exists (TA_g_nq, TWJ.SZ_g_nq). split.
    + exact (TMAP_A_in_G _ _ _ TMAP_A_g_nq).
    + unfold twa_fld, TWJ.OFF_g_nq, TA_g_nq, TWJ.SZ_g_nq in *. unfold in_zr. cbn [fst snd]. lia.
  - exfalso. exact (Hn Hf).
Qed.

Lemma cls_wr_low : forall dp a, cls_wr dp a -> ~ (dp <= a < dp + 4) -> 0 <= a < kLowMemEnd.
Proof.
  intros dp a Hw Hn. apply transport_segs_low. exact (proj1 (HGX a (cls_wr_G dp a Hw Hn))).
Qed.

(* The walk's own kept fact, at the memory TransportGCg.v transport_cg_post_out reads: the four bytes at dp put
   back as they were at the call, every other byte the walk's runs left. *)
Lemma cls_close_kept :
  forall lyc Sc (W : world tfibsegs) (memc : word -> option byte) mdc (mF : word -> option byte)
         (dp slo shi : Z),
  @AR rc tfibsegs B lyc Sc W memc mdc ->
  @YM05.alloc_ceiling rc <= slo -> shi <= 2 ^ 64 ->
  (forall a, slo <= a < shi -> apresent (w_H W) memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ cls_wr dp a ->
     aview tfibsegs (w_H W) mF a = aview tfibsegs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mF a) ->
  acall_kept_g tfibsegs B TGJ.G_HARNESS lyc Sc W memc W (gover [(dp, 4)] mF memc) slo shi (cls_wr dp).
Proof.
  intros lyc Sc W memc mdc mF dp slo shi HAR Hce Hshi Hpres KA GA.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
  assert (HdpG : forall a, 0 <= a < 2 ^ 64 -> inG [(dp, 4)] a -> dp <= a < dp + 4).
  { intros a Ha Hin. apply Exists_exists in Hin as (r & Hr & Hx). cbn [In] in Hr.
    destruct Hr as [<- | []]. unfold in_zr in Hx. cbn [fst snd] in Hx. lia. }
  assert (HdpG' : forall a, dp <= a < dp + 4 -> inG [(dp, 4)] a).
  { intros a Ha. unfold inG. apply Exists_exists. exists (dp, 4). split; [left; reflexivity|].
    unfold in_zr. cbn [fst snd]. lia. }
  apply (@dk_kept_step_g rc tfibsegs B LAWS transport_segs_low TGJ.G_HARNESS lyc Sc W memc mdc memc
           (gover [(dp, 4)] mF memc) slo shi (cls_wr dp)
           (fun a => (slo <= a < shi) \/ (cls_wr dp a /\ ~ (dp <= a < dp + 4))) HAR).
  - apply dk_kept_refl_g. exact Hpres.
  - intros a Ha Hn.
    destruct (Z_le_dec dp a) as [H1|H1]; [destruct (Z_lt_dec a (dp + 4)) as [H2|H2]|].
    + rewrite (cls_gover_in [(dp, 4)] (w_H W) mF memc a Ha (HdpG' a ltac:(lia))). reflexivity.
    + rewrite (gover_out_aview tfibsegs [(dp, 4)] (w_H W) mF memc a Ha
                 ltac:(intros Hin; pose proof (HdpG a Ha Hin); lia)).
      apply KA; [exact Ha | intros Hx; apply Hn; left; exact Hx
                | intros Hx; apply Hn; right; split; [exact Hx | lia]].
    + rewrite (gover_out_aview tfibsegs [(dp, 4)] (w_H W) mF memc a Ha
                 ltac:(intros Hin; pose proof (HdpG a Ha Hin); lia)).
      apply KA; [exact Ha | intros Hx; apply Hn; left; exact Hx
                | intros Hx; apply Hn; right; split; [exact Hx | lia]].
  - intros a (Hh & b & Hb). split; [exact Hh|].
    unfold gover. destruct (inGb [(dp, 4)] (bv_unsigned (Z_to_bv 64 a))).
    + exists b. exact Hb.
    + destruct (GA a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'.
  - intros a [Hw | (Hw & Hn)] Hac.
    + exact Hw.
    + exfalso. pose proof (cls_wr_low dp a Hw Hn) as Hl. unfold kLowMemEnd in Hl. lia.
  - intros b m i Hb Hi [Hw | (Hw & _)]; [|exact Hw]. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a [Hw | (Hw & Hn)] Hi HnG _ _.
    + pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
    + exact (HnG (cls_wr_G dp a Hw Hn)).
  - intros cid pos a Hin Hr [Hw | (Hw & _)]; [|exact Hw]. exfalso.
    destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8)
      by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

End cjk.
