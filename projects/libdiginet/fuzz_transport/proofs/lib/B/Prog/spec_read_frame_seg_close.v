(* spec_read_frame_seg_close: the close of the walk of spec_read_frame (image B; lib/B/Prog/spec_read_frame_cg.v):
   from what run 2 leaves at the `ret` to the statement's post transport_srf_post, that is TransportGCg.v
   transport_cg_post_out with the one out cell [(fp, 80)].
     srf_out_img  the struct's bytes are not image bytes (each is an awr_byte of the caller's journal: the stack
                  window, a block, or one of the journal's own side-stack frames or its shadow).
     srf_close    the post. The journal: W_journalG.v ajournal_gx_exec from the memory the memset returned, the written
                  range the struct (each byte an awr_byte, transport_twr_ok_g with the struct outside G). The kept
                  bytes: acall_kept_g is read at gover [(fp, 80)] m' memc, the memory with the struct's bytes put back as
                  they were at the call, so every byte outside the call's stack window is the call's (the struct by
                  gover, the rest by run 2's munch, the memset's kept clause and run 1's munch, given as KA). X: the
                  code in a0, the struct's bytes sf_bytes b f (TransportFevt.v decode_bytes_garr8), G kept (G lies
                  below kLowMemEnd, outside the window and outside the struct). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YP03.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCgRun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require TransportFevt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import spec_read_frame_cg.
Import ListNotations.
Open Scope Z_scope.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section Close.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation G := TG.G_HARNESS_B.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok segs B G.

Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (b fp : Z).

Hypothesis HJ : @W_journalG.ajournal_gx rc tfib_sink_head segs B G 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis HWLO : sp0 - STK <= spZ regs - SRF_STK.
Hypothesis HWHI : spZ regs <= sp0.
Hypothesis HTWR : transport_twr_ok_g segs B G STK sp0 FP ly S lyc Sc own W memc (spZ regs) fp SRF_SIZE.
Hypothesis HRDP : decode_rd_ok W memc fp SRF_SIZE.
Hypothesis HOWP : decode_off_win regs SRF_STK fp SRF_SIZE.
Hypothesis HNG : forall x, fp <= x < fp + SRF_SIZE -> ~ inG G x.

(* The donor journal at the call: AR, the journal's own frames among the call state's, the stack. *)
Lemma srf_donor :
  AR segs B lyc Sc W memc mdc /\ frames Sc = own ++ frames S /\ astk_ok STK ly sp0 /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a).
Proof.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  destruct HJi as (HAR & _ & _ & _ & _ & HFR & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  split; [exact HAR|]. split; [exact HFR|]. split; [exact Hstk | exact Hpres].
Qed.

(* The struct's bytes are not image bytes. *)
Lemma srf_out_img : forall a, fp <= a < fp + SRF_SIZE -> ~ in_img segs a.
Proof.
  intros a Ha Hi.
  destruct srf_donor as (HAR & HFR & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (decode_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  destruct (HTWR a Ha) as [(Haw & _) | HGa]; [| exact (HNG a Ha HGa)].
  destruct Haw as [Hs | [(_ & bq & nq & Hb & Hr) | [(bq & nq & Hb & _ & Hr) | (cid & pos & Hin & Hr)]]].
  - lia.
  - exact (blk_img segs B LAWS lyc Sc W memc mdc bq nq a HAR Hb Hr Hi).
  - exact (blk_img segs B LAWS lyc Sc W memc mdc bq nq a HAR Hb Hr Hi).
  - assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite HFR; apply in_or_app; left; exact Hin).
    pose proof (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin') as (F1 & _).
    destruct Hr as [Hr | Hr]; unfold in_zr in Hr; cbn [fst snd] in Hr.
    + exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin' Hr Hi).
    + assert (0 <= frame_addr lyc cid pos / 8) by (apply Z.div_pos; lia).
      unfold shadow_addr, SHADOW_OFF in Hr. lia.
Qed.

Lemma srf_in_out : forall a, ~ inG [(fp, 80)] a <-> ~ (fp <= a < fp + 80).
Proof.
  intros a. split; intros H Hin; apply H.
  - apply inG_cons. left. unfold in_zr. cbn [fst snd]. exact Hin.
  - apply inG_cons in Hin as [Hin | Hin]; [unfold in_zr in Hin; cbn [fst snd] in Hin; exact Hin|].
    exfalso. exact (inG_nil a Hin).
Qed.

(* The post, from what run 2 leaves (its munch, wmono and struct bytes), the journal at the memory mem2 the memset
   returned, and what run 1 and the memset kept (KA, GA) and made present (PF, the struct). *)
Lemma srf_close : forall (mem2 : word -> option byte) (md2 : Model) (m' : word -> option byte) (md' : Model)
    (regs' : bvmap 5 word) (f : DSpec.spec_frame),
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SRF_STK <= a < spZ regs) -> ~ (fp <= a < fp + SRF_SIZE) ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SRF_STK <= a < spZ regs) -> ~ (fp <= a < fp + SRF_SIZE) ->
     apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  (forall a, fp <= a < fp + SRF_SIZE -> apresent (w_H W) mem2 a) ->
  munch [(fp, fp + 80)] mem2 m' -> wmono rsegs mem2 m' -> bytes_at rsegs m' fp (TCt.sf_bytes b f) ->
  same_but_materialized md2 md' -> aregs_preserved regs regs' -> YK11.getr regs' 10 = w64 (DSpec.sf_code f) ->
  SRr segs W (mkCfg (YK11.mkst regs' (YK11.getr regs 1) m' (YK11.seg_rom segs)) md')
    (transport_srf_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b fp f).
Proof.
  intros mem2 md2 m' md' regs' f HJ2 KA GA PF MU WM HB SBM HP H10.
  destruct srf_donor as (HAR & HFR & Hstk & Hpres).
  pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HRDP as (HvP & HraP & HhP & HmP & H0P & H63P).
  pose proof HOWP as OWP. unfold decode_off_win in OWP.
  assert (EW : SRF_STK = 4144) by reflexivity. assert (ES : SRF_SIZE = 80) by reflexivity.
  rewrite EW in *. rewrite ES in *.
  assert (Rsp : 0 <= spZ regs < 2 ^ 64)
    by (unfold spZ; pose proof (bv_unsigned_in_range 64 (YK11.getr regs (Z_to_bv 5 2))) as R; exact R).
  (* the journal at mem2: its stack window is present *)
  assert (Hpres2 : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) mem2 a).
  { destruct HJ2 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
    destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp. }
  (* a byte outside the struct is mem2's at m' *)
  assert (MU' : forall a, 0 <= a < 2 ^ 64 -> ~ (fp <= a < fp + 80) -> m' (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
  { intros a Ha Hn. apply MU. cbn [outside]. rewrite unsigned_lit_small by lia. split; [exact Hn | exact I]. }
  (* every byte outside the call's window is the call's at gover [(fp, 80)] m' memc *)
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 4144 <= a < spZ regs) ->
            aview segs (w_H W) (gover [(fp, 80)] m' memc) a = aview segs (w_H W) memc a).
  { intros a Ha Hw. destruct (Z_lt_le_dec a fp) as [Hl | Hl]; [| destruct (Z_lt_le_dec a (fp + 80)) as [Hh | Hh]].
    - rewrite (gover_out_aview segs [(fp, 80)] _ m' memc a Ha) by (apply srf_in_out; lia).
      rewrite (aview_eq_of segs (w_H W) mem2 m' a) by (unfold mrestrict; rewrite MU' by lia; reflexivity).
      apply KA; [exact Ha | exact Hw | lia].
    - apply aview_eq_of. unfold mrestrict, gover. rewrite unsigned_lit_small by lia.
      replace (inGb [(fp, 80)] a) with true; [reflexivity|].
      symmetry. apply inGb_spec. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
    - rewrite (gover_out_aview segs [(fp, 80)] _ m' memc a Ha) by (apply srf_in_out; lia).
      rewrite (aview_eq_of segs (w_H W) mem2 m' a) by (unfold mrestrict; rewrite MU' by lia; reflexivity).
      apply KA; [exact Ha | exact Hw | lia]. }
  apply SRr_ret. unfold transport_srf_post, transport_cg_post_out. change SRF_SIZE with 80.
  exists lyc, Sc, regs', m', md', 0.
  split; [reflexivity|].
  split; [unfold SRF_EV; lia|].
  split.
  { rewrite Z.add_0_r.
    apply (ajournal_gx_exec segs B LAWS decode_segs_low G 0 [] STK sp0 FP ly S W0 mem0 md0 own
             lyc Sc W mem2 md2 k m' md' (fun a => fp <= a < fp + 80) HGX HJ2).
    - intros x Hx. unfold mrestrict. destruct (w_H W x); [reflexivity|].
      apply MU. cbn [outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold mrestrict in *. destruct (w_H W x) eqn:Eh; [exact Hx|].
      pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rx.
      destruct (Z_lt_le_dec (bv_unsigned x) fp) as [Hl | Hl];
        [rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (fp + 80)) as [Hh | Hh];
        [|rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
      assert (Hw : wview rsegs m' x <> None).
      { refine (WM x _). unfold wview. destruct (mem2 x) as [bb|] eqn:Em;
          [discriminate | exfalso; first [exact (Hx Em) | exact (Hx eq_refl)]]. }
      unfold wview in Hw. destruct (m' x) as [bb|] eqn:Em1; [discriminate|]. exfalso.
      rewrite (find_segment_none rsegs (bv_unsigned x)) in Hw; [exact (Hw eq_refl)|].
      intros Him. exact (srf_out_img (bv_unsigned x) ltac:(unfold SRF_SIZE; lia) Him).
    - intros x Hh. apply MU. cbn [outside]. split; [|exact I]. intros Hx.
      destruct (PF (bv_unsigned x) Hx) as [Hv _]. rewrite Z_to_bv_bv_unsigned in Hv. congruence.
    - exact SBM.
    - intros a Ha. cbv beta in Ha. destruct (HTWR a Ha) as [(Hw & _) | HGa]; [left; split; [exact Hw | lia] |].
      right. left. exact HGa. }
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { split; [|split; [|split; [|split; [|split]]]].
    - intros a Ha Hw. apply KF; [lia | exact Hw].
    - intros bq mq i Hb Hi _.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bq mq HAR Hb) as (_ & H4096 & Hbc & _).
      apply KF; lia.
    - intros a Hi _ _ _. pose proof (decode_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. apply KF; lia.
    - intros cid pos a Hin Hr _.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      assert (Ha : 0 <= a < sp0 - STK).
      { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
        pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
        assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
        pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
        unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
      apply KF; lia.
    - intros a Ha Hw Hpr. destruct (Z_lt_le_dec a fp) as [Hl | Hl]; [| destruct (Z_lt_le_dec a (fp + 80)) as [Hh | Hh]].
      + destruct (GA a ltac:(lia) Hw ltac:(lia) Hpr) as [Hv [bb Hbb]]. split; [exact Hv|]. exists bb.
        rewrite (gover_out_mem [(fp, 80)] m' memc a ltac:(lia)) by (apply srf_in_out; lia).
        rewrite MU' by lia. exact Hbb.
      + destruct Hpr as [Hv [bb Hbb]]. split; [exact Hv|]. exists bb. unfold gover.
        rewrite unsigned_lit_small by lia.
        replace (inGb [(fp, 80)] a) with true; [exact Hbb|].
        symmetry. apply inGb_spec. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
      + destruct (GA a ltac:(lia) Hw ltac:(lia) Hpr) as [Hv [bb Hbb]]. split; [exact Hv|]. exists bb.
        rewrite (gover_out_mem [(fp, 80)] m' memc a ltac:(lia)) by (apply srf_in_out; lia).
        rewrite MU' by lia. exact Hbb.
    - intros a Ha. destruct (Hpres2 a ltac:(lia)) as [Hv [bb Hbb]]. split; [exact Hv|]. exists bb.
      rewrite (gover_out_mem [(fp, 80)] m' memc a ltac:(lia)) by (apply srf_in_out; destruct OWP; lia).
      rewrite MU' by (destruct OWP; lia). exact Hbb. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  split; [exact H10|].
  split.
  { apply (TransportFevt.decode_bytes_garr8 (w_H W) m' fp (TCt.sf_bytes b f)); [|exact HB].
    intros j Hj. pose proof (srf_size_bytes b f) as Hl. unfold SRF_SIZE in Hl.
    destruct (PF (fp + Z.of_nat j) ltac:(lia)) as [Hv _]. exact Hv. }
  intros a Ha. pose proof (inG_low segs B decode_segs_low G a HGX Ha) as Hl. unfold kLowMemEnd in Hl.
  assert (Hn : ~ (fp <= a < fp + 80)) by (intros Hr; exact (HNG a ltac:(lia) Ha)).
  rewrite (aview_eq_of segs (w_H W) mem2 m' a) by (unfold mrestrict; rewrite MU' by lia; reflexivity).
  apply KA; [lia | lia | exact Hn].
Qed.

End Close.
