(* m_rx_seg_glue: the two ends of the image-B walk of m_rx (lib/B/Prog/m_rx_cg.v) around its segments, image B's
   twin of lib/A/Prog/m_rx_seg_glue.v.
   - mrx_inner_init: the caller's G journal at m_rx's entry gives the inner G journal of the kit
     (lib/B/Prog/m_rx_seg_kit.v), started at the call state with window MRX_STK below the entry sp, no footprint, no
     frame (YCbq.v ajournal_sub_init on the donor journal inside the caller's, TransportGCg.v gx_open / gx_pack0).
   - mrx_kept_g_of_inner: what the inner journal keeps at the return, as TransportGCg.v acall_kept_g (the donor
     journal's clauses, read at the call memory outside G, where its start memory agrees with it).
   - mrx_close: the inner post (kit mrx_ipost) gives the statement's post transport_mrx_post: the caller's journal at
     the return (W_journalG.v ajournal_gx_sub), the kept bytes (mrx_kept_g_of_inner), no event, no charge.
   - mrx_top_of_entry: the statement's contract at TB_m_rx from the walk from the entry. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YP03.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg m_rx_cg m_rx_seg_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section glue. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis HGX : gx_ok tfibsegs B TG.G_HARNESS_B.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The inner journal at the entry. *)
Lemma mrx_inner_init : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k sp1,
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp1 mod 16 = 0 -> sp0 - STK <= sp1 - MRX_STK -> sp1 <= sp0 ->
  ajournal_gx TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp1 HJ H16 Hlo Hhi.
destruct (gx_open segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as (memS & HJi & _ & HSTK).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & _) & _).
assert (EM : MRX_STK = 8384) by reflexivity.
pose proof (ajournal_sub_init segs B STK sp0 FP ly S W0 memS md0 own lyc Sc W memc mdc k MRX_STK sp1 [] (sp1 - sp0)
  HJi ltac:(lia) ltac:(rewrite Zminus_mod, H16, Hal16; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as HJ1.
exact (gx_pack0 segs B TG.G_HARNESS_B MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0 memc ltac:(lia) HJ1
  (gagree_refl TG.G_HARNESS_B (w_H W) memc)).
Qed.

(* A byte outside G is the same at the inner journal's start memory and at the call memory. *)
Lemma mrx_out_G : forall (W : world segs) memc memS a, gagree TG.G_HARNESS_B (w_H W) memc memS ->
  0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> aview segs (w_H W) memS a = aview segs (w_H W) memc a.
Proof.
intros W memc memS a Hag Ha Hn. apply (aview_gagree segs TG.G_HARNESS_B _ _ _ a Hag).
rewrite YP03.unsigned_lit_small by lia. apply inGb_false. exact Hn.
Qed.

(* What the inner journal keeps, from the call memory to the return. *)
Lemma mrx_kept_g_of_inner : forall stk sp1 lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 k1
    (E : Z -> Prop),
  ajournal_gx TG.G_HARNESS_B 0 [] stk sp1 [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
  @AR rc segs B lyc Sc W memc mdc ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (sp1 - stk) sp1 E.
Proof.
intros stk sp1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 E HJ HAR Hbl.
destruct (gx_open segs B TG.G_HARNESS_B stk sp1 [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 HJ)
  as (memS & HJi & Hag & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (GLOW : forall a, inG TG.G_HARNESS_B a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transportb_segs_low a (proj1 (HGX a Ha)))).
assert (NI : forall a, ~ in_img segs a -> ~ inG TG.G_HARNESS_B a) by (intros a Hi Hg; exact (Hi (proj1 (HGX a Hg)))).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite (G1 a Ha Hw). apply (mrx_out_G W memc memS a Hag ltac:(lia)).
  intros Hg. pose proof (GLOW a Hg). unfold kLowMemEnd in *. lia.
- intros b m i Hb Hi Hn.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
  rewrite (G2 b m i Hb (Hbl b m Hb) Hi) by (intros Hf; destruct Hf as (rg & Hrg & _); exact Hrg).
  apply (mrx_out_G W memc memS (b + i) Hag ltac:(lia)).
  apply NI. exact (blk_img segs B LAWS lyc Sc W memc mdc b m (b + i) HAR Hb ltac:(lia)).
- intros a Hi HnG Hno He. pose proof (transportb_segs_low a Hi) as Hl.
  rewrite (G3 a Hi Hno He (fp_spares_closed [] a sink_closed_nil)).
  exact (mrx_out_G W memc memS a Hag ltac:(unfold kLowMemEnd in Hl; lia) HnG).
- intros cid pos a Hin Hr Hn.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  rewrite (G4 cid pos a Hin Hr) by (intros Hf; destruct Hf as (rg & Hrg & _); exact Hrg).
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
  + apply (mrx_out_G W memc memS a Hag ltac:(lia)).
    apply NI. exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hr).
  + pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd.
    apply (mrx_out_G W memc memS a Hag ltac:(lia)).
    intros Hg. pose proof (GLOW a Hg). unfold kLowMemEnd in *. lia.
- intros a Ha Hw Hp.
  apply (apresent_transfer segs (w_H W) (w_H W2) memc mem2 a ltac:(lia)).
  + intros Him. pose proof (transportb_segs_low a Him). unfold kLowMemEnd in *. lia.
  + rewrite (G1 a Ha Hw). apply (mrx_out_G W memc memS a Hag ltac:(lia)).
    intros Hg. pose proof (GLOW a Hg). unfold kLowMemEnd in *. lia.
  + exact Hp.
- exact Hpres.
Qed.

(* The statement's post from the inner post. *)
Lemma mrx_close : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) Bw' r (W2 : world segs) c2,
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= spZ regs - MRX_STK -> spZ regs <= sp0 ->
  @mrx_ipost fx rc B MT (spZ regs) regs lyc Sc W memc mdc Bw' r W2 c2 ->
  @transport_mrx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw' r W2 c2.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw' r W2 c2 HJ Hlo Hhi
  (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJi & HP & Hfr & Hperm & HMO & H10 & Htw).
pose proof HJ as (_ & _ & (memS0 & HJd & _) & _). rewrite !Z.add_0_r in HJd.
pose proof HJd as (HAR & _).
unfold transport_mrx_post, transport_cg_post.
exists ly2, S2, regs2, mem2, md2, 0.
split; [exact Hc|]. split; [unfold MRX_EV; lia|].
split.
{ pose proof (ajournal_gx_sub segs B LAWS transportb_segs_low TG.G_HARNESS_B STK sp0 0 [] FP ly S W0 mem0 md0 own lyc Sc
    W memc mdc k MRX_STK (spZ regs) 0 [] [] [] ly2 S2 W2 mem2 md2 0 HJ HJi Hlo Hhi ltac:(lia)
    ltac:(intros a Ha; destruct Ha as (rg & Hrg & _); destruct Hrg) HGX
    ltac:(intros a Ha; destruct Ha as (rg & Hrg & _); destruct Hrg)) as HJ2.
  cbn [app] in HJ2. exact HJ2. }
split; [exact HP|]. split; [exact Hfr|]. split; [exact Hperm|].
split.
{ apply (mrx_kept_g_of_inner MRX_STK (spZ regs) lyc Sc W memc mdc ly2 S2 W2 mem2 md2 0 mrx_wr HJi HAR).
  intros b m Hb. exact (Permutation_in _ (Permutation_sym Hperm) Hb). }
split; [exact HMO|]. split; [exact H10 | exact Htw].
Qed.

(* The statement's contract at TB_m_rx from the walk from the entry at every entry (the segments' chain). *)
Lemma mrx_top_of_entry :
  (forall sp1 regs0 lyc Sc (W : world segs) memc mdc fr n Bw' r,
     mrx_static B sp1 regs0 lyc Sc W memc mdc fr n ->
     forall Bw, @mrx_K_entry fx rc B MT sp1 regs0 lyc Sc W memc mdc fr n Bw Bw' r) ->
  @transport_m_rx_cg fx rc B MT (transportb_sigma TB_m_rx).
Proof.
intros CHAIN.
unfold transport_m_rx_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fr n r Bw Bw'
  HJ Hra Hra4 Hgp Htp H10 H11 Hsp16 Hlo Hhi HFR Hfn HAP HROV Htw Hm Hev.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HFR as (Hfa & Hgarr & Hsrc & Hoff).
assert (EM : MRX_STK = 8384) by reflexivity.
assert (HST : mrx_static B (spZ regs) regs lyc Sc W memc mdc fr n).
{ unfold mrx_static.
  split; [reflexivity|]. split; [exact Hsp16|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hgp|]. split; [exact Htp|].
  split; [exact H10|]. split; [exact H11|]. split; [exact Hfa|]. split; [exact Hfn|].
  split.
  { destruct (mrx_m_n _ _ _ _ _ _ Hm) as [Hn0 Hnl].
    destruct (Z.eq_dec (mlen fr) 0) as [E0|E0]; [rewrite E0; lia|].
    assert (Hpos : 0 < mlen fr) by (unfold AK.mlen in *; lia).
    destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc _ _ HAR Hsrc Hpos) as [P|P]; unfold AK.mlen; lia. }
  split; [exact Hsrc|]. split; [exact Hoff|]. split; [exact HAP|].
  split; [unfold MRX_EV in Hev; lia | exact HAR]. }
pose proof (mrx_inner_init STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (spZ regs) HJ Hsp16 Hlo Hhi) as HJI.
pose proof (CHAIN (spZ regs) regs lyc Sc W memc mdc fr n Bw' r HST Bw HJI Hgarr HROV Htw Hm) as HW.
eapply SRr_mono; [exact HW|].
intros W2 c2 _ HQ.
exact (mrx_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw' r W2 c2 HJ Hlo Hhi HQ).
Qed.

End glue.
