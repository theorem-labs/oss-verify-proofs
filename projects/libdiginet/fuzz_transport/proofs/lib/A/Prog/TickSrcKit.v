(* TickSrcKit: two lemmas on lib/A/Prog/DgnTransportCg.v trans_src_ok in the form the image-A tick walk's pieces use,
   for a callee that reads a range of the caller's own side-stack frame, or the current heap frame while that frame is
   on top. This file is the only one of those pieces that builds trans_src_ok.
   - trans_src_ok_fake: trans_src_ok of a range inside a frame of the state (the fake-frame case,
     decode_in_fake) whose bytes are readable (decode_rd_ok). It stands in for a kit lemma DgnTransportCg.v does not
     have: the kit states the G case only (trans_src_ok_G_range).
   - trans_tframe_at_top: check_state_data_cg.v trans_tframe_at of the current heap frame TF, as the caller's entry
     states it at its window STKc, carried to a later state of the same G journal whose frames are the entry's with one
     frame on top (the caller's own) and whose blocks are the entry's, for a callee window K inside the entry's. What
     the walk kept since the entry is acall_kept_g and gx_kept_ex over its written range E, E lies below the shadow
     band, and TF's bytes are apart from E. DgnTransportCg.v's carry lemmas (trans_src_ok_kept_ge0,
     trans_src_ok_acall_ge0, trans_src_ok_acall_g_ge0) ask frames S2 = frames Sc; this is the case of
     TransportGNotice.v trans_tframe_at_kept_gx at the caller's own layout and world, with the bound on E as the
     pieces state it. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg CanKit TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section k. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.

(* trans_src_ok of a range inside a frame of the state whose bytes are readable: its fake-frame case. *)
Lemma trans_src_ok_fake : forall lyc Sc (W : world segs) memc q n,
  decode_in_fake lyc Sc q n -> decode_rd_ok W memc q n -> trans_src_ok B lyc Sc W memc q n.
Proof. intros lyc Sc W memc q n Hf Hrd. right. split; [left; exact Hf | exact Hrd]. Qed.

(* trans_tframe_at of the current heap frame TF, from the caller's entry (window STKc) to a later state of the same G
   journal with the caller's own frame on top, for a callee window K inside the entry's (header). *)
Lemma trans_tframe_at_top : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc S2 memN mdN (regs regsN : bvmap 5 word) (TF : option TI.tframe)
    (E : Z -> Prop) STKc K cid pos,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B lyc S2 W memN mdN ->
  frames S2 = (cid, pos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
  ly_stk_lo lyc < ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W memN (spZ regs - STKc) (spZ regs) E ->
  gx_kept_ex segs TG.G_HARNESS E W memc W memN ->
  (forall x, E x -> forall fr, TF = Some fr ->
     ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)))) ->
  (forall a, E a -> a < SHADOW_OFF) ->
  spZ regs - STKc <= spZ regsN - K -> spZ regsN <= spZ regs ->
  trans_tframe_at B lyc Sc W memc regs STKc TF ->
  trans_tframe_at B lyc S2 W memN regsN K TF.
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc S2 memN mdN regs regsN TF E STKc K cid pos HARc HAR2 Hfr Hbl Hstk
    HK HGK Hap HElo Hw1 Hw2 HT.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (trans_tframe_at_kept_gx B LAWS HRU HRE lyc Sc W memc mdc lyc S2 W memN mdN E regs regsN STKc K TF
    HARc HAR2).
  - intros bm Hbm. rewrite Hbl. exact Hbm.
  - intros f Hf. rewrite Hfr. right. exact Hf.
  - intros c p. reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Hstk.
  - exact HK.
  - exact HGK.
  - intros fr Hfr0 a Ha Ea. exact (Hap a Ea fr Hfr0 Ha).
  - intros a Ha Ea. pose proof (HElo a Ea) as Hl. unfold SHADOW_OFF in Hl. lia.
  - exact Hw1.
  - exact Hw2.
  - exact HT.
Qed.

End k.
