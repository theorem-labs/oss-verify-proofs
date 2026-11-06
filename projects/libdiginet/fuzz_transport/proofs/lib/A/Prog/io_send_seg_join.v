(* io_send_seg_join: the back half of the image-A walk of io_send, joined: from the frame-in-flight cut (0x83338 =
   transport_text + IOS_FLY) through lib/A/Prog/io_send_seg_fly.v ios_fly_seg (the six stores into M.fly and
   __asan_memcpy) and lib/A/Prog/io_send_seg_epi.v ios_epi (the epilogue) to the walk's post (io_send_seg_cut.v
   ios_post), at the world ios_fly frame Bx.

   The cut facts at IOS_FLY are lib/A/Prog/io_send_seg_tail.v ios_tail_at (the common currency of the DATA tail's
   exits and of the E2 arm's), with the registers the tail reads. The glue:
   - ios_len_lt32: the frame is shorter than 2^32 bytes (check_sent_frame's length test makes it at most
     30 + body_len, and body_len = numbytes - 16 with numbytes a 16-bit field), which ios_fly_seg takes;
   - f.send at sp + 40 and its range come from the struct (io_send_seg_tail.v ios_tail_send);
   - ios_saved after the copy: the nine saved words lie in io_send's own frame, above the copy's ESTACK window and
     far above M, so the copy's kept fact keeps them (ios_saved_kept). *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg check_latest_sent_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  io_send_segs io_send_seg_frm io_send_seg_cut io_send_seg_tail io_send_seg_fly io_send_seg_epi.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_sent_frame's length test: len = max (60, 30 + body_len), body_len = numbytes - 16 < 2^16. *)
Lemma ios_len_lt32 : forall Bm frame B',
  TC.check_sent_frame_m Bm frame = Some (B', tt) -> Z.of_nat (length frame) < 2 ^ 32.
Proof.
  intros Bm frame B' H.
  pose proof (ios_sf_code _ _ _ H) as HOK.
  destruct (ios_fields frame HOK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fblen & _).
  pose proof (DSpec.be16_range frame 14) as Rnb.
  unfold TC.check_sent_frame_m in H. cbv zeta in H.
  match type of H with context [if ?c then None else _] => destruct c eqn:C1 end;
    cbv beta iota in H; [discriminate H|].
  match type of H with context [if ?c then None else _] => destruct c eqn:C2 end;
    cbv beta iota in H; [discriminate H|].
  apply orb_false_iff in C2. destruct C2 as [C2 _].
  apply orb_false_iff in C2. destruct C2 as [C2 _].
  apply negb_false_iff, Z.eqb_eq in C2. rewrite C2.
  rewrite Fblen. unfold DSpec.fr_body_len, DSpec.fr_numbytes.
  destruct (DSpec.SPEC_BODY_AT + (DSpec.be16 frame 14 - 16) <? TC.SPEC_MIN_FRAME);
    unfold TC.SPEC_MIN_FRAME, DSpec.SPEC_BODY_AT in *; lia.
Qed.

Section join. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

(* The nine saved words, carried across a stretch that keeps every byte of io_send's frame above sp - 160. *)
Lemma ios_saved_kept : forall (W2 : world segs) (m2 m3 : word -> option byte) (regs : bvmap 5 word),
  (forall a, spZ regs - IOSEND_FRAME <= a < spZ regs -> aview segs (w_H W2) m3 a = aview segs (w_H W2) m2 a) ->
  ios_saved W2 m2 regs -> ios_saved W2 m3 regs.
Proof.
  intros W2 m2 m3 regs HK HS. unfold ios_saved in *.
  rewrite Forall_forall in HS |- *. intros o Ho. rewrite <- (HS o Ho).
  apply rdword_ext. intros i Hi. apply HK.
  unfold IOS_SAVED in Ho. unfold IOSEND_FRAME.
  cbn [In] in Ho.
  repeat (destruct Ho as [Ho | Ho]; [subst o; cbn [fst]; lia |]). destruct Ho.
Qed.

Lemma ios_fly_post : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) p frame Bw Bx ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  ios_tail_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 mem2 md2 Bx ->
  60 <= Z.of_nat (length frame) -> Z.of_nat (length frame) < 2 ^ 32 ->
  YK11.getr regs2 2 = w64 (spZ regs - IOSEND_FRAME) ->
  YK11.getr regs2 3 = YK11.getr regs 3 -> YK11.getr regs2 4 = YK11.getr regs 4 ->
  YK11.getr regs2 8 = w64 (Z.of_nat (length frame)) -> YK11.getr regs2 9 = w64 p ->
  YK11.getr regs2 19 = w64 (TW.g_fail_next Bw) ->
  YK11.getr regs2 21 = w64 (DSpec.sf_cmd (TC.rf frame)) ->
  (forall r, 24 <= r <= 27 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_FLY) regs2 mem2 md2)
    (ios_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame (ios_fly frame Bx) (ios_ret Bw)).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bx ly2 S2 W2 mem2 md2 regs2
    HL HF HT H60 H32 R2 R3 R4 R8 R9 R19 R21 R24.
  pose proof HL as (HCELLS & HIOC & LAWS & MTL & HGX & HGE & HAI0 & HCSF & HCAF & HCLC & HCIR & HCSW & HCIN &
                    HCLF & HCKD & HCLS & HCLD & HAI1).
  pose proof HF as (HJ & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hlo & Hhi & Hp0 & HG8 & HSRC & HOFF & HFAT &
                    Hfail & HROM & HTW & HFLY & HCMD & HEV).
  pose proof HT as (HC & HSV & HSF & HG8' & HSRC' & HOFF' & HFAT' & HTWx).
  pose proof HC as (HJ2 & Hfr & Hperm & Hmo & HK).
  rewrite Z.add_0_r in HJ2.
  destruct (ios_tail_send B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HT) as [Hsend Vsend].
  apply (ios_fly_seg B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k regs regs2 p frame Bx
           _ HIOC LAWS HGX HAI1 HJ HJ2 HK Hsp16 Hlo Hhi R2).
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R8.
  - exact R9.
  - exact R21.
  - exact Hsend.
  - exact Vsend.
  - lia.
  - exact H32.
  - exact HG8'.
  - exact HSRC'.
  - exact HOFF.
  - exact HFAT.
  - exact HTWx.
  - intros regs3 mem3 md3 HJ3 HK3 HKB HP3 HR3 R38 HTW3.
    assert (CS : forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 19 \/ 24 <= r <= 27 ->
                   YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)).
    { intros r Hr. apply HR3; [unfold acallee_saved; lia | lia]. }
    apply (ios_epi B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw (ios_fly frame Bx)
             ly2 S2 W2 mem3 md3 regs3 HL HF).
    + split; [rewrite Z.add_0_r; exact HJ3|]. split; [exact Hfr|]. split; [exact Hperm|]. split; [exact Hmo|].
      exact HK3.
    + apply (ios_saved_kept W2 mem2 mem3 regs); [|exact HSV].
      intros a Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
      pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
      pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                         (Hs16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
      assert (FL : ios_flen frame <= 1514)
        by (unfold ios_flen, TC.SPEC_MAX_FRAME; destruct (Z.ltb_spec (Z.of_nat (length frame)) 1514); lia).
      rewrite iosend_stk_eq in Hlo.
      assert (Hlow : 0x7fff7f800000 + 4096 <= spZ regs - IOSEND_FRAME).
      { unfold CLS_STK, CLS_FRAME, ESTACK in Hlo. unfold IOSEND_FRAME in *. lia. }
      assert (Hup : spZ regs <= 2 ^ 47) by lia.
      apply HKB; unfold ESTACK, TA_M; unfold IOSEND_FRAME in Ha, Hlow |- *;
        first [ lia | match goal with |- ?g => idtac "IOS_JOIN_FAIL" g end; fail ].
    + exact (eq_trans (CS 2 ltac:(lia)) R2).
    + exact (eq_trans (CS 3 ltac:(lia)) R3).
    + exact (eq_trans (CS 4 ltac:(lia)) R4).
    + exact (eq_trans (CS 19 ltac:(lia)) R19).
    + intros r Hr. rewrite (CS r ltac:(lia)). exact (R24 r Hr).
    + exact HTW3.
Qed.

End join.
