(* io_send_seg_dpost: the DATA arm of the image-B walk of io_send (fuzz_transport.asan-ubsan 41113a03c82f, entry
   0x82ffc = TImgB.v ti_io_send timg_B; the statement is lib/B/Prog/io_send_cg.v), from IOS_DATA (0x83148) to the
   walk's post, composed from the segment statements of lib/B/Prog/io_send_seg_cut.v:
     iod_head_stmt      0x83148 .. 0x83198: body[0], s5, check_inflight_new, g_raw: to IOS_CMDS (s2 = f.ncmds or 0)
                        or to IOS_LOOP;
     ios_loop_stmt      the command count loop, IOS_LOOP .. IOS_CMDS, s2 = the model's cmds;
     iod_mid_stmt       IOS_CMDS .. IOS_KA / IOS_SENT: check_latest_frame and the two stores (the world ios_B5);
     ios_tail_seg_stmt  the tail of both cases, to IOS_FLY at the world ios_B6 frame B5 gives;
     io_send_seg_join.v ios_fly_post_of (ios_fly_seg_stmt, ios_epi_stmt): the frame in flight and the epilogue.
   The model's side is image A's io_send_segs.v ios_arm_data (check_inflight_new_m, the count cmds,
   check_latest_frame_m, B6, Bw' = ios_fly frame B6) and io_send_seg_inv.v ios_cmdinv_B5 (the command-length
   invariant at B5, check_latest_sent's premise). *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  io_send_segs io_send_seg_frm io_send_seg_inv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_seg_cut io_send_seg_join.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* A small non-negative value is its own 32-bit signed wrap. *)
Lemma idp_swrap_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

(* A register of the callee-saved set, kept by a call (aregs_preserved). *)
Lemma idp_apZ : forall (R1 R2 : bvmap 5 word) (r : Z), aregs_preserved R1 R2 -> acallee_saved r ->
  YK11.getr R2 (Z_to_bv 5 r) = YK11.getr R1 (Z_to_bv 5 r).
Proof. intros R1 R2 r HP Hc. exact (HP r Hc). Qed.
Lemma idp_ap : forall (R1 R2 : bvmap 5 word) (r : bv 5), aregs_preserved R1 R2 -> acallee_saved (bv_unsigned r) ->
  YK11.getr R2 r = YK11.getr R1 r.
Proof. intros R1 R2 r HP Hc. pose proof (HP _ Hc) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac idp_cs :=
  unfold acallee_saved;
  repeat (lazymatch goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end);
  lia.

(* The model's answer, read off Some. *)
Lemma idp_some : forall (x y : Z), Some x = Some y -> x = y.
Proof. intros x y H. injection H as H. exact H. Qed.

Section dpost. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

Lemma ios_data_post_of : @iod_head_stmt fx rc B MT -> @ios_loop_stmt fx rc B MT -> @iod_mid_stmt fx rc B MT ->
  @ios_tail_seg_stmt fx rc B MT -> @ios_fly_seg_stmt fx rc B MT -> @ios_epi_stmt fx rc B MT ->
  forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k
    regs p frame Bw Bw' ly3 S3 (W2 : world segs) mem3 md3 regs3,
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
  ios_arm Bw frame = Some (Bw', tt) ->
  DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_DATA ->
  TC.truth (DSpec.sf_retry (TC.rf frame)) = false ->
  ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly3 S3 W2 mem3 md3 regs3 ->
  SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_DATA) regs3 mem3 md3)
    (ios_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame Bw' (ios_ret Bw)).
Proof.
intros HHEAD HLOOP HMID HTAIL HFLY HEPI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw'
  ly3 S3 W2 mem3 md3 regs3 HL HF Hcsf Harm Hcmd Hret HAT.
destruct (ios_arm_data Bw frame Bw' Harm Hcmd Hret) as (HCIN & cmds & HCMDS & HCLF & B6 & HB6 & HBw').
pose proof HF as (HJ & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hlo & Hhi & Hp0 & HG8 & HSRC & HOFF & HFAT &
  Hfail & HROM & HTW & HFLY1 & HCMD & HEV).
pose proof (ios_len60 _ _ _ Hcsf) as H60.
pose proof (ios_len_lt32 _ _ _ Hcsf) as H32.
pose proof (ios_sf_code _ _ _ Hcsf) as HOK.
destruct (ios_fields frame HOK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fncmds & _).
pose proof (DSpec.at8_range frame 29) as Rnc. change (2 ^ 8) with 256 in Rnc.
assert (Hncm : 0 <= DSpec.sf_ncmds (TC.rf frame) < 256) by (rewrite Fncmds; unfold DSpec.fr_ncmds; exact Rnc).
destruct (ios_body_len frame HOK) as (_ & _ & Hbl0 & _).
(* the command-length invariant at B5 *)
assert (HINV5 : forall sx, 0 <= sx < TW.g_ncmd (ios_B5 Bw frame) ->
  TW.Cmd_st (ios_B5 Bw frame) sx = TC.PENDING -> TW.Cmd_len (ios_B5 Bw frame) sx <= DSpec.SPEC_CMD_MAX)
  by exact (ios_cmdinv_B5 Bw (DSpec.sf_send (TC.rf frame)) (tw_len TMAP_B _ _ HTW) HCMD).
(* What the three exits of the head share: IOS_CMDS with s2 = the model's cmds. *)
assert (KCMDS : forall mem4 md4 regs4,
  iod_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly3 S3 W2 mem4 md4 regs4 ->
  YK11.getr regs4 18 = w64 (bv_swrap 32 cmds) -> 0 <= cmds < 2 ^ 32 ->
  SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_CMDS) regs4 mem4 md4)
    (ios_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame Bw' (ios_ret Bw))).
{ intros mem4 md4 regs4 HAT4 R18 Hcr.
  apply (HMID STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw cmds ly3 S3 W2 mem4 md4 regs4 _
           HL HF Hcsf HAT4 R18 Hcr HCLF).
  intros mem5 md5 regs5 pc HT5 Q2 Q3 Q4 Q8 Q9 Q19 Q24 Q18 Hcase.
  apply (HTAIL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly3 S3 W2 mem5 md5 regs5
           (ios_B5 Bw frame) B6 pc _ HL HF HT5 Hcsf Q2 ltac:(rewrite Q3; exact Hgp) ltac:(rewrite Q4; exact Htp)
           Q18 HB6 HINV5 Hcase).
  intros ly6 S6 W6 mem6 md6 regs6 HT6 HPRES.
  rewrite HBw'.
  apply (ios_fly_post_of B MT HFLY HEPI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw B6
           ly6 S6 W6 mem6 md6 regs6 HL HF HT6 H60 H32).
  - rewrite (idp_ap regs5 regs6 2 HPRES ltac:(idp_cs)). exact Q2.
  - rewrite (idp_ap regs5 regs6 3 HPRES ltac:(idp_cs)). exact Q3.
  - rewrite (idp_ap regs5 regs6 4 HPRES ltac:(idp_cs)). exact Q4.
  - rewrite (idp_ap regs5 regs6 8 HPRES ltac:(idp_cs)). exact Q8.
  - rewrite (idp_ap regs5 regs6 9 HPRES ltac:(idp_cs)). exact Q9.
  - rewrite (idp_ap regs5 regs6 19 HPRES ltac:(idp_cs)). exact Q19.
  - intros rr Hrr. rewrite (idp_apZ regs5 regs6 rr HPRES ltac:(unfold acallee_saved; lia)). exact (Q24 rr Hrr). }
apply (HHEAD STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly3 S3 W2 mem3 md3 regs3 _
         HL HF Hcsf Hcmd Hret HCIN HAT).
- (* g_raw <> 0 or the keepalive flag: the model's cmds is f.ncmds *)
  intros mem4 md4 regs4 HAT4 R18 Hcase.
  assert (Ecm : DSpec.sf_ncmds (TC.rf frame) = cmds).
  { assert (Hcond : (negb (TC.truth (TW.g_raw (ios_B0 Bw))) && negb (ios_ka frame))%bool = false)
      by (destruct Hcase as [Ht|Hk]; [rewrite Ht | rewrite Hk, Bool.andb_false_r]; reflexivity).
    rewrite Hcond in HCMDS. exact (idp_some _ _ HCMDS). }
  apply (KCMDS mem4 md4 regs4 HAT4); [rewrite <- Ecm, idp_swrap_small by lia; exact R18 | rewrite <- Ecm; lia].
- (* body_len = 0: the loop's answer is 0 *)
  intros mem4 md4 regs4 HAT4 R18 Ht Hk Hb0.
  assert (Ecm : 0 = cmds).
  { assert (Hcond : (negb (TC.truth (TW.g_raw (ios_B0 Bw))) && negb (ios_ka frame))%bool = true)
      by (rewrite Ht, Hk; reflexivity).
    rewrite Hcond, Hb0 in HCMDS. exact (idp_some _ _ HCMDS). }
  apply (KCMDS mem4 md4 regs4 HAT4); [rewrite <- Ecm, idp_swrap_small by lia; exact R18 | rewrite <- Ecm; lia].
- (* the command count loop *)
  intros mem4 md4 regs4 HAT4 R11 Ht Hk Hb0.
  assert (Hcond : (negb (TC.truth (TW.g_raw (ios_B0 Bw))) && negb (ios_ka frame))%bool = true)
    by (rewrite Ht, Hk; reflexivity).
  rewrite Hcond in HCMDS.
  apply (HLOOP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw cmds ly3 S3 W2 mem4 md4 regs4 _
           HL HF Hcsf HAT4 R11 ltac:(lia) HCMDS).
  intros mem5 md5 regs5 HAT5 R18 Hcr.
  exact (KCMDS mem5 md5 regs5 HAT5 R18 Hcr).
Qed.

End dpost.
