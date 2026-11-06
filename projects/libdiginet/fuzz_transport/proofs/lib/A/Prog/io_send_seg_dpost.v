(* io_send_seg_dpost: the DATA arm of the image-A walk of io_send (fuzz_transport.asan e89be137db17, entry
   0x82d60 = TImgA.v ti_io_send timg_A), assembled from the cut IOS_CSF at 0x83160 to the walk's post.

   The arm, piece by piece, each proved elsewhere and joined here:
     lib/A/Prog/io_send_seg_data.v iod_headA    0x83160 .. 0x83190, the keepalive flag and the call of
                                                check_inflight_new;
     lib/A/Prog/io_send_seg_data.v iod_runB0    0x83190 .. 0x831a8, the three branches, to IOS_CMDS with
                                                a1 = f.ncmds or a1 = 0, or to IOS_LOOP;
     lib/A/Prog/io_send_seg_loop.v ios_loop     the command count loop, IOS_LOOP .. IOS_CMDS, a1 = the model's
                                                cmds;
     lib/A/Prog/io_send_seg_data.v iod_callC    IOS_CMDS .. 0x832a4, the call of check_latest_frame;
     lib/A/Prog/io_send_seg_data.v iod_runD     0x832a4 .. 0x832c8, the two stores into G (the world at B5) and
                                                the last branch, to IOS_KA or IOS_SENT;
     lib/A/Prog/io_send_seg_tail.v ios_tail_seg the tail of both cases, to IOS_FLY with the world at B6;
     lib/A/Prog/io_send_seg_join.v ios_fly_post the frame in flight and the epilogue, to the walk's post.
   The model's side is io_send_segs.v ios_m_arm and ios_arm_data: they give check_sent_frame's world ios_B0 Bw,
   check_inflight_new_m, the count cmds, check_latest_frame_m, the B6 of ios_B6 at
   B5 = set_g_last_counter (set_M_host_counter (ios_B0 Bw) f.send) f.send, and Bw' = ios_fly frame B6. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportLeafb LeafCgFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCgRun CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require check_inflight_new_cg check_latest_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  io_send_segs io_send_seg_cut io_send_seg_world io_send_seg_frm io_send_seg_src io_send_seg_ack
  io_send_seg_data io_send_seg_loop io_send_seg_tail io_send_seg_join io_send_seg_inv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section dpost. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Variable B : asyms.
Variable MT : ameter_ops.

(* A register index is callee-saved: compute its number, then compare. *)
Ltac idp_cs :=
  unfold acallee_saved;
  repeat (lazymatch goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end);
  lia.

Lemma idp_unsigned5 : forall rr, 0 <= rr < 32 -> bv_unsigned (Z_to_bv 5 rr) = rr.
Proof.
intros rr H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
apply Z.mod_small. exact H.
Qed.

Lemma idp_map_skipn : forall (A Bt : Type) (f : A -> Bt) (m : nat) (l : list A),
  map f (skipn m l) = skipn m (map f l).
Proof.
intros A Bt f m. induction m as [|m IH]; intros l; [reflexivity|].
destruct l as [|x l]; cbn; [reflexivity | apply IH].
Qed.

Lemma idp_nth_skipn : forall (A : Type) (d : A) (m j : nat) (l : list A), nth j (skipn m l) d = nth (m + j) l d.
Proof.
intros A d m. induction m as [|m IH]; intros j l; [reflexivity|].
destruct l as [|x l]; cbn; [destruct j; reflexivity | apply IH].
Qed.

(* A small non-negative value is its own 32-bit signed wrap. *)
Lemma idp_swrap_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

(* The command count loop answers 0 on an empty body. *)
Lemma idp_loop_zero : forall (n : nat) Bm body, TC.cmds_loop (Datatypes.S n) Bm body 0 0 0 = Some 0.
Proof. intros n Bm body. reflexivity. Qed.

(* The registers the DATA arm carries from its cut to IOS_FLY: io_send's own, with s2 = f.body_len, s4 the shadow
   base, s6 the keepalive flag and s7 the %hi of g_raw. *)
Definition idp_regs (regs regs2 : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z) : Prop :=
  YK11.getr regs2 2 = w64 (spZ regs - IOSEND_FRAME) /\
  YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (Z.of_nat (length frame)) /\ YK11.getr regs2 9 = w64 p /\
  YK11.getr regs2 18 = w64 (ios_blen frame) /\ YK11.getr regs2 19 = w64 fail /\
  YK11.getr regs2 20 = w64 SHADOW_OFF /\
  YK11.getr regs2 21 = w64 (DSpec.sf_cmd (TC.rf frame)) /\
  YK11.getr regs2 22 = w64 (iod_kaz frame) /\ YK11.getr regs2 23 = w64 IOD_S7 /\
  (forall r, 24 <= r <= 27 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).

(* The world the two stores of 0x832a4 - 0x832c4 leave (io_send_segs.v ios_arm_data's B5). *)
Definition idp_B5 (Bw frame : list byte) : list byte :=
  TW.set_g_last_counter (TW.set_M_host_counter (ios_B0 Bw) (DSpec.sf_send (TC.rf frame)))
    (DSpec.sf_send (TC.rf frame)).

Lemma ios_data_post : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k
    regs p frame Bw Bw' r ly3 S3 (W2 : world segs) mem3 md3 regs3,
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  TC.io_send_m timg_A Bw frame = Some (Bw', r) ->
  DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_DATA ->
  TC.truth (DSpec.sf_retry (TC.rf frame)) = false ->
  ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly3 S3 W2 mem3 md3 regs3 ->
  YK11.getr regs3 21 = w64 (DSpec.sf_cmd (TC.rf frame)) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_DATA) regs3 mem3 md3)
    (ios_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame Bw' (ios_ret Bw)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw' r ly3 S3 W2 mem3 md3 regs3
  HL HFX HM HCMD HRET HCSF HS5.
destruct (ios_m_arm Bw frame Bw' r HM) as (HCSFm & HARM & Hr).
destruct (ios_arm_data Bw frame Bw' HARM HCMD HRET) as (HCIN & cmds & HCMDS & HCLF & B6 & HB6 & HBw').
pose proof HL as (HCELLS & HIOC & LAWS & MTL & HGX & HGE & HAI0 & HCSFc & HAF & HLC & HCIR & HSW & HIN2 & HLF
  & HKD & HCLS & HLD & HAI1).
pose proof HFX as (HJ & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hlo & Hhi & Hp0 & Hgarr & Hsrc & Hoff & Hfat
  & Hfail & Hrom & Htw & Hinv1 & Hinv2 & Hnev).
pose proof HCSF as (HCUR & HSAV & HREG & HS811 & HSFa & HSFsrc & HGARR & HSRC & HTW).
pose proof HREG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
pose proof HCUR as (HJ2 & Hfrs & Hperm & Hmo & HKEPT).
pose proof HJ2 as (HSTK3 & _ & (memS3 & HJ3i & _) & _).
rewrite !Z.add_0_r in HJ3i.
pose proof HJ3i as (HAR3 & _).
clear HJ3i memS3.
pose proof HJ as (HSTK & _ & (memS0 & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (FS : IOSEND_STK = 8496) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 + IOSEND_STK <= spZ regs <= 2 ^ 47) by lia.
pose proof (ios_len60 (ios_B0 Bw) frame (ios_B0 Bw) HCSFm) as HL60.
pose proof (ios_sf_code (ios_B0 Bw) frame (ios_B0 Bw) HCSFm) as HOK.
pose proof (ios_len_lt32 (ios_B0 Bw) frame (ios_B0 Bw) HCSFm) as HL32.
assert (Hplen : 4096 <= p /\ p + Z.of_nat (length frame) <= 2 ^ 47).
{ destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc p (Z.of_nat (length frame)) HAR0 Hsrc ltac:(lia))
    as [Hpl | Hpl]; lia. }
destruct Hplen as (Hp1 & Hp2).
set (sp := spZ regs - IOSEND_FRAME) in *.
assert (Esp : sp = spZ regs - IOSEND_FRAME) by reflexivity.
set (graw := TW.u_at (ios_B0 Bw) TW.OFF_g_raw 4) in *.
assert (HGR : TW.g_raw (ios_B0 Bw) = bv_swrap 32 graw) by reflexivity.
pose proof (TWL.u_at_range (ios_B0 Bw) TW.OFF_g_raw 4) as Rgr.
change (8 * Z.of_nat 4) with 32 in Rgr.
set (ncm := DSpec.sf_ncmds (TC.rf frame)) in *.
assert (HWIN : iak_call_win STK sp0 sp) by (split; [rewrite Esp, Zminus_mod, Hsp16, FF; reflexivity | split; lia]).
(* 0x83160 .. 0x83190 *)
apply (iod_headA B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly3 S3 W2 mem3 md3
  regs3 _ HL HFX (conj HCSF HS5) HCSFm HCIN).
(* What the three exits of run B share: the join IOS_CMDS with a1 = the model's cmds. *)
assert (HCMDSK : forall mem5 md5 (regs5 : bvmap 5 word),
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly3 S3 W2 mem5 md5 (k + 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - ESTACK <= a < sp) ->
     aview segs (w_H W2) mem5 a = aview segs (w_H W2) mem3 a) ->
  (forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) mem5 a) ->
  idp_regs regs regs5 p frame (TW.g_fail_next Bw) ->
  YK11.getr regs5 11 = w64 (bv_swrap 32 cmds) -> 0 <= cmds < 2 ^ 32 ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_CMDS) regs5 mem5 md5)
    (ios_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame Bw' (ios_ret Bw))).
{ intros mem5 md5 regs5 HJ5 HK5 HG5 HRG5 R11' Hcmr.
  pose proof HRG5 as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24).
  assert (HSF5 : trans_sframe_at W2 mem5 (sp + 8) p (TC.rf frame)).
  { apply (iak_sframe_kept W2 mem3 mem5 (sp + 8) p (TC.rf frame)); [|exact HSFa].
    intros a Ha. apply HK5; lia. }
  assert (HTW5 : tw_at TMAP_A (aview segs (w_H W2) mem5) (ios_B0 Bw)).
  { apply (tw_kept TMAP_A _ _ _ HTW). intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply HK5; lia. }
  (* IOS_CMDS .. 0x832a4 *)
  apply (iod_callC B MT STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W2 mem5 md5 (k + 0) regs5 sp p cmds frame
    (ios_B0 Bw) _ HL HJ5 Q2 ltac:(transitivity (YK11.getr regs 3); [exact Q3 | exact Hgp])
    ltac:(transitivity (YK11.getr regs 4); [exact Q4 | exact Htp]) R11' Hcmr
    HWIN ltac:(lia) ltac:(lia) HSF5 HTW5 HCLF).
  intros mem6 md6 regs6 HJ6 HK6 HG6 HKC6.
  assert (HK65 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - ESTACK <= a < sp) ->
    aview segs (w_H W2) mem6 a = aview segs (w_H W2) mem3 a)
    by (intros a Ha Hn; rewrite (HK6 a Ha Hn); apply HK5; assumption).
  assert (HSF6 : trans_sframe_at W2 mem6 (sp + 8) p (TC.rf frame)).
  { apply (iak_sframe_kept W2 mem3 mem6 (sp + 8) p (TC.rf frame)); [|exact HSFa].
    intros a Ha. apply HK65; lia. }
  assert (HTW6 : tw_at TMAP_A (aview segs (w_H W2) mem6) (ios_B0 Bw)).
  { apply (tw_kept TMAP_A _ _ _ HTW). intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply HK65; lia. }
  pose proof HSF6 as (Hfp0' & Hfp8' & SB' & HGsb' & HLSB' & G0 & G8' & G16 & G24' & G26 & G28 & G30 & G32 & G36 &
    G40 & G41 & G48 & G56 & G64 & G72).
  pose proof (TWL.u_at_range SB' 32 4) as Rsd. change (8 * Z.of_nat 4) with 32 in Rsd.
  assert (V40 : YI04.val_mem segs (mrestrict (w_H W2) mem6) (sp + 40) 4 (DSpec.sf_send (TC.rf frame))).
  { replace (sp + 40) with (sp + 8 + 32) by lia. rewrite <- G32.
    apply (iod_val_at (mrestrict (w_H W2) mem6) (sp + 8) SB' 32 4 HGsb'); [lia | rewrite HLSB'; cbn; lia]. }
  assert (V0' : YI04.val_mem segs (mrestrict (w_H W2) mem6) TA_g_raw 4 graw).
  { pose proof (tw_read_val segs (mrestrict (w_H W2) mem6) TMAP_A (ios_B0 Bw) TW.OFF_g_raw TA_g_raw TW.SZ_g_raw
      0 4 TMAP_A_ok HTW6 TMAP_A_g_raw ltac:(lia) ltac:(unfold TW.SZ_g_raw; cbn; lia)) as Hv.
    rewrite Z.add_0_r in Hv. unfold graw. rewrite Z.add_0_r in Hv. exact Hv. }
  assert (Hkz : 0 <= iod_kaz frame <= 1) by (unfold iod_kaz; destruct (ios_ka frame); lia).
  (* 0x832a4 .. 0x832c8 *)
  apply (iod_runD B MT STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W2 mem6 md6 (k + 0) regs6 sp
    (DSpec.sf_send (TC.rf frame)) graw (iod_kaz frame) (ios_B0 Bw) _ HL HJ6
    ltac:(transitivity (YK11.getr regs5 2); [apply HKC6; unfold IOD_KEEPC; cbn [In];
          repeat (first [left; reflexivity | right]); try reflexivity | exact Q2])
    ltac:(transitivity (YK11.getr regs5 20); [apply HKC6; unfold IOD_KEEPC; cbn [In];
          repeat (first [left; reflexivity | right]); try reflexivity | exact Q20])
    ltac:(transitivity (YK11.getr regs5 23); [apply HKC6; unfold IOD_KEEPC; cbn [In];
          repeat (first [left; reflexivity | right]); try reflexivity | exact Q23])
    ltac:(transitivity (YK11.getr regs5 22); [apply HKC6; unfold IOD_KEEPC; cbn [In];
          repeat (first [left; reflexivity | right]); try reflexivity | exact Q22])
    Hkz ltac:(lia) ltac:(lia) ltac:(rewrite Esp, Zminus_mod, Hsp16, FF; reflexivity)
    ltac:(lia) ltac:(lia) V40 V0' HTW6 HGR).
  intros mem7 md7 regs7 pc HJ7 HK7 HG7 HKD7 Q20' HTW7 Hcase.
  assert (HK7all : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp - ESTACK <= a < sp) \/ IOD_WR a) ->
    aview segs (w_H W2) mem7 a = aview segs (w_H W2) mem3 a).
  { intros a Ha Hn. rewrite (HK7 a Ha ltac:(intros X; apply Hn; right; exact X)).
    apply HK65; [exact Ha | intros X; apply Hn; left; exact X]. }
  assert (HG7all : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) mem7 a)
    by (intros a Hp'; apply HG7; apply HG6; apply HG5; exact Hp').
  (* the cut, as the tail reads it *)
  assert (HT0 : ios_tail_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly3 S3 W2 mem3 md3
    (ios_B0 Bw))
    by (split; [exact HCUR | split; [exact HSAV | split; [exact HSFa | split; [exact HGARR |
        split; [exact HSRC | split; [exact Hoff | split; [exact Hfat | exact HTW]]]]]]]).
  (* the frame and io_send's own cells across the stretch *)
  assert (HnWR : forall a, p <= a < p + Z.of_nat (length frame) -> ~ IOD_WR a).
  { intros a Ha HW. destruct Hfat as [Hout | (Hgs1 & Hgs2)].
    - apply (Hout a Ha). destruct HW as [HM'|HM'].
      + apply (ios_inG_row _ _ _ _ TMAP_A_M). unfold TW.SZ_M. lia.
      + apply (ios_inG_row _ _ _ _ TMAP_A_g_last_counter). unfold TW.SZ_g_last_counter. lia.
    - unfold IOD_WR, TA_M, TA_g_last_counter, TA_g_s, TW.SZ_g_s in *. lia. }
  assert (KF : forall a, p <= a < p + Z.of_nat (length frame) ->
    aview segs (w_H W2) mem7 a = aview segs (w_H W2) mem3 a).
  { intros a Ha. apply HK7all; [lia|].
    intros [Hw | Hw]; [unfold decode_off_win in Hoff; lia | exact (HnWR a Ha Hw)]. }
  assert (KW : forall a, spZ regs - IOSEND_FRAME + 8 <= a < spZ regs ->
    aview segs (w_H W2) mem7 a = aview segs (w_H W2) mem3 a).
  { intros a Ha. apply HK7all; [lia|].
    intros [Hw | Hw]; [lia | unfold IOD_WR, TA_M, TA_g_last_counter in Hw; lia]. }
  (* the shadow of the caller's frames: far above G and far below the stack *)
  pose proof HJ7 as (HSTK7 & _ & (memS7 & HJ7i & _) & _).
  rewrite !Z.add_0_r in HJ7i. pose proof HJ7i as (HAR7 & _). clear HJ7i memS7.
  assert (KS : forall cid pos s, In (cid, pos) (frames S3) ->
    in_zr s (YG0f.shadow_addr (frame_addr ly3 cid pos), fs_frame_bytes cid / 8) ->
    aview segs (w_H W2) mem7 s = aview segs (w_H W2) mem3 s).
  { intros cid pos s Hin Hs'.
    destruct (frames_bounds segs B LAWS ly3 S3 W2 mem3 md3 cid pos HAR3 Hin) as (F1 & F2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    pose proof (shadow_range_end (frame_addr ly3 cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr ly3 cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr ly3 cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs'. cbn [fst snd] in Hs'.
    unfold FCells.shadow_addr, FCells.ASAN_K, YG0f.shadow_addr, SHADOW_OFF in *.
    change (2 ^ 47 / 8) with (2 ^ 44) in Hd.
    assert (Hsub : frame_addr ly3 cid pos / 8 + fs_frame_bytes cid / 8
      <= (frame_addr ly3 cid pos + fs_frame_bytes cid) / 8) by (Z.div_mod_to_equations; lia).
    pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)).
    assert (Hs0 : 0 <= s < 2 ^ 64) by lia.
    assert (HsW : ~ (sp - ESTACK <= s < sp)) by lia.
    assert (HsG : ~ IOD_WR s) by (unfold IOD_WR, TA_M, TA_g_last_counter; lia).
    apply HK7all; [exact Hs0 | intros [Hw|Hw]; [exact (HsW Hw) | exact (HsG Hw)]]. }
  assert (HSRC7 : trans_src_ok B ly3 S3 W2 mem7 p (Z.of_nat (length frame)))
    by exact (trans_src_ok_kept B LAWS ly3 S3 W2 mem3 md3 ly3 S3 W2 mem7 md7 p (Z.of_nat (length frame))
                HAR3 HAR7 (Permutation_refl _) eq_refl (fun c q => eq_refl) eq_refl eq_refl KF KS HSRC
                ltac:(lia)).
  assert (RKY : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem7 (spZ regs - IOSEND_STK) (spZ regs)
    (iosend_wr (Z.of_nat (length frame)))).
  { apply (ios_kept_win B lyc Sc W memc mdc W memc W2 mem3 mem7 (spZ regs)
      (Z.of_nat (length frame)) LAWS HGX HAR0 ltac:(lia) ltac:(lia) HKEPT); [|exact HG7all].
    intros a Ha Hn Hw. apply HK7all; [exact Ha|].
    intros [Hx | Hx]; [lia|]. apply Hw. destruct Hx as [Hx|Hx];
      [apply (ios_wr_hostc _ a); lia | apply (ios_wr_lastc _ a); lia]. }
  assert (HTAIL : ios_tail_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly3 S3 W2 mem7 md7
    (idp_B5 Bw frame)).
  { apply (ios_tail_core B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly3 S3 W2 mem3 md3
      (ios_B0 Bw) ly3 S3 W2 mem7 md7 (idp_B5 Bw frame) MTL HT0 HJ7 eq_refl (Permutation_refl _)
      (mo_le_refl MT MTL S3) RKY HSRC7 KF KW HTW7). }
  (* the command-length invariant at B5 *)
  assert (HINV5 : forall sx, 0 <= sx < TW.g_ncmd (idp_B5 Bw frame) ->
    TW.Cmd_st (idp_B5 Bw frame) sx = TC.PENDING -> TW.Cmd_len (idp_B5 Bw frame) sx <= DSpec.SPEC_CMD_MAX)
    by exact (ios_cmdinv_B5 Bw (DSpec.sf_send (TC.rf frame)) (tw_len TMAP_A _ _ Htw) Hinv2).
  (* the two stores leave g_raw alone, and the keepalive flag as a boolean *)
  assert (EGR : TW.g_raw (idp_B5 Bw frame) = TW.g_raw (ios_B0 Bw)).
  { assert (LB : Z.of_nat (length (ios_B0 Bw)) = TW.W_LEN).
    { rewrite (tw_len TMAP_A _ _ HTW). unfold TW.W_LEN. lia. }
    unfold idp_B5, TW.set_g_last_counter, TW.set_M_host_counter, TW.g_raw.
    rewrite TWL.s32_at_upd_out by
      (rewrite ?TWL.length_put, ?TWL.length_upd_put;
       unfold TW.OFF_g_last_counter, TW.OFF_g_raw, TW.A_M_host_counter, TW.OFF_M, TW.W_LEN in *; lia).
    rewrite TWL.s32_at_upd_out by
      (rewrite ?TWL.length_put;
       unfold TW.OFF_g_raw, TW.A_M_host_counter, TW.OFF_M, TW.W_LEN in *; lia).
    reflexivity. }
  assert (Hcase' : pc = io_send_seg_tail.IOS_KA /\
      TC.truth (TW.g_raw (idp_B5 Bw frame)) = false /\ ios_ka frame = true \/
    pc = io_send_seg_tail.IOS_SENT /\ YK11.getr regs7 10 = w64 (TW.g_raw (idp_B5 Bw frame)) /\
      (TC.truth (TW.g_raw (idp_B5 Bw frame)) = false -> ios_ka frame = false)).
  { rewrite EGR. destruct Hcase as [(E1 & E2 & E3) | (E1 & E2 & E3)].
    - left. split; [exact E1 | split; [exact E2|]].
      unfold iod_kaz in E3. destruct (ios_ka frame); [reflexivity | lia].
    - right. split; [exact E1 | split; [exact E2|]]. intros Ht. pose proof (E3 Ht) as Hz.
      unfold iod_kaz in Hz. destruct (ios_ka frame); [lia | reflexivity]. }
  (* the registers the tail and the frame in flight read *)
  assert (P2 : YK11.getr regs7 2 = w64 (spZ regs - IOSEND_FRAME)).
  { transitivity (YK11.getr regs6 2); [apply HKD7; unfold IOD_KEEPD; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity|].
    transitivity (YK11.getr regs5 2); [apply HKC6; unfold IOD_KEEPC; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity | exact Q2]. }
  assert (P3 : YK11.getr regs7 3 = YK11.getr regs 3).
  { transitivity (YK11.getr regs6 3); [apply HKD7; unfold IOD_KEEPD; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity|].
    transitivity (YK11.getr regs5 3); [apply HKC6; unfold IOD_KEEPC; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity | exact Q3]. }
  assert (P4 : YK11.getr regs7 4 = YK11.getr regs 4).
  { transitivity (YK11.getr regs6 4); [apply HKD7; unfold IOD_KEEPD; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity|].
    transitivity (YK11.getr regs5 4); [apply HKC6; unfold IOD_KEEPC; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity | exact Q4]. }
  assert (P8 : YK11.getr regs7 8 = w64 (Z.of_nat (length frame))).
  { transitivity (YK11.getr regs6 8); [apply HKD7; unfold IOD_KEEPD; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity|].
    transitivity (YK11.getr regs5 8); [apply HKC6; unfold IOD_KEEPC; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity | exact Q8]. }
  assert (P9 : YK11.getr regs7 9 = w64 p).
  { transitivity (YK11.getr regs6 9); [apply HKD7; unfold IOD_KEEPD; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity|].
    transitivity (YK11.getr regs5 9); [apply HKC6; unfold IOD_KEEPC; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity | exact Q9]. }
  assert (P18 : YK11.getr regs7 18 = w64 (ios_blen frame)).
  { transitivity (YK11.getr regs6 18); [apply HKD7; unfold IOD_KEEPD; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity|].
    transitivity (YK11.getr regs5 18); [apply HKC6; unfold IOD_KEEPC; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity | exact Q18]. }
  assert (P19 : YK11.getr regs7 19 = w64 (TW.g_fail_next Bw)).
  { transitivity (YK11.getr regs6 19); [apply HKD7; unfold IOD_KEEPD; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity|].
    transitivity (YK11.getr regs5 19); [apply HKC6; unfold IOD_KEEPC; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity | exact Q19]. }
  assert (P21 : YK11.getr regs7 21 = w64 (DSpec.sf_cmd (TC.rf frame))).
  { transitivity (YK11.getr regs6 21); [apply HKD7; unfold IOD_KEEPD; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity|].
    transitivity (YK11.getr regs5 21); [apply HKC6; unfold IOD_KEEPC; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity | exact Q21]. }
  assert (P24 : forall rr, 24 <= rr <= 27 -> YK11.getr regs7 (Z_to_bv 5 rr) = YK11.getr regs (Z_to_bv 5 rr)).
  { intros rr Hrr. assert (Er : rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    assert (HinD : In (Z_to_bv 5 rr) IOD_KEEPD).
    { unfold IOD_KEEPD. destruct Er as [Ea|[Eb|[Ec|Ed]]]; cbn [In].
      - rewrite Ea. do 10 right. left. apply bv_eq; reflexivity.
      - rewrite Eb. do 11 right. left. apply bv_eq; reflexivity.
      - rewrite Ec. do 12 right. left. apply bv_eq; reflexivity.
      - rewrite Ed. do 13 right. left. apply bv_eq; reflexivity. }
    assert (HinC : In (Z_to_bv 5 rr) IOD_KEEPC).
    { unfold IOD_KEEPC. destruct Er as [Ea|[Eb|[Ec|Ed]]]; cbn [In].
      - rewrite Ea. do 11 right. left. apply bv_eq; reflexivity.
      - rewrite Eb. do 12 right. left. apply bv_eq; reflexivity.
      - rewrite Ec. do 13 right. left. apply bv_eq; reflexivity.
      - rewrite Ed. do 14 right. left. apply bv_eq; reflexivity. }
    rewrite (HKD7 _ HinD), (HKC6 _ HinC). apply Q24. lia. }
  (* the tail of both cases, then the frame in flight and the epilogue *)
  apply (ios_tail_seg B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly3 S3 W2 mem7 md7
    regs7 (idp_B5 Bw frame) B6 pc _ HL HFX HTAIL HOK ltac:(lia) P2
    ltac:(rewrite P3; exact Hgp) ltac:(rewrite P4; exact Htp) P18 Q20' HB6 HINV5 Hcase').
  intros ly8 S8 W8 mem8 md8 regs8 HTAIL8 HPRES8.
  rewrite HBw'.
  apply (ios_fly_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw B6
    ly8 S8 W8 mem8 md8 regs8 HL HFX HTAIL8 ltac:(lia) HL32
    ltac:(rewrite (iak_ap regs7 regs8 2 HPRES8 ltac:(idp_cs)); exact P2)
    ltac:(rewrite (iak_ap regs7 regs8 3 HPRES8 ltac:(idp_cs)); exact P3)
    ltac:(rewrite (iak_ap regs7 regs8 4 HPRES8 ltac:(idp_cs)); exact P4)
    ltac:(rewrite (iak_ap regs7 regs8 8 HPRES8 ltac:(idp_cs)); exact P8)
    ltac:(rewrite (iak_ap regs7 regs8 9 HPRES8 ltac:(idp_cs)); exact P9)
    ltac:(rewrite (iak_ap regs7 regs8 19 HPRES8 ltac:(idp_cs)); exact P19)
    ltac:(rewrite (iak_ap regs7 regs8 21 HPRES8 ltac:(idp_cs)); exact P21)
    ltac:(intros rr Hrr; rewrite (iak_ap regs7 regs8 (Z_to_bv 5 rr) HPRES8
            ltac:(unfold acallee_saved; rewrite (idp_unsigned5 rr ltac:(lia)); lia)); apply P24; lia)). }
intros mem4 md4 regs4 HJ4 HK4 HG4 HRK4 R18' R22'.
(* the struct, the world and the two values run B reads, at the memory the leaf left *)
assert (HSF4 : trans_sframe_at W2 mem4 (sp + 8) p (TC.rf frame)).
{ apply (iak_sframe_kept W2 mem3 mem4 (sp + 8) p (TC.rf frame)); [|exact HSFa].
  intros a Ha. apply HK4; lia. }
assert (HTW4 : tw_at TMAP_A (aview segs (w_H W2) mem4) (ios_B0 Bw)).
{ apply (tw_kept TMAP_A _ _ _ HTW). intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply HK4; lia. }
assert (HGARR4 : garr8 segs (mrestrict (w_H W2) mem4) p (map DSpec.bz frame)).
{ apply (iak_garr8_kept (w_H W2) mem3 mem4 p (map DSpec.bz frame)); [|exact HGARR].
  intros a Ha. rewrite length_map in Ha. apply HK4;
    [lia | unfold decode_off_win in Hoff; destruct Hoff as [Ho|Ho]; lia]. }
assert (V0 : YI04.val_mem segs (mrestrict (w_H W2) mem4) TA_g_raw 4 graw).
{ pose proof (tw_read_val segs (mrestrict (w_H W2) mem4) TMAP_A (ios_B0 Bw) TW.OFF_g_raw TA_g_raw TW.SZ_g_raw
    0 4 TMAP_A_ok HTW4 TMAP_A_g_raw ltac:(lia) ltac:(unfold TW.SZ_g_raw; cbn; lia)) as Hv.
  rewrite Z.add_0_r in Hv. unfold graw. rewrite Z.add_0_r in Hv. exact Hv. }
pose proof HSF4 as (Hfp0 & Hfp8 & SB & HGsb & HLSB & F0 & F8 & F16 & F24 & F26 & F28 & F30 & F32 & F36 & F40 &
  F41 & F48 & F56 & F64 & F72).
assert (Rncm : 0 <= ncm < 256).
{ pose proof (TWL.u_at_range SB 41 1) as Rr. change (8 * Z.of_nat 1) with 8 in Rr. unfold ncm. rewrite <- F41. lia. }
assert (V49 : YI04.val_mem segs (mrestrict (w_H W2) mem4) (sp + 49) 1 ncm).
{ replace (sp + 49) with (sp + 8 + 41) by lia. unfold ncm. rewrite <- F41.
  apply (iod_val_at (mrestrict (w_H W2) mem4) (sp + 8) SB 41 1 HGsb); [lia | rewrite HLSB; cbn; lia]. }
assert (Rblen : 0 <= ios_blen frame < 2 ^ 64).
{ pose proof (TWL.u_at_range SB 56 8) as Rr. change (8 * Z.of_nat 8) with 64 in Rr.
  unfold ios_blen. rewrite <- F56. lia. }
assert (R2' : YK11.getr regs4 2 = w64 sp).
{ rewrite <- R2. apply HRK4. unfold IOD_KEEP. cbn [In]. auto 20. }
assert (R20' : YK11.getr regs4 20 = w64 SHADOW_OFF).
{ rewrite <- R20. apply HRK4. unfold IOD_KEEP. cbn [In]. auto 20. }
assert (HRGC : forall (rg : bvmap 5 word),
  (forall r, In r IOD_KEEPB -> YK11.getr rg r = YK11.getr regs4 r) ->
  YK11.getr rg 23 = w64 IOD_S7 -> idp_regs regs rg p frame (TW.g_fail_next Bw)).
{ intros rg HK H23. unfold idp_regs. repeat split.
  - transitivity (YK11.getr regs4 2); [apply HK; unfold IOD_KEEPB; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity | exact R2'].
  - transitivity (YK11.getr regs4 3); [apply HK; unfold IOD_KEEPB; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity|].
    transitivity (YK11.getr regs3 3); [apply HRK4; unfold IOD_KEEP; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity | exact R3].
  - transitivity (YK11.getr regs4 4); [apply HK; unfold IOD_KEEPB; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity|].
    transitivity (YK11.getr regs3 4); [apply HRK4; unfold IOD_KEEP; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity | exact R4].
  - transitivity (YK11.getr regs4 8); [apply HK; unfold IOD_KEEPB; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity|].
    transitivity (YK11.getr regs3 8); [apply HRK4; unfold IOD_KEEP; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity | exact R8].
  - transitivity (YK11.getr regs4 9); [apply HK; unfold IOD_KEEPB; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity|].
    transitivity (YK11.getr regs3 9); [apply HRK4; unfold IOD_KEEP; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity | exact R9].
  - transitivity (YK11.getr regs4 18); [apply HK; unfold IOD_KEEPB; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity | exact R18'].
  - transitivity (YK11.getr regs4 19); [apply HK; unfold IOD_KEEPB; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity|].
    transitivity (YK11.getr regs3 19); [apply HRK4; unfold IOD_KEEP; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity | exact R19].
  - transitivity (YK11.getr regs4 20); [apply HK; unfold IOD_KEEPB; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity | exact R20'].
  - transitivity (YK11.getr regs4 21); [apply HK; unfold IOD_KEEPB; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity|].
    transitivity (YK11.getr regs3 21); [apply HRK4; unfold IOD_KEEP; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity | exact HS5].
  - transitivity (YK11.getr regs4 22); [apply HK; unfold IOD_KEEPB; cbn [In]; repeat (first [left; reflexivity | right]); try reflexivity | exact R22'].
  - exact H23.
  - intros rr Hrr.
    assert (Er : rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    assert (HinB : In (Z_to_bv 5 rr) IOD_KEEPB).
    { unfold IOD_KEEPB. destruct Er as [Ea|[Eb|[Ec|Ed]]]; cbn [In].
      - rewrite Ea. do 10 right. left. apply bv_eq; reflexivity.
      - rewrite Eb. do 11 right. left. apply bv_eq; reflexivity.
      - rewrite Ec. do 12 right. left. apply bv_eq; reflexivity.
      - rewrite Ed. do 13 right. left. apply bv_eq; reflexivity. }
    assert (HinA : In (Z_to_bv 5 rr) IOD_KEEP).
    { unfold IOD_KEEP. destruct Er as [Ea|[Eb|[Ec|Ed]]]; cbn [In].
      - rewrite Ea. do 9 right. left. apply bv_eq; reflexivity.
      - rewrite Eb. do 10 right. left. apply bv_eq; reflexivity.
      - rewrite Ec. do 11 right. left. apply bv_eq; reflexivity.
      - rewrite Ed. do 12 right. left. apply bv_eq; reflexivity. }
    rewrite (HK _ HinB), (HRK4 _ HinA). apply HS811. lia. }
(* 0x83190 .. 0x831a8 *)
apply (iod_runB0 B MT STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W2 mem4 md4 (k + 0) regs4 sp graw ncm frame Bw _
  HL HJ4 R2' R20' R18' R22' ltac:(lia) ltac:(lia) ltac:(rewrite Esp, Zminus_mod, Hsp16, FF; reflexivity)
  ltac:(lia) Rncm Rblen HGR V0 V49).
all: intros md5 regs5 HKp R23' R11' HJ5.
- (* g_raw <> 0 or the keepalive flag: the model's cmds is f.ncmds *)
  intros Hcase.
  assert (Ecm : ncm = cmds).
  { assert (Hcond : (negb (TC.truth (TW.g_raw (ios_B0 Bw))) && negb (ios_ka frame))%bool = false)
      by (destruct Hcase as [Ht|Hk]; [rewrite Ht | rewrite Hk, Bool.andb_false_r]; reflexivity).
    rewrite Hcond in HCMDS.
    exact (f_equal (fun o : option Z => match o with Some x => x | None => 0 end) HCMDS). }
  apply (HCMDSK mem4 md5 regs5 HJ5 HK4 HG4 (HRGC regs5 HKp R23'));
    [rewrite <- Ecm, idp_swrap_small by lia; exact R11' | rewrite <- Ecm; lia].
- (* body_len = 0: the loop's answer is 0 *)
  intros Ht Hk Hb0.
  assert (Ecm : 0 = cmds).
  { assert (Hcond : (negb (TC.truth (TW.g_raw (ios_B0 Bw))) && negb (ios_ka frame))%bool = true)
      by (rewrite Ht, Hk; reflexivity).
    rewrite Hcond, Hb0, (idp_loop_zero (Z.to_nat 0) (ios_B0 Bw) (ios_body frame)) in HCMDS.
    exact (f_equal (fun o : option Z => match o with Some x => x | None => 0 end) HCMDS). }
  apply (HCMDSK mem4 md5 regs5 HJ5 HK4 HG4 (HRGC regs5 HKp R23'));
    [rewrite <- Ecm, idp_swrap_small by lia; exact R11' | rewrite <- Ecm; lia].
- (* the command count loop *)
  intros Ht Hk Hb0.
  assert (Hcond : (negb (TC.truth (TW.g_raw (ios_B0 Bw))) && negb (ios_ka frame))%bool = true)
    by (rewrite Ht, Hk; reflexivity).
  rewrite Hcond in HCMDS.
  destruct (ios_body_len frame HOK) as (EB & EBL & EBp & EBl).
  pose proof (TWL.u_at_range SB 56 8) as Rbl. change (8 * Z.of_nat 8) with 64 in Rbl.
  assert (Hbl0 : 0 <= ios_blen frame) by (unfold ios_blen; rewrite <- F56; lia).
  (* the body's bytes at p + 30 *)
  assert (HGB : garr8 segs (mrestrict (w_H W2) mem4) (p + 30) (map DSpec.bz (ios_body frame))).
  { assert (ENTH : forall j, nth j (map DSpec.bz (ios_body frame)) 0 = nth (30 + j) (map DSpec.bz frame) 0).
    { intros j. rewrite EB. rewrite <- (idp_nth_skipn Z 0 30 j (map DSpec.bz frame)). f_equal.
      apply idp_map_skipn. }
    intros j Hj. rewrite length_map, EB, length_skipn in Hj.
    assert (Hj2 : (30 + j < length (map DSpec.bz frame))%nat) by (rewrite length_map; lia).
    destruct (HGARR4 (30 + j)%nat Hj2) as (Hv & Hrb). rewrite ENTH. split.
    - intros i Hi. replace (p + 30 + Z.of_nat j + Z.of_nat i) with (p + Z.of_nat (30 + j) + Z.of_nat i) by lia.
      exact (Hv i Hi).
    - exact Hrb. }
  (* the shadow bytes the loop's checks read are kept across the leaf *)
  assert (HKsh : forall x, 0 <= x < 2 ^ 47 ->
    aview segs (w_H W2) mem4 (shadow_of_addr SHADOW_OFF x) = aview segs (w_H W2) mem3 (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. unfold shadow_of_addr.
    pose proof (Z.div_le_mono x (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as Hd.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as Hd0.
    change (2 ^ 47 / 8) with (2 ^ 44) in Hd.
    apply HK4; unfold SHADOW_OFF; lia. }
  destruct (trans_src_ok_rd B LAWS ly3 S3 W2 mem3 md3 p (Z.of_nat (length frame)) HAR3 HSRC ltac:(lia))
    as (_ & HRAf3 & _ & HAMf & _ & _).
  assert (HRAB : range_addressable (aview segs (w_H W2) mem4) SHADOW_OFF (p + 30) (ios_blen frame)).
  { intros x Hx. destruct (HRAf3 x ltac:(lia)) as (sv & Hsv & Hok).
    exists sv. split; [|exact Hok]. rewrite (HKsh x ltac:(lia)). exact Hsv. }
  assert (HRAC : range_addressable (aview segs (w_H W2) mem4) SHADOW_OFF TA_g_cmd TW.SZ_g_cmd).
  { intros x Hx. unfold TA_g_cmd, TW.SZ_g_cmd in Hx.
    destruct (decode_zshadow_ra B ly3 S3 W2 mem3 md3 TA_g_cmd (TA_g_cmd + TW.SZ_g_cmd) TA_g_cmd TW.SZ_g_cmd
      HAR3 (proj1 HIOC) ltac:(unfold TW.SZ_g_cmd; lia)
      ltac:(unfold TA_g_cmd; vm_compute; discriminate) ltac:(unfold TA_g_cmd, TW.SZ_g_cmd; vm_compute; discriminate))
      as (HR & _).
    destruct (HR x ltac:(unfold TA_g_cmd, TW.SZ_g_cmd; lia)) as (sv & Hsv & Hok).
    exists sv. split; [|exact Hok]. rewrite (HKsh x ltac:(unfold TA_g_cmd in *; lia)). exact Hsv. }
  (* f.body in the slot at sp + 56 *)
  assert (SP5 : spZ regs5 = sp).
  { change (spZ regs5) with (bv_unsigned (YK11.getr regs5 2)).
    rewrite (HKp (2%bv : bv 5) ltac:(unfold IOD_KEEPB; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity)), R2'.
    unfold w64. apply unsigned_lit_small. lia. }
  assert (HSLOT : rdword (aview segs (w_H W2) mem4) (spZ regs5 + 56) = Some (p + 30)).
  { rewrite SP5. apply AF0x.val_mem_rdword; [lia|].
    replace (sp + 56) with (sp + 8 + 48) by lia.
    rewrite <- (iod_sf_body p frame HOK), <- F48.
    apply (iod_val_at (mrestrict (w_H W2) mem4) (sp + 8) SB 48 8 HGsb); [lia | rewrite HLSB; cbn; lia]. }
  (* the body is apart from g_ncmd's four bytes *)
  assert (HDJ : p + 30 + ios_blen frame <= TA_g_ncmd \/ TA_g_ncmd + TW.SZ_g_ncmd <= p + 30).
  { destruct Hfat as [Hout | (Hgs1 & Hgs2)].
    - destruct (Z_le_dec (p + Z.of_nat (length frame)) TA_g_ncmd) as [Hle|Hgt]; [left; lia|].
      destruct (Z_le_dec (TA_g_ncmd + TW.SZ_g_ncmd) p) as [Hle2|Hgt2];
        [right; unfold TW.SZ_g_ncmd in *; lia|].
      exfalso. apply (Hout (Z.max p TA_g_ncmd)); [unfold TW.SZ_g_ncmd in *; lia|].
      apply (ios_inG_row _ _ _ _ TMAP_A_g_ncmd). unfold TW.SZ_g_ncmd in *. lia.
    - right. unfold TA_g_ncmd, TA_g_s, TW.SZ_g_ncmd in *. lia. }
  apply (ios_loop fx rc W2 mem4 regs5 md5 (p + 30) (ios_blen frame) cmds (ios_body frame) (ios_B0 Bw)
    (Datatypes.S (Z.to_nat (ios_blen frame)))
    (fun md => @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
       own ly3 S3 W2 mem4 md (k + 0))
    _).
  + intros md' X HJ'. apply (ajournal_gx_materialize segs B LAWS transport_segs_low). exact HJ'.
  + exact HTW4.
  + exact HGB.
  + lia.
  + rewrite EBL. lia.
  + lia.
  + destruct HAMf as [Ha|Ha]; [left | right]; unfold TC.SPEC_MAX_FRAME in *; lia.
  + exact HRAB.
  + exact HRAC.
  + exact HDJ.
  + exact R11'.
  + rewrite (HKp (18%bv : bv 5) ltac:(unfold IOD_KEEPB; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity)). exact R18'.
  + rewrite (HKp (20%bv : bv 5) ltac:(unfold IOD_KEEPB; cbn [In];
      repeat (first [left; reflexivity | right]); try reflexivity)). exact R20'.
  + rewrite SP5. lia.
  + exact HSLOT.
  + exact HCMDS.
  + exact HJ5.
  + intros regs6 md6 R11'' Hcmr HKP6 HJ6.
    apply (HCMDSK mem4 md6 regs6 HJ6 HK4 HG4); [| exact R11'' | exact Hcmr].
    unfold idp_regs.
    pose proof (HRGC regs5 HKp R23') as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
    repeat split.
    * rewrite (HKP6 (2%bv : bv 5) ltac:(unfold IOS_LP_KP; cbn [In];
        repeat (first [left; reflexivity | right]); try reflexivity)). exact G2.
    * rewrite (HKP6 (3%bv : bv 5) ltac:(unfold IOS_LP_KP; cbn [In];
        repeat (first [left; reflexivity | right]); try reflexivity)). exact G3.
    * rewrite (HKP6 (4%bv : bv 5) ltac:(unfold IOS_LP_KP; cbn [In];
        repeat (first [left; reflexivity | right]); try reflexivity)). exact G4.
    * rewrite (HKP6 (8%bv : bv 5) ltac:(unfold IOS_LP_KP; cbn [In];
        repeat (first [left; reflexivity | right]); try reflexivity)). exact G8.
    * rewrite (HKP6 (9%bv : bv 5) ltac:(unfold IOS_LP_KP; cbn [In];
        repeat (first [left; reflexivity | right]); try reflexivity)). exact G9.
    * rewrite (HKP6 (18%bv : bv 5) ltac:(unfold IOS_LP_KP; cbn [In];
        repeat (first [left; reflexivity | right]); try reflexivity)). exact G18.
    * rewrite (HKP6 (19%bv : bv 5) ltac:(unfold IOS_LP_KP; cbn [In];
        repeat (first [left; reflexivity | right]); try reflexivity)). exact G19.
    * rewrite (HKP6 (20%bv : bv 5) ltac:(unfold IOS_LP_KP; cbn [In];
        repeat (first [left; reflexivity | right]); try reflexivity)). exact G20.
    * rewrite (HKP6 (21%bv : bv 5) ltac:(unfold IOS_LP_KP; cbn [In];
        repeat (first [left; reflexivity | right]); try reflexivity)). exact G21.
    * rewrite (HKP6 (22%bv : bv 5) ltac:(unfold IOS_LP_KP; cbn [In];
        repeat (first [left; reflexivity | right]); try reflexivity)). exact G22.
    * rewrite (HKP6 (23%bv : bv 5) ltac:(unfold IOS_LP_KP; cbn [In];
        repeat (first [left; reflexivity | right]); try reflexivity)). exact G23.
    * intros rr Hrr.
      assert (Er : rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
      assert (HinL : In (Z_to_bv 5 rr) IOS_LP_KP).
      { unfold IOS_LP_KP. destruct Er as [Ea|[Eb|[Ec|Ed]]]; cbn [In].
        - rewrite Ea. do 12 right. left. apply bv_eq; reflexivity.
        - rewrite Eb. do 13 right. left. apply bv_eq; reflexivity.
        - rewrite Ec. do 14 right. left. apply bv_eq; reflexivity.
        - rewrite Ed. do 15 right. left. apply bv_eq; reflexivity. }
      rewrite (HKP6 _ HinL). apply G24. lia.
Qed.

End dpost.
