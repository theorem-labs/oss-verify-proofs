(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2252 of its 2377 lines of code are new or changed and 886 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R10A.v, with its numbers changed; 2171 of its 2324 lines of code are new or changed and 2224 lines of the source are left out. *)
(* lib/A/ACtlG/R10.v -- GLUE for stage seg_R10 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   piece W2, the round trip's turn b).  Written by a Theorem Labs lane (a Theorem Labs lane's stage lane), single writer.
   rule 24: no function proved (stage glue of a walk; At ossv/recipes c5e779efe8c (2026-10-31), no released proof of this unit's LLVMFuzzerTestOneInput outside this unit).

   WHAT IT PROVES
     glue_seg_R10 : forall POST (b : nat), CF POST (ix_cut C_A816c4_at [Z.of_nat b]) -> CF POST (ix_cut C_A81708_at ..)
       -> CF POST (ix_cut C_A81768_at ..) -> CF POST (ix_cut C_A817c8_at ..) -> CF POST (ix_cut C_A817ec_at ..)
       -> CF POST (ix_cut C_A81680_at [Z.of_nat b])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []): ACtl.v (at head lib/A/ACtl.v:682-684)'s Hypothesis seg_R10,
   character for character (from a working branch 1899bed1aee).  Segment R10 (seg_R10 of Seg/R10.v, not in this delivery) dispatches on the turn b:
     b = 0     r10_b0   0x81680 .. 0x81768   R10AF.r10a_evt0_F            exit C_A81768_at
     b = 1, 2  r10_b12  0x81680 .. 0x817ec   R10AF.r10a_evt12_F           exit C_A817ec_at
     b = 3, 4  r10_b34  0x81680 .. 0x816ac   R10AF.r10a_head34_F, then 0x816ac .. the reply entry
                        R10AFs.r10a_call34_pre_Fs, then the cgif-form REPLY_SPEC (the SPLIT POINT, a Theorem Labs lane
                        03:14Z: reac_ctrl_identity_reply has no _F), whose post returns at 0x816c4 = exit C_A816c4_at
     b = 5, 6  r10_b56  0x81680 .. 0x81708 / 0x817c8, R10BFon.r10b_evt_F_on (the route (C) twin of
                        R10BF.r10b_evt_F, the reac_ctrl_identity_fragment call inside on its narrowed contract,
                        supplied by a Theorem Labs lane's reac_ctrl_identity_fragment_F_holds_on_closed)   exits C_A81708_at /
                        C_A817c8_at
     b >= 7    r10_b7   the entry body states (b <= 6)%nat
   Every run is lifted at RNG := ProgBridge.RNG_W (w_H W3) with YA0nR.SRr_fevt_hid after YA0nR.SRr_xregs_eqv
   (glue-pattern.md (a working note, not in this delivery) G1-G5); every journal step is YCbq.ajournal_exec (frame-shadow / callee windows, awr_byte's
   in_frames and stack cases).  Across the reply call the cut's memory facts are carried in the core's view by its
   post's CtrlCallerJ.tcj_kept (section 1b, r10_cp), and the block shadows (HB, the input block) are re-established
   from AR_shadow_law at the post.

   ROUTE (C) (ACtlCut.v:243): the cut gives A.ACtlRtC.ctl_rt_C B ly3 S3 mem3.  Its shadow uses here: the
   arms' metadata stores into the owned frame's shadow [S(fr) + 306, S(fr) + 318) (region (F), r10_cut_fsh); the
   fragment call's own region (reac_ctrl_identity_fragment_shadow_R at this call: the record's spans in (F), the
   message's in the turn block's cover (L), r10_fragR_cut).  Every exit supplies the next cut's ctl_rt_C from its
   journal's AR (A.ProgWorldCtlRtC.ctl_rt_C_of_AR, r10_rtC_exit); no VIS0 / OWNED_RO.

   CITED BY NAME: A.ProgWorldCtlRtC.ctl_rt_C_of_AR (every exit), A.ProgWorldRtC.rt_of_core_C (the five runtime cells
   of the fragment contract, b = 5, 6), A.ProgWorld_Fs.ctl_frame_above_img (the frame above the image, b = 5, 6),
   A.Prog.reac_ctrl_identity_fragment_F_on.reac_ctrl_identity_fragment_F_holds_on_closed (a Theorem Labs lane), and the
   twin A.Prog.Seg.R10BFon.r10b_evt_F_on (this lane's additive beside-file of R10BF.v).

   SECTION HYPOTHESES (ACtl.v's own RELRO_IMG, LAWS, TFIB_SYMS, same texts, and)
   - REPLY_SPEC: ACtl.v's TREPLY, a Theorem Labs lane's treac_ctrl_identity_reply_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI,
     cited by name from lib/A/Prog/C_reac_ctrl_identity_reply.v (open in ACtl.v for the reason at ACtl.v:311-314).

   FRAC IS RE-ESTABLISHED by r10_frac_keep and r10_frac_view (and inside r10_b56), with its trailer word.

   CLOSURE: every Require is qualified; the core's modules are named lib.Reusable.* / lib.Lib.*, ctrl's A.*; the
   _F files (Seg/R10AF.v, Seg/R10AFs.v, Seg/R10BFon.v, reac_ctrl_identity_fragment_F_on.v) and their frame-route
   closure are Required as the closure rule allows.  No unproved step, no axiom, no parameter.
   BUILD STATE: see the commit message (the label of the build of record and its base). *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
(* Every module of the unit is Required by its FULL path (ctrlgate rule (b): a partial form that matches several
   twin copies is refused); the core's lib/Reusable and lib/Lib copies are the intended ones (the cut layer's
   classes and readers are the core's), ctrl's own A/Reusable/YK11 only for the R10B twin's seg_rom. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE01 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI00 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcReply.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2k.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlK.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACfn OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AF0m.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormTr.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.rng_asan OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlBase OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlCallerJ.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlImg OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlList.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlPa OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.PaTable.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_identity_fragment_c.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_identity_fragment_F_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.sh_word_on OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c_on OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_identity_reply_c.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parse.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_identity_reply.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotInv.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFPLib.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.B3Rtm OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.Tac_slot.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R10A OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R10AF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R10B OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R10AFs.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R10BFon.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.Kit.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld_Fs.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlRtC.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldCtlRtC OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldRtC.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   0. Facts that need no Section argument. *)

Lemma r10_ixn0 : forall b : nat, A.ACtlCutP.ixn 0 [Z.of_nat b] = b.
Proof. intros b. exact (Nat2Z.id b). Qed.

(* No segment of the image reaches IMG_HI. *)
Lemma r10_seg_none : forall a, A.Prog.ImgBounds.IMG_HI <= a -> find_segment A.Img0.rsegs a 1 = None.
Proof.
  intros a Ha. destruct (find_segment A.Img0.rsegs a 1) as [s|] eqn:E; [|reflexivity].
  exfalso. destruct (A.MemNormTr.find_segment_end_below A.Img0.rsegs A.Prog.ImgBounds.IMG_HI a 1 s
                       A.MemNormTr.rsegs_below_img E ltac:(lia)) as [L|L]; lia.
Qed.

(* A byte with a non-negative signed value has that value as its unsigned value. *)
Lemma r10_unsigned_of_signed : forall b : byte, 0 <= bv_signed b -> bv_unsigned b = bv_signed b.
Proof.
  intros k H. pose proof (bv_unsigned_in_range 8 k) as R. unfold bv_modulus in R. cbn in R.
  revert H. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8 / 2) with 128. change (2 ^ Z.of_N 8) with 256.
  intros H. Z.div_mod_to_equations. lia.
Qed.

(* Above the image a writable view is a present byte. *)
Lemma r10_wv_some : forall (m : word -> option byte) (a : word),
  A.Prog.ImgBounds.IMG_HI <= bv_unsigned a -> wview A.Img0.rsegs m a <> None -> m a <> None.
Proof.
  intros m a Ha H Hm. apply H. unfold wview. rewrite Hm, (r10_seg_none _ Ha). reflexivity.
Qed.

(* Application memory and the shadow map, for the frame and the blocks. *)
Section Rc.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Lemma r10_in_app_mem : forall p n, lib.Reusable.YG0f.in_app p n ->
  forall x, p <= x < p + n -> A.AsanRT.app_mem x.
Proof.
  intros p n Hp x Hx. pose proof lib.Reusable.YCbq.asan_consts as (HAC & _).
  unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.ASAN_CEIL, lib.Reusable.YG0f.kLowShadowBeg,
    lib.Reusable.YG0f.kHighMemBeg in Hp.
  unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   0b. The core's view (YG0n.aview) against ctrl's byte read (Lib.Mem.mrd) at an address no segment covers
   (r10_off: above the image, or a client byte, AR_client_img_law).  These carry a cut's memory facts across the
   cgif-form reply call, whose post keeps the caller's bytes in the view (CtrlCallerJ.tcj_kept), and build the
   call's view premises from them. *)
Definition r10_off (x : Z) : Prop := 0 <= x < 2 ^ 64 /\ find_segment A.Img0.rsegs x 1 = None.

Lemma r10_off_hi : forall x, A.Prog.ImgBounds.IMG_HI <= x < 2 ^ 64 -> r10_off x.
Proof.
  intros x Hx. split; [unfold A.Prog.ImgBounds.IMG_HI in Hx; lia|]. exact (r10_seg_none x ltac:(lia)).
Qed.

Lemma r10_off_img : forall x, 0 <= x < 2 ^ 64 -> ~ lib.Reusable.YG0d.in_img segs x -> r10_off x.
Proof. intros x Hx Hn. split; [exact Hx|]. exact (lib.Reusable.YCbq.find_segment_none segs x Hn). Qed.

Lemma r10_rom_none : forall x, r10_off x ->
  lib.Lib.PropExec.seg_rom A.Img0.rsegs (lib.Lib.Mem.wa x) = None.
Proof.
  intros x (Hx & Hs). apply A.MemNorm.seg_rom_unmapped. rewrite lib.Lib.Mem.wa_unsigned by lia. exact Hs.
Qed.

Lemma r10_view_rd : forall (H : word -> bool) (m : word -> option byte) x, r10_off x ->
  lib.Reusable.YG0n.aview segs H m x =
  option_map (fun b : byte => bv_unsigned b) (lib.Reusable.YK04.mrestrict H m (lib.Lib.Mem.wa x)).
Proof.
  intros H m x Hx. pose proof (r10_rom_none x Hx) as Hr.
  change (lib.Lib.PropExec.seg_rom A.Img0.rsegs (lib.Lib.Mem.wa x))
    with (lib.Reusable.YK11.seg_rom segs (lib.Lib.Mem.wa x)) in Hr.
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte. change (Z_to_bv 64 x) with (lib.Lib.Mem.wa x).
  destruct (lib.Reusable.YK04.mrestrict H m (lib.Lib.Mem.wa x)); [reflexivity|]. rewrite Hr. reflexivity.
Qed.

Lemma r10_view_of : forall (H : word -> bool) (m : word -> option byte) x b,
  r10_off x -> H (lib.Lib.Mem.wa x) = false ->
  lib.Lib.Mem.mrd A.Img0.rsegs m (lib.Lib.Mem.wa x) = Some b ->
  lib.Reusable.YG0n.aview segs H m x = Some (bv_unsigned b).
Proof.
  intros H m x b Hx Hh Hm. rewrite (r10_view_rd H m x Hx). unfold lib.Reusable.YK04.mrestrict. rewrite Hh.
  pose proof (r10_rom_none x Hx) as Hr. unfold lib.Lib.Mem.mrd in Hm.
  destruct (m (lib.Lib.Mem.wa x)) as [b'|]; [injection Hm as ->; reflexivity | rewrite Hr in Hm; discriminate].
Qed.

Lemma r10_rd_of_view : forall (H : word -> bool) (m : word -> option byte) x v,
  r10_off x -> lib.Reusable.YG0n.aview segs H m x = Some v ->
  H (lib.Lib.Mem.wa x) = false /\ exists b, m (lib.Lib.Mem.wa x) = Some b /\ bv_unsigned b = v /\
    lib.Lib.Mem.mrd A.Img0.rsegs m (lib.Lib.Mem.wa x) = Some b.
Proof.
  intros H m x v Hx Hv. rewrite (r10_view_rd H m x Hx) in Hv. unfold lib.Reusable.YK04.mrestrict in Hv.
  destruct (H (lib.Lib.Mem.wa x)); [discriminate|]. split; [reflexivity|].
  destruct (m (lib.Lib.Mem.wa x)) as [b|] eqn:Em; [|discriminate]. injection Hv as Hb.
  exists b. split; [reflexivity|]. split; [exact Hb|]. unfold lib.Lib.Mem.mrd. rewrite Em. reflexivity.
Qed.

Lemma r10_carry_byte : forall (H H' : word -> bool) (m m' : word -> option byte) x v,
  r10_off x -> H (lib.Lib.Mem.wa x) = false ->
  lib.Lib.Mem.mrd A.Img0.rsegs m (lib.Lib.Mem.wa x) = Some v ->
  lib.Reusable.YG0n.aview segs H' m' x = lib.Reusable.YG0n.aview segs H m x ->
  lib.Lib.Mem.mrd A.Img0.rsegs m' (lib.Lib.Mem.wa x) = Some v.
Proof.
  intros H H' m m' x v Hx Hh Hm Hv. rewrite (r10_view_of H m x v Hx Hh Hm) in Hv.
  destruct (r10_rd_of_view H' m' x _ Hx Hv) as (_ & b & _ & Hb & Hrd). rewrite Hrd. f_equal.
  apply bv_eq. exact Hb.
Qed.

Lemma r10_carry_bytes : forall (H H' : word -> bool) (m m' : word -> option byte) a l,
  (forall i, 0 <= i < Z.of_nat (length l) ->
     r10_off (a + i) /\ H (lib.Lib.Mem.wa (a + i)) = false /\
     lib.Reusable.YG0n.aview segs H' m' (a + i) = lib.Reusable.YG0n.aview segs H m (a + i)) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a l -> lib.Lib.Mem.bytes_at A.Img0.rsegs m' a l.
Proof.
  intros H H' m m' a l Hk (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (Hk (Z.of_nat i) ltac:(lia)) as (Ho & Hh & Hv). pose proof (H2 i Hi) as Hb.
  destruct (nth_error l i) as [v|] eqn:E; [| apply nth_error_None in E; lia].
  exact (r10_carry_byte H H' m m' (a + Z.of_nat i) v Ho Hh Hb Hv).
Qed.

Lemma r10_carry_addr : forall (H H' : word -> bool) (m m' : word -> option byte) p n,
  (forall i, 0 <= i < n ->
     H (lib.Lib.Mem.wa (A.AsanRT.shadow_addr (p + i))) = false /\
     lib.Reusable.YG0n.aview segs H' m' (A.AsanRT.shadow_addr (p + i)) =
     lib.Reusable.YG0n.aview segs H m (A.AsanRT.shadow_addr (p + i))) ->
  A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n.
Proof.
  intros H H' m m' p n Hk (H0 & H1 & H2 & H3). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H3 i Hi) as (Hap & b & Hb & Hok). destruct (Hk i Hi) as (Hh & Hv).
  split; [exact Hap|]. exists b. split; [|exact Hok].
  apply (r10_carry_byte H H' m m' _ b); [| exact Hh | exact Hb | exact Hv].
  apply r10_off_hi.
  unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, A.Prog.ImgBounds.IMG_HI. unfold A.AsanRT.APPMEM_END in H2.
  pose proof (Z.div_pos (p + i) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (p + i) (2 ^ 64) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma r10_wr_of_bytes : forall (m : word -> option byte) a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> r10_off (a + i)) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a l ->
  lib.Lib.Mem.wr_at A.Img0.rsegs m a (Z.of_nat (length l)).
Proof.
  intros m a l Ho (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. pose proof (H2 (Z.to_nat i) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
  destruct (nth_error l (Z.to_nat i)) as [v|] eqn:E; [| apply nth_error_None in E; lia].
  pose proof (Ho i Hi) as Hoi. pose proof (r10_rom_none (a + i) Hoi) as Hr. destruct Hoi as (Hr0 & Hs).
  assert (Hu : bv_unsigned (lib.Lib.Mem.wa (a + i)) = a + i) by (apply lib.Lib.Mem.wa_unsigned; lia).
  unfold lib.Lib.Mem.mrd in Hb.
  destruct (m (lib.Lib.Mem.wa (a + i))) as [bb|] eqn:Em; [| rewrite Hr in Hb; discriminate].
  unfold wview. rewrite Em. rewrite ?Hu. rewrite ?Hs. discriminate.
Qed.

Lemma r10_garr8_of_bytes : forall (H : word -> bool) (m : word -> option byte) a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> r10_off (a + i) /\ H (lib.Lib.Mem.wa (a + i)) = false) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a l ->
  lib.Reusable.YI00.garr8 segs (lib.Reusable.YK04.mrestrict H m) a (map (fun b : byte => bv_unsigned b) l).
Proof.
  intros H m a l Hh (H0 & H1 & H2) j Hj. rewrite length_map in Hj.
  destruct (nth_error l j) as [v|] eqn:E; [| apply nth_error_None in E; lia].
  assert (Ej : nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned v).
  { apply nth_error_nth. rewrite nth_error_map, E. reflexivity. }
  rewrite Ej. pose proof (bv_unsigned_in_range 8 v) as Hv8. change (bv_modulus 8) with 256 in Hv8.
  split; [|lia].
  intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
  pose proof (H2 j Hj) as Hb. rewrite E in Hb. destruct (Hh (Z.of_nat j) ltac:(lia)) as (Ho & Hhj).
  pose proof (r10_rom_none (a + Z.of_nat j) Ho) as Hr. unfold lib.Lib.Mem.mrd in Hb.
  unfold lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict.
  change (Z_to_bv 64 (a + Z.of_nat j)) with (lib.Lib.Mem.wa (a + Z.of_nat j)). rewrite Hhj.
  destruct (m (lib.Lib.Mem.wa (a + Z.of_nat j))) as [bb|]; [| rewrite Hr in Hb; discriminate].
  injection Hb as ->. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. unfold lib.Reusable.YO0f.le_byte.
  change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  rewrite !Z.mod_small; lia.
Qed.

(* A live block's shadow (YG0v.block_shadow, AR_shadow_law) is range_addressable on any prefix, and gives
   AsanRT.addressable of the prefix where its bytes are read through ctrl's mrd. *)
Lemma r10_ra_of_bs : forall (rd : Z -> option Z) OFF p n len,
  lib.Reusable.YG0v.block_shadow rd OFF p n -> 0 <= len <= n ->
  lib.Reusable.YG0v.range_addressable rd OFF p len.
Proof.
  intros rd OFF p n len (Hp8 & Hn0 & Hsh) Hlen x Hx.
  assert (Ex : lib.Reusable.YG0v.shadow_of_addr OFF x = lib.Reusable.YG0v.shadow_of_addr OFF p + (x - p) / 8).
  { unfold lib.Reusable.YG0v.shadow_of_addr. Z.div_mod_to_equations. nia. }
  rewrite Ex. pose proof (Hsh ((x - p) / 8)) as Hi.
  assert (Hr : 0 <= (x - p) / 8 < (n + 7) / 8) by (Z.div_mod_to_equations; nia).
  specialize (Hi Hr). eexists. split; [exact Hi|].
  unfold lib.Reusable.YG0v.saddr_ok.
  destruct ((x - p) / 8 <? n / 8) eqn:Elt; [left; reflexivity | right].
  apply Z.ltb_ge in Elt. Z.div_mod_to_equations. nia.
Qed.
End Rc.

(* ---------------------------------------------------------------------------------------------------------
   1. The memory facts every arm of R10 carries from its entry to its exit, in the cut layer's vocabulary
   (ACtlCutP.v), and their bridge to R10A.r10a_K (R10A.v:943), the same facts in SlotInv.v's vocabulary over the
   ghost r10_g cx.  Both texts are transcriptions of SlotInv.v; they differ only in PRO's input-block conjunct,
   where SlotInv's carries `In (g_p g, g_n g) (g_H g)` (the ghost's heap, here the one input block) and states
   the length as g_n g = length (g_in g) (the core's pre states n = length pl, ACfn.v:39). *)
Definition r10_g (cx : A.ACtlCut.ctlcx) : A.Prog.SlotInv.ghost :=
  A.Prog.SlotInv.Ghost (A.ACtlCut.c_in cx) (A.ACtlCut.c_p cx) (A.ACtlCut.c_sp cx) (A.ACtlCut.c_regs cx)
    (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx)
    [(A.ACtlCut.c_p cx, Z.of_nat (length (A.ACtlCut.c_in cx)))] [].

Definition r10_N (cx : A.ACtlCut.ctlcx) (b : nat) (phi fr : Z) (regs : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  A.ACtlCutP.HB m phi (A.ACtlCutP.rnb cx b) /\ A.ACtlCutP.OURb cx fr m /\ A.ACtlCutP.OUTA fr m /\
  A.ACtlCutP.spill regs m 112 (A.Prog.SlotModel.mrow (A.ACtlCut.c_in cx)) /\
  A.ACtlCutP.spill regs m 128 (fr + 544) /\ A.ACtlCutP.PRO cx fr regs m /\
  A.ACtlCutP.spill regs m 104 0x21140 /\ A.ACtlCutP.spill regs m 96 0x1234 /\
  A.ACtlCutP.spill regs m 64 0xe38f0000 /\
  A.ACtlCutP.spill regs m 144 (fr + 2688) /\ A.ACtlCutP.spill regs m 192 (fr + 2768) /\
  (exists idb, lib.Lib.Step.rw_cells segs m (fr + 2688) [lib.Lib.Cells.CB 38 idb]) /\
  (exists junk, lib.Lib.Step.rw_cells segs m (fr + 2768) [lib.Lib.Cells.CB 72 junk]) /\
  A.ACtlCutP.spill regs m 280 (fr + 3040) /\ A.ACtlCutP.spill regs m 240 (fr + 3056) /\
  (exists jy, lib.Lib.Step.rw_cells segs m (fr + 3040) [lib.Lib.Cells.CB 1 jy]) /\
  (exists junk, lib.Lib.Step.rw_cells segs m (fr + 3056) [lib.Lib.Cells.CB 32 junk]) /\
  A.ACtlCutP.spill regs m 152 (A.ACtlCutP.Sfr fr + 68) /\ A.AsanRT.addressable m (fr + 2176) 38 /\
  A.ACtlCutP.IDBr cx fr (A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) b) m /\
  A.ACtlCutP.FGBr cx fr (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) b) m /\
  lib.Lib.Mem.bytes_at segs m phi (A.Prog.SlotModel.rt_F (A.ACtlCut.c_in cx) (Z.of_nat b)) /\
  A.ACtlCutP.RXS cx fr regs m.

Lemma r10_N_K : forall cx b phi fr regs m,
  A.ACtlCut.c_n cx = Z.of_nat (length (A.ACtlCut.c_in cx)) ->
  r10_N cx b phi fr regs m -> A.Prog.Seg.R10A.r10a_K (r10_g cx) b phi fr regs m.
Proof.
  intros cx b phi fr regs m Ecn H. unfold r10_N, A.ACtlCutP.PRO in H. rewrite Ecn in H.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
    H18 & H19 & H20 & H21 & H22 & H23).
  unfold A.Prog.Seg.R10A.r10a_K.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split.
  { destruct H6 as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16).
    refine (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 (conj P9 (conj P10 _)))))))))).
    split; [intros Hn; split; [left; reflexivity | exact (P11 Hn)]|].
    exact (conj P12 (conj P13 (conj P14 (conj P15 P16)))). }
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
  split; [exact H11|]. split; [exact H12|]. split; [exact H13|]. split; [exact H14|]. split; [exact H15|].
  split; [exact H16|]. split; [exact H17|]. split; [exact H18|]. split; [exact H19|]. split; [exact H20|].
  split; [exact H21|]. split; [exact H22|]. exact H23.
Qed.

Lemma r10_K_N : forall cx b phi fr regs m,
  A.ACtlCut.c_n cx = Z.of_nat (length (A.ACtlCut.c_in cx)) ->
  A.Prog.Seg.R10A.r10a_K (r10_g cx) b phi fr regs m -> r10_N cx b phi fr regs m.
Proof.
  intros cx b phi fr regs m Ecn H. unfold r10_N, A.ACtlCutP.PRO. rewrite Ecn.
  unfold A.Prog.Seg.R10A.r10a_K in H.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
    H18 & H19 & H20 & H21 & H22 & H23).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split.
  { destruct H6 as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16).
    refine (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 (conj P9 (conj P10 _)))))))))).
    split; [intros Hn; exact (proj2 (P11 Hn))|].
    exact (conj P12 (conj P13 (conj P14 (conj P15 P16)))). }
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
  split; [exact H11|]. split; [exact H12|]. split; [exact H13|]. split; [exact H14|]. split; [exact H15|].
  split; [exact H16|]. split; [exact H17|]. split; [exact H18|]. split; [exact H19|]. split; [exact H20|].
  split; [exact H21|]. split; [exact H22|]. exact H23.
Qed.

(* R10A.r10a_keep (R10A.v:955) for a write window inside the frame shadow, [S(fr) + 306, S(fr) + hi), hi <= 318:
   every disjointness it asks for follows from the placement of the save area, the frame and the two blocks in
   application memory and the blocks' separation from the frame. *)
Lemma r10_N_keep_sh : forall cx b phi fr (regs regs' : bvmap 5 word) (m m' : word -> option byte) hi A,
  r10_N cx b phi fr regs m ->
  A.ACtlCut.c_n cx = Z.of_nat (length (A.ACtlCut.c_in cx)) ->
  lib.Lib.Frame.munch [(A.ACtlCutP.Sfr fr + 306, A.ACtlCutP.Sfr fr + hi)] m m' ->
  lib.Lib.Frame.wmono A.Img0.rsegs m m' ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 -> A.ACtlCut.rgv regs 9 A ->
  0 <= A -> A + 416 < 2 ^ 64 -> (b <= 4)%nat -> 0 <= fr -> fr mod 8 = 0 -> hi <= 318 ->
  (forall x, A <= x < A + 416 -> A.AsanRT.app_mem x) ->
  (forall x, fr <= x < fr + 4096 -> A.AsanRT.app_mem x) ->
  0 <= phi -> 1 <= A.ACtlCutP.rnb cx b -> (phi + A.ACtlCutP.rnb cx b <= fr \/ fr + 4096 <= phi) ->
  (forall x, phi <= x < phi + A.ACtlCutP.rnb cx b -> A.AsanRT.app_mem x) ->
  (0 < A.ACtlCut.c_n cx -> 0 <= A.ACtlCut.c_p cx /\
     (A.ACtlCut.c_p cx + A.ACtlCut.c_n cx <= fr \/ fr + 4096 <= A.ACtlCut.c_p cx) /\
     (forall x, A.ACtlCut.c_p cx <= x < A.ACtlCut.c_p cx + A.ACtlCut.c_n cx -> A.AsanRT.app_mem x)) ->
  r10_N cx b phi fr regs' m'.
Proof.
  pose proof A.Prog.SlotInv.FRAME_BYTES_val as HFRAMEb. pose proof A.Prog.SlotInv.FRAME_SHADOW_val as HFRAMEs.
  intros cx b phi fr regs regs' m m' hi A HN Ecn MU WM E9 HA HA0 HA1 Hb4 Hfr0 Hfr8 Hhi HAapp Hfapp
    Hphi0 Hrnb Hphifr Hphiapp Hin.
  apply (r10_K_N cx b phi fr regs' m' Ecn).
  assert (Hfapp' : forall x, fr <= x < fr + A.Prog.SlotInv.FRAME_BYTES -> A.AsanRT.app_mem x)
    by (intros x Hx; apply Hfapp; lia).
  assert (OUT : forall x, A.AsanRT.app_mem x -> lib.Lib.Frame.outside [(A.ACtlCutP.Sfr fr + 306, A.ACtlCutP.Sfr fr + hi)] x).
  { intros x Hx. apply (A.Prog.Seg.R10B.r10b_appbyte_out fr 306 hi x Hfapp'); lia || exact Hx. }
  apply (A.Prog.Seg.R10A.r10a_keep (r10_g cx) b phi fr regs regs' m m'
           [(A.ACtlCutP.Sfr fr + 306, A.ACtlCutP.Sfr fr + hi)] A (r10_N_K cx b phi fr regs m Ecn HN) MU WM E9 HA
           HA0 HA1 Hb4 Hfr0 Hfr8).
  - intros x Hx. apply OUT, HAapp, Hx.
  - intros x Hx _. apply OUT, Hfapp. lia.
  - intros x Hx. apply OUT, Hphiapp. exact Hx.
  - intros k Hk Hk'. cbn [lib.Lib.Frame.outside]. split; [|exact I].
    unfold A.Prog.SlotInv.Sfr, A.ACtlCutP.Sfr. lia.
  - intros i Hi. change (A.Prog.SlotInv.rnb (r10_g cx) b) with (A.ACtlCutP.rnb cx b) in Hi.
    unfold A.Contract.a_size in Hi.
    apply (A.Prog.Seg.R10B.r10b_shobj_out fr 306 hi phi (A.ACtlCutP.rnb cx b) i Hfr8 Hfr0 Hphi0); [|lia].
    destruct Hphifr as [Hd|Hd]; [left|right]; lia.
  - intros Hn x Hx. assert (Hn' : 0 < A.ACtlCut.c_n cx) by (rewrite Ecn; exact Hn).
    destruct (Hin Hn') as (_ & _ & Happ). apply OUT, Happ. rewrite Ecn. exact Hx.
  - intros Hn i Hi. assert (Hn' : 0 < A.ACtlCut.c_n cx) by (rewrite Ecn; exact Hn).
    destruct (Hin Hn') as (Hp0 & Hd & _).
    apply (A.Prog.Seg.R10B.r10b_shobj_out fr 306 hi (A.ACtlCut.c_p cx) (A.ACtlCut.c_n cx) i Hfr8 Hfr0 Hp0);
      [| rewrite Ecn; exact Hi].
    destruct Hd as [Hd|Hd]; [left|right]; lia.
Qed.

(* A region's shadow bytes stay present across a run that keeps every writable view (wmono): a shadow address lies
   above the image, where a writable view is a present byte (r10_wv_some). *)
Lemma r10_srw_on_wm : forall (P : Z -> Prop) (m m' : word -> option byte),
  A.ShadowRwOn.shadow_rw_on P m -> lib.Lib.Frame.wmono A.Img0.rsegs m m' -> A.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P m m' H WM a Hp Ha. apply A.ShadowRwOn.srw_byte_of_mem.
  destruct (H a Hp Ha) as (Hv & _). pose proof (A.AsanRTFacts.in_shadow_range a Ha) as Hr.
  assert (Hlo : 0x5fe000 <= a)
    by (unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
          A.AsanRT.HIGHMEM_BEG in Ha; lia).
  assert (Hu : bv_unsigned (lib.Lib.Mem.wa a) = a) by (apply lib.Lib.Mem.wa_unsigned; lia).
  exact (r10_wv_some m' (lib.Lib.Mem.wa a) ltac:(rewrite Hu; unfold A.Prog.ImgBounds.IMG_HI; lia) (WM _ Hv)).
Qed.

(* ctl_rt_C across a write window inside the frame shadow (the arms' own metadata stores): asan_cells by
   fl_asan_cells (the window is apart from the runtime cells), each shadow region by r10_srw_on_wm, ro_agree by
   R10A.r10a_ro_munch (the window lies above the image). *)
Lemma r10_rtC_keep_sh : forall (B : lib.Reusable.YG0f.asyms) ly (S : lib.Reusable.YG00.astate)
    (m m' : word -> option byte) fr lo hi,
  A.ACtlRtC.ctl_rt_C B ly S m ->
  lib.Lib.Frame.munch [(A.ACtlCutP.Sfr fr + lo, A.ACtlCutP.Sfr fr + hi)] m m' ->
  lib.Lib.Frame.wmono A.Img0.rsegs m m' ->
  (forall a, fr <= a < fr + 4096 -> A.AsanRT.app_mem a) -> 0 <= lo -> hi <= 392 ->
  A.ACtlRtC.ctl_rt_C B ly S m'.
Proof.
  pose proof A.Prog.SlotInv.FRAME_BYTES_val as HFRAMEb. pose proof A.Prog.SlotInv.FRAME_SHADOW_val as HFRAMEs.
  intros B ly S m m' fr lo hi (HC & HCUT & HIMG & HR) MU WM Happ Hlo Hhi.
  assert (Hfapp : forall x, fr <= x < fr + A.Prog.SlotInv.FRAME_BYTES -> A.AsanRT.app_mem x)
    by (intros x Hx; apply Happ; lia).
  assert (Hsh : forall x, A.ACtlCutP.Sfr fr + lo <= x < A.ACtlCutP.Sfr fr + hi -> A.AsanRT.in_shadow x).
  { intros x Hx. replace x with (A.ACtlCutP.Sfr fr + (x - A.ACtlCutP.Sfr fr)) by lia.
    apply A.Prog.Seg.R10B.r10b_fsh; [exact Hfapp | lia]. }
  assert (Hlow : forall x, ~ lib.Lib.Frame.outside [(A.ACtlCutP.Sfr fr + lo, A.ACtlCutP.Sfr fr + hi)] x ->
                  0x5fe000 <= x).
  { intros x Hx. assert (Hx' : A.ACtlCutP.Sfr fr + lo <= x < A.ACtlCutP.Sfr fr + hi).
    { destruct (Z_le_gt_dec (A.ACtlCutP.Sfr fr + lo) x); destruct (Z_lt_ge_dec x (A.ACtlCutP.Sfr fr + hi));
        try lia; exfalso; apply Hx; cbn [lib.Lib.Frame.outside]; split; try exact I; lia. }
    pose proof (Hsh x Hx') as Hs. unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END,
      A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG in Hs. lia. }
  split; [|split; [|split]].
  - apply (A.Prog.RcAsanFPLib.fl_asan_cells _ m m' HC MU). intros x Hx.
    cbn [lib.Lib.Frame.outside]. split; [|exact I]. intros Hx'. pose proof (Hsh x Hx') as Hs.
    unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI in Hx.
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG in Hs. lia.
  - exact (r10_srw_on_wm _ m m' HCUT WM).
  - exact (r10_srw_on_wm _ m m' HIMG WM).
  - exact (A.Prog.Seg.R10A.r10a_ro_munch _ m m' HR MU Hlow).
Qed.

(* FRAC (ACtlCutP.v:980) across a run that keeps its seven registers and misses its memory, except that the 392
   frame-shadow bytes may change as long as each still reads back. *)
Lemma r10_frac_keep : forall B cx fr (regs regs' : bvmap 5 word) (m m' : word -> option byte) W A,
  A.ACtlCutP.FRAC B cx fr fr regs m -> A.ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  lib.Lib.Frame.munch W m m' ->
  (forall x, A <= x < A + 416 -> lib.Lib.Frame.outside W x) ->
  (forall x, fr <= x < fr + 24 -> lib.Lib.Frame.outside W x) ->
  (forall x, fr + 4088 <= x < fr + 4096 -> lib.Lib.Frame.outside W x) ->
  (forall x, A.ACtlCut.c_sp cx - 104 <= x < A.ACtlCut.c_sp cx -> lib.Lib.Frame.outside W x) ->
  (forall x, A.ACtlCutP.Sfr fr <= x < A.ACtlCutP.Sfr fr + 392 ->
     lib.Lib.Frame.outside W x \/ exists bb, lib.Lib.Mem.mrd A.Img0.rsegs m' (lib.Lib.Mem.wa x) = Some bb) ->
  A.ACtlCutP.FRAC B cx fr fr regs' m'.
Proof.
  intros B cx fr regs regs' m m' W A0 HF HA0 HA0r E2 E3 E4 E8 E9 E19 E26 MU OA OF OT OS OSH.
  destruct HF as (A & sp & R2 & Hsp16 & Hspz & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAS & HspA & HfrA &
    HA416 & HSsp & HSapp & Q304 & Q24 & Q16 & QH0 & QH16 & (sh & Bsh & Lsh) & Bsv & Qtr).
  assert (EA : A = A0).
  { pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 2)) as Hu.
    change (bv_modulus 64) with (2 ^ 64) in Hu. unfold lib.Reusable.YG0d.spZ in Hspz.
    unfold A.ACtlCut.rgv in R9, HA0. rewrite R9 in HA0. apply (f_equal bv_unsigned) in HA0.
    rewrite !Z_to_bv_unsigned in HA0. unfold bv_wrap in HA0. unfold A.ACtlCutP.FRAME_BYTES in HfrA.
    unfold A.AsanRT.APPMEM_END in HSapp. change (bv_modulus 64) with (2 ^ 64) in HA0.
    rewrite !Z.mod_small in HA0; lia. }
  subst A0.
  assert (FB : forall a l, lib.Lib.Mem.bytes_at A.Img0.rsegs m a l ->
                 (forall x, a <= x < a + Z.of_nat (length l) -> lib.Lib.Frame.outside W x) ->
                 lib.Lib.Mem.bytes_at A.Img0.rsegs m' a l).
  { intros a l Hb Ho. exact (A.Prog.RcAsanFPLib.fl_bytes W m m' a l Hb MU Ho). }
  unfold A.ACtlCutP.FRAME_BYTES in HfrA.
  exists A, sp.
  split; [exact (eq_trans E2 R2)|]. split; [exact Hsp16|].
  split; [unfold lib.Reusable.YG0d.spZ in *; rewrite <- Hspz; exact (f_equal bv_unsigned E2)|].
  split; [exact (eq_trans E4 R4)|]. split; [exact (eq_trans E8 R8)|]. split; [exact (eq_trans E9 R9)|].
  split; [exact E3 || exact (eq_trans E3 R3)|]. split; [exact (eq_trans E19 R19)|].
  split; [exact (eq_trans E26 R26)|].
  split; [exact Hfr32|]. split; [exact HA32|]. split; [exact HAS|]. split; [exact HspA|].
  split; [unfold A.ACtlCutP.FRAME_BYTES; exact HfrA|]. split; [exact HA416|]. split; [exact HSsp|].
  split; [exact HSapp|].
  split; [apply (FB _ _ Q304); intros x Hx; apply OA; rewrite lib.Lib.Mem.length_le8 in Hx; cbn in Hx; lia|].
  split; [apply (FB _ _ Q24); intros x Hx; apply OA; rewrite lib.Lib.Mem.length_le8 in Hx; cbn in Hx; lia|].
  split; [apply (FB _ _ Q16); intros x Hx; apply OA; rewrite lib.Lib.Mem.length_le8 in Hx; cbn in Hx; lia|].
  split; [apply (FB _ _ QH0); intros x Hx; apply OF; rewrite lib.Lib.Mem.length_le8 in Hx; cbn in Hx; lia|].
  split; [apply (FB _ _ QH16); intros x Hx; apply OF; rewrite lib.Lib.Mem.length_le8 in Hx; cbn in Hx; lia|].
  split.
  - pose proof Bsh as (Hsh0 & Hsh1 & Hsh). change (Z.to_nat A.ACtlCutP.FRAME_SHADOW) with 392%nat in Lsh.
    destruct (A.Prog.Seg.R10B.r10b_bytes_of_present 392 m' (A.ACtlCutP.Sfr fr) ltac:(lia)
                ltac:(rewrite Lsh in Hsh1; exact Hsh1)) as (sh' & Bsh' & Lsh').
    { intros k Hk. destruct (OSH (A.ACtlCutP.Sfr fr + Z.of_nat k) ltac:(lia)) as [Ho|Hrd]; [|exact Hrd].
      destruct (A.Prog.Seg.R10B.r10b_ba_rd m (A.ACtlCutP.Sfr fr) sh (A.ACtlCutP.Sfr fr + Z.of_nat k) Bsh
                  ltac:(rewrite Lsh; lia)) as (bb & Hbb).
      exists bb. unfold lib.Lib.Mem.mrd in *. rewrite MU; [exact Hbb|].
      rewrite lib.Lib.Mem.wa_unsigned by lia. exact Ho. }
    exists sh'. split; [exact Bsh' | rewrite Lsh'; reflexivity].
  - split.
    + apply (FB _ _ Bsv). intros x Hx. apply OS.
      unfold A.ACtlCutP.saved_bytes in Hx. rewrite !length_app, !lib.Lib.Mem.length_le8 in Hx. cbn in Hx. lia.
    + (* the fake frame's trailer word (FRAC's last conjunct, glue base batch 3) *)
      apply (FB _ _ Qtr). intros x Hx. apply OT. rewrite lib.Lib.Mem.length_le8 in Hx. cbn in Hx. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   1b. Carrying the cut's memory facts across the reply call (arm b = 3, 4).  r10_cp is a byte the call keeps:
   no segment covers it, it is visible before the call, and the call's post keeps its view (tcj_kept). *)
Section Carry.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.

Definition r10_cp (H H' : word -> bool) (m m' : word -> option byte) (x : Z) : Prop :=
  r10_off x /\ H (lib.Lib.Mem.wa x) = false /\
  lib.Reusable.YG0n.aview segs H' m' x = lib.Reusable.YG0n.aview segs H m x.

Lemma r10_cp_bytes : forall H H' (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> r10_cp H H' m m' x) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a l -> lib.Lib.Mem.bytes_at A.Img0.rsegs m' a l.
Proof. intros H H' m m' a l Hc. apply (r10_carry_bytes H H'). intros i Hi. exact (Hc (a + i) ltac:(lia)). Qed.

Lemma r10_cp_q64 : forall H H' (m m' : word -> option byte) a v,
  (forall x, a <= x < a + 8 -> r10_cp H H' m m' x) -> A.ACtlCutP.q64 m a v -> A.ACtlCutP.q64 m' a v.
Proof.
  intros H H' m m' a v Hc Hq. apply (r10_cp_bytes H H' m); [|exact Hq].
  intros x Hx. apply Hc. rewrite lib.Lib.Mem.length_le8 in Hx. cbn in Hx. lia.
Qed.

Lemma r10_cp_spill : forall H H' (regs regs' : bvmap 5 word) (m m' : word -> option byte) off v A,
  A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 < 2 ^ 64 -> 0 <= off <= 408 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A + off <= x < A + off + 8 -> r10_cp H H' m m' x) ->
  A.ACtlCutP.spill regs m off v -> A.ACtlCutP.spill regs' m' off v.
Proof.
  intros H H' regs regs' m m' off v A HA HA0 HA1 Hoff E9 Hc Hs.
  pose proof (A.Prog.Seg.R10A.r10a_spill_at regs m A off v HA HA0 HA1 ltac:(lia) Hs) as Hq.
  exists A. split; [unfold A.ACtlCut.rgv in *; rewrite E9; exact HA|].
  exact (r10_cp_q64 H H' m m' (A + off) v Hc Hq).
Qed.

Lemma r10_cp_addr : forall H H' (m m' : word -> option byte) p n,
  (forall i, 0 <= i < n -> r10_cp H H' m m' (A.AsanRT.shadow_addr (p + i))) ->
  A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n.
Proof.
  intros H H' m m' p n Hc. apply (r10_carry_addr H H'). intros i Hi.
  destruct (Hc i Hi) as (_ & Hh & Hv). split; [exact Hh | exact Hv].
Qed.

Lemma r10_cp_rw : forall H H' (m m' : word -> option byte) a n l,
  (forall x, a <= x < a + Z.of_nat n -> r10_cp H H' m m' x) ->
  lib.Lib.Step.rw_cells A.Img0.rsegs m a [lib.Lib.Cells.CB n l] ->
  lib.Lib.Step.rw_cells A.Img0.rsegs m' a [lib.Lib.Cells.CB n l].
Proof.
  intros H H' m m' a n l Hc ((Hwf & Hb) & _).
  cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf] in Hwf. destruct Hwf as (Hl & _).
  cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hb. rewrite app_nil_r in Hb.
  assert (Hb' : lib.Lib.Mem.bytes_at A.Img0.rsegs m' a l).
  { apply (r10_cp_bytes H H' m); [|exact Hb]. rewrite Hl. exact Hc. }
  rewrite <- Hl. apply A.Prog.Seg.R10A.r10a_rw_CB; [exact Hb'|].
  apply r10_wr_of_bytes; [|exact Hb']. intros i Hi. rewrite Hl in Hi. exact (proj1 (Hc (a + i) ltac:(lia))).
Qed.

Lemma r10_signed_small : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros k H. pose proof (bv_unsigned_in_range 8 k) as R. unfold bv_modulus in R. cbn in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8 / 2) with 128. change (2 ^ Z.of_N 8) with 256.
  Z.div_mod_to_equations. lia.
Qed.

(* A live block's view shadow (YG0v.block_shadow, AR_shadow_law) is ctrl's AsanRT.addressable of the block. *)
Lemma r10_addr_of_bs : forall (H : word -> bool) (m : word -> option byte) p n,
  lib.Reusable.YG0v.block_shadow (lib.Reusable.YG0n.aview segs H m) lib.Reusable.YG0f.SHADOW_OFF p n ->
  0 <= p -> p + n <= A.AsanRT.APPMEM_END -> (forall x, p <= x < p + n -> A.AsanRT.app_mem x) ->
  A.AsanRT.addressable m p n.
Proof.
  intros H m p n (Hp8 & Hn0 & Hsh) Hp0 HpE Happ.
  split; [exact Hp0|]. split; [exact Hn0|]. split; [exact HpE|].
  intros i Hi. split; [apply Happ; lia|].
  pose proof (Hsh (i / 8) ltac:(Z.div_mod_to_equations; lia)) as Hv.
  replace (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF p + i / 8)
    with (A.AsanRT.shadow_addr (p + i)) in Hv
    by (unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0v.shadow_of_addr,
          lib.Reusable.YG0f.SHADOW_OFF; Z.div_mod_to_equations; lia).
  assert (Ho : r10_off (A.AsanRT.shadow_addr (p + i))).
  { apply r10_off_hi. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, A.Prog.ImgBounds.IMG_HI.
    unfold A.AsanRT.APPMEM_END in HpE. Z.div_mod_to_equations. lia. }
  destruct (r10_rd_of_view H m _ _ Ho Hv) as (_ & b & _ & Hb & Hrd).
  exists b. split; [exact Hrd|]. unfold A.AsanRT.shadow_ok.
  destruct (i / 8 <? n / 8) eqn:E.
  - left. rewrite r10_signed_small; lia.
  - right. apply Z.ltb_ge in E. rewrite r10_signed_small by (rewrite Hb; pose proof (Z.mod_pos_bound n 8); lia).
    rewrite Hb. Z.div_mod_to_equations. lia.
Qed.

Lemma r10_frac_view : forall B cx fr (regs regs' : bvmap 5 word) (m m' : word -> option byte) H H' A,
  A.ACtlCutP.FRAC B cx fr fr regs m -> A.ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  (forall x, A <= x < A + 416 -> r10_cp H H' m m' x) ->
  (forall x, fr <= x < fr + 24 -> r10_cp H H' m m' x) ->
  (forall x, fr + 4088 <= x < fr + 4096 -> r10_cp H H' m m' x) ->
  (forall x, A.ACtlCut.c_sp cx - 104 <= x < A.ACtlCut.c_sp cx -> r10_cp H H' m m' x) ->
  (forall x, A.ACtlCutP.Sfr fr <= x < A.ACtlCutP.Sfr fr + 392 -> r10_cp H H' m m' x) ->
  A.ACtlCutP.FRAC B cx fr fr regs' m'.
Proof.
  intros B cx fr regs regs' m m' H H' A0 HF HA0 HA0r E2 E3 E4 E8 E9 E19 E26 OA OF OT OS OSH.
  destruct HF as (A & sp & R2 & Hsp16 & Hspz & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAS & HspA & HfrA &
    HA416 & HSsp & HSapp & Q304 & Q24 & Q16 & QH0 & QH16 & (sh & Bsh & Lsh) & Bsv & Qtr).
  assert (EA : A = A0).
  { pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 2)) as Hu.
    change (bv_modulus 64) with (2 ^ 64) in Hu. unfold lib.Reusable.YG0d.spZ in Hspz.
    unfold A.ACtlCut.rgv in R9, HA0. rewrite R9 in HA0. apply (f_equal bv_unsigned) in HA0.
    rewrite !Z_to_bv_unsigned in HA0. unfold bv_wrap in HA0. unfold A.ACtlCutP.FRAME_BYTES in HfrA.
    unfold A.AsanRT.APPMEM_END in HSapp. change (bv_modulus 64) with (2 ^ 64) in HA0.
    rewrite !Z.mod_small in HA0; lia. }
  subst A0. unfold A.ACtlCutP.FRAME_BYTES in HfrA.
  exists A, sp.
  split; [exact (eq_trans E2 R2)|]. split; [exact Hsp16|].
  split; [unfold lib.Reusable.YG0d.spZ in *; rewrite <- Hspz; exact (f_equal bv_unsigned E2)|].
  split; [exact (eq_trans E4 R4)|]. split; [exact (eq_trans E8 R8)|]. split; [exact (eq_trans E9 R9)|].
  split; [exact (eq_trans E3 R3)|]. split; [exact (eq_trans E19 R19)|].
  split; [exact (eq_trans E26 R26)|].
  split; [exact Hfr32|]. split; [exact HA32|]. split; [exact HAS|]. split; [exact HspA|].
  split; [unfold A.ACtlCutP.FRAME_BYTES; exact HfrA|]. split; [exact HA416|]. split; [exact HSsp|].
  split; [exact HSapp|].
  split; [apply (r10_cp_q64 H H' m); [intros x Hx; apply OA; lia | exact Q304]|].
  split; [apply (r10_cp_q64 H H' m); [intros x Hx; apply OA; lia | exact Q24]|].
  split; [apply (r10_cp_q64 H H' m); [intros x Hx; apply OA; lia | exact Q16]|].
  split; [apply (r10_cp_q64 H H' m); [intros x Hx; apply OF; lia | exact QH0]|].
  split; [apply (r10_cp_q64 H H' m); [intros x Hx; apply OF; lia | exact QH16]|].
  split.
  - exists sh. split; [|exact Lsh]. apply (r10_cp_bytes H H' m); [|exact Bsh].
    intros x Hx. apply OSH. rewrite Lsh in Hx. change (Z.of_nat (Z.to_nat A.ACtlCutP.FRAME_SHADOW)) with 392 in Hx.
    lia.
  - split.
    + apply (r10_cp_bytes H H' m); [|exact Bsv]. intros x Hx. apply OS.
      unfold A.ACtlCutP.saved_bytes in Hx. rewrite !length_app, !lib.Lib.Mem.length_le8 in Hx. cbn in Hx. lia.
    + (* the fake frame's trailer word (FRAC's last conjunct, glue base batch 3) *)
      apply (r10_cp_q64 H H' m); [intros x Hx; apply OT; lia | exact Qtr].
Qed.

(* r10_N across the reply call: every frame, stack, block and input byte it names is a kept byte; the block
   shadow facts (HB, PRO's input addressability) are re-established from AR at the post instead. *)
Lemma r10_N_view : forall cx b phi fr (regs regs' : bvmap 5 word) (m m' : word -> option byte) H H' A,
  r10_N cx b phi fr regs m -> A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 < 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A <= x < A + 416 -> r10_cp H H' m m' x) ->
  (forall x, fr + 544 <= x < fr + 2448 \/ fr + 2504 <= x < fr + 3136 -> r10_cp H H' m m' x) ->
  (forall x, A.ACtlCutP.Sfr fr <= x < A.ACtlCutP.Sfr fr + 392 -> r10_cp H H' m m' x) ->
  (forall x, phi <= x < phi + A.ACtlCutP.rnb cx b -> r10_cp H H' m m' x) ->
  (forall x, A.ACtlCut.c_p cx <= x < A.ACtlCut.c_p cx + Z.of_nat (length (A.ACtlCut.c_in cx)) ->
     r10_cp H H' m m' x) ->
  0 <= fr -> fr mod 8 = 0 -> (b <= 4)%nat ->
  A.ACtlCutP.HB m' phi (A.ACtlCutP.rnb cx b) ->
  (0 < A.ACtlCut.c_n cx -> A.AsanRT.addressable m' (A.ACtlCut.c_p cx) (A.ACtlCut.c_n cx)) ->
  r10_N cx b phi fr regs' m'.
Proof.
  intros cx b phi fr regs regs' m m' H H' A HN HA HA0 HA1 E9 CS CF CSh CP CI Hfr0 Hfr8 Hb4 HB' HI'.
  destruct HN as (_ & HOUR & HOUTA & S112 & S128 & HPRO & S104 & S96 & S64 & S144 & S192 & (idb & C2688) &
    (j1 & C2768) & S280 & S240 & (jy & C3040) & (j2 & C3056) & S152 & A2176 & HID & HFG & HPHI & HRXS).
  destruct (A.Prog.Seg.R10A.r10a_lens (A.ACtlCut.c_in cx) b Hb4) as (LF & LI & LG).
  assert (SP : forall off v, 0 <= off <= 408 -> A.ACtlCutP.spill regs m off v -> A.ACtlCutP.spill regs' m' off v).
  { intros off v Ho Hs. apply (r10_cp_spill H H' regs regs' m m' off v A HA HA0 HA1 Ho E9); [|exact Hs].
    intros x Hx. apply CS. lia. }
  assert (AD : forall k n, 544 <= k -> k + n <= 3136 -> A.AsanRT.addressable m (fr + k) n ->
                 A.AsanRT.addressable m' (fr + k) n).
  { intros k n Hk Hn Ha. apply (r10_cp_addr H H' m); [|exact Ha]. intros i Hi. apply CSh.
    unfold A.ACtlCutP.Sfr, A.AsanRT.shadow_addr. Z.div_mod_to_equations. lia. }
  assert (FB : forall k l, (544 <= k /\ k + Z.of_nat (length l) <= 2448 \/
                            2504 <= k /\ k + Z.of_nat (length l) <= 3136) ->
                 lib.Lib.Mem.bytes_at A.Img0.rsegs m (fr + k) l -> lib.Lib.Mem.bytes_at A.Img0.rsegs m' (fr + k) l).
  { intros k l Hk Hb. apply (r10_cp_bytes H H' m); [|exact Hb]. intros x Hx. apply CF. lia. }
  assert (FR : forall k n l, 2504 <= k -> k + Z.of_nat n <= 3136 ->
                 lib.Lib.Step.rw_cells A.Img0.rsegs m (fr + k) [lib.Lib.Cells.CB n l] ->
                 lib.Lib.Step.rw_cells A.Img0.rsegs m' (fr + k) [lib.Lib.Cells.CB n l]).
  { intros k n l Hk Hn Hc. apply (r10_cp_rw H H' m); [|exact Hc]. intros x Hx. apply CF. lia. }
  destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & PA2624 & PIN & PINA & P184 & P256 &
    P264 & P272 & P32).
  destruct HRXS as (X48 & X56 & X88 & X80 & X72 & X8 & X0 & X200 & X216 & XA).
  unfold r10_N, A.ACtlCutP.PRO, A.ACtlCutP.RXS, A.ACtlCutP.OURb, A.ACtlCutP.OUTA, A.ACtlCutP.IDBr,
    A.ACtlCutP.FGBr in *.
  split; [exact HB'|].
  split; [apply FB; [rewrite A.Prog.SlotModel.OUR_length; cbn; lia | exact HOUR]|].
  split; [apply AD; [lia | lia | exact HOUTA]|].
  split; [apply SP; [lia | exact S112]|]. split; [apply SP; [lia | exact S128]|].
  split.
  { split; [apply SP; [lia | exact P40]|]. split; [apply SP; [lia | exact P120]|].
    split; [apply SP; [lia | exact P136]|]. split; [apply SP; [lia | exact P160]|].
    split; [apply SP; [lia | exact P168]|]. split; [apply SP; [lia | exact P176]|].
    split; [apply SP; [lia | exact P208]|]. split; [apply SP; [lia | exact P248]|].
    split; [apply AD; [lia | lia | exact PA2624]|].
    split; [apply (r10_cp_bytes H H' m); [exact CI | exact PIN]|].
    split; [exact HI'|].
    split; [apply SP; [lia | exact P184]|]. split; [apply SP; [lia | exact P256]|].
    split; [apply SP; [lia | exact P264]|]. split; [apply SP; [lia | exact P272]|].
    apply SP; [lia | exact P32]. }
  split; [apply SP; [lia | exact S104]|]. split; [apply SP; [lia | exact S96]|].
  split; [apply SP; [lia | exact S64]|]. split; [apply SP; [lia | exact S144]|].
  split; [apply SP; [lia | exact S192]|].
  split; [exists idb; apply FR; [lia | lia | exact C2688]|].
  split; [exists j1; apply FR; [lia | lia | exact C2768]|].
  split; [apply SP; [lia | exact S280]|]. split; [apply SP; [lia | exact S240]|].
  split; [exists jy; apply FR; [lia | lia | exact C3040]|].
  split; [exists j2; apply FR; [lia | lia | exact C3056]|].
  split; [apply SP; [lia | exact S152]|].
  split; [apply AD; [lia | lia | exact A2176]|].
  split; [apply FB; [rewrite LI; cbn; lia | exact HID]|].
  split; [apply FB; [rewrite LG; cbn; lia | exact HFG]|].
  split; [apply (r10_cp_bytes H H' m); [rewrite LF; exact CP | exact HPHI]|].
  split; [apply SP; [lia | exact X48]|]. split; [apply SP; [lia | exact X56]|].
  split; [apply SP; [lia | exact X88]|]. split; [apply SP; [lia | exact X80]|].
  split; [apply SP; [lia | exact X72]|]. split; [apply SP; [lia | exact X8]|].
  split; [apply SP; [lia | exact X0]|]. split; [apply SP; [lia | exact X200]|].
  split; [apply SP; [lia | exact X216]|].
  apply AD; [lia | lia | exact XA].
Qed.

Lemma r10_unrestrict_bytes : forall (H : word -> bool) (m : word -> option byte) a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> r10_off (a + i)) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs (lib.Reusable.YK04.mrestrict H m) a l ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a l.
Proof.
  intros H m a l Ho (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. pose proof (H2 i Hi) as Hb. pose proof (r10_rom_none _ (Ho (Z.of_nat i) ltac:(lia))) as Hr.
  unfold lib.Lib.Mem.mrd, lib.Reusable.YK04.mrestrict in *.
  destruct (H (lib.Lib.Mem.wa (a + Z.of_nat i))); [|exact Hb].
  rewrite Hr in Hb. destruct (nth_error l i) eqn:E; [discriminate | apply nth_error_None in E; lia].
Qed.

Lemma r10_bytes_of_garr8 : forall (H : word -> bool) (m : word -> option byte) a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> r10_off (a + i)) -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  lib.Reusable.YI00.garr8 segs (lib.Reusable.YK04.mrestrict H m) a (map (fun b : byte => bv_unsigned b) l) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a l.
Proof.
  intros H m a l Ho Ha0 Ha1 Hg. apply (r10_unrestrict_bytes H m a l Ho).
  split; [exact Ha0|]. split; [exact Ha1|]. intros i Hi.
  destruct (nth_error l i) as [v|] eqn:E; [| apply nth_error_None in E; lia].
  destruct (Hg i ltac:(rewrite length_map; exact Hi)) as (Hv & _).
  assert (Ej : nth i (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned v).
  { apply nth_error_nth. rewrite nth_error_map, E. reflexivity. }
  rewrite Ej in Hv. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv.
  transitivity (Some (Z_to_bv 8 (lib.Reusable.YO0f.le_byte (bv_unsigned v) 1 0))); [exact Hv|].
  f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. unfold lib.Reusable.YO0f.le_byte.
  change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  pose proof (bv_unsigned_in_range 8 v) as Hv8. change (bv_modulus 8) with 256 in Hv8.
  rewrite !Z.mod_small; lia.
Qed.
End Carry.

Section GlueR10.

(* ACtl.v's Section shape (ACtl.v:170-194), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
(* ACtl.v's own Section hypotheses (ACtl.v:179, :183, :191), same texts. *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img segs a.
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* ---- arm b = 3, 4: the cgif-form spec of reac_ctrl_identity_reply, cited at the SPLIT POINT (a Theorem Labs lane 03:14Z).
   REPLY_SPEC has the text of ACtl.v's Section hypothesis TREPLY (ACtl.v:304 at a working branch 1899bed1aee): a Theorem Labs lane's
   treac_ctrl_identity_reply_spec, cited by name from lib/A/Prog/C_reac_ctrl_identity_reply.v.  It stays a
   hypothesis for the reason ACtl.v gives at :311-314 (a Theorem Labs lane's pb_reac_ctrl_identity_reply takes six PA-layer laws at B
   that the base does not prove).  It takes no shadow premise, so route (C) changes nothing in it. *)
Hypothesis REPLY_SPEC :
  A.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI.

(* ACtl.v's notation block, verbatim. *)
Local Notation ix_cut := A.ACtlCut.ix_cut.
Local Notation CF POST X :=
  (A.ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81680_at := (A.ACtlCutP.C_A81680_at B).
Local Notation C_A816c4_at := (A.ACtlCutP.C_A816c4_at B).
Local Notation C_A81708_at := (A.ACtlCutP.C_A81708_at B).
Local Notation C_A81768_at := (A.ACtlCutP.C_A81768_at B).
Local Notation C_A817c8_at := (A.ACtlCutP.C_A817c8_at B).
Local Notation C_A817ec_at := (A.ACtlCutP.C_A817ec_at B).

Local Notation journal cx ly3 S3 W3 mem3 md3 k :=
  (lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) []
     (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx)
     (A.ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k).

(* ---------------------------------------------------------------------------------------------------------
   2. Placement facts at an owning cut of the round trip (frames S3 = own6, the frame law). *)
Lemma r10_geo : forall cx fr k ly3 S3 W3 mem3 md3,
  journal cx ly3 S3 W3 mem3 md3 k ->
  lib.Reusable.YG01.frames S3 = A.ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (A.ACtlCut.own6 cx) ->
     fr = lib.Reusable.YG0f.frame_addr (A.ACtlCut.c_ly cx) cid pos) ->
  fr = lib.Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) /\
  4096 <= fr /\ fr + 4096 + A.ACfn.LLVMF_STK <= A.ACtlCut.c_sp cx /\
  (forall x, fr <= x < fr + 4096 -> A.AsanRT.app_mem x) /\
  0x7fff7f800000 + A.ACfn.LLVMF_STK <= A.ACtlCut.c_sp cx /\ A.ACtlCut.c_sp cx <= 2 ^ 47 /\
  lib.Reusable.YG0n.AR segs B ly3 S3 W3 mem3 md3.
Proof.
  intros cx fr k ly3 S3 W3 mem3 md3 HJ HF HL.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  assert (Hin : In (6, A.ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (lib.Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR Hin)
    as (H4096 & Hceil & Happ).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Efr : fr = lib.Reusable.YG0f.frame_addr (A.ACtlCut.c_ly cx) 6 (A.ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr' : fr = lib.Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx)).
  { rewrite Efr. unfold lib.Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  assert (E6 : lib.Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite E6, <- Efr' in *.
  destruct Hstk as (_ & _ & Hc1 & Hc2 & Hc4 & Hc3 & _).
  pose proof lib.Reusable.YCbq.asan_consts as (HAC & _).
  split; [reflexivity|]. split; [exact H4096|]. split; [lia|].
  split; [exact (r10_in_app_mem fr 4096 Happ)|]. split; [lia|]. split; [lia|]. exact HAR.
Qed.

(* The frame-shadow bytes of the owned frame are visible in the cut's world (AR_frames_law, YG0d.v:447). *)
Lemma r10_fsh_vis : forall cx fr ly3 S3 W3 mem3 md3,
  lib.Reusable.YG0n.AR segs B ly3 S3 W3 mem3 md3 ->
  lib.Reusable.YG01.frames S3 = A.ACtlCut.own6 cx ->
  fr = lib.Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) -> 0 <= fr ->
  forall lo len, 0 <= lo -> 0 <= len -> lo + len <= 512 ->
  A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) (A.ACtlCutP.Sfr fr + lo) len.
Proof.
  intros cx fr ly3 S3 W3 mem3 md3 HAR HF Efr Hfr0 lo len Hlo Hlen Hle.
  assert (Hin : In (6, A.ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR Hin)
    as (_ & Happ & _ & Hsh).
  rewrite <- Efr in Happ, Hsh.
  assert (E6 : lib.Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite E6 in Happ, Hsh. change (4096 / 8) with 512 in Hsh.
  pose proof (r10_in_app_mem fr 4096 Happ) as Hfa.
  pose proof (Hfa (fr + 4095) ltac:(lia)) as Ha1.
  unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in Ha1.
  unfold A.ProgBridge.range_visible, A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
  pose proof (Z.div_pos fr 8 Hfr0 ltac:(lia)).
  pose proof (Z.div_le_mono fr (2 ^ 47) 8 ltac:(lia) ltac:(lia)).
  split; [lia|]. split; [lia|].
  intros a Ha. destruct (Hsh (a - (fr / 8 + 2147450880)) ltac:(lia)) as ((Hh & _) & _).
  replace (lib.Reusable.YG0f.shadow_addr fr + (a - (fr / 8 + 2147450880))) with a in Hh
    by (unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF; lia).
  exact Hh.
Qed.

(* The journal across a run whose only writes are a window of the owned frame's shadow, [S(fr) + lo, S(fr) + hi):
   YCbq.ajournal_exec (YCbq.v:636) with Wr := that window, each byte of which is awr_byte's in_frames case (the
   owned class-6 frame's shadow, fs_frame_bytes 6 / 8 = 512 bytes). *)
Lemma r10_journal_sh : forall cx fr k ly3 S3 W3 mem3 md3 (m' : word -> option byte) md' lo hi,
  journal cx ly3 S3 W3 mem3 md3 k ->
  fr = lib.Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) -> 0 <= fr ->
  0 <= lo -> hi <= 512 ->
  lib.Lib.Frame.munch [(A.ACtlCutP.Sfr fr + lo, A.ACtlCutP.Sfr fr + hi)] mem3 m' ->
  lib.Lib.Frame.wmono A.Img0.rsegs mem3 m' ->
  (forall x : word, lib.Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) ->
  lib.Reusable.YK04.same_but_materialized md3 md' ->
  journal cx ly3 S3 W3 m' md' k.
Proof.
  intros cx fr k ly3 S3 W3 mem3 md3 m' md' lo hi HJ Efr Hfr0 Hlo Hhi MU WM Hhid Hsbm.
  assert (HSh : 2147450880 <= A.ACtlCutP.Sfr fr).
  { unfold A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. pose proof (Z.div_pos fr 8 Hfr0 ltac:(lia)).
    lia. }
  eapply (lib.Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
    with (Wr := fun a => A.ACtlCutP.Sfr fr + lo <= a < A.ACtlCutP.Sfr fr + hi).
  - exact HJ.
  - intros x Hx. unfold lib.Reusable.YK04.mrestrict.
    destruct (lib.Reusable.YA0n.w_H W3 x); [reflexivity|].
    apply MU. cbn [lib.Lib.Frame.outside]. split; [exact Hx | exact I].
  - intros x Hx. unfold lib.Reusable.YK04.mrestrict in *.
    destruct (lib.Reusable.YA0n.w_H W3 x); [exact Hx|].
    destruct (Z_le_gt_dec (A.ACtlCutP.Sfr fr + lo) (bv_unsigned x));
      [destruct (Z_lt_ge_dec (bv_unsigned x) (A.ACtlCutP.Sfr fr + hi))|].
    + apply r10_wv_some; [unfold A.Prog.ImgBounds.IMG_HI; lia|]. apply WM.
      unfold wview. destruct (mem3 x); [discriminate | exfalso; apply Hx; reflexivity].
    + rewrite MU; [exact Hx|]. cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
    + rewrite MU; [exact Hx|]. cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
  - exact Hhid.
  - exact Hsbm.
  - intros a Ha. right; right; right. exists 6, (A.ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
    unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
    change (lib.Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
    unfold A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
    unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. lia.
Qed.

(* The read-only data fact of the entry (ctl_base, ACfn.v:41) at every journalled state (ajournal's F3 conjunct,
   as APostBase.arodata_ok_journalP; FP = [] has no open sink, so fp_spares holds everywhere). *)
Lemma r10_aro : forall cx ly3 S3 W3 mem3 md3 k,
  A.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  journal cx ly3 S3 W3 mem3 md3 k ->
  lib.Reusable.YE01.arodata_okS segs B RLO RHI (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) mem3).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k HB HJ.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _) & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  intros a Ha Ho He. rewrite (F3 a); [exact (HRO a Ha Ho He) | | exact Ho | exact He | ].
  - destruct Ha as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hr)].
  - apply lib.Reusable.YCbq.fp_spares_closed. intros (e & He' & _). destruct He'.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2b. Route (C): the cut's runtime conjunct is ctl_rt_C B ly3 S3 mem3 (ACtlCut.v:243).  The owned frame's shadow
   is its (F) region; at every exit the next cut's ctl_rt_C comes from the exit journal's AR. *)
Lemma r10_cut_fsh : forall cx fr ly3 S3 a,
  In (6, A.ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3) ->
  fr = lib.Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) ->
  A.ACtlCutP.Sfr fr <= a < A.ACtlCutP.Sfr fr + 512 -> A.ACtlRtC.cut_shadow B ly3 S3 a.
Proof.
  intros cx fr ly3 S3 a Hin Efr Ha. left. exists 6, (A.ACtlCut.c_fpos cx). split; [exact Hin|].
  rewrite <- Efr. change (lib.Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
  unfold A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
  unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. lia.
Qed.

Lemma r10_rtC_exit : forall cx ly S W m md k,
  A.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx -> journal cx ly S W m md k -> A.ACtlRtC.ctl_rt_C B ly S m.
Proof.
  intros cx ly S W m md k HB HJ. pose proof HJ as (HAR & _).
  exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly S W m md HAR
           (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ (r10_aro cx ly S W m md k HB HJ)
              (Z.le_refl _) (Z.le_refl _))).
Qed.

(* The entry cut of R10, opened (G1): ix_cut's index, then C_A81680_at's conjuncts (ACtlCutP.v:1375-1393). *)
Ltac r10_open Hbody :=
  let Hb := fresh "Hb" in
  destruct Hbody as [? Hb]; subst;
  cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCutP.C_A81680_at] in Hb;
  rewrite r10_ixn0 in Hb.

(* G2, shared by every arm: the entry facts the runs and the exits need, from the cut's shell (ctl_base, the
   journal's AR and astk_ok, the frame law), FRAC, and the AR block laws for the turn's block (phi, rnb cx b) and
   the input block (c_p cx, c_n cx).  Names introduced: Ecn Hinp Efr Hfr4096 HfrS Hfapp HSlo HShi HAR, FRAC's
   A sp R2 Hsp16 Hspz R4 R8 R9 R3 R19 R26 Hfr32 HA32 HAS HspA HfrA HA416 HSsp HSapp, Hu2 Hinf Hphiin Hp4096 Hpapp
   Hpdj Hrnb Hinb Hphinz Hphiad Hphi0 HphiE, Sh and HShb. *)
Ltac r10_g2 b cx fr phi regs3 mem3 ly3 S3 W3 md3 HB HJ HF HL HFRAC HP HHB Hnz :=
  pose proof HB as ((_ & _ & _ & _ & Hinp & Ecn & _) & _);
  destruct (r10_geo _ _ _ _ _ _ _ _ HJ HF HL) as (Efr & Hfr4096 & HfrS & Hfapp & HSlo & HShi & HAR);
  pose proof HFRAC as (A & sp & R2 & Hsp16 & Hspz & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAS & HspA &
    HfrA & HA416 & HSsp & HSapp & _);
  unfold A.ACtlCutP.FRAME_BYTES in HfrA; unfold A.AsanRT.APPMEM_END in HSapp; unfold A.ACfn.LLVMF_STK in *;
  pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs3 2)) as Hu2;
  change (bv_modulus 64) with (2 ^ 64) in Hu2; unfold lib.Reusable.YG0d.spZ in Hspz;
  assert (Hinf : In (6, A.ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity);
  assert (Hphiin : In (phi, A.ACtlCutP.rnb cx b) (lib.Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; left; reflexivity);
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hphiin)
    as (_ & Hp4096 & _ & Hpapp & _);
  pose proof (lib.Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ _ _ HAR Hphiin Hinf) as Hpdj;
  let u := fresh "u" in let Hu := fresh "Hu" in let Hur := fresh "Hur" in
  destruct (A.Prog.Seg.Tac_slot.a_rtn_u (A.ACtlCut.c_in cx) (Z.of_nat b) Hnz) as (u & Hu & Hur);
  assert (Hrnb : 124 <= A.ACtlCutP.rnb cx b <= 1492) by (unfold A.ACtlCutP.rnb; rewrite Hu; lia);
  let Ereq := fresh "Ereq" in
  assert (Ereq : lib.Reusable.YG00.req_size (A.ACtlCutP.rnb cx b) = A.ACtlCutP.rnb cx b)
    by (unfold lib.Reusable.YG00.req_size; destruct (Z.eqb_spec (A.ACtlCutP.rnb cx b) 0); lia);
  rewrite Ereq in Hpapp, Hpdj; unfold lib.Reusable.YG0f.zdisjoint in Hpdj; cbn [fst snd] in Hpdj;
  rewrite <- Efr in Hpdj; change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Hpdj;
  assert (Hinb : 0 < A.ACtlCut.c_n cx -> 0 <= A.ACtlCut.c_p cx /\
     (A.ACtlCut.c_p cx + A.ACtlCut.c_n cx <= fr \/ fr + 4096 <= A.ACtlCut.c_p cx) /\
     (forall x, A.ACtlCut.c_p cx <= x < A.ACtlCut.c_p cx + A.ACtlCut.c_n cx -> A.AsanRT.app_mem x))
    by (let Hn0 := fresh "Hn0" in let Hin3 := fresh "Hin3" in let Hqapp := fresh "Hqapp" in
        let Hqdj := fresh "Hqdj" in let Ereq' := fresh "Ereq'" in
        intros Hn0; destruct Hinp as [(? & _) | (_ & ?Hin0)]; [lia|];
        assert (Hin3 : In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly3 S3))
          by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; assumption);
        destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3)
          as (_ & ? & _ & Hqapp & _);
        pose proof (lib.Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ _ _ HAR Hin3 Hinf) as Hqdj;
        assert (Ereq' : lib.Reusable.YG00.req_size (A.ACtlCut.c_n cx) = A.ACtlCut.c_n cx)
          by (unfold lib.Reusable.YG00.req_size; destruct (Z.eqb_spec (A.ACtlCut.c_n cx) 0); lia);
        rewrite Ereq' in Hqapp, Hqdj; unfold lib.Reusable.YG0f.zdisjoint in Hqdj; cbn [fst snd] in Hqdj;
        rewrite <- Efr in Hqdj; change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Hqdj;
        split; [lia|]; split; [lia|]; exact (r10_in_app_mem _ _ Hqapp));
  pose proof HHB as (Hphinz & Hphiad); pose proof Hphiad as (Hphi0 & _ & HphiE & _);
  unfold A.ACtlK.a_size in HphiE; unfold A.AsanRT.APPMEM_END in HphiE;
  set (Sh := A.ACtlCutP.Sfr fr);
  assert (HShb : 2147450880 <= Sh /\ Sh + 512 <= 17594333495296)
    by (unfold Sh, A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
        pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia));
        pose proof (Z.div_le_mono (fr + 4096) (2 ^ 47) 8 ltac:(lia) ltac:(lia));
        replace ((fr + 4096) / 8) with (fr / 8 + 512) in * by (rewrite <- Z.div_add by lia; f_equal; lia);
        change (2 ^ 47 / 8) with 17592186044416 in *; lia).

(* The window [S(fr) + 306, S(fr) + 306 + n) of the frame shadow as n one-byte cells of mem3 (the (F) region of the
   cut's ctl_rt_C: the owned frame's shadow), and its rng premise at RNG_W (w_H W3) (r10_fsh_vis).
   Names: xs Hxs CH Rsh. *)
Ltac r10_shcells n cx fr ly3 S3 W3 mem3 md3 Sh Hrt Hfapp HAR HF Efr Hinf :=
  let Hshstk := fresh "Hshstk" in
  assert (Hshstk : lib.Lib.Frame.stk A.Img0.rsegs mem3 (Sh + 306) (Sh + 306 + Z.of_nat n))
    by (let HCUT := fresh "HCUT" in let a := fresh "a" in let Ha := fresh "Ha" in
        destruct Hrt as (_ & HCUT & _ & _); split; [lia|]; split; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|];
        intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; apply HCUT;
        [ apply (r10_cut_fsh cx fr ly3 S3 a Hinf Efr); unfold Sh in Ha; lia
        | replace a with (A.Prog.SlotInv.Sfr fr + (a - Sh)) by (unfold Sh, A.Prog.SlotInv.Sfr, A.ACtlCutP.Sfr; lia);
          apply A.Prog.Seg.R10B.r10b_fsh; [intros ? ?; apply Hfapp; lia | lia] ]);
  destruct (A.Prog.Seg.R10A.r10a_ex_C1 mem3 (Sh + 306) n Hshstk) as (xs & Hxs & CH);
  pose proof (A.ProgBridge.rng_of_visible _ _ _
                (r10_fsh_vis cx fr ly3 S3 W3 mem3 md3 HAR HF Efr ltac:(lia) 306 (Z.of_nat n)
                   ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)))
    as Rsh.

(* G3: the cut's configuration in the run's state form (ProgBridge.cfg_at_MS), the cut's pc, and the walk moved
   to the canonical register map mkR_of regs3 (YA0nR.SRr_xregs_eqv), unfolded to lib/Lib's mkR. *)
Ltac r10_g3 X pc POST cx regs3 W3 mem3 md3 :=
  rewrite A.ProgBridge.cfg_at_MS;
  change (A.ACtlCut.cut_pc X) with pc;
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))];
  unfold lib.Lib.Regs6ss.mkR_of.

(* ---------------------------------------------------------------------------------------------------------
   3. Arm b = 0: 0x81680 .. 0x81768 (R10A.r10a_evt0 / R10AF.r10a_evt0_F), five frame-shadow stores in
   [S(fr) + 306, S(fr) + 318), exit C_A81768_at at i = 0. *)
Lemma r10_b0 : forall POST,
  CF POST (ix_cut C_A81768_at [Z.of_nat 0]) -> CF POST (ix_cut C_A81680_at [Z.of_nat 0]).
Proof.
  pose proof A.Prog.SlotInv.FRAME_BYTES_val as HFRAMEb. pose proof A.Prog.SlotInv.FRAME_SHADOW_val as HFRAMEs.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  r10_open Hbody.
  destruct Hb as (phi & HP & HFRAC & (Hn & Hb6 & HHB & R23 & HOUR & HOUTA & HCUR & S112 & S128 & HPRO & S104 &
    S96 & S64 & S144 & S192 & C2688 & C2768 & S280 & S240 & C3040 & C3056 & S152 & R21 & A2176) &
    (HRF & HRXS & Ha0 & R27)).
  destruct HRF as (((_ & _ & _ & _ & HID & HFG) & Hnz & R24 & HPHI) & R18).
  (* G2: the entry facts, the frame and the two blocks; the frame-shadow window as 12 cells *)
  r10_g2 0%nat cx fr phi regs3 mem3 ly3 S3 W3 md3 HB HJ HF HL HFRAC HP HHB Hnz.
  r10_shcells 12%nat cx fr ly3 S3 W3 mem3 md3 Sh Hrt Hfapp HAR HF Efr Hinf.
  change (Z.of_nat 0) with 0 in Ha0, R23.
  (* G3: the cut's state in the run's form, moved to the canonical register map *)
  r10_g3 (ix_cut C_A81680_at [Z.of_nat 0]) 0x81680 POST cx regs3 W3 mem3 md3.
  (* G4: the _F run at RNG_W (w_H W3), lifted with SRr_fevt_hid *)
  lazymatch goal with
  | |- context [lib.Lib.Frame.mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18
                  ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31] =>
      pose proof (A.Prog.Seg.R10AF.r10a_evt0_F (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3))
                    x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                    x27 x28 x29 x30 x31 lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3 Sh phi xs
                    ltac:(exact R19) ltac:(exact R23) ltac:(exact R27)
                    ltac:(unfold A.ACtlCut.a0v, A.ACtlCut.rgv in Ha0;
                          rewrite (A.Prog.Seg.B3Rtm.a_rtm_k0 (A.ACtlCut.c_in cx)) in Ha0; exact Ha0)
                    ltac:(exact R24) Hphi0 ltac:(lia) ltac:(lia) ltac:(lia) Hxs CH Rsh) as HRUN
  end.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 _ _ (POST cx) HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  intros ms' md' HQ Hhid Hsbm.
  destruct HQ as (R & m' & l12 & c4 & c5 & Ems & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K21 & K22 & K23 & K24 &
    K25 & K26 & K10 & K11 & K12 & K13 & MU & WM & B12 & L12 & B4 & V4 & B5 & V5).
  subst ms'. unfold lib.Lib.MState.MS in Hhid. cbn [ms_mem] in Hhid.
  (* G5: the exit cut C_A81768_at at R, m', md' *)
  change (lib.Reusable.YA0n.SRr segs W3
            (lib.Reusable.YG0d.cfg_at segs (A.ACtlCut.cut_pc (ix_cut C_A81768_at [Z.of_nat 0])) R m' md') (POST cx)).
  assert (HN0 : r10_N cx 0 phi fr regs3 mem3)
    by (unfold r10_N; repeat (split; [assumption|]); assumption).
  assert (HN1 : r10_N cx 0 phi fr R m').
  { apply (r10_N_keep_sh cx 0 phi fr regs3 R mem3 m' 318 A HN0 Ecn MU WM ltac:(exact K9) R9); try lia.
    - intros x Hx. unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia.
    - exact Hfapp.
    - exact (r10_in_app_mem _ _ Hpapp).
    - exact Hinb. }
  destruct HN1 as (HHB1 & HOUR1 & HOUTA1 & S112' & S128' & HPRO' & S104' & S96' & S64' & S144' & S192' & C2688' &
    C2768' & S280' & S240' & C3040' & C3056' & S152' & A2176' & HID' & HFG' & HPHI' & HRXS').
  pose proof HRXS' as (X48 & X56 & X88 & X80 & X72 & X16 & X8 & X200 & X216 & XA2256).
  assert (Hrd : forall x, Sh + 306 <= x < Sh + 318 ->
                  exists bb, lib.Lib.Mem.mrd A.Img0.rsegs m' (lib.Lib.Mem.wa x) = Some bb).
  { intros x Hx. apply (A.Prog.Seg.R10A.r10a_ba_rd m' (Sh + 306) l12 x B12). rewrite L12.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (HA2528 : A.AsanRT.addressable m' (fr + 2528) 12).
  { assert (A1 : A.AsanRT.addressable m' (fr + 2528) 8).
    { apply (A.Prog.Seg.R10A.r10a_addr_cell m' fr 2528 8 c4); try (unfold A.AsanRT.APPMEM_END; lia).
      - intros a Ha. apply Hfapp. lia.
      - change (2528 / 8) with 316. exact B4. }
    assert (A2 : A.AsanRT.addressable m' (fr + 2528 + 8) 4).
    { replace (fr + 2528 + 8) with (fr + 2536) by lia.
      apply (A.Prog.Seg.R10A.r10a_addr_cell m' fr 2536 4 c5); try (unfold A.AsanRT.APPMEM_END; lia).
      - intros a Ha. apply Hfapp. lia.
      - change (2536 / 8) with 317. exact B5. }
    exact (A.Prog.Seg.R10A.r10a_addr_cat m' (fr + 2528) 8 4 A1 A2). }
  pose proof (r10_journal_sh cx fr k ly3 S3 W3 mem3 md3 m' md' 306 318 HJ Efr ltac:(lia) ltac:(lia) ltac:(lia)
                MU WM Hhid Hsbm) as HJ'.
  apply (HX cx [Z.of_nat 0] fr k ly3 S3 W3 R m' md' HB).
  - exact HJ'.
  - exact HF.
  - exact HL.
  - exact Hk.
  - cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCut.ix_cut A.ACtlCutP.C_A81768_at].
    split; [reflexivity|]. rewrite r10_ixn0.
    destruct HCUR as (Hc7 & Hc22 & Hc25).
    exists phi, 0%nat.
    split; [exact HP|].
    split.
    { apply (r10_frac_keep B cx fr regs3 R mem3 m' [(Sh + 306, Sh + 318)] A HFRAC R9 ltac:(lia));
        try (exact K2 || exact K3 || exact K4 || exact K8 || exact K9 || exact K19 || exact K26 || exact MU).
      - intros x Hx. cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
      - intros x Hx. apply (A.Prog.Seg.R10B.r10b_appbyte_out fr 306 318 x); try lia.
        + intros y Hy. apply Hfapp. lia.
        + apply Hfapp. lia.
      - intros x Hx. apply (A.Prog.Seg.R10B.r10b_appbyte_out fr 306 318 x); try lia.
        + intros y Hy. apply Hfapp. lia.
        + apply Hfapp. lia.
      - intros x Hx. cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
      - intros x Hx. destruct (Z_lt_le_dec x (Sh + 306)) as [H1|H1];
          [left; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]|].
        destruct (Z_lt_le_dec x (Sh + 318)) as [H2|H2];
          [right; apply Hrd; lia | left; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]]. }
    split.
    { split; [exact Hn|]. split; [exact Hb6|]. split; [exact HHB1|].
      split; [exact (eq_trans K23 R23)|]. split; [exact HOUR1|]. split; [exact HOUTA1|].
      split; [split; [exact Hc7|]; split; [exact (eq_trans K22 Hc22) | exact (eq_trans K25 Hc25)]|].
      split; [lia|].
      split; [unfold A.ACtlCut.rgv; replace (phi + 18 + Z.of_nat 0) with (phi + 18) by lia; exact K10|].
      split; [unfold A.ACtlCut.rgv; replace (phi + 18 + Z.of_nat 0) with (phi + 18) by lia; exact K12|].
      unfold A.ACtlCut.rgv; replace (32 - Z.of_nat 0) with 32 by lia; exact K13. }
    split; [reflexivity|]. split; [lia|]. split; [exact K11|].
    split.
    { split; [split; [split; [exact Hb6|]|]|].
      - split; [split; [exact Hc7|]; split; [exact (eq_trans K22 Hc22) | exact (eq_trans K25 Hc25)]|].
        split; [exact HOUR1|]. split; [exact (eq_trans K23 R23)|]. split; [exact HID' | exact HFG'].
      - split; [exact Hnz|]. split; [exact (eq_trans K24 R24) | exact HPHI'].
      - exact (eq_trans K18 R18). }
    split; [exact S112'|]. split; [exact X16|]. split; [exact X8|]. split; [exact X200|]. split; [exact X216|].
    split; [exact HA2528|]. split; [exact S128'|]. split; [exact HPRO'|]. split; [exact S104'|].
    split; [exact S96'|]. split; [exact S64'|]. split; [exact (eq_trans K21 R21)|].
    split; [exact S144'|]. split; [exact S192'|]. split; [exact C2688'|]. split; [exact C2768'|].
    split; [exact S280'|]. split; [exact S240'|]. split; [exact C3040'|]. split; [exact C3056'|].
    split; [exact S152'|]. split; [exact A2176' | exact HRXS'].
  - exact (r10_rtC_exit cx ly3 S3 W3 m' md' k HB HJ').
Qed.

(* ---------------------------------------------------------------------------------------------------------
   4. Arms b = 1, 2: 0x81680 .. 0x817ec (R10A.r10a_evt12 / R10AF.r10a_evt12_F), three frame-shadow stores in
   [S(fr) + 306, S(fr) + 313), exit C_A817ec_at at i = 0. *)
Lemma r10_b12 : forall POST (b : nat), (b = 1 \/ b = 2)%nat ->
  CF POST (ix_cut C_A817ec_at [Z.of_nat b]) -> CF POST (ix_cut C_A81680_at [Z.of_nat b]).
Proof.
  pose proof A.Prog.SlotInv.FRAME_BYTES_val as HFRAMEb. pose proof A.Prog.SlotInv.FRAME_SHADOW_val as HFRAMEs.
  intros POST b Hb12 HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  r10_open Hbody.
  destruct Hb as (phi & HP & HFRAC & (Hn & Hb6 & HHB & R23 & HOUR & HOUTA & HCUR & S112 & S128 & HPRO & S104 &
    S96 & S64 & S144 & S192 & C2688 & C2768 & S280 & S240 & C3040 & C3056 & S152 & R21 & A2176) &
    (HRF & HRXS & Ha0 & R27)).
  destruct HRF as (((_ & _ & _ & _ & HID & HFG) & Hnz & R24 & HPHI) & R18).
  (* G2 *)
  r10_g2 b cx fr phi regs3 mem3 ly3 S3 W3 md3 HB HJ HF HL HFRAC HP HHB Hnz.
  r10_shcells 7%nat cx fr ly3 S3 W3 mem3 md3 Sh Hrt Hfapp HAR HF Efr Hinf.
  (* G3 *)
  r10_g3 (ix_cut C_A81680_at [Z.of_nat b]) 0x81680 POST cx regs3 W3 mem3 md3.
  (* G4 *)
  lazymatch goal with
  | |- context [lib.Lib.Frame.mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18
                  ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31] =>
      pose proof (A.Prog.Seg.R10AF.r10a_evt12_F (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3))
                    x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                    x27 x28 x29 x30 x31 lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3 Sh phi (Z.of_nat b) xs
                    ltac:(exact R19) ltac:(exact R23) ltac:(exact R27)
                    ltac:(unfold A.ACtlCut.a0v, A.ACtlCut.rgv in Ha0;
                          rewrite (A.Prog.Seg.B3Rtm.a_rtm_k5 (A.ACtlCut.c_in cx) (Z.of_nat b) ltac:(lia)) in Ha0;
                          exact Ha0)
                    ltac:(exact R24) ltac:(lia) Hphi0 ltac:(lia) ltac:(lia) ltac:(lia) Hxs CH Rsh) as HRUN
  end.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 _ _ (POST cx) HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  intros ms' md' HQ Hhid Hsbm.
  destruct HQ as (R & m' & l7 & Ems & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K21 & K22 & K23 & K24 &
    K25 & K26 & K10 & K11 & K12 & K13 & MU & WM & B7 & L7).
  subst ms'. unfold lib.Lib.MState.MS in Hhid. cbn [ms_mem] in Hhid.
  (* G5: the exit cut C_A817ec_at at R, m', md' *)
  change (lib.Reusable.YA0n.SRr segs W3
            (lib.Reusable.YG0d.cfg_at segs (A.ACtlCut.cut_pc (ix_cut C_A817ec_at [Z.of_nat b])) R m' md') (POST cx)).
  assert (HN0 : r10_N cx b phi fr regs3 mem3)
    by (unfold r10_N; repeat (split; [assumption|]); assumption).
  assert (HN1 : r10_N cx b phi fr R m').
  { apply (r10_N_keep_sh cx b phi fr regs3 R mem3 m' 313 A HN0 Ecn MU WM ltac:(exact K9) R9); try lia.
    - intros x Hx. unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia.
    - exact Hfapp.
    - exact (r10_in_app_mem _ _ Hpapp).
    - exact Hinb. }
  destruct HN1 as (HHB1 & HOUR1 & HOUTA1 & S112' & S128' & HPRO' & S104' & S96' & S64' & S144' & S192' & C2688' &
    C2768' & S280' & S240' & C3040' & C3056' & S152' & A2176' & HID' & HFG' & HPHI' & HRXS').
  assert (Hrd : forall x, Sh + 306 <= x < Sh + 313 ->
                  exists bb, lib.Lib.Mem.mrd A.Img0.rsegs m' (lib.Lib.Mem.wa x) = Some bb).
  { intros x Hx. apply (A.Prog.Seg.R10A.r10a_ba_rd m' (Sh + 306) l7 x B7). rewrite L7.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  pose proof (r10_journal_sh cx fr k ly3 S3 W3 mem3 md3 m' md' 306 313 HJ Efr ltac:(lia) ltac:(lia) ltac:(lia)
                MU WM Hhid Hsbm) as HJ'.
  apply (HX cx [Z.of_nat b] fr k ly3 S3 W3 R m' md' HB).
  - exact HJ'.
  - exact HF.
  - exact HL.
  - exact Hk.
  - cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCut.ix_cut A.ACtlCutP.C_A817ec_at].
    split; [reflexivity|]. rewrite r10_ixn0.
    destruct HCUR as (Hc7 & Hc22 & Hc25).
    exists phi, 0%nat.
    split; [exact HP|].
    split.
    { apply (r10_frac_keep B cx fr regs3 R mem3 m' [(Sh + 306, Sh + 313)] A HFRAC R9 ltac:(lia));
        try (exact K2 || exact K3 || exact K4 || exact K8 || exact K9 || exact K19 || exact K26 || exact MU).
      - intros x Hx. cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
      - intros x Hx. apply (A.Prog.Seg.R10B.r10b_appbyte_out fr 306 313 x); try lia.
        + intros y Hy. apply Hfapp. lia.
        + apply Hfapp. lia.
      - intros x Hx. apply (A.Prog.Seg.R10B.r10b_appbyte_out fr 306 313 x); try lia.
        + intros y Hy. apply Hfapp. lia.
        + apply Hfapp. lia.
      - intros x Hx. cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
      - intros x Hx. destruct (Z_lt_le_dec x (Sh + 306)) as [H1|H1];
          [left; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]|].
        destruct (Z_lt_le_dec x (Sh + 313)) as [H2|H2];
          [right; apply Hrd; lia | left; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]]. }
    split.
    { split; [exact Hn|]. split; [exact Hb6|]. split; [exact HHB1|].
      split; [exact (eq_trans K23 R23)|]. split; [exact HOUR1|]. split; [exact HOUTA1|].
      split; [split; [exact Hc7|]; split; [exact (eq_trans K22 Hc22) | exact (eq_trans K25 Hc25)]|].
      split; [lia|].
      split; [unfold A.ACtlCut.rgv; replace (phi + 18 + Z.of_nat 0) with (phi + 18) by lia; exact K10|].
      split; [unfold A.ACtlCut.rgv; replace (phi + 18 + Z.of_nat 0) with (phi + 18) by lia; exact K12|].
      unfold A.ACtlCut.rgv; replace (32 - Z.of_nat 0) with 32 by lia; exact K13. }
    split; [exact Hb12|]. split; [lia|]. split; [exact K11|].
    split.
    { split; [split; [exact Hb6|]|].
      - split; [split; [exact Hc7|]; split; [exact (eq_trans K22 Hc22) | exact (eq_trans K25 Hc25)]|].
        split; [exact HOUR1|]. split; [exact (eq_trans K23 R23)|]. split; [exact HID' | exact HFG'].
      - split; [exact Hnz|]. split; [exact (eq_trans K24 R24) | exact HPHI']. }
    split; [exact S128'|]. split; [exact HPRO'|]. split; [exact S104'|].
    split; [exact S96'|]. split; [exact S64'|]. split; [exact (eq_trans K21 R21)|]. split; [exact S112'|].
    split; [exact S144'|]. split; [exact S192'|]. split; [exact C2688'|]. split; [exact C2768'|].
    split; [exact S280'|]. split; [exact S240'|]. split; [exact C3040'|]. split; [exact C3056'|].
    split; [exact S152'|]. split; [exact A2176' | exact HRXS'].
  - exact (r10_rtC_exit cx ly3 S3 W3 m' md' k HB HJ').
Qed.

(* ---------------------------------------------------------------------------------------------------------
   5. Arms b = 3, 4: the SPLIT POINT at reac_ctrl_identity_reply. *)

(* The caller's stack window is present and visible at every journalled state (ajournal's 14th conjunct). *)
Lemma r10_stk_vis : forall cx ly3 S3 W3 mem3 md3 k,
  journal cx ly3 S3 W3 mem3 md3 k ->
  forall a, A.ACtlCut.c_sp cx - A.ACfn.LLVMF_STK <= a < A.ACtlCut.c_sp cx ->
  lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W3) mem3 a.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k HJ.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _). exact Hs.
Qed.

(* The owned frame lies below the allocator's ceiling and the caller's stack window above it. *)
Lemma r10_geo2 : forall cx fr k ly3 S3 W3 mem3 md3,
  journal cx ly3 S3 W3 mem3 md3 k ->
  lib.Reusable.YG01.frames S3 = A.ACtlCut.own6 cx ->
  fr = lib.Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) ->
  fr + 4096 <= lib.Reusable.YM05.alloc_ceiling /\
  lib.Reusable.YM05.alloc_ceiling + A.ACfn.LLVMF_STK <= A.ACtlCut.c_sp cx.
Proof.
  intros cx fr k ly3 S3 W3 mem3 md3 HJ HF Efr.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  assert (Hin : In (6, A.ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (lib.Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR Hin)
    as (_ & Hceil & _).
  change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Hceil. rewrite <- Efr in Hceil.
  destruct Hstk as (_ & _ & Hc1 & Hc2 & _). split; lia.
Qed.

(* Arms b = 3, 4: 0x81680 .. 0x816ac (R10AF.r10a_head34_F: the frame-shadow stores 2 / 0 / 0 at S(fr) + 306 /
   308 / 312, which make the reply's three caller cells addressable), 0x816ac .. the callee entry
   (R10AFs.r10a_call34_pre_Fs: the argument set-up and the jal), the call by REPLY_SPEC, whose post returns at
   0x816c4 = the exit C_A816c4_at at i = b. *)
Lemma r10_b34 : forall POST (b : nat), (b = 3 \/ b = 4)%nat ->
  CF POST (ix_cut C_A816c4_at [Z.of_nat b]) -> CF POST (ix_cut C_A81680_at [Z.of_nat b]).
Proof.
  pose proof A.Prog.SlotInv.FRAME_BYTES_val as HFRAMEb. pose proof A.Prog.SlotInv.FRAME_SHADOW_val as HFRAMEs.
  intros POST b Hb34 HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  r10_open Hbody.
  destruct Hb as (phi & HP & HFRAC & (Hn & Hb6 & HHB & R23 & HOUR & HOUTA & HCUR & S112 & S128 & HPRO & S104 &
    S96 & S64 & S144 & S192 & C2688 & C2768 & S280 & S240 & C3040 & C3056 & S152 & R21 & A2176) &
    (HRF & HRXS & Ha0 & R27)).
  destruct HRF as (((_ & _ & _ & _ & HID & HFG) & Hnz & R24 & HPHI) & R18).
  (* G2 *)
  r10_g2 b cx fr phi regs3 mem3 ly3 S3 W3 md3 HB HJ HF HL HFRAC HP HHB Hnz.
  r10_shcells 7%nat cx fr ly3 S3 W3 mem3 md3 Sh Hrt Hfapp HAR HF Efr Hinf.
  destruct (r10_geo2 cx fr k ly3 S3 W3 mem3 md3 HJ HF Efr) as (Hceil & Hstkc).
  unfold A.ACfn.LLVMF_STK in Hstkc.
  (* G3 *)
  r10_g3 (ix_cut C_A81680_at [Z.of_nat b]) 0x81680 POST cx regs3 W3 mem3 md3.
  (* G4a: the head run *)
  lazymatch goal with
  | |- context [lib.Lib.Frame.mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18
                  ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31] =>
      pose proof (A.Prog.Seg.R10AF.r10a_head34_F (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3))
                    x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                    x27 x28 x29 x30 x31 lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3 Sh (Z.of_nat b) xs
                    ltac:(exact R19) ltac:(exact R23) ltac:(exact R27)
                    ltac:(unfold A.ACtlCut.a0v, A.ACtlCut.rgv in Ha0;
                          rewrite (A.Prog.Seg.B3Rtm.a_rtm_k5 (A.ACtlCut.c_in cx) (Z.of_nat b) ltac:(lia)) in Ha0;
                          exact Ha0)
                    ltac:(lia) ltac:(lia) ltac:(lia) Hxs CH Rsh) as HRUN
  end.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 _ _ (POST cx) HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  intros ms1 md1 HQ1 Hhid1 Hsbm1.
  destruct HQ1 as (R1 & m1 & l7 & c0 & c1 & c2 & Ems1 & ER1 & MU1 & WM1 & B306 & V306 & B308 & V308 & B312 & V312 &
    B7 & L7).
  subst ms1. unfold lib.Lib.MState.MS in Hhid1. cbn [ms_mem] in Hhid1.
  (* the entry's memory facts at m1 *)
  assert (HN0 : r10_N cx b phi fr regs3 mem3)
    by (unfold r10_N; repeat (split; [assumption|]); assumption).
  assert (HN1 : r10_N cx b phi fr regs3 m1).
  { apply (r10_N_keep_sh cx b phi fr regs3 regs3 mem3 m1 313 A HN0 Ecn MU1 WM1 eq_refl R9); try lia.
    - intros x Hx. unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia.
    - exact Hfapp.
    - exact (r10_in_app_mem _ _ Hpapp).
    - exact Hinb. }
  assert (Hrd : forall x, Sh + 306 <= x < Sh + 313 ->
                  exists bb, lib.Lib.Mem.mrd A.Img0.rsegs m1 (lib.Lib.Mem.wa x) = Some bb).
  { intros x Hx. apply (A.Prog.Seg.R10A.r10a_ba_rd m1 (Sh + 306) l7 x B7). rewrite L7.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (HF1 : A.ACtlCutP.FRAC B cx fr fr regs3 m1).
  { apply (r10_frac_keep B cx fr regs3 regs3 mem3 m1 [(Sh + 306, Sh + 313)] A HFRAC R9 ltac:(lia));
      try reflexivity; try exact MU1.
    - intros x Hx. cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
    - intros x Hx. apply (A.Prog.Seg.R10B.r10b_appbyte_out fr 306 313 x); try lia.
      + intros y Hy. apply Hfapp. lia.
      + apply Hfapp. lia.
    - intros x Hx. apply (A.Prog.Seg.R10B.r10b_appbyte_out fr 306 313 x); try lia.
      + intros y Hy. apply Hfapp. lia.
      + apply Hfapp. lia.
    - intros x Hx. cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
    - intros x Hx. destruct (Z_lt_le_dec x (Sh + 306)) as [H1|H1];
        [left; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]|].
      destruct (Z_lt_le_dec x (Sh + 313)) as [H2|H2];
        [right; apply Hrd; lia | left; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]]. }
  pose proof (r10_journal_sh cx fr k ly3 S3 W3 mem3 md3 m1 md1 306 313 HJ Efr ltac:(lia) ltac:(lia) ltac:(lia)
                MU1 WM1 Hhid1 Hsbm1) as HJ1.
  pose proof HN1 as (HHB1 & HOUR1 & HOUTA1 & S112' & S128' & HPRO' & S104' & S96' & S64' & S144' & S192' & C2688' &
    C2768' & S280' & S240' & C3040' & C3056' & S152' & A2176' & HID' & HFG' & HPHI' & HRXS').
  pose proof HRXS' as (X48 & X56 & X88 & X80 & X72 & X8 & X0 & X200 & X216 & XA2256).
  pose proof (A.Prog.Seg.R10A.r10a_spill_at regs3 m1 A 88 (fr + 2448) R9 ltac:(lia) ltac:(lia) ltac:(lia) X88) as Q88.
  pose proof (A.Prog.Seg.R10A.r10a_spill_at regs3 m1 A 80 (fr + 2464) R9 ltac:(lia) ltac:(lia) ltac:(lia) X80) as Q80.
  pose proof (A.Prog.Seg.R10A.r10a_spill_at regs3 m1 A 72 (fr + 2496) R9 ltac:(lia) ltac:(lia) ltac:(lia) X72) as Q72.
  assert (Hsv : forall lo len, A.ACtlCut.c_sp cx - 32768 <= lo -> lo + len <= A.ACtlCut.c_sp cx ->
                  0 <= len -> A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) lo len).
  { intros lo len H1 H2 H3. split; [lia|]. split; [lia|]. intros a Ha.
    exact (proj1 (r10_stk_vis cx ly3 S3 W3 m1 md1 k HJ1 a ltac:(unfold A.ACfn.LLVMF_STK; lia))). }
  (* G4b: the argument set-up and the jal, from the head run's end map *)
  rewrite ER1.
  lazymatch goal with
  | |- context [lib.Lib.Frame.mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18
                  ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31] =>
      pose proof (A.Prog.Seg.R10AFs.r10a_call34_pre_Fs (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3))
                    x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                    x27 x28 x29 x30 x31 lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr m1
                    (fr + 2448) (fr + 2464) (fr + 2496) A
                    ltac:(exact R9) ltac:(lia) ltac:(lia) Q88 Q80 Q72
                    (A.ProgBridge.rng_of_visible _ _ _ (Hsv (A + 88) 8 ltac:(lia) ltac:(lia) ltac:(lia)))
                    (A.ProgBridge.rng_of_visible _ _ _ (Hsv (A + 80) 8 ltac:(lia) ltac:(lia) ltac:(lia)))
                    (A.ProgBridge.rng_of_visible _ _ _ (Hsv (A + 72) 8 ltac:(lia) ltac:(lia) ltac:(lia))))
        as HRUN2
  end.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN2) as HFS2.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS2.
  apply (lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md1 _ _ (POST cx) HFS2).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  intros ms2 md2 HQ2 Hhid2 Hsbm2. subst ms2.
  pose proof (r10_journal_sh cx fr k ly3 S3 W3 m1 md1 m1 md2 306 306 HJ1 Efr ltac:(lia) ltac:(lia) ltac:(lia)
                (lib.Lib.Frame.munch_refl _ m1) (lib.Lib.Frame.wmono_refl A.Img0.rsegs m1)
                (fun _ _ => eq_refl) Hsbm2) as HJ2.
  (* the callee entry: the cgif configuration at A_reac_ctrl_identity_replyP *)
  lazymatch goal with |- context [lib.Lib.MState.MS ?R _ _ _ _ _ _] => set (Rc := R) end.
  assert (Era : lib.Reusable.YK11.getr Rc 1 = Z_to_bv 64 0x816c4) by reflexivity.
  assert (EsR : forall r, lib.Reusable.YG0d.acallee_saved r ->
                  lib.Reusable.YK11.getr Rc (Z_to_bv 5 r) = lib.Reusable.YK11.getr regs3 (Z_to_bv 5 r)).
  { intros r Hr. unfold lib.Reusable.YG0d.acallee_saved in Hr.
    destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [reflexivity..|].
    assert (Er : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      by lia.
    destruct Er as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity. }
  assert (Hsp2 : lib.Reusable.YG0d.spZ Rc = sp) by (exact Hspz).
  assert (EA : A.Prog.reac_ctrl_identity_reply_c.REAC_CTRL_IDENTITY_REPLY =
               A.Prog.C_reac_ctrl_identity_reply.A_reac_ctrl_identity_replyP)
    by (vm_compute; reflexivity).
  change (lib.Reusable.YA0n.SRr segs W3
            (lib.Reusable.YG0d.cfg_at segs A.Prog.reac_ctrl_identity_reply_c.REAC_CTRL_IDENTITY_REPLY Rc m1 md2)
            (POST cx)).
  rewrite EA.
  set (G := A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) (Z.of_nat b)).
  assert (Hg50 : length G = 50%nat) by (unfold G, A.Prog.SlotModel.rt_g; apply A.Prog.SlotModel.fr50_length).
  pose proof HB as (((_ & _ & _ & Hgp & _) & _) & _).
  pose proof HJ2 as (HAR2 & _).
  assert (Ereq' : lib.Reusable.YG00.req_size (A.ACtlCutP.rnb cx b) = A.ACtlCutP.rnb cx b)
    by (unfold lib.Reusable.YG00.req_size; destruct (Z.eqb_spec (A.ACtlCutP.rnb cx b) 0); lia).
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 m1 md2 _ _ HAR2 Hphiin)
    as (_ & _ & Hpc & Hpap & Hpp & _ & _).
  destruct (lib.Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 m1 md2 _ _ HAR2 Hphiin) as (Hbs & Hhull).
  rewrite Ereq' in Hpc, Hpap, Hpp, Hbs, Hhull.
  assert (Hoff : forall x, phi <= x < phi + A.ACtlCutP.rnb cx b -> r10_off x).
  { intros x Hx. apply r10_off_img; [lia|].
    assert (Hci : exists p n, In (p, n) (lib.Reusable.YG0d.ablocks B ly3 S3) /\
                    p <= x < p + lib.Reusable.YG00.req_size n).
    { exists phi, (A.ACtlCutP.rnb cx b). split; [exact Hphiin|]. rewrite Ereq'. lia. }
    exact (proj2 (lib.Reusable.YG0d.al_client_img _ _ LAWS ly3 S3 W3 m1 md2 x HAR2 (or_introl Hci))). }
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 m1 md2 6 (A.ACtlCut.c_fpos cx) HAR2 Hinf)
    as (_ & _ & Hfp & Hfsp).
  rewrite <- Efr in Hfp, Hfsp. change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfp, Hfsp.
  change (4096 / 8) with 512 in Hfsp.
  eapply (lib.Reusable.YA0n.SRr_bind segs W3 _ _ (POST cx)).
  { apply (REPLY_SPEC A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) [] (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx)
             (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx) (A.ACtlCut.own6 cx) ly3 S3 W3 m1 md2 k Rc
             phi (A.ACtlCutP.rnb cx b) (fr + 2448) (fr + 2464) (fr + 2496) G HJ2
             (r10_aro cx ly3 S3 W3 m1 md2 k HB HJ2)).
    - rewrite Era. vm_compute. reflexivity.
    - unfold lib.Reusable.YG0d.raZ. rewrite Era. rewrite lib.Lib.MState.unsigned_lit by lia. lia.
    - transitivity (lib.Reusable.YK11.getr regs3 3); [reflexivity|]. rewrite R3. exact Hgp.
    - transitivity (lib.Reusable.YK11.getr regs3 4); [reflexivity | exact R4].
    - transitivity (lib.Reusable.YK11.getr regs3 24); [reflexivity | exact R24].
    - transitivity (lib.Reusable.YK11.getr regs3 18); [reflexivity | exact R18].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite Hsp2. exact Hsp16.
    - rewrite Hsp2. unfold A.Prog.C_reac_ctrl_identity_reply.TREPLY_STK, A.Prog.C_reac_ctrl_parse.REAC_CTRL_PARSE_STK,
        A.ACfn.LLVMF_STK. lia.
    - rewrite Hsp2. lia.
    - rewrite HF. vm_compute. reflexivity.
    - exact Hg50.
    - (* the message block (phi, rnb cx b) *)
      intros Hargs H50.
      split; [exists (A.ACtlCutP.rnb cx b); split; [exact Hphiin | rewrite Ereq'; lia]|].
      split.
      + unfold A.Prog.CtrlCallerJ.tsrc_ok. split; [|split; [|split; [|split; [|split]]]].
        * intros a Ha. split.
          -- apply lib.Reusable.YCbq.aview_some_of_apresent. exact (proj1 (Hpp a ltac:(lia))).
          -- rewrite Hsp2. unfold lib.Reusable.YG0d.ESTACK. lia.
        * exact (r10_ra_of_bs _ _ _ _ 50 Hbs ltac:(lia)).
        * intros s Hs. apply Hhull. split; [lia|].
          assert (M1 : lib.Reusable.YG0f.shadow_addr (phi + 50 - 1) <=
                       lib.Reusable.YG0f.shadow_addr (phi + A.ACtlCutP.rnb cx b - 1)).
          { unfold lib.Reusable.YG0f.shadow_addr.
            pose proof (Z.div_le_mono (phi + 50 - 1) (phi + A.ACtlCutP.rnb cx b - 1) 8 ltac:(lia) ltac:(lia)).
            lia. }
          pose proof (Z.div_le_mono _ _ 8 ltac:(lia) M1). lia.
        * unfold lib.Reusable.YG0d.amem_range, lib.Reusable.YG0f.kLowMemEnd, lib.Reusable.YG0f.kHighMemBeg,
            lib.Reusable.YG0f.kHighMemEnd.
          unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg,
            lib.Reusable.YG0f.ASAN_CEIL in Hpap.
          pose proof lib.Reusable.YCbq.asan_consts as (HAC & _). lia.
        * lia.
        * lia.
      + apply r10_garr8_of_bytes.
        * intros i Hi. rewrite Hg50 in Hi. split; [apply Hoff; lia|].
          exact (proj1 (proj1 (Hpp (phi + i) ltac:(lia)))).
        * unfold G, A.Prog.SlotModel.rt_g. apply A.Prog.Seg.R10A.r10a_g50; [|exact HPHI'].
          destruct (A.Prog.Seg.R10A.r10a_lens (A.ACtlCut.c_in cx) b ltac:(lia)) as (Hl & _ & _).
          unfold A.ACtlCutP.rnb in Hrnb. lia.
    - (* the three caller cells at fr + 2448 / 2464 / 2496, made addressable by the head run *)
      intros Hargs.
      assert (Htw : forall q n, fr + 2448 <= q -> q + n <= fr + 2504 ->
                A.Prog.CtrlCallerJ.twr_ok (PI := A.Prog.CtrlImg.PI_ctrl) B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) []
                  (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) ly3 S3 (A.ACtlCut.own6 cx) W3 m1
                  (lib.Reusable.YG0d.spZ Rc) q n).
      { intros q n Hq1 Hq2 a Ha. destruct (Hfp a ltac:(lia)) as (Hpr & Hno).
        split; [|split; [exact Hpr | split; [exact Hno|]]].
        - right; right; right. exists 6, (A.ACtlCut.c_fpos cx). split; [left; reflexivity|]. left.
          unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
          change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
        - rewrite Hsp2. unfold lib.Reusable.YG0d.ESTACK. lia. }
      assert (Hsh : forall j v (c : byte), 0 <= j < 512 -> lib.Lib.Mem.bytes_at A.Img0.rsegs m1 (Sh + j) [c] ->
                 bv_unsigned c = v -> lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) m1 (Sh + j) = Some v).
      { intros j v c Hj Hb Hv. rewrite <- Hv. apply r10_view_of.
        - apply r10_off_hi. unfold A.Prog.ImgBounds.IMG_HI. lia.
        - replace (Sh + j) with (lib.Reusable.YG0f.shadow_addr fr + j)
            by (unfold Sh, A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr,
                  lib.Reusable.YG0f.SHADOW_OFF; lia).
          exact (proj1 (proj1 (Hfsp j Hj))).
        - exact (A.Prog.Seg.R10B.r10b_b1_rd m1 (Sh + j) c Hb). }
      assert (Ec0 : bv_unsigned c0 = 2) by (rewrite (r10_unsigned_of_signed c0) by lia; lia).
      assert (Ec1 : bv_unsigned c1 = 0) by (rewrite (r10_unsigned_of_signed c1) by lia; lia).
      assert (Ec2 : bv_unsigned c2 = 0) by (rewrite (r10_unsigned_of_signed c2) by lia; lia).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split.
      { intros a Ha. exists 6, (A.ACtlCut.c_fpos cx). split; [exact Hinf|].
        unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite <- Efr.
        change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096.
        unfold A.Prog.C_reac_ctrl_identity_reply.treply_out in Ha. lia. }
      split; [apply Htw; lia|]. split; [apply Htw; lia|]. split; [apply Htw; lia|].
      split; [|split].
      + intros x Hx. exists 2. split.
        * replace (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF x) with (Sh + 306)
            by (unfold Sh, A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0v.shadow_of_addr,
                  lib.Reusable.YG0f.SHADOW_OFF; Z.div_mod_to_equations; lia).
          exact (Hsh 306 2 c0 ltac:(lia) B306 Ec0).
        * unfold lib.Reusable.YG0v.saddr_ok. right. Z.div_mod_to_equations. lia.
      + intros x Hx. exists 0. split; [|left; reflexivity].
        replace (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF x) with (Sh + 308)
          by (unfold Sh, A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0v.shadow_of_addr,
                lib.Reusable.YG0f.SHADOW_OFF; Z.div_mod_to_equations; lia).
        exact (Hsh 308 0 c1 ltac:(lia) B308 Ec1).
      + intros x Hx. exists 0. split; [|left; reflexivity].
        replace (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF x) with (Sh + 312)
          by (unfold Sh, A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0v.shadow_of_addr,
                lib.Reusable.YG0f.SHADOW_OFF; Z.div_mod_to_equations; lia).
        exact (Hsh 312 0 c2 ltac:(lia) B312 Ec2). }
  (* the return at 0x816c4: the reply post, then the exit C_A816c4_at at i = b *)
  intros W2 cf2 _ (Hwle & ly2 & S2 & regs2 & mem2 & md5 & Ecf2 & HJ3 & Hpres & HF2 & HP2 & Hret & HK & Hcells).
  subst cf2. rewrite Era.
  change (lib.Reusable.YA0n.SRr segs W2
            (lib.Reusable.YG0d.cfg_at segs (A.ACtlCut.cut_pc (ix_cut C_A816c4_at [Z.of_nat b])) regs2 mem2 md5)
            (POST cx)).
  replace (k + A.Prog.C_reac_ctrl_identity_reply.EV_REPLY) with k in HJ3
    by (unfold A.Prog.C_reac_ctrl_identity_reply.EV_REPLY; lia).
  (* the model: the turn's record is an identity reply with four live pointers *)
  assert (Hargs : lib.Prog.RcReply.reply_args phi (fr + 2448) (fr + 2464) (fr + 2496) = true).
  { unfold lib.Prog.RcReply.reply_args.
    rewrite (proj2 (Z.eqb_neq phi 0) Hphinz), (proj2 (Z.eqb_neq (fr + 2448) 0) ltac:(lia)),
      (proj2 (Z.eqb_neq (fr + 2464) 0) ltac:(lia)), (proj2 (Z.eqb_neq (fr + 2496) 0) ltac:(lia)).
    reflexivity. }
  assert (Hir : lib.Prog.RcReply.ir (A.ACtlCutP.rnb cx b) G = true)
    by (unfold G, A.ACtlCutP.rnb; apply A.Prog.Seg.B3Rtm.a_rtm_ir; lia).
  assert (Hok : lib.Prog.RcReply.reply_ok phi (A.ACtlCutP.rnb cx b) (fr + 2448) (fr + 2464) (fr + 2496) G = true)
    by (unfold lib.Prog.RcReply.reply_ok; rewrite Hargs, Hir; reflexivity).
  assert (Hret1 : lib.Prog.RcReply.reply_ret phi (A.ACtlCutP.rnb cx b) (fr + 2448) (fr + 2464) (fr + 2496) G = 1)
    by (unfold lib.Prog.RcReply.reply_ret; rewrite Hargs, Hir; reflexivity).
  pose proof (lib.Prog.RcReply.ir_true _ _ Hir) as (_ & _ & _ & _ & Hs14 & Hs23 & _).
  destruct (Hcells Hok) as (Ga & Vp & Vn).
  (* the callee-saved registers *)
  assert (EP : forall r, lib.Reusable.YG0d.acallee_saved r ->
                 lib.Reusable.YK11.getr regs2 (Z_to_bv 5 r) = lib.Reusable.YK11.getr regs3 (Z_to_bv 5 r))
    by (intros r Hr; rewrite (Hpres r Hr); exact (EsR r Hr)).
  assert (K2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
    by (exact (EP 2 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
  assert (K3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
    by (exact (EP 3 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
  assert (K4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
    by (exact (EP 4 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
  assert (K8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
    by (exact (EP 8 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
  assert (K9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
    by (exact (EP 9 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
  assert (K18 : lib.Reusable.YK11.getr regs2 18 = lib.Reusable.YK11.getr regs3 18)
    by (exact (EP 18 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
  assert (K19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
    by (exact (EP 19 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
  assert (K21 : lib.Reusable.YK11.getr regs2 21 = lib.Reusable.YK11.getr regs3 21)
    by (exact (EP 21 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
  assert (K22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
    by (exact (EP 22 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
  assert (K23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
    by (exact (EP 23 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
  assert (K24 : lib.Reusable.YK11.getr regs2 24 = lib.Reusable.YK11.getr regs3 24)
    by (exact (EP 24 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
  assert (K25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
    by (exact (EP 25 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
  assert (K26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
    by (exact (EP 26 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
  (* the bytes the call keeps (tcj_kept) *)
  pose proof HK as (KS & KB & _ & KF & _ & _).
  assert (HnE : forall a, ~ (fr + 2448 <= a < fr + 2504) ->
            ~ (lib.Prog.RcReply.reply_ok phi (A.ACtlCutP.rnb cx b) (fr + 2448) (fr + 2464) (fr + 2496) G = true /\
               A.Prog.C_reac_ctrl_identity_reply.treply_out (fr + 2448) (fr + 2464) (fr + 2496) a)).
  { intros a Ha (_ & Ho). unfold A.Prog.C_reac_ctrl_identity_reply.treply_out in Ho. lia. }
  assert (Hfoff : forall x, fr <= x < fr + 4096 -> r10_off x).
  { intros x Hx. apply r10_off_img; [lia|].
    assert (Hci : exists cid pos, In (cid, pos) (lib.Reusable.YG01.frames S3) /\
                    lib.Reusable.YG0f.frame_addr ly3 cid pos <= x <
                    lib.Reusable.YG0f.frame_addr ly3 cid pos + lib.Reusable.YG00.fs_frame_bytes cid).
    { exists 6, (A.ACtlCut.c_fpos cx). split; [exact Hinf|]. rewrite <- Efr.
      change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096. lia. }
    exact (proj2 (lib.Reusable.YG0d.al_client_img _ _ LAWS ly3 S3 W3 m1 md2 x HAR2 (or_intror (or_introl Hci)))). }
  assert (CSk : forall x, sp <= x < A.ACtlCut.c_sp cx ->
                  r10_cp (lib.Reusable.YA0n.w_H W3) (lib.Reusable.YA0n.w_H W2) m1 mem2 x).
  { intros x Hx. split; [apply r10_off_hi; unfold A.Prog.ImgBounds.IMG_HI; lia|].
    split; [exact (proj1 (r10_stk_vis cx ly3 S3 W3 m1 md2 k HJ2 x ltac:(unfold A.ACfn.LLVMF_STK; lia)))|].
    apply KS; [lia | rewrite Hsp2; unfold A.Prog.C_reac_ctrl_identity_reply.TREPLY_STK,
                      A.Prog.C_reac_ctrl_parse.REAC_CTRL_PARSE_STK; lia |].
    apply HnE. lia. }
  assert (CFr : forall x, fr <= x < fr + 4096 -> ~ (fr + 2448 <= x < fr + 2504) ->
                  r10_cp (lib.Reusable.YA0n.w_H W3) (lib.Reusable.YA0n.w_H W2) m1 mem2 x).
  { intros x Hx Hnc. split; [exact (Hfoff x Hx)|]. split; [exact (proj1 (proj1 (Hfp x Hx)))|].
    apply (KF 6 (A.ACtlCut.c_fpos cx) x Hinf); [|exact (HnE x Hnc)].
    left. unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite <- Efr.
    change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096. lia. }
  assert (ESh : lib.Reusable.YG0f.shadow_addr fr = Sh)
    by (unfold Sh, A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr,
          lib.Reusable.YG0f.SHADOW_OFF; lia).
  assert (CSh : forall x, Sh <= x < Sh + 392 ->
                  r10_cp (lib.Reusable.YA0n.w_H W3) (lib.Reusable.YA0n.w_H W2) m1 mem2 x).
  { intros x Hx. split; [apply r10_off_hi; unfold A.Prog.ImgBounds.IMG_HI; lia|].
    pose proof (Hfsp (x - Sh) ltac:(lia)) as ((Hh & _) & _). rewrite ESh in Hh.
    replace (Sh + (x - Sh)) with x in Hh by lia. split; [exact Hh|].
    apply (KF 6 (A.ACtlCut.c_fpos cx) x Hinf).
    - right. unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr, ESh.
      change (lib.Reusable.YG00.fs_frame_bytes 6 / 8) with 512. lia.
    - intros (_ & Ho). unfold A.Prog.C_reac_ctrl_identity_reply.treply_out in Ho.
      pose proof (Hfapp x ltac:(lia)) as Hap.
      unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in Hap. lia. }
  assert (CPh : forall x, phi <= x < phi + A.ACtlCutP.rnb cx b ->
                  r10_cp (lib.Reusable.YA0n.w_H W3) (lib.Reusable.YA0n.w_H W2) m1 mem2 x).
  { intros x Hx. split; [exact (Hoff x Hx)|]. split; [exact (proj1 (proj1 (Hpp x Hx)))|].
    pose proof (KB phi (A.ACtlCutP.rnb cx b) (x - phi) Hphiin ltac:(rewrite Ereq'; lia)
                  ltac:(apply HnE; lia)) as Kx.
    replace (phi + (x - phi)) with x in Kx by lia. exact Kx. }
  assert (CIn : forall x, A.ACtlCut.c_p cx <= x < A.ACtlCut.c_p cx + Z.of_nat (length (A.ACtlCut.c_in cx)) ->
                  r10_cp (lib.Reusable.YA0n.w_H W3) (lib.Reusable.YA0n.w_H W2) m1 mem2 x).
  { intros x Hx. assert (Hn0 : 0 < A.ACtlCut.c_n cx) by (rewrite Ecn; lia).
    assert (Hin3 : In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly3 S3)).
    { destruct Hinp as [(Hz & _) | (_ & Hin0)]; [lia|].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin0. }
    assert (Ereq3 : lib.Reusable.YG00.req_size (A.ACtlCut.c_n cx) = A.ACtlCut.c_n cx)
      by (unfold lib.Reusable.YG00.req_size; destruct (Z.eqb_spec (A.ACtlCut.c_n cx) 0); lia).
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 m1 md2 _ _ HAR2 Hin3)
      as (_ & _ & Hqc & _ & Hqp & _ & _).
    rewrite Ereq3 in Hqc, Hqp. rewrite <- Ecn in Hx.
    destruct (Hinb Hn0) as (Hq0 & Hqd & _).
    split.
    { apply r10_off_img; [lia|].
      assert (Hci : exists p n, In (p, n) (lib.Reusable.YG0d.ablocks B ly3 S3) /\
                      p <= x < p + lib.Reusable.YG00.req_size n).
      { exists (A.ACtlCut.c_p cx), (A.ACtlCut.c_n cx). split; [exact Hin3|]. rewrite Ereq3. lia. }
      exact (proj2 (lib.Reusable.YG0d.al_client_img _ _ LAWS ly3 S3 W3 m1 md2 x HAR2 (or_introl Hci))). }
    split; [exact (proj1 (proj1 (Hqp x Hx)))|].
    pose proof (KB (A.ACtlCut.c_p cx) (A.ACtlCut.c_n cx) (x - A.ACtlCut.c_p cx) Hin3 ltac:(rewrite Ereq3; lia)
                  ltac:(apply HnE; lia)) as Kx.
    replace (A.ACtlCut.c_p cx + (x - A.ACtlCut.c_p cx)) with x in Kx by lia. exact Kx. }
  (* the block shadows at the post, from AR (AR_shadow_law): the turn's block and the input block *)
  pose proof HJ3 as (HAR3 & _).
  assert (HHB2 : A.ACtlCutP.HB mem2 phi (A.ACtlCutP.rnb cx b)).
  { assert (Hphi3 : In (phi, A.ACtlCutP.rnb cx b) (lib.Reusable.YG0d.ablocks B ly2 S2))
      by (apply (Permutation_in _ (Permutation_sym HP2)); exact Hphiin).
    destruct (lib.Reusable.YG0d.al_shadow _ _ LAWS ly2 S2 W2 mem2 md5 _ _ HAR3 Hphi3) as (Hbs3 & _).
    rewrite Ereq' in Hbs3.
    split; [exact Hphinz|]. unfold A.ACtlK.a_size. rewrite Z.max_l by lia.
    apply (r10_addr_of_bs _ _ _ _ Hbs3); [lia | unfold A.AsanRT.APPMEM_END; lia |].
    exact (r10_in_app_mem _ _ Hpapp). }
  assert (HIn2 : 0 < A.ACtlCut.c_n cx -> A.AsanRT.addressable mem2 (A.ACtlCut.c_p cx) (A.ACtlCut.c_n cx)).
  { intros Hn0.
    assert (Hin3 : In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly2 S2)).
    { destruct Hinp as [(Hz & _) | (_ & Hin0)]; [lia|].
      apply (Permutation_in _ (Permutation_sym HP2)). apply (Permutation_in _ (Permutation_sym HP)).
      apply in_or_app. left. exact Hin0. }
    assert (Ereq3 : lib.Reusable.YG00.req_size (A.ACtlCut.c_n cx) = A.ACtlCut.c_n cx)
      by (unfold lib.Reusable.YG00.req_size; destruct (Z.eqb_spec (A.ACtlCut.c_n cx) 0); lia).
    destruct (lib.Reusable.YG0d.al_shadow _ _ LAWS ly2 S2 W2 mem2 md5 _ _ HAR3 Hin3) as (Hbs3 & _).
    rewrite Ereq3 in Hbs3. destruct (Hinb Hn0) as (Hq0 & _ & Hqa).
    pose proof (Hqa (A.ACtlCut.c_p cx + A.ACtlCut.c_n cx - 1) ltac:(lia)) as Hl.
    unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in Hl.
    apply (r10_addr_of_bs _ _ _ _ Hbs3); [lia | unfold A.AsanRT.APPMEM_END; lia | exact Hqa]. }
  pose proof (r10_N_view cx b phi fr regs3 regs2 m1 mem2 _ _ A HN1 R9 ltac:(lia) ltac:(lia) K9
                ltac:(intros x Hx; apply CSk; lia) ltac:(intros x Hx; apply CFr; lia) CSh CPh CIn
                ltac:(lia) ltac:(lia) ltac:(lia) HHB2 HIn2) as HN2.
  pose proof (r10_frac_view B cx fr regs3 regs2 m1 mem2 _ _ A HF1 R9 ltac:(lia) K2 K3 K4 K8 K9 K19 K26
                ltac:(intros x Hx; apply CSk; lia) ltac:(intros x Hx; apply CFr; lia) ltac:(intros x Hx; apply CFr; lia)
                ltac:(intros x Hx; apply CSk; lia) CSh) as HF3.
  destruct HN2 as (_ & HOUR2 & HOUTA2 & S112'' & S128'' & HPRO'' & S104'' & S96'' & S64'' & S144'' & S192'' &
    C2688'' & C2768'' & S280'' & S240'' & C3040'' & C3056'' & S152'' & A2176'' & HID'' & HFG'' & HPHI'' & HRXS'').
  (* the three cells the reply wrote *)
  assert (Cpa : lib.Lib.Step.rw_cells A.Img0.rsegs mem2 (fr + 2448)
                  [lib.Lib.Cells.CB 2 (lib.Prog.RcReply.reply_addr G)]).
  { assert (Bpa : lib.Lib.Mem.bytes_at A.Img0.rsegs mem2 (fr + 2448) (lib.Prog.RcReply.reply_addr G)).
    { apply (r10_bytes_of_garr8 (lib.Reusable.YA0n.w_H W2)); [| cbn; lia | cbn; lia | exact Ga].
      intros i Hi. cbn in Hi. apply Hfoff. lia. }
    apply (A.Prog.Seg.R10A.r10a_rw_CB mem2 (fr + 2448) _ Bpa).
    apply r10_wr_of_bytes; [|exact Bpa]. intros i Hi. cbn in Hi. apply Hfoff. lia. }
  assert (Cw : forall a v, fr + 2464 <= a -> a + 8 <= fr + 2504 -> 0 <= v < 2 ^ 64 ->
                 lib.Reusable.YI04.val_mem segs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W2) mem2) a 8 v ->
                 lib.Lib.Step.rw_cells A.Img0.rsegs mem2 a [lib.Lib.Cells.CB 8 (lib.Lib.Mem.le8 (Z_to_bv 64 v))]).
  { intros a v Ha1 Ha2 Hv Hm.
    pose proof (A.KindBGlue.word_mem_le8 segs _ a v Hm Hv ltac:(lia) ltac:(lia)) as Bm.
    assert (Bm' : lib.Lib.Mem.bytes_at A.Img0.rsegs mem2 a (lib.Lib.Mem.le8 (Z_to_bv 64 v))).
    { apply (r10_unrestrict_bytes (lib.Reusable.YA0n.w_H W2)); [|exact Bm].
      intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. apply Hfoff. cbn in Hi. lia. }
    pose proof (A.Prog.Seg.R10A.r10a_rw_CB mem2 a _ Bm') as Hc. rewrite lib.Lib.Mem.length_le8 in Hc.
    apply Hc. pose proof (r10_wr_of_bytes mem2 a (lib.Lib.Mem.le8 (Z_to_bv 64 v))
                            ltac:(intros i Hi; rewrite lib.Lib.Mem.length_le8 in Hi; apply Hfoff; cbn in Hi; lia)
                            Bm') as Hw.
    rewrite lib.Lib.Mem.length_le8 in Hw. exact Hw. }
  apply (HX cx [Z.of_nat b] fr k ly2 S2 W2 regs2 mem2 md5 HB HJ3).
  - rewrite HF2. exact HF.
  - exact HL.
  - exact Hk.
  - cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCut.ix_cut A.ACtlCutP.C_A816c4_at].
    split; [reflexivity|]. rewrite r10_ixn0.
    destruct HCUR as (Hc7 & Hc22 & Hc25).
    exists phi.
    split; [exact (Permutation_trans HP2 HP)|].
    split; [exact HF3|].
    split.
    { split; [exact Hn|]. split; [exact Hb6|]. split; [exact HHB2|].
      split; [exact (eq_trans K23 R23)|]. split; [exact HOUR2|]. split; [exact HOUTA2|].
      split; [split; [exact Hc7|]; split; [exact (eq_trans K22 Hc22) | exact (eq_trans K25 Hc25)]|].
      split; [exact S112''|]. split; [exact S128''|]. split; [exact HPRO''|]. split; [exact S104''|].
      split; [exact S96''|]. split; [exact S64''|]. split; [exact S144''|]. split; [exact S192''|].
      split; [exact C2688''|]. split; [exact C2768''|]. split; [exact S280''|]. split; [exact S240''|].
      split; [exact C3040''|]. split; [exact C3056''|]. split; [exact S152''|].
      split; [exact (eq_trans K21 R21)|]. exact A2176''. }
    split; [exact Hb34|].
    split; [unfold A.ACtlCut.a0v, A.ACtlCut.rgv; rewrite Hret, Hret1; reflexivity|].
    split.
    { split; [|exact (eq_trans K18 R18)].
      split; [|split; [exact Hnz|]; split; [exact (eq_trans K24 R24) | exact HPHI'']].
      split; [exact Hb6|].
      split; [split; [exact Hc7|]; split; [exact (eq_trans K22 Hc22) | exact (eq_trans K25 Hc25)]|].
      split; [exact HOUR2|]. split; [exact (eq_trans K23 R23)|]. split; [exact HID'' | exact HFG'']. }
    split; [exact HRXS''|].
    split; [exact Cpa|].
    split; [apply Cw; [lia | lia | lia | exact Vp]|].
    apply Cw; [lia | lia | unfold G in Hs14, Hs23; lia | exact Vn].
  - exact (r10_rtC_exit cx ly2 S2 W2 mem2 md5 k HB HJ3).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   5. Arms b = 5, 6: 0x81680 .. 0x81708 (b = 6) / 0x817c8 (b = 5), the run R10BFon.r10b_evt_F_on (the route (C)
   twin of R10BF.r10b_evt_F): three frame-shadow stores in [S(fr) + 306, S(fr) + 313), then
   reac_ctrl_identity_fragment on its narrowed footprint contract (a Theorem Labs lane's proved
   reac_ctrl_identity_fragment_F_holds_on_closed), whose write set is R10B.r10b_W fr sp (the fragment record, the
   three reply cells, the callee window [sp - 4656, sp)).  Exits C_A81708_at (b = 6) and C_A817c8_at (b = 5) at
   i = 0. *)

(* The fragment call's shadow region (a Theorem Labs lane's reac_ctrl_identity_fragment_shadow_R at R10B's call:
   f = fr + 2256, fr = phi, pa / pp / pn = fr + 2448 / 2464 / 2496) lies in the cut's own regions: a callee span over
   the fragment record [fr + 2256, fr + 2328) in the owned frame's shadow (F), a span over the message
   [phi, phi + 50) in the turn block's shadow-word cover (L). *)
Lemma r10_sw_frame : forall fr p n a, A.Prog.sh_word_on.sh_word_on p n a -> 0 <= fr -> fr + 64 <= p ->
  p + n <= fr + 4000 ->
  lib.Reusable.YG0f.shadow_addr fr <= a < lib.Reusable.YG0f.shadow_addr fr + 512.
Proof.
  intros fr p n a (Hn & Ha) Hfr Hp Hpn.
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
  unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

Lemma r10_sw_block : forall q m0 p n a, A.Prog.sh_word_on.sh_word_on p n a -> 0 <= q -> q <= p -> 1 <= n ->
  p + n <= q + m0 ->
  lib.Reusable.YG0f.shadow_addr q / 8 * 8 <= a < lib.Reusable.YG0f.shadow_addr (q + m0 - 1) / 8 * 8 + 8.
Proof.
  intros q m0 p n a (_ & Ha) Hq Hqp Hn Hpn.
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
  unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

Lemma r10_fragR_cut : forall cx fr ly3 S3 phi n0 nb st g a,
  In (6, A.ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3) ->
  fr = lib.Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) -> 0 <= fr -> fr + 4096 <= 2 ^ 64 ->
  In (phi, n0) (lib.Reusable.YG0d.ablocks B ly3 S3) -> 50 <= lib.Reusable.YG00.req_size n0 -> 0 <= phi ->
  phi + 50 <= 2 ^ 64 ->
  A.Prog.reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_shadow_R (fr + 2256) phi nb (fr + 2448)
    (fr + 2464) (fr + 2496) st g a ->
  A.ACtlRtC.cut_shadow B ly3 S3 a.
Proof.
  intros cx fr ly3 S3 phi n0 nb st g a Hin Efr Hfr0 Hfrb Hblk Hreq Hphi0 Hphib HR.
  unfold A.Prog.reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_shadow_R in HR.
  destruct HR as (_ & _ & _ & _ & _ & Hfg & Hcase).
  (* the record's length n = fg_n g: 1 <= n <= 22 (fg_fr); the keep arm's offset lf with lf + n <= 64 (fg_keep) *)
  assert (Hn : 1 <= lib.Prog.RcFrag.fg_n g <= 22).
  { unfold lib.Prog.RcFrag.fg_fr in Hfg.
    repeat match type of Hfg with
           | (_ && _)%bool = true => let H := fresh "Hb" in apply andb_prop in Hfg; destruct Hfg as [Hfg H]
           end.
    repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H end.
    lia. }
  assert (Hlf : 0 <= lib.Prog.RcFrag.fg_lf st < 256).
  { unfold lib.Prog.RcFrag.fg_lf, lib.Prog.RcFrag.bat. exact (bv_unsigned_in_range 8 _). }
  (* the two regions, for a span over the record and for a span over the message *)
  assert (EF : forall p n, A.Prog.sh_word_on.sh_word_on p n a -> fr + 2256 <= p -> p + n <= fr + 2256 + 72 ->
                 A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros p n Hs Hp1 Hp2. left. exists 6, (A.ACtlCut.c_fpos cx). split; [exact Hin|].
    rewrite <- Efr. change (lib.Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
    exact (r10_sw_frame fr p n a Hs Hfr0 ltac:(lia) ltac:(lia)). }
  assert (EL : forall p n, A.Prog.sh_word_on.sh_word_on p n a -> phi <= p -> 1 <= n -> p + n <= phi + 50 ->
                 A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros p n Hs Hp1 Hn1 Hp2. right; left. exists phi, n0. split; [exact Hblk|].
    exact (r10_sw_block phi (lib.Reusable.YG00.req_size n0) p n a Hs Hphi0 Hp1 Hn1 ltac:(lia)). }
  unfold A.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R, A.Prog.bcmp_wrap_c_on.bcmp_wrap_shadow_R in Hcase.
  rewrite !lib.Lib.MState.unsigned_lit in Hcase by lia.
  destruct Hcase as [(_ & [[M|M]|[M|M]]) | (_ & _ & [[M|M]|(Hk & [M|M])])];
    try (unfold lib.Prog.RcFrag.fg_keep, lib.Prog.RcFrag.fg_T in Hk;
         repeat match type of Hk with
                | (_ && _)%bool = true => let H := fresh "Hk" in apply andb_prop in Hk; destruct Hk as [Hk H]
                end;
         repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H end);
    first [ apply (EL _ _ M); lia | apply (EF _ _ M); lia ].
Qed.

(* A fact kept out of lia's sight (R10B.r10b_box), so that lia does not split on it. *)
Ltac r10b56_hide H := let T := type of H in change (A.Prog.Seg.R10B.r10b_box T) in H.

(* Above the image a byte the core's view reads is a visible byte (mbyte falls back to the segments only). *)
Lemma r10b56_aview_vis : forall (H : word -> bool) (m : word -> option byte) a,
  A.Prog.ImgBounds.IMG_HI <= a < 2 ^ 64 -> lib.Reusable.YG0n.aview segs H m a <> None ->
  H (Z_to_bv 64 a) = false.
Proof.
  intros H m a Ha Hv. destruct (H (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso. apply Hv.
  unfold A.Prog.ImgBounds.IMG_HI in Ha.
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by exact (lib.Lib.Mem.wa_unsigned a ltac:(lia)).
  assert (Hr : lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a) = None).
  { apply (A.MemNorm.seg_rom_unmapped A.Img0.rsegs (Z_to_bv 64 a)). rewrite Hu.
    apply r10_seg_none. unfold A.Prog.ImgBounds.IMG_HI. lia. }
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict. rewrite E.
  change (option_map (fun b : byte => bv_unsigned b) (lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a)) = None).
  rewrite Hr. reflexivity.
Qed.

(* A run of present bytes is a present, writable stack range. *)
Lemma r10b56_stk_pres : forall (H : word -> bool) (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> lib.Reusable.YG0n.apresent H m a) ->
  lib.Lib.Frame.stk A.Img0.rsegs m lo hi.
Proof.
  intros H m lo hi Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|].
  intros a Ha. destruct (Hp a Ha) as (_ & b & Hb). unfold lib.Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* A run of present bytes is a visible range. *)
Lemma r10b56_vis_pres : forall (H : word -> bool) (m : word -> option byte) lo len,
  0 <= lo -> lo + len <= 2 ^ 64 -> (forall a, lo <= a < lo + len -> lib.Reusable.YG0n.apresent H m a) ->
  A.ProgBridge.range_visible H lo len.
Proof.
  intros H m lo len H0 H1 Hp. split; [exact H0|]. split; [exact H1|]. intros a Ha. exact (proj1 (Hp a Ha)).
Qed.

(* The 8-aligned shadow cover of [p, p + k] inside a block's visible shadow hull (AR_shadow_law). *)
Lemma r10b56_hull_vis : forall (H : word -> bool) (m : word -> option byte) p n k,
  lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview segs H m) p n ->
  0 <= p -> 0 <= k -> k <= n - 1 -> p + n <= 2 ^ 47 ->
  A.ProgBridge.range_visible H (A.AsanRT.shadow_addr p / 8 * 8)
    (A.AsanRT.shadow_addr (p + k) / 8 * 8 + 8 - A.AsanRT.shadow_addr p / 8 * 8).
Proof.
  intros H m p n k HV Hp Hk Hkn Hpn.
  unfold A.ProgBridge.range_visible, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
  split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros a Ha. apply (r10b56_aview_vis H m a).
  - unfold A.Prog.ImgBounds.IMG_HI. Z.div_mod_to_equations. lia.
  - apply HV. unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

(* The 8-aligned shadow cover of frame bytes [fr + off, fr + off + k] inside the visible frame shadow. *)
Lemma r10b56_fcov_vis : forall (H : word -> bool) fr off k,
  (forall lo len, 0 <= lo -> 0 <= len -> lo + len <= 512 ->
     A.ProgBridge.range_visible H (A.ACtlCutP.Sfr fr + lo) len) ->
  0 <= fr -> 64 <= off -> 0 <= k -> off + k <= 4000 ->
  A.ProgBridge.range_visible H (A.AsanRT.shadow_addr (fr + off) / 8 * 8)
    (A.AsanRT.shadow_addr (fr + off + k) / 8 * 8 + 8 - A.AsanRT.shadow_addr (fr + off) / 8 * 8).
Proof.
  intros H fr off k HV Hfr Hoff Hk Hok.
  pose proof (HV 0 512 ltac:(lia) ltac:(lia) ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  apply (A.ProgBridge.range_visible_sub H _ _ _ _ H0);
    unfold A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* The 8-aligned shadow words of the callee window [spv - 4656, spv) inside the stack's zero shadow
   (AR_zshadow_law at the layout's stack range, the first entry of zero_shadow_ranges). *)
Lemma r10b56_zsh_vis : forall (H : word -> bool) (m : word -> option byte) lo hi spv,
  (forall i, 0 <= i < (hi - lo) / 8 ->
     lib.Reusable.YG0n.aview segs H m (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF lo + i) =
     Some 0) ->
  0 <= lo -> lo + 4096 <= spv - 4656 -> spv + 416 <= hi -> hi <= 2 ^ 47 ->
  A.ProgBridge.range_visible H (A.Prog.rng_asan.sh_al8_lo (spv - 4656))
    (A.Prog.rng_asan.sh_al8_hi (spv - 4656) 4656 - A.Prog.rng_asan.sh_al8_lo (spv - 4656)).
Proof.
  intros H m lo hi spv HZ Hlo Hl Hh Hhi.
  unfold A.ProgBridge.range_visible, A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi,
    A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
  split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros a Ha. apply (r10b56_aview_vis H m a); [unfold A.Prog.ImgBounds.IMG_HI; Z.div_mod_to_equations; lia|].
  replace a with (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF lo +
                  (a - lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF lo)) by lia.
  rewrite HZ; [discriminate|].
  unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

(* The journal across the two write sets of the arm: the frame-shadow window [S(fr) + 306, S(fr) + 313) and the
   callee's R10B.r10b_W fr spv.  YCbq.ajournal_exec with Wr := the bytes of that list; each is awr_byte's
   in_frames case (the owned class-6 frame or its shadow) or its stack case [c_sp - LLVMF_STK, c_sp). *)
Lemma r10b56_journal : forall cx fr spv k ly3 S3 W3 mem3 md3 (m' : word -> option byte) md',
  journal cx ly3 S3 W3 mem3 md3 k ->
  fr = lib.Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) -> A.Prog.ImgBounds.IMG_HI <= fr ->
  A.ACtlCut.c_sp cx - 32768 <= spv - A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K ->
  spv <= A.ACtlCut.c_sp cx ->
  A.Prog.ImgBounds.IMG_HI <= spv - A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K ->
  lib.Lib.Frame.munch ((A.ACtlCutP.Sfr fr + 306, A.ACtlCutP.Sfr fr + 313) :: A.Prog.Seg.R10B.r10b_W fr spv)
    mem3 m' ->
  lib.Lib.Frame.wmono A.Img0.rsegs mem3 m' ->
  (forall x : word, lib.Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) ->
  lib.Reusable.YK04.same_but_materialized md3 md' ->
  journal cx ly3 S3 W3 m' md' k.
Proof.
  intros cx fr spv k ly3 S3 W3 mem3 md3 m' md' HJ Efr Hfr Hw1 Hw2 Hw3 MU WM Hhid Hsbm.
  assert (HSh : 2147450880 <= A.ACtlCutP.Sfr fr).
  { unfold A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. unfold A.Prog.ImgBounds.IMG_HI in Hfr.
    pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)). lia. }
  assert (Hlow : forall x, ~ lib.Lib.Frame.outside
                   ((A.ACtlCutP.Sfr fr + 306, A.ACtlCutP.Sfr fr + 313) :: A.Prog.Seg.R10B.r10b_W fr spv) x ->
                   A.Prog.ImgBounds.IMG_HI <= x).
  { intros x Hx. destruct (A.Prog.Seg.R10B.r10b_notout _ _ _ _ Hx) as [H|H].
    - unfold A.Prog.ImgBounds.IMG_HI. lia.
    - destruct (A.Prog.Seg.R10B.r10b_W_in fr spv x H) as [H'|H']; lia. }
  eapply (lib.Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
    with (Wr := fun a => ~ lib.Lib.Frame.outside
                  ((A.ACtlCutP.Sfr fr + 306, A.ACtlCutP.Sfr fr + 313) :: A.Prog.Seg.R10B.r10b_W fr spv) a).
  - exact HJ.
  - intros x Hx. unfold lib.Reusable.YK04.mrestrict.
    destruct (lib.Reusable.YA0n.w_H W3 x); [reflexivity|].
    apply MU. destruct (A.Prog.Seg.R10B.r10b_out_dec
                         ((A.ACtlCutP.Sfr fr + 306, A.ACtlCutP.Sfr fr + 313) :: A.Prog.Seg.R10B.r10b_W fr spv)
                         (bv_unsigned x)) as [Ho|Ho]; [exact Ho | exfalso; exact (Hx Ho)].
  - intros x Hx. unfold lib.Reusable.YK04.mrestrict in *.
    destruct (lib.Reusable.YA0n.w_H W3 x); [exact Hx|].
    destruct (Z_le_gt_dec A.Prog.ImgBounds.IMG_HI (bv_unsigned x)) as [Hge|Hlt].
    + apply r10_wv_some; [exact Hge|]. apply WM.
      unfold wview. destruct (mem3 x); [discriminate | exfalso; apply Hx; reflexivity].
    + rewrite MU; [exact Hx|].
      destruct (A.Prog.Seg.R10B.r10b_out_dec
                  ((A.ACtlCutP.Sfr fr + 306, A.ACtlCutP.Sfr fr + 313) :: A.Prog.Seg.R10B.r10b_W fr spv)
                  (bv_unsigned x)) as [Ho|Ho]; [exact Ho|].
      pose proof (Hlow _ Ho). lia.
  - exact Hhid.
  - exact Hsbm.
  - intros a Ha. destruct (A.Prog.Seg.R10B.r10b_notout _ _ _ _ Ha) as [H|H].
    + right; right; right. exists 6, (A.ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
      unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
      change (lib.Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
      unfold A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in H.
      unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. lia.
    + destruct (A.Prog.Seg.R10B.r10b_W_in fr spv a H) as [H'|H'].
      * right; right; right. exists 6, (A.ACtlCut.c_fpos cx). split; [left; reflexivity|]. left.
        unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
        change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
      * left. unfold A.ACfn.LLVMF_STK. lia.
Qed.

(* r10_N without the fragment record FGBr (the callee rewrites [fr + 2256, fr + 2328)). *)
Definition r10b56_N (cx : A.ACtlCut.ctlcx) (b : nat) (phi fr : Z) (regs : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  A.ACtlCutP.HB m phi (A.ACtlCutP.rnb cx b) /\ A.ACtlCutP.OURb cx fr m /\ A.ACtlCutP.OUTA fr m /\
  A.ACtlCutP.spill regs m 112 (A.Prog.SlotModel.mrow (A.ACtlCut.c_in cx)) /\
  A.ACtlCutP.spill regs m 128 (fr + 544) /\ A.ACtlCutP.PRO cx fr regs m /\
  A.ACtlCutP.spill regs m 104 0x21140 /\ A.ACtlCutP.spill regs m 96 0x1234 /\
  A.ACtlCutP.spill regs m 64 0xe38f0000 /\
  A.ACtlCutP.spill regs m 144 (fr + 2688) /\ A.ACtlCutP.spill regs m 192 (fr + 2768) /\
  (exists idb, lib.Lib.Step.rw_cells segs m (fr + 2688) [lib.Lib.Cells.CB 38 idb]) /\
  (exists junk, lib.Lib.Step.rw_cells segs m (fr + 2768) [lib.Lib.Cells.CB 72 junk]) /\
  A.ACtlCutP.spill regs m 280 (fr + 3040) /\ A.ACtlCutP.spill regs m 240 (fr + 3056) /\
  (exists jy, lib.Lib.Step.rw_cells segs m (fr + 3040) [lib.Lib.Cells.CB 1 jy]) /\
  (exists junk, lib.Lib.Step.rw_cells segs m (fr + 3056) [lib.Lib.Cells.CB 32 junk]) /\
  A.ACtlCutP.spill regs m 152 (A.ACtlCutP.Sfr fr + 68) /\ A.AsanRT.addressable m (fr + 2176) 38 /\
  A.ACtlCutP.IDBr cx fr (A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) b) m /\
  lib.Lib.Mem.bytes_at segs m phi (A.Prog.SlotModel.rt_F (A.ACtlCut.c_in cx) (Z.of_nat b)) /\
  A.ACtlCutP.RXS cx fr regs m.

(* R10A.r10a_keep (R10A.v:955) for b = 5, 6 (lengths from R10B.r10b_rtn / r10b_lens), over a write set W that may
   also cover [fr + 2256, fr + 2504) (the fragment record and the three reply cells): every fact of r10_N but FGBr
   survives. *)
Lemma r10b56_keep : forall cx b phi fr (regs regs' : bvmap 5 word) (m m' : word -> option byte) W A,
  r10_N cx b phi fr regs m -> lib.Lib.Frame.munch W m m' -> lib.Lib.Frame.wmono A.Img0.rsegs m m' ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 -> A.ACtlCut.rgv regs 9 A ->
  0 <= A -> A + 416 < 2 ^ 64 -> (b = 5 \/ b = 6)%nat -> A.ACtlCutP.rnb cx b <> 0 ->
  0 <= fr -> fr mod 8 = 0 -> A.ACtlCut.c_n cx = Z.of_nat (length (A.ACtlCut.c_in cx)) ->
  (forall x, A <= x < A + 416 -> lib.Lib.Frame.outside W x) ->
  (forall x, fr <= x < fr + 3136 -> ~ (fr + 2256 <= x < fr + 2504) -> lib.Lib.Frame.outside W x) ->
  (forall x, phi <= x < phi + A.ACtlCutP.rnb cx b -> lib.Lib.Frame.outside W x) ->
  (forall k, 0 <= k < 392 -> ~ (306 <= k < 318) -> lib.Lib.Frame.outside W (A.ACtlCutP.Sfr fr + k)) ->
  (forall i, 0 <= i < A.ACtlCutP.rnb cx b -> lib.Lib.Frame.outside W (A.AsanRT.shadow_addr (phi + i))) ->
  (0 < A.ACtlCut.c_n cx -> forall x, A.ACtlCut.c_p cx <= x < A.ACtlCut.c_p cx + A.ACtlCut.c_n cx ->
     lib.Lib.Frame.outside W x) ->
  (0 < A.ACtlCut.c_n cx -> forall i, 0 <= i < A.ACtlCut.c_n cx ->
     lib.Lib.Frame.outside W (A.AsanRT.shadow_addr (A.ACtlCut.c_p cx + i))) ->
  r10b56_N cx b phi fr regs' m'.
Proof.
  intros cx b phi fr regs regs' m m' W A
    (HHB & HOUR & HOUTA & H112 & H128 & HPRO & H104 & H96 & H64 & H144 & H192 & (idb & HC2688) &
     (j1 & HC2768) & H280 & H240 & (jy & HC3040) & (j2 & HC3056) & H152 & HA2176 & HID & _ & HPHI &
     (X48 & X56 & X88 & X80 & X72 & X16 & X8 & X200 & X216 & XA2256))
    MU WM E9 Hr9 HA0 HA1 Hb56 Hnz Hfr0 Hfr8 Ecn HoA HoF HoP HoS HoPS HoI HoIS.
  destruct (A.Prog.Seg.R10B.r10b_rtn (A.ACtlCut.c_in cx) (Z.of_nat b) Hnz) as (_ & Hnb & LFl).
  change (A.Prog.SlotModel.rt_n (A.ACtlCut.c_in cx) (Z.of_nat b)) with (A.ACtlCutP.rnb cx b) in Hnb, LFl.
  pose proof (A.Prog.Seg.R10B.r10b_lens (A.ACtlCut.c_in cx)) as (_ & _ & _ & HI5 & HI6).
  assert (LIl : length (A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) b) = 38%nat)
    by (destruct Hb56 as [-> | ->]; assumption).
  assert (SK : forall off v, 0 <= off <= 408 -> A.ACtlCutP.spill regs m off v -> A.ACtlCutP.spill regs' m' off v)
    by (intros off v Ho Hs; exact (A.Prog.Seg.R10A.r10a_spill_keep regs regs' m m' W A off v E9 Hr9 HA0 HA1 Ho MU HoA Hs)).
  assert (FB : forall a l, fr <= a -> a + Z.of_nat (length l) <= fr + 3136 ->
                 (a + Z.of_nat (length l) <= fr + 2256 \/ fr + 2504 <= a) ->
                 lib.Lib.Mem.bytes_at segs m a l -> lib.Lib.Mem.bytes_at segs m' a l).
  { intros a l H1 H2 H3 Hb. apply (A.Prog.RcAsanFPLib.fl_bytes W m m' a l Hb MU). intros x Hx. apply HoF; lia. }
  assert (RK : forall a n l, fr <= a -> a + Z.of_nat n <= fr + 3136 ->
                 (a + Z.of_nat n <= fr + 2256 \/ fr + 2504 <= a) ->
                 lib.Lib.Step.rw_cells segs m a [lib.Lib.Cells.CB n l] ->
                 lib.Lib.Step.rw_cells segs m' a [lib.Lib.Cells.CB n l]).
  { intros a n l H1 H2 H3 Hc. apply (A.Prog.Seg.R10A.r10a_rw_keep W m m' a n l Hc MU WM).
    intros x Hx. apply HoF; lia. }
  assert (AK : forall k n, 0 <= k -> 0 <= n -> k + n <= 3136 -> (k + n <= 2448 \/ 2544 <= k) ->
                 A.AsanRT.addressable m (fr + k) n -> A.AsanRT.addressable m' (fr + k) n).
  { intros k n H1 H2 H3 H4 Ha. apply (A.Prog.Seg.R10A.r10a_addr_keep W m m' (fr + k) n Ha MU). intros i Hi.
    replace (fr + k + i) with (fr + (k + i)) by lia.
    rewrite (A.Prog.Seg.R10A.r10a_sh_fr fr (k + i) Hfr8 ltac:(lia)).
    change (A.Prog.SlotInv.Sfr fr) with (A.ACtlCutP.Sfr fr).
    apply HoS.
    - clear - H1 H2 H3 Hi. Z.div_mod_to_equations. lia.
    - clear - H1 H2 H3 H4 Hi. Z.div_mod_to_equations. lia. }
  split.
  { destruct HHB as (Hnz' & Had). split; [exact Hnz'|].
    apply (A.Prog.Seg.R10A.r10a_addr_keep W m m' phi _ Had MU). intros i Hi. apply HoPS.
    unfold A.ACtlK.a_size in Hi. lia. }
  split; [unfold A.ACtlCutP.OURb in HOUR |- *; apply (FB (fr + 2624) (A.Prog.SlotModel.OUR (A.ACtlCut.c_in cx)));
          [lia | rewrite A.Prog.SlotModel.OUR_length; cbn; lia | right; lia | exact HOUR]|].
  split; [unfold A.ACtlCutP.OUTA in HOUTA |- *; apply (AK 544 1492); [lia | lia | lia | left; lia | exact HOUTA]|].
  split; [exact (SK 112 _ ltac:(lia) H112)|].
  split; [exact (SK 128 _ ltac:(lia) H128)|].
  split.
  { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & PA2624 & PIN & PBLK &
      P184 & P256 & P264 & P272 & P32).
    split; [exact (SK 40 _ ltac:(lia) P40)|].
    split; [exact (SK 120 _ ltac:(lia) P120)|].
    split; [exact (SK 136 _ ltac:(lia) P136)|].
    split; [exact (SK 160 _ ltac:(lia) P160)|].
    split; [exact (SK 168 _ ltac:(lia) P168)|].
    split; [exact (SK 176 _ ltac:(lia) P176)|].
    split; [exact (SK 208 _ ltac:(lia) P208)|].
    split; [exact (SK 248 _ ltac:(lia) P248)|].
    split; [apply (AK 2624 6); [lia | lia | lia | right; lia | exact PA2624]|].
    split.
    { apply (A.Prog.RcAsanFPLib.fl_bytes W m m' _ _ PIN MU). intros x Hx. rewrite <- Ecn in Hx.
      destruct (Z_lt_le_dec 0 (A.ACtlCut.c_n cx)) as [Hn|Hn]; [exact (HoI Hn x Hx) | lia]. }
    split.
    { intros Hn. exact (A.Prog.Seg.R10A.r10a_addr_keep W m m' _ _ (PBLK Hn) MU (HoIS Hn)). }
    split; [exact (SK 184 _ ltac:(lia) P184)|].
    split; [exact (SK 256 _ ltac:(lia) P256)|].
    split; [exact (SK 264 _ ltac:(lia) P264)|].
    split; [exact (SK 272 _ ltac:(lia) P272) | exact (SK 32 _ ltac:(lia) P32)]. }
  split; [exact (SK 104 _ ltac:(lia) H104)|].
  split; [exact (SK 96 _ ltac:(lia) H96)|].
  split; [exact (SK 64 _ ltac:(lia) H64)|].
  split; [exact (SK 144 _ ltac:(lia) H144)|].
  split; [exact (SK 192 _ ltac:(lia) H192)|].
  split; [exists idb; apply (RK (fr + 2688) 38%nat idb); [lia | cbn; lia | right; lia | exact HC2688]|].
  split; [exists j1; apply (RK (fr + 2768) 72%nat j1); [lia | cbn; lia | right; lia | exact HC2768]|].
  split; [exact (SK 280 _ ltac:(lia) H280)|].
  split; [exact (SK 240 _ ltac:(lia) H240)|].
  split; [exists jy; apply (RK (fr + 3040) 1%nat jy); [lia | cbn; lia | right; lia | exact HC3040]|].
  split; [exists j2; apply (RK (fr + 3056) 32%nat j2); [lia | cbn; lia | right; lia | exact HC3056]|].
  split; [exact (SK 152 _ ltac:(lia) H152)|].
  split; [apply (AK 2176 38); [lia | lia | lia | left; lia | exact HA2176]|].
  split; [unfold A.ACtlCutP.IDBr in HID |- *; apply (FB (fr + 2176) _);
          [lia | rewrite LIl; cbn; lia | left; rewrite LIl; cbn; lia | exact HID]|].
  split.
  { apply (A.Prog.RcAsanFPLib.fl_bytes W m m' _ _ HPHI MU). rewrite LFl. intros x Hx. apply HoP. lia. }
  split; [exact (SK 48 _ ltac:(lia) X48)|].
  split; [exact (SK 56 _ ltac:(lia) X56)|].
  split; [exact (SK 88 _ ltac:(lia) X88)|].
  split; [exact (SK 80 _ ltac:(lia) X80)|].
  split; [exact (SK 72 _ ltac:(lia) X72)|].
  split; [exact (SK 8 _ ltac:(lia) X16)|].
  split; [exact (SK 0 _ ltac:(lia) X8)|].
  split; [exact (SK 200 _ ltac:(lia) X200)|].
  split; [exact (SK 216 _ ltac:(lia) X216)|].
  apply (AK 2256 72); [lia | lia | lia | left; lia | exact XA2256].
Qed.

Lemma r10_b56 : forall POST (b : nat), (b = 5 \/ b = 6)%nat ->
  CF POST (ix_cut C_A81708_at [Z.of_nat b]) -> CF POST (ix_cut C_A817c8_at [Z.of_nat b]) ->
  CF POST (ix_cut C_A81680_at [Z.of_nat b]).
Proof.
  pose proof A.Prog.SlotInv.FRAME_BYTES_val as HFRAMEb. pose proof A.Prog.SlotInv.FRAME_SHADOW_val as HFRAMEs.
  intros POST b Hb56 HX6 HX5 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  r10_open Hbody.
  destruct Hb as (phi & HP & HFRAC & (Hn & Hb6 & HHB & R23 & HOUR & HOUTA & HCUR & S112 & S128 & HPRO & S104 &
    S96 & S64 & S144 & S192 & C2688 & C2768 & S280 & S240 & C3040 & C3056 & S152 & R21 & A2176) &
    (HRF & HRXS & Ha0 & R27)).
  destruct HRF as (((_ & _ & _ & _ & HID & HFG) & Hnz & R24 & HPHI) & R18).
  (* G2: the entry facts, the frame and the two blocks *)
  r10_g2 b cx fr phi regs3 mem3 ly3 S3 W3 md3 HB HJ HF HL HFRAC HP HHB Hnz.
  assert (ESh : Sh = A.ACtlCutP.Sfr fr) by reflexivity.
  assert (EK : A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K = 4656) by reflexivity.
  assert (EHM : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (EAE : A.AsanRT.APPMEM_END = 140737488355328) by reflexivity.
  assert (EIH : A.Prog.ImgBounds.IMG_HI = 6283264) by reflexivity.
  pose proof lib.Reusable.YCbq.asan_consts as (HAC & _).
  (* the journal's stack window, the entry stack's anchoring and the layout's stack range *)
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hstk & _).
  destruct Hstk as (_ & _ & Hc1 & Hc2 & Hc4 & Hc3 & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  try unfold A.ACfn.LLVMF_STK in Hwin, Hc2.
  (* the frame lies above the image (a Theorem Labs lane's ctl_frame_above_img); its bytes are present and visible *)
  pose proof (A.ProgWorld_Fs.ctl_frame_above_img B ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR Hinf) as HGT.
  change (A.Prog.ImgBounds.IMG_HI <= lib.Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx)) in HGT.
  rewrite <- Efr in HGT.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (HfappF : forall x, fr <= x < fr + A.Prog.SlotInv.FRAME_BYTES -> A.AsanRT.app_mem x)
    by (intros x Hx; apply Hfapp; lia).
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR Hinf)
    as (_ & _ & Hfpres & _).
  rewrite <- Efr in Hfpres. change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfpres.
  (* the turn's block lies below the stack, is present and visible, and so is its shadow hull *)
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hphiin)
    as (_ & _ & Hpceil & _ & Hppres & _).
  rewrite Ereq in Hpceil, Hppres.
  destruct (lib.Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hphiin) as (_ & Hphull).
  rewrite Ereq in Hphull.
  assert (Hphiw : phi + A.ACtlCutP.rnb cx b + 32768 <= A.ACtlCut.c_sp cx) by lia.
  (* the input block lies below the stack too *)
  assert (Hinb2 : 0 < A.ACtlCut.c_n cx -> A.ACtlCut.c_p cx + A.ACtlCut.c_n cx + 32768 <= A.ACtlCut.c_sp cx).
  { intros Hn0. destruct Hinp as [(? & _) | (_ & Hin0)]; [lia|].
    assert (Hin3 : In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hin0).
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3) as (_ & _ & Hq & _).
    assert (Eq : lib.Reusable.YG00.req_size (A.ACtlCut.c_n cx) = A.ACtlCut.c_n cx)
      by (unfold lib.Reusable.YG00.req_size; destruct (Z.eqb_spec (A.ACtlCut.c_n cx) 0); lia).
    rewrite Eq in Hq. lia. }
  clear Hinp.
  (* the model of turn b: k_b = 11, the record lengths *)
  assert (Hk11 : A.Prog.SlotModel.rt_k (A.ACtlCut.c_in cx) (Z.of_nat b) = 11).
  { apply A.Prog.Seg.B3Rtm.a_rtm_k11; [destruct Hb56 as [-> | ->]; [left | right]; reflexivity | exact Hnz]. }
  unfold A.ACtlCut.a0v, A.ACtlCut.rgv in Ha0. rewrite Hk11 in Ha0.
  destruct (A.Prog.Seg.R10B.r10b_rtn (A.ACtlCut.c_in cx) (Z.of_nat b) Hnz) as (_ & Hnb & HLF).
  change (A.Prog.SlotModel.rt_n (A.ACtlCut.c_in cx) (Z.of_nat b)) with (A.ACtlCutP.rnb cx b) in Hnb, HLF.
  pose proof (A.Prog.Seg.R10B.r10b_lens (A.ACtlCut.c_in cx)) as (HL5 & HL6 & HL7 & _ & _).
  assert (HLst : length (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) b) = 72%nat)
    by (destruct Hb56 as [-> | ->]; assumption).
  assert (HLfs : length (A.Prog.SlotModel.fg_st (A.ACtlCutP.rnb cx b) (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) b)
                   (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) (Z.of_nat b))) = 72%nat).
  { pose proof (proj2 (A.Prog.Seg.B3Rtm.a_RS_56 (A.ACtlCut.c_in cx) b Hb56 Hnz)) as E.
    unfold A.ACtlCutP.rnb. rewrite <- E. destruct Hb56 as [-> | ->]; assumption. }
  assert (Hg50l : length (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) (Z.of_nat b)) = 50%nat)
    by (unfold A.Prog.SlotModel.rt_g; apply A.Prog.SlotModel.fr50_length).
  r10b56_hide Hb56. r10b56_hide Hinb. r10b56_hide Hinb2.
  (* visibility in the cut's world: the stack window, the frame, the block, the frame shadow *)
  assert (Hvis_stk : forall lo len, A.ACtlCut.c_sp cx - 32768 <= lo -> 0 <= len -> lo + len <= A.ACtlCut.c_sp cx ->
            A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) lo len).
  { intros lo len H1 H2 H3. apply (r10b56_vis_pres _ mem3); [lia | lia | intros a Ha; apply Hwin; lia]. }
  assert (Hvis_fr : forall lo len, fr <= lo -> 0 <= len -> lo + len <= fr + 4096 ->
            A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) lo len).
  { intros lo len H1 H2 H3. apply (r10b56_vis_pres _ mem3);
      [lia | lia | intros a Ha; exact (proj1 (Hfpres a ltac:(lia)))]. }
  assert (Hvis_phi : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) phi 50).
  { apply (r10b56_vis_pres _ mem3); [lia | lia | intros a Ha; exact (proj1 (Hppres a ltac:(lia)))]. }
  pose proof (r10_fsh_vis cx fr ly3 S3 W3 mem3 md3 HAR HF Efr Hfr0) as HFSV.
  (* the window of the three metadata stores *)
  assert (ST306 : lib.Lib.Frame.stk A.Img0.rsegs mem3 (Sh + 306) (Sh + 313)).
  { pose proof Hrt as (_ & HCUT & _ & _). split; [lia|]. split; [lia|]. intros a Ha. apply HCUT.
    - apply (r10_cut_fsh cx fr ly3 S3 a Hinf Efr). rewrite <- ESh. lia.
    - replace a with (A.Prog.SlotInv.Sfr fr + (a - Sh)) by (unfold Sh, A.Prog.SlotInv.Sfr, A.ACtlCutP.Sfr; lia).
      apply A.Prog.Seg.R10B.r10b_fsh; [exact HfappF | lia]. }
  pose proof (A.ProgBridge.rng_of_visible _ _ _ (HFSV 306 7 ltac:(lia) ltac:(lia) ltac:(lia))) as Rsh.
  (* the memory facts the loads and the call read *)
  assert (HA0 : 0 <= A) by lia.
  assert (Hsep : fr + A.Prog.SlotInv.FRAME_BYTES <= sp - A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K) by lia.
  assert (HoW1 : forall x, A.AsanRT.app_mem x -> lib.Lib.Frame.outside [(Sh + 306, Sh + 313)] x)
    by (intros x Hx; exact (A.Prog.Seg.R10B.r10b_appbyte_out fr 306 313 x HfappF ltac:(lia) ltac:(lia) Hx)).
  assert (Happhi : forall x, A.ACtlCut.c_sp cx - 32768 <= x < A.ACtlCut.c_sp cx -> A.AsanRT.app_mem x)
    by (intros x Hx; right; lia).
  assert (STwin : lib.Lib.Frame.stk A.Img0.rsegs mem3 (sp - A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K) sp)
    by (apply (r10b56_stk_pres (lib.Reusable.YA0n.w_H W3)); [lia | lia | intros a Ha; apply Hwin; lia]).
  assert (STfr : lib.Lib.Frame.stk A.Img0.rsegs mem3 (fr + 2256) (fr + 2504))
    by (apply (r10b56_stk_pres (lib.Reusable.YA0n.w_H W3));
        [lia | lia | intros a Ha; exact (proj1 (Hfpres a ltac:(lia)))]).
  assert (HFg : lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 phi (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) (Z.of_nat b)))
    by exact (A.Prog.Seg.R10B.r10b_g50 mem3 phi (A.Prog.SlotModel.rt_F (A.ACtlCut.c_in cx) (Z.of_nat b)) HPHI
                ltac:(rewrite HLF; lia)).
  assert (HAphi50 : A.AsanRT.addressable mem3 phi 50).
  { pose proof Hphiad as (H1 & H2 & H3 & H4). unfold A.ACtlK.a_size in H2, H3, H4.
    split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi. apply H4. lia. }
  assert (HRWst : lib.Lib.Step.rw_cells A.Img0.rsegs mem3 (fr + 2256)
            [lib.Lib.Cells.CB 72 (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) b)]).
  { split; [split|].
    - cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf]. split; [exact HLst | exact I].
    - cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact HFG.
    - cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. rewrite ?Nat.add_0_r.
      apply (A.Prog.Seg.R10B.r10b_wr_sub _ _ _ _ _ STfr); lia. }
  (* the five runtime cells the fragment contract reads (a Theorem Labs lane's rt_of_core_C: RT_used_C's REAL_USED slots,
     asan_cf_cells) *)
  pose proof (A.ProgWorldRtC.rt_of_core_C B MT XM_LIB RLO RHI [] TFIB_SYMS LAWS cx (A.ACtlCut.own6 cx) k ly3 S3 W3
                (lib.Lib.MState.MS regs3 lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x81680) lib.Reusable.YK11.fp_csr None
                   mem3 (lib.Reusable.YK11.seg_rom segs)) md3 HB HJ Hrt) as HRTU.
  unfold A.ProgWorldRtC.RT_used_C in HRTU.
  destruct HRTU as (_ & _ & _ & _ & HCF & _ & _ & HREALS).
  assert (HBc1 : lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 0xa17f0 (lib.Lib.Mem.le8 (lib.Lib.Mem.wa 0x97b0c))).
  { refine (proj1 (Forall_forall _ _) HREALS (0xa17f0, 0x97b0c) _ _).
    - unfold A.AsanRT.RT_REALS. right; right; left; reflexivity.
    - unfold A.ProgWorld.REAL_USED. left; reflexivity. }
  assert (HBc2 : lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 0xa17e8 (lib.Lib.Mem.le8 (lib.Lib.Mem.wa 0x97bdc))).
  { refine (proj1 (Forall_forall _ _) HREALS (0xa17e8, 0x97bdc) _ _).
    - unfold A.AsanRT.RT_REALS. do 9 right. left; reflexivity.
    - unfold A.ProgWorld.REAL_USED. right; left; reflexivity. }
  pose proof HCF as (HCF1 & _ & _ & _ & _ & _ & HCF7 & _).
  assert (HBc3 : lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 0x9fac0 (lib.Lib.Mem.le8 (lib.Lib.Mem.wa 0x13a3a8)))
    by exact HCF1.
  assert (HBc4 : lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 (0x13a3a8 + 254) [Z_to_bv 8 1]).
  { replace (0x13a3a8 + 254) with (A.AsanRT.RT_CF + 240 + Z.of_nat 14) by (unfold A.AsanRT.RT_CF; lia).
    exact (A.Prog.Seg.R10B.r10b_byte mem3 (A.AsanRT.RT_CF + 240) _ 14%nat (Z_to_bv 8 1) HCF7 eq_refl). }
  assert (HBc5 : lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 (0x13a3a8 + 255) [Z_to_bv 8 1]).
  { replace (0x13a3a8 + 255) with (A.AsanRT.RT_CF + 240 + Z.of_nat 15) by (unfold A.AsanRT.RT_CF; lia).
    exact (A.Prog.Seg.R10B.r10b_byte mem3 (A.AsanRT.RT_CF + 240) _ 15%nat (Z_to_bv 8 1) HCF7 eq_refl). }
  clear HREALS HCF HCF1 HCF7.
  (* R10BFon.r10b_pre_on after the three metadata stores: R10B.r10b_pre with the fragment's own shadow region *)
  assert (HPRE : forall m1, lib.Lib.Frame.munch [(Sh + 306, Sh + 313)] mem3 m1 ->
            lib.Lib.Frame.wmono A.Img0.rsegs mem3 m1 -> lib.Lib.Frame.stk A.Img0.rsegs m1 (Sh + 306) (Sh + 313) ->
            A.MemNorm.ro_agree A.Img0.rsegs m1 ->
            lib.Lib.Mem.bytes_at A.Img0.rsegs m1 (Sh + 306) [Z_to_bv 8 2] ->
            lib.Lib.Mem.bytes_at A.Img0.rsegs m1 (Sh + 308) [Z_to_bv 8 0] ->
            lib.Lib.Mem.bytes_at A.Img0.rsegs m1 (Sh + 312) [Z_to_bv 8 0] ->
            A.Prog.Seg.R10BFon.r10b_pre_on m1 A sp fr phi (A.ACtlCutP.rnb cx b)
              (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) (Z.of_nat b)) (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) b)).
  { intros m1 MU1 WM1 ST1 RO1 B306 B308 B312.
    pose proof HRXS as (X48 & X56 & X88 & X80 & X72 & _ & _ & _ & _ & XA2256).
    assert (Hsk : forall off v, 0 <= off -> off + 8 <= 416 ->
              A.ACtlCutP.spill regs3 mem3 off v -> A.ACtlCutP.spill regs3 m1 off v).
    { intros off v Ho1 Ho2 HS.
      apply (A.Prog.Seg.R10B.r10b_spill_keep regs3 regs3 mem3 m1 off v A _ HS R9 eq_refl HA0 ltac:(lia) Ho1 MU1).
      intros x Hx. apply HoW1. right. lia. }
    assert (HWlo1 : forall x, 0 <= x < 6283264 -> lib.Lib.Frame.outside [(Sh + 306, Sh + 313)] x)
      by (intros x Hx; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
    unfold A.Prog.Seg.R10B.r10b_pre.
    split; [exact (A.Prog.Seg.R10B.r10b_spill_rd regs3 m1 48 _ A (Hsk 48 _ ltac:(lia) ltac:(lia) X48) R9 HA0
                     ltac:(lia) ltac:(lia))|].
    split; [exact (A.Prog.Seg.R10B.r10b_spill_rd regs3 m1 88 _ A (Hsk 88 _ ltac:(lia) ltac:(lia) X88) R9 HA0
                     ltac:(lia) ltac:(lia))|].
    split; [exact (A.Prog.Seg.R10B.r10b_spill_rd regs3 m1 80 _ A (Hsk 80 _ ltac:(lia) ltac:(lia) X80) R9 HA0
                     ltac:(lia) ltac:(lia))|].
    split; [exact (A.Prog.Seg.R10B.r10b_spill_rd regs3 m1 72 _ A (Hsk 72 _ ltac:(lia) ltac:(lia) X72) R9 HA0
                     ltac:(lia) ltac:(lia))|].
    split.
    { apply (A.Prog.Seg.R10B.r10b_stk_tr _ mem3 m1 _ _ STwin MU1 WM1). intros x Hx. left.
      apply HoW1, Happhi. lia. }
    split.
    { apply (A.Prog.RcAsanFPLib.fl_bytes _ mem3 m1 phi _ HFg MU1). rewrite Hg50l. intros x Hx.
      apply HoW1. apply (r10_in_app_mem _ _ Hpapp). lia. }
    split.
    { apply (A.Prog.Seg.R10B.r10b_addr_keep _ mem3 m1 phi 50 HAphi50 MU1). intros i Hi.
      apply (A.Prog.Seg.R10B.r10b_shobj_out fr 306 313 phi 50 i Hfr8 Hfr0 Hphi0); [|exact Hi].
      destruct Hpdj as [Hd|Hd]; [left | right]; lia. }
    split.
    { apply (A.Prog.Seg.R10B.r10b_rwcb_keep _ mem3 m1 (fr + 2256) 72 _ MU1 WM1); [|exact HRWst].
      intros x Hx. apply HoW1, HfappF. lia. }
    split.
    { apply (A.Prog.Seg.R10B.r10b_addr_keep _ mem3 m1 (fr + 2256) 72 XA2256 MU1). intros i Hi.
      apply (A.Prog.Seg.R10B.r10b_shobj_out fr 306 313 (fr + 2256) 72 i Hfr8 Hfr0 ltac:(lia));
        [left; lia | exact Hi]. }
    split.
    { apply (A.Prog.Seg.R10B.r10b_stk_tr _ mem3 m1 _ _ STfr MU1 WM1). intros x Hx. left.
      apply HoW1, HfappF. lia. }
    split.
    { apply (A.Prog.Seg.R10B.r10b_addr_r m1 (fr + 2448) 2 (Z_to_bv 8 2));
        [lia | clear - Hfr8; Z.div_mod_to_equations; lia | lia | vm_compute; reflexivity | lia |
         intros i Hi; apply HfappF; lia |].
      replace (A.AsanRT.shadow_addr (fr + 2448)) with (Sh + 306)
        by (replace (fr + 2448) with (fr + 8 * 306) by lia; rewrite A.Prog.Seg.R10B.r10b_sh8; reflexivity).
      exact B306. }
    split.
    { apply (A.Prog.Seg.R10B.r10b_addr_z m1 (fr + 2464) 1 8);
        [reflexivity | lia | clear - Hfr8; Z.div_mod_to_equations; lia | lia | intros i Hi; apply HfappF; lia |].
      replace (A.AsanRT.shadow_addr (fr + 2464)) with (Sh + 308)
        by (replace (fr + 2464) with (fr + 8 * 308) by lia; rewrite A.Prog.Seg.R10B.r10b_sh8; reflexivity).
      exact B308. }
    split.
    { apply (A.Prog.Seg.R10B.r10b_addr_z m1 (fr + 2496) 1 8);
        [reflexivity | lia | clear - Hfr8; Z.div_mod_to_equations; lia | lia | intros i Hi; apply HfappF; lia |].
      replace (A.AsanRT.shadow_addr (fr + 2496)) with (Sh + 312)
        by (replace (fr + 2496) with (fr + 8 * 312) by lia; rewrite A.Prog.Seg.R10B.r10b_sh8; reflexivity).
      exact B312. }
    pose proof (r10_rtC_keep_sh B ly3 S3 mem3 m1 fr 306 313 Hrt MU1 WM1 Hfapp ltac:(lia) ltac:(lia))
      as (HC1 & HCUT1 & _ & _).
    split; [exact HC1|].
    split; [exact (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly3 S3) _ m1
                     (fun a Ha => r10_fragR_cut cx fr ly3 S3 phi (A.ACtlCutP.rnb cx b) _ _ _ a Hinf Efr Hfr0
                                    ltac:(lia) Hphiin ltac:(rewrite Ereq; lia) ltac:(lia) ltac:(lia) Ha) HCUT1)|].
    split; [apply (A.Prog.Seg.R10B.r10b_keep_low _ mem3 m1 _ _ MU1 HBc1 HWlo1);
            rewrite lib.Lib.Mem.length_le8; lia|].
    split; [apply (A.Prog.Seg.R10B.r10b_keep_low _ mem3 m1 _ _ MU1 HBc2 HWlo1);
            rewrite lib.Lib.Mem.length_le8; lia|].
    split; [apply (A.Prog.Seg.R10B.r10b_keep_low _ mem3 m1 _ _ MU1 HBc3 HWlo1);
            rewrite lib.Lib.Mem.length_le8; lia|].
    split; [apply (A.Prog.Seg.R10B.r10b_keep_low _ mem3 m1 _ _ MU1 HBc4 HWlo1); cbn [length]; lia|].
    apply (A.Prog.Seg.R10B.r10b_keep_low _ mem3 m1 _ _ MU1 HBc5 HWlo1); cbn [length]; lia. }
  (* the arm's exit pc *)
  assert (Hpce : exists pce, (Z.of_nat b = 6 /\ pce = 0x81708) \/ (Z.of_nat b = 5 /\ pce = 0x817c8))
    by (destruct Hb56 as [-> | ->]; [exists 0x817c8; right | exists 0x81708; left]; split; reflexivity).
  destruct Hpce as (pce & Harm).
  (* G3: the cut's state in the run's form, moved to the canonical register map *)
  r10_g3 (ix_cut C_A81680_at [Z.of_nat b]) 0x81680 POST cx regs3 W3 mem3 md3.
  (* G4: the run R10BFon.r10b_evt_F_on at RNG_W (w_H W3) (the fragment's narrowed contract by its PROVED closed
     form), lifted with SRr_fevt_hid *)
  lazymatch goal with
  | |- context [lib.Lib.Frame.mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31] =>
      pose proof (A.Prog.Seg.R10BFon.r10b_evt_F_on
                    A.Prog.reac_ctrl_identity_fragment_F_on.reac_ctrl_identity_fragment_F_holds_on_closed
                    (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3))
                    x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3
                    (Z.of_nat b) pce sp A Sh fr phi (A.ACtlCutP.rnb cx b)
                    (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) (Z.of_nat b))
                    (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) b)) as HRUN
  end.
  specialize (HRUN Harm).
  specialize (HRUN ltac:(exact R2)).
  specialize (HRUN ltac:(exact R9)).
  specialize (HRUN ltac:(exact R19)).
  specialize (HRUN ltac:(exact R23)).
  specialize (HRUN ltac:(exact R27)).
  specialize (HRUN ltac:(exact Ha0)).
  specialize (HRUN ltac:(exact R24)).
  specialize (HRUN ltac:(exact R18)).
  specialize (HRUN ltac:(lia)).
  specialize (HRUN ltac:(lia)).
  specialize (HRUN Hsp16).
  specialize (HRUN HA0).
  specialize (HRUN ltac:(lia)).
  specialize (HRUN ltac:(lia)).
  specialize (HRUN ltac:(lia)).
  specialize (HRUN ltac:(lia)).
  specialize (HRUN ltac:(lia)).
  specialize (HRUN Hfr8).
  specialize (HRUN ltac:(lia)).
  specialize (HRUN ltac:(lia)).
  specialize (HRUN ltac:(lia)).
  specialize (HRUN ltac:(destruct Hpdj; [left | right]; lia)).
  specialize (HRUN ltac:(left; lia)).
  specialize (HRUN ltac:(left; exact Hsep)).
  specialize (HRUN ltac:(apply Hfapp; lia)).
  specialize (HRUN Hg50l).
  specialize (HRUN HLst).
  specialize (HRUN ST306).
  specialize (HRUN ltac:(exact (proj2 (proj2 (proj2 Hrt))))).
  specialize (HRUN HPRE).
  specialize (HRUN Rsh).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (Hvis_stk (A + 48) 8 ltac:(lia) ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (Hvis_stk (A + 88) 8 ltac:(lia) ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (Hvis_stk (A + 80) 8 ltac:(lia) ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (Hvis_stk (A + 72) 8 ltac:(lia) ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_bytes_RNG_W _)).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (Hvis_stk (sp - A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K) A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K ltac:(lia) ltac:(lia) ltac:(lia)))).
  specialize (HRUN ltac:(unfold A.Prog.rng_asan.sh_word_rng; right;
    exact (A.ProgBridge.rng_of_visible _ _ _
             (r10b56_zsh_vis (lib.Reusable.YA0n.w_H W3) mem3 (lib.Reusable.YG0f.ly_stk_lo ly3)
                (lib.Reusable.YG0f.ly_stk_hi ly3) sp
                (lib.Reusable.YG0d.al_zshadow _ _ LAWS ly3 S3 W3 mem3 md3
                   (lib.Reusable.YG0f.ly_stk_lo ly3, lib.Reusable.YG0f.ly_stk_hi ly3 - lib.Reusable.YG0f.ly_stk_lo ly3)
                   HAR ltac:(unfold lib.Reusable.YG0n.zero_shadow_ranges; left; reflexivity))
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ Hvis_phi)).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _
    (r10b56_hull_vis _ mem3 phi (A.ACtlCutP.rnb cx b) 49 Hphull ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (Hvis_fr (fr + 2256) 72 ltac:(lia) ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _
    (r10b56_fcov_vis _ fr 2256 71 HFSV Hfr0 ltac:(lia) ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (Hvis_fr (fr + 2448) 2 ltac:(lia) ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _
    (r10b56_fcov_vis _ fr 2448 1 HFSV Hfr0 ltac:(lia) ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (Hvis_fr (fr + 2464) 8 ltac:(lia) ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _
    (r10b56_fcov_vis _ fr 2464 7 HFSV Hfr0 ltac:(lia) ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (Hvis_fr (fr + 2496) 8 ltac:(lia) ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _
    (r10b56_fcov_vis _ fr 2496 7 HFSV Hfr0 ltac:(lia) ltac:(lia) ltac:(lia)))).
  r10b56_hide Harm.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 _ _ (POST cx) HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  intros ms' md' HQ Hhid Hsbm.
  destruct HQ as (R & pc' & m' & Ems & Hpc & m1 & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 &
    K24 & K25 & K26 & K27 & K10 & MU1 & WM1 & ST1 & MU2 & WM2 & RO2 & STw2 & STf1 & FM2).
  subst ms' pc'. unfold lib.Lib.MState.MS in Hhid. cbn [ms_mem] in Hhid.
  (* the two write sets: W1 = [S(fr) + 306, S(fr) + 313), W2 = R10B.r10b_W fr sp *)
  destruct (A.Prog.Seg.R10B.r10b_wfc m1 m' fr sp (A.ACtlCutP.rnb cx b) (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) b)
              (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) (Z.of_nat b)) Hfr0 ltac:(lia) ltac:(lia) (or_introl Hsep)
              HLfs MU2 STw2 STf1 FM2) as (MUW2 & HRD2).
  assert (MUW : lib.Lib.Frame.munch ((Sh + 306, Sh + 313) :: A.Prog.Seg.R10B.r10b_W fr sp) mem3 m').
  { intros x (Hx1 & Hx2). rewrite (MUW2 x Hx2). apply MU1. cbn [lib.Lib.Frame.outside]. split; [exact Hx1 | exact I]. }
  assert (WMW : lib.Lib.Frame.wmono A.Img0.rsegs mem3 m') by (intros x Hx; exact (WM2 x (WM1 x Hx))).
  assert (HshW2 : forall x, A.AsanRT.in_shadow x -> lib.Lib.Frame.outside (A.Prog.Seg.R10B.r10b_W fr sp) x).
  { intros x Hx. apply A.Prog.Seg.R10B.r10b_W_out.
    - destruct (Z_lt_le_dec x (fr + 2256)) as [H1|H1]; [left; exact H1|].
      destruct (Z_lt_le_dec x (fr + 2504)) as [H2|H2]; [|right; exact H2].
      exfalso. exact (A.AsanRTFacts.app_not_shadow x (Hfapp x ltac:(lia)) Hx).
    - left. unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
        A.AsanRT.HIGHMEM_BEG in Hx. lia. }
  assert (HoutW : forall x, A.AsanRT.app_mem x -> (x < fr + 2256 \/ fr + 2504 <= x) ->
            (x < sp - A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K \/ sp <= x) ->
            lib.Lib.Frame.outside ((Sh + 306, Sh + 313) :: A.Prog.Seg.R10B.r10b_W fr sp) x).
  { intros x Hx H1 H2. split; [exact (proj1 (HoW1 x Hx)) | exact (A.Prog.Seg.R10B.r10b_W_out fr sp x H1 H2)]. }
  assert (HshWall : forall x, A.AsanRT.in_shadow x -> ~ (Sh + 306 <= x < Sh + 313) ->
            lib.Lib.Frame.outside ((Sh + 306, Sh + 313) :: A.Prog.Seg.R10B.r10b_W fr sp) x).
  { intros x Hx H1. split; [exact H1 | exact (HshW2 x Hx)]. }
  assert (HRD1 : forall x, Sh + 306 <= x < Sh + 313 ->
            exists bb, lib.Lib.Mem.mrd A.Img0.rsegs m' (lib.Lib.Mem.wa x) = Some bb).
  { intros x Hx. pose proof ST1 as (_ & _ & ST1v). destruct (proj2 (ST1v x Hx)) as (bb & Hbb).
    exists bb. unfold lib.Lib.Mem.mrd in Hbb |- *. rewrite (MUW2 (lib.Lib.Mem.wa x)); [exact Hbb|].
    rewrite lib.Lib.Mem.wa_unsigned by lia. apply HshW2.
    replace x with (A.Prog.SlotInv.Sfr fr + (x - Sh)) by (unfold Sh, A.Prog.SlotInv.Sfr, A.ACtlCutP.Sfr; lia).
    apply A.Prog.Seg.R10B.r10b_fsh; [exact HfappF | lia]. }
  (* the journal, FRAC, ctl_rt and the carried memory facts at R, m', md' *)
  assert (HJ' : journal cx ly3 S3 W3 m' md' k)
    by exact (r10b56_journal cx fr sp k ly3 S3 W3 mem3 md3 m' md' HJ Efr HGT ltac:(lia) ltac:(lia) ltac:(lia)
                MUW WMW Hhid Hsbm).
  assert (HN0 : r10_N cx b phi fr regs3 mem3) by (unfold r10_N; repeat (split; [assumption|]); assumption).
  assert (HN1 : r10b56_N cx b phi fr R m').
  { apply (r10b56_keep cx b phi fr regs3 R mem3 m' _ A HN0 MUW WMW ltac:(exact K9) R9 HA0 ltac:(lia) Hb56 Hnz
             Hfr0 Hfr8 Ecn).
    - intros x Hx. apply HoutW; [right; lia | right; lia | right; lia].
    - intros x Hx Hx'. apply HoutW; [apply Hfapp; lia | lia | left; lia].
    - intros x Hx. apply HoutW; [apply (r10_in_app_mem _ _ Hpapp); lia | lia | left; lia].
    - intros k0 Hk0 Hk0'. apply HshWall; [exact (A.Prog.Seg.R10B.r10b_fsh fr k0 HfappF ltac:(lia)) | lia].
    - intros i Hi. apply HshWall.
      + apply A.AsanRTFacts.shadow_of_app. apply (r10_in_app_mem _ _ Hpapp). lia.
      + exact (proj1 (A.Prog.Seg.R10B.r10b_shobj_out fr 306 313 phi (A.ACtlCutP.rnb cx b) i Hfr8 Hfr0 Hphi0
                        ltac:(destruct Hpdj; [left | right]; lia) Hi)).
    - intros Hn0 x Hx. destruct (Hinb Hn0) as (Hp0 & Hpd & Happ). pose proof (Hinb2 Hn0) as Hq.
      apply HoutW; [apply Happ; exact Hx | destruct Hpd; lia | left; lia].
    - intros Hn0 i Hi. destruct (Hinb Hn0) as (Hp0 & Hpd & Happ). apply HshWall.
      + apply A.AsanRTFacts.shadow_of_app. apply Happ. lia.
      + exact (proj1 (A.Prog.Seg.R10B.r10b_shobj_out fr 306 313 (A.ACtlCut.c_p cx) (A.ACtlCut.c_n cx) i Hfr8 Hfr0
                        Hp0 ltac:(destruct Hpd; [left | right]; lia) Hi)). }
  destruct HN1 as (HHB1 & HOUR1 & HOUTA1 & S112' & S128' & HPRO' & S104' & S96' & S64' & S144' & S192' & C2688' &
    C2768' & S280' & S240' & C3040' & C3056' & S152' & A2176' & HID' & HPHI' & HRXS').
  assert (HFRAC' : A.ACtlCutP.FRAC B cx fr fr R m').
  { apply (r10_frac_keep B cx fr regs3 R mem3 m' ((Sh + 306, Sh + 313) :: A.Prog.Seg.R10B.r10b_W fr sp) A HFRAC R9
             ltac:(lia));
      try (exact K2 || exact K3 || exact K4 || exact K8 || exact K9 || exact K19 || exact K26 || exact MUW).
    - intros x Hx. apply HoutW; [right; lia | right; lia | right; lia].
    - intros x Hx. apply HoutW; [apply Hfapp; lia | left; lia | left; lia].
    - intros x Hx. apply HoutW; [apply Hfapp; lia | right; lia | left; lia].
    - intros x Hx. apply HoutW; [right; lia | right; lia | right; lia].
    - intros x Hx.
      assert (Hsx : A.AsanRT.in_shadow x).
      { replace x with (A.Prog.SlotInv.Sfr fr + (x - A.ACtlCutP.Sfr fr))
          by (unfold A.Prog.SlotInv.Sfr, A.ACtlCutP.Sfr; lia).
        apply A.Prog.Seg.R10B.r10b_fsh; [exact HfappF | lia]. }
      destruct (Z_lt_le_dec x (Sh + 306)) as [H1|H1]; [left; apply HshWall; [exact Hsx | lia]|].
      destruct (Z_lt_le_dec x (Sh + 313)) as [H2|H2]; [right; apply HRD1; lia|].
      left. apply HshWall; [exact Hsx | lia]. }
  pose proof (r10_rtC_exit cx ly3 S3 W3 m' md' k HB HJ') as Hrt'.
  assert (HCUR1 : A.ACtlCutP.CUR cx 7 R).
  { destruct HCUR as (Hc7 & Hc22 & Hc25). split; [exact Hc7|].
    split; [exact (eq_trans K22 Hc22) | exact (eq_trans K25 Hc25)]. }
  (* G5: the arm's exit cut *)
  destruct Harm as [(Eb & ->) | (Eb & ->)].
  - (* b = 6: exit C_A81708_at, the fragment closes the record (FgClose, a0 = 1) *)
    assert (Eb6 : b = 6%nat) by lia. subst b.
    pose proof (A.Prog.Seg.B3Rtm.a_rtm_close (A.ACtlCut.c_in cx) Hnz) as Hc6.
    assert (Hc6a : A.Prog.SlotModel.fcls (A.ACtlCutP.rnb cx 6) (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 6)
                     (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) (Z.of_nat 6)) =
                   A.Prog.SlotModel.fcls (A.Prog.SlotModel.rt_n (A.ACtlCut.c_in cx) 6)
                     (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 6) (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) 6))
      by reflexivity.
    assert (Hc6b : A.Prog.SlotModel.fcls (A.Prog.SlotModel.rt_n (A.ACtlCut.c_in cx) (Z.of_nat 6))
                     (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 6)
                     (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) (Z.of_nat 6)) =
                   A.Prog.SlotModel.fcls (A.Prog.SlotModel.rt_n (A.ACtlCut.c_in cx) 6)
                     (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 6) (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) 6))
      by reflexivity.
    rewrite Hc6a in FM2, K10. rewrite Hc6 in FM2, K10.
    cbn [A.Prog.reac_ctrl_identity_fragment_c.fg_mem] in FM2.
    destruct FM2 as (FG7 & Cpa & Cpp & Cpn).
    assert (E7 : A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 7 =
                 A.Prog.SlotModel.fg_st (A.Prog.SlotModel.rt_n (A.ACtlCut.c_in cx) (Z.of_nat 6))
                   (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 6) (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) (Z.of_nat 6)))
      by exact (proj2 (A.Prog.Seg.B3Rtm.a_RS_56 (A.ACtlCut.c_in cx) 6 (or_intror eq_refl) Hnz)).
    unfold A.Prog.SlotModel.fg_st in E7. rewrite Hc6b, Hc6 in E7. cbn [A.Prog.SlotModel.fg_next] in E7.
    change (lib.Reusable.YA0n.SRr segs W3
              (lib.Reusable.YG0d.cfg_at segs (A.ACtlCut.cut_pc (ix_cut C_A81708_at [Z.of_nat 6])) R m' md')
              (POST cx)).
    apply (HX6 cx [Z.of_nat 6] fr k ly3 S3 W3 R m' md' HB).
    + exact HJ'.
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCut.ix_cut A.ACtlCutP.C_A81708_at].
      split; [reflexivity|]. rewrite r10_ixn0.
      exists phi.
      split; [exact HP|].
      split; [exact HFRAC'|].
      split.
      { split; [exact Hn|]. split; [lia|]. split; [exact HHB1|].
        split; [exact (eq_trans K23 R23)|]. split; [exact HOUR1|]. split; [exact HOUTA1|].
        split; [exact HCUR1|]. split; [exact S112'|]. split; [exact S128'|]. split; [exact HPRO'|].
        split; [exact S104'|]. split; [exact S96'|]. split; [exact S64'|]. split; [exact S144'|].
        split; [exact S192'|]. split; [exact C2688'|]. split; [exact C2768'|]. split; [exact S280'|].
        split; [exact S240'|]. split; [exact C3040'|]. split; [exact C3056'|]. split; [exact S152'|].
        split; [exact (eq_trans K21 R21)|]. exact A2176'. }
      split; [reflexivity|]. split; [exact K10|].
      split.
      { split; [split; [lia|]; split; [exact HCUR1|]; split; [exact HOUR1|]; split; [exact (eq_trans K23 R23)|];
                split; [exact HID' | unfold A.ACtlCutP.FGBr; rewrite E7; exact FG7]|].
        split; [exact Hnz|]. split; [exact (eq_trans K24 R24) | exact HPHI']. }
      split; [exact HRXS'|].
      split; [exact Cpa|]. split; [exact Cpp | exact Cpn].
    + exact Hrt'.
  - (* b = 5: exit C_A817c8_at, the fragment starts the record (FgFirst, a0 = 0) *)
    assert (Eb5 : b = 5%nat) by lia. subst b.
    pose proof (A.Prog.Seg.B3Rtm.a_rtm_first (A.ACtlCut.c_in cx) Hnz) as Hc5.
    assert (Hc5a : A.Prog.SlotModel.fcls (A.ACtlCutP.rnb cx 5) (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 5)
                     (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) (Z.of_nat 5)) =
                   A.Prog.SlotModel.fcls (A.Prog.SlotModel.rt_n (A.ACtlCut.c_in cx) 5)
                     (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 5) (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) 5))
      by reflexivity.
    assert (Hc5b : A.Prog.SlotModel.fcls (A.Prog.SlotModel.rt_n (A.ACtlCut.c_in cx) (Z.of_nat 5))
                     (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 5)
                     (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) (Z.of_nat 5)) =
                   A.Prog.SlotModel.fcls (A.Prog.SlotModel.rt_n (A.ACtlCut.c_in cx) 5)
                     (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 5) (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) 5))
      by reflexivity.
    rewrite Hc5a in FM2, K10. rewrite Hc5 in FM2, K10.
    cbn [A.Prog.reac_ctrl_identity_fragment_c.fg_mem] in FM2.
    assert (E6 : A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 6 =
                 A.Prog.SlotModel.fg_st (A.Prog.SlotModel.rt_n (A.ACtlCut.c_in cx) (Z.of_nat 5))
                   (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 5) (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) (Z.of_nat 5)))
      by exact (proj2 (A.Prog.Seg.B3Rtm.a_RS_56 (A.ACtlCut.c_in cx) 5 (or_introl eq_refl) Hnz)).
    unfold A.Prog.SlotModel.fg_st in E6. rewrite Hc5b, Hc5 in E6. cbn [A.Prog.SlotModel.fg_next] in E6.
    assert (I6 : A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) 6 = A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) 5).
    { rewrite (proj1 (A.Prog.Seg.B3Rtm.a_RS_56 (A.ACtlCut.c_in cx) 5 (or_introl eq_refl) Hnz)).
      unfold A.Prog.SlotModel.fg_id, A.Prog.SlotModel.fg_rf. rewrite Hc5b, Hc5. reflexivity. }
    change (lib.Reusable.YA0n.SRr segs W3
              (lib.Reusable.YG0d.cfg_at segs (A.ACtlCut.cut_pc (ix_cut C_A817c8_at [Z.of_nat 5])) R m' md')
              (POST cx)).
    apply (HX5 cx [Z.of_nat 5] fr k ly3 S3 W3 R m' md' HB).
    + exact HJ'.
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCut.ix_cut A.ACtlCutP.C_A817c8_at].
      split; [reflexivity|]. rewrite r10_ixn0.
      exists phi.
      split; [exact HP|].
      split; [exact HFRAC'|].
      split; [split; [exact Hn|]; split; [lia|]; split; [exact HHB1|]; split; [exact (eq_trans K23 R23)|];
              split; [exact HOUR1|]; split; [exact HOUTA1 | exact HCUR1]|].
      split.
      { split; [lia|]. split; [exact HCUR1|]. split; [exact HOUR1|]. split; [exact (eq_trans K23 R23)|].
        split; [unfold A.ACtlCutP.IDBr; rewrite I6; exact HID' | unfold A.ACtlCutP.FGBr; rewrite E6; exact FM2]. }
      split; [exact (eq_trans K24 R24)|]. split; [exact K10|].
      split; [exact S128'|]. split; [exact HPRO'|]. split; [exact S104'|]. split; [exact S96'|].
      split; [exact S64'|]. split; [exact (eq_trans K21 R21)|]. split; [exact S112'|]. split; [exact S144'|].
      split; [exact S192'|]. split; [exact C2688'|]. split; [exact C2768'|]. split; [exact S280'|].
      split; [exact S240'|]. split; [exact C3040'|]. split; [exact C3056'|]. split; [exact S152'|].
      split; [exact A2176' | exact HRXS'].
    + exact Hrt'.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   7. b >= 7: the entry body states (b <= 6)%nat, so the cut is empty there. *)
Lemma r10_b7 : forall POST (b : nat), (7 <= b)%nat -> CF POST (ix_cut C_A81680_at [Z.of_nat b]).
Proof.
  intros POST b Hb7 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  r10_open Hbody.
  destruct Hb as (phi & _ & _ & (_ & Hb6 & _) & _). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   8. The stage: ACtl.v's Hypothesis seg_R10, character for character (ACtl.v:667-669 at a working branch 1899bed1aee). *)
Lemma glue_seg_R10 : forall POST (b : nat),
  CF POST (ix_cut C_A816c4_at [Z.of_nat b]) -> CF POST (ix_cut C_A81708_at [Z.of_nat b]) -> CF POST (ix_cut C_A81768_at [Z.of_nat b]) ->
  CF POST (ix_cut C_A817c8_at [Z.of_nat b]) -> CF POST (ix_cut C_A817ec_at [Z.of_nat b]) -> CF POST (ix_cut C_A81680_at [Z.of_nat b]).
Proof.
  intros POST b X4c4 X708 X768 X7c8 X7ec.
  destruct b as [|[|[|[|[|[|[|b]]]]]]].
  - exact (r10_b0 POST X768).
  - exact (r10_b12 POST 1 (or_introl eq_refl) X7ec).
  - exact (r10_b12 POST 2 (or_intror eq_refl) X7ec).
  - exact (r10_b34 POST 3 (or_introl eq_refl) X4c4).
  - exact (r10_b34 POST 4 (or_intror eq_refl) X4c4).
  - exact (r10_b56 POST 5 (or_introl eq_refl) X708 X7c8).
  - exact (r10_b56 POST 6 (or_intror eq_refl) X708 X7c8).
  - apply r10_b7. lia.
Qed.

End GlueR10.
