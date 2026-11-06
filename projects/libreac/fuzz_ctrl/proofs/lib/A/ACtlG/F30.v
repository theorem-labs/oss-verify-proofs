(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1114 of its 1252 lines of code are new or changed and 873 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F34.v, with its module paths and module names changed; 702 of its 781 lines of code are new or changed and 1173 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F34.v, with its module paths and module names changed; 768 of its 850 lines of code are new or changed and 699 lines of the source are left out. *)
(* lib/A/ACtlG/F30.v -- GLUE for stage seg_F30 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   `Hypothesis seg_F30`, :836 (at head; :648 at a working branch 524d38bbd10, ACtl.v blob 84ef756918c)).  Written by
   a Theorem Labs lane, one writer.  Pattern: glue-pattern.md (a working note, not in this delivery)
   (G1-G5; section 4 for a run that writes memory; section 8, last bullet: a cgif-form callee walk is cited in its
   caller-journal form at its entry).  rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F30 : forall POST (j : nat),
       CF POST (ix_cut C_A82798_at [Z.of_nat j]) -> CF POST (ix_cut C_A8275c_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F30.  ENTRY cut C_A8275c_at (pc 0x8275c, ACtlCutP.v:2710-2720), EXIT cut C_A82798_at (pc 0x82798,
   ACtlCutP.v:2724-2739).  Segment F30 (Seg/F30.v): six shadow stores and the event cell (0x8275c-0x82790), the call
   `jal reac_ctrl_classify_box_frame` at 0x82794, return to 0x82798 = the exit cut.

   THE RUNS (a Theorem Labs lane's _F line, on the glue base):
     A.Prog.Seg.F30F.f30_stores_F     (Seg/F30F.v:65-94)  0x8275c -> 0x82794, writes [S(fr)+56, S(fr)+67) and
                                                          [fr+528, fr+532), sets a0..a4;
     A.Prog.Seg.F30Fs.f30_evt_call_pre_Fs (Seg/F30Fs.v:210-219)  the jal: 0x82794 -> 0x831b8 with ra = 0x82798,
                                                          premise-free (the narrowed split of F30.F30Call.f30_evt_call);
   both lifted at RNG := ProgBridge.RNG_W (w_H W3), the first with YA0nR.SRr_fevt_hid, the second with SRr_fevt.
   THE CALLEE: reac_ctrl_classify_box_frame (0x831b8) through a Theorem Labs lane's cgif-form spec
   A.Prog.C_reac_ctrl_classify_box_frame.treac_ctrl_classify_box_frame_spec (blob 16b46ddf65a), applied at its entry
   with STK := LLVMF_STK, sp0 := c_sp cx, FP := [], own := own6 cx, f := phi, n := flen cx j, u := fr + 2624,
   o := fr + 448, v := fr + 528, fr := SM.t_g (c_in cx) j, us := SM.OUR (c_in cx) (SlotModel.v:181, :205 are the same
   classify / ctrlparse applications).  Its post returns to ra = 0x82798, the exit cut, so no post-run is lifted.

   THE PROOF (glue-pattern.md G1-G5)
   G1  the entry cut at index [Z.of_nat j] (C_A8275c_at's body).
   G2  the stores' premises from FRAC / FLSI / PRO / FLS (shadow and frame cells, the spills [A+160], [A+168],
       [A+208]), ctl_rt_C's cut_shadow region (disjunct (F): the owned class-6 frame's shadow), and the rng premises by
       visibility (the AR frames law, the journal's window).
   G3  ProgBridge.cfg_at_MS, the walk moved to the run's canonical map (YA0nR.SRr_xregs_eqv).
   G4  the two lifts; the journal moved across the stores (YCbq.ajournal_exec, written bytes are the owned frame's)
       and across the jal (no write); then the callee spec's premises C1-C22 (the caller review sent to a Theorem Labs lane,
       classify-spec-review.md (a working note, not in this delivery)) and YA0n.SRr_bind into its post.
   G5  the exit cut at ly2 S2 W2 regs2 mem2 md2 of the post: journal Q2 (EV_CLS = 0), frames and live list Q3,
       callee-saved registers Q3, a0 Q4, the 36 bytes at fr+448 Q5, the event cell Q6, every other byte by Q7's
       kept classes read at visible addresses, block shadow from the post's AR (al_shadow), frame bytes and shadow
       present by the post's AR (al_frames), ctl_rt_C by a Theorem Labs lane's PROVED A.ProgWorldCtlRtC.ctl_rt_C_of_AR at the post's AR
       (route (C)).  The bundles move by
       ACtlG/F29.v's transfer relation ktr: stores (ktr_of_munch) then callee (ktr_of_eq below), composed.

   SECTION HYPOTHESES (exact text below)
   - RELRO_IMG, LAWS: ACtl.v's own (ACtl.v:192, :210 at 8ee48574229), same text, same order.
   - CLS : treac_ctrl_classify_box_frame_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI.  Owner a Theorem Labs lane.  PROVED as
     pb_reac_ctrl_classify_box_frame (lib/A/Prog/reac_ctrl_classify_box_frame_glue.v, Qed at
     a working branch 77e96750edc) under its own Section hypotheses RELRO_IMG, LAWS, TPARSE (a Theorem Labs lane's
     treac_ctrl_parse_spec) and RT_AR (at that branch; TSYMS here); discharged where the walk is composed (ACtl.v's owner a Theorem Labs lane).
   - TFIB_SYMS : A.AF0m.CtrlTSyms B, ACtl.v's own hypothesis (Section Ctl, ACtl.v:225 at 8ee48574229), same text
     and the same place in the order; it is ctl_rt_C_of_AR's first premise.
   - route (C) (L3 recipe, a Theorem Labs lane): VIS0 / OWNED_RO (A.ProgWorld.AR_states_vis0_shadow / AR_states_owned_ro) are
     GONE.  The exit cut's ctl_rt_C is a Theorem Labs lane's PROVED A.ProgWorldCtlRtC.ctl_rt_C_of_AR (lib/A/ProgWorldCtlRtC.v:37),
     which needs neither; the former Local Notation ctlrt_of_AR is deleted.

   DISCHARGE CALL in ACtl.v (the Section order of glue_seg_F30; measured with `About` on the built .vo, not read off
   the source; XN_LIB is not used and is not an argument):
     exact (glue_seg_F30 B MT XM_LIB RLO RHI RELRO_IMG LAWS TFIB_SYMS CLS)
   (fx / rc stay implicit, resolved by ACtl.v's own Context instances.)

   CLOSURE: every Require names the FULL directory in its From clause, and every lib/Reusable / lib/Lib / lib/Prog
   module this file names is bound by full path in the alias modules below (a Theorem Labs lane 05:28Z).  The closure is
   ACtlG/F29.v's plus Seg/F30F.v / Seg/F30Fs.v (Seg/F30.v and its frame-route closure), the callee spec file and its
   PA files, A.ProgWorldVisFrame (vis_of_aview only), A.AF0m for TFIB_SYMS, and (route (C)) A.ShadowRwOn /
   A.ACtlRtC / A.ProgWorldCtlRtC for ctl_rt_C and ctl_rt_C_of_AR.  MEASURED (before route (C)) with
   closure_scan.py sha256
   039e7d56edc33b08e7d2b05bc9c3d98593c711ff8ef313a5f33ca4d1f7592c8f (16 rule-3 self-test cases on every run):
   see closure-F30-*.txt (a working note, not in this delivery) for the file count and the line
   `closure-rule-3 files: NONE` -- no lib/AZ/AsanW, no W6 file, no cut-free file (SegCF, _cfw, Cf_<word>).

   THE RUNS USED: only F30F.f30_stores_F and the premise-free F30Fs.f30_evt_call_pre_Fs; no `_post_F` / `_post_Fs` is
   consumed (the callee returns straight to the exit cut), so a Theorem Labs lane's spec meets the call with its own post.

   BUILD STATE: 'type-check on 5da74c9c931, closure reaches no stand-in'.  Built on the stand-in-free glue
   base a working branch 121bf608343 (a Theorem Labs lane's 29ddfc3ea99: interim core 5da74c9c931 + Batch3 + a Theorem Labs lane's
   ProgWorld files) by `cb build` of a fresh clone (packed BASE 23b918fe0c2e, a build machine, no port_core_refused
   substitution), the target's .vo and .glob deleted before the launch; logs (internal path)
   and their .prov (compile line, .vo mtime, make's failure list).  Batch3's FRAC trailer
   word at the exit cut comes through ACtlG/F29.v's kt_frac: ktr's frame-byte clause, kept across the stores
   (ktr_of_munch) and across the callee (KF: the callee keeps every byte of the owned class-6 frame outside its write
   set).  Print Assumptions glue_seg_F30: Rocq primitives (PrimInt63 / PrimString / PrimArray) and
   FunctionalExtensionality.functional_extensionality_dep, nothing else.  No Axiom, no Parameter, no Admitted,
   no admit.  This file has NO bare use of the doubled name Z_to_bv_bv_unsigned (measured by grep). *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI04 YM05 YO09 YI16 YK0s YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04 YA0n YA0nR YG0f YG00 YG01 YG0d YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0v YC5d YCbq APostBase YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k ACfn Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlK ACtlCut ACtlCutP ProgBridge ProgWorldVisFrame.
(* A.AF0m carries ACtl.v's TFIB_SYMS type (A.AF0m.CtrlTSyms), ctl_rt_C_of_AR's first premise.  route (C): the narrowed
   cut conjunct ctl_rt_C (A.ACtlRtC over A.ShadowRwOn) and its producer from AR, A.ProgWorldCtlRtC.ctl_rt_C_of_AR (no
   VIS0 / OWNED_RO). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame Cells Step PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcClassify RcClassifyLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel C_reac_ctrl_classify_box_frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F29 F30 F30F F30Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit F29.
Import ListNotations.
Local Open Scope Z_scope.

(* The lib/Reusable, lib/Lib and lib/Prog modules this file names, bound by full path. *)
Module Reusable.
  Module YK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
  Module YA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
  Module YA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
  Module YG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
  Module YG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
  Module YG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
  Module YG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
  Module YG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
  Module YG0v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v.
  Module YC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
  Module YCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
  Module APostBase := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
  Module YE01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE01.
  Module YI04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
  Module YP09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
  Module YK0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.
End Reusable.
Module Lib.
  Module ExecF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
  Module MState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
  Module Regs6ss := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
  Module Mem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
  Module Frame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
  Module Cells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
  Module Step := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
  Module PropExec := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
End Lib.
Module Prog.
  Module RcParse := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
  Module RcClassify := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcClassify.
  Module RcClassifyLib := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcClassifyLib.
End Prog.
Module CLSM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_classify_box_frame.
Module G29 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.F29.

Local Notation segs := A.AB1v.tfibsegs.
Local Notation getrC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr.
Local Notation fpR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs.
Local Notation fpC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr.
Local Notation romC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom.
Local Notation romA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom.
Local Notation reg_get := LinuxProcessSemantics.Riscv.Sem.reg_get.

(* ---------------------------------------------------------------------------------------------------------
   1. The core's view (aview, range_addressable) and lib/Lib's reads (mrd, bytes_at, addressable) at visible bytes. *)

Lemma av_mrd : forall (H : word -> bool) (m : word -> option byte) (a : Z),
  H (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs H m a =
  option_map (fun b : byte => bv_unsigned b) (Lib.Mem.mrd segs m (Lib.Mem.wa a)).
Proof.
  intros H m a Hv. unfold Reusable.YG0n.aview, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict, Lib.Mem.mrd, Lib.Mem.wa.
  rewrite Hv. destruct (m (Z_to_bv 64 a)); reflexivity.
Qed.

Lemma mrd_of_av : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  H (Z_to_bv 64 a) = false -> H' (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs H' m' a = Reusable.YG0n.aview segs H m a ->
  Lib.Mem.mrd segs m' (Lib.Mem.wa a) = Lib.Mem.mrd segs m (Lib.Mem.wa a).
Proof.
  intros H H' m m' a Hv Hv' E. rewrite (av_mrd H' m' a Hv'), (av_mrd H m a Hv) in E.
  destruct (Lib.Mem.mrd segs m' (Lib.Mem.wa a)) as [b'|], (Lib.Mem.mrd segs m (Lib.Mem.wa a)) as [b|];
    cbn in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma av_of_mrd : forall (H : word -> bool) (m : word -> option byte) (a : Z) (b : byte),
  H (Z_to_bv 64 a) = false -> Lib.Mem.mrd segs m (Lib.Mem.wa a) = Some b ->
  Reusable.YG0n.aview segs H m a = Some (bv_unsigned b).
Proof. intros H m a b Hv Hb. rewrite (av_mrd H m a Hv), Hb. reflexivity. Qed.

Lemma mrd_of_av_some : forall (H : word -> bool) (m : word -> option byte) (a z : Z),
  H (Z_to_bv 64 a) = false -> Reusable.YG0n.aview segs H m a = Some z ->
  exists b : byte, Lib.Mem.mrd segs m (Lib.Mem.wa a) = Some b /\ bv_unsigned b = z.
Proof.
  intros H m a z Hv E. rewrite (av_mrd H m a Hv) in E.
  destruct (Lib.Mem.mrd segs m (Lib.Mem.wa a)) as [b|]; cbn in E; [|discriminate E].
  injection E as E. exists b. split; [reflexivity | exact E].
Qed.

Lemma ba_nth : forall (m : word -> option byte) (a : Z) (bs : list byte) (i : nat),
  Lib.Mem.bytes_at segs m a bs -> (i < length bs)%nat ->
  Lib.Mem.mrd segs m (Lib.Mem.wa (a + Z.of_nat i)) = nth_error bs i.
Proof. intros m a bs i (_ & _ & Hb) Hi. exact (Hb i Hi). Qed.

Lemma av_of_bytes : forall (H : word -> bool) (m : word -> option byte) (a : Z) (bs : list byte) (i : nat),
  Lib.Mem.bytes_at segs m a bs -> (i < length bs)%nat -> H (Z_to_bv 64 (a + Z.of_nat i)) = false ->
  Reusable.YG0n.aview segs H m (a + Z.of_nat i) = Some (bv_unsigned (nth i bs (Z_to_bv 8 0))).
Proof.
  intros H m a bs i Hb Hi Hv. apply (av_of_mrd H m _ _ Hv). rewrite (ba_nth m a bs i Hb Hi).
  apply nth_error_nth'. exact Hi.
Qed.

Lemma bytes_of_av : forall (H : word -> bool) (m : word -> option byte) (a : Z) (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat -> H (Z_to_bv 64 (a + Z.of_nat i)) = false /\
     Reusable.YG0n.aview segs H m (a + Z.of_nat i) = Some (bv_unsigned (nth i bs (Z_to_bv 8 0)))) ->
  Lib.Mem.bytes_at segs m a bs.
Proof.
  intros H m a bs H0 H1 Hi. split; [exact H0|]. split; [exact H1|]. intros i Hlt.
  destruct (Hi i Hlt) as (Hv & Ha). destruct (mrd_of_av_some H m _ _ Hv Ha) as (b & Hb & Hu).
  assert (E : nth_error bs i = Some (nth i bs (Z_to_bv 8 0))) by (apply nth_error_nth'; exact Hlt).
  rewrite Hb, E. f_equal. apply bv_eq. exact Hu.
Qed.

Lemma bytes_eq : forall (m m' : word -> option byte) (a : Z) (bs : list byte),
  Lib.Mem.bytes_at segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) ->
     Lib.Mem.mrd segs m' (Lib.Mem.wa x) = Lib.Mem.mrd segs m (Lib.Mem.wa x)) ->
  Lib.Mem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & Hb) He. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  exact (eq_trans (He (a + Z.of_nat i) ltac:(lia)) (Hb i Hi)).
Qed.

(* A shadow byte read as a small signed value is its unsigned value. *)
Lemma sgn_small : forall b : byte, 0 <= bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma sgn_nonneg : forall b : byte, 0 <= bv_signed b -> bv_signed b = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range _ b) as Hr. unfold bv_modulus in Hr. cbn in Hr.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn.
  intros Hs. Z.div_mod_to_equations. lia.
Qed.

Lemma soa_eq : forall x, Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x = A.AsanRT.shadow_addr x.
Proof.
  intros x. unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
  lia.
Qed.

(* The core's range_addressable read through a world's view is lib/Lib's addressable. *)
Lemma addr_of_ra : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (p n : Z),
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) Reusable.YG0f.SHADOW_OFF p n ->
  0 <= p -> 0 <= n -> p + n <= A.AsanRT.APPMEM_END ->
  (forall i, 0 <= i < n -> A.AsanRT.app_mem (p + i)) ->
  A.AsanRT.addressable m p n.
Proof.
  intros W m p n HR H0 H1 H2 Happ. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. split; [exact (Happ i Hi)|].
  destruct (HR (p + i) ltac:(lia)) as (s & Hs & Hok). rewrite soa_eq in Hs.
  assert (Hv : Reusable.YA0n.w_H W (Z_to_bv 64 (A.AsanRT.shadow_addr (p + i))) = false).
  { apply (A.ProgWorldVisFrame.vis_of_aview segs W m). rewrite Hs. discriminate. }
  destruct (mrd_of_av_some _ m _ s Hv Hs) as (b & Hb & Hu). exists b. split; [exact Hb|].
  unfold Reusable.YG0v.saddr_ok in Hok. pose proof (bv_unsigned_in_range _ b) as Hr.
  rewrite (sgn_small b) by lia. unfold A.AsanRT.shadow_ok. lia.
Qed.

Lemma ra_of_addr : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (p n : Z),
  A.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (A.AsanRT.shadow_addr (p + i))) = false) ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) Reusable.YG0f.SHADOW_OFF p n.
Proof.
  intros W m p n (H0 & H1 & H2 & Ha) Hv x Hx.
  destruct (Ha (x - p) ltac:(lia)) as (_ & b & Hb & Hok).
  pose proof (Hv (x - p) ltac:(lia)) as Hvx.
  replace (p + (x - p)) with x in Hb, Hok, Hvx by lia.
  exists (bv_unsigned b). split.
  - rewrite soa_eq. exact (av_of_mrd _ m _ b Hvx Hb).
  - unfold Reusable.YG0v.saddr_ok. unfold A.AsanRT.shadow_ok in Hok.
    destruct Hok as [E | (E1 & E2)].
    + left. rewrite <- (sgn_nonneg b) by lia. exact E.
    + right. rewrite <- (sgn_nonneg b) by lia. lia.
Qed.

(* addressable when every shadow byte of the range reads the same. *)
Lemma addr_eq : forall (m m' : word -> option byte) (p n : Z),
  A.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n -> Lib.Mem.mrd segs m' (Lib.Mem.wa (A.AsanRT.shadow_addr (p + i))) =
                           Lib.Mem.mrd segs m (Lib.Mem.wa (A.AsanRT.shadow_addr (p + i)))) ->
  A.AsanRT.addressable m' p n.
Proof.
  intros m m' p n (H0 & H1 & H2 & Ha) He. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (Ha i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|].
  exists b. split; [exact (eq_trans (He i Hi) Hb) | exact Hok].
Qed.

(* A spill [Ab + off] read through register 9 = Ab is the q64 at Ab + off. *)
Lemma spill_q64 : forall (regs : bvmap 5 word) (m : word -> option byte) (Ab off v : Z),
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 Ab -> 416 <= Ab -> Ab + 416 <= 2 ^ 64 -> 0 <= off <= 400 ->
  ACtlCutP.q64 m (Ab + off) v.
Proof.
  intros regs m Ab off v (A1 & HA1 & Hq) R9 H1 H2 Ho.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite Lib.Mem.length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
  assert (EA : A1 = Ab) by exact (A.Prog.Seg.F29.rg_near regs 9 Ab A1 R9 HA1 H1 H2 ltac:(lia) ltac:(lia)).
  subst A1. exact Hq.
Qed.

Lemma ro_of_q64 : forall (m : word -> option byte) (a v : Z),
  ACtlCutP.q64 m a v -> Lib.Step.ro_cells segs m a [Lib.Cells.C8 (Z_to_bv 64 v)].
Proof.
  intros m a v H. unfold Lib.Step.ro_cells, Lib.Cells.cells_at. split; [cbn; tauto|].
  cbn [Lib.Cells.cells_bytes Lib.Cells.cbytes]. rewrite app_nil_r. exact H.
Qed.

(* The classify event cell: the core's val_mem of a small value at visible bytes is lib/Lib's u32. *)
Lemma u32_of_val : forall (H : word -> bool) (m : word -> option byte) (a e : Z),
  0 <= e <= 5 -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  (forall k, 0 <= k < 4 -> H (Z_to_bv 64 (a + k)) = false) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.val_mem segs (Reusable.YK04.mrestrict H m) a 4 e ->
  ACtlCutP.u32 m a e.
Proof.
  intros H m a e He H0 H1 Hv HV. unfold ACtlCutP.u32. split; [exact H0|].
  split; [rewrite Lib.Mem.length_le4; cbn; lia|].
  intros i Hi. rewrite Lib.Mem.length_le4 in Hi.
  pose proof (HV i Hi) as Hb.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict in Hb.
  rewrite (Hv (Z.of_nat i)) in Hb by lia.
  unfold Lib.Mem.mrd, Lib.Mem.wa.
  destruct (m (Z_to_bv 64 (a + Z.of_nat i))) as [b|] eqn:Em;
    (eapply eq_trans; [exact Hb|]); clear - He Hi;
    (assert (Hc : e = 0 \/ e = 1 \/ e = 2 \/ e = 3 \/ e = 4 \/ e = 5) by lia);
    destruct i as [|[|[|[|i]]]]; try lia;
    destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
Qed.

(* A byte in no segment: the writable view is the memory itself. *)
Lemma wview_noseg : forall (m : word -> option byte) (x : word),
  find_segment A.Img0.rsegs (bv_unsigned x) 1 = None -> wview A.Img0.rsegs m x = m x.
Proof. intros m x Hn. unfold wview. destruct (m x); [reflexivity|]. rewrite Hn. reflexivity. Qed.

(* A live frame's byte is no image byte (the core's AR_client_img_law, YG0d.v:490-495). *)
Lemma frame_noimg : forall {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
    {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
    (B : Reusable.YG0f.asyms), Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : Reusable.YA0n.world segs) mem md cid pos a,
  Reusable.YG0n.AR segs B ly S W mem md -> In (cid, pos) (Reusable.YG01.frames S) ->
  Reusable.YG0f.frame_addr ly cid pos <= a < Reusable.YG0f.frame_addr ly cid pos + Reusable.YG00.fs_frame_bytes cid ->
  ~ Reusable.YG0d.in_img segs a.
Proof.
  intros fx rc B LAWS ly S W mem md cid pos a HAR Hin Ha.
  exact (proj2 (Reusable.YG0d.al_client_img _ _ LAWS ly S W mem md a HAR
                  (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Ha))))))).
Qed.

(* The read-only image view moves along a journal with no fake-stack-pointer list (fp_spares [] holds outright). *)
Lemma aro_journal : forall {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
    {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
    (B : Reusable.YG0f.asyms) (rlo rhi : Z) STK sp0 ly S W mem md own ly' S' W' mem' md' k,
  (forall a, rlo <= a < rhi -> Reusable.YG0d.in_img segs a) ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  Reusable.YE01.arodata_okS segs B rlo rhi (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) ->
  Reusable.YE01.arodata_okS segs B rlo rhi (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W') mem').
Proof.
  intros fx rc B rlo rhi STK sp0 ly S W mem md own ly' S' W' mem' md' k Himg HJ HR a Hro Ho He.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He |
                   exact (Reusable.YCbq.fp_spares_closed [] a Reusable.YCbq.sink_closed_nil)].
  destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (Himg a Hr)].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. ACtlG/F29.v's transfer relation ktr from per-byte read equalities (the callee step). *)
Lemma ktr_of_eq : forall (fr Ab : Z) (cx : ACtlCut.ctlcx) (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  ACtlCut.rgv regs 9 Ab -> getrC regs' 9 = getrC regs 9 -> 416 <= Ab -> Ab + 416 <= ACtlCut.c_sp cx ->
  ACtlCut.c_sp cx <= 2 ^ 64 ->
  (forall x, (fr <= x < fr + 4096 /\ ~ (fr + 448 <= x < fr + 536)) \/ (Ab <= x < ACtlCut.c_sp cx) ->
     Lib.Mem.mrd segs m' (Lib.Mem.wa x) = Lib.Mem.mrd segs m (Lib.Mem.wa x)) ->
  (forall y, fr <= y < fr + 4096 ->
     Lib.Mem.mrd segs m' (Lib.Mem.wa (A.AsanRT.shadow_addr y)) =
     Lib.Mem.mrd segs m (Lib.Mem.wa (A.AsanRT.shadow_addr y))) ->
  (Lib.Mem.bytes_at segs m (ACtlCut.c_p cx) (ACtlCut.c_in cx) ->
     Lib.Mem.bytes_at segs m' (ACtlCut.c_p cx) (ACtlCut.c_in cx)) ->
  (A.AsanRT.addressable m (ACtlCut.c_p cx) (ACtlCut.c_n cx) ->
     A.AsanRT.addressable m' (ACtlCut.c_p cx) (ACtlCut.c_n cx)) ->
  (Lib.Frame.stk segs m fr (fr + 3136) -> Lib.Frame.stk segs m' fr (fr + 3136)) ->
  G29.ktr fr Ab cx regs regs' m m'.
Proof.
  intros fr Ab cx regs regs' m m' R9 E9 HA0 HAc Hc64 KB KS KI KA KT.
  split.
  { intros a bs H Hx. apply (bytes_eq m m' a bs H). intros x Hr. apply KB. exact (Hx x Hr). }
  split.
  { intros p n H Hy. apply (addr_eq m m' p n H). intros i Hi. apply KS.
    destruct (Hy (p + i) ltac:(lia)) as (Hf & _). exact Hf. }
  split.
  { intros off v Ho Hs. exists Ab. split; [exact (eq_trans E9 R9)|].
    pose proof (spill_q64 regs m Ab off v Hs R9 HA0 ltac:(lia) Ho) as Hq.
    unfold ACtlCutP.q64 in *. apply (bytes_eq m m' _ _ Hq). intros x Hx. rewrite Lib.Mem.length_le8 in Hx.
    change (Z.of_nat 8) with 8 in Hx. apply KB. right. lia. }
  split; [exact KI|]. split; [exact KA | exact KT].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   3. The stage. *)
Section GlueF30.

(* ACtl.v's Section shape (ACtl.v:172-185), restricted to what this stage uses, then this stage's two named
   hypotheses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:189, :193-194), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A8275c_at := (ACtlCutP.C_A8275c_at B).
Local Notation C_A82798_at := (ACtlCutP.C_A82798_at B).

(* ACtl.v:181 and :185, verbatim. *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
(* ACtl.v's own TFIB_SYMS (Section Ctl, ACtl.v:193), ctl_rt_C_of_AR's first premise; same text, same place in the
   order. *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
(* The callee's cgif-form spec (a Theorem Labs lane; proved as pb_reac_ctrl_classify_box_frame at 77e96750edc). *)
Hypothesis CLS : CLSM.treac_ctrl_classify_box_frame_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI.
(* route (C): VIS0 / OWNED_RO and the Local Notation ctlrt_of_AR are GONE: the exit cut's ctl_rt_C comes from a Theorem Labs lane's
   PROVED A.ProgWorldCtlRtC.ctl_rt_C_of_AR (lib/A/ProgWorldCtlRtC.v:37), which needs neither. *)

Lemma glue_seg_F30 : forall POST (j : nat),
  CF POST (ix_cut C_A82798_at [Z.of_nat j]) -> CF POST (ix_cut C_A8275c_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 Hbase HJ HF HL Hkmax Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A8275c_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & Hperm & HFRAC & Hcn & Hj & HHB & HFLSI & HLK & HFLS & HLT).
  (* G2: the entry context, the frame, the blocks, the spill base *)
  pose proof Hbase as ((Hafn & _ & _ & _ & Hpn & Hlen & _ & _ & _ & _ & Hros & _) & _).
  pose proof Hafn as (_ & _ & _ & Hgp & _).
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & Hwin3 & Hastk & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  pose proof Hastk as (_ & _ & Hstklo & Hstkhi & _).
  pose proof Reusable.YCbq.asan_consts as (Hceil & _).
  unfold A.ACfn.LLVMF_STK in Hstkhi, Hwin3.
  assert (HF6 : Reusable.YG01.frames S3 = [(6, ACtlCut.c_fpos cx)]) by exact HF.
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF6; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; rewrite EF; reflexivity).
  assert (E4096 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & Hfapp & Hfby & Hfsh).
  rewrite Efr3, E4096 in Hfapp, Hfby, Hfsh. change (4096 / 8) with 512 in Hfsh.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Hfapp.
  assert (HFAPP : forall y, fr <= y < fr + 4096 -> A.AsanRT.app_mem y).
  { intros y Hy. unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
    destruct Hfapp as (H1 & [H2 | (H2 & H3)]); [left | right]; lia. }
  pose proof HFRAC as (Ab & sp & _ & Hsp16 & HspZ & R4 & _ & R9 & R3 & R19 & _ & Hfr32 & _ & HAc & HspA & HfrA &
    HA416 & Hspc & HcAPP & _ & _ & _ & _ & _ & (sh & Hsh & Hshl) & _).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (Hfr0 : 0 <= fr) by (destruct Hfapp; lia).
  assert (Hcsp : A.AsanRT.HIGHMEM_BEG + 4096 <= ACtlCut.c_sp cx) by (unfold A.AsanRT.HIGHMEM_BEG; lia).
  assert (HAHI : A.AsanRT.HIGHMEM_BEG <= Ab) by (unfold A.AsanRT.HIGHMEM_BEG in *; lia).
  assert (HcAPP' : ACtlCut.c_sp cx <= A.AsanRT.APPMEM_END) by lia.
  assert (HAFR : fr + 536 <= Ab) by lia.
  assert (HAb64 : 0 <= Ab < 2 ^ 64) by (unfold A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *; lia).
  assert (Hc64 : ACtlCut.c_sp cx <= 2 ^ 64) by (unfold A.AsanRT.APPMEM_END in *; lia).
  (* the turn's block phi: live, apart from the frame, its size *)
  assert (Hinphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hinphi)
    as (_ & Hph4096 & Hphceil & _ & Hphpres & _ & Hnb).
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi _ 6 (ACtlCut.c_fpos cx) HAR Hinphi
                Hin6) as Hdphi.
  rewrite Efr3, E4096 in Hdphi. unfold Reusable.YG0f.zdisjoint in Hdphi. cbn [fst snd] in Hdphi.
  pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx j) ltac:(unfold Reusable.YG00.MALLOC_MAX in Hnb; lia))
    as Hreqphi.
  pose proof HHB as (Hphi0 & HphA).
  pose proof (A.AsanRTFacts.addressable_app _ _ _ HphA) as HphApp.
  assert (Hasz : A.ACtlK.a_size (ACtlCutP.flen cx j) = Reusable.YG00.req_size (ACtlCutP.flen cx j)).
  { unfold A.ACtlK.a_size, Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  assert (HPH : forall y, phi <= y < phi + A.ACtlK.a_size (ACtlCutP.flen cx j) ->
            A.AsanRT.app_mem y /\ ~ (fr <= y < fr + 4096)).
  { intros y Hy. split; [apply HphApp; lia|]. rewrite Hasz in Hy. lia. }
  (* the input block: live at entry, still live (FP = []), apart from the frame *)
  pose proof HFLSI as (HFLSH & _ & _ & _ & (HinA & HinB) & _).
  pose proof HFLSH as (HPRO & _ & Hstk & _ & _).
  pose proof HPRO as (_ & _ & _ & H160 & H168 & _ & H208 & _ & Had2624 & _ & _ & _).
  pose proof (A.AsanRTFacts.addressable_app _ _ _ HinA) as HinApp.
  assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (intros x0 y0; decide equality; apply Z.eq_dec).
  assert (Hinp3 : 0 < ACtlCut.c_n cx -> In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
  { intros Hn0. destruct Hpn as [(Hn00 & _) | (_ & Hinp)]; [lia|].
    destruct (in_dec Hdec (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)) as [Hi|Hni];
      [exact Hi|].
    exfalso. apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.inFP_nil (ACtlCut.c_p cx + 0)).
    apply (Hgone _ _ 0 Hinp Hni). unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
  assert (HCP : forall y, ACtlCut.c_p cx <= y < ACtlCut.c_p cx + ACtlCut.c_n cx ->
            A.AsanRT.app_mem y /\ ~ (fr <= y < fr + 4096)).
  { intros y Hy. split; [apply HinApp; lia|].
    pose proof (Hinp3 ltac:(lia)) as Hi3.
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx) HAR Hi3 Hin6)
      as Hdin.
    rewrite Efr3, E4096 in Hdin. unfold Reusable.YG0f.zdisjoint in Hdin. cbn [fst snd] in Hdin.
    unfold Reusable.YG00.req_size in Hdin. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
  assert (HLEN : Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx) by (symmetry; exact Hlen).
  (* the frame's shadow *)
  set (Sh := ACtlCutP.Sfr fr) in *.
  assert (ESh : Sh = A.AsanRT.shadow_addr fr) by reflexivity.
  assert (HshA : forall i, 0 <= i < 512 -> Sh + i = A.AsanRT.shadow_addr (fr + 8 * i)).
  { intros i Hi. rewrite ESh. rewrite A.Prog.Seg.F29.sh_frame_of by lia. reflexivity. }
  assert (HinSh : forall i, 0 <= i < 512 -> A.AsanRT.in_shadow (Sh + i)).
  { intros i Hi. rewrite (HshA i Hi). apply A.AsanRTFacts.shadow_of_app. apply HFAPP. lia. }
  assert (HSlo : A.AsanRT.LOWMEM_END <= Sh).
  { pose proof (HinSh 0 ltac:(lia)) as H0. unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END,
      A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG in *. lia. }
  unfold A.AsanRT.LOWMEM_END in HSlo.
  (* the frame's shadow lies apart from the frame and below high memory (the frame is low or high memory) *)
  pose proof (@Reusable.YG0f.ASAN_CEIL_range rc) as (HCE & _). unfold Reusable.YG0f.ASAN_CEIL in HCE.
  assert (HShr : (Sh + 512 <= fr \/ fr + 4096 <= Sh) /\ Sh + 512 <= A.AsanRT.HIGHMEM_BEG).
  { clear - Hfapp HCE ESh. rewrite ESh. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, A.AsanRT.HIGHMEM_BEG.
    Z.div_mod_to_equations. lia. }
  assert (Hshvis3 : forall i, 0 <= i < 512 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 (Sh + i)) = false).
  { intros i Hi. destruct (Hfsh i Hi) as ((Hv & _) & _). rewrite G29.f29_sa_eq, <- ESh in Hv. exact Hv. }
  assert (Hfrvis3 : forall a, fr <= a < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha. destruct (Hfby a Ha) as ((Hv & _) & _). exact Hv. }
  assert (Hwvis3 : forall a, ACtlCut.c_sp cx - 32768 <= a < ACtlCut.c_sp cx ->
            Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha. destruct (Hwin3 a Ha) as (Hv & _). exact Hv. }
  assert (Hphvis3 : forall a, phi <= a < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) ->
            Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha. destruct (Hphpres a Ha) as ((Hv & _) & _). exact Hv. }
  (* G2: the stores' premises *)
  assert (Hshl' : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  destruct Hrt as (Hac & Hcut & Himg & Hro).
  (* route (C): every shadow byte of the owned class-6 frame is in cut_shadow's (F) disjunct *)
  assert (HcutSh : forall i, 0 <= i < 512 -> A.ACtlRtC.cut_shadow B ly3 S3 (Sh + i)).
  { intros i Hi. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
    rewrite Efr3, E4096, ESh. change (4096 / 8) with 512.
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
    Z.div_mod_to_equations; lia. }
  pose proof (A.Prog.Seg.F29.ba_sub mem3 Sh sh 56 11 Hsh ltac:(lia)) as Hsh11.
  change (Z.of_nat 56) with 56 in Hsh11.
  assert (HRWs : Lib.Step.rw_cells A.Img0.rsegs mem3 (Sh + 56) [Lib.Cells.CB 11 (firstn 11 (skipn 56 sh))]).
  { split; [split|].
    - cbn [Lib.Cells.cells_wf Lib.Cells.cell_wf]. split; [rewrite length_firstn, length_skipn; lia | exact I].
    - cbn [Lib.Cells.cells_bytes Lib.Cells.cbytes]. rewrite app_nil_r. exact Hsh11.
    - cbn [Lib.Cells.cells_size Lib.Cells.csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi.
      replace (Sh + 56 + i) with (Sh + (56 + i)) by lia.
      exact (proj1 (Hcut _ (HcutSh (56 + i) ltac:(lia)) (HinSh (56 + i) ltac:(lia)))). }
  destruct (A.Prog.Seg.F30.rw_of_stk mem3 fr (fr + 3136) (fr + 448) 36 Hstk ltac:(lia) ltac:(lia) ltac:(lia))
    as (junk & HRWo).
  destruct (A.Prog.Seg.F30.rw_of_stk mem3 fr (fr + 3136) (fr + 528) 4 Hstk ltac:(lia) ltac:(lia) ltac:(lia))
    as (vb0 & HRWv).
  assert (HR160 := ro_of_q64 _ _ _ (spill_q64 regs3 mem3 Ab 160 (fr + 528) H160 R9 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (HR168 := ro_of_q64 _ _ _ (spill_q64 regs3 mem3 Ab 168 (fr + 2624) H168 R9 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (HR208 := ro_of_q64 _ _ _ (spill_q64 regs3 mem3 Ab 208 (fr + 448) H208 R9 ltac:(lia) ltac:(lia) ltac:(lia))).
  set (RNGW := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (Rs56 : Lib.ExecF.rng RNGW (Sh + 56) 11).
  { apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    replace a with (Sh + (a - Sh)) by lia. apply Hshvis3. lia. }
  assert (Rv : Lib.ExecF.rng RNGW (fr + 528) 4).
  { apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha. apply Hfrvis3. lia. }
  assert (Rwin : forall off, 0 <= off <= 400 -> Lib.ExecF.rng RNGW (Ab + off) 8).
  { intros off Ho. apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    apply Hwvis3. lia. }
  pose proof HFLS as (_ & H18 & _ & H23 & _).
  (* G3: the cut's configuration in the run's state form, the walk moved to the run's canonical map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A8275c_at [Z.of_nat j])) with 0x8275c.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 fpR (Z_to_bv 64 0x8275c) fpC None
           mem3 (romC segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the stores, lifted *)
  pose proof (A.Prog.Seg.F30F.f30_stores_F RNGW
    (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6)
    (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11)
    (reg_get regs3 12) (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16)
    (reg_get regs3 17) (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21)
    (reg_get regs3 22) (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25) (reg_get regs3 26)
    (reg_get regs3 27) (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)
    fpR fpC mem3 Sh Ab fr phi (ACtlCutP.flen cx j) (firstn 11 (skipn 56 sh)) junk vb0
    R19 R9 H23 H18 HRWs HRWo HRWv HR160 HR168 HR208
    ltac:(lia) ltac:(lia) ltac:(lia) Hfr0 ltac:(lia) ltac:(lia)
    Rs56 Rv (Rwin 160 ltac:(lia)) (Rwin 168 ltac:(lia)) (Rwin 208 ltac:(lia))) as HRUN.
  change (romA A.Img0.rsegs) with (romC A.Img0.rsegs) in HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 RNGW _ (POST cx) HFS).
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' HP Hhid Hsbm.
  destruct HP as (m' & mid & Ems & MU & WM & Hshc & Hoc & Hvc). subst ms'.
  change (forall x : word, Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) in Hhid.
  (* G4: the jal, lifted *)
  pose proof (A.Prog.Seg.F30Fs.f30_evt_call_pre_Fs RNGW
    (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6)
    (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) (Z_to_bv 64 phi) (Z_to_bv 64 (ACtlCutP.flen cx j))
    (Z_to_bv 64 (fr + 2624)) (Z_to_bv 64 (fr + 448)) (Z_to_bv 64 (fr + 528)) (reg_get regs3 15)
    (reg_get regs3 16) (reg_get regs3 17) (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20)
    (reg_get regs3 21) (reg_get regs3 22) (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25)
    (reg_get regs3 26) (reg_get regs3 27) (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30)
    (reg_get regs3 31) fpR fpC m') as HRUN2.
  change (romA A.Img0.rsegs) with (romC A.Img0.rsegs) in HRUN2.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN2) as HFS2.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS2.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md' RNGW _ (POST cx) HFS2).
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  intros ms'' md'' Ems2 Hsbm2. subst ms''.
  match goal with |- context [?C ?R _ (Z_to_bv 64 0x831b8) _ _ _ _] => set (regsC := R) end.
  (* the callee-entry register map *)
  assert (C1r : getrC regsC 1 = Z_to_bv 64 0x82798) by reflexivity.
  assert (C2r : getrC regsC 2 = getrC regs3 2) by reflexivity.
  assert (C3r : getrC regsC 3 = getrC regs3 3) by reflexivity.
  assert (C4r : getrC regsC 4 = getrC regs3 4) by reflexivity.
  assert (C9r : getrC regsC 9 = getrC regs3 9) by reflexivity.
  assert (Esp : Reusable.YG0d.spZ regsC = sp) by exact HspZ.
  (* what the stores wrote *)
  destruct Hshc as ((Hshwf & Hshb) & _).
  cbn [Lib.Cells.cells_wf Lib.Cells.cell_wf] in Hshwf.
  destruct Hshwf as (_ & _ & _ & _ & _ & Hmidl & _).
  cbn [Lib.Cells.cells_bytes Lib.Cells.cbytes app] in Hshb.
  assert (SHk : forall kk, 0 <= kk < 5 ->
            Lib.Mem.mrd segs m' (Lib.Mem.wa (Sh + 56 + kk)) =
            Some (Z_to_bv 8 (if kk <? 4 then 0 else 4))).
  { intros kk Hkk. assert (Hc : kk = 0 \/ kk = 1 \/ kk = 2 \/ kk = 3 \/ kk = 4) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | ->]]]].
    - exact (ba_nth m' (Sh + 56) _ 0 Hshb ltac:(cbn; lia)).
    - exact (ba_nth m' (Sh + 56) _ 1 Hshb ltac:(cbn; lia)).
    - exact (ba_nth m' (Sh + 56) _ 2 Hshb ltac:(cbn; lia)).
    - exact (ba_nth m' (Sh + 56) _ 3 Hshb ltac:(cbn; lia)).
    - exact (ba_nth m' (Sh + 56) _ 4 Hshb ltac:(cbn; lia)). }
  assert (SH10 : Lib.Mem.mrd segs m' (Lib.Mem.wa (Sh + 66)) = Some (Z_to_bv 8 4)).
  { pose proof (ba_nth m' (Sh + 56) _ 10 Hshb ltac:(cbn; rewrite length_app, Hmidl; cbn; lia)) as H10.
    change (Z.of_nat 10) with 10 in H10. replace (Sh + 56 + 10) with (Sh + 66) in H10 by lia.
    rewrite H10. change (nth_error (mid ++ [Z_to_bv 8 4]) 5 = Some (Z_to_bv 8 4)).
    rewrite nth_error_app2 by lia. rewrite Hmidl. reflexivity. }
  assert (Hnew : forall x, (Sh + 56 <= x < Sh + 67 \/ fr + 528 <= x < fr + 532) ->
            exists b, Lib.Mem.mrd segs m' (Lib.Mem.wa x) = Some b).
  { intros x [Hx | Hx].
    - replace x with (Sh + 56 + (x - (Sh + 56))) by lia.
      apply (A.Prog.Seg.F29.ba_some m' (Sh + 56) _ (x - (Sh + 56)) Hshb).
      cbn [length]. rewrite length_app, Hmidl. cbn. lia.
    - destruct Hvc as ((_ & Hvb) & _). cbn [Lib.Cells.cells_bytes Lib.Cells.cbytes] in Hvb.
      rewrite app_nil_r in Hvb.
      replace x with (fr + 528 + (x - (fr + 528))) by lia.
      apply (A.Prog.Seg.F29.ba_some m' (fr + 528) _ (x - (fr + 528)) Hvb).
      rewrite Lib.Mem.length_le4. cbn. lia. }
  assert (FS : G29.f_safe fr [(Sh + 56, Sh + 67); (fr + 528, fr + 532)]).
  { split.
    - intros x Hx Hnw. cbn [Lib.Frame.outside]. split; [|split; [lia | exact I]]. intros Hin.
      apply (A.AsanRTFacts.app_not_shadow x Hx).
      replace x with (Sh + (x - Sh)) by lia. apply HinSh. lia.
    - intros y Hy Hny. cbn [Lib.Frame.outside]. split; [|split; [|exact I]].
      + intros Hin. apply Hny.
        pose proof (A.Prog.Seg.F29.sh_frame fr y (A.AsanRT.shadow_addr y - Sh) Hfr0 Hfr8 ltac:(lia)
                      ltac:(rewrite <- ESh; lia)) as Hz.
        lia.
      + assert (Hsy : A.AsanRT.shadow_addr y < fr \/ fr + 4096 <= A.AsanRT.shadow_addr y).
        { clear - Hy Hfapp HCE. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, A.AsanRT.APPMEM_END in *.
          Z.div_mod_to_equations. lia. }
        lia. }
  (* the journal across the stores and the jal *)
  assert (HJc : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => Sh + 56 <= a < Sh + 67 \/ fr + 528 <= a < fr + 532).
    - exact HJ.
    - intros x Hx. unfold Reusable.YK04.mrestrict. destruct (Reusable.YA0n.w_H W3 x); [reflexivity|].
      apply MU. cbn [Lib.Frame.outside]. split; [|split; [|exact I]]; intros Hin; apply Hx; [left | right]; exact Hin.
    - intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
      assert (Hwd : (Sh + 56 <= bv_unsigned x < Sh + 67 \/ fr + 528 <= bv_unsigned x < fr + 532) \/
                    (~ (Sh + 56 <= bv_unsigned x < Sh + 67) /\ ~ (fr + 528 <= bv_unsigned x < fr + 532))) by lia.
      destruct Hwd as [Hw | (Hn1 & Hn2)].
      + assert (Hns : find_segment A.Img0.rsegs (bv_unsigned x) 1 = None).
        { destruct Hw as [Hw | Hw]; [apply G29.f29_seg_none; lia|].
          apply (Reusable.YCbq.find_segment_none segs).
          apply (frame_noimg B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) _ HAR Hin6).
          rewrite Efr3, E4096. lia. }
        rewrite <- (wview_noseg m' x Hns). apply WM. intros E. apply Hx.
        rewrite <- (wview_noseg mem3 x Hns). exact E.
      + rewrite MU; [exact Hx|]. cbn [Lib.Frame.outside]. split; [exact Hn1 | split; [exact Hn2 | exact I]].
    - exact Hhid.
    - exact Hsbm.
    - intros a [Ha | Ha]; unfold Reusable.YCbq.awr_byte, Reusable.YCbq.in_frames; right; right; right;
        exists 6, (ACtlCut.c_fpos cx); (split; [left; reflexivity|]);
        rewrite Efr3, E4096; unfold Reusable.YG0n.in_zr; cbn [fst snd].
      + right. rewrite G29.f29_sa_eq, <- ESh. change (4096 / 8) with 512. lia.
      + left. lia. }
  assert (HJc2 : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                   (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                   (ACtlCut.own6 cx) ly3 S3 W3 m' md'' k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ => False).
    - exact HJc.
    - intros x _. reflexivity.
    - intros x Hx. exact Hx.
    - intros x _. reflexivity.
    - exact Hsbm2.
    - intros a []. }
  (* the stores' transfer (ACtlG/F29.v's ktr), mem3 -> m' *)
  assert (HE : G29.kenv [(Sh + 56, Sh + 67); (fr + 528, fr + 532)] fr mem3 m' cx regs3 regsC Ab).
  { split; [exact MU|]. split; [exact FS|]. split; [exact HFAPP|]. split; [exact HCP|].
    split; [exact HLEN|]. split; [exact R9|]. split; [exact C9r|]. split; [exact HAHI|].
    split; [exact HA416|]. split; [exact HcAPP' | exact HAFR]. }
  assert (HNW : forall x, fr + 448 <= x < fr + 536 ->
            Lib.Frame.outside [(Sh + 56, Sh + 67); (fr + 528, fr + 532)] x \/
            exists b, Lib.Mem.mrd segs m' (Lib.Mem.wa x) = Some b).
  { intros x Hx. destruct (Z_lt_ge_dec x (fr + 528)) as [H1|H1];
      [|destruct (Z_lt_ge_dec x (fr + 532)) as [H2|H2]].
    - left. cbn [Lib.Frame.outside]. split; [|split; [lia | exact I]]. intros Hin.
      apply (A.AsanRTFacts.app_not_shadow x (HFAPP x ltac:(lia))).
      replace x with (Sh + (x - Sh)) by lia. apply HinSh. lia.
    - right. apply Hnew. right. lia.
    - left. cbn [Lib.Frame.outside]. split; [|split; [lia | exact I]]. intros Hin.
      apply (A.AsanRTFacts.app_not_shadow x (HFAPP x ltac:(lia))).
      replace x with (Sh + (x - Sh)) by lia. apply HinSh. lia. }
  pose proof (G29.ktr_of_munch _ _ _ _ _ _ _ _ HE WM HNW) as T1.
  (* G4: the callee's premises at its entry (regsC, m', W3, md'') *)
  assert (Hu8 : (fr + 2624) mod 8 = 0) by (clear - Hfr8; Z.div_mod_to_equations; lia).
  assert (Hsh_idx : forall x, fr <= x -> A.AsanRT.shadow_addr x = Sh + (x - fr) / 8).
  { intros x Hx.
    pose proof (A.Prog.Seg.F29.sh_off fr (x - fr) ((x - fr) / 8) Hfr0 Hfr8 ltac:(Z.div_mod_to_equations; lia)) as E.
    replace (fr + (x - fr)) with x in E by lia. rewrite ESh. exact E. }
  assert (C11 : 50 <= ACtlCutP.flen cx j -> forall i, (i < 50)%nat ->
            Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m' (phi + Z.of_nat i) =
            Some (Prog.RcParse.cp_v (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) i)).
  { intros H50 i Hi. pose proof HFLS as (_ & _ & _ & _ & _ & _ & Hrec & _).
    destruct (Hrec H50) as (_ & _ & Hg & _).
    assert (Hg' : Lib.Mem.bytes_at segs m' phi (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)).
    { apply (G29.k_bytes _ fr mem3 m' MU FS _ _ Hg). rewrite A.Prog.Seg.F29.t_g_length. intros x Hx.
      change (Z.of_nat 50) with 50 in Hx. destruct (HPH x ltac:(rewrite Hasz; lia)) as (Ha & Hn).
      split; [exact Ha | lia]. }
    exact (av_of_bytes _ m' phi _ i Hg' ltac:(rewrite A.Prog.Seg.F29.t_g_length; exact Hi)
             (Hphvis3 (phi + Z.of_nat i) ltac:(lia))). }
  assert (C18 : 50 <= ACtlCutP.flen cx j -> forall i, (i < 6)%nat ->
            Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m' (fr + 2624 + Z.of_nat i) =
            Some (Prog.RcParse.cp_v (A.Prog.SlotModel.OUR (ACtlCut.c_in cx)) i)).
  { intros _ i Hi. pose proof HLK as (_ & _ & HOUR). unfold ACtlCutP.OURb in HOUR.
    assert (HOUR' : Lib.Mem.bytes_at segs m' (fr + 2624) (A.Prog.SlotModel.OUR (ACtlCut.c_in cx))).
    { apply (G29.k_bytes _ fr mem3 m' MU FS _ _ HOUR). rewrite A.Prog.SlotModel.OUR_length. intros x Hx.
      change (Z.of_nat 6) with 6 in Hx. split; [apply HFAPP; lia | lia]. }
    exact (av_of_bytes _ m' _ _ i HOUR' ltac:(rewrite A.Prog.SlotModel.OUR_length; exact Hi)
             (Hfrvis3 (fr + 2624 + Z.of_nat i) ltac:(lia))). }
  assert (C12 : Reusable.APostBase.afobj segs B ly3 S3 W3 m' (fr + 448) 36).
  { split; [exists 6, (ACtlCut.c_fpos cx); rewrite Efr3, E4096; split; [exact Hin6|];
            split; [lia|]; split; [clear - Hfr32; Z.div_mod_to_equations; lia | lia]|].
    split; [clear - Hfr8; Z.div_mod_to_equations; lia|].
    intros x Hx. rewrite soa_eq, (Hsh_idx x ltac:(lia)).
    assert (Hk : 56 <= (x - fr) / 8 <= 60) by (Z.div_mod_to_equations; lia).
    assert (Hm8 : x mod 8 = (x - fr) mod 8) by (clear - Hfr8; Z.div_mod_to_equations; lia).
    pose proof (SHk ((x - fr) / 8 - 56) ltac:(lia)) as Hb.
    replace (Sh + 56 + ((x - fr) / 8 - 56)) with (Sh + (x - fr) / 8) in Hb by lia.
    exists (bv_unsigned (Z_to_bv 8 (if (x - fr) / 8 - 56 <? 4 then 0 else 4))). split.
    - apply (av_of_mrd _ m' _ _ (Hshvis3 ((x - fr) / 8) ltac:(lia)) Hb).
    - unfold Reusable.YG0v.saddr_ok. destruct (Z.ltb_spec ((x - fr) / 8 - 56) 4) as [Hl|Hl].
      + left. reflexivity.
      + right. change (bv_unsigned (Z_to_bv 8 4)) with 4. rewrite Hm8.
        assert (Hx4 : (x - fr) / 8 = 60) by lia. Z.div_mod_to_equations. lia. }
  assert (C14 : Reusable.APostBase.afobj segs B ly3 S3 W3 m' (fr + 528) 4).
  { split; [exists 6, (ACtlCut.c_fpos cx); rewrite Efr3, E4096; split; [exact Hin6|];
            split; [lia|]; split; [clear - Hfr32; Z.div_mod_to_equations; lia | lia]|].
    split; [clear - Hfr8; Z.div_mod_to_equations; lia|].
    intros x Hx. rewrite soa_eq, (Hsh_idx x ltac:(lia)).
    assert (Hk : (x - fr) / 8 = 66) by (Z.div_mod_to_equations; lia).
    assert (Hm8 : x mod 8 = (x - fr) mod 8) by (clear - Hfr8; Z.div_mod_to_equations; lia).
    rewrite Hk. exists 4. split.
    - exact (av_of_mrd _ m' _ _ (Hshvis3 66 ltac:(lia)) SH10).
    - unfold Reusable.YG0v.saddr_ok. right. rewrite Hm8. Z.div_mod_to_equations. lia. }
  assert (C17 : 50 <= ACtlCutP.flen cx j -> Reusable.APostBase.afobj segs B ly3 S3 W3 m' (fr + 2624) 6).
  { intros _. split; [exists 6, (ACtlCut.c_fpos cx); rewrite Efr3, E4096; split; [exact Hin6|];
            split; [lia|]; split; [clear - Hfr32; Z.div_mod_to_equations; lia | lia]|].
    split; [exact Hu8|].
    apply ra_of_addr.
    - apply (G29.k_addr _ fr mem3 m' MU FS _ _ Had2624). intros y Hy. lia.
    - intros i Hi. rewrite (Hsh_idx (fr + 2624 + i) ltac:(lia)). apply Hshvis3. Z.div_mod_to_equations. lia. }
  assert (C13 : forall a, fr + 448 <= a < fr + 448 + 36 ->
            Reusable.YCbq.awr_byte A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
              (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
              (ACtlCut.own6 cx) a).
  { intros a Ha. unfold Reusable.YCbq.awr_byte, Reusable.YCbq.in_frames. right. right. right.
    exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. left.
    rewrite Efr3, E4096. unfold Reusable.YG0n.in_zr. cbn [fst snd]. lia. }
  assert (C15 : forall a, fr + 528 <= a < fr + 528 + 4 ->
            Reusable.YCbq.awr_byte A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
              (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
              (ACtlCut.own6 cx) a).
  { intros a Ha. unfold Reusable.YCbq.awr_byte, Reusable.YCbq.in_frames. right. right. right.
    exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. left.
    rewrite Efr3, E4096. unfold Reusable.YG0n.in_zr. cbn [fst snd]. lia. }
  assert (C2 : Reusable.YE01.arodata_okS segs B RLO RHI
                 (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m')).
  { exact (aro_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJc2 Hros). }
  assert (Hra : bv_unsigned (Z_to_bv 64 0x82798) = 0x82798) by exact (Lib.Mem.wa_unsigned 0x82798 ltac:(lia)).
  assert (C3 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.ret_ok (getrC regsC 1)).
  { change (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.ret_ok (Z_to_bv 64 0x82798)).
    apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.ret_ok_even. rewrite Hra. reflexivity. }
  assert (C3b : 4096 <= Reusable.YG0d.raZ regsC).
  { assert (E : Reusable.YG0d.raZ regsC = 0x82798) by exact Hra. lia. }
  assert (C9 : 50 <= ACtlCutP.flen cx j -> exists Lf, In (phi, Lf) (Reusable.YG0d.ablocks B ly3 S3) /\
                                                     50 <= Reusable.YG00.req_size Lf).
  { intros H50. exists (ACtlCutP.flen cx j). split; [exact Hinphi | lia]. }
  pose proof (CLS A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
    (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 W3 m' md'' k regsC
    phi (ACtlCutP.flen cx j) (fr + 2624) (fr + 448) (fr + 528)
    (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) (A.Prog.SlotModel.OUR (ACtlCut.c_in cx))
    HJc2 C2 C3 C3b
    (eq_trans C3r (eq_trans R3 Hgp)) (eq_trans C4r R4)
    eq_refl eq_refl eq_refl eq_refl eq_refl
    ltac:(unfold Reusable.YG00.MALLOC_MAX in Hnb; lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite Esp; exact Hsp16)
    ltac:(rewrite Esp; unfold CLSM.REAC_CTRL_CLASSIFY_BOX_FRAME_STK, A.ACfn.LLVMF_STK; lia)
    ltac:(rewrite Esp; lia)
    ltac:(rewrite HF6; reflexivity)
    C9
    (A.Prog.Seg.F29.t_g_length _ _) C11 C12 C13 C14 C15 (A.Prog.SlotModel.OUR_length _) C17 C18
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HCLS.
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs CLSM.A_reac_ctrl_classify_box_frameP regsC m' md'') (POST cx)).
  apply (Reusable.YA0n.SRr_bind segs W3 _ _ _ HCLS).
  intros W2 c2 Hle HQ.
  destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & HPR & HFR2 & HBL2 & HQ4 & HQ5 & HQ6 & HQ7).
  subst c2.
  (* G5: the post state *)
  unfold CLSM.EV_CLS in HJ2. rewrite Z.add_0_r in HJ2.
  pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin2 & _).
  pose proof Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
  unfold A.ACfn.LLVMF_STK in Hwin2.
  assert (Efr2 : Reusable.YG0f.frame_addr ly2 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; rewrite EF2; reflexivity).
  assert (Hin62 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S2)) by (rewrite HFR2; exact Hin6).
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly2 S2 W2 mem2 md2 6 (ACtlCut.c_fpos cx) HAR2 Hin62)
    as (_ & _ & Hfby2 & Hfsh2).
  rewrite Efr2, E4096 in Hfby2, Hfsh2. change (4096 / 8) with 512 in Hfsh2.
  assert (Hshvis2 : forall i, 0 <= i < 512 -> Reusable.YA0n.w_H W2 (Z_to_bv 64 (Sh + i)) = false).
  { intros i Hi. destruct (Hfsh2 i Hi) as ((Hv & _) & _). rewrite G29.f29_sa_eq, <- ESh in Hv. exact Hv. }
  assert (Hfrvis2 : forall a, fr <= a < fr + 4096 -> Reusable.YA0n.w_H W2 (Z_to_bv 64 a) = false).
  { intros a Ha. destruct (Hfby2 a Ha) as ((Hv & _) & _). exact Hv. }
  assert (Hwvis2 : forall a, ACtlCut.c_sp cx - 32768 <= a < ACtlCut.c_sp cx ->
            Reusable.YA0n.w_H W2 (Z_to_bv 64 a) = false).
  { intros a Ha. destruct (Hwin2 a Ha) as (Hv & _). exact Hv. }
  assert (Hinphi2 : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly2 S2)) by (rewrite HBL2; exact Hinphi).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 phi _ HAR2 Hinphi2)
    as (_ & _ & _ & _ & Hphpres2 & _).
  assert (Hphvis2 : forall a, phi <= a < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) ->
            Reusable.YA0n.w_H W2 (Z_to_bv 64 a) = false).
  { intros a Ha. destruct (Hphpres2 a Ha) as ((Hv & _) & _). exact Hv. }
  destruct HQ7 as (K1 & K2 & _ & K4 & _ & _).
  assert (HnE : forall a, ~ (fr + 448 <= a < fr + 536) ->
            ~ (fr + 448 <= a < fr + 448 + 36 \/
               (Prog.RcClassify.classify (ACtlCutP.flen cx j) (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)
                  (A.Prog.SlotModel.OUR (ACtlCut.c_in cx)) <> None /\ fr + 528 <= a < fr + 528 + 4))).
  { intros a Ha [H1 | (_ & H1)]; lia. }
  (* the callee step's read equalities, m' -> mem2 *)
  assert (KF : forall x, fr <= x < fr + 4096 -> ~ (fr + 448 <= x < fr + 536) ->
            Lib.Mem.mrd segs mem2 (Lib.Mem.wa x) = Lib.Mem.mrd segs m' (Lib.Mem.wa x)).
  { intros x Hx Hnx. apply (mrd_of_av _ _ _ _ _ (Hfrvis3 x Hx) (Hfrvis2 x Hx)).
    apply (K4 6 (ACtlCut.c_fpos cx) x Hin6); [|exact (HnE x Hnx)].
    left. unfold Reusable.YCbq.frame_rng, Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, E4096. lia. }
  assert (KS : forall y, fr <= y < fr + 4096 ->
            Lib.Mem.mrd segs mem2 (Lib.Mem.wa (A.AsanRT.shadow_addr y)) =
            Lib.Mem.mrd segs m' (Lib.Mem.wa (A.AsanRT.shadow_addr y))).
  { intros y Hy. rewrite (Hsh_idx y ltac:(lia)).
    assert (Hk : 0 <= (y - fr) / 8 < 512) by (Z.div_mod_to_equations; lia).
    apply (mrd_of_av _ _ _ _ _ (Hshvis3 _ Hk) (Hshvis2 _ Hk)).
    apply (K4 6 (ACtlCut.c_fpos cx) _ Hin6).
    - right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, E4096, G29.f29_sa_eq, <- ESh.
      change (4096 / 8) with 512. lia.
    - intros [H1 | (_ & H1)]; lia. }
  assert (KW : forall x, Ab <= x < ACtlCut.c_sp cx ->
            Lib.Mem.mrd segs mem2 (Lib.Mem.wa x) = Lib.Mem.mrd segs m' (Lib.Mem.wa x)).
  { intros x Hx. apply (mrd_of_av _ _ _ _ _ (Hwvis3 x ltac:(lia)) (Hwvis2 x ltac:(lia))).
    apply K1; [lia | | intros [H1 | (_ & H1)]; lia].
    rewrite Esp. unfold CLSM.REAC_CTRL_CLASSIFY_BOX_FRAME_STK. lia. }
  assert (KBL : forall p n x, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) -> p <= x < p + Reusable.YG00.req_size n ->
            ~ (fr <= x < fr + 4096) ->
            Lib.Mem.mrd segs mem2 (Lib.Mem.wa x) = Lib.Mem.mrd segs m' (Lib.Mem.wa x)).
  { intros p n x Hin Hx Hnf.
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR Hin) as (_ & _ & _ & _ & Hpr3 & _).
    assert (Hin2 : In (p, n) (Reusable.YG0d.ablocks B ly2 S2)) by (rewrite HBL2; exact Hin).
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 Hin2) as (_ & _ & _ & _ & Hpr2 & _).
    destruct (Hpr3 x Hx) as ((Hv3 & _) & _). destruct (Hpr2 x Hx) as ((Hv2 & _) & _).
    apply (mrd_of_av _ _ _ _ _ Hv3 Hv2).
    replace x with (p + (x - p)) by lia. apply (K2 p n (x - p) Hin); [lia|].
    replace (p + (x - p)) with x by lia. intros [H1 | (_ & H1)]; lia. }
  (* the callee's transfer m' -> mem2 *)
  assert (G2 : getrC regs2 2 = getrC regs3 2)
    by exact (HPR 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (G3 : getrC regs2 3 = getrC regs3 3)
    by exact (HPR 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (G4 : getrC regs2 4 = getrC regs3 4)
    by exact (HPR 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (G8 : getrC regs2 8 = getrC regs3 8)
    by exact (HPR 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (G9 : getrC regs2 9 = getrC regs3 9)
    by exact (HPR 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (G18 : getrC regs2 18 = getrC regs3 18)
    by exact (HPR 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (G19 : getrC regs2 19 = getrC regs3 19)
    by exact (HPR 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (G21 : getrC regs2 21 = getrC regs3 21)
    by exact (HPR 21 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (G22 : getrC regs2 22 = getrC regs3 22)
    by exact (HPR 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (G23 : getrC regs2 23 = getrC regs3 23)
    by exact (HPR 23 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (G24 : getrC regs2 24 = getrC regs3 24)
    by exact (HPR 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (G25 : getrC regs2 25 = getrC regs3 25)
    by exact (HPR 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (G26 : getrC regs2 26 = getrC regs3 26)
    by exact (HPR 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (T2 : G29.ktr fr Ab cx regsC regs2 m' mem2).
  { apply ktr_of_eq.
    - exact R9.
    - exact (eq_trans G9 (eq_sym C9r)).
    - lia.
    - exact HA416.
    - exact Hc64.
    - intros x [(Hx & Hnx) | Hx]; [exact (KF x Hx Hnx) | exact (KW x Hx)].
    - exact KS.
    - intros Hb. apply (bytes_eq m' mem2 _ _ Hb). intros x Hx. rewrite HLEN in Hx.
      apply (KBL (ACtlCut.c_p cx) (ACtlCut.c_n cx) x (Hinp3 ltac:(lia))).
      + pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)). lia.
      + destruct (HCP x Hx) as (_ & Hn). exact Hn.
    - intros Ha. destruct (Z.eq_dec (ACtlCut.c_n cx) 0) as [E0 | Hn0].
      + apply (addr_eq m' mem2 _ _ Ha). intros i Hi. lia.
      + pose proof Ha as (Ha0 & Ha1 & Ha2 & _).
        pose proof (Hinp3 ltac:(lia)) as Hi3. assert (Hi2 : In (ACtlCut.c_p cx, ACtlCut.c_n cx)
                                                       (Reusable.YG0d.ablocks B ly2 S2)) by (rewrite HBL2; exact Hi3).
        apply (addr_of_ra W2 mem2); [| exact Ha0 | exact Ha1 | exact Ha2 |].
        * apply (Reusable.YCbq.range_addressable_of_block segs B LAWS ly2 S2 W2 mem2 md2 _ _ _ _ HAR2 Hi2);
            [lia | pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)); lia].
        * intros i Hi. apply HinApp. lia.
    - intros _. split; [lia|]. split; [lia|]. intros a Ha.
      destruct (Hfby2 a ltac:(lia)) as ((_ & b & Hb) & _).
      unfold Lib.Mem.mrd, Lib.Mem.wa. rewrite Hb. split; [|exists b; reflexivity].
      unfold wview. rewrite Hb. discriminate. }
  pose proof (G29.ktr_trans fr Ab cx regs3 regsC regs2 mem3 m' mem2 T1 T2) as HT.
  (* the exit cut *)
  change (Reusable.YA0n.SRr segs W2
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82798_at [Z.of_nat j])) regs2 mem2 md2) (POST cx)).
  apply (HX cx [Z.of_nat j] fr k ly2 S2 W2 regs2 mem2 md2 Hbase).
  - (* the journal: Q2 at k + EV_CLS = k *)
    exact HJ2.
  - (* frames: Q3 *)
    rewrite HFR2. exact HF.
  - exact HL.
  - exact Hkmax.
  - (* the exit body, C_A82798_at (ACtlCutP.v:2724-2739), at the same index *)
    split; [reflexivity|].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82798_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    exists phi.
    split; [rewrite HBL2; exact Hperm|].
    split.
    { apply (G29.kt_frac fr Ab cx regs3 regs2 mem3 mem2 HT B fr R9 HAb64 G2 G3 G4 G8 G9 G19 G26); [|exact HFRAC].
      assert (Hpres : forall i, (i < 392)%nat ->
                exists b, Lib.Mem.mrd A.Img0.rsegs mem2 (Lib.Mem.wa (Sh + Z.of_nat i)) = Some b).
      { intros i Hi. destruct (Hfsh2 (Z.of_nat i) ltac:(lia)) as ((_ & b & Hb) & _).
        rewrite G29.f29_sa_eq, <- ESh in Hb. exists b. unfold Lib.Mem.mrd, Lib.Mem.wa. rewrite Hb. reflexivity. }
      destruct (A.Prog.Seg.F29.ba_present mem2 392 Sh ltac:(lia) ltac:(lia) Hpres) as (sh' & Hb' & Hl').
      exists sh'. split; [exact Hb' | rewrite Hl'; reflexivity]. }
    split; [exact Hcn|]. split; [exact Hj|].
    split.
    { split; [exact Hphi0|]. pose proof HphA as (Hp0 & Hp1 & Hp2 & _). rewrite Hasz in *.
      apply (addr_of_ra W2 mem2); [| exact Hp0 | exact Hp1 | exact Hp2 |].
      - apply (Reusable.YCbq.range_addressable_of_block segs B LAWS ly2 S2 W2 mem2 md2 _ _ _ _ HAR2 Hinphi2); lia.
      - intros i Hi. apply HphApp. lia. }
    split; [exact (G29.kt_flsi fr Ab cx regs3 regs2 mem3 mem2 HT j HFLSI)|].
    split; [exact (G29.kt_lk fr Ab cx regs3 regs2 mem3 mem2 HT j G21 HLK)|].
    split.
    { apply (G29.kt_fls fr Ab cx regs3 regs2 mem3 mem2 HT j phi G18 G22 G23 G24 G25); [|exact HFLS].
      intros bs Hbs Hb.
      assert (Hb' : Lib.Mem.bytes_at segs m' phi bs).
      { apply (G29.k_bytes _ fr mem3 m' MU FS _ _ Hb). intros x Hx.
        destruct (HPH x ltac:(rewrite Hasz; lia)) as (Ha & Hn). split; [exact Ha | lia]. }
      apply (bytes_eq m' mem2 _ _ Hb'). intros x Hx.
      apply (KBL phi (ACtlCutP.flen cx j) x Hinphi); [lia|].
      destruct (HPH x ltac:(rewrite Hasz; lia)) as (_ & Hn). exact Hn. }
    split.
    { (* a0: Q4 *) exact HQ4. }
    split.
    { (* the 36 bytes at fr + 448: Q5 *)
      unfold A.Prog.SlotModel.t_B.
      apply (bytes_of_av (Reusable.YA0n.w_H W2) mem2); [lia | rewrite Prog.RcParse.ctrlparse_length; lia|].
      intros i Hi. rewrite Prog.RcParse.ctrlparse_length in Hi.
      split; [apply Hfrvis2; lia | exact (HQ5 i Hi)]. }
    split.
    { (* addressable (fr + 452) 6: the stores' zero shadow bytes, kept *)
      apply (addr_eq m' mem2); [|intros i Hi; apply KS; lia].
      split; [lia|]. split; [lia|]. split; [lia|].
      intros i Hi. split; [apply HFAPP; lia|].
      rewrite (Hsh_idx (fr + 452 + i) ltac:(lia)).
      assert (Hk : (fr + 452 + i - fr) / 8 = 56 \/ (fr + 452 + i - fr) / 8 = 57) by (Z.div_mod_to_equations; lia).
      exists (Z_to_bv 8 0). split; [|left; reflexivity].
      destruct Hk as [Hk | Hk]; rewrite Hk.
      - pose proof (SHk 0 ltac:(lia)) as Hb. rewrite Z.add_0_r in Hb. exact Hb.
      - pose proof (SHk 1 ltac:(lia)) as Hb. replace (Sh + 56 + 1) with (Sh + 57) in Hb by lia. exact Hb. }
    split.
    { (* the event cell: Q6 *)
      intros e He. pose proof (Prog.RcClassifyLib.classify_some _ _ _ _ He) as (_ & _ & _ & _ & _ & He5).
      apply (u32_of_val (Reusable.YA0n.w_H W2) mem2 _ e He5); [lia | lia | |].
      - intros kk Hkk. apply Hfrvis2. lia.
      - exact (HQ6 e He). }
    exact (G29.kt_lt fr Ab cx regs3 regs2 mem3 mem2 HT j HLT).
  - (* ctl_rt_C: a Theorem Labs lane's PROVED ctl_rt_C_of_AR at the post's AR (route (C)), the read-only view kept by the journal *)
    apply (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly2 S2 W2 mem2 md2 HAR2).
    exact (aro_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ2 Hros).
Qed.

End GlueF30.
