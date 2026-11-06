(* ctrl_lay_block (0x855f4) on fuzz_ctrl's ASan build, image A: the caller-journal kept clause (tcj_kept) of the glue's
   final post, composed from the four pieces the glue holds after the box call.  A Theorem Labs lane.
   rule 24: no function proved.

   The chain (memories of C_ctrl_lay_block_glue.v):
     memc --(the class-1 allocator call: acall_kept, window [S - 4512, S), nothing else written)--> mem2
          --(stretch k2: munch [window; class-1 frame head; its shadow; the block])--> mem3
          --(the box call TMB: tcj_kept at sp A, window [A - 4320, A) inside [S - 4512, S), E' in the class-1 frame)-->
     mem4 --(stretches k3 / k4: munch [block; window part; class-1 shadow; frame head; flag byte])--> mem5.
   Every written byte outside the caller's window and the caller's block lies in the class-1 frame (1, pos), its shadow
   or its flag byte.  (1, pos) is not a frame of Sc, so AR's frame separation (al_sep at S2) keeps it apart from every
   frame of Sc; the flag byte is in the fake stack's flag area, below every frame; heap blocks are apart from the fake
   stack (A.ProgWorldBlkApart.ctl_block_apart_fs, proved, a Theorem Labs lane 87fcd8d0b28); shadow bytes of application memory lie in
   [kLowMemEnd, kHighMemBeg), apart from application memory and below the allocation ceiling.
   Imports: C_ctrl_lay_block_glue.v lines 26-71 (the glue Requires this file), plus YG0s for frame_facts. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* The six modules that exist twice (core lib/Reusable/<X> and ctrl's lib/A/Reusable/<X>: YI04 YI16 YK11 YK1b YM05
   YO09; porter a Theorem Labs lane 04:03Z) are Required, never Imported, and every name of theirs is written
   lib.Reusable.<X>.<name>: they are the CORE copies (the cgif world, the PA layer, ProgWorld). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI04 YI16 YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK0h YK0i YK14 YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00 YI0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlBase CtrlRo
CtrlCallerJ C_reac_box_model_block CtrlImg C_ctrl_lay_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import YC85 CtrlFrame.
(* the world-walk kit and the bridges (lemmas only) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04R YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgBridge ProgWorld ProgWorldVisWin ProgWorldVisFrame
  ProgWorldShadow ProgWorld_Fs ProgWorldAstack ProgWorldCtlRt MemNorm MemNormF MemNormTr AF0m.
(* heap blocks are apart from the fake stack (proved, a working branch 87fcd8d0b28) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldBlkApart.
(* the _F closure, QUALIFIED only *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec ExecF MState Mem Frame Step Cells Regs6ss
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_malloc_c ctrl_lay_block_c ctrl_lay_block
  asan_memset_cF asan_memcpy_cF ctrl_lay_block_F_1 ctrl_lay_block_F_3 ctrl_lay_block_F_7 ctrl_lay_block_F_R1
  ctrl_lay_block_F_R2 ctrl_lay_block_F_R3 ctrl_lay_block_F_R4.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth RcLay.
(* frame_facts (YG0s.v:442): a live frame's class, offset and size inside the fake stack *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0s.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Local Notation rget := lib.Reusable.YK11.getr.
Local Notation rmkst := lib.Reusable.YK11.mkst.
(* The walk's segments (C_ctrl_lay_block.v:81); = A.Img0.rsegs by conversion (ProgBridge.tfibsegs_rsegs). *)
#[local] Notation SEGS := AB1v.tfibsegs.

Section kept.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma kept_tlay : TLAY_STK = 4512.
Proof. reflexivity. Qed.

Lemma kept_bmb : REAC_BOX_MODEL_BLOCK_STK = 4320.
Proof. reflexivity. Qed.

Lemma kept_fb1 : fs_frame_bytes 1 = 128.
Proof. reflexivity. Qed.

Lemma kept_ceil : 0x7fff7f800000 <= lib.Reusable.YM05.alloc_ceiling <= 0x7fffff800000.
Proof. pose proof asan_consts as (C & _). exact C. Qed.

(* A view kept across a write set, at an address outside it (lay_acall_kept_after_munch's EQ). *)
Lemma kept_view_munch : forall (H : word -> bool) (m m' : word -> option byte) (WR : list lib.Lib.Frame.ivl) (a : Z),
  lib.Lib.Frame.munch WR m m' -> 0 <= a < 2 ^ 64 -> lib.Lib.Frame.outside WR a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros H m m' WR a HM Ha HO. apply aview_eq_of. unfold mrestrict. rewrite (HM (Z_to_bv 64 a)); [reflexivity|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
  exact HO.
Qed.

(* Presence kept across a write set, at an address outside it. *)
Lemma kept_pres_munch : forall (H : word -> bool) (m m' : word -> option byte) (WR : list lib.Lib.Frame.ivl) (a : Z),
  lib.Lib.Frame.munch WR m m' -> 0 <= a < 2 ^ 64 -> lib.Lib.Frame.outside WR a ->
  apresent H m a -> apresent H m' a.
Proof.
  intros H m m' WR a HM Ha HO [Hh (bb & Hb)]. split; [exact Hh|]. exists bb.
  rewrite (HM (Z_to_bv 64 a)); [exact Hb|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
  exact HO.
Qed.

(* A shadow byte of an 8-aligned range [y, y + n) (n a multiple of 8) is the shadow of an 8-byte granule inside it. *)
Lemma kept_sh_frame : forall y n a, y mod 8 = 0 -> n mod 8 = 0 ->
  in_zr a (lib.Reusable.YG0f.shadow_addr y, n / 8) ->
  y <= 8 * (a - 0x7fff8000) /\ 8 * (a - 0x7fff8000) + 8 <= y + n.
Proof.
  intros y n a Hy Hn Ha.
  unfold in_zr, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in Ha. cbn [fst snd] in Ha.
  clear - Hy Hn Ha. Z.div_mod_to_equations. lia.
Qed.

(* The image lies below IMG_HI (the glue's lay_img_below, same proof). *)
Lemma kept_img_below : forall a, in_img SEGS a -> a < A.Prog.ImgBounds.IMG_HI.
Proof.
  intros a (sg & Hin & Hb). pose proof A.MemNormTr.rsegs_below_img as H.
  unfold A.MemNormTr.seg_ends_below in H. rewrite forallb_forall in H. specialize (H sg Hin).
  apply Z.leb_le in H. lia.
Qed.

Local Ltac kept_out := cbn [lib.Lib.Frame.outside]; repeat split; intro; lia.

Lemma lay_tcj_final : forall lyc Sc S2 (W W4 W3 : world SEGS) memc mem2 mem3 mem4 mem5 mem3' mdc md3' (S A p pos : Z),
  AR SEGS B lyc Sc W memc mdc ->
  (* AR of the call's state S2 at any world / memory: only its frame geometry and separation are read *)
  AR SEGS B lyc S2 W3 mem3' md3' ->
  frames S2 = (1, pos) :: frames Sc -> ~ In (1, pos) (frames Sc) -> ablocks B lyc S2 = ablocks B lyc Sc ->
  lib.Reusable.YM05.alloc_ceiling <= S - 4512 -> S - 144 <= A <= S - 128 -> S < 2 ^ 64 ->
  tfr_hull lyc Sc (p + 18) 32 ->
  acall_kept SEGS B lyc Sc W memc W mem2 (S - 4512) S (fun _ => False) ->
  lib.Lib.Frame.munch [(S - 4512, S); (frame_addr lyc 1 pos, frame_addr lyc 1 pos + 24);
    (frame_addr lyc 1 pos / 8 + A.AsanRT.ASAN_K, frame_addr lyc 1 pos / 8 + A.AsanRT.ASAN_K + 12); (p + 18, p + 50)]
    mem2 mem3 ->
  tcj_kept B REAC_BOX_MODEL_BLOCK_STK lyc S2 W mem3 W4 mem4 A
    (fun a => frame_addr lyc 1 pos + 32 <= a < frame_addr lyc 1 pos + 32 + 32) ->
  lib.Lib.Frame.munch [(p + 18, p + 50); (A - 2224, A);
    (A.AsanRT.shadow_addr (frame_addr lyc 1 pos), A.AsanRT.shadow_addr (frame_addr lyc 1 pos) + 16);
    (frame_addr lyc 1 pos, frame_addr lyc 1 pos + 8); (flag_addr lyc 1 pos, flag_addr lyc 1 pos + 1)] mem4 mem5 ->
  (forall a, S - 4512 <= a < S -> apresent (w_H W4) mem5 a) ->
  tcj_kept B TLAY_STK lyc Sc W memc W4 mem5 S (fun a => p + 18 <= a < p + 50).
Proof.
  intros lyc Sc S2 W W4 W3 memc mem2 mem3 mem4 mem5 mem3' mdc md3' S A p pos
    HARc HAR4 HS2 Hnin Hab Hc HA HS Hhull HK HM1 HT HM2 Hpres.
  pose proof kept_ceil as CE.
  pose proof HARc as (Mc & _). pose proof HAR4 as (M4 & _).
  assert (In1 : In (1, pos) (frames S2)) by (rewrite HS2; left; reflexivity).
  (* the fake stack and the class-1 frame (1, pos) of S2 *)
  destruct (YG0s.frame_facts B lyc S2 _ 1 pos M4 In1) as (_ & _ & FSA & _ & _ & O1 & O2 & _ & _ & _ & FL).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR4 In1) as (M32 & _).
  pose proof (A.ProgWorld_Fs.pw_F_above B lyc S2 W3 mem3' md3' HAR4) as GT.
  unfold asan_stack_malloc_c.ASAN_GT in GT.
  rewrite kept_fb1 in O2.
  unfold kFakeFramesOff, kFakeStackSize in O1, O2.
  unfold kFakeFlagsOff, kFakeFramesOff in FL.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kFakeStackSize in FSA.
  assert (FSC : ly_F lyc + 0xb09000 <= lib.Reusable.YM05.alloc_ceiling) by lia.
  assert (FSZ : ly_F lyc + 0xb09000 <= 0x7fff7000 \/ 0x10007fff8000 <= ly_F lyc) by lia.
  clear FSA.
  assert (EF1 : frame_addr lyc 1 pos = ly_F lyc + fs_frame_off 1 pos) by reflexivity.
  assert (EFL : flag_addr lyc 1 pos = ly_F lyc + fs_flag_off 1 pos) by reflexivity.
  assert (F1b : ly_F lyc + 36864 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= ly_F lyc + 0xb09000)
    by lia.
  assert (FLb : ly_F lyc + 4096 <= flag_addr lyc 1 pos < ly_F lyc + 36864) by lia.
  (* the frames of Sc are apart from (1, pos): al_sep at S2 *)
  destruct (al_sep _ _ LAWS _ _ _ _ _ HAR4) as [Hsep _].
  apply pairwise_app_l in Hsep as [_ Hsep].
  rewrite HS2 in Hsep. cbn [map pairwise fst snd] in Hsep. destruct Hsep as [HF1 _].
  rewrite kept_fb1 in HF1.
  (* the caller's block [p + 18, p + 50) lies in a class >= 2 frame of Sc (tfr_hull), inside the fake stack *)
  assert (EB : ly_F lyc + 36864 <= p + 18 /\ p + 50 <= ly_F lyc + 0xb09000).
  { destruct Hhull as (ce & pe & Ine & Hce & Hh1 & Hh2).
    destruct (YG0s.frame_facts B lyc Sc _ ce pe Mc Ine) as (_ & _ & _ & _ & _ & Oe1 & Oe2 & _ & _ & _ & _).
    assert (EFe : frame_addr lyc ce pe = ly_F lyc + fs_frame_off ce pe) by reflexivity.
    assert (Pe : 0 <= ce * 2 ^ 20) by (apply Z.mul_nonneg_nonneg; lia).
    assert (EH : frame_addr lyc ce pe <= p + 18 /\ p + 50 <= frame_addr lyc ce pe + fs_frame_bytes ce)
      by (clear - Hh1 Hh2; Z.div_mod_to_equations; lia).
    unfold kFakeFramesOff, kFakeStackSize in Oe1, Oe2. lia. }
  clear Hhull.
  (* the class-1 frame's shadow [q1 + K, q1 + K + 16), q1 = frame / 8 *)
  unfold A.AsanRT.shadow_addr in HM2. unfold A.AsanRT.ASAN_K in HM1, HM2.
  assert (Q1 : 8 * (frame_addr lyc 1 pos / 8) = frame_addr lyc 1 pos) by (clear - M32; Z.div_mod_to_equations; lia).
  set (q1 := frame_addr lyc 1 pos / 8) in *. clearbody q1.
  assert (SQ : 0 <= q1 /\ q1 + 0x7fff8000 + 16 <= 0x10007ffe8000) by lia.
  destruct HK as (K1 & K2 & K3 & K4 & K5 & _).
  destruct HT as (T1 & T2 & T3 & T4 & T5 & _).
  rewrite kept_bmb in T1, T5.
  unfold tcj_kept. rewrite kept_tlay. cbv beta.
  split; [|split; [|split; [|split; [|split]]]].
  - (* above the ceiling, outside the window and the block *)
    intros a Ha Hw Hn.
    transitivity (aview SEGS (w_H W4) mem4 a).
    { apply (kept_view_munch _ _ _ _ a HM2); [lia | kept_out]. }
    transitivity (aview SEGS (w_H W) mem3 a).
    { apply (T1 a); [lia | lia | cbv beta; lia]. }
    transitivity (aview SEGS (w_H W) mem2 a).
    { apply (kept_view_munch _ _ _ _ a HM1); [lia | kept_out]. }
    exact (K1 a Ha Hw).
  - (* the heap blocks of Sc *)
    intros b0 m0 i Hin Hi Hn.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b0 m0 HARc Hin) as (_ & Hb0 & Hb1 & Hba & _).
    pose proof (A.ProgWorldBlkApart.ctl_block_apart_fs B LAWS lyc Sc W memc mdc b0 m0 HARc Hin) as Hfs.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hba. unfold kFakeStackSize in Hfs.
    assert (XA : b0 + i < 0x7fff7000 \/ 0x10007fff8000 <= b0 + i) by lia.
    assert (XF : b0 + i < ly_F lyc \/ ly_F lyc + 0xb09000 <= b0 + i) by lia.
    assert (XB : 4096 <= b0 + i < lib.Reusable.YM05.alloc_ceiling) by lia.
    clear Hba Hfs.
    transitivity (aview SEGS (w_H W4) mem4 (b0 + i)).
    { apply (kept_view_munch _ _ _ _ (b0 + i) HM2); [lia | kept_out]. }
    transitivity (aview SEGS (w_H W) mem3 (b0 + i)).
    { apply (T2 b0 m0 i); [rewrite Hab; exact Hin | exact Hi | cbv beta; lia]. }
    transitivity (aview SEGS (w_H W) mem2 (b0 + i)).
    { apply (kept_view_munch _ _ _ _ (b0 + i) HM1); [lia | kept_out]. }
    exact (K2 b0 m0 i Hin Hi (fun H => H)).
  - (* the image *)
    intros a Hi Ho He.
    pose proof (kept_img_below a Hi) as Hb. pose proof (A.ProgWorld.pws_segs_low a Hi) as Hl.
    unfold A.Prog.ImgBounds.IMG_HI in Hb. unfold lib.Reusable.YG0f.kLowMemEnd in Hl.
    transitivity (aview SEGS (w_H W4) mem4 a).
    { apply (kept_view_munch _ _ _ _ a HM2); [lia | kept_out]. }
    transitivity (aview SEGS (w_H W) mem3 a).
    { exact (T3 a Hi Ho He). }
    transitivity (aview SEGS (w_H W) mem2 a).
    { apply (kept_view_munch _ _ _ _ a HM1); [lia | kept_out]. }
    exact (K3 a Hi Ho He).
  - (* the frames of Sc and their shadow *)
    intros c' p' a Hin Hr Hn.
    destruct (YG0s.frame_facts B lyc Sc _ c' p' Mc Hin) as (Cc & _ & _ & _ & _ & P1 & P2 & _ & P4 & P5 & _).
    destruct (al_frames _ _ LAWS _ _ _ _ _ c' p' HARc Hin) as (Y32 & _).
    assert (EY : frame_addr lyc c' p' = ly_F lyc + fs_frame_off c' p') by reflexivity.
    assert (Pc : 0 <= c' * 2 ^ 20) by (apply Z.mul_nonneg_nonneg; lia).
    unfold kFakeFramesOff, kFakeStackSize in P1, P2.
    assert (Yb : ly_F lyc + 36864 <= frame_addr lyc c' p' /\
                 frame_addr lyc c' p' + fs_frame_bytes c' <= ly_F lyc + 0xb09000) by lia.
    assert (Hd : zdisjoint (frame_addr lyc 1 pos, 128) (frame_addr lyc c' p', fs_frame_bytes c')).
    { apply (proj1 (Forall_forall _ _) HF1). apply in_map_iff. exists (c', p'). split; [reflexivity | exact Hin]. }
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    assert (Y8 : frame_addr lyc c' p' mod 8 = 0) by (clear - Y32; Z.div_mod_to_equations; lia).
    assert (N8 : fs_frame_bytes c' mod 8 = 0) by (clear - P5; Z.div_mod_to_equations; lia).
    assert (ZA : (frame_addr lyc c' p' <= a < frame_addr lyc c' p' + fs_frame_bytes c') \/
                 (frame_addr lyc c' p' <= 8 * (a - 0x7fff8000) /\
                  8 * (a - 0x7fff8000) + 8 <= frame_addr lyc c' p' + fs_frame_bytes c')).
    { destruct Hr as [Hr' | Hr'].
      - left. unfold in_zr, frame_rng in Hr'. cbn [fst snd] in Hr'. exact Hr'.
      - right. exact (kept_sh_frame _ _ _ Y8 N8 Hr'). }
    clear Cc P1 P2 P4 P5 Y32 EY Pc Y8 N8.
    transitivity (aview SEGS (w_H W4) mem4 a).
    { apply (kept_view_munch _ _ _ _ a HM2); [lia | kept_out]. }
    transitivity (aview SEGS (w_H W) mem3 a).
    { apply (T4 c' p' a); [rewrite HS2; right; exact Hin | exact Hr | cbv beta; lia]. }
    transitivity (aview SEGS (w_H W) mem2 a).
    { apply (kept_view_munch _ _ _ _ a HM1); [lia | kept_out]. }
    exact (K4 c' p' a Hin Hr (fun H => H)).
  - (* presence above the ceiling outside the window *)
    intros a Ha Hw Hp.
    apply (kept_pres_munch _ _ _ _ a HM2); [lia | kept_out |].
    apply (T5 a); [lia | lia |].
    apply (kept_pres_munch _ _ _ _ a HM1); [lia | kept_out |].
    exact (K5 a Ha Hw Hp).
  - (* the window *)
    exact Hpres.
Qed.
End kept.
