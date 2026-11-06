(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_model_block_glue.v, with its module paths and module names changed; 694 of its 807 lines of code are new or changed and 2299 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/ctrl_lay_block_gctx.v, with its module names changed; 1075 of its 1173 lines of code are new or changed and 709 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/ctrl_lay_block_gR23.v, with its module paths and module names changed; 288 of its 337 lines of code are new or changed and 1124 lines of the source are left out. *)
(* ctrl_lay_block (0x86104) on fuzz_ctrl's ASan+UBSan build, image B (libreac v1.9.0): the call of
   reac_box_model_block at 0x865d8 inside region R2 of the cgif glue pb_ctrl_lay_block (a Theorem Labs lane, hand
   a Theorem Labs lane; consumer a Theorem Labs lane).  rule 24: no function proved here.

   lay_box_arm, with the statement a Theorem Labs lane fixed (lay_R23-statements.v (a working note, not in this delivery), lay_box_arm_stmt): from the call
   state lay_Dbox (ctrl_lay_block_gR23.v) under the call's own premises lay_args, the callee contract TMB
   (C_reac_box_model_block.treac_box_model_block_spec, a Theorem Labs lane) is applied at the call with p := md,
   b := ly_bb (ly_k fr), o := fr1 + 32 (fr1 the call's class-1 frame), and its post gives the box-return descriptor
   lay_D3 (ctrl_lay_block_gD3.v).  Image A's lay_box (written on a working branch, after 9861af6cbb5;
   at head lib/A/Prog/C_ctrl_lay_block_glue.v:1444-1659) is the model; the byte / view / kept helpers are a Theorem Labs lane's
   (ctrl_lay_block_gR23.v Section Data), the shared lemmas gbase's and gctx's.

   CLOSURE: as ctrl_lay_block_gbase.v (the _F files Required QUALIFIED; lib.Reusable twins and B.<module> names in
   full; lib.Reusable.YM05.alloc_ceiling written explicitly). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v YK04R YA0nR YF0m YG0s APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth RcSynthLib RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.AsanRT B.ProgBridge B.ProgWorld B.MemNorm B.MemNormF
  B.MemNormTr.
(* the proved B ProgWorld statements this file reads, by their lemmas (a Theorem Labs lane) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorldShadow B.ProgWorldBlkApart.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec ExecF MState Mem Frame Step Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds asan_stack_malloc_c ctrl_lay_block_c
  ctrl_lay_blockF_on C_ctrl_lay_block C_reac_box_model_block CtrlCallerJ CtrlRo CtrlImg ctrl_lay_block_gbase
  ctrl_lay_block_gD3 ctrl_lay_block_gctx ctrl_lay_block_gR23.
(* image B's PA instance: CtrlCallerJ's shapes over pa_segs PI apply to SEGS by conversion (as
   C_reac_box_model_block.v:55 declares it) *)
#[local] Existing Instance CtrlImg.PI_ctrl_B.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Local Notation getr := lib.Reusable.YK11.getr.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.

(* garr8 over the restricted memory gives the raw bytes (A glue lay_bytes_of_view :500 with lay_garr8_view). *)
Lemma lay_bytes_of_garr8 : forall {fx : lib.Reusable.YK11.FPState} (W : world SEGS) (m : word -> option byte) a
    (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  garr8 SEGS (mrestrict (w_H W) m) a (map (fun x : byte => bv_unsigned x) bs) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs.
Proof.
  intros fx W m a bs H0 H1 G. apply (ctrl_lay_block_gbase.LayLib.bytes_of_view W m a bs H0 H1).
  intros i Hi. destruct (nth_error bs i) as [b|] eqn:E; [| apply nth_error_None in E; lia].
  exists b. split; [reflexivity|].
  rewrite (ctrl_lay_block_gR23.lay_garr8_view (w_H W) m a _ i G ltac:(rewrite length_map; exact Hi)).
  f_equal. rewrite (nth_indep (map _ bs) 0 (bv_unsigned b)) by (rewrite length_map; exact Hi).
  rewrite map_nth. rewrite (nth_error_nth bs i b E). reflexivity.
Qed.

(* reac_box_model_block's result: -1, 0 or 1 (RcSynth.rc). *)
Lemma lay_rc_range : forall row b, -1 <= RcSynth.rc row b <= 1.
Proof.
  intros row b. unfold RcSynth.rc.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

(* The base bytes of a box row (3 <= k <= 9) are the model's (RcLay.ly_base). *)
Lemma lay_base_box : forall k tb zb, 3 <= k <= 9 -> RcLay.ly_base k tb zb = zb.
Proof.
  intros k tb zb Hk. unfold RcLay.ly_base.
  rewrite (proj2 (Z.eqb_neq k 0) ltac:(lia)), (proj2 (Z.eqb_neq k 1) ltac:(lia)),
    (proj2 (Z.eqb_neq k 2) ltac:(lia)).
  reflexivity.
Qed.

Lemma lay_bb_range : forall k, 0 <= RcLay.ly_bb k < 2 ^ 64.
Proof. intros k. unfold RcLay.ly_bb. repeat destruct (_ =? _); lia. Qed.

Section BOX.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Variable B : asyms.
Variable GLOBS : list (Z * Z).
Hypothesis LAWS : AR_laws SEGS B.
(* the registered globals' shadow and the image's shadow (the composer's, as TMB's own proof takes them) *)
Hypothesis HGM : CtrlRo.globs_marked SEGS B GLOBS.
Hypothesis HIMGSH : CtrlRo.img_shadow_vis SEGS B.
(* B ProgWorld statements: PROVED (a Theorem Labs lane), cited by their lemmas *)
Let ctl_block_shadow_of_AR : B.ProgWorld.ctl_block_shadow_of_AR_stmt B := B.ProgWorldShadow.ctl_block_shadow_of_AR B.
Let ctl_block_apart_fs : B.ProgWorld.ctl_block_apart_fs_stmt B := B.ProgWorldBlkApart.ctl_block_apart_fs B.
(* the callee (a Theorem Labs lane), exactly its type *)
Hypothesis TMB : C_reac_box_model_block.treac_box_model_block_spec RLO RHI B GLOBS.

Lemma lay_box_arm : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc k (regs : bvmap 5 word)
    (p f md g : Z) (fr tb mb nb gb : list byte) S2 pos (regsB : bvmap 5 word) mem3 md3
    (Q : world SEGS -> config -> Prop),
  B.Prog.ctrl_lay_block_gR23.lay_args RLO RHI B GLOBS STK sp0 FP ly S own lyc Sc W memc regs p f md g fr tb mb nb gb ->
  B.Prog.ctrl_lay_block_gR23.lay_Dbox (SK := SK) B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p f md g fr
    pos S2 regsB mem3 md3 ->
  (forall ly4 S4 (W4 : world SEGS) (regs4 : bvmap 5 word) mem4 md4,
     B.Prog.ctrl_lay_block_gD3.lay_D3 (SK := SK) B RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
       p f md g fr tb mb nb gb pos ly4 S4 W4 regs4 mem4 md4 ->
     SRr SEGS W4 (mkCfg (lib.Reusable.YK11.mkst regs4 (Z_to_bv 64 549744) mem4 (lib.Reusable.YK11.seg_rom SEGS)) md4) Q) ->
  SRr SEGS W (mkCfg (lib.Reusable.YK11.mkst regsB (Z_to_bv 64 550360) mem3 (lib.Reusable.YK11.seg_rom SEGS)) md3) Q.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p f md g fr tb mb nb gb S2 pos regsB mem3 md3 Q
    HA HDB K.
  pose proof HA as (HROc & Hra & Hgp & Htp & Rp & Rf & Rmd & Rg & SP16 & Hlo & Hhi & Hroom0 & P0 & P50 & HAWP & Hhome
    & HRA & HHV & HAPP & F8 & FL & HFg & HFro & K9 & AOL & HTM & HMD & HG & DJ1 & DJ2 & DJ3 & DJ3g & DJ3m & DB1 & DB2
    & DB3 & DBN & DBG).
  pose proof HDB as (HJ3 & Hfrs2 & Hnin & Eab2 & Hpos & HGT & Hceil & HNI & Hk & RB1 & RB2 & RB3 & RB4 & RB8 & RB9
    & RB10 & RB11 & RB12 & RB18 & RB19 & RB20 & RB21 & RB22 & RB23 & RB24 & RB25 & RB26 & RB27 & Hro3 & (gj & HSV)
    & HBLK3 & H120 & HAD3 & HK3).
  assert (EK : C_ctrl_lay_block.CTRL_LAY_BLOCK_STK = 4512) by reflexivity.
  assert (ET : C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK = 4272) by reflexivity.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  assert (Hspr : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
  rewrite EK in Hlo, Hceil.
  set (A := (spZ regs - 128) / 32 * 32) in *.
  assert (HA1 : spZ regs - 160 <= A <= spZ regs - 128 /\ A mod 32 = 0) by (subst A; Z.div_mod_to_equations; lia).
  destruct (ctrl_lay_block_gctx.lay_geom1 (ly_F lyc) pos) as (G1 & G2 & G3 & G4 & G5).
  set (fr1 := B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos) in *.
  pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & Hstk & _ & _).
  pose proof Hstk as (Hal0 & Hstk0 & Hceil0 & Hslo & Hshi & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  assert (Hin1 : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  assert (Efa : frame_addr lyc 1 pos = fr1) by (unfold frame_addr; rewrite G1; reflexivity).
  destruct (al_frames _ _ LAWS lyc S2 W mem3 md3 1 pos HAR3 Hin1) as (F32 & FAPP & HFRb & HFRs).
  rewrite Efa, G3 in FAPP, HFRb, HFRs. rewrite Efa in F32. change (128 / 8) with 16 in HFRs.
  pose proof HAR3 as (M3 & _).
  destruct (lib.Reusable.YG0s.frame_facts B lyc S2 _ 1 pos M3 Hin1) as (_ & _ & _ & _ & FPA & _ & _ & FQ8 & _).
  unfold page_aligned in FPA.
  assert (HF64 : fr1 mod 64 = 0) by (rewrite G1; clear - FPA FQ8; Z.div_mod_to_equations; lia).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR3 Hin1) as (FB0 & FB1 & FB2).
  rewrite Efa in FB0. rewrite Efa, G3 in FB1, FB2.
  assert (HFlo : ly_F lyc <= fr1) by (rewrite G1, G4; lia).
  pose proof HK3 as (_ & _ & HK3img & _).
  (* the read-only premise at the call memory *)
  assert (HRO3 : arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mem3)).
  { apply (ctrl_lay_block_gR23.lay_arodata_kept RLO RHI RELRO_IMG B _ _ HROc). intros a Ha Ho He.
    exact (HK3img a Ha Ho He). }
  (* the call state as cfg_at *)
  change (SRr SEGS W (cfg_at SEGS C_reac_box_model_block.REAC_BOX_MODEL_BLOCK regsB mem3 md3) Q).
  assert (EspB : spZ regsB = A).
  { unfold spZ. rewrite RB2. unfold w64. apply B.ProgWorld.pws_u64. lia. }
  assert (EraB : raZ regsB = 549744).
  { unfold raZ. rewrite RB1. apply B.ProgWorld.pws_u64. lia. }
  assert (Hpr : forall a, apresent (w_H W) mem3 a -> aview SEGS (w_H W) mem3 a <> None).
  { intros a (Hh & b & Hb). unfold aview, lib.Reusable.YP09.mbyte, mrestrict. rewrite Hh, Hb. discriminate. }
  assert (Esh : forall x, fr1 <= x < fr1 + 128 ->
            B.AsanRT.shadow_addr x = lib.Reusable.YG0f.shadow_addr fr1 + (x - fr1) / 8).
  { intros x Hx. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr,
      lib.Reusable.YG0f.SHADOW_OFF. clear - Hx HF64. Z.div_mod_to_equations; lia. }
  assert (Hinro : forall x, APostBase.in_roP SEGS RLO RHI x -> in_img SEGS x)
    by exact (ctrl_lay_block_gR23.lay_inro_img RLO RHI RELRO_IMG).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in FB2.
  eapply SRr_bind.
  { apply (TMB STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem3 md3 k regsB md (RcLay.ly_bb (RcLay.ly_k fr))
             (fr1 + 32) mb nb HJ3 HRO3).
    - rewrite RB1. apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
    - rewrite EraB. lia.
    - rewrite RB3. exact Hgp.
    - rewrite RB4. exact Htp.
    - exact RB10.
    - exact RB11.
    - exact RB12.
    - exact Rmd.
    - exact (lay_bb_range _).
    - lia.
    - rewrite EspB. clear - HA1. Z.div_mod_to_equations; lia.
    - rewrite EspB, ET. lia.
    - rewrite EspB. lia.
    - rewrite Hfrs2. cbn [count_cid fst]. rewrite (proj2 (Z.eqb_neq 1 0) ltac:(lia)). lia.
    - intros Hmd0. destruct (HMD Hk Hmd0) as (M8 & ML & MG & ((q0 & sz & Hq & Hq1 & Hq2) & MI1 & MI2 & MRO) & _).
      unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in MI1, MI2.
      split; [exact M8|]. split; [exact ML|]. split.
      { apply (ctrl_lay_block_gR23.lay_garr8_kept (w_H W) (w_H W) memc mem3 md _ MG). intros j Hj.
        rewrite length_map, ML in Hj.
        assert (Hj' : 0 <= Z.of_nat j < 296) by (split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_lt in Hj; exact Hj]).
        destruct (MRO (md + Z.of_nat j) ltac:(lia)) as (X1 & X2 & X3). exact (HK3img _ (Hinro _ X1) X2 X3). }
      split; [exists q0, sz; split; [exact Hq | lia]|].
      split; [unfold CtrlRo.IMG_LO; lia|]. split; [unfold CtrlRo.IMG_HI; lia|].
      split; [exact MRO|]. right. right. unfold B.Prog.asan_stack_malloc_c.ASAN_GT in HGT. lia.
    - intros Hmd0 Hb5 Hh Hn. destruct (HMD Hk Hmd0) as (_ & _ & _ & _ & HN).
      destruct (HN Hb5 Hh Hn) as (Hok & NG & ((q0 & sz & Hq & Hq1 & Hq2) & NI1 & NI2 & NRO)).
      unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in NI1, NI2.
      split; [exact Hok|]. split.
      { apply (ctrl_lay_block_gR23.lay_garr8_kept (w_H W) (w_H W) memc mem3 _ _ NG). intros j Hj.
        rewrite length_map in Hj.
        assert (Hj' : 0 <= Z.of_nat j < Z.of_nat (length nb))
          by (split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_lt in Hj; exact Hj]).
        destruct (NRO (RcSynth.rname mb + Z.of_nat j) ltac:(lia)) as (X1 & X2 & X3).
        exact (HK3img _ (Hinro _ X1) X2 X3). }
      split; [exists q0, sz; split; [exact Hq | lia]|].
      split; [unfold CtrlRo.IMG_LO; lia|]. split; [unfold CtrlRo.IMG_HI; lia|].
      split; [exact NRO|]. right. right. unfold B.Prog.asan_stack_malloc_c.ASAN_GT in HGT. lia.
    - intros _. split.
      { left. exists 1, pos. split; [exact Hin1|]. split; [lia|]. intros x Hx. unfold in_zr, frame_rng.
        cbn [fst snd]. rewrite Efa, G3. lia. }
      split.
      { intros x Hx Hi. apply (frm_img SEGS B LAWS _ _ _ _ _ 1 pos x HAR3 Hin1); [rewrite Efa, G3; lia | exact Hi]. }
      split.
      { intros a Ha. split.
        - right. right. right. exists 1, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
          rewrite Efa, G3. lia.
        - destruct (HFRb a ltac:(lia)) as (Hp & Hno). split; [exact Hp|]. split; [exact Hno|]. rewrite EspB.
          unfold ESTACK. lia. }
      split.
      { split.
        - intros a Ha. destruct (HFRb a ltac:(lia)) as (Hp & _). split; [exact (Hpr a Hp)|]. rewrite EspB.
          unfold ESTACK. lia.
        - split.
          + apply (ctrl_lay_block_gR23.lay_addressable_raddr W mem3 (fr1 + 32) 32 HAD3). intros x Hx.
            rewrite (Esh x ltac:(lia)).
            exact (proj1 (proj1 (HFRs ((x - fr1) / 8) ltac:(clear - Hx; Z.div_mod_to_equations; lia)))).
          + split.
            * intros s Hs. unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in Hs.
              replace s with (lib.Reusable.YG0f.shadow_addr fr1 + (s - lib.Reusable.YG0f.shadow_addr fr1)) by lia.
              apply Hpr. apply (proj1 (HFRs (s - lib.Reusable.YG0f.shadow_addr fr1) ltac:(unfold
                lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF; clear - Hs HF64; Z.div_mod_to_equations; lia))).
            * split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|]. split; lia. }
      right. rewrite EspB, ET. lia. }
  cbv beta. intros W4 c4 Hwle (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfrs4 & Eab4 & HIF).
  rewrite RB1.
  apply (K ly4 S4 W4 regs4 mem4 md4).
  change (k + C_reac_box_model_block.EV_BMB) with (k + 0) in HJ4. rewrite Z.add_0_r in HJ4.
  pose proof HJ4 as (HAR4 & Hly4 & _).
  pose proof Hly4 as (_ & _ & _ & _ & _ & EF4 & _).
  assert (EFl : ly_F ly4 = ly_F lyc) by congruence.
  assert (Eab4' : ablocks B ly4 S4 = ablocks B lyc Sc) by (rewrite Eab4; exact Eab2).
  assert (Hfrs4' : frames S4 = (1, pos) :: frames Sc) by (rewrite Hfrs4; exact Hfrs2).
  (* TMB's kept clause at the call's window *)
  assert (Esel : forall X Y : Prop, ((md =? 0) || (fr1 + 32 =? 0) = true -> X) ->
            ((md =? 0) || (fr1 + 32 =? 0) = false -> Y) -> X \/ Y).
  { intros X Y HX HY. destruct ((md =? 0) || (fr1 + 32 =? 0)); [left; apply HX | right; apply HY]; reflexivity. }
  assert (HK4 : CtrlCallerJ.tcj_kept B C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK lyc S2 W mem3 W4 mem4 A
                  (C_reac_box_model_block.treac_box_model_block_out (fr1 + 32))).
  { rewrite <- EspB. destruct ((md =? 0) || (fr1 + 32 =? 0)).
    - destruct HIF as (_ & HK). apply (ctrl_lay_block_gR23.lay_tcj_E B _ _ _ _ _ _ _ _ (fun _ => False)); [intros a [] | exact HK].
    - destruct HIF as (_ & _ & HK). exact HK. }
  pose proof HK4 as (T1 & T2 & T3 & T4 & T5 & T6).
  rewrite ET in T1, T5, T6.
  unfold C_reac_box_model_block.treac_box_model_block_out in T1, T2, T4.
  (* the read-only premise at the return memory *)
  assert (HRO4 : arodata_okS SEGS B RLO RHI (aview SEGS (w_H W4) mem4)).
  { apply (ctrl_lay_block_gR23.lay_arodata_kept RLO RHI RELRO_IMG B _ _ HRO3). intros a Ha Ho He.
    exact (T3 a Ha Ho He). }
  (* what the call kept from its entry memory *)
  assert (HKc : acall_kept SEGS B lyc Sc W memc W4 mem4 (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs)
                  (C_ctrl_lay_block.tctrl_lay_block_out p)).
  { apply (ctrl_lay_block_gR23.lay_kept_tmb B LAWS S2 W W W4 memc mem3 mem4 md3 lyc Sc pos regs
             _ HAR3 Hfrs2 Eab2 Hpos); [rewrite EK; exact Hceil | exact HK3 | exact HK4]. }
  (* the output block at the return memory: present, its bytes kept (TMB writes only its own window and fr1 + 32) *)
  assert (PRE4 : forall a, p + 18 <= a < p + 50 -> apresent (w_H W4) mem4 a /\ ~ aowned B ly4 S4 a).
  { apply (ctrl_lay_block_gR23.lay_out_present B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc ly4 S4 W4 mem4 md4 k p pos
             HJ4 Eab4' EFl). intros a Ha. exact (proj1 (HAWP a Ha)). }
  assert (PRE3 : forall a, p + 18 <= a < p + 50 -> apresent (w_H W) mem3 a /\ ~ aowned B lyc S2 a).
  { apply (ctrl_lay_block_gR23.lay_out_present B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc lyc S2 W mem3 md3 k p pos
             HJ3 Eab2 eq_refl). intros a Ha. exact (proj1 (HAWP a Ha)). }
  destruct (ctrl_lay_block_gR23.lay_fr1_apart B LAWS S2 W mem3 md3 lyc Sc pos HAR3 Hfrs2 Eab2 Hpos)
    as (AB & AF & _).
  assert (BLK4 : lib.Lib.Step.rw_cells B.Img0.rsegs mem4 (p + 18) [lib.Lib.Cells.CB 32 RcLay.ly_zero]).
  { apply (ctrl_lay_block_gR23.lay_rw_kept W W4 mem3 mem4 (p + 18) _ HBLK3).
    - intros i Hi. change (Z.of_nat (lib.Lib.Cells.cells_size [lib.Lib.Cells.CB 32 RcLay.ly_zero])) with 32 in Hi.
      exact (Hpr _ (proj1 (PRE3 (p + 18 + i) ltac:(lia)))).
    - intros i Hi. change (Z.of_nat (lib.Lib.Cells.cells_size [lib.Lib.Cells.CB 32 RcLay.ly_zero])) with 32 in Hi.
      destruct (Hhome (p + 18 + i) ltac:(lia))
        as [(Himg & _ & _) | [(b & mm & i0 & Hin & Hi0 & Ea) | (cid & q & Hin & Hc & Hr)]].
      + exfalso. exact (HNI (p + 18 + i) ltac:(lia) Himg).
      + rewrite Ea. apply (T2 b mm i0 ltac:(rewrite Eab2; exact Hin) Hi0).
        pose proof (AB b mm i0 Hin Hi0). lia.
      + apply (T4 cid q (p + 18 + i) ltac:(rewrite Hfrs2; right; exact Hin) (or_introl Hr)).
        pose proof (AF cid q (p + 18 + i) Hin (or_introl Hr)). lia.
    - intros i Hi. change (Z.of_nat (lib.Lib.Cells.cells_size [lib.Lib.Cells.CB 32 RcLay.ly_zero])) with 32 in Hi.
      exact (proj1 (PRE4 (p + 18 + i) ltac:(lia))). }
  assert (HAD4 : B.AsanRT.addressable mem4 (p + 18) 32).
  { apply (ctrl_lay_block_gR23.lay_blk_addr B LAWS ly4 S4 W W4 memc mem4 md4 lyc Sc p
             (C_ctrl_lay_block.tctrl_lay_block_out p) (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) HAR4);
             [ | exact Eab4' | exact EFl | exact Hhome | exact HNI
             | exact HKc | | exact HRA | exact HAPP | lia].
    - intros c q H. rewrite Hfrs4'. right. exact H.
    - intros a Ha. unfold C_ctrl_lay_block.tctrl_lay_block_out in Ha. apply HAPP. lia. }
  unfold ctrl_lay_block_gD3.lay_D3.
  split; [exact HJ4|]. split; [exact Hwle|].
  split; [exact Hfrs4'|]. split; [exact Hnin|]. split; [exact Eab4'|].
  split; [exact EFl|]. split; [exact Hpos|]. split; [exact HGT|].
  split; [rewrite EK; exact Hlo|]. split; [exact Hhi|]. split; [exact Hra|]. split; [exact Hgp|]. split; [exact Htp|].
  split; [exact Hhome|].
  pose proof HFro as (_ & HFr1 & HFr2 & _). unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in HFr1, HFr2.
  split; [lia|]. split; [unfold B.Prog.asan_stack_malloc_c.ASAN_GT; lia|].
  split; [intros a Ha; exact (proj1 (HAWP a Ha))|]. split; [exact Hk|].
  (* the callee-saved registers *)
  assert (P : forall r, acallee_saved r -> getr regs4 (Z_to_bv 5 r) = getr regsB (Z_to_bv 5 r)) by exact HP4.
  split; [etransitivity; [exact (P 2 ltac:(unfold acallee_saved; lia)) | exact RB2]|].
  split; [etransitivity; [exact (P 3 ltac:(unfold acallee_saved; lia)) | exact RB3]|].
  split; [etransitivity; [exact (P 4 ltac:(unfold acallee_saved; lia)) | exact RB4]|].
  split; [etransitivity; [exact (P 8 ltac:(unfold acallee_saved; lia)) | exact RB8]|].
  split; [etransitivity; [exact (P 9 ltac:(unfold acallee_saved; lia)) | exact RB9]|].
  split; [etransitivity; [exact (P 18 ltac:(unfold acallee_saved; lia)) | exact RB18]|].
  split; [etransitivity; [exact (P 19 ltac:(unfold acallee_saved; lia)) | exact RB19]|].
  split; [etransitivity; [exact (P 20 ltac:(unfold acallee_saved; lia)) | exact RB20]|].
  split; [etransitivity; [exact (P 21 ltac:(unfold acallee_saved; lia)) | exact RB21]|].
  split; [etransitivity; [exact (P 22 ltac:(unfold acallee_saved; lia)) | exact RB22]|].
  split; [etransitivity; [exact (P 23 ltac:(unfold acallee_saved; lia)) | exact RB23]|].
  split; [etransitivity; [exact (P 24 ltac:(unfold acallee_saved; lia)) | exact RB24]|].
  split; [etransitivity; [exact (P 25 ltac:(unfold acallee_saved; lia)) | exact RB25]|].
  split; [etransitivity; [exact (P 26 ltac:(unfold acallee_saved; lia)) | exact RB26]|].
  split; [etransitivity; [exact (P 27 ltac:(unfold acallee_saved; lia)) | exact RB27]|].
  (* reac_box_model_block's result and the base bytes it left at fr1 + 32 *)
  split.
  { unfold ctrl_lay_blockF_on.BASE. rewrite (lay_base_box _ tb _ Hk). unfold RcLay.ly_Z.
    destruct (Z.eq_dec md 0) as [Hmd0 | Hmd0].
    - assert (E1 : (md =? 0) || (fr1 + 32 =? 0) = true) by (rewrite Hmd0; reflexivity).
      rewrite E1 in HIF. destruct HIF as (Ha04 & _).
      exists (-1). split; [exact Ha04|]. split; [lia|]. split; [intros H; lia|].
      intros _. rewrite Hmd0. reflexivity.
    - assert (E1 : (md =? 0) || (fr1 + 32 =? 0) = false)
        by (apply orb_false_iff; split; apply Z.eqb_neq; lia).
      rewrite E1 in HIF. destruct HIF as (Ha04 & Hg4 & _).
      rewrite (proj2 (Z.eqb_neq md 0) Hmd0).
      exists (RcSynth.rc mb (RcLay.ly_bb (RcLay.ly_k fr))). split; [exact Ha04|]. split; [exact (lay_rc_range _ _)|].
      destruct (HMD Hk Hmd0) as (_ & ML & _).
      split.
      + intros Hr1. rewrite (proj2 (Z.eqb_eq _ 1) Hr1).
        pose proof (RcSynthLib.rs_synth_len mb (RcLay.ly_bb (RcLay.ly_k fr)) nb ML) as SL.
        split; [|exact SL].
        apply (lay_bytes_of_garr8 W4 mem4 (fr1 + 32) _ ltac:(lia) ltac:(rewrite SL; lia) Hg4).
      + intros Hr1. rewrite (proj2 (Z.eqb_neq _ 1) Hr1). reflexivity. }
  split; [exact HRO4|].
  (* the 32-byte cell below the saves and the 12 saves *)
  split.
  { exists gj. apply (ctrl_lay_block_gR23.lay_rw_kept W W4 mem3 mem4 (spZ regs + -128) _ HSV).
    - intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add ctrl_lay_blockF_on.SAVES] in Hi.
      exact (Hpr _ (Hpres3 (spZ regs + -128 + i) ltac:(lia))).
    - intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add ctrl_lay_blockF_on.SAVES] in Hi.
      apply T1; lia.
    - intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add ctrl_lay_blockF_on.SAVES] in Hi.
      apply T5; [lia | lia | exact (Hpres3 (spZ regs + -128 + i) ltac:(lia))]. }
  (* the frame's flag-address word *)
  split.
  { apply (ctrl_lay_block_gR23.lay_bytes_kept W W4 mem3 mem4 (fr1 + 120) _ H120).
    - intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi.
      exact (Hpr _ (proj1 (HFRb (fr1 + 120 + Z.of_nat i) ltac:(lia)))).
    - intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi.
      apply (T4 1 pos (fr1 + 120 + Z.of_nat i) Hin1); [left; unfold in_zr, frame_rng; cbn [fst snd];
        rewrite Efa, G3; lia | lia]. }
  (* the box output block's shadow *)
  split.
  { apply (ctrl_lay_block_gR23.lay_addr_kept W W4 mem3 mem4 (fr1 + 32) 32 HAD3).
    - intros i Hi. rewrite (Esh (fr1 + 32 + i) ltac:(lia)).
      exact (proj1 (proj1 (HFRs ((fr1 + 32 + i - fr1) / 8) ltac:(clear - Hi; Z.div_mod_to_equations; lia)))).
    - intros i Hi. apply (T4 1 pos _ Hin1).
      + right. rewrite Efa. unfold in_zr. cbn [fst snd]. rewrite G3. change (128 / 8) with 16.
        rewrite (Esh (fr1 + 32 + i) ltac:(lia)). clear - Hi. Z.div_mod_to_equations; lia.
      + rewrite (Esh (fr1 + 32 + i) ltac:(lia)). unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
        clear - Hi FB0 FB1 FB2 C1 Hc1. Z.div_mod_to_equations; lia. }
  (* the stretch's read facts at the return *)
  split.
  { exact (ctrl_lay_block_gR23.lay_pure_of RLO RHI B GLOBS W memc regs p f md g (ly_F lyc) fr tb mb nb gb HROc HGT
             Rp Rf Rmd Rg SP16 P0 P50 HNI HAPP F8 FL HFro K9 AOL HTM HMD HG DJ1 DJ2 DJ3 DJ3g DJ3m DB1 DB2 DB3 DBN DBG). }
  split.
  { exact (ctrl_lay_block_gR23.lay_data_of RLO RHI B GLOBS HGM HIMGSH ly4 S4 W W4 memc mem4 md4 p f md g fr
             RcLay.ly_zero tb mb nb gb HAR4 Hwle HROc HRO4 BLK4 HAD4 (fun a Ha => proj2 (HAWP a Ha)) HHV ltac:(lia) P50
             FL HFg HFro HTM HMD HG). }
  (* route (C): the image bounds of the read-only ranges (lay_cut_ctx's SR0 at the box return) *)
  split; [exact (ctrl_lay_block_gR23.lay_img_ro_of_args RLO RHI B GLOBS STK sp0 FP ly S own lyc Sc W memc regs
                   p f md g fr tb mb nb gb HA)|].
  exact HKc.
Qed.
End BOX.
