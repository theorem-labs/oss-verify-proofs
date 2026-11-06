(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 2867 of its 3071 lines of code are new or changed and 2908 lines of the source are left out. *)
(* lib/B/ACtlW1.v -- piece W1 (pre-loop: S_A4, S_A5, S_R1, S_R2, S_R3, S_R4, S_R5) of fuzz_ctrl image B's
   (asan-ubsan) walk of LLVMFuzzerTestOneInput in the released cgif_file_fuzzer form.  One writer: a Theorem Labs lane
   (proof pass).  rule 24: no function proved (stage glue of a walk).  Header: see the end of the file. *)

From Coq Require Import ZArith List Permutation Lia.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Lib.ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d Reusable.YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YB1w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCfn Reusable.YE01 Reusable.YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.APostBase Reusable.SetShadowDefP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.Regs6ss.
(* lib/Lib's raw-memory vocabulary (Required only, never Imported). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Frame Cells Step Mem PropExec MState Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.AsanRT B.ACtlK B.ACtlCut B.ACtlCutP.
(* a Theorem Labs lane's frozen image-B bridge and a Theorem Labs lane's image-B ProgWorld layer (the RtPost lemmas). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgBridge B.ProgWorld B.ProgWorld_Fs.
(* route (C): the cut's ctl_rt_C (a Theorem Labs lane's B twin of a Theorem Labs lane's cform), its proof from AR, the narrowed shadow
   vocabulary and its transports. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ACtlRtC ProgWorldCtlRtC ShadowRwOn ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.MemNorm B.MemNormF B.MemNormTr.
(* a Theorem Labs lane's published `_F` modules (Required qualified, never Imported, a Theorem Labs lane 23:38Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require A4F A5F R1F R2F R3F R4F R5F.
(* the segment sources' pure helper lemmas (Required only, used in proofs) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R3 R4 R5 R6 R7 RtmB A5.
(* the image-B callee footprint contracts (statements) and the closed reac_box_catalogue run *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.CtrlBase B.Prog.ImgBounds B.Prog.rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.asan_memset_c B.Prog.asan_memset_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.asan_set_shadow_c B.Prog.asan_set_shadow_cF.
(* route (C): the two callees' shared _on statements and their proofs (a Theorem Labs lane, by path on a working branch):
   reac_identity_init_c.v:160 with reac_identity_initF.v (a Theorem Labs lane 74be6b218f4, cbrec v9 VERDICT ok) over
   asan_memsetF_on.v and memset.v; reac_box_catalogue_c.v:137 with reac_box_catalogueF.v:17. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_identity_init_c B.Prog.reac_identity_initF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.asan_memsetF_on B.Prog.memset.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_box_catalogue_c B.Prog.reac_box_catalogueF.
Import ListNotations.
Local Open Scope Z_scope.

Section W1.

Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

Local Notation segs := Reusable.YB1v.tfibsegs.

(* ---- SHELL BINDING: the only lines that name ACtlCut's / ACtlCutP's argument lists. ---- *)
Local Notation ctl_from := (ACtlCut.ctl_from B MT XM_LIB RLO RHI FP).
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation C_B81220 := (ACtlCutP.C_B81220 B).
Local Notation C_B81548_at := (ACtlCutP.C_B81548_at B).
Local Notation C_B81550 := (ACtlCutP.C_B81550 B).
Local Notation C_B815fc := (ACtlCutP.C_B815fc B).
Local Notation C_B81640 := (ACtlCutP.C_B81640 B).
Local Notation C_B8168c := (ACtlCutP.C_B8168c B).
Local Notation C_B8169c := (ACtlCutP.C_B8169c B).
Local Notation C_B816ec_at := (ACtlCutP.C_B816ec_at B).
Local Notation C_B81cb0 := (ACtlCutP.C_B81cb0 B).
Local Notation C_Jrel := (ACtlCutP.C_Jrel B).
Local Notation CBASE cx := (ACtlCut.ctl_base B MT XM_LIB RLO RHI cx).
Local Notation AJ cx own ly3 S3 W3 mem3 md3 k :=
  (Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
     (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
     own ly3 S3 W3 mem3 md3 k).
Local Notation KEEPR m m' lo hi :=
  (forall a : Z, lo <= a < hi ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)).

(* ---- Section hypotheses (sources and owners in the closing notes) ---- *)
(* The core's AR laws (YG0d.v AR_laws; the donor walk takes them the same way, A/ACf2.v:47). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
(* Route (C) (routeC-refit.md (a working note, not in this delivery)): every successor cut's ctl_rt_C is B.ProgWorldCtlRtC.ctl_rt_C_of_AR (PROVED; CtrlTSyms +
   AR_laws + AR + arodata_okP, no AR_states_vis0_shadow, no AR_states_owned_ro); RELRO_IMG and RO_OFL are the premises
   of APostBase.arodata_ok_journalP (ctl_base's arodata_okS kept along the journal), exact names and texts given by
   a Theorem Labs lane (06:40Z / 06:46Z). *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Context {RO_OFL : Reusable.APostBase.ro_below_ofl segs RLO RHI}.

(* ===========================================================================================================
   1. Helpers (prefix w1_).  Image-B twins of lib/B/ACtlW5.v's / ACtlW2a.v's glue kit. *)

Lemma w1_img : forall a, Reusable.YG0d.in_img segs a -> 0x10000 <= a < 0x5fe000.
Proof.
  intros a (sg & Hin & Ha).
  pose proof (in_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) _ _ Hin) as Hm.
  change Reusable.YB1v.tfibsegs with B.Img0.rsegs in Hm. rewrite B.ProgBridge.rsegs_spans in Hm.
  cbn [In] in Hm. destruct Hm as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; lia.
Qed.

Lemma w1_segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.
Proof. intros a H. apply w1_img in H. unfold Reusable.YG0f.kLowMemEnd. lia. Qed.

Lemma w1_wx : Reusable.YK04.wx_segs_nowrap segs.
Proof. apply Reusable.YK04.wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* The lift of a footprint run from a cut's state (lib/B/ACtlW5.v w5_lift). *)
Lemma w1_lift : forall (W : Reusable.YA0n.world segs) (regs : bvmap 5 word) (mem : word -> option byte) md (pc : Z)
    (RNG : Lib.ExecF.footprint) (P : machine_state -> Prop) (Q : Reusable.YA0n.world segs -> config -> Prop),
  Lib.ExecF.evtF B.Img0.rsegs RNG P
    (lib.Lib.MState.MS (Lib.Regs6ss.mkR_of regs) lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None
       mem (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) ->
  Reusable.YK04R.fp_avoids (Reusable.YA0n.w_H W) RNG ->
  (forall ms' md', P ms' -> (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = mem x) ->
     Reusable.YK04.same_but_materialized md md' -> Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc regs mem md) Q.
Proof.
  intros W regs mem md pc RNG P Q Hrun Hav K.
  change (Reusable.YG0d.cfg_at segs pc regs mem md) with
    (mkCfg (lib.Lib.MState.MS regs lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem
              (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) md).
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W (Lib.Regs6ss.mkR_of regs) regs).
  2: exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs)).
  apply (Reusable.YA0nR.SRr_fevt_hid segs w1_wx W _ md RNG P Q (B.ProgBridge.fevt_of_evtF RNG P _ Hrun) Hav).
  intros ms' md' HP Hhid Hsbm. apply (K ms' md' HP); [| exact Hsbm].
  intros x Hx. rewrite (Hhid x Hx). reflexivity.
Qed.

(* The owned class-6 frame of an own6 cut (lib/B/ACtlW5.v w5_frame). *)
Lemma w1_frame : forall (cx : ACtlCut.ctlcx) ly3 S3 W3 mem3 md3 k,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3) /\
  Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) /\
  4096 <= Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) /\
  Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) + 4096 <= lib.Reusable.YM05.alloc_ceiling /\
  Reusable.YG0f.in_app (Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)) 4096 /\
  (forall a, Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) <= a <
             Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) + 4096 ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a /\ ~ Reusable.YG0d.in_img segs a) /\
  (forall i, 0 <= i < 512 ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3
       (Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)) + i)).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k HJ Hfr.
  pose proof HJ as (HAR & Hly & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (Efa : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) =
                Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)).
  { unfold Reusable.YG0f.frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (E64 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (Hb0 & Hb1 & Happ).
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (_ & _ & Hfb & Hfsh).
  rewrite Efa, E64 in *.
  split; [exact Hin|]. split; [reflexivity|]. split; [exact Hb0|]. split; [exact Hb1|]. split; [exact Happ|].
  split.
  - intros a Ha. split; [exact (proj1 (Hfb a Ha))|].
    refine (proj2 (Reusable.YG0d.al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 a HAR _)).
    right. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin|]. rewrite Efa, E64. exact Ha.
  - intros i Hi. exact (proj1 (Hfsh i ltac:(change (4096 / 8) with 512; lia))).
Qed.

(* The journal's stack facts (lib/B/ACtlW5.v w5_stack). *)
Lemma w1_stack : forall (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k,
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  lib.Reusable.YM05.alloc_ceiling + 32768 <= ACtlCut.c_sp cx /\ ACtlCut.c_sp cx <= 2 ^ 47 /\
  ACtlCut.c_sp cx mod 16 = 0 /\
  (forall a, ACtlCut.c_sp cx - 32768 <= a < ACtlCut.c_sp cx -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HJ.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hstk & _).
  destruct Hstk as (H16 & _ & Hceil & Hlo & Hhi & H47 & _).
  unfold Reusable.YCfn.LLVMF_STK in *.
  split; [lia|]. split; [lia|]. split; [exact H16|]. exact Hwin.
Qed.

(* The journal across a footprint run whose writes (the interval list WR of its munch) are bytes of the journal's
   stack window or of the owned frames, all outside the image (YCbq.ajournal_exec; lib/B/ACtlW5.v w5_journal_munch
   with a list of intervals). *)
Lemma w1_journal_run : forall (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k (m' : word -> option byte) md'
    (WR : list (Z * Z)),
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  lib.Lib.Frame.munch WR mem3 m' -> lib.Lib.Frame.wmono B.Img0.rsegs mem3 m' ->
  (forall x : word, Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) ->
  Reusable.YK04.same_but_materialized md3 md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside WR a ->
     ((ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= a < ACtlCut.c_sp cx) \/ Reusable.YCbq.in_frames ly3 own a) /\
     ~ Reusable.YG0d.in_img segs a) ->
  AJ cx own ly3 S3 W3 m' md' k.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k m' md' WR HJ Hmu Hwm Hhid Hsbm HW.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS w1_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' md'
           (fun a => 0 <= a < 2 ^ 64 /\ ~ lib.Lib.Frame.outside WR a) HJ).
  - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (Hmu x); [reflexivity|].
    destruct (B.ProgWorld.pws_outside_dec WR (bv_unsigned x)) as [Ho|Ho]; [exact Ho|].
    exfalso. apply Hx. split; [|exact Ho].
    pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx. exact Rx.
  - intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H W3 x) eqn:Eh; [exact Hx|].
    pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
    destruct (B.ProgWorld.pws_outside_dec WR (bv_unsigned x)) as [Ho|Ho].
    + rewrite (Hmu x Ho). exact Hx.
    + destruct (HW (bv_unsigned x) Rx Ho) as [_ Hni].
      assert (Hv : wview B.Img0.rsegs mem3 x <> None).
      { unfold wview. destruct (mem3 x); [discriminate | exfalso; exact (Hx eq_refl)]. }
      apply Hwm in Hv. unfold wview in Hv. destruct (m' x) as [b|]; [discriminate|].
      exfalso. apply Hv.
      replace (find_segment B.Img0.rsegs (bv_unsigned x) 1) with (@None Segment)
        by (symmetry; exact (Reusable.YCbq.find_segment_none segs _ Hni)).
      reflexivity.
  - exact Hhid.
  - exact Hsbm.
  - intros a (Ha & Hin). destruct (HW a Ha Hin) as [[Hs | Hf] _]; [left; exact Hs | right; right; right; exact Hf].
Qed.

(* The kept read-only view at a cut state (a Theorem Labs lane 06:46Z): ctl_base's arodata_okS at the entry, the journal to
   the state (APostBase.arodata_ok_journalP). *)
Lemma w1_aro : forall (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k,
  CBASE cx -> AJ cx own ly3 S3 W3 mem3 md3 k ->
  B.Prog.CtrlBase.arodata_okP segs RLO RHI B (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _) & _).
  pose proof (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HRO (Z.le_refl _) (Z.le_refl _)) as HP0.
  exact (Reusable.APostBase.arodata_ok_journalP segs RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HP0).
Qed.

(* ctl_rt_C at a successor cut (route (C)): the journal's AR and the kept read-only view, into a Theorem Labs lane's proved
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR (no AR_states_vis0_shadow, no AR_states_owned_ro). *)
Lemma w1_rt : forall (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k,
  CBASE cx -> AJ cx own ly3 S3 W3 mem3 md3 k -> B.ACtlRtC.ctl_rt_C B ly3 S3 mem3.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  exact (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 mem3 md3 (proj1 HJ)
           (w1_aro cx own ly3 S3 W3 mem3 md3 k HB HJ)).
Qed.

(* ---- raw-memory keeping ---- *)
Lemma w1_keep_munch : forall (WR : list (Z * Z)) (m m' : word -> option byte) (lo hi : Z),
  lib.Lib.Frame.munch WR m m' ->
  (forall a, lo <= a < hi -> 0 <= a < 2 ^ 64 /\ lib.Lib.Frame.outside WR a) ->
  KEEPR m m' lo hi.
Proof.
  intros WR m m' lo hi Hmu H a Ha. destruct (H a Ha) as [Hr Ho].
  unfold lib.Lib.Mem.mrd. rewrite (Hmu (Z_to_bv 64 a)); [reflexivity|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. exact Ho.
Qed.

Lemma w1_keep_vis : forall (H : word -> bool) (WR : list (Z * Z)) (m m' : word -> option byte) (lo hi : Z),
  B.ProgWorld.munch_vis H WR m m' ->
  (forall a, lo <= a < hi -> 0 <= a < 2 ^ 64 /\ H (Z_to_bv 64 a) = false /\ lib.Lib.Frame.outside WR a) ->
  KEEPR m m' lo hi.
Proof.
  intros H WR m m' lo hi MV K a Ha. destruct (K a Ha) as (Hr & Hv & Ho).
  apply (MV (Z_to_bv 64 a) Hv). rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. exact Ho.
Qed.

Lemma w1_keep_sub : forall (m m' : word -> option byte) (lo hi lo' hi' : Z),
  KEEPR m m' lo hi -> lo <= lo' -> hi' <= hi -> KEEPR m m' lo' hi'.
Proof. intros m m' lo hi lo' hi' K H1 H2 a Ha. apply K. lia. Qed.

Lemma w1_bytes_keep : forall (m m' : word -> option byte) (a : Z) (bs : list byte),
  KEEPR m m' a (a + Z.of_nat (length bs)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros m m' a bs K (H0 & H1 & H2). split; [exact H0 |]. split; [exact H1 |].
  intros i Hi. unfold lib.Lib.Mem.wa. rewrite K by lia. exact (H2 i Hi).
Qed.

Lemma w1_q64_keep : forall (m m' : word -> option byte) (a v : Z),
  KEEPR m m' a (a + 8) -> ACtlCutP.q64 m a v -> ACtlCutP.q64 m' a v.
Proof.
  intros m m' a v K H. unfold ACtlCutP.q64 in *. apply (w1_bytes_keep m m'); [|exact H].
  rewrite lib.Lib.Mem.length_le8. exact K.
Qed.

Lemma w1_addr_keep : forall (m m' : word -> option byte) (p n : Z),
  (forall i, 0 <= i < n ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i)))) ->
  B.AsanRT.addressable m p n -> B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n K (H0 & H1 & H2 & H3). split; [exact H0 |]. split; [exact H1 |]. split; [exact H2 |].
  intros i Hi. destruct (H3 i Hi) as (Happ & b & Hb & Hok). split; [exact Happ |]. exists b. split; [| exact Hok].
  unfold lib.Lib.Mem.wa in *. rewrite (K i Hi). exact Hb.
Qed.

(* addressable bytes of the owned frame stay addressable when its shadow [Sfr fr, Sfr fr + 392) is kept. *)
Lemma w1_faddr_keep : forall (m m' : word -> option byte) (fr X n : Z),
  KEEPR m m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW) ->
  fr mod 8 = 0 -> 0 <= X -> 0 <= n -> X + n <= ACtlCutP.FRAME_BYTES ->
  B.AsanRT.addressable m (fr + X) n -> B.AsanRT.addressable m' (fr + X) n.
Proof.
  intros m m' fr X n K H8 HX Hn HXn. apply w1_addr_keep. intros i Hi. apply K. clear K.
  unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in *.
  change (3136 / 8) with 392. Z.div_mod_to_equations. lia.
Qed.

Lemma w1_rgv_unsigned : forall (regs : bvmap 5 word) (r : bv 5) (v : Z),
  ACtlCut.rgv regs r v -> 0 <= v < 2 ^ 64 -> bv_unsigned (lib.Reusable.YK11.getr regs r) = v.
Proof.
  intros regs r v H Hv. unfold ACtlCut.rgv in H. rewrite H, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Hv.
Qed.

Lemma w1_rgv_eq : forall (regs : bvmap 5 word) (r : bv 5) (x y : Z),
  ACtlCut.rgv regs r x -> ACtlCut.rgv regs r y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x = y.
Proof.
  intros regs r x y Hx Hy Hxr Hyr.
  rewrite <- (w1_rgv_unsigned regs r x Hx Hxr), <- (w1_rgv_unsigned regs r y Hy Hyr). reflexivity.
Qed.

Lemma w1_rgv_move : forall (R regs : bvmap 5 word) (r : bv 5) (v : Z),
  lib.Reusable.YK11.getr R r = lib.Reusable.YK11.getr regs r -> ACtlCut.rgv regs r v -> ACtlCut.rgv R r v.
Proof. intros R regs r v E H. unfold ACtlCut.rgv in *. rewrite E. exact H. Qed.

Lemma w1_spZ_range : forall regs : bvmap 5 word, 0 <= Reusable.YG0d.spZ regs < 2 ^ 64.
Proof.
  intros regs. unfold Reusable.YG0d.spZ.
  pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 2)) as H.
  change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

(* A spill read at the spill base A (lib/B/ACtlW2a.v w2_spill_at). *)
Lemma w1_spill_at : forall (regs : bvmap 5 word) (m : word -> option byte) (A off v : Z),
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 448 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m A off v H9 HA0 HA1 Ho0 Ho1 (A' & H9' & Hq).
  pose proof Hq as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1.
  assert (EA : A' = A).
  { unfold ACtlCut.rgv in H9, H9'. rewrite H9 in H9'.
    apply (f_equal bv_unsigned) in H9'. rewrite !Z_to_bv_unsigned in H9'. unfold bv_wrap in H9'.
    change (bv_modulus 64) with (2 ^ 64) in H9'. rewrite (Z.mod_small A) in H9' by lia.
    pose proof (Z.mod_pos_bound A' (2 ^ 64) ltac:(lia)). pose proof (Z.div_mod A' (2 ^ 64) ltac:(lia)).
    lia. }
  subst A'. exact Hq.
Qed.

(* A spill moves to a register map with the same base and a memory that keeps its 8 bytes. *)
Lemma w1_spill_mv : forall (regs R : bvmap 5 word) (m m' : word -> option byte) (A off v : Z),
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 448 ->
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs 9 ->
  KEEPR m m' (A + off) (A + off + 8) -> ACtlCutP.spill regs m off v -> ACtlCutP.spill R m' off v.
Proof.
  intros regs R m m' A off v H9 HA0 HA1 Ho0 Ho1 E9 K Hs.
  pose proof (w1_spill_at regs m A off v H9 HA0 HA1 Ho0 Ho1 Hs) as Hq.
  exists A. split; [unfold ACtlCut.rgv; rewrite E9; exact H9 |].
  exact (w1_q64_keep m m' (A + off) v K Hq).
Qed.

Lemma w1_spill_of : forall (R : bvmap 5 word) (m : word -> option byte) (A off v : Z),
  ACtlCut.rgv R 9 A -> ACtlCutP.q64 m (A + off) v -> ACtlCutP.spill R m off v.
Proof. intros R m A off v H9 Hq. exists A. split; [exact H9 | exact Hq]. Qed.

(* A run that leaves every byte of [lo, lo + N) readable (mrd Some) leaves some N bytes there (ACtlW5 w5_bytes_of_mrd). *)
Lemma w1_bytes_of_mrd : forall (m : word -> option byte) (N : nat) lo,
  0 <= lo -> lo + Z.of_nat N <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat N -> exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (lo + i)) = Some b) ->
  exists bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m lo bs /\ length bs = N.
Proof.
  intros m N. induction N as [|N IH]; intros lo H0 H1 Hb.
  - exists []. split; [|reflexivity]. split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (Hb 0 ltac:(lia)) as (b & Eb). rewrite Z.add_0_r in Eb.
    destruct (IH (lo + 1) ltac:(lia) ltac:(lia)) as (bs & (_ & _ & Hbs) & Hl).
    { intros i Hi. destruct (Hb (i + 1) ltac:(lia)) as (c & Ec). exists c. rewrite <- Ec. f_equal. f_equal. lia. }
    exists (b :: bs). split; [|cbn [length]; rewrite Hl; reflexivity].
    split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi; cbn [nth_error].
    + rewrite Z.add_0_r. exact Eb.
    + rewrite <- (Hbs i ltac:(cbn [length] in Hi; lia)). f_equal. f_equal. lia.
Qed.

(* The owned frame's 392 shadow bytes are readable at every journal state: they are present (AR's frame law,
   w1_frame), so no shadow_rw is read (route (C)). *)
Lemma w1_fsh_rd : forall (cx : ACtlCut.ctlcx) ly3 S3 W3 m md k (fr : Z),
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m md k -> Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) ->
  forall i, 0 <= i < 392 -> exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (ACtlCutP.Sfr fr + i)) = Some b.
Proof.
  intros cx ly3 S3 W3 m md k fr HJ Hfr Efr i Hi.
  destruct (w1_frame cx ly3 S3 W3 m md k HJ Hfr) as (_ & _ & _ & _ & _ & _ & Hfsh).
  rewrite <- Efr in Hfsh.
  destruct (Hfsh i ltac:(lia)) as (_ & b & Hb). exists b.
  assert (E : Reusable.YG0f.shadow_addr fr + i = ACtlCutP.Sfr fr + i)
    by (unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
          Reusable.YG0f.SHADOW_OFF; lia).
  rewrite E in Hb. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity.
Qed.

(* FRAC across a memory change and a register change: the registers 2 3 4 8 9 19 26, the spill words [A + 336] /
   [A + 48] / [A + 40], the frame's header and entry words [fr, fr + 24), the saved caller registers [c_sp - 104, c_sp)
   and the trailer word [fr + 4088, fr + 4096) are kept; the frame's shadow is any 392 readable bytes. *)
Lemma w1_frac_mv : forall (cx : ACtlCut.ctlcx) (fr sel A0 : Z) (regs R : bvmap 5 word) (m m' : word -> option byte),
  ACtlCut.rgv regs 9 A0 -> 0 <= A0 < 2 ^ 64 ->
  lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs 26 ->
  KEEPR m m' (A0 + 336) (A0 + 344) -> KEEPR m m' (A0 + 40) (A0 + 56) ->
  KEEPR m m' fr (fr + 24) ->
  (forall i, 0 <= i < 392 -> exists b, lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa (ACtlCutP.Sfr fr + i)) = Some b) ->
  KEEPR m m' (ACtlCut.c_sp cx - 104) (ACtlCut.c_sp cx) ->
  KEEPR m m' (fr + 4088) (fr + 4096) ->
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCutP.FRAC B cx fr sel R m'.
Proof.
  intros cx fr sel A0 regs R m m' H90 HA0 E2 E3 E4 E8 E9 E19 E26 K336 K40 KF KSP KSV KT
    (A & sp & H2 & H16 & Hsp & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA & HfrA & HA448 & Hsp4 &
     Hc & Q336 & Q48 & Q40 & Qfr & Q16 & (sh & Hsh & Hshl) & Hsv & Qtr).
  pose proof (w1_spZ_range regs) as Hspr. rewrite Hsp in Hspr.
  pose proof Hc as Hc'. unfold B.AsanRT.APPMEM_END in Hc'.
  assert (EA : A0 = A) by (apply (w1_rgv_eq regs 9); [exact H90 | exact H9 | lia | lia]). subst A0.
  exists A, sp.
  assert (Hlen : length (ACtlCutP.saved_bytes cx) = 104%nat).
  { unfold ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8. reflexivity. }
  pose proof (lib.Lib.Mem.bytes_at_bound _ _ _ _ Hsh) as Hshb. rewrite Hshl in Hshb.
  split; [rewrite E2; exact H2|]. split; [exact H16|].
  split; [unfold Reusable.YG0d.spZ; rewrite E2; exact Hsp|]. split; [rewrite E4; exact H4|].
  split; [exact (w1_rgv_move R regs 8 _ E8 H8)|]. split; [exact (w1_rgv_move R regs 9 _ E9 H9)|].
  split; [rewrite E3; exact H3|]. split; [exact (w1_rgv_move R regs 19 _ E19 H19)|].
  split; [exact (w1_rgv_move R regs 26 _ E26 H26)|].
  do 8 (split; [assumption|]).
  split; [apply (w1_q64_keep m m'); [intros a Ha; apply K336; lia | exact Q336]|].
  split; [apply (w1_q64_keep m m'); [intros a Ha; apply K40; lia | exact Q48]|].
  split; [apply (w1_q64_keep m m'); [intros a Ha; apply K40; lia | exact Q40]|].
  split; [apply (w1_q64_keep m m'); [intros a Ha; apply KF; lia | exact Qfr]|].
  split; [apply (w1_q64_keep m m'); [intros a Ha; apply KF; lia | exact Q16]|].
  split.
  { change (Z.to_nat ACtlCutP.FRAME_SHADOW) with 392%nat in *.
    destruct (w1_bytes_of_mrd m' 392 (ACtlCutP.Sfr fr) ltac:(lia) ltac:(lia)) as (sh' & Hsh' & Hl').
    { intros i Hi. exact (KSP i ltac:(lia)). }
    exists sh'. split; [exact Hsh' | exact Hl']. }
  split; [apply (w1_bytes_keep m m'); [rewrite Hlen; intros a Ha; apply KSV; lia | exact Hsv]|].
  apply (w1_q64_keep m m'); [intros a Ha; apply KT; lia | exact Qtr].
Qed.

(* FRAHC (the early cuts' carried part: no [A + 48] / [A + 40] spills, a header word parameter) likewise. *)
Lemma w1_frahc_mv : forall (cx : ACtlCut.ctlcx) (fr sel hdr A0 : Z) (regs R : bvmap 5 word) (m m' : word -> option byte),
  ACtlCut.rgv regs 9 A0 -> 0 <= A0 < 2 ^ 64 ->
  lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs 26 ->
  KEEPR m m' (A0 + 336) (A0 + 344) ->
  KEEPR m m' fr (fr + 24) ->
  (forall i, 0 <= i < 392 -> exists b, lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa (ACtlCutP.Sfr fr + i)) = Some b) ->
  KEEPR m m' (ACtlCut.c_sp cx - 104) (ACtlCut.c_sp cx) ->
  KEEPR m m' (fr + 4088) (fr + 4096) ->
  ACtlCutP.FRAHC B cx fr sel hdr regs m -> ACtlCutP.FRAHC B cx fr sel hdr R m'.
Proof.
  intros cx fr sel hdr A0 regs R m m' H90 HA0 E2 E3 E4 E8 E9 E19 E26 K336 KF KSP KSV KT
    (A & sp & H2 & H16 & Hsp & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA & HfrA & HA448 & Hsp4 &
     Hc & Q336 & Qfr & Q16 & (sh & Hsh & Hshl) & Hsv & Qtr).
  pose proof (w1_spZ_range regs) as Hspr. rewrite Hsp in Hspr.
  pose proof Hc as Hc'. unfold B.AsanRT.APPMEM_END in Hc'.
  assert (EA : A0 = A) by (apply (w1_rgv_eq regs 9); [exact H90 | exact H9 | lia | lia]). subst A0.
  exists A, sp.
  assert (Hlen : length (ACtlCutP.saved_bytes cx) = 104%nat).
  { unfold ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8. reflexivity. }
  pose proof (lib.Lib.Mem.bytes_at_bound _ _ _ _ Hsh) as Hshb. rewrite Hshl in Hshb.
  split; [rewrite E2; exact H2|]. split; [exact H16|].
  split; [unfold Reusable.YG0d.spZ; rewrite E2; exact Hsp|]. split; [rewrite E4; exact H4|].
  split; [exact (w1_rgv_move R regs 8 _ E8 H8)|]. split; [exact (w1_rgv_move R regs 9 _ E9 H9)|].
  split; [rewrite E3; exact H3|]. split; [exact (w1_rgv_move R regs 19 _ E19 H19)|].
  split; [exact (w1_rgv_move R regs 26 _ E26 H26)|].
  do 8 (split; [assumption|]).
  split; [apply (w1_q64_keep m m'); [intros a Ha; apply K336; lia | exact Q336]|].
  split; [apply (w1_q64_keep m m'); [intros a Ha; apply KF; lia | exact Qfr]|].
  split; [apply (w1_q64_keep m m'); [intros a Ha; apply KF; lia | exact Q16]|].
  split.
  { change (Z.to_nat ACtlCutP.FRAME_SHADOW) with 392%nat in *.
    destruct (w1_bytes_of_mrd m' 392 (ACtlCutP.Sfr fr) ltac:(lia) ltac:(lia)) as (sh' & Hsh' & Hl').
    { intros i Hi. exact (KSP i ltac:(lia)). }
    exists sh'. split; [exact Hsh' | exact Hl']. }
  split; [apply (w1_bytes_keep m m'); [rewrite Hlen; intros a Ha; apply KSV; lia | exact Hsv]|].
  apply (w1_q64_keep m m'); [intros a Ha; apply KT; lia | exact Qtr].
Qed.

(* A list of cells read as single bytes (R3.v r3_rw_C1) from one CB cell. *)
Lemma w1_rw_C1 : forall (m : word -> option byte) (A : Z) (n : nat) (bs : list byte),
  lib.Lib.Step.rw_cells B.Img0.rsegs m A (lib.Lib.Cells.CB n bs :: nil) -> length bs = n ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m A (map lib.Lib.Cells.C1 bs).
Proof.
  intros m A n bs ((_ & Hb) & Hw) Hl.
  cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hw. rewrite Nat.add_0_r in Hw.
  apply B.Prog.Seg.R3.r3_rw_C1; [exact Hb | rewrite Hl; exact Hw].
Qed.

(* ---- image data at a cut: RELRO bytes through the kept read-only view, read-only bytes through ro_agree ---- *)
Lemma w1_vis_img : forall (W : Reusable.YA0n.world segs) a, 0x10000 <= a < 0x5fe000 ->
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W a Ha. destruct (B.ProgBridge.img_vis_W W) as (_ & _ & H). apply H.
  unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI. lia.
Qed.

Lemma w1_relro_bytes : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (A : Z) (n : nat) bs,
  B.Prog.CtrlBase.arodata_okP segs RLO RHI B (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) ->
  RLO <= A -> A + Z.of_nat n <= RHI -> 0x10000 <= A -> A + Z.of_nat n <= 0x5fe000 ->
  (forall i, 0 <= i < Z.of_nat n ->
     ~ Exists (Reusable.YG0n.in_zr (A + i)) (Reusable.YG0f.as_owned_static B) /\
     ~ (Reusable.YG0f.as_errno B <= A + i < Reusable.YG0f.as_errno B + 4)) ->
  lib.Lib.Image.image_bytes B.Img0.rsegs A n = Some bs ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m A bs.
Proof.
  intros W m A n bs HP Hlo Hhi Hi0 Hi1 Hown Him.
  pose proof (lib.Lib.Image.image_bytes_length B.Img0.rsegs n A bs Him) as Hlen.
  split; [lia|]. split; [rewrite Hlen; lia|].
  intros i Hi. rewrite Hlen in Hi.
  destruct (Hown (Z.of_nat i) ltac:(lia)) as [Ho He].
  assert (Hro : Reusable.APostBase.in_roP segs RLO RHI (A + Z.of_nat i)) by (right; lia).
  pose proof (HP (A + Z.of_nat i) Hro Ho He) as E.
  rewrite (B.ProgWorld.aview_vis_mrd W m _ (w1_vis_img W (A + Z.of_nat i) ltac:(lia))) in E.
  pose proof (B.Prog.Seg.R5.r5_image_nth n A bs Him i Hi) as Hn.
  assert (E2 : option_map (fun b : byte => bv_unsigned b)
                 (lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (A + Z.of_nat i))) =
               option_map (fun b : byte => bv_unsigned b) (nth_error bs i)) by (rewrite <- Hn; exact E).
  unfold lib.Lib.Mem.wa.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (A + Z.of_nat i))) as [b'|] eqn:Eb,
           (nth_error bs i) as [b|] eqn:Ebs; cbn [option_map] in E2; try discriminate E2; [|reflexivity].
  injection E2 as E2. f_equal. apply bv_eq. exact E2.
Qed.

(* The image data the round trip carries (RBE / R6X): the CTRL_FRAMES rows 3 .. 9 and the turn's catalogue row are
   .data.rel.ro bytes (the writable segment's RELRO part), read through ctl_base's arodata_okS over [RLO, RHI); the
   box is read-only data (ro_agree).  RELRO_CAT places both tables in [RLO, RHI): [CAT, BA_FR + 240) =
   [0x9f620, 0xa06f0) inside .data.rel.ro [0x9f1a0, 0xa0890) (SlotModel.v:26).  Discharged at the top's RLO / RHI by
   computation. *)
Hypothesis RELRO_CAT : RLO <= ACtlCutP.SM.CAT /\
  ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length ACtlCutP.BAP.ba_tbl) <= RHI.

(* T10 (RtPost shared text, RTPOST-SHARED-B.txt (a working note, not in this delivery), token for token; owner a Theorem Labs lane). *)
Hypothesis ctl_relro_not_owned : forall a : Z,
  (B.ACtlCutP.BAC.BA_FR + 72 <= a < B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl) \/
   B.ACtlCutP.SM.CAT <= a < B.ACtlCutP.SM.CAT + B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N) ->
  ~ Exists (Reusable.YG0n.in_zr a) (Reusable.YG0f.as_owned_static B) /\
  ~ (Reusable.YG0f.as_errno B <= a < Reusable.YG0f.as_errno B + 4).

Lemma w1_tbl_bytes : forall (W : Reusable.YA0n.world segs) (m : word -> option byte),
  B.Prog.CtrlBase.arodata_okP segs RLO RHI B (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (ACtlCutP.BAC.BA_FR + 72) ACtlCutP.BAP.ba_tbl.
Proof.
  intros W m HP. pose proof RELRO_CAT as [Hl Hh].
  rewrite B.Prog.Seg.R7.r7_tbl_len in Hh.
  unfold ACtlCutP.SM.CAT, ACtlCutP.BAC.BA_FR in Hl, Hh. change (Z.of_nat 168) with 168 in Hh.
  apply (w1_relro_bytes W m _ 168 _ HP).
  - unfold ACtlCutP.BAC.BA_FR. lia.
  - unfold ACtlCutP.BAC.BA_FR. lia.
  - unfold ACtlCutP.BAC.BA_FR. lia.
  - unfold ACtlCutP.BAC.BA_FR. lia.
  - intros i Hi. apply ctl_relro_not_owned. left. rewrite B.Prog.Seg.R7.r7_tbl_len. lia.
  - exact B.Prog.Seg.R5.r5_tbl_img.
Qed.

Lemma w1_row_img : forall inp : list byte,
  lib.Lib.Image.image_bytes B.Img0.rsegs (ACtlCutP.SM.mrow inp) 296 = Some (ACtlCutP.SM.rt_mb inp).
Proof.
  intros inp.
  assert (Hi : 0 <= B.Prog.SlotModel.istar inp < 11)
    by (unfold B.Prog.SlotModel.istar, B.Prog.SlotModel.CAT_N; apply Z.mod_pos_bound; lia).
  assert (Hin11 : In (B.Prog.SlotModel.istar inp) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]) by (cbn [In]; lia).
  pose proof (proj1 (forallb_forall _ _) B.Prog.Seg.R5.r5_rows_img _ Hin11) as Hrw. cbv beta in Hrw.
  destruct (lib.Lib.Image.image_bytes B.Img0.rsegs
              (B.Prog.SlotModel.CAT + B.Prog.SlotModel.CAT_ROW * B.Prog.SlotModel.istar inp) 296) as [row|] eqn:Hrow;
    [|discriminate Hrw].
  change (ACtlCutP.SM.mrow inp) with (B.Prog.SlotModel.CAT + B.Prog.SlotModel.CAT_ROW * B.Prog.SlotModel.istar inp).
  rewrite Hrow. f_equal.
  change (ACtlCutP.SM.rt_mb inp) with (B.Prog.SlotModel.img
    (B.Prog.SlotModel.CAT + B.Prog.SlotModel.CAT_ROW * B.Prog.SlotModel.istar inp) 296).
  unfold B.Prog.SlotModel.img. rewrite Hrow. reflexivity.
Qed.

Lemma w1_row_bytes : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (inp : list byte),
  B.Prog.CtrlBase.arodata_okP segs RLO RHI B (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (ACtlCutP.SM.mrow inp) (ACtlCutP.SM.rt_mb inp).
Proof.
  intros W m inp HP. pose proof RELRO_CAT as [Hl Hh].
  pose proof (B.Prog.Seg.R7.r7_mrow_range inp) as Hm.
  rewrite B.Prog.Seg.R7.r7_tbl_len in Hh.
  unfold ACtlCutP.SM.CAT, ACtlCutP.BAC.BA_FR in Hl, Hh. change (Z.of_nat 168) with 168 in Hh.
  change ACtlCutP.SM.mrow with B.Prog.SlotModel.mrow.
  apply (w1_relro_bytes W m _ 296 _ HP).
  - lia.
  - change (Z.of_nat 296) with 296. lia.
  - lia.
  - change (Z.of_nat 296) with 296. lia.
  - intros i Hi. apply ctl_relro_not_owned. right.
    unfold ACtlCutP.SM.CAT, ACtlCutP.SM.CAT_ROW, ACtlCutP.SM.CAT_N.
    pose proof (Z.mod_pos_bound (B.Prog.SlotModel.mode inp / 2) 11 ltac:(lia)) as Hb.
    unfold B.Prog.SlotModel.mrow, B.Prog.SlotModel.istar, B.Prog.SlotModel.CAT, B.Prog.SlotModel.CAT_ROW,
      B.Prog.SlotModel.CAT_N in *.
    change (Z.of_nat 296) with 296 in Hi. lia.
  - exact (w1_row_img inp).
Qed.

Lemma w1_box_bytes : forall ly S (m : word -> option byte),
  B.ACtlRtC.ctl_rt_C B ly S m -> lib.Lib.Mem.bytes_at B.Img0.rsegs m ACtlCutP.SM.BOXA ACtlCutP.SM.box6.
Proof.
  intros ly S m (_ & _ & _ & HRO).
  apply (B.Prog.Seg.R5.r5_ro_bytes m ACtlCutP.SM.BOXA 6 ACtlCutP.SM.box6 HRO).
  - exact B.Prog.Seg.R5.r5_box_ro.
  - unfold ACtlCutP.SM.BOXA. lia.
  - unfold ACtlCutP.SM.BOXA. lia.
  - exact B.Prog.Seg.R5.r5_box_img.
Qed.

(* A bounded C string of the image is at most its bound long. *)
Lemma w1_cstr_len : forall k a, (length (ACtlCutP.SM.img_cstr a k) <= k)%nat.
Proof.
  induction k as [|k IH]; intros a; [cbn; lia|].
  cbn [ACtlCutP.SM.img_cstr].
  match goal with |- context [if ?c then _ else _] => destruct c end; cbn [length]; [lia|].
  specialize (IH (a + 1)). lia.
Qed.

(* rw_cells of present bytes (the journal's stack window, an owned frame): some byte list is there. *)
Lemma w1_rw_present : forall (H : word -> bool) (m : word -> option byte) (lo : Z) (N : nat),
  0 <= lo -> lo + Z.of_nat N <= 2 ^ 64 ->
  (forall a, lo <= a < lo + Z.of_nat N -> Reusable.YG0n.apresent H m a) ->
  exists bs, length bs = N /\ lib.Lib.Step.rw_cells B.Img0.rsegs m lo (lib.Lib.Cells.CB N bs :: nil).
Proof.
  intros H m lo N. revert lo. induction N as [|N IH]; intros lo H0 H1 Hp.
  - exists []. split; [reflexivity|].
    apply B.ProgWorld.rw_cells_CB_of_present; [reflexivity | exact H0 | exact H1 | intros i Hi; lia | intros i Hi; lia].
  - destruct (Hp lo ltac:(lia)) as (_ & b & Hb).
    destruct (IH (lo + 1) ltac:(lia) ltac:(lia)) as (bs & Hl & Hrw).
    { intros a Ha. apply Hp. lia. }
    exists (b :: bs). split; [cbn [length]; rewrite Hl; reflexivity|].
    destruct Hrw as ((_ & (_ & _ & Hbs)) & _).
    apply B.ProgWorld.rw_cells_CB_of_present.
    + cbn [length]. rewrite Hl. reflexivity.
    + exact H0.
    + exact H1.
    + intros [|i] Hi; cbn [nth_error].
      * rewrite Z.add_0_r. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
      * cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hbs. rewrite app_nil_r in Hbs.
        rewrite <- (Hbs i ltac:(lia)). unfold lib.Lib.Mem.wa. f_equal. f_equal. lia.
    + intros i Hi. destruct (Hp (lo + i) ltac:(lia)) as (_ & c & Hc). rewrite Hc. discriminate.
Qed.

(* ---- the world-call kit (lib/B/ACtlW2a.v's w2_cfg_back / w2_journal_mat / w2_frac_regs / w2_cur_regs / w2_pres_reg /
   w2_aview_of_apresent / w2_unsigned_of_signed / w2_range_addr_of_raw / w2_frac_mem / w2_kept_ro, renamed; the view
   read through the proved B.ProgWorld.aview_vis_mrd). ---- *)
Lemma w1_cfg_back : forall (W : Reusable.YA0n.world segs) (R : bvmap 5 word) (pc : Z) (mem : word -> option byte) md
    (Q : Reusable.YA0n.world segs -> config -> Prop),
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc R mem md) Q ->
  Reusable.YA0n.SRr segs W
    (mkCfg (lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem
              (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) md) Q.
Proof. intros W R pc mem md Q H. exact H. Qed.

Lemma w1_journal_mat : forall (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 md' k,
  AJ cx own ly3 S3 W3 mem3 md3 k -> Reusable.YK04.same_but_materialized md3 md' ->
  AJ cx own ly3 S3 W3 mem3 md' k.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 md' k HJ Hs.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS w1_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3 md'
           (fun _ => False) HJ).
  - intros x _. reflexivity.
  - intros x Hx. exact Hx.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a [].
Qed.

Lemma w1_frac_regs : forall (cx : ACtlCut.ctlcx) (fr sel : Z) (regs R : bvmap 5 word) (m : word -> option byte),
  lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs 26 ->
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCutP.FRAC B cx fr sel R m.
Proof.
  intros cx fr sel regs R m E2 E3 E4 E8 E9 E19 E26 H.
  unfold ACtlCutP.FRAC, ACtlCut.rgv, Reusable.YG0d.spZ in *.
  rewrite E2, E3, E4, E8, E9, E19, E26. exact H.
Qed.

Lemma w1_cur_regs : forall (cx : ACtlCut.ctlcx) (c : Z) (regs R : bvmap 5 word),
  lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs 23 ->
  lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs 25 ->
  ACtlCutP.CUR cx c regs -> ACtlCutP.CUR cx c R.
Proof.
  intros cx c regs R E23 E25 H. unfold ACtlCutP.CUR, ACtlCut.rgv in *. rewrite E23, E25. exact H.
Qed.

Lemma w1_pres_reg : forall (R R2 regs : bvmap 5 word) (z : Z) (r : bv 5),
  Reusable.YG0d.aregs_preserved R R2 -> Reusable.YG0d.acallee_saved z -> Z_to_bv 5 z = r ->
  lib.Reusable.YK11.getr R r = lib.Reusable.YK11.getr regs r ->
  lib.Reusable.YK11.getr R2 r = lib.Reusable.YK11.getr regs r.
Proof. intros R R2 regs z r HP Hz Er E. rewrite <- E. subst r. exact (HP z Hz). Qed.

Lemma w1_aview_of_apresent : forall (H : word -> bool) (mem : word -> option byte) (a : Z),
  Reusable.YG0n.apresent H mem a -> Reusable.YG0n.aview segs H mem a <> None.
Proof.
  intros H mem a (Hh & b & Hb). unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict.
  cbv beta. rewrite Hh, Hb. discriminate.
Qed.

Lemma w1_unsigned_of_signed : forall b : bv 8, 0 <= bv_signed b -> bv_unsigned b = bv_signed b.
Proof.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as Hr. revert Hb.
  unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256 in *.
  intros Hb. lia.
Qed.

Lemma w1_range_addr_of_raw : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (p n : Z),
  B.AsanRT.addressable mem p n ->
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false) ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) Reusable.YG0f.SHADOW_OFF p n.
Proof.
  intros W mem p n (H0 & H1 & H2 & H3) Hv x Hx.
  assert (Ex : p + (x - p) = x) by lia.
  destruct (H3 (x - p) ltac:(lia)) as (_ & b & Hb & Hok). rewrite Ex in Hb, Hok.
  pose proof (Hv (x - p) ltac:(lia)) as Hvx. rewrite Ex in Hvx.
  assert (Es : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x = B.AsanRT.shadow_addr x)
    by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  unfold B.AsanRT.shadow_ok in Hok.
  exists (bv_signed b). split.
  - rewrite Es, (B.ProgWorld.aview_vis_mrd W mem _ Hvx). unfold lib.Lib.Mem.wa in Hb. rewrite Hb. cbn [option_map].
    f_equal. apply w1_unsigned_of_signed. lia.
  - unfold Reusable.YG0v.saddr_ok. lia.
Qed.

(* A byte off the image is no read-only segment byte. *)
Lemma w1_ro_noimg : forall a, 0 <= a < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs a ->
  lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hn. unfold lib.Lib.Mem.ro_addr. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
  change B.Img0.rsegs with segs. rewrite (Reusable.YCbq.find_segment_none segs a Hn). reflexivity.
Qed.

(* ---- the normalized-memory lift and the footprint kit.  A run or a callee contract with a mem_inv premise runs on
   MemNorm.normalize of the cut memory (MemNorm.mem_inv_normalize); B.ProgWorld.rebase_ro_normalize carries the run
   back to the cut memory under ctl_rt's ro_agree (ProgWorld.v:806-812). ---- *)
Lemma w1_lift_n : forall (W : Reusable.YA0n.world segs) (regs : bvmap 5 word) (mem : word -> option byte) md (pc : Z)
    (RNG : Lib.ExecF.footprint) (P : machine_state -> Prop) (Q : Reusable.YA0n.world segs -> config -> Prop),
  B.MemNorm.ro_agree B.Img0.rsegs mem ->
  Lib.ExecF.evtF B.Img0.rsegs RNG P
    (lib.Lib.MState.MS (Lib.Regs6ss.mkR_of regs) lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None
       (B.MemNorm.normalize B.Img0.rsegs mem) (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) ->
  Reusable.YK04R.fp_avoids (Reusable.YA0n.w_H W) RNG ->
  (forall ms' md' s0, P s0 -> B.MemNorm.ms_rel B.Img0.rsegs ms' s0 ->
     (forall a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs (ms_mem ms') a bs <->
                   lib.Lib.Mem.bytes_at B.Img0.rsegs (ms_mem s0) a bs) ->
     (forall WR, lib.Lib.Frame.munch WR (B.MemNorm.normalize B.Img0.rsegs mem) (ms_mem s0) ->
                 lib.Lib.Frame.munch WR mem (ms_mem ms')) ->
     (lib.Lib.Frame.wmono B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem) (ms_mem s0) ->
      lib.Lib.Frame.wmono B.Img0.rsegs mem (ms_mem ms')) ->
     (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = mem x) ->
     Reusable.YK04.same_but_materialized md md' -> Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc regs mem md) Q.
Proof.
  intros W regs mem md pc RNG P Q Hro Hrun Hav K.
  pose proof (B.ProgWorld.rebase_ro_normalize RNG P _ _ _ _ _ mem _ Hro Hrun) as H2.
  apply (w1_lift W regs mem md pc RNG _ Q H2 Hav).
  intros ms' md' (s0 & HP & Hrel & _ & _ & _ & Hby & _ & Hmu & Hwm & _) Hhid Hsbm.
  exact (K ms' md' s0 HP Hrel Hby Hmu Hwm Hhid Hsbm).
Qed.

Lemma w1_ro_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 a) = false.
Proof. intros a Ha. exact (B.Prog.Seg.R3.r3_ro_wa a Ha). Qed.

(* An empty footprint range at a register value. *)
Lemma w1_rng0 : forall (H : word -> bool) (x : word), Lib.ExecF.rng (B.ProgBridge.RNG_W H) (bv_unsigned x - 0) 0.
Proof.
  intros H x. apply B.ProgBridge.rng_of_visible. pose proof (bv_unsigned_in_range 64 x) as R.
  change (bv_modulus 64) with (2 ^ 64) in R. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

(* Present bytes are byte-backed (stk). *)
Lemma w1_stk_pres : forall (H : word -> bool) (m : word -> option byte) lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> Reusable.YG0n.apresent H m a) -> lib.Lib.Frame.stk B.Img0.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (Hp a Ha) as (_ & b & Hb). split.
  - unfold wview, lib.Lib.Mem.wa. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity.
Qed.

(* win_sh_vis (lib/A/ProgWorldVisWin.v, a Theorem Labs lane; the proof reads only the core): the 8-aligned shadow word cover
   of a stack sub-range is visible, from the stack entry of zero_shadow_ranges through AR_zshadow_law. *)
Lemma w1_win_sh_vis : forall ly S (W : Reusable.YA0n.world segs) mem md lo len,
  Reusable.YG0n.AR segs B ly S W mem md ->
  Reusable.YG0f.ly_stk_lo ly <= lo -> lo + len <= Reusable.YG0f.ly_stk_hi ly -> 0 <= len ->
  len = 0 \/ B.ProgBridge.range_visible (Reusable.YA0n.w_H W)
               (B.Prog.rng_asan.sh_al8_lo lo) (B.Prog.rng_asan.sh_al8_hi lo len - B.Prog.rng_asan.sh_al8_lo lo).
Proof.
  intros ly S W mem md lo len HAR Hlo Hhi Hlen.
  destruct (Z.eq_dec len 0) as [E0 | Hne]; [left; exact E0 | right].
  pose proof (Reusable.YG0n.am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (Reusable.YG0f.lo_top ly HLY) as (_ & _ & _ & Lhi & Plo & Phi & Lbeg).
  pose proof (Reusable.YG0d.al_zshadow _ _ LAWS ly S W mem md
    (Reusable.YG0f.ly_stk_lo ly, Reusable.YG0f.ly_stk_hi ly - Reusable.YG0f.ly_stk_lo ly) HAR
    ltac:(unfold Reusable.YG0n.zero_shadow_ranges; left; reflexivity)) as HZ.
  cbn [fst snd] in HZ. unfold Reusable.YG0v.zero_shadow in HZ.
  unfold Reusable.YG0f.page_aligned, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.kHighMemEnd in *.
  unfold B.ProgBridge.range_visible, B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi,
    B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
  change (2 ^ 64) with 18446744073709551616.
  set (L := Reusable.YG0f.ly_stk_lo ly) in *.
  set (Hh := Reusable.YG0f.ly_stk_hi ly) in *.
  assert (EL : L = 4096 * (L / 4096)) by (pose proof (Z.div_mod L 4096 ltac:(lia)); lia).
  assert (EH : Hh = 4096 * (Hh / 4096)) by (pose proof (Z.div_mod Hh 4096 ltac:(lia)); lia).
  set (l := L / 4096) in *. set (h := Hh / 4096) in *.
  assert (EL8 : L / 8 = 512 * l)
    by (rewrite EL; replace (4096 * l) with (512 * l * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  assert (EHL8 : (Hh - L) / 8 = 512 * (h - l))
    by (rewrite EL, EH; replace (4096 * h - 4096 * l) with (512 * (h - l) * 8) by lia;
        rewrite Z.div_mul by lia; reflexivity).
  pose proof (Z.div_mod lo 8 ltac:(lia)) as D0. pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as D0'.
  pose proof (Z.div_mod (lo + len - 1) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (lo + len - 1) 8 ltac:(lia)) as D1'.
  pose proof (Z.div_mod (lo / 8 + 0x7fff8000) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (lo / 8 + 0x7fff8000) 8 ltac:(lia)) as D2'.
  pose proof (Z.div_mod ((lo + len - 1) / 8 + 0x7fff8000) 8 ltac:(lia)) as D3.
  pose proof (Z.mod_pos_bound ((lo + len - 1) / 8 + 0x7fff8000) 8 ltac:(lia)) as D3'.
  split; [lia |]. split; [lia |].
  intros a Ha.
  assert (HZa : Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a = Some 0).
  { replace a with (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF L +
                    (a - Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF L)) by lia.
    apply HZ. unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF.
    rewrite EL8, EHL8. lia. }
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict in HZa.
  destruct (Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:EHa; [exfalso | reflexivity].
  unfold lib.Reusable.YK11.seg_rom in HZa.
  rewrite (Reusable.YK04.memory_read1_hidden segs (Reusable.YA0n.w_H W) (Reusable.YA0n.w_Hoff W) _ EHa) in HZa.
  discriminate HZa.
Qed.

(* The shadow word cover of an interior range [fr + X, fr + X + N) of the owned frame is visible (its 512 shadow
   bytes are present, al_frames). *)
Lemma w1_frame_sh_vis : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (fr X N : Z),
  (forall i, 0 <= i < 512 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) m (Reusable.YG0f.shadow_addr fr + i)) ->
  0 <= fr -> fr + 4096 <= 2 ^ 47 -> fr mod 8 = 0 -> 56 <= X -> 0 < N -> X + N <= 4032 ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W)
    (B.Prog.rng_asan.sh_al8_lo (fr + X)) (B.Prog.rng_asan.sh_al8_hi (fr + X) N - B.Prog.rng_asan.sh_al8_lo (fr + X)).
Proof.
  intros W m fr X N Hsh H0 H1 H8 HX HN HXN.
  unfold B.ProgBridge.range_visible, B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi,
    B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hsh.
  split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros a Ha.
  assert (Hi : 0 <= a - (0x7fff8000 + fr / 8) < 512) by (Z.div_mod_to_equations; lia).
  pose proof (proj1 (Hsh _ Hi)) as Hv.
  replace (0x7fff8000 + fr / 8 + (a - (0x7fff8000 + fr / 8))) with a in Hv by lia.
  exact Hv.
Qed.

(* Route (C): the shadow word cover of an interior range [fr + X, fr + X + N) of an owned frame lies in the cut's own
   shadow (its (F) region: the frame's fs_frame_bytes / 8 shadow bytes). *)
Lemma w1_frame_cut_shadow : forall ly S (pos fr X N : Z),
  In (6, pos) (Reusable.YG01.frames S) -> Reusable.YG0f.frame_addr ly 6 pos = fr ->
  0 <= fr -> fr mod 8 = 0 -> 56 <= X -> 0 < N -> X + N <= 4032 ->
  forall a, B.Prog.rng_asan.sh_al8_lo (fr + X) <= a < B.Prog.rng_asan.sh_al8_hi (fr + X) N ->
  B.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S pos fr X N Hin Efa H0 H8 HX HN HXN a Ha. left. exists 6, pos. split; [exact Hin|].
  rewrite Efa. change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

(* The owned frame's shadow, written over ctrl's Sfr. *)
Lemma w1_shp : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (fr : Z),
  (forall i, 0 <= i < 512 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) m (Reusable.YG0f.shadow_addr fr + i)) ->
  forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) m a.
Proof.
  intros W m fr Hsh a Ha.
  assert (E : Reusable.YG0f.shadow_addr fr = ACtlCutP.Sfr fr)
    by (unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF;
        lia).
  pose proof (Hsh (a - ACtlCutP.Sfr fr) ltac:(lia)) as Hp. rewrite E in Hp.
  replace (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) with a in Hp by lia. exact Hp.
Qed.

(* The exact shadow range of [lo, lo + len) inside its 8-aligned shadow word cover. *)
Lemma w1_sh_exact : forall (H : word -> bool) (lo len : Z), 0 < len -> 0 <= lo ->
  B.ProgBridge.range_visible H (B.Prog.rng_asan.sh_al8_lo lo)
    (B.Prog.rng_asan.sh_al8_hi lo len - B.Prog.rng_asan.sh_al8_lo lo) ->
  B.ProgBridge.range_visible H (lo / 8 + B.AsanRT.ASAN_K) ((lo + len - 1) / 8 - lo / 8 + 1).
Proof.
  intros H lo len Hl H0 V. apply (B.ProgBridge.range_visible_sub _ _ _ _ _ V);
    unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K;
    Z.div_mod_to_equations; lia.
Qed.

(* reac_identity_init @0x81688 (S_R3) and reac_box_catalogue @0x815f8 (the S_A5 / S_R1 loop exit): route (C).  The
   universal contracts take shadow_rw (reac_identity_init_c.v:72, reac_box_catalogue_c.v:60), false at an AR state;
   the stages use the SHARED _on texts (a Theorem Labs lane), both PROVED, so neither is a hypothesis:
   - reac_box_catalogue: B.Prog.reac_box_catalogue_c.reac_box_catalogue_contract_F_on (c.v:137, shadow_rw premise
     dropped), PROVED as B.Prog.reac_box_catalogueF.reac_box_catalogue_F_holds_on (catalogueF.v:17).
   - reac_identity_init: B.Prog.reac_identity_init_c.reac_identity_init_contract_F_on (init_c.v:160; region
     reac_identity_init_shadow_R id = id <> 0 /\ sh_word_on id 38, post the forall-P transport), PROVED as the callee
     case B.Prog.reac_identity_initF.reac_identity_init_F_holds_on : asan_memset_contract_F_on -> .. (a Theorem Labs lane
     74be6b218f4), its callee by B.Prog.asan_memsetF_on.asan_memset_holds_F_on : memset_contract -> .. and that by
     B.Prog.memset.memset_holds. *)
Local Notation reac_identity_init_F_holds_on :=
  (B.Prog.reac_identity_initF.reac_identity_init_F_holds_on
     (B.Prog.asan_memsetF_on.asan_memset_holds_F_on B.Prog.memset.memset_holds)).

(* __asan_memset @0x81698 (S_R4): the core's memset rule at B's catalogue name (donor YG0d.v:317-335); the text is
   lib/B/ACtlW3a.v's AMEMSET token for token (the twin of lib/B/ACtlW2a.v's AMEMCPY). *)
Hypothesis AMEMSET :
  Reusable.YG0d.aintrin_realizes segs B Reusable.YG0d.OSet Reusable.YB1w.tfib_A_asan_memset.

(* __asan_set_shadow_00 @0x8163c (S_R2): ASF00, RtPost shared text (lib/B/RTPOST-SHARED-B.txt (a working note, not in this delivery), 08:02Z), token for
   token.  Owner a Theorem Labs lane; the top discharges it with B.Rt.SetShadow.ctrl_set_shadow_00P. *)
Hypothesis ASF00 : Reusable.SetShadowDefP.aset_shadow_realizesP segs B 0x55024 0.

(* ASF00 in journal form (the twin of YCbq.aj_intrin_at): from a journal state whose pinned registers make the call,
   the fill of [q, q + n) inside an owned frame's shadow returns at ra with the journal at the new memory (the write
   set is that shadow range, an in_frames range of the journal's own frames: YCbq.ajournal_after_write) and the
   rule's view facts. *)
Lemma w1_aj_set_shadow : forall (W : Reusable.YA0n.world segs) (regsT : bvmap 5 word) memT STK sp0 FP0 ly S W0
    mem md own lyc Sc mdc k (o : Z) raw cid pos q n,
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FP0 ly S W0 mem md own lyc Sc W memT mdc k ->
  In (cid, pos) own ->
  lib.Reusable.YK11.getr regsT 10 = Z_to_bv 64 q -> lib.Reusable.YK11.getr regsT 11 = Z_to_bv 64 n -> 0 < n ->
  Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr lyc cid pos) <= q ->
  q + n <= Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr lyc cid pos) + Reusable.YG00.fs_frame_bytes cid / 8 ->
  Reusable.YG0d.spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> Reusable.YG0d.ESTACK - o <= STK ->
  lib.Reusable.YK11.getr regsT 3 = Z_to_bv 64 (Reusable.YG0f.as_gp B) ->
  lib.Reusable.YK11.getr regsT 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B) ->
  lib.Reusable.YK11.getr regsT 1 = raw -> lib.Reusable.YK0s.ret_ok raw ->
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs 0x55024 regsT memT mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = Reusable.YG0d.cfg_at segs (Reusable.YG0d.raZ regsT) regs2 mem2 md2 /\
       Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FP0 ly S W0 mem md own lyc Sc W mem2 md2 k /\
       Reusable.YG0d.aregs_preserved regsT regs2 /\
       (forall i, 0 <= i < n -> Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem2 (q + i) = Some 0) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) ->
          Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem2 a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) memT a) /\
       (forall a, Reusable.YG0n.apresent (Reusable.YA0n.w_H W) memT a ->
          Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem2 a)).
Proof.
  intros W regsT memT STK sp0 FP0 ly S W0 mem md own lyc Sc mdc k o raw cid pos q n
    HJ Hown Ha0 Ha1 Hn Hq0 Hq1 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic &
                    F5 & HQT).
  assert (HPRE : Reusable.YG0d.ecall_pre segs B lyc Sc W regsT memT mdc).
  { eapply (Reusable.YCbq.ecall_pre_at segs B STK sp0 FP0 ly S W0 mem md own lyc Sc W memT mdc k regsT o);
      try eassumption. rewrite Hra. exact Hraw. }
  assert (Hin : In (cid, pos) (Reusable.YG01.frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  eapply Reusable.YA0n.SRr_mono.
  { exact (ASF00 lyc Sc W regsT memT mdc cid pos q n HPRE Hin Ha0 Ha1 Hn Hq0 Hq1). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hval & Hkeep & _ & Hpres2).
  split; [reflexivity|]. exists regs2, mem2, md2.
  split; [reflexivity|].
  split.
  { eapply (Reusable.YCbq.ajournal_after_write segs B LAWS w1_segs_low STK sp0 FP0 ly S W0 mem md own lyc Sc W memT
              mdc k mem2 md2 (fun a => q <= a < q + n) Sc own HJ).
    - intros a Ha Hna. exact (Hkeep a Ha Hna).
    - exact Hpres2.
    - exact Hsame.
    - intros a Ha. left. right; right; right. exists cid, pos. split; [exact Hown|]. right.
      unfold Reusable.YG0n.in_zr. cbn [fst snd]. lia.
    - exact HAR2.
    - reflexivity.
    - reflexivity.
    - lia.
    - exact Hfrs.
    - exact HQT. }
  split; [exact HP|]. split; [exact Hval|]. split; [exact Hkeep | exact Hpres2].
Qed.

(* The bytes of the owned frame are application memory (frames_bounds' in_app). *)
Lemma w1_frame_app : forall fr a, Reusable.YG0f.in_app fr 4096 -> fr <= a < fr + 4096 -> B.AsanRT.app_mem a.
Proof.
  intros fr a H Ha. pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [Hc _].
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in H.
  unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END.
  unfold Reusable.YG0f.ASAN_CEIL in *. lia.
Qed.

(* The journal's layout keeps the stack bounds of the entry layout (lib/B/ACtlW5.v w5_stk_ly). *)
Lemma w1_stk_ly : forall (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k,
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  Reusable.YG0f.ly_stk_lo ly3 + 32768 <= ACtlCut.c_sp cx /\ ACtlCut.c_sp cx <= Reusable.YG0f.ly_stk_hi ly3.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HJ.
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  destruct Hstk as (_ & _ & _ & Hlo & Hhi & _). rewrite Elo, Ehi. unfold Reusable.YCfn.LLVMF_STK in Hlo. lia.
Qed.

(* V6 (RtPost shared text, RTPOST-SHARED-B.txt (a working note, not in this delivery), token for token; owner a Theorem Labs lane). *)
Hypothesis ctl_names_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md (inp : list byte),
  Reusable.YG0n.AR segs B ly S W mem md ->
  B.ACtlCutP.RS6.has (B.ACtlCutP.SM.rt_mb inp) <> 0 -> B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb inp) <> 0 ->
  B.AsanRT.addressable mem (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb inp))
    (Z.of_nat (length (B.ACtlCutP.SM.rt_nb inp))).

(* The row-name clause of C_B8169c / RBE at any cut memory: the name's bytes are read-only image data (ro_agree;
   R4.v's per-row computation r4_rows_ok), its addressability is V6. *)
Lemma w1_name : forall ly S (W : Reusable.YA0n.world segs) (m : word -> option byte) md (inp : list byte),
  Reusable.YG0n.AR segs B ly S W m md -> B.ACtlRtC.ctl_rt_C B ly S m ->
  B.ACtlCutP.RS6.has (ACtlCutP.SM.rt_mb inp) <> 0 /\ B.ACtlCutP.RS6.rname (ACtlCutP.SM.rt_mb inp) <> 0 ->
  B.ACtlCutP.RBx.name_ok (ACtlCutP.SM.rt_nb inp) /\
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (B.ACtlCutP.RS6.rname (ACtlCutP.SM.rt_mb inp)) (ACtlCutP.SM.rt_nb inp) /\
  B.AsanRT.addressable m (B.ACtlCutP.RS6.rname (ACtlCutP.SM.rt_mb inp))
    (Z.of_nat (length (ACtlCutP.SM.rt_nb inp))) /\
  0 < B.ACtlCutP.RS6.rname (ACtlCutP.SM.rt_mb inp).
Proof.
  intros ly S W m md inp HAR (_ & _ & _ & HRO) (H1 & H2).
  pose proof (ctl_names_addressable ly S W m md inp HAR H1 H2) as HAD.
  unfold ACtlCutP.SM.rt_nb in *. unfold ACtlCutP.SM.rt_mb in *.
  assert (Hi : 0 <= ACtlCutP.SM.istar inp < 11)
    by (unfold ACtlCutP.SM.istar, ACtlCutP.SM.CAT_N; apply Z.mod_pos_bound; lia).
  assert (Hin : In (ACtlCutP.SM.istar inp) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]) by (cbn [In]; lia).
  pose proof (proj1 (forallb_forall _ _) B.Prog.Seg.R4.r4_rows_ok _ Hin) as Hb. unfold B.Prog.Seg.R4.r4_rowb in Hb.
  apply Bool.orb_true_iff in Hb as [Hb|Hb]; [apply Bool.orb_true_iff in Hb as [Hb|Hb]|].
  - apply Z.eqb_eq in Hb. contradiction.
  - apply Z.eqb_eq in Hb. contradiction.
  - unfold B.Prog.Seg.R4.r4_nmb in Hb.
    apply Bool.andb_true_iff in Hb as [Hb Him]. apply Bool.andb_true_iff in Hb as [Hb Hro].
    apply Bool.andb_true_iff in Hb as [Hb Hag]. apply Bool.andb_true_iff in Hb as [Hb Hgt].
    apply Bool.andb_true_iff in Hb as [Hok Hpos].
    apply Z.ltb_lt in Hpos. apply Z.leb_le in Hgt.
    split; [exact (B.Prog.Seg.R4.r4_nokb_ok _ Hok)|].
    split.
    + pose proof HAD as (_ & _ & Hae & _). unfold B.AsanRT.APPMEM_END in Hae.
      match goal with |- lib.Lib.Mem.bytes_at _ _ _ ?bs =>
        apply (B.Prog.Seg.R4.r4_ro_bytes m _ (length bs) _ HRO);
          [| lia | lia | exact (B.Prog.Seg.R4.r4_imgb_ok _ _ Him)] end.
      intros i Hi'. rewrite forallb_forall in Hro. apply Hro. apply in_seq. lia.
    + split; [exact HAD | exact Hpos].
Qed.

(* The walk's journal footprint: ACtl.v instantiates FP with [] (ACtl.v:186-187, `ctl_from ... []`); the input
   block's bytes are kept by the journal only off FP (YCbq.v:360-361).  Discharged by eq_refl at the top. *)
Hypothesis FP_nil : FP = [].

(* T5 (plan 2.4), derived (lib/B/ACtlW2a.v w2_block_addressable): a live block of the core's AR is addressable in
   ctrl's sense. *)
Lemma w1_block_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md (p n : Z),
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) -> 1 <= n ->
  B.AsanRT.addressable mem p n.
Proof.
  intros ly S W mem md p n HAR Hin Hn.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (Hp16 & Hp4 & Hceil & Happ & _ & _ & Hmax).
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [(Hp8 & _ & Hsh) _].
  assert (Er : Reusable.YG00.req_size n = n) by (unfold Reusable.YG00.req_size; destruct (n =? 0) eqn:E; lia).
  rewrite Er in Hceil, Happ, Hsh.
  pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [Hc _]. unfold Reusable.YG0f.ASAN_CEIL in Hc.
  split; [lia |]. split; [lia |]. split; [unfold B.AsanRT.APPMEM_END in *; lia |].
  intros i Hi. split.
  - unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END.
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Happ.
    lia.
  - assert (Hj : 0 <= i / 8 < (n + 7) / 8) by lia.
    pose proof (Hsh (i / 8) Hj) as Hv.
    assert (Es : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF p + i / 8 = B.AsanRT.shadow_addr (p + i)).
    { unfold Reusable.YG0v.shadow_of_addr, B.AsanRT.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.ASAN_K. lia. }
    rewrite Es in Hv.
    assert (Hvis : Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false).
    { destruct (Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i)))) eqn:Eh; [exfalso | reflexivity].
      unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict in Hv. cbv beta in Hv.
      rewrite Eh in Hv. cbv iota in Hv.
      unfold lib.Reusable.YK11.seg_rom, memory_read in Hv. change (Z.of_N 1) with 1 in Hv.
      rewrite (Reusable.YA0n.w_Hoff W _ Eh) in Hv. discriminate Hv. }
    rewrite (B.ProgWorld.aview_vis_mrd W mem _ Hvis) in Hv.
    destruct (lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i)))) as [bb |] eqn:Eb;
      [| discriminate Hv].
    cbn [option_map] in Hv. injection Hv as Hv. exists bb. split; [exact Eb |].
    pose proof (bv_unsigned_in_range 8 bb) as Hr. change (bv_modulus 8) with 256 in Hr.
    assert (Hs : bv_signed bb = bv_unsigned bb).
    { assert (Hlt : bv_unsigned bb < 128).
      { rewrite Hv. destruct (i / 8 <? n / 8); [lia |]. pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia. }
      unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
      rewrite Z.mod_small by lia. lia. }
    unfold B.AsanRT.shadow_ok. rewrite Hs, Hv.
    destruct (i / 8 <? n / 8) eqn:Ej; [left; reflexivity | right].
    apply Z.ltb_ge in Ej. lia.
Qed.

(* The input block at a cut: the core's pre gives its bytes at the entry (tfib_lib_pre_x's garr8, YCfn.v:37-38),
   the journal keeps the view of an entry block that is still live off FP = [] (YCbq.v:360-361), and
   B.ProgWorld.ctl_out_bytes reads the view back raw (a block byte is no image byte, al_client_img). *)
Lemma w1_input : forall (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k,
  CBASE cx -> AJ cx own ly3 S3 W3 mem3 md3 k ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (ACtlCut.c_p cx) (ACtlCut.c_in cx) /\
  (0 < ACtlCut.c_n cx -> B.AsanRT.addressable mem3 (ACtlCut.c_p cx) (ACtlCut.c_n cx)) /\
  0 <= ACtlCut.c_n cx < 2 ^ 26 /\
  (0 < ACtlCut.c_n cx -> In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)) /\
  0 <= ACtlCut.c_p cx /\ ACtlCut.c_p cx + ACtlCut.c_n cx <= 2 ^ 47.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ Hperm.
  pose proof HB as ((_ & _ & _ & _ & Hblk & Hlen & Hg & _) & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite FP_nil in F2.
  destruct Hblk as [[En Ep] | [Hn Hin0]].
  - assert (Ei : ACtlCut.c_in cx = []).
    { destruct (ACtlCut.c_in cx) as [|b l]; [reflexivity|]. cbn [length] in Hlen. lia. }
    rewrite Ei, Ep. unfold Reusable.YCfn.A_EMPTY.
    split; [split; [lia|]; split; [cbn [length Z.of_nat]; lia | intros i Hi; cbn [length] in Hi; lia]|].
    split; [intros Hn; lia|]. split; [lia|]. split; [intros Hn; lia|]. lia.
  - assert (Hin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin0).
    assert (Er : Reusable.YG00.req_size (ACtlCut.c_n cx) = ACtlCut.c_n cx)
      by (unfold Reusable.YG00.req_size; destruct (ACtlCut.c_n cx =? 0) eqn:E; lia).
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3) as (_ & Hp4 & Hceil & _ & _ & _ & _).
    rewrite Er in Hceil.
    pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [Hc _]. unfold Reusable.YG0f.ASAN_CEIL in Hc.
    split.
    + apply (B.ProgWorld.ctl_out_bytes W3 mem3 (ACtlCut.c_p cx) (ACtlCut.c_in cx)).
      * lia.
      * rewrite <- Hlen. lia.
      * intros i Hi Himg.
        assert (Hblk : exists p n, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) /\
                         p <= ACtlCut.c_p cx + Z.of_nat i < p + Reusable.YG00.req_size n)
          by (exists (ACtlCut.c_p cx), (ACtlCut.c_n cx); split; [exact Hin3 | rewrite Er; lia]).
        exact (proj2 (Reusable.YG0d.al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 _ HAR (or_introl Hblk)) Himg).
      * apply (lib.Reusable.YI00.garr8_frame segs _ _ _ _ Hg).
        intros a Ha. rewrite length_map, <- Hlen in Ha.
        pose proof (F2 (ACtlCut.c_p cx) (ACtlCut.c_n cx) (a - ACtlCut.c_p cx) Hin0 Hin3 ltac:(rewrite Er; lia)
                      (lib.Reusable.YI04.inFP_nil _)) as E.
        replace (ACtlCut.c_p cx + (a - ACtlCut.c_p cx)) with a in E by lia.
        unfold Reusable.YG0n.aview in E.
        destruct (lib.Reusable.YP09.mbyte segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W3) mem3) a) as [x|] eqn:Ex,
          (lib.Reusable.YP09.mbyte segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H (ACtlCut.c_W cx)) (ACtlCut.c_mem cx))
             a) as [y|] eqn:Ey;
          cbn [option_map] in E; try discriminate E; [|reflexivity].
        injection E as E. f_equal. apply bv_eq. exact E.
    + split; [intros _; exact (w1_block_addressable _ _ _ _ _ _ _ HAR Hin3 ltac:(lia))|].
      split; [lia|]. split; [intros _; exact Hin3|]. lia.
Qed.

(* ===========================================================================================================
   2. The stages. *)

(* ---------------------------------------------------------------------------------------------------------
   B81220 (0x81220, own6, k <= 0) --S_A4--> B81548_at [0].
   S_A4 (Seg/A4.v seg_A4 :739): A4F.a4_evt_F (0x81220 -> 0x81548): the last 137 of the 392 frame shadow bytes
   [S(fr) + 255, S(fr) + 392), the size test `srli a1,s2,26; beqz a1`, the our[] / cursor init and the frame-loop
   pointer spills [A + 56, A + 320).  The n >= 2^26 exit `j 0x82f2c` to Jrel is dead: ctl_base's pre gives
   n = 0 \/ 0 < n < 2^26 (tfib_lib_pre_x, YCfn.v:37), so the C_Jrel premise is unused.  The shadow byte 06 at
   S(fr) + 328 makes our[]'s six bytes addressable; the input bytes come from the journal (w1_input).  FRAHC is
   re-established at the new memory (w1_frahc_mv). *)
Lemma seg_A4 : forall POST,
  ctl_from POST (ix_cut C_B81548_at [0]) ->
  ctl_from POST C_Jrel ->
  ctl_from POST C_B81220.
Proof.
  intros POST H548 _ cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ACtlCutP.C_B81220 in HJ, Hfr, HFA, Hk, HBODY |- *.
  cbn [ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body ACtlCut.cut_pc] in HJ, Hfr, HFA, Hk, HBODY |- *.
  pose proof (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)) as Efr.
  destruct (w1_frame cx ly3 S3 W3 mem3 md3 k HJ Hfr) as (Hin & Efa & Hf0 & Hf1 & Happ & Hfb & Hfsh).
  rewrite <- Efr in Efa, Hf0, Hf1, Happ, Hfb, Hfsh.
  destruct (w1_stack cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hs0 & Hs47 & Hs16 & Hwin).
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  pose proof Happ as Happ'.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Happ'.
  pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [HcR _]. unfold Reusable.YG0f.ASAN_CEIL in HcR.
  pose proof (w1_shp W3 mem3 fr Hfsh) as Hshp.
  destruct HBODY as (Hperm & HFRAHC & HnMax & H20 & H21 & H24 & H25 & H22 & H18 & H27).
  pose proof HFRAHC as (A & sp & Esp & Hsp16 & EspZ & Etp & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
                        HfrA & HA448 & HSsp & HSapp & Q336 & Qhdr & Q16 & Hsh & Hsav & Qtr).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  pose proof (w1_spZ_range regs3) as Hspr. rewrite EspZ in Hspr.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (ESh : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000)
    by (unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; reflexivity).
  assert (ESA : forall X, 0 <= X -> B.AsanRT.shadow_addr (fr + 8 * X) = ACtlCutP.Sfr fr + X).
  { intros X HX. rewrite ESh. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
    replace (fr + 8 * X) with (fr + X * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (Hdisj : forall a, fr <= a < fr + 4096 -> a < ACtlCutP.Sfr fr \/ ACtlCutP.Sfr fr + 512 <= a).
  { intros a Ha. rewrite ESh. Z.div_mod_to_equations. lia. }
  destruct (w1_input cx _ ly3 S3 W3 mem3 md3 k HB HJ Hperm) as (_ & _ & Hn26 & _).
  destruct (w1_rw_present _ mem3 (ACtlCutP.Sfr fr + 255) 137 ltac:(lia) ltac:(lia)
              ltac:(intros a Ha; apply Hshp; lia)) as (j1 & _ & C1).
  destruct (w1_rw_present _ mem3 (A + 56) 264 ltac:(lia) ltac:(lia)
              ltac:(intros a Ha; apply Hwin; lia)) as (j2 & _ & C2).
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  eapply (w1_lift W3 regs3 mem3 md3 0x81220 RNG).
  { unfold Lib.Regs6ss.mkR_of.
    eapply (A4F.a4_evt_F RNG) with (junk1 := j1) (junk2 := j2).
    - match goal with |- context [bv_unsigned ?x + 255] =>
        replace (bv_unsigned x) with (ACtlCutP.Sfr fr)
          by (symmetry; exact (w1_rgv_unsigned regs3 19 _ E19 ltac:(rewrite ESh; lia))) end.
      exact C1.
    - match goal with |- context [bv_unsigned ?x + 56] =>
        replace (bv_unsigned x) with A by (symmetry; exact (w1_rgv_unsigned regs3 9 _ E9 ltac:(lia))) end.
      exact C2.
    - match goal with |- bv_unsigned ?x + 392 <= bv_unsigned ?y + 56 =>
        replace (bv_unsigned x) with (ACtlCutP.Sfr fr)
          by (symmetry; exact (w1_rgv_unsigned regs3 19 _ E19 ltac:(rewrite ESh; lia)));
        replace (bv_unsigned y) with A by (symmetry; exact (w1_rgv_unsigned regs3 9 _ E9 ltac:(lia))) end.
      rewrite ESh. Z.div_mod_to_equations. lia.
    - match goal with |- context [bv_unsigned ?x + 255] =>
        replace (bv_unsigned x) with (ACtlCutP.Sfr fr)
          by (symmetry; exact (w1_rgv_unsigned regs3 19 _ E19 ltac:(rewrite ESh; lia))) end.
      apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (Hshp a ltac:(lia))).
    - match goal with |- context [bv_unsigned ?x + 56] =>
        replace (bv_unsigned x) with A by (symmetry; exact (w1_rgv_unsigned regs3 9 _ E9 ltac:(lia))) end.
      apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (Hwin a ltac:(lia))). }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' (a0' & a1' & a2' & a3' & a6' & a7' & s4' & pc' & m' & cs1 & cs2 & -> & MU & WM & _ & _ & _ & _ & HX)
    Hhid Hsbm.
  match type of MU with lib.Lib.Frame.munch ((bv_unsigned ?x + _, _) :: (bv_unsigned ?y + _, _) :: nil) _ _ =>
    assert (U19 : bv_unsigned x = ACtlCutP.Sfr fr)
      by exact (w1_rgv_unsigned regs3 19 _ E19 ltac:(rewrite ESh; lia));
    assert (U9 : bv_unsigned y = A) by exact (w1_rgv_unsigned regs3 9 _ E9 ltac:(lia));
    rewrite U19, U9 in MU end.
  destruct HX as [(_ & Hbig) | (-> & _ & B328 & -> & -> & -> & -> & -> & -> & B144 & B112 & B312 & B264 & B56 &
                                B184 & B176 & B208 & B96 & B120 & B240 & B232 & B224 & B64 & B136 & B280 & B168 &
                                B192 & B200 & B216 & B104 & B288 & B296 & B304)].
  { exfalso. match type of Hbig with _ <= bv_unsigned ?x =>
      rewrite (w1_rgv_unsigned regs3 18 _ H18 ltac:(lia) : bv_unsigned x = ACtlCut.c_n cx) in Hbig end.
    lia. }
  match type of B144 with lib.Lib.Mem.bytes_at _ _ (bv_unsigned ?x + 144) (lib.Lib.Mem.le8 (Z_to_bv 64 (bv_unsigned ?y + _))) =>
    assert (U9b : bv_unsigned x = A) by exact (w1_rgv_unsigned regs3 9 _ E9 ltac:(lia));
    assert (U25 : bv_unsigned y = fr) by exact (w1_rgv_unsigned regs3 25 _ H25 ltac:(lia));
    rewrite U9b, U25 in * end.
  match type of B328 with lib.Lib.Mem.bytes_at _ _ (bv_unsigned ?x + 328) _ =>
    rewrite (w1_rgv_unsigned regs3 19 _ E19 ltac:(rewrite ESh; lia) : bv_unsigned x = ACtlCutP.Sfr fr) in B328 end.
  assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { apply (w1_journal_run cx _ ly3 S3 W3 mem3 md3 k m' md' _ HJ MU WM Hhid Hsbm).
    intros a Ha Hni. cbn [lib.Lib.Frame.outside] in Hni. split.
    - destruct (Z_lt_le_dec a (A + 56)) as [Hlt|Hge].
      + right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
        unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa.
        change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
        unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. rewrite ESh in Hni. lia.
      + left. unfold Reusable.YCfn.LLVMF_STK. lia.
    - intros Hi. apply w1_img in Hi. rewrite ESh in Hni. lia. }
  pose proof (w1_rt cx _ ly3 S3 W3 m' md' k HB HJ') as HRT'.
  destruct (w1_frame cx ly3 S3 W3 m' md' k HJ' Hfr) as (_ & _ & _ & _ & _ & Hfb' & _).
  rewrite <- Efr in Hfb'.
  assert (MK : forall lo hi, (forall a, lo <= a < hi -> 0 <= a < 2 ^ 64 /\
                   ~ (ACtlCutP.Sfr fr + 255 <= a < ACtlCutP.Sfr fr + 392) /\ ~ (A + 56 <= a < A + 320)) ->
                 KEEPR mem3 m' lo hi).
  { intros lo hi H. apply (w1_keep_munch _ mem3 m' lo hi MU). intros a Ha.
    destruct (H a Ha) as (H1 & H2 & H3). split; [exact H1|]. cbn [lib.Lib.Frame.outside].
    split; [lia|]. split; [lia | exact I]. }
  assert (KSP : forall i, 0 <= i < 392 ->
                  exists b, lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa (ACtlCutP.Sfr fr + i)) = Some b)
    by exact (w1_fsh_rd cx ly3 S3 W3 m' md' k fr HJ' Hfr Efr).
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R0 _ _ _ _ _ _) _) _ =>
    set (RT := R0) end.
  assert (G9 : lib.Reusable.YK11.getr RT 9 = lib.Reusable.YK11.getr regs3 9) by reflexivity.
  assert (R9 : ACtlCut.rgv RT 9 A) by (unfold ACtlCut.rgv; rewrite G9; exact E9).
  assert (SPO : forall off v, 0 <= off -> off + 8 <= 448 -> ACtlCutP.q64 m' (A + off) v -> ACtlCutP.spill RT m' off v)
    by (intros off v _ _ Hq; exact (w1_spill_of RT m' A off v R9 Hq)).
  apply (H548 cx [0] fr k ly3 S3 W3 RT m' md' HB HJ' Hfr HFA Hk).
  - unfold ACtlCut.ix_cut, ACtlCutP.C_B81548_at, ACtlCutP.ixz. cbn [ACtlCut.cut_body nth].
    split; [reflexivity|].
    split; [exact Hperm|].
    split.
    { apply (w1_frahc_mv cx fr fr 0x41b58ab3 A regs3 RT mem3 m' E9 ltac:(lia)); try reflexivity;
        [apply MK; intros a Ha; split; [lia|]; rewrite ESh; split; [Z.div_mod_to_equations; lia | lia] |
         apply MK; intros a Ha; split; [lia|]; destruct (Hdisj a ltac:(lia)); lia |
         exact KSP |
         apply MK; intros a Ha; split; [lia|]; rewrite ESh; split; [Z.div_mod_to_equations; lia | lia] |
         apply MK; intros a Ha; split; [lia|]; destruct (Hdisj a ltac:(lia)); lia |
         exact HFRAHC]. }
    split.
    { destruct (w1_input cx _ ly3 S3 W3 m' md' k HB HJ' Hperm) as (Hinb & Hina & _ & _).
      unfold ACtlCutP.LOOPB.
      split; [lia|]. split; [lia|].
      split; [exact (w1_rgv_move RT regs3 24 _ eq_refl H24)|].
      split; [exact (w1_rgv_move RT regs3 25 _ eq_refl H25)|].
      split; [apply SPO; [lia | lia | exact B144]|].
      split; [apply SPO; [lia | lia | exact B112]|].
      split; [apply SPO; [lia | lia | exact B312]|].
      split; [apply SPO; [lia | lia | exact B264]|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [unfold ACtlCut.rgv; rewrite Z.add_0_r;
              first [reflexivity |
                     (transitivity (Z_to_bv 64 (bv_unsigned (lib.Reusable.YK11.getr regs3 25) + 2624));
                      [reflexivity | rewrite (w1_rgv_unsigned regs3 25 _ H25 ltac:(lia)); reflexivity])]|].
      split; [reflexivity|].
      split; [unfold ACtlCut.rgv in *; rewrite Z.min_l by lia; rewrite Z.sub_0_r; exact H18|].
      split; [unfold ACtlCut.rgv in *; rewrite Z.min_l by lia; rewrite Z.add_0_r; exact H22|].
      split; [exact H27|].
      split; [apply SPO; [lia | lia | exact B56]|].
      split; [apply SPO; [lia | lia | exact B184]|].
      split; [apply SPO; [lia | lia | exact B176]|].
      split; [apply SPO; [lia | lia | exact B208]|].
      split.
      { apply (B.Prog.Seg.R3.r3_addr_r m' (fr + 2624) 6 (Z_to_bv 8 6));
          [lia | replace (fr + 2624) with (fr + 328 * 8) by lia; rewrite Z_mod_plus_full; exact Hfr8 | lia |
           reflexivity | unfold B.AsanRT.APPMEM_END; lia |
           intros i Hi; apply (w1_frame_app fr); [exact Happ | lia] |].
        replace (fr + 2624) with (fr + 8 * 328) by lia. rewrite (ESA 328 ltac:(lia)). exact B328. }
      split; [apply SPO; [lia | lia | exact B96]|].
      split; [apply SPO; [lia | lia | exact B120]|].
      split; [apply SPO; [lia | lia | exact B240]|].
      split; [apply SPO; [lia | lia | exact B232]|].
      split; [apply SPO; [lia | lia | exact B224]|].
      split; [apply SPO; [lia | lia | exact B64]|].
      split; [exact Hinb|].
      split; [exact Hina|].
      split.
      { destruct (w1_bytes_of_mrd m' 6 (fr + 2624) ltac:(lia) ltac:(lia)) as (bs & Hbs & Hl).
        { intros i Hi. destruct (proj1 (Hfb' (fr + 2624 + i) ltac:(lia))) as (_ & b & Hb).
          exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity. }
        exists bs. split; [exact Hl|]. cbn [Z.to_nat firstn app]. exact Hbs. }
      reflexivity. }
    unfold ACtlCutP.PRA.
    split; [apply SPO; [lia | lia | exact B136]|].
    split; [apply SPO; [lia | lia | exact B280]|].
    split; [apply SPO; [lia | lia | exact B168]|].
    split; [apply SPO; [lia | lia | exact B192]|].
    split; [apply SPO; [lia | lia | exact B200]|].
    split; [apply SPO; [lia | lia | exact B216]|].
    split; [apply SPO; [lia | lia | exact B104]|].
    split; [apply SPO; [lia | lia | exact B288]|].
    split; [apply SPO; [lia | lia | exact B296]|].
    split; [apply SPO; [lia | lia | exact B304]|].
    apply SPO; [lia | lia | exact B168].
  - exact HRT'.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The our[] loop (S_A5 / S_R1: head 0x81548, body 0x81550, latch `j 0x81548`, exit 0x815a0 .. 0x815f8). *)

(* V6 twin for the KIND_NAME table: RtPost shared text (lib/B/RTPOST-SHARED-B.txt (a working note, not in this delivery), token for token; owner
   a Theorem Labs lane).  C_B81cb0 carries `addressable m KNA.KIND_NAME 112`. *)
Hypothesis ctl_kind_name_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> B.AsanRT.addressable mem B.ACtlCutP.KNA.KIND_NAME 112.

(* A fake frame lies above the image: B.ProgWorld.ctl_frame_above_img_stmt, PROVED as lib/B/ProgWorld_Fs.v's
   ctl_frame_above_img (on a working branch line; a Theorem Labs lane's A proof from pw_F_above, B twin).  The catalogue call's
   pre-stretch asks 6283264 <= fr + 2656; the loop turns and S_R3 ask that the frame lies above the image. *)
Local Notation FRAME_ABOVE := (B.ProgWorld_Fs.ctl_frame_above_img (rc := rc) B).

(* A present byte stays present across a raw munch that does not name it. *)
Lemma w1_pres_munch : forall (H : word -> bool) (WR : list (Z * Z)) (m m' : word -> option byte) (a : Z),
  lib.Lib.Frame.munch WR m m' -> 0 <= a < 2 ^ 64 -> lib.Lib.Frame.outside WR a ->
  Reusable.YG0n.apresent H m a -> Reusable.YG0n.apresent H m' a.
Proof.
  intros H WR m m' a MU Ha Ho (Hh & b & Hb). split; [exact Hh|]. exists b.
  rewrite (MU (Z_to_bv 64 a)); [exact Hb|]. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Ho.
Qed.

(* A one-byte read of a known byte (lib/Lib's bytes_at_ov_read). *)
Lemma w1_ov1 : forall (m : word -> option byte) (a : Z) (b : byte),
  0 <= a < 2 ^ 64 -> lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a) = Some b ->
  ov_read_bytes B.Img0.rsegs m (lib.Lib.Mem.wa a) 1 = Some [b].
Proof.
  intros m a b Ha Hb.
  assert (HB : lib.Lib.Mem.bytes_at B.Img0.rsegs m a [b]).
  { split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros [|i] Hi; [|cbn [length] in Hi; lia].
    cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. exact Hb. }
  pose proof (lib.Lib.Mem.bytes_at_ov_read B.Img0.rsegs m a [b] 0 1 HB ltac:(cbn; lia)) as H.
  cbn [Z.of_nat firstn skipn] in H. rewrite Z.add_0_r in H. exact H.
Qed.

(* FRAC = FRAHC plus the exit spills [A + 48] = sel and [A + 40] = fr (ACtlCutP.v:911-946). *)
Lemma w1_frac_of_frahc : forall (cx : ACtlCut.ctlcx) (fr sel A0 : Z) (regs : bvmap 5 word) (m : word -> option byte),
  ACtlCutP.FRAHC B cx fr sel 0x41b58ab3 regs m -> ACtlCut.rgv regs 9 A0 -> 0 <= A0 < 2 ^ 64 ->
  ACtlCutP.q64 m (A0 + 48) sel -> ACtlCutP.q64 m (A0 + 40) fr -> ACtlCutP.FRAC B cx fr sel regs m.
Proof.
  intros cx fr sel A0 regs m (A & sp & H2 & H16 & Hsp & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
    HfrA & HA448 & Hsp4 & Hc & Q336 & Qfr & Q16 & Hsh & Hsv & Qtr) H90 HA0 Q48 Q40.
  pose proof (w1_spZ_range regs) as Hspr. rewrite Hsp in Hspr.
  pose proof Hc as Hc'. unfold B.AsanRT.APPMEM_END in Hc'.
  assert (EA : A0 = A) by (apply (w1_rgv_eq regs 9); [exact H90 | exact H9 | lia | lia]). subst A0.
  exists A, sp.
  exact (conj H2 (conj H16 (conj Hsp (conj H4 (conj H8 (conj H9 (conj H3 (conj H19 (conj H26 (conj Hfr32
          (conj HA32 (conj HAc (conj HspA (conj HfrA (conj HA448 (conj Hsp4 (conj Hc (conj Q336 (conj Q48 (conj Q40
          (conj Qfr (conj Q16 (conj Hsh (conj Hsv Qtr)))))))))))))))))))))))).
Qed.

(* The shadow bytes of a live block are visible (AR_shadow_law: the view reads them, so they are no hidden byte). *)
Lemma w1_block_shvis : forall ly S (W : Reusable.YA0n.world segs) mem md (p n : Z),
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) -> 1 <= n ->
  forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false.
Proof.
  intros ly S W mem md p n HAR Hin Hn i Hi.
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [(Hp8 & _ & Hsh) _].
  assert (Er : Reusable.YG00.req_size n = n) by (unfold Reusable.YG00.req_size; destruct (n =? 0) eqn:E; lia).
  rewrite Er in Hsh.
  assert (Hj : 0 <= i / 8 < (n + 7) / 8) by lia.
  pose proof (Hsh (i / 8) Hj) as Hv.
  assert (Es : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF p + i / 8 = B.AsanRT.shadow_addr (p + i)).
  { unfold Reusable.YG0v.shadow_of_addr, B.AsanRT.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.ASAN_K. lia. }
  rewrite Es in Hv.
  destruct (Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i)))) eqn:Eh; [exfalso | reflexivity].
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict in Hv. cbv beta in Hv.
  rewrite Eh in Hv. cbv iota in Hv.
  unfold lib.Reusable.YK11.seg_rom, memory_read in Hv. change (Z.of_N 1) with 1 in Hv.
  rewrite (Reusable.YA0n.w_Hoff W _ Eh) in Hv. discriminate Hv.
Qed.

(* The loop exit's carried body at 0x815a0 (after turn 5): LOOPB at t = 6 without a0 / a1 / a2 and the input
   facts (w1_input gives those), with our[] complete. *)
Definition w1_EXB (cx : ACtlCut.ctlcx) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  ACtlCut.rgv regs 24 fr /\ ACtlCut.rgv regs 25 fr /\
  ACtlCutP.spill regs m 144 (fr + 2176) /\ ACtlCutP.spill regs m 112 (fr + 2256) /\
  ACtlCutP.spill regs m 312 (fr + 544) /\ ACtlCutP.spill regs m 264 (fr + 2624) /\
  ACtlCut.rgv regs 20 (fr + 2656) /\ ACtlCut.rgv regs 17 (fr + 64) /\
  ACtlCut.rgv regs 18 (ACtlCut.c_n cx - Z.min 6 (ACtlCut.c_n cx)) /\
  ACtlCut.rgv regs 22 (ACtlCut.c_p cx + Z.min 6 (ACtlCut.c_n cx)) /\ ACtlCut.rgv regs 27 (ACtlCutP.Sfr fr + 68) /\
  ACtlCutP.spill regs m 56 (fr + 3040) /\ ACtlCutP.spill regs m 184 (fr + 2368) /\
  ACtlCutP.spill regs m 176 (fr + 2688) /\ ACtlCutP.spill regs m 208 (fr + 2768) /\
  B.AsanRT.addressable m (fr + 2624) 6 /\
  ACtlCutP.spill regs m 96 (ACtlCutP.decl_slot fr) /\ ACtlCutP.spill regs m 120 (fr + 2528) /\
  ACtlCutP.spill regs m 240 (fr + 2448) /\ ACtlCutP.spill regs m 232 (fr + 2464) /\
  ACtlCutP.spill regs m 224 (fr + 2496) /\ ACtlCutP.spill regs m 64 (fr + 3056) /\
  ACtlCutP.OURb cx fr m /\ ACtlCut.rgv regs 16 (fr + 32).

(* ---------------------------------------------------------------------------------------------------------
   The loop exit 0x815a0 .. (after turn 5), one footprint run from the exit state: A5F.b_tail_evt_F (the spills
   [A + 152] = fr + 64, [A + 160] = fr + 32, [A + 48] = sel, [A + 40] = fr; on left = 0 the stub to P3 0x81cb0),
   A5F.b_mode_evt_F (the mode byte in[6]; even: P3 0x81cb0; T02 0x815bc and the shadow check 0x815cc not taken:
   in[6] is addressable), A5F.b_cat_evt_pre_F_on (a Theorem Labs lane's route-(C) run, no shadow premise; the count cell's
   shadow S(fr) + 332 := 00, [fr + 2656] := 0, the call 0x815f8), the catalogue's shared _on contract, PROVED as
   B.Prog.reac_box_catalogueF.reac_box_catalogue_F_holds_on, at the callee, and A5F.b_cat_evt_post_F_on (0 steps at
   0x815fc).  The runs read and write the raw cut memory only (no mem_inv premise).
   P3 gets C_B81cb0's body and 0x815fc C_B815fc's; FRAC is re-established at the new memory (w1_frac_of_frahc after
   w1_frahc_mv). *)
Lemma w1_exit : forall POST (cx : ACtlCut.ctlcx) (fr k : Z) ly3 S3 W3 (R : bvmap 5 word) mem3 md3,
  ctl_from POST C_B815fc -> ctl_from POST C_B81cb0 ->
  CBASE cx -> AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  k <= 0 ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) ->
  ACtlCutP.FRAHC B cx fr fr 0x41b58ab3 R mem3 -> w1_EXB cx fr R mem3 -> ACtlCutP.PRA fr R mem3 ->
  B.ACtlRtC.ctl_rt_C B ly3 S3 mem3 ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x815a0 R mem3 md3) (POST cx).
Proof.
  intros POST cx fr k ly3 S3 W3 R mem3 md3 Hfc Hcb HB HJ Hfr HFA Hk Hperm HFRAHC HEX HPRA HRT.
  pose proof (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)) as Efr.
  destruct (w1_frame cx ly3 S3 W3 mem3 md3 k HJ Hfr) as (Hin & Efa & Hf0 & Hf1 & Happ & Hfb & Hfsh).
  rewrite <- Efr in Efa, Hf0, Hf1, Happ, Hfb, Hfsh.
  pose proof (FRAME_ABOVE ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (proj1 HJ) Hin) as Hfhi.
  rewrite Efa in Hfhi.
  destruct (w1_stack cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hs0 & Hs47 & Hs16 & Hwin).
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  pose proof Happ as Happ'.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Happ'.
  pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [HcR _]. unfold Reusable.YG0f.ASAN_CEIL in HcR.
  pose proof (w1_shp W3 mem3 fr Hfsh) as Hshp.
  destruct HEX as (H24 & H25 & S144 & S112 & S312 & S264 & H20 & H17 & H18 & H22 & H27 & S56 & S184 & S176 & S208 &
                   HA2624 & S96 & S120 & S240 & S232 & S224 & S64 & HOUR & H16).
  pose proof HFRAHC as (A & sp & Esp & Hsp16 & EspZ & Etp & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
                        HfrA & HA448 & HSsp & HSapp & Q336 & Qhdr & Q16 & Hsh & Hsav & Qtr).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  pose proof (w1_spZ_range R) as Hspr. rewrite EspZ in Hspr.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (ESh : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000)
    by (unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; reflexivity).
  assert (ESA : forall X, 0 <= X -> B.AsanRT.shadow_addr (fr + 8 * X) = ACtlCutP.Sfr fr + X).
  { intros X HX. rewrite ESh. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
    replace (fr + 8 * X) with (fr + X * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (Hsh_lo : 0x7fff8000 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 512 <= 2 ^ 46)
    by (rewrite ESh; Z.div_mod_to_equations; lia).
  pose proof HB as ((_ & _ & _ & _ & _ & Hlen & _) & _).
  destruct (w1_input cx _ ly3 S3 W3 mem3 md3 k HB HJ Hperm) as (Hinb & Hina & Hn26 & Hin3 & HP0 & HPN).
  set (N := ACtlCut.c_n cx) in *. set (P := ACtlCut.c_p cx) in *.
  pose proof HRT as (HAC & HSWc & HSWi & HRO).
  destruct (w1_rw_present _ mem3 (A + 40) 16 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply Hwin; lia))
    as (xs1 & Hx1 & CX1).
  destruct (w1_rw_present _ mem3 (A + 152) 16 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply Hwin; lia))
    as (xs2 & Hx2 & CX2).
  pose proof (w1_spill_at R mem3 A 56 (fr + 3040) E9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56) as Q56.
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (RVS : forall lo len, ACtlCut.c_sp cx - 32768 <= lo -> 0 <= len -> lo + len <= ACtlCut.c_sp cx ->
                  lib.Lib.ExecF.rng RNG lo len).
  { intros lo len H1 H2 H3. apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
    intros a Ha. exact (proj1 (Hwin a ltac:(lia))). }
  assert (RVF : forall lo len, fr <= lo -> 0 <= len -> lo + len <= fr + 4096 -> lib.Lib.ExecF.rng RNG lo len).
  { intros lo len H1 H2 H3. apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
    intros a Ha. exact (proj1 (proj1 (Hfb a ltac:(lia)))). }
  assert (RVSH : forall lo len, ACtlCutP.Sfr fr <= lo -> 0 <= len -> lo + len <= ACtlCutP.Sfr fr + 512 ->
                   lib.Lib.ExecF.rng RNG lo len).
  { intros lo len H1 H2 H3. apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
    intros a Ha. exact (proj1 (Hshp a ltac:(lia))). }
  assert (RVI : forall lo len, 0x10000 <= lo -> 0 <= len -> lo + len <= 0x5fe000 -> lib.Lib.ExecF.rng RNG lo len).
  { intros lo len H1 H2 H3. apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
    intros a Ha. apply w1_vis_img. lia. }
  (* the stack window's raw bytes, the frame's and its shadow's, off every write of the run *)
  assert (Hstk_sp : forall a, sp - 16 <= a < sp -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a)
    by (intros a Ha; apply Hwin; lia).
  assert (HRUN : lib.Lib.ExecF.evtF B.Img0.rsegs RNG
    (fun ms' =>
      (exists (R' : bvmap 5 word) (m' : word -> option byte),
         ms' = lib.Lib.MState.MS R' lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x81cb0) lib.Reusable.YK11.fp_csr None m'
                 (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
         lib.Reusable.YK11.getr R' 2 = lib.Reusable.YK11.getr R 2 /\
         lib.Reusable.YK11.getr R' 3 = lib.Reusable.YK11.getr R 3 /\
         lib.Reusable.YK11.getr R' 4 = lib.Reusable.YK11.getr R 4 /\
         lib.Reusable.YK11.getr R' 8 = lib.Reusable.YK11.getr R 8 /\
         lib.Reusable.YK11.getr R' 9 = lib.Reusable.YK11.getr R 9 /\
         lib.Reusable.YK11.getr R' 19 = lib.Reusable.YK11.getr R 19 /\
         lib.Reusable.YK11.getr R' 26 = lib.Reusable.YK11.getr R 26 /\
         lib.Reusable.YK11.getr R' 27 = lib.Reusable.YK11.getr R 27 /\
         lib.Reusable.YK11.getr R' 23 = Z_to_bv 64 (P + Z.min N 7) /\
         lib.Reusable.YK11.getr R' 25 = Z_to_bv 64 (N - Z.min N 7) /\
         lib.Reusable.YK11.getr R' 24 = Z_to_bv 64 (fr + 3040) /\
         lib.Lib.Frame.munch ((A + 40, A + 56) :: (A + 152, A + 168) :: nil) mem3 m' /\
         lib.Lib.Frame.wmono B.Img0.rsegs mem3 m' /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m' (A + 40) (lib.Lib.Mem.le8 (Z_to_bv 64 fr)) /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m' (A + 48) (lib.Lib.Mem.le8 (Z_to_bv 64 fr)) /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m' (A + 152) (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 64))) /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m' (A + 160) (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 32)))) \/
      (exists (R' : bvmap 5 word) (m' : word -> option byte),
         ms' = lib.Lib.MState.MS R' lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x815fc) lib.Reusable.YK11.fp_csr None m'
                 (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
         lib.Reusable.YK11.getr R' 2 = lib.Reusable.YK11.getr R 2 /\
         lib.Reusable.YK11.getr R' 3 = lib.Reusable.YK11.getr R 3 /\
         lib.Reusable.YK11.getr R' 4 = lib.Reusable.YK11.getr R 4 /\
         lib.Reusable.YK11.getr R' 8 = lib.Reusable.YK11.getr R 8 /\
         lib.Reusable.YK11.getr R' 9 = lib.Reusable.YK11.getr R 9 /\
         lib.Reusable.YK11.getr R' 19 = lib.Reusable.YK11.getr R 19 /\
         lib.Reusable.YK11.getr R' 20 = lib.Reusable.YK11.getr R 20 /\
         lib.Reusable.YK11.getr R' 26 = lib.Reusable.YK11.getr R 26 /\
         lib.Reusable.YK11.getr R' 27 = lib.Reusable.YK11.getr R 27 /\
         lib.Reusable.YK11.getr R' 10 = Z_to_bv 64 B.Prog.reac_box_catalogue_c.BOX_CATALOGUE /\
         lib.Reusable.YK11.getr R' 22 = Z_to_bv 64 (ACtlCutP.SM.mode (ACtlCut.c_in cx)) /\
         lib.Reusable.YK11.getr R' 23 = Z_to_bv 64 (P + 7) /\
         lib.Reusable.YK11.getr R' 25 = Z_to_bv 64 (N - 7) /\ 7 <= N /\
         lib.Lib.Frame.munch ((A + 40, A + 56) :: (A + 152, A + 168) :: (ACtlCutP.Sfr fr + 332, ACtlCutP.Sfr fr + 333) ::
                              (fr + 2656, fr + 2664) :: (sp - 16, sp) :: nil) mem3 m' /\
         lib.Lib.Frame.wmono B.Img0.rsegs mem3 m' /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m' (A + 40) (lib.Lib.Mem.le8 (Z_to_bv 64 fr)) /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m' (A + 48) (lib.Lib.Mem.le8 (Z_to_bv 64 fr)) /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m' (A + 152) (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 64))) /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m' (A + 160) (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 32))) /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m' (fr + 2656) (lib.Lib.Mem.le8 (Z_to_bv 64 11))))
    (lib.Lib.MState.MS (Lib.Regs6ss.mkR_of R) lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x815a0) lib.Reusable.YK11.fp_csr
       None mem3 (lib.Lib.PropExec.seg_rom B.Img0.rsegs))).
  { unfold Lib.Regs6ss.mkR_of.
    eapply (lib.Lib.ExecF.evtF_cut B.Img0.rsegs RNG).
    { eapply (A5F.b_tail_evt_F RNG) with (Ab := A) (q := P + Z.min 6 N) (w := N - Z.min 6 N) (frv := fr)
        (a6v := fr + 32) (a7v := fr + 64) (selv := fr) (v56 := fr + 3040) (xs1 := xs1) (xs2 := xs2).
      - exact E9.
      - exact H18.
      - exact H22.
      - exact H25.
      - exact H16.
      - exact H17.
      - exact H24.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - exact Hx1.
      - exact Hx2.
      - exact CX1.
      - exact CX2.
      - apply B.Prog.Seg.R4.r4_ro8. exact Q56.
      - apply RVS; lia.
      - apply RVS; lia.
      - apply RVS; lia. }
    intros ms1 (m1 & MU1 & WM1 & B40 & B48 & B152 & B160 & [(Ew & R1 & E1 & G2 & G3 & G4 & G8 & G9 & G19 & G26 & G27 &
                                                                 G23 & G25 & G24) | (Nw & E1)]).
    - (* left = 0 (n <= 6): the stub to P3 *)
      apply lib.Lib.ExecF.evtF_done. left. exists R1, m1. split; [exact E1|].
      split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G8|].
      split; [etransitivity; [exact G9 | symmetry; exact E9]|]. split; [exact G19|]. split; [exact G26|].
      split; [exact G27|].
      split; [etransitivity; [exact G23 | f_equal; lia]|]. split; [etransitivity; [exact G25 | f_equal; lia]|].
      split; [exact G24|].
      split; [exact MU1|]. split; [exact WM1|].
      split; [exact B40|]. split; [exact B48|]. split; [exact B152 | exact B160].
    - (* left <> 0 (n >= 7): the mode byte *)
      subst ms1.
      assert (HN7 : 7 <= N) by lia.
      replace (Z.min 6 N) with 6 by lia.
      pose proof (Hina ltac:(lia)) as (_ & _ & _ & Hadd).
      destruct (Hadd 6 ltac:(lia)) as (Happ6 & km & Hkm & Hok).
      assert (HinN : 0 < N) by lia.
      pose proof (Hin3 HinN) as HinB.
      destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ (proj1 HJ) HinB)
        as (_ & Hp4 & Hpc & _ & Hpbytes & _ & _).
      assert (Er : Reusable.YG00.req_size N = N)
        by (unfold Reusable.YG00.req_size; destruct (N =? 0) eqn:E; lia).
      rewrite Er in Hpc, Hpbytes.
      assert (HP6 : P + 6 < A + 40) by lia.
      assert (Hkm1 : lib.Lib.Mem.mrd B.Img0.rsegs m1 (Z_to_bv 64 (B.AsanRT.shadow_addr (P + 6))) = Some km).
      { rewrite <- Hkm.
        apply (w1_keep_munch _ mem3 m1 (B.AsanRT.shadow_addr (P + 6)) (B.AsanRT.shadow_addr (P + 6) + 1) MU1); [|lia].
        intros a Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha. split; [Z.div_mod_to_equations; lia|].
        cbn [lib.Lib.Frame.outside]. split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia | exact I]. }
      assert (Hbm1 : lib.Lib.Mem.mrd B.Img0.rsegs m1 (Z_to_bv 64 (P + 6)) =
                     Some (lib.Prog.RcIdentModel.nthb (ACtlCut.c_in cx) 6)).
      { rewrite (w1_keep_munch _ mem3 m1 (P + 6) (P + 7) MU1)
          by (first [lia | (intros a Ha; split; [lia|]; cbn [lib.Lib.Frame.outside]; split; [lia|];
                            split; [lia | exact I])]).
        destruct Hinb as (_ & _ & Hbi). pose proof (Hbi 6%nat ltac:(lia)) as E. change (Z.of_nat 6) with 6 in E.
        unfold lib.Lib.Mem.wa in E. rewrite E.
        unfold lib.Prog.RcIdentModel.nthb. apply nth_error_nth'. lia. }
      eapply (lib.Lib.ExecF.evtF_cut B.Img0.rsegs RNG).
      { eapply (A5F.b_mode_evt_F RNG) with (Ab := A) (q := P + 6) (w := N - 6) (K := B.AsanRT.ASAN_K)
          (v56 := fr + 3040) (bm := lib.Prog.RcIdentModel.nthb (ACtlCut.c_in cx) 6) (km := km).
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - exact E26.
        - lia.
        - lia.
        - lia.
        - lia.
        - lia.
        - lia.
        - unfold B.AsanRT.ASAN_K. lia.
        - unfold B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
        - apply w1_ov1; [unfold B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia | exact Hkm1].
        - unfold B.AsanRT.shadow_ok in Hok. lia.
        - apply w1_ov1; [lia | exact Hbm1].
        - apply B.Prog.Seg.R4.r4_ro8. apply (w1_bytes_keep mem3 m1); [|exact Q56].
          rewrite lib.Lib.Mem.length_le8. change (Z.of_nat 8) with 8.
          apply (w1_keep_munch _ mem3 m1 _ _ MU1). intros a Ha. split; [lia|].
          cbn [lib.Lib.Frame.outside]. split; [lia|]. split; [lia | exact I].
        - apply B.ProgBridge.rng_of_visible. split; [unfold B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
          split; [unfold B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
          intros a Ha. replace a with (B.AsanRT.shadow_addr (P + 6))
            by (unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *; lia).
          exact (w1_block_shvis _ _ _ _ _ _ _ (proj1 HJ) HinB ltac:(lia) 6 ltac:(lia)).
        - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
          intros a Ha. exact (proj1 (proj1 (Hpbytes a ltac:(lia)))).
        - apply RVS; lia. }
      intros ms2 [(Hev & R2 & E2 & G2 & G3 & G4 & G8 & G9 & G19 & G26 & G27 & G23 & G25 & G24) |
                  (Hodd & x0 & x1 & E2)].
      + (* even mode: P3 *)
        apply lib.Lib.ExecF.evtF_done. left. exists R2, m1. split; [exact E2|].
        split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G8|].
        split; [etransitivity; [exact G9 | symmetry; exact E9]|]. split; [exact G19|]. split; [exact G26|].
        split; [exact G27|].
        split; [etransitivity; [exact G23 | f_equal; lia]|]. split; [etransitivity; [exact G25 | f_equal; lia]|].
        split; [exact G24|].
        split; [exact MU1|]. split; [exact WM1|].
        split; [exact B40|]. split; [exact B48|]. split; [exact B152 | exact B160].
      + (* odd mode: the catalogue call *)
        subst ms2.
        destruct (w1_rw_present (Reusable.YA0n.w_H W3) m1 (ACtlCutP.Sfr fr + 332) 1 ltac:(lia) ltac:(lia)
                    ltac:(intros a Ha; apply (w1_pres_munch _ _ mem3 m1 a MU1);
                          [lia | cbn [lib.Lib.Frame.outside]; split; [lia|]; split; [lia | exact I] |
                           apply Hshp; lia]))
          as (sh1 & Hsh1 & CSH).
        destruct (w1_rw_present (Reusable.YA0n.w_H W3) m1 (fr + 2656) 8 ltac:(lia) ltac:(lia)
                    ltac:(intros a Ha; apply (w1_pres_munch _ _ mem3 m1 a MU1);
                          [lia | cbn [lib.Lib.Frame.outside]; split; [lia|]; split; [lia | exact I] |
                           exact (proj1 (Hfb a ltac:(lia)))]))
          as (cs & Hcs & CC).
        assert (ST1 : lib.Lib.Frame.stk B.Img0.rsegs m1 (sp - 16) sp).
        { apply (w1_stk_pres (Reusable.YA0n.w_H W3)); [lia | lia |].
          intros a Ha. apply (w1_pres_munch _ _ mem3 m1 a MU1); [lia | | exact (Hstk_sp a Ha)].
          cbn [lib.Lib.Frame.outside]. split; [lia|]. split; [lia | exact I]. }
        assert (AC1 : B.AsanRT.asan_cells m1).
        { apply (B.AsanRTFacts.asan_cells_kept _ mem3 m1 HAC MU1). cbn [lib.Lib.Frame.disjoint_from].
          unfold B.AsanRT.RT_LO, B.AsanRT.RT_HI. split; [lia|]. split; [lia | exact I]. }
        (* route (C): the catalogue's shared _on contract reads no shadow_rw, and the shared _on runs take none. *)
        eapply (lib.Lib.ExecF.evtF_cut B.Img0.rsegs RNG).
        { eapply (B.Prog.Seg.A5F.b_cat_evt_pre_F_on RNG) with (Sh := ACtlCutP.Sfr fr) (c := fr + 2656) (spv := sp)
            (sh1 := sh1) (cs := cs).
          - exact Esp.
          - exact E19.
          - exact H20.
          - lia.
          - replace (fr + 2656) with (fr + 332 * 8) by lia. rewrite Z_mod_plus_full. exact Hfr8.
          - lia.
          - lia.
          - lia.
          - left. lia.
          - destruct Happ' as [_ [Hl | Hh]]; [left | right]; rewrite ESh; Z.div_mod_to_equations; lia.
          - right. lia.
          - replace (fr + 2656) with (fr + 8 * 332) by lia. exact (ESA 332 ltac:(lia)).
          - intros i Hi. apply (w1_frame_app fr); [exact Happ | lia].
          - intros a Ha. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END.
            right. lia.
          - exact Hsh1.
          - exact Hcs.
          - exact CSH.
          - exact CC.
          - exact ST1.
          - exact AC1.
          - apply RVSH; lia.
          - apply RVF; lia. }
        intros ms3 (mc & Ec3 & MU3 & WM3 & BZ332 & BZc & ST3 & AC3 & SW3 & WR3 & AD3). subst ms3.
        eapply (lib.Lib.ExecF.evtF_cut B.Img0.rsegs RNG).
        { eapply (B.Prog.reac_box_catalogueF.reac_box_catalogue_F_holds_on RNG) with (c := fr + 2656) (lo := sp - 16);
            unfold B.Prog.reac_box_catalogue_c.REAC_BOX_CATALOGUE_FRAME;
            try (match goal with |- context [bv_unsigned ?x] =>
                   replace (bv_unsigned x) with sp by (symmetry; exact (w1_rgv_unsigned R 2 sp Esp ltac:(lia))) end).
          - exact H20.
          - exact ST3.
          - lia.
          - exact AC3.
          - intros x Hx. unfold B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END,
              B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx.
            cbn [lib.Lib.Frame.outside]. split; [lia|]. split; [lia | exact I].
          - right. split; [replace (fr + 2656) with (fr + 332 * 8) by lia; rewrite Z_mod_plus_full; exact Hfr8|].
            split; [exact WR3|]. split; [left; lia | exact AD3].
          - apply RVS; lia.
          - apply RVI; unfold B.AsanRT.GOT_CELL_K; lia.
          - apply RVI; unfold B.AsanRT.CELL_K; lia.
          - intros _. split; [apply RVF; lia|].
            replace (B.AsanRT.shadow_addr (fr + 2656)) with (ACtlCutP.Sfr fr + 332)
              by (symmetry; replace (fr + 2656) with (fr + 8 * 332) by lia; exact (ESA 332 ltac:(lia))).
            replace (B.AsanRT.shadow_addr (fr + 2656 + 7)) with (ACtlCutP.Sfr fr + 332)
              by (rewrite ESh; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia).
            apply RVSH; lia. }
        intros ms4 (a1' & a2' & m4 & E4 & MU4 & WM4 & _ & ST4 & HC4). subst ms4.
        unfold B.Prog.reac_box_catalogue_c.REAC_BOX_CATALOGUE_FRAME in MU4.
        match type of MU4 with lib.Lib.Frame.munch ((bv_unsigned ?x - _, _) :: _) _ _ =>
          replace (bv_unsigned x) with sp in MU4, ST4 by (symmetry; exact (w1_rgv_unsigned R 2 sp Esp ltac:(lia))) end.
        replace (fr + 2656 =? 0) with false in HC4 by (symmetry; apply Z.eqb_neq; lia).
        replace (lib.Lib.MState.ret_pc (Z_to_bv 64 0x815fc)) with (Z_to_bv 64 0x815fc)
          by (symmetry; apply lib.Lib.MState.ret_pc_even; [lia | reflexivity]).
        eapply (lib.Lib.ExecF.evtF_cut B.Img0.rsegs RNG).
        { eapply (B.Prog.Seg.A5F.b_cat_evt_post_F_on RNG) with (m := m1) (mc := mc) (m2 := m4)
            (Sh := ACtlCutP.Sfr fr) (c := fr + 2656) (spv := sp).
          - exact Esp.
          - destruct Happ' as [_ [Hl | Hh]]; [left | right]; rewrite ESh; Z.div_mod_to_equations; lia.
          - right. lia.
          - intros i Hi. apply (w1_frame_app fr); [exact Happ | lia].
          - intros a Ha. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END.
            right. lia.
          - exact MU3.
          - exact WM3.
          - exact BZ332.
          - exact MU4.
          - exact WM4.
          - exact ST4.
          - exact HC4. }
        intros ms5 (R5 & m5 & E5 & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G22 & G23 & G24 & G25 & G26 & G27 & G10 &
                    MU5 & WM5 & _ & _ & HC11 & _).
        apply lib.Lib.ExecF.evtF_done. right. exists R5, m5. split; [exact E5|].
        split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G8|].
        split; [etransitivity; [exact G9 | symmetry; exact E9]|]. split; [exact G19|]. split; [exact G20|].
        split; [exact G26|].
        split; [exact G27|]. split; [exact G10|].
        split.
        { etransitivity; [exact G22|]. unfold lib.Lib.Mem.zxb. f_equal.
          unfold ACtlCutP.SM.mode, B.Prog.SlotModel.mode, B.Prog.SlotModel.inb, B.Prog.SlotModel.nlen.
          replace (7 <=? Z.of_nat (length (ACtlCut.c_in cx))) with true by (symmetry; apply Z.leb_le; lia).
          reflexivity. }
        split; [etransitivity; [exact G23 | f_equal; lia]|]. split; [etransitivity; [exact G25 | f_equal; lia]|].
        split; [exact HN7|].
        assert (MUA : lib.Lib.Frame.munch ((A + 40, A + 56) :: (A + 152, A + 168) ::
                        (ACtlCutP.Sfr fr + 332, ACtlCutP.Sfr fr + 333) :: (fr + 2656, fr + 2664) :: (sp - 16, sp) :: nil)
                        mem3 m5).
        { apply (lib.Lib.Frame.munch_trans _ mem3 m1 m5).
          - refine (lib.Lib.Frame.munch_weaken _ _ mem3 m1 _ MU1).
            intros x Hx; cbn [lib.Lib.Frame.outside] in Hx |- *; intuition lia.
          - refine (lib.Lib.Frame.munch_weaken _ _ m1 m5 _ MU5).
            intros x Hx; cbn [lib.Lib.Frame.outside] in Hx |- *; intuition lia. }
        split; [exact MUA|]. split; [exact (lib.Lib.Frame.wmono_trans _ _ _ _ WM1 WM5)|].
        assert (KT : forall a bs, A + 40 <= a -> a + Z.of_nat (length bs) <= A + 168 ->
                       lib.Lib.Mem.bytes_at B.Img0.rsegs m1 a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m5 a bs).
        { intros a bs H1 H2 Hb. apply (lib.Lib.Frame.bytes_at_transport B.Img0.rsegs _ m1 m5 a bs Hb MU5).
          cbn [lib.Lib.Frame.disjoint_from]. repeat split; lia. }
        split; [apply KT; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact B40]|].
        split; [apply KT; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact B48]|].
        split; [apply KT; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact B152]|].
        split; [apply KT; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact B160]|].
        exact HC11. }
  (* lift the run and close at P3 or at 0x815fc *)
  eapply (w1_lift W3 R mem3 md3 0x815a0 RNG _ (POST cx) HRUN (B.ProgBridge.fp_avoids_RNG_W _)).
  intros ms' md' HQ Hhid Hsbm.
  assert (KSPof : forall m md, AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m md k -> forall i, 0 <= i < 392 ->
                    exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (ACtlCutP.Sfr fr + i)) = Some b)
    by (intros m md HJm; exact (w1_fsh_rd cx ly3 S3 W3 m md k fr HJm Hfr Efr)).
  destruct HQ as [(R' & m' & -> & G2 & G3 & G4 & G8 & G9 & G19 & G26 & G27 & G23 & G25 & G24 & MU & WM & B40 & B48 &
                   B152 & B160) |
                  (R' & m' & -> & G2 & G3 & G4 & G8 & G9 & G19 & G20 & G26 & G27 & G10 & G22 & G23 & G25 & HN7 & MU & WM &
                   B40 & B48 & B152 & B160 & HC11)].
  - (* P3 *)
    assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
    { apply (w1_journal_run cx _ ly3 S3 W3 mem3 md3 k m' md' _ HJ MU WM Hhid Hsbm).
      intros a Ha Hni. cbn [lib.Lib.Frame.outside] in Hni. split.
      - left. unfold Reusable.YCfn.LLVMF_STK. lia.
      - intros Hi. apply w1_img in Hi. lia. }
    pose proof (w1_rt cx _ ly3 S3 W3 m' md' k HB HJ') as HRT'.
    destruct (w1_frame cx ly3 S3 W3 m' md' k HJ' Hfr) as (_ & _ & _ & _ & _ & Hfb' & _).
    rewrite <- Efr in Hfb'.
    assert (MK : forall lo hi, (forall a, lo <= a < hi -> 0 <= a < 2 ^ 64 /\
                     ~ (A + 40 <= a < A + 56) /\ ~ (A + 152 <= a < A + 168)) -> KEEPR mem3 m' lo hi).
    { intros lo hi H. apply (w1_keep_munch _ mem3 m' lo hi MU). intros a Ha. destruct (H a Ha) as (H1 & H2 & H3).
      split; [exact H1|]. cbn [lib.Lib.Frame.outside]. split; [exact H2|]. split; [exact H3 | exact I]. }
    assert (R9' : ACtlCut.rgv R' 9 A) by (unfold ACtlCut.rgv; rewrite G9; exact E9).
    assert (SP : forall off v, 0 <= off -> off + 8 <= 448 -> (off + 8 <= 40 \/ (56 <= off /\ off + 8 <= 152) \/ 168 <= off) ->
                   ACtlCutP.spill R mem3 off v -> ACtlCutP.spill R' m' off v).
    { intros off v H0 H1 H2 Hs. apply (w1_spill_mv R R' mem3 m' A off v E9 ltac:(lia) ltac:(lia) H0 H1 G9); [|exact Hs].
      apply MK. intros a Ha. split; [lia|]. lia. }
    assert (KF : forall lo hi, fr <= lo -> hi <= fr + 4096 -> KEEPR mem3 m' lo hi)
      by (intros lo hi H1 H2; apply MK; intros a Ha; split; [lia|]; lia).
    assert (KS : KEEPR mem3 m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW))
      by (apply MK; intros a Ha; unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in Ha; split; [lia|]; lia).
    assert (HFRAHC' : ACtlCutP.FRAHC B cx fr fr 0x41b58ab3 R' m').
    { apply (w1_frahc_mv cx fr fr 0x41b58ab3 A R R' mem3 m' E9 ltac:(lia) G2 G3 G4 G8 G9 G19 G26);
        [apply MK; intros a Ha; split; [lia|]; lia | apply KF; lia | exact (KSPof m' md' HJ') |
         apply MK; intros a Ha; split; [lia|]; lia | apply KF; lia | exact HFRAHC]. }
    apply (Hcb cx [] fr k ly3 S3 W3 R' m' md' HB HJ' Hfr HFA ltac:(cbn; lia)).
    + unfold ACtlCutP.C_B81cb0. cbn [ACtlCut.cut_body].
      split; [exact Hperm|].
      split; [exact (w1_frac_of_frahc cx fr fr A R' m' HFRAHC' R9' ltac:(lia) B48 B40)|].
      split; [first [exact (proj2 Hn26) | exact Hn26]|].
      split; [unfold ACtlCutP.OURb in *; apply (w1_bytes_keep mem3 m'); [| exact HOUR];
              rewrite ACtlCutP.SM.OUR_length; apply KF; lia|].
      split; [exact G24|].
      split.
      { unfold ACtlCutP.PRO, ACtlCutP.PRA in *.
        destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
        split; [repeat match goal with |- _ /\ _ => split end; apply SP; (lia || assumption)|].
        split; [exact (w1_spill_of R' m' A 152 (fr + 64) R9' B152)|].
        split; [apply SP; [lia | lia | lia | exact S264]|].
        split; [apply (w1_faddr_keep mem3 m' fr 2624 6 KS Hfr8); [lia | lia | unfold ACtlCutP.FRAME_BYTES; lia |];
                replace (fr + 2624) with (fr + 2624) by reflexivity; exact HA2624|].
        exact (w1_spill_of R' m' A 160 (fr + 32) R9' B160). }
      split; [apply SP; [lia | lia | lia | exact S64]|].
      split.
      { unfold ACtlCutP.CUR, ACtlCutP.SM.c0, B.Prog.SlotModel.c0, B.Prog.SlotModel.nlen. rewrite <- Hlen.
        split; [lia|]. split; [exact G23 | exact G25]. }
      split; [exact (ctl_kind_name_addressable _ _ _ _ _ (proj1 HJ'))|].
      destruct (w1_rw_present _ m' (fr + 2688) 38 ltac:(lia) ltac:(lia)
                  ltac:(intros a Ha; exact (proj1 (Hfb' a ltac:(lia))))) as (idb & _ & C2688).
      destruct (w1_rw_present _ m' (fr + 2768) 72 ltac:(lia) ltac:(lia)
                  ltac:(intros a Ha; exact (proj1 (Hfb' a ltac:(lia))))) as (jk & _ & C2768).
      destruct (w1_rw_present _ m' (fr + 2880) 40 ltac:(lia) ltac:(lia)
                  ltac:(intros a Ha; exact (proj1 (Hfb' a ltac:(lia))))) as (jf & _ & C2880).
      exists sp, A, idb, jk.
      split; [rewrite G2; exact Esp|]. split; [rewrite G9; exact E9|]. split; [lia|]. split; [lia|].
      split; [apply (w1_spill_at R' m' A 176 (fr + 2688) R9' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia));
              apply SP; [lia | lia | lia | exact S176]|].
      split.
      { apply B.Prog.Seg.A5.b_rw_C8.
        - apply (w1_spill_at R' m' A 208 (fr + 2768) R9' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
          apply SP; [lia | lia | lia | exact S208].
        - destruct (w1_rw_present (Reusable.YA0n.w_H W3) m' (A + 208) 8 ltac:(lia) ltac:(lia)
                      ltac:(intros a Ha;
                            exact (proj2 (proj2 (proj2 (w1_stack cx _ ly3 S3 W3 m' md' k HJ'))) a ltac:(lia))))
            as (j8 & _ & (_ & HW8)).
          exact HW8. }
      split; [exact C2688|]. split; [exact C2768|]. exists jf. exact C2880.
    + exact HRT'.
  - (* 0x815fc *)
    assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
    { apply (w1_journal_run cx _ ly3 S3 W3 mem3 md3 k m' md' _ HJ MU WM Hhid Hsbm).
      intros a Ha Hni. cbn [lib.Lib.Frame.outside] in Hni. split.
      - rewrite ESh in Hni.
        destruct (Z.eq_dec a (fr / 8 + 0x7fff8000 + 332)) as [Ea | Na].
        + right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
          unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa.
          change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
          unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
        + destruct (Z_le_gt_dec (fr + 2656) a) as [H1 | H1]; [destruct (Z_lt_le_dec a (fr + 2664)) as [H2 | H2] |].
          * right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. left.
            unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa.
            change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
          * left. unfold Reusable.YCfn.LLVMF_STK. lia.
          * left. unfold Reusable.YCfn.LLVMF_STK. lia.
      - intros Hi. apply w1_img in Hi. rewrite ESh in Hni. lia. }
    pose proof (w1_rt cx _ ly3 S3 W3 m' md' k HB HJ') as HRT'.
    assert (MK : forall lo hi, (forall a, lo <= a < hi -> 0 <= a < 2 ^ 64 /\
                     ~ (A + 40 <= a < A + 56) /\ ~ (A + 152 <= a < A + 168) /\
                     ~ (ACtlCutP.Sfr fr + 332 <= a < ACtlCutP.Sfr fr + 333) /\ ~ (fr + 2656 <= a < fr + 2664) /\
                     ~ (sp - 16 <= a < sp)) -> KEEPR mem3 m' lo hi).
    { intros lo hi H. apply (w1_keep_munch _ mem3 m' lo hi MU). intros a Ha. destruct (H a Ha) as (H1 & H2 & H3 & H4 & H5 & H6).
      split; [exact H1|]. cbn [lib.Lib.Frame.outside]. tauto. }
    assert (R9' : ACtlCut.rgv R' 9 A) by (unfold ACtlCut.rgv; rewrite G9; exact E9).
    assert (SP : forall off v, 0 <= off -> off + 8 <= 448 -> (off + 8 <= 40 \/ (56 <= off /\ off + 8 <= 152) \/ 168 <= off) ->
                   ACtlCutP.spill R mem3 off v -> ACtlCutP.spill R' m' off v).
    { intros off v H0 H1 H2 Hs. apply (w1_spill_mv R R' mem3 m' A off v E9 ltac:(lia) ltac:(lia) H0 H1 G9); [|exact Hs].
      apply MK. intros a Ha. rewrite ESh. split; [lia|]. Z.div_mod_to_equations. lia. }
    assert (KF : forall lo hi, fr <= lo -> hi <= fr + 2656 \/ fr + 2664 <= lo -> hi <= fr + 4096 -> KEEPR mem3 m' lo hi)
      by (intros lo hi H1 H2 H3; apply MK; intros a Ha; rewrite ESh; split; [lia|];
          destruct Happ' as [_ [Hl | Hh]]; Z.div_mod_to_equations; lia).
    assert (HFRAHC' : ACtlCutP.FRAHC B cx fr fr 0x41b58ab3 R' m').
    { apply (w1_frahc_mv cx fr fr 0x41b58ab3 A R R' mem3 m' E9 ltac:(lia) G2 G3 G4 G8 G9 G19 G26);
        [apply MK; intros a Ha; rewrite ESh; split; [lia|]; Z.div_mod_to_equations; lia |
         apply KF; lia | exact (KSPof m' md' HJ') |
         apply MK; intros a Ha; rewrite ESh; split; [lia|]; Z.div_mod_to_equations; lia |
         apply KF; lia | exact HFRAHC]. }
    apply (Hfc cx [] fr k ly3 S3 W3 R' m' md' HB HJ' Hfr HFA Hk).
    + unfold ACtlCutP.C_B815fc. cbn [ACtlCut.cut_body].
      split; [exact Hperm|].
      split; [exact (w1_frac_of_frahc cx fr fr A R' m' HFRAHC' R9' ltac:(lia) B48 B40)|].
      split; [first [exact (proj2 Hn26) | exact Hn26]|].
      split; [unfold ACtlCut.a0v, ACtlCut.rgv; rewrite G10; reflexivity|].
      split; [unfold ACtlCutP.OURb in *; apply (w1_bytes_keep mem3 m'); [| exact HOUR];
              rewrite ACtlCutP.SM.OUR_length; apply KF; lia|].
      split; [unfold ACtlCut.rgv; rewrite G27; exact H27|].
      split; [unfold ACtlCutP.CUR; split; [lia|]; split; [exact G23 | exact G25]|].
      split; [apply SP; [lia | lia | lia | exact S144]|].
      split; [apply SP; [lia | lia | lia | exact S112]|].
      split; [apply SP; [lia | lia | lia | exact S312]|].
      split; [apply SP; [lia | lia | lia | exact S264]|].
      split; [unfold ACtlCut.rgv; rewrite G20; exact H20|].
      split; [exact HC11|].
      split; [apply SP; [lia | lia | lia | exact S56]|].
      split; [apply SP; [lia | lia | lia | exact S184]|].
      split.
      { apply (w1_addr_keep mem3 m'); [| exact HA2624]. intros i Hi.
        apply (MK (B.AsanRT.shadow_addr (fr + 2624 + i)) (B.AsanRT.shadow_addr (fr + 2624 + i) + 1)); [| lia].
        intros a Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha. rewrite ESh.
        split; [Z.div_mod_to_equations; lia|]. Z.div_mod_to_equations. lia. }
      split; [apply SP; [lia | lia | lia | exact S96]|].
      split; [apply SP; [lia | lia | lia | exact S120]|].
      split; [apply SP; [lia | lia | lia | exact S240]|].
      split; [apply SP; [lia | lia | lia | exact S232]|].
      split; [apply SP; [lia | lia | lia | exact S224]|].
      split; [apply SP; [lia | lia | lia | exact S176]|].
      split; [apply SP; [lia | lia | lia | exact S208]|].
      split; [apply SP; [lia | lia | lia | exact S64]|].
      split.
      { unfold ACtlCutP.PRA in *.
        destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
        repeat match goal with |- _ /\ _ => split end; apply SP; (lia || assumption). }
      split; [exact (w1_spill_of R' m' A 152 (fr + 64) R9' B152)|].
      split; [exact G22|].
      exact (w1_spill_of R' m' A 160 (fr + 32) R9' B160).
    + exact HRT'.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   After one turn of the loop (from the head 0x81548 or the body cut 0x81550): the byte our[t] written, the turn's
   registers stepped; at t < 5 the next head cut (index t + 1), at t = 5 the exit (w1_exit).  FRAHC is
   re-established at the new memory (w1_frahc_mv). *)
Lemma w1_after_turn : forall POST (t : Z) (cx : ACtlCut.ctlcx) (fr k : Z) ly3 S3 W3 (regs3 R : bvmap 5 word) mem3 md3
    (m' : word -> option byte) md' (junk : list byte),
  (t < 5 -> ctl_from POST (ix_cut C_B81548_at [t + 1])) ->
  ctl_from POST C_B815fc -> ctl_from POST C_B81cb0 ->
  CBASE cx -> AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  k <= 0 -> 0 <= t <= 5 ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) ->
  ACtlCutP.FRAHC B cx fr fr 0x41b58ab3 regs3 mem3 -> ACtlCutP.PRA fr regs3 mem3 ->
  ACtlCut.rgv regs3 24 fr -> ACtlCut.rgv regs3 25 fr ->
  ACtlCutP.spill regs3 mem3 144 (fr + 2176) -> ACtlCutP.spill regs3 mem3 112 (fr + 2256) ->
  ACtlCutP.spill regs3 mem3 312 (fr + 544) -> ACtlCutP.spill regs3 mem3 264 (fr + 2624) ->
  ACtlCut.rgv regs3 20 (fr + 2656) -> ACtlCut.rgv regs3 17 (fr + 64) -> ACtlCut.rgv regs3 27 (ACtlCutP.Sfr fr + 68) ->
  ACtlCutP.spill regs3 mem3 56 (fr + 3040) -> ACtlCutP.spill regs3 mem3 184 (fr + 2368) ->
  ACtlCutP.spill regs3 mem3 176 (fr + 2688) -> ACtlCutP.spill regs3 mem3 208 (fr + 2768) ->
  B.AsanRT.addressable mem3 (fr + 2624) 6 ->
  ACtlCutP.spill regs3 mem3 96 (ACtlCutP.decl_slot fr) -> ACtlCutP.spill regs3 mem3 120 (fr + 2528) ->
  ACtlCutP.spill regs3 mem3 240 (fr + 2448) -> ACtlCutP.spill regs3 mem3 232 (fr + 2464) ->
  ACtlCutP.spill regs3 mem3 224 (fr + 2496) -> ACtlCutP.spill regs3 mem3 64 (fr + 3056) ->
  ACtlCut.rgv regs3 16 (fr + 32) ->
  length junk = Z.to_nat (6 - t) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (fr + 2624) (firstn (Z.to_nat t) (ACtlCutP.SM.OUR (ACtlCut.c_in cx)) ++ junk) ->
  lib.Lib.Frame.munch ((fr + 2624 + t, fr + 2624 + t + 1) :: nil) mem3 m' ->
  lib.Lib.Frame.wmono B.Img0.rsegs mem3 m' ->
  (forall x : word, Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) ->
  Reusable.YK04.same_but_materialized md3 md' ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' (fr + 2624 + t) [lib.Prog.RcIdentModel.nthb (ACtlCut.c_in cx) (Z.to_nat t)] ->
  lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2 ->
  lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3 ->
  lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4 ->
  lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8 ->
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9 ->
  lib.Reusable.YK11.getr R 16 = lib.Reusable.YK11.getr regs3 16 ->
  lib.Reusable.YK11.getr R 17 = lib.Reusable.YK11.getr regs3 17 ->
  lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19 ->
  lib.Reusable.YK11.getr R 20 = lib.Reusable.YK11.getr regs3 20 ->
  lib.Reusable.YK11.getr R 24 = lib.Reusable.YK11.getr regs3 24 ->
  lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25 ->
  lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26 ->
  lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs3 27 ->
  ACtlCut.rgv R 10 (6 - (t + 1)) -> ACtlCut.rgv R 11 1 -> ACtlCut.rgv R 12 (fr + 2624 + (t + 1)) ->
  ACtlCut.rgv R 18 (ACtlCut.c_n cx - Z.min (t + 1) (ACtlCut.c_n cx)) ->
  ACtlCut.rgv R 22 (ACtlCut.c_p cx + Z.min (t + 1) (ACtlCut.c_n cx)) ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (if 6 - t =? 1 then 0x815a0 else 0x81548) R m' md') (POST cx).
Proof.
  intros POST t cx fr k ly3 S3 W3 regs3 R mem3 md3 m' md' junk IH Hfc Hcb HB HJ Hfr HFA Hk Ht Hperm HFRAHC HPRA
    H24 H25 S144 S112 S312 S264 H20 H17 H27 S56 S184 S176 S208 HA2624 S96 S120 S240 S232 S224 S64 H16
    Hjl HOUR MU WM Hhid Hsbm BV G2 G3 G4 G8 G9 G16 G17 G19 G20 G24 G25 G26 G27 R10 R11 R12 R18 R22.
  pose proof (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)) as Efr.
  destruct (w1_frame cx ly3 S3 W3 mem3 md3 k HJ Hfr) as (Hin & Efa & Hf0 & Hf1 & Happ & Hfb & Hfsh).
  rewrite <- Efr in Efa, Hf0, Hf1, Happ, Hfb, Hfsh.
  pose proof (FRAME_ABOVE ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (proj1 HJ) Hin) as Hfhi.
  rewrite Efa in Hfhi.
  destruct (w1_stack cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hs0 & Hs47 & Hs16 & Hwin).
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  pose proof Happ as Happ'.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Happ'.
  pose proof HFRAHC as (A & sp & Esp & Hsp16 & EspZ & Etp & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
                        HfrA & HA448 & HSsp & HSapp & Q336 & Qhdr & Q16 & Hsh & Hsav & Qtr).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  pose proof (w1_spZ_range regs3) as Hspr. rewrite EspZ in Hspr.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (ESh : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000)
    by (unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; reflexivity).
  assert (Hdisj : forall a, fr <= a < fr + 4096 -> a < ACtlCutP.Sfr fr \/ ACtlCutP.Sfr fr + 512 <= a).
  { intros a Ha. rewrite ESh. Z.div_mod_to_equations. lia. }
  assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { apply (w1_journal_run cx _ ly3 S3 W3 mem3 md3 k m' md' _ HJ MU WM Hhid Hsbm).
    intros a Ha Hni. cbn [lib.Lib.Frame.outside] in Hni. split.
    - right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. left.
      unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa. change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
    - intros Hi. apply w1_img in Hi. lia. }
  pose proof (w1_rt cx _ ly3 S3 W3 m' md' k HB HJ') as HRT'.
  assert (MK : forall lo hi, (forall a, lo <= a < hi -> 0 <= a < 2 ^ 64 /\ ~ (fr + 2624 + t <= a < fr + 2624 + t + 1)) ->
                 KEEPR mem3 m' lo hi).
  { intros lo hi H. apply (w1_keep_munch _ mem3 m' lo hi MU). intros a Ha. destruct (H a Ha) as (H1 & H2).
    split; [exact H1|]. cbn [lib.Lib.Frame.outside]. split; [exact H2 | exact I]. }
  assert (KST : forall lo hi, sp <= lo -> hi <= ACtlCut.c_sp cx -> KEEPR mem3 m' lo hi)
    by (intros lo hi H1 H2; apply MK; intros a Ha; split; lia).
  assert (KS : KEEPR mem3 m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW))
    by (apply MK; intros a Ha; unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in Ha; rewrite ESh in Ha;
        split; [lia|]; destruct Happ' as [_ [Hl | Hh]]; Z.div_mod_to_equations; lia).
  assert (KSP : forall i, 0 <= i < 392 ->
                  exists b, lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa (ACtlCutP.Sfr fr + i)) = Some b)
    by exact (w1_fsh_rd cx ly3 S3 W3 m' md' k fr HJ' Hfr Efr).
  assert (SP : forall off v, 0 <= off -> off + 8 <= 448 ->
                 ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R m' off v).
  { intros off v H0 H1 Hs. apply (w1_spill_mv regs3 R mem3 m' A off v E9 ltac:(lia) ltac:(lia) H0 H1 G9); [|exact Hs].
    apply KST; lia. }
  assert (HFRAHC' : ACtlCutP.FRAHC B cx fr fr 0x41b58ab3 R m').
  { apply (w1_frahc_mv cx fr fr 0x41b58ab3 A regs3 R mem3 m' E9 ltac:(lia) G2 G3 G4 G8 G9 G19 G26);
      [apply KST; lia | apply MK; intros a Ha; split; lia | exact KSP | apply KST; lia |
       apply MK; intros a Ha; split; lia | exact HFRAHC]. }
  assert (HPRA' : ACtlCutP.PRA fr R m').
  { unfold ACtlCutP.PRA in *.
    destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
    repeat match goal with |- _ /\ _ => split end; apply SP; (lia || assumption). }
  assert (HA2624' : B.AsanRT.addressable m' (fr + 2624) 6)
    by (exact (w1_faddr_keep mem3 m' fr 2624 6 KS Hfr8 ltac:(lia) ltac:(lia) ltac:(unfold ACtlCutP.FRAME_BYTES; lia)
                 HA2624)).
  assert (Hjl1 : (1 <= length junk)%nat) by lia.
  pose proof (B.Prog.Seg.A5.b_our_keep mem3 m' (fr + 2624) t (firstn (Z.to_nat t) (ACtlCutP.SM.OUR (ACtlCut.c_in cx)))
                junk _ HOUR ltac:(rewrite length_firstn, ACtlCutP.SM.OUR_length; lia) ltac:(lia) Hjl1 MU BV) as HOUR1.
  rewrite <- B.Prog.Seg.A5.b_our_step in HOUR1 by lia.
  replace (S (Z.to_nat t)) with (Z.to_nat (t + 1)) in HOUR1 by lia.
  destruct (Z.eq_dec t 5) as [E5 | N5].
  - (* turn 5 done: the exit *)
    subst t. replace (6 - 5 =? 1) with true by reflexivity.
    refine (w1_exit POST cx fr k ly3 S3 W3 R m' md' Hfc Hcb HB HJ' Hfr HFA Hk Hperm HFRAHC' _ HPRA' HRT').
    unfold w1_EXB.
    split; [exact (w1_rgv_move R regs3 24 _ G24 H24)|].
    split; [exact (w1_rgv_move R regs3 25 _ G25 H25)|].
    split; [apply SP; [lia | lia | exact S144]|].
    split; [apply SP; [lia | lia | exact S112]|].
    split; [apply SP; [lia | lia | exact S312]|].
    split; [apply SP; [lia | lia | exact S264]|].
    split; [exact (w1_rgv_move R regs3 20 _ G20 H20)|].
    split; [exact (w1_rgv_move R regs3 17 _ G17 H17)|].
    split; [exact R18|].
    split; [exact R22|].
    split; [exact (w1_rgv_move R regs3 27 _ G27 H27)|].
    split; [apply SP; [lia | lia | exact S56]|].
    split; [apply SP; [lia | lia | exact S184]|].
    split; [apply SP; [lia | lia | exact S176]|].
    split; [apply SP; [lia | lia | exact S208]|].
    split; [exact HA2624'|].
    split; [apply SP; [lia | lia | exact S96]|].
    split; [apply SP; [lia | lia | exact S120]|].
    split; [apply SP; [lia | lia | exact S240]|].
    split; [apply SP; [lia | lia | exact S232]|].
    split; [apply SP; [lia | lia | exact S224]|].
    split; [apply SP; [lia | lia | exact S64]|].
    split.
    { unfold ACtlCutP.OURb.
      assert (Ej : tl junk = []) by (destruct junk as [|j0 [|j1 l]]; cbn in Hjl |- *; [lia | reflexivity | lia]).
      rewrite Ej, app_nil_r in HOUR1. change (Z.to_nat (5 + 1)) with 6%nat in HOUR1.
      rewrite firstn_all2 in HOUR1 by (rewrite ACtlCutP.SM.OUR_length; lia). exact HOUR1. }
    exact (w1_rgv_move R regs3 16 _ G16 H16).
  - (* the next head *)
    replace (6 - t =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (w1_input cx _ ly3 S3 W3 m' md' k HB HJ' Hperm) as (Hinb & Hina & Hn26 & _).
    apply (IH ltac:(lia) cx [t + 1] fr k ly3 S3 W3 R m' md' HB HJ' Hfr HFA Hk).
    + unfold ACtlCut.ix_cut, ACtlCutP.C_B81548_at, ACtlCutP.ixz. cbn [ACtlCut.cut_body nth].
      split; [reflexivity|]. split; [exact Hperm|]. split; [exact HFRAHC'|]. split; [|exact HPRA'].
      unfold ACtlCutP.LOOPB.
      split; [lia|]. split; [lia|].
      split; [exact (w1_rgv_move R regs3 24 _ G24 H24)|].
      split; [exact (w1_rgv_move R regs3 25 _ G25 H25)|].
      split; [apply SP; [lia | lia | exact S144]|].
      split; [apply SP; [lia | lia | exact S112]|].
      split; [apply SP; [lia | lia | exact S312]|].
      split; [apply SP; [lia | lia | exact S264]|].
      split; [exact (w1_rgv_move R regs3 20 _ G20 H20)|].
      split; [exact R10|]. split; [exact R11|]. split; [exact R12|].
      split; [exact (w1_rgv_move R regs3 17 _ G17 H17)|].
      split; [exact R18|]. split; [exact R22|].
      split; [exact (w1_rgv_move R regs3 27 _ G27 H27)|].
      split; [apply SP; [lia | lia | exact S56]|].
      split; [apply SP; [lia | lia | exact S184]|].
      split; [apply SP; [lia | lia | exact S176]|].
      split; [apply SP; [lia | lia | exact S208]|].
      split; [exact HA2624'|].
      split; [apply SP; [lia | lia | exact S96]|].
      split; [apply SP; [lia | lia | exact S120]|].
      split; [apply SP; [lia | lia | exact S240]|].
      split; [apply SP; [lia | lia | exact S232]|].
      split; [apply SP; [lia | lia | exact S224]|].
      split; [apply SP; [lia | lia | exact S64]|].
      split; [exact Hinb|]. split; [exact Hina|].
      split; [exists (tl junk); split; [destruct junk as [|j0 l]; cbn in Hjl |- *; lia | exact HOUR1]|].
      exact (w1_rgv_move R regs3 16 _ G16 H16).
    + exact HRT'.
Qed.

(* One turn from the head 0x81548 (S_A5's code; EB A5.v b_turn_gen at pc0 = 0x81548): left = s2 <> 0 (t < n):
   A5F.b_hd_ld_evt_F (the cursor's shadow check 0x81560 and T01 0x81554 not taken: in[t] is a live, addressable
   input byte; our[t] := in[t]); left = 0 (t >= n): A5F.b_z_evt_F (our[t] := 0 = in[t] past the end).  Then
   w1_after_turn. *)
Lemma w1_turn : forall POST (t : Z),
  (t < 5 -> ctl_from POST (ix_cut C_B81548_at [t + 1])) ->
  ctl_from POST C_B815fc -> ctl_from POST C_B81cb0 ->
  ctl_from POST (ix_cut C_B81548_at [t]).
Proof.
  intros POST t IH Hfc Hcb cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ACtlCut.ix_cut, ACtlCutP.C_B81548_at in HJ, Hfr, HFA, Hk, HBODY |- *.
  cbn [ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body ACtlCut.cut_pc] in HJ, Hfr, HFA, Hk, HBODY |- *.
  destruct HBODY as (-> & Hperm & HFRAHC & HLOOP & HPRA).
  unfold ACtlCutP.ixz in HLOOP. cbn [nth] in HLOOP.
  destruct HLOOP as (Hn26 & Ht & H24 & H25 & S144 & S112 & S312 & S264 & H20 & H10 & H11 & H12 & H17 & H18 & H22 &
                     H27 & S56 & S184 & S176 & S208 & HA2624 & S96 & S120 & S240 & S232 & S224 & S64 & HINB & HINA &
                     (junk & Hjl & HOUR) & H16).
  pose proof (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)) as Efr.
  destruct (w1_frame cx ly3 S3 W3 mem3 md3 k HJ Hfr) as (Hin & Efa & Hf0 & Hf1 & Happ & Hfb & Hfsh).
  rewrite <- Efr in Efa, Hf0, Hf1, Happ, Hfb, Hfsh.
  destruct (w1_stack cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hs0 & Hs47 & Hs16 & Hwin).
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  pose proof HFRAHC as (A & sp & Esp & Hsp16 & EspZ & Etp & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
                        HfrA & HA448 & HSsp & HSapp & Q336 & Qhdr & Q16 & Hsh & Hsav & Qtr).
  pose proof HB as ((_ & _ & _ & _ & _ & Hlen & _) & _).
  destruct (w1_input cx _ ly3 S3 W3 mem3 md3 k HB HJ Hperm) as (_ & _ & HnR & Hin3 & HP0 & HPN).
  set (N := ACtlCut.c_n cx) in *. set (P := ACtlCut.c_p cx) in *.
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (HWR : lib.Lib.Mem.wr_at B.Img0.rsegs mem3 (fr + 2624) 6).
  { split; [lia|]. split; [lia|]. intros i Hi. destruct (proj1 (Hfb (fr + 2624 + i) ltac:(lia))) as (_ & b & Hb).
    unfold wview, lib.Lib.Mem.wa. rewrite Hb. discriminate. }
  assert (HSTO : store_ok B.Img0.rsegs mem3 (lib.Lib.Mem.wa (fr + 2624 + t)) 1 = true)
    by exact (lib.Lib.Mem.wr_at_store_ok B.Img0.rsegs mem3 (fr + 2624) 6 t 1 HWR ltac:(lia) ltac:(cbn; lia)).
  assert (RVd : lib.Lib.ExecF.rng RNG (fr + 2624 + t) 1).
  { apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
    intros a Ha. exact (proj1 (proj1 (Hfb a ltac:(lia)))). }
  destruct (Z_lt_le_dec t N) as [HtN | HtN].
  - (* left <> 0: our[t] := in[t] *)
    pose proof (HINA ltac:(lia)) as (_ & _ & _ & Hadd).
    destruct (Hadd t ltac:(lia)) as (_ & kq & Hkq & Hok).
    pose proof (Hin3 ltac:(lia)) as HinB.
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ (proj1 HJ) HinB)
      as (_ & Hp4 & Hpc & _ & Hpbytes & _ & _).
    assert (Er : Reusable.YG00.req_size N = N) by (unfold Reusable.YG00.req_size; destruct (N =? 0) eqn:E; lia).
    rewrite Er in Hpc, Hpbytes.
    assert (Hbq : lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (P + t)) =
                  Some (lib.Prog.RcIdentModel.nthb (ACtlCut.c_in cx) (Z.to_nat t))).
    { destruct HINB as (_ & _ & Hbi). pose proof (Hbi (Z.to_nat t) ltac:(lia)) as E.
      rewrite Z2Nat.id in E by lia. etransitivity; [exact E|].
      unfold lib.Prog.RcIdentModel.nthb. apply nth_error_nth'. lia. }
    eapply (w1_lift W3 regs3 mem3 md3 0x81548 RNG).
    { unfold Lib.Regs6ss.mkR_of.
      eapply (A5F.b_hd_ld_evt_F RNG) with (cnt := 6 - t) (d := fr + 2624 + t) (q := P + t) (v := N - t)
        (K := B.AsanRT.ASAN_K) (b := lib.Prog.RcIdentModel.nthb (ACtlCut.c_in cx) (Z.to_nat t)) (kq := kq).
      - exact H10.
      - exact H11.
      - exact H12.
      - unfold ACtlCut.rgv in H18. rewrite Z.min_l in H18 by lia. exact H18.
      - unfold ACtlCut.rgv in H22. rewrite Z.min_l in H22 by lia. exact H22.
      - exact E26.
      - lia. - lia. - lia. - lia. - lia. - lia. - lia.
      - unfold B.AsanRT.ASAN_K. lia.
      - unfold B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
      - apply w1_ov1; [unfold B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia | exact Hkq].
      - unfold B.AsanRT.shadow_ok in Hok. lia.
      - apply w1_ov1; [lia | exact Hbq].
      - exact HSTO.
      - apply B.ProgBridge.rng_of_visible. split; [unfold B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
        split; [unfold B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
        intros a Ha. replace a with (B.AsanRT.shadow_addr (P + t))
          by (unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *; lia).
        exact (w1_block_shvis _ _ _ _ _ _ _ (proj1 HJ) HinB ltac:(lia) t ltac:(lia)).
      - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
        intros a Ha. exact (proj1 (proj1 (Hpbytes a ltac:(lia)))).
      - exact RVd. }
    { apply B.ProgBridge.fp_avoids_RNG_W. }
    intros ms' md' (x4 & x5 & m' & -> & MU & WM & BV) Hhid Hsbm.
    apply w1_cfg_back.
    eapply (w1_after_turn POST t cx fr k ly3 S3 W3 regs3 _ mem3 md3 m' md' junk IH Hfc Hcb HB HJ Hfr HFA Hk
              Ht Hperm HFRAHC HPRA H24 H25 S144 S112 S312 S264 H20 H17 H27 S56 S184 S176 S208 HA2624 S96 S120 S240
              S232 S224 S64 H16 Hjl HOUR MU WM Hhid Hsbm BV); try reflexivity.
    + symmetry. exact E26.
    + unfold ACtlCut.rgv. transitivity (Z_to_bv 64 (6 - t - 1)); [reflexivity | f_equal; lia].
    + unfold ACtlCut.rgv. transitivity (Z_to_bv 64 (fr + 2624 + t + 1)); [reflexivity | f_equal; lia].
    + unfold ACtlCut.rgv. unfold N in *.
      transitivity (Z_to_bv 64 (ACtlCut.c_n cx - t - 1)); [reflexivity | f_equal; lia].
    + unfold ACtlCut.rgv. unfold N, P in *.
      transitivity (Z_to_bv 64 (ACtlCut.c_p cx + t + 1)); [reflexivity | f_equal; lia].
  - (* left = 0: our[t] := 0 *)
    eapply (w1_lift W3 regs3 mem3 md3 0x81548 RNG).
    { unfold Lib.Regs6ss.mkR_of.
      eapply (A5F.b_z_evt_F RNG) with (cnt := 6 - t) (d := fr + 2624 + t).
      - exact H10.
      - exact H12.
      - unfold ACtlCut.rgv in H18. rewrite Z.min_r in H18 by lia. replace (N - N) with 0 in H18 by lia. exact H18.
      - lia. - lia. - lia.
      - exact HSTO.
      - exact RVd. }
    { apply B.ProgBridge.fp_avoids_RNG_W. }
    intros ms' md' (m' & -> & MU & WM & BV) Hhid Hsbm.
    rewrite <- (B.Prog.Seg.A5.b_nth_past (ACtlCut.c_in cx) (Z.to_nat t)) in BV by lia.
    apply w1_cfg_back.
    eapply (w1_after_turn POST t cx fr k ly3 S3 W3 regs3 _ mem3 md3 m' md' junk IH Hfc Hcb HB HJ Hfr HFA Hk
              Ht Hperm HFRAHC HPRA H24 H25 S144 S112 S312 S264 H20 H17 H27 S56 S184 S176 S208 HA2624 S96 S120 S240
              S232 S224 S64 H16 Hjl HOUR MU WM Hhid Hsbm BV); try reflexivity.
    + unfold ACtlCut.rgv. transitivity (Z_to_bv 64 (6 - t - 1)); [reflexivity | f_equal; lia].
    + exact H11.
    + unfold ACtlCut.rgv. transitivity (Z_to_bv 64 (fr + 2624 + t + 1)); [reflexivity | f_equal; lia].
    + unfold ACtlCut.rgv. unfold N in *.
      transitivity (Z_to_bv 64 0); [reflexivity | f_equal; lia].
    + unfold ACtlCut.rgv in H22 |- *. transitivity (lib.Reusable.YK11.getr regs3 22); [reflexivity|].
      rewrite H22. unfold N, P in *. f_equal. lia.
Qed.

(* The our[] loop, every t: well-founded on 5 - t (EB A5.v b_loop :2423-2428), each turn by w1_turn. *)
Lemma w1_our_loop : forall POST,
  ctl_from POST C_B815fc ->
  ctl_from POST C_B81cb0 ->
  ctl_from POST C_B81548_at.
Proof.
  intros POST Hfc Hcb.
  assert (W0 : forall n (t : Z), Z.to_nat (5 - t) = n -> ctl_from POST (ix_cut C_B81548_at [t])).
  { induction n as [|n IHn]; intros t Hn.
    - apply (w1_turn POST t); [intros Ht; lia | exact Hfc | exact Hcb].
    - apply (w1_turn POST t); [| exact Hfc | exact Hcb]. intros Ht. apply IHn. lia. }
  apply ACtlCut.ctl_from_ix. intros i0 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  destruct HBODY as [-> HBODY].
  apply (W0 _ (ACtlCutP.ixz 0 i0) eq_refl cx [ACtlCutP.ixz 0 i0] fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk);
    [| exact HRT].
  split; [reflexivity | exact HBODY].
Qed.

(* B81548_at t --S_A5--> B81550 | B815fc | B81cb0 (ACtl.v's seg_A5 shape, pointwise in t): the loop from the head,
   w1_our_loop at index [t]; the B81550 premise is unused (EB A5.v:2434-2437 drops it the same way). *)
Lemma seg_A5 : forall POST (t : Z),
  ctl_from POST C_B81550 ->
  ctl_from POST C_B815fc ->
  ctl_from POST C_B81cb0 ->
  ctl_from POST (ix_cut C_B81548_at [t]).
Proof.
  intros POST t _ Hfc Hcb.
  exact (proj2 (ACtlCut.ctl_from_ix _ _ _ _ _ _ _ _) (w1_our_loop POST Hfc Hcb) [t]).
Qed.

(* B81550 --S_R1--> B815fc | B81cb0.  S_R1 (EB Seg/R1.v seg_R1 :38): the rest of turn t from the body cut 0x81550
   (R1F.seg_R1_F: T01 0x81554 not taken, the cursor's shadow check, our[t] := in[t]), then w1_after_turn: the next
   head (w1_our_loop at [t + 1]) or the exit (w1_exit). *)
Lemma seg_R1 : forall POST,
  ctl_from POST C_B815fc ->
  ctl_from POST C_B81cb0 ->
  ctl_from POST C_B81550.
Proof.
  intros POST Hfc Hcb cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ACtlCutP.C_B81550 in HJ, Hfr, HFA, Hk, HBODY |- *.
  cbn [ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body ACtlCut.cut_pc] in HJ, Hfr, HFA, Hk, HBODY |- *.
  destruct HBODY as (t & Hperm & HFRAHC & HLOOP & HPRA & HtN & H13).
  destruct HLOOP as (Hn26 & Ht & H24 & H25 & S144 & S112 & S312 & S264 & H20 & H10 & H11 & H12 & H17 & H18 & H22 &
                     H27 & S56 & S184 & S176 & S208 & HA2624 & S96 & S120 & S240 & S232 & S224 & S64 & HINB & HINA &
                     (junk & Hjl & HOUR) & H16).
  pose proof (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)) as Efr.
  destruct (w1_frame cx ly3 S3 W3 mem3 md3 k HJ Hfr) as (Hin & Efa & Hf0 & Hf1 & Happ & Hfb & Hfsh).
  rewrite <- Efr in Efa, Hf0, Hf1, Happ, Hfb, Hfsh.
  destruct (w1_stack cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hs0 & Hs47 & Hs16 & Hwin).
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  pose proof HFRAHC as (A & sp & Esp & Hsp16 & EspZ & Etp & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
                        HfrA & HA448 & HSsp & HSapp & Q336 & Qhdr & Q16 & Hsh & Hsav & Qtr).
  pose proof HB as ((_ & _ & _ & _ & _ & Hlen & _) & _).
  destruct (w1_input cx _ ly3 S3 W3 mem3 md3 k HB HJ Hperm) as (_ & _ & HnR & Hin3 & HP0 & HPN).
  set (N := ACtlCut.c_n cx) in *. set (P := ACtlCut.c_p cx) in *.
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (HWR : lib.Lib.Mem.wr_at B.Img0.rsegs mem3 (fr + 2624) 6).
  { split; [lia|]. split; [lia|]. intros i Hi. destruct (proj1 (Hfb (fr + 2624 + i) ltac:(lia))) as (_ & b & Hb).
    unfold wview, lib.Lib.Mem.wa. rewrite Hb. discriminate. }
  assert (HSTO : store_ok B.Img0.rsegs mem3 (lib.Lib.Mem.wa (fr + 2624 + t)) 1 = true)
    by exact (lib.Lib.Mem.wr_at_store_ok B.Img0.rsegs mem3 (fr + 2624) 6 t 1 HWR ltac:(lia) ltac:(cbn; lia)).
  pose proof (HINA ltac:(lia)) as (_ & _ & _ & Hadd).
  destruct (Hadd t ltac:(lia)) as (_ & kq & Hkq & Hok).
  pose proof (Hin3 ltac:(lia)) as HinB.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ (proj1 HJ) HinB)
    as (_ & Hp4 & Hpc & _ & Hpbytes & _ & _).
  assert (Er : Reusable.YG00.req_size N = N) by (unfold Reusable.YG00.req_size; destruct (N =? 0) eqn:E; lia).
  rewrite Er in Hpc, Hpbytes.
  assert (Hbq : lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (P + t)) =
                Some (lib.Prog.RcIdentModel.nthb (ACtlCut.c_in cx) (Z.to_nat t))).
  { destruct HINB as (_ & _ & Hbi). pose proof (Hbi (Z.to_nat t) ltac:(lia)) as E.
    rewrite Z2Nat.id in E by lia. etransitivity; [exact E|].
    unfold lib.Prog.RcIdentModel.nthb. apply nth_error_nth'. lia. }
  eapply (w1_lift W3 regs3 mem3 md3 0x81550 RNG).
  { unfold Lib.Regs6ss.mkR_of.
    eapply (R1F.seg_R1_F RNG) with (cnt := 6 - t) (d := fr + 2624 + t) (q := P + t) (v := N - t)
      (K := B.AsanRT.ASAN_K) (b := lib.Prog.RcIdentModel.nthb (ACtlCut.c_in cx) (Z.to_nat t)) (kq := kq).
    - exact H10.
    - exact H11.
    - exact H12.
    - exact H13.
    - unfold ACtlCut.rgv in H18. rewrite Z.min_l in H18 by lia. exact H18.
    - unfold ACtlCut.rgv in H22. rewrite Z.min_l in H22 by lia. exact H22.
    - exact E26.
    - lia. - lia. - lia. - lia. - lia. - lia. - lia.
    - unfold B.AsanRT.ASAN_K. lia.
    - unfold B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
    - apply w1_ov1; [unfold B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia | exact Hkq].
    - unfold B.AsanRT.shadow_ok in Hok. lia.
    - apply w1_ov1; [lia | exact Hbq].
    - exact HSTO.
    - apply B.ProgBridge.rng_of_visible. split; [unfold B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
      split; [unfold B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
      intros a Ha. replace a with (B.AsanRT.shadow_addr (P + t))
        by (unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *; lia).
      exact (w1_block_shvis _ _ _ _ _ _ _ (proj1 HJ) HinB ltac:(lia) t ltac:(lia)).
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (proj1 (Hpbytes a ltac:(lia)))).
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (proj1 (Hfb a ltac:(lia)))). }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' (x4 & x5 & m' & -> & MU & WM & BV) Hhid Hsbm.
  apply w1_cfg_back.
  assert (IH : t < 5 -> ctl_from POST (ix_cut C_B81548_at [t + 1])).
  { intros _. exact (proj2 (ACtlCut.ctl_from_ix _ _ _ _ _ _ _ _) (w1_our_loop POST Hfc Hcb) [t + 1]). }
  unfold N, P in *.
  eapply (w1_after_turn POST t cx fr k ly3 S3 W3 regs3 _ mem3 md3 m' md' junk IH Hfc Hcb HB HJ Hfr HFA Hk
            Ht Hperm HFRAHC HPRA H24 H25 S144 S112 S312 S264 H20 H17 H27 S56 S184 S176 S208 HA2624 S96 S120 S240
            S232 S224 S64 H16 Hjl HOUR MU WM Hhid Hsbm BV); try reflexivity.
  all: try (symmetry; exact E26).
  all: unfold ACtlCut.rgv.
  all: first [transitivity (Z_to_bv 64 (6 - t - 1)); [reflexivity | f_equal; lia]
             | transitivity (Z_to_bv 64 (fr + 2624 + t + 1)); [reflexivity | f_equal; lia]
             | transitivity (Z_to_bv 64 (ACtlCut.c_n cx - t - 1)); [reflexivity | f_equal; lia]
             | transitivity (Z_to_bv 64 (ACtlCut.c_p cx + t + 1)); [reflexivity | f_equal; lia]].
Qed.

(* The mode byte is a byte. *)
Lemma w1_mode_range : forall inp, 0 <= ACtlCutP.SM.mode inp < 256.
Proof.
  intros inp. unfold ACtlCutP.SM.mode, ACtlCutP.SM.inb.
  destruct (7 <=? _); [| lia].
  match goal with |- 0 <= ?f ?b < 256 =>
    pose proof (bv_unsigned_in_range 8 b) as H; change (f b) with (bv_unsigned b) end.
  change (bv_modulus 8) with 256 in H. lia.
Qed.


(* ---------------------------------------------------------------------------------------------------------
   B815fc (0x815fc, own6, k <= 0) --S_R2--> B81640.
   S_R2 (Seg/R2.v seg_R2 :995): R2F.r2_evt_pre_F (0x815fc -> __asan_set_shadow_00 0x55024 with ra = 0x81640,
   a0 = S(fr) + 68, a1 = 186: the catalogue result checks, the row offset, T04, [A + 8] := S(fr) + 68), on
   MemNorm.normalize of the cut memory (its mem_inv premise) and carried back by B.ProgWorld.rebase_ro_normalize; then
   __asan_set_shadow_00 by the shared rule ASF00 in journal form (w1_aj_set_shadow), returning at 0x81640 = the
   successor cut.  R2F.r2_evt_post_F (0 steps, raw munch premise) is not applied: the call's post is the world view,
   and the proved B.ProgWorld.ctl_post_set_shadow turns it into munch_vis and the 186 zero shadow bytes, which make
   out[]'s first 1488 bytes addressable.  The three abort branches of the stretch (0x81600 `j 0x82fa4` after
   a0 = CAT <> 0, 0x8160c `j 0x82fa4` after [fr + 2656] = CAT_N = 11 <> 0, T04 0x81628 after a1 <= 2960) are
   not-taken steps inside r2_evt_pre_F, whose premises are the body's a0 = CAT and q64 (fr + 2656) CAT_N.
   s2 = CAT + 296 * ((mode >> 1) mod 11) = mrow.  FRAC is re-established at the new memory (w1_frac_mv). *)
Lemma seg_R2 : forall POST,
  ctl_from POST C_B81640 ->
  ctl_from POST C_B815fc.
Proof.
  intros POST H640 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ACtlCutP.C_B815fc in HJ, Hfr, HFA, Hk, HBODY |- *.
  cbn [ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body ACtlCut.cut_pc] in HJ, Hfr, HFA, Hk, HBODY |- *.
  pose proof (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)) as Efr.
  destruct (w1_frame cx ly3 S3 W3 mem3 md3 k HJ Hfr) as (Hin & Efa & Hf0 & Hf1 & Happ & Hfb & Hfsh).
  rewrite <- Efr in Efa, Hf0, Hf1, Happ, Hfb, Hfsh.
  destruct (w1_stack cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hs0 & Hs47 & Hs16 & Hwin).
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  pose proof Happ as Happ'.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Happ'.
  pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [HcR _]. unfold Reusable.YG0f.ASAN_CEIL in HcR.
  pose proof (w1_shp W3 mem3 fr Hfsh) as Hshp.
  destruct HBODY as (Hperm & HFRAC & Hn & Ha0 & HOUR & H27 & HCUR & S144 & S112 & S312 & S264 & H20 & Q2656 & S56 &
                     S184 & HA2624 & S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HPRA & S152 & H22 & S160).
  pose proof HFRAC as (A & sp & Esp & Hsp16 & EspZ & Etp & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HSsp & HSapp & Q336 & Q48 & Q40 & Qhdr & Q16 & Hsh & Hsav & Qtr).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  pose proof (w1_spZ_range regs3) as Hspr. rewrite EspZ in Hspr.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _ & _ & Hgp0 & _).
  assert (ESh : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000)
    by (unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; reflexivity).
  assert (ESA : forall X, 0 <= X -> B.AsanRT.shadow_addr (fr + 8 * X) = ACtlCutP.Sfr fr + X).
  { intros X HX. rewrite ESh. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
    replace (fr + 8 * X) with (fr + X * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (Hdisj : forall a, fr <= a < fr + 4096 -> a < ACtlCutP.Sfr fr \/ ACtlCutP.Sfr fr + 512 <= a).
  { intros a Ha. rewrite ESh. Z.div_mod_to_equations. lia. }
  assert (H27r : LinuxProcessSemantics.Riscv.Sem.reg_get regs3 27 = Z_to_bv 64 (ACtlCutP.Sfr fr + 68)) by exact H27.
  pose proof (w1_mode_range (ACtlCut.c_in cx)) as Hmode.
  assert (U22r : bv_unsigned (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 22) = ACtlCutP.SM.mode (ACtlCut.c_in cx))
    by (exact (w1_rgv_unsigned regs3 22 _ H22 ltac:(lia))).
  pose proof HRT as (HAC & _ & _ & HRO).
  assert (HROn : B.MemNorm.ro_agree B.Img0.rsegs mem3) by exact HRO.
  pose proof (B.MemNormTr.asan_cells_normalize mem3 HROn HAC) as HACn.
  pose proof (B.MemNorm.mem_inv_normalize B.Img0.rsegs mem3) as HMIn.
  destruct (w1_rw_present _ mem3 (ACtlCutP.Sfr fr + 68) 186 ltac:(lia) ltac:(lia)
              ltac:(intros a Ha; apply Hshp; lia)) as (jq & Hjql & CQ).
  assert (CQn : lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) (ACtlCutP.Sfr fr + 68)
                  (lib.Lib.Cells.CB 186 jq :: nil)).
  { apply (B.MemNormTr.rw_cells_normalize mem3 _ _ HROn); [| exact CQ].
    intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi. apply w1_ro_hi. rewrite ESh. lia. }
  destruct (w1_rw_present _ mem3 (A + 8) 8 ltac:(lia) ltac:(lia)
              ltac:(intros a Ha; apply Hwin; lia)) as (jsp & Hjspl & CS).
  assert (CSn : lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) (A + 8)
                  (lib.Lib.Cells.CB 8 jsp :: nil)).
  { apply (B.MemNormTr.rw_cells_normalize mem3 _ _ HROn); [| exact CS].
    intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi. apply w1_ro_hi. lia. }
  assert (STn : lib.Lib.Frame.stk B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) (A + 8) (A + 16)).
  { apply (B.MemNormTr.stk_normalize_ro mem3 _ _ HROn); [unfold B.Prog.ImgBounds.IMG_HI; lia|].
    apply (w1_stk_pres (Reusable.YA0n.w_H W3)); [lia | lia | intros a Ha; apply Hwin; lia]. }
  pose proof (B.MemNorm.bytes_at_normalize B.Img0.rsegs mem3 _ _ HROn Q2656) as Q2656n.
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  evar (Pq : machine_state -> Prop).
  assert (HRUN : Lib.ExecF.evtF B.Img0.rsegs RNG Pq
                   (lib.Lib.MState.MS (Lib.Regs6ss.mkR_of regs3) lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x815fc)
                      lib.Reusable.YK11.fp_csr None (B.MemNorm.normalize B.Img0.rsegs mem3)
                      (lib.Lib.PropExec.seg_rom B.Img0.rsegs))).
  { unfold Pq, Lib.Regs6ss.mkR_of.
    eapply (R2F.r2_evt_pre_F RNG) with (Ab := A) (c := fr + 2656) (Q := ACtlCutP.Sfr fr + 68) (junk := jq)
      (jsp := jsp).
    - exact Ha0.
    - exact E9.
    - exact H20.
    - exact H27.
    - unfold B.AsanRT.RT_HI. rewrite ESh. lia.
    - rewrite ESh. lia.
    - lia.
    - apply B.Prog.Seg.R4.r4_ro8. exact Q2656n.
    - intros i Hi. replace (ACtlCutP.Sfr fr + 68 + i) with (ACtlCutP.Sfr fr + (68 + i)) by lia.
      apply (B.Prog.Seg.R3.r3_fsh fr (68 + i)); [intros a Ha; apply (w1_frame_app fr); [exact Happ | lia] | lia].
    - exact CQn.
    - exact CSn.
    - exact STn.
    - exact HACn.
    - exact HMIn.
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (proj1 (Hfb a ltac:(lia)))).
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (Hwin a ltac:(lia))). }
  apply (w1_lift_n W3 regs3 mem3 md3 0x815fc RNG Pq (POST cx) HROn HRUN (B.ProgBridge.fp_avoids_RNG_W _)).
  intros ms' md' s0 PO Hrel Hby Hmu Hwm Hhid Hsbm.
  unfold Pq in PO.
  destruct PO as (a2' & s2' & m1 & Es0 & Es2 & MU1 & WM1 & CHQ1 & STS1 & B11 & HAC1 & HMI1).
  subst s0.
  destruct (B.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Ems _].
  rewrite Ems.
  pose proof (Hmu _ MU1) as MU'. pose proof (Hwm WM1) as WM'.
  pose proof (proj2 (Hby _ _) B11) as B11'.
  rewrite H27r in B11'.
  set (m1' := ms_mem ms') in *.
  assert (HJ1 : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m1' md' k).
  { apply (w1_journal_run cx _ ly3 S3 W3 mem3 md3 k m1' md' _ HJ MU' WM' Hhid Hsbm).
    intros a Ha Hni. cbn [lib.Lib.Frame.outside] in Hni. split.
    - destruct (Z_lt_le_dec a (A + 8)) as [Hlt|Hge].
      + right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
        unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa.
        change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
        unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. rewrite ESh in Hni. lia.
      + left. unfold Reusable.YCfn.LLVMF_STK. lia.
    - intros Hi. apply w1_img in Hi. rewrite ESh in Hni. lia. }
  destruct (w1_frame cx ly3 S3 W3 m1' md' k HJ1 Hfr) as (_ & _ & _ & _ & _ & _ & Hfsh1).
  rewrite <- Efr in Hfsh1.
  pose proof (w1_shp W3 m1' fr Hfsh1) as Hshp1.
  apply w1_cfg_back. unfold B.Prog.asan_set_shadow_c.ASAN_SET_SHADOW_00.
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (RT := R) end.
  assert (R1 : lib.Reusable.YK11.getr RT 1 = Z_to_bv 64 0x81640) by reflexivity.
  assert (R2 : lib.Reusable.YK11.getr RT 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (R3 : lib.Reusable.YK11.getr RT 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (R4 : lib.Reusable.YK11.getr RT 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (R8 : lib.Reusable.YK11.getr RT 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (R9 : lib.Reusable.YK11.getr RT 9 = lib.Reusable.YK11.getr regs3 9) by reflexivity.
  assert (R10 : lib.Reusable.YK11.getr RT 10 = Z_to_bv 64 (ACtlCutP.Sfr fr + 68))
    by (transitivity (lib.Reusable.YK11.getr regs3 27); [reflexivity | exact H27]).
  assert (R11 : lib.Reusable.YK11.getr RT 11 = Z_to_bv 64 186) by reflexivity.
  assert (R18 : lib.Reusable.YK11.getr RT 18 = s2') by reflexivity.
  assert (R19 : lib.Reusable.YK11.getr RT 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
  assert (R23 : lib.Reusable.YK11.getr RT 23 = lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (R25 : lib.Reusable.YK11.getr RT 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
  assert (R26 : lib.Reusable.YK11.getr RT 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (HspR : Reusable.YG0d.spZ RT = sp) by (unfold Reusable.YG0d.spZ; rewrite R2; exact EspZ).
  assert (Era : Reusable.YG0d.raZ RT = 0x81640) by (unfold Reusable.YG0d.raZ; rewrite R1; reflexivity).
  eapply Reusable.YA0n.SRr_bind.
  { apply (w1_aj_set_shadow W3 RT m1' Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx)
             (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 md' k
             (sp - ACtlCut.c_sp cx) (Z_to_bv 64 0x81640) 6 (ACtlCut.c_fpos cx) (ACtlCutP.Sfr fr + 68) 186 HJ1).
    - left; reflexivity.
    - exact R10.
    - exact R11.
    - lia.
    - rewrite Efa. rewrite ESh. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
    - rewrite Efa. rewrite ESh. change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
    - rewrite HspR. lia.
    - rewrite Zminus_mod, Hsp16, Hs16. reflexivity.
    - lia.
    - unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK. lia.
    - rewrite R3, E3. exact Hgp0.
    - rewrite R4. exact Etp.
    - exact R1.
    - apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity. }
  cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR & Hval & Hkeep & Hpres).
  rewrite Era.
  pose proof (w1_rt cx _ ly3 S3 W3 mem2 md2 k HB HJ2) as HRT2.
  assert (P6 : B.ProgWorld.rt_post_frame W3 m1' mem2 ((ACtlCutP.Sfr fr + 68, ACtlCutP.Sfr fr + 68 + 186) :: nil)).
  { split.
    - intros a Ha (Ho & _). exact (Hkeep a Ha Ho).
    - exact Hpres. }
  destruct (B.ProgWorld.ctl_post_set_shadow W3 m1' mem2 (ACtlCutP.Sfr fr + 68) 186 0 ltac:(lia) ltac:(lia)
              ltac:(lia) (fun a Ha => Hshp1 a ltac:(lia)) Hval P6) as (MV & _ & HRW).
  (* the raw reads kept from the cut memory to the post memory: off the pre-run's writes (raw munch) and off the
     fill (munch_vis, visible bytes) *)
  assert (MK : forall lo hi, (forall a, lo <= a < hi -> 0 <= a < 2 ^ 64 /\
                   Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\
                   ~ (ACtlCutP.Sfr fr + 68 <= a < ACtlCutP.Sfr fr + 68 + 186) /\ ~ (A + 8 <= a < A + 16)) ->
                 KEEPR mem3 mem2 lo hi).
  { intros lo hi H a Ha. destruct (H a Ha) as (H1 & H2 & H3 & H4).
    transitivity (lib.Lib.Mem.mrd B.Img0.rsegs m1' (Z_to_bv 64 a)).
    - apply (w1_keep_vis _ _ m1' mem2 a (a + 1) MV); [| lia].
      intros a' Ha'. assert (a' = a) by lia. subst a'. split; [exact H1|]. split; [exact H2|].
      cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
    - apply (w1_keep_munch _ mem3 m1' a (a + 1) MU'); [| lia].
      intros a' Ha'. assert (a' = a) by lia. subst a'. split; [exact H1|].
      cbn [lib.Lib.Frame.outside]. split; [lia|]. split; [lia | exact I]. }
  assert (KST : forall lo hi, sp <= lo -> hi <= ACtlCut.c_sp cx -> (hi <= A + 8 \/ A + 16 <= lo) ->
                  KEEPR mem3 mem2 lo hi).
  { intros lo hi H1 H2 H3. apply MK. intros a Ha. split; [lia|].
    split; [exact (proj1 (Hwin a ltac:(lia)))|]. rewrite ESh. Z.div_mod_to_equations. lia. }
  assert (KFR : KEEPR mem3 mem2 fr (fr + 4096)).
  { apply MK. intros a Ha. split; [lia|]. split; [exact (proj1 (proj1 (Hfb a ltac:(lia))))|].
    destruct (Hdisj a Ha); lia. }
  assert (KSP : forall i, 0 <= i < 392 ->
                  exists b, lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa (ACtlCutP.Sfr fr + i)) = Some b)
    by exact (w1_fsh_rd cx ly3 S3 W3 mem2 md2 k fr HJ2 Hfr Efr).
  assert (CSV : forall z, 2 <= z <= 4 \/ 8 <= z <= 9 \/ 18 <= z <= 27 -> Reusable.YG0d.acallee_saved z)
    by (intros z Hz'; unfold Reusable.YG0d.acallee_saved; lia).
  assert (F2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
    by (apply (w1_pres_reg RT regs2 regs3 2); [exact HPR | apply CSV; lia | apply bv_eq; reflexivity | exact R2]).
  assert (F3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
    by (apply (w1_pres_reg RT regs2 regs3 3); [exact HPR | apply CSV; lia | apply bv_eq; reflexivity | exact R3]).
  assert (F4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
    by (apply (w1_pres_reg RT regs2 regs3 4); [exact HPR | apply CSV; lia | apply bv_eq; reflexivity | exact R4]).
  assert (F8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
    by (apply (w1_pres_reg RT regs2 regs3 8); [exact HPR | apply CSV; lia | apply bv_eq; reflexivity | exact R8]).
  assert (F9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
    by (apply (w1_pres_reg RT regs2 regs3 9); [exact HPR | apply CSV; lia | apply bv_eq; reflexivity | exact R9]).
  assert (F18 : lib.Reusable.YK11.getr regs2 18 = s2')
    by (rewrite <- R18; apply (w1_pres_reg RT regs2 RT 18); [exact HPR | apply CSV; lia | apply bv_eq; reflexivity |
                                                            reflexivity]).
  assert (F19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
    by (apply (w1_pres_reg RT regs2 regs3 19); [exact HPR | apply CSV; lia | apply bv_eq; reflexivity | exact R19]).
  assert (F23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
    by (apply (w1_pres_reg RT regs2 regs3 23); [exact HPR | apply CSV; lia | apply bv_eq; reflexivity | exact R23]).
  assert (F25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
    by (apply (w1_pres_reg RT regs2 regs3 25); [exact HPR | apply CSV; lia | apply bv_eq; reflexivity | exact R25]).
  assert (F26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
    by (apply (w1_pres_reg RT regs2 regs3 26); [exact HPR | apply CSV; lia | apply bv_eq; reflexivity | exact R26]).
  assert (R9' : ACtlCut.rgv regs2 9 A) by (unfold ACtlCut.rgv; rewrite F9; exact E9).
  assert (SP : forall off v, 0 <= off -> off + 8 <= 448 -> (off + 8 <= 8 \/ 16 <= off) ->
                 ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill regs2 mem2 off v).
  { intros off v H0 H1 H2 Hs.
    apply (w1_spill_mv regs3 regs2 mem3 mem2 A off v E9 ltac:(lia) ltac:(lia) H0 H1 F9); [|exact Hs].
    apply KST; lia. }
  apply (H640 cx idx fr k ly3 S3 W3 regs2 mem2 md2 HB HJ2 Hfr HFA Hk).
  - unfold ACtlCutP.C_B81640. cbn [ACtlCut.cut_body].
    split; [exact Hperm|].
    split.
    { apply (w1_frac_mv cx fr fr A regs3 regs2 mem3 mem2 E9 ltac:(lia) F2 F3 F4 F8 F9 F19 F26);
        [apply KST; lia | apply KST; lia | intros a Ha; apply KFR; lia | exact KSP | apply KST; lia |
         intros a Ha; apply KFR; lia | exact HFRAC]. }
    split; [exact Hn|].
    split; [exact (w1_cur_regs cx 7 regs3 regs2 F23 F25 HCUR)|].
    split; [unfold ACtlCutP.OURb in *; apply (w1_bytes_keep mem3 mem2); [| exact HOUR];
            rewrite ACtlCutP.SM.OUR_length; intros a Ha; apply KFR; lia|].
    split; [apply SP; [lia | lia | lia | exact S144]|].
    split; [apply SP; [lia | lia | lia | exact S112]|].
    split; [apply SP; [lia | lia | lia | exact S312]|].
    split; [apply SP; [lia | lia | lia | exact S264]|].
    split; [apply SP; [lia | lia | lia | exact S56]|].
    split; [apply SP; [lia | lia | lia | exact S184]|].
    split.
    { apply (B.Prog.Seg.R3.r3_addr_z mem2 (fr + 544) 186 1488); [reflexivity | lia | | unfold B.AsanRT.APPMEM_END; lia
        | intros i Hi; apply (w1_frame_app fr); [exact Happ | lia] |].
      - replace (fr + 544) with (fr + 68 * 8) by lia. rewrite Z_mod_plus_full. exact Hfr8.
      - replace (fr + 544) with (fr + 8 * 68) by lia. rewrite (ESA 68 ltac:(lia)).
        destruct HRW as ((_ & HBQ) & _).
        cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in HBQ. rewrite app_nil_r in HBQ. exact HBQ. }
    split.
    { apply (w1_spill_of regs2 mem2 A 8 _ R9'). unfold ACtlCutP.q64.
      apply (w1_bytes_keep m1' mem2); [| exact B11'].
      rewrite lib.Lib.Mem.length_le8. change (Z.of_nat 8) with 8. intros a Ha.
      apply (w1_keep_vis _ _ m1' mem2 (A + 8) (A + 16) MV); [| lia]. intros a' Ha'.
      split; [lia|]. split; [exact (proj1 (Hwin a' ltac:(lia)))|].
      cbn [lib.Lib.Frame.outside]. rewrite ESh. split; [Z.div_mod_to_equations; lia | exact I]. }
    split.
    { unfold ACtlCut.rgv. rewrite F18, Es2, U22r. reflexivity. }
    split.
    { apply (w1_addr_keep mem3 mem2); [| exact HA2624]. intros i Hi.
      apply (MK (B.AsanRT.shadow_addr (fr + 2624 + i)) (B.AsanRT.shadow_addr (fr + 2624 + i) + 1)); [| lia].
      intros a Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
      split; [Z.div_mod_to_equations; lia|].
      split; [apply Hshp; rewrite ESh; Z.div_mod_to_equations; lia|].
      rewrite ESh. Z.div_mod_to_equations. lia. }
    split; [apply SP; [lia | lia | lia | exact S96]|].
    split; [apply SP; [lia | lia | lia | exact S120]|].
    split; [apply SP; [lia | lia | lia | exact S240]|].
    split; [apply SP; [lia | lia | lia | exact S232]|].
    split; [apply SP; [lia | lia | lia | exact S224]|].
    split; [apply SP; [lia | lia | lia | exact S176]|].
    split; [apply SP; [lia | lia | lia | exact S208]|].
    split; [apply SP; [lia | lia | lia | exact S64]|].
    split.
    { unfold ACtlCutP.PRA in *.
      destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
      repeat match goal with |- _ /\ _ => split end; apply SP; (lia || assumption). }
    split; [apply SP; [lia | lia | lia | exact S152]|].
    apply SP; [lia | lia | lia | exact S160].
  - exact HRT2.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81640 (0x81640, own6, k <= 0) --S_R3--> B8168c.
   S_R3 (Seg/R3.v seg_R3 :714): R3F.r3_pre_F (0x81640 -> reac_identity_init 0x87de8 with ra = 0x8168c, a0 = fr + 2176:
   the fifteen shadow stores [S(fr) + 254, S(fr) + 291) and the load [A + 144]), reac_identity_init by its footprint
   contract (reac_identity_init_F_holds_closed) and R3F.r3_post_F (zero steps at 0x8168c), all on MemNorm.normalize
   of the cut memory (the mem_inv premises); B.ProgWorld.rebase_ro_normalize carries the run back.  The shadow bytes
   04 at S(fr) + 254, 00 00 00 00 06 at S(fr) + 272 and nine 00 at S(fr) + 282 make out[]'s last 4 bytes, the 38 id
   bytes and the 72 fragment bytes addressable; the id bytes are ID0 = RID _ 0.  No trap, no sink. *)
Lemma seg_R3 : forall POST,
  ctl_from POST C_B8168c ->
  ctl_from POST C_B81640.
Proof.
  intros POST H68c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ACtlCutP.C_B81640 in HJ, Hfr, HFA, Hk, HBODY |- *.
  cbn [ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body ACtlCut.cut_pc] in HJ, Hfr, HFA, Hk, HBODY |- *.
  pose proof (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)) as Efr.
  destruct (w1_frame cx ly3 S3 W3 mem3 md3 k HJ Hfr) as (Hin & Efa & Hf0 & Hf1 & Happ & Hfb & Hfsh).
  rewrite <- Efr in Efa, Hf0, Hf1, Happ, Hfb, Hfsh.
  pose proof (FRAME_ABOVE ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (proj1 HJ) Hin) as Hfhi.
  rewrite Efa in Hfhi.
  destruct (w1_stack cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hs0 & Hs47 & Hs16 & Hwin).
  destruct (w1_stk_ly cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hly0 & Hly1).
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  pose proof Happ as Happ'.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Happ'.
  pose proof (w1_shp W3 mem3 fr Hfsh) as Hshp.
  destruct HBODY as (Hperm & HFRAC & Hn & HCUR & HOUR & S144 & S112 & S312 & S264 & S56 & S184 & HA544 & S8 & H18 &
                     HA2624 & S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HPRA & S152 & S160).
  pose proof HFRAC as (A & sp & Esp & Hsp16 & EspZ & Etp & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HSsp & HSapp & Q336 & Q48 & Q40 & Qhdr & Q16 & Hsh & Hsav & Qtr).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  pose proof (w1_spZ_range regs3) as Hspr. rewrite EspZ in Hspr.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (U2r : bv_unsigned (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 2) = sp) by exact EspZ.
  assert (ESh : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000)
    by (unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; reflexivity).
  assert (ESA : forall X, 0 <= X -> B.AsanRT.shadow_addr (fr + 8 * X) = ACtlCutP.Sfr fr + X).
  { intros X HX. rewrite ESh. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
    replace (fr + 8 * X) with (fr + X * 8) by lia. rewrite Z.div_add by lia. lia. }
  pose proof HRT as (HAC & HSWc & _ & HRO).
  assert (HROn : B.MemNorm.ro_agree B.Img0.rsegs mem3) by exact HRO.
  pose proof (B.MemNormTr.asan_cells_normalize mem3 HROn HAC) as HACn.
  (* route (C): the callee's region (the 38 id bytes' shadow word cover) is the owned frame's shadow, the cut's (F)
     region; shadow_rw_on over it is kept by normalize (ShadowRwOnT.shadow_rw_on_normalize). *)
  assert (HSWn : B.ShadowRwOn.shadow_rw_on (B.Prog.reac_identity_init_c.reac_identity_init_shadow_R (fr + 2176))
                   (B.MemNorm.normalize B.Img0.rsegs mem3)).
  { apply (B.ShadowRwOnT.shadow_rw_on_normalize _ mem3 HROn).
    apply (B.ShadowRwOn.shadow_rw_on_mono (B.ACtlRtC.cut_shadow B ly3 S3)); [| exact HSWc].
    intros a (_ & _ & Ha). apply (w1_frame_cut_shadow ly3 S3 (ACtlCut.c_fpos cx) fr 2176 38 Hin Efa); lia. }
  pose proof (B.MemNorm.mem_inv_normalize B.Img0.rsegs mem3) as HMIn.
  (* the 37 shadow bytes, the 38 id bytes and the stack window, on the normalized memory *)
  destruct (w1_rw_present _ mem3 (ACtlCutP.Sfr fr + 254) 37 ltac:(lia) ltac:(lia)
              ltac:(intros a Ha; apply Hshp; lia)) as (xs & Hxl & CX).
  assert (CXn : lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) (ACtlCutP.Sfr fr + 254)
                  (map lib.Lib.Cells.C1 xs)).
  { apply (w1_rw_C1 _ _ 37 xs); [| exact Hxl].
    apply (B.MemNormTr.rw_cells_normalize mem3 _ _ HROn); [| exact CX].
    intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi. apply w1_ro_hi. lia. }
  destruct (w1_rw_present _ mem3 (fr + 2176) 38 ltac:(lia) ltac:(lia)
              ltac:(intros a Ha; exact (proj1 (Hfb a ltac:(lia))))) as (idb & Hidl & CI).
  assert (CIn : lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) (fr + 2176)
                  (lib.Lib.Cells.CB 38 idb :: nil)).
  { apply (B.MemNormTr.rw_cells_normalize mem3 _ _ HROn); [| exact CI].
    intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi. apply w1_ro_hi. lia. }
  assert (STn : lib.Lib.Frame.stk B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) (sp - 2224) sp).
  { apply (B.MemNormTr.stk_normalize_ro mem3 _ _ HROn); [unfold B.Prog.ImgBounds.IMG_HI; lia|].
    apply (w1_stk_pres (Reusable.YA0n.w_H W3)); [lia | lia | intros a Ha; apply Hwin; lia]. }
  pose proof (w1_spill_at regs3 mem3 A 144 (fr + 2176) E9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S144) as Q144.
  pose proof (B.MemNorm.bytes_at_normalize B.Img0.rsegs mem3 _ _ HROn Q144) as Q144n.
  destruct (w1_win_sh_vis ly3 S3 W3 mem3 md3 (sp - 2224) 2224 (proj1 HJ) ltac:(lia) ltac:(lia) ltac:(lia))
    as [E0|VW]; [lia|].
  pose proof (w1_sh_exact _ (sp - 2224) 2224 ltac:(lia) ltac:(lia) VW) as VWe.
  replace (sp - 2224 + 2224 - 1) with (sp - 1) in VWe by lia.
  pose proof (w1_frame_sh_vis W3 mem3 fr 2176 38 Hfsh ltac:(lia) ltac:(lia) Hfr8 ltac:(lia) ltac:(lia) ltac:(lia))
    as VID.
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr in VID.
  replace (fr + 2176 + 38 - 1) with (fr + 2176 + 37) in VID by lia.
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  evar (Pq : machine_state -> Prop).
  assert (HRUN : Lib.ExecF.evtF B.Img0.rsegs RNG Pq
                   (lib.Lib.MState.MS (Lib.Regs6ss.mkR_of regs3) lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x81640)
                      lib.Reusable.YK11.fp_csr None (B.MemNorm.normalize B.Img0.rsegs mem3)
                      (lib.Lib.PropExec.seg_rom B.Img0.rsegs))).
  { unfold Pq, Lib.Regs6ss.mkR_of.
    eapply (Lib.ExecF.evtF_cut B.Img0.rsegs RNG).
    { eapply (B.Prog.Seg.R3F.r3_pre_F_on RNG) with (spv := sp)
        (Sh := ACtlCutP.Sfr fr) (Ab := A) (idp := fr + 2176)
        (lo := sp - 2224) (xs := xs) (idb := idb).
      - exact Esp.
      - exact E19.
      - exact E9.
      - rewrite ESh. unfold B.AsanRT.RT_HI. lia.
      - rewrite ESh. lia.
      - unfold B.AsanRT.HIGHMEM_BEG. lia.
      - lia.
      - unfold B.AsanRT.APPMEM_END. lia.
      - rewrite ESh. lia.
      - lia.
      - rewrite ESh. lia.
      - unfold B.AsanRT.RT_HI. lia.
      - replace (fr + 2176) with (fr + 272 * 8) by lia. rewrite Z_mod_plus_full. exact Hfr8.
      - replace (fr + 2176) with (fr + 8 * 272) by lia. exact (ESA 272 ltac:(lia)).
      - intros a Ha. apply (w1_frame_app fr); [exact Happ | lia].
      - left. lia.
      - exact Hxl.
      - exact CXn.
      - exact CIn.
      - apply B.Prog.Seg.R3.r3_ro8. exact Q144n.
      - exact HMIn.
      - exact STn.
      - exact HACn.
      - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
        intros a Ha. exact (proj1 (Hshp a ltac:(lia))).
      - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
        intros a Ha. exact (proj1 (Hwin a ltac:(lia))). }
    intros ms1 (m1 & E1 & MID & TR1). subst ms1.
    pose proof MID as (MU1 & WM1 & MI1 & ST1 & AC1 & AD1 & RW1 & B0 & B18 & B28).
    eapply (Lib.ExecF.evtF_cut B.Img0.rsegs RNG).
    { eapply (reac_identity_init_F_holds_on RNG) with (lo := sp - 2224) (id := fr + 2176) (idb := idb);
        rewrite ?U2r; unfold B.Prog.reac_identity_init_c.REAC_IDENTITY_INIT_K.
      - reflexivity.
      - lia.
      - intros _. split; [| exact RW1].
        replace (fr + 2176) with (fr + 1088 * 2) by lia. rewrite Z_mod_plus_full. clear - Hfr8.
        Z.div_mod_to_equations. lia.
      - exact MI1.
      - exact ST1.
      - lia.
      - unfold B.AsanRT.HIGHMEM_BEG. lia.
      - unfold B.AsanRT.APPMEM_END. lia.
      - exact AC1.
      - exact (TR1 _ HSWn).
      - intros _. split; [exact AD1|]. right. apply (w1_frame_app fr); [exact Happ | lia].
      - intros _. right. unfold B.AsanRT.RT_HI. lia.
      - intros _. left. lia.
      - exact (B.ProgBridge.rng_bytes_RNG_W _).
      - exact (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.img_vis_W W3)).
      - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
        intros a Ha. exact (proj1 (Hwin a ltac:(lia))).
      - right. exact (B.ProgBridge.rng_of_visible _ _ _ VW).
      - exact (B.ProgBridge.rng_of_visible _ _ _ VWe).
      - exact (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.rt_vis_W W3)).
      - intros _. split.
        + apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
          intros a Ha. exact (proj1 (proj1 (Hfb a ltac:(lia)))).
        + exact (B.ProgBridge.rng_of_visible _ _ _ VID). }
    intros ms2 PO. unfold B.Prog.reac_identity_init_c.reac_identity_init_post_on in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                    E2 & MU2 & WM2 & MI2 & ST2 & AC2 & SW2 & _ & RW2).
    subst ms2.
    unfold B.Prog.reac_identity_init_c.reac_identity_init_W, B.Prog.reac_identity_init_c.REAC_IDENTITY_INIT_K in MU2.
    rewrite ?U2r in MU2, ST2.
    (* r3_Q_on names the return-point memory m2 (the forall-P transport's source); the run's post closes it. *)
    eapply (Lib.ExecF.evtF_mono B.Img0.rsegs RNG).
    { eapply (B.Prog.Seg.R3F.r3_post_F_on RNG) with (spv := sp)
        (Sh := ACtlCutP.Sfr fr) (idp := fr + 2176) (lo := sp - 2224)
        (idb := idb) (m1 := m1).
      - rewrite ESh. lia.
      - lia.
      - rewrite ESh. lia.
      - exact MID.
      - exact MU2.
      - exact WM2.
      - exact MI2.
      - exact ST2.
      - exact AC2.
      - exact (RW2 ltac:(lia)). }
    intros msq HQ.
    match type of HQ with
    | B.Prog.Seg.R3F.r3_Q_on ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13 _ ?a15 ?a16 ?a17 ?a18 msq =>
        exact (ex_intro (fun m2' => B.Prog.Seg.R3F.r3_Q_on a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 m2' a15 a16 a17
                                      a18 msq) m2 HQ)
    end. }
  apply (w1_lift_n W3 regs3 mem3 md3 0x81640 RNG Pq (POST cx) HROn HRUN (B.ProgBridge.fp_avoids_RNG_W _)).
  intros ms' md' s0 PO Hrel Hby Hmu Hwm Hhid Hsbm.
  unfold Pq in PO. destruct PO as (m2q & PO). unfold B.Prog.Seg.R3F.r3_Q_on in PO.
  destruct PO as (R & m0 & Es0 & HR2 & HR3 & HR4 & HR8 & HR9 & HR18 & HR19 & HR23 & HR25 & HR26 & MUQ & WMQ & _ & _ &
                  _ & _ & RWQ & B254 & B272 & B282).
  subst s0.
  destruct (B.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Ems _].
  rewrite Ems.
  pose proof (Hmu _ MUQ) as MU'. pose proof (Hwm WMQ) as WM'.
  set (m' := ms_mem ms') in *.
  assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { apply (w1_journal_run cx _ ly3 S3 W3 mem3 md3 k m' md' _ HJ MU' WM' Hhid Hsbm).
    intros a Ha Hni. cbn [lib.Lib.Frame.outside] in Hni. split.
    - destruct (Z_lt_le_dec a (sp - 2224)) as [Hlt|Hge].
      + right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
        unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa.
        change (Reusable.YG00.fs_frame_bytes 6) with 4096. change (4096 / 8) with 512.
        unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. rewrite ESh in Hni. lia.
      + left. unfold Reusable.YCfn.LLVMF_STK. lia.
    - intros Hi. apply w1_img in Hi. rewrite ESh in Hni. lia. }
  pose proof (w1_rt cx _ ly3 S3 W3 m' md' k HB HJ') as HRT'.
  assert (KSP : forall i, 0 <= i < 392 ->
                  exists b, lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa (ACtlCutP.Sfr fr + i)) = Some b)
    by exact (w1_fsh_rd cx ly3 S3 W3 m' md' k fr HJ' Hfr Efr).
  assert (MK : forall x, 0 <= x < 2 ^ 64 -> ~ (ACtlCutP.Sfr fr + 254 <= x < ACtlCutP.Sfr fr + 291) ->
                 ~ (sp - 2224 <= x < sp) -> ~ (fr + 2176 <= x < fr + 2176 + 38) ->
                 lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
  { intros x Hx H1 H2 H3. apply (w1_keep_munch _ mem3 m' x (x + 1) MU'); [| lia].
    intros a Ha. split; [lia|]. cbn [lib.Lib.Frame.outside]. lia. }
  assert (MKR : forall lo hi, (forall x, lo <= x < hi -> 0 <= x < 2 ^ 64 /\
                   ~ (ACtlCutP.Sfr fr + 254 <= x < ACtlCutP.Sfr fr + 291) /\ ~ (sp - 2224 <= x < sp) /\
                   ~ (fr + 2176 <= x < fr + 2176 + 38)) -> KEEPR mem3 m' lo hi)
    by (intros lo hi H x Hx; destruct (H x Hx) as (H1 & H2 & H3 & H4); exact (MK x H1 H2 H3 H4)).
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R0 _ _ _ _ _ _) _) _ =>
    set (RT := R0) end.
  assert (G2 : lib.Reusable.YK11.getr RT 2 = lib.Reusable.YK11.getr regs3 2) by exact HR2.
  assert (G3 : lib.Reusable.YK11.getr RT 3 = lib.Reusable.YK11.getr regs3 3) by exact HR3.
  assert (G4 : lib.Reusable.YK11.getr RT 4 = lib.Reusable.YK11.getr regs3 4) by exact HR4.
  assert (G8 : lib.Reusable.YK11.getr RT 8 = lib.Reusable.YK11.getr regs3 8) by exact HR8.
  assert (G9 : lib.Reusable.YK11.getr RT 9 = lib.Reusable.YK11.getr regs3 9) by exact HR9.
  assert (G18 : lib.Reusable.YK11.getr RT 18 = lib.Reusable.YK11.getr regs3 18) by exact HR18.
  assert (G19 : lib.Reusable.YK11.getr RT 19 = lib.Reusable.YK11.getr regs3 19) by exact HR19.
  assert (G23 : lib.Reusable.YK11.getr RT 23 = lib.Reusable.YK11.getr regs3 23) by exact HR23.
  assert (G25 : lib.Reusable.YK11.getr RT 25 = lib.Reusable.YK11.getr regs3 25) by exact HR25.
  assert (G26 : lib.Reusable.YK11.getr RT 26 = lib.Reusable.YK11.getr regs3 26) by exact HR26.
  assert (SP : forall off v, 0 <= off -> off + 8 <= 448 ->
                 ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill RT m' off v).
  { intros off v H0 H1 Hs. apply (w1_spill_mv regs3 RT mem3 m' A off v E9 ltac:(lia) ltac:(lia) H0 H1 G9); [|exact Hs].
    apply MKR. intros x Hx. rewrite ESh. split; lia. }
  assert (AKS : forall X n, 0 <= X -> 0 <= n -> X + n <= 2032 \/ 2328 <= X -> X + n <= ACtlCutP.FRAME_BYTES ->
                  B.AsanRT.addressable mem3 (fr + X) n -> B.AsanRT.addressable m' (fr + X) n).
  { intros X n H1 H2 H3 H4. apply w1_addr_keep. intros i Hi. unfold ACtlCutP.FRAME_BYTES in H4.
    apply MK; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; rewrite ?ESh; Z.div_mod_to_equations; lia. }
  apply (H68c cx idx fr k ly3 S3 W3 RT m' md' HB HJ' Hfr HFA Hk).
  - unfold ACtlCutP.C_B8168c. cbn [ACtlCut.cut_body].
    split; [exact Hperm|].
    split.
    { apply (w1_frac_mv cx fr fr A regs3 RT mem3 m' E9 ltac:(lia) G2 G3 G4 G8 G9 G19 G26); try exact KSP;
        try exact HFRAC; apply MKR; intros x Hx; rewrite ESh; split; lia. }
    split; [exact Hn|].
    split; [destruct HCUR as (Hc & H23 & H25); split; [exact Hc|];
            split; [exact (w1_rgv_move RT regs3 23 _ G23 H23) | exact (w1_rgv_move RT regs3 25 _ G25 H25)]|].
    split; [unfold ACtlCutP.OURb in *; apply (w1_bytes_keep mem3 m'); [| exact HOUR];
            rewrite ACtlCutP.SM.OUR_length; apply MKR; intros x Hx; rewrite ESh; split; lia|].
    split.
    { unfold ACtlCutP.IDBr. destruct RWQ as ((_ & HBQ) & _).
      cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in HBQ. rewrite app_nil_r in HBQ.
      exact (proj2 (Hby _ _) HBQ). }
    split.
    { apply (B.Prog.Seg.R3.r3_addr_z m' (fr + 2256) 9 72); [reflexivity | lia | | unfold B.AsanRT.APPMEM_END; lia
        | intros i Hi; apply (w1_frame_app fr); [exact Happ | lia] |].
      - replace (fr + 2256) with (fr + 282 * 8) by lia. rewrite Z_mod_plus_full. exact Hfr8.
      - replace (fr + 2256) with (fr + 8 * 282) by lia. rewrite (ESA 282 ltac:(lia)).
        exact (proj2 (Hby _ _) B282). }
    split; [apply SP; [lia | lia | exact S112]|].
    split; [apply SP; [lia | lia | exact S312]|].
    split; [apply SP; [lia | lia | exact S264]|].
    split; [apply SP; [lia | lia | exact S56]|].
    split; [apply SP; [lia | lia | exact S184]|].
    split.
    { replace 1492 with (1488 + 4) by lia. apply B.Prog.Seg.R3.r3_addr_cat.
      - apply AKS; [lia | lia | lia | unfold ACtlCutP.FRAME_BYTES; lia | exact HA544].
      - replace (fr + 544 + 1488) with (fr + 2032) by lia.
        apply (B.Prog.Seg.R3.r3_addr_r m' (fr + 2032) 4 (Z_to_bv 8 4)); [lia | | lia | reflexivity
          | unfold B.AsanRT.APPMEM_END; lia | intros i Hi; apply (w1_frame_app fr); [exact Happ | lia] |].
        + replace (fr + 2032) with (fr + 254 * 8) by lia. rewrite Z_mod_plus_full. exact Hfr8.
        + replace (fr + 2032) with (fr + 8 * 254) by lia. rewrite (ESA 254 ltac:(lia)).
          exact (proj2 (Hby _ _) B254). }
    split.
    { apply B.Prog.Seg.R3.r3_id_addr; [lia | | unfold B.AsanRT.APPMEM_END; lia
        | intros i Hi; apply (w1_frame_app fr); [exact Happ | lia] |].
      - replace (fr + 2176) with (fr + 272 * 8) by lia. rewrite Z_mod_plus_full. exact Hfr8.
      - replace (fr + 2176) with (fr + 8 * 272) by lia. rewrite (ESA 272 ltac:(lia)).
        exact (proj2 (Hby _ _) B272). }
    split; [apply SP; [lia | lia | exact S144]|].
    split; [apply SP; [lia | lia | exact S8]|].
    split; [exact (w1_rgv_move RT regs3 18 _ G18 H18)|].
    split; [apply AKS; [lia | lia | lia | unfold ACtlCutP.FRAME_BYTES; lia | exact HA2624]|].
    split; [apply SP; [lia | lia | exact S96]|].
    split; [apply SP; [lia | lia | exact S120]|].
    split; [apply SP; [lia | lia | exact S240]|].
    split; [apply SP; [lia | lia | exact S232]|].
    split; [apply SP; [lia | lia | exact S224]|].
    split; [apply SP; [lia | lia | exact S176]|].
    split; [apply SP; [lia | lia | exact S208]|].
    split; [apply SP; [lia | lia | exact S64]|].
    split.
    { unfold ACtlCutP.PRA in *.
      destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
      repeat match goal with |- _ /\ _ => split end; apply SP; (lia || assumption). }
    split; [apply SP; [lia | lia | exact S152]|].
    apply SP; [lia | lia | exact S160].
  - exact HRT'.
Qed.


(* ---------------------------------------------------------------------------------------------------------
   B8168c (0x8168c, own6, k <= 0) --S_R4--> B8169c.
   S_R4 (Seg/R4.v seg_R4 :682): R4F.r4_pre_F (0x8168c -> __asan_memset 0x52600 with ra = 0x8169c, a0 = fr + 2256,
   a1 = 0, a2 = 72; one load, [A + 112]; no store), then the core's memset rule AMEMSET in journal form
   (YCbq.aj_intrin_at, OSet), returning at 0x8169c = the successor cut.  R4F.r4_post_F (0 steps, raw munch premise) is
   not applied: the post is the world view, and the proved B.ProgWorld.ctl_post_memset turns it into munch_vis and
   rw_cells (fr + 2256) [CB 72 z72] (C_B8169c's FGBr, RFG _ 0 = z72); every other body fact is kept.  FRAC is
   re-established at the new memory (w1_frac_mv).  No trap, no sink. *)
Lemma seg_R4 : forall POST,
  ctl_from POST C_B8169c ->
  ctl_from POST C_B8168c.
Proof.
  intros POST H69c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ACtlCutP.C_B8168c in HJ, Hfr, HFA, Hk, HBODY |- *.
  cbn [ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body ACtlCut.cut_pc] in HJ, Hfr, HFA, Hk, HBODY |- *.
  pose proof (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)) as Efr.
  destruct (w1_frame cx ly3 S3 W3 mem3 md3 k HJ Hfr) as (Hin & Efa & Hf0 & Hf1 & Happ & Hfb & Hfsh).
  rewrite <- Efr in Efa, Hf0, Hf1, Happ, Hfb, Hfsh.
  destruct (w1_stack cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hs0 & Hs47 & Hs16 & Hwin).
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  pose proof Happ as Happ'.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Happ'.
  pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [HcR _]. unfold Reusable.YG0f.ASAN_CEIL in HcR.
  pose proof (w1_shp W3 mem3 fr Hfsh) as Hshp.
  destruct HBODY as (Hperm & HFRAC & Hn & HCUR & HOUR & HIDB & HA2256 & S112 & S312 & S264 & S56 & S184 & HA544 &
                     HA2176 & S144 & S8 & H18 & HA2624 & S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HPRA &
                     S152 & S160).
  pose proof HFRAC as (A & sp & Esp & Hsp16 & EspZ & Etp & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HSsp & HSapp & Q336 & Q48 & Q40 & Qhdr & Q16 & Hsh & Hsav & Qtr).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  pose proof (w1_spZ_range regs3) as Hspr. rewrite EspZ in Hspr.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _ & _ & Hgp0 & _).
  pose proof (w1_spill_at regs3 mem3 A 112 (fr + 2256) E9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S112) as Q112.
  eapply (w1_lift W3 regs3 mem3 md3 0x8168c (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { unfold Lib.Regs6ss.mkR_of.
    eapply (R4F.r4_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (Ab := A) (fg := fr + 2256).
    - exact E9.
    - lia.
    - lia.
    - apply B.Prog.Seg.R4.r4_ro8. exact Q112.
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (Hwin a ltac:(lia))). }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' -> _ Hsbm.
  apply w1_cfg_back. change 0x52600 with Reusable.YB1w.tfib_A_asan_memset.
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (RT := R) end.
  pose proof (w1_journal_mat _ _ _ _ _ _ _ _ _ HJ Hsbm) as HJ'.
  assert (R1 : lib.Reusable.YK11.getr RT 1 = Z_to_bv 64 0x8169c) by reflexivity.
  assert (R2 : lib.Reusable.YK11.getr RT 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (R3 : lib.Reusable.YK11.getr RT 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (R4 : lib.Reusable.YK11.getr RT 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (R8 : lib.Reusable.YK11.getr RT 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (R9 : lib.Reusable.YK11.getr RT 9 = Z_to_bv 64 A) by reflexivity.
  assert (R10 : lib.Reusable.YK11.getr RT 10 = Z_to_bv 64 (fr + 2256)) by reflexivity.
  assert (R11 : lib.Reusable.YK11.getr RT 11 = Z_to_bv 64 0) by reflexivity.
  assert (R12 : lib.Reusable.YK11.getr RT 12 = Z_to_bv 64 72) by reflexivity.
  assert (R18 : lib.Reusable.YK11.getr RT 18 = lib.Reusable.YK11.getr regs3 18) by reflexivity.
  assert (R19 : lib.Reusable.YK11.getr RT 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
  assert (R23 : lib.Reusable.YK11.getr RT 23 = lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (R25 : lib.Reusable.YK11.getr RT 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
  assert (R26 : lib.Reusable.YK11.getr RT 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (G9 : lib.Reusable.YK11.getr RT 9 = lib.Reusable.YK11.getr regs3 9) by (rewrite R9; symmetry; exact E9).
  assert (HspR : Reusable.YG0d.spZ RT = sp) by (unfold Reusable.YG0d.spZ; rewrite R2; exact EspZ).
  unfold Reusable.YG0d.cfg_at, Reusable.YG0d.w64.
  eapply Reusable.YA0n.SRr_bind.
  { eapply (Reusable.YCbq.aj_intrin_at segs B LAWS w1_segs_low Reusable.YG0d.OSet Reusable.YB1w.tfib_A_asan_memset
              AMEMSET W3 RT mem3 Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
              (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
              (ACtlCut.own6 cx) ly3 S3 md' k (fr + 2256) 0 72 (sp - ACtlCut.c_sp cx) (Z_to_bv 64 0x8169c) HJ').
    - exact R10.
    - exact R11.
    - exact R12.
    - lia.
    - lia.
    - lia.
    - rewrite HspR. lia.
    - rewrite Zminus_mod, Hsp16, Hs16. reflexivity.
    - lia.
    - unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK. lia.
    - rewrite R3, E3. exact Hgp0.
    - rewrite R4. exact Etp.
    - exact R1.
    - apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
    - intros a Ha. split.
      + right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |]. left.
        unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa. change (Reusable.YG00.fs_frame_bytes 6) with 4096.
        lia.
      + unfold Reusable.YG0d.ESTACK. lia.
    - unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg,
        Reusable.YG0f.kHighMemEnd. lia.
    - apply w1_range_addr_of_raw; [exact HA2256 |]. intros i Hi.
      refine (proj1 (Hshp _ _)). unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
      Z.div_mod_to_equations. lia.
    - intros _ s Hs. apply w1_aview_of_apresent. apply Hshp.
      unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
        Reusable.YG0f.SHADOW_OFF in *.
      Z.div_mod_to_equations. lia.
    - exact I. }
  cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR & Ha02 & Hset & Hkeep & Hpres).
  pose proof (w1_rt cx _ ly3 S3 W3 mem2 md2 k HB HJ2) as HRT2.
  assert (P9 : B.ProgWorld.rt_post_frame W3 mem3 mem2
                 ((fr + 2256, fr + 2256 + 72) :: (sp - Reusable.YG0d.ESTACK, sp) :: nil)).
  { split.
    - intros a Ha (Ho1 & Ho2 & _). apply Hkeep; [exact Ha | exact Ho1 | unfold Reusable.YG0d.ESTACK in *; lia].
    - exact Hpres. }
  destruct (B.ProgWorld.ctl_post_memset W3 mem3 mem2 sp (fr + 2256) 0 72 ltac:(lia) ltac:(lia) ltac:(lia)
              (fun a Ha => proj1 (Hfb a ltac:(lia))) Hset P9) as (MV & _ & HRW).
  assert (MK : forall lo hi, (forall a, lo <= a < hi -> 0 <= a < 2 ^ 64 /\
                   Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\
                   ~ (fr + 2256 <= a < fr + 2328) /\ ~ (sp - 4096 <= a < sp)) ->
                 KEEPR mem3 mem2 lo hi).
  { intros lo hi H. apply (w1_keep_vis _ _ mem3 mem2 lo hi MV). intros a Ha.
    destruct (H a Ha) as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|].
    cbn [lib.Lib.Frame.outside]. unfold Reusable.YG0d.ESTACK.
    split; [lia|]. split; [lia | exact I]. }
  assert (KST : KEEPR mem3 mem2 sp (ACtlCut.c_sp cx)).
  { apply MK. intros a Ha. split; [lia|]. split; [exact (proj1 (Hwin a ltac:(lia)))|]. lia. }
  assert (KFR : KEEPR mem3 mem2 fr (fr + 2256)).
  { apply MK. intros a Ha. split; [lia|]. split; [exact (proj1 (proj1 (Hfb a ltac:(lia))))|]. lia. }
  assert (KFR2 : KEEPR mem3 mem2 (fr + 2328) (fr + 4096)).
  { apply MK. intros a Ha. split; [lia|]. split; [exact (proj1 (proj1 (Hfb a ltac:(lia))))|]. lia. }
  assert (KS : KEEPR mem3 mem2 (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW)).
  { apply MK. intros a Ha.
    unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in Ha. change (3136 / 8) with 392 in Ha.
    split; [unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha; Z.div_mod_to_equations; lia|].
    split; [exact (proj1 (Hshp a ltac:(lia)))|].
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha. Z.div_mod_to_equations. lia. }
  assert (KSP : forall i, 0 <= i < 392 ->
                  exists b, lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa (ACtlCutP.Sfr fr + i)) = Some b)
    by exact (w1_fsh_rd cx ly3 S3 W3 mem2 md2 k fr HJ2 Hfr Efr).
  assert (CS : forall z, 2 <= z <= 4 \/ 8 <= z <= 9 \/ 18 <= z <= 27 -> Reusable.YG0d.acallee_saved z)
    by (intros z Hz'; unfold Reusable.YG0d.acallee_saved; lia).
  assert (F2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
    by (apply (w1_pres_reg RT regs2 regs3 2); [exact HPR | apply CS; lia | apply bv_eq; reflexivity | exact R2]).
  assert (F3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
    by (apply (w1_pres_reg RT regs2 regs3 3); [exact HPR | apply CS; lia | apply bv_eq; reflexivity | exact R3]).
  assert (F4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
    by (apply (w1_pres_reg RT regs2 regs3 4); [exact HPR | apply CS; lia | apply bv_eq; reflexivity | exact R4]).
  assert (F8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
    by (apply (w1_pres_reg RT regs2 regs3 8); [exact HPR | apply CS; lia | apply bv_eq; reflexivity | exact R8]).
  assert (F9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
    by (apply (w1_pres_reg RT regs2 regs3 9); [exact HPR | apply CS; lia | apply bv_eq; reflexivity | exact G9]).
  assert (F18 : lib.Reusable.YK11.getr regs2 18 = lib.Reusable.YK11.getr regs3 18)
    by (apply (w1_pres_reg RT regs2 regs3 18); [exact HPR | apply CS; lia | apply bv_eq; reflexivity | exact R18]).
  assert (F19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
    by (apply (w1_pres_reg RT regs2 regs3 19); [exact HPR | apply CS; lia | apply bv_eq; reflexivity | exact R19]).
  assert (F23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
    by (apply (w1_pres_reg RT regs2 regs3 23); [exact HPR | apply CS; lia | apply bv_eq; reflexivity | exact R23]).
  assert (F25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
    by (apply (w1_pres_reg RT regs2 regs3 25); [exact HPR | apply CS; lia | apply bv_eq; reflexivity | exact R25]).
  assert (F26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
    by (apply (w1_pres_reg RT regs2 regs3 26); [exact HPR | apply CS; lia | apply bv_eq; reflexivity | exact R26]).
  assert (SP : forall off v, 0 <= off -> off + 8 <= 448 ->
                 ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill regs2 mem2 off v).
  { intros off v H0 H1 Hs.
    apply (w1_spill_mv regs3 regs2 mem3 mem2 A off v E9 ltac:(lia) ltac:(lia) H0 H1 F9); [|exact Hs].
    intros a Ha. apply KST. lia. }
  assert (AK : forall X n, 0 <= X -> 0 <= n -> X + n <= ACtlCutP.FRAME_BYTES ->
                 B.AsanRT.addressable mem3 (fr + X) n -> B.AsanRT.addressable mem2 (fr + X) n)
    by (intros X n H1 H2 H3; exact (w1_faddr_keep mem3 mem2 fr X n KS Hfr8 H1 H2 H3)).
  apply (H69c cx idx fr k ly3 S3 W3 regs2 mem2 md2 HB HJ2 Hfr HFA Hk).
  - unfold ACtlCutP.C_B8169c. cbn [ACtlCut.cut_body].
    split; [exact Hperm|].
    split.
    { apply (w1_frac_mv cx fr fr A regs3 regs2 mem3 mem2 E9 ltac:(lia) F2 F3 F4 F8 F9 F19 F26);
        [intros a Ha; apply KST; lia | intros a Ha; apply KST; lia | intros a Ha; apply KFR; lia | exact KSP |
         intros a Ha; apply KST; lia | intros a Ha; apply KFR2; lia | exact HFRAC]. }
    split; [exact Hn|].
    split; [exact (w1_cur_regs cx 7 regs3 regs2 F23 F25 HCUR)|].
    split; [unfold ACtlCutP.OURb in *; apply (w1_bytes_keep mem3 mem2); [| exact HOUR];
            rewrite ACtlCutP.SM.OUR_length; intros a Ha; apply KFR2; lia|].
    split; [unfold ACtlCutP.IDBr in *; apply (w1_bytes_keep mem3 mem2); [| exact HIDB];
            rewrite B.Prog.Seg.RtmB.rb_RID_len; intros a Ha; apply KFR; lia|].
    split.
    { unfold ACtlCutP.FGBr. destruct HRW as ((_ & HB2) & _).
      cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in HB2. rewrite app_nil_r in HB2. exact HB2. }
    split; [apply SP; [lia | lia | exact S312]|].
    split; [apply SP; [lia | lia | exact S264]|].
    split; [apply SP; [lia | lia | exact S56]|].
    split; [apply SP; [lia | lia | exact S184]|].
    split; [apply SP; [lia | lia | exact S144]|].
    split; [apply SP; [lia | lia | exact S8]|].
    split; [exact (w1_rgv_move regs2 regs3 18 _ F18 H18)|].
    split; [apply AK; [lia | lia | unfold ACtlCutP.FRAME_BYTES; lia | exact HA2624]|].
    split; [unfold ACtlCutP.OUTA; apply AK; [lia | lia | unfold ACtlCutP.FRAME_BYTES; lia | exact HA544]|].
    split; [apply SP; [lia | lia | exact S96]|].
    split; [apply SP; [lia | lia | exact S120]|].
    split; [apply SP; [lia | lia | exact S240]|].
    split; [apply SP; [lia | lia | exact S232]|].
    split; [apply SP; [lia | lia | exact S224]|].
    split; [apply SP; [lia | lia | exact S176]|].
    split; [apply SP; [lia | lia | exact S208]|].
    split; [apply SP; [lia | lia | exact S64]|].
    split.
    { unfold ACtlCutP.PRA in *.
      destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
      repeat match goal with |- _ /\ _ => split end; apply SP; (lia || assumption). }
    split; [apply SP; [lia | lia | exact S152]|].
    split; [apply SP; [lia | lia | exact S112]|].
    split; [apply AK; [lia | lia | unfold ACtlCutP.FRAME_BYTES; lia | exact HA2176]|].
    split; [apply AK; [lia | lia | unfold ACtlCutP.FRAME_BYTES; lia | exact HA2256]|].
    split; [exact (w1_name ly3 S3 W3 mem2 md2 (ACtlCut.c_in cx) (proj1 HJ2) HRT2)|].
    apply SP; [lia | lia | exact S160].
  - exact HRT2.
Qed.
(* ---------------------------------------------------------------------------------------------------------
   B8169c (0x8169c, own6, k <= 0) --S_R5--> B816ec_at [0].
   S_R5 (Seg/R5.v seg_R5 :606): R5F.r5_evt_F (0x8169c -> 0x816ec, 20 instructions, no call, no trap, no sink): the
   b = 0 constants of the round trip (s5 = 36, s6 = 0, s11 = 32) and the round-trip spills [A + 16, A + 40),
   [A + 128], [A + 248], [A + 256], [A + 272], all in the journal's stack window.  The image data of RBE / R6X (the
   CTRL_FRAMES rows, the box, the turn's catalogue row) come from the kept read-only view (w1_tbl_bytes,
   w1_row_bytes) and ro_agree (w1_box_bytes). *)
Lemma seg_R5 : forall POST,
  ctl_from POST (ix_cut C_B816ec_at [Z.of_nat 0]) ->
  ctl_from POST C_B8169c.
Proof.
  intros POST H6ec cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ACtlCutP.C_B8169c in HJ, Hfr, HFA, Hk, HBODY |- *.
  cbn [ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body ACtlCut.cut_pc] in HJ, Hfr, HFA, Hk, HBODY |- *.
  pose proof (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)) as Efr.
  destruct (w1_frame cx ly3 S3 W3 mem3 md3 k HJ Hfr) as (Hin & Efa & Hf0 & Hf1 & Happ & Hfb & Hfsh).
  rewrite <- Efr in Efa, Hf0, Hf1, Happ, Hfb, Hfsh.
  destruct (w1_stack cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hs0 & Hs47 & Hs16 & Hwin).
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  destruct HBODY as (Hperm & HFRAC & Hn & HCUR & HOUR & HIDB & HFGB & S312 & S264 & S56 & S184 & S144 & S8 &
                     H18 & HA2624 & HOUTA & S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HPRA & S152 &
                     S112 & HA2176 & HA2256 & HNAME & S160).
  pose proof HFRAC as (A & sp & Esp & Hsp16 & EspZ & Etp & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HSsp & HSapp & Q336 & Q48 & Q40 & Qhdr & Q16 & Hsh & Hsav & Qtr).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  pose proof (w1_spZ_range regs3) as Hspr. rewrite EspZ in Hspr.
  pose proof (B.Prog.Seg.R6.r6_mrow_rng (ACtlCut.c_in cx)) as (Hmr & Hm8).
  change B.Prog.SlotModel.mrow with ACtlCutP.SM.mrow in Hmr, Hm8.
  unfold B.Prog.SlotModel.CAT in Hmr.
  (* the image data at the cut memory *)
  pose proof (w1_aro cx _ ly3 S3 W3 mem3 md3 k HB HJ) as HARO.
  pose proof (w1_tbl_bytes W3 mem3 HARO) as HTBL.
  pose proof (w1_row_bytes W3 mem3 (ACtlCut.c_in cx) HARO) as HROW.
  pose proof (w1_box_bytes ly3 S3 mem3 HRT) as HBOX.
  (* the five spill blocks are present stack bytes *)
  assert (PW : forall a, A + 16 <= a < A + 280 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a)
    by (intros a Ha; apply Hwin; lia).
  destruct (w1_rw_present _ mem3 (A + 16) 24 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply PW; lia))
    as (j1 & _ & C1).
  destruct (w1_rw_present _ mem3 (A + 128) 8 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply PW; lia))
    as (j2 & _ & C2).
  destruct (w1_rw_present _ mem3 (A + 248) 8 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply PW; lia))
    as (j3 & _ & C3).
  destruct (w1_rw_present _ mem3 (A + 256) 8 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply PW; lia))
    as (j4 & _ & C4).
  destruct (w1_rw_present _ mem3 (A + 272) 8 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply PW; lia))
    as (j5 & _ & C5).
  assert (U9 : bv_unsigned (lib.Reusable.YK11.getr regs3 9) = A) by (apply w1_rgv_unsigned; [exact E9 | lia]).
  assert (U18 : bv_unsigned (lib.Reusable.YK11.getr regs3 18) = ACtlCutP.SM.mrow (ACtlCut.c_in cx))
    by (apply w1_rgv_unsigned; [exact H18 | lia]).
  assert (U9r : bv_unsigned (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 9) = A) by exact U9.
  assert (U18r : bv_unsigned (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 18) = ACtlCutP.SM.mrow (ACtlCut.c_in cx))
    by exact U18.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (RV : forall lo len, A + 16 <= lo -> 0 <= len -> lo + len <= A + 280 -> Lib.ExecF.rng RNG lo len).
  { intros lo len H1 H2 H3. apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
    intros a Ha. exact (proj1 (Hwin a ltac:(lia))). }
  eapply (w1_lift W3 regs3 mem3 md3 0x8169c RNG).
  { unfold Lib.Regs6ss.mkR_of.
    eapply (R5F.r5_evt_F RNG) with (j1 := j1) (j2 := j2) (j3 := j3) (j4 := j4) (j5 := j5).
    - change (bv_unsigned (lib.Reusable.YK11.getr regs3 18) mod 8 = 0). rewrite U18. exact Hm8.
    - change (lib.Lib.Step.rw_cells B.Img0.rsegs mem3 (bv_unsigned (lib.Reusable.YK11.getr regs3 9) + 16)
                [lib.Lib.Cells.CB 24 j1]). rewrite U9. exact C1.
    - change (lib.Lib.Step.rw_cells B.Img0.rsegs mem3 (bv_unsigned (lib.Reusable.YK11.getr regs3 9) + 128)
                [lib.Lib.Cells.CB 8 j2]). rewrite U9. exact C2.
    - change (lib.Lib.Step.rw_cells B.Img0.rsegs mem3 (bv_unsigned (lib.Reusable.YK11.getr regs3 9) + 248)
                [lib.Lib.Cells.CB 8 j3]). rewrite U9. exact C3.
    - change (lib.Lib.Step.rw_cells B.Img0.rsegs mem3 (bv_unsigned (lib.Reusable.YK11.getr regs3 9) + 256)
                [lib.Lib.Cells.CB 8 j4]). rewrite U9. exact C4.
    - change (lib.Lib.Step.rw_cells B.Img0.rsegs mem3 (bv_unsigned (lib.Reusable.YK11.getr regs3 9) + 272)
                [lib.Lib.Cells.CB 8 j5]). rewrite U9. exact C5.
    - change (Lib.ExecF.rng RNG (bv_unsigned (lib.Reusable.YK11.getr regs3 9) + 16) 24). rewrite U9. apply RV; lia.
    - change (Lib.ExecF.rng RNG (bv_unsigned (lib.Reusable.YK11.getr regs3 9) + 128) 8). rewrite U9. apply RV; lia.
    - change (Lib.ExecF.rng RNG (bv_unsigned (lib.Reusable.YK11.getr regs3 9) + 248) 8). rewrite U9. apply RV; lia.
    - change (Lib.ExecF.rng RNG (bv_unsigned (lib.Reusable.YK11.getr regs3 9) + 256) 8). rewrite U9. apply RV; lia.
    - change (Lib.ExecF.rng RNG (bv_unsigned (lib.Reusable.YK11.getr regs3 9) + 272) 8). rewrite U9. apply RV; lia. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' (a0' & a1' & a2' & s2' & s5' & s6' & s8' & s11' & m' & -> & E5 & E6 & E11 & Hmu & Hwm &
                  B16 & B24 & B32 & B128 & B248 & B256 & B272) Hhid Hsbm.
  unfold B.Prog.Seg.R5.r5_W in Hmu.
  rewrite U9r in Hmu, B16, B24, B32, B128, B248, B256, B272.
  rewrite U18r in B16, B24, B272.
  assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { apply (w1_journal_run cx _ ly3 S3 W3 mem3 md3 k m' md' _ HJ Hmu Hwm Hhid Hsbm).
    intros a Ha Hni. cbn [lib.Lib.Frame.outside] in Hni.
    split; [left; unfold Reusable.YCfn.LLVMF_STK; lia|].
    intros Hi. apply w1_img in Hi. lia. }
  pose proof (w1_rt cx _ ly3 S3 W3 m' md' k HB HJ') as HRT'.
  assert (KSP : forall i, 0 <= i < 392 ->
                  exists b, lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa (ACtlCutP.Sfr fr + i)) = Some b)
    by exact (w1_fsh_rd cx ly3 S3 W3 m' md' k fr HJ' Hfr Efr).
  assert (MK : forall lo hi, (forall a, lo <= a < hi ->
                 0 <= a < 2 ^ 64 /\ (a < A + 16 \/ (A + 40 <= a < A + 128) \/ (A + 136 <= a < A + 248) \/
                                    (A + 264 <= a < A + 272) \/ A + 280 <= a)) ->
                 KEEPR mem3 m' lo hi).
  { intros lo hi H. apply (w1_keep_munch _ mem3 m' lo hi Hmu). intros a Ha. destruct (H a Ha) as [Hr Hc].
    split; [exact Hr|]. cbn [lib.Lib.Frame.outside]. lia. }
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ =>
    set (RT := R) end.
  assert (G9 : lib.Reusable.YK11.getr RT 9 = lib.Reusable.YK11.getr regs3 9) by reflexivity.
  assert (KA : forall off, 0 <= off -> off + 8 <= 448 ->
                 (off + 8 <= 16 \/ (40 <= off /\ off + 8 <= 128) \/ (136 <= off /\ off + 8 <= 248) \/
                  (264 <= off /\ off + 8 <= 272) \/ 280 <= off) ->
                 KEEPR mem3 m' (A + off) (A + off + 8))
    by (intros off H0 H1 H2; apply MK; intros a Ha; split; lia).
  assert (SP : forall off v, 0 <= off -> off + 8 <= 448 ->
                 (off + 8 <= 16 \/ (40 <= off /\ off + 8 <= 128) \/ (136 <= off /\ off + 8 <= 248) \/
                  (264 <= off /\ off + 8 <= 272) \/ 280 <= off) ->
                 ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill RT m' off v)
    by (intros off v H0 H1 H2 Hs; exact (w1_spill_mv regs3 RT mem3 m' A off v E9 ltac:(lia) ltac:(lia) H0 H1 G9
                                          (KA off H0 H1 H2) Hs)).
  assert (KF : KEEPR mem3 m' fr (fr + 4096)) by (apply MK; intros a Ha; split; lia).
  assert (KS : KEEPR mem3 m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW)).
  { apply MK. intros a Ha. unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, ACtlCutP.FRAME_SHADOW,
      ACtlCutP.FRAME_BYTES in Ha. change (3136 / 8) with 392 in Ha.
    split; lia. }
  assert (KI : KEEPR mem3 m' 0x10000 0x5fe000) by (apply MK; intros a Ha; split; lia).
  assert (MK1 : forall x, 0 <= x < 2 ^ 64 ->
                  (x < A + 16 \/ (A + 40 <= x < A + 128) \/ (A + 136 <= x < A + 248) \/
                   (A + 264 <= x < A + 272) \/ A + 280 <= x) ->
                  lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x H1 H2; apply (MK x (x + 1)); [intros a Ha; split; lia | lia]).
  assert (AK : forall X n, 0 <= X -> 0 <= n -> X + n <= ACtlCutP.FRAME_BYTES ->
                 B.AsanRT.addressable mem3 (fr + X) n -> B.AsanRT.addressable m' (fr + X) n)
    by (intros X n H1 H2 H3; exact (w1_faddr_keep mem3 m' fr X n KS Hfr8 H1 H2 H3)).
  pose proof (B.Prog.Seg.R7.r7_mrow_range (ACtlCut.c_in cx)) as Hmr7.
  change B.Prog.SlotModel.mrow with ACtlCutP.SM.mrow in Hmr7.
  assert (HTBL' : lib.Lib.Mem.bytes_at B.Img0.rsegs m' (ACtlCutP.BAC.BA_FR + 72) ACtlCutP.BAP.ba_tbl).
  { apply (w1_bytes_keep mem3 m'); [| exact HTBL]. rewrite B.Prog.Seg.R7.r7_tbl_len.
    apply (w1_keep_sub _ _ _ _ _ _ KI); unfold ACtlCutP.BAC.BA_FR; lia. }
  assert (HROW' : lib.Lib.Mem.bytes_at B.Img0.rsegs m' (ACtlCutP.SM.mrow (ACtlCut.c_in cx))
                    (ACtlCutP.SM.rt_mb (ACtlCut.c_in cx))).
  { apply (w1_bytes_keep mem3 m'); [| exact HROW]. rewrite (B.Prog.Seg.R7.r7_mb_len (ACtlCut.c_in cx)).
    apply (w1_keep_sub _ _ _ _ _ _ KI); change (Z.of_nat 296) with 296; lia. }
  assert (HBOX' : lib.Lib.Mem.bytes_at B.Img0.rsegs m' ACtlCutP.SM.BOXA ACtlCutP.SM.box6).
  { apply (w1_bytes_keep mem3 m'); [| exact HBOX].
    change (Z.of_nat (length ACtlCutP.SM.box6)) with 6.
    apply (w1_keep_sub _ _ _ _ _ _ KI); unfold ACtlCutP.SM.BOXA; lia. }
  assert (HNAME' : B.ACtlCutP.RS6.has (ACtlCutP.SM.rt_mb (ACtlCut.c_in cx)) <> 0 /\
                   B.ACtlCutP.RS6.rname (ACtlCutP.SM.rt_mb (ACtlCut.c_in cx)) <> 0 ->
                   B.ACtlCutP.RBx.name_ok (ACtlCutP.SM.rt_nb (ACtlCut.c_in cx)) /\
                   lib.Lib.Mem.bytes_at B.Img0.rsegs m' (B.ACtlCutP.RS6.rname (ACtlCutP.SM.rt_mb (ACtlCut.c_in cx)))
                     (ACtlCutP.SM.rt_nb (ACtlCut.c_in cx)) /\
                   B.AsanRT.addressable m' (B.ACtlCutP.RS6.rname (ACtlCutP.SM.rt_mb (ACtlCut.c_in cx)))
                     (Z.of_nat (length (ACtlCutP.SM.rt_nb (ACtlCut.c_in cx)))) /\
                   0 < B.ACtlCutP.RS6.rname (ACtlCutP.SM.rt_mb (ACtlCut.c_in cx))).
  { intros Hh. destruct (HNAME Hh) as (Hok & Hb & Ha & Hp). split; [exact Hok|].
    pose proof (B.Prog.Seg.R7.r7_rname _ (proj1 Hh) (proj2 Hh)) as Hr.
    pose proof (w1_cstr_len 16 (B.ACtlCutP.RS6.rname (ACtlCutP.SM.rt_mb (ACtlCut.c_in cx)))) as Hl.
    change (ACtlCutP.SM.img_cstr (B.ACtlCutP.RS6.rname (ACtlCutP.SM.rt_mb (ACtlCut.c_in cx))) 16) with
      (ACtlCutP.SM.rt_nb (ACtlCut.c_in cx)) in Hl.
    split.
    - apply (w1_bytes_keep mem3 m'); [| exact Hb]. apply (w1_keep_sub _ _ _ _ _ _ KI); lia.
    - split; [| exact Hp]. apply (w1_addr_keep mem3 m'); [| exact Ha]. intros i Hi.
      apply MK1; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia. }
  apply (H6ec cx [Z.of_nat 0] fr k ly3 S3 W3 RT m' md' HB HJ' Hfr HFA).
  - unfold ACtlCut.ix_cut, ACtlCutP.C_B816ec_at, ACtlCutP.ixn. cbn [ACtlCut.cut_kmax nth]. exact Hk.
  - unfold ACtlCut.ix_cut, ACtlCutP.C_B816ec_at, ACtlCutP.ixn. cbn [ACtlCut.cut_body nth].
    split; [reflexivity|]. rewrite ?Nat2Z.id.
    assert (R9 : ACtlCut.rgv RT 9 A) by (unfold ACtlCut.rgv; rewrite G9; exact E9).
    split; [exact Hperm|].
    split.
    { apply (w1_frac_mv cx fr fr A regs3 RT mem3 m' E9 ltac:(lia)); try reflexivity; try exact HFRAC;
        try exact KSP; apply MK; intros a Ha; split; lia. }
    split; [exact Hn|].
    split.
    { (* RS cx fr 0 *)
      unfold ACtlCutP.RS, ACtlCutP.RB. split; [lia|].
      split; [unfold ACtlCutP.CUR, ACtlCut.rgv in *; exact HCUR|].
      split; [unfold ACtlCutP.OURb in *; apply (w1_bytes_keep mem3 m'); [| exact HOUR];
              rewrite ACtlCutP.SM.OUR_length; intros a Ha; apply KF; lia|].
      split; [unfold ACtlCut.rgv; exact E6|].
      split; [unfold ACtlCutP.IDBr in *; apply (w1_bytes_keep mem3 m'); [| exact HIDB];
              rewrite B.Prog.Seg.RtmB.rb_RID_len; intros a Ha; apply KF; lia|].
      unfold ACtlCutP.FGBr in *; apply (w1_bytes_keep mem3 m'); [| exact HFGB].
      rewrite (B.Prog.Seg.RtmB.rb_RFG_len _ 0 ltac:(lia)); intros a Ha; apply KF; lia. }
    split.
    { (* RBE *)
      unfold ACtlCutP.RBE, ACtlCutP.PRA, ACtlCutP.OUTA in *.
      destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
      split; [apply (w1_spill_of RT m' A); [exact R9 | exact B128]|].
      split; [apply SP; [lia | lia | lia | exact S312]|].
      split; [apply (w1_spill_of RT m' A); [exact R9 | exact B272]|].
      split; [apply SP; [lia | lia | lia | exact S264]|].
      split; [apply (w1_spill_of RT m' A); [exact R9 | exact B256]|].
      split; [apply (w1_spill_of RT m' A); [exact R9 | exact B248]|].
      split; [apply SP; [lia | lia | lia | exact S56]|].
      split; [apply SP; [lia | lia | lia | exact S184]|].
      split; [apply SP; [lia | lia | lia | exact S144]|].
      split; [apply SP; [lia | lia | lia | exact S8]|].
      split; [apply (w1_spill_of RT m' A); [exact R9 | exact B32]|].
      split; [apply (w1_spill_of RT m' A); [exact R9 | exact B24]|].
      split; [apply (w1_spill_of RT m' A); [exact R9 | exact B16]|].
      split; [apply SP; [lia | lia | lia | exact S96]|].
      split; [apply SP; [lia | lia | lia | exact S120]|].
      split; [apply SP; [lia | lia | lia | exact S240]|].
      split; [apply SP; [lia | lia | lia | exact S232]|].
      split; [apply SP; [lia | lia | lia | exact S224]|].
      split; [apply SP; [lia | lia | lia | exact S176]|].
      split; [apply SP; [lia | lia | lia | exact S208]|].
      split; [apply SP; [lia | lia | lia | exact S64]|].
      split; [apply AK; [lia | lia | unfold ACtlCutP.FRAME_BYTES; lia | exact HOUTA]|].
      split; [apply AK; [lia | lia | unfold ACtlCutP.FRAME_BYTES; lia | exact HA2176]|].
      split; [exact HNAME'|].
      split; [apply AK; [lia | lia | unfold ACtlCutP.FRAME_BYTES; lia | exact HA2624]|].
      split; [exact HTBL'|]. split; [exact HBOX'|]. split; [exact HROW'|].
      split.
      { split; [apply SP; [lia | lia | lia | exact P136]|]. split; [apply SP; [lia | lia | lia | exact P280]|].
        split; [apply SP; [lia | lia | lia | exact P168]|]. split; [apply SP; [lia | lia | lia | exact P192]|].
        split; [apply SP; [lia | lia | lia | exact P200]|]. split; [apply SP; [lia | lia | lia | exact P216]|].
        split; [apply SP; [lia | lia | lia | exact P104]|]. split; [apply SP; [lia | lia | lia | exact P288]|].
        split; [apply SP; [lia | lia | lia | exact P296]|]. split; [apply SP; [lia | lia | lia | exact P304]|].
        apply SP; [lia | lia | lia | exact P168b]. }
      split; [apply SP; [lia | lia | lia | exact S152]|].
      split; [apply SP; [lia | lia | lia | exact S112]|].
      split; [apply AK; [lia | lia | unfold ACtlCutP.FRAME_BYTES; lia | exact HA2256]|].
      apply SP; [lia | lia | lia | exact S160]. }
    split; [unfold ACtlCut.rgv; exact E5|].
    split.
    { (* R6X cx 0 *)
      unfold ACtlCutP.R6X, ACtlCutP.OUTA in *.
      split; [apply AK; [lia | lia | unfold ACtlCutP.FRAME_BYTES; lia | exact HOUTA]|].
      split; [apply AK; [lia | lia | unfold ACtlCutP.FRAME_BYTES; lia | exact HA2624]|].
      split; [exact HTBL'|]. split; [exact HBOX'|]. split; [exact HROW'|].
      intros ([E|E] & _); cbn in E; discriminate E. }
    split; [exact HNAME'|].
    unfold ACtlCut.rgv; exact E11.
  - exact (w1_rt cx _ ly3 S3 W3 m' md' k HB HJ').
Qed.

End W1.

(* ===========================================================================================================
   CLOSING NOTES (header).  A Theorem Labs lane, a working branch, route (C) shell a working branch.
   Stages proved (Qed): seg_A4, w1_our_loop, seg_A5, seg_R1, seg_R2, seg_R3, seg_R4, seg_R5; each statement is
   token-equal to lib/B/ACtl.v's hypothesis of the same name under the shell binding (ctl_from).
   At a cut a stage HAS ctl_rt_C B ly3 S3 mem3 and reads: ro_agree (seg_R5's box; w1_name), asan_cells (seg_R2 /
   seg_R3 / the loop exit), shadow_rw_on (cut_shadow ..) (seg_R3, the callee's id-buffer region in the owned frame's
   (F) shadow).  At every exit it SUPPLIES ctl_rt_C by B.ProgWorldCtlRtC.ctl_rt_C_of_AR on the journal's AR (w1_rt).
   The owned frame's shadow bytes FRAC needs at a new memory are present by AR's frame law (w1_fsh_rd), not shadow_rw.
   FRAC / FRAHC are re-established (trailer word q64 (fr + 4088) included) by: seg_A4 (FRAHC), w1_after_turn (FRAHC),
   w1_exit (FRAHC then FRAC at P3 and at 0x815fc), seg_R2, seg_R3, seg_R4, seg_R5 (FRAC).
   Footprint runs used: A4F.a4_evt_F (seg_A4), A5F.b_hd_ld_evt_F / b_z_evt_F / b_tail_evt_F / b_mode_evt_F /
   b_cat_evt_pre_F_on / b_cat_evt_post_F_on (w1_turn, w1_exit: seg_A5, seg_R1, w1_our_loop), R1F.seg_R1_F (seg_R1),
   R2F.r2_evt_pre_F (seg_R2), R3F.r3_pre_F_on / r3_post_F_on (seg_R3), R4F.r4_pre_F (seg_R4), R5F.r5_evt_F (seg_R5).
   The four _on runs are a Theorem Labs lane's (a working branch e9effcf7313, R3F.v / A5F.v taken by path).  A5F / R1F /
   R2F are not on the v1.9 record line yet (auditor a Theorem Labs lane, batch 14): seg_A5, seg_R1, w1_our_loop, seg_R2
   depend on them.

   SECTION HYPOTHESES (name: text; open obligation; owner).
   - LAWS : Reusable.YG0d.AR_laws segs B.  The core's AR laws; walk-shared, the top discharges.  a Theorem Labs lane.
   - TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.  Walk-shared (06:40Z text); the top discharges.  a Theorem Labs lane.
   - RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a; Context RO_OFL :
     Reusable.APostBase.ro_below_ofl segs RLO RHI.  Walk-shared (06:46Z); the top discharges.  a Theorem Labs lane.
   - RELRO_CAT : RLO <= ACtlCutP.SM.CAT /\ ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length ACtlCutP.BAP.ba_tbl) <= RHI.
     The catalogue and CTRL_FRAMES rows lie in the RELRO range; by computation at the top's RLO / RHI.  a Theorem Labs lane.
   - ctl_relro_not_owned (T10, RTPOST-SHARED-B.txt (a working note, not in this delivery), token for token).  a Theorem Labs lane.
   - ctl_names_addressable (V6, RTPOST-SHARED-B.txt (a working note, not in this delivery), token for token).  a Theorem Labs lane.
   - ctl_kind_name_addressable (RTPOST-SHARED-B.txt (a working note, not in this delivery), token for token).  a Theorem Labs lane.
   - FP_nil : FP = [].  ACtl.v instantiates the journal footprint with [] (ACtl.v:182); eq_refl.  a Theorem Labs lane.
   - AMEMSET : Reusable.YG0d.aintrin_realizes segs B Reusable.YG0d.OSet Reusable.YB1w.tfib_A_asan_memset.
     The core's memset rule at B's name (lib/B/ACtlW3a.v's text); the top discharges.  a Theorem Labs lane.
   - ASF00 : Reusable.SetShadowDefP.aset_shadow_realizesP segs B 0x55024 0 (RTPOST, 08:02Z).  The top discharges by
     B.Rt.SetShadow.ctrl_set_shadow_00P.  a Theorem Labs lane.
   No callee hypothesis: reac_identity_init by B.Prog.reac_identity_initF.reac_identity_init_F_holds_on
   (B.Prog.asan_memsetF_on.asan_memset_holds_F_on B.Prog.memset.memset_holds); reac_box_catalogue by
   B.Prog.reac_box_catalogueF.reac_box_catalogue_F_holds_on; FRAME_ABOVE by B.ProgWorld_Fs.ctl_frame_above_img
   (all proved, a working branch). *)
