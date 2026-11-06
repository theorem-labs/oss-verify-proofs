(* lib/A/ACtlG/Y1.v -- GLUE for stage seg_Y1 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:880,
   ACtl.v's "W5 tail" block).  Written by a Theorem Labs lane; single writer.  The pattern is
   glue-pattern.md (a working note, not in this delivery), the worked example lib/A/ACtlG/A5.v.
   rule 24: no function proved (stage glue of a walk: an already-proved segment run through an already-proved bridge
   to a fixed stage statement; the released-proof position of LLVMFuzzerTestOneInput was settled for this unit).

   WHAT IT PROVES
     glue_seg_Y1 : forall POST, CF POST C_A82bb0 -> CF POST C_A82b9c
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_Y1.  C_A82b9c (pc 0x82b9c, own6) is the ENTRY, C_A82bb0 (pc 0x82bb0, own0) the EXIT.  Segment Y1 is the
   side-arm release `jal 0x3dbf4 <frame_release_6>` (__asan_stack_free_6) at 0x82b9c and the `j 0x82bb0` at 0x82ba0;
   its footprint run is Seg/YTailF.v y1_evt_F.  The stage also moves the WORLD: the journal goes from own [(6, pos)]
   to own [] and the state from S3 to stack_free_state 6 pos S3 (the class-6 frame release).

   THE PROOF (glue-pattern.md section 3; the run WRITES memory)
   G1  unfold the entry cut C_A82b9c (ACtlCutP.v C_A82b9c): Permutation, FRAHC (ACtlCutP.v FRAHC, with Batch3's
       trailer word LAST, see "CUT TEXT" below), sel = fr, a0 = fr, a1 = FRAME_BYTES = 3136.
   G2  the run's premises, all from VISIBLE state of the cut:
       - the fake-stack layout: FS := ly_F ly3, j := c_fpos cx; fr = fs_frame FS 6 j from the shell's frame law and
         layout_le's ly_F equation; the class-6 numerals of asan_stack_malloc_c.v against YG0f's frame_off /
         flag_off are closed arithmetic (proved below, the cid = 6 case of ProgWorld.ctl_fs_geom);
       - fs_place: 0 < FS and ASAN_GT <= FS (F_ABOVE), FS page aligned and in application memory (YG0s.frame_facts),
         its stk from the side stack's presence (F_PRESENT);
       - the flag byte reads 1: AR's am_flags (fs_flags_ok, frames S3 = [(6, pos)]) read through the view;
       - the frame's back-pointer word: the cut's new FRAHC conjunct;
       - asan_cells / ro_agree: the cut's ctl_rt_C; the run's shadow region (a Theorem Labs lane's asan_stack_free_shadow_R 6 3136
         FS j, the frame's 512 shadow bytes) from ctl_rt_C's cut_shadow, disjunct (F) (route C, HRsh below);
       - the stack window [sp - 32, sp): the journal's presence clause over [c_sp cx - LLVMF_STK, c_sp cx), with
         FRAHC's c_sp cx - 4096 < sp <= A, A + 416 <= c_sp cx;
       - FS + FS_SIZE <= sp - 32: in_app (ly_F, kFakeStackSize) <= ASAN_CEIL <= ly_stk_lo <= c_sp cx - LLVMF_STK;
       - the footprint RNG := ProgBridge.RNG_W (w_H W3): image range ProgBridge.img_vis_W; stack window and side
         stack from presence; the frame's 512 shadow bytes from AR_frames_law (al_frames); rng_bytes_RNG_W;
       - the callee's footprint contract stack_free_6_F_on RNG: YTailF.stack_free_6_F_on_gen (PROVED, by name).
   G3  ProgBridge.cfg_at_MS, then the walk moved from regs3 to the run's canonical map mkR_of regs3
       (YA0nR.SRr_xregs_eqv), exactly as A5.v.
   G4  lift: ProgBridge.fevt_of_evtF, tfibsegs_rsegs, then YA0nR.SRr_fsteps (not SRr_fevt_hid: the release law
       below takes the run's fsteps itself and derives the hidden bytes from it).
   G5  the exit cut C_A82bb0 at the run's end map R and memory m', state stack_free_state 6 pos S3, model md':
         journal  the release law (REL6 below = ProgWorldAstack.ctl_release_of_free_law at cid 6): the run's
                  munch list is the flag byte, the frame's 512 shadow bytes (awr_byte's in_frames case) and the
                  callee window [sp - 32, sp) (awr_byte's stack case); the flag byte reads 0 after the run;
         frames   del_pos [(6, pos)] 6 pos = [] = own0;
         frame law vacuous (own0);  k bound: EV_LLVMF on both cuts;
         body     Permutation by YG01.blocks_stack_free_state; registers 8 / 3 kept by the run (s0 / gp), register 4
                  (tp) kept and equal to the entry's through afn_pre; the saved registers at c_sp cx - 104 kept by
                  the run's munch (all three ranges lie below c_sp cx - 104);
         ctl_rt_C asan_cells by AsanRTFacts.asan_cells_kept (no write in [RT_LO, RT_HI)); ro_agree from the run's
                  post; both shadow regions carried by the run's forall-P post (y1_evt_F_on), the cut region after
                  shadow_rw_on_mono: stack_free_state 6 pos S3's cut_shadow lies in S3's (the frame leaves frames;
                  blocks and layout unchanged).

   SECTION HYPOTHESES (exact text below; source, owner and why for each)
   - LAWS : Reusable.YG0d.AR_laws segs B.  ACtl.v's own Section hypothesis (ACtl.v:237); the frame / flag laws
     (al_frames, al_flag) and the release law take it.  Not new.
   CITED BY NAME (no longer a hypothesis): YTailF.stack_free_6_F_on_gen : forall RNG, stack_free_6_F_on RNG, the
     route (C) footprint contract of __asan_stack_free_6 at a GENERAL footprint (Seg/YTailF.v,
     a working branch 8165843863a; proved from lib/A/Prog/asan_stack_freeF.v's asan_stack_free_6_holds_F_on).
     Before route (C) the same place cited stack_free_6_F_gen (universal shadow_rw premise), which had replaced a
     Section hypothesis HSF6F.
   CITED BY NAME (no longer stand-ins; all three on the glue base since Batch3's twelve ProgWorld files):
     F_ABOVE := A.ProgWorld_Fs.pw_F_above B and F_PRESENT := A.ProgWorld_Fs.pw_F_present B (lib/A/ProgWorld_Fs.v,
     Section Fs; owner a Theorem Labs lane); REL6 := A.ProgWorldAstack.ctl_release_of_free_law B 6 (lib/A/ProgWorldAstack.v
     :333, owner a Theorem Labs lane; its statement A.ProgWorld.ctl_release_of_free_law_stmt B 6, lib/A/ProgWorld.v:493-508,
     owner a Theorem Labs lane).  Each was a transcribed Section hypothesis; each is now a Local Notation for the proved lemma.
   CITED BY NAME, NOT HYPOTHESES: YA0nR.SRr_xregs_eqv / SRr_fsteps, ProgBridge (fevt_of_evtF, tfibsegs_rsegs,
   cfg_at_MS, RNG_W, fp_avoids_RNG_W, rng_RNG_W, rng_of_visible, img_vis_W, rng_bytes_RNG_W), YG0t.astack_free_law_ok
   (the release law's astack_free_law premise), YG0s.frame_facts, YCbq.frames_bounds, AsanRTFacts.asan_cells_kept,
   Frame.bytes_at_transport, YTailF.y1_evt_F_on, ShadowRwOn.shadow_rw_on_mono, the kit's Kit.kit_wx.
   NOT USED: rt_of_core / ctl_RT, ctlrt_of_AR / ctl_rt_C_of_AR (ctl_rt_C is re-established from the run's post and
   the munch), ajournal_exec (the release law steps the journal).

   CUT TEXT: this file reads FRAHC's trailer word `q64 m (fr + 4088) (Reusable.YG0f.flag_addr (c_ly cx) 6
   (c_fpos cx))`, on the glue base since a Theorem Labs lane's Batch3 (d36efc6152d, ACtlCutP.v FRAHC's LAST conjunct; a Theorem Labs lane's
   finding: y1_evt_F needs the word at fr + fs_B 6 - 8, which ctrl's FRA carried as FSREC, SlotInv.v:309-312, and
   which AR / ajournal / ctl_rt never pin).  The ONLY place this file restates FRAHC's text is G1's positional
   destruct of FRAHC (the `destruct HFRAHC as (Asp & sp & ...)` line), which names the trailer as the LAST conjunct
   (Qbp), as Batch3 places it.  The exit cut C_A82bb0 has no FRAC / FRAHC, so no conjunct is re-established, and
   the run writes only [flag, flag + 1), the frame's 512 shadow bytes and [sp - 32, sp), never [fr + 4088, fr + 4096).

   NAMES (porter a Theorem Labs lane 04:24Z / 04:33Z): the closure reaches both the core copy (lib/Reusable/X) and ctrl's copy
   (lib/A/Reusable/X) of YI04 YI16 YK11 YK1b YM05 YO09 (Locate, measured); every use goes through a
   `Module M := <full path>` alias below (RK11 / RM05 / RO09 = core, AK11 = ctrl's YK11 for the _F run's FPState),
   and every Require of them names its directory (lib.Reusable / lib.A.Reusable).  The rest of the core / Lib / LPS
   vocabulary goes through full-path aliases too (RSem.reg_get is LPS Riscv/Sem.v's).  seg_rom / cfg_at are
   RK11 / RG0d qualified; no getr / mkst is named.  No Import / Export of a project module.

   CLOSURE (glue closure rule, a Theorem Labs lane 23:32Z / porter 23:38Z): Seg/YTailF.v and its closure are Required QUALIFIED
   (rule 1); no statement here names a frame-route identifier (the Section hypotheses name the core's world, ctrl's
   fake-stack layout file asan_stack_malloc_c.v and the YTailF callee contract).  Measured closure (every
   `From .. Require` under OSSVerify.Proofs.libreac.fuzz_ctrl, from this file): 425 files; no lib/AZ/AsanW, no
   W6, no SegCF / *_cfw / Cf_* file (the two R/Cfg.v files, core and ctrl's, are configuration files, not cut-free);
   the lib/AZ files are LibA/AcctCore (via Lib/ExecF) and Spec/{AsanCtrl,AsanCtrlProps,STree}.  The frame-route
   blobs (all = the v1.9 blobs of record where glue-pattern.md section 12 names one) are in the commit message.

   BUILD STATE: see the commit message and the lane report (type-check; the label, the closure scan and
   `Print Assumptions glue_seg_Y1` come with each build).  No Axiom, no Parameter, no Admitted, no admit, no
   Abort. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YK04R YA0n YA0nR YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0n YG0d YG0s YG0t YCbq YC5d YM05 YO09 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k Img0 AsanRT AsanRTFacts ACfn ACtlCut ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgBridge ProgWorld_Fs ProgWorldAstack.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_malloc_c asan_stack_free_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require YTailF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame ExecF MState Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* Full-path aliases (porter a Theorem Labs lane 04:24Z: `M.n` for `Module M := <full path>` is a safe spelling). *)
Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module AK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Module RSem := LinuxProcessSemantics.Riscv.Sem.
Module RK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module RK04R := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04R.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module RA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module RG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module RG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module RG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module RG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module RG0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0s.
Module RG0t := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0t.
Module RCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module RC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Module RP09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Module AImg0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module ARF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module YTF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.YTailF.
Module SFO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_free_c_on.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LExecF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LMState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRegs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module KIT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.Kit.

(* The core's segment list, as ACtlCut.v:80 and ACtl.v:203 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* A run of present bytes is a stk range (the statement of A.ProgWorld_Fs.pw_stk_of_present, stated over a bare
   hidden set instead of a world). *)
Lemma y1_stk_of_present : forall (H : word -> bool) (m : word -> option byte) (lo hi : Z),
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> RG0n.apresent H m a) ->
  LFrame.stk AImg0.rsegs m lo hi.
Proof.
  intros H m lo hi Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|].
  intros a Ha. destruct (Hp a Ha) as [_ (b & Hb)]. unfold LMem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold LMem.mrd. rewrite Hb. reflexivity.
Qed.

(* The class-6 numerals of ctrl's fake-stack layout (asan_stack_malloc_c.v:26-32) against the core's (YG0f / YG00):
   the cid = 6 case of A.ProgWorld.ctl_fs_geom, closed arithmetic. *)
Lemma y1_fs_frame6 : forall FS j, SMC.fs_frame FS 6 j = FS + RG0f.fs_frame_off 6 j.
Proof.
  intros FS j. unfold SMC.fs_frame, RG0f.fs_frame_off, RG0f.kFakeFramesOff.
  change (SMC.fs_B 6) with 4096. change (RG00.fs_frame_bytes 6) with 4096.
  change (Z.shiftl 1 RG00.kStackSizeLog) with 1048576. change (Z.of_nat 6) with 6. change (2 ^ 20) with 1048576.
  lia.
Qed.

Lemma y1_fs_flag6 : forall FS j, SMC.fs_flag FS 6 j = FS + RG0f.fs_flag_off 6 j.
Proof.
  intros FS j. unfold SMC.fs_flag, RG0f.fs_flag_off, RG0f.kFakeFlagsOff.
  change (RG0f.fs_flags_off 6) with 32256. change (2 ^ 15) with 32768. change (2 ^ (15 - Z.of_nat 6)) with 512.
  lia.
Qed.

Lemma y1_shadow_addr : forall a, ART.shadow_addr a = RG0f.shadow_addr a.
Proof. intros a. unfold ART.shadow_addr, ART.ASAN_K, RG0f.shadow_addr, RG0f.SHADOW_OFF. apply Z.add_comm. Qed.

Lemma y1_saved_len : forall cx, length (ACtlCutP.saved_bytes cx) = 104%nat.
Proof. intros cx. unfold ACtlCutP.saved_bytes. rewrite !length_app, !LMem.length_le8. reflexivity. Qed.

Section GlueY1.

(* ACtl.v's Section Ctl shape (ACtl.v:205-237, blob c4edf0be7fe: the core classes by full path), restricted to what
   this stage uses; glue_seg_Y1's arguments are therefore B MT XM_LIB RLO RHI LAWS and this file's hypotheses. *)
Context {fx : RK11.FPState} {rc : RM05.RunCeil} {LS : RO09.lib_shape}.
Variable B : RG0f.asyms.
Variable MT : RC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:377-378, :478-479), verbatim. *)
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82b9c := (ACtlCutP.C_A82b9c B).
Local Notation C_A82bb0 := (ACtlCutP.C_A82bb0 B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources, owners and discharge routes in the header). *)

(* ACtl.v:237. *)
Hypothesis LAWS : RG0d.AR_laws segs B.

(* a Theorem Labs lane's PROVED side-stack facts (lib/A/ProgWorld_Fs.v, Section Fs), cited by name. *)
Local Notation F_ABOVE := (A.ProgWorld_Fs.pw_F_above B).
Local Notation F_PRESENT := (A.ProgWorld_Fs.pw_F_present B).

(* a Theorem Labs lane's PROVED release law at cid 6 (lib/A/ProgWorldAstack.v:333), statement
   A.ProgWorld.ctl_release_of_free_law_stmt B 6 (lib/A/ProgWorld.v:493-508), cited by name. *)
Local Notation REL6 := (A.ProgWorldAstack.ctl_release_of_free_law B 6).

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_Y1 : forall POST, CF POST C_A82bb0 -> CF POST C_A82b9c.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_A82b9c (ACtlCutP.v:3005-3012) and FRAHC (ACtlCutP.v:999-1013 + the back-pointer). *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82b9c] in Hbody.
  destruct Hbody as (HP & HFRAHC & _ & Ha0 & R11).
  destruct HFRAHC as (Asp & sp & R2 & Hsp16 & EspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAS & HspA &
    HfrA & HA416 & Hsp4096 & HSapp & Q304 & Qhdr & Q16 & Hsh & Hsaved & Qbp).
  destruct Hrt as (HAC & Hcut & Himg & HRO).
  assert (HF6 : RG01.frames S3 = [(6, ACtlCut.c_fpos cx)]) by exact HF.
  assert (Hin : In (6, ACtlCut.c_fpos cx) (RG01.frames S3)) by (rewrite HF6; left; reflexivity).
  assert (Efr : fr = RG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)) by (apply HL; left; reflexivity).
  (* the entry's tp, from the core's lib pre (afn_pre, YCbq.v:339) *)
  pose proof HB as ((Hafn & _) & _).
  pose proof Hafn as (_ & _ & _ & _ & Htp & _).
  (* the journal: AR, layout_le, the stack window's presence, astk_ok (YCbq.v:350-372) *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  destruct Hstatic as (_ & _ & Hceil & Hlo & _).
  pose proof HAR as (HM & _).
  destruct (RG0s.frame_facts B ly3 S3 _ 6 (ACtlCut.c_fpos cx) HM Hin)
    as (_ & Hpos & HFapp & _ & HFal & _ & _ & _ & _ & _ & Hflb).
  destruct (RCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (Hf4096 & Hfceil & _).
  destruct (RG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (_ & _ & _ & Hshp).
  destruct (RG0d.al_flag _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (Hflp & _ & Hflapp & _).
  pose proof (F_ABOVE ly3 S3 W3 mem3 md3 HAR) as Habove.
  pose proof RG0f.ASAN_CEIL_range as [CR _].
  (* G2: numerals and bounds, all from the visible state above *)
  assert (Efr3 : fr = RG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite Efr. unfold RG0f.frame_addr. rewrite EF. reflexivity. }
  assert (EfrFS : fr = SMC.fs_frame (RG0f.ly_F ly3) 6 (ACtlCut.c_fpos cx)).
  { rewrite y1_fs_frame6. exact Efr3. }
  (* route (C): the run's shadow region (a Theorem Labs lane's asan_stack_free_shadow_R 6 3136 FS j = [S(fr), S(fr) + 512)) is the
     owned class-6 frame's shadow, disjunct (F) *)
  assert (HRsh : forall a, SFO.asan_stack_free_shadow_R 6 3136 (RG0f.ly_F ly3) (ACtlCut.c_fpos cx) a ->
                           A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros a Ha. unfold SFO.asan_stack_free_shadow_R in Ha. rewrite <- EfrFS in Ha.
    change (SMC.fs_shadow_n 6 3136) with 512 in Ha.
    left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin|].
    rewrite <- Efr3, <- y1_shadow_addr. change (RG00.fs_frame_bytes 6 / 8) with 512. exact Ha. }
  assert (Efl : SMC.fs_flag (RG0f.ly_F ly3) 6 (ACtlCut.c_fpos cx) = RG0f.flag_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite y1_fs_flag6. reflexivity. }
  assert (Efl' : RG0f.flag_addr ly3 6 (ACtlCut.c_fpos cx) = RG0f.flag_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)).
  { unfold RG0f.flag_addr. rewrite EF. reflexivity. }
  assert (Efa : RG0f.flag_addr ly3 6 (ACtlCut.c_fpos cx) =
                RG0f.ly_F ly3 + RG0f.fs_flag_off 6 (ACtlCut.c_fpos cx)) by reflexivity.
  unfold ART.APPMEM_END in HSapp. unfold ACtlCutP.FRAME_BYTES in HfrA.
  unfold A.ACfn.LLVMF_STK in Hpres, Hlo.
  unfold RG0f.ASAN_CEIL in CR.
  unfold RG0f.in_app, RG0f.kLowShadowBeg, RG0f.kHighMemBeg, RG0f.ASAN_CEIL, RG0f.kFakeStackSize in HFapp.
  unfold RG0f.kFakeFlagsOff, RG0f.kFakeFramesOff in Hflb.
  unfold SMC.ASAN_GT in Habove.
  rewrite <- Efr3 in Hf4096, Hfceil. change (RG00.fs_frame_bytes 6) with 4096 in Hfceil.
  assert (BFS : 0x5fe000 <= RG0f.ly_F ly3 /\ RG0f.ly_F ly3 + 11571200 <= RM05.alloc_ceiling) by lia.
  assert (Bfl : RG0f.ly_F ly3 + 4096 <= RG0f.flag_addr ly3 6 (ACtlCut.c_fpos cx) < RG0f.ly_F ly3 + 36864) by lia.
  assert (Bsh : 0x7fff8000 <= ART.shadow_addr fr /\ ART.shadow_addr fr + 512 <= 0x10007fff8000).
  { unfold ART.shadow_addr, ART.ASAN_K. Z.div_mod_to_equations. lia. }
  (* the run's register premises *)
  assert (Hj : 0 <= ACtlCut.c_fpos cx < SMC.fs_M 6).
  { replace (SMC.fs_M 6) with (RG00.fs_frames 6) by reflexivity. exact Hpos. }
  (* fs_place (asan_stack_malloc_c.v:34-36) *)
  assert (HPL : SMC.fs_place mem3 (RG0f.ly_F ly3)).
  { split; [lia|]. split; [exact HFal|]. split; [unfold SMC.ASAN_GT; lia|]. split.
    - intros a Ha. unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END.
      unfold SMC.FS_SIZE in Ha. lia.
    - apply (y1_stk_of_present (RA0n.w_H W3)); [lia | unfold SMC.FS_SIZE; lia |].
      intros a Ha. apply (F_PRESENT ly3 S3 W3 mem3 md3 a HAR). unfold RG0f.kFakeStackSize. unfold SMC.FS_SIZE in Ha.
      lia. }
  (* the flag byte reads 1: am_flags (fs_flags_ok, YG0n.v:152-154) at frames S3 = [(6, pos)], read through the view *)
  assert (HFLG : LMem.bytes_at AImg0.rsegs mem3 (SMC.fs_flag (RG0f.ly_F ly3) 6 (ACtlCut.c_fpos cx))
                   (Z_to_bv 8 1 :: nil)).
  { pose proof (RG0n.am_flags _ _ _ _ HM 6 (ACtlCut.c_fpos cx) ltac:(lia) Hpos) as Hfv.
    assert (Emp : RG00.mem_pos (RG01.frames S3) 6 (ACtlCut.c_fpos cx) = true).
    { rewrite HF6. cbn [RG00.mem_pos]. rewrite !Z.eqb_refl. reflexivity. }
    rewrite Emp in Hfv.
    destruct Hflp as [Hh (b & Hb)].
    unfold RG0n.aview, RP09.mbyte, RK04.mrestrict in Hfv. rewrite Hh, Hb in Hfv. cbn [option_map] in Hfv.
    injection Hfv as Hb1.
    assert (Eb : b = Z_to_bv 8 1) by (apply bv_eq; rewrite Hb1; reflexivity).
    rewrite Efl. split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
    cbn [nth_error]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
    unfold LMem.mrd, LMem.wa. rewrite Hb, Eb. reflexivity. }
  (* the frame's back-pointer word: the cut's FRAHC conjunct *)
  assert (HBP : LMem.bytes_at AImg0.rsegs mem3 (fr + SMC.fs_B 6 - 8)
                  (LMem.le8 (Z_to_bv 64 (SMC.fs_flag (RG0f.ly_F ly3) 6 (ACtlCut.c_fpos cx))))).
  { change (SMC.fs_B 6) with 4096. replace (fr + 4096 - 8) with (fr + 4088) by lia.
    rewrite Efl, Efl'. exact Qbp. }
  (* the callee window [sp - 32, sp) and the room below it *)
  assert (HSTK : LFrame.stk AImg0.rsegs mem3 (sp - 32) sp).
  { apply (y1_stk_of_present (RA0n.w_H W3)); [lia | lia |].
    intros a Ha. apply Hpres. lia. }
  assert (HROOM : RG0f.ly_F ly3 + SMC.FS_SIZE <= sp - 32) by (unfold SMC.FS_SIZE; lia).
  assert (HHI : ART.HIGHMEM_BEG <= sp - 32) by (unfold ART.HIGHMEM_BEG; lia).
  assert (HSPA : sp <= ART.APPMEM_END) by (unfold ART.APPMEM_END; lia).
  (* the footprint ranges, from visibility *)
  assert (Rimg : LExecF.rng (PB.RNG_W (RA0n.w_H W3)) 0x10000 0x5ee000).
  { exact (PB.rng_of_visible _ _ _ (PB.img_vis_W W3)). }
  assert (Rstk : LExecF.rng (PB.RNG_W (RA0n.w_H W3)) (sp - 32) 32).
  { apply PB.rng_RNG_W; [lia | lia |]. intros a Ha. exact (proj1 (Hpres a ltac:(lia))). }
  assert (Rfs : LExecF.rng (PB.RNG_W (RA0n.w_H W3)) (RG0f.ly_F ly3) SMC.FS_SIZE).
  { apply PB.rng_RNG_W; [lia | unfold SMC.FS_SIZE; lia |]. intros a Ha.
    refine (proj1 (F_PRESENT ly3 S3 W3 mem3 md3 a HAR _)). unfold RG0f.kFakeStackSize. unfold SMC.FS_SIZE in Ha.
    lia. }
  assert (Rsh : LExecF.rng (PB.RNG_W (RA0n.w_H W3)) (ART.shadow_addr fr) 512).
  { apply PB.rng_RNG_W; [lia | lia |]. intros a Ha.
    assert (Hi : 0 <= a - ART.shadow_addr fr < RG00.fs_frame_bytes 6 / 8)
      by (change (RG00.fs_frame_bytes 6 / 8) with 512; lia).
    destruct (Hshp _ Hi) as [[Hh _] _].
    rewrite <- Efr3, <- y1_shadow_addr in Hh.
    replace (ART.shadow_addr fr + (a - ART.shadow_addr fr)) with a in Hh by lia. exact Hh. }
  (* the run (YTailF.v y1_evt_F_on: premise shadow_rw_on of the frame's 512 shadow bytes, callee stack_free_6_F_on,
     post forall P), at the canonical map of regs3 and ctrl's FPState built from the core's fx *)
  pose proof (@YTF.y1_evt_F_on (AK11.mkFP RK11.fp_regs RK11.fp_csr) (PB.RNG_W (RA0n.w_H W3))
    (RSem.reg_get regs3 1) (RSem.reg_get regs3 2) (RSem.reg_get regs3 3) (RSem.reg_get regs3 4)
    (RSem.reg_get regs3 5) (RSem.reg_get regs3 6) (RSem.reg_get regs3 7) (RSem.reg_get regs3 10)
    (RSem.reg_get regs3 11) (RSem.reg_get regs3 12) (RSem.reg_get regs3 13) (RSem.reg_get regs3 14)
    (RSem.reg_get regs3 15) (RSem.reg_get regs3 16) (RSem.reg_get regs3 17) (RSem.reg_get regs3 28)
    (RSem.reg_get regs3 29) (RSem.reg_get regs3 30) (RSem.reg_get regs3 31) (RSem.reg_get regs3 8)
    (RSem.reg_get regs3 9) (RSem.reg_get regs3 18) (RSem.reg_get regs3 19) (RSem.reg_get regs3 20)
    (RSem.reg_get regs3 21) (RSem.reg_get regs3 22) (RSem.reg_get regs3 23) (RSem.reg_get regs3 24)
    (RSem.reg_get regs3 25) (RSem.reg_get regs3 26) (RSem.reg_get regs3 27)
    mem3 fr (RG0f.ly_F ly3) (ACtlCut.c_fpos cx) (sp - 32) sp
    Ha0 R11 EspZ EfrFS Hj HPL HFLG HBP HAC (A.ShadowRwOn.shadow_rw_on_mono _ _ _ HRsh Hcut) HSTK ltac:(lia) HROOM
    HHI HSPA HRO (PB.rng_bytes_RNG_W _) Rimg Rstk Rfs Rsh (YTF.stack_free_6_F_on_gen _)) as HRUN.
  (* G4 (first half): the run as fsteps over the core's segment list *)
  pose proof (PB.fevt_of_evtF _ _ _ HRUN) as HFS. clear HRUN.
  rewrite <- PB.tfibsegs_rsegs in HFS.
  destruct HFS as (ms' & Hrun & HQ).
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's canonical map *)
  rewrite PB.cfg_at_MS.
  change (ACtlCut.cut_pc C_A82b9c) with 0x82b9c.
  apply (RA0nR.SRr_xregs_eqv segs W3 (LRegs.mkR_of regs3) regs3 RK11.fp_regs (Z_to_bv 64 0x82b9c) RK11.fp_csr None
           mem3 (RK11.seg_rom segs) md3 (POST cx));
    [| exact (LRegs.xregs_eqv_sym _ _ (LRegs.mkR_of_eqv regs3))].
  (* G4: the lift (the release law below takes the fsteps run itself) *)
  apply (RA0nR.SRr_fsteps segs KIT.kit_wx W3 _ ms' md3 (PB.RNG_W (RA0n.w_H W3)) (POST cx) Hrun
           (PB.fp_avoids_RNG_W _)).
  intros md' Hsbm.
  (* G5: the run's post *)
  destruct HQ as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' &
    Ems & MU & WM & RO' & ST' & FLG' & SHB' & SW').
  lazymatch type of Hrun with RK04R.fsteps _ _ ?s0 _ => set (ms0 := s0) in Hrun end.
  rewrite Efl in MU.
  (* YTailF's `Frame.munch` is named through its own Imports; it is lib/Lib/Frame.v's munch by conversion *)
  lazymatch type of MU with _ ?w _ _ => set (WR := w) in MU end.
  assert (MUL : LFrame.munch WR mem3 m') by exact MU.
  (* every byte of the run's write list is the flag byte, a byte of the frame's shadow, or the callee window *)
  assert (Hwr : forall a, 0 <= a < 2 ^ 64 -> ~ LFrame.outside WR a ->
      RCbq.awr_byte A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (RG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx))
        (RG0d.ablocks B ly3 S3) ly3 ((6, ACtlCut.c_fpos cx) :: []) a \/
      a = RG0f.flag_addr ly3 6 (ACtlCut.c_fpos cx)).
  { intros a Ha Hno. unfold WR in Hno. cbn [LFrame.outside] in Hno.
    destruct (Z.eq_dec a (RG0f.flag_addr ly3 6 (ACtlCut.c_fpos cx))) as [Eq|Hne]; [right; exact Eq|].
    left.
    assert (Hcase : (ART.shadow_addr fr <= a < ART.shadow_addr fr + 512) \/ (sp - 32 <= a < sp)).
    { destruct (Z_lt_le_dec a (ART.shadow_addr fr)); destruct (Z_lt_le_dec a (ART.shadow_addr fr + 512));
        destruct (Z_lt_le_dec a (sp - 32)); destruct (Z_lt_le_dec a sp);
        try (left; lia); try (right; lia);
        exfalso; apply Hno; (split; [lia | split; [lia | split; [lia | exact I]]]). }
    unfold RCbq.awr_byte.
    destruct Hcase as [Hs|Hs].
    - right; right; right. unfold RCbq.in_frames.
      exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
      unfold RG0n.in_zr; cbn [fst snd]. rewrite <- Efr3, <- y1_shadow_addr.
      change (RG00.fs_frame_bytes 6 / 8) with 512. exact Hs.
    - left. unfold A.ACfn.LLVMF_STK. lia. }
  (* the flag byte reads 0 after the run *)
  assert (Hflag0 : RP09.mbyte segs (ms_mem ms') (RG0f.flag_addr ly3 6 (ACtlCut.c_fpos cx)) = Some (Z_to_bv 8 0)).
  { rewrite Ems. destruct FLG' as (_ & _ & F0).
    specialize (F0 O ltac:(cbn [length]; lia)). cbn [nth_error] in F0. change (Z.of_nat 0) with 0 in F0.
    rewrite Z.add_0_r, Efl in F0. unfold LMem.mrd, LMem.wa in F0. unfold RP09.mbyte. exact F0. }
  assert (MU' : LFrame.munch WR (ms_mem ms0) (ms_mem ms')) by (rewrite Ems; exact MUL).
  (* the journal at the release: own [(6, pos)] -> [], S3 -> stack_free_state 6 pos S3 *)
  pose proof (REL6 LAWS (RG0t.astack_free_law_ok segs B) KIT.kit_wx ltac:(lia)
    A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx)
    (ACtlCut.c_md cx) [] ly3 S3 W3 ms0 ms' md3 md' k (ACtlCut.c_fpos cx) (PB.RNG_W (RA0n.w_H W3)) WR
    HJ Hrun (PB.fp_avoids_RNG_W _) MU' Hsbm Hwr Hflag0) as HJ'.
  subst ms'.
  lazymatch goal with |- RA0n.SRr _ _ (mkCfg (LMState.MS ?r _ _ _ _ _ _) _) _ => set (R := r) end.
  (* ProgBridge.cfg_at_MS read backwards (eq_refl), at the exit cut's pc *)
  change (RA0n.SRr segs W3 (RG0d.cfg_at segs (ACtlCut.cut_pc C_A82bb0) R m' md') (POST cx)).
  assert (Hdj : LFrame.disjoint_from WR ART.RT_LO (ART.RT_HI - ART.RT_LO)).
  { unfold WR, ART.RT_LO, ART.RT_HI. cbn [LFrame.disjoint_from].
    split; [left; lia|]. split; [left; lia|]. split; [left; lia | exact I]. }
  apply (HX cx [] fr k ly3 (RG01.stack_free_state 6 (ACtlCut.c_fpos cx) S3) W3 R m' md' HB).
  - (* journal: the release law's, at own0 *)
    exact HJ'.
  - (* frames: del_pos [(6, pos)] 6 pos = [] = own0 *)
    change (RG01.frames (RG01.stack_free_state 6 (ACtlCut.c_fpos cx) S3))
      with (RG00.del_pos (RG01.frames S3) 6 (ACtlCut.c_fpos cx)).
    rewrite HF6. cbn [RG00.del_pos]. rewrite ?Z.eqb_refl. reflexivity.
  - (* the frame law: own0 owns nothing *)
    intros cid pos' Hin'. simpl in Hin'. destruct Hin'.
  - (* the event bound: EV_LLVMF on both cuts *)
    exact Hk.
  - (* the exit body, C_A82bb0 (ACtlCutP.v:3025-3032) *)
    cbv beta iota delta [ACtlCut.cut_body ACtlCutP.C_A82bb0].
    split; [unfold RG0d.ablocks; rewrite RG01.blocks_stack_free_state; exact HP|].
    split; [exact R8|].
    split; [exact R3|].
    split; [exact (eq_trans R4 (eq_sym Htp))|].
    apply (LFrame.bytes_at_transport segs WR mem3 m' _ _ Hsaved MUL).
    rewrite y1_saved_len. change (Z.of_nat 104) with 104.
    unfold WR. cbn [LFrame.disjoint_from].
    split; [right; lia|]. split; [right; lia|]. split; [right; lia | exact I].
  - (* ctl_rt_C at stack_free_state 6 pos S3: its regions lie in the entry's (the frame leaves frames; blocks, layout
       unchanged), carried across the run by its forall-P post; asan_cells kept (no write in the runtime range);
       ro_agree from the run's post *)
    assert (HRsub : forall a, A.ACtlRtC.cut_shadow B ly3 (RG01.stack_free_state 6 (ACtlCut.c_fpos cx) S3) a ->
                              A.ACtlRtC.cut_shadow B ly3 S3 a).
    { intros a [(cid & pos' & Hin' & Ha) | [(p & n & Hin' & Ha) | Ha]].
      - exfalso. change (RG01.frames (RG01.stack_free_state 6 (ACtlCut.c_fpos cx) S3))
          with (RG00.del_pos (RG01.frames S3) 6 (ACtlCut.c_fpos cx)) in Hin'.
        rewrite HF6 in Hin'. cbn [RG00.del_pos] in Hin'. rewrite ?Z.eqb_refl in Hin'. simpl in Hin'. exact Hin'.
      - right; left. exists p, n. split; [|exact Ha].
        unfold RG0d.ablocks in Hin' |- *. rewrite RG01.blocks_stack_free_state in Hin'. exact Hin'.
      - right; right. exact Ha. }
    split; [|split; [|split]].
    + exact (ARF.asan_cells_kept WR mem3 m' HAC MUL Hdj).
    + exact (SW' _ (A.ShadowRwOn.shadow_rw_on_mono _ _ _ HRsub Hcut)).
    + exact (SW' _ Himg).
    + exact RO'.
Qed.

End GlueY1.
