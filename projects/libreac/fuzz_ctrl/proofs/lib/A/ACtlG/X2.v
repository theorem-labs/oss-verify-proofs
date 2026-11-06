(* lib/A/ACtlG/X2.v -- GLUE for stage seg_X2 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   W5 tail), and the shared shadow-fill tail 0x82b24 -> 0x82b80 that seg_X1's byte-20 = 0 arm also runs
   (lib/A/ACtlG/X1.v Requires this file for x2_tail).  Written by a Theorem Labs lane; single writer.
   rule 24: no function proved (stage glue of a walk; At ossv/recipes c5e779efe8c (2026-10-31), no released proof of this unit's LLVMFuzzerTestOneInput outside this unit).

   WHAT IT PROVES
     glue_seg_X2 : forall POST, CF POST C_Jrel -> CF POST C_A82b20
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_X2.  Entry C_A82b20 (0x82b20), exit C_Jrel (0x82b80).  Segment X2 is Seg/X12.v seg_X2 (:814 at U):
     0x82b20 beqz a0,0x82bf4 (the failure exit; NOT taken, a0 = q > 0 from the entry body)
   then the shared block 0x82b24 - 0x82b80 (Seg/X12.v x12_tail :604):
     0x82b24 li a0,-8; twenty sb a0,off(s3) at offsets 352 353 354 360-364 348-351 339 340 346 347 328 336-338 of the
     frame's 392 shadow bytes (s3 = S(fr)); 0x82b78 ld s5,24(s1); 0x82b7c ld s6,16(s1).
   ACtl.v's glue comment names only x12_x2_evt; the block after it is x12_store_evt, run here through x2_tail.

   THE PROOF (glue-pattern.md G1-G5)
   x2_tail (from a state at 0x82b24 carrying C_A82b20's shell facts and FRAC, to C_Jrel):
   G2  the store run's premises: s1 = A, s3 = S(fr) (FRAC registers 9 / 19); the 392 shadow bytes present and
       writable (AR_frames_law's shadow bytes: present at the cut's own memory); the spill cells [A + 24] = sel = fr and
       [A + 16] = fr (FRAC); the bounds S(fr) + 392 <= A (the frame is app memory, AR_frames_law's in_app; A is above
       the stack floor, the journal's astk_ok and the ceiling's range); footprint ranges visible: the shadow
       sub-range (AR_frames_law) and the two spill cells (the journal's stack-window presence).
   G3  ProgBridge.cfg_at_MS, YA0nR.SRr_xregs_eqv to mkR_of.
   G4  X12F.x12_store_evt_F at RNG_W (w_H W3), ProgBridge.fevt_of_evtF / tfibsegs_rsegs, YA0nR.SRr_fevt_hid.
   G5  C_Jrel at the run's end map R and memory m': journal by YCbq.ajournal_exec with Wr := [S(fr) + 328, S(fr) + 365)
       (awr_byte's in_frames shadow case), FRAHC with header 0x41b58ab3 (registers computed through R; memory carried
       across the window by Lib.Frame.bytes_at_transport; the 392 shadow bytes re-read from the run's post stk;
       Batch3's trailer word q64 m (fr + 4088) (flag_addr ..) carried from FRAC by jr_q64_keep, the window lying off
       the frame), s5 = sel, s6 = fr; ctl_rt_C kept at the same ly3 S3 (cells are image bytes, ro bytes are image
       bytes, both below the shadow; a shadow byte of the window is present by the run's post stk, whatever region).
   glue_seg_X2:
   G1  C_A82b20's body; G3 as above; G4 X12F.x12_x2_evt_F, register-only, lifted with YA0nR.SRr_fevt at the empty
       footprint Kit.kit_RNG0; G5 x2_tail at the run's end map (journal by ajournal_exec with the empty write set,
       FRAC by Kit.kit_frac_move).

   SECTION HYPOTHESES
   - LAWS: the core's AR law record (ACtl.v's LAWS).  No other: the runs are Required from Seg/X12F.v.

   CITED BY NAME: X12F.x12_x2_evt_F / x12_store_evt_F; ProgBridge RNG_W / fp_avoids_RNG_W / rng_of_visible /
   fevt_of_evtF / tfibsegs_rsegs / cfg_at_MS / range_visible; YA0nR SRr_xregs_eqv / SRr_fevt / SRr_fevt_hid; YCbq
   ajournal_exec; YK04 find_segment_some_spec; YK1b mem_grows_refl; YG0f ASAN_CEIL_range; Lib.Frame
   bytes_at_transport / stk_bytes; Regs6ss mkR_of / mkR_of_eqv / xregs_eqv_sym; Kit kit_wx / kit_segs_low /
   kit_frac_move / kit_RNG0; this lane's Jrel.v jr_mem_of_mrd / jr_q64_keep / jr_saved_len / jr_cells_keep.

   CLOSURE: as Jrel.v (full-path module aliases for every Reusable / Lib module); gains Seg/X12F.v's closure (Seg/X12.v,
   SlotInv, AsanRTInv, Contract, FrameAPI, MemNorm, the memchr wrapper's contract files), as the closure rule allows.

   BUILD STATE: see the commit message (type-check, planning core, port_core_refused substitution in the build
   workspace only). *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* reg_get (the explicit register binders of the _F runs are Regs6ss.mkR_of's fields), as YK11.v:11 imports it *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2k.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACfn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlK.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlRtC.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.X12F.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.Kit.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.Jrel.
Import ListNotations.
Local Open Scope Z_scope.

Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module RK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module RK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module RA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module RG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module RG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module RG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module RG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module RC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Module RCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LMM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module X12F := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.X12F.
Module JR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.Jrel.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* A byte at or above the low-memory end (every shadow byte) is not an image byte: every image segment ends below
   kLowMemEnd (Kit.kit_segs_low). *)
Lemma x2_not_img : forall a, RG0f.kLowMemEnd <= a -> ~ RG0d.in_img segs a.
Proof. intros a Ha Hi. pose proof (A.ACtlG.Kit.kit_segs_low a Hi) as H. lia. Qed.

Section GlueX2.

(* ACtl.v's Section Ctl shape (84ef756918c), in its order: the core class by full path, the same Variables and
   Hypotheses, except TFIB_SYMS / TFIB_LIB, which no glue step here reads and whose types (A.AF0m.CtrlTSyms,
   A.ACeh.TfibLib) would put two planning-core stand-in files into this file's Require closure.  End GlueX2 keeps
   only what each lemma uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : RG0f.asyms.
Variable MT : RC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> RG0d.in_img segs a.
(* The core's AR laws (YCbq.v Section a0's hypothesis; ACtl.v's LAWS). *)
Hypothesis LAWS : RG0d.AR_laws segs B.
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.

(* ACtl.v's notation block, verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82b20 := (ACtlCutP.C_A82b20 B).
Local Notation C_Jrel := (ACtlCutP.C_Jrel B).

(* ---------------------------------------------------------------------------------------------------------
   The shadow-fill tail 0x82b24 -> 0x82b80 (Seg/X12.v x12_tail :604, run x12_store_evt), from the shell facts of
   an own6 cut and FRAC at sel = fr, to C_Jrel. *)
Lemma x2_tail : forall POST, CF POST C_Jrel ->
  forall cx fr k ly3 S3 W3 regs3 mem3 md3,
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  RCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  RG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = RG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  k <= A.ACtlK.EV_LLVMF ->
  Permutation (RG0d.ablocks B ly3 S3) (RG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) ->
  ACtlCutP.FRAC B cx fr fr regs3 mem3 ->
  A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 ->
  RA0n.SRr segs W3 (RG0d.cfg_at segs 0x82b24 regs3 mem3 md3) (POST cx).
Proof.
  intros POST HX cx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk HP HFRAC Hrt.
  destruct HFRAC as (A & sp & R2 & Hsp16 & Hspz & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAc & HspA &
    HfrA & HA416 & Hsplo & Hcapp & Q304 & Q24 & Q16 & Qhdr & Qret & Hsh & Hsaved & Htrl).
  destruct Hrt as (Hcells & Hcut & Himg & Hro).
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  destruct Hastk as (_ & _ & Hc1 & Hc2 & _).
  destruct (@RG0f.ASAN_CEIL_range rc) as ((Hcl & Hch) & _). unfold RG0f.ASAN_CEIL in Hcl, Hch.
  unfold A.ACfn.LLVMF_STK in Hc2, Hpres.
  (* the frame and its 512 shadow bytes, from the journal's AR (AR_frames_law) and the frame law *)
  assert (Hin : In (6, ACtlCut.c_fpos cx) (RG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = RG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)) by (apply HL; left; reflexivity).
  assert (EF3 : RG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold RG0f.frame_addr. rewrite EF. reflexivity. }
  assert (Hfsb : RG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (Hfl : RG0d.AR_frames_law segs B) by (destruct LAWS; assumption).
  destruct (Hfl ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (_ & Happ & _ & Hshb).
  rewrite EF3, Hfsb in Happ, Hshb. change (4096 / 8) with 512 in Hshb.
  assert (ESh : RG0f.shadow_addr fr = ACtlCutP.Sfr fr).
  { unfold RG0f.shadow_addr, RG0f.SHADOW_OFF, ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K. lia. }
  rewrite ESh in Hshb.
  unfold RG0f.in_app, RG0f.kLowShadowBeg, RG0f.kHighMemBeg in Happ.
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold ART.APPMEM_END in Hcapp.
  assert (HShv : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000) by reflexivity.
  pose proof (Z.div_mod fr 8 ltac:(lia)) as Dfr. pose proof (Z.mod_pos_bound fr 8 ltac:(lia)) as Mfr.
  set (Sh := ACtlCutP.Sfr fr) in *.
  assert (HShA : Sh + 392 <= A) by lia.
  assert (HSh0 : 0x7fff8000 <= Sh) by lia.
  (* the store run's window: present and writable, and visible *)
  assert (HSTK : LFR.stk A.Img0.rsegs mem3 Sh (Sh + 392)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (proj1 (Hshb (a - Sh) ltac:(lia))) as (_ & b & Eb).
    replace (Sh + (a - Sh)) with a in Eb by lia.
    split; [unfold wview, LMM.wa; rewrite Eb; discriminate | exists b; unfold LMM.mrd, LMM.wa; rewrite Eb; reflexivity]. }
  assert (Hvsh : PB.range_visible (RA0n.w_H W3) (Sh + 328) 37).
  { split; [lia|]. split; [lia|]. intros a Ha.
    pose proof (proj1 (proj1 (Hshb (a - Sh) ltac:(lia)))) as Hv.
    replace (Sh + (a - Sh)) with a in Hv by lia. exact Hv. }
  assert (Hvwin : forall lo, A + 16 <= lo -> lo + 8 <= A + 32 -> PB.range_visible (RA0n.w_H W3) lo 8).
  { intros lo H1 H2. split; [lia|]. split; [lia|]. intros a Ha.
    exact (proj1 (Hpres a ltac:(lia))). }
  (* G3 *)
  rewrite PB.cfg_at_MS.
  apply (RA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 RK11.fp_regs
           (Z_to_bv 64 0x82b24) RK11.fp_csr None mem3 (RK11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  (* G4: x12_store_evt_F (its binder order: ra0 gp tp ... t6, then sp) *)
  pose proof (X12F.x12_store_evt_F (PB.RNG_W (RA0n.w_H W3))
    (reg_get regs3 1) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6) (reg_get regs3 7)
    (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11) (reg_get regs3 12)
    (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16) (reg_get regs3 17)
    (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21) (reg_get regs3 22)
    (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25) (reg_get regs3 26) (reg_get regs3 27)
    (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)
    (reg_get regs3 2) RK11.fp_regs RK11.fp_csr mem3 A Sh fr fr
    R9 R19 HSTK Q24 Q16 ltac:(lia) ltac:(lia) HShA ltac:(lia)
    (PB.rng_of_visible _ _ _ Hvsh) (PB.rng_of_visible _ _ _ (Hvwin (A + 24) ltac:(lia) ltac:(lia)))
    (PB.rng_of_visible _ _ _ (Hvwin (A + 16) ltac:(lia) ltac:(lia)))) as HRUN.
  pose proof (PB.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- PB.tfibsegs_rsegs in HFS.
  apply (RA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (PB.RNG_W (RA0n.w_H W3)) _ (POST cx) HFS).
  { apply PB.fp_avoids_RNG_W. }
  (* G5 *)
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (m' & Ems & MU & WM & HSTK').
  subst ms'.
  assert (Hhid' : forall x : word, RA0n.w_H W3 x = true -> m' x = mem3 x) by exact Hhid.
  clear Hhid.
  match goal with |- RA0n.SRr _ _ (mkCfg (LMS.MS ?R0 _ _ _ _ _ _) _) _ => set (R := R0) end.
  change (RA0n.SRr segs W3 (RG0d.cfg_at segs (ACtlCut.cut_pc C_Jrel) R m' md') (POST cx)).
  assert (K2 : RK11.getr R 2 = RK11.getr regs3 2) by reflexivity.
  assert (K3 : RK11.getr R 3 = RK11.getr regs3 3) by reflexivity.
  assert (K4 : RK11.getr R 4 = RK11.getr regs3 4) by reflexivity.
  assert (K8 : RK11.getr R 8 = RK11.getr regs3 8) by reflexivity.
  assert (K9 : RK11.getr R 9 = RK11.getr regs3 9) by reflexivity.
  assert (K19 : RK11.getr R 19 = RK11.getr regs3 19) by reflexivity.
  assert (K26 : RK11.getr R 26 = RK11.getr regs3 26) by reflexivity.
  assert (K21 : RK11.getr R 21 = Z_to_bv 64 fr) by reflexivity.
  assert (K22 : RK11.getr R 22 = Z_to_bv 64 fr) by reflexivity.
  assert (Hout : forall x : word, ~ (Sh + 328 <= bv_unsigned x < Sh + 365) -> m' x = mem3 x).
  { intros x Hx. apply MU. cbn [LFR.outside]. split; [exact Hx | exact I]. }
  (* the frame header and the cells after it are app memory, apart from the shadow window *)
  assert (Hfrw : fr + 24 <= Sh + 328 \/ Sh + 365 <= fr) by lia.
  apply (HX cx [] fr k ly3 S3 W3 R m' md' HB).
  - (* journal: ajournal_exec over the shadow window [S(fr) + 328, S(fr) + 365) *)
    eapply (RCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => Sh + 328 <= a < Sh + 365).
    + exact HJ.
    + intros x Hx. unfold RK04.mrestrict. rewrite (Hout x Hx). reflexivity.
    + intros x Hx. unfold RK04.mrestrict in *. destruct (RA0n.w_H W3 x) eqn:Ehx; [exact Hx|].
      destruct (Z_le_gt_dec (Sh + 328) (bv_unsigned x)) as [Hx1|Hx1];
        [destruct (Z_lt_ge_dec (bv_unsigned x) (Sh + 365)) as [Hx2|Hx2]|].
      * destruct HSTK' as (_ & _ & Hs').
        destruct (Hs' (bv_unsigned x) ltac:(lia)) as (_ & b & Hb).
        unfold LMM.wa in Hb. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb.
        rewrite (JR.jr_mem_of_mrd m' x b ltac:(apply x2_not_img; unfold RG0f.kLowMemEnd; lia) Hb). discriminate.
      * rewrite (Hout x ltac:(lia)). exact Hx.
      * rewrite (Hout x ltac:(lia)). exact Hx.
    + exact Hhid'.
    + exact Hsbm.
    + intros a Ha. right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
      right. hnf. cbn [fst snd]. rewrite EF3, Hfsb, ESh. change (4096 / 8) with 512. fold Sh. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: EV_LLVMF on both cuts *)
    exact Hk.
  - (* the exit body, C_Jrel (ACtlCutP.v C_Jrel), at sel = fr *)
    cbv beta iota delta [ACtlCut.cut_body ACtlCutP.C_Jrel].
    split; [exact HP|].
    split.
    { exists A, sp.
      split; [rewrite K2; exact R2|]. split; [exact Hsp16|].
      split; [unfold RG0d.spZ in *; rewrite K2; exact Hspz|].
      split; [rewrite K4; exact R4|].
      split; [unfold ACtlCut.rgv; rewrite K8; exact R8|].
      split; [unfold ACtlCut.rgv; rewrite K9; exact R9|].
      split; [rewrite K3; exact R3|].
      split; [unfold ACtlCut.rgv; rewrite K19; exact R19|].
      split; [unfold ACtlCut.rgv; rewrite K26; exact R26|].
      split; [exact Hfr32|]. split; [exact HA32|]. split; [exact HAc|]. split; [exact HspA|].
      split; [unfold ACtlCutP.FRAME_BYTES; exact HfrA|]. split; [exact HA416|]. split; [exact Hsplo|].
      split; [unfold ART.APPMEM_END; exact Hcapp|].
      split; [apply (JR.jr_q64_keep mem3 m' (Sh + 328) (Sh + 365) (A + 304) fr Q304 MU); lia|].
      split; [apply (JR.jr_q64_keep mem3 m' (Sh + 328) (Sh + 365) fr 0x41b58ab3 Qhdr MU); lia|].
      split; [apply (JR.jr_q64_keep mem3 m' (Sh + 328) (Sh + 365) (fr + 16) A.ACfn.A_LLVMF Qret MU); lia|].
      split.
      { destruct (LFR.stk_bytes A.Img0.rsegs m' Sh (Sh + 392) HSTK' ltac:(lia)) as (bs & Hbl & Hbs).
        exists bs. split; [exact Hbs|]. rewrite Hbl. replace (Sh + 392 - Sh) with 392 by lia. reflexivity. }
      split.
      { apply (LFR.bytes_at_transport segs [(Sh + 328, Sh + 365)] mem3 m' _ _ Hsaved MU).
        cbn [LFR.disjoint_from]. rewrite JR.jr_saved_len. split; [lia | exact I]. }
      (* Batch3's fake-frame trailer word at fr + 4088 (FRAC's to FRAHC's): the run writes only the shadow window
         [S(fr) + 328, S(fr) + 365), which lies off the frame. *)
      apply (JR.jr_q64_keep mem3 m' (Sh + 328) (Sh + 365) (fr + 4088) _ Htrl MU); lia. }
    split; [unfold ACtlCut.rgv; exact K21|].
    unfold ACtlCut.rgv. exact K22.
  - (* ctl_rt_C across the shadow stores; the state stays ly3 S3, so each region is the entry's *)
    (* a shadow byte of the window is present and writable by the run's post; any other one is unchanged *)
    assert (Hkeep : forall Pr : Z -> Prop, A.ShadowRwOn.shadow_rw_on Pr mem3 -> A.ShadowRwOn.shadow_rw_on Pr m').
    { intros Pr Hon a HRg Ha. destruct (Hon a HRg Ha) as (Hw & b & Hb).
      unfold ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END, ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG in Ha.
      destruct (Z_le_gt_dec (Sh + 328) a) as [Ha1|Ha1]; [destruct (Z_lt_ge_dec a (Sh + 365)) as [Ha2|Ha2]|].
      * destruct HSTK' as (_ & _ & Hs'). exact (Hs' a ltac:(lia)).
      * assert (Ea : m' (LMM.wa a) = mem3 (LMM.wa a)) by (apply Hout; rewrite LMM.wa_unsigned by lia; lia).
        split; [unfold wview in *; rewrite Ea; exact Hw | exists b; unfold LMM.mrd in *; rewrite Ea; exact Hb].
      * assert (Ea : m' (LMM.wa a) = mem3 (LMM.wa a)) by (apply Hout; rewrite LMM.wa_unsigned by lia; lia).
        split; [unfold wview in *; rewrite Ea; exact Hw | exists b; unfold LMM.mrd in *; rewrite Ea; exact Hb]. }
    split; [|split; [|split]].
    + (* the runtime cells are image bytes, below the shadow *)
      apply (JR.jr_cells_keep mem3 m'); [|exact Hcells].
      intros x Hx. apply Hout. lia.
    + exact (Hkeep _ Hcut).
    + exact (Hkeep _ Himg).
    + (* a read-only byte is an image byte, below the shadow *)
      intros x Hx.
      destruct (Z_le_gt_dec (Sh + 328) (bv_unsigned x)) as [Hx1|Hx1];
        [destruct (Z_lt_ge_dec (bv_unsigned x) (Sh + 365)) as [Hx2|Hx2]|].
      * exfalso. unfold LMM.ro_addr in Hx.
        destruct (find_segment A.Img0.rsegs (bv_unsigned x) 1) as [sg|] eqn:Ef; [|discriminate].
        destruct (RK04.find_segment_some_spec _ _ _ _ Ef) as (Hs & Hb1 & Hb2).
        apply (x2_not_img (bv_unsigned x)); [unfold RG0f.kLowMemEnd; lia|].
        exists sg. split; [exact Hs | lia].
      * pose proof (Hro x Hx) as E. unfold LMM.mrd in E |- *. rewrite (Hout x ltac:(lia)). exact E.
      * pose proof (Hro x Hx) as E. unfold LMM.mrd in E |- *. rewrite (Hout x ltac:(lia)). exact E.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_X2 : forall POST, CF POST C_Jrel -> CF POST C_A82b20.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_A82b20 (ACtlCutP.v C_A82b20) *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82b20] in Hbody.
  destruct Hbody as (HP & HFRAC & Hn & Hour & (q & Hq & Hqb)).
  (* G3 *)
  rewrite PB.cfg_at_MS.
  change (ACtlCut.cut_pc C_A82b20) with 0x82b20.
  apply (RA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 RK11.fp_regs
           (Z_to_bv 64 0x82b20) RK11.fp_csr None mem3 (RK11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  (* G4: x12_x2_evt_F (beqz a0 not taken; no memory access), at the empty footprint *)
  pose proof (X12F.x12_x2_evt_F A.ACtlG.Kit.kit_RNG0
    (reg_get regs3 1) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6) (reg_get regs3 7)
    (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11) (reg_get regs3 12)
    (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16) (reg_get regs3 17)
    (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21) (reg_get regs3 22)
    (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25) (reg_get regs3 26) (reg_get regs3 27)
    (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)
    (reg_get regs3 2) RK11.fp_regs RK11.fp_csr mem3 q Hq Hqb) as HRUN.
  pose proof (PB.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- PB.tfibsegs_rsegs in HFS.
  apply (RA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx) HFS).
  { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
  (* G5: the run's end state at 0x82b24, the same registers and memory; then the shared tail *)
  intros ms' md' HQ0 Hsbm.
  subst ms'.
  match goal with |- RA0n.SRr _ _ (mkCfg (LMS.MS ?R0 _ _ _ _ _ _) _) _ => set (R := R0) end.
  change (RA0n.SRr segs W3 (RG0d.cfg_at segs 0x82b24 R mem3 md') (POST cx)).
  assert (K2 : RK11.getr R 2 = RK11.getr regs3 2) by reflexivity.
  assert (K3 : RK11.getr R 3 = RK11.getr regs3 3) by reflexivity.
  assert (K4 : RK11.getr R 4 = RK11.getr regs3 4) by reflexivity.
  assert (K8 : RK11.getr R 8 = RK11.getr regs3 8) by reflexivity.
  assert (K9 : RK11.getr R 9 = RK11.getr regs3 9) by reflexivity.
  assert (K19 : RK11.getr R 19 = RK11.getr regs3 19) by reflexivity.
  assert (K26 : RK11.getr R 26 = RK11.getr regs3 26) by reflexivity.
  apply (x2_tail POST HX cx fr k ly3 S3 W3 R mem3 md' HB).
  - (* journal: no byte written, the model materialized *)
    eapply (RCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply RK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha].
  - exact HF.
  - exact HL.
  - exact Hk.
  - exact HP.
  - exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 K9 K19 K26).
  - exact Hrt.
Qed.

End GlueX2.
