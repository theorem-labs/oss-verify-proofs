(* lib/A/ACtlG/F8.v -- GLUE for stage seg_F8 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v (at head lib/A/ACtl.v:766) (an earlier version, blob c4edf0be7fe, not in this delivery)).  Written by a Theorem Labs lane; single writer of this file.
   rule 24: no function proved (stage glue of a walk; kind: segment lemma).

   WHAT IT PROVES
     glue_seg_F8 : forall POST (j : nat), CF POST (ix_cut C_A81f88_at [Z.of_nat j]) ->
                                          CF POST (ix_cut C_A81f7c_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_F8.  Segment F8 is 0x81f7c -> 0x81f88 (Seg/F8.v): `beqz a0` not taken, `mv a0,s8`, and the
   SECOND reac_ctrl_kind_name call at 0x81f84.

   ROUTE (C): the same as lib/A/ACtlG/F7.v, which this file Requires for its kn_* helpers (kn_shadow_vis,
   kn_rt_keep, kn_frac_keep, kn_core_keep, kn_jrnl).  The run is the route (C) twin lib/A/Prog/Seg/F8Fon.v
   f8_evt_F_on (this lane's beside-file; a Theorem Labs lane's F8F.v (not in this delivery) unchanged): callee premise
   reac_ctrl_kind_name_contract_F_on, no shadow_rw premise, the run SPANS the call.  This file supplies the premise
   with A.Prog.reac_ctrl_kind_nameF.reac_ctrl_kind_name_holds_F_on and lifts the WHOLE run once with
   Reusable.YA0nR.SRr_fevt_hid at RNG := A.ProgBridge.RNG_W (w_H W3).  No split; THIS STAGE CITES NO LIFT.

   DIFFERENCES FROM F7, and nothing else
   - the run's first premise is `bv_eqb a0 (Z_to_bv 64 0) = false`: a0 is the entry cut's own
     `rgv regs 10 (kind_name_addr (t_k (c_in cx) j))` (C_A81f7c_at) and every kind-name address is nonzero
     (Seg/F8.v f8_kn_addr_range, f8_eqb0_false);
   - the run reads no spill and no parse-record word, so its footprint is the callee's three ranges only;
   - the end map's ra is existential (the callee's return address is not pinned by the exit cut);
   - the exit cut C_A81f88_at carries ONE conjunct more than the entry: the bytes of the kind-name string at
     `kind_name_addr (t_k (c_in cx) j)`, which is the last clause of the callee's own post, so it comes straight
     out of the run.

   SECTION HYPOTHESES (the same two as F7, same text; both are ACtl.v's own): LAWS (ACtl.v:237) and TFIB_SYMS
   (ACtl.v:252).  KN_SHADOW_VIS is GONE (G7.kn_shadow_vis proves it; F7.v's header says how).

   SHADOWED NAMES: as in F7.v, every core module is bound to its full path by a Module alias, because the run
   file Requires the ASan-side lib/A/Reusable copies.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/F8.v   -- comments only.

   BUILD STATE: as lib/A/ACtlG/F7.v's header records (type-check on a working branch 1899bed1aee, no stand-in in the
   closure).  Every step is proved: no unproved step and no assumed constant. *)

From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* Every project module by its EXACT prefix (twins of several of these exist under lib/A/Reusable, lib/A/Bz/Lib,
   lib/B/... and lib/AZ/Lib). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YK04 YA0n YA0nR YG0f YG00 YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0d YG0n YC5d YCbq YM05 YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v ACfn AE2k AF0m Img0 AsanRT ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlCut ACtlCutP ProgBridge ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_kind_name_c reac_ctrl_kind_nameF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F8Fon F8 F7.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit F7.
Import ListNotations.
Local Open Scope Z_scope.

Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module CG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module CG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module CG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module CG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module CG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module CA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module CA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module CC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Module CCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module MEM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module FRM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module R6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module KNA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_kind_name_c.
Module KNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_kind_nameF.
Module SegF8 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F8.
Module SegF8Fon := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F8Fon.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
(* the kn_* helpers, proved once in lib/A/ACtlG/F7.v and shared by the two kind-name stages *)
Module G7 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.F7.

Local Notation segs := A.AB1v.tfibsegs.

Section GlueF8.

(* ACtl.v's Section shape (ACtl.v:210-214 at blob c4edf0be7fe), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : CG0f.asyms.
Variable MT : CC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:373, :377-378, :434-435), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81f7c_at := (ACtlCutP.C_A81f7c_at B).
Local Notation C_A81f88_at := (ACtlCutP.C_A81f88_at B).

(* --- Section hypotheses: the same two as lib/A/ACtlG/F7.v, with the same text and the same reasons. --- *)

(* ACtl.v:237, exact text. *)
Hypothesis LAWS : CG0d.AR_laws segs B.
(* ACtl.v:252, exact text: the bundle's own symbols (G7.kn_shadow_vis reads its ts_zsh). *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

Lemma glue_seg_F8 : forall POST (j : nat),
  CF POST (ix_cut C_A81f88_at [Z.of_nat j]) -> CF POST (ix_cut C_A81f7c_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 Hbase HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j]. *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81f7c_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HPerm & Hcn26 & Hj255 & HHB & HFLSI & HLK & HbC & HbK & H10 & HIDj & HF17 &
    HW240 & HPF).
  (* route (C): the cut carries ctl_rt_C B ly3 S3 mem3; this stage reads its asan cells and ro_agree only. *)
  pose proof Hrt as (HRTc & _ & _ & HRTr).
  (* G2: the visible-state bounds (the same chain as F7). *)
  pose proof HJ as HJ0.
  destruct HJ0 as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & _).
  destruct Hstatic as (_ & _ & Hceil & Hstklo & Hsphi & Hhi47 & _ & _ & _).
  pose proof CCbq.asan_consts as (Hac & _ & _ & _ & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (CG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (CCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & _).
  assert (Efr : fr = CG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Efr3 : CG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold CG0f.frame_addr. rewrite EF. reflexivity. }
  rewrite Efr3 in Hf4096, Hfceil.
  change (CG00.fs_frame_bytes 6) with 4096 in Hfceil.
  assert (Hphiin : In (phi, ACtlCutP.flen cx j) (CG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  destruct (CG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hphiin)
    as (_ & Hphi4096 & Hphiceil & _ & _ & _ & Hflen0).
  pose proof (CCbq.req_size_pos (ACtlCutP.flen cx j) (proj1 Hflen0)) as (Hrq1 & Hrq2).
  pose proof Hbase as Hbase0.
  destruct Hbase0 as (Hpre & _).
  destruct Hpre as (_ & _ & _ & _ & Hpcase & Hnlen & _).
  assert (Hcpceil : ACtlCut.c_p cx + ACtlCut.c_n cx <= CM05.alloc_ceiling).
  { destruct Hpcase as [(Hn0 & Hp0) | (Hn & Hinb)].
    - rewrite Hn0, Hp0. unfold A.ACfn.A_EMPTY. lia.
    - assert (Hinb3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (CG0d.ablocks B ly3 S3)).
      { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. exact Hinb. }
      destruct (CG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 (ACtlCut.c_p cx) (ACtlCut.c_n cx) HAR Hinb3)
        as (_ & _ & Hpc & _).
      pose proof (CCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as (_ & Hq2). lia. }
  pose proof HFRAC as HFRAC0.
  destruct HFRAC0 as (A & sp & Hsp & Hsp16 & Hspz & H4r & H8r & H9r & H3r & H19r & H26r &
    Hfr32 & HA32 & HAS & HspA & HfrA & HA416 & Hsp4096 & HSapp & _).
  assert (HSappN : ACtlCut.c_sp cx <= 140737488355328).
  { unfold ART.APPMEM_END in HSapp. exact HSapp. }
  assert (Hspnn : 0 <= sp).
  { rewrite <- Hspz. unfold CG0d.spZ. pose proof (bv_unsigned_in_range 64 (CK11.getr regs3 2)) as Hr. lia. }
  assert (Hsp47 : sp <= 140737488355328) by lia.
  assert (Hceilsp : CM05.alloc_ceiling + 4096 <= sp - 16).
  { unfold A.ACfn.LLVMF_STK in *. lia. }
  assert (Hspbig : 140735332483072 + 4096 <= sp - 16) by lia.
  assert (HAnn : 0 <= A < 2 ^ 64).
  { split; [lia|]. change (2 ^ 64) with 18446744073709551616. lia. }
  assert (HA416' : A + 416 < 2 ^ 64)
    by (change (2 ^ 64) with 18446744073709551616; lia).
  assert (Hlo : CG0f.kLowMemEnd <= sp - 16) by (unfold CG0f.kLowMemEnd; lia).
  assert (Hhmlo : ART.HIGHMEM_BEG + 4096 <= sp - 16) by (unfold ART.HIGHMEM_BEG; lia).
  assert (Hlo47 : sp - 16 <= 2 ^ 47) by (change (2 ^ 47) with 140737488355328; lia).
  assert (Hfrlo : fr + ACtlCutP.FRAME_BYTES <= sp - 16) by (unfold ACtlCutP.FRAME_BYTES; lia).
  (* the whole class-6 frame slot [fr, fr + 4096) is below the window (what kn_frac_keep needs) *)
  assert (Hslotlo : fr + 4096 <= sp - 16) by lia.
  assert (Hphilo : phi + A.ACtlK.a_size (ACtlCutP.flen cx j) <= sp - 16).
  { unfold A.ACtlK.a_size, CG00.req_size in *.
    destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  assert (Hcplo : ACtlCut.c_p cx + ACtlCut.c_n cx <= sp - 16) by lia.
  assert (Hknlo : KNA.KIND_NAME + 112 <= sp - 16) by (unfold KNA.KIND_NAME; lia).
  assert (Hhisp2 : sp <= CG0d.spZ regs3) by (rewrite Hspz; lia).
  assert (Hinlen : Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx) by (symmetry; exact Hnlen).
  (* the run's register and memory premises (the cut's own bundles stay intact for kn_core_keep) *)
  pose proof HbK as HbK0.
  destruct HbK0 as (K20 & K22 & K24 & K25 & K280 & KU32 & KR).
  pose proof HbC as HbC0.
  destruct HbC0 as (C23 & C18 & (A1 & H9a & HA1 & HSP & Q232) & HPH & HFR & HKN & HFGj & HFSj).
  destruct HKN as (HKNB & HKNA).
  assert (Hv : 0 <= SM.t_k (ACtlCut.c_in cx) j < 2 ^ 64).
  { pose proof (Prog.RcParse.ctrlparse_kind_range (SM.t_len (ACtlCut.c_in cx) j)
                  (SM.t_g (ACtlCut.c_in cx) j)) as Hk13.
    unfold SM.t_k. change (2 ^ 64) with 18446744073709551616. lia. }
  assert (Ha0 : bv_eqb (CK11.getr regs3 10) (Z_to_bv 64 0) = false).
  { replace (CK11.getr regs3 10) with (Z_to_bv 64 (KNA.kind_name_addr (SM.t_k (ACtlCut.c_in cx) j)))
      by (symmetry; exact H10).
    apply SegF8.f8_eqb0_false. apply SegF8.f8_kn_addr_range. }
  assert (HSTK0 : FRM.stk segs mem3 (sp - 16) sp).
  { split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|].
    intros a Ha.
    destruct (Hpres a ltac:(unfold A.ACfn.LLVMF_STK in *; lia)) as (HHa & b & Hbb).
    assert (Ea : MEM.wa a = Z_to_bv 64 a) by reflexivity.
    split.
    - rewrite Ea. unfold wview. rewrite Hbb. intros HC; discriminate HC.
    - exists b. unfold MEM.mrd. rewrite Ea, Hbb. reflexivity. }
  (* the three footprint ranges are visible *)
  assert (Hwin : forall a, sp - 16 <= a < sp -> CA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha. destruct (Hpres a ltac:(unfold A.ACfn.LLVMF_STK in *; lia)) as (HHa & _). exact HHa. }
  assert (Vimg : PB.range_visible (CA0n.w_H W3) 0x10000 0x5ee000).
  { pose proof (PB.img_vis_W W3) as Hv0.
    unfold PB.range_visible, A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI in Hv0 |- *.
    destruct Hv0 as (V1 & V2 & V3). split; [lia|]. split; [lia|]. intros a Ha. apply V3. lia. }
  assert (Vstk : PB.range_visible (CA0n.w_H W3) (sp - KNA.REAC_CTRL_KIND_NAME_FRAME)
                   KNA.REAC_CTRL_KIND_NAME_FRAME).
  { unfold KNA.REAC_CTRL_KIND_NAME_FRAME.
    split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|].
    intros a Ha. apply Hwin. lia. }
  assert (Vsh : PB.range_visible (CA0n.w_H W3) (ART.shadow_addr KNA.KIND_NAME) 14)
    by exact (G7.kn_shadow_vis B TFIB_SYMS LAWS ly3 S3 W3 mem3 md3 HAR).
  (* the footprint run (the route (C) twin), with the callee's closed _on contract supplied *)
  pose proof (SegF8Fon.f8_evt_F_on KNF.reac_ctrl_kind_name_holds_F_on
                (PB.RNG_W (CA0n.w_H W3))
                (CK11.getr regs3 1) (CK11.getr regs3 2) (CK11.getr regs3 3) (CK11.getr regs3 4)
                (CK11.getr regs3 5) (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8)
                (CK11.getr regs3 9) (CK11.getr regs3 10) (CK11.getr regs3 11) (CK11.getr regs3 12)
                (CK11.getr regs3 13) (CK11.getr regs3 14) (CK11.getr regs3 15) (CK11.getr regs3 16)
                (CK11.getr regs3 17) (CK11.getr regs3 18) (CK11.getr regs3 19) (CK11.getr regs3 20)
                (CK11.getr regs3 21) (CK11.getr regs3 22) (CK11.getr regs3 23) (CK11.getr regs3 24)
                (CK11.getr regs3 25) (CK11.getr regs3 26) (CK11.getr regs3 27) (CK11.getr regs3 28)
                (CK11.getr regs3 29) (CK11.getr regs3 30) (CK11.getr regs3 31)
                CK11.fp_regs CK11.fp_csr mem3
                (SM.t_k (ACtlCut.c_in cx) j) (sp - 16)) as HRUN.
  assert (Hspv : bv_unsigned (CK11.getr regs3 2) = sp) by (rewrite <- Hspz; reflexivity).
  rewrite Hspv in HRUN.
  specialize (HRUN Ha0 K24 Hv HKNB
                (A.Prog.Seg.F8.f8_kn_strings_ro mem3 HRTr) HSTK0
                ltac:(unfold KNA.REAC_CTRL_KIND_NAME_FRAME; lia)
                ltac:(unfold KNA.REAC_CTRL_KIND_NAME_FRAME, KNA.KIND_NAME, CG0f.kLowMemEnd in *; lia)
                HRTc HKNA).
  specialize (HRUN ltac:(intros x Hx; cbn [FRM.outside]; split; [|exact I];
                unfold ART.GOT_CELL_K, ART.CELL_K, ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END,
                  ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG, KNA.REAC_CTRL_KIND_NAME_FRAME in *; lia)).
  specialize (HRUN (PB.rng_of_visible _ _ _ Vimg) (PB.rng_of_visible _ _ _ Vstk)
                (PB.rng_of_visible _ _ _ Vsh)).
  (* G3: the cut's configuration in the run's state form, then the register move. *)
  rewrite PB.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81f7c_at [Z.of_nat j])) with 0x81f7c.
  apply (CA0nR.SRr_xregs_eqv segs W3 (R6.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81f7c) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (R6.xregs_eqv_sym _ _ (R6.mkR_of_eqv regs3))].
  rewrite (G7.kn_mkR_of regs3).
  (* G4: the lift. *)
  pose proof (PB.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- PB.tfibsegs_rsegs in HFS.
  apply (CA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (PB.RNG_W (CA0n.w_H W3)) _ (POST cx) HFS).
  { exact (PB.fp_avoids_RNG_W (CA0n.w_H W3)). }
  (* G5: the continuation. *)
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (ra' & a1' & a2' & mem' & Ems & MU & WM & MI & ST' & HKNS).
  subst ms'.
  cbn [ms_mem] in Hhid.
  set (R1 := FRM.mkR ra' (CK11.getr regs3 2) (CK11.getr regs3 3) (CK11.getr regs3 4)
         (CK11.getr regs3 5) (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8)
         (CK11.getr regs3 9) (Z_to_bv 64 (KNA.kind_name_addr (SM.t_k (ACtlCut.c_in cx) j))) a1' a2'
         (CK11.getr regs3 13) (CK11.getr regs3 14) (CK11.getr regs3 15) (CK11.getr regs3 16)
         (CK11.getr regs3 17) (CK11.getr regs3 18) (CK11.getr regs3 19) (CK11.getr regs3 20)
         (CK11.getr regs3 21) (CK11.getr regs3 22) (CK11.getr regs3 23) (CK11.getr regs3 24)
         (CK11.getr regs3 25) (CK11.getr regs3 26) (CK11.getr regs3 27) (CK11.getr regs3 28)
         (CK11.getr regs3 29) (CK11.getr regs3 30) (CK11.getr regs3 31)) in *.
  change (CA0n.SRr segs W3
            (CG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81f88_at [Z.of_nat j])) R1 mem' md') (POST cx)).
  unfold KNA.REAC_CTRL_KIND_NAME_FRAME in MU, ST'.
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 R1 mem' md' Hbase).
  - (* the journal across the callee's window write *)
    exact (G7.kn_jrnl B cx [] (ACtlCut.cut_own (ix_cut C_A81f7c_at [Z.of_nat j]) cx) ly3 S3 W3 mem3 mem'
             md3 md' k sp LAWS A.ACtlG.Kit.kit_segs_low HJ MU WM Hhid Hsbm
             ltac:(unfold A.ACfn.LLVMF_STK in *; lia) ltac:(lia) Hlo).
  - exact HF.
  - exact HL.
  - exact Hk.
  - (* the exit body *)
    split; [reflexivity|].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81f88_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    split.
    { exact (G7.kn_frac_keep B cx fr fr (sp - 16) sp regs3 R1 mem3 mem' HFRAC
               eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl MU Hslotlo Hhmlo Hhisp2). }
    unfold ACtlCutP.b5_body.
    exists phi.
    split; [exact HPerm|].
    split; [exact Hcn26|].
    split; [exact Hj255|].
    assert (Hcore := G7.kn_core_keep cx j phi fr (sp - 16) sp A regs3 R1 mem3 mem'
      (conj HHB (conj HFLSI (conj HLK (conj HbC (conj HbK
        (conj HIDj (conj HF17 (conj HW240 HPF))))))))
      H9r HAnn HA416' eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      MU WM Hhmlo Hlo47 HspA Hfrlo Hphilo Hcplo Hinlen Hknlo).
    destruct Hcore as (HHB' & HFLSI' & HLK' & HbC' & HbK' & HIDj' & HF17' & HW240' & HPF').
    split; [exact HHB'|].
    split; [exact HFLSI'|].
    split; [exact HLK'|].
    split; [exact HbC'|].
    split; [exact HbK'|].
    split; [reflexivity|].
    split; [exact HKNS|].
    split; [exact HIDj'|].
    split; [exact HF17'|].
    split; [exact HW240' | exact HPF'].
  - (* ctl_rt_C on the new memory, at the same state ly3 S3 *)
    exact (G7.kn_rt_keep B ly3 S3 mem3 mem' (sp - 16) sp A.ACtlG.Kit.kit_segs_low MU WM Hhmlo Hrt).
Qed.

End GlueF8.
