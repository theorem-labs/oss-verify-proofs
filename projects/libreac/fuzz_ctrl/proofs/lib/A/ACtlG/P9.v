(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module paths, module names and numbers changed; 884 of its 966 lines of code are new or changed and 1993 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F13.v; 128 of its 145 lines of code are new or changed and 949 lines of the source are left out. *)
(* lib/A/ACtlG/P9.v -- GLUE for stage seg_P9 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:729).
   Written by a Theorem Labs lane's glue lane (piece W3, second part); single writer.  rule 24: no function proved
   (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_P9 : forall POST, CF POST C_A81c4c -> CF POST C_A81c34
   with ACtl.v's own CF notation, exactly ACtl.v's Section hypothesis seg_P9.  Segment P9 is 0x81c34 -> 0x81c4c
   (Seg/P9.v): li s2,-1; beq a0,s2 (taken, a0 = -1); li a0,0; li a1,0; jal reac_ports_parse.  With p = q = 0 the
   callee fails and writes only its 16-byte frame [sp - 16, sp).

   THE RUN.  a Theorem Labs lane's v1.9 re-run A.Prog.Seg.P9F.p9_evt_F (Seg/P9F.v:39), Required.  Its callee premise
   reac_ports_parse_contract_F is discharged by the PROVED A.Prog.reac_ports_parseF.reac_ports_parse_F_holds; the
   segment is lifted whole (split rule 04:01Z, corrected 04:30Z).

   THE PROOF: the steps of lib/A/ACtlG/P8.v (G1-G5), with that file's W3 lemmas w3_bounds, w3_core_keep,
   w3_fevt_run, w3_not_outside1 and w3_ctlrtC_munch (Required qualified, not copied).  Route (C): the cut carries
   A.ACtlRtC.ctl_rt_C B ly3 S3 mem3; the run reads no shadow byte, and the exit keeps the state's regions across
   the munch (P8.w3_ctlrtC_munch).

   SECTION HYPOTHESIS: LAWS (ACtl.v:183).  The memory helpers are cited by name from
   a Theorem Labs lane's shared lib/A/ACtlG/KitMem.v (a working branch 4a56e997c0f, merged).

   CLOSURE and SHADOWED NAMES: as lib/A/ACtlG/P8.v (twin modules through fully qualified aliases). *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ports_parse_c A.Prog.reac_ports_parseF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.P9F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem A.ACtlG.P8.
Import ListNotations.
Local Open Scope Z_scope.

(* The twin-safe module names (fully qualified). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module CI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LMState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRegs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.

Local Notation segs := A.AB1v.tfibsegs.

Section GlueP9.

Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81c34 := (A.ACtlCutP.C_A81c34 B).
Local Notation C_A81c4c := (A.ACtlCutP.C_A81c4c B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (exact text of lib/A/ACtlG/P8.v). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_P9 : forall POST, CF POST C_A81c4c -> CF POST C_A81c34.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_A81c34 (ACtlCutP.v:1893-1904). *)
  cbv beta iota zeta delta [ACtlCut.cut_body A.ACtlCutP.C_A81c34] in Hbody.
  destruct Hbody as (HP & HFRAC & Hn & HOUR & HCUR & HPRO & S144 & A2691 & S192 & Afrag & A2688 & HIDB & HFGB &
    R10 & HXC & A2880).
  (* G2: the bounds from visible state. *)
  destruct (A.ACtlG.P8.w3_bounds B MT XM_LIB RLO RHI LAWS cx fr k ly3 S3 W3 mem3 md3 HB HJ HF HL HP)
    as (Efr3 & Hfr4096 & Hfrceil & Hframe & Hfsh & Hceilstk & Hsp47 & Hinput).
  pose proof HFRAC as (A & sp & F2 & _ & FspZ & _ & _ & _ & _ & _ & _ & _ & _ & FAc & FspA & _ & _ & Fsplo &
    Fapp & _).
  pose proof (@CM05.alloc_ceiling_value rc) as [[Hac0 _] _].
  assert (Esp : bv_unsigned (CK11.getr regs3 2) = sp) by exact FspZ.
  assert (Hstk : LFrame.stk A.Img0.rsegs mem3 (sp - 16) sp).
  { apply (A.ACtlG.KitMem.kitmem_stk_of_journal B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] _ _ _ _ _ _ _ _ _ mem3 md3 k (sp - 16) sp HJ);
      unfold A.ACfn.LLVMF_STK in *; lia. }
  assert (Hvis : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (sp - 16) 16).
  { pose proof (A.ProgWorldVisWin.win_vis B) as WV.
    unfold A.ProgWorld.win_vis_stmt in WV.
    apply (WV A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] _ _ _ _ _ _ _ _ _ mem3 md3 k (sp - 16) 16 HJ);
      unfold A.ACfn.LLVMF_STK in *; lia. }
  (* G3 *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A81c34) with 0x81c34.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRegs.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81c34) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRegs.xregs_eqv_sym _ _ (LRegs.mkR_of_eqv regs3))].
  (* G4 *)
  pose proof (A.Prog.Seg.P9F.p9_evt_F A.Prog.reac_ports_parseF.reac_ports_parse_F_holds
    (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
    (CK11.getr regs3 1) (CK11.getr regs3 2) (CK11.getr regs3 3) (CK11.getr regs3 4) (CK11.getr regs3 5) (CK11.getr regs3 6)
    (CK11.getr regs3 7) (CK11.getr regs3 8) (CK11.getr regs3 9) (CK11.getr regs3 10) (CK11.getr regs3 11) (CK11.getr regs3 12)
    (CK11.getr regs3 13) (CK11.getr regs3 14) (CK11.getr regs3 15) (CK11.getr regs3 16) (CK11.getr regs3 17)
    (CK11.getr regs3 18) (CK11.getr regs3 19) (CK11.getr regs3 20) (CK11.getr regs3 21) (CK11.getr regs3 22)
    (CK11.getr regs3 23) (CK11.getr regs3 24) (CK11.getr regs3 25) (CK11.getr regs3 26) (CK11.getr regs3 27)
    (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30) (CK11.getr regs3 31)
    CK11.fp_regs CK11.fp_csr mem3 (sp - 16) R10
    ltac:(rewrite Esp; exact Hstk)
    ltac:(rewrite Esp; unfold A.Prog.reac_ports_parse_c.REAC_PORTS_PARSE_FRAME; lia)
    ltac:(rewrite Esp; unfold A.Prog.reac_ports_parse_c.REAC_PORTS_PARSE_FRAME;
          exact (A.ProgBridge.rng_of_visible _ _ _ Hvis))) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 _ _ (POST cx)
           (A.ACtlG.P8.w3_fevt_run _ _ _ _ HFS)).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  (* G5 *)
  intros ms' md' [Hrun HQ] Hsbm.
  destruct HQ as (t0' & t1' & t2' & t3' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & m' & Ems & Es2 & HMU &
    HWM & HST').
  subst ms' s2'.
  rewrite Esp in HMU. unfold A.Prog.reac_ports_parse_c.REAC_PORTS_PARSE_FRAME in HMU.
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (LMState.MS ?R _ _ _ _ _ _) _) _ => set (RX := R) end.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81c4c) RX m' md') (POST cx)).
  assert (K2 : CK11.getr RX 2 = CK11.getr regs3 2) by reflexivity.
  assert (K3 : CK11.getr RX 3 = CK11.getr regs3 3) by reflexivity.
  assert (K4 : CK11.getr RX 4 = CK11.getr regs3 4) by reflexivity.
  assert (K8 : CK11.getr RX 8 = CK11.getr regs3 8) by reflexivity.
  assert (K9 : CK11.getr RX 9 = CK11.getr regs3 9) by reflexivity.
  assert (K19 : CK11.getr RX 19 = CK11.getr regs3 19) by reflexivity.
  assert (K22 : CK11.getr RX 22 = CK11.getr regs3 22) by reflexivity.
  assert (K25 : CK11.getr RX 25 = CK11.getr regs3 25) by reflexivity.
  assert (K26 : CK11.getr RX 26 = CK11.getr regs3 26) by reflexivity.
  assert (K10 : CK11.getr RX 10 = Z_to_bv 64 (-1)) by reflexivity.
  assert (K18 : CK11.getr RX 18 = Z_to_bv 64 (-1)) by reflexivity.
  assert (Hlow : A.AsanRT.HIGHMEM_BEG <= sp - 16)
    by (unfold A.AsanRT.HIGHMEM_BEG, A.ACfn.LLVMF_STK in *; lia).
  assert (Osp : forall x, Reusable.YG0d.spZ regs3 <= x -> LFrame.outside [(sp - 16, sp)] x).
  { intros x Hx. rewrite FspZ in Hx. cbn [LFrame.outside]. split; [lia | exact I]. }
  assert (Osh : forall x, A.AsanRT.in_shadow x -> LFrame.outside [(sp - 16, sp)] x).
  { intros x Hx. cbn [LFrame.outside]. split; [|exact I].
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG in Hx, Hlow. lia. }
  assert (Ofr : forall x, (fr <= x < fr + 2880) \/ (fr + 4088 <= x < fr + 4096) -> LFrame.outside [(sp - 16, sp)] x).
  { intros x Hx. assert (Hx' : fr <= x < fr + 4096) by (destruct Hx; lia). cbn [LFrame.outside].
    split; [unfold A.ACfn.LLVMF_STK in *; lia | exact I]. }
  assert (Oin : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
                  LFrame.outside [(sp - 16, sp)] x).
  { intros x Hx. destruct (Hinput x Hx) as [Hx1 _]. cbn [LFrame.outside].
    split; [unfold A.ACfn.LLVMF_STK in *; lia | exact I]. }
  refine (HX cx idx fr k ly3 S3 W3 RX m' md' HB _ HF HL Hk _ _).
  - (* the journal: ProgWorld.ajournal_of_fsteps, the window is awr_byte's stack case *)
    match type of Hrun with Reusable.YK04R.fsteps _ _ ?ms0 ?ms1 =>
      refine (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx _ _ _ _ _ _ _ _ _ _ _ _ ms0 ms1 _ _ _ _ _
                HJ Hrun (A.ProgBridge.fp_avoids_RNG_W _) HMU Hsbm _) end.
    intros a _ Hno. apply A.ACtlG.P8.w3_not_outside1 in Hno.
    unfold Reusable.YCbq.awr_byte. left. unfold A.ACfn.LLVMF_STK in *. lia.
  - (* the exit body C_A81c4c (ACtlCutP.v:1908-1919) *)
    cbv beta iota delta [ACtlCut.cut_body A.ACtlCutP.C_A81c4c].
    destruct (A.ACtlG.P8.w3_core_keep B cx fr regs3 RX mem3 m' [(sp - 16, sp)]
                (conj HFRAC (conj HOUR (conj HCUR (conj HPRO (conj S144 (conj A2691 (conj S192 (conj Afrag
                  (conj A2688 (conj HIDB (conj HFGB (conj HXC A2880))))))))))))
                K2 K3 K4 K8 K9 K19 K22 K25 K26 HMU (fun i Hi => proj1 (Hframe i Hi)) Osp Osh Ofr Oin)
      as (HFRAC' & HOUR' & HCUR' & HPRO' & S144' & A2691' & S192' & Afrag' & A2688' & HIDB' & HFGB' & HXC' &
          A2880').
    exact (conj HP (conj HFRAC' (conj Hn (conj HOUR' (conj HCUR' (conj HPRO' (conj S144' (conj A2691'
      (conj S192' (conj Afrag' (conj A2688' (conj HIDB' (conj HFGB' (conj K10 (conj K18 (conj HXC'
      A2880')))))))))))))))).
  - (* ctl_rt_C: the window is high application memory, no image byte; the state's regions are kept *)
    apply (A.ACtlG.P8.w3_ctlrtC_munch B ly3 S3 [(sp - 16, sp)] mem3 m' Hrt HMU).
    intros x Hx. apply A.ACtlG.P8.w3_not_outside1 in Hx. split.
    + unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. right. lia.
    + intros Hi. pose proof (A.ACtlG.Kit.kit_segs_low x Hi) as Hl.
      unfold Reusable.YG0f.kLowMemEnd, A.AsanRT.HIGHMEM_BEG in *. lia.
Qed.

End GlueP9.

Print Assumptions glue_seg_P9.
