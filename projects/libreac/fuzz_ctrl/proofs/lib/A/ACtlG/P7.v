(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module paths, module names and numbers changed; 884 of its 966 lines of code are new or changed and 1993 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F13.v, with its module names changed; 186 of its 206 lines of code are new or changed and 946 lines of the source are left out. *)
(* lib/A/ACtlG/P7.v -- GLUE for stage seg_P7 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:725).
   Written by a Theorem Labs lane's glue lane (piece W3, second part); single writer.  rule 24: no function proved
   (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_P7 : forall POST, CF POST C_A81c20 -> CF POST C_A81bf8
   with ACtl.v's own CF notation, exactly ACtl.v's Section hypothesis seg_P7.  Segment P7 is 0x81bf8 -> 0x81c20
   (Seg/P7.v): li s2,-1; beq a0,s2 (taken); ld a0,192(s1) (= fragb fr); li a1,0; li a2,0; mv a3,s7; mv a4,s8;
   mv a5,s4; jal reac_ctrl_identity_fragment.  With fr = len = 0 the callee refuses (returns -1) and writes only its
   frame window [sp - 4656, sp).

   THE RUN.  The route (C) twin A.Prog.Seg.P7F_on.p7_evt_F_on (Seg/P7F_on.v, written by a Theorem Labs lane under
   a Theorem Labs lane's consent 12:55Z) of a Theorem Labs lane's v1.9 re-run Seg/P7F.p7_evt_F (its source is not in this delivery), Required.  It drops the universal
   `shadow_rw m` premise: the run reads no shadow byte, and the callee's narrowed shadow region is empty at fr = 0.
   Its callee premise reac_ctrl_identity_fragment_contract_F_on is discharged by the PROVED CLOSED
   A.Prog.reac_ctrl_identity_fragment_F_on.reac_ctrl_identity_fragment_F_holds_on_closed (a Theorem Labs lane, the memcpy
   and bcmp _on contracts closed inside it); the segment is lifted whole (split rule 04:01Z, corrected 04:30Z).

   THE PROOF: the steps of lib/A/ACtlG/P8.v (G1-G5) with that file's W3 lemmas.  What differs: the run reads the
   runtime cells REAL_BCMP, REAL_MEMCMP, GOT_CF, CF + 254, CF + 255 (the bcmp wrapper's, through the callee's
   contract); they come from a Theorem Labs lane's PROVED A.ProgWorldRtC.RT_used_of_AR_C at the journal's AR (its REAL_USED
   slots and asan_cf_cells), and ro_agree / asan_cells from the carried A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (route
   (C)).  The exit keeps the state's regions across the munch (P8.w3_ctlrtC_munch).

   SECTION HYPOTHESES (exact text below; both are ACtl.v's Section hypotheses, same name and text)
   - LAWS (ACtl.v:237), TFIB_SYMS (ACtl.v:252, the core's symbol facts CtrlTSyms B);
   - the memory helpers are cited by name from a Theorem Labs lane's shared lib/A/ACtlG/KitMem.v (a working branch 4a56e997c0f, merged).

   CLOSURE and SHADOWED NAMES: as lib/A/ACtlG/P8.v. *)

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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.AF0m A.Img0 A.AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlRtC A.ProgWorldRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.bcmp_wrap_c A.Prog.memcmp_c A.Prog.rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ctrl_identity_fragment_F_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.P7F_on.
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

Section GlueP7.

Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81bf8 := (A.ACtlCutP.C_A81bf8 B).
Local Notation C_A81c20 := (A.ACtlCutP.C_A81c20 B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses. *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
(* ACtl.v:252: the core's symbol facts for B. *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_P7 : forall POST, CF POST C_A81c20 -> CF POST C_A81bf8.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_A81bf8 (ACtlCutP.v:1863-1874). *)
  cbv beta iota zeta delta [ACtlCut.cut_body A.ACtlCutP.C_A81bf8] in Hbody.
  destruct Hbody as (HP & HFRAC & Hn & HOUR & HCUR & HPRO & S144 & A2691 & S192 & Afrag & A2688 & HIDB & HFGB &
    R10 & _ & HXC & A2880).
  (* G2: the bounds from visible state. *)
  destruct (A.ACtlG.P8.w3_bounds B MT XM_LIB RLO RHI LAWS cx fr k ly3 S3 W3 mem3 md3 HB HJ HF HL HP)
    as (Efr3 & Hfr4096 & Hfrceil & Hframe & Hfsh & Hceilstk & Hsp47 & Hinput).
  pose proof HFRAC as (A & sp & F2 & Fal & FspZ & _ & _ & F9 & _ & _ & _ & _ & _ & FAc & FspA & _ & FA416 &
    Fsplo & Fapp & _).
  pose proof (@CM05.alloc_ceiling_value rc) as [[Hac0 Hac1] _].
  assert (Esp : bv_unsigned (CK11.getr regs3 2) = sp) by exact FspZ.
  assert (Hsp0 : 0 <= sp).
  { rewrite <- Esp. pose proof (bv_unsigned_in_range 64 (CK11.getr regs3 2)) as Rg.
    change (bv_modulus 64) with (2 ^ 64) in Rg. lia. }
  assert (HAb : 0 <= A /\ A + 400 <= 2 ^ 64) by (unfold A.AsanRT.APPMEM_END in Fapp; lia).
  (* the fragment pointer: the spill [s1 + 192] = fragb fr, read through register 9 = A *)
  pose proof S192 as (A1 & HA1 & Hq192).
  assert (EA1 : A1 = A).
  { assert (E0 : Z_to_bv 64 A = Z_to_bv 64 A1) by exact (eq_trans (eq_sym F9) HA1).
    pose proof (f_equal bv_unsigned E0) as E1. rewrite !LMState.unsigned_lit_wrap in E1.
    unfold A.ACtlCutP.q64 in Hq192.
    pose proof (LMem.bytes_at_bound _ _ _ _ Hq192) as Hb.
    assert (El : length (LMem.le8 (Z_to_bv 64 (A.ACtlCutP.fragb fr))) = 8%nat) by reflexivity.
    rewrite El in Hb. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hb.
    rewrite (Z.mod_small A) in E1 by lia. Z.div_mod_to_equations. lia. }
  subst A1.
  (* the runtime cells the run reads (through the callee's bcmp wrapper): RT_used_C at the journal's AR *)
  pose proof HJ as (HAR & _).
  pose proof (A.ProgWorldRtC.RT_used_of_AR_C B TFIB_SYMS LAWS ly3 S3 W3 mem3 md3 HAR)
    as (_ & _ & _ & _ & Hcf & _ & _ & Hreal).
  destruct Hcf as (Hgotcf & _ & _ & _ & _ & _ & H240 & _).
  pose proof (proj1 (Forall_forall _ _) Hreal (0xa17f0, 0x97b0c)
    ltac:(unfold A.AsanRT.RT_REALS; cbn [In]; right; right; left; reflexivity)
    ltac:(unfold A.ProgWorld.REAL_USED; cbn [In fst]; left; reflexivity)) as HRB.
  pose proof (proj1 (Forall_forall _ _) Hreal (0xa17e8, 0x97bdc)
    ltac:(unfold A.AsanRT.RT_REALS; cbn [In]; do 9 right; left; reflexivity)
    ltac:(unfold A.ProgWorld.REAL_USED; cbn [In fst]; right; left; reflexivity)) as HRM.
  assert (H240' : LMem.bytes_at A.Img0.rsegs mem3 (A.AsanRT.RT_CF + 240)
                    (A.AsanRT.cf_b [0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1] ++ [Z_to_bv 8 1] ++
                     [Z_to_bv 8 1] ++ A.AsanRT.cf_b [1; 1; 1; 1; 0]))
    by exact H240.
  apply LMem.bytes_at_app in H240' as [_ H240'].
  apply LMem.bytes_at_app in H240' as [H254 H240'].
  apply LMem.bytes_at_app in H240' as [H255 _].
  (* the window [sp - 4656, sp) and the spill cell [A + 192, A + 200) *)
  assert (Hstk : LFrame.stk A.Img0.rsegs mem3 (sp - 4656) sp).
  { apply (A.ACtlG.KitMem.kitmem_stk_of_journal B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] _ _ _ _ _ _ _ _ _ mem3 md3 k (sp - 4656) sp HJ);
      unfold A.ACfn.LLVMF_STK in *; lia. }
  pose proof (A.ProgWorldVisWin.win_vis B) as WV.
  unfold A.ProgWorld.win_vis_stmt in WV.
  assert (Hvis : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (sp - 4656) 4656).
  { apply (WV A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] _ _ _ _ _ _ _ _ _ mem3 md3 k (sp - 4656) 4656 HJ);
      unfold A.ACfn.LLVMF_STK in *; lia. }
  assert (Hvis192 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (A + 192) 8).
  { apply (WV A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] _ _ _ _ _ _ _ _ _ mem3 md3 k (A + 192) 8 HJ);
      unfold A.ACfn.LLVMF_STK in *; lia. }
  (* the 8-aligned shadow word span of the window (ProgWorldVisWin.win_sh_vis at the journal's AR; the stack
     bounds of ly3 are the entry layout's, layout_le, and astk_ok places the window inside them) *)
  assert (Hshv : 4656 = 0 \/ A.ProgBridge.range_visible (Reusable.YA0n.w_H W3)
                   (A.Prog.rng_asan.sh_al8_lo (sp - 4656))
                   (A.Prog.rng_asan.sh_al8_hi (sp - 4656) 4656 - A.Prog.rng_asan.sh_al8_lo (sp - 4656))).
  { pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
    destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
    destruct Hstk0 as (_ & _ & Hlo0 & Hlosp0 & Hsphi0 & _).
    pose proof (A.ProgWorldVisWin.win_sh_vis B) as WS. unfold A.ProgWorld.win_sh_vis_stmt in WS.
    apply (WS LAWS ly3 S3 W3 mem3 md3 (sp - 4656) 4656 HAR);
      [rewrite Elo | rewrite Ehi | ]; unfold A.ACfn.LLVMF_STK in *; lia. }
  (* G3 *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A81bf8) with 0x81bf8.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRegs.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81bf8) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRegs.xregs_eqv_sym _ _ (LRegs.mkR_of_eqv regs3))].
  (* G4 *)
  pose proof Hrt as (Hcells & _ & _ & Hroag).
  pose proof (A.Prog.Seg.P7F_on.p7_evt_F_on
    A.Prog.reac_ctrl_identity_fragment_F_on.reac_ctrl_identity_fragment_F_holds_on_closed
    (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
    (CK11.getr regs3 1) (CK11.getr regs3 2) (CK11.getr regs3 3) (CK11.getr regs3 4) (CK11.getr regs3 5)
    (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8) (CK11.getr regs3 9) (CK11.getr regs3 10)
    (CK11.getr regs3 11) (CK11.getr regs3 12) (CK11.getr regs3 13) (CK11.getr regs3 14) (CK11.getr regs3 15)
    (CK11.getr regs3 16) (CK11.getr regs3 17) (CK11.getr regs3 18) (CK11.getr regs3 19) (CK11.getr regs3 20)
    (CK11.getr regs3 21) (CK11.getr regs3 22) (CK11.getr regs3 23) (CK11.getr regs3 24) (CK11.getr regs3 25)
    (CK11.getr regs3 26) (CK11.getr regs3 27) (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30)
    (CK11.getr regs3 31)
    CK11.fp_regs CK11.fp_csr mem3 A (A.ACtlCutP.fragb fr) F9 R10
    ltac:(unfold A.ACtlCutP.fragb; lia) Hq192
    ltac:(rewrite Esp; exact Fal)
    ltac:(rewrite Esp; unfold A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K; exact Hstk)
    Hroag Hcells
    ltac:(rewrite Esp; unfold A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K,
            A.AsanRT.HIGHMEM_BEG, A.ACfn.LLVMF_STK in *; lia)
    ltac:(rewrite Esp; unfold A.AsanRT.APPMEM_END in *; lia)
    HRB HRM Hgotcf H254 H255
    (A.ProgBridge.rng_of_visible _ _ _ Hvis192)
    (A.ProgBridge.rng_bytes_RNG_W _)
    (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3))
    ltac:(rewrite Esp; unfold A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K;
          exact (A.ProgBridge.rng_of_visible _ _ _ Hvis))
    ltac:(rewrite Esp; unfold A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K;
          destruct Hshv as [E0 | Hv]; [left; exact E0 | right; exact (A.ProgBridge.rng_of_visible _ _ _ Hv)])) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 _ _ (POST cx)
           (A.ACtlG.P8.w3_fevt_run _ _ _ _ HFS)).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  (* G5 *)
  intros ms' md' [Hrun HQ] Hsbm.
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s2' & m' &
    Ems & Es2 & HMU & HWM & HST').
  subst ms' s2'.
  rewrite Esp in HMU. unfold A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K in HMU.
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (LMState.MS ?R _ _ _ _ _ _) _) _ => set (RX := R) end.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81c20) RX m' md') (POST cx)).
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
  assert (Hlow : A.AsanRT.HIGHMEM_BEG <= sp - 4656)
    by (unfold A.AsanRT.HIGHMEM_BEG, A.ACfn.LLVMF_STK in *; lia).
  assert (Osp : forall x, Reusable.YG0d.spZ regs3 <= x -> LFrame.outside [(sp - 4656, sp)] x).
  { intros x Hx. rewrite FspZ in Hx. cbn [LFrame.outside]. split; [lia | exact I]. }
  assert (Osh : forall x, A.AsanRT.in_shadow x -> LFrame.outside [(sp - 4656, sp)] x).
  { intros x Hx. cbn [LFrame.outside]. split; [|exact I].
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG in Hx, Hlow. lia. }
  assert (Ofr : forall x, (fr <= x < fr + 2880) \/ (fr + 4088 <= x < fr + 4096) -> LFrame.outside [(sp - 4656, sp)] x).
  { intros x Hx. assert (Hx' : fr <= x < fr + 4096) by (destruct Hx; lia). cbn [LFrame.outside].
    split; [unfold A.ACfn.LLVMF_STK in *; lia | exact I]. }
  assert (Oin : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
                  LFrame.outside [(sp - 4656, sp)] x).
  { intros x Hx. destruct (Hinput x Hx) as [Hx1 _]. cbn [LFrame.outside].
    split; [unfold A.ACfn.LLVMF_STK in *; lia | exact I]. }
  refine (HX cx idx fr k ly3 S3 W3 RX m' md' HB _ HF HL Hk _ _).
  - (* the journal: ProgWorld.ajournal_of_fsteps, the window is awr_byte's stack case *)
    match type of Hrun with Reusable.YK04R.fsteps _ _ ?ms0 ?ms1 =>
      refine (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx _ _ _ _ _ _ _ _ _ _ _ _ ms0 ms1 _ _ _ _ _
                HJ Hrun (A.ProgBridge.fp_avoids_RNG_W _) HMU Hsbm _) end.
    intros a _ Hno. apply A.ACtlG.P8.w3_not_outside1 in Hno.
    unfold Reusable.YCbq.awr_byte. left. unfold A.ACfn.LLVMF_STK in *. lia.
  - (* the exit body C_A81c20 (ACtlCutP.v:1878-1889) *)
    cbv beta iota delta [ACtlCut.cut_body A.ACtlCutP.C_A81c20].
    destruct (A.ACtlG.P8.w3_core_keep B cx fr regs3 RX mem3 m' [(sp - 4656, sp)]
                (conj HFRAC (conj HOUR (conj HCUR (conj HPRO (conj S144 (conj A2691 (conj S192 (conj Afrag
                  (conj A2688 (conj HIDB (conj HFGB (conj HXC A2880))))))))))))
                K2 K3 K4 K8 K9 K19 K22 K25 K26 HMU (fun i Hi => proj1 (Hframe i Hi)) Osp Osh Ofr Oin)
      as (HFRAC' & HOUR' & HCUR' & HPRO' & S144' & A2691' & S192' & Afrag' & A2688' & HIDB' & HFGB' & HXC' &
          A2880').
    exact (conj HP (conj HFRAC' (conj Hn (conj HOUR' (conj HCUR' (conj HPRO' (conj S144' (conj A2691'
      (conj S192' (conj Afrag' (conj A2688' (conj HIDB' (conj HFGB' (conj K10 (conj K18 (conj HXC'
      A2880')))))))))))))))).
  - (* ctl_rt_C: the window is high application memory, no image byte; the state's regions are kept *)
    apply (A.ACtlG.P8.w3_ctlrtC_munch B ly3 S3 [(sp - 4656, sp)] mem3 m' Hrt HMU).
    intros x Hx. apply A.ACtlG.P8.w3_not_outside1 in Hx. split.
    + unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. right. lia.
    + intros Hi. pose proof (A.ACtlG.Kit.kit_segs_low x Hi) as Hl.
      unfold Reusable.YG0f.kLowMemEnd, A.AsanRT.HIGHMEM_BEG in *. lia.
Qed.

End GlueP7.

Print Assumptions glue_seg_P7.
