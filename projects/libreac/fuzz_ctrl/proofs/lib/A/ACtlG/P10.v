(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module paths, module names and numbers changed; 884 of its 966 lines of code are new or changed and 1993 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F13.v; 198 of its 220 lines of code are new or changed and 944 lines of the source are left out. *)
(* lib/A/ACtlG/P10.v -- GLUE for stage seg_P10 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:731).  Written by a Theorem Labs lane's glue lane (piece W3, second part); single writer.
   rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_P10 : forall POST, CF POST C_A81c60 -> CF POST C_A81c4c
   with ACtl.v's own CF notation, exactly ACtl.v's Section hypothesis seg_P10.  Segment P10 is 0x81c4c -> 0x81c60
   (Seg/P10.v, v1.9 CHANGED): beq a0,s2 (taken, a0 = s2 = -1); li a0,0; ld a1,280(s1) (= code = fr + 3040);
   jal reac_ports_unknown.  With p = 0 the callee clears the output byte code and writes its 16-byte frame:
   write list [(sp - 16, sp); (c, c + 1)].

   THE RUN.  The route (C) twin A.Prog.Seg.P10F_on.p10_evt_F_on (Seg/P10F_on.v, written by a Theorem Labs lane under
   a Theorem Labs lane's consent 12:55Z) of a Theorem Labs lane's v1.9 re-run Seg/P10F.p10_evt_F (not in this delivery), Required.  It drops the universal
   `shadow_rw m` premise (the run and its callee read no shadow byte through it).  Its callee premise
   reac_ports_unknown_contract_F_on is discharged by the PROVED
   A.Prog.reac_ports_unknownF.reac_ports_unknown_F_holds_on (a Theorem Labs lane 4038362e590); the segment is lifted whole.

   THE PROOF: the steps of lib/A/ACtlG/P8.v (G1-G5) with that file's W3 lemmas.  What differs: the run writes one
   byte of the owned class-6 frame, c = fr + 3040 (XC's spill [s1 + 280]); it is present and visible
   (AR_frames_law, through P8.w3_bounds), not an image byte (AR_client_img_law, same), its shadow byte visible
   (AR_frames_law's shadow clause, c's shadow is the frame shadow + 380), apart from the input block (AR_sep_law,
   through w3_bounds), and the journal admits it as awr_byte's in_frames case.  The two runtime cells GOT_CELL_K /
   CELL_K are image bytes (p10_in_img, from ProgBridge.rsegs_spans), so the frame byte is not one of them.
   Route (C): the cut carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3; the run takes only its asan_cells conjunct, and the
   exit keeps the state's regions across the munch (P8.w3_ctlrtC_munch: both written ranges are application memory
   off the image).

   SECTION HYPOTHESIS: LAWS (ACtl.v:183).  The memory helpers are cited by name from
   a Theorem Labs lane's shared lib/A/ACtlG/KitMem.v (a working branch 4a56e997c0f, merged).

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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ports_unknown_c A.Prog.reac_ports_unknownF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.P10F_on.
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

(* Every address of the loaded image hull [0x10000, 0x5fe000) is an image byte: the four segments of rsegs tile it
   (ProgBridge.rsegs_spans). *)
Lemma p10_in_img : forall x, 0x10000 <= x < 0x5fe000 -> Reusable.YG0d.in_img segs x.
Proof.
  intros x Hx.
  assert (Hm : forall b sz, In (b, sz) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) A.Img0.rsegs) ->
                 b <= x < b + sz -> Reusable.YG0d.in_img segs x).
  { intros b sz Hin Hr. apply in_map_iff in Hin as (s & Es & Hs). injection Es as Eb Esz. subst b sz.
    exists s. split; [exact Hs | exact Hr]. }
  rewrite A.ProgBridge.rsegs_spans in Hm.
  destruct (Z_lt_le_dec x 0x30000) as [h1 | h1].
  { apply (Hm 0x10000 0x20000); [left; reflexivity | lia]. }
  destruct (Z_lt_le_dec x 0x9e000) as [h2 | h2].
  { apply (Hm 0x30000 0x6e000); [right; left; reflexivity | lia]. }
  destruct (Z_lt_le_dec x 0xa1000) as [h3 | h3].
  { apply (Hm 0x9e000 0x3000); [right; right; left; reflexivity | lia]. }
  apply (Hm 0xa1000 0x55d000); [right; right; right; left; reflexivity | lia].
Qed.

Section GlueP10.

Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81c4c := (A.ACtlCutP.C_A81c4c B).
Local Notation C_A81c60 := (A.ACtlCutP.C_A81c60 B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (exact text of lib/A/ACtlG/P8.v). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_P10 : forall POST, CF POST C_A81c60 -> CF POST C_A81c4c.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_A81c4c (ACtlCutP.v:1908-1919). *)
  cbv beta iota zeta delta [ACtlCut.cut_body A.ACtlCutP.C_A81c4c] in Hbody.
  destruct Hbody as (HP & HFRAC & Hn & HOUR & HCUR & HPRO & S144 & A2691 & S192 & Afrag & A2688 & HIDB & HFGB &
    R10 & R18 & HXC & A2880).
  (* G2: the bounds from visible state. *)
  destruct (A.ACtlG.P8.w3_bounds B MT XM_LIB RLO RHI LAWS cx fr k ly3 S3 W3 mem3 md3 HB HJ HF HL HP)
    as (Efr3 & Hfr4096 & Hfrceil & Hframe & Hfsh & Hceilstk & Hsp47 & Hinput).
  pose proof HFRAC as (A & sp & F2 & _ & FspZ & _ & _ & F9 & _ & _ & _ & _ & _ & FAc & FspA & _ & FA416 & Fsplo &
    Fapp & _).
  pose proof (@CM05.alloc_ceiling_value rc) as [[Hac0 Hac1] _].
  assert (Esp : bv_unsigned (CK11.getr regs3 2) = sp) by exact FspZ.
  assert (Hsp0 : 0 <= sp).
  { rewrite <- Esp. pose proof (bv_unsigned_in_range 64 (CK11.getr regs3 2)) as Rg.
    change (bv_modulus 64) with (2 ^ 64) in Rg. lia. }
  assert (HAb : 0 <= A /\ A + 400 <= 2 ^ 64) by (unfold A.AsanRT.APPMEM_END in Fapp; lia).
  (* the frame byte c = fr + 3040 *)
  destruct (Hframe 3040 ltac:(lia)) as (Hcapp & Hcimg & Hcvis & (bc & Ebc)).
  assert (Hcsh : Reusable.YA0n.w_H W3 (Z_to_bv 64 (A.AsanRT.shadow_addr (fr + 3040))) = false).
  { replace (A.AsanRT.shadow_addr (fr + 3040)) with (Reusable.YG0f.shadow_addr fr + 380).
    - exact (Hfsh 380 ltac:(lia)).
    - unfold A.AsanRT.shadow_addr, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, A.AsanRT.ASAN_K.
      replace (fr + 3040) with (380 * 8 + fr) by lia. rewrite Z.div_add_l by lia. lia. }
  destruct HXC as (HXq & HXa).
  assert (Hstk : LFrame.stk A.Img0.rsegs mem3 (sp - 16) sp).
  { apply (A.ACtlG.KitMem.kitmem_stk_of_journal B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] _ _ _ _ _ _ _ _ _ mem3 md3 k (sp - 16) sp HJ);
      unfold A.ACfn.LLVMF_STK in *; lia. }
  pose proof (A.ProgWorldVisWin.win_vis B) as WV.
  unfold A.ProgWorld.win_vis_stmt in WV.
  assert (Hvis : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (sp - 16) 16).
  { apply (WV A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] _ _ _ _ _ _ _ _ _ mem3 md3 k (sp - 16) 16 HJ);
      unfold A.ACfn.LLVMF_STK in *; lia. }
  assert (Hvis280 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (A + 280) 8).
  { apply (WV A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] _ _ _ _ _ _ _ _ _ mem3 md3 k (A + 280) 8 HJ);
      unfold A.ACfn.LLVMF_STK in *; lia. }
  pose proof (A.ProgBridge.rt_vis_W W3) as HRTV.
  assert (Hgot : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) A.AsanRT.GOT_CELL_K 8).
  { apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HRTV);
      unfold A.AsanRT.GOT_CELL_K, A.AsanRT.RT_LO, A.AsanRT.RT_HI; lia. }
  assert (Hcell : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) A.AsanRT.CELL_K 8).
  { apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HRTV);
      unfold A.AsanRT.CELL_K, A.AsanRT.RT_LO, A.AsanRT.RT_HI; lia. }
  assert (Hcv : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (fr + 3040) 1).
  { split; [lia|]. split; [lia|]. intros a Ha. replace a with (fr + 3040) by lia. exact Hcvis. }
  assert (Hcshv : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (A.AsanRT.shadow_addr (fr + 3040)) 1).
  { unfold A.AsanRT.shadow_addr in *. split; [unfold A.AsanRT.ASAN_K; lia|].
    split; [unfold A.AsanRT.ASAN_K; lia|]. intros a Ha.
    replace a with ((fr + 3040) / 8 + A.AsanRT.ASAN_K) by lia. exact Hcsh. }
  (* G3 *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A81c4c) with 0x81c4c.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRegs.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81c4c) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRegs.xregs_eqv_sym _ _ (LRegs.mkR_of_eqv regs3))].
  (* G4 *)
  pose proof (A.Prog.Seg.P10F_on.p10_evt_F_on A.Prog.reac_ports_unknownF.reac_ports_unknown_F_holds_on
    (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
    (CK11.getr regs3 1) (CK11.getr regs3 2) (CK11.getr regs3 3) (CK11.getr regs3 4) (CK11.getr regs3 5)
    (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8) (CK11.getr regs3 9) (CK11.getr regs3 10)
    (CK11.getr regs3 11) (CK11.getr regs3 12) (CK11.getr regs3 13) (CK11.getr regs3 14) (CK11.getr regs3 15)
    (CK11.getr regs3 16) (CK11.getr regs3 17) (CK11.getr regs3 18) (CK11.getr regs3 19) (CK11.getr regs3 20)
    (CK11.getr regs3 21) (CK11.getr regs3 22) (CK11.getr regs3 23) (CK11.getr regs3 24) (CK11.getr regs3 25)
    (CK11.getr regs3 26) (CK11.getr regs3 27) (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30)
    (CK11.getr regs3 31)
    CK11.fp_regs CK11.fp_csr mem3 A (fr + 3040) (sp - 16) F9 R10 R18 ltac:(lia)
    (HXq A F9 ltac:(lia))
    ltac:(rewrite Esp; exact Hstk)
    ltac:(rewrite Esp; unfold A.Prog.reac_ports_unknown_c.REAC_PORTS_UNKNOWN_FRAME; lia)
    (proj1 Hrt) HXa
    ltac:(split; [lia | split; [lia | intros i Hi; replace (fr + 3040 + i) with (fr + 3040) by lia;
            unfold LMem.wa; unfold wview; rewrite Ebc; discriminate]])
    ltac:(rewrite Esp; unfold A.Prog.reac_ports_unknown_c.REAC_PORTS_UNKNOWN_FRAME; left;
          unfold A.ACfn.LLVMF_STK in *; lia)
    ltac:(rewrite Esp; unfold A.Prog.reac_ports_unknown_c.REAC_PORTS_UNKNOWN_FRAME;
          intros x Hx; cbn [LFrame.outside];
          assert (Hxc : x <> fr + 3040);
          [ intros Exc; subst x;
            destruct Hx as [Hx | [Hx | Hx]];
            [ apply Hcimg; apply p10_in_img; unfold A.AsanRT.GOT_CELL_K in Hx; lia
            | apply Hcimg; apply p10_in_img; unfold A.AsanRT.CELL_K in Hx; lia
            | exact (A.AsanRTFacts.app_not_shadow _ Hcapp Hx) ]
          | assert (Hxs : x < sp - 16);
            [ destruct Hx as [Hx | [Hx | Hx]];
              [ unfold A.AsanRT.GOT_CELL_K in Hx | unfold A.AsanRT.CELL_K in Hx
              | unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
                  A.AsanRT.HIGHMEM_BEG in Hx ];
              unfold A.ACfn.LLVMF_STK in *; lia
            | split; [lia | split; [lia | exact I]] ] ])
    ltac:(exact (A.ProgBridge.rng_of_visible _ _ _ Hvis280))
    ltac:(rewrite Esp; unfold A.Prog.reac_ports_unknown_c.REAC_PORTS_UNKNOWN_FRAME;
          exact (A.ProgBridge.rng_of_visible _ _ _ Hvis))
    (A.ProgBridge.rng_of_visible _ _ _ Hgot) (A.ProgBridge.rng_of_visible _ _ _ Hcell)
    (A.ProgBridge.rng_of_visible _ _ _ Hcv) (A.ProgBridge.rng_of_visible _ _ _ Hcshv)) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 _ _ (POST cx)
           (A.ACtlG.P8.w3_fevt_run _ _ _ _ HFS)).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  (* G5 *)
  intros ms' md' [Hrun HQ] Hsbm.
  destruct HQ as (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & m' & Ems & HMU & HWM & HST' & Hbyte).
  subst ms'.
  rewrite Esp in HMU. unfold A.Prog.reac_ports_unknown_c.REAC_PORTS_UNKNOWN_FRAME in HMU.
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (LMState.MS ?R _ _ _ _ _ _) _) _ => set (RX := R) end.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81c60) RX m' md') (POST cx)).
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
  set (WR := [(sp - 16, sp); (fr + 3040, fr + 3040 + 1)]) in HMU.
  assert (Hlow : A.AsanRT.HIGHMEM_BEG <= sp - 16)
    by (unfold A.AsanRT.HIGHMEM_BEG, A.ACfn.LLVMF_STK in *; lia).
  assert (Out2 : forall x, ~ (sp - 16 <= x < sp) -> x <> fr + 3040 -> LFrame.outside WR x).
  { intros x H1 H2. unfold WR. cbn [LFrame.outside]. split; [exact H1|]. split; [lia | exact I]. }
  assert (Osp : forall x, Reusable.YG0d.spZ regs3 <= x -> LFrame.outside WR x).
  { intros x Hx. rewrite FspZ in Hx. apply Out2; unfold A.ACfn.LLVMF_STK in *; lia. }
  assert (Osh : forall x, A.AsanRT.in_shadow x -> LFrame.outside WR x).
  { intros x Hx. apply Out2.
    - unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
        A.AsanRT.HIGHMEM_BEG in Hx, Hlow. lia.
    - intros Exc. subst x. exact (A.AsanRTFacts.app_not_shadow _ Hcapp Hx). }
  assert (Ofr : forall x, (fr <= x < fr + 2880) \/ (fr + 4088 <= x < fr + 4096) -> LFrame.outside WR x).
  { intros x Hx. assert (Hx' : fr <= x < fr + 4096 /\ x <> fr + 3040) by (destruct Hx; lia).
    apply Out2; unfold A.ACfn.LLVMF_STK in *; lia. }
  assert (Oin : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
                  LFrame.outside WR x).
  { intros x Hx. destruct (Hinput x Hx) as [Hx1 Hx2]. apply Out2; unfold A.ACfn.LLVMF_STK in *; lia. }
  refine (HX cx idx fr k ly3 S3 W3 RX m' md' HB _ HF HL Hk _ _).
  - (* the journal: ProgWorld.ajournal_of_fsteps; the window is awr_byte's stack case, the code byte its owned
       frame case *)
    match type of Hrun with Reusable.YK04R.fsteps _ _ ?ms0 ?ms1 =>
      refine (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx _ _ _ _ _ _ _ _ _ _ _ _ ms0 ms1 _ _ _ _ WR
                HJ Hrun (A.ProgBridge.fp_avoids_RNG_W _) HMU Hsbm _) end.
    intros a _ Hno. apply A.ACtlG.P8.w3_not_outside2 in Hno.
    unfold Reusable.YCbq.awr_byte. destruct Hno as [Hno | Hno].
    + left. unfold A.ACfn.LLVMF_STK in *. lia.
    + right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
      left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3.
      change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
  - (* the exit body C_A81c60 (ACtlCutP.v:1923-1934) *)
    cbv beta iota delta [ACtlCut.cut_body A.ACtlCutP.C_A81c60].
    destruct (A.ACtlG.P8.w3_core_keep B cx fr regs3 RX mem3 m' WR
                (conj HFRAC (conj HOUR (conj HCUR (conj HPRO (conj S144 (conj A2691 (conj S192 (conj Afrag
                  (conj A2688 (conj HIDB (conj HFGB (conj (conj HXq HXa) A2880))))))))))))
                K2 K3 K4 K8 K9 K19 K22 K25 K26 HMU (fun i Hi => proj1 (Hframe i Hi)) Osp Osh Ofr Oin)
      as (HFRAC' & HOUR' & HCUR' & HPRO' & S144' & A2691' & S192' & Afrag' & A2688' & HIDB' & HFGB' & HXC' &
          A2880').
    exact (conj HP (conj HFRAC' (conj Hn (conj HOUR' (conj HCUR' (conj HPRO' (conj S144' (conj A2691'
      (conj S192' (conj Afrag' (conj A2688' (conj HIDB' (conj HFGB' (conj K10 (conj Hbyte (conj HXC'
      A2880')))))))))))))))).
  - (* ctl_rt_C: the window is high application memory, the code byte a frame byte, neither an image byte; the
       state's regions are kept *)
    apply (A.ACtlG.P8.w3_ctlrtC_munch B ly3 S3 WR mem3 m' Hrt HMU).
    intros x Hx. apply A.ACtlG.P8.w3_not_outside2 in Hx. destruct Hx as [Hx | Hx].
    + split.
      * unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. right. lia.
      * intros Hi. pose proof (A.ACtlG.Kit.kit_segs_low x Hi) as Hl.
        unfold Reusable.YG0f.kLowMemEnd, A.AsanRT.HIGHMEM_BEG in *. lia.
    + replace x with (fr + 3040) by lia. exact (conj Hcapp Hcimg).
Qed.

End GlueP10.

Print Assumptions glue_seg_P10.
