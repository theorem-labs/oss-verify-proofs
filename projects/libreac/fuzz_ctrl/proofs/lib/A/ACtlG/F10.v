(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 4006 of its 4152 lines of code are new or changed and 2320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4b.v, with its module paths and module names changed; 782 of its 845 lines of code are new or changed and 4089 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F12.v; 218 of its 245 lines of code are new or changed and 818 lines of the source are left out. *)
(* lib/A/ACtlG/F10.v -- GLUE for stage seg_F10 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:770-772,
   piece W4b).  Written by a Theorem Labs lane; single writer.  rule 24: no function proved
   (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F10 : forall POST (j : nat),
       CF POST (ix_cut C_A8206c_at [Z.of_nat j]) -> CF POST (ix_cut C_A820ac_at [Z.of_nat j]) ->
       CF POST (ix_cut C_A820fc_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ff4_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F10.  Segment F10 starts at 0x81ff4, the return point of `jal reac_ctrl_identity_reply@0x81ff0`, and branches
   on a0 = reply_ret.  The source proof is lib/A/Prog/Seg/F10.v:147-343 (seg_F10, blob b66c500e388 (the blob this tree had at release c5e779efe8c)); this file
   mirrors its steps.  Both arms are the PROVED footprint runs of lib/A/Prog/Seg/F10F.v (blob 37f300c6282):
     seg_F10_run1_F (F10F.v:108-173)  a0 = 1 (ir true): 0x81ff4 -> 0x8206c, reads 7 ranges, writes no memory;
     seg_F10_run2_F (F10F.v:205-222)  a0 = 0 (ir false): 0x81ff4 -> 0x820fc, no memory access.
   The successor C_A820ac_at is not reached from this entry (Seg/F10.v:13-14); its premise is unused.

   THE PROOF (glue-pattern.md section 3, G1-G5)
   G1  ix_cut's index equation, then C_A81ff4_at's body (ACtlCutP.v C_A81ff4_at: FRAC, b5_body, and b5_K / b5_RC /
       the a0 pin / the b5_RPost clause / IDj / b5_F17 / b5_W240 / b5_PF); `Z.to_nat (Z.of_nat j)` by Nat2Z.id.
   G2  the visible footprint (run 1), by the shared KitMem's footprint lemmas (lib/A/ACtlG/KitMem.v section 7,
       a Theorem Labs lane; a Theorem Labs lane's ruling: cite KitMem by name where it states the fact): the three spill cells [A+280,8)
       [A+272,8) [A+264,8) lie in the journal's stack window [c_sp cx - LLVMF_STK, c_sp cx) (FRAC: sp <= A,
       A + 416 <= c_sp cx, c_sp cx - 4096 < sp), so KitMem.kitmem_rng_win; the reply cells [fr+272,8) [fr+304,8)
       lie in the owned class-6 frame [fr, fr + 4096) (KitMem.kitmem_own6 gives its In frames, frame_addr at ly3
       and 4096 <= fr), so KitMem.kitmem_rng_frame; the record byte [phi+26,1) lies in the live block
       (phi, flen cx j) of ablocks (the body's Permutation), so KitMem.kitmem_rng_heap, and its shadow byte
       Z.shiftr (phi + 26) 3 + ASAN_K = shadow_addr (phi + 26) by KitMem.kitmem_rng_heap_sh1.
       The spill base A of b5_C, of b5_K's b5_sp and of FRAC is one value (register 9, all three in [0, 2^64)).
   G3  ProgBridge.cfg_at_MS, then Reusable.YA0nR.SRr_xregs_eqv to the runs' start map Regs6ss.mkR_of regs3.
   G4  case split on RcReply.ir (flen cx j) (t_g (c_in cx) j), as Seg/F10.v:174 does.  Each arm instantiates
       F10F's run at fx := A.Reusable.YK11.mkFP (core fp_regs) (core fp_csr) (glue-pattern.md section 6: the two
       YK11 copies), ProgBridge.fevt_of_evtF, tfibsegs_rsegs, then Reusable.YA0nR.SRr_fevt: run 1 at
       RNG_W (w_H W3) with fp_avoids_RNG_W, run 2 at the empty footprint Kit.kit_RNG0 (fp_avoids vacuous).
   G5  the continuation at the run's end map R: the exit cut's ctl_from at the same cx fr k ly3 S3 W3 mem3:
         journal  Reusable.YCbq.ajournal_exec with the empty write set (memory unchanged, model materialized);
         frames, frame law, k bound, ctl_rt_C   unchanged (exact: route (C)'s ctl_rt_C B ly3 S3 mem3 of a working branch
                  shell, at the same ly3 S3 and memory);
         body     FRAC by Kit.kit_frac_move; the seven b5 bundles by KitMem.kitmem_b5_keep; run 1's six register
                  pins (a0..a5) from the run's post; run 2's IDb1 from IDj on the ir = false edge
                  (ID1 = rp_id (t_ID j) .. = t_ID j there, Seg/F10.v:341).

   THE b5 MOVE IS KitMem.kitmem_b5_keep, and why KitMem carries it (measured 2026-10-29; first written here as the
   local f10g_keep, moved into KitMem by a Theorem Labs lane at a working branch 028b95c2b6b, merged into this
   branch at c5d58e80468).  Seg/F10.v's f10_keep (:130-145) moves the same seven bundles across a register change
   that keeps registers 2 9 18 20 21 22 23 24 25, but it is stated over SlotInv's predicates, and ACtlCutP's
   transcriptions are NOT convertible with them:
     (1) ACtlCutP.f1_IN (ACtlCutP.v:658-659) lacks SlotInv.f1_IN's `(0 < g_n g -> In (g_p g, g_n g) (g_H g))`
         (SlotInv.v:1826), so ACtlCutP.FLSI is weaker than SlotInv.FLSI;
     (2) ACtlCutP.b5_C (ACtlCutP.v:820-825) lacks SlotInv.b5_C's `b5_FS fr m` (SlotInv.v:2128);
     (3) ACtlCutP.b5_PH (ACtlCutP.v:776-780) lacks SlotInv.b5_PH's `(flen g j = 0 -> ~ AC.a_in_fs AC.ASYMS m phi)`
         (SlotInv.v:2058) and reads Reusable.YG0d.spZ where SlotInv reads AC.aspZ.
   f10_keep takes all seven bundles at once, so it cannot be applied from a cut body.  kitmem_b5_keep has f10_keep's
   statement and its unfold + rewrite proof, over ACtlCutP's predicates and the core's Reusable.YK11.getr.

   SECTION HYPOTHESES
   - LAWS: the core's AR law record (YCbq.v:207, Section a0's hypothesis), the one ACtl.v:185 carries; ajournal_exec
     and KitMem's own6 / footprint lemmas take it.
   Nothing else: both runs are Required from Seg/F10F.v (PROVED), every bound is discharged from the walk state.
   PROOF-INTERNAL steps that name frame-route constants (allowed by the closure rule): A.Prog.Seg.F10.f10_sh26
   (the shadow byte of phi+26 is 0, from HB's addressable block) and A.Prog.Seg.F10.f10_lrw8 (an 8-byte reply cell
   as bytes).

   CLOSURE (glue closure rule, a Theorem Labs lane 23:32Z / porter 23:38Z, 23:40Z): every Require is qualified, no Import /
   Export of a project module; the twin modules this file names (YK11 YK1b YM05 YO09) and lib/Lib's ExecF / MState /
   Regs6ss are loaded and named by their absolute path.  Shared kits: lib/A/ACtlG/Kit.v 7e164a09a73 and
   lib/A/ACtlG/KitMem.v 0628a0a76e6 (at branch HEAD c5d58e80468).  Frame-route files reached through Seg/F10F.v
   (blob at c5d58e80468): Seg/F10.v b66c500e388, Seg/F10F.v 37f300c6282, Seg/Tac_slot.v de02ff45188 (of record),
   Seg/Tac_b5.v 4a9ebd96689, SlotInv.v 4cf85db229a (of record), SlotModel.v 04dc7903221 (of record), AsanRT.v
   b67d26f8ec7 (mcs 30), AsanRTInv.v 2a8602e8526, AsanRTFacts.v 1657e654e8c, Contract.v fa6fd478d9a, FrameAPI.v
   f6ffefa9bb4, MemNorm.v cb518fc0304, PContract.v a0c4b1b2aa5, AsanLift.v e92b008d733, KindBGlue.v 35e845dad50,
   RcAsanFPLib.v e1f4a4f0b5a.  No statement here names a frame-route identifier.  No start-up table value is read
   (no ts_zsh / am_const / owned_static / const_shadow / AB01 / port_core_refused literal): the shadow byte of
   phi+26 comes from the AR shadow law of the live block (KitMem.kitmem_rng_heap_sh1) and from HB (f10_sh26).
   FRAC is only read (destructs end in `& _`) and moved by Kit.kit_frac_move; no lemma here re-establishes FRAC.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at only fully qualified.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/F10.v   -- hits only inside comments.

   ROUTE (C) BUILD STATE: type-check rc=0 on a working branch shell 1899bed1aee (cb build, a build machine, log
   (internal path), build 2026-10-29T13:05:56Z); build of record: a Theorem Labs lane's cbrec record
   over lib/A/ACtlG/L3W4bAudit.v (not in this delivery).  The paragraph below is the pre-route-(C) state.
   BUILD STATE (honest): TYPECHECKS, rc=0, build 2026-10-29T07:30:41Z
   (a build machine, wb4b.sh, at branch HEAD c5d58e80468 with KitMem.kitmem_b5_keep; the first green build,
   build-20261029T072129Z.log, compiled Seg/F10.vo, Seg/F10F.vo and this file fresh).  TYPES ONLY: the build
   workspace replaces the core's undefined port_core_refused_<hex> names by their literals (A/AE2k.v is in this
   closure through the CF notation's SK); no AD2l stand-in (A/AD2l.v is not in the closure).  Print Assumptions
   glue_seg_F10: the Rocq primitives (PrimInt63 / PrimString / PrimArray) and functional_extensionality_dep only.
   No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.AsanRT A.ACtlK A.ACfn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcReply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F10 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F10F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* Qualified-use aliases (no Import), as ACtlCutP.v:304-308 names the same two models. *)
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module RRP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcReply.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v binds it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueF10.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :278-282), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81ff4_at := (ACtlCutP.C_A81ff4_at B).
Local Notation C_A8206c_at := (ACtlCutP.C_A8206c_at B).
Local Notation C_A820ac_at := (ACtlCutP.C_A820ac_at B).
Local Notation C_A820fc_at := (ACtlCutP.C_A820fc_at B).

(* F10F's runs live over ctrl's lib/A/Reusable/YK11 FPState (F10F.v:102); this is the core's fx in that class
   (glue-pattern.md section 6): its projections reduce by iota to the core's fp_regs / fp_csr. *)
Local Notation fxA :=
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.mkFP
     (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs fx)
     (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr fx)).

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:185). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

Lemma glue_seg_F10 : forall POST (j : nat),
  CF POST (ix_cut C_A8206c_at [Z.of_nat j]) -> CF POST (ix_cut C_A820ac_at [Z.of_nat j]) -> CF POST (ix_cut C_A820fc_at [Z.of_nat j]) ->
  CF POST (ix_cut C_A81ff4_at [Z.of_nat j]).
Proof.
  intros POST j HX1 _ HX3 cx idx fr k ly3 S3 W3 regs3 mem3 md3 Hbase HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:232-234; C_A81ff4_at, ACtlCutP.v). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81ff4_at ACtlCutP.ixn ACtlCutP.b5_body nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & Hperm & Hn26 & Hj255 & HHB & HFLSI & HLK & HbC & HbK & HbRC & Ha0 & Hpost &
    HID & H17 & H240 & HPF).
  pose proof HFRAC as (Af & sp & _ & _ & _ & _ & _ & FR9 & _ & _ & FR26 & _ & _ & FAS & FspA & FfrA & FA416 &
    FSsp & FSapp & _).
  pose proof HbC as (R23 & R18 & (Ab & RA9 & HAb & HSPILL & _) & HPH & _).
  pose proof HbK as (_ & Q22 & _ & _ & Qsp280 & _ & Hargs).
  (* G3: the cut's configuration in the runs' state form, then the walk moved to the runs' start map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81ff4_at [Z.of_nat j])) with 0x81ff4.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3) regs3
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x81ff4)
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
           (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.xregs_eqv_sym _ _
                (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the reply result decides the arm (Seg/F10.v:174). *)
  destruct (RRP.ir (ACtlCutP.flen cx j) (SM.t_g (ACtlCut.c_in cx) j)) eqn:Hir.
  - (* ---- a0 = 1 (reply_ok): run 1, 0x81ff4 -> 0x8206c (Seg/F10.v:175-289) ---- *)
    assert (Hok : RRP.reply_ok phi (ACtlCutP.flen cx j) (fr + 256) (fr + 272) (fr + 304)
                    (SM.t_g (ACtlCut.c_in cx) j) = true)
      by (unfold RRP.reply_ok; rewrite Hargs, Hir; reflexivity).
    assert (Hr1 : RRP.reply_ret phi (ACtlCutP.flen cx j) (fr + 256) (fr + 272) (fr + 304)
                    (SM.t_g (ACtlCut.c_in cx) j) = 1)
      by (unfold RRP.reply_ret; rewrite Hargs, Hir; reflexivity).
    rewrite Hr1 in Ha0.
    pose proof (Hpost Hok) as HRP.
    pose proof HRP as (_ & RWp & RWn).
    destruct (RRP.ir_bytes _ _ Hir) as (H50 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsr & _ & _ & Hbs & _).
    assert (Hbig : SM.t_big (ACtlCut.c_in cx) j = true) by (unfold SM.t_big; apply Z.leb_le; exact H50).
    assert (Hsum : SM.t_sum_ok (ACtlCut.c_in cx) j = true)
      by (unfold SM.t_sum_ok; rewrite Hbig; unfold RRP.ir_blk in Hbs; rewrite Hbs; reflexivity).
    rewrite Hbig in Q22.
    destruct HHB as (Hphi0 & HAd).
    pose proof HAd as (Hp0 & _ & Hpe & _).
    unfold A.ACtlK.a_size, A.AsanRT.APPMEM_END in Hpe. rewrite Z.max_l in Hpe by lia.
    destruct HPH as (HGb & _).
    pose proof (HGb H50) as HG.
    (* the visible footprint (G2), by KitMem's footprint lemmas *)
    pose proof HJ as (HAR & _).
    destruct (A.ACtlG.KitMem.kitmem_own6 (SK := A.AE2k.tfib_sink_head) B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
      as (Hin6 & Efr3 & Hfr4096 & _).
    assert (Hfs : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
    pose proof (A.ACtlG.KitMem.kitmem_rng_frame B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 272) 8
                  HAR Hin6 ltac:(rewrite Efr3; lia) ltac:(rewrite Efr3, Hfs; lia)) as Vpp.
    pose proof (A.ACtlG.KitMem.kitmem_rng_frame B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 304) 8
                  HAR Hin6 ltac:(rewrite Efr3; lia) ltac:(rewrite Efr3, Hfs; lia)) as Vpn.
    (* the one spill base A (register 9) of FRAC, b5_C and b5_K's b5_sp *)
    unfold ACtlCutP.FRAME_BYTES in FfrA. unfold A.AsanRT.APPMEM_END in FSapp.
    assert (EAf : Af = Ab).
    { assert (E : Z_to_bv 64 Af = Z_to_bv 64 Ab)
        by (unfold ACtlCut.rgv in FR9, RA9; rewrite <- FR9; exact RA9).
      apply (f_equal (bv_unsigned (n:=64))) in E.
      rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit in E by lia. exact E. }
    subst Af.
    destruct Qsp280 as (A' & RA'9 & HA' & Hq280).
    assert (EA' : A' = Ab).
    { assert (E : Z_to_bv 64 A' = Z_to_bv 64 Ab)
        by (unfold ACtlCut.rgv in RA'9, RA9; rewrite <- RA'9; exact RA9).
      apply (f_equal (bv_unsigned (n:=64))) in E.
      rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit in E by lia. exact E. }
    subst A'.
    rewrite Hsum in Hq280.
    destruct HSPILL as (_ & _ & _ & _ & _ & _ & _ & _ & Hq272 & Hq264).
    assert (V280 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng
                     (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (Ab + 280) 8)
      by (eapply (A.ACtlG.KitMem.kitmem_rng_win (SK := A.AE2k.tfib_sink_head) B);
          [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]).
    assert (V272 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng
                     (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (Ab + 272) 8)
      by (eapply (A.ACtlG.KitMem.kitmem_rng_win (SK := A.AE2k.tfib_sink_head) B);
          [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]).
    assert (V264 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng
                     (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (Ab + 264) 8)
      by (eapply (A.ACtlG.KitMem.kitmem_rng_win (SK := A.AE2k.tfib_sink_head) B);
          [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]).
    (* the record block (phi, flen cx j) is live (the body's Permutation) *)
    assert (Hinb : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
    { eapply Permutation_in; [exact (Permutation_sym Hperm)|]. apply in_or_app. right. left. reflexivity. }
    assert (Hrq : Reusable.YG00.req_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j)
      by (unfold Reusable.YG00.req_size; rewrite (proj2 (Z.eqb_neq (ACtlCutP.flen cx j) 0)) by lia; reflexivity).
    pose proof (A.ACtlG.KitMem.kitmem_rng_heap B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 26) 1
                  HAR Hinb ltac:(lia) ltac:(rewrite Hrq; lia)) as V26.
    (* the run reads the shadow byte as Z.shiftr (phi + 26) 3 + ASAN_K = shadow_addr (phi + 26) *)
    assert (Vsh : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng
                    (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (Z.shiftr (phi + 26) 3 + A.AsanRT.ASAN_K) 1).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      exact (A.ACtlG.KitMem.kitmem_rng_heap_sh1 B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 26)
               HAR Hinb ltac:(lia) ltac:(rewrite Hrq; lia)). }
    (* the run (F10F.v:108-129), at the core's fx in ctrl's class *)
    pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F10F.seg_F10_run1_F (fx := fxA)
      regs3 mem3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) Ab fr phi (ACtlCutP.flen cx j)
      (SM.t_g (ACtlCut.c_in cx) j)
      Ha0 RA9 R23 R18 Q22 FR26 ltac:(lia) ltac:(lia) H50 Hsr
      ltac:(unfold SM.t_g; rewrite SM.fr50_length; lia)
      Hq280 Hq272 Hq264
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F10.f10_lrw8 mem3 (fr + 272) (Z_to_bv 64 (phi + 38)) RWp)
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F10.f10_lrw8 mem3 (fr + 304)
         (Z_to_bv 64 (RRP.ir_s (SM.t_g (ACtlCut.c_in cx) j) - 13)) RWn)
      HG (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F10.f10_sh26 mem3 phi (ACtlCutP.flen cx j) HAd H50)
      V280 V272 V264 Vpp Vpn Vsh V26) as HRUN.
    pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
    rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
    apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
             (POST cx) HFS).
    { exact (A.ProgBridge.fp_avoids_RNG_W (Reusable.YA0n.w_H W3)). }
    (* G5: the continuation at the run's end map R *)
    intros ms' md' HQ0 Hsbm.
    destruct HQ0 as (R & pc' & mem' & Ems & Hpc & Hmem & K2 & K3 & K4 & K8 & K19 & K20 & K21 & K24 & K25 &
      K9 & K26 & K18 & K22 & K23 & K10 & K11 & K12 & K13 & K14 & K15).
    subst ms' pc' mem'.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A8206c_at [Z.of_nat j])) R mem3 md') (POST cx)).
    assert (E9 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 9 =
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 9)
      by (transitivity (Z_to_bv 64 Ab); [exact K9 | symmetry; exact RA9]).
    assert (E18 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 18 =
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 18)
      by (transitivity (Z_to_bv 64 (ACtlCutP.flen cx j)); [exact K18 | symmetry; exact R18]).
    assert (E22 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 22 =
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 22)
      by (transitivity (Z_to_bv 64 (phi + 18)); [exact K22 | symmetry; exact Q22]).
    assert (E23 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 23 =
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 23)
      by (transitivity (Z_to_bv 64 phi); [exact K23 | symmetry; exact R23]).
    assert (E26 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 26 =
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 26)
      by (transitivity (Z_to_bv 64 A.ACtlK.ASAN_K); [exact K26 | symmetry; exact FR26]).
    destruct (A.ACtlG.KitMem.kitmem_b5_keep cx j phi fr regs3 R mem3 K2 E9 E18 K20 K21 E22 E23 K24 K25
                HFLSI HLK HbC HbK H17 H240 HPF)
      as (HFLSI' & HLK' & HbC' & HbK' & H17' & H240' & HPF').
    apply (HX1 cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' Hbase).
    + (* journal: no byte written, the model materialized (YCbq.v:636-643) *)
      eapply (Reusable.YCbq.ajournal_exec (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low)
        with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity
        | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl
        | intros x _; reflexivity | exact Hsbm | intros a Ha; destruct Ha].
    + exact HF.
    + exact HL.
    + exact Hk.
    + (* the exit body, C_A8206c_at, at the same turn j *)
      split; [reflexivity|].
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A8206c_at ACtlCutP.ixn ACtlCutP.b5_body nth].
      rewrite Nat2Z.id.
      split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 E9 K19 E26)|].
      exists phi.
      split; [exact Hperm|]. split; [exact Hn26|]. split; [exact Hj255|].
      split; [exact (conj Hphi0 HAd)|].
      split; [exact HFLSI'|]. split; [exact HLK'|]. split; [exact HbC'|]. split; [exact HbK'|].
      split; [exact HbRC|]. split; [exact H50|]. split; [exact Hsum|]. split; [exact Hok|].
      split; [exact HRP|].
      split; [exact K10|].
      split; [unfold ACtlCut.rgv; transitivity (Z_to_bv 64 (RRP.ir_s (SM.t_g (ACtlCut.c_in cx) j) - 13 + 5));
              [exact K11 | f_equal; lia]|].
      split; [exact K12|]. split; [exact K13|]. split; [exact K14|]. split; [exact K15|].
      split; [exact HID|].
      split; [exact H17'|]. split; [exact H240' | exact HPF'].
    + (* ctl_rt_C: the entry cut's ly3 S3 and memory *)
      exact Hrt.
  - (* ---- a0 = 0 (reply_args, ir false): run 2, `bne a0,a1` taken to 0x820fc (Seg/F10.v:290-342) ---- *)
    assert (Hr0 : RRP.reply_ret phi (ACtlCutP.flen cx j) (fr + 256) (fr + 272) (fr + 304)
                    (SM.t_g (ACtlCut.c_in cx) j) = 0)
      by (unfold RRP.reply_ret; rewrite Hargs, Hir; reflexivity).
    rewrite Hr0 in Ha0.
    pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F10F.seg_F10_run2_F (fx := fxA)
      regs3 mem3 A.ACtlG.Kit.kit_RNG0 Ha0) as HRUN.
    pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
    rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
    apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx) HFS).
    { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
    intros ms' md' HQ0 Hsbm.
    destruct HQ0 as (R & pc' & mem' & Ems & Hpc & Hmem & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 &
      K23 & K24 & K25 & K26).
    subst ms' pc' mem'.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A820fc_at [Z.of_nat j])) R mem3 md') (POST cx)).
    destruct (A.ACtlG.KitMem.kitmem_b5_keep cx j phi fr regs3 R mem3 K2 K9 K18 K20 K21 K22 K23 K24 K25
                HFLSI HLK HbC HbK H17 H240 HPF)
      as (HFLSI' & HLK' & HbC' & HbK' & H17' & H240' & HPF').
    apply (HX3 cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' Hbase).
    + eapply (Reusable.YCbq.ajournal_exec (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low)
        with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity
        | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl
        | intros x _; reflexivity | exact Hsbm | intros a Ha; destruct Ha].
    + exact HF.
    + exact HL.
    + exact Hk.
    + (* the exit body, C_A820fc_at, at the same turn j *)
      split; [reflexivity|].
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A820fc_at ACtlCutP.ixn ACtlCutP.b5_body nth].
      rewrite Nat2Z.id.
      split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
      exists phi.
      split; [exact Hperm|]. split; [exact Hn26|]. split; [exact Hj255|]. split; [exact HHB|].
      split; [exact HFLSI'|]. split; [exact HLK'|]. split; [exact HbC'|]. split; [exact HbK'|].
      split; [exact HbRC|]. split; [exact Hir|].
      (* IDb1: on the ir = false edge the stage-2 record ID1 cx j is the carried t_ID j (Seg/F10.v:341) *)
      split; [unfold ACtlCutP.IDb1, ACtlCutP.ID1, SM.rp_id; rewrite Hir; exact HID|].
      split; [exact H17'|]. split; [exact H240' | exact HPF'].
    + (* ctl_rt_C: the entry cut's ly3 S3 and memory *)
      exact Hrt.
Qed.

End GlueF10.

Print Assumptions glue_seg_F10.
