(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module paths, module names and numbers changed; 884 of its 966 lines of code are new or changed and 1993 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F13.v, with its module paths and module names changed; 336 of its 364 lines of code are new or changed and 938 lines of the source are left out. *)
(* lib/A/ACtlG/R19.v -- GLUE for stage seg_R19 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:702).  Written by a Theorem Labs lane; single writer.  The pattern is
   glue-pattern.md (a working note, not in this delivery) (steps G1-G5), the worked example lib/A/ACtlG/A5.v.
   rule 24: no function proved (kind: segment lemma; stage glue of a walk).

   WHAT IT PROVES
     glue_seg_R19 : forall POST (b : nat),
       CF POST (ix_cut C_A818e8_at [Z.of_nat b]) -> CF POST (ix_cut C_A818d0_at [Z.of_nat b])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_R19.  Segment R19 is [0x818d0, 0x818e8) (Seg/R19.v:1-9): `bnez a0` not taken (a0 = vd <> 0), a2 := 32,
   a0 := s11 = phi + 18, a1 := s2 = decl_slot fr, `jal wrapper_bcmp` at 0x818e4; the wrapper writes only its stack
   scratch [sp - BCMP_WRAP_K, sp) and returns a0 = memcmp of the two 32-byte buffers, which is 0 because the 32 bytes
   at phi + 18 are the declaration of the input's catalogue row (B3Rtm.a_rtm_X0).

   THE RUN: Seg/R19F_on.v r19_evt_F_on (route (C) twin of a Theorem Labs lane's R19F.r19_evt_F (its source is not in this delivery), written by this lane with
   a Theorem Labs lane's consent; R19F.v (not in this delivery) unchanged).  Its post (munch of the wrapper's window, wmono, ro_agree, stk, a0 = v,
   registers 2-4, 8, 9, 18-27 kept) rebuilds C_A818e8_at: checked against ACtlCutP.v:1763-1788 before use (pattern
   section 6).  Its callee premise bcmp_wrap_contract_F_on is discharged by the PROVED
   A.Prog.bcmp_wrap_on.bcmp_wrap_holds_F_on (a Theorem Labs lane), its rng_bytes premise by A.ProgBridge.rng_bytes_RNG_W.  No
   split (the run is lifted whole).

   THE PROOF
   G1  unfold the entry cut: ix_cut's index equation, C_A818d0_at's 32 conjuncts (ACtlCutP.v:1623-1650), b = 0, RFb.
   G2  the run's premises, all from VISIBLE state: registers a0 / s11 / s2 / sp from the body and FRAC; the left buffer
       bytes from RFb's frame bytes at phi (firstn 32 (skipn 18 F_0) = decl, B3Rtm.a_rtm_X0); memcmp decl decl 32 = 0
       (R19.r19_memcmp_refl); addressability / end_in_app / app_mem from HB, the decl slot and PRO's our[] bytes; the
       runtime cells from ctl_rt_C (asan_cells, ro_agree) and from rt_of_core_C (A.ProgWorldRtC.rt_of_core_C, PROVED:
       REAL_BCMP / REAL_MEMCMP slots of RT_used_C, GOT_CF and CF + 254 / 255 of asan_cf_cells, as R19.r19_cells reads
       them); the run's shadow region bcmp_wrap_shadow_R (phi + 18) (decl_slot fr) 32 from ctl_rt_C's cut_shadow by
       shadow_rw_on_mono: the left buffer's shadow words lie in the live block (phi, n_0)'s word cover (L), the right
       buffer's (decl_slot fr = fr + 2560, fr mod 32 = 0) in the owned class-6 frame's shadow (F); the stack window
       present (KitMem.kitmem_stk_of_journal: [c_sp - LLVMF_STK, c_sp) holds
       [sp - BCMP_WRAP_K, sp) since c_sp - 4096 < sp <= A <= c_sp); the bounds: the window is above
       alloc_ceiling + 24112 and the class-6 frame ends at fr + 4096 <= alloc_ceiling (KitMem.kitmem_own6:
       frames_bounds + frame law + layout_le's ly_F, and astk_ok's alloc_ceiling <= c_sp - LLVMF_STK), the heap block
       (phi, n_0) of the body's Permutation ends at or below alloc_ceiling (AR block law).  The seven rng premises from
       visibility at RNG := ProgBridge.RNG_W (w_H W3): image ProgBridge.img_vis_W, window ProgWorldVisWin.win_vis,
       left buffer ProgWorldVisHeap.heap_vis / heap_sh_vis, right buffer ProgWorldVisFrame.frame_vis (both parts).
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv to the run's canonical start map Regs6ss.mkR_of regs3 (the
       run's 31 register binders are reg_get regs3 i, so its start map IS mkR_of regs3 by delta).
   G4  ProgBridge.fevt_of_evtF, then YA0nR.SRr_fsteps (the lift of SRr_fevt / SRr_fevt_hid, kept here in its fsteps
       form so that the continuation has the run itself), fp_avoids by ProgBridge.fp_avoids_RNG_W.
   G5  the exit cut at the run's own end map R1 (registers 2 3 4 8 9 18-27 are reg_get regs3 r, so every register
       conjunct of the body is the entry's by conversion; a0 = 0):
         journal  ProgWorld.ajournal_of_fsteps (PROVED, a Theorem Labs lane; it is YCbq.ajournal_exec with the run's hidden
                  bytes and mem_grows from YK04R.fsteps_restrict / pws_fsteps_mem), write set = the window, every
                  written byte awr_byte's stack case (KitMem.kitmem_not_outside, kitmem_awr_win);
         frames, frame law, k bound   unchanged (own6, kmax 2b + 1 on both cuts);
         body     memory conjuncts through the run's munch: every byte the body names is a spill (>= A >= sp,
                  KitMem.kitmem_spill_munch), a frame byte (< fr + 4096 <= alloc_ceiling), the input block or the
                  heap block (<= alloc_ceiling), the saved registers (>= c_sp - 104 > A) or a shadow byte
                  (addressable through AsanRTFacts.munch_meta / addressable_kept); Lib.Frame.bytes_at_transport /
                  rw_cells_transport; FRAC RE-ESTABLISHED at m' by KitMem.kitmem_frac_munch (FRAC's shape, so it also
                  carries the announced trailer word at fr + 4088), moved to R1 by Kit.kit_frac_move;
         ctl_rt_C AsanRTFacts.asan_cells_kept, ShadowRwOnT.shadow_rw_on_kept on both regions (cut_shadow at the same
                  state ly3 S3, img_shadow), and the run's ro_agree.

   SECTION HYPOTHESES (exact text below; source of each)
   - TFIB_SYMS : A.AF0m.CtrlTSyms B.  ACtl.v:193, verbatim (ACtl.v's own Section hypothesis); rt_of_core takes it.
   - LAWS : Reusable.YG0d.AR_laws segs B.  ACtl.v:185, verbatim (ACtl.v's own Section hypothesis).
   rt_of_core_C is CITED, not assumed: A.ProgWorldRtC.rt_of_core_C (a Theorem Labs lane), at FP := [].  Needed for the
   wrapper's five runtime cells (REAL_BCMP, REAL_MEMCMP, GOT_CF, CF + 254, CF + 255), which ctl_rt_C does not carry.
   Route (C): no VIS0 / OWNED_RO (there were none in this file); the cut's ctl_rt_C is opened, never the universal form.
   KitMem (lib/A/ACtlG/KitMem.v, a working branch 0a537d950be, blob 81524d6c608): kitmem_own6,
   kitmem_stk_of_journal, kitmem_spill_munch, kitmem_frac_munch, kitmem_not_outside, kitmem_awr_win.
   No _of_F_bounded corollary (R19F has none, segment-F-premises-A.tsv rows R19).

   CLOSURE: every project Require below is qualified (no Import / Export of a project module); the six modules with a
   lib/A/Reusable twin (YK11 YM05 YO09 used here) and lib/Lib's modules with lib/A/Bz/Lib / lib/A/Tk/UL twins are
   loaded by absolute name and cited through module aliases.  No statement here names a frame-route identifier.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are YK11 / YG0d-qualified everywhere.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/R19.v   -- hits only inside comments.

   BUILD STATE (route (C), type-check): rc=0 on a working branch (a working branch 1899bed1aee merged) through
   cb (BASE row 23b918fe0c2e, a build machine), no substitution; the build of record
   (cbrec) is named in the commit.  Print Assumptions glue_seg_R19 = Rocq primitives + functional_extensionality_dep.
   No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.AF0m A.Img0 A.AsanRT A.ACfn A.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP A.ProgBridge A.ProgWorld A.ProgWorldRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT A.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisWin A.ProgWorldVisHeap A.ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.rng_asan A.Prog.ImgBounds.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
(* The segment's _F run, its callee's closed contract, and the source lemmas the model facts come from (all in the
   closure of Seg/R19F.v). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R19F_on A.Prog.bcmp_wrap_on A.Prog.bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.bcmp_wrap_c_on A.Prog.sh_word_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.memcmp_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R19 A.Prog.Seg.B3Rtm A.Prog.Seg.Tac_rt2_b2.
Import ListNotations.
Local Open Scope Z_scope.

Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module K11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module M05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.

(* The core's segment list, as ACtlCut.v:76 and ACtl.v:165 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueR19.

(* ACtl.v's Section shape (ACtl.v:172-176), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :246-247), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A818d0_at := (ACtlCutP.C_A818d0_at B).
Local Notation C_A818e8_at := (ACtlCutP.C_A818e8_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* ACtl.v:193 *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
(* ACtl.v:185 *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_R19 : forall POST (b : nat), CF POST (ix_cut C_A818e8_at [Z.of_nat b]) -> CF POST (ix_cut C_A818d0_at [Z.of_nat b]).
Proof.
  intros POST b HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat b] (ix_cut, ACtlCut.v:234-236; C_A818d0_at, ACtlCutP.v:1623-1650). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A818d0_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & vd & HP & HFRAC & (Hn & HRF & HOUTA & R10 & Hvd & R27 & R18 & HDB) & Hb0 & HHB & Hvdb &
    HLD & HAD & S128 & HPRO & S104 & S96 & S64 & R21 & S112 & S144 & S192 & (idb & Hidb) & (j72 & Hj72) & S280 &
    S240 & (jy & Hjy) & (j32 & Hj32) & S152 & HA38 & HRXS).
  subst b.
  destruct HRF as ((Hb6 & HCUR & HOUR & R23 & HIDB & HFGB) & Hnz & R24 & HF0).
  pose proof Hrt as (AC & Hcut & Himg & RO).
  (* G2: FRAC's registers and bounds (ACtlCutP.v:982-996). *)
  pose proof HFRAC as (Asp & sp & R2 & Hs16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hf32 & HA32 & HAS & HspA &
    HfrA & HA416 & HSlo & HSapp & _).
  unfold A.ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in HSapp.
  (* G2: the owned class-6 frame and the journal's stack window (KitMem.kitmem_own6: frames_bounds + frame law +
     layout_le's ly_F, and astk_ok): 4096 <= fr, fr + 4096 <= alloc_ceiling <= c_sp - LLVMF_STK. *)
  pose proof HJ as (HAR & _).
  destruct (A.ACtlG.KitMem.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & E3 & Hf4096 & _ & Hfc & Hceil).
  unfold A.ACfn.LLVMF_STK in Hceil.
  pose proof (@M05.alloc_ceiling_value rc) as [[Hc0 _] _].
  assert (Efb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Efb in Hfc.
  (* G2: the heap block (phi, n_0) of the body's live list (ACtlCutP.v:1630), its placement (AR_blocks_law). *)
  assert (Hinphi : In (phi, A.ACtlCutP.rnb cx 0) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (A.ACtlCutP.rnb cx 0) HAR Hinphi)
    as (_ & Hp4096 & Hpceil & _).
  destruct (A.Prog.Seg.Tac_rt2_b2.a_rtn (ACtlCut.c_in cx) 0 Hnz) as (_ & Hnb & HLF).
  change (A.ACtlCutP.SM.rt_n (ACtlCut.c_in cx) 0) with (A.ACtlCutP.rnb cx 0) in Hnb, HLF.
  assert (Ereq : Reusable.YG00.req_size (A.ACtlCutP.rnb cx 0) = A.ACtlCutP.rnb cx 0).
  { unfold Reusable.YG00.req_size. rewrite (proj2 (Z.eqb_neq _ _) Hnz). reflexivity. }
  rewrite Ereq in Hpceil.
  pose proof HHB as (Hphinz & HAphi0).
  assert (Hsz : A.ACtlK.a_size (A.ACtlCutP.rnb cx 0) = A.ACtlCutP.rnb cx 0) by (unfold A.ACtlK.a_size; lia).
  pose proof HAphi0 as HAphi. rewrite Hsz in HAphi.
  pose proof HAphi as (Hp0 & _ & HpE & _).
  pose proof (A.ACtlCutP.ARF.addressable_app mem3 _ _ HAphi) as Happ_phi.
  pose proof HAD as (Hd0 & _ & HdE & _).
  pose proof (A.ACtlCutP.ARF.addressable_app mem3 _ _ HAD) as Happ_d.
  pose proof HPRO as (_ & _ & _ & _ & _ & _ & _ & _ & Pad6 & _).
  pose proof (A.ACtlCutP.ARF.addressable_app mem3 _ _ Pad6) as Happ_6.
  unfold A.AsanRT.APPMEM_END in HpE, HdE.
  (* G2: the left buffer: the 32 bytes at phi + 18 are the row's declaration (Seg/R19.v:587-598). *)
  change (Z.of_nat 0) with 0 in HF0.
  assert (HLS : LMem.bytes_at segs mem3 (phi + 18) (firstn 32 (skipn 18 (A.ACtlCutP.SM.rt_F (ACtlCut.c_in cx) 0)))).
  { pose proof HF0 as HF'. rewrite <- (firstn_skipn 18 (A.ACtlCutP.SM.rt_F (ACtlCut.c_in cx) 0)) in HF'.
    apply LMem.bytes_at_app in HF' as [_ HF'].
    rewrite length_firstn, Nat.min_l in HF' by lia.
    rewrite <- (firstn_skipn 32 (skipn 18 (A.ACtlCutP.SM.rt_F (ACtlCut.c_in cx) 0))) in HF'.
    apply LMem.bytes_at_app in HF' as [HF' _]. exact HF'. }
  assert (EX : firstn 32 (skipn 18 (A.ACtlCutP.SM.rt_F (ACtlCut.c_in cx) 0)) =
               A.ACtlCutP.RDC.decl (A.ACtlCutP.SM.rt_mb (ACtlCut.c_in cx))).
  { rewrite <- (A.Prog.Seg.B3Rtm.a_rtm_X0 (ACtlCut.c_in cx)).
    unfold A.ACtlCutP.RFR.bsl, A.ACtlCutP.SM.rt_g, A.ACtlCutP.SM.fr50.
    change (Z.to_nat 32) with 32%nat. change (Z.to_nat 18) with 18%nat.
    rewrite firstn_app. replace (50 - length (A.ACtlCutP.SM.rt_F (ACtlCut.c_in cx) 0))%nat with 0%nat by lia.
    rewrite firstn_O, app_nil_r, skipn_firstn_comm, firstn_firstn. reflexivity. }
  rewrite EX in HLS.
  pose proof (A.Prog.Seg.R19.r19_memcmp_refl (A.ACtlCutP.RDC.decl (A.ACtlCutP.SM.rt_mb (ACtlCut.c_in cx))) 32
                ltac:(lia)) as HM.
  (* G2: the wrapper's five runtime cells, from RT_used_C (rt_of_core_C) as R19.r19_cells reads them (Seg/R19.v:98-113). *)
  pose proof (A.ProgWorldRtC.rt_of_core_C B MT XM_LIB RLO RHI [] TFIB_SYMS LAWS cx (ACtlCut.own6 cx) k ly3 S3 W3
                (K11.mkst regs3 (Z_to_bv 64 0) mem3 (K11.seg_rom segs)) md3 HB HJ Hrt) as HRTU.
  unfold A.ProgWorldRtC.RT_used_C in HRTU.
  destruct HRTU as (_ & _ & _ & _ & HCF & _ & _ & HREAL).
  assert (RBc : LMem.bytes_at A.Img0.rsegs mem3 A.Prog.bcmp_wrap_c.REAL_BCMP
                  (LMem.le8 (LMem.wa A.Prog.bcmp_wrap_c.BCMP))).
  { apply (proj1 (Forall_forall _ _) HREAL (0xa17f0, 0x97b0c)).
    - unfold A.AsanRT.RT_REALS. cbn [List.In]. repeat (first [left; reflexivity | right]).
    - unfold A.ProgWorld.REAL_USED. cbn [List.In fst]. repeat (first [left; reflexivity | right]). }
  assert (RMc : LMem.bytes_at A.Img0.rsegs mem3 A.Prog.bcmp_wrap_c.REAL_MEMCMP
                  (LMem.le8 (LMem.wa A.Prog.memcmp_c.MEMCMP))).
  { apply (proj1 (Forall_forall _ _) HREAL (0xa17e8, 0x97bdc)).
    - unfold A.AsanRT.RT_REALS. cbn [List.In]. repeat (first [left; reflexivity | right]).
    - unfold A.ProgWorld.REAL_USED. cbn [List.In fst]. repeat (first [left; reflexivity | right]). }
  destruct HCF as (HCF1 & _ & _ & _ & _ & _ & HCF7 & _).
  assert (C254 : LMem.bytes_at A.Img0.rsegs mem3 (A.Prog.bcmp_wrap_c.CF + 254) [Z_to_bv 8 1]).
  { replace (A.Prog.bcmp_wrap_c.CF + 254) with (A.AsanRT.RT_CF + 240 + Z.of_nat 14)
      by (unfold A.Prog.bcmp_wrap_c.CF, A.AsanRT.RT_CF; lia).
    exact (A.Prog.Seg.R19.r19_byte mem3 (A.AsanRT.RT_CF + 240) _ 14%nat (Z_to_bv 8 1) HCF7 eq_refl). }
  assert (C255 : LMem.bytes_at A.Img0.rsegs mem3 (A.Prog.bcmp_wrap_c.CF + 255) [Z_to_bv 8 1]).
  { replace (A.Prog.bcmp_wrap_c.CF + 255) with (A.AsanRT.RT_CF + 240 + Z.of_nat 15)
      by (unfold A.Prog.bcmp_wrap_c.CF, A.AsanRT.RT_CF; lia).
    exact (A.Prog.Seg.R19.r19_byte mem3 (A.AsanRT.RT_CF + 240) _ 15%nat (Z_to_bv 8 1) HCF7 eq_refl). }
  (* G2: the wrapper's address premises. *)
  assert (HAL : A.AsanRT.addressable mem3 (phi + 18) 32).
  { apply (A.ACtlCutP.ARF.addressable_sub mem3 phi (A.ACtlCutP.rnb cx 0)); [exact HAphi | lia | lia | lia]. }
  assert (HEL : A.AsanRT.end_in_app (phi + 18) 32) by (right; apply Happ_phi; lia).
  assert (HPL : A.AsanRT.app_mem (phi + 18 + 7)) by (apply Happ_phi; lia).
  assert (HPR : A.AsanRT.app_mem (A.ACtlCutP.decl_slot fr + 7))
    by (apply Happ_d; unfold A.ACtlCutP.decl_slot; lia).
  assert (HER : A.AsanRT.end_in_app (A.ACtlCutP.decl_slot fr) 32).
  { right. pose proof (Happ_d (A.ACtlCutP.decl_slot fr) ltac:(lia)) as Ha1.
    pose proof (Happ_6 (fr + 2624) ltac:(lia)) as Ha2. unfold A.ACtlCutP.decl_slot in *.
    unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. lia. }
  assert (HRL : phi + 18 + 32 <= sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K \/ sp <= phi + 18)
    by (left; unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K; lia).
  assert (HRR : A.ACtlCutP.decl_slot fr + 32 <= sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K \/
                sp <= A.ACtlCutP.decl_slot fr)
    by (left; unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K, A.ACtlCutP.decl_slot; lia).
  assert (Hw1 : ACtlCut.c_sp cx - A.ACfn.LLVMF_STK <= sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K)
    by (unfold A.ACfn.LLVMF_STK, A.Prog.bcmp_wrap_c.BCMP_WRAP_K; lia).
  assert (Hw2 : sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K + A.Prog.bcmp_wrap_c.BCMP_WRAP_K <= ACtlCut.c_sp cx) by lia.
  assert (Hw3 : sp <= ACtlCut.c_sp cx) by lia.
  pose proof (A.ACtlG.KitMem.kitmem_stk_of_journal B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx)
                (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx)
                ly3 S3 W3 mem3 md3 k (sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K) sp HJ Hw1 Hw3) as HST.
  assert (HK' : sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K + A.Prog.bcmp_wrap_c.BCMP_WRAP_K <= sp) by lia.
  assert (Hlo : A.AsanRT.HIGHMEM_BEG <= sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K)
    by (unfold A.AsanRT.HIGHMEM_BEG, A.Prog.bcmp_wrap_c.BCMP_WRAP_K; lia).
  assert (Hsp : sp <= A.AsanRT.APPMEM_END) by (unfold A.AsanRT.APPMEM_END; lia).
  (* G2: the footprint at RNG_W (w_H W3), each range from visibility. *)
  set (RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (Rimg : LEF.rng RNG 0x10000 0x5ee000)
    by exact (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3)).
  assert (Rstk : LEF.rng RNG (sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K) A.Prog.bcmp_wrap_c.BCMP_WRAP_K)
    by exact (A.ProgBridge.rng_of_visible _ _ _
                (A.ProgWorldVisWin.win_vis B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx)
                   (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx)
                   ly3 S3 W3 mem3 md3 k (sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K) A.Prog.bcmp_wrap_c.BCMP_WRAP_K
                   HJ Hw1 Hw2)).
  assert (Hl1 : phi <= phi + 18) by lia.
  assert (Hl2 : phi + 18 + 32 <= phi + Reusable.YG00.req_size (A.ACtlCutP.rnb cx 0)) by (rewrite Ereq; lia).
  assert (RngL : LEF.rng RNG (phi + 18) 32)
    by exact (A.ProgBridge.rng_of_visible _ _ _
                (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (A.ACtlCutP.rnb cx 0) (phi + 18) 32
                   HAR Hinphi Hl1 Hl2)).
  assert (RngLs : LEF.rng RNG (8 * (A.AsanRT.shadow_addr (phi + 18) / 8))
            (8 * (A.AsanRT.shadow_addr (phi + 18 + 32 - 1) / 8) + 8 - 8 * (A.AsanRT.shadow_addr (phi + 18) / 8))).
  { destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (A.ACtlCutP.rnb cx 0) (phi + 18) 32
                HAR Hinphi Hl1 Hl2 ltac:(lia)) as [E0 | HV]; [lia|].
    apply A.ProgBridge.rng_of_visible.
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in HV.
    rewrite !(Z.mul_comm 8). exact HV. }
  assert (Hr1 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) <= A.ACtlCutP.decl_slot fr)
    by (rewrite E3; unfold A.ACtlCutP.decl_slot; lia).
  assert (Hr2 : A.ACtlCutP.decl_slot fr + 32 <=
                Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) + Reusable.YG00.fs_frame_bytes 6)
    by (rewrite E3, Efb; unfold A.ACtlCutP.decl_slot; lia).
  destruct (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx)
              (A.ACtlCutP.decl_slot fr) 32 HAR Hin6 Hr1 Hr2) as (HVR & HVRs).
  assert (RngR : LEF.rng RNG (A.ACtlCutP.decl_slot fr) 32) by exact (A.ProgBridge.rng_of_visible _ _ _ HVR).
  assert (RngRs : LEF.rng RNG (8 * (A.AsanRT.shadow_addr (A.ACtlCutP.decl_slot fr) / 8))
            (8 * (A.AsanRT.shadow_addr (A.ACtlCutP.decl_slot fr + 32 - 1) / 8) + 8
               - 8 * (A.AsanRT.shadow_addr (A.ACtlCutP.decl_slot fr) / 8))).
  { assert (Hq1 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) <= 64 * (A.ACtlCutP.decl_slot fr / 64))
      by (rewrite E3; unfold A.ACtlCutP.decl_slot; Z.div_mod_to_equations; lia).
    assert (Hq2 : 64 * ((A.ACtlCutP.decl_slot fr + 32 - 1) / 64) + 64 <=
                  Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) + Reusable.YG00.fs_frame_bytes 6)
      by (rewrite E3, Efb; unfold A.ACtlCutP.decl_slot; Z.div_mod_to_equations; lia).
    destruct (HVRs ltac:(lia) Hq1 Hq2) as [E0 | HV]; [lia|].
    apply A.ProgBridge.rng_of_visible.
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in HV.
    rewrite !(Z.mul_comm 8). exact HV. }
  (* G2: the run's shadow region, from the cut's ctl_rt_C (route (C)): the left buffer's shadow words lie in the
     word cover of the live block (phi, n_0) (cut_shadow's (L)), the right buffer's in the owned class-6 frame's
     shadow (cut_shadow's (F); decl_slot fr = fr + 2560 and fr mod 32 = 0). *)
  assert (SWR : A.ShadowRwOn.shadow_rw_on
                  (A.Prog.bcmp_wrap_c_on.bcmp_wrap_shadow_R (phi + 18) (A.ACtlCutP.decl_slot fr) 32) mem3).
  { refine (A.ShadowRwOn.shadow_rw_on_mono _ _ mem3 _ Hcut).
    intros a [(_ & Ha) | (_ & Ha)];
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
    - right; left. exists phi, (A.ACtlCutP.rnb cx 0). split; [exact Hinphi|].
      rewrite Ereq. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      Z.div_mod_to_equations; lia.
    - left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
      rewrite E3, Efb. unfold A.ACtlCutP.decl_slot in Ha. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      Z.div_mod_to_equations; lia. }
  (* G3: the cut's configuration in the run's state form (ProgBridge.cfg_at_MS, eq_refl), then the walk moved to the
     run's canonical start map mkR_of regs3 (YA0nR.SRr_xregs_eqv). *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A818d0_at [Z.of_nat 0])) with 0x818d0.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 K11.fp_regs
           (Z_to_bv 64 0x818d0) K11.fp_csr None mem3 (K11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  (* G4: the run (Seg/R19F_on.v r19_evt_F_on) at the run's canonical start map, its callee by the closed contract. *)
  pose proof (A.Prog.Seg.R19F_on.r19_evt_F_on A.Prog.bcmp_wrap_on.bcmp_wrap_holds_F_on RNG
    (Sem.reg_get regs3 1) (Sem.reg_get regs3 2) (Sem.reg_get regs3 3) (Sem.reg_get regs3 4) (Sem.reg_get regs3 5)
    (Sem.reg_get regs3 6) (Sem.reg_get regs3 7) (Sem.reg_get regs3 8) (Sem.reg_get regs3 9) (Sem.reg_get regs3 10)
    (Sem.reg_get regs3 11) (Sem.reg_get regs3 12) (Sem.reg_get regs3 13) (Sem.reg_get regs3 14)
    (Sem.reg_get regs3 15) (Sem.reg_get regs3 16) (Sem.reg_get regs3 17) (Sem.reg_get regs3 18)
    (Sem.reg_get regs3 19) (Sem.reg_get regs3 20) (Sem.reg_get regs3 21) (Sem.reg_get regs3 22)
    (Sem.reg_get regs3 23) (Sem.reg_get regs3 24) (Sem.reg_get regs3 25) (Sem.reg_get regs3 26)
    (Sem.reg_get regs3 27) (Sem.reg_get regs3 28) (Sem.reg_get regs3 29) (Sem.reg_get regs3 30)
    (Sem.reg_get regs3 31)
    K11.fp_regs K11.fp_csr mem3 sp phi (A.ACtlCutP.decl_slot fr) vd 0 (sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K)
    (A.ACtlCutP.RDC.decl (A.ACtlCutP.SM.rt_mb (ACtlCut.c_in cx)))
    (A.ACtlCutP.RDC.decl (A.ACtlCutP.SM.rt_mb (ACtlCut.c_in cx)))
    R2 R27 R18 R10 Hvd Hvdb Hp0 ltac:(lia) Hd0 ltac:(lia) ltac:(lia) ltac:(lia) HLS HDB HM RO HAL HAD HEL HER HPL HPR
    HRL HRR HST HK' Hlo Hsp AC SWR RBc RMc HCF1 C254 C255 (A.ProgBridge.rng_bytes_RNG_W _)
    Rimg Rstk RngL RngLs RngR RngRs) as HRUN.
  destruct (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as (ms' & Hrun & HQ).
  rewrite <- A.ProgBridge.tfibsegs_rsegs in Hrun.
  match type of Hrun with Reusable.YK04R.fsteps _ _ ?s _ => set (ms0 := s) in Hrun end.
  apply (Reusable.YA0nR.SRr_fsteps segs A.ACtlG.Kit.kit_wx W3 ms0 ms' md3 RNG (POST cx) Hrun
           (A.ProgBridge.fp_avoids_RNG_W _)).
  (* G5: the continuation at the run's end state; R1 is the run's own end map. *)
  intros md' Hsbm.
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    Ems & MU & WM & HRO' & STK').
  match type of Ems with _ = ?f ?R _ _ _ _ _ _ => set (R1 := R) in Ems end.
  subst ms'.
  (* the write set and what lies outside it *)
  assert (Hdj : forall a n, a + n <= OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling \/ sp <= a ->
            LFr.disjoint_from [(sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K, sp)] a n).
  { intros a n Han. cbn [LFr.disjoint_from]. split; [|exact I].
    unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K. lia. }
  assert (Hbt : forall a bs, LMem.bytes_at segs mem3 a bs ->
            a + Z.of_nat (length bs) <= OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling \/ sp <= a ->
            LMem.bytes_at segs m' a bs).
  { intros a bs Hb Hab. exact (LFr.bytes_at_transport segs _ mem3 m' a bs Hb MU (Hdj _ _ Hab)). }
  assert (HAW : A.ACtlCutP.ARF.all_app [(sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K, sp)]).
  { cbn [A.ACtlCutP.ARF.all_app]. split; [|exact I]. intros a Ha. right.
    unfold A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END, A.Prog.bcmp_wrap_c.BCMP_WRAP_K in *. lia. }
  pose proof (A.ACtlCutP.ARF.munch_meta _ mem3 m' MU HAW) as HMK.
  assert (Had : forall p n, A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable m' p n)
    by (intros p n Hpn; exact (A.ACtlCutP.ARF.addressable_kept mem3 m' p n Hpn HMK)).
  assert (Hspk : forall off v, A.ACtlCutP.spill regs3 mem3 off v -> 0 <= off -> off <= 304 ->
            A.ACtlCutP.spill R1 m' off v).
  { intros off v Hs Ho0 Ho1.
    apply (A.ACtlG.KitMem.kitmem_spill_munch _ regs3 R1 mem3 m' off v Asp Hs R9 ltac:(lia) Ho0 ltac:(lia) MU
             eq_refl).
    intros x Hx. cbn [LFr.outside]. split; [unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K; lia | exact I]. }
  assert (Hrw : forall a (n : nat) bs, A.ACtlCutP.STP.rw_cells segs mem3 a [A.ACtlCutP.CEL.CB n bs] ->
            fr <= a -> a + Z.of_nat n <= fr + 4096 ->
            A.ACtlCutP.STP.rw_cells segs m' a [A.ACtlCutP.CEL.CB n bs]).
  { intros a n bs Hc Ha1 Ha2. apply (LFr.rw_cells_transport segs _ mem3 m' a _ Hc MU WM).
    apply Hdj. left. cbn [A.ACtlCutP.CEL.cells_size A.ACtlCutP.CEL.csize]. lia. }
  (* the input block (the pre's In (p, n) (ablocks ..) or n = 0, ACfn.v:38-39) lies below alloc_ceiling *)
  assert (Hinb : ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) <=
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling).
  { pose proof HB as ((_ & _ & _ & _ & Hpn & Hlen & _) & _).
    rewrite <- Hlen.
    destruct Hpn as [(E0 & Ep) | (Hn0 & Hinp)].
    - rewrite E0, Ep. unfold A.ACfn.A_EMPTY. lia.
    - assert (Hinp3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
      { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hinp. }
      destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hinp3) as (_ & _ & Hc & _).
      unfold Reusable.YG00.req_size in Hc. rewrite (proj2 (Z.eqb_neq (ACtlCut.c_n cx) 0) ltac:(lia)) in Hc.
      lia. }
  (* the exit's FRAC at the entry map (KitMem.kitmem_frac_munch, by FRAC's shape: it also carries the announced
     fake-frame trailer word at fr + 4088), then at R1 (registers 2 3 4 8 9 19 26 are reg_get regs3 r) *)
  assert (HFRAC' : A.ACtlCutP.FRAC B cx fr fr regs3 m').
  { apply (A.ACtlG.KitMem.kitmem_frac_munch B cx fr fr regs3 mem3 m' _ HFRAC MU).
    - intros x Hx. rewrite HspZ in Hx. cbn [LFr.outside]. split; [|exact I].
      unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K. lia.
    - intros x Hx. cbn [LFr.outside]. split; [|exact I]. unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K. lia.
    - intros x Hx. cbn [LFr.outside]. split; [|exact I].
      unfold A.ACtlCutP.Sfr, A.ACtlCutP.FRAME_SHADOW, A.ACtlCutP.FRAME_BYTES, A.AsanRT.shadow_addr,
        A.AsanRT.ASAN_K, A.Prog.bcmp_wrap_c.BCMP_WRAP_K in *.
      Z.div_mod_to_equations. lia. }
  pose proof (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R1 m' HFRAC' eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl) as HFRAC1.
  (* the body's memory conjuncts at m' *)
  assert (HOUR' : A.ACtlCutP.OURb cx fr m').
  { unfold A.ACtlCutP.OURb in *. apply (Hbt _ _ HOUR). left. rewrite A.ACtlCutP.SM.OUR_length. lia. }
  assert (HIDB' : A.ACtlCutP.IDBr cx fr (A.ACtlCutP.SM.RID (ACtlCut.c_in cx) 0) m').
  { unfold A.ACtlCutP.IDBr in *. apply (Hbt _ _ HIDB). left.
    assert (LI : length (A.ACtlCutP.SM.RID (ACtlCut.c_in cx) 0) = 38%nat) by reflexivity. rewrite LI. lia. }
  assert (HFGB' : A.ACtlCutP.FGBr cx fr (A.ACtlCutP.SM.RFG (ACtlCut.c_in cx) 0) m').
  { unfold A.ACtlCutP.FGBr in *. apply (Hbt _ _ HFGB). left.
    assert (LF : length (A.ACtlCutP.SM.RFG (ACtlCut.c_in cx) 0) = 72%nat) by reflexivity. rewrite LF. lia. }
  assert (HF0' : LMem.bytes_at segs m' phi (A.ACtlCutP.SM.rt_F (ACtlCut.c_in cx) 0)).
  { apply (Hbt _ _ HF0). left. rewrite HLF, Z2Nat.id by lia. lia. }
  (* the exit cut at the run's end state (ProgBridge.cfg_at_MS read backwards) *)
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A818e8_at [Z.of_nat 0])) R1 m' md') (POST cx)).
  apply (HX cx [Z.of_nat 0] fr k ly3 S3 W3 R1 m' md' HB).
  - (* journal: ProgWorld.ajournal_of_fsteps, the write set the wrapper's window, awr_byte's stack case *)
    refine (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
              (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
              (ACtlCut.own6 cx) ly3 S3 W3 ms0 _ md3 md' k RNG [(sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K, sp)]
              HJ Hrun (A.ProgBridge.fp_avoids_RNG_W _) MU Hsbm _).
    intros a Ha Hno.
    destruct (A.ACtlG.KitMem.kitmem_not_outside _ a Hno) as (lo & hi & [E|[]] & Hr).
    injection E as <- <-. apply A.ACtlG.KitMem.kitmem_awr_win.
    unfold A.ACfn.LLVMF_STK, A.Prog.bcmp_wrap_c.BCMP_WRAP_K in *. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: kmax 2b + 1 on both cuts *)
    exact Hk.
  - (* the exit body, C_A818e8_at (ACtlCutP.v:1654-1679), at b = 0 *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A818e8_at ACtlCutP.ixn nth].
    split; [reflexivity|].
    rewrite Nat2Z.id.
    exists phi.
    split; [exact HP|].
    split; [exact HFRAC1|].
    split.
    { split; [exact Hn|]. split; [exact Hb6|]. split; [exact (conj Hphinz (Had _ _ HAphi0))|].
      split; [exact R23|]. split; [exact HOUR'|]. split; [exact (Had _ _ HOUTA)|exact HCUR]. }
    split; [reflexivity|].
    split; [exact (conj (conj Hb6 (conj HCUR (conj HOUR' (conj R23 (conj HIDB' HFGB'))))) (conj Hnz (conj R24 HF0')))|].
    split; [reflexivity|].
    split; [exact (Hspk _ _ S128 ltac:(lia) ltac:(lia))|].
    split.
    { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg & P184 & P256 & P264 &
        P272 & P32).
      split; [exact (Hspk _ _ P40 ltac:(lia) ltac:(lia))|]. split; [exact (Hspk _ _ P120 ltac:(lia) ltac:(lia))|].
      split; [exact (Hspk _ _ P136 ltac:(lia) ltac:(lia))|]. split; [exact (Hspk _ _ P160 ltac:(lia) ltac:(lia))|].
      split; [exact (Hspk _ _ P168 ltac:(lia) ltac:(lia))|]. split; [exact (Hspk _ _ P176 ltac:(lia) ltac:(lia))|].
      split; [exact (Hspk _ _ P208 ltac:(lia) ltac:(lia))|]. split; [exact (Hspk _ _ P248 ltac:(lia) ltac:(lia))|].
      split; [exact (Had _ _ Pad)|].
      split; [exact (Hbt _ _ Pin (or_introl Hinb))|].
      split; [intros Hn0; exact (Had _ _ (Pg Hn0))|].
      split; [exact (Hspk _ _ P184 ltac:(lia) ltac:(lia))|]. split; [exact (Hspk _ _ P256 ltac:(lia) ltac:(lia))|].
      split; [exact (Hspk _ _ P264 ltac:(lia) ltac:(lia))|]. split; [exact (Hspk _ _ P272 ltac:(lia) ltac:(lia))|].
      exact (Hspk _ _ P32 ltac:(lia) ltac:(lia)). }
    split; [exact (Hspk _ _ S104 ltac:(lia) ltac:(lia))|]. split; [exact (Hspk _ _ S96 ltac:(lia) ltac:(lia))|].
    split; [exact (Hspk _ _ S64 ltac:(lia) ltac:(lia))|].
    split; [exact R21|].
    split; [exact (Hspk _ _ S112 ltac:(lia) ltac:(lia))|].
    split; [exact (Hspk _ _ S144 ltac:(lia) ltac:(lia))|]. split; [exact (Hspk _ _ S192 ltac:(lia) ltac:(lia))|].
    split; [exists idb; exact (Hrw _ _ _ Hidb ltac:(lia) ltac:(lia))|].
    split; [exists j72; exact (Hrw _ _ _ Hj72 ltac:(lia) ltac:(lia))|].
    split; [exact (Hspk _ _ S280 ltac:(lia) ltac:(lia))|]. split; [exact (Hspk _ _ S240 ltac:(lia) ltac:(lia))|].
    split; [exists jy; exact (Hrw _ _ _ Hjy ltac:(lia) ltac:(lia))|].
    split; [exists j32; exact (Hrw _ _ _ Hj32 ltac:(lia) ltac:(lia))|].
    split; [exact (Hspk _ _ S152 ltac:(lia) ltac:(lia))|].
    split; [exact (Had _ _ HA38)|].
    destruct HRXS as (X48 & X56 & X88 & X80 & X72 & X8 & X0 & X200 & X216 & XA).
    split; [exact (Hspk _ _ X48 ltac:(lia) ltac:(lia))|]. split; [exact (Hspk _ _ X56 ltac:(lia) ltac:(lia))|].
    split; [exact (Hspk _ _ X88 ltac:(lia) ltac:(lia))|]. split; [exact (Hspk _ _ X80 ltac:(lia) ltac:(lia))|].
    split; [exact (Hspk _ _ X72 ltac:(lia) ltac:(lia))|]. split; [exact (Hspk _ _ X8 ltac:(lia) ltac:(lia))|].
    split; [exact (Hspk _ _ X0 ltac:(lia) ltac:(lia))|]. split; [exact (Hspk _ _ X200 ltac:(lia) ltac:(lia))|].
    split; [exact (Hspk _ _ X216 ltac:(lia) ltac:(lia))|].
    exact (Had _ _ XA).
  - (* ctl_rt_C at m' (same state ly3 S3): the cells and both shadow regions lie off the window (AsanRTFacts,
       ShadowRwOnT.shadow_rw_on_kept), ro_agree from the run's post *)
    split; [|split; [|split]].
    + apply (A.ACtlCutP.ARF.asan_cells_kept _ mem3 m' AC MU).
      cbn [LFr.disjoint_from]. split; [|exact I]. left.
      unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI, A.Prog.bcmp_wrap_c.BCMP_WRAP_K. lia.
    + exact (A.ShadowRwOnT.shadow_rw_on_kept _ mem3 m' Hcut HMK WM).
    + exact (A.ShadowRwOnT.shadow_rw_on_kept _ mem3 m' Himg HMK WM).
    + exact HRO'.
Qed.

End GlueR19.
