(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2252 of its 2377 lines of code are new or changed and 886 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R10A.v, with its numbers changed; 2171 of its 2324 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/R10.v; 643 of its 727 lines of code are new or changed and 2240 lines of the source are left out. *)
(* lib/A/ACtlG/R14.v -- GLUE for stage seg_R14 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v (at head lib/A/ACtl.v:692) (an earlier version, blob c4edf0be7fe, not in this delivery), a Theorem Labs lane's route (C) walk shell (from a working branch 8ce82d7e310)).
   Written by a Theorem Labs lane (claimed in FREE-PIECES.md (a working note, not in this delivery));
   single writer.
   rule 24: no function proved.  proves no function (kind: segment lemma).
   Pattern: glue-pattern.md sections 3, 4, 8 (a working note, not in this delivery), for a cgif-form callee,
   shape of lib/A/ACtlG/A5.v; the callee site follows a Theorem Labs lane's lib/A/ACtlG/P6.v (a working branch
   708ab9aac34), the one walk stage that already cites a cgif-form callee spec.

   WHAT IT PROVES
     glue_seg_R14 : forall POST (b : nat),
       CF POST (ix_cut C_A8183c_at [Z.of_nat b]) -> CF POST (ix_cut C_A81768_at [Z.of_nat b])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_R14.  Segment R14 (Seg/R14.v:1-27, seg_R14 :1129) is [0x81768, 0x8183c): the 32-byte sum loop from its turn i
   (b3_loop1), the low-byte test (b3_tail1), then `mv a0,s8 ; mv a1,s2 ; jal 84498 <reac_box_catalogue_match>`, whose
   return address 0x8183c IS the exit cut.

   REUSE SEARCH (rule 24, run 2026-10-29 06:1xZ on the agent VM):
     proof-index glue_seg_R14 seg_R14 r14_call r14_head reac_box_catalogue_match treac_box_catalogue_match_spec
     -> glue_seg_R14: 0 named, 0 by address, 0 related, 0 lemmas; seg_R14: 0 named, 6 lemmas (ctrl's own Seg/R14.v
        twins); r14_call / r14_head: 0 named, 8 unreleased (a Theorem Labs lane's Seg/R14F.v heads); reac_box_catalogue_match:
        4 named, 2 by address, 2 lemmas (the callee's contract files and a Theorem Labs lane's spec); treac_box_catalogue_match_spec:
        0 released, 2 unreleased (a Theorem Labs lane's cmg heads).  Index v5 built 04:26Z (f4cc67298b7, ossv/recipes
        e5e7eba2cc0), lemma index 05:56Z, cold heads 06:06Z.  No released glue of this stage exists; the pieces below
        are cited by name.
   At ossv/recipes c5e779efe8c (2026-10-31), r14_call / r14_head / treac_box_catalogue_match_spec are defined only in
   this unit (lib/A/Prog/Seg/R14.v:712 / :671, lib/A/Prog/C_reac_box_catalogue_match.v:116,
   lib/B/Prog/C_reac_box_catalogue_match.v:77).

   THE RUNS (all Required, none assumed)
   - THE HEAD AND THE LOOP: a Theorem Labs lane's A.Prog.Seg.R14F.r14_head_F (Seg/R14F.v (an earlier version, blob 3a53d57d898, not in this delivery), the glue base's blob),
     0x81768 at turn i -> 0x81830.  The loop is ALREADY composed in an _F file: r14_head_F runs B3LoopF.b3_loop1_F
     (the whole loop i .. 32, by its own induction, whole-range rng premises) and b3_tail1_F, so no in-stage loop
     induction is needed here (unlike F28a, whose loop has no _F).
   - THE CALL'S PRE STRETCH: r14g_call_pre_Fs below, the narrowed-stretch rule (glue-pattern.md section 8, P6Fs.v
     precedent): its three instructions (mv, mv, jal) read no memory, so the stretch is stated with no premise and
     PROVED here by stepping.  The base's R14F.v carries no pre / post split of r14_call (its r14_call_F takes the
     callee's contract_F, which the walk does not use), so nothing of r14_call is taken from it.
   - THE CALLEE: a Theorem Labs lane's cgif-form A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec, Required
     qualified from the glue base (lib/A/Prog/C_reac_box_catalogue_match.v 7d25cf12319 (the blob this tree had at release c5e779efe8c), a Theorem Labs lane's statement-only split,
     a working branch 43728b681c5), as the named Section hypothesis CM_SPEC.  The file states the spec only
     (no pb_ theorem), so CM_SPEC stays open.
     No post stretch: the spec's continuation returns to 0x8183c, the exit cut.

   THE PROOF
   G1  the entry cut C_A81768_at at [Z.of_nat b]: phi, the turn i, FRAC (its last conjunct the fake-frame trailer
       word, consumed), b = 0, RF.
   G2  r14_head_F's premises: the registers from the body; xs = skipn 18 (rt_g (c_in cx) 0) and its block sum from
       B3Loop / B3Rtm (as Seg/R14.v:1300-1309); the 32 bytes addressable from HB; the footprint of the 32 bytes and of
       their shadow from AR's block and shadow laws at the live block (phi, rnb cx 0) (F28a's HV1 / HV2).
   G3  the walk moved from regs3 to mkR_of regs3 (YA0nR.SRr_xregs_eqv).
   G4  the lift of head + pre stretch (r14g_head_to_call) by YA0nR.SRr_fevt at RNG_W (w_H W3): read-only.
   G5  the callee entry 0x84498: afn_pre by YCbq.afn_pre_at from the journal (CM_STK + (c_sp - sp) <= LLVMF_STK);
       its frame-pointer chain by YCbq.achain_push over the saved record [c_sp - 16, c_sp) of FRAC's saved bytes and
       the entry pre's chain (r14g_achain); the record garr8 from the block bytes, the catalogue garr8 from the
       read-only view (RELRO_CAT) and the image bytes (CM_TBL_eq); the catalogue not owned / not errno from
       CtrlTSyms' ts_owned / ts_errno; then CM_SPEC through YA0n.SRr_bind.
   G6  the exit cut C_A8183c_at at the callee's end state: the journal by YCbq.ajournal_sub (the walk's journal at the
       callee entry + the callee's own); frames / frame law / k unchanged; registers through aregs_preserved; every
       memory conjunct through the callee journal's keep clauses (the stack above sp: YCbq.v:358; the class-6 frame
       and its 392 shadow bytes: YCbq.v:364; the two live blocks: YCbq.v:360 with the post's Permutation) read at
       visible bytes; the blocks' shadow from AR's shadow law at both states; a0 = mrow by B3Rtm.a_rtm_want;
       ctl_rt_C by A.ProgWorldCtlRtC.ctl_rt_C_of_AR at the exit journal's AR.  FRAC's TRAILER at the exit,
       `q64 mem2 (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx))`: the same cx, so the same flag address, and the
       word [fr + 4088, fr + 4096) is the last word of the class-6 frame [fr, fr + 4096), which the callee journal's
       frames clause keeps (Hba_frm).

   ROUTE (C) (L3 recipe L3-recipe.md section 2 (a working note, not in this delivery)): the cut carries
   A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (ACtlCut.ctl_from).  At the entry it is NOT consumed: the stage reads every shadow
   byte it needs through AR's laws (HV2, Hbsh_keep), and the callee's cgif-form spec takes no shadow_rw premise (its
   only Hypothesis is RELRO_IMG; blob 7d25cf12319).  At the exit it is SUPPLIED by A.ProgWorldCtlRtC.ctl_rt_C_of_AR
   at the exit journal's AR, which needs neither AR_states_vis0_shadow nor AR_states_owned_ro.

   SECTION HYPOTHESES (exact text in the Section; ACtl.v discharges seg_R14 with
     glue_seg_R14 B MT XM_LIB RLO RHI RELRO_IMG RELRO_CAT LAWS TFIB_SYMS CM_SPEC)
   - RELRO_IMG, RELRO_CAT, LAWS, TFIB_SYMS, CM_SPEC: ACtl.v:219, :232, :237, :252, :322-323 (blob c4edf0be7fe), the
     same names and texts.  CM_SPEC is written over the C_ file's names (fully qualified): a Theorem Labs lane's spec at
     GLOBS := [(A_CM_TBL, CM_ROWS)] (the spec's own `In (A_CM_TBL, CM_ROWS) GLOBS` premise).

   START-UP TABLE VALUES READ (a Theorem Labs lane 06:06Z): TFIB_ERRNO = 0x5db76c and Tfib_owned_static (through A.AF0m's ts_errno /
   ts_owned), both checked against the RECORD AF0m at a working branch e56483f863b: errno equal;
   on the record's owned list no owned range meets [0x9e800, 0x9f4b8).  The proof checks that disjointness by
   computation over whichever list AF0m holds (r14g_cat_not_owned below).

   CLOSURE: every project Require names one file's directory; every use of a module that exists in several copies is
   written lib.Reusable.<X> (core), A.Reusable.<X> (ctrl's unit copy), lib.Lib.<X> or A.Prog.<X>.  No statement
   names a frame-route identifier.  Nothing is taken by path: every file but this one is the base's blob (the glue
   base with a Theorem Labs lane's route (C) shell, a working branch).

   No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI16 YM05 YO09 YI04 YI00 YO0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0i YA0n YA0nR YK04 YK0s YP09 YG00 YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0f YG0n YG0d YG0v YC5d YCbq YE01 APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v ACfn AE2k AF0m Img0 AsanRT AsanRTFacts ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlCut ACtlCutP ProgBridge KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldCtlRt ProgWorld_Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require CtrlRo CtrlFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel reac_box_catalogue_match_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_match_lib.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_box_catalogue_match.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF StepF MState Regs6ss Mem PropExec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Step Cells Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require R14F B3Loop B3Rtm Tac_rt2_b2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   1. The runs: the narrowed pre stretch of the call, and head + pre composed. *)

(* [0x81830, 0x84498): `mv a0,s8 ; mv a1,s2 ; jal 84498`, ending at the callee entry with ra = 0x8183c.  Three
   register instructions, no memory access (an instruction fetch is not an access, ExecF.v:98-101), so no premise. *)
Lemma r14g_call_pre_Fs :
  forall (RNG : lib.Lib.ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    lib.Lib.ExecF.evtF A.Img0.rsegs RNG
      (fun ms' => ms' = lib.Lib.MState.MS
                          (lib.Lib.Frame.mkR (Z_to_bv 64 0x8183c) sp gp tp t0 t1 t2 s0 s1 s8 s2 a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 A.Prog.reac_box_catalogue_match_c.REAC_BOX_CATALOGUE_MATCH) fc None m
                          (lib.Reusable.YK11.seg_rom A.Img0.rsegs))
      (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                            s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x81830) fc None m (lib.Reusable.YK11.seg_rom A.Img0.rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  (* the two YK11 copies' seg_rom have the same body (glue-pattern.md section 6); R14F steps over ctrl's *)
  change (lib.Reusable.YK11.seg_rom A.Img0.rsegs) with (A.Reusable.YK11.seg_rom A.Img0.rsegs).
  lib.Lib.StepF.step. (* 81830 mv a0,s8 *)
  lib.Lib.StepF.step. (* 81834 mv a1,s2 *)
  lib.Lib.StepF.step. (* 81838 jal 84498 <reac_box_catalogue_match> *)
  apply lib.Lib.ExecF.evtF_done. reflexivity.
Qed.

(* Head + pre stretch: r14_head_F's run to 0x81830 (taken as a premise, with its post's a1 / a2 abstracted) followed
   by the narrowed pre stretch, to the callee entry.  The loop is inside r14_head_F (B3LoopF.b3_loop1_F). *)
Lemma r14g_head_to_call :
  forall (RNG : lib.Lib.ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 v1 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z),
    lib.Lib.ExecF.evtF A.Img0.rsegs RNG
      (fun ms' => exists a4' a5' : word,
         ms' = lib.Lib.MState.MS
                 (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) v1 (Z_to_bv 64 q) (Z_to_bv 64 0) a4' a5'
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x81830) fc None m (lib.Reusable.YK11.seg_rom A.Img0.rsegs))
      (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                            s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x81768) fc None m (lib.Reusable.YK11.seg_rom A.Img0.rsegs)) ->
    lib.Lib.ExecF.evtF A.Img0.rsegs RNG
      (fun ms' => exists a4' a5' : word,
         ms' = lib.Lib.MState.MS
                 (lib.Lib.Frame.mkR (Z_to_bv 64 0x8183c) sp gp tp t0 t1 t2 s0 s1 s8 s2 (Z_to_bv 64 q) (Z_to_bv 64 0)
                    a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 A.Prog.reac_box_catalogue_match_c.REAC_BOX_CATALOGUE_MATCH) fc None m
                 (lib.Reusable.YK11.seg_rom A.Img0.rsegs))
      (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                            s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x81768) fc None m (lib.Reusable.YK11.seg_rom A.Img0.rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 v1
    F fc m q HH.
  eapply lib.Lib.ExecF.evtF_cut; [exact HH|].
  intros ms' (a4' & a5' & ->).
  eapply lib.Lib.ExecF.evtF_mono;
    [exact (r14g_call_pre_Fs RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) v1 (Z_to_bv 64 q) (Z_to_bv 64 0) a4' a5'
              a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)|].
  intros ms'' ->. exists a4', a5'. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. Memory steps (generic; over lib/Lib's mrd / bytes_at and the core's view). *)
Section Mem.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.

(* A view equality on a byte visible before the step is an mrd equality (P6.v's Hkeep). *)
Lemma r14g_mrd_keep : forall (H2 H3 : word -> bool) (m2 m3 : word -> option byte) (a : Z),
  (forall x, H2 x = true -> H3 x = true) -> H3 (Z_to_bv 64 a) = false ->
  lib.Reusable.YG0n.aview segs H2 m2 a = lib.Reusable.YG0n.aview segs H3 m3 a ->
  lib.Lib.Mem.mrd A.Img0.rsegs m2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd A.Img0.rsegs m3 (lib.Lib.Mem.wa a).
Proof.
  intros H2 H3 m2 m3 a Hle Hv3 Heq.
  assert (Hv2 : H2 (Z_to_bv 64 a) = false).
  { destruct (H2 (Z_to_bv 64 a)) eqn:E; [|reflexivity]. rewrite (Hle _ E) in Hv3. discriminate Hv3. }
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Heq.
  rewrite Hv3, Hv2 in Heq. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa.
  change (lib.Lib.PropExec.seg_rom A.Img0.rsegs (Z_to_bv 64 a)) with (lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a)).
  destruct (m2 (Z_to_bv 64 a)) as [b2|], (m3 (Z_to_bv 64 a)) as [b3|],
    (lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a)) as [b0|]; cbn [option_map] in Heq; try reflexivity;
    try discriminate Heq; injection Heq as Heq; f_equal; apply bv_eq; exact Heq.
Qed.

(* A byte the view reads is visible (a hidden byte reads None over w_Hoff; P6.v's Hvis_view). *)
Lemma r14g_vis_of_view : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) a,
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a <> None ->
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W m a Hv. destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso. apply Hv.
  pose proof (lib.Reusable.YA0n.w_Hoff W _ E) as Hn0.
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict. rewrite E.
  unfold lib.Reusable.YK11.seg_rom, memory_read. cbn [Z.of_N]. rewrite Hn0. reflexivity.
Qed.

Lemma r14g_bytes_keep : forall (m2 m3 : word -> option byte) a l,
  (forall i, (i < length l)%nat ->
     lib.Lib.Mem.mrd A.Img0.rsegs m2 (lib.Lib.Mem.wa (a + Z.of_nat i)) =
     lib.Lib.Mem.mrd A.Img0.rsegs m3 (lib.Lib.Mem.wa (a + Z.of_nat i))) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m3 a l -> lib.Lib.Mem.bytes_at A.Img0.rsegs m2 a l.
Proof.
  intros m2 m3 a l Heq (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (Heq i Hi). exact (H2 i Hi).
Qed.

Lemma r14g_addr_keep : forall (m2 m3 : word -> option byte) p n,
  (forall i, 0 <= i < n ->
     lib.Lib.Mem.mrd A.Img0.rsegs m2 (lib.Lib.Mem.wa (A.AsanRT.shadow_addr (p + i))) =
     lib.Lib.Mem.mrd A.Img0.rsegs m3 (lib.Lib.Mem.wa (A.AsanRT.shadow_addr (p + i)))) ->
  A.AsanRT.addressable m3 p n -> A.AsanRT.addressable m2 p n.
Proof.
  intros m2 m3 p n Heq (H0 & H1 & H2 & H3). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H3 i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|].
  exists b. split; [rewrite (Heq i Hi); exact Hb | exact Hok].
Qed.

(* Above the image no rom byte exists, so mrd equality is equality of the memory itself. *)
Lemma r14g_raw_of_mrd : forall (m2 m3 : word -> option byte) a, 0x5fe000 <= a < 2 ^ 64 ->
  lib.Lib.Mem.mrd A.Img0.rsegs m2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd A.Img0.rsegs m3 (lib.Lib.Mem.wa a) ->
  m2 (lib.Lib.Mem.wa a) = m3 (lib.Lib.Mem.wa a).
Proof.
  intros m2 m3 a Ha H. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa in *.
  change (lib.Lib.PropExec.seg_rom A.Img0.rsegs (Z_to_bv 64 a)) with (lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a)) in H.
  rewrite (A.ProgWorldCtlRt.seg_rom_none_high a Ha) in H.
  destruct (m2 (Z_to_bv 64 a)), (m3 (Z_to_bv 64 a)); congruence.
Qed.

Lemma r14g_rw_keep : forall (m2 m3 : word -> option byte) a (cs : list lib.Lib.Cells.cell),
  (forall i, 0 <= i < Z.of_nat (lib.Lib.Cells.cells_size cs) ->
     m2 (lib.Lib.Mem.wa (a + i)) = m3 (lib.Lib.Mem.wa (a + i))) ->
  lib.Lib.Step.rw_cells A.Img0.rsegs m3 a cs -> lib.Lib.Step.rw_cells A.Img0.rsegs m2 a cs.
Proof.
  intros m2 m3 a cs Heq ((Hwf & H0 & H1 & HB) & (W0 & W1 & HW)).
  pose proof (lib.Lib.Cells.cells_bytes_length cs Hwf) as Hlen.
  split; [split; [exact Hwf|]|].
  - split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite <- (HB i Hi). unfold lib.Lib.Mem.mrd. rewrite (Heq (Z.of_nat i)); [reflexivity|].
    rewrite Hlen in Hi. lia.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. unfold wview. rewrite (Heq i Hi). exact (HW i Hi).
Qed.

(* The view at a visible byte is mrd (a Theorem Labs lane's cm_aview_vis_mrd, restated for one byte). *)
Lemma r14g_mbyte_vis : forall (H : word -> bool) (m : word -> option byte) (x : Z), H (Z_to_bv 64 x) = false ->
  lib.Reusable.YP09.mbyte segs (lib.Reusable.YK04.mrestrict H m) x =
  lib.Lib.Mem.mrd A.Img0.rsegs m (lib.Lib.Mem.wa x).
Proof.
  intros H m x Hv. unfold lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict, lib.Lib.Mem.mrd, lib.Lib.Mem.wa.
  rewrite Hv. reflexivity.
Qed.

Lemma r14g_vm1 : forall (m : word -> option byte) (a : Z) (b : byte),
  lib.Reusable.YP09.mbyte segs m a = Some b ->
  lib.Reusable.YI04.val_mem segs m a 1 (bv_unsigned b) /\ 0 <= bv_unsigned b < 256.
Proof.
  intros m a b H. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  split; [|exact R].
  intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal.
  unfold lib.Reusable.YO0f.le_byte, lib.Reusable.YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
  rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
  symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* bytes_at over visible bytes gives the core's garr8 over the restricted memory. *)
Lemma r14g_garr8_of_bytes : forall (H : word -> bool) (m : word -> option byte) (a : Z) (bs : list byte),
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a bs ->
  (forall j, (j < length bs)%nat -> H (Z_to_bv 64 (a + Z.of_nat j)) = false) ->
  lib.Reusable.YI00.garr8 segs (lib.Reusable.YK04.mrestrict H m) a (map (fun b : byte => bv_unsigned b) bs).
Proof.
  intros H m a bs (_ & _ & Hb) Hv j Hj. rewrite length_map in Hj.
  destruct (nth_error bs j) as [b|] eqn:Ej; [|apply nth_error_None in Ej; lia].
  replace (nth j (map (fun b0 : byte => bv_unsigned b0) bs) 0) with (bv_unsigned b)
    by (symmetry; apply nth_error_nth; rewrite nth_error_map, Ej; reflexivity).
  apply r14g_vm1. rewrite (r14g_mbyte_vis H m _ (Hv j Hj)). rewrite (Hb j Hj). exact Ej.
Qed.

(* An le8 word at visible bytes is the view's rdword (KindBGlue.bytes_at_le8_word, CtrlFrame.rdword_of_val_mem). *)
Lemma r14g_rdword : forall (H : word -> bool) (m : word -> option byte) (a : Z) (w : word),
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a (lib.Lib.Mem.le8 w) ->
  (forall k, (k < 8)%nat -> H (Z_to_bv 64 (a + Z.of_nat k)) = false) ->
  lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview segs H m) a = Some (bv_unsigned w).
Proof.
  intros H m a w Hb Hv.
  apply A.Prog.CtrlFrame.rdword_of_val_mem;
    [|pose proof (bv_unsigned_in_range 64 w) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R].
  pose proof (A.KindBGlue.bytes_at_le8_word A.Img0.rsegs m a w Hb) as Hw.
  intros k Hk. rewrite (r14g_mbyte_vis H m _ (Hv k Hk)). exact (Hw k Hk).
Qed.

(* The bytes image_bytes reads are the rom's. *)
Lemma r14g_image_nth : forall n A0 bs, lib.Lib.Image.image_bytes A.Img0.rsegs A0 n = Some bs ->
  forall j, (j < n)%nat ->
  lib.Lib.PropExec.seg_rom A.Img0.rsegs (lib.Lib.Mem.wa (A0 + Z.of_nat j)) = nth_error bs j.
Proof.
  induction n as [|n IH]; intros A0 bs H j Hj; [lia|].
  cbn [lib.Lib.Image.image_bytes] in H.
  destruct (lib.Lib.Image.image_bytes A.Img0.rsegs (A0 + 1) n) as [bs'|] eqn:E1;
    [|match type of H with context [match ?r with Some _ => _ | None => _ end] => destruct r; discriminate H end].
  match type of H with context [match ?r with Some _ => _ | None => _ end] => destruct r as [b|] eqn:E0 end;
    [|discriminate H].
  injection H as <-. destruct j as [|j].
  - rewrite Z.add_0_r. exact E0.
  - cbn [nth_error]. replace (A0 + Z.of_nat (S j)) with (A0 + 1 + Z.of_nat j) by lia. exact (IH _ _ E1 j ltac:(lia)).
Qed.

(* The callee's frame-pointer chain: the caller's saved record at [sp0 - 16, sp0) on top of the entry chain
   (YCbq.achain_push), or the empty chain when sp0 is the layout's top frame. *)
Lemma r14g_achain : forall (ly ly' : lib.Reusable.YG0f.alayout) (rd rd' : lib.Reusable.YG0f.reader)
    (sp0 sp v ra : Z) (ch : list (Z * Z * Z)),
  lib.Reusable.YCbq.achain ly rd sp0 v ch -> lib.Reusable.YG0f.ly_top ly' = lib.Reusable.YG0f.ly_top ly ->
  lib.Reusable.YG0f.ly_top ly <= 2 ^ 64 ->
  (forall a, sp0 <= a < 2 ^ 64 -> rd' a = rd a) ->
  lib.Reusable.YG0d.rdword rd' (sp0 - 8) = Some ra -> lib.Reusable.YG0d.rdword rd' (sp0 - 16) = Some v ->
  4096 <= ra -> lib.Reusable.YM05.alloc_ceiling <= sp0 -> sp0 mod 8 = 0 -> sp + 16 <= sp0 ->
  exists ch', lib.Reusable.YCbq.achain ly' rd' sp sp0 ch'.
Proof.
  intros ly ly' rd rd' sp0 sp v ra ch Hc Etop Htop Hk H8 H16 Hra Hceil Hal Hsp.
  destruct (Z_lt_le_dec sp0 (lib.Reusable.YG0f.ly_top ly - 16)) as [Hlt | Hge].
  - exists ((sp0, ra, v) :: ch).
    apply (lib.Reusable.YCbq.achain_ly_top ly ly'); [exact Etop|].
    exact (lib.Reusable.YCbq.achain_push ly rd rd' sp0 v ra ch sp Hc Htop Hk H8 H16 Hra Hceil Hal Hlt Hsp).
  - exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

End Mem.

(* ---------------------------------------------------------------------------------------------------------
   3. The stage. *)
Section GlueR14.

(* ACtl.v's Section shape (ACtl.v:210-214, blob c4edf0be7fe, the core classes), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:373, :377-378, :401, :404), verbatim up to the module path. *)
Local Notation ix_cut := A.ACtlCut.ix_cut.
Local Notation CF POST X :=
  (A.ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81768_at := (A.ACtlCutP.C_A81768_at B).
Local Notation C_A8183c_at := (A.ACtlCutP.C_A8183c_at B).

(* ---- Section hypotheses (sources in the header).  RELRO_IMG, RELRO_CAT, LAWS, TFIB_SYMS are ACtl.v's lines
   byte for byte; Reusable.YG0d has one copy (lib/Reusable/YG0d.v), so the partial name is the core's. ---- *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis RELRO_CAT : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis CM_SPEC : A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI [(A.Prog.C_reac_box_catalogue_match.A_CM_TBL, A.Prog.C_reac_box_catalogue_match.CM_ROWS)].

(* RELRO_CAT at the catalogue's size (SlotModel.v:40-41: 11 rows of 296 bytes). *)
Lemma r14g_relro_cat : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + 3256 <= RHI.
Proof. pose proof RELRO_CAT as (H1 & H2). unfold A.Prog.SlotModel.CAT_N, A.Prog.SlotModel.CAT_ROW in H2. lia. Qed.

Lemma r14g_arodataP : forall rd, lib.Reusable.YE01.arodata_okS segs B RLO RHI rd ->
  lib.Reusable.APostBase.arodata_okP segs RLO RHI B rd.
Proof. intros rd H a Ha. apply H. destruct Ha as [Ha|Ha]; [left; exact Ha | right; lia]. Qed.

(* The catalogue [CAT, CAT + 3256) is not an owned static (checked by computation over AF0m's list) and not errno. *)
Lemma r14g_cat_not_owned : forall a, A.Prog.SlotModel.CAT <= a < A.Prog.SlotModel.CAT + 3256 ->
  ~ Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.as_owned_static B).
Proof.
  intros a Ha HE.
  assert (Hdisj : forallb (fun r => (fst r + snd r <=? A.Prog.SlotModel.CAT) || (A.Prog.SlotModel.CAT + 3256 <=? fst r))
                    A.AF0m.Tfib_owned_static = true) by (vm_compute; reflexivity).
  rewrite (A.AF0m.ts_owned B TFIB_SYMS) in HE.
  apply Exists_exists in HE as ([lo len] & Hr & Hz).
  pose proof (proj1 (forallb_forall _ _) Hdisj (lo, len) Hr) as Hb. cbn [fst snd] in Hb.
  unfold lib.Reusable.YG0n.in_zr in Hz. cbn [fst snd] in Hz.
  apply Bool.orb_true_iff in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

Lemma r14g_cat_not_errno : forall a, A.Prog.SlotModel.CAT <= a < A.Prog.SlotModel.CAT + 3256 ->
  ~ (lib.Reusable.YG0f.as_errno B <= a < lib.Reusable.YG0f.as_errno B + 4).
Proof.
  intros a Ha. rewrite (A.AF0m.ts_errno B TFIB_SYMS). unfold A.AF0m.TFIB_ERRNO, A.Prog.SlotModel.CAT in *. lia.
Qed.

Lemma r14g_tbl_eq : A.Prog.C_reac_box_catalogue_match.A_CM_TBL = A.Prog.SlotModel.CAT.
Proof. vm_compute. reflexivity. Qed.

Lemma r14g_pc_eq : A.Prog.C_reac_box_catalogue_match.A_catalogue_matchP = 0x84498.
Proof. vm_compute. reflexivity. Qed.

(* The catalogue rows in the restricted memory, from the read-only view (RELRO_CAT) and the image bytes. *)
Lemma r14g_tbl_garr8 : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte),
  lib.Reusable.YE01.arodata_okS segs B RLO RHI (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) ->
  lib.Reusable.YI00.garr8 segs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) m)
    A.Prog.C_reac_box_catalogue_match.A_CM_TBL A.Prog.C_reac_box_catalogue_match.CM_TBLZ.
Proof.
  intros W m HRO. rewrite r14g_tbl_eq. unfold A.Prog.C_reac_box_catalogue_match.CM_TBLZ. intros j Hj.
  rewrite length_map, A.Prog.reac_box_catalogue_match_lib.CM_TBL_len in Hj.
  pose proof (r14g_image_nth 3256 _ _ A.Prog.reac_box_catalogue_match_lib.CM_TBL_eq j Hj) as Hrom.
  destruct (nth_error A.Prog.reac_box_catalogue_match_lib.CM_TBL j) as [b|] eqn:Eb;
    [|apply nth_error_None in Eb; rewrite A.Prog.reac_box_catalogue_match_lib.CM_TBL_len in Eb; lia].
  replace (nth j (map (fun b0 : byte => bv_unsigned b0) A.Prog.reac_box_catalogue_match_lib.CM_TBL) 0)
    with (bv_unsigned b) by (symmetry; apply nth_error_nth; rewrite nth_error_map, Eb; reflexivity).
  apply r14g_vm1.
  assert (Ha : A.Prog.SlotModel.CAT <= A.Prog.SlotModel.CAT + Z.of_nat j < A.Prog.SlotModel.CAT + 3256) by lia.
  assert (Hrl : RLO <= A.Prog.SlotModel.CAT + Z.of_nat j < RHI) by (pose proof r14g_relro_cat; lia).
  pose proof (HRO (A.Prog.SlotModel.CAT + Z.of_nat j)
                (or_intror Hrl) (r14g_cat_not_owned _ Ha) (r14g_cat_not_errno _ Ha)) as Hv.
  assert (Hr : lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 (A.Prog.SlotModel.CAT + Z.of_nat j)) = Some b).
  { exact Hrom. }
  unfold lib.Reusable.YG0n.aview in Hv. rewrite Hr in Hv. cbn [option_map] in Hv.
  destruct (lib.Reusable.YP09.mbyte segs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) m)
              (A.Prog.SlotModel.CAT + Z.of_nat j)) as [b'|] eqn:E; cbn [option_map] in Hv; [|discriminate Hv].
  injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.

(* The statement after the colon is ACtl.v:677's `Hypothesis seg_R14 :` text byte for byte (blob c4edf0be7fe). *)
Lemma glue_seg_R14 : forall POST (b : nat), CF POST (ix_cut C_A8183c_at [Z.of_nat b]) -> CF POST (ix_cut C_A81768_at [Z.of_nat b]).
Proof.
  intros POST b HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* ---- G1: the entry cut at index [Z.of_nat b] (ACtlCutP.v:1467-1496) ---- *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCutP.C_A81768_at A.ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & i & HP & HFRAC & (Hcn & Hb6 & HHB & R23 & HOUR & HOUTA & HCUR & Hi32 & R10 & R12 & R13) &
    Hb0 & Hi & R11 & HRF & S112 & S8 & S0 & S200 & S216 & A2528 & S128 & HPRO & S104 & S96 & S64 & R21 & S144 &
    S192 & HIDB & HJNK & S280 & S240 & HJY & HJNK2 & S152 & A2176 & HRXS).
  subst b. change (Z.of_nat 0) with 0 in *.
  (* the model facts of turn 0 (Seg/R14.v:1141-1145) *)
  pose proof HRF as (HRFb & R18).
  pose proof HRFb as (HRB & Hnz & R24 & HFb).
  change (Z.of_nat 0) with 0 in HFb.
  destruct (A.Prog.Seg.Tac_rt2_b2.a_rtn (A.ACtlCut.c_in cx) 0 Hnz) as (_ & Hnb & HLF).
  set (n0 := A.ACtlCutP.rnb cx 0) in *.
  change (A.Prog.SlotModel.rt_n (A.ACtlCut.c_in cx) 0) with n0 in Hnb, HLF.
  (* FRAC: its tail is the saved registers and the fake-frame trailer word at fr + 4088 *)
  destruct HFRAC as (A & sp & R2 & Hsp16 & EspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAc & HspA &
    HfrA & HA416 & Hsp4096 & HcAPP & Q304 & Q24 & Q16 & QH0 & QH16 & (sh & Hsh & Hshlen) & HSAVED & HTRL).
  unfold A.ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in HcAPP.
  (* the journal, the base *)
  pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & Hnev3 & Hk0 & F1j & _ & F3j & _ & _ & Fwin3 & Hastk3 & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & _).
  pose proof Hastk3 as (Hcsp16 & _ & Hceil & Hstklo & _ & Hhi47 & _ & _ & Htop).
  unfold A.ACfn.LLVMF_STK in Fwin3, Hstklo, F1j.
  pose proof HB as ((HAFN & _ & _ & _ & Hblk0 & Hnlen & _ & _ & Hnev0 & _ & HROS0 & _) & _).
  pose proof HAFN as (_ & _ & _ & Hgp0 & _ & _ & _ & Hch0 & _).
  assert (Hk1 : k <= 1) by exact Hk.
  assert (Hin6 : In (6, A.ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = lib.Reusable.YG0f.frame_addr (A.ACtlCut.c_ly cx) 6 (A.ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : lib.Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold lib.Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  assert (Hsp0 : 0 <= sp) by (rewrite <- EspZ; unfold lib.Reusable.YG0d.spZ; apply bv_unsigned_in_range).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as Hceilv.
  (* the live block (phi, n0): AR's block and shadow laws *)
  assert (Hinphi : In (phi, n0) (lib.Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  assert (Ers : lib.Reusable.YG00.req_size n0 = n0).
  { unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec n0 0); lia. }
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi n0 HAR3 Hinphi)
    as (_ & Hp4096 & _ & Happphi & Hpresphi & _).
  destruct (lib.Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 phi n0 HAR3 Hinphi) as (_ & Hhull).
  rewrite Ers in Happphi, Hpresphi, Hhull.
  destruct (A.ProgWorldCtlRt.in_app_bounds _ _ Happphi) as (_ & Hphitop).
  (* ---- G2: r14_head_F's premises ---- *)
  assert (HFb50 : (50 <= length (A.Prog.SlotModel.rt_F (A.ACtlCut.c_in cx) 0))%nat) by lia.
  destruct (A.Prog.Seg.B3Loop.b3_blk_at mem3 phi _ HFb ltac:(exact HFb50)) as (HBL & HBLlen).
  rewrite <- (A.Prog.Seg.B3Loop.b3_rt_g (A.ACtlCut.c_in cx) 0) in HBL, HBLlen.
  pose proof (A.Prog.Seg.B3Rtm.a_rtm_sum (A.ACtlCut.c_in cx) 0 ltac:(lia)) as HSUM.
  assert (HA18 : A.AsanRT.addressable mem3 (phi + 18) 32).
  { destruct HHB as (_ & Hadd). unfold A.ACtlK.a_size in Hadd.
    apply (A.AsanRTFacts.addressable_sub mem3 phi (Z.max n0 1) 18 32 Hadd); lia. }
  assert (HV1 : lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) (phi + 18) 32).
  { apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
    intros a Ha. destruct (Hpresphi a ltac:(lia)) as ((Hv & _) & _). exact Hv. }
  assert (HV2 : lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3))
                  ((phi + 18) / 8 + A.AsanRT.ASAN_K) ((phi + 49) / 8 - (phi + 18) / 8 + 1)).
  { apply A.ProgBridge.rng_of_visible. unfold A.AsanRT.ASAN_K.
    assert (D0 : 0 <= (phi + 18) / 8) by (apply Z.div_pos; lia).
    assert (D1 : (phi + 18) / 8 <= (phi + 49) / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : (phi + 49) / 8 <= phi / 8 + 7) by (Z.div_mod_to_equations; lia).
    assert (D3 : (phi + 49) / 8 <= phi + 49) by (Z.div_mod_to_equations; lia).
    split; [lia|]. split; [lia|].
    intros s Hs. apply (r14g_vis_of_view W3 mem3). apply (Hhull s).
    unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
    assert (M1 : phi / 8 <= (phi + 18) / 8) by (apply Z.div_le_mono; lia).
    assert (M2 : (phi + 49) / 8 <= (phi + n0 - 1) / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.mul_div_le (0x7fff8000 + phi / 8) 8 ltac:(lia)) as M3.
    pose proof (Z.mod_pos_bound (0x7fff8000 + (phi + n0 - 1) / 8) 8 ltac:(lia)) as M4.
    pose proof (Z.div_mod (0x7fff8000 + (phi + n0 - 1) / 8) 8 ltac:(lia)) as M5.
    lia. }
  (* ---- G3: the cut's configuration in the run's state form, the walk moved to mkR_of regs3 ---- *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (A.ACtlCut.cut_pc (ix_cut C_A81768_at [0])) with 0x81768.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x81768) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold lib.Lib.Regs6ss.mkR_of.
  (* ---- G4: head (with the loop) + narrowed pre stretch, lifted at RNG_W (w_H W3); read-only ---- *)
  eapply (lib.Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3
            (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3))).
  { apply A.ProgBridge.fevt_of_evtF.
    eapply r14g_head_to_call.
    change (lib.Reusable.YK11.seg_rom A.Img0.rsegs) with (A.Reusable.YK11.seg_rom A.Img0.rsegs).
    apply (A.Prog.Seg.R14F.r14_head_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ phi
             (skipn 18 (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) 0)) i);
      [exact R10 | exact R11 | exact R12 | exact R13 | exact R26 | exact Hi | exact HBLlen | exact HBL
      | exact HA18 | exact HSUM | exact HV1 | exact HV2]. }
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  intros ms' md' Hms Hsbm. cbv beta in Hms. destruct Hms as (a4' & a5' & ->).
  (* ---- G5: the callee entry 0x84498 ---- *)
  match goal with |- context [lib.Lib.MState.MS ?R _ _ _ _ _ _] => set (R' := R) end.
  assert (EspR : lib.Reusable.YG0d.spZ R' = sp) by exact EspZ.
  assert (Es0R : lib.Reusable.YG0d.s0Z R' = A.ACtlCut.c_sp cx).
  { unfold lib.Reusable.YG0d.s0Z. change (lib.Reusable.YK11.getr R' 8) with (lib.Reusable.YK11.getr regs3 8).
    unfold A.ACtlCut.rgv in R8. rewrite R8. apply lib.Lib.MState.unsigned_lit. unfold A.AsanRT.APPMEM_END in *. lia. }
  (* the walk's journal at the callee entry: no byte written, the model materialized *)
  assert (HJe : lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx)
                  [] (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx)
                  (A.ACtlCut.c_md cx) (A.ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k).
  { eapply (lib.Reusable.YCbq.ajournal_exec (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha]. }
  (* the read-only view along any journal from the entry (FP = []; P6.v's Hro_keep) *)
  assert (Hro_keep : forall lyj Sj (Wj : lib.Reusable.YA0n.world segs) memj mdj ownj kj,
            lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) []
              (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx)
              ownj lyj Sj Wj memj mdj kj ->
            lib.Reusable.YE01.arodata_okS segs B RLO RHI
              (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H Wj) memj)).
  { intros lyj Sj Wj memj mdj ownj kj HJ' a Hro Ho He.
    pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
    rewrite (F3 a); [exact (HROS0 a Hro Ho He) | | exact Ho | exact He |].
    - destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr] |].
      exact (RELRO_IMG a Hgot).
    - apply (lib.Reusable.YCbq.fp_spares_closed (SK := A.AE2k.tfib_sink_head)). intros Ho'.
      exact (lib.Reusable.YCbq.sink_closed_nil Ho'). }
  pose proof (Hro_keep _ _ _ _ _ _ _ HJe) as HRO3.
  (* the visible stack window [c_sp - LLVMF_STK, c_sp) *)
  assert (Hvis_win : forall a, A.ACtlCut.c_sp cx - 32768 <= a < A.ACtlCut.c_sp cx ->
            lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha. exact (proj1 (Fwin3 a Ha)). }
  (* the saved record of the caller at [c_sp - 16, c_sp) (FRAC's saved bytes: ..., s0, ra) *)
  pose proof HSAVED as HSV. unfold A.ACtlCutP.saved_bytes in HSV. rewrite !app_assoc in HSV.
  apply lib.Lib.Mem.bytes_at_app in HSV as (HSV1 & HSVra).
  apply lib.Lib.Mem.bytes_at_app in HSV1 as (_ & HSVs0).
  repeat rewrite length_app in HSVra. repeat rewrite length_app in HSVs0.
  repeat rewrite lib.Lib.Mem.length_le8 in HSVra. repeat rewrite lib.Lib.Mem.length_le8 in HSVs0.
  match type of HSVra with lib.Lib.Mem.bytes_at _ _ ?x _ =>
    replace x with (A.ACtlCut.c_sp cx - 8) in HSVra by lia end.
  match type of HSVs0 with lib.Lib.Mem.bytes_at _ _ ?x _ =>
    replace x with (A.ACtlCut.c_sp cx - 16) in HSVs0 by lia end.
  assert (Hrd8 : lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) mem3)
                   (A.ACtlCut.c_sp cx - 8) = Some A.ACfn.RA_LLVMF).
  { rewrite (r14g_rdword _ mem3 _ _ HSVra); [| intros k' Hk'; apply Hvis_win; lia].
    rewrite lib.Lib.MState.unsigned_lit; [reflexivity | unfold A.ACfn.RA_LLVMF; lia]. }
  assert (Hrd16 : lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) mem3)
                    (A.ACtlCut.c_sp cx - 16) = Some (lib.Reusable.YG0d.s0Z (A.ACtlCut.c_regs cx))).
  { rewrite (r14g_rdword _ mem3 _ _ HSVs0); [reflexivity | intros k' Hk'; apply Hvis_win; lia]. }
  destruct (r14g_achain (A.ACtlCut.c_ly cx) ly3
              (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H (A.ACtlCut.c_W cx)) (A.ACtlCut.c_mem cx))
              (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) mem3)
              (A.ACtlCut.c_sp cx) sp (lib.Reusable.YG0d.s0Z (A.ACtlCut.c_regs cx)) A.ACfn.RA_LLVMF [] Hch0 Etop
              ltac:(lia) ltac:(intros a Ha; apply F1j; lia) Hrd8 Hrd16 ltac:(unfold A.ACfn.RA_LLVMF; lia)
              ltac:(lia) ltac:(revert Hcsp16; clear; Z.div_mod_to_equations; lia) ltac:(lia))
    as (ch1 & Hch1).
  assert (HPRE : lib.Reusable.YCbq.afn_pre segs B A.Prog.C_reac_box_catalogue_match.CM_STK ly3 S3 W3 R' mem3 md' ch1).
  { apply (lib.Reusable.YCbq.afn_pre_at (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) []
             (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx)
             (A.ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k R' A.Prog.C_reac_box_catalogue_match.CM_STK
             (sp - A.ACtlCut.c_sp cx) ch1 HJe).
    - rewrite EspR. lia.
    - rewrite Zminus_mod, Hsp16, Hcsp16. reflexivity.
    - lia.
    - unfold A.Prog.C_reac_box_catalogue_match.CM_STK. lia.
    - unfold A.Prog.C_reac_box_catalogue_match.CM_STK, A.ACfn.LLVMF_STK. lia.
    - reflexivity.
    - match goal with |- 4096 <= ?x => assert (Ex : x = 0x8183c) by reflexivity; rewrite Ex; lia end.
    - exact (eq_trans R3 Hgp0).
    - exact R4.
    - rewrite EspR, Es0R. exact Hch1. }
  (* the callee's spec at the entry, through SRr_bind *)
  change (lib.Reusable.YA0n.SRr segs W3 (lib.Reusable.YG0d.cfg_at segs 0x84498 R' mem3 md') (POST cx)).
  pose proof (CM_SPEC ly3 S3 W3 R' mem3 md' ch1 phi n0 (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) 0) HPRE HRO3)
    as HR.
  rewrite r14g_pc_eq in HR.
  (* the 50 record bytes (Seg/R14.v:1300-1303) *)
  assert (HFB : lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 phi (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) 0)).
  { rewrite (A.Prog.Seg.B3Loop.b3_rt_g (A.ACtlCut.c_in cx) 0).
    rewrite (A.Prog.Seg.B3Loop.b3_fr50_eq (A.Prog.SlotModel.rt_F (A.ACtlCut.c_in cx) 0) HFb50).
    pose proof HFb as HF'. rewrite <- (firstn_skipn 50 (A.Prog.SlotModel.rt_F (A.ACtlCut.c_in cx) 0)) in HF'.
    exact (proj1 (proj1 (lib.Lib.Mem.bytes_at_app A.Img0.rsegs mem3 phi _ _) HF')). }
  assert (Lg : length (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) 0) = 50%nat)
    by apply A.Prog.SlotModel.fr50_length.
  eapply (lib.Reusable.YA0n.SRr_bind segs W3 _ _ (POST cx)).
  { apply HR.
    - exact R24.
    - exact R18.
    - lia.
    - lia.
    - exact Lg.
    - intros _. exists n0. split; [exact Hinphi | rewrite Ers; lia].
    - intros _. apply r14g_garr8_of_bytes; [exact HFB|].
      intros j Hj. rewrite Lg in Hj.
      destruct (Hpresphi (phi + Z.of_nat j) ltac:(lia)) as ((Hv & _) & _). exact Hv.
    - exact (r14g_tbl_garr8 W3 mem3 HRO3).
    - left. reflexivity.
    - rewrite r14g_tbl_eq. unfold A.Prog.CtrlRo.IMG_LO, A.Prog.SlotModel.CAT. lia.
    - rewrite r14g_tbl_eq.
      unfold A.Prog.CtrlRo.IMG_HI, A.Prog.SlotModel.CAT, A.Prog.C_reac_box_catalogue_match.CM_ROWS. lia.
    - intros a Ha. rewrite r14g_tbl_eq in Ha. unfold A.Prog.C_reac_box_catalogue_match.CM_ROWS in Ha.
      split; [right; pose proof r14g_relro_cat; lia|].
      split; [exact (r14g_cat_not_owned a Ha) | exact (r14g_cat_not_errno a Ha)].
    - rewrite HF. vm_compute. reflexivity.
    - rewrite HF. vm_compute. reflexivity.
    - rewrite HF. vm_compute. reflexivity.
    - unfold A.Prog.C_reac_box_catalogue_match.EV_CM. unfold A.ACfn.EV_LIB in Hnev0. lia.
    - unfold A.Prog.C_reac_box_catalogue_match.LIVE_CM. rewrite Z.add_0_r.
      exact (lib.Reusable.YG01.wf_live _ _ _ _ _ (lib.Reusable.YG0n.am_wf _ _ _ _ (proj1 HAR3))). }
  (* ---- G6: the exit cut 0x8183c at the callee's end state ---- *)
  intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & HAP & H10' & HPERM).
  subst c2.
  assert (Hle : forall x, lib.Reusable.YA0n.w_H W2 x = true -> lib.Reusable.YA0n.w_H W3 x = true) by exact Hwle.
  change (lib.Reusable.YA0n.SRr segs W2
            (lib.Reusable.YG0d.cfg_at segs (A.ACtlCut.cut_pc (ix_cut C_A8183c_at [0])) regs2 mem2 md2)
            (POST cx)).
  pose proof HJ2 as (HAR2 & _ & _ & _ & _ & Hfr2 & _ & _ & F1c & F2c & _ & F4c & _).
  rewrite EspR in F1c. unfold A.Prog.C_reac_box_catalogue_match.CM_STK in F1c.
  (* the walk's journal at the exit: the entry's to the callee entry, then the callee's own (YCbq.ajournal_sub) *)
  assert (HJx : lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx)
                  [] (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx)
                  (A.ACtlCut.c_md cx) ([] ++ A.ACtlCut.own6 cx) ly2 S2 W2 mem2 md2
                  (k + A.Prog.C_reac_box_catalogue_match.EV_CM)).
  { eapply (lib.Reusable.YCbq.ajournal_sub (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low);
      [exact HJe | exact HJ2 | | | ].
    - rewrite EspR. unfold A.ACfn.LLVMF_STK, A.Prog.C_reac_box_catalogue_match.CM_STK. lia.
    - rewrite EspR. lia.
    - intros a Ha. exfalso. exact (lib.Reusable.YI04.inFP_nil _ Ha). }
  cbn [app] in HJx. unfold A.Prog.C_reac_box_catalogue_match.EV_CM in HJx. rewrite Z.add_0_r in HJx.
  (* the registers the exit cut reads: callee-saved, so the entry's *)
  assert (K2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
    by exact (HAP 2 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
    by exact (HAP 3 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
    by exact (HAP 4 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
    by exact (HAP 8 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
    by exact (HAP 9 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
    by exact (HAP 19 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K21 : lib.Reusable.YK11.getr regs2 21 = lib.Reusable.YK11.getr regs3 21)
    by exact (HAP 21 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
    by exact (HAP 22 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
    by exact (HAP 23 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K24 : lib.Reusable.YK11.getr regs2 24 = lib.Reusable.YK11.getr regs3 24)
    by exact (HAP 24 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
    by exact (HAP 25 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
    by exact (HAP 26 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  (* memory: the stack above sp (the callee's window is below it), visible and kept (YCbq.v:358) *)
  assert (Hstk : forall a, sp <= a < A.ACtlCut.c_sp cx ->
            lib.Lib.Mem.mrd A.Img0.rsegs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd A.Img0.rsegs mem3 (lib.Lib.Mem.wa a)).
  { intros a Ha. apply (r14g_mrd_keep _ _ mem2 mem3 a Hle); [apply Hvis_win; lia|].
    apply F1c; lia. }
  (* the class-6 frame and its shadow: visible (AR's frames law), kept by the frames clause (YCbq.v:364) *)
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR3 Hin6)
    as (_ & _ & Hfbytes & Hfshadow).
  rewrite Efr3 in Hfbytes, Hfshadow.
  change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfbytes, Hfshadow.
  assert (Hfr_hi : 0x5fe000 <= fr).
  { rewrite <- Efr3. exact (A.ProgWorld_Fs.ctl_frame_above_img B ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR3 Hin6). }
  assert (Hfrm : forall a, fr <= a < fr + 4096 ->
            lib.Lib.Mem.mrd A.Img0.rsegs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd A.Img0.rsegs mem3 (lib.Lib.Mem.wa a)).
  { intros a Ha. apply (r14g_mrd_keep _ _ mem2 mem3 a Hle (proj1 (proj1 (Hfbytes a Ha)))).
    apply (F4c 6 (A.ACtlCut.c_fpos cx)); [exact Hin6 | | exact (lib.Reusable.YI04.inFP_nil _)].
    left. unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite Efr3.
    change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096. lia. }
  assert (Hfsh : forall i, 0 <= i < 512 ->
            lib.Lib.Mem.mrd A.Img0.rsegs mem2 (lib.Lib.Mem.wa (A.ACtlCutP.Sfr fr + i)) =
            lib.Lib.Mem.mrd A.Img0.rsegs mem3 (lib.Lib.Mem.wa (A.ACtlCutP.Sfr fr + i))).
  { intros ii Hii.
    assert (ES : A.ACtlCutP.Sfr fr + ii = lib.Reusable.YG0f.shadow_addr fr + ii)
      by (unfold A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, lib.Reusable.YG0f.shadow_addr, A.AsanRT.ASAN_K,
            lib.Reusable.YG0f.SHADOW_OFF; lia).
    rewrite ES. apply (r14g_mrd_keep _ _ mem2 mem3 _ Hle (proj1 (proj1 (Hfshadow ii Hii)))).
    apply (F4c 6 (A.ACtlCut.c_fpos cx)); [exact Hin6 | | exact (lib.Reusable.YI04.inFP_nil _)].
    right. unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3.
    change (lib.Reusable.YG00.fs_frame_bytes 6 / 8) with 512. lia. }
  assert (Hsh_of : forall x, 0 <= x < 3136 ->
            exists i, 0 <= i < 512 /\ A.AsanRT.shadow_addr (fr + x) = A.ACtlCutP.Sfr fr + i).
  { intros x Hx. exists (A.AsanRT.shadow_addr (fr + x) - A.ACtlCutP.Sfr fr). split; [| lia].
    unfold A.ACtlCutP.Sfr, A.AsanRT.shadow_addr. Z.div_mod_to_equations. lia. }
  assert (Hba_frm : forall off l, 0 <= off -> off + Z.of_nat (length l) <= 4096 ->
            lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 (fr + off) l -> lib.Lib.Mem.bytes_at A.Img0.rsegs mem2 (fr + off) l).
  { intros off l Ho Hl. apply r14g_bytes_keep. intros j Hj. rewrite <- Z.add_assoc. apply Hfrm. lia. }
  assert (Had_frm : forall off n, 0 <= off -> off + n <= 3136 ->
            A.AsanRT.addressable mem3 (fr + off) n -> A.AsanRT.addressable mem2 (fr + off) n).
  { intros off n Ho Hl. apply r14g_addr_keep. intros j Hj.
    destruct (Hsh_of (off + j) ltac:(lia)) as (j' & Hj' & Ej). rewrite <- Z.add_assoc, Ej.
    exact (Hfsh j' Hj'). }
  assert (Hrw_frm : forall off cs, 0 <= off -> off + Z.of_nat (lib.Lib.Cells.cells_size cs) <= 4096 ->
            lib.Lib.Step.rw_cells A.Img0.rsegs mem3 (fr + off) cs ->
            lib.Lib.Step.rw_cells A.Img0.rsegs mem2 (fr + off) cs).
  { intros off cs Ho Hl. apply r14g_rw_keep. intros j Hj. rewrite <- Z.add_assoc.
    apply r14g_raw_of_mrd; [lia | apply Hfrm; lia]. }
  assert (Hba_stk : forall a l, sp <= a -> a + Z.of_nat (length l) <= A.ACtlCut.c_sp cx ->
            lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 a l -> lib.Lib.Mem.bytes_at A.Img0.rsegs mem2 a l).
  { intros a l Ha Hl. apply r14g_bytes_keep. intros j Hj. apply Hstk. lia. }
  assert (Hsp : forall off v, 0 <= off <= 304 ->
            A.ACtlCutP.spill regs3 mem3 off v -> A.ACtlCutP.spill regs2 mem2 off v).
  { intros off v Hoff (A' & R9' & Hq). exists A. split; [unfold A.ACtlCut.rgv; rewrite K9; exact R9 |].
    assert (EA : A' = A).
    { pose proof Hq as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1.
      unfold A.ACtlCut.rgv in R9, R9'. rewrite R9 in R9'.
      apply (f_equal bv_unsigned) in R9'. rewrite !Z_to_bv_unsigned in R9'. unfold bv_wrap in R9'.
      change (bv_modulus 64) with (2 ^ 64) in R9'. rewrite (Z.mod_small A) in R9' by lia.
      Z.div_mod_to_equations. lia. }
    subst A'. apply Hba_stk; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact Hq]. }
  (* the two live blocks of the body: their bytes (YCbq.v:360) and shadow (AR's shadow law at both states) *)
  assert (Hblk_keep : forall p n, In (p, n) (lib.Reusable.YG0d.ablocks B ly3 S3) -> 0 < n ->
            forall j, 0 <= j < n ->
            lib.Lib.Mem.mrd A.Img0.rsegs mem2 (lib.Lib.Mem.wa (p + j)) =
            lib.Lib.Mem.mrd A.Img0.rsegs mem3 (lib.Lib.Mem.wa (p + j))).
  { intros p n Hin3 Hn j Hj.
    assert (Hin2 : In (p, n) (lib.Reusable.YG0d.ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HPERM) Hin3).
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR3 Hin3)
      as (_ & _ & _ & Happb & Hpres & _ & _).
    assert (Ern : lib.Reusable.YG00.req_size n = n).
    { unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec n 0); lia. }
    rewrite Ern in Happb, Hpres. destruct (A.ProgWorldCtlRt.in_app_bounds _ _ Happb) as (Hb1 & Hb2).
    apply (r14g_mrd_keep _ _ mem2 mem3 _ Hle (proj1 (proj1 (Hpres (p + j) ltac:(lia))))).
    apply (F2c p n j Hin3 Hin2); [rewrite Ern; lia | exact (lib.Reusable.YI04.inFP_nil _)]. }
  assert (Hbsh_keep : forall p n, In (p, n) (lib.Reusable.YG0d.ablocks B ly3 S3) -> 0 < n ->
            forall j, 0 <= j < n ->
            lib.Lib.Mem.mrd A.Img0.rsegs mem2 (lib.Lib.Mem.wa (A.AsanRT.shadow_addr (p + j))) =
            lib.Lib.Mem.mrd A.Img0.rsegs mem3 (lib.Lib.Mem.wa (A.AsanRT.shadow_addr (p + j)))).
  { intros p n Hin3 Hn j Hj.
    assert (Hin2 : In (p, n) (lib.Reusable.YG0d.ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HPERM) Hin3).
    destruct (lib.Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR3 Hin3) as (BS3 & _).
    destruct (lib.Reusable.YG0d.al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hin2) as (BS2 & _).
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR3 Hin3) as (_ & _ & _ & Happb & _).
    assert (Ern : lib.Reusable.YG00.req_size n = n).
    { unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec n 0); lia. }
    rewrite Ern in BS3, BS2, Happb. destruct (A.ProgWorldCtlRt.in_app_bounds _ _ Happb) as (Hb1 & Hb2).
    destruct BS3 as (Hp8 & _ & BS3). destruct BS2 as (_ & _ & BS2).
    set (j8 := j / 8).
    assert (Hj8 : 0 <= j8 < (n + 7) / 8) by (subst j8; Z.div_mod_to_equations; lia).
    assert (ES : A.AsanRT.shadow_addr (p + j) =
                 lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF p + j8).
    { subst j8. unfold A.AsanRT.shadow_addr, lib.Reusable.YG0v.shadow_of_addr, A.AsanRT.ASAN_K,
        lib.Reusable.YG0f.SHADOW_OFF. Z.div_mod_to_equations. lia. }
    rewrite ES. pose proof (BS3 j8 Hj8) as V3. pose proof (BS2 j8 Hj8) as V2.
    apply (r14g_mrd_keep _ _ mem2 mem3 _ Hle).
    - apply (r14g_vis_of_view W3 mem3). rewrite V3. discriminate.
    - rewrite V2, V3. reflexivity. }
  (* the input block of the lib pre, a live block when 0 < c_n (PRO's last two conjuncts) *)
  assert (Hin3c : 0 < A.ACtlCut.c_n cx ->
            In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly3 S3)).
  { intros Hn0. destruct Hblk0 as [(Hn1 & _) | (_ & Hin)]; [lia |].
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin. }
  (* ---- the exit cut's premises ---- *)
  apply (HX cx [0] fr k ly2 S2 W2 regs2 mem2 md2 HB).
  - exact HJx.
  - rewrite Hfr2. exact HF.
  - exact HL.
  - exact Hk.
  - cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCut.ix_cut A.ACtlCutP.C_A8183c_at A.ACtlCutP.ixn nth].
    split; [reflexivity|].
    change (Z.to_nat 0) with 0%nat. change (Z.of_nat 0) with 0.
    exists phi.
    change (A.ACtlCutP.rnb cx 0) with n0.
    destruct HCUR as (Hc & C22 & C25).
    pose proof HRB as (HRB6 & _ & HOURb & _ & HIDBr & HFGBr).
    destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg &
      P184 & P256 & P264 & P272 & P32).
    destruct HRXS as (X48 & X56 & X88 & X80 & X72 & X8 & X0 & X200 & X216 & XA).
    split; [exact (Permutation_trans HPERM HP) |].
    (* FRAC at the exit: the same A, sp; registers through K; memory on the stack above sp and in the frame *)
    split.
    { exists A, sp.
      split; [rewrite K2; exact R2 |]. split; [exact Hsp16 |].
      split; [unfold lib.Reusable.YG0d.spZ in *; rewrite K2; exact EspZ |].
      split; [rewrite K4; exact R4 |]. split; [unfold A.ACtlCut.rgv in *; rewrite K8; exact R8 |].
      split; [unfold A.ACtlCut.rgv in *; rewrite K9; exact R9 |]. split; [rewrite K3; exact R3 |].
      split; [unfold A.ACtlCut.rgv in *; rewrite K19; exact R19 |].
      split; [unfold A.ACtlCut.rgv in *; rewrite K26; exact R26 |].
      split; [exact Hfr32 |]. split; [exact HA32 |]. split; [exact HAc |]. split; [exact HspA |].
      split; [unfold A.ACtlCutP.FRAME_BYTES; exact HfrA |]. split; [exact HA416 |]. split; [exact Hsp4096 |].
      split; [unfold A.AsanRT.APPMEM_END; exact HcAPP |].
      split; [apply Hba_stk; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact Q304] |].
      split; [apply Hba_stk; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact Q24] |].
      split; [apply Hba_stk; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact Q16] |].
      split; [rewrite <- (Z.add_0_r fr); apply Hba_frm; [lia | rewrite lib.Lib.Mem.length_le8; lia |];
              rewrite Z.add_0_r; exact QH0 |].
      split; [apply Hba_frm; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact QH16] |].
      split.
      { exists sh. split; [| exact Hshlen]. apply (r14g_bytes_keep mem2 mem3); [| exact Hsh]. intros j Hj.
        rewrite Hshlen in Hj. change (Z.to_nat A.ACtlCutP.FRAME_SHADOW) with 392%nat in Hj.
        apply (Hfsh (Z.of_nat j)). lia. }
      (* the tail: the saved registers on the stack, then the trailer word at fr + 4088, the frame's last word *)
      assert (Hsvlen : Z.of_nat (length (A.ACtlCutP.saved_bytes cx)) = 104).
      { unfold A.ACtlCutP.saved_bytes. repeat rewrite length_app. repeat rewrite lib.Lib.Mem.length_le8.
        reflexivity. }
      split; [apply Hba_stk; [lia | rewrite Hsvlen; lia | exact HSAVED] |].
      unfold A.ACtlCutP.q64 in HTRL |- *.
      apply Hba_frm; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact HTRL]. }
    split.
    { split; [exact Hcn |]. split; [exact Hb6 |].
      split.
      { destruct HHB as (Hphi0 & Hadd). split; [exact Hphi0 |]. unfold A.ACtlK.a_size in *.
        replace (Z.max n0 1) with n0 in * by lia.
        apply (r14g_addr_keep mem2 mem3); [| exact Hadd]. intros j Hj. exact (Hbsh_keep phi n0 Hinphi ltac:(lia) j Hj). }
      split; [unfold A.ACtlCut.rgv; rewrite K23; exact R23 |].
      split; [unfold A.ACtlCutP.OURb in *;
              apply Hba_frm; [lia | rewrite A.Prog.SlotModel.OUR_length; lia | exact HOUR] |].
      split; [unfold A.ACtlCutP.OUTA in *; apply Had_frm; [lia | lia | exact HOUTA] |].
      split; [split; [exact Hc |]; unfold A.ACtlCut.rgv in *; rewrite K22, K25; split; assumption |].
      (apply Hsp; [lia | exact S216]). }
    split; [reflexivity |].
    (* RFb at turn 0 *)
    split.
    { split.
      { split; [exact HRB6 |].
        split; [split; [exact Hc |]; unfold A.ACtlCut.rgv in *; rewrite K22, K25; split; assumption |].
        split; [unfold A.ACtlCutP.OURb in *; apply Hba_frm; [lia | rewrite A.Prog.SlotModel.OUR_length; lia
                                                              | exact HOURb] |].
        split; [unfold A.ACtlCut.rgv; rewrite K23; exact R23 |].
        split; [unfold A.ACtlCutP.IDBr in *; apply Hba_frm; [lia | | exact HIDBr];
                assert (EL : length (A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) 0) = 38%nat) by reflexivity;
                rewrite EL; lia |].
        unfold A.ACtlCutP.FGBr in *; apply Hba_frm; [lia | | exact HFGBr].
        assert (EL : length (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 0) = 72%nat) by reflexivity.
        rewrite EL; lia. }
      split; [exact Hnz |]. split; [unfold A.ACtlCut.rgv; rewrite K24; exact R24 |].
      apply (r14g_bytes_keep mem2 mem3); [| exact HFb]. intros j Hj.
      change (Z.of_nat 0) with 0 in Hj. apply (Hblk_keep phi n0 Hinphi ltac:(lia)). rewrite HLF in Hj. lia. }
    (* a0 = mrow (B3Rtm.a_rtm_want) *)
    split.
    { unfold A.ACtlCut.a0v, A.ACtlCut.rgv. rewrite H10'. unfold lib.Reusable.YG0d.w64. f_equal.
      rewrite r14g_tbl_eq. exact (A.Prog.Seg.B3Rtm.a_rtm_want (A.ACtlCut.c_in cx)). }
    split; [(apply Hsp; [lia | exact S112]) |].
    split; [(apply Hsp; [lia | exact S8]) |].
    split; [(apply Hsp; [lia | exact S0]) |].
    split; [(apply Hsp; [lia | exact S200]) |].
    split; [apply Had_frm; [lia | lia | exact A2528] |].
    split; [(apply Hsp; [lia | exact S128]) |].
    split.
    { split; [(apply Hsp; [lia | exact P40]) |]. split; [(apply Hsp; [lia | exact P120]) |].
      split; [(apply Hsp; [lia | exact P136]) |]. split; [(apply Hsp; [lia | exact P160]) |].
      split; [(apply Hsp; [lia | exact P168]) |]. split; [(apply Hsp; [lia | exact P176]) |].
      split; [(apply Hsp; [lia | exact P208]) |]. split; [(apply Hsp; [lia | exact P248]) |].
      split; [apply Had_frm; [lia | lia | exact Pad] |].
      split.
      { apply (r14g_bytes_keep mem2 mem3); [| exact Pin]. intros j Hj.
        assert (Hn0 : 0 < A.ACtlCut.c_n cx) by lia.
        apply (Hblk_keep _ _ (Hin3c Hn0) Hn0). lia. }
      split; [intros Hn0; exact (r14g_addr_keep _ _ _ _ (Hbsh_keep _ _ (Hin3c Hn0) Hn0) (Pg Hn0)) |].
      split; [(apply Hsp; [lia | exact P184]) |]. split; [(apply Hsp; [lia | exact P256]) |].
      split; [(apply Hsp; [lia | exact P264]) |]. split; [(apply Hsp; [lia | exact P272]) |].
      (apply Hsp; [lia | exact P32]). }
    split; [(apply Hsp; [lia | exact S104]) |].
    split; [(apply Hsp; [lia | exact S96]) |].
    split; [(apply Hsp; [lia | exact S64]) |].
    split; [unfold A.ACtlCut.rgv; rewrite K21; exact R21 |].
    split; [(apply Hsp; [lia | exact S144]) |].
    split; [(apply Hsp; [lia | exact S192]) |].
    split; [destruct HIDB as (idb & Hidb); exists idb; apply Hrw_frm; [lia | cbn; lia | exact Hidb] |].
    split; [destruct HJNK as (jk & Hjk); exists jk; apply Hrw_frm; [lia | cbn; lia | exact Hjk] |].
    split; [(apply Hsp; [lia | exact S280]) |].
    split; [(apply Hsp; [lia | exact S240]) |].
    split; [destruct HJY as (jy & Hjy); exists jy; apply Hrw_frm; [lia | cbn; lia | exact Hjy] |].
    split; [destruct HJNK2 as (jk & Hjk); exists jk; apply Hrw_frm; [lia | cbn; lia | exact Hjk] |].
    split; [(apply Hsp; [lia | exact S152]) |].
    split; [apply Had_frm; [lia | lia | exact A2176] |].
    split; [(apply Hsp; [lia | exact X48]) |]. split; [(apply Hsp; [lia | exact X56]) |].
    split; [(apply Hsp; [lia | exact X88]) |]. split; [(apply Hsp; [lia | exact X80]) |].
    split; [(apply Hsp; [lia | exact X72]) |]. split; [(apply Hsp; [lia | exact X8]) |].
    split; [(apply Hsp; [lia | exact X0]) |]. split; [(apply Hsp; [lia | exact X200]) |].
    split; [(apply Hsp; [lia | exact X216]) |].
    apply Had_frm; [lia | lia | exact XA].
  - (* ctl_rt_C at the exit: a Theorem Labs lane's ctl_rt_C_of_AR at the exit journal's AR, the read-only view along the composed
       journal (route (C): no VIS0 / OWNED_RO) *)
    exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly2 S2 W2 mem2 md2 HAR2
             (r14g_arodataP _ (Hro_keep _ _ _ _ _ _ _ HJx))).
Qed.

End GlueR14.
