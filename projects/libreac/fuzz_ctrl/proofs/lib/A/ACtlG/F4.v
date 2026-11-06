(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 507 of its 559 lines of code are new or changed and 3060 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtl.v, with its module paths and module names changed; 364 of its 379 lines of code are new or changed and 544 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F5_e10.v, with its module names and numbers changed; 1362 of its 1528 lines of code are new or changed and 213 lines of the source are left out. *)
(* lib/A/ACtlG/F4.v -- GLUE for stage seg_F4 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v (at head lib/A/ACtl.v:747) (an earlier version, blob 84ef756918c, not in this delivery),
   Hypothesis seg_F4).  Written by a Theorem Labs lane (lane of a Theorem Labs lane, helper of a Theorem Labs lane; single writer of this file),
   from its two arm lanes: a Theorem Labs lane (glue_F4_d64, a working branch dd796055c2f) and a Theorem Labs lane
   (glue_F4_dbc, a working branch d811c09d7a9), merged here except the lib/Lib aliases below; comments since reworded.
   Brief: stage-parse-sites.md (a working note, not in this delivery); pattern:
   glue-pattern.md (a working note, not in this delivery).  rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F4 : forall POST (j : nat),
       CF POST (ix_cut C_A81e88_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ea4_at [Z.of_nat j]) ->
       CF POST (ix_cut C_A81ea8_at [Z.of_nat j]) -> CF POST (ix_cut C_A81e84_at [Z.of_nat j]) ->
       CF POST (ix_cut C_A81dfc_at [Z.of_nat j]) /\ CF POST (ix_cut C_A81e54_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F4 (a two-entry segment, as Seg/F4.v's seg_F4 :3618).  It is glue_F4_d64 /\ glue_F4_dbc.

   THE 0x81dfc ARM (glue_F4_d64; Seg/F4.v seg_F4_d64 :3248-3611)
     The three inline runs of seg_F4_d64, extracted and re-run over StepF in lib/A/Prog/Seg/F4d64F.v (this lane's
     file, a Theorem Labs lane's assignment 04:26Z; a working branch 13aa8a2b8bc; the substitute for a run pin is its
     seg_F4_d64_of_F, constr_eq-pinned to F4.seg_F4_d64): f4_d64_short_run_F (flen <= 49, exit 0x81e88),
     f4_d64_136_run_F (record byte 12 = 136, exit 0x81ea8, also stores [A+240] = b2z t_8819), f4_d64_n136_run_F
     (byte 12 <> 136, exit 0x81ea4).
     G1  ix_cut's index equation, then C_A81dfc_at's body: FRAC, b5_body (phi, Permutation, c_n, j, HB, FLSI, LK, b5_C),
         FC, rgv 10 (t_k j), rgv 25 (phi + 18), (50 <= flen -> rgv 22 0), u32 (fr + 176) (t_k j), IDj, b5_PF.
     G2  the spill base A of FRAC and the bounds (FRAC, the journal's astk_ok, AR's block law over the Permutation, the
         lib pre's input block); the spill words lie in the journal's stack window (apresent: stk and the stack rng
         premises); on the long arms the record bytes phi + 12 / phi + 13 (b5_PH), their shadow bytes (F4.f4_sh_at
         from HB) and their visibility (ProgWorldVisHeap.heap_vis / heap_sh_vis on the live block (phi, flen j)).
     G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv to the runs' start map mkR_of regs.
     G4  the case split of Seg/F4.v:3316 / :3389; the run at fx := UK11.mkFP CK11.fp_regs CK11.fp_csr (the runs are over
         ctrl's lib/A/Reusable/YK11 FPState) and RNG := ProgBridge.RNG_W (w_H W3); ProgBridge.fevt_of_evtF +
         tfibsegs_rsegs + YA0nR.SRr_fevt_hid.
     G5  the exit cut at the run's end map and memory: journal by YCbq.ajournal_exec (write set: the two spill words,
         the stack-window case of awr_byte); frames / frame law / k bound unchanged; body by f4g_d64_body_keep (every
         cell it reads lies off the two spill words; FRAC is re-established by f4g_d64_frac_keep, which walks FRAC's
         conjuncts generically, so a Theorem Labs lane's announced trailer conjunct q64 m (fr + 4088) .. is kept by the same
         step: tested in a scratch copy) plus the run's register facts and the stores (b5_F17, b5_sp 240, b5_W240);
         ctl_rt_C by f4g_d64_ctlrt_keep (both words above HIGHMEM_BEG, off every runtime cell, the shadow and the rom;
         the arm keeps ly3 S3, so the regions cut_shadow / img_shadow do not move: route (C), L3-recipe.md section 2(d) (a working note, not in this delivery),
         two A.ShadowRwOnT.shadow_rw_on_kept).

   THE 0x81e54 ARM (glue_F4_dbc; Seg/F4.v f4_seg_dbc :2901), THROUGH THE PARSE CALL
     Machine code: 0x81e54 addi a0,s7,18 ; sd a0,200(s1) ; sb zero,22..25(s3) ; li a0,4 ; sb a0,26(s3)
     [F4F.f4_dbc_st_F, a Theorem Labs lane's] ; mv a0,s7 ; li a1,0 ; ld a2,248(s1) ; jal reac_ctrl_parse
     [F4Fs.PF.f4_dbc_call_pre_Fs, this lane's split file lib/A/Prog/Seg/F4Fs.v, a working branch 98e9c5325bf,
     a Theorem Labs lane's yes 04:01Z; its post stretch is ZERO instructions: the callee returns to 0x81e84, which IS the exit
     cut C_A81e84_at].
     G1  the entry cut at [j]: FRAC, b5_body (flen j = 0, IDj, b5_PF).
     G2  A = s1 (FRAC), Sfr fr = s3, phi = s7 (b5_C), o = fr + 176 (b5_SPILL); the store targets present and visible
         (the journal's stack window; the class-6 frame's shadow by AR_frames_law); RNG := RNG_W (w_H W3).
     G3  YA0nR.SRr_xregs_eqv to the run's explicit start map.
     G4  ONE run, f4_dbc_st_F then f4_dbc_call_pre_Fs, to the callee entry 0x83578 (ra = 0x81e84, a0 = phi, a1 = 0,
         a2 = fr + 176), lifted by YA0nR.SRr_fsteps; the journal at the callee entry by ProgWorld.ajournal_of_fsteps
         (write set [A+200, A+208): stack window; [Sfr fr + 22, Sfr fr + 27): the owned frame's shadow).
     P   a Theorem Labs lane's cgif-form treac_ctrl_parse_spec at the callee entry (YA0n.SRr_bind), n = 0, o = fr + 176:
         P10 the 36-byte record in the owned frame with its shadow the five stored bytes [0;0;0;0;4] (f4g_dbc_shz),
         P11 the frame clause of awr_byte; the rest from the cut body and the journal.
     G5  the spec's post at the return point is the exit cut's configuration: registers by aregs_preserved; memory in
         two steps (mem3 -> m2: the run's munch; m2 -> mem2: acall_kept via ProgWorld.ctl_post_acall_kept): the stack
         above the callee window, the class-6 frame off the output record and its shadow off the five stored bytes,
         live heap blocks, KIND_NAME's 112 non-owned image bytes; block shadows and KIND_NAME's shadow from the post's
         AR (ProgWorldShadow.ctl_block_shadow_of_AR, ctl_zshadow_of_AR with the zero-shadow row found by value); the
         frame's presence and its shadow word list from the post's AR_frames_law; a0 = 0 = t_k j and the first output
         word 0 (ctrlparse 0 _ = (0, repeat cp_z 36)); b5_F17 is the stored word; b5_PH / b5_PF are off at flen = 0;
         ctl_rt_C by A.ProgWorldCtlRtC.ctl_rt_C_of_AR at the post's AR (route (C), L3-recipe.md section 2(d) (a working note, not in this delivery)).
         FRAC is rebuilt conjunct-generically (the announced trailer conjunct is in the frame, off the output record).

   SECTION HYPOTHESES (after End GlueF4 each lemma keeps only those its proof uses)
   - RELRO_IMG, LAWS, TFIB_SYMS: ACtl.v's Section Ctl hypotheses, same text (ACtl.v:181, :185, :193).
   - TPARSE: the parse spec of record, a working branch 621a4ba64dc (REAC_CTRL_PARSE_STK = 8800),
     lib/A/Prog/C_reac_ctrl_parse.v (`treac_ctrl_parse_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI`), as the
     brief's route cites it; P7 needs c_sp - LLVMF_STK <= sp - 8800, from FRAC's c_sp - 4096 < sp, LLVMF_STK = 32768.
   - none for the exits' runtime conjunct: route (C) takes ctl_rt_C from the post's AR by
     A.ProgWorldCtlRtC.ctl_rt_C_of_AR, which needs neither A.ProgWorld.AR_states_vis0_shadow nor
     AR_states_owned_ro, so the former Section hypotheses VIS0 / OWNED_RO are gone.
   No run is a hypothesis: Seg/F4F.v (a Theorem Labs lane, e1ece7d93f27), Seg/F4Fs.v and Seg/F4d64F.v are Required.

   START-UP TABLE VALUES READ (checked by hand against the RECORD a working branch e56483f863b
   lib/A/AF0m.v): Tfib_zero_shadow (KIND_NAME's 112 shadow bytes: record :2963 row (0x21aa0, 0x9e7d0 - 0x21aa0)
   covers [0x9e760, 0x9e7d0); found by value, no fixed index), Tfib_owned_static (no row meets
   [KIND_NAME, KIND_NAME + 112); record :2965-2981, (0x9e7d0, 0x30) starts at KIND_NAME + 112), TFIB_ERRNO (record
   :18 = 0x5db76c).  gp stays symbolic (as_gp B).  Each holds on the record.

   CLOSURE (glue closure rule): every Require is qualified; no statement names a frame-route identifier (proof-internal
   uses of A.Prog.Seg.F4 / A.Prog.SlotInv names only, inside Qed lemmas).  The six twinned modules (YI04 YI16 YK11
   YK1b YM05 YO09) are named only through the aliases CK11 / CK1b / CM05 / CO09 / CI04 (core) and UK11 (unit) or their
   full path; lib/Lib's Mem / Frame / MState also have copies under lib/A/Bz/Lib and lib/AZ/Lib, so they are Required by
   full path and named only through LMem / LFr / LMS.  The commit message lists the blob of every frame-route file in
   the closure.

   BUILD STATE: built on the stand-in-free image-A glue base a working branch 29ddfc3ea99 (interim core
   5da74c9c931): the closure reaches no stand-in.  No Axiom, no Parameter, no Admitted, no admit. *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)

From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The six twinned modules (YI04 YI16 YK11 YK1b YM05 YO09): Required by FULL path, used only through the aliases
   below (porter's rule, final 04:24Z + amendment (b) 04:33Z). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG01 Reusable.YG0n Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq Reusable.YK04 Reusable.YK04R Reusable.YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.AF0m A.Img0 A.AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldCtlRt A.ProgWorldShadow.
(* route (C): the narrowed cut conjunct, its keep lemma and its producer from AR (no VIS0 / OWNED_RO). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT A.ACtlRtC A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisWin A.ProgWorldVisFrame A.ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.C_reac_ctrl_parse A.Prog.reac_ctrl_parse_c.
(* the runs: Seg/F4F.v (f4_dbc_st_F), Seg/F4Fs.v (the split at the parse call), Seg/F4d64F.v (the three
   inline runs of seg_F4_d64); no run is a Section hypothesis *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F4F A.Prog.Seg.F4Fs A.Prog.Seg.F4d64F.
(* lib/Lib's Mem / Frame / MState have copies under lib/A/Bz/Lib and lib/AZ/Lib: Required by full path, named only
   through the aliases LMem / LFr / LMS below.  ExecF and Regs6ss have one copy. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.ExecF Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
(* cited inside proofs only (all in the closure of Seg/F4F.v, Seg/F4Fs.v and Seg/F4d64F.v, or the PA layer) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AsanRTFacts A.Prog.SlotModel A.Prog.RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.Tac_slot A.Prog.Seg.F4 A.Prog.rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ctrl_kind_name_c A.Prog.ImgBounds A.Prog.CtrlImg Prog.RcParse.
Import ListNotations.
Local Open Scope Z_scope.

(* Aliases (the gate's `M.n` form). C* = the core's copy, U* = the unit's (ctrl's lib/A/Reusable) copy. *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module CI04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
Module UK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
(* lib/Lib and the model / frame-route files the proofs cite, by full path. *)
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module RCP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module F4S := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F4.
Module F4R := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F4d64F.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueF4.

(* ACtl.v's Section Ctl shape (ACtl.v:170-195), restricted to what this stage uses, in ACtl.v's order. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :265-270), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81dfc_at := (ACtlCutP.C_A81dfc_at B).
Local Notation C_A81e54_at := (ACtlCutP.C_A81e54_at B).
Local Notation C_A81e84_at := (ACtlCutP.C_A81e84_at B).
Local Notation C_A81e88_at := (ACtlCutP.C_A81e88_at B).
Local Notation C_A81ea4_at := (ACtlCutP.C_A81ea4_at B).
Local Notation C_A81ea8_at := (ACtlCutP.C_A81ea8_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses. *)

(* The parse spec of record (a working branch 621a4ba64dc), cgif form, applied at the
   `jal reac_ctrl_parse` 0x81e80 (route of a Theorem Labs lane 03:56Z). *)
Hypothesis TPARSE : A.Prog.C_reac_ctrl_parse.treac_ctrl_parse_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI.

(* route (C): VIS0 / OWNED_RO (ProgWorld.AR_states_vis0_shadow / AR_states_owned_ro) are GONE: the dbc exit's
   ctl_rt_C comes from A.ProgWorldCtlRtC.ctl_rt_C_of_AR, which needs neither. *)

(* ---------------------------------------------------------------------------------------------------------
   The 0x81dfc arm's helpers (stage-specific, f4g_d64_ prefix). *)

(* The run's write set: the two spill words F4.v's f4_Wsp names (F4.v:771). *)
Definition f4g_d64_W (A : Z) : list LFr.ivl := [(A + 200, A + 208); (A + 240, A + 248)].

Lemma f4g_d64_W_out : forall A x, x < A + 200 \/ A + 208 <= x < A + 240 \/ A + 248 <= x ->
  LFr.outside (f4g_d64_W A) x.
Proof. intros A x H. unfold f4g_d64_W. cbn [LFr.outside]. repeat split; try exact I; lia. Qed.

Lemma f4g_d64_W_in : forall A x, ~ LFr.outside (f4g_d64_W A) x -> A + 200 <= x < A + 248.
Proof.
  intros A x H.
  destruct (Z_lt_le_dec x (A + 200)) as [H1|H1]; [exfalso; apply H, f4g_d64_W_out; lia|].
  destruct (Z_lt_le_dec x (A + 248)) as [H2|H2]; [lia | exfalso; apply H, f4g_d64_W_out; lia].
Qed.

Lemma f4g_d64_W_app : forall A, A.AsanRT.HIGHMEM_BEG <= A -> A + 248 <= A.AsanRT.APPMEM_END ->
  A.AsanRTFacts.all_app (f4g_d64_W A).
Proof.
  intros A H1 H2. unfold f4g_d64_W. cbn [A.AsanRTFacts.all_app].
  split; [apply F4S.f4_app_ivl; lia | split; [apply F4S.f4_app_ivl; lia | exact I]].
Qed.

Lemma f4g_d64_outside_dec : forall (WR : list LFr.ivl) x, LFr.outside WR x \/ ~ LFr.outside WR x.
Proof.
  induction WR as [|[lo hi] WR IH]; cbn [LFr.outside]; intros x; [left; exact I|].
  assert (D : (lo <= x < hi) \/ ~ (lo <= x < hi)) by lia.
  destruct D as [D|D]; [right; tauto|]. destruct (IH x) as [H|H]; [left; tauto | right; tauto].
Qed.

(* The store of the 0x81e04 spill (short and n136 arms), and of both spills (136 arm). *)
Lemma f4g_d64_wr1 : forall (m : word -> option byte) A (v : word), 0 <= A -> A + 248 <= 2 ^ 64 ->
  LFr.munch (f4g_d64_W A) m (write_to_mem m (LMem.wa (A + 200)) (LMem.le8 v)) /\
  LFr.wmono A.Img0.rsegs m (write_to_mem m (LMem.wa (A + 200)) (LMem.le8 v)) /\
  CK1b.mem_grows m (write_to_mem m (LMem.wa (A + 200)) (LMem.le8 v)).
Proof.
  intros m A v H0 H1. split; [|split].
  - unfold f4g_d64_W. apply (LFr.munch_write _ m m (A + 200) (LMem.le8 v));
      [ apply LFr.munch_refl | lia | rewrite LMem.length_le8; lia
      | rewrite LMem.length_le8; cbn [LFr.inside]; left; lia ].
  - apply LFr.wmono_write. apply LFr.wmono_refl.
  - apply CK1b.write_to_mem_grows.
Qed.

Lemma f4g_d64_wr2 : forall (m : word -> option byte) A (v w : word), 0 <= A -> A + 248 <= 2 ^ 64 ->
  LFr.munch (f4g_d64_W A) m
    (write_to_mem (write_to_mem m (LMem.wa (A + 200)) (LMem.le8 v)) (LMem.wa (A + 240)) (LMem.le8 w)) /\
  LFr.wmono A.Img0.rsegs m
    (write_to_mem (write_to_mem m (LMem.wa (A + 200)) (LMem.le8 v)) (LMem.wa (A + 240)) (LMem.le8 w)) /\
  CK1b.mem_grows m
    (write_to_mem (write_to_mem m (LMem.wa (A + 200)) (LMem.le8 v)) (LMem.wa (A + 240)) (LMem.le8 w)).
Proof.
  intros m A v w H0 H1. destruct (f4g_d64_wr1 m A v H0 H1) as (MU1 & WM1 & GR1). split; [|split].
  - apply (LFr.munch_write _ m _ (A + 240) (LMem.le8 w));
      [ exact MU1 | lia | rewrite LMem.length_le8; lia
      | unfold f4g_d64_W; rewrite LMem.length_le8; cbn [LFr.inside]; right; left; lia ].
  - apply LFr.wmono_write. exact WM1.
  - exact (CK1b.mem_grows_trans _ _ _ GR1 (CK1b.write_to_mem_grows _ _ _)).
Qed.

(* The shadow byte of p + k (k = 0, 1) lies in the shadow word cover of [p, p + 2) (rng_asan.v:80-81). *)
Lemma f4g_d64_sh_cover : forall p k, 0 <= p -> 0 <= k < 2 ->
  A.Prog.rng_asan.sh_al8_lo p <= Z.shiftr (p + k) 3 + A.AsanRT.ASAN_K /\
  Z.shiftr (p + k) 3 + A.AsanRT.ASAN_K + 1 <= A.Prog.rng_asan.sh_al8_hi p 2.
Proof.
  intros p k Hp Hk.
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold A.AsanRT.ASAN_K.
  assert (M1 : p / 8 <= (p + k) / 8) by (apply Z.div_le_mono; lia).
  assert (M2 : (p + k) / 8 <= (p + 2 - 1) / 8) by (apply Z.div_le_mono; lia).
  split; Z.div_mod_to_equations; lia.
Qed.

(* FRAC's spill base is a representative of register 9 in [0, 2 ^ 64). *)
Lemma f4g_d64_frac_base : forall (cx : ACtlCut.ctlcx) (fr sel : Z) (regs : bvmap 5 word)
    (m : word -> option byte),
  ACtlCutP.FRAC B cx fr sel regs m -> exists A, ACtlCut.rgv regs 9 A /\ 0 <= A < 2 ^ 64.
Proof.
  intros cx fr sel regs m H.
  destruct H as (A' & sp & R2 & Hspm & Hspz & _ & _ & R9 & _ & _ & _ & _ & _ & HAS & Hspa & _ & _ & _ & HAPP & _).
  exists A'. split; [exact R9|].
  assert (Hsp0 : 0 <= sp).
  { rewrite <- Hspz. unfold Reusable.YG0d.spZ. exact (proj1 (bv_unsigned_in_range _ _)). }
  unfold A.AsanRT.APPMEM_END in HAPP. lia.
Qed.

(* The numeric facts the keeps and the runs need, from what ctl_from hands a stage.  The last one, fr + 4096 <= A,
   is the class-6 frame's end (frames_bounds and the frame law) below the stack (astk_ok): every word of the frame,
   its trailer word fr + 4088 included, lies below the spill words. *)
Lemma f4g_d64_bounds : forall (cx : ACtlCut.ctlcx) (own : list (Z * Z)) ly3 S3 W3 (m : word -> option byte) md3
    (k fr sel A phi : Z) (j : nat) (regs : bvmap 5 word),
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) own ly3 S3 W3 m md3 k ->
  In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3) ->
  fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) ->
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3)
    (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx) ++ [(phi, ACtlCutP.flen cx j)]) ->
  A.AsanRT.HIGHMEM_BEG <= A /\ A + 416 <= A.AsanRT.APPMEM_END /\ 0 <= fr /\
  fr + ACtlCutP.FRAME_BYTES <= A /\ phi + A.ACtlK.a_size (ACtlCutP.flen cx j) <= A /\
  ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) <= A /\
  ACtlCut.c_sp cx - A.ACfn.LLVMF_STK <= A /\ A + 416 <= ACtlCut.c_sp cx /\ 0 <= ACtlCutP.flen cx j /\
  fr + 4096 <= A.
Proof.
  intros cx own ly3 S3 W3 m md3 k fr sel A phi j regs HB HJ Hin6 Hfrl HFRAC H9 HAr HPerm.
  destruct HFRAC as (A' & sp & _ & _ & _ & _ & _ & R9 & _ & _ & _ & _ & _ & HAS & Hspa & HfrA & HA416 & HS4 & HAPP &
    _ & _ & _ & Qhdr & _).
  pose proof Qhdr as (Hfr0 & _).
  destruct HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hlo & _).
  pose proof Reusable.YCbq.asan_consts as (HAC & _).
  (* the class-6 frame ends below alloc_ceiling (frames_bounds at ly3; layout_le keeps ly_F) *)
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 m md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & Hfc & _).
  assert (Efb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (Efr3 : fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite Hfrl. unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  rewrite Efb, <- Efr3 in Hfc.
  assert (HAPPv : A.AsanRT.APPMEM_END = 140737488355328) by reflexivity.
  assert (HHBv : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HSTKv : A.ACfn.LLVMF_STK = 32768) by reflexivity.
  rewrite HSTKv in Hlo. rewrite HAPPv in HAPP.
  assert (EA : A = A').
  { apply F4S.f4_id; [exact HAr | lia |].
    transitivity (CK11.getr regs 9); [symmetry; exact H9 | exact R9]. }
  subst A'.
  assert (Hin : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 m md3 _ _ HAR Hin) as (_ & _ & Hpc & _ & _ & _ & Hn).
  assert (Hrq : A.ACtlK.a_size (ACtlCutP.flen cx j) <= Reusable.YG00.req_size (ACtlCutP.flen cx j)).
  { unfold A.ACtlK.a_size, Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  assert (Hinp : ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) <= A).
  { destruct HB as (HPRE & _).
    destruct HPRE as (_ & _ & _ & _ & Hpn & Hlen & _).
    rewrite <- Hlen.
    destruct Hpn as [(Hn0 & Hp0) | (Hnpos & Hinp)].
    - rewrite Hn0, Hp0. unfold A.ACfn.A_EMPTY. lia.
    - assert (Hin2 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
      { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. exact Hinp. }
      destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 m md3 _ _ HAR Hin2) as (_ & _ & Hpc2 & _).
      unfold Reusable.YG00.req_size in Hpc2.
      rewrite (proj2 (Z.eqb_neq (ACtlCut.c_n cx) 0) ltac:(lia)) in Hpc2. lia. }
  rewrite HHBv, HAPPv, HSTKv.
  split; [lia|]. split; [lia|]. split; [exact Hfr0|]. split; [exact HfrA|].
  split; [lia|]. split; [exact Hinp|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* The journal across the run: its writes are the two spill words, in the stack window (ajournal_exec, the first
   arm of awr_byte). *)
Lemma f4g_d64_journal : forall STK sp0 (FPj : list (Z * Z)) ly S W mem md own lyc Sc Wc
    (memc : word -> option byte) mdc (k : Z) (memc' : word -> option byte) mdc' (A : Z),
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k ->
  LFr.munch (f4g_d64_W A) memc memc' -> CK1b.mem_grows memc memc' ->
  (forall x : word, Reusable.YA0n.w_H Wc x = true -> memc' x = memc x) ->
  Reusable.YK04.same_but_materialized mdc mdc' ->
  sp0 - STK <= A + 200 -> A + 248 <= sp0 ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B STK sp0 FPj ly S W mem md own lyc Sc Wc memc' mdc' k.
Proof.
  intros STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' A HJ MU Hgr Hhid Hsbm Hlo Hhi.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low STK sp0 FPj ly S W mem md own lyc Sc Wc
    memc mdc k memc' mdc' (fun a => 0 <= a < 2 ^ 64 /\ ~ LFr.outside (f4g_d64_W A) a) HJ).
  - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU x); [reflexivity|].
    destruct (f4g_d64_outside_dec (f4g_d64_W A) (bv_unsigned x)) as [Ho|Ho]; [exact Ho|].
    exfalso. apply Hx. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    split; [exact R | exact Ho].
  - intros x Hx. unfold Reusable.YK04.mrestrict in *.
    destruct (Reusable.YA0n.w_H Wc x); [exact Hx | exact (Hgr x Hx)].
  - exact Hhid.
  - exact Hsbm.
  - intros a (Ha & Ho). left. pose proof (f4g_d64_W_in A a Ho). lia.
Qed.

(* ctl_rt_C across the run: every written byte is above HIGHMEM_BEG <= A, and the state (ly, S) is kept, so the two
   shadow regions cut_shadow B ly S and img_shadow are kept by A.ShadowRwOnT.shadow_rw_on_kept. *)
Lemma f4g_d64_ctlrt_keep : forall ly (S : Reusable.YG00.astate) (m m' : word -> option byte) (A : Z),
  A.ACtlRtC.ctl_rt_C B ly S m -> LFr.munch (f4g_d64_W A) m m' -> LFr.wmono A.Img0.rsegs m m' ->
  A.AsanRT.HIGHMEM_BEG <= A -> A + 248 <= A.AsanRT.APPMEM_END -> A.ACtlRtC.ctl_rt_C B ly S m'.
Proof.
  intros ly S m m' A (HAC & HCUT & HIMG & HRO) MU WM HAh HAa.
  assert (HHBv : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (Hlow : forall x, x < A.AsanRT.HIGHMEM_BEG -> LFr.outside (f4g_d64_W A) x).
  { intros x Hx. apply f4g_d64_W_out. lia. }
  pose proof (f4g_d64_W_app A HAh HAa) as AW.
  assert (T : forall a bs, LMem.bytes_at A.Img0.rsegs m a bs ->
                a + Z.of_nat (length bs) <= A.AsanRT.HIGHMEM_BEG -> LMem.bytes_at A.Img0.rsegs m' a bs).
  { intros a bs Hb Hl. apply (A.Prog.RcAsanFPLib.fl_bytes (f4g_d64_W A) m m' a bs Hb MU).
    intros x Hx. apply Hlow. lia. }
  split; [|split; [|split]].
  - unfold A.ACtlK.asan_cells_at, A.AsanRT.asan_cells in *.
    destruct HAC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17).
    repeat match goal with |- _ /\ _ => split end;
      (apply T; [eassumption |]);
      rewrite ?LMem.length_le8, ?LMem.length_le4; cbn [length];
      rewrite HHBv; unfold A.AsanRT.CELL_K, A.AsanRT.UAR, A.AsanRT.INITED, A.AsanRT.REPLACE, A.AsanRT.CANPOISON,
        A.AsanRT.HIEND, A.AsanRT.MIDBEG, A.AsanRT.MIDEND, A.AsanRT.REAL_MEMCPY, A.AsanRT.REAL_MEMSET,
        A.AsanRT.GOT_CELL_K, A.AsanRT.GOT_UAR, A.AsanRT.GOT_REPLACE, A.AsanRT.GOT_HIEND, A.AsanRT.GOT_MIDBEG,
        A.AsanRT.GOT_MIDEND, A.AsanRT.GOT_REAL_MEMSET; lia.
  - exact (A.ShadowRwOnT.shadow_rw_on_kept _ m m' HCUT (A.AsanRTFacts.munch_meta (f4g_d64_W A) m m' MU AW) WM).
  - exact (A.ShadowRwOnT.shadow_rw_on_kept _ m m' HIMG (A.AsanRTFacts.munch_meta (f4g_d64_W A) m m' MU AW) WM).
  - intros a Hro. unfold LMem.mrd. rewrite (MU a).
    + exact (HRO a Hro).
    + apply Hlow.
      destruct (Z_lt_le_dec (bv_unsigned a) A.AsanRT.HIGHMEM_BEG) as [Hl|Hl]; [exact Hl|]. exfalso.
      assert (Hn : ~ Reusable.YG0d.in_img A.Img0.rsegs (bv_unsigned a)).
      { intros Hi. pose proof (A.ACtlG.Kit.kit_segs_low _ Hi) as Hb.
        unfold Reusable.YG0f.kLowMemEnd in Hb. rewrite HHBv in Hl. lia. }
      unfold LMem.ro_addr in Hro.
      rewrite (Reusable.YCbq.find_segment_none A.Img0.rsegs (bv_unsigned a) Hn) in Hro. discriminate.
Qed.

(* One kept cell's bytes [a, a + n) lie off the spill words: n is 8, the saved-register block's 104 (Hsl), or a
   byte list whose length the context states (the 392 frame shadow bytes, below HIGHMEM_BEG <= A). *)
Local Ltac f4g_d64_bnd A Hsl :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx;
  repeat match goal with Hl : length ?l = _ |- _ => rewrite Hl in Hx end;
  try rewrite Hsl in Hx;
  try change (Z.of_nat (Z.to_nat ACtlCutP.FRAME_SHADOW)) with 392 in Hx;
  try unfold ACtlCutP.Sfr in Hx; try unfold A.AsanRT.shadow_addr in Hx; try unfold A.AsanRT.ASAN_K in Hx;
  refine (f4g_d64_W_out A x _); Z.div_mod_to_equations; lia.

(* The FRAC walk.  The goal is FRAC's conjunction at (regs', m') after the register rewrites; the context holds the
   same conjuncts at (regs, m), destructed.  Each register / numeric conjunct is a hypothesis; each memory conjunct
   (a q64 cell, a byte list, or an existential byte list with its length) is kept from the same fact at m because
   its bytes are off the two spill words.  The walk names no conjunct position, so a conjunct appended to FRAC
   (a Theorem Labs lane's trailer word q64 m (fr + 4088) ..., inside the class-6 frame, below fr + 4096 <= A) is closed by
   the same cases. *)
Local Ltac f4g_d64_frac_walk A m m' MU Hsl :=
  repeat match goal with |- _ /\ _ => split end;
  try assumption;
  lazymatch goal with
  | |- ACtlCutP.q64 m' ?a ?v =>
      match goal with Hq : ACtlCutP.q64 m a v |- _ =>
        apply (F4S.f4_q64_keep (f4g_d64_W A) m m' a v Hq MU) end
  | |- LMem.bytes_at _ m' ?a ?bs =>
      match goal with Hb : LMem.bytes_at _ m a bs |- _ =>
        apply (A.Prog.RcAsanFPLib.fl_bytes (f4g_d64_W A) m m' a bs Hb MU) end
  | |- exists s, LMem.bytes_at _ m' ?a s /\ _ =>
      match goal with Hb : LMem.bytes_at _ m a ?bs |- _ =>
        exists bs; split; [apply (A.Prog.RcAsanFPLib.fl_bytes (f4g_d64_W A) m m' a bs Hb MU) | assumption] end
  end;
  f4g_d64_bnd A Hsl.

(* FRAC across the run: its cells lie below A + 200 or from A + 248 on (the class-6 frame below fr + 4096 <= A);
   its registers are kept. *)
Lemma f4g_d64_frac_keep : forall (cx : ACtlCut.ctlcx) (fr sel A : Z) (regs regs' : bvmap 5 word)
    (m m' : word -> option byte),
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 -> A.AsanRT.HIGHMEM_BEG <= A ->
  fr + 4096 <= A ->
  LFr.munch (f4g_d64_W A) m m' ->
  CK11.getr regs' 2 = CK11.getr regs 2 -> CK11.getr regs' 3 = CK11.getr regs 3 ->
  CK11.getr regs' 4 = CK11.getr regs 4 -> CK11.getr regs' 8 = CK11.getr regs 8 ->
  CK11.getr regs' 9 = CK11.getr regs 9 -> CK11.getr regs' 19 = CK11.getr regs 19 ->
  CK11.getr regs' 26 = CK11.getr regs 26 ->
  ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros cx fr sel A regs regs' m m' H H9 HAr HA H4096 MU E2 E3 E4 E8 E9 E19 E26.
  assert (HAPPv : A.AsanRT.APPMEM_END = 140737488355328) by reflexivity.
  assert (HHBv : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (Hsl : Z.of_nat (length (ACtlCutP.saved_bytes cx)) = 104).
  { unfold ACtlCutP.saved_bytes. rewrite !length_app, !LMem.length_le8. reflexivity. }
  destruct H as (A' & sp & HC).
  (* FRAC's own base is A: a read-only prefix of FRAC's conjuncts *)
  pose proof HC as (_ & _ & Hspz & _ & _ & R9 & _ & _ & _ & _ & _ & HAS & Hspa & _ & _ & _ & HAPP & _).
  assert (Hsp0 : 0 <= sp).
  { rewrite <- Hspz. unfold Reusable.YG0d.spZ. exact (proj1 (bv_unsigned_in_range _ _)). }
  assert (EA : A = A').
  { apply F4S.f4_id; [exact HAr | rewrite HAPPv in HAPP; lia |].
    transitivity (CK11.getr regs 9); [symmetry; exact H9 | exact R9]. }
  subst A'. clear Hspz R9 HAS Hspa HAPP.
  exists A, sp.
  unfold ACtlCut.rgv, Reusable.YG0d.spZ in *.
  rewrite ?E2, ?E3, ?E4, ?E8, ?E9, ?E19, ?E26.
  repeat match goal with
         | Hc : _ /\ _ |- _ => destruct Hc as [? ?]
         | Hc : exists _, _ |- _ => destruct Hc as [? ?]
         end.
  f4g_d64_frac_walk A m m' MU Hsl.
Qed.

(* FLSI / LK / b5_C (ACtlCutP.v:677, :556, :820) read registers 2 (b5_PH's spZ), 9, 18, 21, 23 only. *)
Lemma f4g_d64_move : forall (cx : ACtlCut.ctlcx) (j : nat) (phi fr : Z) (regs regs' : bvmap 5 word)
    (m : word -> option byte),
  CK11.getr regs' 2 = CK11.getr regs 2 -> CK11.getr regs' 9 = CK11.getr regs 9 ->
  CK11.getr regs' 18 = CK11.getr regs 18 -> CK11.getr regs' 21 = CK11.getr regs 21 ->
  CK11.getr regs' 23 = CK11.getr regs 23 ->
  ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.LK cx fr j regs m -> ACtlCutP.b5_C cx j phi fr regs m ->
  ACtlCutP.FLSI cx j fr regs' m /\ ACtlCutP.LK cx fr j regs' m /\ ACtlCutP.b5_C cx j phi fr regs' m.
Proof.
  intros cx j phi fr regs regs' m E2 E9 E18 E21 E23 H1 H2 H3.
  unfold ACtlCutP.FLSI, ACtlCutP.LK, ACtlCutP.b5_C in *.
  unfold ACtlCutP.FLSH, ACtlCutP.FLC, ACtlCutP.b5_PH, ACtlCutP.FSj in *.
  unfold ACtlCutP.PRO, ACtlCutP.FSb in *.
  unfold ACtlCutP.spill in *.
  unfold ACtlCut.rgv, Reusable.YG0d.spZ in *.
  unfold CK11.getr, UK11.getr in *.
  rewrite E2, E9, E18, E21, E23.
  exact (conj H1 (conj H2 H3)).
Qed.

(* HB / FLSI / LK / b5_C / IDj across the run: every cell they read lies off the two spill words; the registers
   they read are kept.  The cut-layer form of F4.v's f4_keep1 (F4.v:881). *)
Lemma f4g_d64_keep : forall (cx : ACtlCut.ctlcx) (j : nat) (phi fr A : Z) (regs regs' : bvmap 5 word)
    (m m' : word -> option byte),
  ACtlCutP.HB m phi (ACtlCutP.flen cx j) -> ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.LK cx fr j regs m ->
  ACtlCutP.b5_C cx j phi fr regs m -> ACtlCutP.IDj cx fr j m ->
  ACtlCut.rgv regs 9 A -> A.AsanRT.HIGHMEM_BEG <= A -> A + 416 <= A.AsanRT.APPMEM_END ->
  fr + ACtlCutP.FRAME_BYTES <= A -> phi + A.ACtlK.a_size (ACtlCutP.flen cx j) <= A ->
  ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) <= A ->
  LFr.munch (f4g_d64_W A) m m' -> LFr.wmono A.Img0.rsegs m m' ->
  CK11.getr regs' 2 = CK11.getr regs 2 -> CK11.getr regs' 9 = CK11.getr regs 9 ->
  CK11.getr regs' 18 = CK11.getr regs 18 -> CK11.getr regs' 21 = CK11.getr regs 21 ->
  CK11.getr regs' 23 = CK11.getr regs 23 ->
  ACtlCutP.HB m' phi (ACtlCutP.flen cx j) /\ ACtlCutP.FLSI cx j fr regs' m' /\ ACtlCutP.LK cx fr j regs' m' /\
  ACtlCutP.b5_C cx j phi fr regs' m' /\ ACtlCutP.IDj cx fr j m'.
Proof.
  intros cx j phi fr A regs regs' m m' HHB HFLSI HLK HC HID H9 HAhi HAapp Hfa Hpa Hin MU WM E2 E9 E18 E21 E23.
  assert (HKh : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HKa : A.AsanRT.APPMEM_END = 140737488355328) by reflexivity.
  assert (HFB : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA : 0 <= A < 2 ^ 64) by lia.
  assert (Hasz1 : 1 <= A.ACtlK.a_size (ACtlCutP.flen cx j)) by (unfold A.ACtlK.a_size; lia).
  assert (Hasz : ACtlCutP.flen cx j <= A.ACtlK.a_size (ACtlCutP.flen cx j)) by (unfold A.ACtlK.a_size; lia).
  pose proof (f4g_d64_W_app A HAhi ltac:(lia)) as HAW.
  pose proof (f4g_d64_W_out A) as Hout.
  (* the keeps, once each, at the old map *)
  assert (SP : forall off v, 0 <= off <= 408 -> off + 8 <= 200 \/ (208 <= off /\ off + 8 <= 240) \/ 248 <= off ->
            ACtlCutP.spill regs m off v -> ACtlCutP.spill regs m' off v).
  { intros off v Hoff Hb Hs.
    exact (F4S.f4_spill_keep regs regs A off v m m' (f4g_d64_W A) Hs H9 HA HAapp Hoff eq_refl MU
             (fun x Hx => Hout x ltac:(lia))). }
  assert (QK : forall a v, a + 8 <= A + 200 \/ (A + 208 <= a /\ a + 8 <= A + 240) \/ A + 248 <= a ->
            ACtlCutP.q64 m a v -> ACtlCutP.q64 m' a v).
  { intros a v Ha Hq. exact (F4S.f4_q64_keep (f4g_d64_W A) m m' a v Hq MU (fun x Hx => Hout x ltac:(lia))). }
  assert (BL : forall a bs, a + Z.of_nat (length bs) <= A + 200 ->
            LMem.bytes_at segs m a bs -> LMem.bytes_at segs m' a bs).
  { intros a bs Ha Hb.
    exact (A.Prog.RcAsanFPLib.fl_bytes (f4g_d64_W A) m m' a bs Hb MU (fun x Hx => Hout x ltac:(lia))). }
  assert (AK : forall p n, A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n).
  { intros p n H. exact (A.Prog.Seg.Tac_slot.sl_addr_keep m m' (f4g_d64_W A) p n H MU HAW). }
  (* HB: the record block's addressable bytes *)
  assert (HHB' : ACtlCutP.HB m' phi (ACtlCutP.flen cx j)).
  { destruct HHB as (Hnz & Had). split; [exact Hnz | exact (AK _ _ Had)]. }
  (* FLSI at the old map *)
  assert (HFLSIm : ACtlCutP.FLSI cx j fr regs m').
  { destruct HFLSI as ((HPRO & Hf128 & Hfstk & Hf144 & Hfa17) & Hf216 & Hf224 & Hf248 & (HINa & HINb) & HFLC).
    destruct HPRO as (Hf40 & Hf120 & Hf136 & Hf160 & Hf168 & Hf176 & Hf208 & Hp248 & Hfout6 & Hinb & Hing &
      Hp184 & Hp256 & Hp264 & Hp272 & Hp32).
    destruct HFLC as (Hc256 & Hc184 & Hc192 & Hc80 & Hc88 & Hc96 & Hc272 & Hc264 & Hcfg & Hcid & Hc72 & Hc64 &
      Hc56 & Hc48).
    split.
    { split.
      { split; [exact (SP 40 _ ltac:(lia) ltac:(lia) Hf40)|].
        split; [exact (SP 120 _ ltac:(lia) ltac:(lia) Hf120)|].
        split; [exact (SP 136 _ ltac:(lia) ltac:(lia) Hf136)|].
        split; [exact (SP 160 _ ltac:(lia) ltac:(lia) Hf160)|].
        split; [exact (SP 168 _ ltac:(lia) ltac:(lia) Hf168)|].
        split; [exact (SP 176 _ ltac:(lia) ltac:(lia) Hf176)|].
        split; [exact (SP 208 _ ltac:(lia) ltac:(lia) Hf208)|].
        split; [exact (SP 248 _ ltac:(lia) ltac:(lia) Hp248)|].
        split; [exact (AK _ _ Hfout6)|].
        split; [exact (BL (ACtlCut.c_p cx) (ACtlCut.c_in cx) ltac:(lia) Hinb)|].
        split; [intros Hn; exact (AK _ _ (Hing Hn))|].
        split; [exact (SP 184 _ ltac:(lia) ltac:(lia) Hp184)|].
        split; [exact (SP 256 _ ltac:(lia) ltac:(lia) Hp256)|].
        split; [exact (SP 264 _ ltac:(lia) ltac:(lia) Hp264)|].
        split; [exact (SP 272 _ ltac:(lia) ltac:(lia) Hp272)|].
        exact (SP 32 _ ltac:(lia) ltac:(lia) Hp32). }
      split; [exact (SP 128 _ ltac:(lia) ltac:(lia) Hf128)|].
      split.
      { apply (A.Prog.RcAsanFPLib.fl_stk (f4g_d64_W A) m m' fr (fr + ACtlCutP.FRAME_BYTES) Hfstk MU WM).
        intros x Hx. left. apply Hout. lia. }
      split; [exact (SP 144 _ ltac:(lia) ltac:(lia) Hf144)|].
      exact (AK _ _ Hfa17). }
    split; [exact (SP 216 _ ltac:(lia) ltac:(lia) Hf216)|].
    split; [exact (SP 224 _ ltac:(lia) ltac:(lia) Hf224)|].
    split; [exact (SP 248 _ ltac:(lia) ltac:(lia) Hf248)|].
    split; [split; [exact (AK _ _ HINa) | exact (BL (ACtlCut.c_p cx) (ACtlCut.c_in cx) ltac:(lia) HINb)]|].
    split; [exact (SP 256 _ ltac:(lia) ltac:(lia) Hc256)|].
    split; [exact (SP 184 _ ltac:(lia) ltac:(lia) Hc184)|].
    split; [exact (SP 192 _ ltac:(lia) ltac:(lia) Hc192)|].
    split; [exact (SP 80 _ ltac:(lia) ltac:(lia) Hc80)|].
    split; [exact (SP 88 _ ltac:(lia) ltac:(lia) Hc88)|].
    split; [exact (SP 96 _ ltac:(lia) ltac:(lia) Hc96)|].
    split; [exact (SP 272 _ ltac:(lia) ltac:(lia) Hc272)|].
    split; [exact (SP 264 _ ltac:(lia) ltac:(lia) Hc264)|].
    split; [exact (AK _ _ Hcfg)|].
    split; [exact (AK _ _ Hcid)|].
    split; [exact (SP 72 _ ltac:(lia) ltac:(lia) Hc72)|].
    split; [exact (SP 64 _ ltac:(lia) ltac:(lia) Hc64)|].
    split; [exact (SP 56 _ ltac:(lia) ltac:(lia) Hc56)|].
    exact (SP 48 _ ltac:(lia) ltac:(lia) Hc48). }
  (* LK at the old map: out[]'s six bytes at fr + 2624 are frame body *)
  assert (HLKm : ACtlCutP.LK cx fr j regs m').
  { destruct HLK as (Hj255 & H21 & HOURb).
    split; [exact Hj255|]. split; [exact H21|].
    refine (BL (fr + 2624) (SM.OUR (ACtlCut.c_in cx)) _ HOURb).
    rewrite SM.OUR_length. lia. }
  (* b5_C at the old map *)
  assert (HCm : ACtlCutP.b5_C cx j phi fr regs m').
  { destruct HC as (Hs23 & Hs18 & (A1 & H9a & HA1 & HSP & H232) & HPH & HFR & HKN & HFG & HFSj).
    assert (EA : A1 = A).
    { apply F4S.f4_id; [exact HA1 | exact HA |].
      transitivity (CK11.getr regs 9); [symmetry; exact H9a | exact H9]. }
    subst A1.
    split; [exact Hs23|]. split; [exact Hs18|].
    split.
    { exists A. split; [exact H9|]. split; [exact HA|].
      destruct HSP as (Hq248 & Hq256 & Hq144 & Hq184 & Hq192 & Hq80 & Hq88 & Hq96 & Hq272 & Hq264).
      split; [|exact (QK (A + 232) _ ltac:(lia) H232)].
      split; [exact (QK (A + 248) _ ltac:(lia) Hq248)|].
      split; [exact (QK (A + 256) _ ltac:(lia) Hq256)|].
      split; [exact (QK (A + 144) _ ltac:(lia) Hq144)|].
      split; [exact (QK (A + 184) _ ltac:(lia) Hq184)|].
      split; [exact (QK (A + 192) _ ltac:(lia) Hq192)|].
      split; [exact (QK (A + 80) _ ltac:(lia) Hq80)|].
      split; [exact (QK (A + 88) _ ltac:(lia) Hq88)|].
      split; [exact (QK (A + 96) _ ltac:(lia) Hq96)|].
      split; [exact (QK (A + 272) _ ltac:(lia) Hq272)|].
      exact (QK (A + 264) _ ltac:(lia) Hq264). }
    (* b5_PH: the record's 50 bytes lie in the record block, below A *)
    destruct HPH as (HPHb & HPHp).
    split.
    { split; [|exact HPHp].
      intros Hlen. refine (BL phi (SM.t_g (ACtlCut.c_in cx) j) _ (HPHb Hlen)).
      unfold SM.t_g. rewrite SM.fr50_length. lia. }
    (* b5_FR: the fragment record (72 bytes at fragb fr) is frame body *)
    destruct HFR as (HFRa & HFRb & HFRc & HFRd).
    split.
    { split; [exact (AK _ _ HFRa)|]. split; [exact (AK _ _ HFRb)|]. split; [|exact HFRd].
      refine (BL (ACtlCutP.fragb fr) _ _ HFRc). rewrite HFRd. unfold ACtlCutP.fragb. lia. }
    (* b5_KN: the kind-name table is image data far below HIGHMEM_BEG <= A *)
    destruct HKN as (HKNa & HKNb).
    split.
    { split; [|exact (AK _ _ HKNb)].
      refine (BL _ _ _ HKNa).
      assert (Hknl : (length A.Prog.reac_ctrl_kind_name_c.kind_name_bytes <= 4096)%nat) by (vm_compute; lia).
      unfold A.Prog.reac_ctrl_kind_name_c.KIND_NAME. lia. }
    (* FGj: the 72 fragment bytes at fr + 2768 *)
    destruct HFG as (HFGb & HFGok).
    split.
    { split; [|exact HFGok]. unfold ACtlCutP.FGBe in *.
      refine (BL (fr + 2768) _ _ HFGb). rewrite HFRd. lia. }
    (* FSj: the two first-fragment spills and the first fragment's body (at most 23 bytes at fr + 2880) *)
    destruct HFSj as (Hq104 & Hq112 & Hfsb & Hfsa & HFI).
    split; [exact (SP 104 _ ltac:(lia) ltac:(lia) Hq104)|].
    split; [exact (SP 112 _ ltac:(lia) ltac:(lia) Hq112)|].
    split; [|split; [exact (AK _ _ Hfsa) | exact HFI]].
    refine (BL (fr + 2880) _ _ Hfsb).
    pose proof (F4S.f4_fs_body_len (ACtlCut.c_in cx) j) as Hbl. lia. }
  (* IDj: the 38 identity bytes at fr + 2688 are frame body *)
  assert (HIDm : ACtlCutP.IDj cx fr j m').
  { destruct HID as (Hb & Hok). split; [|exact Hok].
    refine (BL (fr + 2688) _ _ Hb). rewrite F4S.f4_tID_len. lia. }
  (* the register move *)
  destruct (f4g_d64_move cx j phi fr regs regs' m' E2 E9 E18 E21 E23 HFLSIm HLKm HCm) as (HF' & HL' & HC').
  exact (conj HHB' (conj HF' (conj HL' (conj HC' HIDm)))).
Qed.

(* b5_PF across the run: every cell it names lies below A + 200 (F4.v's f4_pf_sp, F4.v:940). *)
Lemma f4g_d64_pf_keep : forall (cx : ACtlCut.ctlcx) (j : nat) (phi fr A : Z) (regs regs' : bvmap 5 word)
    (m m' : word -> option byte),
  ACtlCutP.b5_PF cx j phi fr regs m -> ACtlCut.rgv regs 9 A ->
  A.AsanRT.HIGHMEM_BEG <= A -> A + 416 <= A.AsanRT.APPMEM_END -> 0 <= fr ->
  fr + ACtlCutP.FRAME_BYTES <= A -> phi + A.ACtlK.a_size (ACtlCutP.flen cx j) <= A ->
  LFr.munch (f4g_d64_W A) m m' ->
  CK11.getr regs' 9 = CK11.getr regs 9 ->
  ACtlCutP.b5_PF cx j phi fr regs' m'.
Proof.
  intros cx j phi fr A regs regs' m m' HPF H9 HAhi HAapp Hfr0 Hfa Hpa MU E9.
  assert (HKh : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HKa : A.AsanRT.APPMEM_END = 140737488355328) by reflexivity.
  assert (HFB : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (EK : A.ACtlK.ASAN_K = A.AsanRT.ASAN_K) by reflexivity.
  assert (HA : 0 <= A < 2 ^ 64) by lia.
  assert (Hasz1 : 1 <= A.ACtlK.a_size (ACtlCutP.flen cx j)) by (unfold A.ACtlK.a_size; lia).
  assert (Hasz : ACtlCutP.flen cx j <= A.ACtlK.a_size (ACtlCutP.flen cx j)) by (unfold A.ACtlK.a_size; lia).
  pose proof (f4g_d64_W_app A HAhi ltac:(lia)) as HAW.
  assert (Hlo : forall x, x < A + 200 -> LFr.outside (f4g_d64_W A) x).
  { intros x Hx. apply f4g_d64_W_out. lia. }
  assert (QL : forall a v, a + 8 <= A + 200 -> ACtlCutP.q64 m a v -> ACtlCutP.q64 m' a v).
  { intros a v Ha Hq. exact (F4S.f4_q64_keep (f4g_d64_W A) m m' a v Hq MU (fun x Hx => Hlo x ltac:(lia))). }
  assert (BL : forall a bs, a + Z.of_nat (length bs) <= A + 200 ->
            LMem.bytes_at segs m a bs -> LMem.bytes_at segs m' a bs).
  { intros a bs Ha Hb.
    exact (A.Prog.RcAsanFPLib.fl_bytes (f4g_d64_W A) m m' a bs Hb MU (fun x Hx => Hlo x ltac:(lia))). }
  assert (AK : forall p n, A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n).
  { intros p n H. exact (A.Prog.Seg.Tac_slot.sl_addr_keep m m' (f4g_d64_W A) p n H MU HAW). }
  destruct HPF as (A1 & H9a & HA1 & Hlong & H8819).
  assert (EA : A1 = A).
  { apply F4S.f4_id; [exact HA1 | exact HA |].
    transitivity (CK11.getr regs 9); [symmetry; exact H9a | exact H9]. }
  subst A1.
  exists A. split; [exact (eq_trans E9 H9)|]. split; [exact HA|].
  split.
  - (* the record's 38-byte prefix and t_phi lie in the record block, below A *)
    intros Hle. destruct (Hlong Hle) as ((rb & Hrb & Hrbl) & Hphib).
    split.
    + exists (firstn 38 rb). split; [|rewrite length_firstn; lia].
      refine (BL phi _ _ (F4S.f4_bytes_first m phi rb 38 Hrb)).
      rewrite length_firstn. lia.
    + refine (BL phi _ _ Hphib).
      (* t_phi j is a firstn of flen j bytes (F4.v's f4_tphi_len, over c_in cx) *)
      assert (Hl : Z.of_nat (length (SM.t_phi (ACtlCut.c_in cx) j)) <= ACtlCutP.flen cx j).
      { assert (H0 : 0 <= ACtlCutP.flen cx j) by lia.
        unfold ACtlCutP.flen, SM.t_len, SM.t_phi, SM.f_phi in *.
        rewrite length_firstn, Nat2Z.inj_min, Z2Nat.id by lia. lia. }
      lia.
  - intros Ht. destruct (H8819 Ht) as
      ((field16 & v14 & v15 & v16 & v17 & Hu16 & Hb14 & Hb15 & Hb16 & Hb17 & Hv14 & Hv15 & Hv16 & Hv17 &
        Hs14 & Hs15 & Hs16 & Hs17 & Ef & Ek) &
       (ls & rs & Hq72 & Hls & Hlsl & Hrs & Hrsl & Hcm & Had) &
       (ls2 & rs2 & Hq64 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hcm2 & Had2)).
    unfold ACtlCutP.u16, ACtlCutP.b8 in *.
    (* the metadata bytes of phi + 14 .. phi + 17 lie below HIGHMEM_BEG <= A *)
    pose proof (LMem.bytes_at_bound segs m (phi + 14) _ Hb14) as (Hp14 & _).
    assert (Hshk : forall k, 14 <= k <= 17 -> Z.shiftr (phi + k) 3 + A.AsanRT.ASAN_K + 1 <= A).
    { intros k Hk. apply F4S.f4_sh_below; [lia | exact HAhi]. }
    pose proof (Hshk 14 ltac:(lia)) as Hk14. pose proof (Hshk 15 ltac:(lia)) as Hk15.
    pose proof (Hshk 16 ltac:(lia)) as Hk16. pose proof (Hshk 17 ltac:(lia)) as Hk17.
    split; [|split].
    + exists field16, v14, v15, v16, v17.
      split; [refine (BL _ _ _ Hu16); rewrite LMem.length_le2; lia|].
      split; [refine (BL _ _ _ Hb14); cbn [length]; lia|].
      split; [refine (BL _ _ _ Hb15); cbn [length]; lia|].
      split; [refine (BL _ _ _ Hb16); cbn [length]; lia|].
      split; [refine (BL _ _ _ Hb17); cbn [length]; lia|].
      split; [exact Hv14|]. split; [exact Hv15|]. split; [exact Hv16|]. split; [exact Hv17|].
      split; [refine (BL _ _ _ Hs14); cbn [length]; lia|].
      split; [refine (BL _ _ _ Hs15); cbn [length]; lia|].
      split; [refine (BL _ _ _ Hs16); cbn [length]; lia|].
      split; [refine (BL _ _ _ Hs17); cbn [length]; lia|].
      split; [exact Ef | exact Ek].
    + exists (firstn 6 ls), (firstn 6 rs).
      split; [exact (QL (A + 72) _ ltac:(lia) Hq72)|].
      split; [refine (BL (fr + 186) _ _ (F4S.f4_bytes_first m (fr + 186) ls 6 Hls));
              rewrite length_firstn; lia|].
      split; [rewrite length_firstn; lia|].
      split; [refine (BL phi _ _ (F4S.f4_bytes_first m phi rs 6 Hrs)); rewrite length_firstn; lia|].
      split; [rewrite length_firstn; lia|].
      split; [rewrite F4S.f4_mcmp_firstn; exact Hcm|].
      exact (AK _ _ Had).
    + exists (firstn 6 ls2), (firstn 6 rs2).
      split; [exact (QL (A + 64) _ ltac:(lia) Hq64)|].
      split; [refine (BL (fr + 180) _ _ (F4S.f4_bytes_first m (fr + 180) ls2 6 Hls2));
              rewrite length_firstn; lia|].
      split; [rewrite length_firstn; lia|].
      split; [refine (BL (phi + 6) _ _ (F4S.f4_bytes_first m (phi + 6) rs2 6 Hrs2));
              rewrite length_firstn; lia|].
      split; [rewrite length_firstn; lia|].
      split; [rewrite F4S.f4_mcmp_firstn; exact Hcm2|].
      exact (AK _ _ Had2).
Qed.

(* The transport, once: the entry body's carried predicates of C_A81dfc_at (ACtlCutP.v:2004-2009) at (regs, m)
   move to (regs', m') when m' agrees with m off the two spill words (the run's write_to_mem) and registers
   2 3 4 8 9 18 19 21 23 26 are kept. *)
Lemma f4g_d64_body_keep : forall (cx : ACtlCut.ctlcx) (j : nat) (phi fr A : Z) (regs regs' : bvmap 5 word)
    (m m' : word -> option byte),
  ACtlCutP.FRAC B cx fr fr regs m -> ACtlCutP.HB m phi (ACtlCutP.flen cx j) -> ACtlCutP.FLSI cx j fr regs m ->
  ACtlCutP.LK cx fr j regs m -> ACtlCutP.b5_C cx j phi fr regs m ->
  ACtlCutP.u32 m (fr + 176) (SM.t_k (ACtlCut.c_in cx) j) -> ACtlCutP.IDj cx fr j m ->
  ACtlCutP.b5_PF cx j phi fr regs m ->
  ACtlCut.rgv regs 9 A -> A.AsanRT.HIGHMEM_BEG <= A -> A + 416 <= A.AsanRT.APPMEM_END -> 0 <= fr ->
  fr + ACtlCutP.FRAME_BYTES <= A -> fr + 4096 <= A -> phi + A.ACtlK.a_size (ACtlCutP.flen cx j) <= A ->
  ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) <= A ->
  LFr.munch (f4g_d64_W A) m m' -> LFr.wmono A.Img0.rsegs m m' ->
  CK11.getr regs' 2 = CK11.getr regs 2 -> CK11.getr regs' 3 = CK11.getr regs 3 ->
  CK11.getr regs' 4 = CK11.getr regs 4 -> CK11.getr regs' 8 = CK11.getr regs 8 ->
  CK11.getr regs' 9 = CK11.getr regs 9 -> CK11.getr regs' 18 = CK11.getr regs 18 ->
  CK11.getr regs' 19 = CK11.getr regs 19 -> CK11.getr regs' 21 = CK11.getr regs 21 ->
  CK11.getr regs' 23 = CK11.getr regs 23 -> CK11.getr regs' 26 = CK11.getr regs 26 ->
  ACtlCutP.FRAC B cx fr fr regs' m' /\ ACtlCutP.HB m' phi (ACtlCutP.flen cx j) /\
  ACtlCutP.FLSI cx j fr regs' m' /\ ACtlCutP.LK cx fr j regs' m' /\ ACtlCutP.b5_C cx j phi fr regs' m' /\
  ACtlCutP.u32 m' (fr + 176) (SM.t_k (ACtlCut.c_in cx) j) /\ ACtlCutP.IDj cx fr j m' /\
  ACtlCutP.b5_PF cx j phi fr regs' m'.
Proof.
  intros cx j phi fr A regs regs' m m' HFRAC HHB HFLSI HLK HC Hu32 HID HPF H9 HAh HAa Hfr0 HfrA Hfr4096 HphiA HinA MU WM
    E2 E3 E4 E8 E9 E18 E19 E21 E23 E26.
  assert (HKh : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HKa : A.AsanRT.APPMEM_END = 140737488355328) by reflexivity.
  assert (HFB : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  destruct (f4g_d64_keep cx j phi fr A regs regs' m m' HHB HFLSI HLK HC HID H9 HAh HAa HfrA HphiA HinA MU WM
              E2 E9 E18 E21 E23) as (KHB & KFLSI & KLK & KC & KID).
  split; [exact (f4g_d64_frac_keep cx fr fr A regs regs' m m' HFRAC H9 ltac:(lia) HAh Hfr4096 MU
                  E2 E3 E4 E8 E9 E19 E26)|].
  split; [exact KHB|]. split; [exact KFLSI|]. split; [exact KLK|]. split; [exact KC|].
  split.
  { apply (F4S.f4_u32_keep (f4g_d64_W A) m m' (fr + 176) _ Hu32 MU). intros x Hx. apply f4g_d64_W_out. lia. }
  split; [exact KID|].
  exact (f4g_d64_pf_keep cx j phi fr A regs regs' m m' HPF H9 HAh HAa Hfr0 HfrA HphiA MU E9).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The arm. *)

(* entry 0x81dfc: the three inline runs of seg_F4_d64 (F4d64F.v), exits 0x81e88 / 0x81ea4 / 0x81ea8. *)
Lemma glue_F4_d64 : forall POST (j : nat),
  CF POST (ix_cut C_A81e88_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ea4_at [Z.of_nat j]) ->
  CF POST (ix_cut C_A81ea8_at [Z.of_nat j]) -> CF POST (ix_cut C_A81dfc_at [Z.of_nat j]).
Proof.
  intros POST j Hdf0 He0c He10 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:234-236; C_A81dfc_at, ACtlCutP.v:1998-2009) *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81dfc_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HPerm & Hcn & Hj255 & HHB & HFLSI & HLK & HC & HFC & R10 & R25 & R22 & Hu32 &
    HID & HPF).
  pose proof HC as (R23 & R18 & _ & (HPHb & _) & _).
  pose proof HFRAC as (? & ? & _ & _ & _ & _ & _ & _ & _ & _ & R26 & _).
  (* G2: the spill base, the bounds, the stack window *)
  destruct (f4g_d64_frac_base cx fr fr regs3 mem3 HFRAC) as (Asp & R9 & HAspR).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  destruct (f4g_d64_bounds cx _ ly3 S3 W3 mem3 md3 k fr fr Asp phi j regs3 HB HJ Hin6 Efr HFRAC R9 HAspR HPerm)
    as (HAh & HAa & Hfr0 & HfrA & HphiA & HinA & HAlo & HAhi & Hflen0 & Hfr4096).
  assert (HHBv : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAPPv : A.AsanRT.APPMEM_END = 140737488355328) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (Hasz : ACtlCutP.flen cx j <= A.ACtlK.a_size (ACtlCutP.flen cx j)) by (unfold A.ACtlK.a_size; lia).
  pose proof HHB as (_ & HAd). pose proof HAd as (Hphi0 & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  assert (HSTK : LFr.stk A.Img0.rsegs mem3 (Asp + 200) (Asp + 248)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hpres a ltac:(lia)) as [_ (b & Hb)].
    change (LMem.wa a) with (Z_to_bv 64 a). split.
    - unfold wview. rewrite Hb. discriminate.
    - exists b. unfold LMem.mrd. rewrite Hb. reflexivity. }
  assert (Hvis : forall lo n, Asp + 200 <= lo -> lo + n <= Asp + 248 ->
                   LEF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo n).
  { intros lo n H1 H2. apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    exact (proj1 (Hpres a ltac:(lia))). }
  pose proof (F4S.f4_store_ok_stku mem3 mem3 (Asp + 200) (Asp + 248) (Asp + 200) 8%nat HSTK
                (LFr.wmono_refl A.Img0.rsegs mem3) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HS200.
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's start map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81dfc_at [Z.of_nat j])) with 0x81dfc.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 CK11.fp_regs (Z_to_bv 64 0x81dfc)
           CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  (* G4: the case split of Seg/F4.v:3316 / :3389 *)
  destruct (Z_le_gt_dec (ACtlCutP.flen cx j) 49) as [Hshort|Hlong].
  - (* ---- the short arm (flen <= 49): exit 0x81e88 ---- *)
    pose proof (@F4R.f4_d64_short_run_F (UK11.mkFP CK11.fp_regs CK11.fp_csr) regs3 mem3
                  (SM.t_k (ACtlCut.c_in cx) j) phi (ACtlCutP.flen cx j) Asp
                  (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                  R10 R25 R9 R18 Hflen0 Hshort HS200 (Hvis (Asp + 200) 8 ltac:(lia) ltac:(lia))) as HRUN.
    pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
    rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
    apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
             _ (POST cx) HFS (A.ProgBridge.fp_avoids_RNG_W _)).
    (* G5 *)
    intros ms' md' HQ0 Hhid Hsbm.
    destruct HQ0 as (R & pc' & mem' & Ems & Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K26 & K23 & K18 & K24 &
      Hmem).
    subst ms' pc'.
    assert (Hmem' : mem' = write_to_mem mem3 (LMem.wa (Asp + 200)) (LMem.le8 (Z_to_bv 64 (phi + 18))))
      by exact Hmem.
    clear Hmem.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81e88_at [Z.of_nat j])) R mem' md') (POST cx)).
    destruct (f4g_d64_wr1 mem3 Asp (Z_to_bv 64 (phi + 18)) ltac:(lia) ltac:(lia)) as (MU & WM & Hgr).
    rewrite <- Hmem' in MU, WM, Hgr.
    assert (Hq200 : ACtlCutP.q64 mem' (Asp + 200) (phi + 18)).
    { rewrite Hmem'. unfold ACtlCutP.q64.
      apply LMem.bytes_at_write_same; [lia | rewrite LMem.length_le8; lia]. }
    destruct (f4g_d64_body_keep cx j phi fr Asp regs3 R mem3 mem' HFRAC HHB HFLSI HLK HC Hu32 HID HPF R9 HAh HAa
                Hfr0 HfrA Hfr4096 HphiA HinA MU WM K2 K3 K4 K8 K9 K18 K19 K21 K23 K26)
      as (KFRAC & KHB & KFLSI & KLK & KC & Ku32 & KID & KPF).
    apply (Hdf0 cx [Z.of_nat j] fr k ly3 S3 W3 R mem' md' HB).
    + (* journal: the store lies in the stack window *)
      apply (f4g_d64_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Asp HJ MU Hgr Hhid Hsbm); lia.
    + (* frames: own6 on both cuts *)
      exact HF.
    + (* the frame law: own6 on both cuts *)
      exact HL.
    + (* the event bound: the same kmax on both cuts *)
      exact Hk.
    + (* the exit body, C_A81e88_at (ACtlCutP.v:2039-2048) *)
      split; [reflexivity|].
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81e88_at ACtlCutP.ixn nth].
      rewrite Nat2Z.id.
      split; [exact KFRAC|].
      unfold ACtlCutP.b5_body. exists phi. cbv beta.
      split; [exact HPerm|]. split; [exact Hcn|]. split; [exact Hj255|].
      split; [exact KHB|]. split; [exact KFLSI|]. split; [exact KLK|]. split; [exact KC|].
      split; [lia|].
      split; [exact K24|].
      split; [exact Ku32|]. split; [exact KID|].
      split; [|exact KPF].
      (* b5_F17: the word 0x81e04 just stored at [Asp + 200] *)
      exists Asp. split; [exact (eq_trans K9 R9)|]. split; [exact HAspR | exact Hq200].
    + (* ctl_rt_C: the store is above HIGHMEM_BEG; ly3 S3 kept *)
      exact (f4g_d64_ctlrt_keep ly3 S3 mem3 mem' Asp Hrt MU WM HAh ltac:(lia)).
  - (* ---- the long arms (50 <= flen): the instrumented checks of the record bytes phi + 12 / phi + 13 ---- *)
    assert (Hlong' : 50 <= ACtlCutP.flen cx j) by lia.
    assert (Hglen : length (SM.t_g (ACtlCut.c_in cx) j) = 50%nat) by (unfold SM.t_g; apply SM.fr50_length).
    pose proof (HPHb Hlong') as HGbytes.
    pose proof (F4S.f4_ba_nth mem3 phi (SM.t_g (ACtlCut.c_in cx) j) 12 HGbytes ltac:(rewrite Hglen; lia)) as Hb12.
    pose proof (F4S.f4_ba_nth mem3 phi (SM.t_g (ACtlCut.c_in cx) j) 13 HGbytes ltac:(rewrite Hglen; lia)) as Hb13.
    change (Z.of_nat 12) with 12 in Hb12. change (Z.of_nat 13) with 13 in Hb13.
    pose proof (F4S.f4_sh_at mem3 phi (ACtlCutP.flen cx j) 12 HAd Hlong' ltac:(lia)) as Hsh12.
    pose proof (F4S.f4_sh_at mem3 phi (ACtlCutP.flen cx j) 13 HAd Hlong' ltac:(lia)) as Hsh13.
    pose proof (F4S.f4_byte_range (nth 12 (SM.t_g (ACtlCut.c_in cx) j) RCP.cp_z)) as Hv12r.
    pose proof (F4S.f4_byte_range (nth 13 (SM.t_g (ACtlCut.c_in cx) j) RCP.cp_z)) as Hv13r.
    assert (Hp12 : 0 <= phi + 12 < A.AsanRT.APPMEM_END) by lia.
    assert (Hp13 : 0 <= phi + 13 < A.AsanRT.APPMEM_END) by lia.
    pose proof (F4S.f4_sh_below (phi + 12) (Asp + 200) Hp12 ltac:(lia)) as Hsa12.
    pose proof (F4S.f4_sh_below (phi + 13) (Asp + 200) Hp13 ltac:(lia)) as Hsa13.
    (* the footprint of the checks: the record bytes and their shadow, visible as the live block (phi, flen j)
       and its shadow cover *)
    assert (Hin : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
    assert (Hreq : Reusable.YG00.req_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j).
    { unfold Reusable.YG00.req_size. rewrite (proj2 (Z.eqb_neq (ACtlCutP.flen cx j) 0) ltac:(lia)). reflexivity. }
    assert (Hhi2 : phi + 12 + 2 <= phi + Reusable.YG00.req_size (ACtlCutP.flen cx j)) by (rewrite Hreq; lia).
    pose proof (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 12) 2
                  HAR Hin ltac:(lia) Hhi2) as HV.
    destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 12) 2
                HAR Hin ltac:(lia) Hhi2 ltac:(lia)) as [HSV|HSV]; [lia|].
    destruct (f4g_d64_sh_cover (phi + 12) 0 ltac:(lia) ltac:(lia)) as (C12a & C12b).
    destruct (f4g_d64_sh_cover (phi + 12) 1 ltac:(lia) ltac:(lia)) as (C13a & C13b).
    rewrite Z.add_0_r in C12a, C12b.
    replace (phi + 12 + 1) with (phi + 13) in C13a, C13b by lia.
    pose proof (A.ProgBridge.rng_of_visible _ _ _
                  (A.ProgBridge.range_visible_sub _ _ _ (phi + 12) 1 HV ltac:(lia) ltac:(lia) ltac:(lia))) as V12.
    pose proof (A.ProgBridge.rng_of_visible _ _ _
                  (A.ProgBridge.range_visible_sub _ _ _ (phi + 13) 1 HV ltac:(lia) ltac:(lia) ltac:(lia))) as V13.
    pose proof (A.ProgBridge.rng_of_visible _ _ _
                  (A.ProgBridge.range_visible_sub _ _ _ (Z.shiftr (phi + 12) 3 + A.AsanRT.ASAN_K) 1 HSV
                     C12a ltac:(lia) ltac:(lia))) as Vs12.
    pose proof (A.ProgBridge.rng_of_visible _ _ _
                  (A.ProgBridge.range_visible_sub _ _ _ (Z.shiftr (phi + 13) 3 + A.AsanRT.ASAN_K) 1 HSV
                     C13a ltac:(lia) ltac:(lia))) as Vs13.
    destruct (Z.eq_dec (bv_unsigned (nth 12 (SM.t_g (ACtlCut.c_in cx) j) RCP.cp_z)) 136) as [H12eq|H12ne].
    + (* ---- byte 12 is 136: the check of byte 13, the spill [Asp + 240], exit 0x81ea8 ---- *)
      assert (H8819 : SM.b2z (SM.t_8819 (ACtlCut.c_in cx) j) =
                      (if bv_unsigned (nth 13 (SM.t_g (ACtlCut.c_in cx) j) RCP.cp_z) =? 25 then 1 else 0)).
      { unfold SM.b2z, SM.t_8819, SM.t_big.
        assert (E1 : (50 <=? SM.t_len (ACtlCut.c_in cx) j) = true) by (apply Z.leb_le; exact Hlong').
        assert (E2 : (RCP.cp_v (SM.t_g (ACtlCut.c_in cx) j) 12 =? 0x88) = true) by (apply Z.eqb_eq; exact H12eq).
        rewrite E1, E2. reflexivity. }
      pose proof (@F4R.f4_d64_136_run_F (UK11.mkFP CK11.fp_regs CK11.fp_csr) regs3 mem3
                    (SM.t_k (ACtlCut.c_in cx) j) phi (ACtlCutP.flen cx j) Asp (SM.b2z (SM.t_8819 (ACtlCut.c_in cx) j))
                    (nth 12 (SM.t_g (ACtlCut.c_in cx) j) RCP.cp_z) (nth 13 (SM.t_g (ACtlCut.c_in cx) j) RCP.cp_z)
                    (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                    R10 R25 R9 R18 R23 R26 HAspR ltac:(lia) Hphi0 ltac:(lia) Hlong Hv12r Hv13r Hsa12 Hsa13 H12eq
                    H8819 HS200 HSTK Hsh12 Hsh13 Hb12 Hb13
                    (Hvis (Asp + 200) 8 ltac:(lia) ltac:(lia)) (Hvis (Asp + 240) 8 ltac:(lia) ltac:(lia))
                    Vs12 V12 Vs13 V13) as HRUN.
      pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
      rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
      apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3
               (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx) HFS (A.ProgBridge.fp_avoids_RNG_W _)).
      intros ms' md' HQ0 Hhid Hsbm.
      destruct HQ0 as (R & pc' & mem' & Ems & Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K26 & K23 & K18 & K22 &
        K25 & K24 & Hmem).
      subst ms' pc'.
      assert (Hmem' : mem' = write_to_mem (write_to_mem mem3 (LMem.wa (Asp + 200)) (LMem.le8 (Z_to_bv 64 (phi + 18))))
                               (LMem.wa (Asp + 240)) (LMem.le8 (Z_to_bv 64 (SM.b2z (SM.t_8819 (ACtlCut.c_in cx) j)))))
        by exact Hmem.
      clear Hmem.
      change (Reusable.YA0n.SRr segs W3
                (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81ea8_at [Z.of_nat j])) R mem' md') (POST cx)).
      destruct (f4g_d64_wr2 mem3 Asp (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 (SM.b2z (SM.t_8819 (ACtlCut.c_in cx) j)))
                  ltac:(lia) ltac:(lia)) as (MU & WM & Hgr).
      rewrite <- Hmem' in MU, WM, Hgr.
      assert (Hq240 : ACtlCutP.q64 mem' (Asp + 240) (SM.b2z (SM.t_8819 (ACtlCut.c_in cx) j))).
      { rewrite Hmem'. unfold ACtlCutP.q64.
        apply LMem.bytes_at_write_same; [lia | rewrite LMem.length_le8; lia]. }
      assert (Hq200 : ACtlCutP.q64 mem' (Asp + 200) (phi + 18)).
      { rewrite Hmem'. unfold ACtlCutP.q64. apply LMem.bytes_at_write_other;
          [ apply LMem.bytes_at_write_same; [lia | rewrite LMem.length_le8; lia] | lia
          | rewrite LMem.length_le8; lia | rewrite !LMem.length_le8; lia ]. }
      destruct (f4g_d64_body_keep cx j phi fr Asp regs3 R mem3 mem' HFRAC HHB HFLSI HLK HC Hu32 HID HPF R9 HAh HAa
                  Hfr0 HfrA Hfr4096 HphiA HinA MU WM K2 K3 K4 K8 K9 K18 K19 K21 K23 K26)
        as (KFRAC & KHB & KFLSI & KLK & KC & Ku32 & KID & KPF).
      apply (He10 cx [Z.of_nat j] fr k ly3 S3 W3 R mem' md' HB).
      * (* journal: both stores lie in the stack window *)
        apply (f4g_d64_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Asp HJ MU Hgr Hhid Hsbm); lia.
      * exact HF.
      * exact HL.
      * exact Hk.
      * (* the exit body, C_A81ea8_at (ACtlCutP.v:2066-2076) *)
        split; [reflexivity|].
        cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81ea8_at ACtlCutP.ixn nth].
        rewrite Nat2Z.id.
        split; [exact KFRAC|].
        unfold ACtlCutP.b5_body. exists phi. cbv beta.
        split; [exact HPerm|]. split; [exact Hcn|]. split; [exact Hj255|].
        split; [exact KHB|]. split; [exact KFLSI|]. split; [exact KLK|]. split; [exact KC|].
        split; [exact Hlong'|].
        split; [exact (eq_trans K22 (R22 Hlong'))|].
        split; [exact K24|].
        split; [exact (eq_trans K25 R25)|].
        (* b5_sp 240: the word 0x81e4c just stored at [Asp + 240] *)
        split; [exists Asp; split; [exact (eq_trans K9 R9)|]; split; [exact HAspR | exact Hq240]|].
        split; [exact Ku32|]. split; [exact KID|].
        (* b5_F17: the word 0x81e04 stored at [Asp + 200], which the 0x81e4c store misses *)
        split; [exists Asp; split; [exact (eq_trans K9 R9)|]; split; [exact HAspR | exact Hq200]|].
        split; [|exact KPF].
        (* b5_W240: the word at [Asp + 240] is b2z (t_8819 j) *)
        exists Asp. split; [exact (eq_trans K9 R9)|]. split; [exact HAspR|].
        exists (SM.b2z (SM.t_8819 (ACtlCut.c_in cx) j)). split; [exact Hq240|].
        destruct (SM.t_8819 (ACtlCut.c_in cx) j); cbv [SM.b2z]; repeat split; intros; try lia; discriminate.
      * exact (f4g_d64_ctlrt_keep ly3 S3 mem3 mem' Asp Hrt MU WM HAh ltac:(lia)).
    + (* ---- byte 12 is not 136: exit 0x81ea4 ---- *)
      assert (H8819f : SM.t_8819 (ACtlCut.c_in cx) j = false).
      { unfold SM.t_8819.
        assert (E2 : (RCP.cp_v (SM.t_g (ACtlCut.c_in cx) j) 12 =? 0x88) = false) by (apply Z.eqb_neq; exact H12ne).
        rewrite E2. rewrite Bool.andb_false_r. reflexivity. }
      pose proof (@F4R.f4_d64_n136_run_F (UK11.mkFP CK11.fp_regs CK11.fp_csr) regs3 mem3
                    (SM.t_k (ACtlCut.c_in cx) j) phi (ACtlCutP.flen cx j) Asp
                    (nth 12 (SM.t_g (ACtlCut.c_in cx) j) RCP.cp_z)
                    (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                    R10 R25 R9 R18 R23 R26 HAspR ltac:(lia) Hphi0 ltac:(lia) Hlong Hv12r Hsa12 H12ne HS200 Hsh12 Hb12
                    (Hvis (Asp + 200) 8 ltac:(lia) ltac:(lia)) Vs12 V12) as HRUN.
      pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
      rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
      apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3
               (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx) HFS (A.ProgBridge.fp_avoids_RNG_W _)).
      intros ms' md' HQ0 Hhid Hsbm.
      destruct HQ0 as (R & pc' & mem' & Ems & Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K26 & K23 & K18 & K22 &
        K25 & K24 & Hmem).
      subst ms' pc'.
      assert (Hmem' : mem' = write_to_mem mem3 (LMem.wa (Asp + 200)) (LMem.le8 (Z_to_bv 64 (phi + 18))))
        by exact Hmem.
      clear Hmem.
      change (Reusable.YA0n.SRr segs W3
                (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81ea4_at [Z.of_nat j])) R mem' md') (POST cx)).
      destruct (f4g_d64_wr1 mem3 Asp (Z_to_bv 64 (phi + 18)) ltac:(lia) ltac:(lia)) as (MU & WM & Hgr).
      rewrite <- Hmem' in MU, WM, Hgr.
      assert (Hq200 : ACtlCutP.q64 mem' (Asp + 200) (phi + 18)).
      { rewrite Hmem'. unfold ACtlCutP.q64.
        apply LMem.bytes_at_write_same; [lia | rewrite LMem.length_le8; lia]. }
      destruct (f4g_d64_body_keep cx j phi fr Asp regs3 R mem3 mem' HFRAC HHB HFLSI HLK HC Hu32 HID HPF R9 HAh HAa
                  Hfr0 HfrA Hfr4096 HphiA HinA MU WM K2 K3 K4 K8 K9 K18 K19 K21 K23 K26)
        as (KFRAC & KHB & KFLSI & KLK & KC & Ku32 & KID & KPF).
      apply (He0c cx [Z.of_nat j] fr k ly3 S3 W3 R mem' md' HB).
      * apply (f4g_d64_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Asp HJ MU Hgr Hhid Hsbm); lia.
      * exact HF.
      * exact HL.
      * exact Hk.
      * (* the exit body, C_A81ea4_at (ACtlCutP.v:2052-2062) *)
        split; [reflexivity|].
        cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81ea4_at ACtlCutP.ixn nth].
        rewrite Nat2Z.id.
        split; [exact KFRAC|].
        unfold ACtlCutP.b5_body. exists phi. cbv beta.
        split; [exact HPerm|]. split; [exact Hcn|]. split; [exact Hj255|].
        split; [exact KHB|]. split; [exact KFLSI|]. split; [exact KLK|]. split; [exact KC|].
        split; [exact Hlong'|].
        split; [exact (eq_trans K22 (R22 Hlong'))|].
        split; [exact K24|].
        split; [exact (eq_trans K25 R25)|].
        split; [exact H8819f|].
        split; [exact Ku32|]. split; [exact KID|].
        split; [|exact KPF].
        (* b5_F17: the word 0x81e04 just stored at [Asp + 200] *)
        exists Asp. split; [exact (eq_trans K9 R9)|]. split; [exact HAspR | exact Hq200].
      * exact (f4g_d64_ctlrt_keep ly3 S3 mem3 mem' Asp Hrt MU WM HAh ltac:(lia)).
Qed.


(* ---------------------------------------------------------------------------------------------------------
   Helpers of glue_F4_dbc (prefix f4g_dbc_). *)

Lemma f4g_dbc_mkR_of : forall regs : bvmap 5 word, Lib.Regs6ss.mkR_of regs =
  LFr.mkR (CK11.getr regs 1) (CK11.getr regs 2) (CK11.getr regs 3) (CK11.getr regs 4) (CK11.getr regs 5)
    (CK11.getr regs 6) (CK11.getr regs 7) (CK11.getr regs 8) (CK11.getr regs 9) (CK11.getr regs 10)
    (CK11.getr regs 11) (CK11.getr regs 12) (CK11.getr regs 13) (CK11.getr regs 14) (CK11.getr regs 15)
    (CK11.getr regs 16) (CK11.getr regs 17) (CK11.getr regs 18) (CK11.getr regs 19) (CK11.getr regs 20)
    (CK11.getr regs 21) (CK11.getr regs 22) (CK11.getr regs 23) (CK11.getr regs 24) (CK11.getr regs 25)
    (CK11.getr regs 26) (CK11.getr regs 27) (CK11.getr regs 28) (CK11.getr regs 29) (CK11.getr regs 30)
    (CK11.getr regs 31).
Proof. intros regs. reflexivity. Qed.

Lemma f4g_dbc_bv_eq : forall a b, Z_to_bv 64 a = Z_to_bv 64 b -> - 2 ^ 20 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 - 2 ^ 20 ->
  a = b.
Proof.
  intros a b E Ha Hb. apply (f_equal (@bv_unsigned 64)) in E. rewrite !Z_to_bv_unsigned in E.
  unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
  assert (P : 2 ^ 64 = 18446744073709551616) by reflexivity. rewrite P in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma f4g_dbc_xbytes : forall (m m' : word -> option byte) (a : Z) (bs : list byte),
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     LMem.mrd segs m' (LMem.wa (a + i)) = LMem.mrd segs m (LMem.wa (a + i))) ->
  LMem.bytes_at segs m a bs -> LMem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs E (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (E (Z.of_nat i)) by lia. exact (H2 i Hi).
Qed.

Lemma f4g_dbc_xq64 : forall (m m' : word -> option byte) (a v : Z),
  (forall i, 0 <= i < 8 -> LMem.mrd segs m' (LMem.wa (a + i)) = LMem.mrd segs m (LMem.wa (a + i))) ->
  ACtlCutP.q64 m a v -> ACtlCutP.q64 m' a v.
Proof.
  intros m m' a v E H. unfold ACtlCutP.q64 in *. apply (f4g_dbc_xbytes m); [|exact H].
  rewrite LMem.length_le8. intros i Hi. apply E. lia.
Qed.

Lemma f4g_dbc_xaddr : forall (m m' : word -> option byte) (p n : Z),
  (forall i, 0 <= i < n -> LMem.mrd segs m' (LMem.wa (A.AsanRT.shadow_addr (p + i))) =
                            LMem.mrd segs m (LMem.wa (A.AsanRT.shadow_addr (p + i)))) ->
  A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n.
Proof.
  intros m m' p n E (H0 & H1 & H2 & H3). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H3 i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|].
  exists b. split; [|exact Hok]. rewrite <- Hb. exact (E i Hi).
Qed.

Lemma f4g_dbc_spill : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) (A off v : Z),
  CK11.getr regs 9 = Z_to_bv 64 A -> CK11.getr regs' 9 = Z_to_bv 64 A ->
  0 <= A -> A + off + 8 <= 2 ^ 64 - 2 ^ 20 -> 0 <= off <= 2 ^ 20 ->
  (forall i, 0 <= i < 8 ->
     LMem.mrd segs m' (LMem.wa (A + off + i)) = LMem.mrd segs m (LMem.wa (A + off + i))) ->
  ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' A off v R9 R9' HA0 HA1 Hoff E (A1 & R1 & Hq).
  assert (EA : A1 = A).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite LMem.length_le8 in Hq1.
    apply f4g_dbc_bv_eq; [unfold ACtlCut.rgv in R1; rewrite <- R1; exact R9 | lia | lia]. }
  subst A1. exists A. split; [exact R9'|]. exact (f4g_dbc_xq64 m m' (A + off) v E Hq).
Qed.

Lemma f4g_dbc_bytes_of_pres : forall (m : word -> option byte) (n : nat) (a : Z),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> exists b, LMem.mrd segs m (LMem.wa (a + i)) = Some b) ->
  exists bs, LMem.bytes_at segs m a bs /\ length bs = n.
Proof.
  intros m n. induction n as [|n IH]; intros a Ha Hn H.
  - exists []. split; [|reflexivity]. split; [exact Ha|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (H 0 ltac:(lia)) as (b & Hb). rewrite Z.add_0_r in Hb.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & (_ & Hbl & Hbs) & Hl).
    { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply H. lia. }
    exists (b :: bs). split; [|cbn [length]; rewrite Hl; reflexivity].
    split; [exact Ha|]. split; [cbn [length]; rewrite Hl; lia|].
    intros [|i] Hi; cbn [nth_error].
    + replace (a + Z.of_nat 0) with a by lia. exact Hb.
    + rewrite <- (Hbs i ltac:(cbn [length] in Hi; lia)). f_equal. f_equal. lia.
Qed.

Lemma f4g_dbc_pres : forall (H : word -> bool) (m : word -> option byte) (a : Z),
  Reusable.YG0n.apresent H m a ->
  H (Z_to_bv 64 a) = false /\ (exists b, LMem.mrd segs m (LMem.wa a) = Some b) /\
  wview segs m (LMem.wa a) <> None.
Proof.
  intros H m a (Hh & b & Hb). split; [exact Hh|]. split.
  - exists b. unfold LMem.mrd, LMem.wa. rewrite Hb. reflexivity.
  - unfold wview, LMem.wa. rewrite Hb. discriminate.
Qed.

Lemma f4g_dbc_kept : forall ly3 S3 (W3 W2 : Reusable.YA0n.world segs) (m2 mem2 : word -> option byte)
    slo shi (E : Z -> Prop) x,
  Reusable.YCbq.acall_kept segs B ly3 S3 W3 m2 W2 mem2 slo shi E ->
  Reusable.YA0n.wle W3 W2 ->
  0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
  A.ProgWorld.kept_class B ly3 S3 slo shi E x ->
  LMem.mrd segs mem2 (LMem.wa x) = LMem.mrd segs m2 (LMem.wa x).
Proof.
  intros ly3 S3 W3 W2 m2 mem2 slo shi E x HK Hle Hx Hv Hc.
  apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 m2 mem2 slo shi E HK Hle (LMem.wa x)).
  - exact Hv.
  - rewrite (LMem.wa_unsigned x Hx). exact Hc.
Qed.

Lemma f4g_dbc_st : forall WR (m m' : word -> option byte) x,
  LFr.munch WR m m' -> 0 <= x < 2 ^ 64 -> LFr.outside WR x ->
  LMem.mrd segs m' (LMem.wa x) = LMem.mrd segs m (LMem.wa x).
Proof.
  intros WR m m' x HM Hx Ho. unfold LMem.mrd. rewrite (HM (LMem.wa x)); [reflexivity|].
  rewrite (LMem.wa_unsigned x Hx). exact Ho.
Qed.

(* the shadow word cover of the 36 output bytes [fr + 176, fr + 212) after the five stores 0x81e5c-0x81e70 *)
Lemma f4g_dbc_shz : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) fr,
  fr mod 8 = 0 -> 0 <= fr ->
  (forall i, 0 <= i < 5 -> Reusable.YA0n.w_H W (Z_to_bv 64 (ACtlCutP.Sfr fr + 22 + i)) = false) ->
  LMem.bytes_at segs m (ACtlCutP.Sfr fr + 22)
    [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m)
    Reusable.YG0f.SHADOW_OFF (fr + 176) 36.
Proof.
  intros W m fr H8 H0 Hv (_ & _ & Hb) x Hx.
  unfold Reusable.YG0v.shadow_of_addr.
  remember ((x - (fr + 176)) / 8) as i eqn:Ei.
  assert (Hi : 0 <= i < 5) by (subst i; Z.div_mod_to_equations; lia).
  assert (Ex : Reusable.YG0f.SHADOW_OFF + x / 8 = ACtlCutP.Sfr fr + 22 + i).
  { subst i. unfold Reusable.YG0f.SHADOW_OFF, ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
    Z.div_mod_to_equations. lia. }
  rewrite Ex, (A.ProgWorld.aview_vis_mrd W m _ (Hv i Hi)).
  assert (Hn : (Z.to_nat i < 5)%nat) by lia.
  pose proof (Hb (Z.to_nat i) Hn) as Hbi. rewrite Z2Nat.id in Hbi by lia.
  unfold LMem.wa in Hbi. rewrite A.ProgBridge.tfibsegs_rsegs in Hbi.
  rewrite Hbi.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | ->]]]].
  - exists 0. split; [reflexivity | left; reflexivity].
  - exists 0. split; [reflexivity | left; reflexivity].
  - exists 0. split; [reflexivity | left; reflexivity].
  - exists 0. split; [reflexivity | left; reflexivity].
  - exists 4. split; [reflexivity|]. right. Z.div_mod_to_equations. lia.
Qed.

(* the read-only data fact through the journal (APostBase.arodata_ok_journalP, in arodata_okS form) *)
Lemma f4g_dbc_arodata : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k,
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  Reusable.YE01.arodata_okS segs B RLO RHI (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) ->
  Reusable.YE01.arodata_okS segs B RLO RHI (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W') mem').
Proof.
  intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He |].
  - destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hr)].
  - apply Reusable.YCbq.fp_spares_closed. intros (r & Hr & _). destruct Hr.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The 0x81e54 arm (the empty-record arm) of seg_F4. *)
Lemma glue_F4_dbc : forall POST (j : nat),
  CF POST (ix_cut C_A81e84_at [Z.of_nat j]) -> CF POST (ix_cut C_A81e54_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1 *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81e54_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HP & Hn & Hj & HHB & HFLSI & HLK & HC & Hlen0 & Hphifr & HID & HPF).
  change (ACtlCut.cut_own (ix_cut C_A81e54_at [Z.of_nat j]) cx) with [(6, ACtlCut.c_fpos cx)] in HJ, HF, HL.
  pose proof HFRAC as (A & sp & R2 & Hspm & Hspz & R4 & R8 & R9 & R3 & R19 & R26 & Hfrm & HAm & HAS & HspA & HfrA &
    HA416 & HS4 & HSapp & Q304 & Q24 & Q16 & Qh1 & Qh2 & Hsh & Hsaved).
  pose proof HC as (R23 & R18 & (A' & R9' & HA' & HSP & Q232) & HPH & HFR & HKN & HFG & HFS).
  pose proof HB as ((Hafn & Hra & Hp10 & Hp11 & Hpn & Hlen & Hgarr & Hfr0 & Hnev & Hlive & Hro & _) & _).
  pose proof Hafn as (HAR0 & _ & _ & Hgp & _).
  pose proof HJ as (HAR & Hly & _ & Hwle & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hstkp & Hastk & _).
  pose proof Hastk as (_ & _ & Hceil_stk & Hstk_lo & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  (* G2: the numbers *)
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof Reusable.YG0f.ASAN_CEIL_range as (Hceil & _). unfold Reusable.YG0f.ASAN_CEIL in Hceil.
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in HSapp. unfold A.ACfn.LLVMF_STK in Hstkp, Hstk_lo.
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hfm32 & Hfapp & Hfb & Hfsh).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & _).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)) by (apply HL; left; reflexivity).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  rewrite Efr3 in Hfm32, Hfapp, Hfb, Hfsh, Hf4096, Hfceil.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfapp, Hfb, Hfsh, Hfceil.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Hfapp.
  assert (ESh : Reusable.YG0f.shadow_addr fr = ACtlCutP.Sfr fr).
  { unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. lia. }
  rewrite ESh in Hfsh.
  assert (H8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (Efr8 : fr = 8 * (fr / 8)) by (pose proof (Z.div_mod fr 8 ltac:(lia)); lia).
  assert (ESfr : ACtlCutP.Sfr fr = fr / 8 + 2147450880) by reflexivity.
  assert (ESfr' : A.Prog.SlotInv.Sfr fr = fr / 8 + 2147450880) by reflexivity.
  assert (EA : A' = A).
  { apply f4g_dbc_bv_eq; [unfold ACtlCut.rgv in R9, R9'; rewrite <- R9', R9; reflexivity | lia | lia]. }
  subst A'.
  pose proof HHB as (Hphi0 & (Hphi_lo & _ & Hphi_hi & _)). unfold A.AsanRT.APPMEM_END in Hphi_hi.
  assert (Hphi : 0 <= phi < 2 ^ 64) by (unfold A.ACtlK.a_size in Hphi_hi; lia).
  (* the model at the empty record *)
  assert (Hlen0' : A.Prog.SlotModel.t_len (ACtlCut.c_in cx) j = 0) by exact Hlen0.
  assert (Htk : A.Prog.SlotModel.t_k (ACtlCut.c_in cx) j = 0).
  { unfold A.Prog.SlotModel.t_k. rewrite Hlen0'. reflexivity. }
  assert (H8819 : A.Prog.SlotModel.t_8819 (ACtlCut.c_in cx) j = false).
  { unfold A.Prog.SlotModel.t_8819, A.Prog.SlotModel.t_big. rewrite Hlen0'. reflexivity. }
  (* visibility and presence in W3 at mem3: the stack window (journal), the frame and its shadow (AR_frames_law) *)
  assert (Vstk : forall x, ACtlCut.c_sp cx - 4096 <= x < ACtlCut.c_sp cx ->
            Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 x) by (intros x Hx; apply Hstkp; lia).
  assert (Vfr : forall x, fr <= x < fr + 4096 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 x)
    by (intros x Hx; exact (proj1 (Hfb x Hx))).
  assert (Vsh : forall i, 0 <= i < 512 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 (ACtlCutP.Sfr fr + i))
    by (intros i Hi; exact (proj1 (Hfsh i ltac:(lia)))).
  set (WR := [(A + 200, A + 208); (ACtlCutP.Sfr fr + 22, ACtlCutP.Sfr fr + 27)]).
  set (RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  (* the run's premises *)
  assert (Wa : LMem.wr_at A.Img0.rsegs mem3 (A + 200) 8).
  { split; [lia|]. split; [lia|]. intros i Hi.
    exact (proj2 (proj2 (f4g_dbc_pres _ _ _ (Vstk (A + 200 + i) ltac:(lia))))). }
  assert (Wsh : LMem.wr_at A.Img0.rsegs mem3 (ACtlCutP.Sfr fr + 22) 5).
  { split; [lia|]. split; [lia|]. intros i Hi.
    replace (ACtlCutP.Sfr fr + 22 + i) with (ACtlCutP.Sfr fr + (22 + i)) by lia.
    exact (proj2 (proj2 (f4g_dbc_pres _ _ _ (Vsh (22 + i) ltac:(lia))))). }
  assert (Ra : Lib.ExecF.rng RNG (A + 200) 8).
  { apply A.ProgBridge.rng_RNG_W; [lia | lia |]. intros a Ha. exact (proj1 (Vstk a ltac:(lia))). }
  assert (Rsh : Lib.ExecF.rng RNG (ACtlCutP.Sfr fr + 22) 5).
  { apply A.ProgBridge.rng_RNG_W; [lia | lia |]. intros a Ha.
    replace a with (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) by lia.
    exact (proj1 (Vsh (a - ACtlCutP.Sfr fr) ltac:(lia))). }
  assert (R248 : Lib.ExecF.rng RNG (A + 248) 8).
  { apply A.ProgBridge.rng_RNG_W; [lia | lia |]. intros a Ha. exact (proj1 (Vstk a ltac:(lia))). }
  (* G3: the cut's configuration, the walk moved to the run's explicit start map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81e54_at [Z.of_nat j])) with 0x81e54.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81e54) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  rewrite f4g_dbc_mkR_of.
  unfold ACtlCut.rgv in R9, R19, R23.
  rewrite R2, R9, R19, R23.
  (* G4: f4_dbc_st_F then f4_dbc_call_pre_Fs, one run to the callee entry *)
  assert (HRUN : Lib.ExecF.evtF A.Img0.rsegs RNG
    (fun ms => exists m2 : word -> option byte,
       ms = LMS.MS
              (LFr.mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 sp) (CK11.getr regs3 3) (CK11.getr regs3 4)
                 (CK11.getr regs3 5) (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8) (Z_to_bv 64 A)
                 (Z_to_bv 64 phi) (Z_to_bv 64 0) (Z_to_bv 64 (fr + 176)) (CK11.getr regs3 13) (CK11.getr regs3 14)
                 (CK11.getr regs3 15) (CK11.getr regs3 16) (CK11.getr regs3 17) (CK11.getr regs3 18)
                 (Z_to_bv 64 (ACtlCutP.Sfr fr)) (CK11.getr regs3 20) (CK11.getr regs3 21) (CK11.getr regs3 22)
                 (Z_to_bv 64 phi) (CK11.getr regs3 24) (CK11.getr regs3 25) (CK11.getr regs3 26) (CK11.getr regs3 27)
                 (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30) (CK11.getr regs3 31))
              CK11.fp_regs (Z_to_bv 64 A.Prog.reac_ctrl_parse_c.REAC_CTRL_PARSE) CK11.fp_csr None m2
              (UK11.seg_rom A.Img0.rsegs) /\
       LFr.munch WR mem3 m2 /\
       LMem.bytes_at A.Img0.rsegs m2 (ACtlCutP.Sfr fr + 22)
         [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] /\
       ACtlCutP.q64 m2 (A + 200) (phi + 18))
    (LMS.MS
       (LFr.mkR (CK11.getr regs3 1) (Z_to_bv 64 sp) (CK11.getr regs3 3) (CK11.getr regs3 4)
          (CK11.getr regs3 5) (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8) (Z_to_bv 64 A)
          (CK11.getr regs3 10) (CK11.getr regs3 11) (CK11.getr regs3 12) (CK11.getr regs3 13) (CK11.getr regs3 14)
          (CK11.getr regs3 15) (CK11.getr regs3 16) (CK11.getr regs3 17) (CK11.getr regs3 18)
          (Z_to_bv 64 (ACtlCutP.Sfr fr)) (CK11.getr regs3 20) (CK11.getr regs3 21) (CK11.getr regs3 22)
          (Z_to_bv 64 phi) (CK11.getr regs3 24) (CK11.getr regs3 25) (CK11.getr regs3 26) (CK11.getr regs3 27)
          (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30) (CK11.getr regs3 31))
       CK11.fp_regs (Z_to_bv 64 0x81e54) CK11.fp_csr None mem3 (UK11.seg_rom A.Img0.rsegs))).
  { eapply Lib.ExecF.evtF_cut.
    { exact (A.Prog.Seg.F4F.f4_dbc_st_F RNG (CK11.getr regs3 1) (Z_to_bv 64 sp) (CK11.getr regs3 3)
        (CK11.getr regs3 4) (CK11.getr regs3 5) (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8)
        (CK11.getr regs3 10) (CK11.getr regs3 11) (CK11.getr regs3 12) (CK11.getr regs3 13) (CK11.getr regs3 14)
        (CK11.getr regs3 15) (CK11.getr regs3 16) (CK11.getr regs3 17) (CK11.getr regs3 18)
        (CK11.getr regs3 20) (CK11.getr regs3 21) (CK11.getr regs3 22)
        (CK11.getr regs3 24) (CK11.getr regs3 25) (CK11.getr regs3 26) (CK11.getr regs3 27)
        (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30) (CK11.getr regs3 31)
        CK11.fp_regs CK11.fp_csr mem3 A fr phi
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Wa Wsh Ra Rsh). }
    intros ms (m1 & m2 & a0' & -> & MU1 & _ & MU2 & _ & _ & _ & HSH2 & HQ2).
    assert (MU : LFr.munch WR mem3 m2).
    { apply (LFr.munch_trans WR mem3 m1 m2).
      - apply (LFr.munch_weaken [(A + 200, A + 208)]); [|exact MU1].
        intros x Hx. unfold WR in Hx. cbn [LFr.outside] in Hx |- *. tauto.
      - apply (LFr.munch_weaken (A.Prog.Seg.F4.f4_Wsh fr)); [|exact MU2].
        intros x Hx. unfold WR in Hx. unfold A.Prog.Seg.F4.f4_Wsh. cbn [LFr.outside] in Hx |- *.
        change (A.Prog.SlotInv.Sfr fr) with (ACtlCutP.Sfr fr). tauto. }
    assert (Q248 : ACtlCutP.q64 m2 (A + 248) (fr + 176)).
    { pose proof HSP as (S248 & _). apply (f4g_dbc_xq64 mem3); [|exact S248].
      intros i Hi. apply (f4g_dbc_st WR); [exact MU | lia |].
      unfold WR. cbn [LFr.outside]. repeat split; lia. }
    pose proof (A.Prog.Seg.F4.f4_rd8 m2 (A + 248) _ Q248 (LMem.length_le8 _)) as H248.
    eapply Lib.ExecF.evtF_mono.
    { exact (A.Prog.Seg.F4Fs.PF.f4_dbc_call_pre_Fs RNG (CK11.getr regs3 1) (CK11.getr regs3 3) (CK11.getr regs3 4)
        (CK11.getr regs3 5) (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8)
        a0' (CK11.getr regs3 11) (CK11.getr regs3 12) (CK11.getr regs3 13) (CK11.getr regs3 14)
        (CK11.getr regs3 15) (CK11.getr regs3 16) (CK11.getr regs3 17) (CK11.getr regs3 18)
        (Z_to_bv 64 (ACtlCutP.Sfr fr)) (CK11.getr regs3 20) (CK11.getr regs3 21) (CK11.getr regs3 22)
        (CK11.getr regs3 24) (CK11.getr regs3 25) (CK11.getr regs3 26) (CK11.getr regs3 27)
        (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30) (CK11.getr regs3 31)
        CK11.fp_regs CK11.fp_csr m2 A phi (fr + 176) sp ltac:(lia) ltac:(lia) H248 R248). }
    intros ms' ->. exists m2. split; [reflexivity|]. split; [exact MU|]. split; [exact HSH2 | exact HQ2]. }
  (* the lift (YA0nR.SRr_fsteps keeps the run for ProgWorld.ajournal_of_fsteps) *)
  destruct (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as (ms' & Hfs & (m2 & Ems & MU & HSH2 & HQ2)).
  rewrite <- A.ProgBridge.tfibsegs_rsegs in Hfs.
  apply (Reusable.YA0nR.SRr_fsteps segs A.ACtlG.Kit.kit_wx W3 _ ms' md3 RNG (POST cx) Hfs
           (A.ProgBridge.fp_avoids_RNG_W _)).
  intros md' Hsbm.
  (* P1: the journal at the callee entry (writes: the spill word and the five frame shadow bytes) *)
  assert (Hawr : forall a, 0 <= a < 2 ^ 64 -> ~ LFr.outside WR a ->
     Reusable.YCbq.awr_byte A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
       (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
       [(6, ACtlCut.c_fpos cx)] a).
  { intros a Ha Hout. unfold WR in Hout. cbn [LFr.outside] in Hout.
    assert (Hc : (A + 200 <= a < A + 208) \/ (ACtlCutP.Sfr fr + 22 <= a < ACtlCutP.Sfr fr + 27)).
    { destruct (Z_lt_le_dec a (A + 200)), (Z_lt_le_dec a (A + 208)),
        (Z_lt_le_dec a (ACtlCutP.Sfr fr + 22)), (Z_lt_le_dec a (ACtlCutP.Sfr fr + 27));
        try (left; lia); try (right; lia); exfalso; apply Hout; repeat split; lia. }
    destruct Hc as [Hc|Hc].
    - left. unfold A.ACfn.LLVMF_STK. lia.
    - right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
      unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, ESh.
      change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512. lia. }
  assert (HJ2a : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
     (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
     [(6, ACtlCut.c_fpos cx)] ly3 S3 W3 m2 md' k).
  { subst ms'.
    match type of Hfs with Reusable.YK04R.fsteps _ _ ?s0 ?s1 =>
      exact (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
        (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
        [(6, ACtlCut.c_fpos cx)] ly3 S3 W3 s0 s1 md3 md' k RNG WR HJ Hfs (A.ProgBridge.fp_avoids_RNG_W _) MU Hsbm
        Hawr)
    end. }
  subst ms'.
  set (Rc := LFr.mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 sp) (CK11.getr regs3 3) (CK11.getr regs3 4)
                 (CK11.getr regs3 5) (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8) (Z_to_bv 64 A)
                 (Z_to_bv 64 phi) (Z_to_bv 64 0) (Z_to_bv 64 (fr + 176)) (CK11.getr regs3 13) (CK11.getr regs3 14)
                 (CK11.getr regs3 15) (CK11.getr regs3 16) (CK11.getr regs3 17) (CK11.getr regs3 18)
                 (Z_to_bv 64 (ACtlCutP.Sfr fr)) (CK11.getr regs3 20) (CK11.getr regs3 21) (CK11.getr regs3 22)
                 (Z_to_bv 64 phi) (CK11.getr regs3 24) (CK11.getr regs3 25) (CK11.getr regs3 26) (CK11.getr regs3 27)
                 (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30) (CK11.getr regs3 31)).
  assert (ESR : Reusable.YG0d.spZ Rc = sp).
  { unfold Reusable.YG0d.spZ. change (CK11.getr Rc 2) with (Z_to_bv 64 sp). apply LMS.unsigned_lit. lia. }
  (* P: TPARSE at the callee entry 0x83578 (ra = 0x81e84, a0 = phi, a1 = 0, a2 = fr + 176) *)
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs A.Prog.C_reac_ctrl_parse.A_reac_ctrl_parseP Rc m2 md') (POST cx)).
  eapply (Reusable.YA0n.SRr_bind segs).
  { apply (TPARSE A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
             (ACtlCut.c_mem cx) (ACtlCut.c_md cx) [(6, ACtlCut.c_fpos cx)] ly3 S3 W3 m2 md' k Rc phi 0 (fr + 176)
             (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)).
    - (* P1 *) exact HJ2a.
    - (* P2 *) exact (f4g_dbc_arodata _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2a Hro).
    - (* P3 *) change (CK11.getr Rc 1) with (Z_to_bv 64 0x81e84). vm_compute. reflexivity.
    - unfold Reusable.YG0d.raZ. change (bv_unsigned (CK11.getr Rc 1)) with 532100. lia.
    - (* P4 *) change (CK11.getr Rc 3) with (CK11.getr regs3 3). rewrite R3. exact Hgp.
    - change (CK11.getr Rc 4) with (CK11.getr regs3 4). exact R4.
    - (* P5 *) reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - (* P7 *) rewrite ESR. exact Hspm.
    - rewrite ESR. unfold A.Prog.C_reac_ctrl_parse.REAC_CTRL_PARSE_STK, A.ACfn.LLVMF_STK. lia.
    - rewrite ESR. lia.
    - (* P8 *) rewrite HF. vm_compute. reflexivity.
    - (* P9 *) intros Hn0. lia.
    - (* P10: the 36-byte output record lies in the owned class-6 frame; its shadow is the five stored bytes *)
      intros _. split.
      + exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split; [lia|]. rewrite Efr3.
        change (Reusable.YG00.fs_frame_bytes 6) with 4096. split; [exact H8|]. split; lia.
      + split; [Z.div_mod_to_equations; lia|].
        apply (f4g_dbc_shz W3 m2 fr H8 ltac:(lia)); [|exact HSH2].
        intros i Hi. replace (ACtlCutP.Sfr fr + 22 + i) with (ACtlCutP.Sfr fr + (22 + i)) by lia.
        exact (proj1 (Vsh (22 + i) ltac:(lia))).
    - (* P11 *) intros _ a Ha. right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
      left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3.
      change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
    - (* P12 *) unfold A.Prog.SlotModel.t_g. apply A.Prog.SlotModel.fr50_length.
    - (* P13 *) intros Hn0. lia. }
  (* G5: after the call, at the return point = the exit cut *)
  intros W2 c2 Hle2 HPOST.
  destruct HPOST as (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & Hpres & HF2 & Hbl2 & _ & HR10 & Hout & Hkept).
  subst c2. rewrite ESR in Hkept.
  change (Reusable.YA0n.SRr segs W2
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81e84_at [Z.of_nat j])) regs2 mem2 md2) (POST cx)).
  pose proof HJ2 as (HAR2 & Hly2 & _).
  assert (Ecp : Prog.RcParse.ctrlparse 0 (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) = (0, repeat Prog.RcParse.cp_z 36))
    by reflexivity.
  rewrite Ecp in HR10, Hout. cbn [fst snd] in HR10, Hout.
  (* registers: kept by the call (aregs_preserved) *)
  assert (KR : forall r : Z, Reusable.YG0d.acallee_saved r ->
                 CK11.getr regs2 (Z_to_bv 5 r) = CK11.getr Rc (Z_to_bv 5 r)) by exact Hpres.
  assert (K2 : CK11.getr regs2 2 = CK11.getr regs3 2).
  { transitivity (CK11.getr Rc 2); [exact (KR 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
    change (CK11.getr Rc 2) with (Z_to_bv 64 sp). symmetry. exact R2. }
  assert (K3 : CK11.getr regs2 3 = CK11.getr regs3 3) by exact (KR 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (K4 : CK11.getr regs2 4 = CK11.getr regs3 4) by exact (KR 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (K8 : CK11.getr regs2 8 = CK11.getr regs3 8) by exact (KR 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (K9z : CK11.getr regs2 9 = Z_to_bv 64 A) by exact (KR 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (K18 : CK11.getr regs2 18 = CK11.getr regs3 18)
    by exact (KR 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (K19 : CK11.getr regs2 19 = Z_to_bv 64 (ACtlCutP.Sfr fr))
    by exact (KR 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (K21 : CK11.getr regs2 21 = CK11.getr regs3 21)
    by exact (KR 21 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (K23 : CK11.getr regs2 23 = Z_to_bv 64 phi)
    by exact (KR 23 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (K26 : CK11.getr regs2 26 = CK11.getr regs3 26)
    by exact (KR 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  (* memory: two steps, mem3 -> m2 (the run's stores, munch WR) and m2 -> mem2 (TPARSE's acall_kept) *)
  pose proof (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 m2 mem2 _ _ _ Hkept Hle2) as KC.
  assert (KS : forall a, sp <= a < ACtlCut.c_sp cx -> ~ (A + 200 <= a < A + 208) ->
            LMem.mrd segs mem2 (LMem.wa a) = LMem.mrd segs mem3 (LMem.wa a)).
  { intros a Ha Hw. transitivity (LMem.mrd segs m2 (LMem.wa a)).
    - apply KC.
      + exact (proj1 (Vstk a ltac:(lia))).
      + rewrite (LMem.wa_unsigned a ltac:(lia)). left. split; [lia|]. lia.
    - apply (f4g_dbc_st WR); [exact MU | lia |]. unfold WR. cbn [LFr.outside]. repeat split; lia. }
  assert (KF : forall a, fr <= a < fr + 4096 -> ~ (fr + 176 <= a < fr + 212) ->
            LMem.mrd segs mem2 (LMem.wa a) = LMem.mrd segs mem3 (LMem.wa a)).
  { intros a Ha Hw. transitivity (LMem.mrd segs m2 (LMem.wa a)).
    - apply KC.
      + exact (proj1 (Vfr a Ha)).
      + rewrite (LMem.wa_unsigned a ltac:(lia)). right. right. right.
        exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split; [|cbv beta; lia].
        left. unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite Efr3.
        change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
    - apply (f4g_dbc_st WR); [exact MU | lia |]. unfold WR. cbn [LFr.outside]. repeat split; lia. }
  assert (KSh : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
            ~ (ACtlCutP.Sfr fr + 22 <= a < ACtlCutP.Sfr fr + 27) ->
            LMem.mrd segs mem2 (LMem.wa a) = LMem.mrd segs mem3 (LMem.wa a)).
  { intros a Ha Hw. transitivity (LMem.mrd segs m2 (LMem.wa a)).
    - apply KC.
      + pose proof (proj1 (Vsh (a - ACtlCutP.Sfr fr) ltac:(lia))) as Hv.
        replace (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) with a in Hv by lia. exact Hv.
      + rewrite (LMem.wa_unsigned a ltac:(lia)). right. right. right.
        exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split; [|cbv beta; lia].
        right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, ESh.
        change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512. lia.
    - apply (f4g_dbc_st WR); [exact MU | lia |]. unfold WR. cbn [LFr.outside]. repeat split; lia. }
  assert (KFA : forall p n, fr + 216 <= p -> p + n <= fr + 4096 -> forall i, 0 <= i < n ->
            LMem.mrd segs mem2 (LMem.wa (A.AsanRT.shadow_addr (p + i))) =
            LMem.mrd segs mem3 (LMem.wa (A.AsanRT.shadow_addr (p + i)))).
  { intros p n Hp Hpn' i Hi. apply KSh; unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr; Z.div_mod_to_equations; lia. }
  assert (KB : forall p n a, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) -> p <= a < p + Reusable.YG00.req_size n ->
            LMem.mrd segs mem2 (LMem.wa a) = LMem.mrd segs mem3 (LMem.wa a)).
  { intros p n a Hin Ha.
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR Hin)
      as (_ & Hp4096 & Hpceil & Hpapp & Hppres & _ & _).
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 p n 6 (ACtlCut.c_fpos cx) HAR Hin Hin6)
      as Hdj.
    unfold Reusable.YG0f.zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite Efr3 in Hdj.
    change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hdj.
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Hpapp.
    transitivity (LMem.mrd segs m2 (LMem.wa a)).
    - apply KC.
      + destruct (Hppres a Ha) as ((Hv & _) & _). exact Hv.
      + rewrite (LMem.wa_unsigned a ltac:(lia)). right. left.
        exists p, n, (a - p). split; [exact Hin|]. split; [lia|]. split; [lia|]. cbv beta. lia.
    - apply (f4g_dbc_st WR); [exact MU | lia |]. unfold WR. cbn [LFr.outside]. repeat split; lia. }
  assert (KKN : forall a, A.Prog.reac_ctrl_kind_name_c.KIND_NAME <= a < A.Prog.reac_ctrl_kind_name_c.KIND_NAME + 112 ->
            LMem.mrd segs mem2 (LMem.wa a) = LMem.mrd segs mem3 (LMem.wa a)).
  { intros a Ha. unfold A.Prog.reac_ctrl_kind_name_c.KIND_NAME in Ha.
    assert (Himg : Reusable.YG0d.in_img segs a) by (apply A.Prog.CtrlImg.ctrl_relro_img; lia).
    transitivity (LMem.mrd segs m2 (LMem.wa a)).
    - apply KC.
      + destruct (A.ProgBridge.img_vis_W W3) as (_ & _ & Hv). apply Hv.
        unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI. lia.
      + rewrite (LMem.wa_unsigned a ltac:(lia)). right. right. left. split; [exact Himg|]. split.
        * rewrite (A.AF0m.ts_owned _ TFIB_SYMS). intros Hex. apply Exists_exists in Hex.
          destruct Hex as (r & Hr & Hz). unfold A.AF0m.Tfib_owned_static in Hr.
          repeat (destruct Hr as [<- | Hr]; [unfold Reusable.YG0n.in_zr in Hz; cbn [fst snd] in Hz; lia |]).
          destruct Hr.
        * rewrite (A.AF0m.ts_errno _ TFIB_SYMS). unfold A.AF0m.TFIB_ERRNO. lia.
    - apply (f4g_dbc_st WR); [exact MU | lia |]. unfold WR. cbn [LFr.outside]. repeat split; lia. }
  (* the frame and its shadow present at mem2 (AR_frames_law at the post's AR) *)
  assert (Efa2 : Reusable.YG0f.frame_addr ly2 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr.
    destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _). rewrite EF2. reflexivity. }
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly2 S2 W2 mem2 md2 6 (ACtlCut.c_fpos cx) HAR2
              ltac:(rewrite HF2; exact Hin6)) as (_ & _ & HFb2 & HFs2).
  rewrite Efa2 in HFb2, HFs2. rewrite ESh in HFs2.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in HFb2, HFs2.
  (* the live blocks *)
  assert (Hinphi3 : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  assert (Hinphi2 : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly2 S2)) by (rewrite Hbl2; exact Hinphi3).
  assert (Ereq : Reusable.YG00.req_size (ACtlCutP.flen cx j) = A.ACtlK.a_size (ACtlCutP.flen cx j)).
  { unfold Reusable.YG00.req_size, A.ACtlK.a_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  assert (HinIN3 : 0 < ACtlCut.c_n cx -> In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
  { intros Hn0. destruct Hpn as [(Hn1 & _) | (_ & Hin)]; [lia|].
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin. }
  assert (INK : LMem.bytes_at segs mem3 (ACtlCut.c_p cx) (ACtlCut.c_in cx) ->
                LMem.bytes_at segs mem2 (ACtlCut.c_p cx) (ACtlCut.c_in cx)).
  { intros Hb. apply (f4g_dbc_xbytes mem3); [|exact Hb].
    intros i Hi. rewrite <- Hlen in Hi. assert (Hn0 : 0 < ACtlCut.c_n cx) by lia.
    apply (KB _ _ _ (HinIN3 Hn0)). unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
  assert (INA : A.AsanRT.addressable mem3 (ACtlCut.c_p cx) (ACtlCut.c_n cx) ->
                A.AsanRT.addressable mem2 (ACtlCut.c_p cx) (ACtlCut.c_n cx)).
  { intros Ha. destruct (Z.eq_dec (ACtlCut.c_n cx) 0) as [E0|Hn0].
    - apply (f4g_dbc_xaddr mem3); [intros i Hi; lia | exact Ha].
    - destruct Ha as (Hp0 & Hn1 & _).
      apply (A.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly2 S2 W2 mem2 md2 (ACtlCut.c_p cx) (ACtlCut.c_n cx)
               (ACtlCut.c_p cx) (ACtlCut.c_n cx) HAR2); [rewrite Hbl2; apply HinIN3; lia | lia | lia |].
      unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
  (* the transports by class *)
  assert (SPK : forall off v, 0 <= off -> off + 8 <= 200 \/ 208 <= off -> off + 8 <= 416 ->
            ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill regs2 mem2 off v).
  { intros off v H0 H1 H2 Hs. apply (f4g_dbc_spill regs3 regs2 mem3 mem2 A off v R9 K9z); [lia | lia | lia | | exact Hs].
    intros i Hi. apply KS; lia. }
  assert (QK : forall off v, 0 <= off -> off + 8 <= 200 \/ 208 <= off -> off + 8 <= 416 ->
            ACtlCutP.q64 mem3 (A + off) v -> ACtlCutP.q64 mem2 (A + off) v).
  { intros off v H0 H1 H2 Hq. apply (f4g_dbc_xq64 mem3); [|exact Hq]. intros i Hi. apply KS; lia. }
  assert (FK : forall a bs, fr + 212 <= a -> a + Z.of_nat (length bs) <= fr + 4096 ->
            LMem.bytes_at segs mem3 a bs -> LMem.bytes_at segs mem2 a bs).
  { intros a bs H0 H1 Hb. apply (f4g_dbc_xbytes mem3); [|exact Hb]. intros i Hi. apply KF; lia. }
  assert (FA : forall p n, fr + 216 <= p -> p + n <= fr + 4096 ->
            A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable mem2 p n).
  { intros p n H0 H1 Ha. apply (f4g_dbc_xaddr mem3); [|exact Ha]. intros i Hi. exact (KFA p n H0 H1 i Hi). }
  assert (Lsaved : length (ACtlCutP.saved_bytes cx) = 104%nat).
  { unfold ACtlCutP.saved_bytes. rewrite !length_app, !LMem.length_le8. reflexivity. }
  (* the output record's first word: the 36 bytes are cp_z = 0 *)
  assert (U176 : ACtlCutP.u32 mem2 (fr + 176) 0).
  { unfold ACtlCutP.u32.
    replace (LMem.le4 (Z_to_bv 64 0)) with (repeat Prog.RcParse.cp_z 4) by (vm_compute; reflexivity).
    split; [lia|]. split; [rewrite repeat_length; lia|].
    intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi.
    assert (Hv3 : Reusable.YA0n.w_H W3 (Z_to_bv 64 (fr + 176 + Z.of_nat i)) = false)
      by exact (proj1 (Vfr (fr + 176 + Z.of_nat i) ltac:(lia))).
    assert (Hv2 : Reusable.YA0n.w_H W2 (Z_to_bv 64 (fr + 176 + Z.of_nat i)) = false).
    { destruct (Reusable.YA0n.w_H W2 (Z_to_bv 64 (fr + 176 + Z.of_nat i))) eqn:E2; [|reflexivity].
      rewrite (Hle2 _ E2) in Hv3. discriminate Hv3. }
    pose proof (Hout ltac:(lia) i ltac:(lia)) as Ho. rewrite nth_repeat in Ho.
    pose proof (A.ProgWorld.mrd_of_aview_some W2 mem2 _ _ Hv2 Ho) as Hm.
    rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hm. unfold LMem.wa. rewrite A.ProgBridge.tfibsegs_rsegs. exact Hm. }
  (* the exit cut *)
  apply (HX cx [Z.of_nat j] fr k ly2 S2 W2 regs2 mem2 md2 HB).
  - (* journal: the post's own *)
    exact HJ2.
  - (* frames *)
    rewrite HF2. exact HF.
  - (* frame law *)
    exact HL.
  - (* event bound *)
    exact Hk.
  - (* the exit body, C_A81e84_at at [j] *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A81e84_at ACtlCutP.ixn ACtlCutP.ixz nth].
    split; [reflexivity|]. rewrite Nat2Z.id.
    split.
    { (* FRAC at regs2 / mem2, conjunct by conjunct: registers by aregs_preserved, memory by KS / KF, the frame's
         shadow word list from the post's AR.  Written generically, so a further q64 conjunct at a stack or frame
         address (a Theorem Labs lane's trailer word at fr + 4088) is kept by the same steps. *)
      pose proof HFRAC as HFRg. unfold ACtlCutP.FRAC in HFRg |- *. destruct HFRg as (Ag & spg & HFRg).
      repeat match type of HFRg with _ /\ _ => let H := fresh "HFRg" in destruct HFRg as [H HFRg] end.
      exists A, sp.
      repeat match goal with |- _ /\ _ => split end.
      all: lazymatch goal with
        | |- ACtlCutP.q64 _ ?a _ =>
            apply (f4g_dbc_xq64 mem3);
              [ intros i Hi;
                tryif (lazymatch a with ?x + _ => constr_eq x fr | ?x => constr_eq x fr end)
                then (apply KF; lia) else (apply KS; lia)
              | assumption ]
        | |- LMem.bytes_at _ _ _ _ =>
            apply (f4g_dbc_xbytes mem3); [intros i Hi; apply KS; lia | assumption]
        | |- exists sh, _ =>
            destruct (f4g_dbc_bytes_of_pres mem2 392 (ACtlCutP.Sfr fr)) as (sh & Hsh2 & Hshl);
              [lia | lia | intros i Hi; exact (proj1 (proj2 (f4g_dbc_pres _ _ _ (proj1 (HFs2 i ltac:(lia))))))
              | exists sh; split; [exact Hsh2 | rewrite Hshl; reflexivity]]
        | |- _ =>
            first [ assumption
                  | (unfold ACtlCut.rgv, Reusable.YG0d.spZ; rewrite ?K2, ?K3, ?K4, ?K8, ?K9z, ?K19, ?K26;
                     first [assumption | reflexivity])
                  | (unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END; lia) ]
        end. }
    unfold ACtlCutP.b5_body. exists phi. cbv beta.
    split; [rewrite Hbl2; exact HP|].
    split; [exact Hn|]. split; [exact Hj|].
    split.
    { (* HB: the record block's shadow, from the post's AR *)
      split; [exact Hphi0|]. rewrite <- Ereq.
      apply (A.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly2 S2 W2 mem2 md2 phi (ACtlCutP.flen cx j) phi
               (Reusable.YG00.req_size (ACtlCutP.flen cx j)) HAR2 Hinphi2); [lia | | lia].
      unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
    split.
    { (* FLSI *)
      destruct HFLSI as ((HPRO & S128 & HSTK & S144 & HAD2691) & S216 & S224 & S248 & (HINa & HINb) & HFLC).
      destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & HAD2624 & HINb' & HINa' &
        P184 & P256 & P264 & P272 & P32).
      destruct HFLC as (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & HADfg & HAD2688 & C72 & C64 & C56 &
        C48).
      split; [split; [|split; [|split; [|split]]]|].
      - (* PRO *)
        split; [refine (SPK _ _ _ _ _ P40); lia|].
        split; [refine (SPK _ _ _ _ _ P120); lia|].
        split; [refine (SPK _ _ _ _ _ P136); lia|].
        split; [refine (SPK _ _ _ _ _ P160); lia|].
        split; [refine (SPK _ _ _ _ _ P168); lia|].
        split; [refine (SPK _ _ _ _ _ P176); lia|].
        split; [refine (SPK _ _ _ _ _ P208); lia|].
        split; [refine (SPK _ _ _ _ _ P248); lia|].
        split; [refine (FA _ _ _ _ HAD2624); lia|].
        split; [exact (INK HINb')|].
        split; [intros Hn0; exact (INA (HINa' Hn0))|].
        split; [refine (SPK _ _ _ _ _ P184); lia|].
        split; [refine (SPK _ _ _ _ _ P256); lia|].
        split; [refine (SPK _ _ _ _ _ P264); lia|].
        split; [refine (SPK _ _ _ _ _ P272); lia|].
        refine (SPK _ _ _ _ _ P32); lia.
      - refine (SPK _ _ _ _ _ S128); lia.
      - (* the frame's presence at mem2 *)
        unfold ACtlCutP.FRAME_BYTES. split; [lia|]. split; [lia|]. intros a Ha.
        destruct (f4g_dbc_pres _ _ _ (proj1 (HFb2 a ltac:(lia)))) as (_ & Hb & Hw). split; [exact Hw | exact Hb].
      - refine (SPK _ _ _ _ _ S144); lia.
      - refine (FA _ _ _ _ HAD2691); lia.
      - split; [refine (SPK _ _ _ _ _ S216); lia|].
        split; [refine (SPK _ _ _ _ _ S224); lia|].
        split; [refine (SPK _ _ _ _ _ S248); lia|].
        split; [split; [exact (INA HINa) | exact (INK HINb)]|].
        unfold ACtlCutP.fragb in *.
        split; [refine (SPK _ _ _ _ _ C256); lia|].
        split; [refine (SPK _ _ _ _ _ C184); lia|].
        split; [refine (SPK _ _ _ _ _ C192); lia|].
        split; [refine (SPK _ _ _ _ _ C80); lia|].
        split; [refine (SPK _ _ _ _ _ C88); lia|].
        split; [refine (SPK _ _ _ _ _ C96); lia|].
        split; [refine (SPK _ _ _ _ _ C272); lia|].
        split; [refine (SPK _ _ _ _ _ C264); lia|].
        split; [refine (FA _ _ _ _ HADfg); lia|].
        split; [refine (FA _ _ _ _ HAD2688); lia|].
        split; [refine (SPK _ _ _ _ _ C72); lia|].
        split; [refine (SPK _ _ _ _ _ C64); lia|].
        split; [refine (SPK _ _ _ _ _ C56); lia|].
        refine (SPK _ _ _ _ _ C48); lia. }
    split.
    { (* LK *)
      destruct HLK as (HjL & R21 & HOUR). split; [exact HjL|].
      split; [unfold ACtlCut.rgv in *; rewrite K21; exact R21|].
      unfold ACtlCutP.OURb in *. refine (FK _ _ _ _ HOUR); [lia|].
      rewrite A.Prog.SlotModel.OUR_length. cbn. lia. }
    split.
    { (* b5_C *)
      split; [exact K23|].
      split; [unfold ACtlCut.rgv in *; rewrite K18; exact R18|].
      split.
      { exists A. split; [exact K9z|]. split; [lia|].
        destruct HSP as (Q248 & Q256 & Q144 & Q184 & Q192 & Q80 & Q88 & Q96 & Q272 & Q264).
        split; [|refine (QK _ _ _ _ _ Q232); lia].
        split; [refine (QK _ _ _ _ _ Q248); lia|].
        split; [refine (QK _ _ _ _ _ Q256); lia|].
        split; [refine (QK _ _ _ _ _ Q144); lia|].
        split; [refine (QK _ _ _ _ _ Q184); lia|].
        split; [refine (QK _ _ _ _ _ Q192); lia|].
        split; [refine (QK _ _ _ _ _ Q80); lia|].
        split; [refine (QK _ _ _ _ _ Q88); lia|].
        split; [refine (QK _ _ _ _ _ Q96); lia|].
        split; [refine (QK _ _ _ _ _ Q272); lia|].
        refine (QK _ _ _ _ _ Q264); lia. }
      split.
      { (* b5_PH: both arms need 50 <= flen, and flen = 0 *)
        split; intros Hn0; exfalso; lia. }
      split.
      { (* b5_FR *)
        destruct HFR as (HFRa1 & HFRa2 & HFRb & HFRl). unfold ACtlCutP.fragb in *.
        split; [refine (FA _ _ _ _ HFRa1); lia|].
        split; [refine (FA _ _ _ _ HFRa2); lia|].
        split; [refine (FK _ _ _ _ HFRb); [lia | rewrite HFRl; cbn; lia]|].
        exact HFRl. }
      split.
      { (* b5_KN: KIND_NAME's 112 bytes (a non-owned image range) and their shadow (a zero-shadow global range,
           found in the bundle's list by value) *)
        destruct HKN as (HKNb & HKNa). split.
        - assert (Hknl : length A.Prog.reac_ctrl_kind_name_c.kind_name_bytes = 112%nat) by (vm_compute; reflexivity).
          apply (f4g_dbc_xbytes mem3); [|exact HKNb]. intros i Hi. apply KKN. lia.
        - assert (Hz : Exists (fun r => fst r <= A.Prog.reac_ctrl_kind_name_c.KIND_NAME /\
                         A.Prog.reac_ctrl_kind_name_c.KIND_NAME + 112 <= fst r + 8 * (snd r / 8))
                         (Reusable.YG0f.as_zero_shadow B)).
          { rewrite (A.AF0m.ts_zsh _ TFIB_SYMS). unfold A.AF0m.Tfib_zero_shadow, A.Prog.reac_ctrl_kind_name_c.KIND_NAME.
            repeat (first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.leb_le; vm_compute; reflexivity
                          | apply Exists_cons_tl ]). }
          apply Exists_exists in Hz as (r & Hr & Hr1 & Hr2).
          exact (A.ProgWorldShadow.ctl_zshadow_of_AR B LAWS ly2 S2 W2 mem2 md2 r _ 112 HAR2 Hr Hr1 ltac:(lia) Hr2). }
      split.
      { (* FGj *)
        destruct HFG as (HFGb & HFGo). split; [|exact HFGo]. unfold ACtlCutP.FGBe in *.
        pose proof HFR as (_ & _ & _ & HFRl).
        refine (FK _ _ _ _ HFGb); [lia | rewrite HFRl; cbn; lia]. }
      (* FSj *)
      destruct HFS as (F104 & F112 & HFSb & HFSa & HFSI).
      split; [refine (SPK _ _ _ _ _ F104); lia|].
      split; [refine (SPK _ _ _ _ _ F112); lia|].
      split; [refine (FK _ _ _ _ HFSb); [lia|]|].
      { pose proof (A.Prog.Seg.F4.f4_fs_body_len (ACtlCut.c_in cx) j) as Hl. lia. }
      split; [refine (FA _ _ _ _ HFSa); lia | exact HFSI]. }
    (* the exit's own conjuncts *)
    split; [lia|].
    split.
    { (* a0 = the parse result, 0 = t_k j at flen = 0 *)
      unfold ACtlCut.rgv. rewrite Htk. exact HR10. }
    split; [rewrite Htk; exact U176|].
    split.
    { (* IDj *)
      destruct HID as (HIDb & HIDo). split; [|exact HIDo]. unfold ACtlCutP.IDBe in *.
      refine (FK _ _ _ _ HIDb); [lia | rewrite A.Prog.Seg.F4.f4_tID_len; cbn; lia]. }
    split.
    { (* b5_F17: the word the run stored at A + 200, kept by the call (stack above its window) *)
      exists A. split; [exact K9z|]. split; [lia|].
      apply (f4g_dbc_xq64 m2); [|exact HQ2]. intros i Hi.
      apply (f4g_dbc_kept ly3 S3 W3 W2 m2 mem2 _ _ _ _ Hkept Hle2);
        [lia | exact (proj1 (Vstk (A + 200 + i) ltac:(lia))) |].
      left. split; [lia|]. lia. }
    (* b5_PF: both arms are off at flen = 0 (t_8819 j = false) *)
    exists A. split; [exact K9z|]. split; [lia|].
    split; [intros Hn0; exfalso; lia | intros E; rewrite H8819 in E; discriminate].
  - (* ctl_rt_C: from the post's AR (the call writes runtime cells) *)
    apply (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly2 S2 W2 mem2 md2 HAR2).
    apply (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI); [| lia | lia].
    exact (f4g_dbc_arodata _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 Hro).
Qed.


(* ---------------------------------------------------------------------------------------------------------
   The stage: ACtl.v:566-568's Hypothesis seg_F4, verbatim. *)
Lemma glue_seg_F4 : forall POST (j : nat),
  CF POST (ix_cut C_A81e88_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ea4_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ea8_at [Z.of_nat j]) ->
  CF POST (ix_cut C_A81e84_at [Z.of_nat j]) -> CF POST (ix_cut C_A81dfc_at [Z.of_nat j]) /\ CF POST (ix_cut C_A81e54_at [Z.of_nat j]).
Proof.
  intros POST j He88 Hea4 Hea8 He84.
  split; [exact (glue_F4_d64 POST j He88 Hea4 Hea8) | exact (glue_F4_dbc POST j He84)].
Qed.

End GlueF4.
