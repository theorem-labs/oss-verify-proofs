(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 4006 of its 4152 lines of code are new or changed and 2320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4b.v, with its module paths and module names changed; 782 of its 845 lines of code are new or changed and 4089 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F12.v, with its module paths and module names changed; 1464 of its 1519 lines of code are new or changed and 790 lines of the source are left out. *)
(* lib/A/ACtlG/F9.v -- GLUE for stage seg_F9 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:768).
   Written by a Theorem Labs lane; single writer.  rule 24: no function proved (kind:
   segment lemma of a walk).  Pattern: glue-pattern.md (a working note, not in this delivery).

   WHAT IT PROVES
     glue_seg_F9 : forall POST (j : nat),
       CF POST (ix_cut C_A81ff4_at [Z.of_nat j]) -> CF POST (ix_cut C_A81f88_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v:768's Section
   hypothesis seg_F9, character for character.

   THE SEGMENT (Seg/F9.v at the v1.9 cut text; its own seg_F9 is :3346).  0x81f88 -> 0x81ff4, in three pieces:
   A  0x81f88 - 0x81fe4 (Seg/F9F.v f9_evtA_F :107, a Theorem Labs lane's mechanical re-run, PROVED): the instrumented 1-byte
      check of the kind-name byte at a0 = X = kind_name_addr (t_k g j), the read of that byte (not '?'), then SIX
      STORES - the frame shadow bytes S3+32 := 2, S3+34 := 0, S3+38 := 0 (S3 = Sfr fr) and the frame cells
      [fr+256, 2) := 0, [fr+272, 8) := 0, [fr+304, 8) := 0 - whose addresses come from the three spill reads
      [A+256], [A+272], [A+264].
   B  THE SPLIT at 0x81ff0 (a Theorem Labs lane's ruling; F9F.v:253-264).  f9_evtB is NOT re-run: no
      reac_ctrl_identity_reply_contract_F exists.  Seg/F9F.v's f9_evtB_pre_F (:267) runs the three register
      instructions 0x81fe8 -> REAC_CTRL_IDENTITY_REPLY with ra = 0x81ff4 and touches no memory; this file composes
      it with f9_evtA_F into ONE footprint run (f9g_run below, by Lib.ExecF.evtF_cut), and applies the callee AT
      ITS ENTRY in cgif caller-journal form as ACtl.v's Section hypothesis TREPLY.
   C  f9_evtB_post_F (F9F.v:293) is EMPTY: the return pc 0x81ff4 IS the exit cut C_A81ff4_at, so the callee's post
      rebuilds that cut's body directly (f9g_exit_body below).

   THE PROOF (glue-pattern.md section 3)
   G1  unfold the entry cut C_A81f88_at (ACtlCutP.v:2135-2146) at index [Z.of_nat j].
   G2  bounds from VISIBLE state only: the owned class-6 frame (KitMem.kitmem_own6: fr = frame_addr ly3 6 (c_fpos
       cx), 4096 <= fr, fr mod 32 = 0, fr + 4096 <= alloc_ceiling <= c_sp cx - LLVMF_STK), the record block
       (phi, flen cx j) of the body's Permutation through the AR block law, and FRAC's spill base A with
       c_sp cx - 4096 < sp <= A, A + 416 <= c_sp cx < APPMEM_END.
   G3  ProgBridge.cfg_at_MS, then the walk moved from the cut's map regs3 to the run's canonical map
       (YA0nR.SRr_xregs_eqv); the run's kept register binders are instantiated with getr regs3 r, so the run's
       start state is the cut's by conversion.
   G4  the composed run at RNG := ProgBridge.RNG_W (w_H W3), lifted ONCE by YA0nR.SRr_fsteps; the journal crosses it
       by a Theorem Labs lane's PROVED ProgWorld.ajournal_of_fsteps, with the six stores' write set f9_WA discharged against
       awr_byte's frame case (f9g_awr).
   G5  the callee at its entry (TREPLY) through YA0n.SRr_bind, then the exit cut C_A81ff4_at at the callee's
       return state: journal from the callee's post, frames / frame law / k bound unchanged, the body rebuilt by
       f9g_exit_body, and ctl_rt_C by a Theorem Labs lane's PROVED ProgWorldCtlRtC.ctl_rt_C_of_AR over the AR of the exit
       journal and the entry's arodata_okS carried by KitMem.kitmem_arodataS_journal.

   ROUTE (C) (a working branch shell 1899bed1aee): the cut carries A.ACtlRtC.ctl_rt_C B ly3 S3
   mem3 in place of ctl_rt mem3.  The stage's one shadow consumption, the writability of the owned class-6 frame's
   shadow [Sfr fr, Sfr fr + 392) for f9_evtA_F's wr_at premise (f9g_entry), reads ctl_rt_C's (F) region: the frame
   (6, c_fpos cx) is in frames S3 and frame_addr ly3 6 (c_fpos cx) = fr (kitmem_own6).  The exit's ctl_rt_C is
   ctl_rt_C_of_AR (CtrlTSyms + AR_laws only); VIS0 / OWNED_RO are gone.

   WHY THIS FILE HAS ITS OWN TRANSPORTS (a Theorem Labs lane's ruling, 04:4xZ: one local Qed lemma per stage where a v1.9
   keep lemma does not apply, with the reason recorded).  MEASURED: Seg/F9.v's keep lemmas CANNOT be reused here.
   f9_fra_st (:2042), f9_fra_call (:1680) and f9_exit_of (:2858) take SlotInv.FRA at the entry AND at the exit (RT,
   aa_AH, the FakeStack placement: frame-route facts a cut does not give), and their callee step is
   `munch (f9_WC ...)`, the frame-route contract's write list.  The cgif-form reply spec gives no munch at all: its
   post gives tcj_kept (CtrlCallerJ.v:40-52), i.e. aview equality on four classes of address.  So the carried part
   of the body moves here along the byte agreement f9_rkeep on the footprint f9_K (both below), and FRAC moves by
   its SHAPE (f9g_frac_keep), which also carries batch3's appended trailer conjunct q64 (fr + 4088).
   Three ACtlCutP / SlotInv transcription differences recorded with that ruling and relevant here: ACtlCutP.f1_IN
   (:658) drops SlotInv.f1_IN's ghost-heap conjunct, ACtlCutP.b5_C (:820) drops b5_FS, ACtlCutP.b5_PH (:776) drops
   the empty-frame FakeStack conjunct and reads Reusable.YG0d.spZ where SlotInv reads AC.aspZ.

   CAVEAT (two Theorem Labs lanes, internal path; a Theorem Labs lane 05:52Z).  Two shadow reads
   of this stage go through TFIB_SYMS' ts_zsh:
   - the shadow byte of the kind-name string X = kind_name_addr (t_k g j).  For the nine strings whose first
     granule is full (0x21260 0x21280 0x212a0 0x212e0 0x21320 0x21340 0x21360 0x21380 0x213c0) the record AF0m
     (a working branch e56483f863b, Tfib_zero_shadow :2955-2964) has a zero row, and this
     file NAMES NO ROW BY POSITION (it finds one by a boolean search), so the proof runs on the record too.  For
     the five PARTIAL-granule strings 0x21220 (5 bytes) 0x21240 (7) 0x212c0 (6) 0x21300 (7) 0x213a0 (6) there is no
     zero row on the record: their shadow is the record's Tfib_const_shadow rows (record AF0m.v:2187, :2191, :2203,
     :2210, :2224).  Those five rows are now PROVED here, by computation, as f9g_rec_kn_shadow: the interim base's
     lib/A/AF0m.v IS the record file (blob 44930bfd861 (the blob this tree had at release c5e779efe8c) = e56483f863b's, checked by a Theorem Labs lane), so the step holds on
     the record AND on the base, and no hypothesis is left for it.  They are used through the local
     f9g_kn_gshadow.  On the PLANNING core those five granules came instead from the row (0x20ec0, 0xa4380 -
     0x20ec0), which the measurement above calls a defect; that core is no longer the one this file builds on.
   - KIND_NAME's 14 shadow bytes, shadow of [0x9e760, 0x9e7d0): the record's row (0x21aa0, 0x9e7d0 - 0x21aa0)
     covers them, so that one holds on the record as well (again found, not named by position).
   No other start-up table VALUE is read: not Tfib_const_abs / am_const, not Tfib_owned_static, not the AB01
   hand-off, no port_core_refused_<hex> literal, and none of TFIB_GP / ts_gp, pc_wrap_memcmp, pc_wrap_bcmp,
   pc_stack_malloc, 0x9fe18, 0xa2878 (a Theorem Labs lane 06:15Z).  getr regs 3 = w64 (as_gp B) comes from the ENTRY's afn_pre
   through FRAC's `getr regs 3 = getr (c_regs cx) 3`, never from TfibLib's gp value.

   SECTION HYPOTHESES (exact text below; each is ACtl.v's Section hypothesis of the same name and text)
   - LAWS, RELRO_IMG, TFIB_SYMS: ACtl.v's.
   - TREPLY: a Theorem Labs lane's treac_ctrl_identity_reply_spec (lib/A/Prog/C_reac_ctrl_identity_reply.v) at
     SK := A.AE2k.tfib_sink_head, B, RLO RHI, as ACtl.v's TREPLY; its constants TREPLY_STK (= 144 +
     C_reac_ctrl_parse.REAC_CTRL_PARSE_STK) and EV_REPLY are cited by name from that file.

   CLOSURE (the glue closure rule): every Require below is qualified, no Import / Export of a project module; no
   statement here names a frame-route identifier (Seg/F9.v and SlotModel lemmas appear only inside proofs,
   qualified).  The six modules that exist both as lib/Reusable/<X> and as lib/A/Reusable/<X> (YI04 YI16 YK11 YK1b
   YM05 YO09) and every lib/Lib module are loaded by ABSOLUTE Require and named in full (aliases K11 I04 LMS LRG
   LEX LMM LFR below): a `From ...lib Require Reusable.YK11` matches ctrl's lib.A.Reusable.YK11 by suffix.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are K11.* / Reusable.YG0d.*-qualified everywhere.  TWIN MODULES: YI00,
   YP09 and YK0s exist as lib/Reusable/<X> and lib/A/Reusable/<X>; they are Required absolutely and named only through
   the aliases CI00 / CP09 / CK0s, which name the core's copies (lib/Reusable), as a Theorem Labs lane's reply spec of record
   does (ctrlgate 81a8c99627b2 DUP / REQ, a Theorem Labs lane 09:09Z; before, the partial `Reusable.YI00.garr8` /
   `Reusable.YP09.mbyte` / `Reusable.YK0s.ret_ok` bound the lib/A/Reusable copies by Locate; the bodies convert).

   ROUTE (C) BUILD STATE: type-check rc=0 on a working branch shell 1899bed1aee (cb build, a build machine, log
   (internal path), build 2026-10-29T13:05:56Z); build of record: a Theorem Labs lane's cbrec record
   over lib/A/ACtlG/L3W4bAudit.v (not in this delivery).  The paragraph below is the pre-route-(C) state.
   BUILD STATE (honest): TYPE-CHECK ONLY (no value of a type-check build counts).  Type-check on
   5da74c9c931, closure reaches no stand-in: rc=0 on a working branch (glue base a1debf82953 =
   29ddfc3ea99 + batch 4 A / A2, KitMem 81524d6c608), built by cb build (VM
   a build machine, BASE row 23b918fe0c2e) with NO port_core_refused substitution and no AD2l stand-in: log
   build 2026-10-29T09:24:38Z (this file; the chain under it at
   build-20261029T092226Z.log and, with the Tk/AW/SmLeaf and SmLib lines, build-20261029T075755Z.log).  `Print
   Assumptions glue_seg_F9` (same log, the command is the file's last line) lists only Rocq's kernel primitives
   (PrimInt63 / PrimString / PrimArray) and FunctionalExtensionality.functional_extensionality_dep, which the two
   lifts bring; `Print Assumptions f9g_rec_kn_shadow` is `Closed under the global context`.  No Axiom, no Parameter,
   no Admitted, no admit, no Abort. *)
From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f Reusable.YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq Reusable.YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0v.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI00 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.AF0m A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldCtlRt.
(* route (C): the cut's narrowed runtime conjunct ctl_rt_C (A.ACtlRtC) and its proof from AR at the exit
   (A.ProgWorldCtlRtC.ctl_rt_C_of_AR) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlRtC ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisWin A.ProgWorldVisFrame A.ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.CtrlImg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.CtrlCallerJ.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ctrl_identity_reply_c A.Prog.reac_ctrl_kind_name_c.
(* the callee's spec of record, ACtl.v's Section hypothesis TREPLY (its stack constant TREPLY_STK is 144 +
   C_reac_ctrl_parse.REAC_CTRL_PARSE_STK) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_ctrl_parse C_reac_ctrl_identity_reply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F9 A.Prog.Seg.F9F.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcReply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcKind.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem A.ProgWorldShadow.
Import ListNotations.
Local Open Scope Z_scope.

Module K11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module I04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
(* the core's copies (lib/Reusable), as a Theorem Labs lane's reply spec of record names them; lib/A/Reusable has twins of all three
   (ctrlgate DUP / REQ, a Theorem Labs lane 09:09Z), so they are named only through these aliases. *)
Module CI00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI00.
Module CP09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Module CK0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LEX := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LMM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module RRP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcReply.
Module RKN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcKind.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module KNA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_kind_name_c.

Local Notation segs := A.AB1v.tfibsegs.

(* The register map at the start of the _F runs, written over the core's getr (Seg/F9.v:3334 states the same
   equation over ctrl's getr). *)
Lemma f9g_mkR_of : forall R, LRG.mkR_of R =
  LFR.mkR (K11.getr R 1) (K11.getr R 2) (K11.getr R 3) (K11.getr R 4) (K11.getr R 5) (K11.getr R 6)
  (K11.getr R 7) (K11.getr R 8) (K11.getr R 9) (K11.getr R 10) (K11.getr R 11) (K11.getr R 12)
  (K11.getr R 13) (K11.getr R 14) (K11.getr R 15) (K11.getr R 16) (K11.getr R 17) (K11.getr R 18)
  (K11.getr R 19) (K11.getr R 20) (K11.getr R 21) (K11.getr R 22) (K11.getr R 23) (K11.getr R 24)
  (K11.getr R 25) (K11.getr R 26) (K11.getr R 27) (K11.getr R 28) (K11.getr R 29) (K11.getr R 30) (K11.getr R 31).
Proof. intros R. reflexivity. Qed.

(* getr at a literal index reads the same as at Z_to_bv 5 of it (aregs_preserved is stated with Z_to_bv 5). *)
Lemma f9g_getr_lit : forall R, K11.getr R (Z_to_bv 5 18) = K11.getr R 18.
Proof. intros R. reflexivity. Qed.

(* f9_evtA_F then f9_evtB_pre_F (Seg/F9F.v:107, :267) as ONE footprint run, 0x81f88 -> the callee entry
   REAC_CTRL_IDENTITY_REPLY with ra = 0x81ff4: evtF_cut of the two, f9_evtA_F's continuation is the second run. *)
Lemma f9g_run : forall (RNG : LEX.footprint)
    (ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X A S3 fr phi len : Z) (b c0 : byte),
  0 <= X < 2 ^ 47 -> 0 <= S3 -> 0 <= fr -> 0 <= A ->
  fr + ACtlCutP.FRAME_BYTES <= A -> A + 416 <= 2 ^ 64 -> S3 + ACtlCutP.FRAME_SHADOW <= A ->
  (S3 + ACtlCutP.FRAME_SHADOW <= fr \/ fr + ACtlCutP.FRAME_BYTES <= S3) ->
  ov_read_bytes A.Img0.rsegs m (LMM.wa (X / 8 + A.AsanRT.ASAN_K)) 1 = Some [b] ->
  (bv_signed b = 0 \/ X mod 8 < bv_signed b) ->
  ov_read_bytes A.Img0.rsegs m (LMM.wa X) 1 = Some [c0] -> bv_unsigned c0 <> 63 ->
  LMM.wr_at A.Img0.rsegs m S3 ACtlCutP.FRAME_SHADOW ->
  LMM.wr_at A.Img0.rsegs m (fr + 256) 2 -> LMM.wr_at A.Img0.rsegs m (fr + 272) 8 ->
  LMM.wr_at A.Img0.rsegs m (fr + 304) 8 ->
  LMM.bytes_at A.Img0.rsegs m (A + 256) (LMM.le8 (Z_to_bv 64 (fr + 256))) ->
  LMM.bytes_at A.Img0.rsegs m (A + 272) (LMM.le8 (Z_to_bv 64 (fr + 272))) ->
  LMM.bytes_at A.Img0.rsegs m (A + 264) (LMM.le8 (Z_to_bv 64 (fr + 304))) ->
  LEX.rng RNG (X / 8 + A.AsanRT.ASAN_K) 1 -> LEX.rng RNG X 1 -> LEX.rng RNG S3 ACtlCutP.FRAME_SHADOW ->
  LEX.rng RNG (fr + 256) 2 -> LEX.rng RNG (fr + 272) 8 -> LEX.rng RNG (fr + 304) 8 ->
  LEX.rng RNG (A + 256) 8 -> LEX.rng RNG (A + 272) 8 -> LEX.rng RNG (A + 264) 8 ->
  LEX.evtF A.Img0.rsegs RNG
    (fun ms => exists m1,
       ms = LMS.MS (LFR.mkR (Z_to_bv 64 0x81ff4) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 phi)
                     (Z_to_bv 64 len) (Z_to_bv 64 (fr + 256)) (Z_to_bv 64 (fr + 272)) (Z_to_bv 64 (fr + 304))
                     a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 S3) s4 s5 s6 (Z_to_bv 64 phi) s8 s9
                     (Z_to_bv 64 A.AsanRT.ASAN_K) s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 A.Prog.reac_ctrl_identity_reply_c.REAC_CTRL_IDENTITY_REPLY) fc None m1
              (K11.seg_rom A.Img0.rsegs) /\
       LFR.munch (A.Prog.Seg.F9.f9_WA S3 fr) m m1 /\
       LMM.bytes_at A.Img0.rsegs m1 (S3 + 32) (LMM.le1 (Z_to_bv 64 2)) /\
       LMM.bytes_at A.Img0.rsegs m1 (S3 + 34) (LMM.le1 (Z_to_bv 64 0)) /\
       LMM.bytes_at A.Img0.rsegs m1 (S3 + 38) (LMM.le1 (Z_to_bv 64 0)) /\
       LMM.bytes_at A.Img0.rsegs m1 (fr + 256) (LMM.le2 (Z_to_bv 64 0)) /\
       LMM.bytes_at A.Img0.rsegs m1 (fr + 272) (LMM.le8 (Z_to_bv 64 0)) /\
       LMM.bytes_at A.Img0.rsegs m1 (fr + 304) (LMM.le8 (Z_to_bv 64 0)))
    (LMS.MS (LFR.mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 len) (Z_to_bv 64 S3) s4 s5 s6 (Z_to_bv 64 phi) s8 s9 (Z_to_bv 64 A.AsanRT.ASAN_K) s11
               t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x81f88) fc None m (K11.seg_rom A.Img0.rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 Fr fc m X A S3 fr phi len
    b c0 HX HS30 Hfr0 HA0 HfrA HA64 HS3A HS3fr RK OK RC0 HC0 Wsh Wa Wp Wn Q256 Q272 Q264
    RSH RX RWSH R256 R272 R304 RS256 RS272 RS264.
  eapply LEX.evtF_cut; [| intros ms' Hms'; exact Hms'].
  apply (A.Prog.Seg.F9F.f9_evtA_F RNG ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6
           Fr fc m _ X A S3 fr phi len b c0 HX HS30 Hfr0 HA0 HfrA HA64 HS3A HS3fr RK OK RC0 HC0 Wsh Wa Wp Wn
           Q256 Q272 Q264); [| exact RSH | exact RX | exact RWSH | exact R256 | exact R272 | exact R304
                             | exact RS256 | exact RS272 | exact RS264].
  intros m1 MU _ _ B32 B34 B38 Ba Bp Bn _ _ _.
  eapply LEX.evtF_mono; [apply A.Prog.Seg.F9F.f9_evtB_pre_F|].
  intros ms' ->. exists m1. split; [reflexivity|].
  exact (conj MU (conj B32 (conj B34 (conj B38 (conj Ba (conj Bp Bn)))))).
Qed.

(* The byte agreement the exit body is carried by: every byte of K that m reads, m' reads the same. *)
Definition f9_rkeep (K : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a, K a -> 0 <= a < 2 ^ 64 -> forall b,
    LMM.mrd A.Img0.rsegs m (LMM.wa a) = Some b -> LMM.mrd A.Img0.rsegs m' (LMM.wa a) = Some b.

(* The footprint of the exit body's carried part (C_A81f88_at's body minus what the run and the call change):
   the s1 spill area [A, A + 416), the saved caller registers [c_sp - 104, c_sp), the class-6 frame minus the
   three reply cells, the frame shadow minus the three bytes phase A writes, the record block and its shadow,
   the input block and its shadow, the kind-name table KIND_NAME and its shadow. *)
Definition f9_K (cx : ACtlCut.ctlcx) (j : nat) (fr A phi : Z) (a : Z) : Prop :=
  (A <= a < A + 416) \/
  (ACtlCut.c_sp cx - 104 <= a < ACtlCut.c_sp cx) \/
  ((fr <= a < fr + 256) \/ (fr + 258 <= a < fr + 272) \/ (fr + 280 <= a < fr + 304) \/ (fr + 312 <= a < fr + 4096)) \/
  (ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 /\
     a <> ACtlCutP.Sfr fr + 32 /\ a <> ACtlCutP.Sfr fr + 34 /\ a <> ACtlCutP.Sfr fr + 38) \/
  (phi <= a < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j)) \/
  (A.AsanRT.shadow_addr phi <= a < A.AsanRT.shadow_addr phi + (Reusable.YG00.req_size (ACtlCutP.flen cx j) + 7) / 8) \/
  (ACtlCut.c_p cx <= a < ACtlCut.c_p cx + ACtlCut.c_n cx) \/
  (0 < ACtlCut.c_n cx /\
     A.AsanRT.shadow_addr (ACtlCut.c_p cx) <= a < A.AsanRT.shadow_addr (ACtlCut.c_p cx) + (ACtlCut.c_n cx + 7) / 8) \/
  (KNA.KIND_NAME <= a < KNA.KIND_NAME + 112) \/
  (A.AsanRT.shadow_addr KNA.KIND_NAME <= a < A.AsanRT.shadow_addr KNA.KIND_NAME + 14).

Ltac f9t_cs := unfold Reusable.YG0d.acallee_saved; lia.

Lemma f9t_bytes : forall (K : Z -> Prop) m m' a bs, f9_rkeep K m m' -> LMM.bytes_at A.Img0.rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> K x) -> LMM.bytes_at A.Img0.rsegs m' a bs.
Proof.
  intros K m m' a bs HK (H0 & H1 & H) HI. split; [exact H0|]. split; [exact H1|].
  intros i Hi. pose proof (H i Hi) as E.
  destruct (nth_error bs i) as [b|] eqn:En; [|apply nth_error_None in En; lia].
  try rewrite En in E.
  apply (HK (a + Z.of_nat i)); [apply HI; lia | lia | exact E].
Qed.

Lemma f9t_q64 : forall (K : Z -> Prop) m m' a v, f9_rkeep K m m' -> ACtlCutP.q64 m a v ->
  (forall x, a <= x < a + 8 -> K x) -> ACtlCutP.q64 m' a v.
Proof.
  intros K m m' a v HK H HI. unfold ACtlCutP.q64 in *. apply (f9t_bytes K m m' a _ HK H).
  rewrite LMM.length_le8. exact HI.
Qed.

Lemma f9t_addr : forall (K : Z -> Prop) m m' p n, f9_rkeep K m m' -> A.AsanRT.addressable m p n ->
  (forall x, p <= x < p + n -> K (A.AsanRT.shadow_addr x)) -> A.AsanRT.addressable m' p n.
Proof.
  intros K m m' p n HK (H1 & H2 & H3 & H) HI. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  apply (HK (A.AsanRT.shadow_addr (p + i))); [apply HI; lia | | exact Hb].
  unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. unfold A.AsanRT.APPMEM_END in H3. Z.div_mod_to_equations. lia.
Qed.

(* Two values of one register, both in [0, 2^64), are equal. *)
Lemma f9t_rgv_eq : forall (regs : bvmap 5 word) (r : bv 5) (a b : Z), ACtlCut.rgv regs r a -> ACtlCut.rgv regs r b ->
  0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof.
  intros regs r a b Ha Hb Ha0 Hb0. unfold ACtlCut.rgv in *. rewrite Ha in Hb.
  apply (f_equal bv_unsigned) in Hb. rewrite !Z_to_bv_unsigned in Hb. unfold bv_wrap in Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. rewrite !Z.mod_small in Hb by lia. exact Hb.
Qed.

(* The regions of f9_K. *)
Lemma f9t_K_A : forall cx j fr A phi x, A <= x < A + 416 -> f9_K cx j fr A phi x.
Proof. intros cx j fr A phi x H. unfold f9_K. left. exact H. Qed.

Lemma f9t_K_sv : forall cx j fr A phi x, ACtlCut.c_sp cx - 104 <= x < ACtlCut.c_sp cx -> f9_K cx j fr A phi x.
Proof. intros cx j fr A phi x H. unfold f9_K. right; left. exact H. Qed.

Lemma f9t_K_fr : forall cx j fr A phi x,
  (fr <= x < fr + 256) \/ (fr + 258 <= x < fr + 272) \/ (fr + 280 <= x < fr + 304) \/ (fr + 312 <= x < fr + 4096) ->
  f9_K cx j fr A phi x.
Proof. intros cx j fr A phi x H. unfold f9_K. right; right; left. exact H. Qed.

(* A frame byte off the granules of the three reply cells has its shadow byte in the kept frame shadow. *)
Lemma f9t_K_frsh : forall cx j fr A phi x, 0 <= fr -> fr mod 32 = 0 ->
  (fr <= x < fr + 256) \/ (fr + 264 <= x < fr + 272) \/ (fr + 280 <= x < fr + 304) \/ (fr + 312 <= x < fr + 4096) ->
  f9_K cx j fr A phi (A.AsanRT.shadow_addr x).
Proof.
  intros cx j fr A phi x H0 H32 Hx. unfold f9_K. right; right; right; left.
  unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Lemma f9t_K_phi : forall cx j fr A phi x, phi <= x < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) ->
  f9_K cx j fr A phi x.
Proof. intros cx j fr A phi x H. unfold f9_K. do 4 right. left. exact H. Qed.

Lemma f9t_K_phish : forall cx j fr A phi x, 0 <= phi -> phi mod 8 = 0 ->
  phi <= x < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) -> f9_K cx j fr A phi (A.AsanRT.shadow_addr x).
Proof.
  intros cx j fr A phi x H0 H8 Hx. unfold f9_K. do 5 right. left.
  set (R := Reusable.YG00.req_size (ACtlCutP.flen cx j)) in *. clearbody R.
  unfold A.AsanRT.shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Lemma f9t_K_in : forall cx j fr A phi x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + ACtlCut.c_n cx ->
  f9_K cx j fr A phi x.
Proof. intros cx j fr A phi x H. unfold f9_K. do 6 right. left. exact H. Qed.

Lemma f9t_K_insh : forall cx j fr A phi x, 0 <= ACtlCut.c_p cx -> ACtlCut.c_p cx mod 8 = 0 ->
  ACtlCut.c_p cx <= x < ACtlCut.c_p cx + ACtlCut.c_n cx -> f9_K cx j fr A phi (A.AsanRT.shadow_addr x).
Proof.
  intros cx j fr A phi x H0 H8 Hx. unfold f9_K. do 7 right. left. split; [lia|].
  set (p := ACtlCut.c_p cx) in *. set (n := ACtlCut.c_n cx) in *. clearbody p n.
  unfold A.AsanRT.shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Lemma f9t_K_kn : forall cx j fr A phi x, KNA.KIND_NAME <= x < KNA.KIND_NAME + 112 -> f9_K cx j fr A phi x.
Proof. intros cx j fr A phi x H. unfold f9_K. do 8 right. left. exact H. Qed.

Lemma f9t_K_knsh : forall cx j fr A phi x, KNA.KIND_NAME <= x < KNA.KIND_NAME + 112 ->
  f9_K cx j fr A phi (A.AsanRT.shadow_addr x).
Proof.
  intros cx j fr A phi x H. unfold f9_K. do 9 right.
  unfold A.AsanRT.shadow_addr, KNA.KIND_NAME in *. Z.div_mod_to_equations. lia.
Qed.

(* T1: the carried body bundles move along a byte agreement on f9_K and a map that keeps the callee-saved
   registers.  FLSH's frame presence (FRM.stk over the whole frame, cells included) is given at m'. *)
Lemma f9g_body_keep : forall cx j fr A phi (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  f9_rkeep (f9_K cx j fr A phi) m m' ->
  Reusable.YG0d.aregs_preserved regs regs' ->
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= A.AsanRT.APPMEM_END ->
  0 <= fr -> fr mod 32 = 0 -> fr + 4096 <= A.AsanRT.APPMEM_END ->
  0 <= phi -> phi mod 8 = 0 -> 0 <= ACtlCutP.flen cx j ->
  phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) <= A.AsanRT.APPMEM_END ->
  (0 < ACtlCut.c_n cx -> ACtlCut.c_p cx mod 8 = 0) ->
  Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx ->
  LFR.stk A.Img0.rsegs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.LK cx fr j regs m -> ACtlCutP.b5_C cx j phi fr regs m ->
  ACtlCutP.b5_K cx j phi fr regs m -> ACtlCutP.IDj cx fr j m -> ACtlCutP.b5_F17 cx j phi fr regs m ->
  ACtlCutP.b5_W240 cx j regs m -> ACtlCutP.b5_PF cx j phi fr regs m ->
  ACtlCutP.FLSI cx j fr regs' m' /\ ACtlCutP.LK cx fr j regs' m' /\ ACtlCutP.b5_C cx j phi fr regs' m' /\
  ACtlCutP.b5_K cx j phi fr regs' m' /\ ACtlCutP.IDj cx fr j m' /\ ACtlCutP.b5_F17 cx j phi fr regs' m' /\
  ACtlCutP.b5_W240 cx j regs' m' /\ ACtlCutP.b5_PF cx j phi fr regs' m'.
Proof.
  intros cx j fr A phi regs regs' m m' HK HP R9 HA0 HA HF0 HF32 HF HP0 HP8 HL0 HLP HCP HCN HSTK
    HFLSI HLK HbC HbK HIDj HF17 HW240 HPF.
  (* registers: the seven register-reading bundles move to regs' at m (KitMem.kitmem_b5_keep) *)
  assert (E2 : K11.getr regs' 2 = K11.getr regs 2) by exact (HP 2 ltac:(f9t_cs)).
  assert (E9 : K11.getr regs' 9 = K11.getr regs 9) by exact (HP 9 ltac:(f9t_cs)).
  assert (E18 : K11.getr regs' 18 = K11.getr regs 18) by exact (HP 18 ltac:(f9t_cs)).
  assert (E20 : K11.getr regs' 20 = K11.getr regs 20) by exact (HP 20 ltac:(f9t_cs)).
  assert (E21 : K11.getr regs' 21 = K11.getr regs 21) by exact (HP 21 ltac:(f9t_cs)).
  assert (E22 : K11.getr regs' 22 = K11.getr regs 22) by exact (HP 22 ltac:(f9t_cs)).
  assert (E23 : K11.getr regs' 23 = K11.getr regs 23) by exact (HP 23 ltac:(f9t_cs)).
  assert (E24 : K11.getr regs' 24 = K11.getr regs 24) by exact (HP 24 ltac:(f9t_cs)).
  assert (E25 : K11.getr regs' 25 = K11.getr regs 25) by exact (HP 25 ltac:(f9t_cs)).
  destruct (A.ACtlG.KitMem.kitmem_b5_keep cx j phi fr regs regs' m E2 E9 E18 E20 E21 E22 E23 E24 E25
              HFLSI HLK HbC HbK HF17 HW240 HPF) as (HFLSI' & HLK' & HbC' & HbK' & HF17' & HW240' & HPF').
  clear HFLSI HLK HbC HbK HF17 HW240 HPF.
  assert (R9' : ACtlCut.rgv regs' 9 A) by (unfold ACtlCut.rgv in *; rewrite E9; exact R9).
  pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx j) HL0) as Hreq.
  unfold A.AsanRT.APPMEM_END in HA, HF, HLP.
  (* memory: the transports at regs', one per region of f9_K *)
  assert (TA : forall off v, 0 <= off -> off + 8 <= 416 ->
            ACtlCutP.q64 m (A + off) v -> ACtlCutP.q64 m' (A + off) v).
  { intros off v Ho Ho' Hq. apply (f9t_q64 _ m m' _ v HK Hq). intros x Hx. apply f9t_K_A. lia. }
  assert (Tsp : forall off v, 0 <= off -> off + 8 <= 416 ->
            ACtlCutP.spill regs' m off v -> ACtlCutP.spill regs' m' off v).
  { intros off v Ho Ho' Hs. exists A. split; [exact R9'|]. apply (TA off v Ho Ho').
    exact (A.ACtlG.KitMem.kitmem_spill_q64 regs' m off v A Hs R9' HA0 Ho ltac:(lia)). }
  assert (TF : forall a bs, LMM.bytes_at A.Img0.rsegs m a bs ->
            (fr <= a /\ a + Z.of_nat (length bs) <= fr + 256) \/
            (fr + 312 <= a /\ a + Z.of_nat (length bs) <= fr + 4096) ->
            LMM.bytes_at A.Img0.rsegs m' a bs).
  { intros a bs Hb Ha. apply (f9t_bytes _ m m' a bs HK Hb). intros x Hx. apply f9t_K_fr. lia. }
  assert (TFS : forall p n, A.AsanRT.addressable m p n ->
            (fr <= p /\ p + n <= fr + 256) \/ (fr + 312 <= p /\ p + n <= fr + 4096) ->
            A.AsanRT.addressable m' p n).
  { intros p n Hb Hp. apply (f9t_addr _ m m' p n HK Hb). intros x Hx.
    apply f9t_K_frsh; [exact HF0 | exact HF32 | lia]. }
  assert (TP : forall a bs, LMM.bytes_at A.Img0.rsegs m a bs -> phi <= a ->
            a + Z.of_nat (length bs) <= phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) ->
            LMM.bytes_at A.Img0.rsegs m' a bs).
  { intros a bs Hb H1 H2. apply (f9t_bytes _ m m' a bs HK Hb). intros x Hx. apply f9t_K_phi. lia. }
  assert (TIN : LMM.bytes_at A.Img0.rsegs m (ACtlCut.c_p cx) (ACtlCut.c_in cx) ->
            LMM.bytes_at A.Img0.rsegs m' (ACtlCut.c_p cx) (ACtlCut.c_in cx)).
  { intros Hb. apply (f9t_bytes _ m m' _ _ HK Hb). intros x Hx. apply f9t_K_in. lia. }
  assert (TINA : A.AsanRT.addressable m (ACtlCut.c_p cx) (ACtlCut.c_n cx) ->
            A.AsanRT.addressable m' (ACtlCut.c_p cx) (ACtlCut.c_n cx)).
  { intros Ha. pose proof Ha as (Hp0 & _ & _ & _). apply (f9t_addr _ m m' _ _ HK Ha). intros x Hx.
    apply f9t_K_insh; [exact Hp0 | apply HCP; lia | exact Hx]. }
  (* FLSI = FLSH (PRO, FRM.stk, two spills, a shadow window), three spills, f1_IN, FLC *)
  split.
  { unfold ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.PRO, ACtlCutP.f1_IN, ACtlCutP.FLC, ACtlCutP.fragb in *.
    destruct HFLSI' as (((P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & PA & PIN & PINA & P184 & P256 &
        P264 & P272 & P32) & H128 & _ & H144 & HA17) & H216 & H224 & H248 & (INA & INB) &
      (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & CAfg & CAid & C72 & C64 & C56 & C48)).
    split.
    - split.
      + split; [exact (Tsp 40 _ ltac:(lia) ltac:(lia) P40)|].
        split; [exact (Tsp 120 _ ltac:(lia) ltac:(lia) P120)|].
        split; [exact (Tsp 136 _ ltac:(lia) ltac:(lia) P136)|].
        split; [exact (Tsp 160 _ ltac:(lia) ltac:(lia) P160)|].
        split; [exact (Tsp 168 _ ltac:(lia) ltac:(lia) P168)|].
        split; [exact (Tsp 176 _ ltac:(lia) ltac:(lia) P176)|].
        split; [exact (Tsp 208 _ ltac:(lia) ltac:(lia) P208)|].
        split; [exact (Tsp 248 _ ltac:(lia) ltac:(lia) P248)|].
        split; [exact (TFS _ _ PA ltac:(lia))|].
        split; [exact (TIN PIN)|].
        split; [intros Hn; exact (TINA (PINA Hn))|].
        split; [exact (Tsp 184 _ ltac:(lia) ltac:(lia) P184)|].
        split; [exact (Tsp 256 _ ltac:(lia) ltac:(lia) P256)|].
        split; [exact (Tsp 264 _ ltac:(lia) ltac:(lia) P264)|].
        split; [exact (Tsp 272 _ ltac:(lia) ltac:(lia) P272)|].
        exact (Tsp 32 _ ltac:(lia) ltac:(lia) P32).
      + split; [exact (Tsp 128 _ ltac:(lia) ltac:(lia) H128)|].
        split; [exact HSTK|].
        split; [exact (Tsp 144 _ ltac:(lia) ltac:(lia) H144)|].
        exact (TFS _ _ HA17 ltac:(lia)).
    - split; [exact (Tsp 216 _ ltac:(lia) ltac:(lia) H216)|].
      split; [exact (Tsp 224 _ ltac:(lia) ltac:(lia) H224)|].
      split; [exact (Tsp 248 _ ltac:(lia) ltac:(lia) H248)|].
      split; [split; [exact (TINA INA) | exact (TIN INB)]|].
      split; [exact (Tsp 256 _ ltac:(lia) ltac:(lia) C256)|].
      split; [exact (Tsp 184 _ ltac:(lia) ltac:(lia) C184)|].
      split; [exact (Tsp 192 _ ltac:(lia) ltac:(lia) C192)|].
      split; [exact (Tsp 80 _ ltac:(lia) ltac:(lia) C80)|].
      split; [exact (Tsp 88 _ ltac:(lia) ltac:(lia) C88)|].
      split; [exact (Tsp 96 _ ltac:(lia) ltac:(lia) C96)|].
      split; [exact (Tsp 272 _ ltac:(lia) ltac:(lia) C272)|].
      split; [exact (Tsp 264 _ ltac:(lia) ltac:(lia) C264)|].
      split; [exact (TFS _ _ CAfg ltac:(lia))|].
      split; [exact (TFS _ _ CAid ltac:(lia))|].
      split; [exact (Tsp 72 _ ltac:(lia) ltac:(lia) C72)|].
      split; [exact (Tsp 64 _ ltac:(lia) ltac:(lia) C64)|].
      split; [exact (Tsp 56 _ ltac:(lia) ltac:(lia) C56) | exact (Tsp 48 _ ltac:(lia) ltac:(lia) C48)]. }
  (* LK: the OUR bytes at fr + 2624 *)
  split.
  { destruct HLK' as (HLj & HL21 & HLour). split; [exact HLj|]. split; [exact HL21|].
    unfold ACtlCutP.OURb in *. apply (TF _ _ HLour). right. rewrite SM.OUR_length.
    change (Z.of_nat 6) with 6. lia. }
  (* b5_C *)
  split.
  { unfold ACtlCutP.b5_C, ACtlCutP.b5_SPILL, ACtlCutP.b5_PH, ACtlCutP.b5_FR, ACtlCutP.b5_KN, ACtlCutP.FGj,
      ACtlCutP.FGb, ACtlCutP.FGBe, ACtlCutP.FSj, ACtlCutP.FSb, ACtlCutP.fragb in *.
    destruct HbC' as (H23 & H18 & (A2 & HA2 & HA2b & (Q248 & Q256 & Q144 & Q184 & Q192 & Q80 & Q88 & Q96 & Q272 &
        Q264) & Q232) & (PH1 & PH2) & (FRa1 & FRa2 & FRb & FRl) & (KNb & KNa) & (FGb & FGok) &
      (S104 & S112 & Sbody & Saddr & SFI)).
    assert (EA2 : A2 = A) by exact (f9t_rgv_eq regs' 9 A2 A HA2 R9' HA2b ltac:(lia)). subst A2.
    split; [exact H23|]. split; [exact H18|].
    split.
    { exists A. split; [exact R9'|]. split; [exact HA2b|].
      split; [|exact (TA 232 _ ltac:(lia) ltac:(lia) Q232)].
      split; [exact (TA 248 _ ltac:(lia) ltac:(lia) Q248)|].
      split; [exact (TA 256 _ ltac:(lia) ltac:(lia) Q256)|].
      split; [exact (TA 144 _ ltac:(lia) ltac:(lia) Q144)|].
      split; [exact (TA 184 _ ltac:(lia) ltac:(lia) Q184)|].
      split; [exact (TA 192 _ ltac:(lia) ltac:(lia) Q192)|].
      split; [exact (TA 80 _ ltac:(lia) ltac:(lia) Q80)|].
      split; [exact (TA 88 _ ltac:(lia) ltac:(lia) Q88)|].
      split; [exact (TA 96 _ ltac:(lia) ltac:(lia) Q96)|].
      split; [exact (TA 272 _ ltac:(lia) ltac:(lia) Q272) | exact (TA 264 _ ltac:(lia) ltac:(lia) Q264)]. }
    split.
    { split; [|exact PH2].
      intros H50. apply (TP _ _ (PH1 H50)); [lia|].
      unfold SM.t_g. rewrite SM.fr50_length. change (Z.of_nat 50) with 50. lia. }
    split.
    { split; [exact (TFS _ _ FRa1 ltac:(lia))|]. split; [exact (TFS _ _ FRa2 ltac:(lia))|].
      split; [|exact FRl]. apply (TF _ _ FRb). right. rewrite FRl. change (Z.of_nat 72) with 72. lia. }
    split.
    { split.
      - apply (f9t_bytes _ m m' _ _ HK KNb). rewrite A.Prog.Seg.F9.f9_kn_len. intros x Hx. apply f9t_K_kn.
        change (Z.of_nat 112) with 112 in Hx. exact Hx.
      - apply (f9t_addr _ m m' _ _ HK KNa). intros x Hx. apply f9t_K_knsh. exact Hx. }
    split.
    { split; [|exact FGok]. apply (TF _ _ FGb). right. rewrite FRl. change (Z.of_nat 72) with 72. lia. }
    { split; [exact (Tsp 104 _ ltac:(lia) ltac:(lia) S104)|].
      split; [exact (Tsp 112 _ ltac:(lia) ltac:(lia) S112)|].
      split.
      - apply (TF _ _ Sbody). right.
        pose proof (A.Prog.Seg.F9.f9_fs_body_len (ACtlCut.c_in cx) j) as Hbl. lia.
      - split; [exact (TFS _ _ Saddr ltac:(lia)) | exact SFI]. } }
  (* b5_K: the [A + 280] spill and the kind word at fr + 176 *)
  split.
  { unfold ACtlCutP.b5_K, ACtlCutP.b5_sp, ACtlCutP.u32 in *.
    destruct HbK' as (K20 & K22 & K24 & K25 & (A2 & HA2 & HA2b & Q280) & U176 & Hargs).
    assert (EA2 : A2 = A) by exact (f9t_rgv_eq regs' 9 A2 A HA2 R9' HA2b ltac:(lia)). subst A2.
    split; [exact K20|]. split; [exact K22|]. split; [exact K24|]. split; [exact K25|].
    split; [exists A; split; [exact R9'|]; split; [exact HA2b | exact (TA 280 _ ltac:(lia) ltac:(lia) Q280)]|].
    split; [|exact Hargs].
    apply (TF _ _ U176). left. rewrite LMM.length_le4. change (Z.of_nat 4) with 4. lia. }
  (* IDj: the 38 identity bytes at fr + 2688 *)
  split.
  { unfold ACtlCutP.IDj, ACtlCutP.IDb, ACtlCutP.IDBe in *. destruct HIDj as (HIDb & HIDok).
    split; [|exact HIDok].
    apply (TF _ _ HIDb). right. rewrite A.Prog.Seg.F9.f9_tID_len. change (Z.of_nat 38) with 38. lia. }
  (* b5_F17 *)
  split.
  { destruct HF17' as (A2 & HA2 & HA2b & Q200).
    assert (EA2 : A2 = A) by exact (f9t_rgv_eq regs' 9 A2 A HA2 R9' HA2b ltac:(lia)). subst A2.
    exists A. split; [exact R9'|]. split; [exact HA2b | exact (TA 200 _ ltac:(lia) ltac:(lia) Q200)]. }
  (* b5_W240 *)
  split.
  { destruct HW240' as (A2 & HA2 & HA2b & w & Q240 & Hw).
    assert (EA2 : A2 = A) by exact (f9t_rgv_eq regs' 9 A2 A HA2 R9' HA2b ltac:(lia)). subst A2.
    exists A. split; [exact R9'|]. split; [exact HA2b|].
    exists w. split; [exact (TA 240 _ ltac:(lia) ltac:(lia) Q240) | exact Hw]. }
  (* b5_PF: the record bytes, and on the 8819 arm the parse bytes, their shadow and the two 6-byte compares
     (each compare operand cut to its first 6 bytes, which is all memcmp_model reads) *)
  { unfold ACtlCutP.b5_PF, ACtlCutP.u16, ACtlCutP.b8 in *.
    destruct HPF' as (A2 & HA2 & HA2b & HR50 & HR8819).
    assert (EA2 : A2 = A) by exact (f9t_rgv_eq regs' 9 A2 A HA2 R9' HA2b ltac:(lia)). subst A2.
    exists A. split; [exact R9'|]. split; [exact HA2b|].
    split.
    - intros H50. destruct (HR50 H50) as ((rb & Hrb & Hrbl) & Hphib).
      split.
      + exists (firstn 38 rb). split; [|rewrite length_firstn; lia].
        apply (TP _ _ (A.Prog.Seg.F9.f9_ba_firstn _ _ _ 38 Hrb)); [lia|]. rewrite length_firstn. lia.
      + apply (TP _ _ Hphib); [lia|].
        assert (Lp : (length (SM.t_phi (ACtlCut.c_in cx) j) <= Z.to_nat (ACtlCutP.flen cx j))%nat)
          by (unfold SM.t_phi, SM.f_phi, ACtlCutP.flen, SM.t_len; apply firstn_le_length).
        lia.
    - intros H8819.
      assert (H50 : 50 <= ACtlCutP.flen cx j).
      { pose proof H8819 as H8. unfold SM.t_8819, SM.t_big in H8. apply andb_prop in H8 as (H8 & _).
        apply andb_prop in H8 as (H8 & _). apply Z.leb_le in H8. exact H8. }
      destruct (HR8819 H8819) as ((f16 & v14 & v15 & v16 & v17 & U16 & B14 & B15 & B16 & B17 & V14 & V15 & V16 &
          V17 & S14 & S15 & S16 & S17 & EF & EK) &
        (ls & rs & Q72 & Hls & Hlsl & Hrs & Hrsl & Hcmp & Had186) &
        (ls2 & rs2 & Q64 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hcmp2 & Had180)).
      assert (TS : forall k, 14 <= k <= 17 ->
                LMM.bytes_at A.Img0.rsegs m (Z.shiftr (phi + k) 3 + A.ACtlK.ASAN_K) [Z_to_bv 8 0] ->
                LMM.bytes_at A.Img0.rsegs m' (Z.shiftr (phi + k) 3 + A.ACtlK.ASAN_K) [Z_to_bv 8 0]).
      { intros k Hk Hb. apply (f9t_bytes _ m m' _ _ HK Hb). intros x Hx. cbn [length] in Hx.
        change (Z.of_nat 1) with 1 in Hx.
        rewrite Z.shiftr_div_pow2 in Hx by lia. change (2 ^ 3) with 8 in Hx.
        replace x with (A.AsanRT.shadow_addr (phi + k)) by (unfold A.AsanRT.shadow_addr, A.ACtlK.ASAN_K in *; lia).
        apply f9t_K_phish; [exact HP0 | exact HP8 | lia]. }
      split.
      { exists f16, v14, v15, v16, v17.
        split; [apply (TF _ _ U16); left; rewrite LMM.length_le2; change (Z.of_nat 2) with 2; lia|].
        split; [apply (TP _ _ B14); [lia|]; cbn [length]; change (Z.of_nat 1) with 1; lia|].
        split; [apply (TP _ _ B15); [lia|]; cbn [length]; change (Z.of_nat 1) with 1; lia|].
        split; [apply (TP _ _ B16); [lia|]; cbn [length]; change (Z.of_nat 1) with 1; lia|].
        split; [apply (TP _ _ B17); [lia|]; cbn [length]; change (Z.of_nat 1) with 1; lia|].
        split; [exact V14|]. split; [exact V15|]. split; [exact V16|]. split; [exact V17|].
        split; [exact (TS 14 ltac:(lia) S14)|]. split; [exact (TS 15 ltac:(lia) S15)|].
        split; [exact (TS 16 ltac:(lia) S16)|]. split; [exact (TS 17 ltac:(lia) S17)|].
        split; [exact EF | exact EK]. }
      split.
      { exists (firstn 6 ls), (firstn 6 rs).
        assert (Lls : length (firstn 6 ls) = 6%nat) by (rewrite length_firstn; lia).
        assert (Lrs : length (firstn 6 rs) = 6%nat) by (rewrite length_firstn; lia).
        split; [exact (TA 72 _ ltac:(lia) ltac:(lia) Q72)|].
        split; [apply (TF _ _ (A.Prog.Seg.F9.f9_ba_firstn _ _ _ 6 Hls)); left; rewrite Lls;
                change (Z.of_nat 6) with 6; lia|].
        split; [lia|].
        split; [apply (TP _ _ (A.Prog.Seg.F9.f9_ba_firstn _ _ _ 6 Hrs)); [lia|]; rewrite Lrs;
                change (Z.of_nat 6) with 6; lia|].
        split; [lia|].
        split; [rewrite A.Prog.Seg.F9.f9_mcmp_firstn; exact Hcmp|].
        exact (TFS _ _ Had186 ltac:(lia)). }
      { exists (firstn 6 ls2), (firstn 6 rs2).
        assert (Lls : length (firstn 6 ls2) = 6%nat) by (rewrite length_firstn; lia).
        assert (Lrs : length (firstn 6 rs2) = 6%nat) by (rewrite length_firstn; lia).
        split; [exact (TA 64 _ ltac:(lia) ltac:(lia) Q64)|].
        split; [apply (TF _ _ (A.Prog.Seg.F9.f9_ba_firstn _ _ _ 6 Hls2)); left; rewrite Lls;
                change (Z.of_nat 6) with 6; lia|].
        split; [lia|].
        split; [apply (TP _ _ (A.Prog.Seg.F9.f9_ba_firstn _ _ _ 6 Hrs2)); [lia|]; rewrite Lrs;
                change (Z.of_nat 6) with 6; lia|].
        split; [lia|].
        split; [rewrite A.Prog.Seg.F9.f9_mcmp_firstn; exact Hcmp2|].
        exact (TFS _ _ Had180 ltac:(lia)). } }
Qed.

(* C1 helper: bytes that m holds at visible addresses are a garr8 of the restricted memory (the view reads them). *)
Lemma f9g_garr8_bytes : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (p : Z) (bs : list byte),
  LMM.bytes_at A.Img0.rsegs m p bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> Reusable.YA0n.w_H W (Z_to_bv 64 (p + i)) = false) ->
  CI00.garr8 segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) m) p (map bv_unsigned bs).
Proof.
  intros W m p bs (_ & _ & Hb) Hv j Hj. rewrite length_map in Hj.
  destruct (nth_error bs j) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  assert (Hn : nth j (map bv_unsigned bs) 0 = bv_unsigned b)
    by (apply nth_error_nth; rewrite nth_error_map, E; reflexivity).
  rewrite Hn. pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
  split; [|exact Rb].
  intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
  pose proof (Hb j Hj) as Hbj. rewrite E in Hbj.
  pose proof (Hv (Z.of_nat j) ltac:(lia)) as Hvj.
  assert (El : Z_to_bv 8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO0f.le_byte (bv_unsigned b) 1 0) = b).
  { unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO0f.le_byte.
    change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
    change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. apply Z_to_bv_bv_unsigned. }
  rewrite El.
  unfold CP09.mbyte, Reusable.YK04.mrestrict. rewrite Hvj.
  unfold LMM.mrd, LMM.wa in Hbj. exact Hbj.
Qed.

(* C2 helper: a byte of an out cell at fr + 8 c + i (i < 8, fr 32-aligned) has granule fr / 8 + c and offset i. *)
Lemma f9g_cell_div : forall fr c i, fr mod 32 = 0 -> 0 <= i < 8 ->
  (fr + 8 * c + i) / 8 = fr / 8 + c /\ (fr + 8 * c + i) mod 8 = i.
Proof.
  intros fr c i H32 Hi.
  pose proof (Z.div_mod fr 32 ltac:(lia)) as D32.
  pose proof (Z.div_mod fr 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound fr 8 ltac:(lia)) as M8.
  pose proof (Z.div_mod (fr + 8 * c + i) 8 ltac:(lia)) as Dx.
  pose proof (Z.mod_pos_bound (fr + 8 * c + i) 8 ltac:(lia)) as Mx.
  split; lia.
Qed.

Lemma f9g_cell_mod : forall fr c, fr mod 32 = 0 -> (fr + 8 * c) mod 2 = 0 /\ (fr + 8 * c) mod 8 = 0.
Proof.
  intros fr c H32.
  pose proof (Z.div_mod fr 32 ltac:(lia)) as D32.
  pose proof (Z.div_mod (fr + 8 * c) 2 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (fr + 8 * c) 2 ltac:(lia)) as M2.
  pose proof (Z.div_mod (fr + 8 * c) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (fr + 8 * c) 8 ltac:(lia)) as M8.
  split; lia.
Qed.

(* A byte off the six run writes is outside f9_WA. *)
Lemma f9x_out_WA : forall S fr a,
  ~ (a = S + 32 \/ a = S + 34 \/ a = S + 38) ->
  ~ (fr + 256 <= a < fr + 258 \/ fr + 272 <= a < fr + 280 \/ fr + 304 <= a < fr + 312) ->
  LFR.outside (A.Prog.Seg.F9.f9_WA S fr) a.
Proof.
  intros S fr a H1 H2. unfold A.Prog.Seg.F9.f9_WA. cbn [LFR.outside].
  repeat split; try exact I; lia.
Qed.

(* The owned frame (application memory, below the ceiling) against its shadow, the spill area and the shadow band. *)
Lemma f9x_arith : forall fr A ceil : Z,
  4096 <= fr -> fr + 4096 <= ceil -> 0x7fff7f800000 <= ceil <= 0x7fffff800000 ->
  (fr + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) -> fr + 3136 <= A -> ceil < A ->
  (fr + 4096 <= fr / 8 + 0x7fff8000 \/ fr / 8 + 0x7fff8000 + 512 <= fr) /\
  fr / 8 + 0x7fff8000 + 512 <= A /\ 0x7fff8000 <= fr / 8 + 0x7fff8000 /\
  fr / 8 + 0x7fff8000 + 512 <= 0x10007fff8000.
Proof.
  intros fr A ceil H1 H2 H3 H4 H5 H6.
  pose proof (Z.div_mod fr 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound fr 8 ltac:(lia)) as Hm.
  destruct H4 as [H4 | H4].
  - split; [left; lia|]. repeat split; lia.
  - split; [right; lia|]. repeat split; lia.
Qed.

(* No owned static range of the bundle meets the kind-name table. *)
Lemma f9x_kn_unowned : forall a, KNA.KIND_NAME <= a < KNA.KIND_NAME + 112 ->
  ~ Exists (Reusable.YG0n.in_zr a) A.AF0m.Tfib_owned_static.
Proof.
  intros a Ha H. unfold KNA.KIND_NAME in Ha. apply Exists_exists in H as (r & Hr & Hz).
  unfold Reusable.YG0n.in_zr in Hz. unfold A.AF0m.Tfib_owned_static in Hr.
  repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Hz; lia |]). destruct Hr.
Qed.

(* The zero-shadow row search (by a boolean test, never by position). *)
Definition f9x_zrow (lo len : Z) (r : Z * Z) : bool :=
  andb (Z.leb (fst r) lo) (Z.leb (lo + len) (fst r + 8 * (snd r / 8))).

Lemma f9x_find_row : forall (l : list (Z * Z)) lo len r,
  find (f9x_zrow lo len) l = Some r -> In r l /\ fst r <= lo /\ lo + len <= fst r + 8 * (snd r / 8).
Proof.
  intros l lo len r H. apply find_some in H as [Hin Hf]. unfold f9x_zrow in Hf.
  apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. auto.
Qed.

(* A frame cell whose shadow byte (at Sfr fr + k / 8) reads b is addressable for n <= 8 bytes. *)
Lemma f9x_addr_cell : forall (m : word -> option byte) fr k n (b : byte),
  fr mod 32 = 0 -> 0 <= fr -> k mod 8 = 0 -> 0 <= k -> 0 <= n <= 8 ->
  (forall a, fr + k <= a < fr + k + n -> A.AsanRT.app_mem a) -> fr + k + n <= A.AsanRT.APPMEM_END ->
  LMM.mrd A.Img0.rsegs m (LMM.wa (ACtlCutP.Sfr fr + k / 8)) = Some b ->
  (bv_signed b = 0 \/ n <= bv_signed b <= 7) ->
  A.AsanRT.addressable m (fr + k) n.
Proof.
  intros m fr k n b Hm H0 Hk Hk0 Hn Happ Hend E Hv.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply Happ; lia|]. exists b. split.
  - replace (A.AsanRT.shadow_addr (fr + k + i)) with (ACtlCutP.Sfr fr + k / 8); [exact E|].
    unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr. clear - Hm Hk Hk0 H0 Hi Hn. Z.div_mod_to_equations. lia.
  - unfold A.AsanRT.shadow_ok. destruct Hv as [Hv|Hv]; [left; exact Hv | right].
    split; [|lia]. clear - Hm Hk Hk0 H0 Hi Hn Hv. Z.div_mod_to_equations. lia.
Qed.

Section GlueF9.
Context {fx : K11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
  {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81f88_at := (ACtlCutP.C_A81f88_at B).
Local Notation C_A81ff4_at := (ACtlCutP.C_A81ff4_at B).

Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
(* The RECORD AF0m's shadow rows of the five kind-name strings whose first granule is partial.  On the interim
   base lib/A/AF0m.v IS the record file (blob 44930bfd861 (the blob this tree had at release c5e779efe8c) = e56483f863b's, checked by a Theorem Labs lane), so this is PROVED
   here by computation instead of assumed: the five rows are Tfib_const_shadow's entries 19, 23, 35, 42 and 56
   (record AF0m.v:2187, :2191, :2203, :2210, :2224), and Tfib_const ly is Tfib_const_sym ++ Tfib_const_abs ++
   Tfib_const_shadow for every ly.  shadow_addr 0x21220 = 0x7fffc244, 0x21240 = 0x7fffc248, 0x212c0 = 0x7fffc258,
   0x21300 = 0x7fffc260, 0x213a0 = 0x7fffc274. *)
Lemma f9g_rec_kn_shadow : forall ly,
  In (Reusable.YG0f.z1 (Reusable.YG0f.ANum (Reusable.YG0f.shadow_addr 0x21220)) 5) (A.AF0m.Tfib_const ly) /\
  In (Reusable.YG0f.z1 (Reusable.YG0f.ANum (Reusable.YG0f.shadow_addr 0x21240)) 7) (A.AF0m.Tfib_const ly) /\
  In (Reusable.YG0f.z1 (Reusable.YG0f.ANum (Reusable.YG0f.shadow_addr 0x212c0)) 6) (A.AF0m.Tfib_const ly) /\
  In (Reusable.YG0f.z1 (Reusable.YG0f.ANum (Reusable.YG0f.shadow_addr 0x21300)) 7) (A.AF0m.Tfib_const ly) /\
  In (Reusable.YG0f.z1 (Reusable.YG0f.ANum (Reusable.YG0f.shadow_addr 0x213a0)) 6) (A.AF0m.Tfib_const ly).
Proof.
  intros ly. unfold A.AF0m.Tfib_const.
  assert (HI : forall (x : Reusable.YG0f.acell) (n : nat),
            nth_error A.AF0m.Tfib_const_shadow n = Some x ->
            In x (A.AF0m.Tfib_const_sym ++ A.AF0m.Tfib_const_abs ++ A.AF0m.Tfib_const_shadow)).
  { intros x n Hn. apply in_or_app. right. apply in_or_app. right. exact (nth_error_In _ n Hn). }
  repeat split.
  - refine (HI _ 19%nat _); vm_compute; reflexivity.
  - refine (HI _ 23%nat _); vm_compute; reflexivity.
  - refine (HI _ 35%nat _); vm_compute; reflexivity.
  - refine (HI _ 42%nat _); vm_compute; reflexivity.
  - refine (HI _ 56%nat _); vm_compute; reflexivity.
Qed.

(* The callee's spec of record, a Theorem Labs lane's treac_ctrl_identity_reply_spec (lib/A/Prog/C_reac_ctrl_identity_reply.v),
   as ACtl.v's Section hypothesis TREPLY: the same name and text, so the top supplies it. *)
Hypothesis TREPLY : A.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI.

(* The spec's entry (BASE + AF_reac_ctrl_identity_reply over the ctrl PA instance) is the callee's entry address. *)
Lemma f9g_reply_pc :
  A.Prog.C_reac_ctrl_identity_reply.A_reac_ctrl_identity_replyP = A.Prog.reac_ctrl_identity_reply_c.REAC_CTRL_IDENTITY_REPLY.
Proof. vm_compute. reflexivity. Qed.

(* The journal from the function's entry to a memory of this cut's shape. *)
Local Notation J0 cx own ly S W m md k :=
  (Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
     (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) own ly S W m md k).
(* The kind-name string address of the turn (F8's a0, the entry cut's rgv 10). *)
Local Notation f9X cx j := (KNA.kind_name_addr (SM.t_k (ACtlCut.c_in cx) j)).
(* The reply's out cells as tcj_kept's write set. *)
Local Notation f9E cx j phi fr :=
  (fun a => RRP.reply_ok phi (ACtlCutP.flen cx j) (fr + 256) (fr + 272) (fr + 304) (SM.t_g (ACtlCut.c_in cx) j) = true /\
            (fr + 256 <= a < fr + 256 + 2 \/ fr + 272 <= a < fr + 272 + 8 \/ fr + 304 <= a < fr + 304 + 8)).

(* LOCAL (one per stage, a Theorem Labs lane 08:2xZ): the shadow value of a granule whose row in the const table is
   `z1 (ANum (shadow_addr g)) k`, read through the world's VIEW.  The shared A.ProgWorldShadow.ctl_gshadow_of_AR
   (a Theorem Labs lane's ctl_gshadow_of_AR_fixed (written on a working branch 1888d8b45bf), ProgWorldShadow.v (at head lib/A/ProgWorldShadow.v:151-177)) does not
   apply: it concludes `addressable` (an mrd byte), while the run's footprint premise needs the byte VISIBLE, i.e.
   the view value (ProgWorldCtlRt.aview_some_vis).  Same route: AR's am_const at as_const B ly = Tfib_const ly
   (TFIB_SYMS' ts_const), the byte k of the 1-byte row at offset 0.  No image bound: no addressable conclusion. *)
Lemma f9g_kn_gshadow : forall ly S (W : Reusable.YA0n.world segs) (m : word -> option byte) md g k,
  Reusable.YG0n.AR segs B ly S W m md ->
  In (Reusable.YG0f.z1 (Reusable.YG0f.ANum (Reusable.YG0f.shadow_addr g)) k) (A.AF0m.Tfib_const ly) ->
  0 <= k < 256 ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (g / 8 + A.AsanRT.ASAN_K) = Some k.
Proof.
  intros ly S W m md g k HAR Hin Hk.
  destruct HAR as [HARm _].
  assert (Hc : Forall (Reusable.YG0f.cell_holds B ly (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m))
                 (Reusable.YG0f.as_const B ly)) by (destruct HARm; assumption).
  rewrite (A.AF0m.ts_const B TFIB_SYMS ly), Forall_forall in Hc.
  specialize (Hc _ Hin).
  unfold Reusable.YG0f.cell_holds, Reusable.YG0f.z1, Reusable.YG0f.c1 in Hc.
  cbn [Reusable.YG0f.c_at Reusable.YG0f.c_w Reusable.YG0f.c_val Reusable.YG0f.aeval] in Hc.
  specialize (Hc 0%nat ltac:(lia)).
  assert (Hle : Reusable.YG0f.le_byte k 1 0 = k).
  { unfold Reusable.YG0f.le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
    change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
  rewrite Hle in Hc. change (Z.of_nat 0) with 0 in Hc. rewrite Z.add_0_r in Hc.
  replace (g / 8 + A.AsanRT.ASAN_K) with (Reusable.YG0f.shadow_addr g)
    by (unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, A.AsanRT.ASAN_K; ring).
  exact Hc.
Qed.

(* E: every premise of f9g_run at this cut, from the entry body, the journal, ctl_rt and AR. *)
Lemma f9g_entry : forall cx j fr k ly3 S3 W3 regs3 mem3 md3 phi A,
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  J0 cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  ACtlCutP.FRAC B cx fr fr regs3 mem3 -> ACtlCut.rgv regs3 9 A -> 0 <= A < 2 ^ 64 ->
  ACtlCutP.FLSI cx j fr regs3 mem3 -> ACtlCutP.b5_C cx j phi fr regs3 mem3 ->
  LMM.bytes_at segs mem3 (f9X cx j) (RKN.cstr_bytes (RKN.kind_name (SM.t_k (ACtlCut.c_in cx) j))) ->
  A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 ->
  0 <= f9X cx j < 2 ^ 47 /\ 0 <= ACtlCutP.Sfr fr /\ 0 <= fr /\ 0 <= A /\
  fr + ACtlCutP.FRAME_BYTES <= A /\ A + 416 <= 2 ^ 64 /\ ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW <= A /\
  (ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW <= fr \/ fr + ACtlCutP.FRAME_BYTES <= ACtlCutP.Sfr fr) /\
  (exists b, ov_read_bytes A.Img0.rsegs mem3 (LMM.wa (f9X cx j / 8 + A.AsanRT.ASAN_K)) 1 = Some [b] /\
     (bv_signed b = 0 \/ f9X cx j mod 8 < bv_signed b)) /\
  (exists c0, ov_read_bytes A.Img0.rsegs mem3 (LMM.wa (f9X cx j)) 1 = Some [c0] /\ bv_unsigned c0 <> 63) /\
  LMM.wr_at A.Img0.rsegs mem3 (ACtlCutP.Sfr fr) ACtlCutP.FRAME_SHADOW /\
  LMM.wr_at A.Img0.rsegs mem3 (fr + 256) 2 /\ LMM.wr_at A.Img0.rsegs mem3 (fr + 272) 8 /\
  LMM.wr_at A.Img0.rsegs mem3 (fr + 304) 8 /\
  LMM.bytes_at A.Img0.rsegs mem3 (A + 256) (LMM.le8 (Z_to_bv 64 (fr + 256))) /\
  LMM.bytes_at A.Img0.rsegs mem3 (A + 272) (LMM.le8 (Z_to_bv 64 (fr + 272))) /\
  LMM.bytes_at A.Img0.rsegs mem3 (A + 264) (LMM.le8 (Z_to_bv 64 (fr + 304))) /\
  LEX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (f9X cx j / 8 + A.AsanRT.ASAN_K) 1 /\
  LEX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (f9X cx j) 1 /\
  LEX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (ACtlCutP.Sfr fr) ACtlCutP.FRAME_SHADOW /\
  LEX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (fr + 256) 2 /\
  LEX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (fr + 272) 8 /\
  LEX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (fr + 304) 8 /\
  LEX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 256) 8 /\
  LEX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 272) 8 /\
  LEX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 264) 8.
Proof.
  intros cx j fr k ly3 S3 W3 regs3 mem3 md3 phi A HB HJ HF HL HFRAC R9 HAb HFLSI HbC HKN Hrt.
  pose proof (proj1 HJ) as HAR.
  (* the owned class-6 frame (kitmem_own6) and its placement in application memory (the AR frames law) *)
  destruct (A.ACtlG.KitMem.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & Efr3 & Hfr4096 & Hfr32 & Hfrc & Hcsp).
  assert (Hfb6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Hfb6 in Hfrc. unfold A.ACfn.LLVMF_STK in Hcsp.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6) as (_ & Happ & _).
  rewrite Efr3, Hfb6 in Happ.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.ASAN_CEIL, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg
    in Happ.
  destruct (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_value rc) as (Hcv & _).
  assert (Happm : forall a, fr <= a < fr + 4096 -> A.AsanRT.app_mem a).
  { intros a Ha. unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  assert (Hfr8 : fr = 8 * (fr / 8)) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (HSfr : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000) by reflexivity.
  (* FRAC's spill base, and b5_C's three spill cells; both bases are the A of register 9 *)
  pose proof HFRAC as (A0 & sp & _ & _ & _ & _ & _ & R9' & _ & _ & _ & _ & _ & HAS & HspA & HfrA & HA416 & HSlo &
    HSapp & _).
  pose proof HbC as (_ & _ & (A1 & R9'' & HA1 & HSP & _) & _).
  destruct HSP as (_ & Q256 & _ & _ & _ & _ & _ & _ & Q272 & Q264).
  change ACtlCutP.FRAME_BYTES with 3136 in HfrA. unfold A.AsanRT.APPMEM_END in HSapp.
  assert (EA0 : A0 = A).
  { unfold ACtlCut.rgv in R9, R9'. rewrite R9 in R9'. apply (f_equal (bv_unsigned (n:=64))) in R9'.
    rewrite !LMS.unsigned_lit in R9' by lia. lia. }
  assert (EA1 : A1 = A).
  { unfold ACtlCut.rgv in R9, R9''. rewrite R9 in R9''. apply (f_equal (bv_unsigned (n:=64))) in R9''.
    rewrite !LMS.unsigned_lit in R9'' by lia. lia. }
  subst A0 A1.
  (* the kind is 0..13 (ctrlparse_kind_range), so the name address is one of the fourteen table strings *)
  assert (Hv13 : 0 <= SM.t_k (ACtlCut.c_in cx) j <= 13).
  { unfold SM.t_k. apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.ctrlparse_kind_range. }
  assert (HXb : forall v, 0 <= v <= 13 -> 0x21220 <= KNA.kind_name_addr v <= 0x213c0).
  { intros v Hv.
    assert (Hc : v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7 \/ v = 8 \/ v = 9 \/ v = 10 \/
                 v = 11 \/ v = 12 \/ v = 13) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]];
      (lazymatch goal with |- context [KNA.kind_name_addr ?c] =>
         let x := eval vm_compute in (KNA.kind_name_addr c) in change (KNA.kind_name_addr c) with x end);
      lia. }
  (* the shadow value of the name's granule, through the view: a zero-shadow row of Tfib_zero_shadow found by a
     boolean search (TFIB_SYMS' ts_zsh, AR's al_zshadow), or, for a granule no zero row covers, the partial row
     f9g_rec_kn_shadow proves (f9g_kn_gshadow) *)
  assert (HSV : forall v, 0 <= v <= 13 ->
            exists s, Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3
                        (KNA.kind_name_addr v / 8 + A.AsanRT.ASAN_K) = Some s /\
              0 <= s < 8 /\ (s = 0 \/ KNA.kind_name_addr v mod 8 < s)).
  { intros v Hv.
    assert (HP : forall g kk,
               In (Reusable.YG0f.z1 (Reusable.YG0f.ANum (Reusable.YG0f.shadow_addr g)) kk) (A.AF0m.Tfib_const ly3) ->
               0 < kk < 8 -> g mod 8 = 0 ->
               exists s, Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3 (g / 8 + A.AsanRT.ASAN_K) = Some s /\
                 0 <= s < 8 /\ (s = 0 \/ g mod 8 < s)).
    { intros g kk Hr Hk Hg. exists kk.
      split; [exact (f9g_kn_gshadow ly3 S3 W3 mem3 md3 g kk HAR Hr ltac:(lia)) | lia]. }
    destruct (find (fun r => (fst r <=? KNA.kind_name_addr v) && (KNA.kind_name_addr v + 1 <=? fst r + 8 * (snd r / 8)) &&
                             (fst r mod 8 =? 0)) A.AF0m.Tfib_zero_shadow) as [r|] eqn:E.
    - destruct (find_some _ _ E) as (Hin & Hp). cbv beta in Hp.
      apply andb_prop in Hp as (Hp & H3). apply andb_prop in Hp as (H1 & H2).
      apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.eqb_eq in H3.
      assert (Hin' : In r (Reusable.YG0n.zero_shadow_ranges B ly3)).
      { unfold Reusable.YG0n.zero_shadow_ranges. right. rewrite (A.AF0m.ts_zsh B TFIB_SYMS). exact Hin. }
      pose proof (Reusable.YG0d.al_zshadow _ _ LAWS ly3 S3 W3 mem3 md3 r HAR Hin') as Hz.
      unfold Reusable.YG0v.zero_shadow in Hz.
      assert (Hi : 0 <= KNA.kind_name_addr v / 8 - fst r / 8 < snd r / 8)
        by (clear - H1 H2 H3; Z.div_mod_to_equations; lia).
      specialize (Hz _ Hi).
      assert (Ea : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (fst r) + (KNA.kind_name_addr v / 8 - fst r / 8) =
                   KNA.kind_name_addr v / 8 + A.AsanRT.ASAN_K)
        by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, A.AsanRT.ASAN_K; ring).
      rewrite Ea in Hz.
      exists 0. split; [exact Hz | lia].
    - destruct (f9g_rec_kn_shadow ly3) as (R1 & R2 & R3 & R4 & R5).
      assert (Hc : v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7 \/ v = 8 \/ v = 9 \/ v = 10 \/
                   v = 11 \/ v = 12 \/ v = 13) by lia.
      destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]];
        (lazymatch goal with |- context [KNA.kind_name_addr ?c] =>
           let x := eval vm_compute in (KNA.kind_name_addr c) in change (KNA.kind_name_addr c) with x in E |- * end);
        first [ (vm_compute in E; discriminate E)
              | exact (HP _ _ R1 ltac:(lia) eq_refl) | exact (HP _ _ R2 ltac:(lia) eq_refl)
              | exact (HP _ _ R3 ltac:(lia) eq_refl) | exact (HP _ _ R4 ltac:(lia) eq_refl)
              | exact (HP _ _ R5 ltac:(lia) eq_refl) ]. }
  destruct (HSV _ Hv13) as (s & Hs & Hs8 & Hsd).
  pose proof (HXb _ Hv13) as HX.
  set (X := KNA.kind_name_addr (SM.t_k (ACtlCut.c_in cx) j)) in *.
  (* the shadow byte as a 1-byte read, and its visibility *)
  pose proof (A.ProgWorldCtlRt.mrd_of_aview W3 mem3 _ _ Hs) as Hmrd.
  pose proof (A.ProgWorldCtlRt.aview_some_vis W3 mem3 _ _ Hs) as Hvis.
  assert (HX8 : 0 <= X / 8 <= X) by (clear - HX; Z.div_mod_to_equations; lia).
  assert (Hb1 : LMM.bytes_at A.Img0.rsegs mem3 (X / 8 + A.AsanRT.ASAN_K) [Z_to_bv 8 s]).
  { unfold LMM.bytes_at. split; [unfold A.AsanRT.ASAN_K; lia|]. split; [cbn [length]; unfold A.AsanRT.ASAN_K; lia|].
    intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
    cbn [nth_error]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact Hmrd. }
  pose proof (LMM.bytes_at_ov_read A.Img0.rsegs mem3 _ _ 0 1 Hb1 ltac:(cbn [length]; lia)) as Hov.
  cbn [firstn skipn] in Hov. change (Z.of_nat 0) with 0 in Hov. rewrite Z.add_0_r in Hov.
  assert (Hsig : bv_signed (Z_to_bv 8 s) = s).
  { assert (Hu : bv_unsigned (Z_to_bv 8 s) = s)
      by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 8) with 256; lia).
    rewrite (A.ProgWorldShadow.pwsh_byte_signed_small (Z_to_bv 8 s) ltac:(lia)). exact Hu. }
  (* the first name byte (l9_name0: not '?') *)
  assert (Hlen : (0 + 1 <= length (RKN.cstr_bytes (RKN.kind_name (SM.t_k (ACtlCut.c_in cx) j))))%nat).
  { unfold RKN.cstr_bytes. rewrite length_app. cbn [length]. lia. }
  pose proof (LMM.bytes_at_ov_read A.Img0.rsegs mem3 _ _ 0 1 HKN Hlen) as Hrd.
  destruct (A.Prog.Seg.F9.l9_name0 _ Hv13) as (c & Hc1 & Hc2).
  rewrite Hc1 in Hrd. change (Z.of_nat 0) with 0 in Hrd. rewrite Z.add_0_r in Hrd.
  (* the frame's presence (FLSI's FLSH) and the shadow's writability (ctl_rt_C's (F) region: the owned class-6
     frame's shadow) *)
  destruct HFLSI as ((_ & _ & Hstk & _) & _).
  destruct Hstk as (_ & _ & Hstk).
  change ACtlCutP.FRAME_BYTES with 3136 in Hstk.
  destruct Hrt as (_ & Hcut & _ & _).
  assert (Hfb68 : Reusable.YG00.fs_frame_bytes 6 / 8 = 512) by reflexivity.
  change ACtlCutP.FRAME_SHADOW with 392. change ACtlCutP.FRAME_BYTES with 3136.
  split; [lia|].
  split; [rewrite HSfr; lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [rewrite HSfr; lia|].
  split.
  { rewrite HSfr. destruct Happ as (_ & [Hlo | (Hhi & _)]); [right | left]; lia. }
  split.
  { exists (Z_to_bv 8 s). split; [exact Hov | rewrite Hsig; exact Hsd]. }
  split.
  { exists c. split; [exact Hrd | exact Hc2]. }
  split.
  { unfold LMM.wr_at. split; [rewrite HSfr; lia|]. split; [rewrite HSfr; lia|].
    intros i Hi.
    assert (Hsh : A.AsanRT.in_shadow (ACtlCutP.Sfr fr + i)).
    { replace (ACtlCutP.Sfr fr + i) with (A.AsanRT.shadow_addr (fr + 8 * i)).
      - apply A.AsanRTFacts.shadow_of_app. apply Happm. lia.
      - unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr. rewrite (Z.mul_comm 8 i), Z.div_add by lia. ring. }
    (* Sfr fr + i is the shadow of the frame byte fr + 8 i, inside the owned frame [fr, fr + 4096) *)
    assert (HF6 : A.ACtlRtC.cut_shadow B ly3 S3 (ACtlCutP.Sfr fr + i)).
    { left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
      rewrite Hfb68, Efr3, HSfr. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia. }
    exact (proj1 (Hcut _ HF6 Hsh)). }
  split.
  { unfold LMM.wr_at. split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (Hstk (fr + 256 + i) ltac:(lia))). }
  split.
  { unfold LMM.wr_at. split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (Hstk (fr + 272 + i) ltac:(lia))). }
  split.
  { unfold LMM.wr_at. split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (Hstk (fr + 304 + i) ltac:(lia))). }
  split; [exact Q256|].
  split; [exact Q272|].
  split; [exact Q264|].
  split.
  { apply A.ProgBridge.rng_of_visible. unfold A.ProgBridge.range_visible.
    split; [unfold A.AsanRT.ASAN_K; lia|]. split; [unfold A.AsanRT.ASAN_K; lia|].
    intros a Ha. replace a with (X / 8 + A.AsanRT.ASAN_K) by lia. exact Hvis. }
  split.
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ (A.ProgBridge.img_vis_W W3));
      unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.IMG_LO,
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.IMG_HI; lia. }
  split.
  { apply (A.ACtlG.KitMem.kitmem_rng_frame_sh B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx));
      [exact HAR | exact Hin6 | rewrite Efr3; unfold ACtlCutP.Sfr; lia
      | rewrite Efr3, Hfb6; unfold ACtlCutP.Sfr; change (4096 / 8) with 512; lia]. }
  split.
  { apply (A.ACtlG.KitMem.kitmem_rng_frame B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx));
      [exact HAR | exact Hin6 | rewrite Efr3; lia | rewrite Efr3, Hfb6; lia]. }
  split.
  { apply (A.ACtlG.KitMem.kitmem_rng_frame B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx));
      [exact HAR | exact Hin6 | rewrite Efr3; lia | rewrite Efr3, Hfb6; lia]. }
  split.
  { apply (A.ACtlG.KitMem.kitmem_rng_frame B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx));
      [exact HAR | exact Hin6 | rewrite Efr3; lia | rewrite Efr3, Hfb6; lia]. }
  split.
  { eapply A.ACtlG.KitMem.kitmem_rng_win; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
  split.
  { eapply A.ACtlG.KitMem.kitmem_rng_win; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
  eapply A.ACtlG.KitMem.kitmem_rng_win; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia].
Qed.

(* The run's six writes are bytes of the owned class-6 frame or of its shadow (awr_byte's frame case). *)
Lemma f9g_awr : forall cx fr k ly3 S3 W3 mem3 md3,
  J0 cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ LFR.outside (A.Prog.Seg.F9.f9_WA (ACtlCutP.Sfr fr) fr) a ->
  Reusable.YCbq.awr_byte A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
    (ACtlCut.own6 cx) a.
Proof.
  intros cx fr k ly3 S3 W3 mem3 md3 HJ HF HL a Ha Hno.
  destruct (A.ACtlG.KitMem.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL) as (_ & Efr3 & _).
  assert (Hfb6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  apply (A.ACtlG.KitMem.kitmem_awr_frame _ _ _ _ _ ly3 (ACtlCut.own6 cx) 6 (ACtlCut.c_fpos cx) fr a (eq_sym Efr3)
           ltac:(left; reflexivity)).
  rewrite Hfb6. change (4096 / 8) with 512.
  destruct (A.ACtlG.KitMem.kitmem_not_outside _ _ Hno) as (lo & hi & Hin & Hlh).
  unfold A.Prog.Seg.F9.f9_WA, ACtlCutP.Sfr in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-; [right|left|right|left|right|left]; lia.
Qed.

(* C1: the reply spec's message premise at the call state (memory m1, after the six stores). *)
Lemma f9g_msg : forall cx j fr k ly3 S3 W3 regs3 mem3 md3 m1 md1 phi A,
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  J0 cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k -> J0 cx (ACtlCut.own6 cx) ly3 S3 W3 m1 md1 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  ACtlCutP.FRAC B cx fr fr regs3 mem3 -> ACtlCut.rgv regs3 9 A -> 0 <= A < 2 ^ 64 ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3)
    (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx) ++ [(phi, ACtlCutP.flen cx j)]) ->
  ACtlCutP.b5_C cx j phi fr regs3 mem3 ->
  LFR.munch (A.Prog.Seg.F9.f9_WA (ACtlCutP.Sfr fr) fr) mem3 m1 ->
  RRP.reply_args phi (fr + 256) (fr + 272) (fr + 304) = true -> 50 <= ACtlCutP.flen cx j ->
  (exists nb, In (phi, nb) (Reusable.YG0d.ablocks B ly3 S3) /\ 50 <= Reusable.YG00.req_size nb) /\
  A.Prog.CtrlCallerJ.tsrc_ok (PI := A.Prog.CtrlImg.PI_ctrl) W3 m1 (Reusable.YG0d.spZ regs3) phi 50 /\
  CI00.garr8 segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W3) m1) phi
    (map bv_unsigned (SM.t_g (ACtlCut.c_in cx) j)).
Proof.
  intros cx j fr k ly3 S3 W3 regs3 mem3 md3 m1 md1 phi A HB HJ HJ1 HF HL HFRAC R9 HA64 HPerm HbC MU Hargs H50.
  pose proof HFRAC as (A' & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9' & R3 & R19 & R26 & Hf32 & HA32 & HAS & HspA &
    HfrA & HA416 & HSlo & HSapp & _).
  destruct (A.ACtlG.KitMem.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & Efr3 & Hfr4096 & Hfr32 & Hfrc & Hcsp).
  assert (Hinphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  (* the AR laws at the call state m1 (the journal across the run, HJ1) *)
  pose proof (proj1 HJ1) as HAR1.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 m1 md1 _ _ HAR1 Hinphi)
    as (_ & Hphi4096 & Hphic & Happ & Hpres & _ & Hlen).
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 m1 md1 _ _ HAR1 Hinphi) as [Hbs Hhull].
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 m1 md1 _ _ 6 (ACtlCut.c_fpos cx) HAR1 Hinphi Hin6)
    as Hsep.
  unfold Reusable.YG0f.zdisjoint in Hsep; cbn [fst snd] in Hsep. rewrite Efr3 in Hsep.
  pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx j) (proj1 Hlen)) as Hreq.
  pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_lt rc) as Hcl.
  assert (Hfb6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Hfb6 in Hsep, Hfrc.
  unfold A.ACfn.LLVMF_STK in Hcsp.
  set (rs := Reusable.YG00.req_size (ACtlCutP.flen cx j)) in *.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Happ.
  assert (Hvis : forall a, phi <= a < phi + 50 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\
            exists b, m1 (Z_to_bv 64 a) = Some b).
  { intros a Ha. exact (proj1 (Hpres a ltac:(lia))). }
  split; [exists (ACtlCutP.flen cx j); split; [exact Hinphi | lia]|].
  split.
  - (* tsrc_ok at the 50 record bytes *)
    assert (T1 : forall a, phi <= a < phi + 50 ->
              Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m1 a <> None /\
              ~ (Reusable.YG0d.spZ regs3 - Reusable.YG0d.ESTACK <= a < Reusable.YG0d.spZ regs3)).
    { intros a Ha. split.
      - destruct (Hvis a Ha) as [Hh (b & Hb)].
        rewrite (A.ProgWorld.aview_vis_mrd W3 m1 a Hh). unfold LMM.mrd. rewrite Hb. cbn [option_map]. discriminate.
      - unfold Reusable.YG0d.ESTACK. rewrite HspZ. lia. }
    assert (T2 : Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m1)
                   Reusable.YG0f.SHADOW_OFF phi 50)
      by exact (Reusable.YG0v.block_shadow_range _ _ phi rs phi 50 Hbs ltac:(lia) ltac:(lia)).
    assert (T3 : Reusable.YG0d.shadow_hull_vis (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m1) phi 50).
    { unfold Reusable.YG0d.shadow_hull_vis in Hhull |- *. intros s Hs. apply Hhull.
      assert (Hm : Reusable.YG0f.shadow_addr (phi + 50 - 1) / 8 <= Reusable.YG0f.shadow_addr (phi + rs - 1) / 8).
      { apply Z.div_le_mono; [lia|]. unfold Reusable.YG0f.shadow_addr. apply Z.add_le_mono_l.
        apply Z.div_le_mono; lia. }
      lia. }
    assert (T4 : Reusable.YG0d.amem_range phi 50).
    { unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg,
        Reusable.YG0f.kHighMemEnd. lia. }
    unfold A.Prog.CtrlCallerJ.tsrc_ok.
    split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4|]. split; lia.
  - (* the record bytes at m1, then garr8 over the restricted m1 *)
    destruct HbC as (_ & _ & _ & (HPH & _) & _).
    pose proof (HPH H50) as Hg.
    assert (Hlg : length (SM.t_g (ACtlCut.c_in cx) j) = 50%nat) by (unfold SM.t_g; apply SM.fr50_length).
    assert (HSr : 0x7fff8000 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 512 <= 0x10007fff8000).
    { unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
      pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)) as D0.
      assert (D1 : fr / 8 < 2 ^ 44 - 512) by (apply Z.div_lt_upper_bound; lia).
      lia. }
    assert (Hg1 : LMM.bytes_at A.Img0.rsegs m1 phi (SM.t_g (ACtlCut.c_in cx) j)).
    { apply (A.ACtlG.KitMem.kitmem_bytes_munch _ mem3 m1 phi _ Hg MU).
      rewrite Hlg. intros x Hx. change (Z.of_nat 50) with 50 in Hx.
      unfold A.Prog.Seg.F9.f9_WA. cbn [LFR.outside].
      repeat split; lia. }
    apply (f9g_garr8_bytes W3 m1 phi _ Hg1).
    rewrite Hlg. intros i Hi. change (Z.of_nat 50) with 50 in Hi. exact (proj1 (Hvis (phi + i) ltac:(lia))).
Qed.

(* C2: the reply spec's out-cell premise at the call state. *)
Lemma f9g_cells : forall cx fr k ly3 S3 W3 regs3 mem3 md3 m1 md1 (phi A : Z),
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  J0 cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k -> J0 cx (ACtlCut.own6 cx) ly3 S3 W3 m1 md1 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  ACtlCutP.FRAC B cx fr fr regs3 mem3 -> ACtlCut.rgv regs3 9 A -> 0 <= A < 2 ^ 64 ->
  LFR.munch (A.Prog.Seg.F9.f9_WA (ACtlCutP.Sfr fr) fr) mem3 m1 ->
  LMM.bytes_at A.Img0.rsegs m1 (ACtlCutP.Sfr fr + 32) (LMM.le1 (Z_to_bv 64 2)) ->
  LMM.bytes_at A.Img0.rsegs m1 (ACtlCutP.Sfr fr + 34) (LMM.le1 (Z_to_bv 64 0)) ->
  LMM.bytes_at A.Img0.rsegs m1 (ACtlCutP.Sfr fr + 38) (LMM.le1 (Z_to_bv 64 0)) ->
  LMM.bytes_at A.Img0.rsegs m1 (fr + 256) (LMM.le2 (Z_to_bv 64 0)) ->
  LMM.bytes_at A.Img0.rsegs m1 (fr + 272) (LMM.le8 (Z_to_bv 64 0)) ->
  LMM.bytes_at A.Img0.rsegs m1 (fr + 304) (LMM.le8 (Z_to_bv 64 0)) ->
  RRP.reply_args phi (fr + 256) (fr + 272) (fr + 304) = true ->
  (fr + 256) mod 2 = 0 /\ (fr + 272) mod 8 = 0 /\ (fr + 304) mod 8 = 0 /\
  (fr + 256 + 2 <= fr + 272 \/ fr + 272 + 8 <= fr + 256) /\ (fr + 256 + 2 <= fr + 304 \/ fr + 304 + 8 <= fr + 256) /\
  (fr + 272 + 8 <= fr + 304 \/ fr + 304 + 8 <= fr + 272) /\
  (forall a, (fr + 256 <= a < fr + 256 + 2 \/ fr + 272 <= a < fr + 272 + 8 \/ fr + 304 <= a < fr + 304 + 8) ->
     exists cid pos, In (cid, pos) (Reusable.YG01.frames S3) /\
       Reusable.YG0n.in_zr a (Reusable.YCbq.frame_rng ly3 (cid, pos))) /\
  A.Prog.CtrlCallerJ.twr_ok (PI := A.Prog.CtrlImg.PI_ctrl) B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) ly3 S3 (ACtlCut.own6 cx) W3 m1 (Reusable.YG0d.spZ regs3) (fr + 256) 2 /\
  A.Prog.CtrlCallerJ.twr_ok (PI := A.Prog.CtrlImg.PI_ctrl) B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) ly3 S3 (ACtlCut.own6 cx) W3 m1 (Reusable.YG0d.spZ regs3) (fr + 272) 8 /\
  A.Prog.CtrlCallerJ.twr_ok (PI := A.Prog.CtrlImg.PI_ctrl) B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) ly3 S3 (ACtlCut.own6 cx) W3 m1 (Reusable.YG0d.spZ regs3) (fr + 304) 8 /\
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m1)
    Reusable.YG0f.SHADOW_OFF (fr + 256) 2 /\
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m1)
    Reusable.YG0f.SHADOW_OFF (fr + 272) 8 /\
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m1)
    Reusable.YG0f.SHADOW_OFF (fr + 304) 8.
Proof.
  intros cx fr k ly3 S3 W3 regs3 mem3 md3 m1 md1 phi A HB HJ HJ1 HF HL HFRAC R9 HA64 MU B32 B34 B38 Ba Bp Bn Hargs.
  pose proof HFRAC as (A' & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9' & R3 & R19 & R26 & Hf32 & HA32 & HAS & HspA &
    HfrA & HA416 & HSlo & HSapp & _).
  destruct (A.ACtlG.KitMem.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & Efr3 & Hfr4096 & Hfr32 & Hfrc & Hcsp).
  (* the AR frames law at the call state m1 (the journal across the run, HJ1) *)
  pose proof (proj1 HJ1) as HAR1.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 m1 md1 6 (ACtlCut.c_fpos cx) HAR1 Hin6)
    as (_ & _ & Hfb & Hfsh).
  rewrite Efr3 in Hfb, Hfsh.
  assert (Hfb6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Hfb6 in Hfb, Hfsh, Hfrc. change (4096 / 8) with 512 in Hfsh.
  pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_lt rc) as Hcl.
  unfold A.ACfn.LLVMF_STK in Hcsp.
  (* an owned-frame range off the callee's stack window is a range the call may write *)
  assert (HW : forall q n, fr <= q -> q + n <= fr + 4096 ->
     A.Prog.CtrlCallerJ.twr_ok (PI := A.Prog.CtrlImg.PI_ctrl) B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
       (ACtlCut.c_ly cx) (ACtlCut.c_S cx) ly3 S3 (ACtlCut.own6 cx) W3 m1 (Reusable.YG0d.spZ regs3) q n).
  { intros q n Hq1 Hq2 a Ha.
    destruct (Hfb a ltac:(lia)) as [Hp Hno].
    split; [|split; [exact Hp|split; [exact Hno|]]].
    - apply (A.ACtlG.KitMem.kitmem_awr_frame _ _ _ _ _ _ _ 6 (ACtlCut.c_fpos cx) fr a (eq_sym Efr3));
        [unfold ACtlCut.own6; left; reflexivity | left; rewrite Hfb6; lia].
    - unfold Reusable.YG0d.ESTACK. rewrite HspZ. lia. }
  (* the three shadow bytes the run wrote are visible and read their values *)
  assert (Hshv : forall c v, 0 <= c < 512 -> (v = 0 \/ v = 2) ->
            LMM.bytes_at A.Img0.rsegs m1 (ACtlCutP.Sfr fr + c) (LMM.le1 (Z_to_bv 64 v)) ->
            Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m1 (ACtlCutP.Sfr fr + c) = Some v).
  { intros c v Hc Hv (_ & _ & Hb).
    assert (ES : ACtlCutP.Sfr fr + c = Reusable.YG0f.shadow_addr fr + c)
      by (unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
            Reusable.YG0f.SHADOW_OFF; lia).
    destruct (Hfsh c Hc) as [[Hh _] _]. rewrite <- ES in Hh.
    rewrite (A.ProgWorld.aview_vis_mrd W3 m1 _ Hh).
    pose proof (Hb 0%nat ltac:(rewrite LMM.length_le1; lia)) as Hb0.
    cbn [Z.of_nat] in Hb0. rewrite Z.add_0_r in Hb0. unfold LMM.wa in Hb0. rewrite Hb0.
    destruct Hv as [-> | ->]; vm_compute; reflexivity. }
  (* a cell fr + 8 c of n <= 8 bytes is addressable from its one shadow byte Sfr fr + c *)
  assert (RA : forall q c v n, q = fr + 8 * c -> 0 <= c < 512 -> 0 < n <= 8 -> (v = 0 \/ v = 2) ->
            (v = 0 \/ n <= v) ->
            LMM.bytes_at A.Img0.rsegs m1 (ACtlCutP.Sfr fr + c) (LMM.le1 (Z_to_bv 64 v)) ->
            Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m1)
              Reusable.YG0f.SHADOW_OFF q n).
  { intros q c v n -> Hc Hn Hv Hvn Hb x Hx.
    destruct (f9g_cell_div fr c (x - (fr + 8 * c)) Hf32 ltac:(lia)) as [Ed Em].
    replace (fr + 8 * c + (x - (fr + 8 * c))) with x in Ed, Em by ring.
    exists v. split.
    - replace (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x) with (ACtlCutP.Sfr fr + c)
        by (unfold Reusable.YG0v.shadow_of_addr, ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K,
              Reusable.YG0f.SHADOW_OFF; rewrite Ed; lia).
      exact (Hshv c v Hc Hv Hb).
    - unfold Reusable.YG0v.saddr_ok. destruct Hvn as [-> | Hvn]; [left; reflexivity|].
      right. rewrite Em. destruct Hv as [-> | ->]; lia. }
  destruct (f9g_cell_mod fr 32 Hf32) as [M256 _].
  destruct (f9g_cell_mod fr 34 Hf32) as [_ M272].
  destruct (f9g_cell_mod fr 38 Hf32) as [_ M304].
  split; [replace (fr + 256) with (fr + 8 * 32) by lia; exact M256|].
  split; [replace (fr + 272) with (fr + 8 * 34) by lia; exact M272|].
  split; [replace (fr + 304) with (fr + 8 * 38) by lia; exact M304|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split.
  { intros a Ha. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
    unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite Efr3, Hfb6. lia. }
  split; [apply HW; lia|]. split; [apply HW; lia|]. split; [apply HW; lia|].
  split; [exact (RA (fr + 256) 32 2 2 ltac:(lia) ltac:(lia) ltac:(lia) (or_intror eq_refl) (or_intror (Z.le_refl 2)) B32)|].
  split; [exact (RA (fr + 272) 34 0 8 ltac:(lia) ltac:(lia) ltac:(lia) (or_introl eq_refl) (or_introl eq_refl) B34)|].
  exact (RA (fr + 304) 38 0 8 ltac:(lia) ltac:(lia) ltac:(lia) (or_introl eq_refl) (or_introl eq_refl) B38).
Qed.

(* T2: FRAC moves along a byte agreement on f9_K and a map that keeps the callee-saved registers; the frame
   shadow window (three of whose bytes phase A rewrites) is given at m'.  Written by FRAC's SHAPE, so the
   announced trailer conjunct q64 m (fr + 4088) .. (inside the frame, in f9_K) is one more q64 step. *)
Lemma f9g_frac_keep : forall cx j fr A phi (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  f9_rkeep (f9_K cx j fr A phi) m m' ->
  Reusable.YG0d.aregs_preserved regs regs' ->
  ACtlCutP.FRAC B cx fr fr regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= A.AsanRT.APPMEM_END ->
  (exists sh, LMM.bytes_at segs m' (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  ACtlCutP.FRAC B cx fr fr regs' m'.
Proof.
  intros cx j fr A phi regs regs' m m' HK HP HFR R9 HA0 HA Hsh.
  pose proof (A.ACtlG.KitMem.kitmem_saved_len cx) as Hlen.
  assert (E2 : K11.getr regs' 2 = K11.getr regs 2) by exact (HP 2 ltac:(f9t_cs)).
  assert (E3 : K11.getr regs' 3 = K11.getr regs 3) by exact (HP 3 ltac:(f9t_cs)).
  assert (E4 : K11.getr regs' 4 = K11.getr regs 4) by exact (HP 4 ltac:(f9t_cs)).
  assert (E8 : K11.getr regs' 8 = K11.getr regs 8) by exact (HP 8 ltac:(f9t_cs)).
  assert (E9 : K11.getr regs' 9 = K11.getr regs 9) by exact (HP 9 ltac:(f9t_cs)).
  assert (E19 : K11.getr regs' 19 = K11.getr regs 19) by exact (HP 19 ltac:(f9t_cs)).
  assert (E26 : K11.getr regs' 26 = K11.getr regs 26) by exact (HP 26 ltac:(f9t_cs)).
  destruct HFR as (A1 & sp & HFR). exists A1, sp.
  repeat match type of HFR with _ /\ _ => let H1 := fresh "HF" in destruct HFR as [H1 HFR] end.
  (* FRAC's own spill base is A: both are register 9, both in [0, 2^64) *)
  assert (EA : A1 = A).
  { match goal with H9 : ACtlCut.rgv regs 9 A1 |- _ => apply (f9t_rgv_eq regs 9 A1 A H9 R9) end;
      [| unfold A.AsanRT.APPMEM_END in HA; lia].
    match goal with Hq : ACtlCutP.q64 m fr _ |- _ => pose proof (proj1 Hq) as Hfr0 end.
    unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in *. lia. }
  subst A1.
  (* the registers FRAC reads are callee-saved: the goal reads regs where it read regs' *)
  unfold ACtlCut.rgv, Reusable.YG0d.spZ in *.
  rewrite ?E2, ?E3, ?E4, ?E8, ?E9, ?E19, ?E26.
  (* split FRAC's own /\ only (syntactically), then one step per conjunct by its shape *)
  repeat (match goal with |- _ /\ _ => split end);
    first
    [ assumption
    | lazymatch goal with
      | |- ACtlCutP.q64 m' ?a ?v =>
          match goal with Hq : ACtlCutP.q64 m a v |- _ =>
            apply (f9t_q64 _ m m' a v HK Hq); intros ? ?;
            first [ apply f9t_K_A; lia | apply f9t_K_fr; lia | apply f9t_K_sv; lia ] end
      | |- LMM.bytes_at _ m' ?a ?bs =>
          match goal with Hb : LMM.bytes_at _ m a bs |- _ =>
            apply (f9t_bytes _ m m' a bs HK Hb); intros ? ?; rewrite ?Hlen in *;
            first [ apply f9t_K_A; lia | apply f9t_K_fr; lia | apply f9t_K_sv; lia ] end
      end ].
Qed.

(* At an address visible in W, a byte m reads is a byte m' reads when the two views agree. *)
Lemma f9x_mrd_view : forall (W W' : Reusable.YA0n.world segs) (m m' : word -> option byte) (a : Z) (b : byte),
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W') m' a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m a ->
  LMM.mrd A.Img0.rsegs m (LMM.wa a) = Some b -> LMM.mrd A.Img0.rsegs m' (LMM.wa a) = Some b.
Proof.
  intros W W' m m' a b Hh E Hb.
  pose proof (A.ProgWorld.aview_vis_mrd W m a Hh) as Hv.
  unfold LMM.wa in Hb. rewrite Hb in Hv. cbn [option_map] in Hv.
  rewrite Hv in E.
  pose proof (A.ProgWorldCtlRt.mrd_of_aview W' m' a _ E) as H'.
  rewrite Z_to_bv_bv_unsigned in H'. exact H'.
Qed.

(* Two views with the same value at a: the byte m reads there is the byte m' reads. *)
Lemma f9x_mrd_same : forall (W W' : Reusable.YA0n.world segs) (m m' : word -> option byte) (a v : Z) (b : byte),
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m a = Some v ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W') m' a = Some v ->
  LMM.mrd A.Img0.rsegs m (LMM.wa a) = Some b -> LMM.mrd A.Img0.rsegs m' (LMM.wa a) = Some b.
Proof.
  intros W W' m m' a v b H1 H2 Hb.
  rewrite (A.ProgWorldCtlRt.mrd_of_aview W m a v H1) in Hb.
  rewrite (A.ProgWorldCtlRt.mrd_of_aview W' m' a v H2). exact Hb.
Qed.

(* The same over a range on which both views are pinned to one function of the offset. *)
Lemma f9x_view_both : forall (W W' : Reusable.YA0n.world segs) (m m' : word -> option byte) (base a n : Z)
    (f : Z -> Z) (b : byte),
  (forall i, 0 <= i < n -> Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (base + i) = Some (f i)) ->
  (forall i, 0 <= i < n -> Reusable.YG0n.aview segs (Reusable.YA0n.w_H W') m' (base + i) = Some (f i)) ->
  base <= a < base + n ->
  LMM.mrd A.Img0.rsegs m (LMM.wa a) = Some b -> LMM.mrd A.Img0.rsegs m' (LMM.wa a) = Some b.
Proof.
  intros W W' m m' base a n f b H1 H2 Ha Hb.
  pose proof (H1 (a - base) ltac:(lia)) as E1. pose proof (H2 (a - base) ltac:(lia)) as E2.
  replace (base + (a - base)) with a in E1, E2 by ring.
  exact (f9x_mrd_same W W' m m' a (f (a - base)) b E1 E2 Hb).
Qed.

Lemma f9x_mrd_of_view : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (x : Z) (c : byte),
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m x = Some (bv_unsigned c) ->
  LMM.mrd A.Img0.rsegs m (LMM.wa x) = Some c.
Proof.
  intros W m x c H. pose proof (A.ProgWorldCtlRt.mrd_of_aview W m x _ H) as E.
  rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.

(* One CB cell from its bytes in the view and the presence of its bytes. *)
Lemma f9x_rw_cb : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (a : Z) (n : nat) (bs : list byte),
  length bs = n -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + Z.of_nat i) =
     option_map (fun c : byte => bv_unsigned c) (nth_error bs i)) ->
  (forall i, 0 <= i < Z.of_nat n -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) m (a + i)) ->
  ACtlCutP.STP.rw_cells segs m a [ACtlCutP.CEL.CB n bs].
Proof.
  intros W m a n bs Hlen H0 H1 Hv Hp. split.
  - split; [cbn [ACtlCutP.CEL.cells_wf ACtlCutP.CEL.cell_wf]; split; [exact Hlen | exact I]|].
    cbn [ACtlCutP.CEL.cells_bytes ACtlCutP.CEL.cbytes]. rewrite app_nil_r.
    split; [exact H0|]. split; [rewrite Hlen; exact H1|].
    intros i Hi. rewrite Hlen in Hi.
    destruct (nth_error bs i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    pose proof (Hv i Hi) as E. rewrite Ec in E. cbn [option_map] in E.
    exact (f9x_mrd_of_view W m _ c E).
  - cbn [ACtlCutP.CEL.cells_size ACtlCutP.CEL.csize]. rewrite Nat.add_0_r.
    split; [exact H0|]. split; [exact H1|].
    intros i Hi. destruct (Hp i Hi) as [_ (c & Hc)]. exact (A.ACtlG.KitMem.kitmem_wview_some m _ c Hc).
Qed.

(* A val_mem word of the restricted memory is a CB 8 cell of its le8 bytes. *)
Lemma f9x_rw_le8 : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (a v : Z),
  I04.val_mem segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) m) a 8 v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) m (a + i)) ->
  ACtlCutP.STP.rw_cells segs m a [ACtlCutP.CEL.CB 8 (LMM.le8 (Z_to_bv 64 v))].
Proof.
  intros W m a v Hv H0 H1 Hp. apply (f9x_rw_cb W m a 8 _ (LMM.length_le8 _) H0 H1); [|exact Hp].
  intros i Hi. unfold Reusable.YG0n.aview. rewrite (Hv i Hi).
  change (LMM.le8 (Z_to_bv 64 v)) with (LMM.le8 (LMM.wa v)).
  rewrite (A.ProgWorldCtlRt.le8_eq v v eq_refl), (A.ProgWorldCtlRt.nth_Z_to_le_bytes 8 v i Hi).
  cbn [option_map]. do 2 f_equal. exact (A.ProgWorldCtlRt.le_byte_shiftr v 8 i Hi).
Qed.

(* A garr8 pair of the restricted memory is a CB 2 cell of those bytes. *)
Lemma f9x_rw_g2 : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (a : Z) (x y : byte),
  CI00.garr8 segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) m) a (map bv_unsigned [x; y]) ->
  0 <= a -> a + 2 <= 2 ^ 64 ->
  (forall i, 0 <= i < 2 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) m (a + i)) ->
  ACtlCutP.STP.rw_cells segs m a [ACtlCutP.CEL.CB 2 [x; y]].
Proof.
  intros W m a x y Hg H0 H1 Hp. apply (f9x_rw_cb W m a 2 [x; y] eq_refl H0 H1); [|exact Hp].
  intros i Hi.
  pose proof (CI00.garr8_mbyte segs _ a _ i Hg ltac:(cbn [length map]; lia)) as E.
  (* garr8's byte reader and the view's are the same definition under two module paths: by conversion *)
  assert (E2 : Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + Z.of_nat i) =
               option_map (fun c : byte => bv_unsigned c) (Some (Z_to_bv 8 (nth i (map bv_unsigned [x; y]) 0)))).
  { unfold Reusable.YG0n.aview. f_equal. exact E. }
  rewrite E2.
  destruct i as [|[|i]]; [| | lia]; cbn [option_map nth map nth_error]; rewrite Z_to_bv_bv_unsigned; reflexivity.
Qed.

(* X: the exit body C_A81ff4_at (ACtlCutP.v:2150-2162) at the callee's return state. *)
Lemma f9g_exit_body : forall cx j fr k ly3 S3 W3 regs3 mem3 md3 m1 md1 phi A ly2 S2 W2 regs2 mem2 md2,
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  J0 cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k -> J0 cx (ACtlCut.own6 cx) ly3 S3 W3 m1 md1 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  ACtlCutP.FRAC B cx fr fr regs3 mem3 -> ACtlCut.rgv regs3 9 A -> 0 <= A < 2 ^ 64 ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3)
    (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx) ++ [(phi, ACtlCutP.flen cx j)]) ->
  ACtlCut.c_n cx < 2 ^ 26 -> (j <= 255)%nat -> ACtlCutP.HB mem3 phi (ACtlCutP.flen cx j) ->
  ACtlCutP.FLSI cx j fr regs3 mem3 -> ACtlCutP.LK cx fr j regs3 mem3 -> ACtlCutP.b5_C cx j phi fr regs3 mem3 ->
  ACtlCutP.b5_K cx j phi fr regs3 mem3 -> ACtlCutP.IDj cx fr j mem3 -> ACtlCutP.b5_F17 cx j phi fr regs3 mem3 ->
  ACtlCutP.b5_W240 cx j regs3 mem3 -> ACtlCutP.b5_PF cx j phi fr regs3 mem3 ->
  LFR.munch (A.Prog.Seg.F9.f9_WA (ACtlCutP.Sfr fr) fr) mem3 m1 ->
  LMM.bytes_at A.Img0.rsegs m1 (ACtlCutP.Sfr fr + 32) (LMM.le1 (Z_to_bv 64 2)) ->
  LMM.bytes_at A.Img0.rsegs m1 (ACtlCutP.Sfr fr + 34) (LMM.le1 (Z_to_bv 64 0)) ->
  LMM.bytes_at A.Img0.rsegs m1 (ACtlCutP.Sfr fr + 38) (LMM.le1 (Z_to_bv 64 0)) ->
  J0 cx (ACtlCut.own6 cx) ly2 S2 W2 mem2 md2 k ->
  Reusable.YG01.frames S2 = Reusable.YG01.frames S3 ->
  Permutation (Reusable.YG0d.ablocks B ly2 S2) (Reusable.YG0d.ablocks B ly3 S3) ->
  Reusable.YG0d.aregs_preserved regs3 regs2 ->
  K11.getr regs2 10 = Reusable.YG0d.w64
    (RRP.reply_ret phi (ACtlCutP.flen cx j) (fr + 256) (fr + 272) (fr + 304) (SM.t_g (ACtlCut.c_in cx) j)) ->
  A.Prog.CtrlCallerJ.tcj_kept (PI := A.Prog.CtrlImg.PI_ctrl) B A.Prog.C_reac_ctrl_identity_reply.TREPLY_STK
    ly3 S3 W3 m1 W2 mem2 (Reusable.YG0d.spZ regs3) (f9E cx j phi fr) ->
  (RRP.reply_ok phi (ACtlCutP.flen cx j) (fr + 256) (fr + 272) (fr + 304) (SM.t_g (ACtlCut.c_in cx) j) = true ->
     CI00.garr8 segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W2) mem2) (fr + 256)
       (map bv_unsigned (RRP.reply_addr (SM.t_g (ACtlCut.c_in cx) j))) /\
     I04.val_mem segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W2) mem2) (fr + 272) 8 (phi + 38) /\
     I04.val_mem segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W2) mem2) (fr + 304) 8
       (RRP.ir_s (SM.t_g (ACtlCut.c_in cx) j) - 13)) ->
  ACtlCut.cut_body C_A81ff4_at cx [Z.of_nat j] (Reusable.YG0d.ablocks B ly2 S2) fr fr regs2 mem2.
Proof.
  intros cx j fr k ly3 S3 W3 regs3 mem3 md3 m1 md1 phi A0 ly2 S2 W2 regs2 mem2 md2 HB HJ HJ1 HF HL HFRAC R9A0 HA0r
    HPerm Hcn Hj HHB HFLSI HLK HbC HbK HIDj HF17 HW240 HPF MU B32 B34 B38 HJ2 HF2 HP2 Hpres3 Ha0 Hkept HRP.
  clear R9A0 HA0r.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (Hfb6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (Hfb68 : Reusable.YG00.fs_frame_bytes 6 / 8 = 512) by reflexivity.
  destruct (@Reusable.YG0f.ASAN_CEIL_range rc) as [Hce _]. unfold Reusable.YG0f.ASAN_CEIL in Hce.
  (* FRAC at the entry: its own spill base A (the one f9_K and the two keep lemmas are used with) and sp *)
  pose proof HFRAC as (A & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hf32 & HA32 & HAS & HspA & HfrA &
    HA416 & HSlo & HSapp & _).
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in HSapp.
  (* the owned class-6 frame at the entry (ly3) and at the return (ly2), by KitMem's own6 and the AR frames law *)
  pose proof (proj1 HJ) as HAR3. pose proof (proj1 HJ2) as HAR2.
  destruct (A.ACtlG.KitMem.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & Efr3 & Hfr4096 & _ & Hfrc & Hcsp).
  destruct (A.ACtlG.KitMem.kitmem_own6 B cx [] ly2 S2 W2 mem2 md2 k fr LAWS HJ2 (eq_trans HF2 HF) HL)
    as (Hin62 & Efr2 & _ & _ & _ & _).
  rewrite Hfb6 in Hfrc. unfold A.ACfn.LLVMF_STK in Hcsp.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR3 Hin6)
    as (_ & Happfr & Hfrp3 & Hshp3).
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly2 S2 W2 mem2 md2 6 (ACtlCut.c_fpos cx) HAR2 Hin62)
    as (_ & _ & Hfrp2 & Hshp2).
  rewrite Efr3, Hfb6 in Happfr. rewrite Efr3, Hfb6 in Hfrp3. rewrite Efr3, Hfb68 in Hshp3.
  rewrite Efr2, Hfb6 in Hfrp2. rewrite Efr2, Hfb68 in Hshp2.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Happfr.
  assert (ESfr : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000) by reflexivity.
  assert (EYS : Reusable.YG0f.shadow_addr fr = ACtlCutP.Sfr fr)
    by (rewrite ESfr; unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF; lia).
  destruct (f9x_arith fr A _ Hfr4096 Hfrc Hce ltac:(lia) HfrA ltac:(lia)) as (D1 & D2 & D3 & D4).
  rewrite <- ESfr in D1, D2, D3, D4.
  (* visibility at the entry: the journal's stack window, the frame and its shadow (AR frames law), the image *)
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPW3 & _).
  unfold A.ACfn.LLVMF_STK in HPW3.
  assert (VST : forall x, A <= x < ACtlCut.c_sp cx -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (HPW3 x ltac:(lia)))).
  assert (VFR : forall x, fr <= x < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (proj1 (Hfrp3 x Hx)))).
  assert (VSH : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512 ->
            Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false).
  { intros x Hx. destruct (Hshp3 (x - ACtlCutP.Sfr fr) ltac:(lia)) as [[Hv _] _].
    rewrite EYS in Hv. replace (ACtlCutP.Sfr fr + (x - ACtlCutP.Sfr fr)) with x in Hv by ring. exact Hv. }
  assert (PSH2 : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512 ->
            Reusable.YG0n.apresent (Reusable.YA0n.w_H W2) mem2 x).
  { intros x Hx. destruct (Hshp2 (x - ACtlCutP.Sfr fr) ltac:(lia)) as [Hv _].
    rewrite EYS in Hv. replace (ACtlCutP.Sfr fr + (x - ACtlCutP.Sfr fr)) with x in Hv by ring. exact Hv. }
  assert (VKN : forall x, KNA.KIND_NAME <= x < KNA.KIND_NAME + 112 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false).
  { intros x Hx. destruct (A.ProgBridge.img_vis_W W3) as (_ & _ & Hv). apply Hv.
    unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI, KNA.KIND_NAME in *. lia. }
  (* the frame bytes are off the image (AR's client-image law) *)
  assert (FOFF : forall x, fr <= x < fr + 4096 -> ~ Reusable.YG0d.in_img segs x).
  { intros x Hx. refine (proj2 (Reusable.YG0d.al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 x HAR3 _)).
    right. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. rewrite Efr3, Hfb6. exact Hx. }
  (* the call's keep law tcj_kept, classes (i) the high window, (ii) live blocks, (iii) the image, (iv) frames *)
  destruct Hkept as (K1 & K2 & K3 & K4 & _ & _).
  assert (TST : forall x, A <= x < ACtlCut.c_sp cx ->
            Reusable.YG0n.aview segs (Reusable.YA0n.w_H W2) mem2 x = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m1 x).
  { intros x Hx. refine (K1 x _ _ _).
    - split; lia.
    - rewrite HspZ.
      unfold A.Prog.C_reac_ctrl_identity_reply.TREPLY_STK, A.Prog.C_reac_ctrl_parse.REAC_CTRL_PARSE_STK. lia.
    - intros (_ & HE). lia. }
  assert (TFR : forall x, fr <= x < fr + 4096 ->
            ~ (fr + 256 <= x < fr + 256 + 2 \/ fr + 272 <= x < fr + 272 + 8 \/ fr + 304 <= x < fr + 304 + 8) ->
            Reusable.YG0n.aview segs (Reusable.YA0n.w_H W2) mem2 x = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m1 x).
  { intros x Hx Hnc. refine (K4 6 (ACtlCut.c_fpos cx) x Hin6 _ _).
    - left. unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite Efr3, Hfb6. lia.
    - intros (_ & HE). exact (Hnc HE). }
  assert (TSH : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512 ->
            Reusable.YG0n.aview segs (Reusable.YA0n.w_H W2) mem2 x = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m1 x).
  { intros x Hx. refine (K4 6 (ACtlCut.c_fpos cx) x Hin6 _ _).
    - right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, Hfb68, EYS. lia.
    - intros (_ & HE). lia. }
  (* the live blocks: the record block, and the input block when c_n > 0 (the entry's lib pre) *)
  assert (Hinphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  assert (Hinphi2 : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly2 S2))
    by exact (Permutation_in _ (Permutation_sym HP2) Hinphi).
  destruct HB as (Hpre & _). pose proof Hpre as (_ & _ & _ & _ & Hcase & Hlenin & _).
  assert (CP : 0 < ACtlCut.c_n cx -> In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
  { intros Hn. destruct Hcase as [(E0 & _) | (_ & Hin)]; [lia|].
    apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. exact Hin. }
  assert (CP2 : 0 < ACtlCut.c_n cx -> In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly2 S2))
    by (intros Hn; exact (Permutation_in _ (Permutation_sym HP2) (CP Hn))).
  assert (BLK : forall p n, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) ->
     4096 <= p /\ p mod 16 = 0 /\
     p + Reusable.YG00.req_size n <= OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling /\
     0 <= n /\ n <= Reusable.YG00.req_size n /\
     (p + Reusable.YG00.req_size n <= 0x7fff7000 \/ 0x10007fff8000 <= p) /\
     (p + Reusable.YG00.req_size n <= fr \/ fr + 4096 <= p) /\
     (forall x, p <= x < p + Reusable.YG00.req_size n -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)).
  { intros p n Hin.
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR3 Hin)
      as (H16 & H4096 & Hc & Happ & Hp & _ & Hn).
    pose proof (Reusable.YCbq.sep_block_frame _ B LAWS ly3 S3 W3 mem3 md3 p n 6 (ACtlCut.c_fpos cx) HAR3 Hin Hin6)
      as Hsep.
    unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite Efr3, Hfb6 in Hsep.
    pose proof (Reusable.YCbq.req_size_pos n (proj1 Hn)) as Hrs.
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
      Reusable.YG0f.ASAN_CEIL in Happ.
    split; [lia|]. split; [exact H16|]. split; [exact Hc|]. split; [lia|]. split; [lia|].
    split; [lia|]. split; [lia|].
    intros x Hx. exact (proj1 (proj1 (Hp x Hx))). }
  assert (TB : forall p n x, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) -> p <= x < p + Reusable.YG00.req_size n ->
            Reusable.YG0n.aview segs (Reusable.YA0n.w_H W2) mem2 x = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m1 x).
  { intros p n x Hin Hx. destruct (BLK p n Hin) as (_ & _ & _ & _ & _ & _ & Hsep & _).
    pose proof (K2 p n (x - p) Hin ltac:(lia) ltac:(intros (_ & HE); lia)) as E.
    replace (p + (x - p)) with x in E by ring. exact E. }
  (* mem3 -> m1 (outside the run's six writes) -> mem2 (the keep law at a visible byte) *)
  assert (KEEP : forall a b, 0 <= a < 2 ^ 64 ->
            ~ (a = ACtlCutP.Sfr fr + 32 \/ a = ACtlCutP.Sfr fr + 34 \/ a = ACtlCutP.Sfr fr + 38) ->
            ~ (fr + 256 <= a < fr + 258 \/ fr + 272 <= a < fr + 280 \/ fr + 304 <= a < fr + 312) ->
            Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false ->
            Reusable.YG0n.aview segs (Reusable.YA0n.w_H W2) mem2 a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m1 a ->
            LMM.mrd A.Img0.rsegs mem3 (LMM.wa a) = Some b -> LMM.mrd A.Img0.rsegs mem2 (LMM.wa a) = Some b).
  { intros a b Ha H1 H2 Hh E Hb. apply (f9x_mrd_view W3 W2 m1 mem2 a b Hh E).
    rewrite (A.ACtlG.KitMem.kitmem_mrd_munch _ mem3 m1 a MU Ha (f9x_out_WA _ fr a H1 H2)). exact Hb. }
  (* the shadow bytes the keep law does not cover: the AR shadow laws at both ends *)
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR3 Hinphi) as [(_ & _ & Sh3) _].
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hinphi2) as [(_ & _ & Sh2) _].
  destruct (find (f9x_zrow KNA.KIND_NAME 112) (Reusable.YG0f.as_zero_shadow B)) as [r|] eqn:Ef;
    [| exfalso; rewrite (A.AF0m.ts_zsh B TFIB_SYMS) in Ef; vm_compute in Ef; discriminate Ef].
  destruct (f9x_find_row _ _ _ _ Ef) as (Hrin & Hr1 & Hr2).
  pose proof (Reusable.YG0d.al_zshadow _ _ LAWS ly3 S3 W3 mem3 md3 r HAR3
    ltac:(unfold Reusable.YG0n.zero_shadow_ranges; right; exact Hrin)) as Z3.
  pose proof (Reusable.YG0d.al_zshadow _ _ LAWS ly2 S2 W2 mem2 md2 r HAR2
    ltac:(unfold Reusable.YG0n.zero_shadow_ranges; right; exact Hrin)) as Z2.
  (* (1) the byte agreement on f9_K *)
  assert (RK : f9_rkeep (f9_K cx j fr A phi) mem3 mem2).
  { intros a HK Ha b Hb.
    destruct HK as [Hs | [Hs | [Hf | [Hsh | [Hp | [Hps | [Hi | [His | [Hk | Hks]]]]]]]]].
    - (* the spill area: class (i) *)
      apply (KEEP a b Ha); [lia | lia | apply VST; lia | apply TST; lia | exact Hb].
    - (* the saved registers: class (i) *)
      apply (KEEP a b Ha); [lia | lia | apply VST; lia | apply TST; lia | exact Hb].
    - (* the frame minus the three cells: class (iv) *)
      apply (KEEP a b Ha); [lia | lia | apply VFR; lia | apply TFR; lia | exact Hb].
    - (* the frame shadow minus the three written bytes: class (iv) *)
      apply (KEEP a b Ha); [lia | lia | apply VSH; lia | apply TSH; lia | exact Hb].
    - (* the record block: class (ii) *)
      destruct (BLK _ _ Hinphi) as (_ & _ & _ & _ & _ & Happ & Hsep & Hv).
      apply (KEEP a b Ha); [lia | lia | apply Hv; lia | apply (TB _ _ a Hinphi); lia | exact Hb].
    - (* its shadow: AR_shadow_law at mem3 and at mem2 *)
      apply (f9x_view_both W3 W2 mem3 mem2 (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF phi) a
               ((Reusable.YG00.req_size (ACtlCutP.flen cx j) + 7) / 8)
               (fun i => if i <? Reusable.YG00.req_size (ACtlCutP.flen cx j) / 8 then 0
                         else Reusable.YG00.req_size (ACtlCutP.flen cx j) mod 8) b Sh3 Sh2); [| exact Hb].
      unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF.
      unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Hps. lia.
    - (* the input block: class (ii) *)
      assert (Hn : 0 < ACtlCut.c_n cx) by lia. pose proof (CP Hn) as Hin.
      destruct (BLK _ _ Hin) as (_ & _ & _ & _ & Hle & Happ & Hsep & Hv).
      apply (KEEP a b Ha); [lia | lia | apply Hv; lia | apply (TB _ _ a Hin); lia | exact Hb].
    - (* its shadow: AR_shadow_law at mem3 and at mem2 *)
      destruct His as (Hn & His). pose proof (CP Hn) as Hin. pose proof (CP2 Hn) as Hin2.
      destruct (BLK _ _ Hin) as (_ & _ & _ & _ & Hle & _).
      destruct (Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR3 Hin) as [(_ & _ & C3) _].
      destruct (Reusable.YG0d.al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hin2) as [(_ & _ & C2) _].
      apply (f9x_view_both W3 W2 mem3 mem2 (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (ACtlCut.c_p cx)) a
               ((Reusable.YG00.req_size (ACtlCut.c_n cx) + 7) / 8)
               (fun i => if i <? Reusable.YG00.req_size (ACtlCut.c_n cx) / 8 then 0
                         else Reusable.YG00.req_size (ACtlCut.c_n cx) mod 8) b C3 C2); [| exact Hb].
      assert ((ACtlCut.c_n cx + 7) / 8 <= (Reusable.YG00.req_size (ACtlCut.c_n cx) + 7) / 8)
        by (apply Z.div_le_mono; lia).
      unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF.
      unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in His. lia.
    - (* the kind-name table: class (iii) *)
      apply (KEEP a b Ha).
      + unfold KNA.KIND_NAME in Hk. lia.
      + intros HC. apply (FOFF a ltac:(lia)). apply A.ACtlG.KitMem.kitmem_in_img.
        unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI, KNA.KIND_NAME in *. lia.
      + apply VKN. exact Hk.
      + refine (K3 a _ _ _).
        * apply A.ACtlG.KitMem.kitmem_in_img.
          unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI, KNA.KIND_NAME in *. lia.
        * rewrite (A.AF0m.ts_owned B TFIB_SYMS). exact (f9x_kn_unowned a Hk).
        * rewrite (A.AF0m.ts_errno B TFIB_SYMS). unfold A.AF0m.TFIB_ERRNO, KNA.KIND_NAME in *. lia.
      + exact Hb.
    - (* its shadow: a zero-shadow row of the bundle (found by search), AR_zshadow_law at both ends *)
      apply (f9x_view_both W3 W2 mem3 mem2 (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (fst r)) a
               (snd r / 8) (fun _ => 0) b Z3 Z2); [| exact Hb].
      unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF.
      unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, KNA.KIND_NAME in Hks. unfold KNA.KIND_NAME in Hr1, Hr2.
      clear - Hks Hr1 Hr2. Z.div_mod_to_equations. lia. }
  (* (2) the facts at mem2 that are not transports *)
  assert (Hstk2 : LFR.stk A.Img0.rsegs mem2 fr (fr + ACtlCutP.FRAME_BYTES)).
  { unfold ACtlCutP.FRAME_BYTES. apply (A.ACtlG.KitMem.kitmem_stk_of_present (Reusable.YA0n.w_H W2)); [lia | lia |].
    intros x Hx. exact (proj1 (Hfrp2 x ltac:(lia))). }
  assert (Hsh2 : exists sh, LMM.bytes_at segs mem2 (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW).
  { change ACtlCutP.FRAME_SHADOW with 392.
    assert (Hst : LFR.stk A.Img0.rsegs mem2 (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 392)).
    { apply (A.ACtlG.KitMem.kitmem_stk_of_present (Reusable.YA0n.w_H W2)); [lia | lia |].
      intros x Hx. exact (PSH2 x ltac:(lia)). }
    destruct (LFR.stk_bytes A.Img0.rsegs mem2 _ _ Hst ltac:(lia)) as (bs & Hl & Hbs).
    exists bs. split; [exact Hbs|]. rewrite Hl. f_equal. ring. }
  assert (MV : forall x c, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512 ->
             LMM.mrd A.Img0.rsegs m1 (LMM.wa x) = Some c -> LMM.mrd A.Img0.rsegs mem2 (LMM.wa x) = Some c)
    by (intros x c Hx Hc; exact (f9x_mrd_view W3 W2 m1 mem2 x c (VSH x Hx) (TSH x Hx) Hc)).
  assert (E32 : LMM.mrd A.Img0.rsegs m1 (LMM.wa (ACtlCutP.Sfr fr + 32)) = Some (Z_to_bv 8 2)).
  { destruct B32 as (_ & _ & Hb). specialize (Hb 0%nat ltac:(rewrite LMM.length_le1; lia)).
    change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb. exact Hb. }
  assert (E34 : LMM.mrd A.Img0.rsegs m1 (LMM.wa (ACtlCutP.Sfr fr + 34)) = Some (Z_to_bv 8 0)).
  { destruct B34 as (_ & _ & Hb). specialize (Hb 0%nat ltac:(rewrite LMM.length_le1; lia)).
    change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb. exact Hb. }
  assert (E38 : LMM.mrd A.Img0.rsegs m1 (LMM.wa (ACtlCutP.Sfr fr + 38)) = Some (Z_to_bv 8 0)).
  { destruct B38 as (_ & _ & Hb). specialize (Hb 0%nat ltac:(rewrite LMM.length_le1; lia)).
    change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb. exact Hb. }
  assert (APP : forall x, fr <= x < fr + 4096 -> A.AsanRT.app_mem x).
  { intros x Hx. unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  assert (RC2 : ACtlCutP.b5_RC fr mem2).
  { split; [|split].
    - apply (f9x_addr_cell mem2 fr 256 2 (Z_to_bv 8 2)); [exact Hf32 | lia | reflexivity | lia | lia
        | intros x Hx; apply APP; lia | unfold A.AsanRT.APPMEM_END; lia
        | exact (MV (ACtlCutP.Sfr fr + 32) _ ltac:(lia) E32) |].
      right. change (bv_signed (Z_to_bv 8 2)) with 2. lia.
    - apply (f9x_addr_cell mem2 fr 272 8 (Z_to_bv 8 0)); [exact Hf32 | lia | reflexivity | lia | lia
        | intros x Hx; apply APP; lia | unfold A.AsanRT.APPMEM_END; lia
        | exact (MV (ACtlCutP.Sfr fr + 34) _ ltac:(lia) E34) |].
      left. reflexivity.
    - apply (f9x_addr_cell mem2 fr 304 8 (Z_to_bv 8 0)); [exact Hf32 | lia | reflexivity | lia | lia
        | intros x Hx; apply APP; lia | unfold A.AsanRT.APPMEM_END; lia
        | exact (MV (ACtlCutP.Sfr fr + 38) _ ltac:(lia) E38) |].
      left. reflexivity. }
  destruct (BLK _ _ Hinphi) as (Hphi4096 & Hphi16 & Hphic & Hflen0 & Hreq & _ & _ & _).
  assert (HB2 : ACtlCutP.HB mem2 phi (ACtlCutP.flen cx j)).
  { split; [exact (proj1 HHB)|].
    apply (A.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly2 S2 W2 mem2 md2 phi (ACtlCutP.flen cx j));
      [exact HAR2 | exact Hinphi2 | lia | unfold A.ACtlK.a_size; lia |].
    unfold A.ACtlK.a_size, Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  assert (RP2 : RRP.reply_ok phi (ACtlCutP.flen cx j) (fr + 256) (fr + 272) (fr + 304) (SM.t_g (ACtlCut.c_in cx) j) = true ->
                ACtlCutP.b5_RPost phi fr (SM.t_g (ACtlCut.c_in cx) j) mem2).
  { intros Hok. destruct (HRP Hok) as (Hg & Hv1 & Hv2).
    assert (PFR2 : forall x, fr <= x < fr + 4096 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W2) mem2 x)
      by (intros x Hx; exact (proj1 (Hfrp2 x Hx))).
    split; [|split].
    - unfold RRP.reply_addr in *. apply (f9x_rw_g2 W2 mem2 (fr + 256) _ _ Hg); [lia | lia | intros i Hi; apply PFR2; lia].
    - apply (f9x_rw_le8 W2 mem2 (fr + 272) _ Hv1); [lia | lia | intros i Hi; apply PFR2; lia].
    - apply (f9x_rw_le8 W2 mem2 (fr + 304) _ Hv2); [lia | lia | intros i Hi; apply PFR2; lia]. }
  (* (3) the carried bundles and FRAC, then the body *)
  assert (HA0 : 0 <= A) by lia.
  assert (HA416' : A + 416 <= A.AsanRT.APPMEM_END) by (unfold A.AsanRT.APPMEM_END; lia).
  assert (Hcp8 : 0 < ACtlCut.c_n cx -> ACtlCut.c_p cx mod 8 = 0).
  { intros Hn. destruct (BLK _ _ (CP Hn)) as (_ & H16 & _). clear - H16. Z.div_mod_to_equations. lia. }
  assert (Hphi8 : phi mod 8 = 0) by (clear - Hphi16; Z.div_mod_to_equations; lia).
  destruct (f9g_body_keep cx j fr A phi regs3 regs2 mem3 mem2 RK Hpres3 R9 HA0 HA416'
              ltac:(lia) Hf32 ltac:(unfold A.AsanRT.APPMEM_END; lia) ltac:(lia) Hphi8 Hflen0
              ltac:(unfold A.AsanRT.APPMEM_END; lia) Hcp8 (eq_sym Hlenin) Hstk2
              HFLSI HLK HbC HbK HIDj HF17 HW240 HPF)
    as (FLSI2 & LK2 & bC2 & bK2 & IDj2 & F172 & W2402 & PF2).
  pose proof (f9g_frac_keep cx j fr A phi regs3 regs2 mem3 mem2 RK Hpres3 HFRAC R9 HA0 HA416' Hsh2) as FRAC2.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81ff4_at ACtlCutP.ixn nth].
  rewrite Nat2Z.id.
  split; [exact FRAC2|].
  unfold ACtlCutP.b5_body. exists phi.
  split; [exact (perm_trans HP2 HPerm)|].
  split; [exact Hcn|]. split; [exact Hj|]. split; [exact HB2|].
  split; [exact FLSI2|]. split; [exact LK2|]. split; [exact bC2|].
  split; [exact bK2|]. split; [exact RC2|]. split; [exact Ha0|]. split; [exact RP2|].
  split; [exact IDj2|]. split; [exact F172|]. split; [exact W2402|]. exact PF2.
Qed.

Lemma glue_seg_F9 : forall POST (j : nat), CF POST (ix_cut C_A81ff4_at [Z.of_nat j]) -> CF POST (ix_cut C_A81f88_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [j] (ix_cut, ACtlCut.v:232-234; C_A81f88_at, ACtlCutP.v:2135-2146) *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81f88_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HPerm & Hcn & Hj & HHB & HFLSI & HLK & HbC & HbK & R10 & HKNs & HIDj & HF17 &
    HW240 & HPF).
  change (ACtlCut.cut_own (ix_cut C_A81f88_at [Z.of_nat j]) cx) with (ACtlCut.own6 cx) in HJ, HF, HL.
  pose proof HFRAC as (A & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hf32 & HA32 & HAS & HspA & HfrA &
    HA416 & HSlo & HSapp & _).
  pose proof HbC as (R23 & R18 & _ & _).
  pose proof HB as ((Hafn & _ & _ & _ & _ & _ & _ & _ & _ & _ & Haro & _) & _).
  pose proof Hafn as (_ & _ & _ & Hgp & _).
  (* G2: bounds from visible state: the owned frame (kitmem_own6), the record block (the AR block law). *)
  destruct (A.ACtlG.KitMem.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & Efr3 & Hfr4096 & Hfr32 & Hfrc & Hcsp).
  assert (Hinphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ (proj1 HJ) Hinphi)
    as (_ & Hphi4096 & Hphic & _ & _ & _ & Hlen).
  pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx j) (proj1 Hlen)) as Hreq.
  pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_lt rc) as Hcl.
  unfold Reusable.YG00.MALLOC_MAX in Hlen.
  assert (Hfb6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (HAb : 0 <= A < 2 ^ 64)
    by (unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in *; lia).
  (* G3: the cut's configuration in the run's state form, the walk moved to the run's canonical register map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81f88_at [Z.of_nat j])) with 0x81f88.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRG.mkR_of regs3) regs3 K11.fp_regs
           (Z_to_bv 64 0x81f88) K11.fp_csr None mem3 (K11.seg_rom segs) md3 (POST cx));
    [| exact (LRG.xregs_eqv_sym _ _ (LRG.mkR_of_eqv regs3))].
  rewrite f9g_mkR_of.
  unfold ACtlCut.rgv in R9, R10, R18, R19, R23, R26.
  rewrite R9, R10, R18, R19, R23, R26.
  (* G4: the run f9_evtA_F ; f9_evtB_pre_F at RNG_W (w_H W3), lifted once *)
  destruct (f9g_entry cx j fr k ly3 S3 W3 regs3 mem3 md3 phi A HB HJ HF HL HFRAC R9 HAb HFLSI HbC HKNs Hrt) as
    (HX47 & HS30 & Hfr0 & HA0 & HfrA' & HA64 & HS3A & HS3fr & (b & RK & OK) & (c0 & RC0 & HC0) & Wsh & Wa & Wp & Wn &
     Q256 & Q272 & Q264 & RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & RG7 & RG8 & RG9).
  pose proof (f9g_run (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
    (K11.getr regs3 1) (K11.getr regs3 2) (K11.getr regs3 3) (K11.getr regs3 4) (K11.getr regs3 5)
    (K11.getr regs3 6) (K11.getr regs3 7) (K11.getr regs3 8)
    (K11.getr regs3 11) (K11.getr regs3 12) (K11.getr regs3 13) (K11.getr regs3 14) (K11.getr regs3 15)
    (K11.getr regs3 16) (K11.getr regs3 17)
    (K11.getr regs3 20) (K11.getr regs3 21) (K11.getr regs3 22) (K11.getr regs3 24) (K11.getr regs3 25)
    (K11.getr regs3 27) (K11.getr regs3 28) (K11.getr regs3 29) (K11.getr regs3 30) (K11.getr regs3 31)
    K11.fp_regs K11.fp_csr mem3 _ A (ACtlCutP.Sfr fr) fr phi (ACtlCutP.flen cx j) b c0
    HX47 HS30 Hfr0 HA0 HfrA' HA64 HS3A HS3fr RK OK RC0 HC0 Wsh Wa Wp Wn Q256 Q272 Q264
    RG1 RG2 RG3 RG4 RG5 RG6 RG7 RG8 RG9) as HRUN.
  destruct (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as (ms1 & Hfs & HQ1).
  destruct HQ1 as (m1 & -> & MU & B32 & B34 & B38 & Ba & Bp & Bn).
  apply (Reusable.YA0nR.SRr_fsteps segs A.ACtlG.Kit.kit_wx W3 _ _ md3 _ (POST cx) Hfs
           (A.ProgBridge.fp_avoids_RNG_W _)).
  intros md1 Hsbm1.
  (* the journal across the run: a Theorem Labs lane's ajournal_of_fsteps, write set f9_WA (the owned frame and its shadow) *)
  assert (HJ1 : J0 cx (ACtlCut.own6 cx) ly3 S3 W3 m1 md1 k).
  { refine (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfs _ MU Hsbm1 _);
      [exact HJ | apply A.ProgBridge.fp_avoids_RNG_W | exact (f9g_awr cx fr k ly3 S3 W3 mem3 md3 HJ HF HL)]. }
  (* G5: the reply call, the treac_ctrl_identity_reply_spec walk at its entry (TREPLY), then the exit cut *)
  lazymatch goal with
  | |- Reusable.YA0n.SRr _ _ (mkCfg (LMS.MS ?R _ _ _ _ _ _) _) _ => set (R1 := R)
  end.
  change (Reusable.YA0n.SRr segs W3
    (Reusable.YG0d.cfg_at segs A.Prog.reac_ctrl_identity_reply_c.REAC_CTRL_IDENTITY_REPLY R1 m1 md1) (POST cx)).
  rewrite <- f9g_reply_pc.
  assert (EspR : Reusable.YG0d.spZ R1 = sp) by exact HspZ.
  eapply Reusable.YA0n.SRr_bind.
  { apply (TREPLY A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
             (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 W3 m1 md1 k R1 phi (ACtlCutP.flen cx j)
             (fr + 256) (fr + 272) (fr + 304) (SM.t_g (ACtlCut.c_in cx) j)).
    - exact HJ1.
    - exact (A.ACtlG.KitMem.kitmem_arodataS_journal (SK := A.AE2k.tfib_sink_head) B RLO RHI
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ1 Haro).
    - vm_compute. reflexivity.
    - vm_compute. congruence.
    - exact (eq_trans R3 Hgp).
    - exact R4.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite EspR. exact Hsp16.
    - rewrite EspR.
      unfold A.Prog.C_reac_ctrl_identity_reply.TREPLY_STK, A.Prog.C_reac_ctrl_parse.REAC_CTRL_PARSE_STK, A.ACfn.LLVMF_STK.
      lia.
    - rewrite EspR. lia.
    - rewrite HF. unfold ACtlCut.own6. vm_compute. reflexivity.
    - unfold SM.t_g. apply SM.fr50_length.
    - intros Hargs H50.
      exact (f9g_msg cx j fr k ly3 S3 W3 regs3 mem3 md3 m1 md1 phi A HB HJ HJ1 HF HL HFRAC R9 HAb HPerm HbC MU
               Hargs H50).
    - intros Hargs.
      exact (f9g_cells cx fr k ly3 S3 W3 regs3 mem3 md3 m1 md1 phi A HB HJ HJ1 HF HL HFRAC R9 HAb MU
               B32 B34 B38 Ba Bp Bn Hargs). }
  intros W2 c2 Hle Hpost.
  unfold A.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_post in Hpost.
  destruct Hpost as (Hwle & ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & Hpres & HF2 & HP2 & Ha0 & Hkept & HRP).
  subst c2. unfold A.Prog.C_reac_ctrl_identity_reply.EV_REPLY in HJ2. rewrite Z.add_0_r in HJ2.
  change (Reusable.YA0n.SRr segs W2
    (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81ff4_at [Z.of_nat j])) regs2 mem2 md2) (POST cx)).
  (* the callee-saved registers of R1 are regs3's (the run kept them, or wrote the value regs3 holds) *)
  assert (HpresR : forall r, Reusable.YG0d.acallee_saved r ->
            K11.getr R1 (Z_to_bv 5 r) = K11.getr regs3 (Z_to_bv 5 r)).
  { intros r Hr. unfold Reusable.YG0d.acallee_saved in Hr.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                 r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      first [ reflexivity | exact (eq_sym R9) | exact (eq_sym R18) | exact (eq_sym R19) | exact (eq_sym R23)
            | exact (eq_sym R26) ]. }
  assert (Hpres3 : Reusable.YG0d.aregs_preserved regs3 regs2).
  { intros r Hr. rewrite (Hpres r Hr). exact (HpresR r Hr). }
  apply (HX cx [Z.of_nat j] fr k ly2 S2 W2 regs2 mem2 md2 HB).
  - exact HJ2.
  - rewrite HF2. exact HF.
  - exact HL.
  - exact Hk.
  - split; [reflexivity|].
    exact (f9g_exit_body cx j fr k ly3 S3 W3 regs3 mem3 md3 m1 md1 phi A ly2 S2 W2 regs2 mem2 md2 HB HJ HJ1 HF HL
             HFRAC R9 HAb HPerm Hcn Hj HHB HFLSI HLK HbC HbK HIDj HF17 HW240 HPF MU B32 B34 B38 HJ2 HF2 HP2 Hpres3
             Ha0 Hkept HRP).
  - (* route (C): ctl_rt_C at the exit journal's AR (no VIS0, no OWNED_RO) *)
    exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly2 S2 W2 mem2 md2 (proj1 HJ2)
             (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _
                (A.ACtlG.KitMem.kitmem_arodataS_journal (SK := A.AE2k.tfib_sink_head) B RLO RHI
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ2 Haro) (Z.le_refl _) (Z.le_refl _))).
Qed.

End GlueF9.

Print Assumptions glue_seg_F9.
