(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2004 of its 2120 lines of code are new or changed and 895 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F30.v; 526 of its 716 lines of code are new or changed and 1930 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F30.v acba01bfc56c (the blob this tree had at release c5e779efe8c) (the same blob at
   a working branch 5b5db392755 and at the glue base a working branch 5f2b9fab28a).
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Callee: the PLAIN contract reac_ctrl_classify_box_frame_contract of lib/A/Prog/reac_ctrl_classify_box_frame_c.v,
   built against the glue base's blob e726b412747 (a working branch has blob 4ea5f8974df: the same plain
   contract plus a contract_F block that this file does not use).
   Compare: each <r>_of_pre_post re-derives F30.F30Call.<r> from the two stretches at ExecF.RNG_all and the plain
   contract (Section Hypothesis HC, which is F30.v's own first premise); <r>_of_pre_post_verbatim checks by
   constr_eq that its type is the type of F30.F30Call.<r>. Mechanical re-cut, SPLIT STRETCHES (a Theorem Labs lane ruling
   00:45Z; shape fixed by a Theorem Labs lane 00:48Z; Theorem Labs split rule of a Theorem Labs lane with a Theorem Labs lane 04:01Z: a split goes in
   a new Seg/<S>Fs.v); input to the ported walk only. rule 24: no function proved. *)
(* SPLIT at the call of reac_ctrl_classify_box_frame, one of the eight cgif-form fake-stack callees: call pc 0x82794
   (jal), callee entry 0x831b8 (lib/A/Prog/reac_ctrl_classify_box_frame_c.v REAC_CTRL_CLASSIFY_BOX_FRAME), return pc
   0x82798. The walk's glue (a Theorem Labs lane, 03:5xZ) cites a Theorem Labs lane's cgif-form callee spec
   treac_ctrl_classify_box_frame_spec (a working branch 987412bd10d; at 7025616996c in
   lib/A/Prog/C_reac_ctrl_classify_box_frame.v, entry A_reac_ctrl_classify_box_frameP = 0x80edc + 0x22dc = 0x831b8,
   ra = getr regs 1) at that entry with ra = 0x82798.
   - f30_evt_call_pre_F / f30_call_norm_pre_F: the binders and premises of F30.F30Call.f30_evt_call /
     f30_call_norm without the contract premise, (RNG : ExecF.footprint) first; the jal at 0x82794 (no data access,
     so no rng premise), ending at the callee entry state: pc 0x831b8, x1 = 0x82798, every other register, the
     float map, fcsr and the memory as at 0x82794.
   - f30_evt_call_post_F / f30_call_norm_post_F: ZERO instructions, because the return pc 0x82798 is the source
     run's exit. A concrete start MS (Regs6ss.mkR_of regs) fp_regs 0x82798 fp_csr None mem under
     Context {fx : FPState} (the shape of a Theorem Labs lane's Seg/F9F.v f9_evtB_post_F; each of_pre_post instantiates
     fx := mkFP F fc). Premises: the register values the source post pins (getr regs k, k = 1 2 3 4 8 9 10 18 .. 27)
     and the facts the source holds of the callee's memory right after the contract (its existential m', here the
     universally bound mem), each as the source states it. The post's other registers (the contract post's
     existentials t0' .. t6') are the matching getr regs k. No rng premise.
   - f30_evt_call_of_pre_post: the pre stretch, F30.F30Call.f30_evt_call's own application of the plain contract
     (its lines unchanged), the post stretch.
   - f30_call_norm_of_pre_post: the pre stretch on the real memory, then F30.F30Call.f30_call_norm's normalization
     (MemNorm.evt_normalize, f30_wx, ro_agree) with the plain contract applied on the normalized memory, its
     premises moved by F30Call's transfer lemmas exactly as in f30_call_norm's bullets and the post moved back as in
     its last lines, then the post stretch. The jal touches no memory, so it is taken on the real memory before the
     normalization instead of on the normalized memory inside f30_evt_call; nothing else changes.
   NARROWED STRETCHES (a Theorem Labs lane's rule 04:23Z, relayed by a Theorem Labs lane 04:34Z): the glue consumes the _Fs forms.
   - f30_evt_call_pre_Fs: the same jal with ONLY the premises the step uses, i.e. none (binders RNG x1 .. x31 F fc m;
     the shape of a Theorem Labs lane's Seg/F9F.v f9_evtB_pre_F). It is the narrowed pre stretch of both runs: the two pre_F
     differ only in premises the jal does not read, so a separate f30_call_norm_pre_Fs would be the same text.
     f30_evt_call_pre_F_of_Fs / f30_call_norm_pre_F_of_Fs re-derive f30_evt_call_pre_F / f30_call_norm_pre_F from it;
     the *_of_Fs_verbatim pins check by constr_eq that each derived statement IS the type of that pre_F.
   - f30_evt_call_post_Fs: the zero-instruction post stretch with no premise, for any post Q of the start state
     (the shape of Seg/F9F.v f9_evtB_post_F): the post_F above over-carry for the glue (mem_inv, fp and
     reac_ctrl_classify_box_frame_tls are ctrl frame-route facts that the cgif world does not carry). The narrowed
     post stretch of both runs. f30_evt_call_post_F_of_Fs / f30_call_norm_post_F_of_Fs re-derive the two post_F from
     it (pinned the same way).
   Seg/F30F.v is not Required (nothing of it is used here). Its former contract_F twins of the call (module F30CallF,
   which cited rng_fp_cls1, absent from the glue base's classify _c.v) are deleted; these split lemmas and their pins
   are now the tie to F30.F30Call.f30_evt_call / f30_call_norm. *)
From Stdlib Require Import ZArith List Bool Lia Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcClassify.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLay reac_ctrl_classify_box_frame_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib
  reac_ctrl_classify_box_frame_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_parse_c bcmp_wrap_c memcmp_c
  asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs F29 F30.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
(* ExecF/StepF re-open bv_scope on Import; the Z arithmetic below needs Z_scope on top (as in F30.v). *)
Open Scope Z_scope.
(* F30.v's Module F30Call imports, in its order, so that every statement below reads with the contract's names. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcClassify
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_classify_box_frame_c.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFP
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parse_c.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_c.
Import F30Call.

(* The canonical register map, expanded (a Theorem Labs lane's Seg/F17F.v f17F_mkR_of_expand). *)
Lemma f30Fs_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* A machine state with no pending syscall is the MS of its own fields (a Theorem Labs lane's Seg/F9.v f9_ms_eta). *)
Lemma f30Fs_ms_eta : forall ms, ms_svc_pending ms = None ->
  ms = MS (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms) (ms_mem ms) (ms_rom ms).
Proof. intros ms H. destruct ms. cbn in H. subst. reflexivity. Qed.

(* ================= the PRE stretches: 0x82794 jal reac_ctrl_classify_box_frame, to the callee entry ========== *)

(* F30.F30Call.f30_evt_call's binders and premises (Seg/F30.v:504) without the contract premise; the script's
   first line `step.` (the jal), ending at the callee entry state. *)
Lemma f30_evt_call_pre_F :
  forall (RNG : ExecF.footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n u o v S FS : Z)
         (fr us junk vb : list byte),
    x10 = Z_to_bv 64 f -> x11 = Z_to_bv 64 n -> x12 = Z_to_bv 64 u -> x13 = Z_to_bv 64 o -> x14 = Z_to_bv 64 v ->
    x2 = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> S < 2^64 ->
    S mod 16 = 0 ->
    REAC_CTRL_CLASSIFY_BOX_FRAME_K <= S -> stk rsegs m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\
                (f + 50 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= f)) ->
    o <> 0 -> o mod 4 = 0 -> o + 36 <= 2^64 -> rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
    length us = 6%nat ->
    (50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\
                (u + 6 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= u)) ->
    v <> 0 -> v mod 4 = 0 -> v + 4 <= 2^64 -> rw_cells rsegs m v [CB 4 vb] ->
    (v + 4 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= v) ->
    (v + 4 <= o \/ o + 36 <= v) -> (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
    mem_inv rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    (50 <= n -> addressable m f 50 /\ addressable m u 6 /\ app_mem (u + 6) /\ app_mem (u + 7)) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m v 4 -> (v + 4 <= RT_LO \/ RT_HI <= v) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S (reac_ctrl_classify_box_frame_W o v S)
      (reac_ctrl_classify_box_frame_D f n u o v) ->
    reac_ctrl_classify_box_frame_tls m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82798) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
                                x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                           F (Z_to_bv 64 0x831b8) fc None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31) F (Z_to_bv 64 0x82794) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m f n u o v S FS fr us junk vb E10 E11 E12 E13 E14 Esp
    Hf Hn Hu Ho Hv HS Hmod HKS HST Hfrl HF50 Ho0 Ho4 Ho36 HRo HoW Hof Hou Husl HU50 Hv0 Hv4 Hv4b HRv HvW
    Hvo Hvf Hvu HMI HAC HSW Hhi Hsp HADW HA50 HADo Hoapp HoCF HADv HvRT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  step. (* 0x82794 jal reac_ctrl_classify_box_frame, ra = 0x82798 *)
  apply ExecF.evtF_done. reflexivity.
Qed.

(* F30.F30Call.f30_call_norm's binders and premises (Seg/F30.v:583) without the contract premise; the same jal. *)
Lemma f30_call_norm_pre_F :
  forall (RNG : ExecF.footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n u o v S FS : Z)
         (fr us junk vb : list byte),
    x10 = Z_to_bv 64 f -> x11 = Z_to_bv 64 n -> x12 = Z_to_bv 64 u -> x13 = Z_to_bv 64 o -> x14 = Z_to_bv 64 v ->
    x2 = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> S < 2^64 ->
    S mod 16 = 0 ->
    REAC_CTRL_CLASSIFY_BOX_FRAME_K <= S -> stk rsegs m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\
                (f + 50 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= f)) ->
    o <> 0 -> o mod 4 = 0 -> o + 36 <= 2^64 -> rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
    length us = 6%nat ->
    (50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\
                (u + 6 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= u)) ->
    v <> 0 -> v mod 4 = 0 -> v + 4 <= 2^64 -> rw_cells rsegs m v [CB 4 vb] ->
    (v + 4 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= v) ->
    (v + 4 <= o \/ o + 36 <= v) -> (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
    ro_agree rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    (50 <= n -> addressable m f 50 /\ addressable m u 6 /\ app_mem (u + 6) /\ app_mem (u + 7)) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m v 4 -> (v + 4 <= RT_LO \/ RT_HI <= v) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S (reac_ctrl_classify_box_frame_W o v S)
      (reac_ctrl_classify_box_frame_D f n u o v) ->
    reac_ctrl_classify_box_frame_tls m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    0x5fe000 <= o -> 0x5fe000 <= v ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82798) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
                                x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                           F (Z_to_bv 64 0x831b8) fc None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31) F (Z_to_bv 64 0x82794) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m f n u o v S FS fr us junk vb E10 E11 E12 E13 E14 Esp
    Hf Hn Hu Ho Hv HS Hmod HKS HST Hfrl HF50 Ho0 Ho4 Ho36 HRo HoW Hof Hou Husl HU50 Hv0 Hv4 Hv4b HRv HvW
    Hvo Hvf Hvu HRO HAC HSW Hhi Hsp HADW HA50 HADo Hoapp HoCF HADv HvRT HADB HRB HRM HGC HC254 HC255 HFP HTLS
    Hog Hvg.
  step. (* 0x82794 jal reac_ctrl_classify_box_frame, ra = 0x82798 *)
  apply ExecF.evtF_done. reflexivity.
Qed.

(* ---- NARROWED pre stretch: the jal with only the premises it uses (none). The glue consumes this form. *)
Lemma f30_evt_call_pre_Fs :
  forall (RNG : ExecF.footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82798) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
                                x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                           F (Z_to_bv 64 0x831b8) fc None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31) F (Z_to_bv 64 0x82794) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m.
  step. (* 0x82794 jal reac_ctrl_classify_box_frame, ra = 0x82798 *)
  apply ExecF.evtF_done. reflexivity.
Qed.

(* f30_evt_call_pre_F's statement, re-derived from the narrowed stretch (pinned below by constr_eq). *)
Lemma f30_evt_call_pre_F_of_Fs :
  forall (RNG : ExecF.footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n u o v S FS : Z)
         (fr us junk vb : list byte),
    x10 = Z_to_bv 64 f -> x11 = Z_to_bv 64 n -> x12 = Z_to_bv 64 u -> x13 = Z_to_bv 64 o -> x14 = Z_to_bv 64 v ->
    x2 = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> S < 2^64 ->
    S mod 16 = 0 ->
    REAC_CTRL_CLASSIFY_BOX_FRAME_K <= S -> stk rsegs m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\
                (f + 50 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= f)) ->
    o <> 0 -> o mod 4 = 0 -> o + 36 <= 2^64 -> rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
    length us = 6%nat ->
    (50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\
                (u + 6 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= u)) ->
    v <> 0 -> v mod 4 = 0 -> v + 4 <= 2^64 -> rw_cells rsegs m v [CB 4 vb] ->
    (v + 4 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= v) ->
    (v + 4 <= o \/ o + 36 <= v) -> (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
    mem_inv rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    (50 <= n -> addressable m f 50 /\ addressable m u 6 /\ app_mem (u + 6) /\ app_mem (u + 7)) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m v 4 -> (v + 4 <= RT_LO \/ RT_HI <= v) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S (reac_ctrl_classify_box_frame_W o v S)
      (reac_ctrl_classify_box_frame_D f n u o v) ->
    reac_ctrl_classify_box_frame_tls m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82798) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
                                x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                           F (Z_to_bv 64 0x831b8) fc None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31) F (Z_to_bv 64 0x82794) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m f n u o v S FS fr us junk vb.
  intros.
  exact (f30_evt_call_pre_Fs RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
           x24 x25 x26 x27 x28 x29 x30 x31 F fc m).
Qed.

(* f30_call_norm_pre_F's statement, re-derived from the narrowed stretch (pinned below by constr_eq). *)
Lemma f30_call_norm_pre_F_of_Fs :
  forall (RNG : ExecF.footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n u o v S FS : Z)
         (fr us junk vb : list byte),
    x10 = Z_to_bv 64 f -> x11 = Z_to_bv 64 n -> x12 = Z_to_bv 64 u -> x13 = Z_to_bv 64 o -> x14 = Z_to_bv 64 v ->
    x2 = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> S < 2^64 ->
    S mod 16 = 0 ->
    REAC_CTRL_CLASSIFY_BOX_FRAME_K <= S -> stk rsegs m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\
                (f + 50 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= f)) ->
    o <> 0 -> o mod 4 = 0 -> o + 36 <= 2^64 -> rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
    length us = 6%nat ->
    (50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\
                (u + 6 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= u)) ->
    v <> 0 -> v mod 4 = 0 -> v + 4 <= 2^64 -> rw_cells rsegs m v [CB 4 vb] ->
    (v + 4 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= v) ->
    (v + 4 <= o \/ o + 36 <= v) -> (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
    ro_agree rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    (50 <= n -> addressable m f 50 /\ addressable m u 6 /\ app_mem (u + 6) /\ app_mem (u + 7)) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m v 4 -> (v + 4 <= RT_LO \/ RT_HI <= v) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S (reac_ctrl_classify_box_frame_W o v S)
      (reac_ctrl_classify_box_frame_D f n u o v) ->
    reac_ctrl_classify_box_frame_tls m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    0x5fe000 <= o -> 0x5fe000 <= v ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82798) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
                                x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                           F (Z_to_bv 64 0x831b8) fc None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31) F (Z_to_bv 64 0x82794) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m f n u o v S FS fr us junk vb.
  intros.
  exact (f30_evt_call_pre_Fs RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
           x24 x25 x26 x27 x28 x29 x30 x31 F fc m).
Qed.

(* ================= the POST stretches: zero instructions at the return pc 0x82798 (the run's exit) ========== *)
Section PostF.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.

(* ---- NARROWED post stretch: zero instructions, no premise, any post Q of the start state (a Theorem Labs lane's
   Seg/F9F.v f9_evtB_post_F shape). The glue consumes this form. *)
Lemma f30_evt_call_post_Fs :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte) (Q : machine_state -> Prop),
    Q (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82798) fp_csr None mem (seg_rom rsegs)) ->
    ExecF.evtF rsegs RNG Q
      (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82798) fp_csr None mem (seg_rom rsegs)).
Proof. intros RNG regs mem Q HQ. apply ExecF.evtF_done. exact HQ. Qed.

(* After F30.F30Call.f30_evt_call applies the contract, the script holds the contract post: the state (here: the
   pinned registers of the canonical map regs) and the facts of the callee's memory m' (here: mem). *)
Lemma f30_evt_call_post_F :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (m : word -> option byte)
         (f n u o v S FS : Z) (fr us vb : list byte),
    getr regs 1 = Z_to_bv 64 0x82798 -> getr regs 2 = x2 -> getr regs 3 = x3 -> getr regs 4 = x4 ->
    getr regs 8 = x8 -> getr regs 9 = x9 -> getr regs 10 = Z_to_bv 64 (cl_r (classify n fr us)) ->
    getr regs 18 = x18 -> getr regs 19 = x19 -> getr regs 20 = x20 -> getr regs 21 = x21 -> getr regs 22 = x22 ->
    getr regs 23 = x23 -> getr regs 24 = x24 -> getr regs 25 = x25 -> getr regs 26 = x26 -> getr regs 27 = x27 ->
    munch ([(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] ++ fp_w [1%nat] FS ++
           [(shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K), shadow_addr S)]) m mem ->
    wmono rsegs m mem -> mem_inv rsegs mem ->
    stk rsegs mem (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    rw_cells rsegs mem o [CB 36 (snd (ctrlparse n fr))] ->
    rw_cells rsegs mem v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] ->
    asan_cells mem -> shadow_rw mem ->
    addressable mem (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    fp [1%nat] mem (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
      (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) ->
    reac_ctrl_classify_box_frame_tls mem (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82798) x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 (cl_r (classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                  fp_regs (Z_to_bv 64 0x82798) fp_csr None m' (seg_rom rsegs) /\
         munch ([(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S /\
         rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))] /\
         rw_cells rsegs m' v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K /\
         fp [1%nat] m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
           (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) /\
         reac_ctrl_classify_box_frame_tls m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S)
      (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82798) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 m f n u o v S FS fr us vb
    E1 E2 E3 E4 E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 MU WM MI' ST' HRo' HRv' AC' SW' AD' FP' TL'.
  rewrite f30Fs_mkR_of_expand, E1, E2, E3, E4, E8, E9, E10, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
  (* F30.F30Call.f30_evt_call's closing lines *)
  apply ExecF.evtF_done. cbv beta. do 14 eexists. exists mem.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact HRo'|]. split; [exact HRv'|]. split; [exact AC'|]. split; [exact SW'|].
  split; [exact AD'|]. split; [exact FP' | exact TL'].
Qed.

(* After F30.F30Call.f30_call_norm moves the contract post back to the real memory, the script holds these facts
   of the real successor memory (here: mem) and the same pinned registers. *)
Lemma f30_call_norm_post_F :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (m : word -> option byte)
         (f n u o v S FS : Z) (fr us vb : list byte),
    getr regs 1 = Z_to_bv 64 0x82798 -> getr regs 2 = x2 -> getr regs 3 = x3 -> getr regs 4 = x4 ->
    getr regs 8 = x8 -> getr regs 9 = x9 -> getr regs 10 = Z_to_bv 64 (cl_r (classify n fr us)) ->
    getr regs 18 = x18 -> getr regs 19 = x19 -> getr regs 20 = x20 -> getr regs 21 = x21 -> getr regs 22 = x22 ->
    getr regs 23 = x23 -> getr regs 24 = x24 -> getr regs 25 = x25 -> getr regs 26 = x26 -> getr regs 27 = x27 ->
    munch ([(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] ++ fp_w [1%nat] FS ++
           [(shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K), shadow_addr S)]) m mem ->
    wmono rsegs m mem -> ro_agree rsegs mem ->
    stk rsegs mem (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    rw_cells rsegs mem o [CB 36 (snd (ctrlparse n fr))] ->
    rw_cells rsegs mem v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] ->
    asan_cells mem -> shadow_rw mem ->
    addressable mem (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    fp [1%nat] mem (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
      (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) ->
    reac_ctrl_classify_box_frame_tls mem (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82798) x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 (cl_r (classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                  fp_regs (Z_to_bv 64 0x82798) fp_csr None m' (seg_rom rsegs) /\
         munch ([(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S /\
         rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))] /\
         rw_cells rsegs m' v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K /\
         fp [1%nat] m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
           (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) /\
         reac_ctrl_classify_box_frame_tls m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S)
      (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82798) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 m f n u o v S FS fr us vb
    E1 E2 E3 E4 E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 MU WM RO' ST' HRo' HRv' AC' SW' AD' FP' TL'.
  rewrite f30Fs_mkR_of_expand, E1, E2, E3, E4, E8, E9, E10, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
  (* F30.F30Call.f30_call_norm's closing lines *)
  apply ExecF.evtF_done. cbv beta. do 14 eexists. exists mem.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact RO'|]. split; [exact ST'|].
  split; [exact HRo'|]. split; [exact HRv'|]. split; [exact AC'|]. split; [exact SW'|].
  split; [exact AD'|]. split; [exact FP' | exact TL'].
Qed.

(* f30_evt_call_post_F's statement, re-derived from the narrowed stretch (pinned below by constr_eq). *)
Lemma f30_evt_call_post_F_of_Fs :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (m : word -> option byte)
         (f n u o v S FS : Z) (fr us vb : list byte),
    getr regs 1 = Z_to_bv 64 0x82798 -> getr regs 2 = x2 -> getr regs 3 = x3 -> getr regs 4 = x4 ->
    getr regs 8 = x8 -> getr regs 9 = x9 -> getr regs 10 = Z_to_bv 64 (cl_r (classify n fr us)) ->
    getr regs 18 = x18 -> getr regs 19 = x19 -> getr regs 20 = x20 -> getr regs 21 = x21 -> getr regs 22 = x22 ->
    getr regs 23 = x23 -> getr regs 24 = x24 -> getr regs 25 = x25 -> getr regs 26 = x26 -> getr regs 27 = x27 ->
    munch ([(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] ++ fp_w [1%nat] FS ++
           [(shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K), shadow_addr S)]) m mem ->
    wmono rsegs m mem -> mem_inv rsegs mem ->
    stk rsegs mem (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    rw_cells rsegs mem o [CB 36 (snd (ctrlparse n fr))] ->
    rw_cells rsegs mem v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] ->
    asan_cells mem -> shadow_rw mem ->
    addressable mem (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    fp [1%nat] mem (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
      (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) ->
    reac_ctrl_classify_box_frame_tls mem (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82798) x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 (cl_r (classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                  fp_regs (Z_to_bv 64 0x82798) fp_csr None m' (seg_rom rsegs) /\
         munch ([(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S /\
         rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))] /\
         rw_cells rsegs m' v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K /\
         fp [1%nat] m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
           (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) /\
         reac_ctrl_classify_box_frame_tls m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S)
      (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82798) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 m f n u o v S FS fr us vb
    E1 E2 E3 E4 E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 MU WM MI' ST' HRo' HRv' AC' SW' AD' FP' TL'.
  apply f30_evt_call_post_Fs. cbv beta.
  rewrite f30Fs_mkR_of_expand, E1, E2, E3, E4, E8, E9, E10, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
  do 14 eexists. exists mem.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact HRo'|]. split; [exact HRv'|]. split; [exact AC'|]. split; [exact SW'|].
  split; [exact AD'|]. split; [exact FP' | exact TL'].
Qed.

(* f30_call_norm_post_F's statement, re-derived from the narrowed stretch (pinned below by constr_eq). *)
Lemma f30_call_norm_post_F_of_Fs :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (m : word -> option byte)
         (f n u o v S FS : Z) (fr us vb : list byte),
    getr regs 1 = Z_to_bv 64 0x82798 -> getr regs 2 = x2 -> getr regs 3 = x3 -> getr regs 4 = x4 ->
    getr regs 8 = x8 -> getr regs 9 = x9 -> getr regs 10 = Z_to_bv 64 (cl_r (classify n fr us)) ->
    getr regs 18 = x18 -> getr regs 19 = x19 -> getr regs 20 = x20 -> getr regs 21 = x21 -> getr regs 22 = x22 ->
    getr regs 23 = x23 -> getr regs 24 = x24 -> getr regs 25 = x25 -> getr regs 26 = x26 -> getr regs 27 = x27 ->
    munch ([(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] ++ fp_w [1%nat] FS ++
           [(shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K), shadow_addr S)]) m mem ->
    wmono rsegs m mem -> ro_agree rsegs mem ->
    stk rsegs mem (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    rw_cells rsegs mem o [CB 36 (snd (ctrlparse n fr))] ->
    rw_cells rsegs mem v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] ->
    asan_cells mem -> shadow_rw mem ->
    addressable mem (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    fp [1%nat] mem (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
      (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) ->
    reac_ctrl_classify_box_frame_tls mem (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82798) x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 (cl_r (classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                  fp_regs (Z_to_bv 64 0x82798) fp_csr None m' (seg_rom rsegs) /\
         munch ([(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S /\
         rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))] /\
         rw_cells rsegs m' v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K /\
         fp [1%nat] m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
           (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) /\
         reac_ctrl_classify_box_frame_tls m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S)
      (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82798) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 m f n u o v S FS fr us vb
    E1 E2 E3 E4 E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 MU WM RO' ST' HRo' HRv' AC' SW' AD' FP' TL'.
  apply f30_evt_call_post_Fs. cbv beta.
  rewrite f30Fs_mkR_of_expand, E1, E2, E3, E4, E8, E9, E10, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
  do 14 eexists. exists mem.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact RO'|]. split; [exact ST'|].
  split; [exact HRo'|]. split; [exact HRv'|]. split; [exact AC'|]. split; [exact SW'|].
  split; [exact AD'|]. split; [exact FP' | exact TL'].
Qed.

End PostF.

(* ================= the two stretches at RNG_all with the PLAIN contract re-derive the source runs ========== *)
Section CallSplit.
(* The plain callee contract, F30.F30Call.f30_evt_call / f30_call_norm's own first premise. *)
Hypothesis HC : reac_ctrl_classify_box_frame_contract.

Lemma f30_evt_call_of_pre_post :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n u o v S FS : Z)
         (fr us junk vb : list byte),
    x10 = Z_to_bv 64 f -> x11 = Z_to_bv 64 n -> x12 = Z_to_bv 64 u -> x13 = Z_to_bv 64 o -> x14 = Z_to_bv 64 v ->
    x2 = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> S < 2^64 ->
    S mod 16 = 0 ->
    REAC_CTRL_CLASSIFY_BOX_FRAME_K <= S -> stk rsegs m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\
                (f + 50 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= f)) ->
    o <> 0 -> o mod 4 = 0 -> o + 36 <= 2^64 -> rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
    length us = 6%nat ->
    (50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\
                (u + 6 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= u)) ->
    v <> 0 -> v mod 4 = 0 -> v + 4 <= 2^64 -> rw_cells rsegs m v [CB 4 vb] ->
    (v + 4 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= v) ->
    (v + 4 <= o \/ o + 36 <= v) -> (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
    mem_inv rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    (50 <= n -> addressable m f 50 /\ addressable m u 6 /\ app_mem (u + 6) /\ app_mem (u + 7)) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m v 4 -> (v + 4 <= RT_LO \/ RT_HI <= v) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S (reac_ctrl_classify_box_frame_W o v S)
      (reac_ctrl_classify_box_frame_D f n u o v) ->
    reac_ctrl_classify_box_frame_tls m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82798) x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 (cl_r (classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x82798) fc None m' (seg_rom rsegs) /\
         munch ([(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S /\
         rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))] /\
         rw_cells rsegs m' v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K /\
         fp [1%nat] m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
           (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) /\
         reac_ctrl_classify_box_frame_tls m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31) F (Z_to_bv 64 0x82794) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m f n u o v S FS fr us junk vb E10 E11 E12 E13 E14 Esp
    Hf Hn Hu Ho Hv HS Hmod HKS HST Hfrl HF50 Ho0 Ho4 Ho36 HRo HoW Hof Hou Husl HU50 Hv0 Hv4 Hv4b HRv HvW
    Hvo Hvf Hvu HMI HAC HSW Hhi Hsp HADW HA50 HADo Hoapp HoCF HADv HvRT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  (* the PRE stretch at RNG_all: 0x82794 jal reac_ctrl_classify_box_frame, ra = 0x82798 *)
  eapply LE.evt_cut.
  { apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    apply (f30_evt_call_pre_F ExecF.RNG_all x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m f n u o v S FS fr us junk vb).
    all: assumption. }
  intros ms0 ->.
  (* the call: F30.F30Call.f30_evt_call's application of the plain contract *)
  pose proof HC as HC'.
  unfold reac_ctrl_classify_box_frame_contract,
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_c.REAC_CTRL_CLASSIFY_BOX_FRAME
    in HC'.
  eapply LE.evt_cut.
  { eapply HC' with (f := f) (n := n) (u := u) (o := o) (v := v) (S := S) (FS := FS) (fr := fr) (us := us)
      (junk := junk) (vb := vb).
    all: first [ assumption | reflexivity ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & ST' & HRo' & HRv' & AC' & SW' & AD' & FP' & TL').
  subst ms'.
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  (* the POST stretch at RNG_all, at the canonical form of the state the callee returned in *)
  lazymatch goal with
  | |- LE.evt _ _ (MS ?RR _ _ _ _ _ _) => change RR with (Regs6ss.mkR_of RR)
  end.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS (Regs6ss.mkR_of ?RR) _ _ _ _ _ _) =>
      apply (@f30_evt_call_post_F (mkFP F fc) ExecF.RNG_all RR m' x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 m f n u o v S FS fr us vb)
  end.
  all: first [ reflexivity | assumption ].
Qed.

Lemma f30_call_norm_of_pre_post :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n u o v S FS : Z)
         (fr us junk vb : list byte),
    x10 = Z_to_bv 64 f -> x11 = Z_to_bv 64 n -> x12 = Z_to_bv 64 u -> x13 = Z_to_bv 64 o -> x14 = Z_to_bv 64 v ->
    x2 = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> S < 2^64 ->
    S mod 16 = 0 ->
    REAC_CTRL_CLASSIFY_BOX_FRAME_K <= S -> stk rsegs m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\
                (f + 50 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= f)) ->
    o <> 0 -> o mod 4 = 0 -> o + 36 <= 2^64 -> rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
    length us = 6%nat ->
    (50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\
                (u + 6 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= u)) ->
    v <> 0 -> v mod 4 = 0 -> v + 4 <= 2^64 -> rw_cells rsegs m v [CB 4 vb] ->
    (v + 4 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= v) ->
    (v + 4 <= o \/ o + 36 <= v) -> (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
    ro_agree rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    (50 <= n -> addressable m f 50 /\ addressable m u 6 /\ app_mem (u + 6) /\ app_mem (u + 7)) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m v 4 -> (v + 4 <= RT_LO \/ RT_HI <= v) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S (reac_ctrl_classify_box_frame_W o v S)
      (reac_ctrl_classify_box_frame_D f n u o v) ->
    reac_ctrl_classify_box_frame_tls m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    0x5fe000 <= o -> 0x5fe000 <= v ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82798) x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 (cl_r (classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x82798) fc None m' (seg_rom rsegs) /\
         munch ([(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S /\
         rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))] /\
         rw_cells rsegs m' v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K /\
         fp [1%nat] m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
           (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) /\
         reac_ctrl_classify_box_frame_tls m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31) F (Z_to_bv 64 0x82794) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m f n u o v S FS fr us junk vb E10 E11 E12 E13 E14 Esp
    Hf Hn Hu Ho Hv HS Hmod HKS HST Hfrl HF50 Ho0 Ho4 Ho36 HRo HoW Hof Hou Husl HU50 Hv0 Hv4 Hv4b HRv HvW
    Hvo Hvf Hvu HRO HAC HSW Hhi Hsp HADW HA50 HADo Hoapp HoCF HADv HvRT HADB HRB HRM HGC HC254 HC255 HFP HTLS
    Hog Hvg.
  (* F30.F30Call.f30_call_norm's first lines *)
  pose proof (mem_rel_normalize rsegs m HRO) as R.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs (normalize rsegs m) a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m (normalize rsegs m) a bs R)).
  assert (Hlo : 0x5fe000 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) by (unfold HIGHMEM_BEG in Hhi; lia).
  (* the PRE stretch at RNG_all, on the real memory: 0x82794 jal reac_ctrl_classify_box_frame, ra = 0x82798 *)
  eapply LE.evt_cut.
  { apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    apply (f30_call_norm_pre_F ExecF.RNG_all x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m f n u o v S FS fr us junk vb).
    all: assumption. }
  intros ms0 ->.
  (* F30.F30Call.f30_call_norm's premise transfers to the normalized memory, bullet by bullet *)
  pose proof (proj1 (f30_stk_rel m _ _ _ R Hlo) HST) as HSTn.
  assert (HF50n : 50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs (normalize rsegs m) f fr /\
                  (f + 50 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= f)).
  { intros H50. destruct (HF50 H50) as (P1 & P2 & P3 & P4).
    split; [exact P1|]. split; [exact P2|]. split; [apply BR; exact P3 | exact P4]. }
  pose proof (proj1 (f30_rw_rel m _ _ _ R Hog) HRo) as HRon.
  assert (HU50n : 50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs (normalize rsegs m) u us /\
                  (u + 6 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= u)).
  { intros H50. destruct (HU50 H50) as (P1 & P2 & P3).
    split; [exact P1|]. split; [apply BR; exact P2 | exact P3]. }
  pose proof (proj1 (f30_rw_rel m _ _ _ R Hvg) HRv) as HRvn.
  pose proof (mem_inv_normalize rsegs m) as HMIn.
  pose proof (proj1 (f30_cells_rel m _ R) HAC) as HACn.
  pose proof (proj1 (f30_srw_rel m _ R) HSW) as HSWn.
  pose proof (proj1 (f30_addr_rel m _ _ _ R) HADW) as HADWn.
  assert (HA50n : 50 <= n -> addressable (normalize rsegs m) f 50 /\ addressable (normalize rsegs m) u 6 /\
                  app_mem (u + 6) /\ app_mem (u + 7)).
  { intros H50. destruct (HA50 H50) as (P1 & P2 & P3 & P4).
    split; [apply (proj1 (f30_addr_rel m _ _ _ R)); exact P1|].
    split; [apply (proj1 (f30_addr_rel m _ _ _ R)); exact P2|].
    split; [exact P3 | exact P4]. }
  pose proof (proj1 (f30_addr_rel m _ _ _ R) HADo) as HADon.
  pose proof (proj1 (f30_addr_rel m _ _ _ R) HADv) as HADvn.
  pose proof (proj1 (f30_addr_rel m _ _ _ R) HADB) as HADBn.
  pose proof (proj1 (BR _ _) HRB) as HRBn.
  pose proof (proj1 (BR _ _) HRM) as HRMn.
  pose proof (proj1 (BR _ _) HGC) as HGCn.
  pose proof (proj1 (BR _ _) HC254) as HC254n.
  pose proof (proj1 (BR _ _) HC255) as HC255n.
  pose proof (proj1 (f30_fp_rel _ m _ _ _ _ _ _ _ R) HFP) as HFPn.
  pose proof (proj1 (f30_clstls_rel m _ _ _ _ _ R) HTLS) as HTLSn.
  (* the call on the normalized memory: f30_call_norm's MemNorm.evt_normalize step around f30_evt_call's
     application of the plain contract *)
  pose proof HC as HC'.
  unfold reac_ctrl_classify_box_frame_contract,
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_c.REAC_CTRL_CLASSIFY_BOX_FRAME
    in HC'.
  eapply LE.evt_cut.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) f30_wx HRO).
    eapply HC' with (f := f) (n := n) (u := u) (o := o) (v := v) (S := S) (FS := FS) (fr := fr) (us := us)
      (junk := junk) (vb := vb).
    all: first [ assumption | reflexivity ]. }
  (* f30_call_norm's last lines: the post moved back to the real memory *)
  intros s (s0' & HQ & REL & SAME).
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E0 & MU & WM & MI & ST & HRo' & HRv' & AC' & SW' & AD' & FP' & TL').
  subst s0'.
  destruct REL as (ER & EF & Epc & Esv & Erv & Efc & Erom & RM).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in ER, EF, Epc, Esv, Erv, Efc,
    Erom, RM, SAME.
  rewrite (f30Fs_ms_eta s Esv), ER, EF, Epc, Erv, Efc, Erom.
  replace (ret_pc (Z_to_bv 64 0x82798)) with (Z_to_bv 64 0x82798)
    by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* the POST stretch at RNG_all, at the canonical form of the real successor state *)
  lazymatch goal with
  | |- LE.evt _ _ (MS ?RR _ _ _ _ _ _) => change RR with (Regs6ss.mkR_of RR)
  end.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS (Regs6ss.mkR_of ?RR) _ _ _ _ _ _) =>
      apply (@f30_call_norm_post_F (mkFP F fc) ExecF.RNG_all RR (ms_mem s) x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23
               x24 x25 x26 x27 m f n u o v S FS fr us vb)
  end.
  all: try reflexivity.
  - exact (munch_rel rsegs _ m (normalize rsegs m) (ms_mem s) m0' R RM SAME MU).
  - exact (wmono_rel rsegs m (normalize rsegs m) (ms_mem s) m0' R RM SAME WM).
  - exact (ro_agree_same rsegs m (ms_mem s) HRO SAME).
  - apply (proj2 (f30_stk_rel (ms_mem s) m0' _ _ RM Hlo)); exact ST.
  - apply (proj2 (f30_rw_rel (ms_mem s) m0' _ _ RM Hog)); exact HRo'.
  - apply (proj2 (f30_rw_rel (ms_mem s) m0' _ _ RM Hvg)); exact HRv'.
  - apply (proj2 (f30_cells_rel (ms_mem s) m0' RM)); exact AC'.
  - apply (proj2 (f30_srw_rel (ms_mem s) m0' RM)); exact SW'.
  - apply (proj2 (f30_addr_rel (ms_mem s) m0' _ _ RM)); exact AD'.
  - apply (proj2 (f30_fp_rel _ (ms_mem s) m0' _ _ _ _ _ _ RM)); exact FP'.
  - apply (proj2 (f30_clstls_rel (ms_mem s) m0' _ _ _ _ RM)). exact TL'.
Qed.

End CallSplit.

(* ---- The pins (the no-weakening check): after End Section each of_pre_post carries the plain contract as its
   first premise (Hypothesis HC), so its type is F30.F30Call.<r>'s, term for term (constr_eq: syntactic, not up
   to conversion). *)
Lemma f30_evt_call_of_pre_post_verbatim : True.
Proof.
  let a := type of F30.F30Call.f30_evt_call in let b := type of f30_evt_call_of_pre_post in constr_eq a b.
  exact I.
Qed.

Lemma f30_call_norm_of_pre_post_verbatim : True.
Proof.
  let a := type of F30.F30Call.f30_call_norm in let b := type of f30_call_norm_of_pre_post in constr_eq a b.
  exact I.
Qed.

(* ---- The narrowed-stretch pins: each *_of_Fs (proved from the narrowed _Fs stretch) states the stretch it
   re-derives, term for term (constr_eq), so the narrowed stretch is provably the same stretch. *)
Lemma f30_evt_call_pre_F_of_Fs_verbatim : True.
Proof.
  let a := type of f30_evt_call_pre_F in let b := type of f30_evt_call_pre_F_of_Fs in constr_eq a b.
  exact I.
Qed.

Lemma f30_call_norm_pre_F_of_Fs_verbatim : True.
Proof.
  let a := type of f30_call_norm_pre_F in let b := type of f30_call_norm_pre_F_of_Fs in constr_eq a b.
  exact I.
Qed.

Lemma f30_evt_call_post_F_of_Fs_verbatim : True.
Proof.
  let a := type of @f30_evt_call_post_F in let b := type of @f30_evt_call_post_F_of_Fs in constr_eq a b.
  exact I.
Qed.

Lemma f30_call_norm_post_F_of_Fs_verbatim : True.
Proof.
  let a := type of @f30_call_norm_post_F in let b := type of @f30_call_norm_post_F_of_Fs in constr_eq a b.
  exact I.
Qed.
