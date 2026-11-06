(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 53 of its 78 lines of code are new or changed and 493 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140): the ONE cut INSIDE
   the segment S_MF_ENTRY of lib/B/Prog/m_file_m.v, at the snprintf return 0x862ac, and the model terms of the
   prologue. A walk lane of the image-B m_file-family owner's G2B. Statement text only: no instruction is executed here.

   S_MF_ENTRY (the image-B m_file segment table section 1, the image-B m_file cut map section 4) runs 0x86140-0x86374 and 0x86e84-0x86ebc. It is
   proved in two halves, because the snprintf wrapper's post is FP-existential (the wrapper returns at its own FP
   state fx1, PaFx.v art_postF / srr_after_artF), so the half after the call must hold at EVERY FP state:
     mf_entry_1.v  ENTRY 0x86140 -> the snprintf call 0x862a8 -> this cut, by MFE_MID_F;
     mf_entry_2.v  this cut 0x862ac -> HEAD 0x86378 (text nonempty) or EXIT 0x86da0 (text empty), = MFE_MID_F.
   MFE_RET_SNP = AF_m_file + 0x16c is the listing offset of 0x862ac (`ld s6,128(s1)`, the reload of c + 0x2000 the
   call clobbered).

   WHAT HOLDS AT 0x862ac (MFE_MID; the image-B m_file cut map section 5's prologue table and table C.1):
   - the side-stack frame (1, pos) is taken and owned by the journal, its header FB + 0 / 8 / 16 written, its 16
     shadow bytes 0xf1 x 4 / 0xf8 x 8 / 0xf3 x 4 (mf_core states only low.i's eight, MF_LOW_OFF), its flag pointer
     in FB + 120, and 120(s1) = FB: that is mf_core at MF_LOW_OFF;
   - the mconf block holds mfe_c0 v: the entry's model with c->reading = snprintf's text and gen NOT yet bumped
     (the bump is 0x862ac-0x862e4, in the second half);
   - the two frame cells the first half wrote and the second half reads: 64(s1) = &c->reading (0x862a0) and
     128(s1) = c + 0x2000 (0x8627c; 0x862ac reloads it into s6). 160(s1) = FB (0x861e8) is never read and is not
     stated; the cells 16 .. 56, 72 .. 112, 136, 144 are the set-up's (0x86300-0x86374), in the second half;
   - the text left at the head of the loop: mf_loop at line 0, p = t, rest = s, cur = None. (mf_loop's shadow
     conjuncts are over the CURRENT reader: the frame call and the wrapper may change the state, so they are
     retaken there, not carried from mf_cx.)
   - the registers 0x862ac keeps: mf_regs_ex (sp = s1, gp, tp, s0 = sp0, s1, s2 = SHADOW_OFF, s7 = FAKE,
     s8 = shadow(FB)) and s9 = c, s10 = t. s3, s4, s5 are set in the second half (0x86354, 0x86334, 0x86300);
     s6 holds the label pointer at the call and is dead (reloaded at 0x862ac).

   THE MODEL. SegModel.m_file mc s lab is the line loop from mfe_c1 (mf_file_lines): the entry's model with
   c->reading = snprintf_s 96 F_s [AS (label or "reac-pw.conf")] and gen + 1. mfe_c0 is the same with gen kept,
   which is what the block holds between the wrapper's return and the store 0x862e4. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* 0x862ac, the snprintf return: `ld s6,128(s1)` (0x862ac - 0x86140 = 0x16c) *)
Definition MFE_RET_SNP : Z := AF_m_file + 0x16c.
(* 0x862a8, the `jal` to the snprintf trampoline *)
Definition MFE_SNP : Z := AF_m_file + 0x168.

(* the %s argument of snprintf(c->reading, 96, "%s", label ? label : "reac-pw.conf") (0x86288-0x86290) *)
Definition mf_lab_text (lab : option (list Z)) : list Z := match lab with Some l => l | None => S_base end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the text snprintf leaves in c->reading *)
Definition mfe_reading (v : mfv) : list Z := snprintf_s 96 F_s [AS (mf_lab_text (mv_lab v))].
(* the block's model after the wrapper returned (gen not yet bumped), and after the bump *)
Definition mfe_c0 (v : mfv) : mconf :=
  MConf (mc_seg (mv_mc v)) (mc_overflow (mv_mc v)) (mc_refused (mv_mc v)) (mc_kept (mv_mc v))
        (mc_gen (mv_mc v)) (mfe_reading v).
Definition mfe_c1 (v : mfv) : mconf :=
  MConf (mc_seg (mv_mc v)) (mc_overflow (mv_mc v)) (mc_refused (mv_mc v)) (mc_kept (mv_mc v))
        (mc_gen (mv_mc v) + 1) (mfe_reading v).

(* SegModel.m_file is the line loop from mfe_c1, with no entry named yet *)
Lemma mf_file_lines : forall v, mf_final v = fst (m_lines (mfe_c1 v, None) 0 (lines (mv_s v))).
Proof. intros v. destruct v. reflexivity. Qed.
(* the empty text: the model is mfe_c1 itself (the tail's exit arm) *)
Lemma mf_file_nil : forall v, mv_s v = [] -> mf_final v = mfe_c1 v.
Proof. intros v H. rewrite mf_file_lines, H. reflexivity. Qed.
(* mfe_c0 and mfe_c1 keep every counter of the entry's model *)
Lemma mfe_c0_counters : forall v,
  mc_seg (mfe_c0 v) = mc_seg (mv_mc v) /\ mc_overflow (mfe_c0 v) = mc_overflow (mv_mc v) /\
  mc_refused (mfe_c0 v) = mc_refused (mv_mc v) /\ mc_kept (mfe_c0 v) = mc_kept (mv_mc v) /\
  mc_gen (mfe_c0 v) = mc_gen (mv_mc v) /\ mc_reading (mfe_c0 v) = mfe_reading v.
Proof. intros v. repeat split. Qed.
Lemma mfe_c1_of_c0 : forall v,
  mfe_c1 v = MConf (mc_seg (mfe_c0 v)) (mc_overflow (mfe_c0 v)) (mc_refused (mfe_c0 v)) (mc_kept (mfe_c0 v))
                   (mc_gen (mfe_c0 v) + 1) (mc_reading (mfe_c0 v)).
Proof. intros v. reflexivity. Qed.

Section e.
Variable B : asyms.

(* ===================== the cut inside S_MF_ENTRY: 0x862ac, the snprintf return ===================== *)
(* mf_core's eight low.i shadow bytes are 0xf8 (MF_LOW_OFF) from 0x86268 on; the other eight shadow bytes and the
   frame header are the journal's, not stated. *)
Definition MFE_MID (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
(memc : word -> option byte) (mdc : Model) (pos : Z) : Prop :=
mf_ls v lyc Sc /\
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF (mfe_c0 v) /\
mf_loop v Wc memc (mfe_c0 v) None 0 (mv_t v) (mv_s v) /\
mf_slot v memc Wc 64 (mv_c v + seg_spec.MC_READING) /\
mf_slot v memc Wc 128 (mv_c v + seg_spec.MC_N) /\
mf_regs_ex B v lyc pos regs1 /\
getr regs1 25 = w64 (mv_c v) /\ getr regs1 26 = w64 (mv_t v).

(* what mf_entry_2.v proves and mf_entry_1.v uses: the walk from 0x862ac realizes m_file's post *)
Definition MFE_MID_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos,
mf_cx B v -> sa_frm0 -> MFE_MID v lyc Sc Wc regs1 memc mdc pos ->
mf_at B v Wc regs1 memc mdc MFE_RET_SNP.

End e.
End f.
End d.

(* the cut at every FP state: the snprintf wrapper returns at its own (PaFx.v fxrel) *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
Section i.
Variable B : asyms.
Definition MFE_MID_F : Prop := forall fx0 : YK11.FPState, MFE_MID_stmt (fx := fx0) B.
End i.
End h.
End g.
