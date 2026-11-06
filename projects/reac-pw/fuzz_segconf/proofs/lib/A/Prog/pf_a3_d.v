(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 37 of its 62 lines of code are new or changed and 493 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A: the ONE mid-walk cut of segment A3 of reac_segconf_parse_file, at the
   return of the snprintf (0x87cec = BASE + PF_FRAME + 0x28), and the statement of the rest of the segment
   from it. Statement text only: nothing is proved here. Segment A3's proof, 2026-10-30.

   A3 runs FRAME 0x87cc4 -> HEAD 0x87ddc or DONE 0x88bb8. Its only two calls are the snprintf at 0x87ce8 and
   the checked memset at 0x87d4c. This file cuts the segment in two at the FIRST of them:
     pf_a3.v      proves FRAME -> 0x87cec (three instructions, one branch on the label, the call) and then
                  applies A3_RET1_stmt;
     pf_a3_w.v    proves A3_RET1_stmt: 0x87cec -> HEAD or DONE (check #1, c->gen++, the slots, cur_name's
                  two shadow cells, the memset, check #2, the loop constants).
   The cut is at the FP state the snprintf returned, so A3_RET1_stmt is stated at the ambient FP state of its
   own Section and pf_a3.v applies it at that state and lifts with PaFx.srr_apost_baseF_lift.

   a3_rd1 is c after the snprintf and BEFORE c->gen++: the reading field holds what snprintf left
   (snprintf_s 96 F_s [AS L] = firstn 95 L, pf_a3_f.a3f_reading), gen is still the entry's. One more
   instruction pair (0x87d00-0x87d14) makes it pf_pieces_spec.pf_start (p_rcs v) (p_lab v). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the listing offset of the snprintf's return, 0x87cec = 0x87cc4 + 0x24 + 4 *)
Definition PF_RET1 : Z := PF_FRAME + 0x28.
(* the memset's call site 0x87d4c and its return 0x87d50 *)
Definition PF_MSET : Z := PF_FRAME + 0x88.
Definition PF_RET2 : Z := PF_FRAME + 0x8c.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* the label the snprintf reads, and c right after it *)
Definition a3_LT (v : pfv) : list Z := match p_lab v with Some l => l | None => S_base end.
Definition a3_rd1 (v : pfv) : rconf :=
  RConf (rc_seg (p_rcs v)) (rc_refusal (p_rcs v)) (rc_refused (p_rcs v)) (rc_overflow (p_rcs v))
        (firstn 95 (a3_LT v)) (rc_gen (p_rcs v)).

(* THE CUT at 0x87cec. Everything pf_pieces.v's INV_FRAME carries, with c's reading field rewritten and the
   registers the snprintf did not clobber (x1 and x10..x17 are caller-saved and are not named). *)
Definition a3_ret1 (v : pfv) (pos : Z) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) : Prop :=
  pf_cx B v /\
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc Wc memc mdc 0 /\
  (exists f, Sc = set_fs f (p_S v)) /\
  Permutation (ablocks B (p_ly v) Sc) (ablocks B (p_ly v) (p_S v)) /\
  pf_saved (rdW Wc memc) (pf_sp0 v) (p_regs v) /\
  rdword (rdW Wc memc) (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) /\
  sa_frm0 /\
  pf_rg rX [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (22, SHADOW_OFF);
            (23, pf_F v pos); (24, p_c v); (25, p_t v); (26, p_c v + seg_spec.RC_GEN);
            (27, pf_SH v pos); (21, p_c v + seg_spec.RC_READING)] /\
  pf_obj B v (p_ly v) Sc (rdW Wc memc) /\
  sa_rconf (rdW Wc memc) (p_c v) (a3_rd1 v) /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x88, pf_F v pos); (0x98, pf_SH v pos + 8)] /\
  pf_fsh (rdW Wc memc) (pf_SH v pos) PF_SC0.

(* the rest of the segment, from that cut *)
Definition A3_RET1_stmt : Prop :=
  (forall n, HA_HEAD B n) -> HA_DONE B ->
  forall v pos Sc (Wc : world SEGS) rX memc mdc,
  a3_ret1 v pos Sc Wc rX memc mdc ->
  SRr SEGS Wc (mkCfg (mkst rX (Z_to_bv 64 (BASE + PF_RET1)) memc (seg_rom SEGS)) mdc) (PF_POST B v).

End e.
End f.
End d.
