(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YN0j.v, with its module paths and module names changed; 546 of its 584 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC.v, with its module names and addresses changed; 1881 of its 1980 lines of code are new or changed and 485 lines of the source are left out. *)
(* check_round_trip 0x81a9c (fuzz_state.c:278-314 with round_trip_document fs.c:229-264 inlined), fs.asan (image
   tfibsegs, the pinned fuzz_state.asan sha256 64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0): the ASan
   walk of FSH_Fn_crt.v check_round_trip_spec, lane B2 = segments 14-19, from the return of the second pj_object at
   0x82128 (0x8212c, crt_INV_8212c, lane B1's boundary) to the return of the third pj_set at 0x821a8 (0x821ac,
   FSH_crt_base.crt_INV_821ac), with the class-3 fake frame live (own = [(3, pos)]).
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from a working branch
   d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_sd4.v .. check_round_trip_sd9.v (the steps
   st4 .. st9 over the stage cuts St4 .. St9 of check_round_trip_stdefs.v :315-373) and check_round_trip_sdglue.v
   crt_cr_call :798 (the carried invariant across a callee)). The function-level line, with the full reuse search
   (index v5 built 2026-10-29T01:50:18Z; Require closure of the hit 334 files, 0 Admitted / Axiom / Parameter) and the
   checker verdict CONFIRM (a Theorem Labs lane, role check, 2026-10-29 04:3xZ), is lines 6-21 of the lane head
   (internal path).
   What is ported and how: d25a984c903's st4 .. st9 each run one callee (pj_string / pj_set through its a_call
   contract), the store-free stretch after it (check_round_trip_runs.v crt_set1 ..), and re-establish the carried
   invariant CR through crt_cr_call. Their a_call_pre / a_call_post statement is not importable, so the same steps are
   restated on the S0 forms: the callee's fpreU at the call site with crt's frame record pushed on the chain (the role
   of crt_cr_call's `pre ACRT_K ...` and window premises), the stack room, the argument registers read
   off the engine's call-site state, the FP relation of the after-call (FSW_K3.fsw_fp_sub) and the frame's flag word
   outside the callee's footprint (FSH_crt_base.crt_after_call's premises), and pj_set's `rd_sum Dold0 <= live` from
   the exact live equation (a Theorem Labs lane's restated pj_set_spec, a working branch 29d0157ef3d,
   FSH_Fn_reader.v:532). The three FP-cover obligations crt_pjset_fp_ok_150 / _17c / _1a8 are taken by path from
   a working branch ba97feda29a lib/A/FSH_crt_segB.v:65-119 (with the frame offsets they name).

   The six segments (MEASURED, capstone 5.0.7 over the pinned fs.asan):
     14  0x8212c..0x82138  pj_string (v = s6 = F + 0xe0, "org.openmixer.preset/2" 0x20ea0)   no branch (pj_object
                           returns void)
     15  0x8213c..0x82150  `bnez a0` to 0x824b8; pj_set (doc = s10 = F + 0x20, "format" 0x20ee0, v)
     16  0x82154..0x82164  `bnez a0` to 0x824b8; pj_string (v, "state" 0x20f00)
     17  0x82168..0x8217c  `bnez a0` to 0x824b8; pj_set (doc, "carries" 0x20f20, v)
     18  0x82180..0x82190  `bnez a0` to 0x824b8; pj_string (v, "base64" 0x20f40)
     19  0x82194..0x821a8  `bnez a0` to 0x824b8; pj_set (state = s7 = F + 0x80, "encoding" 0x20f60, v)
   F = frame_addr lyc 3 pos, the class-3 fake frame (fs_frame_bytes 3 = 512): doc [0x20, 0x58), state [0x80, 0xb8),
   v [0xe0, 0x118), back [0x140, 0x178), the two size_t at 0x1a0 and 0x1c0. A new file: no licence lines
   (internal). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSH_Fn_reader FSH_Fn_writer
FSH_Fn_crt FSW_crt_tbl FSW_rres FSW_frame FSW_frame3 FSW_strkit FSW_rd FSH_crt_base FSH_crt_site FSH_crt_room.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AE2k AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjStruct ReaderRes WriterSpec WriterSpecFacts pj_set_c
  check_round_trip_runs check_round_trip_st8 check_round_trip_stages_b WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the FP-cover obligations of the three pj_set sites, BY PATH from a working branch
   ba97feda29a lib/A/FSH_crt_segB.v:65-119 (text unchanged) ================= *)
(* ================= the class-3 frame's objects (offsets from F, MEASURED 0x81f80-0x81fa0) ================= *)
Definition crtB_DOC : Z := 0x20.
Definition crtB_STATE : Z := 0x80.
Definition crtB_V : Z := 0xe0.
Definition crtB_BACK : Z := 0x140.
Definition crtB_N0 : Z := 0x1a0.
Definition crtB_LENP : Z := 0x1c0.


Section fp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* ---- the FP of a pj_set call from check_round_trip, against crt's class-3 frame ----
   pj_set_spec's footprint at obj o and val w is [(o + 24, o + 56); (w, w + 56)] ++ ablocks_fp (rd_hblocks Dold0) ++
   FS_PSTAT_FP (FSH_Fn_reader.v pj_set_spec). ajournal's frame clause (YCbq.v ajournal) keeps every byte of a live frame
   AND of its shadow that is not in the callee's FP. crt_pjset_fp_at names the conjunct a call site must prove: inside
   crt's frame [F, F + 512) and its shadow [shadow_addr F, shadow_addr F + 64) that FP covers ONLY obj's bytes [24, 56)
   and val's 56 bytes, and both object ranges are frame bytes, i.e. the own-frame arm `in_frames ly [(3, pos)]` of the
   after-call FP relation. The proof is the base's FSH_crt_base.crt_pjset_fp_gen (one copy for the six sites). *)
Definition crt_pjset_fp_at (ly : alayout) (pos : Z) (Dold0 : list (Z * Z)) (oo ow : Z) : Prop :=
  let F := frame_addr ly 3 pos in
  (forall a, inFP ([(F + oo + 24, F + oo + 56); (F + ow, F + ow + 56)] ++ ablocks_fp (rd_hblocks Dold0) ++ FS_PSTAT_FP) a ->
     in_zr a (frame_rng ly (3, pos)) \/ in_zr a (shadow_addr F, fs_frame_bytes 3 / 8) ->
     F + oo + 24 <= a < F + oo + 56 \/ F + ow <= a < F + ow + 56) /\
  (forall a, F + oo + 24 <= a < F + oo + 56 \/ F + ow <= a < F + ow + 56 -> in_frames ly [(3, pos)] a).


(* the three pj_set sites of this group: obj = doc (s10) twice, then state (s7); val = v (s6) each time *)
Lemma crt_pjset_fp_ok_150 : forall ly S W mem md pos Dold0,
  AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
  (forall bk, In bk (rd_hblocks Dold0) -> In bk (ablocks B ly S)) ->
  crt_pjset_fp_at ly pos Dold0 crtB_DOC crtB_V.
Proof.
intros ly S W mem md pos Dold0 HAR Hin Hblk.
exact (crt_pjset_fp_gen B ly S W mem md pos Dold0 crtB_DOC crtB_V HAR Hin Hblk
  ltac:(unfold crtB_DOC; lia) ltac:(unfold crtB_DOC; lia) ltac:(unfold crtB_V; lia) ltac:(unfold crtB_V; lia)).
Qed.
Lemma crt_pjset_fp_ok_17c : forall ly S W mem md pos Dold0,
  AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
  (forall bk, In bk (rd_hblocks Dold0) -> In bk (ablocks B ly S)) ->
  crt_pjset_fp_at ly pos Dold0 crtB_DOC crtB_V.
Proof.
intros ly S W mem md pos Dold0 HAR Hin Hblk.
exact (crt_pjset_fp_gen B ly S W mem md pos Dold0 crtB_DOC crtB_V HAR Hin Hblk
  ltac:(unfold crtB_DOC; lia) ltac:(unfold crtB_DOC; lia) ltac:(unfold crtB_V; lia) ltac:(unfold crtB_V; lia)).
Qed.
Lemma crt_pjset_fp_ok_1a8 : forall ly S W mem md pos Dold0,
  AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
  (forall bk, In bk (rd_hblocks Dold0) -> In bk (ablocks B ly S)) ->
  crt_pjset_fp_at ly pos Dold0 crtB_STATE crtB_V.
Proof.
intros ly S W mem md pos Dold0 HAR Hin Hblk.
exact (crt_pjset_fp_gen B ly S W mem md pos Dold0 crtB_STATE crtB_V HAR Hin Hblk
  ltac:(unfold crtB_STATE; lia) ltac:(unfold crtB_STATE; lia) ltac:(unfold crtB_V; lia) ltac:(unfold crtB_V; lia)).
Qed.
End fp.

(* ================= the six store-free runs of lane B2 =================
   Every segment starts at a return address with FSH_crt_site.crt_ss2 (the boundary state without the frame's two
   regions) and runs to its call; from 0x8213c on it first stops at `bnez a0` (the previous pj_* call's answer, to the
   abort tail 0x824b8), decided by the boundary invariant's a0 = 0 inside crt_seg_call_br. The states and the runs are
   MEASURED by the engine over the lane's decode table (lib/A/FSW_crt_tbl.v) on the pinned fs.asan; each lemma is a
   closed equation closed by vm_compute. crt_site / crt_csite / crt_ssave and the argument registers are read off the
   computed states. ---- *)
(* seg 14: 0x8212c -> 0x83be4 pj_string (&v, "org.openmixer.preset/2" 0x20ea0), return 0x8213c *)
Definition crtB2_c14 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x83be4 (crt_ss2 0x8212c)).
Lemma crtB2_run14 : sym_run_toN tfibsegs crt_tbl FUEL 0x83be4 (crt_ss2 0x8212c) = (crtB2_c14, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtB2_cs14 : crt_csite crtB2_c14 0x83be4 0x8213c /\ crt_ssave crtB2_c14 /\
  sr_get (ss_regs crtB2_c14) 10%bv = SOff 22 0 /\ sr_get (ss_regs crtB2_c14) 11%bv = SLit 0x20ea0.
Proof.
split; [unfold crt_csite; repeat split; vm_compute; reflexivity|].
split; [apply crt_ssave_dec; vm_compute; reflexivity|]. split; vm_compute; reflexivity.
Qed.
(* seg 15: 0x8213c `bnez a0`, -> 0x838e8 pj_set (&doc, "format" 0x20ee0, &v), return 0x82154 *)
Definition crtB2_b15 : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x8213c)).
Lemma crtB2_br15 : sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x8213c) =
  (crtB2_b15, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtB2_c15 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x838e8 (add_cond crtB2_b15 crt_c0)).
Lemma crtB2_run15 : sym_run_toN tfibsegs crt_tbl FUEL 0x838e8 (add_cond crtB2_b15 crt_c0) = (crtB2_c15, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtB2_cs15 : crt_site crtB2_b15 crtB2_c15 0x838e8 0x82154 /\ crt_ssave crtB2_c15 /\
  sr_get (ss_regs crtB2_c15) 10%bv = SOff 26 0 /\ sr_get (ss_regs crtB2_c15) 11%bv = SLit 0x20ee0 /\
  sr_get (ss_regs crtB2_c15) 12%bv = SOff 22 0.
Proof.
split; [unfold crt_site, crt_csite; repeat split; vm_compute; reflexivity|].
split; [apply crt_ssave_dec; vm_compute; reflexivity|]. repeat split; vm_compute; reflexivity.
Qed.
(* seg 16: 0x82154 `bnez a0`, -> 0x83be4 pj_string (&v, "state" 0x20f00), return 0x82168 *)
Definition crtB2_b16 : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82154)).
Lemma crtB2_br16 : sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82154) =
  (crtB2_b16, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtB2_c16 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x83be4 (add_cond crtB2_b16 crt_c0)).
Lemma crtB2_run16 : sym_run_toN tfibsegs crt_tbl FUEL 0x83be4 (add_cond crtB2_b16 crt_c0) = (crtB2_c16, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtB2_cs16 : crt_site crtB2_b16 crtB2_c16 0x83be4 0x82168 /\ crt_ssave crtB2_c16 /\
  sr_get (ss_regs crtB2_c16) 10%bv = SOff 22 0 /\ sr_get (ss_regs crtB2_c16) 11%bv = SLit 0x20f00.
Proof.
split; [unfold crt_site, crt_csite; repeat split; vm_compute; reflexivity|].
split; [apply crt_ssave_dec; vm_compute; reflexivity|]. split; vm_compute; reflexivity.
Qed.
(* seg 17: 0x82168 `bnez a0`, -> 0x838e8 pj_set (&doc, "carries" 0x20f20, &v), return 0x82180 *)
Definition crtB2_b17 : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82168)).
Lemma crtB2_br17 : sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82168) =
  (crtB2_b17, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtB2_c17 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x838e8 (add_cond crtB2_b17 crt_c0)).
Lemma crtB2_run17 : sym_run_toN tfibsegs crt_tbl FUEL 0x838e8 (add_cond crtB2_b17 crt_c0) = (crtB2_c17, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtB2_cs17 : crt_site crtB2_b17 crtB2_c17 0x838e8 0x82180 /\ crt_ssave crtB2_c17 /\
  sr_get (ss_regs crtB2_c17) 10%bv = SOff 26 0 /\ sr_get (ss_regs crtB2_c17) 11%bv = SLit 0x20f20 /\
  sr_get (ss_regs crtB2_c17) 12%bv = SOff 22 0.
Proof.
split; [unfold crt_site, crt_csite; repeat split; vm_compute; reflexivity|].
split; [apply crt_ssave_dec; vm_compute; reflexivity|]. repeat split; vm_compute; reflexivity.
Qed.
(* seg 18: 0x82180 `bnez a0`, -> 0x83be4 pj_string (&v, "base64" 0x20f40), return 0x82194 *)
Definition crtB2_b18 : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82180)).
Lemma crtB2_br18 : sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82180) =
  (crtB2_b18, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtB2_c18 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x83be4 (add_cond crtB2_b18 crt_c0)).
Lemma crtB2_run18 : sym_run_toN tfibsegs crt_tbl FUEL 0x83be4 (add_cond crtB2_b18 crt_c0) = (crtB2_c18, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtB2_cs18 : crt_site crtB2_b18 crtB2_c18 0x83be4 0x82194 /\ crt_ssave crtB2_c18 /\
  sr_get (ss_regs crtB2_c18) 10%bv = SOff 22 0 /\ sr_get (ss_regs crtB2_c18) 11%bv = SLit 0x20f40.
Proof.
split; [unfold crt_site, crt_csite; repeat split; vm_compute; reflexivity|].
split; [apply crt_ssave_dec; vm_compute; reflexivity|]. split; vm_compute; reflexivity.
Qed.
(* seg 19: 0x82194 `bnez a0`, -> 0x838e8 pj_set (&state, "encoding" 0x20f60, &v), return 0x821ac *)
Definition crtB2_b19 : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82194)).
Lemma crtB2_br19 : sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82194) =
  (crtB2_b19, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtB2_c19 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x838e8 (add_cond crtB2_b19 crt_c0)).
Lemma crtB2_run19 : sym_run_toN tfibsegs crt_tbl FUEL 0x838e8 (add_cond crtB2_b19 crt_c0) = (crtB2_c19, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtB2_cs19 : crt_site crtB2_b19 crtB2_c19 0x838e8 0x821ac /\ crt_ssave crtB2_c19 /\
  sr_get (ss_regs crtB2_c19) 10%bv = SOff 23 0 /\ sr_get (ss_regs crtB2_c19) 11%bv = SLit 0x20f60 /\
  sr_get (ss_regs crtB2_c19) 12%bv = SOff 22 0.
Proof.
split; [unfold crt_site, crt_csite; repeat split; vm_compute; reflexivity|].
split; [apply crt_ssave_dec; vm_compute; reflexivity|]. repeat split; vm_compute; reflexivity.
Qed.

(* ================= the FP relation of each call (FSW_K3.fsw_fp_sub, the after-call's five arms) =================
   pj_string's footprint is v's 56 bytes (an object of crt's class-3 frame: the own-frame arm) and fs's statics (the
   static arm: FS_PSTAT_FP is crt's own FP and image bytes, FSH_crt_base.crt_pstat_img); pj_set's adds obj's [24, 56)
   (own frame) and the old kids / keys blocks grow may free (the temporary-block arm: blocks the walk itself allocated,
   not crt's entry blocks - a fact the boundary invariant carries, a premise here). *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma crtB2_fpsub_static : forall ly S lyc Sc own, fsw_fp_sub B ly S lyc Sc own FS_PSTAT_FP FS_PSTAT_FP.
Proof. intros ly S lyc Sc own a Ha. right; right; left. split; [exact Ha | exact (crt_pstat_img a Ha)]. Qed.
(* pj_string at v = F + off *)
Lemma crtB2_fpsub_obj : forall ly S lyc Sc pos off,
  0 <= off -> off + 56 <= 512 ->
  fsw_fp_sub B ly S lyc Sc [(3, pos)] FS_PSTAT_FP
    ([(frame_addr lyc 3 pos + off, frame_addr lyc 3 pos + off + 56)] ++ FS_PSTAT_FP).
Proof.
intros ly S lyc Sc pos off H0 H1 a Ha. apply inFP_app in Ha as [Ha | Ha].
- right; right; right; left. apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
  exists 3, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite crt_frame3. lia.
- exact (crtB2_fpsub_static ly S lyc Sc [(3, pos)] a Ha).
Qed.
(* pj_set at obj F + oo, val F + ow: the two object ranges, the old blocks grow may free, the statics *)
Lemma crtB2_fpsub_pjset : forall ly S lyc Sc pos oo ow Dold0,
  0 <= oo -> oo + 56 <= 512 -> 0 <= ow -> ow + 56 <= 512 ->
  (forall bk, In bk (rd_hblocks Dold0) -> In bk (ablocks B lyc Sc) /\ ~ In bk (ablocks B ly S)) ->
  fsw_fp_sub B ly S lyc Sc [(3, pos)] FS_PSTAT_FP
    ([(frame_addr lyc 3 pos + oo + 24, frame_addr lyc 3 pos + oo + 56);
      (frame_addr lyc 3 pos + ow, frame_addr lyc 3 pos + ow + 56)] ++ ablocks_fp (rd_hblocks Dold0) ++ FS_PSTAT_FP).
Proof.
intros ly S lyc Sc pos oo ow Dold0 H0 H1 H2 H3 Hblk a Ha. apply inFP_app in Ha as [Ha | Ha].
- right; right; right; left. exists 3, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  rewrite crt_frame3.
  apply inFP_cons in Ha as [Ha | Ha]; [lia|].
  apply inFP_cons in Ha as [Ha | Ha]; [lia | exfalso; exact (inFP_nil a Ha)].
- apply inFP_app in Ha as [Ha | Ha].
  + right; left. destruct Ha as (r & Hr & Hra). unfold ablocks_fp in Hr.
    apply in_map_iff in Hr as ([b n] & <- & Hbn). cbn [fst snd] in Hra.
    destruct (Hblk _ Hbn) as (Hc & Hn0). exists b, n. split; [exact Hc|]. split; [exact Hn0 | exact Hra].
  + exact (crtB2_fpsub_static ly S lyc Sc [(3, pos)] a Ha).
Qed.
End f.

(* ---- the frame's tail is outside every callee footprint of the lane ----
   crt_after_call asks that no byte of csF's chunks and none of the flag word [F + 504, F + 512) is in the callee's FP.
   Every FP of lane B2 lies below F + 0x118 inside the frame (doc, state, v end there), or in a heap block (apart from
   the frame, YCbq.sep_block_frame), or in fs's statics (image bytes, which no frame holds, YCbq.frm_img). *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Lemma crtB2_tail_free : forall lyc Sc (W : world tfibsegs) mem md pos FPc,
  AR tfibsegs B lyc Sc W mem md -> In (3, pos) (frames Sc) ->
  (forall a, inFP FPc a -> a < frame_addr lyc 3 pos + 0x118 \/
     (exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/ inFP FS_PSTAT_FP a) ->
  forall a, frame_addr lyc 3 pos + 0x118 <= a < frame_addr lyc 3 pos + 512 -> ~ inFP FPc a.
Proof.
intros lyc Sc W mem md pos FPc HAR Hin HFP a Ha Hf.
destruct (HFP a Hf) as [Hlt | [(b & n & Hbn & Hr) | Hp]]; [lia| |].
- pose proof (sep_block_frame tfibsegs B LAWS lyc Sc W mem md b n 3 pos HAR Hbn Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite crt_frame3 in Hd. lia.
- exact (frm_img tfibsegs B LAWS lyc Sc W mem md 3 pos a HAR Hin ltac:(rewrite crt_frame3; lia) (crt_pstat_img a Hp)).
Qed.
End t.

(* ================= pj_set's `rd_sum Dold0 <= live` at the three sites (FSH_Fn_reader.v:549, Dold0 = kids_blk kids cap
   ++ keys_blk 6 keys cap) from the EXACT live equation the boundary invariants carry (FSH_crt_base.crt_INV_821ac's
   `live = c_live cx + enc_size len + dec_size tb2 + rd_sum (Ddoc ++ Dst)`; the inner invariants of this lane carry the
   same equation with v's blocks Dv appended), through FSH_crt_site.crt_dold0_le (this lane's text, moved there). *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the three sites, over the exact live equation (doc = F + 0x20 at 0x82150 and 0x8217c, state = F + 0x80 at 0x821a8;
   Dv = v's blocks, [] once pj_set has consumed v) *)
Lemma crt_pjset_dold0_150 : forall cx ly S (W : world tfibsegs) mem ms Ddoc Dst Dv num str kids keys n cap live,
  crt_base B cx ->
  rtree tfibsegs B ly S W mem (crt_F cx + 0x20) (PjTree.JObj ms) Ddoc ->
  rd_blocks_ok tfibsegs B ly S W mem (Dst ++ Dv) ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem) (crt_F cx + 0x20) 6 num str kids keys n cap ->
  live = c_live cx + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) +
    FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + rd_sum (Ddoc ++ Dst ++ Dv) ->
  rd_sum (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap) <= live.
Proof.
intros cx ly S W mem ms Ddoc Dst Dv num str kids keys n cap live HB HT HBo Hh ->.
pose proof (crt_live0 B cx HB) as H0.
assert (He : 0 <= FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))))
  by (unfold FSH_Fn_writer.enc_size; Z.div_mod_to_equations; lia).
assert (Hd : 0 <= FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)))
  by (unfold FSH_Fn_writer.dec_size; Z.div_mod_to_equations; lia).
exact (crt_dold0_le B ly S W mem _ ms Ddoc num str kids keys n cap _
  (c_live cx + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) +
   FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))) [] (Dst ++ Dv) HT Hh HBo ltac:(lia) eq_refl).
Qed.
Lemma crt_pjset_dold0_17c : forall cx ly S (W : world tfibsegs) mem ms Ddoc Dst Dv num str kids keys n cap live,
  crt_base B cx ->
  rtree tfibsegs B ly S W mem (crt_F cx + 0x20) (PjTree.JObj ms) Ddoc ->
  rd_blocks_ok tfibsegs B ly S W mem (Dst ++ Dv) ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem) (crt_F cx + 0x20) 6 num str kids keys n cap ->
  live = c_live cx + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) +
    FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + rd_sum (Ddoc ++ Dst ++ Dv) ->
  rd_sum (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap) <= live.
Proof. exact crt_pjset_dold0_150. Qed.
Lemma crt_pjset_dold0_1a8 : forall cx ly S (W : world tfibsegs) mem ms Ddoc Dst Dv num str kids keys n cap live,
  crt_base B cx ->
  rtree tfibsegs B ly S W mem (crt_F cx + 0x80) (PjTree.JObj ms) Dst ->
  rd_blocks_ok tfibsegs B ly S W mem (Ddoc ++ Dv) ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem) (crt_F cx + 0x80) 6 num str kids keys n cap ->
  live = c_live cx + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) +
    FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + rd_sum (Ddoc ++ Dst ++ Dv) ->
  rd_sum (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap) <= live.
Proof.
intros cx ly S W mem ms Ddoc Dst Dv num str kids keys n cap live HB HT HBo Hh ->.
pose proof (crt_live0 B cx HB) as H0.
assert (He : 0 <= FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))))
  by (unfold FSH_Fn_writer.enc_size; Z.div_mod_to_equations; lia).
assert (Hd : 0 <= FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)))
  by (unfold FSH_Fn_writer.dec_size; Z.div_mod_to_equations; lia).
exact (crt_dold0_le B ly S W mem _ ms Dst num str kids keys n cap _
  (c_live cx + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) +
   FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))) Ddoc Dv HT Hh HBo ltac:(lia) eq_refl).
Qed.
End r.

(* ================= the lane's inner boundaries 0x8213c / 0x82154 / 0x82168 / 0x82180 / 0x82194 =================
   One parametric invariant, the ASan twin of d25a984c903's crt_obj_stage (check_round_trip_stdefs.v St4 .. St9 :315-373:
   the document and state trees, v's node, the holdings, the counters), in the forms of FSH_crt_base.crt_INV_821ac.
   The document's and the state's blocks are carried BY SIZE (`Permutation (map snd D) sizes`): pj_set's post has no
   pj_hdr, and the header a later pj_set needs (its cap, hence the grow arm) is read back off pj_node's kids block
   (56 * cap is the only multiple of 56 among the sizes). v is: unknown (VAny, after the second pj_object), zero (VZero,
   after a pj_set consumed it) or a string node holding exactly |cs| + 1 bytes (VStr cs, after pj_string).
   Budgets: K / CNT / LIVE grow by each callee's own terms, in the order of FSH_crt_base.K_821ac / CNT_821ac /
   LIVE_821ac, from the after-pj_object values K_82068 + 1 (the second decode's one malloc), CNT_82068 + 1,
   LIVE_82068 + (dec_size es + HEAD). ---- *)
Inductive crtB2_vst : Type := VAny | VZero | VStr (cs : list Z).

Definition K_8213c (cx : crt_cx) : Z := K_82068 cx + 1 + EV_pj_string.
Definition K_82154 (cx : crt_cx) : Z := K_8213c cx + rd_ev (pj_set_c.set_trace 0 0 6).
Definition K_82168 (cx : crt_cx) : Z := K_82154 cx + EV_pj_string.
Definition K_82180 (cx : crt_cx) : Z := K_82168 cx + rd_ev (pj_set_c.set_trace 1 8 7).
Definition K_82194 (cx : crt_cx) : Z := K_82180 cx + EV_pj_string.
Definition CNT_8213c (cx : crt_cx) : Z := CNT_82068 cx + 1 + 1.
Definition CNT_82154 (cx : crt_cx) : Z := CNT_8213c cx + crt_trlen (pj_set_c.set_trace 0 0 6).
Definition CNT_82168 (cx : crt_cx) : Z := CNT_82154 cx + 1.
Definition CNT_82180 (cx : crt_cx) : Z := CNT_82168 cx + crt_trlen (pj_set_c.set_trace 1 8 7).
Definition CNT_82194 (cx : crt_cx) : Z := CNT_82180 cx + 1.
Definition LIVE_8213c (cx : crt_cx) : Z := LIVE_82068 cx + (FSH_Fn_writer.dec_size (crt_es cx) + HEAD) + (23 + HEAD).
Definition LIVE_82154 (cx : crt_cx) : Z := LIVE_8213c cx + rd_live (pj_set_c.set_trace 0 0 6).
Definition LIVE_82168 (cx : crt_cx) : Z := LIVE_82154 cx + (6 + HEAD).
Definition LIVE_82180 (cx : crt_cx) : Z := LIVE_82168 cx + rd_live (pj_set_c.set_trace 1 8 7).
Definition LIVE_82194 (cx : crt_cx) : Z := LIVE_82180 cx + (7 + HEAD).

Section inv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Definition crtB2_vfact (vs : crtB2_vst) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
  (v : Z) (Dv : list (Z * Z)) : Prop :=
  match vs with
  | VAny => Dv = []
  | VZero => Dv = [] /\ PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v
  | VStr cs => (exists av, Dv = [(av, Z.of_nat (length cs) + 1)]) /\ rtree tfibsegs B ly S W mem v (PjTree.JStr cs) Dv
  end.
Definition crtB2_inv (za : bool) (msd : list (list Z * PjTree.jv)) (sd : list Z)
  (mss : list (list Z * PjTree.jv)) (ss : list Z) (vs : crtB2_vst) (KX CNTX LIVEX : crt_cx -> Z) : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  (za = true -> ew E 10 = Z_to_bv 64 0) /\ ew E 18 = Z_to_bv 64 (c_text cx) /\ ew E 20 = Z_to_bv 64 len /\
  ew E 21 = Z_to_bv 64 (c_bd cx) /\ ew E 22 = Z_to_bv 64 (F + 0xe0) /\ ew E 23 = Z_to_bv 64 (F + 0x80) /\
  ew E 26 = Z_to_bv 64 (F + 0x20) /\ ew E 27 = Z_to_bv 64 (F + 0x1a0) /\
  (exists same nsame dec Ddoc Dst Dv live peak cnt,
     ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 dec /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (dec - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD)] ++ rd_hblocks (Ddoc ++ Dst ++ Dv)) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (dec - HEAD, HEAD)] ++ rd_heads (Ddoc ++ Dst ++ Dv)) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     zbytes_at tfibsegs W3 mem (c_text cx) (tb2 ++ [0]) /\ cstr_ok tfibsegs W3 mem (c_text cx) tb2 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem dec (FSH_Fn_writer.dec_size tb2) /\
     zbytes_at tfibsegs W3 mem dec (c_bs cx) /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x20) (PjTree.JObj msd) Ddoc /\ Permutation (map snd Ddoc) sd /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x80) (PjTree.JObj mss) Dst /\ Permutation (map snd Dst) ss /\
     crtB2_vfact vs ly3 S3 W3 mem (F + 0xe0) Dv /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0x20) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x80) /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0xe0) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x140) /\
     val_mem tfibsegs (mrestrict (w_H W3) mem) (F + 0x1a0) 8 0 /\
     range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (F + 0x1a0) 8 /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + rd_sum (Ddoc ++ Dst ++ Dv) /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVEX cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNTX cx /\ k <= KX cx).

(* the inner boundaries (returns of the first pj_string .. the second pj_string after the second pj_set) *)
Definition crt_INV_8213c : crt_inv :=
  crtB2_inv true [] [] [] [] (VStr check_round_trip_st8.CRT_FMT2) K_8213c CNT_8213c LIVE_8213c.
Definition crt_INV_82154 : crt_inv :=
  crtB2_inv true [(check_round_trip_st8.CRT_FORMAT, PjTree.JStr check_round_trip_st8.CRT_FMT2)]
    [56 * 8; 8 * 8; 7; 23] [] [] VZero K_82154 CNT_82154 LIVE_82154.
Definition crt_INV_82168 : crt_inv :=
  crtB2_inv true [(check_round_trip_st8.CRT_FORMAT, PjTree.JStr check_round_trip_st8.CRT_FMT2)]
    [56 * 8; 8 * 8; 7; 23] [] [] (VStr check_round_trip_runs.CRT_STATE) K_82168 CNT_82168 LIVE_82168.
Definition crt_INV_82180 : crt_inv :=
  crtB2_inv true check_round_trip_st8.crt_doc8 [56 * 8; 8 * 8; 7; 23; 8; 6] [] [] VZero K_82180 CNT_82180 LIVE_82180.
Definition crt_INV_82194 : crt_inv :=
  crtB2_inv true check_round_trip_st8.crt_doc8 [56 * 8; 8 * 8; 7; 23; 8; 6] [] []
    (VStr check_round_trip_stages_b.V_BASE64) K_82194 CNT_82194 LIVE_82194.
(* the state the last pj_set leaves, before it is read as FSH_crt_base.crt_INV_821ac *)
Definition crtB2_INV_821ac : crt_inv :=
  crtB2_inv true check_round_trip_st8.crt_doc8 [56 * 8; 8 * 8; 7; 23; 8; 6] check_round_trip_stages_b.crt_s1
    [56 * 8; 8 * 8; 9; 7] VZero K_821ac CNT_821ac LIVE_821ac.
End inv.

(* ================= what a pj_* call of the lane keeps (the role of d25a984c903's sdglue.v crt_keep_blk :612,
   crt_spared_blk :659 and crt_cr_call :798 across one callee) =================
   Every footprint of the lane is FR ++ ablocks_fp Dh ++ FS_PSTAT_FP: FR inside crt's class-3 frame (the objects the
   callee writes), Dh live heap blocks (pj_set's old kids / keys), and fs's statics. A byte of another live heap block,
   a frame byte outside FR, and every shadow byte are off it. *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Lemma crtB2_pstat_range : forall a, inFP FS_PSTAT_FP a -> 0x10000 <= a < FS_IMG_END.
Proof.
intros a (r & Hr & Hra). unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Hra; unfold FS_IMG_END; lia|]). destruct Hr.
Qed.
(* a byte of a live heap block other than those of Dh *)
Lemma crtB2_off_fp : forall lyc Sc (W : world tfibsegs) mem md pos FR Dh p n x,
  AR tfibsegs B lyc Sc W mem md -> In (3, pos) (frames Sc) ->
  (forall a, inFP FR a -> frame_addr lyc 3 pos <= a < frame_addr lyc 3 pos + 512) ->
  (forall bk, In bk Dh -> In bk (ablocks B lyc Sc)) ->
  In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) Dh -> p <= x < p + req_size n ->
  ~ inFP (FR ++ ablocks_fp Dh ++ FS_PSTAT_FP) x.
Proof.
intros lyc Sc W mem md pos FR Dh p n x HAR Hin HFR HDh Hpn Hnd Hx Hf.
apply inFP_app in Hf as [Hf|Hf].
- pose proof (HFR x Hf) as Hfr.
  pose proof (sep_block_frame tfibsegs B LAWS lyc Sc W mem md p n 3 pos HAR Hpn Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite crt_frame3 in Hd. lia.
- apply inFP_app in Hf as [Hf|Hf].
  + destruct Hf as (r & Hr & Hra). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b m] & <- & Hbm).
    cbn [fst snd] in Hra.
    assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hbm; exact (Hnd Hbm)).
    pose proof (sep_blocks tfibsegs B LAWS lyc Sc W mem md b m p n HAR (HDh _ Hbm) Hpn Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  + pose proof (fsw_ablock_off_img B lyc Sc W mem md p n HAR Hpn) as Ho.
    pose proof (crtB2_pstat_range x Hf) as Hs. lia.
Qed.
(* a byte of crt's frame outside FR *)
Lemma crtB2_frm_off_fp : forall lyc Sc (W : world tfibsegs) mem md pos FR Dh a,
  AR tfibsegs B lyc Sc W mem md -> In (3, pos) (frames Sc) ->
  (forall bk, In bk Dh -> In bk (ablocks B lyc Sc)) ->
  frame_addr lyc 3 pos <= a < frame_addr lyc 3 pos + 512 -> ~ inFP FR a ->
  ~ inFP (FR ++ ablocks_fp Dh ++ FS_PSTAT_FP) a.
Proof.
intros lyc Sc W mem md pos FR Dh a HAR Hin HDh Ha HnFR Hf.
apply inFP_app in Hf as [Hf|Hf]; [exact (HnFR Hf)|].
apply inFP_app in Hf as [Hf|Hf].
- destruct Hf as (r & Hr & Hra). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b m] & <- & Hbm).
  cbn [fst snd] in Hra.
  pose proof (sep_block_frame tfibsegs B LAWS lyc Sc W mem md b m 3 pos HAR (HDh _ Hbm) Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite crt_frame3 in Hd. lia.
- exact (frm_img tfibsegs B LAWS lyc Sc W mem md 3 pos a HAR Hin ltac:(rewrite crt_frame3; lia) (crt_pstat_img a Hf)).
Qed.
(* no byte of such a footprint is a shadow byte *)
Lemma crtB2_fp_noshadow : forall lyc Sc (W : world tfibsegs) mem md pos FR Dh a,
  AR tfibsegs B lyc Sc W mem md -> In (3, pos) (frames Sc) ->
  (forall a, inFP FR a -> frame_addr lyc 3 pos <= a < frame_addr lyc 3 pos + 512) ->
  (forall bk, In bk Dh -> In bk (ablocks B lyc Sc)) ->
  inFP (FR ++ ablocks_fp Dh ++ FS_PSTAT_FP) a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44).
Proof.
intros lyc Sc W mem md pos FR Dh a HAR Hin HFR HDh Hf.
apply inFP_app in Hf as [Hf|Hf].
- destruct (frames_bounds tfibsegs B LAWS lyc Sc W mem md 3 pos HAR Hin) as (_ & _ & Happ).
  pose proof (HFR a Hf) as Hr. rewrite crt_frame3 in Happ.
  pose proof (in_app_addr _ _ a Happ Hr) as AP.
  unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in AP |- *. lia.
- apply inFP_app in Hf as [Hf|Hf].
  + destruct Hf as (r & Hr & Hra). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b m] & <- & Hbm).
    cbn [fst snd] in Hra.
    exact (fsw_ablock_off_shadow B lyc Sc W mem md b m HAR (HDh _ Hbm) a Hra).
  + pose proof (crtB2_pstat_range a Hf) as Hs. unfold FS_IMG_END, SHADOW_OFF in *. lia.
Qed.
(* a byte kept by the callee's journal, read through mbyte (the raw memories) *)
Lemma crtB2_mbyte_kept : forall STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc x,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  ((exists p n, In (p, n) (ablocks B lyc Sc) /\ p <= x < p + req_size n) \/
   (exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid)) ->
  ~ inFP FP1 x ->
  mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W) memc) x.
Proof.
intros STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc x HJ HU HO' HP' Hx Hf.
unfold mbyte. rewrite (proj2 (fsw_journal_kept_byte B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc x
  HJ HU HO' HP' Hx Hf)). reflexivity.
Qed.
End h.

(* ---- each fact of crtB2_inv that a call of the lane does not change, carried across its journal (callee state
   lyc Sc Uc W memc mdc -> ly' S' U' W' mem' md', footprint FR ++ ablocks_fp Dh ++ FS_PSTAT_FP) ---- *)
Section h2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Section c. 
Variables (STK1 sp1 kc pos : Z) (FR Dh : list (Z * Z)) (lyc : alayout) (Sc : astate) (Uc : list (Z * Z))
  (W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (ly' : alayout) (S' : astate) (U' : list (Z * Z))
  (W' : world tfibsegs) (mem' : word -> option byte) (md' : Model).
Hypothesis HJ : ajournal tfibsegs B STK1 sp1 (FR ++ ablocks_fp Dh ++ FS_PSTAT_FP) lyc Sc W (unpoison Uc memc) mdc []
  ly' S' W' (unpoison U' mem') md' kc.
Hypothesis HU : ARU tfibsegs B lyc Sc Uc W memc mdc.
Hypothesis HO' : upoison_ok B ly' S' U'.
Hypothesis HP' : upoisoned tfibsegs W' mem' U'.
Hypothesis Hin3 : In (3, pos) (frames Sc).
Hypothesis HFR : forall a, inFP FR a -> frame_addr lyc 3 pos <= a < frame_addr lyc 3 pos + 512.
Hypothesis HDh : forall bk, In bk Dh -> In bk (ablocks B lyc Sc).
Let FP := FR ++ ablocks_fp Dh ++ FS_PSTAT_FP.
Let HAR : AR tfibsegs B lyc Sc W (unpoison Uc memc) mdc := ARU_AR tfibsegs B _ _ _ _ _ _ HU.

Lemma crtB2_blk_off : forall p n x, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) Dh -> p <= x < p + req_size n ->
  ~ inFP FP x.
Proof. intros p n x H1 H2 H3. exact (crtB2_off_fp B lyc Sc W _ mdc pos FR Dh p n x HAR Hin3 HFR HDh H1 H2 H3). Qed.
Lemma crtB2_frm_off : forall a, frame_addr lyc 3 pos <= a < frame_addr lyc 3 pos + 512 -> ~ inFP FR a -> ~ inFP FP a.
Proof. intros a H1 H2. exact (crtB2_frm_off_fp B lyc Sc W _ mdc pos FR Dh a HAR Hin3 HDh H1 H2). Qed.
(* a live block survives the call when one of its bytes is off the footprint *)
Lemma crtB2_blk_live : forall p n, 0 < n -> In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) Dh ->
  In (p, n) (ablocks B ly' S').
Proof.
intros p n Hn H1 H2.
assert (Hr : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
apply (fsw_journal_block_live B STK1 sp1 FP lyc Sc W (unpoison Uc memc) mdc ly' S' W' (unpoison U' mem') md' kc p n p
  HJ H1); [lia|].
apply (crtB2_blk_off p n p H1 H2). lia.
Qed.
(* a reader block of crt (text, dec) *)
Lemma crtB2_rblock_kept : forall p k, fs_rblock tfibsegs B lyc Sc W memc p k -> ~ In (p - HEAD, k + HEAD) Dh ->
  fs_rblock tfibsegs B ly' S' W' mem' p k.
Proof.
intros p k Hb Hnd. pose proof Hb as (Hin & _ & Hk & _).
apply (fs_rblock_kept_call B STK1 sp1 FP lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc p k HJ HU HO' HP'); [|exact Hb].
intros x Hx. apply (crtB2_blk_off (p - HEAD) (k + HEAD) x Hin Hnd).
pose proof (req_size_pos (k + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr). unfold HEAD in *. lia.
Qed.
(* bytes inside a block live at both ends *)
Lemma crtB2_zbytes_kept : forall p (l : list Z) b m, In (b, m) (ablocks B lyc Sc) -> ~ In (b, m) Dh ->
  b <= p -> p + Z.of_nat (length l) <= b + req_size m ->
  zbytes_at tfibsegs W memc p l -> zbytes_at tfibsegs W' mem' p l.
Proof.
intros p l b m Hin Hnd Hb Hbm Hz. unfold zbytes_at in *.
apply (garr8_frame tfibsegs _ _ p l Hz). intros a Ha.
apply (crtB2_mbyte_kept SK B STK1 sp1 FP lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc a HJ HU HO' HP');
  [left; exists b, m; split; [exact Hin | lia] | apply (crtB2_blk_off b m a Hin Hnd); lia].
Qed.
(* a C string inside a block live at both ends (FSW_strkit.cstr_ok_kept_blkU: the tail word is re-read off AR) *)
Lemma crtB2_cstr_kept : forall p (l : list Z) b m, In (b, m) (ablocks B lyc Sc) -> ~ In (b, m) Dh ->
  b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  (forall r, In r U' -> In r Uc \/ fst r + snd r <= p \/ p + Z.of_nat (length l) + 1 <= fst r) ->
  cstr_ok tfibsegs W memc p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros p l b m Hin Hnd Hb Hbm HU' Hc.
assert (Hm : 0 < m) by lia.
pose proof (crtB2_blk_live b m Hm Hin Hnd) as Hin'.
apply (FSW_strkit.cstr_ok_kept_blkU B STK1 sp1 FP lyc Sc Uc W memc mdc [] ly' S' U' W' mem' md' kc p l b m
  HU HJ HO' HP' Hin Hin' Hb Hbm); [|exact HU' | exact Hc].
intros a Ha. apply (crtB2_blk_off b m a Hin Hnd).
assert (Hr : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
Qed.
(* a tree whose node is a frame object outside FR and whose blocks are not Dh's *)
Lemma crtB2_rtree_kept : forall v t D, frame_addr lyc 3 pos <= v -> v + 56 <= frame_addr lyc 3 pos + 512 ->
  (forall x, v <= x < v + 56 -> ~ inFP FR x) -> (forall bk, In bk (rd_hblocks D) -> ~ In bk Dh) ->
  pobj tfibsegs B lyc Sc W memc v -> rtree tfibsegs B lyc Sc W memc v t D -> rtree tfibsegs B ly' S' W' mem' v t D.
Proof.
intros v t D Hv0 Hv1 HvFR HDD HPv HT.
apply (rtree_kept_call B STK1 sp1 FP lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc v t D HJ HU HO' HP');
  [| | exact HPv | exact HT].
- intros x Hx. apply crtB2_frm_off; [lia | exact (HvFR x Hx)].
- intros a k x Hak Hx. pose proof HT as (_ & HBk & _). destruct (HBk a k Hak) as (Hin & _ & Hk & _).
  apply (crtB2_blk_off (a - HEAD) (k + HEAD) x Hin).
  + apply HDD. unfold rd_hblocks. apply in_map_iff. exists (a, k). split; [reflexivity | exact Hak].
  + pose proof (req_size_pos (k + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr). unfold HEAD in *. lia.
Qed.
(* a frame object outside FR stays a placed object *)
Lemma crtB2_pobj_kept : forall v, frame_addr lyc 3 pos <= v -> v + 56 <= frame_addr lyc 3 pos + 512 ->
  (forall x, v <= x < v + 56 -> ~ inFP FR x) -> FSupoisonU.fs_heads B ly' S' U' ->
  pobj tfibsegs B lyc Sc W memc v -> pobj tfibsegs B ly' S' W' mem' v.
Proof.
intros v Hv0 Hv1 HvFR HH HPv.
apply (pobj_kept_call B STK1 sp1 FP lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc v HJ HU HO' HP');
  [| | exact HH | exact HPv].
- intros x Hx. apply crtB2_frm_off; [lia | exact (HvFR x Hx)].
- intros a Ha. exact (crtB2_fp_noshadow B lyc Sc W _ mdc pos FR Dh a HAR Hin3 HFR HDh Ha).
Qed.
(* the size_t cell n0 at F + 0x1a0 (value and shadow), outside FR *)
Lemma crtB2_n0_kept : forall n0, frame_addr lyc 3 pos mod 32 = 0 ->
  n0 = frame_addr lyc 3 pos + 0x1a0 -> (forall x, n0 <= x < n0 + 8 -> ~ inFP FR x) ->
  ARU tfibsegs B ly' S' U' W' mem' md' ->
  val_mem tfibsegs (mrestrict (w_H W) memc) n0 8 0 ->
  range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF n0 8 ->
  val_mem tfibsegs (mrestrict (w_H W') mem') n0 8 0 /\
  range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF n0 8.
Proof.
intros n0 H32 En0 Hn0FR HARU' Hv Hr. split.
- intros j Hj. rewrite (crtB2_mbyte_kept SK B STK1 sp1 FP lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc _ HJ HU HO' HP').
  + exact (Hv j Hj).
  + right. exists 3, pos. split; [exact Hin3|]. rewrite crt_frame3. lia.
  + apply crtB2_frm_off; [lia | apply Hn0FR; lia].
- intros x Hx. destruct (Hr x Hx) as (s & Es & Hs). exists s. split; [|exact Hs].
  assert (Eo : shadow_of_addr SHADOW_OFF x = shadow_addr (frame_addr lyc 3 pos) + 0x34).
  { unfold shadow_of_addr, shadow_addr. apply Z.mod_divide in H32 as [q Hq]; [|lia].
    rewrite En0 in Hx. rewrite Hq in Hx |- *. Z.div_mod_to_equations. lia. }
  rewrite Eo in Es |- *.
  rewrite (crt_keep_fsh SK B lyc Sc Uc W memc mdc ly' S' U' W' mem' md' STK1 sp1 FP kc 3 pos 0x34 HU HARU' HJ Hin3
    ltac:(rewrite crt_frame3; lia)); [exact Es|].
  intros Hf. apply (crtB2_fp_noshadow B lyc Sc W _ mdc pos FR Dh _ HAR Hin3 HFR HDh Hf).
  destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 3 pos HAR Hin3) as (F1 & F2 & _). rewrite crt_frame3 in F2.
  pose proof (@alloc_ceiling_lt rc) as HC47. change (2 ^ 47) with 140737488355328 in HC47.
  unfold shadow_addr. change (2 ^ 44) with 17592186044416. Z.div_mod_to_equations. lia.
Qed.
End c.
End h2.

(* ================= small facts the call steps share ================= *)
Lemma crtB2_zsum_perm : forall l l', Permutation l l' -> fold_right Z.add 0 l = fold_right Z.add 0 l'.
Proof. intros l l' H. induction H; cbn [fold_right]; lia. Qed.
Lemma crtB2_rd_sum_sizes : forall D sz, Permutation (map snd D) sz -> rd_sum D = fold_right Z.add 0 sz.
Proof.
intros D sz H. rewrite <- (crtB2_zsum_perm _ _ H). clear H. induction D as [|b D IH]; [reflexivity|].
unfold rd_sum in *. cbn [fold_right map]. rewrite IH. reflexivity.
Qed.
(* the encoder's text and the decoder's block, by size *)
Lemma crtB2_tb2_len : forall bs, Z.of_nat (length (WriterSpec.b64_enc bs)) = (Z.of_nat (length bs) + 2) / 3 * 4.
Proof. intros bs. rewrite WriterSpecFacts.b64_enc_length, Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add. reflexivity. Qed.
Lemma crtB2_enc_tb2 : forall bs,
  Z.of_nat (length (WriterSpec.b64_enc bs)) + 1 = FSH_Fn_writer.enc_size (Z.of_nat (length bs)).
Proof. intros bs. rewrite crtB2_tb2_len. unfold FSH_Fn_writer.enc_size. lia. Qed.
Lemma crtB2_bs_dec : forall bs, Z.of_nat (length bs) <= FSH_Fn_writer.dec_size (WriterSpec.b64_enc bs).
Proof. intros bs. unfold FSH_Fn_writer.dec_size. rewrite crtB2_tb2_len. Z.div_mod_to_equations. lia. Qed.
(* a callee-saved register of the call site, read off the resumed env (FSH_crt_site.crt_ssave: s2 .. s11 are the
   boundary's atoms at every call site of the lane) *)
Lemma crtB2_env_kept : forall E ssC regsC regs' extra (n : nat),
  (18 <= n <= 27)%nat -> crt_ssave ssC ->
  (forall rr : bv 5, YK11.getr regsC rr = sv_denot E (sr_get (ss_regs ssC) rr)) ->
  aregs_preserved regsC regs' -> ew (Ereg regs' extra) n = ew E n.
Proof.
intros E ssC regsC regs' extra n Hn HS RG HP.
rewrite (ew_Ereg_nat regs' extra n (Z_to_bv 5 (Z.of_nat n)))
  by (rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | change (bv_modulus 5) with 32; lia]).
rewrite (HP (Z.of_nat n)) by (unfold acallee_saved; lia).
rewrite RG, (HS n Hn). apply fsw_SOff0.
Qed.
Section n. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* a block appended by the callee is apart from every block it found *)
Lemma crtB2_new_apart : forall ly S (W : world tfibsegs) mem md l x y, AR tfibsegs B ly S W mem md ->
  ablocks B ly S = l ++ [y] -> In x l -> zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md l x y HAR E Hx. apply in_split in Hx as (l1 & l2 & ->).
apply (sep_blocks_pos tfibsegs B LAWS ly S W mem md x y l1 l2 [] HAR). rewrite E, <- app_assoc. reflexivity.
Qed.
End n.

(* ================= a pj_string call of the lane (segments 14, 16, 18): v's node takes the string ================= *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis PJ_STRING : @pj_string_spec fx rc SK tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Lemma crtB2_hcall_str : forall ssC r s (cs : list Z) za msd sd mss ss vs0 (K CNT LIVE K' CNT' LIVE' : crt_cx -> Z),
  crt_ssave ssC ->
  sr_get (ss_regs ssC) 1%bv = SLit r -> sr_get (ss_regs ssC) 2%bv = SOff 2 0 ->
  sr_get (ss_regs ssC) 10%bv = SOff 22 0 -> sr_get (ss_regs ssC) 11%bv = SLit s ->
  0 <= r < 2 ^ 64 ->
  In (s, cs) FS_RO_STRS -> 0x10000 <= s -> s + Z.of_nat (length cs) + 1 <= FS_IMG_END ->
  (vs0 = VAny \/ vs0 = VZero) ->
  Z.of_nat (length cs) + 1 + HEAD < MALLOC_MAX ->
  (forall cx, crt_base B cx ->
     K cx + EV_pj_string <= K' cx /\ CNT cx + 1 <= CNT' cx /\ LIVE cx + (Z.of_nat (length cs) + 1 + HEAD) <= LIVE' cx /\
     K' cx <= EV_check_round_trip /\ CNT' cx <= EV_check_round_trip /\ LIVE' cx <= LIVE_check_round_trip /\
     FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) +
       fold_right Z.add 0 sd + fold_right Z.add 0 ss + (Z.of_nat (length cs) + 1) <= LIVE_check_round_trip) ->
  crt_hcall SK B ssC A_pj_string r STK_pj_string (crtB2_inv B za msd sd mss ss vs0 K CNT LIVE)
    (crtB2_inv B true msd sd mss ss (VStr cs) K' CNT' LIVE').
Proof.
intros ssC r s cs za msd sd mss ss vs0 K CNT LIVE K' CNT' LIVE' GS G1 G2 G10 G11 Hr Hstr Hs0 Hs1 Hvs Hmx HBUD.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (HBUD cx HB) as (BK & BC & BL & BK' & BC' & BL' & BLV).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E19 & EX).
destruct HINV as (_ & E18 & E20 & E21 & E22 & E23 & E26 & E27 & same & nsame & dec & Ddoc & Dst & Dv & live & peak & cnt &
  E24 & E25 & HPB & HPU & HHD & HTX & HTZ & HTC & HDC & HDZ & HTD & HSD & HTS & HSS & HVF & HPD & HPS & HPV & HPK &
  HN0 & HN0a & HG & HL & HBB & HCNT & HK).
assert (EDv : Dv = []) by (destruct Hvs as [-> | ->]; cbn [crtB2_vfact] in HVF; [exact HVF | exact (proj1 HVF)]).
subst Dv. clear HVF.
set (F := crt_F cx) in *. set (m3 := ms_mem ms3) in *.
set (len := Z.of_nat (length (c_bs cx))) in *. set (tb2 := WriterSpec.b64_enc (c_bs cx)) in *.
set (n := Z.of_nat (length cs) + 1).
(* the frame, the journal's window, the boundary memory read at the call *)
pose proof HJC as (HARj & Hly3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (crt_F_ly cx _ ly3 Hly3) as EF.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (crt_F_facts SK B cx _ _ _ _ _ _ _ HJC HARUC Hfr) as (HF32 & HF0 & HFc & HFapp & _ & _).
fold F in HF32, HF0, HFc, HFapp.
assert (Hsp1 : spZ (c_regs cx) - 208 <= crt_sp1 cx <= spZ (c_regs cx) - 192).
{ destruct (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
    as (F1 & _ & _). unfold crt_sp1. lia. }
pose proof crt_STK_eq as STKv; unfold crt_STK in STKv.
assert (STKs : STK_pj_string + 208 <= STK_check_round_trip) by (apply Z.leb_le; vm_compute; reflexivity).
assert (STKs0 : 0 <= STK_pj_string) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Esp : spZ regsC = crt_sp1 cx) by (unfold spZ; rewrite RG, G2, fsw_SOff0; exact E2).
assert (R1 : YK11.getr regsC 1%bv = Z_to_bv 64 r) by (rewrite RG, G1; reflexivity).
assert (Rra : raZ regsC = r) by (unfold raZ; rewrite R1; apply wz; lia).
assert (HTDc : rtree tfibsegs B ly3 S3 W3 memC (F + 0x20) (PjTree.JObj msd) Ddoc)
  by exact (rnode_below B ly3 S3 W3 _ mdC m3 memC Ddoc (F + 0x20) _ Ddoc HARC HSB ltac:(lia) ltac:(lia) HTD).
assert (HTSc : rtree tfibsegs B ly3 S3 W3 memC (F + 0x80) (PjTree.JObj mss) Dst)
  by exact (rnode_below B ly3 S3 W3 _ mdC m3 memC Dst (F + 0x80) _ Dst HARC HSB ltac:(lia) ltac:(lia) HTS).
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPD) as HPDc.
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPS) as HPSc.
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPV) as HPVc.
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPK) as HPKc.
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC m3 memC _ _ HARC HSB HTX) as HTXc.
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC m3 memC _ _ HARC HSB HDC) as HDCc.
pose proof (cstr_ok_below W3 m3 memC _ _ HSB HTC) as HTCc.
pose proof (fs_glob_below W3 m3 memC _ _ _ _ HSB HG) as HGc.
pose proof (val_mem_below (w_H W3) m3 memC alloc_ceiling (F + 0x1a0) 8 0 HSB ltac:(lia) ltac:(cbn; lia) HN0) as HN0c.
pose proof (fsw_range_addressable_below (w_H W3) m3 memC (F + 0x1a0) 8 HSB ltac:(lia) ltac:(lia) HN0a) as HN0ac.
pose proof HDC as (HinD & _ & HdecK & _).
pose proof (fsw_rblock_low B ly3 S3 W3 _ mdC m3 dec _ HARC HDC) as (Hdl0 & Hdl1).
assert (HDZc : zbytes_at tfibsegs W3 memC dec (c_bs cx)).
{ unfold zbytes_at in *. apply (garr8_frame tfibsegs _ _ dec (c_bs cx) HDZ). intros a Ha.
  apply (mbyte_below (w_H W3) m3 memC alloc_ceiling a HSB). pose proof (crtB2_bs_dec (c_bs cx)) as Hb.
  unfold tb2, len, HEAD in *. lia. }
(* the callee's spec *)
assert (HGc0 : 0 <= live /\ 0 <= cnt) by (pose proof HGc as (_ & _ & _ & _ & HL0 & _ & HC0 & _); lia).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HQ1 & HQ2 & HQ3) & HLV0 & _ &
  _ & HNEV0 & HBB0).
assert (Hrsum : rd_sum (Ddoc ++ Dst ++ []) = fold_right Z.add 0 sd + fold_right Z.add 0 ss).
{ rewrite app_nil_r, crt_rd_sum_app, (crtB2_rd_sum_sizes Ddoc sd HSD), (crtB2_rd_sum_sizes Dst ss HSS). reflexivity. }
pose proof (fsw_pobj_off_img B ly3 S3 W3 _ mdC memC _ HARC HPVc) as Hvimg.
assert (HSR := PJ_STRING ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) (F + 0xe0) s cs live peak cnt SIZE_MAXZ
  HPREc HHD
  ltac:(rewrite RG, G10, fsw_SOff0; exact E22)
  ltac:(rewrite RG, G11; reflexivity)
  HPVc ltac:(left; rewrite Esp; lia)
  ltac:(right; split; [lia|]; split; [exact (FSW_strkit.cstr_ok_kept_tbl B ly3 S3 U3 W3 memC mdC s cs IMG HARUC
          (proj2 HPREc) (or_introl Hstr))|]; split; [right; left; exact Hstr | lia])
  HGc ltac:(split; [reflexivity | lia]) Hmx ltac:(fold n; lia) ltac:(lia) ltac:(lia)).
exists ([(F + 0xe0, F + 0xe0 + 56)] ++ FS_PSTAT_FP), EV_pj_string.
eexists. split; [exact HSR|].
split.
{ pose proof (crtB2_fpsub_obj B (c_ly cx) (c_S cx) ly3 S3 (c_pos cx) 0xe0 ltac:(lia) ltac:(lia)) as X.
  rewrite EF in X. exact X. }
split.
{ intros a Ha. rewrite crt_frame3 in Ha.
  apply (crtB2_tail_free B ly3 S3 W3 _ mdC (c_pos cx) _ HARC Hin3); rewrite EF; fold F.
  - intros x Hx. apply inFP_app in Hx as [Hx|Hx]; [left|right; right; exact Hx].
    apply inFP_cons in Hx as [Hx|Hx]; [lia | exfalso; exact (inFP_nil x Hx)].
  - lia. }
(* the return *)
intros W' c' (a & ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & R10' & Ha & HBL & HTV' & HPV' & HG').
exists ly', S', (U3 ++ [(a - HEAD, HEAD)]), regs', mem', md'.
split; [exact Ec|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' HARU'.
pose proof (proj1 HJc) as HAR'.
set (FR := [(F + 0xe0, F + 0xe0 + 56)]).
assert (HJcF : ajournal tfibsegs B STK_pj_string (spZ regsC) (FR ++ ablocks_fp [] ++ FS_PSTAT_FP) ly3 S3 W3
  (unpoison U3 memC) mdC [] ly' S' W' (unpoison (U3 ++ [(a - HEAD, HEAD)]) mem') md' EV_pj_string) by exact HJc.
assert (HFRf : forall x, inFP FR x -> frame_addr ly3 3 (c_pos cx) <= x < frame_addr ly3 3 (c_pos cx) + 512).
{ intros x Hx. rewrite EF. apply inFP_cons in Hx as [Hx|Hx]; [lia | exfalso; exact (inFP_nil x Hx)]. }
assert (HDh : forall bk, In bk (@nil (Z * Z)) -> In bk (ablocks B ly3 S3)) by (intros bk []).
assert (HnoFR : forall lo hi x, lo <= x < hi -> (hi <= F + 0xe0 \/ F + 0xe0 + 56 <= lo) -> ~ inFP FR x).
{ intros lo hi x Hx Hd Hf. apply inFP_cons in Hf as [Hf|Hf]; [lia | exact (inFP_nil x Hf)]. }
(* the heads: U3 plus the string block's *)
assert (HHD' : FSupoisonU.fs_heads B ly' S' (U3 ++ [(a - HEAD, HEAD)])).
{ intros q Hq. apply in_app_or in Hq as [Hq|[<-|[]]].
  - destruct (HHD q Hq) as (H16 & m & Hm & Hrm). split; [exact H16|]. exists m. split; [|exact Hrm].
    rewrite HBL. apply in_or_app. left. exact Hm.
  - split; [reflexivity|]. exists (n + HEAD). split; [rewrite HBL; apply in_or_app; right; left; reflexivity|].
    unfold req_size, HEAD. destruct (Z.eqb_spec (n + 16) 0); lia. }
(* text and dec: their blocks are not the string's; the string's head is apart from the text *)
pose proof HTX as (HinT & _ & HTk & _).
assert (Htb2 : Z.of_nat (length tb2) + 1 = FSH_Fn_writer.enc_size len) by exact (crtB2_enc_tb2 (c_bs cx)).
assert (HTX' := crtB2_rblock_kept SK B STK_pj_string (spZ regsC) EV_pj_string (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
  ly' S' (U3 ++ [(a - HEAD, HEAD)]) W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh _ _ HTXc (fun H => H)).
assert (HDC' := crtB2_rblock_kept SK B STK_pj_string (spZ regsC) EV_pj_string (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
  ly' S' (U3 ++ [(a - HEAD, HEAD)]) W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh _ _ HDCc (fun H => H)).
assert (HTC' : cstr_ok tfibsegs W' mem' (c_text cx) tb2).
{ apply (crtB2_cstr_kept SK B STK_pj_string (spZ regsC) EV_pj_string (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
    ly' S' (U3 ++ [(a - HEAD, HEAD)]) W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh (c_text cx) tb2
    (c_text cx - HEAD) (FSH_Fn_writer.enc_size len + HEAD) HinT (fun H => H)); [unfold HEAD; lia | unfold HEAD; lia | |
    exact HTCc].
  intros q Hq. apply in_app_or in Hq as [Hq|[<-|[]]]; [left; exact Hq | right].
  destruct (crtB2_new_apart B ly' S' W' _ md' (ablocks B ly3 S3) (c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD)
    (a - HEAD, n + HEAD) HAR' HBL HinT) as [Hd|Hd]; unfold block_rng in Hd; cbn [fst snd] in Hd |- *;
    pose proof (req_size_pos (FSH_Fn_writer.enc_size len + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr1);
    pose proof (req_size_pos (n + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr2); unfold HEAD in *; lia. }
assert (HDZ' : zbytes_at tfibsegs W' mem' dec (c_bs cx)).
{ apply (crtB2_zbytes_kept SK B STK_pj_string (spZ regsC) EV_pj_string (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
    ly' S' (U3 ++ [(a - HEAD, HEAD)]) W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh dec (c_bs cx)
    (dec - HEAD) (FSH_Fn_writer.dec_size tb2 + HEAD) HinD (fun H => H)); [unfold HEAD; lia | | exact HDZc].
  pose proof (crtB2_bs_dec (c_bs cx)) as Hbd. fold tb2 len in Hbd.
  pose proof (req_size_pos (FSH_Fn_writer.dec_size tb2 + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr1).
  unfold HEAD in *. lia. }
(* the two trees and the four objects that are not v *)
assert (HTD' : rtree tfibsegs B ly' S' W' mem' (F + 0x20) (PjTree.JObj msd) Ddoc).
{ apply (crtB2_rtree_kept SK B STK_pj_string (spZ regsC) EV_pj_string (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
    ly' S' (U3 ++ [(a - HEAD, HEAD)]) W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh); [rewrite EF; lia | rewrite EF; lia
    | intros x Hx; apply (HnoFR (F + 0x20) (F + 0x20 + 56)); lia | intros bk _ [] | exact HPDc | exact HTDc]. }
assert (HTS' : rtree tfibsegs B ly' S' W' mem' (F + 0x80) (PjTree.JObj mss) Dst).
{ apply (crtB2_rtree_kept SK B STK_pj_string (spZ regsC) EV_pj_string (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
    ly' S' (U3 ++ [(a - HEAD, HEAD)]) W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh); [rewrite EF; lia | rewrite EF; lia
    | intros x Hx; apply (HnoFR (F + 0x80) (F + 0x80 + 56)); lia | intros bk _ [] | exact HPSc | exact HTSc]. }
assert (POBJ : forall o, 0 <= o -> o + 56 <= 512 -> (o + 56 <= 0xe0 \/ 0x118 <= o) ->
  pobj tfibsegs B ly3 S3 W3 memC (F + o) -> pobj tfibsegs B ly' S' W' mem' (F + o)).
{ intros o Ho0 Ho1 Ho2 Hpo.
  apply (crtB2_pobj_kept SK B STK_pj_string (spZ regsC) EV_pj_string (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
    ly' S' (U3 ++ [(a - HEAD, HEAD)]) W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh); [rewrite EF; lia | rewrite EF; lia
    | intros x Hx; apply (HnoFR (F + o) (F + o + 56)); lia | exact HHD' | exact Hpo]. }
destruct (crtB2_n0_kept SK B STK_pj_string (spZ regsC) EV_pj_string (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
  ly' S' (U3 ++ [(a - HEAD, HEAD)]) W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh (F + 0x1a0)
  ltac:(rewrite EF; exact HF32) ltac:(rewrite EF; reflexivity)
  ltac:(intros x Hx; apply (HnoFR (F + 0x1a0) (F + 0x1a0 + 8)); lia) HARU' HN0c HN0ac) as (HN0' & HN0a').
(* the new boundary *)
clear HSR.
cbn [crtB2_inv]. fold F len tb2.
set (E' := Ereg regs' (crt_extra cx)).
assert (EK : forall nn : nat, (18 <= nn <= 27)%nat -> ew E' nn = ew E nn)
  by (intros nn Hnn; exact (crtB2_env_kept E ssC regsC regs' (crt_extra cx) nn Hnn GS RG HP)).
split; [intros _; subst E'; rewrite (ew_Ereg_nat regs' (crt_extra cx) 10 10%bv eq_refl); exact R10'|].
rewrite (EK 18%nat ltac:(lia)), (EK 20%nat ltac:(lia)), (EK 21%nat ltac:(lia)), (EK 22%nat ltac:(lia)),
  (EK 23%nat ltac:(lia)), (EK 26%nat ltac:(lia)), (EK 27%nat ltac:(lia)).
split; [exact E18|]. split; [exact E20|]. split; [exact E21|]. split; [exact E22|]. split; [exact E23|].
split; [exact E26|]. split; [exact E27|].
exists same, nsame, dec, Ddoc, Dst, [(a, n)], (live + n), (Z.max peak (live + n)), (cnt + 1).
rewrite (EK 24%nat ltac:(lia)), (EK 25%nat ltac:(lia)).
split; [exact E24|]. split; [exact E25|].
split.
{ rewrite HBL. eapply Permutation_trans; [apply Permutation_app_tail; exact HPB|].
  unfold rd_hblocks. rewrite !map_app, !app_nil_r. cbn [map fst snd]. rewrite <- !app_assoc. apply Permutation_refl. }
split.
{ eapply Permutation_trans; [apply Permutation_app_tail; exact HPU|].
  unfold rd_heads. rewrite !map_app, !app_nil_r. cbn [map fst snd]. rewrite <- !app_assoc. apply Permutation_refl. }
split; [exact HHD'|].
split; [exact HTX'|]. split; [exact (proj1 (proj1 HTC'))|]. split; [exact HTC'|].
split; [exact HDC'|]. split; [exact HDZ'|].
split; [exact HTD'|]. split; [exact HSD|]. split; [exact HTS'|]. split; [exact HSS|].
split; [cbn [crtB2_vfact]; split; [exists a; reflexivity | exact HTV']|].
split; [exact (POBJ 0x20 ltac:(lia) ltac:(lia) ltac:(lia) HPDc)|].
split; [exact (POBJ 0x80 ltac:(lia) ltac:(lia) ltac:(lia) HPSc)|].
split; [exact HPV'|].
split; [exact (POBJ 0x140 ltac:(lia) ltac:(lia) ltac:(lia) HPKc)|].
split; [exact HN0'|]. split; [exact HN0a'|].
split; [exact HG'|].
split.
{ rewrite HL, app_nil_r, !crt_rd_sum_app.
  replace (rd_sum [(a, n)]) with n by (unfold rd_sum; cbn [fold_right snd]; lia). unfold n, len, tb2 in *. lia. }
split.
{ rewrite (blocks_bytes_bsum B ly' S'), HBL, bsum_app, <- (blocks_bytes_bsum B ly3 S3).
  cbn [bsum fold_right snd]. lia. }
split; [lia|]. lia.
Qed.
End s.

(* ================= helpers of the pj_set steps ================= *)
Lemma crtB2_bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof. intros l l' H. induction H; cbn [bsum fold_right] in *; unfold bsum in *; cbn [fold_right] in *; lia. Qed.
Section n2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* two blocks of the two halves of a permutation of ablocks are apart *)
Lemma crtB2_apart_app : forall ly S (W : world tfibsegs) mem md L X x y, AR tfibsegs B ly S W mem md ->
  Permutation (ablocks B ly S) (L ++ X) -> In x L -> In y X -> zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md L X x y HAR HP Hx Hy.
apply in_split in Hx as (l1 & l2 & ->). apply in_split in Hy as (m1 & m2 & ->).
apply (sep_blocks_perm tfibsegs B LAWS ly S W mem md x y (l1 ++ l2 ++ m1 ++ m2) HAR).
eapply Permutation_trans; [exact HP|].
assert (E1 : (l1 ++ x :: l2) ++ m1 ++ y :: m2 = l1 ++ x :: (l2 ++ m1 ++ y :: m2)) by (rewrite <- app_assoc; reflexivity).
rewrite E1. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
assert (E2 : l1 ++ l2 ++ m1 ++ y :: m2 = (l1 ++ l2 ++ m1) ++ y :: m2) by (rewrite <- !app_assoc; reflexivity).
rewrite E2. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
rewrite <- !app_assoc. apply Permutation_refl.
Qed.
(* an empty object's header: n = cap = kids = keys = 0 *)
Lemma crtB2_obj0_hdr : forall ly S (W : world tfibsegs) mem o,
  rtree tfibsegs B ly S W mem o (PjTree.JObj []) [] ->
  exists num str, PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem) o 6 num str 0 0 0 0.
Proof.
intros ly S W mem o (HN & _ & _). cbn [PjStruct.pj_node PjTree.tag length] in HN.
destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & _ & En & _ & Hcap & Di & ED & _).
destruct Hcap as [(-> & -> & ->)|(Hc & _)].
- exists num, str. subst n. exact Hh.
- exfalso. rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia. discriminate ED.
Qed.
Lemma crtB2_rbo_cat : forall ly S (W : world tfibsegs) mem l1 l2,
  rd_blocks_ok tfibsegs B ly S W mem l1 -> rd_blocks_ok tfibsegs B ly S W mem l2 ->
  rd_blocks_ok tfibsegs B ly S W mem (l1 ++ l2).
Proof. intros ly S W mem l1 l2 H1 H2 a k Hak. apply in_app_or in Hak as [H|H]; [exact (H1 a k H) | exact (H2 a k H)]. Qed.
End n2.

(* ================= a pj_set call that grows an EMPTY object (segment 15 on doc, segment 19 on state): grow_res's
   second arm from cap 0 (Dold = [], Dnew = kids 56 * 8 and keys 8 * 8, both heads appended to U), v's node moved
   into the object with the key's copy, v zeroed ================= *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis PJ_SET : @pj_set_spec fx rc SK tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* on doc (F + 0x20): state kept *)
Lemma crtB2_hcall_set0_doc : forall ssC r k (kname cs : list Z) mss ss (K CNT LIVE K' CNT' LIVE' : crt_cx -> Z),
  let klen := Z.of_nat (length kname) in let tr := pj_set_c.set_trace 0 0 klen in
  crt_ssave ssC ->
  sr_get (ss_regs ssC) 1%bv = SLit r -> sr_get (ss_regs ssC) 2%bv = SOff 2 0 ->
  sr_get (ss_regs ssC) 10%bv = SOff 26 0 -> sr_get (ss_regs ssC) 11%bv = SLit k ->
  sr_get (ss_regs ssC) 12%bv = SOff 22 0 ->
  0 <= r < 2 ^ 64 ->
  In (k, kname) FS_RO_STRS -> 0x10000 <= k -> k + klen + 1 <= FS_IMG_END ->
  klen + 1 + HEAD < MALLOC_MAX ->
  PjGrammar.held tr = 56 * 8 + 8 * 8 + (klen + 1) ->
  rd_live tr = (56 * 8 + HEAD) + (8 * 8 + HEAD) + (klen + 1 + HEAD) ->
  (forall cx, crt_base B cx ->
     K cx + rd_ev tr <= K' cx /\ CNT cx + Z.of_nat (length tr) <= CNT' cx /\ LIVE cx + rd_live tr <= LIVE' cx /\
     K' cx <= EV_check_round_trip /\ CNT' cx <= EV_check_round_trip /\ LIVE' cx <= LIVE_check_round_trip /\
     FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) +
       fold_right Z.add 0 ss + (Z.of_nat (length cs) + 1) + rd_live tr <= LIVE_check_round_trip) ->
  crt_hcall SK B ssC A_pj_set r STK_pj_set (crtB2_inv B true [] [] mss ss (VStr cs) K CNT LIVE)
    (crtB2_inv B true [(kname, PjTree.JStr cs)] [56 * 8; 8 * 8; klen + 1; Z.of_nat (length cs) + 1] mss ss VZero
       K' CNT' LIVE').
Proof.
intros ssC r k kname cs mss ss K CNT LIVE K' CNT' LIVE' klen tr GS G1 G2 G10 G11 G12 Hr Hstr Hk0 Hk1 Hmx
  Hheld Hrl HBUD.
intros cx E kk ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (HBUD cx HB) as (BK & BC & BL & BK' & BC' & BL' & BLV).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E19 & EX).
destruct HINV as (_ & E18 & E20 & E21 & E22 & E23 & E26 & E27 & same & nsame & dec & Ddoc & Dst & Dv & live & peak & cnt &
  E24 & E25 & HPB & HPU & HHD & HTX & HTZ & HTC & HDC & HDZ & HTD & HSD & HTS & HSS & HVF & HPD & HPS & HPV & HPK &
  HN0 & HN0a & HG & HL & HBB & HCNT & HK).
apply Permutation_sym, Permutation_nil, map_eq_nil in HSD. subst Ddoc.
cbn [crtB2_vfact] in HVF. destruct HVF as ((av & ->) & HTV).
set (F := crt_F cx) in *. set (m3 := ms_mem ms3) in *.
set (len := Z.of_nat (length (c_bs cx))) in *. set (tb2 := WriterSpec.b64_enc (c_bs cx)) in *.
set (n := Z.of_nat (length cs) + 1) in *.
pose proof HJC as (HARj & Hly3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (crt_F_ly cx _ ly3 Hly3) as EF.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (crt_F_facts SK B cx _ _ _ _ _ _ _ HJC HARUC Hfr) as (HF32 & HF0 & HFc & HFapp & _ & _).
fold F in HF32, HF0, HFc, HFapp.
assert (Hsp1 : spZ (c_regs cx) - 208 <= crt_sp1 cx <= spZ (c_regs cx) - 192).
{ destruct (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
    as (F1 & _ & _). unfold crt_sp1. lia. }
pose proof crt_STK_eq as STKv; unfold crt_STK in STKv.
assert (STKs : STK_pj_set + 208 <= STK_check_round_trip) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Esp : spZ regsC = crt_sp1 cx) by (unfold spZ; rewrite RG, G2, fsw_SOff0; exact E2).
assert (R1 : YK11.getr regsC 1%bv = Z_to_bv 64 r) by (rewrite RG, G1; reflexivity).
assert (Rra : raZ regsC = r) by (unfold raZ; rewrite R1; apply wz; lia).
assert (HTDc : rtree tfibsegs B ly3 S3 W3 memC (F + 0x20) (PjTree.JObj []) [])
  by exact (rnode_below B ly3 S3 W3 _ mdC m3 memC [] (F + 0x20) _ [] HARC HSB ltac:(lia) ltac:(lia) HTD).
assert (HTSc : rtree tfibsegs B ly3 S3 W3 memC (F + 0x80) (PjTree.JObj mss) Dst)
  by exact (rnode_below B ly3 S3 W3 _ mdC m3 memC Dst (F + 0x80) _ Dst HARC HSB ltac:(lia) ltac:(lia) HTS).
assert (HTVc : rtree tfibsegs B ly3 S3 W3 memC (F + 0xe0) (PjTree.JStr cs) [(av, n)])
  by exact (rnode_below B ly3 S3 W3 _ mdC m3 memC [(av, n)] (F + 0xe0) _ [(av, n)] HARC HSB ltac:(lia) ltac:(lia) HTV).
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPD) as HPDc.
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPS) as HPSc.
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPV) as HPVc.
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPK) as HPKc.
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC m3 memC _ _ HARC HSB HTX) as HTXc.
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC m3 memC _ _ HARC HSB HDC) as HDCc.
pose proof (cstr_ok_below W3 m3 memC _ _ HSB HTC) as HTCc.
pose proof (fs_glob_below W3 m3 memC _ _ _ _ HSB HG) as HGc.
pose proof (val_mem_below (w_H W3) m3 memC alloc_ceiling (F + 0x1a0) 8 0 HSB ltac:(lia) ltac:(cbn; lia) HN0) as HN0c.
pose proof (fsw_range_addressable_below (w_H W3) m3 memC (F + 0x1a0) 8 HSB ltac:(lia) ltac:(lia) HN0a) as HN0ac.
pose proof HDC as (HinD & _ & HdecK & _).
pose proof (fsw_rblock_low B ly3 S3 W3 _ mdC m3 dec _ HARC HDC) as (Hdl0 & Hdl1).
assert (HDZc : zbytes_at tfibsegs W3 memC dec (c_bs cx)).
{ unfold zbytes_at in *. apply (garr8_frame tfibsegs _ _ dec (c_bs cx) HDZ). intros a Ha.
  apply (mbyte_below (w_H W3) m3 memC alloc_ceiling a HSB). pose proof (crtB2_bs_dec (c_bs cx)) as Hb.
  unfold tb2, len, HEAD in *. lia. }
assert (HGc0 : 0 <= live /\ 0 <= cnt) by (pose proof HGc as (_ & _ & _ & _ & HL0 & _ & HC0 & _); lia).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HQ1 & HQ2 & HQ3) & HLV0 & _ &
  _ & HNEV0 & HBB0).
assert (Hrsum : rd_sum ([] ++ Dst ++ [(av, n)]) = fold_right Z.add 0 ss + n).
{ cbn [app]. rewrite crt_rd_sum_app, (crtB2_rd_sum_sizes Dst ss HSS). unfold rd_sum. cbn [fold_right snd]. lia. }
(* the v block, apart from the frame and below the image's top or above it *)
pose proof HTVc as (_ & HBv & _). destruct (HBv av n (or_introl eq_refl)) as (HinV & _ & Hn0 & _).
pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 _ mdC (av - HEAD) (n + HEAD) 3 (c_pos cx) HARC HinV Hin3) as HdV.
unfold zdisjoint in HdV. cbn [fst snd] in HdV. rewrite EF, crt_frame3 in HdV. fold F in HdV.
pose proof (req_size_pos (n + HEAD) ltac:(unfold HEAD; lia)) as (_ & HrqV).
pose proof (fsw_ablock_off_img B ly3 S3 W3 _ mdC (av - HEAD) (n + HEAD) HARC HinV) as HimgV.
pose proof (fsw_pobj_off_img B ly3 S3 W3 _ mdC memC _ HARC HPDc) as HimgO.
pose proof (fsw_pobj_off_img B ly3 S3 W3 _ mdC memC _ HARC HPVc) as HimgW.
destruct (crtB2_obj0_hdr B ly3 S3 W3 memC (F + 0x20) HTDc) as (num & str & Hh).
assert (Hlive : live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + rd_sum ([] ++ Dst ++ [(av, n)]))
  by exact HL.
assert (HSR := PJ_SET ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) (F + 0x20) k (F + 0xe0) [] (PjTree.JStr cs) []
  [(av, n)] num str 0 0 0 0 kname live peak cnt SIZE_MAXZ
  HPREc HHD
  ltac:(rewrite RG, G10, fsw_SOff0; exact E26)
  ltac:(rewrite RG, G11; reflexivity)
  ltac:(rewrite RG, G12, fsw_SOff0; exact E22)
  HTDc HPDc Hh ltac:(lia) ltac:(intros x Hx; destruct Hx)
  HTVc HPVc ltac:(intros bk _ Hbk; destruct Hbk)
  ltac:(intros x Hx [Hf | (b & Hb & _)]; [lia | destruct Hb])
  ltac:(intros b x [<- | []] Hx Hox; unfold PjStruct.pj_holds in Hx; cbn [fst snd] in Hx; unfold HEAD in *; lia)
  ltac:(left; rewrite Esp; lia) ltac:(left; rewrite Esp; lia)
  (FSW_strkit.cstr_ok_kept_tbl B ly3 S3 U3 W3 memC mdC k kname IMG HARUC (proj2 HPREc) (or_introl Hstr))
  ltac:(right; left; exact Hstr)
  ltac:(intros x Hx; split; [intros [Hf | (b & Hb & _)]; [lia | destruct Hb] | intros [Hf | (b & [<- | []] & Hb)];
    [lia | unfold PjStruct.pj_holds in Hb; cbn [fst snd] in Hb; unfold HEAD in *; lia]])
  ltac:(intros Hx; destruct Hx)
  HGc ltac:(split; [reflexivity | unfold tr, klen in *; lia])
  ltac:(exact (crt_pjset_dold0_150 B cx ly3 S3 W3 memC [] [] Dst [(av, n)] num str 0 0 0 0 live HB HTDc
    (crtB2_rbo_cat B ly3 S3 W3 memC Dst [(av, n)] (proj1 (proj2 HTSc)) (proj1 (proj2 HTVc))) Hh Hlive))
  Hmx ltac:(intros _; apply Z.ltb_lt; vm_compute; reflexivity)
  ltac:(unfold tr, klen in *; rewrite Hrl, Hlive, Hrsum; lia) ltac:(unfold tr, klen in *; lia)
  ltac:(unfold tr, klen in *; lia)).
exists ([(F + 0x20 + 24, F + 0x20 + 56); (F + 0xe0, F + 0xe0 + 56)] ++ ablocks_fp (rd_hblocks []) ++ FS_PSTAT_FP), (rd_ev tr).
eexists. split; [exact HSR|].
split.
{ pose proof (crtB2_fpsub_pjset B (c_ly cx) (c_S cx) ly3 S3 (c_pos cx) 0x20 0xe0 [] ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(intros bk [])) as X.
  rewrite EF in X. exact X. }
split.
{ intros a Ha. rewrite crt_frame3 in Ha.
  apply (crtB2_tail_free B ly3 S3 W3 _ mdC (c_pos cx) _ HARC Hin3); rewrite EF; fold F.
  - intros x Hx. apply inFP_app in Hx as [Hx|Hx]; [left|].
    + apply inFP_cons in Hx as [Hx|Hx]; [lia|]. apply inFP_cons in Hx as [Hx|Hx]; [lia | exfalso; exact (inFP_nil x Hx)].
    + right; right. apply inFP_app in Hx as [Hx|Hx]; [exfalso; exact (inFP_nil x Hx) | exact Hx].
  - lia. }
(* the return *)
intros W' c' (k' & y' & cap' & Dold & Dnew & Dr & Do & Ug & a & HGR & HPDr & HPDo & ly' & S' & regs' & mem' & md' &
  Ec & HJc & OK' & PO' & HP & R10' & Ha & HBL & HTDo & HZw & HPo & HPw & HKok' & peak' & Hpk & HG').
exists ly', S', (Ug ++ [(a - HEAD, HEAD)]), regs', mem', md'.
split; [exact Ec|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' HARU'.
pose proof (proj1 HJc) as HAR'.
(* grow from cap 0 *)
destruct HGR as [(Hlt & _) | (_ & Ecap & EDold & Hk1' & Hk2' & Hy & _ & EDnew & Um & HU1 & HU2)]; [lia|].
cbn [ReaderRes.cap2 Z.eqb] in Ecap. subst cap'.
cbn [ReaderRes.kids_blk ReaderRes.keys_blk Z.eqb orb negb app] in EDold. subst Dold.
cbn [Z.eqb] in EDnew, HU2. subst Dnew.
destruct HU1 as [(_ & ->) | (Hne & _)]; [|lia]. destruct HU2 as [(_ & ->) | (Hne & _)]; [|lia].
apply Permutation_nil, app_eq_nil in HPDr as (_ & ->).
destruct (Hy eq_refl) as (Hy1 & Hy2).
set (U' := ((U3 ++ [(k' - HEAD, HEAD)]) ++ [(y' - HEAD, HEAD)]) ++ [(a - HEAD, HEAD)]) in *.
set (X := rd_hblocks ([(k', 56 * 8); (y', 8 * 8)] ++ [(a, klen + 1)])).
assert (HBL' : Permutation (ablocks B ly' S') (ablocks B ly3 S3 ++ X)).
{ cbn [rd_hblocks map app] in HBL. rewrite app_nil_r in HBL. exact HBL. }
set (FR := [(F + 0x20 + 24, F + 0x20 + 56); (F + 0xe0, F + 0xe0 + 56)]).
assert (HJcF : ajournal tfibsegs B STK_pj_set (spZ regsC) (FR ++ ablocks_fp [] ++ FS_PSTAT_FP) ly3 S3 W3
  (unpoison U3 memC) mdC [] ly' S' W' (unpoison U' mem') md' (rd_ev tr)) by exact HJc.
assert (HFRf : forall x, inFP FR x -> frame_addr ly3 3 (c_pos cx) <= x < frame_addr ly3 3 (c_pos cx) + 512).
{ intros x Hx. rewrite EF. apply inFP_cons in Hx as [Hx|Hx]; [lia|].
  apply inFP_cons in Hx as [Hx|Hx]; [lia | exfalso; exact (inFP_nil x Hx)]. }
assert (HDh : forall bk, In bk (@nil (Z * Z)) -> In bk (ablocks B ly3 S3)) by (intros bk []).
assert (HnoFR : forall lo hi x, lo <= x < hi -> (hi <= F + 0x20 + 24 \/ F + 0x20 + 56 <= lo) ->
  (hi <= F + 0xe0 \/ F + 0xe0 + 56 <= lo) -> ~ inFP FR x).
{ intros lo hi x Hx Hd1 Hd2 Hf. apply inFP_cons in Hf as [Hf|Hf]; [lia|].
  apply inFP_cons in Hf as [Hf|Hf]; [lia | exact (inFP_nil x Hf)]. }
assert (HinX : forall bk, In bk X -> In bk (ablocks B ly' S')).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HBL')). apply in_or_app. right. exact Hbk. }
assert (Hin3' : forall bk, In bk (ablocks B ly3 S3) -> In bk (ablocks B ly' S')).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HBL')). apply in_or_app. left. exact Hbk. }
(* the heads *)
assert (HHD' : FSupoisonU.fs_heads B ly' S' U').
{ intros q Hq. unfold U' in Hq. rewrite <- !app_assoc in Hq. apply in_app_or in Hq as [Hq|Hq].
  - destruct (HHD q Hq) as (H16 & m & Hm & Hrm). split; [exact H16|]. exists m. split; [exact (Hin3' _ Hm) | exact Hrm].
  - cbn [app In] in Hq. destruct Hq as [<-|[<-|[<-|[]]]]; (split; [reflexivity|]); cbn [fst].
    + exists (56 * 8 + HEAD). split; [apply HinX; cbn; left; reflexivity|].
      unfold req_size, HEAD. destruct (Z.eqb_spec (56 * 8 + 16) 0); lia.
    + exists (8 * 8 + HEAD). split; [apply HinX; cbn; right; left; reflexivity|].
      unfold req_size, HEAD. destruct (Z.eqb_spec (8 * 8 + 16) 0); lia.
    + exists (klen + 1 + HEAD). split; [apply HinX; cbn; right; right; left; reflexivity|].
      unfold req_size, HEAD. destruct (Z.eqb_spec (klen + 1 + 16) 0); lia. }
(* text and dec *)
pose proof HTX as (HinT & _ & HTk & _).
assert (Htb2 : Z.of_nat (length tb2) + 1 = FSH_Fn_writer.enc_size len) by exact (crtB2_enc_tb2 (c_bs cx)).
assert (HTX' := crtB2_rblock_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
  ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh _ _ HTXc (fun H => H)).
assert (HDC' := crtB2_rblock_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
  ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh _ _ HDCc (fun H => H)).
assert (HTC' : cstr_ok tfibsegs W' mem' (c_text cx) tb2).
{ apply (crtB2_cstr_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
    ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh (c_text cx) tb2
    (c_text cx - HEAD) (FSH_Fn_writer.enc_size len + HEAD) HinT (fun H => H)); [unfold HEAD; lia | unfold HEAD; lia | |
    exact HTCc].
  intros q Hq. unfold U' in Hq. rewrite <- !app_assoc in Hq. apply in_app_or in Hq as [Hq|Hq]; [left; exact Hq | right].
  assert (AP : forall y, In y X -> zdisjoint (block_rng (c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD)) (block_rng y))
    by (intros yy Hyy; exact (crtB2_apart_app B ly' S' W' _ md' _ _ _ yy HAR' HBL' HinT Hyy)).
  pose proof (req_size_pos (FSH_Fn_writer.enc_size len + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr1).
  cbn [app In] in Hq. destruct Hq as [<-|[<-|[<-|[]]]].
  + pose proof (AP _ (or_introl eq_refl)) as Hd. unfold block_rng, zdisjoint in Hd. cbn [fst snd] in Hd |- *.
    pose proof (req_size_pos (56 * 8 + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr2). unfold HEAD in *. lia.
  + pose proof (AP _ (or_intror (or_introl eq_refl))) as Hd. unfold block_rng, zdisjoint in Hd. cbn [fst snd] in Hd |- *.
    pose proof (req_size_pos (8 * 8 + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr2). unfold HEAD in *. lia.
  + pose proof (AP _ (or_intror (or_intror (or_introl eq_refl)))) as Hd. unfold block_rng, zdisjoint in Hd.
    cbn [fst snd] in Hd |- *.
    pose proof (req_size_pos (klen + 1 + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr2). unfold HEAD in *. lia. }
assert (HDZ' : zbytes_at tfibsegs W' mem' dec (c_bs cx)).
{ apply (crtB2_zbytes_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
    ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh dec (c_bs cx)
    (dec - HEAD) (FSH_Fn_writer.dec_size tb2 + HEAD) HinD (fun H => H)); [unfold HEAD; lia | | exact HDZc].
  pose proof (crtB2_bs_dec (c_bs cx)) as Hbd. fold tb2 len in Hbd.
  pose proof (req_size_pos (FSH_Fn_writer.dec_size tb2 + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr1).
  unfold HEAD in *. lia. }
assert (HTS' : rtree tfibsegs B ly' S' W' mem' (F + 0x80) (PjTree.JObj mss) Dst).
{ apply (crtB2_rtree_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
    ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh); [rewrite EF; lia | rewrite EF; lia
    | intros x Hx; apply (HnoFR (F + 0x80) (F + 0x80 + 56)); lia | intros bk _ [] | exact HPSc | exact HTSc]. }
assert (POBJ : forall o, 0 <= o -> o + 56 <= 512 -> (o + 56 <= 0x20 + 24 \/ 0x20 + 56 <= o) ->
  (o + 56 <= 0xe0 \/ 0x118 <= o) ->
  pobj tfibsegs B ly3 S3 W3 memC (F + o) -> pobj tfibsegs B ly' S' W' mem' (F + o)).
{ intros o Ho0 Ho1 Ho2 Ho3 Hpo.
  apply (crtB2_pobj_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
    ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh); [rewrite EF; lia | rewrite EF; lia
    | intros x Hx; apply (HnoFR (F + o) (F + o + 56)); lia | exact HHD' | exact Hpo]. }
destruct (crtB2_n0_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
  ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh (F + 0x1a0)
  ltac:(rewrite EF; exact HF32) ltac:(rewrite EF; reflexivity)
  ltac:(intros x Hx; apply (HnoFR (F + 0x1a0) (F + 0x1a0 + 8)); lia) HARU' HN0c HN0ac) as (HN0' & HN0a').
(* the new boundary *)
clear HSR.
cbn [crtB2_inv]. fold F len tb2.
set (E' := Ereg regs' (crt_extra cx)).
assert (EK : forall nn : nat, (18 <= nn <= 27)%nat -> ew E' nn = ew E nn)
  by (intros nn Hnn; exact (crtB2_env_kept E ssC regsC regs' (crt_extra cx) nn Hnn GS RG HP)).
split; [intros _; subst E'; rewrite (ew_Ereg_nat regs' (crt_extra cx) 10 10%bv eq_refl); exact R10'|].
rewrite (EK 18%nat ltac:(lia)), (EK 20%nat ltac:(lia)), (EK 21%nat ltac:(lia)), (EK 22%nat ltac:(lia)),
  (EK 23%nat ltac:(lia)), (EK 26%nat ltac:(lia)), (EK 27%nat ltac:(lia)).
split; [exact E18|]. split; [exact E20|]. split; [exact E21|]. split; [exact E22|]. split; [exact E23|].
split; [exact E26|]. split; [exact E27|].
exists same, nsame, dec, Do, Dst, [], (live + PjGrammar.held tr), peak', (cnt + Z.of_nat (length tr)).
rewrite (EK 24%nat ltac:(lia)), (EK 25%nat ltac:(lia)).
split; [exact E24|]. split; [exact E25|].
assert (HPD3 : Permutation (Dst ++ [(av, n)] ++ [(k', 56 * 8); (y', 8 * 8)] ++ [(a, klen + 1)]) (Do ++ Dst ++ [])).
{ rewrite app_nil_r. eapply Permutation_trans; [apply Permutation_app_comm|]. apply Permutation_app_tail.
  apply Permutation_sym. eapply Permutation_trans; [exact HPDo|]. cbn [app].
  apply Permutation_sym, (Permutation_cons_append [(k', 56 * 8); (y', 8 * 8); (a, klen + 1)] (av, n)). }
split.
{ eapply Permutation_trans; [exact HBL'|]. eapply Permutation_trans; [apply Permutation_app_tail; exact HPB|].
  rewrite <- !app_assoc. apply Permutation_app_head. cbn [app]. do 4 apply perm_skip.
  unfold X, rd_hblocks. rewrite <- !map_app. apply Permutation_map. rewrite <- !app_assoc. cbn [app] in HPD3 |- *.
  exact HPD3. }
split.
{ unfold U'. rewrite <- !app_assoc. eapply Permutation_trans; [apply Permutation_app_tail; exact HPU|].
  rewrite <- !app_assoc. apply Permutation_app_head. cbn [app]. do 2 apply perm_skip.
  assert (EH : [(k' - HEAD, HEAD); (y' - HEAD, HEAD); (a - HEAD, HEAD)] =
    rd_heads ([(k', 56 * 8); (y', 8 * 8)] ++ [(a, klen + 1)])) by reflexivity.
  rewrite EH. unfold rd_heads. rewrite <- map_app. apply Permutation_map.
  rewrite <- !app_assoc. cbn [app] in HPD3 |- *. exact HPD3. }
split; [exact HHD'|].
split; [exact HTX'|]. split; [exact (proj1 (proj1 HTC'))|]. split; [exact HTC'|].
split; [exact HDC'|]. split; [exact HDZ'|].
split; [cbn [PjTree.pj_set_model] in HTDo; exact HTDo|].
split.
{ eapply Permutation_trans; [apply Permutation_map; exact HPDo|]. cbn [map app snd]. apply Permutation_refl. }
split; [exact HTS'|]. split; [exact HSS|].
split; [cbn [crtB2_vfact]; split; [reflexivity | exact HZw]|].
split; [exact HPo|].
split; [exact (POBJ 0x80 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HPSc)|].
split; [exact HPw|].
split; [exact (POBJ 0x140 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HPKc)|].
split; [exact HN0'|]. split; [exact HN0a'|].
split; [exact HG'|].
split.
{ rewrite Hheld, Hlive, Hrsum, app_nil_r, crt_rd_sum_app, (crtB2_rd_sum_sizes Dst ss HSS).
  rewrite (crtB2_rd_sum_sizes Do [56 * 8; 8 * 8; klen + 1; n]); [cbn [fold_right]; unfold n, len, tb2 in *; lia|].
  eapply Permutation_trans; [apply Permutation_map; exact HPDo|]. cbn [map app snd]. apply Permutation_refl. }
split.
{ rewrite (blocks_bytes_bsum B ly' S'), (crtB2_bsum_perm _ _ HBL'), bsum_app, <- (blocks_bytes_bsum B ly3 S3).
  unfold X. cbn [rd_hblocks map app bsum fold_right fst snd]. rewrite Hrl in BL. unfold HEAD, n, len, tb2 in *. lia. }
split; [unfold tr, klen in *; lia|]. unfold tr, klen in *; lia.
Qed.

(* on state (F + 0x80): doc kept *)
Lemma crtB2_hcall_set0_st : forall ssC r k (kname cs : list Z) msd sd (K CNT LIVE K' CNT' LIVE' : crt_cx -> Z),
  let klen := Z.of_nat (length kname) in let tr := pj_set_c.set_trace 0 0 klen in
  crt_ssave ssC ->
  sr_get (ss_regs ssC) 1%bv = SLit r -> sr_get (ss_regs ssC) 2%bv = SOff 2 0 ->
  sr_get (ss_regs ssC) 10%bv = SOff 23 0 -> sr_get (ss_regs ssC) 11%bv = SLit k ->
  sr_get (ss_regs ssC) 12%bv = SOff 22 0 ->
  0 <= r < 2 ^ 64 ->
  In (k, kname) FS_RO_STRS -> 0x10000 <= k -> k + klen + 1 <= FS_IMG_END ->
  klen + 1 + HEAD < MALLOC_MAX ->
  PjGrammar.held tr = 56 * 8 + 8 * 8 + (klen + 1) ->
  rd_live tr = (56 * 8 + HEAD) + (8 * 8 + HEAD) + (klen + 1 + HEAD) ->
  (forall cx, crt_base B cx ->
     K cx + rd_ev tr <= K' cx /\ CNT cx + Z.of_nat (length tr) <= CNT' cx /\ LIVE cx + rd_live tr <= LIVE' cx /\
     K' cx <= EV_check_round_trip /\ CNT' cx <= EV_check_round_trip /\ LIVE' cx <= LIVE_check_round_trip /\
     FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) +
       fold_right Z.add 0 sd + (Z.of_nat (length cs) + 1) + rd_live tr <= LIVE_check_round_trip) ->
  crt_hcall SK B ssC A_pj_set r STK_pj_set (crtB2_inv B true msd sd [] [] (VStr cs) K CNT LIVE)
    (crtB2_inv B true msd sd [(kname, PjTree.JStr cs)] [56 * 8; 8 * 8; klen + 1; Z.of_nat (length cs) + 1] VZero
       K' CNT' LIVE').
Proof.
intros ssC r k kname cs msd sd K CNT LIVE K' CNT' LIVE' klen tr GS G1 G2 G10 G11 G12 Hr Hstr Hk0 Hk1 Hmx
  Hheld Hrl HBUD.
intros cx E kk ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (HBUD cx HB) as (BK & BC & BL & BK' & BC' & BL' & BLV).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E19 & EX).
destruct HINV as (_ & E18 & E20 & E21 & E22 & E23 & E26 & E27 & same & nsame & dec & Ddoc & Dst & Dv & live & peak & cnt &
  E24 & E25 & HPB & HPU & HHD & HTX & HTZ & HTC & HDC & HDZ & HTD & HSD & HTS & HSS & HVF & HPD & HPS & HPV & HPK &
  HN0 & HN0a & HG & HL & HBB & HCNT & HK).
apply Permutation_sym, Permutation_nil, map_eq_nil in HSS. subst Dst.
cbn [crtB2_vfact] in HVF. destruct HVF as ((av & ->) & HTV).
set (F := crt_F cx) in *. set (m3 := ms_mem ms3) in *.
set (len := Z.of_nat (length (c_bs cx))) in *. set (tb2 := WriterSpec.b64_enc (c_bs cx)) in *.
set (n := Z.of_nat (length cs) + 1) in *.
pose proof HJC as (HARj & Hly3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (crt_F_ly cx _ ly3 Hly3) as EF.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (crt_F_facts SK B cx _ _ _ _ _ _ _ HJC HARUC Hfr) as (HF32 & HF0 & HFc & HFapp & _ & _).
fold F in HF32, HF0, HFc, HFapp.
assert (Hsp1 : spZ (c_regs cx) - 208 <= crt_sp1 cx <= spZ (c_regs cx) - 192).
{ destruct (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
    as (F1 & _ & _). unfold crt_sp1. lia. }
pose proof crt_STK_eq as STKv; unfold crt_STK in STKv.
assert (STKs : STK_pj_set + 208 <= STK_check_round_trip) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Esp : spZ regsC = crt_sp1 cx) by (unfold spZ; rewrite RG, G2, fsw_SOff0; exact E2).
assert (R1 : YK11.getr regsC 1%bv = Z_to_bv 64 r) by (rewrite RG, G1; reflexivity).
assert (Rra : raZ regsC = r) by (unfold raZ; rewrite R1; apply wz; lia).
assert (HTDc : rtree tfibsegs B ly3 S3 W3 memC (F + 0x20) (PjTree.JObj msd) Ddoc)
  by exact (rnode_below B ly3 S3 W3 _ mdC m3 memC Ddoc (F + 0x20) _ Ddoc HARC HSB ltac:(lia) ltac:(lia) HTD).
assert (HTSc : rtree tfibsegs B ly3 S3 W3 memC (F + 0x80) (PjTree.JObj []) [])
  by exact (rnode_below B ly3 S3 W3 _ mdC m3 memC [] (F + 0x80) _ [] HARC HSB ltac:(lia) ltac:(lia) HTS).
assert (HTVc : rtree tfibsegs B ly3 S3 W3 memC (F + 0xe0) (PjTree.JStr cs) [(av, n)])
  by exact (rnode_below B ly3 S3 W3 _ mdC m3 memC [(av, n)] (F + 0xe0) _ [(av, n)] HARC HSB ltac:(lia) ltac:(lia) HTV).
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPD) as HPDc.
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPS) as HPSc.
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPV) as HPVc.
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPK) as HPKc.
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC m3 memC _ _ HARC HSB HTX) as HTXc.
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC m3 memC _ _ HARC HSB HDC) as HDCc.
pose proof (cstr_ok_below W3 m3 memC _ _ HSB HTC) as HTCc.
pose proof (fs_glob_below W3 m3 memC _ _ _ _ HSB HG) as HGc.
pose proof (val_mem_below (w_H W3) m3 memC alloc_ceiling (F + 0x1a0) 8 0 HSB ltac:(lia) ltac:(cbn; lia) HN0) as HN0c.
pose proof (fsw_range_addressable_below (w_H W3) m3 memC (F + 0x1a0) 8 HSB ltac:(lia) ltac:(lia) HN0a) as HN0ac.
pose proof HDC as (HinD & _ & HdecK & _).
pose proof (fsw_rblock_low B ly3 S3 W3 _ mdC m3 dec _ HARC HDC) as (Hdl0 & Hdl1).
assert (HDZc : zbytes_at tfibsegs W3 memC dec (c_bs cx)).
{ unfold zbytes_at in *. apply (garr8_frame tfibsegs _ _ dec (c_bs cx) HDZ). intros a Ha.
  apply (mbyte_below (w_H W3) m3 memC alloc_ceiling a HSB). pose proof (crtB2_bs_dec (c_bs cx)) as Hb.
  unfold tb2, len, HEAD in *. lia. }
assert (HGc0 : 0 <= live /\ 0 <= cnt) by (pose proof HGc as (_ & _ & _ & _ & HL0 & _ & HC0 & _); lia).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HQ1 & HQ2 & HQ3) & HLV0 & _ &
  _ & HNEV0 & HBB0).
assert (Hrsum : rd_sum (Ddoc ++ [] ++ [(av, n)]) = fold_right Z.add 0 sd + n).
{ cbn [app]. rewrite crt_rd_sum_app, (crtB2_rd_sum_sizes Ddoc sd HSD). unfold rd_sum. cbn [fold_right snd]. lia. }
pose proof HTVc as (_ & HBv & _). destruct (HBv av n (or_introl eq_refl)) as (HinV & _ & Hn0 & _).
pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 _ mdC (av - HEAD) (n + HEAD) 3 (c_pos cx) HARC HinV Hin3) as HdV.
unfold zdisjoint in HdV. cbn [fst snd] in HdV. rewrite EF, crt_frame3 in HdV. fold F in HdV.
pose proof (req_size_pos (n + HEAD) ltac:(unfold HEAD; lia)) as (_ & HrqV).
pose proof (fsw_ablock_off_img B ly3 S3 W3 _ mdC (av - HEAD) (n + HEAD) HARC HinV) as HimgV.
pose proof (fsw_pobj_off_img B ly3 S3 W3 _ mdC memC _ HARC HPSc) as HimgO.
pose proof (fsw_pobj_off_img B ly3 S3 W3 _ mdC memC _ HARC HPVc) as HimgW.
destruct (crtB2_obj0_hdr B ly3 S3 W3 memC (F + 0x80) HTSc) as (num & str & Hh).
assert (Hlive : live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + rd_sum (Ddoc ++ [] ++ [(av, n)]))
  by exact HL.
assert (HSR := PJ_SET ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) (F + 0x80) k (F + 0xe0) [] (PjTree.JStr cs) []
  [(av, n)] num str 0 0 0 0 kname live peak cnt SIZE_MAXZ
  HPREc HHD
  ltac:(rewrite RG, G10, fsw_SOff0; exact E23)
  ltac:(rewrite RG, G11; reflexivity)
  ltac:(rewrite RG, G12, fsw_SOff0; exact E22)
  HTSc HPSc Hh ltac:(lia) ltac:(intros x Hx; destruct Hx)
  HTVc HPVc ltac:(intros bk _ Hbk; destruct Hbk)
  ltac:(intros x Hx [Hf | (b & Hb & _)]; [lia | destruct Hb])
  ltac:(intros b x [<- | []] Hx Hox; unfold PjStruct.pj_holds in Hx; cbn [fst snd] in Hx; unfold HEAD in *; lia)
  ltac:(left; rewrite Esp; lia) ltac:(left; rewrite Esp; lia)
  (FSW_strkit.cstr_ok_kept_tbl B ly3 S3 U3 W3 memC mdC k kname IMG HARUC (proj2 HPREc) (or_introl Hstr))
  ltac:(right; left; exact Hstr)
  ltac:(intros x Hx; split; [intros [Hf | (b & Hb & _)]; [lia | destruct Hb] | intros [Hf | (b & [<- | []] & Hb)];
    [lia | unfold PjStruct.pj_holds in Hb; cbn [fst snd] in Hb; unfold HEAD in *; lia]])
  ltac:(intros Hx; destruct Hx)
  HGc ltac:(split; [reflexivity | unfold tr, klen in *; lia])
  ltac:(exact (crt_pjset_dold0_1a8 B cx ly3 S3 W3 memC [] Ddoc [] [(av, n)] num str 0 0 0 0 live HB HTSc
    (crtB2_rbo_cat B ly3 S3 W3 memC Ddoc [(av, n)] (proj1 (proj2 HTDc)) (proj1 (proj2 HTVc))) Hh Hlive))
  Hmx ltac:(intros _; apply Z.ltb_lt; vm_compute; reflexivity)
  ltac:(unfold tr, klen in *; rewrite Hrl, Hlive, Hrsum; lia) ltac:(unfold tr, klen in *; lia)
  ltac:(unfold tr, klen in *; lia)).
exists ([(F + 0x80 + 24, F + 0x80 + 56); (F + 0xe0, F + 0xe0 + 56)] ++ ablocks_fp (rd_hblocks []) ++ FS_PSTAT_FP), (rd_ev tr).
eexists. split; [exact HSR|].
split.
{ pose proof (crtB2_fpsub_pjset B (c_ly cx) (c_S cx) ly3 S3 (c_pos cx) 0x80 0xe0 [] ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(intros bk [])) as X.
  rewrite EF in X. exact X. }
split.
{ intros a Ha. rewrite crt_frame3 in Ha.
  apply (crtB2_tail_free B ly3 S3 W3 _ mdC (c_pos cx) _ HARC Hin3); rewrite EF; fold F.
  - intros x Hx. apply inFP_app in Hx as [Hx|Hx]; [left|].
    + apply inFP_cons in Hx as [Hx|Hx]; [lia|]. apply inFP_cons in Hx as [Hx|Hx]; [lia | exfalso; exact (inFP_nil x Hx)].
    + right; right. apply inFP_app in Hx as [Hx|Hx]; [exfalso; exact (inFP_nil x Hx) | exact Hx].
  - lia. }
intros W' c' (k' & y' & cap' & Dold & Dnew & Dr & Do & Ug & a & HGR & HPDr & HPDo & ly' & S' & regs' & mem' & md' &
  Ec & HJc & OK' & PO' & HP & R10' & Ha & HBL & HTDo & HZw & HPo & HPw & HKok' & peak' & Hpk & HG').
exists ly', S', (Ug ++ [(a - HEAD, HEAD)]), regs', mem', md'.
split; [exact Ec|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' HARU'.
pose proof (proj1 HJc) as HAR'.
destruct HGR as [(Hlt & _) | (_ & Ecap & EDold & Hk1' & Hk2' & Hy & _ & EDnew & Um & HU1 & HU2)]; [lia|].
cbn [ReaderRes.cap2 Z.eqb] in Ecap. subst cap'.
cbn [ReaderRes.kids_blk ReaderRes.keys_blk Z.eqb orb negb app] in EDold. subst Dold.
cbn [Z.eqb] in EDnew, HU2. subst Dnew.
destruct HU1 as [(_ & ->) | (Hne & _)]; [|lia]. destruct HU2 as [(_ & ->) | (Hne & _)]; [|lia].
apply Permutation_nil, app_eq_nil in HPDr as (_ & ->).
destruct (Hy eq_refl) as (Hy1 & Hy2).
set (U' := ((U3 ++ [(k' - HEAD, HEAD)]) ++ [(y' - HEAD, HEAD)]) ++ [(a - HEAD, HEAD)]) in *.
set (X := rd_hblocks ([(k', 56 * 8); (y', 8 * 8)] ++ [(a, klen + 1)])).
assert (HBL' : Permutation (ablocks B ly' S') (ablocks B ly3 S3 ++ X)).
{ cbn [rd_hblocks map app] in HBL. rewrite app_nil_r in HBL. exact HBL. }
set (FR := [(F + 0x80 + 24, F + 0x80 + 56); (F + 0xe0, F + 0xe0 + 56)]).
assert (HJcF : ajournal tfibsegs B STK_pj_set (spZ regsC) (FR ++ ablocks_fp [] ++ FS_PSTAT_FP) ly3 S3 W3
  (unpoison U3 memC) mdC [] ly' S' W' (unpoison U' mem') md' (rd_ev tr)) by exact HJc.
assert (HFRf : forall x, inFP FR x -> frame_addr ly3 3 (c_pos cx) <= x < frame_addr ly3 3 (c_pos cx) + 512).
{ intros x Hx. rewrite EF. apply inFP_cons in Hx as [Hx|Hx]; [lia|].
  apply inFP_cons in Hx as [Hx|Hx]; [lia | exfalso; exact (inFP_nil x Hx)]. }
assert (HDh : forall bk, In bk (@nil (Z * Z)) -> In bk (ablocks B ly3 S3)) by (intros bk []).
assert (HnoFR : forall lo hi x, lo <= x < hi -> (hi <= F + 0x80 + 24 \/ F + 0x80 + 56 <= lo) ->
  (hi <= F + 0xe0 \/ F + 0xe0 + 56 <= lo) -> ~ inFP FR x).
{ intros lo hi x Hx Hd1 Hd2 Hf. apply inFP_cons in Hf as [Hf|Hf]; [lia|].
  apply inFP_cons in Hf as [Hf|Hf]; [lia | exact (inFP_nil x Hf)]. }
assert (HinX : forall bk, In bk X -> In bk (ablocks B ly' S')).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HBL')). apply in_or_app. right. exact Hbk. }
assert (Hin3' : forall bk, In bk (ablocks B ly3 S3) -> In bk (ablocks B ly' S')).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HBL')). apply in_or_app. left. exact Hbk. }
assert (HHD' : FSupoisonU.fs_heads B ly' S' U').
{ intros q Hq. unfold U' in Hq. rewrite <- !app_assoc in Hq. apply in_app_or in Hq as [Hq|Hq].
  - destruct (HHD q Hq) as (H16 & m & Hm & Hrm). split; [exact H16|]. exists m. split; [exact (Hin3' _ Hm) | exact Hrm].
  - cbn [app In] in Hq. destruct Hq as [<-|[<-|[<-|[]]]]; (split; [reflexivity|]); cbn [fst].
    + exists (56 * 8 + HEAD). split; [apply HinX; cbn; left; reflexivity|].
      unfold req_size, HEAD. destruct (Z.eqb_spec (56 * 8 + 16) 0); lia.
    + exists (8 * 8 + HEAD). split; [apply HinX; cbn; right; left; reflexivity|].
      unfold req_size, HEAD. destruct (Z.eqb_spec (8 * 8 + 16) 0); lia.
    + exists (klen + 1 + HEAD). split; [apply HinX; cbn; right; right; left; reflexivity|].
      unfold req_size, HEAD. destruct (Z.eqb_spec (klen + 1 + 16) 0); lia. }
pose proof HTX as (HinT & _ & HTk & _).
assert (Htb2 : Z.of_nat (length tb2) + 1 = FSH_Fn_writer.enc_size len) by exact (crtB2_enc_tb2 (c_bs cx)).
assert (HTX' := crtB2_rblock_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
  ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh _ _ HTXc (fun H => H)).
assert (HDC' := crtB2_rblock_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
  ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh _ _ HDCc (fun H => H)).
assert (HTC' : cstr_ok tfibsegs W' mem' (c_text cx) tb2).
{ apply (crtB2_cstr_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
    ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh (c_text cx) tb2
    (c_text cx - HEAD) (FSH_Fn_writer.enc_size len + HEAD) HinT (fun H => H)); [unfold HEAD; lia | unfold HEAD; lia | |
    exact HTCc].
  intros q Hq. unfold U' in Hq. rewrite <- !app_assoc in Hq. apply in_app_or in Hq as [Hq|Hq]; [left; exact Hq | right].
  assert (AP : forall y, In y X -> zdisjoint (block_rng (c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD)) (block_rng y))
    by (intros yy Hyy; exact (crtB2_apart_app B ly' S' W' _ md' _ _ _ yy HAR' HBL' HinT Hyy)).
  pose proof (req_size_pos (FSH_Fn_writer.enc_size len + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr1).
  cbn [app In] in Hq. destruct Hq as [<-|[<-|[<-|[]]]].
  + pose proof (AP _ (or_introl eq_refl)) as Hd. unfold block_rng, zdisjoint in Hd. cbn [fst snd] in Hd |- *.
    pose proof (req_size_pos (56 * 8 + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr2). unfold HEAD in *. lia.
  + pose proof (AP _ (or_intror (or_introl eq_refl))) as Hd. unfold block_rng, zdisjoint in Hd. cbn [fst snd] in Hd |- *.
    pose proof (req_size_pos (8 * 8 + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr2). unfold HEAD in *. lia.
  + pose proof (AP _ (or_intror (or_intror (or_introl eq_refl)))) as Hd. unfold block_rng, zdisjoint in Hd.
    cbn [fst snd] in Hd |- *.
    pose proof (req_size_pos (klen + 1 + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr2). unfold HEAD in *. lia. }
assert (HDZ' : zbytes_at tfibsegs W' mem' dec (c_bs cx)).
{ apply (crtB2_zbytes_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
    ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh dec (c_bs cx)
    (dec - HEAD) (FSH_Fn_writer.dec_size tb2 + HEAD) HinD (fun H => H)); [unfold HEAD; lia | | exact HDZc].
  pose proof (crtB2_bs_dec (c_bs cx)) as Hbd. fold tb2 len in Hbd.
  pose proof (req_size_pos (FSH_Fn_writer.dec_size tb2 + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr1).
  unfold HEAD in *. lia. }
assert (HTD' : rtree tfibsegs B ly' S' W' mem' (F + 0x20) (PjTree.JObj msd) Ddoc).
{ apply (crtB2_rtree_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
    ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh); [rewrite EF; lia | rewrite EF; lia
    | intros x Hx; apply (HnoFR (F + 0x20) (F + 0x20 + 56)); lia | intros bk _ [] | exact HPDc | exact HTDc]. }
assert (POBJ : forall o, 0 <= o -> o + 56 <= 512 -> (o + 56 <= 0x80 + 24 \/ 0x80 + 56 <= o) ->
  (o + 56 <= 0xe0 \/ 0x118 <= o) ->
  pobj tfibsegs B ly3 S3 W3 memC (F + o) -> pobj tfibsegs B ly' S' W' mem' (F + o)).
{ intros o Ho0 Ho1 Ho2 Ho3 Hpo.
  apply (crtB2_pobj_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
    ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh); [rewrite EF; lia | rewrite EF; lia
    | intros x Hx; apply (HnoFR (F + o) (F + o + 56)); lia | exact HHD' | exact Hpo]. }
destruct (crtB2_n0_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR [] ly3 S3 U3 W3 memC mdC
  ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh (F + 0x1a0)
  ltac:(rewrite EF; exact HF32) ltac:(rewrite EF; reflexivity)
  ltac:(intros x Hx; apply (HnoFR (F + 0x1a0) (F + 0x1a0 + 8)); lia) HARU' HN0c HN0ac) as (HN0' & HN0a').
clear HSR.
cbn [crtB2_inv]. fold F len tb2.
set (E' := Ereg regs' (crt_extra cx)).
assert (EK : forall nn : nat, (18 <= nn <= 27)%nat -> ew E' nn = ew E nn)
  by (intros nn Hnn; exact (crtB2_env_kept E ssC regsC regs' (crt_extra cx) nn Hnn GS RG HP)).
split; [intros _; subst E'; rewrite (ew_Ereg_nat regs' (crt_extra cx) 10 10%bv eq_refl); exact R10'|].
rewrite (EK 18%nat ltac:(lia)), (EK 20%nat ltac:(lia)), (EK 21%nat ltac:(lia)), (EK 22%nat ltac:(lia)),
  (EK 23%nat ltac:(lia)), (EK 26%nat ltac:(lia)), (EK 27%nat ltac:(lia)).
split; [exact E18|]. split; [exact E20|]. split; [exact E21|]. split; [exact E22|]. split; [exact E23|].
split; [exact E26|]. split; [exact E27|].
exists same, nsame, dec, Ddoc, Do, [], (live + PjGrammar.held tr), peak', (cnt + Z.of_nat (length tr)).
rewrite (EK 24%nat ltac:(lia)), (EK 25%nat ltac:(lia)).
split; [exact E24|]. split; [exact E25|].
assert (HPD3 : Permutation (Ddoc ++ [(av, n)] ++ [(k', 56 * 8); (y', 8 * 8)] ++ [(a, klen + 1)]) (Ddoc ++ Do ++ [])).
{ rewrite app_nil_r. apply Permutation_app_head.
  apply Permutation_sym. eapply Permutation_trans; [exact HPDo|]. cbn [app].
  apply Permutation_sym, (Permutation_cons_append [(k', 56 * 8); (y', 8 * 8); (a, klen + 1)] (av, n)). }
split.
{ eapply Permutation_trans; [exact HBL'|]. eapply Permutation_trans; [apply Permutation_app_tail; exact HPB|].
  rewrite <- !app_assoc. apply Permutation_app_head. cbn [app]. do 4 apply perm_skip.
  unfold X, rd_hblocks. rewrite <- !map_app. apply Permutation_map. rewrite <- !app_assoc. cbn [app] in HPD3 |- *.
  exact HPD3. }
split.
{ unfold U'. rewrite <- !app_assoc. eapply Permutation_trans; [apply Permutation_app_tail; exact HPU|].
  rewrite <- !app_assoc. apply Permutation_app_head. cbn [app]. do 2 apply perm_skip.
  assert (EH : [(k' - HEAD, HEAD); (y' - HEAD, HEAD); (a - HEAD, HEAD)] =
    rd_heads ([(k', 56 * 8); (y', 8 * 8)] ++ [(a, klen + 1)])) by reflexivity.
  rewrite EH. unfold rd_heads. rewrite <- map_app. apply Permutation_map.
  rewrite <- !app_assoc. cbn [app] in HPD3 |- *. exact HPD3. }
split; [exact HHD'|].
split; [exact HTX'|]. split; [exact (proj1 (proj1 HTC'))|]. split; [exact HTC'|].
split; [exact HDC'|]. split; [exact HDZ'|].
split; [exact HTD'|]. split; [exact HSD|].
split; [cbn [PjTree.pj_set_model] in HTDo; exact HTDo|].
split.
{ eapply Permutation_trans; [apply Permutation_map; exact HPDo|]. cbn [map app snd]. apply Permutation_refl. }
split; [cbn [crtB2_vfact]; split; [reflexivity | exact HZw]|].
split; [exact (POBJ 0x20 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HPDc)|].
split; [exact HPo|].
split; [exact HPw|].
split; [exact (POBJ 0x140 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HPKc)|].
split; [exact HN0'|]. split; [exact HN0a'|].
split; [exact HG'|].
split.
{ rewrite Hheld, Hlive, Hrsum, app_nil_r, crt_rd_sum_app, (crtB2_rd_sum_sizes Ddoc sd HSD).
  rewrite (crtB2_rd_sum_sizes Do [56 * 8; 8 * 8; klen + 1; n]); [cbn [fold_right]; unfold n, len, tb2 in *; lia|].
  eapply Permutation_trans; [apply Permutation_map; exact HPDo|]. cbn [map app snd]. apply Permutation_refl. }
split.
{ rewrite (blocks_bytes_bsum B ly' S'), (crtB2_bsum_perm _ _ HBL'), bsum_app, <- (blocks_bytes_bsum B ly3 S3).
  unfold X. cbn [rd_hblocks map app bsum fold_right fst snd]. rewrite Hrl in BL. unfold HEAD, n, len, tb2 in *. lia. }
split; [unfold tr, klen in *; lia|]. unfold tr, klen in *; lia.
Qed.
End g.

(* ================= helpers of the no-grow pj_set step and of the boundary conversions ================= *)
Lemma crtB2_zsum_app : forall l1 l2, fold_right Z.add 0 (l1 ++ l2) = fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof. intros l1 l2. induction l1 as [|x l1 IH]; cbn [app fold_right]; lia. Qed.
Lemma crtB2_hb_app : forall l1 l2, rd_hblocks (l1 ++ l2) = rd_hblocks l1 ++ rd_hblocks l2.
Proof. intros l1 l2. unfold rd_hblocks. apply map_app. Qed.
Lemma crtB2_hb_in : forall D b, In b D -> In (fst b - HEAD, snd b + HEAD) (rd_hblocks D).
Proof. intros D b Hb. unfold rd_hblocks. apply in_map_iff. exists b. split; [reflexivity | exact Hb]. Qed.
Lemma crtB2_hb_pos : forall D x, (forall b, In b D -> 0 <= snd b) -> In x (rd_hblocks D) -> 0 < req_size (snd x).
Proof.
intros D x HD Hx. unfold rd_hblocks in Hx. apply in_map_iff in Hx as (b & <- & Hb). cbn [snd].
pose proof (HD b Hb) as H0. pose proof (req_size_pos (snd b + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr).
unfold HEAD in *. lia.
Qed.
(* the sizes of a block list, four at a time *)
Lemma crtB2_sizes4 : forall (D : list (Z * Z)) a b c d, Permutation (map snd D) [a; b; c; d] ->
  exists x y z w, Permutation D [(x, a); (y, b); (z, c); (w, d)].
Proof.
intros D a b c d H. apply Permutation_sym in H.
edestruct Permutation_map_inv as (l & El & Hp); [exact H|].
destruct l as [|[x a'] [|[y b'] [|[z c'] [|[w d'] [|? ?]]]]]; cbn [map snd] in El; try discriminate El.
injection El as <- <- <- <-. exists x, y, z, w. exact Hp.
Qed.
Section n3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Lemma crtB2_rbo_pos : forall ly S (W : world tfibsegs) mem D, rd_blocks_ok tfibsegs B ly S W mem D ->
  forall b, In b D -> 0 <= snd b.
Proof. intros ly S W mem D H [p k] Hb. destruct (H p k Hb) as (_ & _ & Hk & _). cbn [snd]. lia. Qed.
(* a block in both halves of a permutation of ablocks would be apart from itself *)
Lemma crtB2_hsep : forall ly S (W : world tfibsegs) mem md P Q x, AR tfibsegs B ly S W mem md ->
  Permutation (ablocks B ly S) (P ++ Q) -> In x P -> In x Q -> 0 < req_size (snd x) -> False.
Proof.
intros ly S W mem md P Q x HAR HP H1 H2 Hr.
pose proof (crtB2_apart_app B ly S W mem md P Q x x HAR HP H1 H2) as Hd.
destruct x as [b m]. unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd, Hr. lia.
Qed.
(* the walk's block list A ++ the reader blocks of three trees: no block twice *)
Lemma crtB2_hsep3 : forall ly S (W : world tfibsegs) mem md A D1 D2 D3, AR tfibsegs B ly S W mem md ->
  Permutation (ablocks B ly S) (A ++ rd_hblocks (D1 ++ D2 ++ D3)) ->
  (forall b, In b (D1 ++ D2 ++ D3) -> 0 <= snd b) ->
  (forall x, In x A -> In x (rd_hblocks (D1 ++ D2 ++ D3)) -> False) /\
  (forall x, In x (rd_hblocks D1) -> In x (rd_hblocks D2) -> False) /\
  (forall x, In x (rd_hblocks D1) -> In x (rd_hblocks D3) -> False) /\
  (forall x, In x (rd_hblocks D2) -> In x (rd_hblocks D3) -> False).
Proof.
intros ly S W mem md A D1 D2 D3 HAR HP HD.
assert (P1 : forall b, In b D1 -> 0 <= snd b) by (intros b Hb; apply HD; apply in_or_app; left; exact Hb).
assert (P2 : forall b, In b D2 -> 0 <= snd b)
  by (intros b Hb; apply HD; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (P3 : forall b, In b D3 -> 0 <= snd b)
  by (intros b Hb; apply HD; apply in_or_app; right; apply in_or_app; right; exact Hb).
rewrite !crtB2_hb_app in HP.
assert (HP12 : Permutation (ablocks B ly S) ((A ++ rd_hblocks D1) ++ (rd_hblocks D2 ++ rd_hblocks D3)))
  by (rewrite <- app_assoc; exact HP).
assert (HP3 : Permutation (ablocks B ly S) ((A ++ rd_hblocks D1 ++ rd_hblocks D2) ++ rd_hblocks D3))
  by (rewrite <- !app_assoc; exact HP).
split; [|split; [|split]].
- intros x Hx1 Hx2. rewrite !crtB2_hb_app in Hx2.
  apply (crtB2_hsep ly S W mem md A _ x HAR HP Hx1 Hx2).
  rewrite <- !crtB2_hb_app in Hx2. exact (crtB2_hb_pos _ x HD Hx2).
- intros x Hx1 Hx2. apply (crtB2_hsep ly S W mem md _ _ x HAR HP12);
    [apply in_or_app; right; exact Hx1 | apply in_or_app; left; exact Hx2 | exact (crtB2_hb_pos _ x P1 Hx1)].
- intros x Hx1 Hx3. apply (crtB2_hsep ly S W mem md _ _ x HAR HP3);
    [apply in_or_app; right; apply in_or_app; left; exact Hx1 | exact Hx3 | exact (crtB2_hb_pos _ x P1 Hx1)].
- intros x Hx2 Hx3. apply (crtB2_hsep ly S W mem md _ _ x HAR HP3);
    [apply in_or_app; right; apply in_or_app; right; exact Hx2 | exact Hx3 | exact (crtB2_hb_pos _ x P2 Hx2)].
Qed.
(* an object node whose blocks are carried by size: its header, with cap = 8 read off the kids block (the only
   multiple of 56 among the sizes), and its own two arrays at the head of its block list *)
Lemma crtB2_hdr8 : forall ly S (W : world tfibsegs) mem o ms D sz,
  rtree tfibsegs B ly S W mem o (PjTree.JObj ms) D -> Permutation (map snd D) sz ->
  (forall c, 0 < c -> In (56 * c) sz -> c = 8) -> ms <> [] ->
  exists num kids keys Di,
    PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem) o 6 num 0 kids keys (Z.of_nat (length ms)) 8 /\
    D = [(kids, 56 * 8); (keys, 8 * 8)] ++ Di.
Proof.
intros ly S W mem o ms D sz (HN & _ & _) HP H8 Hne.
cbn [PjStruct.pj_node PjTree.tag] in HN.
destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & Es & En & Hnc & _ & Di & ED & _).
assert (Hc0 : 0 < cap) by (destruct ms as [|m ms']; [congruence | cbn [length] in En; lia]).
rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
assert (Hin : In (56 * cap) sz) by (apply (Permutation_in _ HP); rewrite ED; cbn; left; reflexivity).
pose proof (H8 cap Hc0 Hin) as ->.
subst str n. exists num, kids, keys, Di. split; [exact Hh | exact ED].
Qed.
End n3.

(* ================= a pj_set call on an object that has room (segment 17, doc with n = 1, cap = 8): grow_res's first
   arm (no grow, Dold = Dnew = [], U unchanged), v's node moved in with the key's copy, v zeroed. Dold0 is the doc's own
   kids / keys pair, read back from the sizes (crtB2_hdr8): pj_set's FP holds those two heap blocks (written at slot n),
   so every kept block of the lane must be another block (crtB2_hsep3) ================= *)
Section g1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis PJ_SET : @pj_set_spec fx rc SK tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Lemma crtB2_hcall_set1_doc : forall ssC r k (kname cs : list Z) msd sd mss ss (K CNT LIVE K' CNT' LIVE' : crt_cx -> Z),
  let klen := Z.of_nat (length kname) in let nn := Z.of_nat (length msd) in
  let tr := pj_set_c.set_trace nn 8 klen in
  crt_ssave ssC ->
  sr_get (ss_regs ssC) 1%bv = SLit r -> sr_get (ss_regs ssC) 2%bv = SOff 2 0 ->
  sr_get (ss_regs ssC) 10%bv = SOff 26 0 -> sr_get (ss_regs ssC) 11%bv = SLit k ->
  sr_get (ss_regs ssC) 12%bv = SOff 22 0 ->
  0 <= r < 2 ^ 64 ->
  In (k, kname) FS_RO_STRS -> 0x10000 <= k -> k + klen + 1 <= FS_IMG_END ->
  klen + 1 + HEAD < MALLOC_MAX ->
  msd <> [] -> nn < 8 -> ~ In kname (map fst msd) ->
  (forall c, 0 < c -> In (56 * c) sd -> c = 8) ->
  PjGrammar.held tr = klen + 1 -> rd_live tr = klen + 1 + HEAD ->
  (forall cx, crt_base B cx ->
     K cx + rd_ev tr <= K' cx /\ CNT cx + Z.of_nat (length tr) <= CNT' cx /\ LIVE cx + rd_live tr <= LIVE' cx /\
     K' cx <= EV_check_round_trip /\ CNT' cx <= EV_check_round_trip /\ LIVE' cx <= LIVE_check_round_trip /\
     FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) +
       fold_right Z.add 0 sd + fold_right Z.add 0 ss + (Z.of_nat (length cs) + 1) + rd_live tr <= LIVE_check_round_trip) ->
  crt_hcall SK B ssC A_pj_set r STK_pj_set (crtB2_inv B true msd sd mss ss (VStr cs) K CNT LIVE)
    (crtB2_inv B true (PjTree.pj_set_model msd kname (PjTree.JStr cs)) (sd ++ [klen + 1; Z.of_nat (length cs) + 1])
       mss ss VZero K' CNT' LIVE').
Proof.
intros ssC r k kname cs msd sd mss ss K CNT LIVE K' CNT' LIVE' klen nn tr GS G1 G2 G10 G11 G12 Hr Hstr Hk0 Hk1 Hmx
  Hne Hnn Hkn H8 Hheld Hrl HBUD.
intros cx E kk ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (HBUD cx HB) as (BK & BC & BL & BK' & BC' & BL' & BLV).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E19 & EX).
destruct HINV as (_ & E18 & E20 & E21 & E22 & E23 & E26 & E27 & same & nsame & dec & Ddoc & Dst & Dv & live & peak & cnt &
  E24 & E25 & HPB & HPU & HHD & HTX & HTZ & HTC & HDC & HDZ & HTD & HSD & HTS & HSS & HVF & HPD & HPS & HPV & HPK &
  HN0 & HN0a & HG & HL & HBB & HCNT & HK).
cbn [crtB2_vfact] in HVF. destruct HVF as ((av & ->) & HTV).
set (F := crt_F cx) in *. set (m3 := ms_mem ms3) in *.
set (len := Z.of_nat (length (c_bs cx))) in *. set (tb2 := WriterSpec.b64_enc (c_bs cx)) in *.
set (n := Z.of_nat (length cs) + 1) in *.
pose proof HJC as (HARj & Hly3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (crt_F_ly cx _ ly3 Hly3) as EF.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (crt_F_facts SK B cx _ _ _ _ _ _ _ HJC HARUC Hfr) as (HF32 & HF0 & HFc & HFapp & _ & _).
fold F in HF32, HF0, HFc, HFapp.
assert (Hsp1 : spZ (c_regs cx) - 208 <= crt_sp1 cx <= spZ (c_regs cx) - 192).
{ destruct (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
    as (F1 & _ & _). unfold crt_sp1. lia. }
pose proof crt_STK_eq as STKv; unfold crt_STK in STKv.
assert (STKs : STK_pj_set + 208 <= STK_check_round_trip) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Esp : spZ regsC = crt_sp1 cx) by (unfold spZ; rewrite RG, G2, fsw_SOff0; exact E2).
assert (HTDc : rtree tfibsegs B ly3 S3 W3 memC (F + 0x20) (PjTree.JObj msd) Ddoc)
  by exact (rnode_below B ly3 S3 W3 _ mdC m3 memC Ddoc (F + 0x20) _ Ddoc HARC HSB ltac:(lia) ltac:(lia) HTD).
assert (HTSc : rtree tfibsegs B ly3 S3 W3 memC (F + 0x80) (PjTree.JObj mss) Dst)
  by exact (rnode_below B ly3 S3 W3 _ mdC m3 memC Dst (F + 0x80) _ Dst HARC HSB ltac:(lia) ltac:(lia) HTS).
assert (HTVc : rtree tfibsegs B ly3 S3 W3 memC (F + 0xe0) (PjTree.JStr cs) [(av, n)])
  by exact (rnode_below B ly3 S3 W3 _ mdC m3 memC [(av, n)] (F + 0xe0) _ [(av, n)] HARC HSB ltac:(lia) ltac:(lia) HTV).
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPD) as HPDc.
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPS) as HPSc.
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPV) as HPVc.
pose proof (pobj_below B ly3 S3 W3 _ mdC m3 memC _ HARC HSB HPK) as HPKc.
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC m3 memC _ _ HARC HSB HTX) as HTXc.
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC m3 memC _ _ HARC HSB HDC) as HDCc.
pose proof (cstr_ok_below W3 m3 memC _ _ HSB HTC) as HTCc.
pose proof (fs_glob_below W3 m3 memC _ _ _ _ HSB HG) as HGc.
pose proof (val_mem_below (w_H W3) m3 memC alloc_ceiling (F + 0x1a0) 8 0 HSB ltac:(lia) ltac:(cbn; lia) HN0) as HN0c.
pose proof (fsw_range_addressable_below (w_H W3) m3 memC (F + 0x1a0) 8 HSB ltac:(lia) ltac:(lia) HN0a) as HN0ac.
pose proof HDC as (HinD & _ & HdecK & _).
pose proof (fsw_rblock_low B ly3 S3 W3 _ mdC m3 dec _ HARC HDC) as (Hdl0 & Hdl1).
assert (HDZc : zbytes_at tfibsegs W3 memC dec (c_bs cx)).
{ unfold zbytes_at in *. apply (garr8_frame tfibsegs _ _ dec (c_bs cx) HDZ). intros a Ha.
  apply (mbyte_below (w_H W3) m3 memC alloc_ceiling a HSB). pose proof (crtB2_bs_dec (c_bs cx)) as Hb.
  unfold tb2, len, HEAD in *. lia. }
assert (HGc0 : 0 <= live /\ 0 <= cnt) by (pose proof HGc as (_ & _ & _ & _ & HL0 & _ & HC0 & _); lia).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HQ1 & HQ2 & HQ3) & HLV0 & _ &
  _ & HNEV0 & HBB0).
assert (Hrsum : rd_sum (Ddoc ++ Dst ++ [(av, n)]) = fold_right Z.add 0 sd + fold_right Z.add 0 ss + n).
{ rewrite !crt_rd_sum_app, (crtB2_rd_sum_sizes Ddoc sd HSD), (crtB2_rd_sum_sizes Dst ss HSS).
  replace (rd_sum [(av, n)]) with n by (unfold rd_sum; cbn [fold_right snd]; lia). lia. }
(* the v block, apart from the frame and off the image *)
pose proof HTVc as (_ & HBv & _). destruct (HBv av n (or_introl eq_refl)) as (HinV & _ & Hn0 & _).
pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 _ mdC (av - HEAD) (n + HEAD) 3 (c_pos cx) HARC HinV Hin3) as HdV.
unfold zdisjoint in HdV. cbn [fst snd] in HdV. rewrite EF, crt_frame3 in HdV. fold F in HdV.
pose proof (req_size_pos (n + HEAD) ltac:(unfold HEAD; lia)) as (_ & HrqV).
pose proof (fsw_ablock_off_img B ly3 S3 W3 _ mdC (av - HEAD) (n + HEAD) HARC HinV) as HimgV.
pose proof (fsw_pobj_off_img B ly3 S3 W3 _ mdC memC _ HARC HPDc) as HimgO.
pose proof (fsw_pobj_off_img B ly3 S3 W3 _ mdC memC _ HARC HPVc) as HimgW.
(* doc's header (cap = 8) and its own two arrays *)
destruct (crtB2_hdr8 B ly3 S3 W3 memC (F + 0x20) msd Ddoc sd HTDc HSD H8 Hne) as (num & kids & keys & Di & Hh & EDd).
pose (D0 := ReaderRes.kids_blk kids 8 ++ ReaderRes.keys_blk 6 keys 8).
assert (Hlive : live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + rd_sum (Ddoc ++ Dst ++ [(av, n)]))
  by exact HL.
(* no block twice: the walk's own blocks, doc's, the state's, v's *)
assert (HBoD : rd_blocks_ok tfibsegs B ly3 S3 W3 memC (Ddoc ++ Dst ++ [(av, n)]))
  by exact (crtB2_rbo_cat B _ _ _ _ _ _ (proj1 (proj2 HTDc)) (crtB2_rbo_cat B _ _ _ _ _ _ (proj1 (proj2 HTSc)) (proj1 (proj2 HTVc)))).
pose proof HPB as HPB'. rewrite app_assoc in HPB'.
destruct (crtB2_hsep3 B ly3 S3 W3 _ mdC _ Ddoc Dst [(av, n)] HARC HPB' (crtB2_rbo_pos B _ _ _ _ _ HBoD))
  as (SA & S12 & S13 & S23).
assert (Vnot : ~ In (av, n) Ddoc).
{ intros Hin. apply (S13 (av - HEAD, n + HEAD)); [exact (crtB2_hb_in Ddoc (av, n) Hin) |
    exact (crtB2_hb_in [(av, n)] (av, n) (or_introl eq_refl))]. }
assert (HDhD : forall bk, In bk (rd_hblocks D0) -> In bk (rd_hblocks Ddoc)).
{ intros bk Hbk. rewrite EDd, crtB2_hb_app. apply in_or_app. left. exact Hbk. }
assert (HDhX : forall bk, In bk (rd_hblocks D0) -> In bk (rd_hblocks (Ddoc ++ Dst ++ [(av, n)]))).
{ intros bk Hbk. rewrite crtB2_hb_app. apply in_or_app. left. exact (HDhD bk Hbk). }
assert (HDh : forall bk, In bk (rd_hblocks D0) -> In bk (ablocks B ly3 S3)).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPB')). apply in_or_app. right. exact (HDhX bk Hbk). }
assert (HDhA : forall bk, In bk (rd_hblocks D0) -> ~ In bk (ablocks B (c_ly cx) (c_S cx))).
{ intros bk Hbk Hin. apply (SA bk); [apply in_or_app; left; exact Hin | exact (HDhX bk Hbk)]. }
assert (HnT : ~ In (c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD) (rd_hblocks D0)).
{ intros Hin. apply (SA (c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD));
    [apply in_or_app; right; left; reflexivity | exact (HDhX _ Hin)]. }
assert (HnD : ~ In (dec - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD) (rd_hblocks D0)).
{ intros Hin. apply (SA (dec - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD));
    [apply in_or_app; right; right; right; right; left; reflexivity | exact (HDhX _ Hin)]. }
assert (HINCL : incl (rd_heads D0) U3).
{ intros q Hq. apply (Permutation_in _ (Permutation_sym HPU)). rewrite EDd. unfold rd_heads in *. rewrite !map_app.
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. apply in_or_app; left. exact Hq. }
(* the key, doc and v: apart *)
assert (Hfoot : forall x, F + 0xe0 <= x < F + 0xe0 + 56 -> ~ PjStruct.pj_foot (F + 0x20) Ddoc x).
{ intros x Hx [Hf | (b & Hb & Hh')]; [lia|]. destruct b as [p kb]. unfold PjStruct.pj_holds in Hh'. cbn [fst snd] in Hh'.
  destruct (proj1 (proj2 HTDc) p kb Hb) as (HinB & _ & Hkb & _).
  pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 _ mdC (p - HEAD) (kb + HEAD) 3 (c_pos cx) HARC HinB Hin3) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF, crt_frame3 in Hd. fold F in Hd.
  pose proof (req_size_pos (kb + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq). unfold HEAD in *. lia. }
assert (Hkey : forall x, k <= x < k + klen + 1 ->
  ~ PjStruct.pj_foot (F + 0x20) Ddoc x /\ ~ PjStruct.pj_foot (F + 0xe0) [(av, n)] x).
{ intros x Hx. split.
  - intros [Hf | (b & Hb & Hh')]; [lia|]. destruct b as [p kb]. unfold PjStruct.pj_holds in Hh'. cbn [fst snd] in Hh'.
    destruct (proj1 (proj2 HTDc) p kb Hb) as (HinB & _ & Hkb & _).
    pose proof (fsw_ablock_off_img B ly3 S3 W3 _ mdC (p - HEAD) (kb + HEAD) HARC HinB) as Hoi.
    pose proof (req_size_pos (kb + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq). unfold HEAD in *. lia.
  - intros [Hf | (b & [<- | []] & Hh')]; [lia | unfold PjStruct.pj_holds in Hh'; cbn [fst snd] in Hh'; unfold HEAD in *; lia]. }
assert (HSR := PJ_SET ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) (F + 0x20) k (F + 0xe0) msd (PjTree.JStr cs) Ddoc
  [(av, n)] num 0 kids keys nn 8 kname live peak cnt SIZE_MAXZ
  HPREc HHD
  ltac:(rewrite RG, G10, fsw_SOff0; exact E26)
  ltac:(rewrite RG, G11; reflexivity)
  ltac:(rewrite RG, G12, fsw_SOff0; exact E22)
  HTDc HPDc Hh ltac:(lia) HINCL
  HTVc HPVc ltac:(intros bk [<- | []]; exact Vnot) Hfoot
  ltac:(intros b x [<- | []] Hx Hox; unfold PjStruct.pj_holds in Hx; cbn [fst snd] in Hx; unfold HEAD in *; lia)
  ltac:(left; rewrite Esp; lia) ltac:(left; rewrite Esp; lia)
  (FSW_strkit.cstr_ok_kept_tbl B ly3 S3 U3 W3 memC mdC k kname IMG HARUC (proj2 HPREc) (or_introl Hstr))
  ltac:(right; left; exact Hstr)
  Hkey Hkn
  HGc ltac:(split; [reflexivity | unfold tr, klen, nn in *; lia])
  (crt_pjset_dold0_17c B cx ly3 S3 W3 memC msd Ddoc Dst [(av, n)] num 0 kids keys nn 8 live HB HTDc
    (crtB2_rbo_cat B ly3 S3 W3 memC Dst [(av, n)] (proj1 (proj2 HTSc)) (proj1 (proj2 HTVc))) Hh Hlive)
  Hmx ltac:(intros Hc; lia)
  ltac:(unfold tr, klen, nn in *; rewrite Hrl, Hlive, Hrsum; lia) ltac:(unfold tr, klen, nn in *; lia)
  ltac:(unfold tr, klen, nn in *; lia)).
exists ([(F + 0x20 + 24, F + 0x20 + 56); (F + 0xe0, F + 0xe0 + 56)] ++ ablocks_fp (rd_hblocks D0) ++ FS_PSTAT_FP),
  (rd_ev tr).
eexists. split; [exact HSR|].
split.
{ pose proof (crtB2_fpsub_pjset B (c_ly cx) (c_S cx) ly3 S3 (c_pos cx) 0x20 0xe0 D0 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(intros bk Hbk; split; [exact (HDh bk Hbk) | exact (HDhA bk Hbk)])) as X.
  rewrite EF in X. exact X. }
split.
{ intros a Ha. rewrite crt_frame3 in Ha.
  apply (crtB2_tail_free B ly3 S3 W3 _ mdC (c_pos cx) _ HARC Hin3); rewrite EF; fold F.
  - intros x Hx. apply inFP_app in Hx as [Hx|Hx]; [left|].
    + apply inFP_cons in Hx as [Hx|Hx]; [lia|]. apply inFP_cons in Hx as [Hx|Hx]; [lia | exfalso; exact (inFP_nil x Hx)].
    + apply inFP_app in Hx as [Hx|Hx]; [right; left | right; right; exact Hx].
      destruct Hx as (r0 & Hr0 & Hra). unfold ablocks_fp in Hr0. apply in_map_iff in Hr0 as ([b m] & <- & Hbm).
      cbn [fst snd] in Hra. exists b, m. split; [exact (HDh _ Hbm) | exact Hra].
  - lia. }
(* the return *)
intros W' c' (k' & y' & cap' & Dold & Dnew & Dr & Do & Ug & a & HGR & HPDr & HPDo & ly' & S' & regs' & mem' & md' &
  Ec & HJc & OK' & PO' & HP & R10' & Ha & HBL & HTDo & HZw & HPo & HPw & HKok' & peak' & Hpk & HG').
exists ly', S', (Ug ++ [(a - HEAD, HEAD)]), regs', mem', md'.
split; [exact Ec|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' HARU'.
pose proof (proj1 HJc) as HAR'.
(* room in doc: no grow *)
destruct HGR as [(Hlt & Ek' & Ey' & Ecap' & EDold & EDnew & EUg) | (Hcap & _)]; [| unfold nn in *; lia].
subst Dold Dnew Ug. cbn [app] in HPDr, HPDo.
set (U' := U3 ++ [(a - HEAD, HEAD)]) in *.
set (X := rd_hblocks [(a, klen + 1)]).
assert (HBL' : Permutation (ablocks B ly' S') (ablocks B ly3 S3 ++ X)).
{ cbn [rd_hblocks map app] in HBL. rewrite app_nil_r in HBL. exact HBL. }
set (FR := [(F + 0x20 + 24, F + 0x20 + 56); (F + 0xe0, F + 0xe0 + 56)]).
assert (HJcF : ajournal tfibsegs B STK_pj_set (spZ regsC) (FR ++ ablocks_fp (rd_hblocks D0) ++ FS_PSTAT_FP) ly3 S3 W3
  (unpoison U3 memC) mdC [] ly' S' W' (unpoison U' mem') md' (rd_ev tr)) by exact HJc.
assert (HFRf : forall x, inFP FR x -> frame_addr ly3 3 (c_pos cx) <= x < frame_addr ly3 3 (c_pos cx) + 512).
{ intros x Hx. rewrite EF. apply inFP_cons in Hx as [Hx|Hx]; [lia|].
  apply inFP_cons in Hx as [Hx|Hx]; [lia | exfalso; exact (inFP_nil x Hx)]. }
assert (HnoFR : forall lo hi x, lo <= x < hi -> (hi <= F + 0x20 + 24 \/ F + 0x20 + 56 <= lo) ->
  (hi <= F + 0xe0 \/ F + 0xe0 + 56 <= lo) -> ~ inFP FR x).
{ intros lo hi x Hx Hd1 Hd2 Hf. apply inFP_cons in Hf as [Hf|Hf]; [lia|].
  apply inFP_cons in Hf as [Hf|Hf]; [lia | exact (inFP_nil x Hf)]. }
assert (HinX : forall bk, In bk X -> In bk (ablocks B ly' S')).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HBL')). apply in_or_app. right. exact Hbk. }
assert (Hin3' : forall bk, In bk (ablocks B ly3 S3) -> In bk (ablocks B ly' S')).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HBL')). apply in_or_app. left. exact Hbk. }
(* the heads *)
assert (HHD' : FSupoisonU.fs_heads B ly' S' U').
{ intros q Hq. unfold U' in Hq. apply in_app_or in Hq as [Hq|[<-|[]]].
  - destruct (HHD q Hq) as (H16 & m & Hm & Hrm). split; [exact H16|]. exists m. split; [exact (Hin3' _ Hm) | exact Hrm].
  - split; [reflexivity|]. cbn [fst]. exists (klen + 1 + HEAD). split; [apply HinX; cbn; left; reflexivity|].
    unfold req_size, HEAD. destruct (Z.eqb_spec (klen + 1 + 16) 0); lia. }
(* text and dec *)
pose proof HTX as (HinT & _ & HTk & _).
assert (Htb2 : Z.of_nat (length tb2) + 1 = FSH_Fn_writer.enc_size len) by exact (crtB2_enc_tb2 (c_bs cx)).
assert (HTX' := crtB2_rblock_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR (rd_hblocks D0) ly3 S3 U3 W3 memC
  mdC ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh _ _ HTXc HnT).
assert (HDC' := crtB2_rblock_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR (rd_hblocks D0) ly3 S3 U3 W3 memC
  mdC ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh _ _ HDCc HnD).
assert (HTC' : cstr_ok tfibsegs W' mem' (c_text cx) tb2).
{ apply (crtB2_cstr_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR (rd_hblocks D0) ly3 S3 U3 W3 memC mdC
    ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh (c_text cx) tb2
    (c_text cx - HEAD) (FSH_Fn_writer.enc_size len + HEAD) HinT HnT); [unfold HEAD; lia | unfold HEAD; lia | |
    exact HTCc].
  intros q Hq. unfold U' in Hq. apply in_app_or in Hq as [Hq|[<-|[]]]; [left; exact Hq | right].
  pose proof (crtB2_apart_app B ly' S' W' _ md' _ _ _ (a - HEAD, klen + 1 + HEAD) HAR' HBL' HinT
    ltac:(unfold X; cbn; left; reflexivity)) as Hd.
  unfold block_rng, zdisjoint in Hd. cbn [fst snd] in Hd |- *.
  pose proof (req_size_pos (FSH_Fn_writer.enc_size len + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr1).
  pose proof (req_size_pos (klen + 1 + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr2). unfold HEAD in *. lia. }
assert (HDZ' : zbytes_at tfibsegs W' mem' dec (c_bs cx)).
{ apply (crtB2_zbytes_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR (rd_hblocks D0) ly3 S3 U3 W3 memC mdC
    ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh dec (c_bs cx)
    (dec - HEAD) (FSH_Fn_writer.dec_size tb2 + HEAD) HinD HnD); [unfold HEAD; lia | | exact HDZc].
  pose proof (crtB2_bs_dec (c_bs cx)) as Hbd. fold tb2 len in Hbd.
  pose proof (req_size_pos (FSH_Fn_writer.dec_size tb2 + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr1).
  unfold HEAD in *. lia. }
assert (HTS' : rtree tfibsegs B ly' S' W' mem' (F + 0x80) (PjTree.JObj mss) Dst).
{ apply (crtB2_rtree_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR (rd_hblocks D0) ly3 S3 U3 W3 memC mdC
    ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh); [rewrite EF; lia | rewrite EF; lia
    | intros x Hx; apply (HnoFR (F + 0x80) (F + 0x80 + 56)); lia
    | intros bk Hbk Hdh; exact (S12 bk (HDhD bk Hdh) Hbk) | exact HPSc | exact HTSc]. }
assert (POBJ : forall o, 0 <= o -> o + 56 <= 512 -> (o + 56 <= 0x20 + 24 \/ 0x20 + 56 <= o) ->
  (o + 56 <= 0xe0 \/ 0x118 <= o) ->
  pobj tfibsegs B ly3 S3 W3 memC (F + o) -> pobj tfibsegs B ly' S' W' mem' (F + o)).
{ intros o Ho0 Ho1 Ho2 Ho3 Hpo.
  apply (crtB2_pobj_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR (rd_hblocks D0) ly3 S3 U3 W3 memC mdC
    ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh); [rewrite EF; lia | rewrite EF; lia
    | intros x Hx; apply (HnoFR (F + o) (F + o + 56)); lia | exact HHD' | exact Hpo]. }
destruct (crtB2_n0_kept SK B STK_pj_set (spZ regsC) (rd_ev tr) (c_pos cx) FR (rd_hblocks D0) ly3 S3 U3 W3 memC mdC
  ly' S' U' W' mem' md' HJcF HARUC OK' PO' Hin3 HFRf HDh (F + 0x1a0)
  ltac:(rewrite EF; exact HF32) ltac:(rewrite EF; reflexivity)
  ltac:(intros x Hx; apply (HnoFR (F + 0x1a0) (F + 0x1a0 + 8)); lia) HARU' HN0c HN0ac) as (HN0' & HN0a').
(* the new boundary *)
clear HSR.
cbn [crtB2_inv]. fold F len tb2.
set (E' := Ereg regs' (crt_extra cx)).
assert (EK : forall nn : nat, (18 <= nn <= 27)%nat -> ew E' nn = ew E nn)
  by (intros nn0 Hnn0; exact (crtB2_env_kept E ssC regsC regs' (crt_extra cx) nn0 Hnn0 GS RG HP)).
split; [intros _; subst E'; rewrite (ew_Ereg_nat regs' (crt_extra cx) 10 10%bv eq_refl); exact R10'|].
rewrite (EK 18%nat ltac:(lia)), (EK 20%nat ltac:(lia)), (EK 21%nat ltac:(lia)), (EK 22%nat ltac:(lia)),
  (EK 23%nat ltac:(lia)), (EK 26%nat ltac:(lia)), (EK 27%nat ltac:(lia)).
split; [exact E18|]. split; [exact E20|]. split; [exact E21|]. split; [exact E22|]. split; [exact E23|].
split; [exact E26|]. split; [exact E27|].
exists same, nsame, dec, Do, Dst, [], (live + PjGrammar.held tr), peak', (cnt + Z.of_nat (length tr)).
rewrite (EK 24%nat ltac:(lia)), (EK 25%nat ltac:(lia)).
split; [exact E24|]. split; [exact E25|].
assert (HPD3 : Permutation (Ddoc ++ Dst ++ [(av, n)] ++ [(a, klen + 1)]) (Do ++ Dst ++ [])).
{ rewrite app_nil_r, HPDo, <- HPDr. cbn [app]. apply Permutation_sym.
  replace (Ddoc ++ Dst ++ [(av, n); (a, klen + 1)]) with ((Ddoc ++ Dst ++ [(av, n)]) ++ [(a, klen + 1)])
    by (rewrite <- !app_assoc; reflexivity).
  apply Permutation_cons_app. rewrite app_nil_r, <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
assert (HSo : Permutation (map snd Do) (sd ++ [klen + 1; n])).
{ assert (HSr : Permutation (map snd Dr) sd)
    by (eapply Permutation_trans; [apply Permutation_map; apply Permutation_sym; exact HPDr | exact HSD]).
  eapply Permutation_trans; [apply Permutation_map; exact HPDo|]. cbn [map snd]. rewrite map_app. cbn [map snd].
  rewrite HSr. apply Permutation_cons_app. apply Permutation_refl. }
split.
{ eapply Permutation_trans; [exact HBL'|]. eapply Permutation_trans; [apply Permutation_app_tail; exact HPB|].
  rewrite <- !app_assoc. apply Permutation_app_head. cbn [app]. do 4 apply perm_skip.
  unfold X, rd_hblocks. rewrite <- !map_app. apply Permutation_map. rewrite <- !app_assoc. cbn [app] in HPD3 |- *.
  exact HPD3. }
split.
{ unfold U'. eapply Permutation_trans; [apply Permutation_app_tail; exact HPU|].
  rewrite <- !app_assoc. apply Permutation_app_head. cbn [app]. do 2 apply perm_skip.
  assert (EH : [(a - HEAD, HEAD)] = rd_heads [(a, klen + 1)]) by reflexivity.
  rewrite EH. unfold rd_heads. rewrite <- map_app. apply Permutation_map.
  rewrite <- !app_assoc. cbn [app] in HPD3 |- *. exact HPD3. }
split; [exact HHD'|].
split; [exact HTX'|]. split; [exact (proj1 (proj1 HTC'))|]. split; [exact HTC'|].
split; [exact HDC'|]. split; [exact HDZ'|].
split; [exact HTDo|]. split; [exact HSo|].
split; [exact HTS'|]. split; [exact HSS|].
split; [cbn [crtB2_vfact]; split; [reflexivity | exact HZw]|].
split; [exact HPo|].
split; [exact (POBJ 0x80 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HPSc)|].
split; [exact HPw|].
split; [exact (POBJ 0x140 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HPKc)|].
split; [exact HN0'|]. split; [exact HN0a'|].
split; [exact HG'|].
split.
{ rewrite Hheld, Hlive, Hrsum, app_nil_r, crt_rd_sum_app, (crtB2_rd_sum_sizes Dst ss HSS), (crtB2_rd_sum_sizes Do _ HSo),
    crtB2_zsum_app. cbn [fold_right]. unfold n, len, tb2 in *. lia. }
split.
{ rewrite (blocks_bytes_bsum B ly' S'), (crtB2_bsum_perm _ _ HBL'), bsum_app, <- (blocks_bytes_bsum B ly3 S3).
  unfold X. cbn [rd_hblocks map app bsum fold_right fst snd]. rewrite Hrl in BL. unfold HEAD, n, len, tb2 in *. lia. }
split; [unfold tr, klen, nn in *; lia|]. unfold tr, klen, nn in *; lia.
Qed.
End g1.

(* ================= the lane's two ends: B1's boundary in the lane's form, the lane's last state in the base's form ======
   crt_INV_8212c (lane B1's text in the base) is crtB2_inv with no tree blocks and v unknown (a0 is not stated there:
   pj_object returns void). At 0x821ac the base asks the state's blocks as four named sizes and both headers with
   cap = 8; both are read back off the sizes the lane carries (crtB2_sizes4, crtB2_hdr8). ---- *)
Section cv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma crtB2_conv_8212c : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_INV_8212c B cx E k ly3 S3 U3 W3 ms3 md3 ->
  crtB2_inv B false [] [] [] [] VAny K_8212c CNT_8212c LIVE_8212c cx E k ly3 S3 U3 W3 ms3 md3.
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 H.
destruct H as (E18 & E20 & E21 & E22 & E23 & E26 & E27 & same & nsame & dec & live & peak & cnt & E24 & E25 & HPB & HPU &
  HHD & HTX & HTZ & HTC & HDC & HDZ & HTD & HTS & _ & _ & HPD & HPS & HPV & HPK & HN0 & HN0a & HG & HL & HBB & HCNT & HK).
cbn [crtB2_inv]. split; [intros Hf; discriminate Hf|].
do 7 (split; [assumption|]).
exists same, nsame, dec, [], [], [], live, peak, cnt.
split; [exact E24|]. split; [exact E25|].
split; [cbn [app rd_hblocks map]; exact HPB|].
split; [cbn [app rd_heads map]; exact HPU|].
split; [exact HHD|]. split; [exact HTX|]. split; [exact HTZ|]. split; [exact HTC|]. split; [exact HDC|].
split; [exact HDZ|]. split; [exact HTD|]. split; [apply perm_nil|]. split; [exact HTS|]. split; [apply perm_nil|].
split; [cbn [crtB2_vfact]; reflexivity|].
split; [exact HPD|]. split; [exact HPS|]. split; [exact HPV|]. split; [exact HPK|].
split; [exact HN0|]. split; [exact HN0a|]. split; [exact HG|].
split; [rewrite HL; cbn [app]; unfold rd_sum; cbn [fold_right]; lia|].
split; [exact HBB|]. split; [exact HCNT|]. exact HK.
Qed.
Lemma crtB2_conv_821ac : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crtB2_INV_821ac B cx E k ly3 S3 U3 W3 ms3 md3 -> crt_INV_821ac B cx E k ly3 S3 U3 W3 ms3 md3.
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 H. unfold crtB2_INV_821ac in H.
destruct H as (Z10 & E18 & E20 & E21 & E22 & E23 & E26 & E27 & same & nsame & dec & Ddoc & Dst & Dv & live & peak & cnt &
  E24 & E25 & HPB & HPU & HHD & HTX & HTZ & HTC & HDC & HDZ & HTD & HSD & HTS & HSS & HVF & HPD & HPS & HPV & HPK &
  HN0 & HN0a & HG & HL & HBB & HCNT & HK).
cbn [crtB2_vfact] in HVF. destruct HVF as (-> & HZ).
rewrite app_nil_r in HPB, HPU, HL.
destruct (crtB2_hdr8 B ly3 S3 W3 (ms_mem ms3) (crt_F cx + 0x20) _ Ddoc _ HTD HSD
  ltac:(intros c Hc Hin; cbn [In] in Hin; lia) ltac:(unfold check_round_trip_st8.crt_doc8; discriminate))
  as (numd & kidsd & keysd & Did & Hhd & EDd).
destruct (crtB2_hdr8 B ly3 S3 W3 (ms_mem ms3) (crt_F cx + 0x80) _ Dst _ HTS HSS
  ltac:(intros c Hc Hin; cbn [In] in Hin; lia) ltac:(unfold check_round_trip_stages_b.crt_s1; discriminate))
  as (nums & kidss & keyss & Dis & Hhs & EDs).
unfold crt_INV_821ac.
split; [exact (Z10 eq_refl)|].
do 7 (split; [assumption|]).
exists same, nsame, dec, Ddoc, Dst, live, peak, cnt.
split; [exact E24|]. split; [exact E25|]. split; [exact HPB|]. split; [exact HPU|].
split; [exact HHD|]. split; [exact HTX|]. split; [exact HTZ|]. split; [exact HTC|]. split; [exact HDC|].
split; [exact HDZ|]. split; [exact HTD|]. split; [exact HTS|].
split; [exact (crtB2_sizes4 Dst _ _ _ _ HSS)|].
split.
{ exists numd, 0, kidsd, keysd, 8. split; [exact Hhd|]. split; [reflexivity|].
  intros q Hq. apply (Permutation_in _ (Permutation_sym HPU)). rewrite EDd. unfold rd_heads in *. rewrite !map_app.
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. apply in_or_app; left. exact Hq. }
split.
{ exists nums, 0, kidss, keyss, 8. split; [exact Hhs|]. split; [reflexivity|].
  intros q Hq. apply (Permutation_in _ (Permutation_sym HPU)). rewrite EDs. unfold rd_heads in *. rewrite !map_app.
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. exact Hq. }
split; [exact HPD|]. split; [exact HPS|]. split; [exact HPV|]. split; [exact HPK|]. split; [exact HZ|].
split; [exact HN0|]. split; [exact HN0a|]. split; [exact HG|]. split; [exact HL|].
split; [exact HBB|]. split; [exact HCNT|]. exact HK.
Qed.
End cv.

(* ================= the budgets: the walk's room from crt_room_D1 (FSH_crt_base; FSH_crt_room.crt_room_D1_holds)
   down to 0x821ac, the closed traces and strings of the six calls computed once ================= *)
Lemma crtB2_vals :
  rd_ev (pj_set_c.set_trace 0 0 6) = 3 /\ Z.of_nat (length (pj_set_c.set_trace 0 0 6)) = 3 /\
  rd_live (pj_set_c.set_trace 0 0 6) = 567 /\
  rd_ev (pj_set_c.set_trace 1 8 7) = 1 /\ Z.of_nat (length (pj_set_c.set_trace 1 8 7)) = 1 /\
  rd_live (pj_set_c.set_trace 1 8 7) = 24 /\
  rd_ev (pj_set_c.set_trace 0 0 8) = 3 /\ Z.of_nat (length (pj_set_c.set_trace 0 0 8)) = 3 /\
  rd_live (pj_set_c.set_trace 0 0 8) = 569.
Proof. repeat (split; [vm_compute; reflexivity|]). vm_compute. reflexivity. Qed.
Lemma crtB2_rd_ev_nn : forall tr, 0 <= rd_ev tr.
Proof.
intros tr. induction tr as [|e tr IH]; [apply Z.leb_le; vm_compute; reflexivity|].
assert (He : 0 <= rd_ev [e]).
{ destruct e as [n0 | m n1 | n2 | n3]; [| destruct (Nat.eqb m 0) eqn:Em | |]; unfold rd_ev; cbn [fold_right];
    rewrite ?Em; unfold EV_fuzz_malloc, EV_fuzz_realloc, EV_fuzz_free; lia. }
assert (Ec : rd_ev (e :: tr) = rd_ev [e] + rd_ev tr) by (unfold rd_ev; cbn [fold_right]; lia).
lia.
Qed.
Lemma crtB2_rd_live_nn : forall tr, 0 <= rd_live tr.
Proof.
intros tr. induction tr as [|e tr IH]; unfold rd_live in *; cbn [fold_right]; [lia|].
pose proof (Zle_0_nat (PjGrammar.esize e)) as H0. assert (H1 : 0 <= HEAD) by (unfold HEAD; lia). lia.
Qed.
(* pj_write's final buffer is not negative: grow_cap only ever replaces c by newcap c need >= c *)
Lemma crtB2_gcap_nn : forall ls x c, 0 <= c -> 0 <= WriterSpec.grow_cap x c ls.
Proof.
induction ls as [|l ls IH]; intros x c Hc; cbn [WriterSpec.grow_cap]; [exact Hc|].
destruct (c <? x + l + 1); apply IH; [|exact Hc].
unfold WriterSpec.newcap. destruct (c =? 0).
- pose proof (crtr_dbl_ge 64 4096 (x + l + 1) ltac:(lia)). lia.
- pose proof (crtr_dbl_ge 64 c (x + l + 1) Hc). lia.
Qed.
Lemma crtB2_wcap_nn : forall cx, 0 <= WriterApp.w_cap (crt_wst cx).
Proof. intros cx. unfold crt_wst. cbv zeta. cbn [WriterApp.w_cap]. apply crtB2_gcap_nn. lia. Qed.
(* KERNEL TRAP (measured, rocq compile -time on a build machine): a hypothesis `LIVE_82268 cx + .. <= ..` used by lia after
   `unfold LIVE_82268 in H` makes the Qed hang, every tactic fast. The kernel's conversion of the folded type with the
   unfolded one unfolds Z.add before LIVE_82268 (the oracle's default) and evaluates the sum's leftmost arguments
   (enc_size's Z.div, ..). Expanding the budget constants first makes the same Qed take milliseconds. *)
Local Strategy expand [K_8212c K_8213c K_82154 K_82168 K_82180 K_82194 K_821ac K_82068 K_82218 K_82268 K_822ac
  CNT_8212c CNT_8213c CNT_82154 CNT_82168 CNT_82180 CNT_82194 CNT_821ac CNT_82068 CNT_82218 CNT_82268
  LIVE_8212c LIVE_8213c LIVE_82154 LIVE_82168 LIVE_82180 LIVE_82194 LIVE_821ac LIVE_82068 LIVE_82218 LIVE_82268
  crt_len crt_es crt_trlen].
Section bud. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* decode's ticks on its success arm: crt_base's input decodes, so its bytes are bytes and the encoded text decodes *)
Lemma crtB2_dec_ev : forall cx, crt_base B cx -> FSH_Fn_writer.dec_ev (WriterSpec.b64_enc (c_bs cx)) = 1.
Proof.
intros cx HB. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HD & _).
unfold FSH_Fn_writer.dec_ev. rewrite (WriterSpecFacts.b64_dec_enc _ (WriterSpecFacts.b64_dec_ok _ _ HD)). reflexivity.
Qed.
Lemma crtB2_enc_nn : forall bs : list Z, 0 <= FSH_Fn_writer.enc_size (Z.of_nat (length bs)).
Proof. intros bs. pose proof (Zle_0_nat (length bs)) as H0. unfold FSH_Fn_writer.enc_size. Z.div_mod_to_equations. lia. Qed.
Lemma crtB2_dec_nn : forall tb : list Z, 0 <= FSH_Fn_writer.dec_size tb.
Proof. intros tb. unfold FSH_Fn_writer.dec_size. Z.div_mod_to_equations. lia. Qed.
(* the room up to 0x821ac, in the atoms the six budget premises use: the tick bound is closed arithmetic; the live
   bound is LIVE_821ac's own sum, read off crt_room_D1's live clause (FSH_crt_room.crt_room_D1_holds), whose later terms
   (LIVE_82218's, pj_write's buffer w_cap + HEAD, pj_parse's rd_live) are not negative *)
Lemma crtB2_room_facts : forall cx, crt_base B cx -> crt_room_D1 cx ->
  let enc := FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) in
  let dec := FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) in
  FSH_Fn_writer.dec_ev (WriterSpec.b64_enc (c_bs cx)) = 1 /\
  EV_preset_base64_encode + 2 * CRT_EV_WRAP + 1 + 3 * EV_pj_string + 3 + 1 + 3 <= EV_check_round_trip /\
  (enc + HEAD) + enc + (Z.of_nat (length (c_tb cx)) + 1) + (dec + HEAD) + (23 + HEAD) + (6 + HEAD) + (7 + HEAD) +
    567 + 24 + 569 <= LIVE_check_round_trip /\
  0 <= enc /\ 0 <= dec.
Proof.
intros cx HB (_ & R2) enc dec.
pose proof (crtB2_dec_ev cx HB) as D. clear HB.
destruct crtB2_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9). clear V1 V2 V4 V5 V7 V8.
pose proof (crtB2_rd_live_nn (crt_TR cx)) as N2. pose proof (crtB2_rd_live_nn (pj_set_c.set_trace 2 8 5)) as N4.
assert (He : 0 <= enc) by exact (crtB2_enc_nn (c_bs cx)).
assert (Hd : 0 <= dec) by exact (crtB2_dec_nn _).
pose proof (crtB2_wcap_nn cx) as Hc.
pose proof (Zle_0_nat (length (WriterSpec.b64_enc (c_bs cx)))) as N5.
unfold LIVE_82268, LIVE_82218, LIVE_821ac, LIVE_82068, crt_len, crt_es in R2. fold enc dec in R2.
split; [exact D|]. clear D.
split; [unfold EV_preset_base64_encode, CRT_EV_WRAP, EV_pj_string, EV_fuzz_strdup, EV_check_round_trip; lia|].
(* every non-numeral atom an opaque variable: lia's certificate stays over variables *)
set (a := rd_live (pj_set_c.set_trace 0 0 6)) in *. set (b := rd_live (pj_set_c.set_trace 1 8 7)) in *.
set (d := rd_live (pj_set_c.set_trace 0 0 8)) in *.
set (t2 := rd_live (crt_TR cx)) in *. set (t4 := rd_live (pj_set_c.set_trace 2 8 5)) in *.
set (t5 := Z.of_nat (length (WriterSpec.b64_enc (c_bs cx)))) in *. set (t6 := Z.of_nat (length (c_tb cx))) in *.
set (w := WriterApp.w_cap (crt_wst cx)) in *.
clearbody a b d t2 t4 t5 t6 w enc dec.
unfold HEAD, LIVE_check_round_trip in *.
split; [lia|]. split; [exact He | exact Hd].
Qed.
End bud.
(* the budget premises of the six calls, in the closed values the calls compute to (strings: "org.openmixer.preset/2"
   22, "format" 6, "state" 5, "carries" 7, "base64" 6, "encoding" 8; traces as crtB2_vals) *)
Ltac crtB2_bud_tac :=
  lazymatch goal with HB : crt_base _ ?cx, HR : crt_room_D1 ?cx |- _ =>
    destruct (crtB2_room_facts _ cx HB HR) as (D1 & RK & RL & N1 & N2); clear HB HR;
    destruct crtB2_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9);
    unfold K_82194, K_82180, K_82168, K_82154, K_8213c, K_8212c, K_821ac, K_82068,
      CNT_82194, CNT_82180, CNT_82168, CNT_82154, CNT_8213c, CNT_8212c, CNT_821ac, CNT_82068,
      LIVE_82194, LIVE_82180, LIVE_82168, LIVE_82154, LIVE_8213c, LIVE_8212c, LIVE_821ac, LIVE_82068,
      crt_trlen, crt_len, crt_es;
    rewrite ?V1, ?V2, ?V3, ?V4, ?V5, ?V6, ?V7, ?V8, ?V9; clear V1 V2 V3 V4 V5 V6 V7 V8 V9;
    rewrite ?D1; clear D1;
    cbn [fold_right];
    pose proof (Zle_0_nat (length (c_tb cx))) as N3;
    set (enc := FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))) in *;
    set (dec := FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))) in *;
    set (t6 := Z.of_nat (length (c_tb cx))) in *;
    clearbody enc dec t6;
    unfold HEAD, EV_pj_string, EV_fuzz_strdup, EV_preset_base64_encode, CRT_EV_WRAP, EV_check_round_trip in *;
    repeat split; lia
  end.
Section bud2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma crtB2_bud14 : forall cx, crt_base B cx -> crt_room_D1 cx ->
  K_8212c cx + EV_pj_string <= K_8213c cx /\ CNT_8212c cx + 1 <= CNT_8213c cx /\
  LIVE_8212c cx + (22 + 1 + HEAD) <= LIVE_8213c cx /\
  K_8213c cx <= EV_check_round_trip /\ CNT_8213c cx <= EV_check_round_trip /\ LIVE_8213c cx <= LIVE_check_round_trip /\
  FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) +
    fold_right Z.add 0 (@nil Z) + fold_right Z.add 0 (@nil Z) + (22 + 1) <= LIVE_check_round_trip.
Proof. intros cx HB HR. crtB2_bud_tac. Qed.
Lemma crtB2_bud15 : forall cx, crt_base B cx -> crt_room_D1 cx ->
  K_8213c cx + rd_ev (pj_set_c.set_trace 0 0 6) <= K_82154 cx /\
  CNT_8213c cx + Z.of_nat (length (pj_set_c.set_trace 0 0 6)) <= CNT_82154 cx /\
  LIVE_8213c cx + rd_live (pj_set_c.set_trace 0 0 6) <= LIVE_82154 cx /\
  K_82154 cx <= EV_check_round_trip /\ CNT_82154 cx <= EV_check_round_trip /\ LIVE_82154 cx <= LIVE_check_round_trip /\
  FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) +
    fold_right Z.add 0 (@nil Z) + (22 + 1) + rd_live (pj_set_c.set_trace 0 0 6) <= LIVE_check_round_trip.
Proof. intros cx HB HR. crtB2_bud_tac. Qed.
Lemma crtB2_bud16 : forall cx, crt_base B cx -> crt_room_D1 cx ->
  K_82154 cx + EV_pj_string <= K_82168 cx /\ CNT_82154 cx + 1 <= CNT_82168 cx /\
  LIVE_82154 cx + (5 + 1 + HEAD) <= LIVE_82168 cx /\
  K_82168 cx <= EV_check_round_trip /\ CNT_82168 cx <= EV_check_round_trip /\ LIVE_82168 cx <= LIVE_check_round_trip /\
  FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) +
    fold_right Z.add 0 [56 * 8; 8 * 8; 7; 23] + fold_right Z.add 0 (@nil Z) + (5 + 1) <= LIVE_check_round_trip.
Proof. intros cx HB HR. crtB2_bud_tac. Qed.
Lemma crtB2_bud17 : forall cx, crt_base B cx -> crt_room_D1 cx ->
  K_82168 cx + rd_ev (pj_set_c.set_trace 1 8 7) <= K_82180 cx /\
  CNT_82168 cx + Z.of_nat (length (pj_set_c.set_trace 1 8 7)) <= CNT_82180 cx /\
  LIVE_82168 cx + rd_live (pj_set_c.set_trace 1 8 7) <= LIVE_82180 cx /\
  K_82180 cx <= EV_check_round_trip /\ CNT_82180 cx <= EV_check_round_trip /\ LIVE_82180 cx <= LIVE_check_round_trip /\
  FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) +
    fold_right Z.add 0 [56 * 8; 8 * 8; 7; 23] + fold_right Z.add 0 (@nil Z) + (5 + 1) +
    rd_live (pj_set_c.set_trace 1 8 7) <= LIVE_check_round_trip.
Proof. intros cx HB HR. crtB2_bud_tac. Qed.
Lemma crtB2_bud18 : forall cx, crt_base B cx -> crt_room_D1 cx ->
  K_82180 cx + EV_pj_string <= K_82194 cx /\ CNT_82180 cx + 1 <= CNT_82194 cx /\
  LIVE_82180 cx + (6 + 1 + HEAD) <= LIVE_82194 cx /\
  K_82194 cx <= EV_check_round_trip /\ CNT_82194 cx <= EV_check_round_trip /\ LIVE_82194 cx <= LIVE_check_round_trip /\
  FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) +
    fold_right Z.add 0 [56 * 8; 8 * 8; 7; 23; 8; 6] + fold_right Z.add 0 (@nil Z) + (6 + 1) <= LIVE_check_round_trip.
Proof. intros cx HB HR. crtB2_bud_tac. Qed.
Lemma crtB2_bud19 : forall cx, crt_base B cx -> crt_room_D1 cx ->
  K_82194 cx + rd_ev (pj_set_c.set_trace 0 0 8) <= K_821ac cx /\
  CNT_82194 cx + Z.of_nat (length (pj_set_c.set_trace 0 0 8)) <= CNT_821ac cx /\
  LIVE_82194 cx + rd_live (pj_set_c.set_trace 0 0 8) <= LIVE_821ac cx /\
  K_821ac cx <= EV_check_round_trip /\ CNT_821ac cx <= EV_check_round_trip /\ LIVE_821ac cx <= LIVE_check_round_trip /\
  FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) +
    fold_right Z.add 0 [56 * 8; 8 * 8; 7; 23; 8; 6] + (6 + 1) + rd_live (pj_set_c.set_trace 0 0 8) <= LIVE_check_round_trip.
Proof. intros cx HB HR. crtB2_bud_tac. Qed.
End bud2.

(* ================= the from-lemma of lane B2: crt_INV_8212c at 0x8212c -> crt_INV_821ac at 0x821ac =================
   Six segments, each a store-free run to a PROGRAM call (FSH_crt_site.crt_seg_call for segment 14, crt_seg_call_br,
   which also decides `bnez a0` against the abort tail 0x824b8 by the boundary's a0 = 0, for 15-19), the call's part
   by this lane's crt_hcall lemmas, the boundaries crt_INV_8213c .. crt_INV_82194 in between, and the two end
   conversions. The callee contracts are the base's Section hypotheses PJ_STRING / PJ_SET (with the explicit sink
   head SK) and IMG the image facts; the room comes from FSH_crt_room.crt_room_D1_holds. ---- *)
Section from. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis PJ_STRING : @pj_string_spec fx rc SK tfibsegs B.
Hypothesis PJ_SET : @pj_set_spec fx rc SK tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.

Lemma crtB2_from_mono : forall ss (INV0 INV1 : crt_inv),
  (forall cx E k ly3 S3 U3 W3 ms3 md3, INV0 cx E k ly3 S3 U3 W3 ms3 md3 -> INV1 cx E k ly3 S3 U3 W3 ms3 md3) ->
  crt_from SK B ss INV1 -> crt_from SK B ss INV0.
Proof.
intros ss INV0 INV1 HI HF cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
exact (HF cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO (HI _ _ _ _ _ _ _ _ _ HINV) HS).
Qed.
Lemma crtB2_hcall_mono : forall ssC A_c r STKc (INV0 INV1 INV' : crt_inv),
  (forall cx E k ly3 S3 U3 W3 ms3 md3, INV0 cx E k ly3 S3 U3 W3 ms3 md3 -> INV1 cx E k ly3 S3 U3 W3 ms3 md3) ->
  crt_hcall SK B ssC A_c r STKc INV1 INV' -> crt_hcall SK B ssC A_c r STKc INV0 INV'.
Proof.
intros ssC A_c r STKc INV0 INV1 INV' HI HC cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV.
exact (HC cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE (HI _ _ _ _ _ _ _ _ _ HINV)).
Qed.

Lemma crtB2_from_8212c :
  crt_from SK B (crt_ss_ret 0x821ac crt_cs1 crt_csF) (crt_INV_821ac B) ->
  crt_from SK B (crt_ss_ret 0x8212c crt_cs1 crt_csF) (crt_INV_8212c B).
Proof.
intros H19.
assert (STKs0 : 0 <= STK_pj_set) by (apply Z.leb_le; vm_compute; reflexivity).
assert (STKs1 : STK_pj_set + 208 <= STK_check_round_trip) by (apply Z.leb_le; vm_compute; reflexivity).
assert (STKt0 : 0 <= STK_pj_string) by (apply Z.leb_le; vm_compute; reflexivity).
assert (STKt1 : STK_pj_string + 208 <= STK_check_round_trip) by (apply Z.leb_le; vm_compute; reflexivity).
(* seg 19: 0x82194 -> pj_set (state, "encoding", v) -> 0x821ac *)
assert (H18 : crt_from SK B (crt_ss_ret 0x82194 crt_cs1 crt_csF) (crt_INV_82194 B)).
{ destruct crtB2_cs19 as (Hs & GS & G10 & G11 & G12). pose proof Hs as (_ & _ & _ & _ & G1 & G2 & _).
  apply (crt_seg_call_br SK B 0x82194 0x838e8 0x821ac crtB2_b19 crtB2_c19 (crt_INV_82194 B) (crtB2_INV_821ac B) STK_pj_set
    crtB2_br19 crtB2_run19 Hs ltac:(lia) ltac:(reflexivity) STKs0 STKs1).
  - intros cx E k ly3 S3 U3 W3 ms3 md3 HI. exact (proj1 HI eq_refl).
  - exact (crtB2_hcall_set0_st SK B PJ_SET IMG crtB2_c19 0x821ac 0x20f60 check_round_trip_stages_b.K_ENCODING
      check_round_trip_stages_b.V_BASE64 check_round_trip_st8.crt_doc8 [56 * 8; 8 * 8; 7; 23; 8; 6]
      K_82194 CNT_82194 LIVE_82194 K_821ac CNT_821ac LIVE_821ac GS G1 G2 G10 G11 G12 ltac:(lia)
      ltac:(unfold FS_RO_STRS; cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(lia) ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.ltb_lt; vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      (fun cx HB => crtB2_bud19 B cx HB (crt_room_D1_holds B cx HB))).
  - exact (crtB2_from_mono _ _ _ (crtB2_conv_821ac B) H19). }
(* seg 18: 0x82180 -> pj_string (v, "base64") -> 0x82194 *)
assert (H17 : crt_from SK B (crt_ss_ret 0x82180 crt_cs1 crt_csF) (crt_INV_82180 B)).
{ destruct crtB2_cs18 as (Hs & GS & G10 & G11). pose proof Hs as (_ & _ & _ & _ & G1 & G2 & _).
  apply (crt_seg_call_br SK B 0x82180 0x83be4 0x82194 crtB2_b18 crtB2_c18 (crt_INV_82180 B) (crt_INV_82194 B) STK_pj_string
    crtB2_br18 crtB2_run18 Hs ltac:(lia) ltac:(reflexivity) STKt0 STKt1).
  - intros cx E k ly3 S3 U3 W3 ms3 md3 HI. exact (proj1 HI eq_refl).
  - exact (crtB2_hcall_str SK B PJ_STRING IMG crtB2_c18 0x82194 0x20f40 check_round_trip_stages_b.V_BASE64 true
      check_round_trip_st8.crt_doc8 [56 * 8; 8 * 8; 7; 23; 8; 6] [] [] VZero
      K_82180 CNT_82180 LIVE_82180 K_82194 CNT_82194 LIVE_82194 GS G1 G2 G10 G11 ltac:(lia)
      ltac:(unfold FS_RO_STRS; cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(lia) ltac:(apply Z.leb_le; vm_compute; reflexivity) (or_intror eq_refl)
      ltac:(apply Z.ltb_lt; vm_compute; reflexivity) (fun cx HB => crtB2_bud18 B cx HB (crt_room_D1_holds B cx HB))).
  - exact H18. }
(* seg 17: 0x82168 -> pj_set (doc, "carries", v) -> 0x82180, doc has room *)
assert (H16 : crt_from SK B (crt_ss_ret 0x82168 crt_cs1 crt_csF) (crt_INV_82168 B)).
{ destruct crtB2_cs17 as (Hs & GS & G10 & G11 & G12). pose proof Hs as (_ & _ & _ & _ & G1 & G2 & _).
  apply (crt_seg_call_br SK B 0x82168 0x838e8 0x82180 crtB2_b17 crtB2_c17 (crt_INV_82168 B) (crt_INV_82180 B) STK_pj_set
    crtB2_br17 crtB2_run17 Hs ltac:(lia) ltac:(reflexivity) STKs0 STKs1).
  - intros cx E k ly3 S3 U3 W3 ms3 md3 HI. exact (proj1 HI eq_refl).
  - exact (crtB2_hcall_set1_doc SK B PJ_SET IMG crtB2_c17 0x82180 0x20f20 check_round_trip_st8.CRT_CARRIES
      check_round_trip_runs.CRT_STATE [(check_round_trip_st8.CRT_FORMAT, PjTree.JStr check_round_trip_st8.CRT_FMT2)]
      [56 * 8; 8 * 8; 7; 23] [] [] K_82168 CNT_82168 LIVE_82168 K_82180 CNT_82180 LIVE_82180
      GS G1 G2 G10 G11 G12 ltac:(lia)
      ltac:(unfold FS_RO_STRS; cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(lia) ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.ltb_lt; vm_compute; reflexivity)
      ltac:(discriminate) ltac:(apply Z.ltb_lt; vm_compute; reflexivity)
      ltac:(cbn [map fst In]; intros [Hk | []]; unfold check_round_trip_st8.CRT_FORMAT, check_round_trip_st8.CRT_CARRIES in Hk;
            discriminate Hk)
      ltac:(intros c Hc Hin; cbn [In] in Hin; lia)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      (fun cx HB => crtB2_bud17 B cx HB (crt_room_D1_holds B cx HB))).
  - exact H17. }
(* seg 16: 0x82154 -> pj_string (v, "state") -> 0x82168 *)
assert (H15 : crt_from SK B (crt_ss_ret 0x82154 crt_cs1 crt_csF) (crt_INV_82154 B)).
{ destruct crtB2_cs16 as (Hs & GS & G10 & G11). pose proof Hs as (_ & _ & _ & _ & G1 & G2 & _).
  apply (crt_seg_call_br SK B 0x82154 0x83be4 0x82168 crtB2_b16 crtB2_c16 (crt_INV_82154 B) (crt_INV_82168 B) STK_pj_string
    crtB2_br16 crtB2_run16 Hs ltac:(lia) ltac:(reflexivity) STKt0 STKt1).
  - intros cx E k ly3 S3 U3 W3 ms3 md3 HI. exact (proj1 HI eq_refl).
  - exact (crtB2_hcall_str SK B PJ_STRING IMG crtB2_c16 0x82168 0x20f00 check_round_trip_runs.CRT_STATE true
      [(check_round_trip_st8.CRT_FORMAT, PjTree.JStr check_round_trip_st8.CRT_FMT2)] [56 * 8; 8 * 8; 7; 23] [] [] VZero
      K_82154 CNT_82154 LIVE_82154 K_82168 CNT_82168 LIVE_82168 GS G1 G2 G10 G11 ltac:(lia)
      ltac:(unfold FS_RO_STRS; cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(lia) ltac:(apply Z.leb_le; vm_compute; reflexivity) (or_intror eq_refl)
      ltac:(apply Z.ltb_lt; vm_compute; reflexivity) (fun cx HB => crtB2_bud16 B cx HB (crt_room_D1_holds B cx HB))).
  - exact H16. }
(* seg 15: 0x8213c -> pj_set (doc, "format", v) -> 0x82154, doc grows from cap 0 *)
assert (H14 : crt_from SK B (crt_ss_ret 0x8213c crt_cs1 crt_csF) (crt_INV_8213c B)).
{ destruct crtB2_cs15 as (Hs & GS & G10 & G11 & G12). pose proof Hs as (_ & _ & _ & _ & G1 & G2 & _).
  apply (crt_seg_call_br SK B 0x8213c 0x838e8 0x82154 crtB2_b15 crtB2_c15 (crt_INV_8213c B) (crt_INV_82154 B) STK_pj_set
    crtB2_br15 crtB2_run15 Hs ltac:(lia) ltac:(reflexivity) STKs0 STKs1).
  - intros cx E k ly3 S3 U3 W3 ms3 md3 HI. exact (proj1 HI eq_refl).
  - exact (crtB2_hcall_set0_doc SK B PJ_SET IMG crtB2_c15 0x82154 0x20ee0 check_round_trip_st8.CRT_FORMAT
      check_round_trip_st8.CRT_FMT2 [] [] K_8213c CNT_8213c LIVE_8213c K_82154 CNT_82154 LIVE_82154
      GS G1 G2 G10 G11 G12 ltac:(lia)
      ltac:(unfold FS_RO_STRS; cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(lia) ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.ltb_lt; vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      (fun cx HB => crtB2_bud15 B cx HB (crt_room_D1_holds B cx HB))).
  - exact H15. }
(* seg 14: 0x8212c -> pj_string (v, "org.openmixer.preset/2") -> 0x8213c; pj_object returned void: no branch *)
destruct crtB2_cs14 as (Hs & GS & G10 & G11). pose proof Hs as (_ & _ & _ & G1 & G2 & _).
apply (crt_seg_call SK B 0x8212c 0x83be4 0x8213c crtB2_c14 (crt_INV_8212c B) (crt_INV_8213c B) STK_pj_string
  crtB2_run14 Hs ltac:(lia) ltac:(reflexivity) STKt0 STKt1).
- apply (crtB2_hcall_mono _ _ _ _ _ _ _ (crtB2_conv_8212c B)).
  exact (crtB2_hcall_str SK B PJ_STRING IMG crtB2_c14 0x8213c 0x20ea0 check_round_trip_st8.CRT_FMT2 false [] [] [] [] VAny
    K_8212c CNT_8212c LIVE_8212c K_8213c CNT_8213c LIVE_8213c GS G1 G2 G10 G11 ltac:(lia)
    ltac:(unfold FS_RO_STRS; cbn [In]; repeat (first [left; reflexivity | right]))
    ltac:(lia) ltac:(apply Z.leb_le; vm_compute; reflexivity) (or_introl eq_refl)
    ltac:(apply Z.ltb_lt; vm_compute; reflexivity) (fun cx HB => crtB2_bud14 B cx HB (crt_room_D1_holds B cx HB))).
- exact H14.
Qed.
End from.
