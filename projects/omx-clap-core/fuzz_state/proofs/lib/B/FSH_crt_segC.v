(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YN0j.v, with its module paths and module names changed; 548 of its 586 lines of code are new or changed and 260 lines of the source are left out. *)
(* check_round_trip 0x81b9c (fuzz_state.c:278-314 with round_trip_document fs.c:229-264 inlined), fs.asan-ubsan (image
   tfibsegs = lib/B/YB1v.v, the pinned fuzz_state.asan-ubsan sha256
   5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e51491f44c053d204): the B twin of the ASan walk of lib/B/FSH_Fn_crt.v
   check_round_trip_spec, segment group C = segments 20-29, from the return of pj_set at 0x82304 (0x82308) to the
   return of pj_get_str at 0x823bc (0x823c0), with the class-3 fake frame live (own = [(3, pos)]).
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from 27728fda52c lib/A/FSH_crt_segC.v)
   Port source: a working branch 27728fda52c proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC.v (blob
   02a0b2e19e2, over S0 + A base v25 / site v24 e377e99a5c4), CTX-free; its own port sources (the bespoke ASan proof of
   this function, a working branch d25a984c903 lib/A/Prog/check_round_trip_*.v; the released plain
   lib/Prog/check_round_trip_stages_b.v stage names; cgif lib/A/AChf.v / ACic.v segment shape; checker a Theorem Labs lane
   CONFIRM on (internal path)) carry over. Same Definition / Lemma names and
   statement shapes as the A file; every pc, return address, callee address, register and slot fact RE-MEASURED on B
   (capstone over the pinned fs.asan-ubsan, (internal path) and crt.calls.tsv) and
   mapped from A by instruction meaning. Requires lib/B/FSH_crt_base.v (v25) and lib/B/FSH_crt_site.v (v24). Imports:
   lib.A.X -> lib.B.X where lib/B/X.v exists (AB1v -> YB1v, AB1w -> YB1w, AE2k -> YE2k, AF0x -> YF0x, every FSH_* /
   FSW_* / FSPstat kit file); FSupoison, FSupoisonU, FSH_YC20 and FSH_Gen stay lib/A's, as lib/B/FSW_K.v imports them.
   A new file: no licence lines.

   A name -> A pc -> B pc (names keep their A form, content is B's):
     crtC_ss_1ac  0x821ac -> 0x82308   call pj_string 0x83be4 -> 0x83e58 at 0x821bc -> 0x82318, ra 0x821c0 -> 0x8231c
     crtC_ss_1c0  0x821c0 -> 0x8231c   call pj_set    0x838e8 -> 0x83adc at 0x821d4 -> 0x82330, ra 0x821d8 -> 0x82334
     crtC_ss_1d8  0x821d8 -> 0x82334   call pj_string 0x83be4 -> 0x83e58 at 0x821e4 -> 0x82340, ra 0x821e8 -> 0x82344
     crtC_ss_1e8  0x821e8 -> 0x82344   call pj_set    0x838e8 -> 0x83adc at 0x821fc -> 0x82358, ra 0x82200 -> 0x8235c
     crtC_ss_200  0x82200 -> 0x8235c   call pj_set    0x838e8 -> 0x83adc at 0x82214 -> 0x82370, ra 0x82218 -> 0x82374
     crtC_ss_218  0x82218 -> 0x82374   call pj_write  0x83d08 -> 0x83f94 at 0x82224 -> 0x82380, ra 0x82228 -> 0x82384
     crtC_ss_228  0x82228 -> 0x82384   call strlen    0x42654 -> 0x426c4 at 0x82234 -> 0x8238c, ra 0x82238 -> 0x82390
     crtC_ss_238  0x82238 -> 0x82390   call pj_parse  0x82eac -> 0x82f3c at 0x82244 -> 0x8239c, ra 0x82248 -> 0x823a0
     crtC_ss_248  0x82248 -> 0x823a0   call pj_get    0x83720 -> 0x83894 at 0x82258 -> 0x823b0, ra 0x8225c -> 0x823b4
     crtC_ss_25c  0x8225c -> 0x823b4   call pj_get_str 0x83868 -> 0x83a54 at 0x82264 -> 0x823bc, ra 0x82268 -> 0x823c0
     (crtC_sb_<r> / crtC_sc_<r> / crtC_br_<r> / crtC_run_<r> / crtC_pc_<r> follow their crtC_ss_<r>; crtC_pre_<A call pc>
     is the precondition at the B call pc of the same row; crt_pjset_fp_ok_1d4 / _1fc / _214 are the pj_set calls at
     B 0x82330 / 0x82358 / 0x82370.)

   The ten segments (MEASURED, capstone over the pinned fs.asan-ubsan; each pj_* return is tested by `bnez a0` to the
   trap arm 0x824e4 = __asan_handle_no_return, then abort 0x824e8, unreachable because the callee's success post gives
   a0 = 0; pj_write's and pj_get_str's by `beqz a0`):
     20  0x82308..0x82318  pj_string (&v, "preset" 0x20f80)            v = s11 = F + 0xe0 (A: s6)
     21  0x8231c..0x82330  pj_set (&state, "context" 0x20fa0, &v)       state = s7 = F + 0x80
     22  0x82334..0x82340  pj_string (&v, text)                         text = s2 (encode's block)
     23  0x82344..0x82358  pj_set (&state, "bytes" 0x20fc0, &v)
     24  0x8235c..0x82370  pj_set (&doc, "state" 0x20f00, &state)       doc = F + 0x20, `ld a0, 0x38(s1)` (A: s10)
     25  0x82374..0x82380  pj_write (&doc, 1)                           doc again from slot 0x38
     26  0x82384..0x8238c  strlen (file) through the thunk 0x426c4       B has no A 0x82228 `ld s2, 0x18(s1)`
     27  0x82390..0x8239c  pj_parse (file, len, &back)                  &back = F + 0x140, `ld a2, 0x20(s1)` (A: s2)
     28  0x823a0..0x823b0  pj_get (&back, "state" 0x20f00)              R1 hold; &back from slot 0x20 (A: s2)
     29  0x823b4..0x823bc  pj_get_str (r, "bytes" 0x20fc0)              R1 hold
   The four key strings sit at the same addresses on B (B's auipc / addi pairs, lib/B/FSH_Rt.v FS_RO_STRS).
   F = frame_addr lyc 3 pos, the class-3 fake frame (fs_frame_bytes 3 = 512), laid out as on A: doc [0x20, 0x58), state
   [0x80, 0xb8), v [0xe0, 0x118), back [0x140, 0x178), the two size_t n at 0x1a0 and 0x1c0 (B 0x820cc-0x820ec: slots
   0x38 := F + 0x20, 0x20 := F + 0x140, 0x28 := F + 0x1a0, s7 = F + 0x80, s11 = F + 0xe0, s6 = F + 0x1c0). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_K3 FSH_Fn_reader
FSH_Fn_writer FSH_Fn_crt FSW_frame FSW_frame3 FSW_rres FSW_crt_tbl FSW_strkit FSH_crt_base FSH_crt_site.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YE2k YF0x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the class-3 frame's objects (offsets from F = frame_addr ly 3 pos) ================= *)
Definition crtC_DOC : Z := 0x20.
Definition crtC_STATE : Z := 0x80.
Definition crtC_V : Z := 0xe0.
Definition crtC_BACK : Z := 0x140.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* SK is an explicit Section variable, as FSH_crt_base.v's Section b declares it: nothing in this file infers it, and
   whoever instantiates the walk passes build B's YE2k.tfib_sink_head. *)
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ---- the three pj_set sites of segment group C (a Theorem Labs lane's re-check list). At each, pj_set's FP is STATED at the
   site's obj / val and closed by FSH_crt_base's crt_pjset_fp_gen: of what ajournal's frame clause protects, the call
   touches only obj's [24, 56) and val's 56 bytes, and both lie in crt's own class-3 frame. ----
   B 0x82330 (A 0x821d4): pj_set (&state, "context", &v): obj = F + 0x80, val = F + 0xe0. *)
Lemma crt_pjset_fp_ok_1d4 : forall ly S W mem md pos Dold0,
  AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
  (forall bk, In bk (rd_hblocks Dold0) -> In bk (ablocks B ly S)) ->
  let F := frame_addr ly 3 pos in
  (forall a, inFP ([(F + crtC_STATE + 24, F + crtC_STATE + 56); (F + crtC_V, F + crtC_V + 56)] ++
                   ablocks_fp (rd_hblocks Dold0) ++ FS_PSTAT_FP) a ->
     in_zr a (frame_rng ly (3, pos)) \/ in_zr a (shadow_addr F, fs_frame_bytes 3 / 8) ->
     F + crtC_STATE + 24 <= a < F + crtC_STATE + 56 \/ F + crtC_V <= a < F + crtC_V + 56) /\
  (forall a, F + crtC_STATE + 24 <= a < F + crtC_STATE + 56 \/ F + crtC_V <= a < F + crtC_V + 56 ->
     in_frames ly [(3, pos)] a).
Proof.
intros ly S W mem md pos Dold0 HAR Hin Hblk.
exact (crt_pjset_fp_gen B ly S W mem md pos Dold0 crtC_STATE crtC_V HAR Hin Hblk
  ltac:(unfold crtC_STATE; lia) ltac:(unfold crtC_STATE; lia) ltac:(unfold crtC_V; lia) ltac:(unfold crtC_V; lia)).
Qed.
(* B 0x82358 (A 0x821fc): pj_set (&state, "bytes", &v): obj = F + 0x80, val = F + 0xe0 *)
Lemma crt_pjset_fp_ok_1fc : forall ly S W mem md pos Dold0,
  AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
  (forall bk, In bk (rd_hblocks Dold0) -> In bk (ablocks B ly S)) ->
  let F := frame_addr ly 3 pos in
  (forall a, inFP ([(F + crtC_STATE + 24, F + crtC_STATE + 56); (F + crtC_V, F + crtC_V + 56)] ++
                   ablocks_fp (rd_hblocks Dold0) ++ FS_PSTAT_FP) a ->
     in_zr a (frame_rng ly (3, pos)) \/ in_zr a (shadow_addr F, fs_frame_bytes 3 / 8) ->
     F + crtC_STATE + 24 <= a < F + crtC_STATE + 56 \/ F + crtC_V <= a < F + crtC_V + 56) /\
  (forall a, F + crtC_STATE + 24 <= a < F + crtC_STATE + 56 \/ F + crtC_V <= a < F + crtC_V + 56 ->
     in_frames ly [(3, pos)] a).
Proof.
intros ly S W mem md pos Dold0 HAR Hin Hblk.
exact (crt_pjset_fp_gen B ly S W mem md pos Dold0 crtC_STATE crtC_V HAR Hin Hblk
  ltac:(unfold crtC_STATE; lia) ltac:(unfold crtC_STATE; lia) ltac:(unfold crtC_V; lia) ltac:(unfold crtC_V; lia)).
Qed.
(* B 0x82370 (A 0x82214): pj_set (&doc, "state", &state): obj = F + 0x20 (slot 0x38), val = F + 0x80 *)
Lemma crt_pjset_fp_ok_214 : forall ly S W mem md pos Dold0,
  AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
  (forall bk, In bk (rd_hblocks Dold0) -> In bk (ablocks B ly S)) ->
  let F := frame_addr ly 3 pos in
  (forall a, inFP ([(F + crtC_DOC + 24, F + crtC_DOC + 56); (F + crtC_STATE, F + crtC_STATE + 56)] ++
                   ablocks_fp (rd_hblocks Dold0) ++ FS_PSTAT_FP) a ->
     in_zr a (frame_rng ly (3, pos)) \/ in_zr a (shadow_addr F, fs_frame_bytes 3 / 8) ->
     F + crtC_DOC + 24 <= a < F + crtC_DOC + 56 \/ F + crtC_STATE <= a < F + crtC_STATE + 56) /\
  (forall a, F + crtC_DOC + 24 <= a < F + crtC_DOC + 56 \/ F + crtC_STATE <= a < F + crtC_STATE + 56 ->
     in_frames ly [(3, pos)] a).
Proof.
intros ly S W mem md pos Dold0 HAR Hin Hblk.
exact (crt_pjset_fp_gen B ly S W mem md pos Dold0 crtC_DOC crtC_STATE HAR Hin Hblk
  ltac:(unfold crtC_DOC; lia) ltac:(unfold crtC_DOC; lia) ltac:(unfold crtC_STATE; lia) ltac:(unfold crtC_STATE; lia)).
Qed.

(* ================= the walk's after-call glue =================
   The program-call step is FSH_crt_base.crt_after_call (this file's proved text, moved into the base by path with its
   ten helpers crt_chunk_env .. crt_sv_in, so all four segment files share one). The write window of a boundary state
   is FSH_crt_base.crt_awr_ok (S0's awr_ok shape, own frame = frames (c_S cx)). *)
End c.

(* ================= the ten straight-line runs of segment group C =================
   Every segment starts at a return address with the store-free run state FSH_crt_site.crt_ss2 (the boundary state
   crt_ss_ret without the frame's regions: the s0 words and the s1 slots, the state crt_seg_call / crt_seg_call_br
   take), runs to its call, and (where the callee returned a result the code tests) crosses one branch whose arm is
   fixed by the callee's post: `bnez a0` after a pj_* call with a0 = 0, `beqz a0` after pj_write / pj_get_str with
   a0 <> 0. The states and the runs below are MEASURED by the engine over the lane's decode table (lib/B/FSW_crt_tbl.v)
   on the pinned fs.asan-ubsan: each lemma is closed by vm_compute. ---- *)
(* B 0x82308 -> 0x83e58 (A 0x821ac -> 0x83be4): pj_string (&v, "preset" 0x20f80) *)
Definition crtC_ss_1ac : sstate := crt_ss2 0x82308.
Definition crtC_sb_1ac : sstate :=
  Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL crtC_ss_1ac).
Lemma crtC_br_1ac : sym_runN tfibsegs crt_tbl FUEL crtC_ss_1ac = (crtC_sb_1ac, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtC_sc_1ac : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x83e58 (add_cond crtC_sb_1ac (mkAC BC_EQ (SOff 10 0) (SLit 0)))).
Lemma crtC_run_1ac : sym_run_toN tfibsegs crt_tbl FUEL 0x83e58 (add_cond crtC_sb_1ac (mkAC BC_EQ (SOff 10 0) (SLit 0)))
  = (crtC_sc_1ac, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtC_pc_1ac : ss_pc crtC_sc_1ac = 0x83e58.
Proof. vm_compute. reflexivity. Qed.

(* B 0x8231c -> 0x83adc (A 0x821c0 -> 0x838e8): pj_set (&state, "context" 0x20fa0, &v) *)
Definition crtC_ss_1c0 : sstate := crt_ss2 0x8231c.
Definition crtC_sb_1c0 : sstate :=
  Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL crtC_ss_1c0).
Lemma crtC_br_1c0 : sym_runN tfibsegs crt_tbl FUEL crtC_ss_1c0 = (crtC_sb_1c0, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtC_sc_1c0 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x83adc (add_cond crtC_sb_1c0 (mkAC BC_EQ (SOff 10 0) (SLit 0)))).
Lemma crtC_run_1c0 : sym_run_toN tfibsegs crt_tbl FUEL 0x83adc (add_cond crtC_sb_1c0 (mkAC BC_EQ (SOff 10 0) (SLit 0)))
  = (crtC_sc_1c0, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtC_pc_1c0 : ss_pc crtC_sc_1c0 = 0x83adc.
Proof. vm_compute. reflexivity. Qed.

(* B 0x82334 -> 0x83e58 (A 0x821d8 -> 0x83be4): pj_string (&v, text) *)
Definition crtC_ss_1d8 : sstate := crt_ss2 0x82334.
Definition crtC_sb_1d8 : sstate :=
  Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL crtC_ss_1d8).
Lemma crtC_br_1d8 : sym_runN tfibsegs crt_tbl FUEL crtC_ss_1d8 = (crtC_sb_1d8, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtC_sc_1d8 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x83e58 (add_cond crtC_sb_1d8 (mkAC BC_EQ (SOff 10 0) (SLit 0)))).
Lemma crtC_run_1d8 : sym_run_toN tfibsegs crt_tbl FUEL 0x83e58 (add_cond crtC_sb_1d8 (mkAC BC_EQ (SOff 10 0) (SLit 0)))
  = (crtC_sc_1d8, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtC_pc_1d8 : ss_pc crtC_sc_1d8 = 0x83e58.
Proof. vm_compute. reflexivity. Qed.

(* B 0x82344 -> 0x83adc (A 0x821e8 -> 0x838e8): pj_set (&state, "bytes" 0x20fc0, &v) *)
Definition crtC_ss_1e8 : sstate := crt_ss2 0x82344.
Definition crtC_sb_1e8 : sstate :=
  Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL crtC_ss_1e8).
Lemma crtC_br_1e8 : sym_runN tfibsegs crt_tbl FUEL crtC_ss_1e8 = (crtC_sb_1e8, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtC_sc_1e8 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x83adc (add_cond crtC_sb_1e8 (mkAC BC_EQ (SOff 10 0) (SLit 0)))).
Lemma crtC_run_1e8 : sym_run_toN tfibsegs crt_tbl FUEL 0x83adc (add_cond crtC_sb_1e8 (mkAC BC_EQ (SOff 10 0) (SLit 0)))
  = (crtC_sc_1e8, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtC_pc_1e8 : ss_pc crtC_sc_1e8 = 0x83adc.
Proof. vm_compute. reflexivity. Qed.

(* B 0x8235c -> 0x83adc (A 0x82200 -> 0x838e8): pj_set (&doc, "state" 0x20f00, &state); B reads &doc from slot 0x38 *)
Definition crtC_ss_200 : sstate := crt_ss2 0x8235c.
Definition crtC_sb_200 : sstate :=
  Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL crtC_ss_200).
Lemma crtC_br_200 : sym_runN tfibsegs crt_tbl FUEL crtC_ss_200 = (crtC_sb_200, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtC_sc_200 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x83adc (add_cond crtC_sb_200 (mkAC BC_EQ (SOff 10 0) (SLit 0)))).
Lemma crtC_run_200 : sym_run_toN tfibsegs crt_tbl FUEL 0x83adc (add_cond crtC_sb_200 (mkAC BC_EQ (SOff 10 0) (SLit 0)))
  = (crtC_sc_200, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtC_pc_200 : ss_pc crtC_sc_200 = 0x83adc.
Proof. vm_compute. reflexivity. Qed.

(* B 0x82374 -> 0x83f94 (A 0x82218 -> 0x83d08): pj_write (&doc, 1); &doc from slot 0x38 *)
Definition crtC_ss_218 : sstate := crt_ss2 0x82374.
Definition crtC_sb_218 : sstate :=
  Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL crtC_ss_218).
Lemma crtC_br_218 : sym_runN tfibsegs crt_tbl FUEL crtC_ss_218 = (crtC_sb_218, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtC_sc_218 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x83f94 (add_cond crtC_sb_218 (mkAC BC_EQ (SOff 10 0) (SLit 0)))).
Lemma crtC_run_218 : sym_run_toN tfibsegs crt_tbl FUEL 0x83f94 (add_cond crtC_sb_218 (mkAC BC_EQ (SOff 10 0) (SLit 0)))
  = (crtC_sc_218, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtC_pc_218 : ss_pc crtC_sc_218 = 0x83f94.
Proof. vm_compute. reflexivity. Qed.

(* B 0x82384 -> 0x426c4 (A 0x82228 -> 0x42654): strlen (file) through __wrap_strlen; B tests a0 first (`beqz a0`
   0x82384), A loaded s2 first *)
Definition crtC_ss_228 : sstate := crt_ss2 0x82384.
Definition crtC_sb_228 : sstate :=
  Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL crtC_ss_228).
Lemma crtC_br_228 : sym_runN tfibsegs crt_tbl FUEL crtC_ss_228 = (crtC_sb_228, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtC_sc_228 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x426c4 (add_cond crtC_sb_228 (mkAC BC_NE (SOff 10 0) (SLit 0)))).
Lemma crtC_run_228 : sym_run_toN tfibsegs crt_tbl FUEL 0x426c4 (add_cond crtC_sb_228 (mkAC BC_NE (SOff 10 0) (SLit 0)))
  = (crtC_sc_228, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtC_pc_228 : ss_pc crtC_sc_228 = 0x426c4.
Proof. vm_compute. reflexivity. Qed.

(* B 0x82390 -> 0x82f3c (A 0x82238 -> 0x82eac): pj_parse (file, len, &back); &back from slot 0x20 *)
Definition crtC_ss_238 : sstate := crt_ss2 0x82390.
Definition crtC_sc_238 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x82f3c crtC_ss_238).
Lemma crtC_run_238 : sym_run_toN tfibsegs crt_tbl FUEL 0x82f3c crtC_ss_238 = (crtC_sc_238, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtC_pc_238 : ss_pc crtC_sc_238 = 0x82f3c.
Proof. vm_compute. reflexivity. Qed.

(* B 0x823a0 -> 0x83894 (A 0x82248 -> 0x83720): pj_get (&back, "state" 0x20f00); &back from slot 0x20 *)
Definition crtC_ss_248 : sstate := crt_ss2 0x823a0.
Definition crtC_sb_248 : sstate :=
  Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL crtC_ss_248).
Lemma crtC_br_248 : sym_runN tfibsegs crt_tbl FUEL crtC_ss_248 = (crtC_sb_248, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtC_sc_248 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x83894 (add_cond crtC_sb_248 (mkAC BC_EQ (SOff 10 0) (SLit 0)))).
Lemma crtC_run_248 : sym_run_toN tfibsegs crt_tbl FUEL 0x83894 (add_cond crtC_sb_248 (mkAC BC_EQ (SOff 10 0) (SLit 0)))
  = (crtC_sc_248, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtC_pc_248 : ss_pc crtC_sc_248 = 0x83894.
Proof. vm_compute. reflexivity. Qed.

(* B 0x823b4 -> 0x83a54 (A 0x8225c -> 0x83868): pj_get_str (r, "bytes" 0x20fc0) *)
Definition crtC_ss_25c : sstate := crt_ss2 0x823b4.
Definition crtC_sc_25c : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x83a54 crtC_ss_25c).
Lemma crtC_run_25c : sym_run_toN tfibsegs crt_tbl FUEL 0x83a54 crtC_ss_25c = (crtC_sc_25c, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtC_pc_25c : ss_pc crtC_sc_25c = 0x83a54.
Proof. vm_compute. reflexivity. Qed.

Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.

(* ================= the callee-side precondition at each program call of segment group C =================
   FSH_crt_site.crt_site_pre at the call-site state the engine measured (crtC_sc_<r>, above): the callee's fpreU with
   crt's frame record pushed (crt_ch1), the measured return address, the fake-frame bound, the
   room `sp + 32 <= ly_top`, and the argument registers as the boundary env's atoms (B: s2 = 18, s6 = 22, s7 = 23,
   s11 = 27, the previous callee's a0 = 10; A: s6 = 22 for v, s10 = 26 for doc) or the slot value the code loads (B:
   &doc = SOff 47 0x20 from slot 0x38, &back = SOff 47 0x140 from slot 0x20; atom 47 = F) or the literal the code
   materialises. The data premises of each spec are the boundary invariant's (FSH_crt_base crt_INV_<pc>). The R1 sites
   (B 0x823b0, 0x823bc): R1 hold - callee spec being restated in S0; this call's premises are re-checked when it lands. *)
(* B 0x82318 (A 0x821bc): pj_string (&v, "preset"), return 0x8231c *)
Lemma crtC_pre_821bc : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_base B cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 -> crt_frame_ok cx S3 W3 ms3 ->
  st_ok tfibsegs E crtC_sc_1ac (restrict (w_H W3) ms3) ->
  fpreU tfibsegs B STK_pj_string ly3 S3 U3 W3 (ms_regs ms3) (ms_mem ms3) md3 (crt_ch1 cx) /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE /\
  spZ (ms_regs ms3) + 32 <= ly_top ly3 /\
  raZ (ms_regs ms3) = 0x8231c /\
  YK11.getr (ms_regs ms3) 10%bv = sv_denot E (SOff 27 0) /\
  YK11.getr (ms_regs ms3) 11%bv = sv_denot E (SLit 0x20f80).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU3 HFR HS.
destruct (crt_site_pre SK B cx E k ly3 S3 U3 W3 ms3 md3 crtC_sc_1ac 0x8231c STK_pj_string HB HE HJ HARU3 HFR HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(vm_compute; reflexivity)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.leb_le; vm_compute; reflexivity))
  as (HP & Hra & HF & HR).
split; [exact HP|].
split; [exact HF|]. split; [exact HR|]. split; [exact Hra|].
split; [rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_1ac ms3 10%bv HS); reflexivity|].
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_1ac ms3 11%bv HS); reflexivity.
Qed.

(* B 0x82330 (A 0x821d4): pj_set (&state, "context", &v), return 0x82334 *)
Lemma crtC_pre_821d4 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_base B cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 -> crt_frame_ok cx S3 W3 ms3 ->
  st_ok tfibsegs E crtC_sc_1c0 (restrict (w_H W3) ms3) ->
  fpreU tfibsegs B STK_pj_set ly3 S3 U3 W3 (ms_regs ms3) (ms_mem ms3) md3 (crt_ch1 cx) /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE /\
  spZ (ms_regs ms3) + 32 <= ly_top ly3 /\
  raZ (ms_regs ms3) = 0x82334 /\
  YK11.getr (ms_regs ms3) 10%bv = sv_denot E (SOff 23 0) /\
  YK11.getr (ms_regs ms3) 11%bv = sv_denot E (SLit 0x20fa0) /\
  YK11.getr (ms_regs ms3) 12%bv = sv_denot E (SOff 27 0).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU3 HFR HS.
destruct (crt_site_pre SK B cx E k ly3 S3 U3 W3 ms3 md3 crtC_sc_1c0 0x82334 STK_pj_set HB HE HJ HARU3 HFR HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(vm_compute; reflexivity)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.leb_le; vm_compute; reflexivity))
  as (HP & Hra & HF & HR).
split; [exact HP|].
split; [exact HF|]. split; [exact HR|]. split; [exact Hra|].
split; [rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_1c0 ms3 10%bv HS); reflexivity|].
split; [rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_1c0 ms3 11%bv HS); reflexivity|].
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_1c0 ms3 12%bv HS); reflexivity.
Qed.

(* B 0x82340 (A 0x821e4): pj_string (&v, text), return 0x82344 *)
Lemma crtC_pre_821e4 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_base B cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 -> crt_frame_ok cx S3 W3 ms3 ->
  st_ok tfibsegs E crtC_sc_1d8 (restrict (w_H W3) ms3) ->
  fpreU tfibsegs B STK_pj_string ly3 S3 U3 W3 (ms_regs ms3) (ms_mem ms3) md3 (crt_ch1 cx) /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE /\
  spZ (ms_regs ms3) + 32 <= ly_top ly3 /\
  raZ (ms_regs ms3) = 0x82344 /\
  YK11.getr (ms_regs ms3) 10%bv = sv_denot E (SOff 27 0) /\
  YK11.getr (ms_regs ms3) 11%bv = sv_denot E (SOff 18 0).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU3 HFR HS.
destruct (crt_site_pre SK B cx E k ly3 S3 U3 W3 ms3 md3 crtC_sc_1d8 0x82344 STK_pj_string HB HE HJ HARU3 HFR HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(vm_compute; reflexivity)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.leb_le; vm_compute; reflexivity))
  as (HP & Hra & HF & HR).
split; [exact HP|].
split; [exact HF|]. split; [exact HR|]. split; [exact Hra|].
split; [rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_1d8 ms3 10%bv HS); reflexivity|].
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_1d8 ms3 11%bv HS); reflexivity.
Qed.

(* B 0x82358 (A 0x821fc): pj_set (&state, "bytes", &v), return 0x8235c *)
Lemma crtC_pre_821fc : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_base B cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 -> crt_frame_ok cx S3 W3 ms3 ->
  st_ok tfibsegs E crtC_sc_1e8 (restrict (w_H W3) ms3) ->
  fpreU tfibsegs B STK_pj_set ly3 S3 U3 W3 (ms_regs ms3) (ms_mem ms3) md3 (crt_ch1 cx) /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE /\
  spZ (ms_regs ms3) + 32 <= ly_top ly3 /\
  raZ (ms_regs ms3) = 0x8235c /\
  YK11.getr (ms_regs ms3) 10%bv = sv_denot E (SOff 23 0) /\
  YK11.getr (ms_regs ms3) 11%bv = sv_denot E (SLit 0x20fc0) /\
  YK11.getr (ms_regs ms3) 12%bv = sv_denot E (SOff 27 0).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU3 HFR HS.
destruct (crt_site_pre SK B cx E k ly3 S3 U3 W3 ms3 md3 crtC_sc_1e8 0x8235c STK_pj_set HB HE HJ HARU3 HFR HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(vm_compute; reflexivity)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.leb_le; vm_compute; reflexivity))
  as (HP & Hra & HF & HR).
split; [exact HP|].
split; [exact HF|]. split; [exact HR|]. split; [exact Hra|].
split; [rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_1e8 ms3 10%bv HS); reflexivity|].
split; [rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_1e8 ms3 11%bv HS); reflexivity|].
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_1e8 ms3 12%bv HS); reflexivity.
Qed.

(* B 0x82370 (A 0x82214): pj_set (&doc, "state", &state), return 0x82374; &doc = F + 0x20 from slot 0x38 (A: s10) *)
Lemma crtC_pre_82214 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_base B cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 -> crt_frame_ok cx S3 W3 ms3 ->
  st_ok tfibsegs E crtC_sc_200 (restrict (w_H W3) ms3) ->
  fpreU tfibsegs B STK_pj_set ly3 S3 U3 W3 (ms_regs ms3) (ms_mem ms3) md3 (crt_ch1 cx) /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE /\
  spZ (ms_regs ms3) + 32 <= ly_top ly3 /\
  raZ (ms_regs ms3) = 0x82374 /\
  YK11.getr (ms_regs ms3) 10%bv = sv_denot E (SOff 47 0x20) /\
  YK11.getr (ms_regs ms3) 11%bv = sv_denot E (SLit 0x20f00) /\
  YK11.getr (ms_regs ms3) 12%bv = sv_denot E (SOff 23 0).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU3 HFR HS.
destruct (crt_site_pre SK B cx E k ly3 S3 U3 W3 ms3 md3 crtC_sc_200 0x82374 STK_pj_set HB HE HJ HARU3 HFR HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(vm_compute; reflexivity)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.leb_le; vm_compute; reflexivity))
  as (HP & Hra & HF & HR).
split; [exact HP|].
split; [exact HF|]. split; [exact HR|]. split; [exact Hra|].
split; [rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_200 ms3 10%bv HS); reflexivity|].
split; [rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_200 ms3 11%bv HS); reflexivity|].
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_200 ms3 12%bv HS); reflexivity.
Qed.

(* B 0x82380 (A 0x82224): pj_write (&doc, 1), return 0x82384; &doc from slot 0x38 (A: s10) *)
Lemma crtC_pre_82224 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_base B cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 -> crt_frame_ok cx S3 W3 ms3 ->
  st_ok tfibsegs E crtC_sc_218 (restrict (w_H W3) ms3) ->
  fpreU tfibsegs B STK_pj_write ly3 S3 U3 W3 (ms_regs ms3) (ms_mem ms3) md3 (crt_ch1 cx) /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE /\
  spZ (ms_regs ms3) + 32 <= ly_top ly3 /\
  raZ (ms_regs ms3) = 0x82384 /\
  YK11.getr (ms_regs ms3) 10%bv = sv_denot E (SOff 47 0x20) /\
  YK11.getr (ms_regs ms3) 11%bv = sv_denot E (SLit 1).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU3 HFR HS.
destruct (crt_site_pre SK B cx E k ly3 S3 U3 W3 ms3 md3 crtC_sc_218 0x82384 STK_pj_write HB HE HJ HARU3 HFR HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(vm_compute; reflexivity)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.leb_le; vm_compute; reflexivity))
  as (HP & Hra & HF & HR).
split; [exact HP|].
split; [exact HF|]. split; [exact HR|]. split; [exact Hra|].
split; [rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_218 ms3 10%bv HS); reflexivity|].
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_218 ms3 11%bv HS); reflexivity.
Qed.

(* B 0x8239c (A 0x82244): pj_parse (file, len, &back), return 0x823a0; &back = F + 0x140 from slot 0x20 (A: s2) *)
Lemma crtC_pre_82244 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_base B cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 -> crt_frame_ok cx S3 W3 ms3 ->
  st_ok tfibsegs E crtC_sc_238 (restrict (w_H W3) ms3) ->
  fpreU tfibsegs B STK_pj_parse ly3 S3 U3 W3 (ms_regs ms3) (ms_mem ms3) md3 (crt_ch1 cx) /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE /\
  spZ (ms_regs ms3) + 32 <= ly_top ly3 /\
  raZ (ms_regs ms3) = 0x823a0 /\
  YK11.getr (ms_regs ms3) 10%bv = sv_denot E (SOff 22 0) /\
  YK11.getr (ms_regs ms3) 11%bv = sv_denot E (SOff 10 0) /\
  YK11.getr (ms_regs ms3) 12%bv = sv_denot E (SOff 47 0x140).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU3 HFR HS.
destruct (crt_site_pre SK B cx E k ly3 S3 U3 W3 ms3 md3 crtC_sc_238 0x823a0 STK_pj_parse HB HE HJ HARU3 HFR HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(vm_compute; reflexivity)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.leb_le; vm_compute; reflexivity))
  as (HP & Hra & HF & HR).
split; [exact HP|].
split; [exact HF|]. split; [exact HR|]. split; [exact Hra|].
split; [rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_238 ms3 10%bv HS); reflexivity|].
split; [rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_238 ms3 11%bv HS); reflexivity|].
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_238 ms3 12%bv HS); reflexivity.
Qed.

(* B 0x823b0 (A 0x82258): pj_get (&back, "state")  [R1 hold], return 0x823b4; &back from slot 0x20 (A: s2) *)
Lemma crtC_pre_82258 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_base B cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 -> crt_frame_ok cx S3 W3 ms3 ->
  st_ok tfibsegs E crtC_sc_248 (restrict (w_H W3) ms3) ->
  fpreU tfibsegs B STK_pj_get ly3 S3 U3 W3 (ms_regs ms3) (ms_mem ms3) md3 (crt_ch1 cx) /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE /\
  spZ (ms_regs ms3) + 32 <= ly_top ly3 /\
  raZ (ms_regs ms3) = 0x823b4 /\
  YK11.getr (ms_regs ms3) 10%bv = sv_denot E (SOff 47 0x140) /\
  YK11.getr (ms_regs ms3) 11%bv = sv_denot E (SLit 0x20f00).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU3 HFR HS.
destruct (crt_site_pre SK B cx E k ly3 S3 U3 W3 ms3 md3 crtC_sc_248 0x823b4 STK_pj_get HB HE HJ HARU3 HFR HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(vm_compute; reflexivity)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.leb_le; vm_compute; reflexivity))
  as (HP & Hra & HF & HR).
split; [exact HP|].
split; [exact HF|]. split; [exact HR|]. split; [exact Hra|].
split; [rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_248 ms3 10%bv HS); reflexivity|].
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_248 ms3 11%bv HS); reflexivity.
Qed.

(* B 0x823bc (A 0x82264): pj_get_str (r, "bytes")  [R1 hold], return 0x823c0 *)
Lemma crtC_pre_82264 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_base B cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 -> crt_frame_ok cx S3 W3 ms3 ->
  st_ok tfibsegs E crtC_sc_25c (restrict (w_H W3) ms3) ->
  fpreU tfibsegs B STK_pj_get_str ly3 S3 U3 W3 (ms_regs ms3) (ms_mem ms3) md3 (crt_ch1 cx) /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE /\
  spZ (ms_regs ms3) + 32 <= ly_top ly3 /\
  raZ (ms_regs ms3) = 0x823c0 /\
  YK11.getr (ms_regs ms3) 10%bv = sv_denot E (SOff 10 0) /\
  YK11.getr (ms_regs ms3) 11%bv = sv_denot E (SLit 0x20fc0).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU3 HFR HS.
destruct (crt_site_pre SK B cx E k ly3 S3 U3 W3 ms3 md3 crtC_sc_25c 0x823c0 STK_pj_get_str HB HE HJ HARU3 HFR HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(vm_compute; reflexivity)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.leb_le; vm_compute; reflexivity))
  as (HP & Hra & HF & HR).
split; [exact HP|].
split; [exact HF|]. split; [exact HR|]. split; [exact Hra|].
split; [rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_25c ms3 10%bv HS); reflexivity|].
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_25c ms3 11%bv HS); reflexivity.
Qed.

(* B 0x8238c (A 0x82234): strlen (file) through __wrap_strlen (FsRt.fr_strlen, astrlen_realizesU), return 0x82390. A
   runtime call: the callee-side precondition is ecall_preU_k STK_RT_STR (FSW_K.fsw_ecall_preU_k_at at o = s1 - s0),
   with the argument a0 = pj_write's answer (the boundary's atom 10, kept by `mv s6, a0` 0x82388) *)
Lemma crtC_pre_82234 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_base B cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  st_ok tfibsegs E crtC_sc_228 (restrict (w_H W3) ms3) ->
  ecall_preU_k tfibsegs B STK_RT_STR ly3 S3 U3 W3 (ms_regs ms3) (ms_mem ms3) md3 /\
  raZ (ms_regs ms3) = 0x82390 /\
  YK11.getr (ms_regs ms3) 10%bv = sv_denot E (SOff 10 0).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU3 HS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HE as (E2v & E3v & E4v & E8v & _).
pose proof HB as ((HPRE0 & _) & _). destruct HPRE0 as ((_ & _ & _ & Hgp0 & Htp0 & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTKv : 8192 + 208 <= STK_check_round_trip) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia)
  ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as ((Flo & Fhi) & Fm32 & Fm16).
assert (Hsp1m : crt_sp1 cx mod 16 = 0) by (unfold crt_sp1; exact Fm16).
assert (Hsp1lo : spZ (c_regs cx) - 208 <= crt_sp1 cx) by (unfold crt_sp1; lia).
assert (Hsp1hi : crt_sp1 cx <= spZ (c_regs cx) - 192) by (unfold crt_sp1; lia).
assert (R1 : YK11.getr (ms_regs ms3) 1%bv = Z_to_bv 64 0x82390)
  by exact (fsw_reg_lit (w_H W3) E crtC_sc_228 ms3 1%bv 0x82390 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R2 : spZ (ms_regs ms3) = crt_sp1 cx).
{ unfold spZ. rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_228 ms3 2%bv HS).
  change (sr_get (ss_regs crtC_sc_228) 2%bv) with (SOff 2 0). rewrite fsw_SOff0. exact E2v. }
assert (R3 : YK11.getr (ms_regs ms3) 3%bv = YK11.getr (c_regs cx) 3%bv).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_228 ms3 3%bv HS).
  change (sr_get (ss_regs crtC_sc_228) 3%bv) with (SOff 3 0). rewrite fsw_SOff0. exact E3v. }
assert (R4 : YK11.getr (ms_regs ms3) 4%bv = YK11.getr (c_regs cx) 4%bv).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_228 ms3 4%bv HS).
  change (sr_get (ss_regs crtC_sc_228) 4%bv) with (SOff 4 0). rewrite fsw_SOff0. exact E4v. }
split.
- eapply (fsw_ecall_preU_k_at B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 (ms_mem ms3) md3 k (ms_regs ms3)
    (crt_sp1 cx - spZ (c_regs cx)) STK_RT_STR HJ HARU3).
  + rewrite R2. lia.
  + rewrite Zminus_mod, Hsp1m, Hal16. reflexivity.
  + lia.
  + unfold ESTACK. lia.
  + unfold STK_RT_STR, ESTACK. lia.
  + unfold STK_RT_STR, ESTACK. lia.
  + rewrite R1. vm_compute. reflexivity.
  + rewrite R3. exact Hgp0.
  + rewrite R4. exact Htp0.
- split; [unfold raZ; rewrite R1; apply wz; lia|].
  rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtC_sc_228 ms3 10%bv HS). reflexivity.
Qed.

End q.

(* ================= the image keys of segment group C =================
   The four read-only strings the group passes (FS_RO_STRS entries, at the same addresses on B): "preset" 0x20f80
   (pj_string's s at B 0x82318), "context" 0x20fa0 and "bytes" 0x20fc0 (pj_set keys at B 0x82330 / 0x82358; "bytes" is
   also pj_get_str's key at B 0x823bc), "state" 0x20f00 (pj_set key at B 0x82370 and pj_get's key at B 0x823b0). At
   every state of the walk each is
   cstr_ok on the machine's memory (FSW_strkit.cstr_ok_kept_tbl from the image facts IMG, ARU and the read-only image
   crt_rodata carries) and cstr_kept by its table arm (U taken, S0 4a924247f5f). IMG is a fact about B alone (RELOC /
   TfibB discharge it in the final instance), the reader and writer files' own name. *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.
Lemma crtC_key : forall cx k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 p l,
  crt_base B cx ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  In (p, l) FS_RO_STRS ->
  cstr_ok tfibsegs W3 (ms_mem ms3) p l /\ cstr_kept B ly3 S3 U3 p l.
Proof.
intros cx k ly3 S3 U3 W3 ms3 md3 p l HB HJ HARU3 Hin. split.
- exact (cstr_ok_kept_tbl B ly3 S3 U3 W3 (ms_mem ms3) md3 p l IMG HARU3
    (crt_rodata SK B cx k ly3 S3 U3 W3 ms3 md3 HB HJ HARU3) (or_introl Hin)).
- right. left. exact Hin.
Qed.
Lemma crtC_in_preset : In (0x20f80, [112; 114; 101; 115; 101; 116]) FS_RO_STRS.
Proof. unfold FS_RO_STRS. cbn [In]. repeat (first [left; reflexivity | right]). Qed.
Lemma crtC_in_context : In (0x20fa0, [99; 111; 110; 116; 101; 120; 116]) FS_RO_STRS.
Proof. unfold FS_RO_STRS. cbn [In]. repeat (first [left; reflexivity | right]). Qed.
Lemma crtC_in_bytes : In (0x20fc0, [98; 121; 116; 101; 115]) FS_RO_STRS.
Proof. unfold FS_RO_STRS. cbn [In]. repeat (first [left; reflexivity | right]). Qed.
Lemma crtC_in_state : In (0x20f00, [115; 116; 97; 116; 101]) FS_RO_STRS.
Proof. unfold FS_RO_STRS. cbn [In]. repeat (first [left; reflexivity | right]). Qed.
End k.

(* ================= the FP relation of each call (FSW_K3.fsw_fp_sub, the after-call's four arms) =================
   Every callee footprint of segment group C splits into: fs's statics (the static arm: FS_PSTAT_FP is crt's own FP and
   image bytes, FSH_crt_base.crt_pstat_img), objects of crt's class-3 frame (the own-frame arm), and for pj_set the old
   kids / keys blocks grow may free (the tmp-block arm: blocks the walk itself allocated, not crt's entry blocks - a
   fact the boundary invariant carries, a premise here). pj_get / pj_get_str post FP = []. pj_write's post (S0
   10ffef27396, FSH_Fn_writer.v pj_write_spec) has window top spZ regs and FP = FS_PSTAT_FP, so its after-call is the
   ordinary crt_after_call with crtC_fpsub_static; it has no raised top and no wkeep at crt's call. *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma crtC_fpsub_static : forall ly S lyc Sc own, fsw_fp_sub B ly S lyc Sc own FS_PSTAT_FP FS_PSTAT_FP.
Proof. intros ly S lyc Sc own a Ha. right; right; left. split; [exact Ha | exact (crt_pstat_img a Ha)]. Qed.
Lemma crtC_fpsub_nil : forall ly S lyc Sc own FP, fsw_fp_sub B ly S lyc Sc own FP [].
Proof. intros ly S lyc Sc own FP a Ha. exfalso. exact (inFP_nil a Ha). Qed.
(* one object of crt's frame (pj_string's v = F + 0xe0, pj_parse's out = F + 0x140), then the statics *)
Lemma crtC_fpsub_obj : forall ly S lyc Sc pos off,
  0 <= off -> off + 56 <= 512 ->
  fsw_fp_sub B ly S lyc Sc [(3, pos)] FS_PSTAT_FP
    ([(frame_addr lyc 3 pos + off, frame_addr lyc 3 pos + off + 56)] ++ FS_PSTAT_FP).
Proof.
intros ly S lyc Sc pos off H0 H1 a Ha. apply inFP_app in Ha as [Ha | Ha].
- right; right; right; left. apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
  exists 3, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite crt_frame3. lia.
- exact (crtC_fpsub_static ly S lyc Sc [(3, pos)] a Ha).
Qed.
(* pj_set at obj F + oo, val F + ow: the two object ranges, the old blocks grow may free, the statics *)
Lemma crtC_fpsub_pjset : forall ly S lyc Sc pos oo ow Dold0,
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
  + exact (crtC_fpsub_static ly S lyc Sc [(3, pos)] a Ha).
Qed.
End f.

(* ---- the frame's tail is outside every callee footprint of the group ----
   crt_after_call asks that no byte of csF's chunks and none of the flag word [F + 504, F + 512) is in the callee's FP.
   Every FP of segment group C lies below F + 0x178 inside the frame (doc, state, v, back end there), or in a heap block
   (apart from the frame, YCbq.sep_block_frame), or in fs's statics (image bytes, which no frame holds, YCbq.frm_img). *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Lemma crtC_tail_free : forall lyc Sc (W : world tfibsegs) mem md pos FPc,
  AR tfibsegs B lyc Sc W mem md -> In (3, pos) (frames Sc) ->
  (forall a, inFP FPc a -> a < frame_addr lyc 3 pos + 0x178 \/
     (exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/ inFP FS_PSTAT_FP a) ->
  forall a, frame_addr lyc 3 pos + 0x178 <= a < frame_addr lyc 3 pos + 512 -> ~ inFP FPc a.
Proof.
intros lyc Sc W mem md pos FPc HAR Hin HFP a Ha Hf.
destruct (HFP a Hf) as [Hlt | [(b & n & Hbn & Hr) | Hp]]; [lia| |].
- pose proof (sep_block_frame tfibsegs B LAWS lyc Sc W mem md b n 3 pos HAR Hbn Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite crt_frame3 in Hd. lia.
- exact (frm_img tfibsegs B LAWS lyc Sc W mem md 3 pos a HAR Hin ltac:(rewrite crt_frame3; lia) (crt_pstat_img a Hp)).
Qed.
(* the two premises of crt_after_call it closes, at csF = crt_csF (the flag word only) *)
Lemma crtC_csF_free : forall lyc Sc (W : world tfibsegs) mem md pos FPc,
  AR tfibsegs B lyc Sc W mem md -> In (3, pos) (frames Sc) ->
  (forall a, inFP FPc a -> a < frame_addr lyc 3 pos + 0x178 \/
     (exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/ inFP FS_PSTAT_FP a) ->
  (forall c, In c crt_csF -> forall i, 0 <= i < YP09.c_len c -> ~ inFP FPc (frame_addr lyc 3 pos + YP09.c_off c + i)) /\
  (forall i, 0 <= i < 8 -> ~ inFP FPc (frame_addr lyc 3 pos + fs_frame_bytes 3 - 8 + i)).
Proof.
intros lyc Sc W mem md pos FPc HAR Hin HFP. split.
- intros c Hc i Hi. unfold crt_csF in Hc. cbn [In] in Hc. destruct Hc as [<- | []].
  cbn [YP09.c_off] in Hi |- *. rewrite crt_frame3.
  apply (crtC_tail_free lyc Sc W mem md pos FPc HAR Hin HFP). cbn in Hi. lia.
- intros i Hi. rewrite crt_frame3. apply (crtC_tail_free lyc Sc W mem md pos FPc HAR Hin HFP). lia.
Qed.
End t.

(* ================= what a zero-footprint call keeps (pj_get B 0x823b0, pj_get_str B 0x823bc) =================
   Their posts carry FP = [], so the callee journal's block, frame and image clauses hold with no exception: every byte
   of a block live at both ends, every byte of a live fake frame and of its shadow, and every read-only image byte
   outside fs's owned statics reads the same after the call. This is the transport the two segments need for the
   invariant's data conjuncts (the trees, the blocks, the n cell); the walk's own stack window is kept by
   crt_kept_stack. *)
Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Lemma crtC_keep_nilFP : forall STKc sp1 lyc Sc Uc (W : world tfibsegs) memC mdC ly' S' U' W' mem' md' kc,
  ajournal tfibsegs B STKc sp1 [] lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  (forall p n i, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
     aview tfibsegs (w_H W') (unpoison U' mem') (p + i) = aview tfibsegs (w_H W) (unpoison Uc memC) (p + i)) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     aview tfibsegs (w_H W') (unpoison U' mem') a = aview tfibsegs (w_H W) (unpoison Uc memC) a) /\
  (forall a, in_img tfibsegs a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) ->
     aview tfibsegs (w_H W') (unpoison U' mem') a = aview tfibsegs (w_H W) (unpoison Uc memC) a).
Proof.
intros STKc sp1 lyc Sc Uc W memC mdC ly' S' U' W' mem' md' kc HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & F3 & F4 & _).
split; [|split].
- intros p n i H1 H2 Hi. exact (F2 p n i H1 H2 Hi (inFP_nil (p + i))).
- intros cid pos a Hin Hr. exact (F4 cid pos a Hin Hr (inFP_nil a)).
- intros a Hi Ho He. exact (F3 a Hi Ho He (inFP_nil a) (fp_spares_closed [] a (fun H => inFP_nil 0 H))).
Qed.
End z.
