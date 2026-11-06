(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: the ROOM round (an internal work row), A's re-fit git diff f6bfd4d6ab5 f6038f3d481
   of lib/A/W_gesture_model.v applied by three-way merge onto lane W4's ARx text (a working branch
   0d0105eaf4d) at B's names: pb_gesture_model_x states gm_spec_x at RP (gm_rm_down drops the unused budget on the
   early-return arms) and passes the room premises to GMSCAN_X. The AR statements (Section r) are W4's, unchanged. *)
(* Modified by Theorem Labs, 2026-10: the IMAGE B (asan-ubsan) walk of fuzz_reply's gesture_model at 0x86048, lane
   W4: the entry and the composition, in the form of lib/A/W_gesture_model.v (A's proved composition, 0x85b9c) and the
   cgif walks of proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites) and lib/A/ACbk.v (entry and return). *)
(* Modified by Theorem Labs, 2026-10: the meter at the KF-COUNT kit's gm_cost H ln (the trace's charge), A's re-fit of
   lib/A/W_gesture_model.v at B's names: GMSCAN_X's meter and room texts take the line; the three early returns name no
   gesture and are charged 0 (gmm_cost_none). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_gesture_model.v; 15 of its 114 lines of code are new or changed and 1320 lines of the source are left out. *)
(* Satisfiability at the real image B of the R contract texts (W_contract_xR_g6.v), at R := wle' SEGS RZ_cf: each
   lemma derives the R form from the existing strict walk, under that walk's own Section hypotheses. The import block
   is the walk file's (W_gesture_model.v), so each hypothesis reads as there. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08 YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame W_gm_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x W_kit_x.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Import RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_gesture_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.

(* pb_gesture_model_xR_sat: gm_spec_xR at R := wle' SEGS RZ_cf, from W_gesture_model.pb_gesture_model_x by gm_spec_xR_of_x and YA0nH.wle_wle'. The
   Section hypotheses are pb_gesture_model_x's own (W_gesture_model.v, Sections a / b / c), unchanged; their comments are left out. *)
Section sat_pb_gesture_model_x.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis LFIND : lfind_spec_x B PST ARx G (BASE + AF_fr_list_find).
Hypothesis LPUSH : lp_spec_x B PST ARx MT RP G MMAX (BASE + AF_fr_list_push).
Hypothesis LDROP : ldrop_spec_x B PST ARx MT RP G (BASE + AF_fr_list_drop).
Hypothesis HLITG : ashp_x ARx (VAL A_lit_gesture) 13.
Hypothesis HLITB : ashp_x ARx (VAL A_lit_begin) 5.
Hypothesis HLITE : ashp_x ARx (VAL A_lit_end) 3.
Hypothesis GMSCAN_X : forall W ly S Hp regs mem md ch HA LINE (ln : list byte) H q k (j : Z) regsc memc mdc,
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 HA -> getr regs 11 = w64 LINE -> getr regs 12 = w64 (Z.of_nat (length ln)) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
rom_view SEGS W mem ->
(lp_grow H = true -> lp_vbytes H < MMAX) -> AREC * hl_cap H < 2 ^ 32 ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) ->
cnt_ok_pk RP (gm_pk H) (ablocks B ly S) ->
firstn 13 (bzs ln) = RelayModel.K_GESTURE ->
nth 13 (bzs ln) 0 = RelayModel.SPACE ->
4096 <= LINE -> LINE + Z.of_nat (length ln) <= 140737479966720 -> HA mod 8 = 0 ->
spZ regsc = spZ regs - GM_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 LINE -> getr regsc 9 = w64 HA ->
getr regsc 18 = w64 (Z.of_nat (length ln)) -> getr regsc 19 = w64 SB ->
(forall r, acallee_saved r -> 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem SEGS (arm W memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm W memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm W memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm W memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm W memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a) ->
ajournal_gx_x SEGS B PST ARx G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
getr regsc 10 = w64 j -> getr regsc 11 = w64 (2 ^ 64 - 1 - LINE) ->
getr regsc 12 = w64 (LINE + Z.of_nat (length ln)) -> getr regsc 13 = w64 32 ->
getr regsc 14 = w64 (2 ^ 64 - Z.of_nat (length ln)) ->
getr regsc 15 = w64 (LINE + Z.of_nat (length ln) - 1) ->
14 <= Z.of_nat (length ln) -> 13 < Z.of_nat (length ln) + j -> j <= 0 ->
(forall t, Z.of_nat (length ln) + j <= t < Z.of_nat (length ln) ->
 nth (Z.to_nat t) (bzs ln) 0 <> RelayModel.SPACE) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_loop)) memc (seg_rom SEGS)) mdc)
(gm_post_x B PST ARx MT RP G regs ly S Hp W mem md HA H ln kr).
Theorem pb_gesture_model_xR_sat :
  gm_spec_xR B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) MT RP MMAX G A_gesture_modelP.
Proof.
apply gm_spec_xR_of_x; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) |].
eapply W_gesture_model.pb_gesture_model_x; eassumption.
Qed.
End sat_pb_gesture_model_x.
