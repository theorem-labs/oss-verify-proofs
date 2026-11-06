(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the image-B (asan-ubsan) walk of plugin-hostd/fuzz_reply's list_push
   (0x85324, 223 instructions, frame 96), proving lib/B/W_contract.v's lp_spec / lp_spec_g at
   BASE + AF_fr_list_push (lib/B/W_listing.v:23, 0x2fe0).  Written in the shape of the image-A walk
   (a working branch ff4c06b2f3a, lib/A/W_list_push.v + lib/A/W_lp_tail.v + lib/A/W_list_push_tail.v, Qed),
   over lib/B's own listing: image B is NOT a relocation of image A (UBSan runs in trap mode here, so every
   check is an inline branch to `unimp`, which changes the register allocation and inserts 19 trap branches in
   this function).  The A tail files are inlined here as one lemma (lp_tail_seg), as the lane gets one new file.

   The walk: list_push(l, s, n) reads l->n and l->cap; when the list is full it grows the vector with realloc
   (8 entries, then doubling), copies the n source bytes into a fresh malloc'd block of n + 1 bytes with
   __asan_memcpy, NUL-terminates it and appends (block, n) to the vector.  Four cuts:
     SEG1  0x85324 .. the realloc call 0x853e0 (grow) or the malloc call 0x85404 (room),
     SEG2  the realloc return 0x853e4 .. the malloc call 0x85404   (lp_grow_seg),
     SEG3  the malloc return 0x85408 .. the __asan_memcpy call 0x8547c,
     SEG4  the memcpy return 0x85480 .. the ret 0x855bc            (SEG3/SEG4: lp_tail_seg).
   realloc goes through ARE (arealloc_cf_rule_c_x at CTX_R), malloc through AMA (amalloc_cf_rule_c_x at CTX_M), __asan_memcpy through
   AMEMCPY (aintrin_realizes_x OCpy); the forced-success posts refute the NULL arms (0x853e4, 0x85470 /
   __asan_handle_no_return; abort).

   The 19 UBSan trap branches to the `unimp` at 0x855c0 (census: TRAPS-CENSUS.md (sha256 b33c2b52103e; internal record)).
   Seven of them stop the runner and are closed with lib/B/W_traps.v (a Theorem Labs lane), the other twelve the runner
   decides itself from this walk's facts:
     0x85360  ALIGN8 LA              trap_align8      (lp_spec's LA mod 8 = 0)
     0x853bc  INT32 DOUBLING         runner           (fact atom 34: cap <= 2 ^ 30 - 1, from alist_at)
     0x85434  NULL-CONS (beq)        trap_br_eq + trap_U_seqz   (v + 16 n >= 4096; snez v folded to 1)
     0x85448  PTR-OVF (signed index) trap_ptr_sovf + trap_U_sltu_ge  (v <= v + 16 n; slti n,0 folded to 0)
     0x8544c  NON-NULL v             runner           (fact atom 44: 4096 <= v)
     0x85454  ALIGN8 v + 16 n        trap_align8      (v is 16-aligned: al_blocks)
     0x8546c  NON-NULL v + 16 n      trap_nonnull
     0x854a8  NULL-CONS (beq)        runner           (the same condition, already assumed at 0x85434)
     0x854bc  PTR-OVF                runner           (assumed at 0x85448)
     0x854c0  NON-NULL v             runner           (fact atom 44)
     0x854c8  ALIGN8 v + 16 n        runner           (assumed at 0x85454)
     0x854e4  PTR-OVF (bltu) d + n   trap_ptr_bltu
     0x854f4  NULL-CONS (xor)        trap_br_eq + trap_U_seqz   (d + n >= 4096; snez d folded to 1)
     0x854f8  NON-NULL d             runner           (fact atom 52: 4096 <= d)
     0x85538  NULL-CONS (beq)        runner           (assumed at 0x85434)
     0x8554c  PTR-OVF                runner           (assumed at 0x85448)
     0x85550  NON-NULL v             runner           (fact atom 44)
     0x85558  ALIGN8 v + 16 n        runner           (assumed at 0x85454)
     0x85578  INT32 +1 (n + 1)       runner           (fact atom 45: n <= 2 ^ 30 - 1)
   B's frame is 96 bytes (0x85324 `addi sp,sp,-96`, ra at 88, s0 .. s10 at 80 .. 0), so LP_STK = 96 + ASTACK
   holds unchanged from image A.  Registers differ from A only in s5 / s6: B keeps the shadow base SB in s6
   (atom 22) and the shadow address of l->n in s5 (atom 21); A has them the other way round.

   The room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record) and C3, as image A's F1b (lib/A/W_list_push.v / W_lp_tail.v at
   e32cc1247c0): the Sections take the room record RP; lp_spec_x's live bytes are C3's peak over list_push's trace
   (lp_peak_grow / lp_peak_nogrow give each call's own premise), its room budget 3 (grow) or 1 (lp_rk_eq) is spent as
   realloc's 2 and the tail malloc's 1, and its peak-form counts give each call's count premise (lp_cnt_at at S; at the
   tail after realloc, S's counts plus the new vector, the old one gone).  lp_tail_pre_x (local here; image A's is
   lib/A/W_list_push_tail.v's text) takes kr and carries the tail malloc's rp_RM RP Sc (1 + kr) and cnt_ok at Sc,
   word for word as image A's; the malloc's stack room comes from the call's journal (W_journal_x.aj_stack_room_x). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_list_push.v; 39 of its 109 lines of code are new or changed and 3669 lines of the source are left out. *)
(* Satisfiability at the real image B of the R contract texts (W_contract_xR.v), at R := wle' SEGS RZ_cf: each
   lemma derives the R form from the existing strict walk, under that walk's own Section hypotheses. The import block
   is the walk file's (W_list_push.v), so each hypothesis reads as there. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State
Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15
YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06
YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d YI00 YN0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_journal W_rep
W_contract W_frame W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_kit_xb W_journal_x W_contract_x
W_sites_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_list_push.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.

(* pb_list_push_xR_sat: lp_spec_xR at R := wle' SEGS RZ_cf, from W_list_push.pb_list_push_x by lp_spec_xR_of_x and YA0nH.wle_wle'. The Section
   hypotheses are pb_list_push_x's own (W_list_push.v, Sections a / b / c), unchanged; their comments are left out. *)
Section sat1.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Variable RP : roomp.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
Hypothesis HMMAX : 2 ^ 29 < MMAX <= 2 ^ 30.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok SEGS B G.
Hypothesis HGR : gx_rt B G.
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Variable CTX_R : list (list Z).
Hypothesis ARE : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_lp_realloc : In [BASE + AF_fr_list_push + 0xc0] CTX_R.
Variable CTX_M : list (list Z).
Hypothesis AMA : amalloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_M.
Hypothesis HCTX_lp_malloc : In [BASE + AF_fr_list_push + 0xe4] CTX_M.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Theorem pb_list_push_xR_sat :
  lp_spec_xR B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) MT RP G MMAX (BASE + AF_fr_list_push).
Proof.
apply lp_spec_xR_of_x; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) |].
eapply W_list_push.pb_list_push_x; eassumption.
Qed.
End sat1.

(* pb_list_push_g_xR_sat: lp_spec_g_xR at R := wle' SEGS RZ_cf, from W_list_push.pb_list_push_g_x by lp_spec_g_xR_of_x and YA0nH.wle_wle'. The Section
   hypotheses are pb_list_push_g_x's own (W_list_push.v, Sections a / b / g), unchanged; their comments are left out. *)
Section sat2.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Variable RP : roomp.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
Hypothesis HMMAX : 2 ^ 29 < MMAX <= 2 ^ 30.
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Variable CTX_R : list (list Z).
Hypothesis ARE : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_lp_realloc : In [BASE + AF_fr_list_push + 0xc0] CTX_R.
Variable CTX_M : list (list Z).
Hypothesis AMA : amalloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_M.
Hypothesis HCTX_lp_malloc : In [BASE + AF_fr_list_push + 0xe4] CTX_M.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Theorem pb_list_push_g_xR_sat :
  lp_spec_g_xR B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) MT RP MMAX (BASE + AF_fr_list_push).
Proof.
apply lp_spec_g_xR_of_x; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) |].
eapply W_list_push.pb_list_push_g_x; eassumption.
Qed.
End sat2.
