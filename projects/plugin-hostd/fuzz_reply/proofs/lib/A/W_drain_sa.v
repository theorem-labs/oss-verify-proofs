(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment TOP of the ASan walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan 0x82d98 .. 0x82e50 / 0x82f44), against the frozen segment interface
   lib/A/W_relay_instance_gone_cx.v (rig_top_stmt).  The Section-hypothesis block is that file's (commit
   92dac370558), verbatim.
   Layout: the tracks' pure trace lemmas, then the generic Section: its hypotheses, the statements of the lemma
   tracks, and their proofs (drain's
   model and budget, drain's live bytes, the relay representation across drain, GLIVE, GIN / GOUT at the key loop's
   start, the snprintf / strlen calls), then the walk itself: top_p1 (0x82d98 -> drain -> 0x82dd0), top_p2
   (0x82dd0 -> snprintf, strlen, the nheld test -> RGI / RGE) and rig_top_proof.
   C3 (475b8a2b569, the peak form): drain's room is the peak of its trace, a prefix of the remaining trace (top_room);
   drain's live bytes are bounded in the NET form, blocks_bytes S' <= blocks_bytes S + tr_net (dr_tr ..) (dr_bytes:
   the potential td_pot now weighs the pending texts too, which drain frees as it reads them), and tb_core carries
   gbud's peak room across the drain step with tr_peak_app.
   ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record); the RIG_x round): over any allocator relation
   ARx with its laws and the room record RP, at W_relay_instance_gone_cx.v's generic Section c (its list copied
   verbatim).  The statements of the lemma tracks now sit inside that Section, after its hypotheses.  Every journal is
   ajournal_gx_x with its head sets; the laws are AR_laws_x's.  THE ROOM at the drain call: gbud's room over the
   remaining trace grest i splits at the drain (tr_cost MT_rk is additive and nonnegative), so drain gets
   rp_RM RP S (Z.to_nat (dr_cost MT_rk ..) + dr_kr ..) with dr_kr the rest's MT_rk count plus gxkr, and its post's
   rp_RM RP S' dr_kr is gbud's room after the drain (top_room / top_budget).  THE COUNTS: drain's count premise dr_pk is
   within gbud's (tr_peakP of a prefix), and after the drain the live counts move by exactly tr_netP of drain's trace
   (stmt_dr_cnt, RR's lib/A/W_rr_m_dcnt.v rmc_dr_cnt), which tr_peakP_app turns into gbud's count bound over the rest
   (tb_core).  The fake frame is only 32-aligned in a generic state (alx_frames): ts_ra, ts_hull and the shadow seat
   tp_seat2 read that alignment (F's shadow address is 4-aligned). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_rig_top.v, with its module paths and module names changed; 6 of its 28 lines of code are new or changed and 5517 lines of the source are left out. *)
(* The caller-side corollary for dr_spec's `SA mod 8 = 0` premise (W_contract.v, image B's drain checks the entry
   pointer's alignment at 0x832b4 / 0x832b8): a slot of the table block is 8-aligned because AR places every live block
   16-aligned (al_blocks).  Ported verbatim from a Theorem Labs lane's dr_sa_align_slot (lib/B/W_drain_cx.v:458 on
   a working branch); callers of drain (relay_event, relay_remove, relay_instance_gone, the entry) cite it
   with SA = G + AENT * i. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0s YP09 YP0b YP0d YI00 YC5d YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_contract.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma dr_sa_align_slot : forall ly S W mem md (G : Z) (i : nat),
AR SEGS B ly S W mem md -> In (G, ATABLE) (ablocks B ly S) -> (G + AENT * Z.of_nat i) mod 8 = 0.
Proof.
intros ly S W mem md G i HAR Hin.
destruct (al_blocks SEGS B LAWS ly S W mem md G ATABLE HAR Hin) as (H16 & _).
apply Z.mod_divide in H16; [|lia]. destruct H16 as (k & ->).
unfold AENT. apply Z.mod_divide; [lia|]. exists (2 * k + 7 * Z.of_nat i). lia.
Qed.

End c.
End b.
End a.
