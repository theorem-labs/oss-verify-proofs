(* Satisfiability witnesses for lib/B/YD1w_cf.v's Section hypotheses on the non-primary room NP, at image B's real
   instance (VERIFY 2026-10-29 21:38Z rule (1); a Theorem Labs lane 22:32Z: A2 owes them for both images).
   The real NP is the cf instance's room_live_cf (Reusable/YGcfRoomLive.v, a Theorem Labs lane; the same instance A's top uses,
   lib/A/ReplyTFIBcf.v section rl), and B's CfParams is lib/A/CfParamsReply.v CfParams_reply (the one record of both
   images, the record B top_x's ARX names), whose
   reply_rl_param_ok discharges room_live_cf's one parameter premise rl_param_ok.  So the three laws hold at B's
   instance with no premise left: NP_LIVE = 3 is room_live_cf_step_gen's live-set bound, and the tail law's
   ROOM_cf_k S 2 is room_live_room_k (RK_realloc = 2).  The proofs are A's np_init_rl / np_step_rl / np_tail_rl
   (lib/A/ReplyTFIBcf.v, cfdriver 46f1762ad5a) at CfParams_reply.
   MT_PRE (lib/B/YD1mcf.v): fuzz_reply's real meter is ameter_triv on both images, so its witness is the trivial one,
   and that IS the real instance, not a stand-in: W8Add withdrew the live-state meter (relay.c:106 grows the held table
   by one entry per begin, so no XM_LIB can bound it; STATUS.md:278-282 (sha256 975db8402b4c; internal record), METER-FINDING.txt (sha256 e56f281c60fb; internal record)), and
   both tops instantiate ameter_triv (lib/A/ReplyATop.v:95 on cfdriver 46f1762ad5a, lib/B/ReplyTFIBBParts.v:60);
   a Theorem Labs lane ruled it a valid witness at 23:23Z. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf YG01cf YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomKeep YGcfRoomLive.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB YD1w_cf YD1mcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
(* the meter Record as the B cut / cut_x and YD1w_cf take it (Reusable YC5d; ameter_triv in Reusable YCbp) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
Import ListNotations.
Open Scope Z_scope.

Lemma np_init_wit_B : iface_room_np_init (@room_live_cf CfParams_reply).
Proof. exact (@room_live_cf_init_gen CfParams_reply reply_rl_param_ok). Qed.

Lemma np_step_wit_B : iface_room_np_step (ci := CfImg_B) (cp := CfParams_reply) (@room_live_cf CfParams_reply).
Proof.
split.
- intros U S n tr trc p S' HW HQ HN HL HP.
  exact (room_live_cf_step_gen (ci := CfImg_B) (cp := CfParams_reply) reply_rl_param_ok U S S' HW HQ HN HL
           (or_introl (ex_intro _ n (ex_intro _ tr (ex_intro _ trc (ex_intro _ p HP)))))).
- intros U S p tr trc S' HW HQ HN HL HP.
  exact (room_live_cf_step_gen (ci := CfImg_B) (cp := CfParams_reply) reply_rl_param_ok U S S' HW HQ HN HL
           (or_intror (ex_intro _ p (ex_intro _ tr (ex_intro _ trc HP))))).
Qed.

Lemma np_tail_wit_B : iface_room_np_tail (cp := CfParams_reply) (@room_live_cf CfParams_reply).
Proof. intros S H. exact (@room_live_room_k CfParams_reply S H). Qed.

(* MT_PRE at the real meter ameter_triv, for every symbol record, NP and per-call budget *)
Lemma mt_pre_wit_B : forall (B : asyms) (NP : astate -> Prop) (XM_LIB : Z -> Z) (S : astate) (n : Z),
  Wf_cf (cp := CfParams_reply) (as_universe B) S -> qtight S -> blocks_bytes S <= DRV_LIVE -> NP S -> 0 <= n < 2 ^ 26 ->
  mo_ok ameter_triv S (XM_LIB n).
Proof. intros. exact I. Qed.

Print Assumptions np_init_wit_B.
Print Assumptions np_step_wit_B.
Print Assumptions np_tail_wit_B.
Print Assumptions mt_pre_wit_B.
