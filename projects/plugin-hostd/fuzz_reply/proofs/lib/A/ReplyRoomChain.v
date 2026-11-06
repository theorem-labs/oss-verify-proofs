(* The long-input room chain (Reusable/YGcfRoomChain.v, ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (g)2) at the room round's rule texts
   and at fuzz_reply's instance (image A):
   - chain_cnt_ok: at every state of the chain, the allocator rules' count premise cnt_ok RP over the live blocks
     (W_journal_x.v), for ANY count record RP whose bounds leave one unit of margin over rest's counts.  It is stated
     for every roomp, so a Theorem Labs lane's cf instance (rl_sec_ok / rl_b24_ok / rl_prim_ok, count_block_iff; not yet in this
     tree) is covered once its bounds meet the margin hypotheses.  With chain_inv's room_live_cf (the cf instance's
     RM) it is the rules' room and count premise at every state of the chain.
   - reply_chain_bounds: the ruled bounds Lsec = 1,024 and L24 = 2 ^ 15 meet room_live_call_keep's arithmetic at
     CfParams_reply (cf_sec_live_max = 8,192), so chain_inv applies at fuzz_reply's instance with no premise left
     beyond the start state and the per-call facts the walk's realloc rule gives. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK11 YM05 YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0d YGcfNames YGcfSecBound.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomLive YGcfRoomChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
Import ListNotations.
Local Open Scope Z_scope.

(* the kit's live count over ablocks is the chain's count over the blocks: ablocks keeps each block's request *)
Lemma acnt_ablocks : forall P B ly S, acnt P (ablocks B ly S) = bcnt P (blocks S).
Proof. intros P B ly S. unfold acnt, bcnt, ablocks. rewrite map_map. reflexivity. Qed.

Section i.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : YG0f.asyms.
Variables Lsec L24 : Z.
Hypothesis HLsec : Lsec + QSEC_MAX + 3 < cf_sec_live_max.
Hypothesis HL24 : kBatchBytes * (L24 + 1 + N24Q + 1) + 4 * kUserMapSize <= kFreeArrayOffset.
Variable N : nat.
Variable S : nat -> astate.
Variable h : nat -> sptr * Z.
Variable rest : list (sptr * Z).
Hypothesis S0_shape : Permutation (blocks (S 0%nat)) (rest ++ [h 0%nat]).
Hypothesis S0_room : room_live_cf (S 0%nat).
Hypothesis S0_sec : Z.of_nat (bcnt rl_sec_req rest) + 1 <= Lsec.
Hypothesis S0_24 : Z.of_nat (bcnt (PresetRoom.in_cls kBatchClass) rest) + 1 <= L24.
Hypothesis STEP : forall k, (k < N)%nat -> chain_step B S h k.

(* the rules' count premise at every state of the chain, for any count record with one unit of margin over rest *)
Theorem chain_cnt_ok : forall (RP : roomp) ly k, (k <= N)%nat ->
  (bcnt (rp_Psec RP) rest + 1 <= rp_Lsec RP)%nat ->
  (bcnt (rp_P24 RP) rest + 1 <= rp_L24 RP)%nat ->
  (forall c, 1 <= c <= 30 -> (bcnt (rp_Pcls RP c) rest + 1 <= rp_LPRIM RP c)%nat) ->
  cnt_ok RP (ablocks B ly (S k)).
Proof.
  intros RP ly k Hk H1 H2 H3. unfold cnt_ok, cnt_ok_pk. rewrite !acnt_ablocks.
  pose proof (chain_bcnt B Lsec L24 HLsec HL24 N S h rest S0_shape S0_room S0_sec S0_24 STEP) as HB.
  split; [pose proof (HB k (rp_Psec RP) Hk); lia|].
  split; [pose proof (HB k (rp_P24 RP) Hk); lia|].
  intros c Hc. rewrite acnt_ablocks. cbv beta. pose proof (HB k (rp_Pcls RP c) Hk). specialize (H3 c Hc). lia.
Qed.

(* the rules' room premise RM at the cf instance (RM := fun S _ => room_live_cf S) and the count premise, at every
   state of the chain *)
Corollary chain_room_cnt_ok : forall (RP : roomp) ly k, (k <= N)%nat ->
  (bcnt (rp_Psec RP) rest + 1 <= rp_Lsec RP)%nat ->
  (bcnt (rp_P24 RP) rest + 1 <= rp_L24 RP)%nat ->
  (forall c, 1 <= c <= 30 -> (bcnt (rp_Pcls RP c) rest + 1 <= rp_LPRIM RP c)%nat) ->
  room_live_cf (S k) /\ cnt_ok RP (ablocks B ly (S k)).
Proof.
  intros RP ly k Hk H1 H2 H3. split.
  - exact (proj1 (chain_inv B Lsec L24 HLsec HL24 N S h rest S0_shape S0_room S0_sec S0_24 STEP k Hk)).
  - exact (chain_cnt_ok RP ly k Hk H1 H2 H3).
Qed.
End i.

(* fuzz_reply's instance: the ruled bounds (a Theorem Labs lane 00:28Z: Lsec = 1,024, L24 = 2 ^ 15) at CfParams_reply *)
Lemma reply_chain_bounds :
  1024 + QSEC_MAX + 3 < @cf_sec_live_max CfParams_reply /\
  kBatchBytes * (2 ^ 15 + 1 + N24Q + 1) + 4 * kUserMapSize <= kFreeArrayOffset.
Proof. split; [cbn; unfold QSEC_MAX, kQuarantineMax, kQuarantineCacheMax|]; apply Z.leb_le || apply Z.ltb_lt;
  vm_compute; reflexivity.
Qed.

Print Assumptions chain_cnt_ok.
Print Assumptions chain_room_cnt_ok.
Print Assumptions reply_chain_bounds.
