(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* IMAGE B TWIN (row G-BCF): lib/A/CfRBridgePrim.v at c6394a5bd7e (sha256 47aeb725f949; internal record), under lib/B so the B tree is
   self-contained (as lib/B/CfParamsReplyB.v). One change: the count names come from lib/B/ReplyCnt (kit cand13's twin
   of lib/A/ReplyCnt.v), the names B's room record reads. CfParams_reply stays lib/A/CfParamsReply's, the one record
   of both images that B's top_x uses (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:12-13, :155). No image address. *)
(* Theorem Labs, 2026-10: plugin-hostd/fuzz_reply.asan-ubsan, the cf allocator bridge (new file), part 2: the
   PRIMARY-CLASS ROOM of the `_x` rules' count premise, rl_prim_ok (design:
   REPLY-CLASS-PEAK.md (sha256 17339ef5a8b7; internal record) section 5), and the one fact it buys: a malloc_cf whose every kernel answer is granted
   returns a block, never NULL, at a state with Wf_cf, qtight and rl_prim_ok.
   - ccnt_c c S: the live requests of class c at S (PresetRoom.room_ok's argument, R/Spec/PresetRoom.v:156-157, at
     rs_live (room_of_cf S) = map snd (blocks S), Reusable/YGcfRoom.v:50-51);
   - rl_prim_ok S: every primary class c (1 <= c <= 30) holds at most RL_PRIM c live requests, RL_PRIM :=
     ReplyCnt.RL_PRIM (2 ^ 31 / PresetRoom.size_of_class c; the one definition, as acnt);
   - rl_prim_room: the 30 closed facts room_ok c (RL_PRIM c), checked by computation as ONE boolean equation (hazard
     #50: the term is evaluated by `eval vm_compute` and replaced, never a vm_compute on an open goal);
   - malloc_cf_granted_not_null: the chain rl_of_acall_pre_cf's ingredients (Wf_cf, qtight) -> a granted path ->
     malloc_cf_null_full (Reusable/YGcfRoom.v:1351: a granted NULL is a full class) -> quar_bytes_ok_cf (:600: the
     quarantine side, no program premise) -> PresetRoom.not_full_of_room (:185) at c := chunk_class n; a granted NULL
     is primary (YGcfPath.malloc_cf_null_path_full :519);
   - the count premise of record at Sc, rl_count_ok Lsec L24 S := rl_sec_ok Lsec S /\ ccnt24 S <= L24 /\
     rl_b24_ok (L24 + 1) S /\ rl_prim_ok S (Reusable/YGcfRoomLive.v:1216-1218 and this file), and its SATISFIABILITY
     WITNESSES at reply's CfParams: at the start state init_state (no block), and at a long-input model state with
     72,687 gesture begins held three times (the relayed line, the held entry and the relay's copy: 218,061 live
     requests of 24 bytes, class 2), at top_x's Lsec := 1024 and L24 := 2 ^ 15;
     count_block_iff_cfr: the kit's count block over ablocks (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) 0.3, acnt with top_x's Psec /
   P24 / Pcls / Lsec / L24 / LPRIM) is exactly rl_count_ok 1024 (2 ^ 15) at reply's CfParams (two closed facts by
   computation; the counts agree by ablocks's definition, YG0d.v:420-421);
   plus rl_prim_ok_of_est: rl_prim_ok holds at every state whose class counts are below (REPLY-CLASS-PEAK.md sha256 17339ef5a8b7; internal record) the
     structural worst case est c at the input bound (est_le_RL_PRIM, checked by computation).
   No function is proved (rule 24); no image address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG00cf YG01cf YGcfPath.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfSecBound YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The premise.                                                                *)
Notation RL_PRIM := ReplyCnt.RL_PRIM (only parsing).
Definition ccnt_c (c : Z) (S : astate) : Z := Z.of_nat (PresetRoom.ccnt c (map snd (blocks S))).
Definition rl_prim_ok (S : astate) : Prop := forall c, 1 <= c <= 30 -> ccnt_c c S <= RL_PRIM c.

(* ---------------------------------------------------------------------------- *)
(* 2. The 30 closed room facts.                                                    *)
Definition room_okb (c live : Z) : bool :=
  live + PresetRoom.QT / (PresetRoom.lo c + 8) + (if c =? PresetRoom.K_BATCH_CLASS then PresetRoom.QT / PresetRoom.Q_BATCH_BYTES else 0)
  + PresetRoom.refill c <=? PresetRoom.cap c.

Lemma room_okb_spec : forall c live, room_okb c live = true -> PresetRoom.room_ok c live.
Proof. intros c live H. unfold room_okb in H. unfold PresetRoom.room_ok. apply Z.leb_le in H. exact H. Qed.

Definition prim_classes : list Z := map Z.of_nat (seq 1 30).

Lemma prim_classes_in : forall c, 1 <= c <= 30 -> In c prim_classes.
Proof.
intros c Hc. unfold prim_classes. apply in_map_iff. exists (Z.to_nat c). split; [lia|].
apply in_seq. lia.
Qed.

Lemma rl_prim_roomb : forallb (fun c => room_okb c (RL_PRIM c)) prim_classes = true.
Proof.
let x' := eval vm_compute in (forallb (fun c => room_okb c (RL_PRIM c)) prim_classes) in
replace (forallb (fun c => room_okb c (RL_PRIM c)) prim_classes) with x' by (vm_compute; reflexivity).
reflexivity.
Qed.

Theorem rl_prim_room : forall c, 1 <= c <= 30 -> PresetRoom.room_ok c (RL_PRIM c).
Proof.
intros c Hc. apply room_okb_spec.
exact (proj1 (forallb_forall _ _) rl_prim_roomb c (prim_classes_in c Hc)).
Qed.

Lemma room_ok_mono : forall c live live', live' <= live -> PresetRoom.room_ok c live -> PresetRoom.room_ok c live'.
Proof. intros c live live' Hle H. unfold PresetRoom.room_ok in *. lia. Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. A granted malloc_cf at rl_prim_ok returns a block.                           *)

(* rpost's flag on a path is the path's last flag (YG0d.v:165). *)
Lemma rpost_apath_flag {A} (t : itree astate A) : forall ns (P : bool -> A -> Prop) tr a,
  rpost ns t P -> apath t tr a -> P (last_flag ns tr) a.
Proof.
induction t as [a' | q snap k IH | pc | f]; cbn; intros ns P tr a H Hy.
- destruct tr; [subst; exact H | destruct Hy].
- destruct tr as [|[q' z] tr']; [destruct Hy|]. destruct Hy as (-> & Hz & Hy). cbn [last_flag].
  exact (IH z _ P tr' a (H z Hz) Hy).
- destruct tr; destruct Hy.
- destruct tr; destruct Hy.
Qed.

Section N. Context {ci : CfImg} {cp : CfParams}.

Theorem malloc_cf_granted_not_null : forall U s n tr trc r,
  Wf_cf U s -> qtight s -> rl_prim_ok s ->
  apath (malloc_cf n tr s) trc r -> gflag trc = true -> fst r <> PNull.
Proof.
intros U s n tr trc [p s'] W T PR Hp Hg Hnull. cbn [fst] in Hnull. subst p.
pose proof W as W0. unfold Wf_cf in W0.
destruct (malloc_cf_null_path_full n tr s trc s' (shape_cf_of_WfP_cf _ _ _ _ _ W0) Hp Hg) as (_ & _ & Fp & _ & _).
pose proof (rpost_apath_flag _ true _ _ _ (malloc_cf_null_full U s n tr true W T) Hp) as H. cbv beta in H.
rewrite (last_flag_granted true trc Hg eq_refl) in H.
pose proof (H eq_refl eq_refl) as NF. cbn [fst] in NF.
pose proof (chunk_class_range n Fp) as Hc.
apply (PresetRoom.not_full_of_room (room_of_cf s) n (chunk_class n) (quar_bytes_ok_cf U s W T) NF (cls_primary n Fp)).
exact (room_ok_mono (chunk_class n) (RL_PRIM (chunk_class n)) _ (PR (chunk_class n) Hc) (rl_prim_room (chunk_class n) Hc)).
Qed.

End N.

(* ---------------------------------------------------------------------------- *)
(* 4. The count premise of record and its satisfiability at reply's CfParams.      *)
Definition rl_count_ok {cp : CfParams} (Lsec L24 : Z) (S : astate) : Prop :=
  rl_sec_ok Lsec S /\ ccnt24 S <= L24 /\ rl_b24_ok (L24 + 1) S /\ rl_prim_ok S.

Definition rl_count_okb {cp : CfParams} (Lsec L24 : Z) (S : astate) : bool :=
  (sec_cnt S <=? Lsec) && (Lsec + QSEC_MAX + 3 <? cf_sec_live_max) && (ccnt24 S <=? L24) &&
  (ccnt24 S <=? L24 + 1) && (kBatchBytes * (L24 + 1 + N24Q + 1) + 4 * kUserMapSize <=? kFreeArrayOffset) &&
  forallb (fun c => ccnt_c c S <=? RL_PRIM c) prim_classes.

Lemma rl_count_okb_spec {cp : CfParams} : forall Lsec L24 S, rl_count_okb Lsec L24 S = true -> rl_count_ok Lsec L24 S.
Proof.
intros Lsec L24 S H. unfold rl_count_okb in H.
repeat rewrite andb_true_iff in H. destruct H as (((((H1 & H2) & H3) & H4) & H5) & H6).
apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5.
split; [split; [exact H1 | exact H2]|]. split; [exact H3|].
split; [split; [exact H4 | exact H5]|].
intros c Hc. apply Z.leb_le. exact (proj1 (forallb_forall _ _) H6 c (prim_classes_in c Hc)).
Qed.

(* The kit's count block (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) 0.3: acnt, at top_x's Psec := rl_sec_req, P24 := in_cls kBatchClass,
   Pcls := in_cls, Lsec := 1024, L24 := 2 ^ 15, LPRIM c := Z.to_nat (RL_PRIM c)) is rl_count_ok 1024 (2 ^ 15). *)
(* The kit's count, ONE definition (ReplyCnt.acnt, the one W_journal_x.v's cnt_ok uses). *)
Notation acnt := ReplyCnt.acnt (only parsing).

Lemma map_snd_ablocks : forall B ly S, map snd (ablocks B ly S) = map snd (blocks S).
Proof. intros B ly S. unfold ablocks. rewrite map_map. reflexivity. Qed.

Lemma rl_sec_room_1024 : 1024 + QSEC_MAX + 3 < @cf_sec_live_max CfParams_reply.
Proof.
apply Z.ltb_lt.
let x' := eval vm_compute in (1024 + QSEC_MAX + 3 <? @cf_sec_live_max CfParams_reply) in
replace (1024 + QSEC_MAX + 3 <? @cf_sec_live_max CfParams_reply) with x' by (vm_compute; reflexivity).
reflexivity.
Qed.

Lemma rl_b24_room_2p15 : kBatchBytes * (2 ^ 15 + 1 + N24Q + 1) + 4 * kUserMapSize <= kFreeArrayOffset.
Proof.
apply Z.leb_le.
let x' := eval vm_compute in (kBatchBytes * (2 ^ 15 + 1 + N24Q + 1) + 4 * kUserMapSize <=? kFreeArrayOffset) in
replace (kBatchBytes * (2 ^ 15 + 1 + N24Q + 1) + 4 * kUserMapSize <=? kFreeArrayOffset) with x' by (vm_compute; reflexivity).
reflexivity.
Qed.

Lemma RL_PRIM_nonneg_b : forallb (fun c => 0 <=? RL_PRIM c) prim_classes = true.
Proof.
let x' := eval vm_compute in (forallb (fun c => 0 <=? RL_PRIM c) prim_classes) in
replace (forallb (fun c => 0 <=? RL_PRIM c) prim_classes) with x' by (vm_compute; reflexivity).
reflexivity.
Qed.

Lemma RL_PRIM_nonneg : forall c, 1 <= c <= 30 -> 0 <= RL_PRIM c.
Proof.
intros c Hc. apply Z.leb_le. exact (proj1 (forallb_forall _ _) RL_PRIM_nonneg_b c (prim_classes_in c Hc)).
Qed.

Theorem count_block_iff_cfr : forall B ly S,
  ((acnt rl_sec_req (ablocks B ly S) <= 1024)%nat /\
   (acnt (PresetRoom.in_cls kBatchClass) (ablocks B ly S) <= 2 ^ 15)%nat /\
   (forall c, 1 <= c <= 30 -> (acnt (PresetRoom.in_cls c) (ablocks B ly S) <= Z.to_nat (RL_PRIM c))%nat)) <->
  @rl_count_ok CfParams_reply 1024 (2 ^ 15) S.
Proof.
intros B ly S. unfold acnt. rewrite !map_snd_ablocks.
unfold rl_count_ok, rl_sec_ok, rl_b24_ok, rl_prim_ok, ccnt_c, ccnt24, sec_cnt, PresetRoom.ccnt.
pose proof rl_sec_room_1024 as C1. pose proof rl_b24_room_2p15 as C2.
change (2 ^ 15)%nat with 32768%nat. change (2 ^ 15) with 32768 in *.
split.
- intros (H1 & H2 & H3).
  apply Nat2Z.inj_le in H1. apply Nat2Z.inj_le in H2.
  change (Z.of_nat 1024) with 1024 in H1. change (Z.of_nat 32768) with 32768 in H2.
  split; [split; [exact H1 | exact C1]|]. split; [exact H2|].
  split; [split; [exact (Z.le_trans _ _ _ H2 (Z.le_succ_diag_r 32768)) | exact C2]|].
  intros c Hc. pose proof (H3 c Hc) as H. pose proof (RL_PRIM_nonneg c Hc) as P.
  apply Nat2Z.inj_le in H. rewrite Z2Nat.id in H by exact P. exact H.
- intros ((H1 & _) & H2 & (_ & _) & H3).
  split; [apply Nat2Z.inj_le; exact H1|]. split; [apply Nat2Z.inj_le; exact H2|].
  intros c Hc. pose proof (H3 c Hc) as H. pose proof (RL_PRIM_nonneg c Hc) as P.
  apply Nat2Z.inj_le. rewrite Z2Nat.id by exact P. exact H.
Qed.

(* top_x's figures (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) 0.3: Lsec := 1024, L24 := 2 ^ 15; reply's peak live secondary count is
   514, CfParamsReply.v:14-23). *)
Definition RL_LSEC : Z := 1024.
Definition RL_L24 : Z := 2 ^ 15.

(* The start state. *)
Lemma rl_count_init_b : @rl_count_okb CfParams_reply RL_LSEC RL_L24 init_state = true.
Proof.
let x' := eval vm_compute in (@rl_count_okb CfParams_reply RL_LSEC RL_L24 init_state) in
replace (@rl_count_okb CfParams_reply RL_LSEC RL_L24 init_state) with x' by (vm_compute; reflexivity).
reflexivity.
Qed.

Theorem rl_count_init : @rl_count_ok CfParams_reply RL_LSEC RL_L24 init_state.
Proof. exact (rl_count_okb_spec RL_LSEC RL_L24 init_state rl_count_init_b). Qed.

(* A long-input model state: init_state with 218,061 live 24-byte requests (72,687 gesture begins
   `param_gesture <3-byte key> begin`, 23 bytes and the NUL, each held three times: s->expected, the held list and the
   relay's copy), all in class 2, at distinct 32-byte-apart chunk offsets. A counts witness: reachability is not
   claimed. *)
Definition N_BEGINS : nat := 72687.
Fixpoint begin_chunks (m : nat) (off : Z) : list chunk :=
  match m with O => [] | S m' => mkChunk (PPrim off) 24 CAllocated :: begin_chunks m' (off + 32) end.
Definition long_state : astate := set_chunks (begin_chunks (3 * N_BEGINS) 0) init_state.

Lemma long_state_count : ccnt_c 2 long_state = 218061.
Proof.
let x' := eval vm_compute in (ccnt_c 2 long_state) in
replace (ccnt_c 2 long_state) with x' by (vm_compute; reflexivity).
reflexivity.
Qed.

Lemma rl_count_long_b : @rl_count_okb CfParams_reply RL_LSEC RL_L24 long_state = true.
Proof.
let x' := eval vm_compute in (@rl_count_okb CfParams_reply RL_LSEC RL_L24 long_state) in
replace (@rl_count_okb CfParams_reply RL_LSEC RL_L24 long_state) with x' by (vm_compute; reflexivity).
reflexivity.
Qed.

Theorem rl_count_long : @rl_count_ok CfParams_reply RL_LSEC RL_L24 long_state.
Proof. exact (rl_count_okb_spec RL_LSEC RL_L24 long_state rl_count_long_b). Qed.

(* room_live_cf at both states: it reads st_sec_arr, st_secs and st_regions only (YGcfRoomLive.v:1209-1212, :1235), so
   long_state has init_state's (room_live_cf_init_gen at reply_rl_param_ok). *)
Theorem room_live_init_reply : @room_live_cf CfParams_reply init_state.
Proof. exact (@room_live_cf_init_gen CfParams_reply reply_rl_param_ok). Qed.

Theorem room_live_long : @room_live_cf CfParams_reply long_state.
Proof. exact room_live_init_reply. Qed.

(* rl_prim_ok at the structural worst case of every class at the input bound (REPLY-CLASS-PEAK.md (sha256 17339ef5a8b7; internal record) section 4:
   est 1 := 33,553,920 + 17; est c := 3 * (33,553,920 / lo c) + 512 + 16 for c >= 2). *)
Definition est (c : Z) : Z := if c =? 1 then 33553920 + 17 else 3 * (33553920 / PresetRoom.lo c) + 512 + 16.

Lemma est_le_RL_PRIM_b : forallb (fun c => est c <=? RL_PRIM c) prim_classes = true.
Proof.
let x' := eval vm_compute in (forallb (fun c => est c <=? RL_PRIM c) prim_classes) in
replace (forallb (fun c => est c <=? RL_PRIM c) prim_classes) with x' by (vm_compute; reflexivity).
reflexivity.
Qed.

Theorem rl_prim_ok_of_est : forall S, (forall c, 1 <= c <= 30 -> ccnt_c c S <= est c) -> rl_prim_ok S.
Proof.
intros S H c Hc. pose proof (H c Hc) as H1.
pose proof (proj1 (forallb_forall _ _) est_le_RL_PRIM_b c (prim_classes_in c Hc)) as H2. cbv beta in H2.
apply Z.leb_le in H2. lia.
Qed.

Print Assumptions rl_prim_room.
Print Assumptions malloc_cf_granted_not_null.
Print Assumptions rl_count_init.
Print Assumptions rl_count_long.
Print Assumptions room_live_long.
Print Assumptions rl_prim_ok_of_est.
Print Assumptions count_block_iff_cfr.
