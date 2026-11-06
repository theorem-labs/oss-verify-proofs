(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_LLVMFuzzerTestOneInput_top_x.v, with its module paths and module names changed; 747 of its 920 lines of code are new or changed and 1054 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
ReplyCnt W_LLVMFuzzerTestOneInput_drain_defs_x W_LLVMFuzzerTestOneInput_drain_calls TopxEntry
W_img_x W_gesture_end W_gestures_end_top AsmTopX CfRBridgeRulesB TopX_RT_lock.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3TrPeakCnl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_send_line_x TopX_RT4 W_errno_azs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require RTx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_head_x ReplyLSB ReplyRINVB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx YG01cf YG05cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_frame W_frame_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0tcf YG0dcf YG08cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_op_add W_LLVMFuzzerTestOneInput_pro W_LLVMFuzzerTestOneInput_pro_x W_LLVMFuzzerTestOneInput_latch_x
W_bx_defs W_LLVMFuzzerTestOneInput_exit_x W_bx_inst W_bx_inst_x YCk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_drain_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_small_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_add W_LLVMFuzzerTestOneInput_add_x W_LLVMFuzzerTestOneInput_write W_LLVMFuzzerTestOneInput_write_x
W_list_push.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_remove W_LLVMFuzzerTestOneInput_remove_x W_LLVMFuzzerTestOneInput_arm_event
W_LLVMFuzzerTestOneInput_event_x TopxImageB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_gone_x W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_base_x
W_LLVMFuzzerTestOneInput_gone_inst.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0scf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
ReplyLS3B_inst ReplyB3Base ReplyB3LSCntL ReplyB3LS3 ReplyB3LS3c ReplyB3LS3p ReplyLSBo ReplyLSBArms ReplyLSBoRf ReplyB3LS3o
ReplyB3LS3e ReplyB3LS3Arms ReplyB3LS3w ReplyB3LScap ReplyB3LS3Peak ReplyB3LS3cTopxPost ReplyBLSrm YCfn_cf.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Local Notation G := (G_fr_c TfibB).
Local Notation LSx := (ReplyLS3B_inst.LSI TfibB ReplyLSBo.OUT_MAX4).
Local Notation RINV := ReplyRINVB.fr_RINV.

Local Ltac btlsi_open H := apply ReplyLS3B_inst.lsi_parts in H; destruct H as (HP & H3c & H3 & HO & HE & HC).

Lemma btlsi_lsi_intro : forall (rc : YM05.RunCeil) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop) cx t m ly S,
  ReplyB3LS3p.fr_LS3cp TfibB YCfn_cf.CALL_ROOM_B cx t m ly S -> ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S ->
  ReplyB3LS3e.fr_ENT TfibB cx m ly S -> CAPS cx t m ly S -> LSx CAPS cx t m ly S.
Proof. intros rc CAPS cx t m ly S HP HO HE HC. exact (conj HP (conj HO (conj HE HC))). Qed.

Module BtlsiPro.
Import ReplyLSB ReplyB3Base ReplyB3LS3 ReplyB3LSCntL ReplyB3LS3c.

Local Ltac btlsi_perm_lia :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hc" in pose proof (proj1 (Permutation_count_occ zzdec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ zzdec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  repeat progress (rewrite ?count_occ_app, ?cnt_cons, ?cnt_nil in *); lia.

Fixpoint cls_chk (s : Z) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S f => (1 <=? PresetRoom.class_id s) && (PresetRoom.class_id s <=? 30) && cls_chk (s + 1) f
  end.
Lemma cls_chk_ok : cls_chk 1 65536 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cls_chk_sound : forall f s m, cls_chk s f = true -> s <= m < s + Z.of_nat f ->
  1 <= PresetRoom.class_id m <= 30.
Proof.
  induction f as [|f IH]; intros s m H Hm; [lia|].
  cbn [cls_chk] in H. apply andb_true_iff in H as (H1 & H2). apply andb_true_iff in H1 as (H1 & H3).
  destruct (Z.eq_dec m s) as [->|Hne]; [apply Z.leb_le in H1; apply Z.leb_le in H3; lia|].
  apply (IH (s + 1) m H2). lia.
Qed.
Lemma needed0_ge8 : forall n, 8 <= PresetRoom.needed0 n.
Proof.
  intros n. unfold PresetRoom.needed0, PresetRoom.rounded_size, PresetRoom.rz_size, PresetRoom.rup.
  assert (0 <= Z.shiftl 16 (PresetRoom.rz_log n)) by (rewrite Z.shiftl_nonneg; lia).
  assert (Z.max n 8 <= (Z.max n 8 + 8 - 1) / 8 * 8).
  { pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
    lia. }
  lia.
Qed.
Lemma in_cls_range : forall c n, PresetRoom.in_cls c n = true -> 1 <= c <= 30.
Proof.
  intros c n H. unfold PresetRoom.in_cls, PresetRoom.cls in H.
  destruct (PresetRoom.is_primary n) eqn:Ep; [|discriminate]. apply Z.eqb_eq in H. subst c.
  unfold PresetRoom.is_primary in Ep. apply Z.leb_le in Ep. unfold PresetRoom.K_MAX_SIZE in Ep.
  pose proof (needed0_ge8 n).
  apply (cls_chk_sound 65536 1 _ cls_chk_ok). change (Z.of_nat 65536) with 65536. lia.
Qed.
Lemma cnt_cls_out : forall c l, ~ (1 <= c <= 30) -> cnt_cls c l = 0.
Proof.
  intros c l Hc. unfold cnt_cls, PresetRoom.ccnt.
  induction (map snd l) as [|n r IH]; [reflexivity|]. cbn [List.filter].
  destruct (PresetRoom.in_cls c n) eqn:E; [apply in_cls_range in E; lia | exact IH].
Qed.
Lemma xok_pre : forall (rc : YM05.RunCeil) cx T0 cap out,
  ReplyCnt.xcnt_ok TfibB (c_S cx) (c_ly cx) (input_blks cx) T0 cap out -> xcnt_pre TfibB cx T0 cap out.
Proof.
  intros rc cx T0 cap out (X1 & X2). split; [exact X1|].
  intros c. destruct (Z_le_dec 1 c) as [L1|L1]; [destruct (Z_le_dec c 30) as [L2|L2]|].
  - exact (X2 c (conj L1 L2)).
  - rewrite (cnt_cls_out c (ablocks TfibB (c_ly cx) (c_S cx)) ltac:(lia)).
    pose proof (cnt_cls_nonneg c (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out)).
    unfold CLS0. lia.
  - rewrite (cnt_cls_out c (ablocks TfibB (c_ly cx) (c_S cx)) ltac:(lia)).
    pose proof (cnt_cls_nonneg c (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out)).
    unfold CLS0. lia.
Qed.
Lemma aout_cap_nonneg : forall (rc : YM05.RunCeil) RG ly S W mem c O mx no cap out,
  aout_at TfibB RG ly S W mem c O mx no cap out -> 0 <= cap.
Proof.
  intros rc RG ly S W mem c O mx no cap out H. unfold aout_at in H.
  repeat match type of H with _ /\ ?R => destruct H as [_ H] end.
  destruct H as [(Hc & _) | (Hc & _)]; lia.
Qed.
Lemma pro_LS3 : forall (rc : YM05.RunCeil) cx q T' pj c O cap out ly S,
  0 <= c_n cx < 2 ^ 26 -> blocks_bytes (c_S cx) + YCfn_cf.CALL_ROOM_B <= LIVE_MAX ->
  (exists T0 rest0, Permutation (ablocks TfibB (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ((T0 = 0 /\ Permutation (ablocks TfibB ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks TfibB ly S) ((q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))))) ->
  fr_LS3 TfibB YCfn_cf.CALL_ROOM_B cx 0 (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) ly S.
Proof.
  intros rc cx q T' pj c O cap out ly S Hc Hlive (T0 & rest0 & HE0 & Hcase).
  assert (Hmb : model_blks (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) =
    (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out) by reflexivity.
  assert (Ep : pend_bytes (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Eh : held_bytes (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Ev : vslack (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Ec : ECRED (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) = E_ENT + K0) by reflexivity.
  assert (En : npend (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Eo : nopen (lm_hs (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out)) = 1) by reflexivity.
  assert (Ek : kk cx (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) = 0)
    by (unfold kk; cbn [W_LLVMFuzzerTestOneInput_pro.pro_m lm_k]; lia).
  assert (Eb0 : blocks_bytes (c_S cx) = bsum (ablocks TfibB (c_ly cx) (c_S cx))) by apply blocks_bytes_bsum.
  destruct Hcase as [(HT0 & HP) | (HT0 & HT' & HP)].
  - subst T0. rewrite Z.eqb_refl in HE0. cbv beta iota in HE0.
    exists rest0, (bsum (aout_blks cap out)).
    split; [rewrite Hmb; btlsi_perm_lia |].
    split; [rewrite Eb0, (bsum_perm _ _ HE0), !bsum_app, ?bsum_nil; lia |].
    split; [exact Hlive | split; [exact Hc | split; [reflexivity | split]]].
    + rewrite En, Ek. lia.
    + unfold PHI3, PHI. rewrite Hmb, Ep, Eh, Ev, Ec, Eo, Ek. rewrite !bsum_cons. cbn [snd].
      unfold W_OPEN, MB_K, MB_C, W_P, W_H, APARTIAL, ATABLE, E_ENT, K0. lia.
  - subst T'. rewrite (proj2 (Z.eqb_neq _ _) HT0) in HE0. cbv beta iota in HE0.
    exists rest0, (ATABLE + bsum (aout_blks cap out)).
    split; [rewrite Hmb; btlsi_perm_lia |].
    split; [rewrite Eb0, (bsum_perm _ _ HE0), !bsum_app, bsum_cons, ?bsum_nil; cbn [snd]; lia |].
    split; [exact Hlive | split; [exact Hc | split; [reflexivity | split]]].
    + rewrite En, Ek. lia.
    + unfold PHI3, PHI. rewrite Hmb, Ep, Eh, Ev, Ec, Eo, Ek. rewrite !bsum_cons. cbn [snd].
      unfold W_OPEN, MB_K, MB_C, W_P, W_H, APARTIAL, ATABLE, E_ENT, K0. lia.
Qed.
Lemma pro_CNT : forall (rc : YM05.RunCeil) cx q T' pj c O cap out ly S T0 rest0,
  Permutation (ablocks TfibB (c_ly cx) (c_S cx))
    (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) ->
  xcnt_pre TfibB cx T0 cap out ->
  ((T0 = 0 /\ Permutation (ablocks TfibB ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))) \/
   (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks TfibB ly S) ((q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx)))) ->
  fr_CNT TfibB cx 0 (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) ly S.
Proof.
  intros rc cx q T' pj c O cap out ly S T0 rest0 HE0 (X1 & X2) Hcase.
  assert (Hmb : model_blks (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) =
    (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out) by reflexivity.
  assert (En : npend (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (HP : Permutation (ablocks TfibB ly S)
    (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) ++ rest0)).
  { rewrite Hmb. destruct Hcase as [(HT0 & HP) | (HT0 & HT' & HP)].
    - subst T0. rewrite Z.eqb_refl in HE0. cbv beta iota in HE0. btlsi_perm_lia.
    - subst T'. rewrite (proj2 (Z.eqb_neq _ _) HT0) in HE0. cbv beta iota in HE0. btlsi_perm_lia. }
  unfold fr_CNT. rewrite (cnt_sec_perm _ _ HP), !cnt_sec_app.
  rewrite (cnt_sec_perm _ _ HE0), !cnt_sec_app in X1.
  split; [lia | split; [| rewrite En; lia]].
  intros c0. specialize (X2 c0). rewrite (cnt_cls_perm _ _ _ HP), !cnt_cls_app.
  rewrite (cnt_cls_perm _ _ _ HE0), !cnt_cls_app in X2. lia.
Qed.
End BtlsiPro.

Lemma btlsi_gse_room : forall MX xs bb c mx no cap,
  ReplyLSBArms.gse_room_c3 MX bb c mx no cap xs -> gse_room MX bb c mx no cap xs.
Proof.
  intros MX xs. induction xs as [|x xs IH]; intros bb c mx no cap H; [exact I|].
  cbn [ReplyLSBArms.gse_room_c3 gse_room] in *. destruct H as [H1 H2].
  split; [exact H1 | exact (IH _ _ _ _ _ H2)].
Qed.
Lemma btlsi_rf_room_p : forall MX es bb c O mx no cap,
  ReplyLSBoRf.lx_rf_room_p MX bb c O mx no cap es -> W_bx_defs.lx_rf_room MX bb c O mx no cap es.
Proof.
  intros MX es. induction es as [|e es IH]; intros bb c O mx no cap H; [exact I|].
  cbn [ReplyLSBoRf.lx_rf_room_p W_bx_defs.lx_rf_room] in *. destruct H as [H1 H2].
  split; [exact (btlsi_gse_room MX _ _ _ _ _ _ H1) | exact (IH _ _ _ _ _ _ H2)].
Qed.

Lemma btlsi_LS_head_nout : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
  (CAPS_head_nout :
    forall cx t m ly S,
    ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S -> CAPS cx t m ly S -> CAPS cx t (W_LLVMFuzzerTestOneInput_head.lm_clear_O m) ly S),
  forall cx t m ly S, LSx CAPS cx t m ly S -> LSx CAPS cx t (W_LLVMFuzzerTestOneInput_head.lm_clear_O m) ly S.
Proof.
  intros rc fx CAPS CAPS_head_nout cx t m ly S H. btlsi_open H. apply btlsi_lsi_intro.
  - eapply ReplyB3LS3p.fr_LS3cp_head_nout; eassumption.
  - eapply ReplyLSBo.fr_OUT_head_nout_b; eassumption.
  - eapply ReplyB3LS3e.fr_ENT_head_nout; eassumption.
  - eapply CAPS_head_nout; eassumption.
Qed.

Lemma btlsi_LS_head_skip : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
  (CAPS_head_skip :
    forall cx t m ly S,
    ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S -> CAPS cx t m ly S -> CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_head.lm_set_k m (W_LLVMFuzzerTestOneInput_head.hd_k' cx m)) ly S),
  forall cx t m ly S, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (W_LLVMFuzzerTestOneInput_head.hd_kb cx m) = None -> LSx CAPS cx t m ly S -> LSx CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_head.lm_set_k m (W_LLVMFuzzerTestOneInput_head.hd_k' cx m)) ly S.
Proof.
  intros rc fx CAPS CAPS_head_skip cx t m ly S Ht Hk HO0 Hpk H1 Hn H. btlsi_open H. apply btlsi_lsi_intro.
  - eapply ReplyB3LS3p.fr_LS3cp_head_skip; eassumption.
  - eapply ReplyLSBo.fr_OUT_head_skip_b; eassumption.
  - eapply ReplyB3LS3e.fr_ENT_head_skip; eassumption.
  - eapply CAPS_head_skip; eassumption.
Qed.

Lemma btlsi_LS_pro : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop) (MT : ameter_ops) (XM_LIB : Z -> Z) (RLO RHI : Z) (LIBROOM NP : astate -> Prop) (ARX : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
  (CAPS_pro :
    forall (XM_LIB0 : Z -> Z) (RLO0 RHI0 : Z) (LIBROOM0 NP0 : astate -> Prop) (Gc : list (Z * Z))
      (ARX0 : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop),
    forall cx Hp q T' pj c O cap out (S2 : astate) pos ly S,
    lf_base_x TfibB MT XM_LIB0 RLO0 RHI0 YCfn_cf.fr_live_pre_b LIBROOM0 NP0 Gc ARX0 cx Hp ->
    (exists c0 mx0, aout_at TfibB fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
    ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
    ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
    st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 ->
    mo_le MT S2 S (W_op_add.oa_cost MT) ->
    (exists T0 rest0, Permutation (ablocks TfibB (c_ly cx) (c_S cx))
         (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
       ReplyCnt.xcnt_ok TfibB (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
       fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
       ((T0 = 0 /\ Permutation (ablocks TfibB ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))) \/
        (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks TfibB ly S) ((q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))))) ->
    CAPS cx 0 (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) ly S),
  forall cx Hp q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base_x TfibB MT XM_LIB RLO RHI YCfn_cf.fr_live_pre_b LIBROOM NP G ARX cx Hp ->
  (exists c0 mx0, aout_at TfibB fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 ->
  mo_le MT S2 S (W_op_add.oa_cost MT) ->
  (exists T0 rest0, Permutation (ablocks TfibB (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ReplyCnt.xcnt_ok TfibB (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks TfibB ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks TfibB ly S) ((q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))))) ->
  LSx CAPS cx 0 (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) ly S.
Proof.
  intros rc fx CAPS MT XM_LIB RLO RHI LIBROOM NP ARX CAPS_pro cx Hp q T' pj c O cap out S2 pos ly S HB Hout Hc1 Hc2 Hc3
    Hc4 Hb2 Hf2 Hn2 Hbb2 Hm0 Hmo HX.
  pose proof HX as (T0 & rest0 & HE0 & Hx & HFH0 & Hcase).
  pose proof HB as (_ & Hpre). destruct Hpre as (_ & _ & _ & _ & Hd & _ & _ & _ & Hlive & _).
  assert (Hc : 0 <= c_n cx < 2 ^ 26) by (destruct Hd as [(Hd & _) | (Hd & _)]; lia).
  pose proof Hout as (c0 & mx0 & Hout0). apply BtlsiPro.aout_cap_nonneg in Hout0.
  assert (HOM0 : 0 <= ReplyLSBo.OUT_MAX4) by (unfold ReplyLSBo.OUT_MAX4; lia).
  apply btlsi_lsi_intro.
  - split; [split|].
    + exact (BtlsiPro.pro_LS3 rc cx q T' pj c O cap out ly S Hc Hlive (ex_intro _ T0 (ex_intro _ rest0 (conj HE0 Hcase)))).
    + exact (BtlsiPro.pro_CNT rc cx q T' pj c O cap out ly S T0 rest0 HE0 (BtlsiPro.xok_pre rc cx T0 cap out Hx) Hcase).
    + intros k.
      assert (E1 : ReplyB3LS3p.pt_kc k (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) = 0) by reflexivity.
      assert (E2 : ReplyB3LS3p.pt_mass (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) = 0) by reflexivity.
      rewrite E1, E2, !Z.mul_0_r. lia.
  - exact (ReplyLSBo.fr_OUT_pro_b TfibB ReplyLSBo.OUT_MAX4 cx q T' pj c O cap out ly S Hout0 HOM0
      (ex_intro _ T0 (ex_intro _ rest0 (conj HE0 Hcase)))).
  - exact (ReplyB3LS3e.fr_ENT_pro TfibB cx q T' pj c O cap out ly S T0 rest0 HE0 Hcase HFH0).
  - eapply CAPS_pro; eassumption.
Qed.

Lemma btlsi_LS_rf_room : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  forall cx t m ly S,
  LSx CAPS cx t m ly S -> 0 <= t <= OPS_MAX ->
  W_bx_defs.lx_rf_room CfParamsReply.fr_MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m)
    (lm_es m).
Proof.
  intros rc fx CAPS cx t m ly S H Ht. btlsi_open H.
  apply btlsi_rf_room_p.
  eapply ReplyLSBoRf.LS_rf_room_p_room with (OVER := ReplyB3LS3.LS3_OVER) (CR := YCfn_cf.CALL_ROOM_B);
    [apply Z.leb_le; vm_compute; reflexivity | eapply ReplyB3LS3.fr_LS3_room_rel; exact H3 | exact HO | exact Ht].
Qed.

Lemma btlsi_LS_exit_cnt : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  forall cx t m ly3 S3 rest (ly' : alayout) (S' : astate) cap out,
  LSx CAPS cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall p n, In (p, n) (ablocks TfibB ly' S') -> 4096 <= p) ->
  ReplyCnt.xcnt_ok TfibB S' ly' (input_blks cx) (lm_G m) cap out.
Proof.
  intros rc fx CAPS cx t m ly3 S3 rest ly' S' cap out H HP3 HP' HA. btlsi_open H.
  eapply ReplyB3LS3w.LS_exit_cnt_3c; eassumption.
Qed.

Lemma btlsi_LS_exit_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
  (CAPS_cap :
    forall cx t m ly S, CAPS cx t m ly S -> ReplyB3LScap.fr_CAP cx t m ly S),
  forall cx t m ly S,
  LSx CAPS cx t m ly S -> RINV cx t m -> 0 <= t <= OPS_MAX ->
  gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) <= CAPOUT_MAX.
Proof.
  intros rc fx CAPS CAPS_cap cx t m ly S H HRI Ht. btlsi_open H.
  eapply ReplyB3LScap.LS_exit_cap_I; first [exact (conj HP (conj HO (conj HE (CAPS_cap _ _ _ _ _ HC)))) | eassumption].
Qed.

Lemma btlsi_LS_drain_skip : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
  (CAPS_drain_skip :
    forall cx t m ly S,
    ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S -> CAPS cx t m ly S -> CAPS cx (t + 1) (dr_skip m (dr_k' cx m)) ly S),
  forall cx t m ly S,
  LSx CAPS cx t m ly S -> LSx CAPS cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
Proof.
  intros rc fx CAPS CAPS_drain_skip cx t m ly S H. btlsi_open H. apply btlsi_lsi_intro.
  - split; [split|].
    + eapply ReplyB3LS3.fr_LS3_k_only with (t := t) (m := m); try reflexivity; [| exact H3].
      left. cbn [W_LLVMFuzzerTestOneInput_drain_defs.dr_skip lm_k]. unfold W_LLVMFuzzerTestOneInput_drain_defs.dr_k'.
      destruct (lm_k m + 1 <? c_n cx); lia.
    + eapply ReplyB3LS3c.fr_CNT_k_only with (t := t) (m := m); try reflexivity; [lia | exact (proj2 H3c)].
    + eapply ReplyB3LS3p.fr_POT_same with (t := t) (m := m); try reflexivity; [lia | exact (proj2 HP)].
  - eapply ReplyLSBo.fr_OUT_k_only with (t := t) (m := m); try reflexivity; [lia | exact HO].
  - eapply ReplyB3LS3e.fr_ENT_keep with (m := m); [reflexivity | exact HE].
  - eapply CAPS_drain_skip; eassumption.
Qed.

Lemma btlsi_LS_drain_step : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop) (MT : ameter_ops)
  (CAPS_drain_step :
    forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
      si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
    ReplyB3LS3.fr_LS3 TfibB YCfn_cf.CALL_ROOM_B cx t m ly S -> ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S -> CAPS cx t m ly S -> dr_pick cx m si h ->
    (j < length (lm_es m))%nat ->
    (exists rest,
       Permutation (ablocks TfibB ly S)
         (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
       Permutation (ablocks TfibB ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
    hl_recs (hs_pending h1) = [] ->
    E = hs_expected h1 -> H = hs_held h1 ->
    (forall rest, Permutation (ablocks TfibB ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
       Permutation (ablocks TfibB ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
    h'' = set_exp_held h1 E' H' ->
    dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_kh (nth j (lm_es m) dr_e0) ->
    W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpre h -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_hn h -> 0 <= lm_cap m ->
    cap' = (if dr_live (lm_c m) h
            then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                     (nth j (lm_es m) dr_e0) h)
            else lm_cap m) ->
    W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epost (nth j (lm_es m) dr_e0) e' h -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpost h h1 ->
    W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_dpost m j h e' h1 -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_cpost h1 E' H' ->
    0 <= cap' -> 0 <= t < OPS_MAX ->
    CAPS cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'),
  forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  LSx CAPS cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  (exists rest,
     Permutation (ablocks TfibB ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks TfibB ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks TfibB ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_kh (nth j (lm_es m) dr_e0) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpre h -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epost (nth j (lm_es m) dr_e0) e' h -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpost h h1 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_dpost m j h e' h1 -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_cpost h1 E' H' ->
  0 <= t < OPS_MAX ->
  LSx CAPS cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof.
  intros rc fx CAPS MT CAPS_drain_step cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1 h1 E' H' HL Hpick Hj
    M1 M2 HF1 Hp1 EE EH HF2 Eh Hat HRI Hfd Heof Hep Hkh Hhp Hhn Hc0 Hcap' Hepo Hhpo Hdp Hcp Ht.
  assert (Hc' : 0 <= cap').
  { rewrite Hcap'. destruct (dr_live (lm_c m) h); [|exact Hc0].
    unfold dr_fin. pose proof (ReplyLS3B_inst.lsi_drain_fin_ocap (dr_live (lm_c m) h) (lm_mx m)
      (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h Hc0). lia. }
  pose proof (Z.le_refl YCfn_cf.CALL_ROOM_B) as HCR. pose proof (Z.le_refl ReplyLSBo.OUT_MAX4) as HOM.
  btlsi_open HL. apply btlsi_lsi_intro.
  - eapply ReplyB3LS3p.fr_LS3cp_drain_step_p; eassumption.
  - eapply ReplyB3LS3o.fr_OUT_drain_step_p; eassumption.
  - eapply ReplyB3LS3e.fr_ENT_drain_step_p; eassumption.
  - eapply CAPS_drain_step; eassumption.
Qed.

Lemma btlsi_LS_close : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
  (CAPS_close :
    forall cx t m i ly S,
    ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S -> CAPS cx t m ly S -> CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_close cx m i) ly S),
  forall cx t m i ly S, LSx CAPS cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSx CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_close cx m i) ly S.
Proof.
  intros rc fx CAPS CAPS_close cx t m i ly S H Hpk. btlsi_open H. apply btlsi_lsi_intro.
  - eapply ReplyB3LS3p.fr_LS3cp_close; eassumption.
  - eapply ReplyB3LS3o.fr_OUT_close; eassumption.
  - eapply ReplyB3LS3e.fr_ENT_close; eassumption.
  - eapply CAPS_close; eassumption.
Qed.

Lemma btlsi_LS_eintr : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
  (CAPS_eintr :
    forall cx t m i ly S,
    ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S -> CAPS cx t m ly S -> CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_eintr cx m i) ly S),
  forall cx t m i ly S, LSx CAPS cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSx CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_eintr cx m i) ly S.
Proof.
  intros rc fx CAPS CAPS_eintr cx t m i ly S H Hpk. btlsi_open H. apply btlsi_lsi_intro.
  - eapply ReplyB3LS3p.fr_LS3cp_eintr; eassumption.
  - eapply ReplyB3LS3o.fr_OUT_eintr; eassumption.
  - eapply ReplyB3LS3e.fr_ENT_eintr; eassumption.
  - eapply CAPS_eintr; eassumption.
Qed.

Lemma btlsi_LS_sendmax : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
  (CAPS_sendmax :
    forall cx t m u ly S,
    ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S -> CAPS cx t m ly S -> CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_sendmax cx m u) ly S),
  forall cx t m ly S, LSx CAPS cx t m ly S ->
  LSx CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Proof.
  intros rc fx CAPS CAPS_sendmax cx t m ly S H. btlsi_open H. apply btlsi_lsi_intro.
  - eapply ReplyB3LS3p.fr_LS3cp_sendmax; eassumption.
  - eapply ReplyB3LS3o.fr_OUT_sendmax; eassumption.
  - eapply ReplyB3LS3e.fr_ENT_sendmax; eassumption.
  - eapply CAPS_sendmax; eassumption.
Qed.

Lemma btlsi_LS_default : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
  (CAPS_default :
    forall cx t m g ly S,
    ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S -> CAPS cx t m ly S -> CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_default cx m g) ly S),
  forall cx t m ly S, LSx CAPS cx t m ly S -> LSx CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_default cx m (W_LLVMFuzzerTestOneInput_small.sm_dg cx m)) ly S.
Proof.
  intros rc fx CAPS CAPS_default cx t m ly S H. btlsi_open H. apply btlsi_lsi_intro.
  - eapply ReplyB3LS3p.fr_LS3cp_default; eassumption.
  - eapply ReplyB3LS3o.fr_OUT_default; eassumption.
  - eapply ReplyB3LS3e.fr_ENT_default; eassumption.
  - eapply CAPS_default; eassumption.
Qed.

Lemma btlsi_LS_add_open : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop) (MT : ameter_ops)
  (CAPS_add_open :
    forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
    ReplyB3LS3.fr_LS3 TfibB YCfn_cf.CALL_ROOM_B cx t m ly S -> W_op_add.oa_first (W_LLVMFuzzerTestOneInput_add.ad_os (lm_hs m)) = Some i ->
    Permutation (ablocks TfibB ly' S') ((q, APARTIAL) :: ablocks TfibB ly S) ->
    ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S -> CAPS cx t m ly S -> CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_add.ad_open m i q pj ev) ly' S'),
  forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  LSx CAPS cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m -> W_op_add.oa_first (W_LLVMFuzzerTestOneInput_add.ad_os (lm_hs m)) = Some i ->
  mo_le MT S S' (W_op_add.oa_cost MT) -> Permutation (ablocks TfibB ly' S') ((q, APARTIAL) :: ablocks TfibB ly S) ->
  LSx CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_add.ad_open m i q pj ev) ly' S'.
Proof.
  intros rc fx CAPS MT CAPS_add_open cx t m i q pj ev ly S ly' S' H HRI Hat Hf Hmo HPm. btlsi_open H. apply btlsi_lsi_intro.
  - eapply ReplyB3LS3p.fr_LS3cp_add_open; eassumption.
  - eapply ReplyB3LS3o.fr_OUT_add_open; eassumption.
  - eapply ReplyB3LS3e.fr_ENT_add_open; eassumption.
  - eapply CAPS_add_open; eassumption.
Qed.

Lemma btlsi_LS_add_none : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
  (CAPS_add_none :
    forall cx t m ly S,
    ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S -> CAPS cx t m ly S -> CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_add.ad_none m) ly S),
  forall cx t m ly S,
  LSx CAPS cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m -> W_op_add.oa_first (W_LLVMFuzzerTestOneInput_add.ad_os (lm_hs m)) = None ->
  LSx CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_add.ad_none m) ly S.
Proof.
  intros rc fx CAPS CAPS_add_none cx t m ly S H HRI Hat Hf. btlsi_open H. apply btlsi_lsi_intro.
  - eapply ReplyB3LS3p.fr_LS3cp_add_none; eassumption.
  - eapply ReplyB3LS3o.fr_OUT_add_none; eassumption.
  - eapply ReplyB3LS3e.fr_ENT_add_none; eassumption.
  - eapply CAPS_add_none; eassumption.
Qed.

Lemma btlsi_LS_write_skip : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
  (CAPS_write_skip :
    forall cx t m ly S,
    ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S -> CAPS cx t m ly S -> CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_skip m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m)) ly S),
  forall cx t m ly S,
  LSx CAPS cx t m ly S -> LSx CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_skip m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m)) ly S.
Proof.
  intros rc fx CAPS CAPS_write_skip cx t m ly S H. btlsi_open H. apply btlsi_lsi_intro.
  - eapply ReplyB3LS3p.fr_LS3cp_write_skip; eassumption.
  - eapply ReplyB3LS3o.fr_OUT_write_skip; eassumption.
  - eapply ReplyB3LS3e.fr_ENT_write_skip; eassumption.
  - eapply CAPS_write_skip; eassumption.
Qed.

Lemma btlsi_LS_write_push : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop) (MT : ameter_ops)
  (CAPS_write_push :
    forall cx t m si h (l' : hlist) d ly S ly' S' ev,
    ReplyB3LS3.fr_LS3 TfibB YCfn_cf.CALL_ROOM_B cx t m ly S -> W_LLVMFuzzerTestOneInput_write.wr_pick cx m si h -> 0 < W_LLVMFuzzerTestOneInput_write.wr_n cx m ->
    hl_recs l' = hl_recs (hs_pending h) ++ [(d, W_LLVMFuzzerTestOneInput_write.wr_x cx m)] ->
    hl_cap l' = ListRep.grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
    (W_contract.lp_grow (hs_pending h) = false -> HarnessRep.hl_v l' = HarnessRep.hl_v (hs_pending h)) ->
    (forall rest, Permutation (ablocks TfibB ly S)
         ((if W_contract.lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
           then [(HarnessRep.hl_v (hs_pending h), W_rep.AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
       Permutation (ablocks TfibB ly' S')
         ((d, Z.of_nat (length (W_LLVMFuzzerTestOneInput_write.wr_x cx m)) + 1) ::
          (if W_contract.lp_grow (hs_pending h) then [(HarnessRep.hl_v l', W_rep.AREC * hl_cap l')] else []) ++ rest)) ->
    ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S -> CAPS cx t m ly S ->
    CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_push m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m) si (W_LLVMFuzzerTestOneInput_write.set_pending h l') ev) ly' S'),
  forall cx t m si h (l' : hlist) d ev ly S ly' S',
  LSx CAPS cx t m ly S -> W_LLVMFuzzerTestOneInput_write.wr_pick cx m si h -> 0 < W_LLVMFuzzerTestOneInput_write.wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, W_LLVMFuzzerTestOneInput_write.wr_x cx m)] ->
  hl_cap l' = ListRep.grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (W_contract.lp_grow (hs_pending h) = false -> HarnessRep.hl_v l' = HarnessRep.hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks TfibB ly S)
       ((if W_contract.lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(HarnessRep.hl_v (hs_pending h), W_rep.AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks TfibB ly' S')
       ((d, Z.of_nat (length (W_LLVMFuzzerTestOneInput_write.wr_x cx m)) + 1) ::
        (if W_contract.lp_grow (hs_pending h) then [(HarnessRep.hl_v l', W_rep.AREC * hl_cap l')] else []) ++ rest)) ->
  mo_le MT S S' (W_contract.lp_cost MT (hs_pending h) (W_LLVMFuzzerTestOneInput_write.wr_n cx m)) ->
  0 <= t < OPS_MAX ->
  LSx CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_push m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m) si (W_LLVMFuzzerTestOneInput_write.set_pending h l') ev) ly' S'.
Proof.
  intros rc fx CAPS MT CAPS_write_push cx t m si h l' d ev ly S ly' S' H Hpk Hn Hr Hc Hv HPm Hmo Ht. btlsi_open H. apply btlsi_lsi_intro.
  - eapply ReplyB3LS3p.fr_LS3cp_write_push; eassumption.
  - eapply ReplyB3LS3o.fr_OUT_write_push; eassumption.
  - eapply ReplyB3LS3e.fr_ENT_write_push; eassumption.
  - eapply CAPS_write_push; eassumption.
Qed.

Lemma btlsi_LS_rm_step : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop) (MT : ameter_ops)
  (CAPS_rm_step :
    forall cx t m ly0 S0 (ly : alayout) (S : astate)
      si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
    ReplyB3LS3.fr_LS3 TfibB YCfn_cf.CALL_ROOM_B cx t m ly0 S0 -> ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly0 S0 -> CAPS cx t m ly0 S0 ->
    RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
    W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
    W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (CheckRep.set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
    (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks TfibB ly S)
         (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
    (forall b, In b (model_blks m) -> 0 <= snd b) ->
    Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) ->
    ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
    0 <= cap2 -> 0 <= t < OPS_MAX ->
    CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S),
  forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  LSx CAPS cx t m ly0 S0 ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S)
       (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= t < OPS_MAX ->
  LSx CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros rc fx CAPS MT CAPS_rm_step cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 HL Hmo HRI
    Hat Hrr Hcnl Hcshe HF Hpos Hkeys Hpend Ht.
  eapply ReplyBLSrm.lsi_LS_rm_step;
    first [exact HL | eassumption | apply Z.le_refl | exact CAPS_rm_step |
           (intros; eapply CAPS_rm_step; eassumption)].
Qed.

Lemma btlsi_LS_rm_step_f9 : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop) (MT : ameter_ops)
  (CAPS_rm_step :
    forall cx t m ly0 S0 (ly : alayout) (S : astate)
      si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
    ReplyB3LS3.fr_LS3 TfibB YCfn_cf.CALL_ROOM_B cx t m ly0 S0 -> ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly0 S0 -> CAPS cx t m ly0 S0 ->
    RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
    W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
    W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (CheckRep.set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
    (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks TfibB ly S)
         (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
    (forall b, In b (model_blks m) -> 0 <= snd b) ->
    Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) ->
    ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
    0 <= cap2 -> 0 <= t < OPS_MAX ->
    CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S),
  forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  LSx CAPS cx t m ly0 S0 ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S)
       (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= t < OPS_MAX ->
  LSx CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros rc fx CAPS MT CAPS_rm_step cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 HL _.
  exact (btlsi_LS_rm_step rc fx CAPS MT CAPS_rm_step cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 HL).
Qed.

Lemma btlsi_LS_event_step : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop) (MT : ameter_ops)
  (CAPS_event_step :
    forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
    ReplyB3LS3.fr_LS3 TfibB YCfn_cf.CALL_ROOM_B cx t m ly S -> ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S -> CAPS cx t m ly S ->
    W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
    0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
    ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
    (exists rest, Permutation (ablocks TfibB ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
       Permutation (ablocks TfibB ly2 S2)
         (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
    (exists l1 l2, ablocks TfibB ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks TfibB ly3 S3 = l1 ++ l2) ->
    CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_arm_event.ev_step cx m e v out') ly3 S3),
  forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  LSx CAPS cx t m ly S -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks TfibB ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks TfibB ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks TfibB ly3 S3 = l1 ++ l2) ->
  0 <= t < OPS_MAX ->
  LSx CAPS cx (t + 1) (W_LLVMFuzzerTestOneInput_arm_event.ev_step cx m e v out') ly3 S3.
Proof.
  intros rc fx CAPS MT CAPS_event_step cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q H He M1 M2 M3 Hk HO0 Hc0 Hm HRR Hf Ht.
  pose proof ReplyLSBo.bo_OUT_MAX4_ev as Hev.
  btlsi_open H. apply btlsi_lsi_intro.
  - eapply ReplyB3LS3p.fr_LS3cp_event_step_p; eassumption.
  - eapply ReplyLSBo.fr_OUT_event_step_b; eassumption.
  - eapply ReplyB3LS3e.fr_ENT_event_step_p; eassumption.
  - eapply CAPS_event_step; eassumption.
Qed.

Lemma btlsi_LS_head_nout_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall cx t m ly S, LSx ReplyB3LScap.fr_CAP cx t m ly S -> LSx ReplyB3LScap.fr_CAP cx t (W_LLVMFuzzerTestOneInput_head.lm_clear_O m) ly S.
Proof.
  intros rc fx. apply (btlsi_LS_head_nout rc fx ReplyB3LScap.fr_CAP).
  intros; eapply ReplyB3LScap.fr_CAP_head_nout; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_head_skip_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall cx t m ly S, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (W_LLVMFuzzerTestOneInput_head.hd_kb cx m) = None -> LSx ReplyB3LScap.fr_CAP cx t m ly S -> LSx ReplyB3LScap.fr_CAP cx (t + 1) (W_LLVMFuzzerTestOneInput_head.lm_set_k m (W_LLVMFuzzerTestOneInput_head.hd_k' cx m)) ly S.
Proof.
  intros rc fx. apply (btlsi_LS_head_skip rc fx ReplyB3LScap.fr_CAP).
  intros; eapply ReplyB3LScap.fr_CAP_head_skip; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_pro_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (MT : ameter_ops) (XM_LIB : Z -> Z) (RLO RHI : Z) (LIBROOM NP : astate -> Prop) (ARX : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop),
  forall cx Hp q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base_x TfibB MT XM_LIB RLO RHI YCfn_cf.fr_live_pre_b LIBROOM NP G ARX cx Hp ->
  (exists c0 mx0, aout_at TfibB fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 ->
  mo_le MT S2 S (W_op_add.oa_cost MT) ->
  (exists T0 rest0, Permutation (ablocks TfibB (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ReplyCnt.xcnt_ok TfibB (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks TfibB ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks TfibB ly S) ((q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))))) ->
  LSx ReplyB3LScap.fr_CAP cx 0 (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) ly S.
Proof.
  intros rc fx MT XM_LIB RLO RHI LIBROOM NP ARX. apply (btlsi_LS_pro rc fx ReplyB3LScap.fr_CAP MT XM_LIB RLO RHI LIBROOM NP ARX).
  intros; eapply ReplyB3LScap.fr_CAP_pro; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_exit_cap_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall cx t m ly S,
  LSx ReplyB3LScap.fr_CAP cx t m ly S -> RINV cx t m -> 0 <= t <= OPS_MAX ->
  gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) <= CAPOUT_MAX.
Proof.
  intros rc fx. apply (btlsi_LS_exit_cap rc fx ReplyB3LScap.fr_CAP).
  intros cx t m ly S HC. exact HC.
Qed.

Lemma btlsi_LS_drain_skip_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall cx t m ly S,
  LSx ReplyB3LScap.fr_CAP cx t m ly S -> LSx ReplyB3LScap.fr_CAP cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
Proof.
  intros rc fx. apply (btlsi_LS_drain_skip rc fx ReplyB3LScap.fr_CAP).
  intros; eapply ReplyB3LScap.fr_CAP_drain_skip; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_drain_step_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (MT : ameter_ops),
  forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  LSx ReplyB3LScap.fr_CAP cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  (exists rest,
     Permutation (ablocks TfibB ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks TfibB ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks TfibB ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_kh (nth j (lm_es m) dr_e0) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpre h -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epost (nth j (lm_es m) dr_e0) e' h -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpost h h1 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_dpost m j h e' h1 -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_cpost h1 E' H' ->
  0 <= t < OPS_MAX ->
  LSx ReplyB3LScap.fr_CAP cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof.
  intros rc fx MT. apply (btlsi_LS_drain_step rc fx ReplyB3LScap.fr_CAP MT).
  intros; eapply ReplyB3LScap.fr_CAP_drain_step; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_close_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall cx t m i ly S, LSx ReplyB3LScap.fr_CAP cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSx ReplyB3LScap.fr_CAP cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_close cx m i) ly S.
Proof.
  intros rc fx. apply (btlsi_LS_close rc fx ReplyB3LScap.fr_CAP).
  intros; eapply ReplyB3LScap.fr_CAP_close; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_eintr_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall cx t m i ly S, LSx ReplyB3LScap.fr_CAP cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSx ReplyB3LScap.fr_CAP cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_eintr cx m i) ly S.
Proof.
  intros rc fx. apply (btlsi_LS_eintr rc fx ReplyB3LScap.fr_CAP).
  intros; eapply ReplyB3LScap.fr_CAP_eintr; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_sendmax_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall cx t m ly S, LSx ReplyB3LScap.fr_CAP cx t m ly S ->
  LSx ReplyB3LScap.fr_CAP cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Proof.
  intros rc fx. apply (btlsi_LS_sendmax rc fx ReplyB3LScap.fr_CAP).
  intros; eapply ReplyB3LScap.fr_CAP_sendmax; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_default_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall cx t m ly S, LSx ReplyB3LScap.fr_CAP cx t m ly S -> LSx ReplyB3LScap.fr_CAP cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_default cx m (W_LLVMFuzzerTestOneInput_small.sm_dg cx m)) ly S.
Proof.
  intros rc fx. apply (btlsi_LS_default rc fx ReplyB3LScap.fr_CAP).
  intros; eapply ReplyB3LScap.fr_CAP_default; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_add_open_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (MT : ameter_ops),
  forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  LSx ReplyB3LScap.fr_CAP cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m -> W_op_add.oa_first (W_LLVMFuzzerTestOneInput_add.ad_os (lm_hs m)) = Some i ->
  mo_le MT S S' (W_op_add.oa_cost MT) -> Permutation (ablocks TfibB ly' S') ((q, APARTIAL) :: ablocks TfibB ly S) ->
  LSx ReplyB3LScap.fr_CAP cx (t + 1) (W_LLVMFuzzerTestOneInput_add.ad_open m i q pj ev) ly' S'.
Proof.
  intros rc fx MT. apply (btlsi_LS_add_open rc fx ReplyB3LScap.fr_CAP MT).
  intros; eapply ReplyB3LScap.fr_CAP_add_open; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_add_none_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall cx t m ly S,
  LSx ReplyB3LScap.fr_CAP cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m -> W_op_add.oa_first (W_LLVMFuzzerTestOneInput_add.ad_os (lm_hs m)) = None ->
  LSx ReplyB3LScap.fr_CAP cx (t + 1) (W_LLVMFuzzerTestOneInput_add.ad_none m) ly S.
Proof.
  intros rc fx. apply (btlsi_LS_add_none rc fx ReplyB3LScap.fr_CAP).
  intros; eapply ReplyB3LScap.fr_CAP_add_none; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_write_skip_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall cx t m ly S,
  LSx ReplyB3LScap.fr_CAP cx t m ly S -> LSx ReplyB3LScap.fr_CAP cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_skip m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m)) ly S.
Proof.
  intros rc fx. apply (btlsi_LS_write_skip rc fx ReplyB3LScap.fr_CAP).
  intros; eapply ReplyB3LScap.fr_CAP_write_skip; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_write_push_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (MT : ameter_ops),
  forall cx t m si h (l' : hlist) d ev ly S ly' S',
  LSx ReplyB3LScap.fr_CAP cx t m ly S -> W_LLVMFuzzerTestOneInput_write.wr_pick cx m si h -> 0 < W_LLVMFuzzerTestOneInput_write.wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, W_LLVMFuzzerTestOneInput_write.wr_x cx m)] ->
  hl_cap l' = ListRep.grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (W_contract.lp_grow (hs_pending h) = false -> HarnessRep.hl_v l' = HarnessRep.hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks TfibB ly S)
       ((if W_contract.lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(HarnessRep.hl_v (hs_pending h), W_rep.AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks TfibB ly' S')
       ((d, Z.of_nat (length (W_LLVMFuzzerTestOneInput_write.wr_x cx m)) + 1) ::
        (if W_contract.lp_grow (hs_pending h) then [(HarnessRep.hl_v l', W_rep.AREC * hl_cap l')] else []) ++ rest)) ->
  mo_le MT S S' (W_contract.lp_cost MT (hs_pending h) (W_LLVMFuzzerTestOneInput_write.wr_n cx m)) ->
  0 <= t < OPS_MAX ->
  LSx ReplyB3LScap.fr_CAP cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_push m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m) si (W_LLVMFuzzerTestOneInput_write.set_pending h l') ev) ly' S'.
Proof.
  intros rc fx MT. apply (btlsi_LS_write_push rc fx ReplyB3LScap.fr_CAP MT).
  intros; eapply ReplyB3LScap.fr_CAP_write_push; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_rm_step_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (MT : ameter_ops),
  forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  LSx ReplyB3LScap.fr_CAP cx t m ly0 S0 ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S)
       (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= t < OPS_MAX ->
  LSx ReplyB3LScap.fr_CAP cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros rc fx MT. apply (btlsi_LS_rm_step rc fx ReplyB3LScap.fr_CAP MT).
  intros; eapply ReplyB3LScap.fr_CAP_rm_step; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_rm_step_f9_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (MT : ameter_ops),
  forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  LSx ReplyB3LScap.fr_CAP cx t m ly0 S0 ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S)
       (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= t < OPS_MAX ->
  LSx ReplyB3LScap.fr_CAP cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros rc fx MT. apply (btlsi_LS_rm_step_f9 rc fx ReplyB3LScap.fr_CAP MT).
  intros; eapply ReplyB3LScap.fr_CAP_rm_step; first [eassumption | apply Z.le_refl].
Qed.

Lemma btlsi_LS_event_step_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (MT : ameter_ops),
  forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  LSx ReplyB3LScap.fr_CAP cx t m ly S -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks TfibB ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks TfibB ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks TfibB ly3 S3 = l1 ++ l2) ->
  0 <= t < OPS_MAX ->
  LSx ReplyB3LScap.fr_CAP cx (t + 1) (W_LLVMFuzzerTestOneInput_arm_event.ev_step cx m e v out') ly3 S3.
Proof.
  intros rc fx MT. apply (btlsi_LS_event_step rc fx ReplyB3LScap.fr_CAP MT).
  intros; eapply ReplyB3LScap.fr_CAP_event_step; first [eassumption | apply Z.le_refl].
Qed.

(* LS_event_relay (top_x.v :831; ReplyBTop.v :195's Context) WITHOUT its meter conjunct, at any CAPS and any meter:
   the two room conjuncts (send_line's own room premises, lib/B/W_contract.v :836 sl_maxr and :834 sl_alloc) are
   lib/B/ReplyB3LS3Arms.v :1968 fr_LS3_event_relay_r at LS v3, read off LSx by lsi_parts (its fr_LS3 at
   CALL_ROOM_B := YCfn_cf.CALL_ROOM_B, so the room premise is Z.le_refl) *)
Lemma btlsi_LS_event_relay_m : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop) (MT : ameter_ops),
  forall cx t m ly S (S1 : astate) e (ly1 : alayout) q,
  LSx CAPS cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  lm_O m = [] ->
  ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
  sl_maxr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) < CfParamsReply.fr_MMAX /\
  blocks_bytes S1 + sl_alloc (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= LIVE_MAX.
Proof.
  intros rc fx CAPS MT cx t m ly S S1 e ly1 q H HRI Hev M1 HO0 Hm.
  btlsi_open H.
  exact (ReplyB3LS3Arms.fr_LS3_event_relay_r TfibB YCfn_cf.CALL_ROOM_B (Z.le_refl _) cx t m ly S S1 e ly1 q
    H3 HRI Hev M1 HO0 Hm).
Qed.

(* LS_event_relay's whole text (ReplyBTop.v :195 at CAPS := ReplyB3LScap.fr_CAP).  Its meter conjunct
   `mo_ok MT S1 (sl_cost MT ..)` (lib/B/W_contract.v :800 sl_cost, the meter of Section s7 :766) is not read off LSx:
   LSI has no meter clause (lib/B/ReplyLS3B_inst.v :224-227).  So it is the premise CAPS_event_relay_mo, over the
   CAPS slot, in the shape of lib/B/ReplyLSBSec.v :1998 sec_LS_event_relay (the count clause fr_SEC at the meter
   MT_sec nsec KMAX, its binders and premises in its order); at ameter_triv it is lib/B/ReplyB3Base.v :265 mo_ok_triv *)
Lemma btlsi_LS_event_relay : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop) (MT : ameter_ops)
  (CAPS_event_relay_mo :
    forall cx t m ly S (S1 : astate) e (ly1 : alayout) (q : Z),
    CAPS cx t m ly S -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
    mo_le MT S S1 (mo_malloc MT (re_len e)) ->
    lm_O m = [] ->
    mo_ok MT S1 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e))),
  forall cx t m ly S (S1 : astate) e (ly1 : alayout) q,
  LSx CAPS cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  lm_O m = [] ->
  ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
  sl_maxr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) < CfParamsReply.fr_MMAX /\
  blocks_bytes S1 + sl_alloc (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= LIVE_MAX /\
  mo_ok MT S1 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)).
Proof.
  intros rc fx CAPS MT CAPS_event_relay_mo cx t m ly S S1 e ly1 q H HRI Hev M1 HO0 Hm.
  destruct (btlsi_LS_event_relay_m rc fx CAPS MT cx t m ly S S1 e ly1 q H HRI Hev M1 HO0 Hm) as (R1 & R2).
  btlsi_open H.
  exact (conj R1 (conj R2 (CAPS_event_relay_mo cx t m ly S S1 e ly1 q HC Hev M1 HO0))).
Qed.
