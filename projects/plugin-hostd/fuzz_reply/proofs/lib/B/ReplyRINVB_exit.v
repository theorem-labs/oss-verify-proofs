(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: new file holding code from lib/A/ReplyRINV_a12.v (419c9d7c02f), lib/A/ReplyRINV_a3.v, lib/A/ReplyRINV.v and lib/A/ReplyTopXRI.v (8da615a239d) and lib/B/ReplyRINVB.v (f908a004fd1), restated at image B's names and at lib/B/ReplyBTop.v's Context texts. *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane, row G-BRI-exit-drain-event of a Theorem Labs lane's pool): six RI obligations of the
   image-B composition lib/B/ReplyBTop.v (a Theorem Labs lane's head f908a004fd1), over lib/B/ReplyRINVB.v's fr_RINV.  Each
   lemma `<name>_btop` below states its obligation's `Context (<name> : ...)` text of ReplyBTop.v word for word, so
   that `exact <name>_btop` closes that Context:
     RI_pro_btop         ReplyBTop.v:84   A source: lib/A/ReplyTopXRI.v topx_RI_pro and lib/A/ReplyRINV.v RI_pro_core
                                          (8da615a239d); here bx_pro_core is ReplyRINVB.v's RI_pro_holds_b body (:247-276)
                                          at W_LLVMFuzzerTestOneInput_pro.pro_m (oa_new_src for pro_new_src); stated at
                                          any MT / XM_LIB (a Theorem Labs lane's ReplyBTop.v) and over B top_x's ARX;
     RI_exit_slots_btop  ReplyBTop.v:88   A source: lib/A/ReplyRINV_a12.v RI_exit_slots_holds and its helpers (419c9d7c02f
                                          :85-129), with lib/A/ReplyRINV.v's fr_pair_of_open (8da615a239d :605-646);
     RI_drain_skip_btop  ReplyBTop.v:98   A source: lib/A/ReplyRINV_a3.v RI_drain_skip_holds (8da615a239d :141-146);
     RI_event_step_btop  ReplyBTop.v:140  A source: lib/A/ReplyRINV_a3.v RI_event_step_holds / RI_event_step_x (:122-138),
                                          with lib/A/ReplyRINV.v's fr_ctl_sl (:1203-1221).
   Two obligations are FALSE for fr_RINV as ReplyBTop.v states them; for each, this file proves the negation of that
   exact text (from any call context, as ReplyRINV_a12.v's `_false` lemmas) and the rule with the premises the B arm
   holds, as a separate lemma (the Context text is not changed here):
     RI_exit_ends (ReplyBTop.v:89, = B W_LLVMFuzzerTestOneInput_top_x.v:367): the text before A's restatement
       (a working branch 3f40808c334).  fr_RINV does not say lm_gn m is 0 or 1, nor that the held texts have no NUL
       byte.  RI_exit_ends_btop_false (lm_gn m = 2: the check gives Some 0, not Some 6) and RI_exit_ends_btop_false_nul
       (a held text of one NUL byte: the check gives None) refute the text; ReplyRINV_a12.v RI_exit_ends_obl_false /
       _false_nul (419c9d7c02f :271-283), over the same states (a12_ names as bx_ names).  RI_exit_ends_btop_restated
       is A's restated text (A top_x.v:461-466 at c0513fdca72) at image B's names; ReplyRINV_a12.v RI_exit_ends_holds
       and fr_exit_ends / fr_exit_ends_live (:390-658, :1076-1087); ExitB.bx_exit_ends_restated_sat: its premises
       hold together.
     RI_drain_step (ReplyBTop.v:99, = B W_LLVMFuzzerTestOneInput_top_x.v:442): B's dr_step_ok
       (W_LLVMFuzzerTestOneInput_drain_defs.v:224-249) is A's without three of its facts: the new entry's two paddings
       (A's `length (re_pad1 e') = 4%nat /\ length (re_pad2 e') = 4%nat`) and check_no_loss's held capacity bound
       (A's `hl_cap H' <= Z.max 8 (...)`), which fr_entry_ok (ReplyRINVB.v:165) and fr_pair_ok (ReplyRINVB.v:154)
       need; and the text lacks A's two restated premises (`0 <= t < OPS_MAX`, the held / begin bound < 2 ^ 22: A
       ReplyRINV.v:203-213, top_x.v:381-388 at c0513fdca72).  RI_drain_step_btop_false_pad (e' with re_pad1 e' = []) and
       RI_drain_step_btop_false_cap (hl_cap H' = 2 ^ 24) refute the text from a state that meets every premise.
       RI_drain_step_btop_restated adds the four premises; each is a fact the B arm has at its call
       (W_LLVMFuzzerTestOneInput_drain_calls_x.v:3591): the t bound (DLK's dr_regs_call, drain_defs.v:197), the
       held / begin bound (LS_cnl_pre, top_x.v:362), the paddings (dr_post's aentry_ok e', W_contract.v:1002, W_rep.v:125)
       and the held capacity (cnl_post, W_contract.v:2036).  Its proof is lib/A/ReplyRINV.v RI_drain_step_fix_holds
       (8da615a239d :1338-1534) with B's conjunct order of dr_step_ok; ExitB.bx_drain_step_restated_sat: its premises
       hold together.
   A -> B swaps: lib/A/ReplyRINV.v's fr_* -> lib/B/ReplyRINVB.v's (the same text, ReplyRINVB.v:3-60); A's _exit.v
   lx_* -> lib/B/W_bx_defs.v's (each definition the proofs read is byte-equal: lxo_e0, lx_ends_slot0, lx_ends_c1,
   lx_ends_scan, lx_ends_outer, lx_ends_run, lx_ends_slot_ok, lx_rf_O, lx_rf_run, lx_norder, lx_ord); A's _drain.v
   dr_* / set_nth -> lib/B/W_LLVMFuzzerTestOneInput_drain_defs.v's; A's _event.v ev_* ->
   lib/B/W_LLVMFuzzerTestOneInput_arm_event.v's; A's W_contract.v sl_* / ge_* / gse_* / dr_fin / dr_lines / dr_ctl /
   dr_live / sl_sends -> lib/B/W_contract.v's (byte-equal); ReplyRINV.v's rm_set_nth -> drain_defs' set_nth (the same
   body); lib/Prog is shared.
   The helpers live in Module ExitB, whose Imports end with it, so the six statements below it are read in
   ReplyBTop.v's own name environment (this file's imports are ReplyBTop.v's, less ReplyBTopLifts and ReplyDriverCfB,
   none of whose names is used here).
   proves no function (rule 24; kind: statement text; model rules over fr_RINV at image B, no machine walk). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf YGcfNames YCbqG YG0lawscf YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp YM05 YG0dcf YGcfRoomLive.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn YCeg YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn_cf YD1w_cf YD1w_cf_fp YD1w_cf_br.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTFIB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD1mcf YD1pcf ReplyTFIBBcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_top_x ReplyLSB ReplyRINVB.
(* the zify flag as this file's own proofs expect it, whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance YE2k.tfib_sink_head.
#[local] Existing Instance checksum_shape.

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyLSB ReplyRINVB ReplyLSBArms ReplyLSBTrPeak ReplyLSBDrainPre ReplyLSBRig ReplyLSBo ReplyLSBoRf.
Local Notation RLV := (@room_live_cf CfParams_reply).
(* the plain proof's lemmas and the model files the helpers name (Require only: no name of the texts below changes) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
CheckRep RelayKeys RelayModel ListRep SlotInv SlotReads SlotDrain3 SlotPass2Aux drain_b_c gestures_end_b_c send_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_bx_defs W_LLVMFuzzerTestOneInput_drain_defs W_LLVMFuzzerTestOneInput_arm_event W_LLVMFuzzerTestOneInput_pro W_op_add.

Module ExitB.
Import CheckRep RelayKeys RelayModel ListRep.
Import ReplyRINVB.
Import W_bx_defs W_LLVMFuzzerTestOneInput_drain_defs W_LLVMFuzzerTestOneInput_arm_event.

Section exitb.
Context {rc : YM05.RunCeil}.

(* ================================================================== lib/A/ReplyRINV.v's helpers (8da615a239d) *)
(* :605 fr_Forall2_r *)
Lemma bx_Forall2_r : forall (X Y : Type) (R : X -> Y -> Prop) l1 l2,
  Forall2 R l1 l2 -> forall y, In y l2 -> exists x, In x l1 /\ R x y.
Proof.
  intros X Y R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros z Hz; [destruct Hz|].
  destruct Hz as [<- | Hz]; [exists x; split; [left; reflexivity | exact Hxy]|].
  destruct (IH z Hz) as (x' & Hx' & HR). exists x'. split; [right; exact Hx' | exact HR].
Qed.
(* :612 fr_Forall2_comb *)
Lemma bx_Forall2_comb : forall (X Y : Type) (R : X -> Y -> Prop) l1 l2,
  Forall2 R l1 l2 -> forall y, In y l2 -> exists x, In (x, y) (combine l1 l2) /\ R x y.
Proof.
  intros X Y R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros z Hz; [destruct Hz|].
  destruct Hz as [<- | Hz]; [exists x; split; [left; reflexivity | exact Hxy]|].
  destruct (IH z Hz) as (x' & Hx' & HR). exists x'. split; [right; exact Hx' | exact HR].
Qed.
(* :620 fr_comb_inj: two entries of the table with the same fd are one row, so their sources are one *)
Lemma bx_comb_inj : forall (Y : Type) (es : list rentry) (hj : list Y), List.NoDup (map re_fd es) ->
  forall e1 p1 e2 p2, In (e1, p1) (combine es hj) -> In (e2, p2) (combine es hj) -> re_fd e1 = re_fd e2 ->
  p1 = p2.
Proof.
  intros Y es. induction es as [|x es IH]; intros hj Hnd e1 p1 e2 p2 H1 H2 Hf; [destruct H1|].
  destruct hj as [|y hj]; [destruct H1|]. cbn [map] in Hnd. apply NoDup_cons_iff in Hnd as [Hx Hnd].
  cbn [combine In] in H1, H2.
  destruct H1 as [E1 | H1]; destruct H2 as [E2 | H2].
  - injection E1 as <- <-. injection E2 as <- <-. reflexivity.
  - injection E1 as <- <-. exfalso. apply Hx. rewrite Hf. apply in_map. eapply in_combine_l. exact H2.
  - injection E2 as <- <-. exfalso. apply Hx. rewrite <- Hf. apply in_map. eapply in_combine_l. exact H1.
  - exact (IH hj Hnd e1 p1 e2 p2 H1 H2 Hf).
Qed.
(* :634 fr_pair_of_open: an open slot is some entry's source *)
Lemma bx_pair_of_open : forall m t hj i h, Forall2 (fr_pair_ok m t) (lm_es m) hj ->
  (forall i, (i < 4)%nat -> SlotInv.slot_open hj i = false -> nth i (lm_hs m) None = None) ->
  (i < 4)%nat -> nth i (lm_hs m) None = Some h ->
  exists e p, In (e, p) (combine (lm_es m) hj) /\ fr_pair_ok m t e p /\ snd p = i /\ fst p = h.
Proof.
  intros m t hj i h HF Hcl Hi Hh.
  destruct (SlotInv.slot_open hj i) eqn:Ho; [|rewrite (Hcl i Hi Ho) in Hh; discriminate Hh].
  unfold SlotInv.slot_open in Ho. apply existsb_exists in Ho as (x & Hx & Hxi).
  apply Nat.eqb_eq in Hxi. subst x. apply in_map_iff in Hx as (p & Hpi & Hp).
  destruct (bx_Forall2_comb _ _ _ _ _ HF p Hp) as (e & Hin & HR).
  exists e, p. split; [exact Hin|]. split; [exact HR|]. split; [exact Hpi|].
  destruct HR as (_ & Hn & _). rewrite Hpi, Hh in Hn. injection Hn as Ef. exact (eq_sym Ef).
Qed.
(* :739 RI_fds_holds: two open slots have distinct fds *)
Lemma bx_fds : forall (cx : lfcx) t m i1 i2 h1 h2,
  fr_RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
Proof.
  intros cx t m i1 i2 h1 h2 (_ & HR & _) Hi1 Hi2 Hne Hh1 Hh2 Hf.
  destruct HR as (_ & Hnd & _ & _ & hj & HF & _ & Hcl & _). apply NoDup_ListNoDup in Hnd.
  destruct (bx_pair_of_open m t hj i1 h1 HF Hcl Hi1 Hh1) as (e1 & p1 & Hin1 & HR1 & Hs1 & Hf1).
  destruct (bx_pair_of_open m t hj i2 h2 HF Hcl Hi2 Hh2) as (e2 & p2 & Hin2 & HR2 & Hs2 & Hf2).
  apply Hne. rewrite <- Hs1, <- Hs2. f_equal.
  apply (bx_comb_inj _ (lm_es m) hj Hnd e1 p1 e2 p2 Hin1 Hin2).
  destruct HR1 as (_ & _ & E1 & _). destruct HR2 as (_ & _ & E2 & _).
  rewrite <- E1, <- E2, Hf1, Hf2. exact Hf.
Qed.
(* :1168 fr_F2_nth *)
Lemma bx_F2_nth : forall (T1 T2 : Type) (R : T1 -> T2 -> Prop) l1 l2, Forall2 R l1 l2 ->
  forall i d1 d2, (i < length l1)%nat -> R (nth i l1 d1) (nth i l2 d2).
Proof.
  intros T1 T2 R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros [|i] d1 d2 Hi; cbn [length] in Hi;
    try lia; cbn [nth]; [exact Hxy | apply IH; lia].
Qed.
(* :1193 fr_keys_total_nonneg, :1195 fr_pair_cost_nonneg *)
Lemma bx_keys_total_nonneg : forall ks, 0 <= gestures_end_b_c.keys_total ks.
Proof. unfold gestures_end_b_c.keys_total. induction ks as [|k ks IH]; cbn [fold_right]; lia. Qed.
Lemma bx_pair_cost_nonneg : forall e p, 0 <= fr_pair_cost e p.
Proof.
  intros e p. unfold fr_pair_cost. pose proof (bx_keys_total_nonneg (re_keys e)).
  destruct (re_skip e =? 0); lia.
Qed.
(* :1203-1229 fr_ctl_ok / fr_ctl_step / fr_ctl_sl / fr_ctl_dr: the controller's flags against g_gone through the
   sends (send_line keeps g_client and g_send_dead; it sets g_client_broken only from g_send_dead) *)
Definition bx_ctl_ok (gn : Z) (c : ctl) : Prop :=
  (gn = 0 -> ct_cl c = 3 /\ ct_br c = 0 /\ ct_dd c = 0) /\ (gn = 1 -> ct_cl c = -1 \/ ct_br c = 1 \/ ct_dd c = 1).
Lemma bx_ctl_step : forall gn c c', ct_cl c' = ct_cl c -> ct_dd c' = ct_dd c ->
  (ct_br c' = ct_br c \/ (ct_br c' = ct_dd c /\ ct_br c <> 1)) -> bx_ctl_ok gn c -> bx_ctl_ok gn c'.
Proof.
  intros gn c c' E1 E2 E3 (G0 & G1). unfold bx_ctl_ok. rewrite E1, E2. split.
  - intros Hg. destruct (G0 Hg) as (A1 & A2 & A3).
    destruct E3 as [E3 | (E3 & _)]; rewrite E3; [exact (conj A1 (conj A2 A3)) | exact (conj A1 (conj A3 A3))].
  - intros Hg. destruct (G1 Hg) as [A1 | [A2 | A3]]; [left; exact A1 | | right; right; exact A3].
    destruct E3 as [E3 | (_ & N)]; [right; left; rewrite E3; exact A2 | contradiction].
Qed.
Lemma bx_ctl_sl : forall gn c len, bx_ctl_ok gn c -> bx_ctl_ok gn (sl_ctl c len).
Proof.
  intros gn c len Hc. apply (bx_ctl_step gn c); [reflexivity | reflexivity | | exact Hc].
  unfold sl_ctl. cbn [ct_br].
  destruct (send_line_c.send_off (ct_cl c) (ct_br c) len) eqn:E; [left; reflexivity|].
  right. split; [reflexivity|]. unfold send_line_c.send_off in E.
  apply orb_false_iff in E as [E _]. apply orb_false_iff in E as [_ E]. apply Z.eqb_neq in E. exact E.
Qed.
Lemma bx_ctl_dr : forall gn c h ev, bx_ctl_ok gn c -> bx_ctl_ok gn (dr_ctl c h ev).
Proof.
  intros gn c h ev Hc. apply (bx_ctl_step gn c); [reflexivity | reflexivity | | exact Hc].
  unfold dr_ctl. cbn [ct_br].
  destruct (send_line_c.send_off (ct_cl c) (ct_br c) (dr_tot h)) eqn:E; [left; reflexivity|].
  right. split; [reflexivity|]. unfold send_line_c.send_off in E.
  apply orb_false_iff in E as [E _]. apply orb_false_iff in E as [_ E]. apply Z.eqb_neq in E. exact E.
Qed.

(* ================================================================== RI_pro (ReplyBTop.v:84) *)
(* ReplyRINVB.v RI_pro_holds_b's body (:250-276) from the input's length range (A ReplyRINV.v RI_pro_core :653), at
   W_LLVMFuzzerTestOneInput_pro.pro_m (B _pro.v:677, the same text as ReplyRINVB.v's pro_m with W_op_add.oa_new_src) *)
Lemma bx_pro_core : forall (cx : lfcx) q T' pj c O cap out,
  0 <= c_n cx < 2 ^ 26 -> ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 ->
  fr_RINV cx 0 (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out).
Proof.
  intros cx q T' pj c O cap out Hn Hcl Hbr Hdd.
  split; [|split; [|split]].
  - unfold fr_count, W_LLVMFuzzerTestOneInput_pro.pro_m, nopen, OPS_MAX. cbn. lia.
  - unfold fr_relay, W_LLVMFuzzerTestOneInput_pro.pro_m. cbn [lm_hs lm_es lm_nfd lm_k].
    split; [reflexivity|].
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split; [constructor; [cbn; lia | constructor]|].
    split.
    { constructor; [|constructor]. unfold fr_entry_ok. cbn.
      split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply NoDup_ListNoDup; constructor | left; reflexivity]. }
    exists [(OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.W_op_add.oa_new_src 100 q pj, 0%nat)].
    split.
    { constructor; [|constructor]. unfold fr_pair_ok. cbn.
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; split; [reflexivity | intros _; reflexivity]|].
      split; [intros y; split; intros []|]. split; [apply NoDup_ListNoDup; constructor|]. split; [reflexivity|].
      split; [left; reflexivity|]. split; [lia|]. split; [unfold SlotInv.WRITE_MAX; lia | lia]. }
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split.
    { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *;
        first [discriminate Ho | reflexivity | lia]. }
    unfold fr_cost, fr_pair_cost. cbn. lia.
  - exact (proj2 Hn).
  - unfold fr_gone, W_LLVMFuzzerTestOneInput_pro.pro_m. cbn [lm_gn lm_c]. split; intros H; [auto | discriminate H].
Qed.

(* ================================================================== RI_exit_slots (ReplyBTop.v:88) *)
(* lib/A/ReplyRINV_a12.v (419c9d7c02f) :85-113: a row's cost is at most the table's; a key costs >= 5; the held list
   is no longer than the keys *)
Lemma bx_sum_nonneg : forall (l : list (rentry * (hsrc * nat))),
  0 <= fold_right Z.add 0 (map (fun q => fr_pair_cost (fst q) (snd q)) l).
Proof.
  induction l as [|q l IH]; cbn [map fold_right]; [lia|].
  pose proof (bx_pair_cost_nonneg (fst q) (snd q)). lia.
Qed.
Lemma bx_sum_ge : forall (l : list (rentry * (hsrc * nat))) q, In q l ->
  fr_pair_cost (fst q) (snd q) <= fold_right Z.add 0 (map (fun q => fr_pair_cost (fst q) (snd q)) l).
Proof.
  induction l as [|q0 l IH]; intros q Hq; [destruct Hq|]. cbn [map fold_right].
  pose proof (bx_sum_nonneg l) as Hl. pose proof (bx_pair_cost_nonneg (fst q0) (snd q0)) as H0.
  destruct Hq as [<- | Hq]; [lia|]. specialize (IH q Hq). lia.
Qed.
Lemma bx_cost_ge : forall es hj e p, In (e, p) (combine es hj) -> fr_pair_cost e p <= fr_cost es hj.
Proof. intros es hj e p Hin. unfold fr_cost. exact (bx_sum_ge (combine es hj) (e, p) Hin). Qed.
Lemma bx_keys_len : forall ks, 5 * Z.of_nat (length ks) <= gestures_end_b_c.keys_total ks.
Proof.
  unfold gestures_end_b_c.keys_total. induction ks as [|k ks IH]; cbn [fold_right length]; lia.
Qed.
Lemma bx_held_keys : forall ks (H : hlist), NoDup (texts H) -> same_set (drain_b_c.keys_texts ks) (texts H) ->
  hl_n H <= Z.of_nat (length ks).
Proof.
  intros ks H Hnd Hss. first [apply NoDup_ListNoDup in Hnd | idtac].
  assert (Hinc : incl (texts H) (drain_b_c.keys_texts ks)) by (intros y Hy; exact (proj2 (Hss y) Hy)).
  pose proof (NoDup_incl_length Hnd Hinc) as Hle.
  unfold texts, drain_b_c.keys_texts in Hle. rewrite !length_map in Hle. unfold hl_n. lia.
Qed.
(* a12 :117-129 RI_exit_slots_holds: an open slot's held list is an entry's (distinct texts, one key for each), and
   the keys' cost (5 bytes or more each) is in the input cost, below c_n cx < 2 ^ 26 *)
Lemma bx_exit_slots : forall (cx : lfcx) t m, fr_RINV cx t m ->
  forall j, (j < 4)%nat -> lx_ends_slot_ok (nth j (lm_hs m) None).
Proof.
  intros cx t m (_ & HR & Hn & _) j Hj.
  destruct HR as (_ & _ & _ & _ & hj & HF & _ & Hcl & _ & Hcn).
  destruct (nth j (lm_hs m) None) as [h|] eqn:Eh; cbn [lx_ends_slot_ok]; [|exact I].
  destruct (bx_pair_of_open m t hj j h HF Hcl Hj Eh) as (e & p & Hin & HRp & _ & Hfst).
  destruct HRp as (_ & _ & _ & _ & Hss & Hnd & _). rewrite Hfst in Hss, Hnd.
  split; [first [exact Hnd | exact (proj1 (NoDup_ListNoDup _) Hnd) | exact (proj2 (NoDup_ListNoDup _) Hnd)]|].
  pose proof (bx_held_keys (re_keys e) (hs_held h) Hnd Hss) as Hle.
  pose proof (bx_keys_len (re_keys e)) as Hk.
  pose proof (bx_cost_ge (lm_es m) hj e p Hin) as Hc.
  unfold fr_pair_cost in Hc. destruct (re_skip e =? 0); lia.
Qed.

(* ================================================================== RI_drain_skip (ReplyBTop.v:98) *)
(* lib/A/ReplyRINV_a3.v (8da615a239d) :141-146: no relay entry to drain for the picked source: only the cursor moves *)
Lemma bx_drain_skip : forall (cx : lfcx) t m si h, fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
   (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
      re_eof (nth j (lm_es m) dr_e0) = 1)) ->
  fr_RINV cx (t + 1) (dr_skip m (dr_k' cx m)).
Proof.
  intros cx t m si h H _ _ _. apply (fr_step_k cx t m _ H); try reflexivity.
  - unfold dr_skip, dr_k'. cbn [lm_k]. destruct (lm_k m + 1 <? c_n cx); lia.
  - destruct H as (_ & _ & _ & HG). exact HG.
Qed.

(* ================================================================== RI_event_step (ReplyBTop.v:140) *)
(* lib/A/ReplyRINV_a3.v :122-130: relay_event sends the event line; the slots, the table and g_nfd stay, the cursor
   moves forward (the input bytes are in [0, 256): lib/B/W_LLVMFuzzerTestOneInput_arm_event.v's ev_in_byte_range) and the flags keep their link to
   g_gone (bx_ctl_sl) *)
Lemma bx_event_step : forall (cx : lfcx) t m e v out',
  fr_RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
  ev_evt cx m e -> 0 <= v < 2 ^ 32 ->
  fr_RINV cx (t + 1) (ev_step cx m e v out').
Proof.
  intros cx t m e v out' H Hk _ _ _ _. apply (fr_step_k cx t m _ H); try reflexivity.
  - unfold ev_step, ev_k2, ev_k1, ev_len, ev_cons2, ev_u16. cbn [lm_k].
    pose proof (ev_in_byte_range cx (lm_k m + 1)). pose proof (ev_in_byte_range cx (lm_k m + 2)).
    destruct (Z.leb_spec 1 (c_n cx - lm_k m - 1)); destruct (Z.leb_spec 2 (c_n cx - lm_k m - 1)); lia.
  - destruct H as (_ & _ & _ & HG). pose proof (bx_ctl_sl (lm_gn m) (lm_c m) (re_len e) HG) as X.
    unfold fr_gone, ev_step, ev_ctl. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. exact X.
Qed.

(* ================================================================== RI_exit_ends (ReplyBTop.v:89): a12 :390-658
   (fr_live3 .. fr_exit_ends), with drain_defs' set_nth for ReplyRINV.v's rm_set_nth *)
Definition bx_live3 (c : ctl) : Prop := ct_cl c = 3 /\ ct_br c = 0 /\ ct_dd c = 0.
Definition bx_dead (c : ctl) : Prop := ct_cl c = -1 \/ ct_br c = 1 \/ ct_dd c = 1.
Lemma bx_sl_live3 : forall c len, bx_live3 c -> sl_live c len = negb (len =? 0).
Proof.
  intros [cl br dd ei ev] len (E1 & E2 & E3). cbn [ct_cl ct_br ct_dd] in *. subst cl br dd.
  unfold sl_live, send_line_c.send_live, send_line_c.send_off. cbn [ct_cl ct_br ct_dd].
  destruct (len =? 0); reflexivity.
Qed.
Lemma bx_sl_ctl3 : forall c len, bx_live3 c -> bx_live3 (sl_ctl c len).
Proof.
  intros [cl br dd ei ev] len (E1 & E2 & E3). cbn [ct_cl ct_br ct_dd] in *. subst cl br dd.
  unfold sl_ctl, bx_live3. cbn [ct_cl ct_br ct_dd].
  destruct (send_line_c.send_off 3 0 len); (repeat split); reflexivity.
Qed.
Lemma bx_sl_O3 : forall c O x, bx_live3 c -> sl_O c O x = O ++ x.
Proof.
  intros c O x H. unfold sl_O. rewrite (bx_sl_live3 c _ H).
  destruct x as [|b x]; [cbn; rewrite app_nil_r; reflexivity | reflexivity].
Qed.
Lemma bx_ge_O3 : forall c O x, bx_live3 c -> ge_O c O x = O ++ x ++ END5.
Proof.
  intros c O x H. unfold ge_O. rewrite (bx_sl_O3 c O x H), (bx_sl_O3 _ _ END5 (bx_sl_ctl3 c _ H)).
  rewrite app_assoc. reflexivity.
Qed.
Lemma bx_gse_run3 : forall xs c O mx no cap, bx_live3 c ->
  gse_O (gse_run c O mx no cap xs) = O ++ concat (map (fun x => x ++ END5) xs) /\
  bx_live3 (gse_c (gse_run c O mx no cap xs)).
Proof.
  induction xs as [|x xs IH]; intros c O mx no cap H.
  - cbn [gse_run gse_O gse_c fst snd map concat]. rewrite app_nil_r. split; [reflexivity | exact H].
  - cbn [gse_run map concat].
    destruct (IH (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
      (ge_cap c mx no cap (Z.of_nat (length x))) (bx_sl_ctl3 _ 5 (bx_sl_ctl3 c _ H))) as (E & L).
    split; [|exact L]. rewrite E, (bx_ge_O3 c O x H). rewrite <- !app_assoc. reflexivity.
Qed.
Lemma bx_rf_run3 : forall es c O mx no cap, bx_live3 c ->
  gse_O (lx_rf_run c O mx no cap es) = O ++ concat (map (fun e => gestures_end_b_c.keys_out (re_keys e)) es).
Proof.
  induction es as [|e es IH]; intros c O mx no cap H.
  - cbn [lx_rf_run gse_O fst snd map concat]. rewrite app_nil_r. reflexivity.
  - cbn [lx_rf_run map concat].
    destruct (bx_gse_run3 (gse_keys e) c O mx no cap H) as (E & L).
    rewrite IH by exact L. rewrite E. rewrite <- app_assoc. f_equal. f_equal.
    unfold gse_keys, gestures_end_b_c.keys_out. rewrite map_map. reflexivity.
Qed.
Lemma bx_sl_dead : forall c len, bx_dead c -> sl_live c len = false /\ bx_dead (sl_ctl c len).
Proof.
  intros [cl br dd ei ev] len Hd. unfold bx_dead in *. cbn [ct_cl ct_br ct_dd] in Hd.
  unfold sl_live, sl_ctl, send_line_c.send_live, send_line_c.send_off. cbn [ct_cl ct_br ct_dd].
  destruct Hd as [-> | [-> | ->]].
  - split; [reflexivity | left; reflexivity].
  - destruct (cl <? 0); (split; [reflexivity | right; left; reflexivity]).
  - destruct ((cl <? 0) || (br =? 1) || (len =? 0)); (split; [reflexivity | right; right; reflexivity]).
Qed.
Lemma bx_ge_dead : forall c O x, bx_dead c -> ge_O c O x = O /\ bx_dead (ge_ctl c (Z.of_nat (length x))).
Proof.
  intros c O x H. unfold ge_O, ge_ctl, sl_O.
  destruct (bx_sl_dead c (Z.of_nat (length x)) H) as (L1 & D1).
  destruct (bx_sl_dead _ 5 D1) as (_ & D2).
  destruct (bx_sl_dead _ (Z.of_nat (length END5)) D1) as (L2 & _).
  rewrite L1, L2. split; [reflexivity | exact D2].
Qed.
Lemma bx_gse_dead : forall xs c O mx no cap, bx_dead c ->
  gse_O (gse_run c O mx no cap xs) = O /\ bx_dead (gse_c (gse_run c O mx no cap xs)).
Proof.
  induction xs as [|x xs IH]; intros c O mx no cap H; cbn [gse_run].
  - split; [reflexivity | exact H].
  - destruct (bx_ge_dead c O x H) as (E & D). rewrite E. apply IH. exact D.
Qed.
Lemma bx_rf_dead : forall es c O mx no cap, bx_dead c -> gse_O (lx_rf_run c O mx no cap es) = O.
Proof.
  induction es as [|e es IH]; intros c O mx no cap H; cbn [lx_rf_run]; [reflexivity|].
  destruct (bx_gse_dead (gse_keys e) c O mx no cap H) as (E & D). rewrite IH by exact D. exact E.
Qed.
(* the check at gone <> 0 only drops the records of prefix "" and keeps the offset *)
Lemma bx_scan_gone : forall gone ob oi A sl, gone <> 0 -> exists sl', lx_ends_scan gone ob oi A sl = Some (sl', A).
Proof.
  intros gone ob oi A sl Hg. apply Z.eqb_neq in Hg.
  induction sl as [|o sl IH]; [exists []; reflexivity|].
  destruct IH as (sl' & E). destruct o as [[fd recs]|]; cbn [lx_ends_scan].
  - destruct (fd =? oi).
    + unfold lx_ends_c1. rewrite Hg. cbv beta iota zeta. rewrite E. eexists. reflexivity.
    + cbv beta iota zeta. rewrite E. eexists. reflexivity.
  - rewrite E. eexists. reflexivity.
Qed.
Lemma bx_outer_gone : forall gone ob ord n i A sl, gone <> 0 ->
  exists sl', lx_ends_outer gone ob ord n i A sl = Some (sl', A).
Proof.
  intros gone ob ord n. induction n as [|n IH]; intros i A sl Hg; cbn [lx_ends_outer].
  - exists sl. reflexivity.
  - destruct (bx_scan_gone gone ob (ord i) A sl Hg) as (sl' & E). rewrite E.
    destruct (IH (i + 1) A sl' Hg) as (sl'' & E'). exists sl''. exact E'.
Qed.
(* the scan at gone = 0 when exactly one slot s0 has the entry's fd oi *)
Lemma bx_scan_none : forall ob oi A (sl : list lx_ends_rslot),
  (forall s fd recs, nth s sl None = Some (fd, recs) -> fd <> oi) ->
  lx_ends_scan 0 ob oi A sl = Some (sl, A).
Proof.
  intros ob oi A sl. induction sl as [|o sl IH]; intros Hn; [reflexivity|].
  assert (Hn' : forall s fd recs, nth s sl None = Some (fd, recs) -> fd <> oi)
    by (intros s fd recs E; exact (Hn (S s) fd recs E)).
  destruct o as [[fd recs]|]; cbn [lx_ends_scan].
  - assert (Hf : fd <> oi) by exact (Hn 0%nat fd recs eq_refl). apply Z.eqb_neq in Hf. rewrite Hf.
    rewrite (IH Hn'). reflexivity.
  - rewrite (IH Hn'). reflexivity.
Qed.
Lemma bx_scan_one : forall ob oi recs0 recs0' A A' (sl : list lx_ends_rslot) s0,
  nth s0 sl None = Some (oi, recs0) ->
  (forall s fd recs, s <> s0 -> nth s sl None = Some (fd, recs) -> fd <> oi) ->
  lx_ends_c1 0 ob recs0 A = Some (recs0', A') ->
  lx_ends_scan 0 ob oi A sl = Some (W_LLVMFuzzerTestOneInput_drain_defs.set_nth s0 (Some (oi, recs0')) sl, A').
Proof.
  intros ob oi recs0 recs0' A A' sl. induction sl as [|o sl IH]; intros s0 H0 Hn Hc;
    [destruct s0; discriminate H0|].
  destruct s0 as [|s0].
  - cbn [nth] in H0. subst o.
    assert (Hn0 : forall s fd recs, nth s sl None = Some (fd, recs) -> fd <> oi)
      by (intros s fd recs E; exact (Hn (S s) fd recs ltac:(lia) E)).
    cbn [lx_ends_scan W_LLVMFuzzerTestOneInput_drain_defs.set_nth]. rewrite Z.eqb_refl, Hc. cbv beta iota zeta.
    rewrite (bx_scan_none ob oi A' sl Hn0). reflexivity.
  - cbn [nth] in H0.
    assert (Hn' : forall s fd recs, s <> s0 -> nth s sl None = Some (fd, recs) -> fd <> oi)
      by (intros s fd recs Hs E; exact (Hn (S s) fd recs ltac:(lia) E)).
    destruct o as [[fd recs]|]; cbn [lx_ends_scan W_LLVMFuzzerTestOneInput_drain_defs.set_nth].
    + assert (Hf : fd <> oi) by exact (Hn 0%nat fd recs ltac:(lia) eq_refl). apply Z.eqb_neq in Hf. rewrite Hf.
      rewrite (IH s0 H0 Hn' Hc). reflexivity.
    + rewrite (IH s0 H0 Hn' Hc). reflexivity.
Qed.
Lemma bx_firstn_S : forall (T : Type) (l : list T) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  intros T l. induction l as [|x l IH]; intros [|i] d Hi; cbn [length] in Hi; try lia; [reflexivity|].
  cbn [firstn nth app]. rewrite (IH i d) by lia. reflexivity.
Qed.
Lemma bx_skipn_S : forall (T : Type) (l : list T) i d, (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof.
  intros T l. induction l as [|x l IH]; intros [|i] d Hi; cbn [length] in Hi; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.
Lemma bx_skipn_concat : forall (T U : Type) (f : T -> list U) (l : list T) i,
  skipn (length (concat (map f (firstn i l)))) (concat (map f l)) = concat (map f (skipn i l)).
Proof.
  intros T U f l. induction l as [|x l IH]; intros [|i]; cbn [firstn skipn map concat]; try reflexivity.
  rewrite length_app, skipn_app, skipn_all2 by lia.
  replace (length (f x) + length (concat (map f (firstn i l))) - length (f x))%nat
    with (length (concat (map f (firstn i l)))) by lia.
  cbn [app]. apply IH.
Qed.
(* the slot list during the check: closed slots stay None, an open slot keeps its fd, and an open slot whose fd no
   entry before i has keeps its held records *)
Definition bx_xinv (es : list rentry) (hs : list (option hsrc)) (i : nat) (sl : list lx_ends_rslot) : Prop :=
  length sl = length hs /\
  forall s, (nth s hs None = None -> nth s sl None = None) /\
    (forall h, nth s hs None = Some h -> exists recs, nth s sl None = Some (hs_fd h, recs) /\
       ((forall k, (k < i)%nat -> re_fd (nth k es lxo_e0) <> hs_fd h) -> recs = hl_recs (hs_held h))).
Lemma bx_xinv0 : forall es hs, bx_xinv es hs 0 (map lx_ends_slot0 hs).
Proof.
  intros es hs. split; [apply length_map|]. intros s.
  change (nth s (map lx_ends_slot0 hs) None) with (nth s (map lx_ends_slot0 hs) (lx_ends_slot0 None)).
  rewrite map_nth. split.
  - intros E. rewrite E. reflexivity.
  - intros h E. exists (hl_recs (hs_held h)). rewrite E. split; [reflexivity | intros _; reflexivity].
Qed.
Lemma bx_exit_ends_live : forall cx t m, fr_RINV cx t m -> bx_live3 (lm_c m) ->
  Forall (fun e => Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k)) (re_keys e)) (lm_es m) ->
  lx_ends_run 0 (lx_rf_O m) (lx_norder m) (lx_ord m) (lm_hs m) 0 = Some (Z.of_nat (length (lx_rf_O m))).
Proof.
  intros cx t m HRI Hlive Hnul.
  pose proof HRI as (_ & HR & _ & _).
  destruct HR as (Hlen & Hnd & _ & Hent & hj & HF & HNDs & Hcl & _).
  apply NoDup_ListNoDup in Hnd. rewrite Forall_forall in Hent, Hnul.
  assert (HO : lx_rf_O m = concat (map (fun e => gestures_end_b_c.keys_out (re_keys e)) (lm_es m)))
    by (unfold lx_rf_O; rewrite (bx_rf_run3 _ _ _ _ _ _ Hlive); reflexivity).
  assert (Hn4 : (length (lm_es m) <= 4)%nat).
  { rewrite (Forall2_length HF). apply NoDup_ListNoDup in HNDs.
    assert (Hinc : incl (map snd hj) [0; 1; 2; 3]%nat).
    { intros y Hy. apply in_map_iff in Hy as (p & <- & Hp).
      destruct (bx_Forall2_r _ _ _ _ _ HF p Hp) as (e & _ & (Hs4 & _)). clear - Hs4.
      revert Hs4. generalize (snd p) as q. intros q Hq.
      destruct q as [|[|[|[|q]]]]; cbn; first [tauto | lia]. }
    pose proof (NoDup_incl_length HNDs Hinc) as X. rewrite length_map in X. exact X. }
  assert (Hno : Z.to_nat (lx_norder m) = length (lm_es m)) by (unfold lx_norder; lia).
  (* the loop over order[0 .. norder) *)
  assert (Hout : forall n i zi A sl, (i + n = length (lm_es m))%nat -> zi = Z.of_nat i ->
      bx_xinv (lm_es m) (lm_hs m) i sl ->
      A = Z.of_nat (length (concat (map (fun e => gestures_end_b_c.keys_out (re_keys e)) (firstn i (lm_es m))))) ->
      exists sl', lx_ends_outer 0 (lx_rf_O m) (lx_ord m) n zi A sl = Some (sl', Z.of_nat (length (lx_rf_O m)))).
  { induction n as [|n IH]; intros i zi A sl Hin Hzi Hinv HA.
    - exists sl. cbn [lx_ends_outer]. rewrite HA, HO. replace i with (length (lm_es m)) by lia.
      rewrite firstn_all. reflexivity.
    - assert (Hi : (i < length (lm_es m))%nat) by lia.
      set (e := nth i (lm_es m) lxo_e0).
      pose proof (bx_F2_nth _ _ _ _ _ HF i lxo_e0 relay_instance_gone_b_c.no_hj Hi) as HRp. fold e in HRp.
      set (p := nth i hj relay_instance_gone_b_c.no_hj) in HRp.
      destruct HRp as (Hs4 & Hsn & Hpfd & _ & Hss & Hndh & _).
      destruct Hinv as (Hsl & Hinv).
      destruct (proj2 (Hinv (snd p)) (fst p) Hsn) as (recs0 & Hr0 & Hun).
      assert (Hunp : forall k, (k < i)%nat -> re_fd (nth k (lm_es m) lxo_e0) <> hs_fd (fst p)).
      { intros k Hk E. rewrite Hpfd in E.
        assert (k = i); [|lia].
        apply (proj1 (NoDup_nth (map re_fd (lm_es m)) (re_fd lxo_e0)) Hnd k i); rewrite ?length_map; try lia.
        rewrite !map_nth. exact E. }
      specialize (Hun Hunp). subst recs0.
      assert (Hoi : lx_ord m zi = re_fd e) by (unfold lx_ord; rewrite Hzi, Nat2Z.id; reflexivity).
      (* the entry's part of the output: its keys' ends, at the offset A *)
      assert (He : In e (lm_es m)) by (apply nth_In; exact Hi).
      assert (Hk : exists rs' ds, ends_run [] (hl_recs (hs_held (fst p)))
          (gestures_end_b_c.keys_out (re_keys e) ++
           concat (map (fun e => gestures_end_b_c.keys_out (re_keys e)) (skipn (S i) (lm_es m))))
          (length (hl_recs (hs_held (fst p)))) =
        Some (rs', ds, Z.of_nat (length (gestures_end_b_c.keys_out (re_keys e))))).
      { apply SlotReads.ends_run_keys.
        - destruct (Hent e He) as (_ & _ & _ & X & _). first [exact X | exact (proj1 (NoDup_ListNoDup _) X)
            | exact (proj2 (NoDup_ListNoDup _) X)].
        - first [exact Hndh | exact (proj1 (NoDup_ListNoDup _) Hndh) | exact (proj2 (NoDup_ListNoDup _) Hndh)].
        - exact Hss.
        - exact (Hnul e He). }
      destruct Hk as (rs' & ds & Hrun).
      assert (Hc1 : lx_ends_c1 0 (lx_rf_O m) (hl_recs (hs_held (fst p))) A =
          Some (rs', A + Z.of_nat (length (gestures_end_b_c.keys_out (re_keys e))))).
      { unfold lx_ends_c1. cbn [Z.eqb]. rewrite HA, Nat2Z.id, HO, bx_skipn_concat, (bx_skipn_S _ _ i lxo_e0 Hi).
        cbn [map concat]. fold e. rewrite SlotReads.want_of_nil, Hrun. reflexivity. }
      assert (Hr0' : nth (snd p) sl None = Some (re_fd e, hl_recs (hs_held (fst p)))) by (rewrite Hr0, Hpfd; reflexivity).
      assert (Hsc := bx_scan_one (lx_rf_O m) (re_fd e) (hl_recs (hs_held (fst p))) rs' A
        (A + Z.of_nat (length (gestures_end_b_c.keys_out (re_keys e)))) sl (snd p) Hr0').
      assert (Hsc' : lx_ends_scan 0 (lx_rf_O m) (re_fd e) A sl =
          Some (W_LLVMFuzzerTestOneInput_drain_defs.set_nth (snd p) (Some (re_fd e, rs')) sl, A + Z.of_nat (length (gestures_end_b_c.keys_out (re_keys e))))).
      { apply Hsc; [|exact Hc1]. intros s fd recs Hs E.
        destruct (nth s (lm_hs m) None) as [h|] eqn:Eh.
        - destruct (proj2 (Hinv s) h Eh) as (recs1 & Er & _). rewrite E in Er. injection Er as -> _.
          assert (Hs4' : (s < 4)%nat).
          { destruct (Nat.lt_ge_cases s 4) as [X | X]; [exact X|]. rewrite nth_overflow in Eh by lia. discriminate Eh. }
          intros Ef. apply (bx_fds cx t m s (snd p) h (fst p) HRI Hs4' Hs4 Hs Eh Hsn). rewrite Ef, Hpfd. reflexivity.
        - rewrite (proj1 (Hinv s) Eh) in E. discriminate E. }
      cbn [lx_ends_outer]. rewrite Hoi, Hsc'. cbv beta iota zeta.
      apply (IH (S i) (zi + 1)); [lia | lia | |].
      + split; [rewrite W_LLVMFuzzerTestOneInput_drain_defs.set_nth_length; exact Hsl|]. intros s.
        destruct (Nat.eq_dec s (snd p)) as [-> | Ns].
        * split; [intros E; rewrite Hsn in E; discriminate E|].
          intros h E. rewrite Hsn in E. injection E as <-. exists rs'. split.
          -- assert (Hsp : (snd p < length sl)%nat) by (rewrite Hsl, Hlen; exact Hs4).
             rewrite Hpfd. exact (W_LLVMFuzzerTestOneInput_drain_defs.set_nth_same _ (snd p) (Some (re_fd e, rs')) sl None Hsp).
          -- intros Hk. exfalso. apply (Hk i ltac:(lia)). fold e. exact (eq_sym Hpfd).
        * rewrite (W_LLVMFuzzerTestOneInput_drain_defs.set_nth_other lx_ends_rslot (snd p) s) by (intros X; apply Ns; symmetry; exact X).
          split; [exact (proj1 (Hinv s))|]. intros h E.
          destruct (proj2 (Hinv s) h E) as (recs1 & Er & Hu). exists recs1. split; [exact Er|].
          intros Hk. apply Hu. intros k Hk'. apply Hk. lia.
      + rewrite HA, (bx_firstn_S _ _ i lxo_e0 Hi), map_app, concat_app, length_app. cbn [map concat].
        rewrite app_nil_r. fold e. lia. }
  unfold lx_ends_run. rewrite Hno.
  destruct (Hout (length (lm_es m)) 0%nat 0 0 (map lx_ends_slot0 (lm_hs m)) eq_refl eq_refl (bx_xinv0 _ _) eq_refl)
    as (sl' & E).
  rewrite E. reflexivity.
Qed.
Lemma bx_exit_ends : forall cx t m, fr_RINV cx t m -> (lm_gn m = 0 \/ lm_gn m = 1) ->
  Forall (fun e => Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k)) (re_keys e)) (lm_es m) ->
  lx_ends_run (lm_gn m) (lx_rf_O m) (lx_norder m) (lx_ord m) (lm_hs m) 0 = Some (Z.of_nat (length (lx_rf_O m))).
Proof.
  intros cx t m HRI Hg Hnul. pose proof HRI as (_ & _ & _ & (G0 & G1)).
  destruct Hg as [E | E]; rewrite E.
  - exact (bx_exit_ends_live cx t m HRI (G0 E) Hnul).
  - assert (HO : lx_rf_O m = []) by (unfold lx_rf_O; apply bx_rf_dead; exact (G1 E)).
    rewrite HO. unfold lx_ends_run.
    destruct (bx_outer_gone 1 [] (lx_ord m) (Z.to_nat (lx_norder m)) 0 0 (map lx_ends_slot0 (lm_hs m)) ltac:(lia))
      as (sl' & E'). rewrite E'. reflexivity.
Qed.

(* a12 :990-999 fr_keys_nz: the key texts are NUL-free when the held list they match is *)
Lemma bx_keys_nz : forall ks (rs : list (Z * list byte)), Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) rs ->
  (forall y, In y (drain_b_c.keys_texts ks) -> In y (map (fun r => bzs (snd r)) rs)) ->
  Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k)) ks.
Proof.
  intros ks rs HR HS. apply Forall_forall. intros k Hk HZ.
  assert (Hy : In (bzs (gestures_end_b_c.key_text k)) (drain_b_c.keys_texts ks))
    by (unfold drain_b_c.keys_texts; apply (in_map (fun k => bzs (gestures_end_b_c.key_text k))); exact Hk).
  apply HS in Hy. apply in_map_iff in Hy as (r & Er & Hr).
  apply SlotReads.bzs_inj in Er. rewrite Forall_forall in HR. apply (HR r Hr). rewrite Er. exact HZ.
Qed.
(* a12 :1069 fr_a12_F2_l *)
Lemma bx_F2_l : forall (X Y : Type) (R : X -> Y -> Prop) l1 l2,
  Forall2 R l1 l2 -> forall x, In x l1 -> exists y, In y l2 /\ R x y.
Proof.
  intros X Y R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros z Hz; [destruct Hz|].
  destruct Hz as [<- | Hz]; [exists y; split; [left; reflexivity | exact Hxy]|].
  destruct (IH z Hz) as (y' & Hy' & HR). exists y'. split; [right; exact Hy' | exact HR].
Qed.
(* a12 :1076-1087 RI_exit_ends_holds: A's restated text (top_x.v:461-466 at c0513fdca72) at image B's names *)
Lemma bx_exit_ends_restated : forall (cx : lfcx) t m, fr_RINV cx t m -> (0 < length (lm_es m))%nat ->
  0 <= lm_gn m <= 1 ->
  (forall i h, nth i (lm_hs m) None = Some h -> Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))) ->
  lx_ends_run (lm_gn m) (lx_rf_O m) (lx_norder m) (lx_ord m) (lm_hs m) 0 = Some (Z.of_nat (length (lx_rf_O m))).
Proof.
  intros cx t m HRI _ Hg Hnul. apply (bx_exit_ends cx t m HRI); [lia|].
  pose proof HRI as (_ & HR & _ & _). destruct HR as (_ & _ & _ & _ & hj & HF & _ & _ & _).
  apply Forall_forall. intros e He.
  destruct (bx_F2_l _ _ _ _ _ HF e He) as (p & _ & HRp).
  destruct HRp as (_ & Hsn & _ & _ & Hss & _).
  exact (bx_keys_nz (re_keys e) (hl_recs (hs_held (fst p))) (Hnul _ _ Hsn) (fun y Hy => proj1 (Hss y) Hy)).
Qed.

(* ================================================================== the states the `_false` and `_sat` lemmas use
   (a12 :155-247, :1125-1161): from any call context cx0 (its layout, state, world, registers, memory and model kept;
   the input replaced), one open slot 0 with source bx_src H (fd 100, held list H), one relay entry (fd 100, keys ks),
   the controller CTL 3 0 0 0 0 *)
Definition bx_cx (cx0 : lfcx) (n : Z) (pl : list byte) : lfcx :=
  LFCX (c_ly cx0) (c_S cx0) (c_W cx0) (c_regs cx0) (c_mem cx0) (c_md cx0) 0 n pl 0.
Definition bx_pad : list byte := [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition bx_E0 : hlist := HL 0 0 [] [].
Definition bx_src (H : hlist) : hsrc := HS 100 1 0 0 bx_E0 0 0 [] 0 0 [] bx_E0 H.
Definition bx_ent (ks : list (Z * list byte * list byte)) : rentry :=
  RE 100 1 1 bx_pad 0 0 0 0 0 bx_pad ks [] [].
Definition bx_m (k : Z) (H : hlist) (ks : list (Z * list byte * list byte)) (gn : Z) : lmod :=
  LM k [Some (bx_src H); None; None; None] 0 [bx_ent ks] (CTL 3 0 0 0 0) [] 0 0 0 gn 1.
(* a12 :166 a12_RINV: fr_RINV holds when the keys and the held texts agree and the keys' cost is in the input *)
Lemma bx_RINV : forall cx0 n pl k H ks gn,
  NoDup (drain_b_c.keys_texts ks) -> same_set (drain_b_c.keys_texts ks) (texts H) -> NoDup (texts H) ->
  hl_cap H < 2 ^ 24 -> gestures_end_b_c.keys_total ks <= k -> k <= n -> n < 2 ^ 26 -> gn <> 1 ->
  fr_RINV (bx_cx cx0 n pl) 0 (bx_m k H ks gn).
Proof.
  intros cx0 n pl k H ks gn Hnk Hss Hnd Hcap Hk Hkn Hn Hgn.
  split; [|split; [|split]].
  - unfold fr_count, nopen, OPS_MAX, bx_m. cbn [lm_nfd lm_hs List.filter length Z.of_nat]. lia.
  - unfold fr_relay, bx_m. cbn [lm_hs lm_es lm_nfd lm_k length].
    split; [reflexivity|].
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split; [constructor; [cbn; lia | constructor]|].
    split.
    { constructor; [|constructor]. unfold fr_entry_ok, bx_ent, bx_pad.
      cbn [re_eof re_pad1 re_pad2 re_keys re_skip length].
      split; [right; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hnk | right; reflexivity]. }
    exists [(bx_src H, 0%nat)].
    split.
    { constructor; [|constructor]. unfold fr_pair_ok, bx_src, bx_ent.
      cbn [fst snd nth lm_hs re_eof re_fd hs_fd re_keys hs_held hs_expected hs_off hl_recs hl_cap].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros E; discriminate E|].
      split; [exact Hss|]. split; [exact Hnd|]. split; [reflexivity|].
      split; [left; reflexivity|]. split; [exact Hcap|].
      split; [unfold pending_stream, bx_E0; cbn [hs_pending hl_recs length Z.of_nat]; unfold SlotInv.WRITE_MAX; lia
             | lia]. }
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split.
    { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *; first [discriminate Ho | reflexivity | lia]. }
    unfold fr_cost, fr_pair_cost, bx_ent, bx_src, pending_stream, bx_E0.
    cbn -[gestures_end_b_c.keys_total]. lia.
  - exact Hn.
  - unfold fr_gone, bx_m. cbn [lm_gn lm_c ct_cl ct_br ct_dd].
    split; intros E; [repeat split | exfalso; exact (Hgn E)].
Qed.
Lemma bx_pick : forall h kb, pick [Some h; None; None; None] kb = Some 0%nat.
Proof. intros h kb. unfold pick. cbn -[Z.modulo]. rewrite Z.mod_1_r. reflexivity. Qed.
(* a12 :228-243: one held text x, one key of text x, cost 6 = |x| + 5; the input 10 bytes of 4 *)
Definition bx_pl : list byte := repeat (Z_to_bv 8 4) 10.
Definition bx_H1 (x : list byte) : hlist := HL 0 8 [(0, x)] [].
Definition bx_ks1 (x : list byte) : list (Z * list byte * list byte) := [(0, x, [])].
Definition bx_a : list byte := [Z_to_bv 8 97].   (* "a" *)
Definition bx_nul : list byte := [Z_to_bv 8 0].  (* one NUL byte *)
Lemma bx_RINV1 : forall cx0 x gn, length x = 1%nat -> gn <> 1 ->
  fr_RINV (bx_cx cx0 10 bx_pl) 0 (bx_m 6 (bx_H1 x) (bx_ks1 x) gn).
Proof.
  intros cx0 x gn Hx Hgn. apply bx_RINV; try lia.
  - apply NoDup_ListNoDup. repeat constructor. intros [].
  - intros y. split; intros Hy; exact Hy.
  - apply NoDup_ListNoDup. repeat constructor. intros [].
  - cbn. lia.
  - unfold gestures_end_b_c.keys_total, bx_ks1, gestures_end_b_c.key_text. cbn [fold_right fst snd].
    rewrite Hx. cbn. lia.
Qed.
(* a12 :1168 a12_a_nz *)
Lemma bx_a_nz : ~ In (Z_to_bv 8 0) bx_a.
Proof. intros [X | []]. apply (f_equal bv_unsigned) in X. revert X. vm_compute. intros X. discriminate X. Qed.
(* a12 :1181-1189 RI_exit_ends_sat: the restated rule's premises hold together *)
Lemma bx_exit_ends_restated_sat : lfcx -> exists (cx : lfcx) t m, fr_RINV cx t m /\ (0 < length (lm_es m))%nat /\
  0 <= lm_gn m <= 1 /\
  (forall i h, nth i (lm_hs m) None = Some h -> Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))).
Proof.
  intros cx0. exists (bx_cx cx0 10 bx_pl), 0, (bx_m 6 (bx_H1 bx_a) (bx_ks1 bx_a) 0).
  split; [apply bx_RINV1; [reflexivity | lia]|]. split; [cbn; lia|]. split; [cbn; lia|].
  intros i h E. destruct i as [|[|[|[|i]]]]; cbn [bx_m lm_hs nth] in E;
    [| discriminate E | discriminate E | discriminate E | destruct i; discriminate E].
  injection E as <-. constructor; [exact bx_a_nz | constructor].
Qed.

(* ================================================================== RI_drain_step (ReplyBTop.v:99): A ReplyRINV.v
   :1338-1411's helpers (drain_defs' set_nth for _drain.v's) *)
Lemma bx_Forall_dset : forall (T : Type) (P : T -> Prop) j x l, Forall P l -> P x ->
  Forall P (W_LLVMFuzzerTestOneInput_drain_defs.set_nth j x l).
Proof.
  intros T P j x l. revert j. induction l as [|a l IH]; intros [|j] Hl Hx;
    cbn [W_LLVMFuzzerTestOneInput_drain_defs.set_nth].
  - constructor.
  - constructor.
  - apply Forall_cons_iff in Hl as [_ Hl]. constructor; [exact Hx | exact Hl].
  - apply Forall_cons_iff in Hl as [Ha Hl]. constructor; [exact Ha | exact (IH j Hl Hx)].
Qed.
Lemma bx_dset_map_eq : forall (T U : Type) (f : T -> U) j x l d, (j < length l)%nat -> f x = f (nth j l d) ->
  map f (W_LLVMFuzzerTestOneInput_drain_defs.set_nth j x l) = map f l.
Proof.
  intros T U f j x l d. revert j. induction l as [|a l IH]; intros [|j] Hj Hf; cbn [length] in Hj; try lia;
    cbn [W_LLVMFuzzerTestOneInput_drain_defs.set_nth map nth] in Hf |- *.
  - rewrite Hf. reflexivity.
  - rewrite (IH j ltac:(lia) Hf). reflexivity.
Qed.
Lemma bx_F2_lift : forall (T1 T2 : Type) (R R' : T1 -> T2 -> Prop) (Q : T2 -> Prop) d2 l1 l2,
  Forall2 R l1 l2 -> (forall a b, Q b -> R a b -> R' a b) ->
  (forall k, (k < length l2)%nat -> Q (nth k l2 d2)) -> Forall2 R' l1 l2.
Proof.
  intros T1 T2 R R' Q d2 l1 l2 H HQ. induction H as [|a b l1 l2 Hab _ IH]; intros Hk; constructor.
  - apply HQ; [exact (Hk 0%nat ltac:(cbn [length]; lia)) | exact Hab].
  - apply IH. intros k Hkl. exact (Hk (S k) ltac:(cbn [length]; lia)).
Qed.
Lemma bx_F2_dset : forall (T1 T2 : Type) (R R' : T1 -> T2 -> Prop) (Q : T2 -> Prop) d2 j x y l1 l2,
  Forall2 R l1 l2 -> R' x y -> (forall a b, Q b -> R a b -> R' a b) ->
  (forall k, k <> j -> (k < length l2)%nat -> Q (nth k l2 d2)) ->
  Forall2 R' (W_LLVMFuzzerTestOneInput_drain_defs.set_nth j x l1) (W_LLVMFuzzerTestOneInput_drain_defs.set_nth j y l2).
Proof.
  intros T1 T2 R R' Q d2 j x y l1 l2 H Hxy HQ. revert j.
  induction H as [|a b l1 l2 Hab Hrest IH]; intros [|j] Hk; cbn [W_LLVMFuzzerTestOneInput_drain_defs.set_nth].
  - constructor.
  - constructor.
  - constructor; [exact Hxy|]. apply (bx_F2_lift _ _ R R' Q d2 l1 l2 Hrest HQ).
    intros k Hkl. exact (Hk (S k) ltac:(lia) ltac:(cbn [length]; lia)).
  - constructor.
    + apply HQ; [exact (Hk 0%nat ltac:(lia) ltac:(cbn [length]; lia)) | exact Hab].
    + apply IH. intros k Hkn Hkl. exact (Hk (S k) ltac:(lia) ltac:(cbn [length]; lia)).
Qed.
Lemma bx_nopen_dset : forall hs i x y, nth i hs None = Some y -> (i < length hs)%nat ->
  nopen (W_LLVMFuzzerTestOneInput_drain_defs.set_nth i (Some x) hs) = nopen hs.
Proof.
  intros hs i x y. unfold nopen. revert i. induction hs as [|o hs IH]; intros [|i] Hn Hi;
    cbn [length] in Hi; try lia.
  - cbn [nth] in Hn. subst o. reflexivity.
  - cbn [nth] in Hn. pose proof (IH i Hn ltac:(lia)) as Hih.
    destruct o; cbn [W_LLVMFuzzerTestOneInput_drain_defs.set_nth List.filter length]; lia.
Qed.
Lemma bx_cost_dset : forall es hj j e' p' d1 d2, length es = length hj -> (j < length es)%nat ->
  fr_cost (W_LLVMFuzzerTestOneInput_drain_defs.set_nth j e' es) (W_LLVMFuzzerTestOneInput_drain_defs.set_nth j p' hj) +
  fr_pair_cost (nth j es d1) (nth j hj d2) = fr_cost es hj + fr_pair_cost e' p'.
Proof.
  unfold fr_cost. induction es as [|e es IH]; intros [|p hj] [|j] e' p' d1 d2 Hl Hj; cbn [length] in Hl, Hj;
    try lia.
  - cbn [W_LLVMFuzzerTestOneInput_drain_defs.set_nth combine map fold_right nth fst snd]. lia.
  - cbn [W_LLVMFuzzerTestOneInput_drain_defs.set_nth combine map fold_right nth fst snd].
    pose proof (IH hj j e' p' d1 d2 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma bx_bzs_line : forall l, SlotReads.zrange l -> bzs (map (Z_to_bv 8) l) = l.
Proof.
  induction l as [|z l IH]; intros Hl; [reflexivity|]. apply Forall_cons_iff in Hl as [Hz Hl].
  unfold bzs in *. cbn [map]. rewrite SlotReads.bz_lit by exact Hz. f_equal. apply IH. exact Hl.
Qed.
Lemma bx_bzs_lines : forall Ls, Forall SlotReads.zrange Ls -> map bzs (map (map (Z_to_bv 8)) Ls) = Ls.
Proof.
  induction Ls as [|l Ls IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [H1 H2]. cbn [map].
  rewrite bx_bzs_line by exact H1. f_equal. apply IH. exact H2.
Qed.
(* the entry with re_used replaced by its line's length: SlotInv.pair_cost of it is fr_pair_cost *)
Definition bx_ru (e : rentry) : rentry :=
  RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (Z.of_nat (length (re_U e))) (re_cap e) (re_hp e)
     (re_kh e) (re_pad2 e) (re_keys e) (re_U e) (re_junk e).
(* A ReplyRINV.v:1418-1534 RI_drain_step_fix_holds, at B's dr_step_ok (lib/B/W_LLVMFuzzerTestOneInput_drain_defs.v:224-249: A's conjuncts less the two
   paddings and the held capacity, the expected capacity before the controller) with those three as premises *)
Lemma bx_drain_step_restated : forall (cx : lfcx) t m si h j e' h' c' O' cap' out' ev' LB E' H',
  fr_RINV cx t m -> 0 <= t < OPS_MAX ->
  hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h'))) < 2 ^ 22 ->
  dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr_step_ok cx m si h j e' h' c' O' cap' out' ev' LB E' H' ->
  length (re_pad1 e') = 4%nat -> length (re_pad2 e') = 4%nat ->
  hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h'))
    (2 * (hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h')))))) ->
  fr_RINV cx (t + 1) (dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' c' O' cap' out').
Proof.
  intros cx t m si h j e' h' c' O' cap' out' ev' LB E' H' HRI Ht Hcb Hat Hpick Hj Hfdj Heof Hok Opad1 Opad2 OHcap.
  pose proof HRI as ((HC & Hnfd) & HR & Hn & HG).
  destruct HR as (Hlen & Hnd & Hrng & Hent & hj & HF & HNDs & Hcl & Hc & Hcn).
  destruct Hpick as (_ & Hsi & Hh).
  (* B's dr_step_ok: drain's half (the expected capacity last), the controller / stream / capacity, then
     check_no_loss's half *)
  destruct Hok as (Ofd & Oeof & _ & _ & _ & Oskip & _ & _ & OND & OSS & Ohfd & _ & _ & OHP & Ooff & OST & Oexp &
    Oheld & OS2 & OW2 & _ & Oecap & Oc' & _ & _ & OE0 & _ & OEcap & OHND & OHt).
  pose proof (Forall2_length HF) as Hlh.
  assert (Hjh : (j < length hj)%nat) by lia.
  assert (Hk : lm_k m <= dr_k' cx m) by (unfold dr_k'; destruct (lm_k m + 1 <? c_n cx); lia).
  (* the row at j is slot si's *)
  pose proof (bx_F2_nth _ _ _ _ _ HF j dr_e0 (h, si) Hj) as Hp0.
  assert (Hs0 : snd (nth j hj (h, si)) = si).
  { destruct Hp0 as (H4 & Hn0 & Hf0 & _).
    destruct (Nat.eq_dec (snd (nth j hj (h, si))) si) as [E | Ne]; [exact E | exfalso].
    apply (bx_fds cx t m _ si _ h HRI H4 Hsi Ne Hn0 Hh). rewrite Hf0. exact Hfdj. }
  assert (Ep0 : nth j hj (h, si) = (h, si)).
  { destruct Hp0 as (_ & Hn0 & _). rewrite Hs0, Hh in Hn0. injection Hn0 as Ef.
    apply injective_projections; [exact (eq_sym Ef) | exact Hs0]. }
  rewrite Ep0 in Hp0.
  destruct Hp0 as (_ & _ & _ & Hre & Hss & _ & Hexp0 & Hec & Hhc & Hpe & Hoff).
  cbn [fst snd] in Hre, Hss, Hexp0, Hec, Hhc, Hpe, Hoff.
  destruct (Hre Heof) as (S1 & W1).
  (* the other rows follow other slots *)
  assert (Hoth : forall k, k <> j -> (k < length hj)%nat -> snd (nth k hj (h, si)) <> si).
  { intros k Hkj Hkl E. apply Hkj.
    pose proof (proj1 (NoDup_ListNoDup _) HNDs) as ND.
    pose proof (proj1 (NoDup_nth (map snd hj) (snd (h, si))) ND) as ND'.
    apply ND'; [rewrite length_map; exact Hkl | rewrite length_map; exact Hjh |].
    rewrite !map_nth. rewrite Hs0. exact E. }
  (* entry j's skip flag, and so the sources' overlong flags *)
  pose proof Hent as Hent'. rewrite Forall_forall in Hent'.
  pose proof Hrng as Hrng'. rewrite Forall_forall in Hrng'.
  assert (He : In (nth j (lm_es m) dr_e0) (lm_es m)) by (apply nth_In; exact Hj).
  destruct (Hent' _ He) as (_ & _ & _ & _ & Hsk).
  assert (O1 : hs_overlong h = 0 \/ hs_overlong h = 1) by (rewrite <- S1; exact Hsk).
  assert (Hsk' : re_skip e' = 0 \/ re_skip e' = 1).
  { rewrite Oskip. match goal with |- context [if ?b then _ else _] => destruct b end; [right | left]; reflexivity. }
  assert (O2 : hs_overlong h' = 0 \/ hs_overlong h' = 1) by (rewrite <- OS2; exact Hsk').
  (* the expected list after the drain holds exactly the drained lines *)
  assert (Etx : texts (hs_expected h') = dr_lines h).
  { unfold texts.
    replace (map (fun r => bzs (snd r)) (hl_recs (hs_expected h')))
      with (map bzs (map snd (hl_recs (hs_expected h')))) by (rewrite List.map_map; reflexivity).
    rewrite Oexp, Hexp0. cbn [map app]. apply bx_bzs_lines.
    exact (proj1 (SlotReads.lines_range (bzs (pending_stream h)) (hs_state h) (SlotReads.zrange_bzs (hs_W h))
      (SlotReads.zrange_bzs (pending_stream h)))). }
  (* its capacity is ecap_ok: at most 65535 * 511 < 2 ^ 25 pending bytes *)
  assert (Hecap : SlotInv.ecap_ok (hl_cap E')).
  { rewrite OEcap, Oecap. unfold dr_fin.
    apply SlotDrain3.drain3_ecap; [exact Hoff | exact Hec |].
    assert (P25 : 2 ^ 25 = 33554432) by reflexivity.
    unfold hl_n. rewrite Hexp0. cbn [length]. unfold SlotInv.WRITE_MAX, OPS_MAX in *. lia. }
  (* row j's cost does not grow *)
  assert (Hpc : fr_pair_cost e' (set_exp_held h' E' H', si) <= fr_pair_cost (nth j (lm_es m) dr_e0) (h, si))
    by exact (SlotPass2Aux.p2_pair_cost (bx_ru (nth j (lm_es m) dr_e0)) (bx_ru e') h h' si S1 W1 O1 eq_refl
                OS2 OW2 O2 eq_refl OST OHP OND OSS).
  pose proof (bx_cost_dset (lm_es m) hj j e' (set_exp_held h' E' H', si) dr_e0 (h, si) Hlh Hj) as Hcd.
  rewrite Ep0 in Hcd.
  split; [|split; [|split; [exact Hn|]]].
  - unfold fr_count, dr_step. cbn [lm_nfd lm_hs].
    rewrite (bx_nopen_dset _ _ _ _ Hh ltac:(lia)). lia.
  - unfold fr_relay, dr_step. cbn [lm_hs lm_es lm_nfd lm_k].
    split; [rewrite W_LLVMFuzzerTestOneInput_drain_defs.set_nth_length; exact Hlen|].
    split; [rewrite (bx_dset_map_eq _ _ re_fd j e' (lm_es m) dr_e0 Hj Ofd); exact Hnd|].
    split.
    { apply bx_Forall_dset; [exact Hrng|]. cbv beta. rewrite Ofd. exact (Hrng' _ He). }
    split.
    { apply bx_Forall_dset; [exact Hent|]. unfold fr_entry_ok.
      split; [rewrite Oeof, Heof; destruct (hs_closed h =? 1); [right | left]; reflexivity|].
      split; [exact Opad1|]. split; [exact Opad2|]. split; [exact OND | exact Hsk']. }
    exists (W_LLVMFuzzerTestOneInput_drain_defs.set_nth j (set_exp_held h' E' H', si) hj).
    split.
    { apply (bx_F2_dset _ _ (fr_pair_ok m t) _ (fun b => snd b <> si) (h, si)); [exact HF | | |].
      - (* the drained row *)
        unfold fr_pair_ok. cbn [fst snd lm_hs].
        rewrite (W_LLVMFuzzerTestOneInput_drain_defs.set_nth_same _ si (Some (set_exp_held h' E' H')) (lm_hs m) None
          ltac:(lia)).
        refine (conj Hsi (conj eq_refl (conj _ (conj _ (conj _ (conj OHND (conj OE0 (conj Hecap
          (conj _ (conj _ _)))))))))).
        + cbn [hs_fd set_exp_held]. rewrite Ohfd, Ofd. exact (eq_sym Hfdj).
        + intros _. split; [exact OS2 | exact OW2].
        + change (same_set (drain_b_c.keys_texts (re_keys e')) (texts H')).
          rewrite OHt, Oheld, Etx. intros y. rewrite (OSS y).
          exact (SlotReads.upds_same_set (dr_lines h) _ _ Hss y).
        + change (hl_cap H' < 2 ^ 24).
          assert (P22 : 2 ^ 22 = 4194304) by reflexivity. assert (P24 : 2 ^ 24 = 16777216) by reflexivity.
          rewrite Oheld in OHcap, Hcb. lia.
        + unfold pending_stream. cbn [hs_pending hs_off set_exp_held]. rewrite OHP. cbn [length].
          unfold SlotInv.WRITE_MAX. lia.
        + cbn [hs_off set_exp_held]. rewrite Ooff. lia.
      - (* the other rows *)
        intros a b Hb Hab. cbv beta in Hb.
        destruct Hab as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
        unfold fr_pair_ok. cbn [lm_hs].
        rewrite (W_LLVMFuzzerTestOneInput_drain_defs.set_nth_other _ si (snd b) _ _ _ (not_eq_sym Hb)).
        unfold SlotInv.WRITE_MAX in *.
        refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9
          (conj _ H11)))))))))). lia.
      - intros k Hkj Hkl. exact (Hoth k Hkj Hkl). }
    split.
    { rewrite (bx_dset_map_eq _ _ snd j (set_exp_held h' E' H', si) hj (h, si) Hjh ltac:(rewrite Ep0; reflexivity)).
      exact HNDs. }
    split.
    { intros i Hi Ho.
      assert (Ho' : SlotInv.slot_open hj i = false).
      { unfold SlotInv.slot_open in *.
        rewrite (bx_dset_map_eq _ _ snd j (set_exp_held h' E' H', si) hj (h, si) Hjh
          ltac:(rewrite Ep0; reflexivity)) in Ho. exact Ho. }
      assert (Hne : si <> i).
      { intros E. subst i. rewrite (Hcl si Hi Ho') in Hh. discriminate Hh. }
      rewrite (W_LLVMFuzzerTestOneInput_drain_defs.set_nth_other _ si i _ _ _ Hne). exact (Hcl i Hi Ho'). }
    split; lia.
  - change (bx_ctl_ok (lm_gn m) c'). rewrite Oc'. apply bx_ctl_dr. exact HG.
Qed.

(* ---- the drain step's state (the `_false` and `_sat` lemmas): the open entry bx_ent0 (eof 0, skip 0) of slot 0
   (a12 :1125-1161's a12_ent0 / a12_m0), the cursor at 6 over ten input bytes of value 2 (op 2 = drain); the drain
   reads no pending byte, and bx_e' / bx_h' are what dr_step_ok's equations make of the entry and the source *)
Definition bx_ent0 : rentry := RE 100 0 0 bx_pad 0 0 0 0 0 bx_pad (bx_ks1 bx_a) [] [].
Definition bx_h0 : hsrc := bx_src (bx_H1 bx_a).
Definition bx_m0 : lmod := LM 6 [Some bx_h0; None; None; None] 0 [bx_ent0] (CTL 3 0 0 0 0) [] 0 0 0 0 1.
Definition bx_pl2 : list byte := repeat (Z_to_bv 8 2) 10.
Lemma bx_RINV0 : forall cx0 pl, fr_RINV (bx_cx cx0 10 pl) 0 bx_m0.
Proof.
  intros cx0 pl. split; [|split; [|split]].
  - unfold fr_count, nopen, OPS_MAX, bx_m0. cbn [lm_nfd lm_hs List.filter length Z.of_nat]. lia.
  - unfold fr_relay, bx_m0. cbn [lm_hs lm_es lm_nfd lm_k length].
    split; [reflexivity|].
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split; [constructor; [cbn; lia | constructor]|].
    split.
    { constructor; [|constructor]. unfold fr_entry_ok, bx_ent0, bx_pad.
      cbn [re_eof re_pad1 re_pad2 re_keys re_skip length].
      split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply NoDup_ListNoDup; repeat constructor; intros [] | left; reflexivity]. }
    exists [(bx_h0, 0%nat)].
    split.
    { constructor; [|constructor]. unfold fr_pair_ok, bx_h0, bx_src, bx_ent0.
      cbn [fst snd nth lm_hs re_eof re_fd hs_fd re_keys hs_held hs_expected hs_off hl_recs hl_cap].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; split; [reflexivity | intros _; reflexivity]|].
      split; [intros y; split; intros Hy; exact Hy|].
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split; [reflexivity|]. split; [left; reflexivity|]. split; [cbn; lia|].
      split; [unfold pending_stream, bx_E0; cbn [hs_pending hl_recs length Z.of_nat]; unfold SlotInv.WRITE_MAX; lia
             | lia]. }
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split.
    { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *; first [discriminate Ho | reflexivity | lia]. }
    unfold fr_cost, fr_pair_cost, bx_ent0, bx_h0, bx_src, pending_stream, bx_E0, bx_ks1, bx_a,
      gestures_end_b_c.keys_total, gestures_end_b_c.key_text.
    cbn. lia.
  - unfold bx_cx. cbn [c_n]. lia.
  - unfold fr_gone, bx_m0. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. split; intros E; [repeat split | discriminate E].
Qed.
Lemma bx_dat : forall cx0, dr_at_op (bx_cx cx0 10 bx_pl2) bx_m0.
Proof.
  intros cx0. unfold dr_at_op, bx_m0. cbn [lm_k lm_O].
  split; [unfold bx_cx; cbn [c_n]; lia|]. split; [reflexivity|]. reflexivity.
Qed.
Lemma bx_dpick : forall cx0, dr_pick (bx_cx cx0 10 bx_pl2) bx_m0 0 bx_h0.
Proof. intros cx0. unfold dr_pick, bx_m0. cbn [lm_hs]. split; [apply bx_pick|]. split; [lia | reflexivity]. Qed.
Definition bx_fin : drain_b_c.dstate :=
  dr_fin (lm_c bx_m0) (lm_mx bx_m0) (Z.of_nat (length (lm_O bx_m0))) (lm_cap bx_m0) bx_ent0 bx_h0.
Definition bx_e' (p1 : list byte) : rentry :=
  RE 100 0 (if drain_b_c.ds_skip bx_fin then 1 else 0) p1 0 0 (drain_b_c.ds_cap bx_fin) 1 (drain_b_c.ds_ka bx_fin)
     bx_pad (map (fun x => (0, map (Z_to_bv 8) x, @nil byte)) (drain_b_c.ds_H bx_fin))
     (map (Z_to_bv 8) (drain_b_c.ds_u bx_fin)) [].
Definition bx_h' : hsrc :=
  HS 100 1 0 0 bx_E0 0 0 [] 0 (if drain_b_c.ds_skip bx_fin then 1 else 0) [] (HL 0 (drain_b_c.ds_ecap bx_fin) [] [])
     (bx_H1 bx_a).
Definition bx_E' : hlist := HL 0 (drain_b_c.ds_ecap bx_fin) [] [].
Definition bx_H' (cap : Z) : hlist := HL 0 cap [(0, bx_a)] [].
Definition bx_c' : ctl := dr_ctl (lm_c bx_m0) bx_h0 0.
Definition bx_O' : list byte := if dr_live (lm_c bx_m0) bx_h0 then lm_O bx_m0 ++ [] else lm_O bx_m0.
Definition bx_cap' : Z := if dr_live (lm_c bx_m0) bx_h0 then drain_b_c.ds_ocap bx_fin else lm_cap bx_m0.
(* dr_step_ok holds at the state, for any first padding p1 of the new entry and any held capacity cap of H' *)
Lemma bx_dok : forall (cx : lfcx) p1 cap,
  dr_step_ok cx bx_m0 0 bx_h0 0 (bx_e' p1) bx_h' bx_c' bx_O' bx_cap' 0 0 [] bx_E' (bx_H' cap).
Proof.
  intros cx p1 cap. unfold dr_step_ok. cbv zeta.
  repeat match goal with |- _ /\ _ => split end.
  all: first [ (vm_compute; reflexivity)
             | (intros _; vm_compute; reflexivity)
             | (intros y; vm_compute; tauto)
             | (apply NoDup_ListNoDup; vm_compute; repeat constructor; intros []) ].
Qed.
(* the restated rule's premises hold together at the state (paddings bx_pad, held capacity 8) *)
Lemma bx_drain_step_restated_sat : forall cx0 : lfcx,
  let cx := bx_cx cx0 10 bx_pl2 in let e' := bx_e' bx_pad in let H' := bx_H' 8 in
  fr_RINV cx 0 bx_m0 /\ 0 <= 0 < OPS_MAX /\
  hl_n (hs_held bx_h') + Z.of_nat (count_begin (texts (hs_expected bx_h'))) < 2 ^ 22 /\
  dr_at_op cx bx_m0 /\ dr_pick cx bx_m0 0 bx_h0 /\
  (0 < length (lm_es bx_m0))%nat /\ re_fd (nth 0 (lm_es bx_m0) dr_e0) = hs_fd bx_h0 /\
  re_eof (nth 0 (lm_es bx_m0) dr_e0) = 0 /\
  dr_step_ok cx bx_m0 0 bx_h0 0 e' bx_h' bx_c' bx_O' bx_cap' 0 0 [] bx_E' H' /\
  length (re_pad1 e') = 4%nat /\ length (re_pad2 e') = 4%nat /\
  hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held bx_h'))
    (2 * (hl_n (hs_held bx_h') + Z.of_nat (count_begin (texts (hs_expected bx_h')))))).
Proof.
  intros cx0 cx e' H'.
  split; [apply bx_RINV0|]. split; [unfold OPS_MAX; lia|].
  split; [vm_compute; reflexivity|]. split; [apply bx_dat|]. split; [apply bx_dpick|].
  split; [cbn; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply bx_dok|].
  split; [reflexivity|]. split; [reflexivity|]. vm_compute. intros X; discriminate X.
Qed.

End exitb.
End ExitB.

(* ================================================================== the obligations, at ReplyBTop.v's Context text
   (f908a004fd1), word for word, except RI_pro_btop (MT / XM_LIB generic, as a Theorem Labs lane's ReplyBTop.v) *)
(* ReplyBTop.v:84 RI_pro: the first head's model meets fr_RINV from lf_base_x's input-length range (its sixth
   conjunct, B _cut_x.v:97, at the place of lf_base's, B _cut.v:261), at any meter MT and library bound XM_LIB *)
Lemma RI_pro_btop : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (MT : ameter_ops) (XM_LIB : Z -> Z), ∀ (cx : @lfcx rc) (Hp : list Z) (q T' : Z) (pj : list byte) (c : ctl) (O : list byte) (cap out : Z), @lf_base_x rc TfibB MT XM_LIB REPLYB_RO_LO REPLYB_RO_HI fr_live_pre_b (@LIBROOM_fr CfParams_reply) RLV (G_fr_c TfibB) (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) cx Hp → (∃ (c0 : ctl) (mx0 : Z), @aout_at rc (@PB_fr rc) TfibB fr_RG (@c_ly rc cx) (@c_S rc cx) (@c_W rc cx) (@c_mem rc cx) c0 O mx0 (Z.of_nat (@length byte O)) cap out) → ct_cl c = 3 → ct_br c = 0 → ct_dd c = 0 → ct_ei c = 0 → @ReplyRINVB.fr_RINV rc cx 0 (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out).
Proof.
  intros rc fx MT XM_LIB cx Hp q T' pj c O cap out HB _ Hcl Hbr Hdd _.
  apply (@ExitB.bx_pro_core rc cx q T' pj c O cap out); [| exact Hcl | exact Hbr | exact Hdd].
  destruct HB as (_ & _ & _ & _ & _ & Hn & _). destruct Hn as [(Hz & _) | (Hn & _)]; lia.
Qed.
(* ReplyBTop.v:88 RI_exit_slots *)
Lemma RI_exit_slots_btop : forall (rc : YM05.RunCeil) (fx : YK11.FPState), ∀ (cx : @lfcx rc) (t : Z) (m : lmod), @ReplyRINVB.fr_RINV rc cx t m → ∀ j : nat, (j < 4)%nat → W_bx_defs.lx_ends_slot_ok (@nth (option hsrc) j (lm_hs m) (@None hsrc)).
Proof. intros rc fx. exact (@ExitB.bx_exit_slots rc). Qed.
(* ReplyBTop.v:98 RI_drain_skip *)
Lemma RI_drain_skip_btop : forall (rc : YM05.RunCeil) (fx : YK11.FPState), ∀ (cx : lfcx) (t : Z) (m : lmod) (si : nat) (h : hsrc), ReplyRINVB.fr_RINV cx t m → W_LLVMFuzzerTestOneInput_drain_defs.dr_at_op cx m → W_LLVMFuzzerTestOneInput_drain_defs.dr_pick cx m si h → W_LLVMFuzzerTestOneInput_drain_defs.dr_nomatch m h (Z.of_nat (length (lm_es m))) ∨ (∃ j : nat, (j < length (lm_es m))%nat ∧ re_fd (nth j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0) = hs_fd h ∧ re_eof (nth j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0) = 1) → ReplyRINVB.fr_RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_drain_defs.dr_skip m (W_LLVMFuzzerTestOneInput_drain_defs.dr_k' cx m)).
Proof. intros rc fx. exact (@ExitB.bx_drain_skip rc). Qed.
(* ReplyBTop.v:140 RI_event_step *)
Lemma RI_event_step_btop : forall (rc : YM05.RunCeil) (fx : YK11.FPState), ∀ (cx : @lfcx rc) (t : Z) (m : lmod) (e : list byte) (v out' : Z), @ReplyRINVB.fr_RINV rc cx t m → 0 <= lm_k m < @c_n rc cx → lm_O m = [] → @in_byte rc cx (lm_k m) mod 10 = 7 → @W_LLVMFuzzerTestOneInput_arm_event.ev_evt rc cx m e → 0 <= v < 2 ^ 32 → @ReplyRINVB.fr_RINV rc cx (t + 1) (@W_LLVMFuzzerTestOneInput_arm_event.ev_step rc cx m e v out').
Proof. intros rc fx. exact (@ExitB.bx_event_step rc). Qed.

(* ================================================================== ReplyBTop.v:89 RI_exit_ends: FALSE for fr_RINV *)
(* lm_gn m = 2 (fr_RINV does not say lm_gn m is 0 or 1): relay_finish sends "a end\0" (6 bytes), and the check at
   gone <> 0 keeps the offset 0, so lx_ends_run gives Some 0, not Some 6 (a12 :271 RI_exit_ends_obl_false) *)
Lemma RI_exit_ends_btop_false : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @lfcx rc -> ¬ (forall (rc : YM05.RunCeil) (fx : YK11.FPState), ∀ (cx : @lfcx rc) (t : Z) (m : lmod), @ReplyRINVB.fr_RINV rc cx t m → (0 < @length rentry (lm_es m))%nat → W_bx_defs.lx_ends_run (lm_gn m) (W_bx_defs.lx_rf_O m) (W_bx_defs.lx_norder m) (W_bx_defs.lx_ord m) (lm_hs m) 0 = @Some Z (Z.of_nat (@length byte (W_bx_defs.lx_rf_O m)))).
Proof.
  intros rc fx cx0 Hobl.
  pose proof (Hobl rc fx _ _ _ (@ExitB.bx_RINV1 rc cx0 ExitB.bx_a 2 eq_refl ltac:(lia)) ltac:(cbn; lia)) as Hc.
  revert Hc. vm_compute. intros Hc. discriminate Hc.
Qed.
(* lm_gn m = 0 with a held text of one NUL byte (fr_RINV does not say the held texts have no NUL byte): the output
   starts with NUL, check_shape_ends' first line is empty and the check gives None (a12 :278
   RI_exit_ends_obl_false_nul) *)
Lemma RI_exit_ends_btop_false_nul : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @lfcx rc -> ¬ (forall (rc : YM05.RunCeil) (fx : YK11.FPState), ∀ (cx : @lfcx rc) (t : Z) (m : lmod), @ReplyRINVB.fr_RINV rc cx t m → (0 < @length rentry (lm_es m))%nat → W_bx_defs.lx_ends_run (lm_gn m) (W_bx_defs.lx_rf_O m) (W_bx_defs.lx_norder m) (W_bx_defs.lx_ord m) (lm_hs m) 0 = @Some Z (Z.of_nat (@length byte (W_bx_defs.lx_rf_O m)))).
Proof.
  intros rc fx cx0 Hobl.
  pose proof (Hobl rc fx _ _ _ (@ExitB.bx_RINV1 rc cx0 ExitB.bx_nul 0 eq_refl ltac:(lia)) ltac:(cbn; lia)) as Hc.
  revert Hc. vm_compute. intros Hc. discriminate Hc.
Qed.
(* the rule with the arm's premises (A's restated text, A top_x.v:461-466 at c0513fdca72, at B's names): lm_gn m is 0
   or 1 (agone_at in amodel_at, B W_rep.v), and the held texts have no NUL byte (a12 :1076 RI_exit_ends_holds) *)
Lemma RI_exit_ends_btop_restated : forall (rc : YM05.RunCeil) (fx : YK11.FPState), ∀ (cx : @lfcx rc) (t : Z) (m : lmod), @ReplyRINVB.fr_RINV rc cx t m → (0 < @length rentry (lm_es m))%nat → 0 <= lm_gn m <= 1 → (∀ (i : nat) (h : hsrc), @nth (option hsrc) i (lm_hs m) (@None hsrc) = @Some hsrc h → @Forall (Z * list byte) (fun r : Z * list byte => ¬ @In byte (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))) → W_bx_defs.lx_ends_run (lm_gn m) (W_bx_defs.lx_rf_O m) (W_bx_defs.lx_norder m) (W_bx_defs.lx_ord m) (lm_hs m) 0 = @Some Z (Z.of_nat (@length byte (W_bx_defs.lx_rf_O m))).
Proof. intros rc fx. exact (@ExitB.bx_exit_ends_restated rc). Qed.

(* ================================================================== ReplyBTop.v:99 RI_drain_step: FALSE for fr_RINV *)
(* B's dr_step_ok says nothing of the new entry's first padding: at re_pad1 e' = [] the new table breaks fr_entry_ok's
   `length (re_pad1 e) = 4%nat` (ReplyRINVB.v:165) *)
Lemma RI_drain_step_btop_false_pad : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @lfcx rc -> ¬ (forall (rc : YM05.RunCeil) (fx : YK11.FPState), ∀ (cx : @lfcx rc) (t : Z) (m : lmod) (si : nat) (h : hsrc) (j : nat) (e' : rentry) (h' : hsrc) (c' : ctl) (O' : list byte) (cap' out' ev' : Z) (LB : list byte) (E' H' : hlist), @ReplyRINVB.fr_RINV rc cx t m → @W_LLVMFuzzerTestOneInput_drain_defs.dr_at_op rc cx m → @W_LLVMFuzzerTestOneInput_drain_defs.dr_pick rc cx m si h → (j < @length rentry (lm_es m))%nat → re_fd (@nth rentry j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0) = hs_fd h → re_eof (@nth rentry j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0) = 0 → @W_LLVMFuzzerTestOneInput_drain_defs.dr_step_ok rc cx m si h j e' h' c' O' cap' out' ev' LB E' H' → @ReplyRINVB.fr_RINV rc cx (t + 1) (W_LLVMFuzzerTestOneInput_drain_defs.dr_step m (@W_LLVMFuzzerTestOneInput_drain_defs.dr_k' rc cx m) si (CheckRep.set_exp_held h' E' H') j e' c' O' cap' out')).
Proof.
  intros rc fx cx0 Hobl.
  pose proof (Hobl rc fx (ExitB.bx_cx cx0 10 ExitB.bx_pl2) 0 ExitB.bx_m0 0%nat ExitB.bx_h0 0%nat (ExitB.bx_e' [])
    ExitB.bx_h' ExitB.bx_c' ExitB.bx_O' ExitB.bx_cap' 0 0 [] ExitB.bx_E' (ExitB.bx_H' 8)
    (ExitB.bx_RINV0 cx0 ExitB.bx_pl2) (ExitB.bx_dat cx0) (ExitB.bx_dpick cx0) ltac:(cbn; lia) eq_refl eq_refl
    (ExitB.bx_dok _ [] 8)) as Hc.
  destruct Hc as (_ & (_ & _ & _ & Hent & _) & _ & _).
  change (Forall ReplyRINVB.fr_entry_ok [ExitB.bx_e' []]) in Hent.
  apply Forall_inv in Hent. destruct Hent as (_ & Hp1 & _). cbn in Hp1. discriminate Hp1.
Qed.
(* B's dr_step_ok says nothing of the held list's capacity after check_no_loss: at hl_cap H' = 2 ^ 24 the drained row
   breaks fr_pair_ok's `hl_cap (hs_held h) < 2 ^ 24` (ReplyRINVB.v:154) *)
Lemma RI_drain_step_btop_false_cap : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @lfcx rc -> ¬ (forall (rc : YM05.RunCeil) (fx : YK11.FPState), ∀ (cx : @lfcx rc) (t : Z) (m : lmod) (si : nat) (h : hsrc) (j : nat) (e' : rentry) (h' : hsrc) (c' : ctl) (O' : list byte) (cap' out' ev' : Z) (LB : list byte) (E' H' : hlist), @ReplyRINVB.fr_RINV rc cx t m → @W_LLVMFuzzerTestOneInput_drain_defs.dr_at_op rc cx m → @W_LLVMFuzzerTestOneInput_drain_defs.dr_pick rc cx m si h → (j < @length rentry (lm_es m))%nat → re_fd (@nth rentry j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0) = hs_fd h → re_eof (@nth rentry j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0) = 0 → @W_LLVMFuzzerTestOneInput_drain_defs.dr_step_ok rc cx m si h j e' h' c' O' cap' out' ev' LB E' H' → @ReplyRINVB.fr_RINV rc cx (t + 1) (W_LLVMFuzzerTestOneInput_drain_defs.dr_step m (@W_LLVMFuzzerTestOneInput_drain_defs.dr_k' rc cx m) si (CheckRep.set_exp_held h' E' H') j e' c' O' cap' out')).
Proof.
  intros rc fx cx0 Hobl.
  pose proof (Hobl rc fx (ExitB.bx_cx cx0 10 ExitB.bx_pl2) 0 ExitB.bx_m0 0%nat ExitB.bx_h0 0%nat
    (ExitB.bx_e' ExitB.bx_pad) ExitB.bx_h' ExitB.bx_c' ExitB.bx_O' ExitB.bx_cap' 0 0 [] ExitB.bx_E' (ExitB.bx_H' (2 ^ 24))
    (ExitB.bx_RINV0 cx0 ExitB.bx_pl2) (ExitB.bx_dat cx0) (ExitB.bx_dpick cx0) ltac:(cbn; lia) eq_refl eq_refl
    (ExitB.bx_dok _ ExitB.bx_pad (2 ^ 24))) as Hc.
  destruct Hc as (_ & (_ & _ & _ & _ & hj & HF & _) & _ & _).
  pose proof (ExitB.bx_F2_nth _ _ _ _ _ HF 0 W_LLVMFuzzerTestOneInput_drain_defs.dr_e0 (ExitB.bx_h0, 0%nat)
    ltac:(cbn; lia)) as Hp.
  remember (nth 0 hj (ExitB.bx_h0, 0%nat)) as p eqn:Ep. clear Ep. destruct p as [hp sp].
  destruct Hp as (Hs4 & Hn & _ & _ & _ & _ & _ & _ & Hhc & _). cbn [fst snd] in Hs4, Hn, Hhc.
  destruct sp as [|[|[|[|sp]]]]; cbn in Hn; try discriminate Hn; [|lia].
  injection Hn as <-. cbn in Hhc. lia.
Qed.
(* the rule with the four premises the B arm has at its call (drain_calls_x.v:3415): the t bound (dr_regs_call,
   drain_defs.v:197), the held / begin bound (LS_cnl_pre, top_x.v:362), the new entry's paddings (dr_post's
   aentry_ok e', W_contract.v:1002 with W_rep.v:125) and the held capacity (cnl_post, W_contract.v:2036) *)
Lemma RI_drain_step_btop_restated : forall (rc : YM05.RunCeil) (fx : YK11.FPState), ∀ (cx : @lfcx rc) (t : Z) (m : lmod) (si : nat) (h : hsrc) (j : nat) (e' : rentry) (h' : hsrc) (c' : ctl) (O' : list byte) (cap' out' ev' : Z) (LB : list byte) (E' H' : hlist), @ReplyRINVB.fr_RINV rc cx t m → 0 <= t < OPS_MAX → hl_n (hs_held h') + Z.of_nat (CheckRep.count_begin (CheckRep.texts (hs_expected h'))) < 2 ^ 22 → @W_LLVMFuzzerTestOneInput_drain_defs.dr_at_op rc cx m → @W_LLVMFuzzerTestOneInput_drain_defs.dr_pick rc cx m si h → (j < @length rentry (lm_es m))%nat → re_fd (@nth rentry j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0) = hs_fd h → re_eof (@nth rentry j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0) = 0 → @W_LLVMFuzzerTestOneInput_drain_defs.dr_step_ok rc cx m si h j e' h' c' O' cap' out' ev' LB E' H' → @length byte (re_pad1 e') = 4%nat → @length byte (re_pad2 e') = 4%nat → hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h')) (2 * (hl_n (hs_held h') + Z.of_nat (CheckRep.count_begin (CheckRep.texts (hs_expected h')))))) → @ReplyRINVB.fr_RINV rc cx (t + 1) (W_LLVMFuzzerTestOneInput_drain_defs.dr_step m (@W_LLVMFuzzerTestOneInput_drain_defs.dr_k' rc cx m) si (CheckRep.set_exp_held h' E' H') j e' c' O' cap' out').
Proof. intros rc fx. exact (@ExitB.bx_drain_step_restated rc). Qed.
