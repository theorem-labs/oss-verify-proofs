(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: helpers for the segments S20 (chain_clear), S23 (pin_clear) and S24 (quit) of
   the walk of verbs_receive on the ASan build of plugin-hostd/fuzz_command (lib/A/Prog/verbs_receive_iface.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdAddr CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c answer_c answer_code_c hand_back_c arg_i_c socket_send_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_live PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* ---------------------------------------------------------------------------------------------------------------
   The model's side of the three routes *)
Lemma vr_st_route : forall D, Verbs.toks D <> [] ->
  vr_st D = VRR.plan_at (VRR.route (Verbs.toks D)) atoi_a (Verbs.line D) (Verbs.toks D).
Proof.
intros D H. unfold vr_st, Verbs.receive. destruct (Verbs.toks D) as [|v args] eqn:E; [congruence|].
cbn [fst]. apply VRR.plan_route. discriminate.
Qed.

Ltac rt_chain H :=
  cbv beta iota in H;
  repeat (match type of H with context [if ?b then _ else _] => destruct b; cbv beta iota in H end); try discriminate H.

Lemma route_chclear_v : forall v args, VRR.route (v :: args) = VRR.RChclear -> v = Verbs.Lit.verb_chain_clear.
Proof.
intros v args H. apply Verbs.list_eqb_eq.
destruct (Verbs.list_eqb v Verbs.Lit.verb_chain_clear) eqn:Ecc; [reflexivity|exfalso].
unfold VRR.route, VRR.route_mid in H. rewrite Ecc in H. rt_chain H.
unfold VRR.route_tail, VRR.route_conn, VRR.route_cd in H.
destruct (Verbs.ledger_of v Verbs.Lit.instance_info_verbs); [discriminate H|].
destruct args as [|a [|b [|c rest]]]; try discriminate H; destruct (Verbs.is_instance_verb v); try discriminate H;
destruct (_ || _); discriminate H.
Qed.

Lemma route_pinclr_v : forall v args, VRR.route (v :: args) = VRR.RPinclr -> v = Verbs.Lit.verb_pin_clear.
Proof.
intros v args H. apply Verbs.list_eqb_eq.
destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_clear) eqn:Ecc; [reflexivity|exfalso].
unfold VRR.route, VRR.route_mid in H. rewrite Ecc in H. rt_chain H.
unfold VRR.route_tail, VRR.route_conn, VRR.route_cd in H.
destruct (Verbs.ledger_of v Verbs.Lit.instance_info_verbs); [discriminate H|].
destruct args as [|a [|b [|c rest]]]; try discriminate H; destruct (Verbs.is_instance_verb v); try discriminate H;
destruct (_ || _); discriminate H.
Qed.

Lemma route_quit_v : forall v args, (forall b, In b v -> bv_unsigned b <> 32 /\ bv_unsigned b <> 9) ->
  VRR.route (v :: args) = VRR.RQuit -> v = Verbs.Lit.verb_quit.
Proof.
intros v args Hv H.
assert (Hq : Verbs.verb_is_m v Verbs.Lit.fmt_quit = true).
{ destruct (Verbs.verb_is_m v Verbs.Lit.fmt_quit) eqn:Ecc; [reflexivity|exfalso].
  unfold VRR.route, VRR.route_mid in H. rewrite Ecc in H. rt_chain H.
  unfold VRR.route_tail, VRR.route_conn, VRR.route_cd in H.
  destruct (Verbs.ledger_of v Verbs.Lit.instance_info_verbs); [discriminate H|].
  destruct args as [|a [|b [|c rest]]]; try discriminate H; destruct (Verbs.is_instance_verb v); try discriminate H;
  destruct (_ || _); discriminate H. }
apply (proj1 (Verbs.verb_is_m_token v Verbs.Lit.fmt_quit Hv)) in Hq. rewrite Hq. reflexivity.
Qed.

Lemma ev_route_not_cp : forall R ln v args s,
  Verbs.list_eqb v Verbs.Lit.verb_chain = false -> Verbs.list_eqb v Verbs.Lit.verb_pin_set = false ->
  ev_route R ln (v :: args) s = ev_step R s.
Proof. intros R ln v args s H1 H2. unfold ev_route. rewrite H1, H2. reflexivity. Qed.

Lemma calls_pins_clear : forall R u, (length (r_calls (fst (pins_clear_m R u))) <= S (length (r_calls R)))%nat.
Proof.
intros R u. unfold pins_clear_m, rec_stub_code, rec_answer_code, rec_mix, rec_record, set_state, set_answer, set_calls, set_spill.
destruct (Nat.ltb _ 16); cbn [r_calls r_refuse r_code fst]; destruct (_ =? 0); cbn [r_calls fst]; rewrite ?length_app; cbn [length]; lia.
Qed.
Lemma calls_lv2 : forall R u, (length (r_calls (lv2_refusals_forget_m R u)) <= S (length (r_calls R)))%nat.
Proof.
intros R u. unfold lv2_refusals_forget_m, rec_stub_mix, rec_mix, rec_record, set_state, set_calls, set_spill.
destruct (Nat.ltb _ 16); cbn [r_calls]; rewrite ?length_app; cbn [length]; lia.
Qed.
Lemma calls_chain_clear : forall R i, (length (r_calls (fst (sup_chain_clear_m R i))) <= S (length (r_calls R)))%nat.
Proof.
intros R i. unfold sup_chain_clear_m, rec_stub, rec_answer, hand_back, rec_mix, rec_record, set_state, set_answer, set_calls, set_spill.
destruct (Nat.ltb _ 16); cbn [r_calls r_refuse fst]; destruct (_ =? 0); cbn [r_calls fst]; rewrite ?length_app; cbn [length]; lia.
Qed.
Lemma code_pins_clear : forall R u, snd (pins_clear_m R u) = 0 \/ snd (pins_clear_m R u) = r_code R.
Proof.
intros R u. unfold pins_clear_m, rec_stub_code, rec_answer_code, rec_mix, rec_record, set_state, set_answer, set_calls, set_spill.
destruct (Nat.ltb _ 16); cbn [r_calls r_refuse r_code fst snd]; destruct (_ =? 0); cbn [snd]; auto.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Lists of blocks *)
Lemma vr_nodup_app : forall (l1 l2 : list (Z * Z)), List.NoDup l1 -> List.NoDup l2 ->
  (forall x, In x l1 -> ~ In x l2) -> List.NoDup (l1 ++ l2).
Proof.
induction l1 as [|a l1 IH]; intros l2 H1 H2 Hd; [exact H2|]. cbn. apply List.NoDup_cons_iff in H1 as [Ha H1].
constructor.
- intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Ha Hin) | exact (Hd a (or_introl eq_refl) Hin)].
- apply IH; [exact H1 | exact H2 | intros x Hx; apply Hd; right; exact Hx].
Qed.
Lemma vr_nodup_app_r : forall (l1 l2 : list (Z * Z)), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof. induction l1 as [|a l1 IH]; intros l2 H; [exact H|]. cbn in H. apply List.NoDup_cons_iff in H as [_ H]. exact (IH _ H). Qed.
Lemma vr_nodup_app_dis : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
induction l1 as [|a l1 IH]; intros l2 x H Hx; [destruct Hx|]. cbn in H. apply List.NoDup_cons_iff in H as [Ha H].
destruct Hx as [<-|Hx]; [intros Hin; apply Ha; apply in_or_app; right; exact Hin | exact (IH _ _ H Hx)].
Qed.
Definition pz_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Definition inb (O : list (Z * Z)) (pn : Z * Z) : bool := if in_dec pz_eq_dec pn O then true else false.
Lemma inb_true : forall O pn, inb O pn = true <-> In pn O.
Proof. intros O pn. unfold inb. destruct (in_dec pz_eq_dec pn O); split; intros H; try discriminate; auto. Qed.
Lemma in_filter_inb : forall O l pn, In pn (List.filter (inb O) l) <-> In pn l /\ In pn O.
Proof. intros O l pn. rewrite filter_In, inb_true. tauto. Qed.
(* the live blocks after a recorder callee: those of the walk and of the entry's rest stay, the recorder's are
   the callee's O1, and the callee's new blocks (its text) are added *)
Lemma vr_perm_after : forall bl0 bl1 Oc O1 tmps rest new,
  List.NoDup bl0 -> List.NoDup bl1 -> Permutation bl0 (Oc ++ tmps ++ rest) ->
  (forall pn, In pn bl0 -> ~ In pn Oc -> In pn bl1) ->
  (forall pn, In pn bl1 -> (In pn bl0 /\ ~ In pn Oc) \/ In pn O1 \/ In pn new) ->
  (forall pn, In pn O1 -> In pn Oc \/ ~ In pn bl0) ->
  (forall pn, In pn new -> In pn bl1) ->
  List.NoDup new -> (forall pn, In pn new -> ~ In pn bl0 /\ ~ In pn O1) ->
  Permutation bl1 (List.filter (inb O1) bl1 ++ (new ++ tmps) ++ rest).
Proof.
intros bl0 bl1 Oc O1 tmps rest new Hn0 Hn1 HP Hk Hc HO1 Hnw Hnn Hnd.
assert (Hnd0 : List.NoDup (Oc ++ tmps ++ rest)) by exact (Permutation_NoDup HP Hn0).
assert (Hin0 : forall pn, In pn (tmps ++ rest) -> In pn bl0 /\ ~ In pn Oc).
{ intros pn Hpn. split; [apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hpn|].
  intros HO. exact (vr_nodup_app_dis _ _ pn Hnd0 HO Hpn). }
apply NoDup_Permutation.
- exact Hn1.
- rewrite <- app_assoc. apply vr_nodup_app; [apply List.NoDup_filter; exact Hn1|apply vr_nodup_app; [exact Hnn | exact (vr_nodup_app_r _ _ Hnd0)|]|].
  + intros x Hx Hx'. destruct (Hnd x Hx) as [Hx0 _]. exact (Hx0 (proj1 (Hin0 x Hx'))).
  + intros x Hx Hx'. apply in_filter_inb in Hx as [_ HxO]. apply in_app_or in Hx' as [Hx'|Hx'].
    * exact (proj2 (Hnd x Hx') HxO).
    * destruct (Hin0 x Hx') as [Hb HnO]. destruct (HO1 x HxO) as [H|H]; [exact (HnO H) | exact (H Hb)].
- intros x. rewrite <- app_assoc. rewrite !in_app_iff, in_filter_inb. split.
  + intros Hx. destruct (Hc x Hx) as [[Hb HnO]|[HO|Hw]].
    * right. right. assert (Hx' : In x (Oc ++ tmps ++ rest)) by exact (Permutation_in _ HP Hb).
      rewrite !in_app_iff in Hx'. tauto.
    * left. split; [exact Hx | exact HO].
    * right. left. exact Hw.
  + intros [[Hx _]|[Hw|Ht]]; [exact Hx | exact (Hnw x Hw) |].
    destruct (Hin0 x ltac:(apply in_app_iff; exact Ht)) as [Hb HnO]. exact (Hk x Hb HnO).
Qed.

(* vr_perm_after for a callee that may hand back, as its new block, the address and size of a recorder block it
   freed: a new block is none of the walk's or the rest's blocks *)
Lemma vk_perm_after : forall bl0 bl1 Oc O1 tmps rest new,
  List.NoDup bl0 -> List.NoDup bl1 -> Permutation bl0 (Oc ++ tmps ++ rest) ->
  (forall pn, In pn bl0 -> ~ In pn Oc -> In pn bl1) ->
  (forall pn, In pn bl1 -> (In pn bl0 /\ ~ In pn Oc) \/ In pn O1 \/ In pn new) ->
  (forall pn, In pn O1 -> In pn Oc \/ ~ In pn bl0) ->
  (forall pn, In pn new -> In pn bl1) ->
  List.NoDup new -> (forall pn, In pn new -> (In pn bl0 -> In pn Oc) /\ ~ In pn O1) ->
  Permutation bl1 (List.filter (inb O1) bl1 ++ (new ++ tmps) ++ rest).
Proof.
intros bl0 bl1 Oc O1 tmps rest new Hn0 Hn1 HP Hk Hc HO1 Hnw Hnn Hnd.
assert (Hnd0 : List.NoDup (Oc ++ tmps ++ rest)) by exact (Permutation_NoDup HP Hn0).
assert (Hin0 : forall pn, In pn (tmps ++ rest) -> In pn bl0 /\ ~ In pn Oc).
{ intros pn Hpn. split; [apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hpn|].
  intros HO. exact (vr_nodup_app_dis _ _ pn Hnd0 HO Hpn). }
apply NoDup_Permutation.
- exact Hn1.
- rewrite <- app_assoc. apply vr_nodup_app; [apply List.NoDup_filter; exact Hn1|apply vr_nodup_app; [exact Hnn | exact (vr_nodup_app_r _ _ Hnd0)|]|].
  + intros x Hx Hx'. destruct (Hnd x Hx) as [Hx0 _]. destruct (Hin0 x Hx') as [Hb HnO]. exact (HnO (Hx0 Hb)).
  + intros x Hx Hx'. apply in_filter_inb in Hx as [_ HxO]. apply in_app_or in Hx' as [Hx'|Hx'].
    * exact (proj2 (Hnd x Hx') HxO).
    * destruct (Hin0 x Hx') as [Hb HnO]. destruct (HO1 x HxO) as [H|H]; [exact (HnO H) | exact (H Hb)].
- intros x. rewrite <- app_assoc. rewrite !in_app_iff, in_filter_inb. split.
  + intros Hx. destruct (Hc x Hx) as [[Hb HnO]|[HO|Hw]].
    * right. right. assert (Hx' : In x (Oc ++ tmps ++ rest)) by exact (Permutation_in _ HP Hb).
      rewrite !in_app_iff in Hx'. tauto.
    * left. split; [exact Hx | exact HO].
    * right. left. exact Hw.
  + intros [[Hx _]|[Hw|Ht]]; [exact Hx | exact (Hnw x Hw) |].
    destruct (Hin0 x ltac:(apply in_app_iff; exact Ht)) as [Hb HnO]. exact (Hk x Hb HnO).
Qed.

(* the text of a recorder stub is at most 28 bytes (the plain proof's stub_text_len) *)
Lemma vk_stub_len : forall R fn As v ch, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_stub R fn As (shape_of v) ch)) <= 28)%nat.
Proof.
intros R fn As v ch HC. unfold rec_stub. rewrite rec_answer_text.
assert (E : r_code (rec_record R fn As) = r_code R) by (unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
destruct (r_refuse (rec_record R fn As) =? 0).
- exact (proj1 (proj2 (shape_of_facts v))).
- rewrite E. pose proof (resp_length (r_code R) HC). lia.
Qed.

(* the value `lw` loads from a 4-byte cell holding v mod 2^32 *)
Lemma vk_lw_val : forall v, -2^31 <= v < 2^31 ->
  sext 64 (bv_extract 0 32 (Z_to_bv 64 (v mod 2^32))) = Z_to_bv 64 v.
Proof.
intros v Hv. rewrite <- (sext32_small v Hv).
pose proof (zext_low_sound true 32 (v mod 2^32)) as H1. pose proof (zext_low_sound true 32 v) as H2.
cbv beta iota in H1, H2. rewrite H1, H2. f_equal. unfold zext_low, zcanon, M64. cbv zeta.
change (Z.of_N 32) with 32.
rewrite (Z.mod_small (v mod 2^32) (2^64)) by (pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)); lia).
rewrite Zmod_mod. rewrite (Z.mod_mod_divide v (2^64) (2^32)) by (exists (2^32); reflexivity).
reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma aval_val_mem : forall (H : word -> bool) mem a n v, aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte SEGS H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.

Lemma cmd_got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [H _]. unfold cmd_ro_bytes in H.
repeat lazymatch type of H with
| abytes_atR _ _ RO_ptr_a7068 /\ _ => fail
| _ /\ _ => apply proj2 in H
end.
destruct H as (H1 & H2 & H3 & H4).
unfold cmd_got_ok, aval_mem.
split; [|split; [|split]]; intros k Hk;
[rewrite (H1 k) | rewrite (H2 k) | rewrite (H3 k) | rewrite (H4 k)]; try (cbn; lia);
do 8 (destruct k as [|k]; [reflexivity|]); lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis MTL : ameter_laws MT.

Lemma ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof. intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]. Qed.

Lemma aro_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall a, in_roP SEGS RLO RHI a -> ~ inFP FP a) -> ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HFP Hso HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a (ro_img a Hro) Ho He (fp_spares_closed FP a Hso (HFP a Hro))). exact (HR a Hro Ho He).
Qed.

Lemma aro_agree : forall rd rd', arodata_okP SEGS RLO RHI B rd -> (forall a, in_roP SEGS RLO RHI a -> rd' a = rd a) ->
  arodata_okP SEGS RLO RHI B rd'.
Proof. intros rd rd' H Hk a Hro Ho He. rewrite (Hk a Hro). exact (H a Hro Ho He). Qed.

Lemma vr_env_of : forall ly S W mem md, AR SEGS B ly S W mem md -> arodata_okP SEGS RLO RHI B (rdW W mem) ->
  vr_env B W mem.
Proof.
intros ly S W mem md HAR Haro. pose proof (ROA ly S W mem md HAR Haro) as Hro.
destruct (RECC ly S W mem md HAR) as (Hf & Hg & He).
split; [exact Haro|]. split; [exact (cmd_got_of_ro _ Hro)|]. split; [exact Hro|]. split; [exact Hg|]. split; [exact Hf | exact He].
Qed.

Definition rec_fp (O : list (Z * Z)) : list (Z * Z) :=
  (A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma rec_fp_inv : forall O a, inFP (rec_fp O) a ->
  inFP cmd_PG a \/ exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a Ha. unfold rec_fp in Ha. apply inFP_cons in Ha as [Ha|Ha].
- left. unfold cmd_PG. apply inFP_cons. left. unfold REC_SIZE in Ha. exact Ha.
- apply inFP_cons in Ha as [Ha|Ha].
  + left. unfold cmd_PG. apply inFP_cons. right. apply inFP_cons. left. unfold SC_SIZE in Ha. exact Ha.
  + right. exact (inFP_ablocks_fp_inv O a Ha).
Qed.

Lemma rec_fp_not_ro : forall ly S W mem md O, AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  forall a, in_roP SEGS RLO RHI a -> ~ inFP (rec_fp O) a.
Proof.
intros ly S W mem md O HAR HO a Hro Ha. destruct (rec_fp_inv O a Ha) as [Hpg | (p & n & Hpn & Hr)].
- exact (RPG a Hpg Hro).
- exact (blk_img SEGS B LAWS _ _ _ _ _ p n a HAR (HO _ Hpn) Hr (ro_img a Hro)).
Qed.

Lemma rec_fp_closed : forall ly S W mem md O, AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  ~ YI16.sink_open_fp (rec_fp O).
Proof.
intros ly S W mem md O HAR HO. unfold rec_fp.
apply sink_closed_cons; [cbn; unfold A_G_REC; lia|]. apply sink_closed_cons; [cbn; unfold A_REC_SPILL; lia|].
apply sink_closed_ablocks_fp. apply Forall_forall. intros [p n] Hpn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & H4 & _). cbn. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The walk's own memory: the real frame's saves and spills, the side-stack frame and its shadow, the line and copy
   blocks. Every piece of vr_core and of the boundary that reads memory reads only these bytes, besides the recorder's
   statics and blocks, g_quitting and the read-only image. *)
Definition vr_wrange (e : vrE) (F q c a : Z) : Prop :=
  (vr_s1 e <= a < vr_s1 e + 80) \/ (vr_sp0 e - 104 <= a < vr_sp0 e) \/
  (F <= a < F + 1024) \/ (shadow_addr F <= a < shadow_addr F + 128) \/
  (q <= a < q + req_size (vr_l (e_n e) (e_D e) + 1)) \/
  (c <= a < c + req_size (Z.of_nat (length (Verbs.line (e_D e))) + 1)).
Definition vr_wkeep (e : vrE) (F q c : Z) (rd rd' : reader) : Prop := forall a, vr_wrange e F q c a -> rd' a = rd a.

Lemma vr_s1_bounds : forall e, vr_sp0 e - 224 < vr_s1 e <= vr_sp0 e - 192 /\ vr_s1 e mod 32 = 0.
Proof.
intros e. unfold vr_s1. pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as Hm.
split.
- generalize dependent ((vr_sp0 e - 192) mod 32). intros X HX. lia.
- rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity.
Qed.
Lemma vr_s1_ge : forall e, vr_sp0 e mod 16 = 0 -> vr_sp0 e - 208 <= vr_s1 e /\ (vr_s1 e - vr_sp0 e) mod 16 = 0.
Proof.
intros e H16. unfold vr_s1.
assert (E : exists m, vr_sp0 e = 16 * m) by (exists (vr_sp0 e / 16); pose proof (Z.div_mod (vr_sp0 e) 16 ltac:(lia)); lia).
destruct E as [m Em]. rewrite Em.
replace (16 * m - 192) with (16 * (m - 12)) by lia.
change 32 with (16 * 2). rewrite (Z.mul_mod_distr_l (m - 12) 2 16) by lia.
pose proof (Z.mod_pos_bound (m - 12) 2 ltac:(lia)) as Hb.
generalize dependent ((m - 12) mod 2). intros X HX. split; [lia|].
replace (16 * (m - 12) - 16 * X - 16 * m) with ((-12 - X) * 16) by lia. apply Z.mod_mul. lia.
Qed.

Lemma vr_find_byte_upto0 : forall D, match StrFun.find_byte 0 D with Some i => firstn i D | None => D end = Verbs.upto0 D.
Proof.
unfold Verbs.upto0. induction D as [|x D IH]; [reflexivity|]. cbn [StrFun.find_byte Verbs.upto].
destruct (bv_unsigned x =? 0); [reflexivity|].
destruct (StrFun.find_byte 0 D) as [i|]; cbn [firstn]; f_equal; exact IH.
Qed.
Lemma vr_strnlen_upto : forall D, StrFun.strnlen_res (Z.of_nat (length D)) D = Z.of_nat (length (Verbs.upto0 D)).
Proof.
intros D. pose proof (vr_find_byte_upto0 D) as E. unfold StrFun.strnlen_res. rewrite Nat2Z.id, firstn_all.
destruct (StrFun.find_byte 0 D) as [i|] eqn:F.
- destruct (StrFun.find_byte_Some _ _ _ F) as (Hl & _). rewrite <- E, length_firstn. lia.
- rewrite <- E. reflexivity.
Qed.

Lemma vr_line_le : forall e, Z.of_nat (length (e_D e)) = e_n e ->
  Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e).
Proof.
intros e Hn. unfold vr_l. rewrite <- Hn. rewrite vr_strnlen_upto.
unfold Verbs.line, Verbs.trim. rewrite length_rev.
pose proof (verbs_receive_route.dropw_len Verbs.is_trail (rev (Verbs.upto0 (e_D e)))) as H. rewrite length_rev in H. lia.
Qed.

Lemma vr_saved_keep : forall e F q c W mem W' mem', vr_wkeep e F q c (rdW W mem) (rdW W' mem') ->
  vr_saved e W mem -> vr_saved e W' mem'.
Proof.
intros e F q c W mem W' mem' HK HS j r Hj. apply (aval_mem_agree _ _ _ 8 _ (HS j r Hj)).
assert (Hjl : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
cbn [length vr_saved_regs] in Hjl.
intros k Hk. apply HK. right; left. pose proof (vr_s1_bounds e). change (Z.of_nat 8) with 8 in Hk. lia.
Qed.

Lemma vr_spill_keep : forall e F q c W mem W' mem' sl, vr_wkeep e F q c (rdW W mem) (rdW W' mem') ->
  Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 80) sl -> vr_spill e W mem sl -> vr_spill e W' mem' sl.
Proof.
intros e F q c W mem W' mem' sl HK Hsl HS. unfold vr_spill in *. rewrite Forall_forall in *. intros ov Hov.
apply (aval_mem_agree _ _ _ 8 _ (HS ov Hov)). intros k Hk. apply HK. left.
pose proof (Hsl ov Hov). change (Z.of_nat 8) with 8 in Hk. lia.
Qed.

Lemma vr_sl3_ok : forall F q c, Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 80) (vr_sl3 F q c).
Proof. intros F q c. unfold vr_sl3. repeat constructor; cbn; lia. Qed.

Lemma vr_frame_keep : forall e q c lyc ly' W mem W' mem' pos F sh, ly_F ly' = ly_F lyc ->
  vr_wkeep e F q c (rdW W mem) (rdW W' mem') -> vr_frame lyc W mem pos F sh -> vr_frame ly' W' mem' pos F sh.
Proof.
intros e q c lyc ly' W mem W' mem' pos F sh EF HK (HF & Hfl & Hsh). unfold vr_frame.
assert (E1 : frame_addr ly' 4 pos = frame_addr lyc 4 pos) by (unfold frame_addr; rewrite EF; reflexivity).
assert (E2 : flag_addr ly' 4 pos = flag_addr lyc 4 pos) by (unfold flag_addr; rewrite EF; reflexivity).
split; [rewrite E1; exact HF|]. split.
- rewrite E2, <- Hfl. apply rdword_ext. intros k Hk. apply HK. right; right; left. lia.
- intros i Hi. rewrite <- (Hsh i Hi). apply HK. right; right; right; left. lia.
Qed.

Lemma vr_line_keep : forall e F q c W mem W' mem', Z.of_nat (length (e_D e)) = e_n e ->
  vr_wkeep e F q c (rdW W mem) (rdW W' mem') -> vr_line B e q W mem -> vr_line B e q W' mem'.
Proof.
intros e F q c W mem W' mem' Hn HK [Hf Hs]. split; [exact Hf|].
apply (astr_atR_agree _ _ q _ (Z.of_nat (length (Verbs.line (e_D e))) + 1) Hs); [lia|].
intros k Hk. apply HK. right; right; right; right; left.
pose proof (vr_line_le e Hn). pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [_ Hr]. lia.
Qed.

Lemma vr_copy_keep : forall e F q c tp W mem W' mem', vr_wkeep e F q c (rdW W mem) (rdW W' mem') ->
  vr_copy B e F c tp W mem -> vr_copy B e F c tp W' mem'.
Proof.
intros e F q c tp W mem W' mem' HK [Hf (H1 & H2 & H3 & H4)]. split; [exact Hf|]. split; [exact H1|]. split; [exact H2|].
pose proof (Verbs.toks_length (e_D e)) as HL. split.
- intros i p Hi. apply (aval_mem_agree _ _ _ 8 _ (H3 i p Hi)).
  assert (Hil : (i < length tp)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  intros k Hk. apply HK. right; right; left. change (Z.of_nat 8) with 8 in Hk. lia.
- intros i p w Hi Hw. destruct (H4 i p w Hi Hw) as (A1 & A2 & A3 & A4).
  split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
  apply (astr_atR_agree _ _ p w (Z.of_nat (length w) + 1) A1); [lia|].
  intros k Hk. apply HK. right; right; right; right; right.
  pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [_ Hr]. lia.
Qed.

(* across a callee whose footprint avoids the walk's own memory *)
Lemma vr_wkeep_call : forall e pos F q c lyc Sc (Wc : world SEGS) memc mdc STK1 FP1 ly2 S2 W2 mem2 md2 k1,
  ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
  In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos ->
  In (vr_lb e q) (ablocks B lyc Sc) -> In (vr_lb e q) (ablocks B ly2 S2) ->
  In (vr_cb e c) (ablocks B lyc Sc) -> In (vr_cb e c) (ablocks B ly2 S2) ->
  alloc_ceiling <= vr_s1 e -> vr_sp0 e <= 2 ^ 64 ->
  (forall a, inFP FP1 a -> vr_wrange e F q c a -> False) ->
  vr_wkeep e F q c (rdW Wc memc) (rdW W2 mem2).
Proof.
intros e pos F q c lyc Sc Wc memc mdc STK1 FP1 ly2 S2 W2 mem2 md2 k1 HJ Hfr EF Hl1 Hl2 Hc1 Hc2 Hs1 Hsp HD a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _ & G4 & _).
assert (HnF : ~ inFP FP1 a) by (intros Hf; exact (HD a Hf Ha)).
pose proof (vr_s1_bounds e) as Hb.
assert (E4 : fs_frame_bytes 4 = 1024) by reflexivity.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
- apply G1; [lia | lia | exact HnF].
- apply G1; [lia | lia | exact HnF].
- apply (G4 4 pos a Hfr); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite <- EF, E4; lia | exact HnF].
- apply (G4 4 pos a Hfr); [right; unfold in_zr; cbn [fst snd]; rewrite <- EF, E4; change (1024 / 8) with 128; lia | exact HnF].
- unfold vr_lb in Hl1, Hl2. replace a with (q + (a - q)) by lia.
  apply (G2 q _ (a - q) Hl1 Hl2); [lia | replace (q + (a - q)) with a by lia; exact HnF].
- unfold vr_cb in Hc1, Hc2. replace a with (c + (a - c)) by lia.
  apply (G2 c _ (a - c) Hc1 Hc2); [lia | replace (c + (a - c)) with a by lia; exact HnF].
Qed.

Lemma vr_keep_trans : forall e F q c rd1 rd2 rd3, vr_wkeep e F q c rd1 rd2 -> vr_wkeep e F q c rd2 rd3 -> vr_wkeep e F q c rd1 rd3.
Proof. intros e F q c rd1 rd2 rd3 H12 H23 a Ha. rewrite (H23 a Ha). exact (H12 a Ha). Qed.

(* the walk's memory lies apart from the recorder's statics and blocks *)
Lemma vr_rec_fp_apart : forall e pos F q c lyc Sc Wc memc mdc Oc tmps,
  AR SEGS B lyc Sc Wc memc mdc -> In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos ->
  Permutation (ablocks B lyc Sc) (Oc ++ tmps ++ e_rest e) -> In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
  alloc_ceiling <= vr_s1 e ->
  forall a, inFP (rec_fp Oc) a -> vr_wrange e F q c a -> False.
Proof.
intros e pos F q c lyc Sc Wc memc mdc Oc tmps HAR Hfr EF HP Hl Hc Hs1 a Ha Hw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vr_s1_bounds e) as Hb.
assert (Hnd : List.NoDup (Oc ++ tmps ++ e_rest e)) by exact (Permutation_NoDup HP (verbs_receive_live.vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR)).
assert (Hinb : forall pn, In pn (Oc ++ tmps ++ e_rest e) -> In pn (ablocks B lyc Sc)) by (intros pn Hpn; exact (Permutation_in _ (Permutation_sym HP) Hpn)).
assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc)) by (apply Hinb; apply in_or_app; right; apply in_or_app; left; exact Hl).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)) by (apply Hinb; apply in_or_app; right; apply in_or_app; left; exact Hc).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hfr) as (Hf0 & Hfc & Hfapp).
assert (E4 : fs_frame_bytes 4 = 1024) by reflexivity. rewrite E4 in Hfc. rewrite <- EF in Hf0, Hfc.
pose proof (shadow_addr_bounds F ltac:(lia)) as Hsh.
destruct (rec_fp_inv Oc a Ha) as [Hpg | (p & n & Hpn & Hr)].
- destruct (PROGU a Hpg) as (Himg & _ & _). pose proof (pa_img_range a Himg) as Hia.
  destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]; try lia.
  + apply (frm_img SEGS B LAWS _ _ _ _ _ 4 pos a HAR Hfr); [rewrite <- EF, E4; lia | exact Himg].
  + apply (blk_img SEGS B LAWS _ _ _ _ _ q _ a HAR Hlb); [cbn [fst snd]; lia | exact Himg].
  + apply (blk_img SEGS B LAWS _ _ _ _ _ c _ a HAR Hcb); [cbn [fst snd]; lia | exact Himg].
- assert (Hpb : In (p, n) (ablocks B lyc Sc)) by (apply Hinb; apply in_or_app; left; exact Hpn).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpb) as (_ & Hp4 & Hpc & Hpapp & _).
  destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]; try lia.
  + pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ p n 4 pos HAR Hpb Hfr) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite <- EF, E4 in D. lia.
  + apply (fshadow_not_app F 128 p (req_size n) a); [lia | lia | exact Hpapp | unfold shadow_addr, SHADOW_OFF in Hw; lia | lia].
  + assert (Hne : (p, n) <> vr_lb e q).
    { intros E. apply (vr_nodup_app_dis _ _ (p, n) Hnd Hpn). rewrite E. apply in_or_app. left. exact Hl. }
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ p n _ _ HAR Hpb Hlb Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
  + assert (Hne : (p, n) <> vr_cb e c).
    { intros E. apply (vr_nodup_app_dis _ _ (p, n) Hnd Hpn). rewrite E. apply in_or_app. left. exact Hc. }
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ p n _ _ HAR Hpb Hcb Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* number's footprint, the result cell s1+84 of this frame, lies apart from the walk's own memory *)
Lemma vr_out_apart : forall e pos F q c lyc Sc Wc memc mdc Oc tmps,
  AR SEGS B lyc Sc Wc memc mdc -> In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos ->
  Permutation (ablocks B lyc Sc) (Oc ++ tmps ++ e_rest e) -> In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
  alloc_ceiling <= vr_s1 e ->
  forall a, inFP [(vr_s1 e + 84, vr_s1 e + 84 + 4)] a -> vr_wrange e F q c a -> False.
Proof.
intros e pos F q c lyc Sc Wc memc mdc Oc tmps HAR Hfr EF HP Hl Hc Hs1 a Ha Hw.
apply inFP_cons in Ha as [Ha | Ha]; [|exact (inFP_nil a Ha)].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (vr_s1_bounds e) as Hb.
assert (Hinb : forall pn, In pn (Oc ++ tmps ++ e_rest e) -> In pn (ablocks B lyc Sc)) by (intros pn Hpn; exact (Permutation_in _ (Permutation_sym HP) Hpn)).
assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc)) by (apply Hinb; apply in_or_app; right; apply in_or_app; left; exact Hl).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)) by (apply Hinb; apply in_or_app; right; apply in_or_app; left; exact Hc).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hfr) as (Hf0 & Hfc & Hfapp).
assert (E4 : fs_frame_bytes 4 = 1024) by reflexivity. rewrite E4 in Hfc. rewrite <- EF in Hf0, Hfc.
pose proof (shadow_addr_bounds F ltac:(lia)) as Hsh.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hlb) as (_ & _ & Hlc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & _ & Hcc & _).
unfold vr_lb, vr_cb in *; cbn [fst snd] in *.
destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]; lia.
Qed.

(* bytes the callee leaves: those of the image it does not hold, the blocks it does not hold, the stack above it *)
Lemma img_kept_call : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 a,
  ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
  inFP cmd_PG a -> ~ inFP FP1 a -> ~ YI16.sink_open_fp FP1 ->
  rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 a HJ Hpg HnF Hso.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _).
destruct (PROGU a Hpg) as (Himg & Ho & He). exact (G3 a Himg Ho He (fp_spares_closed FP1 a Hso HnF)).
Qed.

Lemma gq_kept_call : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 v,
  ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
  (forall a, inFP FP1 a -> ~ (A_G_QUITTING <= a < A_G_QUITTING + 4)) -> ~ YI16.sink_open_fp FP1 ->
  aval_mem (rdW Wc memc) A_G_QUITTING 4 v -> aval_mem (rdW W2 mem2) A_G_QUITTING 4 v.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 v HJ HF Hso Hv.
apply (aval_mem_agree _ _ _ 4 _ Hv). intros k Hk. change (Z.of_nat 4) with 4 in Hk.
apply (img_kept_call STK1 sp1 FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1); [exact HJ | | | exact Hso].
- unfold cmd_PG. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. left. unfold A_G_QUITTING. lia.
- intros Hf. exact (HF _ Hf ltac:(lia)).
Qed.

Lemma rec_kept_call : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 R O,
  ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
  (forall a, inFP FP1 a -> ~ inFP cmd_PG a) -> ~ YI16.sink_open_fp FP1 ->
  (forall p n i, In (p, n) O -> 0 <= i < req_size n -> ~ inFP FP1 (p + i)) ->
  (forall pn, In pn O -> In pn (ablocks B ly2 S2)) ->
  rec_repA B lyc Sc (rdW Wc memc) R O -> rec_repA B ly2 S2 (rdW W2 mem2) R O.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 R O HJ HFP Hso HFO HO2 HR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
apply (rec_repA_agree B _ _ _ _ _ _ R O HR).
- intros pn Hpn _. exact (HO2 pn Hpn).
- intros k Hk. assert (Hpg : inFP cmd_PG (A_G_REC + k)) by (unfold cmd_PG; apply inFP_cons; left; unfold REC_SIZE in Hk; lia).
  apply (img_kept_call STK1 sp1 FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 _ HJ Hpg); [intros Hf; exact (HFP _ Hf Hpg) | exact Hso].
- intros k Hk. assert (Hpg : inFP cmd_PG (A_REC_SPILL + k)).
  { unfold cmd_PG; apply inFP_cons; right; apply inFP_cons; left; unfold SC_SIZE in Hk; unfold A_REC_SPILL; lia. }
  apply (img_kept_call STK1 sp1 FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 _ HJ Hpg); [intros Hf; exact (HFP _ Hf Hpg) | exact Hso].
- intros [p n] Hpn k Hk. cbn [fst snd] in *.
  assert (Hb : In (p, n) (ablocks B lyc Sc)) by exact (rec_repA_in_blocks B _ _ _ _ _ _ HR Hpn).
  pose proof (req_size_pos n ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ) (HO2 _ Hpn)) as (_ & _ & _ & _ & _ & _ & Hn); lia)) as [_ Hr].
  apply (G2 p n k Hb (HO2 _ Hpn)); [lia | exact (HFO p n k Hpn ltac:(lia))].
Qed.

(* the memory above this function's frame is the entry's: the journal keeps every byte outside the window that the
   footprint does not hold, and the footprint lies below the allocator's ceiling *)
Lemma vr_fp_low : forall e, vr_ent B MT e -> forall a, inFP (vr_fp e) a -> a < alloc_ceiling.
Proof.
intros e He a Ha. pose proof asan_consts as (C1 & _).
destruct He as ((HAR & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREC & _).
unfold vr_fp in Ha. destruct Ha as (r & Hr & Hra). apply in_app_or in Hr as [Hr|Hr].
- unfold VERBS_RECEIVE_PG in Hr. cbn in Hr. unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, REC_SIZE, SC_SIZE in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hra; lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). cbn [fst snd] in Hra.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (rec_repA_in_blocks B _ _ _ _ _ _ HREC Hpn)) as (_ & _ & Hc & _). lia.
Qed.

Lemma vr_above : forall e lyc Sc (Wc : world SEGS) memc mdc k pos,
  vr_ent B MT e ->
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc Wc memc mdc k ->
  forall a, vr_sp0 e <= a < 2 ^ 64 -> rdW Wc memc a = rdW (e_W e) (e_mem e) a.
Proof.
intros e lyc Sc Wc memc mdc k pos He HJ a Ha.
apply (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Ha).
intros Hf. pose proof (vr_fp_low e He a Hf). destruct He as ((_ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & _) & _) & _).
unfold vr_sp0 in Ha. lia.
Qed.

(* the frame chain at a call: s0 holds this function's sp0, whose saved ra and s0 the prologue stored *)
Lemma vr_achain : forall e lyc (Wc : world SEGS) memc,
  vr_ent B MT e -> ly_top lyc = ly_top (e_ly e) ->
  (forall a, vr_sp0 e <= a < 2 ^ 64 -> rdW Wc memc a = rdW (e_W e) (e_mem e) a) ->
  vr_saved e Wc memc -> exists ch1, achain lyc (rdW Wc memc) (vr_s1 e) (vr_sp0 e) ch1.
Proof.
intros e lyc Wc memc He Etop Habove HS.
destruct He as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (vr_s1_bounds e) as Hb. pose proof asan_consts as (C1 & _).
destruct (Z_lt_ge_dec (vr_sp0 e) (ly_top lyc - 16)) as [Hlt | Hge].
- assert (Hw0 : rdword (rdW Wc memc) (vr_sp0 e - 8) = Some (raZ (e_regs e))).
  { apply rdword_of_val_mem; [|unfold raZ; apply bv_unsigned_in_range].
    apply aval_val_mem. pose proof (HS 0%nat 1 eq_refl) as H0.
    assert (E0 : vr_sp0 e - 8 - 8 * Z.of_nat 0 = vr_sp0 e - 8) by lia. rewrite E0 in H0. exact H0. }
  assert (Hw1 : rdword (rdW Wc memc) (vr_sp0 e - 16) = Some (s0Z (e_regs e))).
  { apply rdword_of_val_mem; [|unfold s0Z; apply bv_unsigned_in_range].
    apply aval_val_mem. pose proof (HS 1%nat 8 eq_refl) as H1.
    assert (E1 : vr_sp0 e - 8 - 8 * Z.of_nat 1 = vr_sp0 e - 16) by lia. rewrite E1 in H1. exact H1. }
  exists ((vr_sp0 e, raZ (e_regs e), s0Z (e_regs e)) :: e_ch e).
  apply (achain_ly_top (e_ly e) lyc); [exact Etop|].
  apply (achain_push (e_ly e) (rdW (e_W e) (e_mem e)) (rdW Wc memc) (vr_sp0 e) (s0Z (e_regs e)) (raZ (e_regs e)) (e_ch e) (vr_s1 e)).
  + exact Hch.
  + lia.
  + exact Habove.
  + exact Hw0.
  + exact Hw1.
  + exact Hra4.
  + unfold vr_sp0. lia.
  + unfold vr_sp0. rewrite <- Z.mod_mod_divide with (b := 16) by (try exists 2; lia). rewrite Hal16. reflexivity.
  + rewrite <- Etop. exact Hlt.
  + lia.
- exists []. left. split; [right; left; lia | reflexivity].
Qed.

Hypothesis HB : AF0m.CmdBSyms B.
(* the walk's own store into g_quitting: a program static its footprint holds *)
Lemma gq_awr : forall e STK sp0 bl0 blc fr0 ly own a, A_G_QUITTING <= a < A_G_QUITTING + 4 ->
  awr_byte SEGS B STK sp0 (vr_fp e) bl0 blc fr0 ly own a.
Proof.
intros e STK sp0 bl0 blc fr0 ly own a Ha. right; right; right; right; left.
assert (Hpg : inFP cmd_PG a) by (unfold cmd_PG; apply inFP_cons; right; apply inFP_cons; right; apply inFP_cons; left; exact Ha).
split; [|split].
- exists (A_G_QUITTING, A_G_QUITTING + 4). split; [|exact Ha].
  unfold vr_fp, VERBS_RECEIVE_PG. apply in_or_app. left. right. right. left. reflexivity.
- rewrite (AF0m.ts_prog B HB). unfold AF0m.TFIB_PROG_STATIC. apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
  unfold in_zr. cbn [fst snd]. unfold A_G_QUITTING in Ha. lia.
- exact (proj1 (PROGU a Hpg)).
Qed.

(* ===============================================================================================================
   The steps of S20, S23 and S24: a boundary state across a symbolic run and across a program call, and the call
   rule over cl_callS_wide (PaNoChain.v) *)
Lemma vk_rv_get : forall regs l r v, vr_rv regs l -> In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs l r v H Hin. unfold vr_rv in H. rewrite Forall_forall in H. exact (H (r, v) Hin). Qed.

Lemma vk_rv_kept : forall (regs regs' : bvmap 5 word) l,
  vr_rv regs l -> (forall r v, In (r, v) l -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) -> vr_rv regs' l.
Proof.
intros regs regs' l H Hk. unfold vr_rv in *. rewrite Forall_forall in *. intros [r v] Hin. cbn [fst snd].
rewrite (Hk r v Hin). exact (H (r, v) Hin).
Qed.

(* the registers after a callee: the callee-saved ones of the call, and a0 *)
Lemma vk_rv_after : forall e (regs regs2 : bvmap 5 word) rl rl' t,
  aregs_preserved regs regs2 -> vr_rv regs (vr_base B e ++ rl) -> getr regs2 10 = w64 t ->
  (forall r v, In (r, v) rl' -> (r = 10 /\ v = t) \/ (acallee_saved r /\ In (r, v) rl)) ->
  vr_rv regs2 (vr_base B e ++ rl').
Proof.
intros e regs regs2 rl rl' t HP Hrv H10 Hrl. unfold vr_rv. apply Forall_app. split.
- apply Forall_forall. intros [r v] Hin. cbn [fst snd].
  assert (Hcs : acallee_saved r).
  { unfold vr_base in Hin. cbn [In] in Hin. unfold acallee_saved.
    destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _; lia. }
  rewrite (HP r Hcs). apply (vk_rv_get regs _ r v Hrv). apply in_or_app. left. exact Hin.
- apply Forall_forall. intros [r v] Hin. cbn [fst snd].
  destruct (Hrl r v Hin) as [[-> ->] | [Hcs Hin']]; [exact H10|].
  rewrite (HP r Hcs). apply (vk_rv_get regs _ r v Hrv). apply in_or_app. right. exact Hin'.
Qed.

Lemma vk_k1_le : forall R D, vr_k1 R D <= ev_vr R D.
Proof.
intros R D. rewrite ev_vr_eq. unfold vr_k3, vr_k2.
assert (H : 0 <= ev_after (vr_R2 R D) (vr_aft D)).
{ unfold ev_after. destruct (vr_aft D) as [p|]; [|lia].
  unfold EV_SUP_AFTER_REPLY, rec_spill_frees, EV_ARG_I, EV_XSTRDUP. destruct (Nat.ltb _ _); lia. }
assert (H2 : 0 <= EV_REPLY) by (unfold EV_REPLY, EV_SOCKET_SEND; lia).
lia.
Qed.

Lemma vk_frames : forall e pos lyc Sc (Wc : world SEGS) memc mdc k,
  vr_ent B MT e ->
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(4, pos)] lyc Sc Wc memc mdc k ->
  Z.of_nat (length (frames Sc)) <= 5.
Proof.
intros e pos lyc Sc Wc memc mdc k He HJ.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & Hf4 & _).
rewrite Hfrs. cbn [length app]. lia.
Qed.

Lemma vk_nev : forall e pos lyc Sc (Wc : world SEGS) memc mdc k EV1,
  vr_ent B MT e ->
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(4, pos)] lyc Sc Wc memc mdc k ->
  k + EV1 <= ev_vr (e_R e) (e_D e) -> st_nev Sc + EV1 <= EV_MAX.
Proof.
intros e pos lyc Sc Wc memc mdc k EV1 He HJ Hk.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & Hev & _).
lia.
Qed.

Lemma vk_live : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc LIVE1,
  vr_ent B MT e ->
  vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
  (6 * Z.of_nat (length (r_calls Rc)) + 8) * (LMAX + 2) + bsum tmps + LIVE1 <= LIVE_VERBS_RECEIVE ->
  blocks_bytes Sc + LIVE1 <= LIVE_MAX.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc LIVE1 He HC Hb.
pose proof HC as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hrec & _ & Hperm & _).
destruct He as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & Hlive & _).
pose proof (vr_live_le SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) (proj1 HJ) Hperm0 Hperm Hrec) as HL.
lia.
Qed.

(* a symbolic run that changes no byte the boundary reads: new registers and model *)
Lemma vk_regs : forall e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc Wc regsc regsc' memc mdc mdc',
  vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(4, pos)] lyc Sc Wc memc mdc' k ->
  vr_rv regsc' (vr_base B e ++ rl') ->
  vr_core B MT e pos F tmps sh sl rl' Rc Oc qv k kmax nm nmax lyc Sc Wc regsc' memc mdc'.
Proof.
intros e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc Wc regsc regsc' memc mdc mdc'
  (HJ & Hk & Hm & Hnm & Hfr & Hrv & H) HJ' Hrv'.
split; [exact HJ'|]. split; [exact Hk|]. split; [exact Hm|]. split; [exact Hnm|]. split; [exact Hfr|].
split; [exact Hrv' | exact H].
Qed.

(* the bounds kmax and nmax of a boundary may grow *)
Lemma vk_loosen : forall e pos F tmps sh sl rl Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc Wc regsc memc mdc,
  vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
  kmax <= kmax' -> nmax <= nmax' ->
  vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax' nm nmax' lyc Sc Wc regsc memc mdc.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc Wc regsc memc mdc
  (HJ & Hk & Hm & Hnm & H) H1 H2.
split; [exact HJ|]. split; [lia|]. split; [exact Hm|]. split; [lia | exact H].
Qed.

(* the bytes of the program's statics lie apart from the walk's own memory *)
Lemma vk_pg_apart : forall e pos F q c lyc Sc (Wc : world SEGS) memc mdc Oc tmps,
  AR SEGS B lyc Sc Wc memc mdc -> In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos ->
  Permutation (ablocks B lyc Sc) (Oc ++ tmps ++ e_rest e) -> In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
  alloc_ceiling <= vr_s1 e ->
  forall a, inFP cmd_PG a -> vr_wrange e F q c a -> False.
Proof.
intros e pos F q c lyc Sc Wc memc mdc Oc tmps HAR Hfr EF HP Hl Hc Hs1 a Hpg Hw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vr_s1_bounds e) as Hb.
assert (Hinb : forall pn, In pn (Oc ++ tmps ++ e_rest e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (Permutation_in _ (Permutation_sym HP) Hpn)).
assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc)) by (apply Hinb; apply in_or_app; right; apply in_or_app; left; exact Hl).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)) by (apply Hinb; apply in_or_app; right; apply in_or_app; left; exact Hc).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hfr) as (Hf0 & Hfc & Hfapp).
assert (E4 : fs_frame_bytes 4 = 1024) by reflexivity. rewrite E4 in Hfc. rewrite <- EF in Hf0, Hfc.
pose proof (shadow_addr_bounds F ltac:(lia)) as Hsh.
destruct (PROGU a Hpg) as (Himg & _ & _). pose proof (pa_img_range a Himg) as Hia.
destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]; try lia.
- apply (frm_img SEGS B LAWS _ _ _ _ _ 4 pos a HAR Hfr); [rewrite <- EF, E4; lia | exact Himg].
- apply (blk_img SEGS B LAWS _ _ _ _ _ q _ a HAR Hlb); [cbn [fst snd]; lia | exact Himg].
- apply (blk_img SEGS B LAWS _ _ _ _ _ c _ a HAR Hcb); [cbn [fst snd]; lia | exact Himg].
Qed.

Lemma vk_gq_pg : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> inFP cmd_PG a.
Proof. intros a Ha. unfold cmd_PG; apply inFP_cons; right; apply inFP_cons; right; apply inFP_cons; left; exact Ha. Qed.

Lemma vk_wrange_rng : forall e pos F q c lyc Sc (Wc : world SEGS) memc mdc Oc tmps,
  AR SEGS B lyc Sc Wc memc mdc -> In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos ->
  Permutation (ablocks B lyc Sc) (Oc ++ tmps ++ e_rest e) -> In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
  alloc_ceiling <= vr_s1 e -> vr_sp0 e <= 2 ^ 47 ->
  forall a, vr_wrange e F q c a -> 0 <= a < 2 ^ 64.
Proof.
intros e pos F q c lyc Sc Wc memc mdc Oc tmps HAR Hfr EF HP Hl Hc Hs1 Hsp a Hw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vr_s1_bounds e) as Hb.
assert (Hinb : forall pn, In pn (Oc ++ tmps ++ e_rest e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (Permutation_in _ (Permutation_sym HP) Hpn)).
assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc)) by (apply Hinb; apply in_or_app; right; apply in_or_app; left; exact Hl).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)) by (apply Hinb; apply in_or_app; right; apply in_or_app; left; exact Hc).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hfr) as (Hf0 & Hfc & Hfapp).
assert (E4 : fs_frame_bytes 4 = 1024) by reflexivity. rewrite E4 in Hfc. rewrite <- EF in Hf0, Hfc.
pose proof (shadow_addr_bounds F ltac:(lia)) as Hsh.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hlb) as (_ & Hl4 & Hlc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4 & Hcc & _).
unfold vr_lb, vr_cb in *; cbn [fst snd] in *.
destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]; lia.
Qed.

(* a symbolic run whose only store is into g_quitting (S24's quit flag) *)
Lemma vk_same : forall e pos F q c tp tmps rl rl' Rc Oc qv qv' k kmax nm nmax lyc Sc Wc regsc regsc' memc memc' mdc mdc',
  Z.of_nat (length (e_D e)) = e_n e ->
  vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
  vr_line B e q Wc memc -> vr_copy B e F c tp Wc memc ->
  In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(4, pos)] lyc Sc Wc memc' mdc' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_QUITTING <= a < A_G_QUITTING + 4) -> rdW Wc memc' a = rdW Wc memc a) ->
  aval_mem (rdW Wc memc') A_G_QUITTING 4 qv' ->
  vr_rv regsc' (vr_base B e ++ rl') ->
  vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl' Rc Oc qv' k kmax nm nmax lyc Sc Wc regsc' memc' mdc' /\
  vr_line B e q Wc memc' /\ vr_copy B e F c tp Wc memc'.
Proof.
intros e pos F q c tp tmps rl rl' Rc Oc qv qv' k kmax nm nmax lyc Sc Wc regsc regsc' memc memc' mdc mdc'
  HDn HC HL HCP Hl Hc HJ' Hkeep Hq' Hrv'.
destruct HC as (HJ & Hk & Hm & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hd & Hperm & Hq).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof (proj1 HJ') as HAR'.
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HV : 224 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (vr_s1_bounds e) as Hs1b.
assert (Hs1c : alloc_ceiling <= vr_s1 e) by lia.
assert (Hfr4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof Hfr as (EF & _ & _).
assert (HK : vr_wkeep e F q c (rdW Wc memc) (rdW Wc memc')).
{ intros a Ha. apply Hkeep.
  - exact (vk_wrange_rng e pos F q c lyc Sc Wc memc mdc Oc tmps HAR Hfr4 EF Hperm Hl Hc Hs1c ltac:(lia) a Ha).
  - intros Hga. exact (vk_pg_apart e pos F q c lyc Sc Wc memc mdc Oc tmps HAR Hfr4 EF Hperm Hl Hc Hs1c a (vk_gq_pg a Hga) Ha). }
split; [|split].
- split; [exact HJ'|]. split; [exact Hk|]. split; [exact Hm|]. split; [exact Hnm|].
  split; [exact (vr_frame_keep e q c lyc lyc Wc memc Wc memc' pos F vr_sh2 eq_refl HK Hfr)|].
  split; [exact Hrv'|].
  split; [exact (vr_saved_keep e F q c Wc memc Wc memc' HK Hsv)|].
  split; [exact (vr_spill_keep e F q c Wc memc Wc memc' (vr_sl3 F q c) HK (vr_sl3_ok F q c) Hsp)|].
  split.
  { apply (vr_env_of lyc Sc Wc memc' mdc' HAR'). destruct Henv as (Haro & _).
    apply (aro_agree _ _ Haro). intros a Hro.
    pose proof (pa_segs_low a (ro_img a Hro)) as Hlo.
    apply Hkeep; [lia|]. intros Hga. exact (RPG a (vk_gq_pg a Hga) Hro). }
  split.
  { apply (rec_repA_agree B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc memc') Rc Oc Hrec).
    - intros pn _ H. exact H.
    - intros kk Hkk. apply Hkeep; unfold A_G_REC, REC_SIZE, A_G_QUITTING in *; lia.
    - intros kk Hkk. apply Hkeep; unfold A_REC_SPILL, SC_SIZE, A_G_QUITTING in *; lia.
    - intros [p n] Hpn kk Hkk. cbn [fst snd] in *.
      pose proof (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn) as Hb.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hb) as (_ & Hp4 & Hpc & _ & _ & _ & Hn).
      pose proof (req_size_pos n ltac:(lia)) as [_ Hr].
      apply Hkeep; [lia|]. intros Hga.
      apply (blk_img SEGS B LAWS _ _ _ _ _ p n (p + kk) HAR Hb); [lia | exact (proj1 (PROGU _ (vk_gq_pg _ Hga)))]. }
  split; [exact Hd|]. split; [exact Hperm | exact Hq'].
- exact (vr_line_keep e F q c Wc memc Wc memc' HDn HK HL).
- exact (vr_copy_keep e F q c tp Wc memc Wc memc' HK HCP).
Qed.

(* a boundary state across a program call: the callee's journal keeps the walk's memory, which its footprint
   avoids, the read-only bytes and g_quitting; the recorder, the live blocks and the meter are the callee's post *)
Lemma vk_call_core : forall e pos F q c tp tmps tmps' rl rl' Rc Rc' Oc Oc' qv k k' kmax kmax' nm nm' nmax nmax'
  lyc Sc Wc regsc memc mdc ly2 S2 W2 regs2 mem2 md2 STK1 FP1 EV1,
  Z.of_nat (length (e_D e)) = e_n e ->
  vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
  vr_line B e q Wc memc -> vr_copy B e F c tp Wc memc ->
  In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(4, pos)] ly2 S2 W2 mem2 md2 k' ->
  ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 EV1 ->
  (forall a, inFP FP1 a -> vr_wrange e F q c a -> False) -> ~ YI16.sink_open_fp FP1 ->
  (forall a, in_roP SEGS RLO RHI a -> ~ inFP FP1 a) ->
  (forall a, inFP FP1 a -> ~ (A_G_QUITTING <= a < A_G_QUITTING + 4)) ->
  In (vr_lb e q) (ablocks B ly2 S2) -> In (vr_cb e c) (ablocks B ly2 S2) ->
  k' <= kmax' -> vr_meter MT e S2 k' nm' -> nm' <= nmax' ->
  vr_rv regs2 (vr_base B e ++ rl') ->
  rec_repA B ly2 S2 (rdW W2 mem2) Rc' Oc' -> ~ In (e_data e, Z.max (e_n e) 1) Oc' ->
  Permutation (ablocks B ly2 S2) (Oc' ++ tmps' ++ e_rest e) ->
  vr_core B MT e pos F tmps' vr_sh2 (vr_sl3 F q c) rl' Rc' Oc' qv k' kmax' nm' nmax' ly2 S2 W2 regs2 mem2 md2 /\
  vr_line B e q W2 mem2 /\ vr_copy B e F c tp W2 mem2.
Proof.
intros e pos F q c tp tmps tmps' rl rl' Rc Rc' Oc Oc' qv k k' kmax kmax' nm nm' nmax nmax'
  lyc Sc Wc regsc memc mdc ly2 S2 W2 regs2 mem2 md2 STK1 FP1 EV1
  HDn HC HL HCP Hl Hc HJ' HJ1 HFP Hso HFro HFgq Hl2 Hc2 Hk' Hm' Hnm' Hrv' Hrec' Hd' Hperm'.
destruct HC as (HJ & Hk & Hm & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hd & Hperm & Hq).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HJ1 as (HAR2 & Hly2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HV : 224 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (vr_s1_bounds e) as Hs1b.
assert (Hs1c : alloc_ceiling <= vr_s1 e) by lia.
assert (Hsp64 : vr_sp0 e <= 2 ^ 64) by lia.
assert (Hfr4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof Hfr as (EF & _ & _).
assert (Hinb : forall pn, In pn tmps -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right; apply in_or_app; left; exact Hpn. }
assert (HK : vr_wkeep e F q c (rdW Wc memc) (rdW W2 mem2))
  by exact (vr_wkeep_call e pos F q c lyc Sc Wc memc mdc STK1 FP1 ly2 S2 W2 mem2 md2 EV1 HJ1 Hfr4 EF
    (Hinb _ Hl) Hl2 (Hinb _ Hc) Hc2 Hs1c Hsp64 HFP).
assert (EF2 : ly_F ly2 = ly_F lyc) by (destruct Hly2 as (_ & _ & _ & _ & _ & EFx & _); exact EFx).
split; [|split].
- split; [exact HJ'|]. split; [exact Hk'|]. split; [exact Hm'|]. split; [exact Hnm'|].
  split; [exact (vr_frame_keep e q c lyc ly2 Wc memc W2 mem2 pos F vr_sh2 EF2 HK Hfr)|].
  split; [exact Hrv'|].
  split; [exact (vr_saved_keep e F q c Wc memc W2 mem2 HK Hsv)|].
  split; [exact (vr_spill_keep e F q c Wc memc W2 mem2 (vr_sl3 F q c) HK (vr_sl3_ok F q c) Hsp)|].
  split; [exact (vr_env_of ly2 S2 W2 mem2 md2 HAR2
    (aro_kept STK1 (vr_s1 e) FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 EV1 HJ1 HFro Hso (proj1 Henv)))|].
  split; [exact Hrec'|]. split; [exact Hd'|]. split; [exact Hperm'|].
  exact (gq_kept_call STK1 (vr_s1 e) FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 EV1 qv HJ1 HFgq Hso Hq).
- exact (vr_line_keep e F q c Wc memc W2 mem2 HDn HK HL).
- exact (vr_copy_keep e F q c tp Wc memc W2 mem2 HK HCP).
Qed.

(* the call rule at a boundary state: the frame chain (vr_achain, achain_push on afn_pre's chain), the window's
   presence from the walk's journal, and cl_callS_wide *)
Lemma vk_step : forall e pos F tmps sl rl Rc Oc qv k kmax nm nmax lyc Sc (W : world SEGS) regsc memc mdc
  AF STK1 FP1 EV1 retk (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (Q : world SEGS -> config -> Prop),
  vr_ent B MT e ->
  vr_core B MT e pos F tmps vr_sh2 sl rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc ->
  getr regsc 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK ->
  (forall a, inFP FP1 a -> awr_byte SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (ablocks B (e_ly e) (e_S e))
     (ablocks B lyc Sc) (frames (e_S e)) lyc [(4, pos)] a) ->
  (forall ch, afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch ->
     SRr SEGS W (cfg_at SEGS (BASE + AF) regsc memc mdc) (apost_base SEGS B STK1 FP1 regsc lyc Sc W memc mdc EV1 K)) ->
  ((forall a, vr_sp0 e - VERBS_RECEIVE_STK <= a < vr_sp0 e -> apresent (w_H W) memc a) ->
   forall ly2 S2 W2 regs2 mem2 md2, K ly2 S2 W2 regs2 mem2 md2 -> forall a, inFP FP1 a ->
     vr_sp0 e - VERBS_RECEIVE_STK <= a < vr_sp0 e -> ~ (vr_s1 e - STK1 <= a < vr_s1 e) -> aview SEGS (w_H W2) mem2 a <> None) ->
  (forall ly2 S2 W2 regs2 mem2 md2,
     ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
       [(4, pos)] ly2 S2 W2 mem2 md2 (k + EV1) ->
     ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 ->
     aregs_preserved regsc regs2 -> K ly2 S2 W2 regs2 mem2 md2 ->
     SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros e pos F tmps sl rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc AF STK1 FP1 EV1 retk K Q
  He HC R1 Hretk Hretk2 HST0 HSTK1 HAW CALL VIS CONT.
destruct HC as (HJ & _ & _ & _ & _ & Hrv & Hsv & _).
pose proof He as (HPRE0 & _).
pose proof HPRE0 as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & _).
assert (Etop : ly_top lyc = ly_top (e_ly e)) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Ex & _); exact Ex).
pose proof (vr_s1_bounds e) as Hs1b. pose proof (vr_s1_ge e Hal16) as [Hs1g Ho16].
assert (R2 : getr regsc 2 = w64 (vr_s1 e)) by (apply (vk_rv_get regsc _ 2 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R3 : getr regsc 3 = w64 (as_gp B)) by (apply (vk_rv_get regsc _ 3 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R4 : getr regsc 4 = w64 (as_tp B)) by (apply (vk_rv_get regsc _ 4 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R8 : getr regsc 8 = w64 (vr_sp0 e)) by (apply (vk_rv_get regsc _ 8 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (Hsp1 : spZ regsc = vr_s1 e) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regsc = vr_sp0 e) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
destruct (vr_achain e lyc W memc He Etop (vr_above e lyc Sc W memc mdc k pos He HJ) Hsv) as (ch1 & Hch1).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W regsc memc (Z_to_bv 64 (BASE + AF)) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e)
    (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdc k STK1 FP1 EV1 (vr_s1 e - vr_sp0 e)
    (Z_to_bv 64 (BASE + retk)) ch1 K HJ).
  - rewrite Hsp1. lia.
  - exact Ho16.
  - lia.
  - exact HST0.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; lia.
  - rewrite unsigned_lit_small by lia. lia.
  - replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) by lia. rewrite Hs0. exact Hch1.
  - intros HPRE1. pose proof (CALL ch1 HPRE1) as HC1.
    unfold cfg_at, w64 in HC1. eapply SRr_mono; [exact HC1|].
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. rewrite R1. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - exact HAW.
  - intros ly2 S2 W2 regs2 mem2 md2 HK2 a Ha Hw Hn. apply (VIS HP1 ly2 S2 W2 regs2 mem2 md2 HK2 a Ha Hw).
    intros Hw'. apply Hn. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & HK).
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
exact (CONT ly2 S2 W2 regs2 mem2 md2 HJ2 HJc HP HK).
Qed.

(* vk_step for a printf-reaching callee (statement pass 4: apost_baseF): the continuation runs at the FP state fx'
   the callee returns at, related to this one by fxrel (PaFx.v cl_callS_wideF) *)
Lemma vk_stepF : forall e pos F tmps sl rl Rc Oc qv k kmax nm nmax lyc Sc (W : world SEGS) regsc memc mdc
  AF STK1 FP1 EV1 retk (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (Q : world SEGS -> config -> Prop),
  vr_ent B MT e ->
  vr_core B MT e pos F tmps vr_sh2 sl rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc ->
  getr regsc 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK ->
  (forall a, inFP FP1 a -> awr_byte SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (ablocks B (e_ly e) (e_S e))
     (ablocks B lyc Sc) (frames (e_S e)) lyc [(4, pos)] a) ->
  (forall ch, afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch ->
     SRr SEGS W (cfg_at SEGS (BASE + AF) regsc memc mdc) (apost_baseF SEGS B STK1 FP1 regsc lyc Sc W memc mdc EV1 K)) ->
  ((forall a, vr_sp0 e - VERBS_RECEIVE_STK <= a < vr_sp0 e -> apresent (w_H W) memc a) ->
   forall ly2 S2 W2 regs2 mem2 md2, K ly2 S2 W2 regs2 mem2 md2 -> forall a, inFP FP1 a ->
     vr_sp0 e - VERBS_RECEIVE_STK <= a < vr_sp0 e -> ~ (vr_s1 e - STK1 <= a < vr_s1 e) -> aview SEGS (w_H W2) mem2 a <> None) ->
  (forall (fx' : YK11.FPState) ly2 S2 W2 regs2 mem2 md2, fxrel fx fx' ->
     ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
       [(4, pos)] ly2 S2 W2 mem2 md2 (k + EV1) ->
     ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 ->
     aregs_preserved regsc regs2 -> K ly2 S2 W2 regs2 mem2 md2 ->
     SRr SEGS W2 (mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros e pos F tmps sl rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc AF STK1 FP1 EV1 retk K Q
  He HC R1 Hretk Hretk2 HST0 HSTK1 HAW CALL VIS CONT.
destruct HC as (HJ & _ & _ & _ & _ & Hrv & Hsv & _).
pose proof He as (HPRE0 & _).
pose proof HPRE0 as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & _).
assert (Etop : ly_top lyc = ly_top (e_ly e)) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Ex & _); exact Ex).
pose proof (vr_s1_bounds e) as Hs1b. pose proof (vr_s1_ge e Hal16) as [Hs1g Ho16].
assert (R2 : getr regsc 2 = w64 (vr_s1 e)) by (apply (vk_rv_get regsc _ 2 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R3 : getr regsc 3 = w64 (as_gp B)) by (apply (vk_rv_get regsc _ 3 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R4 : getr regsc 4 = w64 (as_tp B)) by (apply (vk_rv_get regsc _ 4 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R8 : getr regsc 8 = w64 (vr_sp0 e)) by (apply (vk_rv_get regsc _ 8 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (Hsp1 : spZ regsc = vr_s1 e) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regsc = vr_sp0 e) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
destruct (vr_achain e lyc W memc He Etop (vr_above e lyc Sc W memc mdc k pos He HJ) Hsv) as (ch1 & Hch1).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
eapply SRr_bind.
{ eapply (cl_callS_wideF B LAWS W regsc memc (Z_to_bv 64 (BASE + AF)) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e)
    (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdc k STK1 FP1 EV1 (vr_s1 e - vr_sp0 e)
    (Z_to_bv 64 (BASE + retk)) ch1 K HJ).
  - rewrite Hsp1. lia.
  - exact Ho16.
  - lia.
  - exact HST0.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; lia.
  - rewrite unsigned_lit_small by lia. lia.
  - replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) by lia. rewrite Hs0. exact Hch1.
  - intros HPRE1. pose proof (CALL ch1 HPRE1) as HC1.
    unfold cfg_at, w64 in HC1. eapply SRr_mono; [exact HC1|].
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HR' & HC' & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. rewrite R1. split; [reflexivity|]. split; [exact HR'|]. split; [exact HC'|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - exact HAW.
  - intros ly2 S2 W2 regs2 mem2 md2 HK2 a Ha Hw Hn. apply (VIS HP1 ly2 S2 W2 regs2 mem2 md2 HK2 a Ha Hw).
    intros Hw'. apply Hn. lia. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJc & HP & HK).
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
exact (CONT fx' ly2 S2 W2 regs2 mem2 md2 Hfx HJ2 HJc HP HK).
Qed.

(* vr_ent at another FP state that keeps rounding mode 0 (only its last conjunct names the FP state) *)
Lemma vk_ent_fx : forall (f0 f1 : YK11.FPState) e, vr_ent (fx := f0) B MT e -> fxrel f0 f1 -> vr_ent (fx := f1) B MT e.
Proof.
intros f0 f1 e He Hfx. pose proof (fxrel_frm0 f0 f1) as Hf.
unfold vr_ent in *. cbv zeta in *.
repeat lazymatch type of He with
  | ?A /\ ?Rst => let H1 := fresh "H" in destruct He as [H1 He]; split; [exact H1|]
  end.
exact (Hf He Hfx).
Qed.

Lemma vk_env_agree : forall (regs : bvmap 5 word) extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma vk_kept_regs : forall E ss ms (regs0 : bvmap 5 word) extra (zs : list Z),
  st_ok SEGS E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) (map (Z_to_bv 5) zs) = true ->
  forall r, In r zs -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros E ss ms regs0 extra zs HS HA Hl r Hr.
apply (regs_kept_of_st_ok SEGS E ss ms regs0 extra (map (Z_to_bv 5) zs) HS HA Hl). apply in_map. exact Hr.
Qed.

Lemma vk_strnlen_le : forall n D, 0 <= n -> 0 <= StrFun.strnlen_res n D <= n.
Proof.
intros n D Hn. unfold StrFun.strnlen_res.
destruct (StrFun.find_byte 0 (firstn (Z.to_nat n) D)) as [i|] eqn:Fb; [|lia].
destruct (StrFun.find_byte_Some _ _ _ Fb) as (Hl & _). rewrite length_firstn in Hl. lia.
Qed.

Lemma vk_bsum2 : forall e q c, vr_ent B MT e -> bsum [vr_lb e q; vr_cb e c] <= 16386.
Proof.
intros e q c He. pose proof He as (_ & _ & _ & _ & _ & _ & _ & Hn8 & HDn & _).
pose proof (vr_line_le e HDn) as Hll.
pose proof (vk_strnlen_le (e_n e) (e_D e) ltac:(lia)) as Hl.
unfold vr_l in *. unfold bsum, vr_lb, vr_cb, vr_l. cbn [fold_right snd]. lia.
Qed.

(* a symbolic state that names only the registers, and the jump of a return pc to its join *)
Definition vk_ss_ret (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Lemma vk_jmp : forall retk stopk, 0 <= retk ->
  sym_run_toN_pi pl_tpi FUEL stopk (vk_ss_ret retk) = (vk_ss_ret stopk, PRS_running) ->
  forall W2 (regs2 : bvmap 5 word) mem2 md2 (Q : world SEGS -> config -> Prop) STK sp0 FP ly S W0 mem md own ly2 S2 kk,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 kk ->
  (forall regs3 md3, (forall r, getr regs3 r = getr regs2 r) ->
    ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md3 kk ->
    Q W2 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + stopk)) mem2 (seg_rom SEGS)) md3)) ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros retk stopk Hk Hrun W2 regs2 mem2 md2 Q STK sp0 FP ly S W0 mem md own ly2 S2 kk HJ HQ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs2 [])) (vk_ss_ret retk)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold vk_ss_ret. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
eapply (SRr_run_to_pi_AJ B LAWS W2 FUEL stopk (Eimg (Ereg regs2 [])) (vk_ss_ret retk) (vk_ss_ret stopk) PRS_running _
  STK sp0 FP ly S W0 mem md own ly2 S2 md2 kk Q HEI HS Hrun I HJ).
- apply awr_ok_nil.
- intros ms' mat HS' HJ' HF HFr HG.
  assert (Hro : rs_read_only (ss_mem (vk_ss_ret retk)) = true) by reflexivity.
  pose proof (frame_of_read_only _ _ _ _ Hro HF) as Hm. cbn [ms_mem mkst] in Hm.
  rewrite (st_ok_pi_restrict_mkst (w_H W2) _ (vk_ss_ret stopk) ms' HS' eq_refl). cbn [ss_pc vk_ss_ret].
  rewrite Hm in HJ' |- *.
  apply SRr_ret. apply HQ; [|exact HJ'].
  intros r. rewrite (st_ok_pi_restrict_reg (w_H W2) _ (vk_ss_ret stopk) ms' r HS'). cbn [ss_regs vk_ss_ret].
  symmetry. exact (regs_ok_Eimg_Ereg regs2 [] r).
Qed.

(* a word of tok[] handed to a callee: a C string inside the copy block, apart from the recorder's blocks *)
Lemma vk_tok_arg : forall e F c tp lyc Sc (W : world SEGS) mem md Oc tmps i p w,
  AR SEGS B lyc Sc W mem md ->
  Permutation (ablocks B lyc Sc) (Oc ++ tmps ++ e_rest e) -> In (vr_cb e c) tmps ->
  vr_copy B e F c tp W mem ->
  nth_error tp i = Some p -> nth_error (Verbs.toks (e_D e)) i = Some w ->
  in_blockA (ablocks B lyc Sc) p (Z.of_nat (length w) + 1) /\
  Forall (fun qk => iv_apart p (Z.of_nat (length w) + 1) (fst qk) (snd qk)) Oc /\
  astr_atR (rdW W mem) p w /\ Z.of_nat (length w) + 1 <= LMAX + 1 /\
  aval_mem (rdW W mem) (F + 32 + 8 * Z.of_nat i) 8 p /\ 4096 <= p /\ p + Z.of_nat (length w) + 1 <= alloc_ceiling.
Proof.
intros e F c tp lyc Sc W mem md Oc tmps i p w HAR Hperm Hc (Hfc & (Hmod & HlenP & Hptr & Hw)) Hp Hwi.
destruct (Hw i p w Hp Hwi) as (A1 & A2 & A3 & A4).
assert (HndOT : List.NoDup (Oc ++ tmps ++ e_rest e))
  by exact (Permutation_NoDup Hperm (verbs_receive_live.vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR)).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; left. exact Hc. }
assert (HcbO : ~ In (vr_cb e c) Oc).
{ intros H. exact (vr_nodup_app_dis _ _ _ HndOT H (in_or_app _ _ _ (or_introl Hc))). }
unfold vr_cb in Hcb, HcbO.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn).
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrs.
split; [exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1); split; [exact Hcb | lia]|].
split.
{ apply Forall_forall. intros [p' n'] Hin'.
  assert (Hin2 : In (p', n') (ablocks B lyc Sc))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hin').
  assert (Hne : (p', n') <> (c, Z.of_nat (length (Verbs.line (e_D e))) + 1))
    by (intros E; rewrite E in Hin'; exact (HcbO Hin')).
  pose proof (sep_blocks SEGS B LAWS lyc Sc W mem md p' n' _ _ HAR Hin2 Hcb Hne) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin2) as (_ & _ & _ & _ & _ & _ & Hn').
  pose proof (req_size_pos n' ltac:(lia)) as Hrs'.
  unfold zdisjoint in Hd. unfold iv_apart. cbn [fst snd] in *. lia. }
split; [exact A1|]. split; [unfold LMAX; lia|].
split; [exact (Hptr i p Hp)|]. split; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   sup_resp(code) at a boundary state: the text is a fresh block, the recorder untouched *)
Lemma vk_frm0 : forall e, vr_ent B MT e -> frm0 fx.
Proof.
intros e He. unfold vr_ent in He. cbv zeta in He.
repeat lazymatch type of He with _ /\ _ => destruct He as [_ He] end. exact He.
Qed.

Hypothesis TSUP_RESP : tsup_resp_spec B MT.
Lemma vk_sup_resp : forall e pos F q c tp tmps rl Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc (W : world SEGS)
  regsc memc mdc code retk (rlf : Z -> list (Z * Z)) (Q : world SEGS -> config -> Prop),
  vr_ent B MT e ->
  vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc ->
  vr_line B e q W memc -> vr_copy B e F c tp W memc -> In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
  getr regsc 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsc 10 = w64 code -> - 2 ^ 31 <= code < 2 ^ 31 ->
  k + EV_SUP_RESP <= ev_vr (e_R e) (e_D e) -> k + EV_SUP_RESP <= kmax' ->
  nm + 1 <= VERBS_RECEIVE_MALLOCS -> nm + 1 <= nmax' ->
  (6 * Z.of_nat (length (r_calls Rc)) + 8) * (LMAX + 2) + bsum tmps + 17 <= LIVE_VERBS_RECEIVE ->
  (forall tq r v, In (r, v) (rlf tq) -> (r = 10 /\ v = tq) \/ (acallee_saved r /\ In (r, v) rl)) ->
  (forall (fx' : YK11.FPState) tq ly2 S2 W2 regs2 mem2 md2, fxrel fx fx' -> 4096 <= tq ->
     astr_atR (rdW W2 mem2) tq (resp code) ->
     vr_core B MT e pos F ((tq, Z.of_nat (length (resp code)) + 1) :: tmps) vr_sh2 (vr_sl3 F q c) (rlf tq) Rc Oc qv
       (k + EV_SUP_RESP) kmax' (nm + 1) nmax' ly2 S2 W2 regs2 mem2 md2 ->
     vr_line B e q W2 mem2 -> vr_copy B e F c tp W2 mem2 ->
     SRr SEGS W2 (mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_sup_resp)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros e pos F q c tp tmps rl Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc W regsc memc mdc code retk rlf Q
  He HC HL HCP Hl Hc R1 Hrk1 Hrk2 R10 Hcode Hkev Hkmax Hnm32 Hnmax Hlv Hrlf CONT.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hd & Hperm & Hq).
pose proof He as (_ & _ & _ & _ & _ & _ & _ & _ & HDn & _).
assert (HSR : SUP_RESP_STK + 208 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSR0 : 0 <= SUP_RESP_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (resp_length code Hcode) as Hrl.
pose proof (mo_malloc_nonneg MT MTL VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as Hmm.
pose proof (mo_free_nonneg MT MTL) as Hmf.
assert (HXM : XM_SUP_RESP MT code <= 1 * mo_malloc MT VERBS_RECEIVE_REQ + 0 * mo_free MT).
{ unfold XM_SUP_RESP, XM_XSTRDUP.
  pose proof (mo_malloc_mono MT MTL (Z.of_nat (length (resp code)) + 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ; lia)). lia. }
assert (HXM0 : 0 <= XM_SUP_RESP MT code).
{ unfold XM_SUP_RESP, XM_XSTRDUP. apply mo_malloc_nonneg; [exact MTL | lia]. }
assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right; apply in_or_app; left; exact Hl. }
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right; apply in_or_app; left; exact Hc. }
eapply (vk_stepF e pos F tmps (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc AF_sup_resp
  SUP_RESP_STK [] EV_SUP_RESP retk _ Q He HC R1 Hrk1 Hrk2 HSR0 HSR).
- intros a Ha. destruct (inFP_nil a Ha).
- intros ch HPRE.
  exact (TSUP_RESP lyc Sc W regsc memc mdc ch code HPRE (vk_frm0 e He)
    ltac:(pose proof (vk_frames e pos lyc Sc W memc mdc k He HJ); lia)
    (proj1 Henv) (proj1 (proj2 (proj2 Henv))) R10 Hcode
    (vk_nev e pos lyc Sc W memc mdc k EV_SUP_RESP He HJ Hkev)
    (vk_live e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc
      (LIVE_SUP_RESP code) He HC ltac:(unfold LIVE_SUP_RESP, LIVE_XSTRDUP; lia))
    (vri_meter_ok B MT e Sc k nm (XM_SUP_RESP MT code) 1 0 EV_SUP_RESP MTL He Hmet HXM
      ltac:(unfold EV_SUP_RESP, EV_XSTRDUP; lia) ltac:(unfold EV_SUP_RESP, EV_XSTRDUP; lia) Hkev)).
- intros _ ly2 S2 W2 regs2 mem2 md2 _ a Ha. destruct (inFP_nil a Ha).
- intros fx' ly2 S2 W2 regs2 mem2 md2 Hfx HJ2 HJc HP HK. cbv beta zeta in HK.
  destruct HK as (tq & Htq10 & Htqr & Hperm2 & _ & _ & Hstr & Hrect & _ & Hmo).
  assert (Hlb2 : In (vr_lb e q) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm2)); right; exact Hlb).
  assert (Hcb2 : In (vr_cb e c) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm2)); right; exact Hcb).
  pose proof (Hrect Rc Oc Hrec) as Hrec2. cbn [sup_resp_m fst] in Hrec2.
  destruct (vk_call_core e pos F q c tp tmps ((tq, Z.of_nat (length (resp code)) + 1) :: tmps) rl (rlf tq) Rc Rc Oc Oc qv
    k (k + EV_SUP_RESP) kmax kmax' nm (nm + 1) nmax nmax' lyc Sc W regsc memc mdc ly2 S2 W2 regs2 mem2 md2
    SUP_RESP_STK [] EV_SUP_RESP HDn HC HL HCP Hl Hc HJ2 HJc) as (HC2 & HL2 & HCP2).
  + intros a Ha. destruct (inFP_nil a Ha).
  + exact (sink_closed_pos [] (Forall_nil _)).
  + intros a _ Ha. destruct (inFP_nil a Ha).
  + intros a Ha. destruct (inFP_nil a Ha).
  + exact Hlb2.
  + exact Hcb2.
  + exact Hkmax.
  + exact (vri_meter_step MT e Sc S2 k nm (XM_SUP_RESP MT code) 1 0 EV_SUP_RESP MTL Hmet Hmo HXM
      ltac:(unfold EV_SUP_RESP, EV_XSTRDUP; lia) ltac:(unfold EV_SUP_RESP, EV_XSTRDUP; lia)).
  + exact Hnmax.
  + exact (vk_rv_after e regsc regs2 rl (rlf tq) tq HP Hrv Htq10 (Hrlf tq)).
  + exact Hrec2.
  + exact Hd.
  + eapply Permutation_trans; [exact Hperm2|]. eapply Permutation_trans; [apply perm_skip; exact Hperm|].
    apply Permutation_middle.
  + exact (CONT fx' tq ly2 S2 W2 regs2 mem2 md2 Hfx ltac:(lia) Hstr HC2 HL2 HCP2).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Recorder callees: their footprint is g_rec, record.spill and the recorder's blocks (rec_fp) *)
Lemma vk_rec_low : forall lyc Sc (Wc : world SEGS) memc mdc Oc, AR SEGS B lyc Sc Wc memc mdc ->
  (forall pn, In pn Oc -> In pn (ablocks B lyc Sc)) ->
  forall a, inFP (rec_fp Oc) a -> a < alloc_ceiling.
Proof.
intros lyc Sc Wc memc mdc Oc HAR HO a Ha. pose proof asan_consts as (C1 & _).
unfold rec_fp in Ha.
apply inFP_cons in Ha as [G|Ha]; [unfold A_G_REC, REC_SIZE in *; lia|].
apply inFP_cons in Ha as [G|Ha]; [unfold A_REC_SPILL, SC_SIZE in *; lia|].
destruct (inFP_ablocks_fp_inv Oc a Ha) as (p & n & Hpn & Hr).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & _ & Hc & _). lia.
Qed.

Lemma vk_rec_gq : forall lyc Sc (Wc : world SEGS) memc mdc Oc, AR SEGS B lyc Sc Wc memc mdc ->
  (forall pn, In pn Oc -> In pn (ablocks B lyc Sc)) ->
  forall a, inFP (rec_fp Oc) a -> ~ (A_G_QUITTING <= a < A_G_QUITTING + 4).
Proof.
intros lyc Sc Wc memc mdc Oc HAR HO a Ha Hg. unfold rec_fp in Ha.
apply inFP_cons in Ha as [G|Ha]; [unfold A_G_REC, REC_SIZE, A_G_QUITTING in *; lia|].
apply inFP_cons in Ha as [G|Ha]; [unfold A_REC_SPILL, SC_SIZE, A_G_QUITTING in *; lia|].
destruct (inFP_ablocks_fp_inv Oc a Ha) as (p & n & Hpn & Hr).
exact (blk_img SEGS B LAWS _ _ _ _ _ p n a HAR (HO _ Hpn) Hr (proj1 (PROGU a (vk_gq_pg a Hg)))).
Qed.

(* every footprint byte of a recorder callee is one the walk may write: g_rec and record.spill (program statics),
   a recorder block of the entry (the walk's footprint) or one made since the entry (a temporary block) *)
Lemma vk_rec_awr : forall e pos lyc Sc (Wc : world SEGS) memc mdc Oc tmps,
  vr_ent B MT e -> AR SEGS B lyc Sc Wc memc mdc ->
  Permutation (ablocks B lyc Sc) (Oc ++ tmps ++ e_rest e) ->
  forall a, inFP (rec_fp Oc) a -> awr_byte SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e)
    (ablocks B (e_ly e) (e_S e)) (ablocks B lyc Sc) (frames (e_S e)) lyc [(4, pos)] a.
Proof.
intros e pos lyc Sc Wc memc mdc Oc tmps He HAR Hperm a Ha.
pose proof He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _).
assert (Hnd : List.NoDup (Oc ++ tmps ++ e_rest e))
  by exact (Permutation_NoDup Hperm (verbs_receive_live.vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR)).
assert (HO : forall pn, In pn Oc -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hpn).
unfold rec_fp in Ha. apply inFP_cons in Ha as [G|Ha].
- right; right; right; right; left. split; [exists (A_G_REC, A_G_REC + REC_SIZE); split;
    [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; left; reflexivity | exact G]|].
  assert (Hpg : inFP cmd_PG a) by (unfold cmd_PG; apply inFP_cons; left; unfold REC_SIZE in G; exact G).
  split; [|exact (proj1 (PROGU a Hpg))].
  rewrite (AF0m.ts_prog _ HB). unfold AF0m.TFIB_PROG_STATIC. apply Exists_cons_hd.
  unfold in_zr, A_G_REC, REC_SIZE in *. cbn [fst snd]. lia.
- apply inFP_cons in Ha as [G|Ha].
  + right; right; right; right; left. split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split;
      [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; right; left; reflexivity | exact G]|].
    assert (Hpg : inFP cmd_PG a)
      by (unfold cmd_PG; apply inFP_cons; right; apply inFP_cons; left; unfold SC_SIZE in G; exact G).
    split; [|exact (proj1 (PROGU a Hpg))].
    rewrite (AF0m.ts_prog _ HB). unfold AF0m.TFIB_PROG_STATIC. apply Exists_cons_tl. apply Exists_cons_hd.
    unfold in_zr, A_REC_SPILL, SC_SIZE in *. cbn [fst snd]. lia.
  + destruct (inFP_ablocks_fp_inv Oc a Ha) as (p & n & Hpn & Hr).
    destruct (in_dec pz_eq_dec (p, n) (e_O e)) as [HinO | HnO].
    * right; left. split; [exists (p, p + req_size n); split; [unfold vr_fp; apply in_or_app; right; unfold ablocks_fp;
        exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (p, n) HinO) | cbn; lia]|].
      exists p, n. split; [exact (HO _ Hpn) | exact Hr].
    * right; right; left. exists p, n. split; [exact (HO _ Hpn)|]. split; [|exact Hr].
      intros Hin0. apply (Permutation_in _ Hperm0) in Hin0. apply in_app_or in Hin0 as [H|H]; [exact (HnO H)|].
      apply (vr_nodup_app_dis _ _ (p, n) Hnd Hpn). apply in_or_app; right; exact H.
Qed.

Lemma vk_rec_mem : forall ly S rd R O O', rec_repA B ly S rd R O -> (forall pn, In pn O' <-> In pn O) ->
  rec_repA B ly S rd R O'.
Proof. intros ly S rd R O O' (Q & HA & HOQ) HE. exists Q. split; [exact HA|]. intros pn. rewrite HE. apply HOQ. Qed.

Lemma vk_rv_saved : forall e (regs regs2 : bvmap 5 word) rl rl',
  aregs_preserved regs regs2 -> vr_rv regs (vr_base B e ++ rl) ->
  (forall r v, In (r, v) rl' -> acallee_saved r /\ In (r, v) rl) ->
  vr_rv regs2 (vr_base B e ++ rl').
Proof.
intros e regs regs2 rl rl' HP Hrv Hrl. unfold vr_rv. apply Forall_app. split.
- apply Forall_forall. intros [r v] Hin. cbn [fst snd].
  assert (Hcs : acallee_saved r).
  { unfold vr_base in Hin. cbn [In] in Hin. unfold acallee_saved.
    destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _; lia. }
  rewrite (HP r Hcs). apply (vk_rv_get regs _ r v Hrv). apply in_or_app. left. exact Hin.
- apply Forall_forall. intros [r v] Hin. cbn [fst snd]. destruct (Hrl r v Hin) as [Hcs Hin'].
  rewrite (HP r Hcs). apply (vk_rv_get regs _ r v Hrv). apply in_or_app. right. exact Hin'.
Qed.

Lemma vk_code_range : forall ly S rd R O, rec_repA B ly S rd R O -> -2^31 <= r_code R < 2^31.
Proof. intros ly S rd R O (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HC & _) & _) & _). exact HC. Qed.

Lemma vk_rsf_nonneg : forall R, 0 <= rec_spill_frees R.
Proof. intros R. unfold rec_spill_frees. destruct (Nat.ltb _ _); lia. Qed.

(* a boundary state across a recorder callee: the recorder's blocks become filter (inb O1) of the live blocks, the
   callee's new blocks (its text, if any) join the walk's *)
Lemma vk_rec_core : forall e pos F q c tp tmps rl rl' Rc Rc' Oc O1 new qv k k' kmax kmax' nm nm' nmax nmax'
  lyc Sc Wc regsc memc mdc ly2 S2 W2 regs2 mem2 md2 STK1 EV1,
  vr_ent B MT e ->
  vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
  vr_line B e q Wc memc -> vr_copy B e F c tp Wc memc ->
  In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(4, pos)] ly2 S2 W2 mem2 md2 k' ->
  ajournal SEGS B STK1 (vr_s1 e) (rec_fp Oc) lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 EV1 ->
  rec_repA B ly2 S2 (rdW W2 mem2) Rc' O1 ->
  (forall pn, In pn O1 -> In pn Oc \/ ~ In pn (ablocks B lyc Sc)) ->
  (forall pn, In pn (ablocks B lyc Sc) -> ~ In pn Oc -> In pn (ablocks B ly2 S2)) ->
  (forall pn, In pn (ablocks B ly2 S2) -> (In pn (ablocks B lyc Sc) /\ ~ In pn Oc) \/ In pn O1 \/ In pn new) ->
  (forall pn, In pn new -> In pn (ablocks B ly2 S2)) -> List.NoDup new ->
  (forall pn, In pn new -> (In pn (ablocks B lyc Sc) -> In pn Oc) /\ ~ In pn O1) ->
  k' <= kmax' -> vr_meter MT e S2 k' nm' -> nm' <= nmax' ->
  vr_rv regs2 (vr_base B e ++ rl') ->
  vr_core B MT e pos F (new ++ tmps) vr_sh2 (vr_sl3 F q c) rl' Rc' (List.filter (inb O1) (ablocks B ly2 S2)) qv
    k' kmax' nm' nmax' ly2 S2 W2 regs2 mem2 md2 /\
  vr_line B e q W2 mem2 /\ vr_copy B e F c tp W2 mem2.
Proof.
intros e pos F q c tp tmps rl rl' Rc Rc' Oc O1 new qv k k' kmax kmax' nm nm' nmax nmax'
  lyc Sc Wc regsc memc mdc ly2 S2 W2 regs2 mem2 md2 STK1 EV1
  He HC HL HCP Hl Hc HJ' HJ1 Hrec' Ha1 Hsurv Hall Hnew Hndn Hnnew Hk' Hm' Hnm' Hrv'.
pose proof HC as (HJ & _ & _ & _ & (EF & _ & _) & _ & _ & _ & _ & Hrec & Hd & Hperm & _).
pose proof He as (_ & _ & _ & _ & _ & _ & _ & _ & HDn & HinD & HnotO & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _).
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ1) as HAR2.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HV : 224 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (vr_s1_bounds e) as Hs1b.
assert (Hs1c : alloc_ceiling <= vr_s1 e) by lia.
assert (Hfr4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (HO : forall pn, In pn Oc -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
assert (HO1s : forall pn, In pn O1 -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec' Hpn)).
assert (Hnd : List.NoDup (Oc ++ tmps ++ e_rest e))
  by exact (Permutation_NoDup Hperm (verbs_receive_live.vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR)).
assert (Hinb : forall pn, In pn (tmps ++ e_rest e) -> In pn (ablocks B lyc Sc) /\ ~ In pn Oc).
{ intros pn Hpn. split; [apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; exact Hpn|].
  intros HinO. exact (vr_nodup_app_dis _ _ _ Hnd HinO Hpn). }
assert (Hl2 : In (vr_lb e q) (ablocks B ly2 S2))
  by (destruct (Hinb (vr_lb e q) ltac:(apply in_or_app; left; exact Hl)) as [H1 H2]; exact (Hsurv _ H1 H2)).
assert (Hc2 : In (vr_cb e c) (ablocks B ly2 S2))
  by (destruct (Hinb (vr_cb e c) ltac:(apply in_or_app; left; exact Hc)) as [H1 H2]; exact (Hsurv _ H1 H2)).
assert (HinR : In (e_data e, Z.max (e_n e) 1) (e_rest e)).
{ pose proof (Permutation_in _ Hperm0 HinD) as H0. apply in_app_or in H0 as [H0|H0]; [contradiction | exact H0]. }
apply (vk_call_core e pos F q c tp tmps (new ++ tmps) rl rl' Rc Rc' Oc (List.filter (inb O1) (ablocks B ly2 S2)) qv
  k k' kmax kmax' nm nm' nmax nmax' lyc Sc Wc regsc memc mdc ly2 S2 W2 regs2 mem2 md2 STK1 (rec_fp Oc) EV1
  HDn HC HL HCP Hl Hc HJ' HJ1).
- exact (vr_rec_fp_apart e pos F q c lyc Sc Wc memc mdc Oc tmps HAR Hfr4 EF Hperm Hl Hc Hs1c).
- exact (rec_fp_closed lyc Sc Wc memc mdc Oc HAR HO).
- exact (rec_fp_not_ro lyc Sc Wc memc mdc Oc HAR HO).
- exact (vk_rec_gq lyc Sc Wc memc mdc Oc HAR HO).
- exact Hl2.
- exact Hc2.
- exact Hk'.
- exact Hm'.
- exact Hnm'.
- exact Hrv'.
- apply (vk_rec_mem _ _ _ _ O1 _ Hrec'). intros pn. rewrite in_filter_inb.
  split; [intros [_ H]; exact H | intros H; split; [exact (HO1s _ H) | exact H]].
- intros Hin. apply in_filter_inb in Hin as [_ Hin]. destruct (Ha1 _ Hin) as [H|H]; [exact (Hd H)|].
  apply H. exact (proj1 (Hinb _ (in_or_app _ _ _ (or_intror HinR)))).
- exact (vk_perm_after (ablocks B lyc Sc) (ablocks B ly2 S2) Oc O1 tmps (e_rest e) new
    (verbs_receive_live.vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR)
    (verbs_receive_live.vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR2) Hperm Hsurv Hall Ha1 Hnew Hndn Hnnew).
Qed.

Hypothesis TPINS_CLEAR : tpins_clear_spec B MT.
Lemma vk_pins_clear : forall e pos F q c tp tmps rl Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc (W : world SEGS)
  regsc memc mdc pu u retk (rlf : Z -> list (Z * Z)) (Q : world SEGS -> config -> Prop),
  vr_ent B MT e ->
  vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc ->
  vr_line B e q W memc -> vr_copy B e F c tp W memc -> In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
  getr regsc 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsc 10 = w64 pu -> 0 <= pu < 2 ^ 64 ->
  in_blockA (ablocks B lyc Sc) pu (Z.of_nat (length u) + 1) ->
  Forall (fun qk => iv_apart pu (Z.of_nat (length u) + 1) (fst qk) (snd qk)) Oc ->
  astr_atR (rdW W memc) pu u -> Z.of_nat (length u) + 1 <= LMAX + 1 ->
  rec_spill_frees Rc = 0 ->
  k + EV_PINS_CLEAR Rc <= ev_vr (e_R e) (e_D e) -> k + EV_PINS_CLEAR Rc <= kmax' ->
  nm + 3 <= VERBS_RECEIVE_MALLOCS -> nm + 3 <= nmax' ->
  (6 * Z.of_nat (length (r_calls Rc)) + 8) * (LMAX + 2) + bsum tmps + LIVE_PINS_CLEAR Rc (Some u) <= LIVE_VERBS_RECEIVE ->
  (forall t r v, In (r, v) (rlf t) -> (r = 10 /\ v = t) \/ (acallee_saved r /\ In (r, v) rl)) ->
  (forall (fx' : YK11.FPState) R1 rcd Oc1 ly2 S2 W2 regs2 mem2 md2, fxrel fx fx' ->
     pins_clear_m Rc (Some u) = (R1, rcd) -> - 2 ^ 31 <= rcd < 2 ^ 31 ->
     vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) (rlf rcd) R1 Oc1 qv (k + EV_PINS_CLEAR Rc) kmax' (nm + 3) nmax'
       ly2 S2 W2 regs2 mem2 md2 ->
     vr_line B e q W2 mem2 -> vr_copy B e F c tp W2 mem2 ->
     SRr SEGS W2 (mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_pins_clear)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros e pos F q c tp tmps rl Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc W regsc memc mdc pu u retk rlf Q
  He HC HL HCP Hl Hc R1 Hrk1 Hrk2 R10 Hpu Hblk Hap Hstr Hlen Hsf Hkev Hkmax Hnm32 Hnmax Hlv Hrlf CONT.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hd & Hperm & Hq).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HPS : PINS_CLEAR_STK + 208 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HPS0 : 0 <= PINS_CLEAR_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (vk_code_range lyc Sc _ Rc Oc Hrec) as Hcode.
assert (Hrcr : - 2 ^ 31 <= snd (pins_clear_m Rc (Some u)) < 2 ^ 31)
  by (destruct (code_pins_clear Rc (Some u)) as [-> | ->]; lia).
pose proof (resp_length _ Hrcr) as Hrl.
pose proof (mo_malloc_nonneg MT MTL VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as Hmm.
pose proof (mo_free_nonneg MT MTL) as Hmf.
assert (HXM : XM_PINS_CLEAR MT Rc (Some u) <= 3 * mo_malloc MT VERBS_RECEIVE_REQ + 2 * mo_free MT).
{ unfold XM_PINS_CLEAR, XM_ANSWER_CODE, XM_HAND_BACK, XM_XSTRDUP. rewrite Hsf. cbn [sarg].
  pose proof (mo_malloc_mono MT MTL (Z.of_nat (length u) + 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ, LMAX in *; lia)).
  pose proof (mo_malloc_mono MT MTL (Z.of_nat (length (resp (snd (pins_clear_m Rc (Some u))))) + 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ; lia)).
  lia. }
assert (HXM0 : 0 <= XM_PINS_CLEAR MT Rc (Some u)).
{ unfold XM_PINS_CLEAR, XM_ANSWER_CODE, XM_HAND_BACK, XM_XSTRDUP. rewrite Hsf. cbn [sarg].
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length u) + 1) ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (resp (snd (pins_clear_m Rc (Some u))))) + 1) ltac:(lia)).
  lia. }
assert (HEV : EV_PINS_CLEAR Rc = 5)
  by (unfold EV_PINS_CLEAR, EV_ANSWER_CODE, EV_HAND_BACK, EV_XSTRDUP; rewrite Hsf; reflexivity).
assert (HO : forall pn, In pn Oc -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
eapply (vk_stepF e pos F tmps (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc AF_pins_clear
  PINS_CLEAR_STK (rec_fp Oc) (EV_PINS_CLEAR Rc) retk _ Q He HC R1 Hrk1 Hrk2 HPS0 HPS).
- exact (vk_rec_awr e pos lyc Sc W memc mdc Oc tmps He HAR Hperm).
- intros ch HPRE.
  exact (TPINS_CLEAR lyc Sc W regsc memc mdc ch pu u Rc Oc HPRE (vk_frm0 e He) (proj1 Henv) (proj1 (proj2 (proj2 Henv)))
    R10 Hpu Hblk Hap Hstr Hlen Hrec
    ltac:(pose proof (vk_frames e pos lyc Sc W memc mdc k He HJ); lia)
    (vk_nev e pos lyc Sc W memc mdc k (EV_PINS_CLEAR Rc) He HJ Hkev)
    (vk_live e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc
      (LIVE_PINS_CLEAR Rc (Some u)) He HC Hlv)
    (vri_meter_ok B MT e Sc k nm (XM_PINS_CLEAR MT Rc (Some u)) 3 2 (EV_PINS_CLEAR Rc) MTL He Hmet HXM
      ltac:(rewrite HEV; lia) ltac:(rewrite HEV; lia) Hkev)).
- intros _ ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
  pose proof (vk_rec_low lyc Sc W memc mdc Oc HAR HO a Ha). lia.
- intros fx' ly2 S2 W2 regs2 mem2 md2 Hfx HJ2 HJc HP HK.
  destruct HK as (R1' & rcd & O1 & Em & Hr10 & Hrr & Hrec' & Ha1 & Hsurv & Hall & _ & Hmo).
  destruct (vk_rec_core e pos F q c tp tmps rl (rlf rcd) Rc R1' Oc O1 [] qv k (k + EV_PINS_CLEAR Rc) kmax kmax'
    nm (nm + 3) nmax nmax' lyc Sc W regsc memc mdc ly2 S2 W2 regs2 mem2 md2 PINS_CLEAR_STK (EV_PINS_CLEAR Rc)
    He HC HL HCP Hl Hc HJ2 HJc Hrec' Ha1 Hsurv) as (HC2 & HL2 & HCP2).
  + intros pn Hpn. destruct (Hall pn Hpn) as [H|H]; [left; exact H | right; left; exact H].
  + intros pn [].
  + constructor.
  + intros pn [].
  + exact Hkmax.
  + exact (vri_meter_step MT e Sc S2 k nm _ 3 2 (EV_PINS_CLEAR Rc) MTL Hmet Hmo HXM
      ltac:(rewrite HEV; lia) ltac:(rewrite HEV; lia)).
  + exact Hnmax.
  + exact (vk_rv_after e regsc regs2 rl (rlf rcd) rcd HP Hrv Hr10 (Hrlf rcd)).
  + cbn [app] in HC2. exact (CONT fx' R1' rcd _ ly2 S2 W2 regs2 mem2 md2 Hfx Em Hrr HC2 HL2 HCP2).
Qed.

Hypothesis TLV2_REFUSALS_FORGET : tlv2_refusals_forget_spec B MT.
Lemma vk_lv2 : forall e pos F q c tp tmps rl rl' Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc (W : world SEGS)
  regsc memc mdc retk (Q : world SEGS -> config -> Prop),
  vr_ent B MT e ->
  vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc ->
  vr_line B e q W memc -> vr_copy B e F c tp W memc -> In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
  getr regsc 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsc 10 = w64 0 ->
  k + EV_LV2_REFUSALS_FORGET Rc <= ev_vr (e_R e) (e_D e) -> k + EV_LV2_REFUSALS_FORGET Rc <= kmax' ->
  nm + 1 <= VERBS_RECEIVE_MALLOCS -> nm + 1 <= nmax' ->
  (6 * Z.of_nat (length (r_calls Rc)) + 8) * (LMAX + 2) + bsum tmps + 2 <= LIVE_VERBS_RECEIVE ->
  (forall r v, In (r, v) rl' -> acallee_saved r /\ In (r, v) rl) ->
  (forall Oc1 ly2 S2 W2 regs2 mem2 md2,
     vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl' (lv2_refusals_forget_m Rc None) Oc1 qv
       (k + EV_LV2_REFUSALS_FORGET Rc) kmax' (nm + 1) nmax' ly2 S2 W2 regs2 mem2 md2 ->
     vr_line B e q W2 mem2 -> vr_copy B e F c tp W2 mem2 ->
     SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_lv2_refusals_forget)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros e pos F q c tp tmps rl rl' Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc W regsc memc mdc retk Q
  He HC HL HCP Hl Hc R1 Hrk1 Hrk2 R10 Hkev Hkmax Hnm32 Hnmax Hlv Hrl CONT.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hd & Hperm & Hq).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HLS : LV2_REFUSALS_FORGET_STK + 208 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HLS0 : 0 <= LV2_REFUSALS_FORGET_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (mo_malloc_nonneg MT MTL VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as Hmm.
pose proof (mo_free_nonneg MT MTL) as Hmf.
pose proof (vk_rsf_nonneg Rc) as Hsf0.
assert (HXM : XM_LV2_REFUSALS_FORGET MT Rc None <= 1 * mo_malloc MT VERBS_RECEIVE_REQ + rec_spill_frees Rc * mo_free MT).
{ unfold XM_LV2_REFUSALS_FORGET, XM_XSTRDUP. cbn [darg].
  lazymatch goal with |- context [mo_malloc MT ?x] =>
    pose proof (mo_malloc_mono MT MTL x VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; cbn; lia)) end.
  lia. }
assert (HXM0 : 0 <= XM_LV2_REFUSALS_FORGET MT Rc None).
{ unfold XM_LV2_REFUSALS_FORGET, XM_XSTRDUP. cbn [darg].
  lazymatch goal with |- context [mo_malloc MT ?x] =>
    pose proof (mo_malloc_nonneg MT MTL x ltac:(cbn; lia)) end.
  nia. }
assert (HEV : EV_LV2_REFUSALS_FORGET Rc = rec_spill_frees Rc + 1)
  by (unfold EV_LV2_REFUSALS_FORGET, EV_XSTRDUP; reflexivity).
assert (HLV : LIVE_LV2_REFUSALS_FORGET None <= 2) by (unfold LIVE_LV2_REFUSALS_FORGET, LIVE_XSTRDUP; cbn; lia).
assert (HO : forall pn, In pn Oc -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
eapply (vk_step e pos F tmps (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc AF_lv2_refusals_forget
  LV2_REFUSALS_FORGET_STK (rec_fp Oc) (EV_LV2_REFUSALS_FORGET Rc) retk _ Q He HC R1 Hrk1 Hrk2 HLS0 HLS).
- exact (vk_rec_awr e pos lyc Sc W memc mdc Oc tmps He HAR Hperm).
- intros ch HPRE.
  exact (TLV2_REFUSALS_FORGET lyc Sc W regsc memc mdc ch 0 None Rc Oc HPRE (proj1 Henv)
    (proj1 (proj2 (proj2 Henv))) R10 ltac:(lia) eq_refl (fun x Hx => ltac:(discriminate Hx)) Hrec
    (vk_nev e pos lyc Sc W memc mdc k (EV_LV2_REFUSALS_FORGET Rc) He HJ Hkev)
    (vk_live e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc
      (LIVE_LV2_REFUSALS_FORGET None) He HC ltac:(lia))
    (vri_meter_ok B MT e Sc k nm (XM_LV2_REFUSALS_FORGET MT Rc None) 1 (rec_spill_frees Rc) (EV_LV2_REFUSALS_FORGET Rc)
      MTL He Hmet HXM ltac:(rewrite HEV; lia) ltac:(rewrite HEV; lia) Hkev)).
- intros _ ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
  pose proof (vk_rec_low lyc Sc W memc mdc Oc HAR HO a Ha). lia.
- intros ly2 S2 W2 regs2 mem2 md2 HJ2 HJc HP HK.
  destruct HK as (O1 & Hrec' & Ha1 & Hsurv & Hall & _ & Hmo).
  destruct (vk_rec_core e pos F q c tp tmps rl rl' Rc (lv2_refusals_forget_m Rc None) Oc O1 [] qv k
    (k + EV_LV2_REFUSALS_FORGET Rc) kmax kmax' nm (nm + 1) nmax nmax' lyc Sc W regsc memc mdc ly2 S2 W2 regs2 mem2 md2
    LV2_REFUSALS_FORGET_STK (EV_LV2_REFUSALS_FORGET Rc) He HC HL HCP Hl Hc HJ2 HJc Hrec' Ha1 Hsurv) as (HC2 & HL2 & HCP2).
  + intros pn Hpn. destruct (Hall pn Hpn) as [H|H]; [left; exact H | right; left; exact H].
  + intros pn [].
  + constructor.
  + intros pn [].
  + exact Hkmax.
  + exact (vri_meter_step MT e Sc S2 k nm _ 1 (rec_spill_frees Rc) (EV_LV2_REFUSALS_FORGET Rc) MTL Hmet Hmo HXM
      ltac:(rewrite HEV; lia) ltac:(rewrite HEV; lia)).
  + exact Hnmax.
  + exact (vk_rv_saved e regsc regs2 rl rl' HP Hrv Hrl).
  + cbn [app] in HC2. exact (CONT _ ly2 S2 W2 regs2 mem2 md2 HC2 HL2 HCP2).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   number(word, s1+84): its footprint is the result cell s1+84 of this function's real frame; it keeps the layout,
   the live blocks and the recorder, and changes only the side-stack frame state (meter class (b), MTFL) *)
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TNUMBER : tnumber_spec B MT.
Lemma vk_number : forall e pos F q c tp tmps rl Rc Oc qv k kmax nm nmax lyc Sc (W : world SEGS)
  regsc memc mdc pw wd retk (rlf : Z -> list (Z * Z)) (Q : world SEGS -> config -> Prop),
  vr_ent B MT e ->
  vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc ->
  vr_line B e q W memc -> vr_copy B e F c tp W memc -> In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
  getr regsc 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsc 10 = w64 pw -> 0 <= pw < 2 ^ 64 -> getr regsc 11 = w64 (vr_s1 e + 84) ->
  in_blockA (ablocks B lyc Sc) pw (Z.of_nat (length wd) + 1) -> astr_atR (rdW W memc) pw wd ->
  Z.of_nat (length wd) + 1 <= LMAX + 1 ->
  k <= ev_vr (e_R e) (e_D e) ->
  (forall t r v, In (r, v) (rlf t) -> (r = 10 /\ v = t) \/ (acallee_saved r /\ In (r, v) rl)) ->
  (forall ly2 S2 W2 regs2 mem2 md2,
     vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c)
       (rlf (match Verbs.number_m wd with Some _ => 1 | None => 0 end)) Rc Oc qv k kmax nm nmax ly2 S2 W2 regs2 mem2 md2 ->
     vr_line B e q W2 mem2 -> vr_copy B e F c tp W2 mem2 ->
     (forall v, Verbs.number_m wd = Some v -> aval_mem (rdW W2 mem2) (vr_s1 e + 84) 4 v) ->
     SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_number)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros e pos F q c tp tmps rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc pw wd retk rlf Q
  He HC HL HCP Hl Hc R1 Hrk1 Hrk2 R10 Hpw R11 Hblk Hstr Hlen Hkev Hrlf CONT.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hd & Hperm & Hq).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (Etop : ly_top lyc = ly_top (e_ly e)) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Ex & _); exact Ex).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HV : 224 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HNS : NUMBER_STK + 208 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HNS0 : 0 <= NUMBER_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (vr_s1_bounds e) as Hs1b.
assert (Hs1c : alloc_ceiling <= vr_s1 e) by lia.
assert (Hfr4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof Hfr as (EF & _ & _).
assert (R2 : getr regsc 2 = w64 (vr_s1 e)) by (apply (vk_rv_get regsc _ 2 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (Hsp1 : spZ regsc = vr_s1 e) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hmod4 : (vr_s1 e + 84) mod 4 = 0).
{ destruct Hs1b as [_ Hm]. apply Z.mod_divide in Hm; [|lia]. destruct Hm as [z Hz]. rewrite Hz.
  replace (z * 32 + 84) with ((8 * z + 21) * 4) by lia. apply Z_mod_mult. }
assert (HO : forall pn, In pn Oc -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
eapply (vk_step e pos F tmps (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc AF_number
  NUMBER_STK [(vr_s1 e + 84, vr_s1 e + 84 + 4)] EV_NUMBER retk _ Q He HC R1 Hrk1 Hrk2 HNS0 HNS).
- intros a Ha. apply inFP_cons in Ha as [Ha|Ha]; [|destruct (inFP_nil a Ha)]. left. lia.
- intros ch HPRE.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  assert (Hslot : spZ regsc <= vr_s1 e + 84 /\ vr_s1 e + 84 + 4 <= ly_top lyc /\
    (forall i, 0 <= i < 4 -> apresent (w_H W) memc (vr_s1 e + 84 + i))).
  { split; [rewrite Hsp1; lia|]. split; [rewrite Etop; lia|]. intros i Hi. apply Hpres. lia. }
  assert (Hern : iv_apart (vr_s1 e + 84) 4 (as_errno B) 4)
    by (rewrite (AF0m.ts_errno B HB); unfold AF0m.TFIB_ERRNO, iv_apart; right; lia).
  assert (Hfrm : Z.of_nat (length (frames Sc)) <= 6) by (pose proof (vk_frames e pos lyc Sc W memc mdc k He HJ); lia).
  assert (Hkn : k + EV_NUMBER <= ev_vr (e_R e) (e_D e)) by (unfold EV_NUMBER; lia).
  exact (TNUMBER lyc Sc W regsc memc mdc ch pw (vr_s1 e + 84) wd HPRE (proj1 Henv) R10 Hpw R11 ltac:(lia)
    Hblk Hstr Hlen Hmod4 (or_intror Hslot) Hern Hfrm (vk_nev e pos lyc Sc W memc mdc k EV_NUMBER He HJ Hkn)).
- intros HP1 ly2 S2 W2 regs2 mem2 md2 HK a Ha Hw Hn. destruct HK as (HKm & _ & _ & _).
  apply inFP_cons in Ha as [Ha|Ha]; [|destruct (inFP_nil a Ha)].
  destruct (Verbs.number_m wd) as [v|]; destruct HKm as [_ HKm].
  + replace a with (vr_s1 e + 84 + Z.of_nat (Z.to_nat (a - (vr_s1 e + 84)))) by lia.
    rewrite (HKm (Z.to_nat (a - (vr_s1 e + 84))) ltac:(lia)). discriminate.
  + replace a with (vr_s1 e + 84 + (a - (vr_s1 e + 84))) by lia. rewrite (HKm (a - (vr_s1 e + 84)) ltac:(lia)).
    replace (vr_s1 e + 84 + (a - (vr_s1 e + 84))) with a by lia.
    intros Hnone. exact (aview_some_of_apresent SEGS _ _ a (HP1 a Hw) Hnone).
- intros ly2 S2 W2 regs2 mem2 md2 HJ2 HJc HP HK. destruct HK as (HKm & Hperm2 & -> & (f & ->)).
  replace (k + EV_NUMBER) with k in HJ2 by (unfold EV_NUMBER; lia).
  assert (Hsv1 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B lyc (set_fs f Sc)))
    by (intros pn Hpn; exact (Permutation_in _ (Permutation_sym Hperm2) Hpn)).
  assert (Hinb : forall pn, In pn tmps -> In pn (ablocks B lyc Sc)).
  { intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right; apply in_or_app; left; exact Hpn. }
  assert (H10 : getr regs2 10 = w64 (match Verbs.number_m wd with Some _ => 1 | None => 0 end))
    by (destruct (Verbs.number_m wd); destruct HKm as [H _]; exact H).
  destruct (vk_call_core e pos F q c tp tmps tmps rl (rlf (match Verbs.number_m wd with Some _ => 1 | None => 0 end))
    Rc Rc Oc Oc qv k k kmax kmax nm nm nmax nmax lyc Sc W regsc memc mdc lyc (set_fs f Sc) W2 regs2 mem2 md2
    NUMBER_STK [(vr_s1 e + 84, vr_s1 e + 84 + 4)] EV_NUMBER
    ltac:(destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & HDn & _); exact HDn) HC HL HCP Hl Hc HJ2 HJc)
    as (HC2 & HL2 & HCP2).
  + exact (vr_out_apart e pos F q c lyc Sc W memc mdc Oc tmps HAR Hfr4 EF Hperm Hl Hc Hs1c).
  + apply sink_closed_cons; [cbn; lia | exact (sink_closed_pos [] (Forall_nil _))].
  + intros a Hro Ha. apply inFP_cons in Ha as [Ha|Ha]; [|exact (inFP_nil a Ha)].
    pose proof (pa_segs_low a (ro_img a Hro)). lia.
  + intros a Ha Hg. apply inFP_cons in Ha as [Ha|Ha]; [|exact (inFP_nil a Ha)]. unfold A_G_QUITTING in Hg. lia.
  + exact (Hsv1 _ (Hinb _ Hl)).
  + exact (Hsv1 _ (Hinb _ Hc)).
  + exact Hk.
  + destruct Hmet as (nf & H0 & H1 & H2 & Hle). exists nf. split; [lia|]. split; [lia|]. split; [lia|].
    exact (mo_le_set_fs_r MT MTFL _ _ f _ Hle).
  + exact Hnm.
  + exact (vk_rv_after e regsc regs2 rl _ _ HP Hrv H10 (Hrlf _)).
  + apply (rec_kept_call NUMBER_STK (vr_s1 e) [(vr_s1 e + 84, vr_s1 e + 84 + 4)] lyc Sc W memc mdc lyc (set_fs f Sc)
      W2 mem2 md2 EV_NUMBER Rc Oc HJc).
    * intros a Ha Hpg. apply inFP_cons in Ha as [Ha|Ha]; [|exact (inFP_nil a Ha)].
      destruct (PROGU a Hpg) as (Himg & _ & _). pose proof (pa_img_range a Himg). lia.
    * apply sink_closed_cons; [cbn; lia | exact (sink_closed_pos [] (Forall_nil _))].
    * intros p n i Hpn Hi Ha. apply inFP_cons in Ha as [Ha|Ha]; [|exact (inFP_nil _ Ha)].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & _ & Hcc & _). lia.
    * intros pn Hin. exact (Hsv1 _ (HO _ Hin)).
    * exact Hrec.
  + exact Hd.
  + exact (Permutation_trans Hperm2 Hperm).
  + apply (CONT lyc (set_fs f Sc) W2 regs2 mem2 md2 HC2 HL2 HCP2).
    intros v Hv. rewrite Hv in HKm. exact (proj2 HKm).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   sup_chain_clear(id): a recorder callee that hands back a text block *)
Hypothesis TSUP_CHAIN_CLEAR : tsup_chain_clear_spec B MT.
Lemma vk_chain_clear : forall e pos F q c tp tmps rl Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc (W : world SEGS)
  regsc memc mdc id retk (rlf : Z -> list (Z * Z)) (Q : world SEGS -> config -> Prop),
  vr_ent B MT e ->
  vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc ->
  vr_line B e q W memc -> vr_copy B e F c tp W memc -> In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
  getr regsc 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsc 10 = w64 id -> - 2 ^ 31 <= id < 2 ^ 31 ->
  rec_spill_frees Rc = 0 ->
  k + EV_SUP_CHAIN_CLEAR Rc <= ev_vr (e_R e) (e_D e) -> k + EV_SUP_CHAIN_CLEAR Rc <= kmax' ->
  nm + 3 <= VERBS_RECEIVE_MALLOCS -> nm + 3 <= nmax' ->
  (6 * Z.of_nat (length (r_calls Rc)) + 8) * (LMAX + 2) + bsum tmps + LIVE_SUP_CHAIN_CLEAR Rc id <= LIVE_VERBS_RECEIVE ->
  (forall t r v, In (r, v) (rlf t) -> (r = 10 /\ v = t) \/ (acallee_saved r /\ In (r, v) rl)) ->
  (forall (fx' : YK11.FPState) R1 t tq Oc1 ly2 S2 W2 regs2 mem2 md2, fxrel fx fx' ->
     sup_chain_clear_m Rc id = (R1, t) -> 4096 <= tq ->
     astr_atR (rdW W2 mem2) tq t ->
     vr_core B MT e pos F ((tq, Z.of_nat (length t) + 1) :: tmps) vr_sh2 (vr_sl3 F q c) (rlf tq) R1 Oc1 qv
       (k + EV_SUP_CHAIN_CLEAR Rc) kmax' (nm + 3) nmax' ly2 S2 W2 regs2 mem2 md2 ->
     vr_line B e q W2 mem2 -> vr_copy B e F c tp W2 mem2 ->
     SRr SEGS W2 (mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_sup_chain_clear)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros e pos F q c tp tmps rl Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc W regsc memc mdc id retk rlf Q
  He HC HL HCP Hl Hc R1 Hrk1 Hrk2 R10 Hid Hsf Hkev Hkmax Hnm32 Hnmax Hlv Hrlf CONT.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hd & Hperm & Hq).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HCS : SUP_CHAIN_CLEAR_STK + 208 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HCS0 : 0 <= SUP_CHAIN_CLEAR_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (vk_code_range lyc Sc _ Rc Oc Hrec) as Hcode.
assert (Ht : (length (snd (sup_chain_clear_m Rc id)) <= 28)%nat)
  by (unfold sup_chain_clear_m, daemon_shape; apply vk_stub_len; exact Hcode).
pose proof (dec_length id Hid) as Hdl.
pose proof (mo_malloc_nonneg MT MTL VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as Hmm.
pose proof (mo_free_nonneg MT MTL) as Hmf.
assert (HXM : XM_SUP_CHAIN_CLEAR MT Rc id <= 3 * mo_malloc MT VERBS_RECEIVE_REQ + 1 * mo_free MT).
{ unfold XM_SUP_CHAIN_CLEAR, XM_ARG_I, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. rewrite Hsf.
  pose proof (mo_malloc_mono MT MTL (Z.of_nat (length (dec id)) + 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ; lia)).
  pose proof (mo_malloc_mono MT MTL (Z.of_nat (length (snd (sup_chain_clear_m Rc id))) + 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ; lia)).
  lia. }
assert (HXM0 : 0 <= XM_SUP_CHAIN_CLEAR MT Rc id).
{ unfold XM_SUP_CHAIN_CLEAR, XM_ARG_I, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. rewrite Hsf.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (dec id)) + 1) ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_chain_clear_m Rc id))) + 1) ltac:(lia)).
  lia. }
assert (HEV : EV_SUP_CHAIN_CLEAR Rc = 4)
  by (unfold EV_SUP_CHAIN_CLEAR, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP; rewrite Hsf; reflexivity).
assert (HO : forall pn, In pn Oc -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
eapply (vk_stepF e pos F tmps (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc AF_sup_chain_clear
  SUP_CHAIN_CLEAR_STK (rec_fp Oc) (EV_SUP_CHAIN_CLEAR Rc) retk _ Q He HC R1 Hrk1 Hrk2 HCS0 HCS).
- exact (vk_rec_awr e pos lyc Sc W memc mdc Oc tmps He HAR Hperm).
- intros ch HPRE.
  exact (TSUP_CHAIN_CLEAR lyc Sc W regsc memc mdc ch id Rc Oc HPRE (vk_frm0 e He) (proj1 Henv) (proj1 (proj2 (proj2 Henv)))
    R10 Hid Hrec
    ltac:(pose proof (vk_frames e pos lyc Sc W memc mdc k He HJ); lia)
    (vk_nev e pos lyc Sc W memc mdc k (EV_SUP_CHAIN_CLEAR Rc) He HJ Hkev)
    (vk_live e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc
      (LIVE_SUP_CHAIN_CLEAR Rc id) He HC Hlv)
    (vri_meter_ok B MT e Sc k nm (XM_SUP_CHAIN_CLEAR MT Rc id) 3 1 (EV_SUP_CHAIN_CLEAR Rc) MTL He Hmet HXM
      ltac:(rewrite HEV; lia) ltac:(rewrite HEV; lia) Hkev)).
- intros _ ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
  pose proof (vk_rec_low lyc Sc W memc mdc Oc HAR HO a Ha). lia.
- intros fx' ly2 S2 W2 regs2 mem2 md2 Hfx HJ2 HJc HP HK.
  destruct HK as (R1' & t & qq & O1 & Em & Hq10 & Hqr & Hrec' & Ha1 & Hqin & Hqnot & HqO' & Hstr & Hkeep & Hall & _ & Hmo).
  destruct (vk_rec_core e pos F q c tp tmps rl (rlf qq) Rc R1' Oc O1 [(qq, Z.of_nat (length t) + 1)] qv k
    (k + EV_SUP_CHAIN_CLEAR Rc) kmax kmax' nm (nm + 3) nmax nmax' lyc Sc W regsc memc mdc ly2 S2 W2 regs2 mem2 md2
    SUP_CHAIN_CLEAR_STK (EV_SUP_CHAIN_CLEAR Rc) He HC HL HCP Hl Hc HJ2 HJc Hrec' Ha1) as (HC2 & HL2 & HCP2).
  + intros pn H1 H2. exact (proj1 (Hkeep pn H1 H2)).
  + intros pn Hpn. destruct (Hall pn Hpn) as [H|[H|H]]; [left; exact H | right; left; exact H |].
    right; right. rewrite H. left. reflexivity.
  + intros pn [<-|[]]. exact Hqin.
  + constructor; [intros []|constructor].
  + intros pn [<-|[]]. split.
    * intros Hin. destruct (in_dec pz_eq_dec (qq, Z.of_nat (length t) + 1) Oc) as [H|H]; [exact H|].
      exfalso. exact (Hqnot _ Hin H eq_refl).
    * intros Hin. apply HqO'. exact (in_map fst O1 _ Hin).
  + exact Hkmax.
  + exact (vri_meter_step MT e Sc S2 k nm _ 3 1 (EV_SUP_CHAIN_CLEAR Rc) MTL Hmet Hmo HXM
      ltac:(rewrite HEV; lia) ltac:(rewrite HEV; lia)).
  + exact Hnmax.
  + exact (vk_rv_after e regsc regs2 rl (rlf qq) qq HP Hrv Hq10 (Hrlf qq)).
  + cbn [app] in HC2. exact (CONT fx' R1' t qq _ ly2 S2 W2 regs2 mem2 md2 Hfx Em ltac:(lia) Hstr HC2 HL2 HCP2).
Qed.

End e.
End f.
End d.
