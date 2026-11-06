(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: helpers of the segments S21 (pin_set) and S22 (pin_accept) of the walk of
   verbs_receive on the ASan+UBSan build of plugin-hostd/fuzz_command (image B, lib/B/Prog/verbs_receive_iface.v):
   the route facts of the two verbs, the transport of a boundary state across a run that writes no byte, the seed of
   the symbolic state at a route entry, and what a boundary state keeps across a program call whose footprint is the
   recorder's statics and blocks. Ported from the A walk's lib/A/Prog/verbs_receive_s18_kit.v and
   verbs_receive_s18_call.v (a working branch); B's differences: B keeps tok = F+32 in the
   spill slot s1+40 and reloads it into s3 before an arm (A held it in s6), so the seeds read the slot s1+40 and tok[1]
   through a region based at the loaded value; the record names are lib/B/YF0m.v's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import socket_send_c xmalloc_c arg_s_c record_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* ---------- the routes of the two verbs ---------- *)
Ltac vr_kill_route H :=
  unfold VRR.route, VRR.route_mid, VRR.route_tail, VRR.route_conn, VRR.route_cd in H;
  repeat match type of H with
  | context [if ?b then _ else _] => destruct b
  | context [match ?x with Some _ => _ | None => _ end] => destruct x
  | context [match ?x with [] => _ | _ :: _ => _ end] => destruct x
  end; try discriminate H.

Lemma vr_route_pinset : forall v args, VRR.route (v :: args) = VRR.RPinset -> v = Verbs.Lit.verb_pin_set.
Proof.
intros v args H. destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_set) eqn:E; [apply Verbs.list_eqb_eq; exact E|].
exfalso. unfold VRR.route, VRR.route_mid in H. rewrite E in H. vr_kill_route H.
Qed.
Lemma vr_route_pinacc : forall v args, VRR.route (v :: args) = VRR.RPinacc -> v = Verbs.Lit.verb_pin_accept.
Proof.
intros v args H. destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_accept) eqn:E; [apply Verbs.list_eqb_eq; exact E|].
exfalso. unfold VRR.route, VRR.route_mid in H. rewrite E in H. vr_kill_route H.
Qed.

(* the step the dispatch takes on a route, from plan_route *)
Lemma vr_st_route : forall D v args, Verbs.toks D = v :: args ->
  vr_st D = VRR.plan_at (VRR.route (v :: args)) atoi_a (Verbs.line D) (v :: args).
Proof.
intros D v args Ht. unfold vr_st, Verbs.receive. rewrite Ht. cbn [fst].
apply VRR.plan_route. discriminate.
Qed.

(* the events of the route (B's verbs_receive_c.v:186-193) *)
Lemma vr_k1_simple : forall R D v args, Verbs.toks D = v :: args ->
  Verbs.list_eqb v Verbs.Lit.verb_chain = false -> Verbs.list_eqb v Verbs.Lit.verb_pin_set = false ->
  vr_k1 R D = 2 + ev_step R (vr_st D).
Proof. intros R D v args Ht E1 E2. unfold vr_k1, ev_route. rewrite Ht, E1, E2. reflexivity. Qed.
Lemma vr_k1_pinset : forall R D args, Verbs.toks D = Verbs.Lit.verb_pin_set :: args ->
  vr_k1 R D = 2 + (EV_PIN_SET_WORDS R (Verbs.line D) args + EV_SUP_RESP).
Proof. intros R D args Ht. unfold vr_k1, ev_route. rewrite Ht. reflexivity. Qed.

(* the handler leaves at least 5 events of the budget (B's events: lib/B/Prog/verbs_receive_s30_kit.v vr_k1_ev) *)
Lemma vr21_k1_ev : forall R D, vr_k1 R D + 5 <= ev_vr R D.
Proof.
intros R D. rewrite ev_vr_eq. unfold vr_k3, vr_k2, ev_after, EV_REPLY, EV_SOCKET_SEND, EV_XMALLOC.
destruct (vr_aft D) as [[i v]|]; [|lia].
unfold EV_SUP_AFTER_REPLY, EV_RECORD, rec_spill_frees, EV_ARG_S, EV_XMALLOC. destruct (Nat.ltb _ _); lia.
Qed.

(* ---------- readers that agree everywhere ---------- *)
Section rd.
Definition rd_same (rd rd' : reader) : Prop := forall a, rd' a = rd a.
Lemma aval_mem_same : forall rd rd' a n v, rd_same rd rd' -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v RS H k Hk. rewrite RS. exact (H k Hk). Qed.
Lemma abytes_same : forall rd rd' a l, rd_same rd rd' -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l RS H i Hi. rewrite RS. exact (H i Hi). Qed.
Lemma astr_same : forall rd rd' a s, rd_same rd rd' -> astr_atR rd a s -> astr_atR rd' a s.
Proof. intros rd rd' a s RS [H1 H2]. split; [exact (abytes_same rd rd' a _ RS H1) | exact H2]. Qed.
Lemma rdword_same : forall rd rd' a, rd_same rd rd' -> rdword rd' a = rdword rd a.
Proof. intros rd rd' a RS. unfold rdword. rewrite !RS. reflexivity. Qed.
Lemma rd32_same : forall rd rd' a v, rd_same rd rd' -> rd32 rd a v -> rd32 rd' a v.
Proof. intros rd rd' a v RS H k Hk. rewrite RS. exact (H k Hk). Qed.
Lemma atoks_same : forall rd rd' tok ptrs tks cb ncb, rd_same rd rd' ->
  atoks_atA rd tok ptrs tks cb ncb -> atoks_atA rd' tok ptrs tks cb ncb.
Proof.
intros rd rd' tok ptrs tks cb ncb RS (H8 & Hlen & Hp & Hw).
split; [exact H8|]. split; [exact Hlen|]. split.
- intros i p Hi. exact (aval_mem_same rd rd' _ 8 p RS (Hp i p Hi)).
- intros i p w Hi Hw'. destruct (Hw i p w Hi Hw') as (Hs & Hl & Hc1 & Hc2).
  split; [exact (astr_same rd rd' p w RS Hs) | split; [exact Hl | split; [exact Hc1 | exact Hc2]]].
Qed.
Lemma cmd_ro_ok_same : forall rd rd', rd_same rd rd' -> cmd_ro_ok rd -> cmd_ro_ok rd'.
Proof.
intros rd rd' RS [Hb Ht]. split.
- unfold cmd_ro_bytes in Hb |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; eapply (abytes_same rd rd' _ _ RS); eassumption.
- intros e He a Ha. rewrite RS. exact (Ht e He a Ha).
Qed.
Lemma cmd_got_ok_same : forall rd rd', rd_same rd rd' -> cmd_got_ok rd -> cmd_got_ok rd'.
Proof.
intros rd rd' RS (H1 & H2 & H3 & H4).
split; [|split; [|split]]; eapply (aval_mem_same rd rd' _ _ _ RS); eassumption.
Qed.
End rd.

(* the GOT words are in cmd_ro_ok (B's CmdRo.v RO_ptr_a6bc8 .. RO_ptr_a6be0; lib/B/Prog/verbs_receive_s30_kit.v) *)
Lemma vr21_aval_of_bytes : forall (rd : reader) a (l : list byte) v,
abytes_atR rd a l -> length l = 8%nat -> (forall k, (k < 8)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = le_byte v 8 k) ->
aval_mem rd a 8 v.
Proof. intros rd a l v H Hl Hk k Hk8. rewrite (H k ltac:(lia)). rewrite Hk by exact Hk8. reflexivity. Qed.
Lemma vr21_got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb. decompose [and] Hb. clear Hb.
unfold cmd_got_ok. split; [|split; [|split]];
(eapply vr21_aval_of_bytes; [eassumption | reflexivity |];
 intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia).
Qed.

(* the trimmed line fits in strndup's block (q, l+1) *)
Lemma vr_find_upto0 : forall D, match StrFun.find_byte 0 D with Some i => firstn i D | None => D end = Verbs.upto0 D.
Proof.
unfold Verbs.upto0. induction D as [|x D IH]; [reflexivity|]. cbn [StrFun.find_byte Verbs.upto].
destruct (bv_unsigned x =? 0); [reflexivity|].
destruct (StrFun.find_byte 0 D) as [i|]; cbn [firstn]; f_equal; exact IH.
Qed.
Lemma vr_line_le_l : forall D, Z.of_nat (length (Verbs.line D)) <= StrFun.strnlen_res (Z.of_nat (length D)) D.
Proof.
intros D. unfold StrFun.strnlen_res. rewrite Nat2Z.id, firstn_all.
assert (L1 : (length (Verbs.line D) <= length (Verbs.upto0 D))%nat).
{ unfold Verbs.line, Verbs.trim. rewrite length_rev. pose proof (VRR.dropw_len Verbs.is_trail (rev (Verbs.upto0 D))) as H.
  rewrite length_rev in H. exact H. }
pose proof (vr_find_upto0 D) as E.
destruct (StrFun.find_byte 0 D) as [i|]; rewrite <- E in L1; [rewrite length_firstn in L1|]; lia.
Qed.

(* the word array under a reader that agrees on the array and on the copy block *)
Lemma vr_atoks_agree : forall (rd rd' : reader) tok ptrs tks cb ncb,
atoks_atA rd tok ptrs tks cb ncb ->
(forall k, 0 <= k < 8 * Z.of_nat (length ptrs) -> rd' (tok + k) = rd (tok + k)) ->
(forall k, 0 <= k < ncb -> rd' (cb + k) = rd (cb + k)) ->
atoks_atA rd' tok ptrs tks cb ncb.
Proof.
intros rd rd' tok ptrs tks cb ncb (H8 & Hlen & Hp & Hw) HT HB.
split; [exact H8|]. split; [exact Hlen|]. split.
- intros i p Hi. apply (aval_mem_agree rd rd' _ 8 _ (Hp i p Hi)).
  assert (Hi' : (i < length ptrs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  replace (tok + 8 * Z.of_nat i + k) with (tok + (8 * Z.of_nat i + k)) by lia. apply HT. lia.
- intros i p w Hi Hw'. destruct (Hw i p w Hi Hw') as (Hs & Hl & Hc1 & Hc2).
  split; [|split; [exact Hl | split; [exact Hc1 | exact Hc2]]].
  apply (astr_atR_agree rd rd' _ _ (cb + ncb - p) Hs); [lia|].
  intros k Hk. replace (p + k) with (cb + (p - cb + k)) by lia. apply HB. lia.
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

Lemma vr_aview_wrap : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a.
assert (E : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity. }
unfold aview, mbyte. rewrite E. reflexivity.
Qed.
Lemma vr_rd_same_of : forall H H' (m m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS H' m' a = aview SEGS H m a) -> rd_same (aview SEGS H m) (aview SEGS H' m').
Proof.
intros H H' m m' K a. rewrite (vr_aview_wrap H' m' a), (vr_aview_wrap H m a). apply K.
apply Z.mod_pos_bound. lia.
Qed.

Lemma vr_val_mem_of_aval : forall (W : world SEGS) mem a n v,
aval_mem (aview SEGS (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte SEGS (w_H W) mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma vr_frame_same : forall ly W W' m m' pos F sh, rd_same (rdW W m) (rdW W' m') ->
  vr_frame ly W m pos F sh -> vr_frame ly W' m' pos F sh.
Proof.
intros ly W W' m m' pos F sh RS (H1 & H2 & H3). split; [exact H1|]. split.
- rewrite (rdword_same _ _ _ RS). exact H2.
- intros i Hi. rewrite RS. exact (H3 i Hi).
Qed.
Lemma vr_saved_same : forall e W W' m m', rd_same (rdW W m) (rdW W' m') -> vr_saved e W m -> vr_saved e W' m'.
Proof. intros e W W' m m' RS H j r Hj. exact (aval_mem_same _ _ _ _ _ RS (H j r Hj)). Qed.
Lemma vr_spill_same : forall e W W' m m' l, rd_same (rdW W m) (rdW W' m') -> vr_spill e W m l -> vr_spill e W' m' l.
Proof.
intros e W W' m m' l RS H. unfold vr_spill in *. eapply Forall_impl; [|exact H].
intros ov Hov. exact (aval_mem_same _ _ _ _ _ RS Hov).
Qed.
Lemma vr_env_same : forall W W' m m', rd_same (rdW W m) (rdW W' m') ->
  vr_env B W m -> vr_env B W' m'.
Proof.
intros W W' m m' RS (H1 & H2 & H3 & H4 & H5 & H6).
split; [intros a Hr Ho He; rewrite RS; exact (H1 a Hr Ho He)|].
split; [exact (cmd_got_ok_same _ _ RS H2)|].
split; [exact (cmd_ro_ok_same _ _ RS H3)|].
split; [destruct H4 as [G1 (can & G2)]; split; [rewrite (rdword_same _ _ _ RS); exact G1 | exists can; rewrite (rdword_same _ _ _ RS); exact G2]|].
split; [rewrite RS; exact H5|].
destruct H6 as (ev & Hev). exists ev. exact (rd32_same _ _ _ _ RS Hev).
Qed.
Lemma vr_line_same : forall e q W W' m m', rd_same (rdW W m) (rdW W' m') -> vr_line B e q W m -> vr_line B e q W' m'.
Proof. intros e q W W' m m' RS [H1 H2]. split; [exact H1 | exact (astr_same _ _ _ _ RS H2)]. Qed.
Lemma vr_copy_same : forall e F c tp W W' m m', rd_same (rdW W m) (rdW W' m') ->
  vr_copy B e F c tp W m -> vr_copy B e F c tp W' m'.
Proof. intros e F c tp W W' m m' RS [H1 H2]. split; [exact H1 | exact (atoks_same _ _ _ _ _ _ _ RS H2)]. Qed.
Lemma vr_rec_same : forall ly S (W W' : world SEGS) m m' R O, rd_same (rdW W m) (rdW W' m') ->
  rec_repA B ly S (rdW W m) R O -> rec_repA B ly S (rdW W' m') R O.
Proof.
intros ly S W W' m m' R O RS H.
apply (rec_repA_agree B ly S ly S _ _ R O H (fun _ _ Hb => Hb)); intros; apply RS.
Qed.

(* a boundary state, after a run that wrote no byte and moved no block *)
Lemma vr_core_same : forall e pos F tmps sh sl rl rl' Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc Wc regsc memc mdc regs' mem' md',
  vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(4, pos)] lyc Sc Wc mem' md' k ->
  rd_same (rdW Wc memc) (rdW Wc mem') ->
  vr_rv regs' (vr_base B e ++ rl') -> k <= kmax' -> nm <= nmax' ->
  vr_core B MT e pos F tmps sh sl rl' Rc Oc qv k kmax' nm nmax' lyc Sc Wc regs' mem' md'.
Proof.
intros e pos F tmps sh sl rl rl' Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc Wc regsc memc mdc regs' mem' md'
  (HJ & Hk & HM & Hnm & HFR & HRV & HSV & HSP & HENV & HREC & HnD & HPERM & HQ) HJ' RS HRV' Hk' Hnm'.
split; [exact HJ'|]. split; [exact Hk'|]. split; [exact HM|]. split; [exact Hnm'|].
split; [exact (vr_frame_same _ _ _ _ _ _ _ _ RS HFR)|].
split; [exact HRV'|].
split; [exact (vr_saved_same _ _ _ _ _ RS HSV)|].
split; [exact (vr_spill_same _ _ _ _ _ _ RS HSP)|].
split; [exact (vr_env_same _ _ _ _ RS HENV)|].
split; [exact (vr_rec_same _ _ _ _ _ _ _ _ RS HREC)|].
split; [exact HnD|]. split; [exact HPERM|].
exact (aval_mem_same _ _ _ _ _ RS HQ).
Qed.

(* the frame's stack pointer s1 = (sp0 - 192) & -32, below the real frame and above the heap *)
Lemma vr_s1_gen : forall sp0, sp0 mod 16 = 0 ->
  (sp0 - 192 - (sp0 - 192) mod 32) + 192 <= sp0 <= (sp0 - 192 - (sp0 - 192) mod 32) + 208 /\
  (sp0 - 192 - (sp0 - 192) mod 32) mod 32 = 0.
Proof.
intros sp0 H16.
pose proof (Z.div_mod (sp0 - 192) 32 ltac:(lia)) as D32.
pose proof (Z.mod_pos_bound (sp0 - 192) 32 ltac:(lia)) as B32.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as D16.
replace (sp0 - 192 - (sp0 - 192) mod 32) with (32 * ((sp0 - 192) / 32)) by lia.
split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma vr_ent_stk : forall e, vr_ent B MT e ->
  alloc_ceiling + 16384 <= vr_s1 e /\ vr_s1 e + 192 <= vr_sp0 e <= vr_s1 e + 208 /\ vr_s1 e mod 32 = 0 /\
  vr_sp0 e <= 2 ^ 47 /\ vr_sp0 e mod 16 = 0 /\ alloc_ceiling + VERBS_RECEIVE_STK <= vr_sp0 e.
Proof.
intros e He. unfold vr_ent in He. cbv zeta in He. destruct He as (HPRE & _).
destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HSTK : 192 + 16 + 4 * ESTACK <= VERBS_RECEIVE_STK).
{ unfold VERBS_RECEIVE_STK. pose proof (Z.le_max_r VR_CALLEE_STK (Z.max ASTACK (4 * ESTACK))).
  pose proof (Z.le_max_r ASTACK (4 * ESTACK)). lia. }
assert (HES : ESTACK = 4096) by reflexivity.
destruct (vr_s1_gen (spZ (e_regs e)) Hal16) as [HB Hm].
unfold vr_s1, vr_sp0. lia.
Qed.
Lemma vr_rv_in : forall regs l r v, vr_rv regs l -> In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs l r v H Hin. unfold vr_rv in H. rewrite Forall_forall in H. exact (H (r, v) Hin). Qed.
Lemma vr_spill_in : forall e (W : world SEGS) mem l o v, vr_spill e W mem l -> In (o, v) l ->
  aval_mem (rdW W mem) (vr_s1 e + o) 8 v.
Proof. intros e W mem l o v H Hin. unfold vr_spill in H. rewrite Forall_forall in H. exact (H (o, v) Hin). Qed.
(* a block of the boundary's own list is live *)
Lemma vr_tmp_live : forall e lyc Sc Oc tmps b, Permutation (ablocks B lyc Sc) (Oc ++ tmps ++ e_rest e) ->
  In b tmps -> In b (ablocks B lyc Sc).
Proof.
intros e lyc Sc Oc tmps b HP Hin. apply (Permutation_in _ (Permutation_sym HP)).
apply in_or_app. right. apply in_or_app. left. exact Hin.
Qed.
(* ---------- the symbolic state at a route entry ---------- *)
(* the regions a B route reads: the spill slot s1+40 (tok = F+32, atom 32) and tok[1] (atom 33), the second based
   at the value the first holds (B reloads tok with `ld s3,40(s1)`); each is read-only (empty write window) *)
Definition vr_rsp40 : YP09.region := YP09.mkRegion (Some 9%nat) 40 48 40 40 [YP09.mkChunk 40 (CVal 8 (SOff 32 0))].
Definition vr_rtk1 : YP09.region := YP09.mkRegion (Some 32%nat) 8 16 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition vr_nofacts : facts := mkFacts [] [] [].

Lemma vr_ew_reg : forall (regs : bvmap 5 word) extra n, (n < 32)%nat ->
  ew (Eimg (Ereg regs extra)) n = getr regs (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros regs extra n Hn. apply ew_Eimg_Ereg_nat. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32. rewrite Z.mod_small; lia.
Qed.
Lemma vr_ew_extra : forall (regs : bvmap 5 word) extra j, (j < 100)%nat ->
  ew (Eimg (Ereg regs extra)) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j Hj. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma vr_U_reg : forall (regs : bvmap 5 word) extra n v, (n < 32)%nat ->
  getr regs (Z_to_bv 5 (Z.of_nat n)) = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew (Eimg (Ereg regs extra)) n) = v.
Proof. intros regs extra n v Hn H Hv. rewrite vr_ew_reg by exact Hn. rewrite H. apply unsigned_lit_small. exact Hv. Qed.

Ltac vr_chunk E32 v :=
  apply (chunk_ok_val SEGS _ _ _ _ 8 _ v);
  [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
  | change (Z.of_N 8) with 8; lia
  | apply vr_val_mem_of_aval; assumption ].

Lemma vr_seed0 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc sr_atoms [] None vr_nofacts)
   (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. exact I.
- unfold facts_ok, vr_nofacts; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

(* the spill slot s1+40 (tok, atom 32) *)
Lemma vr_seed_t : forall (W : world SEGS) (regs : bvmap 5 word) mem pc s1 t,
  getr regs (Z_to_bv 5 9) = w64 s1 -> 0 <= s1 -> s1 + 48 <= 2 ^ 64 -> 0 <= t < 2 ^ 64 ->
  aval_mem (rdW W mem) (s1 + 40) 8 t ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 t])) (mkSS pc sr_atoms [vr_rsp40] None vr_nofacts)
   (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc s1 t H9 Hs0 Hs1 Ht Hsp.
assert (E9 : bv_unsigned (ew (Eimg (Ereg regs [Z_to_bv 64 t])) 9) = s1) by (apply vr_U_reg; [lia | exact H9 | lia]).
assert (E32 : ew (Eimg (Ereg regs [Z_to_bv 64 t])) 32 = Z_to_bv 64 t) by exact (vr_ew_extra regs _ 0 ltac:(lia)).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vr_rsp40.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor]. vr_chunk E32 t.
- apply pairwise_disjoint_of_extents. unfold vr_rsp40, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [zpairwise_disjoint zall_disjoint]. split; exact I.
- unfold facts_ok, vr_nofacts; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

(* the spill slot s1+40 (tok, atom 32) and tok[1] (atom 33), read through the loaded tok *)
Lemma vr_seed_t1 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc s1 t p1,
  getr regs (Z_to_bv 5 9) = w64 s1 -> 0 <= s1 ->
  0 <= t -> t + 16 <= s1 + 40 -> s1 + 48 <= 2 ^ 64 -> 0 <= p1 < 2 ^ 64 ->
  aval_mem (rdW W mem) (s1 + 40) 8 t -> aval_mem (rdW W mem) (t + 8) 8 p1 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 t; Z_to_bv 64 p1])) (mkSS pc sr_atoms [vr_rsp40; vr_rtk1] None vr_nofacts)
   (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc s1 t p1 H9 Hs0 Ht0 Hts Hs1 Hp1 Hsp Hp1m.
set (E := Eimg (Ereg regs [Z_to_bv 64 t; Z_to_bv 64 p1])).
assert (E9 : bv_unsigned (ew E 9) = s1) by (apply vr_U_reg; [lia | exact H9 | lia]).
assert (E32 : ew E 32 = Z_to_bv 64 t) by exact (vr_ew_extra regs _ 0 ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 p1) by exact (vr_ew_extra regs _ 1 ltac:(lia)).
assert (E32u : bv_unsigned (ew E 32) = t) by (rewrite E32; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, vr_rsp40, vr_rtk1;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. vr_chunk E32 t.
  + rewrite E32u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. vr_chunk E33 p1.
- apply pairwise_disjoint_of_extents. unfold vr_rsp40, vr_rtk1, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E32u.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- unfold facts_ok, vr_nofacts; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.
(* the values of a branch's operands *)
Lemma vr_U_SOff_reg : forall (regs : bvmap 5 word) extra n v, (n < 32)%nat ->
  getr regs (Z_to_bv 5 (Z.of_nat n)) = w64 v -> 0 <= v < 2 ^ 64 -> U (Eimg (Ereg regs extra)) (SOff n 0) = v.
Proof.
intros regs extra n v Hn H Hv. rewrite U_SOff, (vr_U_reg regs extra n v Hn H Hv), Z.add_0_r.
unfold zcanon, M64. apply Z.mod_small. exact Hv.
Qed.
Lemma vr_U_lit : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. unfold U. cbn [sv_denot]. apply unsigned_lit_small. exact Hz. Qed.

End e.

(* ---------------------------------------------------------------------------------------------------------------
   What a boundary state keeps across a program call whose footprint is the recorder's statics and blocks (the
   callee's journal, YCbq.v ajournal): the real stack above the callee's window, the image off the recorder statics,
   the walk's own blocks, the side-stack frame, and from them vr_frame, vr_saved, vr_spill, vr_env, the quit flag,
   vr_line and vr_copy (A's verbs_receive_s18_call.v). *)
Section e1.
Variable B : asyms.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the recorder's footprint of a recorder callee: g_rec, record.spill and the recorder's blocks *)
Definition vr_fp1 (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
Lemma vr_notFP1 : forall O a, (a < A_G_REC \/ A_G_REC + REC_SIZE <= a) -> (a < A_REC_SPILL \/ A_REC_SPILL + SC_SIZE <= a) ->
  (forall p n, In (p, n) O -> ~ (p <= a < p + req_size n)) -> ~ inFP (vr_fp1 O) a.
Proof.
intros O a H1 H2 H3 Hf. unfold vr_fp1 in Hf. apply inFP_cons in Hf as [Hf | Hf]; [lia|].
apply inFP_cons in Hf as [Hf | Hf]; [lia|].
destruct (inFP_ablocks_fp_inv O a Hf) as (p & n & Hpn & Hr). exact (H3 p n Hpn Hr).
Qed.
Lemma vr_fp1_closed : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) -> ~ YI16.sink_open_fp (vr_fp1 O).
Proof.
intros ly S W mem md O HAR HO (r & Hr & H0). unfold vr_fp1 in Hr.
destruct Hr as [<- | [<- | Hr]]; [cbn in H0; unfold A_G_REC in H0; lia | cbn in H0; unfold A_REC_SPILL in H0; lia|].
unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). cbn [fst snd] in H0.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & H4 & _). lia.
Qed.
(* an image byte off the recorder statics is off the footprint *)
Lemma vr_img_spared : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) -> 0x10000 <= a < 0x606000 ->
  (a < A_G_REC \/ A_G_REC + REC_SIZE <= a) -> (a < A_REC_SPILL \/ A_REC_SPILL + SC_SIZE <= a) ->
  fp_spares (vr_fp1 O) a.
Proof.
intros ly S W mem md O a HAR HO Ha H1 H2. apply fp_spares_closed; [exact (vr_fp1_closed _ _ _ _ _ O HAR HO)|].
apply vr_notFP1; [exact H1 | exact H2|]. intros p n Hpn Hr.
pose proof (blk_off_imgP B ly S W mem md p n HAR (HO _ Hpn)) as Hoff. unfold off_img in Hoff. lia.
Qed.

Section call.
(* the callee's journal from the state at the call (lyc, Sc, W, memc) to the state at its return *)
Variables (lyc : alayout) (Sc : astate) (W W2 : world SEGS) (memc mem2 : word -> option byte) (mdc md2 : Model).
Variables (ly2 : alayout) (S2 : astate) (STK1 s1 EV1 : Z) (O : list (Z * Z)).
Hypothesis HJc : ajournal SEGS B STK1 s1 (vr_fp1 O) lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1.
Hypothesis HAR : AR SEGS B lyc Sc W memc mdc.
Hypothesis HO : forall pn, In pn O -> In pn (ablocks B lyc Sc).
Hypothesis HSTK1 : 0 <= STK1.

(* the real stack above the callee's window *)
Lemma vr_call_stack : forall a, alloc_ceiling <= a < 2 ^ 64 -> s1 <= a -> rdW W2 mem2 a = rdW W memc a.
Proof using HJc HAR HO LAWS.
intros a Ha Hs. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof asan_consts as (CR & _).
apply F1; [lia | lia|]. apply vr_notFP1; [unfold A_G_REC, REC_SIZE; lia | unfold A_REC_SPILL, SC_SIZE; lia|].
intros p n Hpn Hr. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & _ & Hc & _). lia.
Qed.
(* an image byte that is neither the runtime's, nor errno, nor a recorder static *)
Lemma vr_call_img : forall a, in_img SEGS a -> 0x10000 <= a < 0x606000 ->
  ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  (a < A_G_REC \/ A_G_REC + REC_SIZE <= a) -> (a < A_REC_SPILL \/ A_REC_SPILL + SC_SIZE <= a) ->
  rdW W2 mem2 a = rdW W memc a.
Proof using HJc HAR HO LAWS.
intros a Hi Ha Ho He H1 H2. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
exact (F3 a Hi Ho He (vr_img_spared _ _ _ _ _ O a HAR HO Ha H1 H2)).
Qed.
(* a byte of a live block that is none of the recorder's and still live *)
Lemma vr_call_block : forall p n i, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> ~ In (p, n) O ->
  0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W memc (p + i).
Proof using HJc HAR HO LAWS.
intros p n i H1 H2 Hn Hi. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i H1 H2 Hi).
apply vr_notFP1.
- pose proof (blk_off_imgP B lyc Sc W memc mdc p n HAR H1) as Hoff. unfold off_img, A_G_REC, REC_SIZE in *. lia.
- pose proof (blk_off_imgP B lyc Sc W memc mdc p n HAR H1) as Hoff. unfold off_img, A_REC_SPILL, SC_SIZE in *. lia.
- intros b m Hbm Hr. assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hbm; exact (Hn Hbm)).
  pose proof (sep_blocks SEGS B LAWS lyc Sc W memc mdc b m p n HAR (HO _ Hbm) H1 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* a byte of a side-stack frame of the caller, or of its shadow *)
Lemma vr_call_frame : forall cid pos a, In (cid, pos) (frames Sc) ->
  (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
  rdW W2 mem2 a = rdW W memc a.
Proof using HJc HAR HO LAWS.
intros cid pos a Hin Hr. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
apply (F4 cid pos a Hin Hr).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfapp).
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Hoff. unfold off_img in Hoff.
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
pose proof asan_consts as (CR & _).
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(unfold kHighMemEnd; lia)) as Hsa.
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
apply vr_notFP1.
- destruct Hr as [Hr|Hr]; unfold A_G_REC, REC_SIZE, kLowMemEnd in *; lia.
- destruct Hr as [Hr|Hr]; unfold A_REC_SPILL, SC_SIZE, kLowMemEnd in *; lia.
- intros b m Hbm Hb.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR (HO _ Hbm)) as (_ & _ & _ & [Hh1 Hh2] & _).
  pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc b m cid pos HAR (HO _ Hbm) Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(unfold kHighMemEnd; lia)).
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfb).
  unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *.
  destruct Hr as [Hr|Hr]; lia.
Qed.

(* the parts of a boundary state that live in the real frame, the side-stack frame, the image, the walk's blocks *)
Lemma vr_call_vrframe : forall pos F sh, In (4, pos) (frames Sc) ->
  vr_frame lyc W memc pos F sh -> vr_frame ly2 W2 mem2 pos F sh.
Proof using HJc HAR HO LAWS.
intros pos F sh Hin (HF & Hfl & Hsh).
pose proof HJc as (_ & Hly & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly) as (_ & Efa & _).
assert (EF : ly_F ly2 = ly_F lyc) by (destruct Hly as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (HB1 : fs_frame_bytes 4 = 1024) by reflexivity.
split; [rewrite Efa; exact HF|]. split.
- assert (Efl : flag_addr ly2 4 pos = flag_addr lyc 4 pos) by (unfold flag_addr; rewrite EF; reflexivity).
  rewrite Efl, <- Hfl. apply rdword_ext. intros kk Hkk.
  apply (vr_call_frame 4 pos (F + 1016 + kk) Hin). left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite <- HF, HB1. lia.
- intros i Hi. rewrite <- (Hsh i Hi). apply (vr_call_frame 4 pos _ Hin). right. unfold in_zr. cbn [fst snd].
  rewrite <- HF, HB1. change (1024 / 8) with 128. lia.
Qed.
Lemma vr_call_saved : forall e, alloc_ceiling <= s1 -> s1 + 192 <= vr_sp0 e -> vr_sp0 e <= 2 ^ 47 ->
  vr_saved e W memc -> vr_saved e W2 mem2.
Proof using HJc HAR HO LAWS.
intros e Hc Hs Ht H j r Hj k Hk.
assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
cbn [length vr_saved_regs] in Hj13.
rewrite vr_call_stack by lia. exact (H j r Hj k Hk).
Qed.
Lemma vr_call_spill : forall e l, s1 = vr_s1 e -> alloc_ceiling <= s1 -> s1 + 192 <= 2 ^ 64 ->
  Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 192) l -> vr_spill e W memc l -> vr_spill e W2 mem2 l.
Proof using HJc HAR HO LAWS.
intros e l Hs Hc Ht Hl H. unfold vr_spill in *. rewrite Forall_forall in *. intros [o v] Hin. cbn [fst snd].
intros k Hk. pose proof (Hl _ Hin) as Ho. cbn [fst snd] in Ho.
rewrite vr_call_stack by lia. exact (H _ Hin k Hk).
Qed.
Lemma vr_call_quit : vr_prog_unowned B -> forall v,
  aval_mem (rdW W memc) A_G_QUITTING 4 v -> aval_mem (rdW W2 mem2) A_G_QUITTING 4 v.
Proof using HJc HAR HO LAWS.
intros PU v H k Hk.
assert (Hf : inFP cmd_PG (A_G_QUITTING + Z.of_nat k)).
{ unfold cmd_PG. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. left. lia. }
destruct (PU _ Hf) as (Hi & Ho & He).
rewrite vr_call_img; [exact (H k Hk) | exact Hi | unfold A_G_QUITTING; lia | exact Ho | exact He
| unfold A_G_QUITTING, A_G_REC, REC_SIZE; lia | unfold A_G_QUITTING, A_REC_SPILL, SC_SIZE; lia].
Qed.
Lemma vr_call_env : vr_relro_img -> vr_pg_not_ro -> vr_ro_of_aro B -> vr_rec_cells B ->
  vr_env B W memc -> vr_env B W2 mem2.
Proof using HJc HAR HO LAWS.
intros RRO RPG ROA RECC (HRO & _ & _ & _ & _ & _).
pose proof HJc as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (HRO2 : arodata_okP SEGS RLO RHI B (rdW W2 mem2)).
{ intros a Hro Ho He.
  assert (Hi : in_img SEGS a)
    by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (RRO a Hr)]).
  rewrite (F3 a Hi Ho He); [exact (HRO a Hro Ho He)|].
  apply fp_spares_closed; [exact (vr_fp1_closed _ _ _ _ _ O HAR HO)|].
  apply vr_notFP1.
  - destruct (Z_lt_le_dec a A_G_REC) as [Hl|Hl]; [left; exact Hl|].
    destruct (Z_lt_le_dec a (A_G_REC + REC_SIZE)) as [Hh|Hh]; [|right; exact Hh].
    exfalso. apply (RPG a); [|exact Hro]. unfold cmd_PG. apply inFP_cons. left. unfold A_G_REC, REC_SIZE in *. lia.
  - destruct (Z_lt_le_dec a A_REC_SPILL) as [Hl|Hl]; [left; exact Hl|].
    destruct (Z_lt_le_dec a (A_REC_SPILL + SC_SIZE)) as [Hh|Hh]; [|right; exact Hh].
    exfalso. apply (RPG a); [|exact Hro]. unfold cmd_PG. apply inFP_cons. right. apply inFP_cons. left.
    unfold A_REC_SPILL, SC_SIZE in *. lia.
  - intros p n Hpn Hr. exact (blk_img SEGS B LAWS _ _ _ _ _ p n a HAR (HO _ Hpn) Hr Hi). }
pose proof (ROA ly2 S2 W2 mem2 md2 HAR2 HRO2) as HCRO2.
destruct (RECC ly2 S2 W2 mem2 md2 HAR2) as (HFL2 & HAG2 & HEV2).
split; [exact HRO2|]. split; [exact (vr21_got_of_ro _ HCRO2)|]. split; [exact HCRO2|].
split; [exact HAG2|]. split; [exact HFL2 | exact HEV2].
Qed.
Lemma vr_call_line : forall e q, vr_line B e q W memc -> In (vr_lb e q) (ablocks B lyc Sc) ->
  In (vr_lb e q) (ablocks B ly2 S2) -> ~ In (vr_lb e q) O ->
  Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e) -> vr_line B e q W2 mem2.
Proof using HJc HAR HO LAWS.
intros e q [Hf Hs] H1 H2 Hn Hlen. split; [exact Hf|]. unfold vr_lb in *.
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [_ Hr].
apply (astr_atR_agree _ _ q _ (vr_l (e_n e) (e_D e) + 1) Hs); [lia|].
intros k Hk. apply (vr_call_block q _ k H1 H2 Hn). lia.
Qed.
Lemma vr_call_copy : forall e pos F c tp, F = frame_addr lyc 4 pos -> In (4, pos) (frames Sc) ->
  vr_copy B e F c tp W memc -> In (vr_cb e c) (ablocks B lyc Sc) -> In (vr_cb e c) (ablocks B ly2 S2) ->
  ~ In (vr_cb e c) O -> vr_copy B e F c tp W2 mem2.
Proof using HJc HAR HO LAWS.
intros e pos F c tp HF Hin [Hf Ht] H1 H2 Hn. split; [exact Hf|]. unfold vr_cb in *.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [_ Hr].
pose proof Ht as (_ & Hlen & _).
pose proof (Verbs.toks_length (e_D e)) as Htl.
apply (vr_atoks_agree _ _ _ _ _ _ _ Ht).
- intros k Hk. apply (vr_call_frame 4 pos _ Hin). left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite <- HF.
  change (fs_frame_bytes 4) with 1024. rewrite Hlen in Hk. lia.
- intros k Hk. apply (vr_call_block c _ k H1 H2 Hn). lia.
Qed.

End call.
End e1.
End f.
End d.

(* every region of these walks' states is read-only *)
Ltac vr_awr := repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* a register of the state the symbolic state HS describes, as the value of its symbolic expression *)
Ltac vr_sreg HS :=
  rewrite (st_ok_pi_restrict_reg _ _ _ _ _ HS);
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr) = _ =>
    let v := eval vm_compute in (sr_get a rr) in change (sr_get a rr) with v end;
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
Ltac vr_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac vr_unchanged sg UN HFr :=
  pose proof (kept_of_frame (segs := sg) _ _ _ _ _ (fun _ => False) HFr
  ltac:(let b := fresh "b" in let wl := fresh "wl" in let wh := fresh "wh" in let x := fresh "x" in
        let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
        intros b wl wh x Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn in Hrr; lia|]); destruct Hin)) as UN.
