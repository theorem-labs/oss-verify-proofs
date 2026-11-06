(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: helpers of the segments S18 (worker_env), S19 (chain), S21 (pin_set) and S22
   (pin_accept) of the walk of verbs_receive on the ASan build of plugin-hostd/fuzz_command
   (lib/A/Prog/verbs_receive_iface.v): the transport of a boundary state across a run that writes no byte, the
   route facts of the four verbs, and the seed of the symbolic state at a route entry. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* ---------- the routes of the four verbs ---------- *)
Ltac vr_kill_route H :=
  unfold VRR.route, VRR.route_mid, VRR.route_tail, VRR.route_conn, VRR.route_cd in H;
  repeat match type of H with
  | context [if ?b then _ else _] => destruct b
  | context [match ?x with Some _ => _ | None => _ end] => destruct x
  | context [match ?x with [] => _ | _ :: _ => _ end] => destruct x
  end; try discriminate H.

Lemma vr_route_hd : forall v args lit r, VRR.route (v :: args) = r ->
  Verbs.list_eqb v lit = true -> VRR.route (lit :: args) = r.
Proof. intros v args lit r H E. apply Verbs.list_eqb_eq in E. subst v. exact H. Qed.

(* the verb of a route: the route of a word that is not the route's literal is another route *)
Lemma vr_route_env : forall v args, VRR.route (v :: args) = VRR.REnv -> v = Verbs.Lit.verb_worker_env.
Proof.
intros v args H. destruct (Verbs.list_eqb v Verbs.Lit.verb_worker_env) eqn:E; [apply Verbs.list_eqb_eq; exact E|].
exfalso. unfold VRR.route, VRR.route_mid in H. rewrite E in H. vr_kill_route H.
Qed.
Lemma vr_route_chain : forall v args, VRR.route (v :: args) = VRR.RChain -> v = Verbs.Lit.verb_chain.
Proof.
intros v args H. destruct (Verbs.list_eqb v Verbs.Lit.verb_chain) eqn:E; [apply Verbs.list_eqb_eq; exact E|].
exfalso. unfold VRR.route, VRR.route_mid in H. rewrite E in H. vr_kill_route H.
Qed.
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

(* the events of the route (verbs_receive_c.v:148-155) *)
Lemma vr_k1_simple : forall R D v args, Verbs.toks D = v :: args ->
  Verbs.list_eqb v Verbs.Lit.verb_chain = false -> Verbs.list_eqb v Verbs.Lit.verb_pin_set = false ->
  vr_k1 R D = 2 + ev_step R (vr_st D).
Proof. intros R D v args Ht E1 E2. unfold vr_k1, ev_route. rewrite Ht, E1, E2. reflexivity. Qed.
Lemma vr_k1_chain : forall R D args, Verbs.toks D = Verbs.Lit.verb_chain :: args ->
  vr_k1 R D = 2 + EV_CHAIN_WORDS R.
Proof. intros R D args Ht. unfold vr_k1, ev_route. rewrite Ht. reflexivity. Qed.
Lemma vr_k1_pinset : forall R D args, Verbs.toks D = Verbs.Lit.verb_pin_set :: args ->
  vr_k1 R D = 2 + (EV_PIN_SET_WORDS R (Verbs.line D) args + EV_SUP_RESP).
Proof. intros R D args Ht. unfold vr_k1, ev_route. rewrite Ht. reflexivity. Qed.

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
(* the regions a route reads: the copy pointer spilled at s1+56, and the word pointers tok[1..] in the frame array
   (s6 = F+32); each is read-only (empty write window) *)
Definition vr_rsp : YP09.region := YP09.mkRegion (Some 9%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition vr_rtok1 : YP09.region := YP09.mkRegion (Some 22%nat) 8 16 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition vr_rtok3 : YP09.region := YP09.mkRegion (Some 22%nat) 8 32 8 8
[YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 8 (SOff 35 0))].
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

Lemma vr_seed_sp : forall (W : world SEGS) (regs : bvmap 5 word) mem pc s1 c,
  getr regs (Z_to_bv 5 9) = w64 s1 -> 0 <= s1 -> s1 + 64 <= 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  aval_mem (rdW W mem) (s1 + 56) 8 c ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 c])) (mkSS pc sr_atoms [vr_rsp] None vr_nofacts)
   (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc s1 c H9 Hs0 Hs1 Hc Hsp.
assert (E9 : bv_unsigned (ew (Eimg (Ereg regs [Z_to_bv 64 c])) 9) = s1) by (apply vr_U_reg; [lia | exact H9 | lia]).
assert (E32 : ew (Eimg (Ereg regs [Z_to_bv 64 c])) 32 = Z_to_bv 64 c) by exact (vr_ew_extra regs _ 0 ltac:(lia)).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vr_rsp.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor]. vr_chunk E32 c.
- apply pairwise_disjoint_of_extents. unfold vr_rsp, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [zpairwise_disjoint zall_disjoint]. split; exact I.
- unfold facts_ok, vr_nofacts; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

Lemma vr_seed_sp_tok1 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc s1 c t p1,
  getr regs (Z_to_bv 5 9) = w64 s1 -> getr regs (Z_to_bv 5 22) = w64 t ->
  0 <= t -> t + 64 <= s1 + 56 -> s1 + 64 <= 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= p1 < 2 ^ 64 ->
  aval_mem (rdW W mem) (s1 + 56) 8 c -> aval_mem (rdW W mem) (t + 8) 8 p1 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 c; Z_to_bv 64 p1])) (mkSS pc sr_atoms [vr_rsp; vr_rtok1] None vr_nofacts)
   (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc s1 c t p1 H9 H22 Ht0 Hts Hs1 Hc Hp1 Hsp Hp1m.
set (E := Eimg (Ereg regs [Z_to_bv 64 c; Z_to_bv 64 p1])).
assert (E9 : bv_unsigned (ew E 9) = s1) by (apply vr_U_reg; [lia | exact H9 | lia]).
assert (E22 : bv_unsigned (ew E 22) = t) by (apply vr_U_reg; [lia | exact H22 | lia]).
assert (E32 : ew E 32 = Z_to_bv 64 c) by exact (vr_ew_extra regs _ 0 ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 p1) by exact (vr_ew_extra regs _ 1 ltac:(lia)).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, vr_rsp, vr_rtok1;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. vr_chunk E32 c.
  + rewrite E22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. vr_chunk E33 p1.
- apply pairwise_disjoint_of_extents. unfold vr_rsp, vr_rtok1, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E22.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- unfold facts_ok, vr_nofacts; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

Lemma vr_seed_sp_tok3 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc s1 c t p1 p2 p3,
  getr regs (Z_to_bv 5 9) = w64 s1 -> getr regs (Z_to_bv 5 22) = w64 t ->
  0 <= t -> t + 64 <= s1 + 56 -> s1 + 64 <= 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  0 <= p1 < 2 ^ 64 -> 0 <= p2 < 2 ^ 64 -> 0 <= p3 < 2 ^ 64 ->
  aval_mem (rdW W mem) (s1 + 56) 8 c -> aval_mem (rdW W mem) (t + 8) 8 p1 ->
  aval_mem (rdW W mem) (t + 16) 8 p2 -> aval_mem (rdW W mem) (t + 24) 8 p3 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 c; Z_to_bv 64 p1; Z_to_bv 64 p2; Z_to_bv 64 p3]))
   (mkSS pc sr_atoms [vr_rsp; vr_rtok3] None vr_nofacts)
   (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc s1 c t p1 p2 p3 H9 H22 Ht0 Hts Hs1 Hc Hp1 Hp2 Hp3 Hsp Hp1m Hp2m Hp3m.
set (E := Eimg (Ereg regs [Z_to_bv 64 c; Z_to_bv 64 p1; Z_to_bv 64 p2; Z_to_bv 64 p3])).
assert (E9 : bv_unsigned (ew E 9) = s1) by (apply vr_U_reg; [lia | exact H9 | lia]).
assert (E22 : bv_unsigned (ew E 22) = t) by (apply vr_U_reg; [lia | exact H22 | lia]).
assert (E32 : ew E 32 = Z_to_bv 64 c) by exact (vr_ew_extra regs _ 0 ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 p1) by exact (vr_ew_extra regs _ 1 ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 p2) by exact (vr_ew_extra regs _ 2 ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 p3) by exact (vr_ew_extra regs _ 3 ltac:(lia)).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, vr_rsp, vr_rtok3;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. vr_chunk E32 c.
  + rewrite E22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [vr_chunk E33 p1|]. constructor; [vr_chunk E34 p2|]. constructor; [vr_chunk E35 p3|]. constructor.
- apply pairwise_disjoint_of_extents. unfold vr_rsp, vr_rtok3, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E22.
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
