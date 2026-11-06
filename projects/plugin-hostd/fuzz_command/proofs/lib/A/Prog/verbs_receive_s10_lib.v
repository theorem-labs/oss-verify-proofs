(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the shared part of the segments S10 REMOVE, S11 WLIST and S13 RESET of the walk
   of verbs_receive on the ASan build of plugin-hostd/fuzz_command (interface lib/A/Prog/verbs_receive_iface.v). Each
   route tests the word count, may call the atoi wrapper (S10), loads spill slots of the real frame, calls one
   recorder function and reaches a join (vr_hd) or a refusal stub (vr_pr). The pieces are copied, under the module
   VRL10, from the S08/S09/S12 arm (verbs_receive_s08_lib.v and
   verbs_receive_s12.v) and ported to the interface on the fixed statements:
   - reader transports (vr_core_same) and the transports across the atoi wrapper (vr_core_kx);
   - the symbolic state seeded with the spill slots of the real frame and tok[1] as regions (vr_seed_sp, vr_seed_spt);
   - the refusal exit (vr_pr_mk) and the join from the state after the call (vr_hd_of_aft);
   - the generic call arm vr_call_arm: from the callee's entry (vr_cs) through the callee's contract (rc_post, with
     PaFx's cl_callS_wideF; the frame chain at s0 = sp0 by achain_push on the entry's chain, vr_chain) to the state
     at the return address (vr_aft), which the segment's continuation takes to the join. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import Setoid Morphisms.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
sup_resp_c sup_reply_code_c answer_c hand_back_c xstrdup_c arg_i_c reply_c socket_send_c sup_after_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaNoChain verbs_receive_live PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module VRL10.
Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.
Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.

(* ---------------------------------------------------------------------------------------------------------------
   The symbolic states: at a return pc the registers alone; with the spill slots of the real frame (base s1, the
   slots of vr_sl3) as a region, and with tok[1] (base s6 = F + 32, offset 8) as a second one. The values the slots
   hold are the extra atoms 32.. (F, its shadow and shadow + 4, the copy c, the line q, tok[1]). *)
Definition ss_ret (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Definition vr_xt (F c q t1 : Z) : list word := map (Z_to_bv 64) [F; shadow_addr F; shadow_addr F + 4; c; q; t1].
Definition rg_spill : YP09.region := YP09.mkRegion (Some 9%nat) 0 80 0 0
  [YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 32 32)); YP09.mkChunk 24 (CVal 8 (SOff 36 0));
   YP09.mkChunk 32 (CVal 8 (SOff 34 0)); YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 48 (CVal 8 (SOff 32 0));
   YP09.mkChunk 56 (CVal 8 (SOff 35 0)); YP09.mkChunk 72 (CVal 8 (SOff 32 0))].
Definition rg_tok : YP09.region := YP09.mkRegion (Some 22%nat) 0 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 37 0))].
Definition ss_sp (pc : Z) : sstate := mkSS pc sr_atoms [rg_spill] None (mkFacts [] [] []).
Definition ss_spt (pc : Z) : sstate := mkSS pc sr_atoms [rg_spill; rg_tok] None (mkFacts [] [] []).
Lemma ro_sp : Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) (ss_mem (ss_sp 0)).
Proof. repeat constructor; cbn; lia. Qed.
Lemma ro_spt : Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) (ss_mem (ss_spt 0)).
Proof. repeat constructor; cbn; lia. Qed.

(* the text of a recorder stub is at most 28 bytes (the plain proof's verbs_receive_br.v stub_text_len) *)
Lemma stub_len : forall R fn As v ch, -2^31 <= r_code R < 2^31 ->
(length (snd (rec_stub R fn As (shape_of v) ch)) <= 28)%nat.
Proof.
intros R fn As v ch HC. unfold rec_stub. rewrite rec_answer_text.
assert (E : r_code (rec_record R fn As) = r_code R) by (unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
destruct (r_refuse (rec_record R fn As) =? 0).
- exact (proj1 (proj2 (shape_of_facts v))).
- rewrite E. pose proof (resp_length (r_code R) HC). lia.
Qed.
Lemma stub_len_host : forall R fn As ch, -2^31 <= r_code R < 2^31 ->
(length (snd (rec_stub R fn As REC_MOD_HOST_SHAPE ch)) <= 28)%nat.
Proof.
intros R fn As ch HC. unfold rec_stub. rewrite rec_answer_text.
assert (E : r_code (rec_record R fn As) = r_code R) by (unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
destruct (r_refuse (rec_record R fn As) =? 0).
- assert (L6 : length (inst REC_MOD_HOST_SHAPE) = 6%nat) by (vm_compute; reflexivity). lia.
- rewrite E. pose proof (resp_length (r_code R) HC). lia.
Qed.
Lemma spill_frees0 : forall R, r_calls R = [] -> rec_spill_frees R = 0.
Proof. intros R H. unfold rec_spill_frees. rewrite H. reflexivity. Qed.
(* the atoi wrapper's value is an int *)
Lemma swrap32_range : forall z, -2 ^ 31 <= bv_swrap 32 z < 2 ^ 31.
Proof.
intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
assert (E : 2 ^ Z.of_N 32 = 4294967296) by reflexivity. rewrite E.
change (Z.div 4294967296 2) with 2147483648.
pose proof (Z.mod_pos_bound (z + 2147483648) 4294967296 ltac:(lia)). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Readers that read the same *)
Definition rdeq (rd rd' : reader) : Prop := forall a, rd' a = rd a.

Lemma aval_mem_eq : forall rd rd' a n v, rdeq rd rd' -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v E H k Hk. rewrite E. exact (H k Hk). Qed.
Lemma abytes_atR_eq : forall rd rd' a l, rdeq rd rd' -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l E H i Hi. rewrite E. exact (H i Hi). Qed.
Lemma astr_atR_eq : forall rd rd' a s, rdeq rd rd' -> astr_atR rd a s -> astr_atR rd' a s.
Proof. intros rd rd' a s E [H1 H2]. split; [exact (abytes_atR_eq rd rd' a _ E H1) | exact H2]. Qed.
Lemma rdword_eq : forall rd rd' a, rdeq rd rd' -> rdword rd' a = rdword rd a.
Proof. intros rd rd' a E. apply rdword_ext. intros k _. apply E. Qed.
Lemma rd32_eq : forall rd rd' a v, rdeq rd rd' -> rd32 rd a v -> rd32 rd' a v.
Proof. intros rd rd' a v E H k Hk. rewrite E. exact (H k Hk). Qed.
Lemma rdeq_refl : forall rd, rdeq rd rd.
Proof. intros rd a. reflexivity. Qed.
Lemma rdeq_trans : forall a b c, rdeq a b -> rdeq b c -> rdeq a c.
Proof. intros a b c H1 H2 x. rewrite H2. apply H1. Qed.
Lemma atoks_atA_eq : forall rd rd' tok ptrs tks cb ncb, rdeq rd rd' ->
atoks_atA rd tok ptrs tks cb ncb -> atoks_atA rd' tok ptrs tks cb ncb.
Proof.
intros rd rd' tok ptrs tks cb ncb E (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
- intros i p Hp. exact (aval_mem_eq rd rd' _ 8 p E (H3 i p Hp)).
- intros i p w Hp Hw. destruct (H4 i p w Hp Hw) as (A1 & A2 & A3 & A4).
  split; [exact (astr_atR_eq rd rd' p w E A1) | auto].
Qed.
Lemma cmd_got_ok_eq : forall rd rd', rdeq rd rd' -> cmd_got_ok rd -> cmd_got_ok rd'.
Proof.
intros rd rd' E (H1 & H2 & H3 & H4).
split; [exact (aval_mem_eq _ _ _ _ _ E H1)|]. split; [exact (aval_mem_eq _ _ _ _ _ E H2)|].
split; [exact (aval_mem_eq _ _ _ _ _ E H3) | exact (aval_mem_eq _ _ _ _ _ E H4)].
Qed.
Lemma cmd_ro_ok_eq : forall rd rd', rdeq rd rd' -> cmd_ro_ok rd -> cmd_ro_ok rd'.
Proof.
intros rd rd' E [Hb Ht]. split.
- unfold cmd_ro_bytes in *. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (eapply abytes_atR_eq; [exact E | eassumption]).
- intros e' He a Ha. rewrite E. exact (Ht e' He a Ha).
Qed.

(* the 8-byte value of aval_mem, as rdword reads it *)
Lemma rdword_of_aval : forall (rd : reader) a v, aval_mem rd a 8 v -> 0 <= v < 2 ^ 64 -> rdword rd a = Some v.
Proof.
intros rd a v H Hr. unfold rdword.
assert (B0 : rd a = Some (le_byte v 8 0)) by (rewrite <- (Z.add_0_r a) at 1; exact (H 0%nat ltac:(lia))).
change (rd (a + 1)) with (rd (a + Z.of_nat 1)). change (rd (a + 2)) with (rd (a + Z.of_nat 2)).
change (rd (a + 3)) with (rd (a + Z.of_nat 3)). change (rd (a + 4)) with (rd (a + Z.of_nat 4)).
change (rd (a + 5)) with (rd (a + Z.of_nat 5)). change (rd (a + 6)) with (rd (a + Z.of_nat 6)).
change (rd (a + 7)) with (rd (a + Z.of_nat 7)).
rewrite B0, (H 1%nat), (H 2%nat), (H 3%nat), (H 4%nat), (H 5%nat), (H 6%nat), (H 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The model of the three routes *)
Lemma vr_st_route : forall D, Verbs.toks D <> [] ->
vr_st D = VRR.plan_at (VRR.route (Verbs.toks D)) atoi_a (Verbs.line D) (Verbs.toks D).
Proof.
intros D H. unfold vr_st, Verbs.receive. destruct (Verbs.toks D) as [|v args] eqn:E; [contradiction|].
cbn [fst]. apply VRR.plan_route. discriminate.
Qed.
Lemma route_tail_ne : forall v args r, VRR.route_tail v args = r ->
r <> VRR.RRemove /\ r <> VRR.RWlist /\ r <> VRR.RReset.
Proof.
intros v args r H. unfold VRR.route_tail, VRR.route_conn, VRR.route_cd in H.
destruct (PV.ledger_of v PV.Lit.instance_info_verbs); [subst; repeat split; discriminate|].
destruct args as [|a args]; [subst; repeat split; discriminate|].
destruct (PV.is_instance_verb v); [subst; repeat split; discriminate|].
destruct args as [|b [|c args]]; try (subst; repeat split; discriminate).
destruct (PV.verb_is_m v PV.Lit.fmt_connect || PV.verb_is_m v PV.Lit.fmt_disconnect); subst; repeat split; discriminate.
Qed.
Ltac route_cases H :=
repeat match type of H with
| context [if ?b then _ else _] => let Eb := fresh "Eb" in destruct b eqn:Eb; [try discriminate H|]
end.
Lemma route_wlist : forall tk, VRR.route tk = VRR.RWlist -> exists args, tk = PV.Lit.verb_worker_list :: args.
Proof.
intros [|v args] H; [discriminate H|]. unfold VRR.route in H.
destruct (PV.list_eqb v PV.Lit.verb_add); [discriminate H|].
destruct (PV.list_eqb v PV.Lit.verb_descriptor_get); [discriminate H|].
destruct (PV.list_eqb v PV.Lit.verb_panel_get); [discriminate H|].
destruct (PV.verb_is_m v PV.Lit.fmt_remove); [discriminate H|].
unfold VRR.route_mid in H. destruct (PV.list_eqb v PV.Lit.verb_worker_list) eqn:E.
- apply PV.list_eqb_eq in E. subst v. exists args. reflexivity.
- exfalso. route_cases H. exact (proj1 (proj2 (route_tail_ne v args _ H)) eq_refl).
Qed.
Lemma route_reset : forall tk, VRR.route tk = VRR.RReset -> exists args, tk = PV.Lit.verb_supervisor_reset :: args.
Proof.
intros [|v args] H; [discriminate H|]. unfold VRR.route in H.
destruct (PV.list_eqb v PV.Lit.verb_add); [discriminate H|].
destruct (PV.list_eqb v PV.Lit.verb_descriptor_get); [discriminate H|].
destruct (PV.list_eqb v PV.Lit.verb_panel_get); [discriminate H|].
destruct (PV.verb_is_m v PV.Lit.fmt_remove); [discriminate H|].
unfold VRR.route_mid in H.
destruct (PV.list_eqb v PV.Lit.verb_worker_list); [discriminate H|].
destruct (PV.list_eqb v PV.Lit.verb_instance_info); [discriminate H|].
destruct (PV.list_eqb v PV.Lit.verb_supervisor_reset) eqn:E.
- apply PV.list_eqb_eq in E. subst v. exists args. reflexivity.
- exfalso. route_cases H. exact (proj2 (proj2 (route_tail_ne v args _ H)) eq_refl).
Qed.
Lemma route_remove : forall tk, VRR.route tk = VRR.RRemove ->
exists v args, tk = v :: args /\ PV.list_eqb v PV.Lit.verb_chain = false /\ PV.list_eqb v PV.Lit.verb_pin_set = false.
Proof.
intros [|v args] H; [discriminate H|]. unfold VRR.route in H.
destruct (PV.list_eqb v PV.Lit.verb_add); [discriminate H|].
destruct (PV.list_eqb v PV.Lit.verb_descriptor_get); [discriminate H|].
destruct (PV.list_eqb v PV.Lit.verb_panel_get); [discriminate H|].
destruct (PV.verb_is_m v PV.Lit.fmt_remove) eqn:E.
- exists v, args. split; [reflexivity|]. split.
  + destruct (PV.list_eqb v PV.Lit.verb_chain) eqn:E2; [|reflexivity].
    apply PV.list_eqb_eq in E2. subst v. vm_compute in E. discriminate E.
  + destruct (PV.list_eqb v PV.Lit.verb_pin_set) eqn:E2; [|reflexivity].
    apply PV.list_eqb_eq in E2. subst v. vm_compute in E. discriminate E.
- exfalso. unfold VRR.route_mid in H. route_cases H. exact (proj1 (route_tail_ne v args _ H) eq_refl).
Qed.
Lemma ev_route_plain : forall R ln v args st, PV.list_eqb v PV.Lit.verb_chain = false ->
PV.list_eqb v PV.Lit.verb_pin_set = false -> ev_route R ln (v :: args) st = ev_step R st.
Proof. intros R ln v args st H1 H2. unfold ev_route. rewrite H1, H2. reflexivity. Qed.
(* a route whose step is reject: the recorder untouched, sup_resp(-902) *)
Lemma vr_rej_of : forall R D, Verbs.toks D <> [] ->
(forall v args, Verbs.toks D = v :: args -> PV.list_eqb v PV.Lit.verb_chain = false /\ PV.list_eqb v PV.Lit.verb_pin_set = false) ->
vr_st D = Verbs.reject ->
vr_h R D = (R, resp (-902), false) /\ vr_k1 R D = 2 + EV_SUP_RESP.
Proof.
intros R D Hne Hv Hst. unfold vr_h, vr_k1. rewrite Hst. split; [reflexivity|].
destruct (Verbs.toks D) as [|v args] eqn:T; [exact (False_ind _ (Hne eq_refl))|].
destruct (Hv v args eq_refl) as [H1 H2]. rewrite ev_route_plain by assumption. reflexivity.
Qed.
Lemma vr_call_of : forall R D c, Verbs.toks D <> [] ->
(forall v args, Verbs.toks D = v :: args -> PV.list_eqb v PV.Lit.verb_chain = false /\ PV.list_eqb v PV.Lit.verb_pin_set = false) ->
vr_st D = Verbs.SCall c ->
vr_h R D = (VerbsRun.run_call R c, false) /\ vr_k1 R D = 2 + ev_call R c.
Proof.
intros R D c Hne Hv Hst. unfold vr_h, vr_k1. rewrite Hst. split; [reflexivity|].
destruct (Verbs.toks D) as [|v args] eqn:T; [exact (False_ind _ (Hne eq_refl))|].
destruct (Hv v args eq_refl) as [H1 H2]. rewrite ev_route_plain by assumption. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   List facts *)
Lemma nodup_of_pw : forall l : list (Z * Z), Forall (fun b => 0 <= snd b) l ->
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hnn Hpw; [constructor|].
cbn [map pairwise] in Hpw. destruct Hpw as [Hx Hl]. inversion Hnn as [|? ? Hx0 Hl0]; subst.
constructor; [|exact (IH Hl0 Hl)].
intros Hin. rewrite Forall_forall in Hx.
pose proof (Hx (fst x, req_size (snd x)) (in_map (fun b => (fst b, req_size (snd b))) l x Hin)) as Hd.
pose proof (req_size_pos (snd x) Hx0). unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma nodup_app_r : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
intros A l1. induction l1 as [|x l1 IH]; intros l2 H; [exact H|]. cbn in H. apply NoDup_cons_iff in H as [_ Hd].
exact (IH _ Hd).
Qed.
Lemma nodup_app_disj : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
intros A l1. induction l1 as [|y l1 IH]; intros l2 x H Hx; [destruct Hx|]. cbn in H. apply NoDup_cons_iff in H as [Hn Hd].
destruct Hx as [<- | Hx]; [intros H'; apply Hn; apply in_or_app; right; exact H' | exact (IH _ _ Hd Hx)].
Qed.
Lemma nodup_app_intro : forall {A} (l1 l2 : list A), List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 -> ~ In x l2) ->
List.NoDup (l1 ++ l2).
Proof.
intros A l1. induction l1 as [|y l1 IH]; intros l2 H1 H2 Hd; [exact H2|]. apply NoDup_cons_iff in H1 as [Hn H1].
cbn. apply NoDup_cons_iff. split.
- intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hn Hin) | exact (Hd y (or_introl eq_refl) Hin)].
- apply IH; [exact H1 | exact H2 | intros x Hx; apply Hd; right; exact Hx].
Qed.
Lemma aval_of_abytes8 : forall rd a l v, abytes_atR rd a l -> length l = 8%nat ->
(forall k, (k < 8)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = le_byte v 8 k) -> aval_mem rd a 8 v.
Proof. intros rd a l v H Hl Hk k Hkk. rewrite (H k ltac:(lia)). rewrite (Hk k Hkk). reflexivity. Qed.
Lemma cmd_got_ok_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb.
assert (G1 : abytes_atR rd 0xa7068 RO_ptr_a7068) by (decompose [and] Hb; assumption).
assert (G2 : abytes_atR rd 0xa7070 RO_ptr_a7070) by (decompose [and] Hb; assumption).
assert (G3 : abytes_atR rd 0xa7078 RO_ptr_a7078) by (decompose [and] Hb; assumption).
assert (G4 : abytes_atR rd 0xa7080 RO_ptr_a7080) by (decompose [and] Hb; assumption).
unfold cmd_got_ok.
split; [apply (aval_of_abytes8 rd _ _ _ G1 eq_refl); intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|].
split; [apply (aval_of_abytes8 rd _ _ _ G2 eq_refl); intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|].
split; [apply (aval_of_abytes8 rd _ _ _ G3 eq_refl); intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|].
apply (aval_of_abytes8 rd _ _ _ G4 eq_refl); intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.
Qed.
Lemma vr_k1_ev : forall R D, vr_k1 R D + 5 <= ev_vr R D.
Proof.
intros R D. rewrite ev_vr_eq. unfold vr_k3, vr_k2, ev_after, EV_REPLY, EV_SOCKET_SEND.
destruct (vr_aft D) as [[i v]|]; [|lia].
unfold EV_SUP_AFTER_REPLY, rec_spill_frees, EV_ARG_I, EV_XSTRDUP. destruct (Nat.ltb _ _); lia.
Qed.
Lemma find0_upto0n : forall M : list byte,
match StrFun.find_byte 0 M with Some i => i | None => length M end = length (Verbs.upto0 M).
Proof.
unfold Verbs.upto0. induction M as [|b M IH]; [reflexivity|].
cbn [StrFun.find_byte Verbs.upto]. destruct (bv_unsigned b =? 0); [reflexivity|].
destruct (StrFun.find_byte 0 M) as [i|] eqn:Fb; try rewrite Fb in IH; cbn; lia.
Qed.
Lemma line_le_strnlen : forall D n, Z.of_nat (length D) = n -> Z.of_nat (length (Verbs.line D)) <= StrFun.strnlen_res n D.
Proof.
intros D n <-. unfold StrFun.strnlen_res. rewrite Nat2Z.id, firstn_all.
assert (L : (length (Verbs.line D) <= length (Verbs.upto0 D))%nat).
{ unfold Verbs.line, Verbs.trim. rewrite length_rev.
  pose proof (verbs_receive_route.dropw_len Verbs.is_trail (rev (Verbs.upto0 D))) as H1. rewrite length_rev in H1. exact H1. }
pose proof (find0_upto0n D) as E. destruct (StrFun.find_byte 0 D) as [i|]; lia.
Qed.
Lemma strnlen_le : forall n D, 0 <= n -> 0 <= StrFun.strnlen_res n D <= n.
Proof.
intros n D Hn. unfold StrFun.strnlen_res.
destruct (StrFun.find_byte 0 (firstn (Z.to_nat n) D)) as [i|] eqn:Fb; [|lia].
destruct (StrFun.find_byte_Some _ _ _ Fb) as (Hl & _). rewrite length_firstn in Hl. lia.
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

Lemma val_mem_of_aval : forall H mem a n v, aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte SEGS H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Seeding *)
Lemma vr_env_regs : forall (regs : bvmap 5 word) extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma vr_env_extra : forall (regs : bvmap 5 word) extra m, (32 <= m < A_TEXT)%nat ->
ew (Eimg (Ereg regs extra)) m = nth (m - 32) extra (Z_to_bv 64 0).
Proof.
intros regs extra m Hm. rewrite Eimg_low by lia. replace m with (32 + (m - 32))%nat at 1 by lia. apply ew_Ereg_extra.
Qed.
Lemma vr_chunk8 : forall E H mem base off e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
aval_mem (aview SEGS H mem) (base + off) 8 v ->
YP09.chunk_ok SEGS E (mrestrict H mem) base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E H mem base off e v He Hv Ha.
apply (chunk_ok_val SEGS E _ base off 8 e v He); [cbn; lia | cbn; lia | exact (val_mem_of_aval H mem _ 8 v Ha)].
Qed.
Definition vr_slots_ok (rd : reader) (s1 F q c : Z) : Prop :=
Forall (fun ov => aval_mem rd (s1 + fst ov) 8 (snd ov)) (vr_sl3 F q c).
Definition vr_vals_ok (F q c t1 : Z) : Prop :=
0 <= F /\ F + 2048 <= 2 ^ 47 /\ 0 <= q < 2 ^ 64 /\ 0 <= c < 2 ^ 64 /\ 0 <= t1 < 2 ^ 64.
Lemma vr_xt_atoms : forall (regs : bvmap 5 word) F c q t1,
let E := Eimg (Ereg regs (vr_xt F c q t1)) in
ew E 32 = Z_to_bv 64 F /\ ew E 33 = Z_to_bv 64 (shadow_addr F) /\ ew E 34 = Z_to_bv 64 (shadow_addr F + 4) /\
ew E 35 = Z_to_bv 64 c /\ ew E 36 = Z_to_bv 64 q /\ ew E 37 = Z_to_bv 64 t1.
Proof.
intros regs F c q t1 E. subst E.
repeat split; (rewrite vr_env_extra by (unfold A_TEXT; lia); reflexivity).
Qed.
Lemma sv_atom_val : forall E n x w v, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> v = w + x ->
sv_denot E (SOff n x) = Z_to_bv 64 v.
Proof. intros E n x w v Hn Hw ->. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by exact Hw. reflexivity. Qed.
Lemma shadow_range : forall F, 0 <= F -> F + 2048 <= 2 ^ 47 -> 0 <= shadow_addr F /\ shadow_addr F + 4 < 2 ^ 64.
Proof.
intros F H0 H1. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
assert (F / 8 <= F) by (apply Z.div_le_upper_bound; lia). lia.
Qed.

Lemma vr_region_spill : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 F q c t1,
bv_unsigned (getr regs 9) = s1 -> 0 <= s1 -> s1 + 80 <= 2 ^ 64 -> vr_vals_ok F q c t1 ->
vr_slots_ok (rdW W mem) s1 F q c ->
YP09.region_ok SEGS (Eimg (Ereg regs (vr_xt F c q t1))) (mrestrict (w_H W) mem) rg_spill.
Proof.
intros W regs mem s1 F q c t1 H9 Hs0 Hs1 (HF0 & HF1 & Hq & Hc & Ht) Hsl.
pose proof (vr_xt_atoms regs F c q t1) as (X32 & X33 & X34 & X35 & X36 & X37).
set (E := Eimg (Ereg regs (vr_xt F c q t1))) in *.
assert (E9 : base_val E (Some 9%nat) = s1) by (cbn [base_val]; subst E; rewrite (vr_env_regs regs _ 9 9%bv eq_refl); exact H9).
pose proof (shadow_range F HF0 HF1) as SH.
unfold vr_slots_ok, vr_sl3 in Hsl.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [? H] end.
cbn [fst snd] in *.
unfold YP09.region_ok, rg_spill. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite E9.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (vr_chunk8 E (w_H W) mem s1 8 _ (shadow_addr F)); [apply (sv_atom_val E 33 0 (shadow_addr F)); [exact X33 | lia | lia] | lia | assumption]|].
apply Forall_cons; [apply (vr_chunk8 E (w_H W) mem s1 16 _ (F + 32)); [apply (sv_atom_val E 32 32 F); [exact X32 | lia | lia] | lia | assumption]|].
apply Forall_cons; [apply (vr_chunk8 E (w_H W) mem s1 24 _ q); [apply (sv_atom_val E 36 0 q); [exact X36 | lia | lia] | lia | assumption]|].
apply Forall_cons; [apply (vr_chunk8 E (w_H W) mem s1 32 _ (shadow_addr F + 4)); [apply (sv_atom_val E 34 0 (shadow_addr F + 4)); [exact X34 | lia | lia] | lia | assumption]|].
apply Forall_cons; [apply (vr_chunk8 E (w_H W) mem s1 40 _ F); [apply (sv_atom_val E 32 0 F); [exact X32 | lia | lia] | lia | assumption]|].
apply Forall_cons; [apply (vr_chunk8 E (w_H W) mem s1 48 _ F); [apply (sv_atom_val E 32 0 F); [exact X32 | lia | lia] | lia | assumption]|].
apply Forall_cons; [apply (vr_chunk8 E (w_H W) mem s1 56 _ c); [apply (sv_atom_val E 35 0 c); [exact X35 | lia | lia] | lia | assumption]|].
apply Forall_cons; [apply (vr_chunk8 E (w_H W) mem s1 72 _ F); [apply (sv_atom_val E 32 0 F); [exact X32 | lia | lia] | lia | assumption]|].
apply Forall_nil.
Qed.

Lemma vr_region_tok : forall (W : world SEGS) (regs : bvmap 5 word) mem F q c t1,
bv_unsigned (getr regs 22) = F + 32 -> vr_vals_ok F q c t1 ->
aval_mem (rdW W mem) (F + 40) 8 t1 ->
YP09.region_ok SEGS (Eimg (Ereg regs (vr_xt F c q t1))) (mrestrict (w_H W) mem) rg_tok.
Proof.
intros W regs mem F q c t1 H22 (HF0 & HF1 & Hq & Hc & Ht) Hta.
pose proof (vr_xt_atoms regs F c q t1) as (X32 & X33 & X34 & X35 & X36 & X37).
set (E := Eimg (Ereg regs (vr_xt F c q t1))) in *.
assert (E22 : base_val E (Some 22%nat) = F + 32) by (cbn [base_val]; subst E; rewrite (vr_env_regs regs _ 22 22%bv eq_refl); exact H22).
unfold YP09.region_ok, rg_tok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite E22.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (vr_chunk8 E (w_H W) mem (F + 32) 8 _ t1); [apply (sv_atom_val E 37 0 t1); [exact X37 | lia | lia] | lia |].
replace (F + 32 + 8) with (F + 40) by lia. exact Hta.
Qed.

Lemma vr_seed_ret : forall pc (W : world SEGS) regs mem,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (ss_ret pc)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc W regs mem. rewrite restrict_mkst_fx. unfold ss_ret. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.

Lemma vr_seed_sp : forall pc (W : world SEGS) (regs : bvmap 5 word) mem s1 F q c t1,
bv_unsigned (getr regs 9) = s1 -> 0 <= s1 -> s1 + 80 <= 2 ^ 64 -> vr_vals_ok F q c t1 ->
vr_slots_ok (rdW W mem) s1 F q c ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (vr_xt F c q t1))) (ss_sp pc)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc W regs mem s1 F q c t1 H9 Hs0 Hs1 HV Hsl. rewrite restrict_mkst_fx. unfold ss_sp. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_cons; [exact (vr_region_spill W regs mem s1 F q c t1 H9 Hs0 Hs1 HV Hsl) | apply Forall_nil].
- cbn. tauto.
- split; [exact I | split; exact I].
Qed.

Lemma vr_seed_spt : forall pc (W : world SEGS) (regs : bvmap 5 word) mem s1 F q c t1,
bv_unsigned (getr regs 9) = s1 -> bv_unsigned (getr regs 22) = F + 32 -> 0 <= s1 -> s1 + 80 <= 2 ^ 64 ->
F + 48 <= s1 -> vr_vals_ok F q c t1 ->
vr_slots_ok (rdW W mem) s1 F q c -> aval_mem (rdW W mem) (F + 40) 8 t1 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (vr_xt F c q t1))) (ss_spt pc)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc W regs mem s1 F q c t1 H9 H22 Hs0 Hs1 HFs HV Hsl Hta. rewrite restrict_mkst_fx. unfold ss_spt.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_cons; [exact (vr_region_spill W regs mem s1 F q c t1 H9 Hs0 Hs1 HV Hsl)|].
  apply Forall_cons; [exact (vr_region_tok W regs mem F q c t1 H22 HV Hta) | apply Forall_nil].
- cbn [pairwise_disjoint all_disjoint]. split; [|split; [exact I | exact I]]. split; [|exact I].
  unfold extent_disjoint, rg_spill, rg_tok. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite (vr_env_regs regs _ 9 9%bv eq_refl), (vr_env_regs regs _ 22 22%bv eq_refl), H9, H22. lia.
- split; [exact I | split; exact I].
Qed.

Lemma rdeq_of_frame : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
rdeq (aview SEGS H m) (aview SEGS H m').
Proof.
intros E rs H m m' Hf Hro a. apply (aview_eq_of SEGS). apply Hf.
intros (r & Hr & Ha). rewrite Forall_forall in Hro. pose proof (Hro r Hr). lia.
Qed.
Lemma kept_regs_st_ok : forall E ss ms (regs0 : bvmap 5 word) extra (zs : list Z),
st_ok SEGS E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) (map (Z_to_bv 5) zs) = true ->
forall r, In r zs -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros E ss ms regs0 extra zs HS HA Hl r Hr.
apply (regs_kept_of_st_ok SEGS E ss ms regs0 extra (map (Z_to_bv 5) zs) HS HA Hl). apply in_map. exact Hr.
Qed.
Lemma env_agree_Eimg : forall (regs : bvmap 5 word) extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma arodata_okP_eq : forall rd rd', rdeq rd rd' -> arodata_okP SEGS RLO RHI B rd -> arodata_okP SEGS RLO RHI B rd'.
Proof. intros rd rd' E H a H1 H2 H3. rewrite E. exact (H a H1 H2 H3). Qed.

Lemma vr_env_same : forall W mem W' mem', rdeq (rdW W mem) (rdW W' mem') ->
vr_env B W mem -> vr_env B W' mem'.
Proof.
intros W mem W' mem' E (H1 & H2 & H3 & (G1 & c & G2) & H5 & ev & H6).
split; [exact (arodata_okP_eq _ _ E H1)|]. split; [exact (cmd_got_ok_eq _ _ E H2)|].
split; [exact (cmd_ro_ok_eq _ _ E H3)|].
split; [split; [rewrite (rdword_eq _ _ _ E); exact G1 | exists c; rewrite (rdword_eq _ _ _ E); exact G2]|].
split; [rewrite E; exact H5 | exists ev; exact (rd32_eq _ _ _ _ E H6)].
Qed.

Lemma vr_core_same : forall e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md W' regs' mem' md',
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W' mem' md' k ->
rdeq (rdW W mem) (rdW W' mem') ->
vr_rv regs' (vr_base B e ++ rl') ->
vr_core B MT e pos F tmps sh sl rl' Rc Oc qv k kmax nm nmax lyc Sc W' regs' mem' md'.
Proof.
intros e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md W' regs' mem' md'
(HJ & Hk & Hm & Hnm & (HF1 & HF2 & HF3) & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq) HJ' E Hrv'.
split; [exact HJ'|]. split; [exact Hk|]. split; [exact Hm|]. split; [exact Hnm|].
split; [split; [exact HF1|]; split; [rewrite (rdword_eq _ _ _ E); exact HF2 | intros i Hi; rewrite E; exact (HF3 i Hi)]|].
split; [exact Hrv'|].
split; [intros j r Hj; exact (aval_mem_eq _ _ _ _ _ E (Hsv j r Hj))|].
split; [unfold vr_spill in *; eapply Forall_impl; [|exact Hsp]; intros ov Hov; exact (aval_mem_eq _ _ _ _ _ E Hov)|].
split; [exact (vr_env_same W mem W' mem' E Henv)|].
split.
{ apply (rec_repA_agree B _ _ _ _ _ _ Rc Oc Hrec (fun pn _ Hb => Hb)); intros; apply E. }
split; [exact Hdat|]. split; [exact Hperm | exact (aval_mem_eq _ _ _ _ _ E Hq)].
Qed.

Lemma vr_line_same : forall e q W mem W' mem', rdeq (rdW W mem) (rdW W' mem') ->
vr_line B e q W mem -> vr_line B e q W' mem'.
Proof. intros e q W mem W' mem' E [H1 H2]. split; [exact H1 | exact (astr_atR_eq _ _ _ _ E H2)]. Qed.
Lemma vr_copy_same : forall e F c tp W mem W' mem', rdeq (rdW W mem) (rdW W' mem') ->
vr_copy B e F c tp W mem -> vr_copy B e F c tp W' mem'.
Proof. intros e F c tp W mem W' mem' E [H1 H2]. split; [exact H1 | exact (atoks_atA_eq _ _ _ _ _ _ _ E H2)]. Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Registers of a boundary *)
Lemma vr_rv_get : forall regs l r v, vr_rv regs l -> In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs l r v H Hin. unfold vr_rv in H. rewrite Forall_forall in H. exact (H (r, v) Hin). Qed.
Lemma vr_rv_intro : forall regs l, (forall r v, In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v) -> vr_rv regs l.
Proof. intros regs l H. unfold vr_rv. apply Forall_forall. intros [r v] Hin. exact (H r v Hin). Qed.
Lemma vr_rv_incl : forall regs L1 L2, vr_rv regs L1 -> incl L2 L1 -> vr_rv regs L2.
Proof. intros regs L1 L2 H Hi. unfold vr_rv in *. rewrite Forall_forall in *. intros x Hx. exact (H x (Hi x Hx)). Qed.
Lemma vr_rv_keep : forall e (regs regsc : bvmap 5 word) rl rl',
vr_rv regsc (vr_base B e ++ rl) ->
(forall r, In r [2; 3; 4; 8; 9] -> getr regs (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) ->
(forall r v, In (r, v) rl' ->
  (In (r, v) rl /\ getr regs (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) \/ getr regs (Z_to_bv 5 r) = w64 v) ->
vr_rv regs (vr_base B e ++ rl').
Proof.
intros e regs regsc rl rl' Hrv Hb Hl. apply vr_rv_intro. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
- assert (Hr : In r [2; 3; 4; 8; 9]).
  { unfold vr_base in Hin. cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _; cbn; tauto. }
  rewrite (Hb r Hr). apply (vr_rv_get regsc _ _ _ Hrv). apply in_or_app; left; exact Hin.
- destruct (Hl r v Hin) as [[H1 H2] | H]; [|exact H].
  rewrite H2. apply (vr_rv_get regsc _ _ _ Hrv). apply in_or_app; right; exact H1.
Qed.
Lemma vr_s1_cases : forall e, vr_sp0 e mod 16 = 0 -> vr_s1 e = vr_sp0 e - 192 \/ vr_s1 e = vr_sp0 e - 208.
Proof.
intros e H. unfold vr_s1. pose proof (Z.div_mod (vr_sp0 e) 16 ltac:(lia)) as D1.
pose proof (Z.div_mod (vr_sp0 e - 192) 32 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as M2.
rewrite H in D1. lia.
Qed.
Lemma nodup_ablocks : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. apply nodup_of_pw.
- apply Forall_forall. intros [p n] Hin. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  cbn. lia.
- destruct (ablocks B ly S) as [|[p n] l] eqn:E; [exact I|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR ltac:(rewrite E; left; reflexivity)) as (_ & _ & _ & _ & _ & Hpw & _).
  rewrite E in Hpw. exact Hpw.
Qed.
Lemma rec_code_range : forall ly S rd R O, rec_repA B ly S rd R O -> -2^31 <= r_code R < 2^31.
Proof. intros ly S rd R O (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HC & _) & _) & _). exact HC. Qed.

(* the two blocks of a boundary: the line and the copy, live and none of the recorder's *)
Lemma vr_tmp_blocks : forall e (O : list (Z * Z)) lyc Sc (W : world SEGS) mem md tmps,
AR SEGS B lyc Sc W mem md ->
Permutation (ablocks B lyc Sc) (O ++ tmps ++ e_rest e) ->
forall y, In y tmps -> In y (ablocks B lyc Sc) /\ ~ In y O.
Proof.
intros e O lyc Sc W mem md tmps HAR Hperm y Hy.
assert (Hnd : List.NoDup (O ++ tmps ++ e_rest e)) by exact (Permutation_NoDup Hperm (nodup_ablocks _ _ _ _ _ HAR)).
split.
- apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; left. exact Hy.
- intros Hy2. apply (nodup_app_disj _ _ y Hnd Hy2). apply in_or_app; left. exact Hy.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   vr_ent at a later FP state (statement pass 4): its only FP conjunct, rounding mode 0 (the last), survives fxrel,
   so the walk after a printf-reaching call, which runs at the FP state the call returns, has vr_ent there too *)
Ltac vr_ent_copy H Hx :=
lazymatch type of H with
| _ /\ _ => let H1 := fresh "H" in let H2 := fresh "H" in
  destruct H as [H1 H2]; split; [exact H1 | vr_ent_copy H2 Hx]
| _ => exact (fxrel_frm0 _ _ H Hx)
end.
Lemma vr_ent_fx : forall (f0 f1 : YK11.FPState) e, vr_ent (fx := f0) B MT e -> fxrel f0 f1 -> vr_ent (fx := f1) B MT e.
Proof.
intros f0 f1 e He Hx. unfold vr_ent in *. cbv zeta in *. vr_ent_copy He Hx.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The record facts (names and types as the assembly collects them) *)
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.

(* ---------------------------------------------------------------------------------------------------------------
   What a recorder call keeps: its footprint lies in g_rec, record.spill and the recorder's blocks *)
Definition fp1 (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma fp1_cases : forall O a, inFP (fp1 O) a ->
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a H. unfold fp1 in H. apply inFP_cons in H as [H|H]; [left; exact H|].
apply inFP_cons in H as [H|H]; [right; left; exact H|]. right; right. exact (inFP_ablocks_fp_inv O a H).
Qed.
Lemma inFP_PG_rec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity | unfold REC_SIZE in Ha; cbn; lia]. Qed.
Lemma inFP_PG_spill : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity | unfold SC_SIZE in Ha; cbn; lia]. Qed.
Lemma inFP_PG_quit : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; right; right; left; reflexivity | cbn; lia]. Qed.

Lemma O_pos : forall ly S (W : world SEGS) mem md (O : list (Z * Z)), AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> Forall (fun pn => 0 < fst pn) O.
Proof.
intros ly S W mem md O HAR HO. apply Forall_forall. intros [p n] Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hin)) as (_ & H4 & _). cbn. lia.
Qed.
Lemma fp1_closed : forall O, Forall (fun pn => 0 < fst pn) O -> ~ YI16.sink_open_fp (fp1 O).
Proof.
intros O HO. unfold fp1. apply sink_closed_cons; [unfold A_G_REC; cbn; lia|].
apply sink_closed_cons; [unfold A_REC_SPILL; cbn; lia|]. apply sink_closed_ablocks_fp. exact HO.
Qed.

Section ck.
Variables (O FP1 : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (STK1 sp1 : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (mem2 : word -> option byte) (md2 : Model) (k1 : Z).
Hypothesis HAR : AR SEGS B lyc Sc W mem md.
Hypothesis HJc : ajournal SEGS B STK1 sp1 FP1 lyc Sc W mem md [] ly2 S2 W2 mem2 md2 k1.
Hypothesis HO : forall pn, In pn O -> In pn (ablocks B lyc Sc).
Hypothesis HFP : forall a, inFP FP1 a -> inFP (fp1 O) a.

Lemma ck_cases : forall a, inFP FP1 a ->
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof. intros a Ha. exact (fp1_cases O a (HFP a Ha)). Qed.
Lemma ck_closed : ~ YI16.sink_open_fp FP1.
Proof. intros H0. apply (fp1_closed O (O_pos lyc Sc W mem md O HAR HO)). exact (HFP 0 H0). Qed.

Lemma ck_stack : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) -> rdW W2 mem2 a = rdW W mem a.
Proof.
intros a Ha Hw. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
apply F1; [exact Ha | exact Hw |]. pose proof asan_consts as (C1 & _).
intros Hf. destruct (ck_cases a Hf) as [G|[G|(p & n & Hpn & Hr)]].
- unfold A_G_REC, REC_SIZE in G. lia.
- unfold A_REC_SPILL, SC_SIZE in G. lia.
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & _ & Hc & _). lia.
Qed.

Lemma ck_block : forall p n i, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> ~ In (p, n) O ->
0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W mem (p + i).
Proof.
intros p n i H1 H2 HnO Hi. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i H1 H2 Hi). intros Hf.
assert (Himg : ~ in_img SEGS (p + i)) by exact (blk_img SEGS B LAWS _ _ _ _ _ p n (p + i) HAR H1 ltac:(lia)).
destruct (ck_cases _ Hf) as [G|[G|(b & m & Hbm & Hr)]].
- exact (Himg (proj1 (PROGU _ (inFP_PG_rec _ G)))).
- exact (Himg (proj1 (PROGU _ (inFP_PG_spill _ G)))).
- assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hbm; exact (HnO Hbm)).
  pose proof (sep_blocks SEGS B LAWS lyc Sc W mem md b m p n HAR (HO _ Hbm) H1 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma ck_frame : forall cid pos a, In (cid, pos) (frames Sc) ->
(frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid \/
 shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8) ->
rdW W2 mem2 a = rdW W mem a.
Proof.
intros cid pos a Hin Ha. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
apply (F4 cid pos a Hin); [unfold frame_rng, in_zr; cbn [fst snd]; lia |].
intros Hf. pose proof asan_consts as (C1 & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfa).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)) as Hdl.
destruct Ha as [Ha | Ha].
- assert (Himg : ~ in_img SEGS a) by exact (frm_img SEGS B LAWS lyc Sc W mem md cid pos a HAR Hin Ha).
  destruct (ck_cases _ Hf) as [G|[G|(b & m & Hbm & Hr)]].
  + exact (Himg (proj1 (PROGU _ (inFP_PG_rec _ G)))).
  + exact (Himg (proj1 (PROGU _ (inFP_PG_spill _ G)))).
  + pose proof (sep_block_frame SEGS B LAWS lyc Sc W mem md b m cid pos HAR (HO _ Hbm) Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)) as Hdp.
  destruct (ck_cases _ Hf) as [G|[G|(b & m & Hbm & Hr)]].
  + unfold shadow_addr, SHADOW_OFF, A_G_REC, REC_SIZE in *. lia.
  + unfold shadow_addr, SHADOW_OFF, A_REC_SPILL, SC_SIZE in *. lia.
  + destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR (HO _ Hbm)) as (_ & _ & _ & Happ & _).
    apply (fshadow_not_app (frame_addr lyc cid pos) (fs_frame_bytes cid / 8) b (req_size m) a); [lia | lia | exact Happ | | exact Hr].
    unfold shadow_addr, SHADOW_OFF in Ha. lia.
Qed.

Lemma ck_img : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ (A_G_REC <= a < A_G_REC + REC_SIZE) -> ~ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
rdW W2 mem2 a = rdW W mem a.
Proof.
intros a Himg Ho He Hg Hs. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply (F3 a Himg Ho He). apply fp_spares_closed; [exact ck_closed|].
intros Hf. destruct (ck_cases _ Hf) as [G|[G|(b & m & Hbm & Hr)]]; [exact (Hg G) | exact (Hs G) |].
exact (blk_img SEGS B LAWS lyc Sc W mem md b m a HAR (HO _ Hbm) Hr Himg).
Qed.

Lemma ck_arodata : arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W2 mem2).
Proof.
intros HR a Hro Ho He.
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]).
rewrite (ck_img a Himg Ho He); [exact (HR a Hro Ho He) | |].
- intros G. exact (RPG a (inFP_PG_rec a G) Hro).
- intros G. exact (RPG a (inFP_PG_spill a G) Hro).
Qed.

Lemma ck_quit : forall v, aval_mem (rdW W mem) A_G_QUITTING 4 v -> aval_mem (rdW W2 mem2) A_G_QUITTING 4 v.
Proof.
intros v Hq kk Hk.
assert (Ha : A_G_QUITTING <= A_G_QUITTING + Z.of_nat kk < A_G_QUITTING + 4) by lia.
destruct (PROGU _ (inFP_PG_quit _ Ha)) as (Hi & Ho & He).
rewrite (ck_img _ Hi Ho He); [exact (Hq kk Hk) | |].
- unfold A_G_QUITTING, A_G_REC, REC_SIZE. lia.
- unfold A_G_QUITTING, A_REC_SPILL, SC_SIZE. lia.
Qed.
End ck.

(* ---------------------------------------------------------------------------------------------------------------
   The frame record at the entry sp: verbs_receive keeps its frame pointer sp0 in s0 at every program call,
   so a callee's chain is achain_push on the entry's chain (afn_pre's) with the ra and entry
   s0 words the prologue stored at sp0 - 8 and sp0 - 16, or achain's empty case when sp0 >= ly_top - 16 *)
Lemma vr_chain : forall e pos lyc Sc W mem md k sp',
vr_ent B MT e ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem md k ->
vr_saved e W mem -> sp' + 16 <= vr_sp0 e ->
exists ch1, achain lyc (rdW W mem) sp' (vr_sp0 e) ch1.
Proof.
intros e pos lyc Sc W mem md k sp' Hent HJ Hsv Hsp'.
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrec0 & _).
pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & _ & _ & Hstk0 & _ & Hch0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
assert (Hk : forall a, vr_sp0 e <= a < 2 ^ 64 -> rdW W mem a = rdW (e_W e) (e_mem e) a).
{ intros a Ha. apply F1; [lia | lia |].
  intros (r & Hr & Hra). unfold vr_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - unfold VERBS_RECEIVE_PG in Hr. cbn in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn in Hra;
    unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, A_G_QUITTING in Hra; lia.
  - apply in_map_iff in Hr as ([p n] & <- & Hpn). cbn in Hra.
    pose proof (rec_repA_in_blocks B _ _ _ _ _ _ Hrec0 Hpn) as Hb.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 Hb) as (_ & _ & Hc & _). lia. }
destruct (Z_lt_le_dec (vr_sp0 e) (ly_top (e_ly e) - 16)) as [Hlt | Hge].
- exists ((vr_sp0 e, raZ (e_regs e), s0Z (e_regs e)) :: e_ch e).
  apply (achain_ly_top (e_ly e) lyc); [exact Etop|].
  apply (achain_push (e_ly e) (rdW (e_W e) (e_mem e)) (rdW W mem) (vr_sp0 e) (s0Z (e_regs e)) (raZ (e_regs e)) (e_ch e) sp' Hch0).
  + lia.
  + intros a Ha. exact (Hk a Ha).
  + apply rdword_of_aval; [|unfold raZ; apply bv_unsigned_in_range].
    replace (vr_sp0 e - 8) with (vr_sp0 e - 8 - 8 * Z.of_nat 0) by lia. exact (Hsv 0%nat 1 eq_refl).
  + apply rdword_of_aval; [|unfold s0Z; apply bv_unsigned_in_range].
    replace (vr_sp0 e - 16) with (vr_sp0 e - 8 - 8 * Z.of_nat 1) by lia. exact (Hsv 1%nat 8 eq_refl).
  + exact Hra40.
  + lia.
  + apply Z.mod_divide; [lia|]. pose proof Hal16 as H16. apply Z.mod_divide in H16; [|lia].
    destruct H16 as [z Hz]. exists (2 * z). lia.
  + exact Hlt.
  + exact Hsp'.
- exists []. left. split; [right; left; rewrite Etop; exact Hge | reflexivity].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The state at a callee's entry (after the `jal`): vr_core of the route with ra, a0 and the callee-saved registers
   rl named, the line and the copy *)
Definition vr_cs (e : vrE) (pos F q c x retk : Z) (tp : list Z) (rl : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k nm : Z) : Prop :=
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  ((1, BASE + retk) :: (10, x) :: rl) (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regs mem md /\
vr_line B e q W mem /\ vr_copy B e F c tp W mem.

(* the post of a recorder call that returns a text, in the form the arm uses (each callee's post implies it) *)
Definition rc_post (R : rstate) (O : list (Z * Z)) (m : rstate * list byte) (XM1 : Z) (ly : alayout) (S : astate)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 m = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 mo_le MT S S' XM1.

(* sup_worker_list / sup_reset's post form, and sup_remove / sup_remove_all's *)
Lemma rc_post_of_b : forall R O m XM1 LIVE ly S ly' S' W' regs' mem' md',
(exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 m = (R', t) /\ getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\ rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\ ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE /\ mo_le MT S S' XM1) ->
rc_post R O m XM1 ly S ly' S' W' regs' mem' md'.
Proof.
intros R O m XM1 LIVE ly S ly' S' W' regs' mem' md'
  (R' & t & q & O' & Em & H10 & Hq & Hrec & Hsrc & Hin & Hne & HnO & Hstr & Hkeep & Hcls & _ & Hmo).
exists R', t, q, O'. split; [exact Em|]. split; [exact H10|]. split; [lia|]. split; [exact Hrec|].
split; [exact Hsrc|]. split; [exact Hin|]. split; [exact Hne|]. split; [exact HnO|]. split; [exact Hstr|].
split; [intros pn H1 H2; exact (proj1 (Hkeep pn H1 H2))|]. split; [exact Hcls | exact Hmo].
Qed.
Lemma rc_post_of_a : forall R O m XM1 LIVE ly S ly' S' W' regs' mem' md',
(exists (R' : rstate) (O' : list (Z * Z)) (q : Z), m = (R', snd m) /\
 let n := Z.of_nat (length (snd m)) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\ rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 In (q, n) (ablocks B ly' S') /\ (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, n)) /\
 ~ In q (map fst O') /\ astr_atR (rdW W' mem') q (snd m) /\
 blocks_bytes S' <= blocks_bytes S + LIVE /\ mo_le MT S S' XM1) ->
rc_post R O m XM1 ly S ly' S' W' regs' mem' md'.
Proof.
intros R O m XM1 LIVE ly S ly' S' W' regs' mem' md' (R' & O' & q & Em & HH). cbv zeta in HH.
destruct HH as (H10 & Hq & Hrec & Hsrc & Hcls & Hkeep & Hin & Hne & HnO & Hstr & _ & Hmo).
exists R', (snd m), q, O'. split; [exact Em|]. split; [exact H10|]. split; [lia|]. split; [exact Hrec|].
split; [exact Hsrc|]. split; [exact Hin|]. split; [exact Hne|]. split; [exact HnO|]. split; [exact Hstr|].
split; [exact Hkeep|]. split; [exact Hcls | exact Hmo].
Qed.
(* the callees' FP-existential post (statement pass 4) under a weaker return predicate *)
Lemma apost_baseF_impl : forall STK FP regs ly S (W : world SEGS) mem md k
  (P P' : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
(forall ly' S' W' regs' mem' md', P ly' S' W' regs' mem' md' -> P' ly' S' W' regs' mem' md') ->
forall W' c', apost_baseF SEGS B STK FP regs ly S W mem md k P W' c' -> apost_baseF SEGS B STK FP regs ly S W mem md k P' W' c'.
Proof.
intros STK FP regs ly S W mem md k P P' HPP W' c' (fx' & ly' & S' & regs' & mem' & md' & Ec & HR & HC & HJ & HRg & HP).
exists fx', ly', S', regs', mem', md'. split; [exact Ec|]. split; [exact HR|]. split; [exact HC|]. split; [exact HJ|].
split; [exact HRg | exact (HPP _ _ _ _ _ _ HP)].
Qed.

(* the refusal stubs 0x8da28 and 0x8dacc from a route's state, the step being reject *)
Lemma vr_pr_mk : forall e pc W pos F q c tp rl lyc Sc regs mem md k nm,
vr_h (e_R e) (e_D e) = (e_R e, resp (-902), false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_RESP ->
Verbs.toks (e_D e) <> [] ->
vr_pr_ntok pc (length (Verbs.toks (e_D e))) ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regs mem md ->
vr_rv regs (vr_base B e ++ vr_rl_pr e F q c pc (-902)) ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
vr_pr B MT e pc W (cfg_at SEGS (vr_pc pc) regs mem md).
Proof.
intros e pc W pos F q c tp rl lyc Sc regs mem md k nm Hvh Hk1 Hne Hnt Hcore Hrv Hline Hcopy.
exists (-902), (e_R e), (e_O e), pos, F, q, c, tp, lyc, Sc, regs, mem, md, k, nm.
split; [reflexivity|]. split; [intros _; reflexivity|]. split; [lia|]. split; [exact Hvh|]. split; [exact Hne|].
split; [exact Hnt|]. split; [|split; [exact Hline | exact Hcopy]].
destruct Hcore as (H1 & H2 & H3 & H4 & H5 & _ & H7).
split; [exact H1|]. split; [rewrite Hk1; lia|]. split; [exact H3|].
split; [unfold VR_NM_PR, VR_NM_PRE in *; lia|]. split; [exact H5|]. split; [exact Hrv | exact H7].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The state at the callee's return address: the handler is done, its text tq is a live block, a0 = tq and the
   callee-saved registers rl kept *)
Definition vr_aft (e : vrE) (pos F q c : Z) (tp : list Z) (rl : list (Z * Z)) (tq : Z) (O1 : list (Z * Z))
  (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
  (kk nm2 : Z) : Prop :=
4096 <= tq /\ astr_atR (rdW W2 mem2) tq (vr_x (e_R e) (e_D e)) /\
vr_core B MT e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  ((10, tq) :: rl) (vr_R1 (e_R e) (e_D e)) O1 (vr_qv e) kk (vr_k1 (e_R e) (e_D e)) nm2 VR_NM_HD ly2 S2 W2 regs2 mem2 md2 /\
vr_line B e q W2 mem2 /\ vr_copy B e F c tp W2 mem2.

Lemma vr_hd_of_aft : forall e pc pos F q c tp rl tq O1 ly2 S2 W2 regs2 mem2 md2 kk nm2 regs3 mem3 md3,
vr_aft e pos F q c tp rl tq O1 ly2 S2 W2 regs2 mem2 md2 kk nm2 ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  ly2 S2 W2 mem3 md3 kk ->
rdeq (rdW W2 mem2) (rdW W2 mem3) ->
vr_rv regs3 (vr_base B e ++ vr_rl_hd e F q c pc tq) ->
vr_hd_ntok pc (length (Verbs.toks (e_D e))) ->
vr_hd B MT e pc W2 (cfg_at SEGS (vr_pc pc) regs3 mem3 md3).
Proof.
intros e pc pos F q c tp rl tq O1 ly2 S2 W2 regs2 mem2 md2 kk nm2 regs3 mem3 md3
  (Htq & Hx & Hcore & Hline & Hcopy) HJ3 Em Hrv Hnt.
exists tq, O1, pos, F, q, c, tp, ly2, S2, regs3, mem3, md3, kk, nm2.
split; [reflexivity|]. split; [exact Hnt|]. split; [exact Htq|]. split; [exact (astr_atR_eq _ _ _ _ Em Hx)|].
split; [eapply vr_core_same; [exact Hcore | exact HJ3 | exact Em | exact Hrv]|].
split; [exact (vr_line_same _ _ _ _ _ _ Em Hline) | exact (vr_copy_same _ _ _ _ _ _ _ _ Em Hcopy)].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The meter across one recorder call (one named lemma per call shape): a recorder call that returns a text spends at
   most three mallocs of at most VERBS_RECEIVE_REQ bytes and one free (the argument copy, answer's two copies, the free
   of the old answer; the spill arm's frees are 0, the entry's recorder holding no call) in at least three events, so
   the interface's vri_meter_ok (the callee's mo_ok premise) and vri_meter_step (the exit's vr_meter) apply with
   a = 3, b = 1, ev = EV1 *)
Lemma vr10_meter_pre : forall e Sc k nm XM1 EV1,
vr_ent B MT e -> vr_meter MT e Sc k nm ->
XM1 <= 3 * mo_malloc MT VERBS_RECEIVE_REQ + mo_free MT -> 3 <= EV1 -> k + EV1 <= ev_vr (e_R e) (e_D e) ->
mo_ok MT Sc XM1.
Proof.
intros e Sc k nm XM1 EV1 Hent Hmet HXM1 HEV1 Hk.
eapply vri_meter_ok with (e := e) (k := k) (nm := nm) (a := 3) (b := 1) (ev := EV1);
  [exact MTL | exact Hent | exact Hmet | lia | lia | lia | exact Hk].
Qed.
Lemma vr10_meter_post : forall e Sc S2 k nm XM1 EV1,
vr_meter MT e Sc k nm -> mo_le MT Sc S2 XM1 ->
XM1 <= 3 * mo_malloc MT VERBS_RECEIVE_REQ + mo_free MT -> 3 <= EV1 ->
vr_meter MT e S2 (k + EV1) (nm + 3).
Proof.
intros e Sc S2 k nm XM1 EV1 Hmet Hmle HXM1 HEV1.
eapply vri_meter_step with (X := XM1) (b := 1);
  [exact MTL | exact Hmet | exact Hmle | lia | lia | lia].
Qed.

Lemma vr_aft_build : forall e W pos F q c x retk tp rl lyc Sc regs mem md k nm STK1 FP1 EV1 XM1 (m : rstate * list byte)
  W2 ly2 S2 regs2 mem2 md2,
vr_ent B MT e ->
vr_cs e pos F q c x retk tp rl lyc Sc W regs mem md k nm ->
Forall (fun rv => acallee_saved (fst rv)) rl ->
vr_h (e_R e) (e_D e) = (m, false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV1 ->
3 <= EV1 -> XM1 <= 3 * mo_malloc MT VERBS_RECEIVE_REQ + mo_free MT ->
(forall a, inFP FP1 a -> inFP (fp1 (e_O e)) a) ->
ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc W mem md [] ly2 S2 W2 mem2 md2 EV1 ->
aregs_preserved regs regs2 ->
rc_post (e_R e) (e_O e) m XM1 lyc Sc ly2 S2 W2 regs2 mem2 md2 ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  ly2 S2 W2 mem2 md2 (k + EV1) ->
exists tq O1, vr_aft e pos F q c tp rl tq O1 ly2 S2 W2 regs2 mem2 md2 (k + EV1) (nm + 3).
Proof.
intros e W pos F q c x retk tp rl lyc Sc regs mem md k nm STK1 FP1 EV1 XM1 m W2 ly2 S2 regs2 mem2 md2
  Hent Hcs Hrl Hvh Hk1 HEV1 HXM1 HFP HJc HP HK HJ3.
destruct Hcs as (Hcore & Hline & Hcopy).
destruct Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & HinD & HnotO & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _).
pose proof HPRE0 as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & _).
pose proof HJc as (HAR2 & Hly2 & _).
pose proof (vr_s1_cases e Hal16) as Hs1.
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
assert (HO : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
pose proof (ck_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJc HO HFP) as KS.
pose proof (ck_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJc HO HFP) as KB.
pose proof (ck_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJc HO HFP) as KF.
pose proof (ck_arodata _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJc HO HFP) as KA.
pose proof (ck_quit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJc HO HFP) as KQ.
destruct HK as (R' & t & qq & O' & Em' & Ha0 & Hq4096 & Hrec' & HO'1 & Hqin & Hqnot & HqnotO' & Hstr & Hkeep & Hall
  & Hmle).
destruct Hrec' as (Q' & HarQ & HOQ).
assert (EX : vr_x (e_R e) (e_D e) = t) by (unfold vr_x; rewrite Hvh, Em'; reflexivity).
assert (ER1 : vr_R1 (e_R e) (e_D e) = R') by (unfold vr_R1; rewrite Hvh, Em'; reflexivity).
assert (EQV : vr_qv e = e_q0 e) by (unfold vr_qv, vr_quit; rewrite Hvh; reflexivity).
assert (HinF : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (Efr : frame_addr ly2 4 pos = frame_addr lyc 4 pos)
  by (unfold frame_addr; destruct Hly2 as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
assert (Efl : flag_addr ly2 4 pos = flag_addr lyc 4 pos)
  by (unfold flag_addr; destruct Hly2 as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
assert (HinR : In (e_data e, Z.max (e_n e) 1) (e_rest e))
  by (pose proof (Permutation_in _ Hperm0 HinD) as H0; apply in_app_or in H0 as [H0|H0]; [contradiction | exact H0]).
set (T0 := [vr_lb e q; vr_cb e c] ++ e_rest e) in *.
assert (HndOT : List.NoDup (e_O e ++ T0)) by exact (Permutation_NoDup Hperm (nodup_ablocks _ _ _ _ _ HAR)).
assert (HinT0 : forall y, In y T0 -> In y (ablocks B lyc Sc) /\ ~ In y (e_O e)).
{ intros y Hy. split.
  - apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hy.
  - intros Hy2. exact (nodup_app_disj _ _ y HndOT Hy2 Hy). }
assert (HFsz : fs_frame_bytes 4 = 1024) by reflexivity.
exists qq, (lay_blocks Q'). unfold vr_aft.
split; [lia|].
split; [rewrite EX; exact Hstr|].
split.
{ rewrite ER1, EQV, EX. unfold vr_core.
  split; [exact HJ3|].
  split; [rewrite Hk1; lia|].
  split.
  { exact (vr10_meter_post e Sc S2 k nm XM1 EV1 Hmet Hmle HXM1 HEV1). }
  split; [unfold VR_NM_HD, VR_NM_PRE in *; lia|].
  split.
  { destruct Hfr as (EF & HF2 & HF3).
    split; [rewrite Efr; exact EF|].
    split.
    - rewrite Efl, <- HF2. apply rdword_ext. intros kk Hkk.
      apply (KF 4 pos _ HinF). left. rewrite <- EF, HFsz. lia.
    - intros i Hi. rewrite (KF 4 pos _ HinF); [exact (HF3 i Hi)|].
      right. rewrite <- EF, HFsz. change (1024 / 8) with 128. lia. }
  split.
  { apply vr_rv_intro. intros r v Hin.
    apply in_app_or in Hin as [Hin | Hin].
    - unfold vr_base in Hin. cbn in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-;
      (match goal with |- getr _ (Z_to_bv 5 ?r) = _ => rewrite (HP r ltac:(unfold acallee_saved; lia)) end;
       apply (vr_rv_get regs _ _ _ Hrv); apply in_or_app; left; cbn; tauto).
    - destruct Hin as [E | Hin]; [injection E as <- <-; exact Ha0|].
      rewrite Forall_forall in Hrl. pose proof (Hrl (r, v) Hin) as Hcs. cbn [fst] in Hcs.
      rewrite (HP r Hcs). apply (vr_rv_get regs _ _ _ Hrv). apply in_or_app; right. right; right. exact Hin. }
  split.
  { intros j r Hj. pose proof (Hsv j r Hj) as H.
    assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbn [length vr_saved_regs] in Hj13.
    intros kk Hkk. rewrite KS; [exact (H kk Hkk) | lia | lia]. }
  split.
  { unfold vr_spill in *. apply Forall_forall. intros [off v] Hin. rewrite Forall_forall in Hsp. pose proof (Hsp _ Hin) as H.
    cbn [fst snd] in H |- *.
    assert (Hoff : 8 <= off <= 72).
    { unfold vr_sl3 in Hin. cbn in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. }
    intros kk Hkk. rewrite KS; [exact (H kk Hkk) | lia | lia]. }
  split.
  { destruct Henv as (HR1 & _).
    assert (HR3 : arodata_okP SEGS RLO RHI B (rdW W2 mem2)) by exact (KA HR1).
    assert (HRO3 : cmd_ro_ok (rdW W2 mem2)) by exact (ROA ly2 S2 W2 mem2 md2 HAR2 HR3).
    destruct (RECC ly2 S2 W2 mem2 md2 HAR2) as (Hfl & Hgd & Herr).
    split; [exact HR3|]. split; [exact (cmd_got_ok_of_ro _ HRO3)|]. split; [exact HRO3|].
    split; [exact Hgd|]. split; [exact Hfl | exact Herr]. }
  split.
  { exists Q'. split; [exact HarQ|]. intros pn. split; intros H; exact H. }
  split.
  { intros Hin. apply HOQ in Hin. destruct (HO'1 _ Hin) as [H|H]; [exact (Hdat H)|]. apply H.
    apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; right. exact HinR. }
  split.
  { change ([(qq, Z.of_nat (length t) + 1); vr_lb e q; vr_cb e c] ++ e_rest e) with ((qq, Z.of_nat (length t) + 1) :: T0).
    apply NoDup_Permutation.
    - exact (nodup_ablocks _ _ _ _ _ HAR2).
    - apply nodup_app_intro.
      + destruct HarQ as (_ & _ & _ & _ & _ & _ & _ & (Hnd & _)).
        first [exact (NoDup_map_inv _ _ Hnd) | exact (NoDup_map_inv _ _ (proj1 (NoDup_ListNoDup _) Hnd))].
      + constructor; [intros Hin; destruct (HinT0 _ Hin) as [H1 H2]; exact (Hqnot _ H1 H2 eq_refl) | exact (nodup_app_r _ _ HndOT)].
      + intros y Hy Hy2. apply HOQ in Hy. destruct Hy2 as [<- | Hy2].
        * apply HqnotO'. apply in_map_iff. exists (qq, Z.of_nat (length t) + 1). split; [reflexivity | exact Hy].
        * destruct (HinT0 _ Hy2) as [H1 H2]. destruct (HO'1 _ Hy) as [H3|H3]; [exact (H2 H3) | exact (H3 H1)].
    - intros y. split.
      + intros Hy. destruct (Hall y Hy) as [(H1 & H2) | [H1 | H1]].
        * apply in_or_app; right; right. pose proof (Permutation_in _ Hperm H1) as H3.
          apply in_app_or in H3 as [H3|H3]; [contradiction | exact H3].
        * apply in_or_app; left. apply HOQ. exact H1.
        * apply in_or_app; right; left. symmetry. exact H1.
      + intros Hy. apply in_app_or in Hy as [Hy | [Hy | Hy]].
        * apply HOQ in Hy. exact (rec_repA_in_blocks B _ _ _ _ _ _ (ex_intro _ Q' (conj HarQ HOQ)) Hy).
        * rewrite <- Hy. exact Hqin.
        * destruct (HinT0 _ Hy) as [H1 H2]. exact (Hkeep _ H1 H2). }
  exact (KQ _ Hq). }
split.
{ destruct Hline as (Hfl & Hls). split; [exact Hfl|].
  destruct (HinT0 (vr_lb e q) ltac:(left; reflexivity)) as [H1 H2]. pose proof (Hkeep _ H1 H2) as H3.
  unfold vr_lb in H1, H2, H3.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR H1) as (_ & _ & _ & _ & _ & _ & Hn1).
  pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as Hrs.
  apply (astr_atR_agree (rdW W mem) (rdW W2 mem2) q (Verbs.line (e_D e)) (vr_l (e_n e) (e_D e) + 1) Hls).
  - pose proof (line_le_strnlen (e_D e) (e_n e) HlenD). unfold vr_l. lia.
  - intros kk Hkk. apply (KB q (vr_l (e_n e) (e_D e) + 1) kk H1 H3 H2). lia. }
{ destruct Hcopy as (Hfc & (Hmod & HlenP & Hptr & Hw)). split; [exact Hfc|].
  destruct Hfr as (EF & _).
  assert (Hntk : (length (Verbs.toks (e_D e)) <= 64)%nat)
    by (unfold Verbs.toks; rewrite length_firstn; unfold Verbs.line_words_max; lia).
  split; [exact Hmod|]. split; [exact HlenP|]. split.
  - intros i p Hp. pose proof (Hptr i p Hp) as H.
    assert (Hi : (i < length tp)%nat) by (apply nth_error_Some; rewrite Hp; discriminate).
    rewrite HlenP in Hi.
    intros kk Hkk. rewrite (KF 4 pos _ HinF); [exact (H kk Hkk)|]. left. rewrite <- EF, HFsz. lia.
  - intros i p w Hp Hwi. destruct (Hw i p w Hp Hwi) as (A1 & A2 & A3 & A4).
    split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
    destruct (HinT0 (vr_cb e c) ltac:(right; left; reflexivity)) as [H1 H2]. pose proof (Hkeep _ H1 H2) as H3.
    unfold vr_cb in H1, H2, H3.
    pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrs.
    apply (astr_atR_agree _ _ p w (Z.of_nat (length w) + 1) A1); [lia|].
    intros kk Hkk. replace (p + kk) with (c + (p - c + kk)) by lia.
    apply (KB c _ (p - c + kk) H1 H3 H2). lia. }
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The generic arm: from the callee's entry, through its contract (CALL, FP-existential since statement pass 4: the
   call rule is PaFx's cl_callS_wideF), to the state at the return address (vr_aft) at the FP state fx' the callee
   returns, which the continuation K (stated for every such fx') takes to the segment's exit. The callee's live-bytes
   premise comes from verbs_receive_live.v's vr_live_le (the entry's recorder holds no call); its frame chain from
   vr_chain; its rounding mode 0 is vr_ent's last conjunct. *)
Lemma vr_call_arm : forall e W pos F q c x retk tp rl lyc Sc regs mem md k nm AF STK1 FP1 EV1 XM1 LIVE1
  (m : rstate * list byte) (Q : world SEGS -> config -> Prop),
vr_ent B MT e ->
vr_cs e pos F q c x retk tp rl lyc Sc W regs mem md k nm ->
Forall (fun rv => acallee_saved (fst rv)) rl ->
vr_h (e_R e) (e_D e) = (m, false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV1 ->
3 <= EV1 -> XM1 <= 3 * mo_malloc MT VERBS_RECEIVE_REQ + mo_free MT -> LIVE1 <= 20 * VERBS_RECEIVE_REQ ->
0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK ->
0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
(forall a, inFP FP1 a -> inFP (fp1 (e_O e)) a) ->
(forall ch, afn_pre SEGS B STK1 lyc Sc W regs mem md ch -> frm0 fx ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) ->
  rec_repA B lyc Sc (rdW W mem) (e_R e) (e_O e) -> Z.of_nat (length (frames Sc)) <= 8 ->
  st_nev Sc + EV1 <= EV_MAX -> blocks_bytes Sc + LIVE1 <= LIVE_MAX -> mo_ok MT Sc XM1 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md)
  (apost_baseF SEGS B STK1 FP1 regs lyc Sc W mem md EV1 (rc_post (e_R e) (e_O e) m XM1 lyc Sc))) ->
(forall fx' : YK11.FPState, fxrel fx fx' -> forall W2 regs2 mem2 md2 ly2 S2 tq O1,
  vr_aft e pos F q c tp rl tq O1 ly2 S2 W2 regs2 mem2 md2 (k + EV1) (nm + 3) ->
  SRr SEGS W2 (mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md) Q.
Proof.
intros e W pos F q c x retk tp rl lyc Sc regs mem md k nm AF STK1 FP1 EV1 XM1 LIVE1 m Q
  Hent Hcs Hrl Hvh Hk1 HEV1 HXM1 HLV1 HST0 HSTK1 Hretk Hretk2 HFP CALL K.
pose proof Hcs as (Hcore & Hline & Hcopy).
pose proof Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & _ & Hcalls & _ & _ & _ & _ & Hperm0
  & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm0 & Hev0 & Hlive0 & Hmok0 & HRM0).
pose proof HPRE0 as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & _).
pose proof (vr_s1_cases e Hal16) as Hs1.
assert (R1 : getr regs 1 = Z_to_bv 64 (BASE + retk))
  by (apply (vr_rv_get regs _ 1 _ Hrv); apply in_or_app; right; left; reflexivity).
assert (R2 : getr regs 2 = w64 (vr_s1 e)) by (apply (vr_rv_get regs _ 2 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R3 : getr regs 3 = w64 (as_gp B)) by (apply (vr_rv_get regs _ 3 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R4 : getr regs 4 = w64 (as_tp B)) by (apply (vr_rv_get regs _ 4 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R8 : getr regs 8 = w64 (vr_sp0 e)) by (apply (vr_rv_get regs _ 8 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (Hsp1 : spZ regs = vr_s1 e) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = vr_sp0 e) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (vr_chain e pos lyc Sc W mem md k (vr_s1 e) Hent HJ Hsv ltac:(lia)) as (ch1 & Hch1).
assert (HO : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
pose proof (vr_k1_ev (e_R e) (e_D e)) as Hkev.
assert (Ho16 : (vr_s1 e - vr_sp0 e) mod 16 = 0)
  by (destruct Hs1 as [E|E]; rewrite E; [replace (vr_sp0 e - 192 - vr_sp0 e) with (-192) by lia
      | replace (vr_sp0 e - 208 - vr_sp0 e) with (-208) by lia]; reflexivity).
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
(* the live bytes now: the entry's, the recorder's (no call yet) and the line and copy blocks *)
assert (Hbb : blocks_bytes Sc <= blocks_bytes (e_S e) + 10 * VERBS_RECEIVE_REQ).
{ pose proof (vr_live_le SEGS B LAWS (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) lyc Sc W mem md (rdW W mem) (e_R e)
    (e_O e) (e_O e) [vr_lb e q; vr_cb e c] (e_rest e) HAR0 HAR Hperm0 Hperm Hrec) as HL.
  rewrite Hcalls in HL. cbn [length Z.of_nat] in HL. rewrite !bsum_cons in HL. unfold bsum in HL. cbn [fold_right] in HL.
  unfold vr_lb, vr_cb, vr_l in HL. cbn [snd] in HL.
  pose proof (strnlen_le (e_n e) (e_D e) ltac:(lia)) as Hsl.
  pose proof (line_le_strnlen (e_D e) (e_n e) HlenD) as Hll.
  unfold LMAX, VERBS_RECEIVE_REQ in *. lia. }
unfold cfg_at, w64.
eapply SRr_bind.
{ eapply (cl_callS_wideF B LAWS W regs mem _ VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(4, pos)] lyc Sc md k STK1 FP1 EV1 (vr_s1 e - vr_sp0 e) (Z_to_bv 64 (BASE + retk)) ch1
    (rc_post (e_R e) (e_O e) m XM1 lyc Sc) HJ).
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
  - intros HPRE1. eapply SRr_mono.
    { apply (CALL ch1 HPRE1 HRM0).
      - exact (proj1 Henv).
      - exact (proj1 (proj2 (proj2 Henv))).
      - exact Hrec.
      - rewrite Hfrs. cbn [length app]. lia.
      - lia.
      - unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in *. lia.
      - apply (vr10_meter_pre e Sc k nm XM1 EV1 Hent Hmet HXM1 HEV1). rewrite Hk1 in Hkev. lia. }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HR' & HC' & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. rewrite R1. split; [reflexivity|]. split; [exact HR'|]. split; [exact HC'|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. destruct (fp1_cases (e_O e) a (HFP a Ha)) as [G|[G|(p & n & Hpn & Hr)]].
    + right; right; right; right; left. split; [exists (A_G_REC, A_G_REC + REC_SIZE); split;
        [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; left; reflexivity | exact G]|].
      split; [|exact (proj1 (PROGU a (inFP_PG_rec a G)))].
      rewrite (AF0m.ts_prog _ HB). unfold AF0m.TFIB_PROG_STATIC. apply Exists_cons_hd.
      unfold in_zr, A_G_REC, REC_SIZE in *. cbn [fst snd]. lia.
    + right; right; right; right; left. split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split;
        [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; right; left; reflexivity | exact G]|].
      split; [|exact (proj1 (PROGU a (inFP_PG_spill a G)))].
      rewrite (AF0m.ts_prog _ HB). unfold AF0m.TFIB_PROG_STATIC. apply Exists_cons_tl. apply Exists_cons_hd.
      unfold in_zr, A_REC_SPILL, SC_SIZE in *. cbn [fst snd]. lia.
    + right; left. split; [exists (p, p + req_size n); split; [unfold vr_fp; apply in_or_app; right; unfold ablocks_fp;
        exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (p, n) Hpn) | cbn; lia]|].
      exists p, n. split; [exact (HO _ Hpn) | exact Hr].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    destruct (fp1_cases (e_O e) a (HFP a Ha)) as [G|[G|(p & n & Hpn & Hr)]].
    + unfold A_G_REC, REC_SIZE in G. lia.
    + unfold A_REC_SPILL, SC_SIZE in G. lia.
    + destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & _ & Hc & _). lia. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJc & HP & HK).
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
destruct (vr_aft_build e W pos F q c x retk tp rl lyc Sc regs mem md k nm STK1 FP1 EV1 XM1 m W2 ly2 S2 regs2 mem2 md2
  Hent Hcs Hrl Hvh Hk1 HEV1 HXM1 HFP HJc HP HK HJ2) as (tq & O1 & Haft).
exact (K fx' Hfx W2 regs2 mem2 md2 ly2 S2 tq O1 Haft).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   One jump from a return pc, run from a state that names only the registers *)
Lemma vr_jmp : forall retk stopk, 0 <= retk ->
sym_run_toN_pi pl_tpi FUEL stopk (ss_ret retk) = (ss_ret stopk, PRS_running) ->
forall W2 (regs2 : bvmap 5 word) mem2 md2 (Q : world SEGS -> config -> Prop) STK sp0 FP ly S W0 mem md own ly2 S2 kk,
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 kk ->
(forall regs3 mem3 md3, (forall r, getr regs3 r = getr regs2 r) -> rdeq (rdW W2 mem2) (rdW W2 mem3) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem3 md3 kk ->
  Q W2 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + stopk)) mem3 (seg_rom SEGS)) md3)) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros retk stopk Hk Hrun W2 regs2 mem2 md2 Q STK sp0 FP ly S W0 mem md own ly2 S2 kk HJ HQ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
pose proof (vr_seed_ret retk W2 regs2 mem2) as HS.
eapply (SRr_run_to_pi_AJ B LAWS W2 FUEL stopk (Eimg (Ereg regs2 [])) (ss_ret retk) (ss_ret stopk) PRS_running _
  STK sp0 FP ly S W0 mem md own ly2 S2 md2 kk Q HEI HS Hrun I HJ).
- apply awr_ok_nil.
- intros ms' mat HS' HJ' HF HFr HG.
  rewrite (st_ok_pi_restrict_mkst (w_H W2) _ (ss_ret stopk) ms' HS' eq_refl). cbn [ss_pc ss_ret].
  apply SRr_ret. apply HQ.
  + intros r. rewrite (st_ok_pi_restrict_reg (w_H W2) _ (ss_ret stopk) ms' r HS'). cbn [ss_regs ss_ret].
    symmetry. exact (regs_ok_Eimg_Ereg regs2 [] r).
  + cbn [ms_mem mkst ss_mem ss_ret] in HFr. exact (rdeq_of_frame _ [] _ _ _ HFr (Forall_nil _)).
  + exact HJ'.
Qed.

(* a word of tok[] handed to a recorder function: a C string in the copy block, none of the recorder's *)
Lemma vr_tok_arg : forall e F q c tp lyc Sc (W : world SEGS) mem md i p w,
AR SEGS B lyc Sc W mem md ->
Permutation (ablocks B lyc Sc) (e_O e ++ [vr_lb e q; vr_cb e c] ++ e_rest e) ->
vr_copy B e F c tp W mem ->
nth_error tp i = Some p -> nth_error (Verbs.toks (e_D e)) i = Some w ->
astr_argA B lyc Sc (rdW W mem) (in_roP SEGS RLO RHI) (e_O e) p (Some w) /\
aval_mem (rdW W mem) (F + 32 + 8 * Z.of_nat i) 8 p /\ 4096 <= p /\ p + Z.of_nat (length w) + 1 <= alloc_ceiling /\
Z.of_nat (length w) <= 8192.
Proof.
intros e F q c tp lyc Sc W mem md i p w HAR Hperm (Hfc & (Hmod & HlenP & Hptr & Hw)) Hp Hwi.
destruct (Hw i p w Hp Hwi) as (A1 & A2 & A3 & A4).
assert (HndOT : List.NoDup (e_O e ++ [vr_lb e q; vr_cb e c] ++ e_rest e))
  by exact (Permutation_NoDup Hperm (nodup_ablocks _ _ _ _ _ HAR)).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. right; left; reflexivity. }
assert (HcbO : ~ In (vr_cb e c) (e_O e)).
{ intros H. exact (nodup_app_disj _ _ _ HndOT H (or_intror (or_introl eq_refl))). }
unfold vr_cb in Hcb, HcbO.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn).
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrs.
split; [|split; [exact (Hptr i p Hp) | split; [lia | split; [lia | exact A2]]]].
cbn [astr_argA]. split; [lia|]. split; [exact A1|]. split; [unfold LMAX; lia|].
left. split.
- exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1). split; [exact Hcb | lia].
- apply Forall_forall. intros [p' n'] Hin'.
  assert (Hin2 : In (p', n') (ablocks B lyc Sc))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hin').
  assert (Hne : (p', n') <> (c, Z.of_nat (length (Verbs.line (e_D e))) + 1)) by (intros E; rewrite E in Hin'; exact (HcbO Hin')).
  pose proof (sep_blocks SEGS B LAWS lyc Sc W mem md p' n' _ _ HAR Hin2 Hcb Hne) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin2) as (_ & _ & _ & _ & _ & _ & Hn').
  pose proof (req_size_pos n' ltac:(lia)) as Hrs'.
  unfold zdisjoint in Hd. unfold iv_apart. cbn [fst snd] in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Across the atoi call: memory that agrees below the allocation ceiling and from the realigned stack pointer up,
   except at the errno cell (aj_art_at's frame for aatoi_realizes, whose window is below vr_s1) *)
Definition vr_kx (e : vrE) (W : world SEGS) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ vr_s1 e <= a) -> ~ aerrno_cell B a -> rdW W m' a = rdW W m a.

Lemma nerr_hi : forall a, kLowMemEnd <= a -> ~ aerrno_cell B a.
Proof. intros a Ha He. pose proof (pal_env B TL) as ((E0 & E1) & _). unfold aerrno_cell in He. lia. Qed.
Lemma nerr_img : forall a, ~ in_img SEGS a -> ~ aerrno_cell B a.
Proof. intros a Ha He. pose proof (pal_env B TL) as (_ & EI & _). exact (Ha (EI a He)). Qed.
Lemma nerr_frame : forall lyc Sc (W : world SEGS) mem md pos a, AR SEGS B lyc Sc W mem md -> In (4, pos) (frames Sc) ->
frame_addr lyc 4 pos <= a < frame_addr lyc 4 pos + 1024 -> ~ aerrno_cell B a.
Proof.
intros lyc Sc W mem md pos a HAR Hin Ha. apply nerr_img. apply (frm_img SEGS B LAWS lyc Sc W mem md 4 pos a HAR Hin).
change (fs_frame_bytes 4) with 1024. exact Ha.
Qed.
Lemma nerr_block : forall lyc Sc (W : world SEGS) mem md p n a, AR SEGS B lyc Sc W mem md -> In (p, n) (ablocks B lyc Sc) ->
p <= a < p + req_size n -> ~ aerrno_cell B a.
Proof. intros lyc Sc W mem md p n a HAR Hin Ha. apply nerr_img. exact (blk_img SEGS B LAWS lyc Sc W mem md p n a HAR Hin Ha). Qed.
Lemma nerr_pg : forall a, inFP cmd_PG a -> ~ aerrno_cell B a.
Proof. intros a Ha. destruct (PROGU a Ha) as (_ & _ & He). exact He. Qed.
Lemma img_pg : forall a, inFP cmd_PG a -> a < 0x606000.
Proof. intros a Ha. destruct (PROGU a Ha) as (Hi & _). exact (proj2 (pa_img_range a Hi)). Qed.

Lemma vr_core_kx : forall e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md regs' mem' md',
vr_ent B MT e ->
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  [(4, pos)] lyc Sc W mem' md' k ->
vr_kx e W mem mem' ->
Forall (fun ov => 0 <= fst ov <= 200) sl ->
vr_rv regs' (vr_base B e ++ rl') ->
vr_core B MT e pos F tmps sh sl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs' mem' md'.
Proof.
intros e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md regs' mem' md'
  Hent (HJ & Hkm & Hmeter & Hnm & Hframe & Hrv & Hsaved & Hspill & Henv & Hrec & HdO & Hperm & Hquit) HJ' K Hsl Hrv'.
pose proof Hent as (HPRE0 & _). pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof (vr_s1_cases e Hal16) as Hs1.
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ') as HAR'.
assert (Hin4 : In (4, pos) (frames Sc)) by (pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _); rewrite Hfrs; left; reflexivity).
split; [exact HJ'|]. split; [exact Hkm|]. split; [exact Hmeter|]. split; [exact Hnm|].
split.
{ destruct Hframe as (HF & Hfl & Hsh). subst F.
  destruct (frames_bounds SEGS B LAWS lyc Sc W mem md 4 pos HAR Hin4) as (B1 & B2 & _).
  change (fs_frame_bytes 4) with 1024 in B2.
  split; [reflexivity|]. split.
  - rewrite (rdword_ext (rdW W mem) (rdW W mem')); [exact Hfl|]. intros kk Hkk'.
    apply K; [lia | left; lia | apply (nerr_frame lyc Sc W mem md pos _ HAR Hin4); lia].
  - intros i Hi.
    pose proof (Z.div_mod (frame_addr lyc 4 pos) 8 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (frame_addr lyc 4 pos) 8 ltac:(lia)) as M.
    rewrite (K (shadow_addr (frame_addr lyc 4 pos) + Z.of_nat i)); [exact (Hsh i Hi) | | |];
      unfold shadow_addr, SHADOW_OFF in *.
    + lia.
    + left. lia.
    + apply nerr_hi. unfold kLowMemEnd. lia. }
split; [exact Hrv'|].
split.
{ intros j r Hj.
  assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length vr_saved_regs] in Hj13.
  intros kk Hkk. rewrite K; [exact (Hsaved j r Hj kk Hkk) | lia | right; lia | apply nerr_hi; lia]. }
split.
{ unfold vr_spill in *. rewrite Forall_forall in Hspill, Hsl |- *. intros ov Hov.
  pose proof (Hsl ov Hov) as Hb.
  intros kk Hkk. rewrite K; [exact (Hspill ov Hov kk Hkk) | lia | right; lia | apply nerr_hi; lia]. }
split.
{ destruct Henv as (HRO & _).
  assert (HRO' : arodata_okP SEGS RLO RHI B (rdW W mem')).
  { intros a Hro Ho He.
    assert (Hi : in_img SEGS a)
      by (destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]).
    pose proof (pa_img_range a Hi).
    rewrite K; [exact (HRO a Hro Ho He) | lia | left; lia | exact He]. }
  destruct (RECC _ _ _ _ _ HAR') as (Hfl & Hg & Her).
  pose proof (ROA _ _ _ _ _ HAR' HRO') as HROk.
  split; [exact HRO'|]. split; [exact (cmd_got_ok_of_ro _ HROk)|]. split; [exact HROk|].
  split; [exact Hg|]. split; [exact Hfl | exact Her]. }
split.
{ apply (rec_repA_agree B _ _ _ _ _ _ Rc Oc Hrec (fun pn _ Hb => Hb)).
  - intros kk Hk.
    assert (G : A_G_REC <= A_G_REC + kk < A_G_REC + REC_SIZE) by (unfold A_G_REC, REC_SIZE in *; lia).
    pose proof (img_pg _ (inFP_PG_rec _ G)).
    apply K; [unfold A_G_REC, REC_SIZE in *; lia | left; lia | exact (nerr_pg _ (inFP_PG_rec _ G))].
  - intros kk Hk.
    assert (G : A_REC_SPILL <= A_REC_SPILL + kk < A_REC_SPILL + SC_SIZE) by (unfold A_REC_SPILL, SC_SIZE in *; lia).
    pose proof (img_pg _ (inFP_PG_spill _ G)).
    apply K; [unfold A_REC_SPILL, SC_SIZE in *; lia | left; lia | exact (nerr_pg _ (inFP_PG_spill _ G))].
  - intros [p n] Hpn kk Hk. cbn [fst snd] in *.
    pose proof (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as Hrq.
    apply K; [lia | left; lia | apply (nerr_block lyc Sc W mem md p n _ HAR Hin); lia]. }
split; [exact HdO|]. split; [exact Hperm|].
intros kk Hkk.
assert (G : A_G_QUITTING <= A_G_QUITTING + Z.of_nat kk < A_G_QUITTING + 4) by lia.
pose proof (img_pg _ (inFP_PG_quit _ G)).
rewrite K; [exact (Hquit kk Hkk) | unfold A_G_QUITTING in *; lia | left; lia | exact (nerr_pg _ (inFP_PG_quit _ G))].
Qed.

Lemma vr_line_kx : forall e q lyc Sc (W : world SEGS) mem md mem', vr_ent B MT e ->
AR SEGS B lyc Sc W mem md -> In (vr_lb e q) (ablocks B lyc Sc) ->
vr_line B e q W mem -> vr_kx e W mem mem' -> vr_line B e q W mem'.
Proof.
intros e q lyc Sc W mem md mem' Hent HAR Hin (Hfr & Hs) K. split; [exact Hfr|].
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _).
pose proof asan_consts as (C1 & _).
unfold vr_lb in Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as Hrs.
pose proof (line_le_strnlen (e_D e) (e_n e) HlenD) as Hll.
apply (astr_atR_agree (rdW W mem) (rdW W mem') q (Verbs.line (e_D e)) (vr_l (e_n e) (e_D e) + 1) Hs).
- unfold vr_l in *. lia.
- intros kk Hkk. apply K; [lia | left; lia | apply (nerr_block lyc Sc W mem md q _ _ HAR Hin); lia].
Qed.

Lemma vr_copy_kx : forall e F c tp pos lyc Sc (W : world SEGS) mem md mem', AR SEGS B lyc Sc W mem md ->
In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos -> In (vr_cb e c) (ablocks B lyc Sc) ->
vr_copy B e F c tp W mem -> vr_kx e W mem mem' -> vr_copy B e F c tp W mem'.
Proof.
intros e F c tp pos lyc Sc W mem md mem' HAR Hin4 HF Hin (Hfr & Hal & Hlen & Hptr & Hw) K. subst F.
pose proof asan_consts as (C1 & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md 4 pos HAR Hin4) as (B1 & B2 & _).
change (fs_frame_bytes 4) with 1024 in B2.
unfold vr_cb in Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrq.
assert (Htk : (length (Verbs.toks (e_D e)) <= 64)%nat)
  by (unfold Verbs.toks; rewrite length_firstn; unfold Verbs.line_words_max; lia).
split; [exact Hfr|]. split; [exact Hal|]. split; [exact Hlen|]. split.
- intros i p Hi.
  assert (Hi64 : (i < 64)%nat)
    by (rewrite <- Hlen in Htk; pose proof (proj1 (nth_error_Some tp i) ltac:(rewrite Hi; discriminate)); lia).
  intros kk Hkk. rewrite K; [exact (Hptr i p Hi kk Hkk) | lia | left; lia |].
  apply (nerr_frame lyc Sc W mem md pos _ HAR Hin4). lia.
- intros i p w Hi Hwi. destruct (Hw i p w Hi Hwi) as (Hs & Hl8 & Hp1 & Hp2).
  split; [|split; [exact Hl8 | split; [exact Hp1 | exact Hp2]]].
  apply (astr_atR_agree _ _ p w (Z.of_nat (length w) + 1) Hs); [lia|].
  intros kk Hkk. apply K; [lia | left; lia | apply (nerr_block lyc Sc W mem md c _ _ HAR Hin); lia].
Qed.

End e.
End f.
End d.
End VRL10.
