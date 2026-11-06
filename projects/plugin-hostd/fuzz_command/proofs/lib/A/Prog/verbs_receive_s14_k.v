(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the shared lemmas of the four one-call arms S14 QCLEAR, S15 POLICY, S16 LV2 and
   S17 POOL of the walk of verbs_receive (lib/A/Prog/verbs_receive_iface.v): memory transport through a symbolic run
   that writes nothing and through a recorder callee, the read-only environment at any journal state, the refusal
   stub 0x8dc9c (vr_pr) and the join 0x8dc94 (vr_hd) assembled from a route state, and the premises of a recorder
   callee at the call. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route verbs_receive_tail_m SlotWords.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString RtNumber RtAlloc04 RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.
(* stdpp's NoDup is in scope through BvBase; the block lists below use the standard library's *)
Local Notation NoDup := List.NoDup.

(* ---------------------------------------------------------------------------------------------------------------
   Lists of blocks *)
Definition zz_eqb (x y : Z * Z) : bool := (fst x =? fst y) && (snd x =? snd y).
Lemma zz_eqb_true : forall x y, zz_eqb x y = true <-> x = y.
Proof.
intros [a b] [c d]. unfold zz_eqb. cbn [fst snd]. rewrite andb_true_iff, !Z.eqb_eq.
split; [intros [-> ->]; reflexivity | intros E; injection E as -> ->; split; reflexivity].
Qed.
Definition zz_mem (x : Z * Z) (l : list (Z * Z)) : bool := existsb (zz_eqb x) l.
Lemma zz_mem_true : forall x l, zz_mem x l = true <-> In x l.
Proof.
intros x l. unfold zz_mem. rewrite existsb_exists. split.
- intros (y & Hy & E). apply zz_eqb_true in E. subst. exact Hy.
- intros H. exists x. split; [exact H | apply zz_eqb_true; reflexivity].
Qed.
Definition zz_minus (L K : list (Z * Z)) : list (Z * Z) := List.filter (fun x => negb (zz_mem x K)) L.
Lemma in_zz_minus : forall x L K, In x (zz_minus L K) <-> In x L /\ ~ In x K.
Proof.
intros x L K. unfold zz_minus. rewrite List.filter_In, negb_true_iff.
split; intros [H1 H2]; split; try exact H1.
- intros H. apply zz_mem_true in H. congruence.
- destruct (zz_mem x K) eqn:E; [apply zz_mem_true in E; contradiction | reflexivity].
Qed.
Lemma NoDup_app_disj : forall (l1 l2 : list (Z * Z)), NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
induction l1 as [|a l1 IH]; intros l2 H1 H2 Hd; [exact H2|]. cbn. inversion H1 as [|a' l1' Ha Hl1]; subst.
constructor.
- intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Ha Hin)|]. exact (Hd a (or_introl eq_refl) Hin).
- apply IH; [exact Hl1 | exact H2 |]. intros x Hx. apply Hd. right. exact Hx.
Qed.
Lemma perm_zz_minus : forall L K, NoDup L -> NoDup K -> (forall x, In x K -> In x L) ->
Permutation L (zz_minus L K ++ K).
Proof.
intros L K HL HK Hinc. apply Permutation.NoDup_Permutation; [exact HL | |].
- apply NoDup_app_disj; [unfold zz_minus; apply List.NoDup_filter; exact HL | exact HK |].
  intros x Hx. apply in_zz_minus in Hx. exact (proj2 Hx).
- intros x. rewrite in_app_iff, in_zz_minus. split.
  + intros Hx. destruct (in_dec (fun a b : Z * Z => ltac:(decide equality; apply Z.eq_dec)) x K) as [Hk|Hk];
    [right; exact Hk | left; split; assumption].
  + intros [[Hx _] | Hx]; [exact Hx | exact (Hinc x Hx)].
Qed.
Lemma NoDup_of_pairwise : forall l, Forall (fun x : Z * Z => 0 < snd x) l -> pairwise zdisjoint l -> NoDup l.
Proof.
induction l as [|x l IH]; intros Hpos Hp; [constructor|]. cbn in Hp. destruct Hp as [Hx Hl].
inversion Hpos as [|x' l' Hx0 Hl0]; subst. constructor; [|exact (IH Hl0 Hl)].
intros Hin. rewrite Forall_forall in Hx. specialize (Hx x Hin). unfold zdisjoint in Hx. lia.
Qed.
Lemma NoDup_perm_app_r : forall (L A K : list (Z * Z)), NoDup L -> Permutation L (A ++ K) -> NoDup K.
Proof.
intros L A K HL HP. pose proof (Permutation.Permutation_NoDup HP HL) as H. apply List.NoDup_app_remove_l in H. exact H.
Qed.
Lemma NoDup_perm_disj : forall (L A K : list (Z * Z)) x, NoDup L -> Permutation L (A ++ K) -> In x A -> ~ In x K.
Proof.
intros L A K x HL HP HA HK. pose proof (Permutation.Permutation_NoDup HP HL) as H. clear HP HL.
induction A as [|a A IH]; [destruct HA|]. cbn in H. inversion H as [|a' l' Ha Hl]; subst.
destruct HA as [<- | HA]; [apply Ha; apply in_or_app; right; exact HK | exact (IH HA Hl)].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Readers that agree everywhere *)
Definition rd_same (rd rd' : reader) : Prop := forall a, rd' a = rd a.
Lemma aval_mem_same : forall rd rd' a n v, rd_same rd rd' -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hs H k Hk. rewrite Hs. exact (H k Hk). Qed.
Lemma abytes_atR_same : forall rd rd' a l, rd_same rd rd' -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l Hs H i Hi. rewrite Hs. exact (H i Hi). Qed.
Lemma astr_atR_same : forall rd rd' p s, rd_same rd rd' -> astr_atR rd p s -> astr_atR rd' p s.
Proof. intros rd rd' p s Hs [H1 H2]. split; [exact (abytes_atR_same rd rd' p _ Hs H1) | exact H2]. Qed.
Lemma rdword_same : forall rd rd' a, rd_same rd rd' -> rdword rd' a = rdword rd a.
Proof. intros rd rd' a Hs. unfold rdword. rewrite !Hs. reflexivity. Qed.
Lemma atoks_atA_same : forall rd rd' tok tp tks cb ncb, rd_same rd rd' ->
atoks_atA rd tok tp tks cb ncb -> atoks_atA rd' tok tp tks cb ncb.
Proof.
intros rd rd' tok tp tks cb ncb Hs (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
- intros i p Hp. exact (aval_mem_same rd rd' _ _ _ Hs (H3 i p Hp)).
- intros i p w Hp Hw. destruct (H4 i p w Hp Hw) as (A1 & A2 & A3 & A4).
  split; [exact (astr_atR_same rd rd' _ _ Hs A1)|]. auto.
Qed.
Lemma rdword_of_aval : forall rd a v, aval_mem rd a 8 v -> 0 <= v < 2 ^ 64 -> rdword rd a = Some v.
Proof.
intros rd a v B Hr. unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
Lemma aval_of_abytes8 : forall rd a l v, abytes_atR rd a l -> length l = 8%nat ->
(forall k, (k < 8)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = le_byte v 8 k) -> aval_mem rd a 8 v.
Proof. intros rd a l v H Hl Hk k Hkk. rewrite (H k ltac:(lia)). rewrite Hk by exact Hkk. reflexivity. Qed.
Lemma cmd_got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [H _]. unfold cmd_ro_bytes in H.
repeat match type of H with _ /\ (_ /\ (_ /\ (_ /\ _))) => destruct H as [_ H] end.
destruct H as (G1 & G2 & G3 & G4).
split; [|split; [|split]]; (eapply aval_of_abytes8; [eassumption | reflexivity |]);
intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.
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

Lemma rd_same_of_frame : forall E rs (W : world SEGS) m m',
Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> rd_same (rdW W m) (rdW W m').
Proof.
intros E rs W m m' Hro Hf a. apply aview_eq_of. apply Hf. intros (r & Hin & Hr).
rewrite Forall_forall in Hro. specialize (Hro r Hin). lia.
Qed.
Lemma vr_frame_same : forall lyc (W : world SEGS) m m' pos F sh, rd_same (rdW W m) (rdW W m') ->
vr_frame lyc W m pos F sh -> vr_frame lyc W m' pos F sh.
Proof.
intros lyc W m m' pos F sh Hs (H1 & H2 & H3). split; [exact H1|].
split; [rewrite (rdword_same _ _ _ Hs); exact H2|]. intros i Hi. rewrite Hs. exact (H3 i Hi).
Qed.
Lemma vr_saved_same : forall e (W : world SEGS) m m', rd_same (rdW W m) (rdW W m') -> vr_saved e W m -> vr_saved e W m'.
Proof. intros e W m m' Hs H j r Hj. exact (aval_mem_same _ _ _ _ _ Hs (H j r Hj)). Qed.
Lemma vr_spill_same : forall e (W : world SEGS) m m' l, rd_same (rdW W m) (rdW W m') -> vr_spill e W m l -> vr_spill e W m' l.
Proof.
intros e W m m' l Hs H. unfold vr_spill in *. eapply Forall_impl; [|exact H].
intros ov Hov. exact (aval_mem_same _ _ _ _ _ Hs Hov).
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
Hypothesis ROA : vr_ro_of_aro B.

Lemma vr_line_same : forall e q (W : world SEGS) m m', rd_same (rdW W m) (rdW W m') -> vr_line B e q W m -> vr_line B e q W m'.
Proof. intros e q W m m' Hs [H1 H2]. split; [exact H1 | exact (astr_atR_same _ _ _ _ Hs H2)]. Qed.
Lemma vr_copy_same : forall e F c tp (W : world SEGS) m m', rd_same (rdW W m) (rdW W m') ->
vr_copy B e F c tp W m -> vr_copy B e F c tp W m'.
Proof. intros e F c tp W m m' Hs [H1 H2]. split; [exact H1 | exact (atoks_atA_same _ _ _ _ _ _ _ Hs H2)]. Qed.
Lemma rec_repA_same : forall ly S rd rd' R O, rd_same rd rd' -> rec_repA B ly S rd R O -> rec_repA B ly S rd' R O.
Proof.
intros ly S rd rd' R O Hs H. apply (rec_repA_agree B ly S ly S rd rd' R O H (fun pn _ Hb => Hb));
intros; apply Hs.
Qed.

Lemma in_img_of_ro : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof. intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]. Qed.
Lemma inFP_app_or : forall l1 l2 a, inFP (l1 ++ l2) a -> inFP l1 a \/ inFP l2 a.
Proof.
intros l1 l2 a (r & Hr & Ha). apply in_app_or in Hr as [Hr|Hr]; [left | right]; exists r; split; assumption.
Qed.
Lemma vr_ent_O_blocks : forall e pn, vr_ent B MT e -> In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e)).
Proof.
intros e pn He Hpn. destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREC & _).
exact (rec_repA_in_blocks B _ _ _ _ _ _ HREC Hpn).
Qed.
(* statement pass 4: vr_ent's last conjunct is rounding mode 0 at the entry FP state (PaFx's frm0); it is the only
   conjunct that names the FP state, so vr_ent holds at every FP state fxrel reaches (verbs_receive.v vr_ent_fxr, under
   this file's name) *)
Lemma v14_ent_frm0 : forall e, vr_ent B MT e -> frm0 fx.
Proof.
intros e He. unfold vr_ent in He. cbv zeta in He.
repeat lazymatch type of He with _ /\ _ => apply proj2 in He end. exact He.
Qed.
Lemma v14_ent_fxr : forall f0 f1 e, vr_ent (fx := f0) B MT e -> fxrel f0 f1 -> vr_ent (fx := f1) B MT e.
Proof.
intros f0 f1 e He Hr. revert He. unfold vr_ent. cbv zeta. intros He.
repeat lazymatch type of He with
| _ /\ _ => let H1 := fresh "H" in destruct He as [H1 He]; split; [exact H1|]
end.
exact (fxrel_frm0 f0 f1 He Hr).
Qed.
Lemma vr_fp_spares : forall e a, vr_ent B MT e -> in_roP SEGS RLO RHI a -> fp_spares (vr_fp e) a.
Proof.
intros e a He Hro. pose proof He as (HPRE & _). pose proof HPRE as (HAR & _).
apply fp_spares_closed.
- apply sink_closed_pos. unfold vr_fp, VERBS_RECEIVE_PG. apply Forall_app. split.
  + repeat constructor; cbn; unfold A_G_REC, A_REC_SPILL, A_G_QUITTING; lia.
  + unfold ablocks_fp. apply Forall_map. apply Forall_forall. intros [p n] Hpn. cbn [fst].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (vr_ent_O_blocks e _ He Hpn)) as (_ & H4 & _). lia.
- intros Hf. apply inFP_app_or in Hf as [Hf | Hf].
  + apply (RPG a); [|exact Hro]. exact Hf.
  + destruct (inFP_ablocks_fp_inv (e_O e) a Hf) as (p & n & Hpn & Hr).
    exact (blk_img SEGS B LAWS _ _ _ _ _ p n a HAR (vr_ent_O_blocks e _ He Hpn) Hr (in_img_of_ro a Hro)).
Qed.
Lemma vr_env_of_journal : forall e own ly2 S2 (W2 : world SEGS) mem2 md2 k,
vr_ent B MT e ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) own ly2 S2 W2 mem2 md2 k ->
vr_env B W2 mem2.
Proof.
intros e own ly2 S2 W2 mem2 md2 k He HJ.
pose proof He as (_ & HROD & _).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (HRO2 : arodata_okP SEGS RLO RHI B (rdW W2 mem2)).
{ intros a Hro Ho Herr. rewrite (F3 a (in_img_of_ro a Hro) Ho Herr (vr_fp_spares e a He Hro)). exact (HROD a Hro Ho Herr). }
pose proof (ROA ly2 S2 W2 mem2 md2 HAR2 HRO2) as HCR.
destruct (RECC ly2 S2 W2 mem2 md2 HAR2) as (Hfl & Hag & Her).
split; [exact HRO2|]. split; [exact (cmd_got_of_ro _ HCR)|]. split; [exact HCR|].
split; [exact Hag|]. split; [exact Hfl | exact Her].
Qed.
Lemma ablocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
assert (HP : forall p n, In (p, n) (ablocks B ly S) -> pairwise zdisjoint (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B ly S)) /\ 0 < req_size n).
{ intros p n Hin. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & Hpw & Hn).
  pose proof (req_size_pos n ltac:(lia)). split; [exact Hpw | lia]. }
destruct (ablocks B ly S) as [|[p n] l] eqn:El; [constructor|].
apply (NoDup_map_inv (fun b : Z * Z => (fst b, req_size (snd b)))).
apply NoDup_of_pairwise; [|exact (proj1 (HP p n (or_introl eq_refl)))].
apply Forall_forall. intros [x m] Hx. apply in_map_iff in Hx as ([p' n'] & E & Hx). injection E as <- <-. cbn [snd].
exact (proj2 (HP p' n' Hx)).
Qed.

(* the refusal stub 0x8dc9c from a route state whose memory a run has not changed *)
Lemma vr_pr9c_of : forall e (W : world SEGS) pos F q c tp lyc Sc regsc memc mdc k nm r regs' mem' md',
vr_ent B MT e ->
VRR.route (Verbs.toks (e_D e)) = r -> Verbs.toks (e_D e) <> [] ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_rt e F q (hd 0 tp) r) (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
rd_same (rdW W memc) (rdW W mem') ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc W mem' md' k ->
vr_rv regs' (vr_base B e ++ vr_rl_pr e F q c 0x8dc9c (-902)) ->
vr_h (e_R e) (e_D e) = (e_R e, resp (-902), false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_RESP ->
vr_pr B MT e 0x8dc9c W (cfg_at SEGS (vr_pc 0x8dc9c) regs' mem' md').
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm r regs' mem' md' He Hr Hne Hcore Hline Hcopy Hs HJ' Hrv Hh Hk1.
destruct Hcore as (HJ & Hk & Hmet & Hnm & Hfr & _ & Hsav & Hspl & _ & Hrec & HdO & Hperm & Hq).
exists (-902), (e_R e), (e_O e), pos, F, q, c, tp, lyc, Sc, regs', mem', md', k, nm.
split; [reflexivity|]. split; [intros _; reflexivity|]. split; [lia|]. split; [exact Hh|]. split; [exact Hne|].
split; [unfold vr_pr_ntok; cbn -[Verbs.toks]; destruct (Verbs.toks (e_D e)); [congruence | cbn; lia]|].
split; [|split; [exact (vr_line_same _ _ _ _ _ Hs Hline) | exact (vr_copy_same _ _ _ _ _ _ _ Hs Hcopy)]].
split; [exact HJ'|]. split; [rewrite Hk1; lia|]. split; [exact Hmet|]. split; [unfold VR_NM_PR, VR_NM_PRE in *; lia|].
split; [exact (vr_frame_same _ _ _ _ _ _ _ Hs Hfr)|]. split; [exact Hrv|].
split; [exact (vr_saved_same _ _ _ _ Hs Hsav)|]. split; [exact (vr_spill_same _ _ _ _ _ Hs Hspl)|].
split; [exact (vr_env_of_journal e _ _ _ _ _ _ _ He HJ')|].
split; [exact (rec_repA_same _ _ _ _ _ _ Hs Hrec)|]. split; [exact HdO|]. split; [exact Hperm|].
exact (aval_mem_same _ _ _ _ _ Hs Hq).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Through a recorder callee: its footprint is g_rec, record.spill and the recorder's blocks *)
Hypothesis MTL : ameter_laws MT.
Hypothesis PROGU : vr_prog_unowned B.
Definition vr_cfp (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
Lemma cfp_cases : forall O a, inFP (vr_cfp O) a -> in_img SEGS a \/ exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a Ha. unfold vr_cfp in Ha. apply inFP_cons in Ha as [Ha | Ha].
- left. apply (PROGU a). unfold cmd_PG. apply inFP_cons. left. unfold REC_SIZE in Ha. exact Ha.
- apply inFP_cons in Ha as [Ha | Ha].
  + left. apply (PROGU a). unfold cmd_PG. apply inFP_cons. right. apply inFP_cons. left. unfold SC_SIZE in Ha. exact Ha.
  + right. exact (inFP_ablocks_fp_inv O a Ha).
Qed.
Lemma not_cfp_hi : forall O ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) -> alloc_ceiling <= a -> ~ inFP (vr_cfp O) a.
Proof.
intros O ly S W mem md a HAR HO Ha Hf. pose proof asan_consts as (C1 & _).
destruct (cfp_cases O a Hf) as [Himg | (p & n & Hpn & Hr)].
- pose proof (pa_img_range a Himg). lia.
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & _ & Hc & _). lia.
Qed.
Lemma not_cfp_block : forall O ly S (W : world SEGS) mem md p n i,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
In (p, n) (ablocks B ly S) -> ~ In (p, n) O -> 0 <= i < req_size n -> ~ inFP (vr_cfp O) (p + i).
Proof.
intros O ly S W mem md p n i HAR HO Hin HnO Hi Hf. destruct (cfp_cases O _ Hf) as [Himg | (p' & n' & Hpn' & Hr)].
- exact (blk_img SEGS B LAWS _ _ _ _ _ p n (p + i) HAR Hin ltac:(lia) Himg).
- assert (Hne : (p', n') <> (p, n)) by (intros E; rewrite E in Hpn'; exact (HnO Hpn')).
  pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ p' n' p n HAR (HO _ Hpn') Hin Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma frame_not_block : forall ly S (W : world SEGS) mem md b m cid pos a,
AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ (b <= a < b + req_size m).
Proof.
intros ly S W mem md b m cid pos a HAR Hbin HinC Hr Hb.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md b m cid pos HAR Hbin HinC) as Hd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
unfold zdisjoint, frame_rng, in_zr in *. cbn [fst snd] in *.
pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(zlia)).
pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(zlia)).
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
destruct Hr as [Hr|Hr]; zlia.
Qed.
Lemma not_cfp_frame : forall O ly S (W : world SEGS) mem md cid pos a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) -> In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP (vr_cfp O) a.
Proof.
intros O ly S W mem md cid pos a HAR HO HinC Hr Hf. destruct (cfp_cases O a Hf) as [Himg | (p & n & Hpn & Hp)].
- destruct Hr as [Hr | Hr].
  + unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. exact (frm_img SEGS B LAWS _ _ _ _ _ cid pos a HAR HinC Hr Himg).
  + destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
    pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (pa_img_range a Himg). pose proof (fs_frame_bytes_nonneg cid).
    pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(zlia)). unfold in_zr in Hr. cbn [fst snd] in Hr. zlia.
- exact (frame_not_block ly S W mem md p n cid pos a HAR (HO _ Hpn) HinC Hr Hp).
Qed.

Section call.
Variables (O : list (Z * Z)) (STK1 sp1 : Z) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (mdc : Model) (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (mem2 : word -> option byte) (md2 : Model) (k1 : Z).
Hypothesis HAR : AR SEGS B lyc Sc W memc mdc.
Hypothesis HO : forall pn, In pn O -> In pn (ablocks B lyc Sc).
Hypothesis HJc : ajournal SEGS B STK1 sp1 (vr_cfp O) lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1.
Lemma call_kept_hi : forall a, sp1 <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memc a.
Proof.
intros a Ha. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & _) & _).
eapply aview_above_of_journal; [exact HJc | exact Ha |]. apply (not_cfp_hi O lyc Sc W memc mdc a HAR HO). lia.
Qed.
Lemma call_kept_block : forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) O -> In (p, n) (ablocks B ly2 S2) ->
0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W memc (p + i).
Proof.
intros p n i H1 HnO H2 Hi. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i H1 H2 Hi). exact (not_cfp_block O lyc Sc W memc mdc p n i HAR HO H1 HnO Hi).
Qed.
Lemma call_kept_frame : forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
rdW W2 mem2 a = rdW W memc a.
Proof.
intros cid pos a Hin Hr. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
apply (F4 cid pos a Hin Hr). exact (not_cfp_frame O lyc Sc W memc mdc cid pos a HAR HO Hin Hr).
Qed.
Lemma call_kept_quit : forall v, aval_mem (rdW W memc) A_G_QUITTING 4 v -> aval_mem (rdW W2 mem2) A_G_QUITTING 4 v.
Proof.
intros v H. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply (aval_mem_agree _ _ _ _ _ H). intros k Hk. change (Z.of_nat 4) with 4 in Hk.
assert (HPG : inFP cmd_PG (A_G_QUITTING + k)).
{ unfold cmd_PG. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. left. lia. }
destruct (PROGU _ HPG) as (Himg & Hown & Herr).
apply (F3 _ Himg Hown Herr). apply fp_spares_closed.
- apply sink_closed_pos. unfold vr_cfp. constructor; [cbn; unfold A_G_REC; lia|]. constructor; [cbn; unfold A_REC_SPILL; lia|].
  unfold ablocks_fp. apply Forall_map. apply Forall_forall. intros [p n] Hpn. cbn [fst].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & H4 & _). lia.
- intros Hf. destruct (cfp_cases O _ Hf) as [_ | (p & n & Hpn & Hr)].
  + unfold vr_cfp in Hf. apply inFP_cons in Hf as [Hf | Hf]; [unfold A_G_REC, REC_SIZE, A_G_QUITTING in *; lia|].
    apply inFP_cons in Hf as [Hf | Hf]; [unfold A_REC_SPILL, SC_SIZE, A_G_QUITTING in *; lia|].
    destruct (inFP_ablocks_fp_inv O _ Hf) as (p & n & Hpn & Hr).
    exact (blk_img SEGS B LAWS _ _ _ _ _ p n _ HAR (HO _ Hpn) Hr Himg).
  + exact (blk_img SEGS B LAWS _ _ _ _ _ p n _ HAR (HO _ Hpn) Hr Himg).
Qed.
Lemma call_frame : forall pos F sh, In (4, pos) (frames Sc) -> vr_frame lyc W memc pos F sh -> vr_frame ly2 W2 mem2 pos F sh.
Proof.
intros pos F sh Hin (H1 & H2 & H3). pose proof HJc as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (E1 : frame_addr ly2 4 pos = frame_addr lyc 4 pos) by (unfold frame_addr; rewrite EF; reflexivity).
assert (E2 : flag_addr ly2 4 pos = flag_addr lyc 4 pos) by (unfold flag_addr; rewrite EF; reflexivity).
assert (EB : fs_frame_bytes 4 = 1024) by reflexivity.
split; [rewrite E1; exact H1|]. split.
- rewrite E2, <- H2. apply rdword_ext. intros k Hk. apply (call_kept_frame 4 pos); [exact Hin|].
  left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EB, <- H1. lia.
- intros i Hi. rewrite <- (H3 i Hi). apply (call_kept_frame 4 pos); [exact Hin|].
  right. unfold in_zr. cbn [fst snd]. rewrite EB, <- H1. change (1024 / 8) with 128. lia.
Qed.
Lemma call_astr : forall p n x s, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) O -> In (p, n) (ablocks B ly2 S2) ->
p <= x -> x + Z.of_nat (length s) + 1 <= p + n -> astr_atR (rdW W memc) x s -> astr_atR (rdW W2 mem2) x s.
Proof.
intros p n x s H1 HnO H2 Hx Hxs H. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR H1) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hrs].
apply (astr_atR_agree _ _ x s (Z.of_nat (length s) + 1) H); [lia|]. intros k Hk.
replace (x + k) with (p + (x - p + k)) by lia. apply (call_kept_block p n); [exact H1 | exact HnO | exact H2 | lia].
Qed.
End call.

(* the registers a callee keeps *)
Lemma vr_rv_preserved : forall (regs regs' : bvmap 5 word) l, aregs_preserved regs regs' ->
Forall (fun rv => acallee_saved (fst rv)) l -> vr_rv regs l -> vr_rv regs' l.
Proof.
intros regs regs' l HP Hl H. unfold vr_rv in *. rewrite Forall_forall in *. intros rv Hrv.
rewrite (HP (fst rv) (Hl rv Hrv)). exact (H rv Hrv).
Qed.
Lemma rec_repA_iff : forall ly S rd R O1 O2, (forall pn, In pn O1 <-> In pn O2) -> rec_repA B ly S rd R O2 -> rec_repA B ly S rd R O1.
Proof. intros ly S rd R O1 O2 HE (Q & HA & HQ). exists Q. split; [exact HA|]. intros pn. rewrite HE. exact (HQ pn). Qed.

End e.
End f.
End d.
