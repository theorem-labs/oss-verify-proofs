(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the call kit of the segment S23 (pin_clear, 0x8d7b4-0x8d7dc) of the walk of
   verbs_receive on the ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v,
   vr_s23_stmt). The B port of the parts of lib/A/Prog/verbs_receive_s20_k.v that S23 uses: the model of the route
   RPinclr, a boundary state across a recorder callee (the walk's own memory kept, the recorder's blocks the
   callee's post), and the calls of pins_clear (its post is apost_baseF: PaFx.v cl_callS_wideF) and
   lv2_refusals_forget (apost_base: PaNoChain.v cl_callS_wide). The frame chain at a call is the B kit's
   vr_chain_at (statement pass 5, no astack_pres); B's allocator constants (EV_RECORD, EV_ARG_S, EV_ANSWER_CODE,
   XM_RECORD, XM_ARG_S, XM_ANSWER_CODE) are unfolded where A had xstrdup and arg_i. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c arg_s_c record_c hand_back_c answer_code_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pins_clear_c lv2_refusals_forget_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_live.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s30_m verbs_receive_s30_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* ---------------------------------------------------------------------------------------------------------------
   The model's side of the route RPinclr: with one argument the step pins_clear, then lv2_refusals_forget(NULL) when
   its code is 0 (VerbsRun.pins_follow); else reject. The second recorder call is charged on the state the first
   left (verbs_receive_c.v ev_step, SPinClear). *)
Ltac rt_chain H :=
  cbv beta iota in H;
  repeat (match type of H with context [if ?b then _ else _] => destruct b; cbv beta iota in H end); try discriminate H.

Lemma vk_ev_route_not_cp : forall R ln v args s,
  Verbs.list_eqb v Verbs.Lit.verb_chain = false -> Verbs.list_eqb v Verbs.Lit.verb_pin_set = false ->
  ev_route R ln (v :: args) s = ev_step R s.
Proof. intros R ln v args s H1 H2. unfold ev_route. rewrite H1, H2. reflexivity. Qed.

Lemma vk_route_cp_pinclr : forall v args, VRR.route (v :: args) = VRR.RPinclr ->
  Verbs.list_eqb v Verbs.Lit.verb_chain = false /\ Verbs.list_eqb v Verbs.Lit.verb_pin_set = false.
Proof.
intros v args H. split.
- destruct (Verbs.list_eqb v Verbs.Lit.verb_chain) eqn:E; [exfalso|reflexivity].
  unfold VRR.route, VRR.route_mid in H. rewrite E in H. rt_chain H.
- destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_set) eqn:E; [exfalso|reflexivity].
  unfold VRR.route, VRR.route_mid in H. rewrite E in H. rt_chain H.
Qed.

Lemma vk_pinclr_two : forall R D v a, Verbs.toks D = [v; a] -> VRR.route (Verbs.toks D) = VRR.RPinclr ->
  vr_h R D = (VerbsRun.pins_follow (fst (pins_clear_m R (Some a))) (snd (pins_clear_m R (Some a))), false) /\
  vr_k1 R D = 2 + (EV_PINS_CLEAR R + (if snd (pins_clear_m R (Some a)) =? 0
     then EV_LV2_REFUSALS_FORGET (fst (pins_clear_m R (Some a))) else 0) + EV_SUP_RESP).
Proof.
intros R D v a T Hr. rewrite T in Hr.
assert (St : vr_st D = Verbs.SPinClear a).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. rewrite Hr. reflexivity. }
destruct (vk_route_cp_pinclr v [a] Hr) as [Hc1 Hc2].
split.
- unfold vr_h. rewrite St. cbn [VerbsRun.run_step]. destruct (pins_clear_m R (Some a)); reflexivity.
- unfold vr_k1. rewrite St, T. rewrite (vk_ev_route_not_cp _ _ _ _ _ Hc1 Hc2). cbn [ev_step].
  destruct (pins_clear_m R (Some a)); reflexivity.
Qed.

Lemma vk_pinclr_rej : forall R D, VRR.route (Verbs.toks D) = VRR.RPinclr -> Verbs.toks D <> [] ->
  length (Verbs.toks D) <> 2%nat ->
  vr_h R D = (R, resp (-902), false) /\ vr_k1 R D = 2 + EV_SUP_RESP.
Proof.
intros R D Hr Hne Hl. destruct (Verbs.toks D) as [|v args] eqn:T; [congruence|].
assert (St : vr_st D = Verbs.reject).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. rewrite Hr. cbn [VRR.plan_at].
  destruct args as [|a [|b args]]; [reflexivity | cbn in Hl; lia | reflexivity]. }
destruct (vk_route_cp_pinclr v args Hr) as [Hc1 Hc2].
split.
- unfold vr_h. rewrite St. reflexivity.
- unfold vr_k1. rewrite St, T. rewrite (vk_ev_route_not_cp _ _ _ _ _ Hc1 Hc2). reflexivity.
Qed.

Lemma vk_calls_pins_clear : forall R u, (length (r_calls (fst (pins_clear_m R u))) <= S (length (r_calls R)))%nat.
Proof.
intros R u. unfold pins_clear_m, rec_stub_code, rec_answer_code, rec_mix, rec_record, set_state, set_answer, set_calls, set_spill.
destruct (Nat.ltb _ 16); cbn [r_calls r_refuse r_code fst]; destruct (_ =? 0); cbn [r_calls fst]; rewrite ?length_app; cbn [length]; lia.
Qed.
Lemma vk_code_pins_clear : forall R u, snd (pins_clear_m R u) = 0 \/ snd (pins_clear_m R u) = r_code R.
Proof.
intros R u. unfold pins_clear_m, rec_stub_code, rec_answer_code, rec_mix, rec_record, set_state, set_answer, set_calls, set_spill.
destruct (Nat.ltb _ 16); cbn [r_calls r_refuse r_code fst snd]; destruct (_ =? 0); cbn [snd]; auto.
Qed.
Lemma vk_rsf_nonneg : forall R, 0 <= rec_spill_frees R.
Proof. intros R. unfold rec_spill_frees. destruct (Nat.ltb _ _); lia. Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Lists of blocks *)
Lemma vk_nodup_app : forall (l1 l2 : list (Z * Z)), List.NoDup l1 -> List.NoDup l2 ->
  (forall x, In x l1 -> ~ In x l2) -> List.NoDup (l1 ++ l2).
Proof.
induction l1 as [|a l1 IH]; intros l2 H1 H2 Hd; [exact H2|]. cbn. apply List.NoDup_cons_iff in H1 as [Ha H1].
constructor.
- intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Ha Hin) | exact (Hd a (or_introl eq_refl) Hin)].
- apply IH; [exact H1 | exact H2 | intros x Hx; apply Hd; right; exact Hx].
Qed.
Lemma vk_nodup_app_r : forall (l1 l2 : list (Z * Z)), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof. induction l1 as [|a l1 IH]; intros l2 H; [exact H|]. cbn in H. apply List.NoDup_cons_iff in H as [_ H]. exact (IH _ H). Qed.
Lemma vk_nodup_app_dis : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
induction l1 as [|a l1 IH]; intros l2 x H Hx; [destruct Hx|]. cbn in H. apply List.NoDup_cons_iff in H as [Ha H].
destruct Hx as [<-|Hx]; [intros Hin; apply Ha; apply in_or_app; right; exact Hin | exact (IH _ _ H Hx)].
Qed.
Definition vk_pz_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Definition vk_inb (O : list (Z * Z)) (pn : Z * Z) : bool := if in_dec vk_pz_eq_dec pn O then true else false.
Lemma vk_inb_true : forall O pn, vk_inb O pn = true <-> In pn O.
Proof. intros O pn. unfold vk_inb. destruct (in_dec vk_pz_eq_dec pn O); split; intros H; try discriminate; auto. Qed.
Lemma vk_in_filter_inb : forall O l pn, In pn (List.filter (vk_inb O) l) <-> In pn l /\ In pn O.
Proof. intros O l pn. rewrite filter_In, vk_inb_true. tauto. Qed.

(* the live blocks after a recorder callee: those of the walk and of the entry's rest stay, the recorder's are the
   callee's O1, and the callee's new blocks are added (a new block is none of the walk's or the rest's) *)
Lemma vk_perm_after : forall bl0 bl1 Oc O1 tmps rest new,
  List.NoDup bl0 -> List.NoDup bl1 -> Permutation bl0 (Oc ++ tmps ++ rest) ->
  (forall pn, In pn bl0 -> ~ In pn Oc -> In pn bl1) ->
  (forall pn, In pn bl1 -> (In pn bl0 /\ ~ In pn Oc) \/ In pn O1 \/ In pn new) ->
  (forall pn, In pn O1 -> In pn Oc \/ ~ In pn bl0) ->
  (forall pn, In pn new -> In pn bl1) ->
  List.NoDup new -> (forall pn, In pn new -> (In pn bl0 -> In pn Oc) /\ ~ In pn O1) ->
  Permutation bl1 (List.filter (vk_inb O1) bl1 ++ (new ++ tmps) ++ rest).
Proof.
intros bl0 bl1 Oc O1 tmps rest new Hn0 Hn1 HP Hk Hc HO1 Hnw Hnn Hnd.
assert (Hnd0 : List.NoDup (Oc ++ tmps ++ rest)) by exact (Permutation_NoDup HP Hn0).
assert (Hin0 : forall pn, In pn (tmps ++ rest) -> In pn bl0 /\ ~ In pn Oc).
{ intros pn Hpn. split; [apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hpn|].
  intros HO. exact (vk_nodup_app_dis _ _ pn Hnd0 HO Hpn). }
apply NoDup_Permutation.
- exact Hn1.
- rewrite <- app_assoc. apply vk_nodup_app; [apply List.NoDup_filter; exact Hn1|apply vk_nodup_app; [exact Hnn | exact (vk_nodup_app_r _ _ Hnd0)|]|].
  + intros x Hx Hx'. destruct (Hnd x Hx) as [Hx0 _]. destruct (Hin0 x Hx') as [Hb HnO]. exact (HnO (Hx0 Hb)).
  + intros x Hx Hx'. apply vk_in_filter_inb in Hx as [_ HxO]. apply in_app_or in Hx' as [Hx'|Hx'].
    * exact (proj2 (Hnd x Hx') HxO).
    * destruct (Hin0 x Hx') as [Hb HnO]. destruct (HO1 x HxO) as [H|H]; [exact (HnO H) | exact (H Hb)].
- intros x. rewrite <- app_assoc. rewrite !in_app_iff, vk_in_filter_inb. split.
  + intros Hx. destruct (Hc x Hx) as [[Hb HnO]|[HO|Hw]].
    * right. right. assert (Hx' : In x (Oc ++ tmps ++ rest)) by exact (Permutation_in _ HP Hb).
      rewrite !in_app_iff in Hx'. tauto.
    * left. split; [exact Hx | exact HO].
    * right. left. exact Hw.
  + intros [[Hx _]|[Hw|Ht]]; [exact Hx | exact (Hnw x Hw) |].
    destruct (Hin0 x ltac:(apply in_app_iff; exact Ht)) as [Hb HnO]. exact (Hk x Hb HnO).
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

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the record facts of the interface (the assembly discharges each by exact from lib/B/Prog/CmdRec*.v) *)
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HB : YF0m.CmdBSyms B.

Lemma vk_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof. intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]. Qed.

Lemma vk_aro_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall a, in_roP SEGS RLO RHI a -> ~ inFP FP a) -> ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HFP Hso HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a (vk_ro_img a Hro) Ho He (fp_spares_closed FP a Hso (HFP a Hro))). exact (HR a Hro Ho He).
Qed.

Definition vk_rec_fp (O : list (Z * Z)) : list (Z * Z) :=
  (A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma vk_rec_fp_inv : forall O a, inFP (vk_rec_fp O) a ->
  inFP cmd_PG a \/ exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a Ha. unfold vk_rec_fp in Ha. apply inFP_cons in Ha as [Ha|Ha].
- left. unfold cmd_PG. apply inFP_cons. left. unfold REC_SIZE in Ha. exact Ha.
- apply inFP_cons in Ha as [Ha|Ha].
  + left. unfold cmd_PG. apply inFP_cons. right. apply inFP_cons. left. unfold SC_SIZE in Ha. exact Ha.
  + right. exact (inFP_ablocks_fp_inv O a Ha).
Qed.

Lemma vk_rec_fp_not_ro : forall ly S W mem md O, AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  forall a, in_roP SEGS RLO RHI a -> ~ inFP (vk_rec_fp O) a.
Proof.
intros ly S W mem md O HAR HO a Hro Ha. destruct (vk_rec_fp_inv O a Ha) as [Hpg | (p & n & Hpn & Hr)].
- exact (RPG a Hpg Hro).
- exact (blk_img SEGS B LAWS _ _ _ _ _ p n a HAR (HO _ Hpn) Hr (vk_ro_img a Hro)).
Qed.

Lemma vk_rec_fp_closed : forall ly S W mem md O, AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  ~ YI16.sink_open_fp (vk_rec_fp O).
Proof.
intros ly S W mem md O HAR HO. unfold vk_rec_fp.
apply sink_closed_cons; [cbn; unfold A_G_REC; lia|]. apply sink_closed_cons; [cbn; unfold A_REC_SPILL; lia|].
apply sink_closed_ablocks_fp. apply Forall_forall. intros [p n] Hpn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & H4 & _). cbn. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The walk's own memory: the real frame's saves and spills, the side-stack frame and its shadow, the line and copy
   blocks. Every piece of vr_core and of the boundary that reads memory reads only these bytes, besides the recorder's
   statics and blocks, g_quitting and the read-only image. *)
Definition vk_wrange (e : vrE) (F q c a : Z) : Prop :=
  (vr_s1 e <= a < vr_s1 e + 80) \/ (vr_sp0 e - 104 <= a < vr_sp0 e) \/
  (F <= a < F + 1024) \/ (shadow_addr F <= a < shadow_addr F + 128) \/
  (q <= a < q + req_size (vr_l (e_n e) (e_D e) + 1)) \/
  (c <= a < c + req_size (Z.of_nat (length (Verbs.line (e_D e))) + 1)).
Definition vk_wkeep (e : vrE) (F q c : Z) (rd rd' : reader) : Prop := forall a, vk_wrange e F q c a -> rd' a = rd a.

Lemma vk_s1_bounds : forall e, vr_sp0 e - 224 < vr_s1 e <= vr_sp0 e - 192 /\ vr_s1 e mod 32 = 0.
Proof.
intros e. unfold vr_s1. pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as Hm.
split.
- generalize dependent ((vr_sp0 e - 192) mod 32). intros X HX. lia.
- rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity.
Qed.
Lemma vk_s1_ge : forall e, vr_sp0 e mod 16 = 0 -> vr_sp0 e - 208 <= vr_s1 e /\ (vr_s1 e - vr_sp0 e) mod 16 = 0.
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

Lemma vk_line_le : forall e, Z.of_nat (length (e_D e)) = e_n e ->
  Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e).
Proof. intros e Hn. unfold vr_l. rewrite <- Hn. exact (vrm_line_le (e_D e)). Qed.

Lemma vk_saved_keep : forall e F q c W mem W' mem', vk_wkeep e F q c (rdW W mem) (rdW W' mem') ->
  vr_saved e W mem -> vr_saved e W' mem'.
Proof.
intros e F q c W mem W' mem' HK HS j r Hj. apply (aval_mem_agree _ _ _ 8 _ (HS j r Hj)).
assert (Hjl : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
cbn [length vr_saved_regs] in Hjl.
intros k Hk. apply HK. right; left. pose proof (vk_s1_bounds e). change (Z.of_nat 8) with 8 in Hk. lia.
Qed.

Lemma vk_spill_keep : forall e F q c W mem W' mem' sl, vk_wkeep e F q c (rdW W mem) (rdW W' mem') ->
  Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 80) sl -> vr_spill e W mem sl -> vr_spill e W' mem' sl.
Proof.
intros e F q c W mem W' mem' sl HK Hsl HS. unfold vr_spill in *. rewrite Forall_forall in *. intros ov Hov.
apply (aval_mem_agree _ _ _ 8 _ (HS ov Hov)). intros k Hk. apply HK. left.
pose proof (Hsl ov Hov). change (Z.of_nat 8) with 8 in Hk. lia.
Qed.

Lemma vk_sl3_ok : forall F q c, Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 80) (vr_sl3 F q c).
Proof. intros F q c. unfold vr_sl3. repeat constructor; cbn; lia. Qed.

Lemma vk_frame_keep : forall e q c lyc ly' W mem W' mem' pos F sh, ly_F ly' = ly_F lyc ->
  vk_wkeep e F q c (rdW W mem) (rdW W' mem') -> vr_frame lyc W mem pos F sh -> vr_frame ly' W' mem' pos F sh.
Proof.
intros e q c lyc ly' W mem W' mem' pos F sh EF HK (HF & Hfl & Hsh). unfold vr_frame.
assert (E1 : frame_addr ly' 4 pos = frame_addr lyc 4 pos) by (unfold frame_addr; rewrite EF; reflexivity).
assert (E2 : flag_addr ly' 4 pos = flag_addr lyc 4 pos) by (unfold flag_addr; rewrite EF; reflexivity).
split; [rewrite E1; exact HF|]. split.
- rewrite E2, <- Hfl. apply rdword_ext. intros k Hk. apply HK. right; right; left. lia.
- intros i Hi. rewrite <- (Hsh i Hi). apply HK. right; right; right; left. lia.
Qed.

Lemma vk_line_keep : forall e F q c W mem W' mem', Z.of_nat (length (e_D e)) = e_n e ->
  vk_wkeep e F q c (rdW W mem) (rdW W' mem') -> vr_line B e q W mem -> vr_line B e q W' mem'.
Proof.
intros e F q c W mem W' mem' Hn HK [Hf Hs]. split; [exact Hf|].
apply (astr_atR_agree _ _ q _ (Z.of_nat (length (Verbs.line (e_D e))) + 1) Hs); [lia|].
intros k Hk. apply HK. right; right; right; right; left.
pose proof (vk_line_le e Hn). pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [_ Hr]. lia.
Qed.

Lemma vk_copy_keep : forall e F q c tp W mem W' mem', vk_wkeep e F q c (rdW W mem) (rdW W' mem') ->
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
Lemma vk_wkeep_call : forall e pos F q c lyc Sc (Wc : world SEGS) memc mdc STK1 FP1 ly2 S2 W2 mem2 md2 k1,
  ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
  In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos ->
  In (vr_lb e q) (ablocks B lyc Sc) -> In (vr_lb e q) (ablocks B ly2 S2) ->
  In (vr_cb e c) (ablocks B lyc Sc) -> In (vr_cb e c) (ablocks B ly2 S2) ->
  alloc_ceiling <= vr_s1 e -> vr_sp0 e <= 2 ^ 64 ->
  (forall a, inFP FP1 a -> vk_wrange e F q c a -> False) ->
  vk_wkeep e F q c (rdW Wc memc) (rdW W2 mem2).
Proof.
intros e pos F q c lyc Sc Wc memc mdc STK1 FP1 ly2 S2 W2 mem2 md2 k1 HJ Hfr EF Hl1 Hl2 Hc1 Hc2 Hs1 Hsp HD a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _ & G4 & _).
assert (HnF : ~ inFP FP1 a) by (intros Hf; exact (HD a Hf Ha)).
pose proof (vk_s1_bounds e) as Hb.
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

(* the walk's memory lies apart from the recorder's statics and blocks *)
Lemma vk_rec_fp_apart : forall e pos F q c lyc Sc Wc memc mdc Oc tmps,
  AR SEGS B lyc Sc Wc memc mdc -> In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos ->
  Permutation (ablocks B lyc Sc) (Oc ++ tmps ++ e_rest e) -> In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
  alloc_ceiling <= vr_s1 e ->
  forall a, inFP (vk_rec_fp Oc) a -> vk_wrange e F q c a -> False.
Proof.
intros e pos F q c lyc Sc Wc memc mdc Oc tmps HAR Hfr EF HP Hl Hc Hs1 a Ha Hw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vk_s1_bounds e) as Hb.
assert (Hnd : List.NoDup (Oc ++ tmps ++ e_rest e)) by exact (Permutation_NoDup HP (verbs_receive_live.vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR)).
assert (Hinb : forall pn, In pn (Oc ++ tmps ++ e_rest e) -> In pn (ablocks B lyc Sc)) by (intros pn Hpn; exact (Permutation_in _ (Permutation_sym HP) Hpn)).
assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc)) by (apply Hinb; apply in_or_app; right; apply in_or_app; left; exact Hl).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)) by (apply Hinb; apply in_or_app; right; apply in_or_app; left; exact Hc).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hfr) as (Hf0 & Hfc & Hfapp).
assert (E4 : fs_frame_bytes 4 = 1024) by reflexivity. rewrite E4 in Hfc. rewrite <- EF in Hf0, Hfc.
pose proof (shadow_addr_bounds F ltac:(lia)) as Hsh.
destruct (vk_rec_fp_inv Oc a Ha) as [Hpg | (p & n & Hpn & Hr)].
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
    { intros E. apply (vk_nodup_app_dis _ _ (p, n) Hnd Hpn). rewrite E. apply in_or_app. left. exact Hl. }
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ p n _ _ HAR Hpb Hlb Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
  + assert (Hne : (p, n) <> vr_cb e c).
    { intros E. apply (vk_nodup_app_dis _ _ (p, n) Hnd Hpn). rewrite E. apply in_or_app. left. exact Hc. }
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ p n _ _ HAR Hpb Hcb Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* bytes the callee leaves: those of the image it does not hold *)
Lemma vk_img_kept : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 a,
  ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
  inFP cmd_PG a -> ~ inFP FP1 a -> ~ YI16.sink_open_fp FP1 ->
  rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 a HJ Hpg HnF Hso.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _).
destruct (PROGU a Hpg) as (Himg & Ho & He). exact (G3 a Himg Ho He (fp_spares_closed FP1 a Hso HnF)).
Qed.

Lemma vk_gq_kept : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 v,
  ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
  (forall a, inFP FP1 a -> ~ (A_G_QUITTING <= a < A_G_QUITTING + 4)) -> ~ YI16.sink_open_fp FP1 ->
  aval_mem (rdW Wc memc) A_G_QUITTING 4 v -> aval_mem (rdW W2 mem2) A_G_QUITTING 4 v.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 v HJ HF Hso Hv.
apply (aval_mem_agree _ _ _ 4 _ Hv). intros k Hk. change (Z.of_nat 4) with 4 in Hk.
apply (vk_img_kept STK1 sp1 FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1); [exact HJ | | | exact Hso].
- unfold cmd_PG. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. left. unfold A_G_QUITTING. lia.
- intros Hf. exact (HF _ Hf ltac:(lia)).
Qed.

(* ===============================================================================================================
   A boundary state across a program call, and the call rules at a boundary state *)
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
  rewrite (HP r Hcs). apply (vr_rv_get regs _ r v Hrv). apply in_or_app. left. exact Hin.
- apply Forall_forall. intros [r v] Hin. cbn [fst snd].
  destruct (Hrl r v Hin) as [[-> ->] | [Hcs Hin']]; [exact H10|].
  rewrite (HP r Hcs). apply (vr_rv_get regs _ r v Hrv). apply in_or_app. right. exact Hin'.
Qed.

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
  rewrite (HP r Hcs). apply (vr_rv_get regs _ r v Hrv). apply in_or_app. left. exact Hin.
- apply Forall_forall. intros [r v] Hin. cbn [fst snd]. destruct (Hrl r v Hin) as [Hcs Hin'].
  rewrite (HP r Hcs). apply (vr_rv_get regs _ r v Hrv). apply in_or_app. right. exact Hin'.
Qed.

Lemma vk_k1_le : forall R D, vr_k1 R D <= ev_vr R D.
Proof. intros R D. pose proof (vr_k1_ev R D). lia. Qed.

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

Lemma vk_gq_pg : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> inFP cmd_PG a.
Proof. intros a Ha. unfold cmd_PG; apply inFP_cons; right; apply inFP_cons; right; apply inFP_cons; left; exact Ha. Qed.

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
  (forall a, inFP FP1 a -> vk_wrange e F q c a -> False) -> ~ YI16.sink_open_fp FP1 ->
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
pose proof (vk_s1_bounds e) as Hs1b.
assert (Hs1c : alloc_ceiling <= vr_s1 e) by lia.
assert (Hsp64 : vr_sp0 e <= 2 ^ 64) by lia.
assert (Hfr4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof Hfr as (EF & _ & _).
assert (Hinb : forall pn, In pn tmps -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right; apply in_or_app; left; exact Hpn. }
assert (HK : vk_wkeep e F q c (rdW Wc memc) (rdW W2 mem2))
  by exact (vk_wkeep_call e pos F q c lyc Sc Wc memc mdc STK1 FP1 ly2 S2 W2 mem2 md2 EV1 HJ1 Hfr4 EF
    (Hinb _ Hl) Hl2 (Hinb _ Hc) Hc2 Hs1c Hsp64 HFP).
assert (EF2 : ly_F ly2 = ly_F lyc) by (destruct Hly2 as (_ & _ & _ & _ & _ & EFx & _); exact EFx).
split; [|split].
- split; [exact HJ'|]. split; [exact Hk'|]. split; [exact Hm'|]. split; [exact Hnm'|].
  split; [exact (vk_frame_keep e q c lyc ly2 Wc memc W2 mem2 pos F vr_sh2 EF2 HK Hfr)|].
  split; [exact Hrv'|].
  split; [exact (vk_saved_keep e F q c Wc memc W2 mem2 HK Hsv)|].
  split; [exact (vk_spill_keep e F q c Wc memc W2 mem2 (vr_sl3 F q c) HK (vk_sl3_ok F q c) Hsp)|].
  split; [exact (vr_env_of_aro B MT RRO RPG RECC PROGU ROA ly2 S2 W2 mem2 md2 HAR2
    (vk_aro_kept STK1 (vr_s1 e) FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 EV1 HJ1 HFro Hso (proj1 Henv)))|].
  split; [exact Hrec'|]. split; [exact Hd'|]. split; [exact Hperm'|].
  exact (vk_gq_kept STK1 (vr_s1 e) FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 EV1 qv HJ1 HFgq Hso Hq).
- exact (vk_line_keep e F q c Wc memc W2 mem2 HDn HK HL).
- exact (vk_copy_keep e F q c tp Wc memc W2 mem2 HK HCP).
Qed.

(* the call rule at a boundary state for a callee whose post is apost_base: the frame chain (the kit's vr_chain_at,
   pass 5) and cl_callS_wide; the callee's footprint lies below the allocator's ceiling, so no byte of this
   function's window *)
Lemma vk_step : forall e pos F tmps sl rl Rc Oc qv k kmax nm nmax lyc Sc (W : world SEGS) regsc memc mdc
  AF STK1 FP1 EV1 retk (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (Q : world SEGS -> config -> Prop),
  vr_ent B MT e ->
  vr_core B MT e pos F tmps vr_sh2 sl rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc ->
  getr regsc 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK ->
  (forall a, inFP FP1 a -> awr_byte SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (ablocks B (e_ly e) (e_S e))
     (ablocks B lyc Sc) (frames (e_S e)) lyc [(4, pos)] a) ->
  (forall a, inFP FP1 a -> a < alloc_ceiling) ->
  (forall ch, afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch ->
     SRr SEGS W (cfg_at SEGS (BASE + AF) regsc memc mdc) (apost_base SEGS B STK1 FP1 regsc lyc Sc W memc mdc EV1 K)) ->
  (forall ly2 S2 W2 regs2 mem2 md2,
     ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
       [(4, pos)] ly2 S2 W2 mem2 md2 (k + EV1) ->
     ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 ->
     aregs_preserved regsc regs2 -> K ly2 S2 W2 regs2 mem2 md2 ->
     SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros e pos F tmps sl rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc AF STK1 FP1 EV1 retk K Q
  He HC R1 Hretk Hretk2 HST0 HSTK1 HAW HLOW CALL CONT.
destruct HC as (HJ & _ & _ & _ & _ & Hrv & Hsv & _).
pose proof He as (HPRE0 & _).
pose proof HPRE0 as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vk_s1_bounds e) as Hs1b. pose proof (vk_s1_ge e Hal16) as [Hs1g Ho16].
assert (R2 : getr regsc 2 = w64 (vr_s1 e)) by (apply (vr_rv_get regsc _ 2 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R3 : getr regsc 3 = w64 (as_gp B)) by (apply (vr_rv_get regsc _ 3 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R4 : getr regsc 4 = w64 (as_tp B)) by (apply (vr_rv_get regsc _ 4 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R8 : getr regsc 8 = w64 (vr_sp0 e)) by (apply (vr_rv_get regsc _ 8 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (Hsp1 : spZ regsc = vr_s1 e) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
destruct (vr_chain_at B MT RRO RPG RECC PROGU ROA e lyc Sc W memc mdc k pos regsc He HJ Hsv R8) as (ch1 & Hch1).
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
  - replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) by lia. exact Hch1.
  - intros HPRE1. pose proof (CALL ch1 HPRE1) as HC1.
    unfold cfg_at, w64 in HC1. eapply SRr_mono; [exact HC1|].
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. rewrite R1. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - exact HAW.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (HLOW a Ha). lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & HK).
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
exact (CONT ly2 S2 W2 regs2 mem2 md2 HJ2 HJc HP HK).
Qed.

(* vk_step for a callee whose post is apost_baseF: the continuation runs at the FP state fx' the callee returns at,
   related to this one by fxrel (PaFx.v cl_callS_wideF) *)
Lemma vk_stepF : forall e pos F tmps sl rl Rc Oc qv k kmax nm nmax lyc Sc (W : world SEGS) regsc memc mdc
  AF STK1 FP1 EV1 retk (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (Q : world SEGS -> config -> Prop),
  vr_ent B MT e ->
  vr_core B MT e pos F tmps vr_sh2 sl rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc ->
  getr regsc 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK ->
  (forall a, inFP FP1 a -> awr_byte SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (ablocks B (e_ly e) (e_S e))
     (ablocks B lyc Sc) (frames (e_S e)) lyc [(4, pos)] a) ->
  (forall a, inFP FP1 a -> a < alloc_ceiling) ->
  (forall ch, afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch ->
     SRr SEGS W (cfg_at SEGS (BASE + AF) regsc memc mdc) (apost_baseF SEGS B STK1 FP1 regsc lyc Sc W memc mdc EV1 K)) ->
  (forall (fx' : YK11.FPState) ly2 S2 W2 regs2 mem2 md2, fxrel fx fx' ->
     ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
       [(4, pos)] ly2 S2 W2 mem2 md2 (k + EV1) ->
     ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 ->
     aregs_preserved regsc regs2 -> K ly2 S2 W2 regs2 mem2 md2 ->
     SRr SEGS W2 (mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros e pos F tmps sl rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc AF STK1 FP1 EV1 retk K Q
  He HC R1 Hretk Hretk2 HST0 HSTK1 HAW HLOW CALL CONT.
destruct HC as (HJ & _ & _ & _ & _ & Hrv & Hsv & _).
pose proof He as (HPRE0 & _).
pose proof HPRE0 as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vk_s1_bounds e) as Hs1b. pose proof (vk_s1_ge e Hal16) as [Hs1g Ho16].
assert (R2 : getr regsc 2 = w64 (vr_s1 e)) by (apply (vr_rv_get regsc _ 2 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R3 : getr regsc 3 = w64 (as_gp B)) by (apply (vr_rv_get regsc _ 3 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R4 : getr regsc 4 = w64 (as_tp B)) by (apply (vr_rv_get regsc _ 4 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R8 : getr regsc 8 = w64 (vr_sp0 e)) by (apply (vr_rv_get regsc _ 8 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (Hsp1 : spZ regsc = vr_s1 e) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
destruct (vr_chain_at B MT RRO RPG RECC PROGU ROA e lyc Sc W memc mdc k pos regsc He HJ Hsv R8) as (ch1 & Hch1).
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
  - replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) by lia. exact Hch1.
  - intros HPRE1. pose proof (CALL ch1 HPRE1) as HC1.
    unfold cfg_at, w64 in HC1. eapply SRr_mono; [exact HC1|].
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HR' & HC' & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. rewrite R1. split; [reflexivity|]. split; [exact HR'|]. split; [exact HC'|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - exact HAW.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (HLOW a Ha). lia. }
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

Lemma vk_bsum2 : forall e q c, vr_ent B MT e -> bsum [vr_lb e q; vr_cb e c] <= 16386.
Proof.
intros e q c He. pose proof He as (_ & _ & _ & _ & _ & _ & _ & Hn8 & HDn & _).
pose proof (vk_line_le e HDn) as Hll.
pose proof (vrm_l_le (e_n e) (e_D e) ltac:(lia)) as Hl.
unfold vr_l in *. unfold bsum, vr_lb, vr_cb, vr_l. cbn [fold_right snd]. lia.
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
{ intros H. exact (vk_nodup_app_dis _ _ _ HndOT H (in_or_app _ _ _ (or_introl Hc))). }
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

Lemma vk_frm0 : forall e, vr_ent B MT e -> frm0 fx.
Proof.
intros e He. unfold vr_ent in He. cbv zeta in He.
repeat lazymatch type of He with _ /\ _ => destruct He as [_ He] end. exact He.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Recorder callees: their footprint is g_rec, record.spill and the recorder's blocks (vk_rec_fp) *)
Lemma vk_rec_low : forall lyc Sc (Wc : world SEGS) memc mdc Oc, AR SEGS B lyc Sc Wc memc mdc ->
  (forall pn, In pn Oc -> In pn (ablocks B lyc Sc)) ->
  forall a, inFP (vk_rec_fp Oc) a -> a < alloc_ceiling.
Proof.
intros lyc Sc Wc memc mdc Oc HAR HO a Ha. pose proof asan_consts as (C1 & _).
unfold vk_rec_fp in Ha.
apply inFP_cons in Ha as [G|Ha]; [unfold A_G_REC, REC_SIZE in *; lia|].
apply inFP_cons in Ha as [G|Ha]; [unfold A_REC_SPILL, SC_SIZE in *; lia|].
destruct (inFP_ablocks_fp_inv Oc a Ha) as (p & n & Hpn & Hr).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & _ & Hc & _). lia.
Qed.

Lemma vk_rec_gq : forall lyc Sc (Wc : world SEGS) memc mdc Oc, AR SEGS B lyc Sc Wc memc mdc ->
  (forall pn, In pn Oc -> In pn (ablocks B lyc Sc)) ->
  forall a, inFP (vk_rec_fp Oc) a -> ~ (A_G_QUITTING <= a < A_G_QUITTING + 4).
Proof.
intros lyc Sc Wc memc mdc Oc HAR HO a Ha Hg. unfold vk_rec_fp in Ha.
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
  forall a, inFP (vk_rec_fp Oc) a -> awr_byte SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e)
    (ablocks B (e_ly e) (e_S e)) (ablocks B lyc Sc) (frames (e_S e)) lyc [(4, pos)] a.
Proof.
intros e pos lyc Sc Wc memc mdc Oc tmps He HAR Hperm a Ha.
pose proof He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _).
assert (Hnd : List.NoDup (Oc ++ tmps ++ e_rest e))
  by exact (Permutation_NoDup Hperm (verbs_receive_live.vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR)).
assert (HO : forall pn, In pn Oc -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hpn).
unfold vk_rec_fp in Ha. apply inFP_cons in Ha as [G|Ha].
- right; right; right; right; left. split; [exists (A_G_REC, A_G_REC + REC_SIZE); split;
    [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; left; reflexivity | exact G]|].
  assert (Hpg : inFP cmd_PG a) by (unfold cmd_PG; apply inFP_cons; left; unfold REC_SIZE in G; exact G).
  split; [|exact (proj1 (PROGU a Hpg))].
  rewrite (YF0m.ts_prog _ HB). unfold YF0m.TFIB_PROG_STATIC. apply Exists_cons_hd.
  unfold in_zr, A_G_REC, REC_SIZE in *. cbn [fst snd]. lia.
- apply inFP_cons in Ha as [G|Ha].
  + right; right; right; right; left. split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split;
      [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; right; left; reflexivity | exact G]|].
    assert (Hpg : inFP cmd_PG a)
      by (unfold cmd_PG; apply inFP_cons; right; apply inFP_cons; left; unfold SC_SIZE in G; exact G).
    split; [|exact (proj1 (PROGU a Hpg))].
    rewrite (YF0m.ts_prog _ HB). unfold YF0m.TFIB_PROG_STATIC. apply Exists_cons_tl. apply Exists_cons_hd.
    unfold in_zr, A_REC_SPILL, SC_SIZE in *. cbn [fst snd]. lia.
  + destruct (inFP_ablocks_fp_inv Oc a Ha) as (p & n & Hpn & Hr).
    destruct (in_dec vk_pz_eq_dec (p, n) (e_O e)) as [HinO | HnO].
    * right; left. split; [exists (p, p + req_size n); split; [unfold vr_fp; apply in_or_app; right; unfold ablocks_fp;
        exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (p, n) HinO) | cbn; lia]|].
      exists p, n. split; [exact (HO _ Hpn) | exact Hr].
    * right; right; left. exists p, n. split; [exact (HO _ Hpn)|]. split; [|exact Hr].
      intros Hin0. apply (Permutation_in _ Hperm0) in Hin0. apply in_app_or in Hin0 as [H|H]; [exact (HnO H)|].
      apply (vk_nodup_app_dis _ _ (p, n) Hnd Hpn). apply in_or_app; right; exact H.
Qed.

Lemma vk_rec_mem : forall ly S rd R O O', rec_repA B ly S rd R O -> (forall pn, In pn O' <-> In pn O) ->
  rec_repA B ly S rd R O'.
Proof. intros ly S rd R O O' (Q & HA & HOQ) HE. exists Q. split; [exact HA|]. intros pn. rewrite HE. apply HOQ. Qed.

Lemma vk_code_range : forall ly S rd R O, rec_repA B ly S rd R O -> -2^31 <= r_code R < 2^31.
Proof. intros ly S rd R O (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HC & _) & _) & _). exact HC. Qed.

(* a boundary state across a recorder callee: the recorder's blocks become filter (vk_inb O1) of the live blocks,
   the callee's new blocks (its text, if any) join the walk's *)
Lemma vk_rec_core : forall e pos F q c tp tmps rl rl' Rc Rc' Oc O1 new qv k k' kmax kmax' nm nm' nmax nmax'
  lyc Sc Wc regsc memc mdc ly2 S2 W2 regs2 mem2 md2 STK1 EV1,
  vr_ent B MT e ->
  vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
  vr_line B e q Wc memc -> vr_copy B e F c tp Wc memc ->
  In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(4, pos)] ly2 S2 W2 mem2 md2 k' ->
  ajournal SEGS B STK1 (vr_s1 e) (vk_rec_fp Oc) lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 EV1 ->
  rec_repA B ly2 S2 (rdW W2 mem2) Rc' O1 ->
  (forall pn, In pn O1 -> In pn Oc \/ ~ In pn (ablocks B lyc Sc)) ->
  (forall pn, In pn (ablocks B lyc Sc) -> ~ In pn Oc -> In pn (ablocks B ly2 S2)) ->
  (forall pn, In pn (ablocks B ly2 S2) -> (In pn (ablocks B lyc Sc) /\ ~ In pn Oc) \/ In pn O1 \/ In pn new) ->
  (forall pn, In pn new -> In pn (ablocks B ly2 S2)) -> List.NoDup new ->
  (forall pn, In pn new -> (In pn (ablocks B lyc Sc) -> In pn Oc) /\ ~ In pn O1) ->
  k' <= kmax' -> vr_meter MT e S2 k' nm' -> nm' <= nmax' ->
  vr_rv regs2 (vr_base B e ++ rl') ->
  vr_core B MT e pos F (new ++ tmps) vr_sh2 (vr_sl3 F q c) rl' Rc' (List.filter (vk_inb O1) (ablocks B ly2 S2)) qv
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
pose proof (vk_s1_bounds e) as Hs1b.
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
  intros HinO. exact (vk_nodup_app_dis _ _ _ Hnd HinO Hpn). }
assert (Hl2 : In (vr_lb e q) (ablocks B ly2 S2))
  by (destruct (Hinb (vr_lb e q) ltac:(apply in_or_app; left; exact Hl)) as [H1 H2]; exact (Hsurv _ H1 H2)).
assert (Hc2 : In (vr_cb e c) (ablocks B ly2 S2))
  by (destruct (Hinb (vr_cb e c) ltac:(apply in_or_app; left; exact Hc)) as [H1 H2]; exact (Hsurv _ H1 H2)).
assert (HinR : In (e_data e, Z.max (e_n e) 1) (e_rest e)).
{ pose proof (Permutation_in _ Hperm0 HinD) as H0. apply in_app_or in H0 as [H0|H0]; [contradiction | exact H0]. }
apply (vk_call_core e pos F q c tp tmps (new ++ tmps) rl rl' Rc Rc' Oc (List.filter (vk_inb O1) (ablocks B ly2 S2)) qv
  k k' kmax kmax' nm nm' nmax nmax' lyc Sc Wc regsc memc mdc ly2 S2 W2 regs2 mem2 md2 STK1 (vk_rec_fp Oc) EV1
  HDn HC HL HCP Hl Hc HJ' HJ1).
- exact (vk_rec_fp_apart e pos F q c lyc Sc Wc memc mdc Oc tmps HAR Hfr4 EF Hperm Hl Hc Hs1c).
- exact (vk_rec_fp_closed lyc Sc Wc memc mdc Oc HAR HO).
- exact (vk_rec_fp_not_ro lyc Sc Wc memc mdc Oc HAR HO).
- exact (vk_rec_gq lyc Sc Wc memc mdc Oc HAR HO).
- exact Hl2.
- exact Hc2.
- exact Hk'.
- exact Hm'.
- exact Hnm'.
- exact Hrv'.
- apply (vk_rec_mem _ _ _ _ O1 _ Hrec'). intros pn. rewrite vk_in_filter_inb.
  split; [intros [_ H]; exact H | intros H; split; [exact (HO1s _ H) | exact H]].
- intros Hin. apply vk_in_filter_inb in Hin as [_ Hin]. destruct (Ha1 _ Hin) as [H|H]; [exact (Hd H)|].
  apply H. exact (proj1 (Hinb _ (in_or_app _ _ _ (or_intror HinR)))).
- exact (vk_perm_after (ablocks B lyc Sc) (ablocks B ly2 S2) Oc O1 tmps (e_rest e) new
    (verbs_receive_live.vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR)
    (verbs_receive_live.vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR2) Hperm Hsurv Hall Ha1 Hnew Hndn Hnnew).
Qed.

(* pins_clear(u) at a boundary state (B: record, arg_s, answer_code; post apost_baseF). The continuation runs at the
   FP state pins_clear returns at. *)
Lemma vk_pins_clear : @tpins_clear_spec fx rc SK PI B MT ->
  forall e pos F q c tp tmps rl Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc (W : world SEGS)
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
intros TPINS_CLEAR e pos F q c tp tmps rl Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc W regsc memc mdc pu u retk rlf Q
  He HC HL HCP Hl Hc R1 Hrk1 Hrk2 R10 Hpu Hblk Hap Hstr Hlen Hsf Hkev Hkmax Hnm32 Hnmax Hlv Hrlf CONT.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hd & Hperm & Hq).
pose proof (proj1 HJ) as HAR.
assert (HPS : PINS_CLEAR_STK + 208 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HPS0 : 0 <= PINS_CLEAR_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (vk_code_range lyc Sc _ Rc Oc Hrec) as Hcode.
assert (Hrcr : - 2 ^ 31 <= snd (pins_clear_m Rc (Some u)) < 2 ^ 31)
  by (destruct (vk_code_pins_clear Rc (Some u)) as [-> | ->]; lia).
pose proof (resp_length _ Hrcr) as Hrl.
pose proof (mo_malloc_nonneg MT MTL VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as Hmm.
pose proof (mo_free_nonneg MT MTL) as Hmf.
assert (HXM : XM_PINS_CLEAR MT Rc (Some u) <= 3 * mo_malloc MT VERBS_RECEIVE_REQ + 2 * mo_free MT).
{ unfold XM_PINS_CLEAR, XM_RECORD, XM_ARG_S, XM_ANSWER_CODE, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC.
  rewrite Hsf. cbn [sarg].
  pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length u) + 1) 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ, LMAX in *; lia)).
  pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length (resp (snd (pins_clear_m Rc (Some u))))) + 1) 1)
    VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)).
  lia. }
assert (HEV : EV_PINS_CLEAR Rc = 5)
  by (unfold EV_PINS_CLEAR, EV_RECORD, EV_ARG_S, EV_ANSWER_CODE, EV_HAND_BACK, EV_XMALLOC; rewrite Hsf; reflexivity).
assert (HO : forall pn, In pn Oc -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
eapply (vk_stepF e pos F tmps (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc AF_pins_clear
  PINS_CLEAR_STK (vk_rec_fp Oc) (EV_PINS_CLEAR Rc) retk _ Q He HC R1 Hrk1 Hrk2 HPS0 HPS).
- exact (vk_rec_awr e pos lyc Sc W memc mdc Oc tmps He HAR Hperm).
- exact (vk_rec_low lyc Sc W memc mdc Oc HAR HO).
- intros ch HPRE.
  exact (TPINS_CLEAR lyc Sc W regsc memc mdc ch pu u Rc Oc HPRE (vk_frm0 e He) (proj1 Henv) (proj1 (proj2 (proj2 Henv)))
    R10 Hpu Hblk Hap Hstr Hlen Hrec
    ltac:(pose proof (vk_frames e pos lyc Sc W memc mdc k He HJ); lia)
    (vk_nev e pos lyc Sc W memc mdc k (EV_PINS_CLEAR Rc) He HJ Hkev)
    (vk_live e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc
      (LIVE_PINS_CLEAR Rc (Some u)) He HC Hlv)
    (vri_meter_ok B MT e Sc k nm (XM_PINS_CLEAR MT Rc (Some u)) 3 2 (EV_PINS_CLEAR Rc) MTL He Hmet HXM
      ltac:(rewrite HEV; lia) ltac:(rewrite HEV; lia) Hkev)).
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

(* lv2_refusals_forget(NULL) at a boundary state (B: record, arg_s of the default "*", mix_call; post apost_base,
   so the FP state is kept) *)
Lemma vk_lv2 : @tlv2_refusals_forget_spec fx rc SK PI B MT ->
  forall e pos F q c tp tmps rl rl' Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc (W : world SEGS)
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
intros TLV2 e pos F q c tp tmps rl rl' Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc W regsc memc mdc retk Q
  He HC HL HCP Hl Hc R1 Hrk1 Hrk2 R10 Hkev Hkmax Hnm32 Hnmax Hlv Hrl CONT.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hd & Hperm & Hq).
pose proof (proj1 HJ) as HAR.
assert (HLS : LV2_REFUSALS_FORGET_STK + 208 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HLS0 : 0 <= LV2_REFUSALS_FORGET_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (mo_malloc_nonneg MT MTL VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as Hmm.
pose proof (mo_free_nonneg MT MTL) as Hmf.
pose proof (vk_rsf_nonneg Rc) as Hsf0.
assert (HXM : XM_LV2_REFUSALS_FORGET MT Rc None <= 1 * mo_malloc MT VERBS_RECEIVE_REQ + rec_spill_frees Rc * mo_free MT).
{ unfold XM_LV2_REFUSALS_FORGET, XM_RECORD, XM_ARG_S, XM_XMALLOC, LIVE_XMALLOC. cbn [darg sarg].
  lazymatch goal with |- context [mo_malloc MT ?x] =>
    pose proof (mo_malloc_mono MT MTL x VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; cbn; lia)) end.
  lia. }
assert (HEV : EV_LV2_REFUSALS_FORGET Rc = rec_spill_frees Rc + 1)
  by (unfold EV_LV2_REFUSALS_FORGET, EV_RECORD, EV_ARG_S, EV_XMALLOC; reflexivity).
assert (HLV : LIVE_LV2_REFUSALS_FORGET None <= 2)
  by (unfold LIVE_LV2_REFUSALS_FORGET, LIVE_ARG_S, LIVE_XMALLOC; cbn; lia).
assert (HO : forall pn, In pn Oc -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
eapply (vk_step e pos F tmps (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc AF_lv2_refusals_forget
  LV2_REFUSALS_FORGET_STK (vk_rec_fp Oc) (EV_LV2_REFUSALS_FORGET Rc) retk _ Q He HC R1 Hrk1 Hrk2 HLS0 HLS).
- exact (vk_rec_awr e pos lyc Sc W memc mdc Oc tmps He HAR Hperm).
- exact (vk_rec_low lyc Sc W memc mdc Oc HAR HO).
- intros ch HPRE.
  exact (TLV2 lyc Sc W regsc memc mdc ch 0 None Rc Oc HPRE (proj1 Henv)
    (proj1 (proj2 (proj2 Henv))) R10 ltac:(lia) eq_refl (fun x Hx => ltac:(discriminate Hx)) Hrec
    (vk_nev e pos lyc Sc W memc mdc k (EV_LV2_REFUSALS_FORGET Rc) He HJ Hkev)
    (vk_live e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc
      (LIVE_LV2_REFUSALS_FORGET None) He HC ltac:(lia))
    (vri_meter_ok B MT e Sc k nm (XM_LV2_REFUSALS_FORGET MT Rc None) 1 (rec_spill_frees Rc) (EV_LV2_REFUSALS_FORGET Rc)
      MTL He Hmet HXM ltac:(rewrite HEV; lia) ltac:(rewrite HEV; lia) Hkev)).
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

End e.
End f.
End d.
