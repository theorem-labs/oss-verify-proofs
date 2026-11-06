(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S07 (route add, B 0x8d2e8) of the walk of verbs_receive on the
   ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v, vr_s07_stmt): the walk's kit: the
   meter across a callee (meter_step, xm_*_le, over B's record / arg_s accounts), a word of the copy as a callee or
   runtime argument (tok_apart, tok_argA, tok_rt), the symbolic state at a point of the walk (seed_core, seed_core_e)
   and the exit at the join JB 0x8d4d0 (exit_hd_d0). The B twin of lib/A/Prog/verbs_receive_s07b.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route VerbsFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
descriptors_add_c sup_add_c sup_reply_code_c sup_resp_c answer_c hand_back_c record_c arg_s_c xmalloc_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s07a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a run whose regions write nothing leaves the reader of the memory as it was *)
Lemma ro_frame_view : forall E rs H m m', frame_of E rs (mrestrict H m) (mrestrict H m') ->
Forall (fun r => r_whi r <= r_wlo r) rs -> forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hf Hro a Ha. apply aview_eq_of. apply Hf. intros (r & Hr & Hw).
rewrite Forall_forall in Hro. pose proof (Hro r Hr). rewrite Z_to_bv_unsigned in Hw.
unfold bv_wrap, bv_modulus in Hw. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hw. rewrite Z.mod_small in Hw by lia. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis MTL : ameter_laws MT.
Hypothesis BLKT : vr_blktail B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the meter across a callee step (the interface's vri_meter_step): am mallocs of at most VERBS_RECEIVE_REQ bytes and
   af frees, each at most the events EV the step adds *)
Lemma meter_step : forall e Sc S' k nm am af X EV,
vr_meter MT e Sc k nm -> mo_le MT Sc S' X ->
X <= am * mo_malloc MT VERBS_RECEIVE_REQ + af * mo_free MT ->
0 <= am <= EV -> 0 <= af <= EV ->
vr_meter MT e S' (k + EV) (nm + am).
Proof.
intros e Sc S' k nm am af X EV H1 H2 H3 H4 H5.
eapply vri_meter_step; [exact MTL | exact H1 | exact H2 | exact H3 | exact H4 | exact H5].
Qed.
Lemma mm_le : forall (w : list byte), Z.of_nat (length w) <= LMAX -> mo_malloc MT (Z.of_nat (length w) + 1) <= mo_malloc MT VERBS_RECEIVE_REQ.
Proof. intros w H. apply (mo_malloc_mono MT MTL). unfold LMAX, VERBS_RECEIVE_REQ in *. lia. Qed.
Lemma mf_nn : 0 <= mo_free MT. Proof. exact (mo_free_nonneg MT MTL). Qed.
(* arg_s's copy of a string of at most LMAX bytes: one malloc of at most VERBS_RECEIVE_REQ bytes *)
Lemma xm_arg_le : forall (v : option (list byte)), Z.of_nat (length (sarg v)) <= LMAX ->
XM_ARG_S MT v <= mo_malloc MT VERBS_RECEIVE_REQ.
Proof.
intros v H. unfold XM_ARG_S, XM_XMALLOC, LIVE_XMALLOC. rewrite Z.max_l by lia. exact (mm_le (sarg v) H).
Qed.

Lemma xm_add_le : forall R uri id pl cl t,
Z.of_nat (length (sarg uri)) <= LMAX -> -2^31 <= id < 2^31 ->
Z.of_nat (length (darg pl (bstr "-"%string))) <= LMAX -> Z.of_nat (length (darg cl (bstr "-"%string))) <= LMAX ->
Z.of_nat (length t) <= LMAX ->
XM_SUP_ADD MT R uri id pl cl t <= 6 * mo_malloc MT VERBS_RECEIVE_REQ + rec_spill_frees R * mo_free MT + mo_free MT.
Proof.
intros R uri id pl cl t Hu Hi Hp Hc Ht.
unfold XM_SUP_ADD, XM_RECORD, XM_ANSWER. rewrite Z.max_id.
pose proof (xm_arg_le uri Hu). pose proof (dec_length id Hi) as Hdl.
pose proof (xm_arg_le (Some (dec id)) ltac:(cbn [sarg]; unfold LMAX; lia)).
pose proof (xm_arg_le (Some (darg pl (bstr "-"%string))) ltac:(cbn [sarg]; exact Hp)).
pose proof (xm_arg_le (Some (darg cl (bstr "-"%string))) ltac:(cbn [sarg]; exact Hc)).
unfold XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC. rewrite Z.max_l by lia. pose proof (mm_le t Ht).
pose proof mf_nn. lia.
Qed.
Lemma xm_desc_le : forall R uri,
Z.of_nat (length (sarg uri)) <= LMAX ->
XM_DESCRIPTORS_ADD MT R uri <= 1 * mo_malloc MT VERBS_RECEIVE_REQ + rec_spill_frees R * mo_free MT.
Proof.
intros R uri Hu. unfold XM_DESCRIPTORS_ADD, XM_RECORD. pose proof (xm_arg_le uri Hu). lia.
Qed.
Lemma xm_resp_le : forall code, -2^31 <= code < 2^31 ->
XM_SUP_RESP MT code <= 1 * mo_malloc MT VERBS_RECEIVE_REQ + 0 * mo_free MT.
Proof.
intros code Hc. unfold XM_SUP_RESP, XM_XMALLOC, LIVE_XMALLOC. pose proof (resp_length code Hc).
rewrite Z.max_l by lia. pose proof (mm_le (resp code) ltac:(unfold LMAX; lia)). lia.
Qed.

(* a token pointer's facts, from the copy block and the recorder *)
Lemma tok_apart : forall lyc Sc Wc memc mdc Rc Oc c nc p n,
AR SEGS B lyc Sc Wc memc mdc -> rec_repA B lyc Sc (rdW Wc memc) Rc Oc ->
In (c, nc) (ablocks B lyc Sc) -> ~ In (c, nc) Oc -> c <= p -> p + n <= c + nc ->
Forall (fun qk => iv_apart p n (fst qk) (snd qk)) Oc.
Proof.
intros lyc Sc Wc memc mdc Rc Oc c nc p n HAR Hrec Hcin Hcno Hp1 Hp2.
apply Forall_forall. intros [b m] Hqk. cbn [fst snd].
pose proof (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hqk) as Hbin.
assert (Hne : (c, nc) <> (b, m)) by (intros E; rewrite E in Hcno; exact (Hcno Hqk)).
pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc c nc b m HAR Hcin Hbin Hne) as Hdj.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
pose proof (req_size_pos nc ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ c nc HAR Hcin) as (_ & _ & _ & _ & _ & _ & H); lia)) as [_ Rc'].
pose proof (req_size_pos m ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hbin) as (_ & _ & _ & _ & _ & _ & H); lia)) as [_ Rm].
unfold iv_apart. lia.
Qed.

Lemma tok_argA : forall e F c tp lyc Sc Wc memc mdc Rc Oc tmps j p w,
AR SEGS B lyc Sc Wc memc mdc -> vr_copy B e F c tp Wc memc ->
rec_repA B lyc Sc (rdW Wc memc) Rc Oc -> In (vr_cb e c) tmps -> ~ In (vr_cb e c) Oc ->
Permutation (ablocks B lyc Sc) (Oc ++ tmps ++ e_rest e) ->
nth_error tp j = Some p -> nth_error (Verbs.toks (e_D e)) j = Some w ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) Oc p (Some w).
Proof.
intros e F c tp lyc Sc Wc memc mdc Rc Oc tmps j p w HAR Hcopy Hrec Hcbin Hcbno Hperm Hjp Hjw.
destruct Hcopy as [Hcf Hta]. destruct Hta as (Htk8 & Htkl & Htkp & Htkw).
destruct (Htkw j p w Hjp Hjw) as (Hstr & Hwl & Hc1 & Hc2).
assert (Hcbin' : In (vr_cb e c) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; apply in_or_app; left; exact Hcbin).
unfold astr_argA. cbn [vr_cb fst snd] in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcbin') as (_ & Hc4096 & _). cbn [fst snd] in Hc4096.
split; [lia|]. split; [exact Hstr|]. split; [unfold LMAX; lia|]. left. split.
- unfold in_blockA. exists c, (Z.of_nat (length (PV.line (e_D e))) + 1). split; [exact Hcbin' | split; [lia | lia]].
- apply (tok_apart lyc Sc Wc memc mdc Rc Oc c (Z.of_nat (length (PV.line (e_D e))) + 1) p (Z.of_nat (length w) + 1) HAR Hrec Hcbin' Hcbno); lia.
Qed.

(* a token's runtime-call facts (astr_at / aread_ok / atail_vis), from the copy block *)
Lemma tok_rt : forall e F c tp lyc Sc W memc mdc regs stk j p w,
AR SEGS B lyc Sc W memc mdc -> vr_copy B e F c tp W memc -> In (vr_cb e c) (ablocks B lyc Sc) ->
nth_error tp j = Some p -> nth_error (Verbs.toks (e_D e)) j = Some w ->
alloc_ceiling <= spZ regs - stk ->
astr_at SEGS W memc p w /\ aread_ok SEGS stk W regs memc p (astr_len w + 1) /\ atail_vis SEGS W memc (p + astr_len w).
Proof.
intros e F c tp lyc Sc W memc mdc regs stk j p w HAR Hcopy Hcbin Hjp Hjw Hsp.
destruct Hcopy as [Hcf Hta]. destruct Hta as (Htk8 & Htkl & Htkp & Htkw).
destruct (Htkw j p w Hjp Hjw) as (Hstr & Hwl & Hc1 & Hc2). destruct Hstr as [Hb Hn0].
cbn [vr_cb fst snd] in Hc1, Hc2, Hcbin. unfold astr_len.
split; [split; [apply (proj1 (abytes_atR_view SEGS W memc p _)); exact Hb | exact Hn0]|].
split.
- apply (aread_ok_of_block SEGS B LAWS stk lyc Sc W regs memc mdc c (Z.of_nat (length (PV.line (e_D e))) + 1) p (Z.of_nat (length w) + 1)
    HAR Hcbin ltac:(lia) ltac:(lia) ltac:(lia) Hsp).
- apply (BLKT lyc Sc W memc mdc c (Z.of_nat (length (PV.line (e_D e))) + 1) (p + Z.of_nat (length w)) HAR Hcbin). lia.
Qed.

(* the symbolic state at a point of S07, from the facts of a boundary-shaped state there (s3 = tok = F+32) *)
Lemma seed_core : forall e pos F q c tp tmps rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc pc tps,
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc ->
vr_copy B e F c tp W memc -> In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
getr regsc 19 = Z_to_bv 64 (F + 32) ->
(forall i p, nth_error tps i = Some p -> nth_error tp (S i) = Some p) -> (length tps <= 4)%nat ->
st_ok_pi SEGS VAL (E07 regsc (shadow_addr F + 4) F tps) (ss07 pc (length tps))
(restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros e pos F q c tp tmps rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc pc tps
Hcore Hcopy Hlb Hcb R19 Htps Hlen.
pose proof Hcore as (HJ & Hk & Hm & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hd & Hperm & Hq).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (vr_stk_ge) as [Hstk4 Hstk5]. unfold ESTACK, ASTACK in *.
destruct (vr_s1_bounds e Hal) as [Hs1 Hs1m].
destruct Hfr as (HF & Hflag & Hsh).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF0 & HF1 & _).
rewrite <- HF in HF0, HF1. change (fs_frame_bytes 4) with 1024 in HF1.
unfold vr_rv, vr_base in Hrv. apply Forall_app in Hrv as [Hrb _].
apply Forall_cons_iff in Hrb as [_ Hrb]. apply Forall_cons_iff in Hrb as [_ Hrb].
apply Forall_cons_iff in Hrb as [_ Hrb]. apply Forall_cons_iff in Hrb as [_ Hrb].
apply Forall_cons_iff in Hrb as [R9 _]. cbn [fst snd] in R9.
unfold vr_spill, vr_sl3 in Hsp.
apply Forall_cons_iff in Hsp as [S0 Hsp]. apply Forall_cons_iff in Hsp as [S8 Hsp].
apply Forall_cons_iff in Hsp as [S16 Hsp]. apply Forall_cons_iff in Hsp as [S24 Hsp].
apply Forall_cons_iff in Hsp as [S32 Hsp]. apply Forall_cons_iff in Hsp as [S40 Hsp].
apply Forall_cons_iff in Hsp as [S48 Hsp]. apply Forall_cons_iff in Hsp as [S56 Hsp].
apply Forall_cons_iff in Hsp as [S72 _].
cbn [fst snd] in S0, S8, S16, S24, S32, S40, S48, S56, S72.
assert (Hbl : forall b, In b tmps -> In b (ablocks B lyc Sc)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (Hbl _ Hlb)) as (_ & Hq4 & Hqc & _ & _ & _ & Hqn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (Hbl _ Hcb)) as (_ & Hc4 & Hcc & _ & _ & _ & Hcn).
cbn [fst snd] in Hq4, Hqc, Hqn, Hc4, Hcc, Hcn.
pose proof (req_size_pos _ (proj1 Hqn)) as [_ Hqr]. pose proof (req_size_pos _ (proj1 Hcn)) as [_ Hcr].
destruct Hcopy as [Hcf Hta]. pose proof Hta as (Htk8 & Htkl & Htkp & Htkw).
assert (Htp' : forall i p, nth_error tps i = Some p ->
  aval_mem (rdW W memc) (F + 40 + 8 * Z.of_nat i) 8 p /\ 0 <= p < 2 ^ 64).
{ intros i p Hi. pose proof (Htps i p Hi) as Hi'.
  pose proof (Htkp _ _ Hi') as Hv. replace (F + 32 + 8 * Z.of_nat (S i)) with (F + 40 + 8 * Z.of_nat i) in Hv by lia.
  split; [exact Hv|].
  assert (Hil : (S i < length (PV.toks (e_D e)))%nat) by (rewrite <- Htkl; apply nth_error_Some; rewrite Hi'; discriminate).
  destruct (nth_error (PV.toks (e_D e)) (S i)) as [w|] eqn:Ew; [|apply nth_error_None in Ew; lia].
  destruct (Htkw _ _ _ Hi' Ew) as (_ & _ & Hp1 & Hp2). lia. }
assert (HF8 : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
exact (seed07 W regsc memc pc (vr_s1 e) F tps R9 R19 ltac:(lia) ltac:(lia) HF0 HF1 S32 S40
  ltac:(unfold shadow_addr, SHADOW_OFF; lia) Htp' Hlen).
Qed.

(* the symbolic state at the route's entry (s3 is not tok yet): the spill region only *)
Lemma seed_core_e : forall e pos F q c tmps rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc pc,
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc ->
st_ok_pi SEGS VAL (E07 regsc (shadow_addr F + 4) F []) (ss07e pc)
(restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros e pos F q c tmps rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc pc Hcore.
pose proof Hcore as (HJ & Hk & Hm & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hd & Hperm & Hq).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (vr_stk_ge) as [Hstk4 Hstk5]. unfold ESTACK, ASTACK in *.
destruct (vr_s1_bounds e Hal) as [Hs1 Hs1m].
destruct Hfr as (HF & Hflag & Hsh).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF0 & HF1 & _).
rewrite <- HF in HF0, HF1. change (fs_frame_bytes 4) with 1024 in HF1.
unfold vr_rv, vr_base in Hrv. apply Forall_app in Hrv as [Hrb _].
apply Forall_cons_iff in Hrb as [_ Hrb]. apply Forall_cons_iff in Hrb as [_ Hrb].
apply Forall_cons_iff in Hrb as [_ Hrb]. apply Forall_cons_iff in Hrb as [_ Hrb].
apply Forall_cons_iff in Hrb as [R9 _]. cbn [fst snd] in R9.
unfold vr_spill, vr_sl3 in Hsp.
apply Forall_cons_iff in Hsp as [S0 Hsp]. apply Forall_cons_iff in Hsp as [S8 Hsp].
apply Forall_cons_iff in Hsp as [S16 Hsp]. apply Forall_cons_iff in Hsp as [S24 Hsp].
apply Forall_cons_iff in Hsp as [S32 Hsp]. apply Forall_cons_iff in Hsp as [S40 _].
cbn [fst snd] in S32, S40.
assert (HF8 : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
exact (seed07e W regsc memc pc (vr_s1 e) F R9 ltac:(lia) ltac:(lia) HF0 HF1 S32 S40
  ltac:(unfold shadow_addr, SHADOW_OFF; lia)).
Qed.

Lemma add_short : forall args, (length args <= 1)%nat -> PV.add_m atoi_a args = PV.reject.
Proof. intros [|a [|b r]] H; cbn [length] in H; [reflexivity | reflexivity | lia]. Qed.

(* the handler's exit at 0x8d4d0: package the transported state into vr_hd *)
Lemma exit_hd_d0 : forall e Wc tq O1 pos F q c tp lyc Sc regsc memc mdc k nm,
(2 <= length (Verbs.toks (e_D e)))%nat ->
4096 <= tq -> astr_atR (rdW Wc memc) tq (vr_x (e_R e) (e_D e)) ->
vr_core B MT e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c]
  vr_sh2 (vr_sl3 F q c) (vr_rl_hd e F q c 0x8d4d0 tq) (vr_R1 (e_R e) (e_D e)) O1 (vr_qv e)
  k (vr_k1 (e_R e) (e_D e)) nm VR_NM_HD lyc Sc Wc regsc memc mdc ->
vr_line B e q Wc memc -> vr_copy B e F c tp Wc memc ->
SRr SEGS Wc (cfg_at SEGS (vr_pc 0x8d4d0) regsc memc mdc) (vr_athd B MT 0x8d4d0 e).
Proof.
intros e Wc tq O1 pos F q c tp lyc Sc regsc memc mdc k nm Hnt Htq Hstr Hcore Hline Hcopy.
apply SRr_ret. unfold vr_athd, vr_hd.
exists tq, O1, pos, F, q, c, tp, lyc, Sc, regsc, memc, mdc, k, nm.
split; [reflexivity|]. split; [unfold vr_hd_ntok; cbn; exact Hnt|].
split; [exact Htq|]. split; [exact Hstr|]. split; [exact Hcore|]. split; [exact Hline | exact Hcopy].
Qed.

End e.
End f.
End d.
