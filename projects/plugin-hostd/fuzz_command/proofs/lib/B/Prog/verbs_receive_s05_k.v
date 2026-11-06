(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the call of sup_resp(code) from a dispatch state of the walk of verbs_receive on
   the ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v), shared by the segments S05
   (EMPTY, sup_resp(-902) at 0x8d2d0) and S24 (RQuit, sup_resp(0) at 0x8d2b4). The B twin of the call part of
   lib/A/Prog/verbs_receive_s05.v (a working branch), over B's sup_resp contract
   (lib/B/Prog/sup_resp_c.v: EV_SUP_RESP = EV_XMALLOC, XM_SUP_RESP / LIVE_SUP_RESP through xmalloc, SUP_RESP_STK =
   16512) and B's frame (s1 = sp0 - 192 or sp0 - 208). sup_resp's post is FP-existential, so the call goes through
   PaFx's cl_callSF and returns at some FP state fx' with fxrel fx fx'. The call keeps the frame, the spill slots of
   the caller (any list of slots below s1 + 80), the line, the copy and tok[], and g_quitting (its journal has an
   empty footprint). All names of this file carry the prefix vr05_. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route verbs_receive_pre.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c socket_send_c reply_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_after_reply_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_live verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s30_m verbs_receive_s30_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac vr05_inl := cbn; repeat first [left; reflexivity | right].

(* tok[] at a memory that agrees on tok's words and on the copy block (lib/B/Prog/verbs_receive_s29.v
   v29_atoks_atA_agree) *)
Lemma vr05_atoks_agree : forall (rd rd' : reader) tok ptrs tks cb ncb,
atoks_atA rd tok ptrs tks cb ncb ->
(forall k, 0 <= k < 8 * Z.of_nat (length ptrs) -> rd' (tok + k) = rd (tok + k)) ->
(forall k, 0 <= k < ncb -> rd' (cb + k) = rd (cb + k)) ->
atoks_atA rd' tok ptrs tks cb ncb.
Proof.
intros rd rd' tok ptrs tks cb ncb (Hal & Hlen & Hp & Ht) HT HC.
split; [exact Hal|]. split; [exact Hlen|].
split.
- intros i p Hi. assert (Hib : (i < length ptrs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  apply (aval_mem_agree rd rd' _ 8 _ (Hp i p Hi)). intros kk Hkk.
  replace (tok + 8 * Z.of_nat i + kk) with (tok + (8 * Z.of_nat i + kk)) by lia. apply HT. lia.
- intros i p w Hi Hw. destruct (Ht i p w Hi Hw) as (A1 & A2 & A3 & A4).
  split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
  apply (astr_atR_agree rd rd' p w (Z.of_nat (length w) + 1) A1); [lia|].
  intros kk Hkk. replace (p + kk) with (cb + (p - cb + kk)) by lia. apply HC. lia.
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
(* the entry's facts at another FP state: only the last conjunct of vr_ent (rounding mode 0) names the FP state *)
Lemma vr05_ent_at : forall (f0 : YK11.FPState) B MT e, vr_ent (fx := f0) B MT e -> frm0 fx ->
vr_ent (fx := fx) B MT e.
Proof.
intros f0 B MT e He H1. unfold vr_ent in *. cbv zeta in *.
repeat lazymatch type of He with
| ?A /\ ?R => let Ha := fresh "Ha" in destruct He as [Ha He]; split; [exact Ha|]
end.
exact H1.
Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* sup_resp's contract at every FP state (verbs_receive_c.v), and the record facts of the interface *)
Hypothesis TSUP_RESP : forall fx0 : YK11.FPState, tsup_resp_spec (fx := fx0) B MT.
Hypothesis MTL : ameter_laws MT.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* every lemma below takes all the section's hypotheses, in the order above *)
Local Set Default Proof Using "All".

(* ------------------------------------------------------------------------------------------------------------
   The entry's facts *)
Lemma vr05_ent_facts : forall e, vr_ent B MT e ->
afn_pre SEGS B VERBS_RECEIVE_STK (e_ly e) (e_S e) (e_W e) (e_regs e) (e_mem e) (e_md e) (e_ch e) /\
rec_repA B (e_ly e) (e_S e) (rdW (e_W e) (e_mem e)) (e_R e) (e_O e) /\
(0 <= e_n e <= 8192) /\ Z.of_nat (length (e_D e)) = e_n e /\
st_nev (e_S e) + ev_vr (e_R e) (e_D e) <= EV_MAX /\
blocks_bytes (e_S e) + LIVE_VERBS_RECEIVE <= LIVE_MAX /\
mo_ok MT (e_S e) (XM_VERBS_RECEIVE MT (e_R e) (e_D e)) /\
Z.of_nat (length (frames (e_S e))) <= 4 /\
r_calls (e_R e) = [] /\
Permutation (ablocks B (e_ly e) (e_S e)) (e_O e ++ e_rest e) /\
afobj SEGS B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_msg e) 24 /\
aval_mem (rdW (e_W e) (e_mem e)) (e_msg e) 4 (e_fd e) /\
frm0 fx.
Proof.
intros e H. unfold vr_ent in H.
destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
  H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & H32 & H33).
split; [exact H1|]. split; [exact H14|]. split; [exact H8|]. split; [exact H9|].
split; [exact H30|]. split; [exact H31|]. split; [exact H32|]. split; [exact H29|].
split; [exact H15|]. split; [exact H20|]. split; [exact H4|]. split; [exact H5 | exact H33].
Qed.

Lemma vr05_frameF : forall {e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc},
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
In (4, pos) (frames Sc) /\ AR SEGS B lyc Sc Wc memc mdc /\ 4096 <= F /\ F + 1024 <= alloc_ceiling.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc HC.
pose proof HC as (HJ & _ & _ & _ & (HF & _) & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 4 pos HAR Hin) as (H1 & H2 & _).
change (fs_frame_bytes 4) with 1024 in H2. rewrite <- HF in H1, H2.
split; [exact Hin|]. split; [exact HAR|]. split; [exact H1 | exact H2].
Qed.

Lemma vr05_stkF : forall {e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc},
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
astk_ok VERBS_RECEIVE_STK (e_ly e) (vr_sp0 e).
Proof.
intros. pose proof H as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _). exact Hstk.
Qed.

(* B's frame: s1 = sp0 - 192 - (sp0 - 192) mod 32 with sp0 mod 16 = 0, so s1 is sp0 - 192 or sp0 - 208 *)
Lemma vr05_s1_bounds : forall e, astk_ok VERBS_RECEIVE_STK (e_ly e) (vr_sp0 e) ->
4096 <= vr_s1 e /\ vr_sp0 e - 208 <= vr_s1 e <= vr_sp0 e - 192 /\ vr_sp0 e <= 2 ^ 47 /\
alloc_ceiling <= vr_s1 e /\ (vr_s1 e - vr_sp0 e) mod 16 = 0 /\ vr_sp0 e mod 16 = 0 /\
SUP_RESP_STK + 208 <= VERBS_RECEIVE_STK /\ 0 <= SUP_RESP_STK.
Proof.
intros e Hstk. pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
assert (HV : 16720 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HR : SUP_RESP_STK = 16512) by (vm_compute; reflexivity).
pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as Hmb.
pose proof (Z.div_mod (vr_sp0 e - 192) 32 ltac:(lia)) as D1.
pose proof (Z.div_mod (vr_sp0 e) 16 ltac:(lia)) as D2.
unfold vr_s1 in *.
assert (Hm16 : (vr_sp0 e - 192) mod 32 = 0 \/ (vr_sp0 e - 192) mod 32 = 16) by lia.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split.
{ destruct Hm16 as [E | E]; rewrite E;
  [replace (vr_sp0 e - 192 - 0 - vr_sp0 e) with ((-12) * 16) by lia
  | replace (vr_sp0 e - 192 - 16 - vr_sp0 e) with ((-13) * 16) by lia]; apply Z.mod_mul; lia. }
split; [exact Hal|]. split; lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The meter at sup_resp's call: its account is xmalloc's one malloc of |resp code|+1 <= VERBS_RECEIVE_REQ bytes
   and no free, within its EV_SUP_RESP = EV_XMALLOC = 1 event *)
Lemma vr05_xm_le : forall code, - 2 ^ 31 <= code < 2 ^ 31 ->
XM_SUP_RESP MT code <= 1 * mo_malloc MT VERBS_RECEIVE_REQ + 0 * mo_free MT.
Proof.
intros code Hcode. pose proof (resp_length code Hcode) as Hrl.
assert (HXM : XM_SUP_RESP MT code <= mo_malloc MT VERBS_RECEIVE_REQ).
{ unfold XM_SUP_RESP, XM_XMALLOC, LIVE_XMALLOC. apply (mo_malloc_mono MT MTL). unfold VERBS_RECEIVE_REQ. lia. }
lia.
Qed.

Lemma vr05_meter_pre : forall e Sc k nm code,
vr_ent B MT e -> - 2 ^ 31 <= code < 2 ^ 31 ->
vr_meter MT e Sc k nm -> k <= vr_k1 (e_R e) (e_D e) - EV_SUP_RESP ->
mo_ok MT Sc (XM_SUP_RESP MT code).
Proof.
intros e Sc k nm code He Hcode Hmet Hk.
pose proof (vr_k1_ev (e_R e) (e_D e)) as Hkev.
exact (vri_meter_ok B MT e Sc k nm (XM_SUP_RESP MT code) 1 0 EV_SUP_RESP MTL He Hmet (vr05_xm_le code Hcode)
  ltac:(unfold EV_SUP_RESP, EV_XMALLOC; lia) ltac:(unfold EV_SUP_RESP, EV_XMALLOC; lia) ltac:(lia)).
Qed.

Lemma vr05_meter_post : forall e Sc S2 k nm code,
- 2 ^ 31 <= code < 2 ^ 31 ->
vr_meter MT e Sc k nm -> mo_le MT Sc S2 (XM_SUP_RESP MT code) ->
vr_meter MT e S2 (k + EV_SUP_RESP) (nm + 1).
Proof.
intros e Sc S2 k nm code Hcode Hmet Hmo.
exact (vri_meter_step MT e Sc S2 k nm (XM_SUP_RESP MT code) 1 0 EV_SUP_RESP MTL Hmet Hmo (vr05_xm_le code Hcode)
  ltac:(unfold EV_SUP_RESP, EV_XMALLOC; lia) ltac:(unfold EV_SUP_RESP, EV_XMALLOC; lia)).
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The premises of tsup_resp_spec at a call from a dispatch state (the line and the copy blocks live, the recorder
   untouched, at most two events spent) *)
Lemma vr05_call_pre : forall e pos F q c sl rlp qv lyc Sc (W : world SEGS) regsc memc mdc k nm code,
vr_ent B MT e -> vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_RESP -> - 2 ^ 31 <= code < 2 ^ 31 ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 sl rlp (e_R e) (e_O e) qv
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
Z.of_nat (length (frames Sc)) <= 8 /\
arodata_okP SEGS RLO RHI B (rdW W memc) /\ cmd_ro_ok (rdW W memc) /\
st_nev Sc + EV_SUP_RESP <= EV_MAX /\ blocks_bytes Sc + LIVE_SUP_RESP code <= LIVE_MAX /\
mo_ok MT Sc (XM_SUP_RESP MT code).
Proof.
intros e pos F q c sl rlp qv lyc Sc W regsc memc mdc k nm code He Hk1 Hcode HC.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & HnO & Hperm & Hquit).
destruct (vr05_ent_facts e He) as (HPRE & HREC0 & Hn8 & HDn & Hev & Hlive & Hmok & Hfrs4 & Hcalls0 & Hperm0 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & Hnev & Hk0 & _).
pose proof HPRE as (HAR0 & _).
pose proof (vr_k1_ev (e_R e) (e_D e)) as Hkev.
pose proof (resp_length code Hcode) as Hrl.
pose proof (vrm_l_le (e_n e) (e_D e) ltac:(lia)) as Hl0.
pose proof (vrm_line_le (e_D e)) as Hl1. rewrite HDn in Hl1.
assert (Hbb : blocks_bytes Sc <= blocks_bytes (e_S e) +
  (6 * Z.of_nat (length (r_calls (e_R e))) + 8) * (LMAX + 2) + bsum [vr_lb e q; vr_cb e c]).
{ exact (vr_live_le SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HAR Hperm0 Hperm Hrec). }
rewrite Hcalls0 in Hbb. cbn [length Z.of_nat] in Hbb.
assert (Hbs : bsum [vr_lb e q; vr_cb e c] <= 16386).
{ unfold bsum, vr_lb, vr_cb, vr_l. cbn [fold_right snd]. lia. }
assert (Hlm : LMAX = 8192) by reflexivity.
split; [rewrite Hfrs; cbn [length app]; rewrite Nat2Z.inj_succ; lia|].
split; [exact (proj1 Henv)|].
split; [exact (proj1 (proj2 (proj2 Henv)))|].
split; [unfold EV_SUP_RESP, EV_XMALLOC in *; lia|].
split.
{ unfold LIVE_SUP_RESP, LIVE_XMALLOC, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in *. lia. }
exact (vr05_meter_pre e Sc k nm code He Hcode Hmet ltac:(lia)).
Qed.

(* after sup_resp returned: the text is a block of its own; the frame, the spills, the saves, the blocks, tok[] and
   the read-only and record facts are kept (the callee's journal has an empty footprint) *)
Lemma vr05_call_post : forall (e : vrE) pos F q c sl qv code qt lyc Sc (W : world SEGS) regsc memc mdc k nm rlp
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 tq rl2,
vr_ent B MT e ->
vr_h (e_R e) (e_D e) = (e_R e, resp code, qt) -> vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_RESP ->
- 2 ^ 31 <= code < 2 ^ 31 ->
Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 80) sl ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 sl rlp (e_R e) (e_O e) qv
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  ly2 S2 W2 mem2 md2 (k + EV_SUP_RESP) ->
ajournal SEGS B SUP_RESP_STK (vr_s1 e) [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV_SUP_RESP ->
Permutation (ablocks B ly2 S2) ((tq, Z.of_nat (length (resp code)) + 1) :: ablocks B lyc Sc) ->
(forall R O, rec_repA B lyc Sc (rdW W memc) R O -> rec_repA B ly2 S2 (rdW W2 mem2) (fst (sup_resp_m R code)) O) ->
mo_le MT Sc S2 (XM_SUP_RESP MT code) ->
vr_rv regs2 (vr_base B e ++ rl2) ->
vr_core B MT e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c] vr_sh2 sl
  rl2 (vr_R1 (e_R e) (e_D e)) (e_O e) qv (k + EV_SUP_RESP) (vr_k1 (e_R e) (e_D e)) (nm + 1) VR_NM_HD
  ly2 S2 W2 regs2 mem2 md2 /\
vr_line B e q W2 mem2 /\
(forall tp, vr_copy B e F c tp W memc -> vr_copy B e F c tp W2 mem2).
Proof.
intros e pos F q c sl qv code qt lyc Sc W regsc memc mdc k nm rlp ly2 S2 W2 regs2 mem2 md2 tq rl2
  He Hh Hk1 Hcode Hsl HC Hline HJ2 HJc Hpq Hrectr Hmo Hrv2.
assert (Hxv : vr_x (e_R e) (e_D e) = resp code) by (unfold vr_x; rewrite Hh; reflexivity).
assert (HR1 : vr_R1 (e_R e) (e_D e) = e_R e) by (unfold vr_R1; rewrite Hh; reflexivity).
rewrite Hxv, HR1, Hk1.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & HnO & Hperm & Hquit).
destruct (vr05_frameF HC) as (Hinf & HAR & HF1 & HF2).
pose proof (vr05_stkF HC) as Hstk.
destruct (vr05_s1_bounds e Hstk) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e & Hs1f & Hs1g & Hs1h).
destruct (vr05_ent_facts e He) as (_ & _ & Hn8 & HDn & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJc as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & G1 & G2 & G3 & G4 & _ & _ & _ & _ & _).
assert (Hnofp : forall a : Z, ~ inFP ([] : list (Z * Z)) a) by (intros a (r & [] & _)).
assert (Hsp2 : forall a, vr_s1 e <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memc a)
  by (intros a Ha; apply G1; [lia | lia | apply Hnofp]).
assert (Hblk : forall p n i, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
  rdW W2 mem2 (p + i) = rdW W memc (p + i)) by (intros p n i H1 H2 H3; exact (G2 p n i H1 H2 H3 (Hnofp _))).
assert (Himg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> rdW W2 mem2 a = rdW W memc a).
{ intros a H1 H2 H3. apply G3; try assumption.
  split; [intros Hs; destruct (sink_closed_pos [] (Forall_nil _) Hs) | apply Hnofp]. }
assert (Hfrm : forall a, (in_zr a (frame_rng lyc (4, pos)) \/
    in_zr a (shadow_addr (frame_addr lyc 4 pos), fs_frame_bytes 4 / 8)) -> rdW W2 mem2 a = rdW W memc a)
  by (intros a Ha; apply (G4 4 pos a Hinf Ha); apply Hnofp).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFA : frame_addr ly2 4 pos = frame_addr lyc 4 pos) by (unfold frame_addr; rewrite EF; reflexivity).
assert (EFL : flag_addr ly2 4 pos = flag_addr lyc 4 pos) by (unfold flag_addr; rewrite EF; reflexivity).
pose proof (resp_length code Hcode) as Hrl.
assert (FB : fs_frame_bytes 4 = 1024) by reflexivity.
destruct Hfr as (HFeq & HFflag & HFsh).
assert (KF : forall a, (F <= a < F + 1024 \/ shadow_addr F <= a < shadow_addr F + 128) -> rdW W2 mem2 a = rdW W memc a).
{ intros a Ha. apply Hfrm. destruct Ha as [Ha | Ha].
  - left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite FB, <- HFeq. lia.
  - right. unfold in_zr. cbn [fst snd]. rewrite FB, <- HFeq. change (1024 / 8) with 128. lia. }
assert (HinLb : In (vr_lb e q) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
assert (HinLb2 : In (vr_lb e q) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hpq)); right; exact HinLb).
assert (HinCb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. right. left. reflexivity. }
assert (HinCb2 : In (vr_cb e c) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hpq)); right; exact HinCb).
assert (Hll : Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e)).
{ unfold vr_l. rewrite <- HDn. exact (vrm_line_le (e_D e)). }
assert (Hl0 : 0 <= vr_l (e_n e) (e_D e)) by (unfold vr_l; pose proof (vrm_l_le (e_n e) (e_D e) ltac:(lia)); lia).
split; [|split].
- (* vr_core *)
  split; [exact HJ2|].
  split; [lia|].
  split; [exact (vr05_meter_post e Sc S2 k nm code Hcode Hmet Hmo)|].
  split; [unfold VR_NM_PRE, VR_NM_HD in *; lia|].
  split.
  { split; [rewrite EFA; exact HFeq|]. split.
    - rewrite EFL, <- HFflag. apply rdword_ext. intros kk Hkk. apply KF. left. lia.
    - intros i Hi. rewrite KF; [exact (HFsh i Hi)|]. right. lia. }
  split; [exact Hrv2|].
  split.
  { intros j r Hj.
    assert (Hjl : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbv [vr_saved_regs] in Hjl; cbn [length] in Hjl.
    apply (aval_mem_agree _ _ _ 8 _ (Hsv j r Hj)). intros kk Hkk. apply Hsp2. lia. }
  split.
  { unfold vr_spill in *. rewrite Forall_forall in Hsp, Hsl |- *. intros ov Hov.
    destruct (Hsl ov Hov) as [Hob1 Hob2].
    apply (aval_mem_agree _ _ _ 8 _ (Hsp ov Hov)). intros kk Hkk.
    replace (vr_s1 e + fst ov + kk) with (vr_s1 e + (fst ov + kk)) by lia. apply Hsp2. lia. }
  split.
  { exact (vr_env_of_aro B MT RRO RPG RECC PROGU ROA ly2 S2 W2 mem2 md2 (proj1 HJ2)
      (vr_aro_kept B MT RRO RPG RECC PROGU ROA e _ ly2 S2 W2 mem2 md2 _ He HJ2)). }
  split.
  { pose proof (Hrectr (e_R e) (e_O e) Hrec) as Hr2. cbn [sup_resp_m fst] in Hr2. exact Hr2. }
  split; [exact HnO|].
  split.
  { eapply Permutation_trans; [exact Hpq|].
    eapply Permutation_trans; [apply perm_skip; exact Hperm|]. apply Permutation_middle. }
  { intros j Hj.
    assert (HPG : inFP cmd_PG (A_G_QUITTING + Z.of_nat j)).
    { exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; vr05_inl | cbn [fst snd]; lia]. }
    destruct (PROGU _ HPG) as (P1 & P2 & P3).
    rewrite Himg; [exact (Hquit j Hj) | exact P1 | exact P2 | exact P3]. }
- (* the line *)
  destruct Hline as (Hfresh & Hls). split; [exact Hfresh|].
  apply (astr_atR_agree _ _ q _ (vr_l (e_n e) (e_D e) + 1) Hls); [lia|].
  intros kk Hkk. apply (Hblk q (vr_l (e_n e) (e_D e) + 1) kk HinLb HinLb2).
  pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)). lia.
- (* the copy and tok[] *)
  intros tp (Hfc & Htk). split; [exact Hfc|].
  pose proof (Verbs.toks_length (e_D e)) as Hl64.
  pose proof Htk as (_ & Htl & _).
  apply (vr05_atoks_agree _ _ _ _ _ _ _ Htk).
  + intros kk Hkk. rewrite Htl in Hkk. apply KF. left. lia.
  + intros kk Hkk. apply (Hblk c (Z.of_nat (length (Verbs.line (e_D e))) + 1) kk HinCb HinCb2).
    pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The call of sup_resp(code) (PaFx's cl_callSF: sup_resp returns at some FP state fx') *)
Definition vr05_resp_post (code : Z) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists q,
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 Permutation (ablocks B ly' S') ((q, Z.of_nat (length (resp code)) + 1) :: ablocks B ly S) /\
 Forall (fun qk => iv_apart q (Z.of_nat (length (resp code)) + 1) (fst qk) (snd qk)) (ablocks B ly S) /\
 In (q, Z.of_nat (length (resp code)) + 1) (ablocks B ly' S') /\ astr_atR (rdW W' mem') q (resp code) /\
 (forall R O, rec_repA B ly S (rdW W mem) R O -> rec_repA B ly' S' (rdW W' mem') (fst (sup_resp_m R code)) O) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_RESP code /\
 mo_le MT S S' (XM_SUP_RESP MT code).

Lemma vr05_resp_call : forall e pos F q c sl qv lyc Sc (W : world SEGS) regs mem md k nm retk code qt rlk,
vr_ent B MT e ->
vr_h (e_R e) (e_D e) = (e_R e, resp code, qt) -> vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_RESP ->
- 2 ^ 31 <= code < 2 ^ 31 ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 sl ((1, BASE + retk) :: (10, code) :: rlk)
  (e_R e) (e_O e) qv k 2 nm VR_NM_PRE lyc Sc W regs mem md ->
vr_line B e q W mem ->
Forall (fun rv => 18 <= fst rv <= 27) rlk ->
Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 80) sl ->
0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_sup_resp)) mem (seg_rom SEGS)) md)
  (fun W2 c2 => exists (fx' : YK11.FPState) tq ly2 S2 regs2 mem2 md2,
   c2 = mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 /\ fxrel fx fx' /\
   4096 <= tq /\ astr_atR (rdW W2 mem2) tq (vr_x (e_R e) (e_D e)) /\
   vr_core B MT e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c] vr_sh2
     sl ((10, tq) :: rlk) (vr_R1 (e_R e) (e_D e)) (e_O e) qv (k + EV_SUP_RESP)
     (vr_k1 (e_R e) (e_D e)) (nm + 1) VR_NM_HD ly2 S2 W2 regs2 mem2 md2 /\
   vr_line B e q W2 mem2 /\
   (forall tp, vr_copy B e F c tp W mem -> vr_copy B e F c tp W2 mem2)).
Proof.
intros e pos F q c sl qv lyc Sc W regs mem md k nm retk code qt rlk He Hh Hk1 Hcode HC Hline Hcs Hsl Hretk Hretk2.
assert (Hxv : vr_x (e_R e) (e_D e) = resp code) by (unfold vr_x; rewrite Hh; reflexivity).
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & HnO & Hperm & Hquit).
destruct (vr05_ent_facts e He) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm).
destruct (vr05_call_pre e pos F q c _ _ qv lyc Sc W regs mem md k nm code He Hk1 Hcode HC)
  as (Hfrs8 & Haro & Hro & Hev1 & Hlv1 & Hmo1).
pose proof (vr05_stkF HC) as Hstk.
destruct (vr05_s1_bounds e Hstk) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e & Hs1f & Hs1g & Hs1h).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (R1 : getr regs 1 = w64 (BASE + retk))
  by (apply (vr_rv_get regs _ 1 _ Hrv); apply in_or_app; right; left; reflexivity).
assert (R10 : getr regs 10 = w64 code)
  by (apply (vr_rv_get regs _ 10 _ Hrv); apply in_or_app; right; right; left; reflexivity).
assert (R2 : getr regs 2 = w64 (vr_s1 e)) by (apply (vr_rv_get regs _ 2 _ Hrv); apply in_or_app; left; unfold vr_base; vr05_inl).
assert (R3 : getr regs 3 = w64 (as_gp B)) by (apply (vr_rv_get regs _ 3 _ Hrv); apply in_or_app; left; unfold vr_base; vr05_inl).
assert (R4 : getr regs 4 = w64 (as_tp B)) by (apply (vr_rv_get regs _ 4 _ Hrv); apply in_or_app; left; unfold vr_base; vr05_inl).
assert (R8 : getr regs 8 = w64 (vr_sp0 e)) by (apply (vr_rv_get regs _ 8 _ Hrv); apply in_or_app; left; unfold vr_base; vr05_inl).
assert (Hsp1 : spZ regs = vr_s1 e) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* the frame chain at the call: s0 = sp0, verbs_receive's frame pointer, with the prologue's saves of ra and the
   entry s0 on top of afn_pre's chain (the kit's vr_chain_at) *)
destruct (vr_chain_at B MT RRO RPG RECC PROGU ROA e lyc Sc W mem md k pos regs He HJ Hsv R8) as (ch1 & Hch1).
eapply SRr_mono.
{ apply (cl_callSF B LAWS W regs mem (Z_to_bv 64 (BASE + AF_sup_resp)) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e)
    (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc md k SUP_RESP_STK [] EV_SUP_RESP (vr_s1 e - vr_sp0 e)
    (w64 (BASE + retk)) ch1 (vr05_resp_post code lyc Sc W mem) HJ).
  - rewrite Hsp1. lia.
  - exact Hs1e.
  - lia.
  - exact Hs1h.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - unfold w64. apply ret_ok_codeptr_v; [lia | exact Hretk2].
  - unfold w64. rewrite unsigned_lit_small by lia. lia.
  - replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) by lia. exact Hch1.
  - intros HPRE1. eapply SRr_mono.
    { exact (TSUP_RESP fx lyc Sc W regs mem md ch1 code HPRE1 Hfrm Hfrs8 Haro Hro R10 Hcode Hev1 Hlv1 Hmo1). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HR' & HC' & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. rewrite R1. split; [reflexivity|]. split; [exact HR'|].
    split; [exact HC'|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a (r & [] & _). }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJc & HP2 & HK).
destruct HK as (tq & Htq10 & Htq & Hpq & Hap & Hin & Hstr & Hrectr & Hbb & Hmo).
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
exists fx', tq, ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact Hfx|]. split; [lia|].
split; [rewrite Hxv; exact Hstr|].
apply (vr05_call_post e pos F q c sl qv code qt lyc Sc W regs mem md k nm _ ly2 S2 W2 regs2 mem2 md2 tq ((10, tq) :: rlk)
  He Hh Hk1 Hcode Hsl HC Hline HJ2 HJc Hpq Hrectr Hmo).
apply vr_rv_intro. intros r v Hin'. apply in_app_or in Hin' as [Hin' | [Hin' | Hin']].
- assert (Hr : acallee_saved r).
  { unfold vr_base in Hin'. cbn in Hin'. destruct Hin' as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _;
    unfold acallee_saved; lia. }
  rewrite (HP2 r Hr). apply (vr_rv_get regs _ _ _ Hrv). apply in_or_app. left. exact Hin'.
- injection Hin' as <- <-. exact Htq10.
- assert (Hr : acallee_saved r).
  { rewrite Forall_forall in Hcs. pose proof (Hcs (r, v) Hin') as Hrr. cbn [fst] in Hrr. unfold acallee_saved. lia. }
  rewrite (HP2 r Hr). apply (vr_rv_get regs _ _ _ Hrv). apply in_or_app. right. right. right. exact Hin'.
Qed.

End e.
End f.
End d.
