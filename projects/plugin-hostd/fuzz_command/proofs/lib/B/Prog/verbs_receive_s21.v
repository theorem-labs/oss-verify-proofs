(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S21 PINSET (B 0x8d654-0x8d668, 6 instructions) of the walk of
   verbs_receive on the ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v
   vr_s21_stmt): `mv a0,s2` (the trimmed line), `ld s3,40(s1)` (B reloads tok from the spill slot, where A held it
   in s6), `mv a1,s3; mv a2,s9` (tok, ntok), `jal pin_set_words` and `j 0x8d88c` into the shared sup_resp stub with
   pin_set_words' code already in a0 (vr_pr at 0x8d88c, whose register list carries (10, code) exactly there). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c arg_s_c record_c answer_code_c hand_back_c pins_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_live.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s21_kit verbs_receive_s21_arm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the listing offset of the segment (B pc - 0x86530) *)
Definition S21_PC : Z := AF_verbs_receive + 0x808.   (* 0x8d654 mv a0,s2 *)

(* the handler of pin_set: the model's step is pin_set_words_m, a refusal or the call of pins_set; either way its
   text is resp of the code pin_set_run returns (VerbsRun.v:31-38) *)
Lemma vr_pinset_h : forall R D args, Verbs.toks D = Verbs.Lit.verb_pin_set :: args ->
  vr_h R D = (fst (VerbsRun.pin_set_run R (Verbs.line D) args), resp (snd (VerbsRun.pin_set_run R (Verbs.line D) args)),
    false).
Proof.
intros R D args T.
assert (St : vr_st D = Verbs.pin_set_words_m (Verbs.line D) args) by (rewrite (vr_st_route D _ args T); reflexivity).
assert (HP : (exists u f l v, Verbs.pin_set_words_m (Verbs.line D) args = Verbs.SPinSet u f l v) \/
  Verbs.pin_set_words_m (Verbs.line D) args = Verbs.reject).
{ unfold Verbs.pin_set_words_m.
  destruct args as [|u [|fl [|ly [|vd [|x rest]]]]]; try (right; reflexivity);
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  first [right; reflexivity | left; do 4 eexists; reflexivity]. }
unfold vr_h. rewrite St. unfold VerbsRun.pin_set_run.
destruct HP as [(u & f & l & v & Hs) | Hs]; rewrite Hs.
- cbn [VerbsRun.run_step]. destruct (pins_set_m R (Some u) (Some f) (Some l) v) as [R1 rc]. reflexivity.
- reflexivity.
Qed.

Lemma vr_ev_psw_nonneg : forall R ln args, 0 <= EV_PIN_SET_WORDS R ln args.
Proof.
intros R ln args. unfold EV_PIN_SET_WORDS.
destruct (Verbs.pin_set_words_m ln args); try lia.
match goal with |- context [pins_set_m ?R0 ?a ?b ?c ?d] => destruct (pins_set_m R0 a b c d) as [R1 r] end.
unfold EV_PINS_SET, EV_LV2_REFUSALS_FORGET, EV_ANSWER_CODE, EV_HAND_BACK, EV_RECORD, EV_ARG_S, EV_XMALLOC,
rec_spill_frees.
repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
Qed.

(* from a recorder with no recorded call, pin_set_words spends at most 9 events: pins_set's 8 (record()'s spill arm
   is empty, four arg_s copies and answer_code's four) and lv2_refusals_forget's 1 *)
Lemma vr_ev_psw_le : forall R ln args, r_calls R = [] -> EV_PIN_SET_WORDS R ln args <= 9.
Proof.
intros R ln args Hc.
assert (E0 : forall u f l v, rec_spill_frees (fst (pins_set_m R u f l v)) = 0).
{ intros u f l v. unfold pins_set_m, rec_stub_code, rec_record. rewrite Hc. cbv zeta.
  match goal with |- context [r_refuse ?X =? 0] => destruct (r_refuse X =? 0) end; reflexivity. }
unfold EV_PIN_SET_WORDS.
destruct (Verbs.pin_set_words_m ln args); try lia.
match goal with |- context [pins_set_m ?R0 ?a ?b ?c ?d] =>
  pose proof (E0 a b c d) as E1; destruct (pins_set_m R0 a b c d) as [R1 r] eqn:Ep end.
try rewrite Ep in E1. cbn [fst] in E1.
unfold EV_PINS_SET, EV_LV2_REFUSALS_FORGET, EV_ANSWER_CODE, EV_HAND_BACK, EV_RECORD, EV_ARG_S, EV_XMALLOC.
rewrite (vr_spill_frees0 R Hc), E1. destruct (r =? 0); lia.
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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* the callee's contract at every FP state (verbs_receive_c.v) and the record facts of the brief *)
Hypothesis TPIN_SET_WORDS : forall fx0 : YK11.FPState, @tpin_set_words_spec fx0 rc SK PI B MT.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.

Lemma vr_s21 : vr_s21_stmt B MT.
Proof.
intros e W cf Hent Hrt.
destruct Hrt as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hne & HC & HL & HCP).
change (vr_pc (vr_route_pc VRR.RPinset)) with (vr_pc 0x8d654).
destruct (Verbs.toks (e_D e)) as [|v args] eqn:Ht; [congruence|].
pose proof (vr_route_pinset v args Hroute) as Hv. subst v.
pose proof HC as (HJ & Hk & HM & Hnm & HFR & HRV & HSV & HSP & HENV & HREC & HnD & HPERM & HQ).
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HlenD & _ & _ & _ & _ & _ & Hcalls & _ & _ & _ & Hdecl & _ & _ & _ & _
  & _ & HVO & _).
destruct (vr_ent_stk B MT e Hent) as (Hs1lo & Hs1sp & Hs1al & Hsp47 & Hsp16 & HspS).
pose proof asan_consts as (CR & _).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
assert (HinF : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof HFR as (EF & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR HinF) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
pose proof (Verbs.toks_length (e_D e)) as Htl. rewrite Ht in Htl.
assert (Hnt : vr_ntok (e_D e) = Z.of_nat (length (Verbs.Lit.verb_pin_set :: args)))
  by (unfold vr_ntok; rewrite Ht; reflexivity).
cbn [length] in Hnt, Htl.
assert (RG : forall r v, In (r, v) (vr_base B e ++ vr_rl_rt e F q (hd 0 tp)) -> getr regsc (Z_to_bv 5 r) = w64 v)
  by (intros r v Hin; exact (vr_rv_in _ _ _ _ HRV Hin)).
unfold vr_base, vr_rl_rt in RG. cbn [app hd] in RG.
pose proof (RG 9 (vr_s1 e) ltac:(vr_in)) as R9.
pose proof (RG 18 q ltac:(vr_in)) as R18.
pose proof (RG 25 (vr_ntok (e_D e)) ltac:(vr_in)) as R25.
pose proof (vr_spill_in e W memc _ 40 (F + 32) HSP ltac:(unfold vr_sl3; vr_in)) as HStok.
destruct (vr_tmps_in B e q c lyc Sc W memc mdc HAR HPERM (vr_lb e q) ltac:(left; reflexivity)) as [Hlb1 Hlb2].
destruct (vr_tmps_in B e q c lyc Sc W memc mdc HAR HPERM (vr_cb e c) ltac:(right; left; reflexivity)) as [Hcb1 Hcb2].
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hlb1) as (_ & Hq4096 & Hqceil & _).
unfold vr_lb in Hq4096, Hqceil. cbn [fst snd] in Hq4096, Hqceil.
pose proof (vr_strnlen_le (e_n e) (e_D e)) as Hsl.
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1)) as Hrq.
pose proof (vr_seed_t W regsc memc S21_PC (vr_s1 e) (F + 32) R9 ltac:(lia) ltac:(lia) ltac:(lia) HStok) as HS.
set (E := Eimg (Ereg regsc [Z_to_bv 64 (F + 32)])) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regsc [Z_to_bv 64 (F + 32)]) E) by apply vr_env_agree_Eimg.
assert (E18 : ew E 18 = Z_to_bv 64 q) by (unfold E; rewrite vr_ew_reg by lia; exact R18).
assert (E25 : ew E 25 = Z_to_bv 64 (vr_ntok (e_D e))) by (unfold E; rewrite vr_ew_reg by lia; exact R25).
assert (E32 : ew E 32 = Z_to_bv 64 (F + 32)) by exact (vr_ew_extra regsc _ 0 ltac:(lia)).
clearbody E.
replace (cfg_at SEGS (vr_pc 0x8d654) regsc memc mdc)
  with (mkCfg (mkst regsc (Z_to_bv 64 (BASE + S21_PC)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, vr_pc, S21_PC; f_equal; f_equal; f_equal; lia).
(* 0x8d654 mv a0,s2; 0x8d658 ld s3,40(s1); 0x8d65c mv a1,s3; 0x8d660 mv a2,s9; 0x8d664 jal pin_set_words *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
vr_unchanged (@pa_segs _ cmd_listing PI) UN1 HFr. clear HF HFr HG.
assert (RS : rd_same (rdW W memc) (rdW W (ms_mem ms))).
{ apply vr_rd_same_of. intros x Hx. exact (UN1 x Hx (fun y => y)). }
prreg HS (1%bv : bv 5) Q1.
prreg HS (10%bv : bv 5) Q10. rewrite E18 in Q10.
prreg HS (11%bv : bv 5) Q11. rewrite E32 in Q11.
prreg HS (12%bv : bv 5) Q12. rewrite E25 in Q12.
prreg HS (19%bv : bv 5) Q19. rewrite E32 in Q19.
pose proof (vr_kept_regs E _ _ regsc [Z_to_bv 64 (F + 32)]
  [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
rewrite (SIGP CS_pin_set_words) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_pin_set_words) with AF_pin_set_words.
set (rk := [(19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)]).
assert (Hcs : vr_cs B MT e pos F q c 0x7138 rk tp lyc Sc W (ms_regs ms) (ms_mem ms) mdv k nm).
{ split; [|split; [exact (vr_line_same B e q W W memc _ RS HL) | exact (vr_copy_same B e F c tp W W memc _ RS HCP)]].
  apply (vr_core_same B MT e pos F _ _ _ _ _ _ _ _ k 2 _ nm VR_NM_PRE _ lyc Sc W regsc memc mdc _ _ _ HC HJ RS);
    [| lia | unfold VR_NM_PRE in *; lia].
  apply vr_rv_mk. intros r0 v0 Hin. apply in_app_or in Hin as [Hin|Hin].
  - unfold vr_base in Hin. cbn [In] in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
    rewrite KR by (cbn; tauto); apply RG; vr_in.
  - unfold rk in Hin. cbn [In] in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]; injection E1 as <- <-;
    first [exact Q1 | exact Q19 | rewrite KR by (cbn; tauto); apply RG; vr_in]. }
(* the arguments of pin_set_words at the call *)
pose proof (vr_line_same B e q W W memc _ RS HL) as (_ & HLs).
pose proof (vr_copy_same B e F c tp W W memc _ RS HCP) as (_ & HTOK).
pose proof HTOK as (HT8 & _).
rewrite Ht in HTOK.
pose proof (vr_frame_same lyc W W memc (ms_mem ms) pos F vr_sh2 RS HFR) as HFR2.
assert (HAF : afobj SEGS B lyc Sc W (ms_mem ms) (F + 32) (8 * vr_ntok (e_D e)))
  by exact (vr_tok_afobj B lyc Sc W (ms_mem ms) pos F (vr_ntok (e_D e)) HFR2 HinF HT8 ltac:(lia)).
assert (HLL : Z.of_nat (length (Verbs.line (e_D e))) + 1 <= vr_l (e_n e) (e_D e) + 1).
{ pose proof (vr_line_le_l (e_D e)) as H0. rewrite HlenD in H0. unfold vr_l. lia. }
set (EV1 := EV_PIN_SET_WORDS (e_R e) (Verbs.line (e_D e)) args).
set (Rr := VerbsRun.pin_set_run (e_R e) (Verbs.line (e_D e)) args).
assert (Hvh : vr_h (e_R e) (e_D e) = (fst Rr, resp (snd Rr), false)) by exact (vr_pinset_h (e_R e) (e_D e) args Ht).
assert (Hk1 : vr_k1 (e_R e) (e_D e) = 2 + EV1 + EV_SUP_RESP)
  by (rewrite (vr_k1_pinset (e_R e) (e_D e) args Ht); unfold EV1; lia).
assert (HNF : 0 <= EV1 <= EV1) by (pose proof (vr_ev_psw_nonneg (e_R e) (Verbs.line (e_D e)) args); unfold EV1; lia).
(* pin_set_words' account, per event (pin_set_words_c.v:107-108): EV1 mallocs and EV1 frees, EV1 <= 9 from the
   entry's empty call table *)
set (XM1 := XM_PIN_SET_WORDS MT (e_R e) (Verbs.line (e_D e)) args).
assert (HE9 : EV1 <= 9) by exact (vr_ev_psw_le (e_R e) (Verbs.line (e_D e)) args Hcalls).
assert (HNM : EV1 + VR_NM_PRE <= VR_NM_PR) by (unfold VR_NM_PRE, VR_NM_PR; lia).
assert (HXM : XM1 <= EV1 * mo_malloc MT VERBS_RECEIVE_REQ + EV1 * mo_free MT)
  by (unfold XM1, XM_PIN_SET_WORDS; fold EV1; change PIN_SET_WORDS_REQ with VERBS_RECEIVE_REQ;
      rewrite Z.mul_add_distr_l; lia).
assert (HLV : LIVE_PIN_SET_WORDS <= 20 * VERBS_RECEIVE_REQ)
  by (unfold LIVE_PIN_SET_WORDS, PIN_SET_WORDS_MALLOCS, PIN_SET_WORDS_REQ, VERBS_RECEIVE_REQ; lia).
assert (HV : PIN_SET_WORDS_STK = ltac:(let v := eval vm_compute in PIN_SET_WORDS_STK in exact v)) by reflexivity.
assert (HV2 : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
assert (HST0 : 0 <= PIN_SET_WORDS_STK) by lia.
assert (HSTK : PIN_SET_WORDS_STK + 208 <= VERBS_RECEIVE_STK) by lia.
assert (Hstop : vr_pc 0x8d88c = BASE + 0x735c) by (unfold vr_pc, AF_verbs_receive; lia).
assert (Hrun : sym_run_toN_pi pl_tpi FUEL 0x735c (vr_ss_ret 0x7138) = (vr_ss_ret 0x735c, PRS_running))
  by (vm_compute; reflexivity).
assert (Hne' : Verbs.toks (e_D e) <> []) by (rewrite Ht; discriminate).
assert (Hntok : vr_pr_ntok 0x8d88c (length (Verbs.toks (e_D e)))) by (unfold vr_pr_ntok; rewrite Ht; cbn; lia).
assert (Hrl : forall code, vr_rl_pr e F q c 0x8d88c code = (10, code) :: rk) by (intros code; reflexivity).
assert (Hrk : Forall (fun rv => acallee_saved (fst rv)) rk)
  by (unfold rk; repeat (apply Forall_cons; [unfold acallee_saved; cbn [fst]; lia|]); apply Forall_nil).
assert (Hcode : 0x8d88c <> 0x8d88c -> snd Rr = -902) by (intros H0; exfalso; apply H0; reflexivity).
assert (CALL : forall ch, afn_pre SEGS B PIN_SET_WORDS_STK lyc Sc W (ms_regs ms) (ms_mem ms) mdv ch ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W (ms_mem ms)) -> cmd_ro_ok (rdW W (ms_mem ms)) ->
  rec_repA B lyc Sc (rdW W (ms_mem ms)) (e_R e) (e_O e) -> Z.of_nat (length (frames Sc)) <= 5 ->
  st_nev Sc + EV1 <= EV_MAX -> blocks_bytes Sc + LIVE_PIN_SET_WORDS <= LIVE_MAX ->
  mo_ok MT Sc XM1 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_pin_set_words) (ms_regs ms) (ms_mem ms) mdv)
  (apost_baseF SEGS B PIN_SET_WORDS_STK (vr_fp1 (e_O e)) (ms_regs ms) lyc Sc W (ms_mem ms) mdv EV1
    (vr_ps_post B MT (e_O e) Rr LIVE_PIN_SET_WORDS XM1 lyc Sc))).
{ intros ch HPRE1 H1 H2 H3 H4 H5 H6 H7.
  exact (TPIN_SET_WORDS fx lyc Sc W (ms_regs ms) (ms_mem ms) mdv ch q (vr_l (e_n e) (e_D e) + 1) (F + 32)
    (vr_ntok (e_D e)) c (Z.of_nat (length (Verbs.line (e_D e))) + 1) (Verbs.line (e_D e)) tp
    (Verbs.Lit.verb_pin_set :: args) (e_R e) (e_O e)
    HPRE1 (vr18_ent_frm0 B MT e Hent) H1 Q10 ltac:(lia) Q11 ltac:(lia) Q12 Hlb1 Hlb2 HLs HLL HAF HTOK Hcb1 Hcb2
    Hnt ltac:(lia) eq_refl
    H3 Hdecl ltac:(rewrite Hcalls; cbn; lia) H2 HVO H4 H5 H6 H7). }
exact (vr_call_arm_ps B MT HB MTL ROA RRO RPG RECC PROGU e W pos F q c 0x7138 0x735c rk 0x8d88c tp lyc Sc
  (ms_regs ms) (ms_mem ms) mdv k nm AF_pin_set_words PIN_SET_WORDS_STK EV1 LIVE_PIN_SET_WORDS
  XM1 EV1 EV1 Rr
  Hent Hcs Hne' Hntok Hrl Hrk Hvh Hcode Hk1 HNF HNF HNM HXM HLV HST0 HSTK ltac:(lia) eq_refl Hstop Hrun CALL).
Qed.

End e.
End f.
End d.
