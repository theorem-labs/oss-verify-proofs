(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S19 CHAIN (0x8dcd0-0x8dcdc, 4 instructions) of the walk of verbs_receive
   on the ASan build of plugin-hostd/fuzz_command (lib/A/Prog/verbs_receive_iface.v vr_s19_stmt):
   `mv a0,s6; mv a1,s9; jal chain_words; j 0x8dca4` calls chain_words(&tok[0], ntok) through its statement
   (chain_words_c.v, exact text block since statement pass 4b) and leaves its text in a0 (vr_hd at 0x8dca4). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c arg_i_c answer_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
verbs_receive_s18_kit verbs_receive_s18_call verbs_receive_s18_arm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the listing offset of the segment (0x8d480 + d) *)
Definition S19_PC : Z := AF_verbs_receive + 0x850.   (* 0x8dcd0 mv a0,s6 *)

(* the handler of chain: chain_words_m's step, the call of sup_chain or a refusal, is chain_run (VerbsRun.v:40-44) *)
Lemma vr_chain_h : forall R D args, Verbs.toks D = Verbs.Lit.verb_chain :: args ->
  vr_h R D = (VerbsRun.chain_run R args, false).
Proof.
intros R D args T.
assert (St : vr_st D = Verbs.chain_words_m args) by (rewrite (vr_st_route D _ args T); reflexivity).
assert (HP : (exists c0, Verbs.chain_words_m args = Verbs.SCall c0) \/ Verbs.chain_words_m args = Verbs.reject).
{ unfold Verbs.chain_words_m.
  destruct args as [|a [|b rest]]; try (right; reflexivity).
  destruct (Verbs.number_m a), (Verbs.numbers_m (b :: rest)); first [left; eexists; reflexivity | right; reflexivity]. }
unfold vr_h. rewrite St. unfold VerbsRun.chain_run.
destruct HP as [(c0 & Hs) | Hs]; rewrite Hs; reflexivity.
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
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* the callee's contract at every FP state (verbs_receive_c.v:195) and the named record facts *)
Hypothesis TCHAIN_WORDS : forall fx0 : YK11.FPState, @tchain_words_spec fx0 rc SK PI B MT.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.

(* chain_words' post (its text block is exactly (p, |x| + 1)), in the form of a recorder call that hands back a
   text (vr_rc_post) *)
Lemma vr_cw_post : forall R O args LIVE1 XM1 ly S ly' S' W' regs' mem' md',
  AR SEGS B ly' S' W' mem' md' ->
  (let '(R', x) := VerbsRun.chain_run R args in
   exists (O' : list (Z * Z)) (p n : Z),
   rec_repA B ly' S' (rdW W' mem') R' O' /\
   getr regs' 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\ In (p, n) (ablocks B ly' S') /\ ~ In (p, n) O' /\
   astr_atR (rdW W' mem') p x /\ n = Z.of_nat (length x) + 1 /\
   (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> iv_apart (fst pn) (snd pn) p n) /\
   (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
   (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (p, n)) /\
   (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
   blocks_bytes S' <= blocks_bytes S + LIVE1 /\
   mo_le MT S S' XM1) ->
  vr_rc_post B MT R O (VerbsRun.chain_run R args) LIVE1 XM1 ly S ly' S' W' regs' mem' md'.
Proof.
intros R O args LIVE1 XM1 ly S ly' S' W' regs' mem' md' HAR' HQ.
unfold vr_rc_post. destruct (VerbsRun.chain_run R args) as [R' x].
destruct HQ as (O' & p & n & Hrec' & Ha0 & Hp & Hin & HnO & Hstr & Hn & Hap & Hkeep & Hall & HO' & Hbb & Hmle).
subst n. exists R', x, p, O'.
split; [reflexivity|]. split; [exact Ha0|]. split; [exact Hp|]. split; [exact Hrec'|]. split; [exact HO'|].
split; [exact Hin|].
split.
{ intros pn H1 H2 E. subst pn. pose proof (Hap _ H1 H2) as Hd. unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
split.
{ intros Hm. apply in_map_iff in Hm as ([p' n'] & Hp' & HinO'). cbn [fst] in Hp'. subst p'.
  assert (HinB : In (p, n') (ablocks B ly' S')) by exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec' HinO').
  assert (Hne : (p, n') <> (p, Z.of_nat (length x) + 1)) by (intros E; rewrite E in HinO'; exact (HnO HinO')).
  pose proof (sep_blocks SEGS B LAWS ly' S' W' mem' md' p n' p _ HAR' HinB Hin Hne) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR' HinB) as (_ & _ & _ & _ & _ & _ & Hn').
  pose proof (req_size_pos n' ltac:(lia)) as Hr1.
  pose proof (req_size_pos (Z.of_nat (length x) + 1) ltac:(lia)) as Hr2.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
split; [exact Hstr|].
split; [intros pn H1 H2; split; [exact (Hkeep _ H1 H2) | exact (Hap _ H1 H2)]|].
split; [exact Hall|]. split; [exact Hbb | exact Hmle].
Qed.

Lemma vr_s19 : vr_s19_stmt B MT.
Proof.
intros e W cf Hent Hrt.
destruct Hrt as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hne & HC & HL & HCP).
change (vr_pc (vr_route_pc VRR.RChain)) with (vr_pc 0x8dcd0).
destruct (Verbs.toks (e_D e)) as [|v args] eqn:Ht; [congruence|].
pose proof (vr_route_chain v args Hroute) as Hv. subst v.
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
assert (Hnt : vr_ntok (e_D e) = Z.of_nat (length (Verbs.Lit.verb_chain :: args))) by (unfold vr_ntok; rewrite Ht; reflexivity).
cbn [length] in Hnt, Htl.
assert (RG : forall r v, In (r, v) (vr_base B e ++ vr_rl_rt e F q (hd 0 tp) VRR.RChain) -> getr regsc (Z_to_bv 5 r) = w64 v)
  by (intros r v Hin; exact (vr_rv_in _ _ _ _ HRV Hin)).
unfold vr_base, vr_rl_rt in RG. cbn [vr_rgroup app] in RG.
pose proof (RG 22 (F + 32) ltac:(vr_in)) as R22.
pose proof (RG 25 (vr_ntok (e_D e)) ltac:(vr_in)) as R25.
destruct (vr_tmps_in B e q c lyc Sc W memc mdc HAR HPERM (vr_cb e c) ltac:(right; left; reflexivity)) as [Hcb1 Hcb2].
pose proof (vr_seed0 W regsc memc S19_PC) as HS.
set (E := Eimg (Ereg regsc [])) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regsc []) E) by apply vr_env_agree_Eimg.
assert (E22 : ew E 22 = Z_to_bv 64 (F + 32)) by (unfold E; rewrite vr_ew_reg by lia; exact R22).
assert (E25 : ew E 25 = Z_to_bv 64 (vr_ntok (e_D e))) by (unfold E; rewrite vr_ew_reg by lia; exact R25).
clearbody E.
replace (cfg_at SEGS (vr_pc 0x8dcd0) regsc memc mdc)
  with (mkCfg (mkst regsc (Z_to_bv 64 (BASE + S19_PC)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, vr_pc, S19_PC; f_equal; f_equal; f_equal; lia).
(* 0x8dcd0 mv a0,s6; 0x8dcd4 mv a1,s9; 0x8dcd8 jal chain_words *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
vr_unchanged (@pa_segs _ cmd_listing PI) UN1 HFr. clear HF HFr HG.
assert (RS : rd_same (rdW W memc) (rdW W (ms_mem ms))).
{ apply vr_rd_same_of. intros x Hx. exact (UN1 x Hx (fun y => y)). }
prreg HS (1%bv : bv 5) Q1.
prreg HS (10%bv : bv 5) Q10. rewrite E22 in Q10.
prreg HS (11%bv : bv 5) Q11. rewrite E25 in Q11.
pose proof (vr_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
rewrite (SIGP CS_chain_words) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_chain_words) with AF_chain_words.
set (rk := [(18, q); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)]).
assert (Hcs : vr_cs B MT e pos F q c 0x77f8 rk tp lyc Sc W (ms_regs ms) (ms_mem ms) mdv k nm).
{ split; [|split; [exact (vr_line_same B e q W W memc _ RS HL) | exact (vr_copy_same B e F c tp W W memc _ RS HCP)]].
  apply (vr_core_same B MT e pos F _ _ _ _ _ _ _ _ k 2 _ nm VR_NM_PRE _ lyc Sc W regsc memc mdc _ _ _ HC HJ RS);
    [| lia | unfold VR_NM_PRE in *; lia].
  apply vr_rv_mk. intros r0 v Hin. apply in_app_or in Hin as [Hin|Hin].
  - unfold vr_base in Hin. cbn [In] in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
    rewrite KR by (cbn; tauto); apply RG; vr_in.
  - unfold rk in Hin. cbn [In] in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]; injection E1 as <- <-;
    first [exact Q1 | rewrite KR by (cbn; tauto); apply RG; vr_in]. }
(* the arguments of chain_words at the call *)
pose proof (vr_copy_same B e F c tp W W memc _ RS HCP) as (_ & HTOK).
pose proof HTOK as (HT8 & _).
rewrite Ht in HTOK.
pose proof (vr_frame_same lyc W W memc (ms_mem ms) pos F vr_sh2 RS HFR) as HFR2.
assert (HAF : afobj SEGS B lyc Sc W (ms_mem ms) (F + 32) (8 * vr_ntok (e_D e)))
  by exact (vr_tok_afobj B lyc Sc W (ms_mem ms) pos F (vr_ntok (e_D e)) HFR2 HinF HT8 ltac:(lia)).
set (EV1 := EV_CHAIN_WORDS (e_R e)).
set (m := VerbsRun.chain_run (e_R e) args).
assert (Hvh : vr_h (e_R e) (e_D e) = (m, false)) by exact (vr_chain_h (e_R e) (e_D e) args Ht).
assert (Hk1 : vr_k1 (e_R e) (e_D e) = 2 + EV1) by exact (vr_k1_chain (e_R e) (e_D e) args Ht).
assert (HNF : 0 <= EV1 <= EV1).
{ unfold EV1, EV_CHAIN_WORDS. pose proof (Z.le_max_r (EV_SUP_CHAIN (e_R e)) EV_SUP_RESP).
  unfold EV_SUP_RESP, EV_XSTRDUP in *. lia. }
assert (HNM : 6 + VR_NM_PRE <= VR_NM_HD) by (unfold VR_NM_PRE, VR_NM_HD; lia).
(* chain_words' six mallocs are within its events: EV_SUP_CHAIN R >= 8 (sup_chain_c.v:60-61) *)
assert (HNM1 : 0 <= 6 <= EV1).
{ pose proof (vr_spill_frees0 _ Hcalls) as Hs0.
  unfold EV1, EV_CHAIN_WORDS. pose proof (Z.le_max_l (EV_SUP_CHAIN (e_R e)) EV_SUP_RESP) as Hm.
  unfold EV_SUP_CHAIN, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in Hm |- *. lia. }
assert (HXM : XM_CHAIN_WORDS MT (e_R e) <= 6 * mo_malloc MT VERBS_RECEIVE_REQ + EV1 * mo_free MT)
  by (unfold XM_CHAIN_WORDS, CHAIN_WORDS_MALLOCS, CHAIN_WORDS_REQ, VERBS_RECEIVE_REQ, EV1; lia).
assert (HLV : LIVE_CHAIN_WORDS <= 20 * VERBS_RECEIVE_REQ)
  by (unfold LIVE_CHAIN_WORDS, CHAIN_WORDS_MALLOCS, CHAIN_WORDS_REQ, VERBS_RECEIVE_REQ; lia).
assert (HV : CHAIN_WORDS_STK = ltac:(let v := eval vm_compute in CHAIN_WORDS_STK in exact v)) by reflexivity.
assert (HV2 : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
assert (HST0 : 0 <= CHAIN_WORDS_STK) by lia.
assert (HSTK : CHAIN_WORDS_STK + 208 <= VERBS_RECEIVE_STK) by lia.
assert (Hstop : vr_pc 0x8dca4 = BASE + 0x77c0) by (unfold vr_pc, AF_verbs_receive; lia).
assert (Hrun : sym_run_toN_pi pl_tpi FUEL 0x77c0 (vr_ss_ret 0x77f8) = (vr_ss_ret 0x77c0, PRS_running))
  by (vm_compute; reflexivity).
assert (Hntok : vr_hd_ntok 0x8dca4 (length (Verbs.toks (e_D e)))) by (unfold vr_hd_ntok; rewrite Ht; cbn; lia).
assert (Hrl : forall tq, vr_rl_hd e F q c 0x8dca4 tq = (10, tq) :: rk) by (intros tq; reflexivity).
assert (Hrk : Forall (fun rv => acallee_saved (fst rv)) rk)
  by (unfold rk; repeat (apply Forall_cons; [unfold acallee_saved; cbn [fst]; lia|]); apply Forall_nil).
assert (CALL : forall ch, afn_pre SEGS B CHAIN_WORDS_STK lyc Sc W (ms_regs ms) (ms_mem ms) mdv ch ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W (ms_mem ms)) -> cmd_ro_ok (rdW W (ms_mem ms)) ->
  rec_repA B lyc Sc (rdW W (ms_mem ms)) (e_R e) (e_O e) -> Z.of_nat (length (frames Sc)) <= 5 ->
  st_nev Sc + EV1 <= EV_MAX -> blocks_bytes Sc + LIVE_CHAIN_WORDS <= LIVE_MAX ->
  mo_ok MT Sc (XM_CHAIN_WORDS MT (e_R e)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_chain_words) (ms_regs ms) (ms_mem ms) mdv)
  (apost_baseF SEGS B CHAIN_WORDS_STK (vr_fp1 (e_O e)) (ms_regs ms) lyc Sc W (ms_mem ms) mdv EV1
    (vr_rc_post B MT (e_R e) (e_O e) m LIVE_CHAIN_WORDS (XM_CHAIN_WORDS MT (e_R e)) lyc Sc))).
{ intros ch HPRE1 H1 H2 H3 H4 H5 H6 H7.
  eapply SRr_mono.
  { exact (TCHAIN_WORDS fx lyc Sc W (ms_regs ms) (ms_mem ms) mdv ch (F + 32) (vr_ntok (e_D e))
      c (Z.of_nat (length (Verbs.line (e_D e))) + 1) tp (Verbs.Lit.verb_chain :: args) (e_R e) (e_O e)
      HPRE1 (vr18_ent_frm0 B MT e Hent) H1 Q10 ltac:(lia) Q11 HAF HTOK Hcb1 Hcb2 Hnt ltac:(lia) eq_refl
      H3 Hdecl ltac:(rewrite Hcalls; cbn; lia) H2 HVO H4 H5 H6 H7). }
  intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & Hc' & HR' & HC' & HJ' & HP' & HQ').
  exists fx', ly', S', regs', mem', md'. split; [exact Hc'|]. split; [exact HR'|]. split; [exact HC'|].
  split; [exact HJ'|]. split; [exact HP'|].
  exact (vr_cw_post (e_R e) (e_O e) args LIVE_CHAIN_WORDS (XM_CHAIN_WORDS MT (e_R e)) lyc Sc ly' S' W' regs' mem' md'
    (proj1 HJ') HQ'). }
exact (vr_call_arm_hd B MT HB MTL ROA RRO RPG RECC PROGU e W pos F q c 0x77f8 0x77c0 rk 0x8dca4 tp lyc Sc
  (ms_regs ms) (ms_mem ms) mdv k nm AF_chain_words CHAIN_WORDS_STK EV1 LIVE_CHAIN_WORDS (XM_CHAIN_WORDS MT (e_R e))
  6 EV1 m Hent Hcs Hntok Hrl Hrk Hvh Hk1 HNF HNM1 HNM HXM HLV HST0 HSTK ltac:(lia) eq_refl Hstop Hrun CALL).
Qed.

End e.
End f.
End d.
