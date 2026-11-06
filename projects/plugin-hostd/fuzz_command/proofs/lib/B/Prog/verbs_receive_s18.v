(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S18 ENV (0x8d5d0-0x8d604, 14 instructions) of the walk of verbs_receive
   on the ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v vr_s18_stmt):
   `li a0,4; bne s5,a0,0x8d68c` refuses (vr_pr at 0x8d68c) unless the message has four words; then
   `li a0,-9; ld s3,40(s1); bltu a0,s3,0x8d938; li a0,-17; bltu a0,s3,0x8d938; li a0,-25; bltu a0,s3,0x8d938`
   reloads tok = F+32 from the spill slot s1+40 and passes UBSan's three checks of tok + 8, tok + 16 and tok + 24
   (none taken: tok lies in the side-stack frame, below alloc_ceiling, vr_tok_chk); then
   `ld a0,8(s3); ld a1,16(s3); ld a2,24(s3); jal sup_worker_env; j 0x8d4cc` calls sup_worker_env(tok[1], tok[2],
   tok[3]) through its statement and leaves its text in a0 (vr_hd at 0x8d4cc). The B twin of the A walk's
   verbs_receive_s18.v (a working branch). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c arg_s_c record_c answer_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
verbs_receive_s18_kit verbs_receive_s18_call verbs_receive_s18_arm PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the listing offsets of the segment (B entry 0x8ce4c = listing AF_verbs_receive) *)
Definition S18_PC : Z := AF_verbs_receive + 0x784.   (* 0x8d5d0 li a0,4 *)
Definition S18_PR : Z := AF_verbs_receive + 0x840.   (* 0x8d68c li a0,-902 *)

(* the dispatch refuses worker_env with other than three arguments *)
Lemma vr_st_env_rej : forall D, VRR.route (Verbs.toks D) = VRR.REnv -> Verbs.toks D <> [] ->
  vr_ntok D <> 4 -> vr_st D = Verbs.SResp (-902).
Proof.
intros D Hr Hne Hn. destruct (Verbs.toks D) as [|v args] eqn:Ht; [congruence|].
rewrite (vr_st_route D v args Ht), Hr. cbn [VRR.plan_at].
unfold vr_ntok in Hn. rewrite Ht in Hn. cbn [length] in Hn.
destruct args as [|a1 [|a2 [|a3 [|a4 args]]]]; try reflexivity. cbn [length] in Hn. lia.
Qed.
Lemma vr_k1_env_rej : forall R D, VRR.route (Verbs.toks D) = VRR.REnv -> Verbs.toks D <> [] ->
  vr_ntok D <> 4 -> vr_k1 R D = 2 + EV_SUP_RESP.
Proof.
intros R D Hr Hne Hn. pose proof (vr_st_env_rej D Hr Hne Hn) as Hst.
destruct (Verbs.toks D) as [|v args] eqn:Ht; [congruence|].
pose proof (vr_route_env v args Hr) as Hv. subst v.
rewrite (vr_k1_simple R D _ args Ht) by (vm_compute; reflexivity). rewrite Hst. reflexivity.
Qed.
(* with three arguments the dispatch calls sup_worker_env(tok[1], tok[2], tok[3]) *)
Lemma vr_env_call : forall R D a1 a2 a3, Verbs.toks D = [Verbs.Lit.verb_worker_env; a1; a2; a3] ->
  vr_h R D = (sup_worker_env_m R (Some a1) (Some a2) (Some a3), false) /\ vr_k1 R D = 2 + EV_SUP_WORKER_ENV R.
Proof.
intros R D a1 a2 a3 T.
assert (St : vr_st D = Verbs.SCall (Verbs.sup_worker_env a1 a2 a3)).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. reflexivity. }
split.
- unfold vr_h. rewrite St. reflexivity.
- unfold vr_k1. rewrite St, T. reflexivity.
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
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).
(* the callee's contract at every FP state (verbs_receive_c.v:257) and the record facts of the brief *)
Hypothesis TSUP_WORKER_ENV : forall fx0 : YK11.FPState, @tsup_worker_env_spec fx0 rc SK PI B MT.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.

(* S18 with other than four words: `li a0,4; bne s5,a0,0x8d68c` to the refusal stub 0x8d68c *)
Lemma vr_s18_pr : forall e (W : world SEGS) pos F q c tp lyc Sc regsc memc mdc k nm,
  vr_ent B MT e ->
  VRR.route (Verbs.toks (e_D e)) = VRR.REnv -> Verbs.toks (e_D e) <> [] ->
  vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_rt e F q (hd 0 tp))
    (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
  vr_line B e q W memc -> vr_copy B e F c tp W memc ->
  vr_ntok (e_D e) <> 4 ->
  SRr SEGS W (cfg_at SEGS (vr_pc 0x8d5d0) regsc memc mdc) (vr_pr B MT e 0x8d68c).
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm He Hroute Hne HC HL HCP Hnt.
pose proof HC as (HJ & Hk & HM & Hnm & HFR & HRV & HSV & HSP & HENV & HREC & HnD & HPERM & HQ).
assert (RG : forall r v, In (r, v) (vr_base B e ++ vr_rl_rt e F q (hd 0 tp)) -> getr regsc (Z_to_bv 5 r) = w64 v)
  by (intros r v Hin; exact (vr_rv_in _ _ _ _ HRV Hin)).
unfold vr_base, vr_rl_rt in RG. cbn [app] in RG.
pose proof (RG 21 (vr_ntok (e_D e)) ltac:(vr_in)) as R21.
pose proof (vr_seed0 W regsc memc S18_PC) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc []))) by apply Eimg_env.
replace (cfg_at SEGS (vr_pc 0x8d5d0) regsc memc mdc)
  with (mkCfg (mkst regsc (Z_to_bv 64 (BASE + S18_PC)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, vr_pc, S18_PC; f_equal; f_equal; f_equal; lia).
(* 0x8d5d0 li a0,4 *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
vr_unchanged (@pa_segs _ cmd_listing PI) UN1 HFr. clear HF HFr HG.
assert (Hntr : 0 <= vr_ntok (e_D e) < 2 ^ 64).
{ unfold vr_ntok. pose proof (Verbs.toks_length (e_D e)). lia. }
(* 0x8d5d4 bne s5,a0,0x8d68c: taken *)
psrr_branch_pi RUNP BR HS;
  rewrite branch_ne_U, (vr_U_SOff_reg regsc [] 21 _ ltac:(lia) R21 Hntr), vr_U_lit in Hc by lia.
2: { exfalso. apply negb_false_iff, Z.eqb_eq in Hc. lia. }
paj_run_to_sh RUNTOP HS HJ S18_PR.
{ vr_awr. }
set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
vr_unchanged (@pa_segs _ cmd_listing PI) UN2 HFr. clear HF HFr HG.
pmkst HS.
apply SRr_ret.
exists (-902), (e_R e), (e_O e), pos, F, q, c, tp, lyc, Sc, (ms_regs ms0), (ms_mem ms0), mdv2, k, nm.
split; [unfold cfg_at, w64, vr_pc; f_equal; f_equal; f_equal; unfold S18_PR, AF_verbs_receive; lia|].
split; [intros _; reflexivity|].
split; [lia|].
split; [unfold vr_h; rewrite (vr_st_env_rej _ Hroute Hne Hnt); reflexivity|].
split; [exact Hne|].
split; [unfold vr_pr_ntok; cbn -[length Verbs.toks]; destruct (Verbs.toks (e_D e)); [congruence | cbn; lia]|].
assert (RS : rd_same (rdW W memc) (rdW W (ms_mem ms0))).
{ apply vr_rd_same_of. intros a Ha. rewrite (UN2 a Ha (fun x => x)). exact (UN1 a Ha (fun x => x)). }
split; [|split; [exact (vr_line_same B e q W W memc _ RS HL) | exact (vr_copy_same B e F c tp W W memc _ RS HCP)]].
apply (vr_core_same B MT e pos F _ _ _ _ _ _ _ _ k 2 _ nm VR_NM_PRE _ lyc Sc W regsc memc mdc _ _ _ HC HJ RS).
- replace (vr_rl_pr e F q c 0x8d68c (-902))
    with [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)] by reflexivity.
  unfold vr_rv, vr_base. cbn [app].
  repeat (apply Forall_cons; [cbn [fst snd]; vr_sreg HS; rewrite vr_ew_reg by lia; apply RG; vr_in |]).
  apply Forall_nil.
- rewrite (vr_k1_env_rej _ _ Hroute Hne Hnt). lia.
- unfold VR_NM_PRE, VR_NM_PR in *. lia.
Qed.

(* S18 with four words: the three UBSan checks on tok, then `ld a0,8(s3); ld a1,16(s3); ld a2,24(s3);
   jal sup_worker_env; j 0x8d4cc` (vr_hd at 0x8d4cc) *)
Lemma vr_s18_call : forall e (W : world SEGS) pos F q c tp lyc Sc regsc memc mdc k nm a1 a2 a3,
  vr_ent B MT e ->
  Verbs.toks (e_D e) = [Verbs.Lit.verb_worker_env; a1; a2; a3] ->
  vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_rt e F q (hd 0 tp))
    (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
  vr_line B e q W memc -> vr_copy B e F c tp W memc ->
  SRr SEGS W (cfg_at SEGS (vr_pc 0x8d5d0) regsc memc mdc)
    (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\ vr_hd (fx := fq) B MT e 0x8d4cc W' cf').
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm a1 a2 a3 He Ht HC HL HCP.
pose proof HC as (HJ & Hk & HM & Hnm & HFR & HRV & HSV & HSP & HENV & HREC & HnD & HPERM & HQ).
pose proof He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcalls & _).
destruct (vr_ent_stk B MT e He) as (Hs1lo & Hs1sp & Hs1al & Hsp47 & Hsp16 & HspS).
pose proof asan_consts as (CR & _).
pose proof (proj1 HJ) as HAR.
pose proof HFR as (EF & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR) as (Hf0 & Hfc & _).
{ rewrite Hfrs. left. reflexivity. }
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
assert (Hlen4 : length (Verbs.toks (e_D e)) = 4%nat) by (rewrite Ht; reflexivity).
assert (Hnt4 : vr_ntok (e_D e) = 4) by (unfold vr_ntok; rewrite Hlen4; reflexivity).
assert (HlenP : length tp = 4%nat) by (destruct HCP as (_ & (_ & HlenP & _)); rewrite HlenP, Hlen4; reflexivity).
destruct tp as [|p0 [|p1 [|p2 [|p3 [|p4 tp']]]]]; cbn in HlenP; try lia. clear HlenP.
destruct (vr_tok_blk B e F q c [p0; p1; p2; p3] lyc Sc W memc mdc 1 p1 a1 HAR HPERM HCP eq_refl
  ltac:(rewrite Ht; reflexivity)) as (_ & _ & Hlmax1 & _ & Hp1m & Hp14 & Hp1c).
destruct (vr_tok_blk B e F q c [p0; p1; p2; p3] lyc Sc W memc mdc 2 p2 a2 HAR HPERM HCP eq_refl
  ltac:(rewrite Ht; reflexivity)) as (_ & _ & Hlmax2 & _ & Hp2m & Hp24 & Hp2c).
destruct (vr_tok_blk B e F q c [p0; p1; p2; p3] lyc Sc W memc mdc 3 p3 a3 HAR HPERM HCP eq_refl
  ltac:(rewrite Ht; reflexivity)) as (_ & _ & Hlmax3 & _ & Hp3m & Hp34 & Hp3c).
assert (RG : forall r v, In (r, v) (vr_base B e ++ vr_rl_rt e F q p0) -> getr regsc (Z_to_bv 5 r) = w64 v)
  by (intros r v Hin; exact (vr_rv_in _ _ _ _ HRV Hin)).
unfold vr_base, vr_rl_rt in RG. cbn [app] in RG.
pose proof (RG 9 (vr_s1 e) ltac:(vr_in)) as R9.
pose proof (RG 21 (vr_ntok (e_D e)) ltac:(vr_in)) as R21.
pose proof (RG 22 F ltac:(vr_in)) as R22.
pose proof (vr_spill_in e W memc _ 40 (F + 32) HSP ltac:(unfold vr_sl3; vr_in)) as HSl.
pose proof (vr_seed_tk3 W regsc memc S18_PC (vr_s1 e) F p1 p2 p3 R9 R22 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) HSl
  ltac:(replace (F + 40) with (F + 32 + 8 * Z.of_nat 1) by lia; exact Hp1m)
  ltac:(replace (F + 48) with (F + 32 + 8 * Z.of_nat 2) by lia; exact Hp2m)
  ltac:(replace (F + 56) with (F + 32 + 8 * Z.of_nat 3) by lia; exact Hp3m)) as HS.
set (E := Eimg (Ereg regsc [Z_to_bv 64 p1; Z_to_bv 64 p2; Z_to_bv 64 p3])) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regsc [Z_to_bv 64 p1; Z_to_bv 64 p2; Z_to_bv 64 p3]) E)
  by apply vr_env_agree_Eimg.
assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e))) by (unfold E; rewrite vr_ew_reg by lia; exact R21).
assert (E22 : bv_unsigned (ew E 22) = F) by (unfold E; apply vr_U_reg; [lia | exact R22 | lia]).
assert (E32 : ew E 32 = Z_to_bv 64 p1) by exact (vr_ew_extra regsc _ 0 ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 p2) by exact (vr_ew_extra regsc _ 1 ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 p3) by exact (vr_ew_extra regsc _ 2 ltac:(lia)).
clearbody E.
assert (Hro : Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) [vr_rsl; vr_rtk3])
  by (apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia | apply Forall_nil]).
replace (cfg_at SEGS (vr_pc 0x8d5d0) regsc memc mdc)
  with (mkCfg (mkst regsc (Z_to_bv 64 (BASE + S18_PC)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, vr_pc, S18_PC; f_equal; f_equal; f_equal; lia).
(* 0x8d5d0 li a0,4 *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
pose proof (vr_rdeq_of_frame E [vr_rsl; vr_rtk3] (w_H W) memc (ms_mem ms) HFr Hro) as RS1. clear HF HFr HG.
(* 0x8d5d4 bne s5,a0,0x8d68c: not taken *)
psrr_branch_pi RUNP BR HS; rewrite branch_ne_U, (U_atom E 21 _ E21), vr_U_lit in Hc by lia.
1: { exfalso. apply negb_true_iff, Z.eqb_neq in Hc. lia. }
(* 0x8d5d8 li a0,-9; 0x8d5dc ld s3,40(s1) *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
pose proof (vr_rdeq_of_frame E [vr_rsl; vr_rtk3] (w_H W) (ms_mem ms) (ms_mem ms0) HFr Hro) as RS2. clear HF HFr HG.
(* 0x8d5e0 bltu a0,s3,0x8d938 (tok + 8 wraps): not taken *)
psrr_branch_pi RUNP BR HS.
1: { vr_trap E22. }
(* 0x8d5e4 li a0,-17 *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mat1 mdv2) in *. clearbody mdv3.
pose proof (vr_rdeq_of_frame E [vr_rsl; vr_rtk3] (w_H W) (ms_mem ms0) (ms_mem ms1) HFr Hro) as RS3. clear HF HFr HG.
(* 0x8d5e8 bltu a0,s3,0x8d938 (tok + 16 wraps): not taken *)
psrr_branch_pi RUNP BR HS.
1: { vr_trap E22. }
(* 0x8d5ec li a0,-25 *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv4 := with_vm_backing (m_vm_lazy mdv3) mat2 mdv3) in *. clearbody mdv4.
pose proof (vr_rdeq_of_frame E [vr_rsl; vr_rtk3] (w_H W) (ms_mem ms1) (ms_mem ms2) HFr Hro) as RS4. clear HF HFr HG.
(* 0x8d5f0 bltu a0,s3,0x8d938 (tok + 24 wraps): not taken *)
psrr_branch_pi RUNP BR HS.
1: { vr_trap E22. }
(* 0x8d5f4..0x8d5fc the three words; 0x8d600 jal sup_worker_env *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv5 := with_vm_backing (m_vm_lazy mdv4) mat3 mdv4) in *. clearbody mdv5.
pose proof (vr_rdeq_of_frame E [vr_rsl; vr_rtk3] (w_H W) (ms_mem ms2) (ms_mem ms3) HFr Hro) as RS5. clear HF HFr HG.
assert (RS : rd_same (rdW W memc) (rdW W (ms_mem ms3))).
{ intros x. rewrite (RS5 x), (RS4 x), (RS3 x), (RS2 x). exact (RS1 x). }
clear RS1 RS2 RS3 RS4 RS5.
prreg HS (1%bv : bv 5) Q1.
prreg HS (10%bv : bv 5) Q10. rewrite E32 in Q10.
prreg HS (11%bv : bv 5) Q11. rewrite E33 in Q11.
prreg HS (12%bv : bv 5) Q12. rewrite E34 in Q12.
prreg HS (19%bv : bv 5) Q19. rewrite E22 in Q19.
pose proof (vr_kept_regs E _ _ regsc [Z_to_bv 64 p1; Z_to_bv 64 p2; Z_to_bv 64 p3]
  [2; 3; 4; 8; 9; 18; 21; 22; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
rewrite (SIGP CS_sup_worker_env) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_sup_worker_env) with AF_sup_worker_env.
set (rk := [(19, F + 32); (18, q); (22, F); (27, shadow_addr F + 4)]).
assert (Hcs : vr_cs B MT e pos F q c 0x70d4 rk [p0; p1; p2; p3] lyc Sc W (ms_regs ms3) (ms_mem ms3) mdv5 k nm).
{ split; [|split; [exact (vr_line_same B e q W W memc _ RS HL)
                 | exact (vr_copy_same B e F c [p0; p1; p2; p3] W W memc _ RS HCP)]].
  apply (vr_core_same B MT e pos F _ _ _ _ _ _ _ _ k 2 _ nm VR_NM_PRE _ lyc Sc W regsc memc mdc _ _ _ HC HJ RS);
    [| lia | unfold VR_NM_PRE in *; lia].
  apply vr_rv_mk. intros r0 v Hin. apply in_app_or in Hin as [Hin|Hin].
  - unfold vr_base in Hin. cbn [In] in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
    rewrite KR by (cbn; tauto); apply RG; vr_in.
  - unfold rk in Hin. cbn [In] in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
    first [exact Q1 | exact Q19 | rewrite KR by (cbn; tauto); apply RG; vr_in]. }
pose proof (vr_copy_same B e F c [p0; p1; p2; p3] W W memc _ RS HCP) as HCP2.
destruct (vr_tok_blk B e F q c [p0; p1; p2; p3] lyc Sc W (ms_mem ms3) mdv5 1 p1 a1 (proj1 HJ) HPERM HCP2 eq_refl
  ltac:(rewrite Ht; reflexivity)) as (Hblk1 & Hstr1 & _ & Hap1 & _).
destruct (vr_tok_blk B e F q c [p0; p1; p2; p3] lyc Sc W (ms_mem ms3) mdv5 2 p2 a2 (proj1 HJ) HPERM HCP2 eq_refl
  ltac:(rewrite Ht; reflexivity)) as (Hblk2 & Hstr2 & _ & Hap2 & _).
destruct (vr_tok_blk B e F q c [p0; p1; p2; p3] lyc Sc W (ms_mem ms3) mdv5 3 p3 a3 (proj1 HJ) HPERM HCP2 eq_refl
  ltac:(rewrite Ht; reflexivity)) as (Hblk3 & Hstr3 & _ & Hap3 & _).
destruct (vr_env_call (e_R e) (e_D e) a1 a2 a3 Ht) as [Hvh Hk1].
set (m := sup_worker_env_m (e_R e) (Some a1) (Some a2) (Some a3)) in *.
assert (Ht28 : (length (snd m) <= 28)%nat).
{ unfold m, sup_worker_env_m, daemon_shape. apply vr_stub_len. exact (vr_rec_code_range B _ _ _ _ _ HREC). }
assert (Hntok : vr_hd_ntok 0x8d4cc (length (Verbs.toks (e_D e)))) by (unfold vr_hd_ntok; rewrite Hlen4; cbn; lia).
assert (Hrl : forall tq, vr_rl_hd e F q c 0x8d4cc tq = (10, tq) :: rk) by (intros tq; reflexivity).
assert (Hrk : Forall (fun rv => acallee_saved (fst rv)) rk)
  by (unfold rk; repeat (apply Forall_cons; [unfold acallee_saved; cbn [fst]; lia|]); apply Forall_nil).
(* sup_worker_env's events: record() with no spill, three arg_s copies, answer's free and two copies *)
assert (HNF : 0 <= 1 <= EV_SUP_WORKER_ENV (e_R e))
  by (unfold EV_SUP_WORKER_ENV, EV_RECORD, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC;
      rewrite (vr_spill_frees0 _ Hcalls); lia).
assert (HNM : 5 + VR_NM_PRE <= VR_NM_HD) by (unfold VR_NM_PRE, VR_NM_HD; lia).
assert (HNM1 : 0 <= 5 <= EV_SUP_WORKER_ENV (e_R e))
  by (unfold EV_SUP_WORKER_ENV, EV_RECORD, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC;
      rewrite (vr_spill_frees0 _ Hcalls); lia).
assert (HXM : XM_SUP_WORKER_ENV MT (e_R e) (Some a1) (Some a2) (Some a3) <=
  5 * mo_malloc MT VERBS_RECEIVE_REQ + 1 * mo_free MT).
{ unfold XM_SUP_WORKER_ENV, XM_RECORD, XM_ARG_S, XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC.
  rewrite (vr_spill_frees0 _ Hcalls). cbn [sarg]. fold m.
  pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length a1) + 1) 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ, LMAX in *; lia)) as M1.
  pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length a2) + 1) 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ, LMAX in *; lia)) as M2.
  pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length a3) + 1) 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ, LMAX in *; lia)) as M3.
  pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length (snd m)) + 1) 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M4.
  lia. }
assert (HLV : LIVE_SUP_WORKER_ENV (e_R e) (Some a1) (Some a2) (Some a3) <= 20 * VERBS_RECEIVE_REQ).
{ unfold LIVE_SUP_WORKER_ENV, LIVE_ARG_S, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC, VERBS_RECEIVE_REQ. cbn [sarg].
  fold m. unfold LMAX in Hlmax1, Hlmax2, Hlmax3. lia. }
assert (HV : SUP_WORKER_ENV_STK = ltac:(let v := eval vm_compute in SUP_WORKER_ENV_STK in exact v)) by reflexivity.
assert (HV2 : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
assert (HST0 : 0 <= SUP_WORKER_ENV_STK) by lia.
assert (HSTK : SUP_WORKER_ENV_STK + 208 <= VERBS_RECEIVE_STK) by lia.
assert (Hstop : vr_pc 0x8d4cc = BASE + 0x6f9c) by (unfold vr_pc, AF_verbs_receive; lia).
assert (Hrun : sym_run_toN_pi pl_tpi FUEL 0x6f9c (vr_ss_ret 0x70d4) = (vr_ss_ret 0x6f9c, PRS_running))
  by (vm_compute; reflexivity).
assert (Hp1r : 0 <= p1 < 2 ^ 64) by lia.
assert (Hp2r : 0 <= p2 < 2 ^ 64) by lia.
assert (Hp3r : 0 <= p3 < 2 ^ 64) by lia.
assert (CALL : forall ch, afn_pre SEGS B SUP_WORKER_ENV_STK lyc Sc W (ms_regs ms3) (ms_mem ms3) mdv5 ch ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W (ms_mem ms3)) -> cmd_ro_ok (rdW W (ms_mem ms3)) ->
  rec_repA B lyc Sc (rdW W (ms_mem ms3)) (e_R e) (e_O e) -> Z.of_nat (length (frames Sc)) <= 5 ->
  st_nev Sc + EV_SUP_WORKER_ENV (e_R e) <= EV_MAX ->
  blocks_bytes Sc + LIVE_SUP_WORKER_ENV (e_R e) (Some a1) (Some a2) (Some a3) <= LIVE_MAX ->
  mo_ok MT Sc (XM_SUP_WORKER_ENV MT (e_R e) (Some a1) (Some a2) (Some a3)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_sup_worker_env) (ms_regs ms3) (ms_mem ms3) mdv5)
  (apost_baseF SEGS B SUP_WORKER_ENV_STK (vr_fp1 (e_O e)) (ms_regs ms3) lyc Sc W (ms_mem ms3) mdv5
    (EV_SUP_WORKER_ENV (e_R e))
    (vr_rc_post B MT (e_R e) (e_O e) m (LIVE_SUP_WORKER_ENV (e_R e) (Some a1) (Some a2) (Some a3))
      (XM_SUP_WORKER_ENV MT (e_R e) (Some a1) (Some a2) (Some a3)) lyc Sc))).
{ intros ch HPRE1 H1 H2 H3 H4 H5 H6 H7.
  assert (H4' : Z.of_nat (length (frames Sc)) <= 8) by lia.
  exact (TSUP_WORKER_ENV fx lyc Sc W (ms_regs ms3) (ms_mem ms3) mdv5 ch p1 p2 p3 (Some a1) (Some a2) (Some a3)
    (e_R e) (e_O e) HPRE1 (vr18_ent_frm0 B MT e He) H1 H2 Q10 Hp1r Q11 Hp2r Q12 Hp3r
    (ex_intro _ a1 (conj eq_refl (conj Hblk1 (conj Hstr1 (conj Hlmax1 Hap1)))))
    (ex_intro _ a2 (conj eq_refl (conj Hblk2 (conj Hstr2 (conj Hlmax2 Hap2)))))
    (ex_intro _ a3 (conj eq_refl (conj Hblk3 (conj Hstr3 (conj Hlmax3 Hap3)))))
    H3 H4' H5 H6 H7). }
exact (vr_call_arm_hd B MT HB MTL ROA RRO RPG RECC PROGU e W pos F q c 0x70d4 0x6f9c rk 0x8d4cc [p0; p1; p2; p3] lyc Sc
  (ms_regs ms3) (ms_mem ms3) mdv5 k nm AF_sup_worker_env SUP_WORKER_ENV_STK (EV_SUP_WORKER_ENV (e_R e))
  (LIVE_SUP_WORKER_ENV (e_R e) (Some a1) (Some a2) (Some a3)) (XM_SUP_WORKER_ENV MT (e_R e) (Some a1) (Some a2) (Some a3))
  5 1 m He Hcs Hntok Hrl Hrk Hvh Hk1 HNF HNM1 HNM HXM HLV HST0 HSTK ltac:(lia) eq_refl Hstop Hrun CALL).
Qed.

Lemma vr_s18 : vr_s18_stmt B MT.
Proof.
intros e W cf Hent Hrt.
destruct Hrt as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hne & Hcore & Hline & Hcopy).
change (vr_pc (vr_route_pc VRR.REnv)) with (vr_pc 0x8d5d0).
destruct (Z.eq_dec (vr_ntok (e_D e)) 4) as [H4 | H4].
- unfold vr_ntok in H4.
  destruct (Verbs.toks (e_D e)) as [|v args] eqn:Ht; [congruence|].
  pose proof (vr_route_env v args Hroute) as Hv. subst v.
  destruct args as [|a1 [|a2 [|a3 [|a4 args]]]]; cbn [length] in H4; [lia | lia | lia | | lia].
  eapply SRr_mono; [exact (vr_s18_call e W pos F q c tp lyc Sc regsc memc mdc k nm a1 a2 a3 Hent Ht Hcore Hline Hcopy)|].
  intros W' c' _ (fq & Hr & H). exists fq. split; [exact Hr | right; exact H].
- eapply SRr_mono; [exact (vr_s18_pr e W pos F q c tp lyc Sc regsc memc mdc k nm Hent Hroute Hne Hcore Hline Hcopy H4)|].
  intros W' c' _ H. exists fx. split; [apply fxrel_refl | left; exact H].
Qed.

End e.
End f.
End d.
