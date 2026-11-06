(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S22 PINACC (B 0x8d66c-0x8d688, 7 instructions) of the walk of
   verbs_receive on the ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v
   vr_s22_stmt): `li a0,2; bne s5,a0,0x8d68c` refuses (vr_pr at 0x8d68c) unless the message has two words; then
   `ld s3,40(s1)` reloads tok from the spill slot (B keeps it there, where A held it in s6), the UBSan site
   0x8d67c (`bltu -9,s3`, tok + 16 wraps) is refuted from the side-stack frame's bounds, and
   `ld a0,8(s3); jal sup_pin_accept; j 0x8d4cc` calls sup_pin_accept(tok[1]) through its statement and leaves its
   text in a0 (vr_hd at 0x8d4cc). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c arg_s_c record_c answer_c hand_back_c rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_live.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s21_kit verbs_receive_s21_arm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the listing offsets of the segment (B pc - 0x86530) *)
Definition S22_PC : Z := AF_verbs_receive + 0x820.   (* 0x8d66c li a0,2 *)
Definition S22_PR : Z := AF_verbs_receive + 0x840.   (* 0x8d68c li a0,-902 *)

(* the dispatch refuses pin_accept with other than one argument *)
Lemma vr_st_pinacc_rej : forall D, VRR.route (Verbs.toks D) = VRR.RPinacc -> Verbs.toks D <> [] ->
  vr_ntok D <> 2 -> vr_st D = Verbs.SResp (-902).
Proof.
intros D Hr Hne Hn. destruct (Verbs.toks D) as [|v args] eqn:Ht; [congruence|].
rewrite (vr_st_route D v args Ht), Hr. cbn [VRR.plan_at].
unfold vr_ntok in Hn. rewrite Ht in Hn. cbn [length] in Hn.
destruct args as [|a [|b args]]; try reflexivity. cbn [length] in Hn. lia.
Qed.
Lemma vr_k1_pinacc_rej : forall R D, VRR.route (Verbs.toks D) = VRR.RPinacc -> Verbs.toks D <> [] ->
  vr_ntok D <> 2 -> vr_k1 R D = 2 + EV_SUP_RESP.
Proof.
intros R D Hr Hne Hn. pose proof (vr_st_pinacc_rej D Hr Hne Hn) as Hst.
destruct (Verbs.toks D) as [|v args] eqn:Ht; [congruence|].
pose proof (vr_route_pinacc v args Hr) as Hv. subst v.
rewrite (vr_k1_simple R D _ args Ht) by (vm_compute; reflexivity). rewrite Hst. reflexivity.
Qed.
(* with one argument the dispatch calls sup_pin_accept(tok[1]) *)
Lemma vr_pinacc_call : forall R D a, Verbs.toks D = [Verbs.Lit.verb_pin_accept; a] ->
  vr_h R D = (sup_pin_accept_m R (Some a), false) /\ vr_k1 R D = 2 + EV_SUP_PIN_ACCEPT R.
Proof.
intros R D a T.
assert (St : vr_st D = Verbs.SCall (Verbs.sup_pin_accept a)).
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
(* the callee's contract at every FP state (verbs_receive_c.v) and the record facts of the brief *)
Hypothesis TSUP_PIN_ACCEPT : forall fx0 : YK11.FPState, @tsup_pin_accept_spec fx0 rc SK PI B MT.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.

(* S22 with other than two words: the refusal stub 0x8d68c *)
Lemma vr_s22_pr : forall e (W : world SEGS) pos F q c tp lyc Sc regsc memc mdc k nm,
  vr_ent B MT e ->
  VRR.route (Verbs.toks (e_D e)) = VRR.RPinacc -> Verbs.toks (e_D e) <> [] ->
  vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_rt e F q (hd 0 tp))
    (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
  vr_line B e q W memc -> vr_copy B e F c tp W memc ->
  vr_ntok (e_D e) <> 2 ->
  SRr SEGS W (cfg_at SEGS (vr_pc 0x8d66c) regsc memc mdc) (vr_pr B MT e 0x8d68c).
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm He Hroute Hne HC HL HCP Hnt.
pose proof HC as (HJ & Hk & HM & Hnm & HFR & HRV & HSV & HSP & HENV & HREC & HnD & HPERM & HQ).
destruct (vr_ent_stk B MT e He) as (Hs1lo & Hs1sp & Hs1al & Hsp47 & Hsp16 & HspS).
pose proof asan_consts as (CR & _).
assert (RG : forall r v, In (r, v) (vr_base B e ++ vr_rl_rt e F q (hd 0 tp)) -> getr regsc (Z_to_bv 5 r) = w64 v)
  by (intros r v Hin; exact (vr_rv_in _ _ _ _ HRV Hin)).
unfold vr_base, vr_rl_rt in RG. cbn [app] in RG.
pose proof (RG 21 (vr_ntok (e_D e)) ltac:(vr_in)) as R21.
pose proof (proj1 HJ) as HAR.
assert (Hntr : 0 <= vr_ntok (e_D e) < 2 ^ 64).
{ unfold vr_ntok. pose proof (Verbs.toks_length (e_D e)). lia. }
pose proof (vr_seed0 W regsc memc S22_PC) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc []))) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regsc []) (Eimg (Ereg regsc []))) by apply vr_env_agree_Eimg.
replace (cfg_at SEGS (vr_pc 0x8d66c) regsc memc mdc)
  with (mkCfg (mkst regsc (Z_to_bv 64 (BASE + S22_PC)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, vr_pc, S22_PC; f_equal; f_equal; f_equal; lia).
(* 0x8d66c li a0,2 *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
vr_unchanged (@pa_segs _ cmd_listing PI) UN1 HFr. clear HF HFr HG.
(* 0x8d670 bne s5,a0,0x8d68c: taken *)
psrr_branch_pi RUNP BR HS;
  rewrite branch_ne_U, (vr_U_SOff_reg regsc [] 21 _ ltac:(lia) R21 Hntr), vr_U_lit in Hc by lia.
2: { exfalso. apply negb_false_iff, Z.eqb_eq in Hc. lia. }
paj_run_to_sh RUNTOP HS HJ S22_PR.
{ vr_awr. }
vr_unchanged (@pa_segs _ cmd_listing PI) UN2 HFr. clear HF HFr HG.
pose proof (vr_kept_regs _ _ _ regsc [] [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] HS HAE
  ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
apply SRr_ret.
exists (-902), (e_R e), (e_O e), pos, F, q, c, tp, lyc, Sc, (ms_regs ms0), (ms_mem ms0). eexists. exists k, nm.
split; [unfold cfg_at, w64, vr_pc; f_equal; f_equal; f_equal; unfold S22_PR, AF_verbs_receive; lia|].
split; [intros _; reflexivity|].
split; [lia|].
split; [unfold vr_h; rewrite (vr_st_pinacc_rej _ Hroute Hne Hnt); reflexivity|].
split; [exact Hne|].
split; [unfold vr_pr_ntok; cbn -[length Verbs.toks]; destruct (Verbs.toks (e_D e)); [congruence | cbn; lia]|].
assert (RS : rd_same (rdW W memc) (rdW W (ms_mem ms0))).
{ apply vr_rd_same_of. intros a Ha. rewrite (UN2 a Ha (fun x => x)). exact (UN1 a Ha (fun x => x)). }
split; [|split; [exact (vr_line_same B e q W W memc _ RS HL) | exact (vr_copy_same B e F c tp W W memc _ RS HCP)]].
apply (vr_core_same B MT e pos F _ _ _ _ _ _ _ _ k 2 _ nm VR_NM_PRE _ lyc Sc W regsc memc mdc _ _ _ HC HJ RS).
- replace (vr_rl_pr e F q c 0x8d68c (-902))
    with [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)] by reflexivity.
  apply vr_rv_mk. intros r0 v0 Hin. cbn [In] in Hin.
  destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]]]; injection E1 as <- <-;
    rewrite KR by (cbn; tauto); apply RG; vr_in.
- rewrite (vr_k1_pinacc_rej _ _ Hroute Hne Hnt). lia.
- unfold VR_NM_PRE, VR_NM_PR in *. lia.
Qed.

(* S22 with two words: `ld s3,40(s1); ld a0,8(s3); jal sup_pin_accept; j 0x8d4cc` (vr_hd at 0x8d4cc) *)
Lemma vr_s22_call : forall e (W : world SEGS) pos F q c tp lyc Sc regsc memc mdc k nm a,
  vr_ent B MT e ->
  Verbs.toks (e_D e) = [Verbs.Lit.verb_pin_accept; a] ->
  vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_rt e F q (hd 0 tp))
    (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
  vr_line B e q W memc -> vr_copy B e F c tp W memc ->
  SRr SEGS W (cfg_at SEGS (vr_pc 0x8d66c) regsc memc mdc)
    (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\ vr_hd (fx := fq) B MT e 0x8d4cc W' cf').
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm a He Ht HC HL HCP.
pose proof HC as (HJ & Hk & HM & Hnm & HFR & HRV & HSV & HSP & HENV & HREC & HnD & HPERM & HQ).
pose proof He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcalls & _).
destruct (vr_ent_stk B MT e He) as (Hs1lo & Hs1sp & Hs1al & Hsp47 & Hsp16 & HspS).
pose proof asan_consts as (CR & _).
pose proof (proj1 HJ) as HAR.
pose proof HFR as (EF & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
assert (HinF : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR HinF) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
assert (Hlen2 : length (Verbs.toks (e_D e)) = 2%nat) by (rewrite Ht; reflexivity).
assert (Hnt2 : vr_ntok (e_D e) = 2) by (unfold vr_ntok; rewrite Hlen2; reflexivity).
assert (HlenP : length tp = 2%nat) by (destruct HCP as (_ & (_ & HlenP & _)); rewrite HlenP, Hlen2; reflexivity).
destruct tp as [|p0 [|p1 [|p2 tp']]]; cbn in HlenP; try lia. clear HlenP.
destruct (vr_tok_blk B e F q c [p0; p1] lyc Sc W memc mdc 1 p1 a HAR HPERM HCP eq_refl ltac:(rewrite Ht; reflexivity))
  as (Hblk & Hstr & Hlmax & Hap & Hp1m & Hp14 & Hp1c).
assert (RG : forall r v, In (r, v) (vr_base B e ++ vr_rl_rt e F q p0) -> getr regsc (Z_to_bv 5 r) = w64 v)
  by (intros r v Hin; exact (vr_rv_in _ _ _ _ HRV Hin)).
unfold vr_base, vr_rl_rt in RG. cbn [app hd] in RG.
pose proof (RG 9 (vr_s1 e) ltac:(vr_in)) as R9.
pose proof (RG 21 (vr_ntok (e_D e)) ltac:(vr_in)) as R21.
pose proof (vr_spill_in e W memc _ 40 (F + 32) HSP ltac:(unfold vr_sl3; vr_in)) as HStok.
pose proof (vr_seed_t1 W regsc memc S22_PC (vr_s1 e) (F + 32) p1 R9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  HStok ltac:(replace (F + 32 + 8) with (F + 32 + 8 * Z.of_nat 1) by lia; exact Hp1m)) as HS.
set (E := Eimg (Ereg regsc [Z_to_bv 64 (F + 32); Z_to_bv 64 p1])) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regsc [Z_to_bv 64 (F + 32); Z_to_bv 64 p1]) E) by apply vr_env_agree_Eimg.
assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e))) by (unfold E; rewrite vr_ew_reg by lia; exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (F + 32)) by exact (vr_ew_extra regsc _ 0 ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 p1) by exact (vr_ew_extra regsc _ 1 ltac:(lia)).
clearbody E.
assert (Hntr : 0 <= vr_ntok (e_D e) < 2 ^ 64) by (rewrite Hnt2; lia).
replace (cfg_at SEGS (vr_pc 0x8d66c) regsc memc mdc)
  with (mkCfg (mkst regsc (Z_to_bv 64 (BASE + S22_PC)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, vr_pc, S22_PC; f_equal; f_equal; f_equal; lia).
(* 0x8d66c li a0,2 *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
vr_unchanged (@pa_segs _ cmd_listing PI) UN1 HFr. clear HF HFr HG.
(* 0x8d670 bne s5,a0,0x8d68c: not taken *)
psrr_branch_pi RUNP BR HS; rewrite branch_ne_U, (U_atom E 21 _ E21) in Hc by lia;
  change (U E (SLit 2)) with 2 in Hc.
1: { exfalso. apply negb_true_iff, Z.eqb_neq in Hc. lia. }
clear Hc.
(* 0x8d674 li a0,-9; 0x8d678 ld s3,40(s1) *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
vr_unchanged (@pa_segs _ cmd_listing PI) UN2 HFr. clear HF HFr HG.
(* 0x8d67c bltu a0,s3,0x8d938 (UBSan: tok + 16 wraps): not taken, tok = F + 32 is a side-stack address *)
psrr_branch_pi RUNP BR HS.
1: { exfalso. rewrite branch_ltu_U, (U_atom E 32 _ E32) in Hc by lia.
     rewrite U_SLit in Hc. unfold zcanon, M64 in Hc. apply Z.ltb_lt in Hc. revert Hc.
     lazymatch goal with |- ?K mod 2 ^ 64 < _ -> False =>
       let v := eval vm_compute in (K mod 2 ^ 64) in change (K mod 2 ^ 64) with v end.
     lia. }
clear Hc.
(* 0x8d680 ld a0,8(s3); 0x8d684 jal sup_pin_accept *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mat1 mdv2) in *. clearbody mdv3.
vr_unchanged (@pa_segs _ cmd_listing PI) UN3 HFr. clear HF HFr HG.
assert (RS : rd_same (rdW W memc) (rdW W (ms_mem ms1))).
{ apply vr_rd_same_of. intros x Hx. rewrite (UN3 x Hx (fun y => y)).
  rewrite (UN2 x Hx (fun y => y)). exact (UN1 x Hx (fun y => y)). }
prreg HS (1%bv : bv 5) Q1.
prreg HS (10%bv : bv 5) Q10. rewrite E33 in Q10.
prreg HS (19%bv : bv 5) Q19. rewrite E32 in Q19.
pose proof (vr_kept_regs E _ _ regsc [Z_to_bv 64 (F + 32); Z_to_bv 64 p1]
  [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
rewrite (SIGP CS_sup_pin_accept) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_sup_pin_accept) with AF_sup_pin_accept.
set (rk := [(19, F + 32); (18, q); (22, F); (27, shadow_addr F + 4)]).
assert (Hcs : vr_cs B MT e pos F q c 0x7158 rk [p0; p1] lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv3 k nm).
{ split; [|split; [exact (vr_line_same B e q W W memc _ RS HL) | exact (vr_copy_same B e F c [p0; p1] W W memc _ RS HCP)]].
  apply (vr_core_same B MT e pos F _ _ _ _ _ _ _ _ k 2 _ nm VR_NM_PRE _ lyc Sc W regsc memc mdc _ _ _ HC HJ RS);
    [| lia | unfold VR_NM_PRE in *; lia].
  apply vr_rv_mk. intros r0 v0 Hin. apply in_app_or in Hin as [Hin|Hin].
  - unfold vr_base in Hin. cbn [In] in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
    rewrite KR by (cbn; tauto); apply RG; vr_in.
  - unfold rk in Hin. cbn [In] in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
    first [exact Q1 | exact Q19 | rewrite KR by (cbn; tauto); apply RG; vr_in]. }
destruct (vr_tok_blk B e F q c [p0; p1] lyc Sc W (ms_mem ms1) mdv3 1 p1 a (proj1 HJ) HPERM
  (vr_copy_same B e F c [p0; p1] W W memc _ RS HCP) eq_refl ltac:(rewrite Ht; reflexivity))
  as (Hblk2 & Hstr2 & _ & Hap2 & _).
destruct (vr_pinacc_call (e_R e) (e_D e) a Ht) as [Hvh Hk1].
assert (Ht28 : (length (snd (sup_pin_accept_m (e_R e) (Some a))) <= 28)%nat).
{ unfold sup_pin_accept_m, daemon_shape. apply vr_stub_len. exact (vr_rec_code_range B _ _ _ _ _ HREC). }
assert (Hntok : vr_hd_ntok 0x8d4cc (length (Verbs.toks (e_D e)))) by (unfold vr_hd_ntok; rewrite Hlen2; cbn; lia).
assert (Hrl : forall tq, vr_rl_hd e F q c 0x8d4cc tq = (10, tq) :: rk) by (intros tq; reflexivity).
assert (Hrk : Forall (fun rv => acallee_saved (fst rv)) rk)
  by (unfold rk; repeat (apply Forall_cons; [unfold acallee_saved; cbn [fst]; lia|]); apply Forall_nil).
assert (HEVC : EV_SUP_PIN_ACCEPT (e_R e) = 4)
  by (unfold EV_SUP_PIN_ACCEPT, EV_RECORD, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC;
      rewrite (vr_spill_frees0 _ Hcalls); reflexivity).
assert (HNF : 0 <= 1 <= EV_SUP_PIN_ACCEPT (e_R e)) by lia.
assert (HNM : 3 + VR_NM_PRE <= VR_NM_HD) by (unfold VR_NM_PRE, VR_NM_HD; lia).
assert (HNM1 : 0 <= 3 <= EV_SUP_PIN_ACCEPT (e_R e)) by lia.
assert (HXM : XM_SUP_PIN_ACCEPT MT (e_R e) (Some a) <= 3 * mo_malloc MT VERBS_RECEIVE_REQ + 1 * mo_free MT).
{ unfold XM_SUP_PIN_ACCEPT, XM_RECORD, XM_ARG_S, XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC.
  rewrite (vr_spill_frees0 _ Hcalls). cbn [sarg].
  pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length a) + 1) 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ, LMAX in *; lia)) as M1.
  pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length (snd (sup_pin_accept_m (e_R e) (Some a)))) + 1) 1)
    VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M2.
  lia. }
assert (HLV : LIVE_SUP_PIN_ACCEPT (e_R e) (Some a) <= 20 * VERBS_RECEIVE_REQ).
{ unfold LIVE_SUP_PIN_ACCEPT, LIVE_ARG_S, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC, VERBS_RECEIVE_REQ. cbn [sarg].
  unfold LMAX in Hlmax. lia. }
assert (HV : SUP_PIN_ACCEPT_STK = ltac:(let v := eval vm_compute in SUP_PIN_ACCEPT_STK in exact v)) by reflexivity.
assert (HV2 : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
assert (HST0 : 0 <= SUP_PIN_ACCEPT_STK) by lia.
assert (HSTK : SUP_PIN_ACCEPT_STK + 208 <= VERBS_RECEIVE_STK) by lia.
assert (Hstop : vr_pc 0x8d4cc = BASE + 0x6f9c) by (unfold vr_pc, AF_verbs_receive; lia).
assert (Hrun : sym_run_toN_pi pl_tpi FUEL 0x6f9c (vr_ss_ret 0x7158) = (vr_ss_ret 0x6f9c, PRS_running))
  by (vm_compute; reflexivity).
assert (Hp1r : 0 <= p1 < 2 ^ 64) by lia.
assert (CALL : forall ch, afn_pre SEGS B SUP_PIN_ACCEPT_STK lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv3 ch ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W (ms_mem ms1)) -> cmd_ro_ok (rdW W (ms_mem ms1)) ->
  rec_repA B lyc Sc (rdW W (ms_mem ms1)) (e_R e) (e_O e) -> Z.of_nat (length (frames Sc)) <= 5 ->
  st_nev Sc + EV_SUP_PIN_ACCEPT (e_R e) <= EV_MAX ->
  blocks_bytes Sc + LIVE_SUP_PIN_ACCEPT (e_R e) (Some a) <= LIVE_MAX ->
  mo_ok MT Sc (XM_SUP_PIN_ACCEPT MT (e_R e) (Some a)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_sup_pin_accept) (ms_regs ms1) (ms_mem ms1) mdv3)
  (apost_baseF SEGS B SUP_PIN_ACCEPT_STK (vr_fp1 (e_O e)) (ms_regs ms1) lyc Sc W (ms_mem ms1) mdv3
    (EV_SUP_PIN_ACCEPT (e_R e))
    (vr_rc_post B MT (e_R e) (e_O e) (sup_pin_accept_m (e_R e) (Some a)) (LIVE_SUP_PIN_ACCEPT (e_R e) (Some a))
      (XM_SUP_PIN_ACCEPT MT (e_R e) (Some a)) lyc Sc))).
{ intros ch HPRE1 H1 H2 H3 H4 H5 H6 H7.
  assert (H4' : Z.of_nat (length (frames Sc)) <= 8) by lia.
  exact (TSUP_PIN_ACCEPT fx lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv3 ch p1 (Some a) (e_R e) (e_O e)
    HPRE1 (vr18_ent_frm0 B MT e He) H1 H2 Q10 Hp1r
    (ex_intro _ a (conj eq_refl (conj Hblk2 (conj Hstr2 (conj Hlmax Hap2))))) H3 H4' H5 H6 H7). }
exact (vr_call_arm_hd B MT HB MTL ROA RRO RPG RECC PROGU e W pos F q c 0x7158 0x6f9c rk 0x8d4cc [p0; p1] lyc Sc
  (ms_regs ms1) (ms_mem ms1) mdv3 k nm AF_sup_pin_accept SUP_PIN_ACCEPT_STK (EV_SUP_PIN_ACCEPT (e_R e))
  (LIVE_SUP_PIN_ACCEPT (e_R e) (Some a)) (XM_SUP_PIN_ACCEPT MT (e_R e) (Some a)) 3 1 (sup_pin_accept_m (e_R e) (Some a))
  He Hcs Hntok Hrl Hrk Hvh Hk1 HNF HNM1 HNM HXM HLV HST0 HSTK ltac:(lia) eq_refl Hstop Hrun CALL).
Qed.

Lemma vr_s22 : vr_s22_stmt B MT.
Proof.
intros e W cf Hent Hrt.
destruct Hrt as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hne & Hcore & Hline & Hcopy).
change (vr_pc (vr_route_pc VRR.RPinacc)) with (vr_pc 0x8d66c).
destruct (Z.eq_dec (vr_ntok (e_D e)) 2) as [H2 | H2].
- unfold vr_ntok in H2.
  destruct (Verbs.toks (e_D e)) as [|v args] eqn:Ht; [congruence|].
  pose proof (vr_route_pinacc v args Hroute) as Hv. subst v.
  destruct args as [|a [|b args]]; cbn [length] in H2; [lia | | lia].
  eapply SRr_mono; [exact (vr_s22_call e W pos F q c tp lyc Sc regsc memc mdc k nm a Hent Ht Hcore Hline Hcopy)|].
  intros W' c' _ (fq & Hr & H). exists fq. split; [exact Hr | right; exact H].
- eapply SRr_mono; [exact (vr_s22_pr e W pos F q c tp lyc Sc regsc memc mdc k nm Hent Hroute Hne Hcore Hline Hcopy H2)|].
  intros W' c' _ H. exists fx. split; [apply fxrel_refl | left; exact H].
Qed.

End e.
End f.
End d.
