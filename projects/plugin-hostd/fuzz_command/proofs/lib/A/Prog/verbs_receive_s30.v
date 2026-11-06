(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S30 (JOIN) of the walk of verbs_receive on the ASan build of
   plugin-hostd/fuzz_command (lib/A/Prog/verbs_receive_iface.v, vr_s30_stmt): the seven join entries J1 (0x8d9b4),
   JA (0x8da34/40/44) and JB (0x8dad4/e0/e4), each a short register-move prologue, the call reply(fd, text) through
   lib/A/Prog/verbs_receive_s30_kit.v vr_join_call (TREPLY under cl_callS_wide), and the move to the next boundary:
   J1 jumps to 0x8db50 (vr_af); JA tests the number of words (one: 0x8db50, vr_af; more: 0x8daf4, vr_ar); JB
   reloads s9 and falls into 0x8daf4 (vr_ar). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import socket_send_c reply_c sup_resp_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import arg_i_c sup_after_reply_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_s30_m verbs_receive_s30_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* a list membership of concrete entries *)
Ltac vr30_inl := cbn; repeat first [left; reflexivity | right].
(* a register of a boundary list: a fact of the run (assumption), or a register the run kept (KR) whose value the
   boundary before the run lists (HR) *)
Ltac vr30_reg KR HR :=
  first
  [ assumption
  | lazymatch goal with |- getr _ (Z_to_bv 5 ?r) = w64 ?v =>
      rewrite (KR r ltac:(vr30_inl)); apply (vr_rv_get _ _ r v HR); unfold vr_base; vr30_inl end ].
Ltac vr30_regs KR HR :=
  apply vr_rv_intro; intros r v Hin; unfold vr_base in Hin; cbn [app In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; vr30_reg KR HR |]); contradiction.

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
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis TREPLY : forall fx0 : YK11.FPState, treply_spec (fx := fx0) B MT.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let SEED := vr_seed_hd B MT RRO RPG RECC PROGU ROA TREPLY HB MTL SIGP.
Let MOVE := vr_core_move B MT RRO RPG RECC PROGU ROA.
Let JCALL := vr_join_call B MT RRO RPG RECC PROGU ROA TREPLY HB MTL SIGP.
Let JMP := vr_jmp B MT RRO RPG RECC PROGU ROA TREPLY HB MTL SIGP.

(* J1 0x8d9b4: ld s3,56(s1); mv a0,s8; jal reply; j 0x8db50 -> vr_af *)
Lemma vr_s30_j1 : vr_seg B MT (vr_athd B MT 0x8d9b4) (vr_af B MT).
Proof.
intros e W cf He Hhd.
destruct Hhd as (tq & O1 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & Hcf & Hntok & Htq4 & Hstr
  & Hcore & Hline & Hcopy).
unfold vr_hd_ntok in Hntok. rewrite Z.eqb_refl in Hntok.
assert (Haft : vr_aft (e_D e) = None) by exact (vrm_after_one atoi_a (e_D e) Hntok).
assert (Erl : vr_rl_hd e F q c 0x8d9b4 tq = [(11, tq); (18, q); (20, F); (25, shadow_addr F); (27, shadow_addr F + 4)])
  by reflexivity.
rewrite Erl in Hcore.
pose proof Hcore as (HJ & _ & _ & _ & _ & HR & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
subst cf. unfold cfg_at, w64.
replace (vr_pc 0x8d9b4) with (BASE + 29904) by (unfold vr_pc, AF_verbs_receive; lia).
pose proof (SEED e pos F q c _ _ _ _ _ _ _ k _ nm _ lyc Sc W regsc memc mdc 29904 Hcore
  ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) (incl_refl _)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia)) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c))))) by apply Eimg_env.
pose proof (vr_env_agree regsc (vr_vals (vr_sl3 F q c))) as HAE.
assert (E38 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 38 = w64 c)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
remember (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) as E eqn:HE. clear HE.
(* ld s3,56(s1); mv a0,s8; jal reply *)
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
assert (Eq : forall a, rdW W (ms_mem ms) a = rdW W memc a).
{ apply (vr_rdW_frame E _ W memc (ms_mem ms) HFr). apply vr_no_wrange. apply vr_ss_ro. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (19%bv : bv 5) Q19. rewrite ?E38 in Q19.
pose proof (vr_kept_regs E _ _ regsc _ [2; 3; 4; 8; 9; 11; 18; 20; 25; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
assert (Hrv : vr_rv (ms_regs ms) (vr_base B e ++ (vr_rl_af F q c ++ [(11, tq)]))) by (unfold vr_rl_af; vr30_regs KR HR).
pose proof (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ _ O1 (vr_qv e) k _ nm _ lyc Sc W regsc memc mdc
  (vr_sl3 F q c) _ (vr_k1 (e_R e) (e_D e)) VR_NM_HD (ms_regs ms) (ms_mem ms) mdv Hcore HJ Eq Hrv
  (incl_refl _) (Z.le_refl _) (Z.le_refl _)) as Hcore2.
assert (Hk3 : vr_k3 (e_R e) (e_D e) = vr_k2 (e_R e) (e_D e)) by (unfold vr_k3; rewrite Haft; cbn [ev_after]; lia).
eapply SRr_bind.
{ apply (JCALL e W (ms_regs ms) (ms_mem ms) mdv pos F q c tp tq (vr_sl3 F q c) (vr_rl_af F q c) O1 (vr_qv e) k nm lyc Sc
    29916 (vr_k3 (e_R e) (e_D e)) VR_NM_AF He Hcore2 (vr_line_eq B e q W memc (ms_mem ms) Eq Hline)
    (vr_copy_eq B e F c tp W memc (ms_mem ms) Eq Hcopy) Q1).
  - lia.
  - reflexivity.
  - unfold vr_rl_af. repeat (apply Forall_cons; [unfold acallee_saved; cbn [fst]; lia|]). apply Forall_nil.
  - unfold vr_sl3. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil.
  - exact Htq4.
  - exact (vr_astr_eq _ _ tq _ Eq Hstr).
  - rewrite Hk3. lia.
  - unfold VR_NM_AR, VR_NM_AF. lia. }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & O2 & -> & HPres & Hcore3 & Hline3 & Hcopy3).
pose proof Hcore3 as (HJ3 & _ & _ & _ & _ & HR3 & _).
(* j 0x8db50 *)
apply (JMP 29916 30316 ltac:(vm_compute; reflexivity) W2 regs2 mem2 md2 _ _ _ _ _ _ _ _ _ _ ly2 S2 _ HJ3).
intros regs3 mem3 md3 Er Em HJ4.
exists O2, pos, F, q, c, ly2, S2, regs3, mem3, md3, (k + EV_REPLY), (nm + 1).
split; [unfold cfg_at, w64; replace (vr_pc 0x8db50) with (BASE + 30316) by (unfold vr_pc, AF_verbs_receive; lia);
  reflexivity|].
split; [|split; [exact (proj1 Hline3) | exact (proj1 Hcopy3)]].
replace (vr_R3 (e_R e) (e_D e)) with (vr_R2 (e_R e) (e_D e)) by (unfold vr_R3; rewrite Haft; reflexivity).
apply (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) (vr_rl_af F q c) _ O2 (vr_qv e) (k + EV_REPLY) (vr_k3 (e_R e) (e_D e))
  (nm + 1) VR_NM_AF ly2 S2 W2 regs2 mem2 md2 [(48, F)] (vr_rl_af F q c) (vr_k3 (e_R e) (e_D e)) VR_NM_AF regs3 mem3 md3
  Hcore3 HJ4 Em).
- unfold vr_rv in HR3 |- *. rewrite Forall_forall in HR3 |- *. intros rv Hrv'. rewrite Er. exact (HR3 rv Hrv').
- intros x [<- | []]. unfold vr_sl3. vr30_inl.
- lia.
- lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   JA: the registers at the call of reply (s10 = the text moved into a1), the call, then at 0x8da50
   `li a0,1; bne s5,a0,0x8daf4; j 0x8db50` *)
Definition vr30_rl_ja (e : vrE) (F q c : Z) : list (Z * Z) :=
[(18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F); (27, shadow_addr F + 4)].

Lemma vr30_ja_tail : forall e (W : world SEGS) (regs : bvmap 5 word) mem md pos F q c tp tq O1 k nm lyc Sc,
vr_ent B MT e -> (1 <= length (Verbs.toks (e_D e)))%nat ->
vr_core B MT e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  (vr30_rl_ja e F q c ++ [(11, tq)]) (vr_R1 (e_R e) (e_D e)) O1 (vr_qv e) k (vr_k1 (e_R e) (e_D e)) nm VR_NM_HD
  lyc Sc W regs mem md ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
getr regs 1 = Z_to_bv 64 (BASE + 30060) ->
4096 <= tq -> astr_atR (rdW W mem) tq (vr_x (e_R e) (e_D e)) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (pa_sigma CS_reply)) mem (seg_rom SEGS)) md) (vr_or (vr_ar B MT) (vr_af B MT) e).
Proof.
intros e W regs mem md pos F q c tp tq O1 k nm lyc Sc He Hnt1 Hcore Hline Hcopy Hra Htq4 Hstr.
assert (Hnt : 0 <= vr_ntok (e_D e) <= 64).
{ unfold vr_ntok, Verbs.toks, Verbs.line_words_max. rewrite length_firstn. lia. }
eapply SRr_bind.
{ apply (JCALL e W regs mem md pos F q c tp tq (vr_sl3 F q c) (vr30_rl_ja e F q c) O1 (vr_qv e) k nm lyc Sc
    30060 (vr_k2 (e_R e) (e_D e)) VR_NM_AR He Hcore Hline Hcopy Hra).
  - lia.
  - reflexivity.
  - unfold vr30_rl_ja. repeat (apply Forall_cons; [unfold acallee_saved; cbn [fst]; lia|]). apply Forall_nil.
  - unfold vr_sl3. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil.
  - exact Htq4.
  - exact Hstr.
  - lia.
  - lia. }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & O2 & -> & HPres & Hcore3 & Hline3 & Hcopy3).
pose proof Hcore3 as (HJ & _ & _ & _ & _ & HR & _).
unfold vr30_rl_ja in HR.
pose proof (vr_seed0 W2 regs2 mem2 30060) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
pose proof (vr_env_agree regs2 []) as HAE.
assert (E21 : ew (Eimg (Ereg regs2 [])) 21 = Z_to_bv 64 (vr_ntok (e_D e))).
{ rewrite (ew_Eimg_Ereg_nat regs2 [] 21 (Z_to_bv 5 21) eq_refl).
  apply (vr_rv_get regs2 _ 21 _ HR). unfold vr_base. vr30_inl. }
remember (Eimg (Ereg regs2 [])) as E eqn:HE. clear HE.
(* li a0,1 *)
paj_run_sh RUNP HS HJ.
{ awr_ok_tac. }
set (mdv := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdv.
assert (Eq1 : forall a, rdW W2 (ms_mem ms) a = rdW W2 mem2 a).
{ apply (vr_rdW_frame E _ W2 mem2 (ms_mem ms) HFr). apply vr_no_wrange. constructor. }
clear HF HFr HG.
(* bne s5,a0,0x8daf4 *)
psrr_branch_pi RUNP BR HS.
- (* more than one word: the state after the reply at 0x8daf4 *)
  assert (Hnt2 : (2 <= length (Verbs.toks (e_D e)))%nat).
  { rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia. change (U E (SLit 1)) with 1 in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc. unfold vr_ntok in Hc. lia. }
  paj_run_to_shc RUNTO HS HJ 30224.
  { awr_ok_tac. }
  set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
  assert (Eq2 : forall a, rdW W2 (ms_mem ms0) a = rdW W2 (ms_mem ms) a).
  { apply (vr_rdW_frame E _ W2 (ms_mem ms) (ms_mem ms0) HFr). apply vr_no_wrange. constructor. }
  clear HF HFr HG.
  pose proof (vr_kept_regs E _ _ regs2 [] [2; 3; 4; 8; 9; 18; 19; 20; 22; 25; 27] HS HAE ltac:(vm_compute; reflexivity))
    as KR.
  cbn [ms_regs restrict] in KR.
  pmkst HS.
  apply SRr_ret. left.
  assert (Eq : forall a, rdW W2 (ms_mem ms0) a = rdW W2 mem2 a) by (intros a; rewrite Eq2; exact (Eq1 a)).
  exists O2, pos, F, q, c, tp, ly2, S2, (ms_regs ms0), (ms_mem ms0), mdv2, (k + EV_REPLY), (nm + 1).
  split; [unfold cfg_at, w64; replace (vr_pc 0x8daf4) with (BASE + 30224) by (unfold vr_pc, AF_verbs_receive; lia);
    reflexivity|].
  split; [exact Hnt2|].
  split; [|split; [exact (vr_line_eq B e q W2 mem2 _ Eq Hline3) | exact (vr_copy_eq B e F c tp W2 mem2 _ Eq Hcopy3)]].
  apply (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ _ O2 (vr_qv e) (k + EV_REPLY) (vr_k2 (e_R e) (e_D e)) (nm + 1) VR_NM_AR
    ly2 S2 W2 regs2 mem2 md2 (vr_sl3 F q c) (vr_rl_ar F q c) (vr_k2 (e_R e) (e_D e)) VR_NM_AR (ms_regs ms0) (ms_mem ms0)
    mdv2 Hcore3 HJ Eq).
  + unfold vr_rl_ar. vr30_regs KR HR.
  + apply incl_refl.
  + lia.
  + lia.
- (* one word: j 0x8db50, the state after the call after the reply *)
  assert (Hnt1' : length (Verbs.toks (e_D e)) = 1%nat).
  { rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia. change (U E (SLit 1)) with 1 in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc. unfold vr_ntok in Hc. lia. }
  assert (Haft : vr_aft (e_D e) = None) by exact (vrm_after_one atoi_a (e_D e) Hnt1').
  assert (Hk3 : vr_k3 (e_R e) (e_D e) = vr_k2 (e_R e) (e_D e)) by (unfold vr_k3; rewrite Haft; cbn [ev_after]; lia).
  paj_run_to_shc RUNTO HS HJ 30316.
  { awr_ok_tac. }
  set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
  assert (Eq2 : forall a, rdW W2 (ms_mem ms0) a = rdW W2 (ms_mem ms) a).
  { apply (vr_rdW_frame E _ W2 (ms_mem ms) (ms_mem ms0) HFr). apply vr_no_wrange. constructor. }
  clear HF HFr HG.
  pose proof (vr_kept_regs E _ _ regs2 [] [2; 3; 4; 8; 9; 18; 19; 20; 25; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pmkst HS.
  apply SRr_ret. right.
  assert (Eq : forall a, rdW W2 (ms_mem ms0) a = rdW W2 mem2 a) by (intros a; rewrite Eq2; exact (Eq1 a)).
  exists O2, pos, F, q, c, ly2, S2, (ms_regs ms0), (ms_mem ms0), mdv2, (k + EV_REPLY), (nm + 1).
  split; [unfold cfg_at, w64; replace (vr_pc 0x8db50) with (BASE + 30316) by (unfold vr_pc, AF_verbs_receive; lia);
    reflexivity|].
  split; [|split; [exact (proj1 Hline3) | exact (proj1 Hcopy3)]].
  replace (vr_R3 (e_R e) (e_D e)) with (vr_R2 (e_R e) (e_D e)) by (unfold vr_R3; rewrite Haft; reflexivity).
  apply (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ _ O2 (vr_qv e) (k + EV_REPLY) (vr_k2 (e_R e) (e_D e)) (nm + 1) VR_NM_AR
    ly2 S2 W2 regs2 mem2 md2 [(48, F)] (vr_rl_af F q c) (vr_k3 (e_R e) (e_D e)) VR_NM_AF (ms_regs ms0) (ms_mem ms0) mdv2
    Hcore3 HJ Eq).
  + unfold vr_rl_af. vr30_regs KR HR.
  + intros x [<- | []]. unfold vr_sl3. vr30_inl.
  + rewrite Hk3. lia.
  + unfold VR_NM_AR, VR_NM_AF. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   JB: the registers at the call of reply (s9 = the text moved into a1), the call, then at 0x8daf0 `ld s9,8(s1)`
   and the fall into 0x8daf4 *)
Definition vr30_rl_jb (F q c : Z) : list (Z * Z) :=
[(18, q); (19, c); (20, F); (22, F + 32); (27, shadow_addr F + 4)].

Lemma vr30_jb_tail : forall e (W : world SEGS) (regs : bvmap 5 word) mem md pos F q c tp tq O1 k nm lyc Sc,
vr_ent B MT e -> (2 <= length (Verbs.toks (e_D e)))%nat ->
vr_core B MT e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  (vr30_rl_jb F q c ++ [(11, tq)]) (vr_R1 (e_R e) (e_D e)) O1 (vr_qv e) k (vr_k1 (e_R e) (e_D e)) nm VR_NM_HD
  lyc Sc W regs mem md ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
getr regs 1 = Z_to_bv 64 (BASE + 30220) ->
4096 <= tq -> astr_atR (rdW W mem) tq (vr_x (e_R e) (e_D e)) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (pa_sigma CS_reply)) mem (seg_rom SEGS)) md) (vr_ar B MT e).
Proof.
intros e W regs mem md pos F q c tp tq O1 k nm lyc Sc He Hnt2 Hcore Hline Hcopy Hra Htq4 Hstr.
eapply SRr_bind.
{ apply (JCALL e W regs mem md pos F q c tp tq (vr_sl3 F q c) (vr30_rl_jb F q c) O1 (vr_qv e) k nm lyc Sc
    30220 (vr_k2 (e_R e) (e_D e)) VR_NM_AR He Hcore Hline Hcopy Hra).
  - lia.
  - reflexivity.
  - unfold vr30_rl_jb. repeat (apply Forall_cons; [unfold acallee_saved; cbn [fst]; lia|]). apply Forall_nil.
  - unfold vr_sl3. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil.
  - exact Htq4.
  - exact Hstr.
  - lia.
  - lia. }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & O2 & -> & HPres & Hcore3 & Hline3 & Hcopy3).
pose proof Hcore3 as (HJ & _ & _ & _ & _ & HR & _).
unfold vr30_rl_jb in HR.
pose proof (SEED e pos F q c _ _ _ _ _ _ _ (k + EV_REPLY) _ (nm + 1) _ ly2 S2 W2 regs2 mem2 md2 30220 Hcore3
  ltac:(left; reflexivity) ltac:(right; left; reflexivity) (incl_refl _)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia)) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 (vr_vals (vr_sl3 F q c))))) by apply Eimg_env.
pose proof (vr_env_agree regs2 (vr_vals (vr_sl3 F q c))) as HAE.
assert (E32 : ew (Eimg (Ereg regs2 (vr_vals (vr_sl3 F q c)))) 32 = w64 (shadow_addr F))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
remember (Eimg (Ereg regs2 (vr_vals (vr_sl3 F q c)))) as E eqn:HE. clear HE.
(* ld s9,8(s1) *)
paj_run_to_shc RUNTO HS HJ 30224.
{ awr_ok_tac. }
set (mdv := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdv.
assert (Eq : forall a, rdW W2 (ms_mem ms) a = rdW W2 mem2 a).
{ apply (vr_rdW_frame E _ W2 mem2 (ms_mem ms) HFr). apply vr_no_wrange. apply vr_ss_ro. }
clear HF HFr HG.
prreg HS (25%bv : bv 5) Q25. rewrite ?E32 in Q25.
pose proof (vr_kept_regs E _ _ regs2 _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
apply SRr_ret.
exists O2, pos, F, q, c, tp, ly2, S2, (ms_regs ms), (ms_mem ms), mdv, (k + EV_REPLY), (nm + 1).
split; [unfold cfg_at, w64; replace (vr_pc 0x8daf4) with (BASE + 30224) by (unfold vr_pc, AF_verbs_receive; lia);
  reflexivity|].
split; [exact Hnt2|].
split; [|split; [exact (vr_line_eq B e q W2 mem2 _ Eq Hline3) | exact (vr_copy_eq B e F c tp W2 mem2 _ Eq Hcopy3)]].
apply (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ _ O2 (vr_qv e) (k + EV_REPLY) (vr_k2 (e_R e) (e_D e)) (nm + 1) VR_NM_AR
  ly2 S2 W2 regs2 mem2 md2 (vr_sl3 F q c) (vr_rl_ar F q c) (vr_k2 (e_R e) (e_D e)) VR_NM_AR (ms_regs ms) (ms_mem ms)
  mdv Hcore3 HJ Eq).
- unfold vr_rl_ar. vr30_regs KR HR.
- apply incl_refl.
- lia.
- lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The six JA/JB entries: the seed at the entry, the run to the call (the loads of the spill slots and the moves),
   the boundary at the call *)
(* JA 0x8da34: ld s4,40(s1); ld s9,8(s1); ld s11,32(s1); ld s3,56(s1); mv a0,s8; mv a1,s10; jal reply *)
Lemma vr_s30_ja34 : vr_seg B MT (vr_athd B MT 0x8da34) (vr_or (vr_ar B MT) (vr_af B MT)).
Proof.
intros e W cf He Hhd.
destruct Hhd as (tq & O1 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & Hcf & Hntok & Htq4 & Hstr
  & Hcore & Hline & Hcopy).
assert (Hnt1 : (1 <= length (Verbs.toks (e_D e)))%nat) by exact Hntok.
assert (Erl : vr_rl_hd e F q c 0x8da34 tq = [(26, tq); (18, q); (21, vr_ntok (e_D e)); (22, F + 32)]) by reflexivity.
rewrite Erl in Hcore.
pose proof Hcore as (HJ & _ & _ & _ & _ & HR & _).
subst cf. unfold cfg_at, w64.
replace (vr_pc 0x8da34) with (BASE + 30032) by (unfold vr_pc, AF_verbs_receive; lia).
pose proof (SEED e pos F q c _ _ _ _ _ _ _ k _ nm _ lyc Sc W regsc memc mdc 30032 Hcore
  ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) (incl_refl _)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia)) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c))))) by apply Eimg_env.
pose proof (vr_env_agree regsc (vr_vals (vr_sl3 F q c))) as HAE.
assert (E32 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 32 = w64 (shadow_addr F))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (E35 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 35 = w64 (shadow_addr F + 4))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (E36 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 36 = w64 F)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (E38 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 38 = w64 c)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (E26 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 26 = w64 tq).
{ rewrite (ew_Eimg_Ereg_nat regsc _ 26 (Z_to_bv 5 26) eq_refl). apply (vr_rv_get regsc _ 26 _ HR). unfold vr_base. vr30_inl. }
remember (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) as E eqn:HE. clear HE.
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
assert (Eq : forall a, rdW W (ms_mem ms) a = rdW W memc a).
{ apply (vr_rdW_frame E _ W memc (ms_mem ms) HFr). apply vr_no_wrange. apply vr_ss_ro. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (11%bv : bv 5) Q11. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
rewrite ?E26 in Q11. rewrite ?E38 in Q19. rewrite ?E36 in Q20. rewrite ?E32 in Q25. rewrite ?E35 in Q27.
pose proof (vr_kept_regs E _ _ regsc _ [2; 3; 4; 8; 9; 18; 21; 22] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
assert (Hrv : vr_rv (ms_regs ms) (vr_base B e ++ (vr30_rl_ja e F q c ++ [(11, tq)]))) by (unfold vr30_rl_ja; vr30_regs KR HR).
pose proof (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ _ O1 (vr_qv e) k _ nm _ lyc Sc W regsc memc mdc
  (vr_sl3 F q c) _ (vr_k1 (e_R e) (e_D e)) VR_NM_HD (ms_regs ms) (ms_mem ms) mdv Hcore HJ Eq Hrv
  (incl_refl _) (Z.le_refl _) (Z.le_refl _)) as Hcore2.
exact (vr30_ja_tail e W (ms_regs ms) (ms_mem ms) mdv pos F q c tp tq O1 k nm lyc Sc He Hnt1 Hcore2
  (vr_line_eq B e q W memc (ms_mem ms) Eq Hline) (vr_copy_eq B e F c tp W memc (ms_mem ms) Eq Hcopy) Q1 Htq4
  (vr_astr_eq _ _ tq _ Eq Hstr)).
Qed.

(* JA 0x8da40: ld s3,56(s1); mv a0,s8; mv a1,s10; jal reply *)
Lemma vr_s30_ja40 : vr_seg B MT (vr_athd B MT 0x8da40) (vr_or (vr_ar B MT) (vr_af B MT)).
Proof.
intros e W cf He Hhd.
destruct Hhd as (tq & O1 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & Hcf & Hntok & Htq4 & Hstr
  & Hcore & Hline & Hcopy).
assert (Hnt1 : (1 <= length (Verbs.toks (e_D e)))%nat) by exact Hntok.
assert (Erl : vr_rl_hd e F q c 0x8da40 tq =
  [(26, tq); (18, q); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F); (27, shadow_addr F + 4)])
  by reflexivity.
rewrite Erl in Hcore.
pose proof Hcore as (HJ & _ & _ & _ & _ & HR & _).
subst cf. unfold cfg_at, w64.
replace (vr_pc 0x8da40) with (BASE + 30044) by (unfold vr_pc, AF_verbs_receive; lia).
pose proof (SEED e pos F q c _ _ _ _ _ _ _ k _ nm _ lyc Sc W regsc memc mdc 30044 Hcore
  ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) (incl_refl _)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia)) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c))))) by apply Eimg_env.
pose proof (vr_env_agree regsc (vr_vals (vr_sl3 F q c))) as HAE.
assert (E38 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 38 = w64 c)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (E26 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 26 = w64 tq).
{ rewrite (ew_Eimg_Ereg_nat regsc _ 26 (Z_to_bv 5 26) eq_refl). apply (vr_rv_get regsc _ 26 _ HR). unfold vr_base. vr30_inl. }
remember (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) as E eqn:HE. clear HE.
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
assert (Eq : forall a, rdW W (ms_mem ms) a = rdW W memc a).
{ apply (vr_rdW_frame E _ W memc (ms_mem ms) HFr). apply vr_no_wrange. apply vr_ss_ro. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (11%bv : bv 5) Q11. prreg HS (19%bv : bv 5) Q19.
rewrite ?E26 in Q11. rewrite ?E38 in Q19.
pose proof (vr_kept_regs E _ _ regsc _ [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 27] HS HAE ltac:(vm_compute; reflexivity))
  as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
assert (Hrv : vr_rv (ms_regs ms) (vr_base B e ++ (vr30_rl_ja e F q c ++ [(11, tq)]))) by (unfold vr30_rl_ja; vr30_regs KR HR).
pose proof (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ _ O1 (vr_qv e) k _ nm _ lyc Sc W regsc memc mdc
  (vr_sl3 F q c) _ (vr_k1 (e_R e) (e_D e)) VR_NM_HD (ms_regs ms) (ms_mem ms) mdv Hcore HJ Eq Hrv
  (incl_refl _) (Z.le_refl _) (Z.le_refl _)) as Hcore2.
exact (vr30_ja_tail e W (ms_regs ms) (ms_mem ms) mdv pos F q c tp tq O1 k nm lyc Sc He Hnt1 Hcore2
  (vr_line_eq B e q W memc (ms_mem ms) Eq Hline) (vr_copy_eq B e F c tp W memc (ms_mem ms) Eq Hcopy) Q1 Htq4
  (vr_astr_eq _ _ tq _ Eq Hstr)).
Qed.

(* JA 0x8da44: mv a0,s8; mv a1,s10; jal reply *)
Lemma vr_s30_ja44 : vr_seg B MT (vr_athd B MT 0x8da44) (vr_or (vr_ar B MT) (vr_af B MT)).
Proof.
intros e W cf He Hhd.
destruct Hhd as (tq & O1 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & Hcf & Hntok & Htq4 & Hstr
  & Hcore & Hline & Hcopy).
assert (Hnt1 : (1 <= length (Verbs.toks (e_D e)))%nat) by exact Hntok.
assert (Erl : vr_rl_hd e F q c 0x8da44 tq =
  [(26, tq); (18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F);
   (27, shadow_addr F + 4)]) by reflexivity.
rewrite Erl in Hcore.
pose proof Hcore as (HJ & _ & _ & _ & _ & HR & _).
subst cf. unfold cfg_at, w64.
replace (vr_pc 0x8da44) with (BASE + 30048) by (unfold vr_pc, AF_verbs_receive; lia).
pose proof (SEED e pos F q c _ _ _ _ _ _ _ k _ nm _ lyc Sc W regsc memc mdc 30048 Hcore
  ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) (incl_refl _)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia)) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c))))) by apply Eimg_env.
pose proof (vr_env_agree regsc (vr_vals (vr_sl3 F q c))) as HAE.
assert (E26 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 26 = w64 tq).
{ rewrite (ew_Eimg_Ereg_nat regsc _ 26 (Z_to_bv 5 26) eq_refl). apply (vr_rv_get regsc _ 26 _ HR). unfold vr_base. vr30_inl. }
remember (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) as E eqn:HE. clear HE.
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
assert (Eq : forall a, rdW W (ms_mem ms) a = rdW W memc a).
{ apply (vr_rdW_frame E _ W memc (ms_mem ms) HFr). apply vr_no_wrange. apply vr_ss_ro. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (11%bv : bv 5) Q11. rewrite ?E26 in Q11.
pose proof (vr_kept_regs E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 27] HS HAE ltac:(vm_compute; reflexivity))
  as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
assert (Hrv : vr_rv (ms_regs ms) (vr_base B e ++ (vr30_rl_ja e F q c ++ [(11, tq)]))) by (unfold vr30_rl_ja; vr30_regs KR HR).
pose proof (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ _ O1 (vr_qv e) k _ nm _ lyc Sc W regsc memc mdc
  (vr_sl3 F q c) _ (vr_k1 (e_R e) (e_D e)) VR_NM_HD (ms_regs ms) (ms_mem ms) mdv Hcore HJ Eq Hrv
  (incl_refl _) (Z.le_refl _) (Z.le_refl _)) as Hcore2.
exact (vr30_ja_tail e W (ms_regs ms) (ms_mem ms) mdv pos F q c tp tq O1 k nm lyc Sc He Hnt1 Hcore2
  (vr_line_eq B e q W memc (ms_mem ms) Eq Hline) (vr_copy_eq B e F c tp W memc (ms_mem ms) Eq Hcopy) Q1 Htq4
  (vr_astr_eq _ _ tq _ Eq Hstr)).
Qed.

(* JB 0x8dad4: mv s9,a0; ld s4,40(s1); ld s11,32(s1); ld s3,56(s1); mv a0,s8; mv a1,s9; jal reply *)
Lemma vr_s30_jb : vr_seg B MT (vr_athd B MT 0x8dad4) (vr_ar B MT).
Proof.
intros e W cf He Hhd.
destruct Hhd as (tq & O1 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & Hcf & Hntok & Htq4 & Hstr
  & Hcore & Hline & Hcopy).
assert (Hnt2 : (2 <= length (Verbs.toks (e_D e)))%nat) by exact Hntok.
assert (Erl : vr_rl_hd e F q c 0x8dad4 tq = [(10, tq); (18, q); (22, F + 32)]) by reflexivity.
rewrite Erl in Hcore.
pose proof Hcore as (HJ & _ & _ & _ & _ & HR & _).
subst cf. unfold cfg_at, w64.
replace (vr_pc 0x8dad4) with (BASE + 30192) by (unfold vr_pc, AF_verbs_receive; lia).
pose proof (SEED e pos F q c _ _ _ _ _ _ _ k _ nm _ lyc Sc W regsc memc mdc 30192 Hcore
  ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) (incl_refl _)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia)) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c))))) by apply Eimg_env.
pose proof (vr_env_agree regsc (vr_vals (vr_sl3 F q c))) as HAE.
assert (E35 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 35 = w64 (shadow_addr F + 4))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (E36 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 36 = w64 F)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (E38 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 38 = w64 c)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (E10 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 10 = w64 tq).
{ rewrite (ew_Eimg_Ereg_nat regsc _ 10 (Z_to_bv 5 10) eq_refl). apply (vr_rv_get regsc _ 10 _ HR). unfold vr_base. vr30_inl. }
remember (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) as E eqn:HE. clear HE.
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
assert (Eq : forall a, rdW W (ms_mem ms) a = rdW W memc a).
{ apply (vr_rdW_frame E _ W memc (ms_mem ms) HFr). apply vr_no_wrange. apply vr_ss_ro. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (11%bv : bv 5) Q11. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (27%bv : bv 5) Q27.
rewrite ?E10 in Q11. rewrite ?E38 in Q19. rewrite ?E36 in Q20. rewrite ?E35 in Q27.
pose proof (vr_kept_regs E _ _ regsc _ [2; 3; 4; 8; 9; 18; 22] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
assert (Hrv : vr_rv (ms_regs ms) (vr_base B e ++ (vr30_rl_jb F q c ++ [(11, tq)]))) by (unfold vr30_rl_jb; vr30_regs KR HR).
pose proof (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ _ O1 (vr_qv e) k _ nm _ lyc Sc W regsc memc mdc
  (vr_sl3 F q c) _ (vr_k1 (e_R e) (e_D e)) VR_NM_HD (ms_regs ms) (ms_mem ms) mdv Hcore HJ Eq Hrv
  (incl_refl _) (Z.le_refl _) (Z.le_refl _)) as Hcore2.
exact (vr30_jb_tail e W (ms_regs ms) (ms_mem ms) mdv pos F q c tp tq O1 k nm lyc Sc He Hnt2 Hcore2
  (vr_line_eq B e q W memc (ms_mem ms) Eq Hline) (vr_copy_eq B e F c tp W memc (ms_mem ms) Eq Hcopy) Q1 Htq4
  (vr_astr_eq _ _ tq _ Eq Hstr)).
Qed.

(* JB 0x8dae0: ld s3,56(s1); mv a0,s8; mv a1,s9; jal reply *)
Lemma vr_s30_je0 : vr_seg B MT (vr_athd B MT 0x8dae0) (vr_ar B MT).
Proof.
intros e W cf He Hhd.
destruct Hhd as (tq & O1 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & Hcf & Hntok & Htq4 & Hstr
  & Hcore & Hline & Hcopy).
assert (Hnt2 : (2 <= length (Verbs.toks (e_D e)))%nat) by exact Hntok.
assert (Erl : vr_rl_hd e F q c 0x8dae0 tq = [(25, tq); (18, q); (20, F); (22, F + 32); (27, shadow_addr F + 4)])
  by reflexivity.
rewrite Erl in Hcore.
pose proof Hcore as (HJ & _ & _ & _ & _ & HR & _).
subst cf. unfold cfg_at, w64.
replace (vr_pc 0x8dae0) with (BASE + 30204) by (unfold vr_pc, AF_verbs_receive; lia).
pose proof (SEED e pos F q c _ _ _ _ _ _ _ k _ nm _ lyc Sc W regsc memc mdc 30204 Hcore
  ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) (incl_refl _)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia)) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c))))) by apply Eimg_env.
pose proof (vr_env_agree regsc (vr_vals (vr_sl3 F q c))) as HAE.
assert (E38 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 38 = w64 c)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (E25 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 25 = w64 tq).
{ rewrite (ew_Eimg_Ereg_nat regsc _ 25 (Z_to_bv 5 25) eq_refl). apply (vr_rv_get regsc _ 25 _ HR). unfold vr_base. vr30_inl. }
remember (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) as E eqn:HE. clear HE.
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
assert (Eq : forall a, rdW W (ms_mem ms) a = rdW W memc a).
{ apply (vr_rdW_frame E _ W memc (ms_mem ms) HFr). apply vr_no_wrange. apply vr_ss_ro. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (11%bv : bv 5) Q11. prreg HS (19%bv : bv 5) Q19.
rewrite ?E25 in Q11. rewrite ?E38 in Q19.
pose proof (vr_kept_regs E _ _ regsc _ [2; 3; 4; 8; 9; 18; 20; 22; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
assert (Hrv : vr_rv (ms_regs ms) (vr_base B e ++ (vr30_rl_jb F q c ++ [(11, tq)]))) by (unfold vr30_rl_jb; vr30_regs KR HR).
pose proof (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ _ O1 (vr_qv e) k _ nm _ lyc Sc W regsc memc mdc
  (vr_sl3 F q c) _ (vr_k1 (e_R e) (e_D e)) VR_NM_HD (ms_regs ms) (ms_mem ms) mdv Hcore HJ Eq Hrv
  (incl_refl _) (Z.le_refl _) (Z.le_refl _)) as Hcore2.
exact (vr30_jb_tail e W (ms_regs ms) (ms_mem ms) mdv pos F q c tp tq O1 k nm lyc Sc He Hnt2 Hcore2
  (vr_line_eq B e q W memc (ms_mem ms) Eq Hline) (vr_copy_eq B e F c tp W memc (ms_mem ms) Eq Hcopy) Q1 Htq4
  (vr_astr_eq _ _ tq _ Eq Hstr)).
Qed.

(* JB 0x8dae4: mv a0,s8; mv a1,s9; jal reply *)
Lemma vr_s30_je4 : vr_seg B MT (vr_athd B MT 0x8dae4) (vr_ar B MT).
Proof.
intros e W cf He Hhd.
destruct Hhd as (tq & O1 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & Hcf & Hntok & Htq4 & Hstr
  & Hcore & Hline & Hcopy).
assert (Hnt2 : (2 <= length (Verbs.toks (e_D e)))%nat) by exact Hntok.
assert (Erl : vr_rl_hd e F q c 0x8dae4 tq =
  [(25, tq); (18, q); (19, c); (20, F); (22, F + 32); (27, shadow_addr F + 4)]) by reflexivity.
rewrite Erl in Hcore.
pose proof Hcore as (HJ & _ & _ & _ & _ & HR & _).
subst cf. unfold cfg_at, w64.
replace (vr_pc 0x8dae4) with (BASE + 30208) by (unfold vr_pc, AF_verbs_receive; lia).
pose proof (SEED e pos F q c _ _ _ _ _ _ _ k _ nm _ lyc Sc W regsc memc mdc 30208 Hcore
  ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) (incl_refl _)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia)) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c))))) by apply Eimg_env.
pose proof (vr_env_agree regsc (vr_vals (vr_sl3 F q c))) as HAE.
assert (E25 : ew (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) 25 = w64 tq).
{ rewrite (ew_Eimg_Ereg_nat regsc _ 25 (Z_to_bv 5 25) eq_refl). apply (vr_rv_get regsc _ 25 _ HR). unfold vr_base. vr30_inl. }
remember (Eimg (Ereg regsc (vr_vals (vr_sl3 F q c)))) as E eqn:HE. clear HE.
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
assert (Eq : forall a, rdW W (ms_mem ms) a = rdW W memc a).
{ apply (vr_rdW_frame E _ W memc (ms_mem ms) HFr). apply vr_no_wrange. apply vr_ss_ro. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (11%bv : bv 5) Q11. rewrite ?E25 in Q11.
pose proof (vr_kept_regs E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
assert (Hrv : vr_rv (ms_regs ms) (vr_base B e ++ (vr30_rl_jb F q c ++ [(11, tq)]))) by (unfold vr30_rl_jb; vr30_regs KR HR).
pose proof (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ _ O1 (vr_qv e) k _ nm _ lyc Sc W regsc memc mdc
  (vr_sl3 F q c) _ (vr_k1 (e_R e) (e_D e)) VR_NM_HD (ms_regs ms) (ms_mem ms) mdv Hcore HJ Eq Hrv
  (incl_refl _) (Z.le_refl _) (Z.le_refl _)) as Hcore2.
exact (vr30_jb_tail e W (ms_regs ms) (ms_mem ms) mdv pos F q c tp tq O1 k nm lyc Sc He Hnt2 Hcore2
  (vr_line_eq B e q W memc (ms_mem ms) Eq Hline) (vr_copy_eq B e F c tp W memc (ms_mem ms) Eq Hcopy) Q1 Htq4
  (vr_astr_eq _ _ tq _ Eq Hstr)).
Qed.

Lemma vr_s30 : vr_s30_stmt B MT.
Proof.
exact (conj vr_s30_j1 (conj vr_s30_ja34 (conj vr_s30_ja40 (conj vr_s30_ja44
  (conj vr_s30_jb (conj vr_s30_je0 vr_s30_je4)))))).
Qed.

End e.
End f.
End d.
