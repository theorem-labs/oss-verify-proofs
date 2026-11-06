(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S07 (route add, 0x8d8fc) of the walk of verbs_receive on the ASan build
   of plugin-hostd/fuzz_command (lib/A/Prog/verbs_receive_iface.v, vr_s07_stmt): the refusal inside the arm,
   0x8d9d4-0x8d9e0 and 0x8dab8-0x8dac0: `li a0,-902; jal sup_resp; mv s9,a0; j; ld s4,40(s1); ld s11,32(s1); j 0x8dae4`
   (too many words after the uri and the id), from the state there to the join JB at 0x8dae4 (vr_hd). sup_resp's post
   is FP-existential (statement pass 4), so the code after its return is legR_k, in its own section (it holds at
   every FP state), and legR ends at JB at the FP state sup_resp returned at (hdF07). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_resp_c xstrdup_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_s07a verbs_receive_s07b verbs_receive_s07c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.

Section dk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fk.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section ek.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : PALib B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUN07 := run07 B MT TL ROA RRO RECC PROGU.

(* after sup_resp returned, 0x8d9dc: `mv s9,a0; j 0x8dab8; ld s4,40(s1); ld s11,32(s1); j 0x8dae4` *)
Lemma legR_k : forall e W2 pos F q c tp ly2 S2 regs2 mem2 md2 k nm tq,
Z.of_nat (length (e_D e)) = e_n e ->
vr_h (e_R e) (e_D e) = (e_R e, resp (-902), false) -> (2 <= length (PV.toks (e_D e)))%nat ->
vr_core B MT e pos F [(tq, Z.of_nat (length (resp (-902))) + 1); vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(18, q); (19, c); (22, F + 32)] (e_R e) (e_O e) (e_q0 e) k (vr_k1 (e_R e) (e_D e)) nm VR_NM_HD
  ly2 S2 W2 regs2 mem2 md2 ->
vr_line B e q W2 mem2 -> vr_copy B e F c tp W2 mem2 ->
getr regs2 (Z_to_bv 5 10) = w64 tq -> astr_atR (rdW W2 mem2) tq (resp (-902)) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 29944)) mem2 (seg_rom SEGS)) md2) (vr_athd B MT 0x8dae4 e).
Proof.
intros e W2 pos F q c tp ly2 S2 regs2 mem2 md2 k nm tq HDn EH Hnt Hc2 Hl2 Hcp2 Ha0' Hstr.
pose proof Hc2 as (HJ2 & _ & _ & _ & _ & Hrv2 & _ & _ & _ & _ & _ & Hperm2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (resp_length (-902) ltac:(lia)) as Hrl.
set (n := Z.of_nat (length (resp (-902))) + 1) in *.
assert (Htin : In (tq, n) (ablocks B ly2 S2)).
{ apply (Permutation_in _ (Permutation_sym Hperm2)). apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ tq n (proj1 HJ2) Htin) as (_ & Hq4 & Hqc & _ & _ & _ & Hqn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
assert (R22b : getr regs2 (Z_to_bv 5 22) = w64 (F + 32)) by (apply (rv_get07 regs2 _ 22 _ Hrv2); cbn; tauto).
pose proof (seed_core B MT e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 29944 []
  Hc2 Hcp2 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) R22b
  ltac:(intros [|i] p0 Hi; discriminate) ltac:(cbn; lia)) as HS2.
remember (E07 regs2 q (shadow_addr F + 4) F c []) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply E07_env).
pose proof (env_agree07 regs2 q (shadow_addr F + 4) F c []) as HAE2. rewrite <- HE2 in HAE2.
assert (X33 : ew E2 33 = Z_to_bv 64 (shadow_addr F + 4)) by (rewrite HE2; apply (E07_ext _ _ _ _ _ _ 1); [lia | reflexivity]).
assert (X34 : ew E2 34 = Z_to_bv 64 F) by (rewrite HE2; apply (E07_ext _ _ _ _ _ _ 2); [lia | reflexivity]).
assert (EE10 : ew E2 10 = getr regs2 (Z_to_bv 5 10)) by (rewrite HE2; apply E07_reg; reflexivity).
clear HE2.
paj_run_to_sh RUNTOP HS2 HJ2 (AF_verbs_receive + (0x8dae4 - 0x8d480)).
{ awr07. }
mdv_set.
assert (V2 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms) a = rdW W2 mem2 a)
  by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
prreg HS2 (Z_to_bv 5 25) T25. prreg HS2 (Z_to_bv 5 20) T20. prreg HS2 (Z_to_bv 5 27) T27.
rewrite EE10, Ha0' in T25. rewrite X34 in T20. rewrite X33 in T27.
pose proof (kept_regs07 E2 _ _ regs2 _ [2; 3; 4; 8; 9; 18; 19; 22] HS2 HAE2 ltac:(vm_compute; reflexivity)) as KR2.
cbn [ms_regs restrict] in KR2.
assert (Hrv3 : vr_rv (ms_regs ms) (vr_base B e ++ vr_rl_hd e F q c 0x8dae4 tq)).
{ change (vr_rl_hd e F q c 0x8dae4 tq) with [(25, tq); (18, q); (19, c); (20, F); (22, F + 32); (27, shadow_addr F + 4)].
  apply rv_intro07. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
  - unfold vr_base in Hin. cbn in Hin.
    destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
      (rewrite KR2 by (cbn; tauto); apply (rv_get07 regs2 _ _ _ Hrv2); cbn; tauto).
  - cbn in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]; injection E1 as <- <-;
      first [exact T25 | exact T20 | exact T27 | rewrite KR2 by (cbn; tauto); apply (rv_get07 regs2 _ _ _ Hrv2); cbn; tauto]. }
destruct (RUN07 e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ W2 regs2 (ms_regs ms) mem2 (ms_mem ms) md2 mdv
  Hc2 Hl2 Hcp2 HJ2 V2 Hrv3 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) HDn)
  as (Hc3 & Hl3 & Hcp3).
pmkst HS2.
replace (BASE + 30208) with (vr_pc 0x8dae4) by (unfold vr_pc, AF_verbs_receive; lia).
assert (EX : vr_x (e_R e) (e_D e) = resp (-902)) by (unfold vr_x; rewrite EH; reflexivity).
assert (ER : vr_R1 (e_R e) (e_D e) = e_R e) by (unfold vr_R1; rewrite EH; reflexivity).
assert (EQ : vr_qv e = e_q0 e) by (unfold vr_qv, vr_quit; rewrite EH; reflexivity).
apply (exit_hd_e4 B MT e W2 tq (e_O e) pos F q c tp ly2 S2 (ms_regs ms) (ms_mem ms) mdv k nm).
- exact Hnt.
- lia.
- rewrite EX. apply (astr_atR_agree (rdW W2 mem2) _ tq (resp (-902)) n Hstr); [unfold n; lia|].
  intros kk Hkk. apply V2. lia.
- rewrite EX, ER, EQ. exact Hc3.
- exact Hl3.
- exact Hcp3.
Qed.

End ek.
End fk.
End dk.

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
Hypothesis TSUP_RESP : tsup_resp_spec B MT.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let C07C := c07_call B MT TL ROA RECC RRO PROGU RPG.
Let RUN07 := run07 B MT TL ROA RRO RECC PROGU.
Let CALL07F := call07F B MT HB PROGU.

Lemma legR : forall e W pos F q c tp lyc Sc regsc memc mdc k nm args,
vr_ent B MT e ->
PV.toks (e_D e) = PV.Lit.verb_add :: args -> PV.add_m atoi_a args = PV.reject -> (1 <= length args)%nat ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) [(18, q); (19, c); (22, F + 32)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
SRr SEGS W (cfg_at SEGS (vr_pc 0x8d9d4) regsc memc mdc) (hdF07 B MT 0x8dae4 e).
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm args Hent Htk Hrej Hargs Hcore Hline Hcopy.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HDn & _).
pose proof Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof (core_regs07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore)
  as (R2 & R3 & R4 & R8 & R9 & Hspz & Hs0 & Ho16 & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (EH : vr_h (e_R e) (e_D e) = (e_R e, resp (-902), false))
  by (unfold vr_h; rewrite (st_add _ _ Htk), Hrej; reflexivity).
assert (EK : vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_RESP)
  by (unfold vr_k1; rewrite (evr_add _ _ _ Htk), Hrej; reflexivity).
assert (Hcs3 : cs07 [(18, q); (19, c); (22, F + 32)]) by (unfold cs07; cs07_tac).
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 (F + 32)) by (apply (rv_get07 regsc _ 22 _ Hrv); cbn; tauto).
pose proof (seed_core B MT e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (AF_verbs_receive + (0x8d9d4 - 0x8d480)) []
  Hcore Hcopy ltac:(left; reflexivity) ltac:(right; left; reflexivity) R22
  ltac:(intros [|i] p0 Hi; discriminate) ltac:(cbn; lia)) as HS.
remember (E07 regsc q (shadow_addr F + 4) F c []) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply E07_env).
pose proof (env_agree07 regsc q (shadow_addr F + 4) F c []) as HAE. rewrite <- HE in HAE.
clear HE.
unfold cfg_at, vr_pc, w64.
(* 0x8d9d4: li a0,-902; jal sup_resp *)
paj_run_shc RUNP RUNC HS HJ.
{ awr07. }
mdv_set.
assert (V : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a)
  by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
clear HF HFr HG.
prreg HS (Z_to_bv 5 1) Q1. prreg HS (Z_to_bv 5 10) Q10.
pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS HAE
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
pose proof (ap_of_kept07 regsc (ms_regs ms) KR) as HP0.
pmkst HS.
rewrite (SIGP CS_sup_resp) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_sup_resp) with AF_sup_resp.
destruct (RUN07 e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms) memc (ms_mem ms) mdc mdv
  Hcore Hline Hcopy HJ V (rv_keep07 B e regsc (ms_regs ms) _ Hrv Hcs3 HP0)
  ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn) as (Hc1 & Hl1 & Hcp1).
pose proof Hc1 as (HJ1 & Hk1 & Hmet1 & Hnm1 & Hfr1 & Hrv1 & Hsv1 & Hsp1 & Henv1 & Hrec1 & Hdat1 & Hperm1 & Hq1).
assert (HV1 : SUP_RESP_STK = ltac:(let v := eval vm_compute in SUP_RESP_STK in exact v)) by reflexivity.
assert (HV0 : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
eapply (CALL07F e pos F q c _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs ms) (ms_mem ms) mdv AF_sup_resp SUP_RESP_STK [] EV_SUP_RESP
  _ _ _ Hent Hc1 Q1).
- lia.
- reflexivity.
- lia.
- lia.
- intros a (r0 & Hr0 & _). destruct Hr0.
- (* the callee *)
  intros ch HPRE.
  apply (TSUP_RESP lyc Sc W (ms_regs ms) (ms_mem ms) mdv ch (-902) HPRE (frm07 B MT e Hent)).
  + pose proof (frames07 B MT e pos lyc Sc W (ms_mem ms) mdv k Hent HJ1). lia.
  + exact (proj1 Henv1).
  + exact (proj1 (proj2 (proj2 Henv1))).
  + refine (eq_trans Q10 _). apply bv_eq. vm_compute. reflexivity.
  + lia.
  + exact (ev07 B MT e _ lyc Sc W (ms_mem ms) mdv k EV_SUP_RESP Hent HJ1 ltac:(rewrite EK; lia)).
  + pose proof (live07 B MT e pos F q c _ _ _ _ _ _ _ _ _ lyc Sc W _ _ _ Hent Hc1) as HL.
    pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlive0 & _).
    pose proof (resp_length (-902) ltac:(lia)) as Hrl.
    unfold LIVE_SUP_RESP, LIVE_XSTRDUP, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in *. lia.
  + apply (mok07 B MT MTL e Sc k nm 1 0 _ EV_SUP_RESP Hent Hmet1).
    * rewrite EK. lia.
    * exact (xm_resp_le MT MTL (-902) ltac:(lia)).
    * unfold EV_SUP_RESP, EV_XSTRDUP. lia.
    * unfold EV_SUP_RESP, EV_XSTRDUP. lia.
- (* after the return, 0x8d9dc, at the FP state fx' sup_resp returned at *)
  intros fx' ly2 S2 W2 regs2 mem2 md2 Hfx HJ2 HJc HP2 HK.
  destruct HK as (tq & HK). cbv zeta in HK.
  destruct HK as (Ha0 & Htq & HpermR & Hap & HinT & Hstr & HrecT & Hbb & Hmle).
  assert (Ha0' : getr regs2 (Z_to_bv 5 10) = w64 tq) by exact Ha0.
  set (n := Z.of_nat (length (resp (-902))) + 1) in *.
  pose proof (rv_keep07 B e (ms_regs ms) regs2 _ Hrv1 Hcs3 HP2) as Hrv2.
  assert (Hmet2 : vr_meter MT e S2 (k + EV_SUP_RESP) (nm + 1)).
  { apply (meter_step MT MTL e Sc S2 k nm 1 0 (XM_SUP_RESP MT (-902)) EV_SUP_RESP Hmet1 Hmle
      (xm_resp_le MT MTL (-902) ltac:(lia))); unfold EV_SUP_RESP, EV_XSTRDUP; lia. }
  assert (HpermT : Permutation (ablocks B ly2 S2) (e_O e ++ [(tq, n); vr_lb e q; vr_cb e c] ++ e_rest e)).
  { eapply perm_trans; [exact HpermR|]. eapply perm_trans; [apply perm_skip; exact Hperm1|]. apply Permutation_middle. }
  destruct (C07C e pos F q c tp [vr_lb e q; vr_cb e c] [(tq, n); vr_lb e q; vr_cb e c] _ [(18, q); (19, c); (22, F + 32)]
    (e_R e) (e_R e) (e_O e) (e_O e) (e_q0 e) k (k + EV_SUP_RESP) 2 (vr_k1 (e_R e) (e_D e)) nm (nm + 1) VR_NM_PRE VR_NM_HD
    lyc Sc W (ms_regs ms) (ms_mem ms) mdv ly2 S2 W2 regs2 mem2 md2 SUP_RESP_STK [] EV_SUP_RESP
    Hc1 Hl1 Hcp1 HJ2 HJc ltac:(lia) ltac:(intros a (r0 & Hr0 & _); destruct Hr0)
    ltac:(intros pn Hpn _; apply (Permutation_in _ (Permutation_sym HpermR)); right; exact Hpn)
    ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn
    ltac:(rewrite EK; lia) Hmet2 ltac:(unfold VR_NM_HD, VR_NM_PRE in *; lia) Hrv2 (HrecT _ _ Hrec1) Hdat1 HpermT)
    as (Hc2 & Hl2 & Hcp2).
  eapply SRr_mono.
  { exact (legR_k (fx := fx') B MT TL ROA RRO RECC PROGU e W2 pos F q c tp ly2 S2 regs2 mem2 md2 (k + EV_SUP_RESP) (nm + 1)
      tq HDn EH ltac:(rewrite Htk; cbn [length]; lia) Hc2 Hl2 Hcp2 Ha0' Hstr). }
  intros W' c' _ H. unfold hdF07. exists fx'. split; [exact Hfx | exact H].
Qed.

End e.
End f.
End d.
