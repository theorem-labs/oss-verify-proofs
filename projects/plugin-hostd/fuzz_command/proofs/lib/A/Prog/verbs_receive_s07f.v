(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S07 (route add, 0x8d8fc) of the walk of verbs_receive on the ASan build
   of plugin-hostd/fuzz_command (lib/A/Prog/verbs_receive_iface.v, vr_s07_stmt): the add tail after sup_add returned,
   0x8da90-0x8dab0: `beqz a0` (not taken: sup_add's text is a live block), `mv s9,a0; jal sup_reply_code`, the
   reloads of s4 and s11, `bltz a0, 0x8dae4` (a refusal code), else `ld a0,8(s6); jal descriptors_add; j 0x8dae4`
   (tok[1] recorded), to the join JB at 0x8dae4 (vr_hd). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
descriptors_add_c sup_add_c sup_reply_code_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
verbs_receive_s07a verbs_receive_s07b verbs_receive_s07c verbs_receive_s07e.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.

Lemma EVd_nn07 : forall R, 0 <= EV_DESCRIPTORS_ADD R.
Proof. intros R. unfold EV_DESCRIPTORS_ADD, rec_spill_frees, EV_XSTRDUP. destruct (Nat.ltb _ _); lia. Qed.

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
Hypothesis TSUP_REPLY_CODE : tsup_reply_code_spec B MT.
Hypothesis TDESCRIPTORS_ADD : tdescriptors_add_spec B MT.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis BLKT : vr_blktail B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let C07C := c07_call B MT TL ROA RECC RRO PROGU RPG.
Let RUN07 := run07 B MT TL ROA RRO RECC PROGU.
Let CALL07 := call07 B MT HB PROGU.

Lemma legT2 : forall e W pos F q c tp lyc Sc regsc memc mdc k nm args u iv pl cl R1 t O1 tq pu,
vr_ent B MT e ->
PV.toks (e_D e) = PV.Lit.verb_add :: args -> PV.add_m atoi_a args = PV.SAdd u iv pl cl ->
sup_add_m (e_R e) (Some u) iv pl cl = (R1, t) ->
nth_error tp 1 = Some pu -> nth_error (PV.toks (e_D e)) 1 = Some u -> (1 <= length args)%nat ->
vr_core B MT e pos F [(tq, Z.of_nat (length t) + 1); vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(18, q); (19, c); (22, F + 32)] R1 O1 (e_q0 e) k (vr_k1 (e_R e) (e_D e)) nm VR_NM_HD lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
getr regsc (Z_to_bv 5 10) = w64 tq -> 4096 <= tq -> astr_atR (rdW W memc) tq t ->
k + EV_SUP_REPLY_CODE + EV_DESCRIPTORS_ADD R1 <= vr_k1 (e_R e) (e_D e) -> nm <= 8 ->
blocks_bytes Sc + 8193 <= LIVE_MAX ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + 30124)) memc (seg_rom SEGS)) mdc) (vr_athd B MT 0x8dae4 e).
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm args u iv pl cl R1 t O1 tq pu
  Hent Htk Hadd Hsa Hpu Hu Hargs Hcore Hline Hcopy R10 Htq4 Hstr HkE Hnm8 Hlive.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HDn & _).
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & VOBJS & _).
pose proof Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof (core_regs07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore)
  as (R2 & R3 & R4 & R8 & R9 & Hspz & Hs0 & Ho16 & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
set (n := Z.of_nat (length t) + 1) in *.
pose proof (proj1 HJ) as HAR.
assert (Htin : In (tq, n) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ tq n HAR Htin) as (_ & Hq4 & Hqc & _ & _ & _ & Hqn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
assert (EH : vr_h (e_R e) (e_D e) = ((if 0 <=? reply_code_a t then descriptors_add_m R1 (Some u) else R1), t, false)).
{ unfold vr_h. rewrite (st_add _ _ Htk), Hadd. cbn [VerbsRun.run_step]. rewrite Hsa. reflexivity. }
assert (EX : vr_x (e_R e) (e_D e) = t) by (unfold vr_x; rewrite EH; reflexivity).
assert (EQ : vr_qv e = e_q0 e) by (unfold vr_qv, vr_quit; rewrite EH; reflexivity).
assert (Hnt : (2 <= length (PV.toks (e_D e)))%nat) by (rewrite Htk; cbn [length]; lia).
assert (HV0 : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
assert (Hcs4 : cs07 [(18, q); (19, c); (22, F + 32); (25, tq)]) by (unfold cs07; cs07_tac).
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 (F + 32)) by (apply (rv_get07 regsc _ 22 _ Hrv); cbn; tauto).
(* 0x8da90: beqz a0 *)
pose proof (seed_core B MT e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 30124 []
  Hcore Hcopy ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) R22
  ltac:(intros [|i] p0 Hi; discriminate) ltac:(cbn; lia)) as HS.
remember (E07 regsc q (shadow_addr F + 4) F c []) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply E07_env).
pose proof (env_agree07 regsc q (shadow_addr F + 4) F c []) as HAE. rewrite <- HE in HAE.
assert (EE10 : ew E 10 = getr regsc (Z_to_bv 5 10)) by (rewrite HE; apply E07_reg; reflexivity).
clear HE.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_eq_U, U_lit, (U_atom E 10 tq) in Hc by (try (rewrite EE10, R10; reflexivity); lia).
  apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* 0x8da94: mv s9,a0; jal sup_reply_code *)
paj_run_shc RUNP RUNC HS HJ.
{ awr07. }
mdv_set.
assert (V : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a)
  by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
clear HF HFr HG.
prreg HS (Z_to_bv 5 1) Q1. prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 25) Q25.
rewrite EE10 in Q10, Q25.
pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27] HS HAE
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
pmkst HS.
rewrite (SIGP CS_sup_reply_code) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_sup_reply_code) with AF_sup_reply_code.
assert (Hrv1 : vr_rv (ms_regs ms) (vr_base B e ++ [(18, q); (19, c); (22, F + 32); (25, tq)])).
{ apply rv_intro07. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
  - unfold vr_base in Hin. cbn in Hin.
    destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
      (rewrite KR by (cbn; tauto); apply (rv_get07 regsc _ _ _ Hrv); cbn; tauto).
  - cbn in Hin. destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-;
      first [rewrite KR by (cbn; tauto); apply (rv_get07 regsc _ _ _ Hrv); cbn; tauto | exact (eq_trans Q25 R10)]. }
destruct (RUN07 e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms) memc (ms_mem ms) mdc mdv
  Hcore Hline Hcopy HJ V Hrv1 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) HDn)
  as (Hc1 & Hl1 & Hcp1).
pose proof Hc1 as (HJ1 & Hk1 & Hmet1 & Hnm1 & Hfr1 & Hrv1' & Hsv1 & Hsp1 & Henv1 & Hrec1 & Hdat1 & Hperm1 & Hq1).
pose proof (proj1 HJ1) as HAR1.
assert (Hstr1 : astr_atR (rdW W (ms_mem ms)) tq t).
{ apply (astr_atR_agree (rdW W memc) _ tq t n Hstr); [unfold n; lia|]. intros kk Hkk. apply V. lia. }
assert (HV1 : SUP_REPLY_CODE_STK = ltac:(let v := eval vm_compute in SUP_REPLY_CODE_STK in exact v)) by reflexivity.
eapply (CALL07 e pos F q c _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs ms) (ms_mem ms) mdv AF_sup_reply_code
  SUP_REPLY_CODE_STK [] EV_SUP_REPLY_CODE _ _ _ Hent Hc1 Q1).
- lia.
- reflexivity.
- lia.
- lia.
- intros a (r0 & Hr0 & _). destruct Hr0.
- (* sup_reply_code(text) *)
  intros ch HPRE.
  apply (TSUP_REPLY_CODE lyc Sc W (ms_regs ms) (ms_mem ms) mdv tq t (afn_pre_na_of SEGS B _ _ _ _ _ _ _ _ HPRE)).
  + exact (proj1 Henv1).
  + exact (eq_trans Q10 R10).
  + lia.
  + exists tq, n. split; [exact Htin | lia].
  + exact Hstr1.
  + apply (BLKT lyc Sc W (ms_mem ms) mdv tq n (tq + Z.of_nat (length t)) HAR1 Htin). unfold n. lia.
  + exact (proj1 (proj2 (proj2 Henv1))).
  + exact VOBJS.
  + apply (ev07 B MT e _ lyc Sc W (ms_mem ms) mdv k EV_SUP_REPLY_CODE Hent HJ1).
    pose proof (EVd_nn07 R1). lia.
- (* after the return, 0x8da9c *)
  intros ly2 S2 W2 regs2 mem2 md2 HJ2 HJc HP2 HK.
  destruct HK as (Ha0 & HpermR & -> & ->).
  assert (Ha0' : getr regs2 (Z_to_bv 5 10) = w64 (reply_code_a t)) by exact Ha0.
  pose proof (rv_keep07 B e (ms_regs ms) regs2 _ Hrv1 Hcs4 HP2) as Hrv2.
  pose proof (recj07 B PROGU lyc Sc W (ms_mem ms) mdv lyc Sc W2 mem2 md2 SUP_REPLY_CODE_STK (vr_s1 e)
    EV_SUP_REPLY_CODE R1 O1 HAR1 Hrec1 HJc (fun pn Hpn => rec_repA_in_blocks B _ _ _ _ _ _ Hrec1 Hpn)) as Hrec2.
  assert (Hmet2 : vr_meter MT e Sc (k + EV_SUP_REPLY_CODE) nm) by (unfold EV_SUP_REPLY_CODE; rewrite Z.add_0_r; exact Hmet1).
  destruct (C07C e pos F q c tp [(tq, n); vr_lb e q; vr_cb e c] [(tq, n); vr_lb e q; vr_cb e c] _
    [(18, q); (19, c); (22, F + 32); (25, tq)]
    R1 R1 O1 O1 (e_q0 e) k (k + EV_SUP_REPLY_CODE) (vr_k1 (e_R e) (e_D e)) (vr_k1 (e_R e) (e_D e)) nm nm VR_NM_HD VR_NM_HD
    lyc Sc W (ms_regs ms) (ms_mem ms) mdv lyc Sc W2 regs2 mem2 md2 SUP_REPLY_CODE_STK [] EV_SUP_REPLY_CODE
    Hc1 Hl1 Hcp1 HJ2 HJc ltac:(lia) ltac:(intros a (r0 & Hr0 & _); destruct Hr0)
    ltac:(intros pn Hpn _; exact Hpn)
    ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) HDn
    ltac:(pose proof (EVd_nn07 R1); lia)
    Hmet2 Hnm1 Hrv2 Hrec2 Hdat1 Hperm1)
    as (Hc2 & Hl2 & Hcp2).
  assert (Hstr2 : astr_atR (rdW W2 mem2) tq t).
  { apply (astr_atR_agree (rdW W (ms_mem ms)) _ tq t n Hstr1); [unfold n; lia|]. intros kk Hkk.
    exact (blk07 B MT PROGU e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs ms) (ms_mem ms) mdv
      SUP_REPLY_CODE_STK (vr_s1 e) [] lyc Sc W2 mem2 md2 EV_SUP_REPLY_CODE tq n Hc1 HJc
      ltac:(intros a (r0 & Hr0 & _); destruct Hr0) ltac:(left; reflexivity) Htin kk ltac:(lia)). }
  pose proof Hc2 as (HJ2' & Hk2 & Hmet2' & Hnm2 & Hfr2 & Hrv2' & Hsv2 & Hsp2 & Henv2 & Hrec2' & Hdat2 & Hperm2 & Hq2).
  (* 0x8da9c: ld s4,40(s1); ld s11,32(s1); bltz a0, 0x8dae4 *)
  assert (R22b : getr regs2 (Z_to_bv 5 22) = w64 (F + 32)) by (apply (rv_get07 regs2 _ 22 _ Hrv2); cbn; tauto).
  pose proof (seed_core B MT e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 30136 [pu]
    Hc2 Hcp2 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) R22b
    ltac:(intros [|[|i]] p0 Hi; cbn in Hi; [injection Hi as <-; exact Hpu | discriminate | discriminate])
    ltac:(cbn; lia)) as HS2.
  remember (E07 regs2 q (shadow_addr F + 4) F c [pu]) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply E07_env).
  pose proof (env_agree07 regs2 q (shadow_addr F + 4) F c [pu]) as HAE2. rewrite <- HE2 in HAE2.
  assert (X33 : ew E2 33 = Z_to_bv 64 (shadow_addr F + 4)) by (rewrite HE2; apply (E07_ext _ _ _ _ _ _ 1); [lia | reflexivity]).
  assert (X34 : ew E2 34 = Z_to_bv 64 F) by (rewrite HE2; apply (E07_ext _ _ _ _ _ _ 2); [lia | reflexivity]).
  assert (X36 : ew E2 36 = Z_to_bv 64 pu) by (rewrite HE2; apply (E07_ext _ _ _ _ _ _ 4); [lia | reflexivity]).
  assert (EE10b : ew E2 10 = getr regs2 (Z_to_bv 5 10)) by (rewrite HE2; apply E07_reg; reflexivity).
  clear HE2.
  paj_run_sh RUNP HS2 HJ2'.
  { awr07. }
  mdv_set.
  assert (V2 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms0) a = rdW W2 mem2 a)
    by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
  clear HF HFr HG.
  pose proof (rc_range07 t) as Hrcr.
  psrr_branch_pi RUNP BR HS2.
  + (* a refusal code: the join *)
    rewrite (lt0_07 E2 10 (reply_code_a t)) in Hc by (try (rewrite EE10b; exact Ha0'); lia).
    apply Z.ltb_lt in Hc.
    paj_run_to_sh RUNTOP HS2 HJ2' (AF_verbs_receive + (0x8dae4 - 0x8d480)).
    { awr07. }
    mdv_set.
    assert (V3 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms1) a = rdW W2 mem2 a).
    { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V2 a Ha). }
    clear HF HFr HG.
    prreg HS2 (Z_to_bv 5 20) T20. prreg HS2 (Z_to_bv 5 27) T27.
    rewrite X34 in T20. rewrite X33 in T27.
    pose proof (kept_regs07 E2 _ _ regs2 _ [2; 3; 4; 8; 9; 18; 19; 22; 25] HS2 HAE2 ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    assert (Hrv3 : vr_rv (ms_regs ms1) (vr_base B e ++ vr_rl_hd e F q c 0x8dae4 tq)).
    { change (vr_rl_hd e F q c 0x8dae4 tq) with [(25, tq); (18, q); (19, c); (20, F); (22, F + 32); (27, shadow_addr F + 4)].
      apply rv_intro07. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
      - unfold vr_base in Hin. cbn in Hin.
        destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
          (rewrite KR2 by (cbn; tauto); apply (rv_get07 regs2 _ _ _ Hrv2); cbn; tauto).
      - cbn in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]; injection E1 as <- <-;
          first [exact T20 | exact T27 | rewrite KR2 by (cbn; tauto); apply (rv_get07 regs2 _ _ _ Hrv2); cbn; tauto]. }
    destruct (RUN07 e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ W2 regs2 (ms_regs ms1) mem2 (ms_mem ms1) md2 mdv1
      Hc2 Hl2 Hcp2 HJ2' V3 Hrv3 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) HDn)
      as (Hc3 & Hl3 & Hcp3).
    pmkst HS2.
    replace (BASE + 30208) with (vr_pc 0x8dae4) by (unfold vr_pc, AF_verbs_receive; lia).
    assert (ER : vr_R1 (e_R e) (e_D e) = R1).
    { unfold vr_R1. rewrite EH. cbn [fst]. destruct (Z.leb_spec 0 (reply_code_a t)); [lia | reflexivity]. }
    apply (exit_hd_e4 B MT e W2 tq O1 pos F q c tp lyc Sc (ms_regs ms1) (ms_mem ms1) mdv1 (k + EV_SUP_REPLY_CODE) nm).
    * exact Hnt.
    * lia.
    * rewrite EX. apply (astr_atR_agree (rdW W2 mem2) _ tq t n Hstr2); [unfold n; lia|].
      intros kk Hkk. apply V3. lia.
    * rewrite EX, ER, EQ. exact Hc3.
    * exact Hl3.
    * exact Hcp3.
  + (* a reply code: descriptors_add(tok[1]) *)
    rewrite (lt0_07 E2 10 (reply_code_a t)) in Hc by (try (rewrite EE10b; exact Ha0'); lia).
    apply Z.ltb_ge in Hc.
    paj_run_shc RUNP RUNC HS2 HJ2'.
    { awr07. }
    mdv_set.
    assert (V3 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms1) a = rdW W2 mem2 a).
    { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V2 a Ha). }
    clear HF HFr HG.
    prreg HS2 (Z_to_bv 5 1) Q1b. prreg HS2 (Z_to_bv 5 10) Q10b. prreg HS2 (Z_to_bv 5 20) T20. prreg HS2 (Z_to_bv 5 27) T27.
    rewrite X36 in Q10b. rewrite X34 in T20. rewrite X33 in T27.
    pose proof (kept_regs07 E2 _ _ regs2 _ [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26] HS2 HAE2
      ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    pmkst HS2.
    rewrite (SIGP CS_descriptors_add) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
    change (cmd_af CS_descriptors_add) with AF_descriptors_add.
    set (rl6 := [(18, q); (19, c); (20, F); (22, F + 32); (25, tq); (27, shadow_addr F + 4)]).
    assert (Hcs6 : cs07 rl6) by (unfold cs07, rl6; cs07_tac).
    assert (Hrv3 : vr_rv (ms_regs ms1) (vr_base B e ++ rl6)).
    { apply rv_intro07. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
      - unfold vr_base in Hin. cbn in Hin.
        destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
          (rewrite KR2 by (cbn; tauto); apply (rv_get07 regs2 _ _ _ Hrv2); cbn; tauto).
      - unfold rl6 in Hin. cbn in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]; injection E1 as <- <-;
          first [exact T20 | exact T27 | rewrite KR2 by (cbn; tauto); apply (rv_get07 regs2 _ _ _ Hrv2); cbn; tauto]. }
    destruct (RUN07 e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ W2 regs2 (ms_regs ms1) mem2 (ms_mem ms1) md2 mdv1
      Hc2 Hl2 Hcp2 HJ2' V3 Hrv3 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) HDn)
      as (Hc3 & Hl3 & Hcp3).
    pose proof Hc3 as (HJ3 & Hk3 & Hmet3 & Hnm3 & Hfr3 & Hrv3' & Hsv3 & Hsp3 & Henv3 & Hrec3 & Hdat3 & Hperm3 & Hq3).
    pose proof (proj1 HJ3) as HAR3.
    destruct (tok_blk07 B e F c tp lyc Sc W2 (ms_mem ms1) mdv1 R1 O1 [(tq, n); vr_lb e q; vr_cb e c] 1 pu u HAR3 Hcp3 Hrec3
      ltac:(right; right; left; reflexivity) Hperm3 Hpu Hu) as (Hub & Huap & Hus & Hul & Hpu4 & Hpu64 & Hu8).
    assert (Hstr3 : astr_atR (rdW W2 (ms_mem ms1)) tq t).
    { apply (astr_atR_agree (rdW W2 mem2) _ tq t n Hstr2); [unfold n; lia|]. intros kk Hkk. apply V3. lia. }
    assert (HV2 : DESCRIPTORS_ADD_STK = ltac:(let v := eval vm_compute in DESCRIPTORS_ADD_STK in exact v)) by reflexivity.
    assert (HEVd : 0 <= rec_spill_frees R1) by (unfold rec_spill_frees; destruct (Nat.ltb _ _); lia).
    eapply (CALL07 e pos F q c _ _ _ _ _ _ _ _ _ lyc Sc W2 (ms_regs ms1) (ms_mem ms1) mdv1 AF_descriptors_add
      DESCRIPTORS_ADD_STK _ (EV_DESCRIPTORS_ADD R1) _ _ _ Hent Hc3 Q1b).
    * lia.
    * reflexivity.
    * lia.
    * lia.
    * exact (fp_desc07 O1).
    * (* descriptors_add(tok[1]) *)
      intros ch HPRE.
      apply (TDESCRIPTORS_ADD lyc Sc W2 (ms_regs ms1) (ms_mem ms1) mdv1 ch pu (Some u) R1 O1 HPRE).
      -- exact (proj1 Henv3).
      -- exact (proj1 (proj2 (proj2 Henv3))).
      -- exact Q10b.
      -- lia.
      -- exists u. split; [reflexivity|]. split; [exact Hub|]. split; [exact Hus|]. split; [exact Hul | exact Huap].
      -- exact Hrec3.
      -- apply (ev07 B MT e _ lyc Sc W2 (ms_mem ms1) mdv1 (k + EV_SUP_REPLY_CODE) (EV_DESCRIPTORS_ADD R1) Hent HJ3). lia.
      -- unfold LIVE_DESCRIPTORS_ADD, LIVE_XSTRDUP, sarg. lia.
      -- apply (mok07 B MT MTL e Sc (k + EV_SUP_REPLY_CODE) nm 1 (rec_spill_frees R1) _ (EV_DESCRIPTORS_ADD R1) Hent Hmet3).
         ++ lia.
         ++ apply (xm_desc_le MT MTL R1 (Some u)). unfold sarg. lia.
         ++ unfold EV_DESCRIPTORS_ADD, EV_XSTRDUP. lia.
         ++ unfold EV_DESCRIPTORS_ADD, EV_XSTRDUP. lia.
    * (* after the return, 0x8dab0 *)
      intros ly4 S4 W4 regs4 mem4 md4 HJ4 HJc4 HP4 HK4.
      destruct HK4 as (O3 & HrecO3 & HO3 & Hkeep4 & Hcl4 & Hbb4 & Hmle4).
      destruct (rec_nodup07 B _ _ _ _ _ HrecO3) as (O4 & Hrec4 & HO4 & HndO4).
      pose proof (rv_keep07 B e (ms_regs ms1) regs4 _ Hrv3 Hcs6 HP4) as Hrv4.
      assert (Hmet4 : vr_meter MT e S4 (k + EV_SUP_REPLY_CODE + EV_DESCRIPTORS_ADD R1) (nm + 1)).
      { apply (meter_step MT MTL e Sc S4 (k + EV_SUP_REPLY_CODE) nm 1 (rec_spill_frees R1)
          (XM_DESCRIPTORS_ADD MT R1 (Some u)) (EV_DESCRIPTORS_ADD R1) Hmet3 Hmle4).
        - apply (xm_desc_le MT MTL R1 (Some u)). unfold sarg. lia.
        - unfold EV_DESCRIPTORS_ADD, EV_XSTRDUP. lia.
        - unfold EV_DESCRIPTORS_ADD, EV_XSTRDUP. lia. }
      assert (HO4b : forall x, In x O4 -> In x (ablocks B ly4 S4)).
      { intros x Hx. exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec4 Hx). }
      assert (Hperm4 : Permutation (ablocks B ly4 S4) (O4 ++ [(tq, n); vr_lb e q; vr_cb e c] ++ e_rest e)).
      { apply (perm_notext07 (ablocks B lyc Sc) (ablocks B ly4 S4) O1 O4 ([(tq, n); vr_lb e q; vr_cb e c] ++ e_rest e)).
        - exact (abl_nodup B _ _ _ _ _ (proj1 HJ4)).
        - exact Hperm3.
        - exact (Permutation_NoDup Hperm3 (abl_nodup B _ _ _ _ _ HAR3)).
        - exact HndO4.
        - intros x Hx. apply HO3. apply HO4. exact Hx.
        - intros x Hx. destruct (Hcl4 x Hx) as [H1|H1]; [left; exact H1 | right; apply HO4; exact H1].
        - exact Hkeep4.
        - exact HO4b. }
      assert (Hdat4 : ~ In (e_data e, Z.max (e_n e) 1) O4).
      { intros Hin. apply HO4 in Hin. destruct (HO3 _ Hin) as [H1|H1]; [exact (Hdat3 H1)|]. apply H1.
        pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HinD & HnotO & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _).
        assert (HinR : In (e_data e, Z.max (e_n e) 1) (e_rest e)).
        { pose proof (Permutation_in _ Hperm0 HinD) as H0. apply in_app_or in H0 as [H0|H0]; [contradiction | exact H0]. }
        apply (Permutation_in _ (Permutation_sym Hperm3)). apply in_or_app. right. apply in_or_app. right. exact HinR. }
      destruct (C07C e pos F q c tp [(tq, n); vr_lb e q; vr_cb e c] [(tq, n); vr_lb e q; vr_cb e c] _ rl6
        R1 (descriptors_add_m R1 (Some u)) O1 O4 (e_q0 e) (k + EV_SUP_REPLY_CODE) (k + EV_SUP_REPLY_CODE + EV_DESCRIPTORS_ADD R1)
        (vr_k1 (e_R e) (e_D e)) (vr_k1 (e_R e) (e_D e)) nm (nm + 1) VR_NM_HD VR_NM_HD
        lyc Sc W2 (ms_regs ms1) (ms_mem ms1) mdv1 ly4 S4 W4 regs4 mem4 md4 DESCRIPTORS_ADD_STK _ (EV_DESCRIPTORS_ADD R1)
        Hc3 Hl3 Hcp3 HJ4 HJc4 ltac:(lia) (fp_desc07 O1) (fun pn H1 H2 => Hkeep4 pn H1 H2)
        ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) HDn
        ltac:(lia) Hmet4 ltac:(unfold VR_NM_HD; lia) Hrv4 Hrec4 Hdat4 Hperm4)
        as (Hc4 & Hl4 & Hcp4).
      assert (Hstr4 : astr_atR (rdW W4 mem4) tq t).
      { apply (astr_atR_agree (rdW W2 (ms_mem ms1)) _ tq t n Hstr3); [unfold n; lia|]. intros kk Hkk.
        exact (blk07 B MT PROGU e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W2 (ms_regs ms1) (ms_mem ms1) mdv1
          DESCRIPTORS_ADD_STK (vr_s1 e) _ ly4 S4 W4 mem4 md4 (EV_DESCRIPTORS_ADD R1) tq n Hc3 HJc4
          (fp_desc07 O1) ltac:(left; reflexivity) (Hkeep4 _ Htin ltac:(exact (perm_tmp_notin B _ _ _ _ _ _ _ _ _ HAR3 Hperm3
            ltac:(left; reflexivity)))) kk ltac:(lia)). }
      (* 0x8dab0: j 0x8dae4 *)
      assert (R22c : getr regs4 (Z_to_bv 5 22) = w64 (F + 32)) by (apply (rv_get07 regs4 _ 22 _ Hrv4); unfold rl6; cbn; tauto).
      pose proof (seed_core B MT e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 30156 []
        Hc4 Hcp4 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) R22c
        ltac:(intros [|i] p0 Hi; discriminate) ltac:(cbn; lia)) as HS4.
      remember (E07 regs4 q (shadow_addr F + 4) F c []) as E4 eqn:HE4.
      assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply E07_env).
      pose proof (env_agree07 regs4 q (shadow_addr F + 4) F c []) as HAE4. rewrite <- HE4 in HAE4.
      clear HE4.
      pose proof Hc4 as (HJ4' & _).
      paj_run_to_sh RUNTOP HS4 HJ4' (AF_verbs_receive + (0x8dae4 - 0x8d480)).
      { awr07. }
      mdv_set.
      assert (V4 : forall a, 0 <= a < 2 ^ 64 -> rdW W4 (ms_mem ms2) a = rdW W4 mem4 a)
        by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
      clear HF HFr HG.
      pose proof (kept_regs07 E4 _ _ regs4 _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS4 HAE4
        ltac:(vm_compute; reflexivity)) as KR4.
      cbn [ms_regs restrict] in KR4.
      pose proof (ap_of_kept07 regs4 (ms_regs ms2) KR4) as HP5.
      assert (Hrv5 : vr_rv (ms_regs ms2) (vr_base B e ++ vr_rl_hd e F q c 0x8dae4 tq)).
      { apply (rv_sub07 _ _ _ (rv_keep07 B e regs4 (ms_regs ms2) rl6 Hrv4 Hcs6 HP5)).
        intros x Hx. change (vr_rl_hd e F q c 0x8dae4 tq) with [(25, tq); (18, q); (19, c); (20, F); (22, F + 32); (27, shadow_addr F + 4)] in Hx.
        apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx | right]. unfold rl6. cbn in Hx |- *. tauto. }
      destruct (RUN07 e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ W4 regs4 (ms_regs ms2) mem4 (ms_mem ms2) md4 mdv2
        Hc4 Hl4 Hcp4 HJ4' V4 Hrv5 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) HDn)
        as (Hc5 & Hl5 & Hcp5).
      pmkst HS4.
      replace (BASE + 30208) with (vr_pc 0x8dae4) by (unfold vr_pc, AF_verbs_receive; lia).
      assert (ER : vr_R1 (e_R e) (e_D e) = descriptors_add_m R1 (Some u)).
      { unfold vr_R1. rewrite EH. cbn [fst]. destruct (Z.leb_spec 0 (reply_code_a t)); [reflexivity | lia]. }
      apply (exit_hd_e4 B MT e W4 tq O4 pos F q c tp ly4 S4 (ms_regs ms2) (ms_mem ms2) mdv2
        (k + EV_SUP_REPLY_CODE + EV_DESCRIPTORS_ADD R1) (nm + 1)).
      -- exact Hnt.
      -- lia.
      -- rewrite EX. apply (astr_atR_agree (rdW W4 mem4) _ tq t n Hstr4); [unfold n; lia|].
         intros kk Hkk. apply V4. lia.
      -- rewrite EX, ER, EQ. exact Hc5.
      -- exact Hl5.
      -- exact Hcp5.
Qed.

End e.
End f.
End d.
