(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S09 PGET (0x8d934-0x8d944, 5 instructions) of the walk of verbs_receive
   on the ASan build of plugin-hostd/fuzz_command (interface lib/A/Prog/verbs_receive_iface.v, vr_s09_stmt):
     li a0,2; bne s5,a0,0x8da28; ld a0,8(s6); jal descriptors_panel_get; j 0x8dad4.
   With ntok <> 2 the step is reject and the run stops at the refusal stub 0x8da28 (vr_pr, at the entry's FP state);
   with ntok = 2 it is descriptors_panel_get(tok[1]) (descriptors_panel_get_c.v, FP-existential since statement
   pass 4) and the run reaches the join 0x8dad4 (vr_hd at the FP state fx' the call returns at, PaFx's fxrel fx fx'),
   through verbs_receive_s08_lib.v's generic arm vr_call_arm. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
descriptors_panel_get_c xstrdup_c answer_c hand_back_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_s08_lib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the model: the route RPget is the verb panel_get; with one argument the step is descriptors_panel_get, else reject *)
Lemma route_pget : forall tk, VRR.route tk = VRR.RPget -> exists args, tk = Verbs.Lit.verb_panel_get :: args.
Proof.
intros [|v args] H; [discriminate H|]. exists args. f_equal.
unfold VRR.route, VRR.route_mid, VRR.route_tail, VRR.route_conn, VRR.route_cd in H.
repeat match type of H with
| context [if ?b then _ else _] =>
    let Eb := fresh "Eb" in
    destruct b eqn:Eb; cbv beta iota in H; [first [discriminate H | apply Verbs.list_eqb_eq; exact Eb] |]
end.
destruct (Verbs.ledger_of v Verbs.Lit.instance_info_verbs); [discriminate H|].
destruct args as [|a [|b [|c r]]]; try discriminate H.
all: cbv beta iota in H;
  repeat match type of H with context [if ?b then _ else _] => destruct b; cbv beta iota in H end;
  discriminate H.
Qed.

Lemma pget_call : forall R D a, Verbs.toks D = [Verbs.Lit.verb_panel_get; a] ->
vr_h R D = (descriptors_panel_get_m R (Some a), false) /\ vr_k1 R D = 2 + EV_DESCRIPTORS_PANEL_GET R.
Proof.
intros R D a T.
assert (St : vr_st D = Verbs.SCall (Verbs.descriptors_panel_get a)).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. reflexivity. }
split.
- unfold vr_h. rewrite St. reflexivity.
- unfold vr_k1. rewrite St, T. reflexivity.
Qed.

Lemma pget_rej : forall R D, VRR.route (Verbs.toks D) = VRR.RPget -> length (Verbs.toks D) <> 2%nat ->
vr_h R D = (R, resp (-902), false) /\ vr_k1 R D = 2 + EV_SUP_RESP.
Proof.
intros R D Hr Hl. destruct (route_pget _ Hr) as (args & T).
assert (St : vr_st D = Verbs.reject).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. rewrite <- T, Hr, T. cbn [VRR.plan_at].
  destruct args as [|a [|b r]]; [reflexivity | rewrite T in Hl; cbn in Hl; lia | reflexivity]. }
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
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callee's contract at every FP state (verbs_receive_c.v:198) and the named record facts *)
Hypothesis TDESCRIPTORS_PANEL_GET : forall fx0 : YK11.FPState, @tdescriptors_panel_get_spec fx0 rc SK PI B MT.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).

Lemma ro_tok09 : Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) (ss_mem (ss_tok 0)).
Proof. repeat constructor; cbn; lia. Qed.

Lemma vr_s09 : vr_s09_stmt B MT.
Proof.
intros e W cf Hent Hrt.
destruct Hrt as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hne & Hcore & Hline & Hcopy).
pose proof Hcore as (HJ & _ & _ & _ & (EF & _) & Hrv & _ & _ & _ & Hrec & _ & Hperm & _).
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & _ & Hcalls & _).
pose proof (proj1 HJ) as HAR.
assert (R21 : getr regsc (Z_to_bv 5 21) = w64 (vr_ntok (e_D e)))
  by (apply (vr_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn; tauto).
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 (F + 32))
  by (apply (vr_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn; tauto).
assert (Hnt : 0 <= vr_ntok (e_D e) <= 64).
{ unfold vr_ntok, Verbs.toks, Verbs.line_words_max. rewrite length_firstn. lia. }
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR) as (Hf0 & Hfc & _).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
change (vr_pc (vr_route_pc VRR.RPget)) with (vr_pc 0x8d934).
replace (vr_pc 0x8d934) with (BASE + 0x7450) by (unfold vr_pc, AF_verbs_receive; lia).
unfold cfg_at, w64.
destruct (Nat.eq_dec (length (Verbs.toks (e_D e))) 2) as [H2 | H2].
- (* two words: descriptors_panel_get(tok[1]), then the jump to JB *)
  destruct (route_pget _ Hroute) as (args & T).
  destruct args as [|a [|b r]]; [rewrite T in H2; cbn in H2; lia | | rewrite T in H2; cbn in H2; lia].
  assert (HlenP : length tp = 2%nat) by (destruct Hcopy as (_ & (_ & HlenP & _)); rewrite HlenP, H2; reflexivity).
  destruct tp as [|p0 [|p1 [|p2 tp']]]; cbn in HlenP; try lia.
  destruct (vr_tok_arg B e F q c [p0; p1] lyc Sc W memc mdc 1 p1 a HAR Hperm Hcopy eq_refl
    ltac:(rewrite T; reflexivity)) as (_ & Hp1m & Hp14 & Hp1c & Ha8).
  assert (Hp1r : 0 <= p1 < 2 ^ 64) by lia.
  remember (Eimg (Ereg regsc [Z_to_bv 64 p1])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc [Z_to_bv 64 p1]) E) by (subst E; apply env_agree_Eimg).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (E22 : ew E 22 = Z_to_bv 64 (F + 32))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 22 (Z_to_bv 5 22) eq_refl), R22; reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 p1)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc [Z_to_bv 64 p1] 0)).
  assert (HS : st_ok_pi SEGS VAL E (ss_tok 0x7450)
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 0x7450)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_tok. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E22. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (F + 32) 8 8 (SOff 32 0) p1).
      + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      + lia.
      + lia.
      + change (N.to_nat 8) with 8%nat. replace (F + 32 + 8) with (F + 32 + 8 * Z.of_nat 1) by lia.
        apply val_mem_of_aval. exact Hp1m.
    - cbn. tauto.
    - split; [exact I | split; exact I]. }
  clear HE.
  (* 0x8d934: li a0,2 *)
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_tok09) as Eq1. clear HF HFr HG.
  (* 0x8d938: bne s5,a0,0x8da28 *)
  psrr_branch_pi RUNP BR HS.
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    unfold vr_ntok in Hc. rewrite H2 in Hc. vm_compute in Hc. discriminate Hc.
  + (* 0x8d93c: ld a0,8(s6); 0x8d940: jal descriptors_panel_get *)
    paj_run_shc RUNP RUNC HS HJ.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_tok09) as Eq2. clear HF HFr HG.
    pose proof (fun x => eq_trans (Eq2 x) (Eq1 x)) as Eq.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. rewrite E32 in Q10.
    pose proof (kept_regs_st_ok E _ _ regsc [Z_to_bv 64 p1] [2; 3; 4; 8; 9; 18; 21; 22] HS HAE
      ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    pmkst HS.
    rewrite (SIGP CS_descriptors_panel_get) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
    change (cmd_af CS_descriptors_panel_get) with AF_descriptors_panel_get.
    assert (Hcs : vr_cs B MT e pos F q c p1 0x7460 [p0; p1] lyc Sc W (ms_regs ms0) (ms_mem ms0) mdv2 k nm).
    { split; [|split; [exact (vr_line_same B e q W memc W (ms_mem ms0) Eq Hline)
                     | exact (vr_copy_same B e F c [p0; p1] W memc W (ms_mem ms0) Eq Hcopy)]].
      eapply vr_core_same; [exact Hcore | exact HJ | exact Eq |].
      apply (vr_rv_keep B e (ms_regs ms0) regsc _ _ Hrv).
      - intros r0 Hr0. apply KR. cbn in Hr0 |- *. tauto.
      - intros r0 v Hin. cbn in Hin. destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-.
        + right. exact Q1.
        + right. exact Q10.
        + left. split; [cbn; tauto | apply KR; cbn; tauto].
        + left. split; [cbn; tauto | apply KR; cbn; tauto]. }
    assert (Ht : (length (snd (descriptors_panel_get_m (e_R e) (Some a))) <= 28)%nat).
    { unfold descriptors_panel_get_m, daemon_shape. apply stub_len. exact (rec_code_range B _ _ _ _ _ Hrec). }
    eapply SRr_mono.
    { apply (vr_call_arm B MT HB MTL ROA RRO RPG RECC PROGU e W pos F q c p1 0x7460 [p0; p1] lyc Sc
        (ms_regs ms0) (ms_mem ms0) mdv2 k nm AF_descriptors_panel_get DESCRIPTORS_PANEL_GET_STK (EV_DESCRIPTORS_PANEL_GET (e_R e))
        (XM_DESCRIPTORS_PANEL_GET MT (e_R e) (Some a)) (LIVE_DESCRIPTORS_PANEL_GET (e_R e) (Some a))
        (descriptors_panel_get_m (e_R e) (Some a)) Hent Hcs H2).
      - exact (proj1 (pget_call (e_R e) (e_D e) a T)).
      - exact (proj2 (pget_call (e_R e) (e_D e) a T)).
      - unfold EV_DESCRIPTORS_PANEL_GET, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP. rewrite (spill_frees0 _ Hcalls). lia.
      - unfold XM_DESCRIPTORS_PANEL_GET, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. rewrite (spill_frees0 _ Hcalls). cbn [sarg].
        pose proof (mo_malloc_mono MT MTL (Z.of_nat (length a) + 1) VERBS_RECEIVE_REQ
          ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M1.
        pose proof (mo_malloc_mono MT MTL (Z.of_nat (length (snd (descriptors_panel_get_m (e_R e) (Some a)))) + 1)
          VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M2.
        lia.
      - unfold LIVE_DESCRIPTORS_PANEL_GET, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP, VERBS_RECEIVE_REQ. cbn [sarg]. lia.
      - assert (HV : DESCRIPTORS_PANEL_GET_STK = ltac:(let v := eval vm_compute in DESCRIPTORS_PANEL_GET_STK in exact v))
          by reflexivity. lia.
      - assert (HV : DESCRIPTORS_PANEL_GET_STK = ltac:(let v := eval vm_compute in DESCRIPTORS_PANEL_GET_STK in exact v))
          by reflexivity.
        assert (HV2 : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v))
          by reflexivity. lia.
      - lia.
      - reflexivity.
      - vm_compute; reflexivity.
      - intros ch HPRE1 HF0 H1 H2' H3 H4 H5 H6 H7.
        destruct (vr_tok_arg B e F q c [p0; p1] lyc Sc W (ms_mem ms0) mdv2 1 p1 a (proj1 HJ) Hperm
          (vr_copy_same B e F c [p0; p1] W memc W (ms_mem ms0) Eq Hcopy) eq_refl ltac:(rewrite T; reflexivity))
          as (Harg & _).
        exact (TDESCRIPTORS_PANEL_GET fx lyc Sc W (ms_regs ms0) (ms_mem ms0) mdv2 ch p1 (Some a) (e_R e) (e_O e)
          HPRE1 HF0 H1 H2' Q10 Hp1r (ex_intro _ a (conj eq_refl Harg)) H3 H4 H5 H6 H7). }
    intros W' c' _ (fq & Hfq & H). exists fq. split; [exact Hfq|]. right. exact H.
- (* not two words: the refusal stub 0x8da28 *)
  pose proof (pget_rej (e_R e) (e_D e) Hroute H2) as Hrj.
  remember (Eimg (Ereg regsc [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply env_agree_Eimg).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (HS : st_ok_pi SEGS VAL E (ss_ret 0x7450)
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 0x7450)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_ret. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  clear HE.
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq1. clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  + paj_run_to_shc RUNTO HS HJ 0x7544.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    pose proof (rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq2. clear HF HFr HG.
    pose proof (fun x => eq_trans (Eq2 x) (Eq1 x)) as Eq.
    pose proof (kept_regs_st_ok E _ _ regsc [] [2; 3; 4; 8; 9; 18; 21; 22] HS HAE
      ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply SRr_ret. cbv beta. exists fx. split; [apply fxrel_refl|]. left. unfold vrF_pr, vr_atpr.
    replace (BASE + 30020) with (vr_pc 0x8da28) by (unfold vr_pc, AF_verbs_receive; lia).
    apply (vr_pr_build B MT e W pos F q c tp lyc Sc (ms_regs ms0) (ms_mem ms0) mdv2 k nm
      (proj1 Hrj) (proj2 Hrj) Hne).
    * eapply vr_core_same; [exact Hcore | exact HJ | exact Eq |].
      apply (vr_rv_keep B e (ms_regs ms0) regsc _ _ Hrv).
      -- intros r0 Hr0. apply KR. cbn in Hr0 |- *. tauto.
      -- intros r0 v Hin. left. cbn in Hin. destruct Hin as [E1|[E1|[E1|[]]]]; injection E1 as <- <-;
         (split; [cbn; tauto | apply KR; cbn; tauto]).
    * exact (vr_line_same B e q W memc W (ms_mem ms0) Eq Hline).
    * exact (vr_copy_same B e F c tp W memc W (ms_mem ms0) Eq Hcopy).
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    change (U E (SLit 2)) with 2 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold vr_ntok in Hc. lia.
Qed.

End e.
End f.
End d.
