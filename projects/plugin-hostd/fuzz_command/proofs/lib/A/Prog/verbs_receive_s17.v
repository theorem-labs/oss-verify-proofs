(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S17 POOL (0x8dc74-0x8dc90, 8 instructions) of the walk of
   verbs_receive on the ASan build of plugin-hostd/fuzz_command (interface lib/A/Prog/verbs_receive_iface.v,
   vr_s17_stmt):
     li a0,3; bne s5,a0,0x8dc9c; ld s9,8(s6); ld a0,16(s6); jal wrapper_atoi; mv a1,a0; mv a0,s9;
     jal sup_pool_config (returning at the join 0x8dc94).
   With ntok <> 3 the step is reject and the run stops at the refusal stub 0x8dc9c (vr_pr, verbs_receive_s14_k.v
   vr_pr9c_of). With ntok = 3 the run calls the atoi wrapper on tok[2] (RtNumber.v's aatoi_realizes through
   PaArt.aj_art_at: the wrapper writes its window below s1 and the errno cell, verbs_receive_s17_x.v carries the
   boundary facts across), then sup_pool_config(tok[1], atoi_a tok[2]) (sup_pool_config_c.v) through the shared arm
   vr_call_join (verbs_receive_s14_c.v), whose return pc is the join 0x8dc94 itself (vr_hd, at the FP state the callee
   returns at: statement pass 4, the exit is vr_segF's). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
sup_pool_config_c sup_reply_code_c arg_i_c xstrdup_c answer_c hand_back_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
verbs_receive_s14_k verbs_receive_s14_j verbs_receive_s14_c verbs_receive_s14_r verbs_receive_s17_x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

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
(* the callee's contract and the atoi entry at every FP state (verbs_receive_c.v:217, :242) and the record facts *)
Hypothesis TSUP_POOL_CONFIG : forall fx0 : YK11.FPState, @tsup_pool_config_spec fx0 rc SK PI B MT.
Hypothesis AATOI : forall fx0 : YK11.FPState, @RtNumber.aatoi_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis BLKT : vr_blktail B.
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
Let ART := aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL).

Lemma vr_s17 : vr_s17_stmt B MT.
Proof.
intros e W cf Hent Hrt.
destruct Hrt as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hne & Hcore & Hline & Hcopy).
pose proof Hcore as (HJ & _ & _ & _ & (EF & _) & Hrv & _ & _ & _ & Hrec & _ & Hperm & _).
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & HlenD & _ & _ & _ & _ & _ & Hcalls & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H470 & _).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (R21 : getr regsc (Z_to_bv 5 21) = w64 (vr_ntok (e_D e)))
  by (apply (v14_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn; tauto).
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 (F + 32))
  by (apply (v14_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn; tauto).
assert (Hnt : 0 <= vr_ntok (e_D e) <= 64).
{ unfold vr_ntok, Verbs.toks, Verbs.line_words_max. rewrite length_firstn. lia. }
assert (Hin4 : In (4, pos) (frames Sc)) by (pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _); rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
change (vr_pc (vr_route_pc VRR.RPool)) with (vr_pc 0x8dc74).
replace (vr_pc 0x8dc74) with (BASE + 30608) by (unfold vr_pc, AF_verbs_receive; lia).
unfold cfg_at, w64.
destruct (Nat.eq_dec (length (Verbs.toks (e_D e))) 3) as [H3 | H3].
- (* three words: atoi(tok[2]), sup_pool_config(tok[1], its value), returning at the join 0x8dc94 *)
  case_eq (Verbs.toks (e_D e)); [intros T; exfalso; exact (Hne T) | intros v args T].
  destruct args as [|a [|b [|x r]]]; [rewrite T in H3; cbn in H3; lia | rewrite T in H3; cbn in H3; lia | |
    rewrite T in H3; cbn in H3; lia].
  destruct (pool_facts (e_R e) (e_D e) v [a; b] T Hroute) as [Hcall _].
  destruct (Hcall a b eq_refl) as [Hh Hk1]. clear Hcall.
  assert (HlenP : length tp = 3%nat) by (destruct Hcopy as (_ & (_ & HlenP & _)); rewrite HlenP, T; reflexivity).
  destruct tp as [|p0 [|p1 [|p2 [|p3 tp']]]]; cbn in HlenP; try lia.
  destruct (tok_argB B e F c [p0; p1; p2] lyc Sc W memc mdc q 1 p1 a HAR Hperm Hcopy eq_refl
    ltac:(rewrite T; reflexivity)) as (_ & Hp1m & Hp14 & Hp1c & Ha8).
  destruct (tok_argB B e F c [p0; p1; p2] lyc Sc W memc mdc q 2 p2 b HAR Hperm Hcopy eq_refl
    ltac:(rewrite T; reflexivity)) as (_ & Hp2m & Hp24 & Hp2c & Hb8).
  assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. right; left; reflexivity. }
  assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. left; reflexivity. }
  destruct (vr_o_facts e Hal16) as [Hs1o Ho].
  assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
  assert (HES : ESTACK = ltac:(let v := eval vm_compute in ESTACK in exact v)) by reflexivity.
  remember (Eimg (Ereg regsc [Z_to_bv 64 p1; Z_to_bv 64 p2])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc [Z_to_bv 64 p1; Z_to_bv 64 p2]) E) by (subst E; apply v14_env_agree).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (E22 : ew E 22 = Z_to_bv 64 (F + 32))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 22 (Z_to_bv 5 22) eq_refl), R22; reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 p1)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc [Z_to_bv 64 p1; Z_to_bv 64 p2] 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 p2)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc [Z_to_bv 64 p1; Z_to_bv 64 p2] 1)).
  assert (HS : st_ok_pi SEGS VAL E (mkSS 30608 sr_atoms [v14_tok2_r 32 33] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 30608)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold v14_tok2_r. apply Forall_cons; [|apply Forall_nil].
      unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E22, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho'; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (chunk_ok_val SEGS E _ (F + 32) 8 8 (SOff 32 0) p1).
        * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        * lia.
        * lia.
        * change (N.to_nat 8) with 8%nat. replace (F + 32 + 8) with (F + 32 + 8 * Z.of_nat 1) by lia.
          apply v14_val_mem_of_aval. exact Hp1m.
      + apply (chunk_ok_val SEGS E _ (F + 32) 16 8 (SOff 33 0) p2).
        * cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        * lia.
        * lia.
        * change (N.to_nat 8) with 8%nat. replace (F + 32 + 16) with (F + 32 + 8 * Z.of_nat 2) by lia.
          apply v14_val_mem_of_aval. exact Hp2m.
    - cbn. tauto.
    - split; [exact I | split; exact I]. }
  clear HE.
  assert (Hro : Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) [v14_tok2_r 32 33])
    by (unfold v14_tok2_r; repeat constructor; cbn; lia).
  (* 0x8dc74: li a0,3 *)
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (rd_same_of_frame E _ W memc (ms_mem ms) Hro HFr) as Eq1. clear HF HFr HG.
  (* 0x8dc78: bne s5,a0,0x8dc9c *)
  psrr_branch_pi RUNP BR HS.
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    unfold vr_ntok in Hc. rewrite H3 in Hc. vm_compute in Hc. discriminate Hc.
  + (* 0x8dc7c: ld s9,8(s6); 0x8dc80: ld a0,16(s6); 0x8dc84: jal wrapper_atoi *)
    paj_run_shc RUNP RUNC HS HJ.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    pose proof (rd_same_of_frame E _ W (ms_mem ms) (ms_mem ms0) Hro HFr) as Eq2. clear HF HFr HG.
    pose proof (fun x => eq_trans (Eq2 x) (Eq1 x)) as Eq.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (25%bv : bv 5) Q25.
    rewrite E33 in Q10. rewrite E32 in Q25.
    pose proof (v14_kept_regs E _ _ regsc [Z_to_bv 64 p1; Z_to_bv 64 p2]
      [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    pmkst HS.
    assert (Q2 : getr (ms_regs ms0) 2 = w64 (vr_s1 e)).
    { etransitivity; [exact (KR 2 ltac:(cbn; tauto))|]. apply (v14_rv_get regsc _ 2 _ Hrv). apply in_or_app; left; cbn; tauto. }
    assert (Q3 : getr (ms_regs ms0) 3 = w64 (as_gp B)).
    { etransitivity; [exact (KR 3 ltac:(cbn; tauto))|]. apply (v14_rv_get regsc _ 3 _ Hrv). apply in_or_app; left; cbn; tauto. }
    assert (Q4 : getr (ms_regs ms0) 4 = w64 (as_tp B)).
    { etransitivity; [exact (KR 4 ltac:(cbn; tauto))|]. apply (v14_rv_get regsc _ 4 _ Hrv). apply in_or_app; left; cbn; tauto. }
    assert (Qsp : spZ (ms_regs ms0) = vr_sp0 e + (vr_s1 e - vr_sp0 e)).
    { unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
    assert (Hra : YK0s.ret_ok (getr (ms_regs ms0) 1))
      by (rewrite Q1; apply ret_ok_codeptr_v; first [lia | reflexivity | vm_compute; reflexivity]).
    pose proof (proj1 HJ) as HAR1.
    pose proof (vr_env_of_journal B MT RRO RPG RECC ROA e _ _ _ _ _ _ _ Hent HJ) as (HRO1 & _ & _ & Hgd1 & Hfl1 & (ev & Herr1)).
    pose proof (vr_copy_same B e F c [p0; p1; p2] W memc (ms_mem ms0) Eq Hcopy) as HcopyA.
    pose proof HcopyA as (_ & (_ & _ & _ & HwA)).
    destruct (HwA 2%nat p2 b eq_refl ltac:(rewrite T; reflexivity)) as (A1 & A2 & A3 & A4).
    pose proof (ecall_pre_stk_at SEGS B (3 * ESTACK) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e)
      (e_mem e) (e_md e) [(4, pos)] lyc Sc W (ms_mem ms0) mdv2 k (ms_regs ms0) (vr_s1 e - vr_sp0 e) HJ Qsp Hs1o
      ltac:(lia) ltac:(lia) ltac:(lia) Hra Q3 Q4) as HPRE1.
    (* the atoi wrapper on tok[2] *)
    eapply SRr_bind.
    { eapply (ART (3 * ESTACK) (aerrno_cell B) _ W (ms_regs ms0) (ms_mem ms0) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e)
        (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdv2 k (vr_s1 e - vr_sp0 e) _ _ HJ);
        [exact Qsp | exact Hs1o | lia | lia | lia | exact Q1 | intros a0 Ha0; exact Ha0 |].
      apply (AATOI fx lyc Sc W (ms_regs ms0) (ms_mem ms0) mdv2 p2 b ev Hfl1 Hgd1 HPRE1 Q10 ltac:(lia)).
      - apply astr_atR_view. exact A1.
      - apply (aread_ok_of_block SEGS B LAWS (3 * ESTACK) lyc Sc W (ms_regs ms0) (ms_mem ms0) mdv2 c
          (Z.of_nat (length (Verbs.line (e_D e))) + 1) p2 (astr_len b + 1) HAR1 Hcb); unfold astr_len; [lia | lia | lia |].
        rewrite Qsp. lia.
      - apply (amem8_of_blockA SEGS B LAWS lyc Sc W (ms_mem ms0) mdv2); [exact HAR1 | | unfold astr_len; lia].
        exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1). split; [exact Hcb | unfold astr_len; lia].
      - unfold astr_len. apply (BLKT lyc Sc W (ms_mem ms0) mdv2 c (Z.of_nat (length (Verbs.line (e_D e))) + 1));
          [exact HAR1 | exact Hcb | lia].
      - exact Herr1.
      - (* tok[2] apart from the errno cell: its bytes are in the copy block, not image bytes (blk_img); the
           errno cell's are (api_env) *)
        pose proof (pal_env B TL) as (_ & Hzi & _).
        destruct (Z_le_gt_dec (p2 + astr_len b + 1) (as_errno B)) as [Hz1|Hz1]; [left; exact Hz1|].
        destruct (Z_le_gt_dec (as_errno B + 4) p2) as [Hz2|Hz2]; [right; exact Hz2|]. exfalso.
        apply (blk_img SEGS B LAWS lyc Sc W (ms_mem ms0) mdv2 c (Z.of_nat (length (Verbs.line (e_D e))) + 1)
          (Z.max p2 (as_errno B)) HAR1 Hcb); [| apply Hzi; clear - Hz1 Hz2; lia].
        unfold req_size. destruct (Z.eqb_spec (Z.of_nat (length (Verbs.line (e_D e))) + 1) 0) as [Hzk|Hzk]; cbv iota;
          clear - A3 A4 Hz1 Hzk; unfold astr_len in Hz1; lia.
      - exact (vr_rtrom_ok B W (ms_mem ms0) HRO1). }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HA0 & _) & HK2).
    (* 0x8dc88: mv a1,a0; 0x8dc8c: mv a0,s9; 0x8dc90: jal sup_pool_config, from a state that names only the registers *)
    remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
    assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
    assert (HAE2 : env_agree 32 (Ereg regs2 []) E2) by (subst E2; apply v14_env_agree).
    assert (E2_10 : ew E2 10 = getr regs2 (Z_to_bv 5 10))
      by (subst E2; exact (ew_Eimg_Ereg_nat regs2 _ 10 (Z_to_bv 5 10) eq_refl)).
    assert (E2_25 : ew E2 25 = getr regs2 (Z_to_bv 5 25))
      by (subst E2; exact (ew_Eimg_Ereg_nat regs2 _ 25 (Z_to_bv 5 25) eq_refl)).
    assert (HS2 : st_ok_pi SEGS VAL E2 (mkSS 30628 sr_atoms [] None (mkFacts [] [] []))
      (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + 30628)) mem2 (seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
      - subst E2. apply regs_ok_Eimg_Ereg.
      - reflexivity.
      - constructor.
      - exact I.
      - split; [exact I | split; exact I]. }
    clear HE2.
    paj_run_shc RUNP RUNC HS2 HJ2.
    { awr_ok_tac. }
    match goal with |- context [with_vm_backing (m_vm_lazy md2) ?mt md2] =>
      set (mdv3 := with_vm_backing (m_vm_lazy md2) mt md2) in * end.
    clearbody mdv3.
    pose proof (rd_same_of_frame E2 [] W mem2 (ms_mem ms1) (Forall_nil _) HFr) as Eq3. clear HF HFr HG.
    prreg HS2 (1%bv : bv 5) Q1b. prreg HS2 (10%bv : bv 5) Q10b. prreg HS2 (11%bv : bv 5) Q11b.
    rewrite E2_25 in Q10b. rewrite E2_10 in Q11b.
    pose proof (v14_kept_regs E2 _ _ regs2 [] [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] HS2 HAE2
      ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
    pmkst HS2.
    rewrite (SIGP CS_sup_pool_config) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
    change (cmd_af CS_sup_pool_config) with AF_sup_pool_config.
    assert (KRall : forall r, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] ->
      getr (ms_regs ms1) (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)).
    { intros r0 Hr0.
      rewrite (KR2 r0 Hr0).
      rewrite (HP2 r0 ltac:(unfold acallee_saved; cbn in Hr0; lia)).
      exact (KR r0 Hr0). }
    assert (P10 : getr (ms_regs ms1) 10 = w64 p1).
    { etransitivity; [exact Q10b|]. rewrite (HP2 25 ltac:(unfold acallee_saved; lia)). exact Q25. }
    assert (P11 : getr (ms_regs ms1) 11 = w64 (atoi_a b)).
    { etransitivity; [exact Q11b|]. exact HA0. }
    assert (Hra2 : getr (ms_regs ms1) 1 = Z_to_bv 64 (vr_pc 0x8dc94)).
    { etransitivity; [exact Q1b|]. unfold vr_pc, AF_verbs_receive. f_equal; lia. }
    assert (KX : v17_kx B e W memc (ms_mem ms1)).
    { intros a0 Ha0 Hb Hn. rewrite (Eq3 a0), (HK2 a0 Ha0); [exact (Eq a0) | | exact Hn]. lia. }
    assert (Hsl : Forall (fun ov => 0 <= fst ov <= 200) (vr_sl3 F q c))
      by (unfold vr_sl3; repeat constructor; cbn [fst]; lia).
    assert (Hrv1 : vr_rv (ms_regs ms1) (vr_base B e ++ [(18, q); (20, F); (22, F + 32); (27, shadow_addr F + 4)])).
    { apply (v14_rv_keep B e (ms_regs ms1) regsc _ _ Hrv).
      - intros r0 Hr0. apply KRall. cbn in Hr0 |- *. tauto.
      - intros r0 v0 Hin. left. cbn in Hin. destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-;
        (split; [cbn; tauto | apply KRall; cbn; tauto]). }
    pose proof (v17_core_kx B MT RRO RPG RECC ROA PROGU TL e pos F _ _ _ _ _ _ _ _ k _ nm _ lyc Sc W regsc memc mdc
      (ms_regs ms1) (ms_mem ms1) mdv3 Hent Hcore HJ2 KX Hsl Hrv1) as Hcore1.
    pose proof (v17_line_kx B MT TL e q lyc Sc W memc mdc (ms_mem ms1) Hent HAR Hlb Hline KX) as Hline1.
    pose proof (v17_copy_kx B TL e F c [p0; p1; p2] pos lyc Sc W memc mdc (ms_mem ms1) HAR Hin4 EF Hcb Hcopy KX) as Hcopy1.
    destruct (tok_argB B e F c [p0; p1; p2] lyc Sc W (ms_mem ms1) mdv3 q 1 p1 a (proj1 HJ2) Hperm Hcopy1 eq_refl
      ltac:(rewrite T; reflexivity)) as (Harg1 & _).
    assert (Hid : -2 ^ 31 <= atoi_a b < 2 ^ 31) by (unfold atoi_a; apply v17_swrap32_range).
    destruct (v14_pool_budget MT MTL (e_R e) a (atoi_a b) Hcalls (v14_code_range B _ _ _ _ _ Hrec) Ha8 Hid)
      as (HEV & HXM & HLV).
    assert (HV1 : SUP_POOL_CONFIG_STK = ltac:(let v := eval vm_compute in SUP_POOL_CONFIG_STK in exact v))
      by reflexivity.
    eapply SRr_mono.
    { apply (vr_call_join B MT RRO RPG RECC ROA MTL PROGU HB e W pos F q c [p0; p1; p2] lyc Sc (ms_regs ms1) (ms_mem ms1)
        mdv3 k nm _ (ms_mem ms1) mdv3 (ms_regs ms1) SUP_POOL_CONFIG_STK (EV_SUP_POOL_CONFIG (e_R e))
        (XM_SUP_POOL_CONFIG MT (e_R e) (Some a) (atoi_a b)) (LIVE_SUP_POOL_CONFIG (e_R e) (Some a) (atoi_a b))
        (sup_pool_config_m (e_R e) (Some a) (atoi_a b)) 4 1 0x8dc94 _
        Hent ltac:(lia) Hcore1 Hline1 Hcopy1 (fun x => eq_refl) HJ2 Hrv1 Hra2 ltac:(unfold AF_verbs_receive; lia)
        ltac:(unfold AF_verbs_receive; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        HXM HLV Hh Hk1).
      intros ch1 Hpre Hfrm Haro Hcro Hrec' Hfr Hev Hlv Hmo.
      exact (TSUP_POOL_CONFIG fx lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv3 ch1 p1 (atoi_a b) (Some a) (e_R e) (e_O e)
        Hpre Hfrm Haro Hcro P10 ltac:(lia) P11 Hid (ex_intro _ a (conj eq_refl Harg1)) Hrec' Hfr Hev Hlv Hmo). }
    intros W3 c3 _ (fq & Hfq & H4). exists fq. split; [exact Hfq|]. right. exact (vr_hdx_hd (fx := fq) B MT e W3 c3 H4).
- (* not three words: the refusal stub 0x8dc9c *)
  case_eq (Verbs.toks (e_D e)); [intros T; exfalso; exact (Hne T) | intros v args T].
  destruct (pool_facts (e_R e) (e_D e) v args T Hroute) as [_ Hrej].
  destruct (Hrej ltac:(rewrite T in H3; cbn in H3; lia)) as [Hh Hk1]. clear Hrej.
  remember (Eimg (Ereg regsc [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply v14_env_agree).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (HS : st_ok_pi SEGS VAL E (mkSS 30608 sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 30608)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  clear HE.
  (* 0x8dc74: li a0,3 *)
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (rd_same_of_frame E [] W memc (ms_mem ms) (Forall_nil _) HFr) as Eq1. clear HF HFr HG.
  (* 0x8dc78: bne s5,a0,0x8dc9c *)
  psrr_branch_pi RUNP BR HS.
  + paj_run_to_shc RUNTO HS HJ 30648.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    pose proof (rd_same_of_frame E [] W (ms_mem ms) (ms_mem ms0) (Forall_nil _) HFr) as Eq2. clear HF HFr HG.
    pose proof (fun x => eq_trans (Eq2 x) (Eq1 x)) as Eq.
    pose proof (v14_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] HS HAE
      ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    pmkst HS.
    assert (Hrvp : vr_rv (ms_regs ms0) (vr_base B e ++ vr_rl_pr e F q c 0x8dc9c (-902))).
    { change (vr_rl_pr e F q c 0x8dc9c (-902))
        with [(18, q); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)].
      apply (v14_rv_keep B e (ms_regs ms0) regsc _ _ Hrv).
      - intros r0 Hr0. apply KR. cbn in Hr0 |- *. tauto.
      - intros r0 v0 Hin. left. cbn in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
        (split; [cbn; tauto | apply KR; cbn; tauto]). }
    apply SRr_ret. exists fx. split; [apply fxrel_refl|]. left.
    replace (BASE + 30648) with (vr_pc 0x8dc9c) by (unfold vr_pc, AF_verbs_receive; lia).
    exact (vr_pr9c_of B MT RRO RPG RECC ROA e W pos F q c tp lyc Sc regsc memc mdc k nm VRR.RPool
      (ms_regs ms0) (ms_mem ms0) mdv2 Hent Hroute Hne Hcore Hline Hcopy Eq HJ Hrvp Hh Hk1).
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    change (U E (SLit 3)) with 3 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold vr_ntok in Hc. lia.
Qed.

End e.
End f.
End d.
