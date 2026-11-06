(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S16 LV2 (0x8dc5c-0x8dc70, 6 instructions) of the walk of
   verbs_receive on the ASan build of plugin-hostd/fuzz_command (interface lib/A/Prog/verbs_receive_iface.v,
   vr_s16_stmt):
     li a0,3; bne s5,a0,0x8dc9c; ld a0,8(s6); ld a1,16(s6); jal sup_lv2_worker_set; j 0x8dc94.
   With ntok <> 3 the step is reject and the run stops at the refusal stub 0x8dc9c (vr_pr, verbs_receive_s14_k.v
   vr_pr9c_of); with ntok = 3 the step is sup_lv2_worker_set(tok[1], tok[2]) (sup_lv2_worker_set_c.v), called through the
   shared arm vr_call_join (verbs_receive_s14_c.v), and the jump at the return reaches the join 0x8dc94 (vr_hd,
   vr_jump) at the FP state the callee returns at (statement pass 4: the exit is vr_segF's). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
sup_lv2_worker_set_c xstrdup_c answer_c hand_back_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
verbs_receive_s14_k verbs_receive_s14_j verbs_receive_s14_c verbs_receive_s14_r.
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
(* the callee's contract at every FP state (verbs_receive_c.v:214) and the named record facts *)
Hypothesis TSUP_LV2_WORKER_SET : forall fx0 : YK11.FPState, @tsup_lv2_worker_set_spec fx0 rc SK PI B MT.
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

Lemma vr_s16 : vr_s16_stmt B MT.
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
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR) as (Hf0 & Hfc & _).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
change (vr_pc (vr_route_pc VRR.RLv2)) with (vr_pc 0x8dc5c).
replace (vr_pc 0x8dc5c) with (BASE + 30584) by (unfold vr_pc, AF_verbs_receive; lia).
unfold cfg_at, w64.
destruct (Nat.eq_dec (length (Verbs.toks (e_D e))) 3) as [H3 | H3].
- (* three words: sup_lv2_worker_set(tok[1], tok[2]), then the jump to 0x8dc94 *)
  case_eq (Verbs.toks (e_D e)); [intros T; exfalso; exact (Hne T) | intros v args T].
  destruct args as [|a [|b [|x r]]]; [rewrite T in H3; cbn in H3; lia | rewrite T in H3; cbn in H3; lia | |
    rewrite T in H3; cbn in H3; lia].
  destruct (lv2_facts (e_R e) (e_D e) v [a; b] T Hroute) as [Hcall _].
  destruct (Hcall a b eq_refl) as [Hh Hk1]. clear Hcall.
  assert (HlenP : length tp = 3%nat) by (destruct Hcopy as (_ & (_ & HlenP & _)); rewrite HlenP, T; reflexivity).
  destruct tp as [|p0 [|p1 [|p2 [|p3 tp']]]]; cbn in HlenP; try lia.
  destruct (tok_argB B e F c [p0; p1; p2] lyc Sc W memc mdc q 1 p1 a HAR Hperm Hcopy eq_refl
    ltac:(rewrite T; reflexivity)) as (_ & Hp1m & Hp14 & Hp1c & Ha8).
  destruct (tok_argB B e F c [p0; p1; p2] lyc Sc W memc mdc q 2 p2 b HAR Hperm Hcopy eq_refl
    ltac:(rewrite T; reflexivity)) as (_ & Hp2m & Hp24 & Hp2c & Hb8).
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
  assert (HS : st_ok_pi SEGS VAL E (mkSS 30584 sr_atoms [v14_tok2_r 32 33] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 30584)) memc (seg_rom SEGS)))).
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
  (* 0x8dc5c: li a0,3 *)
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (rd_same_of_frame E _ W memc (ms_mem ms) Hro HFr) as Eq1. clear HF HFr HG.
  (* 0x8dc60: bne s5,a0,0x8dc9c *)
  psrr_branch_pi RUNP BR HS.
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    unfold vr_ntok in Hc. rewrite H3 in Hc. vm_compute in Hc. discriminate Hc.
  + (* 0x8dc64: ld a0,8(s6); 0x8dc68: ld a1,16(s6); 0x8dc6c: jal sup_lv2_worker_set *)
    paj_run_shc RUNP RUNC HS HJ.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    pose proof (rd_same_of_frame E _ W (ms_mem ms) (ms_mem ms0) Hro HFr) as Eq2. clear HF HFr HG.
    pose proof (fun x => eq_trans (Eq2 x) (Eq1 x)) as Eq.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    rewrite E32 in Q10. rewrite E33 in Q11.
    pose proof (v14_kept_regs E _ _ regsc [Z_to_bv 64 p1; Z_to_bv 64 p2]
      [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    pmkst HS.
    rewrite (SIGP CS_sup_lv2_worker_set) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
    change (cmd_af CS_sup_lv2_worker_set) with AF_sup_lv2_worker_set.
    assert (Hrvc : vr_rv (ms_regs ms0) (vr_base B e ++ [(18, q); (20, F); (22, F + 32); (27, shadow_addr F + 4)])).
    { apply (v14_rv_keep B e (ms_regs ms0) regsc _ _ Hrv).
      - intros r0 Hr0. apply KR. cbn in Hr0 |- *. tauto.
      - intros r0 v0 Hin. left. cbn in Hin. destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-;
        (split; [cbn; tauto | apply KR; cbn; tauto]). }
    assert (Hra : getr (ms_regs ms0) 1 = Z_to_bv 64 (vr_pc 0x8dc70)).
    { etransitivity; [exact Q1|]. unfold vr_pc, AF_verbs_receive. f_equal; lia. }
    destruct (tok_argB B e F c [p0; p1; p2] lyc Sc W (ms_mem ms0) mdv2 q 1 p1 a (proj1 HJ) Hperm
      (vr_copy_same B e F c [p0; p1; p2] W memc (ms_mem ms0) Eq Hcopy) eq_refl ltac:(rewrite T; reflexivity))
      as (Harg1 & _).
    destruct (tok_argB B e F c [p0; p1; p2] lyc Sc W (ms_mem ms0) mdv2 q 2 p2 b (proj1 HJ) Hperm
      (vr_copy_same B e F c [p0; p1; p2] W memc (ms_mem ms0) Eq Hcopy) eq_refl ltac:(rewrite T; reflexivity))
      as (Harg2 & _).
    destruct (v14_lv2_budget MT MTL (e_R e) a b Hcalls (v14_code_range B _ _ _ _ _ Hrec) Ha8 Hb8)
      as (HEV & HXM & HLV).
    assert (HV1 : SUP_LV2_WORKER_SET_STK = ltac:(let v := eval vm_compute in SUP_LV2_WORKER_SET_STK in exact v))
      by reflexivity.
    assert (HV2 : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
    eapply SRr_bind.
    { apply (vr_call_join B MT RRO RPG RECC ROA MTL PROGU HB e W pos F q c [p0; p1; p2] lyc Sc regsc memc mdc k nm _
        (ms_mem ms0) mdv2 (ms_regs ms0) SUP_LV2_WORKER_SET_STK (EV_SUP_LV2_WORKER_SET (e_R e))
        (XM_SUP_LV2_WORKER_SET MT (e_R e) (Some a) (Some b)) (LIVE_SUP_LV2_WORKER_SET (e_R e) (Some a) (Some b))
        (sup_lv2_worker_set_m (e_R e) (Some a) (Some b)) 4 1 0x8dc70 _
        Hent ltac:(lia) Hcore Hline Hcopy Eq HJ Hrvc Hra ltac:(unfold AF_verbs_receive; lia)
        ltac:(unfold AF_verbs_receive; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        HXM HLV Hh Hk1).
      intros ch1 Hpre Hfrm Haro Hcro Hrec' Hfr Hev Hlv Hmo.
      exact (TSUP_LV2_WORKER_SET fx lyc Sc W (ms_regs ms0) (ms_mem ms0) mdv2 ch1 p1 p2 (Some a) (Some b) (e_R e) (e_O e)
        Hpre Hfrm Haro Hcro Q10 ltac:(lia) Q11 ltac:(lia) (ex_intro _ a (conj eq_refl Harg1))
        (ex_intro _ b (conj eq_refl Harg2)) Hrec' Hfr Hev Hlv Hmo). }
    (* the jump into the join runs at the callee's return FP state fq (vr_jump is generic in the FP state) *)
    intros W2 c2 _ (fq & Hfq & Hhdx).
    eapply SRr_mono.
    { exact (vr_jump (fx := fq) B MT RRO RPG RECC ROA e 0x8dc70 (mkSS 30640 sr_atoms [] None (mkFacts [] [] [])) PRS_running
        W2 c2 (v14_ent_fxr B MT fx fq e Hent Hfq) ltac:(vm_compute; reflexivity) I eq_refl Hhdx). }
    intros W3 c3 _ H4. exists fq. split; [exact Hfq|]. right. exact H4.
- (* not three words: the refusal stub 0x8dc9c *)
  case_eq (Verbs.toks (e_D e)); [intros T; exfalso; exact (Hne T) | intros v args T].
  destruct (lv2_facts (e_R e) (e_D e) v args T Hroute) as [_ Hrej].
  destruct (Hrej ltac:(rewrite T in H3; cbn in H3; lia)) as [Hh Hk1]. clear Hrej.
  remember (Eimg (Ereg regsc [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply v14_env_agree).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (HS : st_ok_pi SEGS VAL E (mkSS 30584 sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 30584)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  clear HE.
  (* 0x8dc5c: li a0,3 *)
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (rd_same_of_frame E [] W memc (ms_mem ms) (Forall_nil _) HFr) as Eq1. clear HF HFr HG.
  (* 0x8dc60: bne s5,a0,0x8dc9c *)
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
    exact (vr_pr9c_of B MT RRO RPG RECC ROA e W pos F q c tp lyc Sc regsc memc mdc k nm VRR.RLv2
      (ms_regs ms0) (ms_mem ms0) mdv2 Hent Hroute Hne Hcore Hline Hcopy Eq HJ Hrvp Hh Hk1).
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    change (U E (SLit 3)) with 3 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold vr_ntok in Hc. lia.
Qed.

End e.
End f.
End d.
