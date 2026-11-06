(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S11 WLIST (0x8d3a0-0x8d3ac, 4 instructions) of the walk of verbs_receive
   on the ASan+UBSan build of plugin-hostd/fuzz_command (image B, interface lib/B/Prog/verbs_receive_iface.v,
   vr_s11_stmt). The B twin of the A walk's lib/A/Prog/verbs_receive_s11.v (a working branch):
     0x8d3a0 li a0,1; 0x8d3a4 ld s3,40(s1)            B reloads tok (the spill slot s1+40) into s3
     0x8d3a8 bne s5,a0,0x8d4c4                        one word only, else the refusal stub 0x8d4c4 (vr_pr, s3 = tok)
     0x8d3ac jal sup_worker_list                      the recorder call (sup_worker_list_c.v)
     0x8d3b0                                          the join J1 (vr_hd, the text in a0): the return address itself
   B-only code walked: 0x8d3a4 (the reload of tok from s1+40, the codegen range of B-PREP section 3). The call goes
   through verbs_receive_s10_lib.v's generic arm vr_call_arm; since B returns straight into J1 (A ran four more
   instructions), the continuation after the call only names J1's registers. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_worker_list_c answer_c hand_back_c xmalloc_c record_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_s10_lib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
Import ListNotations.
Import VRL10.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the callee-saved registers at the call of sup_worker_list (0x8d3ac), as J1 0x8d3b0 names them besides the text *)
Definition rl11 (e : vrE) (F q : Z) : list (Z * Z) := [(18, q); (22, F); (27, shadow_addr F + 4)].

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the callee's contract at every FP state (verbs_receive_c.v) and the record facts of the brief *)
Hypothesis TSUP_WORKER_LIST : forall fx0 : YK11.FPState, @tsup_worker_list_spec fx0 rc SK PI B MT.
Hypothesis HB : YF0m.CmdBSyms B.
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

Lemma vr_s11 : vr_s11_stmt B MT.
Proof.
intros e W cf Hent Hrt.
destruct Hrt as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hne & Hcore & Hline & Hcopy).
pose proof Hcore as (HJ & Hk & _ & _ & (EF & _) & Hrv & _ & Hspl & _ & Hrec & _ & Hperm & _).
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & _ & Hcalls & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof (proj1 HJ) as HAR.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & _).
destruct (route_wlist _ Hroute) as (args & T).
assert (Hvv : forall v args', Verbs.toks (e_D e) = v :: args' ->
  Verbs.list_eqb v Verbs.Lit.verb_chain = false /\ Verbs.list_eqb v Verbs.Lit.verb_pin_set = false).
{ intros v args' T'. rewrite T in T'. injection T' as <- _. split; vm_compute; reflexivity. }
assert (R9 : getr regsc (Z_to_bv 5 9) = w64 (vr_s1 e))
  by (apply (vr_rv_get regsc _ _ _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R21 : getr regsc (Z_to_bv 5 21) = w64 (vr_ntok (e_D e)))
  by (apply (vr_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn; tauto).
assert (Hnt : 0 <= vr_ntok (e_D e) <= 64).
{ unfold vr_ntok, Verbs.toks, Verbs.line_words_max. rewrite length_firstn. lia. }
assert (Hin4 : In (4, pos) (frames Sc)) by (pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _); rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
destruct (vr_tmp_blocks B e _ lyc Sc W memc mdc _ HAR Hperm (vr_lb e q) ltac:(left; reflexivity)) as (Hlb & _).
destruct (vr_tmp_blocks B e _ lyc Sc W memc mdc _ HAR Hperm (vr_cb e c) ltac:(right; left; reflexivity)) as (Hcb & _).
unfold vr_lb, vr_cb in Hlb, Hcb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hlb) as (_ & Hq4 & Hqc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4 & Hcc & _).
assert (Hlpos : 0 <= vr_l (e_n e) (e_D e)) by (unfold vr_l; pose proof (strnlen_le (e_n e) (e_D e) ltac:(lia)); lia).
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as Hrq1.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrq2.
pose proof (vr_s1_cases e Hal16) as Hs1.
assert (U9 : bv_unsigned (getr regsc 9) = vr_s1 e)
  by (change (getr regsc 9) with (getr regsc (Z_to_bv 5 9)); rewrite R9; unfold w64; apply unsigned_lit_small; lia).
change (vr_pc (vr_route_pc VRR.RWlist)) with (vr_pc 0x8d3a0).
replace (vr_pc 0x8d3a0) with (BASE + 0x6e70) by (unfold vr_pc, AF_verbs_receive; lia).
unfold cfg_at, w64.
assert (HV : vr_vals_ok F q c 0) by (unfold vr_vals_ok; lia).
pose proof (vr_seed_sp 0x6e70 W regsc memc (vr_s1 e) F q c 0 U9 ltac:(lia) ltac:(lia) HV Hspl) as HS.
pose proof (vr_xt_atoms regsc F c q 0) as (X32 & X33 & X34 & X35 & _).
pose proof (vr_env_regs regsc (vr_xt F c q 0) 21 (Z_to_bv 5 21) eq_refl) as X21. rewrite R21 in X21.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc (vr_xt F c q 0)))) by apply Eimg_env.
pose proof (env_agree_Eimg regsc (vr_xt F c q 0)) as HAE.
set (E := Eimg (Ereg regsc (vr_xt F c q 0))) in *. clearbody E.
(* 0x8d3a0: li a0,1; 0x8d3a4: ld s3,40(s1) *)
paj_run_sh RUNP HS HJ.
{ awr_ok_tac. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
cbn [ms_mem mkst] in HFr.
pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_sp) as Eq1. clear HF HFr HG.
(* 0x8d3a8: bne s5,a0,0x8d4c4 *)
psrr_branch_pi RUNP BR HS.
- (* more than one word: the refusal stub 0x8d4c4, with s3 = tok *)
  assert (Hn1 : length (Verbs.toks (e_D e)) <> 1%nat).
  { intros H1. rewrite branch_ne_U, (U_atom E 21 _ X21) in Hc by lia.
    unfold vr_ntok in Hc. rewrite H1 in Hc. vm_compute in Hc. discriminate Hc. }
  assert (St : vr_st (e_D e) = Verbs.reject).
  { rewrite (vr_st_route _ Hne), Hroute, T. cbn [VRR.plan_at]. rewrite T in Hn1.
    destruct args; [cbn in Hn1; lia | reflexivity]. }
  destruct (vr_rej_of (e_R e) (e_D e) Hne Hvv St) as [Hvh Hk1].
  paj_run_to_shc RUNTO HS HJ 0x6f94.
  { awr_ok_tac. }
  set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
  pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_sp) as Eq2. clear HF HFr HG.
  pose proof (rdeq_trans _ _ _ Eq1 Eq2) as Eq.
  prreg HS (19%bv : bv 5) Q19.
  pose proof (kept_regs_st_ok E _ _ regsc (vr_xt F c q 0) [2; 3; 4; 8; 9; 18; 21; 22; 24; 27] HS HAE
    ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
  pmkst HS.
  apply SRr_ret. cbv beta. exists fx. split; [apply fxrel_refl|]. left. unfold vrF_pr, vr_atpr.
  replace (BASE + 0x6f94) with (vr_pc 0x8d4c4) by (unfold vr_pc, AF_verbs_receive; lia).
  assert (Hrv' : vr_rv (ms_regs ms0) (vr_base B e ++ vr_rl_pr e F q c 0x8d4c4 (-902))).
  { replace (vr_rl_pr e F q c 0x8d4c4 (-902))
      with [(19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)] by reflexivity.
    apply (vr_rv_keep B e (ms_regs ms0) regsc _ _ Hrv).
    - intros r0 Hr0. apply KR. cbn in Hr0 |- *. tauto.
    - intros r0 v Hin. cbn in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-.
      + right. etransitivity; [exact Q19|]. rewrite X32. unfold w64. f_equal. rewrite unsigned_lit_small by lia. reflexivity.
      + left. split; [cbn; tauto | apply KR; cbn; tauto].
      + left. split; [cbn; tauto | apply KR; cbn; tauto].
      + left. split; [cbn; tauto | apply KR; cbn; tauto].
      + left. split; [cbn; tauto | apply KR; cbn; tauto]. }
  apply (vr_pr_mk B MT e 0x8d4c4 W pos F q c tp (vr_rl_pr e F q c 0x8d4c4 (-902)) lyc Sc (ms_regs ms0) (ms_mem ms0)
    mdv2 k nm Hvh Hk1 Hne).
  + change (vr_pr_ntok 0x8d4c4 (length (Verbs.toks (e_D e)))) with (2 <= length (Verbs.toks (e_D e)))%nat.
    destruct (Verbs.toks (e_D e)); [congruence | cbn [length] in Hn1 |- *; lia].
  + eapply vr_core_same; [exact Hcore | exact HJ | exact Eq | exact Hrv'].
  + exact Hrv'.
  + exact (vr_line_same B e q W memc W (ms_mem ms0) Eq Hline).
  + exact (vr_copy_same B e F c tp W memc W (ms_mem ms0) Eq Hcopy).
- (* one word: sup_worker_list, which returns into J1 *)
  assert (H1 : length (Verbs.toks (e_D e)) = 1%nat).
  { rewrite branch_ne_U, (U_atom E 21 _ X21) in Hc by lia.
    change (U E (SLit 1)) with 1 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold vr_ntok in Hc. lia. }
  assert (St : vr_st (e_D e) = Verbs.SCall Verbs.sup_worker_list).
  { rewrite (vr_st_route _ Hne), Hroute, T. cbn [VRR.plan_at]. rewrite T in H1.
    destruct args; [reflexivity | cbn in H1; lia]. }
  destruct (vr_call_of (e_R e) (e_D e) _ Hne Hvv St) as [Hvh Hk1]. cbn [VerbsRun.run_call ev_call] in Hvh, Hk1.
  (* 0x8d3ac: jal sup_worker_list *)
  paj_run_shc RUNP RUNC HS HJ.
  { awr_ok_tac. }
  set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
  pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_sp) as Eq2. clear HF HFr HG.
  pose proof (rdeq_trans _ _ _ Eq1 Eq2) as Eq.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  pose proof (kept_regs_st_ok E _ _ regsc (vr_xt F c q 0) [2; 3; 4; 8; 9; 18; 21; 22; 24; 27] HS HAE
    ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
  pmkst HS.
  rewrite (SIGP CS_sup_worker_list) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
  change (cmd_af CS_sup_worker_list) with AF_sup_worker_list.
  assert (Hcs : vr_cs B MT e pos F q c 1 0x6e80 tp (rl11 e F q) lyc Sc W (ms_regs ms0) (ms_mem ms0) mdv2 k nm).
  { split; [|split; [exact (vr_line_same B e q W memc W (ms_mem ms0) Eq Hline)
                   | exact (vr_copy_same B e F c tp W memc W (ms_mem ms0) Eq Hcopy)]].
    eapply vr_core_same; [exact Hcore | exact HJ | exact Eq |].
    apply (vr_rv_keep B e (ms_regs ms0) regsc _ _ Hrv).
    - intros r0 Hr0. apply KR. cbn in Hr0 |- *. tauto.
    - intros r0 v Hin. unfold rl11 in Hin. cbn in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-.
      + right. exact Q1.
      + right. exact Q10.
      + left. split; [cbn; tauto | apply KR; cbn; tauto].
      + left. split; [cbn; tauto | apply KR; cbn; tauto].
      + left. split; [cbn; tauto | apply KR; cbn; tauto]. }
  assert (Ht : (length (snd (sup_worker_list_m (e_R e))) <= 28)%nat).
  { unfold sup_worker_list_m, daemon_shape. apply stub_len. exact (rec_code_range B _ _ _ _ _ Hrec). }
  assert (HFsz : SUP_WORKER_LIST_STK = ltac:(let v := eval vm_compute in SUP_WORKER_LIST_STK in exact v))
    by reflexivity.
  assert (HVsz : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v))
    by reflexivity.
  apply (vr_call_arm B MT HB MTL ROA RRO RPG RECC PROGU e W pos F q c 1 0x6e80 tp (rl11 e F q) lyc Sc
    (ms_regs ms0) (ms_mem ms0) mdv2 k nm AF_sup_worker_list SUP_WORKER_LIST_STK (fp1 (e_O e))
    (EV_SUP_WORKER_LIST (e_R e)) (XM_SUP_WORKER_LIST MT (e_R e)) (LIVE_SUP_WORKER_LIST (e_R e))
    (sup_worker_list_m (e_R e)) _ Hent Hcs).
  + unfold rl11. repeat (apply Forall_cons; [cbn [fst]; unfold acallee_saved; lia|]). apply Forall_nil.
  + exact Hvh.
  + exact Hk1.
  + unfold EV_SUP_WORKER_LIST, EV_RECORD, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC. rewrite (spill_frees0 _ Hcalls). lia.
  + unfold XM_SUP_WORKER_LIST, XM_RECORD, XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC.
    rewrite (spill_frees0 _ Hcalls).
    pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length (snd (sup_worker_list_m (e_R e)))) + 1) 1)
      VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M2.
    pose proof (mo_malloc_nonneg MT MTL VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M0.
    lia.
  + unfold LIVE_SUP_WORKER_LIST, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC, VERBS_RECEIVE_REQ. lia.
  + rewrite HFsz. lia.
  + rewrite HFsz, HVsz. lia.
  + lia.
  + reflexivity.
  + intros a Ha. exact Ha.
  + intros ch HPRE1 Hfrm1 H1' H2' H3' H4' H5' H6' H7'.
    eapply SRr_mono.
    { exact (TSUP_WORKER_LIST fx lyc Sc W (ms_regs ms0) (ms_mem ms0) mdv2 ch (e_R e) (e_O e)
        HPRE1 Hfrm1 H1' H2' H3' ltac:(lia) H5' H6' H7'). }
    intros W' c' _ HP. revert HP. apply apost_baseF_impl. intros ly' S' W'' regs' mem' md' HP.
    eapply rc_post_of_b. exact HP.
  + (* the return address is J1 0x8d3b0 itself, reached at the FP state fx' the call returns *)
    intros fx' Hfx W2 regs2 mem2 md2 ly2 S2 tq O1 Haft.
    pose proof Haft as (_ & _ & (HJ2 & _ & _ & _ & _ & Hrv2 & _) & _).
    apply SRr_ret. cbv beta. exists fx'. split; [exact Hfx|]. right. unfold vrF_hd, vr_athd.
    replace (BASE + 0x6e80) with (vr_pc 0x8d3b0) by (unfold vr_pc, AF_verbs_receive; lia).
    apply (vr_hd_of_aft (fx := fx') B MT e 0x8d3b0 pos F q c tp (rl11 e F q) tq O1 ly2 S2 W2 regs2 mem2 md2 _ _
      regs2 mem2 md2 Haft HJ2 (rdeq_refl _)).
    * replace (vr_rl_hd e F q c 0x8d3b0 tq) with ((10, tq) :: rl11 e F q) by reflexivity. exact Hrv2.
    * change (vr_hd_ntok 0x8d3b0 (length (Verbs.toks (e_D e)))) with (length (Verbs.toks (e_D e)) = 1%nat). exact H1.
Qed.

End e.
End f.
End d.
