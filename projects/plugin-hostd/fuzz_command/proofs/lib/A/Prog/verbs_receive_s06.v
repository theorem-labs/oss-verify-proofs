(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S06 DISP (0x8d6fc-0x8d8a4, 0x8dec4-0x8ded4) of the ASan walk of
   verbs_receive on plugin-hostd/fuzz_command (interface lib/A/Prog/verbs_receive_iface.v, vr_s06_stmt): from vr_b4t
   at 0x8d6fc, the inline check of msg+0 and the loads of fd, &tok[0], tok[0] and ntok - 1 (v6_entry), then the
   dispatch's 18 tests in the order of the code, one lemma per test (each case is one
   concrete symbolic run): 16 strcmp(tok[0], literal) through the runtime contract (PaArt.aj_art_at, the tactic
   v6_strcmp_site), the inline verb_is(remove) (strcspn, then strncmp) and verb_is(quit) through verb_is's contract
   (PaNoChain.cl_callS_na). Each test leaves for its route's pc (vr_rt, with the route of
   lib/Prog/verbs_receive_route.v) or for the next test (v6_dm, verbs_receive_s06_k.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c lv2_refusals_forget_c
pin_set_words_c pins_clear_c pins_set_c reply_c socket_send_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c
sup_lv2_worker_set_c sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c
sup_remove_all_c sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c answer_c answer_code_c
hand_back_c arg_i_c arg_line_c rec_canonical_c xstrdup_c is_instance_verb_c number_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verb_is_c verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_s06_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.
Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.

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
Hypothesis TL : PALib B.
Hypothesis SHOK : vr_shadow_ok B.
Hypothesis BLKT : vr_blktail B.
Hypothesis STRCMP : forall fx0 : YK11.FPState, @RtString.astrcmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcmp).
Hypothesis STRNCMP : forall fx0 : YK11.FPState, @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
Hypothesis STRCSPN : forall fx0 : YK11.FPState, @RtString.astrcspn_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis TVERB_IS : forall fx0 : YK11.FPState, @tverb_is_spec fx0 rc SK PI B MT.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let STEP := v6_strcmp_step B MT TL SHOK BLKT STRCMP.
Let CSPN := v6_strcspn_step B MT TL SHOK BLKT STRCSPN.
Let NCMP := v6_strncmp_step B MT TL SHOK BLKT STRNCMP.
Let VISTEP := v6_vi_step B MT TL SHOK BLKT HB SIGP TVERB_IS.
Let CORJ := v6_core_j B MT ROA RRO RECC PROGU.



(* the entry of the dispatch (0x8d6fc-0x8d714): the inline check of msg+0 (its shadow byte is 0: the caller's
   frame object is addressable and 8-aligned), fd := msg->sender_id, s6 := &tok[0], verb := tok[0], s11 := ntok - 1.
   Two runs: the message object and its shadow byte, then the spill slot of &tok[0] and tok[0] (the two runs keep
   the caller's frame and this call's frame in separate symbolic states) *)
Definition v6_ssA : sstate := mkSS (AF_verbs_receive + (0x8d6fc - 0x8d480)) sr_atoms
  [YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
   YP09.mkRegion (Some 24%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))]] None
  (mkFacts [] [] [(SAlu ALU_ADD (SOff 22 0) (SOff 19 0), SOff 32 0)]).
Definition v6_ssB : sstate := mkSS (AF_verbs_receive + (0x8d70c - 0x8d480)) sr_atoms
  [YP09.mkRegion (Some 9%nat) 16 24 16 16 [YP09.mkChunk 16 (CVal 8 (SOff 32 32))];
   YP09.mkRegion (Some 32%nat) 32 40 32 32 [YP09.mkChunk 32 (CVal 8 (SOff 33 0))]] None (mkFacts [] [] []).

Lemma v6_entry : forall e W cf, vr_ent B MT e -> vr_b4t B MT e W cf -> SRr SEGS W cf (v6_dm B MT e 0x8d718 0 0).
Proof.
intros e W cf Hent Hb.
destruct Hb as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hne & Hcore & Hline & Hcopy).
pose proof Hent as (HPRE0 & HROD0 & Hr10 & HOBJ & Hfd & Hdata & Hnv & Hnb & HlenD & Hinblk & HnotO & HbytesD & HSP0
  & HREC0 & Hcalls & Hans & Hrep & Hnrep & Hdecl & HPERM0 & Hq0 & HGOT0 & HRO0 & HROIN & HVOBJ & Herrno & Hflag
  & HguardE & Hfrlen & Hevb & Hlive & HMOK).
pose proof HPRE0 as (HARe & _).
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _ & HSP & _).
destruct (v6_rv_base B e regsc _ Hrv) as (R2 & R3 & R4 & R8 & R9).
assert (R19 : getr regsc (Z_to_bv 5 19) = w64 SHADOW_OFF)
  by (apply (v6_rv_get regsc _ _ _ Hrv); unfold vr_base, vr_rl4t; cbn; tauto).
assert (R21 : getr regsc (Z_to_bv 5 21) = w64 (vr_ntok (e_D e)))
  by (apply (v6_rv_get regsc _ _ _ Hrv); unfold vr_base, vr_rl4t; cbn; tauto).
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 (e_msg e / 8))
  by (apply (v6_rv_get regsc _ _ _ Hrv); unfold vr_base, vr_rl4t; cbn; tauto).
assert (R24 : getr regsc (Z_to_bv 5 24) = w64 (e_msg e))
  by (apply (v6_rv_get regsc _ _ _ Hrv); unfold vr_base, vr_rl4t; cbn; tauto).
pose proof HJ as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (v6_s1_rng (vr_sp0 e) Hal16) as [S1a S1b]. fold (vr_s1 e) in S1a, S1b.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (VRS : VERBS_RECEIVE_STK = 16992) by reflexivity.
destruct (v6_core_blocks B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as (Hlb & Hcb & Hin4 & HFa).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR0 Hin4) as (HF0 & HFc & _). rewrite <- HFa in HF0, HFc.
change (fs_frame_bytes 4) with 1024 in HFc.
assert (Hnt : 0 <= vr_ntok (e_D e) <= 64).
{ unfold vr_ntok, Verbs.toks, Verbs.line_words_max. rewrite length_firstn. lia. }
(* the message object at the boundary: its first word and its shadow byte *)
assert (HOincl : forall pn, In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e)))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ HREC0 Hpn)).
pose proof HOBJ as ((cidm & posm & Hinm & Hcidm & Halm & Hlom & Hhim) & Hmod8 & HRA0).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cidm posm HARe Hinm) as (Hfm0 & Hfmc & Hfmapp).
pose proof (fs_frame_bytes_nonneg cidm) as Hfmb.
assert (HMSG : forall a, e_msg e <= a < e_msg e + 24 \/ (exists i, 0 <= i < 3 /\ a = shadow_addr (e_msg e) + i) ->
  rdW W memc a = rdW (e_W e) (e_mem e) a)
  by (intros a Ha; exact (v6_caller_kept B e [(4, pos)] lyc Sc W memc mdc k a HJ HARe HOBJ HOincl Ha)).
assert (Hsh0 : rdW W memc (shadow_addr (e_msg e)) = Some 0).
{ rewrite HMSG by (right; exists 0; split; [lia | ring]).
  destruct (HRA0 (e_msg e + 7) ltac:(lia)) as (s & Hs & Hok).
  assert (Esh : shadow_of_addr SHADOW_OFF (e_msg e + 7) = shadow_addr (e_msg e)).
  { unfold shadow_of_addr, shadow_addr. f_equal. symmetry.
    pose proof (Z.div_mod (e_msg e) 8 ltac:(lia)) as D. rewrite Hmod8 in D.
    apply Z.div_unique with (r := 7); lia. }
  rewrite Esh in Hs. destruct Hok as [-> | [Hk1 Hk2]]; [exact Hs|].
  exfalso. assert (M7 : (e_msg e + 7) mod 8 = 7) by (rewrite Z.add_mod, Hmod8 by lia; reflexivity). lia. }
assert (Hfd1 : aval_mem (rdW W memc) (e_msg e) 4 (e_fd e mod 2 ^ 32)).
{ intros kx Hkx. rewrite HMSG by (left; lia). rewrite (Hfd kx Hkx). f_equal. unfold YG0f.le_byte.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity. }
destruct (v6_shadow_band (e_msg e) 24 ltac:(lia) ltac:(lia) ltac:(eapply Z.le_trans; [exact Hhim | exact Hfmc])) as [Hb1 Hb2].
pose proof (shadow_mono (e_msg e) (e_msg e + 24) ltac:(lia)) as Hmo.
pose proof (Z.mod_pos_bound (e_fd e) (2 ^ 32) ltac:(lia)) as Hfdr.
(* the first run: the check of msg+0 and the load of msg->sender_id *)
rewrite <- v6_cfg.
remember (Eimg (Ereg regsc [Z_to_bv 64 (shadow_addr (e_msg e)); Z_to_bv 64 (e_fd e mod 2 ^ 32)])) as EA eqn:HEA.
assert (HEIA : img_env VAL A_LIM EA) by (rewrite HEA; apply Eimg_env).
assert (HAEA : env_agree 32 (Ereg regsc [Z_to_bv 64 (shadow_addr (e_msg e)); Z_to_bv 64 (e_fd e mod 2 ^ 32)]) EA)
  by (rewrite HEA; apply v6_env_agree).
assert (EEA : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew EA n = getr regsc rr)
  by (intros n rr Hn; rewrite HEA; apply ew_Eimg_Ereg_nat; exact Hn).
assert (XA32 : ew EA 32 = Z_to_bv 64 (shadow_addr (e_msg e)))
  by (rewrite HEA, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (XA33 : ew EA 33 = Z_to_bv 64 (e_fd e mod 2 ^ 32))
  by (rewrite HEA, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (HSA : st_ok_pi SEGS VAL EA v6_ssA
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + (AF_verbs_receive + (0x8d6fc - 0x8d480)))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold v6_ssA. apply pa_entry_st_ok_full.
  - rewrite HEA. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite XA32, unsigned_lit_small by zlia.
      split; [zlia|]. split; [zlia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS EA _ (shadow_addr (e_msg e)) 0 1 (SLit 0) 0);
      [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
      apply v6_aval_val. intros kk Hkk. destruct kk as [|kk]; [|cbn in Hkk; lia].
      cbn [Z.of_nat]. rewrite !Z.add_0_r. rewrite Hsh0. reflexivity.
    + rewrite (EEA 24%nat (Z_to_bv 5 24) eq_refl), R24. unfold w64. rewrite unsigned_lit_small by zlia.
      split; [zlia|]. split; [zlia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS EA _ (e_msg e) 0 4 (SOff 33 0) (e_fd e mod 2 ^ 32));
      [cbn [sv_denot]; rewrite XA33, Z.add_0_r, unsigned_lit_small by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
      apply v6_aval_val. rewrite Z.add_0_r. exact Hfd1.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite XA32, (EEA 24%nat (Z_to_bv 5 24) eq_refl), R24. unfold w64. rewrite !unsigned_lit_small by zlia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; zlia.
  - split; [exact I|]. split; [exact I|]. split; [|exact I].
    assert (Hm8r : 0 <= e_msg e / 8 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Hshr : 0 <= shadow_addr (e_msg e) < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF in *; lia).
    cbn [sv_denot]. rewrite (EEA 22%nat (Z_to_bv 5 22) eq_refl), (EEA 19%nat (Z_to_bv 5 19) eq_refl), R22, R19, XA32.
    unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF in *; lia). rewrite !Z.add_0_r.
    rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw].
    rewrite (zcanon_id (e_msg e / 8)) by (unfold M64; lia). rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
    replace (e_msg e / 8 + SHADOW_OFF) with (shadow_addr (e_msg e)) by (unfold shadow_addr; lia).
    apply Z_to_bv64_canon. }
paj_run_to_sh RUNTO HSA HJ 29224.
{ awr_ok_tac. }
set (mdvA := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdvA.
set (msA := ms) in *.
cbn [ms_mem mkst] in HFr.
pose proof (v6_rdeq_frame _ _ _ _ _ HFr ltac:(repeat constructor; cbn; lia)) as EqA. clear HF HFr HG.
pose proof (v6_kept_regs EA _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 25; 26; 27] HSA HAEA
  ltac:(vm_compute; reflexivity)) as KRA. cbn [ms_regs restrict] in KRA.
(* the second run: &tok[0] from its spill slot, then tok[0], and ntok - 1 *)
destruct tp as [|v tps].
{ exfalso. destruct Hcopy as (_ & _ & Hlen & _). destruct (Verbs.toks (e_D e)); [exact (Hne eq_refl) | discriminate Hlen]. }
pose proof Hcopy as (Hfc & Hm8 & Hlen & Hptr & Hwrd).
pose proof (Hptr 0%nat v eq_refl) as Hv0. rewrite Z.add_0_r in Hv0.
unfold vr_spill, vr_sl3 in HSP. rewrite Forall_forall in HSP. pose proof (HSP (16, F + 32) ltac:(cbn; tauto)) as Hsp16.
cbn [fst snd] in Hsp16.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hcb) as (_ & Hc4 & Hcc & _).
destruct (Hwrd 0%nat v (hd [] (Verbs.toks (e_D e)))) as (_ & _ & Hcv & Hve);
  [reflexivity | destruct (Verbs.toks (e_D e)); [exact (False_ind _ (Hne eq_refl)) | reflexivity] |].
unfold vr_cb in Hc4, Hcc. cbn [fst snd] in Hc4, Hcc.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [_ Rc].
remember (Eimg (Ereg (ms_regs msA) [Z_to_bv 64 F; Z_to_bv 64 v])) as EB eqn:HEB.
assert (HEIB : img_env VAL A_LIM EB) by (rewrite HEB; apply Eimg_env).
assert (HAEB : env_agree 32 (Ereg (ms_regs msA) [Z_to_bv 64 F; Z_to_bv 64 v]) EB) by (rewrite HEB; apply v6_env_agree).
assert (EEB : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew EB n = getr (ms_regs msA) rr)
  by (intros n rr Hn; rewrite HEB; apply ew_Eimg_Ereg_nat; exact Hn).
assert (XB32 : ew EB 32 = Z_to_bv 64 F)
  by (rewrite HEB, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs msA) _ 0)).
assert (XB33 : ew EB 33 = Z_to_bv 64 v)
  by (rewrite HEB, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs msA) _ 1)).
assert (E9 : bv_unsigned (ew EB 9) = vr_s1 e).
{ rewrite (EEB 9%nat (Z_to_bv 5 9) eq_refl), (KRA 9 ltac:(cbn; tauto)), R9. unfold w64.
  apply unsigned_lit_small. unfold vr_sp0 in *. lia. }
pmkst HSA.
assert (HSB : st_ok_pi SEGS VAL EB v6_ssB
  (restrict (w_H W) (mkst (ms_regs msA) (Z_to_bv 64 (BASE + (AF_verbs_receive + (0x8d70c - 0x8d480)))) (ms_mem msA) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold v6_ssB. apply pa_entry_st_ok_full.
  - rewrite HEB. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E9. split; [unfold vr_sp0 in *; lia|]. split; [unfold vr_sp0 in *; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS EB _ (vr_s1 e) 16 8 (SOff 32 32) (F + 32));
      [cbn [sv_denot]; rewrite XB32, (unsigned_lit_small F) by lia; reflexivity | cbn; lia | cbn; lia |].
      apply v6_aval_val. intros kx Hkx. rewrite EqA. exact (Hsp16 kx Hkx).
    + rewrite XB32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS EB _ F 32 8 (SOff 33 0) v);
      [cbn [sv_denot]; rewrite XB33, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
      apply v6_aval_val. intros kx Hkx. rewrite EqA. exact (Hv0 kx Hkx).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite E9, XB32, unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; unfold vr_sp0 in *; lia.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
paj_run_to_sh RUNTO HSB HJ 29236.
{ awr_ok_tac. }
set (mdvB := with_vm_backing (m_vm_lazy mdvA) mat0 mdvA) in *. clearbody mdvB.
set (msB := ms0) in *.
cbn [ms_mem mkst] in HFr.
pose proof (v6_rdeq_frame _ _ _ _ _ HFr ltac:(repeat constructor; cbn; lia)) as EqB. clear HF HFr HG.
pose proof (v6_kept_regs EB _ _ (ms_regs msA) _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25] HSB HAEB
  ltac:(vm_compute; reflexivity)) as KRB. cbn [ms_regs restrict] in KRB.
prreg HSB (Z_to_bv 5 22) T22. prreg HSB (Z_to_bv 5 26) T26. prreg HSB (Z_to_bv 5 27) T27.
rewrite XB32, unsigned_lit_small in T22 by lia. rewrite XB33 in T26.
rewrite (EEB 21%nat (Z_to_bv 5 21) eq_refl), (KRA 21 ltac:(cbn; tauto)), R21 in T27. unfold w64 in T27.
rewrite unsigned_lit_small in T27 by lia. replace (vr_ntok (e_D e) + -1) with (vr_ntok (e_D e) - 1) in T27 by lia.
assert (HrvB : vr_rv (ms_regs msB) (vr_base B e ++ v6_rl e F q (hd 0 (v :: tps)) 0)).
{ apply v6_rv_intro. intros r0 v0 Hin. unfold vr_base, v6_rl in Hin. cbn [app In hd] in Hin.
  repeat (destruct Hin as [E0|Hin]; [injection E0 as <- <-;
    first [exact T22 | exact T26 | exact T27
          | rewrite KRB by (cbn; tauto); rewrite KRA by (cbn; tauto); apply (v6_rv_get regsc _ _ _ Hrv);
            unfold vr_base, vr_rl4t; cbn; tauto] |]).
  destruct Hin. }
pose proof (v6_KO_eq e W memc (ms_mem msB) (fun a _ => eq_trans (EqB a) (EqA a))) as HKOB.
pmkst HSB. apply SRr_ret.
exists pos, F, q, c, (v :: tps), lyc, Sc, (ms_regs msB), (ms_mem msB), mdvB, k, nm.
split; [apply v6_cfg2; reflexivity|]. split; [exact Hne|]. split; [exact (v6_route_casc_ne _ Hne)|].
exact (v6_exit B MT TL e pos F q c (v :: tps) lyc Sc W regsc memc mdc k nm _ (ms_regs msB) (ms_mem msB) mdvB _ Hent Hcore
  Hline Hcopy HJ HKOB HrvB).
Qed.

(* a test strcmp(tok[0], lit) of the dispatch, from the state v6_dm at pc (its first instruction): the seed
   (v6_seed), the run to the call, the call (v6_strcmp_step), the return path up to the branch, and the two exits:
   to the route r (strcmp returned 0) or to the next test at pcn. i is the test's index in v6_tests, g the reload
   group after it, KRL the registers its return path keeps. One tactic, since every name it uses is bound in it. *)
Ltac v6_strcmp_site pc i r pcn g LIT KRL :=
let pcr := eval vm_compute in (AF_verbs_receive + (vr_route_pc r - 0x8d480)) in
let pcn := eval vm_compute in (AF_verbs_receive + (pcn - 0x8d480)) in
let y := lazymatch type of LIT with v6_lit ?y _ => y end in
let sy := lazymatch type of LIT with v6_lit _ ?sy => sy end in
intros e W cf Hent Hdm;
destruct Hdm as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hne & Hroute & Hcore & Hline & Hcopy);
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _);
pose proof (v6_seed B MT e pos F q c lyc Sc W regsc memc mdc k nm _ pc Hcore) as HS;
rewrite <- v6_cfg;
remember (Eimg (Ereg regsc (v6_extra F q))) as E eqn:HE;
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env);
assert (HAE : env_agree 32 (Ereg regsc (v6_extra F q)) E) by (rewrite HE; apply v6_env_agree);
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regsc rr)
  by (intros n rr Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn);
pose proof (v6_E_ex regsc F q) as (X32 & X33 & X34); rewrite <- HE in X32, X33, X34;
destruct (v6_rv_base B e regsc _ Hrv) as (R2 & R3 & R4 & R8 & R9);
pose proof HJ as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _);
pose proof (v6_s1_rng (vr_sp0 e) Hal16) as [S1a S1b]; fold (vr_s1 e) in S1a, S1b;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
assert (VRS : VERBS_RECEIVE_STK = 16992) by reflexivity;
destruct (v6_core_blocks B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as (Hlb & Hcb & Hin4 & HFa);
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR0 Hin4) as (HF0 & HFc & _); rewrite <- HFa in HF0, HFc;
change (fs_frame_bytes 4) with 1024 in HFc;
pose proof (shadow_addr_bounds F ltac:(lia)) as SB;
assert (SB0 : 0 <= shadow_addr F < 2 ^ 64) by v6_lia2;
pose proof (v6_ent_ro B MT e Hent) as [_ HVOBJ];
paj_run_shc RUNP RUNC HS HJ; [awr_ok_tac|];
let mt1 := lazymatch goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] => mt end in
set (mdv := with_vm_backing (m_vm_lazy mdc) mt1 mdc) in *; clearbody mdv;
let m1 := lazymatch goal with H : st_ok _ _ _ (restrict _ ?m) |- _ => m end in
set (ms1 := m1) in *;
let Hf1 := lazymatch goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => H end in
pose proof (v6_rdeq_frame _ _ _ _ _ Hf1 ltac:(repeat constructor; cbn; lia)) as Eq1;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
repeat match goal with H : mem_grows _ _ |- _ => clear H end;
pose proof (v6_KO_eq e W memc (ms_mem ms1) (fun a _ => Eq1 a)) as KOc;
let Q1 := fresh "Q1" in let Q10 := fresh "Q10" in let Q11 := fresh "Q11" in
prreg HS (Z_to_bv 5 1) Q1; prreg HS (Z_to_bv 5 10) Q10; prreg HS (Z_to_bv 5 11) Q11;
rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl) in Q10;
rewrite (v6_rv_get regsc _ 26 (hd 0 tp) Hrv ltac:(unfold vr_base, v6_rl; cbn; tauto)) in Q10;
let n := lazymatch type of Q11 with getr _ _ = ew _ ?n => n end in
let j := eval vm_compute in (n - 241)%nat in
let yv := eval vm_compute in (nth j cmd_objs 0) in
assert (Xlit : ew E n = Z_to_bv 64 yv)
  by (rewrite (img_env_atomP E n HEI ltac:(unfold A_TEXT, A_LIM; lia)); change n with (A_OBJ j);
      rewrite (HVOBJ j ltac:(vm_compute; lia)); reflexivity);
rewrite Xlit in Q11; clear Xlit;
pose proof (v6_kept_regs E _ _ regsc (v6_extra F q) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS HAE
  ltac:(vm_compute; reflexivity)) as KR; cbn [ms_regs restrict] in KR;
assert (Qsp : spZ (ms_regs ms1) = vr_s1 e) by
  (change (spZ (ms_regs ms1)) with (bv_unsigned (getr (ms_regs ms1) (Z_to_bv 5 2))); rewrite (KR 2 ltac:(cbn; tauto)), R2;
   unfold w64; rewrite unsigned_lit_small by (unfold vr_sp0 in *; lia); reflexivity);
assert (Q3 : getr (ms_regs ms1) (Z_to_bv 5 3) = w64 (as_gp B)) by (rewrite (KR 3 ltac:(cbn; tauto)); exact R3);
assert (Q4 : getr (ms_regs ms1) (Z_to_bv 5 4) = w64 (as_tp B)) by (rewrite (KR 4 ltac:(cbn; tauto)); exact R4);
pmkst HS;
apply (STEP e pos F q c tp lyc Sc W regsc memc mdc k nm _ (ms_regs ms1) (ms_mem ms1) mdv y sy _ _
  Hcore Hcopy Hne HJ KOc Qsp Q1 ltac:(apply ret_ok_codeptr_v; [lia | reflexivity]) Q3 Q4 Q10 Q11 LIT);
intros regs2 mem2 md2 HJ2 HP2 HQ2 HKO2;
let HS2 := fresh "HS2" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2;
let P := lazymatch type of HS2 with ?P -> _ => P end in
  assert (HQ : P) by
    (constructor; [|constructor]; split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ms_mem restrict];
     intros a Ha; [|lia];
     apply (mbyte_of_aview SEGS); rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9 in Ha; unfold w64 in Ha;
     rewrite unsigned_lit_small in Ha by (unfold vr_sp0 in *; lia);
     rewrite (HKO2 a ltac:(unfold vr_sp0 in *; lia) ltac:(lia)); symmetry; apply KOc; [unfold vr_sp0 in *; lia | lia]);
  specialize (HS2 HQ); clear HQ;
rewrite <- restrict_mkst_fx in HS2;
pose proof (img_env_havoc_hi E 1024 (map (getr regs2) CLOB) HEI ltac:(unfold A_LIM; lia)) as HEI2;
assert (Ua0 : U (havoc E 1024 (map (getr regs2) CLOB)) (SOff 1028 0) = bv_unsigned (getr regs2 10)) by
  (unfold U; cbn [sv_denot]; change 1028%nat with (1024 + 4)%nat;
   rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbn; lia); unfold CLOB; cbn [map nth];
   rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
assert (HAE2 : env_agree 32 (Ereg regsc (v6_extra F q)) (havoc E 1024 (map (getr regs2) CLOB)))
  by (apply v6_env_agree_havoc; [lia | exact HAE]);
paj_run_sh RUNP HS2 HJ2; [awr_ok_tac|];
let mt2 := lazymatch goal with |- context [with_vm_backing (m_vm_lazy md2) ?mt md2] => mt end in
set (mdv2 := with_vm_backing (m_vm_lazy md2) mt2 md2) in *; clearbody mdv2;
let Hf2 := lazymatch goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => H end in
cbn [ms_mem mkst] in Hf2; pose proof (v6_rdeq_frame _ _ _ _ _ Hf2 ltac:(repeat constructor; cbn; lia)) as Eq2;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
repeat match goal with H : mem_grows _ _ |- _ => clear H end;
pose proof (v6_KO_trans e W memc mem2 _ HKO2 (v6_KO_eq e W mem2 _ (fun a _ => Eq2 a))) as KO2;
psrr_branch_pi RUNP BR HS2;
[ let Hc := lazymatch goal with H : branch_taken _ _ _ = true |- _ => H end in
  rewrite branch_eq_U, Ua0 in Hc;
  assert (H0 : getr regs2 10 = w64 0) by
    (apply Z.eqb_eq in Hc; unfold U in Hc; cbn [sv_denot] in Hc; rewrite unsigned_lit_small in Hc by lia;
     apply bv_eq; rewrite Hc; unfold w64; rewrite unsigned_lit_small by lia; reflexivity);
  apply HQ2 in H0;
  assert (Hr : VRR.route (Verbs.toks (e_D e)) = r)
    by (apply (v6_hit i _ _ _ _ eq_refl Hroute); cbv beta; apply PV.list_eqb_eq; exact H0);
  paj_run_to_sh RUNTO HS2 HJ2 pcr; [awr_ok_tac|];
  let mt3 := lazymatch goal with |- context [with_vm_backing (m_vm_lazy mdv2) ?mt mdv2] => mt end in
  set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mt3 mdv2) in *; clearbody mdv3;
  let Hf3 := lazymatch goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => H end in
  pose proof (v6_rdeq_frame _ _ _ _ _ Hf3 ltac:(repeat constructor; cbn; lia)) as Eq3;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
  repeat match goal with H : mem_grows _ _ |- _ => clear H end;
  let m3 := lazymatch goal with H : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => m end in
  set (ms3 := m3) in *;
  pose proof (v6_kept_regs _ _ _ regsc (v6_extra F q) KRL HS2 HAE2 ltac:(vm_compute; reflexivity)) as KR3;
  cbn [ms_regs restrict] in KR3;
  let T18 := fresh "T18" in let T20 := fresh "T20" in let T27 := fresh "T27" in
  prreg HS2 (Z_to_bv 5 18) T18; prreg HS2 (Z_to_bv 5 20) T20; prreg HS2 (Z_to_bv 5 27) T27;
  try rewrite X33 in T18; try rewrite X32 in T20;
  try (rewrite X34, (unsigned_lit_small (shadow_addr F)) in T27 by exact SB0);
  pose proof (v6_KO_trans e W memc _ (ms_mem ms3) KO2 (v6_KO_eq e W _ (ms_mem ms3) (fun a _ => Eq3 a))) as HKO3;
  assert (Hrv3 : vr_rv (ms_regs ms3) (vr_base B e ++ v6_rl e F q (hd 0 tp) g)) by
    (apply (v6_rv_keep B e (ms_regs ms3) regsc _ _ Hrv); [intros r0 Hr0; apply KR3; cbn in Hr0 |- *; tauto|];
     intros r0 v0 Hin; unfold v6_rl in Hin; cbn [app In] in Hin;
     repeat (destruct Hin as [E0|Hin]; [injection E0 as <- <-;
       first [left; split; [unfold v6_rl; cbn [app In]; tauto | apply KR3; cbn; tauto]
             | right; first [exact T18 | exact T20 | exact T27]] |]);
     destruct Hin);
  pmkst HS2; apply SRr_ret; left;
  exists pos, F, q, c, tp, lyc, Sc, (ms_regs ms3), (ms_mem ms3), mdv3, k, nm;
  split; [rewrite Hr; apply v6_cfg2; reflexivity|];
  split; [reflexivity|]; split; [exact Hne|];
  rewrite v6_rl_rt, Hr; cbn [vr_rgroup];
  exact (v6_exit B MT TL e pos F q c tp lyc Sc W regsc memc mdc k nm _ (ms_regs ms3) (ms_mem ms3) mdv3 _ Hent Hcore Hline Hcopy
    HJ2 HKO3 Hrv3)
| let Hc := lazymatch goal with H : branch_taken _ _ _ = false |- _ => H end in
  rewrite branch_eq_U, Ua0 in Hc;
  assert (H0 : hd [] (Verbs.toks (e_D e)) <> sy)
    by (intros Heq; apply HQ2 in Heq; rewrite Heq in Hc; vm_compute in Hc; discriminate Hc);
  assert (Hr : VRR.route (Verbs.toks (e_D e)) =
    v6_casc (skipn (S i) v6_tests) (hd [] (Verbs.toks (e_D e))) (tl (Verbs.toks (e_D e))))
    by (apply (v6_miss i _ _ _ _ eq_refl Hroute); cbv beta;
        destruct (PV.list_eqb (hd [] (Verbs.toks (e_D e))) sy) eqn:El; [|reflexivity];
        exfalso; apply H0; apply PV.list_eqb_eq; exact El);
  paj_run_to_sh RUNTO HS2 HJ2 pcn; [awr_ok_tac|];
  let mt3 := lazymatch goal with |- context [with_vm_backing (m_vm_lazy mdv2) ?mt mdv2] => mt end in
  set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mt3 mdv2) in *; clearbody mdv3;
  let Hf3 := lazymatch goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => H end in
  pose proof (v6_rdeq_frame _ _ _ _ _ Hf3 ltac:(repeat constructor; cbn; lia)) as Eq3;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
  repeat match goal with H : mem_grows _ _ |- _ => clear H end;
  let m3 := lazymatch goal with H : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => m end in
  set (ms3 := m3) in *;
  pose proof (v6_kept_regs _ _ _ regsc (v6_extra F q) KRL HS2 HAE2 ltac:(vm_compute; reflexivity)) as KR3;
  cbn [ms_regs restrict] in KR3;
  let T18 := fresh "T18" in let T20 := fresh "T20" in let T27 := fresh "T27" in
  prreg HS2 (Z_to_bv 5 18) T18; prreg HS2 (Z_to_bv 5 20) T20; prreg HS2 (Z_to_bv 5 27) T27;
  try rewrite X33 in T18; try rewrite X32 in T20;
  try (rewrite X34, (unsigned_lit_small (shadow_addr F)) in T27 by exact SB0);
  pose proof (v6_KO_trans e W memc _ (ms_mem ms3) KO2 (v6_KO_eq e W _ (ms_mem ms3) (fun a _ => Eq3 a))) as HKO3;
  assert (Hrv3 : vr_rv (ms_regs ms3) (vr_base B e ++ v6_rl e F q (hd 0 tp) g)) by
    (apply (v6_rv_keep B e (ms_regs ms3) regsc _ _ Hrv); [intros r0 Hr0; apply KR3; cbn in Hr0 |- *; tauto|];
     intros r0 v0 Hin; unfold v6_rl in Hin; cbn [app In] in Hin;
     repeat (destruct Hin as [E0|Hin]; [injection E0 as <- <-;
       first [left; split; [unfold v6_rl; cbn [app In]; tauto | apply KR3; cbn; tauto]
             | right; first [exact T18 | exact T20 | exact T27]] |]);
     destruct Hin);
  pmkst HS2; apply SRr_ret; right;
  exists pos, F, q, c, tp, lyc, Sc, (ms_regs ms3), (ms_mem ms3), mdv3, k, nm;
  split; [apply v6_cfg2; reflexivity|];
  split; [exact Hne|]; split; [exact Hr|];
  exact (v6_exit B MT TL e pos F q c tp lyc Sc W regsc memc mdc k nm _ (ms_regs ms3) (ms_mem ms3) mdv3 _ Hent Hcore Hline Hcopy
    HJ2 HKO3 Hrv3) ].

Ltac v6_pre pc :=
intros e W cf Hent Hdm;
destruct Hdm as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hne & Hroute & Hcore & Hline & Hcopy);
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _);
pose proof (v6_seed B MT e pos F q c lyc Sc W regsc memc mdc k nm _ pc Hcore) as HS;
rewrite <- v6_cfg;
remember (Eimg (Ereg regsc (v6_extra F q))) as E eqn:HE;
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env);
assert (HAE : env_agree 32 (Ereg regsc (v6_extra F q)) E) by (rewrite HE; apply v6_env_agree);
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regsc rr)
  by (intros n rr Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn);
pose proof (v6_E_ex regsc F q) as (X32 & X33 & X34); rewrite <- HE in X32, X33, X34;
destruct (v6_rv_base B e regsc _ Hrv) as (R2 & R3 & R4 & R8 & R9);
pose proof HJ as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _);
pose proof (v6_s1_rng (vr_sp0 e) Hal16) as [S1a S1b]; fold (vr_s1 e) in S1a, S1b;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
assert (VRS : VERBS_RECEIVE_STK = 16992) by reflexivity;
destruct (v6_core_blocks B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as (Hlb & Hcb & Hin4 & HFa);
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR0 Hin4) as (HF0 & HFc & _); rewrite <- HFa in HF0, HFc;
change (fs_frame_bytes 4) with 1024 in HFc;
pose proof (shadow_addr_bounds F ltac:(lia)) as SB;
assert (SB0 : 0 <= shadow_addr F < 2 ^ 64) by v6_lia2;
pose proof (v6_ent_ro B MT e Hent) as [_ HVOBJ];
paj_run_shc RUNP RUNC HS HJ; [awr_ok_tac|];
let mt1 := lazymatch goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] => mt end in
set (mdv := with_vm_backing (m_vm_lazy mdc) mt1 mdc) in *; clearbody mdv;
let m1 := lazymatch goal with H : st_ok _ _ _ (restrict _ ?m) |- _ => m end in
set (ms1 := m1) in *;
let Hf1 := lazymatch goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => H end in
pose proof (v6_rdeq_frame _ _ _ _ _ Hf1 ltac:(repeat constructor; cbn; lia)) as Eq1;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
repeat match goal with H : mem_grows _ _ |- _ => clear H end;
pose proof (v6_KO_eq e W memc (ms_mem ms1) (fun a _ => Eq1 a)) as KOc;
let Q1 := fresh "Q1" in let Q10 := fresh "Q10" in let Q11 := fresh "Q11" in
prreg HS (Z_to_bv 5 1) Q1; prreg HS (Z_to_bv 5 10) Q10; prreg HS (Z_to_bv 5 11) Q11;
rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl) in Q10;
rewrite (v6_rv_get regsc _ 26 (hd 0 tp) Hrv ltac:(unfold vr_base, v6_rl; cbn; tauto)) in Q10;
let n := lazymatch type of Q11 with getr _ _ = ew _ ?n => n end in
let j := eval vm_compute in (n - 241)%nat in
let yv := eval vm_compute in (nth j cmd_objs 0) in
assert (Xlit : ew E n = Z_to_bv 64 yv)
  by (rewrite (img_env_atomP E n HEI ltac:(unfold A_TEXT, A_LIM; lia)); change n with (A_OBJ j);
      rewrite (HVOBJ j ltac:(vm_compute; lia)); reflexivity);
rewrite Xlit in Q11; clear Xlit;
pose proof (v6_kept_regs E _ _ regsc (v6_extra F q) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS HAE
  ltac:(vm_compute; reflexivity)) as KR; cbn [ms_regs restrict] in KR;
assert (Qsp : spZ (ms_regs ms1) = vr_s1 e) by
  (change (spZ (ms_regs ms1)) with (bv_unsigned (getr (ms_regs ms1) (Z_to_bv 5 2))); rewrite (KR 2 ltac:(cbn; tauto)), R2;
   unfold w64; rewrite unsigned_lit_small by (unfold vr_sp0 in *; lia); reflexivity);
assert (Q3 : getr (ms_regs ms1) (Z_to_bv 5 3) = w64 (as_gp B)) by (rewrite (KR 3 ltac:(cbn; tauto)); exact R3);
assert (Q4 : getr (ms_regs ms1) (Z_to_bv 5 4) = w64 (as_tp B)) by (rewrite (KR 4 ltac:(cbn; tauto)); exact R4);
pmkst HS.

Definition v6_out (e : vrE) (pcn : Z) (g i : nat) : world SEGS -> config -> Prop := fun W' cf' =>
vr_rt B MT e (VRR.route (Verbs.toks (e_D e))) W' cf' \/ v6_dm B MT e pcn g i W' cf'.

Lemma v6_site0 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d718 0 0 W cf ->
SRr SEGS W cf (v6_out e 0x8d72c 0 1).
Proof. unfold v6_out. v6_strcmp_site 0x8d718 0%nat VRR.RAdd 0x8d72c 0%nat v6_lit_add [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.
Lemma v6_site1 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d72c 0 1 W cf ->
SRr SEGS W cf (v6_out e 0x8d744 1 2).
Proof. unfold v6_out. v6_strcmp_site 0x8d72c 1%nat VRR.RDget 0x8d744 1%nat v6_lit_dget [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.
Lemma v6_site2 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d744 1 2 W cf ->
SRr SEGS W cf (v6_out e 0x8d758 1 3).
Proof. unfold v6_out. v6_strcmp_site 0x8d744 2%nat VRR.RPget 0x8d758 1%nat v6_lit_pget [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.
Lemma v6_site4 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d788 1 4 W cf ->
SRr SEGS W cf (v6_out e 0x8d79c 1 5).
Proof. unfold v6_out. v6_strcmp_site 0x8d788 4%nat VRR.RWlist 0x8d79c 1%nat v6_lit_wlist [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.
Lemma v6_site5 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d79c 1 5 W cf ->
SRr SEGS W cf (v6_out e 0x8d7b0 1 6).
Proof. unfold v6_out. v6_strcmp_site 0x8d79c 5%nat VRR.RIinfo 0x8d7b0 1%nat v6_lit_iinfo [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.
Lemma v6_site6 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d7b0 1 6 W cf ->
SRr SEGS W cf (v6_out e 0x8d7c4 1 7).
Proof. unfold v6_out. v6_strcmp_site 0x8d7b0 6%nat VRR.RReset 0x8d7c4 1%nat v6_lit_reset [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.
Lemma v6_site7 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d7c4 1 7 W cf ->
SRr SEGS W cf (v6_out e 0x8d7d8 1 8).
Proof. unfold v6_out. v6_strcmp_site 0x8d7c4 7%nat VRR.RQclear 0x8d7d8 1%nat v6_lit_qclear [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.
Lemma v6_site8 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d7d8 1 8 W cf ->
SRr SEGS W cf (v6_out e 0x8d7f4 2 9).
Proof. unfold v6_out. v6_strcmp_site 0x8d7d8 8%nat VRR.RPolicy 0x8d7f4 2%nat v6_lit_policy [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26]. Qed.
Lemma v6_site9 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d7f4 2 9 W cf ->
SRr SEGS W cf (v6_out e 0x8d808 2 10).
Proof. unfold v6_out. v6_strcmp_site 0x8d7f4 9%nat VRR.RLv2 0x8d808 2%nat v6_lit_lv2 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.
Lemma v6_site10 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d808 2 10 W cf ->
SRr SEGS W cf (v6_out e 0x8d81c 2 11).
Proof. unfold v6_out. v6_strcmp_site 0x8d808 10%nat VRR.RPool 0x8d81c 2%nat v6_lit_pool [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.
Lemma v6_site11 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d81c 2 11 W cf ->
SRr SEGS W cf (v6_out e 0x8d830 2 12).
Proof. unfold v6_out. v6_strcmp_site 0x8d81c 11%nat VRR.REnv 0x8d830 2%nat v6_lit_env [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.
Lemma v6_site12 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d830 2 12 W cf ->
SRr SEGS W cf (v6_out e 0x8d844 2 13).
Proof. unfold v6_out. v6_strcmp_site 0x8d830 12%nat VRR.RChain 0x8d844 2%nat v6_lit_chain [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.
Lemma v6_site13 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d844 2 13 W cf ->
SRr SEGS W cf (v6_out e 0x8d858 2 14).
Proof. unfold v6_out. v6_strcmp_site 0x8d844 13%nat VRR.RChclear 0x8d858 2%nat v6_lit_chclear [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.
Lemma v6_site14 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d858 2 14 W cf ->
SRr SEGS W cf (v6_out e 0x8d86c 2 15).
Proof. unfold v6_out. v6_strcmp_site 0x8d858 14%nat VRR.RPinset 0x8d86c 2%nat v6_lit_pinset [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.
Lemma v6_site15 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d86c 2 15 W cf ->
SRr SEGS W cf (v6_out e 0x8d880 2 16).
Proof. unfold v6_out. v6_strcmp_site 0x8d86c 15%nat VRR.RPinacc 0x8d880 2%nat v6_lit_pinacc [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.
Lemma v6_site16 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d880 2 16 W cf ->
SRr SEGS W cf (v6_out e 0x8d894 2 17).
Proof. unfold v6_out. v6_strcmp_site 0x8d880 16%nat VRR.RPinclr 0x8d894 2%nat v6_lit_pinclr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]. Qed.





Lemma v6_upto_le : forall p l, (length (PV.upto p l) <= length l)%nat.
Proof. intros p l. induction l as [|b l IH]; cbn; [lia|]. destruct (p b); cbn; lia. Qed.

(* the inline verb_is(remove) (0x8d758-0x8d784): strcspn(tok[0], " \t") = 6, then strncmp(tok[0], "remove %i", 6) *)
Lemma v6_site3 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d758 1 3 W cf -> SRr SEGS W cf (v6_out e 0x8d788 1 4).
Proof.
unfold v6_out. v6_pre 0x8d758.
assert (Hlv : Z.of_nat (length (PV.tfirst (hd [] (Verbs.toks (e_D e))))) <= 8192).
{ pose proof Hcopy as (_ & _ & Hlen & _ & Hw).
  destruct (Verbs.toks (e_D e)) as [|w0 args] eqn:Et; [exfalso; exact (Hne eq_refl)|].
  destruct tp as [|p0 tps]; [cbn in Hlen; discriminate|].
  destruct (Hw 0%nat p0 w0 eq_refl eq_refl) as (_ & Hl8 & _).
  unfold PV.tfirst. cbn [hd]. pose proof (v6_upto_le PV.is_sep w0). lia. }
apply (CSPN e pos F q c tp lyc Sc W regsc memc mdc k nm _ (ms_regs ms1) (ms_mem ms1) mdv _ _
  Hcore Hcopy Hne HJ KOc Qsp Q1 ltac:(apply ret_ok_codeptr_v; [lia | reflexivity]) Q3 Q4 Q10 Q11).
intros regs2 mem2 md2 HJ2 HP2 HQ2 HKO2.
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2.
lazymatch type of HS2 with ?P -> _ =>
  assert (HQ : P) by
    (constructor; [|constructor]; split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ms_mem restrict];
     intros a Ha; [|lia];
     apply (mbyte_of_aview SEGS); rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9 in Ha; unfold w64 in Ha;
     rewrite unsigned_lit_small in Ha by (unfold vr_sp0 in *; lia);
     rewrite (HKO2 a ltac:(unfold vr_sp0 in *; lia) ltac:(lia)); symmetry; apply KOc; [unfold vr_sp0 in *; lia | lia]);
  specialize (HS2 HQ); clear HQ end.
rewrite <- restrict_mkst_fx in HS2.
pose proof (img_env_havoc_hi E 1024 (map (getr regs2) CLOB) HEI ltac:(unfold A_LIM; lia)) as HEI2.
assert (Ua0 : U (havoc E 1024 (map (getr regs2) CLOB)) (SOff 1028 0) = bv_unsigned (getr regs2 10)) by
  (unfold U; cbn [sv_denot]; change 1028%nat with (1024 + 4)%nat;
   rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbn; lia); unfold CLOB; cbn [map nth];
   rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (HAE2 : env_agree 32 (Ereg regsc (v6_extra F q)) (havoc E 1024 (map (getr regs2) CLOB)))
  by (apply v6_env_agree_havoc; [lia | exact HAE]).
paj_run_sh RUNP HS2 HJ2.
{ awr_ok_tac. }
match goal with |- context [with_vm_backing (m_vm_lazy md2) ?mt md2] =>
  set (mdv2 := with_vm_backing (m_vm_lazy md2) mt md2) in * end. clearbody mdv2.
cbn [ms_mem mkst] in HFr.
pose proof (v6_rdeq_frame _ _ _ _ _ HFr ltac:(repeat constructor; cbn; lia)) as Eq2. clear HF HFr HG.
pose proof (v6_KO_trans e W memc mem2 _ HKO2 (v6_KO_eq e W mem2 _ (fun a _ => Eq2 a))) as KO2.
rewrite HQ2 in Ua0.
assert (Ul : bv_unsigned (w64 (Z.of_nat (length (PV.tfirst (hd [] (Verbs.toks (e_D e))))))) =
  Z.of_nat (length (PV.tfirst (hd [] (Verbs.toks (e_D e)))))) by (unfold w64; apply unsigned_lit_small; lia).
rewrite Ul in Ua0.
psrr_branch_pi RUNP BR HS2.
- (* strcspn <> 6: not remove *)
  rewrite branch_ne_U, Ua0 in Hc.
  assert (Hl6 : length (PV.tfirst (hd [] (Verbs.toks (e_D e)))) <> 6%nat).
  { intros Hl. rewrite Hl in Hc. vm_compute in Hc. discriminate Hc. }
  assert (Hr : VRR.route (Verbs.toks (e_D e)) =
    v6_casc (skipn 4 v6_tests) (hd [] (Verbs.toks (e_D e))) (tl (Verbs.toks (e_D e)))).
  { apply (v6_miss 3 _ _ _ _ eq_refl Hroute). cbv beta. unfold PV.verb_is_m.
    replace (Nat.eqb (length (PV.tfirst (hd [] (Verbs.toks (e_D e))))) (length (PV.vfirst PV.Lit.fmt_remove))) with false;
      [reflexivity|].
    symmetry. apply Nat.eqb_neq. change (length (PV.vfirst PV.Lit.fmt_remove)) with 6%nat. exact Hl6. }
  paj_run_to_sh RUNTO HS2 HJ2 29348.
  { awr_ok_tac. }
  match goal with |- context [with_vm_backing (m_vm_lazy mdv2) ?mt mdv2] =>
    set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mt mdv2) in * end. clearbody mdv3.
  pose proof (v6_rdeq_frame _ _ _ _ _ HFr ltac:(repeat constructor; cbn; lia)) as Eq3. clear HF HFr HG.
  match goal with H : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => set (ms3 := m) in * end.
  pose proof (v6_kept_regs _ _ _ regsc (v6_extra F q) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS2 HAE2
    ltac:(vm_compute; reflexivity)) as KR3. cbn [ms_regs restrict] in KR3.
  pose proof (v6_KO_trans e W memc _ (ms_mem ms3) KO2 (v6_KO_eq e W _ (ms_mem ms3) (fun a _ => Eq3 a))) as HKO3.
  assert (Hrv3 : vr_rv (ms_regs ms3) (vr_base B e ++ v6_rl e F q (hd 0 tp) 1)).
  { apply (v6_rv_keep B e (ms_regs ms3) regsc _ _ Hrv); [intros r0 Hr0; apply KR3; cbn in Hr0 |- *; tauto|].
    intros r0 v0 Hin. left. split; [exact Hin | apply KR3; unfold v6_rl in Hin; cbn [app In] in Hin;
      repeat (destruct Hin as [E0|Hin]; [injection E0 as <- <-; cbn; tauto|]); destruct Hin]. }
  pmkst HS2. apply SRr_ret. right.
  exists pos, F, q, c, tp, lyc, Sc, (ms_regs ms3), (ms_mem ms3), mdv3, k, nm.
  split; [apply v6_cfg2; reflexivity|].
  split; [exact Hne|]. split; [exact Hr|].
  exact (v6_exit B MT TL e pos F q c tp lyc Sc W regsc memc mdc k nm _ (ms_regs ms3) (ms_mem ms3) mdv3 _ Hent Hcore Hline Hcopy
    HJ2 HKO3 Hrv3).
- (* strcspn = 6: strncmp(tok[0], "remove %i", 6) *)
  rewrite branch_ne_U, Ua0 in Hc.
  assert (H6 : Z.of_nat (length (PV.tfirst (hd [] (Verbs.toks (e_D e))))) = 6).
  { apply negb_false_iff, Z.eqb_eq in Hc. rewrite Hc. reflexivity. }
  paj_run_shc RUNP RUNC HS2 HJ2.
  { awr_ok_tac. }
  match goal with |- context [with_vm_backing (m_vm_lazy mdv2) ?mt mdv2] =>
    set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mt mdv2) in * end. clearbody mdv3.
  match goal with H : st_ok _ _ _ (restrict _ ?m) |- _ => set (ms3 := m) in * end.
  pose proof (v6_rdeq_frame _ _ _ _ _ HFr ltac:(repeat constructor; cbn; lia)) as Eq3. clear HF HFr HG.
  pose proof (v6_KO_trans e W memc _ (ms_mem ms3) KO2 (v6_KO_eq e W _ (ms_mem ms3) (fun a _ => Eq3 a))) as KOc2.
  prreg HS2 (Z_to_bv 5 1) Q1b. prreg HS2 (Z_to_bv 5 10) Q10b. prreg HS2 (Z_to_bv 5 11) Q11b. prreg HS2 (Z_to_bv 5 12) Q12b.
  rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl) in Q10b.
  rewrite (v6_rv_get regsc _ 26 (hd 0 tp) Hrv ltac:(unfold vr_base, v6_rl; cbn; tauto)) in Q10b.
  assert (Xlit2 : ew E 326 = Z_to_bv 64 0x225c0)
    by (rewrite (img_env_atomP E 326 HEI ltac:(unfold A_TEXT, A_LIM; lia)); change 326%nat with (A_OBJ 85);
        rewrite (HVOBJ 85%nat ltac:(vm_compute; lia)); reflexivity).
  rewrite Xlit2 in Q11b.
  pose proof (v6_kept_regs _ _ _ regsc (v6_extra F q) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS2 HAE2
    ltac:(vm_compute; reflexivity)) as KRb. cbn [ms_regs restrict] in KRb.
  assert (Qspb : spZ (ms_regs ms3) = vr_s1 e) by
    (change (spZ (ms_regs ms3)) with (bv_unsigned (getr (ms_regs ms3) (Z_to_bv 5 2))); rewrite (KRb 2 ltac:(cbn; tauto)), R2;
     unfold w64; rewrite unsigned_lit_small by (unfold vr_sp0 in *; lia); reflexivity).
  assert (Q3b : getr (ms_regs ms3) (Z_to_bv 5 3) = w64 (as_gp B)) by (rewrite (KRb 3 ltac:(cbn; tauto)); exact R3).
  assert (Q4b : getr (ms_regs ms3) (Z_to_bv 5 4) = w64 (as_tp B)) by (rewrite (KRb 4 ltac:(cbn; tauto)); exact R4).
  pmkst HS2.
  apply (NCMP e pos F q c tp lyc Sc W regsc memc mdc k nm _ (ms_regs ms3) (ms_mem ms3) mdv3 _ _
    Hcore Hcopy Hne H6 HJ2 KOc2 Qspb Q1b ltac:(apply ret_ok_codeptr_v; [lia | reflexivity]) Q3b Q4b Q10b Q11b Q12b).
  intros regs3 mem3 md3 HJ3 HP3 HQ3 HKO3.
  jafter_call_keep_hi HS2 1040%nat regs3 (mrestrict (w_H W) mem3) HP3 (@nil nat) HS3.
  specialize (HS3 (Forall_nil _)). rewrite <- restrict_mkst_fx in HS3.
  pose proof (img_env_havoc_hi _ 1040 (map (getr regs3) CLOB) HEI2 ltac:(unfold A_LIM; lia)) as HEI3.
  assert (Ub0 : U (havoc (havoc E 1024 (map (getr regs2) CLOB)) 1040 (map (getr regs3) CLOB)) (SOff 1044 0) =
    bv_unsigned (getr regs3 10)) by
    (unfold U; cbn [sv_denot]; change 1044%nat with (1040 + 4)%nat;
     rewrite (ew_havoc_new _ 1040 _ 4 (Z_to_bv 64 0)) by (cbn; lia); unfold CLOB; cbn [map nth];
     rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (HAE3 : env_agree 32 (Ereg regsc (v6_extra F q))
    (havoc (havoc E 1024 (map (getr regs2) CLOB)) 1040 (map (getr regs3) CLOB)))
    by (apply v6_env_agree_havoc; [lia | exact HAE2]).
  psrr_branch_pi RUNP BR HS3.
  + (* strncmp returned 0: remove *)
    rewrite branch_eq_U, Ub0 in Hc0.
    assert (H0 : getr regs3 10 = w64 0).
    { apply Z.eqb_eq in Hc0. unfold U in Hc0. cbn [sv_denot] in Hc0. rewrite unsigned_lit_small in Hc0 by lia.
      apply bv_eq. rewrite Hc0. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    apply HQ3 in H0.
    assert (Hr : VRR.route (Verbs.toks (e_D e)) = VRR.RRemove) by (apply (v6_hit 3 _ _ _ _ eq_refl Hroute); cbv beta; exact H0).
    paj_run_to_sh RUNTO HS3 HJ3 29976.
    { awr_ok_tac. }
    match goal with |- context [with_vm_backing (m_vm_lazy md3) ?mt md3] =>
      set (mdv4 := with_vm_backing (m_vm_lazy md3) mt md3) in * end. clearbody mdv4.
    pose proof (v6_rdeq_frame _ _ _ _ _ HFr ltac:(repeat constructor; cbn; lia)) as Eq4. clear HF HFr HG.
    match goal with H : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => set (msq := m) in * end.
    pose proof (v6_kept_regs _ _ _ regsc (v6_extra F q) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS3 HAE3
      ltac:(vm_compute; reflexivity)) as KR4. cbn [ms_regs restrict] in KR4.
    pose proof (v6_KO_trans e W memc _ (ms_mem msq) HKO3 (v6_KO_eq e W _ (ms_mem msq) (fun a _ => Eq4 a))) as HKO4.
    assert (Hrv4 : vr_rv (ms_regs msq) (vr_base B e ++ v6_rl e F q (hd 0 tp) 1)).
    { apply (v6_rv_keep B e (ms_regs msq) regsc _ _ Hrv); [intros r0 Hr0; apply KR4; cbn in Hr0 |- *; tauto|].
      intros r0 v0 Hin. left. split; [exact Hin | apply KR4; unfold v6_rl in Hin; cbn [app In] in Hin;
        repeat (destruct Hin as [E0|Hin]; [injection E0 as <- <-; cbn; tauto|]); destruct Hin]. }
    pmkst HS3. apply SRr_ret. left.
    exists pos, F, q, c, tp, lyc, Sc, (ms_regs msq), (ms_mem msq), mdv4, k, nm.
    split; [rewrite Hr; apply v6_cfg2; reflexivity|].
    split; [reflexivity|]. split; [exact Hne|].
    rewrite v6_rl_rt, Hr. cbn [vr_rgroup].
    exact (v6_exit B MT TL e pos F q c tp lyc Sc W regsc memc mdc k nm _ (ms_regs msq) (ms_mem msq) mdv4 _ Hent Hcore Hline Hcopy
      HJ3 HKO4 Hrv4).
  + (* strncmp returned a nonzero value: the next test *)
    rewrite branch_eq_U, Ub0 in Hc0.
    assert (H0 : PV.verb_is_m (hd [] (Verbs.toks (e_D e))) PV.Lit.fmt_remove = false).
    { destruct (PV.verb_is_m (hd [] (Verbs.toks (e_D e))) PV.Lit.fmt_remove) eqn:Ev; [|reflexivity].
      exfalso. assert (Hz : getr regs3 10 = w64 0) by (apply HQ3; reflexivity).
      rewrite Hz in Hc0. vm_compute in Hc0. discriminate Hc0. }
    assert (Hr : VRR.route (Verbs.toks (e_D e)) =
      v6_casc (skipn 4 v6_tests) (hd [] (Verbs.toks (e_D e))) (tl (Verbs.toks (e_D e))))
      by (apply (v6_miss 3 _ _ _ _ eq_refl Hroute); cbv beta; exact H0).
    paj_run_to_sh RUNTO HS3 HJ3 29348.
    { awr_ok_tac. }
    match goal with |- context [with_vm_backing (m_vm_lazy md3) ?mt md3] =>
      set (mdv4 := with_vm_backing (m_vm_lazy md3) mt md3) in * end. clearbody mdv4.
    pose proof (v6_rdeq_frame _ _ _ _ _ HFr ltac:(repeat constructor; cbn; lia)) as Eq4. clear HF HFr HG.
    match goal with H : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => set (msq := m) in * end.
    pose proof (v6_kept_regs _ _ _ regsc (v6_extra F q) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS3 HAE3
      ltac:(vm_compute; reflexivity)) as KR4. cbn [ms_regs restrict] in KR4.
    pose proof (v6_KO_trans e W memc _ (ms_mem msq) HKO3 (v6_KO_eq e W _ (ms_mem msq) (fun a _ => Eq4 a))) as HKO4.
    assert (Hrv4 : vr_rv (ms_regs msq) (vr_base B e ++ v6_rl e F q (hd 0 tp) 1)).
    { apply (v6_rv_keep B e (ms_regs msq) regsc _ _ Hrv); [intros r0 Hr0; apply KR4; cbn in Hr0 |- *; tauto|].
      intros r0 v0 Hin. left. split; [exact Hin | apply KR4; unfold v6_rl in Hin; cbn [app In] in Hin;
        repeat (destruct Hin as [E0|Hin]; [injection E0 as <- <-; cbn; tauto|]); destruct Hin]. }
    pmkst HS3. apply SRr_ret. right.
    exists pos, F, q, c, tp, lyc, Sc, (ms_regs msq), (ms_mem msq), mdv4, k, nm.
    split; [apply v6_cfg2; reflexivity|].
    split; [exact Hne|]. split; [exact Hr|].
    exact (v6_exit B MT TL e pos F q c tp lyc Sc W regsc memc mdc k nm _ (ms_regs msq) (ms_mem msq) mdv4 _ Hent Hcore Hline Hcopy
      HJ3 HKO4 Hrv4).
Qed.

(* the event count of a route is not negative (the unfolding of HarnessArgsEv.v's ev_route_le, for any recorder) *)
Ltac v6_ev_unfold :=
  unfold ev_route, ev_step, ev_call, ev_after,
    EV_CHAIN_WORDS, EV_PIN_SET_WORDS, EV_SUP_ADD, EV_DESCRIPTORS_ADD, EV_DESCRIPTORS_GET, EV_DESCRIPTORS_PANEL_GET,
    EV_SUP_REMOVE, EV_SUP_REMOVE_ALL, EV_SUP_WORKER_LIST, EV_SUP_INSTANCE_INFO, EV_SUP_RESET, EV_SUP_QUARANTINE_CLEAR,
    EV_SUP_POLICY_SET, EV_SUP_LV2_WORKER_SET, EV_SUP_POOL_CONFIG, EV_SUP_WORKER_ENV, EV_SUP_CHAIN, EV_SUP_CHAIN_CLEAR,
    EV_SUP_PIN_ACCEPT, EV_SUP_INSTANCE_VERB, EV_SUP_CALL, EV_SUP_CONNECT, EV_SUP_REPLY_CODE, EV_PINS_SET,
    EV_PINS_CLEAR, EV_LV2_REFUSALS_FORGET, EV_SUP_BROADCAST, EV_SUP_HOST_SETTING, EV_SUP_AFTER_REPLY, EV_SUP_RESP,
    EV_ANSWER_CODE, EV_ANSWER, EV_HAND_BACK, EV_ARG_I, EV_ARG_LINE, EV_REC_CANONICAL, EV_XSTRDUP, rec_spill_frees.
Ltac v6_rec_unfold :=
  unfold sup_add_m, sup_broadcast_m, pins_set_m, pins_clear_m, rec_stub_code, rec_answer_code, rec_stub,
    rec_answer, hand_back, rec_record, rec_mix.
Ltac v6_ifs := repeat (match goal with |- context [if ?c then _ else _] =>
  lazymatch c with context [if _ then _ else _] => fail | _ => destruct c end end; cbn).
Lemma v6_ev_step_nn : forall R s, 0 <= ev_step R s.
Proof.
intros R s. destruct s as [c0|c|u i p q|u f l v|u| |ln tk]; [|destruct c|..];
  v6_ev_unfold; v6_rec_unfold; cbn; v6_ifs; lia.
Qed.
Lemma v6_ev_route_nn : forall R ln tk s, 0 <= ev_route R ln tk s.
Proof.
intros R ln tk s. pose proof (v6_ev_step_nn R s) as Hs. unfold ev_route.
destruct tk as [|v args]; [v6_ev_unfold; lia|].
destruct (Verbs.list_eqb v Verbs.Lit.verb_chain); [v6_ev_unfold; v6_rec_unfold; cbn; v6_ifs; lia|].
destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_set); [|lia].
unfold EV_PIN_SET_WORDS. destruct (Verbs.pin_set_words_m ln args); v6_ev_unfold; v6_rec_unfold; cbn; v6_ifs; lia.
Qed.
Lemma v6_ev_vr_ge : forall R D, 2 <= ev_vr R D.
Proof.
intros R D. rewrite ev_vr_eq. unfold vr_k3, vr_k2, vr_k1.
pose proof (v6_ev_route_nn R (Verbs.line D) (Verbs.toks D) (vr_st D)) as H1.
assert (H2 : 0 <= ev_after (vr_R2 R D) (vr_aft D)).
{ unfold ev_after. destruct (vr_aft D) as [[i v]|]; [|lia]. v6_ev_unfold; v6_rec_unfold; cbn; v6_ifs; lia. }
unfold EV_REPLY, EV_SOCKET_SEND in *. lia.
Qed.

(* the last test, verb_is(tok[0], "quit") (0x8d894-0x8d8a4): verb_is through its contract; 0 leaves for the scan
   of g_instance_info_verbs (0x8dd70), 1 for the quit verb (0x8d8a8) *)
Lemma v6_site17 : forall e W cf, vr_ent B MT e -> v6_dm B MT e 0x8d894 2 17 W cf ->
SRr SEGS W cf (fun W' cf' => vr_rt B MT e (VRR.route (Verbs.toks (e_D e))) W' cf').
Proof.
v6_pre 0x8d894.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HlenD & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & Hevb & _).
assert (Hev : st_nev Sc + EV_VERB_IS <= EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _). pose proof Hcore as (_ & Hkk & _).
  pose proof (v6_ev_vr_ge (e_R e) (e_D e)) as Hg. unfold EV_VERB_IS. lia. }
assert (Hrv1 : vr_rv (ms_regs ms1) (vr_base B e ++ v6_rl e F q (hd 0 tp) 2)).
{ apply (v6_rv_keep B e (ms_regs ms1) regsc _ _ Hrv); [intros r0 Hr0; apply KR; cbn in Hr0 |- *; tauto|].
  intros r0 v0 Hin. left. split; [exact Hin | apply KR; unfold v6_rl in Hin; cbn [app In] in Hin;
    repeat (destruct Hin as [E0|Hin]; [injection E0 as <- <-; cbn; tauto|]); destruct Hin]. }
destruct (v6_exit B MT TL e pos F q c tp lyc Sc W regsc memc mdc k nm _ (ms_regs ms1) (ms_mem ms1) mdv _ Hent Hcore Hline Hcopy
  HJ KOc Hrv1) as (Hcore1 & Hline1 & Hcopy1).
pose proof (proj1 HJ) as HAR1.
pose proof (v6_ent_len B MT e Hent) as HDn.
apply (VISTEP e pos F q c tp lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv k nm _ (ms_regs ms1) (ms_mem ms1) mdv _ _
  Hent Hcore1 Hcopy1 Hne HJ (v6_KO_refl e W (ms_mem ms1)) Hev Qsp Q1 ltac:(apply ret_ok_codeptr_v; [lia | reflexivity])
  ltac:(pose proof pa_B_ok as HBo; pose proof pa_base_lo as HBl; rewrite unsigned_lit_small; lia) Q3 Q4 Q10 Q11).
intros W2 regs2 mem2 md2 HJ2 HJc HP2 HQ2.
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W2) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)). rewrite <- restrict_mkst_fx in HS2.
pose proof (img_env_havoc_hi E 1024 (map (getr regs2) CLOB) HEI ltac:(unfold A_LIM; lia)) as HEI2.
assert (Ua0 : U (havoc E 1024 (map (getr regs2) CLOB)) (SOff 1028 0) = bv_unsigned (getr regs2 10)) by
  (unfold U; cbn [sv_denot]; change 1028%nat with (1024 + 4)%nat;
   rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbn; lia); unfold CLOB; cbn [map nth];
   rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (HAE2 : env_agree 32 (Ereg regsc (v6_extra F q)) (havoc E 1024 (map (getr regs2) CLOB)))
  by (apply v6_env_agree_havoc; [lia | exact HAE]).
pose proof HJ2 as HJ2m.
rewrite HQ2 in Ua0.
psrr_branch_pi RUNP BR HS2.
- (* verb_is returned 0: the scan of g_instance_info_verbs *)
  rewrite branch_eq_U, Ua0 in Hc.
  assert (Hvi : PV.verb_is_m (hd [] (Verbs.toks (e_D e))) PV.Lit.fmt_quit = false).
  { destruct (PV.verb_is_m (hd [] (Verbs.toks (e_D e))) PV.Lit.fmt_quit) eqn:Ev; [|reflexivity].
    vm_compute in Hc. discriminate Hc. }
  assert (Hr : VRR.route (Verbs.toks (e_D e)) = VRR.route_tail (hd [] (Verbs.toks (e_D e))) (tl (Verbs.toks (e_D e)))).
  { rewrite (v6_miss 17 _ _ _ _ eq_refl Hroute ltac:(cbv beta; exact Hvi)). reflexivity. }
  paj_run_to_sh RUNTO HS2 HJ2 30860.
  { awr_ok_tac. }
  match goal with |- context [with_vm_backing (m_vm_lazy md2) ?mt md2] =>
    set (mdv3 := with_vm_backing (m_vm_lazy md2) mt md2) in * end. clearbody mdv3.
  pose proof (v6_rdeq_frame _ _ _ _ _ HFr ltac:(repeat constructor; cbn; lia)) as Eq3. clear HF HFr HG.
  match goal with H : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => set (msz := m) in * end.
  pose proof (v6_kept_regs _ _ _ regsc (v6_extra F q) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS2 HAE2
    ltac:(vm_compute; reflexivity)) as KR3. cbn [ms_regs restrict] in KR3.
  assert (Hrv3 : vr_rv (ms_regs msz) (vr_base B e ++ v6_rl e F q (hd 0 tp) 2)).
  { apply (v6_rv_keep B e (ms_regs msz) regsc _ _ Hrv); [intros r0 Hr0; apply KR3; cbn in Hr0 |- *; tauto|].
    intros r0 v0 Hin. left. split; [exact Hin | apply KR3; unfold v6_rl in Hin; cbn [app In] in Hin;
      repeat (destruct Hin as [E0|Hin]; [injection E0 as <- <-; cbn; tauto|]); destruct Hin]. }
  pose proof (CORJ e pos F _ _ _ _ _ _ _ _ k _ nm _ lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv W2 (ms_regs msz) mem2 md2 _ _
    Hcore1 HJc HJ2m ltac:(unfold vr_sl3; repeat constructor; cbn [fst]; lia) Hrv3) as Hcore2.
  destruct (v6_lc_j B e pos F q c tp lyc Sc W (ms_mem ms1) mdv W2 mem2 md2 _ HAR1 Hlb Hcb Hin4 HFa HDn HJc Hline1 Hcopy1)
    as (Hline2 & Hcopy2).
  pmkst HS2. apply SRr_ret.
  exists pos, F, q, c, tp, lyc, Sc, (ms_regs msz), (ms_mem msz), mdv3, k, nm.
  split; [rewrite Hr, (proj1 (v6_tail_pc _ _)); apply v6_cfg2; reflexivity|].
  split; [reflexivity|]. split; [exact Hne|].
  rewrite v6_rl_rt, Hr, (proj2 (v6_tail_pc _ _)).
  exact (v6_exit B MT TL e pos F q c tp lyc Sc W2 (ms_regs msz) mem2 md2 k nm _ (ms_regs msz) (ms_mem msz) mdv3 _ Hent
    Hcore2 Hline2 Hcopy2 HJ2 (v6_KO_eq e W2 mem2 (ms_mem msz) (fun a _ => Eq3 a)) Hrv3).
- (* verb_is returned 1: quit *)
  rewrite branch_eq_U, Ua0 in Hc.
  assert (Hvi : PV.verb_is_m (hd [] (Verbs.toks (e_D e))) PV.Lit.fmt_quit = true).
  { destruct (PV.verb_is_m (hd [] (Verbs.toks (e_D e))) PV.Lit.fmt_quit) eqn:Ev; [reflexivity|].
    vm_compute in Hc. discriminate Hc. }
  assert (Hr : VRR.route (Verbs.toks (e_D e)) = VRR.RQuit)
    by (apply (v6_hit 17 _ _ _ _ eq_refl Hroute); cbv beta; exact Hvi).
  paj_run_to_sh RUNTO HS2 HJ2 29636.
  { awr_ok_tac. }
  match goal with |- context [with_vm_backing (m_vm_lazy md2) ?mt md2] =>
    set (mdv3 := with_vm_backing (m_vm_lazy md2) mt md2) in * end. clearbody mdv3.
  pose proof (v6_rdeq_frame _ _ _ _ _ HFr ltac:(repeat constructor; cbn; lia)) as Eq3. clear HF HFr HG.
  match goal with H : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => set (msz := m) in * end.
  pose proof (v6_kept_regs _ _ _ regsc (v6_extra F q) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS2 HAE2
    ltac:(vm_compute; reflexivity)) as KR3. cbn [ms_regs restrict] in KR3.
  assert (Hrv3 : vr_rv (ms_regs msz) (vr_base B e ++ v6_rl e F q (hd 0 tp) 2)).
  { apply (v6_rv_keep B e (ms_regs msz) regsc _ _ Hrv); [intros r0 Hr0; apply KR3; cbn in Hr0 |- *; tauto|].
    intros r0 v0 Hin. left. split; [exact Hin | apply KR3; unfold v6_rl in Hin; cbn [app In] in Hin;
      repeat (destruct Hin as [E0|Hin]; [injection E0 as <- <-; cbn; tauto|]); destruct Hin]. }
  pose proof (CORJ e pos F _ _ _ _ _ _ _ _ k _ nm _ lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv W2 (ms_regs msz) mem2 md2 _ _
    Hcore1 HJc HJ2m ltac:(unfold vr_sl3; repeat constructor; cbn [fst]; lia) Hrv3) as Hcore2.
  destruct (v6_lc_j B e pos F q c tp lyc Sc W (ms_mem ms1) mdv W2 mem2 md2 _ HAR1 Hlb Hcb Hin4 HFa HDn HJc Hline1 Hcopy1)
    as (Hline2 & Hcopy2).
  pmkst HS2. apply SRr_ret.
  exists pos, F, q, c, tp, lyc, Sc, (ms_regs msz), (ms_mem msz), mdv3, k, nm.
  split; [rewrite Hr; apply v6_cfg2; reflexivity|].
  split; [reflexivity|]. split; [exact Hne|].
  rewrite v6_rl_rt, Hr. cbn [vr_rgroup].
  exact (v6_exit B MT TL e pos F q c tp lyc Sc W2 (ms_regs msz) mem2 md2 k nm _ (ms_regs msz) (ms_mem msz) mdv3 _ Hent
    Hcore2 Hline2 Hcopy2 HJ2 (v6_KO_eq e W2 mem2 (ms_mem msz) (fun a _ => Eq3 a)) Hrv3).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   S06: the entry, the 18 tests in the order of the code, each leaving for its route or for the next test *)
Lemma vr_s06 : vr_s06_stmt B MT.
Proof.
intros e W cf Hent Hb.
eapply SRr_bind; [exact (v6_entry e W cf Hent Hb)|]. intros W0 c0 _ H0.
eapply SRr_bind; [exact (v6_site0 e W0 c0 Hent H0)|]. intros W1 c1 _ [H1|H1]; [apply SRr_ret; exact H1|].
eapply SRr_bind; [exact (v6_site1 e W1 c1 Hent H1)|]. intros W2 c2 _ [H2|H2]; [apply SRr_ret; exact H2|].
eapply SRr_bind; [exact (v6_site2 e W2 c2 Hent H2)|]. intros W3 c3 _ [H3|H3]; [apply SRr_ret; exact H3|].
eapply SRr_bind; [exact (v6_site3 e W3 c3 Hent H3)|]. intros W4 c4 _ [H4|H4]; [apply SRr_ret; exact H4|].
eapply SRr_bind; [exact (v6_site4 e W4 c4 Hent H4)|]. intros W5 c5 _ [H5|H5]; [apply SRr_ret; exact H5|].
eapply SRr_bind; [exact (v6_site5 e W5 c5 Hent H5)|]. intros W6 c6 _ [H6|H6]; [apply SRr_ret; exact H6|].
eapply SRr_bind; [exact (v6_site6 e W6 c6 Hent H6)|]. intros W7 c7 _ [H7|H7]; [apply SRr_ret; exact H7|].
eapply SRr_bind; [exact (v6_site7 e W7 c7 Hent H7)|]. intros W8 c8 _ [H8|H8]; [apply SRr_ret; exact H8|].
eapply SRr_bind; [exact (v6_site8 e W8 c8 Hent H8)|]. intros W9 c9 _ [H9|H9]; [apply SRr_ret; exact H9|].
eapply SRr_bind; [exact (v6_site9 e W9 c9 Hent H9)|]. intros W10 c10 _ [H10|H10]; [apply SRr_ret; exact H10|].
eapply SRr_bind; [exact (v6_site10 e W10 c10 Hent H10)|]. intros W11 c11 _ [H11|H11]; [apply SRr_ret; exact H11|].
eapply SRr_bind; [exact (v6_site11 e W11 c11 Hent H11)|]. intros W12 c12 _ [H12|H12]; [apply SRr_ret; exact H12|].
eapply SRr_bind; [exact (v6_site12 e W12 c12 Hent H12)|]. intros W13 c13 _ [H13|H13]; [apply SRr_ret; exact H13|].
eapply SRr_bind; [exact (v6_site13 e W13 c13 Hent H13)|]. intros W14 c14 _ [H14|H14]; [apply SRr_ret; exact H14|].
eapply SRr_bind; [exact (v6_site14 e W14 c14 Hent H14)|]. intros W15 c15 _ [H15|H15]; [apply SRr_ret; exact H15|].
eapply SRr_bind; [exact (v6_site15 e W15 c15 Hent H15)|]. intros W16 c16 _ [H16|H16]; [apply SRr_ret; exact H16|].
eapply SRr_bind; [exact (v6_site16 e W16 c16 Hent H16)|]. intros W17 c17 _ [H17|H17]; [apply SRr_ret; exact H17|].
exact (v6_site17 e W17 c17 Hent H17).
Qed.

End e.
End f.
End d.
