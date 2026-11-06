(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the segment S24 (quit, 0x8d8a8-0x8d8c8 and 0x8ddf0-0x8ddf8) of the walk of
   verbs_receive on the ASan build of plugin-hostd/fuzz_command (lib/A/Prog/verbs_receive_iface.v vr_s24_stmt). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdAddr CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c answer_c answer_code_c hand_back_c arg_i_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_live verbs_receive_s20_k PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* the symbolic states of S24: at 0x8d8a8 with g_quitting a writable window (the quit arm stores into it) or with no
   region (the refusal arm); at 0x8d8c0, sup_resp's return, with the spill word s1+8 (shadow(F), atom 32) *)
Definition r_gq : YP09.region := YP09.mkRegion (Some (A_HI 277)) 944 948 944 948 [].
Definition ss24q : sstate := mkSS 29636 sr_atoms [r_gq] None (mkFacts [] [] []).
Definition r_spr24 : YP09.region := YP09.mkRegion (Some 9%nat) 8 16 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 32 0))].
Definition ss24j : sstate := mkSS 29660 sr_atoms [r_spr24] None (mkFacts [] [] []).

(* the model: the route RQuit; with no argument the step is quit (sup_resp(0), the flag set), else reject *)
Lemma route_cp_quit : forall v args, VRR.route (v :: args) = VRR.RQuit ->
  Verbs.list_eqb v Verbs.Lit.verb_chain = false /\ Verbs.list_eqb v Verbs.Lit.verb_pin_set = false.
Proof.
intros v args H. split.
- destruct (Verbs.list_eqb v Verbs.Lit.verb_chain) eqn:E; [exfalso|reflexivity].
  unfold VRR.route, VRR.route_mid in H. rewrite E in H. rt_chain H.
- destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_set) eqn:E; [exfalso|reflexivity].
  unfold VRR.route, VRR.route_mid in H. rewrite E in H. rt_chain H.
Qed.

Lemma quit_step : forall R D, VRR.route (Verbs.toks D) = VRR.RQuit -> length (Verbs.toks D) = 1%nat ->
  vr_h R D = (R, resp 0, true) /\ vr_k1 R D = 2 + EV_SUP_RESP.
Proof.
intros R D Hr Hl. destruct (Verbs.toks D) as [|v args] eqn:T; [cbn in Hl; lia|].
destruct args as [|a args]; [|cbn in Hl; lia].
assert (St : vr_st D = Verbs.SQuit).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. rewrite Hr. reflexivity. }
destruct (route_cp_quit v [] Hr) as [Hc1 Hc2].
split.
- unfold vr_h. rewrite St. reflexivity.
- unfold vr_k1. rewrite St, T. rewrite (ev_route_not_cp _ _ _ _ _ Hc1 Hc2). reflexivity.
Qed.

Lemma quit_rej : forall R D, VRR.route (Verbs.toks D) = VRR.RQuit -> Verbs.toks D <> [] ->
  length (Verbs.toks D) <> 1%nat ->
  vr_h R D = (R, resp (-902), false) /\ vr_k1 R D = 2 + EV_SUP_RESP.
Proof.
intros R D Hr Hne Hl. destruct (Verbs.toks D) as [|v args] eqn:T; [congruence|].
destruct args as [|a args]; [cbn in Hl; lia|].
assert (St : vr_st D = Verbs.reject).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. rewrite Hr. reflexivity. }
destruct (route_cp_quit v (a :: args) Hr) as [Hc1 Hc2].
split.
- unfold vr_h. rewrite St. reflexivity.
- unfold vr_k1. rewrite St, T. rewrite (ev_route_not_cp _ _ _ _ _ Hc1 Hc2). reflexivity.
Qed.

Lemma hd_ntok_9b4 : forall nt, nt = 1%nat -> vr_hd_ntok 0x8d9b4 nt.
Proof. intros nt H. unfold vr_hd_ntok. exact H. Qed.
Lemma hd_ntok_c94 : forall nt, (2 <= nt)%nat -> vr_hd_ntok 0x8dc94 nt.
Proof. intros nt H. unfold vr_hd_ntok. exact H. Qed.

Ltac s24_rv HS KR Hrv E10 E32 :=
  lazymatch goal with
  | |- getr _ ?r = w64 _ =>
    first [ rewrite KR by (cbn; tauto); apply (vk_rv_get _ _ _ _ Hrv); apply in_or_app;
            first [left; cbn; tauto | right; cbn; tauto]
          | let Hx := fresh "Hx" in prreg HS r Hx; rewrite Hx; clear Hx;
            first [exact E10 | exact E32 | (rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [exact E10 | exact E32])] ]
  end.

Section dt. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section ft.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section et.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.

(* the code after sup_resp returns (statement pass 4: sup_resp's post is FP-existential, so this part runs at the FP
   state the callee returns at; proved in its own section, it holds at every FP state). The quit arm: 0x8d8c0 mv a1,a0;
   ld s9,8(s1); j 0x8d9b4 *)
Lemma s24_quit_tail : forall e pos F q c tp tq k nm ly2 S2 W2 regs2 mem2 md2,
  vr_h (e_R e) (e_D e) = (e_R e, resp 0, true) -> length (Verbs.toks (e_D e)) = 1%nat ->
  4096 <= tq -> astr_atR (rdW W2 mem2) tq (resp 0) ->
  vr_core B MT e pos F ((tq, Z.of_nat (length (resp 0)) + 1) :: [vr_lb e q; vr_cb e c]) vr_sh2 (vr_sl3 F q c)
    [(10, tq); (18, q); (20, F); (27, shadow_addr F + 4)] (e_R e) (e_O e) 1 (k + EV_SUP_RESP) (vr_k1 (e_R e) (e_D e))
    (nm + 1) VR_NM_HD ly2 S2 W2 regs2 mem2 md2 ->
  vr_line B e q W2 mem2 -> vr_copy B e F c tp W2 mem2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 29660)) mem2 (seg_rom SEGS)) md2) (vr_athd B MT 0x8d9b4 e).
Proof.
intros e pos F q c tp tq k nm ly2 S2 W2 regs2 mem2 md2 Hvh H1 Htq Hstr HC2 HL2 HCP2.
pose proof HC2 as (HJ2 & _ & _ & _ & (EF & _ & _) & Hrv2 & _ & Hsp2 & _).
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (vr_s1_bounds e) as Hs1b.
assert (HV : 224 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hfr4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hfr4) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
pose proof (shadow_addr_bounds F ltac:(lia)) as HshF.
assert (R9 : getr regs2 (Z_to_bv 5 9) = w64 (vr_s1 e))
  by (apply (vk_rv_get regs2 _ _ _ Hrv2); apply in_or_app; left; cbn; tauto).
assert (R10 : getr regs2 (Z_to_bv 5 10) = w64 tq)
  by (apply (vk_rv_get regs2 _ _ _ Hrv2); apply in_or_app; right; cbn; tauto).
assert (Hav : aval_mem (rdW W2 mem2) (vr_s1 e + 8) 8 (shadow_addr F)).
{ unfold vr_spill in Hsp2; rewrite Forall_forall in Hsp2.
  exact (Hsp2 (8, shadow_addr F) ltac:(unfold vr_sl3; cbn; tauto)). }
set (E2 := Eimg (Ereg regs2 [w64 (shadow_addr F)])).
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (HAE2 : env_agree 32 (Ereg regs2 [w64 (shadow_addr F)]) E2) by (subst E2; apply vk_env_agree).
assert (E9 : bv_unsigned (ew E2 9%nat) = vr_s1 e).
{ subst E2. rewrite (ew_Eimg_Ereg_nat regs2 _ 9%nat (Z_to_bv 5 9) eq_refl), R9.
  unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew E2 32%nat = w64 (shadow_addr F)).
{ subst E2. rewrite Eimg_low by (unfold A_TEXT; lia).
  pose proof (ew_Ereg_extra regs2 [w64 (shadow_addr F)] 0%nat) as HH. cbn [Nat.add nth] in HH. exact HH. }
assert (E10 : ew E2 10%nat = w64 tq)
  by (subst E2; rewrite (ew_Eimg_Ereg_nat regs2 _ 10%nat (Z_to_bv 5 10) eq_refl); exact R10).
assert (HS2 : st_ok_pi SEGS VAL E2 ss24j
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 29660)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss24j. apply pa_entry_st_ok_full.
  - subst E2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold r_spr24, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E2 _ (vr_s1 e) 8 8%N (SOff 32 0) (shadow_addr F)).
    + cbn [sv_denot]. rewrite E32. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn. lia.
    + apply aval_val_mem. exact Hav.
  - cbn. tauto.
  - split; [exact I | split; exact I]. }
(* 0x8d8c0: mv a1,a0; ld s9,8(s1); j 0x8d9b4 *)
paj_run_to_shc RUNTO HS2 HJ2 29904.
{ unfold ss24j; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
assert (Hro : rs_read_only (ss_mem ss24j) = true) by (vm_compute; reflexivity).
lazymatch goal with
| Hfx : frame_of _ _ _ (ms_mem _) |- _ =>
  pose proof (frame_of_read_only _ _ _ _ Hro Hfx) as Hmem; cbn [ms_mem mkst] in Hmem
end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdv3 := m) in *; clearbody mdv3 end.
pose proof (vk_kept_regs E2 _ _ regs2 [w64 (shadow_addr F)] [2; 3; 4; 8; 9; 18; 20; 27] HS2 HAE2
  ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
pmkst HS2. rewrite Hmem in HJ2 |- *.
apply SRr_ret. unfold vr_athd, vr_hd.
assert (EX : vr_x (e_R e) (e_D e) = resp 0) by (unfold vr_x; rewrite Hvh; reflexivity).
assert (ER1 : vr_R1 (e_R e) (e_D e) = e_R e) by (unfold vr_R1; rewrite Hvh; reflexivity).
assert (EQV : vr_qv e = 1) by (unfold vr_qv, vr_quit; rewrite Hvh; reflexivity).
lazymatch goal with |- context [mkCfg (mkst ?rg _ _ _) _] =>
  exists tq, (e_O e), pos, F, q, c, tp, ly2, S2, rg, mem2, mdv3, (k + EV_SUP_RESP), (nm + 1) end.
split; [unfold cfg_at, w64; replace (vr_pc 0x8d9b4) with (BASE + 29904) by (unfold vr_pc, AF_verbs_receive; lia);
  reflexivity|].
split; [exact (hd_ntok_9b4 _ H1)|].
split; [lia|].
split; [rewrite EX; exact Hstr|].
rewrite EX, ER1, EQV.
split; [|split; [exact HL2 | exact HCP2]].
eapply (vk_regs B MT); [exact HC2 | exact HJ2 |].
unfold vr_rv, vr_base, vr_rl_hd. cbn [Z.eqb Pos.eqb app].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; s24_rv HS2 KR2 Hrv2 E10 E32.
Qed.

(* the refusal arm: sup_resp(-902) returned to 0x8ddf4 (j 0x8dc94) *)
Lemma s24_rej_tail : forall e pos F q c tp tq k nm ly2 S2 W2 regs2 mem2 md2,
  vr_h (e_R e) (e_D e) = (e_R e, resp (-902), false) -> (2 <= length (Verbs.toks (e_D e)))%nat ->
  4096 <= tq -> astr_atR (rdW W2 mem2) tq (resp (-902)) ->
  vr_core B MT e pos F ((tq, Z.of_nat (length (resp (-902))) + 1) :: [vr_lb e q; vr_cb e c]) vr_sh2 (vr_sl3 F q c)
    [(10, tq); (18, q); (20, F); (22, F + 32); (27, shadow_addr F + 4)] (e_R e) (e_O e) (e_q0 e) (k + EV_SUP_RESP)
    (vr_k1 (e_R e) (e_D e)) (nm + 1) VR_NM_HD ly2 S2 W2 regs2 mem2 md2 ->
  vr_line B e q W2 mem2 -> vr_copy B e F c tp W2 mem2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 30996)) mem2 (seg_rom SEGS)) md2) (vr_athd B MT 0x8dc94 e).
Proof.
intros e pos F q c tp tq k nm ly2 S2 W2 regs2 mem2 md2 Hvh H2 Htq Hstr HC2 HL2 HCP2.
pose proof HC2 as (HJ2 & _ & _ & _ & _ & Hrv2 & _).
apply (vk_jmp B 30996 30640 ltac:(lia) ltac:(vm_compute; reflexivity) W2 regs2 mem2 md2 _ _ _ _ _ _ _ _ _ _
  ly2 S2 _ HJ2).
intros regs3 md3 Er HJ3.
unfold vr_athd, vr_hd.
exists tq, (e_O e), pos, F, q, c, tp, ly2, S2, regs3, mem2, md3, (k + EV_SUP_RESP), (nm + 1).
assert (EX : vr_x (e_R e) (e_D e) = resp (-902)) by (unfold vr_x; rewrite Hvh; reflexivity).
assert (ER1 : vr_R1 (e_R e) (e_D e) = e_R e) by (unfold vr_R1; rewrite Hvh; reflexivity).
assert (EQV : vr_qv e = e_q0 e) by (unfold vr_qv, vr_quit; rewrite Hvh; reflexivity).
split; [unfold cfg_at, w64; replace (vr_pc 0x8dc94) with (BASE + 30640) by (unfold vr_pc, AF_verbs_receive; lia);
  reflexivity|].
split; [exact (hd_ntok_c94 _ H2)|].
split; [lia|].
split; [rewrite EX; exact Hstr|].
rewrite EX, ER1, EQV.
split; [|split; [exact HL2 | exact HCP2]].
eapply (vk_regs B MT); [exact HC2 | exact HJ3 |].
apply (vk_rv_kept regs2 _ _ Hrv2). intros r v _. apply Er.
Qed.

End et.
End ft.
End dt.

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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the callee's contract (verbs_receive_c.v:219) and the named record facts *)
Hypothesis TSUP_RESP : forall fx0 : YK11.FPState, @tsup_resp_spec fx0 rc SK PI B MT.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VHIS : cmd_val_his (PI := PI).
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).

(* the auipc at 0x8d8b0 is the listing's PHi atom A_HI 277 (CmdObj's cmd_val_his) *)
Lemma vhis_277 : VAL (A_HI 277) = 0x5e38b0.
Proof. rewrite (VHIS 277%nat) by (apply Nat.ltb_lt; vm_compute; reflexivity). vm_compute. reflexivity. Qed.

Lemma vr_s24 : vr_s24_stmt B MT.
Proof.
intros e W cf He HP.
destruct HP as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & Hcf & Hroute & Hne & HC & HL & HCP).
pose proof HC as (HJ & Hk & _ & Hnm & (EF & _ & _) & Hrv & _ & Hsp & _ & Hrec & _ & Hperm & _).
pose proof He as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HDn & _ & _ & _ & _ & _ & Hcalls & _).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (vr_s1_bounds e) as Hs1b.
assert (HV : 224 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hfr4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hfr4) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
pose proof (shadow_addr_bounds F ltac:(lia)) as HshF.
assert (Hnt : 0 <= vr_ntok (e_D e) <= 64).
{ unfold vr_ntok, Verbs.toks, Verbs.line_words_max. rewrite length_firstn. lia. }
assert (R21 : getr regsc (Z_to_bv 5 21) = w64 (vr_ntok (e_D e)))
  by (apply (vk_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn; tauto).
pose proof (vk_k1_le (e_R e) (e_D e)) as Hk1ev.
pose proof (vk_bsum2 B MT e q c He) as Hbs.
assert (HLV : (6 * Z.of_nat (length (r_calls (e_R e))) + 8) * (LMAX + 2) + bsum [vr_lb e q; vr_cb e c] + 17
  <= LIVE_VERBS_RECEIVE) by (rewrite Hcalls; unfold LMAX, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ; cbn [length]; lia).
subst cf. unfold cfg_at, w64.
replace (vr_pc (vr_route_pc VRR.RQuit)) with (BASE + 29636) by (unfold vr_pc, vr_route_pc, AF_verbs_receive; lia).
destruct (Nat.eq_dec (length (Verbs.toks (e_D e))) 1) as [H1 | H1].
- (* one word: g_quitting := 1, sup_resp(0), the text into a1, s9 := shadow(F), to J1 0x8d9b4 *)
  destruct (quit_step (e_R e) (e_D e) Hroute H1) as [Hvh Hk1].
  set (E := Eimg (Ereg regsc [])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply vk_env_agree).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (U677 : bv_unsigned (ew E (A_HI 277)) = 0x5e38b0).
  { subst E. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia). rewrite vhis_277. apply unsigned_lit_small. lia. }
  assert (Hwin : forall x : word, ~ (A_G_QUITTING <= bv_unsigned x < A_G_QUITTING + 4) -> ~ in_wrange E [r_gq] (bv_unsigned x)).
  { intros x Hx (r & [<-|[]] & Hr). cbn [YP09.r_base YP09.r_wlo YP09.r_whi r_gq base_val] in Hr. rewrite U677 in Hr.
    apply Hx. unfold A_G_QUITTING. lia. }
  assert (HS : st_ok_pi SEGS VAL E ss24q (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 29636)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss24q. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, r_gq.
      cbv beta iota delta [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U677. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply PRW. rewrite (AF0m.ts_prog B HB). unfold AF0m.TFIB_PROG_STATIC.
      apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. split; lia.
    - cbn. tauto.
    - split; [exact I | split; exact I]. }
  (* 0x8d8a8: li a0,1 *)
  paj_run_shc RUNP RUNC HS HJ.
  { eapply awr_ok_cons_gen with (n := A_HI 277) (b := 0x5e38b0); [reflexivity | exact U677 | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi r_gq]. intros a Ha. apply (gq_awr B PROGU HB). unfold A_G_QUITTING. split; lia. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  rename HFr into HFr1. clear HF HG.
  (* 0x8d8ac: bne s5,a0,0x8ddf0 *)
  psrr_branch_pi RUNP BR HS.
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    unfold vr_ntok in Hc. rewrite H1 in Hc. vm_compute in Hc. discriminate Hc.
  + (* 0x8d8b0: auipc a1; sw a0,944(a1); li a0,0; jal sup_resp *)
    paj_run_shc RUNP RUNC HS HJ.
    { eapply awr_ok_cons_gen with (n := A_HI 277) (b := 0x5e38b0); [reflexivity | exact U677 | | apply awr_ok_nil].
      cbn [YP09.r_wlo YP09.r_whi r_gq]. intros a Ha. apply (gq_awr B PROGU HB). unfold A_G_QUITTING. split; lia. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
    pose proof (vk_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27] HS HAE
      ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_QUITTING <= a < A_G_QUITTING + 4) ->
      rdW W (ms_mem ms0) a = rdW W memc a).
    { intros a Ha Hga. apply (aview_eq_of SEGS).
      assert (Hx : ~ (A_G_QUITTING <= bv_unsigned (Z_to_bv 64 a) < A_G_QUITTING + 4))
        by (rewrite unsigned_lit_small by lia; exact Hga).
      rewrite (HFr (Z_to_bv 64 a) (Hwin _ Hx)). exact (HFr1 (Z_to_bv 64 a) (Hwin _ Hx)). }
    assert (Hq1 : aval_mem (rdW W (ms_mem ms0)) A_G_QUITTING 4 1).
    { pose proof (st_ok_mem_ok SEGS E _ _ HS) as (_ & HRs & _).
      lazymatch type of HRs with Forall _ ?l => let l' := eval vm_compute in l in
        change l with l' in HRs end.
      apply Forall_inv in HRs. destruct HRs as (_ & _ & _ & HC0).
      cbn [YP09.r_chunks YP09.r_base base_val] in HC0. apply Forall_inv in HC0.
      intros kk Hkk. destruct (HC0 (Z.of_nat kk) ltac:(cbn; lia)) as (b & Hb1 & Hb2).
      cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1, Hb2.
      assert (U677' : bv_unsigned (ew E 677%nat) = 0x5e38b0) by exact U677. rewrite U677' in Hb2.
      unfold aview. cbn [ms_mem restrict] in Hb2.
      replace (A_G_QUITTING + Z.of_nat kk) with (0x5e38b0 + 944 + Z.of_nat kk) by (unfold A_G_QUITTING; lia).
      rewrite Hb2. cbn [option_map]. f_equal. injection Hb1 as <-.
      destruct kk as [|[|[|[|kk]]]]; [vm_compute; reflexivity .. | lia]. }
    assert (Hrv0 : vr_rv (ms_regs ms0) (vr_base B e ++ vr_rl_rt e F q (hd 0 tp) VRR.RQuit)).
    { apply (vk_rv_kept regsc _ _ Hrv). intros r v Hin. apply KR.
      unfold vr_base, vr_rl_rt in Hin. cbn [vr_rgroup app In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; cbn; tauto|]). destruct Hin. }
    clear HF HFr HFr1 HG.
    destruct (vk_same B MT RRO RPG RECC PROGU ROA e pos F q c tp [vr_lb e q; vr_cb e c] _ _ (e_R e) (e_O e) (e_q0 e) 1
      k 2 nm VR_NM_PRE lyc Sc W regsc (ms_regs ms0) memc (ms_mem ms0) mdc mdv2 HDn HC HL HCP
      (or_introl eq_refl) (or_intror (or_introl eq_refl)) HJ Hkeep Hq1 Hrv0) as (HC1 & HL1 & HCP1).
    pmkst HS.
    rewrite (SIGP CS_sup_resp ltac:(unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
    change (cmd_af CS_sup_resp) with AF_sup_resp.
    apply (vk_sup_resp B MT RRO RECC PROGU ROA MTL (TSUP_RESP fx) e pos F q c tp [vr_lb e q; vr_cb e c] _ (e_R e) (e_O e) 1
      k 2 (vr_k1 (e_R e) (e_D e)) nm VR_NM_PRE VR_NM_HD lyc Sc W (ms_regs ms0) (ms_mem ms0) mdv2 0 29660
      (fun tq => [(10, tq); (18, q); (20, F); (27, shadow_addr F + 4)]) _ He HC1 HL1 HCP1
      (or_introl eq_refl) (or_intror (or_introl eq_refl)) Q1 ltac:(lia) eq_refl Q10 ltac:(lia)).
    * lia.
    * lia.
    * unfold VERBS_RECEIVE_MALLOCS, VR_NM_PRE in *. lia.
    * unfold VR_NM_HD, VR_NM_PRE in *. lia.
    * exact HLV.
    * intros tq r v Hin. cbn [In] in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-;
        [left; split; reflexivity | right; split; [unfold acallee_saved; lia | cbn; tauto] ..].
    * intros fx' tq ly2 S2 W2 regs2 mem2 md2 Hfx Htq Hstr HC2 HL2 HCP2.
      eapply SRr_mono; [exact (s24_quit_tail (fx := fx') B MT e pos F q c tp tq k nm ly2 S2 W2 regs2 mem2 md2
        Hvh H1 Htq Hstr HC2 HL2 HCP2)|].
      intros W' cf' _ Hh. exists fx'. split; [exact Hfx|]. unfold vrF_or, vr_or, vrF_hd. left. exact Hh.
- (* two or more words: sup_resp(-902) at 0x8ddf0, to 0x8dc94 *)
  destruct (quit_rej (e_R e) (e_D e) Hroute Hne H1) as [Hvh Hk1].
  set (E := Eimg (Ereg regsc [])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply vk_env_agree).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (HS : st_ok_pi SEGS VAL E (vk_ss_ret 29636)
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 29636)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold vk_ss_ret. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  paj_run_shc RUNP RUNC HS HJ.
  { apply awr_ok_nil. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  assert (Hro1 : rs_read_only (ss_mem (vk_ss_ret 29636)) = true) by reflexivity.
  pose proof (frame_of_read_only _ _ _ _ Hro1 HF) as Hm1. clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  + (* 0x8ddf0: li a0,-902; jal sup_resp *)
    paj_run_shc RUNP RUNC HS HJ.
    { apply awr_ok_nil. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    lazymatch goal with
    | Hfx : frame_of _ ?rs (ms_mem _) (ms_mem _) |- _ =>
      assert (Hro2 : rs_read_only rs = true) by (vm_compute; reflexivity);
      pose proof (frame_of_read_only _ _ _ _ Hro2 Hfx) as Hm2
    end.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
    pose proof (vk_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27] HS HAE
      ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    assert (Q10' : getr (ms_regs ms0) 10 = w64 (-902)).
    { rewrite Q10. unfold w64. first [reflexivity | (apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity)]. }
    assert (Hmm : ms_mem ms0 = memc) by (rewrite Hm2; exact Hm1).
    rewrite Hmm in HJ.
    assert (Hrv0 : vr_rv (ms_regs ms0) (vr_base B e ++ vr_rl_rt e F q (hd 0 tp) VRR.RQuit)).
    { apply (vk_rv_kept regsc _ _ Hrv). intros r v Hin. apply KR.
      unfold vr_base, vr_rl_rt in Hin. cbn [vr_rgroup app In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; cbn; tauto|]). destruct Hin. }
    assert (HC1 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_rt e F q (hd 0 tp) VRR.RQuit)
      (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs ms0) memc mdv2)
      by (eapply (vk_regs B MT); [exact HC | exact HJ | exact Hrv0]).
    pmkst HS. rewrite Hmm.
    rewrite (SIGP CS_sup_resp ltac:(unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
    change (cmd_af CS_sup_resp) with AF_sup_resp.
    apply (vk_sup_resp B MT RRO RECC PROGU ROA MTL (TSUP_RESP fx) e pos F q c tp [vr_lb e q; vr_cb e c] _ (e_R e) (e_O e)
      (e_q0 e) k 2 (vr_k1 (e_R e) (e_D e)) nm VR_NM_PRE VR_NM_HD lyc Sc W (ms_regs ms0) memc mdv2 (-902) 30996
      (fun tq => [(10, tq); (18, q); (20, F); (22, F + 32); (27, shadow_addr F + 4)]) _ He HC1 HL HCP
      (or_introl eq_refl) (or_intror (or_introl eq_refl)) Q1 ltac:(lia) eq_refl Q10' ltac:(lia)).
    * lia.
    * lia.
    * unfold VERBS_RECEIVE_MALLOCS, VR_NM_PRE in *. lia.
    * unfold VR_NM_HD, VR_NM_PRE in *. lia.
    * exact HLV.
    * intros tq r v Hin. cbn [In] in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
        [left; split; reflexivity | right; split; [unfold acallee_saved; lia | cbn; tauto] ..].
    * intros fx' tq ly2 S2 W2 regs2 mem2 md2 Hfx Htq Hstr HC2 HL2 HCP2.
      assert (H2 : (2 <= length (Verbs.toks (e_D e)))%nat)
        by (destruct (Verbs.toks (e_D e)) as [|v0 [|v1 r1]]; [congruence | cbn in H1; lia | cbn [length]; lia]).
      eapply SRr_mono; [exact (s24_rej_tail (fx := fx') B MT e pos F q c tp tq k nm ly2 S2 W2 regs2 mem2 md2
        Hvh H2 Htq Hstr HC2 HL2 HCP2)|].
      intros W' cf' _ Hh. exists fx'. split; [exact Hfx|]. unfold vrF_or, vr_or, vrF_hd. right. exact Hh.
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    change (U E (SLit 1)) with 1 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold vr_ntok in Hc. lia.
Qed.

End e.
End f.
End d.