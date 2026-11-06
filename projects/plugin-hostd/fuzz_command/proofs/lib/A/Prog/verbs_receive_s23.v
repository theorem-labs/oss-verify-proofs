(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the segment S23 (pin_clear, 0x8dd48-0x8dd6c and 0x8ddfc-0x8de08) of the walk of
   verbs_receive on the ASan build of plugin-hostd/fuzz_command (lib/A/Prog/verbs_receive_iface.v vr_s23_stmt). *)
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

(* the symbolic states of S23: at 0x8dd48 the spill words s1+8 (shadow(F), atom 32) and s1+56 (the copy c, atom 33),
   and on the two-word path tok[1] (atom 34); at 0x8dd5c, pins_clear's return, the spill word s1+8 *)
Definition r_sp23 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 64 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 56 (CVal 8 (SOff 33 0))].
Definition r_tok23 : YP09.region := YP09.mkRegion (Some 22%nat) 8 16 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 34 0))].
Definition ss23r : sstate := mkSS 30820 sr_atoms [r_sp23] None (mkFacts [] [] []).
Definition ss23t : sstate := mkSS 30820 sr_atoms [r_sp23; r_tok23] None (mkFacts [] [] []).
Definition r_s823 : YP09.region := YP09.mkRegion (Some 9%nat) 8 16 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 32 0))].
Definition ss23p : sstate := mkSS 30840 sr_atoms [r_s823] None (mkFacts [] [] []).

(* the model: the route RPinclr; with one argument the step pins_clear, then lv2_refusals_forget(NULL) when its
   code is 0, then sup_resp(code); else reject *)
Lemma route_cp_pinclr : forall v args, VRR.route (v :: args) = VRR.RPinclr ->
  Verbs.list_eqb v Verbs.Lit.verb_chain = false /\ Verbs.list_eqb v Verbs.Lit.verb_pin_set = false.
Proof.
intros v args H. split.
- destruct (Verbs.list_eqb v Verbs.Lit.verb_chain) eqn:E; [exfalso|reflexivity].
  unfold VRR.route, VRR.route_mid in H. rewrite E in H. rt_chain H.
- destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_set) eqn:E; [exfalso|reflexivity].
  unfold VRR.route, VRR.route_mid in H. rewrite E in H. rt_chain H.
Qed.

Lemma pinclr_two : forall R D v a, Verbs.toks D = [v; a] -> VRR.route (Verbs.toks D) = VRR.RPinclr ->
  vr_h R D = (VerbsRun.pins_follow (fst (pins_clear_m R (Some a))) (snd (pins_clear_m R (Some a))), false) /\
  vr_k1 R D = 2 + (EV_PINS_CLEAR R + (if snd (pins_clear_m R (Some a)) =? 0
     then EV_LV2_REFUSALS_FORGET (fst (pins_clear_m R (Some a))) else 0) + EV_SUP_RESP).
Proof.
intros R D v a T Hr. rewrite T in Hr.
assert (St : vr_st D = Verbs.SPinClear a).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. rewrite Hr. reflexivity. }
destruct (route_cp_pinclr v [a] Hr) as [Hc1 Hc2].
split.
- unfold vr_h. rewrite St. cbn [VerbsRun.run_step]. destruct (pins_clear_m R (Some a)); reflexivity.
- unfold vr_k1. rewrite St, T. rewrite (ev_route_not_cp _ _ _ _ _ Hc1 Hc2). cbn [ev_step].
  destruct (pins_clear_m R (Some a)); reflexivity.
Qed.

Lemma pinclr_rej : forall R D, VRR.route (Verbs.toks D) = VRR.RPinclr -> Verbs.toks D <> [] ->
  length (Verbs.toks D) <> 2%nat ->
  vr_h R D = (R, resp (-902), false) /\ vr_k1 R D = 2 + EV_SUP_RESP.
Proof.
intros R D Hr Hne Hl. destruct (Verbs.toks D) as [|v args] eqn:T; [congruence|].
assert (St : vr_st D = Verbs.reject).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. rewrite Hr. cbn [VRR.plan_at].
  destruct args as [|a [|b args]]; [reflexivity | cbn in Hl; lia | reflexivity]. }
destruct (route_cp_pinclr v args Hr) as [Hc1 Hc2].
split.
- unfold vr_h. rewrite St. reflexivity.
- unfold vr_k1. rewrite St, T. rewrite (ev_route_not_cp _ _ _ _ _ Hc1 Hc2). reflexivity.
Qed.

Lemma hd_ntok_c54 : forall nt, (1 <= nt)%nat -> vr_hd_ntok 0x8dc54 nt.
Proof. intros nt H. unfold vr_hd_ntok. exact H. Qed.

Lemma mod64_zero : forall r, -2^31 <= r < 2^31 -> r mod 2^64 = 0 -> r = 0.
Proof.
intros r Hr H. destruct (Z_lt_le_dec r 0) as [Hn|Hp].
- rewrite <- (Z_mod_plus_full r 1 (2^64)) in H. rewrite Z.mod_small in H by lia. lia.
- rewrite Z.mod_small in H by lia. exact H.
Qed.

(* a register of a boundary list: kept by the run (KR) or the value the run gave it *)
Ltac s23_rv HS KR Hrv fin :=
  lazymatch goal with
  | |- getr _ ?r = w64 _ =>
    first [ rewrite KR by (cbn; tauto); apply (vk_rv_get _ _ _ _ Hrv); apply in_or_app;
            first [left; cbn; tauto | right; cbn; tauto]
          | let Hx := fresh "Hx" in prreg HS r Hx; rewrite Hx; clear Hx;
            first [fin | (rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; fin)] ]
  end.

Section dj. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fj.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section ej.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the stub's jump and the join state at 0x8dc54 after sup_resp(code) returned to 0x8de08 (statement pass 4: it runs
   at the FP state sup_resp returns at; proved in its own section, it holds at every FP state) *)
Lemma s23_join : forall e pos F q c tp tq Rx code qv k nm ly2 S2 W2 regs2 mem2 md2 Ox,
  Verbs.toks (e_D e) <> [] ->
  vr_h (e_R e) (e_D e) = (Rx, resp code, false) ->
  qv = e_q0 e -> k + EV_SUP_RESP <= vr_k1 (e_R e) (e_D e) -> nm + 1 <= VR_NM_HD -> 4096 <= tq ->
  astr_atR (rdW W2 mem2) tq (resp code) ->
  vr_core B MT e pos F ((tq, Z.of_nat (length (resp code)) + 1) :: [vr_lb e q; vr_cb e c]) vr_sh2 (vr_sl3 F q c)
    [(10, tq); (18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F);
     (27, shadow_addr F + 4)] Rx Ox qv (k + EV_SUP_RESP) (vr_k1 (e_R e) (e_D e)) (nm + 1) VR_NM_HD
    ly2 S2 W2 regs2 mem2 md2 ->
  vr_line B e q W2 mem2 -> vr_copy B e F c tp W2 mem2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 31012)) mem2 (seg_rom SEGS)) md2) (vr_athd B MT 0x8dc54 e).
Proof.
intros e pos F q c tp tq Rx code qv k nm ly2 S2 W2 regs2 mem2 md2 Ox Hne Hvh Eqv Hkk Hnn Htq Hstr HC2 HL2 HCP2.
pose proof HC2 as (HJ2 & _ & _ & _ & _ & Hrv2 & _).
apply (vk_jmp B 31012 30576 ltac:(lia) ltac:(vm_compute; reflexivity) W2 regs2 mem2 md2 _ _ _ _ _ _ _ _ _ _
  ly2 S2 _ HJ2).
intros regs3 md3 Er HJ3.
unfold vr_athd, vr_hd.
exists tq, Ox, pos, F, q, c, tp, ly2, S2, regs3, mem2, md3, (k + EV_SUP_RESP), (nm + 1).
assert (EX : vr_x (e_R e) (e_D e) = resp code) by (unfold vr_x; rewrite Hvh; reflexivity).
assert (ER1 : vr_R1 (e_R e) (e_D e) = Rx) by (unfold vr_R1; rewrite Hvh; reflexivity).
assert (EQV : vr_qv e = e_q0 e) by (unfold vr_qv, vr_quit; rewrite Hvh; reflexivity).
split; [unfold cfg_at, w64; replace (vr_pc 0x8dc54) with (BASE + 30576) by (unfold vr_pc, AF_verbs_receive; lia);
  reflexivity|].
split; [apply hd_ntok_c54; destruct (Verbs.toks (e_D e)); [congruence | cbn [length]; lia]|].
split; [lia|].
split; [rewrite EX; exact Hstr|].
rewrite EX, ER1, EQV. rewrite Eqv in HC2.
split; [|split; [exact HL2 | exact HCP2]].
eapply (vk_regs B MT); [exact HC2 | exact HJ3 |].
apply (vk_rv_kept regs2 _ _ Hrv2). intros r v _. apply Er.
Qed.

End ej.
End fj.
End dj.

Section dp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fp.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section ep.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).

(* the code after pins_clear returns, 0x8dd5c to the exit 0x8dc54 (statement pass 4: pins_clear's post is
   FP-existential, so this runs at the FP state it returns at; proved in its own section, it holds at every FP state):
   ld s9,8(s1); on code 0 lv2_refusals_forget(NULL) (not printf-reaching) and sup_resp(0), else sup_resp(code); each
   sup_resp ends at a later FP state *)
Lemma s23_after_pins : tsup_resp_spec B MT -> tlv2_refusals_forget_spec B MT -> AF0m.CmdBSyms B -> ameter_laws MT ->
  cmd_sig_prog (PI := PI) -> vr_relro_img -> vr_pg_not_ro -> vr_rec_cells B -> vr_prog_unowned B -> vr_ro_of_aro B ->
  forall e pos F q c p0 p1 a k nm R1 rcd Oc1 ly2 S2 W2 regs2 mem2 md2,
  vr_ent B MT e -> Verbs.toks (e_D e) <> [] ->
  vr_h (e_R e) (e_D e) =
    (VerbsRun.pins_follow (fst (pins_clear_m (e_R e) (Some a))) (snd (pins_clear_m (e_R e) (Some a))), false) ->
  vr_k1 (e_R e) (e_D e) = 2 + (EV_PINS_CLEAR (e_R e) + (if snd (pins_clear_m (e_R e) (Some a)) =? 0
     then EV_LV2_REFUSALS_FORGET (fst (pins_clear_m (e_R e) (Some a))) else 0) + EV_SUP_RESP) ->
  EV_PINS_CLEAR (e_R e) = 5 -> (length (r_calls (fst (pins_clear_m (e_R e) (Some a)))) <= 1)%nat ->
  k <= 2 -> nm <= VR_NM_PRE ->
  pins_clear_m (e_R e) (Some a) = (R1, rcd) -> - 2 ^ 31 <= rcd < 2 ^ 31 ->
  vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
    [(10, rcd); (18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)]
    R1 Oc1 (e_q0 e) (k + EV_PINS_CLEAR (e_R e)) (vr_k1 (e_R e) (e_D e)) (nm + 3) VR_NM_HD ly2 S2 W2 regs2 mem2 md2 ->
  vr_line B e q W2 mem2 -> vr_copy B e F c [p0; p1] W2 mem2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 30840)) mem2 (seg_rom SEGS)) md2)
    (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\ vr_athd (fx := fq) B MT 0x8dc54 e W' cf').
Proof.
intros TSUP_RESP TLV2_REFUSALS_FORGET HB MTL SIGP RRO RPG RECC PROGU ROA
  e pos F q c p0 p1 a k nm R1 rcd Oc1 ly2 S2 W2 regs2 mem2 md2 He Hne' Hvh Hk1 HEVP Hcl1 Hk Hnm Em Hrr HC2 HL2 HCP2.
pose proof HC2 as (HJ2x & _ & _ & _ & (EF & _ & _) & _).
pose proof (proj1 HJ2x) as HAR2.
pose proof HJ2x as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (vr_s1_bounds e) as Hs1b.
assert (HV : 224 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hfr4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hfr4) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
pose proof (shadow_addr_bounds F ltac:(lia)) as HshF.
clear HJ2x HAR2 Hfr4 Hfrs Hstk.
pose proof (vk_k1_le (e_R e) (e_D e)) as Hk1ev.
pose proof (vk_bsum2 B MT e q c He) as Hbs.
assert (HSR1 : EV_SUP_RESP = 1) by reflexivity.
assert (Erc : rcd = snd (pins_clear_m (e_R e) (Some a))) by (rewrite Em; reflexivity).
assert (ER1 : R1 = fst (pins_clear_m (e_R e) (Some a))) by (rewrite Em; reflexivity).
pose proof HC2 as (HJ2 & _ & _ & _ & _ & Hrv2 & _ & Hsp2 & _).
assert (R92 : getr regs2 (Z_to_bv 5 9) = w64 (vr_s1 e))
  by (apply (vk_rv_get regs2 _ _ _ Hrv2); apply in_or_app; left; cbn; tauto).
assert (R102 : getr regs2 (Z_to_bv 5 10) = w64 rcd)
  by (apply (vk_rv_get regs2 _ _ _ Hrv2); apply in_or_app; right; cbn; tauto).
assert (Hav82 : aval_mem (rdW W2 mem2) (vr_s1 e + 8) 8 (shadow_addr F)).
{ unfold vr_spill in Hsp2; rewrite Forall_forall in Hsp2.
  exact (Hsp2 (8, shadow_addr F) ltac:(unfold vr_sl3; cbn; tauto)). }
set (E2 := Eimg (Ereg regs2 [w64 (shadow_addr F)])).
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (HAE2 : env_agree 32 (Ereg regs2 [w64 (shadow_addr F)]) E2) by (subst E2; apply vk_env_agree).
assert (E92 : bv_unsigned (ew E2 9%nat) = vr_s1 e).
{ subst E2. rewrite (ew_Eimg_Ereg_nat regs2 _ 9%nat (Z_to_bv 5 9) eq_refl), R92.
  unfold w64. apply unsigned_lit_small. lia. }
assert (E322 : ew E2 32%nat = w64 (shadow_addr F)).
{ subst E2. rewrite Eimg_low by (unfold A_TEXT; lia).
  pose proof (ew_Ereg_extra regs2 [w64 (shadow_addr F)] 0%nat) as HH. cbn [Nat.add nth] in HH. exact HH. }
assert (E102 : ew E2 10%nat = w64 rcd)
  by (subst E2; rewrite (ew_Eimg_Ereg_nat regs2 _ 10%nat (Z_to_bv 5 10) eq_refl); exact R102).
assert (HS2 : st_ok_pi SEGS VAL E2 ss23p
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 30840)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss23p. apply pa_entry_st_ok_full.
  - subst E2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold r_s823, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E92. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E2 _ (vr_s1 e) 8 8%N (SOff 32 0) (shadow_addr F)).
    + cbn [sv_denot]. rewrite E322. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn. lia.
    + apply aval_val_mem. exact Hav82.
  - cbn. tauto.
  - split; [exact I | split; exact I]. }
paj_run_shc RUNP RUNC HS2 HJ2.
{ unfold ss23p; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdv3 := m) in *; clearbody mdv3 end.
assert (Hro3 : rs_read_only (ss_mem ss23p) = true) by (vm_compute; reflexivity).
lazymatch goal with
| Hfx : frame_of _ _ _ (ms_mem _) |- _ =>
  pose proof (frame_of_read_only _ _ _ _ Hro3 Hfx) as Hm3; cbn [ms_mem mkst] in Hm3
end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS2.
{ (* rc <> 0: 0x8de04 jal sup_resp(rc) *)
  assert (Hrc0 : rcd <> 0).
  { intros ->. rewrite branch_ne_U in Hc. rewrite U_SOff, E102, Z.add_0_r in Hc.
    change (U E2 (SLit 0)) with 0 in Hc. vm_compute in Hc. discriminate Hc. }
  paj_run_shc RUNP RUNC HS2 HJ2.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdv4 := m) in *; clearbody mdv4 end.
  lazymatch goal with
  | Hfx : frame_of _ ?rs (ms_mem _) (ms_mem _) |- _ =>
    assert (Hro4 : rs_read_only rs = true) by (vm_compute; reflexivity);
    pose proof (frame_of_read_only _ _ _ _ Hro4 Hfx) as Hm4
  end.
  clear HF HFr HG.
  lazymatch type of Hm4 with ms_mem ?m4 = ms_mem ?m3 =>
    assert (Hmm2 : ms_mem m4 = mem2) by (rewrite Hm4; exact Hm3) end.
  rewrite Hmm2 in HJ2.
  prreg HS2 (1%bv : bv 5) Q1b. prreg HS2 (10%bv : bv 5) Q10b.
  pose proof (vk_kept_regs E2 _ _ regs2 [w64 (shadow_addr F)] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 27] HS2 HAE2
    ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
  set (rl2 := [(18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F);
    (27, shadow_addr F + 4)]).
  lazymatch type of Q1b with getr (ms_regs ?m4) _ = _ => rename m4 into ms4 end.
  assert (Hrv4 : vr_rv (ms_regs ms4) (vr_base B e ++ rl2)).
  { unfold vr_rv, vr_base, rl2. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    s23_rv HS2 KR2 Hrv2 ltac:(first [exact E322 | exact E102]). }
  assert (Q10b' : getr (ms_regs ms4) 10 = w64 rcd) by (rewrite Q10b; first [exact E102 | (rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E102)]).
  assert (HC4 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl2
    R1 Oc1 (e_q0 e) (k + EV_PINS_CLEAR (e_R e)) (vr_k1 (e_R e) (e_D e)) (nm + 3) VR_NM_HD ly2 S2 W2 (ms_regs ms4) mem2 mdv4)
    by (eapply (vk_regs B MT); [exact HC2 | exact HJ2 | exact Hrv4]).
  pmkst HS2. rewrite Hmm2.
  rewrite (SIGP CS_sup_resp ltac:(unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
  change (cmd_af CS_sup_resp) with AF_sup_resp.
  assert (Hrcb : (rcd =? 0) = false) by (apply Z.eqb_neq; exact Hrc0).
  assert (Hvh' : vr_h (e_R e) (e_D e) = (R1, resp rcd, false)).
  { rewrite Hvh. unfold VerbsRun.pins_follow. rewrite <- Erc, <- ER1, Hrcb. reflexivity. }
  assert (Hk1' : vr_k1 (e_R e) (e_D e) = 2 + (EV_PINS_CLEAR (e_R e) + EV_SUP_RESP)).
  { rewrite Hk1, <- Erc, Hrcb. cbv iota. lia. }
  apply (vk_sup_resp B MT RRO RECC PROGU ROA MTL TSUP_RESP e pos F q c [p0; p1] [vr_lb e q; vr_cb e c] rl2 R1 Oc1
    (e_q0 e) (k + EV_PINS_CLEAR (e_R e)) (vr_k1 (e_R e) (e_D e)) (vr_k1 (e_R e) (e_D e)) (nm + 3) VR_NM_HD VR_NM_HD
    ly2 S2 W2 (ms_regs ms4) mem2 mdv4 rcd 31012
    (fun tq => [(10, tq); (18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F);
      (27, shadow_addr F + 4)]) _ He HC4 HL2 HCP2 (or_introl eq_refl) (or_intror (or_introl eq_refl)) Q1b ltac:(lia)
    eq_refl Q10b' Hrr).
  - lia.
  - lia.
  - unfold VERBS_RECEIVE_MALLOCS, VR_NM_PRE in *. lia.
  - unfold VR_NM_HD, VR_NM_PRE in *. lia.
  - rewrite ER1. unfold LMAX, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ. lia.
  - intros tq r0 v0 Hin. cbn [In] in Hin.
    destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]]; injection E1 as <- <-;
      [left; split; reflexivity | right; split; [unfold acallee_saved; lia | unfold rl2; cbn; tauto] ..].
  - intros fx2 tq ly3 S3 W3 regs3 mem3 md3 Hfx2 Htq Hstr HC3 HL3 HCP3.
    eapply SRr_mono; [exact (s23_join (fx := fx2) B MT e pos F q c [p0; p1] tq R1 rcd (e_q0 e) (k + EV_PINS_CLEAR (e_R e))
      (nm + 3) ly3 S3 W3 regs3 mem3 md3 _ Hne' Hvh' eq_refl ltac:(lia) ltac:(unfold VR_NM_HD, VR_NM_PRE in *; lia)
      Htq Hstr HC3 HL3 HCP3)|].
    intros W' cf' _ Hh. exists fx2. split; [exact Hfx2 | exact Hh]. }
{ (* rc = 0: 0x8dd64 jal lv2_refusals_forget(NULL) *)
  assert (Hrc0 : rcd = 0).
  { rewrite branch_ne_U in Hc. rewrite U_SOff, E102, Z.add_0_r in Hc.
    change (U E2 (SLit 0)) with 0 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    unfold w64 in Hc. rewrite Z_to_bv_unsigned in Hc. unfold zcanon, M64, bv_wrap in Hc.
    change (bv_modulus 64) with (2 ^ 64) in Hc. rewrite Zmod_mod in Hc. exact (mod64_zero rcd Hrr Hc). }
  rewrite Hrc0 in *.
  paj_run_shc RUNP RUNC HS2 HJ2.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdv4 := m) in *; clearbody mdv4 end.
  lazymatch goal with
  | Hfx : frame_of _ ?rs (ms_mem _) (ms_mem _) |- _ =>
    assert (Hro4 : rs_read_only rs = true) by (vm_compute; reflexivity);
    pose proof (frame_of_read_only _ _ _ _ Hro4 Hfx) as Hm4
  end.
  clear HF HFr HG.
  lazymatch type of Hm4 with ms_mem ?m4 = ms_mem ?m3 =>
    assert (Hmm2 : ms_mem m4 = mem2) by (rewrite Hm4; exact Hm3) end.
  rewrite Hmm2 in HJ2.
  prreg HS2 (1%bv : bv 5) Q1b. prreg HS2 (10%bv : bv 5) Q10b.
  pose proof (vk_kept_regs E2 _ _ regs2 [w64 (shadow_addr F)] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 27] HS2 HAE2
    ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
  set (rl2 := [(18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F);
    (27, shadow_addr F + 4)]).
  lazymatch type of Q1b with getr (ms_regs ?m4) _ = _ => rename m4 into ms4 end.
  assert (Hrv4 : vr_rv (ms_regs ms4) (vr_base B e ++ rl2)).
  { unfold vr_rv, vr_base, rl2. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    s23_rv HS2 KR2 Hrv2 ltac:(first [exact E322 | exact E102]). }
  assert (Q10b' : getr (ms_regs ms4) 10 = w64 0)
    by (rewrite Q10b; first [exact E102 | reflexivity | (rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E102)]).
  assert (HC4 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl2
    R1 Oc1 (e_q0 e) (k + EV_PINS_CLEAR (e_R e)) (vr_k1 (e_R e) (e_D e)) (nm + 3) VR_NM_HD ly2 S2 W2 (ms_regs ms4) mem2 mdv4)
    by (eapply (vk_regs B MT); [exact HC2 | exact HJ2 | exact Hrv4]).
  pmkst HS2. rewrite Hmm2.
  rewrite (SIGP CS_lv2_refusals_forget ltac:(unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
  change (cmd_af CS_lv2_refusals_forget) with AF_lv2_refusals_forget.
  assert (Hrcb : (0 =? 0) = true) by reflexivity.
  assert (Hvh' : vr_h (e_R e) (e_D e) = (lv2_refusals_forget_m R1 None, resp 0, false)).
  { rewrite Hvh. unfold VerbsRun.pins_follow. rewrite <- Erc, <- ER1. reflexivity. }
  assert (Hk1' : vr_k1 (e_R e) (e_D e) = 2 + (EV_PINS_CLEAR (e_R e) + EV_LV2_REFUSALS_FORGET R1 + EV_SUP_RESP)).
  { rewrite Hk1, <- Erc, <- ER1. reflexivity. }
  assert (Hsf1 : rec_spill_frees R1 = 0).
  { unfold rec_spill_frees. rewrite ER1. destruct (Nat.ltb_spec (length (r_calls (fst (pins_clear_m (e_R e) (Some a))))) 16); [reflexivity | lia]. }
  assert (HEVL : EV_LV2_REFUSALS_FORGET R1 = 1) by (unfold EV_LV2_REFUSALS_FORGET, EV_XSTRDUP; rewrite Hsf1; reflexivity).
  apply (vk_lv2 B MT RRO RPG RECC PROGU ROA MTL HB TLV2_REFUSALS_FORGET e pos F q c [p0; p1] [vr_lb e q; vr_cb e c] rl2 rl2
    R1 Oc1 (e_q0 e) (k + EV_PINS_CLEAR (e_R e)) (vr_k1 (e_R e) (e_D e)) (vr_k1 (e_R e) (e_D e)) (nm + 3) VR_NM_HD
    VR_NM_HD ly2 S2 W2 (ms_regs ms4) mem2 mdv4 30852 _ He HC4 HL2 HCP2 (or_introl eq_refl) (or_intror (or_introl eq_refl))
    Q1b ltac:(lia) eq_refl Q10b').
  - rewrite HEVL. rewrite Hk1' in Hk1ev. unfold EV_SUP_RESP, EV_XSTRDUP in *. lia.
  - rewrite HEVL, Hk1'. unfold EV_SUP_RESP, EV_XSTRDUP in *. lia.
  - unfold VERBS_RECEIVE_MALLOCS, VR_NM_PRE in *. lia.
  - unfold VR_NM_HD, VR_NM_PRE in *. lia.
  - rewrite ER1. unfold LMAX, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ. lia.
  - intros r0 v0 Hin. split; [|exact Hin]. unfold rl2 in Hin. cbn [In] in Hin.
    destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]; injection E1 as <- _; unfold acallee_saved; lia.
  - (* after lv2: 0x8dd68 li a0,0; j 0x8de04; jal sup_resp(0) *)
    intros Oc5 ly5 S5 W5 regs5 mem5 md5 HC5 HL5 HCP5.
    pose proof HC5 as (HJ5 & _ & _ & _ & _ & Hrv5 & _).
    set (E5 := Eimg (Ereg regs5 [])).
    assert (HEI5 : img_env VAL A_LIM E5) by (subst E5; apply Eimg_env).
    assert (HAE5 : env_agree 32 (Ereg regs5 []) E5) by (subst E5; apply vk_env_agree).
    assert (HS5 : st_ok_pi SEGS VAL E5 (vk_ss_ret 30852)
      (restrict (w_H W5) (mkst regs5 (Z_to_bv 64 (BASE + 30852)) mem5 (seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. unfold vk_ss_ret. apply pa_entry_st_ok_full.
      - subst E5. apply regs_ok_Eimg_Ereg.
      - reflexivity.
      - constructor.
      - exact I.
      - split; [exact I | split; exact I]. }
    paj_run_shc RUNP RUNC HS5 HJ5.
    { apply awr_ok_nil. }
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdv6 := m) in *; clearbody mdv6 end.
    lazymatch goal with
    | Hfx : frame_of _ ?rs _ (ms_mem ?m6) |- _ =>
      assert (Hro6 : rs_read_only rs = true) by (vm_compute; reflexivity);
      pose proof (frame_of_read_only _ _ _ _ Hro6 Hfx) as Hm6; cbn [ms_mem mkst] in Hm6
    end.
    clear HF HFr HG.
    rewrite Hm6 in HJ5.
    prreg HS5 (1%bv : bv 5) Q1c. prreg HS5 (10%bv : bv 5) Q10c.
    pose proof (vk_kept_regs E5 _ _ regs5 [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 27] HS5 HAE5
      ltac:(vm_compute; reflexivity)) as KR5. cbn [ms_regs restrict] in KR5.
    lazymatch type of Q1c with getr (ms_regs ?m6) _ = _ => rename m6 into ms6 end.
    assert (Hrv6 : vr_rv (ms_regs ms6) (vr_base B e ++ rl2)).
    { apply (vk_rv_kept regs5 _ _ Hrv5). intros r0 v0 Hin. apply KR5.
      unfold vr_base, rl2 in Hin. cbn [app In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; cbn; tauto|]). destruct Hin. }
    assert (HC6 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl2
      (lv2_refusals_forget_m R1 None) Oc5 (e_q0 e) (k + EV_PINS_CLEAR (e_R e) + EV_LV2_REFUSALS_FORGET R1)
      (vr_k1 (e_R e) (e_D e)) (nm + 3 + 1) VR_NM_HD ly5 S5 W5 (ms_regs ms6) mem5 mdv6)
      by (eapply (vk_regs B MT); [exact HC5 | exact HJ5 | exact Hrv6]).
    pmkst HS5. rewrite Hm6.
    rewrite (SIGP CS_sup_resp ltac:(unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
    change (cmd_af CS_sup_resp) with AF_sup_resp.
    assert (Hcl2 : (length (r_calls (lv2_refusals_forget_m R1 None)) <= 2)%nat)
      by (pose proof (calls_lv2 R1 None); rewrite ER1 in *; lia).
    apply (vk_sup_resp B MT RRO RECC PROGU ROA MTL TSUP_RESP e pos F q c [p0; p1] [vr_lb e q; vr_cb e c] rl2
      (lv2_refusals_forget_m R1 None) Oc5 (e_q0 e) (k + EV_PINS_CLEAR (e_R e) + EV_LV2_REFUSALS_FORGET R1)
      (vr_k1 (e_R e) (e_D e)) (vr_k1 (e_R e) (e_D e)) (nm + 3 + 1) VR_NM_HD VR_NM_HD
      ly5 S5 W5 (ms_regs ms6) mem5 mdv6 0 31012
      (fun tq => [(10, tq); (18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F);
        (27, shadow_addr F + 4)]) _ He HC6 HL5 HCP5 (or_introl eq_refl) (or_intror (or_introl eq_refl)) Q1c ltac:(lia)
      eq_refl Q10c ltac:(lia)).
    + rewrite Hk1' in Hk1ev. lia.
    + rewrite Hk1'. lia.
    + unfold VERBS_RECEIVE_MALLOCS, VR_NM_PRE in *. lia.
    + unfold VR_NM_HD, VR_NM_PRE in *. lia.
    + unfold LMAX, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ. lia.
    + intros tq r0 v0 Hin. cbn [In] in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]]; injection E1 as <- <-;
        [left; split; reflexivity | right; split; [unfold acallee_saved; lia | unfold rl2; cbn; tauto] ..].
    + intros fx2 tq ly7 S7 W7 regs7 mem7 md7 Hfx2 Htq Hstr HC7 HL7 HCP7.
      eapply SRr_mono; [exact (s23_join (fx := fx2) B MT e pos F q c [p0; p1] tq (lv2_refusals_forget_m R1 None) 0 (e_q0 e)
        (k + EV_PINS_CLEAR (e_R e) + EV_LV2_REFUSALS_FORGET R1) (nm + 3 + 1) ly7 S7 W7 regs7 mem7 md7 _ Hne' Hvh'
        eq_refl ltac:(rewrite Hk1'; lia) ltac:(unfold VR_NM_HD, VR_NM_PRE in *; lia) Htq Hstr HC7 HL7 HCP7)|].
      intros W' cf' _ Hh. exists fx2. split; [exact Hfx2 | exact Hh]. }
Qed.

End ep.
End fp.
End dp.

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
(* the callees' contracts (verbs_receive_c.v:196, 199, 219) and the named record facts *)
Hypothesis TLV2_REFUSALS_FORGET : forall fx0 : YK11.FPState, @tlv2_refusals_forget_spec fx0 rc SK PI B MT.
Hypothesis TPINS_CLEAR : forall fx0 : YK11.FPState, @tpins_clear_spec fx0 rc SK PI B MT.
Hypothesis TSUP_RESP : forall fx0 : YK11.FPState, @tsup_resp_spec fx0 rc SK PI B MT.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).

Lemma vr_s23 : vr_s23_stmt B MT.
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
assert (R9 : getr regsc (Z_to_bv 5 9) = w64 (vr_s1 e))
  by (apply (vk_rv_get regsc _ _ _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R21 : getr regsc (Z_to_bv 5 21) = w64 (vr_ntok (e_D e)))
  by (apply (vk_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn; tauto).
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 (F + 32))
  by (apply (vk_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn; tauto).
assert (Hav8 : aval_mem (rdW W memc) (vr_s1 e + 8) 8 (shadow_addr F)).
{ unfold vr_spill in Hsp; rewrite Forall_forall in Hsp. exact (Hsp (8, shadow_addr F) ltac:(unfold vr_sl3; cbn; tauto)). }
assert (Hav56 : aval_mem (rdW W memc) (vr_s1 e + 56) 8 c).
{ unfold vr_spill in Hsp; rewrite Forall_forall in Hsp. exact (Hsp (56, c) ltac:(unfold vr_sl3; cbn; tauto)). }
pose proof (vk_k1_le (e_R e) (e_D e)) as Hk1ev.
pose proof (vk_bsum2 B MT e q c He) as Hbs.
pose proof HCP as (_ & (_ & Htkl & _ & _)).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. right; left; reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4096 & Hcc & _).
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrsc.
subst cf. unfold cfg_at, w64.
replace (vr_pc (vr_route_pc VRR.RPinclr)) with (BASE + 30820) by (unfold vr_pc, vr_route_pc, AF_verbs_receive; lia).
destruct (Nat.eq_dec (length (Verbs.toks (e_D e))) 2) as [H2 | H2].
- (* two words: pins_clear(tok[1]) *)
  destruct (Verbs.toks (e_D e)) as [|v [|a [|b rest]]] eqn:T; try (cbn in H2; lia).
  destruct (pinclr_two (e_R e) (e_D e) v a T ltac:(rewrite T; exact Hroute)) as [Hvh Hk1].
  assert (Hne' : Verbs.toks (e_D e) <> []) by (rewrite T; discriminate).
  assert (HlenP : length tp = 2%nat) by (rewrite Htkl; reflexivity).
  destruct tp as [|p0 [|p1 [|p2 tp']]]; cbn in HlenP; try lia.
  destruct (vk_tok_arg B e F c [p0; p1] lyc Sc W memc mdc (e_O e) [vr_lb e q; vr_cb e c] 1 p1 a HAR Hperm
    (or_intror (or_introl eq_refl)) HCP eq_refl ltac:(rewrite T; reflexivity))
    as (Hblk & Hap & Hstra & Hlena & Hp1m & Hp14 & Hp1c).
  set (E := Eimg (Ereg regsc [w64 (shadow_addr F); w64 c; w64 p1])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc [w64 (shadow_addr F); w64 c; w64 p1]) E) by (subst E; apply vk_env_agree).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (E9 : bv_unsigned (ew E 9%nat) = vr_s1 e).
  { subst E. rewrite (ew_Eimg_Ereg_nat regsc _ 9%nat (Z_to_bv 5 9) eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
  assert (E22 : bv_unsigned (ew E 22%nat) = F + 32).
  { subst E. rewrite (ew_Eimg_Ereg_nat regsc _ 22%nat (Z_to_bv 5 22) eq_refl), R22. unfold w64. apply unsigned_lit_small. lia. }
  assert (E32 : ew E 32%nat = w64 (shadow_addr F)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    pose proof (ew_Ereg_extra regsc [w64 (shadow_addr F); w64 c; w64 p1] 0%nat) as HH. cbn [Nat.add nth] in HH. exact HH. }
  assert (E33 : ew E 33%nat = w64 c).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    pose proof (ew_Ereg_extra regsc [w64 (shadow_addr F); w64 c; w64 p1] 1%nat) as HH. cbn [Nat.add nth] in HH. exact HH. }
  assert (E34 : ew E 34%nat = w64 p1).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    pose proof (ew_Ereg_extra regsc [w64 (shadow_addr F); w64 c; w64 p1] 2%nat) as HH. cbn [Nat.add nth] in HH. exact HH. }
  assert (HS : st_ok_pi SEGS VAL E ss23t (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 30820)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss23t. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor]].
      + unfold r_sp23, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor]].
        * apply (chunk_ok_val SEGS E _ (vr_s1 e) 8 8%N (SOff 32 0) (shadow_addr F)).
          -- cbn [sv_denot]. rewrite E32. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
          -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
          -- cbn. lia.
          -- apply aval_val_mem. exact Hav8.
        * apply (chunk_ok_val SEGS E _ (vr_s1 e) 56 8%N (SOff 33 0) c).
          -- cbn [sv_denot]. rewrite E33. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
          -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
          -- cbn. lia.
          -- apply aval_val_mem. exact Hav56.
      + unfold r_tok23, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (F + 32) 8 8%N (SOff 34 0) p1).
        -- cbn [sv_denot]. rewrite E34. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn. lia.
        -- apply aval_val_mem. replace (F + 32 + 8) with (F + 32 + 8 * Z.of_nat 1) by lia. exact Hp1m.
    - cbn [pairwise_disjoint all_disjoint]. split; [|split; exact I]. split; [|exact I].
      unfold extent_disjoint, r_sp23, r_tok23. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E22. right. lia.
    - split; [exact I | split; exact I]. }
  (* 0x8dd48: li a0,2; ld s3,56(s1) *)
  paj_run_shc RUNP RUNC HS HJ.
  { unfold ss23t; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  assert (Hro1 : rs_read_only (ss_mem ss23t) = true) by (vm_compute; reflexivity).
  pose proof (frame_of_read_only _ _ _ _ Hro1 HF) as Hm1. clear HF HFr HG.
  (* 0x8dd50: bne s5,a0,0x8ddfc *)
  psrr_branch_pi RUNP BR HS.
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    unfold vr_ntok in Hc. rewrite T in Hc. vm_compute in Hc. discriminate Hc.
  + (* 0x8dd54: ld a0,8(s6); jal pins_clear *)
    clear Hc.
    paj_run_shc RUNP RUNC HS HJ.
    { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
        let rs' := eval vm_compute in rs in change rs with rs' end.
      apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    lazymatch goal with
    | Hfx : frame_of _ ?rs (ms_mem _) (ms_mem _) |- _ =>
      assert (Hro2 : rs_read_only rs = true) by (vm_compute; reflexivity);
      pose proof (frame_of_read_only _ _ _ _ Hro2 Hfx) as Hm2
    end.
    clear HF HFr HG.
    assert (Hmm : ms_mem ms0 = memc) by (rewrite Hm2; exact Hm1).
    rewrite Hmm in HJ.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
    pose proof (vk_kept_regs E _ _ regsc [w64 (shadow_addr F); w64 c; w64 p1]
      [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    assert (Q10' : getr (ms_regs ms0) 10 = w64 p1) by (rewrite Q10; first [exact E34 | (rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E34)]).
    set (rl1 := [(18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)]).
    assert (Hrv1 : vr_rv (ms_regs ms0) (vr_base B e ++ rl1)).
    { unfold vr_rv, vr_base, rl1. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      s23_rv HS KR Hrv ltac:(first [exact E33 | exact E32 | exact E34]). }
    assert (HC1 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl1
      (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs ms0) memc mdv2)
      by (eapply (vk_regs B MT); [exact HC | exact HJ | exact Hrv1]).
    pmkst HS. rewrite Hmm.
    rewrite (SIGP CS_pins_clear ltac:(unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
    change (cmd_af CS_pins_clear) with AF_pins_clear.
    assert (Hsf0 : rec_spill_frees (e_R e) = 0) by (unfold rec_spill_frees; rewrite Hcalls; reflexivity).
    assert (HEVP : EV_PINS_CLEAR (e_R e) = 5)
      by (unfold EV_PINS_CLEAR, EV_ANSWER_CODE, EV_HAND_BACK, EV_XSTRDUP; rewrite Hsf0; reflexivity).
    pose proof (vk_code_range B lyc Sc _ (e_R e) (e_O e) Hrec) as Hcode0.
    assert (Hrcr : - 2 ^ 31 <= snd (pins_clear_m (e_R e) (Some a)) < 2 ^ 31)
      by (destruct (code_pins_clear (e_R e) (Some a)) as [-> | ->]; lia).
    pose proof (resp_length _ Hrcr) as Hrl0.
    assert (HL2pos : 0 <= (if snd (pins_clear_m (e_R e) (Some a)) =? 0
      then EV_LV2_REFUSALS_FORGET (fst (pins_clear_m (e_R e) (Some a))) else 0)).
    { destruct (_ =? 0); [|lia]. unfold EV_LV2_REFUSALS_FORGET, EV_XSTRDUP.
      pose proof (vk_rsf_nonneg (fst (pins_clear_m (e_R e) (Some a)))). lia. }
    assert (HSR1 : EV_SUP_RESP = 1) by reflexivity.
    assert (Hcl1 : (length (r_calls (fst (pins_clear_m (e_R e) (Some a)))) <= 1)%nat)
      by (pose proof (calls_pins_clear (e_R e) (Some a)) as HH; rewrite Hcalls in HH; exact HH).
    apply (vk_pins_clear B MT RRO RPG RECC PROGU ROA MTL HB (TPINS_CLEAR fx) e pos F q c [p0; p1] [vr_lb e q; vr_cb e c] rl1
      (e_R e) (e_O e) (e_q0 e) k 2 (vr_k1 (e_R e) (e_D e)) nm VR_NM_PRE VR_NM_HD lyc Sc W (ms_regs ms0) memc mdv2
      p1 a 30840 (fun t => [(10, t); (18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32);
        (27, shadow_addr F + 4)]) _ He HC1 HL HCP (or_introl eq_refl) (or_intror (or_introl eq_refl)) Q1 ltac:(lia)
      eq_refl Q10' ltac:(lia) Hblk Hap Hstra Hlena Hsf0).
    * rewrite Hk1 in Hk1ev. lia.
    * rewrite Hk1. lia.
    * unfold VERBS_RECEIVE_MALLOCS, VR_NM_PRE in *. lia.
    * unfold VR_NM_HD, VR_NM_PRE in *. lia.
    * rewrite Hcalls. unfold LIVE_PINS_CLEAR, LIVE_XSTRDUP, LIVE_ANSWER_CODE, LIVE_HAND_BACK, LIVE_XSTRDUP. cbn [sarg length].
      unfold LMAX, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in *. lia.
    * intros t r0 v0 Hin. cbn [In] in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]; injection E1 as <- <-;
        [left; split; reflexivity | right; split; [unfold acallee_saved; lia | unfold rl1; cbn; tauto] ..].
    * (* after pins_clear: 0x8dd5c, at the FP state fx' pins_clear returns at *)
      intros fx' R1 rcd Oc1 ly2 S2 W2 regs2 mem2 md2 Hfx Em Hrr HC2 HL2 HCP2.
      eapply SRr_mono; [exact (s23_after_pins (fx := fx') B MT (TSUP_RESP fx') (TLV2_REFUSALS_FORGET fx') HB MTL SIGP
        RRO RPG RECC PROGU ROA e pos F q c p0 p1 a k nm R1 rcd Oc1 ly2 S2 W2 regs2 mem2 md2 (vk_ent_fx B MT fx fx' e He Hfx)
        Hne' Hvh Hk1 HEVP Hcl1 Hk Hnm Em Hrr HC2 HL2 HCP2)|].
      intros W' cf' _ (fq & Hfq & Hh). exists fq. split; [exact (fxrel_trans _ _ _ Hfx Hfq) | exact Hh].
- (* not two words: 0x8ddfc li a0,-902; ld s9,8(s1); jal sup_resp(-902) *)
  destruct (pinclr_rej (e_R e) (e_D e) Hroute Hne H2) as [Hvh Hk1].
  set (E := Eimg (Ereg regsc [w64 (shadow_addr F); w64 c])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc [w64 (shadow_addr F); w64 c]) E) by (subst E; apply vk_env_agree).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (E9 : bv_unsigned (ew E 9%nat) = vr_s1 e).
  { subst E. rewrite (ew_Eimg_Ereg_nat regsc _ 9%nat (Z_to_bv 5 9) eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
  assert (E32 : ew E 32%nat = w64 (shadow_addr F)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    pose proof (ew_Ereg_extra regsc [w64 (shadow_addr F); w64 c] 0%nat) as HH. cbn [Nat.add nth] in HH. exact HH. }
  assert (E33 : ew E 33%nat = w64 c).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    pose proof (ew_Ereg_extra regsc [w64 (shadow_addr F); w64 c] 1%nat) as HH. cbn [Nat.add nth] in HH. exact HH. }
  assert (HS : st_ok_pi SEGS VAL E ss23r (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 30820)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss23r. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor].
      unfold r_sp23, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      + apply (chunk_ok_val SEGS E _ (vr_s1 e) 8 8%N (SOff 32 0) (shadow_addr F)).
        * cbn [sv_denot]. rewrite E32. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        * cbn. lia.
        * apply aval_val_mem. exact Hav8.
      + apply (chunk_ok_val SEGS E _ (vr_s1 e) 56 8%N (SOff 33 0) c).
        * cbn [sv_denot]. rewrite E33. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        * cbn. lia.
        * apply aval_val_mem. exact Hav56.
    - cbn. tauto.
    - split; [exact I | split; exact I]. }
  paj_run_shc RUNP RUNC HS HJ.
  { unfold ss23r; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  assert (Hro1 : rs_read_only (ss_mem ss23r) = true) by (vm_compute; reflexivity).
  pose proof (frame_of_read_only _ _ _ _ Hro1 HF) as Hm1. clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  + paj_run_shc RUNP RUNC HS HJ.
    { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
        let rs' := eval vm_compute in rs in change rs with rs' end.
      apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    lazymatch goal with
    | Hfx : frame_of _ ?rs (ms_mem _) (ms_mem _) |- _ =>
      assert (Hro2 : rs_read_only rs = true) by (vm_compute; reflexivity);
      pose proof (frame_of_read_only _ _ _ _ Hro2 Hfx) as Hm2
    end.
    clear HF HFr HG.
    assert (Hmm : ms_mem ms0 = memc) by (rewrite Hm2; exact Hm1).
    rewrite Hmm in HJ.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
    pose proof (vk_kept_regs E _ _ regsc [w64 (shadow_addr F); w64 c] [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] HS HAE
      ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    assert (Q10' : getr (ms_regs ms0) 10 = w64 (-902)).
    { rewrite Q10. unfold w64. first [reflexivity | (apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity)]. }
    set (rl1 := [(18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F);
      (27, shadow_addr F + 4)]).
    assert (Hrv1 : vr_rv (ms_regs ms0) (vr_base B e ++ rl1)).
    { unfold vr_rv, vr_base, rl1. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      s23_rv HS KR Hrv ltac:(first [exact E33 | exact E32]). }
    assert (HC1 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl1
      (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs ms0) memc mdv2)
      by (eapply (vk_regs B MT); [exact HC | exact HJ | exact Hrv1]).
    pmkst HS. rewrite Hmm.
    rewrite (SIGP CS_sup_resp ltac:(unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
    change (cmd_af CS_sup_resp) with AF_sup_resp.
    apply (vk_sup_resp B MT RRO RECC PROGU ROA MTL (TSUP_RESP fx) e pos F q c tp [vr_lb e q; vr_cb e c] rl1 (e_R e) (e_O e)
      (e_q0 e) k 2 (vr_k1 (e_R e) (e_D e)) nm VR_NM_PRE VR_NM_HD lyc Sc W (ms_regs ms0) memc mdv2 (-902) 31012
      (fun tq => [(10, tq); (18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F);
        (27, shadow_addr F + 4)]) _ He HC1 HL HCP (or_introl eq_refl) (or_intror (or_introl eq_refl)) Q1 ltac:(lia)
      eq_refl Q10' ltac:(lia)).
    * lia.
    * lia.
    * unfold VERBS_RECEIVE_MALLOCS, VR_NM_PRE in *. lia.
    * unfold VR_NM_HD, VR_NM_PRE in *. lia.
    * rewrite Hcalls. unfold LMAX, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ. cbn [length]. lia.
    * intros tq r0 v0 Hin. cbn [In] in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]]; injection E1 as <- <-;
        [left; split; reflexivity | right; split; [unfold acallee_saved; lia | unfold rl1; cbn; tauto] ..].
    * intros fx' tq ly2 S2 W2 regs2 mem2 md2 Hfx Htq Hstr HC2 HL2 HCP2.
      eapply SRr_mono; [exact (s23_join (fx := fx') B MT e pos F q c tp tq (e_R e) (-902) (e_q0 e) k nm ly2 S2 W2 regs2
        mem2 md2 _ Hne Hvh eq_refl ltac:(lia) ltac:(unfold VR_NM_HD, VR_NM_PRE in *; lia) Htq Hstr HC2 HL2 HCP2)|].
      intros W' cf' _ Hh. exists fx'. split; [exact Hfx | exact Hh].
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    change (U E (SLit 2)) with 2 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold vr_ntok in Hc. lia.
Qed.

End e.
End f.
End d.