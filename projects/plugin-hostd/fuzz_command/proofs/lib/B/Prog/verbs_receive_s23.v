(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the segment S23 (pin_clear, 0x8d7b4-0x8d7dc) of the walk of verbs_receive on
   the ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v vr_s23_stmt). The structure
   is the A walk's (lib/A/Prog/verbs_receive_s23.v); the runs are B's instructions (gen/dis/verbs_receive.s):
     0x8d7b4 li a0,2; bne s5,a0,0x8d884         -- not two words: the refusal stub 0x8d884 (code -902)
     0x8d7bc li a0,-9; ld s3,40(s1)             -- s3 = tok = F + 32 (the spill slot s1+40)
     0x8d7c4 bltu a0,s3,0x8d938                 -- UBSan trap (tok + 8 wraps): refuted, F + 32 < 2^64 - 9
     0x8d7c8 ld a0,8(s3); jal pins_clear        -- pins_clear(tok[1]) (post apost_baseF)
     0x8d7d0 bnez a0,0x8d88c                    -- code <> 0: the stub 0x8d88c with that code
     0x8d7d4 jal lv2_refusals_forget            -- a0 = 0 = NULL (post apost_base)
     0x8d7d8 li a0,0; j 0x8d88c                 -- the stub 0x8d88c with code 0
   B's S23 stops at the stubs (sup_resp is S29's, at 0x8d88c), where A's went through sup_resp to a join. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c arg_s_c record_c hand_back_c answer_code_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pins_clear_c lv2_refusals_forget_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_live.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s30_m verbs_receive_s30_kit verbs_receive_s23_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the symbolic state of the two-word path at 0x8d7b4 (B listing offset 29316): the spill word s1+40 (tok = F + 32,
   atom 32) and tok[1] (atom 33), in a region based at atom 32 (B reloads tok from the frame, where A kept it in s6) *)
Definition r_sp23 : YP09.region := YP09.mkRegion (Some 9%nat) 40 48 40 40 [YP09.mkChunk 40 (CVal 8 (SOff 32 0))].
Definition r_tok23 : YP09.region := YP09.mkRegion (Some 32%nat) 8 16 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition ss23t : sstate := mkSS 29316 sr_atoms [r_sp23; r_tok23] None (mkFacts [] [] []).

Lemma mod64_zero : forall r, -2^31 <= r < 2^31 -> r mod 2^64 = 0 -> r = 0.
Proof.
intros r Hr H. destruct (Z_lt_le_dec r 0) as [Hn|Hp].
- rewrite <- (Z_mod_plus_full r 1 (2^64)) in H. rewrite Z.mod_small in H by lia. lia.
- rewrite Z.mod_small in H by lia. exact H.
Qed.

(* a symbolic run that stores nothing leaves the memory as it was *)
Ltac vk23_mem HF Hm :=
  lazymatch type of HF with
  | frame_of _ ?rs _ _ =>
    let Hro := fresh "Hro" in
    assert (Hro : rs_read_only rs = true) by (vm_compute; reflexivity);
    pose proof (frame_of_read_only _ _ _ _ Hro HF) as Hm; clear Hro; cbn [ms_mem mkst] in Hm
  end.
(* the state after a run: name it, and abstract its model (TRAP: the model term doubles per run) *)
Ltac vk23_post ms md :=
  lazymatch goal with |- SRr _ _ (mkCfg ?m ?d) _ => rename m into ms; set (md := d) in *; clearbody md end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the registers the stubs name besides vr_base: 0x8d88c adds a0 = the code and s3 = tok to the common list *)
Definition vk_prb (e : vrE) (F q c : Z) : list (Z * Z) := tl (tl (vr_rl_pr e F q c 0x8d88c 0)).
Lemma vk_rl_pr_88c : forall e F q c code, vr_rl_pr e F q c 0x8d88c code = (10, code) :: (19, F + 32) :: vk_prb e F q c.
Proof. reflexivity. Qed.
Lemma vk_rl_pr_884 : forall e F q c code, vr_rl_pr e F q c 0x8d884 code = vk_prb e F q c.
Proof. reflexivity. Qed.
Lemma vk_prb_cs : forall e F q c r v, In (r, v) ((19, F + 32) :: vk_prb e F q c) -> acallee_saved r.
Proof.
intros e F q c r v Hin. cbv [vk_prb vr_rl_pr] in Hin. cbn [Z.eqb Pos.eqb orb tl In] in Hin.
repeat (destruct Hin as [E|Hin]; [injection E as <- _; unfold acallee_saved; lia|]). contradiction.
Qed.

End f.
End d.

(* a list membership of concrete entries *)
Ltac vk23_inl := cbv [vk_prb vr_rl_pr vr_rl_rt vr_base]; cbn; repeat first [left; reflexivity | right].
(* a register of a boundary list: a fact of the run (assumption), or a register the run kept (KR) whose value the
   boundary before the run lists (HR) *)
Ltac vk23_reg KR HR :=
  first
  [ assumption
  | lazymatch goal with |- getr _ (Z_to_bv 5 ?r) = w64 ?v =>
      rewrite (KR r ltac:(vk23_inl)); apply (vr_rv_get _ _ r v HR); vk23_inl end ].
Ltac vk23_regs KR HR :=
  apply vr_rv_intro; intros r v Hin; cbv [vk_prb vr_rl_pr vr_base] in Hin; cbn [Z.eqb Pos.eqb orb tl app In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; vk23_reg KR HR |]); contradiction.

(* ---------------------------------------------------------------------------------------------------------------
   After pins_clear returns (0x8d7d0, listing offset 29344), at the FP state it returns at: proved in its own section,
   so it holds at every FP state *)
Section dp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fp.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section ep.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).

Lemma s23_after_pins : @tlv2_refusals_forget_spec fx rc SK PI B MT -> YF0m.CmdBSyms B -> ameter_laws MT ->
  cmd_sig_prog (PI := PI) -> vr_relro_img -> vr_pg_not_ro -> vr_rec_cells B -> vr_prog_unowned B -> vr_ro_of_aro B ->
  forall e pos F q c tp a k nm R1 rcd Oc1 ly2 S2 W2 regs2 mem2 md2,
  vr_ent B MT e -> Verbs.toks (e_D e) <> [] ->
  vr_h (e_R e) (e_D e) =
    (VerbsRun.pins_follow (fst (pins_clear_m (e_R e) (Some a))) (snd (pins_clear_m (e_R e) (Some a))), false) ->
  vr_k1 (e_R e) (e_D e) = 2 + (EV_PINS_CLEAR (e_R e) + (if snd (pins_clear_m (e_R e) (Some a)) =? 0
     then EV_LV2_REFUSALS_FORGET (fst (pins_clear_m (e_R e) (Some a))) else 0) + EV_SUP_RESP) ->
  (length (r_calls (fst (pins_clear_m (e_R e) (Some a)))) <= 1)%nat ->
  k <= 2 -> nm <= VR_NM_PRE ->
  pins_clear_m (e_R e) (Some a) = (R1, rcd) -> - 2 ^ 31 <= rcd < 2 ^ 31 ->
  vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_pr e F q c 0x8d88c rcd)
    R1 Oc1 (e_q0 e) (k + EV_PINS_CLEAR (e_R e)) (vr_k1 (e_R e) (e_D e) - EV_SUP_RESP) (nm + 3) VR_NM_PR
    ly2 S2 W2 regs2 mem2 md2 ->
  vr_line B e q W2 mem2 -> vr_copy B e F c tp W2 mem2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 29344)) mem2 (seg_rom SEGS)) md2) (vr_atpr B MT 0x8d88c e).
Proof.
intros TLV2 HB MTL SIGP RRO RPG RECC PROGU ROA
  e pos F q c tp a k nm R1 rcd Oc1 ly2 S2 W2 regs2 mem2 md2 He Hne Hvh Hk1 Hcl1 Hk Hnm Em Hrr HC2 HL2 HCP2.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Erc : rcd = snd (pins_clear_m (e_R e) (Some a))) by (rewrite Em; reflexivity).
assert (ER1 : R1 = fst (pins_clear_m (e_R e) (Some a))) by (rewrite Em; reflexivity).
rewrite <- ER1 in Hcl1.
pose proof (vk_k1_le (e_R e) (e_D e)) as Hk1ev.
pose proof (vk_bsum2 B MT e q c He) as Hbs.
assert (HSR1 : EV_SUP_RESP = 1) by reflexivity.
assert (Hntk : vr_pr_ntok 0x8d88c (length (Verbs.toks (e_D e)))).
{ unfold vr_pr_ntok. cbn [Z.eqb Pos.eqb orb]. destruct (Verbs.toks (e_D e)) as [|t0 ts] eqn:T; [congruence | cbn [length]; lia]. }
rewrite vk_rl_pr_88c in HC2.
pose proof HC2 as (HJ2 & _ & _ & _ & _ & Hrv2 & _).
assert (R102 : getr regs2 (Z_to_bv 5 10) = w64 rcd)
  by (apply (vr_rv_get regs2 _ 10 _ Hrv2); apply in_or_app; right; left; reflexivity).
pose proof (vr_seed0 W2 regs2 mem2 29344) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
pose proof (vr_env_agree regs2 []) as HAE.
assert (E10 : ew (Eimg (Ereg regs2 [])) 10 = w64 rcd)
  by (rewrite (ew_Eimg_Ereg_nat regs2 [] 10 (Z_to_bv 5 10) eq_refl); exact R102).
remember (Eimg (Ereg regs2 [])) as E eqn:HE. clear HE.
(* 0x8d7d0 bnez a0,0x8d88c *)
psrr_branch_pi RUNP BR HS.
- (* code <> 0: the stub 0x8d88c with the code pins_clear answered *)
  assert (Hrc0 : rcd <> 0).
  { intros ->. rewrite branch_ne_U in Hc. rewrite U_SOff, E10, Z.add_0_r in Hc.
    change (U E (SLit 0)) with 0 in Hc. vm_compute in Hc. discriminate Hc. }
  assert (Hrcb : (rcd =? 0) = false) by (apply Z.eqb_neq; exact Hrc0).
  paj_run_to_shc RUNTO HS HJ2 29532.
  { awr_ok_tac. }
  vk23_post msE mdv.
  vk23_mem HF Hm. clear HF HFr HG. rewrite Hm in HJ2.
  pose proof (vr_kept_regs E _ _ regs2 [] [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 24; 25; 26; 27] HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pmkst HS. rewrite Hm.
  apply SRr_ret. unfold vr_atpr, vr_pr.
  exists rcd, R1, Oc1, pos, F, q, c, tp, ly2, S2, (ms_regs msE), mem2, mdv, (k + EV_PINS_CLEAR (e_R e)), (nm + 3).
  split; [unfold cfg_at, w64; replace (vr_pc 0x8d88c) with (BASE + 29532) by (unfold vr_pc, AF_verbs_receive; lia);
    reflexivity|].
  split; [intros Hx; exfalso; exact (Hx eq_refl)|].
  split; [exact Hrr|].
  split; [rewrite Hvh; unfold VerbsRun.pins_follow; rewrite <- Erc, <- ER1, Hrcb; reflexivity|].
  split; [exact Hne|]. split; [exact Hntk|].
  split; [|split; [exact HL2 | exact HCP2]].
  rewrite vk_rl_pr_88c.
  apply (vr_core_move B MT RRO RPG RECC PROGU ROA e pos F _ vr_sh2 (vr_sl3 F q c) _ R1 Oc1 (e_q0 e) _ _ _ _
    ly2 S2 W2 regs2 mem2 md2 (vr_sl3 F q c) _ _ _ (ms_regs msE) mem2 mdv HC2 HJ2 (fun _ => eq_refl)).
  + vk23_regs KR Hrv2.
  + apply incl_refl.
  + lia.
  + lia.
- (* code 0: 0x8d7d4 jal lv2_refusals_forget(NULL) *)
  assert (Hrc0 : rcd = 0).
  { rewrite branch_ne_U in Hc. rewrite U_SOff, E10, Z.add_0_r in Hc.
    change (U E (SLit 0)) with 0 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    unfold w64 in Hc. rewrite Z_to_bv_unsigned in Hc. unfold zcanon, M64, bv_wrap in Hc.
    change (bv_modulus 64) with (2 ^ 64) in Hc. rewrite Zmod_mod in Hc. exact (mod64_zero rcd Hrr Hc). }
  rewrite Hrc0 in *.
  paj_run_shc RUNP RUNC HS HJ2.
  { awr_ok_tac. }
  vk23_post msL mdv.
  vk23_mem HF Hm. clear HF HFr HG. rewrite Hm in HJ2.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  pose proof (vr_kept_regs E _ _ regs2 [] [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 24; 25; 26; 27] HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  assert (Q10' : getr (ms_regs msL) 10 = w64 0)
    by (rewrite Q10; first [exact E10 | reflexivity | (rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E10)]).
  assert (HC4 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
    ((10, 0) :: (19, F + 32) :: vk_prb e F q c) R1 Oc1 (e_q0 e) (k + EV_PINS_CLEAR (e_R e))
    (vr_k1 (e_R e) (e_D e) - EV_SUP_RESP) (nm + 3) VR_NM_PR ly2 S2 W2 (ms_regs msL) mem2 mdv).
  { apply (vr_core_move B MT RRO RPG RECC PROGU ROA e pos F _ vr_sh2 (vr_sl3 F q c) _ R1 Oc1 (e_q0 e) _ _ _ _
      ly2 S2 W2 regs2 mem2 md2 (vr_sl3 F q c) _ _ _ (ms_regs msL) mem2 mdv HC2 HJ2 (fun _ => eq_refl)).
    - vk23_regs KR Hrv2.
    - apply incl_refl.
    - lia.
    - lia. }
  pmkst HS. rewrite Hm.
  assert (Epc : pa_sigma CS_lv2_refusals_forget = BASE + AF_lv2_refusals_forget).
  { assert (E0 : cmd_af CS_lv2_refusals_forget = AF_lv2_refusals_forget) by (vm_compute; reflexivity).
    rewrite (SIGP CS_lv2_refusals_forget ltac:(unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right])), E0.
    reflexivity. }
  rewrite Epc.
  assert (Hvh' : vr_h (e_R e) (e_D e) = (lv2_refusals_forget_m R1 None, resp 0, false)).
  { rewrite Hvh. unfold VerbsRun.pins_follow. rewrite <- Erc, <- ER1. reflexivity. }
  assert (Hk1' : vr_k1 (e_R e) (e_D e) = 2 + (EV_PINS_CLEAR (e_R e) + EV_LV2_REFUSALS_FORGET R1 + EV_SUP_RESP)).
  { rewrite Hk1, <- Erc, <- ER1. reflexivity. }
  assert (Hsf1 : rec_spill_frees R1 = 0).
  { unfold rec_spill_frees. destruct (Nat.ltb_spec (length (r_calls R1)) 16); [reflexivity | lia]. }
  assert (HEVL : EV_LV2_REFUSALS_FORGET R1 = 1)
    by (unfold EV_LV2_REFUSALS_FORGET, EV_RECORD, EV_ARG_S, EV_XMALLOC; rewrite Hsf1; reflexivity).
  apply (vk_lv2 B MT RRO RPG RECC PROGU ROA MTL HB TLV2 e pos F q c tp [vr_lb e q; vr_cb e c]
    ((10, 0) :: (19, F + 32) :: vk_prb e F q c) ((19, F + 32) :: vk_prb e F q c)
    R1 Oc1 (e_q0 e) (k + EV_PINS_CLEAR (e_R e)) (vr_k1 (e_R e) (e_D e) - EV_SUP_RESP)
    (vr_k1 (e_R e) (e_D e) - EV_SUP_RESP) (nm + 3) VR_NM_PR VR_NM_PR ly2 S2 W2 (ms_regs msL) mem2 mdv 29352 _
    He HC4 HL2 HCP2 (or_introl eq_refl) (or_intror (or_introl eq_refl)) Q1 ltac:(lia) eq_refl Q10').
  + rewrite HEVL. rewrite Hk1' in Hk1ev. lia.
  + rewrite HEVL, Hk1'. lia.
  + unfold VERBS_RECEIVE_MALLOCS, VR_NM_PRE in *. lia.
  + unfold VR_NM_PR, VR_NM_PRE in *. lia.
  + unfold LMAX, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ. lia.
  + intros r0 v0 Hin. split; [exact (vk_prb_cs e F q c r0 v0 Hin) | right; exact Hin].
  + (* after lv2_refusals_forget, 0x8d7d8 li a0,0; j 0x8d88c *)
    intros Oc5 ly5 S5 W5 regs5 mem5 md5 HC5 HL5 HCP5.
    pose proof HC5 as (HJ5 & _ & _ & _ & _ & Hrv5 & _).
    pose proof (vr_seed0 W5 regs5 mem5 29352) as HS5.
    assert (HEI5 : img_env VAL A_LIM (Eimg (Ereg regs5 []))) by apply Eimg_env.
    pose proof (vr_env_agree regs5 []) as HAE5.
    remember (Eimg (Ereg regs5 [])) as E5 eqn:HE5. clear HE5.
    paj_run_to_shc RUNTO HS5 HJ5 29532.
    { awr_ok_tac. }
    vk23_post ms6 mdv6.
    vk23_mem HF Hm6. clear HF HFr HG. rewrite Hm6 in HJ5.
    prreg HS5 (10%bv : bv 5) Q10c.
    assert (Q10c' : getr (ms_regs ms6) (Z_to_bv 5 10) = w64 0) by exact Q10c.
    pose proof (vr_kept_regs E5 _ _ regs5 [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27] HS5 HAE5
      ltac:(vm_compute; reflexivity)) as KR5.
    cbn [ms_regs restrict] in KR5.
    pmkst HS5. rewrite Hm6.
    apply SRr_ret. unfold vr_atpr, vr_pr.
    exists 0, (lv2_refusals_forget_m R1 None), Oc5, pos, F, q, c, tp, ly5, S5, (ms_regs ms6), mem5, mdv6,
      (k + EV_PINS_CLEAR (e_R e) + EV_LV2_REFUSALS_FORGET R1), (nm + 3 + 1).
    split; [unfold cfg_at, w64; replace (vr_pc 0x8d88c) with (BASE + 29532) by (unfold vr_pc, AF_verbs_receive; lia);
      reflexivity|].
    split; [intros Hx; exfalso; exact (Hx eq_refl)|].
    split; [lia|].
    split; [exact Hvh'|].
    split; [exact Hne|]. split; [exact Hntk|].
    split; [|split; [exact HL5 | exact HCP5]].
    rewrite vk_rl_pr_88c.
    apply (vr_core_move B MT RRO RPG RECC PROGU ROA e pos F _ vr_sh2 (vr_sl3 F q c) _ _ Oc5 (e_q0 e) _ _ _ _
      ly5 S5 W5 regs5 mem5 md5 (vr_sl3 F q c) _ _ _ (ms_regs ms6) mem5 mdv6 HC5 HJ5 (fun _ => eq_refl)).
    * vk23_regs KR5 Hrv5.
    * apply incl_refl.
    * lia.
    * lia.
Qed.

End ep.
End fp.
End dp.

(* ---------------------------------------------------------------------------------------------------------------
   The segment *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the callees' contracts (verbs_receive_c.v), fx-generic, and the record facts of the interface *)
Hypothesis TLV2_REFUSALS_FORGET : forall fx0 : YK11.FPState, @tlv2_refusals_forget_spec fx0 rc SK PI B MT.
Hypothesis TPINS_CLEAR : forall fx0 : YK11.FPState, @tpins_clear_spec fx0 rc SK PI B MT.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).

Lemma vr_s23 : vr_s23_stmt B MT.
Proof.
intros e W cf He HP.
destruct HP as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & Hcf & Hroute & Hne & HC & HL & HCP).
pose proof HC as (HJ & Hk & _ & Hnm & (EF & _ & _) & Hrv & _ & Hsp & _ & Hrec & _ & Hperm & _).
pose proof He as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HDn & _ & _ & _ & _ & _ & Hcalls & _).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (vk_s1_bounds e) as Hs1b.
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in Hal16, HSTK0, Hceil, Hslo, Hshi, H47, Hbot, Htop2, Htop.
assert (HV : 224 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hfr4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hfr4) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
assert (Hnt : 0 <= vr_ntok (e_D e) <= 64).
{ unfold vr_ntok, Verbs.toks, Verbs.line_words_max. rewrite length_firstn. lia. }
assert (R9 : getr regsc (Z_to_bv 5 9) = w64 (vr_s1 e))
  by (apply (vr_rv_get regsc _ _ _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R21 : getr regsc (Z_to_bv 5 21) = w64 (vr_ntok (e_D e)))
  by (apply (vr_rv_get regsc _ 21 _ Hrv); vk23_inl).
pose proof (vk_k1_le (e_R e) (e_D e)) as Hk1ev.
pose proof (vk_bsum2 B MT e q c He) as Hbs.
pose proof HCP as (_ & (_ & Htkl & _ & _)).
subst cf. unfold cfg_at, w64.
replace (vr_pc (vr_route_pc VRR.RPinclr)) with (BASE + 29316) by (unfold vr_pc, vr_route_pc, AF_verbs_receive; lia).
destruct (Nat.eq_dec (length (Verbs.toks (e_D e))) 2) as [H2 | H2].
- (* two words: pins_clear(tok[1]) *)
  destruct (Verbs.toks (e_D e)) as [|vw [|a [|b rest]]] eqn:T; try (cbn in H2; lia).
  destruct (vk_pinclr_two (e_R e) (e_D e) vw a T ltac:(rewrite T; exact Hroute)) as [Hvh Hk1].
  assert (Hne' : Verbs.toks (e_D e) <> []) by (rewrite T; discriminate).
  assert (HlenP : length tp = 2%nat) by (rewrite Htkl; rewrite ?T; reflexivity).
  destruct tp as [|p0 [|p1 [|p2 tp']]]; cbn in HlenP; try lia.
  destruct (vk_tok_arg B e F c [p0; p1] lyc Sc W memc mdc (e_O e) [vr_lb e q; vr_cb e c] 1 p1 a HAR Hperm
    (or_intror (or_introl eq_refl)) HCP eq_refl ltac:(rewrite T; reflexivity))
    as (Hblk & Hap & Hstra & Hlena & Hp1m & Hp14 & Hp1c).
  assert (Hav40 : aval_mem (rdW W memc) (vr_s1 e + 40) 8 (F + 32)).
  { unfold vr_spill in Hsp; rewrite Forall_forall in Hsp. exact (Hsp (40, F + 32) ltac:(unfold vr_sl3; cbn; tauto)). }
  set (E := Eimg (Ereg regsc [w64 (F + 32); w64 p1])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc [w64 (F + 32); w64 p1]) E) by (subst E; apply vr_env_agree).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (E9 : bv_unsigned (ew E 9%nat) = vr_s1 e).
  { subst E. rewrite (ew_Eimg_Ereg_nat regsc _ 9%nat (Z_to_bv 5 9) eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
  assert (E32 : ew E 32%nat = w64 (F + 32)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    pose proof (ew_Ereg_extra regsc [w64 (F + 32); w64 p1] 0%nat) as HH. cbn [Nat.add nth] in HH. exact HH. }
  assert (E33 : ew E 33%nat = w64 p1).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    pose proof (ew_Ereg_extra regsc [w64 (F + 32); w64 p1] 1%nat) as HH. cbn [Nat.add nth] in HH. exact HH. }
  assert (E32u : bv_unsigned (ew E 32%nat) = F + 32) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi SEGS VAL E ss23t (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 29316)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss23t. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor]].
      + unfold r_sp23, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (vr_s1 e) 40 8%N (SOff 32 0) (F + 32)).
        * cbn [sv_denot]. rewrite E32. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        * cbn. lia.
        * apply vr_val_mem_of_aval. exact Hav40.
      + unfold r_tok23, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E32u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (F + 32) 8 8%N (SOff 33 0) p1).
        * cbn [sv_denot]. rewrite E33. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        * cbn. lia.
        * apply vr_val_mem_of_aval. replace (F + 32 + 8) with (F + 32 + 8 * Z.of_nat 1) by lia. exact Hp1m.
    - cbn [pairwise_disjoint all_disjoint]. split; [|split; exact I]. split; [|exact I].
      unfold extent_disjoint, r_sp23, r_tok23. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E32u. right. lia.
    - split; [exact I | split; exact I]. }
  clearbody E.
  (* 0x8d7b4 li a0,2; stops at 0x8d7b8 bne s5,a0 *)
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  vk23_post ms1 mdv1.
  vk23_mem HF Hm1. clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    unfold vr_ntok in Hc. rewrite T in Hc. vm_compute in Hc. discriminate Hc.
  + clear Hc.
    (* 0x8d7bc li a0,-9; ld s3,40(s1); stops at 0x8d7c4 bltu a0,s3,0x8d938 *)
    paj_run_sh RUNP HS HJ.
    { awr_ok_tac. }
    vk23_post ms2 mdv2.
    vk23_mem HF Hm2. clear HF HFr HG.
    psrr_branch_pi RUNP BR HS.
    * (* the UBSan trap 0x8d938: tok + 8 would wrap; tok = F + 32 is far below 2 ^ 64 - 9 *)
      exfalso. rewrite branch_ltu_U in Hc. rewrite (U_atom E 32 _ E32) in Hc by lia.
      lazymatch type of Hc with context [U E ?x] =>
        let y := eval vm_compute in (U E x) in change (U E x) with y in Hc end.
      apply Z.ltb_lt in Hc. lia.
    * clear Hc.
      (* 0x8d7c8 ld a0,8(s3); 0x8d7cc jal pins_clear *)
      paj_run_shc RUNP RUNC HS HJ.
      { awr_ok_tac. }
      vk23_post ms3 mdv3.
      vk23_mem HF Hm3. clear HF HFr HG. rewrite Hm2, Hm1 in Hm3. rewrite Hm3 in HJ.
      prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (19%bv : bv 5) Q19.
      rewrite ?E33 in Q10. rewrite ?E32 in Q19.
      pose proof (vr_kept_regs E _ _ regsc [w64 (F + 32); w64 p1] [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 26; 27]
        HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      assert (Q10' : getr (ms_regs ms3) 10 = w64 p1)
        by (rewrite Q10; first [exact E33 | reflexivity | (rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E33)]).
      assert (Q19' : getr (ms_regs ms3) (Z_to_bv 5 19) = w64 (F + 32)) by exact Q19.
      set (rl1 := (19, F + 32) :: vk_prb e F q c).
      assert (HC1 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl1
        (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs ms3) memc mdv3).
      { apply (vr_core_move B MT RRO RPG RECC PROGU ROA e pos F _ vr_sh2 (vr_sl3 F q c) _ (e_R e) (e_O e) (e_q0 e) k 2
          nm VR_NM_PRE lyc Sc W regsc memc mdc (vr_sl3 F q c) rl1 2 VR_NM_PRE (ms_regs ms3) memc mdv3 HC HJ
          (fun _ => eq_refl)).
        - unfold rl1. vk23_regs KR Hrv.
        - apply incl_refl.
        - lia.
        - lia. }
      pmkst HS. rewrite Hm3.
      assert (Epc : pa_sigma CS_pins_clear = BASE + AF_pins_clear).
      { assert (E0 : cmd_af CS_pins_clear = AF_pins_clear) by (vm_compute; reflexivity).
        rewrite (SIGP CS_pins_clear ltac:(unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right])), E0.
        reflexivity. }
      rewrite Epc.
      assert (Hsf0 : rec_spill_frees (e_R e) = 0) by (unfold rec_spill_frees; rewrite Hcalls; reflexivity).
      pose proof (vk_code_range B lyc Sc _ (e_R e) (e_O e) Hrec) as Hcode0.
      assert (Hrcr : - 2 ^ 31 <= snd (pins_clear_m (e_R e) (Some a)) < 2 ^ 31)
        by (destruct (vk_code_pins_clear (e_R e) (Some a)) as [-> | ->]; lia).
      pose proof (resp_length _ Hrcr) as Hrl0.
      assert (HL2pos : 0 <= (if snd (pins_clear_m (e_R e) (Some a)) =? 0
        then EV_LV2_REFUSALS_FORGET (fst (pins_clear_m (e_R e) (Some a))) else 0)).
      { destruct (_ =? 0); [|lia]. unfold EV_LV2_REFUSALS_FORGET, EV_RECORD, EV_ARG_S, EV_XMALLOC.
        pose proof (vk_rsf_nonneg (fst (pins_clear_m (e_R e) (Some a)))). lia. }
      assert (HSR1 : EV_SUP_RESP = 1) by reflexivity.
      assert (Hcl1 : (length (r_calls (fst (pins_clear_m (e_R e) (Some a)))) <= 1)%nat)
        by (pose proof (vk_calls_pins_clear (e_R e) (Some a)) as HH; rewrite Hcalls in HH; exact HH).
      apply (vk_pins_clear B MT RRO RPG RECC PROGU ROA MTL HB (TPINS_CLEAR fx) e pos F q c [p0; p1]
        [vr_lb e q; vr_cb e c] rl1 (e_R e) (e_O e) (e_q0 e) k 2 (vr_k1 (e_R e) (e_D e) - EV_SUP_RESP) nm VR_NM_PRE
        VR_NM_PR lyc Sc W (ms_regs ms3) memc mdv3 p1 a 29344 (vr_rl_pr e F q c 0x8d88c) _ He HC1 HL HCP
        (or_introl eq_refl) (or_intror (or_introl eq_refl)) Q1 ltac:(lia) eq_refl Q10' ltac:(lia)
        Hblk Hap Hstra Hlena Hsf0).
      -- rewrite Hk1 in Hk1ev. lia.
      -- rewrite Hk1. lia.
      -- unfold VERBS_RECEIVE_MALLOCS, VR_NM_PRE in *. lia.
      -- unfold VR_NM_PR, VR_NM_PRE in *. lia.
      -- rewrite Hcalls. unfold LIVE_PINS_CLEAR, LIVE_ARG_S, LIVE_ANSWER_CODE, LIVE_HAND_BACK, LIVE_XMALLOC.
         cbn [sarg length]. unfold LMAX, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in *. lia.
      -- intros t r0 v0 Hin. rewrite vk_rl_pr_88c in Hin. destruct Hin as [E1 | Hin].
         ++ left. injection E1 as <- <-. split; reflexivity.
         ++ right. split; [exact (vk_prb_cs e F q c r0 v0 Hin) | exact Hin].
      -- (* after pins_clear: 0x8d7d0, at the FP state fx' pins_clear returns at *)
         intros fx' R1 rcd Oc1 ly2 S2 W2 regs2 mem2 md2 Hfx Em Hrr HC2 HL2 HCP2.
         eapply SRr_mono; [exact (s23_after_pins (fx := fx') B MT (TLV2_REFUSALS_FORGET fx') HB MTL SIGP
           RRO RPG RECC PROGU ROA e pos F q c [p0; p1] a k nm R1 rcd Oc1 ly2 S2 W2 regs2 mem2 md2
           (vk_ent_fx B MT fx fx' e He Hfx) Hne' Hvh Hk1 Hcl1 Hk Hnm Em Hrr HC2 HL2 HCP2)|].
         intros W' cf' _ Hh. exists fx'. split; [exact Hfx|]. unfold vrF_or, vr_or. right. exact Hh.
- (* not two words: 0x8d7b4 li a0,2; bne s5,a0,0x8d884 taken -- the refusal stub 0x8d884 *)
  destruct (vk_pinclr_rej (e_R e) (e_D e) Hroute Hne H2) as [Hvh Hk1].
  pose proof (vr_seed0 W regsc memc 29316) as HS.
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc []))) by apply Eimg_env.
  pose proof (vr_env_agree regsc []) as HAE.
  assert (E21 : ew (Eimg (Ereg regsc [])) 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (rewrite (ew_Eimg_Ereg_nat regsc [] 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  remember (Eimg (Ereg regsc [])) as E eqn:HE. clear HE.
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  vk23_post ms1 mdv1.
  vk23_mem HF Hm1. clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  + (* ntok <> 2: at 0x8d884 *)
    paj_run_to_shc RUNTO HS HJ 29524.
    { awr_ok_tac. }
    vk23_post ms2 mdv2.
    vk23_mem HF Hm2. clear HF HFr HG. rewrite Hm1 in Hm2. rewrite Hm2 in HJ.
    pose proof (vr_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27] HS HAE
      ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Hm2.
    apply SRr_ret. exists fx. split; [apply fxrel_refl|]. unfold vrF_or, vr_or. left.
    unfold vrF_pr, vr_atpr, vr_pr.
    exists (-902), (e_R e), (e_O e), pos, F, q, c, tp, lyc, Sc, (ms_regs ms2), memc, mdv2, k, nm.
    split; [unfold cfg_at, w64; replace (vr_pc 0x8d884) with (BASE + 29524) by (unfold vr_pc, AF_verbs_receive; lia);
      reflexivity|].
    split; [intros _; reflexivity|].
    split; [lia|].
    split; [exact Hvh|].
    split; [exact Hne|].
    split; [unfold vr_pr_ntok; cbn [Z.eqb Pos.eqb orb];
      destruct (Verbs.toks (e_D e)) as [|t0 ts] eqn:T; [congruence | cbn [length]; lia]|].
    split; [|split; [exact HL | exact HCP]].
    rewrite vk_rl_pr_884.
    apply (vr_core_move B MT RRO RPG RECC PROGU ROA e pos F _ vr_sh2 (vr_sl3 F q c) _ (e_R e) (e_O e) (e_q0 e) k 2 nm
      VR_NM_PRE lyc Sc W regsc memc mdc (vr_sl3 F q c) _ (vr_k1 (e_R e) (e_D e) - EV_SUP_RESP) VR_NM_PR
      (ms_regs ms2) memc mdv2 HC HJ (fun _ => eq_refl)).
    * vk23_regs KR Hrv.
    * apply incl_refl.
    * rewrite Hk1. lia.
    * unfold VR_NM_PR, VR_NM_PRE. lia.
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    change (U E (SLit 2)) with 2 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold vr_ntok in Hc. lia.
Qed.

End e.
End f.
End d.
