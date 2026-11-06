(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S05 (EMPTY, 0x8d8cc-0x8d8f8) of the walk of verbs_receive on the ASan
   build of plugin-hostd/fuzz_command (lib/A/Prog/verbs_receive_iface.v, vr_s05_stmt): the copy holds no word, so
     add s3,s6,s3; lb a0,0(s3); bnez a0,0x8ded8   (the inline check of msg+0, check #6: covered, not taken)
     lw s7,0(s8); li a0,-902; jal sup_resp        (sup_resp_c.v through PaCall's cl_callS)
     mv a1,a0; mv a0,s7; jal reply                (reply_c.v through the kit's vr_join_call)
     mv s2,s5; ld s3,56(s1); j 0x8db50            (vr_af)
   The check is removed by tok_load over the shadow entry of the message object (the caller's side-stack frame,
   vr_ent's afobj msg 24), s6 = msg >> 3 seeded as the shift the tokenizer computed at 0x8d698. The sup_resp call is
   S29's (verbs_receive_s29.v v29_pr_call, v29_call_post, v29_meter_pre/post), here on
   the spill slots vr_sl2 of the no-word path; the message object's facts are S02's kit's (verbs_receive_s02_kit.v
   vr_caller_kept). All names of this file carry the prefix vr05_. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route verbs_receive_pre.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import socket_send_c reply_c sup_resp_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import arg_i_c sup_after_reply_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_live verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_s30_m verbs_receive_s30_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac vr05_inl := cbn; repeat first [left; reflexivity | right].
Ltac vr05_reg KR HR :=
  first
  [ assumption
  | lazymatch goal with |- getr _ (Z_to_bv 5 ?r) = w64 ?v =>
      rewrite (KR r ltac:(vr05_inl)); apply (vr_rv_get _ _ r v HR); unfold vr_base; vr05_inl end ].
Ltac vr05_regs KR HR :=
  apply vr_rv_intro; intros r v Hin; unfold vr_base in Hin; cbn [app In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; vr05_reg KR HR |]); contradiction.
Ltac vr05_fa := cbv beta; repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia.

(* ------------------------------------------------------------------------------------------------------------
   The model: no word, so the step is sup_resp(-902) and no call follows the reply *)
Lemma vr05_model : forall R D, Verbs.toks D = [] ->
vr_aft D = None /\ vr_h R D = (R, resp (-902), false) /\ vr_k1 R D = 2 + EV_SUP_RESP.
Proof.
intros R D H. pose proof (vrm_empty atoi_a D H) as E.
assert (S : vr_st D = Verbs.SResp (-902)) by (unfold vr_st; rewrite E; reflexivity).
split; [unfold vr_aft; rewrite E; reflexivity|].
split; [unfold vr_h; rewrite S; reflexivity|].
unfold vr_k1. rewrite H. reflexivity.
Qed.

(* the four bytes of the sender: their value modulo 2^32 *)
Lemma vr05_aval_mod : forall (rd : reader) a v, aval_mem rd a 4 v -> aval_mem rd a 4 (v mod 2 ^ 32).
Proof.
intros rd a v H k Hk. rewrite (H k Hk). f_equal. unfold YG0f.le_byte.
assert (E : 2 ^ (8 * Z.of_nat 4) = 2 ^ 32) by reflexivity. rewrite E. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* a register of the seed set to a term with the register's value *)
Lemma vr05_regs_ok_set : forall E sr (regs : bvmap 5 word) (r : bv 5) e, YP0l.regs_ok E sr regs ->
sv_denot E e = getr regs r -> YP0l.regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hr0; [apply Hr|].
specialize (Hr r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
- apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
- exact Hr.
Qed.

Lemma vr05_m902 : Z_to_bv 64 18446744073709550714 = w64 (-902).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma vr05_al8_of_al64 : forall x, x mod 64 = 0 -> x mod 8 = 0.
Proof.
intros x H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia].
destruct H as [c Hc]. exists (8 * c). lia.
Qed.

(* the symbolic state at 0x8d8cc: s6 is the shift of msg (atom 24) the tokenizer computed, the message object of the
   caller's frame is the one region (its sender word, atom 32), x19 is the shadow base and msg is 8-aligned *)
Definition vr05_msg : YP09.region := YP09.mkRegion (Some 24%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition vr05_ss : sstate :=
mkSS 29672 (sr_set sr_atoms (Z_to_bv 5 22) (SAlu ALU_SRL (SOff 24 0) (SLit 3))) [vr05_msg] None
  (mkFacts [(19%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (24%nat, HPTR 3)] [] []).
Definition vr05_Bx : sv := SOff 19 0.
Definition vr05_SH : list shent := [mkSHE 24 0 24].
Definition vr05_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Lemma vr05_ro : Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) (ss_mem vr05_ss).
Proof. cbv [vr05_ss vr05_msg]. cbn. apply Forall_cons; [cbn; lia | apply Forall_nil]. Qed.

(* the registers kept across the call of sup_resp and of reply, and needed at the end *)
Definition vr05_rlk (F q : Z) : list (Z * Z) := [(20, F); (21, q); (25, shadow_addr F); (27, shadow_addr F + 4)].
Lemma vr05_sl2_incl : forall F q c, incl (vr_sl2 F c) (vr_sl3 F q c).
Proof. intros F q c x Hx. unfold vr_sl2 in Hx. destruct Hx as [<- | [<- | [<- | []]]]; unfold vr_sl3; vr05_inl. Qed.

(* ============================================================================================================
   After sup_resp (statement pass 4: sup_resp's post is FP-existential, so the code after its return runs at some FP
   state fx'). This part of the walk, from the return address 0x8d8e4 to the exit at 0x8db50, is proved here at this
   section's fx; once the section is closed it holds at every FP state, and vr_s05 below uses it at fx'. *)
Section dk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fk.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the entry's facts at another FP state: only the last conjunct of vr_ent (rounding mode 0) names the FP state *)
Lemma vr05_ent_at : forall (f0 : YK11.FPState) B MT e, vr_ent (fx := f0) B MT e -> frm0 fx ->
vr_ent (fx := fx) B MT e.
Proof.
intros f0 B MT e He H1. unfold vr_ent in *. cbv zeta in *.
repeat lazymatch type of He with
| ?A /\ ?R => let Ha := fresh "Ha" in destruct He as [Ha He]; split; [exact Ha|]
end.
exact H1.
Qed.
Section ek.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TREPLY : forall fx0 : YK11.FPState, treply_spec (fx := fx0) B MT.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let SEED := vr_seed_hd B MT RRO RPG RECC PROGU ROA TREPLY HB MTL SIGP.
Let MOVE := vr_core_move B MT RRO RPG RECC PROGU ROA.
Let JCALL := vr_join_call B MT RRO RPG RECC PROGU ROA TREPLY HB MTL SIGP.
(* the lemmas below take every hypothesis of this section, in the order above *)
Local Set Default Proof Using "All".

(* ------------------------------------------------------------------------------------------------------------
   0x8d8f0 (after reply): mv s2,s5; ld s3,56(s1); j 0x8db50 -> vr_af *)
Lemma vr05_p3 : forall e (W : world SEGS) (regs : bvmap 5 word) mem md pos F q c O2 ly2 S2 k nm,
vr_ent B MT e -> Verbs.toks (e_D e) = [] ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl2 F c) (vr05_rlk F q) (vr_R2 (e_R e) (e_D e)) O2 (e_q0 e)
  k (vr_k3 (e_R e) (e_D e)) nm VR_NM_AF ly2 S2 W regs mem md ->
vr_fresh B e (vr_lb e q) -> vr_fresh B e (vr_cb e c) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 29708)) mem (seg_rom SEGS)) md) (vr_af B MT e).
Proof.
intros e W regs mem md pos F q c O2 ly2 S2 k nm He Htk Hcore Hfl Hfc.
destruct (vr05_model (e_R e) (e_D e) Htk) as (Haft & Hh & Hk1).
pose proof Hcore as (HJ & _ & _ & _ & _ & HR & _).
unfold vr05_rlk in HR.
pose proof (SEED e pos F q c _ _ _ _ _ _ _ k _ nm _ ly2 S2 W regs mem md 29708 Hcore
  ltac:(left; reflexivity) ltac:(right; left; reflexivity) (vr05_sl2_incl F q c)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia)) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (vr_vals (vr_sl2 F c))))) by apply Eimg_env.
pose proof (vr_env_agree regs (vr_vals (vr_sl2 F c))) as HAE.
assert (E33 : ew (Eimg (Ereg regs (vr_vals (vr_sl2 F c)))) 33 = w64 c)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (E21 : ew (Eimg (Ereg regs (vr_vals (vr_sl2 F c)))) 21 = w64 q).
{ rewrite (ew_Eimg_Ereg_nat regs _ 21 (Z_to_bv 5 21) eq_refl). apply (vr_rv_get regs _ 21 _ HR). unfold vr_base. vr05_inl. }
remember (Eimg (Ereg regs (vr_vals (vr_sl2 F c)))) as E eqn:HE. clear HE.
paj_run_to_shc RUNTO HS HJ 30316.
{ awr_ok_tac. }
set (mdv := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody mdv.
assert (Eq : forall a, rdW W (ms_mem ms) a = rdW W mem a).
{ apply (vr_rdW_frame E _ W mem (ms_mem ms) HFr). apply vr_no_wrange. apply vr_ss_ro. }
clear HF HFr HG.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. rewrite ?E21 in Q18. rewrite ?E33 in Q19.
pose proof (vr_kept_regs E _ _ regs _ [2; 3; 4; 8; 9; 20; 25; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
apply SRr_ret.
assert (Hqv : vr_qv e = e_q0 e) by (unfold vr_qv, vr_quit; rewrite Hh; reflexivity).
assert (Hk3 : vr_k3 (e_R e) (e_D e) = vr_k2 (e_R e) (e_D e)) by (unfold vr_k3; rewrite Haft; cbn [ev_after]; lia).
exists O2, pos, F, q, c, ly2, S2, (ms_regs ms), (ms_mem ms), mdv, k, nm.
split; [unfold cfg_at, w64; replace (vr_pc 0x8db50) with (BASE + 30316) by (unfold vr_pc, AF_verbs_receive; lia);
  reflexivity|].
split; [|split; [exact Hfl | exact Hfc]].
replace (vr_R3 (e_R e) (e_D e)) with (vr_R2 (e_R e) (e_D e)) by (unfold vr_R3; rewrite Haft; reflexivity).
rewrite Hqv.
apply (MOVE e pos F _ vr_sh2 (vr_sl2 F c) _ _ O2 (e_q0 e) k (vr_k3 (e_R e) (e_D e)) nm VR_NM_AF ly2 S2 W regs mem md
  [(48, F)] (vr_rl_af F q c) (vr_k3 (e_R e) (e_D e)) VR_NM_AF (ms_regs ms) (ms_mem ms) mdv Hcore HJ Eq).
- unfold vr_rl_af. vr05_regs KR HR.
- intros x [<- | []]. unfold vr_sl2. vr05_inl.
- lia.
- lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   0x8d8e4 (after sup_resp): mv a1,a0; mv a0,s7; jal reply; then 0x8d8f0 *)
Lemma vr05_p2 : forall e (W : world SEGS) (regs : bvmap 5 word) mem md pos F q c tq lyc Sc k nm,
vr_ent B MT e -> Verbs.toks (e_D e) = [] ->
vr_core B MT e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c] vr_sh2 (vr_sl2 F c)
  ((10, tq) :: vr05_rlk F q) (vr_R1 (e_R e) (e_D e)) (e_O e) (e_q0 e) k (vr_k1 (e_R e) (e_D e)) nm VR_NM_HD
  lyc Sc W regs mem md ->
vr_line B e q W mem -> vr_fresh B e (vr_cb e c) ->
4096 <= tq -> astr_atR (rdW W mem) tq (vr_x (e_R e) (e_D e)) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 29696)) mem (seg_rom SEGS)) md) (vr_af B MT e).
Proof.
intros e W regs mem md pos F q c tq lyc Sc k nm He Htk Hcore Hline Hfc Htq4 Hstr.
destruct (vr05_model (e_R e) (e_D e) Htk) as (Haft & Hh & Hk1).
pose proof Hcore as (HJ & _ & _ & _ & (HFa & _) & HR & _).
unfold vr05_rlk in HR.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
(* tok[] holds no word: the copy predicate of the reply call *)
assert (Hcopy : forall m, vr_copy B e F c [] W m).
{ intros m. split; [exact Hfc|].
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
  assert (HF4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  destruct (al_frames _ _ LAWS lyc Sc W mem md 4 pos HAR HF4) as (Hal32 & _).
  split.
  - rewrite HFa. apply Z.mod_divide in Hal32; [|lia]. destruct Hal32 as [z Hz].
    apply Z.mod_divide; [lia|]. exists (4 * z + 4). lia.
  - split; [rewrite Htk; reflexivity|]. split; intros i p; [intros Hp | intros w Hp]; destruct i; discriminate Hp. }
pose proof (vr_seed0 W regs mem 29696) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
pose proof (vr_env_agree regs []) as HAE.
assert (E10 : ew (Eimg (Ereg regs [])) 10 = w64 tq).
{ rewrite (ew_Eimg_Ereg_nat regs [] 10 (Z_to_bv 5 10) eq_refl). apply (vr_rv_get regs _ 10 _ HR). unfold vr_base. vr05_inl. }
remember (Eimg (Ereg regs [])) as E eqn:HE. clear HE.
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
set (mdv := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody mdv.
assert (Eq : forall a, rdW W (ms_mem ms) a = rdW W mem a).
{ apply (vr_rdW_frame E _ W mem (ms_mem ms) HFr). apply vr_no_wrange. constructor. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (11%bv : bv 5) Q11. rewrite ?E10 in Q11.
pose proof (vr_kept_regs E _ _ regs _ [2; 3; 4; 8; 9; 20; 21; 25; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
assert (Hrv : vr_rv (ms_regs ms) (vr_base B e ++ (vr05_rlk F q ++ [(11, tq)]))) by (unfold vr05_rlk; vr05_regs KR HR).
pose proof (MOVE e pos F _ vr_sh2 (vr_sl2 F c) _ _ (e_O e) (e_q0 e) k _ nm _ lyc Sc W regs mem md
  (vr_sl2 F c) _ (vr_k1 (e_R e) (e_D e)) VR_NM_HD (ms_regs ms) (ms_mem ms) mdv Hcore HJ Eq Hrv
  (incl_refl _) (Z.le_refl _) (Z.le_refl _)) as Hcore2.
assert (Hk3 : vr_k3 (e_R e) (e_D e) = vr_k2 (e_R e) (e_D e)) by (unfold vr_k3; rewrite Haft; cbn [ev_after]; lia).
eapply SRr_bind.
{ apply (JCALL e W (ms_regs ms) (ms_mem ms) mdv pos F q c [] tq (vr_sl2 F c) (vr05_rlk F q) (e_O e) (e_q0 e) k nm
    lyc Sc 29708 (vr_k3 (e_R e) (e_D e)) VR_NM_AF He Hcore2 (vr_line_eq B e q W mem (ms_mem ms) Eq Hline)
    (Hcopy (ms_mem ms)) Q1).
  - lia.
  - reflexivity.
  - unfold vr05_rlk. repeat (apply Forall_cons; [unfold acallee_saved; cbn [fst]; lia|]). apply Forall_nil.
  - unfold vr_sl2. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil.
  - exact Htq4.
  - exact (vr_astr_eq _ _ tq _ Eq Hstr).
  - rewrite Hk3. lia.
  - unfold VR_NM_AR, VR_NM_AF. lia. }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & O2 & -> & HPres & Hcore3 & Hline3 & Hcopy3).
exact (vr05_p3 e W2 regs2 mem2 md2 pos F q c O2 ly2 S2 (k + EV_REPLY) (nm + 1) He Htk Hcore3 (proj1 Hline3) Hfc).
Qed.

End ek.
End fk.
End dk.

(* ============================================================================================================
   The segment: the entry at this section's fx, the call of sup_resp, then the continuation above at fx' *)
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
(* the callees' contracts at every FP state (statement pass 4, verbs_receive_c.v): sup_resp is called at this
   section's fx; reply runs after it, at the FP state sup_resp returns *)
Hypothesis TSUP_RESP : forall fx0 : YK11.FPState, tsup_resp_spec (fx := fx0) B MT.
Hypothesis TREPLY : forall fx0 : YK11.FPState, treply_spec (fx := fx0) B MT.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let MOVE := vr_core_move B MT RRO RPG RECC PROGU ROA.

(* ------------------------------------------------------------------------------------------------------------
   The entry's facts *)
Lemma vr05_ent_facts : forall e, vr_ent B MT e ->
afn_pre SEGS B VERBS_RECEIVE_STK (e_ly e) (e_S e) (e_W e) (e_regs e) (e_mem e) (e_md e) (e_ch e) /\
rec_repA B (e_ly e) (e_S e) (rdW (e_W e) (e_mem e)) (e_R e) (e_O e) /\
(0 <= e_n e <= 8192) /\ Z.of_nat (length (e_D e)) = e_n e /\
st_nev (e_S e) + ev_vr (e_R e) (e_D e) <= EV_MAX /\
blocks_bytes (e_S e) + LIVE_VERBS_RECEIVE <= LIVE_MAX /\
mo_ok MT (e_S e) (XM_VERBS_RECEIVE MT (e_R e) (e_D e)) /\
Z.of_nat (length (frames (e_S e))) <= 4 /\
r_calls (e_R e) = [] /\
Permutation (ablocks B (e_ly e) (e_S e)) (e_O e ++ e_rest e) /\
afobj SEGS B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_msg e) 24 /\
aval_mem (rdW (e_W e) (e_mem e)) (e_msg e) 4 (e_fd e) /\
frm0 fx.
Proof.
intros e H. unfold vr_ent in H.
destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
  H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & H32 & H33).
split; [exact H1|]. split; [exact H14|]. split; [exact H8|]. split; [exact H9|].
split; [exact H30|]. split; [exact H31|]. split; [exact H32|]. split; [exact H29|].
split; [exact H15|]. split; [exact H20|]. split; [exact H4|]. split; [exact H5 | exact H33].
Qed.

Lemma vr05_frameF : forall {e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc},
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
In (4, pos) (frames Sc) /\ AR SEGS B lyc Sc Wc memc mdc /\ 4096 <= F /\ F + 1024 <= alloc_ceiling.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc HC.
pose proof HC as (HJ & _ & _ & _ & (HF & _) & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 4 pos HAR Hin) as (H1 & H2 & _).
change (fs_frame_bytes 4) with 1024 in H2. rewrite <- HF in H1, H2.
split; [exact Hin|]. split; [exact HAR|]. split; [exact H1 | exact H2].
Qed.

Lemma vr05_stkF : forall {e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc},
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
astk_ok VERBS_RECEIVE_STK (e_ly e) (vr_sp0 e).
Proof.
intros. pose proof H as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _). exact Hstk.
Qed.

Lemma vr05_s1_bounds : forall e, astk_ok VERBS_RECEIVE_STK (e_ly e) (vr_sp0 e) ->
4096 <= vr_s1 e /\ vr_s1 e + 224 <= vr_sp0 e + 32 /\ vr_sp0 e <= 2 ^ 47 /\ vr_s1 e + 16 <= 2 ^ 64 /\
vr_sp0 e - 224 <= vr_s1 e <= vr_sp0 e - 192.
Proof.
intros e (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
unfold vr_s1. pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)). lia.
Qed.

Lemma vr05_s1_bounds2 : forall e, astk_ok VERBS_RECEIVE_STK (e_ly e) (vr_sp0 e) ->
alloc_ceiling <= vr_s1 e /\ (vr_s1 e - vr_sp0 e) mod 16 = 0 /\ vr_sp0 e mod 16 = 0 /\
SUP_RESP_STK - (vr_s1 e - vr_sp0 e) <= VERBS_RECEIVE_STK /\ 0 <= SUP_RESP_STK.
Proof.
intros e Hstk. pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HV : 16752 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HR : SUP_RESP_STK = 16528) by (vm_compute; reflexivity).
pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as Hmb.
unfold vr_s1 in *.
split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [exact Hal|]. split; lia.
Qed.

(* the message object of the caller's frame, and the shadow bytes of it, are kept by the journal of the walk (S02's
   kit, vr_caller_kept, with its two footprint facts) *)
Lemma vr05_fp_not_frame : forall e ly S (Wc : world SEGS) memc mdc cid pos' a,
AR SEGS B ly S Wc memc mdc ->
(forall pn, In pn (e_O e) -> In pn (ablocks B ly S)) ->
In (cid, pos') (frames S) ->
frame_addr ly cid pos' <= a < frame_addr ly cid pos' + fs_frame_bytes cid ->
~ inFP (vr_fp e) a.
Proof.
intros e ly S Wc memc mdc cid pos' a HAR HO Hin Ha (r & Hr & Hrr).
pose proof (frm_off_imgP B ly S Wc memc mdc cid pos' HAR Hin) as Hoff. unfold off_img in Hoff.
unfold vr_fp, VERBS_RECEIVE_PG in Hr. apply in_app_or in Hr as [Hr | Hr].
- unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, REC_SIZE, SC_SIZE in *.
  cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrr; zlia.
- apply in_map_iff in Hr as ([p m] & <- & Hpm). cbn [fst snd] in Hrr.
  pose proof (sep_block_frame SEGS B LAWS ly S Wc memc mdc p m cid pos' HAR (HO _ Hpm) Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
Qed.
Lemma vr05_fp_not_shadow : forall e lyc Sc (Wc : world SEGS) memc mdc a,
AR SEGS B lyc Sc Wc memc mdc ->
(forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc)) ->
kLowMemEnd <= a < kHighMemBeg -> ~ inFP (vr_fp e) a.
Proof.
intros e lyc Sc Wc memc mdc a HAR HO Ha (r & Hin & Hr).
unfold vr_fp, VERBS_RECEIVE_PG in Hin. apply in_app_or in Hin as [Hin | Hin].
- unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, REC_SIZE, SC_SIZE, kLowMemEnd, kHighMemBeg in *.
  cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
- apply in_map_iff in Hin as ([p m] & <- & Hpm). cbn [fst snd] in Hr.
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p m HAR (HO _ Hpm)) as (_ & _ & _ & [Hh1 Hh2] & _).
  unfold in_app, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. zlia.
Qed.
Lemma vr05_shadow_band : forall x n, 0 <= x -> 0 <= n -> x + n <= alloc_ceiling ->
kLowMemEnd <= shadow_addr x /\ shadow_addr (x + n) < kHighMemBeg.
Proof.
intros x n Hx Hn Hxn. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (H1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (H2 : (x + n) / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; [lia | zlia]).
unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg. zlia.
Qed.
Lemma vr05_caller_kept : forall e own lyc Sc (Wc : world SEGS) memc mdc kk a,
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  own lyc Sc Wc memc mdc kk ->
AR SEGS B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) ->
afobj SEGS B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_msg e) 24 ->
(forall pn, In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e))) ->
(e_msg e <= a < e_msg e + 24 \/ (exists i, 0 <= i < 3 /\ a = shadow_addr (e_msg e) + i)) ->
rdW Wc memc a = rdW (e_W e) (e_mem e) a.
Proof.
intros e own lyc Sc Wc memc mdc kk a HJ HAR0 ((cid & pos' & Hin & Hcid & Hal & Hlo & Hhi) & Hmod & _) HO Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
pose proof (shadow_mono (frame_addr (e_ly e) cid pos') (e_msg e) Hlo) as M1.
pose proof (shadow_range_end (frame_addr (e_ly e) cid pos') (fs_frame_bytes cid) Hfb) as M2.
pose proof (shadow_mono (e_msg e + 24) (frame_addr (e_ly e) cid pos' + fs_frame_bytes cid) Hhi) as M3.
destruct (frames_bounds SEGS B LAWS (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) cid pos' HAR0 Hin) as (Hf0 & Hfc & Hfapp).
apply F4 with (cid := cid) (pos := pos'); [exact Hin | |].
- destruct Ha as [Ha | (i & Hi & ->)].
  + left. unfold in_zr, frame_rng. cbn [fst snd]. zlia.
  + right. unfold in_zr. cbn [fst snd].
    destruct (frame_al64 SEGS B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) cid pos' HAR0 Hin)
      as (Ha64 & Hb64 & Hge64).
    pose proof (vr05_al8_of_al64 _ Ha64) as Hf8. pose proof (vr05_al8_of_al64 _ Hb64) as Hs8.
    pose proof (Z.div_mod (e_msg e) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (e_msg e) 8 ltac:(lia)) as P1.
    pose proof (Z.div_mod (frame_addr (e_ly e) cid pos') 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (frame_addr (e_ly e) cid pos') 8 ltac:(lia)) as P2.
    pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D3.
    pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)) as P3.
    unfold shadow_addr, SHADOW_OFF in *. zlia.
- destruct Ha as [Ha | (i & Hi & ->)].
  + exact (vr05_fp_not_frame e (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) cid pos' a HAR0 HO Hin ltac:(zlia)).
  + destruct (vr05_shadow_band (e_msg e) 24 ltac:(zlia) ltac:(lia) ltac:(zlia)) as [Hb1 Hb2].
    apply (vr05_fp_not_shadow e (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) _ HAR0 HO).
    pose proof (shadow_mono (e_msg e) (e_msg e + 24) ltac:(lia)) as Hmo.
    pose proof (Z.div_mod (e_msg e) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (e_msg e) 8 ltac:(lia)) as P1.
    pose proof (Z.div_mod (e_msg e + 24) 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (e_msg e + 24) 8 ltac:(lia)) as P2.
    unfold shadow_addr, SHADOW_OFF in *. zlia.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The meter at sup_resp's call: its account is xstrdup's one malloc of |resp code|+1 <= VERBS_RECEIVE_REQ bytes and no
   free, within its EV_SUP_RESP = 1 event; the room for it before the call (the interface's vri_meter_ok) and
   vr_meter after it (vri_meter_step). The meter reasoning of this call shape lives in these three lemmas only. *)
Lemma vr05_xm_le : forall code, - 2 ^ 31 <= code < 2 ^ 31 ->
XM_SUP_RESP MT code <= 1 * mo_malloc MT VERBS_RECEIVE_REQ + 0 * mo_free MT.
Proof.
intros code Hcode. pose proof (resp_length code Hcode) as Hrl.
assert (HXM : XM_SUP_RESP MT code <= mo_malloc MT VERBS_RECEIVE_REQ).
{ unfold XM_SUP_RESP, XM_XSTRDUP. apply (mo_malloc_mono MT MTL). unfold VERBS_RECEIVE_REQ. lia. }
lia.
Qed.

Lemma vr05_meter_pre : forall e Sc k nm code,
vr_ent B MT e -> - 2 ^ 31 <= code < 2 ^ 31 ->
vr_meter MT e Sc k nm -> k <= vr_k1 (e_R e) (e_D e) - EV_SUP_RESP ->
mo_ok MT Sc (XM_SUP_RESP MT code).
Proof.
intros e Sc k nm code He Hcode Hmet Hk.
pose proof (vr_k1_ev (e_R e) (e_D e)) as Hkev.
exact (vri_meter_ok B MT e Sc k nm (XM_SUP_RESP MT code) 1 0 EV_SUP_RESP MTL He Hmet (vr05_xm_le code Hcode)
  ltac:(unfold EV_SUP_RESP, EV_XSTRDUP; lia) ltac:(unfold EV_SUP_RESP, EV_XSTRDUP; lia) ltac:(lia)).
Qed.

Lemma vr05_meter_post : forall e Sc S2 k nm code,
- 2 ^ 31 <= code < 2 ^ 31 ->
vr_meter MT e Sc k nm -> mo_le MT Sc S2 (XM_SUP_RESP MT code) ->
vr_meter MT e S2 (k + EV_SUP_RESP) (nm + 1).
Proof.
intros e Sc S2 k nm code Hcode Hmet Hmo.
exact (vri_meter_step MT e Sc S2 k nm (XM_SUP_RESP MT code) 1 0 EV_SUP_RESP MTL Hmet Hmo (vr05_xm_le code Hcode)
  ltac:(unfold EV_SUP_RESP, EV_XSTRDUP; lia) ltac:(unfold EV_SUP_RESP, EV_XSTRDUP; lia)).
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The premises of tsup_resp_spec at 0x8d8e0 (S29's v29_call_pre, on the no-word path) *)
Lemma vr05_call_pre : forall e pos F q c sl rlp lyc Sc (W : world SEGS) regsc memc mdc k nm,
vr_ent B MT e -> Verbs.toks (e_D e) = [] ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 sl rlp (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
Z.of_nat (length (frames Sc)) <= 8 /\
arodata_okP SEGS RLO RHI B (rdW W memc) /\ cmd_ro_ok (rdW W memc) /\
st_nev Sc + EV_SUP_RESP <= EV_MAX /\ blocks_bytes Sc + LIVE_SUP_RESP (-902) <= LIVE_MAX /\
mo_ok MT Sc (XM_SUP_RESP MT (-902)).
Proof.
intros e pos F q c sl rlp lyc Sc W regsc memc mdc k nm He Htk HC.
destruct (vr05_model (e_R e) (e_D e) Htk) as (_ & _ & Hk1).
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & HnO & Hperm & Hquit).
destruct (vr05_ent_facts e He) as (HPRE & HREC0 & Hn8 & HDn & Hev & Hlive & Hmok & Hfrs4 & Hcalls0 & Hperm0 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & Hnev & Hk0 & _).
pose proof HPRE as (HAR0 & _).
pose proof (vr_k1_ev (e_R e) (e_D e)) as Hkev.
pose proof (resp_length (-902) ltac:(lia)) as Hrl.
assert (Hlb : vr_l (e_n e) (e_D e) <= 8192).
{ unfold vr_l. rewrite <- HDn. rewrite (proj2 (verbs_receive_pre.strnlen_upto (e_D e))).
  pose proof (verbs_receive_route.upto_len (fun b => bv_unsigned b =? 0) (e_D e)) as Hu.
  change (Verbs.upto0 (e_D e)) with (Verbs.upto (fun b => bv_unsigned b =? 0) (e_D e)). lia. }
assert (Hcb : Z.of_nat (length (Verbs.line (e_D e))) <= 8192).
{ pose proof (verbs_receive_route.line_len (e_D e)) as Hl. lia. }
assert (Hbb : blocks_bytes Sc <= blocks_bytes (e_S e) +
  (6 * Z.of_nat (length (r_calls (e_R e))) + 8) * (LMAX + 2) + bsum [vr_lb e q; vr_cb e c]).
{ exact (vr_live_le SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HAR Hperm0 Hperm Hrec). }
rewrite Hcalls0 in Hbb. cbn [length Z.of_nat] in Hbb.
assert (Hbs : bsum [vr_lb e q; vr_cb e c] <= 16386).
{ unfold bsum, vr_lb, vr_cb. cbn [fold_right snd]. lia. }
assert (Hlm : LMAX = 8192) by reflexivity.
split; [rewrite Hfrs; cbn [length app]; rewrite Nat2Z.inj_succ; lia|].
split; [exact (proj1 Henv)|].
split; [exact (proj1 (proj2 (proj2 Henv)))|].
split; [unfold EV_SUP_RESP, EV_XSTRDUP in *; lia|].
split.
{ unfold LIVE_SUP_RESP, LIVE_XSTRDUP, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in *. lia. }
exact (vr05_meter_pre e Sc k nm (-902) He ltac:(lia) Hmet ltac:(lia)).
Qed.

(* after sup_resp returned: the text is a block of its own; the frame, the spills, the saves, the blocks and the
   read-only and record facts are kept (the callee's journal has an empty footprint) (S29's v29_call_post) *)
Lemma vr05_call_post : forall (e : vrE) pos F q c lyc Sc (W : world SEGS) regsc memc mdc k nm rlp
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 tq rl2,
vr_ent B MT e -> Verbs.toks (e_D e) = [] ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl2 F c) rlp (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  ly2 S2 W2 mem2 md2 (k + EV_SUP_RESP) ->
ajournal SEGS B SUP_RESP_STK (vr_s1 e) [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV_SUP_RESP ->
Permutation (ablocks B ly2 S2) ((tq, Z.of_nat (length (resp (-902))) + 1) :: ablocks B lyc Sc) ->
(forall R O, rec_repA B lyc Sc (rdW W memc) R O -> rec_repA B ly2 S2 (rdW W2 mem2) (fst (sup_resp_m R (-902))) O) ->
mo_le MT Sc S2 (XM_SUP_RESP MT (-902)) ->
vr_rv regs2 (vr_base B e ++ rl2) ->
vr_core B MT e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c] vr_sh2 (vr_sl2 F c)
  rl2 (vr_R1 (e_R e) (e_D e)) (e_O e) (e_q0 e) (k + EV_SUP_RESP) (vr_k1 (e_R e) (e_D e)) (nm + 1) VR_NM_HD
  ly2 S2 W2 regs2 mem2 md2 /\
vr_line B e q W2 mem2.
Proof.
intros e pos F q c lyc Sc W regsc memc mdc k nm rlp ly2 S2 W2 regs2 mem2 md2 tq rl2
  He Htk HC Hline HJ2 HJc Hpq Hrectr Hmo Hrv2.
destruct (vr05_model (e_R e) (e_D e) Htk) as (Haft & Hh & Hk1).
assert (Hxv : vr_x (e_R e) (e_D e) = resp (-902)) by (unfold vr_x; rewrite Hh; reflexivity).
assert (HR1 : vr_R1 (e_R e) (e_D e) = e_R e) by (unfold vr_R1; rewrite Hh; reflexivity).
rewrite Hxv, HR1, Hk1.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & HnO & Hperm & Hquit).
destruct (vr05_frameF HC) as (Hinf & HAR & HF1 & HF2).
pose proof (vr05_stkF HC) as Hstk.
destruct (vr05_s1_bounds e Hstk) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e).
destruct (vr05_s1_bounds2 e Hstk) as (Hs2a & Hs2b & Hs2c & Hs2d & Hs2e).
destruct (vr05_ent_facts e He) as (_ & _ & Hn8 & HDn & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJc as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & G1 & G2 & G3 & G4 & _ & _ & _ & _ & _).
assert (Hnofp : forall a : Z, ~ inFP ([] : list (Z * Z)) a) by (intros a (r & [] & _)).
assert (Hsp2 : forall a, vr_s1 e <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memc a)
  by (intros a Ha; apply G1; [lia | lia | apply Hnofp]).
assert (Hblk : forall p n i, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
  rdW W2 mem2 (p + i) = rdW W memc (p + i)) by (intros p n i H1 H2 H3; exact (G2 p n i H1 H2 H3 (Hnofp _))).
assert (Himg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> rdW W2 mem2 a = rdW W memc a).
{ intros a H1 H2 H3. apply G3; try assumption.
  split; [intros Hs; destruct (sink_closed_pos [] (Forall_nil _) Hs) | apply Hnofp]. }
assert (Hfrm : forall a, (in_zr a (frame_rng lyc (4, pos)) \/
    in_zr a (shadow_addr (frame_addr lyc 4 pos), fs_frame_bytes 4 / 8)) -> rdW W2 mem2 a = rdW W memc a)
  by (intros a Ha; apply (G4 4 pos a Hinf Ha); apply Hnofp).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFA : frame_addr ly2 4 pos = frame_addr lyc 4 pos) by (unfold frame_addr; rewrite EF; reflexivity).
assert (EFL : flag_addr ly2 4 pos = flag_addr lyc 4 pos) by (unfold flag_addr; rewrite EF; reflexivity).
pose proof (resp_length (-902) ltac:(lia)) as Hrl.
assert (FB : fs_frame_bytes 4 = 1024) by reflexivity.
destruct Hfr as (HFeq & HFflag & HFsh).
assert (HinLb : In (vr_lb e q) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
assert (HinLb2 : In (vr_lb e q) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hpq)); right; exact HinLb).
split.
- (* vr_core *)
  split; [exact HJ2|].
  split; [lia|].
  split; [exact (vr05_meter_post e Sc S2 k nm (-902) ltac:(lia) Hmet Hmo)|].
  split; [unfold VR_NM_PRE, VR_NM_HD in *; lia|].
  split.
  { split; [rewrite EFA; exact HFeq|]. split.
    - rewrite EFL, <- HFflag. apply rdword_ext. intros kk Hkk. apply Hfrm. left.
      unfold frame_rng, in_zr. cbn [fst snd]. rewrite FB, <- HFeq. lia.
    - intros i Hi. rewrite Hfrm; [exact (HFsh i Hi)|]. right. unfold in_zr. cbn [fst snd].
      rewrite FB, <- HFeq. change (1024 / 8) with 128. lia. }
  split; [exact Hrv2|].
  split.
  { intros j r Hj.
    assert (Hjl : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbv [vr_saved_regs] in Hjl; cbn [length] in Hjl.
    apply (aval_mem_agree _ _ _ 8 _ (Hsv j r Hj)). intros kk Hkk. apply Hsp2. lia. }
  split.
  { unfold vr_spill in *. rewrite Forall_forall in Hsp |- *. intros ov Hov.
    assert (Hob : 0 <= fst ov <= 72).
    { unfold vr_sl2 in Hov. cbn [In] in Hov.
      repeat (destruct Hov as [<- | Hov]; [cbn [fst]; lia|]). destruct Hov. }
    apply (aval_mem_agree _ _ _ 8 _ (Hsp ov Hov)). intros kk Hkk.
    replace (vr_s1 e + fst ov + kk) with (vr_s1 e + (fst ov + kk)) by lia. apply Hsp2. lia. }
  split.
  { destruct Henv as (Haro & _).
    assert (HAR2s : AR SEGS B ly2 S2 W2 mem2 md2) by exact (proj1 HJ2).
    assert (Haro2 : arodata_okP SEGS RLO RHI B (rdW W2 mem2)).
    { intros a Hro Ho He'. rewrite Himg; [exact (Haro a Hro Ho He') | | exact Ho | exact He'].
      destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (RRO a Hr)]. }
    exact (vr_env_of_aro B MT RRO RPG RECC PROGU ROA ly2 S2 W2 mem2 md2 HAR2s Haro2). }
  split.
  { pose proof (Hrectr (e_R e) (e_O e) Hrec) as Hr2. cbn [sup_resp_m fst] in Hr2. exact Hr2. }
  split; [exact HnO|].
  split.
  { eapply Permutation_trans; [exact Hpq|].
    eapply Permutation_trans; [apply perm_skip; exact Hperm|]. apply Permutation_middle. }
  { intros j Hj.
    assert (HPG : inFP cmd_PG (A_G_QUITTING + Z.of_nat j)).
    { exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; vr05_inl | cbn [fst snd]; lia]. }
    destruct (PROGU _ HPG) as (P1 & P2 & P3).
    rewrite Himg; [exact (Hquit j Hj) | exact P1 | exact P2 | exact P3]. }
- (* the line *)
  destruct Hline as (Hfresh & Hls). split; [exact Hfresh|].
  assert (Hll : Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e)).
  { unfold vr_l. rewrite <- HDn. exact (vrm_line_le (e_D e)). }
  apply (astr_atR_agree _ _ q _ (vr_l (e_n e) (e_D e) + 1) Hls); [lia|].
  intros kk Hkk. apply (Hblk q (vr_l (e_n e) (e_D e) + 1) kk HinLb HinLb2).
  pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The call of sup_resp(-902) at 0x8d8e0 (S29's v29_resp_post / v29_pr_call, through PaFx's cl_callSF:
   sup_resp returns at some FP state fx') *)
Definition vr05_resp_post (code : Z) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists q,
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 Permutation (ablocks B ly' S') ((q, Z.of_nat (length (resp code)) + 1) :: ablocks B ly S) /\
 Forall (fun qk => iv_apart q (Z.of_nat (length (resp code)) + 1) (fst qk) (snd qk)) (ablocks B ly S) /\
 In (q, Z.of_nat (length (resp code)) + 1) (ablocks B ly' S') /\ astr_atR (rdW W' mem') q (resp code) /\
 (forall R O, rec_repA B ly S (rdW W mem) R O -> rec_repA B ly' S' (rdW W' mem') (fst (sup_resp_m R code)) O) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_RESP code /\
 mo_le MT S S' (XM_SUP_RESP MT code).

Lemma vr05_resp_call : forall e pos F q c lyc Sc (W : world SEGS) regs mem md k nm rlk,
vr_ent B MT e -> Verbs.toks (e_D e) = [] ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl2 F c) ((1, BASE + 29696) :: (10, -902) :: rlk)
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regs mem md ->
vr_line B e q W mem ->
Forall (fun rv => 18 <= fst rv <= 27) rlk ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_sup_resp)) mem (seg_rom SEGS)) md)
  (fun W2 c2 => exists (fx' : YK11.FPState) tq ly2 S2 regs2 mem2 md2,
   c2 = mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + 29696)) mem2 (seg_rom SEGS)) md2 /\ fxrel fx fx' /\
   4096 <= tq /\ astr_atR (rdW W2 mem2) tq (vr_x (e_R e) (e_D e)) /\
   vr_core B MT e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c] vr_sh2
     (vr_sl2 F c) ((10, tq) :: rlk) (vr_R1 (e_R e) (e_D e)) (e_O e) (e_q0 e) (k + EV_SUP_RESP)
     (vr_k1 (e_R e) (e_D e)) (nm + 1) VR_NM_HD ly2 S2 W2 regs2 mem2 md2 /\
   vr_line B e q W2 mem2).
Proof.
intros e pos F q c lyc Sc W regs mem md k nm rlk He Htk HC Hline Hcs.
destruct (vr05_model (e_R e) (e_D e) Htk) as (Haft & Hh & Hk1).
assert (Hxv : vr_x (e_R e) (e_D e) = resp (-902)) by (unfold vr_x; rewrite Hh; reflexivity).
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & HnO & Hperm & Hquit).
destruct (vr05_ent_facts e He) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm).
destruct (vr05_call_pre e pos F q c _ _ lyc Sc W regs mem md k nm He Htk HC)
  as (Hfrs8 & Haro & Hro & Hev1 & Hlv1 & Hmo1).
pose proof (vr05_stkF HC) as Hstk.
destruct (vr05_s1_bounds e Hstk) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e).
destruct (vr05_s1_bounds2 e Hstk) as (Hs2a & Hs2b & Hs2c & Hs2d & Hs2e).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (R1 : getr regs 1 = w64 (BASE + 29696))
  by (apply (vr_rv_get regs _ 1 _ Hrv); apply in_or_app; right; left; reflexivity).
assert (R10 : getr regs 10 = w64 (-902))
  by (apply (vr_rv_get regs _ 10 _ Hrv); apply in_or_app; right; right; left; reflexivity).
assert (R2 : getr regs 2 = w64 (vr_s1 e)) by (apply (vr_rv_get regs _ 2 _ Hrv); apply in_or_app; left; unfold vr_base; vr05_inl).
assert (R3 : getr regs 3 = w64 (as_gp B)) by (apply (vr_rv_get regs _ 3 _ Hrv); apply in_or_app; left; unfold vr_base; vr05_inl).
assert (R4 : getr regs 4 = w64 (as_tp B)) by (apply (vr_rv_get regs _ 4 _ Hrv); apply in_or_app; left; unfold vr_base; vr05_inl).
assert (R8 : getr regs 8 = w64 (vr_sp0 e)) by (apply (vr_rv_get regs _ 8 _ Hrv); apply in_or_app; left; unfold vr_base; vr05_inl).
assert (Hsp1 : spZ regs = vr_s1 e) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* the frame chain at the call: s0 = sp0, verbs_receive's frame pointer: achain_push
   on afn_pre's chain with the prologue's saves of ra and the entry s0 (the kit's vr_chain_at) *)
destruct (vr_chain_at B MT RRO RPG RECC PROGU ROA e lyc Sc W mem md k pos regs He HJ Hsv R8) as (ch1 & Hch1).
eapply SRr_mono.
{ apply (cl_callSF B LAWS W regs mem (Z_to_bv 64 (BASE + AF_sup_resp)) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e)
    (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc md k SUP_RESP_STK [] EV_SUP_RESP (vr_s1 e - vr_sp0 e)
    (w64 (BASE + 29696)) ch1 (vr05_resp_post (-902) lyc Sc W mem) HJ).
  - rewrite Hsp1. lia.
  - exact Hs2b.
  - lia.
  - exact Hs2e.
  - exact Hs2d.
  - exact R3.
  - exact R4.
  - exact R1.
  - unfold w64. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold w64. rewrite unsigned_lit_small by lia. lia.
  - replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) by lia. exact Hch1.
  - intros HPRE1. eapply SRr_mono.
    { exact (TSUP_RESP fx lyc Sc W regs mem md ch1 (-902) HPRE1 Hfrm Hfrs8 Haro Hro R10 ltac:(lia) Hev1 Hlv1 Hmo1). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HR' & HC' & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. rewrite R1. split; [reflexivity|]. split; [exact HR'|].
    split; [exact HC'|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a (r & [] & _). }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJc & HP2 & HK).
destruct HK as (tq & Htq10 & Htq & Hpq & Hap & Hin & Hstr & Hrectr & Hbb & Hmo).
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
exists fx', tq, ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact Hfx|]. split; [lia|].
split; [rewrite Hxv; exact Hstr|].
apply (vr05_call_post e pos F q c lyc Sc W regs mem md k nm _ ly2 S2 W2 regs2 mem2 md2 tq ((10, tq) :: rlk)
  He Htk HC Hline HJ2 HJc Hpq Hrectr Hmo).
apply vr_rv_intro. intros r v Hin'. apply in_app_or in Hin' as [Hin' | [Hin' | Hin']].
- assert (Hr : acallee_saved r).
  { unfold vr_base in Hin'. cbn in Hin'. destruct Hin' as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _;
    unfold acallee_saved; lia. }
  rewrite (HP2 r Hr). apply (vr_rv_get regs _ _ _ Hrv). apply in_or_app. left. exact Hin'.
- injection Hin' as <- <-. exact Htq10.
- assert (Hr : acallee_saved r).
  { rewrite Forall_forall in Hcs. pose proof (Hcs (r, v) Hin') as Hrr. cbn [fst] in Hrr. unfold acallee_saved. lia. }
  rewrite (HP2 r Hr). apply (vr_rv_get regs _ _ _ Hrv). apply in_or_app. right. right. right. exact Hin'.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   S05: the seed at 0x8d8cc, the run through the check and the load of the sender to sup_resp's entry *)
Lemma vr_s05 : vr_s05_stmt B MT.
Proof.
intros e W cf He Hb.
destruct Hb as (pos & F & q & c & lyc & Sc & regsc & memc & mdc & k & nm & Hcf & Htk & Hcore & Hline & Hfc).
destruct (vr05_ent_facts e He)
  as (HPRE & HREC0 & Hn8 & HDn & Hev & Hlive & Hmok & Hfrs4 & Hcalls0 & Hperm0 & HOBJ & Hfd & Hfrm).
pose proof HPRE as (HAR0 & _).
pose proof Hcore as (HJ & _ & _ & _ & _ & HR & _).
unfold vr_rl4e, vr_rl2 in HR.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HOincl : forall pn, In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e)))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ HREC0 Hpn)).
pose proof HOBJ as ((cidm & posm & Hinm & Hcidm & Halm & Hlom & Hhim) & Hmod8 & HRA0).
assert (HMSG : forall a, e_msg e <= a < e_msg e + 24 \/ (exists i, 0 <= i < 3 /\ a = shadow_addr (e_msg e) + i) ->
  rdW W memc a = rdW (e_W e) (e_mem e) a).
{ intros a Ha. exact (vr05_caller_kept e [(4, pos)] lyc Sc W memc mdc k a HJ HAR0 HOBJ HOincl Ha). }
assert (HRA : range_addressable (rdW W memc) SHADOW_OFF (e_msg e) 24).
{ intros x Hx. destruct (HRA0 x Hx) as (cc & Hc & Hor). exists cc. split; [|exact Hor].
  replace x with (e_msg e + (x - e_msg e)) by lia.
  rewrite (shadow_of_addr_aligned_off SHADOW_OFF (e_msg e) (x - e_msg e) Hmod8).
  rewrite HMSG.
  - rewrite <- (shadow_of_addr_aligned_off SHADOW_OFF (e_msg e) (x - e_msg e) Hmod8).
    replace (e_msg e + (x - e_msg e)) with x by lia. exact Hc.
  - right. exists ((x - e_msg e) / 8). split; [|unfold shadow_addr, shadow_of_addr; reflexivity].
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cidm posm HAR0 Hinm) as (Hfm0 & Hfmc & Hfmapp).
pose proof (fs_frame_bytes_nonneg cidm) as Hfmb.
set (fd32 := e_fd e mod 2 ^ 32).
assert (Hfd32 : 0 <= fd32 < 2 ^ 32) by (unfold fd32; apply Z.mod_pos_bound; lia).
assert (Hfd1 : aval_mem (rdW W memc) (e_msg e) 4 fd32).
{ intros kx Hkx. rewrite HMSG by (left; lia). exact (vr05_aval_mod _ _ _ Hfd kx Hkx). }
(* the registers at 0x8d8cc *)
assert (R19 : getr regsc (Z_to_bv 5 19) = w64 SHADOW_OFF) by (apply (vr_rv_get regsc _ 19 _ HR); unfold vr_base; vr05_inl).
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 (e_msg e / 8)) by (apply (vr_rv_get regsc _ 22 _ HR); unfold vr_base; vr05_inl).
assert (R24 : getr regsc (Z_to_bv 5 24) = w64 (e_msg e)) by (apply (vr_rv_get regsc _ 24 _ HR); unfold vr_base; vr05_inl).
assert (Hmsg : 4096 <= e_msg e /\ e_msg e + 24 <= alloc_ceiling) by lia.
(* the environment: the registers, then the sender word *)
remember (Eimg (Ereg regsc [w64 fd32])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc [w64 fd32]) E) by (subst E; apply vr_env_agree).
assert (E32 : ew E 32 = w64 fd32) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (E19 : ew E 19 = w64 SHADOW_OFF)
  by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 19 (Z_to_bv 5 19) eq_refl); exact R19).
assert (E24 : ew E 24 = w64 (e_msg e))
  by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 24 (Z_to_bv 5 24) eq_refl); exact R24).
assert (HROK : YP0l.regs_ok E (sr_set sr_atoms (Z_to_bv 5 22) (SAlu ALU_SRL (SOff 24 0) (SLit 3))) regsc).
{ apply vr05_regs_ok_set; [subst E; apply regs_ok_Eimg_Ereg|].
  rewrite R22. cbn [sv_denot]. rewrite E24. unfold w64.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. rewrite zalu64_sound. f_equal.
  unfold zalu64, zalu_raw, zcanon, M64.
  rewrite (Z.mod_small (e_msg e)) by lia. change (Z.land (3 mod 2 ^ 64) 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
clear HE.
assert (HS : st_ok_pi SEGS VAL E vr05_ss
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 29672)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold vr05_ss. apply pa_entry_st_ok_full.
  - exact HROK.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vr05_msg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E24. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (e_msg e) 0 4 (SOff 32 0) fd32).
    + cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
    + cbn. lia.
    + rewrite Z.add_0_r. exact (vr_val_mem_of_aval W memc (e_msg e) 4 fd32 Hfd1).
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite E19, E24. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; zlia).
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite Z.mod_1_r.
    split; [split; [lia | split; [reflexivity | lia]]|]. split; [|exact I].
    split; [zlia|]. split; [exact Hmod8 | lia]. }
assert (SHOK : sh_ok SEGS vr05_Bx vr05_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, vr05_SH. apply Forall_cons; [|apply Forall_nil]. split.
  - unfold U, vr05_Bx. cbn [sv_denot she_m she_lo she_hi]. rewrite E19, E24, !Z.add_0_r. unfold w64.
    rewrite !Z_to_bv_bv_unsigned, !unsigned_lit_small by (unfold SHADOW_OFF; zlia).
    replace (e_msg e + 0) with (e_msg e) by lia. replace (24 - 0) with 24 by lia. exact HRA.
  - intros a Ha Hband. unfold U, vr05_Bx in *. cbn [sv_denot she_m she_lo she_hi] in *.
    rewrite E19, E24, !Z.add_0_r in *. unfold w64 in *.
    rewrite !Z_to_bv_bv_unsigned, !unsigned_lit_small in * by (unfold SHADOW_OFF; zlia).
    unfold SHADOW_OFF in Hband. zlia. }
subst cf. unfold cfg_at, w64.
replace (vr_pc 0x8d8cc) with (BASE + 29672) by (unfold vr_pc, AF_verbs_receive; lia).
(* add s3,s6,s3; lb a0,0(s3); bnez a0,0x8ded8; lw s7,0(s8); li a0,-902; jal sup_resp *)
paj_run_tok RUN HS HJ SHOK vr05_Bspan; [awr_ok_tac |].
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
assert (Eq : forall a, rdW W (ms_mem ms) a = rdW W memc a).
{ apply (vr_rdW_frame E _ W memc (ms_mem ms) HFr). apply vr_no_wrange. exact vr05_ro. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. rewrite ?vr05_m902 in Q10.
pose proof (vr_kept_regs E _ _ regsc _ [2; 3; 4; 8; 9; 20; 21; 25; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
assert (Hrv : vr_rv (ms_regs ms) (vr_base B e ++ (1, BASE + 29696) :: (10, -902) :: vr05_rlk F q))
  by (unfold vr05_rlk; vr05_regs KR HR).
pose proof (MOVE e pos F _ vr_sh2 (vr_sl2 F c) _ _ (e_O e) (e_q0 e) k _ nm _ lyc Sc W regsc memc mdc
  (vr_sl2 F c) _ 2 VR_NM_PRE (ms_regs ms) (ms_mem ms) mdv Hcore HJ Eq Hrv
  (incl_refl _) (Z.le_refl _) (Z.le_refl _)) as Hcore1.
rewrite (SIGP CS_sup_resp ltac:(unfold cmd_prog_syms; vr05_inl)).
change (cmd_af CS_sup_resp) with AF_sup_resp.
eapply SRr_bind.
{ exact (vr05_resp_call e pos F q c lyc Sc W (ms_regs ms) (ms_mem ms) mdv k nm (vr05_rlk F q) He Htk Hcore1
    (vr_line_eq B e q W memc (ms_mem ms) Eq Hline) ltac:(unfold vr05_rlk; vr05_fa)). }
intros W2 c2 _ (fx' & tq & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfx & Htq4 & Hstr & Hcore2 & Hline2).
(* the rest of the walk at the FP state sup_resp returned (the continuation section above, at fx') *)
eapply SRr_mono.
{ exact (vr05_p2 (fx := fx') B MT TREPLY HB MTL SIGP RRO RPG RECC PROGU ROA e W2 regs2 mem2 md2 pos F q c tq ly2 S2
    (k + EV_SUP_RESP) (nm + 1) (vr05_ent_at (fx := fx') fx B MT e He (fxrel_frm0 fx fx' Hfrm Hfx)) Htk Hcore2
    Hline2 Hfc Htq4 Hstr). }
intros W' cf' _ H. exists fx'. split; [exact Hfx | exact H].
Qed.

End e.
End f.
End d.
