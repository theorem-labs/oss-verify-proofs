(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S17 POOL (0x8d598-0x8d5cc, 14 instructions) of the walk of verbs_receive
   on the ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v vr_s17_stmt):
     li a0,3; bne s5,a0,0x8d68c; li a0,-9; ld s3,40(s1); bltu a0,s3,0x8d938; li a0,-17; bltu a0,s3,0x8d938;
     ld s9,8(s3); ld a0,16(s3); jal atoi; mv a1,a0; mv a0,s9; jal sup_pool_config; j 0x8d4cc.
   With ntok <> 3 the step is reject and the run stops at the refusal stub 0x8d68c (vr_pr). With ntok = 3 the run
   reloads tok = F+32 from the spill slot s1+40, passes UBSan's two checks of tok + 8 and tok + 16 (none taken: tok
   lies in the side-stack frame, below alloc_ceiling, vr_tok_chk), calls the atoi wrapper on tok[2] (a Theorem Labs lane's
   aatoi_realizes through PaArt.aj_art_at: the wrapper writes its window below s1 and the errno cell,
   verbs_receive_s17_x.v carries the boundary facts across), then sup_pool_config(tok[1], atoi_a tok[2])
   (sup_pool_config_c.v) through the call arm vr_call_arm_hd (verbs_receive_s18_arm.v), and jumps to the join
   0x8d4cc (vr_hd, at the FP state the callee returns at). The B twin of the A walk's verbs_receive_s17.v
   (a working branch), whose arm was the A walk's S14 kit; here it is the S18 arm. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_pool_config_c sup_reply_code_c xmalloc_c arg_s_c record_c answer_c hand_back_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
verbs_receive_s18_kit verbs_receive_s18_call verbs_receive_s18_arm verbs_receive_s17_x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the listing offsets of the segment (B entry 0x8ce4c = listing AF_verbs_receive) *)
Definition S17_PC : Z := AF_verbs_receive + 0x74c.   (* 0x8d598 li a0,3 *)
Definition S17_PR : Z := AF_verbs_receive + 0x840.   (* 0x8d68c li a0,-902 *)
Definition S17_RA : Z := AF_verbs_receive + 0x774.   (* 0x8d5c0 mv a1,a0: the atoi wrapper's return *)

(* the dispatch refuses pool_config with other than two arguments *)
Lemma vr_st_pool_rej : forall D, VRR.route (Verbs.toks D) = VRR.RPool -> Verbs.toks D <> [] ->
  vr_ntok D <> 3 -> vr_st D = Verbs.SResp (-902).
Proof.
intros D Hr Hne Hn. destruct (Verbs.toks D) as [|v args] eqn:Ht; [congruence|].
rewrite (vr_st_route D v args Ht), Hr. cbn [VRR.plan_at].
unfold vr_ntok in Hn. rewrite Ht in Hn. cbn [length] in Hn.
destruct args as [|a1 [|a2 [|a3 args]]]; try reflexivity. cbn [length] in Hn. lia.
Qed.
Lemma vr_k1_pool_rej : forall R D, VRR.route (Verbs.toks D) = VRR.RPool -> Verbs.toks D <> [] ->
  vr_ntok D <> 3 -> vr_k1 R D = 2 + EV_SUP_RESP.
Proof.
intros R D Hr Hne Hn. pose proof (vr_st_pool_rej D Hr Hne Hn) as Hst.
destruct (Verbs.toks D) as [|v args] eqn:Ht; [congruence|].
pose proof (vr_route_pool v args Hr) as Hv. subst v.
rewrite (vr_k1_simple R D _ args Ht) by (vm_compute; reflexivity). rewrite Hst. reflexivity.
Qed.
(* with two arguments the dispatch calls sup_pool_config(tok[1], atoi(tok[2])), atoi the ASan wrapper's *)
Lemma vr_pool_call : forall R D a b, Verbs.toks D = [Verbs.Lit.verb_pool_config; a; b] ->
  vr_h R D = (sup_pool_config_m R (Some a) (atoi_a b), false) /\ vr_k1 R D = 2 + EV_SUP_POOL_CONFIG R.
Proof.
intros R D a b T.
assert (St : vr_st D = Verbs.SCall (Verbs.sup_pool_config a (atoi_a b))).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. reflexivity. }
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
(* the callee's contract and the atoi entry at every FP state (verbs_receive_c.v:250, :277) and the record facts *)
Hypothesis TSUP_POOL_CONFIG : forall fx0 : YK11.FPState, @tsup_pool_config_spec fx0 rc SK PI B MT.
Hypothesis AATOI : forall fx0 : YK11.FPState,
  @RtNumber.aatoi_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Hypothesis HB : YF0m.CmdBSyms B.
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
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).
Let ART := aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL).

(* S17 with other than three words: `li a0,3; bne s5,a0,0x8d68c` to the refusal stub 0x8d68c *)
Lemma vr_s17_pr : forall e (W : world SEGS) pos F q c tp lyc Sc regsc memc mdc k nm,
  vr_ent B MT e ->
  VRR.route (Verbs.toks (e_D e)) = VRR.RPool -> Verbs.toks (e_D e) <> [] ->
  vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_rt e F q (hd 0 tp))
    (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
  vr_line B e q W memc -> vr_copy B e F c tp W memc ->
  vr_ntok (e_D e) <> 3 ->
  SRr SEGS W (cfg_at SEGS (vr_pc 0x8d598) regsc memc mdc) (vr_pr B MT e 0x8d68c).
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm He Hroute Hne HC HL HCP Hnt.
pose proof HC as (HJ & Hk & HM & Hnm & HFR & HRV & HSV & HSP & HENV & HREC & HnD & HPERM & HQ).
assert (RG : forall r v, In (r, v) (vr_base B e ++ vr_rl_rt e F q (hd 0 tp)) -> getr regsc (Z_to_bv 5 r) = w64 v)
  by (intros r v Hin; exact (vr_rv_in _ _ _ _ HRV Hin)).
unfold vr_base, vr_rl_rt in RG. cbn [app] in RG.
pose proof (RG 21 (vr_ntok (e_D e)) ltac:(vr_in)) as R21.
pose proof (vr_seed0 W regsc memc S17_PC) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc []))) by apply Eimg_env.
replace (cfg_at SEGS (vr_pc 0x8d598) regsc memc mdc)
  with (mkCfg (mkst regsc (Z_to_bv 64 (BASE + S17_PC)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, vr_pc, S17_PC; f_equal; f_equal; f_equal; lia).
(* 0x8d598 li a0,3 *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
vr_unchanged (@pa_segs _ cmd_listing PI) UN1 HFr. clear HF HFr HG.
assert (Hntr : 0 <= vr_ntok (e_D e) < 2 ^ 64).
{ unfold vr_ntok. pose proof (Verbs.toks_length (e_D e)). lia. }
(* 0x8d59c bne s5,a0,0x8d68c: taken *)
psrr_branch_pi RUNP BR HS;
  rewrite branch_ne_U, (vr_U_SOff_reg regsc [] 21 _ ltac:(lia) R21 Hntr), vr_U_lit in Hc by lia.
2: { exfalso. apply negb_false_iff, Z.eqb_eq in Hc. lia. }
paj_run_to_sh RUNTOP HS HJ S17_PR.
{ vr_awr. }
set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
vr_unchanged (@pa_segs _ cmd_listing PI) UN2 HFr. clear HF HFr HG.
pmkst HS.
apply SRr_ret.
exists (-902), (e_R e), (e_O e), pos, F, q, c, tp, lyc, Sc, (ms_regs ms0), (ms_mem ms0), mdv2, k, nm.
split; [unfold cfg_at, w64, vr_pc; f_equal; f_equal; f_equal; unfold S17_PR, AF_verbs_receive; lia|].
split; [intros _; reflexivity|].
split; [lia|].
split; [unfold vr_h; rewrite (vr_st_pool_rej _ Hroute Hne Hnt); reflexivity|].
split; [exact Hne|].
split; [unfold vr_pr_ntok; cbn -[length Verbs.toks]; destruct (Verbs.toks (e_D e)); [congruence | cbn; lia]|].
assert (RS : rd_same (rdW W memc) (rdW W (ms_mem ms0))).
{ apply vr_rd_same_of. intros a Ha. rewrite (UN2 a Ha (fun x => x)). exact (UN1 a Ha (fun x => x)). }
split; [|split; [exact (vr_line_same B e q W W memc _ RS HL) | exact (vr_copy_same B e F c tp W W memc _ RS HCP)]].
apply (vr_core_same B MT e pos F _ _ _ _ _ _ _ _ k 2 _ nm VR_NM_PRE _ lyc Sc W regsc memc mdc _ _ _ HC HJ RS).
- replace (vr_rl_pr e F q c 0x8d68c (-902))
    with [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)] by reflexivity.
  unfold vr_rv, vr_base. cbn [app].
  repeat (apply Forall_cons; [cbn [fst snd]; vr_sreg HS; rewrite vr_ew_reg by lia; apply RG; vr_in |]).
  apply Forall_nil.
- rewrite (vr_k1_pool_rej _ _ Hroute Hne Hnt). lia.
- unfold VR_NM_PRE, VR_NM_PR in *. lia.
Qed.

(* S17 with three words: the two UBSan checks on tok, atoi(tok[2]), then sup_pool_config(tok[1], its value) and
   `j 0x8d4cc` (vr_hd at 0x8d4cc) *)
Lemma vr_s17_call : forall e (W : world SEGS) pos F q c tp lyc Sc regsc memc mdc k nm a b,
  vr_ent B MT e ->
  Verbs.toks (e_D e) = [Verbs.Lit.verb_pool_config; a; b] ->
  vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_rt e F q (hd 0 tp))
    (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
  vr_line B e q W memc -> vr_copy B e F c tp W memc ->
  SRr SEGS W (cfg_at SEGS (vr_pc 0x8d598) regsc memc mdc)
    (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\ vr_hd (fx := fq) B MT e 0x8d4cc W' cf').
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm a b He Ht HC HL HCP.
pose proof HC as (HJ & Hk & HM & Hnm & HFR & HRV & HSV & HSP & HENV & HREC & HnD & HPERM & HQ).
pose proof He as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & HlenD & _ & _ & _ & _ & _ & Hcalls & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H470 & _).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
destruct (vr_ent_stk B MT e He) as (Hs1lo & Hs1sp & Hs1al & Hsp47 & Hsp16 & HspS).
pose proof asan_consts as (CR & _).
pose proof (proj1 HJ) as HAR.
pose proof HFR as (EF & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
assert (Hlen3 : length (Verbs.toks (e_D e)) = 3%nat) by (rewrite Ht; reflexivity).
assert (Hnt3 : vr_ntok (e_D e) = 3) by (unfold vr_ntok; rewrite Hlen3; reflexivity).
assert (HlenP : length tp = 3%nat) by (destruct HCP as (_ & (_ & HlenP & _)); rewrite HlenP, Hlen3; reflexivity).
destruct tp as [|p0 [|p1 [|p2 [|p3 tp']]]]; cbn in HlenP; try lia. clear HlenP.
destruct (vr_tok_blk B e F q c [p0; p1; p2] lyc Sc W memc mdc 1 p1 a HAR HPERM HCP eq_refl
  ltac:(rewrite Ht; reflexivity)) as (_ & _ & Hlmax1 & _ & Hp1m & Hp14 & Hp1c).
destruct (vr_tok_blk B e F q c [p0; p1; p2] lyc Sc W memc mdc 2 p2 b HAR HPERM HCP eq_refl
  ltac:(rewrite Ht; reflexivity)) as (_ & _ & Hlmax2 & _ & Hp2m & Hp24 & Hp2c).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)) by exact (vr_tmp_live B e lyc Sc (e_O e) _ (vr_cb e c) HPERM ltac:(vr_in)).
assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc)) by exact (vr_tmp_live B e lyc Sc (e_O e) _ (vr_lb e q) HPERM ltac:(vr_in)).
assert (RG : forall r v, In (r, v) (vr_base B e ++ vr_rl_rt e F q p0) -> getr regsc (Z_to_bv 5 r) = w64 v)
  by (intros r v Hin; exact (vr_rv_in _ _ _ _ HRV Hin)).
unfold vr_base, vr_rl_rt in RG. cbn [app] in RG.
pose proof (RG 9 (vr_s1 e) ltac:(vr_in)) as R9.
pose proof (RG 21 (vr_ntok (e_D e)) ltac:(vr_in)) as R21.
pose proof (RG 22 F ltac:(vr_in)) as R22.
pose proof (vr_spill_in e W memc _ 40 (F + 32) HSP ltac:(unfold vr_sl3; vr_in)) as HSl.
pose proof (vr_seed_tk2 W regsc memc S17_PC (vr_s1 e) F p1 p2 R9 R22 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) HSl
  ltac:(replace (F + 40) with (F + 32 + 8 * Z.of_nat 1) by lia; exact Hp1m)
  ltac:(replace (F + 48) with (F + 32 + 8 * Z.of_nat 2) by lia; exact Hp2m)) as HS.
set (E := Eimg (Ereg regsc [Z_to_bv 64 p1; Z_to_bv 64 p2])) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regsc [Z_to_bv 64 p1; Z_to_bv 64 p2]) E) by apply vr_env_agree_Eimg.
assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e))) by (unfold E; rewrite vr_ew_reg by lia; exact R21).
assert (E22 : bv_unsigned (ew E 22) = F) by (unfold E; apply vr_U_reg; [lia | exact R22 | lia]).
assert (E32 : ew E 32 = Z_to_bv 64 p1) by exact (vr_ew_extra regsc _ 0 ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 p2) by exact (vr_ew_extra regsc _ 1 ltac:(lia)).
clearbody E.
assert (Hro : Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) [vr_rsl; vr_rtk2])
  by (apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia | apply Forall_nil]).
replace (cfg_at SEGS (vr_pc 0x8d598) regsc memc mdc)
  with (mkCfg (mkst regsc (Z_to_bv 64 (BASE + S17_PC)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, vr_pc, S17_PC; f_equal; f_equal; f_equal; lia).
(* 0x8d598 li a0,3 *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
pose proof (vr_rdeq_of_frame E [vr_rsl; vr_rtk2] (w_H W) memc (ms_mem ms) HFr Hro) as RS1. clear HF HFr HG.
(* 0x8d59c bne s5,a0,0x8d68c: not taken *)
psrr_branch_pi RUNP BR HS; rewrite branch_ne_U, (U_atom E 21 _ E21), vr_U_lit in Hc by lia.
1: { exfalso. apply negb_true_iff, Z.eqb_neq in Hc. lia. }
(* 0x8d5a0 li a0,-9; 0x8d5a4 ld s3,40(s1) *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
pose proof (vr_rdeq_of_frame E [vr_rsl; vr_rtk2] (w_H W) (ms_mem ms) (ms_mem ms0) HFr Hro) as RS2. clear HF HFr HG.
(* 0x8d5a8 bltu a0,s3,0x8d938 (tok + 8 wraps): not taken *)
psrr_branch_pi RUNP BR HS.
1: { vr_trap E22. }
(* 0x8d5ac li a0,-17 *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mat1 mdv2) in *. clearbody mdv3.
pose proof (vr_rdeq_of_frame E [vr_rsl; vr_rtk2] (w_H W) (ms_mem ms0) (ms_mem ms1) HFr Hro) as RS3. clear HF HFr HG.
(* 0x8d5b0 bltu a0,s3,0x8d938 (tok + 16 wraps): not taken *)
psrr_branch_pi RUNP BR HS.
1: { vr_trap E22. }
(* 0x8d5b4 ld s9,8(s3); 0x8d5b8 ld a0,16(s3); 0x8d5bc jal atoi *)
paj_run_shc RUNP RUNC HS HJ.
{ vr_awr. }
set (mdv4 := with_vm_backing (m_vm_lazy mdv3) mat2 mdv3) in *. clearbody mdv4.
pose proof (vr_rdeq_of_frame E [vr_rsl; vr_rtk2] (w_H W) (ms_mem ms1) (ms_mem ms2) HFr Hro) as RS4. clear HF HFr HG.
assert (RS : rd_same (rdW W memc) (rdW W (ms_mem ms2))).
{ intros x. rewrite (RS4 x), (RS3 x), (RS2 x). exact (RS1 x). }
clear RS1 RS2 RS3 RS4.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (25%bv : bv 5) Q25.
prreg HS (19%bv : bv 5) Q19.
rewrite E33 in Q10. rewrite E32 in Q25. rewrite E22 in Q19.
pose proof (vr_kept_regs E _ _ regsc [Z_to_bv 64 p1; Z_to_bv 64 p2]
  [2; 3; 4; 8; 9; 18; 21; 22; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
pmkst HS.
assert (Q2 : getr (ms_regs ms2) 2 = w64 (vr_s1 e)).
{ etransitivity; [exact (KR 2 ltac:(cbn; tauto))|]. apply RG. vr_in. }
assert (Q3 : getr (ms_regs ms2) 3 = w64 (as_gp B)).
{ etransitivity; [exact (KR 3 ltac:(cbn; tauto))|]. apply RG. vr_in. }
assert (Q4 : getr (ms_regs ms2) 4 = w64 (as_tp B)).
{ etransitivity; [exact (KR 4 ltac:(cbn; tauto))|]. apply RG. vr_in. }
assert (Qsp : spZ (ms_regs ms2) = vr_sp0 e + (vr_s1 e - vr_sp0 e)).
{ unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hra : YK0s.ret_ok (getr (ms_regs ms2) 1))
  by (rewrite Q1; apply ret_ok_codeptr_v; first [lia | reflexivity | vm_compute; reflexivity]).
pose proof (proj1 HJ) as HAR1.
pose proof (vr_env_of_journal B MT RRO RPG RECC ROA e _ _ _ _ _ _ _ He HJ) as (HRO1 & _ & _ & Hgd1 & Hfl1 & (ev & Herr1)).
pose proof (vr_copy_same B e F c [p0; p1; p2] W W memc (ms_mem ms2) RS HCP) as HcopyA.
pose proof HcopyA as (_ & (_ & _ & _ & HwA)).
destruct (HwA 2%nat p2 b eq_refl ltac:(rewrite Ht; reflexivity)) as (A1 & A2 & A3 & A4).
destruct (vr_o_facts e Hal16) as [Hs1o Ho].
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
assert (HES : ESTACK = ltac:(let v := eval vm_compute in ESTACK in exact v)) by reflexivity.
pose proof (ecall_pre_stk_at SEGS B (3 * ESTACK) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e)
  (e_mem e) (e_md e) [(4, pos)] lyc Sc W (ms_mem ms2) mdv4 k (ms_regs ms2) (vr_s1 e - vr_sp0 e) HJ Qsp Hs1o
  ltac:(lia) ltac:(lia) ltac:(lia) Hra Q3 Q4) as HPRE1.
(* the atoi wrapper on tok[2] *)
eapply SRr_bind.
{ eapply (ART (3 * ESTACK) (aerrno_cell B) _ W (ms_regs ms2) (ms_mem ms2) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e)
    (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdv4 k (vr_s1 e - vr_sp0 e) _ _ HJ);
    [exact Qsp | exact Hs1o | lia | lia | lia | exact Q1 | intros a0 Ha0; exact Ha0 |].
  apply (AATOI fx lyc Sc W (ms_regs ms2) (ms_mem ms2) mdv4 p2 b ev Hfl1 Hgd1 HPRE1 Q10 ltac:(lia)).
  - apply astr_atR_view. exact A1.
  - apply (aread_ok_of_block SEGS B LAWS (3 * ESTACK) lyc Sc W (ms_regs ms2) (ms_mem ms2) mdv4 c
      (Z.of_nat (length (Verbs.line (e_D e))) + 1) p2 (astr_len b + 1) HAR1 Hcb); unfold astr_len; [lia | lia | lia |].
    rewrite Qsp. lia.
  - apply (amem8_of_blockA SEGS B LAWS lyc Sc W (ms_mem ms2) mdv4); [exact HAR1 | | unfold astr_len; lia].
    exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1). split; [exact Hcb | unfold astr_len; lia].
  - unfold astr_len. apply (BLKT lyc Sc W (ms_mem ms2) mdv4 c (Z.of_nat (length (Verbs.line (e_D e))) + 1));
      [exact HAR1 | exact Hcb | lia].
  - exact Herr1.
  - (* tok[2] apart from the errno cell: its bytes are in the copy block, not image bytes (blk_img); the errno
       cell's are (api_env) *)
    pose proof (pal_env B TL) as (_ & Hzi & _).
    destruct (Z_le_gt_dec (p2 + astr_len b + 1) (as_errno B)) as [Hz1|Hz1]; [left; exact Hz1|].
    destruct (Z_le_gt_dec (as_errno B + 4) p2) as [Hz2|Hz2]; [right; exact Hz2|]. exfalso.
    apply (blk_img SEGS B LAWS lyc Sc W (ms_mem ms2) mdv4 c (Z.of_nat (length (Verbs.line (e_D e))) + 1)
      (Z.max p2 (as_errno B)) HAR1 Hcb); [| apply Hzi; clear - Hz1 Hz2; lia].
    unfold req_size. destruct (Z.eqb_spec (Z.of_nat (length (Verbs.line (e_D e))) + 1) 0) as [Hzk|Hzk]; cbv iota;
      clear - A3 A4 Hz1 Hzk; unfold astr_len in Hz1; lia.
  - exact (vr_rtrom_ok B W (ms_mem ms2) HRO1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HA0 & _) & HK2).
(* 0x8d5c0 mv a1,a0; 0x8d5c4 mv a0,s9; 0x8d5c8 jal sup_pool_config, from a state that names only the registers *)
pose proof (vr_seed0 W regs2 mem2 0x7090) as HS2.
set (E2 := Eimg (Ereg regs2 [])) in HS2.
assert (HEI2 : img_env VAL A_LIM E2) by apply Eimg_env.
assert (HAE2 : env_agree 32 (Ereg regs2 []) E2) by apply vr_env_agree_Eimg.
assert (E2_10 : ew E2 10 = getr regs2 (Z_to_bv 5 10)) by (unfold E2; apply vr_ew_reg; lia).
assert (E2_25 : ew E2 25 = getr regs2 (Z_to_bv 5 25)) by (unfold E2; apply vr_ew_reg; lia).
clearbody E2.
paj_run_shc RUNP RUNC HS2 HJ2.
{ vr_awr. }
match goal with |- context [with_vm_backing (m_vm_lazy md2) ?mt md2] =>
  set (mdv5 := with_vm_backing (m_vm_lazy md2) mt md2) in * end.
clearbody mdv5.
pose proof (vr_rdeq_of_frame E2 [] (w_H W) mem2 (ms_mem ms3) HFr (Forall_nil _)) as RS5. clear HF HFr HG.
prreg HS2 (1%bv : bv 5) Q1b. prreg HS2 (10%bv : bv 5) Q10b. prreg HS2 (11%bv : bv 5) Q11b.
rewrite E2_25 in Q10b. rewrite E2_10 in Q11b.
pose proof (vr_kept_regs E2 _ _ regs2 [] [2; 3; 4; 8; 9; 18; 19; 21; 22; 25; 27] HS2 HAE2
  ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
pmkst HS2.
rewrite (SIGP CS_sup_pool_config) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_sup_pool_config) with AF_sup_pool_config.
assert (KRall : forall r, In r [2; 3; 4; 8; 9; 18; 21; 22; 27] ->
  getr (ms_regs ms3) (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)).
{ intros r0 Hr0.
  rewrite (KR2 r0 ltac:(cbn in Hr0 |- *; tauto)).
  rewrite (HP2 r0 ltac:(unfold acallee_saved; cbn in Hr0; lia)).
  exact (KR r0 Hr0). }
assert (P19 : getr (ms_regs ms3) (Z_to_bv 5 19) = w64 (F + 32)).
{ rewrite (KR2 19 ltac:(cbn; tauto)). rewrite (HP2 19 ltac:(unfold acallee_saved; lia)). exact Q19. }
assert (P10 : getr (ms_regs ms3) 10 = w64 p1).
{ etransitivity; [exact Q10b|]. rewrite (HP2 25 ltac:(unfold acallee_saved; lia)). exact Q25. }
assert (P11 : getr (ms_regs ms3) 11 = w64 (atoi_a b)).
{ etransitivity; [exact Q11b|]. exact HA0. }
assert (KX : v17_kx B e W memc (ms_mem ms3)).
{ intros a0 Ha0 Hb Hn. rewrite (RS5 a0), (HK2 a0 Ha0); [exact (RS a0) | | exact Hn]. lia. }
assert (Hsl : Forall (fun ov => 0 <= fst ov <= 200) (vr_sl3 F q c))
  by (unfold vr_sl3; repeat constructor; cbn [fst]; lia).
set (rk := [(19, F + 32); (18, q); (22, F); (27, shadow_addr F + 4)]).
assert (Hrv1 : vr_rv (ms_regs ms3) (vr_base B e ++ (1, BASE + 0x709c) :: rk)).
{ apply vr_rv_mk. intros r0 v Hin. apply in_app_or in Hin as [Hin|Hin].
  - unfold vr_base in Hin. cbn [In] in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
    rewrite KRall by (cbn; tauto); apply RG; vr_in.
  - unfold rk in Hin. cbn [In] in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
    first [exact Q1b | exact P19 | rewrite KRall by (cbn; tauto); apply RG; vr_in]. }
pose proof (v17_core_kx B MT RRO RPG RECC ROA PROGU TL e pos F _ _ _ _ _ _ _ _ k _ nm _ lyc Sc W regsc memc mdc
  (ms_regs ms3) (ms_mem ms3) mdv5 He HC HJ2 KX Hsl Hrv1) as Hcore1.
pose proof (v17_line_kx B MT TL e q lyc Sc W memc mdc (ms_mem ms3) He HAR Hlb HL KX) as Hline1.
pose proof (v17_copy_kx B TL e F c [p0; p1; p2] pos lyc Sc W memc mdc (ms_mem ms3) HAR Hin4 EF Hcb HCP KX) as Hcopy1.
assert (Hcs : vr_cs B MT e pos F q c 0x709c rk [p0; p1; p2] lyc Sc W (ms_regs ms3) (ms_mem ms3) mdv5 k nm)
  by (split; [exact Hcore1 | split; [exact Hline1 | exact Hcopy1]]).
destruct (vr_tok_blk B e F q c [p0; p1; p2] lyc Sc W (ms_mem ms3) mdv5 1 p1 a (proj1 HJ2) HPERM Hcopy1 eq_refl
  ltac:(rewrite Ht; reflexivity)) as (Hblk1 & Hstr1 & _ & Hap1 & _).
destruct (vr_pool_call (e_R e) (e_D e) a b Ht) as [Hvh Hk1].
set (m := sup_pool_config_m (e_R e) (Some a) (atoi_a b)) in *.
assert (Hid : -2 ^ 31 <= atoi_a b < 2 ^ 31) by (unfold atoi_a; apply v17_swrap32_range).
assert (Ht28 : (length (snd m) <= 28)%nat).
{ unfold m, sup_pool_config_m, daemon_shape. apply vr_stub_len. exact (vr_rec_code_range B _ _ _ _ _ HREC). }
pose proof (dec_length (atoi_a b) Hid) as Hd.
assert (Hntok : vr_hd_ntok 0x8d4cc (length (Verbs.toks (e_D e)))) by (unfold vr_hd_ntok; rewrite Hlen3; cbn; lia).
assert (Hrl : forall tq, vr_rl_hd e F q c 0x8d4cc tq = (10, tq) :: rk) by (intros tq; reflexivity).
assert (Hrk : Forall (fun rv => acallee_saved (fst rv)) rk)
  by (unfold rk; repeat (apply Forall_cons; [unfold acallee_saved; cbn [fst]; lia|]); apply Forall_nil).
(* sup_pool_config's events: record() with no spill, two arg_s copies, answer's free and two copies *)
assert (HNF : 0 <= 1 <= EV_SUP_POOL_CONFIG (e_R e))
  by (unfold EV_SUP_POOL_CONFIG, EV_RECORD, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC;
      rewrite (vr_spill_frees0 _ Hcalls); lia).
assert (HNM : 4 + VR_NM_PRE <= VR_NM_HD) by (unfold VR_NM_PRE, VR_NM_HD; lia).
assert (HNM1 : 0 <= 4 <= EV_SUP_POOL_CONFIG (e_R e))
  by (unfold EV_SUP_POOL_CONFIG, EV_RECORD, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC;
      rewrite (vr_spill_frees0 _ Hcalls); lia).
assert (HXM : XM_SUP_POOL_CONFIG MT (e_R e) (Some a) (atoi_a b) <=
  4 * mo_malloc MT VERBS_RECEIVE_REQ + 1 * mo_free MT).
{ unfold XM_SUP_POOL_CONFIG, XM_RECORD, XM_ARG_S, XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC.
  rewrite (vr_spill_frees0 _ Hcalls). cbn [sarg]. fold m.
  pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length a) + 1) 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ, LMAX in *; lia)) as M1.
  pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length (dec (atoi_a b))) + 1) 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M2.
  pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length (snd m)) + 1) 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M4.
  lia. }
assert (HLV : LIVE_SUP_POOL_CONFIG (e_R e) (Some a) (atoi_a b) <= 20 * VERBS_RECEIVE_REQ).
{ unfold LIVE_SUP_POOL_CONFIG, LIVE_ARG_S, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC, VERBS_RECEIVE_REQ. cbn [sarg].
  fold m. unfold LMAX in Hlmax1. lia. }
assert (HV : SUP_POOL_CONFIG_STK = ltac:(let v := eval vm_compute in SUP_POOL_CONFIG_STK in exact v)) by reflexivity.
assert (HST0 : 0 <= SUP_POOL_CONFIG_STK) by lia.
assert (HSTK1 : SUP_POOL_CONFIG_STK + 208 <= VERBS_RECEIVE_STK) by lia.
assert (Hstop : vr_pc 0x8d4cc = BASE + 0x6f9c) by (unfold vr_pc, AF_verbs_receive; lia).
assert (Hrun : sym_run_toN_pi pl_tpi FUEL 0x6f9c (vr_ss_ret 0x709c) = (vr_ss_ret 0x6f9c, PRS_running))
  by (vm_compute; reflexivity).
assert (Hp1r : 0 <= p1 < 2 ^ 64) by lia.
assert (CALL : forall ch, afn_pre SEGS B SUP_POOL_CONFIG_STK lyc Sc W (ms_regs ms3) (ms_mem ms3) mdv5 ch ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W (ms_mem ms3)) -> cmd_ro_ok (rdW W (ms_mem ms3)) ->
  rec_repA B lyc Sc (rdW W (ms_mem ms3)) (e_R e) (e_O e) -> Z.of_nat (length (frames Sc)) <= 5 ->
  st_nev Sc + EV_SUP_POOL_CONFIG (e_R e) <= EV_MAX ->
  blocks_bytes Sc + LIVE_SUP_POOL_CONFIG (e_R e) (Some a) (atoi_a b) <= LIVE_MAX ->
  mo_ok MT Sc (XM_SUP_POOL_CONFIG MT (e_R e) (Some a) (atoi_a b)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_sup_pool_config) (ms_regs ms3) (ms_mem ms3) mdv5)
  (apost_baseF SEGS B SUP_POOL_CONFIG_STK (vr_fp1 (e_O e)) (ms_regs ms3) lyc Sc W (ms_mem ms3) mdv5
    (EV_SUP_POOL_CONFIG (e_R e))
    (vr_rc_post B MT (e_R e) (e_O e) m (LIVE_SUP_POOL_CONFIG (e_R e) (Some a) (atoi_a b))
      (XM_SUP_POOL_CONFIG MT (e_R e) (Some a) (atoi_a b)) lyc Sc))).
{ intros ch HPRE2 H1 H2 H3 H4 H5 H6 H7.
  assert (H4' : Z.of_nat (length (frames Sc)) <= 7) by lia.
  exact (TSUP_POOL_CONFIG fx lyc Sc W (ms_regs ms3) (ms_mem ms3) mdv5 ch p1 (atoi_a b) (Some a) (e_R e) (e_O e)
    HPRE2 (vr18_ent_frm0 B MT e He) H1 H2 P10 Hp1r P11 Hid
    (ex_intro _ a (conj eq_refl (conj Hblk1 (conj Hstr1 (conj Hlmax1 Hap1)))))
    H3 H4' H5 H6 H7). }
exact (vr_call_arm_hd B MT HB MTL ROA RRO RPG RECC PROGU e W pos F q c 0x709c 0x6f9c rk 0x8d4cc [p0; p1; p2] lyc Sc
  (ms_regs ms3) (ms_mem ms3) mdv5 k nm AF_sup_pool_config SUP_POOL_CONFIG_STK (EV_SUP_POOL_CONFIG (e_R e))
  (LIVE_SUP_POOL_CONFIG (e_R e) (Some a) (atoi_a b)) (XM_SUP_POOL_CONFIG MT (e_R e) (Some a) (atoi_a b))
  4 1 m He Hcs Hntok Hrl Hrk Hvh Hk1 HNF HNM1 HNM HXM HLV HST0 HSTK1 ltac:(lia) eq_refl Hstop Hrun CALL).
Qed.

Lemma vr_s17 : vr_s17_stmt B MT.
Proof.
intros e W cf Hent Hrt.
destruct Hrt as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hne & Hcore & Hline & Hcopy).
change (vr_pc (vr_route_pc VRR.RPool)) with (vr_pc 0x8d598).
destruct (Z.eq_dec (vr_ntok (e_D e)) 3) as [H3 | H3].
- unfold vr_ntok in H3.
  destruct (Verbs.toks (e_D e)) as [|v args] eqn:Ht; [congruence|].
  pose proof (vr_route_pool v args Hroute) as Hv. subst v.
  destruct args as [|a [|b [|x args]]]; cbn [length] in H3; [lia | lia | | lia].
  eapply SRr_mono; [exact (vr_s17_call e W pos F q c tp lyc Sc regsc memc mdc k nm a b Hent Ht Hcore Hline Hcopy)|].
  intros W' c' _ (fq & Hr & H). exists fq. split; [exact Hr | right; exact H].
- eapply SRr_mono; [exact (vr_s17_pr e W pos F q c tp lyc Sc regsc memc mdc k nm Hent Hroute Hne Hcore Hline Hcopy H3)|].
  intros W' c' _ H. exists fx. split; [apply fxrel_refl | left; exact H].
Qed.

End e.
End f.
End d.
