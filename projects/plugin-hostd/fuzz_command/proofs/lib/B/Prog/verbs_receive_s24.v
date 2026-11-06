(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S24 (RQuit, 0x8d2a0-0x8d2b8) of the walk of verbs_receive on the
   ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v, vr_s24_stmt):
     li a0,1; bne s5,a0,0x8d870          (more than one word: to the refusal stub 0x8d870, vr_pr)
     auipc a1,0x556; sw a0,1336(a1)      (g_quitting := 1, a program static of the footprint, vr_prog_unowned)
     li a0,0; jal sup_resp               (sup_resp_c.v through PaFx's cl_callSF, verbs_receive_s05_k.v)
     j 0x8d3b0                           (the join J1 with the text in a0, vr_hd)
   The B twin of lib/A/Prog/verbs_receive_s24.v (a working branch): B leaves the refusal to
   the shared stub 0x8d870 (A called sup_resp(-902) in the arm) and keeps the text in a0 to J1 (A moved it to a1 and
   reloaded s9). The store's window is the listing's PHi atom A_HI 233 (0x5e32a8, CmdObj's cmd_val_his) + 1336 =
   0x5e37e0 = A_G_QUITTING; writing it asks the core's prog_rw (YCbq.v:1145), the record fact PRW that
   lib/B/Prog/CmdRecCells.v PROG_WRITABLE takes as well. All names of this file carry the prefix vr24_. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route verbs_receive_pre.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c socket_send_c reply_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_after_reply_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_live verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s30_m verbs_receive_s30_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx verbs_receive_s05_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the symbolic state of S24 at 0x8d2a0 with g_quitting a writable window (the quit arm stores into it) *)
Definition vr24_gq : YP09.region := YP09.mkRegion (Some (A_HI 233)) 1336 1340 1336 1340 [].
Definition vr24_ssq : sstate := mkSS 28016 sr_atoms [vr24_gq] None (mkFacts [] [] []).

(* the registers the quit arm keeps to J1 0x8d3b0 (vr_rl_hd without a0) *)
(* (s8 is not carried: the interface names no sender register after the dispatch, verbs_receive_iface.v vr_rl_rt) *)
Definition vr24_rlk (F q : Z) : list (Z * Z) := [(18, q); (22, F); (27, shadow_addr F + 4)].

(* ------------------------------------------------------------------------------------------------------------
   The model: the route RQuit; with no argument the step is quit (sup_resp(0), the flag set), else reject *)
Ltac vr24_rt_chain H :=
  cbv beta iota in H;
  repeat (match type of H with context [if ?b then _ else _] => destruct b; cbv beta iota in H end); try discriminate H.

Lemma vr24_route_cp : forall v args, VRR.route (v :: args) = VRR.RQuit ->
  Verbs.list_eqb v Verbs.Lit.verb_chain = false /\ Verbs.list_eqb v Verbs.Lit.verb_pin_set = false.
Proof.
intros v args H. split.
- destruct (Verbs.list_eqb v Verbs.Lit.verb_chain) eqn:E; [exfalso|reflexivity].
  unfold VRR.route, VRR.route_mid in H. rewrite E in H. vr24_rt_chain H.
- destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_set) eqn:E; [exfalso|reflexivity].
  unfold VRR.route, VRR.route_mid in H. rewrite E in H. vr24_rt_chain H.
Qed.

Lemma vr24_ev_route : forall R ln v args s,
  Verbs.list_eqb v Verbs.Lit.verb_chain = false -> Verbs.list_eqb v Verbs.Lit.verb_pin_set = false ->
  ev_route R ln (v :: args) s = ev_step R s.
Proof. intros R ln v args s H1 H2. unfold ev_route. rewrite H1, H2. reflexivity. Qed.

Lemma vr24_quit_step : forall R D, VRR.route (Verbs.toks D) = VRR.RQuit -> length (Verbs.toks D) = 1%nat ->
  vr_h R D = (R, resp 0, true) /\ vr_k1 R D = 2 + EV_SUP_RESP.
Proof.
intros R D Hr Hl. destruct (Verbs.toks D) as [|v args] eqn:T; [cbn in Hl; lia|].
destruct args as [|a args]; [|cbn in Hl; lia].
assert (St : vr_st D = Verbs.SQuit).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. rewrite Hr. reflexivity. }
destruct (vr24_route_cp v [] Hr) as [Hc1 Hc2].
split.
- unfold vr_h. rewrite St. reflexivity.
- unfold vr_k1. rewrite St, T. rewrite (vr24_ev_route _ _ _ _ _ Hc1 Hc2). reflexivity.
Qed.

Lemma vr24_quit_rej : forall R D, VRR.route (Verbs.toks D) = VRR.RQuit -> Verbs.toks D <> [] ->
  length (Verbs.toks D) <> 1%nat ->
  vr_h R D = (R, resp (-902), false) /\ vr_k1 R D = 2 + EV_SUP_RESP.
Proof.
intros R D Hr Hne Hl. destruct (Verbs.toks D) as [|v args] eqn:T; [congruence|].
destruct args as [|a args]; [cbn in Hl; lia|].
assert (St : vr_st D = Verbs.reject).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. rewrite Hr. reflexivity. }
destruct (vr24_route_cp v (a :: args) Hr) as [Hc1 Hc2].
split.
- unfold vr_h. rewrite St. reflexivity.
- unfold vr_k1. rewrite St, T. rewrite (vr24_ev_route _ _ _ _ _ Hc1 Hc2). reflexivity.
Qed.

Lemma vr24_hd_ntok : forall nt, nt = 1%nat -> vr_hd_ntok 0x8d3b0 nt.
Proof. intros nt H. unfold vr_hd_ntok. exact H. Qed.
Lemma vr24_pr_ntok : forall nt, (2 <= nt)%nat -> vr_pr_ntok 0x8d870 nt.
Proof. intros nt H. unfold vr_pr_ntok. exact H. Qed.

Lemma vr24_rv_kept : forall (regs regs' : bvmap 5 word) l,
  vr_rv regs l -> (forall r v, In (r, v) l -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) -> vr_rv regs' l.
Proof.
intros regs regs' l H Hk. unfold vr_rv in *. rewrite Forall_forall in *. intros [r v] Hin. cbn [fst snd].
rewrite (Hk r v Hin). exact (H (r, v) Hin).
Qed.

Ltac vr24_reg KR HR :=
  first
  [ assumption
  | lazymatch goal with |- getr _ (Z_to_bv 5 ?r) = w64 ?v =>
      rewrite (KR r ltac:(vr05_inl)); apply (vr_rv_get _ _ r v HR); apply in_or_app;
      first [left; unfold vr_base; solve [vr05_inl] | right; unfold vr_rl_rt; solve [vr05_inl]] end ].
Ltac vr24_regs KR HR :=
  apply vr_rv_intro; intros r v Hin; unfold vr_base in Hin; cbn [app In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; vr24_reg KR HR |]); contradiction.
Ltac vr24_fa := cbv beta; repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia.

(* ============================================================================================================
   After sup_resp (statement pass 4: sup_resp's post is FP-existential, so the code after its return runs at some FP
   state fx'): 0x8d2b8 j 0x8d3b0, proved at this section's fx and used below at fx' *)
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
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let MOVE := vr_core_move B MT RRO RPG RECC PROGU ROA.
(* the lemmas below take every hypothesis of this section, in the order above *)
Local Set Default Proof Using "All".

(* the jump of a return pc to a boundary, run from a state that names only the registers (the kit's vr_jmp, over
   the walk's LAWS alone) *)
Lemma vr24_jmp : forall retk stopk,
sym_run_toN_pi pl_tpi FUEL stopk (vr_ss0 retk) = (vr_ss0 stopk, PRS_running) ->
forall W2 (regs2 : bvmap 5 word) mem2 md2 (Q : world SEGS -> config -> Prop) STK sp0 FP ly S W0 mem md own ly2 S2 kk,
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 kk ->
(forall regs3 mem3 md3, (forall r, getr regs3 r = getr regs2 r) -> (forall a, rdW W2 mem3 a = rdW W2 mem2 a) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem3 md3 kk ->
  Q W2 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + stopk)) mem3 (seg_rom SEGS)) md3)) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros retk stopk Hrun W2 regs2 mem2 md2 Q STK sp0 FP ly S W0 mem md own ly2 S2 kk HJ HQ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
pose proof (vr_seed0 W2 regs2 mem2 retk) as HS.
eapply (SRr_run_to_pi_AJ B LAWS W2 FUEL stopk (Eimg (Ereg regs2 [])) (vr_ss0 retk) (vr_ss0 stopk) PRS_running _
  STK sp0 FP ly S W0 mem md own ly2 S2 md2 kk Q HEI HS Hrun I HJ).
- apply awr_ok_nil.
- intros ms' mat HS' HJ' HF HFr HG.
  rewrite (st_ok_pi_restrict_mkst (w_H W2) _ (vr_ss0 stopk) ms' HS' eq_refl). cbn [ss_pc vr_ss0].
  apply SRr_ret. apply HQ.
  + intros r. rewrite (st_ok_pi_restrict_reg (w_H W2) _ (vr_ss0 stopk) ms' r HS'). cbn [ss_regs vr_ss0].
    symmetry. exact (regs_ok_Eimg_Ereg regs2 [] r).
  + cbn [ms_mem mkst ss_mem vr_ss0] in HFr. intros a.
    exact (vr_rdW_frame _ [] W2 _ _ HFr (vr_no_wrange _ [] (Forall_nil _)) a).
  + exact HJ'.
Qed.

(* the quit arm after sup_resp returned to 0x8d2b8: j 0x8d3b0, the text in a0 *)
Lemma vr24_quit_tail : forall e pos F q c tp tq k nm ly2 S2 W2 regs2 mem2 md2,
  vr_h (e_R e) (e_D e) = (e_R e, resp 0, true) -> length (Verbs.toks (e_D e)) = 1%nat ->
  4096 <= tq -> astr_atR (rdW W2 mem2) tq (vr_x (e_R e) (e_D e)) ->
  vr_core B MT e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c] vr_sh2
    (vr_sl3 F q c) ((10, tq) :: vr24_rlk F q) (vr_R1 (e_R e) (e_D e)) (e_O e) 1 k (vr_k1 (e_R e) (e_D e)) nm
    VR_NM_HD ly2 S2 W2 regs2 mem2 md2 ->
  vr_line B e q W2 mem2 -> vr_copy B e F c tp W2 mem2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 28040)) mem2 (seg_rom SEGS)) md2) (vr_athd B MT 0x8d3b0 e).
Proof.
intros e pos F q c tp tq k nm ly2 S2 W2 regs2 mem2 md2 Hvh H1 Htq Hstr HC2 HL2 HCP2.
pose proof HC2 as (HJ2 & _ & _ & _ & _ & Hrv2 & _).
apply (vr24_jmp 28040 28288 ltac:(vm_compute; reflexivity) W2 regs2 mem2 md2 _ _ _ _ _ _ _ _ _ _ ly2 S2 _ HJ2).
intros regs3 mem3 md3 Er Em HJ3.
unfold vr_athd, vr_hd.
assert (EQV : vr_qv e = 1) by (unfold vr_qv, vr_quit; rewrite Hvh; reflexivity).
exists tq, (e_O e), pos, F, q, c, tp, ly2, S2, regs3, mem3, md3, k, nm.
split; [unfold cfg_at, w64; replace (vr_pc 0x8d3b0) with (BASE + 28288) by (unfold vr_pc, AF_verbs_receive; lia);
  reflexivity|].
split; [exact (vr24_hd_ntok _ H1)|].
split; [lia|].
split; [exact (vr_astr_eq _ _ tq _ Em Hstr)|].
rewrite EQV.
split; [|split; [exact (vr_line_eq B e q W2 mem2 mem3 Em HL2) | exact (vr_copy_eq B e F c tp W2 mem2 mem3 Em HCP2)]].
assert (Erl : vr_rl_hd e F q c 0x8d3b0 tq = (10, tq) :: vr24_rlk F q) by reflexivity.
rewrite Erl.
apply (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ _ (e_O e) 1 k _ nm _ ly2 S2 W2 regs2 mem2 md2
  (vr_sl3 F q c) _ (vr_k1 (e_R e) (e_D e)) VR_NM_HD regs3 mem3 md3 HC2 HJ3 Em).
- apply (vr24_rv_kept regs2 _ _ Hrv2). intros r v _. apply Er.
- apply incl_refl.
- lia.
- lia.
Qed.

End et.
End ft.
End dt.

(* ============================================================================================================
   The segment *)
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
(* the callee's contract (verbs_receive_c.v) and the record facts: the interface's, and the core's prog_rw for the
   store into g_quitting *)
Hypothesis TSUP_RESP : forall fx0 : YK11.FPState, tsup_resp_spec (fx := fx0) B MT.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VHIS : cmd_val_his (PI := PI).
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let MOVE := vr_core_move B MT RRO RPG RECC PROGU ROA.
Let ENTF := vr05_ent_facts B MT TSUP_RESP MTL RRO RPG RECC PROGU ROA.
Let S1B := vr05_s1_bounds B MT TSUP_RESP MTL RRO RPG RECC PROGU ROA.
Let RCALL := vr05_resp_call B MT TSUP_RESP MTL RRO RPG RECC PROGU ROA.

(* the auipc at 0x8d2a8 is the listing's PHi atom A_HI 233 (CmdObj's cmd_val_his) *)
Lemma vr24_vhis : VAL (A_HI 233) = 0x5e32a8.
Proof. rewrite (VHIS 233%nat) by (apply Nat.ltb_lt; vm_compute; reflexivity). vm_compute. reflexivity. Qed.

(* the walk's own store into g_quitting: a program static its footprint holds *)
Lemma vr24_gq_awr : forall e STK sp0 bl0 blc fr0 ly own a, A_G_QUITTING <= a < A_G_QUITTING + 4 ->
  awr_byte SEGS B STK sp0 (vr_fp e) bl0 blc fr0 ly own a.
Proof.
intros e STK sp0 bl0 blc fr0 ly own a Ha. right; right; right; right; left.
assert (Hpg : inFP cmd_PG a)
  by (unfold cmd_PG; apply inFP_cons; right; apply inFP_cons; right; apply inFP_cons; left; exact Ha).
split; [|split].
- exists (A_G_QUITTING, A_G_QUITTING + 4). split; [|exact Ha].
  unfold vr_fp, VERBS_RECEIVE_PG. apply in_or_app. left. right. right. left. reflexivity.
- rewrite (YF0m.ts_prog B HB). unfold YF0m.TFIB_PROG_STATIC. apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
  unfold in_zr. cbn [fst snd]. unfold A_G_QUITTING in Ha. lia.
- exact (proj1 (PROGU a Hpg)).
Qed.

(* a boundary state across a run whose only store is into g_quitting: the frame, the saves, the spills, the blocks,
   the recorder, tok[] and the read-only facts lie apart from it *)
Lemma vr24_gq_move : forall e pos F q c tp rl rl' Rc Oc qv qv' k kmax nm nmax lyc Sc (W : world SEGS)
  regs regs' mem mem' md md',
vr_ent B MT e ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem' md' k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_QUITTING <= a < A_G_QUITTING + 4) -> rdW W mem' a = rdW W mem a) ->
aval_mem (rdW W mem') A_G_QUITTING 4 qv' ->
vr_rv regs' (vr_base B e ++ rl') ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl' Rc Oc qv' k kmax nm nmax lyc Sc W regs' mem' md' /\
vr_line B e q W mem' /\ vr_copy B e F c tp W mem'.
Proof.
intros e pos F q c tp rl rl' Rc Oc qv qv' k kmax nm nmax lyc Sc W regs regs' mem mem' md md'
  He HC HL HCP HJ' Hkeep Hq' Hrv'.
destruct HC as (HJ & Hk & Hm & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hd & Hperm & Hq).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct (S1B e Hstk) as (Hs1a & Hs1b & Hs1c & Hs1d & _).
destruct (ENTF e He) as (_ & _ & Hn8 & HDn & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfr4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct Hfr as (HFa & HFw & HFs).
assert (FB : fs_frame_bytes 4 = 1024) by reflexivity.
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md 4 pos HAR Hfr4) as (Hf0 & Hfc & _).
rewrite FB, <- HFa in Hfc. rewrite <- HFa in Hf0.
assert (HGQimg : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> in_img SEGS a).
{ intros a Ha. apply (proj1 (PROGU a ltac:(unfold cmd_PG; apply inFP_cons; right; apply inFP_cons; right;
    apply inFP_cons; left; exact Ha))). }
pose proof (shadow_addr_bounds F ltac:(unfold kHighMemEnd in *; lia)) as Hsh.
assert (KF : forall a, (F <= a < F + 1024 \/ shadow_addr F <= a < shadow_addr F + 128) -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply Hkeep.
  - unfold kLowMemEnd, kHighShadowEnd in Hsh. destruct Ha as [Ha | Ha]; lia.
  - intros Hga. destruct Ha as [Ha | Ha].
    + apply (frm_img SEGS B LAWS lyc Sc W mem md 4 pos a HAR Hfr4); [rewrite <- HFa, FB; lia | exact (HGQimg a Hga)].
    + unfold A_G_QUITTING, kLowMemEnd in *. lia. }
assert (KS : forall a, vr_s1 e <= a < vr_sp0 e -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply Hkeep; [lia | unfold A_G_QUITTING; lia]. }
assert (KB : forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n ->
  rdW W mem' (p + i) = rdW W mem (p + i)).
{ intros p n i Hb Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hb) as (_ & Hp1 & Hp2 & _ & _ & _ & Hp4).
  apply Hkeep; [lia|]. intros Hga.
  apply (blk_img SEGS B LAWS lyc Sc W mem md p n (p + i) HAR Hb); [lia | exact (HGQimg _ Hga)]. }
assert (HinLb : In (vr_lb e q) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
assert (HinCb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. right. left. reflexivity. }
split; [|split].
- split; [exact HJ'|]. split; [exact Hk|]. split; [exact Hm|]. split; [exact Hnm|].
  split.
  { split; [exact HFa|]. split.
    - rewrite <- HFw. apply rdword_ext. intros kk Hkk. apply KF. left. lia.
    - intros i Hi. rewrite KF; [exact (HFs i Hi) | right; lia]. }
  split; [exact Hrv'|].
  split.
  { intros j r Hj. assert (Hjl : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbv [vr_saved_regs] in Hjl; cbn [length] in Hjl.
    apply (aval_mem_agree _ _ _ 8 _ (Hsv j r Hj)). intros kk Hkk. apply KS. lia. }
  split.
  { unfold vr_spill in *. rewrite Forall_forall in Hsp |- *. intros ov Hov.
    assert (Hob : 0 <= fst ov <= 72).
    { unfold vr_sl3 in Hov. cbn [In] in Hov.
      repeat (destruct Hov as [<- | Hov]; [cbn [fst]; lia|]). destruct Hov. }
    apply (aval_mem_agree _ _ _ 8 _ (Hsp ov Hov)). intros kk Hkk.
    replace (vr_s1 e + fst ov + kk) with (vr_s1 e + (fst ov + kk)) by lia. apply KS. lia. }
  split.
  { exact (vr_env_of_aro B MT RRO RPG RECC PROGU ROA lyc Sc W mem' md' (proj1 HJ')
      (vr_aro_kept B MT RRO RPG RECC PROGU ROA e _ lyc Sc W mem' md' _ He HJ')). }
  split.
  { apply (rec_repA_agree B lyc Sc lyc Sc (rdW W mem) (rdW W mem') Rc Oc Hrec).
    - intros pn _ H. exact H.
    - intros kk Hkk. apply Hkeep; unfold A_G_REC, REC_SIZE, A_G_QUITTING in *; lia.
    - intros kk Hkk. apply Hkeep; unfold A_REC_SPILL, SC_SIZE, A_G_QUITTING in *; lia.
    - intros [p n] Hpn kk Hkk. cbn [fst snd] in *.
      pose proof (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn) as Hb.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hb) as (_ & _ & _ & _ & _ & _ & Hn).
      pose proof (req_size_pos n ltac:(lia)) as [_ Hr].
      apply (KB p n kk Hb). lia. }
  split; [exact Hd|]. split; [exact Hperm | exact Hq'].
- (* the line *)
  destruct HL as (Hfl & Hln). split; [exact Hfl|].
  assert (Hll : Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e)).
  { unfold vr_l. rewrite <- HDn. exact (vrm_line_le (e_D e)). }
  assert (Hl0 : 0 <= vr_l (e_n e) (e_D e)) by (unfold vr_l; pose proof (vrm_l_le (e_n e) (e_D e) ltac:(lia)); lia).
  apply (astr_atR_agree _ _ q _ (vr_l (e_n e) (e_D e) + 1) Hln); [lia|].
  intros kk Hkk. apply (KB q (vr_l (e_n e) (e_D e) + 1) kk HinLb).
  pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)). lia.
- (* the copy and tok[] *)
  destruct HCP as (Hfc' & Htk). split; [exact Hfc'|].
  pose proof (Verbs.toks_length (e_D e)) as Hl64.
  pose proof Htk as (_ & Htl & _).
  apply (vr05_atoks_agree _ _ _ _ _ _ _ Htk).
  + intros kk Hkk. rewrite Htl in Hkk. apply KF. left. lia.
  + intros kk Hkk. apply (KB c (Z.of_nat (length (Verbs.line (e_D e))) + 1) kk HinCb).
    pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   S24 *)
Lemma vr_s24 : vr_s24_stmt B MT.
Proof.
intros e W cf He HP.
destruct HP as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & Hcf & Hroute & Hne & HC & HL & HCP).
pose proof HC as (HJ & Hk & _ & Hnm & (EF & _ & _) & Hrv & _ & Hsp & _ & Hrec & _ & Hperm & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Hnt : 0 <= vr_ntok (e_D e) <= 64).
{ unfold vr_ntok. pose proof (Verbs.toks_length (e_D e)). lia. }
assert (R21 : getr regsc (Z_to_bv 5 21) = w64 (vr_ntok (e_D e)))
  by (apply (vr_rv_get regsc _ _ _ Hrv); apply in_or_app; right; unfold vr_rl_rt; vr05_inl).
subst cf. unfold cfg_at, w64.
replace (vr_pc (vr_route_pc VRR.RQuit)) with (BASE + 28016) by (unfold vr_pc, vr_route_pc, AF_verbs_receive; lia).
destruct (Nat.eq_dec (length (Verbs.toks (e_D e))) 1) as [H1 | H1].
- (* one word: g_quitting := 1, sup_resp(0), to J1 0x8d3b0 with the text in a0 *)
  destruct (vr24_quit_step (e_R e) (e_D e) Hroute H1) as [Hvh Hk1].
  set (E := Eimg (Ereg regsc [])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply vr_env_agree).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (U633 : bv_unsigned (ew E (A_HI 233)) = 0x5e32a8).
  { subst E. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia). rewrite vr24_vhis. apply unsigned_lit_small. lia. }
  assert (Hwin : forall x : word, ~ (A_G_QUITTING <= bv_unsigned x < A_G_QUITTING + 4) ->
    ~ in_wrange E [vr24_gq] (bv_unsigned x)).
  { intros x Hx (r & [<-|[]] & Hr). cbn [YP09.r_base YP09.r_wlo YP09.r_whi vr24_gq base_val] in Hr. rewrite U633 in Hr.
    apply Hx. unfold A_G_QUITTING. lia. }
  assert (HS : st_ok_pi SEGS VAL E vr24_ssq
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 28016)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold vr24_ssq. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vr24_gq.
      cbv beta iota delta [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U633. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply PRW. rewrite (YF0m.ts_prog B HB). unfold YF0m.TFIB_PROG_STATIC.
      apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. split; lia.
    - cbn. tauto.
    - split; [exact I | split; exact I]. }
  (* 0x8d2a0: li a0,1 *)
  paj_run_shc RUNP RUNC HS HJ.
  { eapply awr_ok_cons_gen with (n := A_HI 233) (b := 0x5e32a8); [reflexivity | exact U633 | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi vr24_gq]. intros a Ha. apply (vr24_gq_awr e). unfold A_G_QUITTING. split; lia. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  rename HFr into HFr1. clear HF HG.
  (* 0x8d2a4: bne s5,a0,0x8d870 *)
  psrr_branch_pi RUNP BR HS.
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    unfold vr_ntok in Hc. rewrite H1 in Hc. vm_compute in Hc. discriminate Hc.
  + (* 0x8d2a8: auipc a1,0x556; sw a0,1336(a1); li a0,0; jal sup_resp *)
    paj_run_shc RUNP RUNC HS HJ.
    { eapply awr_ok_cons_gen with (n := A_HI 233) (b := 0x5e32a8); [reflexivity | exact U633 | | apply awr_ok_nil].
      cbn [YP09.r_wlo YP09.r_whi vr24_gq]. intros a Ha. apply (vr24_gq_awr e). unfold A_G_QUITTING. split; lia. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
    pose proof (vr_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 18; 22; 27] HS HAE
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
      assert (U633' : bv_unsigned (ew E 633%nat) = 0x5e32a8) by exact U633. rewrite U633' in Hb2.
      unfold aview. cbn [ms_mem restrict] in Hb2.
      replace (A_G_QUITTING + Z.of_nat kk) with (0x5e32a8 + 1336 + Z.of_nat kk) by (unfold A_G_QUITTING; lia).
      rewrite Hb2. cbn [option_map]. f_equal. injection Hb1 as <-.
      destruct kk as [|[|[|[|kk]]]]; [vm_compute; reflexivity .. | lia]. }
    assert (Hrv0 : vr_rv (ms_regs ms0) (vr_base B e ++ (1, BASE + 28040) :: (10, 0) :: vr24_rlk F q))
      by (unfold vr24_rlk; vr24_regs KR Hrv).
    clear HF HFr HFr1 HG.
    destruct (vr24_gq_move e pos F q c tp _ _ (e_R e) (e_O e) (e_q0 e) 1 k 2 nm VR_NM_PRE lyc Sc W regsc (ms_regs ms0)
      memc (ms_mem ms0) mdc mdv2 He HC HL HCP HJ Hkeep Hq1 Hrv0) as (HC1 & HL1 & HCP1).
    pmkst HS.
    rewrite (SIGP CS_sup_resp ltac:(unfold cmd_prog_syms; vr05_inl)).
    change (cmd_af CS_sup_resp) with AF_sup_resp.
    eapply SRr_bind.
    { exact (RCALL e pos F q c (vr_sl3 F q c) 1 lyc Sc W (ms_regs ms0) (ms_mem ms0) mdv2 k nm 28040 0 true
        (vr24_rlk F q) He Hvh Hk1 ltac:(lia) HC1 HL1 ltac:(unfold vr24_rlk; vr24_fa) ltac:(unfold vr_sl3; vr24_fa)
        ltac:(lia) eq_refl). }
    intros W2 c2 _ (fx' & tq & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfx & Htq4 & Hstr & Hcore2 & Hline2 & Hcopy2).
    (* the rest of the walk at the FP state sup_resp returned (the section above, at fx') *)
    eapply SRr_mono.
    { exact (vr24_quit_tail (fx := fx') B MT RRO RPG RECC PROGU ROA e pos F q c tp tq (k + EV_SUP_RESP) (nm + 1)
        ly2 S2 W2 regs2 mem2 md2 Hvh H1 Htq4 Hstr Hcore2 Hline2 (Hcopy2 tp HCP1)). }
    intros W' cf' _ Hh. exists fx'. split; [exact Hfx|]. unfold vrF_or, vr_or, vrF_hd. right. exact Hh.
- (* two or more words: to the refusal stub 0x8d870 (li a0,-902; jal sup_resp there, S29) *)
  destruct (vr24_quit_rej (e_R e) (e_D e) Hroute Hne H1) as [Hvh Hk1].
  assert (Hl2 : (2 <= length (Verbs.toks (e_D e)))%nat)
    by (destruct (Verbs.toks (e_D e)) as [|v0 [|v1 r1]] eqn:T;
        [congruence | try rewrite T in H1; cbn [length] in H1; lia | cbn [length]; lia]).
  pose proof (vr_seed0 W regsc memc 28016) as HS.
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc []))) by apply Eimg_env.
  pose proof (vr_env_agree regsc []) as HAE.
  assert (E21 : ew (Eimg (Ereg regsc [])) 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  remember (Eimg (Ereg regsc [])) as E eqn:HE. clear HE.
  (* 0x8d2a0: li a0,1 *)
  paj_run_shc RUNP RUNC HS HJ.
  { apply awr_ok_nil. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  assert (Hro1 : rs_read_only (ss_mem (vr_ss0 28016)) = true) by reflexivity.
  pose proof (frame_of_read_only _ _ _ _ Hro1 HF) as Hm1. clear HF HFr HG.
  (* 0x8d2a4: bne s5,a0,0x8d870 *)
  psrr_branch_pi RUNP BR HS.
  + (* the branch taken: to 0x8d870 *)
    paj_run_to_shc RUNTO HS HJ 29504.
    { apply awr_ok_nil. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    lazymatch goal with
    | Hfx : frame_of _ ?rs (ms_mem _) (ms_mem _) |- _ =>
      assert (Hro2 : rs_read_only rs = true) by (vm_compute; reflexivity);
      pose proof (frame_of_read_only _ _ _ _ Hro2 Hfx) as Hm2
    end.
    clear HF HFr HG.
    pose proof (vr_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 18; 21; 22; 27] HS HAE
      ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    assert (Hmm : ms_mem ms0 = memc) by (rewrite Hm2; exact Hm1).
    pmkst HS. rewrite Hmm in HJ |- *.
    apply SRr_ret.
    exists fx. split; [apply fxrel_refl|]. unfold vrF_or, vr_or, vrF_pr, vr_atpr, vr_pr. left.
    exists (-902), (e_R e), (e_O e), pos, F, q, c, tp, lyc, Sc, (ms_regs ms0), memc, mdv2, k, nm.
    split; [unfold cfg_at, w64; replace (vr_pc 0x8d870) with (BASE + 29504) by (unfold vr_pc, AF_verbs_receive; lia);
      reflexivity|].
    split; [intros _; reflexivity|].
    split; [lia|].
    split; [exact Hvh|].
    split; [exact Hne|].
    split; [exact (vr24_pr_ntok _ Hl2)|].
    split; [|split; [exact HL | exact HCP]].
    assert (Erl : vr_rl_pr e F q c 0x8d870 (-902) =
      [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)]) by reflexivity.
    rewrite Erl.
    apply (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc
      (vr_sl3 F q c) _ (vr_k1 (e_R e) (e_D e) - EV_SUP_RESP) VR_NM_PR (ms_regs ms0) memc mdv2 HC HJ (fun a => eq_refl)).
    * vr24_regs KR Hrv.
    * apply incl_refl.
    * rewrite Hk1. lia.
    * unfold VR_NM_PRE, VR_NM_PR. lia.
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    change (U E (SLit 1)) with 1 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold vr_ntok in Hc. lia.
Qed.

End e.
End f.
End d.
