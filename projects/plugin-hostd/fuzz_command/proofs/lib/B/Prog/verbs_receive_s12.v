(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S12 RIinfo (B 0x8d3f8-0x8d418, 8 instructions) of the walk of
   verbs_receive on the ASan+UBSan build of plugin-hostd/fuzz_command (interface lib/B/Prog/verbs_receive_iface.v,
   vr_s12_stmt):
     li a0,2; bne s5,a0,0x8d68c; li a0,-9; ld s3,40(s1); bltu a0,s3,0x8d938; ld a0,8(s3); jal wrapper_atoi;
     jal sup_instance_info; j 0x8d4cc.
   The S08 arm with the atoi wrapper before the recorder call: B reloads tok from its frame slot s1+40 where A kept
   it in s6, and inserts the UBSan check 0x8d408 on tok + 8 (B-only, B-PREP section 3), which the frame bounds
   refute (tok = F + 32 with F + 1024 <= alloc_ceiling <= 2 ^ 47).
   With ntok <> 2 the step is reject and the run stops at the refusal stub 0x8d68c (vr_pr, at the entry's FP state).
   With ntok = 2 the run calls the atoi wrapper on tok[1] (a Theorem Labs lane's aatoi_realizes, through PaArt.aj_art_at: the
   wrapper writes its window below the stack pointer and the errno cell), then sup_instance_info(atoi_a tok[1])
   (sup_instance_info_c.v, FP-existential), and reaches the join 0x8d4cc through verbs_receive_s08_lib.v's generic
   arm vr_call_arm. The boundary facts are carried across the atoi call by vr_kx: the memory agrees below the
   allocation ceiling and from the realigned stack pointer up, except at the errno cell. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_instance_info_c sup_reply_code_c sup_resp_c xmalloc_c arg_s_c record_c answer_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s30_m verbs_receive_s30_kit verbs_receive_s08_lib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the model: the route RIinfo is the verb instance_info; with one argument the step is
   sup_instance_info (atoi_a tok[1]), else reject *)
Lemma route_iinfo : forall tk, VRR.route tk = VRR.RIinfo -> exists args, tk = Verbs.Lit.verb_instance_info :: args.
Proof.
intros [|v args] H; [discriminate H|]. exists args. f_equal.
unfold VRR.route, VRR.route_mid, VRR.route_tail, VRR.route_conn, VRR.route_cd in H.
repeat match type of H with
| context [if ?b then _ else _] =>
    let Eb := fresh "Eb" in
    destruct b eqn:Eb; cbv beta iota in H; [first [discriminate H | apply Verbs.list_eqb_eq; exact Eb] |]
end.
destruct (Verbs.ledger_of v Verbs.Lit.instance_info_verbs); [discriminate H|].
destruct args as [|a [|b [|c r]]]; try discriminate H.
all: cbv beta iota in H;
  repeat match type of H with context [if ?b then _ else _] => destruct b; cbv beta iota in H end;
  discriminate H.
Qed.

Lemma iinfo_call : forall R D a, Verbs.toks D = [Verbs.Lit.verb_instance_info; a] ->
vr_h R D = (sup_instance_info_m R (atoi_a a), false) /\ vr_k1 R D = 2 + EV_SUP_INSTANCE_INFO R.
Proof.
intros R D a T.
assert (St : vr_st D = Verbs.SCall (Verbs.sup_instance_info (atoi_a a))).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. reflexivity. }
split.
- unfold vr_h. rewrite St. reflexivity.
- unfold vr_k1. rewrite St, T. reflexivity.
Qed.

Lemma iinfo_rej : forall R D, VRR.route (Verbs.toks D) = VRR.RIinfo -> length (Verbs.toks D) <> 2%nat ->
vr_h R D = (R, resp (-902), false) /\ vr_k1 R D = 2 + EV_SUP_RESP.
Proof.
intros R D Hr Hl. destruct (route_iinfo _ Hr) as (args & T).
assert (St : vr_st D = Verbs.reject).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. rewrite <- T, Hr, T. cbn [VRR.plan_at].
  destruct args as [|a [|b r]]; [reflexivity | rewrite T in Hl; cbn in Hl; lia | reflexivity]. }
split.
- unfold vr_h. rewrite St. reflexivity.
- unfold vr_k1. rewrite St, T. reflexivity.
Qed.

(* the atoi wrapper's value is an int *)
Lemma swrap32_range : forall z, -2 ^ 31 <= bv_swrap 32 z < 2 ^ 31.
Proof.
intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
assert (E : 2 ^ Z.of_N 32 = 4294967296) by reflexivity. rewrite E.
change (Z.div 4294967296 2) with 2147483648.
pose proof (Z.mod_pos_bound (z + 2147483648) 4294967296 ltac:(lia)). lia.
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
(* the callee's contract and the atoi entry at every FP state, as the statement states them (verbs_receive_c.v:245,
   :277), and the record facts of the interface. ENV (api_env: the errno cell is in the low image and the
   allocator's one-frame traces are in the record's universe) is what PaArt's aj_art_at asks of a runtime entry
   that writes errno; the interface's list does not name it. At PI := PB_cmd the assembly discharges it by
   `exact (pal_env B (cmd_palib B HB))` (CmdRecRest.v), or by CmdRecCells' cmd_cf_env from HB and
   cmd_img_facts_tfib. *)
Hypothesis TSUP_INSTANCE_INFO : forall fx0 : YK11.FPState, @tsup_instance_info_spec fx0 rc SK PI B MT.
Hypothesis AATOI : forall fx0 : YK11.FPState,
  @RtNumber.aatoi_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis BLKT : vr_blktail B.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis ENV : api_env SEGS B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let ART := aj_art_at SEGS B LAWS pa_segs_low ENV.
#[local] Notation vtok_arg := (vr_tok_arg B MT RRO RPG RECC PROGU ROA HB MTL).
#[local] Notation vrv_keep := (vr_rv_keep B MT RRO RPG RECC PROGU ROA HB MTL).
#[local] Notation vpr_build := (vr_pr_build B MT RRO RPG RECC PROGU ROA HB MTL).
#[local] Notation vcall_arm := (vr_call_arm B MT RRO RPG RECC PROGU ROA HB MTL).
#[local] Notation vseed_tok := (vr_seed_tok B).
#[local] Notation vcore_move := (vr_core_move B MT RRO RPG RECC PROGU ROA).
#[local] Notation vFPrec := (inFP_PG_rec B MT RRO RPG RECC PROGU ROA HB MTL).
#[local] Notation vFPspill := (inFP_PG_spill B MT RRO RPG RECC PROGU ROA HB MTL).
#[local] Notation vFPquit := (inFP_PG_quit B MT RRO RPG RECC PROGU ROA HB MTL).

(* ---------------------------------------------------------------------------------------------------------------
   Across the atoi call: memory that agrees below the allocation ceiling and from the realigned stack pointer up,
   except at the errno cell (aj_art_at's frame for aatoi_realizes, whose window is below vr_s1) *)
Definition vr_kx (e : vrE) (W : world SEGS) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ vr_s1 e <= a) -> ~ aerrno_cell B a -> rdW W m' a = rdW W m a.

Lemma nerr_hi : forall a, kLowMemEnd <= a -> ~ aerrno_cell B a.
Proof. intros a Ha He. pose proof ENV as ((E0 & E1) & _). unfold aerrno_cell in He. lia. Qed.
Lemma nerr_img : forall a, ~ in_img SEGS a -> ~ aerrno_cell B a.
Proof. intros a Ha He. pose proof ENV as (_ & EI & _). exact (Ha (EI a He)). Qed.
Lemma nerr_frame : forall lyc Sc (W : world SEGS) mem md pos a, AR SEGS B lyc Sc W mem md -> In (4, pos) (frames Sc) ->
frame_addr lyc 4 pos <= a < frame_addr lyc 4 pos + 1024 -> ~ aerrno_cell B a.
Proof.
intros lyc Sc W mem md pos a HAR Hin Ha. apply nerr_img. apply (frm_img SEGS B LAWS lyc Sc W mem md 4 pos a HAR Hin).
change (fs_frame_bytes 4) with 1024. exact Ha.
Qed.
Lemma nerr_block : forall lyc Sc (W : world SEGS) mem md p n a, AR SEGS B lyc Sc W mem md -> In (p, n) (ablocks B lyc Sc) ->
p <= a < p + req_size n -> ~ aerrno_cell B a.
Proof. intros lyc Sc W mem md p n a HAR Hin Ha. apply nerr_img. exact (blk_img SEGS B LAWS lyc Sc W mem md p n a HAR Hin Ha). Qed.
Lemma nerr_pg : forall a, inFP cmd_PG a -> ~ aerrno_cell B a.
Proof. intros a Ha. destruct (PROGU a Ha) as (_ & _ & He). exact He. Qed.
Lemma img_pg : forall a, inFP cmd_PG a -> a < 0x606000.
Proof. intros a Ha. destruct (PROGU a Ha) as (Hi & _). exact (proj2 (pa_img_range a Hi)). Qed.

Lemma vr_core_kx : forall e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md regs' mem' md',
vr_ent B MT e ->
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  [(4, pos)] lyc Sc W mem' md' k ->
vr_kx e W mem mem' ->
Forall (fun ov => 0 <= fst ov <= 200) sl ->
vr_rv regs' (vr_base B e ++ rl') ->
vr_core B MT e pos F tmps sh sl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs' mem' md'.
Proof.
intros e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md regs' mem' md'
  Hent (HJ & Hkm & Hmeter & Hnm & Hframe & Hrv & Hsaved & Hspill & Henv & Hrec & HdO & Hperm & Hquit) HJ' K Hsl Hrv'.
pose proof Hent as (HPRE0 & _). pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof (vr_s1_cases e Hal16) as Hs1.
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ') as HAR'.
assert (Hin4 : In (4, pos) (frames Sc)) by (pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _); rewrite Hfrs; left; reflexivity).
split; [exact HJ'|]. split; [exact Hkm|]. split; [exact Hmeter|]. split; [exact Hnm|].
split.
{ destruct Hframe as (HF & Hfl & Hsh). subst F.
  destruct (frames_bounds SEGS B LAWS lyc Sc W mem md 4 pos HAR Hin4) as (B1 & B2 & _).
  change (fs_frame_bytes 4) with 1024 in B2.
  split; [reflexivity|]. split.
  - rewrite (rdword_ext (rdW W mem) (rdW W mem')); [exact Hfl|]. intros kk Hkk'.
    apply K; [lia | left; lia | apply (nerr_frame lyc Sc W mem md pos _ HAR Hin4); lia].
  - intros i Hi.
    pose proof (Z.div_mod (frame_addr lyc 4 pos) 8 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (frame_addr lyc 4 pos) 8 ltac:(lia)) as M.
    rewrite (K (shadow_addr (frame_addr lyc 4 pos) + Z.of_nat i)); [exact (Hsh i Hi) | | |];
      unfold shadow_addr, SHADOW_OFF in *.
    + lia.
    + left. lia.
    + apply nerr_hi. unfold kLowMemEnd. lia. }
split; [exact Hrv'|].
split.
{ intros j r Hj.
  assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length vr_saved_regs] in Hj13.
  intros kk Hkk. rewrite K; [exact (Hsaved j r Hj kk Hkk) | lia | right; lia | apply nerr_hi; lia]. }
split.
{ unfold vr_spill in *. rewrite Forall_forall in Hspill, Hsl |- *. intros ov Hov.
  pose proof (Hsl ov Hov) as Hb.
  intros kk Hkk. rewrite K; [exact (Hspill ov Hov kk Hkk) | lia | right; lia | apply nerr_hi; lia]. }
split.
{ destruct Henv as (HRO & _).
  assert (HRO' : arodata_okP SEGS RLO RHI B (rdW W mem')).
  { intros a Hro Ho He.
    assert (Hi : in_img SEGS a)
      by (destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]).
    pose proof (pa_img_range a Hi).
    rewrite K; [exact (HRO a Hro Ho He) | lia | left; lia | exact He]. }
  exact (vr_env_of_aro B MT RRO RPG RECC PROGU ROA lyc Sc W mem' md' HAR' HRO'). }
split.
{ apply (rec_repA_agree B _ _ _ _ _ _ Rc Oc Hrec (fun pn _ Hb => Hb)).
  - intros kk Hk.
    assert (G : A_G_REC <= A_G_REC + kk < A_G_REC + REC_SIZE) by (unfold A_G_REC, REC_SIZE in *; lia).
    pose proof (img_pg _ (vFPrec _ G)).
    apply K; [unfold A_G_REC, REC_SIZE in *; lia | left; lia | exact (nerr_pg _ (vFPrec _ G))].
  - intros kk Hk.
    assert (G : A_REC_SPILL <= A_REC_SPILL + kk < A_REC_SPILL + SC_SIZE) by (unfold A_REC_SPILL, SC_SIZE in *; lia).
    pose proof (img_pg _ (vFPspill _ G)).
    apply K; [unfold A_REC_SPILL, SC_SIZE in *; lia | left; lia | exact (nerr_pg _ (vFPspill _ G))].
  - intros [p n] Hpn kk Hk. cbn [fst snd] in *.
    pose proof (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as Hrq.
    apply K; [lia | left; lia | apply (nerr_block lyc Sc W mem md p n _ HAR Hin); lia]. }
split; [exact HdO|]. split; [exact Hperm|].
intros kk Hkk.
assert (G : A_G_QUITTING <= A_G_QUITTING + Z.of_nat kk < A_G_QUITTING + 4) by lia.
pose proof (img_pg _ (vFPquit _ G)).
rewrite K; [exact (Hquit kk Hkk) | unfold A_G_QUITTING in *; lia | left; lia | exact (nerr_pg _ (vFPquit _ G))].
Qed.

Lemma vr_line_kx : forall e q lyc Sc (W : world SEGS) mem md mem', vr_ent B MT e ->
AR SEGS B lyc Sc W mem md -> In (vr_lb e q) (ablocks B lyc Sc) ->
vr_line B e q W mem -> vr_kx e W mem mem' -> vr_line B e q W mem'.
Proof.
intros e q lyc Sc W mem md mem' Hent HAR Hin (Hfr & Hs) K. split; [exact Hfr|].
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _).
pose proof asan_consts as (C1 & _).
unfold vr_lb in Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as Hrs.
pose proof (line_le_strnlen (e_D e) (e_n e) HlenD) as Hll.
apply (astr_atR_agree (rdW W mem) (rdW W mem') q (Verbs.line (e_D e)) (vr_l (e_n e) (e_D e) + 1) Hs).
- unfold vr_l in *. lia.
- intros kk Hkk. apply K; [lia | left; lia | apply (nerr_block lyc Sc W mem md q _ _ HAR Hin); lia].
Qed.

Lemma vr_copy_kx : forall e F c tp pos lyc Sc (W : world SEGS) mem md mem', AR SEGS B lyc Sc W mem md ->
In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos -> In (vr_cb e c) (ablocks B lyc Sc) ->
vr_copy B e F c tp W mem -> vr_kx e W mem mem' -> vr_copy B e F c tp W mem'.
Proof.
intros e F c tp pos lyc Sc W mem md mem' HAR Hin4 HF Hin (Hfr & Hal & Hlen & Hptr & Hw) K. subst F.
pose proof asan_consts as (C1 & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md 4 pos HAR Hin4) as (B1 & B2 & _).
change (fs_frame_bytes 4) with 1024 in B2.
unfold vr_cb in Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrq.
assert (Htk : (length (Verbs.toks (e_D e)) <= 64)%nat)
  by (unfold Verbs.toks; rewrite length_firstn; unfold Verbs.line_words_max; lia).
split; [exact Hfr|]. split; [exact Hal|]. split; [exact Hlen|]. split.
- intros i p Hi.
  assert (Hi64 : (i < 64)%nat)
    by (rewrite <- Hlen in Htk; pose proof (proj1 (nth_error_Some tp i) ltac:(rewrite Hi; discriminate)); lia).
  intros kk Hkk. rewrite K; [exact (Hptr i p Hi kk Hkk) | lia | left; lia |].
  apply (nerr_frame lyc Sc W mem md pos _ HAR Hin4). lia.
- intros i p w Hi Hwi. destruct (Hw i p w Hi Hwi) as (Hs & Hl8 & Hp1 & Hp2).
  split; [|split; [exact Hl8 | split; [exact Hp1 | exact Hp2]]].
  apply (astr_atR_agree _ _ p w (Z.of_nat (length w) + 1) Hs); [lia|].
  intros kk Hkk. apply K; [lia | left; lia | apply (nerr_block lyc Sc W mem md c _ _ HAR Hin); lia].
Qed.

Lemma vr_s12 : vr_s12_stmt B MT.
Proof.
intros e W cf Hent Hrt.
destruct Hrt as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hne & Hcore & Hline & Hcopy).
pose proof Hcore as (HJ & _ & _ & _ & (EF & _) & Hrv & _ & Hspill & Henv & Hrec & _ & Hperm & _).
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & _ & Hcalls & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof (proj1 HJ) as HAR.
assert (R21 : getr regsc (Z_to_bv 5 21) = w64 (vr_ntok (e_D e)))
  by (apply (vr_rv_get regsc _ 21 _ Hrv); apply in_or_app; right; cbn; tauto).
assert (Hnt : 0 <= vr_ntok (e_D e) <= 64).
{ unfold vr_ntok, Verbs.toks, Verbs.line_words_max. rewrite length_firstn. lia. }
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & _).
assert (Hin4 : In (4, pos) (frames Sc))
  by (pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _); rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
assert (HES : ESTACK = ltac:(let v := eval vm_compute in ESTACK in exact v)) by reflexivity.
pose proof (vr_s1_cases e Hal16) as Hs1.
assert (Hs1lo : alloc_ceiling <= vr_s1 e) by lia.
assert (Hs1hi : vr_s1 e + 80 <= 2 ^ 64) by lia.
assert (Hs1o : (vr_s1 e - vr_sp0 e) mod 16 = 0)
  by (destruct Hs1 as [E|E]; rewrite E; [replace (vr_sp0 e - 192 - vr_sp0 e) with (-192) by lia
      | replace (vr_sp0 e - 208 - vr_sp0 e) with (-208) by lia]; reflexivity).
assert (Hsl40 : aval_mem (rdW W memc) (vr_s1 e + 40) 8 (F + 32)).
{ unfold vr_spill in Hspill. rewrite Forall_forall in Hspill.
  exact (Hspill (40, F + 32) ltac:(unfold vr_sl3; cbn; tauto)). }
assert (HRb : vr_rv regsc (vr_base B e)) by exact (proj1 (proj1 (vr_rv_app regsc _ _) Hrv)).
change (vr_pc (vr_route_pc VRR.RIinfo)) with (vr_pc 0x8d3f8).
replace (vr_pc 0x8d3f8) with (BASE + 0x6ec8) by (unfold vr_pc, AF_verbs_receive; lia).
unfold cfg_at, w64.
destruct (Nat.eq_dec (length (Verbs.toks (e_D e))) 2) as [H2 | H2].
- (* two words: atoi(tok[1]), sup_instance_info of its value, then the jump to JB *)
  destruct (route_iinfo _ Hroute) as (args & T).
  destruct args as [|a [|b r]]; [rewrite T in H2; cbn in H2; lia | | rewrite T in H2; cbn in H2; lia].
  assert (HlenP : length tp = 2%nat) by (destruct Hcopy as (_ & (_ & HlenP & _)); rewrite HlenP, H2; reflexivity).
  destruct tp as [|p0 [|p1 [|p2 tp']]]; cbn in HlenP; try lia.
  destruct (vtok_arg e F q c [p0; p1] lyc Sc W memc mdc 1 p1 a HAR Hperm Hcopy eq_refl
    ltac:(rewrite T; reflexivity)) as (_ & Hp1m & Hp14 & Hp1c & Ha8).
  assert (Hp1r : 0 <= p1 < 2 ^ 64) by lia.
  assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; left. right; left; reflexivity. }
  assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; left. left; reflexivity. }
  remember (Eimg (Ereg regsc [Z_to_bv 64 (F + 32); Z_to_bv 64 p1])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc [Z_to_bv 64 (F + 32); Z_to_bv 64 p1]) E) by (subst E; apply vr_env_agree).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 (F + 32))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        exact (ew_Ereg_extra regsc [Z_to_bv 64 (F + 32); Z_to_bv 64 p1] 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 p1)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        exact (ew_Ereg_extra regsc [Z_to_bv 64 (F + 32); Z_to_bv 64 p1] 1)).
  assert (HS : st_ok_pi SEGS VAL E (ss_tok 0x6ec8)
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 0x6ec8)) memc (seg_rom SEGS))))
    by (subst E; exact (vseed_tok e W regsc memc F p1 0x6ec8 HRb Hsl40 Hp1m ltac:(lia) ltac:(lia) Hs1lo Hs1hi Hp1r)).
  clear HE.
  (* 0x8d3f8: li a0,2 *)
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (rdeq_of_frame _ _ _ _ _ HFr (ro_tok 0)) as Eq1. clear HF HFr HG.
  (* 0x8d3fc: bne s5,a0,0x8d68c *)
  psrr_branch_pi RUNP BR HS.
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    unfold vr_ntok in Hc. rewrite H2 in Hc. vm_compute in Hc. discriminate Hc.
  + (* 0x8d400: li a0,-9; 0x8d404: ld s3,40(s1) *)
    clear Hc.
    paj_run_sh RUNP HS HJ.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    cbn [ms_mem mkst] in HFr.
    pose proof (rdeq_of_frame _ _ _ _ _ HFr (ro_tok 0)) as Eq2. clear HF HFr HG.
    (* 0x8d408: bltu a0,s3,0x8d938 — the UBSan check on tok + 8 *)
    psrr_branch_pi RUNP BR HS.
    * exfalso. rewrite branch_ltu_U in Hc. rewrite (U_atom E 32 _ E32) in Hc by lia.
      match type of Hc with (?x <? _) = true =>
        assert (Hx : x = 2 ^ 64 - 9) by (vm_compute; reflexivity); rewrite Hx in Hc end.
      apply Z.ltb_lt in Hc. lia.
    * (* 0x8d40c: ld a0,8(s3); 0x8d410: jal wrapper_atoi *)
      clear Hc.
      paj_run_shc RUNP RUNC HS HJ.
      { awr_ok_tac. }
      set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mat1 mdv2) in *. clearbody mdv3.
      pose proof (rdeq_of_frame _ _ _ _ _ HFr (ro_tok 0)) as Eq3. clear HF HFr HG.
      pose proof (fun x => eq_trans (Eq3 x) (eq_trans (Eq2 x) (Eq1 x))) as Eq.
      prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. rewrite E33 in Q10.
      prreg HS (19%bv : bv 5) Q19. rewrite E32 in Q19.
      pose proof (vr_kept_regs E _ _ regsc [Z_to_bv 64 (F + 32); Z_to_bv 64 p1] [2; 3; 4; 8; 9; 18; 21; 22; 24; 27]
        HS HAE ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
      pmkst HS.
      assert (Q2 : getr (ms_regs ms1) 2 = w64 (vr_s1 e)).
      { etransitivity; [exact (KR 2 ltac:(cbn; tauto))|].
        apply (vr_rv_get regsc _ 2 _ Hrv). apply in_or_app; left; cbn; tauto. }
      assert (Q3 : getr (ms_regs ms1) 3 = w64 (as_gp B)).
      { etransitivity; [exact (KR 3 ltac:(cbn; tauto))|].
        apply (vr_rv_get regsc _ 3 _ Hrv). apply in_or_app; left; cbn; tauto. }
      assert (Q4 : getr (ms_regs ms1) 4 = w64 (as_tp B)).
      { etransitivity; [exact (KR 4 ltac:(cbn; tauto))|].
        apply (vr_rv_get regsc _ 4 _ Hrv). apply in_or_app; left; cbn; tauto. }
      assert (Qsp : spZ (ms_regs ms1) = vr_sp0 e + (vr_s1 e - vr_sp0 e)).
      { unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
      assert (Hra : YK0s.ret_ok (getr (ms_regs ms1) 1))
        by (rewrite Q1; apply ret_ok_codeptr_v; first [lia | reflexivity | vm_compute; reflexivity]).
      pose proof (proj1 HJ) as HAR1.
      pose proof (vr_aro_kept B MT RRO RPG RECC PROGU ROA e _ lyc Sc W (ms_mem ms1) mdv3 k Hent HJ) as HRO1.
      pose proof (vr_env_of_aro B MT RRO RPG RECC PROGU ROA lyc Sc W (ms_mem ms1) mdv3 HAR1 HRO1) as Henv1.
      destruct Henv1 as (_ & _ & _ & Hgd1 & Hfl1 & (ev & Herr1)).
      pose proof (vr_copy_eq B e F c [p0; p1] W memc (ms_mem ms1) Eq Hcopy) as Hcopy1.
      pose proof Hcopy1 as (_ & (_ & _ & _ & Hw1)).
      destruct (Hw1 1%nat p1 a eq_refl ltac:(rewrite T; reflexivity)) as (A1 & A2 & A3 & A4).
      pose proof (ecall_pre_stk_at SEGS B (3 * ESTACK) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e)
        (e_mem e) (e_md e) [(4, pos)] lyc Sc W (ms_mem ms1) mdv3 k (ms_regs ms1) (vr_s1 e - vr_sp0 e) HJ Qsp Hs1o
        ltac:(lia) ltac:(lia) ltac:(lia) Hra Q3 Q4) as HPRE1.
      (* the atoi wrapper on tok[1] *)
      eapply SRr_bind.
      { eapply (ART (3 * ESTACK) (aerrno_cell B) _ W (ms_regs ms1) (ms_mem ms1) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e)
          (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdv3 k (vr_s1 e - vr_sp0 e) _ _ HJ);
          [exact Qsp | exact Hs1o | lia | lia | lia | exact Q1 | intros a0 Ha0; exact Ha0 |].
        apply (AATOI fx lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv3 p1 a ev Hfl1 Hgd1 HPRE1 Q10 ltac:(lia)).
        - apply astr_atR_view. exact A1.
        - apply (aread_ok_of_block SEGS B LAWS (3 * ESTACK) lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv3 c
            (Z.of_nat (length (Verbs.line (e_D e))) + 1) p1 (astr_len a + 1) HAR1 Hcb); unfold astr_len;
            [lia | lia | lia |].
          rewrite Qsp. lia.
        - apply (amem8_of_blockA SEGS B LAWS lyc Sc W (ms_mem ms1) mdv3); [exact HAR1 | | unfold astr_len; lia].
          exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1). split; [exact Hcb | unfold astr_len; lia].
        - unfold astr_len. apply (BLKT lyc Sc W (ms_mem ms1) mdv3 c (Z.of_nat (length (Verbs.line (e_D e))) + 1));
            [exact HAR1 | exact Hcb | lia].
        - exact Herr1.
        - (* tok[1] apart from the errno cell: its bytes are in the copy block, not image bytes (blk_img); the
             errno cell's are (ENV, api_env) *)
          pose proof ENV as (_ & Hzi & _).
          destruct (Z_le_gt_dec (p1 + astr_len a + 1) (as_errno B)) as [Hz1|Hz1]; [left; exact Hz1|].
          destruct (Z_le_gt_dec (as_errno B + 4) p1) as [Hz2|Hz2]; [right; exact Hz2|]. exfalso.
          apply (blk_img SEGS B LAWS lyc Sc W (ms_mem ms1) mdv3 c (Z.of_nat (length (Verbs.line (e_D e))) + 1)
            (Z.max p1 (as_errno B)) HAR1 Hcb); [| apply Hzi; clear - Hz1 Hz2; lia].
          unfold req_size. destruct (Z.eqb_spec (Z.of_nat (length (Verbs.line (e_D e))) + 1) 0) as [Hzk|Hzk]; cbv iota;
            clear - A3 A4 Hz1 Hzk; unfold astr_len in Hz1; lia.
        - exact (vr_rtrom_ok B W (ms_mem ms1) HRO1). }
      cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HA0 & _) & HK2).
      (* 0x8d414: jal sup_instance_info, from a state that names only the registers *)
      remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
      assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
      assert (HAE2 : env_agree 32 (Ereg regs2 []) E2) by (subst E2; apply vr_env_agree).
      assert (HS2 : st_ok_pi SEGS VAL E2 (vr_ss0 0x6ee4)
        (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + 0x6ee4)) mem2 (seg_rom SEGS))))
        by (subst E2; apply vr_seed0).
      clear HE2.
      paj_run_shc RUNP RUNC HS2 HJ2.
      { awr_ok_tac. }
      match goal with |- context [with_vm_backing (m_vm_lazy md2) ?mt md2] =>
        set (mdv4 := with_vm_backing (m_vm_lazy md2) mt md2) in * end.
      clearbody mdv4.
      pose proof (rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq4. clear HF HFr HG.
      prreg HS2 (1%bv : bv 5) Q1b.
      pose proof (vr_kept_regs E2 _ _ regs2 [] [2; 3; 4; 8; 9; 10; 18; 19; 21; 22; 24; 27] HS2 HAE2
        ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
      pmkst HS2.
      rewrite (SIGP CS_sup_instance_info) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
      change (cmd_af CS_sup_instance_info) with AF_sup_instance_info.
      assert (KRall : forall r, In r [2; 3; 4; 8; 9; 18; 21; 22; 24; 27] ->
        getr (ms_regs ms2) (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)).
      { intros r0 Hr0.
        rewrite (KR2 r0 ltac:(cbn in Hr0 |- *; tauto)).
        rewrite (HP2 r0 ltac:(unfold acallee_saved; cbn in Hr0; lia)).
        apply KR. exact Hr0. }
      assert (Q19b : getr (ms_regs ms2) 19 = w64 (F + 32)).
      { etransitivity; [exact (KR2 19 ltac:(cbn; tauto))|]. rewrite (HP2 19 ltac:(unfold acallee_saved; lia)). exact Q19. }
      assert (Q10b : getr (ms_regs ms2) 10 = w64 (atoi_a a)).
      { etransitivity; [exact (KR2 10 ltac:(cbn; tauto))|]. exact HA0. }
      assert (KX : vr_kx e W memc (ms_mem ms2)).
      { intros a0 Ha0 Hb Hn. rewrite (Eq4 a0), (HK2 a0 Ha0); [exact (Eq a0) | | exact Hn]. lia. }
      assert (Hsl : Forall (fun ov => 0 <= fst ov <= 200) (vr_sl3 F q c)).
      { apply Forall_forall. intros [o v] Hin. unfold vr_sl3 in Hin. cbn in Hin.
        repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; cbn; lia|]). destruct Hin. }
      assert (Hcs : vr_cs B MT e pos F q c (atoi_a a) 0x6ee8 [p0; p1] lyc Sc W (ms_regs ms2) (ms_mem ms2) mdv4 k nm).
      { split; [|split; [exact (vr_line_kx e q lyc Sc W memc mdc (ms_mem ms2) Hent HAR Hlb Hline KX)
                       | exact (vr_copy_kx e F c [p0; p1] pos lyc Sc W memc mdc (ms_mem ms2) HAR Hin4 EF Hcb Hcopy KX)]].
        apply (vr_core_kx e pos F _ _ _ _ _ _ _ _ k _ nm _ lyc Sc W regsc memc mdc (ms_regs ms2) (ms_mem ms2) mdv4
          Hent Hcore HJ2 KX Hsl).
        apply (vrv_keep e (ms_regs ms2) regsc _ _ Hrv).
        - intros r0 Hr0. apply KRall. cbn in Hr0 |- *. tauto.
        - intros r0 v Hin. cbn in Hin.
          destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]; injection E1 as <- <-.
          + right. exact Q1b.
          + right. exact Q10b.
          + left. split; [cbn; tauto | apply KRall; cbn; tauto].
          + right. exact Q19b.
          + left. split; [cbn; tauto | apply KRall; cbn; tauto].
          + left. split; [cbn; tauto | apply KRall; cbn; tauto]. }
      assert (Hid : -2 ^ 31 <= atoi_a a < 2 ^ 31) by (unfold atoi_a; apply swrap32_range).
      pose proof (dec_length (atoi_a a) Hid) as Hdec.
      assert (Ht : (length (snd (sup_instance_info_m (e_R e) (atoi_a a))) <= 28)%nat).
      { unfold sup_instance_info_m, daemon_shape. apply stub_len.
        exact (rec_code_range B MT RRO RPG RECC PROGU ROA HB MTL _ _ _ _ _ Hrec). }
      eapply SRr_mono.
      { apply (vcall_arm e W pos F q c (atoi_a a) 0x6ee8 [p0; p1] lyc Sc
          (ms_regs ms2) (ms_mem ms2) mdv4 k nm AF_sup_instance_info SUP_INSTANCE_INFO_STK
          (EV_SUP_INSTANCE_INFO (e_R e))
          (XM_SUP_INSTANCE_INFO MT (e_R e) (atoi_a a)) (LIVE_SUP_INSTANCE_INFO (e_R e) (atoi_a a))
          (sup_instance_info_m (e_R e) (atoi_a a)) Hent Hcs H2).
        - exact (proj1 (iinfo_call (e_R e) (e_D e) a T)).
        - exact (proj2 (iinfo_call (e_R e) (e_D e) a T)).
        - unfold EV_SUP_INSTANCE_INFO, EV_RECORD, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC.
          rewrite (spill_frees0 _ Hcalls). lia.
        - unfold XM_SUP_INSTANCE_INFO, XM_RECORD, XM_ARG_S, XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC.
          rewrite (spill_frees0 _ Hcalls).
          pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length (sarg (Some (dec (atoi_a a))))) + 1) 1)
            VERBS_RECEIVE_REQ ltac:(unfold sarg, VERBS_RECEIVE_REQ; lia)) as M1.
          pose proof (mo_malloc_mono MT MTL
            (Z.max (Z.of_nat (length (snd (sup_instance_info_m (e_R e) (atoi_a a)))) + 1) 1) VERBS_RECEIVE_REQ
            ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M2.
          lia.
        - unfold LIVE_SUP_INSTANCE_INFO, LIVE_ARG_S, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC, VERBS_RECEIVE_REQ.
          unfold sarg. lia.
        - assert (HV : SUP_INSTANCE_INFO_STK
            = ltac:(let v := eval vm_compute in SUP_INSTANCE_INFO_STK in exact v)) by reflexivity. lia.
        - assert (HV : SUP_INSTANCE_INFO_STK
            = ltac:(let v := eval vm_compute in SUP_INSTANCE_INFO_STK in exact v)) by reflexivity. lia.
        - lia.
        - reflexivity.
        - vm_compute; reflexivity.
        - intros ch HPRE2 HF0 H1 H2' H3 H4 H5 H6 H7.
          exact (TSUP_INSTANCE_INFO fx lyc Sc W (ms_regs ms2) (ms_mem ms2) mdv4 ch (atoi_a a) (e_R e) (e_O e)
            HPRE2 HF0 H1 H2' Q10b Hid H3 ltac:(lia) H5 H6 H7). }
      intros W' c' _ (fq & Hfq & H). exists fq. split; [exact Hfq|]. right. exact H.
- (* not two words: the refusal stub 0x8d68c *)
  pose proof (iinfo_rej (e_R e) (e_D e) Hroute H2) as Hrj.
  remember (Eimg (Ereg regsc [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply vr_env_agree).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (HS : st_ok_pi SEGS VAL E (vr_ss0 0x6ec8)
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 0x6ec8)) memc (seg_rom SEGS))))
    by (subst E; apply vr_seed0).
  clear HE.
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq1. clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  + paj_run_to_shc RUNTO HS HJ 0x715c.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    pose proof (rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq2. clear HF HFr HG.
    pose proof (fun x => eq_trans (Eq2 x) (Eq1 x)) as Eq.
    pose proof (vr_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 18; 21; 22; 24; 27] HS HAE
      ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply SRr_ret. cbv beta. exists fx. split; [apply fxrel_refl|]. left. unfold vrF_pr, vr_atpr.
    replace (BASE + 29020) with (vr_pc 0x8d68c) by (unfold vr_pc, AF_verbs_receive; lia).
    apply (vpr_build e W pos F q c tp lyc Sc (ms_regs ms0) (ms_mem ms0) mdv2 k nm
      (proj1 Hrj) (proj2 Hrj) Hne).
    * apply (vcore_move e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc _ _ 2 VR_NM_PRE
        (ms_regs ms0) (ms_mem ms0) mdv2 Hcore HJ Eq).
      -- apply (vrv_keep e (ms_regs ms0) regsc _ _ Hrv).
         ++ intros r0 Hr0. apply KR. cbn in Hr0 |- *. tauto.
         ++ intros r0 v Hin. left. cbn in Hin.
            destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-;
            (split; [cbn; tauto | apply KR; cbn; tauto]).
      -- apply incl_refl.
      -- lia.
      -- lia.
    * exact (vr_line_eq B e q W memc (ms_mem ms0) Eq Hline).
    * exact (vr_copy_eq B e F c tp W memc (ms_mem ms0) Eq Hcopy).
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    change (U E (SLit 2)) with 2 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold vr_ntok in Hc. lia.
Qed.

End e.
End f.
End d.
