(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S27 (INST, 0x8d830-0x8d86c, 16 instructions) of the walk of
   verbs_receive on the ASan+UBSan build (image B) of plugin-hostd/fuzz_command: `vr_s27_stmt` of
   lib/B/Prog/verbs_receive_iface.v. The B twin of lib/A/Prog/verbs_receive_s27.v (A 0x8ddc0-0x8ddec).

     8d830 mv a0,s10 ; 8d834 jal is_instance_verb
     8d838 li a1,1 ; 8d83c beq s5,a1,8d8c4 ; 8d840 beqz a0,8d8c4      -> S28 (vr_s28in)
     8d844 li a0,-9 ; 8d848 ld s6,24(s1) ; 8d84c ld s11,32(s1) ; 8d850 ld s2,56(s1) ; 8d854 ld s3,40(s1)
     8d858 bltu a0,s3,8d938                                            (UBSan: tok + 8 wraps; never taken)
     8d85c ld a0,8(s3) ; 8d860 jal __interceptor_trampoline_atoi       (a0 = tok[1])
     8d864 mv a1,s2 ; 8d868 jal sup_call                               (atoi(tok[1]), line)
     8d86c j 8d4cc                                                     -> JB (vr_hd 0x8d4cc)

   B-only: the four reloads 0x8d848-0x8d854 (B keeps F, shadow_addr F + 4, the line and tok in the frame slots
   s1+24, s1+32, s1+56, s1+40 and reloads them before the arm; A read tok and the line from s1+16 / s1+24 around
   the calls) and the UBSan check 0x8d858 (`li a0,-9` / `bltu a0,s3`: taken only when tok = F + 32 > 2^64 - 9; F is
   this call's class-4 frame, below alloc_ceiling, so the trap branch is refuted by lia).

   The walk is cgif_file_fuzzer's: the verified symbolic executor over the position-abstract listing
   (lib/B/Prog/CmdList.v; PaLibF's SRr_run_pi_AJ, PaCallRun's SRr_run_pi_AJ_call), a fresh symbolic state seeded at
   each leg, the frameless is_instance_verb through PaNoChain's cl_callS_na (q_na_call), sup_call through
   PaFx's cl_callS_wideF (q_rcallF) and their statements, the atoi wrapper through a Theorem Labs lane's
   aatoi_realizes and PaArt's aj_art_at. Leg A runs to the return of is_instance_verb (s27_R); leg B takes the two
   branches; leg C, on an instance verb with an argument, the reloads, the check, the atoi and sup_call calls and the
   jump to JB. sup_call is printf-reaching (apost_baseF): it returns at some FP state fx' with fxrel fx fx', and the
   jump to JB runs at fx' (q_jmp is FP-generic), so the segment is stated with vr_segF. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route verbs_receive_pre.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c arg_line_c answer_c hand_back_c rec_canonical_c xmalloc_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_live verbs_receive_s2728_fn verbs_receive_s2728_st
PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module VQ7 := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the listing offsets this segment names: AF_verbs_receive + (pc - 0x8ce4c), AF_verbs_receive = 0x691c *)
Definition S27_A : Z := 29440.   (* 0x8d830 *)
Definition S27_B : Z := 29448.   (* 0x8d838, after is_instance_verb *)
Definition S27_D : Z := 29492.   (* 0x8d864, after atoi *)
Definition S27_E : Z := 29500.   (* 0x8d86c, after sup_call *)
Definition S27_JB : Z := 28572.  (* 0x8d4cc *)
Definition S27_28 : Z := 29588.  (* 0x8d8c4 *)

(* the model: the word, and the routes behind route_conn *)
Definition s27_iv (D : list byte) : Z := if Verbs.is_instance_verb (hd [] (Verbs.toks D)) then 1 else 0.

Lemma s27_cd_one : forall v, VQ7.route_conn v [] = VQ7.route_cd v [].
Proof. reflexivity. Qed.

Lemma s27_cd_noinst : forall v a rest, Verbs.is_instance_verb v = false ->
VQ7.route_conn v (a :: rest) = VQ7.route_cd v (a :: rest).
Proof. intros v a rest H. unfold VQ7.route_conn. rewrite H. reflexivity. Qed.

Lemma s27_inst : forall v a rest, Verbs.is_instance_verb v = true ->
VQ7.route_conn v (a :: rest) = VQ7.RInst.
Proof. intros v a rest H. unfold VQ7.route_conn. rewrite H. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* at every FP state f: the exit after sup_call is at the FP state it returns *)
Lemma s27_cfg : forall (f : YK11.FPState) regs mem md pc off, off = AF_verbs_receive + (pc - 0x8ce4c) ->
mkCfg (@mkst f regs (Z_to_bv 64 (BASE + off)) mem (seg_rom SEGS)) md = cfg_at (fx := f) SEGS (vr_pc pc) regs mem md.
Proof. intros f regs mem md pc off Ho. unfold cfg_at, vr_pc, w64. rewrite Ho. reflexivity. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callee contracts and the runtime entry in the statement's fx-generic form (lib/B/Prog/verbs_receive_c.v:232,
   :241, :277) and the record facts of the brief, with their names; TL is the per-listing record PALib, which the
   assembly takes from CmdRecRest's cmd_palib at the pinned listing *)
Hypothesis TIS_INSTANCE_VERB : forall fx0 : YK11.FPState, @tis_instance_verb_spec fx0 rc SK PI B MT.
Hypothesis TSUP_CALL : forall fx0 : YK11.FPState, @tsup_call_spec fx0 rc SK PI B MT.
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
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let ART := aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL).

(* ---------------------------------------------------------------------------------------------------------------
   Across the atoi call: memory that agrees below the allocation ceiling and from the realigned stack pointer up,
   except at the errno cell (aj_art_at's frame for aatoi_realizes, whose window is below vr_s1); the S12 lane's
   vr_kx (a working branch 1413152415c, verbs_receive_s12.v), on the fixed interface *)
Definition s27_kx (e : vrE) (W : world SEGS) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ vr_s1 e <= a) -> ~ aerrno_cell B a -> rdW W m' a = rdW W m a.

Lemma s27_nerr_hi : forall a, kLowMemEnd <= a -> ~ aerrno_cell B a.
Proof. intros a Ha He. pose proof (pal_env B TL) as ((E0 & E1) & _). unfold aerrno_cell in He. lia. Qed.
Lemma s27_nerr_img : forall a, ~ in_img SEGS a -> ~ aerrno_cell B a.
Proof. intros a Ha He. pose proof (pal_env B TL) as (_ & EI & _). exact (Ha (EI a He)). Qed.
Lemma s27_nerr_frame : forall lyc Sc (W : world SEGS) mem md pos a, AR SEGS B lyc Sc W mem md -> In (4, pos) (frames Sc) ->
frame_addr lyc 4 pos <= a < frame_addr lyc 4 pos + 1024 -> ~ aerrno_cell B a.
Proof.
intros lyc Sc W mem md pos a HAR Hin Ha. apply s27_nerr_img. apply (frm_img SEGS B LAWS lyc Sc W mem md 4 pos a HAR Hin).
change (fs_frame_bytes 4) with 1024. exact Ha.
Qed.
Lemma s27_nerr_block : forall lyc Sc (W : world SEGS) mem md p n a, AR SEGS B lyc Sc W mem md -> In (p, n) (ablocks B lyc Sc) ->
p <= a < p + req_size n -> ~ aerrno_cell B a.
Proof. intros lyc Sc W mem md p n a HAR Hin Ha. apply s27_nerr_img. exact (blk_img SEGS B LAWS lyc Sc W mem md p n a HAR Hin Ha). Qed.
Lemma s27_nerr_pg : forall a, inFP cmd_PG a -> ~ aerrno_cell B a.
Proof. intros a Ha. destruct (PROGU a Ha) as (_ & _ & He). exact He. Qed.
Lemma s27_img_pg : forall a, inFP cmd_PG a -> a < 0x606000.
Proof. intros a Ha. destruct (PROGU a Ha) as (Hi & _). exact (proj2 (pa_img_range a Hi)). Qed.

Lemma s27_core_kx : forall e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md regs' mem' md',
vr_ent B MT e ->
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  [(4, pos)] lyc Sc W mem' md' k ->
s27_kx e W mem mem' ->
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
destruct (s28_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
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
    apply K; [lia | left; lia | apply (s27_nerr_frame lyc Sc W mem md pos _ HAR Hin4); lia].
  - intros i Hi.
    pose proof (Z.div_mod (frame_addr lyc 4 pos) 8 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (frame_addr lyc 4 pos) 8 ltac:(lia)) as M.
    rewrite (K (shadow_addr (frame_addr lyc 4 pos) + Z.of_nat i)); [exact (Hsh i Hi) | | |];
      unfold shadow_addr, SHADOW_OFF in *.
    + lia.
    + left. lia.
    + apply s27_nerr_hi. unfold kLowMemEnd. lia. }
split; [exact Hrv'|].
split.
{ intros j r Hj.
  assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length vr_saved_regs] in Hj13.
  intros kk Hkk. rewrite K; [exact (Hsaved j r Hj kk Hkk) | lia | right; lia | apply s27_nerr_hi; lia]. }
split.
{ unfold vr_spill in *. rewrite Forall_forall in Hspill, Hsl |- *. intros ov Hov.
  pose proof (Hsl ov Hov) as Hb.
  intros kk Hkk. rewrite K; [exact (Hspill ov Hov kk Hkk) | lia | right; lia | apply s27_nerr_hi; lia]. }
split.
{ destruct Henv as (HRO & _).
  assert (HRO' : arodata_okP SEGS RLO RHI B (rdW W mem')).
  { intros a Hro Ho He.
    assert (Hi : in_img SEGS a) by exact (vr_roP_img RRO a Hro).
    pose proof (pa_img_range a Hi).
    rewrite K; [exact (HRO a Hro Ho He) | lia | left; lia | exact He]. }
  exact (vr_env_of B ROA RECC _ _ _ _ _ HAR' HRO'). }
split.
{ apply (rec_repA_agree B _ _ _ _ _ _ Rc Oc Hrec (fun pn _ Hb => Hb)).
  - intros kk Hk.
    assert (G : inFP cmd_PG (A_G_REC + kk)) by (apply s28_pg_img; left; left; unfold REC_SIZE in *; lia).
    pose proof (s27_img_pg _ G).
    apply K; [unfold A_G_REC, REC_SIZE in *; lia | left; lia | exact (s27_nerr_pg _ G)].
  - intros kk Hk.
    assert (G : inFP cmd_PG (A_REC_SPILL + kk)) by (apply s28_pg_img; left; right; unfold SC_SIZE in *; lia).
    pose proof (s27_img_pg _ G).
    apply K; [unfold A_REC_SPILL, SC_SIZE in *; lia | left; lia | exact (s27_nerr_pg _ G)].
  - intros [p n] Hpn kk Hk. cbn [fst snd] in *.
    pose proof (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as Hrq.
    apply K; [lia | left; lia | apply (s27_nerr_block lyc Sc W mem md p n _ HAR Hin); lia]. }
split; [exact HdO|]. split; [exact Hperm|].
intros kk Hkk.
assert (G : inFP cmd_PG (A_G_QUITTING + Z.of_nat kk)) by (apply s28_pg_img; right; lia).
pose proof (s27_img_pg _ G).
rewrite K; [exact (Hquit kk Hkk) | unfold A_G_QUITTING in *; lia | left; lia | exact (s27_nerr_pg _ G)].
Qed.

Lemma s27_line_kx : forall e q lyc Sc (W : world SEGS) mem md mem', vr_ent B MT e ->
AR SEGS B lyc Sc W mem md -> In (vr_lb e q) (ablocks B lyc Sc) ->
vr_line B e q W mem -> s27_kx e W mem mem' -> vr_line B e q W mem'.
Proof.
intros e q lyc Sc W mem md mem' Hent HAR Hin (Hfr & Hs) K. split; [exact Hfr|].
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _).
pose proof asan_consts as (C1 & _).
unfold vr_lb in Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as Hrs.
pose proof (vr_line_le_l (e_n e) (e_D e) HlenD) as Hll.
apply (astr_atR_agree (rdW W mem) (rdW W mem') q (Verbs.line (e_D e)) (vr_l (e_n e) (e_D e) + 1) Hs).
- lia.
- intros kk Hkk. apply K; [lia | left; lia | apply (s27_nerr_block lyc Sc W mem md q _ _ HAR Hin); lia].
Qed.

Lemma s27_copy_kx : forall e F c tp pos lyc Sc (W : world SEGS) mem md mem', AR SEGS B lyc Sc W mem md ->
In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos -> In (vr_cb e c) (ablocks B lyc Sc) ->
vr_copy B e F c tp W mem -> s27_kx e W mem mem' -> vr_copy B e F c tp W mem'.
Proof.
intros e F c tp pos lyc Sc W mem md mem' HAR Hin4 HF Hin (Hfr & Hal & Hlen & Hptr & Hw) K. subst F.
pose proof asan_consts as (C1 & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md 4 pos HAR Hin4) as (B1 & B2 & _).
change (fs_frame_bytes 4) with 1024 in B2.
unfold vr_cb in Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrq.
pose proof (s28_toks_le (e_D e)) as Htk.
split; [exact Hfr|]. split; [exact Hal|]. split; [exact Hlen|]. split.
- intros i p Hi.
  assert (Hi64 : (i < 64)%nat)
    by (rewrite <- Hlen in Htk; pose proof (proj1 (nth_error_Some tp i) ltac:(rewrite Hi; discriminate)); lia).
  intros kk Hkk. rewrite K; [exact (Hptr i p Hi kk Hkk) | lia | left; lia |].
  apply (s27_nerr_frame lyc Sc W mem md pos _ HAR Hin4). lia.
- intros i p w Hi Hwi. destruct (Hw i p w Hi Hwi) as (Hs & Hl8 & Hp1 & Hp2).
  split; [|split; [exact Hl8 | split; [exact Hp1 | exact Hp2]]].
  apply (astr_atR_agree _ _ p w (Z.of_nat (length w) + 1) Hs); [lia|].
  intros kk Hkk. apply K; [lia | left; lia | apply (s27_nerr_block lyc Sc W mem md c _ _ HAR Hin); lia].
Qed.

Lemma s27_sl3 : forall F q c, Forall (fun ov => 0 <= fst ov <= 200) (vr_sl3 F q c).
Proof. intros F q c. unfold vr_sl3. repeat constructor; cbn [fst]; lia. Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Leg A: from 0x8d830, the call of is_instance_verb(tok[0]), to its return at 0x8d838 *)
Definition s27_rlR (e : vrE) (tp : list Z) : list (Z * Z) :=
[(10, s27_iv (e_D e)); (21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, hd 0 tp)].

Definition s27_R (e : vrE) : world SEGS -> config -> Prop := fun Wc cf =>
exists pos F q c tp lyc Sc regsc memc mdc k nm,
cf = mkCfg (mkst regsc (Z_to_bv 64 (BASE + S27_B)) memc (seg_rom SEGS)) mdc /\
(match Verbs.toks (e_D e) with
 | v :: args => Verbs.ledger_of v Verbs.Lit.instance_info_verbs = None /\ VQ7.route (v :: args) = VQ7.route_conn v args
 | [] => False end) /\
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (s27_rlR e tp)
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc Wc regsc memc mdc /\
vr_line B e q Wc memc /\ vr_copy B e F c tp Wc memc.

(* the events of the walk leave room for the frameless calls *)
Lemma s27_ev4 : forall e v args, Verbs.toks (e_D e) = v :: args ->
VQ7.route (v :: args) = VQ7.route_conn v args -> 2 + 0 <= ev_vr (e_R e) (e_D e).
Proof.
intros e v args Et Hrc. pose proof (vr_k1_ge2 (e_R e) (e_D e) v args Et Hrc).
pose proof (q_k1_ev (e_R e) (e_D e)). pose proof s28_ev_reply. lia.
Qed.

Lemma s27_A : forall e W cf, vr_ent B MT e -> vr_s27in B MT e W cf -> SRr SEGS W cf (s27_R e).
Proof.
intros e W cf Hent Hin.
destruct Hin as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hcore & Hline & Hcopy).
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & _ & Hcalls & _ & _ & _ & _ & _
  & _ & _ & _ & _ & VOBJS & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (s28_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _).
destruct (Verbs.toks (e_D e)) as [|v args] eqn:Et; [contradiction|].
destruct Hroute as [Hled Hrc].
pose proof Hcopy as (_ & (_ & HlenP & _)).
destruct tp as [|p0 tps]; [rewrite Et in HlenP; discriminate HlenP|].
assert (Hrows : forall r val, In (r, val) (vr_base B e ++ [(21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, hd 0 (p0 :: tps))]) ->
  getr regsc (Z_to_bv 5 r) = w64 val) by (intros r val Hi; exact (vr_rv_get _ _ r val Hrv Hi)).
assert (R26 := Hrows 26 p0 ltac:(unfold vr_base; cbn [app In hd]; tauto)).
rewrite <- (s27_cfg fx regsc memc mdc 0x8d830 S27_A ltac:(unfold S27_A, AF_verbs_receive; lia)).
pose proof (q_seed0 W regsc memc S27_A) as HS.
remember (Eimg (Ereg regsc [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply q_env_agree).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
  set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
clearbody mdv.
pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq1. clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), R26 in Q10.
pose proof (q_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 21; 25; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
rewrite (SIGP CS_is_instance_verb) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_is_instance_verb) with AF_is_instance_verb.
(* the state at the callee's entry *)
assert (HcoreM : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(1, BASE + S27_B); (21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, p0)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs ms) (ms_mem ms) mdv).
{ apply (q_core_same B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc W (ms_regs ms) (ms_mem ms) mdv
    Hcore HJ Eq1).
  apply (q_rv_keep B e (ms_regs ms) regsc _ _ Hrv).
  - intros r Hr. apply KR. cbn in Hr |- *. tauto.
  - intros r val Hi. cbn in Hi. destruct Hi as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-.
    + right. exact Q1.
    + left. split; [cbn; tauto | apply KR; cbn; tauto].
    + left. split; [cbn; tauto | apply KR; cbn; tauto].
    + left. split; [cbn; tauto | apply KR; cbn; tauto]. }
pose proof (q_line_same B e q W memc W (ms_mem ms) Eq1 Hline) as HlineM.
pose proof (q_copy_same B e F c (p0 :: tps) W memc W (ms_mem ms) Eq1 Hcopy) as HcopyM.
pose proof HcoreM as (HJm & _ & _ & _ & _ & _ & _ & _ & HenvM & _).
pose proof HenvM as (HROm & _ & HROkm & _).
destruct (q_tok_arg B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c (p0 :: tps) 0%nat p0 v HcoreM
  (or_intror (or_introl eq_refl)) HcopyM eq_refl ltac:(rewrite Et; reflexivity))
  as ((Hib & _ & Hstr & Hlm) & _ & Hp04 & Hp0c & _).
pose proof (q_nev B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W _ _ _ EV_IS_INSTANCE_VERB Hent HcoreM
  (s27_ev4 e v args Et Hrc)) as Hnev.
assert (HSI : IS_INSTANCE_VERB_STK = 8272) by reflexivity.
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
eapply SRr_bind.
{ apply (q_na_call B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs ms) (ms_mem ms) mdv AF_is_instance_verb
    IS_INSTANCE_VERB_STK EV_IS_INSTANCE_VERB S27_B
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
       getr regs' 10 = w64 (if existsb (Verbs.verb_is_m v) Verbs.Lit.instance_verb_formats then 1 else 0) /\
       Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\ ly' = lyc /\ S' = Sc) HcoreM Hal16).
  - exact Q1.
  - unfold S27_B. lia.
  - reflexivity.
  - lia.
  - lia.
  - intros HPRE1.
    exact (TIS_INSTANCE_VERB fx lyc Sc W (ms_regs ms) (ms_mem ms) mdv p0 v HPRE1 HROm Q10 ltac:(lia) Hib Hstr Hlm
      HROkm VOBJS Hnev). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & (Ha0 & _ & -> & ->)).
change EV_IS_INSTANCE_VERB with 0 in HJ2. rewrite Z.add_0_r in HJ2.
assert (Hrv2 : vr_rv regs2 (vr_base B e ++ s27_rlR e (p0 :: tps))).
{ apply (q_rv_keep B e regs2 (ms_regs ms) _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HcoreM))))))).
  - intros r Hr. apply HP. unfold acallee_saved. cbn in Hr. lia.
  - intros r val Hi. unfold s27_rlR in Hi. cbn in Hi. destruct Hi as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-.
    + right. unfold s27_iv. rewrite Et. cbn [hd]. unfold Verbs.is_instance_verb. exact Ha0.
    + left. split; [cbn; tauto | apply HP; unfold acallee_saved; lia].
    + left. split; [cbn; tauto | apply HP; unfold acallee_saved; lia].
    + left. split; [cbn; tauto | apply HP; unfold acallee_saved; lia]. }
destruct (q_keep_na B MT ROA RRO RPG RECC PROGU e pos F q c (p0 :: tps) [vr_lb e q; vr_cb e c] _ (s27_rlR e (p0 :: tps))
  (e_R e) (e_O e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs ms) (ms_mem ms) mdv IS_INSTANCE_VERB_STK EV_IS_INSTANCE_VERB
  W2 regs2 mem2 md2 Hent HcoreM HlineM HcopyM (or_introl eq_refl) (or_intror (or_introl eq_refl)) HJc HJ2 Hrv2)
  as (Hc2 & Hl2 & Hcp2).
apply SRr_ret.
exists pos, F, q, c, (p0 :: tps), lyc, Sc, regs2, mem2, md2, k, nm.
split; [reflexivity|]. split; [rewrite Et; split; [exact Hled | exact Hrc]|].
split; [exact Hc2|]. split; [exact Hl2 | exact Hcp2].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Leg B: the two branches at 0x8d83c and 0x8d840; a single word or a verb that is not an instance verb leaves for
   S28 at 0x8d8c4, an instance verb with an argument goes on at 0x8d844 (s27_I) *)
Definition S27_C : Z := 29460.   (* 0x8d844 *)

Definition s27_I (e : vrE) : world SEGS -> config -> Prop := fun Wc cf =>
exists pos F q c tp lyc Sc regsc memc mdc k nm,
cf = mkCfg (mkst regsc (Z_to_bv 64 (BASE + S27_C)) memc (seg_rom SEGS)) mdc /\
(match Verbs.toks (e_D e) with
 | v :: a :: rest => VQ7.route (v :: a :: rest) = VQ7.RInst
 | _ => False end) /\
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, hd 0 tp)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc Wc regsc memc mdc /\
vr_line B e q Wc memc /\ vr_copy B e F c tp Wc memc.

(* the state at a pc reached by a run that kept the memory and the registers of the boundary *)
Lemma s27_kept : forall e pos F q c tp lyc Sc (W : world SEGS) regsc memc mdc k nm rl rl' regs' mem' md',
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE
  lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem' md' k ->
q_rdeq (rdW W memc) (rdW W mem') ->
(forall r v, In (r, v) rl' -> In (r, v) rl) ->
(forall r, In r [2; 3; 4; 8; 9; 21; 25; 26] -> getr regs' (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) ->
(forall r v, In (r, v) rl' -> In r [21; 25; 26]) ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl' (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE
  lyc Sc W regs' mem' md' /\ vr_line B e q W mem' /\ vr_copy B e F c tp W mem'.
Proof.
intros e pos F q c tp lyc Sc W regsc memc mdc k nm rl rl' regs' mem' md' Hcore Hline Hcopy HJ' Eq Hsub KR Hr.
pose proof Hcore as (_ & _ & _ & _ & _ & Hrv & _).
split; [|split; [exact (q_line_same B e q W memc W mem' Eq Hline) | exact (q_copy_same B e F c tp W memc W mem' Eq Hcopy)]].
apply (q_core_same B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc W regs' mem' md' Hcore HJ' Eq).
apply (q_rv_keep B e regs' regsc rl rl' Hrv).
- intros r Hr0. apply KR. cbn in Hr0 |- *. tauto.
- intros r v Hi. left. split; [exact (Hsub r v Hi)|]. apply KR. pose proof (Hr r v Hi) as Hr1. cbn in Hr1 |- *. tauto.
Qed.

Lemma s27_B : forall e W cf, vr_ent B MT e -> s27_R e W cf ->
SRr SEGS W cf (vr_or s27_I (vr_s28in B MT) e).
Proof.
intros e W cf Hent HR.
destruct HR as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hcore & Hline & Hcopy).
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
destruct (s28_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _).
destruct (Verbs.toks (e_D e)) as [|v args] eqn:Et; [contradiction|].
destruct Hroute as [Hled Hrc].
assert (Hnt : vr_ntok (e_D e) = Z.of_nat (length (v :: args))) by (unfold vr_ntok; rewrite Et; reflexivity).
assert (Hnt64 : vr_ntok (e_D e) <= 64) by (unfold vr_ntok; pose proof (s28_toks_le (e_D e)); lia).
assert (Hiv : s27_iv (e_D e) = if Verbs.is_instance_verb v then 1 else 0) by (unfold s27_iv; rewrite Et; reflexivity).
assert (Hrows : forall r val, In (r, val) (vr_base B e ++ s27_rlR e tp) -> getr regsc (Z_to_bv 5 r) = w64 val)
  by (intros r val Hi; exact (vr_rv_get _ _ r val Hrv Hi)).
assert (R10 := Hrows 10 _ ltac:(unfold vr_base, s27_rlR; cbn [app In]; tauto)).
assert (R21 := Hrows 21 _ ltac:(unfold vr_base, s27_rlR; cbn [app In]; tauto)).
pose proof (q_seed0 W regsc memc S27_B) as HS.
remember (Eimg (Ereg regsc [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply q_env_agree).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e))) by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 (s27_iv (e_D e))) by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), R10; reflexivity).
assert (Hiv01 : 0 <= s27_iv (e_D e) <= 1) by (rewrite Hiv; destruct (Verbs.is_instance_verb v); lia).
(* 0x8d838: li a1,1 *)
paj_run_sh RUNP HS HJ.
{ awr_ok_tac. }
match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
  set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
clearbody mdv.
cbn [ms_mem mkst] in HFr.
pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq1. clear HF HFr HG.
(* 0x8d83c: beq s5,a1,0x8d8c4 *)
psrr_branch_pi RUNP BR HS.
- (* one word: to S28 *)
  rewrite branch_eq_U, (U_atom E 21 _ E21) in Hc by lia.
  assert (Hone : args = []).
  { destruct args as [|a r]; [reflexivity|]. exfalso. change (U E (SLit 1)) with 1 in Hc.
    apply Z.eqb_eq in Hc. rewrite Hnt in Hc. cbn [length] in Hc. lia. }
  subst args.
  paj_run_to_sh RUNTO HS HJ S27_28.
  { awr_ok_tac. }
  match goal with |- context [with_vm_backing (m_vm_lazy mdv) ?mt mdv] =>
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mt mdv) in * end.
  clearbody mdv2.
  pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq2. clear HF HFr HG.
  pose proof (fun x => eq_trans (Eq2 x) (Eq1 x)) as Eq.
  pose proof (q_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 21; 25; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pmkst HS.
  apply SRr_ret. right.
  match goal with |- vr_s28in B MT e W (mkCfg (mkst ?rg _ ?mm _) _) =>
    destruct (s27_kept e pos F q c tp lyc Sc W regsc memc mdc k nm (s27_rlR e tp)
      [(21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, hd 0 tp)] rg mm mdv2 Hcore Hline Hcopy HJ Eq
      ltac:(intros r val Hi; unfold s27_rlR; cbn in Hi |- *; tauto) KR
      ltac:(intros r val Hi; cbn in Hi |- *; destruct Hi as [E1|[E1|[E1|[]]]]; injection E1 as <- _; tauto))
    as (Hc2 & Hl2 & Hcp2);
    exists pos, F, q, c, tp, lyc, Sc, rg, mm, mdv2, k, nm end.
  split; [apply s27_cfg; unfold S27_28, AF_verbs_receive; lia|].
  split; [rewrite Et; cbv beta iota; rewrite Hrc; reflexivity|].
  split; [exact Hc2|]. split; [exact Hl2 | exact Hcp2].
- (* two or more words: 0x8d840 beqz a0,0x8d8c4 *)
  rewrite branch_eq_U, (U_atom E 21 _ E21) in Hc by lia.
  assert (Hmany : exists a rest, args = a :: rest).
  { destruct args as [|a r]; [|exists a, r; reflexivity]. exfalso. change (U E (SLit 1)) with 1 in Hc.
    rewrite Hnt in Hc. cbn in Hc. discriminate Hc. }
  destruct Hmany as (a & rest & ->). clear Hc.
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  match goal with |- context [with_vm_backing (m_vm_lazy mdv) ?mt mdv] =>
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mt mdv) in * end.
  clearbody mdv2.
  cbn [ms_mem mkst] in HFr.
  pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq2. clear HF HFr HG.
  pose proof (fun x => eq_trans (Eq2 x) (Eq1 x)) as Eq12.
  psrr_branch_pi RUNP BR HS.
  + (* a0 = 0: not an instance verb, to S28 *)
    rewrite branch_eq_U, (U_atom E 10 _ E10) in Hc by lia.
    change (U E (SLit 0)) with 0 in Hc. apply Z.eqb_eq in Hc. rewrite Hiv in Hc.
    assert (Hni : Verbs.is_instance_verb v = false) by (destruct (Verbs.is_instance_verb v); [discriminate Hc | reflexivity]).
    paj_run_to_sh RUNTO HS HJ S27_28.
    { awr_ok_tac. }
    match goal with |- context [with_vm_backing (m_vm_lazy mdv2) ?mt mdv2] =>
      set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mt mdv2) in * end.
    clearbody mdv3.
    pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq3. clear HF HFr HG.
    pose proof (fun x => eq_trans (Eq3 x) (Eq12 x)) as Eq.
    pose proof (q_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 21; 25; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply SRr_ret. right.
    match goal with |- vr_s28in B MT e W (mkCfg (mkst ?rg _ ?mm _) _) =>
      destruct (s27_kept e pos F q c tp lyc Sc W regsc memc mdc k nm (s27_rlR e tp)
        [(21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, hd 0 tp)] rg mm mdv3 Hcore Hline Hcopy HJ Eq
        ltac:(intros r val Hi; unfold s27_rlR; cbn in Hi |- *; tauto) KR
        ltac:(intros r val Hi; cbn in Hi |- *; destruct Hi as [E1|[E1|[E1|[]]]]; injection E1 as <- _; tauto))
      as (Hc2 & Hl2 & Hcp2);
      exists pos, F, q, c, tp, lyc, Sc, rg, mm, mdv3, k, nm end.
    split; [apply s27_cfg; unfold S27_28, AF_verbs_receive; lia|].
    split; [rewrite Et; cbv beta iota; rewrite Hrc; exact (s27_cd_noinst v a rest Hni)|].
    split; [exact Hc2|]. split; [exact Hl2 | exact Hcp2].
  + (* a0 <> 0: an instance verb with an argument, on to 0x8d844 *)
    rewrite branch_eq_U, (U_atom E 10 _ E10) in Hc by lia.
    change (U E (SLit 0)) with 0 in Hc. rewrite Hiv in Hc.
    assert (Hyi : Verbs.is_instance_verb v = true) by (destruct (Verbs.is_instance_verb v); [reflexivity | discriminate Hc]).
    paj_run_to_sh RUNTO HS HJ S27_C.
    { awr_ok_tac. }
    match goal with |- context [with_vm_backing (m_vm_lazy mdv2) ?mt mdv2] =>
      set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mt mdv2) in * end.
    clearbody mdv3.
    pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq3. clear HF HFr HG.
    pose proof (fun x => eq_trans (Eq3 x) (Eq12 x)) as Eq.
    pose proof (q_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 21; 25; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply SRr_ret. left.
    match goal with |- s27_I e W (mkCfg (mkst ?rg _ ?mm _) _) =>
      destruct (s27_kept e pos F q c tp lyc Sc W regsc memc mdc k nm (s27_rlR e tp)
        [(21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, hd 0 tp)] rg mm mdv3 Hcore Hline Hcopy HJ Eq
        ltac:(intros r val Hi; unfold s27_rlR; cbn in Hi |- *; tauto) KR
        ltac:(intros r val Hi; cbn in Hi |- *; destruct Hi as [E1|[E1|[E1|[]]]]; injection E1 as <- _; tauto))
      as (Hc2 & Hl2 & Hcp2);
      exists pos, F, q, c, tp, lyc, Sc, rg, mm, mdv3, k, nm end.
    split; [reflexivity|].
    split; [rewrite Et; cbv beta iota; rewrite Hrc; exact (s27_inst v a rest Hyi)|].
    split; [exact Hc2|]. split; [exact Hl2 | exact Hcp2].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Leg C: an instance verb with an argument: the reloads and the UBSan check, atoi(tok[1]),
   sup_call(atoi(tok[1]), line), the jump to JB *)
(* the meter of the sup_call shape, in one lemma: B's account (record's spill arm, arg_s's copy of the printed number,
   arg_line's and answer's) is 4 mallocs of at most VERBS_RECEIVE_REQ bytes and 1 free (answer's), within its 5
   events; the callee's mo_ok premise and the boundary's vr_meter after its mo_le come from q_meter (vri_meter_ok /
   vri_meter_step) *)
Lemma s27_meter_call : forall e Sc k nm id line t,
vr_ent B MT e -> vr_meter MT e Sc k nm -> r_calls (e_R e) = [] ->
-2 ^ 31 <= id < 2 ^ 31 -> Z.of_nat (length line) <= 8192 -> (length t <= 28)%nat ->
k + EV_SUP_CALL (e_R e) <= ev_vr (e_R e) (e_D e) ->
mo_ok MT Sc (XM_SUP_CALL MT (e_R e) id line t) /\
(forall S2, mo_le MT Sc S2 (XM_SUP_CALL MT (e_R e) id line t) ->
  vr_meter MT e S2 (k + EV_SUP_CALL (e_R e)) (nm + 4)).
Proof.
intros e Sc k nm id line t Hent Hm Hc Hid Hl Ht Hk.
assert (HEV : EV_SUP_CALL (e_R e) = 5)
  by (unfold EV_SUP_CALL, EV_RECORD, EV_ARG_S, EV_XMALLOC, EV_ARG_LINE, EV_REC_CANONICAL, EV_ANSWER, EV_HAND_BACK;
      rewrite (q_spill0 _ Hc); reflexivity).
apply (q_meter B MT e Sc k nm _ 4 1 (EV_SUP_CALL (e_R e)) MTL Hent Hm); [| lia | lia | exact Hk].
pose proof (dec_length id Hid) as Hd.
unfold XM_SUP_CALL, XM_RECORD, XM_ARG_S, XM_ARG_LINE, XM_REC_CANONICAL, XM_ANSWER, XM_HAND_BACK, sarg.
unfold XM_XMALLOC, LIVE_XMALLOC. cbv beta iota. rewrite (q_spill0 _ Hc).
pose proof (q_mall MT (Z.max (Z.of_nat (length (dec id)) + 1) 1) MTL ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M1.
pose proof (q_mall MT (Z.max (Z.of_nat (length line) + 1) 1) MTL ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M2.
pose proof (q_mall MT (Z.max (Z.of_nat (length t) + 1) 1) MTL ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M3.
set (m1 := mo_malloc MT (Z.max (Z.of_nat (length (dec id)) + 1) 1)) in *.
set (m2 := mo_malloc MT (Z.max (Z.of_nat (length line) + 1) 1)) in *.
set (m3 := mo_malloc MT (Z.max (Z.of_nat (length t) + 1) 1)) in *.
set (mM := mo_malloc MT VERBS_RECEIVE_REQ) in *. set (mF := mo_free MT) in *.
clearbody m1 m2 m3 mM mF.
clear - M1 M2 M3. lia.
Qed.

Lemma s27_C : forall e W cf, vr_ent B MT e -> s27_I e W cf ->
SRr SEGS W cf (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\ vr_athd (fx := fq) B MT 0x8d4cc e W' cf').
Proof.
intros e W cf Hent HI.
destruct HI as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hcore & Hline & Hcopy).
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & _ & Hcalls & _ & _ & _ & _ & _
  & _ & _ & _ & _ & VOBJS & _ & _ & _ & Hfr4 & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (s28_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof Hcore as (HJ & Hkk & Hmeter & Hnm & Hframe & Hrv & Hsaved & Hspill & Henv & Hrec & HdO & Hperm & Hquit).
pose proof (proj1 HJ) as HAR.
pose proof (s28_frames_own B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hin4.
destruct Hframe as (HFa & Hflag & Hshf).
destruct (s28_frame_bounds B lyc Sc W memc mdc pos HAR Hin4) as (BF1 & BF2 & BF3 & BF4).
rewrite <- HFa in BF1, BF2, BF3, BF4.
destruct (q_shadow_range F BF1 BF2) as [HSA1 HSA2].
destruct (q_tmps B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as (HtB & HtO & HOin).
pose proof (HtB _ (or_introl eq_refl)) as Hlb. pose proof (HtB _ (or_intror (or_introl eq_refl))) as Hcb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hlb) as (_ & Hq4096 & Hqc & _).
unfold vr_lb in Hq4096, Hqc. cbn [fst snd] in Hq4096, Hqc.
assert (HL : 0 <= vr_l (e_n e) (e_D e) <= e_n e) by (apply verbs_receive_pre.strnlen_res_le; lia).
assert (HLL : Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e)) by (apply vr_line_le_l; exact HlenD).
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [Hrq1 Hrq2].
destruct (Verbs.toks (e_D e)) as [|v [|a rest]] eqn:Et; try contradiction.
pose proof Hcopy as (_ & (_ & HlenP & _)).
destruct tp as [|p0 [|p1 tps]]; rewrite Et in HlenP; try discriminate HlenP.
assert (Hst : vr_st (e_D e) = Verbs.SCall (Verbs.sup_call (atoi_a a) (Verbs.line (e_D e))))
  by exact (vr_st_inst (e_D e) v a rest Et Hroute).
assert (Hk1 : vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_CALL (e_R e)) by exact (vr_k1_inst (e_R e) (e_D e) v a rest Et Hroute).
set (t := snd (sup_call_m (e_R e) (atoi_a a) (Verbs.line (e_D e)))).
assert (HX : vr_x (e_R e) (e_D e) = t) by (rewrite (vr_x_call _ _ _ Hst); reflexivity).
assert (HR1 : vr_R1 (e_R e) (e_D e) = fst (sup_call_m (e_R e) (atoi_a a) (Verbs.line (e_D e))))
  by (rewrite (vr_R1_call _ _ _ Hst); reflexivity).
assert (Hqv : vr_qv e = e_q0 e) by (unfold vr_qv; rewrite (vr_quit_call _ _ _ Hst); reflexivity).
assert (HEV : EV_SUP_CALL (e_R e) = 5)
  by (unfold EV_SUP_CALL, EV_RECORD, EV_ARG_S, EV_XMALLOC, EV_ARG_LINE, EV_REC_CANONICAL, EV_ANSWER, EV_HAND_BACK;
      rewrite (q_spill0 _ Hcalls); reflexivity).
assert (Hid : -2 ^ 31 <= atoi_a a < 2 ^ 31) by exact (vr_atoi_range a).
pose proof (dec_length (atoi_a a) Hid) as Hdec.
assert (Ht28 : (length t <= 28)%nat).
{ unfold t, sup_call_m. apply vr_text_len. exact (q_code_range B _ _ _ _ _ Hrec). }
assert (Hev2 : 2 + EV_SUP_CALL (e_R e) <= ev_vr (e_R e) (e_D e))
  by (pose proof (q_k1_ev (e_R e) (e_D e)); pose proof s28_ev_reply; lia).
(* the registers and the slots of the boundary *)
assert (Hrows : forall r val, In (r, val) (vr_base B e ++ [(21, vr_ntok (e_D e)); (25, vr_ntok (e_D e));
  (26, hd 0 (p0 :: p1 :: tps))]) -> getr regsc (Z_to_bv 5 r) = w64 val)
  by (intros r val Hi; exact (vr_rv_get _ _ r val Hrv Hi)).
assert (R9 := Hrows 9 (vr_s1 e) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (Hsp : forall o val, In (o, val) (q_sl F q) -> aval_mem (rdW W memc) (vr_s1 e + o) 8 val).
{ intros o val Hi. unfold vr_spill in Hspill. rewrite Forall_forall in Hspill.
  exact (Hspill (o, val) (q_sl_of_sl3 F q c o val Hi)). }
destruct (q_tok_arg B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c (p0 :: p1 :: tps) 1%nat p1 a Hcore
  (or_intror (or_introl eq_refl)) Hcopy eq_refl ltac:(rewrite Et; reflexivity)) as (_ & Hp1m & Hp14 & Hp1c & Hp1cc & Hcp1).
pose proof (q_seedT1 W regsc memc S27_C (vr_s1 e) q F p1 0 R9 ltac:(lia) ltac:(lia) ltac:(lia) BF1 BF2 ltac:(lia)
  ltac:(lia) Hsp ltac:(replace (F + 40) with (F + 32 + 8 * Z.of_nat 1) by lia; exact Hp1m)) as HS.
remember (Eimg (Ereg regsc (q_extra q F p1 0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc (q_extra q F p1 0)) E) by (subst E; apply q_env_agree).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (q_extra q F p1 0) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
clear HE.
assert (X32 : ew E 32 = Z_to_bv 64 q) by exact (EX 0%nat ltac:(lia)).
assert (X33 : ew E 33 = Z_to_bv 64 F) by exact (EX 1%nat ltac:(lia)).
assert (X34 : ew E 34 = Z_to_bv 64 p1) by exact (EX 2%nat ltac:(lia)).
assert (X36 : ew E 36 = Z_to_bv 64 (shadow_addr F)) by exact (EX 4%nat ltac:(lia)).
(* 0x8d844: li a0,-9; ld s6,24(s1); ld s11,32(s1); ld s2,56(s1); ld s3,40(s1); up to the check 0x8d858 *)
paj_run_sh RUNP HS HJ.
{ q_awr. }
match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
  set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
clearbody mdv.
cbn [ms_mem mkst] in HFr.
pose proof (q_rdeq_of_frame _ _ _ _ _ HFr q_ro_rt1) as Eq0. clear HF HFr HG.
(* 0x8d858: bltu a0,s3,0x8d938 (UBSan: tok + 8 wraps) *)
psrr_branch_pi RUNP BR HS.
{ (* taken: 2^64 - 9 < tok = F + 32, against the frame's bound F + 1024 <= alloc_ceiling < 2^47 *)
  exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
  rewrite (U_atom_off E 33 F 32 X33 ltac:(lia) ltac:(lia)) in Hc.
  rewrite U_lit in Hc by lia. lia. }
clear Hc.
(* 0x8d85c: ld a0,8(s3); jal __interceptor_trampoline_atoi *)
paj_run_shc RUNP RUNC HS HJ.
{ q_awr. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into msA end.
match goal with |- context [with_vm_backing (m_vm_lazy mdv) ?mt mdv] =>
  set (mdv1 := with_vm_backing (m_vm_lazy mdv) mt mdv) in * end.
clearbody mdv1.
pose proof (q_rdeq_of_frame _ _ _ _ _ HFr q_ro_rt1) as Eq1'. clear HF HFr HG.
pose proof (fun x => eq_trans (Eq1' x) (Eq0 x)) as Eq1.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18.
prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (27%bv : bv 5) Q27.
rewrite X34 in Q10. rewrite X32 in Q18. rewrite X33, unsigned_lit_small in Q19 by lia.
rewrite X33 in Q22. rewrite X36, unsigned_lit_small in Q27 by lia.
pose proof (q_kept_regs E _ _ regsc (q_extra q F p1 0) [2; 3; 4; 8; 9; 21; 24; 26] HS HAE ltac:(vm_compute; reflexivity))
  as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
assert (HcoreA : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(1, BASE + S27_D); (10, p1); (18, q); (19, F + 32); (21, vr_ntok (e_D e)); (22, F); (26, p0);
   (27, shadow_addr F + 4)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs msA) (ms_mem msA) mdv1).
{ apply (q_core_same B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc W (ms_regs msA) (ms_mem msA) mdv1
    Hcore HJ Eq1).
  apply (q_rv_keep B e (ms_regs msA) regsc _ _ Hrv).
  - intros r Hr. apply KR. cbn in Hr |- *. tauto.
  - intros r val Hi. cbn in Hi.
    destruct Hi as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]]; injection E1 as <- <-.
    + right. exact Q1.
    + right. exact Q10.
    + right. exact Q18.
    + right. exact Q19.
    + left. split; [cbn; tauto | apply KR; cbn; tauto].
    + right. exact Q22.
    + left. split; [cbn; tauto | apply KR; cbn; tauto].
    + right. exact Q27. }
pose proof (q_line_same B e q W memc W (ms_mem msA) Eq1 Hline) as HlineA.
pose proof (q_copy_same B e F c (p0 :: p1 :: tps) W memc W (ms_mem msA) Eq1 Hcopy) as HcopyA.
pose proof HcoreA as (_ & _ & _ & _ & _ & HrvA & _ & _ & HenvA & _).
pose proof HenvA as (HRO1 & _ & _ & Hgd1 & Hfl1 & (ev & Herr1)).
pose proof HcopyA as (_ & (_ & _ & _ & Hw1)).
destruct (Hw1 1%nat p1 a eq_refl ltac:(rewrite Et; reflexivity)) as (A1 & _ & _ & _).
pose proof (proj1 HJ) as HAR1.
assert (Q2 : getr (ms_regs msA) 2 = w64 (vr_s1 e)).
{ etransitivity; [exact (KR 2 ltac:(cbn; tauto))|]. apply (vr_rv_get regsc _ 2 _ Hrv). apply in_or_app; left; cbn; tauto. }
assert (Q3 : getr (ms_regs msA) 3 = w64 (as_gp B)).
{ etransitivity; [exact (KR 3 ltac:(cbn; tauto))|]. apply (vr_rv_get regsc _ 3 _ Hrv). apply in_or_app; left; cbn; tauto. }
assert (Q4 : getr (ms_regs msA) 4 = w64 (as_tp B)).
{ etransitivity; [exact (KR 4 ltac:(cbn; tauto))|]. apply (vr_rv_get regsc _ 4 _ Hrv). apply in_or_app; left; cbn; tauto. }
assert (Qsp : spZ (ms_regs msA) = vr_sp0 e + (vr_s1 e - vr_sp0 e)).
{ unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hra : YK0s.ret_ok (getr (ms_regs msA) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; first [lia | reflexivity]).
pose proof (ecall_pre_stk_at SEGS B (3 * ESTACK) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e)
  (e_mem e) (e_md e) [(4, pos)] lyc Sc W (ms_mem msA) mdv1 k (ms_regs msA) (vr_s1 e - vr_sp0 e) HJ Qsp Hs1o
  ltac:(lia) ltac:(lia) ltac:(lia) Hra Q3 Q4) as HPRE1.
(* the atoi wrapper on tok[1] *)
eapply SRr_bind.
{ eapply (ART (3 * ESTACK) (aerrno_cell B) _ W (ms_regs msA) (ms_mem msA) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e)
    (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdv1 k (vr_s1 e - vr_sp0 e) _ _ HJ);
    [exact Qsp | exact Hs1o | lia | lia | lia | exact Q1 | intros a0 Ha0; exact Ha0 |].
  apply (AATOI fx lyc Sc W (ms_regs msA) (ms_mem msA) mdv1 p1 a ev Hfl1 Hgd1 HPRE1 Q10 ltac:(lia)).
  - apply astr_atR_view. exact A1.
  - apply (aread_ok_of_block SEGS B LAWS (3 * ESTACK) lyc Sc W (ms_regs msA) (ms_mem msA) mdv1 c
      (Z.of_nat (length (Verbs.line (e_D e))) + 1) p1 (astr_len a + 1) HAR1 Hcb); unfold astr_len; [lia | lia | lia |].
    rewrite Qsp. lia.
  - apply (amem8_of_blockA SEGS B LAWS lyc Sc W (ms_mem msA) mdv1); [exact HAR1 | | unfold astr_len; lia].
    exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1). split; [exact Hcb | unfold astr_len; lia].
  - unfold astr_len. apply (BLKT lyc Sc W (ms_mem msA) mdv1 c (Z.of_nat (length (Verbs.line (e_D e))) + 1));
      [exact HAR1 | exact Hcb | lia].
  - exact Herr1.
  - (* tok[1] apart from the errno cell: its bytes are in the copy block, not image bytes (blk_img); the errno
       cell's are (api_env) *)
    pose proof (pal_env B TL) as (_ & Hzi & _).
    destruct (Hw1 1%nat p1 a eq_refl ltac:(rewrite Et; reflexivity)) as (_ & _ & Hza & Hzb).
    destruct (Z_le_gt_dec (p1 + astr_len a + 1) (as_errno B)) as [Hz1|Hz1]; [left; exact Hz1|].
    destruct (Z_le_gt_dec (as_errno B + 4) p1) as [Hz2|Hz2]; [right; exact Hz2|]. exfalso.
    apply (blk_img SEGS B LAWS lyc Sc W (ms_mem msA) mdv1 c (Z.of_nat (length (Verbs.line (e_D e))) + 1)
      (Z.max p1 (as_errno B)) HAR1 Hcb); [| apply Hzi; clear - Hz1 Hz2; lia].
    unfold req_size. destruct (Z.eqb_spec (Z.of_nat (length (Verbs.line (e_D e))) + 1) 0) as [Hzk|Hzk]; cbv iota;
      clear - Hza Hzb Hz1 Hzk; unfold astr_len in Hz1; lia.
  - exact (vr_rtrom_ok B W (ms_mem msA) HRO1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HA0 & _) & HK2).
assert (KX : s27_kx e W (ms_mem msA) mem2).
{ intros a0 Ha0 Hb Hn. apply HK2; [exact Ha0 | | exact Hn]. lia. }
assert (HrvB : vr_rv regs2 (vr_base B e ++
  [(10, atoi_a a); (18, q); (19, F + 32); (21, vr_ntok (e_D e)); (22, F); (26, p0);
   (27, shadow_addr F + 4)])).
{ apply (q_rv_keep B e regs2 (ms_regs msA) _ _ HrvA).
  - intros r Hr. apply HP2. unfold acallee_saved. cbn in Hr. lia.
  - intros r val Hi. cbn in Hi. destruct Hi as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]; injection E1 as <- <-.
    + right. exact HA0.
    + left. split; [cbn; tauto | apply HP2; unfold acallee_saved; lia].
    + left. split; [cbn; tauto | apply HP2; unfold acallee_saved; lia].
    + left. split; [cbn; tauto | apply HP2; unfold acallee_saved; lia].
    + left. split; [cbn; tauto | apply HP2; unfold acallee_saved; lia].
    + left. split; [cbn; tauto | apply HP2; unfold acallee_saved; lia].
    + left. split; [cbn; tauto | apply HP2; unfold acallee_saved; lia]. }
pose proof (s27_core_kx e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs msA) (ms_mem msA) mdv1 regs2 mem2 md2
  Hent HcoreA HJ2 KX (s27_sl3 F q c) HrvB) as HcoreB.
pose proof (s27_line_kx e q lyc Sc W (ms_mem msA) mdv1 mem2 Hent HAR1 Hlb HlineA KX) as HlineB.
pose proof (s27_copy_kx e F c (p0 :: p1 :: tps) pos lyc Sc W (ms_mem msA) mdv1 mem2 HAR1 Hin4 HFa Hcb HcopyA KX)
  as HcopyB.
(* 0x8d864: mv a1,s2; jal sup_call *)
assert (R18B : getr regs2 (Z_to_bv 5 18) = w64 q)
  by (apply (vr_rv_get _ _ 18 _ HrvB); unfold vr_base; cbn [app In]; tauto).
pose proof (q_seed0 W regs2 mem2 S27_D) as HS2.
remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (HAE2 : env_agree 32 (Ereg regs2 []) E2) by (subst E2; apply q_env_agree).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
  by (intros n r Hn; subst E2; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE2.
paj_run_shc RUNP RUNC HS2 HJ2.
{ awr_ok_tac. }
lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?m) => rename m into msC end.
match goal with |- context [with_vm_backing (m_vm_lazy md2) ?mt md2] =>
  set (mdv2 := with_vm_backing (m_vm_lazy md2) mt md2) in * end.
clearbody mdv2.
pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq2. clear HF HFr HG.
prreg HS2 (1%bv : bv 5) Q1c. prreg HS2 (11%bv : bv 5) Q11c.
rewrite (EE2 18%nat (Z_to_bv 5 18) eq_refl), R18B in Q11c.
pose proof (q_kept_regs E2 _ _ regs2 [] [2; 3; 4; 8; 9; 10; 18; 19; 21; 22; 24; 26; 27] HS2 HAE2
  ltac:(vm_compute; reflexivity)) as KR2.
cbn [ms_regs restrict] in KR2.
pmkst HS2.
rewrite (SIGP CS_sup_call) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_sup_call) with AF_sup_call.
set (rlC := [(1, BASE + S27_E); (10, atoi_a a); (11, q); (18, q); (19, F + 32); (21, vr_ntok (e_D e)); (22, F);
  (26, p0); (27, shadow_addr F + 4)]).
assert (HcoreC : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rlC
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs msC) (ms_mem msC) mdv2).
{ apply (q_core_same B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regs2 mem2 md2 W (ms_regs msC) (ms_mem msC) mdv2
    HcoreB HJ2 Eq2).
  apply (q_rv_keep B e (ms_regs msC) regs2 _ _ HrvB).
  - intros r Hr. apply KR2. cbn in Hr |- *. tauto.
  - intros r val Hi. unfold rlC in Hi. cbn in Hi.
    destruct Hi as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]]]; injection E1 as <- <-.
    + right. exact Q1c.
    + left. split; [cbn; tauto | apply KR2; cbn; tauto].
    + right. exact Q11c.
    + left. split; [cbn; tauto | apply KR2; cbn; tauto].
    + left. split; [cbn; tauto | apply KR2; cbn; tauto].
    + left. split; [cbn; tauto | apply KR2; cbn; tauto].
    + left. split; [cbn; tauto | apply KR2; cbn; tauto].
    + left. split; [cbn; tauto | apply KR2; cbn; tauto].
    + left. split; [cbn; tauto | apply KR2; cbn; tauto]. }
pose proof (q_line_same B e q W mem2 W (ms_mem msC) Eq2 HlineB) as HlineC.
pose proof (q_copy_same B e F c (p0 :: p1 :: tps) W mem2 W (ms_mem msC) Eq2 HcopyB) as HcopyC.
pose proof HcoreC as (HJC & _ & HmeterC & HnmC & _ & HrvC & _ & _ & HenvC & HrecC & _).
pose proof HenvC as (HROC & _ & HROkC & _).
assert (R1C : getr (ms_regs msC) 1 = Z_to_bv 64 (BASE + S27_E)) by exact Q1c.
assert (R10C : getr (ms_regs msC) 10 = w64 (atoi_a a)) by (apply (vr_rv_get _ _ 10 _ HrvC); unfold rlC, vr_base; cbn [app In]; tauto).
assert (R11C : getr (ms_regs msC) 11 = w64 q) by (apply (vr_rv_get _ _ 11 _ HrvC); unfold rlC, vr_base; cbn [app In]; tauto).
destruct (s27_meter_call e Sc k nm (atoi_a a) (Verbs.line (e_D e)) t Hent HmeterC Hcalls Hid ltac:(lia) Ht28
  ltac:(lia)) as [HmokC Hmeter3].
assert (HSC : SUP_CALL_STK = ltac:(let v := eval vm_compute in SUP_CALL_STK in exact v)) by reflexivity.
eapply SRr_bind.
{ eapply (q_rcallF B MT HB PROGU e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs msC) (ms_mem msC) mdv2 AF_sup_call
    SUP_CALL_STK _ (EV_SUP_CALL (e_R e)) S27_E _ Hent HcoreC).
  - exact R1C.
  - unfold S27_E; lia.
  - reflexivity.
  - lia.
  - lia.
  - exact (s28_FP_conn (e_O e)).
  - intros ch HPRE2.
    apply (TSUP_CALL fx lyc Sc W (ms_regs msC) (ms_mem msC) mdv2 ch (atoi_a a) q (Verbs.line (e_D e)) (e_R e) (e_O e)
      HPRE2 (q_ent_frm0 B MT e Hent)).
    + pose proof HJC as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. cbn [app length]. lia.
    + exact HROC.
    + exact HROkC.
    + exact R10C.
    + exact Hid.
    + exact R11C.
    + lia.
    + exact (q_line_arg B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs msC) (ms_mem msC) mdv2 q Hent HcoreC
        (or_introl eq_refl) HlineC).
    + exact HrecC.
    + exact (q_nev B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs msC) (ms_mem msC) mdv2 _ Hent HcoreC Hev2).
    + apply (q_live B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs msC) (ms_mem msC) mdv2 _ 0 Hent HcoreC
        ltac:(rewrite Hcalls; cbn; lia)).
      fold t. unfold bsum, vr_lb, vr_cb. cbn [fold_right fst snd].
      unfold LIVE_SUP_CALL, LIVE_ARG_S, LIVE_ARG_LINE, LIVE_REC_CANONICAL, LIVE_ANSWER, LIVE_HAND_BACK, sarg.
      unfold LIVE_XMALLOC. cbv beta iota. rewrite !Z.max_l by lia.
      unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ, LMAX. lia.
    + exact HmokC. }
cbv beta. intros W3 c3 _ (fx' & ly3 & S3 & regs3 & mem3 & md3 & Hfx & -> & HJ3 & HJc3 & HP3 & HK3).
destruct HK3 as (R' & O' & qt & Hm & Ha0 & Hqt & Hrec' & HO'1 & HB2 & HB1 & Hqin & Hqne & HqO' & Hstr & _ & Hmle).
assert (Hrv3 : vr_rv regs3 (vr_base B e ++ vr_rl_hd e F q c 0x8d4cc qt)).
{ replace (vr_rl_hd e F q c 0x8d4cc qt) with
    [(10, qt); (19, F + 32); (18, q); (22, F); (27, shadow_addr F + 4)] by reflexivity.
  apply (q_rv_keep B e regs3 (ms_regs msC) _ _ HrvC).
  - intros r Hr. apply HP3. unfold acallee_saved. cbn in Hr. lia.
  - intros r val Hi. cbn in Hi. destruct Hi as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-.
    + right. exact Ha0.
    + left. split; [unfold rlC; cbn; tauto | apply HP3; unfold acallee_saved; lia].
    + left. split; [unfold rlC; cbn; tauto | apply HP3; unfold acallee_saved; lia].
    + left. split; [unfold rlC; cbn; tauto | apply HP3; unfold acallee_saved; lia].
    + left. split; [unfold rlC; cbn; tauto | apply HP3; unfold acallee_saved; lia]. }
destruct (s28_post_new B MT ROA RRO RPG RECC PROGU e pos F q c (p0 :: p1 :: tps) rlC (vr_rl_hd e F q c 0x8d4cc qt)
  [vr_lb e q; vr_cb e c] (e_R e) (e_O e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs msC) (ms_mem msC) mdv2 SUP_CALL_STK _
  (EV_SUP_CALL (e_R e)) ly3 S3 W3 mem3 md3 regs3 R' O' qt (Z.of_nat (length t) + 1) (k + EV_SUP_CALL (e_R e))
  (vr_k1 (e_R e) (e_D e)) (nm + 4) VR_NM_HD Hent HcoreC HlineC HcopyC (or_introl eq_refl) (or_intror (or_introl eq_refl))
  HJc3 HJ3 (s28_FP_conn (e_O e)) ltac:(rewrite Hk1; lia) (Hmeter3 S3 Hmle) ltac:(unfold VR_NM_HD, VR_NM_PRE in *; lia)
  Hrec' HO'1
  HB1 HB2 Hqin Hqne HqO' Hrv3) as (O1 & _ & Hc3 & Hl3 & Hcp3).
assert (HR1' : vr_R1 (e_R e) (e_D e) = R') by (rewrite HR1, Hm; reflexivity).
(* 0x8d86c: j 0x8d4cc, at the FP state sup_call returned *)
apply (q_jmp (fx := fx') B S27_E S27_JB ltac:(unfold S27_E; lia) ltac:(vm_compute; reflexivity) W3 regs3 mem3 md3
  _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3).
intros regs5 mem5 md5 Er Em HJ5.
exists fx'. split; [exact Hfx|].
unfold vr_athd, vr_hd.
exists qt, O1, pos, F, q, c, (p0 :: p1 :: tps), ly3, S3, regs5, mem5, md5, (k + EV_SUP_CALL (e_R e)), (nm + 4).
split; [apply s27_cfg; unfold S27_JB, AF_verbs_receive; lia|].
split; [unfold vr_hd_ntok; rewrite Et; simpl; lia|].
split; [lia|].
rewrite HX, HR1', Hqv.
split; [exact (q_astr_eq _ _ _ _ Em Hstr)|].
split.
{ apply (q_core_same B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 regs3 mem3 md3 W3 regs5 mem5 md5 Hc3 HJ5 Em).
  apply q_rv_intro. intros r val Hi. rewrite Er. exact (vr_rv_get _ _ r val (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hc3)))))) Hi). }
split; [exact (q_line_same B e q W3 mem3 W3 mem5 Em Hl3) | exact (q_copy_same B e F c (p0 :: p1 :: tps) W3 mem3 W3 mem5 Em Hcp3)].
Qed.

Lemma vr_s27 : vr_s27_stmt B MT.
Proof.
intros e W cf Hent Hin.
eapply SRr_bind; [exact (s27_A e W cf Hent Hin)|].
intros W1 cf1 _ HR. eapply SRr_bind; [exact (s27_B e W1 cf1 Hent HR)|].
intros W2 cf2 _ [HI | H28].
- eapply SRr_mono; [exact (s27_C e W2 cf2 Hent HI)|].
  intros W3 cf3 _ (fq & Hfq & H). exists fq. split; [exact Hfq | left; exact H].
- apply SRr_ret. exists fx. split; [apply fxrel_refl | right; exact H28].
Qed.

End e.
End f.
End d.
