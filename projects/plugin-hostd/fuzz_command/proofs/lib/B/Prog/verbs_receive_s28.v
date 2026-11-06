(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S28 CONNBROAD (0x8d8c4-0x8d934 and 0x8d93c-0x8d970) of the walk of
   verbs_receive on the ASan+UBSan build (image B) of plugin-hostd/fuzz_command (interface:
   lib/B/Prog/verbs_receive_iface.v, vr_s28_stmt). The B twin of lib/A/Prog/verbs_receive_s28.v (A 0x8de40-0x8dec0).

     8d8c4 auipc/addi a1 = .str.22 "connect %s %s" 0x22840 ; mv a0,s10 ; jal verb_is        (leg V1, to 0x8d8d4)
     8d8d4 beqz a0,8d8e4 ; li a0,3 ; beq s5,a0,8d900 ; j 8d93c                               (leg D1)
     8d8e4 auipc/addi a1 = .str.23 "disconnect %s %s" 0x22860 ; mv a0,s10 ; jal verb_is     (leg V2, to 0x8d8f4)
     8d8f4 li a1,3 ; bne s5,a1,8d93c ; beqz a0,8d93c                                         (leg D2)
     8d900 li a0,-9 ; ld s6,24(s1) ; ld s11,32(s1) ; ld s2,56(s1) ; ld s3,40(s1) ;
           bltu a0,s3,8d938 ; li a0,-17 ; bltu a0,s3,8d938 ;                                (UBSan: never taken)
           ld a2,8(s3) ; ld a3,16(s3) ; mv a0,s10 ; mv a1,s2 ; jal sup_connect ; j 8d4cc   (leg CN, to JB)
     8d93c ld s2,56(s1) ; mv a0,s2 ; jal sup_broadcast ;                                     (leg BC)
     8d948 mv s10,a0 ; mv a0,s2 ; ld s3,40(s1) ; mv a1,s3 ; mv a2,s9 ; jal sup_host_setting ; (s28_BC2)
     8d960 ld s4,16(s1) ; ld s6,24(s1) ; ld s9,8(s1) ; ld s11,32(s1) ; j 8d6a4              (s28_tail, to JA)

   B-only: the reloads 0x8d904-0x8d910 and 0x8d960-0x8d96c (B keeps F, shadow_addr F, shadow_addr F + 4, the line and
   tok in the frame slots and reloads them around the calls), the two UBSan checks 0x8d914 / 0x8d91c (tok + 8 and
   tok + 16 do not wrap: tok = F + 32 with F this call's class-4 frame below alloc_ceiling), and the broadcast arm's
   `mv a2,s9`: s9 = ntok, which the interface's vr_s28in carries (s9 is callee-saved across sup_broadcast).

   The symbolic executor runs over the position-abstract listing with a state seeded from the boundary at every leg
   (the seeds of verbs_receive_s2728_st.v); verb_is goes through PaNoChain's cl_callS_na (q_na_call), the recorder
   calls through PaFx's cl_callS_wideF (q_rcallF) and their statements; the boundary after each call is rebuilt by
   q_keep_na / s28_post_new / s28_post_same. The recorder callees are printf-reaching (apost_baseF): each returns at
   some FP state fx' with fxrel fx fx', so the segment is stated with vr_segF. The jump after sup_connect runs at fx'
   through the FP-generic q_jmp; the walk after sup_broadcast is s28_BC2 and the run after sup_host_setting is
   s28_tail, each proved in its own section at that section's FP state and used at the FP state the call returned. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep CmdChk.
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

Module VQ8 := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the listing offsets of the segment: AF_verbs_receive + (pc - 0x8ce4c), AF_verbs_receive = 0x691c *)
Definition S28_A : Z := 29588.   (* 0x8d8c4, the entry *)
Definition S28_B : Z := 29604.   (* 0x8d8d4, after verb_is(tok[0], "connect %s %s") *)
Definition S28_C : Z := 29620.   (* 0x8d8e4 *)
Definition S28_D : Z := 29636.   (* 0x8d8f4, after verb_is(tok[0], "disconnect %s %s") *)
Definition S28_E : Z := 29648.   (* 0x8d900, the connect leg *)
Definition S28_F : Z := 29700.   (* 0x8d934, after sup_connect *)
Definition S28_G : Z := 29708.   (* 0x8d93c, the broadcast leg *)
Definition S28_H : Z := 29720.   (* 0x8d948, after sup_broadcast *)
Definition S28_I : Z := 29744.   (* 0x8d960, after sup_host_setting *)
Definition S28_JB : Z := 28572.  (* 0x8d4cc *)
Definition S28_JA : Z := 29044.  (* 0x8d6a4 *)

(* ------------------------------------------------------------------------------------------------------------
   The model: the two verb_is tests and the routes they decide *)
Definition s28_b (fb : list byte) (D : list byte) : Z := if Verbs.verb_is_m (hd [] (Verbs.toks D)) fb then 1 else 0.

Lemma s28_rconn : forall v a b, Verbs.verb_is_m v Verbs.Lit.fmt_connect = true -> VQ8.route_cd v [a; b] = VQ8.RConn.
Proof. intros v a b H. unfold VQ8.route_cd. rewrite H. reflexivity. Qed.
Lemma s28_rdisc : forall v a b, Verbs.verb_is_m v Verbs.Lit.fmt_disconnect = true -> VQ8.route_cd v [a; b] = VQ8.RConn.
Proof. intros v a b H. unfold VQ8.route_cd. rewrite H, orb_true_r. reflexivity. Qed.
Lemma s28_rbroad_len : forall v args, length args <> 2%nat -> VQ8.route_cd v args = VQ8.RBroad.
Proof. intros v [|a [|b [|d r]]] H; cbn in H; try reflexivity; lia. Qed.
Lemma s28_rbroad_no : forall v args, Verbs.verb_is_m v Verbs.Lit.fmt_connect = false ->
Verbs.verb_is_m v Verbs.Lit.fmt_disconnect = false -> VQ8.route_cd v args = VQ8.RBroad.
Proof. intros v [|a [|b [|d r]]] H1 H2; try reflexivity. unfold VQ8.route_cd. rewrite H1, H2. reflexivity. Qed.

Lemma s28_nth_rep0 : forall i n (d : Z), (i < n)%nat -> nth i (repeat 0 n) d = 0.
Proof.
induction i as [|i IH]; intros [|n] d H; cbn [repeat nth]; first [lia | (apply IH; lia)].
Qed.

Lemma s28_nth_sh2 : forall i, (i < 64)%nat -> nth (4 + i) vr_sh2 0 = 0.
Proof.
intros i Hi. unfold vr_sh2.
rewrite app_nth2 by (rewrite repeat_length; lia).
rewrite repeat_length. replace (4 + i - 4)%nat with i by lia.
rewrite app_nth1 by (rewrite repeat_length; lia). apply s28_nth_rep0. exact Hi.
Qed.

Lemma s28_forall2_of_nth : forall {X Y : Type} (R : X -> Y -> Prop) (l1 : list X) (l2 : list Y),
length l1 = length l2 ->
(forall i x y, nth_error l1 i = Some x -> nth_error l2 i = Some y -> R x y) ->
Forall2 R l1 l2.
Proof.
intros X Y R l1. induction l1 as [|x l1 IH]; intros [|y l2] Hl H; cbn in Hl; try discriminate; [constructor|].
constructor; [exact (H 0%nat x y eq_refl eq_refl)|].
apply IH; [lia | intros i a b H1 H2; exact (H (S i) a b H1 H2)].
Qed.

Lemma s28_nth_some : forall {X Y : Type} (l1 : list X) (l2 : list Y) i x, length l1 = length l2 ->
nth_error l1 i = Some x -> exists y, nth_error l2 i = Some y.
Proof.
intros X Y l1 l2 i x Hl H. destruct (nth_error l2 i) as [y|] eqn:E; [exists y; reflexivity|].
apply nth_error_None in E. assert (Hi : (i < length l1)%nat) by (apply nth_error_Some; rewrite H; discriminate). lia.
Qed.

(* the tail routes behind route_cd spend at least the duplications' events *)
Lemma s28_k1_ge2 : forall R D v args, Verbs.toks D = v :: args -> VQ8.route (v :: args) = VQ8.route_cd v args ->
2 <= vr_k1 R D.
Proof.
intros R D v args HT HR.
assert (Hs : forall R0, 0 <= rec_spill_frees R0) by (intros R0; unfold rec_spill_frees; destruct (Nat.ltb _ _); lia).
assert (H3 : VQ8.route (v :: args) = VQ8.RConn \/ VQ8.route (v :: args) = VQ8.RBroad).
{ rewrite HR. unfold VQ8.route_cd. destruct args as [|a [|b [|d r]]]; try (right; reflexivity).
  destruct (_ || _); [left | right]; reflexivity. }
destruct H3 as [H | H].
- destruct (vr_toks_conn (v :: args) H) as (v' & a & b & E). injection E as <- ->.
  rewrite (vr_k1_conn R D v a b HT H). unfold EV_SUP_CONNECT, EV_RECORD, EV_ARG_S, EV_ARG_LINE, EV_REC_CANONICAL,
    EV_ANSWER, EV_HAND_BACK, EV_XMALLOC.
  pose proof (Hs R). lia.
- rewrite (vr_k1_broad R D v args HT H). unfold EV_SUP_BROADCAST, EV_SUP_HOST_SETTING, EV_RECORD, EV_ARG_S,
    EV_ARG_LINE, EV_REC_CANONICAL, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC.
  pose proof (Hs R). pose proof (Hs (fst (sup_broadcast_m R (Verbs.line D)))). lia.
Qed.

Lemma s28_ev0 : forall R D v args, Verbs.toks D = v :: args -> VQ8.route (v :: args) = VQ8.route_cd v args ->
2 + 0 <= ev_vr R D.
Proof.
intros R D v args HT HR. pose proof (s28_k1_ge2 R D v args HT HR). pose proof (q_k1_ev R D). pose proof s28_ev_reply.
lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The run after sup_host_setting, in its own section: it runs at the FP state sup_host_setting returns, so it is
   proved here at this section's FP state and holds at every FP state once the section is closed *)
Section d0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f0.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* at every FP state f: an exit after a recorder call is at the FP state the call returns *)
Lemma s28_cfg : forall (f : YK11.FPState) regs mem md pc off, off = AF_verbs_receive + (pc - 0x8ce4c) ->
mkCfg (@mkst f regs (Z_to_bv 64 (BASE + off)) mem (seg_rom SEGS)) md = cfg_at (fx := f) SEGS (vr_pc pc) regs mem md.
Proof. intros f regs mem md pc off Ho. unfold cfg_at, vr_pc, w64. rewrite Ho. reflexivity. Qed.

Section e0.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.

(* 0x8d960: ld s4,16(s1) ; ld s6,24(s1) ; ld s9,8(s1) ; ld s11,32(s1) ; j 0x8d6a4. B reloads the four registers JA
   names (A's broadcast arm needed none: A kept F + 32 in s6 across the calls) *)
Lemma s28_tail : forall e tmps Rc Oc qv kmax nmax q1 pos F q c tp ly S (W : world SEGS) regs mem md k nm,
vr_ent B MT e -> In (vr_lb e q) tmps ->
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) [(18, q); (19, F + 32); (21, vr_ntok (e_D e)); (26, q1)]
  Rc Oc qv k kmax nm nmax ly S W regs mem md ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + S28_I)) mem (seg_rom SEGS)) md)
(fun W' cf' => W' = W /\ exists regs' mem' md', cf' = cfg_at SEGS (vr_pc 0x8d6a4) regs' mem' md' /\
  q_rdeq (rdW W mem) (rdW W mem') /\
  vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) (vr_rl_hd e F q c 0x8d6a4 q1) Rc Oc qv k kmax nm nmax
    ly S W regs' mem' md' /\
  vr_line B e q W mem' /\ vr_copy B e F c tp W mem').
Proof.
intros e tmps Rc Oc qv kmax nmax q1 pos F q c tp ly S W regs mem md k nm Hent Hlbt Hcore Hline Hcopy.
pose proof Hent as (HPRE0 & _). pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (s28_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
pose proof Hcore as (HJ & _ & _ & _ & Hframe & Hrv & _ & Hspill & _).
pose proof (proj1 HJ) as HAR.
pose proof (s28_frames_own B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hin4.
pose proof Hframe as (HFa & _ & _).
destruct (s28_frame_bounds B ly S W mem md pos HAR Hin4) as (BF1 & BF2 & BF3 & BF4).
rewrite <- HFa in BF1, BF2, BF3, BF4.
destruct (q_shadow_range F BF1 BF2) as [HSA1 HSA2].
destruct (q_tmps B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as (HtB & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (HtB _ Hlbt)) as (_ & Hq4096 & Hqc & _).
unfold vr_lb in Hq4096, Hqc. cbn [fst snd] in Hq4096, Hqc.
assert (HL : 0 <= vr_l (e_n e) (e_D e)).
{ pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _).
  apply verbs_receive_pre.strnlen_res_le; lia. }
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [Hrq1 Hrq2].
assert (R9 : getr regs (Z_to_bv 5 9) = w64 (vr_s1 e)) by (apply (vr_rv_get _ _ 9 _ Hrv); unfold vr_base; cbn [app In]; tauto).
assert (Hsp : forall o val, In (o, val) (q_sl F q) -> aval_mem (rdW W mem) (vr_s1 e + o) 8 val).
{ intros o val Hi. unfold vr_spill in Hspill. rewrite Forall_forall in Hspill.
  exact (Hspill (o, val) (q_sl_of_sl3 F q c o val Hi)). }
pose proof (q_seedS W regs mem S28_I (vr_s1 e) q F 0 0 R9 ltac:(lia) ltac:(lia) ltac:(lia) BF1 BF2 ltac:(lia)
  ltac:(lia) Hsp) as HS.
remember (Eimg (Ereg regs (q_extra q F 0 0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (q_extra q F 0 0)) E) by (subst E; apply q_env_agree).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (q_extra q F 0 0) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
clear HE.
assert (X33 : ew E 33 = Z_to_bv 64 F) by exact (EX 1%nat ltac:(lia)).
assert (X36 : ew E 36 = Z_to_bv 64 (shadow_addr F)) by exact (EX 4%nat ltac:(lia)).
paj_run_to_sh RUNTO HS HJ S28_JA.
{ q_awr. }
match goal with |- context [with_vm_backing (m_vm_lazy md) ?mt md] =>
  set (mdv := with_vm_backing (m_vm_lazy md) mt md) in * end.
clearbody mdv.
pose proof (q_rdeq_of_frame _ _ _ _ _ HFr q_ro_rsp) as Eq. clear HF HFr HG.
prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
rewrite X33 in Q20, Q22. rewrite X36 in Q25. rewrite X36, unsigned_lit_small in Q27 by lia.
pose proof (q_kept_regs E _ _ regs (q_extra q F 0 0) [2; 3; 4; 8; 9; 18; 19; 21; 26] HS HAE
  ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), mdv.
split; [apply s28_cfg; unfold S28_JA, AF_verbs_receive; lia|].
split; [exact Eq|].
split.
{ apply (q_core_same B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ ly S W regs mem md W (ms_regs ms) (ms_mem ms) mdv Hcore HJ Eq).
  replace (vr_rl_hd e F q c 0x8d6a4 q1) with
    [(26, q1); (19, F + 32); (20, F); (21, vr_ntok (e_D e)); (25, shadow_addr F); (18, q); (22, F);
     (27, shadow_addr F + 4)] by reflexivity.
  apply (q_rv_keep B e (ms_regs ms) regs _ _ Hrv).
  - intros r Hr. apply KR. cbn in Hr |- *. tauto.
  - intros r val Hi. cbn in Hi.
    destruct Hi as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]]; injection E1 as <- <-.
    + left. split; [cbn; tauto | apply KR; cbn; tauto].
    + left. split; [cbn; tauto | apply KR; cbn; tauto].
    + right. exact Q20.
    + left. split; [cbn; tauto | apply KR; cbn; tauto].
    + right. exact Q25.
    + left. split; [cbn; tauto | apply KR; cbn; tauto].
    + right. exact Q22.
    + right. exact Q27. }
split; [exact (q_line_same B e q W mem W (ms_mem ms) Eq Hline) | exact (q_copy_same B e F c tp W mem W (ms_mem ms) Eq Hcopy)].
Qed.

End e0.
End f0.
End d0.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the two format literals of the segment: their bytes, their tails *)
Lemma s28_ro_lits : forall rd, cmd_ro_ok rd ->
abytes_atR rd 0x22840 RO_lit_22840 /\ abytes_atR rd 0x22860 RO_lit_22860.
Proof. intros rd [H _]. unfold cmd_ro_bytes in H. decompose [and] H. split; assumption. Qed.

Lemma s28_ro_tail : forall (W : world SEGS) mem ee, cmd_ro_ok (rdW W mem) ->
existsb (Z.eqb ee) cmd_ro_ends = true -> atail_vis SEGS W mem ee.
Proof.
intros W mem ee [_ HT] Hin a Ha. apply existsb_exists in Hin as (e' & He' & Hq).
apply Z.eqb_eq in Hq. subst e'. exact (HT _ He' a Ha).
Qed.

Lemma s28_ro_end : forall ee, existsb (Z.eqb ee) cmd_ro_ends = true -> In ee cmd_ro_ends.
Proof. intros ee H. apply existsb_exists in H as (e' & He' & Hq). apply Z.eqb_eq in Hq. subst e'. exact He'. Qed.

Lemma s28_no0 : forall s : list byte, forallb (fun b : byte => negb (bv_unsigned b =? 0)) s = true ->
~ In (Z_to_bv 8 0) s.
Proof. intros s H Hin. rewrite forallb_forall in H. specialize (H _ Hin). vm_compute in H. discriminate H. Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The walk after sup_broadcast, in its own section: it runs at the FP state sup_broadcast returns, so it is proved
   here at this section's FP state and holds at every FP state once the section is closed. Its callee contract and
   record facts are this section's, at this FP state. *)
Section e1.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TSUP_HOST_SETTING : tsup_host_setting_spec B MT.
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

(* the meter of sup_host_setting: record's spill arm (none: one recorded call), arg_line's copy of the line, arg_s's
   copy of the printed count, xmalloc's word list, arg_s's copy of it (4 mallocs) and the list's free *)
Lemma s28_meter_hs : forall e Sc k nm R line toks,
vr_ent B MT e -> vr_meter MT e Sc k nm -> rec_spill_frees R = 0 ->
Z.of_nat (length line) <= 8192 -> hs_words_len toks <= Z.of_nat (length line) + 1 -> (length toks <= 64)%nat ->
k + EV_SUP_HOST_SETTING R <= ev_vr (e_R e) (e_D e) ->
mo_ok MT Sc (XM_SUP_HOST_SETTING MT R line toks) /\
(forall S2, mo_le MT Sc S2 (XM_SUP_HOST_SETTING MT R line toks) ->
  vr_meter MT e S2 (k + EV_SUP_HOST_SETTING R) (nm + 4)).
Proof.
intros e Sc k nm R line toks Hent Hm Hc Hl Hh Ht Hk.
assert (HEV : EV_SUP_HOST_SETTING R = 5)
  by (unfold EV_SUP_HOST_SETTING, EV_RECORD, EV_ARG_LINE, EV_REC_CANONICAL, EV_ARG_S, EV_XMALLOC; rewrite Hc; reflexivity).
pose proof (dec_length (Z.of_nat (length toks)) ltac:(lia)) as Hd.
pose proof (vr_join_len toks) as Hj. pose proof (vr_hs_nonneg toks) as Hh0.
apply (q_meter B MT e Sc k nm _ 4 1 (EV_SUP_HOST_SETTING R) MTL Hent Hm); [| lia | lia | exact Hk].
unfold XM_SUP_HOST_SETTING, XM_RECORD, XM_ARG_LINE, XM_REC_CANONICAL, XM_ARG_S, sarg.
unfold XM_XMALLOC, LIVE_XMALLOC. cbv beta iota. rewrite Hc. rewrite !Z.max_l by lia.
pose proof (q_mall MT (Z.of_nat (length line) + 1) MTL ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M1.
pose proof (q_mall MT (Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1) MTL ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M2.
pose proof (q_mall MT (hs_words_len toks + 1) MTL ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M3.
pose proof (q_mall MT (Z.of_nat (length (join_sp toks)) + 1) MTL ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M4.
lia.
Qed.

Lemma s28_tok_shadow : forall (W : world SEGS) mem lyc pos F n, vr_frame lyc W mem pos F vr_sh2 -> F mod 8 = 0 ->
0 <= n <= 64 -> 0 <= F ->
range_addressable (rdW W mem) SHADOW_OFF (F + 32) (8 * n).
Proof.
intros W mem lyc pos F n (_ & _ & Hsh) HF8 Hn HF0.
apply zero_shadow_range; [rewrite Zplus_mod, HF8; reflexivity | rewrite Z.mul_comm, Z_mod_mult; reflexivity|].
intros i Hi. rewrite Z.mul_comm, Z_div_mult in Hi by lia.
unfold shadow_of_addr.
assert (D : (F + 32) / 8 = F / 8 + 4) by (rewrite <- (Z.div_add F 4 8) by lia; f_equal; lia).
assert (E : SHADOW_OFF + (F + 32) / 8 + i = shadow_addr F + Z.of_nat (4 + Z.to_nat i)).
{ unfold shadow_addr. rewrite D, Nat2Z.inj_add, Z2Nat.id by lia. cbn [Z.of_nat Pos.of_succ_nat]. lia. }
rewrite E, (Hsh (4 + Z.to_nat i)%nat ltac:(lia)), s28_nth_sh2 by lia. reflexivity.
Qed.

(* the walk after sup_broadcast, at this section's FP state (s28_BC uses it at the FP state sup_broadcast returns):
   0x8d948 mv s10,a0 ; mv a0,s2 ; ld s3,40(s1) ; mv a1,s3 ; mv a2,s9 ; jal sup_host_setting ; then s28_tail *)
Lemma s28_BC2 : forall e pos F q c p0 tps v args k nm q1 O1 ly3 S3 (W3 : world SEGS) regs3 mem3 md3,
vr_ent B MT e -> frm0 fx ->
Verbs.toks (e_D e) = v :: args -> VQ8.route (v :: args) = VQ8.RBroad -> k <= 2 -> nm <= VR_NM_PRE ->
vr_core B MT e pos F ((q1, Z.of_nat (length (snd (sup_broadcast_m (e_R e) (Verbs.line (e_D e))))) + 1) ::
  [vr_lb e q; vr_cb e c]) vr_sh2 (vr_sl3 F q c)
  [(10, q1); (18, q); (21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, p0)]
  (fst (sup_broadcast_m (e_R e) (Verbs.line (e_D e)))) O1 (e_q0 e) (k + EV_SUP_BROADCAST (e_R e))
  (2 + EV_SUP_BROADCAST (e_R e)) (nm + 3) 5 ly3 S3 W3 regs3 mem3 md3 ->
vr_line B e q W3 mem3 -> vr_copy B e F c (p0 :: tps) W3 mem3 ->
astr_atR (rdW W3 mem3) q1 (snd (sup_broadcast_m (e_R e) (Verbs.line (e_D e)))) ->
SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + S28_H)) mem3 (seg_rom SEGS)) md3)
(fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\ vr_athd (fx := fq) B MT 0x8d6a4 e W' cf').
Proof.
intros e pos F q c p0 tps v args k nm q1 O1 ly3 S3 W3 regs3 mem3 md3 Hent Hfrm Et HPb Hkk Hnm HcM HlM HcpM Hstr1.
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & HREC0 & Hcalls & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & Hfr4 & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (s28_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
set (R1 := fst (sup_broadcast_m (e_R e) (Verbs.line (e_D e)))) in *.
set (t1 := snd (sup_broadcast_m (e_R e) (Verbs.line (e_D e)))) in *.
assert (Ht28 : (length t1 <= 28)%nat).
{ unfold t1, sup_broadcast_m. apply vr_text_len. exact (q_code_range B _ _ _ _ _ HREC0). }
pose proof HcM as (HJ3 & _ & _ & _ & HframeM0 & _).
pose proof (proj1 HJ3) as HAR3.
pose proof (s28_frames_own B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as Hin4.
pose proof HframeM0 as (HFa & _ & _).
destruct (s28_frame_bounds B ly3 S3 W3 mem3 md3 pos HAR3 Hin4) as (BF1 & BF2 & BF3 & BF4).
rewrite <- HFa in BF1, BF2, BF3, BF4.
destruct (q_shadow_range F BF1 BF2) as [HSA1 HSA2].
destruct (q_tmps B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HcM) as (HtB0 & _ & _).
pose proof (HtB0 _ (or_intror (or_introl eq_refl))) as Hlb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hlb) as (_ & Hq4096 & Hqc & _).
unfold vr_lb in Hq4096, Hqc. cbn [fst snd] in Hq4096, Hqc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 (HtB0 _ (or_introl eq_refl))) as (_ & Hq1 & _).
assert (HL : 0 <= vr_l (e_n e) (e_D e) <= e_n e) by (apply verbs_receive_pre.strnlen_res_le; lia).
assert (HLL : Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e)) by (apply vr_line_le_l; exact HlenD).
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (s28_toks_le (e_D e)) as Htk64.
pose proof HcpM as (_ & (HF8' & HlenP & _)).
assert (Hlen1 : (1 <= length (v :: args) <= 64)%nat)
  by (split; [cbn [length]; lia | pose proof (s28_toks_le (e_D e)) as H; rewrite Et in H; exact H]).
assert (Hnt : vr_ntok (e_D e) = Z.of_nat (length (v :: args))) by (unfold vr_ntok; rewrite Et; reflexivity).
assert (Hhs' : hs_words_len (v :: args) <= Z.of_nat (length (Verbs.line (e_D e))) + 1)
  by (pose proof (vr_hs_toks (e_D e)) as H; rewrite Et in H; exact H).
set (tks := v :: args) in *.
set (tp := p0 :: tps) in *.
assert (Hst : vr_st (e_D e) = Verbs.SBroadcast (Verbs.line (e_D e)) tks) by exact (vr_st_broad (e_D e) v args Et HPb).
assert (Hk1 : vr_k1 (e_R e) (e_D e) = 2 + (EV_SUP_BROADCAST (e_R e) + EV_SUP_HOST_SETTING R1))
  by exact (vr_k1_broad (e_R e) (e_D e) v args Et HPb).
assert (HX : vr_x (e_R e) (e_D e) = t1) by exact (vr_x_broad _ _ _ _ Hst).
assert (HR1 : vr_R1 (e_R e) (e_D e) = sup_host_setting_m R1 (Verbs.line (e_D e)) tks) by exact (vr_R1_broad _ _ _ _ Hst).
assert (Hqv : vr_qv e = e_q0 e) by (unfold vr_qv; rewrite (vr_quit_broad _ _ _ _ Hst); reflexivity).
assert (HEVb : EV_SUP_BROADCAST (e_R e) = 4)
  by (unfold EV_SUP_BROADCAST, EV_RECORD, EV_ARG_LINE, EV_REC_CANONICAL, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC;
      rewrite (q_spill0 _ Hcalls); reflexivity).
assert (Hsp1 : rec_spill_frees R1 = 0) by exact (s28_bcast_spill (e_R e) (Verbs.line (e_D e)) Hcalls).
assert (HEVh : EV_SUP_HOST_SETTING R1 = 5)
  by (unfold EV_SUP_HOST_SETTING, EV_RECORD, EV_ARG_LINE, EV_REC_CANONICAL, EV_ARG_S, EV_XMALLOC; rewrite Hsp1;
      reflexivity).
assert (Hev2 : 2 + (EV_SUP_BROADCAST (e_R e) + EV_SUP_HOST_SETTING R1) <= ev_vr (e_R e) (e_D e))
  by (pose proof (q_k1_ev (e_R e) (e_D e)); pose proof s28_ev_reply; lia).
set (rlM := [(10, q1); (18, q); (21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, p0)]) in *.
(* 0x8d948: mv s10,a0; mv a0,s2; ld s3,40(s1); mv a1,s3; mv a2,s9; jal sup_host_setting *)
pose proof HcM as (HJM & _ & HmeterM & HnmM & HframeM & HrvM & _ & HspillM & HenvM & HrecM & _).
assert (HspM : forall o val, In (o, val) (q_sl F q) -> aval_mem (rdW W3 mem3) (vr_s1 e + o) 8 val).
{ intros o val Hi. unfold vr_spill in HspillM. rewrite Forall_forall in HspillM.
  exact (HspillM (o, val) (q_sl_of_sl3 F q c o val Hi)). }
assert (R9M : getr regs3 (Z_to_bv 5 9) = w64 (vr_s1 e))
  by (apply (vr_rv_get _ _ 9 _ HrvM); unfold vr_base; cbn [app In]; tauto).
assert (R10M : getr regs3 (Z_to_bv 5 10) = w64 q1) by (apply (vr_rv_get _ _ 10 _ HrvM); unfold rlM, vr_base; cbn [app In]; tauto).
assert (R18M : getr regs3 (Z_to_bv 5 18) = w64 q) by (apply (vr_rv_get _ _ 18 _ HrvM); unfold rlM, vr_base; cbn [app In]; tauto).
assert (R25M : getr regs3 (Z_to_bv 5 25) = w64 (vr_ntok (e_D e)))
  by (apply (vr_rv_get _ _ 25 _ HrvM); unfold rlM, vr_base; cbn [app In]; tauto).
pose proof (q_seedS W3 regs3 mem3 S28_H (vr_s1 e) q F 0 0 R9M ltac:(lia) ltac:(lia) ltac:(lia) BF1 BF2 ltac:(lia)
  ltac:(lia) HspM) as HS2.
remember (Eimg (Ereg regs3 (q_extra q F 0 0))) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (HAE2 : env_agree 32 (Ereg regs3 (q_extra q F 0 0)) E2) by (subst E2; apply q_env_agree).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs3 r)
  by (intros n r Hn; subst E2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX2 : forall j, (j < 5)%nat -> ew E2 (32 + j) = nth j (q_extra q F 0 0) (Z_to_bv 64 0))
  by (intros j Hj; subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
clear HE2.
assert (X33 : ew E2 33 = Z_to_bv 64 F) by exact (EX2 1%nat ltac:(lia)).
paj_run_shc RUNP RUNC HS2 HJ3.
{ q_awr. }
lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?m) => rename m into msH end.
match goal with |- context [with_vm_backing (m_vm_lazy md3) ?mt md3] =>
  set (mdv2 := with_vm_backing (m_vm_lazy md3) mt md3) in * end.
clearbody mdv2.
pose proof (q_rdeq_of_frame _ _ _ _ _ HFr q_ro_rsp) as Eq2. clear HF HFr HG.
prreg HS2 (1%bv : bv 5) Q1h. prreg HS2 (10%bv : bv 5) Q10h. prreg HS2 (11%bv : bv 5) Q11h.
prreg HS2 (12%bv : bv 5) Q12h. prreg HS2 (19%bv : bv 5) Q19h. prreg HS2 (26%bv : bv 5) Q26h.
rewrite (EE2 18%nat (Z_to_bv 5 18) eq_refl), R18M in Q10h.
rewrite X33, unsigned_lit_small in Q11h, Q19h by lia.
rewrite (EE2 25%nat (Z_to_bv 5 25) eq_refl), R25M in Q12h.
rewrite (EE2 10%nat (Z_to_bv 5 10) eq_refl), R10M in Q26h.
pose proof (q_kept_regs E2 _ _ regs3 (q_extra q F 0 0) [2; 3; 4; 8; 9; 18; 21; 25] HS2 HAE2
  ltac:(vm_compute; reflexivity)) as KR2.
cbn [ms_regs restrict] in KR2.
pmkst HS2.
rewrite (SIGP CS_sup_host_setting) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_sup_host_setting) with AF_sup_host_setting.
set (rlH := [(1, BASE + S28_I); (10, q); (11, F + 32); (12, vr_ntok (e_D e)); (18, q); (19, F + 32);
  (21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, q1)]).
assert (HcoreH : vr_core B MT e pos F ((q1, Z.of_nat (length t1) + 1) :: [vr_lb e q; vr_cb e c]) vr_sh2 (vr_sl3 F q c)
  rlH R1 O1 (e_q0 e) (k + EV_SUP_BROADCAST (e_R e)) (2 + EV_SUP_BROADCAST (e_R e)) (nm + 3) 5
  ly3 S3 W3 (ms_regs msH) (ms_mem msH) mdv2).
{ apply (q_core_same B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 regs3 mem3 md3 W3 (ms_regs msH) (ms_mem msH) mdv2
    HcM HJ3 Eq2).
  apply (q_rv_keep B e (ms_regs msH) regs3 _ _ HrvM).
  - intros r0 Hr. apply KR2. cbn in Hr |- *. tauto.
  - intros r0 val Hi. unfold rlH in Hi. cbn in Hi.
    destruct Hi as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]]]; injection E1 as <- <-.
    + right. exact Q1h.
    + right. exact Q10h.
    + right. exact Q11h.
    + right. exact Q12h.
    + left. split; [unfold rlM; cbn; tauto | apply KR2; cbn; tauto].
    + right. exact Q19h.
    + left. split; [unfold rlM; cbn; tauto | apply KR2; cbn; tauto].
    + left. split; [unfold rlM; cbn; tauto | apply KR2; cbn; tauto].
    + right. exact Q26h. }
pose proof (q_line_same B e q W3 mem3 W3 (ms_mem msH) Eq2 HlM) as HlineH.
pose proof (q_copy_same B e F c tp W3 mem3 W3 (ms_mem msH) Eq2 HcpM) as HcopyH.
pose proof HcoreH as (HJH & HkkH & HmeterH & HnmH & HframeH & HrvH & _ & _ & HenvH & HrecH & _).
pose proof HenvH as (HROH & _ & HROkH & _).
pose proof (proj1 HJH) as HARH.
destruct (q_tmps B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HcoreH) as (HtBH & HtOH & HOinH).
assert (Hlen1' : length tp = length tks) by (rewrite HlenP, Et; reflexivity).
pose proof HframeH as (HFaH & _).
pose proof (s28_frames_own B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJH) as Hin4H.
assert (HF8 : F mod 8 = 0).
{ replace F with ((F + 32) + (-4) * 8) by lia. rewrite Z_mod_plus_full. exact HF8'. }
destruct (s28_meter_hs e S3 (k + EV_SUP_BROADCAST (e_R e)) (nm + 3) R1 (Verbs.line (e_D e)) tks Hent HmeterH Hsp1
  ltac:(lia) Hhs' ltac:(lia) ltac:(lia)) as [HmokH Hmeter4].
assert (HSH : SUP_HOST_SETTING_STK = ltac:(let x := eval vm_compute in SUP_HOST_SETTING_STK in exact x)) by reflexivity.
assert (Hwords : forall i p w, nth_error tp i = Some p -> nth_error tks i = Some w ->
  (in_blockA (ablocks B ly3 S3) p (Z.of_nat (length w) + 1) /\
   Forall (fun qk => iv_apart p (Z.of_nat (length w) + 1) (fst qk) (snd qk)) O1 /\
   astr_atR (rdW W3 (ms_mem msH)) p w /\ Z.of_nat (length w) + 1 <= LMAX + 1) /\
  aval_mem (rdW W3 (ms_mem msH)) (F + 32 + 8 * Z.of_nat i) 8 p /\ 4096 <= p /\
  p + Z.of_nat (length w) + 1 <= alloc_ceiling).
{ intros i p w Hp Hw.
  destruct (q_tok_arg B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c tp i p w HcoreH
    (or_intror (or_intror (or_introl eq_refl))) HcopyH Hp ltac:(rewrite Et; exact Hw))
    as (H1 & H2 & H3 & H4 & _ & _).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4]. }
eapply SRr_bind.
{ eapply (q_rcallF B MT HB PROGU e pos F _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 (ms_regs msH) (ms_mem msH) mdv2
    AF_sup_host_setting SUP_HOST_SETTING_STK _ (EV_SUP_HOST_SETTING R1) S28_I _ Hent HcoreH).
  - exact Q1h.
  - unfold S28_I; lia.
  - reflexivity.
  - lia.
  - lia.
  - exact (s28_FP_hs O1).
  - intros ch HPRE2.
    apply (TSUP_HOST_SETTING ly3 S3 W3 (ms_regs msH) (ms_mem msH) mdv2 ch q (F + 32) tp (Verbs.line (e_D e)) tks R1 O1
      HPRE2 Hfrm).
    + exact HROH.
    + exact HROkH.
    + exact (vr_rv_get _ _ 10 _ HrvH ltac:(unfold rlH, vr_base; cbn [app In]; tauto)).
    + lia.
    + exact (vr_rv_get _ _ 11 _ HrvH ltac:(unfold rlH, vr_base; cbn [app In]; tauto)).
    + lia.
    + rewrite <- Hnt. exact (vr_rv_get _ _ 12 _ HrvH ltac:(unfold rlH, vr_base; cbn [app In]; tauto)).
    + exact Hlen1.
    + exact (q_line_arg B MT e pos F _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 (ms_regs msH) (ms_mem msH) mdv2 q Hent HcoreH
        (or_intror (or_introl eq_refl)) HlineH).
    + lia.
    + rewrite Zplus_mod, HF8. reflexivity.
    + left. split; [|split].
      * exists 4, pos. split; [exact Hin4H|]. split; [lia|]. rewrite <- HFaH.
        split; [exact HF8|]. change (fs_frame_bytes 4) with 1024. lia.
      * rewrite Zplus_mod, HF8. reflexivity.
      * exact (s28_tok_shadow W3 (ms_mem msH) ly3 pos F (Z.of_nat (length tks)) HframeH HF8 ltac:(lia) ltac:(lia)).
    + exact Hlen1'.
    + intros i p Hp. destruct (s28_nth_some tp tks i p Hlen1' Hp) as (w & Hw).
      destruct (Hwords i p w Hp Hw) as (_ & H2 & H3 & H4). split; [lia | exact H2].
    + apply s28_forall2_of_nth; [exact Hlen1'|]. intros i p w Hp Hw. exact (proj1 (Hwords i p w Hp Hw)).
    + unfold LMAX. lia.
    + exact HrecH.
    + pose proof HJH as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. cbn [app length]. lia.
    + exact (q_nev B MT e pos F _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 (ms_regs msH) (ms_mem msH) mdv2
        (EV_SUP_HOST_SETTING R1) Hent HcoreH ltac:(lia)).
    + apply (q_live B MT e pos F _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 (ms_regs msH) (ms_mem msH) mdv2 _ 1 Hent HcoreH
        ltac:(unfold R1; rewrite (s28_bcast_calls (e_R e) (Verbs.line (e_D e)) Hcalls); lia)).
      unfold bsum, vr_lb, vr_cb. cbn [fold_right fst snd].
      pose proof (dec_length (Z.of_nat (length tks)) ltac:(lia)) as Hd.
      pose proof (vr_join_len tks) as Hj. pose proof (vr_hs_nonneg tks) as Hh0.
      unfold LIVE_SUP_HOST_SETTING, LIVE_ARG_LINE, LIVE_REC_CANONICAL, LIVE_ARG_S, sarg.
      unfold LIVE_XMALLOC. cbv beta iota. rewrite !Z.max_l by lia.
      unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ, LMAX. lia.
    + exact HmokH. }
cbv beta. intros W4 c4 _ (fx2 & ly4 & S4 & regs4 & mem4 & md4 & Hfx2 & -> & HJ4 & HJc4 & HP4 & HK4).
destruct HK4 as (O2 & Hrec2 & HO2 & HB1' & HB2' & _ & Hmle2).
set (rl4 := [(18, q); (19, F + 32); (21, vr_ntok (e_D e)); (26, q1)]).
assert (Hrv4 : vr_rv regs4 (vr_base B e ++ rl4)).
{ apply (q_rv_keep B e regs4 (ms_regs msH) _ _ HrvH).
  - intros r0 Hr. apply HP4. unfold acallee_saved. cbn in Hr. lia.
  - intros r0 val Hi. unfold rl4 in Hi. cbn in Hi. destruct Hi as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-;
      (left; split; [unfold rlH; cbn; tauto | apply HP4; unfold acallee_saved; lia]). }
(* the reply text survives sup_host_setting: its block is none of the recorder's *)
destruct (s28_keep B MT ROA RRO RPG RECC PROGU e pos F q c rlH ((q1, Z.of_nat (length t1) + 1) :: [vr_lb e q; vr_cb e c])
  R1 O1 (e_q0 e) (k + EV_SUP_BROADCAST (e_R e)) (2 + EV_SUP_BROADCAST (e_R e)) (nm + 3) 5 ly3 S3 W3 (ms_regs msH)
  (ms_mem msH) mdv2 SUP_HOST_SETTING_STK _ (EV_SUP_HOST_SETTING R1) ly4 S4 W4 mem4 md4 HcoreH HJc4 (s28_FP_hs O1))
  as (_ & _ & _ & _ & _ & KB4 & _).
assert (Ht1in : In (q1, Z.of_nat (length t1) + 1) (ablocks B ly3 S3)) by (apply HtBH; left; reflexivity).
assert (Ht1O : ~ In (q1, Z.of_nat (length t1) + 1) O1) by (apply HtOH; left; reflexivity).
assert (Ht1in4 : In (q1, Z.of_nat (length t1) + 1) (ablocks B ly4 S4)) by exact (HB1' _ Ht1in Ht1O).
pose proof (req_size_pos (Z.of_nat (length t1) + 1) ltac:(lia)) as [_ Hrt1].
assert (Hstr4 : astr_atR (rdW W4 mem4) q1 t1).
{ apply (astr_atR_agree (rdW W3 (ms_mem msH)) _ q1 t1 (Z.of_nat (length t1) + 1)); [|lia|].
  - exact (q_astr_eq _ _ _ _ Eq2 Hstr1).
  - intros kk Hk4. exact (KB4 q1 _ kk Ht1in Ht1O Ht1in4 ltac:(lia)). }
destruct (s28_post_same B MT ROA RRO RPG RECC PROGU e pos F q c tp rlH rl4
  ((q1, Z.of_nat (length t1) + 1) :: [vr_lb e q; vr_cb e c]) R1 O1 (k + EV_SUP_BROADCAST (e_R e))
  (2 + EV_SUP_BROADCAST (e_R e)) (nm + 3) 5 ly3 S3 W3 (ms_regs msH) (ms_mem msH) mdv2 SUP_HOST_SETTING_STK _
  (EV_SUP_HOST_SETTING R1) ly4 S4 W4 mem4 md4 regs4 (sup_host_setting_m R1 (Verbs.line (e_D e)) tks) O2
  (k + EV_SUP_BROADCAST (e_R e) + EV_SUP_HOST_SETTING R1) (vr_k1 (e_R e) (e_D e)) (nm + 3 + 4) VR_NM_HD
  Hent HcoreH HlineH HcopyH (or_intror (or_introl eq_refl)) (or_intror (or_intror (or_introl eq_refl)))
  HJc4 HJ4 (s28_FP_hs O1) ltac:(rewrite Hk1; lia) (Hmeter4 S4 Hmle2) ltac:(unfold VR_NM_HD, VR_NM_PRE in *; lia)
  Hrec2 HO2 HB1' HB2' Hrv4) as (O3 & _ & Hc4 & Hl4 & Hcp4).
(* 0x8d960: the reloads and the jump to JA, at the FP state sup_host_setting returned (s28_tail at fx2) *)
eapply SRr_mono.
{ exact (s28_tail (fx := fx2) B MT e ((q1, Z.of_nat (length t1) + 1) :: [vr_lb e q; vr_cb e c]) _ _ _ _ _
    q1 pos F q c tp ly4 S4 W4 regs4 mem4 md4 _ _
    (q_ent_fxr B MT fx fx2 e Hent Hfx2) (or_intror (or_introl eq_refl)) Hc4 Hl4 Hcp4). }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & Em & Hc5 & Hl5 & Hcp5).
exists fx2. split; [exact Hfx2|].
unfold vr_athd, vr_hd.
exists q1, O3, pos, F, q, c, tp, ly4, S4, regs5, mem5, md5, (k + EV_SUP_BROADCAST (e_R e) + EV_SUP_HOST_SETTING R1),
  (nm + 3 + 4).
split; [reflexivity|].
split; [unfold vr_hd_ntok; rewrite Et; simpl; lia|].
split; [lia|].
rewrite HX, HR1, Hqv.
split; [exact (q_astr_eq _ _ _ _ Em Hstr4)|].
split; [exact Hc5|]. split; [exact Hl5 | exact Hcp5].
Qed.

End e1.
End f.
End d.

(* ---------------------------------------------------------------------------------------------------------------
   The segment, at the FP state of its entry *)
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
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
(* the callee contracts (fx-generic, lib/B/Prog/verbs_receive_c.v:240, :243, :244, :259) and the record facts of the
   brief, with their names *)
Hypothesis TVERB_IS : forall fx0 : YK11.FPState, @tverb_is_spec fx0 rc SK PI B MT.
Hypothesis TSUP_CONNECT : forall fx0 : YK11.FPState, @tsup_connect_spec fx0 rc SK PI B MT.
Hypothesis TSUP_BROADCAST : forall fx0 : YK11.FPState, @tsup_broadcast_spec fx0 rc SK PI B MT.
Hypothesis TSUP_HOST_SETTING : forall fx0 : YK11.FPState, @tsup_host_setting_spec fx0 rc SK PI B MT.
Hypothesis HB : YF0m.CmdBSyms B.
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

Lemma s28_unowned : forall lo hi a, lo <= a < hi ->
forallb (fun r => ((fst r + snd r <=? lo) || (hi <=? fst r))%bool) YF0m.Tfib_owned_static = true ->
~ Exists (in_zr a) (as_owned_static B).
Proof.
intros lo hi a Ha Hall. rewrite (YF0m.ts_owned B HB). rewrite forallb_forall in Hall.
intros Hex. apply Exists_exists in Hex as (r & Hr & Hz). specialize (Hall r Hr). unfold in_zr in Hz.
apply orb_true_iff in Hall as [H | H]; apply Z.leb_le in H; lia.
Qed.

Lemma s28_lit_conn : forall ly S (W : world SEGS) mem,
cmd_ro_ok (rdW W mem) -> cmd_ro_in (in_roP SEGS RLO RHI) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] 0x22840 (Some Verbs.Lit.fmt_connect) /\
atail_vis SEGS W mem (0x22840 + Z.of_nat (length Verbs.Lit.fmt_connect)).
Proof.
intros ly S W mem HRO HRIN.
destruct (s28_ro_lits _ HRO) as [Hb _].
split.
- cbn [astr_argA]. split; [lia|].
  split; [split; [exact Hb | apply s28_no0; vm_compute; reflexivity]|].
  split; [unfold LMAX; cbn; lia|].
  right. split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | apply s28_ro_end; vm_compute; reflexivity]]].
  intros i Hi. change (Z.of_nat (length Verbs.Lit.fmt_connect) + 1) with 14 in Hi.
  split; [|split].
  + unfold cmd_ro_in in HRIN. decompose [and] HRIN.
    match goal with H : forall i, 0 <= i < 14 -> in_roP SEGS RLO RHI (0x22840 + i) |- _ => exact (H i Hi) end.
  + exact (s28_unowned 0x22840 0x2284e (0x22840 + i) ltac:(lia) ltac:(vm_compute; reflexivity)).
  + rewrite (YF0m.ts_errno B HB). unfold YF0m.TFIB_ERRNO. lia.
- apply (s28_ro_tail W mem); [exact HRO | vm_compute; reflexivity].
Qed.

Lemma s28_lit_disc : forall ly S (W : world SEGS) mem,
cmd_ro_ok (rdW W mem) -> cmd_ro_in (in_roP SEGS RLO RHI) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] 0x22860 (Some Verbs.Lit.fmt_disconnect) /\
atail_vis SEGS W mem (0x22860 + Z.of_nat (length Verbs.Lit.fmt_disconnect)).
Proof.
intros ly S W mem HRO HRIN.
destruct (s28_ro_lits _ HRO) as [_ Hb].
split.
- cbn [astr_argA]. split; [lia|].
  split; [split; [exact Hb | apply s28_no0; vm_compute; reflexivity]|].
  split; [unfold LMAX; cbn; lia|].
  right. split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | apply s28_ro_end; vm_compute; reflexivity]]].
  intros i Hi. change (Z.of_nat (length Verbs.Lit.fmt_disconnect) + 1) with 17 in Hi.
  split; [|split].
  + unfold cmd_ro_in in HRIN. decompose [and] HRIN.
    match goal with H : forall i, 0 <= i < 17 -> in_roP SEGS RLO RHI (0x22860 + i) |- _ => exact (H i Hi) end.
  + exact (s28_unowned 0x22860 0x22871 (0x22860 + i) ltac:(lia) ltac:(vm_compute; reflexivity)).
  + rewrite (YF0m.ts_errno B HB). unfold YF0m.TFIB_ERRNO. lia.
- apply (s28_ro_tail W mem); [exact HRO | vm_compute; reflexivity].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The states inside the segment: a pc, the registers besides the base, a fact about the message's words, and
   the boundary state of the interface with the entry's recorder *)
Definition s28_rl0 (e : vrE) (tp : list Z) : list (Z * Z) :=
[(21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, hd 0 tp)].
Definition s28_rlb (b : Z) (e : vrE) (tp : list Z) : list (Z * Z) := (10, b) :: s28_rl0 e tp.

Definition s28_at (pc : Z) (rlf : list Z -> list (Z * Z)) (P : Prop) (e : vrE) : world SEGS -> config -> Prop :=
fun Wc cf => exists pos F q c tp lyc Sc regsc memc mdc k nm,
cf = mkCfg (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)) mdc /\ P /\
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (rlf tp) (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE
  lyc Sc Wc regsc memc mdc /\
vr_line B e q Wc memc /\ vr_copy B e F c tp Wc memc.

Definition s28_P0 (e : vrE) : Prop :=
match Verbs.toks (e_D e) with v :: args => VQ8.route (v :: args) = VQ8.route_cd v args | [] => False end.
Definition s28_P1 (e : vrE) : Prop :=
s28_P0 e /\ Verbs.verb_is_m (hd [] (Verbs.toks (e_D e))) Verbs.Lit.fmt_connect = false.
Definition s28_Pconn (e : vrE) : Prop :=
match Verbs.toks (e_D e) with [v; a; b] => VQ8.route [v; a; b] = VQ8.RConn | _ => False end.
Definition s28_Pbroad (e : vrE) : Prop :=
match Verbs.toks (e_D e) with v :: args => VQ8.route (v :: args) = VQ8.RBroad | [] => False end.

(* the state at a pc reached by a run that kept the memory and the registers of the boundary *)
Lemma s28_kept : forall e pos F q c tp lyc Sc (W : world SEGS) regsc memc mdc k nm rl rl' regs' mem' md',
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

Lemma s28_rl0_sub : forall e tp b r v, In (r, v) (s28_rl0 e tp) -> In (r, v) (s28_rlb b e tp).
Proof. intros e tp b r v H. right. exact H. Qed.
Lemma s28_rl0_regs : forall e tp r v, In (r, v) (s28_rl0 e tp) -> In r [21; 25; 26].
Proof. intros e tp r v Hi. unfold s28_rl0 in Hi. cbn in Hi |- *. destruct Hi as [E1|[E1|[E1|[]]]]; injection E1 as <- _; tauto. Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Leg V1: from 0x8d8c4, verb_is(tok[0], "connect %s %s"), to its return at 0x8d8d4 *)
Lemma s28_V1 : forall e W cf, vr_ent B MT e -> vr_s28in B MT e W cf ->
SRr SEGS W cf (s28_at S28_B (s28_rlb (s28_b Verbs.Lit.fmt_connect (e_D e)) e) (s28_P0 e) e).
Proof.
intros e W cf Hent Hin.
destruct Hin as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hcore & Hline & Hcopy).
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & _ & Hcalls & _ & _ & _ & _ & _
  & _ & _ & _ & HROIN & VOBJS & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _).
assert (HP0 : s28_P0 e) by exact Hroute.
unfold s28_P0 in Hroute.
destruct (Verbs.toks (e_D e)) as [|v args] eqn:Et; [contradiction|].
pose proof (s28_ev0 (e_R e) (e_D e) v args Et Hroute) as Hev0.
pose proof Hcopy as (_ & (_ & HlenP & _)).
destruct tp as [|p0 tps]; [rewrite Et in HlenP; discriminate HlenP|].
assert (R26 : getr regsc (Z_to_bv 5 26) = w64 p0)
  by (apply (vr_rv_get _ _ 26 _ Hrv); unfold vr_base; cbn [app In hd]; tauto).
rewrite <- (s28_cfg fx regsc memc mdc 0x8d8c4 S28_A ltac:(unfold S28_A, AF_verbs_receive; lia)).
pose proof (q_seed0 W regsc memc S28_A) as HS.
remember (Eimg (Ereg regsc [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply q_env_agree).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (X359 : ew E 359 = Z_to_bv 64 0x22840).
{ rewrite (img_env_atomP E 359 HEI ltac:(unfold A_TEXT, A_LIM; lia)).
  change 359%nat with (A_OBJ 118). rewrite (VOBJS 118%nat ltac:(vm_compute; lia)). reflexivity. }
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
  set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
clearbody mdv.
pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq1. clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), R26 in Q10. rewrite X359 in Q11.
pose proof (q_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 21; 25; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
rewrite (SIGP CS_verb_is) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_verb_is) with AF_verb_is.
assert (HcoreM : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(1, BASE + S28_B); (21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, p0)]
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
pose proof HcoreM as (_ & _ & _ & _ & _ & HrvM & _ & _ & HenvM & _).
pose proof HenvM as (HROm & _ & HROkm & _).
destruct (q_tok_arg B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c (p0 :: tps) 0%nat p0 v HcoreM
  (or_intror (or_introl eq_refl)) HcopyM eq_refl ltac:(rewrite Et; reflexivity))
  as ((Hib & _ & Hstr & Hlm) & _ & Hp04 & Hp0c & _).
destruct (s28_lit_conn lyc Sc W (ms_mem ms) HROkm HROIN) as [Hlit Htail].
pose proof (q_nev B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W _ _ _ EV_VERB_IS Hent HcoreM Hev0) as Hnev.
assert (HSV : VERB_IS_STK = 8224) by reflexivity.
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
eapply SRr_bind.
{ apply (q_na_call B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs ms) (ms_mem ms) mdv AF_verb_is
    VERB_IS_STK EV_VERB_IS S28_B
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
       getr regs' 10 = w64 (if Verbs.verb_is_m v Verbs.Lit.fmt_connect then 1 else 0) /\
       Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\ ly' = lyc /\ S' = Sc) HcoreM Hal16).
  - exact Q1.
  - unfold S28_B. lia.
  - reflexivity.
  - lia.
  - lia.
  - intros HPRE1.
    exact (TVERB_IS fx lyc Sc W (ms_regs ms) (ms_mem ms) mdv p0 0x22840 v Verbs.Lit.fmt_connect HPRE1 HROm Q10
      ltac:(lia) Q11 ltac:(lia) Hib Hstr Hlm Hlit Htail HROkm VOBJS Hnev). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & (Ha0 & _ & -> & ->)).
change EV_VERB_IS with 0 in HJ2. rewrite Z.add_0_r in HJ2.
assert (Hrv2 : vr_rv regs2 (vr_base B e ++ s28_rlb (s28_b Verbs.Lit.fmt_connect (e_D e)) e (p0 :: tps))).
{ apply (q_rv_keep B e regs2 (ms_regs ms) _ _ HrvM).
  - intros r Hr. apply HP. unfold acallee_saved. cbn in Hr. lia.
  - intros r val Hi. unfold s28_rlb, s28_rl0 in Hi. cbn in Hi. destruct Hi as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-.
    + right. unfold s28_b. rewrite Et. cbn [hd]. exact Ha0.
    + left. split; [cbn; tauto | apply HP; unfold acallee_saved; lia].
    + left. split; [cbn; tauto | apply HP; unfold acallee_saved; lia].
    + left. split; [cbn; tauto | apply HP; unfold acallee_saved; lia]. }
destruct (q_keep_na B MT ROA RRO RPG RECC PROGU e pos F q c (p0 :: tps) [vr_lb e q; vr_cb e c] _
  (s28_rlb (s28_b Verbs.Lit.fmt_connect (e_D e)) e (p0 :: tps))
  (e_R e) (e_O e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs ms) (ms_mem ms) mdv VERB_IS_STK EV_VERB_IS
  W2 regs2 mem2 md2 Hent HcoreM HlineM HcopyM (or_introl eq_refl) (or_intror (or_introl eq_refl)) HJc HJ2 Hrv2)
  as (Hc2 & Hl2 & Hcp2).
apply SRr_ret.
exists pos, F, q, c, (p0 :: tps), lyc, Sc, regs2, mem2, md2, k, nm.
split; [reflexivity|]. split; [exact HP0|].
split; [exact Hc2|]. split; [exact Hl2 | exact Hcp2].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Leg V2: from 0x8d8e4, verb_is(tok[0], "disconnect %s %s"), to its return at 0x8d8f4 *)
Lemma s28_V2 : forall e W cf, vr_ent B MT e -> s28_at S28_C (s28_rl0 e) (s28_P1 e) e W cf ->
SRr SEGS W cf (s28_at S28_D (s28_rlb (s28_b Verbs.Lit.fmt_disconnect (e_D e)) e) (s28_P1 e) e).
Proof.
intros e W cf Hent HA.
destruct HA as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & HP1 & Hcore & Hline & Hcopy).
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & _ & Hcalls & _ & _ & _ & _ & _
  & _ & _ & _ & HROIN & VOBJS & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _).
pose proof HP1 as (Hroute & _).
unfold s28_P0 in Hroute.
destruct (Verbs.toks (e_D e)) as [|v args] eqn:Et; [contradiction|].
pose proof (s28_ev0 (e_R e) (e_D e) v args Et Hroute) as Hev0.
pose proof Hcopy as (_ & (_ & HlenP & _)).
destruct tp as [|p0 tps]; [rewrite Et in HlenP; discriminate HlenP|].
assert (R26 : getr regsc (Z_to_bv 5 26) = w64 p0)
  by (apply (vr_rv_get _ _ 26 _ Hrv); unfold vr_base, s28_rl0; cbn [app In hd]; tauto).
pose proof (q_seed0 W regsc memc S28_C) as HS.
remember (Eimg (Ereg regsc [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply q_env_agree).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (X360 : ew E 360 = Z_to_bv 64 0x22860).
{ rewrite (img_env_atomP E 360 HEI ltac:(unfold A_TEXT, A_LIM; lia)).
  change 360%nat with (A_OBJ 119). rewrite (VOBJS 119%nat ltac:(vm_compute; lia)). reflexivity. }
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
  set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
clearbody mdv.
pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq1. clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), R26 in Q10. rewrite X360 in Q11.
pose proof (q_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 21; 25; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
rewrite (SIGP CS_verb_is) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_verb_is) with AF_verb_is.
assert (HcoreM : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(1, BASE + S28_D); (21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, p0)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs ms) (ms_mem ms) mdv).
{ apply (q_core_same B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc W (ms_regs ms) (ms_mem ms) mdv
    Hcore HJ Eq1).
  apply (q_rv_keep B e (ms_regs ms) regsc _ _ Hrv).
  - intros r Hr. apply KR. cbn in Hr |- *. tauto.
  - intros r val Hi. cbn in Hi. destruct Hi as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-.
    + right. exact Q1.
    + left. split; [unfold s28_rl0; cbn; tauto | apply KR; cbn; tauto].
    + left. split; [unfold s28_rl0; cbn; tauto | apply KR; cbn; tauto].
    + left. split; [unfold s28_rl0; cbn; tauto | apply KR; cbn; tauto]. }
pose proof (q_line_same B e q W memc W (ms_mem ms) Eq1 Hline) as HlineM.
pose proof (q_copy_same B e F c (p0 :: tps) W memc W (ms_mem ms) Eq1 Hcopy) as HcopyM.
pose proof HcoreM as (_ & _ & _ & _ & _ & HrvM & _ & _ & HenvM & _).
pose proof HenvM as (HROm & _ & HROkm & _).
destruct (q_tok_arg B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c (p0 :: tps) 0%nat p0 v HcoreM
  (or_intror (or_introl eq_refl)) HcopyM eq_refl ltac:(rewrite Et; reflexivity))
  as ((Hib & _ & Hstr & Hlm) & _ & Hp04 & Hp0c & _).
destruct (s28_lit_disc lyc Sc W (ms_mem ms) HROkm HROIN) as [Hlit Htail].
pose proof (q_nev B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W _ _ _ EV_VERB_IS Hent HcoreM Hev0) as Hnev.
assert (HSV : VERB_IS_STK = 8224) by reflexivity.
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
eapply SRr_bind.
{ apply (q_na_call B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs ms) (ms_mem ms) mdv AF_verb_is
    VERB_IS_STK EV_VERB_IS S28_D
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
       getr regs' 10 = w64 (if Verbs.verb_is_m v Verbs.Lit.fmt_disconnect then 1 else 0) /\
       Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\ ly' = lyc /\ S' = Sc) HcoreM Hal16).
  - exact Q1.
  - unfold S28_D. lia.
  - reflexivity.
  - lia.
  - lia.
  - intros HPRE1.
    exact (TVERB_IS fx lyc Sc W (ms_regs ms) (ms_mem ms) mdv p0 0x22860 v Verbs.Lit.fmt_disconnect HPRE1 HROm Q10
      ltac:(lia) Q11 ltac:(lia) Hib Hstr Hlm Hlit Htail HROkm VOBJS Hnev). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & (Ha0 & _ & -> & ->)).
change EV_VERB_IS with 0 in HJ2. rewrite Z.add_0_r in HJ2.
assert (Hrv2 : vr_rv regs2 (vr_base B e ++ s28_rlb (s28_b Verbs.Lit.fmt_disconnect (e_D e)) e (p0 :: tps))).
{ apply (q_rv_keep B e regs2 (ms_regs ms) _ _ HrvM).
  - intros r Hr. apply HP. unfold acallee_saved. cbn in Hr. lia.
  - intros r val Hi. unfold s28_rlb, s28_rl0 in Hi. cbn in Hi. destruct Hi as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-.
    + right. unfold s28_b. rewrite Et. cbn [hd]. exact Ha0.
    + left. split; [cbn; tauto | apply HP; unfold acallee_saved; lia].
    + left. split; [cbn; tauto | apply HP; unfold acallee_saved; lia].
    + left. split; [cbn; tauto | apply HP; unfold acallee_saved; lia]. }
destruct (q_keep_na B MT ROA RRO RPG RECC PROGU e pos F q c (p0 :: tps) [vr_lb e q; vr_cb e c] _
  (s28_rlb (s28_b Verbs.Lit.fmt_disconnect (e_D e)) e (p0 :: tps))
  (e_R e) (e_O e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs ms) (ms_mem ms) mdv VERB_IS_STK EV_VERB_IS
  W2 regs2 mem2 md2 Hent HcoreM HlineM HcopyM (or_introl eq_refl) (or_intror (or_introl eq_refl)) HJc HJ2 Hrv2)
  as (Hc2 & Hl2 & Hcp2).
apply SRr_ret.
exists pos, F, q, c, (p0 :: tps), lyc, Sc, regs2, mem2, md2, k, nm.
split; [reflexivity|]. split; [exact HP1|].
split; [exact Hc2|]. split; [exact Hl2 | exact Hcp2].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Leg D1: 0x8d8d4 beqz a0,0x8d8e4 ; li a0,3 ; beq s5,a0,0x8d900 ; j 0x8d93c *)
Lemma s28_D1 : forall e W cf, vr_ent B MT e ->
s28_at S28_B (s28_rlb (s28_b Verbs.Lit.fmt_connect (e_D e)) e) (s28_P0 e) e W cf ->
SRr SEGS W cf (fun W' cf' => s28_at S28_C (s28_rl0 e) (s28_P1 e) e W' cf' \/
  s28_at S28_E (s28_rl0 e) (s28_Pconn e) e W' cf' \/ s28_at S28_G (s28_rl0 e) (s28_Pbroad e) e W' cf').
Proof.
intros e W cf Hent HA.
destruct HA as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & HP0 & Hcore & Hline & Hcopy).
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _).
pose proof HP0 as Hroute. unfold s28_P0 in Hroute.
destruct (Verbs.toks (e_D e)) as [|v args] eqn:Et; [contradiction|].
assert (Hnt : vr_ntok (e_D e) = Z.of_nat (length (v :: args))) by (unfold vr_ntok; rewrite Et; reflexivity).
assert (Hnt64 : vr_ntok (e_D e) <= 64) by (unfold vr_ntok; pose proof (s28_toks_le (e_D e)); lia).
assert (Hb : s28_b Verbs.Lit.fmt_connect (e_D e) = if Verbs.verb_is_m v Verbs.Lit.fmt_connect then 1 else 0)
  by (unfold s28_b; rewrite Et; reflexivity).
assert (Hb01 : 0 <= s28_b Verbs.Lit.fmt_connect (e_D e) <= 1) by (rewrite Hb; destruct (Verbs.verb_is_m _ _); lia).
assert (R10 := vr_rv_get _ _ 10 _ Hrv ltac:(unfold vr_base, s28_rlb; cbn [app In]; tauto)).
assert (R21 := vr_rv_get _ _ 21 _ Hrv ltac:(unfold vr_base, s28_rlb, s28_rl0; cbn [app In]; tauto)).
pose proof (q_seed0 W regsc memc S28_B) as HS.
remember (Eimg (Ereg regsc [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply q_env_agree).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e))) by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 (s28_b Verbs.Lit.fmt_connect (e_D e)))
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), R10; reflexivity).
assert (Hkeep : forall pc ms mdx, (forall r, In r [2; 3; 4; 8; 9; 21; 25; 26] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) ->
  q_rdeq (rdW W memc) (rdW W (ms_mem ms)) ->
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
    lyc Sc W (ms_mem ms) mdx k ->
  forall P, P -> s28_at pc (s28_rl0 e) P e W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (ms_mem ms) (seg_rom SEGS)) mdx)).
{ intros pc ms mdx KR Eq HJx P HP.
  destruct (s28_kept e pos F q c tp lyc Sc W regsc memc mdc k nm _ (s28_rl0 e tp) (ms_regs ms) (ms_mem ms) mdx
    Hcore Hline Hcopy HJx Eq (s28_rl0_sub e tp _) KR (s28_rl0_regs e tp)) as (Hc2 & Hl2 & Hcp2).
  exists pos, F, q, c, tp, lyc, Sc, (ms_regs ms), (ms_mem ms), mdx, k, nm.
  split; [reflexivity|]. split; [exact HP|]. split; [exact Hc2|]. split; [exact Hl2 | exact Hcp2]. }
(* 0x8d8d4: beqz a0,0x8d8e4 *)
psrr_branch_pi RUNP BR HS.
- (* a0 = 0: not "connect", on to 0x8d8e4 *)
  rewrite branch_eq_U, (U_atom E 10 _ E10) in Hc by lia.
  change (U E (SLit 0)) with 0 in Hc. apply Z.eqb_eq in Hc. rewrite Hb in Hc.
  assert (Hc0 : Verbs.verb_is_m v Verbs.Lit.fmt_connect = false)
    by (destruct (Verbs.verb_is_m v Verbs.Lit.fmt_connect); [discriminate Hc | reflexivity]).
  clear Hc.
  paj_run_to_sh RUNTO HS HJ S28_C.
  { awr_ok_tac. }
  match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
    set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
  clearbody mdv.
  pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq. clear HF HFr HG.
  pose proof (q_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 21; 25; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pmkst HS. apply SRr_ret. left.
  apply (Hkeep S28_C _ mdv KR Eq HJ). split; [exact HP0|]. rewrite Et. exact Hc0.
- (* a0 <> 0: "connect" *)
  rewrite branch_eq_U, (U_atom E 10 _ E10) in Hc by lia.
  change (U E (SLit 0)) with 0 in Hc. rewrite Hb in Hc.
  assert (Hc1 : Verbs.verb_is_m v Verbs.Lit.fmt_connect = true)
    by (destruct (Verbs.verb_is_m v Verbs.Lit.fmt_connect); [reflexivity | discriminate Hc]).
  clear Hc.
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
    set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
  clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq1. clear HF HFr HG.
  (* 0x8d8dc: beq s5,a0,0x8d900 *)
  psrr_branch_pi RUNP BR HS.
  + (* three words: to the connect leg *)
    rewrite branch_eq_U, (U_atom E 21 _ E21) in Hc by lia.
    change (U E (SLit 3)) with 3 in Hc. apply Z.eqb_eq in Hc. rewrite Hnt in Hc.
    assert (Ha3 : exists a b, args = [a; b]).
    { destruct args as [|a [|b [|d r]]]; cbn in Hc; try lia. exists a, b. reflexivity. }
    destruct Ha3 as (a & b & ->). clear Hc.
    paj_run_to_sh RUNTO HS HJ S28_E.
    { awr_ok_tac. }
    match goal with |- context [with_vm_backing (m_vm_lazy mdv) ?mt mdv] =>
      set (mdv2 := with_vm_backing (m_vm_lazy mdv) mt mdv) in * end.
    clearbody mdv2.
    pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq2. clear HF HFr HG.
    pose proof (fun x => eq_trans (Eq2 x) (Eq1 x)) as Eq.
    pose proof (q_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 21; 25; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. apply SRr_ret. right. left.
    apply (Hkeep S28_E _ mdv2 KR Eq HJ). unfold s28_Pconn. rewrite Et. cbv beta iota.
    rewrite Hroute. exact (s28_rconn v a b Hc1).
  + (* not three words: to the broadcast leg *)
    rewrite branch_eq_U, (U_atom E 21 _ E21) in Hc by lia.
    change (U E (SLit 3)) with 3 in Hc. rewrite Hnt in Hc.
    assert (Hl2 : length args <> 2%nat) by (intros Hl; cbn [length] in Hc; rewrite Hl in Hc; cbn in Hc; discriminate Hc).
    clear Hc.
    paj_run_to_sh RUNTO HS HJ S28_G.
    { awr_ok_tac. }
    match goal with |- context [with_vm_backing (m_vm_lazy mdv) ?mt mdv] =>
      set (mdv2 := with_vm_backing (m_vm_lazy mdv) mt mdv) in * end.
    clearbody mdv2.
    pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq2. clear HF HFr HG.
    pose proof (fun x => eq_trans (Eq2 x) (Eq1 x)) as Eq.
    pose proof (q_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 21; 25; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. apply SRr_ret. right. right.
    apply (Hkeep S28_G _ mdv2 KR Eq HJ). unfold s28_Pbroad. rewrite Et. cbv beta iota.
    rewrite Hroute. exact (s28_rbroad_len v args Hl2).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Leg D2: 0x8d8f4 li a1,3 ; bne s5,a1,0x8d93c ; beqz a0,0x8d93c ; on to 0x8d900 *)
Lemma s28_D2 : forall e W cf, vr_ent B MT e ->
s28_at S28_D (s28_rlb (s28_b Verbs.Lit.fmt_disconnect (e_D e)) e) (s28_P1 e) e W cf ->
SRr SEGS W cf (fun W' cf' => s28_at S28_E (s28_rl0 e) (s28_Pconn e) e W' cf' \/
  s28_at S28_G (s28_rl0 e) (s28_Pbroad e) e W' cf').
Proof.
intros e W cf Hent HA.
destruct HA as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & HP1 & Hcore & Hline & Hcopy).
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _).
pose proof HP1 as (Hroute & Hnc). unfold s28_P0 in Hroute.
destruct (Verbs.toks (e_D e)) as [|v args] eqn:Et; [contradiction|].
cbn [hd] in Hnc.
assert (Hnt : vr_ntok (e_D e) = Z.of_nat (length (v :: args))) by (unfold vr_ntok; rewrite Et; reflexivity).
assert (Hnt64 : vr_ntok (e_D e) <= 64) by (unfold vr_ntok; pose proof (s28_toks_le (e_D e)); lia).
assert (Hb : s28_b Verbs.Lit.fmt_disconnect (e_D e) = if Verbs.verb_is_m v Verbs.Lit.fmt_disconnect then 1 else 0)
  by (unfold s28_b; rewrite Et; reflexivity).
assert (Hb01 : 0 <= s28_b Verbs.Lit.fmt_disconnect (e_D e) <= 1)
  by (rewrite Hb; destruct (Verbs.verb_is_m v Verbs.Lit.fmt_disconnect); lia).
assert (R10 := vr_rv_get _ _ 10 _ Hrv ltac:(unfold vr_base, s28_rlb; cbn [app In]; tauto)).
assert (R21 := vr_rv_get _ _ 21 _ Hrv ltac:(unfold vr_base, s28_rlb, s28_rl0; cbn [app In]; tauto)).
pose proof (q_seed0 W regsc memc S28_D) as HS.
remember (Eimg (Ereg regsc [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply q_env_agree).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e))) by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 (s28_b Verbs.Lit.fmt_disconnect (e_D e)))
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), R10; reflexivity).
assert (Hkeep : forall pc ms mdx, (forall r, In r [2; 3; 4; 8; 9; 21; 25; 26] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) ->
  q_rdeq (rdW W memc) (rdW W (ms_mem ms)) ->
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
    lyc Sc W (ms_mem ms) mdx k ->
  forall P, P -> s28_at pc (s28_rl0 e) P e W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (ms_mem ms) (seg_rom SEGS)) mdx)).
{ intros pc ms mdx KR Eq HJx P HP.
  destruct (s28_kept e pos F q c tp lyc Sc W regsc memc mdc k nm _ (s28_rl0 e tp) (ms_regs ms) (ms_mem ms) mdx
    Hcore Hline Hcopy HJx Eq (s28_rl0_sub e tp _) KR (s28_rl0_regs e tp)) as (Hc2 & Hl2 & Hcp2).
  exists pos, F, q, c, tp, lyc, Sc, (ms_regs ms), (ms_mem ms), mdx, k, nm.
  split; [reflexivity|]. split; [exact HP|]. split; [exact Hc2|]. split; [exact Hl2 | exact Hcp2]. }
(* 0x8d8f4: li a1,3 *)
paj_run_sh RUNP HS HJ.
{ awr_ok_tac. }
match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
  set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
clearbody mdv.
cbn [ms_mem mkst] in HFr.
pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq1. clear HF HFr HG.
(* 0x8d8f8: bne s5,a1,0x8d93c *)
psrr_branch_pi RUNP BR HS.
- (* not three words: broadcast *)
  rewrite branch_ne_U, (U_atom E 21 _ E21) in Hc by lia.
  change (U E (SLit 3)) with 3 in Hc. rewrite Hnt in Hc.
  assert (Hl2 : length args <> 2%nat) by (intros Hl; cbn [length] in Hc; rewrite Hl in Hc; cbn in Hc; discriminate Hc).
  clear Hc.
  paj_run_to_sh RUNTO HS HJ S28_G.
  { awr_ok_tac. }
  match goal with |- context [with_vm_backing (m_vm_lazy mdv) ?mt mdv] =>
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mt mdv) in * end.
  clearbody mdv2.
  pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq2. clear HF HFr HG.
  pose proof (fun x => eq_trans (Eq2 x) (Eq1 x)) as Eq.
  pose proof (q_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 21; 25; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pmkst HS. apply SRr_ret. right.
  apply (Hkeep S28_G _ mdv2 KR Eq HJ). unfold s28_Pbroad. rewrite Et. cbv beta iota.
  rewrite Hroute. exact (s28_rbroad_len v args Hl2).
- (* three words: 0x8d8fc beqz a0,0x8d93c *)
  rewrite branch_ne_U, (U_atom E 21 _ E21) in Hc by lia.
  change (U E (SLit 3)) with 3 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rewrite Hnt in Hc.
  assert (Ha3 : exists a b, args = [a; b]).
  { destruct args as [|a [|b [|d r]]]; cbn in Hc; try lia. exists a, b. reflexivity. }
  destruct Ha3 as (a & b & ->). clear Hc.
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  match goal with |- context [with_vm_backing (m_vm_lazy mdv) ?mt mdv] =>
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mt mdv) in * end.
  clearbody mdv2.
  cbn [ms_mem mkst] in HFr.
  pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq2. clear HF HFr HG.
  pose proof (fun x => eq_trans (Eq2 x) (Eq1 x)) as Eq12.
  psrr_branch_pi RUNP BR HS.
  + (* not "disconnect": broadcast *)
    rewrite branch_eq_U, (U_atom E 10 _ E10) in Hc by lia.
    change (U E (SLit 0)) with 0 in Hc. apply Z.eqb_eq in Hc. rewrite Hb in Hc.
    assert (Hd0 : Verbs.verb_is_m v Verbs.Lit.fmt_disconnect = false)
      by (destruct (Verbs.verb_is_m v Verbs.Lit.fmt_disconnect); [discriminate Hc | reflexivity]).
    clear Hc.
    paj_run_to_sh RUNTO HS HJ S28_G.
    { awr_ok_tac. }
    match goal with |- context [with_vm_backing (m_vm_lazy mdv2) ?mt mdv2] =>
      set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mt mdv2) in * end.
    clearbody mdv3.
    pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq3. clear HF HFr HG.
    pose proof (fun x => eq_trans (Eq3 x) (Eq12 x)) as Eq.
    pose proof (q_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 21; 25; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. apply SRr_ret. right.
    apply (Hkeep S28_G _ mdv3 KR Eq HJ). unfold s28_Pbroad. rewrite Et. cbv beta iota.
    rewrite Hroute. exact (s28_rbroad_no v [a; b] Hnc Hd0).
  + (* "disconnect" with two arguments: connect *)
    rewrite branch_eq_U, (U_atom E 10 _ E10) in Hc by lia.
    change (U E (SLit 0)) with 0 in Hc. rewrite Hb in Hc.
    assert (Hd1 : Verbs.verb_is_m v Verbs.Lit.fmt_disconnect = true)
      by (destruct (Verbs.verb_is_m v Verbs.Lit.fmt_disconnect); [reflexivity | discriminate Hc]).
    clear Hc.
    paj_run_to_sh RUNTO HS HJ S28_E.
    { awr_ok_tac. }
    match goal with |- context [with_vm_backing (m_vm_lazy mdv2) ?mt mdv2] =>
      set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mt mdv2) in * end.
    clearbody mdv3.
    pose proof (q_rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq3. clear HF HFr HG.
    pose proof (fun x => eq_trans (Eq3 x) (Eq12 x)) as Eq.
    pose proof (q_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 21; 25; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. apply SRr_ret. left.
    apply (Hkeep S28_E _ mdv3 KR Eq HJ). unfold s28_Pconn. rewrite Et. cbv beta iota.
    rewrite Hroute. exact (s28_rdisc v a b Hd1).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The meter of each recorder call of the segment, one lemma per call shape: the call's account as a mallocs of at
   most VERBS_RECEIVE_REQ bytes and b frees within its events, then q_meter (the interface's vri_meter_ok /
   vri_meter_step) gives the callee's mo_ok premise and the boundary's vr_meter after its mo_le *)
Lemma s28_meter_conn : forall e Sc k nm v line a b t,
vr_ent B MT e -> vr_meter MT e Sc k nm -> r_calls (e_R e) = [] ->
Z.of_nat (length v) <= 8192 -> Z.of_nat (length line) <= 8192 -> Z.of_nat (length a) <= 8192 ->
Z.of_nat (length b) <= 8192 -> (length t <= 28)%nat ->
k + EV_SUP_CONNECT (e_R e) <= ev_vr (e_R e) (e_D e) ->
mo_ok MT Sc (XM_SUP_CONNECT MT (e_R e) (Some v) line (Some a) (Some b) t) /\
(forall S2, mo_le MT Sc S2 (XM_SUP_CONNECT MT (e_R e) (Some v) line (Some a) (Some b) t) ->
  vr_meter MT e S2 (k + EV_SUP_CONNECT (e_R e)) (nm + 6)).
Proof.
intros e Sc k nm v line a b t Hent Hm Hc Hv Hl Ha Hb Ht Hk.
assert (HEV : EV_SUP_CONNECT (e_R e) = 7)
  by (unfold EV_SUP_CONNECT, EV_RECORD, EV_ARG_S, EV_ARG_LINE, EV_REC_CANONICAL, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC;
      rewrite (q_spill0 _ Hc); reflexivity).
apply (q_meter B MT e Sc k nm _ 6 1 (EV_SUP_CONNECT (e_R e)) MTL Hent Hm); [| lia | lia | exact Hk].
unfold XM_SUP_CONNECT, XM_RECORD, XM_ARG_S, XM_ARG_LINE, XM_REC_CANONICAL, XM_ANSWER, XM_HAND_BACK, sarg.
unfold XM_XMALLOC, LIVE_XMALLOC. cbv beta iota. rewrite (q_spill0 _ Hc). rewrite !Z.max_l by lia.
pose proof (q_mall MT (Z.of_nat (length v) + 1) MTL ltac:(unfold VERBS_RECEIVE_REQ; lia)).
pose proof (q_mall MT (Z.of_nat (length line) + 1) MTL ltac:(unfold VERBS_RECEIVE_REQ; lia)).
pose proof (q_mall MT (Z.of_nat (length a) + 1) MTL ltac:(unfold VERBS_RECEIVE_REQ; lia)).
pose proof (q_mall MT (Z.of_nat (length b) + 1) MTL ltac:(unfold VERBS_RECEIVE_REQ; lia)).
pose proof (q_mall MT (Z.of_nat (length t) + 1) MTL ltac:(unfold VERBS_RECEIVE_REQ; lia)).
lia.
Qed.

Lemma s28_meter_bc : forall e Sc k nm line t,
vr_ent B MT e -> vr_meter MT e Sc k nm -> r_calls (e_R e) = [] ->
Z.of_nat (length line) <= 8192 -> (length t <= 28)%nat ->
k + EV_SUP_BROADCAST (e_R e) <= ev_vr (e_R e) (e_D e) ->
mo_ok MT Sc (XM_SUP_BROADCAST MT (e_R e) line t) /\
(forall S2, mo_le MT Sc S2 (XM_SUP_BROADCAST MT (e_R e) line t) ->
  vr_meter MT e S2 (k + EV_SUP_BROADCAST (e_R e)) (nm + 3)).
Proof.
intros e Sc k nm line t Hent Hm Hc Hl Ht Hk.
assert (HEV : EV_SUP_BROADCAST (e_R e) = 4)
  by (unfold EV_SUP_BROADCAST, EV_RECORD, EV_ARG_LINE, EV_REC_CANONICAL, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC;
      rewrite (q_spill0 _ Hc); reflexivity).
apply (q_meter B MT e Sc k nm _ 3 1 (EV_SUP_BROADCAST (e_R e)) MTL Hent Hm); [| lia | lia | exact Hk].
unfold XM_SUP_BROADCAST, XM_RECORD, XM_ARG_LINE, XM_REC_CANONICAL, XM_ANSWER, XM_HAND_BACK.
unfold XM_XMALLOC, LIVE_XMALLOC. cbv beta iota. rewrite (q_spill0 _ Hc). rewrite !Z.max_l by lia.
pose proof (q_mall MT (Z.of_nat (length line) + 1) MTL ltac:(unfold VERBS_RECEIVE_REQ; lia)).
pose proof (q_mall MT (Z.of_nat (length t) + 1) MTL ltac:(unfold VERBS_RECEIVE_REQ; lia)).
lia.
Qed.

(* B's sup_connect and sup_broadcast state the recorder's new blocks and the text's freshness in the
   contrapositive form; s28_post_new asks the A form *)
Lemma s28_post_conv : forall (bl O O' : list (Z * Z)) qt n,
(forall pn, In pn O' -> In pn bl -> In pn O) -> (In (qt, n) bl -> In (qt, n) O) ->
(forall pn, In pn O' -> In pn O \/ ~ In pn bl) /\ (forall pn, In pn bl -> ~ In pn O -> pn <> (qt, n)).
Proof.
intros bl O O' qt n H1 H2. split.
- intros pn Hpn. destruct (in_dec pn_eq_dec pn bl) as [Hi | Hn]; [left; exact (H1 pn Hpn Hi) | right; exact Hn].
- intros pn Hin HnO ->. exact (HnO (H2 Hin)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Leg CN: 0x8d900, the reloads and the two UBSan checks, sup_connect(tok[0], line, tok[1], tok[2]) and the jump
   to JB *)
Lemma s28_CN : forall e W cf, vr_ent B MT e -> s28_at S28_E (s28_rl0 e) (s28_Pconn e) e W cf ->
SRr SEGS W cf (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\ vr_athd (fx := fq) B MT 0x8d4cc e W' cf').
Proof.
intros e W cf Hent HA.
destruct HA as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & HPc & Hcore & Hline & Hcopy).
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & _ & Hcalls & _ & _ & _ & _ & _
  & _ & _ & _ & HROIN & VOBJS & _ & _ & _ & Hfr4 & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (s28_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
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
unfold s28_Pconn in HPc.
destruct (Verbs.toks (e_D e)) as [|v [|a [|b [|d r]]]] eqn:Et; try contradiction.
pose proof Hcopy as (_ & (_ & HlenP & _)).
destruct tp as [|p0 [|p1 [|p2 [|p3 tps]]]]; rewrite Et in HlenP; try discriminate HlenP.
assert (Hst : vr_st (e_D e) = Verbs.SCall (Verbs.sup_connect v (Verbs.line (e_D e)) a b))
  by exact (vr_st_conn (e_D e) v a b Et HPc).
assert (Hk1 : vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_CONNECT (e_R e)) by exact (vr_k1_conn (e_R e) (e_D e) v a b Et HPc).
set (t := snd (sup_connect_m (e_R e) (Some v) (Verbs.line (e_D e)) (Some a) (Some b))).
assert (HX : vr_x (e_R e) (e_D e) = t) by (rewrite (vr_x_call _ _ _ Hst); reflexivity).
assert (HR1 : vr_R1 (e_R e) (e_D e) = fst (sup_connect_m (e_R e) (Some v) (Verbs.line (e_D e)) (Some a) (Some b)))
  by (rewrite (vr_R1_call _ _ _ Hst); reflexivity).
assert (Hqv : vr_qv e = e_q0 e) by (unfold vr_qv; rewrite (vr_quit_call _ _ _ Hst); reflexivity).
assert (HEV : EV_SUP_CONNECT (e_R e) = 7)
  by (unfold EV_SUP_CONNECT, EV_RECORD, EV_ARG_S, EV_ARG_LINE, EV_REC_CANONICAL, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC;
      rewrite (q_spill0 _ Hcalls); reflexivity).
assert (Ht28 : (length t <= 28)%nat).
{ unfold t, sup_connect_m. apply vr_text_len. exact (q_code_range B _ _ _ _ _ Hrec). }
assert (Hev2 : 2 + EV_SUP_CONNECT (e_R e) <= ev_vr (e_R e) (e_D e))
  by (pose proof (q_k1_ev (e_R e) (e_D e)); pose proof s28_ev_reply; lia).
assert (R9 : getr regsc (Z_to_bv 5 9) = w64 (vr_s1 e)) by (apply (vr_rv_get _ _ 9 _ Hrv); unfold vr_base; cbn [app In]; tauto).
assert (R26 : getr regsc (Z_to_bv 5 26) = w64 p0)
  by (apply (vr_rv_get _ _ 26 _ Hrv); unfold vr_base, s28_rl0; cbn [app In hd]; tauto).
assert (Hsp : forall o val, In (o, val) (q_sl F q) -> aval_mem (rdW W memc) (vr_s1 e + o) 8 val).
{ intros o val Hi. unfold vr_spill in Hspill. rewrite Forall_forall in Hspill.
  exact (Hspill (o, val) (q_sl_of_sl3 F q c o val Hi)). }
destruct (q_tok_arg B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c [p0; p1; p2] 1%nat p1 a Hcore
  (or_intror (or_introl eq_refl)) Hcopy eq_refl ltac:(rewrite Et; reflexivity)) as (_ & Hp1m & Hp14 & Hp1c & _ & _).
destruct (q_tok_arg B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c [p0; p1; p2] 2%nat p2 b Hcore
  (or_intror (or_introl eq_refl)) Hcopy eq_refl ltac:(rewrite Et; reflexivity)) as (_ & Hp2m & Hp24 & Hp2c & _ & _).
pose proof (q_seedT2 W regsc memc S28_E (vr_s1 e) q F p1 p2 R9 ltac:(lia) ltac:(lia) ltac:(lia) BF1 BF2 ltac:(lia)
  ltac:(lia) Hsp
  ltac:(replace (F + 40) with (F + 32 + 8 * Z.of_nat 1) by lia; exact Hp1m)
  ltac:(replace (F + 48) with (F + 32 + 8 * Z.of_nat 2) by lia; exact Hp2m)) as HS.
remember (Eimg (Ereg regsc (q_extra q F p1 p2))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc (q_extra q F p1 p2)) E) by (subst E; apply q_env_agree).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (q_extra q F p1 p2) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
clear HE.
assert (X32 : ew E 32 = Z_to_bv 64 q) by exact (EX 0%nat ltac:(lia)).
assert (X33 : ew E 33 = Z_to_bv 64 F) by exact (EX 1%nat ltac:(lia)).
assert (X34 : ew E 34 = Z_to_bv 64 p1) by exact (EX 2%nat ltac:(lia)).
assert (X35 : ew E 35 = Z_to_bv 64 p2) by exact (EX 3%nat ltac:(lia)).
assert (X36 : ew E 36 = Z_to_bv 64 (shadow_addr F)) by exact (EX 4%nat ltac:(lia)).
(* 0x8d900: li a0,-9; ld s6,24(s1); ld s11,32(s1); ld s2,56(s1); ld s3,40(s1); up to the check 0x8d914 *)
paj_run_sh RUNP HS HJ.
{ q_awr. }
match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
  set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
clearbody mdv.
cbn [ms_mem mkst] in HFr.
pose proof (q_rdeq_of_frame _ _ _ _ _ HFr q_ro_rt2) as Eq0. clear HF HFr HG.
(* 0x8d914: bltu a0,s3,0x8d938 (UBSan: tok + 8 wraps) *)
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
  rewrite (U_atom_off E 33 F 32 X33 ltac:(lia) ltac:(lia)) in Hc.
  rewrite U_lit in Hc by lia. lia. }
clear Hc.
(* 0x8d918: li a0,-17; up to the check 0x8d91c *)
paj_run_sh RUNP HS HJ.
{ q_awr. }
match goal with |- context [with_vm_backing (m_vm_lazy mdv) ?mt mdv] =>
  set (mdv1 := with_vm_backing (m_vm_lazy mdv) mt mdv) in * end.
clearbody mdv1.
cbn [ms_mem mkst] in HFr.
pose proof (q_rdeq_of_frame _ _ _ _ _ HFr q_ro_rt2) as Eq0'. clear HF HFr HG.
(* 0x8d91c: bltu a0,s3,0x8d938 (UBSan: tok + 16 wraps) *)
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
  rewrite (U_atom_off E 33 F 32 X33 ltac:(lia) ltac:(lia)) in Hc.
  rewrite U_lit in Hc by lia. lia. }
clear Hc.
(* 0x8d920: ld a2,8(s3); ld a3,16(s3); mv a0,s10; mv a1,s2; jal sup_connect *)
paj_run_shc RUNP RUNC HS HJ.
{ q_awr. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into msC end.
match goal with |- context [with_vm_backing (m_vm_lazy mdv1) ?mt mdv1] =>
  set (mdv2 := with_vm_backing (m_vm_lazy mdv1) mt mdv1) in * end.
clearbody mdv2.
pose proof (q_rdeq_of_frame _ _ _ _ _ HFr q_ro_rt2) as Eq1'. clear HF HFr HG.
pose proof (fun x => eq_trans (Eq1' x) (eq_trans (Eq0' x) (Eq0 x))) as Eq1.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (18%bv : bv 5) Q18.
prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (27%bv : bv 5) Q27.
rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), R26 in Q10. rewrite X32 in Q11, Q18. rewrite X34 in Q12.
rewrite X35 in Q13. rewrite X33, unsigned_lit_small in Q19 by lia. rewrite X33 in Q22.
rewrite X36, unsigned_lit_small in Q27 by lia.
pose proof (q_kept_regs E _ _ regsc (q_extra q F p1 p2) [2; 3; 4; 8; 9; 21; 25; 26] HS HAE
  ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
rewrite (SIGP CS_sup_connect) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_sup_connect) with AF_sup_connect.
set (rlC := [(1, BASE + S28_F); (10, p0); (11, q); (12, p1); (13, p2); (18, q); (19, F + 32);
  (21, vr_ntok (e_D e)); (22, F); (25, vr_ntok (e_D e)); (26, p0); (27, shadow_addr F + 4)]).
assert (HcoreC : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rlC
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs msC) (ms_mem msC) mdv2).
{ apply (q_core_same B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc W (ms_regs msC) (ms_mem msC) mdv2
    Hcore HJ Eq1).
  apply (q_rv_keep B e (ms_regs msC) regsc _ _ Hrv).
  - intros r0 Hr. apply KR. cbn in Hr |- *. tauto.
  - intros r0 val Hi. unfold rlC in Hi. cbn in Hi.
    destruct Hi as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]]]]]]; injection E1 as <- <-.
    + right. exact Q1.
    + right. exact Q10.
    + right. exact Q11.
    + right. exact Q12.
    + right. exact Q13.
    + right. exact Q18.
    + right. exact Q19.
    + left. split; [unfold s28_rl0; cbn; tauto | apply KR; cbn; tauto].
    + right. exact Q22.
    + left. split; [unfold s28_rl0; cbn; tauto | apply KR; cbn; tauto].
    + left. split; [unfold s28_rl0; cbn; tauto | apply KR; cbn; tauto].
    + right. exact Q27. }
pose proof (q_line_same B e q W memc W (ms_mem msC) Eq1 Hline) as HlineC.
pose proof (q_copy_same B e F c [p0; p1; p2] W memc W (ms_mem msC) Eq1 Hcopy) as HcopyC.
pose proof HcoreC as (HJC & _ & HmeterC & HnmC & _ & HrvC & _ & _ & HenvC & HrecC & _).
pose proof HenvC as (HROC & _ & HROkC & _).
pose proof (proj1 HJC) as HARC.
destruct (q_tok_arg B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c [p0; p1; p2] 0%nat p0 v HcoreC
  (or_intror (or_introl eq_refl)) HcopyC eq_refl ltac:(rewrite Et; reflexivity))
  as ((Hib0 & Hap0 & Hstr0 & Hlm0) & _ & Hp04 & Hp0c & Hp0cc & Hcp0).
destruct (q_tok_arg B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c [p0; p1; p2] 1%nat p1 a HcoreC
  (or_intror (or_introl eq_refl)) HcopyC eq_refl ltac:(rewrite Et; reflexivity))
  as (Harg1 & _ & _ & _ & Hp1cc & Hcp1).
destruct (q_tok_arg B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c [p0; p1; p2] 2%nat p2 b HcoreC
  (or_intror (or_introl eq_refl)) HcopyC eq_refl ltac:(rewrite Et; reflexivity))
  as (Harg2 & _ & _ & _ & Hp2cc & Hcp2).
assert (R1C : getr (ms_regs msC) 1 = Z_to_bv 64 (BASE + S28_F)) by exact Q1.
destruct (s28_meter_conn e Sc k nm v (Verbs.line (e_D e)) a b t Hent HmeterC Hcalls ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) Ht28 ltac:(lia)) as [HmokC Hmeter3].
assert (HSC : SUP_CONNECT_STK = ltac:(let x := eval vm_compute in SUP_CONNECT_STK in exact x)) by reflexivity.
eapply SRr_bind.
{ eapply (q_rcallF B MT HB PROGU e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs msC) (ms_mem msC) mdv2 AF_sup_connect
    SUP_CONNECT_STK _ (EV_SUP_CONNECT (e_R e)) S28_F _ Hent HcoreC).
  - exact R1C.
  - unfold S28_F; lia.
  - reflexivity.
  - lia.
  - lia.
  - exact (s28_FP_conn (e_O e)).
  - intros ch HPRE2.
    apply (TSUP_CONNECT fx lyc Sc W (ms_regs msC) (ms_mem msC) mdv2 ch p0 q p1 p2 (Some v) (Verbs.line (e_D e)) a b
      (e_R e) (e_O e) HPRE2 (q_ent_frm0 B MT e Hent)).
    + pose proof HJC as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. cbn [app length]. lia.
    + exact HROC.
    + exact HROkC.
    + exact (vr_rv_get _ _ 10 _ HrvC ltac:(unfold rlC, vr_base; cbn [app In]; tauto)).
    + lia.
    + exact (vr_rv_get _ _ 11 _ HrvC ltac:(unfold rlC, vr_base; cbn [app In]; tauto)).
    + lia.
    + exact (vr_rv_get _ _ 12 _ HrvC ltac:(unfold rlC, vr_base; cbn [app In]; tauto)).
    + lia.
    + exact (vr_rv_get _ _ 13 _ HrvC ltac:(unfold rlC, vr_base; cbn [app In]; tauto)).
    + lia.
    + cbn [astr_argA]. split; [lia|]. split; [exact Hstr0|]. split; [exact Hlm0|]. left. split; [exact Hib0 | exact Hap0].
    + intros x Hx. injection Hx as <-.
      apply (BLKT lyc Sc W (ms_mem msC) mdv2 c (Z.of_nat (length (Verbs.line (e_D e))) + 1)); [exact HARC | exact Hcb | lia].
    + exact (q_line_arg B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs msC) (ms_mem msC) mdv2 q Hent HcoreC
        (or_introl eq_refl) HlineC).
    + exact Harg1.
    + exact Harg2.
    + exact HrecC.
    + exact (q_nev B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs msC) (ms_mem msC) mdv2 _ Hent HcoreC Hev2).
    + apply (q_live B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs msC) (ms_mem msC) mdv2 _ 0 Hent HcoreC
        ltac:(rewrite Hcalls; cbn; lia)).
      fold t. unfold bsum, vr_lb, vr_cb. cbn [fold_right fst snd].
      unfold LIVE_SUP_CONNECT, LIVE_ARG_S, LIVE_ARG_LINE, LIVE_REC_CANONICAL, LIVE_ANSWER, LIVE_HAND_BACK, sarg.
      unfold LIVE_XMALLOC. cbv beta iota. rewrite !Z.max_l by lia.
      unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ, LMAX. lia.
    + exact HmokC. }
cbv beta. intros W3 c3 _ (fx' & ly3 & S3 & regs3 & mem3 & md3 & Hfx & -> & HJ3 & HJc3 & HP3 & HK3).
destruct HK3 as (R' & O' & qt & Hm & Ha0 & Hqt & Hrec' & HO'n & HB2 & HB1 & Hqin & Hqfr & HqO' & Hstr & _ & Hmle).
destruct (s28_post_conv (ablocks B lyc Sc) (e_O e) O' qt (Z.of_nat (length t) + 1) HO'n Hqfr) as [HO'1 Hqne].
assert (Hrv3 : vr_rv regs3 (vr_base B e ++ vr_rl_hd e F q c 0x8d4cc qt)).
{ replace (vr_rl_hd e F q c 0x8d4cc qt) with
    [(10, qt); (19, F + 32); (18, q); (22, F); (27, shadow_addr F + 4)] by reflexivity.
  apply (q_rv_keep B e regs3 (ms_regs msC) _ _ HrvC).
  - intros r0 Hr. apply HP3. unfold acallee_saved. cbn in Hr. lia.
  - intros r0 val Hi. cbn in Hi. destruct Hi as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-.
    + right. exact Ha0.
    + left. split; [unfold rlC; cbn; tauto | apply HP3; unfold acallee_saved; lia].
    + left. split; [unfold rlC; cbn; tauto | apply HP3; unfold acallee_saved; lia].
    + left. split; [unfold rlC; cbn; tauto | apply HP3; unfold acallee_saved; lia].
    + left. split; [unfold rlC; cbn; tauto | apply HP3; unfold acallee_saved; lia]. }
destruct (s28_post_new B MT ROA RRO RPG RECC PROGU e pos F q c [p0; p1; p2] rlC (vr_rl_hd e F q c 0x8d4cc qt)
  [vr_lb e q; vr_cb e c] (e_R e) (e_O e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs msC) (ms_mem msC) mdv2 SUP_CONNECT_STK _
  (EV_SUP_CONNECT (e_R e)) ly3 S3 W3 mem3 md3 regs3 R' O' qt (Z.of_nat (length t) + 1) (k + EV_SUP_CONNECT (e_R e))
  (vr_k1 (e_R e) (e_D e)) (nm + 6) VR_NM_HD Hent HcoreC HlineC HcopyC (or_introl eq_refl) (or_intror (or_introl eq_refl))
  HJc3 HJ3 (s28_FP_conn (e_O e)) ltac:(rewrite Hk1; lia) (Hmeter3 S3 Hmle) ltac:(unfold VR_NM_HD, VR_NM_PRE in *; lia)
  Hrec' HO'1 HB1 HB2 Hqin Hqne HqO' Hrv3) as (O1 & _ & Hc3 & Hl3 & Hcp3).
assert (HR1' : vr_R1 (e_R e) (e_D e) = R') by (rewrite HR1, Hm; reflexivity).
(* 0x8d934: j 0x8d4cc, at the FP state sup_connect returned *)
apply (q_jmp (fx := fx') B S28_F S28_JB ltac:(unfold S28_F; lia) ltac:(vm_compute; reflexivity) W3 regs3 mem3 md3
  _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3).
intros regs5 mem5 md5 Er Em HJ5.
exists fx'. split; [exact Hfx|].
unfold vr_athd, vr_hd.
exists qt, O1, pos, F, q, c, [p0; p1; p2], ly3, S3, regs5, mem5, md5, (k + EV_SUP_CONNECT (e_R e)), (nm + 6).
split; [apply s28_cfg; unfold S28_JB, AF_verbs_receive; lia|].
split; [unfold vr_hd_ntok; rewrite Et; simpl; lia|].
split; [lia|].
rewrite HX, HR1', Hqv.
split; [exact (q_astr_eq _ _ _ _ Em Hstr)|].
split.
{ apply (q_core_same B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 regs3 mem3 md3 W3 regs5 mem5 md5 Hc3 HJ5 Em).
  apply q_rv_intro. intros r0 val Hi. rewrite Er. exact (vr_rv_get _ _ r0 val (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hc3)))))) Hi). }
split; [exact (q_line_same B e q W3 mem3 W3 mem5 Em Hl3) | exact (q_copy_same B e F c [p0; p1; p2] W3 mem3 W3 mem5 Em Hcp3)].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Leg BC: 0x8d93c, sup_broadcast(line), then s28_BC2 (sup_host_setting(line, &tok[0], ntok) and s28_tail) *)
Lemma s28_BC : forall e W cf, vr_ent B MT e -> s28_at S28_G (s28_rl0 e) (s28_Pbroad e) e W cf ->
SRr SEGS W cf (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\ vr_athd (fx := fq) B MT 0x8d6a4 e W' cf').
Proof.
intros e W cf Hent HA.
destruct HA as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & HPb & Hcore & Hline & Hcopy).
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & _ & Hcalls & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & Hfr4 & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (s28_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
pose proof Hcore as (HJ & Hkk & Hmeter & Hnm & Hframe & Hrv & Hsaved & Hspill & Henv & Hrec & HdO & Hperm & Hquit).
pose proof (proj1 HJ) as HAR.
pose proof (s28_frames_own B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hin4.
pose proof Hframe as (HFa & _ & _).
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
unfold s28_Pbroad in HPb.
destruct (Verbs.toks (e_D e)) as [|v args] eqn:Et; [contradiction|].
pose proof Hcopy as (_ & (HF8' & HlenP & _)).
destruct tp as [|p0 tps]; [rewrite Et in HlenP; discriminate HlenP|].
set (tp := p0 :: tps) in *.
set (R1 := fst (sup_broadcast_m (e_R e) (Verbs.line (e_D e)))).
set (t1 := snd (sup_broadcast_m (e_R e) (Verbs.line (e_D e)))).
assert (Hk1 : vr_k1 (e_R e) (e_D e) = 2 + (EV_SUP_BROADCAST (e_R e) + EV_SUP_HOST_SETTING R1))
  by exact (vr_k1_broad (e_R e) (e_D e) v args Et HPb).
assert (HEVb : EV_SUP_BROADCAST (e_R e) = 4)
  by (unfold EV_SUP_BROADCAST, EV_RECORD, EV_ARG_LINE, EV_REC_CANONICAL, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC;
      rewrite (q_spill0 _ Hcalls); reflexivity).
assert (Hsp1 : rec_spill_frees R1 = 0) by exact (s28_bcast_spill (e_R e) (Verbs.line (e_D e)) Hcalls).
assert (HEVh : EV_SUP_HOST_SETTING R1 = 5)
  by (unfold EV_SUP_HOST_SETTING, EV_RECORD, EV_ARG_LINE, EV_REC_CANONICAL, EV_ARG_S, EV_XMALLOC; rewrite Hsp1;
      reflexivity).
assert (Ht28 : (length t1 <= 28)%nat).
{ unfold t1, sup_broadcast_m. apply vr_text_len. exact (q_code_range B _ _ _ _ _ Hrec). }
assert (Hev2 : 2 + (EV_SUP_BROADCAST (e_R e) + EV_SUP_HOST_SETTING R1) <= ev_vr (e_R e) (e_D e))
  by (pose proof (q_k1_ev (e_R e) (e_D e)); pose proof s28_ev_reply; lia).
assert (R9 : getr regsc (Z_to_bv 5 9) = w64 (vr_s1 e)) by (apply (vr_rv_get _ _ 9 _ Hrv); unfold vr_base; cbn [app In]; tauto).
assert (Hsp : forall o val, In (o, val) (q_sl F q) -> aval_mem (rdW W memc) (vr_s1 e + o) 8 val).
{ intros o val Hi. unfold vr_spill in Hspill. rewrite Forall_forall in Hspill.
  exact (Hspill (o, val) (q_sl_of_sl3 F q c o val Hi)). }
pose proof (q_seedS W regsc memc S28_G (vr_s1 e) q F 0 0 R9 ltac:(lia) ltac:(lia) ltac:(lia) BF1 BF2 ltac:(lia)
  ltac:(lia) Hsp) as HS.
remember (Eimg (Ereg regsc (q_extra q F 0 0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc (q_extra q F 0 0)) E) by (subst E; apply q_env_agree).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (q_extra q F 0 0) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
clear HE.
assert (X32 : ew E 32 = Z_to_bv 64 q) by exact (EX 0%nat ltac:(lia)).
(* 0x8d93c: ld s2,56(s1); mv a0,s2; jal sup_broadcast *)
paj_run_shc RUNP RUNC HS HJ.
{ q_awr. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into msC end.
match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
  set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
clearbody mdv.
pose proof (q_rdeq_of_frame _ _ _ _ _ HFr q_ro_rsp) as Eq1. clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18.
rewrite X32 in Q10, Q18.
pose proof (q_kept_regs E _ _ regsc (q_extra q F 0 0) [2; 3; 4; 8; 9; 21; 25; 26] HS HAE
  ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
rewrite (SIGP CS_sup_broadcast) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_sup_broadcast) with AF_sup_broadcast.
set (rlC := [(1, BASE + S28_H); (10, q); (18, q); (21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, p0)]).
assert (HcoreC : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rlC
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs msC) (ms_mem msC) mdv).
{ apply (q_core_same B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc W (ms_regs msC) (ms_mem msC) mdv
    Hcore HJ Eq1).
  apply (q_rv_keep B e (ms_regs msC) regsc _ _ Hrv).
  - intros r0 Hr. apply KR. cbn in Hr |- *. tauto.
  - intros r0 val Hi. unfold rlC in Hi. cbn in Hi.
    destruct Hi as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]; injection E1 as <- <-.
    + right. exact Q1.
    + right. exact Q10.
    + right. exact Q18.
    + left. split; [unfold s28_rl0; cbn; tauto | apply KR; cbn; tauto].
    + left. split; [unfold s28_rl0; cbn; tauto | apply KR; cbn; tauto].
    + left. split; [unfold s28_rl0, tp; cbn; tauto | apply KR; cbn; tauto]. }
pose proof (q_line_same B e q W memc W (ms_mem msC) Eq1 Hline) as HlineC.
pose proof (q_copy_same B e F c tp W memc W (ms_mem msC) Eq1 Hcopy) as HcopyC.
pose proof HcoreC as (HJC & _ & HmeterC & HnmC & _ & HrvC & _ & _ & HenvC & HrecC & _).
pose proof HenvC as (HROC & _ & HROkC & _).
assert (R1C : getr (ms_regs msC) 1 = Z_to_bv 64 (BASE + S28_H)) by exact Q1.
destruct (s28_meter_bc e Sc k nm (Verbs.line (e_D e)) t1 Hent HmeterC Hcalls ltac:(lia) Ht28 ltac:(lia))
  as [HmokC Hmeter3].
assert (HSB : SUP_BROADCAST_STK = ltac:(let x := eval vm_compute in SUP_BROADCAST_STK in exact x)) by reflexivity.
eapply SRr_bind.
{ eapply (q_rcallF B MT HB PROGU e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs msC) (ms_mem msC) mdv AF_sup_broadcast
    SUP_BROADCAST_STK _ (EV_SUP_BROADCAST (e_R e)) S28_H _ Hent HcoreC).
  - exact R1C.
  - unfold S28_H; lia.
  - reflexivity.
  - lia.
  - lia.
  - exact (s28_FP_conn (e_O e)).
  - intros ch HPRE2.
    apply (TSUP_BROADCAST fx lyc Sc W (ms_regs msC) (ms_mem msC) mdv ch q (Verbs.line (e_D e)) (e_R e) (e_O e)
      HPRE2 (q_ent_frm0 B MT e Hent)).
    + pose proof HJC as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. cbn [app length]. lia.
    + exact HROC.
    + exact HROkC.
    + exact (vr_rv_get _ _ 10 _ HrvC ltac:(unfold rlC, vr_base; cbn [app In]; tauto)).
    + lia.
    + exact (q_line_arg B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs msC) (ms_mem msC) mdv q Hent HcoreC
        (or_introl eq_refl) HlineC).
    + exact HrecC.
    + exact (q_nev B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs msC) (ms_mem msC) mdv
        (EV_SUP_BROADCAST (e_R e)) Hent HcoreC ltac:(lia)).
    + apply (q_live B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs msC) (ms_mem msC) mdv _ 0 Hent HcoreC
        ltac:(rewrite Hcalls; cbn; lia)).
      fold t1. unfold bsum, vr_lb, vr_cb. cbn [fold_right fst snd].
      unfold LIVE_SUP_BROADCAST, LIVE_ARG_LINE, LIVE_REC_CANONICAL, LIVE_ANSWER, LIVE_HAND_BACK.
      unfold LIVE_XMALLOC. cbv beta iota. rewrite !Z.max_l by lia.
      unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ, LMAX. lia.
    + exact HmokC. }
cbv beta. intros W3 c3 _ (fx' & ly3 & S3 & regs3 & mem3 & md3 & Hfx & -> & HJ3 & HJc3 & HP3 & HK3).
destruct HK3 as (R1' & O1' & q1 & Hm1 & Ha0 & Hq1 & Hrec1 & HO1n & HB2 & HB1 & Hqin & Hqfr & HqO & Hstr1 & _ & Hmle1).
destruct (s28_post_conv (ablocks B lyc Sc) (e_O e) O1' q1 (Z.of_nat (length t1) + 1) HO1n Hqfr) as [HO1 Hqne].
assert (ER1 : R1' = R1) by (unfold R1; rewrite Hm1; reflexivity).
subst R1'.
set (rlM := [(10, q1); (18, q); (21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, p0)]).
assert (Hrv3 : vr_rv regs3 (vr_base B e ++ rlM)).
{ apply (q_rv_keep B e regs3 (ms_regs msC) _ _ HrvC).
  - intros r0 Hr. apply HP3. unfold acallee_saved. cbn in Hr. lia.
  - intros r0 val Hi. unfold rlM in Hi. cbn in Hi. destruct Hi as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-.
    + right. exact Ha0.
    + left. split; [unfold rlC; cbn; tauto | apply HP3; unfold acallee_saved; lia].
    + left. split; [unfold rlC; cbn; tauto | apply HP3; unfold acallee_saved; lia].
    + left. split; [unfold rlC; cbn; tauto | apply HP3; unfold acallee_saved; lia].
    + left. split; [unfold rlC; cbn; tauto | apply HP3; unfold acallee_saved; lia]. }
destruct (s28_post_new B MT ROA RRO RPG RECC PROGU e pos F q c tp rlC rlM
  [vr_lb e q; vr_cb e c] (e_R e) (e_O e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs msC) (ms_mem msC) mdv SUP_BROADCAST_STK _
  (EV_SUP_BROADCAST (e_R e)) ly3 S3 W3 mem3 md3 regs3 R1 O1' q1 (Z.of_nat (length t1) + 1)
  (k + EV_SUP_BROADCAST (e_R e)) (2 + EV_SUP_BROADCAST (e_R e)) (nm + 3) 5 Hent HcoreC HlineC HcopyC
  (or_introl eq_refl) (or_intror (or_introl eq_refl))
  HJc3 HJ3 (s28_FP_conn (e_O e)) ltac:(lia) (Hmeter3 S3 Hmle1) ltac:(unfold VR_NM_PRE in *; lia)
  Hrec1 HO1 HB1 HB2 Hqin Hqne HqO Hrv3) as (O1 & _ & HcM & HlM & HcpM).
(* 0x8d948 ..: the rest of the leg at the FP state sup_broadcast returned (s28_BC2 at fx') *)
eapply SRr_mono.
{ exact (s28_BC2 (fx := fx') B MT (TSUP_HOST_SETTING fx') HB MTL SIGP ROA RRO RPG RECC PROGU e pos F q c p0 tps v args
    k nm q1 O1 ly3 S3 W3 regs3 mem3 md3 (q_ent_fxr B MT fx fx' e Hent Hfx)
    (fxrel_frm0 fx fx' (q_ent_frm0 B MT e Hent) Hfx) Et HPb Hkk Hnm HcM HlM HcpM Hstr1). }
cbv beta. intros W' cf' _ (fq & Hfq & HQ). exists fq. split; [exact (fxrel_trans fx fx' fq Hfx Hfq) | exact HQ].
Qed.

Lemma vr_s28 : vr_s28_stmt B MT.
Proof.
intros e W cf Hent Hin.
eapply SRr_bind; [exact (s28_V1 e W cf Hent Hin)|].
intros W1 cf1 _ H1. eapply SRr_bind; [exact (s28_D1 e W1 cf1 Hent H1)|].
intros W2 cf2 _ [H2 | [H2 | H2]].
- eapply SRr_bind; [exact (s28_V2 e W2 cf2 Hent H2)|].
  intros W3 cf3 _ H3. eapply SRr_bind; [exact (s28_D2 e W3 cf3 Hent H3)|].
  intros W4 cf4 _ [H4 | H4].
  + eapply SRr_mono; [exact (s28_CN e W4 cf4 Hent H4)|].
    intros W5 cf5 _ (fq & Hfq & H5). exists fq. split; [exact Hfq | left; exact H5].
  + eapply SRr_mono; [exact (s28_BC e W4 cf4 Hent H4)|].
    intros W5 cf5 _ (fq & Hfq & H5). exists fq. split; [exact Hfq | right; exact H5].
- eapply SRr_mono; [exact (s28_CN e W2 cf2 Hent H2)|].
  intros W5 cf5 _ (fq & Hfq & H5). exists fq. split; [exact Hfq | left; exact H5].
- eapply SRr_mono; [exact (s28_BC e W2 cf2 Hent H2)|].
  intros W5 cf5 _ (fq & Hfq & H5). exists fq. split; [exact Hfq | right; exact H5].
Qed.

End e.
End f2.
End d2.
