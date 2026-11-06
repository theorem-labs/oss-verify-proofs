(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S10 REMOVE (0x8d41c-0x8d44c, 0x8d548-0x8d54c, 15 instructions) of the
   walk of verbs_receive on the ASan+UBSan build of plugin-hostd/fuzz_command (image B, interface
   lib/B/Prog/verbs_receive_iface.v, vr_s10_stmt). The B twin of the A walk's lib/A/Prog/verbs_receive_s10.v
   (a working branch):
     0x8d41c li a0,2; 0x8d420 bne s5,a0,0x8d68c       not two words: the shared refusal stub 0x8d68c (vr_pr)
     0x8d424 li a0,-9; 0x8d428 ld s3,40(s1)           B reloads tok (the spill slot s1+40) into s3
     0x8d42c bltu a0,s3,0x8d938                       UBSan: tok + 8 wraps (verbs.c:156); refuted, tok = F + 32
     0x8d430 ld a0,8(s3); 0x8d434 jal wrapper_atoi    atoi(tok[1]) (a Theorem Labs lane's aatoi_realizes, PaArt.aj_art_at)
     0x8d438 li a1,-1; 0x8d43c beq a0,a1,0x8d548
     0x8d440 li a1,-8; 0x8d444 beq s3,a1,0x8d938      UBSan: tok + 8 null (verbs.c:156); refuted, tok = F + 32
     0x8d448 jal sup_remove; 0x8d44c j 0x8d4cc        sup_remove(id) (sup_remove_c.v)
     0x8d548 jal sup_remove_all; 0x8d54c j 0x8d4cc    id = -1: sup_remove_all (sup_remove_all_c.v)
     0x8d4cc                                          the join JB (vr_hd, the text in a0, s3 = tok)
   B-only code walked: 0x8d424-0x8d42c (the reload of tok from s1+40 and the UBSan check of tok + 8 for tok[1]) and
   0x8d440-0x8d444 (the UBSan check tok + 8 <> 0 before sup_remove); both trap branches to the unimp at 0x8d938 are
   refuted from F's bounds (F + 2048 <= 2 ^ 47, so tok = F + 32 is neither above 2 ^ 64 - 9 nor 2 ^ 64 - 8). The
   boundary facts cross the atoi wrapper by verbs_receive_s10_lib.v's vr_core_kx, the calls go through its generic
   arm vr_call_arm. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_remove_c sup_remove_all_c arg_s_c answer_c hand_back_c xmalloc_c record_c sup_resp_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_s10_lib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
Import ListNotations.
Import VRL10.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* beq a0,a1 after `li a1,-1`, with a0 the atoi wrapper's int *)
Lemma beq_m1 : forall E x z, ew E 10 = Z_to_bv 64 x -> -2 ^ 31 <= x < 2 ^ 31 -> U E (SLit z) = 2 ^ 64 - 1 ->
(U E (SOff 10 0) =? U E (SLit z)) = (x =? -1).
Proof.
intros E x z H Hx Hz. rewrite Hz, U_SOff, H, Z.add_0_r.
assert (Hu : zcanon (bv_unsigned (Z_to_bv 64 x)) = x mod 2 ^ 64).
{ unfold zcanon, M64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_mod. lia. }
rewrite Hu.
destruct (Z.eqb_spec x (-1)) as [->|Hn]; [reflexivity|].
apply Z.eqb_neq. intros Hc. pose proof (Z.div_mod x (2 ^ 64) ltac:(lia)) as D. rewrite Hc in D.
change (2 ^ 64) with 18446744073709551616 in *. lia.
Qed.

(* the footprint sup_remove and sup_remove_all state (sup_remove_c.v): bytes of g_rec, record.spill and O *)
Definition fp_rm (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
(A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the callee-saved registers at the two calls, as JB 0x8d4cc names them besides the text *)
Definition rl10 (e : vrE) (F q : Z) : list (Z * Z) :=
[(19, F + 32); (18, q); (22, F); (27, shadow_addr F + 4)].

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callees' contracts at every FP state (verbs_receive_c.v), the atoi entry (called before them, at the
   segment's own FP state) and the record facts of the brief *)
Hypothesis TSUP_REMOVE : forall fx0 : YK11.FPState, @tsup_remove_spec fx0 rc SK PI B MT.
Hypothesis TSUP_REMOVE_ALL : forall fx0 : YK11.FPState, @tsup_remove_all_spec fx0 rc SK PI B MT.
Hypothesis AATOI : forall fx0 : YK11.FPState,
  @RtNumber.aatoi_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis BLKT : vr_blktail B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let ART := aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL).

Lemma fp_rm_sub : forall O a, inFP (fp_rm O) a -> inFP (fp1 O) a.
Proof.
intros O a Ha. unfold fp_rm, fp1 in *.
apply inFP_cons in Ha as [Ha|Ha]; [apply inFP_cons; left; unfold OFF_NCALLS, REC_SIZE in *; lia|].
apply inFP_cons in Ha as [Ha|Ha]; [apply inFP_cons; left; unfold OFF_CALLS, OFF_ANSWER, REC_SIZE in *; lia|].
apply inFP_cons in Ha as [Ha|Ha]; [apply inFP_cons; left; unfold OFF_STATE, REC_SIZE in *; lia|].
apply inFP_cons; right. exact Ha.
Qed.

(* the jump from a call's return address (0x8d54c or 0x8d44c) to JB 0x8d4cc, at the FP state the call returns *)
Lemma s10_to_jb : forall (fx' : YK11.FPState) e pos F q c tp tq O1 W2 regs2 mem2 md2 ly2 S2 kk nm2 retk
  (Q : world SEGS -> config -> Prop),
(retk = 0x701c \/ retk = 0x6f1c) ->
vr_aft B MT e pos F q c tp (rl10 e F q) tq O1 ly2 S2 W2 regs2 mem2 md2 kk nm2 ->
length (Verbs.toks (e_D e)) = 2%nat ->
(forall W3 c3, vr_hd (fx := fx') B MT e 0x8d4cc W3 c3 -> Q W3 c3) ->
SRr SEGS W2 (mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros fx' e pos F q c tp tq O1 W2 regs2 mem2 md2 ly2 S2 kk nm2 retk Q Hretk Haft H2 HQ.
pose proof Haft as (_ & _ & (HJ2 & _ & _ & _ & _ & Hrv2 & _) & _).
assert (K : forall regs3 mem3 md3, (forall r, getr regs3 r = getr regs2 r) -> rdeq (rdW W2 mem2) (rdW W2 mem3) ->
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
    ly2 S2 W2 mem3 md3 kk ->
  Q W2 (mkCfg (@mkst fx' regs3 (Z_to_bv 64 (BASE + 0x6f9c)) mem3 (seg_rom SEGS)) md3)).
{ intros regs3 mem3 md3 Er Em HJ3. apply HQ.
  replace (BASE + 0x6f9c) with (vr_pc 0x8d4cc) by (unfold vr_pc, AF_verbs_receive; lia).
  apply (vr_hd_of_aft (fx := fx') B MT e 0x8d4cc pos F q c tp (rl10 e F q) tq O1 ly2 S2 W2 regs2 mem2 md2 _ _
    regs3 mem3 md3 Haft HJ3 Em).
  + replace (vr_rl_hd e F q c 0x8d4cc tq) with ((10, tq) :: rl10 e F q) by reflexivity.
    apply (vr_rv_keep B e regs3 regs2 _ _ Hrv2).
    * intros r0 _. apply Er.
    * intros r0 v Hin. left. split; [exact Hin | apply Er].
  + change (vr_hd_ntok 0x8d4cc (length (Verbs.toks (e_D e)))) with (2 <= length (Verbs.toks (e_D e)))%nat. lia. }
destruct Hretk as [-> | ->].
- exact (vr_jmp (fx := fx') B 0x701c 0x6f9c ltac:(lia) ltac:(vm_compute; reflexivity) W2 regs2 mem2 md2 _ _ _ _ _ _ _ _ _ _
    ly2 S2 _ HJ2 K).
- exact (vr_jmp (fx := fx') B 0x6f1c 0x6f9c ltac:(lia) ltac:(vm_compute; reflexivity) W2 regs2 mem2 md2 _ _ _ _ _ _ _ _ _ _
    ly2 S2 _ HJ2 K).
Qed.

(* sup_remove_all from its entry, through the jump 0x8d54c to JB 0x8d4cc, at the FP state the call returns *)
Lemma s10_call_all : forall e W pos F q c tp lyc Sc regs mem md k nm x (Q : world SEGS -> config -> Prop),
vr_ent B MT e ->
vr_cs B MT e pos F q c x 0x701c tp (rl10 e F q) lyc Sc W regs mem md k nm ->
length (Verbs.toks (e_D e)) = 2%nat ->
vr_h (e_R e) (e_D e) = (sup_remove_all_m (e_R e), false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_REMOVE_ALL (e_R e) ->
(forall (fx' : YK11.FPState) W2 c2, fxrel fx fx' -> vr_hd (fx := fx') B MT e 0x8d4cc W2 c2 -> Q W2 c2) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_remove_all) regs mem md) Q.
Proof.
intros e W pos F q c tp lyc Sc regs mem md k nm x Q Hent Hcs H2 Hvh Hk1 HQ.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcalls & _).
pose proof Hcs as ((HJ & _ & _ & _ & _ & Hrv & _ & _ & _ & Hrec & _) & _).
assert (Ht : (length (snd (sup_remove_all_m (e_R e))) <= 28)%nat).
{ unfold sup_remove_all_m. apply stub_len_host. exact (rec_code_range B _ _ _ _ _ Hrec). }
assert (HFsz : SUP_REMOVE_ALL_STK = ltac:(let v := eval vm_compute in SUP_REMOVE_ALL_STK in exact v)) by reflexivity.
assert (HVsz : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
apply (vr_call_arm B MT HB MTL ROA RRO RPG RECC PROGU e W pos F q c x 0x701c tp (rl10 e F q) lyc Sc
  regs mem md k nm AF_sup_remove_all SUP_REMOVE_ALL_STK (fp_rm (e_O e)) (EV_SUP_REMOVE_ALL (e_R e))
  (XM_SUP_REMOVE_ALL MT (e_R e) (snd (sup_remove_all_m (e_R e)))) (LIVE_SUP_REMOVE_ALL (snd (sup_remove_all_m (e_R e))))
  (sup_remove_all_m (e_R e)) _ Hent Hcs).
- unfold rl10. repeat (apply Forall_cons; [cbn [fst]; unfold acallee_saved; lia|]). apply Forall_nil.
- exact Hvh.
- exact Hk1.
- unfold EV_SUP_REMOVE_ALL, EV_RECORD, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC. rewrite (spill_frees0 _ Hcalls). lia.
- unfold XM_SUP_REMOVE_ALL, XM_RECORD, XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC. rewrite (spill_frees0 _ Hcalls).
  pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length (snd (sup_remove_all_m (e_R e)))) + 1) 1)
    VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M2.
  pose proof (mo_malloc_nonneg MT MTL VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M0.
  lia.
- unfold LIVE_SUP_REMOVE_ALL, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC, VERBS_RECEIVE_REQ. lia.
- rewrite HFsz. lia.
- rewrite HFsz, HVsz. lia.
- lia.
- reflexivity.
- exact (fp_rm_sub (e_O e)).
- intros ch HPRE1 Hfrm1 H1' H2' H3' H4' H5' H6' H7'.
  eapply SRr_mono.
  { exact (TSUP_REMOVE_ALL fx lyc Sc W regs mem md ch (e_R e) (e_O e) HPRE1 Hfrm1 ltac:(lia) H1' H2' H3' H5' H6' H7'). }
  intros W' c' _ HP. revert HP. apply apost_baseF_impl. intros ly' S' W'' regs' mem' md' HP.
  eapply rc_post_of_a. exact HP.
- (* 0x8d54c: j 0x8d4cc, at the FP state fx' the call returns *)
  intros fx' Hfx W2 regs2 mem2 md2 ly2 S2 tq O1 Haft.
  exact (s10_to_jb fx' e pos F q c tp tq O1 W2 regs2 mem2 md2 ly2 S2 _ _ 0x701c Q (or_introl eq_refl) Haft H2
    (fun W3 c3 H => HQ fx' W3 c3 Hfx H)).
Qed.

(* sup_remove(id) from its entry, through the jump 0x8d44c to JB 0x8d4cc, at the FP state the call returns *)
Lemma s10_call_rm : forall e W pos F q c tp lyc Sc regs mem md k nm id (Q : world SEGS -> config -> Prop),
vr_ent B MT e ->
vr_cs B MT e pos F q c id 0x6f1c tp (rl10 e F q) lyc Sc W regs mem md k nm ->
length (Verbs.toks (e_D e)) = 2%nat -> -2 ^ 31 <= id < 2 ^ 31 ->
vr_h (e_R e) (e_D e) = (sup_remove_m (e_R e) id, false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_REMOVE (e_R e) ->
(forall (fx' : YK11.FPState) W2 c2, fxrel fx fx' -> vr_hd (fx := fx') B MT e 0x8d4cc W2 c2 -> Q W2 c2) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_remove) regs mem md) Q.
Proof.
intros e W pos F q c tp lyc Sc regs mem md k nm id Q Hent Hcs H2 Hid Hvh Hk1 HQ.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcalls & _).
pose proof Hcs as ((HJ & _ & _ & _ & _ & Hrv & _ & _ & _ & Hrec & _) & _).
assert (Q10 : getr regs 10 = w64 id)
  by (apply (vr_rv_get regs _ 10 id Hrv); apply in_or_app; right; right; left; reflexivity).
assert (Ht : (length (snd (sup_remove_m (e_R e) id)) <= 28)%nat).
{ unfold sup_remove_m. apply stub_len_host. exact (rec_code_range B _ _ _ _ _ Hrec). }
pose proof (dec_length id Hid) as Hdec.
assert (HFsz : SUP_REMOVE_STK = ltac:(let v := eval vm_compute in SUP_REMOVE_STK in exact v)) by reflexivity.
assert (HVsz : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
apply (vr_call_arm B MT HB MTL ROA RRO RPG RECC PROGU e W pos F q c id 0x6f1c tp (rl10 e F q) lyc Sc
  regs mem md k nm AF_sup_remove SUP_REMOVE_STK (fp_rm (e_O e)) (EV_SUP_REMOVE (e_R e))
  (XM_SUP_REMOVE MT (e_R e) id (snd (sup_remove_m (e_R e) id))) (LIVE_SUP_REMOVE id (snd (sup_remove_m (e_R e) id)))
  (sup_remove_m (e_R e) id) _ Hent Hcs).
- unfold rl10. repeat (apply Forall_cons; [cbn [fst]; unfold acallee_saved; lia|]). apply Forall_nil.
- exact Hvh.
- exact Hk1.
- unfold EV_SUP_REMOVE, EV_RECORD, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC. rewrite (spill_frees0 _ Hcalls). lia.
- unfold XM_SUP_REMOVE, XM_RECORD, XM_ARG_S, XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC.
  rewrite (spill_frees0 _ Hcalls). change (sarg (Some (dec id))) with (dec id).
  pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length (dec id)) + 1) 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M1.
  pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length (snd (sup_remove_m (e_R e) id))) + 1) 1)
    VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M2.
  lia.
- unfold LIVE_SUP_REMOVE, LIVE_ARG_S, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC, VERBS_RECEIVE_REQ.
  change (sarg (Some (dec id))) with (dec id). lia.
- rewrite HFsz. lia.
- rewrite HFsz, HVsz. lia.
- lia.
- reflexivity.
- exact (fp_rm_sub (e_O e)).
- intros ch HPRE1 Hfrm1 H1' H2' H3' H4' H5' H6' H7'.
  eapply SRr_mono.
  { exact (TSUP_REMOVE fx lyc Sc W regs mem md ch id (e_R e) (e_O e) HPRE1 Hfrm1 ltac:(lia) H1' H2' Q10 Hid H3' H5' H6' H7'). }
  intros W' c' _ HP. revert HP. apply apost_baseF_impl. intros ly' S' W'' regs' mem' md' HP.
  eapply rc_post_of_a. exact HP.
- (* 0x8d44c: j 0x8d4cc, at the FP state fx' the call returns *)
  intros fx' Hfx W2 regs2 mem2 md2 ly2 S2 tq O1 Haft.
  exact (s10_to_jb fx' e pos F q c tp tq O1 W2 regs2 mem2 md2 ly2 S2 _ _ 0x6f1c Q (or_intror eq_refl) Haft H2
    (fun W3 c3 H => HQ fx' W3 c3 Hfx H)).
Qed.

Lemma vr_s10 : vr_s10_stmt B MT.
Proof.
intros e W cf Hent Hrt.
destruct Hrt as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hne & Hcore & Hline & Hcopy).
pose proof Hcore as (HJ & Hk & _ & _ & (EF & _) & Hrv & _ & Hspl & Henv & Hrec & _ & Hperm & _).
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & _ & Hcalls & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof (proj1 HJ) as HAR.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & _).
destruct (route_remove _ Hroute) as (v & args & T & Hv1 & Hv2).
assert (Hvv : forall v' args', Verbs.toks (e_D e) = v' :: args' ->
  Verbs.list_eqb v' Verbs.Lit.verb_chain = false /\ Verbs.list_eqb v' Verbs.Lit.verb_pin_set = false).
{ intros v' args' T'. rewrite T in T'. injection T' as <- _. exact (conj Hv1 Hv2). }
assert (R9 : getr regsc (Z_to_bv 5 9) = w64 (vr_s1 e))
  by (apply (vr_rv_get regsc _ _ _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R21 : getr regsc (Z_to_bv 5 21) = w64 (vr_ntok (e_D e)))
  by (apply (vr_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn; tauto).
assert (Hnt : 0 <= vr_ntok (e_D e) <= 64).
{ unfold vr_ntok, Verbs.toks, Verbs.line_words_max. rewrite length_firstn. lia. }
assert (Hntv : vr_ntok (e_D e) = Z.of_nat (length (Verbs.toks (e_D e)))) by reflexivity.
assert (Hin4 : In (4, pos) (frames Sc)) by (pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _); rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
destruct (vr_tmp_blocks B e _ lyc Sc W memc mdc _ HAR Hperm (vr_lb e q) ltac:(left; reflexivity)) as (Hlb0 & _).
destruct (vr_tmp_blocks B e _ lyc Sc W memc mdc _ HAR Hperm (vr_cb e c) ltac:(right; left; reflexivity)) as (Hcb0 & _).
pose proof Hlb0 as Hlb. pose proof Hcb0 as Hcb. unfold vr_lb, vr_cb in Hlb, Hcb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hlb) as (_ & Hq4 & Hqc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4 & Hcc & _).
assert (Hlpos : 0 <= vr_l (e_n e) (e_D e)) by (unfold vr_l; pose proof (strnlen_le (e_n e) (e_D e) ltac:(lia)); lia).
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as Hrq1.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrq2.
pose proof (vr_s1_cases e Hal16) as Hs1.
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
assert (HES : ESTACK = ltac:(let v := eval vm_compute in ESTACK in exact v)) by reflexivity.
assert (U9 : bv_unsigned (getr regsc 9) = vr_s1 e)
  by (change (getr regsc 9) with (getr regsc (Z_to_bv 5 9)); rewrite R9; unfold w64; apply unsigned_lit_small; lia).
change (vr_pc (vr_route_pc VRR.RRemove)) with (vr_pc 0x8d41c).
replace (vr_pc 0x8d41c) with (BASE + 0x6eec) by (unfold vr_pc, AF_verbs_receive; lia).
unfold cfg_at, w64.
destruct (Nat.eq_dec (length (Verbs.toks (e_D e))) 2) as [H2 | H2].
- (* two words: atoi(tok[1]), then sup_remove_all or sup_remove *)
  destruct args as [|a [|b rest]]; [rewrite T in H2; cbn in H2; lia | | rewrite T in H2; cbn in H2; lia].
  assert (HlenP : length tp = 2%nat) by (destruct Hcopy as (_ & (_ & HlenP & _)); rewrite HlenP, H2; reflexivity).
  destruct tp as [|p0 [|p1 [|p2 tp']]]; cbn in HlenP; try lia.
  destruct (vr_tok_arg B e F q c [p0; p1] lyc Sc W memc mdc 1 p1 a HAR Hperm Hcopy eq_refl
    ltac:(rewrite T; reflexivity)) as (_ & Hp1m & Hp14 & Hp1c & Ha8).
  assert (Hp1m' : aval_mem (rdW W memc) (F + 40) 8 p1)
    by (replace (F + 40) with (F + 32 + 8 * Z.of_nat 1) by lia; exact Hp1m).
  assert (HV : vr_vals_ok F q c p1) by (unfold vr_vals_ok; lia).
  pose proof (vr_seed_spt 0x6eec W regsc memc (vr_s1 e) F q c p1 U9 ltac:(lia) ltac:(lia) ltac:(lia) HV Hspl Hp1m')
    as HS.
  pose proof (vr_xt_atoms regsc F c q p1) as (X32 & _ & _ & _ & _ & X37).
  pose proof (vr_env_regs regsc (vr_xt F c q p1) 21 (Z_to_bv 5 21) eq_refl) as X21. rewrite R21 in X21.
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc (vr_xt F c q p1)))) by apply Eimg_env.
  pose proof (env_agree_Eimg regsc (vr_xt F c q p1)) as HAE.
  set (E := Eimg (Ereg regsc (vr_xt F c q p1))) in *. clearbody E.
  (* 0x8d41c: li a0,2 *)
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_spt) as Eq1. clear HF HFr HG.
  (* 0x8d420: bne s5,a0,0x8d68c *)
  psrr_branch_pi RUNP BR HS.
  + exfalso. rewrite branch_ne_U, (U_atom E 21 _ X21) in Hc by lia.
    unfold vr_ntok in Hc. rewrite H2 in Hc. vm_compute in Hc. discriminate Hc.
  + (* 0x8d424: li a0,-9; 0x8d428: ld s3,40(s1) *)
    paj_run_sh RUNP HS HJ.
    { awr_ok_tac. }
    set (mdv1 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv1.
    cbn [ms_mem mkst] in HFr.
    pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_spt) as Eq1b. clear HF HFr HG.
    (* 0x8d42c: bltu a0,s3,0x8d938 (UBSan: tok + 8 wraps) *)
    psrr_branch_pi RUNP BR HS.
    * exfalso. rewrite branch_ltu_U in Hc0.
      match type of Hc0 with context [U E (SLit ?z)] =>
        replace (U E (SLit z)) with (2 ^ 64 - 9) in Hc0 by (vm_compute; reflexivity) end.
      rewrite U_SOff, X32, unsigned_lit_small, zcanon_id in Hc0 by (unfold M64; lia).
      apply Z.ltb_lt in Hc0. lia.
    * (* 0x8d430: ld a0,8(s3); 0x8d434: jal wrapper_atoi *)
      paj_run_shc RUNP RUNC HS HJ.
      { awr_ok_tac. }
      set (mdv2 := with_vm_backing (m_vm_lazy mdv1) mat1 mdv1) in *. clearbody mdv2.
      pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_spt) as Eq2. clear HF HFr HG.
      pose proof (rdeq_trans _ _ _ (rdeq_trans _ _ _ Eq1 Eq1b) Eq2) as Eq.
      prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (19%bv : bv 5) Q19.
      pose proof (kept_regs_st_ok E _ _ regsc (vr_xt F c q p1) [2; 3; 4; 8; 9; 18; 21; 22; 24; 27] HS HAE
        ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
      pmkst HS.
      assert (Q10' : getr (ms_regs ms1) 10 = w64 p1) by (etransitivity; [exact Q10|]; rewrite X37; reflexivity).
      assert (Q19' : getr (ms_regs ms1) 19 = w64 (F + 32)).
      { etransitivity; [exact Q19|]. rewrite X32. unfold w64. f_equal. rewrite unsigned_lit_small by lia. reflexivity. }
      assert (Q2 : getr (ms_regs ms1) 2 = w64 (vr_s1 e)).
      { etransitivity; [exact (KR 2 ltac:(cbn; tauto))|]. apply (vr_rv_get regsc _ 2 _ Hrv). apply in_or_app; left; cbn; tauto. }
      assert (Q3 : getr (ms_regs ms1) 3 = w64 (as_gp B)).
      { etransitivity; [exact (KR 3 ltac:(cbn; tauto))|]. apply (vr_rv_get regsc _ 3 _ Hrv). apply in_or_app; left; cbn; tauto. }
      assert (Q4 : getr (ms_regs ms1) 4 = w64 (as_tp B)).
      { etransitivity; [exact (KR 4 ltac:(cbn; tauto))|]. apply (vr_rv_get regsc _ 4 _ Hrv). apply in_or_app; left; cbn; tauto. }
      assert (Hs1o : (vr_s1 e - vr_sp0 e) mod 16 = 0)
        by (destruct Hs1 as [E0|E0]; rewrite E0; [replace (vr_sp0 e - 192 - vr_sp0 e) with (-192) by lia
            | replace (vr_sp0 e - 208 - vr_sp0 e) with (-208) by lia]; reflexivity).
      assert (Qsp : spZ (ms_regs ms1) = vr_sp0 e + (vr_s1 e - vr_sp0 e)).
      { unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
      assert (Hra : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; first [lia | reflexivity | vm_compute; reflexivity]).
      pose proof (proj1 HJ) as HAR1.
      pose proof (vr_env_same B W memc W (ms_mem ms1) Eq Henv) as Henv1.
      pose proof Henv1 as (HRO1 & _ & _ & Hgd1 & Hfl1 & (ev & Herr1)).
      pose proof (vr_copy_same B e F c [p0; p1] W memc W (ms_mem ms1) Eq Hcopy) as Hcopy1.
      pose proof Hcopy1 as (_ & (_ & _ & _ & Hw1)).
      destruct (Hw1 1%nat p1 a eq_refl ltac:(rewrite T; reflexivity)) as (A1 & A2 & A3 & A4).
      pose proof (ecall_pre_stk_at SEGS B (3 * ESTACK) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e)
        (e_mem e) (e_md e) [(4, pos)] lyc Sc W (ms_mem ms1) mdv2 k (ms_regs ms1) (vr_s1 e - vr_sp0 e) HJ Qsp Hs1o
        ltac:(lia) ltac:(lia) ltac:(lia) Hra Q3 Q4) as HPRE1.
      (* the atoi wrapper on tok[1] *)
      eapply SRr_bind.
      { eapply (ART (3 * ESTACK) (aerrno_cell B) _ W (ms_regs ms1) (ms_mem ms1) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e)
          (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdv2 k (vr_s1 e - vr_sp0 e) _ _ HJ);
          [exact Qsp | exact Hs1o | lia | lia | lia | exact Q1 | intros a0 Ha0; exact Ha0 |].
        apply (AATOI fx lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv2 p1 a ev Hfl1 Hgd1 HPRE1 Q10' ltac:(lia)).
        - apply astr_atR_view. exact A1.
        - apply (aread_ok_of_block SEGS B LAWS (3 * ESTACK) lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv2 c
            (Z.of_nat (length (Verbs.line (e_D e))) + 1) p1 (astr_len a + 1) HAR1 Hcb); unfold astr_len; [lia | lia | lia |].
          rewrite Qsp. lia.
        - apply (amem8_of_blockA SEGS B LAWS lyc Sc W (ms_mem ms1) mdv2); [exact HAR1 | | unfold astr_len; lia].
          exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1). split; [exact Hcb | unfold astr_len; lia].
        - unfold astr_len. apply (BLKT lyc Sc W (ms_mem ms1) mdv2 c (Z.of_nat (length (Verbs.line (e_D e))) + 1));
            [exact HAR1 | exact Hcb | lia].
        - exact Herr1.
        - (* tok[1] apart from the errno cell: its bytes are in the copy block, not image bytes (blk_img); the
             errno cell's are (api_env) *)
          pose proof (pal_env B TL) as (_ & Hzi & _).
          destruct (Z_le_gt_dec (p1 + astr_len a + 1) (as_errno B)) as [Hz1|Hz1]; [left; exact Hz1|].
          destruct (Z_le_gt_dec (as_errno B + 4) p1) as [Hz2|Hz2]; [right; exact Hz2|]. exfalso.
          apply (blk_img SEGS B LAWS lyc Sc W (ms_mem ms1) mdv2 c (Z.of_nat (length (Verbs.line (e_D e))) + 1)
            (Z.max p1 (as_errno B)) HAR1 Hcb); [| apply Hzi; clear - Hz1 Hz2; lia].
          unfold req_size. destruct (Z.eqb_spec (Z.of_nat (length (Verbs.line (e_D e))) + 1) 0) as [Hzk|Hzk]; cbv iota;
            clear - A3 A4 Hz1 Hzk; unfold astr_len in Hz1; lia.
        - exact (vr_rtrom_ok B W (ms_mem ms1) HRO1). }
      cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HA0 & _) & HK2).
      (* the boundary facts across the wrapper *)
      assert (KX : vr_kx B e W memc mem2).
      { intros a0 Ha0 Hb Hn. rewrite (HK2 a0 Ha0); [exact (Eq a0) | | exact Hn]. lia. }
      assert (KRall : forall r, In r [2; 3; 4; 8; 9; 18; 21; 22; 24; 27] ->
        getr regs2 (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)).
      { intros r0 Hr0. rewrite (HP2 r0 ltac:(unfold acallee_saved; cbn in Hr0; lia)). exact (KR r0 Hr0). }
      assert (R19' : getr regs2 (Z_to_bv 5 19) = w64 (F + 32))
        by (rewrite (HP2 19 ltac:(unfold acallee_saved; lia)); exact Q19').
      assert (Hrv2 : vr_rv regs2 (vr_base B e ++ [(19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F);
        (27, shadow_addr F + 4)])).
      { apply (vr_rv_keep B e regs2 regsc _ _ Hrv).
        - intros r0 Hr0. apply KRall. cbn in Hr0 |- *. tauto.
        - intros r0 v0 Hin. cbn in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-.
          + right. exact R19'.
          + left. split; [cbn; tauto | apply KRall; cbn; tauto].
          + left. split; [cbn; tauto | apply KRall; cbn; tauto].
          + left. split; [cbn; tauto | apply KRall; cbn; tauto].
          + left. split; [cbn; tauto | apply KRall; cbn; tauto]. }
      assert (Hsl : Forall (fun ov => 0 <= fst ov <= 200) (vr_sl3 F q c)).
      { apply Forall_forall. intros [o w] Hin. unfold vr_sl3 in Hin. cbn in Hin.
        repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; cbn; lia|]). destruct Hin. }
      assert (Hcore2 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
        [(19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)]
        (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regs2 mem2 md2).
      { eapply (vr_core_kx B MT TL ROA RRO RECC PROGU e); [exact Hent | exact Hcore | exact HJ2 | exact KX | exact Hsl | exact Hrv2]. }
      pose proof (vr_line_kx B MT TL e q lyc Sc W memc mdc mem2 Hent HAR Hlb0 Hline KX) as Hline2.
      pose proof (vr_copy_kx B TL e F c [p0; p1] pos lyc Sc W memc mdc mem2 HAR Hin4 EF Hcb0 Hcopy KX) as Hcopy2.
      pose proof Hcore2 as (_ & _ & _ & _ & _ & _ & _ & Hspl2 & _).
      assert (U9' : bv_unsigned (getr regs2 9) = vr_s1 e).
      { change (getr regs2 9) with (getr regs2 (Z_to_bv 5 9)). rewrite (KRall 9 ltac:(cbn; tauto)), R9. unfold w64.
        apply unsigned_lit_small. lia. }
      assert (HV0 : vr_vals_ok F q c 0) by (unfold vr_vals_ok; lia).
      pose proof (vr_seed_sp 0x6f08 W regs2 mem2 (vr_s1 e) F q c 0 U9' ltac:(lia) ltac:(lia) HV0 Hspl2) as HS2.
      pose proof (vr_env_regs regs2 (vr_xt F c q 0) 10 (Z_to_bv 5 10) eq_refl) as X10e.
      assert (X10 : ew (Eimg (Ereg regs2 (vr_xt F c q 0))) 10 = Z_to_bv 64 (atoi_a a)) by (rewrite X10e; exact HA0).
      clear X10e.
      pose proof (vr_env_regs regs2 (vr_xt F c q 0) 19 (Z_to_bv 5 19) eq_refl) as X19. rewrite R19' in X19.
      assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg regs2 (vr_xt F c q 0)))) by apply Eimg_env.
      pose proof (env_agree_Eimg regs2 (vr_xt F c q 0)) as HAE2.
      set (E2 := Eimg (Ereg regs2 (vr_xt F c q 0))) in *. clearbody E2.
      assert (Hid : -2 ^ 31 <= atoi_a a < 2 ^ 31) by (unfold atoi_a; apply swrap32_range).
      (* 0x8d438: li a1,-1 *)
      paj_run_sh RUNP HS2 HJ2.
      { awr_ok_tac. }
      match goal with |- context [with_vm_backing (m_vm_lazy md2) ?mt md2] =>
        set (mdv3 := with_vm_backing (m_vm_lazy md2) mt md2) in * end.
      clearbody mdv3.
      cbn [ms_mem mkst] in HFr.
      pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_sp) as Eq3. clear HF HFr HG.
      (* 0x8d43c: beq a0,a1,0x8d548 *)
      psrr_branch_pi RUNP BR HS2.
      -- (* id = -1: 0x8d548 jal sup_remove_all *)
         rewrite branch_eq_U, (beq_m1 E2 (atoi_a a) _ X10 Hid) in Hc1 by (vm_compute; reflexivity).
         apply Z.eqb_eq in Hc1.
         assert (St : vr_st (e_D e) = Verbs.SCall Verbs.sup_remove_all).
         { rewrite (vr_st_route _ Hne), Hroute, T. cbn [VRR.plan_at]. rewrite Hc1. reflexivity. }
         destruct (vr_call_of (e_R e) (e_D e) _ Hne Hvv St) as [Hvh Hk1]. cbn [VerbsRun.run_call ev_call] in Hvh, Hk1.
         paj_run_shc RUNP RUNC HS2 HJ2.
         { awr_ok_tac. }
         match goal with |- context [with_vm_backing (m_vm_lazy mdv3) ?mt mdv3] =>
           set (mdv4 := with_vm_backing (m_vm_lazy mdv3) mt mdv3) in * end.
         clearbody mdv4.
         pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_sp) as Eq4. clear HF HFr HG.
         pose proof (rdeq_trans _ _ _ Eq3 Eq4) as Eq'.
         prreg HS2 (1%bv : bv 5) R1.
         pose proof (kept_regs_st_ok E2 _ _ regs2 (vr_xt F c q 0) [2; 3; 4; 8; 9; 10; 18; 19; 21; 22; 24; 27] HS2 HAE2
           ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
         pmkst HS2.
         rewrite (SIGP CS_sup_remove_all) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
         change (cmd_af CS_sup_remove_all) with AF_sup_remove_all.
         assert (Hcs : vr_cs B MT e pos F q c (atoi_a a) 0x701c [p0; p1] (rl10 e F q) lyc Sc W (ms_regs ms3) (ms_mem ms3)
           mdv4 k nm).
         { split; [|split; [exact (vr_line_same B e q W mem2 W (ms_mem ms3) Eq' Hline2)
                          | exact (vr_copy_same B e F c [p0; p1] W mem2 W (ms_mem ms3) Eq' Hcopy2)]].
           eapply vr_core_same; [exact Hcore2 | exact HJ2 | exact Eq' |].
           apply (vr_rv_keep B e (ms_regs ms3) regs2 _ _ Hrv2).
           - intros r0 Hr0. apply KR2. cbn in Hr0 |- *. tauto.
           - intros r0 v0 Hin. unfold rl10 in Hin. cbn in Hin.
             destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]; injection E1 as <- <-.
             + right. exact R1.
             + right. rewrite (KR2 10 ltac:(cbn; tauto)). exact HA0.
             + left. split; [cbn; tauto | apply KR2; cbn; tauto].
             + left. split; [cbn; tauto | apply KR2; cbn; tauto].
             + left. split; [cbn; tauto | apply KR2; cbn; tauto].
             + left. split; [cbn; tauto | apply KR2; cbn; tauto]. }
         apply (s10_call_all e W pos F q c [p0; p1] lyc Sc _ _ _ k nm (atoi_a a) _ Hent Hcs H2 Hvh Hk1).
         intros fx' W3 c3 Hfx H. cbv beta. exists fx'. split; [exact Hfx | right; exact H].
      -- (* id <> -1: 0x8d440: li a1,-8 *)
         rewrite branch_eq_U, (beq_m1 E2 (atoi_a a) _ X10 Hid) in Hc1 by (vm_compute; reflexivity).
         assert (St : vr_st (e_D e) = Verbs.SCall (Verbs.sup_remove (atoi_a a))).
         { rewrite (vr_st_route _ Hne), Hroute, T. cbn [VRR.plan_at]. rewrite Hc1. reflexivity. }
         destruct (vr_call_of (e_R e) (e_D e) _ Hne Hvv St) as [Hvh Hk1]. cbn [VerbsRun.run_call ev_call] in Hvh, Hk1.
         paj_run_sh RUNP HS2 HJ2.
         { awr_ok_tac. }
         match goal with |- context [with_vm_backing (m_vm_lazy mdv3) ?mt mdv3] =>
           set (mdv4 := with_vm_backing (m_vm_lazy mdv3) mt mdv3) in * end.
         clearbody mdv4.
         cbn [ms_mem mkst] in HFr.
         pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_sp) as Eq4. clear HF HFr HG.
         (* 0x8d444: beq s3,a1,0x8d938 (UBSan: tok + 8 null) *)
         psrr_branch_pi RUNP BR HS2.
         ++ exfalso. rewrite branch_eq_U, (U_atom E2 19 _ X19) in Hc2 by lia.
            match type of Hc2 with context [U E2 (SLit ?z)] =>
              replace (U E2 (SLit z)) with (2 ^ 64 - 8) in Hc2 by (vm_compute; reflexivity) end.
            apply Z.eqb_eq in Hc2. lia.
         ++ (* 0x8d448: jal sup_remove *)
            paj_run_shc RUNP RUNC HS2 HJ2.
            { awr_ok_tac. }
            match goal with |- context [with_vm_backing (m_vm_lazy mdv4) ?mt mdv4] =>
              set (mdv5 := with_vm_backing (m_vm_lazy mdv4) mt mdv4) in * end.
            clearbody mdv5.
            pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_sp) as Eq5. clear HF HFr HG.
            pose proof (rdeq_trans _ _ _ (rdeq_trans _ _ _ Eq3 Eq4) Eq5) as Eq'.
            prreg HS2 (1%bv : bv 5) R1.
            pose proof (kept_regs_st_ok E2 _ _ regs2 (vr_xt F c q 0) [2; 3; 4; 8; 9; 10; 18; 19; 21; 22; 24; 27] HS2 HAE2
              ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
            pmkst HS2.
            rewrite (SIGP CS_sup_remove) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
            change (cmd_af CS_sup_remove) with AF_sup_remove.
            assert (Hcs : vr_cs B MT e pos F q c (atoi_a a) 0x6f1c [p0; p1] (rl10 e F q) lyc Sc W (ms_regs ms4) (ms_mem ms4)
              mdv5 k nm).
            { split; [|split; [exact (vr_line_same B e q W mem2 W (ms_mem ms4) Eq' Hline2)
                             | exact (vr_copy_same B e F c [p0; p1] W mem2 W (ms_mem ms4) Eq' Hcopy2)]].
              eapply vr_core_same; [exact Hcore2 | exact HJ2 | exact Eq' |].
              apply (vr_rv_keep B e (ms_regs ms4) regs2 _ _ Hrv2).
              - intros r0 Hr0. apply KR2. cbn in Hr0 |- *. tauto.
              - intros r0 v0 Hin. unfold rl10 in Hin. cbn in Hin.
                destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]; injection E1 as <- <-.
                + right. exact R1.
                + right. rewrite (KR2 10 ltac:(cbn; tauto)). exact HA0.
                + left. split; [cbn; tauto | apply KR2; cbn; tauto].
                + left. split; [cbn; tauto | apply KR2; cbn; tauto].
                + left. split; [cbn; tauto | apply KR2; cbn; tauto].
                + left. split; [cbn; tauto | apply KR2; cbn; tauto]. }
            apply (s10_call_rm e W pos F q c [p0; p1] lyc Sc _ _ _ k nm (atoi_a a) _ Hent Hcs H2 Hid Hvh Hk1).
            intros fx' W3 c3 Hfx H. cbv beta. exists fx'. split; [exact Hfx | right; exact H].
- (* not two words: the shared refusal stub 0x8d68c *)
  assert (St : vr_st (e_D e) = Verbs.reject).
  { rewrite (vr_st_route _ Hne), Hroute, T. cbn [VRR.plan_at].
    destruct args as [|a [|b r]]; [reflexivity | rewrite T in H2; cbn in H2; lia | reflexivity]. }
  destruct (vr_rej_of (e_R e) (e_D e) Hne Hvv St) as [Hvh Hk1].
  remember (Eimg (Ereg regsc [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply env_agree_Eimg).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (vr_env_regs regsc [] 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  pose proof (vr_seed_ret 0x6eec W regsc memc) as HS. rewrite <- HE in HS.
  clear HE.
  (* 0x8d41c: li a0,2 *)
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq1. clear HF HFr HG.
  (* 0x8d420: bne s5,a0,0x8d68c *)
  psrr_branch_pi RUNP BR HS.
  + paj_run_to_shc RUNTO HS HJ 0x715c.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    pose proof (rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq2. clear HF HFr HG.
    pose proof (rdeq_trans _ _ _ Eq1 Eq2) as Eq.
    pose proof (kept_regs_st_ok E _ _ regsc [] [2; 3; 4; 8; 9; 18; 21; 22; 24; 27] HS HAE
      ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply SRr_ret. cbv beta. exists fx. split; [apply fxrel_refl|]. left. unfold vrF_pr, vr_atpr.
    replace (BASE + 0x715c) with (vr_pc 0x8d68c) by (unfold vr_pc, AF_verbs_receive; lia).
    assert (Hrv' : vr_rv (ms_regs ms0) (vr_base B e ++ vr_rl_pr e F q c 0x8d68c (-902))).
    { replace (vr_rl_pr e F q c 0x8d68c (-902))
        with [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)] by reflexivity.
      apply (vr_rv_keep B e (ms_regs ms0) regsc _ _ Hrv).
      - intros r0 Hr0. apply KR. cbn in Hr0 |- *. tauto.
      - intros r0 v0 Hin. left. cbn in Hin. destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-;
        (split; [cbn; tauto | apply KR; cbn; tauto]). }
    apply (vr_pr_mk B MT e 0x8d68c W pos F q c tp (vr_rl_pr e F q c 0x8d68c (-902)) lyc Sc (ms_regs ms0) (ms_mem ms0)
      mdv2 k nm Hvh Hk1 Hne).
    * change (vr_pr_ntok 0x8d68c (length (Verbs.toks (e_D e)))) with (1 <= length (Verbs.toks (e_D e)))%nat.
      rewrite T. cbn [length]. lia.
    * eapply vr_core_same; [exact Hcore | exact HJ | exact Eq | exact Hrv'].
    * exact Hrv'.
    * exact (vr_line_same B e q W memc W (ms_mem ms0) Eq Hline).
    * exact (vr_copy_same B e F c tp W memc W (ms_mem ms0) Eq Hcopy).
  + exfalso. rewrite branch_ne_U, (U_atom E 21 _ E21) in Hc by lia.
    change (U E (SLit 2)) with 2 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. lia.
Qed.

End e.
End f.
End d.
