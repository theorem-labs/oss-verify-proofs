(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S13 RESET (0x8dac4-0x8dac8, 0x8dc08-0x8dc14, 0x8dc3c-0x8dc50, 12
   instructions) of the walk of verbs_receive on the ASan build of plugin-hostd/fuzz_command (interface
   lib/A/Prog/verbs_receive_iface.v, vr_s13_stmt):
     0x8dac4 li a0,2; 0x8dac8 bltu s11,a0,0x8dc08     s11 = ntok - 1: three words or more fall to the refusal stub
                                                      0x8dacc (vr_pr)
     0x8dc08 ld s3,56(s1); 0x8dc0c bne s5,a0,0x8dc3c
     0x8dc10 ld a0,8(s6); 0x8dc14 j 0x8dc44           two words: which = tok[1] (a word of the copy block)
     0x8dc3c auipc a0; 0x8dc40 addi a0 (.str.10)      one word: which = the literal "all" at 0x22660
     0x8dc44 ld s4,40(s1); ld s9,8(s1); ld s11,32(s1); 0x8dc50 jal sup_reset
     0x8dc54                                          the stub into JA (vr_hd, the text in a0)
   The word count is split by case (one symbolic run per case). The call goes through verbs_receive_s10_lib.v's
   generic arm vr_call_arm (s13_call). The literal is handed through astr_argA's read-only branch: its bytes are
   read-only by vr_ent's cmd_ro_in conjunct, unowned and apart from the errno cell by HB, and the record's checks hold
   by computation. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
sup_reset_c answer_c hand_back_c xstrdup_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_s10_lib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
Import ListNotations.
Import VRL10.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the literal "all" (.str.10, 0x22660): its bytes, its end among CmdRo's literal ends *)
Lemma s13_all_str : forall rd, cmd_ro_ok rd -> astr_atR rd 0x22660 Verbs.Lit.word_all.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb. split.
- assert (H : abytes_atR rd 0x22660 RO_lit_22660) by (repeat (first [exact (proj1 Hb) | apply proj2 in Hb]); exact Hb).
  replace (Verbs.Lit.word_all ++ [Z_to_bv 8 0]) with RO_lit_22660 by (vm_compute; reflexivity). exact H.
- intros Hin. apply (in_map bv_unsigned) in Hin. vm_compute in Hin.
  destruct Hin as [H|[H|[H|[]]]]; discriminate.
Qed.
Lemma s13_all_end : In (0x22660 + Z.of_nat (length Verbs.Lit.word_all)) cmd_ro_ends.
Proof.
assert (H : existsb (Z.eqb 0x22663) cmd_ro_ends = true) by (vm_compute; reflexivity).
apply existsb_exists in H as (x & Hx & Hq). apply Z.eqb_eq in Hq.
change (0x22660 + Z.of_nat (length Verbs.Lit.word_all)) with 0x22663. rewrite Hq. exact Hx.
Qed.
Lemma s13_all_tail : forall rd, cmd_ro_ok rd ->
forall a, 0x22663 < a < 0x22663 - 0x22663 mod 8 + 8 -> rd a <> None.
Proof.
intros rd [_ Ht] a Ha. apply (Ht 0x22663); [|exact Ha].
pose proof s13_all_end as H. change (0x22660 + Z.of_nat (length Verbs.Lit.word_all)) with 0x22663 in H. exact H.
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
(* the callee's contract at every FP state (verbs_receive_c.v:222) and the named record facts *)
Hypothesis TSUP_RESET : forall fx0 : YK11.FPState, @tsup_reset_spec fx0 rc SK PI B MT.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis VOBJS : cmd_val_objs (PI := PI).
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

Lemma s13_unowned : forall i, 0 <= i < 4 -> ~ Exists (in_zr (0x22660 + i)) (as_owned_static B).
Proof.
intros i Hi. rewrite (AF0m.ts_owned B HB).
assert (Hall : forallb (fun r => ((fst r + snd r <=? 0x22660) || (0x22664 <=? fst r))%bool) AF0m.Tfib_owned_static = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in Hall. intros Hex. apply Exists_exists in Hex as (r & Hr & Hz). specialize (Hall r Hr).
unfold in_zr in Hz. apply orb_true_iff in Hall as [H | H]; apply Z.leb_le in H; lia.
Qed.
Lemma s13_errno : forall i, 0 <= i < 4 -> ~ (as_errno B <= 0x22660 + i < as_errno B + 4).
Proof. intros i Hi. rewrite (AF0m.ts_errno B HB). unfold AF0m.TFIB_ERRNO. lia. Qed.

(* the callee-saved registers at the call of sup_reset (0x8dc50), as JA's stub 0x8dc54 names them *)
Definition rl13 (e : vrE) (F q c : Z) : list (Z * Z) :=
[(18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F); (27, shadow_addr F + 4)].

(* the call of sup_reset from its entry to the stub 0x8dc54, which is its return address: it ends at the FP state the
   call returns *)
Lemma s13_call : forall e W pos F q c tp lyc Sc regs mem md k nm pw which (Q : world SEGS -> config -> Prop),
vr_ent B MT e ->
vr_cs B MT e pos F q c pw 0x7770 tp (rl13 e F q c) lyc Sc W regs mem md k nm ->
Verbs.toks (e_D e) <> [] ->
vr_h (e_R e) (e_D e) = (sup_reset_m (e_R e) which, false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_RESET (e_R e) ->
Z.of_nat (length (sarg which)) <= 8192 ->
0 <= pw < 2 ^ 64 ->
astr_argA B lyc Sc (rdW W mem) (in_roP SEGS RLO RHI) (e_O e) pw which ->
(forall x, which = Some x -> atail_vis SEGS W mem (pw + Z.of_nat (length x))) ->
(forall (fx' : YK11.FPState) W2 c2, fxrel fx fx' -> vr_hd (fx := fx') B MT e 0x8dc54 W2 c2 -> Q W2 c2) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_reset) regs mem md) Q.
Proof.
intros e W pos F q c tp lyc Sc regs mem md k nm pw which Q Hent Hcs Hne Hvh Hk1 Hlw Hpw Harg Htail HQ.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcalls & _).
pose proof Hcs as ((HJ & _ & _ & _ & _ & Hrv & _ & _ & _ & Hrec & _) & _).
assert (Q10 : getr regs 10 = w64 pw)
  by (apply (vr_rv_get regs _ 10 pw Hrv); apply in_or_app; right; right; left; reflexivity).
assert (Ht : (length (snd (sup_reset_m (e_R e) which)) <= 28)%nat).
{ unfold sup_reset_m, daemon_shape. apply stub_len. exact (rec_code_range B _ _ _ _ _ Hrec). }
assert (HFsz : SUP_RESET_STK = ltac:(let v := eval vm_compute in SUP_RESET_STK in exact v)) by reflexivity.
assert (HVsz : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
apply (vr_call_arm B MT HB MTL ROA RRO RPG RECC PROGU e W pos F q c pw 0x7770 tp (rl13 e F q c) lyc Sc
  regs mem md k nm AF_sup_reset SUP_RESET_STK (fp1 (e_O e)) (EV_SUP_RESET (e_R e)) (XM_SUP_RESET MT (e_R e) which)
  (LIVE_SUP_RESET (e_R e) which) (sup_reset_m (e_R e) which) _ Hent Hcs).
- unfold rl13. repeat (apply Forall_cons; [cbn [fst]; unfold acallee_saved; lia|]). apply Forall_nil.
- exact Hvh.
- exact Hk1.
- unfold EV_SUP_RESET, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP. rewrite (spill_frees0 _ Hcalls). lia.
- unfold XM_SUP_RESET, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. rewrite (spill_frees0 _ Hcalls).
  pose proof (mo_malloc_mono MT MTL (Z.of_nat (length (sarg which)) + 1) VERBS_RECEIVE_REQ
    ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M1.
  pose proof (mo_malloc_mono MT MTL (Z.of_nat (length (snd (sup_reset_m (e_R e) which))) + 1)
    VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M2.
  lia.
- unfold LIVE_SUP_RESET, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP, VERBS_RECEIVE_REQ. lia.
- rewrite HFsz. lia.
- rewrite HFsz, HVsz. lia.
- lia.
- reflexivity.
- intros a Ha. exact Ha.
- intros ch HPRE1 Hfrm1 H1' H2' H3' H4' H5' H6' H7'.
  eapply SRr_mono.
  { exact (TSUP_RESET fx lyc Sc W regs mem md ch pw which (e_R e) (e_O e)
      HPRE1 Hfrm1 H1' H2' Q10 Hpw Harg Htail H3' H4' H5' H6' H7'). }
  intros W' c' _ HP. revert HP. apply apost_baseF_impl. intros ly' S' W'' regs' mem' md' HP.
  eapply rc_post_of_b. exact HP.
- (* the return address is the stub 0x8dc54 itself, reached at the FP state fx' the call returns *)
  intros fx' Hfx W2 regs2 mem2 md2 ly2 S2 tq O1 Haft.
  pose proof Haft as (_ & _ & (HJ2 & _ & _ & _ & _ & Hrv2 & _) & _).
  apply SRr_ret. apply (HQ fx' _ _ Hfx).
  replace (BASE + 0x7770) with (vr_pc 0x8dc54) by (unfold vr_pc, AF_verbs_receive; lia).
  apply (vr_hd_of_aft (fx := fx') B MT e 0x8dc54 pos F q c tp (rl13 e F q c) tq O1 ly2 S2 W2 regs2 mem2 md2 _ _
    regs2 mem2 md2 Haft HJ2 (rdeq_refl _)).
  + replace (vr_rl_hd e F q c 0x8dc54 tq) with ((10, tq) :: rl13 e F q c) by reflexivity. exact Hrv2.
  + change (vr_hd_ntok 0x8dc54 (length (Verbs.toks (e_D e)))) with (1 <= length (Verbs.toks (e_D e)))%nat.
    destruct (Verbs.toks (e_D e)); [congruence | cbn [length]; lia].
Qed.

Lemma vr_s13 : vr_s13_stmt B MT.
Proof.
intros e W cf Hent Hrt.
destruct Hrt as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hne & Hcore & Hline & Hcopy).
pose proof Hcore as (HJ & Hk & _ & _ & (EF & _) & Hrv & _ & Hspl & _ & Hrec & _ & Hperm & _).
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & _ & Hcalls & _ & _ & _ & _ & _ & _ & _ & _
  & Hroin & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof (proj1 HJ) as HAR.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & _).
destruct (route_reset _ Hroute) as (args & T).
assert (Hvv : forall v args', Verbs.toks (e_D e) = v :: args' ->
  Verbs.list_eqb v Verbs.Lit.verb_chain = false /\ Verbs.list_eqb v Verbs.Lit.verb_pin_set = false).
{ intros v args' T'. rewrite T in T'. injection T' as <- _. split; vm_compute; reflexivity. }
assert (R9 : getr regsc (Z_to_bv 5 9) = w64 (vr_s1 e))
  by (apply (vr_rv_get regsc _ _ _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R21 : getr regsc (Z_to_bv 5 21) = w64 (vr_ntok (e_D e)))
  by (apply (vr_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn; tauto).
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 (F + 32))
  by (apply (vr_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn; tauto).
assert (R27 : getr regsc (Z_to_bv 5 27) = w64 (vr_ntok (e_D e) - 1))
  by (apply (vr_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn; tauto).
assert (Hnt : 0 <= vr_ntok (e_D e) <= 64).
{ unfold vr_ntok, Verbs.toks, Verbs.line_words_max. rewrite length_firstn. lia. }
assert (Hntv : vr_ntok (e_D e) = Z.of_nat (length (Verbs.toks (e_D e)))) by reflexivity.
assert (Hin4 : In (4, pos) (frames Sc)) by (pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _); rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
destruct (vr_tmp_blocks B e _ lyc Sc W memc mdc _ HAR Hperm (vr_lb e q) ltac:(left; reflexivity)) as (Hlb & _).
destruct (vr_tmp_blocks B e _ lyc Sc W memc mdc _ HAR Hperm (vr_cb e c) ltac:(right; left; reflexivity)) as (Hcb & _).
unfold vr_lb, vr_cb in Hlb, Hcb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hlb) as (_ & Hq4 & Hqc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4 & Hcc & _).
assert (Hlpos : 0 <= vr_l (e_n e) (e_D e)) by (unfold vr_l; pose proof (strnlen_le (e_n e) (e_D e) ltac:(lia)); lia).
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as Hrq1.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrq2.
pose proof (vr_s1_cases e Hal16) as Hs1.
assert (U9 : bv_unsigned (getr regsc 9) = vr_s1 e)
  by (change (getr regsc 9) with (getr regsc (Z_to_bv 5 9)); rewrite R9; unfold w64; apply unsigned_lit_small; lia).
change (vr_pc (vr_route_pc VRR.RReset)) with (vr_pc 0x8dac4).
replace (vr_pc 0x8dac4) with (BASE + 0x75e0) by (unfold vr_pc, AF_verbs_receive; lia).
unfold cfg_at, w64.
destruct args as [|a [|b rest]].
- (* one word: which = "all" *)
  assert (H1 : length (Verbs.toks (e_D e)) = 1%nat) by (rewrite T; reflexivity).
  assert (St : vr_st (e_D e) = Verbs.SCall (Verbs.sup_reset Verbs.Lit.word_all))
    by (rewrite (vr_st_route _ Hne), Hroute, T; reflexivity).
  destruct (vr_call_of (e_R e) (e_D e) _ Hne Hvv St) as [Hvh Hk1]. cbn [VerbsRun.run_call ev_call] in Hvh, Hk1.
  assert (HV : vr_vals_ok F q c 0) by (unfold vr_vals_ok; lia).
  pose proof (vr_seed_sp 0x75e0 W regsc memc (vr_s1 e) F q c 0 U9 ltac:(lia) ltac:(lia) HV Hspl) as HS.
  pose proof (vr_xt_atoms regsc F c q 0) as (X32 & X33 & X34 & X35 & _).
  pose proof (vr_env_regs regsc (vr_xt F c q 0) 21 (Z_to_bv 5 21) eq_refl) as X21. rewrite R21 in X21.
  pose proof (vr_env_regs regsc (vr_xt F c q 0) 27 (Z_to_bv 5 27) eq_refl) as X27. rewrite R27 in X27.
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc (vr_xt F c q 0)))) by apply Eimg_env.
  pose proof (env_agree_Eimg regsc (vr_xt F c q 0)) as HAE.
  pose proof (img_env_atomP _ 346 HEI ltac:(unfold A_TEXT, A_LIM; lia)) as X346.
  set (E := Eimg (Ereg regsc (vr_xt F c q 0))) in *. clearbody E.
  (* 0x8dac4: li a0,2 *)
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_sp) as Eq1. clear HF HFr HG.
  (* 0x8dac8: bltu s11,a0,0x8dc08 *)
  psrr_branch_pi RUNP BR HS.
  + (* 0x8dc08: ld s3,56(s1) *)
    paj_run_sh RUNP HS HJ.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_sp) as Eq2. clear HF HFr HG.
    (* 0x8dc0c: bne s5,a0,0x8dc3c *)
    psrr_branch_pi RUNP BR HS.
    * (* 0x8dc3c: a0 = "all"; the three loads; jal sup_reset *)
      paj_run_shc RUNP RUNC HS HJ.
      { awr_ok_tac. }
      set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mat1 mdv2) in *. clearbody mdv3.
      pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_sp) as Eq3. clear HF HFr HG.
      pose proof (rdeq_trans _ _ _ (rdeq_trans _ _ _ Eq1 Eq2) Eq3) as Eq.
      prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (19%bv : bv 5) Q19.
      prreg HS (20%bv : bv 5) Q20. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
      pose proof (kept_regs_st_ok E _ _ regsc (vr_xt F c q 0) [2; 3; 4; 8; 9; 18; 21; 22] HS HAE
        ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
      pmkst HS.
      rewrite (SIGP CS_sup_reset) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
      change (cmd_af CS_sup_reset) with AF_sup_reset.
      assert (Hcs : vr_cs B MT e pos F q c 0x22660 0x7770 tp (rl13 e F q c) lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv3 k nm).
      { split; [|split; [exact (vr_line_same B e q W memc W (ms_mem ms1) Eq Hline)
                       | exact (vr_copy_same B e F c tp W memc W (ms_mem ms1) Eq Hcopy)]].
        eapply vr_core_same; [exact Hcore | exact HJ | exact Eq |].
        apply (vr_rv_keep B e (ms_regs ms1) regsc _ _ Hrv).
        - intros r0 Hr0. apply KR. cbn in Hr0 |- *. tauto.
        - intros r0 v Hin. unfold rl13 in Hin. cbn in Hin.
          destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]]]; injection E1 as <- <-.
          + right. exact Q1.
          + right. etransitivity; [exact Q10|]. rewrite X346. change 346%nat with (A_OBJ 105).
            rewrite (VOBJS 105%nat ltac:(vm_compute; lia)). vm_compute. reflexivity.
          + left. split; [cbn; tauto | apply KR; cbn; tauto].
          + right. etransitivity; [exact Q19|]. rewrite X35. reflexivity.
          + right. etransitivity; [exact Q20|]. rewrite X32. reflexivity.
          + left. split; [cbn; tauto | apply KR; cbn; tauto].
          + left. split; [cbn; tauto | apply KR; cbn; tauto].
          + right. etransitivity; [exact Q25|]. rewrite X33. reflexivity.
          + right. etransitivity; [exact Q27|]. rewrite X34. reflexivity. }
      pose proof Hcs as ((_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hro1 & _) & _) & _).
      assert (RO22660 : forall i, 0 <= i < 4 -> in_roP SEGS RLO RHI (0x22660 + i)).
      { pose proof Hroin as H. unfold cmd_ro_in in H. repeat (first [exact (proj1 H) | apply proj2 in H]). }
      apply (s13_call e W pos F q c tp lyc Sc _ _ _ k nm 0x22660 (Some Verbs.Lit.word_all) _ Hent Hcs Hne Hvh Hk1).
      -- change (length (sarg (Some Verbs.Lit.word_all))) with 3%nat. lia.
      -- lia.
      -- cbn [astr_argA]. split; [lia|]. split; [exact (s13_all_str _ Hro1)|].
         change (length Verbs.Lit.word_all) with 3%nat. split; [unfold LMAX; lia|].
         right. split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | exact s13_all_end]]].
         intros i Hi. split; [exact (RO22660 i ltac:(lia))|].
         split; [exact (s13_unowned i ltac:(lia)) | exact (s13_errno i ltac:(lia))].
      -- intros x Hx. injection Hx as <-. change (0x22660 + Z.of_nat (length Verbs.Lit.word_all)) with 0x22663.
         intros a0 Ha0. exact (s13_all_tail _ Hro1 a0 Ha0).
      -- intros fx' W2 c2 Hfx H. cbv beta. exists fx'. split; [exact Hfx | right; exact H].
    * exfalso. rewrite branch_ne_U, (U_atom E 21 _ X21) in Hc0 by lia.
      change (U E (SLit 2)) with 2 in Hc0. apply negb_false_iff, Z.eqb_eq in Hc0. lia.
  + exfalso. rewrite branch_ltu_U, (U_atom E 27 _ X27) in Hc by lia.
    change (U E (SLit 2)) with 2 in Hc. apply Z.ltb_ge in Hc. lia.
- (* two words: which = tok[1] *)
  assert (H2 : length (Verbs.toks (e_D e)) = 2%nat) by (rewrite T; reflexivity).
  assert (St : vr_st (e_D e) = Verbs.SCall (Verbs.sup_reset a))
    by (rewrite (vr_st_route _ Hne), Hroute, T; reflexivity).
  destruct (vr_call_of (e_R e) (e_D e) _ Hne Hvv St) as [Hvh Hk1]. cbn [VerbsRun.run_call ev_call] in Hvh, Hk1.
  assert (HlenP : length tp = 2%nat) by (destruct Hcopy as (_ & (_ & HlenP & _)); rewrite HlenP, H2; reflexivity).
  destruct tp as [|p0 [|p1 [|p2 tp']]]; cbn in HlenP; try lia.
  destruct (vr_tok_arg B e F q c [p0; p1] lyc Sc W memc mdc 1 p1 a HAR Hperm Hcopy eq_refl
    ltac:(rewrite T; reflexivity)) as (_ & Hp1m & Hp14 & Hp1c & Ha8).
  assert (Hp1m' : aval_mem (rdW W memc) (F + 40) 8 p1)
    by (replace (F + 40) with (F + 32 + 8 * Z.of_nat 1) by lia; exact Hp1m).
  assert (HV : vr_vals_ok F q c p1) by (unfold vr_vals_ok; lia).
  assert (U22 : bv_unsigned (getr regsc 22) = F + 32)
    by (change (getr regsc 22) with (getr regsc (Z_to_bv 5 22)); rewrite R22; unfold w64; apply unsigned_lit_small; lia).
  pose proof (vr_seed_spt 0x75e0 W regsc memc (vr_s1 e) F q c p1 U9 U22 ltac:(lia) ltac:(lia) ltac:(lia) HV Hspl Hp1m')
    as HS.
  pose proof (vr_xt_atoms regsc F c q p1) as (X32 & X33 & X34 & X35 & _ & X37).
  pose proof (vr_env_regs regsc (vr_xt F c q p1) 21 (Z_to_bv 5 21) eq_refl) as X21. rewrite R21 in X21.
  pose proof (vr_env_regs regsc (vr_xt F c q p1) 27 (Z_to_bv 5 27) eq_refl) as X27. rewrite R27 in X27.
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc (vr_xt F c q p1)))) by apply Eimg_env.
  pose proof (env_agree_Eimg regsc (vr_xt F c q p1)) as HAE.
  set (E := Eimg (Ereg regsc (vr_xt F c q p1))) in *. clearbody E.
  (* 0x8dac4: li a0,2 *)
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_spt) as Eq1. clear HF HFr HG.
  (* 0x8dac8: bltu s11,a0,0x8dc08 *)
  psrr_branch_pi RUNP BR HS.
  + (* 0x8dc08: ld s3,56(s1) *)
    paj_run_sh RUNP HS HJ.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_spt) as Eq2. clear HF HFr HG.
    (* 0x8dc0c: bne s5,a0,0x8dc3c *)
    psrr_branch_pi RUNP BR HS.
    * exfalso. rewrite branch_ne_U, (U_atom E 21 _ X21) in Hc0 by lia.
      change (U E (SLit 2)) with 2 in Hc0. unfold vr_ntok in Hc0. rewrite H2 in Hc0. vm_compute in Hc0. discriminate Hc0.
    * (* 0x8dc10: ld a0,8(s6); j; the three loads; jal sup_reset *)
      paj_run_shc RUNP RUNC HS HJ.
      { awr_ok_tac. }
      set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mat1 mdv2) in *. clearbody mdv3.
      pose proof (rdeq_of_frame _ _ _ _ _ HFr ro_spt) as Eq3. clear HF HFr HG.
      pose proof (rdeq_trans _ _ _ (rdeq_trans _ _ _ Eq1 Eq2) Eq3) as Eq.
      prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (19%bv : bv 5) Q19.
      prreg HS (20%bv : bv 5) Q20. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
      pose proof (kept_regs_st_ok E _ _ regsc (vr_xt F c q p1) [2; 3; 4; 8; 9; 18; 21; 22] HS HAE
        ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
      pmkst HS.
      rewrite (SIGP CS_sup_reset) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
      change (cmd_af CS_sup_reset) with AF_sup_reset.
      assert (Hcs : vr_cs B MT e pos F q c p1 0x7770 [p0; p1] (rl13 e F q c) lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv3 k nm).
      { split; [|split; [exact (vr_line_same B e q W memc W (ms_mem ms1) Eq Hline)
                       | exact (vr_copy_same B e F c [p0; p1] W memc W (ms_mem ms1) Eq Hcopy)]].
        eapply vr_core_same; [exact Hcore | exact HJ | exact Eq |].
        apply (vr_rv_keep B e (ms_regs ms1) regsc _ _ Hrv).
        - intros r0 Hr0. apply KR. cbn in Hr0 |- *. tauto.
        - intros r0 v Hin. unfold rl13 in Hin. cbn in Hin.
          destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]]]; injection E1 as <- <-.
          + right. exact Q1.
          + right. etransitivity; [exact Q10|]. rewrite X37. reflexivity.
          + left. split; [cbn; tauto | apply KR; cbn; tauto].
          + right. etransitivity; [exact Q19|]. rewrite X35. reflexivity.
          + right. etransitivity; [exact Q20|]. rewrite X32. reflexivity.
          + left. split; [cbn; tauto | apply KR; cbn; tauto].
          + left. split; [cbn; tauto | apply KR; cbn; tauto].
          + right. etransitivity; [exact Q25|]. rewrite X33. reflexivity.
          + right. etransitivity; [exact Q27|]. rewrite X34. reflexivity. }
      pose proof (vr_copy_same B e F c [p0; p1] W memc W (ms_mem ms1) Eq Hcopy) as Hcopy1.
      destruct (vr_tok_arg B e F q c [p0; p1] lyc Sc W (ms_mem ms1) mdv3 1 p1 a (proj1 HJ) Hperm Hcopy1 eq_refl
        ltac:(rewrite T; reflexivity)) as (Harg & _).
      pose proof Hcopy1 as (_ & (_ & _ & _ & Hw1)).
      destruct (Hw1 1%nat p1 a eq_refl ltac:(rewrite T; reflexivity)) as (_ & _ & A3 & A4).
      apply (s13_call e W pos F q c [p0; p1] lyc Sc _ _ _ k nm p1 (Some a) _ Hent Hcs Hne Hvh Hk1).
      -- cbn [sarg]. exact Ha8.
      -- lia.
      -- exact Harg.
      -- intros x Hx. injection Hx as <-.
         apply (BLKT lyc Sc W (ms_mem ms1) mdv3 c (Z.of_nat (length (Verbs.line (e_D e))) + 1)); [exact (proj1 HJ) | exact Hcb | lia].
      -- intros fx' W2 c2 Hfx H. cbv beta. exists fx'. split; [exact Hfx | right; exact H].
  + exfalso. rewrite branch_ltu_U, (U_atom E 27 _ X27) in Hc by lia.
    change (U E (SLit 2)) with 2 in Hc. apply Z.ltb_ge in Hc. lia.
- (* three words or more: the refusal stub 0x8dacc *)
  assert (H3 : (3 <= length (Verbs.toks (e_D e)))%nat) by (rewrite T; cbn [length]; lia).
  assert (St : vr_st (e_D e) = Verbs.reject) by (rewrite (vr_st_route _ Hne), Hroute, T; reflexivity).
  destruct (vr_rej_of (e_R e) (e_D e) Hne Hvv St) as [Hvh Hk1].
  remember (Eimg (Ereg regsc [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply env_agree_Eimg).
  assert (E27 : ew E 27 = Z_to_bv 64 (vr_ntok (e_D e) - 1))
    by (subst E; rewrite (vr_env_regs regsc [] 27 (Z_to_bv 5 27) eq_refl), R27; reflexivity).
  pose proof (vr_seed_ret 0x75e0 W regsc memc) as HS. rewrite <- HE in HS.
  clear HE.
  (* 0x8dac4: li a0,2 *)
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq1. clear HF HFr HG.
  (* 0x8dac8: bltu s11,a0,0x8dc08 *)
  psrr_branch_pi RUNP BR HS.
  + exfalso. rewrite branch_ltu_U, (U_atom E 27 _ E27) in Hc by lia.
    change (U E (SLit 2)) with 2 in Hc. apply Z.ltb_lt in Hc. lia.
  + paj_run_to_shc RUNTO HS HJ 0x75e8.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    pose proof (rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq2. clear HF HFr HG.
    pose proof (rdeq_trans _ _ _ Eq1 Eq2) as Eq.
    pose proof (kept_regs_st_ok E _ _ regsc [] [2; 3; 4; 8; 9; 18; 21; 22] HS HAE
      ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply SRr_ret. cbv beta. exists fx. split; [apply fxrel_refl|]. left. unfold vrF_pr, vr_atpr.
    replace (BASE + 30184) with (vr_pc 0x8dacc) by (unfold vr_pc, AF_verbs_receive; lia).
    assert (Hrv' : vr_rv (ms_regs ms0) (vr_base B e ++ vr_rl_pr e F q c 0x8dacc (-902))).
    { replace (vr_rl_pr e F q c 0x8dacc (-902)) with [(18, q); (22, F + 32)] by reflexivity.
      apply (vr_rv_keep B e (ms_regs ms0) regsc _ _ Hrv).
      - intros r0 Hr0. apply KR. cbn in Hr0 |- *. tauto.
      - intros r0 v Hin. left. cbn in Hin. destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-;
        (split; [cbn; tauto | apply KR; cbn; tauto]). }
    apply (vr_pr_mk B MT e 0x8dacc W pos F q c tp (vr_rl_pr e F q c 0x8dacc (-902)) lyc Sc (ms_regs ms0) (ms_mem ms0)
      mdv2 k nm Hvh Hk1 Hne).
    * change (vr_pr_ntok 0x8dacc (length (Verbs.toks (e_D e)))) with (2 <= length (Verbs.toks (e_D e)))%nat. lia.
    * eapply vr_core_same; [exact Hcore | exact HJ | exact Eq | exact Hrv'].
    * exact Hrv'.
    * exact (vr_line_same B e q W memc W (ms_mem ms0) Eq Hline).
    * exact (vr_copy_same B e F c tp W memc W (ms_mem ms0) Eq Hcopy).
Qed.

End e.
End f.
End d.
