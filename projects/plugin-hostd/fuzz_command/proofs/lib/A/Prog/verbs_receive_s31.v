(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S31 (AFTER, 0x8daf4-0x8db4c, 23 instructions) of the walk of
   verbs_receive on the ASan build of plugin-hostd/fuzz_command: vr_s31_stmt of lib/A/Prog/verbs_receive_iface.v,
   on the interface of the fixed statements (the read-only range is CmdGlob's CMD_RLO / CMD_RHI).
   After the reply, s8 := tok[0]; strcspn(tok[0], " \t") is 9 or 11 and strncmp(tok[0], "patch_set %i %s %s", 9)
   or strncmp(tok[0], "preset_load %i %s", 11) is 0 exactly when Verbs.after gives a call (VerbsFacts' cspn_tfirst
   and strncmp_verb); then sup_after_reply(atoi(tok[1]), tok[0]). Every path ends at 0x8db50 (vr_af).
   The walk is cut at the three runtime calls and the program call: each piece seeds the symbolic state from the
   concrete boundary (verbs_receive_s31_k.v s31_seed), runs to the next call or branch (PaLibF / PaCallRun), steps
   the runtime entry through the kit's aj_art_at (PaArt.v), and rebuilds the boundary with core_keep; the program
   call goes through PaFx's cl_callS_wideF (sup_after_reply's post is apost_baseF, so the exit vr_af is at the FP
   state the call returns at), its frame chain by achain_push on the entry's chain (s31_chain). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strcspn_c VerbsFacts __intscan_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route verbs_receive_pre SlotRec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString RtNumber RtAlloc04 RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_after_reply_c arg_i_c xstrdup_c rec_calls_free_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_live.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx verbs_receive_s31_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PCs := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strcspn_c.
Module PSn := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.StrFun.
Module PVF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.VerbsFacts.
Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.
Module PIS := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.__intscan_c.
Module K := VrS31K.

Lemma AFV : AF_verbs_receive = 28572.
Proof. reflexivity. Qed.

(* the three literals S31 hands to strcspn and strncmp, from cmd_ro_ok *)
Lemma s31_lits : forall rd, cmd_ro_ok rd ->
abytes_atR rd 0x224c0 RO_lit_224c0 /\ abytes_atR rd 0x224e0 RO_lit_224e0 /\ abytes_atR rd 0x22520 RO_lit_22520.
Proof. intros rd [H _]. unfold cmd_ro_bytes in H. decompose [and] H. repeat split; assumption. Qed.

(* the two formats of the inline verb_is, as the image holds them *)
Lemma s31_fmt_pl : PV.Lit.fmt_preset_load ++ [Z_to_bv 8 0] = RO_lit_224e0.
Proof. vm_compute. reflexivity. Qed.
Lemma s31_fmt_ps : PV.Lit.fmt_patch_set ++ [Z_to_bv 8 0] = RO_lit_22520.
Proof. vm_compute. reflexivity. Qed.
Lemma s31_vf_pl : length (PV.vfirst PV.Lit.fmt_preset_load) = 11%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma s31_vf_ps : length (PV.vfirst PV.Lit.fmt_patch_set) = 9%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma s31_len_pl : length PV.Lit.fmt_preset_load = 17%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma s31_len_ps : length PV.Lit.fmt_patch_set = 18%nat.
Proof. vm_compute. reflexivity. Qed.

(* a list of bytes with no NUL *)
Lemma nz_of_forallb : forall s : list byte, forallb (fun b => negb (bv_unsigned b =? 0)) s = true ->
Forall (fun b => bv_unsigned b <> 0) s.
Proof.
intros s H. rewrite forallb_forall in H. apply Forall_forall. intros b Hb E.
specialize (H b Hb). rewrite E in H. cbn in H. discriminate H.
Qed.
Lemma nz_of_notin : forall s : list byte, ~ In (Z_to_bv 8 0) s -> Forall (fun b => bv_unsigned b <> 0) s.
Proof.
intros s H. apply Forall_forall. intros b Hb E. apply H.
replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. vm_compute. reflexivity.
Qed.
Lemma notin_of_nz : forall s : list byte, Forall (fun b => bv_unsigned b <> 0) s -> ~ In (Z_to_bv 8 0) s.
Proof.
intros s H Hin. rewrite Forall_forall in H. specialize (H _ Hin). apply H. vm_compute. reflexivity.
Qed.

(* the atoi wrapper's value is an int *)
Lemma swrap32_range : forall z, -2 ^ 31 <= bv_swrap 32 z < 2 ^ 31.
Proof.
intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
assert (E : 2 ^ Z.of_N 32 = 4294967296) by reflexivity. rewrite E.
change (Z.div 4294967296 2) with 2147483648.
pose proof (Z.mod_pos_bound (z + 2147483648) 4294967296 ltac:(lia)). lia.
Qed.

(* the call after the reply, as the dispatch's own words give it *)
Lemma s31_aft_toks : forall D, Verbs.toks D <> [] -> vr_aft D = PV.after atoi_a (Verbs.toks D).
Proof.
intros D H. unfold vr_aft, PV.receive. destruct (Verbs.toks D) as [|w tk] eqn:E; [congruence | reflexivity].
Qed.

(* the inline verb_is of S31: the first word is the verb of preset_load or of patch_set. Their verbs are 11 and 9
   bytes long, so the length of the first word's own first word decides which of the two tests can hold *)
Lemma s31_aft_ps : forall w0 w1 tk, length (PV.tfirst w0) = 9%nat ->
(PV.after atoi_a (w0 :: w1 :: tk) <> None <-> PV.verb_is_m w0 PV.Lit.fmt_patch_set = true).
Proof.
intros w0 w1 tk Hl. unfold PV.after. cbv beta iota.
rewrite (PVF.verb_is_m_len_ne w0 PV.Lit.fmt_preset_load ltac:(rewrite Hl, s31_vf_pl; discriminate)). cbn [orb].
destruct (PV.verb_is_m w0 PV.Lit.fmt_patch_set).
- split; [reflexivity | intros _; discriminate].
- split; [intros H; exfalso; exact (H eq_refl) | discriminate].
Qed.
Lemma s31_aft_pl : forall w0 w1 tk, length (PV.tfirst w0) = 11%nat ->
(PV.after atoi_a (w0 :: w1 :: tk) <> None <-> PV.verb_is_m w0 PV.Lit.fmt_preset_load = true).
Proof.
intros w0 w1 tk Hl. unfold PV.after. cbv beta iota.
rewrite (PVF.verb_is_m_len_ne w0 PV.Lit.fmt_patch_set ltac:(rewrite Hl, s31_vf_ps; discriminate)).
rewrite orb_false_r.
destruct (PV.verb_is_m w0 PV.Lit.fmt_preset_load).
- split; [reflexivity | intros _; discriminate].
- split; [intros H; exfalso; exact (H eq_refl) | discriminate].
Qed.
Lemma s31_aft_none : forall D w0 w1 tk, Verbs.toks D = w0 :: w1 :: tk ->
length (PV.tfirst w0) <> 9%nat -> length (PV.tfirst w0) <> 11%nat -> vr_aft D = None.
Proof.
intros D w0 w1 tk Etk H9 H11.
rewrite (s31_aft_toks D ltac:(rewrite Etk; discriminate)), Etk. unfold PV.after. cbv beta iota.
rewrite (PVF.verb_is_m_len_ne w0 PV.Lit.fmt_preset_load ltac:(rewrite s31_vf_pl; exact H11)).
rewrite (PVF.verb_is_m_len_ne w0 PV.Lit.fmt_patch_set ltac:(rewrite s31_vf_ps; exact H9)).
reflexivity.
Qed.
Lemma s31_aft_val : forall D w0 w1 tk, Verbs.toks D = w0 :: w1 :: tk ->
PV.after atoi_a (w0 :: w1 :: tk) <> None -> vr_aft D = Some (atoi_a w1, w0).
Proof.
intros D w0 w1 tk Etk H. rewrite (s31_aft_toks D ltac:(rewrite Etk; discriminate)), Etk.
revert H. unfold PV.after. cbv beta iota. destruct (_ || _); [reflexivity | intros H; exfalso; exact (H eq_refl)].
Qed.
Lemma s31_aft_some_none : forall D w0 w1 tk, Verbs.toks D = w0 :: w1 :: tk ->
PV.after atoi_a (w0 :: w1 :: tk) = None -> vr_aft D = None.
Proof.
intros D w0 w1 tk Etk H. rewrite (s31_aft_toks D ltac:(rewrite Etk; discriminate)), Etk. exact H.
Qed.

Definition s31_pdec : forall u v : Z * Z, {u = v} + {u <> v}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* a word of memory that reads zero *)
Lemma w64_zero_iff : forall x : word, x = w64 0 <-> bv_unsigned x = 0.
Proof.
intros x. split; [intros ->; vm_compute; reflexivity|].
intros H. apply bv_eq. rewrite H. vm_compute. reflexivity.
Qed.

(* lib/Prog/HarnessPropsProof.v:1361 step_frame's call count, from a recorder state that holds no call;
   socket_send keeps the calls, so R2 holds at most two *)
Lemma s31_calls_step : forall (rcode : list byte -> Z) R s, r_calls R = [] ->
(length (r_calls (fst (fst (VerbsRun.run_step rcode R s)))) <= 2)%nat.
Proof.
intros rcode [rf cd cl sp an nr rp st hs] s Hc. cbn in Hc. subst cl.
destruct s as [c0|c|u i p q|u f l v|u| |ln tk]; [|destruct c|..];
  unfold VerbsRun.run_step, VerbsRun.run_call, VerbsRun.pins_follow, sup_add_m, descriptors_get_m,
    descriptors_panel_get_m, sup_remove_m, sup_remove_all_m, sup_worker_list_m, sup_instance_info_m, sup_reset_m,
    sup_quarantine_clear_m, sup_policy_set_m, sup_lv2_worker_set_m, sup_pool_config_m, sup_worker_env_m,
    sup_chain_m, sup_chain_clear_m, sup_pin_accept_m, sup_instance_verb_m, sup_call_m, sup_connect_m,
    sup_broadcast_m, sup_host_setting_m, pins_set_m, pins_clear_m, lv2_refusals_forget_m, descriptors_add_m,
    rec_stub, rec_answer, hand_back, rec_record, rec_mix, rec_mix_host, rec_stub_code, rec_answer_code,
    rec_stub_mix; cbn;
  repeat (match goal with |- context [if ?c then _ else _] => destruct c end; cbn);
  lia.
Qed.
Lemma s31_calls2 : forall R D, r_calls R = [] -> (length (r_calls (vr_R2 R D)) <= 2)%nat.
Proof.
intros R D H. unfold vr_R2, socket_send_m, rec_socket_send, set_reply. cbn [fst r_calls].
unfold vr_R1, vr_h. exact (s31_calls_step reply_code_a R (vr_st D) H).
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
(* the statement's Section hypotheses this segment uses (verbs_receive_c.v:195-245); the program callee in the
   fx-generic form of statement pass 4 *)
Hypothesis TSUP_AFTER_REPLY : forall fx0 : YK11.FPState, @tsup_after_reply_spec fx0 rc SK PI B MT.
Hypothesis STRNCMP : forall fx0 : YK11.FPState, @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
Hypothesis STRCSPN : forall fx0 : YK11.FPState, @RtString.astrcspn_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis AATOI : forall fx0 : YK11.FPState, @RtNumber.aatoi_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
(* the record facts and the interface's named premises *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis SHOK : vr_shadow_ok B.
Hypothesis BLKT : vr_blktail B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let ART := aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL).

(* a state between the runtime calls: vr_ar's state with s8 = tok[0] and the facts Pr about the registers *)
Definition s31_mid (e : vrE) (pc : Z) (Pr : list (list byte) -> list Z -> bvmap 5 word -> Prop)
  : world SEGS -> config -> Prop := fun Wc cf =>
exists O2 pos F q c tp lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc pc) regsc memc mdc /\
(2 <= length (Verbs.toks (e_D e)))%nat /\
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_ar F q c ++ [(24, hd 0 tp)])
  (vr_R2 (e_R e) (e_D e)) O2 (vr_qv e) k (vr_k2 (e_R e) (e_D e)) nm VR_NM_AR lyc Sc Wc regsc memc mdc /\
vr_fresh B e (vr_lb e q) /\ vr_copy B e F c tp Wc memc /\ Pr (Verbs.toks (e_D e)) tp regsc.

Definition Pr1 (tk : list (list byte)) (tp : list Z) (r : bvmap 5 word) : Prop :=
getr r 10 = w64 (Z.of_nat (length (PV.tfirst (hd [] tk)))).
Definition Pr2 (tk : list (list byte)) (tp : list Z) (r : bvmap 5 word) : Prop :=
getr r 10 = w64 0 <-> PV.after atoi_a tk <> None.
Definition Pr3 (tk : list (list byte)) (tp : list Z) (r : bvmap 5 word) : Prop :=
getr r 10 = w64 (atoi_a (nth 1 tk [])) /\ PV.after atoi_a tk <> None.

(* S31 to the return of strcspn, 0x8daf4 .. 0x8db04 *)
Lemma s31_p1 : vr_seg B MT (vr_ar B MT) (fun e => s31_mid e 0x8db08 Pr1).
Proof.
intros e W cf HE HAR.
destruct HAR as (O2 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hnt & HC & HL & HCP).
pose proof HC as (HJ & Hk & HM & Hnm & HFR & HRV & HSV & HSP & HENV & HREC & HnD & HPERM & HQ).
unfold vr_ent in HE. cbv zeta in HE.
destruct HE as (HPRE & HROD & H10 & HOBJ & HFD & HDATA & HN & Hn & HlD & HdIn & HdO & HDb & HTV & HREC0 & Hc0 & Ha0
  & Hr0 & Hnr0 & Hdec & HPERM0 & HQ0 & HGOT0 & HRO0 & HROIN & HVO & HEV0 & HFL0 & HAG0 & Hfr4 & Hnev & Hlive & HMOK
  & Hfrm).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HARj & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HTS : VERBS_RECEIVE_STK = 16992) by (vm_compute; reflexivity).
destruct (K.s1_props e Hal16) as [Hal Hs1].
destruct HCP as [Hcf Hat]. pose proof Hat as (Hmod & Hlen & Hptr & Hstr).
destruct (Verbs.toks (e_D e)) as [|w0 [|w1 tk]] eqn:Etk; [cbn in Hnt; lia | cbn in Hnt; lia |].
destruct tp as [|p0 [|p1 tp']]; cbn [length] in Hlen; [discriminate | discriminate |].
pose proof (Hptr 0%nat p0 eq_refl) as Hp0c. pose proof (Hptr 1%nat p1 eq_refl) as Hp1c.
replace (F + 32 + 8 * Z.of_nat 0) with (F + 32) in Hp0c by lia.
replace (F + 32 + 8 * Z.of_nat 1) with (F + 40) in Hp1c by lia.
destruct (Hstr 0%nat p0 w0 eq_refl eq_refl) as (Hw0 & Hw0l & Hcp0 & Hp0e).
destruct (Hstr 1%nat p1 w1 eq_refl eq_refl) as (Hw1 & Hw1l & Hcp1 & Hp1e).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ eapply Permutation_in; [symmetry; exact HPERM|]. apply in_or_app. right. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc _ _ HARj Hcb) as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct HFR as (EF & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HARj Hin4) as (HF0 & HFc & _).
change (fs_frame_bytes 4) with 1024 in HFc. rewrite <- EF in HF0, HFc.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [_ Hrq].
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 (F + 32)) by (apply (K.vr_rv_get regsc _ _ _ HRV); apply in_or_app; right; cbn; tauto).
set (pc0 := AF_verbs_receive + (0x8daf4 - 0x8d480)).
pose proof (K.s31_seed W regsc memc pc0 F p0 p1 R22 ltac:(lia) ltac:(lia) Hp0c Hp1c ltac:(lia) ltac:(lia)) as HS.
pose proof (K.E31_img regsc p0 p1) as HEI.
unfold cfg_at, w64. change (Z_to_bv 64 (vr_pc 0x8daf4)) with (Z_to_bv 64 (BASE + pc0)).
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
(* the run stored nothing: memory is the boundary's *)
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin; destruct Hin as [Hq | []]; injection Hq as <- <- <-; lia)) as KM0.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a) by (intros a Ha; exact (KM0 a Ha (fun x => x))).
clear KM0 HF HFr HG.
assert (HRV1 : vr_rv (ms_regs ms) (vr_base B e ++ vr_rl_ar F q c)).
{ apply (K.rv_kept _ _ (restrict (w_H W) ms) regsc [w64 p0; w64 p1] _ HS (K.E31_agree regsc p0 p1)); [vm_compute; reflexivity|].
  exact HRV. }
cbn [ms_regs restrict] in HRV1.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (24%bv : bv 5) R24. prreg HS (1%bv : bv 5) R1.
rewrite K.E31_32 in R10, R24.
assert (Hsp1 : spZ (ms_regs ms) = vr_s1 e).
{ unfold spZ. rewrite <- K.getr_Z2, (K.vr_rv_get _ _ 2 (vr_s1 e) HRV1) by (apply in_or_app; left; unfold vr_base; cbn; tauto).
  unfold w64. apply unsigned_lit_small. lia. }
assert (Hgp : getr (ms_regs ms) 3 = w64 (as_gp B)) by (exact (K.vr_rv_get _ _ 3 _ HRV1 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto))).
assert (Htp : getr (ms_regs ms) 4 = w64 (as_tp B)) by (exact (K.vr_rv_get _ _ 4 _ HRV1 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto))).
assert (Hra : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
pmkst HS.
pose proof (proj1 HJ) as HAR1.
assert (KP1 : K.kp W memc (ms_mem ms) (vr_s1 e) (vr_s1 e)) by (intros a Ha _ _; exact (KM a Ha)).
assert (Hev1 : exists ev, rd32 (rdW W (ms_mem ms)) (as_errno B) ev).
{ pose proof HENV as (_ & _ & _ & _ & _ & ev & Hev). exists ev. intros kk Hkk. rewrite (K.s31_errno B HB) in *.
  rewrite KM by lia. exact (Hev kk Hkk). }
destruct (K.env_keep B HB W memc (ms_mem ms) (vr_s1 e) (vr_s1 e) HENV KP1 ltac:(lia) Hev1)
  as (HA1 & HG1 & HR1 & HAG1 & HF1 & HEV1).
pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e)
  (e_mem e) (e_md e) [(4, pos)] lyc Sc W (ms_mem ms) _ k (ms_regs ms) (vr_s1 e - vr_sp0 e) HJ
  ltac:(rewrite Hsp1; lia) Hal ltac:(lia) ltac:(change ESTACK with 4096; lia) ltac:(change ESTACK with 4096; lia)
  Hra Hgp Htp) as HPRE1.
destruct (s31_lits _ HR1) as (L1 & L2 & L3).
unfold vr_cb in Hcb.
eapply SRr_bind.
{ eapply (ART (2 * ESTACK) (fun _ => False) _ W (ms_regs ms) (ms_mem ms) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e)
    (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc _ k (vr_s1 e - vr_sp0 e) _
    (fun regs' _ => getr regs' 10 = w64 (Z.of_nat (PCs.cspn_len [Z_to_bv 8 32; Z_to_bv 8 9] w0))) HJ);
  [ rewrite Hsp1; lia | exact Hal | lia | change ESTACK with 4096; lia | change ESTACK with 4096; lia | exact R1 | intros a [] | ].
  cbn [ss_pc setpc].
  apply (STRCSPN fx lyc Sc W _ _ _ p0 0x224c0 w0 [Z_to_bv 8 32; Z_to_bv 8 9]).
  - exact HAG1.
  - exact HPRE1.
  - rewrite R10. reflexivity.
  - rewrite R11. change 322%nat with (A_OBJ 81).
    apply (K.obj_val _ 81 0x224c0 HEI VOBJS); [apply Nat.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity | cbv; lia].
  - lia.
  - lia.
  - apply astr_atR_view. apply (astr_atR_agree (rdW W memc) _ p0 w0 (Z.of_nat (length w0) + 1) Hw0); [lia|].
    intros kk Hkk. apply KM. lia.
  - apply astr_atR_view. split; [exact L1|].
    intros [Hq | [Hq | []]]; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate Hq.
  - apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) lyc Sc W (ms_regs ms) (ms_mem ms) _ c
      (Z.of_nat (length (Verbs.line (e_D e))) + 1) p0 (astr_len w0 + 1) HAR1 Hcb); unfold astr_len;
      [lia | lia | lia | rewrite Hsp1; change ESTACK with 4096; lia].
  - apply (amem8_of_blockA SEGS B LAWS lyc Sc W (ms_mem ms) _ p0 (astr_len w0) HAR1); [|unfold astr_len; lia].
    exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1). split; [exact Hcb | unfold astr_len; lia].
  - change (astr_len [Z_to_bv 8 32; Z_to_bv 8 9] + 1) with (Z.of_nat (length RO_lit_224c0)).
    apply (K.lit_rd B (2 * ESTACK) W (ms_regs ms) (ms_mem ms) lyc Sc _ 0x224c0 RO_lit_224c0 HAR1 SHOK L1);
      [apply K.in_shr_chk; vm_compute; reflexivity | lia | cbn; lia | rewrite Hsp1; change ESTACK with 4096; lia | cbn; lia].
  - apply amem8_of_low; [lia | change (astr_len [Z_to_bv 8 32; Z_to_bv 8 9]) with 2; unfold kLowMemEnd; lia].
  - apply (BLKT lyc Sc W (ms_mem ms) _ c (Z.of_nat (length (Verbs.line (e_D e))) + 1) (p0 + astr_len w0) HAR1 Hcb).
    unfold astr_len. lia.
  - change (0x224c0 + astr_len [Z_to_bv 8 32; Z_to_bv 8 9]) with 0x224c2. apply K.tail_lit; [exact HR1 | vm_compute; reflexivity].
  - apply vr_rtrom_ok. exact HA1. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HFR2').
pose proof (fun a Ha Hn => HFR2' a Ha Hn (fun x : False => x)) as HFR2. clear HFR2'.
change [Z_to_bv 8 32; Z_to_bv 8 9] with (map (Z_to_bv 8) [32; 9]) in HQ2. rewrite PVF.cspn_tfirst in HQ2.
change ESTACK with 4096 in HFR2.
assert (KP2 : K.kp W memc mem2 (vr_s1 e - 2 * 4096) (vr_s1 e)).
{ intros a Ha Hw He. rewrite HFR2 by lia. apply KM. exact Ha. }
apply SRr_ret.
exists O2, pos, F, q, c, (p0 :: p1 :: tp'), lyc, Sc, regs2, mem2, md2, k, nm.
split; [unfold cfg_at, w64; replace (vr_pc 0x8db08) with (BASE + 30244) by (unfold vr_pc; rewrite AFV; lia); reflexivity|].
split; [rewrite Etk; cbn; lia|].
split.
{ eapply (K.core_keep B MT HB) with (lo := vr_s1 e - 2 * 4096) (hi := vr_s1 e); [exact HC | exact HJ2 | exact KP2 | lia | lia | | | ].
  - destruct HEV1 as (ev & Hev). exists ev. intros kk Hkk. rewrite (K.s31_errno B HB) in Hev |- *. rewrite HFR2 by lia. exact (Hev kk Hkk).
  - apply (K.vr_rv_pres (ms_regs ms) regs2 _ HP2).
    + unfold vr_base, vr_rl_ar. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
    + rewrite app_assoc. apply K.vr_rv_app. split; [exact HRV1|]. constructor; [exact R24 | constructor].
  - unfold vr_sl3. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
split; [exact (proj1 HL)|].
split.
{ rewrite <- Etk in Hat. apply (K.copy_keep B e F c (p0 :: p1 :: tp') lyc Sc W memc mdc mem2 (vr_s1 e - 2 * 4096) (vr_s1 e) pos k).
  - exact (proj1 HC).
  - exact EF.
  - exact Hcb.
  - split; [exact Hcf | exact Hat].
  - exact KP2.
  - lia. }
unfold Pr1. rewrite Etk. exact HQ2.
Qed.

(* the strncmp call on tok[0] against one of the two formats: from the state at the entry of the wrapper, to the
   return 0x8db3c with the answer *)
Lemma s31_ncmp : forall e (W : world SEGS) O2 pos F q c tp lyc Sc regsc memc mdc k nm w0 w1 tk p0 lit (fmt : list byte) n,
vr_ent B MT e ->
Verbs.toks (e_D e) = w0 :: w1 :: tk ->
(* tp holds the words of the line, so its first entry is the word tok[0] *)
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_ar F q c ++ [(24, hd 0 tp)])
  (vr_R2 (e_R e) (e_D e)) O2 (vr_qv e) k (vr_k2 (e_R e) (e_D e)) nm VR_NM_AR lyc Sc W regsc memc mdc ->
vr_fresh B e (vr_lb e q) -> vr_copy B e F c tp W memc ->
nth_error tp 0 = Some p0 ->
getr regsc 10 = w64 p0 -> getr regsc 11 = w64 lit -> getr regsc 12 = w64 n ->
getr regsc 1 = Z_to_bv 64 (BASE + 30296) ->
getr regsc 2 = w64 (vr_s1 e) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
vr_rv regsc (vr_base B e ++ vr_rl_ar F q c ++ [(24, hd 0 tp)]) ->
abytes_atR (rdW W memc) lit (fmt ++ [Z_to_bv 8 0]) -> In (lit, Z.of_nat (length fmt) + 1) vr_shr ->
existsb (Z.eqb (lit + Z.of_nat (length fmt))) cmd_ro_ends = true ->
0 < lit -> lit + Z.of_nat (length fmt) + 1 <= 0x606000 ->
Forall (fun b => bv_unsigned b <> 0) fmt ->
length (PV.tfirst w0) = length (PV.vfirst fmt) ->
n = Z.of_nat (length (PV.vfirst fmt)) -> 0 < n < 2 ^ 32 ->
(PV.after atoi_a (w0 :: w1 :: tk) <> None <-> PV.verb_is_m w0 fmt = true) ->
SRr SEGS W (cfg_at SEGS (SIGMA CS___interceptor_trampoline_strncmp) regsc memc mdc)
  (s31_mid e 0x8db3c Pr2).
Proof.
intros e W O2 pos F q c tp lyc Sc regsc memc mdc k nm w0 w1 tk p0 lit fmt n
  HE Etk HC HL HCP Hp0 R10 R11 R12 R1 R2 R3 R4 HRV Hlit Hshr Hend Hlit0 Hlit6 Hnzf Hlenf -> Hn Haft.
pose proof HC as (HJ & Hk & HM & Hnm & HFR & _ & HSV & HSP & HENV & HREC & HnD & HPERM & HQ).
pose proof HE as HE'. unfold vr_ent in HE'. cbv zeta in HE'.
destruct HE' as (HPRE & HROD & _ & _ & _ & _ & _ & Hn8 & HlD & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HARj & Hly & _ & _ & _ & Hfrs & _).
destruct (K.s1_props e Hal16) as [Hal Hs1].
assert (HTS : VERBS_RECEIVE_STK = 16992) by (vm_compute; reflexivity).
destruct HCP as [Hcf Hat]. pose proof Hat as (Hmod & Hlen & Hptr & Hstr).
destruct (Hstr 0%nat p0 w0 Hp0 ltac:(rewrite Etk; reflexivity)) as (Hw0 & Hw0l & Hcp0 & Hp0e).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ eapply Permutation_in; [symmetry; exact HPERM|]. apply in_or_app. right. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc _ _ HARj Hcb) as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn).
unfold vr_cb in Hcb, Hc4096, Hcc, Hcn. cbn [fst snd] in Hc4096, Hcc, Hcn.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [_ Hrq].
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct HFR as (EF & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HARj Hin4) as (HF0 & HFc & _).
change (fs_frame_bytes 4) with 1024 in HFc. rewrite <- EF in HF0, HFc.
pose proof HENV as (HA1 & HG1 & HR1 & HAG1 & HF1 & (ev0 & HEV1)).
assert (Hsp1 : spZ regsc = vr_sp0 e + (vr_s1 e - vr_sp0 e))
  by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hra : YK0s.ret_ok (getr regsc 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e)
  (e_mem e) (e_md e) [(4, pos)] lyc Sc W memc mdc k regsc (vr_s1 e - vr_sp0 e) HJ Hsp1 Hal
  ltac:(lia) ltac:(change ESTACK with 4096; lia) ltac:(change ESTACK with 4096; lia) Hra R3 R4) as HPRE1.
eapply SRr_bind.
{ eapply (ART (2 * ESTACK) (fun _ => False) _ W regsc memc VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e)
    (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdc k (vr_s1 e - vr_sp0 e) _
    (fun regs' _ => getr regs' 10 = w64 0 <->
       PSn.strncmp_model (w0 ++ [Z_to_bv 8 0]) (fmt ++ [Z_to_bv 8 0]) (Z.of_nat (length (PV.vfirst fmt))) = Some 0) HJ);
  [ exact Hsp1 | exact Hal | lia | change ESTACK with 4096; lia | change ESTACK with 4096; lia | exact R1 | intros a [] | ].
  apply (STRNCMP fx lyc Sc W regsc memc mdc p0 lit (Z.of_nat (length (PV.vfirst fmt))) w0 fmt HPRE1 R10 R11 R12
    ltac:(lia)
    ltac:(lia) ltac:(lia)).
  - apply astr_atR_view. exact Hw0.
  - apply astr_atR_view. split; [exact Hlit | exact (notin_of_nz _ Hnzf)].
  - apply (K.aread_ok_sub (2 * ESTACK) W regsc memc p0 (astr_len w0 + 1)).
    + apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) lyc Sc W regsc memc mdc c
        (Z.of_nat (length (Verbs.line (e_D e))) + 1) p0 (astr_len w0 + 1) HARj Hcb); unfold astr_len;
        [lia | lia | lia | rewrite Hsp1; change ESTACK with 4096; lia].
    + unfold astr_len. pose proof (PVF.upto_length PV.is_sep w0) as Hu. unfold PV.tfirst in Hlenf.
      rewrite Z.min_l by lia. lia.
  - apply (amem8_of_blockA SEGS B LAWS lyc Sc W memc mdc p0 (astr_len w0) HARj); [|unfold astr_len; lia].
    exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1). split; [exact Hcb | unfold astr_len; lia].
  - apply (K.aread_ok_sub (2 * ESTACK) W regsc memc lit (Z.of_nat (length fmt) + 1)).
    + replace (Z.of_nat (length fmt) + 1) with (Z.of_nat (length (fmt ++ [Z_to_bv 8 0])))
        by (rewrite length_app; cbn [length]; lia).
      apply (K.lit_rd B (2 * ESTACK) W regsc memc lyc Sc mdc lit (fmt ++ [Z_to_bv 8 0]) HARj SHOK Hlit);
        [rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; exact Hshr | lia
        | rewrite length_app; cbn [length]; lia | rewrite Hsp1; change ESTACK with 4096; lia
        | rewrite length_app; cbn [length]; lia].
    + unfold astr_len. pose proof (PVF.upto_length (fun b => bv_unsigned b =? 32) fmt) as Hv. unfold PV.vfirst in *.
      rewrite Z.min_l by lia. lia.
  - apply amem8_of_low; unfold astr_len, kLowMemEnd; lia.
  - unfold astr_len. apply (BLKT lyc Sc W memc mdc c (Z.of_nat (length (Verbs.line (e_D e))) + 1) (p0 + Z.of_nat (length w0)) HARj Hcb).
    lia.
  - unfold astr_len. apply K.tail_lit; [exact HR1 | exact Hend].
  - apply vr_rtrom_ok. exact HA1. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HFR2').
pose proof (fun a Ha Hn' => HFR2' a Ha Hn' (fun x : False => x)) as HFR2. clear HFR2'.
change ESTACK with 4096 in HFR2.
assert (KP2 : K.kp W memc mem2 (vr_s1 e - 2 * 4096) (vr_s1 e)).
{ intros a Ha Hw He. apply HFR2; lia. }
apply SRr_ret.
exists O2, pos, F, q, c, tp, lyc, Sc, regs2, mem2, md2, k, nm.
split; [unfold cfg_at, w64; replace (vr_pc 0x8db3c) with (BASE + 30296) by (unfold vr_pc; rewrite AFV; lia); reflexivity|].
split; [rewrite Etk; cbn; lia|].
split.
{ eapply (K.core_keep B MT HB) with (lo := vr_s1 e - 2 * 4096) (hi := vr_s1 e); [exact HC | exact HJ2 | exact KP2 | lia | lia | | | ].
  - exists ev0. intros kk Hkk. rewrite (K.s31_errno B HB) in HEV1 |- *. rewrite HFR2 by lia. exact (HEV1 kk Hkk).
  - apply (K.vr_rv_pres regsc regs2 _ HP2); [|exact HRV].
    unfold vr_base, vr_rl_ar. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
  - unfold vr_sl3. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
split; [exact HL|].
split.
{ apply (K.copy_keep B e F c tp lyc Sc W memc mdc mem2 (vr_s1 e - 2 * 4096) (vr_s1 e) pos k).
  - exact HJ.
  - exact EF.
  - exact Hcb.
  - split; [exact Hcf | exact Hat].
  - exact KP2.
  - lia. }
(* the answer: strncmp is zero exactly when the word is the verb of the format *)
unfold Pr2. rewrite Etk.
assert (Hnz0 : Forall (fun b => bv_unsigned b <> 0) w0) by (apply nz_of_notin; exact (proj2 Hw0)).
destruct (PVF.strncmp_verb w0 fmt [] Hnz0 Hnzf Hlenf) as (v & Hv & Hvr & Hvq).
rewrite Hv in HQ2.
rewrite Haft. rewrite <- Hvq. rewrite HQ2. split.
- intros Hq. injection Hq as <-. apply Z.eqb_refl.
- intros Hq. apply Z.eqb_eq in Hq. rewrite Hq. reflexivity.
Qed.

(* the strncmp call at each of the two formats *)
Lemma s31_ncmp_ps : forall e (W : world SEGS) O2 pos F q c tp lyc Sc regsc memc mdc k nm w0 w1 tk p0,
vr_ent B MT e -> Verbs.toks (e_D e) = w0 :: w1 :: tk ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_ar F q c ++ [(24, hd 0 tp)])
  (vr_R2 (e_R e) (e_D e)) O2 (vr_qv e) k (vr_k2 (e_R e) (e_D e)) nm VR_NM_AR lyc Sc W regsc memc mdc ->
vr_fresh B e (vr_lb e q) -> vr_copy B e F c tp W memc ->
nth_error tp 0 = Some p0 ->
getr regsc 10 = w64 p0 -> getr regsc 11 = w64 0x22520 -> getr regsc 12 = w64 9 ->
getr regsc 1 = Z_to_bv 64 (BASE + 30296) ->
getr regsc 2 = w64 (vr_s1 e) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
vr_rv regsc (vr_base B e ++ vr_rl_ar F q c ++ [(24, hd 0 tp)]) ->
cmd_ro_ok (rdW W memc) -> length (PV.tfirst w0) = 9%nat ->
SRr SEGS W (cfg_at SEGS (SIGMA CS___interceptor_trampoline_strncmp) regsc memc mdc) (s31_mid e 0x8db3c Pr2).
Proof.
intros e W O2 pos F q c tp lyc Sc regsc memc mdc k nm w0 w1 tk p0
  HE Etk HC HL HCP Hp0 R10 R11 R12 R1 R2 R3 R4 HRV Hro Hl9.
destruct (s31_lits _ Hro) as (_ & _ & L3).
apply (s31_ncmp e W O2 pos F q c tp lyc Sc regsc memc mdc k nm w0 w1 tk p0 0x22520 PV.Lit.fmt_patch_set 9
  HE Etk HC HL HCP Hp0 R10 R11 R12 R1 R2 R3 R4 HRV).
- exact L3.
- apply K.in_shr_chk. vm_compute. reflexivity.
- vm_compute. reflexivity.
- lia.
- rewrite s31_len_ps. lia.
- apply nz_of_forallb. vm_compute. reflexivity.
- rewrite s31_vf_ps. exact Hl9.
- rewrite s31_vf_ps. reflexivity.
- change (2 ^ 32) with 4294967296. lia.
- apply s31_aft_ps. exact Hl9.
Qed.

Lemma s31_ncmp_pl : forall e (W : world SEGS) O2 pos F q c tp lyc Sc regsc memc mdc k nm w0 w1 tk p0,
vr_ent B MT e -> Verbs.toks (e_D e) = w0 :: w1 :: tk ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_ar F q c ++ [(24, hd 0 tp)])
  (vr_R2 (e_R e) (e_D e)) O2 (vr_qv e) k (vr_k2 (e_R e) (e_D e)) nm VR_NM_AR lyc Sc W regsc memc mdc ->
vr_fresh B e (vr_lb e q) -> vr_copy B e F c tp W memc ->
nth_error tp 0 = Some p0 ->
getr regsc 10 = w64 p0 -> getr regsc 11 = w64 0x224e0 -> getr regsc 12 = w64 11 ->
getr regsc 1 = Z_to_bv 64 (BASE + 30296) ->
getr regsc 2 = w64 (vr_s1 e) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
vr_rv regsc (vr_base B e ++ vr_rl_ar F q c ++ [(24, hd 0 tp)]) ->
cmd_ro_ok (rdW W memc) -> length (PV.tfirst w0) = 11%nat ->
SRr SEGS W (cfg_at SEGS (SIGMA CS___interceptor_trampoline_strncmp) regsc memc mdc) (s31_mid e 0x8db3c Pr2).
Proof.
intros e W O2 pos F q c tp lyc Sc regsc memc mdc k nm w0 w1 tk p0
  HE Etk HC HL HCP Hp0 R10 R11 R12 R1 R2 R3 R4 HRV Hro Hl11.
destruct (s31_lits _ Hro) as (_ & L2 & _).
apply (s31_ncmp e W O2 pos F q c tp lyc Sc regsc memc mdc k nm w0 w1 tk p0 0x224e0 PV.Lit.fmt_preset_load 11
  HE Etk HC HL HCP Hp0 R10 R11 R12 R1 R2 R3 R4 HRV).
- exact L2.
- apply K.in_shr_chk. vm_compute. reflexivity.
- vm_compute. reflexivity.
- lia.
- rewrite s31_len_pl. lia.
- apply nz_of_forallb. vm_compute. reflexivity.
- rewrite s31_vf_pl. exact Hl11.
- rewrite s31_vf_pl. reflexivity.
- change (2 ^ 32) with 4294967296. lia.
- apply s31_aft_pl. exact Hl11.
Qed.

(* 0x8db08 .. 0x8db38: the two tests of the length of the first word, and the strncmp of the format each one picks;
   a length that is neither 9 nor 11 leaves for 0x8db50 with no call after the reply *)
Lemma s31_p2 : vr_seg B MT (fun e => s31_mid e 0x8db08 Pr1) (vr_or (vr_af B MT) (fun e => s31_mid e 0x8db3c Pr2)).
Proof.
intros e W cf HE HM.
destruct HM as (O2 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hnt & HC & HL & HCP & HPr).
pose proof HC as (HJ & Hk & HMe & Hnm & HFR & HRV & HSV & HSP & HENV & HREC & HnD & HPERM & HQ).
pose proof HE as HE'. unfold vr_ent in HE'. cbv zeta in HE'.
destruct HE' as (HPRE & HROD & _ & _ & _ & _ & _ & Hn8 & HlD & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HARj & Hly & _ & _ & _ & Hfrs & _).
destruct (K.s1_props e Hal16) as [Hal Hs1].
assert (HTS : VERBS_RECEIVE_STK = 16992) by (vm_compute; reflexivity).
destruct HCP as [Hcf Hat]. pose proof Hat as (Hmod & Hlen & Hptr & Hstr).
destruct (Verbs.toks (e_D e)) as [|w0 [|w1 tk]] eqn:Etk; [cbn in Hnt; lia | cbn in Hnt; lia |].
destruct tp as [|p0 [|p1 tp']]; cbn [length] in Hlen; [discriminate | discriminate |].
pose proof (Hptr 0%nat p0 eq_refl) as Hp0c. pose proof (Hptr 1%nat p1 eq_refl) as Hp1c.
replace (F + 32 + 8 * Z.of_nat 0) with (F + 32) in Hp0c by lia.
replace (F + 32 + 8 * Z.of_nat 1) with (F + 40) in Hp1c by lia.
destruct (Hstr 0%nat p0 w0 eq_refl eq_refl) as (Hw0 & Hw0l & Hcp0 & Hp0e).
destruct (Hstr 1%nat p1 w1 eq_refl eq_refl) as (Hw1 & Hw1l & Hcp1 & Hp1e).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ eapply Permutation_in; [symmetry; exact HPERM|]. apply in_or_app. right. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc _ _ HARj Hcb) as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn).
unfold vr_cb in Hcb, Hc4096, Hcc, Hcn. cbn [fst snd] in Hc4096, Hcc, Hcn.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct HFR as (EF & Hfw & Hfs).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HARj Hin4) as (HF0 & HFc & _).
change (fs_frame_bytes 4) with 1024 in HFc. rewrite <- EF in HF0, HFc.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [_ Hrq].
pose proof HENV as (HA1 & HG1 & HR1 & HAG1 & HFl1 & (ev0 & HEV1)).
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 (F + 32))
  by (apply (K.vr_rv_get regsc _ _ _ HRV); apply in_or_app; right; apply in_or_app; left; cbn; tauto).
assert (R24 : getr regsc (Z_to_bv 5 24) = w64 p0)
  by (apply (K.vr_rv_get regsc _ _ _ HRV); apply in_or_app; right; apply in_or_app; right; cbn; tauto).
assert (R2 : getr regsc (Z_to_bv 5 2) = w64 (vr_s1 e))
  by (apply (K.vr_rv_get regsc _ _ _ HRV); apply in_or_app; left; unfold vr_base; cbn; tauto).
assert (R3 : getr regsc (Z_to_bv 5 3) = w64 (as_gp B))
  by (apply (K.vr_rv_get regsc _ _ _ HRV); apply in_or_app; left; unfold vr_base; cbn; tauto).
assert (R4 : getr regsc (Z_to_bv 5 4) = w64 (as_tp B))
  by (apply (K.vr_rv_get regsc _ _ _ HRV); apply in_or_app; left; unfold vr_base; cbn; tauto).
unfold Pr1 in HPr. cbn [hd] in HPr.
rewrite <- Etk in Hat.
set (L0 := Z.of_nat (length (PV.tfirst w0))) in *.
assert (HL0 : 0 <= L0 <= Z.of_nat (length w0)).
{ unfold L0, PV.tfirst. pose proof (PVF.upto_length PV.is_sep w0). lia. }
pose proof (K.s31_seed W regsc memc 30244 F p0 p1 R22 ltac:(lia) ltac:(lia) Hp0c Hp1c ltac:(lia) ltac:(lia)) as HS.
pose proof (K.E31_img regsc p0 p1) as HEI.
assert (E10 : ew (K.E31 regsc p0 p1) 10 = Z_to_bv 64 L0)
  by (rewrite (K.E31_reg regsc p0 p1 10%nat (10%bv) ltac:(vm_compute; reflexivity)); exact HPr).
assert (E24 : ew (K.E31 regsc p0 p1) 24 = Z_to_bv 64 p0)
  by (rewrite (K.E31_reg regsc p0 p1 24%nat (24%bv) ltac:(vm_compute; reflexivity)); exact R24).
unfold cfg_at, w64.
replace (Z_to_bv 64 (vr_pc 0x8db08)) with (Z_to_bv 64 (BASE + 30244)) by (unfold vr_pc; rewrite AFV; do 2 f_equal; lia).
paj_run_sh RUNP HS HJ.
{ awr_ok_tac. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
cbn [ms_mem mkst] in HFr.
pose proof (K.rdeq_of_frame _ _ _ _ _ HFr (K.ro_ss31 30244)) as Eq1. clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- (* 0x8db0c beq a0,9: the word is nine bytes long, the format is patch_set *)
  rewrite branch_eq_U in Hc. rewrite (U_atom _ 10 L0 E10 ltac:(lia)) in Hc.
  rewrite (U_lit _ 9 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
  paj_run_shc RUNP RUNC HS HJ.
  { awr_ok_tac. }
  match goal with |- context [with_vm_backing (m_vm_lazy mdv) ?mt mdv] =>
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mt mdv) in * end.
  clearbody mdv2.
  cbn [ms_mem mkst] in HFr.
  pose proof (K.rdeq_of_frame _ _ _ _ _ HFr (K.ro_ss31 30244)) as Eq2. clear HF HFr HG.
  pose proof (fun x => eq_trans (Eq2 x) (Eq1 x)) as Eq.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
  pose proof (K.rv_kept _ _ (restrict (w_H W) ms0) regsc [w64 p0; w64 p1]
    (vr_base B e ++ vr_rl_ar F q c ++ [(24, hd 0 (p0 :: p1 :: tp'))]) HS (K.E31_agree regsc p0 p1)
    ltac:(vm_compute; reflexivity) HRV) as HRV2.
  cbn [ms_regs restrict] in HRV2.
  pmkst HS.
  assert (HC2 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
      (vr_rl_ar F q c ++ [(24, hd 0 (p0 :: p1 :: tp'))]) (vr_R2 (e_R e) (e_D e)) O2 (vr_qv e) k
      (vr_k2 (e_R e) (e_D e)) nm VR_NM_AR lyc Sc W (ms_regs ms0) (ms_mem ms0) mdv2).
  { eapply (K.core_keep B MT HB) with (lo := vr_s1 e) (hi := vr_s1 e);
      [exact HC | exact HJ | intros a Ha _ _; exact (Eq a) | lia | lia | | exact HRV2 | ].
    - exists ev0. intros kk Hkk. rewrite (K.s31_errno B HB) in HEV1 |- *. rewrite Eq. exact (HEV1 kk Hkk).
    - unfold vr_sl3. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
  assert (HCP2 : vr_copy B e F c (p0 :: p1 :: tp') W (ms_mem ms0))
    by (apply (K.copy_keep B e F c (p0 :: p1 :: tp') lyc Sc W memc mdc (ms_mem ms0) (vr_s1 e) (vr_s1 e) pos k);
        [exact (proj1 HC) | exact EF | exact Hcb | split; [exact Hcf | exact Hat] | intros a Ha _ _; exact (Eq a) | lia]).
  assert (Q10' : getr (ms_regs ms0) 10 = w64 p0) by (rewrite Q10, E24; reflexivity).
  assert (Q11' : getr (ms_regs ms0) 11 = w64 0x22520).
  { rewrite Q11. change 345%nat with (A_OBJ 104).
    apply (K.obj_val _ 104 0x22520 HEI VOBJS);
      [apply Nat.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity | cbv; lia]. }
  assert (Q2' : getr (ms_regs ms0) 2 = w64 (vr_s1 e))
    by exact (K.vr_rv_get _ _ 2 _ HRV2 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto)).
  assert (Q3' : getr (ms_regs ms0) 3 = w64 (as_gp B))
    by exact (K.vr_rv_get _ _ 3 _ HRV2 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto)).
  assert (Q4' : getr (ms_regs ms0) 4 = w64 (as_tp B))
    by exact (K.vr_rv_get _ _ 4 _ HRV2 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto)).
  assert (HRO2 : cmd_ro_ok (rdW W (ms_mem ms0))) by (apply (K.cmd_ro_ok_keep _ _ HR1); intros a _; exact (Eq a)).
  assert (Hl9 : length (PV.tfirst w0) = 9%nat) by (unfold L0 in Hc; lia).
  eapply SRr_mono.
  { exact (s31_ncmp_ps e W O2 pos F q c (p0 :: p1 :: tp') lyc Sc (ms_regs ms0) (ms_mem ms0) mdv2 k nm w0 w1 tk p0
      HE Etk HC2 HL HCP2 eq_refl Q10' Q11' Q12 Q1 Q2' Q3' Q4' HRV2 HRO2 Hl9). }
  cbv beta. intros W' c' _ H. right. exact H.
- (* not nine bytes: 0x8db10 li a1,11; 0x8db14 bne a0,11 *)
  rewrite branch_eq_U in Hc. rewrite (U_atom _ 10 L0 E10 ltac:(lia)) in Hc.
  rewrite (U_lit _ 9 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
  paj_run_sh RUNP HS HJ.
  { awr_ok_tac. }
  match goal with |- context [with_vm_backing (m_vm_lazy mdv) ?mt mdv] =>
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mt mdv) in * end.
  clearbody mdv2.
  cbn [ms_mem mkst] in HFr.
  pose proof (K.rdeq_of_frame _ _ _ _ _ HFr (K.ro_ss31 30244)) as Eq2. clear HF HFr HG.
  pose proof (fun x => eq_trans (Eq2 x) (Eq1 x)) as Eq.
  psrr_branch_pi RUNP BR HS.
  + (* neither nine nor eleven: no call after the reply, the run reaches 0x8db50 *)
    rewrite branch_ne_U in Hc0. rewrite (U_atom _ 10 L0 E10 ltac:(lia)) in Hc0.
    rewrite (U_lit _ 11 ltac:(lia)) in Hc0. apply negb_true_iff, Z.eqb_neq in Hc0.
    paj_run_to_shc RUNTOP HS HJ 30316.
    { awr_ok_tac. }
    match goal with |- context [with_vm_backing (m_vm_lazy mdv2) ?mt mdv2] =>
      set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mt mdv2) in * end.
    clearbody mdv3.
    cbn [ms_mem mkst] in HFr.
    pose proof (K.rdeq_of_frame _ _ _ _ _ HFr (K.ro_ss31 30244)) as Eq3. clear HF HFr HG.
    pose proof (fun x => eq_trans (Eq3 x) (Eq x)) as Eqf.
    pose proof (K.rv_kept _ _ (restrict (w_H W) ms1) regsc [w64 p0; w64 p1]
      (vr_base B e ++ vr_rl_ar F q c ++ [(24, hd 0 (p0 :: p1 :: tp'))]) HS (K.E31_agree regsc p0 p1)
      ltac:(vm_compute; reflexivity) HRV) as HRV2.
    cbn [ms_regs restrict hd] in HRV2.
    pmkst HS.
    assert (HC2 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
        (vr_rl_ar F q c ++ [(24, p0)]) (vr_R2 (e_R e) (e_D e)) O2 (vr_qv e) k
        (vr_k2 (e_R e) (e_D e)) nm VR_NM_AR lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv3).
    { eapply (K.core_keep B MT HB) with (lo := vr_s1 e) (hi := vr_s1 e);
        [exact HC | exact HJ | intros a Ha _ _; exact (Eqf a) | lia | lia | | exact HRV2 | ].
      - exists ev0. intros kk Hkk. rewrite (K.s31_errno B HB) in HEV1 |- *. rewrite Eqf. exact (HEV1 kk Hkk).
      - unfold vr_sl3. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
    assert (Haf : vr_aft (e_D e) = None)
      by exact (s31_aft_none (e_D e) w0 w1 tk Etk ltac:(unfold L0 in Hc; lia) ltac:(unfold L0 in Hc0; lia)).
    apply SRr_ret. left.
    replace (BASE + 30316) with (vr_pc 0x8db50) by (unfold vr_pc; rewrite AFV; lia).
    exact (K.s31_to_af B MT e O2 pos F q c lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv3 k nm [(24, p0)] Haf HC2 HL Hcf).
  + (* eleven bytes: the format is preset_load *)
    rewrite branch_ne_U in Hc0. rewrite (U_atom _ 10 L0 E10 ltac:(lia)) in Hc0.
    rewrite (U_lit _ 11 ltac:(lia)) in Hc0. apply negb_false_iff, Z.eqb_eq in Hc0.
    paj_run_shc RUNP RUNC HS HJ.
    { awr_ok_tac. }
    match goal with |- context [with_vm_backing (m_vm_lazy mdv2) ?mt mdv2] =>
      set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mt mdv2) in * end.
    clearbody mdv3.
    cbn [ms_mem mkst] in HFr.
    pose proof (K.rdeq_of_frame _ _ _ _ _ HFr (K.ro_ss31 30244)) as Eq3. clear HF HFr HG.
    pose proof (fun x => eq_trans (Eq3 x) (Eq x)) as Eqf.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
    pose proof (K.rv_kept _ _ (restrict (w_H W) ms1) regsc [w64 p0; w64 p1]
      (vr_base B e ++ vr_rl_ar F q c ++ [(24, hd 0 (p0 :: p1 :: tp'))]) HS (K.E31_agree regsc p0 p1)
      ltac:(vm_compute; reflexivity) HRV) as HRV2.
    cbn [ms_regs restrict] in HRV2.
    pmkst HS.
    assert (HC2 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
        (vr_rl_ar F q c ++ [(24, hd 0 (p0 :: p1 :: tp'))]) (vr_R2 (e_R e) (e_D e)) O2 (vr_qv e) k
        (vr_k2 (e_R e) (e_D e)) nm VR_NM_AR lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv3).
    { eapply (K.core_keep B MT HB) with (lo := vr_s1 e) (hi := vr_s1 e);
        [exact HC | exact HJ | intros a Ha _ _; exact (Eqf a) | lia | lia | | exact HRV2 | ].
      - exists ev0. intros kk Hkk. rewrite (K.s31_errno B HB) in HEV1 |- *. rewrite Eqf. exact (HEV1 kk Hkk).
      - unfold vr_sl3. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
    assert (HCP2 : vr_copy B e F c (p0 :: p1 :: tp') W (ms_mem ms1))
      by (apply (K.copy_keep B e F c (p0 :: p1 :: tp') lyc Sc W memc mdc (ms_mem ms1) (vr_s1 e) (vr_s1 e) pos k);
          [exact (proj1 HC) | exact EF | exact Hcb | split; [exact Hcf | exact Hat] | intros a Ha _ _; exact (Eqf a) | lia]).
    assert (Q10' : getr (ms_regs ms1) 10 = w64 p0) by (rewrite Q10, E24; reflexivity).
    assert (Q11' : getr (ms_regs ms1) 11 = w64 0x224e0).
    { rewrite Q11. change 344%nat with (A_OBJ 103).
      apply (K.obj_val _ 103 0x224e0 HEI VOBJS);
        [apply Nat.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity | cbv; lia]. }
    assert (Q2' : getr (ms_regs ms1) 2 = w64 (vr_s1 e))
      by exact (K.vr_rv_get _ _ 2 _ HRV2 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto)).
    assert (Q3' : getr (ms_regs ms1) 3 = w64 (as_gp B))
      by exact (K.vr_rv_get _ _ 3 _ HRV2 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto)).
    assert (Q4' : getr (ms_regs ms1) 4 = w64 (as_tp B))
      by exact (K.vr_rv_get _ _ 4 _ HRV2 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto)).
    assert (HRO2 : cmd_ro_ok (rdW W (ms_mem ms1))) by (apply (K.cmd_ro_ok_keep _ _ HR1); intros a _; exact (Eqf a)).
    assert (Hl11 : length (PV.tfirst w0) = 11%nat) by (unfold L0 in Hc0; lia).
    eapply SRr_mono.
    { exact (s31_ncmp_pl e W O2 pos F q c (p0 :: p1 :: tp') lyc Sc (ms_regs ms1) (ms_mem ms1) mdv3 k nm w0 w1 tk p0
        HE Etk HC2 HL HCP2 eq_refl Q10' Q11' Q12 Q1 Q2' Q3' Q4' HRV2 HRO2 Hl11). }
    cbv beta. intros W' c' _ H. right. exact H.
Qed.

(* 0x8db3c .. 0x8db44: a nonzero answer of strncmp leaves for 0x8db50 with no call after the reply; a zero answer
   loads tok[1] and takes the atoi wrapper on it *)
Lemma s31_p3 : vr_seg B MT (fun e => s31_mid e 0x8db3c Pr2) (vr_or (vr_af B MT) (fun e => s31_mid e 0x8db48 Pr3)).
Proof.
intros e W cf HE HM.
destruct HM as (O2 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hnt & HC & HL & HCP & HPr).
pose proof HC as (HJ & Hk & HMe & Hnm & HFR & HRV & HSV & HSP & HENV & HREC & HnD & HPERM & HQ).
pose proof HE as HE'. unfold vr_ent in HE'. cbv zeta in HE'.
destruct HE' as (HPRE & HROD & _ & _ & _ & _ & _ & Hn8 & HlD & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HARj & Hly & _ & _ & _ & Hfrs & _).
destruct (K.s1_props e Hal16) as [Hal Hs1].
assert (HTS : VERBS_RECEIVE_STK = 16992) by (vm_compute; reflexivity).
destruct HCP as [Hcf Hat]. pose proof Hat as (Hmod & Hlen & Hptr & Hstr).
destruct (Verbs.toks (e_D e)) as [|w0 [|w1 tk]] eqn:Etk; [cbn in Hnt; lia | cbn in Hnt; lia |].
destruct tp as [|p0 [|p1 tp']]; cbn [length] in Hlen; [discriminate | discriminate |].
pose proof (Hptr 0%nat p0 eq_refl) as Hp0c. pose proof (Hptr 1%nat p1 eq_refl) as Hp1c.
replace (F + 32 + 8 * Z.of_nat 0) with (F + 32) in Hp0c by lia.
replace (F + 32 + 8 * Z.of_nat 1) with (F + 40) in Hp1c by lia.
destruct (Hstr 0%nat p0 w0 eq_refl eq_refl) as (Hw0 & Hw0l & Hcp0 & Hp0e).
destruct (Hstr 1%nat p1 w1 eq_refl eq_refl) as (Hw1 & Hw1l & Hcp1 & Hp1e).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ eapply Permutation_in; [symmetry; exact HPERM|]. apply in_or_app. right. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc _ _ HARj Hcb) as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn).
unfold vr_cb in Hcb, Hc4096, Hcc, Hcn. cbn [fst snd] in Hc4096, Hcc, Hcn.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct HFR as (EF & Hfw & Hfs).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HARj Hin4) as (HF0 & HFc & _).
change (fs_frame_bytes 4) with 1024 in HFc. rewrite <- EF in HF0, HFc.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [_ Hrq].
pose proof HENV as (HA1 & HG1 & HR1 & HAG1 & HFl1 & (ev0 & HEV1)).
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 (F + 32))
  by (apply (K.vr_rv_get regsc _ _ _ HRV); apply in_or_app; right; apply in_or_app; left; cbn; tauto).
rewrite <- Etk in Hat.
set (av := bv_unsigned (getr regsc 10)).
assert (Hav : 0 <= av < 2 ^ 64).
{ unfold av. pose proof (bv_unsigned_in_range 64 (getr regsc 10)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  exact Hr. }
pose proof (K.s31_seed W regsc memc 30296 F p0 p1 R22 ltac:(lia) ltac:(lia) Hp0c Hp1c ltac:(lia) ltac:(lia)) as HS.
pose proof (K.E31_img regsc p0 p1) as HEI.
assert (E10 : ew (K.E31 regsc p0 p1) 10 = Z_to_bv 64 av).
{ rewrite (K.E31_reg regsc p0 p1 10%nat (10%bv) ltac:(vm_compute; reflexivity)). unfold av.
  symmetry. apply Z_to_bv_bv_unsigned. }
unfold cfg_at, w64.
replace (Z_to_bv 64 (vr_pc 0x8db3c)) with (Z_to_bv 64 (BASE + 30296)) by (unfold vr_pc; rewrite AFV; do 2 f_equal; lia).
psrr_branch_pi RUNP BR HS.
- (* 0x8db3c bnez a0: a nonzero answer, no call after the reply *)
  rewrite branch_ne_U in Hc. rewrite (U_atom _ 10 av E10 ltac:(lia)) in Hc. rewrite (U_lit _ 0 ltac:(lia)) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_shc RUNTOP HS HJ 30316.
  { awr_ok_tac. }
  match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
    set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
  clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (K.rdeq_of_frame _ _ _ _ _ HFr (K.ro_ss31 30296)) as Eq1. clear HF HFr HG.
  pose proof (K.rv_kept _ _ (restrict (w_H W) ms) regsc [w64 p0; w64 p1]
    (vr_base B e ++ vr_rl_ar F q c ++ [(24, hd 0 (p0 :: p1 :: tp'))]) HS (K.E31_agree regsc p0 p1)
    ltac:(vm_compute; reflexivity) HRV) as HRV2.
  cbn [ms_regs restrict hd] in HRV2.
  pmkst HS.
  assert (HC2 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
      (vr_rl_ar F q c ++ [(24, p0)]) (vr_R2 (e_R e) (e_D e)) O2 (vr_qv e) k
      (vr_k2 (e_R e) (e_D e)) nm VR_NM_AR lyc Sc W (ms_regs ms) (ms_mem ms) mdv).
  { eapply (K.core_keep B MT HB) with (lo := vr_s1 e) (hi := vr_s1 e);
      [exact HC | exact HJ | intros a Ha _ _; exact (Eq1 a) | lia | lia | | exact HRV2 | ].
    - exists ev0. intros kk Hkk. rewrite (K.s31_errno B HB) in HEV1 |- *. rewrite Eq1. exact (HEV1 kk Hkk).
    - unfold vr_sl3. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
  assert (Haf : vr_aft (e_D e) = None).
  { apply (s31_aft_some_none (e_D e) w0 w1 tk Etk).
    destruct (PV.after atoi_a (w0 :: w1 :: tk)) as [pr|] eqn:Ea; [|reflexivity].
    exfalso. apply Hc. unfold av. apply (proj1 (w64_zero_iff (getr regsc 10))). apply (proj2 HPr).
    rewrite Ea. discriminate. }
  apply SRr_ret. left.
  replace (BASE + 30316) with (vr_pc 0x8db50) by (unfold vr_pc; rewrite AFV; lia).
  exact (K.s31_to_af B MT e O2 pos F q c lyc Sc W (ms_regs ms) (ms_mem ms) mdv k nm [(24, p0)] Haf HC2 HL Hcf).
- (* a zero answer: 0x8db40 ld a0,8(s6); 0x8db44 jal atoi *)
  rewrite branch_ne_U in Hc. rewrite (U_atom _ 10 av E10 ltac:(lia)) in Hc. rewrite (U_lit _ 0 ltac:(lia)) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Haft : PV.after atoi_a (w0 :: w1 :: tk) <> None).
  { apply (proj1 HPr). apply (proj2 (w64_zero_iff (getr regsc 10))). exact Hc. }
  paj_run_shc RUNP RUNC HS HJ.
  { awr_ok_tac. }
  match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
    set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
  clearbody mdv.
  cbn [ms_mem mkst] in HFr.
  pose proof (K.rdeq_of_frame _ _ _ _ _ HFr (K.ro_ss31 30296)) as Eq1. clear HF HFr HG.
  prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1.
  rewrite K.E31_33 in Q10.
  pose proof (K.rv_kept _ _ (restrict (w_H W) ms) regsc [w64 p0; w64 p1]
    (vr_base B e ++ vr_rl_ar F q c ++ [(24, hd 0 (p0 :: p1 :: tp'))]) HS (K.E31_agree regsc p0 p1)
    ltac:(vm_compute; reflexivity) HRV) as HRV2.
  cbn [ms_regs restrict] in HRV2.
  pmkst HS.
  pose proof (proj1 HJ) as HAR1.
  assert (Hra : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (Hsp1 : spZ (ms_regs ms) = vr_sp0 e + (vr_s1 e - vr_sp0 e)).
  { unfold spZ. rewrite <- K.getr_Z2.
    rewrite (K.vr_rv_get _ _ 2 (vr_s1 e) HRV2 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto)).
    unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (Q3' : getr (ms_regs ms) 3 = w64 (as_gp B))
    by exact (K.vr_rv_get _ _ 3 _ HRV2 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto)).
  assert (Q4' : getr (ms_regs ms) 4 = w64 (as_tp B))
    by exact (K.vr_rv_get _ _ 4 _ HRV2 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto)).
  pose proof (ecall_pre_stk_at SEGS B (3 * ESTACK) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e)
    (e_mem e) (e_md e) [(4, pos)] lyc Sc W (ms_mem ms) mdv k (ms_regs ms) (vr_s1 e - vr_sp0 e) HJ Hsp1 Hal
    ltac:(lia) ltac:(change ESTACK with 4096; lia) ltac:(change ESTACK with 4096; lia) Hra Q3' Q4') as HPRE1.
  eapply SRr_bind.
  { eapply (ART (3 * ESTACK) (aerrno_cell B) _ W (ms_regs ms) (ms_mem ms) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e)
      (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdv k (vr_s1 e - vr_sp0 e) _
      (fun regs' mem' => getr regs' 10 = w64 (bv_swrap 32 (PIS.s10_val w1)) /\
         rd32 (rdW W mem') (as_errno B) (bv_unsigned (PIS.s10_errno w1 (Z_to_bv 64 ev0)))) HJ);
      [ exact Hsp1 | exact Hal | lia | change ESTACK with 4096; lia | change ESTACK with 4096; lia | exact Q1
      | intros a Ha; exact Ha | ].
    cbn [ss_pc setpc].
    apply (AATOI fx lyc Sc W (ms_regs ms) (ms_mem ms) mdv p1 w1 ev0).
    - rewrite Eq1. exact HFl1.
    - destruct HAG1 as [HG1a (cn & HG1b)]. split; [rewrite (K.rdword_eq _ _ _ Eq1); exact HG1a|].
      exists cn. rewrite (K.rdword_eq _ _ _ Eq1). exact HG1b.
    - exact HPRE1.
    - exact Q10.
    - lia.
    - apply astr_atR_view. apply (astr_atR_agree (rdW W memc) _ p1 w1 (Z.of_nat (length w1) + 1) Hw1); [lia|].
      intros kk Hkk. exact (Eq1 _).
    - apply (aread_ok_of_block SEGS B LAWS (3 * ESTACK) lyc Sc W (ms_regs ms) (ms_mem ms) mdv c
        (Z.of_nat (length (Verbs.line (e_D e))) + 1) p1 (astr_len w1 + 1) HAR1 Hcb); unfold astr_len;
        [lia | lia | lia | rewrite Hsp1; change ESTACK with 4096; lia].
    - apply (amem8_of_blockA SEGS B LAWS lyc Sc W (ms_mem ms) mdv p1 (astr_len w1) HAR1); [|unfold astr_len; lia].
      exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1). split; [exact Hcb | unfold astr_len; lia].
    - unfold astr_len. apply (BLKT lyc Sc W (ms_mem ms) mdv c (Z.of_nat (length (Verbs.line (e_D e))) + 1)
        (p1 + Z.of_nat (length w1)) HAR1 Hcb). lia.
    - intros kk Hkk. rewrite Eq1. exact (HEV1 kk Hkk).
    - (* tok[1] apart from the errno cell: its bytes are in the copy block, not image bytes (blk_img); the errno
         cell's are (api_env) *)
      pose proof (pal_env B TL) as (_ & Hzi & _).
      destruct (Z_le_gt_dec (p1 + astr_len w1 + 1) (as_errno B)) as [Hz1|Hz1]; [left; exact Hz1|].
      destruct (Z_le_gt_dec (as_errno B + 4) p1) as [Hz2|Hz2]; [right; exact Hz2|]. exfalso.
      apply (blk_img SEGS B LAWS lyc Sc W (ms_mem ms) mdv c (Z.of_nat (length (Verbs.line (e_D e))) + 1)
        (Z.max p1 (as_errno B)) HAR1 Hcb); [| apply Hzi; clear - Hz1 Hz2; lia].
      unfold req_size. destruct (Z.eqb_spec (Z.of_nat (length (Verbs.line (e_D e))) + 1) 0) as [Hzk|Hzk]; cbv iota;
        clear - Hcp1 Hp1e Hz1 Hzk; unfold astr_len in Hz1; lia.
    - apply vr_rtrom_ok. intros a H1 H2 H3. rewrite Eq1. exact (HA1 a H1 H2 H3). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HQ2 & HQerr) & HFR2).
  change ESTACK with 4096 in HFR2.
  assert (KP2 : K.kp W memc mem2 (vr_s1 e - 3 * 4096) (vr_s1 e)).
  { intros a Ha Hw He.
    rewrite (HFR2 a Ha ltac:(lia) ltac:(unfold aerrno_cell; rewrite (K.s31_errno B HB); exact He)).
    exact (Eq1 a). }
  apply SRr_ret. right.
  exists O2, pos, F, q, c, (p0 :: p1 :: tp'), lyc, Sc, regs2, mem2, md2, k, nm.
  split; [unfold cfg_at, w64; replace (vr_pc 0x8db48) with (BASE + 30308) by (unfold vr_pc; rewrite AFV; lia); reflexivity|].
  split; [rewrite Etk; cbn; lia|].
  split.
  { eapply (K.core_keep B MT HB) with (lo := vr_s1 e - 3 * 4096) (hi := vr_s1 e);
      [exact HC | exact HJ2 | exact KP2 | lia | lia | | | ].
    - exists (bv_unsigned (PIS.s10_errno w1 (Z_to_bv 64 ev0))). exact HQerr.
    - apply (K.vr_rv_pres (ms_regs ms) regs2 _ HP2); [|exact HRV2].
      unfold vr_base, vr_rl_ar. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
    - unfold vr_sl3. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
  split; [exact HL|].
  split.
  { apply (K.copy_keep B e F c (p0 :: p1 :: tp') lyc Sc W memc mdc mem2 (vr_s1 e - 3 * 4096) (vr_s1 e) pos k);
      [exact (proj1 HC) | exact EF | exact Hcb | split; [exact Hcf | exact Hat] | exact KP2 | lia]. }
  unfold Pr3. rewrite Etk. cbn [nth]. split; [exact HQ2 | exact Haft].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The program call sup_after_reply(atoi(tok[1]), tok[0]): its footprint is g_rec, record.spill and the recorder's
   blocks (sup_after_reply_c.v:93); what the call keeps, as verbs_receive_s08_lib.v's ck_* lemmas *)
Definition s31_fp1 (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma s31_fp1_cases : forall O a, inFP (s31_fp1 O) a ->
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a H. unfold s31_fp1 in H. apply inFP_cons in H as [H|H]; [left; exact H|].
apply inFP_cons in H as [H|H]; [right; left; exact H|]. right; right. exact (inFP_ablocks_fp_inv O a H).
Qed.
Lemma s31_PG_rec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity | unfold REC_SIZE in Ha; cbn; lia]. Qed.
Lemma s31_PG_spill : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity | unfold SC_SIZE in Ha; cbn; lia]. Qed.
Lemma s31_PG_quit : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; right; right; left; reflexivity | cbn; lia]. Qed.
Lemma s31_O_pos : forall ly S (W : world SEGS) mem md (O : list (Z * Z)), AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> Forall (fun pn => 0 < fst pn) O.
Proof.
intros ly S W mem md O HAR HO. apply Forall_forall. intros [p n] Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hin)) as (_ & H4 & _). cbn. lia.
Qed.
Lemma s31_fp1_closed : forall O, Forall (fun pn => 0 < fst pn) O -> ~ YI16.sink_open_fp (s31_fp1 O).
Proof.
intros O HO. unfold s31_fp1. apply sink_closed_cons; [unfold A_G_REC; cbn; lia|].
apply sink_closed_cons; [unfold A_REC_SPILL; cbn; lia|]. apply sink_closed_ablocks_fp. exact HO.
Qed.

Section s31ck.
Variables (O : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (STK1 sp1 : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (mem2 : word -> option byte) (md2 : Model) (k1 : Z).
Hypothesis HAR : AR SEGS B lyc Sc W mem md.
Hypothesis HJc : ajournal SEGS B STK1 sp1 (s31_fp1 O) lyc Sc W mem md [] ly2 S2 W2 mem2 md2 k1.
Hypothesis HO : forall pn, In pn O -> In pn (ablocks B lyc Sc).

Lemma s31_ck_stack : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) -> rdW W2 mem2 a = rdW W mem a.
Proof.
intros a Ha Hw. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
apply F1; [exact Ha | exact Hw |]. pose proof asan_consts as (C1 & _).
intros Hf. destruct (s31_fp1_cases O a Hf) as [G|[G|(p & n & Hpn & Hr)]].
- unfold A_G_REC, REC_SIZE in G. lia.
- unfold A_REC_SPILL, SC_SIZE in G. lia.
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & _ & Hc & _). lia.
Qed.

Lemma s31_ck_frame : forall cid pos a, In (cid, pos) (frames Sc) ->
(frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid \/
 shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8) ->
rdW W2 mem2 a = rdW W mem a.
Proof.
intros cid pos a Hin Ha. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
apply (F4 cid pos a Hin); [unfold frame_rng, in_zr; cbn [fst snd]; lia |].
intros Hf. pose proof asan_consts as (C1 & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfa).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)) as Hdl.
destruct Ha as [Ha | Ha].
- assert (Himg : ~ in_img SEGS a) by exact (frm_img SEGS B LAWS lyc Sc W mem md cid pos a HAR Hin Ha).
  destruct (s31_fp1_cases O _ Hf) as [G|[G|(b & m & Hbm & Hr)]].
  + exact (Himg (proj1 (PROGU _ (s31_PG_rec _ G)))).
  + exact (Himg (proj1 (PROGU _ (s31_PG_spill _ G)))).
  + pose proof (sep_block_frame SEGS B LAWS lyc Sc W mem md b m cid pos HAR (HO _ Hbm) Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)) as Hdp.
  destruct (s31_fp1_cases O _ Hf) as [G|[G|(b & m & Hbm & Hr)]].
  + unfold shadow_addr, SHADOW_OFF, A_G_REC, REC_SIZE in *. lia.
  + unfold shadow_addr, SHADOW_OFF, A_REC_SPILL, SC_SIZE in *. lia.
  + destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR (HO _ Hbm)) as (_ & _ & _ & Happ & _).
    apply (fshadow_not_app (frame_addr lyc cid pos) (fs_frame_bytes cid / 8) b (req_size m) a); [lia | lia | exact Happ | | exact Hr].
    unfold shadow_addr, SHADOW_OFF in Ha. lia.
Qed.

Lemma s31_ck_img : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ (A_G_REC <= a < A_G_REC + REC_SIZE) -> ~ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
rdW W2 mem2 a = rdW W mem a.
Proof.
intros a Himg Ho He Hg Hs. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply (F3 a Himg Ho He). apply fp_spares_closed; [exact (s31_fp1_closed O (s31_O_pos lyc Sc W mem md O HAR HO))|].
intros Hf. destruct (s31_fp1_cases O _ Hf) as [G|[G|(b & m & Hbm & Hr)]]; [exact (Hg G) | exact (Hs G) |].
exact (blk_img SEGS B LAWS lyc Sc W mem md b m a HAR (HO _ Hbm) Hr Himg).
Qed.

Lemma s31_ck_arodata : arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W2 mem2).
Proof.
intros HR a Hro Ho He.
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]).
rewrite (s31_ck_img a Himg Ho He); [exact (HR a Hro Ho He) | |].
- intros G. exact (RPG a (s31_PG_rec a G) Hro).
- intros G. exact (RPG a (s31_PG_spill a G) Hro).
Qed.

Lemma s31_ck_quit : forall v, aval_mem (rdW W mem) A_G_QUITTING 4 v -> aval_mem (rdW W2 mem2) A_G_QUITTING 4 v.
Proof.
intros v Hq kk Hk.
assert (Ha : A_G_QUITTING <= A_G_QUITTING + Z.of_nat kk < A_G_QUITTING + 4) by lia.
destruct (PROGU _ (s31_PG_quit _ Ha)) as (Hi & Ho & He).
rewrite (s31_ck_img _ Hi Ho He); [exact (Hq kk Hk) | |].
- unfold A_G_QUITTING, A_G_REC, REC_SIZE. lia.
- unfold A_G_QUITTING, A_REC_SPILL, SC_SIZE. lia.
Qed.
End s31ck.

(* tok[0] handed to sup_after_reply: a C string in the copy block, apart from every block of the recorder *)
Lemma s31_tok_arg : forall e F q c tp lyc Sc (W : world SEGS) mem md O i p w,
AR SEGS B lyc Sc W mem md ->
Permutation (ablocks B lyc Sc) (O ++ [vr_lb e q; vr_cb e c] ++ e_rest e) ->
vr_copy B e F c tp W mem ->
nth_error tp i = Some p -> nth_error (Verbs.toks (e_D e)) i = Some w ->
in_blockA (ablocks B lyc Sc) p (Z.of_nat (length w) + 1) /\ astr_atR (rdW W mem) p w /\
Z.of_nat (length w) + 1 <= LMAX + 1 /\
Forall (fun qk => iv_apart p (Z.of_nat (length w) + 1) (fst qk) (snd qk)) O.
Proof.
intros e F q c tp lyc Sc W mem md O i p w HAR Hperm (Hfc & (Hmod & HlenP & Hptr & Hw)) Hp Hwi.
destruct (Hw i p w Hp Hwi) as (A1 & A2 & A3 & A4).
assert (HndOT : List.NoDup (O ++ [vr_lb e q; vr_cb e c] ++ e_rest e))
  by exact (Permutation_NoDup Hperm (K.ablocks_nodup B _ _ _ _ _ HAR)).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. right; left; reflexivity. }
assert (HcO : ~ In (vr_cb e c) O).
{ intros H. exact (K.nodup_app_disj O _ _ HndOT H ltac:(right; left; reflexivity)). }
unfold vr_cb in Hcb, HcO.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn).
cbn [fst snd] in Hc4096, Hcc, Hcn.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [Hrq1 Hrq2].
split; [exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1); split; [exact Hcb | lia]|].
split; [exact A1|]. split; [unfold LMAX; lia|].
apply Forall_forall. intros [b m] Hbm.
assert (Hb : In (b, m) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; left. exact Hbm. }
assert (Hne : (c, Z.of_nat (length (Verbs.line (e_D e))) + 1) <> (b, m)) by (intros E; rewrite E in HcO; exact (HcO Hbm)).
pose proof (sep_blocks SEGS B LAWS lyc Sc W mem md _ _ b m HAR Hcb Hb Hne) as Hd.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hmn).
pose proof (req_size_pos m ltac:(lia)) as [Hm1 Hm2].
unfold zdisjoint in Hd. cbn [fst snd] in Hd |- *. unfold iv_apart. lia.
Qed.

(* the meter of the call after the reply, in one lemma so that a change of the meter's form stays here:
   sup_after_reply's account is two copies (arg_i of the number, xstrdup of the verb), each of at most
   VERBS_RECEIVE_REQ bytes, and no spill frees on a recorder of fewer than 16 calls; it spends two events *)
Lemma s31_sar_meter : forall R id (w : list byte), (length (r_calls R) < 16)%nat -> -2 ^ 31 <= id < 2 ^ 31 ->
Z.of_nat (length w) <= 8192 ->
XM_SUP_AFTER_REPLY MT R id (Some w) <= 2 * mo_malloc MT VERBS_RECEIVE_REQ + 0 * mo_free MT /\
EV_SUP_AFTER_REPLY R = 2.
Proof.
intros R id w Hc Hid Hw.
assert (Hspill : rec_spill_frees R = 0).
{ unfold rec_spill_frees. destruct (Nat.ltb_spec (length (r_calls R)) 16); [reflexivity | lia]. }
pose proof (dec_length id Hid) as Hd.
split; [|unfold EV_SUP_AFTER_REPLY, EV_ARG_I, EV_XSTRDUP; rewrite Hspill; reflexivity].
unfold XM_SUP_AFTER_REPLY, XM_ARG_I, XM_XSTRDUP. cbn [sarg]. rewrite Hspill.
pose proof (mo_malloc_mono MT MTL (Z.of_nat (length (dec id)) + 1) VERBS_RECEIVE_REQ
  ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M1.
pose proof (mo_malloc_mono MT MTL (Z.of_nat (length w) + 1) VERBS_RECEIVE_REQ
  ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M2.
lia.
Qed.

(* the frame chain at the call of sup_after_reply: s0 = sp0, verbs_receive's own frame pointer (class B of
   the s0 call-site survey); the prologue stored the caller's ra and s0 at sp0 - 8 and sp0 - 16 (vr_saved, j = 0 and
   j = 1), and the journal keeps every word from sp0 up, so achain_push extends afn_pre's chain (vr_ent's first
   conjunct); when sp0 >= ly_top - 16 the chain is achain's empty case *)
Lemma s31_chain : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs memc mdc,
vr_ent B MT e ->
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs memc mdc ->
exists ch1, achain lyc (rdW W memc) (vr_s1 e) (vr_sp0 e) ch1.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs memc mdc Hent Hcore.
unfold vr_ent in Hent. cbv zeta in Hent.
destruct Hent as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREC0 & _).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct Hcore as (HJ & _ & _ & _ & _ & _ & Hsaved & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & _).
destruct (K.s1_props e Hal16) as [_ Hs1].
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (HFP : forall a, alloc_ceiling <= a -> ~ inFP (vr_fp e) a).
{ intros a Ha (r & Hr & Hrr). unfold vr_fp, VERBS_RECEIVE_PG in Hr. apply in_app_or in Hr as [Hr | Hr].
  - cbn in Hr. unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, A_G_QUITTING in Hr.
    repeat destruct Hr as [<- | Hr]; [cbn in Hrr; lia | cbn in Hrr; lia | cbn in Hrr; lia | destruct Hr].
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). cbn [fst snd] in Hrr.
    pose proof (rec_repA_in_blocks B _ _ _ _ _ _ HREC0 Hpn) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 Hin) as (_ & _ & Hc & _). lia. }
assert (KA : forall a, vr_sp0 e <= a < 2 ^ 64 -> rdW W memc a = rdW (e_W e) (e_mem e) a).
{ intros a Ha. apply F1; [lia | lia | apply HFP; lia]. }
pose proof (achain_kept (e_ly e) _ (rdW W memc) _ _ _ (vr_sp0 e) Hch ltac:(unfold vr_sp0; lia) ltac:(lia)
  ltac:(intros a Ha; apply KA; unfold vr_sp0 in *; lia)) as Hch'.
destruct (Z_lt_le_dec (vr_sp0 e) (ly_top (e_ly e) - 16)) as [Hlt | Hge].
- exists ((vr_sp0 e, raZ (e_regs e), s0Z (e_regs e)) :: e_ch e).
  apply (achain_ly_top (e_ly e) lyc); [exact Etop|].
  apply (achain_push (e_ly e) (rdW W memc) (rdW W memc));
    [exact Hch' | lia | intros; reflexivity | | | exact Hra4 | lia | | exact Hlt | lia].
  + apply K.rdword_of_aval; [|unfold raZ; apply bv_unsigned_in_range].
    replace (vr_sp0 e - 8) with (vr_sp0 e - 8 - 8 * Z.of_nat 0) by lia. exact (Hsaved 0%nat 1 eq_refl).
  + apply K.rdword_of_aval; [|unfold s0Z; apply bv_unsigned_in_range].
    replace (vr_sp0 e - 16) with (vr_sp0 e - 8 - 8 * Z.of_nat 1) by lia. exact (Hsaved 1%nat 8 eq_refl).
  + apply Z.mod_divide; [lia|]. pose proof Hal16 as H16. apply Z.mod_divide in H16; [|lia].
    destruct H16 as [z Hz]. exists (2 * z). lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* 0x8db48 .. 0x8db4c: mv a1,s8; jal sup_after_reply, from the state with a0 = atoi(tok[1]), to 0x8db50 (vr_af).
   sup_after_reply reaches the printf wrappers (its post is apost_baseF), so the exit is vr_af at the FP state fx'
   the call returns at, related to the entry's by fxrel; the call is the segment's last instruction, so nothing
   runs at fx' *)
Lemma s31_p4 : vr_segF B MT (fun e => s31_mid e 0x8db48 Pr3) (vrF_af B MT).
Proof.
intros e W cf HE HM.
destruct HM as (O2 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hnt & HC & HL & HCP & HPr).
pose proof HC as (HJ & Hk & HMe & Hnm & HFR & HRV & HSV & HSP & HENV & HREC & HnD & HPERM & HQ).
pose proof HE as HE'. unfold vr_ent in HE'. cbv zeta in HE'.
destruct HE' as (HPRE & HROD & H10 & HOBJ & HFD & HDATA & HN & Hn8 & HlD & HdIn & HdO & HDb & HTV & HREC0 & Hc0 & Ha0
  & Hr0 & Hnr0 & Hdec & HPERM0 & HQ0 & HGOT0 & HRO0 & HROIN & HVO & HEV0 & HFL0 & HAG0 & Hfr4 & Hnev & Hlive & HMOK
  & Hfrm).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ as (HARj & Hly & _ & _ & _ & Hfrs & Hnevj & Hk0 & _).
destruct (K.s1_props e Hal16) as [Hal Hs1].
assert (HTS : VERBS_RECEIVE_STK = 16992) by (vm_compute; reflexivity).
assert (HSS : SUP_AFTER_REPLY_STK = 16592) by (vm_compute; reflexivity).
destruct HCP as [Hcf Hat]. pose proof Hat as (Hmod & Hlen & Hptr & Hstr).
destruct (Verbs.toks (e_D e)) as [|w0 [|w1 tk]] eqn:Etk; [cbn in Hnt; lia | cbn in Hnt; lia |].
destruct tp as [|p0 [|p1 tp']]; cbn [length] in Hlen; [discriminate | discriminate |].
destruct (Hstr 0%nat p0 w0 eq_refl eq_refl) as (Hw0 & Hw0l & Hcp0 & Hp0e).
rewrite <- Etk in Hat.
unfold Pr3 in HPr. cbn [nth] in HPr. destruct HPr as [HPr10 HPraft].
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ eapply Permutation_in; [symmetry; exact HPERM|]. apply in_or_app. right. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc _ _ HARj Hcb) as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn).
unfold vr_cb in Hcb, Hc4096, Hcc, Hcn. cbn [fst snd] in Hc4096, Hcc, Hcn.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof HFR as (EF & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HARj Hin4) as (HF0 & HFc & _).
change (fs_frame_bytes 4) with 1024 in HFc. rewrite <- EF in HF0, HFc.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [_ Hrq].
pose proof HENV as (HA1 & HG1 & HR1 & HAG1 & HFl1 & (ev0 & HEV1)).
(* the model: the call after the reply is sup_after_reply(atoi_a tok[1], tok[0]) *)
assert (Haf : vr_aft (e_D e) = Some (atoi_a w1, w0)) by exact (s31_aft_val (e_D e) w0 w1 tk Etk HPraft).
assert (ER3 : vr_R3 (e_R e) (e_D e) = sup_after_reply_m (vr_R2 (e_R e) (e_D e)) (atoi_a w1) (Some w0))
  by (unfold vr_R3; rewrite Haf; reflexivity).
pose proof (ev_vr_eq (e_R e) (e_D e)) as Hevq.
assert (Hc2 : (length (r_calls (vr_R2 (e_R e) (e_D e))) <= 2)%nat) by exact (s31_calls2 (e_R e) (e_D e) Hc0).
assert (Hid : -2 ^ 31 <= atoi_a w1 < 2 ^ 31) by (unfold atoi_a; apply swrap32_range).
pose proof (dec_length (atoi_a w1) Hid) as Hdec1.
destruct (s31_sar_meter (vr_R2 (e_R e) (e_D e)) (atoi_a w1) w0 ltac:(lia) Hid Hw0l) as [HXM HEV].
assert (EK3 : vr_k3 (e_R e) (e_D e) = vr_k2 (e_R e) (e_D e) + EV_SUP_AFTER_REPLY (vr_R2 (e_R e) (e_D e)))
  by (unfold vr_k3, ev_after; rewrite Haf; reflexivity).
(* the blocks at the call *)
assert (HND : List.NoDup (O2 ++ [vr_lb e q; vr_cb e (c)] ++ e_rest e))
  by exact (Permutation_NoDup HPERM (K.ablocks_nodup B _ _ _ _ _ HARj)).
assert (HO2 : forall pn, In pn O2 -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ HREC Hpn)).
assert (HTSc : forall pn, In pn ([vr_lb e q; vr_cb e c] ++ e_rest e) -> In pn (ablocks B lyc Sc))
  by (intros pn H; apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; exact H).
assert (HO2T : forall pn, In pn O2 -> ~ In pn ([vr_lb e q; vr_cb e c] ++ e_rest e))
  by (intros pn H1 H2; exact (K.nodup_app_disj O2 _ pn HND H1 H2)).
assert (HNDT : List.NoDup ([vr_lb e q; vr_cb e c] ++ e_rest e)) by exact (K.nodup_app_r _ _ HND).
assert (HdT : In (e_data e, Z.max (e_n e) 1) ([vr_lb e q; vr_cb e c] ++ e_rest e)).
{ apply (Permutation_in _ HPERM0) in HdIn. apply in_app_iff in HdIn as [H | H]; [exact (False_ind _ (HdO H))|].
  apply in_or_app. right. exact H. }
(* the live bytes, the events and the meter at the call *)
assert (Hbb : blocks_bytes Sc <= blocks_bytes (e_S e) + 20 * (LMAX + 2) + bsum [vr_lb e q; vr_cb e c]).
{ pose proof (vr_live_le SEGS B LAWS (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) lyc Sc W memc mdc (rdW W memc)
    (vr_R2 (e_R e) (e_D e)) (e_O e) O2 [vr_lb e q; vr_cb e c] (e_rest e) HAR0 HARj HPERM0 HPERM HREC) as HL2.
  assert (Hmono : (6 * Z.of_nat (length (r_calls (vr_R2 (e_R e) (e_D e)))) + 8) * (LMAX + 2) <= 20 * (LMAX + 2))
    by (apply Z.mul_le_mono_nonneg_r; [unfold LMAX; lia | lia]).
  lia. }
assert (Hts : bsum [vr_lb e q; vr_cb e c] <= 8193 + 8193).
{ unfold vr_lb, vr_cb. rewrite !bsum_cons. unfold bsum. cbn [fold_right snd].
  pose proof (verbs_receive_pre.strnlen_res_le (e_n e) (e_D e) ltac:(lia)) as Hsl. unfold vr_l.
  pose proof (SlotRec.line_len (e_D e)) as Hll.
  pose proof (SlotRec.strnlen_upto0 (e_D e) (e_n e) HlD) as Hup. lia. }
assert (Hlv : LIVE_SUP_AFTER_REPLY (atoi_a w1) (Some w0) <= 12 + 8193).
{ unfold LIVE_SUP_AFTER_REPLY, LIVE_ARG_I, LIVE_XSTRDUP. cbn [sarg]. lia. }
assert (Hlive1 : blocks_bytes Sc + LIVE_SUP_AFTER_REPLY (atoi_a w1) (Some w0) <= LIVE_MAX).
{ unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ, LMAX in *. lia. }
assert (Hev1 : st_nev Sc + EV_SUP_AFTER_REPLY (vr_R2 (e_R e) (e_D e)) <= EV_MAX) by lia.
assert (Hfr8 : Z.of_nat (length (frames Sc)) <= 8) by (rewrite Hfrs; cbn [length app]; lia).
assert (Hmok1 : mo_ok MT Sc (XM_SUP_AFTER_REPLY MT (vr_R2 (e_R e) (e_D e)) (atoi_a w1) (Some w0))).
{ eapply vri_meter_ok with (a := 2) (b := 0) (ev := 2); [exact MTL | exact HE | exact HMe | exact HXM | lia | lia | lia]. }
(* the run 0x8db48 mv a1,s8; 0x8db4c jal sup_after_reply, from the registers alone *)
remember (Eimg (Ereg regsc [])) as E0 eqn:HE0.
assert (HEI : img_env VAL A_LIM E0) by (subst E0; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc []) E0) by (subst E0; apply K.Er_agree).
assert (E10 : ew E0 10 = getr regsc 10) by (subst E0; exact (ew_Eimg_Ereg_nat regsc [] 10 (10%bv) eq_refl)).
assert (E24 : ew E0 24 = getr regsc 24) by (subst E0; exact (ew_Eimg_Ereg_nat regsc [] 24 (24%bv) eq_refl)).
assert (HS : st_ok_pi SEGS VAL E0 (K.ssr31 30308)
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 30308)) memc (seg_rom SEGS))))
  by (subst E0; exact (K.s31_seed_r W regsc memc 30308)).
clear HE0.
unfold cfg_at, w64.
replace (Z_to_bv 64 (vr_pc 0x8db48)) with (Z_to_bv 64 (BASE + 30308)) by (unfold vr_pc; rewrite AFV; do 2 f_equal; lia).
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
  set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
clearbody mdv.
cbn [ms_mem mkst] in HFr.
pose proof (K.rdeq_of_frame _ _ _ _ _ HFr (Forall_nil _)) as Eq1. clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
pose proof (K.rv_kept _ _ (restrict (w_H W) ms) regsc []
  (vr_base B e ++ vr_rl_ar F q c ++ [(24, hd 0 (p0 :: p1 :: tp'))]) HS HAE
  ltac:(vm_compute; reflexivity) HRV) as HRV2.
cbn [ms_regs restrict] in HRV2.
pmkst HS.
cbn [ss_pc setpc].
rewrite (SIGP CS_sup_after_reply) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_sup_after_reply) with AF_sup_after_reply.
pose proof (proj1 HJ) as HAR1.
assert (Q10' : getr (ms_regs ms) 10 = w64 (atoi_a w1)).
{ rewrite Q10, E10. exact HPr10. }
assert (Q11' : getr (ms_regs ms) 11 = w64 p0).
{ rewrite Q11, E24.
  exact (K.vr_rv_get _ _ 24 p0 HRV ltac:(apply in_or_app; right; apply in_or_app; right; cbn; tauto)). }
assert (Hsp1 : spZ (ms_regs ms) = vr_sp0 e + (vr_s1 e - vr_sp0 e)).
{ unfold spZ. rewrite <- K.getr_Z2.
  rewrite (K.vr_rv_get _ _ 2 (vr_s1 e) HRV2 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto)).
  unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Q3' : getr (ms_regs ms) 3 = w64 (as_gp B))
  by exact (K.vr_rv_get _ _ 3 _ HRV2 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto)).
assert (Q4' : getr (ms_regs ms) 4 = w64 (as_tp B))
  by exact (K.vr_rv_get _ _ 4 _ HRV2 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto)).
assert (R8 : getr (ms_regs ms) (Z_to_bv 5 8) = w64 (vr_sp0 e))
  by exact (K.vr_rv_get _ _ 8 _ HRV2 ltac:(apply in_or_app; left; unfold vr_base; cbn; tauto)).
(* the boundary at the call *)
assert (HC2 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
    (vr_rl_ar F q c ++ [(24, hd 0 (p0 :: p1 :: tp'))]) (vr_R2 (e_R e) (e_D e)) O2 (vr_qv e) k
    (vr_k2 (e_R e) (e_D e)) nm VR_NM_AR lyc Sc W (ms_regs ms) (ms_mem ms) mdv).
{ eapply (K.core_keep B MT HB) with (lo := vr_s1 e) (hi := vr_s1 e);
    [exact HC | exact HJ | intros a Ha _ _; exact (Eq1 a) | lia | lia | | exact HRV2 | ].
  - exists ev0. intros kk Hkk. rewrite (K.s31_errno B HB) in HEV1 |- *. rewrite Eq1. exact (HEV1 kk Hkk).
  - unfold vr_sl3. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
pose proof HC2 as (_ & _ & _ & _ & _ & _ & _ & _ & HENV2 & HREC2 & _).
pose proof HENV2 as (HA2 & _ & HR2 & _).
assert (HCP2 : vr_copy B e F c (p0 :: p1 :: tp') W (ms_mem ms))
  by (apply (K.copy_keep B e F c (p0 :: p1 :: tp') lyc Sc W memc mdc (ms_mem ms) (vr_s1 e) (vr_s1 e) pos k);
      [exact (proj1 HC) | exact EF | exact Hcb | split; [exact Hcf | exact Hat] | intros a Ha _ _; exact (Eq1 a) | lia]).
destruct (s31_tok_arg e F q c (p0 :: p1 :: tp') lyc Sc W (ms_mem ms) mdv O2 0 p0 w0 HAR1 HPERM HCP2 eq_refl
  ltac:(rewrite Etk; reflexivity)) as (Hib & Hstr0 & Hlen0 & Hap).
(* the frame chain at the call: s0 = sp0 (s31_chain) *)
destruct (s31_chain e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs ms) (ms_mem ms) mdv HE HC2) as [ch1 Hch1].
assert (Hs0 : s0Z (ms_regs ms) = vr_sp0 e).
{ unfold s0Z. etransitivity; [exact (f_equal bv_unsigned R8)|]. unfold w64. apply unsigned_lit_small. lia. }
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS W (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_sup_after_reply))
    VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdv k
    SUP_AFTER_REPLY_STK (s31_fp1 O2) (EV_SUP_AFTER_REPLY (vr_R2 (e_R e) (e_D e))) (vr_s1 e - vr_sp0 e)
    (Z_to_bv 64 (BASE + 30316)) ch1
    (fun ly' S' W' (regs' : bvmap 5 word) mem' md' => exists O' : list (Z * Z),
      rec_repA B ly' S' (rdW W' mem') (sup_after_reply_m (vr_R2 (e_R e) (e_D e)) (atoi_a w1) (Some w0)) O' /\
      (forall pn, In pn O' -> In pn O2 \/ ~ In pn (ablocks B lyc Sc)) /\
      (forall pn, In pn (ablocks B lyc Sc) -> ~ In pn O2 -> In pn (ablocks B ly' S')) /\
      (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B lyc Sc) /\ ~ In pn O2) \/ In pn O') /\
      blocks_bytes S' <= blocks_bytes Sc + LIVE_SUP_AFTER_REPLY (atoi_a w1) (Some w0) /\
      mo_le MT Sc S' (XM_SUP_AFTER_REPLY MT (vr_R2 (e_R e) (e_D e)) (atoi_a w1) (Some w0))) HJ).
  - exact Hsp1.
  - exact Hal.
  - lia.
  - rewrite HSS. lia.
  - rewrite HSS, HTS. lia.
  - exact Q3'.
  - exact Q4'.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) by lia. rewrite Hs0. exact Hch1.
  - intros HPRE1. eapply SRr_mono.
    { exact (TSUP_AFTER_REPLY fx lyc Sc W (ms_regs ms) (ms_mem ms) mdv ch1 (atoi_a w1) p0 (Some w0)
        (vr_R2 (e_R e) (e_D e)) O2 HPRE1 Hfrm HA2 HR2 Q10' Hid Q11' ltac:(lia)
        (ex_intro _ w0 (conj eq_refl (conj Hib (conj Hstr0 (conj Hlen0 Hap)))))
        HREC2 Hfr8 Hev1 Hlive1 Hmok1). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HR' & HC' & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. rewrite Q1. split; [reflexivity|]. split; [exact HR'|]. split; [exact HC'|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. destruct (s31_fp1_cases O2 a Ha) as [G|[G|(p & n & Hpn & Hr)]].
    + right; right; right; right; left. split; [exists (A_G_REC, A_G_REC + REC_SIZE); split;
        [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; left; reflexivity | exact G]|].
      split; [|exact (proj1 (PROGU a (s31_PG_rec a G)))].
      rewrite (ts_prog _ HB). unfold TFIB_PROG_STATIC. apply Exists_cons_hd.
      unfold in_zr, A_G_REC, REC_SIZE in *. cbn [fst snd]. lia.
    + right; right; right; right; left. split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split;
        [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; right; left; reflexivity | exact G]|].
      split; [|exact (proj1 (PROGU a (s31_PG_spill a G)))].
      rewrite (ts_prog _ HB). unfold TFIB_PROG_STATIC. apply Exists_cons_tl. apply Exists_cons_hd.
      unfold in_zr, A_REC_SPILL, SC_SIZE in *. cbn [fst snd]. lia.
    + assert (HpS : In (p, n) (ablocks B lyc Sc)) by exact (HO2 _ Hpn).
      destruct (in_dec s31_pdec (p, n) (ablocks B (e_ly e) (e_S e))) as [Hent | Hnent].
      * apply (Permutation_in _ HPERM0) in Hent. apply in_app_iff in Hent as [HinO | HinR].
        -- right; left. split; [|exists p, n; split; [exact HpS | exact Hr]].
           unfold vr_fp. apply inFP_app. right. replace a with (p + (a - p)) by lia.
           apply (inFP_ablocks_fp _ p n); [exact HinO | lia].
        -- exfalso. apply (HO2T _ Hpn). apply in_or_app. right. exact HinR.
      * right; right; left. exists p, n. split; [exact HpS | split; [exact Hnent | exact Hr]].
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw Hn. exfalso.
    destruct (s31_fp1_cases O2 a Ha) as [G|[G|(p & n & Hpn & Hr)]].
    + unfold A_G_REC, REC_SIZE in G. lia.
    + unfold A_REC_SPILL, SC_SIZE in G. lia.
    + destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARj (HO2 _ Hpn)) as (_ & _ & Hc' & _). lia. }
(* the state at 0x8db50 *)
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJo & HJi & HPres
  & (O' & HRec' & HO'1 & Hkeep & Hall & Hbb2 & Hmle)).
pose proof HJi as (HAR2 & Hly2 & _).
assert (Efr : frame_addr ly2 4 pos = frame_addr lyc 4 pos)
  by (unfold frame_addr; destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _); rewrite EF2; reflexivity).
assert (Efl : flag_addr ly2 4 pos = flag_addr lyc 4 pos)
  by (unfold flag_addr; destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _); rewrite EF2; reflexivity).
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJi by lia.
assert (KSt : forall a, vr_s1 e <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memc a).
{ intros a Ha. rewrite (s31_ck_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR1 HJi HO2 a ltac:(lia) ltac:(lia)). exact (Eq1 a). }
assert (KFr : forall a, (F <= a < F + 1024 \/ shadow_addr F <= a < shadow_addr F + 128) -> rdW W2 mem2 a = rdW W memc a).
{ intros a Ha. rewrite (s31_ck_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR1 HJi HO2 4 pos a Hin4
    ltac:(rewrite <- EF; change (fs_frame_bytes 4) with 1024; change (1024 / 8) with 128; exact Ha)).
  exact (Eq1 a). }
set (O3 := nodup s31_pdec O').
assert (HO3 : forall pn, In pn O3 <-> In pn O') by (intros pn; unfold O3; apply nodup_In).
rewrite HEV in HJo.
exists fx'. split; [exact Hfx|].
exists O3, pos, F, q, c, ly2, S2, regs2, mem2, md2, (k + 2), (nm + 2).
split; [unfold cfg_at, w64; replace (vr_pc 0x8db50) with (BASE + 30316) by (unfold vr_pc; rewrite AFV; lia); reflexivity|].
split; [|split; [exact HL | exact Hcf]].
rewrite ER3, EK3, HEV.
split; [exact HJo|].
split; [lia|].
split.
{ eapply vri_meter_step with (X := XM_SUP_AFTER_REPLY MT (vr_R2 (e_R e) (e_D e)) (atoi_a w1) (Some w0))
    (a := 2) (b := 0) (ev := 2); [exact MTL | exact HMe | exact Hmle | exact HXM | lia | lia]. }
split; [unfold VR_NM_AR, VR_NM_AF in *; lia|].
split.
{ destruct HFR as (EF' & HF2 & HF3).
  split; [rewrite Efr; exact EF'|].
  split.
  - rewrite Efl. rewrite (rdword_ext (rdW W memc) (rdW W2 mem2) (F + 1016)); [exact HF2|].
    intros kk Hkk. apply KFr. left. lia.
  - intros i Hi. rewrite KFr; [exact (HF3 i Hi) | right; lia]. }
split.
{ apply K.vr_rv_intro. intros r v Hin. apply in_app_or in Hin as [Hin | Hin].
  - assert (Hcs : acallee_saved r)
      by (unfold vr_base in Hin; cbn in Hin; destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _;
          unfold acallee_saved; lia).
    rewrite (HPres r Hcs). apply (K.vr_rv_get _ _ _ _ HRV2). apply in_or_app; left; exact Hin.
  - assert (Hcs : acallee_saved r)
      by (unfold vr_rl_af in Hin; cbn in Hin; destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _;
          unfold acallee_saved; lia).
    rewrite (HPres r Hcs). apply (K.vr_rv_get _ _ _ _ HRV2). apply in_or_app; right. apply in_or_app; left.
    unfold vr_rl_af in Hin. unfold vr_rl_ar. cbn in Hin |- *. tauto. }
split.
{ intros j r Hj. pose proof (HSV j r Hj) as H.
  assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length vr_saved_regs] in Hj13.
  intros kk Hkk. rewrite KSt; [exact (H kk Hkk) | lia]. }
split.
{ unfold vr_spill. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
  unfold vr_spill in HSP. rewrite Forall_forall in HSP.
  pose proof (HSP (48, F) ltac:(unfold vr_sl3; cbn; tauto)) as H. cbn [fst snd] in H.
  intros kk Hkk. rewrite KSt; [exact (H kk Hkk) | lia]. }
split.
{ assert (HR3 : arodata_okP SEGS RLO RHI B (rdW W2 mem2))
    by exact (s31_ck_arodata _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR1 HJi HO2 HA2).
  pose proof (ROA ly2 S2 W2 mem2 md2 HAR2 HR3) as HRO3.
  destruct (RECC ly2 S2 W2 mem2 md2 HAR2) as (Hfl3 & Hgd3 & Herr3).
  split; [exact HR3|]. split; [exact (K.got_of_ro _ HRO3)|]. split; [exact HRO3|].
  split; [exact Hgd3|]. split; [exact Hfl3 | exact Herr3]. }
split.
{ destruct HRec' as (Q & HA & HOQ). exists Q. split; [exact HA|]. intros pn. rewrite HO3. apply HOQ. }
split.
{ rewrite HO3. intros H. destruct (HO'1 _ H) as [H1 | H1]; [exact (HnD H1) | exact (H1 (HTSc _ HdT))]. }
split.
{ apply NoDup_Permutation.
  - exact (K.ablocks_nodup B _ _ _ _ _ HAR2).
  - apply K.nodup_app_intro; [unfold O3; apply NoDup_nodup | exact HNDT |].
    intros pn H1 H2. rewrite HO3 in H1. destruct (HO'1 _ H1) as [H3 | H3]; [exact (HO2T _ H3 H2) | exact (H3 (HTSc _ H2))].
  - intros pn. split.
    + intros H. destruct (Hall pn H) as [(H1 & H2) | H1].
      * apply in_or_app. right. apply (Permutation_in _ HPERM) in H1. apply in_app_iff in H1 as [H1 | H1];
        [exact (False_ind _ (H2 H1)) | exact H1].
      * apply in_or_app. left. rewrite HO3. exact H1.
    + intros H. apply in_app_iff in H as [H | H].
      * rewrite HO3 in H. exact (rec_repA_in_blocks B _ _ _ _ _ _ HRec' H).
      * apply Hkeep; [exact (HTSc _ H) | intros H1; exact (HO2T _ H1 H)]. }
exact (s31_ck_quit _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR1 HJi HO2 _ (K.aval_mem_eq _ _ _ _ _ Eq1 HQ)).
Qed.

(* S31: the four pieces in sequence; the exits before sup_after_reply are at the entry's own FP state *)
Lemma vr_s31 : vr_s31_stmt B MT.
Proof.
intros e W cf HE HAR.
eapply SRr_bind; [exact (s31_p1 e W cf HE HAR)|].
cbv beta. intros W1 c1 _ H1.
eapply SRr_bind; [exact (s31_p2 e W1 c1 HE H1)|].
cbv beta. intros W2 c2 _ [H2 | H2]; [apply SRr_ret; exists fx; split; [apply fxrel_refl | exact H2]|].
eapply SRr_bind; [exact (s31_p3 e W2 c2 HE H2)|].
cbv beta. intros W3 c3 _ [H3 | H3]; [apply SRr_ret; exists fx; split; [apply fxrel_refl | exact H3]|].
exact (s31_p4 e W3 c3 HE H3).
Qed.

End e.
End f.
End d.
