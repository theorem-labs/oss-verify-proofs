(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the vDSO layer: the vDSO step cases of sstep refuted under Hnv : vdso_text_seg segs = None; ms_resv cleared on system-call return, so regraft takes the advanced state's reservation; RomBase.sys_rob at the nodes and star_rob at the loop exit carried across equivalent states). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem Require VdsoCommuteSys.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe4Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qe4Y.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Notation cfg_eqv := (Qe4Y.cfg_eqv).
Notation sstep := (Run.sstep_cfg segs (alloc_only_cfg false)).
(* LPS 727298f3: the step has three vDSO arms; over a segment list with no vDSO text no pc is an exported
   entry ([vdso_entry_fn_none_of_no_text]), so those arms never fire and the successor stays deterministic *)
Hypothesis Hnv : vdso_text_seg segs = None.

(* LPS 727298f3: returning from a system call clears the load reservation ([advance_past_svc] sets
   [ms_resv := None]), so the regrafted state takes the reservation of the advanced state [d] *)
Definition regraft (d cms : machine_state) : machine_state :=
{| ms_regs := bvmap_set (10 : reg) (reg_get (ms_regs d) (10 : reg)) (ms_regs cms);
ms_fregs := ms_fregs cms;
ms_pc_val := ms_pc_val d;
ms_svc_pending := None;
ms_resv := ms_resv d; ms_fcsr := ms_fcsr cms;
ms_mem := ms_mem d;
ms_rom := ms_rom cms |}.

Definition nx_tr (c' : config) (d : config) : config :=
match ms_svc_pending (cfg_ms c') with
| None => match mi_account_step segs (cfg_ms c') (cfg_model c') with
| MachineOk (ms1, md1) => mkCfg ms1 md1
| _ => d
end
| Some _ =>
match ms_svc_pending (cfg_ms d) with
| Some _ => mkCfg (cfg_ms c') (cfg_model d)
| None => mkCfg (regraft (cfg_ms d) (cfg_ms c')) (cfg_model d)
end
end.

#[using="Type"] Lemma advance_pending : forall ms eff, ms_svc_pending (advance_past_svc (apply_effect ms eff)) = None.
Proof. intros. reflexivity. Qed.

#[using="Type"] Lemma advance_regraft : forall ms cms eff, ms_eqv ms cms ->
advance_past_svc (apply_effect cms eff) = regraft (advance_past_svc (apply_effect ms eff)) cms.
Proof.
intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro'] eff (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
unfold advance_past_svc, apply_effect, regraft, set_reg, ms_pc.
replace (bv_eqb (10 : reg) 0) with false by reflexivity. cbn -[reg_get bvmap_set apply_writes apply_copies apply_zeros apply_unmaps bv_add].
rewrite reg_get_set_same. reflexivity.
Qed.

#[using="Type"] Lemma advance_eqv : forall ms cms eff, ms_eqv ms cms ->
ms_eqv (advance_past_svc (apply_effect ms eff)) (advance_past_svc (apply_effect cms eff)).
Proof. intros ms cms eff H. apply advance_past_svc_eqv, apply_effect_eqv, H. Qed.

#[using="Type"] Lemma halted_materialize : forall md accs md', materialize_model_accesses md accs = Some md' -> m_halted md' = m_halted md.
Proof.
intros md accs md' H. pose proof (materialize_model_accesses_frame md accs md' H) as (_ & _ & _ & _ & _ & P & _).
unfold m_halted. rewrite P. reflexivity.
Qed.

#[using="Type Hnv"] Lemma sstep_tr : forall c c' e d, cfg_eqv c c' -> sstep c e (SNext d) ->
sstep c' e (SNext (nx_tr c' d)) /\ cfg_eqv d (nx_tr c' d).
Proof.
intros [ms md] [cms cmd] e d [Heqv Hmd] Hst; simpl in Heqv, Hmd; subst cmd.
pose proof Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
pose proof (mi_account_step_eqv segs ms cms md Heqv) as Hres.
inversion Hst; subst.
all: try (exfalso; match goal with HV : vdso_entry_fn segs _ = Some _ |- _ =>
  rewrite (VdsoCommuteSys.vdso_entry_fn_none_of_no_text segs _ Hnv) in HV; discriminate end).
-
lazymatch goal with HS : mi_account_step _ _ _ = MachineOk _, HP : ms_svc_pending ms = None |- _ =>
rewrite HS in Hres; destruct (mi_account_step segs cms md) as [[cms1 md1]| |] eqn:E; simpl in Hres; try contradiction;
destruct Hres as [Hres <-];
unfold nx_tr; cbn [cfg_ms cfg_model]; rewrite <- Hsvc, HP, E;
split; [apply sstep_cfg_instr; auto; congruence| split; [exact Hres| reflexivity]] end.
-
lazymatch goal with HP : ms_svc_pending ms = Some ?x8, HY : syscall_spec _ _ (Ok ?eff ?model' _), HM : materialize_model_accesses _ _ = Some ?md2, HH : m_halted ?model' = None |- _ =>
unfold nx_tr; cbn [cfg_ms cfg_model]; rewrite <- Hsvc, HP; rewrite advance_pending;
rewrite <- (advance_regraft ms cms eff Heqv); split;
[ apply (sstep_cfg_syscall segs (alloc_only_cfg false) cms md x8 eff model' md2 e);
[assumption| congruence| rewrite <- (sys_input_eqv segs ms cms x8 Heqv); assumption
| rewrite <- (sys_input_eqv segs ms cms x8 Heqv); assumption| assumption| assumption]
| split; [apply advance_eqv; exact Heqv| reflexivity] ] end.
-
lazymatch goal with HP : ms_svc_pending ms = Some ?x8, HY : syscall_spec _ _ (Ok ?eff ?model' ?evs), HH : m_halted ?model' = Some ?code |- _ =>
unfold nx_tr; cbn [cfg_ms cfg_model]; rewrite <- Hsvc, !HP; split;
[ apply (sstep_cfg_exit segs (alloc_only_cfg false) cms md x8 eff model' evs code);
[assumption| congruence| rewrite <- (sys_input_eqv segs ms cms x8 Heqv); assumption| assumption| assumption]
| split; [exact Heqv| reflexivity] ] end.
-
lazymatch goal with HP : ms_svc_pending ms = Some ?x8, HY : syscall_spec _ _ (Ok ?eff ?model' ?evs), HKd : m_killed ?model' = Some ?sig |- _ =>
unfold nx_tr; cbn [cfg_ms cfg_model]; rewrite <- Hsvc, !HP; split;
[ apply (sstep_cfg_killed segs (alloc_only_cfg false) cms md x8 eff model' evs sig);
[assumption| congruence| rewrite <- (sys_input_eqv segs ms cms x8 Heqv); assumption| assumption]
| split; [exact Heqv| reflexivity] ] end.
Qed.

#[using="Type Hnv"] Lemma sstep_tr_back : forall c c' e st, cfg_eqv c c' -> sstep c' e st ->
(st = SError /\ sstep c e SError) \/ (exists d, sstep c e (SNext d) /\ st = SNext (nx_tr c' d)).
Proof.
intros [ms md] [cms cmd] e st [Heqv Hmd] Hst; simpl in Heqv, Hmd; subst cmd.
pose proof Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
pose proof (mi_account_step_eqv segs ms cms md Heqv) as Hres.
inversion Hst; subst.
all: try (exfalso; match goal with HV : vdso_entry_fn segs _ = Some _ |- _ =>
  rewrite (VdsoCommuteSys.vdso_entry_fn_none_of_no_text segs _ Hnv) in HV; discriminate end).
- right. lazymatch goal with HS : mi_account_step _ cms _ = MachineOk (?cms1, ?md1), HP : ms_svc_pending cms = None |- _ =>
destruct (mi_account_step segs ms md) as [[ms1 mdx]| |] eqn:E; rewrite HS in Hres; simpl in Hres; try contradiction;
destruct Hres as [Hres ->]; exists (mkCfg ms1 md1); split; [apply sstep_cfg_instr; auto; congruence|];
unfold nx_tr; cbn [cfg_ms cfg_model]; rewrite HP, HS; reflexivity end.
- left. split; [reflexivity|]. lazymatch goal with HS : mi_account_step _ cms _ = MachineFault |- _ =>
destruct (mi_account_step segs ms md) as [[ms1 mdx]| |] eqn:E; rewrite HS in Hres; simpl in Hres; try contradiction end.
apply sstep_cfg_instr_fault; auto; congruence.
- left. split; [reflexivity|]. lazymatch goal with HS : mi_account_step _ cms _ = MachineUnmodeled |- _ =>
destruct (mi_account_step segs ms md) as [[ms1 mdx]| |] eqn:E; rewrite HS in Hres; simpl in Hres; try contradiction end.
apply sstep_cfg_instr_unmodeled; first [exact (VdsoCommuteSys.vdso_entry_fn_none_of_no_text segs _ Hnv) | auto; congruence].
- right. lazymatch goal with HP : ms_svc_pending cms = Some ?x8, HY : syscall_spec _ _ (Ok ?eff ?model' _), HM : materialize_model_accesses _ _ = Some ?md2, HH : m_halted ?model' = None |- _ =>
exists (mkCfg (advance_past_svc (apply_effect ms eff)) md2); split;
[ apply (sstep_cfg_syscall segs (alloc_only_cfg false) ms md x8 eff model' md2 e);
[assumption| congruence| rewrite (sys_input_eqv segs ms cms x8 Heqv); assumption
| rewrite (sys_input_eqv segs ms cms x8 Heqv); assumption| assumption| assumption]
| unfold nx_tr; cbn [cfg_ms cfg_model]; rewrite HP; rewrite advance_pending;
rewrite (advance_regraft ms cms eff Heqv); reflexivity ] end.
- left. split; [reflexivity|].
lazymatch goal with HP : ms_svc_pending cms = Some ?x8, HY : syscall_spec _ _ (Ok ?eff ?model' ?evs) |- _ =>
apply (sstep_cfg_syscall_materialization_fault segs (alloc_only_cfg false) ms md x8 eff model' evs);
[assumption| congruence| rewrite (sys_input_eqv segs ms cms x8 Heqv); assumption
| rewrite (sys_input_eqv segs ms cms x8 Heqv); assumption| assumption| assumption] end.
- right. lazymatch goal with HP : ms_svc_pending cms = Some ?x8, HY : syscall_spec _ _ (Ok ?eff ?model' ?evs), HH : m_halted ?model' = Some ?code |- _ =>
exists (mkCfg ms model'); split;
[ apply (sstep_cfg_exit segs (alloc_only_cfg false) ms md x8 eff model' evs code);
[assumption| congruence| rewrite (sys_input_eqv segs ms cms x8 Heqv); assumption| assumption| assumption]
| unfold nx_tr; cbn [cfg_ms cfg_model]; rewrite Hsvc, !HP; reflexivity ] end.
- right. lazymatch goal with HP : ms_svc_pending cms = Some ?x8, HY : syscall_spec _ _ (Ok ?eff ?model' ?evs), HKd : m_killed ?model' = Some ?sig |- _ =>
exists (mkCfg ms model'); split;
[ apply (sstep_cfg_killed segs (alloc_only_cfg false) ms md x8 eff model' evs sig);
[assumption| congruence| rewrite (sys_input_eqv segs ms cms x8 Heqv); assumption| assumption]
| unfold nx_tr; cbn [cfg_ms cfg_model]; rewrite Hsvc, !HP; reflexivity ] end.
- left. split; [reflexivity|].
lazymatch goal with HP : ms_svc_pending cms = Some ?x8 |- _ =>
apply (sstep_cfg_syscall_unmodeled segs (alloc_only_cfg false) ms md x8);
[assumption| congruence| rewrite (sys_input_eqv segs ms cms x8 Heqv); assumption] end.
Qed.

#[using="Type Hnv"] Lemma node_ok_tr : forall c c' (I : Type) evs nx, cfg_eqv c c' -> node_ok segs c I evs nx ->
node_ok segs c' I evs (fun i => nx_tr c' (nx i)) /\ (forall i, cfg_eqv (nx i) (nx_tr c' (nx i))).
Proof.
intros c c' I evs nx Heqv [N1 N2]. split; [split|].
- intros i. exact (proj1 (sstep_tr c c' (evs i) (nx i) Heqv (N1 i))).
- intros e st Hst. destruct (sstep_tr_back c c' e st Heqv Hst) as [[-> HE]|(d & Hd & ->)].
+ destruct (N2 e SError HE) as (i & _ & Hi). discriminate Hi.
+ destruct (N2 e (SNext d) Hd) as (i & -> & Hi). injection Hi as ->. exists i. split; reflexivity.
- intros i. exact (proj2 (sstep_tr c c' (evs i) (nx i) Heqv (N1 i))).
Qed.

Definition eclo (V : config -> Prop) (c : config) : Prop := exists c0, V c0 /\ cfg_eqv c0 c.

(* LPS 727298f3: [RomBase.sys_rob] and the loop exit's [star_rob] carry across equivalent states (the
   system-call input reads only what [ms_eqv] keeps equal) *)
#[using="Type"] Lemma wrom_eqv : forall ms ms' r, ms_eqv ms ms' -> ms_eqv (RomBase.wrom ms r) (RomBase.wrom ms' r).
Proof.
intros ms ms' r Hm. unfold ms_eqv in *. destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
unfold RomBase.wrom. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
repeat split; first [exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6 | exact H7 | reflexivity].
Qed.

#[using="Type"] Lemma sys_rob_eqv : forall c c', cfg_eqv c c' -> RomBase.sys_rob segs c -> RomBase.sys_rob segs c'.
Proof.
intros [ms md] [ms' md'] [Hms Hmd] H r x8 Hr Hs v o. cbn [cfg_ms cfg_model] in *. subst md'.
pose proof Hms as (_ & _ & _ & Hsvc & _ & _ & _ & Hro).
rewrite <- (sys_input_eqv segs (RomBase.wrom ms r) (RomBase.wrom ms' r) x8 (wrom_eqv ms ms' r Hms)).
rewrite <- (sys_input_eqv segs ms ms' x8 Hms).
apply (H r x8); cbn [cfg_ms]; [rewrite Hro; exact Hr | rewrite Hsvc; exact Hs].
Qed.

#[using="Type"] Lemma star_rob_eqv : forall c c1, star_rob segs c c1 ->
forall c', cfg_eqv c c' -> exists c1', star_rob segs c' c1' /\ cfg_eqv c1 c1'.
Proof.
intros c c1 H. induction H as [c | c c2 c3 Hst Hrob Hstar IH]; intros c' Heqv.
- exists c'. split; [apply srob_refl | exact Heqv].
- destruct (sstep_cfg_eqv segs c c' [] (SNext c2) Heqv Hst) as (X' & Hst' & HX).
destruct X' as [c2'|]; simpl in HX; [|contradiction].
destruct (IH c2' HX) as (c3' & Hstar' & H3).
exists c3'. split; [|exact H3].
exact (srob_step segs c' c2' c3' Hst' (sys_rob_eqv c c' Heqv Hrob) Hstar').
Qed.

#[using="Type Hnv"] Theorem realizes_eqv_mut :
(forall c T, realizes segs c T -> forall c', cfg_eqv c c' -> realizes segs c' T)
/\ (forall V T c, lbody segs V T c -> forall c', cfg_eqv c c' -> lbody segs (eclo V) T c').
Proof.
apply realizes_lbody_mutind.
-  intros c I evs nx T i0 Hnode Hrob Hcont IH c' Heqv.
destruct (node_ok_tr c c' I evs nx Heqv Hnode) as [Hnode' Hnx].
apply (rz_node segs c' I evs (fun i => nx_tr c' (nx i)) T i0 Hnode' (sys_rob_eqv c c' Heqv Hrob)).
intros i. apply (IH i). apply Hnx.
-  intros c Hh [ms' md'] [_ Hmd]. apply rz_halt. cbn in Hmd |- *. rewrite <- Hmd. exact Hh.
-  intros c T T' H IH Heq c' Heqv. eapply rz_conseq; [apply IH; exact Heqv| exact Heq].
-  intros V T c c_e HV Hbody IHbody Hstar He IHe c' Heqv.
destruct (star_rob_eqv c c_e Hstar c' Heqv) as (c_e' & Hstar' & He').
apply (rz_loop segs (eclo V) T c' c_e').
 + exists c. split; [exact HV| exact Heqv].
 + intros c1 (c0 & HV0 & H01). exact (IHbody c0 HV0 c1 H01).
 + exact Hstar'.
 + apply IHe. exact He'.
-  intros V T c H IH c' Heqv. apply lb_exit. apply IH. exact Heqv.
-  intros V T c I nx k Hnode Hrob Hk IHk Hv c' Heqv.
destruct (node_ok_tr c c' I (fun _ => []) nx Heqv Hnode) as [Hnode' Hnx].
apply (lb_node segs (eclo V) T c' I (fun i => nx_tr c' (nx i)) k Hnode' (sys_rob_eqv c c' Heqv Hrob)).
 + intros i Hi. apply (IHk i Hi). apply Hnx.
 + intros i Hi. exists (nx i). split; [exact (Hv i Hi)| apply Hnx].
Qed.

#[using="Type Hnv"] Theorem realizes_eqv : forall c c' T, cfg_eqv c c' -> realizes segs c T -> realizes segs c' T.
Proof. intros c c' T Heqv H. exact (proj1 realizes_eqv_mut c T H c' Heqv). Qed.

#[using="Type Hnv"] Theorem realizes_canon : forall R F pc fc rv m ro md T,
realizes segs (mkCfg (MS (canonR R) F pc fc rv m ro) md) T ->
realizes segs (mkCfg (MS R F pc fc rv m ro) md) T.
Proof.
intros R F pc fc rv m ro md T H. eapply realizes_eqv; [| exact H].
split; [| reflexivity]. apply ms_eqv_sym. apply ms_eqv_canon.
Qed.
End WithSegs.
