(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VStep VStepMem VStepSound VStepMemSound VStepMemSound2 VCert VItab VDriverMatch VContract VDriver VSoundMatch VSound VSoundStep VSoundCall VSoundCall2 VSoundContract.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ctab_ok (SEGS : list Segment) (G : genv) (rom : word -> option byte) : Prop :=
  forall U E mem0,
    params_ok SEGS (unit_params G U) ->
    ctab_sound SEGS (unit_params G U) E mem0 rom (ge_CI G) (ge_ctab G).

Definition genv_ok (SEGS : list Segment) (G : genv) (rom : word -> option byte) : Prop :=
  ge_ranks G = true
  /\ itab_ok SEGS (ge_itab G)
  /\ params_ok SEGS (ge_P0 G)
  /\ ctab_ok SEGS G rom.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma unit_static_ok_wsets G P U :
  unit_static_ok G P U = None ->
  forallb (fun r : Z * Z => Z.leb (- vp_frame P) (fst r) && Z.leb (snd r) 0 && Z.leb (u_sp U) (fst r)) (u_wstack U) = true
  /\ forallb (fun c : Z * Z => in_cells (vp_fcells P) (fst c) (snd c)) (vp_wcells P) = true
  /\ (Z.ltb 0 (u_sp U) || Z.ltb (u_sp U) (- vp_frame P)) = false.
Proof.
  unfold unit_static_ok.
  destruct (cstate_ok P (u_pre U)); [|discriminate].
  destruct (pre_canonical G U); [|discriminate].
  destruct (forallb (fun c => pc_ok (cut_pc c) && forallb (cstate_ok P) (cut_states c)) (u_cuts U)); [|discriminate].
  destruct (pc_ok (u_entry U)); [|discriminate].
  destruct (forallb (cstate_ok P) (u_exits U)); [|discriminate].
  cbn [negb].
  destruct (ge_ranks G && negb (forallb (fun c => Nat.eqb (length (cut_ranks c)) (length (cut_states c)) && rank_nonneg c) (u_cuts U))); [discriminate|].
  destruct (forallb (fun r : Z * Z => Z.leb (- vp_frame P) (fst r) && Z.leb (snd r) 0 && Z.leb (u_sp U) (fst r)) (u_wstack U)); [|discriminate].
  destruct (forallb (fun c : Z * Z => in_cells (vp_fcells P) (fst c) (snd c)) (vp_wcells P)); [|discriminate].
  destruct (Z.ltb 0 (u_sp U) || Z.ltb (u_sp U) (- vp_frame P)); [discriminate|].
  auto.
Qed.

Lemma unit_params_ok SEGS G U :
  params_ok SEGS (ge_P0 G) ->
  unit_static_ok G (unit_params G U) U = None ->
  params_ok SEGS (unit_params G U).
Proof.
  intros PO ST.
  destruct (unit_static_ok_wsets _ _ _ ST) as (W1 & W2 & W3).
  destruct PO as (Pfr & Psphi & Psegs & Pfc & Pwc & Pws & Ppr & Prom).
  unfold params_ok, unit_params in *. cbn [vp_frame vp_wstack vp_wcells vp_fcells vp_segs vp_pristine vp_rom vp_nmax vp_splo vp_sphi] in *.
  split; [exact Pfr|]. split; [exact Psphi|]. split; [exact Psegs|]. split; [exact Pfc|]. split; [|split; [|split; [exact Ppr|exact Prom]]].
  - intros c Hc. rewrite forallb_forall in W2. specialize (W2 _ Hc). cbn beta in W2.
    destruct (in_cells_sound _ _ _ W2) as (f & Hf & H1 & H2). exists f. auto.
  - intros r [<-|Hr].
    + cbn [fst snd]. apply Bool.orb_false_elim in W3 as [W3a W3b]. apply Z.ltb_ge in W3a. apply Z.ltb_ge in W3b. lia.
    + rewrite forallb_forall in W1. specialize (W1 _ Hr). cbn beta in W1.
      apply andb_prop in W1 as [W1 _]. apply andb_prop in W1 as [Wa Wb]. apply Z.leb_le in Wa. apply Z.leb_le in Wb. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section OneUnit.
  Variable SEGS : list Segment.
  Variable G : genv.
  Variable rom : word -> option byte.
  Hypothesis GOK : genv_ok SEGS G rom.

  Lemma check_unit_static done U :
    check_unit G done U = ROk -> unit_static_ok G (unit_params G U) U = None.
  Proof.
    unfold check_unit. change (de_P (mk_denv G done U)) with (unit_params G U).
    destruct (unit_static_ok G (unit_params G U) U); [discriminate|reflexivity].
  Qed.

  Theorem check_unit_okS done U :
    Forall (unit_okS SEGS G rom) done ->
    check_unit G done U = ROk ->
    unit_okS SEGS G rom U.
  Proof.
    intros DONE CHK. destruct GOK as (RANKS & ITAB & PO0 & CTAB).
    pose proof (check_unit_static _ _ CHK) as STATIC.
    pose proof (unit_params_ok SEGS G U PO0 STATIC) as PO.
    split; [exact STATIC|].
    intros E mem0 nu regs mem RET HG.
    assert (VSTEP : forall A i succs nu regs mem (pc : word) w,
      vstep (unit_params G U) A i = VR_next succs ->
      gamma SEGS (unit_params G U) E mem0 A nu regs mem -> vs_pc A = bv_unsigned pc ->
      fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
      step_post SEGS (unit_params G U) E mem0 A nu succs regs mem pc rom).
    { intros A i succs nu1 regs1 mem1 pc w Hv HG1 Hpc Hf He Hd.
      exact (vstep_sound SEGS (unit_params G U) E mem0 PO A nu1 regs1 mem1 pc rom w i succs HG1 Hpc Hf He Hd Hv). }
    eapply (check_unit_sound_E SEGS G rom done U E mem0 RANKS); [|exact STATIC|exact CHK|exact HG].
    eapply (dstep_sound SEGS G rom done U E mem0 ITAB RET STATIC VSTEP).
    - eapply (contract_sound SEGS G rom done U E mem0); [|exact RET|exact STATIC|exact VSTEP].
      apply CTAB. exact PO.
    - eapply (call_sound SEGS G rom done U E mem0 DONE PO VSTEP).
  Qed.
End OneUnit.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma check_units_sound SEGS G rom :
  genv_ok SEGS G rom ->
  forall l done,
    Forall (unit_okS SEGS G rom) done ->
    check_units G done l = ROk ->
    Forall (unit_okS SEGS G rom) l.
Proof.
  intros GOK. induction l as [|U t IH]; intros done DONE CHK; [constructor|].
  cbn [check_units] in CHK.
  destruct (check_unit G done U) eqn:CU; [|discriminate].
  pose proof (check_unit_okS SEGS G rom GOK done U DONE CU) as HU.
  constructor; [exact HU|].
  eapply (IH (done ++ [U])%list); [|exact CHK].
  apply Forall_app. split; [exact DONE|]. constructor; [exact HU|constructor].
Qed.

Theorem check_cert_sound SEGS G rom C :
  genv_ok SEGS G rom -> check_cert G C = ROk -> Forall (unit_okS SEGS G rom) C.
Proof.
  intros GOK CHK. eapply (check_units_sound SEGS G rom GOK C []); [constructor|exact CHK].
Qed.

Corollary check_cert_unit_ok SEGS G rom C U :
  genv_ok SEGS G rom -> check_cert G C = ROk -> In U C -> unit_ok SEGS G rom U.
Proof.
  intros GOK CHK HU. pose proof (check_cert_sound SEGS G rom C GOK CHK) as ALL.
  rewrite Forall_forall in ALL. exact (proj2 (ALL U HU)).
Qed.
