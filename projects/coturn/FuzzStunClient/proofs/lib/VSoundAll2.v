(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VStep VStepMem VStepMemSound VCert VItab VDriverMatch VContract VDriver VSound VSoundCall VSoundAll VState2 VStepMem2 VCert2 VContract2 VDriverMatch2 VDriver2 VGamma2 VSound2 VSoundStep2 VContract2Iface VSoundContract2 VSoundMatch2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition VSTEP2_iface (SEGS : list Segment) : Prop :=
  forall P E mem0 rom A i succs nu regs mem (pc : word) w,
    params_ok2 SEGS P ->
    vstep2 P A i = VR2_next succs ->
    gamma2 SEGS P E mem0 A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.

(* [comment removed for export] *)

Definition unit_okS2 (SEGS : list Segment) (G : genv2) (rom : word -> option byte) (V : vunit2) : Prop :=
  unit_static_ok2 G (unit_params2 G V) V = None /\ unit_ok2 SEGS G rom V.

(* [comment removed for export] *)
Definition CALL_iface (SEGS : list Segment) (G : genv2) (rom : word -> option byte) : Prop :=
  forall done U E mem0 mem_e,
    Forall (unit_okS2 SEGS G rom) done ->
    params_ok2 SEGS (ge2_P0 G) ->
    params_ok2 SEGS (unit_params2 G U) ->
    unit_static_ok2 G (unit_params2 G U) U = None ->
    (forall A i succs nu regs mem (pc : word) w,
       vstep2 (unit_params2 G U) A i = VR2_next succs ->
       gamma2 SEGS (unit_params2 G U) E mem0 A nu regs mem -> vs2_pc A = bv_unsigned pc ->
       fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
       step_post2 SEGS (unit_params2 G U) E mem0 A nu succs regs mem pc rom) ->
    forall A (rd : reg) (imm : bv 21) vs succs nu regs mem (pc : word) w,
      do_call2 (mk_denv2 G done U) A (wrap64 (vs2_pc A + bv_signed imm)) (npc_of (v1 A)) vs = SN2 succs ->
      vs <> [] -> vs = call_variants2 (mk_denv2 G done U) (vs2_pc A) (wrap64 (vs2_pc A + bv_signed imm)) ->
      rz rd = 1 ->
      (FIRST_FRESH2 <= vs2_next A)%positive ->
      gammaE SEGS G U E mem0 mem_e A nu regs mem -> vs2_pc A = bv_unsigned pc ->
      fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Jal rd imm, 4) ->
      dstep_post2 SEGS G rom U E mem0 mem_e A succs nu regs pc mem.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ctab_ok2 (SEGS : list Segment) (G : genv2) (rom : word -> option byte) : Prop :=
  forall U E mem0,
    params_ok2 SEGS (unit_params2 G U) ->
    ctab_sound2 SEGS (unit_params2 G U) E mem0 rom (ge2_CI G) (ge2_ctab G).

Definition genv_ok2 (SEGS : list Segment) (G : genv2) (rom : word -> option byte) : Prop :=
  ge2_ranks G = true
  /\ itab_ok SEGS (ge2_itab G)
  /\ params_ok2 SEGS (ge2_P0 G)
  /\ ctab_ok2 SEGS G rom.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma unit_static_ok2_wsets G P U :
  unit_static_ok2 G P U = None ->
  forallb (fun r : Z * Z => Z.leb (- vp_frame (p1 P)) (fst r) && Z.leb (snd r) 0 && Z.leb (u_sp (u1 U)) (fst r)) (u_wstack (u1 U)) = true
  /\ forallb (fun c : Z * Z => in_cells (vp_fcells (p1 P)) (fst c) (snd c)) (vp_wcells (p1 P)) = true
  /\ (Z.ltb 0 (u_sp (u1 U)) || Z.ltb (u_sp (u1 U)) (- vp_frame (p1 P))) = false
  /\ forallb (fun w : Z * (Z * Z) => Z.leb 0 (fst w) && Z.ltb (fst w) 8 && Z.leb (fst (snd w)) (snd (snd w))) (u2_wrgn U) = true.
Proof.
  unfold unit_static_ok2.
  destruct (cstate2_ok P (u2_pre U) && cstate2_iface_b (u2_pre U) && wrgn_ok U (u2_pre U)); [|discriminate].
  destruct (pre_canonical2 G P U); [|discriminate].
  destruct (forallb _ (u2_cuts U)); [|discriminate].
  destruct (pc_ok (u_entry (u1 U))); [|discriminate].
  destruct (forallb _ (u2_exits U)); [|discriminate].
  cbn [negb].
  destruct (ge2_ranks G && negb _); [discriminate|].
  destruct (forallb (fun r : Z * Z => Z.leb (- vp_frame (p1 P)) (fst r) && Z.leb (snd r) 0 && Z.leb (u_sp (u1 U)) (fst r)) (u_wstack (u1 U))); [|discriminate].
  destruct (forallb (fun c : Z * Z => in_cells (vp_fcells (p1 P)) (fst c) (snd c)) (vp_wcells (p1 P))); [|discriminate].
  destruct (Z.ltb 0 (u_sp (u1 U)) || Z.ltb (u_sp (u1 U)) (- vp_frame (p1 P))); [discriminate|].
  destruct (mod8_ok P U); [|discriminate].
  destruct (forallb (fun w : Z * (Z * Z) => Z.leb 0 (fst w) && Z.ltb (fst w) 8 && Z.leb (fst (snd w)) (snd (snd w))) (u2_wrgn U)); [|discriminate].
  auto.
Qed.

Lemma unit_params2_ok SEGS G U :
  params_ok2 SEGS (ge2_P0 G) ->
  unit_static_ok2 G (unit_params2 G U) U = None ->
  params_ok2 SEGS (unit_params2 G U).
Proof.
  intros PO ST.
  destruct (unit_static_ok2_wsets _ _ _ ST) as (W1 & W2 & W3 & W4).
  destruct PO as (P1 & Psh & Pfr16 & Pk & Pz & Pw & Pfs & Pnoz & Pzs).
  assert (P1' : params_ok SEGS (p1 (unit_params2 G U))).
  { destruct P1 as (Pfr & Psphi & Psegs & Pfc & Pwc & Pws & Ppr & Prom).
    unfold params_ok, unit_params2 in *. cbn [p1 vp_frame vp_wstack vp_wcells vp_fcells vp_segs vp_pristine vp_rom vp_nmax vp_splo vp_sphi] in *.
    split; [exact Pfr|]. split; [exact Psphi|]. split; [exact Psegs|]. split; [exact Pfc|]. split; [|split; [|split; [exact Ppr|exact Prom]]].
    - intros c Hc. rewrite forallb_forall in W2. specialize (W2 _ Hc). cbn beta in W2.
      destruct (in_cells_sound _ _ _ W2) as (f & Hf & H1 & H2). exists f. auto.
    - intros r [<-|Hr].
      + cbn [fst snd]. apply Bool.orb_false_elim in W3 as [W3a W3b]. apply Z.ltb_ge in W3a. apply Z.ltb_ge in W3b. lia.
      + rewrite forallb_forall in W1. specialize (W1 _ Hr). cbn beta in W1.
        apply andb_prop in W1 as [W1 _]. apply andb_prop in W1 as [Wa Wb]. apply Z.leb_le in Wa. apply Z.leb_le in Wb. lia. }
  unfold params_ok2. unfold unit_params2 in *.
  cbn [p1 vp_frame vp_fcells vp_splo vp_shoff vp_kcells vp_kruns vp_fzones vp_fs vp_datal vp_wrgn] in *.
  split; [exact P1'|]. split; [exact Psh|]. split; [exact Pfr16|]. split; [exact Pk|]. split; [exact Pz|]. split; [|split; [exact Pfs|split; [exact Pnoz|exact Pzs]]].
  intros i lo hi Hin. rewrite forallb_forall in W4. specialize (W4 _ Hin). cbn [fst snd] in W4.
  apply andb_prop in W4 as [W4 W4c]. apply andb_prop in W4 as [W4a W4b].
  apply Z.leb_le in W4a. apply Z.ltb_lt in W4b. apply Z.leb_le in W4c. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section All2.
  Variable SEGS : list Segment.
  Variable G : genv2.
  Variable rom : word -> option byte.
  Hypothesis GOK : genv_ok2 SEGS G rom.
  Hypothesis VSTEP2S : VSTEP2_iface SEGS.
  Hypothesis CALLS : CALL_iface SEGS G rom.

  Lemma check_unit2_static done U :
    check_unit2 G done U = R2Ok -> unit_static_ok2 G (unit_params2 G U) U = None.
  Proof.
    unfold check_unit2. change (de2_P (mk_denv2 G done U)) with (unit_params2 G U).
    destruct (unit_static_ok2 G (unit_params2 G U) U); [discriminate|reflexivity].
  Qed.

  Theorem check_unit2_okS done U :
    Forall (unit_okS2 SEGS G rom) done ->
    check_unit2 G done U = R2Ok ->
    unit_okS2 SEGS G rom U.
  Proof.
    intros DONE CHK. destruct GOK as (RANKS & ITAB & PO0 & CTAB).
    pose proof (check_unit2_static _ _ CHK) as STATIC.
    pose proof (unit_params2_ok SEGS G U PO0 STATIC) as PO.
    split; [exact STATIC|].
    intros E mem0 nu regs mem RET HG.
    assert (VSTEP2 : forall A i succs nu regs mem (pc : word) w,
      vstep2 (unit_params2 G U) A i = VR2_next succs ->
      gamma2 SEGS (unit_params2 G U) E mem0 A nu regs mem -> vs2_pc A = bv_unsigned pc ->
      fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
      step_post2 SEGS (unit_params2 G U) E mem0 A nu succs regs mem pc rom).
    { intros A i succs nu1 regs1 mem1 pc w Hv HG1 Hpc Hf He Hd. eapply VSTEP2S; eauto. }
    assert (MATCH := fun A X pc ctx sigma nu0 regs0 mem1 => match_state2_sound_cut SEGS (unit_params2 G U) E mem0 A X pc ctx sigma nu0 regs0 mem1 PO).
    assert (FI0 : fl_inv G U E (load_cstate2 (unit_params2 G U) (u2_pre U) (u_entry (u1 U)) []) nu mem mem).
    { apply fl_inv_entry. apply (own_flags_iface G U).
      unfold unit_static_ok2 in STATIC.
      destruct (cstate2_ok (unit_params2 G U) (u2_pre U) && cstate2_iface_b (u2_pre U) && wrgn_ok U (u2_pre U)) eqn:C0; [|discriminate].
      apply andb_prop in C0 as [C0 _]. apply andb_prop in C0 as [_ C0]. exact C0. }
    eapply (check_unit2_sound_E SEGS G rom done U E mem0 mem RANKS); [|exact STATIC|exact MATCH|exact CHK|split; [exact HG|exact FI0]].
    eapply (dstep2_sound SEGS G rom done U E mem0 mem ITAB RET STATIC VSTEP2).
    - eapply (contract2_sound SEGS G rom done U E mem0 mem); [|exact RET|exact STATIC|exact VSTEP2|exact MATCH].
      apply CTAB. exact PO.
    - eapply (CALLS done U E mem0 mem DONE PO0 PO STATIC VSTEP2).
    - exact MATCH.
  Qed.

  Lemma check_units2_sound : forall l done,
    Forall (unit_okS2 SEGS G rom) done ->
    check_units2 G done l = R2Ok ->
    Forall (unit_okS2 SEGS G rom) l.
  Proof.
    induction l as [|U t IH]; intros done DONE CHK; [constructor|].
    cbn [check_units2] in CHK.
    destruct (check_unit2 G done U) eqn:CU; [|discriminate].
    pose proof (check_unit2_okS done U DONE CU) as HU.
    constructor; [exact HU|].
    eapply (IH (done ++ [U])%list); [|exact CHK].
    apply Forall_app. split; [exact DONE|]. constructor; [exact HU|constructor].
  Qed.

  Theorem check_cert2_sound C : check_cert2 G C = R2Ok -> Forall (unit_okS2 SEGS G rom) C.
  Proof. intros CHK. eapply (check_units2_sound C []); [constructor|exact CHK]. Qed.
End All2.
