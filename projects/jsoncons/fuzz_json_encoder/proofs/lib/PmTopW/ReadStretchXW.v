(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core Pm6PlanKit PmLibDefs PmLibSpecs PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit CutL5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require Import TopKit ReadKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_read_a_xsrc Cut_read_b_xsrc Cut_read_c_xsrc Cut_read_d_xsrc.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require Import ReadStretchX.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Module RSW.
Import RS.
Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

(* [comment removed for export] *)
Ltac hv_open cp plans off gl pn sp0 R M fx model K Hh Hl Hfp H2 Hpins :=
  let E := fresh "E" in set (E := TK.hvE sp0 R (RK.ghl gl));
  assert (U2 : bv_unsigned (ev E 2) = sp0) by (apply TK.hvE_sp; lia);
  apply (TK.stretch_cps FPM cp fx E R M model K plans Hh Hl Hfp);
  [ apply (RK.regs_ok_hv _ off pn); [vm_compute; reflexivity | lia | lia | first [exact H2 | rewrite Z.add_0_r; exact H2] | Hpins] | | ].
Ltac no_pins := let q := fresh in let z := fresh in intros q z [].
(* [comment removed for export] *)
Ltac reg_atom E sp0 R v r Hr := let U := fresh "Ur" in
  lazymatch type of Hr with getr _ _ = Z_to_bv 64 ?z =>
    assert (U : bv_unsigned (ev E v) = z) by (change v with (32 + ridx (r : reg))%nat; subst E; apply (RK.hv_reg_u sp0 R _ r z Hr); lia) end.
Ltac gh_atom E sp0 R v k z := let U := fresh "Ug" in
  assert (U : bv_unsigned (ev E v) = z) by (change v with (64 + k)%nat; subst E; eapply RK.ghl_u; [reflexivity | lia]).
(* [comment removed for export] *)
Ltac leaf_open Hag HLF E' nxv :=
  assert (Hag64 : env_agree 64 _ E') by (eapply CC.env_agree_le; [exact Hag | vm_compute; lia]);
  repeat match goal with U : bv_unsigned (ev ?E ?v) = ?z |- _ =>
           lazymatch E with E' => fail | _ => let U' := fresh "V" in assert (U' : bv_unsigned (ev E' v) = z) by (rewrite <- (proj1 Hag v) by (vm_compute; lia); exact U); clear U end end.


Ltac leaf_k k Hnth := destruct k as [|k]; [injection Hnth as <- | ].
Ltac leaf_end k Hnth := destruct k; discriminate Hnth.
Ltac leaves n k Hnth tac := lazymatch n with O => leaf_end k Hnth | S ?m => destruct k as [|k]; [injection Hnth as <-; tac | leaves m k Hnth tac] end.
Ltac probes_in HLF PF := pose proof (RK.leaf_probes _ _ _ _ _ _ HLF) as PF; vm_compute RK.probes in PF; cbn [RK.pfacts edenot] in PF.
Ltac w2z H := repeat match type of H with context [ev ?E ?v] => match goal with U : bv_unsigned (ev E v) = ?z |- _ => rewrite (RK.w_of_u _ _ U) in H end end.
Ltac hv_keeps HLF Hag64 sp0 R E' R' M M' qs := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; exact (TK.keeps_hv_sound _ _ sp0 R _ E' R' M M' qs r HLF eq_refl Hag64 Hr).
(* [comment removed for export] *)
Ltac llin HLF x := let x' := rr x in tk_lin HLF x'.
Ltac lreg HLF x := let x' := rr x in tk_reg HLF x'.
Ltac lkeep HLF Hag64 sp0 R x v r := let x' := rr x in let r' := rr r in tk_reg HLF x'; rewrite <- (proj1 Hag64 v) by lia; exact (TK.hvE_reg sp0 R _ r').
Ltac lcell64 HLF b off v := eapply (CL5.kword64_elim RSEGS); [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA b off) 8 v)); cbn; tauto | ev_start | ].
Ltac lcell32 HLF b off v := eapply TK.kword32_elim; [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA b off) 4 v)); cbn; tauto | ev_start | ].
Ltac lcell8 HLF b off v := eapply RK.kword8_elim; [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA b off) 1 v)); cbn; tauto | ev_start | ].
Ltac vlit := cbn [edenot]; apply u64_of_Z; lia.
Ltac vreg Hag64 sp0 R v r := let r' := rr r in cbn [edenot]; rewrite <- (proj1 Hag64 v) by lia; f_equal; exact (TK.hvE_reg sp0 R _ r').
Ltac vlin := apply CL5.u_lin; [lin_eval; rw_atoms; rewrite ?u64_of_Z by lia; lia | lia].
Ltac kw64 A0 z0 H := eapply CL5.kword64_intro with (A := A0) (z := z0); [ev_start | lia | lia | reflexivity | exact H].
Ltac kw32 A0 z0 H := eapply RK.kword32_intro with (A := A0) (z := z0); [ev_start | lia | lia | reflexivity | exact H].
Ltac kw8 A0 z0 H := eapply TK.kword8_intro with (A := A0) (z := z0); [ev_start | lia | lia | reflexivity | lia | exact H].
Ltac lframe HLF := apply (TK.frame_samem _ _ _ _ _ _ _ HLF); let a := fresh "a" in let Ha := fresh "Ha" in let Hk := fresh "Hk" in intros a Ha Hk; cbn [CC.cp_F]; tk_outside.
(* [comment removed for export] *)
Ltac lsame HLF M M' A0 e p D Ce Cp b ve vp :=
  assert (SAME : M' = M);
  [ eapply (RK.same_mem16 M M' A0 e p); [lia | lia | lframe HLF | exact (CC.lf_grows _ _ _ _ _ _ _ HLF) | exact D | exact Ce | | replace (A0 + 8) with (A0 - 512 + 520) by lia; ring_simplify (A0 - 512 + 520); exact Cp | ];
    [ lcell64 HLF b 512 ve; cbn [edenot]; assumption | replace (A0 + 8) with (A0 - 512 + 520) by lia; ring_simplify (A0 - 512 + 520); lcell64 HLF b 520 vp; cbn [edenot]; assumption ] | ].
(* [comment removed for export] *)
Ltac pf_z H := w2z H; rewrite ?RK.ext_s32, ?RK.ext_u8 in H by lia; rewrite ?RK.and_lit in H by lia;
  first [apply RK.w_inj in H; [| first [lia | apply RK.land_range; lia] | first [lia | apply RK.land_range; lia]] | apply RK.w_neq in H].
Ltac pf_all PF := repeat (let X := fresh "PFx" in destruct PF as [X PF]; pf_z X); clear PF.
Ltac pins45 H20 H21 := let q := fresh in let z := fresh in let X := fresh in intros q z [X|[X|[]]]; injection X as <- <-; [exact H20 | exact H21].

Lemma s_rn_r_psomew : forall (fx : FPState) R M model K sp1 Rr Ev code st dn mo p e,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 Rr -> getr R 8%bv = Z_to_bv 64 Ev -> pok Rr -> pok Ev -> getr R 20%bv = Z_to_bv 64 1 -> getr R 21%bv = Z_to_bv 64 2 ->
  getr R 19%bv = Z_to_bv 64 p -> getr R 22%bv = Z_to_bv 64 e -> 0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 ->
  L5.u32_at RSEGS M Ev code -> 0 <= code < 2 ^ 31 -> L5.u8_at RSEGS M (Rr + 528) st -> L5.u8_at RSEGS M (Rr + 532) dn -> L5.u8_at RSEGS M (Rr + 531) mo ->
  0 <= st <= 255 -> 0 <= dn <= 255 -> 0 <= mo <= 255 ->
  (code = 0 -> (p = e /\ st = 1) \/ (mo = 0 /\ (p = e -> st = 2 \/ Z.land dn 1 <> 0)) (* [comment removed for export] *) ->
      forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 1%bv = Z_to_bv 64 RT.LOOPB -> getr R' 10%bv = getr R 18%bv -> TK.keepsR KS45 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SKIP_WS M model) K) ->
  (code = 0 -> mo <> 0 -> (p = e -> st <> 1 /\ (st = 2 \/ Z.land dn 1 <> 0)) (* [comment removed for export] *) -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 20%bv = Z_to_bv 64 1 -> getr R' 21%bv = Z_to_bv 64 2 -> TK.keepsR KS45 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.LOOPA M model) K) ->
  (code <> 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> TK.keepsR KS45 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.RN_EPI M model) K) ->
  (code = 0 -> p = e -> st <> 1 -> st <> 2 -> Z.land dn 1 = 0 (* [comment removed for export] *) -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 1%bv = Z_to_bv 64 RT.RN_EPI ->
      getr R' 10%bv = Z_to_bv 64 Ev -> getr R' 11%bv = Z_to_bv 64 1 -> TK.keepsR KS45 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SET_EC M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.RN_R_PSOME M model) K.
Proof.
  intros fx R M model K sp1 Rr Ev code st dn mo p e Hh Hl Hfp H2 [Hsp Hal] H9 H8 [Hr1 Hr2] [He1 He2] H20 H21 H19 H22 Rp Re Cc Rc Cst Cdn Cmo Rst Rdn Rmo Kws Kloop Kepi Ksetec.
  change RT.RN_R_PSOME with (CC.cp_pc GA.cp3).
  hv_open GA.cp3 (GA.plans 3%nat _ eq_refl) (-80) [code; st; dn; mo] [(20%nat, 1); (21%nat, 2)] sp1 R M fx model K Hh Hl Hfp H2 ltac:(pins45 H20 H21).
  - reg_atom E sp1 R 41%nat r_s1 H9. reg_atom E sp1 R 40%nat r_s0 H8. gh_atom E sp1 R 64%nat 0%nat code. gh_atom E sp1 R 65%nat 1%nat st. gh_atom E sp1 R 66%nat 2%nat dn. gh_atom E sp1 R 67%nat 3%nat mo.
    unfold know_ok, GA.cp3. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_range. + kw32 Ev code Cc. + kw8 (Rr + 528) st Cst. + kw8 (Rr + 532) dn Cdn. + kw8 (Rr + 531) mo Cmo.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 R 41%nat r_s1 H9. reg_atom E sp1 R 40%nat r_s0 H8. reg_atom E sp1 R 51%nat r_s3 H19. reg_atom E sp1 R 54%nat r_s6 H22.
    gh_atom E sp1 R 64%nat 0%nat code. gh_atom E sp1 R 65%nat 1%nat st. gh_atom E sp1 R 66%nat 2%nat dn. gh_atom E sp1 R 67%nat 3%nat mo.
    leaf_open Hag HLF E' 68%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    assert (WS : code = 0 -> (p = e /\ st = 1) \/ (mo = 0 /\ (p = e -> st = 2 \/ Z.land dn 1 <> 0)) -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 1%bv = Z_to_bv 64 RT.LOOPB -> getr R' 10%bv = getr R 18%bv -> TK.keepsR KS45 R R' ->
                 srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SKIP_WS M model) K) by (intros X Y; exact (Kws X Y fx' R' Hfp')).
    assert (LP : code = 0 -> mo <> 0 -> (p = e -> st <> 1 /\ (st = 2 \/ Z.land dn 1 <> 0)) -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 20%bv = Z_to_bv 64 1 -> getr R' 21%bv = Z_to_bv 64 2 -> TK.keepsR KS45 R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' RT.LOOPA M model) K) by (intros X Y W; exact (Kloop X Y W fx' R' Hfp')).
    assert (EP : code <> 0 -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> TK.keepsR KS45 R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' RT.RN_EPI M model) K) by (intros X; exact (Kepi X fx' R' Hfp')).
    clear Kws Kloop Kepi.
    leaves 10%nat k Hnth ltac:(probes_in HLF PF; pf_all PF).
    + apply WS; [lia | lia | llin HLF r_sp | unfold RT.LOOPB; llin HLF r_ra | lkeep HLF Hag64 sp1 R r_a0 50%nat r_s2 | hv_keeps HLF Hag64 sp1 R E' R' M M' KS45].
    + apply WS; [lia | lia | llin HLF r_sp | unfold RT.LOOPB; llin HLF r_ra | lkeep HLF Hag64 sp1 R r_a0 50%nat r_s2 | hv_keeps HLF Hag64 sp1 R E' R' M M' KS45].
    + apply LP; [lia | lia | lia | llin HLF r_sp | llin HLF r_s4 | llin HLF r_s5 | hv_keeps HLF Hag64 sp1 R E' R' M M' KS45].
    + apply (Ksetec ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | unfold RT.RN_EPI; llin HLF r_ra | llin HLF r_a0 | llin HLF r_a1 | hv_keeps HLF Hag64 sp1 R E' R' M M' KS45].
    + apply WS; [lia | lia | llin HLF r_sp | unfold RT.LOOPB; llin HLF r_ra | lkeep HLF Hag64 sp1 R r_a0 50%nat r_s2 | hv_keeps HLF Hag64 sp1 R E' R' M M' KS45].
    + apply LP; [lia | lia | lia | llin HLF r_sp | llin HLF r_s4 | llin HLF r_s5 | hv_keeps HLF Hag64 sp1 R E' R' M M' KS45].
    + apply EP; [lia | llin HLF r_sp | hv_keeps HLF Hag64 sp1 R E' R' M M' KS45].
    + apply WS; [lia | lia | llin HLF r_sp | unfold RT.LOOPB; llin HLF r_ra | lkeep HLF Hag64 sp1 R r_a0 50%nat r_s2 | hv_keeps HLF Hag64 sp1 R E' R' M M' KS45].
    + apply LP; [lia | lia | lia | llin HLF r_sp | llin HLF r_s4 | llin HLF r_s5 | hv_keeps HLF Hag64 sp1 R E' R' M M' KS45].
    + apply EP; [lia | llin HLF r_sp | hv_keeps HLF Hag64 sp1 R E' R' M M' KS45].
Qed.

End S.
End RSW.
