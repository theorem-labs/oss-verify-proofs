(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u ReadKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_rnext_a_csrc_u Cut_rnext_b_csrc_u Cut_rnext_c_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module RNT.
Definition RN : Z := 0x3b180.        Definition LOOP : Z := 0x3b1c8.     Definition R_CHUNK : Z := 0x3b1e0.  Definition R_PSOME : Z := 0x3b234.
Definition DONE : Z := 0x3b278.      Definition EPI : Z := 0x3b280.      Definition TAILEPI : Z := 0x3b2ac.  Definition RET : Z := 0x3b2a8.
End RNT.

Module RNS.
Module GA := Cut_rnext_a_csrc_u.  Module GB := Cut_rnext_b_csrc_u.  Module GC := Cut_rnext_c_csrc_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition spok (sp0 : Z) : Prop := 2 ^ 40 <= sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0.
Definition pok (p : Z) : Prop := 2 ^ 12 <= p <= 2 ^ 47.

Definition KSE : list nat := [3; 4; 23; 24; 25; 26; 27]%nat.
Definition KSL : list nat := [3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%nat.
Definition KSP : list nat := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition KSX : list nat := [3; 4; 24; 25; 26; 27]%nat.
Definition KSQ : list nat := [3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%nat.

Definition r_ra : reg := 1%bv.   Definition r_sp : reg := 2%bv.   Definition r_s0 : reg := 8%bv.   Definition r_s1 : reg := 9%bv.
Definition r_a0 : reg := 10%bv.  Definition r_a1 : reg := 11%bv.  Definition r_a2 : reg := 12%bv.  Definition r_s2 : reg := 18%bv.
Definition r_s3 : reg := 19%bv.  Definition r_s4 : reg := 20%bv.  Definition r_s5 : reg := 21%bv.  Definition r_s6 : reg := 22%bv.  Definition r_s7 : reg := 23%bv.
Ltac rr x := eval cbv delta [r_ra r_sp r_s0 r_s1 r_a0 r_a1 r_a2 r_s2 r_s3 r_s4 r_s5 r_s6 r_s7] in x.

Definition rn_frame (M : mem) (sp1 rav : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp1 - 8) rav /\ L5.u64_at RSEGS M (sp1 - 16) (bv_unsigned (getr R0 8%bv)) /\ L5.u64_at RSEGS M (sp1 - 24) (bv_unsigned (getr R0 9%bv)) /\
  L5.u64_at RSEGS M (sp1 - 32) (bv_unsigned (getr R0 18%bv)) /\ L5.u64_at RSEGS M (sp1 - 40) (bv_unsigned (getr R0 19%bv)) /\ L5.u64_at RSEGS M (sp1 - 48) (bv_unsigned (getr R0 20%bv)) /\
  L5.u64_at RSEGS M (sp1 - 56) (bv_unsigned (getr R0 21%bv)) /\ L5.u64_at RSEGS M (sp1 - 64) (bv_unsigned (getr R0 22%bv)) /\ L5.u64_at RSEGS M (sp1 - 72) (bv_unsigned (getr R0 23%bv)).
Definition same_s07 (R0 R' : bvmap 5 word) : Prop :=
  getr R' 8%bv = getr R0 8%bv /\ getr R' 9%bv = getr R0 9%bv /\ getr R' 18%bv = getr R0 18%bv /\ getr R' 19%bv = getr R0 19%bv /\ getr R' 20%bv = getr R0 20%bv /\
  getr R' 21%bv = getr R0 21%bv /\ getr R' 22%bv = getr R0 22%bv /\ getr R' 23%bv = getr R0 23%bv.

Definition eof_flag (R' : bvmap 5 word) (pn en rem rdb : Z) : Prop :=
  (getr R' 23%bv = Z_to_bv 64 0 /\ pn = en /\ rem = 0 /\ Z.land rdb 2 <> 0) \/ (getr R' 23%bv = Z_to_bv 64 1 /\ ~ (pn = en /\ rem = 0 /\ Z.land rdb 2 <> 0)).

Lemma sltu_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof.
  intros a b Ha Hb. change (alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b)) with (if bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) then Z_to_bv 64 1 else Z_to_bv 64 0 : word).
  unfold bv_ltu. rewrite !u64_of_Z by lia. destruct (Z.ltb_spec a b); reflexivity.
Qed.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Ltac hv_open cp plans off gl pn sp0 R M fx model K Hh Hl Hfp H2 Hpins :=
  let E := fresh "E" in set (E := TK.hvE sp0 R (RK.ghl gl));
  assert (U2 : bv_unsigned (ev E 2) = sp0) by (apply TK.hvE_sp; lia);
  apply (TK.stretch_cps FPM cp fx E R M model K plans Hh Hl Hfp);
  [ apply (RK.regs_ok_hv _ off pn); [vm_compute; reflexivity | lia | lia | first [exact H2 | rewrite Z.add_0_r; exact H2] | Hpins] | | ].
Ltac no_pins := let q := fresh in let z := fresh in intros q z [].

Ltac reg_atom E sp0 R v r Hr := let U := fresh "Ur" in
  lazymatch type of Hr with getr _ _ = Z_to_bv 64 ?z =>
    assert (U : bv_unsigned (ev E v) = z) by (change v with (32 + ridx (r : reg))%nat; subst E; apply (RK.hv_reg_u sp0 R _ r z Hr); lia) end.
Ltac gh_atom E sp0 R v k z := let U := fresh "Ug" in
  assert (U : bv_unsigned (ev E v) = z) by (change v with (64 + k)%nat; subst E; eapply RK.ghl_u; [reflexivity | lia]).

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
Ltac pf_z H := w2z H; rewrite ?RK.ext_s32, ?RK.ext_u8 in H by lia; rewrite ?RK.and_lit in H by lia;
  first [apply RK.w_inj in H; [| first [lia | apply RK.land_range; lia] | first [lia | apply RK.land_range; lia]] | apply RK.w_neq in H].
Ltac pf_all PF := repeat (let X := fresh "PFx" in destruct PF as [X PF]; pf_z X); clear PF.

Ltac lsame HLF M M' A0 e p D Ce Cp b ve vp :=
  assert (SAME : M' = M);
  [ eapply (RK.same_mem16 M M' A0 e p); [lia | lia | lframe HLF | exact (CC.lf_grows _ _ _ _ _ _ _ HLF) | exact D | exact Ce | | replace (A0 + 8) with (A0 - 512 + 520) by lia; ring_simplify (A0 - 512 + 520); exact Cp | ];
    [ lcell64 HLF b 512 ve; cbn [edenot]; assumption | replace (A0 + 8) with (A0 - 512 + 520) by lia; ring_simplify (A0 - 512 + 520); lcell64 HLF b 520 vp; cbn [edenot]; assumption ] | ].

Ltac pf_pre PF := w2z PF; rewrite ?RK.ext_s32, ?RK.ext_u8 in PF by lia; rewrite ?RK.and_lit in PF by lia.
Ltac pf_sltu PF c := rewrite ?sltu_lit in PF by lia; revert PF; destruct (Z.ltb_spec 0 c); intros PF; cbv beta iota in PF.
Ltac pins56 H21 H22 := let q := fresh in let z := fresh in let X := fresh in intros q z [X|[X|[]]]; injection X as <- <-; [exact H21 | exact H22].

Lemma ret_rn : CL.is_ret_at RSEGS RNT.RET. Proof. CL.solve_is_ret. Qed.

Lemma s_rn_entry : forall (fx : FPState) R M model K sp1 C rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 sp1 -> spok sp1 ->
  getr R 10%bv = Z_to_bv 64 C -> getr R 1%bv = Z_to_bv 64 rav -> 0 <= rav < 2 ^ 64 -> pok C ->
  L5.defined M (sp1 - 80) 80 -> L5.defined M (C + 531) 1 -> sp1 <= C ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) ->
      getr R' 8%bv = getr R 12%bv -> getr R' 9%bv = Z_to_bv 64 C -> getr R' 18%bv = getr R 11%bv -> getr R' 19%bv = Z_to_bv 64 (C + 320) -> getr R' 20%bv = Z_to_bv 64 (C + 8) ->
      getr R' 21%bv = Z_to_bv 64 1 -> getr R' 22%bv = Z_to_bv 64 2 -> TK.keepsR KSE R R' ->
      rn_frame M' sp1 rav R -> L5.u8_at RSEGS M' (C + 531) 1 ->
      TK.samem (fun a => ~ (sp1 - 80 <= a < sp1) /\ ~ (C + 531 <= a < C + 532)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RNT.LOOP M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RNT.RN M model) K.
Proof.
  intros fx R M model K sp1 C rav Hh Hl Hfp H2 [Hsp Hal] H10 H1 Rra [Hc1 Hc2] D1 D2 A1 Hcont.
  change RNT.RN with (CC.cp_pc GA.cp0).
  hv_open GA.cp0 (GA.plans 0%nat _ eq_refl) 0 (@nil Z) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - reg_atom E sp1 R 42%nat r_a0 H10.
    unfold know_ok, GA.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 R 42%nat r_a0 H10. reg_atom E sp1 R 33%nat r_ra H1.
    leaf_open Hag HLF E' 64%nat.
    leaves 1%nat k Hnth ltac:(idtac).
    apply (Hcont fx' R' M' Hfp').
    + llin HLF r_sp. + lkeep HLF Hag64 sp1 R r_s0 44%nat r_a2. + llin HLF r_s1. + lkeep HLF Hag64 sp1 R r_s2 43%nat r_a1.
    + llin HLF r_s3. + llin HLF r_s4. + llin HLF r_s5. + llin HLF r_s6.
    + hv_keeps HLF Hag64 sp1 R E' R' M M' KSE.
    + unfold rn_frame. repeat split.
      * lcell64 HLF (EVar 2) (-8) (EVar 33). cbn [edenot]. assumption.
      * lcell64 HLF (EVar 2) (-16) (EVar 40). vreg Hag64 sp1 R 40%nat r_s0.
      * lcell64 HLF (EVar 2) (-24) (EVar 41). vreg Hag64 sp1 R 41%nat r_s1.
      * lcell64 HLF (EVar 2) (-32) (EVar 50). vreg Hag64 sp1 R 50%nat r_s2.
      * lcell64 HLF (EVar 2) (-40) (EVar 51). vreg Hag64 sp1 R 51%nat r_s3.
      * lcell64 HLF (EVar 2) (-48) (EVar 52). vreg Hag64 sp1 R 52%nat r_s4.
      * lcell64 HLF (EVar 2) (-56) (EVar 53). vreg Hag64 sp1 R 53%nat r_s5.
      * lcell64 HLF (EVar 2) (-64) (EVar 54). vreg Hag64 sp1 R 54%nat r_s6.
      * lcell64 HLF (EVar 2) (-72) (EVar 55). vreg Hag64 sp1 R 55%nat r_s7.
    + lcell8 HLF (EVar 42) 531 (ELit 1). vlit.
    + lframe HLF.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Lemma s_loop : forall (fx : FPState) R M model K sp1 C p e,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 C -> pok C -> L5.u64_at RSEGS M (C + 512) e -> L5.u64_at RSEGS M (C + 520) p ->
  0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 ->
  (p = e -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 1%bv = Z_to_bv 64 RNT.R_CHUNK ->
      getr R' 10%bv = getr R 20%bv -> getr R' 11%bv = getr R 8%bv -> TK.keepsR KSL R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_READ_CHUNK M model) K) ->
  (p <> e -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 1%bv = Z_to_bv 64 RNT.R_PSOME ->
      getr R' 10%bv = getr R 19%bv -> getr R' 11%bv = getr R 18%bv -> getr R' 12%bv = getr R 8%bv -> getr R' 23%bv = Z_to_bv 64 1 -> TK.keepsR KSL R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_PARSE_SOME M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RNT.LOOP M model) K.
Proof.
  intros fx R M model K sp1 C p e Hh Hl Hfp H2 [Hsp Hal] H9 [Hc1 Hc2] Ce Cp Rp Re Kchunk Kpsome.
  change RNT.LOOP with (CC.cp_pc GB.cp0).
  hv_open GB.cp0 (GB.plans 0%nat _ eq_refl) (-80) [e; p] (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - reg_atom E sp1 R 41%nat r_s1 H9. gh_atom E sp1 R 64%nat 0%nat e. gh_atom E sp1 R 65%nat 1%nat p.
    unfold know_ok, GB.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range.
    + kw64 (C + 512) e Ce. + kw64 (C + 520) p Cp.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 R 41%nat r_s1 H9. gh_atom E sp1 R 64%nat 0%nat e. gh_atom E sp1 R 65%nat 1%nat p.
    leaf_open Hag HLF E' 66%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    (leaf_k k Hnth; [|leaf_k k Hnth; [|leaf_end k Hnth]]); probes_in HLF PF.
    + destruct PF as (PF & _). w2z PF. apply RK.w_inj in PF; [|lia|lia].
      apply (Kchunk ltac:(lia) fx' R' Hfp').
      * llin HLF r_sp. * unfold RNT.R_CHUNK. llin HLF r_ra. * lkeep HLF Hag64 sp1 R r_a0 52%nat r_s4. * lkeep HLF Hag64 sp1 R r_a1 40%nat r_s0.
      * hv_keeps HLF Hag64 sp1 R E' R' M M' KSL.
    + destruct PF as (PF & _). w2z PF. assert (NE : p <> e) by (intros X; apply PF; rewrite X; reflexivity).
      apply (Kpsome NE fx' R' Hfp').
      * llin HLF r_sp. * unfold RNT.R_PSOME. llin HLF r_ra. * lkeep HLF Hag64 sp1 R r_a0 51%nat r_s3. * lkeep HLF Hag64 sp1 R r_a1 50%nat r_s2.
      * lkeep HLF Hag64 sp1 R r_a2 40%nat r_s0. * llin HLF r_s7.
      * hv_keeps HLF Hag64 sp1 R E' R' M M' KSL.
Qed.

Lemma s_epi : forall (fx : FPState) R M model K sp1 rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> spok sp1 -> rn_frame M sp1 rav R0 -> L5.ra_ok rav ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s07 R0 R' -> TK.keepsR KSX R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RNT.EPI M model) K.
Proof.
  intros fx R M model K sp1 rav R0 Hh Hl Hfp H2 [Hsp Hal] (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9) [Hrar Hrae] Hcont.
  change RNT.EPI with (CC.cp_pc GB.cp1).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  set (GL := [rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv);
              bv_unsigned (getr R0 21%bv); bv_unsigned (getr R0 22%bv); bv_unsigned (getr R0 23%bv)]).
  hv_open GB.cp1 (GB.plans 1%nat _ eq_refl) (-80) GL (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - unfold know_ok, GB.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + kw64 (sp1 - 8) rav F1. + kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3.
    + kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4. + kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6.
    + kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7. + kw64 (sp1 - 64) (bv_unsigned (getr R0 22%bv)) F8. + kw64 (sp1 - 72) (bv_unsigned (getr R0 23%bv)) F9.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    leaf_open Hag HLF E' 73%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    leaves 1%nat k Hnth ltac:(idtac).
    assert (GH : forall j z, nth_error GL j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj9 : (j < 9)%nat) by (do 9 (destruct j as [|j]; [lia|]); destruct j; discriminate Hj). change (CC.cp_nx GB.cp1) with 73%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. unfold E. rewrite TK.hvE_ghost. unfold RK.ghl. rewrite (nth_error_nth _ _ _ Hj). reflexivity. }
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (lreg HLF r_ra; exact (GH 0%nat _ eq_refl)).
    unfold PML.cfg. apply (CL.ret_cps RSEGS fx' R' _ M model K ret_rn Hh Hl).
    + rewrite R1. apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact Hrae.
    + rewrite R1. apply (Hcont fx' R' Hfp').
      * llin HLF r_sp.
      * unfold same_s07. repeat split.
        -- lreg HLF r_s0. etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- lreg HLF r_s1. etransitivity; [exact (GH 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- lreg HLF r_s2. etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- lreg HLF r_s3. etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- lreg HLF r_s4. etransitivity; [exact (GH 5%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- lreg HLF r_s5. etransitivity; [exact (GH 6%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- lreg HLF r_s6. etransitivity; [exact (GH 7%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- lreg HLF r_s7. etransitivity; [exact (GH 8%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * hv_keeps HLF Hag64 sp1 R E' R' M M' KSX.
Qed.

Lemma s_tailepi : forall (fx : FPState) R M model K sp1 rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> spok sp1 -> rn_frame M sp1 rav R0 -> 0 <= rav < 2 ^ 64 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 1%bv = Z_to_bv 64 rav -> getr R' 10%bv = getr R 8%bv -> getr R' 11%bv = Z_to_bv 64 1 ->
      same_s07 R0 R' -> TK.keepsR KSX R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SET_EC M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RNT.TAILEPI M model) K.
Proof.
  intros fx R M model K sp1 rav R0 Hh Hl Hfp H2 [Hsp Hal] (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9) Rrav Hcont.
  change RNT.TAILEPI with (CC.cp_pc GB.cp2).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  set (GL := [rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv);
              bv_unsigned (getr R0 21%bv); bv_unsigned (getr R0 22%bv); bv_unsigned (getr R0 23%bv)]).
  hv_open GB.cp2 (GB.plans 2%nat _ eq_refl) (-80) GL (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - unfold know_ok, GB.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + kw64 (sp1 - 8) rav F1. + kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3.
    + kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4. + kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6.
    + kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7. + kw64 (sp1 - 64) (bv_unsigned (getr R0 22%bv)) F8. + kw64 (sp1 - 72) (bv_unsigned (getr R0 23%bv)) F9.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    leaf_open Hag HLF E' 73%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    leaves 1%nat k Hnth ltac:(idtac).
    assert (GH : forall j z, nth_error GL j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj9 : (j < 9)%nat) by (do 9 (destruct j as [|j]; [lia|]); destruct j; discriminate Hj). change (CC.cp_nx GB.cp2) with 73%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. unfold E. rewrite TK.hvE_ghost. unfold RK.ghl. rewrite (nth_error_nth _ _ _ Hj). reflexivity. }
    apply (Hcont fx' R' Hfp').
    + llin HLF r_sp.
    + lreg HLF r_ra. exact (GH 0%nat _ eq_refl).
    + lkeep HLF Hag64 sp1 R r_a0 40%nat r_s0.
    + llin HLF r_a1.
    + unfold same_s07. repeat split.
      * lreg HLF r_s0. etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * lreg HLF r_s1. etransitivity; [exact (GH 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * lreg HLF r_s2. etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * lreg HLF r_s3. etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * lreg HLF r_s4. etransitivity; [exact (GH 5%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * lreg HLF r_s5. etransitivity; [exact (GH 6%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * lreg HLF r_s6. etransitivity; [exact (GH 7%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * lreg HLF r_s7. etransitivity; [exact (GH 8%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + hv_keeps HLF Hag64 sp1 R E' R' M M' KSX.
Qed.

Lemma s_done : forall (fx : FPState) R M model K sp1 C,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 C -> pok C -> L5.defined M (C + 640) 1 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> TK.keepsR KSP R R' ->
      L5.u8_at RSEGS M' (C + 640) 1 -> TK.samem (fun a => ~ (C + 640 <= a < C + 641)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RNT.EPI M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RNT.DONE M model) K.
Proof.
  intros fx R M model K sp1 C Hh Hl Hfp H2 [Hsp Hal] H9 [Hc1 Hc2] D1 Hcont.
  change RNT.DONE with (CC.cp_pc GC.cp0).
  hv_open GC.cp0 (GC.plans 0%nat _ eq_refl) (-80) (@nil Z) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - reg_atom E sp1 R 41%nat r_s1 H9.
    unfold know_ok, GC.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. reg_atom E sp1 R 41%nat r_s1 H9.
    leaf_open Hag HLF E' 64%nat. leaves 1%nat k Hnth ltac:(idtac).
    apply (Hcont fx' R' M' Hfp').
    + llin HLF r_sp.
    + hv_keeps HLF Hag64 sp1 R E' R' M M' KSP.
    + lcell8 HLF (EVar 41) 640 (ELit 1). vlit.
    + lframe HLF.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Definition rc_slot (off : Z) (pins : list (nat * Z)) (ads : list (nat * (nat * Z))) (q : nat) : expr :=
  match List.find (fun a => Nat.eqb (fst a) q) ads with
  | Some a => EAlu ALU_ADD (EVar (32 + fst (snd a))) (ELit (snd (snd a)))
  | None => RK.hv_slot off pins q
  end.
Definition rc_shape (sr : list expr) (off : Z) (pins : list (nat * Z)) (ads : list (nat * (nat * Z))) : bool :=
  forallb (fun q => expr_eqb (nth q sr (ELit 0)) (rc_slot off pins ads q)) (seq 1 31) && forallb (fun a => Nat.ltb (fst (snd a)) 32) ads.
Lemma rc_regs_ok : forall sr off pins ads sp0 R gh,
  rc_shape sr off pins ads = true -> 0 <= sp0 < 2 ^ 64 -> 0 <= sp0 + off < 2 ^ 64 ->
  getr R 2%bv = Z_to_bv 64 (sp0 + off) ->
  (forall q z, In (q, z) pins -> getr R (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z) ->
  Forall (fun a => getr R (Z_to_bv 5 (Z.of_nat (fst a))) = alu64 ALU_ADD (getr R (Z_to_bv 5 (Z.of_nat (fst (snd a))))) (Z_to_bv 64 (snd (snd a)))) ads ->
  regs_ok (TK.hvE sp0 R gh) sr R.
Proof.
  intros sr off pins ads sp0 R gh Hsh Hsp Hspo H2 Hpins Hads. unfold rc_shape in Hsh. apply andb_true_iff in Hsh as [Hsh Hlt].
  rewrite forallb_forall in Hsh, Hlt. rewrite Forall_forall in Hads.
  apply APSX.regs_ok_pointwise. intros r Hr0.
  assert (Hq : In (ridx r) (seq 1 31)).
  { apply in_seq. pose proof (ridx_range r). assert (ridx r <> 0%nat).
    { intros X. apply Hr0. rewrite <- (ridx_roundtrip r), X. apply bv_eq. reflexivity. } lia. }
  specialize (Hsh _ Hq). apply expr_eqb_eq in Hsh. rewrite Hsh. unfold rc_slot.
  destruct (find (fun a => Nat.eqb (fst a) (ridx r)) ads) as [[q [b c]]|] eqn:Hf.
  - apply find_some in Hf as [Hin Hq2]. cbn [fst] in Hq2. apply Nat.eqb_eq in Hq2. subst q.
    pose proof (Hlt _ Hin) as Hb. pose proof (Hads _ Hin) as Ha. cbn [fst snd] in Hb, Ha |- *. apply Nat.ltb_lt in Hb.
    cbn [edenot]. rewrite <- (ridx_roundtrip r). rewrite Ha. f_equal.
    cbn [ev TK.hvE]. unfold TK.hvV.
    replace (Nat.ltb (32 + b) 32) with false by (symmetry; apply Nat.ltb_ge; lia).
    replace (Nat.ltb (32 + b) 64) with true by (symmetry; apply Nat.ltb_lt; lia).
    replace (32 + b - 32)%nat with b by lia. reflexivity.
  - unfold RK.hv_slot. destruct (Nat.eqb (ridx r) 2) eqn:E2.
    + apply Nat.eqb_eq in E2. assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r), E2; apply bv_eq; reflexivity). subst r.
      destruct (Z.eqb_spec off 0) as [->|Hne].
      * cbn [edenot ev TK.hvE]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite H2. f_equal. lia.
      * cbn [edenot ev TK.hvE]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite TK.add_lit by lia. exact H2.
    + destruct (find (fun p => Nat.eqb (fst p) (ridx r)) pins) as [[q z]|] eqn:Hf2.
      * apply find_some in Hf2 as [Hin Hq2]. cbn [fst] in Hq2. apply Nat.eqb_eq in Hq2. subst q. cbn [snd edenot].
        rewrite <- (Hpins _ _ Hin), ridx_roundtrip. reflexivity.
      * cbn [edenot]. symmetry. apply TK.hvE_reg.
Qed.
Ltac rc_open cp plans off gl pn ad sp0 R M fx model K Hh Hl Hfp H2 Hpins Hads :=
  let E := fresh "E" in set (E := TK.hvE sp0 R (RK.ghl gl));
  assert (U2 : bv_unsigned (ev E 2) = sp0) by (apply TK.hvE_sp; lia);
  apply (TK.stretch_cps FPM cp fx E R M model K plans Hh Hl Hfp);
  [ apply (rc_regs_ok _ off pn ad); [vm_compute; reflexivity | lia | lia | first [exact H2 | rewrite Z.add_0_r; exact H2] | Hpins | Hads] | | ].
Lemma rc_add8 : forall R (C : Z), getr R 9%bv = Z_to_bv 64 C -> getr R 20%bv = Z_to_bv 64 (C + 8) -> 0 <= C -> C + 8 < 2 ^ 64 ->
  getr R 20%bv = alu64 ALU_ADD (getr R 9%bv) (Z_to_bv 64 8).
Proof. intros R C H9 H20 H0 H1. rewrite H20, H9. symmetry. apply TK.add_lit; lia. Qed.
Ltac rc_ad20 R C H9 H20 := apply Forall_cons; [exact (rc_add8 R C H9 H20 ltac:(lia) ltac:(lia)) | apply Forall_nil].
Lemma rc_keeps : forall c ps sp0 R gh E' R' M M' qs,
  CC.leaf_facts RSEGS c ps E' R' M M' -> TK.keeps_hv ps (List.filter (fun q => negb (Nat.eqb q 20)) qs) = true ->
  env_agree 64 (TK.hvE sp0 R gh) E' -> getr R' 20%bv = getr R 20%bv -> TK.keepsR qs R R'.
Proof.
  intros c ps sp0 R gh E' R' M M' qs HLF H Hag H20 r Hr.
  destruct (Nat.eqb_spec (ridx r) 20) as [X|X].
  - assert (r = 20%bv) by (rewrite <- (ridx_roundtrip r), X; apply bv_eq; reflexivity). subst r. exact H20.
  - apply (TK.keeps_hv_sound c ps sp0 R gh E' R' M M' _ r HLF H Hag). apply List.filter_In. split; [exact Hr|]. cbv beta.
    apply negb_true_iff, Nat.eqb_neq. exact X.
Qed.
Ltac rc_kp HLF Hag64 sp0 R E' R' M M' qs H20 :=
  apply (rc_keeps _ _ sp0 R _ E' R' M M' qs HLF eq_refl Hag64);
  lreg HLF r_s4; repeat match goal with U : bv_unsigned (ev E' ?v) = ?z |- context [ev E' ?v] => rewrite (RK.w_of_u _ _ U) end;
  rewrite H20; apply TK.add_lit; lia.
Lemma rc_eof_w : forall E Kc v r, Kc = 2 ^ 62 -> bv_unsigned (ev E v) = r -> 0 <= r <= 255 ->
  edenot E (EAlu ALU_XOR (EAlu ALU_SRL (EMd M_MUL (ELit Kc) (EVar v)) (ELit 63)) (ELit 1)) = Z_to_bv 64 (if Z.land r 2 =? 0 then 1 else 0).
Proof.
  intros E Kc v r -> Hv Hr.
  transitivity (edenot E (EAlu ALU_XOR (EAlu ALU_SRL (EMd M_MUL (ELit (2 ^ 62)) (ELit r)) (ELit 63)) (ELit 1))).
  { cbn [edenot]. rewrite (RK.w_of_u _ _ Hv). reflexivity. }
  assert (B : forallb (fun n => Z.eqb (bv_unsigned (edenot E (EAlu ALU_XOR (EAlu ALU_SRL (EMd M_MUL (ELit (2 ^ 62)) (ELit (Z.of_nat n))) (ELit 63)) (ELit 1))))
                                     (if Z.land (Z.of_nat n) 2 =? 0 then 1 else 0)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B (Z.to_nat r) ltac:(apply in_seq; lia)). cbv beta in B. rewrite Z2Nat.id in B by lia.
  apply Z.eqb_eq in B. apply bv_eq. rewrite B. rewrite u64_of_Z; [reflexivity | destruct (Z.land r 2 =? 0); lia].
Qed.
Lemma s_r_chunk : forall (fx : FPState) R M model K sp1 C Ev code p e rem IS rdb p' k,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 C -> getr R 8%bv = Z_to_bv 64 Ev -> getr R 20%bv = Z_to_bv 64 (C + 8) -> pok C -> pok Ev -> getr R 10%bv = Z_to_bv 64 p' -> getr R 11%bv = Z_to_bv 64 k ->
  0 <= p' -> 0 <= k -> p' + k < 2 ^ 64 -> k <= 16384 -> (k <> 0 -> pok p') ->
  L5.u32_at RSEGS M Ev code -> 0 <= code < 2 ^ 31 -> L5.u64_at RSEGS M (C + 512) e -> L5.u64_at RSEGS M (C + 520) p -> L5.u64_at RSEGS M (C + 296) rem ->
  L5.u64_at RSEGS M (C + 248) IS -> pok IS -> IS mod 8 = 0 -> L5.u64_at RSEGS M IS PML.VT_ISS -> L5.u8_at RSEGS M (IS + 152) rdb -> 0 <= rdb <= 255 -> PML.img_ro M ->
  0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 -> 0 <= rem < 2 ^ 64 -> L5.defined M (C + 512) 16 -> (C + 656 <= Ev \/ Ev + 16 <= C) -> (C + 656 <= IS \/ IS + 272 <= C) ->
  (code <> 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> TK.keepsR KSL R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RNT.EPI M model) K) ->
  (code = 0 -> forall (fx' : FPState) R' M' pn en, PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 1%bv = Z_to_bv 64 RNT.R_PSOME ->
      getr R' 10%bv = getr R 19%bv -> getr R' 11%bv = getr R 18%bv -> getr R' 12%bv = Z_to_bv 64 Ev ->
      eof_flag R' pn en rem rdb -> TK.keepsR KSL R R' ->
      ((k = 0 /\ pn = p /\ en = e /\ M' = M) \/
       (k <> 0 /\ pn = p' /\ en = p' + k /\ L5.u64_at RSEGS M' (C + 512) en /\ L5.u64_at RSEGS M' (C + 520) pn /\ TK.samem (fun a => ~ (C + 512 <= a < C + 528)) M M' /\ mem_grows M M')) ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_PARSE_SOME M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RNT.R_CHUNK M model) K.
Proof.
  intros fx R M model K sp1 C Ev code p e rem IS rdb p' k Hh Hl Hfp H2 [Hsp Hal] H9 H8 H20 [Hc1 Hc2] [He1 He2] H10 H11 Rp' Rk Rpk Rkd Pp'
         Cc Rc Ce Cp Crem Cis [Hi1 Hi2] Hia Cvt Crd Rrd RO Rp Re Rrem D1 AP1 AP2 Kepi Kps.
  destruct (Z.eq_dec k 0) as [Hk0|Hk0].
  - change RNT.R_CHUNK with (CC.cp_pc GA.cp1).
    rc_open GA.cp1 (GA.plans 1%nat _ eq_refl) (-80) [code; e; p; rem; IS; rdb] (@nil (nat * Z)) [(20%nat, (9%nat, 8))] sp1 R M fx model K Hh Hl Hfp H2
      no_pins ltac:(rc_ad20 R C H9 H20).
    + reg_atom E sp1 R 41%nat r_s1 H9. reg_atom E sp1 R 40%nat r_s0 H8. reg_atom E sp1 R 43%nat r_a1 H11.
      gh_atom E sp1 R 64%nat 0%nat code. gh_atom E sp1 R 65%nat 1%nat e. gh_atom E sp1 R 66%nat 2%nat p. gh_atom E sp1 R 67%nat 3%nat rem. gh_atom E sp1 R 68%nat 4%nat IS. gh_atom E sp1 R 69%nat 5%nat rdb.
      unfold know_ok, GA.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
      * e_range. * e_align Hal. * e_range. * e_range. * kw32 Ev code Cc.
      * kw64 (C + 512) e Ce. * kw64 (C + 520) p Cp. * kw64 (C + 296) rem Crem. * kw64 (C + 248) IS Cis. * e_wr.
      * e_range. * kw64 IS PML.VT_ISS Cvt. * kw8 (IS + 152) rdb Crd. * e_range. * tk_kimg RO. * e_disj. * e_disj.
      * e_range. * e_align Hia.
    + intros fx' E' R' M' k0 ps Hnth Hag HLF Hfp'.
      reg_atom E sp1 R 41%nat r_s1 H9. reg_atom E sp1 R 40%nat r_s0 H8. reg_atom E sp1 R 42%nat r_a0 H10. reg_atom E sp1 R 43%nat r_a1 H11.
      gh_atom E sp1 R 64%nat 0%nat code. gh_atom E sp1 R 65%nat 1%nat e. gh_atom E sp1 R 66%nat 2%nat p. gh_atom E sp1 R 67%nat 3%nat rem. gh_atom E sp1 R 68%nat 4%nat IS. gh_atom E sp1 R 69%nat 5%nat rdb.
      leaf_open Hag HLF E' 70%nat.
      leaves 4%nat k0 Hnth ltac:(probes_in HLF PF; pf_all PF).
      * lsame HLF M M' (C + 512) e p D1 Ce Cp (EVar 41) (EVar 65) (EVar 66).
        apply (Kps ltac:(lia) fx' R' M' p e Hfp').
        -- llin HLF r_sp. -- unfold RNT.R_PSOME. llin HLF r_ra. -- lkeep HLF Hag64 sp1 R r_a0 51%nat r_s3. -- lkeep HLF Hag64 sp1 R r_a1 50%nat r_s2. -- llin HLF r_a2.
        -- assert (S7 : getr R' 23%bv = Z_to_bv 64 (if Z.land rdb 2 =? 0 then 1 else 0)).
           { rewrite (TK.ps_reg_r _ _ _ _ _ _ 23%bv (EAlu ALU_XOR (EAlu ALU_SRL (EMd M_MUL (ELit (2 ^ 62)) (EVar 69)) (ELit 63)) (ELit 1)) HLF ltac:(vm_compute; reflexivity)).
             match goal with U : bv_unsigned (ev E' 69) = _ |- _ => exact (rc_eof_w E' (2 ^ 62) 69 rdb eq_refl U ltac:(lia)) end. }
           destruct (Z.eq_dec (Z.land rdb 2) 0) as [L0|L0].
           ++ right. split; [rewrite S7, L0; reflexivity | intros (_ & _ & X); exact (X L0)].
           ++ left. split; [rewrite S7; rewrite (proj2 (Z.eqb_neq _ _) L0); reflexivity | split; [lia | split; [lia | exact L0]]].
        -- rc_kp HLF Hag64 sp1 R E' R' M M' KSL H20.
        -- left. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. exact SAME.
      * lsame HLF M M' (C + 512) e p D1 Ce Cp (EVar 41) (EVar 65) (EVar 66).
        apply (Kps ltac:(lia) fx' R' M' p e Hfp').
        -- llin HLF r_sp. -- unfold RNT.R_PSOME. llin HLF r_ra. -- lkeep HLF Hag64 sp1 R r_a0 51%nat r_s3. -- lkeep HLF Hag64 sp1 R r_a1 50%nat r_s2. -- llin HLF r_a2.
        -- right. split; [llin HLF r_s7 | intros (_ & X & _); lia].
        -- rc_kp HLF Hag64 sp1 R E' R' M M' KSL H20.
        -- left. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. exact SAME.
      * lsame HLF M M' (C + 512) e p D1 Ce Cp (EVar 41) (EVar 65) (EVar 66).
        apply (Kps ltac:(lia) fx' R' M' p e Hfp').
        -- llin HLF r_sp. -- unfold RNT.R_PSOME. llin HLF r_ra. -- lkeep HLF Hag64 sp1 R r_a0 51%nat r_s3. -- lkeep HLF Hag64 sp1 R r_a1 50%nat r_s2. -- llin HLF r_a2.
        -- right. split; [llin HLF r_s7 | intros (X & _); lia].
        -- rc_kp HLF Hag64 sp1 R E' R' M M' KSL H20.
        -- left. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. exact SAME.
      * lsame HLF M M' (C + 512) e p D1 Ce Cp (EVar 41) (EVar 65) (EVar 66). rewrite SAME.
        apply (Kepi ltac:(lia) fx' R' Hfp').
        -- llin HLF r_sp.
        -- rc_kp HLF Hag64 sp1 R E' R' M M' KSL H20.
  - destruct (Pp' Hk0) as [Hp1 Hp2]. change RNT.R_CHUNK with (CC.cp_pc GA.cp3).
    rc_open GA.cp3 (GA.plans 3%nat _ eq_refl) (-80) [code; e; p; rem; IS; rdb] (@nil (nat * Z)) [(20%nat, (9%nat, 8))] sp1 R M fx model K Hh Hl Hfp H2
      no_pins ltac:(rc_ad20 R C H9 H20).
    + reg_atom E sp1 R 41%nat r_s1 H9. reg_atom E sp1 R 40%nat r_s0 H8. reg_atom E sp1 R 42%nat r_a0 H10. reg_atom E sp1 R 43%nat r_a1 H11.
      gh_atom E sp1 R 64%nat 0%nat code. gh_atom E sp1 R 65%nat 1%nat e. gh_atom E sp1 R 66%nat 2%nat p. gh_atom E sp1 R 67%nat 3%nat rem. gh_atom E sp1 R 68%nat 4%nat IS. gh_atom E sp1 R 69%nat 5%nat rdb.
      unfold know_ok, GA.cp3. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
      * e_range. * e_align Hal. * e_range. * e_range. * kw32 Ev code Cc.
      * kw64 (C + 512) e Ce. * kw64 (C + 520) p Cp. * kw64 (C + 296) rem Crem. * kw64 (C + 248) IS Cis. * e_wr.
      * e_range. * kw64 IS PML.VT_ISS Cvt. * kw8 (IS + 152) rdb Crd. * e_range. * tk_kimg RO. * e_disj. * e_disj.
      * e_range. * e_range.
    + intros fx' E' R' M' k0 ps Hnth Hag HLF Hfp'.
      reg_atom E sp1 R 41%nat r_s1 H9. reg_atom E sp1 R 40%nat r_s0 H8. reg_atom E sp1 R 42%nat r_a0 H10. reg_atom E sp1 R 43%nat r_a1 H11.
      gh_atom E sp1 R 64%nat 0%nat code. gh_atom E sp1 R 65%nat 1%nat e. gh_atom E sp1 R 66%nat 2%nat p. gh_atom E sp1 R 67%nat 3%nat rem. gh_atom E sp1 R 68%nat 4%nat IS. gh_atom E sp1 R 69%nat 5%nat rdb.
      leaf_open Hag HLF E' 70%nat.
      leaves 2%nat k0 Hnth ltac:(probes_in HLF PF; pf_all PF).
      * apply (Kps ltac:(lia) fx' R' M' p' (p' + k) Hfp').
        -- llin HLF r_sp. -- unfold RNT.R_PSOME. llin HLF r_ra. -- lkeep HLF Hag64 sp1 R r_a0 51%nat r_s3. -- lkeep HLF Hag64 sp1 R r_a1 50%nat r_s2. -- llin HLF r_a2.
        -- right. split; [llin HLF r_s7 | intros (X & _); lia].
        -- rc_kp HLF Hag64 sp1 R E' R' M M' KSL H20.
        -- right. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [|split; [|split]].
           ++ lcell64 HLF (EVar 41) 512 (EAlu ALU_ADD (EVar 42) (EVar 43)). vlin.
           ++ lcell64 HLF (EVar 41) 520 (EVar 42). cbn [edenot]. assumption.
           ++ lframe HLF.
           ++ exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
      * lsame HLF M M' (C + 512) e p D1 Ce Cp (EVar 41) (EVar 65) (EVar 66). rewrite SAME.
        apply (Kepi ltac:(lia) fx' R' Hfp').
        -- llin HLF r_sp.
        -- rc_kp HLF Hag64 sp1 R E' R' M M' KSL H20.
Qed.

Lemma rp_land1 : forall x, 0 <= x <= 1 -> Z.land x 1 = x.
Proof. intros x Hx. assert (H : x = 0 \/ x = 1) by lia. destruct H as [H|H]; rewrite H; reflexivity. Qed.
Lemma s_r_psome : forall (fx : FPState) R M model K sp1 C Ev code st dn mo nte,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 C -> getr R 8%bv = Z_to_bv 64 Ev -> pok C -> pok Ev -> getr R 21%bv = Z_to_bv 64 1 -> getr R 22%bv = Z_to_bv 64 2 ->
  getr R 23%bv = Z_to_bv 64 nte -> (nte = 0 \/ nte = 1) ->
  L5.u32_at RSEGS M Ev code -> 0 <= code < 2 ^ 31 -> L5.u8_at RSEGS M (C + 528) st -> L5.u8_at RSEGS M (C + 532) dn -> L5.u8_at RSEGS M (C + 531) mo ->
  0 <= st <= 255 -> 0 <= dn <= 1 -> 0 <= mo <= 1 ->
  (code <> 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> TK.keepsR KSQ R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RNT.EPI M model) K) ->
  (code = 0 -> nte = 0 -> st = 1 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> TK.keepsR KSQ R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RNT.DONE M model) K) ->
  (code = 0 -> Z.land mo 1 = 0 -> (nte <> 0 \/ (st <> 1 /\ (st = 2 \/ Z.land dn 1 <> 0))) -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) ->
      TK.keepsR KSQ R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' RNT.EPI M model) K) ->
  (code = 0 -> Z.land mo 1 <> 0 -> (nte <> 0 \/ (st <> 1 /\ (st = 2 \/ Z.land dn 1 <> 0))) -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) ->
      getr R' 21%bv = Z_to_bv 64 1 -> getr R' 22%bv = Z_to_bv 64 2 -> TK.keepsR KSQ R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' RNT.LOOP M model) K) ->
  (code = 0 -> nte = 0 -> st <> 1 -> st <> 2 -> Z.land dn 1 = 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> TK.keepsR KSQ R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RNT.TAILEPI M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RNT.R_PSOME M model) K.
Proof.
  intros fx R M model K sp1 C Ev code st dn mo nte Hh Hl Hfp H2 [Hsp Hal] H9 H8 [Hc1 Hc2] [He1 He2] H21 H22 H23 Rnte Cc Rc Cst Cdn Cmo Rst Rdn Rmo
         Kerr Kdone Kstop Kloop Keof.
  change RNT.R_PSOME with (CC.cp_pc GA.cp2).
  hv_open GA.cp2 (GA.plans 2%nat _ eq_refl) (-80) [code; st; dn; mo] [(21%nat, 1); (22%nat, 2)] sp1 R M fx model K Hh Hl Hfp H2 ltac:(pins56 H21 H22).
  - reg_atom E sp1 R 41%nat r_s1 H9. reg_atom E sp1 R 40%nat r_s0 H8.
    gh_atom E sp1 R 64%nat 0%nat code. gh_atom E sp1 R 65%nat 1%nat st. gh_atom E sp1 R 66%nat 2%nat dn. gh_atom E sp1 R 67%nat 3%nat mo.
    unfold know_ok, GA.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_range. + kw32 Ev code Cc. + kw8 (C + 528) st Cst. + kw8 (C + 532) dn Cdn. + kw8 (C + 531) mo Cmo.
    + e_range. + e_range.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 R 41%nat r_s1 H9. reg_atom E sp1 R 40%nat r_s0 H8. assert (Rnte' : 0 <= nte < 2 ^ 64) by lia. reg_atom E sp1 R 55%nat r_s7 H23.
    gh_atom E sp1 R 64%nat 0%nat code. gh_atom E sp1 R 65%nat 1%nat st. gh_atom E sp1 R 66%nat 2%nat dn. gh_atom E sp1 R 67%nat 3%nat mo.
    leaf_open Hag HLF E' 68%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    pose proof (rp_land1 mo Rmo) as LEm. pose proof (rp_land1 dn Rdn) as LEd.
    leaves 10%nat k Hnth ltac:(probes_in HLF PF; pf_pre PF; lazymatch type of PF with context [alu64 ALU_SLTU] => pf_sltu PF code | _ => idtac end; pf_all PF;
      first [ exfalso; lia
            | apply (Kerr ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | hv_keeps HLF Hag64 sp1 R E' R' M M' KSQ]
            | apply (Kdone ltac:(lia) ltac:(lia) ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | hv_keeps HLF Hag64 sp1 R E' R' M M' KSQ]
            | apply (Kstop ltac:(lia) ltac:(lia) ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | hv_keeps HLF Hag64 sp1 R E' R' M M' KSQ]
            | apply (Kloop ltac:(lia) ltac:(lia) ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | llin HLF r_s5 | llin HLF r_s6 | hv_keeps HLF Hag64 sp1 R E' R' M M' KSQ]
            | apply (Keof ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | hv_keeps HLF Hag64 sp1 R E' R' M M' KSQ] ]).
Qed.
End S.
End RNS.
