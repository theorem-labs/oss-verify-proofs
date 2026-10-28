(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg FPSteps
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmCurDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ChunkKit_u Skel_u VisitC_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges2_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_visit_double_csrc_u Cut_visit_double_b_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module VISD.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Module GD := Cut_visit_double_csrc_u.
Module GE := Cut_visit_double_b_csrc_u.
Lemma ret_double : CL.is_ret_at RSEGS 0x41d28. Proof. CL.solve_is_ret. Qed.

Definition FSD_PC : Z := 0x41d20.
Definition fsd_chk : bool :=
  match fetch_word RSEGS (Z_to_bv 64 FSD_PC) with
  | Some w => if is_ecall w then false else
              match decode_any w with
              | Some (FStore FMT_D rs1 rs2 imm, sz) => (Z.eqb sz 4 && bv_eqb rs1 12%bv && bv_eqb rs2 10%bv && Z.eqb (bv_signed imm) 32)%bool
              | _ => false end
  | None => false end.
Lemma fsd_chk_ok : fsd_chk = true.
Proof. vmc_refl. Qed.
Lemma vaddi_lit : forall a k, 0 <= a -> a + k < 2 ^ 64 -> 0 <= k -> v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof.
  intros a k H0 H1 H2. unfold v_addi. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small a) by lia. reflexivity.
Qed.
Lemma bv_eqb_true : forall n (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. apply bv_eq. unfold bv_eqb in H. apply Z.eqb_eq in H. exact H. Qed.
Lemma fsd_step : forall (fx : FPState) R (M : mem) V, getr R 12%bv = Z_to_bv 64 V -> 0 <= V -> V + 48 < 2 ^ 64 ->
  store_ok RSEGS M (Z_to_bv 64 (V + 32)) 8 = true ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 FSD_PC) M (seg_rom RSEGS))
               (@mkst fx R (Z_to_bv 64 (FSD_PC + 4)) (wbytes M (Z_to_bv 64 (V + 32)) (word_to_le_bytes 8 (reg_get (@fp_regs fx) 10%bv))) (seg_rom RSEGS)).
Proof.
  intros fx R M V HV H0 H1 Hok. pose proof fsd_chk_ok as C. unfold fsd_chk in C.
  destruct (fetch_word RSEGS (Z_to_bv 64 FSD_PC)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:He; [discriminate|].
  destruct (decode_any w) as [[i sz]|] eqn:Hd; [|discriminate].
  destruct i; try discriminate. destruct fmt; try discriminate.
  apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
  apply Z.eqb_eq in C1, C4. apply bv_eqb_true in C2, C3. subst sz rs1 rs2.
  assert (Ha : v_addi (getr R 12%bv) (bv_signed imm) = Z_to_bv 64 (V + 32)) by (rewrite HV, C4; apply vaddi_lit; lia).
  pose proof (fp_step_fsd fx RSEGS R (Z_to_bv 64 FSD_PC) M (seg_rom RSEGS) w 12%bv 10%bv imm (Z_to_bv 64 (V + 32)) Hf He Hd Ha Hok) as Hs.
  rewrite <- (vaddi_lit FSD_PC 4) by (unfold FSD_PC; lia). apply msteps_one; [reflexivity | exact Hs].
Qed.

Lemma wbytes_u64_out : forall (M : mem) A bs a v, length bs = 8%nat -> 0 <= A -> A + 8 <= 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= A \/ A + 8 <= a) ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS (wbytes M (Z_to_bv 64 A) bs) a v.
Proof.
  intros M A bs a v Hl H0 H1 H2 H3 Hd Hu. apply (L5C.u64_at_agree RSEGS M _ a v); [| lia | lia | exact Hu].
  intros i Hi. apply (CK.wbytes_samem M A bs ltac:(lia) ltac:(rewrite Hl; lia) i ltac:(lia)). rewrite Hl. cbn. lia.
Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma rp_trans : forall R1 R2 R3, regs_preserved R1 R2 -> regs_preserved R2 R3 -> regs_preserved R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr. rewrite (H2 r Hr), (H1 r Hr). reflexivity. Qed.

Theorem visit_double_ok : PMS.visit_double_spec L PMS.PC_VIS_DOUBLE.
Proof.
  intros V sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & (VP & VD) & (O1 & O2 & O3) & _) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0 in A0. pose proof (L5C.stk_floor _ _ _ _ (conj S1 (conj S2 (conj S3 (conj S4 S5))))) as FLR. unfold PMS.VIS_SCR in *.
  change PMS.PC_VIS_DOUBLE with (CC.cp_pc GD.cp0).
  ck_open FPM GD.cp0 (GD.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0.
    unfold know_ok, GD.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_range. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].

    assert (A2' : getr R' 12%bv = Z_to_bv 64 V) by tk_lin HLF (12%bv : reg).
    assert (A0' : getr R' 10%bv = Z_to_bv 64 1) by tk_lin HLF (10%bv : reg).
    assert (SP' : getr R' 2%bv = Z_to_bv 64 sp) by tk_lin HLF (2%bv : reg).
    assert (RA' : getr R' 1%bv = Z_to_bv 64 r).
    { rewrite (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ SK.KRA 1%bv HLF ltac:(vm_compute; reflexivity) Hag64 ltac:(ck_in)). exact Hra. }
    assert (RP1 : regs_preserved R R').
    { apply CK.rp_of_keeps; [rewrite SP', Hsp; reflexivity|].
      intros q Hq. exact (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ SK.KRA q HLF ltac:(vm_compute; reflexivity) Hag64 (SK.csr_kra _ Hq)). }
    assert (F8 : L5.u64_at RSEGS M' (V + 8) 128) by (ck_cell64 HLF (EVar 42) 8 (ELit 128); reflexivity).
    assert (DV' : L5.defined M' (V + 8) 40) by exact (VIS.ev_defined M M' V VD (CC.lf_grows _ _ _ _ _ _ _ HLF)).
    assert (Hok : store_ok RSEGS M' (Z_to_bv 64 (V + 32)) 8 = true).
    { pose proof (CK.lf_cell _ _ _ _ _ _ (KWr (SA (EVar 42) 8) (ELit 40)) HLF ltac:(vm_compute; reflexivity)) as KW. cbn [kentry_ok] in KW. destruct KW as (_ & KW).
      assert (Es : estart E' (SA (EVar 42) 8) = V + 8) by ev_start.
      assert (El : elenZ E' (ELit 40) = 40) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; lia).
      pose proof (KW 24 8%nat ltac:(lia) ltac:(rewrite El; cbn; lia)) as W24. rewrite Es in W24. replace (V + 8 + 24) with (V + 32) in W24 by lia. exact W24. }
    set (bs := word_to_le_bytes 8 (reg_get (@fp_regs fx') 10%bv)).
    set (M1 := wbytes M' (Z_to_bv 64 (V + 32)) bs).
    assert (Hbl : length bs = 8%nat) by reflexivity.
    pose proof (fsd_step fx' R' M' V A2' ltac:(lia) ltac:(lia) Hok) as HMS. fold bs M1 in HMS.
    change (SR.ps_pc _) with FSD_PC. unfold PML.cfg. eapply L5.cps_of_msteps; [exact Hh | exact Hl | exact HMS |].
    pose proof (FPM _ _ _ _ _ _ _ _ HMS Hfp') as Hfp1.
    assert (F8' : L5.u64_at RSEGS M1 (V + 8) 128) by (apply wbytes_u64_out; [exact Hbl | lia | lia | lia | lia | lia | exact F8]).
    assert (G1 : mem_grows M' M1) by exact (CK.wbytes_grows M' _ bs).
    assert (DV1 : L5.defined M1 (V + 8) 40) by exact (L5.defined_grows M' M1 _ _ G1 DV').

    clear Hag64.
    change (FSD_PC + 4) with (CC.cp_pc GE.cp0).
    ck_open FPM GE.cp0 (GE.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp R' M1 fx' model K Hh Hl Hfp1 SP' ck_no_pins.
    + ck_reg E0 (12%bv : reg) A2'.
      unfold know_ok, GE.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
      * e_range. * e_align S1. * e_range. * e_unk. * e_wr. * ck_kw64 (V + 8) 128 F8'.
    + intros fx2 E2 R2 M2 k2 ps2 Hnth2 Hag2 HLF2 Hfp2.
      ck_reg E0 (12%bv : reg) A2'. ck_reg E0 (10%bv : reg) A0'. ck_leaf Hag2 E2.
      ck_leaf_k k2 Hnth2; [|ck_leaf_end k2 Hnth2].
      apply (SK.fin_ret _ _ sp R' _ _ E2 R2 M1 M2 fx2 model K _ r HLF2 Hag64 ret_double Hh Hl eq_refl eq_refl RA' Hrok SP' ltac:(lia)). intros RP2.
      assert (DV2 : L5.defined M2 (V + 8) 40) by exact (L5.defined_grows M1 M2 _ _ (CC.lf_grows _ _ _ _ _ _ _ HLF2) DV1).
      destruct (PB2.cell_exists M2 (V + 32) 8 ltac:(lia)) as (x & Rx & Hx); [eapply (L5.defined_sub _ _ _ _ _ DV2); lia|].
      apply (Hcont fx2 R2 M2 Hfp2).
      * split; [unfold PML.a0; tk_lin HLF2 (10%bv : reg)|]. exists (PMCUR.EvDbl x). split; [exists x; reflexivity|].
        unfold PMCUR.ev_at. split; [exact DV2|]. split; [ck_cell64 HLF2 (EVar 44) 8 (ELit 128); reflexivity | exact Hx].
      * exact (rp_trans R R' R2 RP1 RP2).
      * apply (CK.samem_frame_but (fun a => ~ (V + 8 <= a < V + 48))).
        -- apply (TK.samem_trans _ M M' M2).
           ++ apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk. cbn [CC.cp_F]. tk_outside.
           ++ apply (TK.samem_trans _ M' M1 M2).
              ** intros a Ha Hk. apply (CK.wbytes_samem M' (V + 32) bs ltac:(lia) ltac:(rewrite Hbl; lia) a Ha). rewrite Hbl. cbn. lia.
              ** apply (TK.frame_samem _ _ _ _ _ _ _ HLF2). intros a Ha Hk. cbn [CC.cp_F]. tk_outside.
        -- intros a Ha. pose proof (Ha (V + 8, 40) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
      * exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ (CC.lf_grows _ _ _ _ _ _ _ HLF) G1) (CC.lf_grows _ _ _ _ _ _ _ HLF2)).
Qed.
End S.
End VISD.

