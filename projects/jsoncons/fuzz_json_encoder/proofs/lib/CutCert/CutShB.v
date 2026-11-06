(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA CutShA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CSL1.
Definition mem := (word -> option byte).

(* [comment removed for export] *)
Definition site_chk1 (segs : list Segment) (pc : Z) : option (nat * nat) :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w1 =>
      if is_ecall w1 then None else
      match CSL.dec_load1 w1 with
      | Some (_, rd, rs, imm) => if (Z.eqb (bv_signed imm) 0 && negb (bv_eqb rd 0%bv))%bool then Some (ridx rd, ridx rs) else None
      | None => None
      end
  | None => None
  end.
Lemma site_chk1_sound : forall segs pc rd rs, site_chk1 segs pc = Some (rd, rs) ->
  exists w1 sx rdr rsr imm,
    fetch_word segs (Z_to_bv 64 pc) = Some w1 /\ is_ecall w1 = false /\ decode_any w1 = Some (Load SZ1 sx rdr rsr imm, 4) /\ bv_signed imm = 0 /\
    rdr <> 0%bv /\ ridx rdr = rd /\ ridx rsr = rs.
Proof.
  intros segs pc rd rs H. unfold site_chk1 in H.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w1|] eqn:Hf1; [|discriminate].
  destruct (is_ecall w1) eqn:He1; [discriminate|].
  destruct (CSL.dec_load1 w1) as [[[[sx rdr] rsr] imm]|] eqn:Hd1; [|discriminate].
  lazymatch type of H with (if ?bb then _ else _) = _ => destruct bb eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Himm Hrd0]. apply Z.eqb_eq in Himm. apply negb_true_iff in Hrd0. injection H as <- <-.
  exists w1, sx, rdr, rsr, imm.
  split; [reflexivity|]. split; [exact He1|]. split; [exact (CSL.dec_load1_sound _ _ _ _ _ Hd1)|]. split; [exact Himm|].
  split; [intros ->; rewrite bv_eqb_refl in Hrd0; discriminate|| (intros EE; subst; cbn in Hrd0; discriminate)|]. split; reflexivity.
Qed.

Section Leaf.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBrest : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable Cred : nat -> env -> credit -> Prop.
Variable D0 : Z.
Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Variable XI : nat -> env -> list (Z * Z) -> mem -> Model -> Prop.

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).
Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 XI).

Theorem shload1_leaf : forall i c ps j cj s rd rs cur SBz kv a b,
  nth_error CPS j = Some cj ->
  site_chk1 (hl_segs L) (SR.ps_pc ps) = Some (rd, rs) ->
  CSL.shl_chk NF c ps cj s rd rs (SR.ps_pc ps + 4) cur SBz kv a b = true ->
  CHA.goto_amb_chk NF d c (nth i BLS []) (nth j BLS []) (nth i FFS []) (nth j FFS []) s = true ->
  0 <= SR.ps_pc ps /\ SR.ps_pc ps + 4 < 2 ^ 64 ->
  (forall E E' R R' A M model M1 model1,
     CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> XI i E A M model -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
     (exists zb zoff gr B, In (KZero (SA zb zoff) gr) (SR.ps_cells ps) /\ estart E' (SA zb zoff) = B / 8 + SBz /\
        B mod 8 = 0 /\ B <= bv_unsigned (edenot E' cur) < B + 8 * bv_unsigned (edenot E' gr))
     /\ XI j (CC.env_over NF s E') A M1 model1) ->
  (forall E E' R' M M' cr, env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr -> Cred j (CC.env_over NF s E') cr) ->
  CCA.leaf_ok (hl_segs L) CPS AMBX K FPI i c ps.
Proof.
  intros i c ps j cj s rd rs cur SBz kv a b Hcj Hsite Hchk Hgchk Hpc USER CRED fx' E R A M model E' R' M1 model1 HAt [HA HXI] HFP Hag HLF HIH.
  (* [comment removed for export] *)
  unfold CSL.shl_chk in Hchk.
  apply andb_prop in Hchk as [Hchk Xkvar]. apply andb_prop in Hchk as [Hchk Xklt]. apply andb_prop in Hchk as [Hchk Xa64]. apply andb_prop in Hchk as [Hchk Xba]. apply andb_prop in Hchk as [Hchk Xb0].
  apply andb_prop in Hchk as [Hchk Xmj]. apply andb_prop in Hchk as [Hchk Xmi]. apply andb_prop in Hchk as [Hchk Xmv]. apply andb_prop in Hchk as [Hchk Xkn]. apply andb_prop in Hchk as [Hchk Xregs].
  apply andb_prop in Hchk as [Hchk Xrs]. apply andb_prop in Hchk as [Hchk Xrs32]. apply andb_prop in Hchk as [Hchk Xrs0]. apply andb_prop in Hchk as [Hchk Xrd32]. apply andb_prop in Hchk as [Hchk Xrd0].
  apply andb_prop in Hchk as [Hchk Xnf].
  apply Z.eqb_eq in Hchk. apply Nat.leb_le in Xnf. apply Nat.ltb_lt in Xrd0. apply Nat.ltb_lt in Xrd32. apply Nat.ltb_lt in Xrs0. apply Nat.ltb_lt in Xrs32.
  apply CSL.reg_is_sound in Xrs. apply expr_eqb_eq in Xmi. apply expr_eqb_eq in Xmj. apply Z.leb_le in Xb0. apply Z.ltb_lt in Xba. apply Z.leb_le in Xa64. apply Nat.ltb_lt in Xklt.
  (* [comment removed for export] *)
  destruct (site_chk1_sound _ _ _ _ Hsite) as (w1 & sx & rd0 & rs0 & imm & Hf1 & He1 & Hd1 & Himm & Hrdnz & Erd & Ers0).
  (* [comment removed for export] *)
  pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
  destruct (USER E E' R R' A M model M1 model1 HAt HA HXI Hag HLF) as ((zb & zoff & gr & ub & Hinz & Hest & Hal & Hlo & Hhi) & HXIj).
  pose proof (CC.lf_cells _ _ _ _ _ _ _ HLFv _ Hinz) as (Hflz & Hz). unfold elenZ in Hz. rewrite Hest in Hz.
  set (uc := bv_unsigned (edenot E' cur)) in *. set (ug := bv_unsigned (edenot E' gr)) in *.
  destruct Hflz as (F1 & F2 & F3 & F4). rewrite Hest in F1, F2, F4. unfold elenZ in F3, F4. fold ug in F3, F4, Hz.
  pose proof (u64_range (edenot E' cur)) as Rc. fold uc in Rc. change two64 with (2 ^ 64) in Rc.
  (* [comment removed for export] *)
  destruct (CC.lf_regs _ _ _ _ _ _ _ HLFv _ _ Xrs) as [_ Hrs].
  set (rsr := (Z_to_bv 5 (Z.of_nat rs)) : reg) in Hrs.
  assert (Ers : rs0 = rsr) by (unfold rsr; rewrite <- Ers0; symmetry; apply CC.reg_of_ridx).
  assert (Hrsv : bv_unsigned (getr R' rs0) = (uc / 8 + SBz) mod 2 ^ 64).
  { rewrite Ers, Hrs. change (edenot E' (EAlu ALU_ADD (EAlu ALU_SRL cur (ELit 3)) (ELit SBz))) with (alu64 ALU_ADD (edenot E' (EAlu ALU_SRL cur (ELit 3))) (Z_to_bv 64 SBz)).
    rewrite u_add64, u_srl_lit. change (2 ^ ((3 mod two64) mod 64)) with 8. fold uc. rewrite u_lit64. change two64 with (2 ^ 64). apply Z.add_mod_idemp_r. lia. }
  (* [comment removed for export] *)
  assert (Hz0 : CCA.vis A model1 M1 (getr R' rs0) = Some (Z_to_bv 8 0)).
  { assert (Hq : ub = 8 * (ub / 8)) by (pose proof (Z.div_mod ub 8 ltac:(lia)) as DM; lia).
    assert (Hidx : 0 <= uc / 8 - ub / 8 < ug).
    { split; [apply Z.le_0_sub; apply Z.div_le_mono; lia|].
      assert (uc / 8 < ub / 8 + ug); [apply Z.div_lt_upper_bound; lia | lia]. }
    specialize (Hz (uc / 8 - ub / 8) Hidx). rewrite <- Hz. f_equal. rewrite <- (Z_to_bv_bv_unsigned 64 (getr R' rs0)), Hrsv.
    rewrite Z.mod_small by lia. f_equal. lia. }
  (* [comment removed for export] *)
  pose proof (CHA.leaf_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
                i c ps E E' R R' A M model M1 model1) as HA1.
  unfold CHA.goto_amb_chk in Hgchk. pose proof Hgchk as Hgchk'. apply andb_prop in Hgchk' as [Hgchk' _]. apply andb_prop in Hgchk' as [Hfoot _].
  specialize (HA1 Hfoot HAt HA Hag HLF).
  destruct (CHA.aamb_model L ar C HI HIok LY_below NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i E A M1 model1 HA1) as (Hh1 & HMI1 & HAwf & Hoff1).
  set (H1 := ahid A model1).
  set (R2 := regupd R' rd0 (Z_to_bv 64 0)).
  destruct Hpc as (Hpc0 & Hpc4).
  assert (X0R : getr R' 0%bv = Z_to_bv 64 0) by (exact (CC.lf_x0 _ _ _ _ _ _ _ HLFv)).
  assert (MS : msteps (hl_segs L) (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) (mrestrict H1 M1) (seg_rom (hl_segs L)))
                                  (@mkst fx' R2 (Z_to_bv 64 (SR.ps_pc ps + 4)) (mrestrict H1 M1) (seg_rom (hl_segs L)))).
  { eapply mst_step; [reflexivity | | apply mst_refl].
    destruct sx.
    + rewrite (step_lb (hl_segs L) R' (Z_to_bv 64 (SR.ps_pc ps)) (mrestrict H1 M1) (seg_rom (hl_segs L)) w1 rd0 rs0 imm (Z_to_bv 8 0) Hf1 He1 Hd1).
      * rewrite (proj2 (bv_eqb_neq rd0 0%bv) Hrdnz) || (destruct (bv_eqb rd0 0%bv) eqn:EE; [exfalso; apply Hrdnz; apply bv_eq; unfold bv_eqb in EE; apply Z.eqb_eq in EE; exact EE|]).
        rewrite CSL.pc4 by lia. reflexivity.
      * rewrite Himm. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply CSL.rdn1. exact Hz0.
    + rewrite (step_lbu (hl_segs L) R' (Z_to_bv 64 (SR.ps_pc ps)) (mrestrict H1 M1) (seg_rom (hl_segs L)) w1 rd0 rs0 imm (Z_to_bv 8 0) Hf1 He1 Hd1).
      * rewrite (proj2 (bv_eqb_neq rd0 0%bv) Hrdnz) || (destruct (bv_eqb rd0 0%bv) eqn:EE; [exfalso; apply Hrdnz; apply bv_eq; unfold bv_eqb in EE; apply Z.eqb_eq in EE; exact EE|]).
        rewrite CSL.pc4 by lia. reflexivity.
      * rewrite Himm. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply CSL.rdn1. exact Hz0. }
  eapply (L5LZ.cps_of_msteps_lazy (hl_segs L) H1 A fx' fx' R' _ M1 R2 _ (mrestrict H1 M1) model1 K Hoff1 LY_nowrap (L5LZ.lazy_cover_ahid A model1) HAwf HMI1 Hh1 MS).
  intros model2 HMI2 HS12 _.
  replace (munrestrict H1 M1 (mrestrict H1 M1)) with M1
    by (apply FunctionalExtensionality.functional_extensionality; intros x; unfold munrestrict, mrestrict; destruct (H1 x); reflexivity).
  assert (HLF2 : CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model2).
  { constructor.
    - rewrite (CCA.vis_sbm A model1 model2 M1 HS12). exact HLFv.
    - exact (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF).
    - exact (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF).
    - exact (CCA.lfa_hid _ _ _ _ _ _ _ _ _ _ HLF).
    - exact (same_but_materialized_trans _ _ _ (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF) HS12).
    - exact HMI2. }
  rewrite <- Hchk.
  set (E2 := CC.env_over NF s E').
  apply (HIH j cj fx' E2 R2 A M1 model2 Hcj).
  - split.
    + intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
      * assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er).
        cbn [edenot]. unfold R2. rewrite getr_other by (intros EE; apply Hrdnz; symmetry; exact EE). exact X0R.
      * assert (Hr : (1 <= ridx r < 32)%nat).
        { unfold ridx. pose proof (bv_unsigned_in_range _ r) as B. change (bv_modulus 5) with 32 in B.
          unfold bv_eqb in Er. apply Z.eqb_neq in Er. change (bv_unsigned (0%bv : bv 5)) with 0 in Er. lia. }
        rewrite forallb_forall in Xregs. specialize (Xregs (ridx r) ltac:(apply in_seq; lia)).
        destruct (Nat.eqb (ridx r) rd) eqn:Erd'.
        -- apply Nat.eqb_eq in Erd'. assert (Err : r = rd0) by (rewrite <- (CC.reg_of_ridx r), <- (CC.reg_of_ridx rd0); rewrite Erd', Erd; reflexivity).
           apply expr_eqb_eq in Xregs. unfold R2. rewrite Err, (getr_same _ _ _ Hrdnz). unfold E2. rewrite <- CC.esubstL_denot. rewrite Erd, <- Erd', Xregs. reflexivity.
        -- apply Nat.eqb_neq in Erd'. apply CSL.reg_is_sound in Xregs. destruct (CC.lf_regs _ _ _ _ _ _ _ HLFv _ _ Xregs) as [_ Hg]. rewrite CC.reg_of_ridx in Hg.
           unfold R2. rewrite getr_other by (intros EE; apply Erd'; rewrite EE; exact Erd). rewrite Hg. unfold E2. apply CC.esubstL_denot.
    + rewrite (CCA.vis_sbm A model1 model2 M1 HS12).
      unfold know_ok. apply Forall_forall. intros X' HX'. rewrite forallb_forall in Xkn. specialize (Xkn X' HX'). cbv zeta in Xkn.
      apply (CC.kentry_ok_ksubstL (hl_segs L) NF s E' _ X'). apply orb_prop in Xkn. destruct Xkn as [Xkn|Xkn].
      * apply CC.has_cell_In in Xkn. exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ Xkn).
      * apply (CX.fact2_ok_sound (hl_segs L) E' _ (SR.ps_cells ps) _ ltac:(unfold know_ok; apply Forall_forall; intros Y HY; exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HY)) Xkn).
  - split.
    + exact (CHA.goto_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
               i c ps j s Hgchk CRED E R A M model E' R' M1 model2 HAt HA Hag HLF2).
    + exact (proj2 (USER E E' R R' A M model M1 model2 HAt HA HXI Hag HLF2)).
  - exact HFP.
  - unfold CC.meas. unfold E2. rewrite <- CC.esubstL_denot, Xmj. rewrite Xmi. rewrite Xmi in Xmv.
    rewrite (SR.edenot_agree_AP _ E E' _ Hag Xmv).
    unfold CSL.kvar_ok in Xkvar. apply existsb_exists in Xkvar as (Xk & HXk & Hkb). destruct Xk as [| | | | |ek lo hi| | | |]; try discriminate Hkb.
    destruct ek as [|v| | | | | |]; try discriminate Hkb. apply andb_prop in Hkb as [Hkb Hkhi]. apply andb_prop in Hkb as [Hv Hklo].
    apply Nat.eqb_eq in Hv. apply Z.leb_le in Hklo. apply Z.leb_le in Hkhi. subst v.
    pose proof (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HXk) as HK. cbn [kentry_ok edenot] in HK.
    rewrite !CSL.u_meas_form by lia. lia.
Qed.
End Leaf.
End CSL1.
