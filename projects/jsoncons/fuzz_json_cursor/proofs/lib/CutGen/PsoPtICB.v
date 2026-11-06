(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtC CutRtD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA PtKitB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_psome_cboth_T Cut_psome_cboth_D Cut_psome_cboth.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsKitA PsoInstCB PsoSemA PsoSemCA PsoKnCB ParseSomeChkCB PsoBaseCB PsoAuxCB PsoXiCB PsoLinkCB PsoFrmCB PsoExitCB PsoStCB PsoCkCB PsoKnOkCB PsoPtCB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_cboth.

Module PSOPI.
Import PSOP.

Lemma CO_SKIPSP : forall ps cells t l d z, callee_ok SKIPSP ps cells t l d z =
  (CL.ps_reg_is ps 11 (EAlu Instr.ALU_ADD PE (ELit 200)) && PSO.expectb z && PSO.is_same (PSO.d_wptr d) && expr_eqb (PSO.v_wptr t) PSO.CURH && PSO.lo_ge cells (EVar JV) 1
   && match CAX.cell_at cells (PSO.v_wptr l) 0 1 with Some eb => rng_all cells eb wsb | None => false end)%bool.
Proof. intros. reflexivity. Qed.
Lemma CO_PNULL : forall ps cells t l d z, callee_ok PNULL ps cells t l d z =
  (CL.ps_reg_is ps 11 VE && CL.ps_reg_is ps 12 EE && PSO.expectb z && PSO.is_same (PSO.d_wptr d) && expr_eqb (PSO.v_wptr t) PSO.CURH && PSO.lo_ge cells (EVar JV) 1)%bool.
Proof. intros. reflexivity. Qed.
Lemma CO_LIT : forall pc ps cells t l d z, pc = PTRUE \/ pc = PFALSE -> callee_ok pc ps cells t l d z =
  (CL.ps_reg_is ps 11 (PSO.v_wptr l) && CL.ps_reg_is ps 12 VE && CL.ps_reg_is ps 13 EE && PSO.expectb z && PSO.is_same (PSO.d_wptr d) && expr_eqb (PSO.v_wptr t) PSO.CURH
   && PSO.lo_ge cells (EVar JV) 1)%bool.
Proof. intros pc ps cells t l d z [->| ->]; reflexivity. Qed.
Lemma CO_CONT : forall pc ps cells t l d z, pc = BOBJ \/ pc = BARR \/ pc = EOBJ \/ pc = EARR -> callee_ok pc ps cells t l d z =
  (CL.ps_reg_is ps 11 VE && CL.ps_reg_is ps 12 EE && negb (PSO.ccrb z) && negb (Z.eqb z 15))%bool.
Proof. intros pc ps cells t l d z [->|[->|[->| ->]]]; reflexivity. Qed.
Lemma CO_BMEMBER : forall ps cells t l d z, callee_ok BMEMBER ps cells t l d z = (CL.ps_reg_is ps 11 EE && Z.eqb z 7)%bool.
Proof. intros. reflexivity. Qed.
Lemma CO_PSTRING : forall ps cells t l d z, callee_ok PSTRING ps cells t l d z =
  (CL.ps_reg_is ps 11 (PSO.v_wptr l) && CL.ps_reg_is ps 12 VE && CL.ps_reg_is ps 13 EE && Z.eqb z 15 && PSO.lo_ge cells (EVar JV) 1
   && (expr_eqb (PSO.v_wptr l) PSO.CURH || expr_eqb (PSO.v_wptr l) (EAlu Instr.ALU_ADD PSO.CURH (ELit 1))))%bool.
Proof. intros. reflexivity. Qed.
Lemma CO_PNUMBER : forall ps cells t l d z, callee_ok PNUMBER ps cells t l d z =
  (CL.ps_reg_is ps 11 (PSO.v_wptr l) && CL.ps_reg_is ps 12 VE && CL.ps_reg_is ps 13 EE && Z.eqb z 17 && expr_eqb (nth 11 (CA.ps_reglist ps) (ELit 0)) (PSO.v_wptr l))%bool.
Proof. intros. reflexivity. Qed.
Lemma CO_END : forall pc ps cells t l d z, pc = ENDINT \/ pc = ENDFRAC -> callee_ok pc ps cells t l d z =
  (CL.ps_reg_is ps 11 VE && CL.ps_reg_is ps 12 EE && Z.eqb z 17 && PSO.is_same (PSO.d_nst d) && rng_all cells (PSO.v_nst l) nfin)%bool.
Proof. intros pc ps cells t l d z [->| ->]; reflexivity. Qed.
Lemma SCR_PF : PMSA.PF_SCR mod 8 = 0 /\ 0 <= PMSA.PF_SCR /\ 672 + PMSA.PF_SCR <= 10496.
Proof. split; [reflexivity|]. split; apply Z.leb_le; reflexivity. Qed.
Lemma SCR_EN : PMSA.ENDNUM_SCR mod 8 = 0 /\ 0 <= PMSA.ENDNUM_SCR /\ 672 + PMSA.ENDNUM_SCR <= 10496.
Proof. split; [reflexivity|]. split; apply Z.leb_le; reflexivity. Qed.

Lemma EXPB : forall z, PSO.expectb z = true -> PML.is_expect z.
Proof. intros z H. unfold PSO.expectb, PSO.inb in H. apply existsb_exists in H as (y & Hy & Hz). apply Z.eqb_eq in Hz. subst y. exact Hy. Qed.
Lemma CCRB : forall z, PSO.ccrb z = false -> ~ PML.comment_or_cr z.
Proof.
  intros z H [X|X]; unfold PSO.ccrb, PSO.commentb in H; apply orb_false_iff in H as [H1 H2]; [|apply Z.eqb_neq in H2; apply H2; exact X].
  apply andb_false_iff in H1 as [Y|Y]; apply Z.leb_gt in Y; lia.
Qed.
Lemma WP_same : forall cells t l, PSO.is_same (PSO.d_wptr (PSO.mkdelta cells t l)) = true -> PSO.v_wptr l = PSO.v_wptr t.
Proof.
  intros cells t l H. cbn [PSO.mkdelta PSO.d_wptr] in H. unfold PSO.fdelta in H.
  destruct (expr_eqb (PSO.v_wptr t) (PSO.v_wptr l)) eqn:X; [apply expr_eqb_eq in X; symmetry; exact X|].
  destruct (PSO.v_wptr l); discriminate H.
Qed.
Lemma RNGALL : forall segs Ex (Mv : mem) cells e f, know_ok segs Ex Mv cells -> rng_all cells e f = true -> f (CL5A.uv Ex e) = true /\ 0 <= CL5A.uv Ex e <= 255.
Proof.
  intros segs Ex Mv cells e f HK H. unfold rng_all in H. destruct (CX.range3 cells e) as [[lo hi]|] eqn:HR; [|discriminate H].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. pose proof (CX.range3_sound _ _ _ _ _ _ _ HK HR) as X.
  change (bv_unsigned (edenot Ex e)) with (CL5A.uv Ex e) in X. split; [|lia].
  rewrite forallb_forall in H3. apply H3. unfold PSO.zseq. apply in_map_iff. exists (Z.to_nat (CL5A.uv Ex e - lo)).
  split; [rewrite Z2Nat.id by lia; lia | apply in_seq; lia].
Qed.
Lemma INB : forall z l, PSO.inb z l = true -> In z l.
Proof. intros z l H. unfold PSO.inb in H. apply existsb_exists in H as (y & Hy & Hz). apply Z.eqb_eq in Hz. subst y. exact Hy. Qed.

Definition u0_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TOther pc => if (PSO.inb pc PT && negb (PSO.dead_chk i ps pc) && negb (PSO.inb pc [ENDINT; ENDFRAC]))%bool then negb (PSO.u0 i) else true | _ => true end.
Lemma U0_all : CH2.leaves_all G.CPS G.TAGS u0_chk = true. Proof. vmc_refl. Qed.
Lemma U0PT : forall i c k ps0 pc, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> In pc PT -> PSO.dead_chk i ps0 pc = false -> pc <> ENDINT -> pc <> ENDFRAC ->
  PSO.u0 i = false.
Proof.
  intros i c k ps0 pc IL Hin Hd N1 N2. pose proof (CH2.leaves_all_sound _ _ _ U0_all _ _ _ _ _ IL) as X. cbn [u0_chk] in X. rewrite Hd in X.
  replace (PSO.inb pc PT) with true in X by (symmetry; unfold PSO.inb; apply existsb_exists; exists pc; split; [exact Hin | apply Z.eqb_refl]).
  replace (PSO.inb pc [ENDINT; ENDFRAC]) with false in X by (symmetry; unfold PSO.inb; cbn [existsb]; rewrite (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2); reflexivity).
  cbn [andb negb] in X. apply negb_true_iff in X. exact X.
Qed.

Section Q.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation LK := (PSOI.iLK I).   Local Abbreviation cr := (PSOI.icr I).   Local Abbreviation A := (PSOI.iA I).
Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).      Local Abbreviation V := (PSOI.iV I).     Local Abbreviation E := (PSOI.iE I).     Local Abbreviation B := (PSOI.iB I).
Local Abbreviation kx := (PSOI.ikx I).   Local Abbreviation bx := (PSOI.ibx I).    Local Abbreviation g := (PSOI.ig I).     Local Abbreviation ps := (PSOI.ips I).
Local Abbreviation R := (PSOI.iR I).     Local Abbreviation M := (PSOI.iM I).      Local Abbreviation model := (PSOI.imodel I). Local Abbreviation K := (PSOI.iK I).
Local Abbreviation E0 := (PSOI.E0 I).

Lemma P2J : forall p2 jj dl, p2 = (PSOI.we0 I - jj + dl) mod 2 ^ 64 -> PSOI.wp0 I <= p2 <= PSOI.we0 I -> 0 <= jj <= 16384 -> 0 <= dl <= 1 -> p2 = PSOI.we0 I - jj + dl.
Proof.
  intros p2 jj dl CU R2 HJ HD. pose_facts I.
  destruct (Z_le_gt_dec 0 (PSOI.we0 I - jj + dl)) as [G|G].
  - rewrite Z.mod_small in CU; [exact CU | clear - G R2 WI0 WI1 WI2 WI6 HJ HD; unfold PSOI.wlen in *; lia].
  - exfalso. rewrite <- (Z.mod_add _ 1 (2 ^ 64)) in CU by lia. rewrite Z.mod_small in CU by (clear - G HJ HD WI0 WI1 WI2 WI6; unfold PSOI.wlen in *; lia).
    clear - CU G R2 WI0 WI1 WI2 WI6 HJ HD. unfold PSOI.wlen in *. lia.
Qed.

Lemma U8LEAF : forall i E1 A1 M1 m1 c ps0 E' R' M' m' a eb, AAMB I i E1 A1 M1 m1 -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  know_ok (hl_segs L) E' (CCA.vis A1 m' M') (SR.ps_cells ps0) -> CAX.cell_at (SR.ps_cells ps0) a 0 1 = Some eb -> L5.u8_at (hl_segs L) M' (CL5A.uv E' a) (CL5A.uv E' eb).
Proof.
  intros i E1 A1 M1 m1 c ps0 E' R' M' m' a eb HA HLF KL HC.
  pose proof (CBA.amb_off L ar C HI (PSOI.iHIok I) (LYB I) GT.NF E0 M model A LBo FF LK sp G.HDECL (WW I) G.BLS PSO.FFS (PSOX.Cred I) 6 i E1 A1 M1 m1 HA) as Hoff.
  rewrite <- (L5LZ.sbm_ahid A1 m1 m' (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)) in Hoff.
  pose proof (proj1 (Forall_forall _ _) KL _ (cell_at_has _ _ _ _ _ HC)) as K8.
  pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (CL5A.uv E' a + 0) K8 eq_refl) as G0. rewrite Z.add_0_r in G0.
  exact (CL5A.u8_full (hl_segs L) _ Hoff _ _ _ G0).
Qed.

Lemma CURW : forall i c E1 A1 M1 m1 E' l dl, nth_error G.CPS i = Some c -> (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 -> env_agree (CC.cp_nx c) E1 E' ->
  (PSO.v_wptr l = PSO.CURH /\ dl = 0 \/ PSO.v_wptr l = EAlu Instr.ALU_ADD PSO.CURH (ELit 1) /\ dl = 1) ->
  PSOI.wp0 I <= CL5A.uv E' (PSO.v_wptr l) <= PSOI.we0 I -> 0 <= CL5A.uv E1 (EVar JV) <= 16384 ->
  CL5A.uv E' (PSO.v_wptr l) = PSOI.we0 I - CL5A.uv E1 (EVar JV) + dl.
Proof.
  intros i c E1 A1 M1 m1 E' l dl Hci Hi HA Hag HD R2 HJ.
  apply P2J; [exact (CURSOR I i c E1 A1 M1 m1 E' l Hci Hi HA Hag dl HD) | exact R2 | exact HJ | destruct HD as [(_ & ->)|(_ & ->)]; lia].
Qed.
Lemma U200_of : forall E', CL5A.uv E' PE = P -> CL5A.uv E' (EAlu Instr.ALU_ADD PE (ELit 200)) = P + 200.
Proof.
  intros E' UP. pose_facts I. unfold CL5A.uv. cbn [edenot]. rewrite u_add64. fold (CL5A.uv E' PE). rewrite UP, u_lit64. rewrite Zplus_mod_idemp_r.
  apply Z.mod_small. clear - O3 O6. lia.
Qed.
Lemma HCR_of : forall (M2 : mem) code, PMLA.ec_at (hl_segs L) IC M2 E code -> 0 <= code <= 31.
Proof. intros M2 code (_ & _ & [->|(X & _)]); lia. Qed.
Lemma BBS_of : forall ps2, PML.buf_bound ps2 B -> PSOX.WIN I ps2 -> PMSA.buf_bound_stale ps2 B.
Proof.
  intros ps2 (B1 & B2) W. pose proof (WN_of I ps2 W) as W0. pose proof (PSOI.buf_need_nonneg ps2) as NN. unfold PMSA.buf_bound_stale. lia.
Qed.
Lemma NUMF : forall ps2, PML.wf_ps ps2 -> PML.ps_more ps2 = true -> PML.ps_st ps2 = PML.ST_NUMBER -> In (PML.ps_nst ps2) [1; 2; 4; 7] -> PML.num_final (PML.ps_buf ps2).
Proof.
  intros ps2 WF MO ST NI. destruct WF as (_ & _ & _ & _ & Cc & Tt & _ & _ & W7). destruct (W7 MO) as (_ & _ & _ & _ & _ & NP).
  destruct (NP ST) as (kk & Hk & [Hn|(Hn & Hk1)]); exists kk; split; [exact Hk | rewrite <- Hn; exact NI | exact Hk | subst kk; cbn; tauto].
Qed.

Ltac cb_intro := intros i c k ps0 j cj gx t l E1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z IL DC PTL PRE Ht Hl Hret Hz HA Hag HLF KT HNX Hi Hci Hcj Hj Kj HNXj HLS.
Ltac cb_kit pcx HLS :=
  let CF := fresh "CF" in
  pose proof (CBK I pcx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as CF;
  destruct CF as [COK ZR REG A0 UP UV UE KL PA2 BB2 JR J46 WN];
  let HL := fresh "HL" in pose proof HLS as HL; destruct HL as [CO2 WF2 LV2 MO2 ST2 CU2 WI2 NS2].
Ltac ptr_no := split; [let H := fresh "HN" in intros H; cbv in H; discriminate H | let H := fresh "HN" in intros [H|H]; cbv in H; discriminate H].

Lemma L_BMEMBER : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther BMEMBER) -> PSO.call_chk i c k ps0 BMEMBER = true -> PSO.dead_chk i ps0 BMEMBER = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOI.iBMEMBER I) as SP. unfold PMSA.begin_member_specA, PMSA.ptransA, PMSA.ptrans_gA in SP.
  refine (L_GEN I PMCUR.wf_c PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ _ => PMSA.parser_at L IC) BMEMBER PMSA.PF_SCR 3 true _ _ (PMSA.W_parAc IC) (fun _ => SP)
            _ PSOK.XS_BMEMBER eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PF (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_same (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 w a Hw Hin => WR_A I Ex H10 H12 H11 w a Hw Hin) (WW_A I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_intro. cb_kit BMEMBER HLS.
    rewrite CO_BMEMBER in COK. apply andb_prop in COK as [R11 Z7]. apply Z.eqb_eq in Z7.
    split.
    { split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UE; exact (REG 11%nat EE R11)|]; split; [exact MO2 | rewrite ST2, Z7; reflexivity]|].
      split; [exact PA2|]. split; [exact (conj WF2 LV2) | exact BB2]. }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    destruct REL as (HC0 & HM3 & HST3 & HSK3 & HLV3 & HW3).
    apply (SAME_POST I BMEMBER PSOK.XS_BMEMBER i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HW3);
      [|exact BB3].
    intros _ _. ptr_no.
Qed.

Lemma L_BOBJ : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther BOBJ) -> PSO.call_chk i c k ps0 BOBJ = true -> PSO.dead_chk i ps0 BOBJ = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOI.iBOBJ I) as SP. unfold PMSA.begin_object_specA, PMSA.begin_container_specA, PMSA.ptransA, PMSA.ptrans_gA in SP.
  refine (L_GEN I PMCUR.wf_c PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ _ => PMSA.parser_at L IC) BOBJ PMSA.PF_SCR 5 true _ _ (PMSA.W_parAc IC) (fun _ => SP)
            _ PSOK.XS_BOBJ eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PF (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_same (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 w a Hw Hin => WR_A I Ex H10 H12 H11 w a Hw Hin) (WW_A I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_intro. cb_kit BOBJ HLS.
    rewrite (CO_CONT BOBJ) in COK by tauto. apply andb_prop in COK as [COK Z15]. apply andb_prop in COK as [COK ZC]. apply andb_prop in COK as [R11 R12].
    split.
    { split; [split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UV; exact (REG 11%nat VE R11) | unfold PMSA.a2; rewrite <- UE; exact (REG 12%nat EE R12)]|];
              split; [exact MO2|]; rewrite ST2; split; [apply CCRB; apply negb_true_iff; exact ZC | apply negb_true_iff in Z15; apply Z.eqb_neq in Z15; exact Z15]|].
      split; [exact PA2|]. split; [exact (conj WF2 LV2) | exact BB2]. }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    assert (HW3 : PML.ps_win ps3 = PML.ps_win ps2) by (destruct REL as [(_ & _ & _ & _ & _ & X)|(_ & _ & X)]; exact X).
    apply (SAME_POST I BOBJ PSOK.XS_BOBJ i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HW3); [|exact BB3].
    intros HC _. ptr_no.
Qed.
Lemma L_BARR : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther BARR) -> PSO.call_chk i c k ps0 BARR = true -> PSO.dead_chk i ps0 BARR = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOI.iBARR I) as SP. unfold PMSA.begin_array_specA, PMSA.begin_container_specA, PMSA.ptransA, PMSA.ptrans_gA in SP.
  refine (L_GEN I PMCUR.wf_c PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ _ => PMSA.parser_at L IC) BARR PMSA.PF_SCR 5 true _ _ (PMSA.W_parAc IC) (fun _ => SP)
            _ PSOK.XS_BARR eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PF (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_same (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 w a Hw Hin => WR_A I Ex H10 H12 H11 w a Hw Hin) (WW_A I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_intro. cb_kit BARR HLS.
    rewrite (CO_CONT BARR) in COK by tauto. apply andb_prop in COK as [COK Z15]. apply andb_prop in COK as [COK ZC]. apply andb_prop in COK as [R11 R12].
    split.
    { split; [split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UV; exact (REG 11%nat VE R11) | unfold PMSA.a2; rewrite <- UE; exact (REG 12%nat EE R12)]|];
              split; [exact MO2|]; rewrite ST2; split; [apply CCRB; apply negb_true_iff; exact ZC | apply negb_true_iff in Z15; apply Z.eqb_neq in Z15; exact Z15]|].
      split; [exact PA2|]. split; [exact (conj WF2 LV2) | exact BB2]. }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    assert (HW3 : PML.ps_win ps3 = PML.ps_win ps2) by (destruct REL as [(_ & _ & _ & _ & _ & X)|(_ & _ & X)]; exact X).
    apply (SAME_POST I BARR PSOK.XS_BARR i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HW3); [|exact BB3].
    intros HC _. ptr_no.
Qed.

Lemma L_EOBJ : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther EOBJ) -> PSO.call_chk i c k ps0 EOBJ = true -> PSO.dead_chk i ps0 EOBJ = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOI.iEOBJ I) as SP. unfold PMSA.end_object_specA, PMSA.end_container_specA, PMSA.ptransA, PMSA.ptrans_gA in SP.
  refine (L_GEN I PMCUR.wf_c PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ _ => PMSA.parser_at L IC) EOBJ PMSA.PF_SCR 3 true _ _ (PMSA.W_parAc IC) (fun _ => SP)
            _ PSOK.XS_EOBJ eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PF (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_same (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 w a Hw Hin => WR_A I Ex H10 H12 H11 w a Hw Hin) (WW_A I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_intro. cb_kit EOBJ HLS.
    rewrite (CO_CONT EOBJ) in COK by tauto. apply andb_prop in COK as [COK Z15]. apply andb_prop in COK as [COK ZC]. apply andb_prop in COK as [R11 R12].
    split.
    { split; [split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UV; exact (REG 11%nat VE R11) | unfold PMSA.a2; rewrite <- UE; exact (REG 12%nat EE R12)]|];
              split; [exact MO2|]; rewrite ST2; split; [apply CCRB; apply negb_true_iff; exact ZC | apply negb_true_iff in Z15; apply Z.eqb_neq in Z15; exact Z15]|].
      split; [exact PA2|]. split; [exact (conj WF2 LV2) | exact BB2]. }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    assert (HW3 : PML.ps_win ps3 = PML.ps_win ps2) by (destruct REL as [(_ & _ & _ & _ & _ & X)|(_ & X)]; exact X).
    apply (SAME_POST I EOBJ PSOK.XS_EOBJ i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HW3); [|exact BB3].
    intros HC _. ptr_no.
Qed.
Lemma L_EARR : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther EARR) -> PSO.call_chk i c k ps0 EARR = true -> PSO.dead_chk i ps0 EARR = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOI.iEARR I) as SP. unfold PMSA.end_array_specA, PMSA.end_container_specA, PMSA.ptransA, PMSA.ptrans_gA in SP.
  refine (L_GEN I PMCUR.wf_c PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ _ => PMSA.parser_at L IC) EARR PMSA.PF_SCR 3 true _ _ (PMSA.W_parAc IC) (fun _ => SP)
            _ PSOK.XS_EARR eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PF (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_same (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 w a Hw Hin => WR_A I Ex H10 H12 H11 w a Hw Hin) (WW_A I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_intro. cb_kit EARR HLS.
    rewrite (CO_CONT EARR) in COK by tauto. apply andb_prop in COK as [COK Z15]. apply andb_prop in COK as [COK ZC]. apply andb_prop in COK as [R11 R12].
    split.
    { split; [split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UV; exact (REG 11%nat VE R11) | unfold PMSA.a2; rewrite <- UE; exact (REG 12%nat EE R12)]|];
              split; [exact MO2|]; rewrite ST2; split; [apply CCRB; apply negb_true_iff; exact ZC | apply negb_true_iff in Z15; apply Z.eqb_neq in Z15; exact Z15]|].
      split; [exact PA2|]. split; [exact (conj WF2 LV2) | exact BB2]. }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    assert (HW3 : PML.ps_win ps3 = PML.ps_win ps2) by (destruct REL as [(_ & _ & _ & _ & _ & X)|(_ & X)]; exact X).
    apply (SAME_POST I EARR PSOK.XS_EARR i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HW3); [|exact BB3].
    intros HC _. ptr_no.
Qed.

Lemma L_ENDINT : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther ENDINT) -> PSO.call_chk i c k ps0 ENDINT = true -> PSO.dead_chk i ps0 ENDINT = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOI.iENDINT I) as SP. unfold PMSA.end_integer_value_specA, PMSA.end_number_specA, PMSA.ptrans_staleA in SP.
  refine (L_GEN I PMCUR.wf_c_stale PMSA.buf_bound_stale (fun mw M P ps => PMSA.parser_at L IC M P (PML.ps_set_win ps mw))
            (fun mw ps M' P ps' => PMSA.parser_at L IC M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) ENDINT PMSA.ENDNUM_SCR 4 true _ _ (PMSA.W_parAc IC) SP
            _ PSOK.XS_ENDINT eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_EN (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_same (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 w a Hw Hin => WR_A I Ex H10 H12 H11 w a Hw Hin) (WW_A I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_intro. cb_kit ENDINT HLS.
    rewrite (CO_END ENDINT) in COK by tauto. apply andb_prop in COK as [COK YN]. apply andb_prop in COK as [COK _]. apply andb_prop in COK as [COK Z17].
    apply andb_prop in COK as [R11 R12]. apply Z.eqb_eq in Z17.
    destruct (RNGALL _ _ _ _ _ _ KL YN) as (NF & NR).
    assert (NS : CL5A.uv E' (PSO.v_nst l) = PML.ps_nst ps2) by (apply PSOCK.bv8_eq; [exact NS2 | lia | destruct WF2 as (_ & X & _); lia]).
    rewrite NS in NF.
    split.
    { split; [split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UV; exact (REG 11%nat VE R11) | unfold PMSA.a2; rewrite <- UE; exact (REG 12%nat EE R12)]|];
              split; [exact MO2|]; split; [rewrite ST2, Z17; reflexivity|]; apply NUMF; [exact WF2 | exact MO2 | rewrite ST2, Z17; reflexivity | exact (INB _ _ NF)]|].
      split; [exact (PSOX.c_pa _ _ _ _ _ _ _ _ CO2)|]. split; [exact (conj (PML.wf_ps_stale_of _ WF2) LV2) | exact (BBS_of ps2 BB2 (PSOX.c_win _ _ _ _ _ _ _ _ CO2))]. }
    intros R2 M2 A2 m2 ps3 code (PA3 & HW3) REL WF3 CM3 EC3 BB3.
    rewrite <- HW3, PSOX.set_win_self in PA3.
    apply (SAME_POST I ENDINT PSOK.XS_ENDINT i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HW3); [|exact BB3].
    intros HC Hm. destruct REL as [(_ & HM & HS & _)|X]; [rewrite HM in Hm; discriminate Hm | rewrite HC in X; discriminate X].
Qed.
Lemma L_ENDFRAC : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther ENDFRAC) -> PSO.call_chk i c k ps0 ENDFRAC = true -> PSO.dead_chk i ps0 ENDFRAC = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOI.iENDFRAC I) as SP. unfold PMSA.end_fraction_value_specA, PMSA.ptrans_staleeA in SP.
  refine (L_GEN I PMCUR.wf_c_stale PMSA.buf_bound_stale (fun mw M P ps => PMSA.parser_at L IC M P (PML.ps_set_win ps mw))
            (fun mw ps M' P ps' => PMSA.parser_at L IC M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) ENDFRAC PMSA.ENDNUM_SCR 4 true _ _ (PMSA.W_parEc L IC) SP
            _ PSOK.XS_ENDFRAC eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_EN (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_same (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 w a Hw Hin => WR_E I Ex H10 H12 H11 w a Hw Hin) (WW_E I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_intro. cb_kit ENDFRAC HLS.
    rewrite (CO_END ENDFRAC) in COK by tauto. apply andb_prop in COK as [COK YN]. apply andb_prop in COK as [COK _]. apply andb_prop in COK as [COK Z17].
    apply andb_prop in COK as [R11 R12]. apply Z.eqb_eq in Z17.
    destruct (RNGALL _ _ _ _ _ _ KL YN) as (NF & NR).
    assert (NS : CL5A.uv E' (PSO.v_nst l) = PML.ps_nst ps2) by (apply PSOCK.bv8_eq; [exact NS2 | lia | destruct WF2 as (_ & X & _); lia]).
    rewrite NS in NF.
    split.
    { split; [split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UV; exact (REG 11%nat VE R11) | unfold PMSA.a2; rewrite <- UE; exact (REG 12%nat EE R12)]|];
              split; [exact MO2|]; split; [rewrite ST2, Z17; reflexivity|]; apply NUMF; [exact WF2 | exact MO2 | rewrite ST2, Z17; reflexivity | exact (INB _ _ NF)]|].
      split; [exact (PSOX.c_pa _ _ _ _ _ _ _ _ CO2)|]. split; [exact (conj (PML.wf_ps_stale_of _ WF2) LV2) | exact (BBS_of ps2 BB2 (PSOX.c_win _ _ _ _ _ _ _ _ CO2))]. }
    intros R2 M2 A2 m2 ps3 code (PA3 & HW3) REL WF3 CM3 EC3 BB3.
    rewrite <- HW3, PSOX.set_win_self in PA3.
    apply (SAME_POST I ENDFRAC PSOK.XS_ENDFRAC i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HW3); [|exact BB3].
    intros HC Hm. destruct REL as [(_ & HM & HS & _)|X]; [rewrite HM in Hm; discriminate Hm | rewrite HC in X; discriminate X].
Qed.

Lemma L_PNULL : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther PNULL) -> PSO.call_chk i c k ps0 PNULL = true -> PSO.dead_chk i ps0 PNULL = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOI.iPNULL I) as SP. unfold PMSA.parse_null_specA, PMSA.ptransA, PMSA.ptrans_gA in SP.
  refine (L_GEN I PMCUR.wf_c PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ _ => PMSA.parser_at L IC) PNULL PMSA.PF_SCR 2 true _ _ (PMSA.W_parAc IC) (fun _ => SP)
            _ PSOK.XS_PNULL eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PF (fun _ _ _ => eq_refl)
            (fun _ => XA0_condBm) PSOK.WFACTS_condB (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 w a Hw Hin => WR_A I Ex H10 H12 H11 w a Hw Hin) (WW_A I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_intro. cb_kit PNULL HLS.
    rewrite CO_PNULL in COK. apply andb_prop in COK as [COK YJ]. apply andb_prop in COK as [COK YT]. apply andb_prop in COK as [COK YS]. apply andb_prop in COK as [COK YE].
    apply andb_prop in COK as [R11 R12]. apply expr_eqb_eq in YT. pose proof (WP_same _ _ _ YS) as WPS. rewrite YT in WPS.
    pose proof (LOGE _ _ _ _ _ _ KL YJ) as J1. rewrite J46 in J1.
    pose proof (U0PT i c k ps0 PNULL IL ltac:(unfold PT; cbn [In]; tauto) DC ltac:(intros X; cbv in X; discriminate X) ltac:(intros X; cbv in X; discriminate X)) as HU.
    destruct (WN HU) as (HW2 & R2p).
    pose proof (CURW i c E1 A1 M1 m1 E' l 0 Hci Hi HA Hag (or_introl (conj WPS eq_refl)) R2p JR) as P2.
    split.
    { split; [split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UV; exact (REG 11%nat VE R11) | unfold PMSA.a2; rewrite <- UE; exact (REG 12%nat EE R12)]|];
              split; [exact MO2|]; split; [unfold PMSA.win_exhausted; rewrite HW2; intros X; rewrite P2 in X; lia | rewrite ST2; apply EXPB; exact YE]|].
      split; [exact PA2|]. split; [exact (conj WF2 LV2) | exact BB2]. }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    apply (NULL_POST I PNULL PSOK.XS_PNULL i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl WPS JR J1 PA3).
    + destruct REL as [(X & Y & _)|(X & Y)]; [left | right]; split; assumption.
    + intros HC _. ptr_no.
    + exact BB3.
Qed.

Lemma L_PTRUE : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther PTRUE) -> PSO.call_chk i c k ps0 PTRUE = true -> PSO.dead_chk i ps0 PTRUE = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOI.iPTRUE I) as SP. unfold PMSA.parse_true_specA, PMSA.ptrans_curA, PMSA.ptrans_gA in SP.
  refine (L_GEN I PMCUR.wf_c PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ ps M' P ps' => PMSA.parser_at L IC M' P (PML.ps_set_win ps' (PML.ps_win ps))) PTRUE PMSA.PF_SCR 2 true
            _ _ (PMSA.W_parAc IC) (fun _ => SP)
            _ PSOK.XS_PTRUE eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PF (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_condBm (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 w a Hw Hin => WR_A I Ex H10 H12 H11 w a Hw Hin) (WW_A I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_intro. cb_kit PTRUE HLS.
    rewrite (CO_LIT PTRUE) in COK by tauto. apply andb_prop in COK as [COK YJ]. apply andb_prop in COK as [COK YT]. apply andb_prop in COK as [COK YS].
    apply andb_prop in COK as [COK YE]. apply andb_prop in COK as [COK R13]. apply andb_prop in COK as [R11 R12].
    apply expr_eqb_eq in YT. pose proof (WP_same _ _ _ YS) as WPS. rewrite YT in WPS.
    pose proof (LOGE _ _ _ _ _ _ KL YJ) as J1. rewrite J46 in J1.
    pose proof (U0PT i c k ps0 PTRUE IL ltac:(unfold PT; cbn [In]; tauto) DC ltac:(intros X; cbv in X; discriminate X) ltac:(intros X; cbv in X; discriminate X)) as HU.
    destruct (WN HU) as (HW2 & R2p).
    pose proof (CURW i c E1 A1 M1 m1 E' l 0 Hci Hi HA Hag (or_introl (conj WPS eq_refl)) R2p JR) as P2.
    split.
    { split; [split; [split; [exact A0|]; split; [unfold PMSA.a2; rewrite <- UV; exact (REG 12%nat VE R12)|]; split; [unfold PMSA.a3; rewrite <- UE; exact (REG 13%nat EE R13)|];
                      exists (CL5A.uv E' (PSO.v_wptr l)), (PSOI.we0 I); split; [exact HW2 | unfold PMSA.a1; exact (REG 11%nat _ R11)]|];
              split; [exact MO2|]; split; [unfold PMSA.win_exhausted; rewrite HW2; intros X; rewrite P2 in X; lia | rewrite ST2; apply EXPB; exact YE]|].
      split; [exact PA2|]. split; [exact (conj WF2 LV2) | exact BB2]. }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    destruct REL as (LR & HNR & HA03).
    apply (CUR_POST I PTRUE PSOK.XS_PTRUE i c ps0 j cj gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code 0 Hci PRE Ht Hl Hi HA Hag HNX Hcj Hj Kj HNXj HLS
             eq_refl eq_refl (fun _ _ => eq_refl) (or_introl (conj WPS eq_refl)) JR PA3 HNR HA03).
    + destruct LR as [(_ & X & _)|(X & _)]; [right; left; exact X | left; rewrite X; lia].
    + intros HC _. ptr_no.
    + exact BB3.
    + exact (HCR_of M2 code EC3).
Qed.
Lemma L_PFALSE : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther PFALSE) -> PSO.call_chk i c k ps0 PFALSE = true -> PSO.dead_chk i ps0 PFALSE = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOI.iPFALSE I) as SP. unfold PMSA.parse_false_specA, PMSA.ptrans_curA, PMSA.ptrans_gA in SP.
  refine (L_GEN I PMCUR.wf_c PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ ps M' P ps' => PMSA.parser_at L IC M' P (PML.ps_set_win ps' (PML.ps_win ps))) PFALSE PMSA.PF_SCR 2 true
            _ _ (PMSA.W_parAc IC) (fun _ => SP)
            _ PSOK.XS_PFALSE eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PF (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_condBm (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 w a Hw Hin => WR_A I Ex H10 H12 H11 w a Hw Hin) (WW_A I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_intro. cb_kit PFALSE HLS.
    rewrite (CO_LIT PFALSE) in COK by tauto. apply andb_prop in COK as [COK YJ]. apply andb_prop in COK as [COK YT]. apply andb_prop in COK as [COK YS].
    apply andb_prop in COK as [COK YE]. apply andb_prop in COK as [COK R13]. apply andb_prop in COK as [R11 R12].
    apply expr_eqb_eq in YT. pose proof (WP_same _ _ _ YS) as WPS. rewrite YT in WPS.
    pose proof (LOGE _ _ _ _ _ _ KL YJ) as J1. rewrite J46 in J1.
    pose proof (U0PT i c k ps0 PFALSE IL ltac:(unfold PT; cbn [In]; tauto) DC ltac:(intros X; cbv in X; discriminate X) ltac:(intros X; cbv in X; discriminate X)) as HU.
    destruct (WN HU) as (HW2 & R2p).
    pose proof (CURW i c E1 A1 M1 m1 E' l 0 Hci Hi HA Hag (or_introl (conj WPS eq_refl)) R2p JR) as P2.
    split.
    { split; [split; [split; [exact A0|]; split; [unfold PMSA.a2; rewrite <- UV; exact (REG 12%nat VE R12)|]; split; [unfold PMSA.a3; rewrite <- UE; exact (REG 13%nat EE R13)|];
                      exists (CL5A.uv E' (PSO.v_wptr l)), (PSOI.we0 I); split; [exact HW2 | unfold PMSA.a1; exact (REG 11%nat _ R11)]|];
              split; [exact MO2|]; split; [unfold PMSA.win_exhausted; rewrite HW2; intros X; rewrite P2 in X; lia | rewrite ST2; apply EXPB; exact YE]|].
      split; [exact PA2|]. split; [exact (conj WF2 LV2) | exact BB2]. }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    destruct REL as (LR & HNR & HA03).
    apply (CUR_POST I PFALSE PSOK.XS_PFALSE i c ps0 j cj gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code 0 Hci PRE Ht Hl Hi HA Hag HNX Hcj Hj Kj HNXj HLS
             eq_refl eq_refl (fun _ _ => eq_refl) (or_introl (conj WPS eq_refl)) JR PA3 HNR HA03).
    + destruct LR as [(_ & X & _)|(X & _)]; [right; left; exact X | left; rewrite X; lia].
    + intros HC _. ptr_no.
    + exact BB3.
    + exact (HCR_of M2 code EC3).
Qed.

Lemma L_PSTRING : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther PSTRING) -> PSO.call_chk i c k ps0 PSTRING = true -> PSO.dead_chk i ps0 PSTRING = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOI.iPSTRING I) as SP. unfold PMSA.parse_string_specA, PMSA.ptrans_curA, PMSA.ptrans_gA in SP.
  refine (L_GEN I PMCUR.wf_c PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ ps M' P ps' => PMSA.parser_at L IC M' P (PML.ps_set_win ps' (PML.ps_win ps))) PSTRING PMSA.PF_SCR 4 true
            _ _ (PMSA.W_parAc IC) (fun _ => SP)
            _ PSOK.XS_PSTRING eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PF (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_condBm (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 w a Hw Hin => WR_A I Ex H10 H12 H11 w a Hw Hin) (WW_A I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_intro. cb_kit PSTRING HLS.
    rewrite CO_PSTRING in COK. apply andb_prop in COK as [COK YD]. apply andb_prop in COK as [COK YJ]. apply andb_prop in COK as [COK Z15].
    apply andb_prop in COK as [COK R13]. apply andb_prop in COK as [R11 R12]. apply Z.eqb_eq in Z15.
    assert (HDL : exists dl, PSO.v_wptr l = PSO.CURH /\ dl = 0 \/ PSO.v_wptr l = EAlu Instr.ALU_ADD PSO.CURH (ELit 1) /\ dl = 1).
    { apply orb_prop in YD as [D|D]; apply expr_eqb_eq in D; [exists 0; left | exists 1; right]; split; [exact D | reflexivity | exact D | reflexivity]. }
    destruct HDL as (dl & HDL). assert (DL01 : 0 <= dl <= 1) by (destruct HDL as [(_ & ->)|(_ & ->)]; lia).
    pose proof (LOGE _ _ _ _ _ _ KL YJ) as J1. rewrite J46 in J1.
    pose proof (U0PT i c k ps0 PSTRING IL ltac:(unfold PT; cbn [In]; tauto) DC ltac:(intros X; cbv in X; discriminate X) ltac:(intros X; cbv in X; discriminate X)) as HU.
    destruct (WN HU) as (HW2 & R2p).
    pose proof (CURW i c E1 A1 M1 m1 E' l dl Hci Hi HA Hag HDL R2p JR) as P2.
    split.
    { split; [split; [split; [exact A0|]; split; [unfold PMSA.a2; rewrite <- UV; exact (REG 12%nat VE R12)|]; split; [unfold PMSA.a3; rewrite <- UE; exact (REG 13%nat EE R13)|];
                      exists (CL5A.uv E' (PSO.v_wptr l)), (PSOI.we0 I); split; [exact HW2 | unfold PMSA.a1; exact (REG 11%nat _ R11)]|];
              split; [exact MO2 | rewrite ST2, Z15; reflexivity]|].
      split; [exact PA2|]. split; [exact (conj WF2 LV2) | exact BB2]. }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    destruct REL as (HNR & HA03 & HPR & HCM).
    pose proof (HCR_of M2 code EC3) as HCR.
    apply (CUR_POST I PSTRING PSOK.XS_PSTRING i c ps0 j cj gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code dl Hci PRE Ht Hl Hi HA Hag HNX Hcj Hj Kj HNXj HLS
             eq_refl eq_refl (fun _ _ => eq_refl) HDL JR PA3 HNR HA03).
    + destruct HPR as [X|[X|X]]; [left; lia | right; left; exact X | right; right].
      unfold PMSA.win_exhausted in X. rewrite HW2 in X. rewrite P2 in X. lia.
    + intros HC _. ptr_no.
    + exact BB3.
    + exact HCR.
Qed.

Lemma L_PNUMBER : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther PNUMBER) -> PSO.call_chk i c k ps0 PNUMBER = true -> PSO.dead_chk i ps0 PNUMBER = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOI.iPNUMBER I) as SP. unfold PMSA.parse_number_specA, PMSA.ptrans_cureA, PMSA.ptrans_geA in SP.
  refine (L_GEN I PMCUR.wf_c PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ ps M' P ps' => PMSA.parser_at L IC M' P (PML.ps_set_win ps' (PML.ps_win ps))) PNUMBER PMSA.PF_SCR 5 true
            _ _ (PMSA.W_parEc L IC) (fun _ => SP)
            _ PSOK.XS_PNUMBER eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PF (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_a1m (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 w a Hw Hin => WR_E I Ex H10 H12 H11 w a Hw Hin) (WW_E I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_intro. cb_kit PNUMBER HLS.
    rewrite CO_PNUMBER in COK. apply andb_prop in COK as [COK YR]. apply andb_prop in COK as [COK Z17]. apply andb_prop in COK as [COK R13].
    apply andb_prop in COK as [R11 R12]. apply Z.eqb_eq in Z17. apply expr_eqb_eq in YR.
    pose proof (U0PT i c k ps0 PNUMBER IL ltac:(unfold PT; cbn [In]; tauto) DC ltac:(intros X; cbv in X; discriminate X) ltac:(intros X; cbv in X; discriminate X)) as HU.
    destruct (WN HU) as (HW2 & R2p).
    split.
    { split; [split; [split; [exact A0|]; split; [unfold PMSA.a2; rewrite <- UV; exact (REG 12%nat VE R12)|]; split; [unfold PMSA.a3; rewrite <- UE; exact (REG 13%nat EE R13)|];
                      exists (CL5A.uv E' (PSO.v_wptr l)), (PSOI.we0 I); split; [exact HW2 | unfold PMSA.a1; exact (REG 11%nat _ R11)]|];
              split; [exact MO2 | rewrite ST2, Z17; reflexivity]|].
      split; [exact PA2|]. split; [exact (conj WF2 LV2) | exact BB2]. }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    destruct REL as (HNR & HA03 & HCM).
    apply (NUM_POST I PNUMBER PSOK.XS_PNUMBER i c ps0 j cj gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX Hcj Hj Kj HNXj HLS
             eq_refl eq_refl (fun _ _ => eq_refl) YR PA3 HNR HA03).
    + intros HC _. destruct (HCM HC) as (_ & HSN & HIN). split; [intros _; split; [exact HIN | exact HSN] | intros [X|X]; cbv in X; discriminate X].
    + exact BB3.
    + exact (HCR_of M2 code EC3).
Qed.

Lemma L_SKIPSP : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther SKIPSP) -> PSO.call_chk i c k ps0 SKIPSP = true -> PSO.dead_chk i ps0 SKIPSP = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOI.iSKIPSP I) as SP. unfold PMSA.skip_space_specA, PMSA.ptransA, PMSA.ptrans_gA in SP.
  refine (L_GEN I PMCUR.wf_c PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ _ => PMSA.parser_at L IC) SKIPSP PMSA.PF_SCR 4 false _ _ (PMSA.W_parAc IC) (fun _ => SP)
            _ PSOK.XS_SKIPSP eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PF (fun _ _ _ => eq_refl)
            (fun _ => XA0_a1m) PSOK.WFACTS_cell1 (fun g0 => [KRange (EVar g0) 0 0]) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 w a Hw Hin => WR_A I Ex H10 H12 H11 w a Hw Hin) (WW_A I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_intro. cb_kit SKIPSP HLS.
    rewrite CO_SKIPSP in COK. apply andb_prop in COK as [COK YB]. apply andb_prop in COK as [COK YJ]. apply andb_prop in COK as [COK YT]. apply andb_prop in COK as [COK YS].
    apply andb_prop in COK as [R11 YE]. apply expr_eqb_eq in YT. pose proof (WP_same _ _ _ YS) as WPS. rewrite YT in WPS.
    destruct (CAX.cell_at (SR.ps_cells ps0) (PSO.v_wptr l) 0 1) as [eb|] eqn:HCB; [|discriminate YB].
    destruct (RNGALL _ _ _ _ _ _ KL YB) as (WSB & _).
    pose proof (LOGE _ _ _ _ _ _ KL YJ) as J1. rewrite J46 in J1.
    pose proof (U0PT i c k ps0 SKIPSP IL ltac:(unfold PT; cbn [In]; tauto) DC ltac:(intros X; cbv in X; discriminate X) ltac:(intros X; cbv in X; discriminate X)) as HU.
    destruct (WN HU) as (HW2 & R2p).
    pose proof (CURW i c E1 A1 M1 m1 E' l 0 Hci Hi HA Hag (or_introl (conj WPS eq_refl)) R2p JR) as P2.
    pose proof (U200_of E' UP) as U200.
    split.
    { split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- U200; exact (REG 11%nat _ R11)|]; split; [unfold PML.ws_ok; rewrite MO2; intros X; discriminate X|];
              split; [exact MO2|]; split; [rewrite ST2; apply EXPB; exact YE|];
              exists (CL5A.uv E' (PSO.v_wptr l)), (PSOI.we0 I), (CL5A.uv E' eb); split; [exact HW2|]; split; [rewrite P2; lia|];
              split; [exact (U8LEAF i E1 A1 M1 m1 c ps0 E' R' M' m' (PSO.v_wptr l) eb HA HLF KL HCB) | exact (INB _ _ WSB)]|].
      split; [exact PA2|]. split; [exact (conj WF2 LV2) | exact BB2]. }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    destruct REL as (HC0 & HCO & HM3 & _).
    apply (SKIP_POST I SKIPSP PSOK.XS_SKIPSP i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HC0 HCO);
      [|exact BB3].
    intros _ _. ptr_no.
Qed.

Lemma L_PT : forall pc, In pc PT -> forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> PSO.call_chk i c k ps0 pc = true -> PSO.dead_chk i ps0 pc = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  intros pc Hpc. unfold PT in Hpc. cbn [In] in Hpc.
  repeat (destruct Hpc as [<-|Hpc]; [first [exact L_SKIPSP | exact L_PNULL | exact L_BOBJ | exact L_BARR | exact L_EOBJ | exact L_EARR | exact L_BMEMBER
                                          | exact L_PTRUE | exact L_PFALSE | exact L_PSTRING | exact L_PNUMBER | exact L_ENDINT | exact L_ENDFRAC]|]).
  destruct Hpc.
Qed.
End Q.
End PSOPI.
