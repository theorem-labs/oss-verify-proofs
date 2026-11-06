(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtC CutRtD CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecs PmEncSpecs PmLibSpecsXA PmLibSpecsX PmLibSpecsW PmRef PmRefFacts PmRefXA PmLibSpecsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA PtKitB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_psome_xboth_T Cut_psome_xboth_D Cut_psome_xboth.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PsKitA XKitXA PsoInstXB PsoSemXB PsoKnXB ParseSomeChkXB PsoAuxXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import PsoInstXBW PsoBaseXBW PsoXiXBW PsoLinkXBW PsoFrmXBW PsoExitXBW PsoStXBW PsoCkXBW PsoKnOkXBW PsoPtXBW.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation RSEGS := Pm5PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_xboth.

Module PSOPI.
Import PSOP.
(* [comment removed for export] *)
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
Lemma SCR_PF : PMSA.PF_SCR mod 8 = 0 /\ 0 <= PMSA.PF_SCR /\ 672 + PMSA.PF_SCR <= 17600.
Proof. split; [reflexivity|]. split; apply Z.leb_le; reflexivity. Qed.
Lemma SCR_EN : PMSA.ENDNUM_SCR mod 8 = 0 /\ 0 <= PMSA.ENDNUM_SCR /\ 672 + PMSA.ENDNUM_SCR <= 17600.
Proof. split; [reflexivity|]. split; apply Z.leb_le; reflexivity. Qed.

Lemma SCR_PFX : (PMXA.PFXA_SCR XKA.VIS) mod 8 = 0 /\ 0 <= (PMXA.PFXA_SCR XKA.VIS) /\ 672 + (PMXA.PFXA_SCR XKA.VIS) <= 17600.      (* [comment removed for export] *)
Proof. split; [reflexivity|]. split; apply Z.leb_le; reflexivity. Qed.
Lemma SCR_ENX : (PMXA.ENDNUMXA_SCR XKA.VIS) mod 8 = 0 /\ 0 <= (PMXA.ENDNUMXA_SCR XKA.VIS) /\ 672 + (PMXA.ENDNUMXA_SCR XKA.VIS) <= 17600.      (* [comment removed for export] *)
Proof. split; [reflexivity|]. split; apply Z.leb_le; reflexivity. Qed.
Definition PTA : list Z := [SKIPSP; BMEMBER].      (* [comment removed for export] *)
Definition PTX : list Z := [PNULL; BOBJ; BARR; EOBJ; EARR; PTRUE; PFALSE; PSTRING; PNUMBER; ENDINT; ENDFRAC].      (* [comment removed for export] *)

(* [comment removed for export] *)
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
(* [comment removed for export] *)
Definition u0_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TOther pc => if (PSO.inb pc PT && negb (PSO.dead_chk i ps pc) && negb (PSO.inb pc [ENDINT; ENDFRAC]))%bool then negb (PSO.u0 i) else true | _ => true end.
Lemma U0_all : CH2.leaves_all G.CPS G.TAGS u0_chk = true. Proof. vm_compute. reflexivity. Qed.
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
Variable I : PSOIW.inst.
Hypothesis IETA : PSOIW.setg I (PSOIW.ig1 I) = I.      (* [comment removed for export] *)
Local Abbreviation L := (PSOIW.iL I).     Local Abbreviation ar := (PSOIW.iar I).    Local Abbreviation C := (PSOIW.iC I).     Local Abbreviation HI := (PSOIW.iHI I).
Local Abbreviation LBo := (PSOIW.iLBo I). Local Abbreviation FF := (PSOIW.iFF I).    Local Abbreviation LK := (PSOIW.iLK I).   Local Abbreviation cr := (PSOIW.icr I).   Local Abbreviation A := (PSOIW.iA I).
Local Abbreviation sp := (PSOIW.isp I).   Local Abbreviation P := (PSOIW.iP I).      Local Abbreviation V := (PSOIW.iV I).     Local Abbreviation E := (PSOIW.iE I).     Local Abbreviation B := (PSOIW.iB I).
Local Abbreviation kx := (PSOIW.ikx I).   Local Abbreviation bx := (PSOIW.ibx I).    Local Abbreviation g := (PSOIW.ig I).     Local Abbreviation ps := (PSOIW.ips I).
Local Abbreviation R := (PSOIW.iR I).     Local Abbreviation M := (PSOIW.iM I).      Local Abbreviation model := (PSOIW.imodel I). Local Abbreviation K := (PSOIW.iK I).
Local Abbreviation E0 := (PSOIW.E0 I).

(* [comment removed for export] *)
Lemma P2J : forall p2 jj dl, p2 = (PSOIW.we0 I - jj + dl) mod 2 ^ 64 -> PSOIW.wp0 I <= p2 <= PSOIW.we0 I -> 0 <= jj <= 16384 -> 0 <= dl <= 1 -> p2 = PSOIW.we0 I - jj + dl.
Proof.
  intros p2 jj dl CU R2 HJ HD. pose_facts I.
  destruct (Z_le_gt_dec 0 (PSOIW.we0 I - jj + dl)) as [G|G].
  - rewrite Z.mod_small in CU; [exact CU | clear - G R2 WI0 WI1 WI2 WI6 HJ HD; unfold PSOIW.wlen in *; lia].
  - exfalso. rewrite <- (Z.mod_add _ 1 (2 ^ 64)) in CU by lia. rewrite Z.mod_small in CU by (clear - G HJ HD WI0 WI1 WI2 WI6; unfold PSOIW.wlen in *; lia).
    clear - CU G R2 WI0 WI1 WI2 WI6 HJ HD. unfold PSOIW.wlen in *. lia.
Qed.
(* [comment removed for export] *)
Lemma U8LEAF : forall i E1 A1 M1 m1 c ps0 E' R' M' m' a eb, AAMB I i E1 A1 M1 m1 -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  know_ok (hl_segs L) E' (CCA.vis A1 m' M') (SR.ps_cells ps0) -> CAX.cell_at (SR.ps_cells ps0) a 0 1 = Some eb -> L5.u8_at (hl_segs L) M' (CL5A.uv E' a) (CL5A.uv E' eb).
Proof.
  intros i E1 A1 M1 m1 c ps0 E' R' M' m' a eb HA HLF KL HC.
  pose proof HA as (M0d_ & OKW_ & HA__). pose proof (CBA.amb_off L ar C HI (PSOIW.iHIok I) (LYB I) GT.NF E0 M0d_ model A (PSOIW.LBV I (PSOIW.ig1 I)) FF LK sp G.HDECL (PSOIW.WW I) G.BLS PSO.FFS (PSOX.Cred I) 11 i E1 A1 M1 m1 HA__) as Hoff.
  rewrite <- (L5LZ.sbm_ahid A1 m1 m' (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)) in Hoff.
  pose proof (proj1 (Forall_forall _ _) KL _ (cell_at_has _ _ _ _ _ HC)) as K8.
  pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (CL5A.uv E' a + 0) K8 eq_refl) as G0. rewrite Z.add_0_r in G0.
  exact (CL5A.u8_full (hl_segs L) _ Hoff _ _ _ G0).
Qed.
(* [comment removed for export] *)
Lemma CURW : forall i c E1 A1 M1 m1 E' l dl, nth_error G.CPS i = Some c -> (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 -> env_agree (CC.cp_nx c) E1 E' ->
  (PSO.v_wptr l = PSO.CURH /\ dl = 0 \/ PSO.v_wptr l = EAlu Instr.ALU_ADD PSO.CURH (ELit 1) /\ dl = 1) ->
  PSOIW.wp0 I <= CL5A.uv E' (PSO.v_wptr l) <= PSOIW.we0 I -> 0 <= CL5A.uv E1 (EVar JV) <= 16384 ->
  CL5A.uv E' (PSO.v_wptr l) = PSOIW.we0 I - CL5A.uv E1 (EVar JV) + dl.
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
  intros ps2 (B1 & B2) W. pose proof (WN_of I ps2 W) as W0. pose proof (PSOIW.buf_need_nonneg ps2) as NN. unfold PMSA.buf_bound_stale. lia.
Qed.
Lemma NUMF : forall ps2, PML.wf_ps ps2 -> PML.ps_more ps2 = true -> PML.ps_st ps2 = PML.ST_NUMBER -> In (PML.ps_nst ps2) [1; 2; 4; 7] -> PML.num_final (PML.ps_buf ps2).
Proof.
  intros ps2 WF MO ST NI. destruct WF as (_ & _ & _ & _ & Cc & Tt & _ & _ & W7). destruct (W7 MO) as (_ & _ & _ & _ & _ & NP).
  destruct (NP ST) as (kk & Hk & [Hn|(Hn & Hk1)]); exists kk; split; [exact Hk | rewrite <- Hn; exact NI | exact Hk | subst kk; cbn; tauto].
Qed.

Ltac cb_intro := intros i c k ps0 j cj gx t l E1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z IL DC PTL PRE Ht Hl Hret Hz HA Hag HLF KT HNX Hi Hci Hcj Hj Kj HNXj HLS.
Ltac cb_introx := intros i c k ps0 j cj gx t l E1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z IL DC PTL PRE Ht Hl Hret Hz HA Hag HLF KT HNX Hi Hci Hcj Hj Kj HNXj HLS XM.      (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac cb_introw := intros i c k ps0 j cj gx t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z IL DC PTL PRE Ht Hl Hret Hz HAt HA Hag HLF KT HNX Hi Hci Hcj Hj Kj HNXj HLS AK HFL HCO1 HWCO1 HPW1 HLSW.
Ltac cb_introxw := intros i c k ps0 j cj gx t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z IL DC PTL PRE Ht Hl Hret Hz HAt HA Hag HLF KT HNX Hi Hci Hcj Hj Kj HNXj HLS XM AK HFL HCO1 HWCO1 HPW1 HLSW.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac cb_kit pcx HLS :=
  let CF := fresh "CF" in
  pose proof (CBK I pcx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as CF;
  destruct CF as [COK ZR REG A0 UP UV UE KL PA2 BB2 JR J46 WN];
  let HL := fresh "HL" in pose proof HLS as HL; destruct HL as [CO2 WF2 MO2 ST2 CU2 WI2 NS2].
Ltac ptr_no := split; [let H := fresh "HN" in intros H; cbv in H; discriminate H | let H := fresh "HN" in intros [H|H]; cbv in H; discriminate H].

(* [comment removed for export] *)
Lemma L_BMEMBER : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther BMEMBER) -> PSO.call_chk i c k ps0 BMEMBER = true -> PSO.dead_chk i ps0 BMEMBER = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOIW.iBMEMBER I) as SP. unfold PMXAW.begin_member_specAW, PMXAW.ptransAW, PMXAW.ptrans_gAW in SP.
  refine (L_GEN I IETA PMW.FBeginMember (PMW.rm_match (PMRXA.the_rmA L)) PMW.inp_win PML.wf_ps PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ _ => PMSA.parser_at L IC) BMEMBER PMSA.PF_SCR 3 true _ _ (PMLA.W_parA IC) (fun _ => SP) (fun _ _ _ H => H)
            _ PSOK.XS_BMEMBER eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PF (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_same (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 w a Hw Hin => WR_A I Ex H10 H12 w a Hw Hin) (WW_A I) (WX_A I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_introw. cb_kit BMEMBER HLS.
    rewrite CO_BMEMBER in COK. apply andb_prop in COK as [R11 Z7]. apply Z.eqb_eq in Z7.
    split.
    { split; [intros wx; split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UE; exact (REG 11%nat EE R11)|]; split; [exact MO2 | rewrite ST2, Z7; reflexivity]|].
      split; [exact PA2|]. split; [exact WF2|]. split; [exact BB2|].
      exact (CALLW I IETA BMEMBER i c k ps0 t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z j cj IL ltac:(unfold PT; cbn [In]; tauto) DC Ht Hl Hret Hz Hi Hci HAt HA Hag HLF AK HFL HCO1 HWCO1 HPW1 HLS HLSW). }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    destruct REL as (HC0 & HM3 & HST3 & HSK3 & HLV3 & HW3). split.
    { apply (SAME_POST I BMEMBER PSOK.XS_BMEMBER i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HW3);
        [|exact BB3].
      intros _. split; [exact HM3 | ptr_no]. }
    (* [comment removed for export] *)
    intros _. destruct (PSOX.c_sync _ _ _ _ _ _ _ _ CO2 eq_refl) as [XD XK]. split; [rewrite HLV3; exact XD|]. apply PMXA.key_inv_pos. rewrite HLV3.
    destruct WF2 as (_ & _ & _ & _ & Cc & Tt & _ & _ & W7). destruct (W7 MO2) as (_ & _ & _ & _ & W8 & _). apply W8. left. rewrite ST2, Z7. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma L_BOBJ : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther BOBJ) -> PSO.call_chk i c k ps0 BOBJ = true -> PSO.dead_chk i ps0 BOBJ = false ->
  forall M0c, OKVt I M0c -> LEAFV I (PSOIW.ig1 I) M0c i c ps0.      (* [comment removed for export] *)
Proof.
  pose proof (PSOIW.iBOBJ I) as SP. unfold PMXAW.begin_object_specXAW, PMXAW.begin_container_specXAW, PMXAW.ptransxAW, PMXAW.ptrans_gxAW in SP.
  refine (L_GENX I IETA PMW.FBeginObject (PMW.rm_match (PMRXA.the_rmA L)) PMW.inp_win PML.wf_ps PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ _ => PMSA.parser_at L IC) BOBJ (PMXA.PFXA_SCR XKA.VIS) (PMXA.DBEGXA XKA.VISD) true _ _ (fun P V E S2 => PMLA.W_parA IC P E ++ PMXA.W_encA IC V S2) (fun _ => SP) (fun _ _ _ H => H)
            _ PSOK.XS_BOBJ eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PFX (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_same (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 H37 w a Hw Hin => WR_AX I Ex H10 H12 H11 H37 w a Hw Hin) (WW_AX I) _).
  - unfold PT. cbn [In]. tauto.
  - split; apply Z.leb_le; reflexivity.
  - cb_introxw. cb_kit BOBJ HLS.
    rewrite (CO_CONT BOBJ) in COK by tauto. apply andb_prop in COK as [COK Z15]. apply andb_prop in COK as [COK ZC]. apply andb_prop in COK as [R11 R12].
    split.
    { split; [intros wx; split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UV; exact (REG 11%nat VE R11) | unfold PMSA.a2; rewrite <- UE; exact (REG 12%nat EE R12)]|];
              split; [exact MO2|]; rewrite ST2; split; [apply CCRB; apply negb_true_iff; exact ZC | apply negb_true_iff in Z15; apply Z.eqb_neq in Z15; exact Z15]|].
      split; [exact PA2|]. split; [exact WF2|]. split; [exact BB2|].
      exact (CALLW I IETA BOBJ i c k ps0 t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z j cj IL ltac:(unfold PT; cbn [In]; tauto) DC Ht Hl Hret Hz Hi Hci HAt HA Hag HLF AK HFL HCO1 HWCO1 HPW1 HLS HLSW). }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    assert (HW3 : PML.ps_win ps3 = PML.ps_win ps2) by (destruct REL as [(_ & _ & _ & _ & _ & X)|(_ & _ & X)]; exact X).
    apply (SAME_POST I BOBJ PSOK.XS_BOBJ i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HW3); [|exact BB3].
    intros HC. split; [destruct REL as [(_ & _ & _ & X & _)|(X & _)]; [exact X | rewrite HC in X; discriminate X] | ptr_no].
Qed.
Lemma L_BARR : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther BARR) -> PSO.call_chk i c k ps0 BARR = true -> PSO.dead_chk i ps0 BARR = false ->
  forall M0c, OKVt I M0c -> LEAFV I (PSOIW.ig1 I) M0c i c ps0.      (* [comment removed for export] *)
Proof.
  pose proof (PSOIW.iBARR I) as SP. unfold PMXAW.begin_array_specXAW, PMXAW.begin_container_specXAW, PMXAW.ptransxAW, PMXAW.ptrans_gxAW in SP.
  refine (L_GENX I IETA PMW.FBeginArray (PMW.rm_match (PMRXA.the_rmA L)) PMW.inp_win PML.wf_ps PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ _ => PMSA.parser_at L IC) BARR (PMXA.PFXA_SCR XKA.VIS) (PMXA.DBEGXA XKA.VISD) true _ _ (fun P V E S2 => PMLA.W_parA IC P E ++ PMXA.W_encA IC V S2) (fun _ => SP) (fun _ _ _ H => H)
            _ PSOK.XS_BARR eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PFX (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_same (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 H37 w a Hw Hin => WR_AX I Ex H10 H12 H11 H37 w a Hw Hin) (WW_AX I) _).
  - unfold PT. cbn [In]. tauto.
  - split; apply Z.leb_le; reflexivity.
  - cb_introxw. cb_kit BARR HLS.
    rewrite (CO_CONT BARR) in COK by tauto. apply andb_prop in COK as [COK Z15]. apply andb_prop in COK as [COK ZC]. apply andb_prop in COK as [R11 R12].
    split.
    { split; [intros wx; split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UV; exact (REG 11%nat VE R11) | unfold PMSA.a2; rewrite <- UE; exact (REG 12%nat EE R12)]|];
              split; [exact MO2|]; rewrite ST2; split; [apply CCRB; apply negb_true_iff; exact ZC | apply negb_true_iff in Z15; apply Z.eqb_neq in Z15; exact Z15]|].
      split; [exact PA2|]. split; [exact WF2|]. split; [exact BB2|].
      exact (CALLW I IETA BARR i c k ps0 t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z j cj IL ltac:(unfold PT; cbn [In]; tauto) DC Ht Hl Hret Hz Hi Hci HAt HA Hag HLF AK HFL HCO1 HWCO1 HPW1 HLS HLSW). }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    assert (HW3 : PML.ps_win ps3 = PML.ps_win ps2) by (destruct REL as [(_ & _ & _ & _ & _ & X)|(_ & _ & X)]; exact X).
    apply (SAME_POST I BARR PSOK.XS_BARR i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HW3); [|exact BB3].
    intros HC. split; [destruct REL as [(_ & _ & _ & X & _)|(X & _)]; [exact X | rewrite HC in X; discriminate X] | ptr_no].
Qed.

(* [comment removed for export] *)
Lemma L_EOBJ : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther EOBJ) -> PSO.call_chk i c k ps0 EOBJ = true -> PSO.dead_chk i ps0 EOBJ = false ->
  forall M0c, OKVt I M0c -> LEAFV I (PSOIW.ig1 I) M0c i c ps0.      (* [comment removed for export] *)
Proof.
  pose proof (PSOIW.iEOBJ I) as SP. unfold PMXAW.end_object_specXAW, PMXAW.end_container_specXAW, PMXAW.ptransxAW, PMXAW.ptrans_gxAW in SP.
  refine (L_GENX I IETA PMW.FEndObject (PMW.rm_match (PMRXA.the_rmA L)) PMW.inp_win PML.wf_ps PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ _ => PMSA.parser_at L IC) EOBJ (PMXA.PFXA_SCR XKA.VIS) (PMXA.DVXA3 XKA.VISD) true _ _ (fun P V E S2 => PMLA.W_parA IC P E ++ PMXA.W_encA IC V S2) (fun _ => SP) (fun _ _ _ H => H)
            _ PSOK.XS_EOBJ eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PFX (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_same (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 H37 w a Hw Hin => WR_AX I Ex H10 H12 H11 H37 w a Hw Hin) (WW_AX I) _).
  - unfold PT. cbn [In]. tauto.
  - split; apply Z.leb_le; reflexivity.
  - cb_introxw. cb_kit EOBJ HLS.
    rewrite (CO_CONT EOBJ) in COK by tauto. apply andb_prop in COK as [COK Z15]. apply andb_prop in COK as [COK ZC]. apply andb_prop in COK as [R11 R12].
    split.
    { split; [intros wx; split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UV; exact (REG 11%nat VE R11) | unfold PMSA.a2; rewrite <- UE; exact (REG 12%nat EE R12)]|];
              split; [exact MO2|]; rewrite ST2; split; [apply CCRB; apply negb_true_iff; exact ZC | apply negb_true_iff in Z15; apply Z.eqb_neq in Z15; exact Z15]|].
      split; [exact PA2|]. split; [exact WF2|]. split; [exact BB2|].
      exact (CALLW I IETA EOBJ i c k ps0 t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z j cj IL ltac:(unfold PT; cbn [In]; tauto) DC Ht Hl Hret Hz Hi Hci HAt HA Hag HLF AK HFL HCO1 HWCO1 HPW1 HLS HLSW). }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    assert (HW3 : PML.ps_win ps3 = PML.ps_win ps2) by (destruct REL as [(_ & _ & _ & _ & _ & X)|(_ & X)]; exact X).
    apply (SAME_POST I EOBJ PSOK.XS_EOBJ i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HW3); [|exact BB3].
    intros HC. split; [destruct REL as [(_ & _ & X & _)|(X & _)]; [exact X | exfalso; rewrite HC in X; cbn [In] in X; intuition discriminate] | ptr_no].
Qed.
Lemma L_EARR : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther EARR) -> PSO.call_chk i c k ps0 EARR = true -> PSO.dead_chk i ps0 EARR = false ->
  forall M0c, OKVt I M0c -> LEAFV I (PSOIW.ig1 I) M0c i c ps0.      (* [comment removed for export] *)
Proof.
  pose proof (PSOIW.iEARR I) as SP. unfold PMXAW.end_array_specXAW, PMXAW.end_container_specXAW, PMXAW.ptransxAW, PMXAW.ptrans_gxAW in SP.
  refine (L_GENX I IETA PMW.FEndArray (PMW.rm_match (PMRXA.the_rmA L)) PMW.inp_win PML.wf_ps PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ _ => PMSA.parser_at L IC) EARR (PMXA.PFXA_SCR XKA.VIS) (PMXA.DVXA3 XKA.VISD) true _ _ (fun P V E S2 => PMLA.W_parA IC P E ++ PMXA.W_encA IC V S2) (fun _ => SP) (fun _ _ _ H => H)
            _ PSOK.XS_EARR eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PFX (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_same (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 H37 w a Hw Hin => WR_AX I Ex H10 H12 H11 H37 w a Hw Hin) (WW_AX I) _).
  - unfold PT. cbn [In]. tauto.
  - split; apply Z.leb_le; reflexivity.
  - cb_introxw. cb_kit EARR HLS.
    rewrite (CO_CONT EARR) in COK by tauto. apply andb_prop in COK as [COK Z15]. apply andb_prop in COK as [COK ZC]. apply andb_prop in COK as [R11 R12].
    split.
    { split; [intros wx; split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UV; exact (REG 11%nat VE R11) | unfold PMSA.a2; rewrite <- UE; exact (REG 12%nat EE R12)]|];
              split; [exact MO2|]; rewrite ST2; split; [apply CCRB; apply negb_true_iff; exact ZC | apply negb_true_iff in Z15; apply Z.eqb_neq in Z15; exact Z15]|].
      split; [exact PA2|]. split; [exact WF2|]. split; [exact BB2|].
      exact (CALLW I IETA EARR i c k ps0 t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z j cj IL ltac:(unfold PT; cbn [In]; tauto) DC Ht Hl Hret Hz Hi Hci HAt HA Hag HLF AK HFL HCO1 HWCO1 HPW1 HLS HLSW). }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    assert (HW3 : PML.ps_win ps3 = PML.ps_win ps2) by (destruct REL as [(_ & _ & _ & _ & _ & X)|(_ & X)]; exact X).
    apply (SAME_POST I EARR PSOK.XS_EARR i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HW3); [|exact BB3].
    intros HC. split; [destruct REL as [(_ & _ & X & _)|(X & _)]; [exact X | exfalso; rewrite HC in X; cbn [In] in X; intuition discriminate] | ptr_no].
Qed.

(* [comment removed for export] *)
Lemma L_ENDINT : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther ENDINT) -> PSO.call_chk i c k ps0 ENDINT = true -> PSO.dead_chk i ps0 ENDINT = false ->
  forall M0c, OKVt I M0c -> LEAFV I (PSOIW.ig1 I) M0c i c ps0.      (* [comment removed for export] *)
Proof.
  pose proof (PSOIW.iENDINT I) as SP. unfold PMXAW.end_integer_value_specXAW, PMXAW.end_number_specXAW, PMXAW.ptrans_stalexAW in SP.
  refine (L_GENX I IETA PMW.FEndInt (PMW.rm_stale (PMRXA.the_rmA L)) PMW.inp_buf PML.wf_ps_stale PMSA.buf_bound_stale (fun mw M P ps => PMSA.parser_at L IC M P (PML.ps_set_win ps mw))
            (fun mw ps M' P ps' => PMSA.parser_at L IC M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) ENDINT (PMXA.ENDNUMXA_SCR XKA.VIS) (PMXA.DVXA4 XKA.VISD) true _ _ (fun P V E S2 => PMLA.W_parA IC P E ++ PMXA.W_encA IC V S2) SP (fun cw Mx psx H => PMRXA.rm_matchA_stale L cw Mx P psx H)
            _ PSOK.XS_ENDINT eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_ENX (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_same (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 H37 w a Hw Hin => WR_AX I Ex H10 H12 H11 H37 w a Hw Hin) (WW_AX I) _).
  - unfold PT. cbn [In]. tauto.
  - split; apply Z.leb_le; reflexivity.
  - cb_introxw. cb_kit ENDINT HLS.
    rewrite (CO_END ENDINT) in COK by tauto. apply andb_prop in COK as [COK YN]. apply andb_prop in COK as [COK _]. apply andb_prop in COK as [COK Z17].
    apply andb_prop in COK as [R11 R12]. apply Z.eqb_eq in Z17.
    destruct (RNGALL _ _ _ _ _ _ KL YN) as (NF & NR).
    assert (NS : CL5A.uv E' (PSO.v_nst l) = PML.ps_nst ps2) by (apply PSOCK.bv8_eq; [exact NS2 | lia | destruct WF2 as (_ & X & _); lia]).
    rewrite NS in NF.
    split.
    { split; [intros wx; split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UV; exact (REG 11%nat VE R11) | unfold PMSA.a2; rewrite <- UE; exact (REG 12%nat EE R12)]|];
              split; [exact MO2|]; split; [rewrite ST2, Z17; reflexivity|]; apply NUMF; [exact WF2 | exact MO2 | rewrite ST2, Z17; reflexivity | exact (INB _ _ NF)]|].
      split; [exact (PSOX.c_pa _ _ _ _ _ _ _ _ CO2)|]. split; [exact (PML.wf_ps_stale_of _ WF2)|]. split; [exact (BBS_of ps2 BB2 (PSOX.c_win _ _ _ _ _ _ _ _ CO2))|].
      exact (CALLW I IETA ENDINT i c k ps0 t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z j cj IL ltac:(unfold PT; cbn [In]; tauto) DC Ht Hl Hret Hz Hi Hci HAt HA Hag HLF AK HFL HCO1 HWCO1 HPW1 HLS HLSW). }
    intros R2 M2 A2 m2 ps3 code (PA3 & HW3) REL WF3 CM3 EC3 BB3.
    rewrite <- HW3, PSOX.set_win_self in PA3.
    apply (SAME_POST I ENDINT PSOK.XS_ENDINT i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HW3); [|exact BB3].
    intros HC. destruct REL as [(_ & HM & HS & _)|X]; [|rewrite HC in X; discriminate X].
    split; [exact HM|]. split; [intros X; cbv in X; discriminate X|]. intros _. rewrite HS. destruct (Z.eqb (PML.ps_level ps2) 0); cbn [In]; tauto.
Qed.
Lemma L_ENDFRAC : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther ENDFRAC) -> PSO.call_chk i c k ps0 ENDFRAC = true -> PSO.dead_chk i ps0 ENDFRAC = false ->
  forall M0c, OKVt I M0c -> LEAFV I (PSOIW.ig1 I) M0c i c ps0.      (* [comment removed for export] *)
Proof.
  pose proof (PSOIW.iENDFRAC I) as SP. unfold PMXAW.end_fraction_value_specXAW, PMXAW.ptrans_stalexeAW in SP.
  refine (L_GENX I IETA PMW.FEndFrac (PMW.rm_stale (PMRXA.the_rmA L)) PMW.inp_buf PML.wf_ps_stale PMSA.buf_bound_stale (fun mw M P ps => PMSA.parser_at L IC M P (PML.ps_set_win ps mw))
            (fun mw ps M' P ps' => PMSA.parser_at L IC M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) ENDFRAC (PMXA.ENDNUMXA_SCR XKA.VIS) (PMXA.DVXA4 XKA.VISD) true _ _ (fun P V E S2 => PMSA.W_parE L IC P E ++ PMXA.W_encA IC V S2) SP (fun cw Mx psx H => PMRXA.rm_matchA_stale L cw Mx P psx H)
            _ PSOK.XS_ENDFRAC eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_ENX (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_same (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 H37 w a Hw Hin => WR_EX I Ex H10 H12 H11 H37 w a Hw Hin) (WW_EX I) _).
  - unfold PT. cbn [In]. tauto.
  - split; apply Z.leb_le; reflexivity.
  - cb_introxw. cb_kit ENDFRAC HLS.
    rewrite (CO_END ENDFRAC) in COK by tauto. apply andb_prop in COK as [COK YN]. apply andb_prop in COK as [COK _]. apply andb_prop in COK as [COK Z17].
    apply andb_prop in COK as [R11 R12]. apply Z.eqb_eq in Z17.
    destruct (RNGALL _ _ _ _ _ _ KL YN) as (NF & NR).
    assert (NS : CL5A.uv E' (PSO.v_nst l) = PML.ps_nst ps2) by (apply PSOCK.bv8_eq; [exact NS2 | lia | destruct WF2 as (_ & X & _); lia]).
    rewrite NS in NF.
    split.
    { split; [intros wx; split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UV; exact (REG 11%nat VE R11) | unfold PMSA.a2; rewrite <- UE; exact (REG 12%nat EE R12)]|];
              split; [exact MO2|]; split; [rewrite ST2, Z17; reflexivity|]; apply NUMF; [exact WF2 | exact MO2 | rewrite ST2, Z17; reflexivity | exact (INB _ _ NF)]|].
      split; [exact (PSOX.c_pa _ _ _ _ _ _ _ _ CO2)|]. split; [exact (PML.wf_ps_stale_of _ WF2)|]. split; [exact (BBS_of ps2 BB2 (PSOX.c_win _ _ _ _ _ _ _ _ CO2))|].
      exact (CALLW I IETA ENDFRAC i c k ps0 t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z j cj IL ltac:(unfold PT; cbn [In]; tauto) DC Ht Hl Hret Hz Hi Hci HAt HA Hag HLF AK HFL HCO1 HWCO1 HPW1 HLS HLSW). }
    intros R2 M2 A2 m2 ps3 code (PA3 & HW3) REL WF3 CM3 EC3 BB3.
    rewrite <- HW3, PSOX.set_win_self in PA3.
    apply (SAME_POST I ENDFRAC PSOK.XS_ENDFRAC i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HW3); [|exact BB3].
    intros HC. destruct REL as [(_ & HM & HS & _)|X]; [|rewrite HC in X; discriminate X].
    split; [exact HM|]. split; [intros X; cbv in X; discriminate X|]. intros _. rewrite HS. destruct (Z.eqb (PML.ps_level ps2) 0); cbn [In]; tauto.
Qed.

(* [comment removed for export] *)
Lemma L_PNULL : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther PNULL) -> PSO.call_chk i c k ps0 PNULL = true -> PSO.dead_chk i ps0 PNULL = false ->
  forall M0c, OKVt I M0c -> LEAFV I (PSOIW.ig1 I) M0c i c ps0.      (* [comment removed for export] *)
Proof.
  pose proof (PSOIW.iPNULL I) as SP. unfold PMXAW.parse_null_specXAW, PMXAW.ptransxAW, PMXAW.ptrans_gxAW in SP.
  refine (L_GENX I IETA PMW.FParseNull (PMW.rm_match (PMRXA.the_rmA L)) PMW.inp_win PML.wf_ps PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ _ => PMSA.parser_at L IC) PNULL (PMXA.PFXA_SCR XKA.VIS) (PMXA.DVXA2 XKA.VISD) true _ _ (fun P V E S2 => PMLA.W_parA IC P E ++ PMXA.W_encA IC V S2) (fun _ => SP) (fun _ _ _ H => H)
            _ PSOK.XS_PNULL eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PFX (fun _ _ _ => eq_refl)
            (fun _ => XA0_condBm) PSOK.WFACTS_condB (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 H37 w a Hw Hin => WR_AX I Ex H10 H12 H11 H37 w a Hw Hin) (WW_AX I) _).
  - unfold PT. cbn [In]. tauto.
  - split; apply Z.leb_le; reflexivity.
  - cb_introxw. cb_kit PNULL HLS.
    rewrite CO_PNULL in COK. apply andb_prop in COK as [COK YJ]. apply andb_prop in COK as [COK YT]. apply andb_prop in COK as [COK YS]. apply andb_prop in COK as [COK YE].
    apply andb_prop in COK as [R11 R12]. apply expr_eqb_eq in YT. pose proof (WP_same _ _ _ YS) as WPS. rewrite YT in WPS.
    pose proof (LOGE _ _ _ _ _ _ KL YJ) as J1. rewrite J46 in J1.
    pose proof (U0PT i c k ps0 PNULL IL ltac:(unfold PT; cbn [In]; tauto) DC ltac:(intros X; cbv in X; discriminate X) ltac:(intros X; cbv in X; discriminate X)) as HU.
    destruct (WN HU) as (HW2 & R2p).
    pose proof (CURW i c E1 A1 M1 m1 E' l 0 Hci Hi HA Hag (or_introl (conj WPS eq_refl)) R2p JR) as P2.
    split.
    { split; [intros wx; split; [split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- UV; exact (REG 11%nat VE R11) | unfold PMSA.a2; rewrite <- UE; exact (REG 12%nat EE R12)]|];
              split; [exact MO2|]; split; [unfold PMSA.win_exhausted; rewrite HW2; intros X; rewrite P2 in X; lia|]; rewrite ST2; apply EXPB; exact YE|].
      split; [exact PA2|]. split; [exact WF2|]. split; [exact BB2|].
      exact (CALLW I IETA PNULL i c k ps0 t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z j cj IL ltac:(unfold PT; cbn [In]; tauto) DC Ht Hl Hret Hz Hi Hci HAt HA Hag HLF AK HFL HCO1 HWCO1 HPW1 HLS HLSW). }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    apply (NULL_POST I PNULL PSOK.XS_PNULL i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl WPS JR J1 PA3).
    + destruct REL as [(X & Y & _)|(X & Y)]; [left | right]; split; assumption.
    + intros HC. destruct REL as [(_ & _ & X & _)|(X & _)]; [split; [exact X | ptr_no] | rewrite HC in X; discriminate X].
    + exact BB3.
Qed.

(* [comment removed for export] *)
Lemma L_PTRUE : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther PTRUE) -> PSO.call_chk i c k ps0 PTRUE = true -> PSO.dead_chk i ps0 PTRUE = false ->
  forall M0c, OKVt I M0c -> LEAFV I (PSOIW.ig1 I) M0c i c ps0.      (* [comment removed for export] *)
Proof.
  pose proof (PSOIW.iPTRUE I) as SP. unfold PMXAW.parse_true_specXAW, PMXAW.ptrans_curxAW, PMXAW.ptrans_gxAW in SP.
  refine (L_GENX I IETA PMW.FParseTrue (PMW.rm_match (PMRXA.the_rmA L)) PMW.inp_win PML.wf_ps PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ ps M' P ps' => PMSA.parser_at L IC M' P (PML.ps_set_win ps' (PML.ps_win ps))) PTRUE (PMXA.PFXA_SCR XKA.VIS) (PMXA.DVXA2 XKA.VISD) true
            _ _ (fun P V E S2 => PMLA.W_parA IC P E ++ PMXA.W_encA IC V S2) (fun _ => SP) (fun _ _ _ H => H)
            _ PSOK.XS_PTRUE eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PFX (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_condBm (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 H37 w a Hw Hin => WR_AX I Ex H10 H12 H11 H37 w a Hw Hin) (WW_AX I) _).
  - unfold PT. cbn [In]. tauto.
  - split; apply Z.leb_le; reflexivity.
  - cb_introxw. cb_kit PTRUE HLS.
    rewrite (CO_LIT PTRUE) in COK by tauto. apply andb_prop in COK as [COK YJ]. apply andb_prop in COK as [COK YT]. apply andb_prop in COK as [COK YS].
    apply andb_prop in COK as [COK YE]. apply andb_prop in COK as [COK R13]. apply andb_prop in COK as [R11 R12].
    apply expr_eqb_eq in YT. pose proof (WP_same _ _ _ YS) as WPS. rewrite YT in WPS.
    pose proof (LOGE _ _ _ _ _ _ KL YJ) as J1. rewrite J46 in J1.
    pose proof (U0PT i c k ps0 PTRUE IL ltac:(unfold PT; cbn [In]; tauto) DC ltac:(intros X; cbv in X; discriminate X) ltac:(intros X; cbv in X; discriminate X)) as HU.
    destruct (WN HU) as (HW2 & R2p).
    pose proof (CURW i c E1 A1 M1 m1 E' l 0 Hci Hi HA Hag (or_introl (conj WPS eq_refl)) R2p JR) as P2.
    split.
    { split; [intros wx; split; [split; [exact A0|]; split; [unfold PMSA.a2; rewrite <- UV; exact (REG 12%nat VE R12)|]; split; [unfold PMSA.a3; rewrite <- UE; exact (REG 13%nat EE R13)|];
                      exists (CL5A.uv E' (PSO.v_wptr l)), (PSOIW.we0 I); split; [exact HW2 | unfold PMSA.a1; exact (REG 11%nat _ R11)]|];
              split; [exact MO2|]; split; [unfold PMSA.win_exhausted; rewrite HW2; intros X; rewrite P2 in X; lia|]; rewrite ST2; apply EXPB; exact YE|].
      split; [exact PA2|]. split; [exact WF2|]. split; [exact BB2|].
      exact (CALLW I IETA PTRUE i c k ps0 t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z j cj IL ltac:(unfold PT; cbn [In]; tauto) DC Ht Hl Hret Hz Hi Hci HAt HA Hag HLF AK HFL HCO1 HWCO1 HPW1 HLS HLSW). }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    destruct REL as (LR & HNR & HA03).
    apply (CUR_POST I PTRUE PSOK.XS_PTRUE i c ps0 j cj gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code 0 Hci PRE Ht Hl Hi HA Hag HNX Hcj Hj Kj HNXj HLS
             eq_refl eq_refl (fun _ _ => eq_refl) (or_introl (conj WPS eq_refl)) JR PA3 HNR HA03).
    + destruct LR as [(_ & X & _)|(X & _)]; [right; left; exact X | left; rewrite X; lia].
    + intros HC. destruct LR as [(_ & _ & X & _)|(X & _)]; [split; [exact X | ptr_no] | rewrite HC in X; discriminate X].
    + exact BB3.
    + exact (HCR_of M2 code EC3).
Qed.
Lemma L_PFALSE : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther PFALSE) -> PSO.call_chk i c k ps0 PFALSE = true -> PSO.dead_chk i ps0 PFALSE = false ->
  forall M0c, OKVt I M0c -> LEAFV I (PSOIW.ig1 I) M0c i c ps0.      (* [comment removed for export] *)
Proof.
  pose proof (PSOIW.iPFALSE I) as SP. unfold PMXAW.parse_false_specXAW, PMXAW.ptrans_curxAW, PMXAW.ptrans_gxAW in SP.
  refine (L_GENX I IETA PMW.FParseFalse (PMW.rm_match (PMRXA.the_rmA L)) PMW.inp_win PML.wf_ps PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ ps M' P ps' => PMSA.parser_at L IC M' P (PML.ps_set_win ps' (PML.ps_win ps))) PFALSE (PMXA.PFXA_SCR XKA.VIS) (PMXA.DVXA2 XKA.VISD) true
            _ _ (fun P V E S2 => PMLA.W_parA IC P E ++ PMXA.W_encA IC V S2) (fun _ => SP) (fun _ _ _ H => H)
            _ PSOK.XS_PFALSE eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PFX (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_condBm (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 H37 w a Hw Hin => WR_AX I Ex H10 H12 H11 H37 w a Hw Hin) (WW_AX I) _).
  - unfold PT. cbn [In]. tauto.
  - split; apply Z.leb_le; reflexivity.
  - cb_introxw. cb_kit PFALSE HLS.
    rewrite (CO_LIT PFALSE) in COK by tauto. apply andb_prop in COK as [COK YJ]. apply andb_prop in COK as [COK YT]. apply andb_prop in COK as [COK YS].
    apply andb_prop in COK as [COK YE]. apply andb_prop in COK as [COK R13]. apply andb_prop in COK as [R11 R12].
    apply expr_eqb_eq in YT. pose proof (WP_same _ _ _ YS) as WPS. rewrite YT in WPS.
    pose proof (LOGE _ _ _ _ _ _ KL YJ) as J1. rewrite J46 in J1.
    pose proof (U0PT i c k ps0 PFALSE IL ltac:(unfold PT; cbn [In]; tauto) DC ltac:(intros X; cbv in X; discriminate X) ltac:(intros X; cbv in X; discriminate X)) as HU.
    destruct (WN HU) as (HW2 & R2p).
    pose proof (CURW i c E1 A1 M1 m1 E' l 0 Hci Hi HA Hag (or_introl (conj WPS eq_refl)) R2p JR) as P2.
    split.
    { split; [intros wx; split; [split; [exact A0|]; split; [unfold PMSA.a2; rewrite <- UV; exact (REG 12%nat VE R12)|]; split; [unfold PMSA.a3; rewrite <- UE; exact (REG 13%nat EE R13)|];
                      exists (CL5A.uv E' (PSO.v_wptr l)), (PSOIW.we0 I); split; [exact HW2 | unfold PMSA.a1; exact (REG 11%nat _ R11)]|];
              split; [exact MO2|]; split; [unfold PMSA.win_exhausted; rewrite HW2; intros X; rewrite P2 in X; lia|]; rewrite ST2; apply EXPB; exact YE|].
      split; [exact PA2|]. split; [exact WF2|]. split; [exact BB2|].
      exact (CALLW I IETA PFALSE i c k ps0 t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z j cj IL ltac:(unfold PT; cbn [In]; tauto) DC Ht Hl Hret Hz Hi Hci HAt HA Hag HLF AK HFL HCO1 HWCO1 HPW1 HLS HLSW). }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    destruct REL as (LR & HNR & HA03).
    apply (CUR_POST I PFALSE PSOK.XS_PFALSE i c ps0 j cj gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code 0 Hci PRE Ht Hl Hi HA Hag HNX Hcj Hj Kj HNXj HLS
             eq_refl eq_refl (fun _ _ => eq_refl) (or_introl (conj WPS eq_refl)) JR PA3 HNR HA03).
    + destruct LR as [(_ & X & _)|(X & _)]; [right; left; exact X | left; rewrite X; lia].
    + intros HC. destruct LR as [(_ & _ & X & _)|(X & _)]; [split; [exact X | ptr_no] | rewrite HC in X; discriminate X].
    + exact BB3.
    + exact (HCR_of M2 code EC3).
Qed.

(* [comment removed for export] *)
Lemma L_PSTRING : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther PSTRING) -> PSO.call_chk i c k ps0 PSTRING = true -> PSO.dead_chk i ps0 PSTRING = false ->
  forall M0c, OKVt I M0c -> LEAFV I (PSOIW.ig1 I) M0c i c ps0.      (* [comment removed for export] *)
Proof.
  pose proof (PSOIW.iPSTRING I) as SP. unfold PMXAW.parse_string_specXAW, PMXAW.ptrans_curxAW, PMXAW.ptrans_gxAW in SP.
  refine (L_GENX I IETA PMW.FParseString (PMW.rm_match (PMRXA.the_rmA L)) PMW.inp_win PML.wf_ps PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ ps M' P ps' => PMSA.parser_at L IC M' P (PML.ps_set_win ps' (PML.ps_win ps))) PSTRING (PMXA.PFXA_SCR XKA.VIS) (PMXA.DPSXA XKA.VISD) true
            _ _ (fun P V E S2 => PMLA.W_parA IC P E ++ PMXA.W_encA IC V S2) (fun _ => SP) (fun _ _ _ H => H)
            _ PSOK.XS_PSTRING eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PFX (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_condBm (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 H37 w a Hw Hin => WR_AX I Ex H10 H12 H11 H37 w a Hw Hin) (WW_AX I) _).
  - unfold PT. cbn [In]. tauto.
  - split; apply Z.leb_le; reflexivity.
  - cb_introxw. cb_kit PSTRING HLS.
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
    { split; [intros wx; split; [split; [exact A0|]; split; [unfold PMSA.a2; rewrite <- UV; exact (REG 12%nat VE R12)|]; split; [unfold PMSA.a3; rewrite <- UE; exact (REG 13%nat EE R13)|];
                      exists (CL5A.uv E' (PSO.v_wptr l)), (PSOIW.we0 I); split; [exact HW2 | unfold PMSA.a1; exact (REG 11%nat _ R11)]|];
              split; [exact MO2|]; rewrite ST2, Z15; reflexivity|].
      split; [exact PA2|]. split; [exact WF2|]. split; [exact BB2|].
      exact (CALLW I IETA PSTRING i c k ps0 t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z j cj IL ltac:(unfold PT; cbn [In]; tauto) DC Ht Hl Hret Hz Hi Hci HAt HA Hag HLF AK HFL HCO1 HWCO1 HPW1 HLS HLSW). }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    destruct REL as (HNR & HA03 & HPR & HCM).
    pose proof (HCR_of M2 code EC3) as HCR.
    apply (CUR_POST I PSTRING PSOK.XS_PSTRING i c ps0 j cj gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code dl Hci PRE Ht Hl Hi HA Hag HNX Hcj Hj Kj HNXj HLS
             eq_refl eq_refl (fun _ _ => eq_refl) HDL JR PA3 HNR HA03).
    + destruct HPR as [X|[X|X]]; [left; lia | right; left; exact X | right; right].
      unfold PMSA.win_exhausted in X. rewrite HW2 in X. rewrite P2 in X. lia.
    + intros HC. split; [exact (proj1 (HCM HC)) | ptr_no].
    + exact BB3.
    + exact HCR.
Qed.

(* [comment removed for export] *)
Lemma L_PNUMBER : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther PNUMBER) -> PSO.call_chk i c k ps0 PNUMBER = true -> PSO.dead_chk i ps0 PNUMBER = false ->
  forall M0c, OKVt I M0c -> LEAFV I (PSOIW.ig1 I) M0c i c ps0.      (* [comment removed for export] *)
Proof.
  pose proof (PSOIW.iPNUMBER I) as SP. unfold PMXAW.parse_number_specXAW, PMXAW.ptrans_curxeAW, PMXAW.ptrans_gxeAW in SP.
  refine (L_GENX I IETA PMW.FParseNumber (PMW.rm_match (PMRXA.the_rmA L)) PMW.inp_win PML.wf_ps PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ ps M' P ps' => PMSA.parser_at L IC M' P (PML.ps_set_win ps' (PML.ps_win ps))) PNUMBER (PMXA.PFXA_SCR XKA.VIS) (PMXA.DPNXA XKA.VISD) true
            _ _ (fun P V E S2 => PMSA.W_parE L IC P E ++ PMXA.W_encA IC V S2) (fun _ => SP) (fun _ _ _ H => H)
            _ PSOK.XS_PNUMBER eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PFX (fun _ _ _ => eq_refl)
            XW_same PSOK.WFACTS_a1m (fun _ => []) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 H11 H37 w a Hw Hin => WR_EX I Ex H10 H12 H11 H37 w a Hw Hin) (WW_EX I) _).
  - unfold PT. cbn [In]. tauto.
  - split; apply Z.leb_le; reflexivity.
  - cb_introxw. cb_kit PNUMBER HLS.
    rewrite CO_PNUMBER in COK. apply andb_prop in COK as [COK YR]. apply andb_prop in COK as [COK Z17]. apply andb_prop in COK as [COK R13].
    apply andb_prop in COK as [R11 R12]. apply Z.eqb_eq in Z17. apply expr_eqb_eq in YR.
    pose proof (U0PT i c k ps0 PNUMBER IL ltac:(unfold PT; cbn [In]; tauto) DC ltac:(intros X; cbv in X; discriminate X) ltac:(intros X; cbv in X; discriminate X)) as HU.
    destruct (WN HU) as (HW2 & R2p).
    split.
    { split; [intros wx; split; [split; [exact A0|]; split; [unfold PMSA.a2; rewrite <- UV; exact (REG 12%nat VE R12)|]; split; [unfold PMSA.a3; rewrite <- UE; exact (REG 13%nat EE R13)|];
                      exists (CL5A.uv E' (PSO.v_wptr l)), (PSOIW.we0 I); split; [exact HW2 | unfold PMSA.a1; exact (REG 11%nat _ R11)]|];
              split; [exact MO2|]; rewrite ST2, Z17; reflexivity|].
      split; [exact PA2|]. split; [exact WF2|]. split; [exact BB2|].
      exact (CALLW I IETA PNUMBER i c k ps0 t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z j cj IL ltac:(unfold PT; cbn [In]; tauto) DC Ht Hl Hret Hz Hi Hci HAt HA Hag HLF AK HFL HCO1 HWCO1 HPW1 HLS HLSW). }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    destruct REL as (HNR & HA03 & HCM).
    apply (NUM_POST I PNUMBER PSOK.XS_PNUMBER i c ps0 j cj gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX Hcj Hj Kj HNXj HLS
             eq_refl eq_refl (fun _ _ => eq_refl) YR PA3 HNR HA03).
    + intros HC. destruct (HCM HC) as (_ & HM & HSN & HIN). split; [exact HM|]. split; [intros _; split; [exact HIN | exact HSN] | intros [X|X]; cbv in X; discriminate X].
    + exact BB3.
    + exact (HCR_of M2 code EC3).
Qed.

(* [comment removed for export] *)
Lemma L_SKIPSP : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther SKIPSP) -> PSO.call_chk i c k ps0 SKIPSP = true -> PSO.dead_chk i ps0 SKIPSP = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  pose proof (PSOIW.iSKIPSP I) as SP. unfold PMXAW.skip_space_spec2AW, PMXAW.ptransAW, PMXAW.ptrans_gAW in SP.
  refine (L_GEN I IETA PMW.FSkipSpace (PMW.rm_match (PMRXA.the_rmA L)) PMW.inp_win PML.wf_ps PML.buf_bound (fun _ => PMSA.parser_at L IC) (fun _ _ => PMSA.parser_at L IC) SKIPSP PMSA.PF_SCR 4 false _ _ (PMLA.W_parA IC) (fun _ => SP) (fun _ _ _ H => H)
            _ PSOK.XS_SKIPSP eq_refl eq_refl eq_refl (fun _ _ => eq_refl) _ SCR_PF (fun _ _ _ => eq_refl)
            (fun _ => XA0_a1m) PSOK.WFACTS_cell1 (fun g0 => [KRange (EVar g0) 0 0]) (fun _ _ _ => eq_refl) (fun regs Ex H10 H12 w a Hw Hin => WR_A I Ex H10 H12 w a Hw Hin) (WW_A I) (WX_A I) _).
  - unfold PT. cbn [In]. tauto.
  - split; lia.
  - cb_introw. cb_kit SKIPSP HLS.
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
    { split; [intros wx; split; [exact A0|]; split; [unfold PMSA.a1; rewrite <- U200; exact (REG 11%nat _ R11)|]; split; [unfold PML.ws_ok; rewrite MO2; intros X; discriminate X|];
              split; [rewrite MO2, ST2; apply EXPB; exact YE|];
              exists (CL5A.uv E' (PSO.v_wptr l)), (PSOIW.we0 I), (CL5A.uv E' eb); split; [exact HW2|]; split; [rewrite P2; lia|];
              split; [exact (U8LEAF i E1 A1 M1 m1 c ps0 E' R' M' m' (PSO.v_wptr l) eb HA HLF KL HCB) | exact (INB _ _ WSB)]|].
      split; [exact PA2|]. split; [exact WF2|]. split; [exact BB2|].
      exact (CALLW I IETA SKIPSP i c k ps0 t l E1 R1 A1 M1 m1 E' R' M' m' ps1 ps2 g1 z j cj IL ltac:(unfold PT; cbn [In]; tauto) DC Ht Hl Hret Hz Hi Hci HAt HA Hag HLF AK HFL HCO1 HWCO1 HPW1 HLS HLSW). }
    intros R2 M2 A2 m2 ps3 code PA3 REL WF3 CM3 EC3 BB3.
    destruct REL as (HC0 & HCO & HM3 & HWS3 & HSS3 & HLV3). split.
    { apply (SKIP_POST I SKIPSP PSOK.XS_SKIPSP i c ps0 j gx t l E1 A1 M1 m1 E' M' ps1 ps2 g1 z R2 M2 A2 m2 ps3 code Hci PRE Ht Hl Hi HA Hag HNX HLS eq_refl eq_refl PA3 HC0 HCO);
        [|exact BB3].
      intros _. split; [rewrite HM3; exact MO2 | ptr_no]. }
    (* [comment removed for export] *)
    intros _. destruct (PSOX.c_sync _ _ _ _ _ _ _ _ CO2 eq_refl) as [XD XK]. split; [rewrite HLV3; exact XD|].
    destruct HSS3 as [(HS3 & HK3)|(HS3 & _ & HK3)]; [exact (PMXA.key_inv_same ps2 ps3 HS3 HK3 HLV3 MO2 XK)|].
    apply (PMXA.key_inv_push ps2 ps3 (PML.ps_st ps2) MO2 HK3 HLV3 XK). pose proof (EXPB _ YE) as EX. rewrite <- ST2 in EX.
    intros [Hin|Hin]; [exfalso; rewrite HS3 in Hin | cbn [In] in Hin; destruct Hin as [Hin|Hin]; [exfalso; rewrite <- Hin in EX | left; exact Hin]];
      unfold PMXA.KEY_STATES, PML.is_expect, PML.ST_CR, PML.ST_MEMBER_NAME, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON in *; cbn [In] in *; lia.
Qed.

(* [comment removed for export] *)
Lemma L_PTA : forall pc, In pc PTA -> forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> PSO.call_chk i c k ps0 pc = true -> PSO.dead_chk i ps0 pc = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  intros pc Hpc. unfold PTA in Hpc. cbn [In] in Hpc.
  repeat (destruct Hpc as [<-|Hpc]; [first [exact L_SKIPSP | exact L_BMEMBER]|]).
  destruct Hpc.
Qed.
Lemma L_PTX : forall pc, In pc PTX -> forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> PSO.call_chk i c k ps0 pc = true -> PSO.dead_chk i ps0 pc = false ->
  forall M0c, OKVt I M0c -> LEAFV I (PSOIW.ig1 I) M0c i c ps0.
Proof.
  intros pc Hpc. unfold PTX in Hpc. cbn [In] in Hpc.
  repeat (destruct Hpc as [<-|Hpc]; [first [exact L_PNULL | exact L_BOBJ | exact L_BARR | exact L_EOBJ | exact L_EARR
                                          | exact L_PTRUE | exact L_PFALSE | exact L_PSTRING | exact L_PNUMBER | exact L_ENDINT | exact L_ENDFRAC]|]).
  destruct Hpc.
Qed.
Lemma PT_split : forall pc, In pc PT -> In pc PTA \/ In pc PTX.
Proof. intros pc Hpc. unfold PT in Hpc. unfold PTA, PTX. cbn [In] in *. tauto. Qed.
End Q.
End PSOPI.
