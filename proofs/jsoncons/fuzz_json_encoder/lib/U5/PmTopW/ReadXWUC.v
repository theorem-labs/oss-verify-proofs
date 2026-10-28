(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5
  PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5 PmRefFacts2_u5 PmRefRead_u5 PmTopSpecsXW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutLib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopSpecs_u5 ReadKit_u5 ReadStretchX_u5 ReadBase_u5 TopKitX_u5 PsBase_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require Import TopSpecsW_u5 TopKitW_u5 PsKitW_u5 ReadKitXW_u5 ReadStretchXW_u5 ReadInvXW_u5.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require Import ReadXWHU ReadRoomWU ReadXWUB.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module RDXWUC.
Local Strategy expand [TPSW.chunk_of TPSW.rest_of TPSW.chunk_w].
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Ltac inlist := cbv [In RS.KS01 RS.KS012 RS.KSA callee_saved_idx]; repeat (first [left; reflexivity | right]).

Lemma ks012_ksa : forall q, In q RS.KS012 -> In q RS.KSA.
Proof. intros q Hq. unfold RS.KS012, RS.KSA in *. cbn [In] in *. tauto. Qed.
Lemma ks012_cs : forall q : reg, In (ridx q) RS.KS012 -> In (bv_unsigned q) callee_saved_idx.
Proof.
  intros q Hq. pose proof (bv_unsigned_in_range _ q) as Rq. change (bv_modulus 5) with 32 in Rq.
  unfold ridx, RS.KS012 in Hq. unfold callee_saved_idx. cbn [In] in Hq |- *. lia.
Qed.
Lemma rp_split : forall R1 R2 : bvmap 5 word, (forall q : reg, In (ridx q) RS.KS012 -> getr R2 q = getr R1 q) ->
  getr R2 2%bv = getr R1 2%bv -> getr R2 8%bv = getr R1 8%bv -> getr R2 9%bv = getr R1 9%bv -> getr R2 18%bv = getr R1 18%bv -> regs_preserved R1 R2.
Proof.
  intros R1 R2 HK H2 H8 H9 H18 q Hq.
  pose proof (bv_unsigned_in_range _ q) as Rq. change (bv_modulus 5) with 32 in Rq.
  destruct (Z.eq_dec (bv_unsigned q) 2) as [Eq2|N2].
  { assert (q = 2%bv) by (apply bv_eq; exact Eq2). subst q. exact H2. }
  destruct (Z.eq_dec (bv_unsigned q) 8) as [Eq8|N8].
  { assert (q = 8%bv) by (apply bv_eq; exact Eq8). subst q. exact H8. }
  destruct (Z.eq_dec (bv_unsigned q) 9) as [Eq9|N9].
  { assert (q = 9%bv) by (apply bv_eq; exact Eq9). subst q. exact H9. }
  destruct (Z.eq_dec (bv_unsigned q) 18) as [Eq18|N18].
  { assert (q = 18%bv) by (apply bv_eq; exact Eq18). subst q. exact H18. }
  apply HK. unfold callee_saved_idx in Hq. unfold ridx, RS.KS012. cbn [In] in Hq |- *. lia.
Qed.
Lemma exh_eq : forall ps, PMS.win_exhausted ps -> RB.wp ps = RB.we ps.
Proof. intros ps. unfold PMS.win_exhausted, RB.wp, RB.we. destruct (PML.ps_win ps) as [[p e]|]; auto. Qed.
Lemma eq_exh : forall ps, RB.wp ps = RB.we ps -> PMS.win_exhausted ps.
Proof. intros ps. unfold PMS.win_exhausted, RB.wp, RB.we. destruct (PML.ps_win ps) as [[p e]|]; auto. Qed.
Lemma ww_exh : forall ps, PMS.win_exhausted ps -> RDXWHU.ww ps = 0.
Proof. intros ps HX. unfold RDXWHU.ww. rewrite (exh_eq ps HX), Z.eqb_refl. reflexivity. Qed.
Lemma ww_ne : forall ps, RB.wp ps <> RB.we ps -> RDXWHU.ww ps = 1.
Proof. intros ps Hne. unfold RDXWHU.ww. destruct (Z.eqb_spec (RB.wp ps) (RB.we ps)); [contradiction | reflexivity]. Qed.
Lemma nch0 : forall rs, 0 <= PMRR.nchunks rs.
Proof.
  intros rs. unfold PMRR.nchunks. destruct (PMR.r_eof rs); [lia|].
  pose proof (Z.div_pos (Z.of_nat (length (PMR.r_rest rs))) PMR.CHUNK ltac:(lia) ltac:(reflexivity)). lia.
Qed.
Lemma ra_chunk : L5.ra_ok RT.CD_R_CHUNK.
Proof. apply RDXWHU.ra_lit; [split; [apply Z.leb_le | apply Z.ltb_lt]; reflexivity | reflexivity]. Qed.
Lemma ra_pcd : L5.ra_ok RT.CD_R_PCD.
Proof. apply RDXWHU.ra_lit; [split; [apply Z.leb_le | apply Z.ltb_lt]; reflexivity | reflexivity]. Qed.


Lemma ks012_ks01 : forall q, In q RS.KS012 -> In q RS.KS01.
Proof. intros q Hq. unfold RS.KS012, RS.KS01 in *. cbn [In] in *. tauto. Qed.
Lemma rp_trans : forall R1 R2 R3 : bvmap 5 word, regs_preserved R1 R2 -> regs_preserved R2 R3 -> regs_preserved R1 R3.
Proof. intros R1 R2 R3 A C q Hq. rewrite (C q Hq). exact (A q Hq). Qed.
Lemma rp_ksa : forall R1 R2 : bvmap 5 word, TK.keepsR RS.KSA R1 R2 -> getr R2 2%bv = getr R1 2%bv -> regs_preserved R1 R2.
Proof.
  intros R1 R2 HK H2. apply rp_split; [intros q Hq; exact (HK q (ks012_ksa _ Hq)) | exact H2 | exact (HK 8%bv ltac:(inlist)) |
    exact (HK 9%bv ltac:(inlist)) | exact (HK 18%bv ltac:(inlist))].
Qed.
Lemma rp_k01 : forall R0 R R' : bvmap 5 word, TK.keepsR RS.KS01 R0 R -> TK.keepsR RS.KS01 R R' -> getr R' 2%bv = getr R0 2%bv ->
  getr R' 8%bv = getr R0 8%bv -> getr R' 9%bv = getr R0 9%bv -> regs_preserved R0 R'.
Proof.
  intros R0 R R' A C H2 H8 H9. apply rp_split; [intros q Hq; rewrite (C q (ks012_ks01 _ Hq)); exact (A q (ks012_ks01 _ Hq)) | exact H2 | exact H8 | exact H9 |
    rewrite (C 18%bv ltac:(inlist)); exact (A 18%bv ltac:(inlist))].
Qed.
Lemma z2b : forall w : word, Z_to_bv 64 (bv_unsigned w) = w.
Proof. intros w. apply bv_eq. rewrite Z_to_bv_small; [reflexivity | apply bv_unsigned_in_range]. Qed.
Lemma wwz01 : forall rs, 0 <= PMRR.wwz rs <= 1.
Proof. intros rs. unfold PMRR.wwz. destruct (PMR.r_w rs); lia. Qed.
Lemma F_pos : forall rs F, PMRR.nchunks rs + PMRR.wwz rs + 1 <= Z.of_nat F -> exists F2, F = S F2 /\ PMRR.nchunks rs + PMRR.wwz rs <= Z.of_nat F2.
Proof.
  intros rs F HF. pose proof (nch0 rs). pose proof (wwz01 rs).
  destruct F as [|F2]; [change (Z.of_nat 0) with 0 in HF; lia | exists F2; split; [reflexivity | lia]].
Qed.
Lemma wwz_nil : forall IS rep c gp bof rdst, PMRR.wwz (RDXWHU.rsof IS rep c [] gp bof rdst) = 0.
Proof. reflexivity. Qed.
Lemma wwz_cons : forall IS rep c b w gp bof rdst, PMRR.wwz (RDXWHU.rsof IS rep c (b :: w) gp bof rdst) = 1.
Proof. reflexivity. Qed.
Section RK.
Variables (sp Rr E : Z) (R0 : bvmap 5 word).
Definition cdr (R : bvmap 5 word) : Prop :=
  getr R 2%bv = Z_to_bv 64 (sp - 32) /\ getr R 9%bv = Z_to_bv 64 Rr /\ getr R 8%bv = Z_to_bv 64 E /\ getr R 18%bv = Z_to_bv 64 (Rr + 320) /\ TK.keepsR RS.KS012 R0 R.
Lemma cdr_tp : getr R0 4%bv = Z_to_bv 64 PML.TP -> forall R, cdr R -> getr R 4%bv = Z_to_bv 64 PML.TP.
Proof. intros T R (_ & _ & _ & _ & HK). rewrite (HK 4%bv ltac:(inlist)). exact T. Qed.
Lemma cdr_keep : forall R R1 : bvmap 5 word, cdr R -> TK.keepsR RS.KSA R R1 -> getr R1 2%bv = Z_to_bv 64 (sp - 32) -> cdr R1.
Proof.
  intros R R1 (H2 & H9 & H8 & H18 & HK) HA H21.
  split; [exact H21|]. split; [rewrite (HA 9%bv ltac:(inlist)); exact H9|]. split; [rewrite (HA 8%bv ltac:(inlist)); exact H8|].
  split; [rewrite (HA 18%bv ltac:(inlist)); exact H18|].
  intros q Hq. rewrite (HA q (ks012_ksa _ Hq)). exact (HK q Hq).
Qed.
Lemma cdr_pres : forall R R1 : bvmap 5 word, cdr R -> regs_preserved R R1 -> cdr R1.
Proof.
  intros R R1 (H2 & H9 & H8 & H18 & HK) HP.
  split; [rewrite (HP 2%bv ltac:(unfold callee_saved_idx; inlist)); exact H2|].
  split; [rewrite (HP 9%bv ltac:(unfold callee_saved_idx; inlist)); exact H9|].
  split; [rewrite (HP 8%bv ltac:(unfold callee_saved_idx; inlist)); exact H8|].
  split; [rewrite (HP 18%bv ltac:(unfold callee_saved_idx; inlist)); exact H18|].
  intros q Hq. rewrite (HP q (ks012_cs q Hq)). exact (HK q Hq).
Qed.
Lemma cdr_epi : getr R0 2%bv = Z_to_bv 64 sp -> forall R R', cdr R -> getr R' 2%bv = Z_to_bv 64 sp -> RS.same_s02 R0 R' -> TK.keepsR RS.KS012 R R' -> regs_preserved R0 R'.
Proof.
  intros S0 R R' (H2 & H9 & H8 & H18 & HK) H2' (S8 & S9 & S18) HK'.
  apply rp_split; [intros q Hq; rewrite (HK' q Hq); exact (HK q Hq) | rewrite H2', S0; reflexivity | exact S8 | exact S9 | exact S18].
Qed.
End RK.

Section H.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable STRTOD_SCR : Z.
Variable WD_SCR : Z.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis VPUSH : PMS.vec_push_spec L HI.
Hypothesis PSOMEWU : PMW.parse_some_specwU L HI STRTOD_SCR WD_SCR PMR.the_rm.
Hypothesis SKIPWSW : PMW.skip_whitespace_specw L HI STRTOD_SCR PMR.the_rm.
Hypothesis PCDW : PMW.parser_check_done_specw L HI STRTOD_SCR PMR.the_rm.
Hypothesis SETEC : PMS.set_ec_spec L.
Hypothesis RCHUNKW : TPSW.read_chunk_specw L.

Section Run.
Variables (LBo : list (Z * Z)) (sp r Rr IS V E S2 ch kx bx : Z) (rep : PML.srep) (g0 : PML.ls_state) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : ShapeAlg.TSet) (eg0 : PMES.eghost).
Let SS := PMX.READX_SCR STRTOD_SCR WD_SCR.
Let n := Z.of_nat (length (PML.srep_chars rep)).
Let D := PML.srep_data (IS + 80) rep.
Let P := Rr + 320.
Let LBk := lb_remove ch LBo.
Hypothesis Hn : n < 2 ^ 26.
Hypothesis HB : Forall (fun b => 0 <= b <= 255) (PML.srep_chars rep).
Hypothesis G0 : g0 <> PML.LS0.
Hypothesis SPOK : RS.spok sp.
Hypothesis Hceil : hl_ceil L + SS <= sp.
Hypothesis Hsptop : sp <= hl_sptop L.
Hypothesis Htop : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis Prok : L5.ra_ok r.
Hypothesis OR : PML.obj_on_stack L sp Rr 592.
Hypothesis OI : PML.obj_on_stack L sp IS 272.
Hypothesis OV : PML.obj_on_stack L sp V 8.
Hypothesis OE : PML.obj_on_stack L sp E 16.
Hypothesis AP : PML.apart Rr 592 IS 272 /\ PML.apart Rr 592 V 8 /\ PML.apart Rr 592 E 16 /\ PML.apart IS 272 V 8 /\ PML.apart IS 272 E 16 /\ PML.apart V 8 E 16.
Hypothesis OVX : PML.obj_on_stack L sp V PMES.ENC_SIZE.
Hypothesis OS2 : PML.obj_on_stack L sp S2 24.
Hypothesis APX : PML.apart V PMES.ENC_SIZE S2 24 /\ PML.apart Rr 592 V PMES.ENC_SIZE /\ PML.apart Rr 592 S2 24 /\ PML.apart IS 272 V PMES.ENC_SIZE /\ PML.apart IS 272 S2 24 /\
                 PML.apart V PMES.ENC_SIZE E 16 /\ PML.apart S2 24 E 16.
Hypothesis KX0 : 0 <= kx.
Hypothesis INch : In (ch, 16384) LBo.
Hypothesis INrep : forall b, In b (PML.srep_blocks rep) -> In b LBo.
Hypothesis NEch : forall b, In b (PML.srep_blocks rep) -> fst b <> ch.
Hypothesis R0sp : getr R0 2%bv = Z_to_bv 64 sp.
Hypothesis R0tp : getr R0 4%bv = Z_to_bv 64 PML.TP.
Hypothesis HK0 : K [].
Hypothesis BX0 : 0 <= bx.
Hypothesis WR0 : PMW.wroomU eg0 (PMR.K (PML.srep_chars rep)) (PMR.ALLOW (PML.srep_chars rep)).
Let i_CONT0 (b : Z) : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (cr' : credit) (ps' : PML.pstate) (code gp' rdst' : Z) (g' : PML.ls_state) (eg' : PMES.eghost),
  PML.fp_ok fx' ->
  PML.source_at M' Rr ch -> PML.parser_at M' (Rr + 320) ps' -> PML.isrc_at M' IS rep gp' rdst' -> PML.ec_at M' E code -> PML.ls_ok g' M' -> (g' = g0 \/ (g' = PML.LS2 /\ code <> 0)) ->
  PMES.enc_inv M' V S2 eg' -> PML.lits_ok M' ->
  PML.pcredit_x L cr' ps' (kx + PMX.kenc L eg') b -> PML.wf_ps ps' ->
  False ->
  regs_preserved R0 R' -> L5C.hpres L LBk sp SS (RIXW.Wr Rr IS V E S2) M0 M' -> model_but_vm model0 model' -> hi_heap HI (PML.ps_blocks ps' ++ LBo ++ PMES.g_lbv eg') cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model') K.
Proof. intros. contradiction. Defined.
Let i_al8 := @RIXW.al8 sp.
Let i_al16 := @RIXW.al16 sp.
Let i_al8_add := @RIXW.al8_add .
Let i_not_outside := @RIXW.not_outside .
Let i_in_lb_remove := @RIXW.in_lb_remove .
Let i_lb_remove_in := @RIXW.lb_remove_in .
Let i_lb_remove_fst := @RIXW.lb_remove_fst .
Let i_nodup_app_l := @RIXW.nodup_app_l .
Let i_nodup_app_disj := @RIXW.nodup_app_disj .
Let i_win_ok_setwin := @RIXW.win_ok_setwin ch.
Let i_win_ok_exh := @RIXW.win_ok_exh .
Let i_win_ok_mono := @RIXW.win_ok_mono .
Let i_ra_ok_lit := @RIXW.ra_ok_lit r.
Let i_CSv := @RIXW.CSv .
Let i_keeps_sub := @RIXW.keeps_sub .
Let i_keeps_pres := @RIXW.keeps_pres .
Let i_KSM_cs := @RIXW.KSM_cs .
Let i_KSA_cs := @RIXW.KSA_cs .
Let i_KSM_KSA := @RIXW.KSM_KSA .
Let i_KSM_KSW := @RIXW.KSM_KSW .
Let i_KSM_KS45 := @RIXW.KSM_KS45 .
Let i_KSM_KS01 := @RIXW.KSM_KS01 .
Let i_KSM_KS012 := @RIXW.KSM_KS012 .
Let i_KSM_KS06 := @RIXW.KSM_KS06 .
Let i_mk_entry := @RIXW.mk_entry L.
Let i_Wr := @RIXW.Wr Rr IS V E S2.
Let i_Wr_eq := @RIXW.Wr_eq Rr IS V E S2.
Let i_foot := @RIXW.foot Rr IS V E S2.
Let i_wfx := @RIXW.wfx .
Let i_ws_setwin := @RIXW.ws_setwin .
Let i_finish (b : Z) := @RIXW.finish SCFG_P L HI STRTOD_SCR WD_SCR LBo sp r Rr IS V E S2 ch kx b rep g0 R0 M0 model0 K (fun (_ : PMES.eghost) (_ : Z) => False) (i_CONT0 b).
Let i_blk := @RIXW.blk SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY Rr IS rep.
Let i_enc_inv_K := @RIXW.enc_inv_K L STRTOD_SCR WD_SCR sp Rr IS V E S2 rep SPOK Hceil Htop OR OI OV OE OVX OS2.
Let i_lits_K := @RIXW.lits_K .
Let i_enc_stack := @RIXW.enc_stack SCFG_P L HI STRTOD_SCR WD_SCR HIok sp Rr IS V E S2 rep SPOK Hceil Htop OR OI OV OE OVX OS2.
Let i_hpres_weaken := @RIXW.hpres_weaken L.
Let i_ginv_stack (b : Z) := @RIXW.ginv_stack SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp r Rr IS V E S2 ch kx b rep g0 R0 M0 model0 K Hn SPOK Hceil Htop OR OI OV OE OVX OS2 INrep NEch (fun (_ : PMES.eghost) (_ : Z) => False) (i_CONT0 b).
Let i_foot_cases := @RIXW.foot_cases STRTOD_SCR WD_SCR Rr IS V E S2 rep.
Let i_foot_cases2 := @RIXW.foot_cases2 L STRTOD_SCR WD_SCR sp Rr IS V E S2 rep SPOK Hceil Htop OR OI OV OE OVX OS2.
Let i_wpar_foot := @RIXW.wpar_foot STRTOD_SCR WD_SCR Rr IS V E S2 rep.
Let i_wparx_foot := @RIXW.wparx_foot STRTOD_SCR WD_SCR Rr IS V E S2 rep.
Let i_wsi_parx := @RIXW.wsi_parx L STRTOD_SCR WD_SCR sp Rr IS V E S2 rep SPOK Hceil Htop OR OI OV OE OVX OS2.
Let i_out_parx := @RIXW.out_parx L STRTOD_SCR WD_SCR sp Rr IS V E S2 rep SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX.
Let i_mk_stk := @RIXW.mk_stk L STRTOD_SCR WD_SCR sp Rr IS V E rep SPOK Hceil Htop OR OI OV OE.
Let i_mok_bv := @RIXW.mok_bv .
Let i_ginv_ptrans (b : Z) := @RIXW.ginv_ptrans SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep.
Let i_enc_pms (b : Z) := @RIXW.enc_pms SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX.
Let i_Wc := @RIXW.Wc Rr IS E ch.
Let i_hfacts := @RIXW.hfacts SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo Rr IS ch rep INch.
Let i_hfacts_enc := @RIXW.hfacts_enc SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo Rr IS ch rep INch.
Let i_ginv_chunk (b : Z) := @RIXW.ginv_chunk SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INch.
Let i_wf_setwin := @RIXW.wf_setwin .
Let i_pcredit_setwin := @RIXW.pcredit_setwin L.
Let i_ginv_setwin (b : Z) := @RIXW.ginv_setwin SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp r Rr IS V E S2 ch kx b rep g0 R0 M0 model0 K Hn SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INch INrep NEch (fun (_ : PMES.eghost) (_ : Z) => False) (i_CONT0 b).
Let i_We := @RIXW.We E.
Let i_ginv_setec (b : Z) := @RIXW.ginv_setec SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp r Rr IS V E S2 ch kx b rep g0 R0 M0 model0 K Hn SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep NEch (fun (_ : PMES.eghost) (_ : Z) => False) (i_CONT0 b).
Let i_ginv0 := @RIXW.ginv0 L HI STRTOD_SCR WD_SCR LBo sp Rr IS V E S2 ch rep M0 model0.
Let i_ginv0_entry (b : Z) := @RIXW.ginv0_entry SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp r Rr IS V E S2 ch kx b rep g0 R0 M0 model0 K Hn SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep NEch (fun (_ : PMES.eghost) (_ : Z) => False) (i_CONT0 b).
Let i_ginv_ptrans0 (b : Z) := @RIXW.ginv_ptrans0 SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep.
Let i_ginv_pcells (b : Z) := @RIXW.ginv_pcells SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp r Rr IS V E S2 ch kx b rep g0 R0 M0 model0 K Hn SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep NEch (fun (_ : PMES.eghost) (_ : Z) => False) (i_CONT0 b).
Let egacc := @RDXWHU.egacc eg0.
Let wfin := @RDXWHU.wfin rep eg0.
Let ginv (b : Z) := @RDXWHU.ginv L HI STRTOD_SCR WD_SCR LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0.
Let lay := @RDXWHU.lay L STRTOD_SCR WD_SCR sp Rr IS V E rep SPOK Hceil Htop OR OI OV OE.
Let layx := @RDXWHU.layx L STRTOD_SCR WD_SCR sp Rr V S2 rep OVX OS2.
Let rsof := @RDXWHU.rsof IS rep.
Let wst := @RDXWHU.wst Rr.
Let rinvA := @RDXWHU.rinvA Rr IS rep eg0.
Let rinvP := @RDXWHU.rinvP Rr IS rep eg0.
Let rinvB0 := @RDXWHU.rinvB0 Rr IS rep eg0.
Let rinvB := @RDXWHU.rinvB Rr IS rep eg0.
Let rinvE := @RDXWHU.rinvE rep eg0.
Let rinvX := @RDXWHU.rinvX Rr IS rep eg0.
Let accC0 := @RDXWHU.accC0 rep eg0.
Let rinvC0 := @RDXWHU.rinvC0 Rr IS rep eg0.
Let rinvC := @RDXWHU.rinvC Rr IS rep eg0.
Let rinvPC := @RDXWHU.rinvPC Rr IS rep eg0.
Let rinvC00 := @RDXWHU.rinvC00 Rr IS rep eg0.
Let ginv_ptrans (b : Z) := @RDXWHU.ginv_ptrans SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep.
Let enc_pms (b : Z) := @RDXWHU.enc_pms SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX.
Let ginv_chunk (b : Z) := @RDXWHU.ginv_chunk SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INch.
Let ginv0 := @RDXWHU.ginv0 L HI STRTOD_SCR WD_SCR LBo sp Rr IS V E S2 ch rep M0 model0.
Let ginv_ptrans0 (b : Z) := @RDXWHU.ginv_ptrans0 SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep.
Let hfacts := @RDXWHU.hfacts SCFG_P L HI HIok LAY LBo Rr ch rep INch.
Let mk_stk := @RDXWHU.mk_stk L STRTOD_SCR WD_SCR sp Rr IS V E rep SPOK Hceil Htop OR OI OV OE.
Let mk_entry := @RDXWHU.mk_entry L STRTOD_SCR WD_SCR sp Rr IS V E rep SPOK Hceil Htop OR OI OV OE.
Let enc_sync_setwin := @RDXWHU.enc_sync_setwin .
Let oos := @RDXWHU.oos L STRTOD_SCR WD_SCR sp Rr IS rep.
Let ginv_ws (b : Z) := @RDXWHU.ginv_ws L HI STRTOD_SCR WD_SCR LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0.
Let ws_same := @RDXWHU.ws_same .
Let call_ptransw (b : Z) := @RDXWHU.call_ptransw SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 K G0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep HK0.
Let call_chunkw (b : Z) := @RDXWHU.call_chunkw SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY RCHUNKW LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 K Hn HB G0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INch INrep NEch HK0.
Let gcells (b : Z) := @RDXWHU.gcells SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE OVX OS2 INch.
Let blkW := @RDXWHU.blkW SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY Rr IS rep.
Let wst_x (b : Z) := @RDXWHU.wst_x SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE.
Let wst_stack (b : Z) := @RDXWHU.wst_stack SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE.
Let wst_len := @RDXWHU.wst_len Rr.
Let wst_nil := @RDXWHU.wst_nil Rr.
Let wst_cons := @RDXWHU.wst_cons STRTOD_SCR WD_SCR Rr IS rep.
Let exh_nil := @RDXWHU.exh_nil STRTOD_SCR WD_SCR Rr IS rep.
Let wst_core := @RDXWHU.wst_core Rr.
Let st_small := @RDXWHU.st_small STRTOD_SCR WD_SCR Rr IS rep.
Let chunk_post := @RDXWHU.chunk_post STRTOD_SCR WD_SCR Rr IS ch rep HB.
Let wst_rchunk := @RDXWHU.wst_rchunk L STRTOD_SCR WD_SCR sp Rr IS V E ch rep SPOK Hceil Htop OR OI OV OE AP.
Let wst_setwin := @RDXWHU.wst_setwin L STRTOD_SCR WD_SCR sp Rr IS V E ch rep SPOK Hceil Htop OR OI OV OE.
Let step_psome := @RDXWHU.step_psome .
Let step_pcd := @RDXWHU.step_pcd .
Let step_sws := @RDXWHU.step_sws .
Let egacc_app := @RDXWHU.egacc_app STRTOD_SCR WD_SCR Rr IS rep eg0.
Let egacc_nil := @RDXWHU.egacc_nil eg0.
Let wfin_A := @RDXWHU.wfin_A IS rep eg0.
Let wfin_B := @RDXWHU.wfin_B IS rep eg0.
Let wfin_C := @RDXWHU.wfin_C IS rep eg0.
Let wfin_Ceof := @RDXWHU.wfin_Ceof IS rep eg0.
Let b2z_t := @RDXWHU.b2z_t .
Let b2z_f := @RDXWHU.b2z_f .
Let b2z_0 := @RDXWHU.b2z_0 .
Let b2z_n0 := @RDXWHU.b2z_n0 .
Let weof_ne := @RDXWHU.weof_ne IS rep.
Let weof_nil := @RDXWHU.weof_nil IS rep.
Let rankz_in := @RDXWHU.rankz_in .
Let rankz_nin := @RDXWHU.rankz_nin .
Let rtail_break' := @RDXWHU.rtail_break' .
Let refill_eof_w := @RDXWHU.refill_eof_w IS rep.
Let st_mod (b : Z) := @RDXWHU.st_mod L HI STRTOD_SCR WD_SCR LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0.
Let rp_of := @RDXWHU.rp_of L STRTOD_SCR WD_SCR Rr IS V E S2 rep R0 Htop AP APX.
Let cd_frame_x := @RDXWHU.cd_frame_x L STRTOD_SCR WD_SCR sp r Rr IS V E rep R0 SPOK Hceil Hsptop Htop OR OI OV OE.
Let ee := @RDXWHU.ee .
Let ww := @RDXWHU.ww .
Let muC := @RDXWHU.muC IS rep.
Let land2 := @RDXWHU.land2 STRTOD_SCR WD_SCR Rr IS rep.
Let ra_lit := @RDXWHU.ra_lit .
Let ginv_g0 (b : Z) := @RDXWHU.ginv_g0 L HI STRTOD_SCR WD_SCR LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0.
Let ee_range := @RDXWHU.ee_range STRTOD_SCR WD_SCR Rr IS rep.
Let ww_range := @RDXWHU.ww_range STRTOD_SCR WD_SCR Rr IS rep.
Let rd_frame := @RDXWHU.rd_frame sp r R0.
Let rd_frame_x := @RDXWHU.rd_frame_x L STRTOD_SCR WD_SCR sp r Rr IS V E rep R0 SPOK Hceil Hsptop Htop OR OI OV OE.
Let KSN_KSA := @RDXWHU.KSN_KSA L Rr IS V E S2 Htop AP APX.
Let KSN_KSW := @RDXWHU.KSN_KSW L Rr IS V E S2 Htop AP APX.
Let KSN_KS45 := @RDXWHU.KSN_KS45 L Rr IS V E S2 Htop AP APX.
Let KSN_rp := @RDXWHU.KSN_rp L Rr IS V E S2 Htop AP APX.
Let muB := @RDXWHU.muB IS rep.
Let rank := @RDXWHU.rank .
Let muA := @RDXWHU.muA IS rep.
Let rank_range := @RDXWHU.rank_range STRTOD_SCR WD_SCR Rr IS rep.
Let rank_in := @RDXWHU.rank_in .
Let rank_nin := @RDXWHU.rank_nin .
Let wp_setwin := @RDXWHU.wp_setwin .
Let we_setwin := @RDXWHU.we_setwin .
Let more_setwin := @RDXWHU.more_setwin .
Let st_setwin := @RDXWHU.st_setwin .
Let b2z_range := @RDXWHU.b2z_range STRTOD_SCR WD_SCR Rr IS rep.
Let b2z_nz := @RDXWHU.b2z_nz .
Let ginvU := @RDXWUB.ginvU L HI STRTOD_SCR WD_SCR LBo sp Rr IS V E S2 ch kx bx rep g0 M0 model0.
Hypothesis CONTU : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (cr' : credit) (ps' : PML.pstate) (code gp' rdst' : Z) (g' : PML.ls_state) (eg' : PMES.eghost),
  PML.fp_ok fx' ->
  PML.source_at M' Rr ch -> PML.parser_at M' (Rr + 320) ps' -> PML.isrc_at M' IS rep gp' rdst' -> PML.ec_at M' E code -> PML.ls_ok g' M' -> (g' = g0 \/ (g' = PML.LS2 /\ code <> 0)) ->
  PMES.enc_inv M' V S2 eg' -> PML.lits_ok M' ->
  PML.pcredit_x L cr' ps' (kx + PMES.kenc L eg') (bx + PMES.benc L eg') -> PML.wf_ps ps' ->
  wfin eg' code ->
  regs_preserved R0 R' -> L5C.hpres L LBk sp SS (RIXW.Wr Rr IS V E S2) M0 M' -> model_but_vm model0 model' -> hi_heap HI (PML.ps_blocks ps' ++ LBo ++ PMES.g_lbv eg') cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model') K.
Let finishU := @RDXWUB.finishU SCFG_P L HI STRTOD_SCR WD_SCR LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0 CONTU.
Let rd_after_stmtU := @RDXWUB.rd_after_stmtU SCFG_P L HI STRTOD_SCR WD_SCR LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0.
Let rn_entry_stmtU := @RDXWUB.rn_entry_stmtU SCFG_P L HI STRTOD_SCR WD_SCR LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0.

Definition cd_regs (R : bvmap 5 word) : Prop :=
  getr R 2%bv = Z_to_bv 64 (sp - 32) /\ getr R 9%bv = Z_to_bv 64 Rr /\ getr R 8%bv = Z_to_bv 64 E /\ getr R 18%bv = Z_to_bv 64 (Rr + 320) /\ TK.keepsR RS.KS012 R0 R.

Let cd_tp := cdr_tp sp Rr E R0 R0tp.
Let cd_regs_keep := cdr_keep sp Rr E R0.
Let cd_regs_pres := cdr_pres sp Rr E R0.

Lemma gU : forall M model cr ps gp rdst code bof g B eg, ginvU M model cr ps gp rdst code bof g B eg -> ginv (bx + PMES.benc L eg) M model cr ps gp rdst code bof g B eg.
Proof. intros. assumption. Qed.
Lemma Ug : forall M model cr ps gp rdst code bof g B eg, ginv (bx + PMES.benc L eg) M model cr ps gp rdst code bof g B eg -> ginvU M model cr ps gp rdst code bof g B eg.
Proof. intros. assumption. Qed.
Lemma gmod : forall b M model cr ps gp rdst code bof g B eg, ginv b M model cr ps gp rdst code bof g B eg -> m_halted model = None /\ m_vm_lazy model = [].
Proof. intros b M model cr ps gp rdst code bof g B eg GI. destruct GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hh & Hl & _) & _). split; assumption. Qed.
Lemma gheap : forall b M model cr ps gp rdst code bof g B eg, ginv b M model cr ps gp rdst code bof g B eg ->
  hi_heap HI (PML.ps_blocks ps ++ LBo ++ PMES.g_lbv eg) cr M (m_vmmaps model).
Proof. intros b M model cr ps gp rdst code bof g B eg GI. destruct GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HH & _). exact HH. Qed.
Lemma gB : forall b M model cr ps gp rdst code bof g B eg, ginv b M model cr ps gp rdst code bof g B eg -> B <= gp - PML.srep_data (IS + 80) rep.
Proof. intros b M model cr ps gp rdst code bof g B eg GI. destruct GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HB0 & _). exact HB0. Qed.
Lemma gstk : forall b M model cr ps gp rdst code bof g B eg, ginv b M model cr ps gp rdst code bof g B eg ->
  forall a, sp - PMX.READX_SCR STRTOD_SCR WD_SCR <= a < sp -> M (Z_to_bv 64 a) <> None.
Proof. intros b M model cr ps gp rdst code bof g B eg GI. destruct GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HS) & _). exact HS. Qed.
Lemma samem_win : forall M1 M2 : mem, TK.samem (fun a => ~ (Rr + 512 <= a < Rr + 528)) M1 M2 -> TK.samem (fun a => sp - 32 <= a < sp) M1 M2.
Proof. intros M1 M2 HS a Ha Hin. pose proof lay as (_ & _ & LY2 & _). apply HS; [exact Ha|]. cbv beta in Hin |- *. intros C. lia. Qed.

Definition mu0 (gp rdst : Z) : Z := (2 * (PML.srep_data (IS + 80) rep + Z.of_nat (length (PML.srep_chars rep)) - gp) + RDXWHU.ee rdst) * 2.
Lemma muC_eq : forall ps gp rdst, muC ps gp rdst = mu0 gp rdst + RDXWHU.ww ps.
Proof. intros. reflexivity. Qed.
Lemma muC_nn : forall ps gp rdst, gp <= PML.srep_data (IS + 80) rep + Z.of_nat (length (PML.srep_chars rep)) -> 0 <= muC ps gp rdst.
Proof. intros ps gp rdst Hg. rewrite muC_eq. unfold mu0. pose proof (RDXWHU.ee_range STRTOD_SCR WD_SCR Rr IS rep rdst). pose proof (RDXWHU.ww_range STRTOD_SCR WD_SCR Rr IS rep ps). lia. Qed.

Lemma cd_exit : forall (fx : FPState) R M model cr ps gp rdst code bof g B eg,
  PML.fp_ok fx -> ginvU M model cr ps gp rdst code bof g B eg -> wfin eg code -> cd_regs R -> RS.cd_frame M sp r R0 ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.CD_EPI M model) K.
Proof.
  intros fx R M model cr ps gp rdst code bof g B eg Hfp GI WF HR HF.
  destruct (gmod _ _ _ _ _ _ _ _ _ _ _ _ (gU _ _ _ _ _ _ _ _ _ _ _ GI)) as (Hh & Hl).
  pose proof HR as (H2 & _).
  apply (RS.s_cd_epi FPM fx R M model K sp r R0 Hh Hl Hfp H2 SPOK HF Prok).
  intros fx' R' Hfp' H2' HS HK'.
  exact (finishU fx' R' M model cr ps gp rdst code bof g B eg Hfp' GI WF (cdr_epi sp Rr E R0 R0sp R R' HR H2' HS HK')).
Qed.

Definition atC (m : Z) : Prop := forall (fx : FPState) R M model cr ps gp rdst bof B eg,
  muC ps gp rdst < m -> PML.fp_ok fx -> ginvU M model cr ps gp rdst 0 bof g0 B eg -> rinvC M ps gp rdst bof eg -> cd_regs R -> RS.cd_frame M sp r R0 ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.LOOPC M model) K.

Lemma c00_ok : forall m, atC m -> forall (fx : FPState) R M model cr ps gp rdst bof B eg,
  (rdst = 0 -> mu0 gp rdst < m) -> PMS.win_exhausted ps -> PML.fp_ok fx -> ginvU M model cr ps gp rdst 0 bof g0 B eg -> rinvC00 M ps gp rdst bof eg ->
  cd_regs R -> RS.cd_frame M sp r R0 -> getr R 10%bv = Z_to_bv 64 (RB.we ps) -> getr R 11%bv = Z_to_bv 64 (RB.wp ps) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.CD_C00 M model) K.
Proof.
  intros m Hm fx R M model cr ps gp rdst bof B eg Hmu HX Hfp GI HC HR HF H10 H11.
  pose proof (gU _ _ _ _ _ _ _ _ _ _ _ GI) as GIb. destruct (gmod _ _ _ _ _ _ _ _ _ _ _ _ GIb) as (Hh & Hl).
  destruct (gcells _ _ _ _ _ _ _ _ _ _ _ _ GIb) as (G240 & GVT & G152 & G152b & Grd & Gro & G288 & G312 & G512 & G520 & Gwp & Gwe & GE & Gcode & Gdef & G528 & G531 & G532 & Ggp).
  pose proof lay as (LY0 & LY1 & LY2 & LY3 & LY4 & LY5 & _).
  pose proof OI as (OI1 & OI2 & OI3).
  pose proof HR as (H2 & H9 & H8 & H18 & HK).
  destruct HC as (tA & rsB & c & F'' & AC & EOF & WST & C2 & C0).
  refine (RS.s_cd_c00 FPM fx R M model K sp Rr IS rdst (RB.we ps) (RB.wp ps) Hh Hl Hfp H2 SPOK H9 _ _ Gro H10 H11 _ _ G288 G240 GVT G152b _ OI3 _ _).
  - unfold RS.pok. lia.
  - unfold RS.pok. lia.
  - lia.
  - lia.
  - destruct Grd as [-> | ->]; lia.
  - intros Hor fx' R' Hfp' H2' HK'.
    assert (R0d : rdst = 0).
    { destruct Hor as [Hne | Hl2]; [exfalso; exact (Hne (eq_sym (exh_eq ps HX))) | exact (proj1 (land2 rdst Grd) Hl2)]. }
    subst rdst.
    apply (Hm fx' R' M model cr ps gp 0 bof B eg); [rewrite muC_eq, (ww_exh ps HX); specialize (Hmu eq_refl); lia | exact Hfp' | exact GI | | exact (cd_regs_keep R R' HR HK' H2') | exact HF].
    destruct (C0 eq_refl) as (RC & NB).
    unfold rinvC, RDXWHU.rinvC. exists tA, rsB, c, [], F''. split; [exact AC|]. split; [exact EOF|]. split; [exact WST|]. split; [exact RC|].
    rewrite wwz_nil. lia.
  - intros Heq Hl2 fx' R' Hfp' H2' HK'.
    assert (R2d : rdst = 2) by (destruct Grd as [-> | ->]; [exfalso; apply Hl2; reflexivity | reflexivity]).
    subst rdst.
    apply (cd_exit fx' R' M model cr ps gp 2 0 bof g0 B eg Hfp' GI); [| exact (cd_regs_keep R R' HR HK' H2') | exact HF].
    exact (wfin_C eg tA rsB 0 AC EOF (C2 eq_refl)).
Qed.

Lemma pcd_call : forall m, atC m -> forall (fx : FPState) R M model cr ps gp rdst bof B eg,
  mu0 gp rdst < m -> PML.fp_ok fx -> ginvU M model cr ps gp rdst 0 bof g0 B eg -> rinvPC M ps gp rdst bof eg -> cd_regs R -> RS.cd_frame M sp r R0 ->
  getr R 1%bv = Z_to_bv 64 RT.CD_R_PCD -> getr R 10%bv = Z_to_bv 64 (Rr + 320) -> getr R 11%bv = Z_to_bv 64 E ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_PCHECK_DONE M model) K.
Proof.
  intros m Hm fx R M model cr ps gp rdst bof B eg Hmu Hfp GI HC HR HF H1 H10 H11.
  pose proof lay as (LY0 & LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & LY13 & LY14).
  pose proof layx as (LX0 & LX1 & LX2 & LX3 & LX4 & LX5).
  destruct HC as (tA & rsB & c & w & F'' & rs & AC & EOF & WST & Wne & RF & RC & NB).
  pose proof HR as (H2 & H9 & H8 & H18 & HK).
  apply (call_ptransw (bx + PMES.benc L eg) PMW.FCheckDone PML.PC_PCHECK_DONE (PMS.PF_SCR STRTOD_SCR) _ _ PCDW fx R M model cr ps gp rdst bof B eg (sp - 32) RT.CD_R_PCD c w
           Hfp (gU _ _ _ _ _ _ _ _ _ _ _ GI) WST H1 ra_pcd H2 (cd_tp R HR)).
  - pose proof SPOK as (_ & S16). apply i_al16; [exact S16 | reflexivity].
  - lia.
  - lia.
  - lia.
  - cbn [PMW.ax PML.a0 PML.a1]. split; [exact H10 | exact H11].
  - intros ps' code' R' [(_ & Hx & Hmo & Hst & Hsk & Hlv) | C4] Hz; [| lia]. apply (ws_same ps ps' Hmo Hst Hsk Hlv).
    exact (ginv_ws _ _ _ _ _ _ _ _ _ _ _ (gU _ _ _ _ _ _ _ _ _ _ _ GI)).
  - intros fx' R' M' model' cr' ps' code' g' Hfp' HRP GI' HMORE HREL HSTEP HSM.
    cbv zeta in HSTEP. destruct HSTEP as (Hcode & _ & HW).
    rewrite step_pcd in Hcode, HW. unfold PMR.r_of in Hcode, HW. cbn [PMW.r_code PMW.r_ctrl] in Hcode, HW.
    pose proof (RKW.pcd_facts c w) as PF. cbv zeta in PF. destruct PF as (PF0 & PF1).
    assert (HR' : cd_regs R') by (exact (cd_regs_pres R R' HR HRP)).
    pose proof HR' as (H2' & H9' & H8' & H18' & HK').
    assert (HF' : RS.cd_frame M' sp r R0) by (apply (cd_frame_x M M' (sp - 32) HSM); [lia | exact HF]).
    destruct (gmod _ _ _ _ _ _ _ _ _ _ _ _ GI') as (Hh' & Hl').
    destruct (gcells _ _ _ _ _ _ _ _ _ _ _ _ GI') as (G240 & GVT & G152 & G152b & Grd & Gro & G288 & G312 & G512 & G520 & Gwp & Gwe & GE & Gcode & Gdef & G528 & G531 & G532 & Ggp).
    pose proof OE as (OE1 & OE2 & OE3).
    refine (RS.s_cd_r_pcd FPM fx' R' M' model' K sp Rr E code' (RB.wp ps') (RB.we ps') Hh' Hl' Hfp' H2' SPOK H9' H8' _ _ GE Gcode G512 G520 _ _ _ _).
    + unfold RS.pok. lia.
    + unfold RS.pok. lia.
    + lia.
    + lia.
    + intros Hne fx2 R2 Hfp2 H22 HK2.
      apply (cd_exit fx2 R2 M' model' cr' ps' gp rdst code' bof g' B eg Hfp2 (Ug _ _ _ _ _ _ _ _ _ _ _ GI')); [| exact (cd_regs_keep R' R2 HR' HK2 H22) | exact HF'].
      apply (wfin_C eg tA rsB code' AC EOF).
      destruct w as [|b0 w0]; [exfalso; exact (Wne eq_refl)|].
      rewrite RC. rewrite (PMRR.rcheck_unfold F'' rs), RF. unfold RDXWHU.rsof, RKW.rsof. cbn [fst snd negb Z.eqb PMR.r_w PMR.r_c PMR.r_rest PMR.r_bof PMR.r_eof].
      rewrite <- Hcode. destruct (Z.eqb_spec code' 0) as [E0|E0]; [contradiction | reflexivity].
    + intros Hz fx2 R2 Hfp2 H22 H102 H112 HK2.
      assert (Hq0 : PMR.q_code (PMR.pcheck_done c w) = 0) by (rewrite <- Hcode; exact Hz).
      destruct (PF0 Hq0) as (QW & QC).
      rewrite Hz in HREL, GI', HW.
      destruct HREL as [(_ & HX' & HMO & HST & HSK & HLV) | C4]; [| lia].
      assert (W' : RDXWHU.wst Rr M' ps' c []).
      { specialize (HW eq_refl). unfold PMW.w_after in HW. cbn [PMW.r_used] in HW. rewrite QC, QW in HW.
        replace (Z.to_nat (Z.of_nat (length w) - Z.of_nat (length (@nil Z)))) with (length w) in HW by (cbn [length]; lia).
        rewrite skipn_all in HW. exact HW. }
      assert (GI2 : ginvU M' model' cr' ps' gp rdst 0 bof g0 B eg).
      { pose proof (ginv_g0 _ _ _ _ _ _ _ _ _ _ _ GI') as Eg. subst g'. exact GI'. }
      apply (c00_ok m Hm fx2 R2 M' model' cr' ps' gp rdst bof B eg); [| exact HX' | exact Hfp2 | exact GI2 | | exact (cd_regs_keep R' R2 HR' HK2 H22) | exact HF' | exact H102 | exact H112].
      * intros _. lia.
      * assert (RC2 : PMR.rcheck (S F'') rs = PMR.rcheck F'' (RDXWHU.rsof IS rep c [] gp bof rdst) \/ rdst = 2 /\ PMR.rcheck (S F'') rs = 0).
        { destruct w as [|b0 w0]; [exfalso; exact (Wne eq_refl)|].
          rewrite (PMRR.rcheck_unfold F'' rs), RF. unfold RDXWHU.rsof, RKW.rsof. cbn [fst snd negb Z.eqb PMR.r_w PMR.r_c PMR.r_rest PMR.r_bof PMR.r_eof].
          rewrite Hq0, QC, QW. cbn [negb Z.eqb PMR.q_c PMR.q_w PMR.r_eof].
          destruct (Z.eqb_spec rdst 2) as [->|N2]; [right; split; reflexivity | left; reflexivity]. }
        exists tA, rsB, c, F''. split; [exact AC|]. split; [exact EOF|]. split; [exact W'|].
        split.
        -- intros ->. rewrite RC. destruct RC2 as [RC2 | (_ & RC2)]; [| exact RC2].
           rewrite RC2. destruct F'' as [|F3]; [pose proof (nch0 (RDXWHU.rsof IS rep c w gp bof 2)) as N0; change (Z.of_nat 0) with 0 in NB; lia | reflexivity].
        -- intros ->. split; [| exact NB]. rewrite RC. destruct RC2 as [RC2 | (E2 & _)]; [exact RC2 | discriminate E2].
Qed.

Lemma loopC_step : forall m, atC m -> atC (m + 1).
Proof.
  intros m Hm fx R M model cr ps gp rdst bof B eg Hmu Hfp GI HC HR HF.
  pose proof (gU _ _ _ _ _ _ _ _ _ _ _ GI) as GIb.
  destruct (gmod _ _ _ _ _ _ _ _ _ _ _ _ GIb) as (Hh & Hl).
  destruct (gcells _ _ _ _ _ _ _ _ _ _ _ _ GIb) as (G240 & GVT & G152 & G152b & Grd & Gro & G288 & G312 & G512 & G520 & Gwp & Gwe & GE & Gcode & Gdef & G528 & G531 & G532 & Ggp).
  pose proof lay as (LY0 & LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & LY13 & LY14).
  pose proof OR as (OR1 & OR2 & OR3).
  pose proof HR as (H2 & H9 & H8 & H18 & HK).
  destruct HC as (tA & rsB & c & w & F' & AC & EOF & WST & RC & NB).
  destruct (F_pos _ _ NB) as (F2 & -> & NB2).
  refine (RS.s_loopC FPM fx R M model K sp Rr (RB.we ps) (RB.wp ps) Hh Hl Hfp H2 SPOK H9 _ OR3 G512 G520 _ _ _ _).
  - unfold RS.pok. lia.
  - lia.
  - lia.
  - intros Heq fx' R' Hfp' H2' H1' H10' H11' HK'.
    assert (HX : PMS.win_exhausted ps) by exact (eq_exh ps Heq).
    pose proof (wst_nil _ _ _ _ WST HX) as ->.
    assert (HR' : cd_regs R') by exact (cd_regs_keep R R' HR HK' H2').
    rewrite H9 in H10'. rewrite H8 in H11'.
    destruct (hfacts M model cr ps eg (gheap _ _ _ _ _ _ _ _ _ _ _ _ GIb)) as (_ & _ & _ & _ & HC0 & HC1 & _ & _ & (BR0 & _)).
    pose proof AP as (_ & _ & APE & _).
    apply (call_chunkw (bx + PMES.benc L eg) fx' R' M model cr ps gp rdst bof B eg (sp - 32) RT.CD_R_CHUNK Hfp' GIb HX H1' ra_chunk H2' (cd_tp R' HR') H10' H11').
    + apply i_al16; [exact LY1 | reflexivity].
    + lia.
    + lia.
    + intros fx2 R2 M2 pc k gp' rdst' code' bof' g' Hfp2 HRP2 GI2 H102 H112 Hp0 Hpk Hk Hkch Hgp' Hkg Hc0 Hrd' H2b H0b HFB HGR HSM.
      assert (HR2 : cd_regs R2) by exact (cd_regs_pres R' R2 HR' HRP2).
      pose proof HR2 as (H22 & H92 & H82 & H182 & HK2).
      assert (HF2 : RS.cd_frame M2 sp r R0) by (apply (cd_frame_x M M2 (sp - 32) HSM); [lia | exact HF]).
      destruct (gmod _ _ _ _ _ _ _ _ _ _ _ _ GI2) as (Hh2 & Hl2).
      destruct (gcells _ _ _ _ _ _ _ _ _ _ _ _ GI2) as (G240' & GVT' & G152' & G152b' & Grd'' & Gro' & G288' & G312' & G512' & G520' & Gwp' & Gwe' & GE' & Gcode' & Gdef' & G528' & G531' & G532' & Ggp').
      destruct (chunk_post M2 c gp rdst bof pc k gp' rdst' code' bof' Ggp Grd H2b H0b) as (w1 & Hrf & Hlw & Hbw & HFw & Hcw & Hnch).
      assert (WST2 : RDXWHU.wst Rr M2 ps c []) by exact (wst_rchunk M M2 ps c (sp - 32) WST HX HFB ltac:(lia) HC1).
      refine (RS.s_cd_r_chunk FPM fx2 R2 M2 model K sp Rr E code' (RB.wp ps) (RB.we ps) pc k Hh2 Hl2 Hfp2 H22 SPOK H92 H82 _ _ H102 H112 Hp0 ltac:(lia) ltac:(lia) _ GE' Gcode' G512' G520' ltac:(lia) ltac:(lia) Gdef' _ _ _ _).
      * unfold RS.pok. lia.
      * unfold RS.pok. lia.
      * intros Hk0. destruct (Hkch ltac:(lia)) as (Q1 & Q2). unfold RS.pok. lia.
      * destruct APE as [A1 | A1]; [left | right]; lia.
      * intros Hne fx3 R3 Hfp3 H23 HK3.
        apply (cd_exit fx3 R3 M2 model cr ps gp' rdst' code' bof' g' B eg Hfp3 (Ug _ _ _ _ _ _ _ _ _ _ _ GI2)); [| exact (cd_regs_keep R2 R3 HR2 HK3 H23) | exact HF2].
        apply (wfin_C eg tA rsB code' AC EOF). rewrite RC. exact (PMRR.rcheck_referr F2 _ _ code' Hrf Hne).
      * intros Hz Hk0 _ fx3 R3 Hfp3 H23 H103 H113 HK3.
        pose proof (Hc0 Hz Hk0) as Hrd2. subst rdst'.
        rewrite Hz in Hrf, GI2.
        destruct w1 as [|b1 w1]; [| cbn [length] in Hlw; lia].
        pose proof (ginv_g0 _ _ _ _ _ _ _ _ _ _ _ GI2) as Eg. subst g'.
        apply (c00_ok m Hm fx3 R3 M2 model cr ps gp' 2 bof' B eg); [intros E2; discriminate E2 | exact HX | exact Hfp3 | exact (Ug _ _ _ _ _ _ _ _ _ _ _ GI2) | | exact (cd_regs_keep R2 R3 HR2 HK3 H23) | exact HF2 | exact H103 | rewrite (exh_eq ps HX); exact H113].
        exists tA, rsB, c, F2. split; [exact AC|]. split; [exact EOF|]. split; [exact WST2|].
        split; [| intros E2; discriminate E2].
        intros _. rewrite RC, (PMRR.rcheck_unfold F2), Hrf. reflexivity.
      * intros Hz fx3 R3 M3 Hfp3 H23 H13 H103 H113 HK3 Hcase. rewrite Hz in Hrf, GI2.
        destruct Hcase as [(_ & Hne & _) | (Hk0 & W512 & W520 & HSM3 & HGR3)]; [exfalso; exact (Hne Heq) |].
        assert (Hrd0 : rdst = 0) by (destruct Grd as [E0 | E2]; [exact E0 | destruct (H2b E2) as (K0 & _); contradiction]).
        subst rdst.
        pose proof (ginv_g0 _ _ _ _ _ _ _ _ _ _ _ GI2) as Eg. subst g'.
        destruct (Hkch ltac:(lia)) as (Q1 & Q2).
        pose proof (gB _ _ _ _ _ _ _ _ _ _ _ _ GIb) as HBg.
        destruct (i_ginv_setwin (bx + PMES.benc L eg) M2 M3 model cr ps gp' rdst' bof' g0 B eg pc k GI2 HX HSM3 HGR3 W512 W520 ltac:(lia) Q1 Q2 ltac:(lia)) as (GI3 & _).
        assert (WST3 : RDXWHU.wst Rr M3 (PML.ps_set_win ps (Some (pc, pc + k))) c w1).
        { apply (wst_setwin M2 M3 ps c w1 pc k WST2 HSM3 (Hbw ltac:(lia)) Hlw HFw); lia. }
        assert (HF3 : RS.cd_frame M3 sp r R0) by (apply (cd_frame_x M2 M3 (sp - 32) (samem_win M2 M3 HSM3)); [lia | exact HF2]).
        assert (HR3 : cd_regs R3) by exact (cd_regs_keep R2 R3 HR2 HK3 H23).
        apply (pcd_call m Hm fx3 R3 M3 model cr (PML.ps_set_win ps (Some (pc, pc + k))) gp' rdst' bof' (B + k) eg); [| exact Hfp3 | exact (Ug _ _ _ _ _ _ _ _ _ _ _ GI3) | | exact HR3 | exact HF3 | exact H13 | rewrite H103; exact H182 | exact H113].
        -- rewrite muC_eq, (ww_exh ps HX) in Hmu. unfold mu0 in *.
           pose proof (RDXWHU.ee_range STRTOD_SCR WD_SCR Rr IS rep 0). pose proof (RDXWHU.ee_range STRTOD_SCR WD_SCR Rr IS rep rdst'). lia.
        -- exists tA, rsB, c, w1, F2, (RDXWHU.rsof IS rep c [] gp bof 0).
           split; [exact AC|]. split; [exact EOF|]. split; [exact WST3|].
           split; [intros E1; subst w1; cbn [length] in Hlw; lia|].
           split; [exact Hrf|]. split; [exact RC|].
           specialize (Hnch eq_refl). rewrite wwz_nil in NB2. lia.
  - intros Hne fx' R' Hfp' H2' H1' H10' H11' HK'.
    assert (HNX : ~ PMS.win_exhausted ps) by (intros HX; exact (Hne (exh_eq ps HX))).
    pose proof (wst_cons _ _ _ _ WST HNX) as Wne.
    apply (pcd_call m Hm fx' R' M model cr ps gp rdst bof B eg); [| exact Hfp' | exact GI | | exact (cd_regs_keep R R' HR HK' H2') | exact HF | exact H1' | rewrite H10'; exact H18 | rewrite H11'; exact H8].
    + rewrite muC_eq, (ww_ne ps Hne) in Hmu. lia.
    + destruct w as [|b0 w0]; [exfalso; exact (Wne eq_refl)|].
      exists tA, rsB, c, (b0 :: w0), F2, (RDXWHU.rsof IS rep c (b0 :: w0) gp bof rdst).
      split; [exact AC|]. split; [exact EOF|]. split; [exact WST|]. split; [exact Wne|].
      split; [exact (RKW.refill_nonempty IS rep c b0 w0 gp bof rdst)|]. split; [exact RC|].
      rewrite wwz_cons in NB2. lia.
Qed.

Lemma loopC_all : forall k : nat, atC (Z.of_nat k).
Proof.
  induction k as [|k IH].
  - intros fx R M model cr ps gp rdst bof B eg Hmu Hfp GI HC HR HF. exfalso.
    destruct (gcells _ _ _ _ _ _ _ _ _ _ _ _ (gU _ _ _ _ _ _ _ _ _ _ _ GI)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ggp).
    pose proof (muC_nn ps gp rdst (proj2 Ggp)). change (Z.of_nat 0) with 0 in Hmu. lia.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_r. exact (loopC_step _ IH).
Qed.

Lemma cd_ok : forall (fx : FPState) R M model cr ps gp rdst bof B eg,
  PML.fp_ok fx -> ginvU M model cr ps gp rdst 0 bof g0 B eg -> rinvC0 M ps gp rdst bof eg -> getr R 2%bv = Z_to_bv 64 sp -> getr R 1%bv = Z_to_bv 64 r ->
  getr R 10%bv = Z_to_bv 64 Rr -> getr R 11%bv = Z_to_bv 64 E -> regs_preserved R0 R ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_RCHECK_DONE M model) K.
Proof.
  intros fx R M model cr ps gp rdst bof B eg Hfp GI HC0 H2 H1 H10 H11 HRP.
  pose proof (gU _ _ _ _ _ _ _ _ _ _ _ GI) as GIb.
  destruct (gmod _ _ _ _ _ _ _ _ _ _ _ _ GIb) as (Hh & Hl).
  destruct (gcells _ _ _ _ _ _ _ _ _ _ _ _ GIb) as (G240 & GVT & G152 & G152b & Grd & Gro & G288 & G312 & G512 & G520 & Gwp & Gwe & GE & Gcode & Gdef & G528 & G531 & G532 & Ggp).
  pose proof lay as (LY0 & LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & LY13 & LY14).
  pose proof layx as (LX0 & LX1 & LX2 & LX3 & LX4 & LX5).
  pose proof OI as (OI1 & OI2 & OI3).
  destruct HC0 as (tA & rsB & c & w & AC & WST & ->).
  assert (TP : getr R 4%bv = Z_to_bv 64 PML.TP) by (rewrite (HRP 4%bv ltac:(inlist)); exact R0tp).
  refine (RS.s_cd_entry FPM fx R M model K sp Rr IS rdst (RB.wp ps) (RB.we ps) r Hh Hl Hfp H2 SPOK H10 H1 _ _ _ Gro G240 GVT G152 _ _ G288 G512 G520 _ _ _ LY2 LY4 OI3 _ _).
  - pose proof Prok as (P1 & _). lia.
  - unfold RS.pok. lia.
  - unfold RS.pok. lia.
  - destruct Grd as [-> | ->]; lia.
  - destruct Grd as [-> | ->]; reflexivity.
  - lia.
  - lia.
  - intros i Hi. apply (gstk _ _ _ _ _ _ _ _ _ _ _ _ GIb). lia.
  - intros Hl2 fx' R' M' Hfp' H2' H1' H10' H11' HK' HSM HGR.
    assert (Hr2 : rdst = 2) by (destruct Grd as [E0 | E2]; [subst rdst; exfalso; apply Hl2; reflexivity | exact E2]).
    subst rdst.
    assert (GI' : ginv (bx + PMES.benc L eg) M' model cr ps gp 2 0 bof g0 B eg).
    { apply (i_ginv_stack _ M M' model cr ps gp 2 0 bof g0 B eg (sp - 32) sp GIb HSM HGR); lia. }
    assert (WST' : RDXWHU.wst Rr M' ps c w) by (apply (wst_stack _ M M' model cr ps gp 2 0 bof g0 B eg c w (sp - 32) sp GIb WST HSM); lia).
    assert (TP' : getr R' 4%bv = Z_to_bv 64 PML.TP) by (rewrite (HK' 4%bv ltac:(inlist)); exact TP).
    apply (call_ptransw (bx + PMES.benc L eg) PMW.FCheckDone PML.PC_PCHECK_DONE (PMS.PF_SCR STRTOD_SCR) _ _ PCDW fx' R' M' model cr ps gp 2 bof B eg sp r c w
             Hfp' GI' WST' H1' Prok H2' TP').
    + exact LY1.
    + lia.
    + lia.
    + lia.
    + cbn [PMW.ax PML.a0 PML.a1]. split; [exact H10' | unfold PML.a1; rewrite H11'; exact H11].
    + intros ps' code' R2 [(_ & Hx & Hmo & Hst & Hsk & Hlv) | C4] Hz; [| lia]. apply (ws_same ps ps' Hmo Hst Hsk Hlv).
      exact (ginv_ws _ _ _ _ _ _ _ _ _ _ _ GIb).
    + intros fx2 R2 M2 model2 cr2 ps2 code2 g2 Hfp2 HRP2 GI2 _ _ HSTEP _.
      cbv zeta in HSTEP. destruct HSTEP as (Hcode & _ & _).
      rewrite step_pcd in Hcode. unfold PMR.r_of in Hcode. cbn [PMW.r_code] in Hcode.
      apply (finishU fx2 R2 M2 model2 cr2 ps2 gp 2 code2 bof g2 B eg Hfp2 (Ug _ _ _ _ _ _ _ _ _ _ _ GI2)).
      * exact (wfin_Ceof eg tA c w gp bof code2 AC Hcode).
      * apply (rp_trans R0 R R2 HRP). apply (rp_trans R R' R2); [| exact HRP2].
        apply rp_ksa; [exact HK' | rewrite H2', H2; reflexivity].
  - intros Hl0 fx' R' M' Hfp' H2' H9' H8' H18' HK' HF' HSM HGR.
    assert (Hr0 : rdst = 0) by exact (proj1 (land2 rdst Grd) Hl0).
    subst rdst.
    assert (GI' : ginv (bx + PMES.benc L eg) M' model cr ps gp 0 0 bof g0 B eg).
    { apply (i_ginv_stack _ M M' model cr ps gp 0 0 bof g0 B eg (sp - 32) sp GIb HSM HGR); lia. }
    assert (WST' : RDXWHU.wst Rr M' ps c w) by (apply (wst_stack _ M M' model cr ps gp 0 0 bof g0 B eg c w (sp - 32) sp GIb WST HSM); lia).
    assert (HR' : cd_regs R').
    { unfold cd_regs. split; [exact H2'|]. split; [exact H9'|]. split; [rewrite H8'; exact H11|]. split; [exact H18'|].
      intros q Hq. rewrite (HK' q Hq). exact (HRP q (ks012_cs q Hq)). }
    assert (HF0 : RS.cd_frame M' sp r R0).
    { unfold RS.cd_frame in HF' |- *. rewrite (HRP 8%bv ltac:(inlist)), (HRP 9%bv ltac:(inlist)), (HRP 18%bv ltac:(inlist)) in HF'. exact HF'. }
    pose proof (muC_nn ps gp 0 (proj2 Ggp)) as MN.
    apply (loopC_all (Z.to_nat (muC ps gp 0 + 1)) fx' R' M' model cr ps gp 0 bof B eg); [rewrite Z2Nat.id by lia; lia | exact Hfp' | exact (Ug _ _ _ _ _ _ _ _ _ _ _ GI') | | exact HR' | exact HF0].
    exists tA, (RDXWHU.rsof IS rep c w gp bof 0), c, w, (PMR.rfuel (PML.srep_chars rep)).
    split; [exact AC|]. split; [reflexivity|]. split; [exact WST'|]. split; [reflexivity|].
    pose proof (RKW.rfuel_ge IS rep c w gp bof 0 Ggp) as RF. change (RKW.rsof IS rep c w gp bof 0) with (RDXWHU.rsof IS rep c w gp bof 0) in RF.
    pose proof (wwz01 (RDXWHU.rsof IS rep c w gp bof 0)). lia.
Qed.

Lemma rd_afterU : rd_after_stmtU.
Proof using All.
  intros fx R M model cr ps gp rdst code bof g B eg Hfp GI HX HF H2 H8 H9 HK.
  pose proof (gU _ _ _ _ _ _ _ _ _ _ _ GI) as GIb.
  destruct (gmod _ _ _ _ _ _ _ _ _ _ _ _ GIb) as (Hh & Hl).
  destruct (gcells _ _ _ _ _ _ _ _ _ _ _ _ GIb) as (G240 & GVT & G152 & G152b & Grd & Gro & G288 & G312 & G512 & G520 & Gwp & Gwe & GE & Gcode & Gdef & G528 & G531 & G532 & Ggp).
  pose proof lay as (LY0 & LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & LY13 & LY14).
  destruct HF as (F8 & F16 & F24).
  assert (RP : forall R' : bvmap 5 word, TK.keepsR RS.KS01 R R' -> getr R' 2%bv = Z_to_bv 64 sp -> getr R' 8%bv = Z_to_bv 64 (bv_unsigned (getr R0 8%bv)) ->
             getr R' 9%bv = Z_to_bv 64 (bv_unsigned (getr R0 9%bv)) -> regs_preserved R0 R').
  { intros R' HK' H2' H8' H9'. apply (rp_k01 R0 R R' HK HK'); [rewrite H2', R0sp; reflexivity | rewrite H8', z2b; reflexivity | rewrite H9', z2b; reflexivity]. }
  destruct HX as (tA & Hrl & Hacc & Hcase).
  refine (RS.s_rd_r_next FPM fx R M model K sp E r (bv_unsigned (getr R0 8%bv)) (bv_unsigned (getr R0 9%bv)) code Hh Hl Hfp H2 SPOK H8 _ GE Gcode F8 F16 F24 Prok (bv_unsigned_in_range _ _) (bv_unsigned_in_range _ _) _ _).
  - unfold RS.pok. lia.
  - intros Hc0 fx' R' Hfp' H2' H1' H10' H11' H8' H9' HK'. subst code.
    pose proof (ginv_g0 _ _ _ _ _ _ _ _ _ _ _ GIb) as ->.
    apply (cd_ok fx' R' M model cr ps gp rdst bof B eg Hfp' GI); [| exact H2' | exact H1' | rewrite H10'; exact H9 | exact H11' | exact (RP R' HK' H2' H8' H9')].
    destruct Hcase as [(Hne & Hc) | (Ht0 & tB & Htb & [(Hne & Hc) | (Hs0 & _ & c & w & WST & Hfst)])]; [exfalso; exact (Hne (eq_sym Hc)) | exfalso; exact (Hne (eq_sym Hc)) |].
    exists tA, (fst tB), c, w. split; [| split; [exact WST | exact Hfst]].
    split; [exact Hrl|]. split; [exact Ht0|]. split; [exact Hacc|]. rewrite Htb. destruct tB as [rsT cT]. cbn [fst snd] in *. subst cT. reflexivity.
  - intros Hne fx' R' Hfp' H2' H8' H9' HK'.
    apply (finishU fx' R' M model cr ps gp rdst code bof g B eg Hfp' GI); [| exact (RP R' HK' H2' H8' H9')].
    destruct Hcase as [(Ht & ->) | (Ht0 & tB & Htb & [(Hs & ->) | (_ & Hc & _)])].
    + exact (wfin_A eg tA Hrl Ht Hacc).
    + exact (wfin_B eg tA tB Hrl Ht0 Hacc Htb Hs).
    + contradiction.
Qed.
End Run.
End H.
End RDXWUC.
