(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmCurDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseSomeAt_u ParseSomeSem_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallPure SmallKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmSmall Require Import SmallAt_u SmallPt_u SmallWin_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmSmall Require Import SmallCall2_u SmallCur_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import VisitSums.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_end_integer_value_csrc_T_u Cut_end_integer_value_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module EndIntegerValueProof.
Module G := Cut_end_integer_value_csrc_u.
Module GT := Cut_end_integer_value_csrc_T_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Definition PCF : Z := PML.PC_END_INT.
Definition Pb : expr := EVar 10.  Definition Vb : expr := EVar 11.  Definition Eb : expr := EVar 12.
Definition DECU64 : Z := PML.PC_DEC_U64.
Definition AFTERV : Z := PML.PC_AFTER_VALUE.

Definition VISS : Z := PMS.PC_VIS_STRING.
Definition VISI : Z := PMS.PC_VIS_I64.
Definition VISU : Z := PMS.PC_VIS_U64.
Definition SCR : Z := CH.hd_scr G.HDECL.
Definition CONSTS : PSK.consts := PSK.CONSTS PML.VT_PARSER PML.VT_FUNC PML.VT_VISITOR 0x10000 0xf8000 0x10000 PML.IMG_RO_HI SCR [] 0.
Definition X0 : PSK.pexprs := SPT.X0 (ELit 17) (ELit 1).
Lemma kn0_eq : CC.cp_know G.cp0 = SPK.kn CONSTS false Pb Vb Eb (EVar 2) (EVar 33) X0.
Proof. vmc_refl. Qed.
Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma rets : forall pc, In pc GT.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[<-|[]]]; CL.solve_is_ret. Qed.

Abbreviation PE := SPT.PE.  Abbreviation CE := SPT.CE.

Definition is_end (j : nat) : bool := existsb (fun r : nat * nat * nat * Z => let '(j', _, _, p) := r in (Nat.eqb j' j && Z.eqb p AFTERV)%bool) G.RETS.
Definition SEND0 : expr := APC.eadd (EVar 38) (EVar 39).
Definition SCEND0 : expr := APC.eadd (EVar 38) (EVar 40).

Definition view_chk (cells : list kentry) : bool :=
  match SPA.pview_w cells Pb PE CE with
  | Some pv => (expr_eqb (PB4.pv_level pv) (EVar 41) && expr_eqb (PB4.pv_wend pv) (EVar 33) && expr_eqb (PB4.pv_wptr pv) (EVar 32) && expr_eqb (PB4.pv_st pv) (ELit 17)
                && expr_eqb (PB4.pv_sst pv) (EVar 43) && expr_eqb (PB4.pv_nst pv) (EVar 44) && expr_eqb (PB4.pv_more pv) (ELit 0) && expr_eqb (PB4.pv_done pv) (EVar 46)
                && expr_eqb (PB4.pv_size pv) (EVar 36) && expr_eqb (PB4.pv_sb pv) (EVar 38) && expr_eqb (PB4.pv_send pv) SEND0 && expr_eqb (PB4.pv_scend pv) SCEND0)%bool
  | None => false
  end.
Definition nxg2 (cj : CC.cutpoint) : nat := (CC.cp_nx cj - APC.NCS - 2)%nat.

Definition dec_chk (d : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  let '(vb, vk) := split_lit (nth 12 regs (ELit 0)) in
  if (expr_eqb (nth 10 regs (ELit 0)) (if Z.eqb d 0 then PE else APC.eaddz PE d) && expr_eqb (nth 11 regs (ELit 0)) (if Z.eqb d 0 then EVar 36 else APC.eaddz (EVar 36) (- d))
      && (Z.eqb d 0 || SPW.rng_in (SR.ps_cells ps) (EVar 36) 1 67108863) && expr_eqb vb (EVar 2) && CH2.blocks_eqb BLj BLi)%bool
  then match CH2.custom_chk GT.NF G.HDECL 16 2 BLi [(EVar 2, vk, ELit 8)] (SSU2.decu64_news (EVar 2) vk (nxg2 cj)) (Some (EVar (nxg2 cj))) c ps cj BLi with
       | Some ci => if (Z.leb (CH2.ci_csp ci) vk && Z.leb (vk + 8) 0 && Z.leb (- SCR) vk && Nat.eqb (CC.cp_nx cj) (CH2.ci_nx ci + 2 + APC.NCS) && Nat.leb GT.NF (CH2.ci_nx ci))%bool then Some ci else None
       | None => None end
  else None.
Definition vk_of (ps : SR.post_spec) : Z := snd (split_lit (nth 12 (CA.ps_reglist ps) (ELit 0))).
Definition stack_reg_eqb (r : SGP.region) : bool := let '(b, lo, len) := r in (expr_eqb b (EVar 2) && Z.eqb lo (- SCR) && expr_eqb len (ELit SCR))%bool.

Definition VIS_NEWS_S (nx : expr) : list kentry := [VSU.fl Vb 0 1; KWord (SA Vb 32) 8 PE; KWord (SA Vb 40) 8 nx].
Definition vis_chk_s (nx : expr) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in let cells := SR.ps_cells ps in
  let '(svb, svk) := split_lit (nth 11 regs (ELit 0)) in
  if (expr_eqb (nth 10 regs (ELit 0)) Vb && expr_eqb svb (EVar 2) && Z.leb (- SCR) svk && Z.leb (svk + 16) 0 && CH2.blocks_eqb BLj BLi
      && PB.has cells (KWord (SA Vb 0) 8 (ELit PML.VT_VISITOR)) && PB.has cells (KWord (SA (EVar 2) svk) 8 PE) && PB.has cells (KWord (SA (EVar 2) (svk + 8)) 8 nx))%bool
  then CH2.custom_chk GT.NF G.HDECL PMS.VIS_SCR 0 BLi [(Vb, 8, ELit 40)] (VIS_NEWS_S nx) (Some (ELit 1)) c ps cj BLi
  else None.
Definition vis_chk_v (flags : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (expr_eqb (nth 10 regs (ELit 0)) Vb && CH2.blocks_eqb BLj BLi && PB.has (SR.ps_cells ps) (KWord (SA Vb 0) 8 (ELit PML.VT_VISITOR)))%bool
  then CH2.custom_chk GT.NF G.HDECL PMS.VIS_SCR 0 BLi [(Vb, 8, ELit 40)] (VSU.val_news Vb 0 flags (nth 11 regs (ELit 0))) (Some (ELit 1)) c ps cj BLi
  else None.
Definition vis_chk_d (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (expr_eqb (nth 10 regs (ELit 0)) Vb && CH2.blocks_eqb BLj BLi && PB.has (SR.ps_cells ps) (KWord (SA Vb 0) 8 (ELit PML.VT_VISITOR)))%bool
  then CH2.custom_chk GT.NF G.HDECL PMS.VIS_SCR 1 BLi [(Vb, 8, ELit 40)] (VSU.dbl_news Vb 0 (CC.cp_nx cj - APC.NCS - 1)) (Some (ELit 1)) c ps cj BLi
  else None.
Definition vis_okb (o : option CH2.cinfo) (c : CC.cutpoint) : bool := match o with Some ci => Nat.leb (CC.cp_nx c) (CH2.ci_nx ci) | None => false end.
Definition vis_ok_v (flags : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : bool :=
  match vis_chk_v flags c ps cj BLi BLj with Some ci => (Nat.leb (CC.cp_nx c) (CH2.ci_nx ci) && APC.expr_vars_lt (CH2.ci_nx ci) (nth 11 (CA.ps_reglist ps) (ELit 0)))%bool | None => false end.
Definition vis_ok_d (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : bool :=
  match vis_chk_d c ps cj BLi BLj with Some ci => (Nat.leb (CC.cp_nx c) (CH2.ci_nx ci) && Nat.eqb (CC.cp_nx cj) (CH2.ci_nx ci + 1 + APC.NCS))%bool | None => false end.

Definition ev_chk_s (cells : list kentry) : bool :=
  (PB.has cells (VSU.fl Vb 0 1) && PB.has cells (KWord (SA Vb 32) 8 PE) &&
   (PB.has cells (KWord (SA Vb 40) 8 (EVar 36)) || (PB.has cells (KWord (SA Vb 40) 8 (ELit 0)) && PB.has cells (KRange (EVar 36) 0 0))))%bool.
Definition ev_chk_v (cells : list kentry) (flags : Z) : bool :=
  (PB.has cells (VSU.fl Vb 0 flags) && match CAX.cell_at cells Vb 32 8 with Some v => PB.has cells (KWord (SA Vb 32) 8 v) | None => false end)%bool.
Definition ev_any (cells : list kentry) : bool := (ev_chk_s cells || ev_chk_v cells 32 || ev_chk_v cells 16 || ev_chk_v cells 128)%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if (Z.eqb pc DECU64 || Z.eqb pc AFTERV || Z.eqb pc VISS || Z.eqb pc VISI || Z.eqb pc VISU)%bool then
        (Z.eqb (SR.ps_pc ps) pc && negb (is_end i) &&
         match CH2.ret_of G.RETS i k with
         | Some j => match nth_error G.CPS j with
                     | Some cj => let BLi := nth i G.BLS [] in let BLj := nth j G.BLS [] in
                                  if Z.eqb pc DECU64 then (negb (is_end j) && existsb (fun d => match dec_chk d c ps cj BLi BLj with Some _ => true | None => false end) [0; 1])%bool
                                  else if Z.eqb pc VISS then (negb (is_end j) && (vis_okb (vis_chk_s (EVar 36) c ps cj BLi BLj) c || vis_okb (vis_chk_s (ELit 0) c ps cj BLi BLj) c))%bool
                                  else if Z.eqb pc VISI then (negb (is_end j) && vis_ok_v 16 c ps cj BLi BLj)%bool
                                  else if Z.eqb pc VISU then (negb (is_end j) && vis_ok_v 32 c ps cj BLi BLj)%bool
                                  else (is_end j && CH2.blocks_eqb BLi SPT.BL0 && expr_eqb (nth 10 (CA.ps_reglist ps) (ELit 0)) Pb && expr_eqb (nth 11 (CA.ps_reglist ps) (ELit 0)) Eb && view_chk cells && PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) && PB.has cells (KWord (SA Vb 0) 8 (ELit PML.VT_VISITOR))
                                        && match PB2.ptrans_chk GT.NF G.HDECL Eb 0 Pb 0 512 11 c ps cj BLi BLj with Some _ => true | None => false end)%bool
                     | None => false end
         | None => false end)%bool
      else (is_end i && PB.exit_base_chk GT.NF pc c ps && existsb (Z.eqb pc) GT.ENDS && forallb stack_reg_eqb (CC.cp_F c) && ev_any cells)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Definition F0 : list SGP.region := [(EVar 2, - SCR, ELit SCR); (Pb, 0, ELit 272)].
Lemma foot_ok : CC.cps_all G.CPS (fun _ c => SP.F_sub (CC.cp_F c) F0) = true.
Proof. vmc_refl. Qed.
Lemma nf_all : CC.cps_all G.CPS (fun _ c => Nat.leb GT.NF (CC.cp_nx c)) = true.
Proof. vmc_refl. Qed.
Lemma end0 : is_end 0 = false.
Proof. vmc_refl. Qed.

Section Main.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis DECU64_OK : PMS.dec_u64_spec L.
Hypothesis AFTERV_OK : PMS.after_value_spec L HI.
Hypothesis VISS_OK : PMS.visit_string_spec L VISS.
Hypothesis VISI_OK : PMS.visit_i64_spec L VISI.
Hypothesis VISU_OK : PMS.visit_u64_spec L VISU.
Abbreviation SSCR := PML.STRTOD_SCR_V.
Abbreviation SCRC := (PMS.ENDNUM_SCR SSCR).

Variables (mw : option (Z * Z)) (LBo : list (Z * Z)) (cr : credit) (sp r P V E B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate).
Variables (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet).
Hypothesis HH : hi_heap HI (PML.ps_blocks ps ++ LBo) cr M (m_vmmaps model).
Hypothesis Hmo : PML.model_ok model.
Hypothesis HKnil : K [].
Hypothesis Hfp : PML.fp_ok fx.
Hypothesis Hentry : PML.entry L R M sp r SCRC.
Hypothesis Ha0 : PML.a0 R P.
Hypothesis Ha1 : PML.a1 R V.
Hypothesis Ha2 : PML.a2 R E.
Hypothesis Hmore : PML.ps_more ps = true.
Hypothesis Hst : PML.ps_st ps = PML.ST_NUMBER.
Hypothesis HPA : PML.parser_at M P (PML.ps_set_win ps mw).
Hypothesis HWF : PML.wf_ps_stale ps.
Hypothesis HLV : PMCUR.lvl_ok ps.
Hypothesis HWIN : PML.win_ok M LBo ps.
Hypothesis HBB : PMS.buf_bound_stale ps B.
Hypothesis HVIS : PML.vis_at M V.
Hypothesis HEC : PML.ec_at M E 0.
Hypothesis HLS : PML.ls_ok g M.
Hypothesis HG : g <> PML.LS0.
Hypothesis HPC : PML.pcredit_x L cr ps kx bx.
Hypothesis OP : PML.obj_on_stack L sp P 272.
Hypothesis OV : PML.obj_on_stack L sp V 48.
Hypothesis OE : PML.obj_on_stack L sp E 16.
Hypothesis AP1 : PML.apart P 272 V 48.
Hypothesis AP2 : PML.apart P 272 E 16.
Hypothesis AP3 : PML.apart V 48 E 16.

Definition AVREL (ps2 : PML.pstate) (code : Z) : Prop :=
  code = 0 /\ PML.ps_more ps2 = false /\ PML.ps_st ps2 = (if Z.eqb (PML.ps_level ps) 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\
  PML.ps_stack ps2 = PML.ps_stack ps /\ PML.ps_level ps2 = PML.ps_level ps /\ PML.ps_win ps2 = PML.ps_win ps.

Definition AVRELC (ps2 : PML.pstate) (code : Z) : Prop :=
  PMCUR.wf_c (PMCUR.ps_set_more ps2 true) /\ code = 0 /\ PML.ps_more ps2 = false /\ PML.ps_st ps2 = (if Z.eqb (PML.ps_level ps) 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\
  PML.ps_stack ps2 = PML.ps_stack ps /\ PML.ps_level ps2 = PML.ps_level ps /\ PML.ps_win ps2 = PML.ps_win ps /\
  PML.ps_bptr ps2 = PML.ps_bptr ps /\ length (PML.ps_buf ps2) = length (PML.ps_buf ps).

Hypothesis Hcont : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range),
   PML.fp_ok fx' ->
   (exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state),
      (PML.parser_at M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) /\ PMCUR.wf_c ps' /\ PML.win_ok M' LBo ps' /\ PML.buf_bound ps' B /\ PML.ec_at M' E code /\
      (code <> 0 -> PML.ps_more ps' = false) /\ PML.ls_ok g' M' /\ (g' = g \/ g' = PML.regJ g /\ code <> 0) /\
      LB' = PML.ps_blocks ps' ++ LBo /\ LBk = LBo /\ W = PMS.W_parc P V E /\ PML.pcredit_x L cr' ps' kx bx /\
      (AVREL ps' code \/ code = 19) /\ PMCUR.cur_post RSEGS ps ps' code M' V) ->
   regs_preserved R R' -> L5C.hpres L LBk sp SCRC W M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
   srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model') K.

Variables (line0 pos0 : Z).
Hypothesis Hline0 : PML.u64 M (P + 160) line0.
Hypothesis Hpos0 : PML.u64 M (P + 168) pos0.
Hypothesis Hlpr : 0 <= line0 < 2 ^ 64 /\ 0 <= pos0 < 2 ^ 64.

Let bcap := PML.ps_bcap ps.
Let bptr := PML.ps_bptr ps.
Let size0 := Z.of_nat (length (PML.ps_buf ps)).
Let sb := PML.ps_sb ps.
Let scap := PML.ps_scap ps.
Let slen := Z.of_nat (length (PML.ps_stack ps)).
Let level := PML.ps_level ps.
Definition E0 : env := SPT.E0 mw B ps R line0 pos0 [] SPT.noeb.

Lemma SCRV : CH.hd_scr G.HDECL = 576.
Proof. reflexivity. Qed.
Lemma SCRCV : SCRC = 9456.
Proof. reflexivity. Qed.
Lemma WFM : 0 <= level <= 1024 /\ In scap [66; 132; 264; 528; 1056].
Proof.
  destruct HWF as (Wn & n' & W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)). cbn [PML.ps_set_nst PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st] in *.
  destruct (W7 Hmore) as (W8 & W9 & _). split; [exact W9 | exact W4].
Qed.

Lemma INST : SPT.inst L HI mw LBo cr sp r P V E B kx bx g ps R M model SCRC G.HDECL Pb Vb Eb line0 pos0 [] SPT.noeb.
Proof.
  unfold SPT.inst. destruct Hlpr as (Q1 & Q2). pose proof WFM as (F1 & _). pose proof SCRCV as HSC.
  destruct Hentry as (_ & _ & Hsp & _ & Hstk). pose proof (L5C.stk_floor _ _ _ _ Hstk) as FL. pose proof Hstk as (S1 & S2 & S3 & S4 & S5).
  destruct OP as (OP1 & OP2 & OP3), OV as (OV1 & OV2 & OV3), OE as (OE1 & OE2 & OE3).
  split; [exact HIok|]. split; [exact LAY|]. split; [exact HH|]. split; [exact Hentry|]. split; [rewrite SCRV; lia|]. split; [lia|].
  split; [exact HPA|]. split; [exact HWF|]. split; [unfold level in *; lia|].
  split; [destruct HBB as (HB1 & HB2 & HB3); lia|].
  split; [rewrite Hst; unfold PML.ST_NUMBER; lia|].
  split; [exact HVIS|]. split; [exact HEC|]. split; [exact HLS|]. split; [exact HPC|].
  split; [exact (conj OP1 (conj OP2 OP3))|]. split; [exact (conj OV1 (conj OV2 OV3))|]. split; [exact (conj OE1 (conj OE2 OE3))|]. split; [exact AP1|]. split; [exact AP2|]. split; [exact AP3|].
  split; [exact Hline0|]. split; [exact Hpos0|]. split; [exact Q1|]. split; [exact Q2|].
  split; [unfold PB.uv, Pb; cbn [edenot]; rewrite (SPT.EV0 mw B ps R line0 pos0 [] SPT.noeb 10%bv), Ha0; apply u64_of_Z; lia|].
  split; [unfold PB.uv, Vb; cbn [edenot]; rewrite (SPT.EV0 mw B ps R line0 pos0 [] SPT.noeb 11%bv), Ha1; apply u64_of_Z; lia|].
  split; [unfold PB.uv, Eb; cbn [edenot]; rewrite (SPT.EV0 mw B ps R line0 pos0 [] SPT.noeb 12%bv), Ha2; apply u64_of_Z; lia|].
  split; [reflexivity|]. split; reflexivity.
Qed.
Notation kit X := (X L HI mw LBo cr sp r P V E B kx bx g ps R M model SCRC G.HDECL Pb Vb Eb line0 pos0 [] SPT.noeb INST) (only parsing).

Lemma At0 : CC.At RSEGS G.cp0 E0 R M.
Proof.
  split; [exact (regs_ok_id R _ _)|]. rewrite kn0_eq.
  apply (kit SPT.kn_ok CONSTS (ELit 17) (ELit 1) eq_refl eq_refl eq_refl (conj eq_refl eq_refl) (conj eq_refl eq_refl) eq_refl).
  - rewrite PB2.uv_lit by lia. rewrite Hst. reflexivity.
  - rewrite PB2.uv_lit by lia. rewrite Hmore. reflexivity.
Qed.

Definition W : list L5.range := PMS.W_parc P V E.
Definition STKF := kit SPT.STKF.
Definition SCRP := kit SPT.SCRP.
Lemma NF32 : (32 <= GT.NF)%nat.
Proof. unfold GT.NF. lia. Qed.
Definition U2 : bv_unsigned (ev E0 2) = sp := kit SPT.U2.
Definition TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L) := kit SPT.TP0.
Definition W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a := kit SPT.W_OK.
Lemma CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a).
Proof. intros rg [<-|[]]. apply (kit SPT.CRS_OK 0 0 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl eq_refl). left. reflexivity. Qed.
Lemma WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a).
Proof. intros rg Hin. apply (kit SPT.WRS_OK). exact Hin. Qed.
Lemma IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Proof. intros rg a Hin. apply (kit SPT.IMG_OK). exact Hin. Qed.
Definition DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL) := kit SPT.DEF0.
Definition FRZ := kit SPT.FRZ.

Definition bcap_of (i : nat) (E1 : env) : Z := snd (nth 0 (CH2.den E1 (nth i G.BLS [])) (0, 0)).
Definition scap_of (i : nat) (E1 : env) : Z := snd (nth 1 (CH2.den E1 (nth i G.BLS [])) (0, 0)).
Definition Cred (i : nat) (E1 : env) (cr1 : credit) : Prop := PPS.bufcred L cr1 (bcap_of i E1) (PPS.stk_kx L (scap_of i E1) + kx) (PPS.stk_bx L (scap_of i E1) + bx).
Lemma CRED_BLK : forall i j E1 E2 cr1, CH2.den E2 (nth j G.BLS []) = CH2.den E1 (nth i G.BLS []) -> Cred i E1 cr1 -> Cred j E2 cr1.
Proof. intros i j E1 E2 cr1 Hd H. unfold Cred, bcap_of, scap_of in *. rewrite Hd. exact H. Qed.
Lemma cred_pc : forall i E1 cr1 ps1, CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps1 -> In (PML.ps_scap ps1) [66; 132; 264; 528; 1056] -> (Cred i E1 cr1 <-> PML.pcredit_x L cr1 ps1 kx bx).
Proof.
  intros i E1 cr1 ps1 Hd Hs. unfold Cred, bcap_of, scap_of. rewrite Hd. cbn [PML.ps_blocks nth snd].
  destruct HPC as (K0 & B0 & _). symmetry. exact (PPS.pcredit_x_bufcred L cr1 ps1 kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) Hs K0 B0).
Qed.

Definition XLOW (M1 : mem) : Prop := forall a, 0 <= a < hl_ceil L -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Definition XEND (i : nat) (E1 : env) (M1 : mem) : Prop := exists ps2 code g',
  (PML.parser_at M1 P (PML.ps_set_win ps2 mw) /\ PML.ps_win ps2 = PML.ps_win ps) /\ PMCUR.wf_c ps2 /\ PML.win_ok M1 LBo ps2 /\ PML.buf_bound ps2 B /\ PML.ec_at M1 E code /\
  (code <> 0 -> PML.ps_more ps2 = false) /\ PML.ls_ok g' M1 /\ (g' = g \/ (g' = PML.regJ g /\ code <> 0)) /\ AVRELC ps2 code /\ CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps2.
Definition XI (i : nat) (E1 : env) (M1 : mem) : Prop := if is_end i then XEND i E1 M1 else XLOW M1.

Abbreviation HAMB := (CH2.heap_amb L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred).
Abbreviation AMB3 := (CH2.amb3 L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred XI).
Abbreviation is_leaf := (CH2.is_leaf G.CPS G.TAGS).
Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.

Lemma below_frame : forall i c E' (M1 M' : mem), nth_error G.CPS i = Some c -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' (CC.cp_F c) a -> M' a = M1 a) -> forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof. intros i c E' M1 M' Hc Hag HF. exact (kit SPT.below_frame (CC.cp_F c) E' M1 M' (CC.cps_all_sound _ _ foot_ok i c Hc) Hag HF). Qed.
Lemma leaf_know : forall c ps1 E' R' (M1 M' : mem), CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' -> know_ok RSEGS E' M' (SR.ps_cells ps1).
Proof. intros c ps1 E' R' M1 M' HLF. unfold know_ok. apply Forall_forall. intros X HX. rewrite <- LS. exact (CC.lf_cells _ _ _ _ _ _ _ HLF X HX). Qed.
Lemma foot_low : forall a, PB2.ls_foot a -> 0 <= a < hl_ceil L.
Proof. intros a Ha. pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). unfold PB2.ls_foot, PML.IMG_RO_HI in Ha. unfold hl_ceil. lia. Qed.
Lemma amb_agree : forall i E1 (M1 : mem) model1, HAMB i E1 M1 model1 -> env_agree GT.NF E0 E1.
Proof. intros i E1 M1 model1 (_ & _ & X & _). exact X. Qed.
Lemma xlow_tr : forall (M1 M' : mem), (forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> XLOW M1 -> XLOW M'.
Proof. intros M1 M' H X a Ha. rewrite (H a Ha). exact (X a Ha). Qed.
Lemma xi_low : forall i E1 (M1 : mem), is_end i = false -> XI i E1 M1 -> XLOW M1.
Proof. intros i E1 M1 Hi HX. unfold XI in HX. rewrite Hi in HX. exact HX. Qed.
Lemma xlow_ls : forall (M1 : mem), XLOW M1 -> PML.ls_ok g M1.
Proof. intros M1 X. apply (PB2.ls_ok_keep M M1); [|exact HG | exact HLS]. intros a Ha. exact (X a (foot_low a Ha)). Qed.
Lemma xlow_bytes : forall (M1 : mem) b n (bs : list Z), XLOW M1 -> 0 <= b -> b + n <= hl_ceil L -> Z.of_nat (length bs) <= n -> L5.bytes_at RSEGS M b bs -> L5.bytes_at RSEGS M1 b bs.
Proof. intros M1 b n bs X H0 H1 H2 HB. exact (kit SPT.bytes_below M M1 b n bs X H0 H1 H2 HB). Qed.
Lemma low_frame : forall (M1 M2 : mem) spc scr (Wz : list L5.range), L5.frame_but ((spc - scr, scr) :: Wz) M1 M2 -> hl_ceil L <= spc - scr -> (forall w, In w Wz -> hl_ceil L <= fst w) ->
  forall a, 0 <= a < hl_ceil L -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof.
  intros M1 M2 spc scr Wz HFB Hs HW a Ha. pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). apply HFB. rewrite L5.unsigned_lit by (unfold hl_ceil in *; lia).
  intros rg [<-|Hin]; unfold L5.in_rng; cbn [fst snd]; [lia | specialize (HW _ Hin); lia].
Qed.

Lemma amb_def_own : forall i E1 (M1 : mem) model1 a n, HAMB i E1 M1 model1 -> sp - SCR <= a -> a + n <= sp -> L5.defined M1 a n.
Proof.
  intros i E1 M1 model1 a n (_ & _ & _ & _ & _ & Hdf) H0 H1 q Hq. pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). pose proof SCRV as HV. pose proof SCRCV as HC. unfold SCR in *.
  apply Hdf; [lia | | replace (a + q) with (sp - CH.hd_scr G.HDECL + (a + q - (sp - CH.hd_scr G.HDECL))) by lia; apply DEF0; rewrite HV; lia]. split; [right; left; unfold hl_ceil in *; split; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); unfold hl_ceil in *; lia].
Qed.
Lemma retEx_a1 : forall E' nx ghosts R2, ev (CH2.retEx E' nx ghosts R2) (nx + length ghosts + 5) = getr R2 11%bv.
Proof. intros E' nx ghosts R2. unfold CH2.retEx, CH2.retE. rewrite APS.ext_list_at by (clear; cbn; lia). cbn [APC.caller_saved map nth]. f_equal. Qed.
Lemma reg_arg : forall E' (R' : bvmap 5 word) regs (x : reg) q e z, regs_ok E' regs R' -> q = ridx x -> bv_eqb x 0 = false -> nth q regs (ELit 0) = e -> uv E' e = z -> getr R' x = Z_to_bv 64 z.
Proof.
  intros E' R' regs x q e z HRL -> Hx0 He Hz. rewrite (HRL x). unfold sr_get. rewrite Hx0. rewrite He. rewrite <- Hz. unfold PB.uv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma leaf_dec : forall i c k ps1 j cj d ci, is_leaf i c k ps1 (CC.TOther DECU64) -> is_end i = false -> is_end j = false -> CH2.ret_of G.RETS i k = Some j -> nth_error G.CPS j = Some cj ->
  SR.ps_pc ps1 = DECU64 -> In d [0; 1] -> dec_chk d c ps1 cj (nth i G.BLS []) (nth j G.BLS []) = Some ci -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 j cj d ci IL Hi Hj Hret Hcj Hpc Hd Hchk. unfold dec_chk in Hchk.
  destruct (split_lit (nth 12 (CA.ps_reglist ps1) (ELit 0))) as [vb vk] eqn:Hsplit.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb HBL]. apply andb_prop in Hb as [Hb Hvb]. apply andb_prop in Hb as [Hb Hsz]. apply andb_prop in Hb as [Ha0e Ha1e]. apply expr_eqb_eq in Ha0e, Ha1e, Hvb. subst vb.
  destruct (CH2.custom_chk GT.NF G.HDECL 16 2 (nth i G.BLS []) [(EVar 2, vk, ELit 8)] (SSU2.decu64_news (EVar 2) vk (nxg2 cj)) (Some (EVar (nxg2 cj))) c ps1 cj (nth i G.BLS [])) as [ci0|] eqn:Hcc; [|discriminate].
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb2; [|discriminate] end. injection Hchk as ->.
  apply andb_prop in Hb2 as [Hb2 Hnf]. apply andb_prop in Hb2 as [Hb2 Hnx]. apply andb_prop in Hb2 as [Hb2 Hlo]. apply andb_prop in Hb2 as [Hcsp Hhi].
  apply Z.leb_le in Hcsp, Hhi, Hlo. apply Nat.eqb_eq in Hnx. apply Nat.leb_le in Hnf.
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  assert (Hnxv : nxg2 cj = CH2.ci_nx ci) by (unfold nxg2; rewrite Hnx; lia).
  rewrite Hnxv in Hcc.
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). pose proof SCRV as HSV. pose proof SCRCV as HSC. unfold SCR in Hlo. rewrite HSV in Hlo.
  assert (ES2 : forall Ex, env_agree GT.NF E0 Ex -> forall q, estart Ex (SA (EVar 2) q) = sp + q).
  { intros Ex Hx q. destruct (FRZ Ex Hx) as (G2 & _). unfold estart. cbn [a_base a_off]. fold (uv Ex (EVar 2)). rewrite G2. reflexivity. }
  apply (SPC2.pure_leaf_own_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K XI DEF0 CRED_BLK
           DECU64 16 2%nat [(EVar 2, vk, ELit 8)] (SSU2.decu64_news (EVar 2) vk (CH2.ci_nx ci)) (Some (EVar (CH2.ci_nx ci))) [(sp + vk, 8)] i c k ps1 j cj ci IL Hret Hcj Hpc Hcc HBL).
  - intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. right. left. rewrite HSV. lia.
  - intros E' HagE' w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (EVar 2, vk, ELit 8). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite (ES2 E' HagE' vk). unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp' HFP Hmh Hml RET.
    pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
    assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame i c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
    pose proof (xlow_tr M1 M' HLOW (xi_low i E1 M1 Hi HX)) as HXL.
    destruct (FRZ E' HagE') as (G2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & G36 & _ & _ & _ & _ & _ & GPE & _).
    pose proof (kit SPT.NUM) as ((B0 & B1 & B2 & B3 & B4) & BR2 & BD1 & BD2 & A1 & Hk & N1 & N2 & _). fold bptr bcap size0 in B0, B4, BD1, N2.
    assert (Hsz1 : d = 1 -> 1 <= size0).
    { intros ->. cbn [Z.eqb orb] in Hsz. pose proof (SPW.rng_in_sound E' M' _ _ _ _ HK Hsz) as Q. rewrite G36 in Q. lia. }
    assert (Hd01 : d = 0 \/ d = 1) by (cbn [In] in Hd; lia).
    assert (Ua0 : uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0)) = bptr + d).
    { rewrite Ha0e. destruct Hd01 as [-> | ->]; cbn [Z.eqb]; [rewrite GPE; lia|]. rewrite PB.uv_eaddz, GPE. unfold hl_ceil in *. apply Z.mod_small. lia. }
    assert (Ua1 : uv E' (nth 11 (CA.ps_reglist ps1) (ELit 0)) = size0 - d).
    { rewrite Ha1e. destruct Hd01 as [-> | ->]; cbn [Z.eqb]; [rewrite G36; lia|]. rewrite PB.uv_eaddz, G36. specialize (Hsz1 eq_refl). apply Z.mod_small. unfold size0 in *. lia. }
    assert (Ua2 : uv E' (nth 12 (CA.ps_reglist ps1) (ELit 0)) = sp + vk).
    { pose proof (APS.split_lit_denot E' _ _ _ Hsplit) as Q. unfold PB.uv. rewrite Q. fold (uv E' (EVar 2)). rewrite G2. apply u64_of_Z. lia. }
    assert (Hsize : size0 < 2 ^ 26) by (destruct HBB as (HB1 & HB2 & HB3); unfold size0; lia).
    destruct Hent as (Hra' & Hraok' & Hsp' & Htp' & Hstk'). pose proof (L5C.stk_window _ _ _ _ Hstk') as (SW1 & _).
    apply (DECU64_OK (bptr + d) (size0 - d) (sp + vk) (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model1 K Hmh Hml HKnil HFP).
    { split; [exact (conj Hra' (conj Hraok' (conj Hsp' (conj Htp' Hstk'))))|].
      split; [exact (reg_arg E' R' _ 10%bv 10%nat _ _ HRL eq_refl eq_refl eq_refl Ua0)|]. split; [exact (reg_arg E' R' _ 11%bv 11%nat _ _ HRL eq_refl eq_refl eq_refl Ua1)|].
      split; [exact (reg_arg E' R' _ 12%bv 12%nat _ _ HRL eq_refl eq_refl eq_refl Ua2)|].
      split; [destruct Hd01 as [-> | ->]; [unfold size0; lia | specialize (Hsz1 eq_refl); lia]|].
      split; [intros q Hq; rewrite (HXL (bptr + d + q) ltac:(lia)); replace (bptr + d + q) with (bptr + (d + q)) by lia; apply BD1; lia|].
      split; [apply (amb_def_own i E1 M' model1 (sp + vk) 8 HA'); unfold SCR; rewrite ?HSV; lia|].
      split; [lia|]. split; [lia|]. split; [exact (proj1 (xlow_ls M' HXL))|]. split; lia. }
    intros fx2 R2 M2 HFP2 (q & cc & Hq & Hcc' & Hcin) HRP HFB HGR.
    assert (HdV : L5.defined M2 (sp + vk) (Z.of_nat 8)) by (intros t Ht; apply HGR; apply (amb_def_own i E1 M' model1 (sp + vk) 8 HA'); [unfold SCR; rewrite ?HSV; lia | lia | exact Ht]).
    destruct (PB2.cell_exists M2 (sp + vk) 8 ltac:(lia) HdV) as (v & Rv & Hv).
    set (E2 := CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 q; Z_to_bv 64 v] R2).
    assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [apply CH2.retEx_agree | exact Hnf]]).
    assert (GG0 : ev E2 (CH2.ci_nx ci) = Z_to_bv 64 q).
    { pose proof (CH2.retEx_ghost E' (CH2.ci_nx ci) [Z_to_bv 64 q; Z_to_bv 64 v] R2 0 ltac:(cbn; lia)) as GG. rewrite Nat.add_0_r in GG. exact GG. }
    assert (GG1 : ev E2 (CH2.ci_nx ci + 1) = Z_to_bv 64 v) by exact (CH2.retEx_ghost E' (CH2.ci_nx ci) [Z_to_bv 64 q; Z_to_bv 64 v] R2 1 ltac:(cbn; lia)).
    apply (RET fx2 R2 M2 [Z_to_bv 64 q; Z_to_bv 64 v] eq_refl HFP2 HRP HFB HGR).
    + cbn [edenot]. fold E2. rewrite GG0. exact Hq.
    + fold E2. intros X [<-|[<-|[]]].
      * rewrite LS. eapply CL5.kword64_intro with (A := sp + vk) (z := v); [exact (ES2 E2 HagE2 vk) | lia | lia | cbn [edenot]; exact GG1 | exact Hv].
      * unfold SSU2.a1var. cbn [kentry_ok edenot]. pose proof (retEx_a1 E' (CH2.ci_nx ci) [Z_to_bv 64 q; Z_to_bv 64 v] R2) as Q. cbn [length] in Q. fold E2 in Q. rewrite Q, Hcc'.
        cbn [In] in Hcin. rewrite u64_of_Z by lia. lia.
    + intros _. unfold XI. rewrite Hj. apply (xlow_tr M' M2); [|exact HXL].
      apply (low_frame M' M2 (sp + CH2.ci_csp ci) 16 [(sp + vk, 8)] HFB ltac:(lia)). intros w [<-|[]]. cbn [fst]. lia.
Qed.

Lemma u64_transfer : forall (M1 M2 : mem) a b p q, L5.u64_at RSEGS M1 a p -> L5.u64_at RSEGS M1 a q -> L5.u64_at RSEGS M2 b p -> L5.u64_at RSEGS M2 b q.
Proof. unfold L5.u64_at. intros M1 M2 a b p q H1 H2 H3. rewrite H1 in H2. rewrite H3. exact H2. Qed.
Lemma z2bv_add : forall a b k, Z_to_bv 64 a = Z_to_bv 64 b -> Z_to_bv 64 (a + k) = Z_to_bv 64 (b + k).
Proof.
  intros a b k H. apply bv_eq. rewrite !Z_to_bv_unsigned. apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H.
  rewrite <- (bv_wrap_add_idemp_l 64 a k), H, bv_wrap_add_idemp_l. reflexivity.
Qed.
Lemma nv36 : forall Ex, env_agree GT.NF E0 Ex -> uv Ex (EVar 36) = size0.
Proof. intros Ex Hx. destruct (FRZ Ex Hx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G36 & _). exact G36. Qed.
Lemma nv0 : forall Ex, env_agree GT.NF E0 Ex -> uv Ex (ELit 0) = 0.
Proof. intros Ex _. apply PB2.uv_lit. lia. Qed.
Lemma nr36 : 0 <= size0 < 2 ^ 64.
Proof. destruct HBB as (HB1 & HB2 & HB3). unfold size0 in *. lia. Qed.
Lemma vis_evs : forall (M2 : mem) p n, PMCUR.ev_at RSEGS M2 V (PMCUR.EvStr p n) -> L5.u64_at RSEGS M2 (V + 8) 1 /\ L5.u64_at RSEGS M2 (V + 32) p /\ L5.u64_at RSEGS M2 (V + 40) n.
Proof. intros M2 p n (_ & H). exact H. Qed.
Lemma vis_evu : forall (M2 : mem) x, PMCUR.ev_at RSEGS M2 V (PMCUR.EvU64 x) -> L5.u64_at RSEGS M2 (V + 8) 32 /\ L5.u64_at RSEGS M2 (V + 32) x.
Proof. intros M2 x (_ & H). exact H. Qed.
Lemma vis_evi : forall (M2 : mem) x, PMCUR.ev_at RSEGS M2 V (PMCUR.EvI64 x) -> L5.u64_at RSEGS M2 (V + 8) 16 /\ L5.u64_at RSEGS M2 (V + 32) x.
Proof. intros M2 x (_ & H). exact H. Qed.
Lemma vis_evd : forall (M2 : mem) x, PMCUR.ev_at RSEGS M2 V (PMCUR.EvDbl x) -> L5.u64_at RSEGS M2 (V + 8) 128 /\ L5.u64_at RSEGS M2 (V + 32) x.
Proof. intros M2 x (_ & H). exact H. Qed.
Lemma leaf_vis_s : forall (nx : expr) (nv : Z), (forall Ex, env_agree GT.NF E0 Ex -> uv Ex nx = nv) -> 0 <= nv < 2 ^ 64 ->
  forall i c k ps1 j cj ci, is_leaf i c k ps1 (CC.TOther VISS) -> is_end i = false -> is_end j = false -> CH2.ret_of G.RETS i k = Some j -> nth_error G.CPS j = Some cj ->
  SR.ps_pc ps1 = VISS -> vis_chk_s nx c ps1 cj (nth i G.BLS []) (nth j G.BLS []) = Some ci -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros nx nv Hnv Hnr i c k ps1 j cj ci IL Hi Hj Hret Hcj Hpc Hchk Hnx. unfold vis_chk_s in Hchk.
  destruct (split_lit (nth 11 (CA.ps_reglist ps1) (ELit 0))) as [svb svk] eqn:Hsplit.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb Hsl]. apply andb_prop in Hb as [Hb Hsd]. apply andb_prop in Hb as [Hb Hvt]. apply andb_prop in Hb as [Hb HBL].
  apply andb_prop in Hb as [Hb Hk2]. apply andb_prop in Hb as [Hb Hk1]. apply andb_prop in Hb as [Ha0e Hsvb]. apply expr_eqb_eq in Ha0e, Hsvb. apply Z.leb_le in Hk1, Hk2. subst svb.
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  pose proof (CC.cps_all_sound _ _ nf_all i c Hc) as HNF. cbv beta in HNF. apply Nat.leb_le in HNF.
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). pose proof OV as (OV1 & OV2 & OV3). pose proof SCRV as HSV. unfold SCR in Hk1. rewrite HSV in Hk1.
  assert (ESV : forall Ex, env_agree GT.NF E0 Ex -> forall q, estart Ex (SA Vb q) = V + q).
  { intros Ex Hx q. destruct (FRZ Ex Hx) as (_ & _ & _ & GV & _). unfold estart. cbn [a_base a_off]. fold (uv Ex Vb). rewrite GV. reflexivity. }
  assert (ESS : forall Ex, env_agree GT.NF E0 Ex -> forall q, estart Ex (SA (EVar 2) q) = sp + q).
  { intros Ex Hx q. destruct (FRZ Ex Hx) as (G2x & _). unfold estart. cbn [a_base a_off]. fold (uv Ex (EVar 2)). rewrite G2x. reflexivity. }
  assert (ELN : forall Ex z, 0 <= z < 2 ^ 64 -> elenZ Ex (ELit z) = z) by (intros Ex z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K XI DEF0 CRED_BLK
           VISS PMS.VIS_SCR 0%nat [(Vb, 8, ELit 40)] (VIS_NEWS_S nx) (Some (ELit 1)) [(V + 8, 40)] i c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
  - intros w a [<-|[]] Hin. exists (V + 8, 40). split; [unfold W, PMS.W_parc, PML.W_par; cbn [app]; right; right; right; right; left; reflexivity | exact Hin].
  - intros E' HagE' w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (Vb, 8, ELit 40). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite (ESV E' HagE' 8), (ELN E' 40 ltac:(lia)). lia.
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
    destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & G42 & G43 & G44 & G45 & G46 & G36 & G38 & G39 & G40 & GSE & GSC & GPE & GCE & G32 & G33 & _).
    assert (Ra0 : PML.a0 R' V).
    { unfold PML.a0. rewrite (HRL 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Ha0e.
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' Vb)). fold (uv E' Vb). rewrite GV. reflexivity. }
    assert (Usv : uv E' (nth 11 (CA.ps_reglist ps1) (ELit 0)) = sp + svk).
    { pose proof (APS.split_lit_denot E' _ _ _ Hsplit) as Q. unfold PB.uv. rewrite Q. fold (uv E' (EVar 2)). rewrite G2. apply u64_of_Z. lia. }
    pose proof (reg_arg E' R' _ 11%bv 11%nat _ (sp + svk) HRL eq_refl eq_refl eq_refl Usv) as Ra1.
    assert (HSD : L5.u64_at RSEGS M' (sp + svk) bptr).
    { pose proof (PB2.kword64_elim E' M' _ _ (sp + svk) (PB.has_ok E' M' _ _ HK Hsd) (ESS E' HagE' svk)) as T. rewrite GPE in T. exact T. }
    assert (HSL : L5.u64_at RSEGS M' (sp + svk + 8) nv).
    { assert (Q : estart E' (SA (EVar 2) (svk + 8)) = sp + svk + 8) by (rewrite (ESS E' HagE'); lia).
      pose proof (PB2.kword64_elim E' M' _ _ (sp + svk + 8) (PB.has_ok E' M' _ _ HK Hsl) Q) as T. rewrite (Hnv E' HagE') in T. exact T. }
    assert (HVT : PML.u64 M' V PML.VT_VISITOR).
    { pose proof (PB2.kword64_elim E' M' _ _ V (PB.has_ok E' M' _ _ HK Hvt)) as T. rewrite PB2.uv_lit in T by (unfold PML.VT_VISITOR; lia). apply T. rewrite (ESV E' HagE' 0). lia. }
    assert (HdV' : L5.defined M' V 48) by (apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 V 48 HA' (proj2 HVIS)); left; lia).
    assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame i c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
    apply (VISS_OK V (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model1 K Hmh Hml HKnil HFP).
    { split; [exact Hent|]. split; [exact Ra0|]. split; [split; [exact HVT | exact HdV']|]. split; [unfold PML.obj_on_stack; repeat split; lia|].
      exists (sp + svk), bptr, nv. split; [exact Ra1|]. split; [exact HSD|]. split; [exact HSL|]. lia. }
    intros fx2 R2 M2 HFP2 (Ha0' & e & (sv & p & n & Hsv1 & Hp & Hn & ->) & Hev) HRP HFB HGR.
    assert (Wsv : Z_to_bv 64 sv = Z_to_bv 64 (sp + svk)) by (unfold PML.a1 in Hsv1; rewrite <- Hsv1; exact Ra1).
    assert (Hp' : L5.u64_at RSEGS M' (sp + svk) p) by (unfold PML.u64, L5.u64_at in Hp |- *; rewrite <- Wsv; exact Hp).
    assert (Hn' : L5.u64_at RSEGS M' (sp + svk + 8) n) by (unfold PML.u64, L5.u64_at in Hn |- *; rewrite <- (z2bv_add sv (sp + svk) 8 Wsv); exact Hn).
    destruct (vis_evs M2 p n Hev) as (H8 & H32 & H40).
    pose proof (u64_transfer M' M2 _ _ p bptr Hp' HSD H32) as H32s. pose proof (u64_transfer M' M2 _ _ n nv Hn' HSL H40) as H40s.
    set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
    assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [apply CH2.retEx_agree | lia]]).
    assert (HLOW2 : forall a, 0 <= a < hl_ceil L -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
    { destruct Hent as (_ & _ & _ & _ & Hstk'). pose proof (L5C.stk_window _ _ _ _ Hstk') as (SW1 & _).
      intros a Ha. apply HFB. rewrite L5.unsigned_lit by (unfold hl_ceil in *; lia). intros rg [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; unfold hl_ceil, PMS.VIS_SCR in *; lia. }
    apply (RET fx2 R2 M2 [] eq_refl HFP2 HRP HFB HGR).
    + cbn [edenot]. unfold PML.a0 in Ha0'. exact Ha0'.
    + intros X HXin. destruct (FRZ E2 HagE2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GPE2 & _). rewrite LS.
      unfold VIS_NEWS_S, VSU.fl in HXin. destruct HXin as [<-|[<-|[<-|[]]]].
      * eapply CL5.kword64_intro with (A := V + 8) (z := 1); [rewrite (ESV E2 HagE2); lia | lia | lia | reflexivity | exact H8].
      * eapply CL5.kword64_intro with (A := V + 32) (z := bptr); [rewrite (ESV E2 HagE2); lia | lia | lia | exact (PB.edenot_of_uv E2 _ _ GPE2) | exact H32s].
      * eapply CL5.kword64_intro with (A := V + 40) (z := nv); [rewrite (ESV E2 HagE2); lia | lia | lia | exact (PB.edenot_of_uv E2 _ _ (Hnv E2 HagE2)) | exact H40s].
    + intros _. unfold XI. rewrite Hj. unfold XI in HX. rewrite Hi in HX. intros a Ha. rewrite (HLOW2 a Ha), (HLOW a Ha). exact (HX a Ha).
Qed.
Lemma leaf_vis_v : forall (vpc flags : Z) (mk : Z -> PMCUR.sevent), PMS.visit_spec L vpc (fun _ _ => True) (fun R _ e => exists x, PML.a1 R x /\ e = mk x) ->
  (forall (M2 : mem) x, PMCUR.ev_at RSEGS M2 V (mk x) -> L5.u64_at RSEGS M2 (V + 8) flags /\ L5.u64_at RSEGS M2 (V + 32) x) -> 0 <= flags < 2 ^ 64 ->
  forall i c k ps1 j cj ci, is_leaf i c k ps1 (CC.TOther vpc) -> is_end i = false -> is_end j = false -> CH2.ret_of G.RETS i k = Some j -> nth_error G.CPS j = Some cj ->
  SR.ps_pc ps1 = vpc -> vis_chk_v flags c ps1 cj (nth i G.BLS []) (nth j G.BLS []) = Some ci -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
  APC.expr_vars_lt (CH2.ci_nx ci) (nth 11 (CA.ps_reglist ps1) (ELit 0)) = true ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros vpc flags mk VIS_OK HMK Hfr i c k ps1 j cj ci IL Hi Hj Hret Hcj Hpc Hchk Hnx Hvl. unfold vis_chk_v in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb Hvt]. apply andb_prop in Hb as [Ha0e HBL]. apply expr_eqb_eq in Ha0e.
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  pose proof (CC.cps_all_sound _ _ nf_all i c Hc) as HNF. cbv beta in HNF. apply Nat.leb_le in HNF.
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). pose proof OV as (OV1 & OV2 & OV3).
  assert (ESV : forall Ex, env_agree GT.NF E0 Ex -> forall q, estart Ex (SA Vb q) = V + q).
  { intros Ex Hx q. destruct (FRZ Ex Hx) as (_ & _ & _ & GV & _). unfold estart. cbn [a_base a_off]. fold (uv Ex Vb). rewrite GV. reflexivity. }
  assert (ELN : forall Ex z, 0 <= z < 2 ^ 64 -> elenZ Ex (ELit z) = z) by (intros Ex z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K XI DEF0 CRED_BLK
           vpc PMS.VIS_SCR 0%nat [(Vb, 8, ELit 40)] (VSU.val_news Vb 0 flags (nth 11 (CA.ps_reglist ps1) (ELit 0))) (Some (ELit 1)) [(V + 8, 40)] i c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
  - intros w a [<-|[]] Hin. exists (V + 8, 40). split; [unfold W, PMS.W_parc, PML.W_par; cbn [app]; right; right; right; right; left; reflexivity | exact Hin].
  - intros E' HagE' w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (Vb, 8, ELit 40). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite (ESV E' HagE' 8), (ELN E' 40 ltac:(lia)). lia.
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
    destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & _).
    assert (Ra0 : PML.a0 R' V).
    { unfold PML.a0. rewrite (HRL 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Ha0e.
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' Vb)). fold (uv E' Vb). rewrite GV. reflexivity. }
    assert (Ga1 : getr R' 11%bv = edenot E' (nth 11 (CA.ps_reglist ps1) (ELit 0))).
    { rewrite (HRL 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. reflexivity. }
    assert (HVT : PML.u64 M' V PML.VT_VISITOR).
    { pose proof (PB2.kword64_elim E' M' _ _ V (PB.has_ok E' M' _ _ HK Hvt)) as T. rewrite PB2.uv_lit in T by (unfold PML.VT_VISITOR; lia). apply T. rewrite (ESV E' HagE' 0). lia. }
    assert (HdV' : L5.defined M' V 48) by (apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 V 48 HA' (proj2 HVIS)); left; lia).
    assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame i c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
    apply (VIS_OK V (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model1 K Hmh Hml HKnil HFP).
    { split; [exact Hent|]. split; [exact Ra0|]. split; [split; [exact HVT | exact HdV']|]. split; [unfold PML.obj_on_stack; repeat split; lia | exact I]. }
    intros fx2 R2 M2 HFP2 (Ha0' & e & (x & Hx1 & ->) & Hev) HRP HFB HGR.
    destruct (HMK M2 x Hev) as (H8 & H32).
    set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
    assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [apply CH2.retEx_agree | lia]]).
    assert (Hval : edenot E2 (nth 11 (CA.ps_reglist ps1) (ELit 0)) = Z_to_bv 64 x).
    { rewrite <- (SR.edenot_agree_AP (CH2.ci_nx ci) E' E2 _ (CH2.retEx_agree _ _ _ _) Hvl). rewrite <- Ga1. exact Hx1. }
    assert (HLOW2 : forall a, 0 <= a < hl_ceil L -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
    { destruct Hent as (_ & _ & _ & _ & Hstk'). pose proof (L5C.stk_window _ _ _ _ Hstk') as (SW1 & _).
      intros a Ha. apply HFB. rewrite L5.unsigned_lit by (unfold hl_ceil in *; lia). intros rg [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; unfold hl_ceil, PMS.VIS_SCR in *; lia. }
    apply (RET fx2 R2 M2 [] eq_refl HFP2 HRP HFB HGR).
    + cbn [edenot]. unfold PML.a0 in Ha0'. exact Ha0'.
    + intros X HXin. rewrite LS. unfold VSU.val_news, VSU.fl in HXin. destruct HXin as [<-|[<-|[]]].
      * eapply CL5.kword64_intro with (A := V + 8) (z := flags); [rewrite (ESV E2 HagE2); lia | lia | lia | reflexivity | exact H8].
      * eapply CL5.kword64_intro with (A := V + 32) (z := x); [rewrite (ESV E2 HagE2); lia | lia | lia | exact Hval | exact H32].
    + intros _. unfold XI. rewrite Hj. unfold XI in HX. rewrite Hi in HX. intros a Ha. rewrite (HLOW2 a Ha), (HLOW a Ha). exact (HX a Ha).
Qed.

Lemma EADDR : estart E0 (SA Eb 0) = E.
Proof. unfold estart. cbn [a_base a_off]. fold (uv E0 Eb). unfold E0. rewrite (proj1 (proj2 (proj2 (kit SPT.UU)))). lia. Qed.
Lemma PADDR : estart E0 (SA Pb 0) = P.
Proof. unfold estart. cbn [a_base a_off]. fold (uv E0 Pb). unfold E0. rewrite (proj1 (proj2 (kit SPT.UU))). lia. Qed.
Lemma OBJS : PML.obj_on_stack L sp P 272 /\ PML.obj_on_stack L sp V 48 /\ PML.obj_on_stack L sp E 16 /\ PML.apart P 272 V 48 /\ PML.apart P 272 E 16 /\ PML.apart V 48 E 16.
Proof. exact (conj OP (conj OV (conj OE (conj AP1 (conj AP2 AP3))))). Qed.
Lemma WPAR_in : forall w a, In w (PML.W_par P E) -> L5.in_rng w a -> exists w', In w' W /\ L5.in_rng w' a.
Proof. intros w a Hw Hin. exists w. split; [unfold W, PMS.W_parc; apply in_or_app; left; exact Hw | exact Hin]. Qed.

Lemma sm_sm : forall q, PML.ps_more q = true -> PMCUR.ps_set_more (PMCUR.ps_set_more q false) true = q.
Proof. intros [] H; cbn in H; subst; reflexivity. Qed.

Lemma pa_cap : forall (M1 : mem) P1 ps2 w, PML.parser_at M1 P1 (PML.ps_set_win ps2 w) -> PML.ps_bcap ps2 mod 2 = 0.
Proof.
  intros M1 P1 ps2 w H. unfold PML.parser_at in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _). cbn [PML.ps_set_win PML.ps_bcap PML.ps_bptr PML.ps_buf] in Hs.
  destruct Hs as (_ & H8 & _). pose proof (Z.div_mod (PML.ps_bcap ps2) 8 ltac:(lia)) as D. rewrite H8 in D. rewrite D, Z.add_0_r. replace (8 * (PML.ps_bcap ps2 / 8)) with ((4 * (PML.ps_bcap ps2 / 8)) * 2) by lia.
  apply Z.mod_mul. lia.
Qed.
Lemma pa_retext : forall (M1 : mem) st sst nst mo dn lv stk sb1 sc1 cap ptr buf buf' w,
  PML.parser_at M1 P (PML.PS st sst nst mo dn lv stk sb1 sc1 cap ptr buf w) -> L5.bytes_at RSEGS M1 ptr buf' -> length buf' = length buf ->
  PML.parser_at M1 P (PML.PS st sst nst mo dn lv stk sb1 sc1 cap ptr buf' w).
Proof.
  intros M1 st sst nst mo dn lv stk sb1 sc1 cap ptr buf buf' w H Hb Hl. unfold PML.parser_at in *.
  cbn [PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win] in *.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & Hs & Rest).
  repeat (split; [assumption|]). split; [exact (PB3.str_retext M1 (P + 224) cap ptr buf buf' Hs Hb Hl) | exact Rest].
Qed.

Lemma entry_bytes : L5.bytes_at RSEGS M bptr (PML.ps_buf ps) /\ L5.bytes_at RSEGS M sb (PML.ps_stack ps).
Proof.
  pose proof HPA as H. unfold PML.parser_at in H. cbn [PML.ps_set_win PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_sb PML.ps_stack] in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _ & _ & _ & _ & Hst' & _).
  destruct Hs as ((_ & _ & _ & _ & BS & _) & _). split; [exact BS | exact Hst'].
Qed.
Lemma leaf_after : forall i c k ps1 j cj ci, is_leaf i c k ps1 (CC.TOther AFTERV) -> is_end i = false -> is_end j = true -> CH2.ret_of G.RETS i k = Some j -> nth_error G.CPS j = Some cj ->
  SR.ps_pc ps1 = AFTERV -> CH2.blocks_eqb (nth i G.BLS []) SPT.BL0 = true -> nth 10 (CA.ps_reglist ps1) (ELit 0) = Pb -> nth 11 (CA.ps_reglist ps1) (ELit 0) = Eb ->
  view_chk (SR.ps_cells ps1) = true -> PB.has (SR.ps_cells ps1) (KWord (SA Eb 0) 4 (ELit 0)) = true -> PB.has (SR.ps_cells ps1) (KWord (SA Vb 0) 8 (ELit PML.VT_VISITOR)) = true ->
  PB2.ptrans_chk GT.NF G.HDECL Eb 0 Pb 0 512 11 c ps1 cj (nth i G.BLS []) (nth j G.BLS []) = Some ci -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 j cj ci IL Hi Hj Hret Hcj Hpc HBL Ha0e Ha1e HV Hec Hvis Hchk.
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  apply (PB2.ptrans_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K HKnil XI DEF0
           Eb 0 eq_refl E EADDR OE g HG Pb 0 eq_refl P PADDR V OBJS WPAR_in AFTERV 512 _ _ _ _ _ _ (AFTERV_OK mw)
           (fun pst M1 P1 ps2 H => pa_cap M1 P1 ps2 _ (proj1 H)) B kx bx 11%nat i c k ps1 j cj ci IL Hret Hcj Hpc Hchk).
  intros E1 E' R' M1 M' model1 cr1 HagE' Vregs Hnx Hag HLF HRL HA' HX HH1 HC1.
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame i c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
  pose proof (xlow_tr M1 M' HLOW (xi_low i E1 M1 Hi HX)) as HXL.
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). pose proof SCRCV as HSC. destruct OP as (OP1 & OP2 & OP3), OE as (OE1 & OE2 & OE3), OV as (OV1 & OV2 & OV3).
  pose proof (kit SPT.NUM) as ((B0 & B1 & B2 & B3 & B4) & (C0 & C1 & C2 & C3 & C4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _).
  assert (HQ : 0 <= sb /\ sb + scap <= hl_ceil L /\ Z.of_nat (length (PML.ps_stack ps)) <= scap /\ 0 <= bptr /\ bptr + bcap <= hl_ceil L /\ Z.of_nat (length (PML.ps_buf ps)) <= bcap).
  { unfold sb, scap, bptr, bcap. clear - B0 B4 C0 C4 N2 N4. lia. }
  destruct HQ as (HQ1 & HQ2 & HQ3 & HQ4 & HQ5 & HQ6).
  destruct entry_bytes as (HBUF & HSTK).
  pose proof (SPT.pa_def _ _ _ HPA) as HdefP. destruct HEC as (_ & HEd & _).
  assert (HdP' : L5.defined M' P 272) by (apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 P 272 HA' HdefP); left; lia).
  assert (HdE' : L5.defined M' E 16) by (apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 E 16 HA' HEd); left; lia).
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & G42 & G43 & G44 & G45 & G46 & G36 & G38 & G39 & G40 & GSE & GSC & GPE & GCE & G32 & G33 & _).

  assert (HPA' : PML.parser_at M' P (PML.ps_set_win (PMCUR.ps_set_more ps false) mw)).
  { unfold view_chk in HV. destruct (SPA.pview_w (SR.ps_cells ps1) Pb PE CE) as [pv|] eqn:HPV; [|discriminate].
    apply andb_prop in HV as [HV Y12]. apply andb_prop in HV as [HV Y11]. apply andb_prop in HV as [HV Y10]. apply andb_prop in HV as [HV Y9]. apply andb_prop in HV as [HV Y8].
    apply andb_prop in HV as [HV Y7]. apply andb_prop in HV as [HV Y6]. apply andb_prop in HV as [HV Y5]. apply andb_prop in HV as [HV Y4]. apply andb_prop in HV as [HV Y3].
    apply andb_prop in HV as [Y1 Y2]. apply expr_eqb_eq in Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11, Y12.
    destruct (SPA.parser_view_w E' M' (SR.ps_cells ps1) Pb PE CE pv P false (PML.ps_done ps) (PML.ps_stack ps) scap mw HK HPV GP' ltac:(lia) ltac:(lia)) as (buf & HPAv & Hlen' & _).
    - rewrite Y7. rewrite PB2.uv_lit by lia. reflexivity.
    - rewrite Y8, G46. reflexivity.
    - rewrite Y10, G38. exact (xlow_bytes M' sb scap _ HXL HQ1 HQ2 HQ3 HSTK).
    - rewrite Y11, Y10. unfold SEND0. rewrite GSE, G38. reflexivity.
    - rewrite Y12, Y10. unfold SCEND0. rewrite GSC, G38. reflexivity.
    - exact HQ3.
    - rewrite Y3. exact G32.
    - rewrite Y2. exact G33.
    - exact (kit SPT.mw_le).
    - exact HdP'.
    - rewrite Y4, Y5, Y6, Y1, Y10, G43, G44, G41, G38, GCE, GPE in HPAv. rewrite Y9, G36 in Hlen'. rewrite PB2.uv_lit in HPAv by lia.
      pose proof (pa_retext M' _ _ _ _ _ _ _ _ _ _ _ buf (PML.ps_buf ps) mw HPAv (xlow_bytes M' bptr bcap _ HXL HQ4 HQ5 HQ6 HBUF) ltac:(apply Nat2Z.inj; rewrite Hlen'; reflexivity)) as Q.
      unfold PML.ps_set_win, PMCUR.ps_set_more. rewrite Hst. exact Q. }
  exists (PMCUR.ps_set_more ps false). split; [rewrite (CH2.blocks_eqb_eq _ _ HBL); exact (kit SPT.den_BL0 E' HagE')|].
  assert (Hden1 : CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps) by (rewrite (CH2.blocks_eqb_eq _ _ HBL); exact (kit SPT.den_BL0 E1 (amb_agree _ _ _ _ HA'))).
  pose proof WFM as (_ & F5).
  split.
  { unfold PB2.ptrans_pre.
    split; [split; [exact (reg_arg E' R' _ 10%bv 10%nat _ P HRL eq_refl eq_refl Ha0e GP') | split; [exact (reg_arg E' R' _ 11%bv 11%nat _ E HRL eq_refl eq_refl Ha1e GE) | split; [reflexivity | split; [exact Hst | rewrite (sm_sm ps Hmore); exact (conj HWF HLV)]]]]|].
    split; [exact HPA'|]. split; [split; [apply SCU.wf_ps_stale_stop; [reflexivity | rewrite (sm_sm ps Hmore); exact HWF] | apply SCU.lvl_ok_stop; reflexivity]|].
    split; [apply (SPT.win_ok_tr M M' LBo ps (PMCUR.ps_set_more ps false) eq_refl HWIN); intros ch p n Hch C1' C2' Hwd; apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 p n HA' Hwd); right; exists ch; split; [exact Hch | lia]|].
    split; [exact HBB|].
    split; [unfold PML.vis_at; split; [pose proof (PB2.kword64_elim E' M' _ _ V (PB.has_ok E' M' _ _ HK Hvis)) as T; rewrite PB2.uv_lit in T by (unfold PML.VT_VISITOR; lia); apply T;
            unfold estart; cbn [a_base a_off]; fold (uv E' Vb); rewrite GV; lia | apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 V 48 HA' (proj2 HVIS)); left; lia]|].
    split; [split; [|split; [exact HdE' | left; reflexivity]]; pose proof (PB2.kword32_elim E' M' _ _ E (PB.has_ok E' M' _ _ HK Hec)) as T; rewrite PB2.uv_lit in T by lia; apply T;
            unfold estart; cbn [a_base a_off]; fold (uv E' Eb); rewrite GE; lia|].
    split; [exact (xlow_ls M' HXL) | exact (proj1 (cred_pc i E1 cr1 ps Hden1 F5) HC1)]. }
  intros R2 M2 cr2 ps2 code g' E2 (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) HagE2 Hcode Hden2 HP.
  split.
  - unfold XI. rewrite Hj. exists ps2, code, g'. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|]. split; [exact Q8|]. split; [exact Q10 | exact Hden2].
  - destruct Q2 as ((_ & _ & _ & W4 & _) & _). exact (proj2 (cred_pc j E2 cr2 ps2 Hden2 W4) Q9).
Qed.

Lemma exit_end : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> is_end i = true -> PB.exit_base_chk GT.NF pc c ps1 = true -> In pc GT.ENDS -> forallb stack_reg_eqb (CC.cp_F c) = true ->
  ev_any (SR.ps_cells ps1) = true ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc IL Hi Hbase Hpcin F6 HEVA fx' E1 R1 M1 model1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct Hentry as (Hra & Hraok & _). pose proof SCRCV as HSC. pose proof SCRV as HSV.
  apply (PB.exit_ret L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K XI DEF0 (fun _ => 0) (fun _ => 0) SCRC
           ltac:(rewrite SCRV; lia) ltac:(lia) S5 R (SPT.EV0 mw B ps R line0 pos0 [] SPT.noeb) r Hra Hraok heap_ok3 pc i c k ps1 _ (rets pc Hpcin) IL Hbase fx' E1 R1 M1 model1 E' R' M' HAt HAmb Hag HLF).
  intros HRP HP HA' HagE'.
  unfold XI in HX. rewrite Hi in HX. destruct HX as (ps2 & code & g' & (X1 & X2) & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X13).

  set (F := [(sp - 576, 576)] : list L5.range).
  assert (FR : L5.frame_but F M1 M').
  { intros x Hx. apply (CC.lf_frame _ _ _ _ _ _ _ HLF). unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
    rewrite forallb_forall in F6. specialize (F6 _ Hin). unfold stack_reg_eqb in F6. apply andb_prop in F6 as [F6 H3]. apply andb_prop in F6 as [H1 H2].
    apply expr_eqb_eq in H1, H3. apply Z.eqb_eq in H2. subst rb rlo rlen.
    rewrite (PB.estart_agree GT.NF E0 E' (EVar 2) (- SCR) HagE' eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. pose proof U2 as U2'. rewrite U2'. unfold SCR. rewrite HSV. rewrite u64_of_Z by lia.
    specialize (Hx (sp - 576, 576) ltac:(left; reflexivity)). unfold L5.in_rng in Hx. cbn [fst snd] in Hx. lia. }
  pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as GR.
  assert (OUT_HI : forall a n, sp <= a -> a + n <= 2 ^ 64 -> PB2.out F a n).
  { intros a n A1 A2. split; [lia|]. split; [exact A2|]. intros q Hq w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  assert (OUT_LO : forall a n, 0 <= a -> a + n <= sp - 576 -> PB2.out F a n).
  { intros a n A1 A2. split; [lia|]. split; [lia|]. intros q Hq w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  pose proof HAmb as (_ & _ & _ & (cr0 & HH0 & _) & _ & _). unfold CH2.cur in HH0. rewrite X13 in HH0.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH0) as (Hwf & _).
  destruct (Hwf (PML.ps_bptr ps2, PML.ps_bcap ps2) ltac:(left; reflexivity)) as ((B0 & _ & _ & B3 & B4) & _). destruct (Hwf (PML.ps_sb ps2, PML.ps_scap ps2) ltac:(right; left; reflexivity)) as ((D0 & _ & _ & D3 & D4) & _).
  cbn [fst snd] in *. unfold hl_ceil in B4, D4, S6. destruct OP as (OP1 & OP2 & OP3), OE as (OE1 & OE2 & OE3).
  assert (HPA' : PML.parser_at M' P (PML.ps_set_win ps2 mw)).
  { apply (PB2.parser_at_fr F M1 M' FR GR P _ (OUT_HI P 272 ltac:(lia) ltac:(lia))); [apply OUT_LO; cbn [PML.ps_set_win PML.ps_bptr PML.ps_bcap]; lia | apply OUT_LO; cbn [PML.ps_set_win PML.ps_sb PML.ps_scap]; lia | exact X1]. }
  assert (HEC' : PML.ec_at M' E code) by (apply (PB2.ec_at_fr F M1 M' FR GR E code (OUT_HI E 16 ltac:(lia) ltac:(lia))); exact X7).
  assert (HLS' : PML.ls_ok g' M').
  { apply (PB2.ls_ok_fr F M1 M' FR g'); [destruct X10 as [->|[-> _]]; [exact HG | destruct g; discriminate] | apply OUT_LO; lia | exact X9]. }
  pose proof (PB2.win_ok_fr M1 M' GR LBo ps2 X5) as HWO.
  pose proof HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr & Hdf). unfold CH2.cur in HH1. rewrite X13 in HH1.
  assert (Hsc2 : In (PML.ps_scap ps2) [66; 132; 264; 528; 1056]) by (destruct X4 as ((_ & _ & _ & W4 & _) & _); exact W4).
  apply (Hcont fx' R' M' model1 (PML.ps_blocks ps2 ++ LBo) cr1 LBo W HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH1].
  exists ps2, code, g'.
  split; [exact (conj HPA' X2)|]. split; [exact X4|]. split; [exact HWO|]. split; [exact X6|].
  split; [exact HEC'|]. split; [exact X8|]. split; [exact HLS'|]. split; [exact X10|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact (proj1 (cred_pc i E1 cr1 ps2 X13 Hsc2) HC1)|].
  destruct X11 as (X11a & X11b & X11c & X11d & X11e & X11f & X11g & X11h & X11i). subst code.
  split; [left; split; [reflexivity|]; split; [exact X11c|]; split; [exact X11d|]; split; [exact X11e|]; split; [exact X11f | exact X11g]|].

  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & G42 & G43 & G44 & G45 & G46 & G36 & G38 & G39 & G40 & GSE & GSC & GPE & GCE & G32 & G33 & _).
  pose proof OV as (OV1 & OV2 & OV3).
  assert (ESV : forall q, estart E' (SA Vb q) = V + q) by (intros q; unfold estart; cbn [a_base a_off]; fold (uv E' Vb); rewrite GV; reflexivity).
  assert (HdV' : L5.defined M' (V + 8) 40).
  { apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 (V + 8) 40 HA'); [eapply (L5.defined_sub _ _ _ _ _ (proj2 HVIS)); lia | left; lia]. }
  assert (HFLG : forall f, 0 <= f < 2 ^ 64 -> PB.has (SR.ps_cells ps1) (VSU.fl Vb 0 f) = true -> L5.u64_at RSEGS M' (V + 8) f).
  { intros f Hf Hfl. assert (Q : estart E' (SA Vb (0 + 8)) = V + 8) by (rewrite ESV; lia).
    pose proof (PB2.kword64_elim E' M' _ _ (V + 8) (PB.has_ok E' M' _ _ HK Hfl) Q) as T. rewrite PB2.uv_lit in T by exact Hf. exact T. }
  assert (HV32 : forall v, PB.has (SR.ps_cells ps1) (KWord (SA Vb 32) 8 v) = true -> L5.u64_at RSEGS M' (V + 32) (uv E' v)).
  { intros v Hv. exact (PB2.kword64_elim E' M' _ _ (V + 32) (PB.has_ok E' M' _ _ HK Hv) (ESV 32)). }
  assert (HAV : PMCUR.after_value_st ps2) by (unfold PMCUR.after_value_st; rewrite X11d; destruct (Z.eqb (PML.ps_level ps) 0); cbn; tauto).
  unfold ev_any in HEVA.
  destruct (ev_chk_s (SR.ps_cells ps1)) eqn:ES0; [clear HEVA|destruct (ev_chk_v (SR.ps_cells ps1) 32) eqn:EU0; [clear HEVA|destruct (ev_chk_v (SR.ps_cells ps1) 16) eqn:EI0;
    [clear HEVA|destruct (ev_chk_v (SR.ps_cells ps1) 128) eqn:ED0; [clear HEVA|discriminate HEVA]]]].
  -
    unfold ev_chk_s in ES0. apply andb_prop in ES0 as [ES0 Hn]. apply andb_prop in ES0 as [Hfl Hp].
    assert (HN : L5.u64_at RSEGS M' (V + 40) size0).
    { apply orb_prop in Hn as [Hn|Hn].
      - pose proof (PB2.kword64_elim E' M' _ _ (V + 40) (PB.has_ok E' M' _ _ HK Hn) (ESV 40)) as T. rewrite G36 in T. exact T.
      - apply andb_prop in Hn as [Hn Hz]. pose proof (PB.has_ok E' M' _ _ HK Hz) as Z0. cbn [kentry_ok] in Z0. fold (uv E' (EVar 36)) in Z0. rewrite G36 in Z0.
        pose proof (PB2.kword64_elim E' M' _ _ (V + 40) (PB.has_ok E' M' _ _ HK Hn) (ESV 40)) as T. rewrite PB2.uv_lit in T by lia. replace size0 with 0 by lia. exact T. }
    apply (SCU.cur_post_event RSEGS ps ps2 M' V (PMCUR.EvStr bptr size0) X11c X11a).
    + unfold PMCUR.ev_at. split; [exact HdV'|]. split; [exact (HFLG 1 ltac:(lia) Hfl)|]. split; [|exact HN].
      pose proof (PB2.kword64_elim E' M' _ _ (V + 32) (PB.has_ok E' M' _ _ HK Hp) (ESV 32)) as T. rewrite GPE in T. exact T.
    + cbn [PMCUR.ev_rel]. split; [exact HAV|]. split; [exact X11f|]. left. split; [symmetry; exact X11h | unfold size0; rewrite X11i; reflexivity].
  -
    unfold ev_chk_v in EU0. apply andb_prop in EU0 as [Hfl EU0]. destruct (CAX.cell_at (SR.ps_cells ps1) Vb 32 8) as [v|]; [|discriminate EU0].
    apply (SCU.cur_post_event RSEGS ps ps2 M' V (PMCUR.EvU64 (uv E' v)) X11c X11a).
    + unfold PMCUR.ev_at. split; [exact HdV'|]. split; [exact (HFLG 32 ltac:(lia) Hfl) | exact (HV32 v EU0)].
    + cbn [PMCUR.ev_rel]. split; [exact HAV | exact X11f].
  -
    unfold ev_chk_v in EI0. apply andb_prop in EI0 as [Hfl EI0]. destruct (CAX.cell_at (SR.ps_cells ps1) Vb 32 8) as [v|]; [|discriminate EI0].
    apply (SCU.cur_post_event RSEGS ps ps2 M' V (PMCUR.EvI64 (uv E' v)) X11c X11a).
    + unfold PMCUR.ev_at. split; [exact HdV'|]. split; [exact (HFLG 16 ltac:(lia) Hfl) | exact (HV32 v EI0)].
    + cbn [PMCUR.ev_rel]. split; [exact HAV | exact X11f].
  -
    unfold ev_chk_v in ED0. apply andb_prop in ED0 as [Hfl ED0]. destruct (CAX.cell_at (SR.ps_cells ps1) Vb 32 8) as [v|]; [|discriminate ED0].
    apply (SCU.cur_post_event RSEGS ps ps2 M' V (PMCUR.EvDbl (uv E' v)) X11c X11a).
    + unfold PMCUR.ev_at. split; [exact HdV'|]. split; [exact (HFLG 128 ltac:(lia) Hfl) | exact (HV32 v ED0)].
    + cbn [PMCUR.ev_rel]. split; [exact HAV | exact X11f].
Qed.

Lemma leaves : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. cbn [leaf_chk] in X.
  destruct (Z.eqb pc DECU64 || Z.eqb pc AFTERV || Z.eqb pc VISS || Z.eqb pc VISI || Z.eqb pc VISU)%bool eqn:HPC'.
  - apply andb_prop in X as [X XR]. apply andb_prop in X as [Hpc Hi]. apply Z.eqb_eq in Hpc. apply negb_true_iff in Hi.
    destruct (CH2.ret_of G.RETS i k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate]. cbv zeta in XR.
    destruct (Z.eqb_spec pc DECU64) as [->|N1]; [|destruct (Z.eqb_spec pc VISS) as [->|N2]; [|destruct (Z.eqb_spec pc VISI) as [->|N3]; [|destruct (Z.eqb_spec pc VISU) as [->|N4]]]].
    + apply andb_prop in XR as [Hj XD]. apply negb_true_iff in Hj. apply existsb_exists in XD as (d & Hd & XD).
      destruct (dec_chk d c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
      exact (leaf_dec i c k ps1 j cj d ci IL Hi Hj Hret Hcj Hpc Hd Hchk).
    + apply andb_prop in XR as [Hj XV]. apply negb_true_iff in Hj. apply orb_prop in XV as [XV|XV].
      * unfold vis_okb in XV. destruct (vis_chk_s (EVar 36) c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. apply Nat.leb_le in XV.
        exact (leaf_vis_s (EVar 36) size0 nv36 nr36 i c k ps1 j cj ci IL Hi Hj Hret Hcj Hpc Hchk XV).
      * unfold vis_okb in XV. destruct (vis_chk_s (ELit 0) c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. apply Nat.leb_le in XV.
        exact (leaf_vis_s (ELit 0) 0 nv0 ltac:(lia) i c k ps1 j cj ci IL Hi Hj Hret Hcj Hpc Hchk XV).
    + apply andb_prop in XR as [Hj XV]. apply negb_true_iff in Hj. unfold vis_ok_v in XV.
      destruct (vis_chk_v 16 c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. apply andb_prop in XV as [XV Hvl]. apply Nat.leb_le in XV.
      exact (leaf_vis_v VISI 16 PMCUR.EvI64 VISI_OK vis_evi ltac:(lia) i c k ps1 j cj ci IL Hi Hj Hret Hcj Hpc Hchk XV Hvl).
    + apply andb_prop in XR as [Hj XV]. apply negb_true_iff in Hj. unfold vis_ok_v in XV.
      destruct (vis_chk_v 32 c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. apply andb_prop in XV as [XV Hvl]. apply Nat.leb_le in XV.
      exact (leaf_vis_v VISU 32 PMCUR.EvU64 VISU_OK vis_evu ltac:(lia) i c k ps1 j cj ci IL Hi Hj Hret Hcj Hpc Hchk XV Hvl).
    + cbn [orb] in HPC'. rewrite ?orb_false_r in HPC'. apply Z.eqb_eq in HPC'. rewrite HPC' in IL, Hpc. clear N1 N2 N3 N4.
      apply andb_prop in XR as [XR XC]. apply andb_prop in XR as [XR Hvis]. apply andb_prop in XR as [XR Hec]. apply andb_prop in XR as [XR HV]. apply andb_prop in XR as [XR Ha1e].
      apply andb_prop in XR as [XR Ha0e]. apply andb_prop in XR as [Hj HBL]. apply expr_eqb_eq in Ha0e, Ha1e.
      destruct (PB2.ptrans_chk GT.NF G.HDECL Eb 0 Pb 0 512 11 c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
      exact (leaf_after i c k ps1 j cj ci IL Hi Hj Hret Hcj Hpc HBL Ha0e Ha1e HV Hec Hvis Hchk).
  - apply andb_prop in X as [X HEVA]. apply andb_prop in X as [X F6]. apply andb_prop in X as [X Hin]. apply andb_prop in X as [Hi Hbase].
    apply existsb_exists in Hin as (pc' & Hin & Heq). apply Z.eqb_eq in Heq. subst pc'. exact (exit_end i c k ps1 pc IL Hi Hbase Hin F6 HEVA).
Qed.

Lemma main : srealizes RSEGS SCFG (@PML.cfg fx R PCF M model) K.
Proof.
  unfold PML.cfg. change PCF with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply (CH2.cert_sound3 L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 W_OK WRS_OK
            G.CPS K PML.fp_ok G.TAGS XI) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok3.
  - intros i c k ps1 j s0 IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. discriminate X.
  - intros i c k ps1 j s0 IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. discriminate X.
  - exact leaves.
  - reflexivity.
  - rewrite LS. exact At0.
  - pose proof WFM as (_ & F5).
    assert (Hden0 : CH2.den E0 (nth 0 G.BLS []) = PML.ps_blocks ps) by (change (nth 0 G.BLS []) with SPT.BL0; exact (kit SPT.den_BL0 E0 (CC.env_agree_refl _ _))).
    split.
    + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr. split; [unfold CH2.cur; rewrite Hden0; exact HH | exact (proj2 (cred_pc 0%nat E0 cr ps Hden0 F5) HPC)].
    + unfold XI. rewrite end0. intros a _. reflexivity.
  - exact Hfp.
Qed.
End Main.

Section Final.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis DECU64_OK : PMS.dec_u64_spec L.
Hypothesis AFTERV_OK : PMS.after_value_spec L HI.
Hypothesis VISS_OK : PMS.visit_string_spec L PMS.PC_VIS_STRING.
Hypothesis VISI_OK : PMS.visit_i64_spec L PMS.PC_VIS_I64.
Hypothesis VISU_OK : PMS.visit_u64_spec L PMS.PC_VIS_U64.

Theorem end_integer_value_ok : PMS.end_integer_value_spec L HI PML.STRTOD_SCR_V.
Proof.
  unfold PMS.end_integer_value_spec, PMS.end_number_spec, PMS.ptrans_stale, PMS.ptrans_gb. intros mw LBo cr sp r P V E B kx bx g ps. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & ((Ha0 & Ha1 & Ha2) & Hmore & Hst & Hnf) & HPA & (HWF & HLV) & HWIN & HBB & HVIS & HEC & HLS & HG & HPC & OP & OV & OE & AP1 & AP2 & AP3) Hcont.
  pose proof (SPT.pa_def _ _ _ HPA) as HdP.
  destruct (PB2.cell_exists M (P + 160) 8 ltac:(lia)) as (line0 & Rc1 & Hc1); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  destruct (PB2.cell_exists M (P + 168) 8 ltac:(lia)) as (pos0 & Rc2 & Hc2); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  exact (main L HI HIok LAY FPM DECU64_OK AFTERV_OK VISS_OK VISI_OK VISU_OK mw LBo cr sp r P V E B kx bx g ps fx R M model K HH Hmo HKnil Hfp Hentry Ha0 Ha1 Ha2 Hmore Hst HPA HWF HLV HWIN HBB HVIS HEC HLS HG HPC OP OV OE AP1 AP2 AP3
           Hcont line0 pos0 Hc1 Hc2 (conj Rc1 Rc2)).
Qed.
End Final.
End EndIntegerValueProof.

