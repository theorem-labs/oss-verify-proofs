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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseSomeAt_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallPure SmallKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmSmall Require Import SmallAt_u SmallPt_u SmallCur_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_begin_member_csrc_T_u Cut_begin_member_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module BeginMemberProof.
Module G := Cut_begin_member_csrc_u.
Module GT := Cut_begin_member_csrc_T_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Definition Pb : expr := EVar 10.  Definition Eb : expr := EVar 11.  Definition Vb : expr := EVar 49.
Definition RETPC : Z := nth 0 GT.ENDS 0.
Definition DEADPC : Z := nth 1 GT.ENDS 0.
Definition PARENT : Z := PML.PC_PARENT.
Definition SCR : Z := CH.hd_scr G.HDECL.
Definition CONSTS : PSK.consts := PSK.CONSTS PML.VT_PARSER PML.VT_FUNC PML.VT_VISITOR 0x10000 0xf8000 0x10000 PML.IMG_RO_HI SCR [] 0.
Definition X0 : PSK.pexprs := SPT.X0 (ELit 7) (ELit 1).
Lemma kn0_eq : CC.cp_know G.cp0 = SPK.kn CONSTS false Pb Vb Eb (EVar 2) (EVar 33) X0.
Proof. vmc_refl. Qed.
Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Abbreviation PE := SPT.PE.  Abbreviation CE := SPT.CE.
Definition GP : expr := EVar (CC.cp_nx (nth 1 G.CPS G.cp0) - APC.NCS - 1).

Definition view_chk (cells : list kentry) (stv : expr) : bool :=
  match SPA.pview_w cells Pb PE CE with
  | Some pv => (expr_eqb (PB4.pv_level pv) (EVar 41) && expr_eqb (PB4.pv_wend pv) (EVar 33) && expr_eqb (PB4.pv_wptr pv) (EVar 32) && expr_eqb (PB4.pv_st pv) stv
                && expr_eqb (PB4.pv_sst pv) (EVar 43) && expr_eqb (PB4.pv_nst pv) (EVar 44) && expr_eqb (PB4.pv_more pv) (ELit 1) && expr_eqb (PB4.pv_done pv) (EVar 46)
                && expr_eqb (PB4.pv_size pv) (EVar 36) && expr_eqb (PB4.pv_sb pv) (EVar 38) && expr_eqb (PB4.pv_send pv) (APC.eadd (EVar 38) (EVar 39))
                && expr_eqb (PB4.pv_scend pv) (APC.eadd (EVar 38) (EVar 40)))%bool
  | None => false
  end.
Definition parent_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in let nx := (CC.cp_nx cj - APC.NCS - 1)%nat in
  if (expr_eqb (nth 10 regs (ELit 0)) Pb && CH2.blocks_eqb BLj BLi && view_chk (SR.ps_cells ps) (ELit 7))%bool
  then CH2.custom_chk GT.NF G.HDECL 48 1 BLi [] [KRange (EVar nx) 0 255] (Some (EVar nx)) c ps cj BLi
  else None.
Definition sltu0 (c : Z) : kentry := KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB GP (ELit c)) (ELit 1)) 0 0.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc PARENT then
        (Z.eqb (SR.ps_pc ps) PARENT && Nat.eqb i 0 &&
         match CH2.ret_of G.RETS i k with
         | Some j => match nth_error G.CPS j with
                     | Some cj => (Nat.eqb j 1 && match parent_chk c ps cj (nth i G.BLS []) (nth j G.BLS []) with Some ci => Nat.eqb (CC.cp_nx cj) (CH2.ci_nx ci + 1 + APC.NCS) | None => false end)%bool
                     | None => false end
         | None => false end)%bool
      else if Z.eqb pc DEADPC then (Nat.eqb i 1 && PB.has cells (sltu0 0) && PB.has cells (sltu0 8) && PB.has cells (sltu0 14))%bool
      else (Nat.eqb i 1 &&
            (PB.has cells (KRange GP 0 0)
             || (PB.exit_base_chk GT.NF RETPC c ps && CH2.blocks_eqb (nth i G.BLS []) SPT.BL0 && PB.has cells (KWord (SA Eb 0) 4 (ELit 0))
                 && ((view_chk cells (ELit 10) && PB.has cells (KRange GP 8 8)) || (view_chk cells (ELit 13) && PB.has cells (KRange GP 14 14))))))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Definition F0 : list SGP.region := CC.cp_F G.cp0.
Lemma foot_ok : CC.cps_all G.CPS (fun _ c => SP.F_sub (CC.cp_F c) F0) = true.
Proof. vmc_refl. Qed.

Section Main.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis PARENT_OK : PMS.parent_spec L.
Abbreviation SSCR := PML.STRTOD_SCR_V.
Abbreviation SCRC := (PMS.PF_SCR SSCR).

Variables (LBo : list (Z * Z)) (cr : credit) (sp r P V E B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate).
Variables (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet).
Hypothesis HH : hi_heap HI (PML.ps_blocks ps ++ LBo) cr M (m_vmmaps model).
Hypothesis Hmo : PML.model_ok model.
Hypothesis HKnil : K [].
Hypothesis Hfp : PML.fp_ok fx.
Hypothesis Hentry : PML.entry L R M sp r SCRC.
Hypothesis Ha0 : PML.a0 R P.
Hypothesis Ha1 : PML.a1 R E.
Hypothesis Hmore : PML.ps_more ps = true.
Hypothesis Hst : PML.ps_st ps = PML.ST_EXPECT_COMMA_OR_END.
Hypothesis HPA : PML.parser_at M P ps.
Hypothesis HWF : PML.wf_ps ps.
Hypothesis HWIN : PML.win_ok M LBo ps.
Hypothesis HBB : PML.buf_bound ps B.
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

Hypothesis Hcont : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range),
   PML.fp_ok fx' ->
   (exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state),
      PML.parser_at M' P ps' /\ PMCUR.wf_c ps' /\ PML.win_ok M' LBo ps' /\ PML.buf_bound ps' B /\ PML.ec_at M' E code /\
      (code <> 0 -> PML.ps_more ps' = false) /\ PML.ls_ok g' M' /\ (g' = g \/ g' = PML.regJ g /\ code <> 0) /\
      LB' = PML.ps_blocks ps' ++ LBo /\ LBk = LBo /\ W = PMS.W_parc P V E /\ PML.pcredit_x L cr' ps' kx bx /\
      (code = 0 /\ PML.ps_more ps' = true /\ In (PML.ps_st ps') [PML.ST_EXPECT_MEMBER_NAME; PML.ST_EXPECT_VALUE] /\
       PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps /\ PML.ps_win ps' = PML.ps_win ps) /\ PMCUR.cur_post RSEGS ps ps' code M' V) ->
   regs_preserved R R' -> L5C.hpres L LBk sp SCRC W M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
   srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model') K.

Variables (line0 pos0 : Z).
Hypothesis Hline0 : PML.u64 M (P + 160) line0.
Hypothesis Hpos0 : PML.u64 M (P + 168) pos0.
Hypothesis Hlpr : 0 <= line0 < 2 ^ 64 /\ 0 <= pos0 < 2 ^ 64.

Let mw := PML.ps_win ps.
Let bcap := PML.ps_bcap ps.
Let bptr := PML.ps_bptr ps.
Let size0 := Z.of_nat (length (PML.ps_buf ps)).
Let sb := PML.ps_sb ps.
Let scap := PML.ps_scap ps.
Let slen := Z.of_nat (length (PML.ps_stack ps)).
Let level := PML.ps_level ps.
Definition E0 : env := SPT.E0 mw B ps R line0 pos0 [V] SPT.noeb.

Lemma ps_mw : PML.ps_set_win ps mw = ps.
Proof. unfold mw. destruct ps; reflexivity. Qed.
Lemma SCRV : CH.hd_scr G.HDECL = 512.
Proof. reflexivity. Qed.

Lemma INST : SPT.inst L HI mw LBo cr sp r P V E B kx bx g ps R M model SCRC G.HDECL Pb Vb Eb line0 pos0 [V] SPT.noeb.
Proof.
  unfold SPT.inst. destruct Hlpr as (Q1 & Q2).
  pose proof HWF as (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)). destruct (W7 Hmore) as (W8 & W9 & _).
  destruct Hentry as (_ & _ & Hsp & _ & Hstk). pose proof (L5C.stk_floor _ _ _ _ Hstk) as FL. pose proof Hstk as (S1 & S2 & S3 & S4 & S5).
  destruct OP as (OP1 & OP2 & OP3), OV as (OV1 & OV2 & OV3), OE as (OE1 & OE2 & OE3).
  assert (HSC : SCRC = 9968) by reflexivity.
  split; [exact HIok|]. split; [exact LAY|]. split; [exact HH|]. split; [exact Hentry|]. split; [rewrite SCRV; lia|]. split; [lia|].
  split; [rewrite ps_mw; exact HPA|]. split; [exact (PML.wf_ps_stale_of ps HWF)|]. split; [lia|].
  split.
  { destruct HBB as (HB1 & HB2). pose proof (SPT.win_le M P ps HPA) as HWL. unfold PML.winlen, PML.buf_need in HB1. rewrite Hmore, Hst in HB1. cbn [andb Z.eqb] in HB1.
    change (PML.ST_EXPECT_COMMA_OR_END =? PML.ST_STRING) with false in HB1. destruct (PML.ps_win ps) as [[p e]|]; lia. }
  split; [rewrite Hst; unfold PML.ST_EXPECT_COMMA_OR_END; lia|].
  split; [exact HVIS|]. split; [exact HEC|]. split; [exact HLS|]. split; [exact HPC|].
  split; [exact (conj OP1 (conj OP2 OP3))|]. split; [exact (conj OV1 (conj OV2 OV3))|]. split; [exact (conj OE1 (conj OE2 OE3))|]. split; [exact AP1|]. split; [exact AP2|]. split; [exact AP3|].
  split; [exact Hline0|]. split; [exact Hpos0|]. split; [exact Q1|]. split; [exact Q2|].
  split; [unfold PB.uv, Pb; cbn [edenot]; rewrite (SPT.EV0 mw B ps R line0 pos0 [V] SPT.noeb 10%bv), Ha0; apply u64_of_Z; lia|].
  split; [unfold PB.uv, Vb; cbn [edenot]; change (ev (SPT.E0 mw B ps R line0 pos0 [V] SPT.noeb) 49) with (Z_to_bv 64 V); apply u64_of_Z; lia|].
  split; [unfold PB.uv, Eb; cbn [edenot]; rewrite (SPT.EV0 mw B ps R line0 pos0 [V] SPT.noeb 11%bv), Ha1; apply u64_of_Z; lia|].
  split; [reflexivity|]. split; reflexivity.
Qed.
Notation kit X := (X L HI mw LBo cr sp r P V E B kx bx g ps R M model SCRC G.HDECL Pb Vb Eb line0 pos0 [V] SPT.noeb INST) (only parsing).

Lemma At0 : CC.At RSEGS G.cp0 E0 R M.
Proof.
  split; [exact (regs_ok_id R _ _)|]. rewrite kn0_eq.
  apply (kit SPT.kn_ok CONSTS (ELit 7) (ELit 1) eq_refl eq_refl eq_refl (conj eq_refl eq_refl) (conj eq_refl eq_refl) eq_refl).
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

Definition Cred (i : nat) (E1 : env) (cr1 : credit) : Prop := cr1 = cr.
Lemma CRED_BLK : forall i j E1 E2 cr1, CH2.den E2 (nth j G.BLS []) = CH2.den E1 (nth i G.BLS []) -> Cred i E1 cr1 -> Cred j E2 cr1.
Proof. intros i j E1 E2 cr1 _ H. exact H. Qed.

Definition XI (i : nat) (E1 : env) (M1 : mem) : Prop :=
  (forall a, 0 <= a < 2 ^ 40 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\
  L5.bytes_at RSEGS M1 sb (PML.ps_stack ps) /\
  (i = 1%nat -> exists rest x, PML.ps_stack ps = rest ++ [x] /\ uv E1 GP = x).

Abbreviation HAMB := (CH2.heap_amb L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred).
Abbreviation AMB3 := (CH2.amb3 L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred XI).
Abbreviation is_leaf := (CH2.is_leaf G.CPS G.TAGS).
Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.

Lemma below_frame : forall i c E' (M1 M' : mem), nth_error G.CPS i = Some c -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' (CC.cp_F c) a -> M' a = M1 a) -> forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof.
  intros i c E' M1 M' Hc Hag HF a Ha. apply HF. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  pose proof (SP.F_sub_in _ _ _ (CC.cps_all_sound _ _ foot_ok i c Hc) Hin) as Hin0.
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OP as (OP1 & OP2 & _). pose proof (kit SPT.UU) as (U2' & UP & _ & _).
  assert (HSC : SCRC = 9968) by reflexivity.
  unfold hl_ceil in *. rewrite L5.unsigned_lit by lia. left.
  unfold F0 in Hin0. cbn [G.cp0 CC.cp_F In] in Hin0. destruct Hin0 as [X|[X|[]]]; injection X as <- <- <-.
  - rewrite (PB.estart_agree GT.NF E0 E' (EVar 2) (-512) Hag eq_refl). unfold estart. cbn [a_base a_off]. fold (uv E0 (EVar 2)). unfold E0. rewrite U2'. lia.
  - unfold Pb in UP. rewrite (PB.estart_agree GT.NF E0 E' (EVar 10) 0 Hag eq_refl). unfold estart. cbn [a_base a_off]. fold (uv E0 (EVar 10)). unfold E0. rewrite UP. lia.
Qed.

Lemma xi_below : forall i E1 (M1 M' : mem), (forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> XI i E1 M1 ->
  (forall a, 0 <= a < 2 ^ 40 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\ L5.bytes_at RSEGS M' sb (PML.ps_stack ps).
Proof.
  intros i E1 M1 M' HB (X1 & X2 & _). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  pose proof (kit SPT.NUM) as (BR1 & (B0 & B1 & B2 & B3 & B4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _).
  assert (HSC : SCRC = 9968) by reflexivity.
  split; [intros a Ha; rewrite (HB a ltac:(unfold hl_ceil; lia)); exact (X1 a Ha)|].
  assert (FR : L5.frame_but [(hl_ceil L, 2 ^ 64 - hl_ceil L)] M1 M').
  { intros x Hout. rewrite <- (Z_to_bv_bv_unsigned _ x). pose proof (bv_unsigned_in_range _ x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. apply HB.
    split; [lia|]. destruct (Z_lt_dec (bv_unsigned x) (hl_ceil L)) as [Y|Y]; [exact Y|]. exfalso. apply (Hout (hl_ceil L, 2 ^ 64 - hl_ceil L) ltac:(left; reflexivity)). unfold L5.in_rng. cbn [fst snd]. lia. }
  apply (PB2.bytes_fr _ M1 M' FR); [|exact X2].
  split; [lia|]. split; [unfold hl_ceil in *; lia|]. intros j Hj w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
Qed.

Definition FRZ := kit SPT.FRZ.
Lemma NCC : ~ PML.comment_or_cr (PML.ps_st ps) /\ PML.ps_st ps <> PML.ST_STRING.
Proof. rewrite Hst. unfold PML.comment_or_cr, PML.ST_EXPECT_COMMA_OR_END, PML.ST_CR, PML.ST_STRING. split; lia. Qed.

Lemma last_stack : exists rest x, PML.ps_stack ps = rest ++ [x] /\ (x = 8 \/ x = 14) /\ exists C, PML.ps_stack ps = PML.ST_ROOT :: C /\ Forall PML.is_container C /\ Z.of_nat (length C) = level /\ 0 <= level <= 1024.
Proof.
  destruct (kit SPT.last_stack Hmore (proj1 NCC) (proj2 NCC)) as (rest & x & Hs & Hx & HC). exists rest, x. split; [exact Hs|]. split; [|exact HC].
  destruct HWF as (_ & _ & _ & _ & (C & T & _ & _ & W7)). destruct (W7 Hmore) as (_ & _ & _ & _ & W12 & _). specialize (W12 (or_introl Hst)). fold level in W12.
  destruct Hx as [(_ & Hl)|(Hx & _)]; [unfold level in *; lia | exact Hx].
Qed.

Lemma view_sound : forall cells stv E' (M' : mem), view_chk cells stv = true -> know_ok RSEGS E' M' cells -> env_agree GT.NF E0 E' ->
  L5.bytes_at RSEGS M' sb (PML.ps_stack ps) -> L5.defined M' P 272 ->
  exists buf, PML.parser_at M' P (PML.PS (uv E' stv) (PML.ps_sst ps) (PML.ps_nst ps) true (PML.ps_done ps) level (PML.ps_stack ps) sb scap bcap bptr buf mw) /\ Z.of_nat (length buf) = size0.
Proof.
  intros cells stv E' M' HV HK Hag HB HdP. unfold view_chk in HV. destruct (SPA.pview_w cells Pb PE CE) as [pv|] eqn:HPV; [|discriminate].
  apply andb_prop in HV as [HV Y12]. apply andb_prop in HV as [HV Y11]. apply andb_prop in HV as [HV Y10]. apply andb_prop in HV as [HV Y9]. apply andb_prop in HV as [HV Y8].
  apply andb_prop in HV as [HV Y7]. apply andb_prop in HV as [HV Y6]. apply andb_prop in HV as [HV Y5]. apply andb_prop in HV as [HV Y4]. apply andb_prop in HV as [HV Y3].
  apply andb_prop in HV as [Y1 Y2]. apply expr_eqb_eq in Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11, Y12.
  destruct (FRZ E' Hag) as (G2 & GP' & GE & GV & G41 & G42 & G43 & G44 & G45 & G46 & G36 & G38 & G39 & G40 & GSE & GSC & GPE & GCE & G32 & G33 & _).
  pose proof (kit SPT.NUM) as (BR1 & BR2 & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _).
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OP as (OP1 & OP2 & OP3).
  assert (HSC : SCRC = 9968) by reflexivity.
  destruct (SPA.parser_view_w E' M' cells Pb PE CE pv P true (PML.ps_done ps) (PML.ps_stack ps) scap mw HK HPV GP' ltac:(lia) ltac:(lia)) as (buf & HPA' & Hlen & _).
  - rewrite Y7. rewrite PB2.uv_lit by lia. reflexivity.
  - rewrite Y8, G46. reflexivity.
  - rewrite Y10, G38. exact HB.
  - rewrite Y11, Y10, GSE, G38. reflexivity.
  - rewrite Y12, Y10, GSC, G38. reflexivity.
  - lia.
  - rewrite Y3. exact G32.
  - rewrite Y2. exact G33.
  - exact (kit SPT.mw_le).
  - exact HdP.
  - exists buf. rewrite Y4, Y5, Y6, Y1, Y10, G43, G44, G41, G38, GCE, GPE in HPA'. rewrite Y9, G36 in Hlen. split; [exact HPA' | exact Hlen].
Qed.

Lemma leaf_know : forall c ps1 E' R' (M1 M' : mem), CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' -> know_ok RSEGS E' M' (SR.ps_cells ps1).
Proof. intros c ps1 E' R' M1 M' HLF. unfold know_ok. apply Forall_forall. intros X HX. rewrite <- LS. exact (CC.lf_cells _ _ _ _ _ _ _ HLF X HX). Qed.
Lemma cut1 : forall c, nth_error G.CPS 1 = Some c -> c = nth 1 G.CPS G.cp0.
Proof. intros c H. symmetry. exact (nth_error_nth _ _ _ H). Qed.

Lemma ghost_at : forall c E1 E' (M1 : mem), nth_error G.CPS 1 = Some c -> env_agree (CC.cp_nx c) E1 E' -> XI 1 E1 M1 ->
  exists rest x, PML.ps_stack ps = rest ++ [x] /\ uv E' GP = x.
Proof.
  intros c E1 E' M1 Hc Hag (_ & _ & X3). destruct (X3 eq_refl) as (rest & x & Hs & Hx). exists rest, x. split; [exact Hs|].
  rewrite (cut1 c Hc) in Hag. rewrite (PB.uv_agree _ E1 E' GP Hag ltac:(vm_compute; reflexivity)). exact Hx.
Qed.
Lemma ghost_val : forall c ps1 E1 E' R' (M1 M' : mem) x, nth_error G.CPS 1 = Some c -> env_agree (CC.cp_nx c) E1 E' -> XI 1 E1 M1 -> CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' ->
  PB.has (SR.ps_cells ps1) (KRange GP x x) = true -> exists rest, PML.ps_stack ps = rest ++ [x].
Proof.
  intros c ps1 E1 E' R' M1 M' x Hc Hag HX HLF Hh. destruct (ghost_at c E1 E' M1 Hc Hag HX) as (rest & x' & Hs & Hx').
  pose proof (PB.has_ok E' M' _ _ (leaf_know c ps1 E' R' M1 M' HLF) Hh) as HGK. cbn [kentry_ok] in HGK. fold (uv E' GP) in HGK. assert (Hxx : x' = x) by lia. clear Hx'. subst x'. exists rest. exact Hs.
Qed.

Lemma leaf_exit : forall c k ps1 pc stz x, is_leaf 1 c k ps1 (CC.TOther pc) -> PB.exit_base_chk GT.NF RETPC c ps1 = true -> CH2.blocks_eqb (nth 1 G.BLS []) SPT.BL0 = true ->
  PB.has (SR.ps_cells ps1) (KWord (SA Eb 0) 4 (ELit 0)) = true -> view_chk (SR.ps_cells ps1) (ELit stz) = true -> PB.has (SR.ps_cells ps1) (KRange GP x x) = true ->
  (stz = 10 /\ x = 8) \/ (stz = 13 /\ x = 14) ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok 1 c ps1.
Proof.
  intros c k ps1 pc stz x IL Hbase HBL Hec HV HGh Hsx fx' E1 R1 M1 model1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct Hentry as (Hra & Hraok & _).
  assert (HSC : SCRC = 9968) by reflexivity.
  assert (Hc : nth_error G.CPS 1 = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  apply (PB.exit_ret L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K XI DEF0 (fun _ => 0) (fun _ => 0) SCRC
           ltac:(rewrite SCRV; lia) ltac:(lia) S5 R (SPT.EV0 mw B ps R line0 pos0 [V] SPT.noeb) r Hra Hraok heap_ok3 RETPC 1%nat c k ps1 _ ret_at IL Hbase fx' E1 R1 M1 model1 E' R' M' HAt HAmb Hag HLF).
  intros HRP HP HA' HagE'.
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct OP as (OP1 & OP2 & OP3), OE as (OE1 & OE2 & OE3).
  pose proof (SPT.pa_def _ _ _ HPA) as HdefP. destruct HEC as (_ & HEd & _).
  assert (HdP' : L5.defined M' P 272) by (apply (kit SPT.amb_def GT.NF G.BLS Cred 1%nat E1 M' model1 P 272 HA' HdefP); left; lia).
  assert (HdE' : L5.defined M' E 16) by (apply (kit SPT.amb_def GT.NF G.BLS Cred 1%nat E1 M' model1 E 16 HA' HEd); left; lia).
  assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { apply (below_frame 1%nat c E' M1 M' Hc HagE'). exact (CC.lf_frame _ _ _ _ _ _ _ HLF). }
  destruct (xi_below 1%nat E1 M1 M' HLOW HX) as (HST & HBY).
  destruct (view_sound _ (ELit stz) E' M' HV HK HagE' HBY HdP') as (buf & HPA' & Hlen).
  rewrite PB2.uv_lit in HPA' by lia.
  destruct (FRZ E' HagE') as (G2 & GP' & GE & _).
  destruct (ghost_val c ps1 E1 E' R' M1 M' x Hc Hag HX HLF HGh) as (rest & Hs).
  destruct last_stack as (rest0 & x0 & Hs0 & Hx0 & (C & HSC' & HCC & HCL & HLV)).
  set (ps' := PML.PS stz (PML.ps_sst ps) (PML.ps_nst ps) true (PML.ps_done ps) level (PML.ps_stack ps) sb scap bcap bptr buf (PML.ps_win ps)).
  assert (Hden : CH2.den E1 (nth 1 G.BLS []) = PML.ps_blocks ps').
  { rewrite (CH2.blocks_eqb_eq _ _ HBL). exact (kit SPT.den_BL0 E1 ltac:(destruct HAmb as (_ & _ & X & _); exact X)). }
  pose proof HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr & Hdf). unfold Cred in HC1. subst cr1.
  unfold CH2.cur in HH1. rewrite Hden in HH1.
  apply (Hcont fx' R' M' model1 (PML.ps_blocks ps' ++ LBo) cr LBo W HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH1].
  assert (L1 : 1 <= level).
  { destruct HWF as (_ & _ & _ & _ & (C0 & T0 & _ & _ & W7)). destruct (W7 Hmore) as (_ & _ & _ & _ & W12 & _). exact (W12 (or_introl Hst)). }
  exists ps', 0, g.
  split; [exact HPA'|].
  split; [split|].
  {
    destruct HWF as (W1 & W2 & W3 & W4 & _).
    unfold PML.wf_ps, ps'. cbn [PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st PML.ps_buf].
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. exists C, []. rewrite app_nil_r. split; [exact HSC'|]. split; [exact HCC|]. intros _.
    split; [exact HCL|]. split; [exact HLV|].
    unfold PML.handled, PML.transient, PML.comment_or_cr, PML.ST_EXPECT_COMMA_OR_END, PML.ST_NUMBER, PML.ST_CR.
    split; [destruct Hsx as [(-> & _)|(-> & _)]; lia|]. split; [left; split; [reflexivity | destruct Hsx as [(-> & _)|(-> & _)]; lia]|].
    split; [intros [Hq|[]]; destruct Hsx as [(-> & _)|(-> & _)]; discriminate Hq|].
    intros Hq. destruct Hsx as [(-> & _)|(-> & _)]; discriminate Hq. }
  { apply (SCU.lvl_ok_rootc ps' C); [exact HSC' | exact HCC | intros _ _; unfold ps'; cbn [PML.ps_level]; exact L1]. }
  split.
  { apply (SPT.win_ok_tr M M' LBo ps ps' eq_refl HWIN). intros ch p n Hch C1 C2 Hwd.
    apply (kit SPT.amb_def GT.NF G.BLS Cred 1%nat E1 M' model1 p n HA' Hwd). right. exists ch. split; [exact Hch | lia]. }
  split.
  { apply (SPT.buf_bound_tr ps ps' B eq_refl); [unfold ps'; cbn [PML.ps_buf]; exact Hlen | | exact HBB].
    unfold PML.buf_need, ps'. cbn [PML.ps_more PML.ps_st PML.ps_sst]. rewrite Hmore, Hst. destruct Hsx as [(-> & _)|(-> & _)]; cbn; lia. }
  split.
  { split; [|split; [exact HdE' | left; reflexivity]].
    pose proof (PB2.kword32_elim E' M' _ _ E (PB.has_ok E' M' _ _ HK Hec)) as T. rewrite PB2.uv_lit in T by lia. apply T. unfold estart. cbn [a_base a_off]. fold (uv E' Eb). rewrite GE. lia. }
  split; [intros Hq; exfalso; apply Hq; reflexivity|].
  split; [apply (PB2.ls_ok_keep M M'); [|exact HG | exact HLS]; intros a Ha; apply HST; unfold PB2.ls_foot, PML.IMG_RO_HI in Ha; lia|].
  split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HPC|].
  split; [|exact (SCU.cur_post_more RSEGS ps ps' 0 M' V eq_refl eq_refl)].
  split; [reflexivity|]. split; [reflexivity|]. split; [|split; [reflexivity | split; reflexivity]].
  unfold ps'. cbn [PML.ps_st]. unfold PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_VALUE. destruct Hsx as [(-> & _)|(-> & _)]; [left; reflexivity | right; left; reflexivity].
Qed.

Lemma leaf_root : forall c k ps1 pc, is_leaf 1 c k ps1 (CC.TOther pc) -> PB.has (SR.ps_cells ps1) (KRange GP 0 0) = true -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok 1 c ps1.
Proof.
  intros c k ps1 pc IL HGh fx' E1 R1 M1 model1 E' R' M' HAt [HAmb HX] HFP Hag HLF _. exfalso.
  assert (Hc : nth_error G.CPS 1 = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  destruct (ghost_val c ps1 E1 E' R' M1 M' 0 Hc Hag HX HLF HGh) as (rest & Hs).
  destruct last_stack as (rest0 & x0 & Hs0 & Hx0 & _). assert (x0 = 0) by (rewrite Hs in Hs0; symmetry; exact (SPT.app_last_inj _ _ _ _ Hs0)). lia.
Qed.
Lemma leaf_dead : forall c k ps1, is_leaf 1 c k ps1 (CC.TOther DEADPC) ->
  PB.has (SR.ps_cells ps1) (sltu0 0) = true -> PB.has (SR.ps_cells ps1) (sltu0 8) = true -> PB.has (SR.ps_cells ps1) (sltu0 14) = true ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok 1 c ps1.
Proof.
  intros c k ps1 IL H0 H8 H14 fx' E1 R1 M1 model1 E' R' M' HAt [HAmb HX] HFP Hag HLF _. exfalso.
  assert (Hc : nth_error G.CPS 1 = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct (ghost_at c E1 E' M1 Hc Hag HX) as (rest & x & Hs & Hx).
  destruct last_stack as (rest0 & x0 & Hs0 & Hx0 & _). assert (x0 = x) by (rewrite Hs in Hs0; symmetry; exact (SPT.app_last_inj _ _ _ _ Hs0)). subst x0.
  assert (NE : forall cst, PB.has (SR.ps_cells ps1) (sltu0 cst) = true -> 0 <= cst < 2 ^ 64 -> x <> cst).
  { intros cst Hh Hr. pose proof (PB.has_ok E' M' _ _ HK Hh) as Q. unfold sltu0 in Q. cbn [kentry_ok] in Q. rewrite <- Hx. apply SPA.sltu_sub_ne; [|exact Hr]. unfold PB.uv. lia. }
  pose proof (NE 8 H8 ltac:(lia)). pose proof (NE 14 H14 ltac:(lia)). lia.
Qed.

Lemma leaf_parent : forall c k ps1 j cj ci, is_leaf 0 c k ps1 (CC.TOther PARENT) -> CH2.ret_of G.RETS 0 k = Some j -> nth_error G.CPS j = Some cj -> j = 1%nat -> SR.ps_pc ps1 = PARENT ->
  parent_chk c ps1 cj (nth 0 G.BLS []) (nth j G.BLS []) = Some ci -> CC.cp_nx cj = (CH2.ci_nx ci + 1 + APC.NCS)%nat ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok 0 c ps1.
Proof.
  intros c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk Hnx. unfold parent_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb HV]. apply andb_prop in Hb as [Ha0e HBL]. apply expr_eqb_eq in Ha0e.
  assert (Hc : nth_error G.CPS 0 = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  assert (HGP : GP = EVar (CH2.ci_nx ci)).
  { unfold GP. subst j. rewrite (nth_error_nth _ _ G.cp0 Hcj), Hnx. f_equal. unfold APC.NCS. lia. }
  set (nx := (CC.cp_nx cj - APC.NCS - 1)%nat) in *.
  assert (Hnxv : nx = CH2.ci_nx ci) by (unfold nx; rewrite Hnx; lia).
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K XI DEF0 CRED_BLK
           PARENT 48 1%nat [] [KRange (EVar nx) 0 255] (Some (EVar nx)) [] 0%nat c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
  - intros w a [].
  - intros E' _ w a [].
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
    pose proof (kit SPT.NUM) as (BR1 & (B0 & B1 & B2 & B3 & B4) & _).
    pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OP as (OP1 & OP2 & OP3).
    assert (HSC : SCRC = 9968) by reflexivity.
    pose proof (SPT.pa_def _ _ _ HPA) as HdefP.
    assert (HdP' : L5.defined M' P 272) by (apply (kit SPT.amb_def GT.NF G.BLS Cred 0%nat E1 M' model1 P 272 HA' HdefP); left; lia).
    assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { apply (below_frame 0%nat c E' M1 M' Hc HagE'). exact (CC.lf_frame _ _ _ _ _ _ _ HLF). }
    destruct (xi_below 0%nat E1 M1 M' HLOW HX) as (HST & HBY).
    destruct (view_sound _ (ELit 7) E' M' HV HK HagE' HBY HdP') as (buf & HPA' & Hlen).
    destruct (FRZ E' HagE') as (G2 & GP' & GE & _).
    destruct last_stack as (rest & x & Hs & Hx0 & _).
    assert (Ra0 : PML.a0 R' P).
    { unfold PML.a0. rewrite (HRL 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Ha0e.
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' Pb)). fold (uv E' Pb). rewrite GP'. reflexivity. }
    set (psx := PML.PS (uv E' (ELit 7)) (PML.ps_sst ps) (PML.ps_nst ps) true (PML.ps_done ps) level (PML.ps_stack ps) sb scap bcap bptr buf mw) in *.
    apply (PARENT_OK P x (sp + CH2.ci_csp ci) (CC.cp_pc cj) psx rest fx' R' M' model1 K Hmh Hml HKnil HFP).
    { split; [exact Hent|]. split; [exact Ra0|]. split; [exact HPA'|]. unfold psx. cbn [PML.ps_stack PML.ps_sb PML.ps_scap].
      split; [exact Hs|]. split; [unfold PML.obj_on_stack; repeat split; lia|]. split; [lia|]. split; [lia | exact B4]. }
    intros fx2 R2 M2 HFP2 Hpost HRP HFB HGR.
    apply (RET fx2 R2 M2 [Z_to_bv 64 x] eq_refl HFP2 HRP HFB HGR).
    + rewrite Hnxv. cbn [edenot]. pose proof (CH2.retEx_ghost E' (CH2.ci_nx ci) [Z_to_bv 64 x] R2 0 ltac:(cbn; lia)) as GG. rewrite Nat.add_0_r in GG. rewrite GG. exact Hpost.
    + intros X [<-|[]]. cbn [kentry_ok edenot]. rewrite Hnxv. pose proof (CH2.retEx_ghost E' (CH2.ci_nx ci) [Z_to_bv 64 x] R2 0 ltac:(cbn; lia)) as GG. rewrite Nat.add_0_r in GG. rewrite GG.
      cbn [nth]. rewrite u64_of_Z by lia. lia.
    + intros _. subst j.
      assert (HLOW2 : forall a, 0 <= a < hl_ceil L -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
      { destruct Hent as (_ & _ & _ & _ & Hstk'). pose proof (L5C.stk_window _ _ _ _ Hstk') as (SW1 & _).
        intros a Ha. apply HFB. rewrite L5.unsigned_lit by (unfold hl_ceil in *; lia). intros rg [<-|[]]. unfold L5.in_rng. cbn [fst snd]. unfold hl_ceil in *. lia. }
      assert (HX' : XI 0%nat E1 M') by (destruct (xi_below 0%nat E1 M1 M' HLOW HX) as (Q1 & Q2); split; [exact Q1 | split; [exact Q2 | intros Q; discriminate Q]]).
      destruct (xi_below 0%nat E1 M' M2 HLOW2 HX') as (Q1 & Q2). split; [exact Q1|]. split; [exact Q2|]. intros _. exists rest, x. split; [exact Hs|].
      rewrite HGP. unfold PB.uv. cbn [edenot]. pose proof (CH2.retEx_ghost E' (CH2.ci_nx ci) [Z_to_bv 64 x] R2 0 ltac:(cbn; lia)) as GG. rewrite Nat.add_0_r in GG. rewrite GG.
      cbn [nth]. apply u64_of_Z. lia.
Qed.

Lemma leaves : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. cbn [leaf_chk] in X.
  destruct (Z.eqb_spec pc PARENT) as [->|N1].
  - apply andb_prop in X as [X XR]. apply andb_prop in X as [Hpc Hi]. apply Z.eqb_eq in Hpc. apply Nat.eqb_eq in Hi. subst i.
    destruct (CH2.ret_of G.RETS 0 k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
    apply andb_prop in XR as [Hj XC]. apply Nat.eqb_eq in Hj. destruct (parent_chk c ps1 cj (nth 0 G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. apply Nat.eqb_eq in XC.
    exact (leaf_parent c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk XC).
  - destruct (Z.eqb_spec pc DEADPC) as [->|N2].
    + apply andb_prop in X as [X H14]. apply andb_prop in X as [X H8]. apply andb_prop in X as [Hi H0]. apply Nat.eqb_eq in Hi. subst i. exact (leaf_dead c k ps1 IL H0 H8 H14).
    + apply andb_prop in X as [Hi X]. apply Nat.eqb_eq in Hi. subst i. apply orb_prop in X as [X|X]; [exact (leaf_root c k ps1 pc IL X)|].
      apply andb_prop in X as [X XV]. apply andb_prop in X as [X Hec]. apply andb_prop in X as [Hbase HBL].
      apply orb_prop in XV as [XV|XV]; apply andb_prop in XV as [HV HG'].
      * exact (leaf_exit c k ps1 pc 10 8 IL Hbase HBL Hec HV HG' ltac:(left; split; reflexivity)).
      * exact (leaf_exit c k ps1 pc 13 14 IL Hbase HBL Hec HV HG' ltac:(right; split; reflexivity)).
Qed.

Lemma main : srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_BEGIN_MEMBER M model) K.
Proof.
  unfold PML.cfg. change PML.PC_BEGIN_MEMBER with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply (CH2.cert_sound3 L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 W_OK WRS_OK
            G.CPS K PML.fp_ok G.TAGS XI) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok3.
  - intros i c k ps1 j s IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. discriminate X.
  - intros i c k ps1 j s IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. discriminate X.
  - exact leaves.
  - reflexivity.
  - rewrite LS. exact At0.
  - split.
    + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr. split; [unfold CH2.cur; change (nth 0 G.BLS []) with SPT.BL0; rewrite (kit SPT.den_BL0 E0 (CC.env_agree_refl _ _)); exact HH | reflexivity].
    + split; [intros a _; reflexivity|]. split; [exact (SPT.pa_stack _ _ _ HPA) | intros Q; discriminate Q].
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
Hypothesis PARENT_OK : PMS.parent_spec L.

Theorem begin_member_ok : PMS.begin_member_spec L HI PML.STRTOD_SCR_V.
Proof.
  unfold PMS.begin_member_spec, PMS.ptrans, PMS.ptrans_g, PMS.ptrans_gb. intros LBo cr sp r P V E B kx bx g ps. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & (Ha0 & Ha1 & Hmore & Hst) & HPA & (HWF & _) & HWIN & HBB & HVIS & HEC & HLS & HG & HPC & OP & OV & OE & AP1 & AP2 & AP3) Hcont.
  pose proof (SPT.pa_def _ _ _ HPA) as HdP.
  destruct (PB2.cell_exists M (P + 160) 8 ltac:(lia)) as (line0 & Rc1 & Hc1); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  destruct (PB2.cell_exists M (P + 168) 8 ltac:(lia)) as (pos0 & Rc2 & Hc2); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  exact (main L HI HIok LAY FPM PARENT_OK LBo cr sp r P V E B kx bx g ps fx R M model K HH Hmo HKnil Hfp Hentry Ha0 Ha1 Hmore Hst HPA HWF HWIN HBB HVIS HEC HLS HG HPC OP OV OE AP1 AP2 AP3
           Hcont line0 pos0 Hc1 Hc2 (conj Rc1 Rc2)).
Qed.
End Final.
End BeginMemberProof.

