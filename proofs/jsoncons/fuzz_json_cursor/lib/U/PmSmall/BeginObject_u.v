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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallPure SmallKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmSmall Require Import SmallAt_u SmallPt_u SmallCur_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import VisitSums.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_begin_object_csrc_T_u Cut_begin_object_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module BeginObjectProof.
Module G := Cut_begin_object_csrc_u.
Module GT := Cut_begin_object_csrc_T_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Definition KIND : Z := PML.ST_OBJECT.
Definition STNEW : Z := PML.ST_EXPECT_MEMBER_NAME_OR_END.
Definition PCF : Z := PML.PC_BEGIN_OBJECT.

Definition VISPC : Z := PMS.PC_VIS_BEGIN_OBJECT_TAG.
Definition VFLAGS : Z := 256.
Definition VEV : PMCUR.sevent := PMCUR.EvBeginObj.
Definition Pb : expr := EVar 10.  Definition Vb : expr := EVar 11.  Definition Eb : expr := EVar 12.
Definition RETPC : Z := nth 0 GT.ENDS 0.
Definition VECPUSH : Z := PML.PC_VEC_PUSH.
Definition SETEC : Z := PML.PC_SET_EC.
Definition SCR : Z := CH.hd_scr G.HDECL.
Definition CONSTS : PSK.consts := PSK.CONSTS PML.VT_PARSER PML.VT_FUNC PML.VT_VISITOR 0x10000 0xf8000 0x10000 PML.IMG_RO_HI SCR [(-8, 1%nat); (-16, 8%nat); (-24, 9%nat); (-32, 18%nat)] 32.
Definition X0 : PSK.pexprs := SPT.X0 (EVar 42) (ELit 1).
Lemma kn0_eq : CC.cp_know G.cp0 = SPK.kn CONSTS false Pb Vb Eb (EVar 2) (EVar 33) X0.
Proof. vmc_refl. Qed.
Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Abbreviation PE := SPT.PE.  Abbreviation CE := SPT.CE.

Definition jof (pc : Z) : nat := match find (fun r : nat * nat * nat * Z => let '(_, _, _, p) := r in Z.eqb p pc) G.RETS with Some (j, _, _, _) => j | None => 0%nat end.
Definition JPUSH : nat := Eval vm_compute in jof VECPUSH.
Definition JSETEC : nat := Eval vm_compute in jof SETEC.
Definition JVIS : nat := Eval vm_compute in jof VISPC.

Definition NXG : nat := (CC.cp_nx (nth JPUSH G.CPS G.cp0) - APC.NCS - 2)%nat.
Definition GB : expr := EVar NXG.  Definition GC : expr := EVar (NXG + 1).
Definition BL1 : CA.blocks := [(PE, CE); (GB, GC)].
Definition LVL1 : expr := APC.eaddz (EVar 41) 1.
Definition SEND0 : expr := APC.eadd (EVar 38) (EVar 39).
Definition SEND1 : expr := APC.eaddz (APC.eadd (EVar 39) GB) 1.

Definition view_chk (cells : list kentry) (lvl stv morev sbv sendv scendv : expr) : bool :=
  match SPA.pview_w cells Pb PE CE with
  | Some pv => (expr_eqb (PB4.pv_level pv) lvl && expr_eqb (PB4.pv_wend pv) (EVar 33) && expr_eqb (PB4.pv_wptr pv) (EVar 32) && expr_eqb (PB4.pv_st pv) stv
                && expr_eqb (PB4.pv_sst pv) (EVar 43) && expr_eqb (PB4.pv_nst pv) (EVar 44) && expr_eqb (PB4.pv_more pv) morev && expr_eqb (PB4.pv_done pv) (EVar 46)
                && expr_eqb (PB4.pv_size pv) (EVar 36) && expr_eqb (PB4.pv_sb pv) sbv && expr_eqb (PB4.pv_send pv) sendv && expr_eqb (PB4.pv_scend pv) scendv)%bool
  | None => false
  end.

Definition xcell_chk (cells : list kentry) : bool :=
  forallb (fun X => match X with KWord (SA (EVar 2) _) 1%nat v => expr_eqb v (ELit KIND) | _ => true end) cells.
Definition push_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : bool :=
  let cells := SR.ps_cells ps in
  match PB4.vecpush_chk GT.NF G.HDECL Pb 248 c ps cj BLi BLj with
  | Some ci => (xcell_chk cells && PB.has cells (KRange (EVar 41) 0 1023) && CH2.blocks_eqb BLi SPT.BL0 && CH2.blocks_eqb BLj BL1
                && match CAX.cell_at cells Pb (248 + 8) 8 with Some c8 => expr_eqb c8 SEND0 | None => false end)%bool
  | None => false
  end.
Definition setec_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (expr_eqb (nth 10 regs (ELit 0)) Eb && expr_eqb (nth 11 regs (ELit 0)) (ELit 5) && CH2.blocks_eqb BLj BLi)%bool
  then CH2.custom_chk GT.NF G.HDECL 256 0 BLi ((Eb, 0, ELit 16) :: PSU.statics_wregs) (PSU.setec_news Eb 0 (ELit 5)) (Some Eb) c ps cj BLi
  else None.

Definition vis_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (expr_eqb (nth 10 regs (ELit 0)) Vb && CH2.blocks_eqb BLj BLi && PB.has (SR.ps_cells ps) (KWord (SA Vb 0) 8 (ELit PML.VT_VISITOR)))%bool
  then CH2.custom_chk GT.NF G.HDECL PMS.VIS_SCR 0 BLi [(Vb, 8, ELit 40)] (VSU.const_news Vb 0 VFLAGS) (Some (ELit 1)) c ps cj BLi
  else None.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc VISPC then
        (Z.eqb (SR.ps_pc ps) VISPC && Nat.eqb i JPUSH &&
         match CH2.ret_of G.RETS i k with
         | Some j => match nth_error G.CPS j with
                     | Some cj => (Nat.eqb j JVIS && match vis_chk c ps cj (nth i G.BLS []) (nth j G.BLS []) with Some ci => Nat.leb (CC.cp_nx c) (CH2.ci_nx ci) | None => false end)%bool
                     | None => false end
         | None => false end)%bool
      else if (Z.eqb pc VECPUSH || Z.eqb pc SETEC)%bool then
        (Z.eqb (SR.ps_pc ps) pc && Nat.eqb i 0 &&
         match CH2.ret_of G.RETS i k with
         | Some j => match nth_error G.CPS j with
                     | Some cj => if Z.eqb pc VECPUSH then (Nat.eqb j JPUSH && push_chk c ps cj (nth i G.BLS []) (nth j G.BLS []))%bool
                                  else (Nat.eqb j JSETEC && match setec_chk c ps cj (nth i G.BLS []) (nth j G.BLS []) with Some ci => Nat.leb GT.NF (CH2.ci_nx ci) | None => false end)%bool
                     | None => false end
         | None => false end)%bool
      else (PB.exit_base_chk GT.NF RETPC c ps &&
            ((Nat.eqb i JVIS && CH2.blocks_eqb (nth i G.BLS []) BL1 && PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) && view_chk cells LVL1 (ELit STNEW) (ELit 0) GB SEND1 (APC.eadd GB GC) && PB.has cells (KRange (EVar 41) 0 1023)
              && PB.has cells (VSU.fl Vb 0 VFLAGS))
             || (Nat.eqb i JSETEC && CH2.blocks_eqb (nth i G.BLS []) SPT.BL0 && PB.has cells (KWord (SA Eb 0) 4 (ELit 5)) && PB.has cells (KWord (SA Eb 8) 8 (ELit PML.OBJ_JSON_CATEGORY))
                 && view_chk cells LVL1 (EVar 42) (ELit 0) (EVar 38) SEND0 (APC.eadd (EVar 38) (EVar 40)) && PB.has cells (KRange (EVar 41) 1024 1025))))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Definition F0 : list SGP.region := [(EVar 2, - SCR, ELit SCR); (Pb, 0, ELit 272)].
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
Hypothesis VECPUSH_OK : PMS.vec_push_spec L HI.
Hypothesis SETEC_OK : PMS.set_ec_spec L.
Hypothesis VIS_OK : PMS.visit_begin_object_spec L VISPC.
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
Hypothesis Ha1 : PML.a1 R V.
Hypothesis Ha2 : PML.a2 R E.
Hypothesis Hmore : PML.ps_more ps = true.
Hypothesis Hncc : ~ PML.comment_or_cr (PML.ps_st ps).
Hypothesis Hnstr : PML.ps_st ps <> PML.ST_STRING.
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
      ((code = 0 /\ PML.ps_level ps' = PML.ps_level ps + 1 /\ PML.ps_st ps' = STNEW /\ PML.ps_more ps' = false /\ PML.ps_stack ps' = PML.ps_stack ps ++ [KIND] /\ PML.ps_win ps' = PML.ps_win ps)
       \/ (code = 5 /\ PML.ps_level ps = 1024)) /\ PMCUR.cur_post RSEGS ps ps' code M' V) ->
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
Definition E0 : env := SPT.E0 mw B ps R line0 pos0 [] SPT.noeb.

Lemma ps_mw : PML.ps_set_win ps mw = ps.
Proof. unfold mw. destruct ps; reflexivity. Qed.
Lemma SCRV : CH.hd_scr G.HDECL = 8416.
Proof. reflexivity. Qed.
Lemma WFM : Z.of_nat (length (PML.ps_stack ps)) = level + 1 /\ 0 <= level <= 1024 /\ PML.handled (PML.ps_st ps) /\ In scap [66; 132; 264; 528; 1056] /\
  exists C, PML.ps_stack ps = PML.ST_ROOT :: C /\ Forall PML.is_container C /\ Z.of_nat (length C) = level.
Proof.
  pose proof HWF as (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)). destruct (W7 Hmore) as (W8 & W9 & W10 & W11 & _).
  assert (HT : T = []).
  { unfold PML.transient in W11. destruct W11 as [(HT & _)|[(_ & X)|[(S & _ & _ & X)|(S & _ & _ & X)]]]; [exact HT | contradiction | contradiction |]. exfalso. apply Hncc. right. exact X. }
  subst T. rewrite app_nil_r in W5. fold level in W8, W9.
  split; [rewrite W5; cbn [length]; lia|]. split; [exact W9|]. split; [exact W10|]. split; [exact W4|]. exists C. split; [exact W5|]. split; [exact W6 | exact W8].
Qed.

Lemma INST : SPT.inst L HI mw LBo cr sp r P V E B kx bx g ps R M model SCRC G.HDECL Pb Vb Eb line0 pos0 [] SPT.noeb.
Proof.
  unfold SPT.inst. destruct Hlpr as (Q1 & Q2). pose proof WFM as (F1 & F2 & F3 & F4 & _).
  destruct Hentry as (_ & _ & Hsp & _ & Hstk). pose proof (L5C.stk_floor _ _ _ _ Hstk) as FL. pose proof Hstk as (S1 & S2 & S3 & S4 & S5).
  destruct OP as (OP1 & OP2 & OP3), OV as (OV1 & OV2 & OV3), OE as (OE1 & OE2 & OE3).
  assert (HSC : SCRC = 9968) by reflexivity.
  split; [exact HIok|]. split; [exact LAY|]. split; [exact HH|]. split; [exact Hentry|]. split; [rewrite SCRV; lia|]. split; [lia|].
  split; [rewrite ps_mw; exact HPA|]. split; [exact (PML.wf_ps_stale_of ps HWF)|]. split; [unfold level in *; lia|].
  split.
  { destruct HBB as (HB1 & HB2). pose proof (SPT.win_le M P ps HPA) as HWL. unfold PML.winlen, PML.buf_need in HB1.
    destruct (Z.eqb_spec (PML.ps_st ps) PML.ST_STRING) as [Q|_]; [contradiction|]. rewrite Bool.andb_false_r in HB1. destruct (PML.ps_win ps) as [[p e]|]; lia. }
  split; [unfold PML.handled in F3; lia|].
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
  apply (kit SPT.kn_ok CONSTS (EVar 42) (ELit 1) eq_refl eq_refl eq_refl (conj eq_refl eq_refl) (conj eq_refl eq_refl) eq_refl).
  - destruct (kit SPT.FRZ E0 (CC.env_agree_refl _ _)) as (_ & _ & _ & _ & _ & G42 & _). exact G42.
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

Definition scap_of (i : nat) (E1 : env) : Z := snd (nth 1 (CH2.den E1 (nth i G.BLS [])) (0, 0)).
Definition Cred (i : nat) (E1 : env) (cr1 : credit) : Prop := PPS.bufcred L cr1 bcap (PPS.stk_kx L (scap_of i E1) + kx) (PPS.stk_bx L (scap_of i E1) + bx).
Lemma CRED_BLK : forall i j E1 E2 cr1, CH2.den E2 (nth j G.BLS []) = CH2.den E1 (nth i G.BLS []) -> Cred i E1 cr1 -> Cred j E2 cr1.
Proof. intros i j E1 E2 cr1 Hd H. unfold Cred, scap_of in *. rewrite Hd. exact H. Qed.
Lemma cred_pc : forall i E1 cr1 ps1, CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps1 -> PML.ps_bcap ps1 = bcap -> In (PML.ps_scap ps1) [66; 132; 264; 528; 1056] ->
  (Cred i E1 cr1 <-> PML.pcredit_x L cr1 ps1 kx bx).
Proof.
  intros i E1 cr1 ps1 Hd Hb Hs. unfold Cred, scap_of. rewrite Hd. cbn [PML.ps_blocks nth snd]. rewrite <- Hb.
  destruct HPC as (K0 & B0 & _). symmetry. exact (PPS.pcredit_x_bufcred L cr1 ps1 kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) Hs K0 B0).
Qed.

Definition XI0 (M1 : mem) : Prop := (forall a, PB2.ls_foot a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\ L5.bytes_at RSEGS M1 sb (PML.ps_stack ps).
Definition XIP (E1 : env) (M1 : mem) : Prop :=
  (forall a, PB2.ls_foot a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\
  exists b' cap', CH2.den E1 (nth JPUSH G.BLS []) = [(bptr, bcap); (b', cap')] /\ L5.bytes_at RSEGS M1 b' (PML.ps_stack ps ++ [KIND]) /\ In cap' [66; 132; 264; 528; 1056] /\ slen + 1 <= cap'.
Definition XIS (M1 : mem) : Prop := PML.ls_ok (PML.regJ g) M1 /\ L5.bytes_at RSEGS M1 sb (PML.ps_stack ps).
Definition XI (i : nat) (E1 : env) (M1 : mem) : Prop := if Nat.eqb i 0 then XI0 M1 else if (Nat.eqb i JPUSH || Nat.eqb i JVIS)%bool then XIP E1 M1 else XIS M1.

Lemma bls_vis : nth JVIS G.BLS [] = nth JPUSH G.BLS [].
Proof. vmc_refl. Qed.
Lemma xi0 : forall E1 M1, XI 0 E1 M1 = XI0 M1.
Proof. reflexivity. Qed.
Lemma xi_push : forall E1 M1, XI JPUSH E1 M1 = XIP E1 M1.
Proof. reflexivity. Qed.
Lemma xi_vis : forall E1 M1, XI JVIS E1 M1 = XIP E1 M1.
Proof. reflexivity. Qed.
Lemma xi_setec : forall E1 M1, XI JSETEC E1 M1 = XIS M1.
Proof. reflexivity. Qed.

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
Lemma need0 : PML.buf_need ps = 0.
Proof. unfold PML.buf_need. destruct (Z.eqb_spec (PML.ps_st ps) PML.ST_STRING) as [Q|_]; [contradiction|]. rewrite Bool.andb_false_r. reflexivity. Qed.
Lemma VADDR : estart E0 (SA Pb 248) = P + 248.
Proof. unfold estart. cbn [a_base a_off]. fold (uv E0 Pb). unfold E0. rewrite (proj1 (proj2 (kit SPT.UU))). reflexivity. Qed.
Lemma VOBJ : sp <= P + 248 /\ P + 248 + 24 <= hl_sptop L /\ (P + 248) mod 8 = 0 /\ (forall a, P + 248 <= a < P + 248 + 24 -> exists w, In w W /\ L5.in_rng w a).
Proof.
  destruct OP as (O1 & O2 & O3). split; [lia|]. split; [lia|]. split; [rewrite Z.add_mod by lia; rewrite O3; reflexivity|].
  intros a Ha. exists (P, 272). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
Qed.
Lemma amb_agree : forall i E1 (M1 : mem) model1, HAMB i E1 M1 model1 -> env_agree GT.NF E0 E1.
Proof. intros i E1 M1 model1 (_ & _ & X & _). exact X. Qed.

Lemma leaf_push : forall c k ps1 j cj, is_leaf 0 c k ps1 (CC.TOther VECPUSH) -> CH2.ret_of G.RETS 0 k = Some j -> nth_error G.CPS j = Some cj -> j = JPUSH -> SR.ps_pc ps1 = VECPUSH ->
  push_chk c ps1 cj (nth 0 G.BLS []) (nth j G.BLS []) = true -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok 0 c ps1.
Proof.
  intros c k ps1 j cj IL Hret Hcj Hj Hpc Hchk. unfold push_chk in Hchk. destruct (PB4.vecpush_chk _ _ _ _ _ _ _ _ _) as [ci|] eqn:HVC; [|discriminate].
  apply andb_prop in Hchk as [Hchk Hc8]. apply andb_prop in Hchk as [Hchk HB1]. apply andb_prop in Hchk as [Hchk HB0]. apply andb_prop in Hchk as [Hx Hlv].
  apply CH2.blocks_eqb_eq in HB0, HB1.
  assert (Hc : nth_error G.CPS 0 = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  apply (PB4.vecpush_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K HKnil XI DEF0
           Pb 248 eq_refl (P + 248) VADDR VOBJ VECPUSH_OK 0%nat c k ps1 j cj ci IL Hret Hcj Hpc HVC).
  intros E1 E' R' M1 M' model1 cr1 b1 sbe sce c8 xv xk HagE' Hag HLF HA' HX HBL Hcell8 Hcellx HH1 HC1.
  rewrite HB0 in HBL. unfold SPT.BL0 in HBL. injection HBL as <- <- <-.
  rewrite Hcell8 in Hc8. apply expr_eqb_eq in Hc8. subst c8.
  destruct (PB.cell_at_has _ _ _ _ _ Hcellx) as (b0 & Hin & ->). unfold xcell_chk in Hx. rewrite forallb_forall in Hx. specialize (Hx _ Hin). cbv beta iota in Hx. apply expr_eqb_eq in Hx. subst xv.
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & G42 & G43 & G44 & G45 & G46 & G36 & G38 & G39 & G40 & GSE & GSC & GPE & GCE & G32 & G33 & _).
  pose proof WFM as (F1 & F2 & F3 & F4 & C & HSC & HCC & HCL).
  pose proof (kit SPT.NUM) as (BR1 & (B0 & B1 & B2 & B3 & B4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _).
  assert (HL : level <= 1023).
  { pose proof (PB.has_ok E' M' _ _ HK Hlv) as Q. cbn [kentry_ok] in Q. fold (uv E' (EVar 41)) in Q. rewrite G41 in Q. unfold level. lia. }
  assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame 0%nat c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
  rewrite xi0 in HX. destruct HX as (HS & HBY).
  assert (Hden1 : CH2.den E1 (nth 0 G.BLS []) = PML.ps_blocks ps) by (rewrite HB0; exact (kit SPT.den_BL0 E1 (amb_agree _ _ _ _ HA'))).
  assert (HC1' : PPS.bufcred L cr1 bcap (PPS.stk_kx L scap + kx) (PPS.stk_bx L scap + bx)) by (unfold Cred, scap_of in HC1; rewrite Hden1 in HC1; exact HC1).
  destruct HPC as (K0 & B0' & _).
  assert (GROW : Z.of_nat (length (PML.ps_stack ps)) = scap -> In scap [66; 132; 264; 528]) by (intros Q; cbn [In] in F4 |- *; unfold level, scap in *; lia).
  exists (PML.ps_stack ps).
  split; [rewrite G38; apply (kit SPT.bytes_below M1 M' sb scap (PML.ps_stack ps) HLOW ltac:(lia) B4 ltac:(unfold slen in N4; lia) HBY)|].
  split; [unfold SEND0; rewrite GSE, G38; reflexivity|].
  split; [unfold level in *; lia|].
  split; [rewrite G40; unfold slen in N4; lia|].
  split; [rewrite G40; exact F4|].
  split; [rewrite G40; intros Q; exact (proj1 (PSS.stk_grow L cr1 bcap scap kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) K0 B0' (GROW Q) HC1'))|].
  intros E2 M2 LBk spc b2 cap2 cr2 Hag2 HP Hincl Hby Hden2 Hcase. subst j. cbn [fst snd] in Hden2. fold (uv E' PE) (uv E' CE) in Hden2. rewrite GPE, GCE in Hden2.
  rewrite G40, G38 in Hcase.
  split.
  - rewrite xi_push. split.
    + intros a Ha. rewrite <- (HS a Ha), <- (HLOW a (foot_low a Ha)). apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). apply (kit SPT.lsfoot_kept).
      * exact Ha.
      * intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. pose proof (foot_low a Ha) as Q. pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OP as (O1 & _). unfold hl_ceil in *. lia.
    + exists b2, cap2. split; [exact Hden2|]. split; [rewrite PB2.uv_lit in Hby by (unfold KIND, PML.ST_OBJECT, PML.ST_ARRAY; lia); exact Hby|].
      split; [destruct Hcase as [(_ & -> & _ & _)|(-> & _ & Q)]; [exact F4|]; specialize (GROW Q); cbn [In] in GROW |- *; lia|].
      unfold slen. destruct Hcase as [(_ & -> & _ & Q)|(-> & _ & Q)]; lia.
  - unfold Cred, scap_of. rewrite Hden2. cbn [nth snd].
    destruct Hcase as [(_ & -> & -> & _)|(-> & -> & Q)]; [exact HC1'|].
    exact (proj2 (PSS.stk_grow L cr1 bcap scap kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) K0 B0' (GROW Q) HC1')).
Qed.

Lemma leaf_setec : forall c k ps1 j cj ci, is_leaf 0 c k ps1 (CC.TOther SETEC) -> CH2.ret_of G.RETS 0 k = Some j -> nth_error G.CPS j = Some cj -> j = JSETEC -> SR.ps_pc ps1 = SETEC ->
  setec_chk c ps1 cj (nth 0 G.BLS []) (nth j G.BLS []) = Some ci -> (GT.NF <= CH2.ci_nx ci)%nat -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok 0 c ps1.
Proof.
  intros c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk Hnx. unfold setec_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb HBL]. apply andb_prop in Hb as [Ha0e Ha1e]. apply expr_eqb_eq in Ha0e, Ha1e.
  assert (Hc : nth_error G.CPS 0 = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OE as (OE1 & OE2 & OE3).
  assert (ESE : forall Ex, env_agree GT.NF E0 Ex -> forall q, estart Ex (SA Eb q) = E + q).
  { intros Ex Hx q. destruct (FRZ Ex Hx) as (_ & _ & GE & _). unfold estart. cbn [a_base a_off]. fold (uv Ex Eb). rewrite GE. reflexivity. }
  assert (ESL : forall Ex z, 0 <= z < 2 ^ 63 -> estart Ex (SA (ELit 0) z) = z) by (intros Ex z Hz; unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; lia).
  assert (ELN : forall Ex z, 0 <= z < 2 ^ 64 -> elenZ Ex (ELit z) = z) by (intros Ex z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K XI DEF0 CRED_BLK
           SETEC 256 0%nat ((Eb, 0, ELit 16) :: PSU.statics_wregs) (PSU.setec_news Eb 0 (ELit 5)) (Some Eb) [(E, 16); (0xd4df8, 2); (0xf6848, 544)] 0%nat c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
  - intros w a Hw Hin. exists w. split; [|exact Hin]. unfold W, PMS.W_parc, PML.W_par. cbn [In app] in Hw |- *. tauto.
  - intros E' HagE' w a Hw Hin. unfold L5.in_rng in Hin. destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hin.
    + exists (Eb, 0, ELit 16). split; [left; reflexivity|]. unfold CH2.in_reg. rewrite (ESE E' HagE' 0), (ELN E' 16 ltac:(lia)). lia.
    + exists (ELit 0, 0xd4df8, ELit 2). split; [right; left; reflexivity|]. unfold CH2.in_reg. rewrite (ESL E' 0xd4df8 ltac:(lia)), (ELN E' 2 ltac:(lia)). lia.
    + exists (ELit 0, 0xf6848, ELit 544). split; [right; right; left; reflexivity|]. unfold CH2.in_reg. rewrite (ESL E' 0xf6848 ltac:(lia)), (ELN E' 544 ltac:(lia)). lia.
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    pose proof (kit SPT.NUM) as (BR1 & (B0 & B1 & B2 & B3 & B4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _).
    destruct (FRZ E' HagE') as (G2 & GP' & GE & _). destruct HEC as (_ & HEd & _).
    assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame 0%nat c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
    rewrite xi0 in HX. destruct HX as (HS & HBY).
    assert (HLS' : PML.ls_ok g M') by (apply (PB2.ls_ok_keep M M'); [|exact HG | exact HLS]; intros a Ha; rewrite (HLOW a (foot_low a Ha)); exact (HS a Ha)).
    assert (HdE' : L5.defined M' E 16) by (apply (kit SPT.amb_def GT.NF G.BLS Cred 0%nat E1 M' model1 E 16 HA' HEd); left; lia).
    assert (Ra0 : PML.a0 R' E).
    { unfold PML.a0. rewrite (HRL 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Ha0e.
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' Eb)). fold (uv E' Eb). rewrite GE. reflexivity. }
    assert (Ra1 : PML.a1 R' 5).
    { unfold PML.a1. rewrite (HRL 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Ha1e. reflexivity. }
    apply (SETEC_OK E 5 (sp + CH2.ci_csp ci) (CC.cp_pc cj) g fx' R' M' model1 K Hmh Hml HKnil HFP).
    { split; [exact Hent|]. split; [exact Ra0|]. split; [exact Ra1|]. split; [lia|]. split; [exact HdE'|]. split; [unfold PML.obj_on_stack; lia|]. split; [exact HLS' | exact HG]. }
    intros fx2 R2 M2 HFP2 (Hec & Hls2 & Ha0') HRP HFB HGR.
    set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
    assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [apply CH2.retEx_agree | exact Hnx]]).
    apply (RET fx2 R2 M2 [] eq_refl HFP2 HRP HFB HGR).
    + fold E2. destruct (FRZ E2 HagE2) as (_ & _ & GE2 & _). rewrite Ha0'. rewrite <- (Z_to_bv_bv_unsigned _ (edenot E2 Eb)). fold (uv E2 Eb). rewrite GE2. reflexivity.
    + fold E2. intros X HXin. destruct Hec as (Hu32 & _ & Hcat). rewrite LS. destruct HXin as [<-|[<-|[]]].
      * eapply PB.kword32_intro with (A := E) (z := 5); [rewrite (ESE E2 HagE2 0); lia | lia | lia | reflexivity | exact Hu32].
      * destruct Hcat as [Hz|[_ Hcat]]; [lia|].
        eapply CL5.kword64_intro with (A := E + 8) (z := PML.OBJ_JSON_CATEGORY); [exact (ESE E2 HagE2 8) | lia | lia | reflexivity | exact Hcat].
    + intros _. subst j. rewrite xi_setec. split; [exact Hls2|].
      pose proof (kit SPT.bytes_below M1 M' sb scap (PML.ps_stack ps) HLOW ltac:(lia) B4 ltac:(unfold slen in N4; lia) HBY) as HBY'.
      apply (PB2.bytes_fr _ M' M2 HFB); [|exact HBY'].
      destruct Hent as (_ & _ & _ & _ & Hstk'). pose proof (L5C.stk_window _ _ _ _ Hstk') as (SW1 & _).
      rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in B1.
      split; [lia|]. split; [unfold hl_ceil in *; lia|]. intros q Hq w Hw. unfold L5.in_rng. unfold slen in N4. unfold hl_ceil in *.
      destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PMS.SETEC_SCR; lia.
Qed.

Lemma leaf_vis : forall c k ps1 j cj ci, is_leaf JPUSH c k ps1 (CC.TOther VISPC) -> CH2.ret_of G.RETS JPUSH k = Some j -> nth_error G.CPS j = Some cj -> j = JVIS -> SR.ps_pc ps1 = VISPC ->
  vis_chk c ps1 cj (nth JPUSH G.BLS []) (nth j G.BLS []) = Some ci -> (CC.cp_nx c <= CH2.ci_nx ci)%nat -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok JPUSH c ps1.
Proof.
  intros c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk Hnx. unfold vis_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb Hvt]. apply andb_prop in Hb as [Ha0e HBL]. apply expr_eqb_eq in Ha0e.
  assert (Hc : nth_error G.CPS JPUSH = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  assert (Hc' : c = nth JPUSH G.CPS G.cp0) by exact (eq_sym (nth_error_nth _ _ G.cp0 Hc)).
  assert (HNF : (GT.NF <= CC.cp_nx c)%nat) by (rewrite Hc'; vm_compute; lia).
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OV as (OV1 & OV2 & OV3).
  assert (ESV : forall Ex, env_agree GT.NF E0 Ex -> forall q, estart Ex (SA Vb q) = V + q).
  { intros Ex Hx q. destruct (FRZ Ex Hx) as (_ & _ & _ & GV & _). unfold estart. cbn [a_base a_off]. fold (uv Ex Vb). rewrite GV. reflexivity. }
  assert (ELN : forall Ex z, 0 <= z < 2 ^ 64 -> elenZ Ex (ELit z) = z) by (intros Ex z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K XI DEF0 CRED_BLK
           VISPC PMS.VIS_SCR 0%nat [(Vb, 8, ELit 40)] (VSU.const_news Vb 0 VFLAGS) (Some (ELit 1)) [(V + 8, 40)] JPUSH c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
  - intros w a [<-|[]] Hin. exists (V + 8, 40). split; [unfold W, PMS.W_parc, PML.W_par; cbn [app]; right; right; right; right; left; reflexivity | exact Hin].
  - intros E' HagE' w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (Vb, 8, ELit 40). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite (ESV E' HagE' 8), (ELN E' 40 ltac:(lia)). lia.
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
    destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & _).
    assert (Ra0 : PML.a0 R' V).
    { unfold PML.a0. rewrite (HRL 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Ha0e.
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' Vb)). fold (uv E' Vb). rewrite GV. reflexivity. }
    assert (HVT : PML.u64 M' V PML.VT_VISITOR).
    { pose proof (PB2.kword64_elim E' M' _ _ V (PB.has_ok E' M' _ _ HK Hvt)) as T. rewrite PB2.uv_lit in T by (unfold PML.VT_VISITOR; lia). apply T. rewrite (ESV E' HagE' 0). lia. }
    assert (HdV' : L5.defined M' V 48) by (apply (kit SPT.amb_def GT.NF G.BLS Cred JPUSH E1 M' model1 V 48 HA' (proj2 HVIS)); left; lia).
    assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame JPUSH c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
    apply (VIS_OK V (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model1 K Hmh Hml HKnil HFP).
    { split; [exact Hent|]. split; [exact Ra0|]. split; [split; [exact HVT | exact HdV']|]. split; [unfold PML.obj_on_stack; repeat split; lia | exact I]. }
    intros fx2 R2 M2 HFP2 (Ha0' & e & He & Hev) HRP HFB HGR. subst e.
    set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
    assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [apply CH2.retEx_agree | lia]]).
    assert (HLOW2 : forall a, 0 <= a < hl_ceil L -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
    { destruct Hent as (_ & _ & _ & _ & Hstk'). pose proof (L5C.stk_window _ _ _ _ Hstk') as (SW1 & _).
      intros a Ha. apply HFB. rewrite L5.unsigned_lit by (unfold hl_ceil in *; lia). intros rg [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; unfold hl_ceil, PMS.VIS_SCR in *; lia. }
    apply (RET fx2 R2 M2 [] eq_refl HFP2 HRP HFB HGR).
    + cbn [edenot]. unfold PML.a0 in Ha0'. exact Ha0'.
    + intros X [<-|[]]. destruct Hev as (_ & Hfl). rewrite LS. unfold VSU.const_news, VSU.fl.
      eapply CL5.kword64_intro with (A := V + 8) (z := VFLAGS); [rewrite (ESV E2 HagE2); lia | lia | lia | reflexivity | exact Hfl].
    + intros _. subst j. rewrite xi_vis. rewrite xi_push in HX. destruct HX as (HS & b' & cap' & Hden & Hby & Hcin & Hcap).
      split; [intros a Ha; rewrite (HLOW2 a (foot_low a Ha)), (HLOW a (foot_low a Ha)); exact (HS a Ha)|].
      exists b', cap'. split.
      { assert (Hagg : env_agree (CC.cp_nx c) E1 E2) by (eapply CC.env_agree_trans; [exact Hag | eapply CC.env_agree_le; [apply CH2.retEx_agree | exact Hnx]]).
        rewrite (CH2.den_agree (CC.cp_nx c) E1 E2 _ Hagg); [exact Hden|]. rewrite Hc'. vm_compute. reflexivity. }
      split; [|split; [exact Hcin | exact Hcap]].
      pose proof HA' as (_ & _ & _ & (cr1 & HH1 & _) & _ & _). destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _).
      assert (Hinb : In (b', cap') (CH2.cur LBo G.BLS JPUSH E1)) by (unfold CH2.cur; apply in_or_app; left; rewrite Hden; right; left; reflexivity).
      destruct (Hwf _ Hinb) as ((B0 & B1 & B2 & B3 & B4) & _). cbn [fst snd] in B0, B1, B2, B3, B4.
      assert (Hlen1 : Z.of_nat (length (PML.ps_stack ps ++ [KIND])) = slen + 1) by (rewrite length_app; cbn [length]; unfold slen; lia).
      apply (kit SPT.bytes_below M' M2 b' cap' _ HLOW2 ltac:(lia) B4 ltac:(rewrite Hlen1; lia)).
      apply (kit SPT.bytes_below M1 M' b' cap' _ HLOW ltac:(lia) B4 ltac:(rewrite Hlen1; lia) Hby).
Qed.

Lemma exit_gen : forall i c k ps1 pc lvl stv morev sbv sendv scendv,
  is_leaf i c k ps1 (CC.TOther pc) -> PB.exit_base_chk GT.NF RETPC c ps1 = true -> view_chk (SR.ps_cells ps1) lvl stv morev sbv sendv scendv = true ->
  (forall E1 E' R' (M1 M' : mem) model1, env_agree (CC.cp_nx c) E1 E' -> CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' -> XI i E1 M1 -> HAMB i E1 M' model1 -> env_agree GT.NF E0 E' ->
      L5.defined M' E 16 ->
      exists (more' : bool) (stack' : list Z) (scap' code : Z) (g' : PML.ls_state),
        uv E' morev = PML.b2z more' /\ L5.bytes_at RSEGS M' (uv E' sbv) stack' /\ uv E' sendv = uv E' sbv + Z.of_nat (length stack') /\ uv E' scendv = uv E' sbv + scap' /\
        Z.of_nat (length stack') <= scap' /\ In scap' [66; 132; 264; 528; 1056] /\
        PML.ec_at M' E code /\ (code <> 0 -> more' = false) /\ PML.ls_ok g' M' /\ (g' = g \/ g' = PML.regJ g /\ code <> 0) /\
        CH2.den E1 (nth i G.BLS []) = [(bptr, bcap); (uv E' sbv, scap')] /\
        forall buf, let ps' := PML.PS (uv E' stv) (PML.ps_sst ps) (PML.ps_nst ps) more' (PML.ps_done ps) (uv E' lvl) stack' (uv E' sbv) scap' bcap bptr buf (PML.ps_win ps) in
          PMCUR.wf_c ps' /\ PML.buf_need ps' = 0 /\
          ((code = 0 /\ PML.ps_level ps' = PML.ps_level ps + 1 /\ PML.ps_st ps' = STNEW /\ PML.ps_more ps' = false /\ PML.ps_stack ps' = PML.ps_stack ps ++ [KIND] /\ PML.ps_win ps' = PML.ps_win ps)
           \/ (code = 5 /\ PML.ps_level ps = 1024)) /\ PMCUR.cur_post RSEGS ps ps' code M' V) ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc lvl stv morev sbv sendv scendv IL Hbase HV HKIND fx' E1 R1 M1 model1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct Hentry as (Hra & Hraok & _).
  assert (HSC : SCRC = 9968) by reflexivity.
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  apply (PB.exit_ret L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K XI DEF0 (fun _ => 0) (fun _ => 0) SCRC
           ltac:(rewrite SCRV; lia) ltac:(lia) S5 R (SPT.EV0 mw B ps R line0 pos0 [] SPT.noeb) r Hra Hraok heap_ok3 RETPC i c k ps1 _ ret_at IL Hbase fx' E1 R1 M1 model1 E' R' M' HAt HAmb Hag HLF).
  intros HRP HP HA' HagE'.
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct OP as (OP1 & OP2 & OP3), OE as (OE1 & OE2 & OE3).
  pose proof (SPT.pa_def _ _ _ HPA) as HdefP. destruct HEC as (_ & HEd & _).
  assert (HdP' : L5.defined M' P 272) by (apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 P 272 HA' HdefP); left; lia).
  assert (HdE' : L5.defined M' E 16) by (apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 E 16 HA' HEd); left; lia).
  destruct (HKIND E1 E' R' M1 M' model1 Hag HLF HX HA' HagE' HdE') as (more' & stack' & scap' & code & g' & Hmo' & Hby' & Hse & Hsc & Hle & Hin' & Hec' & Hcm & Hls' & Hg' & Hden & HPS).
  unfold view_chk in HV. destruct (SPA.pview_w (SR.ps_cells ps1) Pb PE CE) as [pv|] eqn:HPV; [|discriminate].
  apply andb_prop in HV as [HV Y12]. apply andb_prop in HV as [HV Y11]. apply andb_prop in HV as [HV Y10]. apply andb_prop in HV as [HV Y9]. apply andb_prop in HV as [HV Y8].
  apply andb_prop in HV as [HV Y7]. apply andb_prop in HV as [HV Y6]. apply andb_prop in HV as [HV Y5]. apply andb_prop in HV as [HV Y4]. apply andb_prop in HV as [HV Y3].
  apply andb_prop in HV as [Y1 Y2]. apply expr_eqb_eq in Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11, Y12.
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & G42 & G43 & G44 & G45 & G46 & G36 & G38 & G39 & G40 & GSE & GSC & GPE & GCE & G32 & G33 & _).
  destruct (SPA.parser_view_w E' M' (SR.ps_cells ps1) Pb PE CE pv P more' (PML.ps_done ps) stack' scap' mw HK HPV GP' ltac:(lia) ltac:(lia)) as (buf & HPA' & Hlen & _).
  - rewrite Y7. exact Hmo'.
  - rewrite Y8, G46. reflexivity.
  - rewrite Y10. exact Hby'.
  - rewrite Y11, Y10. exact Hse.
  - rewrite Y12, Y10. exact Hsc.
  - exact Hle.
  - rewrite Y3. exact G32.
  - rewrite Y2. exact G33.
  - exact (kit SPT.mw_le).
  - exact HdP'.
  - rewrite Y4, Y5, Y6, Y1, Y10, G43, G44, GCE, GPE in HPA'. rewrite Y9, G36 in Hlen.
    set (ps' := PML.PS (uv E' stv) (PML.ps_sst ps) (PML.ps_nst ps) more' (PML.ps_done ps) (uv E' lvl) stack' (uv E' sbv) scap' bcap bptr buf (PML.ps_win ps)) in *.
    destruct (HPS buf) as (Hwf' & Hneed' & HREL). fold ps' in Hwf', Hneed', HREL.
    assert (Hden' : CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps') by (rewrite Hden; reflexivity).
    pose proof HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr & Hdf).
    unfold CH2.cur in HH1. rewrite Hden' in HH1.
    apply (Hcont fx' R' M' model1 (PML.ps_blocks ps' ++ LBo) cr1 LBo W HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH1].
    exists ps', code, g'.
    split; [exact HPA'|]. split; [exact Hwf'|].
    split; [apply (SPT.win_ok_tr M M' LBo ps ps' eq_refl HWIN); intros ch p n Hch C1 C2 Hwd;
            apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 p n HA' Hwd); right; exists ch; split; [exact Hch | lia]|].
    split; [apply (SPT.buf_bound_tr ps ps' B eq_refl); [unfold ps'; cbn [PML.ps_buf]; exact Hlen | rewrite Hneed', need0; lia | exact HBB]|].
    split; [exact Hec'|]. split; [exact Hcm|]. split; [exact Hls'|]. split; [exact Hg'|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact (proj1 (cred_pc i E1 cr1 ps' Hden' eq_refl Hin') HC1) | exact HREL].
Qed.

Lemma ecell : forall E' (M' : mem) cells, know_ok RSEGS E' M' cells -> env_agree GT.NF E0 E' -> PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) = true -> L5.defined M' E 16 -> PML.ec_at M' E 0.
Proof.
  intros E' M' cells HK Hag Y1 HdE'. destruct (FRZ E' Hag) as (_ & _ & GE & _). destruct OE as (OE1 & OE2 & OE3). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & _).
  split; [|split; [exact HdE' | left; reflexivity]].
  pose proof (PB2.kword32_elim E' M' _ _ E (PB.has_ok E' M' _ _ HK Y1)) as T. rewrite PB2.uv_lit in T by lia. apply T. unfold estart. cbn [a_base a_off]. fold (uv E' Eb). rewrite GE. lia.
Qed.

Lemma leaf_exit1 : forall c k ps1 pc, is_leaf JVIS c k ps1 (CC.TOther pc) -> PB.exit_base_chk GT.NF RETPC c ps1 = true -> CH2.blocks_eqb (nth JVIS G.BLS []) BL1 = true ->
  PB.has (SR.ps_cells ps1) (KWord (SA Eb 0) 4 (ELit 0)) = true -> view_chk (SR.ps_cells ps1) LVL1 (ELit STNEW) (ELit 0) GB SEND1 (APC.eadd GB GC) = true ->
  PB.has (SR.ps_cells ps1) (KRange (EVar 41) 0 1023) = true -> PB.has (SR.ps_cells ps1) (VSU.fl Vb 0 VFLAGS) = true -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok JVIS c ps1.
Proof.
  intros c k ps1 pc IL Hbase HBL Hec HV Hlv Hfl. apply (exit_gen JVIS c k ps1 pc _ _ _ _ _ _ IL Hbase HV).
  intros E1 E' R' M1 M' model1 Hag HLF HX HA' HagE' HdE'.
  assert (Hc : nth_error G.CPS JVIS = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  rewrite xi_vis in HX. destruct HX as (HS & b' & cap' & Hden & Hby & Hcin & Hcap).
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & G42 & G43 & G44 & G45 & G46 & G36 & G38 & G39 & G40 & GSE & GSC & GPE & GCE & G32 & G33 & _).
  pose proof WFM as (F1 & F2 & F3 & F4 & C & HSC & HCC & HCL).
  assert (HL : level <= 1023).
  { pose proof (PB.has_ok E' M' _ _ HK Hlv) as Q. cbn [kentry_ok] in Q. fold (uv E' (EVar 41)) in Q. rewrite G41 in Q. unfold level. lia. }

  rewrite <- bls_vis in Hden. rewrite (CH2.blocks_eqb_eq _ _ HBL) in Hden. unfold CH2.den, BL1 in Hden. cbn [map fst snd] in Hden. fold (uv E1 PE) (uv E1 CE) (uv E1 GB) (uv E1 GC) in Hden. injection Hden as _ _ HGB HGC.
  assert (Hag1 : env_agree (CC.cp_nx (nth JVIS G.CPS G.cp0)) E1 E') by (rewrite (nth_error_nth _ _ G.cp0 Hc); exact Hag).
  assert (HGB' : uv E' GB = b') by (rewrite (PB.uv_agree _ E1 E' GB Hag1 ltac:(vm_compute; reflexivity)); exact HGB).
  assert (HGC' : uv E' GC = cap') by (rewrite (PB.uv_agree _ E1 E' GC Hag1 ltac:(vm_compute; reflexivity)); exact HGC).

  pose proof HA' as (_ & _ & _ & (cr1 & HH1 & _) & _ & _). destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _).
  assert (Hinb : In (b', cap') (CH2.cur LBo G.BLS JVIS E1)).
  { unfold CH2.cur. apply in_or_app. left. rewrite (CH2.blocks_eqb_eq _ _ HBL). unfold CH2.den, BL1. cbn [map fst snd]. fold (uv E1 GB) (uv E1 GC). rewrite HGB, HGC. right. left. reflexivity. }
  destruct (Hwf _ Hinb) as ((B0 & B1 & B2 & B3 & B4) & _). cbn [fst snd] in B0, B1, B2, B3, B4.
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). pose proof (kit SPT.NUM) as (_ & _ & _ & _ & _ & _ & _ & _ & N3 & _).
  assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame JVIS c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
  assert (Hlen1 : Z.of_nat (length (PML.ps_stack ps ++ [KIND])) = slen + 1) by (rewrite length_app; cbn [length]; unfold slen; lia).
  exists false, (PML.ps_stack ps ++ [KIND]), cap', 0, g.
  split; [rewrite PB2.uv_lit by lia; reflexivity|].
  split; [rewrite HGB'; apply (kit SPT.bytes_below M1 M' b' cap' _ HLOW ltac:(lia) B4 ltac:(rewrite Hlen1; lia) Hby)|].
  split; [unfold SEND1; rewrite PB.uv_eaddz, PB.uv_eadd, G39, HGB', Hlen1; unfold hl_ceil in *; rewrite (Z.mod_small (slen + b')) by lia; rewrite Z.mod_small by lia; lia|].
  split; [rewrite PB.uv_eadd, HGB', HGC'; unfold hl_ceil in *; apply Z.mod_small; lia|].
  split; [rewrite Hlen1; exact Hcap|]. split; [exact Hcin|].
  split; [exact (ecell E' M' _ HK HagE' Hec HdE')|]. split; [intros Q; exfalso; apply Q; reflexivity|].
  split; [apply (PB2.ls_ok_keep M M'); [|exact HG | exact HLS]; intros a Ha; rewrite (HLOW a (foot_low a Ha)); exact (HS a Ha)|].
  split; [left; reflexivity|].
  split; [rewrite (CH2.blocks_eqb_eq _ _ HBL); unfold CH2.den, BL1; cbn [map fst snd]; fold (uv E1 PE) (uv E1 CE) (uv E1 GB) (uv E1 GC);
          destruct (FRZ E1 (amb_agree _ _ _ _ HA')) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPE1 & HCE1 & _); rewrite HPE1, HCE1, HGB, HGC, HGB'; reflexivity|].
  intros buf. cbv zeta. rewrite PB2.uv_lit by (unfold STNEW, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_VALUE_OR_END; lia).
  assert (HLV1 : uv E' LVL1 = level + 1) by (unfold LVL1; rewrite PB.uv_eaddz, G41; apply Z.mod_small; unfold level in *; lia).
  rewrite HLV1.
  match goal with |- PMCUR.wf_c ?q /\ _ => set (psq := q) end.
  assert (WT : PML.wf_ps (PMCUR.ps_set_more psq true)).
  { destruct HWF as (W1 & W2 & W3 & W4 & _).
    unfold PML.wf_ps, psq. cbn [PMCUR.ps_set_more PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st PML.ps_buf].
    split; [exact W1|]. split; [exact W2|]. split; [apply Nat2Z.inj_le; rewrite Hlen1; unfold slen, level in *; lia|]. split; [exact Hcin|].
    exists (C ++ [KIND]), []. rewrite app_nil_r. split; [rewrite HSC; reflexivity|].
    split; [apply Forall_app; split; [exact HCC | constructor; [unfold PML.is_container, KIND; tauto | constructor]]|]. intros _.
    split; [rewrite length_app; cbn [length]; unfold level in *; lia|]. split; [unfold level in *; lia|].
    unfold PML.handled, PML.transient, PML.comment_or_cr, STNEW, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_VALUE_OR_END, PML.ST_EXPECT_COMMA_OR_END, PML.ST_NUMBER, PML.ST_CR.
    split; [lia|]. split; [left; split; [reflexivity | lia]|]. split; [intros [Q|[]]; discriminate Q | intros Q; discriminate Q]. }
  assert (LT : PMCUR.lvl_ok (PMCUR.ps_set_more psq true)).
  { apply (SCU.lvl_ok_rootc _ (C ++ [KIND])); [unfold psq; cbn [PMCUR.ps_set_more PML.ps_stack]; rewrite HSC; reflexivity | |].
    - apply Forall_app; split; [exact HCC | constructor; [unfold PML.is_container, KIND; tauto | constructor]].
    - intros _ _. unfold psq. cbn [PMCUR.ps_set_more PML.ps_level]. unfold level in *. lia. }
  destruct (FRZ E' HagE') as (_ & _ & _ & GVV & _).
  assert (HdV' : L5.defined M' (V + 8) 40).
  { apply (kit SPT.amb_def GT.NF G.BLS Cred JVIS E1 M' model1 (V + 8) 40 HA'); [eapply (L5.defined_sub _ _ _ _ _ (proj2 HVIS)); lia | left; destruct OV as (OV1 & OV2 & _); pose proof (kit SPT.SPF) as (_ & _ & _ & SS4 & _); lia]. }
  assert (HFL : L5.u64_at RSEGS M' (V + 8) VFLAGS).
  { pose proof (PB.has_ok E' M' _ _ HK Hfl) as Q. unfold VSU.fl in Q. pose proof (PB2.kword64_elim E' M' _ _ (V + 8) Q) as T. rewrite PB2.uv_lit in T by (unfold VFLAGS; lia).
    apply T. unfold estart. cbn [a_base a_off]. fold (uv E' Vb). rewrite GVV. lia. }
  split; [exact (SCU.wf_c_stop psq eq_refl WT)|].
  split; [reflexivity|]. split; [left; repeat split; reflexivity|].
  apply (SCU.cur_post_event RSEGS ps psq M' V VEV eq_refl (conj WT LT)).
  - unfold PMCUR.ev_at, VEV. split; [exact HdV' | exact HFL].
  - unfold PMCUR.ev_rel, VEV. unfold psq. cbn [PML.ps_st PML.ps_level]. split; [unfold STNEW; reflexivity | unfold level; reflexivity].
Qed.

Lemma leaf_exit2 : forall c k ps1 pc, is_leaf JSETEC c k ps1 (CC.TOther pc) -> PB.exit_base_chk GT.NF RETPC c ps1 = true -> CH2.blocks_eqb (nth JSETEC G.BLS []) SPT.BL0 = true ->
  PB.has (SR.ps_cells ps1) (KWord (SA Eb 0) 4 (ELit 5)) = true -> PB.has (SR.ps_cells ps1) (KWord (SA Eb 8) 8 (ELit PML.OBJ_JSON_CATEGORY)) = true ->
  view_chk (SR.ps_cells ps1) LVL1 (EVar 42) (ELit 0) (EVar 38) SEND0 (APC.eadd (EVar 38) (EVar 40)) = true ->
  PB.has (SR.ps_cells ps1) (KRange (EVar 41) 1024 1025) = true -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok JSETEC c ps1.
Proof.
  intros c k ps1 pc IL Hbase HBL Hec0 Hec8 HV Hlv. apply (exit_gen JSETEC c k ps1 pc _ _ _ _ _ _ IL Hbase HV).
  intros E1 E' R' M1 M' model1 Hag HLF HX HA' HagE' HdE'.
  assert (Hc : nth_error G.CPS JSETEC = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  rewrite xi_setec in HX. destruct HX as (HLS2 & HBY).
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & G42 & G43 & G44 & G45 & G46 & G36 & G38 & G39 & G40 & GSE & GSC & GPE & GCE & G32 & G33 & _).
  pose proof WFM as (F1 & F2 & F3 & F4 & C & HSC & HCC & HCL).
  pose proof (kit SPT.NUM) as (BR1 & (B0 & B1 & B2 & B3 & B4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _).
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OE as (OE1 & OE2 & OE3).
  assert (HL : level = 1024).
  { pose proof (PB.has_ok E' M' _ _ HK Hlv) as Q. cbn [kentry_ok] in Q. fold (uv E' (EVar 41)) in Q. rewrite G41 in Q. unfold level in *. lia. }
  assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame JSETEC c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
  assert (ES : forall q, estart E' (SA Eb q) = E + q) by (intros q; unfold estart; cbn [a_base a_off]; fold (uv E' Eb); rewrite GE; reflexivity).
  exists false, (PML.ps_stack ps), scap, 5, (PML.regJ g).
  split; [rewrite PB2.uv_lit by lia; reflexivity|].
  split; [rewrite G38; apply (kit SPT.bytes_below M1 M' sb scap (PML.ps_stack ps) HLOW ltac:(lia) B4 ltac:(unfold slen in N4; lia) HBY)|].
  split; [unfold SEND0; rewrite GSE, G38; reflexivity|]. split; [rewrite GSC, G38; reflexivity|].
  split; [unfold slen in N4; lia|]. split; [exact F4|].
  split.
  { split; [|split; [exact HdE' | right; split; [lia|]]].
    - pose proof (PB2.kword32_elim E' M' _ _ E (PB.has_ok E' M' _ _ HK Hec0)) as T. rewrite PB2.uv_lit in T by lia. apply T. rewrite ES. lia.
    - pose proof (PB2.kword64_elim E' M' _ _ (E + 8) (PB.has_ok E' M' _ _ HK Hec8)) as T. rewrite PB2.uv_lit in T by (unfold PML.OBJ_JSON_CATEGORY; lia). apply T. apply ES. }
  split; [intros _; reflexivity|].
  split; [exact (kit SPT.ls_below M1 M' (PML.regJ g) ltac:(destruct g; discriminate) HLOW HLS2)|].
  split; [right; split; [reflexivity | lia]|].
  split; [rewrite (CH2.blocks_eqb_eq _ _ HBL), (kit SPT.den_BL0 E1 (amb_agree _ _ _ _ HA')), G38; reflexivity|].
  intros buf. cbv zeta.
  split; [split; [|apply SCU.lvl_ok_stop; reflexivity]|].
  { destruct HWF as (W1 & W2 & W3 & W4 & (C0 & T0 & W5 & W6 & _)).
    unfold PML.wf_ps. cbn [PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st PML.ps_buf].
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. exists C0, T0. split; [exact W5|]. split; [exact W6|]. intros Q; discriminate Q. }
  split; [reflexivity|]. split; [right; split; [reflexivity | exact HL] | exact (SCU.cur_post_err RSEGS ps _ 5 M' V ltac:(lia))].
Qed.

Lemma leaves : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. cbn [leaf_chk] in X.
  destruct (Z.eqb_spec pc VISPC) as [->|NV].
  { try rewrite Z.eqb_refl in X. apply andb_prop in X as [X XR]. apply andb_prop in X as [Hpc Hi]. apply Z.eqb_eq in Hpc. apply Nat.eqb_eq in Hi. subst i.
    destruct (CH2.ret_of G.RETS JPUSH k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
    apply andb_prop in XR as [Hj XC]. apply Nat.eqb_eq in Hj.
    destruct (vis_chk c ps1 cj (nth JPUSH G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. apply Nat.leb_le in XC.
    exact (leaf_vis c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk XC). }
  try (apply Z.eqb_neq in NV; rewrite NV in X).
  destruct (Z.eqb pc VECPUSH || Z.eqb pc SETEC)%bool eqn:HPC'.
  - apply andb_prop in X as [X XR]. apply andb_prop in X as [Hpc Hi]. apply Z.eqb_eq in Hpc. apply Nat.eqb_eq in Hi. subst i.
    destruct (CH2.ret_of G.RETS 0 k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
    destruct (Z.eqb_spec pc VECPUSH) as [->|N1].
    + apply andb_prop in XR as [Hj XC]. apply Nat.eqb_eq in Hj. exact (leaf_push c k ps1 j cj IL Hret Hcj Hj Hpc XC).
    + cbn [orb] in HPC'. apply Z.eqb_eq in HPC'. subst pc. apply andb_prop in XR as [Hj XC]. apply Nat.eqb_eq in Hj.
      destruct (setec_chk c ps1 cj (nth 0 G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. apply Nat.leb_le in XC.
      exact (leaf_setec c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk XC).
  - apply andb_prop in X as [Hbase X]. apply orb_prop in X as [X|X].
    + apply andb_prop in X as [X Hfl]. apply andb_prop in X as [X Hlv]. apply andb_prop in X as [X HV]. apply andb_prop in X as [X Hec]. apply andb_prop in X as [Hi HBL]. apply Nat.eqb_eq in Hi. subst i.
      exact (leaf_exit1 c k ps1 pc IL Hbase HBL Hec HV Hlv Hfl).
    + apply andb_prop in X as [X Hlv]. apply andb_prop in X as [X HV]. apply andb_prop in X as [X Hec8]. apply andb_prop in X as [X Hec0]. apply andb_prop in X as [Hi HBL]. apply Nat.eqb_eq in Hi. subst i.
      exact (leaf_exit2 c k ps1 pc IL Hbase HBL Hec0 Hec8 HV Hlv).
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
  - intros i c k ps1 j s IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. discriminate X.
  - intros i c k ps1 j s IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. discriminate X.
  - exact leaves.
  - reflexivity.
  - rewrite LS. exact At0.
  - pose proof WFM as (F1 & F2 & F3 & F4 & _).
    assert (Hden0 : CH2.den E0 (nth 0 G.BLS []) = PML.ps_blocks ps) by (change (nth 0 G.BLS []) with SPT.BL0; exact (kit SPT.den_BL0 E0 (CC.env_agree_refl _ _))).
    split.
    + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr. split; [unfold CH2.cur; rewrite Hden0; exact HH | exact (proj2 (cred_pc 0%nat E0 cr ps Hden0 eq_refl F4) HPC)].
    + rewrite xi0. split; [intros a _; reflexivity | exact (SPT.pa_stack _ _ _ HPA)].
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
Hypothesis VECPUSH_OK : PMS.vec_push_spec L HI.
Hypothesis SETEC_OK : PMS.set_ec_spec L.
Hypothesis VIS_OK : PMS.visit_begin_object_spec L PMS.PC_VIS_BEGIN_OBJECT_TAG.

Theorem begin_object_ok : PMS.begin_object_spec L HI PML.STRTOD_SCR_V.
Proof.
  unfold PMS.begin_object_spec, PMS.begin_container_spec, PMS.ptrans, PMS.ptrans_g, PMS.ptrans_gb. intros LBo cr sp r P V E B kx bx g ps. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & ((Ha0 & Ha1 & Ha2) & Hmore & Hncc & Hnstr) & HPA & (HWF & _) & HWIN & HBB & HVIS & HEC & HLS & HG & HPC & OP & OV & OE & AP1 & AP2 & AP3) Hcont.
  pose proof (SPT.pa_def _ _ _ HPA) as HdP.
  destruct (PB2.cell_exists M (P + 160) 8 ltac:(lia)) as (line0 & Rc1 & Hc1); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  destruct (PB2.cell_exists M (P + 168) 8 ltac:(lia)) as (pos0 & Rc2 & Hc2); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  exact (main L HI HIok LAY FPM VECPUSH_OK SETEC_OK VIS_OK LBo cr sp r P V E B kx bx g ps fx R M model K HH Hmo HKnil Hfp Hentry Ha0 Ha1 Ha2 Hmore Hncc Hnstr HPA HWF HWIN HBB HVIS HEC HLS HG HPC OP OV OE AP1 AP2 AP3
           Hcont line0 pos0 Hc1 Hc2 (conj Rc1 Rc2)).
Qed.
End Final.
End BeginObjectProof.

