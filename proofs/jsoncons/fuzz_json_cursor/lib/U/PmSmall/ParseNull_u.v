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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallPure SmallKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmSmall Require Import SmallAt_u SmallPt_u SmallWin_u SmallCur_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import VisitSums.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_parse_null_csrc_T_u Cut_parse_null_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module ParseNullProof.
Module G := Cut_parse_null_csrc_u.
Module GT := Cut_parse_null_csrc_T_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Definition NLIT : Z := 4.
Definition STSHORT : Z := 18.
Definition PCF : Z := PML.PC_PARSE_NULL.

Definition VISPC : Z := PMS.PC_VIS_NULL.
Definition VEV : PMCUR.sevent := PMCUR.EvNull.
Definition Pb : expr := EVar 10.  Definition Vb : expr := EVar 11.  Definition Eb : expr := EVar 12.
Definition SEG : expr := EVar 50.  Definition WLEN : expr := EVar 51.  Definition WEND : expr := APC.eadd SEG WLEN.
Definition RETPC : Z := nth 0 GT.ENDS 0.
Definition SETEC : Z := PML.PC_SET_EC.
Definition SCR : Z := CH.hd_scr G.HDECL.
Definition CONSTS : PSK.consts := PSK.CONSTS PML.VT_PARSER PML.VT_FUNC PML.VT_VISITOR 0x10000 0xf8000 0x10000 PML.IMG_RO_HI SCR [(-8, 1%nat); (-16, 8%nat); (-24, 9%nat)] 24.
Definition X0 : PSK.pexprs := SPT.X0w SEG (EVar 42) (ELit 1).
Lemma kn0_eq : CC.cp_know G.cp0 = SPK.kn CONSTS false Pb Vb Eb (EVar 2) WEND X0 ++ SPK.win_f CONSTS Pb Vb Eb (EVar 2) SEG WLEN X0 ++ [KRange WLEN 1 16384].
Proof. vmc_refl. Qed.
Lemma regs0_eq : CC.cp_regs G.cp0 = sr_id.
Proof. vmc_refl. Qed.
Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Abbreviation PE := SPT.PE.  Abbreviation CE := SPT.CE.
Definition SEND0 : expr := APC.eadd (EVar 38) (EVar 39).

Definition view_chk (cells : list kentry) (wpv stv morev : expr) : bool :=
  match SPA.pview_w cells Pb PE CE with
  | Some pv => (expr_eqb (PB4.pv_level pv) (EVar 41) && expr_eqb (PB4.pv_wend pv) WEND && expr_eqb (PB4.pv_wptr pv) wpv && expr_eqb (PB4.pv_st pv) stv
                && expr_eqb (PB4.pv_sst pv) (EVar 43) && expr_eqb (PB4.pv_nst pv) (EVar 44) && expr_eqb (PB4.pv_more pv) morev && expr_eqb (PB4.pv_done pv) (EVar 46)
                && expr_eqb (PB4.pv_size pv) (EVar 36) && expr_eqb (PB4.pv_sb pv) (EVar 38) && expr_eqb (PB4.pv_send pv) SEND0 && expr_eqb (PB4.pv_scend pv) (APC.eadd (EVar 38) (EVar 40)))%bool
  | None => false
  end.

Definition cur_of (ps : SR.post_spec) : expr := match CAX.cell_at (SR.ps_cells ps) Pb 200 8 with Some e => e | None => ELit 0 end.
Definition has_cur (ps : SR.post_spec) : bool := match CAX.cell_at (SR.ps_cells ps) Pb 200 8 with Some _ => true | None => false end.
Definition setec_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (expr_eqb (nth 10 regs (ELit 0)) Eb && expr_eqb (nth 11 regs (ELit 0)) (ELit 11) && CH2.blocks_eqb BLj BLi)%bool
  then CH2.custom_chk GT.NF G.HDECL 256 0 BLi ((Eb, 0, ELit 16) :: PSU.statics_wregs) (PSU.setec_news Eb 0 (ELit 11)) (Some Eb) c ps cj BLi
  else None.
Definition jof (pc : Z) : nat := match find (fun r : nat * nat * nat * Z => let '(_, _, _, p) := r in Z.eqb p pc) G.RETS with Some (j, _, _, _) => j | None => 0%nat end.
Definition JVIS : nat := Eval vm_compute in jof VISPC.

Definition vis_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (expr_eqb (nth 10 regs (ELit 0)) Vb && CH2.blocks_eqb BLj BLi && PB.has (SR.ps_cells ps) (KWord (SA Vb 0) 8 (ELit PML.VT_VISITOR)))%bool
  then CH2.custom_chk GT.NF G.HDECL PMS.VIS_SCR 0 BLi [(Vb, 8, ELit 40)] (VSU.const_news Vb 0 4) (Some (ELit 1)) c ps cj BLi
  else None.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc VISPC then
        (Z.eqb (SR.ps_pc ps) VISPC && Nat.eqb i 0 &&
         match CH2.ret_of G.RETS i k with
         | Some j => match nth_error G.CPS j with
                     | Some cj => (Nat.eqb j JVIS && match vis_chk c ps cj (nth i G.BLS []) (nth j G.BLS []) with Some ci => Nat.leb (CC.cp_nx c) (CH2.ci_nx ci) | None => false end)%bool
                     | None => false end
         | None => false end)%bool
      else if Z.eqb pc SETEC then
        (Z.eqb (SR.ps_pc ps) pc && Nat.eqb i 0 &&
         match CH2.ret_of G.RETS i k with
         | Some j => match nth_error G.CPS j with
                     | Some cj => (negb (Nat.eqb j 0) && negb (Nat.eqb j JVIS) && match setec_chk c ps cj (nth i G.BLS []) (nth j G.BLS []) with Some ci => Nat.leb GT.NF (CH2.ci_nx ci) | None => false end)%bool
                     | None => false end
         | None => false end)%bool
      else (PB.exit_base_chk GT.NF RETPC c ps && CH2.blocks_eqb (nth i G.BLS []) SPT.BL0 && has_cur ps &&
            if Nat.eqb i 0
            then (PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) && view_chk cells (cur_of ps) (ELit STSHORT) (ELit 1) && SPW.rng_is cells (APC.esub (cur_of ps) SEG) 1)
            else if Nat.eqb i JVIS
            then (PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) && SPW.rng_is cells (APC.esub (cur_of ps) SEG) NLIT && SPW.rng_in cells WLEN NLIT 16384 &&
                  PB.has cells (VSU.fl Vb 0 4) &&
                  (view_chk cells (cur_of ps) (ELit PML.ST_ACCEPT) (ELit 0) || (view_chk cells (cur_of ps) (ELit PML.ST_EXPECT_COMMA_OR_END) (ELit 0) && SPW.rng_in cells (EVar 41) 1 1025)))
            else (PB.has cells (KWord (SA Eb 0) 4 (ELit 11)) && PB.has cells (KWord (SA Eb 8) 8 (ELit PML.OBJ_JSON_CATEGORY)) && view_chk cells (cur_of ps) (EVar 42) (ELit 0) && expr_eqb (cur_of ps) SEG))%bool
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
Hypothesis SETEC_OK : PMS.set_ec_spec L.
Hypothesis VIS_OK : PMS.visit_null_spec L VISPC.
Abbreviation SSCR := PML.STRTOD_SCR_V.
Abbreviation SCRC := (PMS.PF_SCR SSCR).

Variables (LBo : list (Z * Z)) (cr : credit) (sp r P V E B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate).
Variables (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet).
Variables (p e : Z).
Hypothesis HH : hi_heap HI (PML.ps_blocks ps ++ LBo) cr M (m_vmmaps model).
Hypothesis Hmo : PML.model_ok model.
Hypothesis HKnil : K [].
Hypothesis Hfp : PML.fp_ok fx.
Hypothesis Hentry : PML.entry L R M sp r SCRC.
Hypothesis Ha0 : PML.a0 R P.
Hypothesis Ha1 : PML.a1 R V.
Hypothesis Ha2 : PML.a2 R E.
Hypothesis Hwin : PML.ps_win ps = Some (p, e).
Hypothesis Hmore : PML.ps_more ps = true.
Hypothesis Hnex : ~ PMS.win_exhausted ps.
Hypothesis Hexp : PML.is_expect (PML.ps_st ps).
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
      PMS.literal_rel ps ps' code /\ PMCUR.cur_post RSEGS ps ps' code M' V) ->
   regs_preserved R R' -> L5C.hpres L LBk sp SCRC W M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
   srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model') K.

Variables (line0 pos0 : Z) (winb : list Z).
Hypothesis Hline0 : PML.u64 M (P + 160) line0.
Hypothesis Hpos0 : PML.u64 M (P + 168) pos0.
Hypothesis Hlpr : 0 <= line0 < 2 ^ 64 /\ 0 <= pos0 < 2 ^ 64.
Hypothesis Hwinb : L5.bytes_at RSEGS M p winb /\ Z.of_nat (length winb) = e - p.

Let mw := PML.ps_win ps.
Let bcap := PML.ps_bcap ps.
Let bptr := PML.ps_bptr ps.
Let size0 := Z.of_nat (length (PML.ps_buf ps)).
Let sb := PML.ps_sb ps.
Let scap := PML.ps_scap ps.
Let slen := Z.of_nat (length (PML.ps_stack ps)).
Let level := PML.ps_level ps.
Let st := PML.ps_st ps.
Let wlen := e - p.
Definition ebf : nat -> list (bv 8) := fun k => if Nat.eqb k 1 then map (Z_to_bv 8) winb else [].
Definition XV : list Z := [V; p; wlen].
Definition E0 : env := SPT.E0 mw B ps R line0 pos0 XV ebf.

Lemma ps_mw : PML.ps_set_win ps mw = ps.
Proof. unfold mw. destruct ps; reflexivity. Qed.
Lemma SCRV : CH.hd_scr G.HDECL = 512.
Proof. reflexivity. Qed.

Lemma WFM : 0 <= level <= 1024 /\ st <> PML.ST_STRING /\ st <> PML.ST_NUMBER /\ 0 <= st <= 255 /\ In scap [66; 132; 264; 528; 1056] /\
  exists C, PML.ps_stack ps = PML.ST_ROOT :: C /\ Forall PML.is_container C /\ Z.of_nat (length C) = level.
Proof.
  pose proof HWF as (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)). unfold st, level. destruct (W7 Hmore) as (W8 & W9 & W10 & W11 & _).
  assert (HX : PML.ps_st ps <> PML.ST_STRING /\ PML.ps_st ps <> PML.ST_NUMBER /\ ~ PML.comment_or_cr (PML.ps_st ps) /\ 0 <= PML.ps_st ps <= 255).
  { unfold PML.is_expect in Hexp. unfold PML.ST_STRING, PML.ST_NUMBER, PML.comment_or_cr, PML.ST_CR. cbn [In] in Hexp. lia. }
  destruct HX as (X1 & X1' & X2 & X3).
  assert (HT : T = []).
  { unfold PML.transient in W11. destruct W11 as [(HT & _)|[(_ & X)|[(S & _ & _ & X)|(S & _ & _ & X)]]]; [exact HT | contradiction | contradiction |]. exfalso. apply X2. right. exact X. }
  subst T. rewrite app_nil_r in W5.
  split; [exact W9|]. split; [exact X1|]. split; [exact X1'|]. split; [exact X3|]. split; [exact W4|]. exists C. split; [exact W5|]. split; [exact W6 | exact W8].
Qed.
Lemma need0 : PML.buf_need ps = 0.
Proof. pose proof WFM as (_ & F2 & _). unfold PML.buf_need. destruct (Z.eqb_spec (PML.ps_st ps) PML.ST_STRING) as [Q|_]; [contradiction|]. rewrite Bool.andb_false_r. reflexivity. Qed.

Lemma Hpe : p < e.
Proof. pose proof (SPT.win_le M P ps HPA) as Q. rewrite Hwin in Q. unfold PMS.win_exhausted in Hnex. rewrite Hwin in Hnex. lia. Qed.
Lemma WINF : exists ch, In (ch, 16384) LBo /\ ch <= p /\ e <= ch + 16384 /\ L5.defined M p wlen.
Proof. pose proof HWIN as HW. unfold PML.win_ok in HW. rewrite Hwin in HW. exact HW. Qed.
Lemma WRNG : 4096 <= p /\ e <= hl_ceil L /\ 1 <= wlen <= 16384.
Proof.
  destruct WINF as (ch & Hch & C1 & C2 & _). destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _). pose proof Hpe.
  destruct (Hwf (ch, 16384) ltac:(right; right; exact Hch)) as ((B0 & B1 & B2 & B3 & B4) & _). cbn [fst snd] in *. unfold wlen. lia.
Qed.

Lemma INST : SPT.inst L HI mw LBo cr sp r P V E B kx bx g ps R M model SCRC G.HDECL Pb Vb Eb line0 pos0 XV ebf.
Proof.
  unfold SPT.inst. destruct Hlpr as (Q1 & Q2). pose proof WFM as (F1 & F2 & F3 & F4 & F5 & _). pose proof Hpe as Hpe'.
  destruct Hentry as (_ & _ & Hsp & _ & Hstk). pose proof (L5C.stk_floor _ _ _ _ Hstk) as FL. pose proof Hstk as (S1 & S2 & S3 & S4 & S5).
  destruct OP as (OP1 & OP2 & OP3), OV as (OV1 & OV2 & OV3), OE as (OE1 & OE2 & OE3).
  assert (HSC : SCRC = 9968) by reflexivity.
  split; [exact HIok|]. split; [exact LAY|]. split; [exact HH|]. split; [exact Hentry|]. split; [rewrite SCRV; lia|]. split; [lia|].
  split; [rewrite ps_mw; exact HPA|]. split; [exact (PML.wf_ps_stale_of ps HWF)|]. split; [unfold level in *; lia|].
  split.
  { destruct HBB as (HB1 & HB2). rewrite need0 in HB1. unfold PML.winlen in HB1. rewrite Hwin in HB1. lia. }
  split; [exact F4|].
  split; [exact HVIS|]. split; [exact HEC|]. split; [exact HLS|]. split; [exact HPC|].
  split; [exact (conj OP1 (conj OP2 OP3))|]. split; [exact (conj OV1 (conj OV2 OV3))|]. split; [exact (conj OE1 (conj OE2 OE3))|]. split; [exact AP1|]. split; [exact AP2|]. split; [exact AP3|].
  split; [exact Hline0|]. split; [exact Hpos0|]. split; [exact Q1|]. split; [exact Q2|].
  split; [unfold PB.uv, Pb; cbn [edenot]; rewrite (SPT.EV0 mw B ps R line0 pos0 XV ebf 10%bv), Ha0; apply u64_of_Z; lia|].
  split; [unfold PB.uv, Vb; cbn [edenot]; rewrite (SPT.EV0 mw B ps R line0 pos0 XV ebf 11%bv), Ha1; apply u64_of_Z; lia|].
  split; [unfold PB.uv, Eb; cbn [edenot]; rewrite (SPT.EV0 mw B ps R line0 pos0 XV ebf 12%bv), Ha2; apply u64_of_Z; lia|].
  split; [reflexivity|]. split; reflexivity.
Qed.
Notation kit X := (X L HI mw LBo cr sp r P V E B kx bx g ps R M model SCRC G.HDECL Pb Vb Eb line0 pos0 XV ebf INST) (only parsing).

Lemma FRZW : forall E', env_agree GT.NF E0 E' -> uv E' SEG = p /\ uv E' WLEN = wlen /\ uv E' WEND = e /\ eb E' = ebf.
Proof.
  intros E' Hag. pose proof WRNG as (R1 & R2 & R3). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). unfold hl_ceil in R2.
  destruct (SPT.FRZx mw B ps R G.HDECL line0 pos0 XV ebf E' 1%nat p Hag ltac:(unfold SPT.NF; lia) eq_refl ltac:(lia)) as (G50 & Geb).
  destruct (SPT.FRZx mw B ps R G.HDECL line0 pos0 XV ebf E' 2%nat wlen Hag ltac:(unfold SPT.NF; lia) eq_refl ltac:(lia)) as (G51 & _).
  change (49 + 1)%nat with 50%nat in G50. change (49 + 2)%nat with 51%nat in G51.
  split; [exact G50|]. split; [exact G51|]. split; [|exact Geb]. unfold WEND. rewrite PB.uv_eadd. unfold SEG, WLEN. rewrite G50, G51. unfold wlen. rewrite Z.mod_small by lia. lia.
Qed.

Lemma At0 : CC.At RSEGS G.cp0 E0 R M.
Proof.
  pose proof WRNG as (R1 & R2 & R3). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OP as (OP1 & OP2 & OP3).
  destruct (FRZW E0 (CC.env_agree_refl _ _)) as (G50 & G51 & GWE & _).
  split.
  - rewrite regs0_eq. exact (regs_ok_id R _ _).
  - rewrite kn0_eq. unfold know_ok. rewrite !Forall_app. split; [|split].
    + apply (kit SPT.kn_okw CONSTS SEG WEND (EVar 42) (ELit 1) eq_refl eq_refl eq_refl (conj eq_refl eq_refl) (conj eq_refl eq_refl) eq_refl).
      * destruct (kit SPT.FRZ E0 (CC.env_agree_refl _ _)) as (_ & _ & _ & _ & _ & G42 & _). exact G42.
      * rewrite PB2.uv_lit by lia. rewrite Hmore. reflexivity.
      * unfold mw. rewrite Hwin. reflexivity.
      * fold E0. unfold mw. rewrite Hwin. cbn [PSA.wincells snd]. rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 WEND)). fold (uv E0 WEND). rewrite GWE. reflexivity.
    + destruct WINF as (ch & Hch & C1 & C2 & Hwd). destruct Hwinb as (Hwb & Hwl).
      apply (kit SPT.winf_ok CONSTS SEG (EVar 42) (ELit 1) p wlen ch winb (conj eq_refl eq_refl) eq_refl Hch C1 ltac:(unfold wlen; lia) Hwb Hwl Hwd eq_refl eq_refl eq_refl).
    + constructor; [|constructor]. cbn [kentry_ok]. fold (uv E0 WLEN). rewrite G51. lia.
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
Proof.
  intros rg Hin. destruct WINF as (ch & Hch & C1 & C2 & _). pose proof WRNG as (R1 & R2 & R3). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). unfold hl_ceil in R2.
  assert (Q1 : p + wlen <= ch + 16384) by (unfold wlen; lia). assert (Q2 : 0 <= wlen) by lia. assert (Q3 : 0 <= p) by lia. assert (Q4 : p + wlen < 2 ^ 64) by (unfold wlen; lia).
  apply (kit SPT.CRS_OK p wlen (or_intror (ex_intro _ ch (conj Hch (conj C1 Q1)))) Q2 Q3 Q4 eq_refl eq_refl). exact Hin.
Qed.
Lemma WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a).
Proof. intros rg Hin. apply (kit SPT.WRS_OK). exact Hin. Qed.
Lemma IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Proof. intros rg a Hin. apply (kit SPT.IMG_OK). exact Hin. Qed.
Definition DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL) := kit SPT.DEF0.
Definition FRZ := kit SPT.FRZ.

Definition Cred (i : nat) (E1 : env) (cr1 : credit) : Prop := cr1 = cr.
Lemma CRED_BLK : forall i j E1 E2 cr1, CH2.den E2 (nth j G.BLS []) = CH2.den E1 (nth i G.BLS []) -> Cred i E1 cr1 -> Cred j E2 cr1.
Proof. intros i j E1 E2 cr1 _ H. exact H. Qed.

Definition XI0 (M1 : mem) : Prop := (forall a, PB2.ls_foot a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\ L5.bytes_at RSEGS M1 sb (PML.ps_stack ps).
Definition XIS (M1 : mem) : Prop := PML.ls_ok (PML.regJ g) M1 /\ L5.bytes_at RSEGS M1 sb (PML.ps_stack ps).
Definition XI (i : nat) (E1 : env) (M1 : mem) : Prop := if (Nat.eqb i 0 || Nat.eqb i JVIS)%bool then XI0 M1 else XIS M1.

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
Lemma stack_below : forall (M1 M' : mem), (forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> L5.bytes_at RSEGS M1 sb (PML.ps_stack ps) -> L5.bytes_at RSEGS M' sb (PML.ps_stack ps).
Proof.
  intros M1 M' HLOW HBY. pose proof (kit SPT.NUM) as (BR1 & (B0 & B1 & B2 & B3 & B4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _).
  exact (kit SPT.bytes_below M1 M' sb scap (PML.ps_stack ps) HLOW ltac:(lia) B4 ltac:(unfold slen in N4; lia) HBY).
Qed.

Lemma leaf_setec : forall c k ps1 j cj ci, is_leaf 0 c k ps1 (CC.TOther SETEC) -> CH2.ret_of G.RETS 0 k = Some j -> nth_error G.CPS j = Some cj -> Nat.eqb j 0 = false -> Nat.eqb j JVIS = false -> SR.ps_pc ps1 = SETEC ->
  setec_chk c ps1 cj (nth 0 G.BLS []) (nth j G.BLS []) = Some ci -> (GT.NF <= CH2.ci_nx ci)%nat -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok 0 c ps1.
Proof.
  intros c k ps1 j cj ci IL Hret Hcj Hj HjV Hpc Hchk Hnx. unfold setec_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb HBL]. apply andb_prop in Hb as [Ha0e Ha1e]. apply expr_eqb_eq in Ha0e, Ha1e.
  assert (Hc : nth_error G.CPS 0 = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OE as (OE1 & OE2 & OE3).
  assert (ESE : forall Ex, env_agree GT.NF E0 Ex -> forall q, estart Ex (SA Eb q) = E + q).
  { intros Ex Hx q. destruct (FRZ Ex Hx) as (_ & _ & GE & _). unfold estart. cbn [a_base a_off]. fold (uv Ex Eb). rewrite GE. reflexivity. }
  assert (ESL : forall Ex z, 0 <= z < 2 ^ 63 -> estart Ex (SA (ELit 0) z) = z) by (intros Ex z Hz; unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; lia).
  assert (ELN : forall Ex z, 0 <= z < 2 ^ 64 -> elenZ Ex (ELit z) = z) by (intros Ex z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K XI DEF0 CRED_BLK
           SETEC 256 0%nat ((Eb, 0, ELit 16) :: PSU.statics_wregs) (PSU.setec_news Eb 0 (ELit 11)) (Some Eb) [(E, 16); (0xd4df8, 2); (0xf6848, 544)] 0%nat c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
  - intros w a Hw Hin. exists w. split; [|exact Hin]. unfold W, PMS.W_parc, PML.W_par. cbn [In app] in Hw |- *. tauto.
  - intros E' HagE' w a Hw Hin. unfold L5.in_rng in Hin. destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hin.
    + exists (Eb, 0, ELit 16). split; [left; reflexivity|]. unfold CH2.in_reg. rewrite (ESE E' HagE' 0), (ELN E' 16 ltac:(lia)). lia.
    + exists (ELit 0, 0xd4df8, ELit 2). split; [right; left; reflexivity|]. unfold CH2.in_reg. rewrite (ESL E' 0xd4df8 ltac:(lia)), (ELN E' 2 ltac:(lia)). lia.
    + exists (ELit 0, 0xf6848, ELit 544). split; [right; right; left; reflexivity|]. unfold CH2.in_reg. rewrite (ESL E' 0xf6848 ltac:(lia)), (ELN E' 544 ltac:(lia)). lia.
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    pose proof (kit SPT.NUM) as (BR1 & (B0 & B1 & B2 & B3 & B4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _).
    destruct (FRZ E' HagE') as (G2 & GP' & GE & _). destruct HEC as (_ & HEd & _).
    assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame 0%nat c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
    change (XI 0 E1 M1) with (XI0 M1) in HX. destruct HX as (HS & HBY).
    assert (HLS' : PML.ls_ok g M') by (apply (PB2.ls_ok_keep M M'); [|exact HG | exact HLS]; intros a Ha; rewrite (HLOW a (foot_low a Ha)); exact (HS a Ha)).
    assert (HdE' : L5.defined M' E 16) by (apply (kit SPT.amb_def GT.NF G.BLS Cred 0%nat E1 M' model1 E 16 HA' HEd); left; lia).
    assert (Ra0 : PML.a0 R' E).
    { unfold PML.a0. rewrite (HRL 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Ha0e.
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' Eb)). fold (uv E' Eb). rewrite GE. reflexivity. }
    assert (Ra1 : PML.a1 R' 11).
    { unfold PML.a1. rewrite (HRL 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Ha1e. reflexivity. }
    apply (SETEC_OK E 11 (sp + CH2.ci_csp ci) (CC.cp_pc cj) g fx' R' M' model1 K Hmh Hml HKnil HFP).
    { split; [exact Hent|]. split; [exact Ra0|]. split; [exact Ra1|]. split; [lia|]. split; [exact HdE'|]. split; [unfold PML.obj_on_stack; lia|]. split; [exact HLS' | exact HG]. }
    intros fx2 R2 M2 HFP2 (Hec & Hls2 & Ha0') HRP HFB HGR.
    set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
    assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [apply CH2.retEx_agree | exact Hnx]]).
    apply (RET fx2 R2 M2 [] eq_refl HFP2 HRP HFB HGR).
    + fold E2. destruct (FRZ E2 HagE2) as (_ & _ & GE2 & _). rewrite Ha0'. rewrite <- (Z_to_bv_bv_unsigned _ (edenot E2 Eb)). fold (uv E2 Eb). rewrite GE2. reflexivity.
    + fold E2. intros X HXin. destruct Hec as (Hu32 & _ & Hcat). rewrite LS. destruct HXin as [<-|[<-|[]]].
      * eapply PB.kword32_intro with (A := E) (z := 11); [rewrite (ESE E2 HagE2 0); lia | lia | lia | reflexivity | exact Hu32].
      * destruct Hcat as [Hz|[_ Hcat]]; [lia|].
        eapply CL5.kword64_intro with (A := E + 8) (z := PML.OBJ_JSON_CATEGORY); [exact (ESE E2 HagE2 8) | lia | lia | reflexivity | exact Hcat].
    + intros _. unfold XI. rewrite Hj, HjV. split; [exact Hls2|].
      pose proof (stack_below M1 M' HLOW HBY) as HBY'.
      apply (PB2.bytes_fr _ M' M2 HFB); [|exact HBY'].
      destruct Hent as (_ & _ & _ & _ & Hstk'). pose proof (L5C.stk_window _ _ _ _ Hstk') as (SW1 & _).
      rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in B1.
      split; [lia|]. split; [unfold hl_ceil in *; lia|]. intros q Hq w Hw. unfold L5.in_rng. unfold slen in N4. unfold hl_ceil in *.
      destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PMS.SETEC_SCR; lia.
Qed.

Lemma leaf_vis : forall c k ps1 j cj ci, is_leaf 0 c k ps1 (CC.TOther VISPC) -> CH2.ret_of G.RETS 0 k = Some j -> nth_error G.CPS j = Some cj -> j = JVIS -> SR.ps_pc ps1 = VISPC ->
  vis_chk c ps1 cj (nth 0 G.BLS []) (nth j G.BLS []) = Some ci -> (CC.cp_nx c <= CH2.ci_nx ci)%nat -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok 0 c ps1.
Proof.
  intros c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk Hnx. unfold vis_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb Hvt]. apply andb_prop in Hb as [Ha0e HBL]. apply expr_eqb_eq in Ha0e.
  assert (Hc : nth_error G.CPS 0 = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  assert (Hc' : c = nth 0 G.CPS G.cp0) by exact (eq_sym (nth_error_nth _ _ G.cp0 Hc)).
  assert (HNF : (GT.NF <= CC.cp_nx c)%nat) by (rewrite Hc'; vm_compute; lia).
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OV as (OV1 & OV2 & OV3).
  assert (ESV : forall Ex, env_agree GT.NF E0 Ex -> forall q, estart Ex (SA Vb q) = V + q).
  { intros Ex Hx q. destruct (FRZ Ex Hx) as (_ & _ & _ & GV & _). unfold estart. cbn [a_base a_off]. fold (uv Ex Vb). rewrite GV. reflexivity. }
  assert (ELN : forall Ex z, 0 <= z < 2 ^ 64 -> elenZ Ex (ELit z) = z) by (intros Ex z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K XI DEF0 CRED_BLK
           VISPC PMS.VIS_SCR 0%nat [(Vb, 8, ELit 40)] (VSU.const_news Vb 0 4) (Some (ELit 1)) [(V + 8, 40)] 0%nat c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
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
    assert (HdV' : L5.defined M' V 48) by (apply (kit SPT.amb_def GT.NF G.BLS Cred 0%nat E1 M' model1 V 48 HA' (proj2 HVIS)); left; lia).
    assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame 0%nat c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
    apply (VIS_OK V (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model1 K Hmh Hml HKnil HFP).
    { split; [exact Hent|]. split; [exact Ra0|]. split; [split; [exact HVT | exact HdV']|]. split; [unfold PML.obj_on_stack; repeat split; lia | exact I]. }
    intros fx2 R2 M2 HFP2 (Ha0' & e0 & He & Hev) HRP HFB HGR. subst e0.
    set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
    assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [apply CH2.retEx_agree | lia]]).
    assert (HLOW2 : forall a, 0 <= a < hl_ceil L -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
    { destruct Hent as (_ & _ & _ & _ & Hstk'). pose proof (L5C.stk_window _ _ _ _ Hstk') as (SW1 & _).
      intros a Ha. apply HFB. rewrite L5.unsigned_lit by (unfold hl_ceil in *; lia). intros rg [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; unfold hl_ceil, PMS.VIS_SCR in *; lia. }
    apply (RET fx2 R2 M2 [] eq_refl HFP2 HRP HFB HGR).
    + cbn [edenot]. unfold PML.a0 in Ha0'. exact Ha0'.
    + intros X [<-|[]]. destruct Hev as (_ & Hfl). rewrite LS. unfold VSU.const_news, VSU.fl.
      eapply CL5.kword64_intro with (A := V + 8) (z := 4); [rewrite (ESV E2 HagE2); lia | lia | lia | reflexivity | exact Hfl].
    + intros _. subst j. change (XI JVIS E2 M2) with (XI0 M2). change (XI 0 E1 M1) with (XI0 M1) in HX. destruct HX as (HS & HBY).
      split; [intros a Ha; rewrite (HLOW2 a (foot_low a Ha)), (HLOW a (foot_low a Ha)); exact (HS a Ha)|].
      exact (stack_below M' M2 HLOW2 (stack_below M1 M' HLOW HBY)).
Qed.

Lemma exit_gen : forall i c k ps1 pc stv morev,
  is_leaf i c k ps1 (CC.TOther pc) -> PB.exit_base_chk GT.NF RETPC c ps1 = true -> CH2.blocks_eqb (nth i G.BLS []) SPT.BL0 = true -> has_cur ps1 = true ->
  view_chk (SR.ps_cells ps1) (cur_of ps1) stv morev = true ->
  (forall E1 E' R' (M1 M' : mem) model1, env_agree (CC.cp_nx c) E1 E' -> CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' -> XI i E1 M1 -> HAMB i E1 M' model1 -> env_agree GT.NF E0 E' ->
      L5.defined M' E 16 -> (forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      exists (more' : bool) (code p' : Z) (g' : PML.ls_state),
        uv E' morev = PML.b2z more' /\ uv E' (cur_of ps1) = p' /\ p <= p' <= e /\
        PML.ec_at M' E code /\ (code <> 0 -> more' = false) /\ PML.ls_ok g' M' /\ (g' = g \/ g' = PML.regJ g /\ code <> 0) /\ L5.bytes_at RSEGS M' sb (PML.ps_stack ps) /\
        forall buf, let ps' := PML.PS (uv E' stv) (PML.ps_sst ps) (PML.ps_nst ps) more' (PML.ps_done ps) level (PML.ps_stack ps) sb scap bcap bptr buf (Some (p', e)) in
          PMCUR.wf_c ps' /\ PML.buf_need ps' = 0 /\ ((code = 0 /\ p < p') \/ code = 11) /\ PMCUR.cur_post RSEGS ps ps' code M' V) ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc stv morev IL Hbase HBL Hcur HV HKIND fx' E1 R1 M1 model1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct Hentry as (Hra & Hraok & _).
  assert (HSC : SCRC = 9968) by reflexivity.
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  apply (PB.exit_ret L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K XI DEF0 (fun _ => 0) (fun _ => 0) SCRC
           ltac:(rewrite SCRV; lia) ltac:(lia) S5 R (SPT.EV0 mw B ps R line0 pos0 XV ebf) r Hra Hraok heap_ok3 RETPC i c k ps1 _ ret_at IL Hbase fx' E1 R1 M1 model1 E' R' M' HAt HAmb Hag HLF).
  intros HRP HP HA' HagE'.
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct OP as (OP1 & OP2 & OP3), OE as (OE1 & OE2 & OE3).
  pose proof (SPT.pa_def _ _ _ HPA) as HdefP. destruct HEC as (_ & HEd & _).
  assert (HdP' : L5.defined M' P 272) by (apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 P 272 HA' HdefP); left; lia).
  assert (HdE' : L5.defined M' E 16) by (apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 E 16 HA' HEd); left; lia).
  assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame i c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
  destruct (HKIND E1 E' R' M1 M' model1 Hag HLF HX HA' HagE' HdE' HLOW) as (more' & code & p' & g' & Hmo' & Hwp & Hpp & Hec' & Hcm & Hls' & Hg' & Hby' & HPS).
  unfold view_chk in HV. destruct (SPA.pview_w (SR.ps_cells ps1) Pb PE CE) as [pv|] eqn:HPV; [|discriminate].
  apply andb_prop in HV as [HV Y12]. apply andb_prop in HV as [HV Y11]. apply andb_prop in HV as [HV Y10]. apply andb_prop in HV as [HV Y9]. apply andb_prop in HV as [HV Y8].
  apply andb_prop in HV as [HV Y7]. apply andb_prop in HV as [HV Y6]. apply andb_prop in HV as [HV Y5]. apply andb_prop in HV as [HV Y4]. apply andb_prop in HV as [HV Y3].
  apply andb_prop in HV as [Y1 Y2]. apply expr_eqb_eq in Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11, Y12.
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & G42 & G43 & G44 & G45 & G46 & G36 & G38 & G39 & G40 & GSE & GSC & GPE & GCE & G32 & G33 & _).
  destruct (FRZW E' HagE') as (G50 & G51 & GWE & _).
  pose proof (kit SPT.NUM) as (BR1 & BR2 & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _). pose proof WFM as (F1 & F2 & F3 & F4 & F5 & _).

  destruct (SPA.parser_view_w E' M' (SR.ps_cells ps1) Pb PE CE pv P more' (PML.ps_done ps) (PML.ps_stack ps) scap (Some (p', e)) HK HPV GP' ltac:(lia) ltac:(lia)) as (buf & HPA' & Hlen & _).
  - rewrite Y7. exact Hmo'.
  - rewrite Y8, G46. reflexivity.
  - rewrite Y10, G38. exact Hby'.
  - rewrite Y11, Y10. unfold SEND0. rewrite GSE, G38. reflexivity.
  - rewrite Y12, Y10, GSC, G38. reflexivity.
  - unfold slen in N4. lia.
  - rewrite Y3. cbn [PSA.wincells fst]. rewrite <- Hwp. unfold PB.uv. symmetry. apply Z_to_bv_bv_unsigned.
  - rewrite Y2. cbn [PSA.wincells snd]. rewrite <- GWE. unfold PB.uv. symmetry. apply Z_to_bv_bv_unsigned.
  - lia.

  - exact HdP'.
  - rewrite Y4, Y5, Y6, Y1, Y10, G43, G44, G41, G38, GCE, GPE in HPA'. rewrite Y9, G36 in Hlen.
    set (ps' := PML.PS (uv E' stv) (PML.ps_sst ps) (PML.ps_nst ps) more' (PML.ps_done ps) level (PML.ps_stack ps) sb scap bcap bptr buf (Some (p', e))) in *.
    destruct (HPS buf) as (Hwf' & Hneed' & HREL & HCUR). fold ps' in Hwf', Hneed', HREL.
    assert (Hden' : CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps') by (rewrite (CH2.blocks_eqb_eq _ _ HBL), (kit SPT.den_BL0 E1 (amb_agree _ _ _ _ HA')); reflexivity).
    pose proof HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr & Hdf). unfold Cred in HC1. subst cr1.
    unfold CH2.cur in HH1. rewrite Hden' in HH1.
    apply (Hcont fx' R' M' model1 (PML.ps_blocks ps' ++ LBo) cr LBo W HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH1].
    exists ps', code, g'.
    split; [exact HPA'|]. split; [exact Hwf'|].
    split.
    { destruct WINF as (ch & Hch & C1 & C2 & Hwd). unfold PML.win_ok, ps'. cbn [PML.ps_win]. exists ch. split; [exact Hch|]. split; [lia|]. split; [exact C2|].
      apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 p' (e - p') HA'); [eapply (L5.defined_sub _ _ _ _ _ Hwd); unfold wlen; lia | right; exists ch; split; [exact Hch | lia]]. }
    split.
    { destruct HBB as (HB1 & HB2). rewrite need0 in HB1. unfold PML.winlen in HB1. rewrite Hwin in HB1. unfold PML.buf_bound. rewrite Hneed'. unfold PML.winlen, ps'. cbn [PML.ps_win PML.ps_buf].
      fold size0 in HB1. split; [lia | exact HB2]. }
    split; [exact Hec'|]. split; [intros Q; exact (Hcm Q)|]. split; [exact Hls'|]. split; [exact Hg'|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HPC|].
    split; [|exact HCUR].
    destruct HREL as [(Q1 & Q2)|Q]; [left | right; exact Q]. split; [exact Q1|]. split; [unfold PMS.consumed; rewrite Hwin; unfold ps'; cbn [PML.ps_win]; split; [reflexivity | lia]|].
    split; reflexivity.
Qed.

Lemma ecell : forall E' (M' : mem) cells, know_ok RSEGS E' M' cells -> env_agree GT.NF E0 E' -> PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) = true -> L5.defined M' E 16 -> PML.ec_at M' E 0.
Proof.
  intros E' M' cells HK Hag Y1 HdE'. destruct (FRZ E' Hag) as (_ & _ & GE & _). destruct OE as (OE1 & OE2 & OE3). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & _).
  split; [|split; [exact HdE' | left; reflexivity]].
  pose proof (PB2.kword32_elim E' M' _ _ E (PB.has_ok E' M' _ _ HK Y1)) as T. rewrite PB2.uv_lit in T by lia. apply T. unfold estart. cbn [a_base a_off]. fold (uv E' Eb). rewrite GE. lia.
Qed.

Lemma wf_exit : forall stz buf p', PML.handled stz -> ~ PML.comment_or_cr stz -> stz <> PML.ST_STRING -> stz <> PML.ST_NUMBER -> (stz = PML.ST_EXPECT_COMMA_OR_END -> 1 <= level) ->
  PML.wf_ps (PML.PS stz (PML.ps_sst ps) (PML.ps_nst ps) true (PML.ps_done ps) level (PML.ps_stack ps) sb scap bcap bptr buf (Some (p', e))).
Proof.
  intros stz buf p' Hh Hnc Hns Hnn Hlv. destruct HWF as (W1 & W2 & W3 & W4 & _). pose proof WFM as (F1 & _ & _ & _ & _ & C & HSC & HCC & HCL).
  unfold PML.wf_ps. cbn [PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st PML.ps_buf].
  split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. exists C, []. rewrite app_nil_r. split; [exact HSC|]. split; [exact HCC|]. intros _.
  split; [exact HCL|]. split; [exact F1|]. split; [exact Hh|]. split; [left; split; [reflexivity | exact Hnc]|]. split; [intros [Q|[]]; exact (Hlv Q) | intros Q; contradiction].
Qed.

Lemma leaf_exit0 : forall c k ps1 pc stz lit, is_leaf 0 c k ps1 (CC.TOther pc) -> PB.exit_base_chk GT.NF RETPC c ps1 = true -> CH2.blocks_eqb (nth 0 G.BLS []) SPT.BL0 = true -> has_cur ps1 = true ->
  PB.has (SR.ps_cells ps1) (KWord (SA Eb 0) 4 (ELit 0)) = true -> view_chk (SR.ps_cells ps1) (cur_of ps1) (ELit stz) (ELit 1) = true -> SPW.rng_is (SR.ps_cells ps1) (APC.esub (cur_of ps1) SEG) lit = true ->
  1 <= lit <= 16384 -> (lit = 1 \/ SPW.rng_in (SR.ps_cells ps1) WLEN lit 16384 = true) ->
  17 < stz <= 27 \/ stz = PML.ST_ACCEPT \/ (stz = PML.ST_EXPECT_COMMA_OR_END /\ SPW.rng_in (SR.ps_cells ps1) (EVar 41) 1 1025 = true) ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok 0 c ps1.
Proof.
  intros c k ps1 pc stz lit IL Hbase HBL Hcur Hec HV HCUR Hlit HWL HST. apply (exit_gen 0%nat c k ps1 pc _ _ IL Hbase HBL Hcur HV).
  intros E1 E' R' M1 M' model1 Hag HLF HX HA' HagE' HdE' HLOW.
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & _). destruct (FRZW E' HagE') as (G50 & G51 & GWE & _).
  pose proof WRNG as (R1 & R2 & R3). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). unfold hl_ceil in R2.
  change (XI 0 E1 M1) with (XI0 M1) in HX. destruct HX as (HS & HBY).
  assert (HWLv : lit <= wlen).
  { destruct HWL as [->|HWL]; [lia|]. pose proof (SPW.rng_in_sound E' M' _ _ _ _ HK HWL) as Q. rewrite G51 in Q. lia. }
  assert (HCV : uv E' (cur_of ps1) = p + lit).
  { pose proof (SPW.rng_is_sound E' M' _ _ _ HK HCUR) as Q. rewrite PB.uv_esub, G50 in Q.
    pose proof (PB.uv_range E' (cur_of ps1)) as Hr. destruct (Z_lt_dec (uv E' (cur_of ps1) - p) 0) as [N|N]; [rewrite PB3.mod_neg64 in Q by lia; lia | rewrite Z.mod_small in Q by lia; lia]. }
  exists true, 0, (p + lit), g.
  split; [rewrite PB2.uv_lit by lia; reflexivity|]. split; [exact HCV|]. split; [unfold wlen in HWLv; lia|].
  split; [exact (ecell E' M' _ HK HagE' Hec HdE')|]. split; [intros Q; exfalso; apply Q; reflexivity|].
  split; [apply (PB2.ls_ok_keep M M'); [|exact HG | exact HLS]; intros a Ha; rewrite (HLOW a (foot_low a Ha)); exact (HS a Ha)|].
  split; [left; reflexivity|]. split; [exact (stack_below M1 M' HLOW HBY)|].
  intros buf. cbv zeta. rewrite PB2.uv_lit by (unfold PML.ST_ACCEPT, PML.ST_EXPECT_COMMA_OR_END in HST; lia).
  assert (HL1 : stz = PML.ST_EXPECT_COMMA_OR_END -> 1 <= level).
  { intros Q. destruct HST as [HST|[HST|(_ & HST)]]; [unfold PML.ST_EXPECT_COMMA_OR_END in Q; lia | rewrite HST in Q; discriminate Q |]. pose proof (SPW.rng_in_sound E' M' _ _ _ _ HK HST) as Q2. rewrite G41 in Q2. lia. }
  split; [split|].
  { apply wf_exit; [| | | | exact HL1]; unfold PML.handled, PML.comment_or_cr, PML.ST_CR, PML.ST_STRING, PML.ST_NUMBER, PML.ST_ACCEPT, PML.ST_EXPECT_COMMA_OR_END in *; lia. }
  { pose proof WFM as (_ & _ & _ & _ & _ & C & HSC & HCC & _).
    apply (SCU.lvl_ok_rootc _ C); [exact HSC | exact HCC |]. intros Hin _. cbn [PML.ps_st PML.ps_level] in Hin |- *.
    destruct HST as [HST|[HST|(HST & _)]]; [exfalso; unfold PMCUR.ICS in Hin; cbn in Hin; unfold PML.ST_EXPECT_COMMA_OR_END, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON, PML.ST_EXPECT_VALUE_OR_END, PML.ST_EXPECT_VALUE, PML.ST_MEMBER_NAME in Hin; lia
                                   | exfalso; subst stz; unfold PMCUR.ICS in Hin; cbn in Hin; unfold PML.ST_ACCEPT, PML.ST_EXPECT_COMMA_OR_END, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON, PML.ST_EXPECT_VALUE_OR_END, PML.ST_EXPECT_VALUE, PML.ST_MEMBER_NAME in Hin; lia
                                   | exact (HL1 HST)]. }
  split; [unfold PML.buf_need; cbn [PML.ps_more PML.ps_st]; destruct (Z.eqb_spec stz PML.ST_STRING) as [Q|_]; [unfold PML.ST_STRING, PML.ST_ACCEPT, PML.ST_EXPECT_COMMA_OR_END in *; lia | reflexivity]|].
  split; [left; split; [reflexivity | lia] | apply (SCU.cur_post_more RSEGS ps _ 0 M' V); reflexivity].
Qed.

Lemma leaf_exitV : forall c k ps1 pc stz, is_leaf JVIS c k ps1 (CC.TOther pc) -> PB.exit_base_chk GT.NF RETPC c ps1 = true -> CH2.blocks_eqb (nth JVIS G.BLS []) SPT.BL0 = true -> has_cur ps1 = true ->
  PB.has (SR.ps_cells ps1) (KWord (SA Eb 0) 4 (ELit 0)) = true -> view_chk (SR.ps_cells ps1) (cur_of ps1) (ELit stz) (ELit 0) = true -> SPW.rng_is (SR.ps_cells ps1) (APC.esub (cur_of ps1) SEG) NLIT = true ->
  SPW.rng_in (SR.ps_cells ps1) WLEN NLIT 16384 = true -> PB.has (SR.ps_cells ps1) (VSU.fl Vb 0 4) = true ->
  stz = PML.ST_ACCEPT \/ (stz = PML.ST_EXPECT_COMMA_OR_END /\ SPW.rng_in (SR.ps_cells ps1) (EVar 41) 1 1025 = true) ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok JVIS c ps1.
Proof.
  intros c k ps1 pc stz IL Hbase HBL Hcur Hec HV HCUR HWL Hfl HST. apply (exit_gen JVIS c k ps1 pc _ _ IL Hbase HBL Hcur HV).
  intros E1 E' R' M1 M' model1 Hag HLF HX HA' HagE' HdE' HLOW.
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & _). destruct (FRZW E' HagE') as (G50 & G51 & GWE & _).
  pose proof WRNG as (R1 & R2 & R3). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). unfold hl_ceil in R2.
  change (XI JVIS E1 M1) with (XI0 M1) in HX. destruct HX as (HS & HBY).
  assert (HWLv : NLIT <= wlen) by (pose proof (SPW.rng_in_sound E' M' _ _ _ _ HK HWL) as Q; rewrite G51 in Q; lia).
  assert (HCV : uv E' (cur_of ps1) = p + NLIT).
  { pose proof (SPW.rng_is_sound E' M' _ _ _ HK HCUR) as Q. rewrite PB.uv_esub, G50 in Q.
    pose proof (PB.uv_range E' (cur_of ps1)) as Hr. destruct (Z_lt_dec (uv E' (cur_of ps1) - p) 0) as [N|N]; [rewrite PB3.mod_neg64 in Q by lia; lia | rewrite Z.mod_small in Q by lia; lia]. }
  assert (HL1 : stz = PML.ST_EXPECT_COMMA_OR_END -> 1 <= level).
  { intros Q. destruct HST as [HST|(_ & HST)]; [rewrite HST in Q; discriminate Q|]. pose proof (SPW.rng_in_sound E' M' _ _ _ _ HK HST) as Q2. rewrite G41 in Q2. lia. }
  exists false, 0, (p + NLIT), g.
  split; [rewrite PB2.uv_lit by lia; reflexivity|]. split; [exact HCV|]. split; [unfold wlen in HWLv; unfold NLIT in *; lia|].
  split; [exact (ecell E' M' _ HK HagE' Hec HdE')|]. split; [intros Q; exfalso; apply Q; reflexivity|].
  split; [apply (PB2.ls_ok_keep M M'); [|exact HG | exact HLS]; intros a Ha; rewrite (HLOW a (foot_low a Ha)); exact (HS a Ha)|].
  split; [left; reflexivity|]. split; [exact (stack_below M1 M' HLOW HBY)|].
  intros buf. cbv zeta. rewrite PB2.uv_lit by (destruct HST as [->|(-> & _)]; unfold PML.ST_ACCEPT, PML.ST_EXPECT_COMMA_OR_END; lia).
  match goal with |- PMCUR.wf_c ?q /\ _ => set (psq := q) end.
  assert (WT : PML.wf_ps (PMCUR.ps_set_more psq true)).
  { unfold psq. cbn [PMCUR.ps_set_more PML.ps_st PML.ps_sst PML.ps_nst PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win].
    apply (wf_exit stz); [| | | | exact HL1]; destruct HST as [->|(-> & _)]; unfold PML.handled, PML.comment_or_cr, PML.ST_CR, PML.ST_STRING, PML.ST_NUMBER, PML.ST_ACCEPT, PML.ST_EXPECT_COMMA_OR_END; lia. }
  assert (LT : PMCUR.lvl_ok (PMCUR.ps_set_more psq true)).
  { pose proof WFM as (_ & _ & _ & _ & _ & C & HSC & HCC & _).
    apply (SCU.lvl_ok_rootc _ C); [unfold psq; cbn [PMCUR.ps_set_more PML.ps_stack]; exact HSC | exact HCC |].
    intros Hin _. unfold psq in Hin |- *. cbn [PMCUR.ps_set_more PML.ps_st PML.ps_level] in Hin |- *.
    destruct HST as [Hz|(Hz & _)]; [exfalso; subst stz; unfold PMCUR.ICS in Hin; cbn in Hin; unfold PML.ST_ACCEPT, PML.ST_EXPECT_COMMA_OR_END, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON, PML.ST_EXPECT_VALUE_OR_END, PML.ST_EXPECT_VALUE, PML.ST_MEMBER_NAME in Hin; lia | exact (HL1 Hz)]. }
  assert (HdV' : L5.defined M' (V + 8) 40).
  { apply (kit SPT.amb_def GT.NF G.BLS Cred JVIS E1 M' model1 (V + 8) 40 HA'); [eapply (L5.defined_sub _ _ _ _ _ (proj2 HVIS)); lia | left; destruct OV as (OV1 & OV2 & _); lia]. }
  assert (ESV : forall q, estart E' (SA Vb q) = V + q) by (intros q; unfold estart; cbn [a_base a_off]; fold (uv E' Vb); rewrite GV; reflexivity).
  assert (HFL : L5.u64_at RSEGS M' (V + 8) 4).
  { pose proof (PB.has_ok E' M' _ _ HK Hfl) as Q. unfold VSU.fl in Q. pose proof (PB2.kword64_elim E' M' _ _ (V + 8) Q) as T. rewrite PB2.uv_lit in T by lia. apply T. rewrite ESV. lia. }
  split; [exact (SCU.wf_c_stop psq eq_refl WT)|].
  split; [unfold PML.buf_need, psq; cbn [PML.ps_more PML.ps_st]; destruct HST as [->|(-> & _)]; reflexivity|].
  split; [left; split; [reflexivity | unfold NLIT; lia]|].
  apply (SCU.cur_post_event RSEGS ps psq M' V VEV eq_refl (conj WT LT)).
  - unfold PMCUR.ev_at, VEV. split; [exact HdV' | exact HFL].
  - unfold PMCUR.ev_rel, VEV, PMCUR.after_value_st, psq. cbn [PML.ps_st PML.ps_level]. split; [destruct HST as [->|(-> & _)]; cbn; tauto | unfold level; reflexivity].
Qed.

Lemma leaf_exit1 : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> Nat.eqb i 0 = false -> Nat.eqb i JVIS = false -> PB.exit_base_chk GT.NF RETPC c ps1 = true -> CH2.blocks_eqb (nth i G.BLS []) SPT.BL0 = true -> has_cur ps1 = true ->
  PB.has (SR.ps_cells ps1) (KWord (SA Eb 0) 4 (ELit 11)) = true -> PB.has (SR.ps_cells ps1) (KWord (SA Eb 8) 8 (ELit PML.OBJ_JSON_CATEGORY)) = true ->
  view_chk (SR.ps_cells ps1) (cur_of ps1) (EVar 42) (ELit 0) = true -> expr_eqb (cur_of ps1) SEG = true -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc IL Hi HiV Hbase HBL Hcur Hec0 Hec8 HV HCUR. apply (exit_gen i c k ps1 pc _ _ IL Hbase HBL Hcur HV).
  intros E1 E' R' M1 M' model1 Hag HLF HX HA' HagE' HdE' HLOW. apply expr_eqb_eq in HCUR.
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & G42 & _). destruct (FRZW E' HagE') as (G50 & G51 & GWE & _).
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OE as (OE1 & OE2 & OE3). pose proof Hpe as Hpe'.
  unfold XI in HX. rewrite Hi, HiV in HX. destruct HX as (HLS2 & HBY).
  assert (ES : forall q, estart E' (SA Eb q) = E + q) by (intros q; unfold estart; cbn [a_base a_off]; fold (uv E' Eb); rewrite GE; reflexivity).
  exists false, 11, p, (PML.regJ g).
  split; [rewrite PB2.uv_lit by lia; reflexivity|]. split; [rewrite HCUR; exact G50|]. split; [lia|].
  split.
  { split; [|split; [exact HdE' | right; split; [lia|]]].
    - pose proof (PB2.kword32_elim E' M' _ _ E (PB.has_ok E' M' _ _ HK Hec0)) as T. rewrite PB2.uv_lit in T by lia. apply T. rewrite ES. lia.
    - pose proof (PB2.kword64_elim E' M' _ _ (E + 8) (PB.has_ok E' M' _ _ HK Hec8)) as T. rewrite PB2.uv_lit in T by (unfold PML.OBJ_JSON_CATEGORY; lia). apply T. apply ES. }
  split; [intros _; reflexivity|].
  split; [exact (kit SPT.ls_below M1 M' (PML.regJ g) ltac:(destruct g; discriminate) HLOW HLS2)|].
  split; [right; split; [reflexivity | lia]|]. split; [exact (stack_below M1 M' HLOW HBY)|].
  intros buf. cbv zeta.
  split; [split; [|apply SCU.lvl_ok_stop; reflexivity]|].
  { destruct HWF as (W1 & W2 & W3 & W4 & (C0 & T0 & W5 & W6 & _)).
    unfold PML.wf_ps. cbn [PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st PML.ps_buf].
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. exists C0, T0. split; [exact W5|]. split; [exact W6|]. intros Q; discriminate Q. }
  split; [reflexivity|]. split; [right; reflexivity | apply SCU.cur_post_err; lia].
Qed.

Lemma leaves : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. cbn [leaf_chk] in X.
  destruct (Z.eqb_spec pc VISPC) as [->|NV].
  { try rewrite Z.eqb_refl in X. apply andb_prop in X as [X XR]. apply andb_prop in X as [Hpc Hi]. apply Z.eqb_eq in Hpc. apply Nat.eqb_eq in Hi. subst i.
    destruct (CH2.ret_of G.RETS 0 k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
    apply andb_prop in XR as [Hj XC]. apply Nat.eqb_eq in Hj.
    destruct (vis_chk c ps1 cj (nth 0 G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. apply Nat.leb_le in XC.
    exact (leaf_vis c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk XC). }
  try (apply Z.eqb_neq in NV; rewrite NV in X).
  destruct (Z.eqb_spec pc SETEC) as [->|N1].
  - apply andb_prop in X as [X XR]. apply andb_prop in X as [Hpc Hi]. apply Z.eqb_eq in Hpc. apply Nat.eqb_eq in Hi. subst i.
    destruct (CH2.ret_of G.RETS 0 k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
    apply andb_prop in XR as [Hj XC]. apply andb_prop in Hj as [Hj HjV]. apply negb_true_iff in Hj, HjV.
    destruct (setec_chk c ps1 cj (nth 0 G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. apply Nat.leb_le in XC.
    exact (leaf_setec c k ps1 j cj ci IL Hret Hcj Hj HjV Hpc Hchk XC).
  - apply andb_prop in X as [X XR]. apply andb_prop in X as [X Hcur]. apply andb_prop in X as [Hbase HBL]. destruct (Nat.eqb i 0) eqn:Hi.
    + apply Nat.eqb_eq in Hi. subst i. apply andb_prop in XR as [XR HCUR]. apply andb_prop in XR as [Hec HV].
      apply (leaf_exit0 c k ps1 pc STSHORT 1 IL Hbase HBL Hcur Hec HV HCUR ltac:(lia) (or_introl eq_refl)). left. unfold STSHORT. lia.
    + destruct (Nat.eqb i JVIS) eqn:HiV.
      * apply Nat.eqb_eq in HiV. subst i. apply andb_prop in XR as [XR XV]. apply andb_prop in XR as [XR Hfl]. apply andb_prop in XR as [XR HWL].
        apply andb_prop in XR as [Hec HCUR]. apply orb_prop in XV as [HV|XV].
        -- exact (leaf_exitV c k ps1 pc PML.ST_ACCEPT IL Hbase HBL Hcur Hec HV HCUR HWL Hfl (or_introl eq_refl)).
        -- apply andb_prop in XV as [HV HLV]. exact (leaf_exitV c k ps1 pc PML.ST_EXPECT_COMMA_OR_END IL Hbase HBL Hcur Hec HV HCUR HWL Hfl (or_intror (conj eq_refl HLV))).
      * apply andb_prop in XR as [XR HCUR]. apply andb_prop in XR as [XR HV]. apply andb_prop in XR as [Hec0 Hec8]. exact (leaf_exit1 i c k ps1 pc IL Hi HiV Hbase HBL Hcur Hec0 Hec8 HV HCUR).
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
  - assert (Hden0 : CH2.den E0 (nth 0 G.BLS []) = PML.ps_blocks ps) by (change (nth 0 G.BLS []) with SPT.BL0; exact (kit SPT.den_BL0 E0 (CC.env_agree_refl _ _))).
    split.
    + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr. split; [unfold CH2.cur; rewrite Hden0; exact HH | reflexivity].
    + change (XI 0 E0 M) with (XI0 M). split; [intros a _; reflexivity | exact (SPT.pa_stack _ _ _ HPA)].
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
Hypothesis SETEC_OK : PMS.set_ec_spec L.
Hypothesis VIS_OK : PMS.visit_null_spec L PMS.PC_VIS_NULL.

Theorem parse_null_ok : PMS.parse_null_spec L HI PML.STRTOD_SCR_V.
Proof.
  unfold PMS.parse_null_spec, PMS.ptrans, PMS.ptrans_g, PMS.ptrans_gb. intros LBo cr sp r P V E B kx bx g ps. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & ((Ha0 & Ha1 & Ha2) & Hmore & Hnex & Hexp) & HPA & (HWF & _) & HWIN & HBB & HVIS & HEC & HLS & HG & HPC & OP & OV & OE & AP1 & AP2 & AP3) Hcont.
  destruct (PML.ps_win ps) as [[p e]|] eqn:Hwin; [|exfalso; apply Hnex; unfold PMS.win_exhausted; rewrite Hwin; exact I].
  pose proof (SPT.pa_def _ _ _ HPA) as HdP.
  destruct (PB2.cell_exists M (P + 160) 8 ltac:(lia)) as (line0 & Rc1 & Hc1); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  destruct (PB2.cell_exists M (P + 168) 8 ltac:(lia)) as (pos0 & Rc2 & Hc2); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  pose proof (SPT.win_le M P ps HPA) as Hle. rewrite Hwin in Hle.
  pose proof HWIN as HW. unfold PML.win_ok in HW. rewrite Hwin in HW. destruct HW as (ch & Hch & C1 & C2 & Hwd).
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _). destruct (Hwf (ch, 16384) ltac:(right; right; exact Hch)) as ((B0 & B1 & B2 & B3 & B4) & _). cbn [fst snd] in *.
  destruct Hentry as (E1 & E2 & E3 & E4 & Hstk). pose proof (L5C.stk_window _ _ _ _ Hstk) as (W1 & W2 & W3). unfold hl_ceil in B4.
  destruct (PB3.bytes_of_defined_r M (Z.to_nat (e - p)) p ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (winb & Hwl & Hwb & Hwr); [rewrite Z2Nat.id by lia; exact Hwd|].
  assert (Hwbl : Z.of_nat (length winb) = e - p) by (rewrite Hwl; apply Z2Nat.id; lia).

  exact (main L HI HIok LAY FPM SETEC_OK VIS_OK LBo cr sp r P V E B kx bx g ps fx R M model K p e HH Hmo HKnil Hfp (conj E1 (conj E2 (conj E3 (conj E4 Hstk)))) Ha0 Ha1 Ha2 Hwin Hmore Hnex Hexp
           HPA HWF HWIN HBB HVIS HEC HLS HG HPC OP OV OE AP1 AP2 AP3 Hcont line0 pos0 winb Hc1 Hc2 (conj Rc1 Rc2) (conj Hwb Hwbl)).

Qed.
End Final.
End ParseNullProof.

