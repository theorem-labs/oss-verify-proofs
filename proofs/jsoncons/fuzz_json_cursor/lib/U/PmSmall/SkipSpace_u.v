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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallPure SmallKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmSmall Require Import SmallAt_u SmallPt_u SmallWin_u SmallCur_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_skip_space_csrc_T_u Cut_skip_space_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module SkipSpaceProof.
Module G := Cut_skip_space_csrc_u.
Module GT := Cut_skip_space_csrc_T_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Definition PCF : Z := PML.PC_SKIP_SPACE.

Definition Pb : expr := EVar 10.  Definition Vb : expr := EVar 49.  Definition Eb : expr := EVar 34.
Definition SEG : expr := EVar 50.  Definition WLEN : expr := EVar 51.  Definition WEND : expr := APC.eadd SEG WLEN.
Definition RETPC : Z := nth 0 GT.ENDS 0.
Definition VECPUSH : Z := PML.PC_VEC_PUSH.
Definition SCR : Z := CH.hd_scr G.HDECL.
Definition CONSTS : PSK.consts := PSK.CONSTS PML.VT_PARSER PML.VT_FUNC PML.VT_VISITOR 0x10000 0xf8000 0x10000 PML.IMG_RO_HI SCR [(-8, 1%nat); (-16, 8%nat); (-24, 9%nat); (-32, 18%nat)] 32.
Definition X0 : PSK.pexprs := SPT.X0w SEG (EVar 42) (EVar 45).
Lemma kn0_eq : CC.cp_know G.cp0 = SPK.kn CONSTS false Pb Vb Eb (EVar 2) WEND X0 ++ SPK.win_f CONSTS Pb Vb Eb (EVar 2) SEG WLEN X0 ++ [KRange WLEN 1 16384].
Proof. vmc_refl. Qed.
Lemma regs0_eq : CC.cp_regs G.cp0 = sr_upd sr_id 11 (APC.eaddz Pb 200).
Proof. vmc_refl. Qed.
Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Abbreviation PE := SPT.PE.  Abbreviation CE := SPT.CE.
Definition jof (pc : Z) : nat := match find (fun r : nat * nat * nat * Z => let '(_, _, _, p) := r in Z.eqb p pc) G.RETS with Some (j, _, _, _) => j | None => 0%nat end.
Definition JPUSH : nat := Eval vm_compute in jof VECPUSH.

Definition NXG : nat := (CC.cp_nx (nth JPUSH G.CPS G.cp0) - APC.NCS - 2)%nat.
Definition GB : expr := EVar NXG.  Definition GC : expr := EVar (NXG + 1).
Definition BL1 : CA.blocks := [(PE, CE); (GB, GC)].
Definition SEND0 : expr := APC.eadd (EVar 38) (EVar 39).
Definition SEND1 : expr := APC.eaddz (APC.eadd (EVar 39) GB) 1.

Definition view_chk (cells : list kentry) (stv sbv sendv scendv wpv : expr) : bool :=
  match SPA.pview_w cells Pb PE CE with
  | Some pv => (expr_eqb (PB4.pv_level pv) (EVar 41) && expr_eqb (PB4.pv_wend pv) WEND && expr_eqb (PB4.pv_wptr pv) wpv && expr_eqb (PB4.pv_st pv) stv
                && expr_eqb (PB4.pv_sst pv) (EVar 43) && expr_eqb (PB4.pv_nst pv) (EVar 44) && expr_eqb (PB4.pv_more pv) (EVar 45) && expr_eqb (PB4.pv_done pv) (EVar 46)
                && expr_eqb (PB4.pv_size pv) (EVar 36) && expr_eqb (PB4.pv_sb pv) sbv && expr_eqb (PB4.pv_send pv) sendv && expr_eqb (PB4.pv_scend pv) scendv)%bool
  | None => false
  end.
Definition cur_of (cells : list kentry) : expr := match CAX.cell_at cells Pb 200 8 with Some e => e | None => ELit 0 end.

Definition cons_chk (cells : list kentry) (wpv : expr) : bool :=
  (SPW.rng_in cells (APC.esub WEND wpv) 0 16384 &&
   (SPW.rng_in cells (APC.esub wpv SEG) 1 16384
    || (SPW.rng_in cells (APC.esub wpv SEG) 0 16384 && match SPW.named_at cells wpv with Some (_, v, lo, hi) => SPW.nonws_chk cells v lo hi | None => false end)))%bool.

Definition xcell_chk (cells : list kentry) : bool :=
  forallb (fun X => match X with KWord (SA (EVar 2) _) 1%nat v => expr_eqb v (EVar 42) | _ => true end) cells.
Definition push_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : bool :=
  let cells := SR.ps_cells ps in
  match PB4.vecpush_chk GT.NF G.HDECL Pb 248 c ps cj BLi BLj with
  | Some ci => (xcell_chk cells && CH2.blocks_eqb BLi SPT.BL0 && CH2.blocks_eqb BLj BL1
                && match CAX.cell_at cells Pb (248 + 8) 8 with Some c8 => expr_eqb c8 SEND0 | None => false end)%bool
  | None => false
  end.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto j _ => (negb (Nat.eqb i JPUSH) && negb (Nat.eqb j JPUSH))%bool
  | CC.TOther pc =>
      if Z.eqb pc VECPUSH then
        (Z.eqb (SR.ps_pc ps) pc && negb (Nat.eqb i JPUSH) &&
         match CH2.ret_of G.RETS i k with
         | Some j => match nth_error G.CPS j with
                     | Some cj => (Nat.eqb j JPUSH && push_chk c ps cj (nth i G.BLS []) (nth j G.BLS []))%bool
                     | None => false end
         | None => false end)%bool
      else (PB.exit_base_chk GT.NF RETPC c ps && PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) &&
            if Nat.eqb i JPUSH
            then (CH2.blocks_eqb (nth i G.BLS []) BL1 && view_chk cells (ELit PML.ST_CR) GB SEND1 (APC.eadd GB GC) (cur_of cells) && SPW.rng_is cells (APC.esub WEND (cur_of cells)) 0)
            else (CH2.blocks_eqb (nth i G.BLS []) SPT.BL0 && view_chk cells (EVar 42) (EVar 38) SEND0 (APC.eadd (EVar 38) (EVar 40)) (cur_of cells) && cons_chk cells (cur_of cells)))%bool
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
Abbreviation SSCR := PML.STRTOD_SCR_V.
Abbreviation SCRC := (PMS.PF_SCR SSCR).

Variables (LBo : list (Z * Z)) (cr : credit) (sp r P V E B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate).
Variables (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet).
Variables (p e b : Z).
Hypothesis HH : hi_heap HI (PML.ps_blocks ps ++ LBo) cr M (m_vmmaps model).
Hypothesis Hmo : PML.model_ok model.
Hypothesis HKnil : K [].
Hypothesis Hfp : PML.fp_ok fx.
Hypothesis Hentry : PML.entry L R M sp r SCRC.
Hypothesis Ha0 : PML.a0 R P.
Hypothesis Ha1 : PML.a1 R (P + 200).
Hypothesis HWS : PML.ws_ok ps.
Hypothesis HCS : if PML.ps_more ps then PML.is_expect (PML.ps_st ps) else PML.ps_st ps = PML.ST_DONE.
Hypothesis Hmore1 : PML.ps_more ps = true.
Hypothesis Hwin : PML.ps_win ps = Some (p, e).
Hypothesis Hpe : p < e.
Hypothesis Hb8 : PML.u8 M p b.
Hypothesis Hbws : In b [9; 10; 13; 32].
Hypothesis HPA : PML.parser_at M P ps.
Hypothesis HWF : PML.wf_ps ps.
Hypothesis HLV : PMCUR.lvl_ok ps.
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
      (code = 0 /\ PMS.consumed ps ps' /\ PML.ps_more ps' = PML.ps_more ps /\ PML.ws_ok ps' /\
       (PML.ps_st ps' = PML.ps_st ps \/ (PML.ps_st ps' = PML.ST_CR /\ PMS.win_exhausted ps')) /\ PML.ps_level ps' = PML.ps_level ps) /\ PMCUR.cur_post RSEGS ps ps' code M' V) ->
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
Definition E0 : env := SPT.E0 mw E ps R line0 pos0 XV ebf.

Lemma ps_mw : PML.ps_set_win ps mw = ps.
Proof. unfold mw. destruct ps; reflexivity. Qed.
Lemma SCRV : CH.hd_scr G.HDECL = 8416.
Proof. reflexivity. Qed.

Lemma WFM : 0 <= level <= 1024 /\ st <> PML.ST_STRING /\ ~ PML.comment_or_cr st /\ 0 <= st <= 255 /\ In scap [66; 132; 264; 528; 1056] /\
  exists C, PML.ps_stack ps = PML.ST_ROOT :: C /\ Forall PML.is_container C /\ (length C <= 1024)%nat.
Proof.
  pose proof HWF as (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)). unfold st, level. destruct (PML.ps_more ps) eqn:Hm.
  - destruct (W7 eq_refl) as (W8 & W9 & W10 & W11 & _).
    assert (HX : PML.ps_st ps <> PML.ST_STRING /\ ~ PML.comment_or_cr (PML.ps_st ps) /\ 0 <= PML.ps_st ps <= 255).
    { unfold PML.is_expect in HCS. unfold PML.ST_STRING, PML.comment_or_cr, PML.ST_CR. cbn [In] in HCS. lia. }
    destruct HX as (X1 & X2 & X3).
    assert (HT : T = []).
    { unfold PML.transient in W11. destruct W11 as [(HT & _)|[(_ & X)|[(S & _ & _ & X)|(S & _ & _ & X)]]]; [exact HT | contradiction | contradiction |]. exfalso. apply X2. right. exact X. }
    subst T. rewrite app_nil_r in W5.
    split; [exact W9|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact W4|]. exists C. split; [exact W5|]. split; [exact W6 | lia].
  - destruct (HWS Hm) as (C0 & Q1 & Q2 & Q3 & Q4). rewrite HCS in *.
    destruct Q3 as [(_ & Q3)|(Q3 & _)]; [|unfold PML.ST_DONE, PML.ST_CR in Q3; discriminate Q3].
    unfold PML.ST_STRING, PML.comment_or_cr, PML.ST_CR, PML.ST_DONE.
    split; [exact Q4|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact W4|]. exists C0. split; [exact Q3|]. split; [exact Q1 | exact Q2].
Qed.
Lemma need0 : PML.buf_need ps = 0.
Proof. pose proof WFM as (_ & F2 & _). unfold PML.buf_need. destruct (Z.eqb_spec (PML.ps_st ps) PML.ST_STRING) as [Q|_]; [contradiction|]. rewrite Bool.andb_false_r. reflexivity. Qed.
Lemma SLEN : slen <= 1025.
Proof. pose proof WFM as (_ & _ & _ & _ & _ & C & HSC & _ & HCL). unfold slen. rewrite HSC. cbn [length]. lia. Qed.

Lemma WINF : exists ch, In (ch, 16384) LBo /\ ch <= p /\ e <= ch + 16384 /\ L5.defined M p wlen.
Proof. pose proof HWIN as HW. unfold PML.win_ok in HW. rewrite Hwin in HW. exact HW. Qed.
Lemma WRNG : 4096 <= p /\ e <= hl_ceil L /\ 1 <= wlen <= 16384.
Proof.
  destruct WINF as (ch & Hch & C1 & C2 & _). destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _).
  destruct (Hwf (ch, 16384) ltac:(right; right; exact Hch)) as ((B0 & B1 & B2 & B3 & B4) & _). cbn [fst snd] in *. unfold wlen. lia.
Qed.

Lemma INST : SPT.inst L HI mw LBo cr sp r P V E E kx bx g ps R M model SCRC G.HDECL Pb Vb Eb line0 pos0 XV ebf.
Proof.
  unfold SPT.inst. destruct Hlpr as (Q1 & Q2). pose proof WFM as (F1 & F2 & F3 & F4 & F5 & _).
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
  split; [unfold PB.uv, Pb; cbn [edenot]; rewrite (SPT.EV0 mw E ps R line0 pos0 XV ebf 10%bv), Ha0; apply u64_of_Z; lia|].
  split; [unfold PB.uv, Vb; cbn [edenot]; change (ev (SPT.E0 mw E ps R line0 pos0 XV ebf) 49) with (Z_to_bv 64 V); apply u64_of_Z; lia|].
  split; [unfold PB.uv, Eb; cbn [edenot]; change (ev (SPT.E0 mw E ps R line0 pos0 XV ebf) 34) with (Z_to_bv 64 E); apply u64_of_Z; lia|].
  split; [reflexivity|]. split; reflexivity.
Qed.
Notation kit X := (X L HI mw LBo cr sp r P V E E kx bx g ps R M model SCRC G.HDECL Pb Vb Eb line0 pos0 XV ebf INST) (only parsing).

Lemma FRZW : forall E', env_agree GT.NF E0 E' -> uv E' SEG = p /\ uv E' WLEN = wlen /\ uv E' WEND = e /\ eb E' = ebf.
Proof.
  intros E' Hag. pose proof WRNG as (R1 & R2 & R3). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). unfold hl_ceil in R2.
  destruct (SPT.FRZx mw E ps R G.HDECL line0 pos0 XV ebf E' 1%nat p Hag ltac:(unfold SPT.NF; lia) eq_refl ltac:(lia)) as (G50 & Geb).
  destruct (SPT.FRZx mw E ps R G.HDECL line0 pos0 XV ebf E' 2%nat wlen Hag ltac:(unfold SPT.NF; lia) eq_refl ltac:(lia)) as (G51 & _).
  change (49 + 1)%nat with 50%nat in G50. change (49 + 2)%nat with 51%nat in G51.
  split; [exact G50|]. split; [exact G51|]. split; [|exact Geb]. unfold WEND. rewrite PB.uv_eadd. unfold SEG, WLEN. rewrite G50, G51. unfold wlen. rewrite Z.mod_small by lia. lia.
Qed.

Lemma At0 : CC.At RSEGS G.cp0 E0 R M.
Proof.
  pose proof WRNG as (R1 & R2 & R3). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OP as (OP1 & OP2 & OP3).
  destruct (FRZW E0 (CC.env_agree_refl _ _)) as (G50 & G51 & GWE & _).
  split.
  - rewrite regs0_eq. apply (regs_ok_pin E0 sr_id R 11%bv); [exact (regs_ok_id R _ _)|].
    rewrite Ha1. rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 (APC.eaddz Pb 200))). fold (uv E0 (APC.eaddz Pb 200)). rewrite PB.uv_eaddz. pose proof (proj1 (proj2 (kit SPT.UU))) as UP. fold E0 in UP. rewrite UP.
    rewrite Z.mod_small by lia. reflexivity.
  - rewrite kn0_eq. unfold know_ok. rewrite !Forall_app. split; [|split].
    + apply (kit SPT.kn_okw CONSTS SEG WEND (EVar 42) (EVar 45) eq_refl eq_refl eq_refl (conj eq_refl eq_refl) (conj eq_refl eq_refl) eq_refl).
      * destruct (kit SPT.FRZ E0 (CC.env_agree_refl _ _)) as (_ & _ & _ & _ & _ & G42 & _). exact G42.
      * destruct (kit SPT.FRZ E0 (CC.env_agree_refl _ _)) as (_ & _ & _ & _ & _ & _ & _ & _ & G45 & _). exact G45.
      * unfold mw. rewrite Hwin. reflexivity.
      * fold E0. unfold mw. rewrite Hwin. cbn [PSA.wincells snd]. rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 WEND)). fold (uv E0 WEND). rewrite GWE. reflexivity.
    + destruct WINF as (ch & Hch & C1 & C2 & Hwd). destruct Hwinb as (Hwb & Hwl).
      apply (kit SPT.winf_ok CONSTS SEG (EVar 42) (EVar 45) p wlen ch winb (conj eq_refl eq_refl) eq_refl Hch C1 ltac:(unfold wlen; lia) Hwb Hwl Hwd eq_refl eq_refl eq_refl).
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

Definition XI0 (M1 : mem) : Prop := (forall a, PB2.ls_foot a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\ L5.bytes_at RSEGS M1 sb (PML.ps_stack ps) /\ PML.u8 M1 p b.
Definition XIP (E1 : env) (M1 : mem) : Prop :=
  (forall a, PB2.ls_foot a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\
  exists b' cap', CH2.den E1 (nth JPUSH G.BLS []) = [(bptr, bcap); (b', cap')] /\ L5.bytes_at RSEGS M1 b' (PML.ps_stack ps ++ [st]) /\ In cap' [66; 132; 264; 528; 1056] /\ slen + 1 <= cap'.
Definition XI (i : nat) (E1 : env) (M1 : mem) : Prop := if Nat.eqb i JPUSH then XIP E1 M1 else XI0 M1.

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
Lemma VADDR : estart E0 (SA Pb 248) = P + 248.
Proof. unfold estart. cbn [a_base a_off]. fold (uv E0 Pb). unfold E0. rewrite (proj1 (proj2 (kit SPT.UU))). reflexivity. Qed.
Lemma VOBJ : sp <= P + 248 /\ P + 248 + 24 <= hl_sptop L /\ (P + 248) mod 8 = 0 /\ (forall a, P + 248 <= a < P + 248 + 24 -> exists w, In w W /\ L5.in_rng w a).
Proof.
  destruct OP as (O1 & O2 & O3). split; [lia|]. split; [lia|]. split; [rewrite Z.add_mod by lia; rewrite O3; reflexivity|].
  intros a Ha. exists (P, 272). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
Qed.
Lemma amb_agree : forall i E1 (M1 : mem) model1, HAMB i E1 M1 model1 -> env_agree GT.NF E0 E1.
Proof. intros i E1 M1 model1 (_ & _ & X & _). exact X. Qed.

Lemma xi0_below : forall (M1 M' : mem), (forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> XI0 M1 -> XI0 M'.
Proof.
  intros M1 M' HLOW (HS & HBY & HB8). pose proof (kit SPT.NUM) as (BR1 & (B0 & B1 & B2 & B3 & B4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _). pose proof WRNG as (R1 & R2 & R3).
  split; [intros a Ha; rewrite (HLOW a (foot_low a Ha)); exact (HS a Ha)|].
  split; [apply (kit SPT.bytes_below M1 M' sb scap (PML.ps_stack ps) HLOW ltac:(lia) B4 ltac:(unfold slen in N4; lia) HBY)|].
  apply (SPW.u8_frame M1 M' p b); [apply HLOW; unfold wlen in R3; lia | exact HB8].
Qed.

Lemma goto_facts : forall i c k ps1 j s, is_leaf i c k ps1 (CC.TGoto j s) ->
  (GT.NF <= CC.cp_nx c)%nat /\ CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) = true /\ CH2.bsubst GT.NF s (nth j G.BLS []) = nth i G.BLS [] /\ Nat.eqb i JPUSH = false /\ Nat.eqb j JPUSH = false.
Proof.
  intros i c k ps1 j s IL.
  pose proof (CH2.leaves_all_sound _ _ _ heap_ok3 _ _ _ _ _ IL) as X. cbn [CH2.leaf_chk3] in X. unfold CH2.goto_amb_chk in X. apply andb_prop in X as [Hf Hb].
  apply CH2.blocks_eqb_eq in Hb. unfold CH2.foot_chk in Hf. apply andb_prop in Hf as [Hf F4]. apply andb_prop in Hf as [Hf F3]. apply Nat.leb_le in F4.
  pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as Y. cbn [leaf_chk] in Y. apply andb_prop in Y as [Y1 Y2]. apply negb_true_iff in Y1, Y2. repeat split; assumption.
Qed.
Lemma goto_cred : forall i c k ps1 j s, is_leaf i c k ps1 (CC.TGoto j s) -> forall E1 E' R' (M1 M' : mem) cr1, env_agree GT.NF E0 E1 ->
  env_agree (CC.cp_nx c) E1 E' -> CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' -> Cred i E1 cr1 -> Cred j (CC.env_over GT.NF s E') cr1.
Proof.
  intros i c k ps1 j s IL E1 E' R' M1 M' cr1 Hag0 Hag HLF HC. destruct (goto_facts _ _ _ _ _ _ IL) as (F1 & F2 & F3 & _).
  assert (Hd : CH2.den (CC.env_over GT.NF s E') (nth j G.BLS []) = CH2.den E1 (nth i G.BLS [])).
  { rewrite <- CH2.den_bsubst, F3. exact (CH2.den_agree _ E1 E' _ Hag F2). }
  exact (CRED_BLK i j E1 _ cr1 Hd HC).
Qed.
Lemma goto_xi : forall i c k ps1 j s, is_leaf i c k ps1 (CC.TGoto j s) -> forall E1 R1 E' R' (M1 M' : mem) model1, CC.At (hl_segs L) c E1 R1 M1 -> HAMB i E1 M1 model1 ->
  env_agree (CC.cp_nx c) E1 E' -> CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' -> XI i E1 M1 -> XI j (CC.env_over GT.NF s E') M'.
Proof.
  intros i c k ps1 j s IL E1 R1 E' R' M1 M' model1 HAt HA Hag HLF HX. destruct (goto_facts _ _ _ _ _ _ IL) as (F1 & _ & _ & Hi & Hj).
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact (amb_agree _ _ _ _ HA) | eapply CC.env_agree_le; [exact Hag | exact F1]]).
  unfold XI in *. rewrite Hi in HX. rewrite Hj. apply (xi0_below M1 M'); [|exact HX].
  apply (below_frame i c E' M1 M' Hc HagE'). exact (CC.lf_frame _ _ _ _ _ _ _ HLF).
Qed.

Lemma leaf_push : forall i c k ps1 j cj, is_leaf i c k ps1 (CC.TOther VECPUSH) -> Nat.eqb i JPUSH = false -> CH2.ret_of G.RETS i k = Some j -> nth_error G.CPS j = Some cj -> j = JPUSH -> SR.ps_pc ps1 = VECPUSH ->
  push_chk c ps1 cj (nth i G.BLS []) (nth j G.BLS []) = true -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 j cj IL Hi Hret Hcj Hj Hpc Hchk. unfold push_chk in Hchk. destruct (PB4.vecpush_chk _ _ _ _ _ _ _ _ _) as [ci|] eqn:HVC; [|discriminate].
  apply andb_prop in Hchk as [Hchk Hc8]. apply andb_prop in Hchk as [Hchk HB1]. apply andb_prop in Hchk as [Hx HB0].
  apply CH2.blocks_eqb_eq in HB0, HB1.
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  apply (PB4.vecpush_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K HKnil XI DEF0
           Pb 248 eq_refl (P + 248) VADDR VOBJ VECPUSH_OK i c k ps1 j cj ci IL Hret Hcj Hpc HVC).
  intros E1 E' R' M1 M' model1 cr1 b1 sbe sce c8 xv xk HagE' Hag HLF HA' HX HBL Hcell8 Hcellx HH1 HC1.
  rewrite HB0 in HBL. unfold SPT.BL0 in HBL. injection HBL as <- <- <-.
  rewrite Hcell8 in Hc8. apply expr_eqb_eq in Hc8. subst c8.
  destruct (PB.cell_at_has _ _ _ _ _ Hcellx) as (b0 & Hin & ->). unfold xcell_chk in Hx. rewrite forallb_forall in Hx. specialize (Hx _ Hin). cbv beta iota in Hx. apply expr_eqb_eq in Hx. subst xv.
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & G42 & G43 & G44 & G45 & G46 & G36 & G38 & G39 & G40 & GSE & GSC & GPE & GCE & G32 & G33 & _).
  pose proof WFM as (F1 & F2 & F3 & F4 & F5 & C & HSC & HCC & HCL). pose proof SLEN as HSL.
  pose proof (kit SPT.NUM) as (BR1 & (B0 & B1 & B2 & B3 & B4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _).
  assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame i c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
  unfold XI in HX. rewrite Hi in HX. destruct (xi0_below M1 M' HLOW HX) as (HS & HBY & _).
  assert (Hden1 : CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps) by (rewrite HB0; exact (kit SPT.den_BL0 E1 (amb_agree _ _ _ _ HA'))).
  assert (HC1' : PPS.bufcred L cr1 bcap (PPS.stk_kx L scap + kx) (PPS.stk_bx L scap + bx)) by (unfold Cred, scap_of in HC1; rewrite Hden1 in HC1; exact HC1).
  destruct HPC as (K0 & B0' & _).
  assert (GROW : Z.of_nat (length (PML.ps_stack ps)) = scap -> In scap [66; 132; 264; 528]) by (intros Q; cbn [In] in F5 |- *; unfold slen, scap in *; lia).
  exists (PML.ps_stack ps).
  split; [rewrite G38; exact HBY|].
  split; [unfold SEND0; rewrite GSE, G38; reflexivity|].
  split; [unfold slen in HSL; lia|].
  split; [rewrite G40; unfold slen in N4; lia|].
  split; [rewrite G40; exact F5|].
  split; [rewrite G40; intros Q; exact (proj1 (PSS.stk_grow L cr1 bcap scap kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) K0 B0' (GROW Q) HC1'))|].
  intros E2 M2 LBk spc b2 cap2 cr2 Hag2 HP Hincl Hby Hden2 Hcase. subst j. cbn [fst snd] in Hden2. fold (uv E' PE) (uv E' CE) in Hden2. rewrite GPE, GCE in Hden2.
  rewrite G40, G38 in Hcase. rewrite G42 in Hby.
  split.
  - unfold XI. rewrite Nat.eqb_refl. split.
    + intros a Ha. rewrite <- (HS a Ha). apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). apply (kit SPT.lsfoot_kept).
      * exact Ha.
      * intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. pose proof (foot_low a Ha) as Q. pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OP as (O1 & _). unfold hl_ceil in *. lia.
    + exists b2, cap2. split; [exact Hden2|]. split; [exact Hby|].
      split; [destruct Hcase as [(_ & -> & _ & _)|(-> & _ & Q)]; [exact F5|]; specialize (GROW Q); cbn [In] in GROW |- *; lia|].
      unfold slen. destruct Hcase as [(_ & -> & _ & Q)|(-> & _ & Q)]; lia.
  - unfold Cred, scap_of. rewrite Hden2. cbn [nth snd].
    destruct Hcase as [(_ & -> & -> & _)|(-> & -> & Q)]; [exact HC1'|].
    exact (proj2 (PSS.stk_grow L cr1 bcap scap kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) K0 B0' (GROW Q) HC1')).
Qed.

Lemma ecell : forall E' (M' : mem) cells, know_ok RSEGS E' M' cells -> env_agree GT.NF E0 E' -> PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) = true -> L5.defined M' E 16 -> PML.ec_at M' E 0.
Proof.
  intros E' M' cells HK Hag Y1 HdE'. destruct (FRZ E' Hag) as (_ & _ & GE & _). destruct OE as (OE1 & OE2 & OE3). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & _).
  split; [|split; [exact HdE' | left; reflexivity]].
  pose proof (PB2.kword32_elim E' M' _ _ E (PB.has_ok E' M' _ _ HK Y1)) as T. rewrite PB2.uv_lit in T by lia. apply T. unfold estart. cbn [a_base a_off]. fold (uv E' Eb). rewrite GE. lia.
Qed.
Lemma exit_gen : forall i c k ps1 pc stv sbv sendv scendv wpv,
  is_leaf i c k ps1 (CC.TOther pc) -> PB.exit_base_chk GT.NF RETPC c ps1 = true -> PB.has (SR.ps_cells ps1) (KWord (SA Eb 0) 4 (ELit 0)) = true ->
  view_chk (SR.ps_cells ps1) stv sbv sendv scendv wpv = true ->
  (forall E1 E' R' (M1 M' : mem) model1, env_agree (CC.cp_nx c) E1 E' -> CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' -> XI i E1 M1 -> HAMB i E1 M' model1 -> env_agree GT.NF E0 E' ->
      exists (stack' : list Z) (scap' p' : Z),
        L5.bytes_at RSEGS M' (uv E' sbv) stack' /\ uv E' sendv = uv E' sbv + Z.of_nat (length stack') /\ uv E' scendv = uv E' sbv + scap' /\
        Z.of_nat (length stack') <= scap' /\ In scap' [66; 132; 264; 528; 1056] /\
        uv E' wpv = p' /\ p < p' <= e /\ PML.ls_ok g M' /\
        CH2.den E1 (nth i G.BLS []) = [(bptr, bcap); (uv E' sbv, scap')] /\
        forall buf, let ps' := PML.PS (uv E' stv) (PML.ps_sst ps) (PML.ps_nst ps) (PML.ps_more ps) (PML.ps_done ps) level stack' (uv E' sbv) scap' bcap bptr buf (Some (p', e)) in
          PMCUR.wf_c ps' /\ PML.buf_need ps' = 0 /\ PML.ws_ok ps' /\ (PML.ps_st ps' = PML.ps_st ps \/ (PML.ps_st ps' = PML.ST_CR /\ p' = e))) ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc stv sbv sendv scendv wpv IL Hbase Hec HV HKIND fx' E1 R1 M1 model1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct Hentry as (Hra & Hraok & _).
  assert (HSC : SCRC = 9968) by reflexivity.
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  apply (PB.exit_ret L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K XI DEF0 (fun _ => 0) (fun _ => 0) SCRC
           ltac:(rewrite SCRV; lia) ltac:(lia) S5 R (SPT.EV0 mw E ps R line0 pos0 XV ebf) r Hra Hraok heap_ok3 RETPC i c k ps1 _ ret_at IL Hbase fx' E1 R1 M1 model1 E' R' M' HAt HAmb Hag HLF).
  intros HRP HP HA' HagE'.
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct OP as (OP1 & OP2 & OP3), OE as (OE1 & OE2 & OE3).
  pose proof (SPT.pa_def _ _ _ HPA) as HdefP. destruct HEC as (_ & HEd & _).
  assert (HdP' : L5.defined M' P 272) by (apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 P 272 HA' HdefP); left; lia).
  assert (HdE' : L5.defined M' E 16) by (apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 E 16 HA' HEd); left; lia).
  destruct (HKIND E1 E' R' M1 M' model1 Hag HLF HX HA' HagE') as (stack' & scap' & p' & Hby' & Hse & Hsc & Hle & Hin' & Hwp & Hpp & Hls' & Hden & HPS).
  unfold view_chk in HV. destruct (SPA.pview_w (SR.ps_cells ps1) Pb PE CE) as [pv|] eqn:HPV; [|discriminate].
  apply andb_prop in HV as [HV Y12]. apply andb_prop in HV as [HV Y11]. apply andb_prop in HV as [HV Y10]. apply andb_prop in HV as [HV Y9]. apply andb_prop in HV as [HV Y8].
  apply andb_prop in HV as [HV Y7]. apply andb_prop in HV as [HV Y6]. apply andb_prop in HV as [HV Y5]. apply andb_prop in HV as [HV Y4]. apply andb_prop in HV as [HV Y3].
  apply andb_prop in HV as [Y1 Y2]. apply expr_eqb_eq in Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11, Y12.
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & G42 & G43 & G44 & G45 & G46 & G36 & G38 & G39 & G40 & GSE & GSC & GPE & GCE & G32 & G33 & _).
  destruct (FRZW E' HagE') as (G50 & G51 & GWE & _).
  destruct (SPA.parser_view_w E' M' (SR.ps_cells ps1) Pb PE CE pv P (PML.ps_more ps) (PML.ps_done ps) stack' scap' (Some (p', e)) HK HPV GP' ltac:(lia) ltac:(lia)) as (buf & HPA' & Hlen & _).
  - rewrite Y7. exact G45.
  - rewrite Y8, G46. reflexivity.
  - rewrite Y10. exact Hby'.
  - rewrite Y11, Y10. exact Hse.
  - rewrite Y12, Y10. exact Hsc.
  - exact Hle.
  - rewrite Y3. cbn [PSA.wincells fst]. rewrite <- Hwp. unfold PB.uv. symmetry. apply Z_to_bv_bv_unsigned.
  - rewrite Y2. cbn [PSA.wincells snd]. rewrite <- GWE. unfold PB.uv. symmetry. apply Z_to_bv_bv_unsigned.
  - lia.
  - exact HdP'.
  - rewrite Y4, Y5, Y6, Y1, Y10, G43, G44, G41, GCE, GPE in HPA'. rewrite Y9, G36 in Hlen.
    set (ps' := PML.PS (uv E' stv) (PML.ps_sst ps) (PML.ps_nst ps) (PML.ps_more ps) (PML.ps_done ps) level stack' (uv E' sbv) scap' bcap bptr buf (Some (p', e))) in *.
    destruct (HPS buf) as (Hwf' & Hneed' & Hws' & HST). fold ps' in Hwf', Hneed', Hws', HST.
    assert (Hden' : CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps') by (rewrite Hden; reflexivity).
    pose proof HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr & Hdf).
    unfold CH2.cur in HH1. rewrite Hden' in HH1.
    apply (Hcont fx' R' M' model1 (PML.ps_blocks ps' ++ LBo) cr1 LBo W HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH1].
    exists ps', 0, g.
    split; [exact HPA'|]. split; [exact Hwf'|].
    split.
    { destruct WINF as (ch & Hch & C1 & C2 & Hwd). unfold PML.win_ok, ps'. cbn [PML.ps_win]. exists ch. split; [exact Hch|]. split; [lia|]. split; [exact C2|].
      apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 p' (e - p') HA'); [eapply (L5.defined_sub _ _ _ _ _ Hwd); unfold wlen; lia | right; exists ch; split; [exact Hch | lia]]. }
    split.
    { destruct HBB as (HB1 & HB2). rewrite need0 in HB1. unfold PML.winlen in HB1. rewrite Hwin in HB1. unfold PML.buf_bound. rewrite Hneed'. unfold PML.winlen, ps'. cbn [PML.ps_win PML.ps_buf].
      fold size0 in HB1. split; [lia | exact HB2]. }
    split; [exact (ecell E' M' _ HK HagE' Hec HdE')|]. split; [intros Q; exfalso; apply Q; reflexivity|]. split; [exact Hls'|]. split; [left; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact (proj1 (cred_pc i E1 cr1 ps' Hden' eq_refl Hin') HC1)|].
    split; [|exact (SCU.cur_post_more RSEGS ps ps' 0 M' V ltac:(unfold ps'; cbn [PML.ps_more]; exact Hmore1) eq_refl)].
    split; [reflexivity|]. split; [unfold PMS.consumed; rewrite Hwin; unfold ps'; cbn [PML.ps_win]; split; [reflexivity | exact Hpp]|]. split; [reflexivity|]. split; [exact Hws'|].
    split; [|reflexivity]. destruct HST as [Q|(Q1 & Q2)]; [left; exact Q | right; split; [exact Q1 | unfold PMS.win_exhausted, ps'; cbn [PML.ps_win]; exact Q2]].
Qed.

Lemma leaf_exit0 : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> Nat.eqb i JPUSH = false -> PB.exit_base_chk GT.NF RETPC c ps1 = true ->
  PB.has (SR.ps_cells ps1) (KWord (SA Eb 0) 4 (ELit 0)) = true -> CH2.blocks_eqb (nth i G.BLS []) SPT.BL0 = true ->
  view_chk (SR.ps_cells ps1) (EVar 42) (EVar 38) SEND0 (APC.eadd (EVar 38) (EVar 40)) (cur_of (SR.ps_cells ps1)) = true -> cons_chk (SR.ps_cells ps1) (cur_of (SR.ps_cells ps1)) = true ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc IL Hi Hbase Hec HBL HV HCONS. apply (exit_gen i c k ps1 pc _ _ _ _ _ IL Hbase Hec HV).
  intros E1 E' R' M1 M' model1 Hag HLF HX HA' HagE'. set (wpv := cur_of (SR.ps_cells ps1)) in *.
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & G42 & G43 & G44 & G45 & G46 & G36 & G38 & G39 & G40 & GSE & GSC & GPE & GCE & G32 & G33 & _).
  destruct (FRZW E' HagE') as (G50 & G51 & GWE & _).
  pose proof WFM as (F1 & F2 & F3 & F4 & F5 & C & HSC & HCC & HCL). pose proof WRNG as (R1 & R2 & R3).
  pose proof (kit SPT.NUM) as (BR1 & (B0 & B1 & B2 & B3 & B4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _).
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame i c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
  unfold XI in HX. rewrite Hi in HX. destruct (xi0_below M1 M' HLOW HX) as (HS & HBY & HB8).

  assert (HPP : p < uv E' wpv <= e).
  { unfold cons_chk in HCONS. fold wpv in HCONS. apply andb_prop in HCONS as [C1 C2].
    pose proof (SPW.rng_in_sound E' M' _ _ _ _ HK C1) as Q1. rewrite PB.uv_esub, GWE in Q1.
    assert (HW : forall lo, 0 <= lo -> lo <= uv E' (APC.esub wpv SEG) <= 16384 -> p + lo <= uv E' wpv <= e).
    { intros lo Hlo Q2. rewrite PB.uv_esub, G50 in Q2. replace e with (p + wlen) by (unfold wlen; lia).
      apply (SPW.win_pos p wlen (uv E' wpv) lo ltac:(lia) ltac:(lia) ltac:(unfold wlen, hl_ceil in *; lia) (PB.uv_range E' wpv) Hlo Q2). replace (p + wlen) with e by (unfold wlen; lia). lia. }
    apply orb_prop in C2 as [C2|C2].
    - pose proof (HW 1 ltac:(lia) (SPW.rng_in_sound E' M' _ _ _ _ HK C2)). lia.
    - apply andb_prop in C2 as [C2 C3]. pose proof (HW 0 ltac:(lia) (SPW.rng_in_sound E' M' _ _ _ _ HK C2)) as Q.
      destruct (SPW.named_at (SR.ps_cells ps1) wpv) as [[[[a v] lo] hi]|] eqn:HN; [|discriminate].
      destruct (SPW.named_sound E' M' _ _ _ _ _ _ HK HN) as (N8 & Nr & Nl & Nh).
      pose proof (SPW.nonws_sound E' M' _ _ _ _ HK C3 Nr) as NWS.
      destruct (Z.eq_dec (uv E' wpv) p) as [Heq|Hne]; [|lia]. exfalso. apply NWS. rewrite Heq in N8.
      rewrite (SPW.u8_inj M' p (uv E' v) b N8 HB8 ltac:(lia) ltac:(cbn [In] in Hbws; lia)). exact Hbws. }
  exists (PML.ps_stack ps), scap, (uv E' wpv).
  split; [rewrite G38; exact HBY|].
  split; [unfold SEND0; rewrite GSE, G38; reflexivity|]. split; [rewrite GSC, G38; reflexivity|].
  split; [unfold slen in N4; lia|]. split; [exact F5|]. split; [reflexivity|]. split; [exact HPP|].
  split; [apply (PB2.ls_ok_keep M M'); [exact HS | exact HG | exact HLS]|].
  split; [rewrite (CH2.blocks_eqb_eq _ _ HBL), (kit SPT.den_BL0 E1 (amb_agree _ _ _ _ HA')), G38; reflexivity|].
  intros buf. cbv zeta. rewrite G42, G38.
  split; [split; [|exact HLV]|].
  { destruct HWF as (W1 & W2 & W3 & W4 & (C0 & T0 & W5 & W6 & W7)).
    unfold PML.wf_ps. cbn [PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st PML.ps_buf].
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. exists C0, T0. split; [exact W5|]. split; [exact W6|]. intros Hm.
    destruct (W7 Hm) as (W8 & W9 & W10 & W11 & W12 & _). repeat (split; [assumption|]). intros Q. exfalso. rewrite Hm in HCS. unfold PML.is_expect, PML.ST_NUMBER in *. cbn [In] in HCS. lia. }
  split; [unfold PML.buf_need; cbn [PML.ps_more PML.ps_st]; destruct (Z.eqb_spec (PML.ps_st ps) PML.ST_STRING) as [Q|_]; [contradiction | rewrite Bool.andb_false_r; reflexivity]|].
  split; [exact HWS | left; reflexivity].
Qed.

Lemma leaf_exit1 : forall c k ps1 pc, is_leaf JPUSH c k ps1 (CC.TOther pc) -> PB.exit_base_chk GT.NF RETPC c ps1 = true ->
  PB.has (SR.ps_cells ps1) (KWord (SA Eb 0) 4 (ELit 0)) = true -> CH2.blocks_eqb (nth JPUSH G.BLS []) BL1 = true ->
  view_chk (SR.ps_cells ps1) (ELit PML.ST_CR) GB SEND1 (APC.eadd GB GC) (cur_of (SR.ps_cells ps1)) = true -> SPW.rng_is (SR.ps_cells ps1) (APC.esub WEND (cur_of (SR.ps_cells ps1))) 0 = true ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok JPUSH c ps1.
Proof.
  intros c k ps1 pc IL Hbase Hec HBL HV HEND. apply (exit_gen JPUSH c k ps1 pc _ _ _ _ _ IL Hbase Hec HV).
  intros E1 E' R' M1 M' model1 Hag HLF HX HA' HagE'. set (wpv := cur_of (SR.ps_cells ps1)) in *.
  assert (Hc : nth_error G.CPS JPUSH = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  unfold XI in HX. rewrite Nat.eqb_refl in HX. destruct HX as (HS & b' & cap' & Hden & Hby & Hcin & Hcap).
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & G42 & G43 & G44 & G45 & G46 & G36 & G38 & G39 & G40 & GSE & GSC & GPE & GCE & G32 & G33 & _).
  destruct (FRZW E' HagE') as (G50 & G51 & GWE & _).
  pose proof WFM as (F1 & F2 & F3 & F4 & F5 & C & HSC & HCC & HCL). pose proof WRNG as (R1 & R2 & R3). pose proof SLEN as HSL.

  rewrite (CH2.blocks_eqb_eq _ _ HBL) in Hden. unfold CH2.den, BL1 in Hden. cbn [map fst snd] in Hden. fold (uv E1 PE) (uv E1 CE) (uv E1 GB) (uv E1 GC) in Hden. injection Hden as _ _ HGB HGC.
  assert (Hag1 : env_agree (CC.cp_nx (nth JPUSH G.CPS G.cp0)) E1 E') by (rewrite (nth_error_nth _ _ G.cp0 Hc); exact Hag).
  assert (HGB' : uv E' GB = b') by (rewrite (PB.uv_agree _ E1 E' GB Hag1 ltac:(vm_compute; reflexivity)); exact HGB).
  assert (HGC' : uv E' GC = cap') by (rewrite (PB.uv_agree _ E1 E' GC Hag1 ltac:(vm_compute; reflexivity)); exact HGC).
  pose proof HA' as (_ & _ & _ & (cr1 & HH1 & _) & _ & _). destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _).
  assert (Hinb : In (b', cap') (CH2.cur LBo G.BLS JPUSH E1)).
  { unfold CH2.cur. apply in_or_app. left. rewrite (CH2.blocks_eqb_eq _ _ HBL). unfold CH2.den, BL1. cbn [map fst snd]. fold (uv E1 GB) (uv E1 GC). rewrite HGB, HGC. right. left. reflexivity. }
  destruct (Hwf _ Hinb) as ((B0 & B1 & B2 & B3 & B4) & _). cbn [fst snd] in B0, B1, B2, B3, B4.
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame JPUSH c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
  assert (Hlen1 : Z.of_nat (length (PML.ps_stack ps ++ [st])) = slen + 1) by (rewrite length_app; cbn [length]; unfold slen; lia).
  assert (HPE' : uv E' wpv = e).
  { pose proof (SPW.rng_is_sound E' M' _ _ _ HK HEND) as Q. rewrite PB.uv_esub, GWE in Q. symmetry. apply (SPW.mod64_zero e (uv E' wpv)); [unfold hl_ceil in *; lia | exact (PB.uv_range E' wpv) | exact Q]. }
  exists (PML.ps_stack ps ++ [st]), cap', e.
  split; [rewrite HGB'; apply (kit SPT.bytes_below M1 M' b' cap' _ HLOW ltac:(lia) B4 ltac:(rewrite Hlen1; lia) Hby)|].
  split; [unfold SEND1; rewrite PB.uv_eaddz, PB.uv_eadd, G39, HGB', Hlen1; unfold hl_ceil in *; rewrite (Z.mod_small (slen + b')) by (unfold slen; lia); rewrite Z.mod_small by (unfold slen; lia); lia|].
  split; [rewrite PB.uv_eadd, HGB', HGC'; unfold hl_ceil in *; apply Z.mod_small; lia|].
  split; [rewrite Hlen1; exact Hcap|]. split; [exact Hcin|]. split; [exact HPE'|]. split; [lia|].
  split; [apply (PB2.ls_ok_keep M M'); [|exact HG | exact HLS]; intros a Ha; rewrite (HLOW a (foot_low a Ha)); exact (HS a Ha)|].
  split; [rewrite (CH2.blocks_eqb_eq _ _ HBL); unfold CH2.den, BL1; cbn [map fst snd]; fold (uv E1 PE) (uv E1 CE) (uv E1 GB) (uv E1 GC);
          destruct (FRZ E1 (amb_agree _ _ _ _ HA')) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPE1 & HCE1 & _); rewrite HPE1, HCE1, HGB, HGC, HGB'; reflexivity|].
  intros buf. cbv zeta. rewrite PB2.uv_lit by (unfold PML.ST_CR; lia).
  split; [split|].
  { destruct HWF as (W1 & W2 & W3 & W4 & (C0 & T0 & W5 & W6 & W7)).
    unfold PML.wf_ps. cbn [PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st PML.ps_buf].
    split; [exact W1|]. split; [exact W2|]. split; [apply Nat2Z.inj_le; rewrite Hlen1; lia|]. split; [exact Hcin|].
    exists C, [st]. split; [rewrite HSC; reflexivity|]. split; [exact HCC|]. intros Hm.
    rewrite Hm in HCS. destruct (W7 Hm) as (W8 & W9 & W10 & W11 & W12 & _).
    assert (HT0 : T0 = []).
    { unfold PML.transient in W11. fold st in W11. destruct W11 as [(HT & _)|[(_ & X)|[(S & _ & _ & X)|(S & _ & _ & X)]]]; [exact HT | contradiction | contradiction |]. exfalso. apply F3. right. exact X. }
    subst T0. rewrite app_nil_r in W5. rewrite HSC in W5. injection W5 as W5. subst C0.
    split; [exact W8|]. split; [exact W9|]. split; [unfold PML.handled, PML.ST_CR; lia|].
    split; [right; right; left; exists st; split; [exact HCS | split; [reflexivity | right; reflexivity]]|].
    split; [intros [Q|[Q|[]]]; [unfold PML.ST_CR, PML.ST_EXPECT_COMMA_OR_END in Q; discriminate Q | apply W12; left; fold st; exact Q]|].
    intros Q. unfold PML.ST_CR, PML.ST_NUMBER in Q. discriminate Q. }
  { intros Hm [Hin|(x & Hx & Hin)]; cbn [PML.ps_st PML.ps_stack PML.ps_level] in *.
    - exfalso. unfold PMCUR.ICS in Hin. cbn in Hin. unfold PML.ST_CR, PML.ST_EXPECT_COMMA_OR_END, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON, PML.ST_EXPECT_VALUE_OR_END, PML.ST_EXPECT_VALUE, PML.ST_MEMBER_NAME in Hin. lia.
    - apply in_app_or in Hx as [Hx|[Hx|[]]]; [apply (HLV Hmore1); right; exists x; split; assumption | subst x; apply (HLV Hmore1); left; exact Hin]. }
  split; [unfold PML.buf_need; cbn [PML.ps_more PML.ps_st]; change (PML.ST_CR =? PML.ST_STRING) with false; rewrite Bool.andb_false_r; reflexivity|].
  split; [|right; split; reflexivity].
  unfold PML.ws_ok. cbn [PML.ps_more PML.ps_st PML.ps_stack PML.ps_level]. intros Hm. rewrite Hm in HCS. exists C. split; [exact HCC|]. split; [exact HCL|].
  split; [right; split; [reflexivity | rewrite HSC; unfold st; cbv iota in HCS; rewrite HCS; reflexivity]|]. exact F1.
Qed.

Lemma leaves : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. cbn [leaf_chk] in X.
  destruct (Z.eqb_spec pc VECPUSH) as [->|N1].
  - apply andb_prop in X as [X XR]. apply andb_prop in X as [Hpc Hi]. apply Z.eqb_eq in Hpc. apply negb_true_iff in Hi.
    destruct (CH2.ret_of G.RETS i k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
    apply andb_prop in XR as [Hj XC]. apply Nat.eqb_eq in Hj. exact (leaf_push i c k ps1 j cj IL Hi Hret Hcj Hj Hpc XC).
  - apply andb_prop in X as [X XR]. apply andb_prop in X as [Hbase Hec]. destruct (Nat.eqb i JPUSH) eqn:Hi.
    + apply Nat.eqb_eq in Hi. subst i. apply andb_prop in XR as [XR HEND]. apply andb_prop in XR as [HBL HV]. exact (leaf_exit1 c k ps1 pc IL Hbase Hec HBL HV HEND).
    + apply andb_prop in XR as [XR HCONS]. apply andb_prop in XR as [HBL HV]. exact (leaf_exit0 i c k ps1 pc IL Hi Hbase Hec HBL HV HCONS).
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
  - exact goto_cred.
  - exact goto_xi.
  - exact leaves.
  - reflexivity.
  - rewrite LS. exact At0.
  - pose proof WFM as (_ & _ & _ & _ & F5 & _).
    assert (Hden0 : CH2.den E0 (nth 0 G.BLS []) = PML.ps_blocks ps) by (change (nth 0 G.BLS []) with SPT.BL0; exact (kit SPT.den_BL0 E0 (CC.env_agree_refl _ _))).
    split.
    + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr. split; [unfold CH2.cur; rewrite Hden0; exact HH | exact (proj2 (cred_pc 0%nat E0 cr ps Hden0 eq_refl F5) HPC)].
    + change (XI 0 E0 M) with (XI0 M). split; [intros a _; reflexivity|]. split; [exact (SPT.pa_stack _ _ _ HPA) | exact Hb8].
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

Theorem skip_space_ok : PMS.skip_space_spec L HI PML.STRTOD_SCR_V.
Proof.
  unfold PMS.skip_space_spec, PMS.ptrans, PMS.ptrans_g, PMS.ptrans_gb. intros LBo cr sp r P V E B kx bx g ps. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & (Ha0 & Ha1 & HWS & Hmore1 & Hexp & (p & e & b & Hwin & Hpe & Hb8 & Hbws)) & HPA & (HWF & HLV) & HWIN & HBB & HVIS & HEC & HLS & HG & HPC & OP & OV & OE & AP1 & AP2 & AP3) Hcont.
  assert (HCS : if PML.ps_more ps then PML.is_expect (PML.ps_st ps) else PML.ps_st ps = PML.ST_DONE) by (rewrite Hmore1; exact Hexp).
  pose proof (SPT.pa_def _ _ _ HPA) as HdP.
  destruct (PB2.cell_exists M (P + 160) 8 ltac:(lia)) as (line0 & Rc1 & Hc1); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  destruct (PB2.cell_exists M (P + 168) 8 ltac:(lia)) as (pos0 & Rc2 & Hc2); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  pose proof HWIN as HW. unfold PML.win_ok in HW. rewrite Hwin in HW. destruct HW as (ch & Hch & C1 & C2 & Hwd).
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _). destruct (Hwf (ch, 16384) ltac:(right; right; exact Hch)) as ((B0 & B1 & B2 & B3 & B4) & _). cbn [fst snd] in *.
  destruct Hentry as (E1 & E2 & E3 & E4 & Hstk). pose proof (L5C.stk_window _ _ _ _ Hstk) as (W1 & W2 & W3). unfold hl_ceil in B4.
  destruct (PB3.bytes_of_defined_r M (Z.to_nat (e - p)) p ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (winb & Hwl & Hwb & Hwr); [rewrite Z2Nat.id by lia; exact Hwd|].
  assert (Hwbl : Z.of_nat (length winb) = e - p) by (rewrite Hwl; apply Z2Nat.id; lia).
  exact (main L HI HIok LAY FPM VECPUSH_OK LBo cr sp r P V E B kx bx g ps fx R M model K p e b HH Hmo HKnil Hfp (conj E1 (conj E2 (conj E3 (conj E4 Hstk)))) Ha0 Ha1 HWS HCS Hmore1 Hwin Hpe Hb8 Hbws
           HPA HWF HLV HWIN HBB HVIS HEC HLS HG HPC OP OV OE AP1 AP2 AP3 Hcont line0 pos0 winb Hc1 Hc2 (conj Rc1 Rc2) (conj Hwb Hwbl)).
Qed.
End Final.
End SkipSpaceProof.

