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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallPure SmallKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmSmall Require Import SmallAt_u SmallPt_u SmallWin_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmSmall Require Import SmallCur_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import VisitSums.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_end_string_value_csrc_T_u Cut_end_string_value_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module EndStringValueProof.
Module G := Cut_end_string_value_csrc_u.
Module GT := Cut_end_string_value_csrc_T_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Definition PCF : Z := PML.PC_END_STRING.
Definition Pb : expr := EVar 10.  Definition Vb : expr := EVar 13.  Definition Eb : expr := EVar 14.
Definition SX : expr := EVar 11.  Definition LENX : expr := EVar 12.  Definition TAG : expr := EVar 49.
Definition RETPC : Z := nth 0 GT.ENDS 0.
Definition DEADPC : Z := nth 1 GT.ENDS 0.
Definition VALIDATE : Z := PML.PC_VALIDATE.
Definition PARENT : Z := PML.PC_PARENT.
Definition POP : Z := PML.PC_POP_STATE.
Definition SETEC : Z := PML.PC_SET_EC.

Definition VISS : Z := PMS.PC_VIS_STRING.
Definition VISK : Z := PMS.PC_VIS_KEY.
Definition SCR : Z := CH.hd_scr G.HDECL.
Definition CONSTS : PSK.consts :=
  PSK.CONSTS PML.VT_PARSER PML.VT_FUNC PML.VT_VISITOR 0x10000 0xf8000 0x10000 PML.IMG_RO_HI SCR [(-8, 1%nat); (-16, 8%nat); (-24, 9%nat); (-32, 18%nat); (-40, 19%nat); (-48, 20%nat); (-56, 21%nat)] 56.
Definition X0 : PSK.pexprs := SPT.X0 (ELit 15) (ELit 1).
Lemma kn0_eq : CC.cp_know G.cp0 = SPK.kn CONSTS false Pb Vb Eb (EVar 2) (EVar 33) X0 ++ [KWord (SA Pb 220) 1 TAG; KRange TAG 0 255].
Proof. vmc_refl. Qed.
Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Abbreviation PE := SPT.PE.  Abbreviation CE := SPT.CE.

Definition jof (pc : Z) : nat := match find (fun r : nat * nat * nat * Z => let '(_, _, _, p) := r in Z.eqb p pc) G.RETS with Some (j, _, _, _) => j | None => 0%nat end.
Definition JVAL : nat := Eval vm_compute in jof VALIDATE.
Definition JPAR : nat := Eval vm_compute in jof PARENT.
Definition JPOP : nat := Eval vm_compute in jof POP.

Definition JVK : nat := Eval vm_compute in jof VISK.
Definition JVS : list nat := Eval vm_compute in map (fun r : nat * nat * nat * Z => let '(j, _, _, _) := r in j) (filter (fun r : nat * nat * nat * Z => let '(_, _, _, p) := r in Z.eqb p VISS) G.RETS).
Definition is_jvs (i : nat) : bool := existsb (Nat.eqb i) JVS.
Definition is_err (i : nat) : bool := (negb (Nat.eqb i 0) && negb (Nat.eqb i JVAL) && negb (Nat.eqb i JPAR) && negb (Nat.eqb i JPOP) && negb (Nat.eqb i JVK) && negb (is_jvs i))%bool.

Definition has_gh (i : nat) : bool := (Nat.eqb i JPAR || Nat.eqb i JPOP || Nat.eqb i JVK || is_jvs i)%bool.
Definition ghost_of (j : nat) : expr := EVar (CC.cp_nx (nth j G.CPS G.cp0) - APC.NCS - 1).
Definition GPN : nat := Eval vm_compute in (CC.cp_nx (nth JPAR G.CPS G.cp0) - APC.NCS - 1)%nat.
Definition GP : expr := EVar GPN.

Definition ROT : expr := EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 128) GP) (EAlu Instr.ALU_SRL GP (ELit 1))) (ELit 255).
Definition SEND0 : expr := APC.eadd (EVar 38) (EVar 39).
Definition SENDM1 : expr := APC.eaddz SEND0 (-1).
Definition SCEND0 : expr := APC.eadd (EVar 38) (EVar 40).

Definition view_chk (cells : list kentry) (stv morev sendv : expr) : bool :=
  match SPA.pview_w cells Pb PE CE with
  | Some pv => (expr_eqb (PB4.pv_level pv) (EVar 41) && expr_eqb (PB4.pv_wend pv) (EVar 33) && expr_eqb (PB4.pv_wptr pv) (EVar 32) && expr_eqb (PB4.pv_st pv) stv
                && expr_eqb (PB4.pv_sst pv) (EVar 43) && expr_eqb (PB4.pv_nst pv) (EVar 44) && expr_eqb (PB4.pv_more pv) morev && expr_eqb (PB4.pv_done pv) (EVar 46)
                && expr_eqb (PB4.pv_size pv) (EVar 36) && expr_eqb (PB4.pv_sb pv) (EVar 38) && expr_eqb (PB4.pv_send pv) sendv && expr_eqb (PB4.pv_scend pv) SCEND0)%bool
  | None => false
  end.
Definition nxg (cj : CC.cutpoint) : nat := (CC.cp_nx cj - APC.NCS - 1)%nat.
Definition validate_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (expr_eqb (nth 10 regs (ELit 0)) SX && expr_eqb (nth 11 regs (ELit 0)) LENX && CH2.blocks_eqb BLj BLi)%bool
  then CH2.custom_chk GT.NF G.HDECL 96 1 BLi [] (SSU2.validate_news (nxg cj)) (Some (EVar (nxg cj))) c ps cj BLi
  else None.
Definition parent_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (expr_eqb (nth 10 regs (ELit 0)) Pb && CH2.blocks_eqb BLj BLi && view_chk (SR.ps_cells ps) (ELit 15) (ELit 1) SEND0)%bool
  then CH2.custom_chk GT.NF G.HDECL 48 1 BLi [] [KRange (EVar (nxg cj)) 0 255] (Some (EVar (nxg cj))) c ps cj BLi
  else None.
Definition pop_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (expr_eqb (nth 10 regs (ELit 0)) Pb && CH2.blocks_eqb BLj BLi && view_chk (SR.ps_cells ps) (ELit 15) (ELit 0) SEND0)%bool
  then CH2.custom_chk GT.NF G.HDECL 48 1 BLi [(Pb, 256, ELit 8)] [KWord (SA Pb 256) 8 SENDM1; KRange (EVar (nxg cj)) 0 255] (Some (EVar (nxg cj))) c ps cj BLi
  else None.
Definition CODES : list Z := [25; 26; 27; 28; 29].
Definition setec_chk (code : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (expr_eqb (nth 10 regs (ELit 0)) Eb && expr_eqb (nth 11 regs (ELit 0)) (ELit code) && CH2.blocks_eqb BLj BLi)%bool
  then CH2.custom_chk GT.NF G.HDECL 256 0 BLi ((Eb, 0, ELit 16) :: PSU.statics_wregs) (PSU.setec_news Eb 0 (ELit code)) (Some Eb) c ps cj BLi
  else None.
Definition setec_any (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : bool :=
  existsb (fun code => match setec_chk code c ps cj BLi BLj with Some ci => Nat.leb GT.NF (CH2.ci_nx ci) | None => false end) CODES.
Definition ghost_ok (cj : CC.cutpoint) (o : option CH2.cinfo) : bool := match o with Some ci => (Nat.eqb (CC.cp_nx cj) (CH2.ci_nx ci + 1 + APC.NCS) && Nat.leb GT.NF (CH2.ci_nx ci))%bool | None => false end.

Definition rot_dead (cells : list kentry) : bool := match CX.range3 cells ROT with Some (lo, hi) => forallb (SPW.ne_chk cells ROT lo hi) [0; 4; 7; 8] | None => false end.

Definition SVK : Z := -80.
Definition vis_news (flags : Z) : list kentry := [VSU.fl Vb 0 flags; KWord (SA Vb 32) 8 SX; KWord (SA Vb 40) 8 LENX].
Definition vis_chk (flags : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in let cells := SR.ps_cells ps in
  if (expr_eqb (nth 10 regs (ELit 0)) Vb && expr_eqb (nth 11 regs (ELit 0)) (APC.eaddz (EVar 2) SVK) && CH2.blocks_eqb BLj BLi
      && PB.has cells (KWord (SA Vb 0) 8 (ELit PML.VT_VISITOR)) && PB.has cells (KWord (SA (EVar 2) SVK) 8 SX) && PB.has cells (KWord (SA (EVar 2) (SVK + 8)) 8 LENX))%bool
  then CH2.custom_chk GT.NF G.HDECL PMS.VIS_SCR 0 BLi [(Vb, 8, ELit 40)] (vis_news flags) (Some (ELit 1)) c ps cj BLi
  else None.
Definition vis_ok (flags : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : bool :=
  match vis_chk flags c ps cj BLi BLj with Some ci => Nat.leb (CC.cp_nx c) (CH2.ci_nx ci) | None => false end.

Definition ev_chk (cells : list kentry) (flags : Z) : bool :=
  (PB.has cells (VSU.fl Vb 0 flags) && PB.has cells (KWord (SA Vb 32) 8 SX) && PB.has cells (KWord (SA Vb 40) 8 LENX))%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if (Z.eqb pc VALIDATE || Z.eqb pc PARENT || Z.eqb pc POP || Z.eqb pc SETEC || Z.eqb pc VISS || Z.eqb pc VISK)%bool then
        (Z.eqb (SR.ps_pc ps) pc &&
         match CH2.ret_of G.RETS i k with
         | Some j => match nth_error G.CPS j with
                     | Some cj => let BLi := nth i G.BLS [] in let BLj := nth j G.BLS [] in
                                  if Z.eqb pc VALIDATE then (Nat.eqb i 0 && Nat.eqb j JVAL && ghost_ok cj (validate_chk c ps cj BLi BLj))%bool
                                  else if Z.eqb pc PARENT then (Nat.eqb i JVAL && Nat.eqb j JPAR && ghost_ok cj (parent_chk c ps cj BLi BLj))%bool
                                  else if Z.eqb pc POP then (Nat.eqb i JVK && Nat.eqb j JPOP && ghost_ok cj (pop_chk c ps cj BLi BLj) && match pop_chk c ps cj BLi BLj with Some ci => Nat.ltb GPN (CH2.ci_nx ci) | None => false end)%bool
                                  else if Z.eqb pc VISS then (Nat.eqb i JPAR && is_jvs j && vis_ok 1 c ps cj BLi BLj)%bool
                                  else if Z.eqb pc VISK then (Nat.eqb i JPAR && Nat.eqb j JVK && vis_ok 4097 c ps cj BLi BLj)%bool
                                  else (Nat.eqb i JVAL && is_err j && setec_any c ps cj BLi BLj)%bool
                     | None => false end
         | None => false end)%bool
      else if Z.eqb pc DEADPC then (Nat.eqb i JPAR && rot_dead cells)%bool
      else (PB.exit_base_chk GT.NF RETPC c ps && CH2.blocks_eqb (nth i G.BLS []) SPT.BL0 &&
            if is_err i then (existsb (fun code => PB.has cells (KWord (SA Eb 0) 4 (ELit code))) CODES && PB.has cells (KWord (SA Eb 8) 8 (ELit PML.OBJ_JSON_CATEGORY)) && view_chk cells (ELit 15) (ELit 0) SEND0)
            else (PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) &&
                  if Nat.eqb i JPOP then (view_chk cells (ELit PML.ST_EXPECT_COLON) (ELit 0) SENDM1 && SPW.eq_chk cells ROT 8 && ev_chk cells 4097)
                  else (is_jvs i && ev_chk cells 1 &&
                        ((view_chk cells (ELit PML.ST_ACCEPT) (ELit 0) SEND0 && SPW.eq_chk cells ROT 0)
                         || (view_chk cells (ELit PML.ST_EXPECT_COMMA_OR_END) (ELit 0) SEND0 && (SPW.eq_chk cells ROT 4 || SPW.eq_chk cells ROT 7))))))%bool
  end.
Lemma gpn_ok : CC.cps_all G.CPS (fun i c => (negb (has_gh i) || Nat.ltb GPN (CC.cp_nx c))%bool) = true.
Proof. vmc_refl. Qed.
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
Hypothesis VALIDATE_OK : PMS.validate_spec L.
Hypothesis PARENT_OK : PMS.parent_spec L.
Hypothesis POP_OK : PMS.pop_state_spec L.
Hypothesis SETEC_OK : PMS.set_ec_spec L.
Hypothesis VISS_OK : PMS.visit_string_spec L VISS.
Hypothesis VISK_OK : PMS.visit_key_spec L VISK.
Abbreviation SCRC := PMS.ESV_SCR.

Variables (mw : option (Z * Z)) (LBo : list (Z * Z)) (cr : credit) (sp r P V E B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate).
Variables (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet).
Variables (s len : Z).
Hypothesis HH : hi_heap HI (PML.ps_blocks ps ++ LBo) cr M (m_vmmaps model).
Hypothesis Hmo : PML.model_ok model.
Hypothesis HKnil : K [].
Hypothesis Hfp : PML.fp_ok fx.
Hypothesis Hentry : PML.entry L R M sp r SCRC.
Hypothesis Ha0 : PML.a0 R P.
Hypothesis Ha1 : PML.a1 R s.
Hypothesis Ha2 : PML.a2 R len.
Hypothesis Ha3 : PML.a3 R V.
Hypothesis Ha4 : getr R 14%bv = Z_to_bv 64 E.
Hypothesis Hmore : PML.ps_more ps = true.
Hypothesis Hst : PML.ps_st ps = PML.ST_STRING.
Hypothesis Hlen : 0 <= len < 2 ^ 26.
Hypothesis Htxt : L5.defined M s len.
Hypothesis Hsrg : 4096 <= s /\ s + len <= hl_ceil L.
Hypothesis Htok : PMCUR.txt_ok (PML.ps_win ps) ps s len.
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

Hypothesis Hcont : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range),
   PML.fp_ok fx' ->
   (exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state),
      (PML.parser_at M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) /\ PMCUR.wf_c ps' /\ PML.win_ok M' LBo ps' /\ PML.buf_bound ps' B /\ PML.ec_at M' E code /\
      (code <> 0 -> PML.ps_more ps' = false) /\ PML.ls_ok g' M' /\ (g' = g \/ g' = PML.regJ g /\ code <> 0) /\
      LB' = PML.ps_blocks ps' ++ LBo /\ LBk = LBo /\ W = PMS.W_parc P V E /\ PML.pcredit_x L cr' ps' kx bx /\
      ((code = 0 /\ PML.ps_more ps' = false /\ PML.ps_level ps' = PML.ps_level ps /\ In (PML.ps_st ps') [PML.ST_EXPECT_COLON; PML.ST_EXPECT_COMMA_OR_END; PML.ST_ACCEPT])
       \/ In code [25; 26; 27; 28; 29]) /\ PMCUR.cur_post RSEGS ps ps' code M' V) ->
   regs_preserved R R' -> L5C.hpres L LBk sp SCRC W M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
   srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model') K.

Variables (line0 pos0 tag0 : Z).
Hypothesis Hline0 : PML.u64 M (P + 160) line0.
Hypothesis Hpos0 : PML.u64 M (P + 168) pos0.
Hypothesis Htag0 : PML.u8 M (P + 220) tag0.
Hypothesis Hlpr : 0 <= line0 < 2 ^ 64 /\ 0 <= pos0 < 2 ^ 64 /\ 0 <= tag0 < 256.

Let bcap := PML.ps_bcap ps.
Let bptr := PML.ps_bptr ps.
Let size0 := Z.of_nat (length (PML.ps_buf ps)).
Let sb := PML.ps_sb ps.
Let scap := PML.ps_scap ps.
Let slen := Z.of_nat (length (PML.ps_stack ps)).
Let level := PML.ps_level ps.
Definition XV : list Z := [tag0].
Definition E0 : env := SPT.E0 mw B ps R line0 pos0 XV SPT.noeb.

Lemma SCRV : CH.hd_scr G.HDECL = 512.
Proof. reflexivity. Qed.

Lemma WFM : 0 <= level <= 1024 /\ In scap [66; 132; 264; 528; 1056] /\ 0 <= PML.ps_sst ps <= 11 /\ 0 <= PML.ps_nst ps <= 7 /\ (length (PML.ps_stack ps) <= 1027)%nat /\
  exists C T, PML.ps_stack ps = PML.ST_ROOT :: C ++ T /\ Forall PML.is_container C /\ Z.of_nat (length C) = level /\ (T = [] \/ T = [PML.ST_MEMBER_NAME]).
Proof.
  destruct HWF as (Wn & n' & W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)). cbn [PML.ps_set_nst PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st] in *.
  destruct (W7 Hmore) as (W8 & W9 & W10 & W11 & _). rewrite Hst in W11.
  split; [exact W9|]. split; [exact W4|]. split; [exact W1|]. split; [exact Wn|]. split; [exact W3|]. exists C, T. split; [exact W5|]. split; [exact W6|]. split; [exact W8|].
  unfold PML.transient, PML.comment_or_cr, PML.ST_STRING, PML.ST_CR in W11. destruct W11 as [(HT & _)|[(HT & _)|[(S & _ & _ & X)|(S & _ & _ & X)]]]; [left; exact HT | right; exact HT | lia | lia].
Qed.

Lemma LAST : forall rest x, PML.ps_stack ps = rest ++ [x] ->
  (x = PML.ST_MEMBER_NAME /\ exists C, rest = PML.ST_ROOT :: C /\ Forall PML.is_container C /\ Z.of_nat (length C) = level) \/
  (x = 0 /\ level = 0 /\ exists C, PML.ps_stack ps = PML.ST_ROOT :: C /\ Forall PML.is_container C /\ Z.of_nat (length C) = level) \/
  ((x = 8 \/ x = 14) /\ 1 <= level /\ exists C, PML.ps_stack ps = PML.ST_ROOT :: C /\ Forall PML.is_container C /\ Z.of_nat (length C) = level).
Proof.
  intros rest x Hs. pose proof WFM as (_ & _ & _ & _ & _ & C & T & HSC & HCC & HCL & [->| ->]).
  - rewrite app_nil_r in HSC. destruct (SPT.last_cases C) as [->|(C' & y & ->)].
    + right. left. rewrite HSC in Hs. change [PML.ST_ROOT] with ([] ++ [PML.ST_ROOT]) in Hs. pose proof (SPT.app_last_inj _ _ _ _ Hs) as Q. cbn [length] in HCL.
      split; [unfold PML.ST_ROOT in Q; lia|]. split; [lia|]. exists []. split; [exact HSC|]. split; [constructor | exact HCL].
    + right. right. rewrite HSC in Hs. change (PML.ST_ROOT :: C' ++ [y]) with ((PML.ST_ROOT :: C') ++ [y]) in Hs. pose proof (SPT.app_last_inj _ _ _ _ Hs) as Q. subst y.
      pose proof HCC as HCC'. apply Forall_app in HCC' as [_ HY]. inversion HY as [|y' l' Hy _]; subst. unfold PML.is_container, PML.ST_OBJECT, PML.ST_ARRAY in Hy.
      split; [lia|]. split; [rewrite length_app in HCL; cbn [length] in HCL; lia|]. exists (C' ++ [x]). split; [exact HSC|]. split; [exact HCC | exact HCL].
  - left. rewrite HSC in Hs. change (PML.ST_ROOT :: C ++ [PML.ST_MEMBER_NAME]) with ((PML.ST_ROOT :: C) ++ [PML.ST_MEMBER_NAME]) in Hs.
    pose proof (SPT.app_last_inj _ _ _ _ Hs) as Q. split; [symmetry; exact Q|]. subst x. apply app_inv_tail in Hs. exists C. split; [symmetry; exact Hs|]. split; [exact HCC | exact HCL].
Qed.
Lemma LASTX : exists rest x, PML.ps_stack ps = rest ++ [x] /\ 0 <= x < 256.
Proof.
  pose proof WFM as (_ & _ & _ & _ & _ & C & T & HSC & _). destruct (SPT.last_cases (PML.ps_stack ps)) as [Q|(rest & x & Q)]; [rewrite Q in HSC; discriminate HSC|].
  exists rest, x. split; [exact Q|]. destruct (LAST rest x Q) as [(-> & _)|[(-> & _)|([->| ->] & _)]]; unfold PML.ST_MEMBER_NAME; lia.
Qed.

Lemma INST : SPT.inst L HI mw LBo cr sp r P V E B kx bx g ps R M model SCRC G.HDECL Pb Vb Eb line0 pos0 XV SPT.noeb.
Proof.
  unfold SPT.inst. destruct Hlpr as (Q1 & Q2 & Q3). pose proof WFM as (F1 & _).
  destruct Hentry as (_ & _ & Hsp & _ & Hstk). pose proof (L5C.stk_floor _ _ _ _ Hstk) as FL. pose proof Hstk as (S1 & S2 & S3 & S4 & S5).
  destruct OP as (OP1 & OP2 & OP3), OV as (OV1 & OV2 & OV3), OE as (OE1 & OE2 & OE3).
  assert (HSC : SCRC = 512) by reflexivity.
  split; [exact HIok|]. split; [exact LAY|]. split; [exact HH|]. split; [exact Hentry|]. split; [rewrite SCRV; lia|]. split; [lia|].
  split; [exact HPA|]. split; [exact HWF|]. split; [unfold level in *; lia|].
  split; [destruct HBB as (HB1 & HB2 & HB3); lia|].
  split; [rewrite Hst; unfold PML.ST_STRING; lia|].
  split; [exact HVIS|]. split; [exact HEC|]. split; [exact HLS|]. split; [exact HPC|].
  split; [exact (conj OP1 (conj OP2 OP3))|]. split; [exact (conj OV1 (conj OV2 OV3))|]. split; [exact (conj OE1 (conj OE2 OE3))|]. split; [exact AP1|]. split; [exact AP2|]. split; [exact AP3|].
  split; [exact Hline0|]. split; [exact Hpos0|]. split; [exact Q1|]. split; [exact Q2|].
  split; [unfold PB.uv, Pb; cbn [edenot]; rewrite (SPT.EV0 mw B ps R line0 pos0 XV SPT.noeb 10%bv), Ha0; apply u64_of_Z; lia|].
  split; [unfold PB.uv, Vb; cbn [edenot]; rewrite (SPT.EV0 mw B ps R line0 pos0 XV SPT.noeb 13%bv), Ha3; apply u64_of_Z; lia|].
  split; [unfold PB.uv, Eb; cbn [edenot]; rewrite (SPT.EV0 mw B ps R line0 pos0 XV SPT.noeb 14%bv), Ha4; apply u64_of_Z; lia|].
  split; [reflexivity|]. split; reflexivity.
Qed.
Notation kit X := (X L HI mw LBo cr sp r P V E B kx bx g ps R M model SCRC G.HDECL Pb Vb Eb line0 pos0 XV SPT.noeb INST) (only parsing).

Lemma FRZA : forall E', env_agree GT.NF E0 E' -> uv E' SX = s /\ uv E' LENX = len /\ uv E' TAG = tag0.
Proof.
  intros E' Hag. destruct Hsrg as (R1 & R2). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). unfold hl_ceil in R2. destruct Hlpr as (_ & _ & Q3).
  split; [|split].
  - rewrite (PB.uv_agree GT.NF E0 E' SX Hag eq_refl). unfold PB.uv, SX. cbn [edenot]. unfold E0. rewrite (SPT.EV0 mw B ps R line0 pos0 XV SPT.noeb 11%bv), Ha1. apply u64_of_Z. lia.
  - rewrite (PB.uv_agree GT.NF E0 E' LENX Hag eq_refl). unfold PB.uv, LENX. cbn [edenot]. unfold E0. rewrite (SPT.EV0 mw B ps R line0 pos0 XV SPT.noeb 12%bv), Ha2. apply u64_of_Z. lia.
  - exact (proj1 (SPT.FRZx mw B ps R G.HDECL line0 pos0 XV SPT.noeb E' 0%nat tag0 Hag ltac:(unfold SPT.NF; lia) eq_refl ltac:(lia))).
Qed.

Lemma At0 : CC.At RSEGS G.cp0 E0 R M.
Proof.
  split; [exact (regs_ok_id R _ _)|]. rewrite kn0_eq. unfold know_ok. rewrite Forall_app. split.
  - apply (kit SPT.kn_ok CONSTS (ELit 15) (ELit 1) eq_refl eq_refl eq_refl (conj eq_refl eq_refl) (conj eq_refl eq_refl) eq_refl).
    + rewrite PB2.uv_lit by lia. rewrite Hst. reflexivity.
    + rewrite PB2.uv_lit by lia. rewrite Hmore. reflexivity.
  - destruct (FRZA E0 (CC.env_agree_refl _ _)) as (_ & _ & GT0). destruct Hlpr as (_ & _ & Q3). destruct OP as (OP1 & OP2 & OP3). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
    pose proof (proj1 (proj2 (kit SPT.UU))) as UP. fold E0 in UP.
    constructor; [|constructor; [|constructor]].
    + eapply PB2.kword8_intro with (A := P + 220) (z := tag0); [unfold estart; cbn [a_base a_off]; fold (uv E0 Pb); rewrite UP; reflexivity | lia | lia | exact (PB.edenot_of_uv E0 _ _ GT0) | lia | exact Htag0].
    + cbn [kentry_ok]. fold (uv E0 TAG). rewrite GT0. lia.
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

Definition Cred (i : nat) (E1 : env) (cr1 : credit) : Prop := cr1 = cr.
Lemma CRED_BLK : forall i j E1 E2 cr1, CH2.den E2 (nth j G.BLS []) = CH2.den E1 (nth i G.BLS []) -> Cred i E1 cr1 -> Cred j E2 cr1.
Proof. intros i j E1 E2 cr1 _ H. exact H. Qed.

Definition XLOW (M1 : mem) : Prop := forall a, 0 <= a < hl_ceil L -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Definition XIG (E1 : env) : Prop := exists rest x, PML.ps_stack ps = rest ++ [x] /\ uv E1 GP = x.
Definition XIS (M1 : mem) : Prop := PML.ls_ok (PML.regJ g) M1 /\ L5.bytes_at RSEGS M1 sb (PML.ps_stack ps).
Definition XI (i : nat) (E1 : env) (M1 : mem) : Prop := if is_err i then XIS M1 else (XLOW M1 /\ (has_gh i = true -> XIG E1)).

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
Lemma stack_below : forall (M1 M' : mem), (forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> L5.bytes_at RSEGS M1 sb (PML.ps_stack ps) -> L5.bytes_at RSEGS M' sb (PML.ps_stack ps).
Proof.
  intros M1 M' HLOW HBY. pose proof (kit SPT.NUM) as (BR1 & (B0 & B1 & B2 & B3 & B4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _).
  exact (kit SPT.bytes_below M1 M' sb scap (PML.ps_stack ps) HLOW ltac:(lia) B4 ltac:(unfold slen in N4; lia) HBY).
Qed.

Lemma xlow_ls : forall (M1 : mem), XLOW M1 -> PML.ls_ok g M1.
Proof. intros M1 X. apply (PB2.ls_ok_keep M M1); [|exact HG | exact HLS]. intros a Ha. exact (X a (foot_low a Ha)). Qed.
Lemma xlow_stack : forall (M1 : mem), XLOW M1 -> L5.bytes_at RSEGS M1 sb (PML.ps_stack ps).
Proof. intros M1 X. apply (stack_below M M1 X). exact (SPT.pa_stack _ _ _ HPA). Qed.

Lemma low_frame : forall (M1 M2 : mem) spc scr (Wz : list L5.range), L5.frame_but ((spc - scr, scr) :: Wz) M1 M2 -> hl_ceil L <= spc - scr -> (forall w, In w Wz -> hl_ceil L <= fst w) ->
  forall a, 0 <= a < hl_ceil L -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof.
  intros M1 M2 spc scr Wz HFB Hs HW a Ha. pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). apply HFB. rewrite L5.unsigned_lit by (unfold hl_ceil in *; lia).
  intros rg [<-|Hin]; unfold L5.in_rng; cbn [fst snd]; [lia | specialize (HW _ Hin); lia].
Qed.

Lemma view_gen : forall cells stv morev sendv E' (M' : mem) (more' : bool) (stack' : list Z),
  view_chk cells stv morev sendv = true -> know_ok RSEGS E' M' cells -> env_agree GT.NF E0 E' -> L5.defined M' P 272 ->
  uv E' morev = PML.b2z more' -> L5.bytes_at RSEGS M' sb stack' -> uv E' sendv = sb + Z.of_nat (length stack') -> Z.of_nat (length stack') <= scap ->
  exists buf, PML.parser_at M' P (PML.PS (uv E' stv) (PML.ps_sst ps) (PML.ps_nst ps) more' (PML.ps_done ps) level stack' sb scap bcap bptr buf mw) /\ Z.of_nat (length buf) = size0.
Proof.
  intros cells stv morev sendv E' M' more' stack' HV HK HagE' HdP' Hmo' Hby' Hse Hle.
  unfold view_chk in HV. destruct (SPA.pview_w cells Pb PE CE) as [pv|] eqn:HPV; [|discriminate].
  apply andb_prop in HV as [HV Y12]. apply andb_prop in HV as [HV Y11]. apply andb_prop in HV as [HV Y10]. apply andb_prop in HV as [HV Y9]. apply andb_prop in HV as [HV Y8].
  apply andb_prop in HV as [HV Y7]. apply andb_prop in HV as [HV Y6]. apply andb_prop in HV as [HV Y5]. apply andb_prop in HV as [HV Y4]. apply andb_prop in HV as [HV Y3].
  apply andb_prop in HV as [Y1 Y2]. apply expr_eqb_eq in Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11, Y12.
  destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & G41 & G42 & G43 & G44 & G45 & G46 & G36 & G38 & G39 & G40 & GSE & GSC & GPE & GCE & G32 & G33 & _).
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OP as (OP1 & OP2 & OP3).
  destruct (SPA.parser_view_w E' M' cells Pb PE CE pv P more' (PML.ps_done ps) stack' scap mw HK HPV GP' ltac:(lia) ltac:(lia)) as (buf & HPA' & Hlen' & _).
  - rewrite Y7. exact Hmo'.
  - rewrite Y8, G46. reflexivity.
  - rewrite Y10, G38. exact Hby'.
  - rewrite Y11, Y10, G38. exact Hse.
  - rewrite Y12, Y10. unfold SCEND0. rewrite GSC, G38. reflexivity.
  - exact Hle.
  - rewrite Y3. exact G32.
  - rewrite Y2. exact G33.
  - exact (kit SPT.mw_le).
  - exact HdP'.
  - exists buf. rewrite Y4, Y5, Y6, Y1, Y10, G43, G44, G41, G38, GCE, GPE in HPA'. rewrite Y9, G36 in Hlen'. split; [exact HPA' | exact Hlen'].
Qed.
Lemma stack_exprs : forall E', env_agree GT.NF E0 E' -> uv E' SEND0 = sb + slen /\ uv E' SENDM1 = sb + slen - 1 /\ 1 <= slen <= scap /\ 4096 <= sb /\ sb + scap <= hl_ceil L.
Proof.
  intros E' Hag. destruct (FRZ E' Hag) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G38 & G39 & G40 & GSE & GSC & _).
  pose proof (kit SPT.NUM) as (BR1 & (B0 & B1 & B2 & B3 & B4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  split; [unfold SEND0; exact GSE|]. split; [|split; [fold slen scap in N3, N4; lia | split; [exact B0 | exact B4]]].
  unfold SENDM1. rewrite PB.uv_eaddz. unfold SEND0. rewrite GSE. fold slen in N3. unfold hl_ceil in *. rewrite Z.mod_small by lia. lia.
Qed.
Lemma xi_low : forall i E1 (M1 : mem), is_err i = false -> XI i E1 M1 -> XLOW M1.
Proof. intros i E1 M1 Hi HX. unfold XI in HX. rewrite Hi in HX. exact (proj1 HX). Qed.
Lemma retEx_a1 : forall E' nx ghosts R2, ev (CH2.retEx E' nx ghosts R2) (nx + length ghosts + 5) = getr R2 11%bv.
Proof. intros E' nx ghosts R2. unfold CH2.retEx, CH2.retE. rewrite APS.ext_list_at by (clear; cbn; lia). cbn [APC.caller_saved map nth]. f_equal. Qed.
Lemma reg_arg : forall E' (R' : bvmap 5 word) regs (x : reg) q e z, regs_ok E' regs R' -> q = ridx x -> bv_eqb x 0 = false -> nth q regs (ELit 0) = e -> uv E' e = z -> getr R' x = Z_to_bv 64 z.
Proof.
  intros E' R' regs x q e z HRL -> Hx0 He Hz. rewrite (HRL x). unfold sr_get. rewrite Hx0. rewrite He. rewrite <- Hz. unfold PB.uv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma ghost_at : forall i c E1 E' (M1 : mem), nth_error G.CPS i = Some c -> has_gh i = true -> is_err i = false -> env_agree (CC.cp_nx c) E1 E' -> XI i E1 M1 ->
  exists rest x, PML.ps_stack ps = rest ++ [x] /\ uv E' GP = x.
Proof.
  intros i c E1 E' M1 Hc Hij Hie Hag HX. unfold XI in HX. rewrite Hie in HX. destruct HX as (_ & X). destruct (X Hij) as (rest & x & Hs & Hx). exists rest, x. split; [exact Hs|].
  pose proof (CC.cps_all_sound _ _ gpn_ok i c Hc) as Q. cbv beta in Q. rewrite Hij in Q. cbn [negb orb] in Q.
  rewrite (PB.uv_agree _ E1 E' GP Hag ltac:(unfold GP; cbn [APC.expr_vars_lt]; exact Q)). exact Hx.
Qed.

Lemma leaf_validate : forall c k ps1 j cj ci, is_leaf 0 c k ps1 (CC.TOther VALIDATE) -> CH2.ret_of G.RETS 0 k = Some j -> nth_error G.CPS j = Some cj -> j = JVAL -> SR.ps_pc ps1 = VALIDATE ->
  validate_chk c ps1 cj (nth 0 G.BLS []) (nth j G.BLS []) = Some ci -> CC.cp_nx cj = (CH2.ci_nx ci + 1 + APC.NCS)%nat -> (GT.NF <= CH2.ci_nx ci)%nat ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok 0 c ps1.
Proof.
  intros c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk Hnx Hnf. unfold validate_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb HBL]. apply andb_prop in Hb as [Ha0e Ha1e]. apply expr_eqb_eq in Ha0e, Ha1e.
  assert (Hc : nth_error G.CPS 0 = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  assert (Hnxv : nxg cj = CH2.ci_nx ci) by (unfold nxg; rewrite Hnx; lia).
  rewrite Hnxv in Hchk.
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K XI DEF0 CRED_BLK
           VALIDATE 96 1%nat [] (SSU2.validate_news (CH2.ci_nx ci)) (Some (EVar (CH2.ci_nx ci))) [] 0%nat c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
  - intros w a [].
  - intros E' _ w a [].
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    destruct (FRZA E' HagE') as (GS & GL & _). destruct Hsrg as (R1 & R2).
    assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame 0%nat c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
    pose proof (xlow_tr M1 M' HLOW (xi_low 0%nat E1 M1 eq_refl HX)) as HXL.
    apply (VALIDATE_OK s len (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model1 K Hmh Hml HKnil HFP).
    { split; [exact Hent|]. split; [exact (reg_arg E' R' _ 10%bv 10%nat _ s HRL eq_refl eq_refl Ha0e GS)|]. split; [exact (reg_arg E' R' _ 11%bv 11%nat _ len HRL eq_refl eq_refl Ha1e GL)|].
      split; [lia|]. split; [intros q Hq; rewrite (HXL (s + q) ltac:(lia)); exact (Htxt q Hq)|]. split; [exact (proj1 (xlow_ls M' HXL))|]. split; [exact R1 | exact R2]. }
    intros fx2 R2' M2 HFP2 (q & cc & Hq & Hcc & Hqr & Hcr) HRP HFB HGR.
    set (E2 := CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 q] R2').
    assert (GG : ev E2 (CH2.ci_nx ci) = Z_to_bv 64 q).
    { pose proof (CH2.retEx_ghost E' (CH2.ci_nx ci) [Z_to_bv 64 q] R2' 0 ltac:(cbn; lia)) as GG. rewrite Nat.add_0_r in GG. exact GG. }
    apply (RET fx2 R2' M2 [Z_to_bv 64 q] eq_refl HFP2 HRP HFB HGR).
    + cbn [edenot]. fold E2. rewrite GG. exact Hq.
    + fold E2. intros X [<-|[]]. unfold SSU2.a1var. cbn [kentry_ok edenot]. pose proof (retEx_a1 E' (CH2.ci_nx ci) [Z_to_bv 64 q] R2') as Q. cbn [length] in Q. fold E2 in Q. rewrite Q, Hcc.
      rewrite u64_of_Z by lia. lia.
    + intros _. subst j. unfold XI. change (is_err JVAL) with false. cbv iota. split; [|intros Q; discriminate Q].
      apply (xlow_tr M' M2); [|exact HXL]. destruct Hent as (_ & _ & _ & _ & Hstk'). pose proof (L5C.stk_window _ _ _ _ Hstk') as (SW1 & _).
      apply (low_frame M' M2 (sp + CH2.ci_csp ci) 96 [] HFB ltac:(lia)). intros w [].
Qed.

Lemma leaf_parent : forall c k ps1 j cj ci, is_leaf JVAL c k ps1 (CC.TOther PARENT) -> CH2.ret_of G.RETS JVAL k = Some j -> nth_error G.CPS j = Some cj -> j = JPAR -> SR.ps_pc ps1 = PARENT ->
  parent_chk c ps1 cj (nth JVAL G.BLS []) (nth j G.BLS []) = Some ci -> CC.cp_nx cj = (CH2.ci_nx ci + 1 + APC.NCS)%nat -> (GT.NF <= CH2.ci_nx ci)%nat ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok JVAL c ps1.
Proof.
  intros c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk Hnx Hnf. unfold parent_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb HV]. apply andb_prop in Hb as [Ha0e HBL]. apply expr_eqb_eq in Ha0e.
  assert (Hc : nth_error G.CPS JVAL = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  assert (Hnxv : nxg cj = CH2.ci_nx ci) by (unfold nxg; rewrite Hnx; lia).
  assert (HGP : GP = EVar (CH2.ci_nx ci)).
  { unfold GP. f_equal. rewrite <- Hnxv. unfold nxg. subst j. change cj with (nth JPAR G.CPS G.cp0) || rewrite <- (nth_error_nth _ _ G.cp0 Hcj). reflexivity. }
  rewrite Hnxv in Hchk.
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K XI DEF0 CRED_BLK
           PARENT 48 1%nat [] [KRange (EVar (CH2.ci_nx ci)) 0 255] (Some (EVar (CH2.ci_nx ci))) [] JVAL c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
  - intros w a [].
  - intros E' _ w a [].
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
    pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OP as (OP1 & OP2 & OP3).
    pose proof (SPT.pa_def _ _ _ HPA) as HdefP.
    assert (HdP' : L5.defined M' P 272) by (apply (kit SPT.amb_def GT.NF G.BLS Cred JVAL E1 M' model1 P 272 HA' HdefP); left; lia).
    assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame JVAL c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
    pose proof (xlow_tr M1 M' HLOW (xi_low JVAL E1 M1 eq_refl HX)) as HXL.
    destruct (stack_exprs E' HagE') as (GSE & GSM & NS & B0 & B4).
    destruct (view_gen _ _ _ _ E' M' true (PML.ps_stack ps) HV HK HagE' HdP' ltac:(rewrite PB2.uv_lit by lia; reflexivity) (xlow_stack M' HXL) GSE ltac:(fold slen; lia)) as (buf & HPA' & _).
    destruct (FRZ E' HagE') as (_ & GP' & _).
    destruct LASTX as (rest & x & Hs & Hx0).
    set (psx := PML.PS (uv E' (ELit 15)) (PML.ps_sst ps) (PML.ps_nst ps) true (PML.ps_done ps) level (PML.ps_stack ps) sb scap bcap bptr buf mw) in *.
    apply (PARENT_OK P x (sp + CH2.ci_csp ci) (CC.cp_pc cj) psx rest fx' R' M' model1 K Hmh Hml HKnil HFP).
    { split; [exact Hent|]. split; [exact (reg_arg E' R' _ 10%bv 10%nat _ P HRL eq_refl eq_refl Ha0e GP')|]. split; [exact HPA'|]. unfold psx. cbn [PML.ps_stack PML.ps_sb PML.ps_scap].
      split; [exact Hs|]. split; [unfold PML.obj_on_stack; repeat split; lia|]. split; [lia|]. split; [lia | exact B4]. }
    intros fx2 R2 M2 HFP2 Hpost HRP HFB HGR.
    set (E2 := CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 x] R2).
    assert (GG : ev E2 (CH2.ci_nx ci) = Z_to_bv 64 x).
    { pose proof (CH2.retEx_ghost E' (CH2.ci_nx ci) [Z_to_bv 64 x] R2 0 ltac:(cbn; lia)) as GG. rewrite Nat.add_0_r in GG. exact GG. }
    apply (RET fx2 R2 M2 [Z_to_bv 64 x] eq_refl HFP2 HRP HFB HGR).
    + cbn [edenot]. fold E2. rewrite GG. exact Hpost.
    + fold E2. intros X [<-|[]]. cbn [kentry_ok edenot]. rewrite GG. rewrite u64_of_Z by lia. lia.
    + intros _. subst j. unfold XI. change (is_err JPAR) with false. cbv iota. split.
      * apply (xlow_tr M' M2); [|exact HXL]. destruct Hent as (_ & _ & _ & _ & Hstk'). pose proof (L5C.stk_window _ _ _ _ Hstk') as (SW1 & _).
        apply (low_frame M' M2 (sp + CH2.ci_csp ci) 48 [] HFB ltac:(lia)). intros w [].
      * intros _. exists rest, x. split; [exact Hs|]. rewrite HGP. unfold PB.uv. cbn [edenot]. fold E2. rewrite GG. apply u64_of_Z. lia.
Qed.

Lemma leaf_pop : forall c k ps1 j cj ci, is_leaf JVK c k ps1 (CC.TOther POP) -> CH2.ret_of G.RETS JVK k = Some j -> nth_error G.CPS j = Some cj -> j = JPOP -> SR.ps_pc ps1 = POP ->
  pop_chk c ps1 cj (nth JVK G.BLS []) (nth j G.BLS []) = Some ci -> CC.cp_nx cj = (CH2.ci_nx ci + 1 + APC.NCS)%nat -> (GT.NF <= CH2.ci_nx ci)%nat -> (GPN < CH2.ci_nx ci)%nat ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok JVK c ps1.
Proof.
  intros c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk Hnx Hnf Hgpn. unfold pop_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb HV]. apply andb_prop in Hb as [Ha0e HBL]. apply expr_eqb_eq in Ha0e.
  assert (Hc : nth_error G.CPS JVK = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  assert (Hnxv : nxg cj = CH2.ci_nx ci) by (unfold nxg; rewrite Hnx; lia).
  rewrite Hnxv in Hchk.
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OP as (OP1 & OP2 & OP3).
  assert (ESP : forall Ex, env_agree GT.NF E0 Ex -> forall q, estart Ex (SA Pb q) = P + q).
  { intros Ex Hx q. destruct (FRZ Ex Hx) as (_ & GPx & _). unfold estart. cbn [a_base a_off]. fold (uv Ex Pb). rewrite GPx. reflexivity. }
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K XI DEF0 CRED_BLK
           POP 48 1%nat [(Pb, 256, ELit 8)] [KWord (SA Pb 256) 8 SENDM1; KRange (EVar (CH2.ci_nx ci)) 0 255] (Some (EVar (CH2.ci_nx ci))) [(P + 256, 8)] JVK c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
  - intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (P, 272). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
  - intros E' HagE' w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (Pb, 256, ELit 8). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite (ESP E' HagE' 256). unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
    pose proof (SPT.pa_def _ _ _ HPA) as HdefP.
    assert (HdP' : L5.defined M' P 272) by (apply (kit SPT.amb_def GT.NF G.BLS Cred JVK E1 M' model1 P 272 HA' HdefP); left; lia).
    assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame JVK c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
    pose proof (xlow_tr M1 M' HLOW (xi_low JVK E1 M1 eq_refl HX)) as HXL.
    destruct (ghost_at JVK c E1 E' M1 Hc eq_refl eq_refl Hag HX) as (rest & x & Hs & HGx).
    destruct (stack_exprs E' HagE') as (GSE & GSM & NS & B0 & B4).
    destruct (view_gen _ _ _ _ E' M' false (PML.ps_stack ps) HV HK HagE' HdP' ltac:(rewrite PB2.uv_lit by lia; reflexivity) (xlow_stack M' HXL) GSE ltac:(fold slen; lia)) as (buf & HPA' & _).
    destruct (FRZ E' HagE') as (_ & GP' & _).
    assert (Hx0 : 0 <= x < 256) by (destruct (LAST rest x Hs) as [(-> & _)|[(-> & _)|([->| ->] & _)]]; unfold PML.ST_MEMBER_NAME; lia).
    set (psx := PML.PS (uv E' (ELit 15)) (PML.ps_sst ps) (PML.ps_nst ps) false (PML.ps_done ps) level (PML.ps_stack ps) sb scap bcap bptr buf mw) in *.
    apply (POP_OK P x (sp + CH2.ci_csp ci) (CC.cp_pc cj) psx rest fx' R' M' model1 K Hmh Hml HKnil HFP).
    { split; [exact Hent|]. split; [exact (reg_arg E' R' _ 10%bv 10%nat _ P HRL eq_refl eq_refl Ha0e GP')|]. split; [exact HPA'|]. unfold psx. cbn [PML.ps_stack PML.ps_sb PML.ps_scap].
      split; [exact Hs|]. split; [unfold PML.obj_on_stack; repeat split; lia|]. split; [lia|]. split; [lia | exact B4]. }
    intros fx2 R2 M2 HFP2 (Hpost & Hu) HRP HFB HGR. unfold psx in Hu. cbn [PML.ps_sb] in Hu.
    set (E2 := CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 x] R2).
    assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [apply CH2.retEx_agree | exact Hnf]]).
    assert (GG : ev E2 (CH2.ci_nx ci) = Z_to_bv 64 x).
    { pose proof (CH2.retEx_ghost E' (CH2.ci_nx ci) [Z_to_bv 64 x] R2 0 ltac:(cbn; lia)) as GG. rewrite Nat.add_0_r in GG. exact GG. }
    assert (Hrl : Z.of_nat (length rest) = slen - 1) by (unfold slen; rewrite Hs, length_app; cbn [length]; lia).
    apply (RET fx2 R2 M2 [Z_to_bv 64 x] eq_refl HFP2 HRP HFB HGR).
    + cbn [edenot]. fold E2. rewrite GG. exact Hpost.
    + fold E2. intros X [<-|[<-|[]]].
      * destruct (stack_exprs E2 HagE2) as (_ & GSM2 & _). rewrite LS.
        eapply CL5.kword64_intro with (A := P + 256) (z := sb + slen - 1); [exact (ESP E2 HagE2 256) | lia | lia | exact (PB.edenot_of_uv E2 _ _ GSM2) |].
        rewrite Hrl in Hu. replace (sb + slen - 1) with (sb + (slen - 1)) by lia. exact Hu.
      * cbn [kentry_ok edenot]. rewrite GG. rewrite u64_of_Z by lia. lia.
    + intros _. subst j. unfold XI. change (is_err JPOP) with false. cbv iota. split.
      * apply (xlow_tr M' M2); [|exact HXL]. destruct Hent as (_ & _ & _ & _ & Hstk'). pose proof (L5C.stk_window _ _ _ _ Hstk') as (SW1 & _).
        apply (low_frame M' M2 (sp + CH2.ci_csp ci) 48 [(P + 256, 8)] HFB ltac:(lia)). intros w [<-|[]]. cbn [fst]. lia.
      * intros _. exists rest, x. split; [exact Hs|]. fold E2.
        rewrite (PB.uv_agree (CH2.ci_nx ci) E' E2 GP (CH2.retEx_agree _ _ _ _) ltac:(unfold GP; cbn [APC.expr_vars_lt]; apply Nat.ltb_lt; exact Hgpn)). exact HGx.
Qed.

Lemma leaf_setec : forall c k ps1 j cj code ci, is_leaf JVAL c k ps1 (CC.TOther SETEC) -> CH2.ret_of G.RETS JVAL k = Some j -> nth_error G.CPS j = Some cj -> is_err j = true -> SR.ps_pc ps1 = SETEC ->
  setec_chk code c ps1 cj (nth JVAL G.BLS []) (nth j G.BLS []) = Some ci -> (GT.NF <= CH2.ci_nx ci)%nat -> In code CODES -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok JVAL c ps1.
Proof.
  intros c k ps1 j cj code ci IL Hret Hcj Hj Hpc Hchk Hnx Hcode. unfold setec_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb HBL]. apply andb_prop in Hb as [Ha0e Ha1e]. apply expr_eqb_eq in Ha0e, Ha1e.
  assert (Hc : nth_error G.CPS JVAL = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  assert (Hcr : 25 <= code <= 29) by (unfold CODES in Hcode; cbn [In] in Hcode; lia).
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OE as (OE1 & OE2 & OE3).
  assert (ESE : forall Ex, env_agree GT.NF E0 Ex -> forall q, estart Ex (SA Eb q) = E + q).
  { intros Ex Hx q. destruct (FRZ Ex Hx) as (_ & _ & GE & _). unfold estart. cbn [a_base a_off]. fold (uv Ex Eb). rewrite GE. reflexivity. }
  assert (ESL : forall Ex z, 0 <= z < 2 ^ 63 -> estart Ex (SA (ELit 0) z) = z) by (intros Ex z Hz; unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; lia).
  assert (ELN : forall Ex z, 0 <= z < 2 ^ 64 -> elenZ Ex (ELit z) = z) by (intros Ex z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K XI DEF0 CRED_BLK
           SETEC 256 0%nat ((Eb, 0, ELit 16) :: PSU.statics_wregs) (PSU.setec_news Eb 0 (ELit code)) (Some Eb) [(E, 16); (0xd4df8, 2); (0xf6848, 544)] JVAL c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
  - intros w a Hw Hin. exists w. split; [|exact Hin]. unfold W, PMS.W_parc, PML.W_par. cbn [In app] in Hw |- *. tauto.
  - intros E' HagE' w a Hw Hin. unfold L5.in_rng in Hin. destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hin.
    + exists (Eb, 0, ELit 16). split; [left; reflexivity|]. unfold CH2.in_reg. rewrite (ESE E' HagE' 0), (ELN E' 16 ltac:(lia)). lia.
    + exists (ELit 0, 0xd4df8, ELit 2). split; [right; left; reflexivity|]. unfold CH2.in_reg. rewrite (ESL E' 0xd4df8 ltac:(lia)), (ELN E' 2 ltac:(lia)). lia.
    + exists (ELit 0, 0xf6848, ELit 544). split; [right; right; left; reflexivity|]. unfold CH2.in_reg. rewrite (ESL E' 0xf6848 ltac:(lia)), (ELN E' 544 ltac:(lia)). lia.
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    pose proof (kit SPT.NUM) as (BR1 & (B0 & B1 & B2 & B3 & B4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _).
    destruct (FRZ E' HagE') as (G2 & GP' & GE & _). destruct HEC as (_ & HEd & _).
    assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame JVAL c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
    pose proof (xlow_tr M1 M' HLOW (xi_low JVAL E1 M1 eq_refl HX)) as HXL.
    assert (HdE' : L5.defined M' E 16) by (apply (kit SPT.amb_def GT.NF G.BLS Cred JVAL E1 M' model1 E 16 HA' HEd); left; lia).
    apply (SETEC_OK E code (sp + CH2.ci_csp ci) (CC.cp_pc cj) g fx' R' M' model1 K Hmh Hml HKnil HFP).
    { split; [exact Hent|]. split; [exact (reg_arg E' R' _ 10%bv 10%nat _ E HRL eq_refl eq_refl Ha0e GE)|].
      split; [exact (reg_arg E' R' _ 11%bv 11%nat _ code HRL eq_refl eq_refl Ha1e (PB2.uv_lit E' code ltac:(lia)))|].
      split; [lia|]. split; [exact HdE'|]. split; [unfold PML.obj_on_stack; lia|]. split; [exact (xlow_ls M' HXL) | exact HG]. }
    intros fx2 R2 M2 HFP2 (Hec & Hls2 & Ha0') HRP HFB HGR.
    set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
    assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [apply CH2.retEx_agree | exact Hnx]]).
    apply (RET fx2 R2 M2 [] eq_refl HFP2 HRP HFB HGR).
    + fold E2. destruct (FRZ E2 HagE2) as (_ & _ & GE2 & _). rewrite Ha0'. rewrite <- (Z_to_bv_bv_unsigned _ (edenot E2 Eb)). fold (uv E2 Eb). rewrite GE2. reflexivity.
    + fold E2. intros X HXin. destruct Hec as (Hu32 & _ & Hcat). rewrite LS. destruct HXin as [<-|[<-|[]]].
      * eapply PB.kword32_intro with (A := E) (z := code); [rewrite (ESE E2 HagE2 0); lia | lia | lia | reflexivity | exact Hu32].
      * destruct Hcat as [Hz|[_ Hcat]]; [lia|].
        eapply CL5.kword64_intro with (A := E + 8) (z := PML.OBJ_JSON_CATEGORY); [exact (ESE E2 HagE2 8) | lia | lia | reflexivity | exact Hcat].
    + intros _. unfold XI. rewrite Hj. split; [exact Hls2|].
      apply (PB2.bytes_fr _ M' M2 HFB); [|exact (xlow_stack M' HXL)].
      destruct Hent as (_ & _ & _ & _ & Hstk'). pose proof (L5C.stk_window _ _ _ _ Hstk') as (SW1 & _).
      rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in B1.
      split; [lia|]. split; [unfold hl_ceil in *; lia|]. intros q Hq w Hw. unfold L5.in_rng. fold slen scap in N4. unfold hl_ceil in *.
      destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PMS.SETEC_SCR; lia.
Qed.

Lemma u64_transfer : forall (M1 M2 : mem) a b p q, L5.u64_at RSEGS M1 a p -> L5.u64_at RSEGS M1 a q -> L5.u64_at RSEGS M2 b p -> L5.u64_at RSEGS M2 b q.
Proof. unfold L5.u64_at. intros M1 M2 a b p q H1 H2 H3. rewrite H1 in H2. rewrite H3. exact H2. Qed.
Lemma z2bv_add : forall a b k, Z_to_bv 64 a = Z_to_bv 64 b -> Z_to_bv 64 (a + k) = Z_to_bv 64 (b + k).
Proof.
  intros a b k H. apply bv_eq. rewrite !Z_to_bv_unsigned. apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H.
  rewrite <- (bv_wrap_add_idemp_l 64 a k), H, bv_wrap_add_idemp_l. reflexivity.
Qed.
Lemma gpn_lt : forall i c, nth_error G.CPS i = Some c -> has_gh i = true -> (GPN < CC.cp_nx c)%nat.
Proof. intros i c Hc Hi. pose proof (CC.cps_all_sound _ _ gpn_ok i c Hc) as Q. cbv beta in Q. rewrite Hi in Q. cbn [negb orb] in Q. apply Nat.ltb_lt. exact Q. Qed.
Lemma has_gh_jvs : forall i, is_jvs i = true -> has_gh i = true.
Proof. intros i H. unfold has_gh. rewrite H. rewrite !orb_true_r. reflexivity. Qed.
Lemma jvs_not_err : forall i, is_jvs i = true -> is_err i = false.
Proof. intros i H. unfold is_err. rewrite H. cbn [negb]. rewrite andb_false_r. reflexivity. Qed.
Lemma vis_evs : forall (M2 : mem) p n, PMCUR.ev_at RSEGS M2 V (PMCUR.EvStr p n) -> L5.u64_at RSEGS M2 (V + 8) 1 /\ L5.u64_at RSEGS M2 (V + 32) p /\ L5.u64_at RSEGS M2 (V + 40) n.
Proof. intros M2 p n (_ & H). exact H. Qed.
Lemma vis_evk : forall (M2 : mem) p n, PMCUR.ev_at RSEGS M2 V (PMCUR.EvKey p n) -> L5.u64_at RSEGS M2 (V + 8) 4097 /\ L5.u64_at RSEGS M2 (V + 32) p /\ L5.u64_at RSEGS M2 (V + 40) n.
Proof. intros M2 p n (_ & H). exact H. Qed.
Lemma leaf_vis : forall (vpc flags : Z) (mk : Z -> Z -> PMCUR.sevent), PMS.visit_text_spec L vpc mk ->
  (forall (M2 : mem) p n, PMCUR.ev_at RSEGS M2 V (mk p n) -> L5.u64_at RSEGS M2 (V + 8) flags /\ L5.u64_at RSEGS M2 (V + 32) p /\ L5.u64_at RSEGS M2 (V + 40) n) ->
  forall c k ps1 j cj ci, is_leaf JPAR c k ps1 (CC.TOther vpc) -> CH2.ret_of G.RETS JPAR k = Some j -> nth_error G.CPS j = Some cj -> has_gh j = true -> is_err j = false ->
  SR.ps_pc ps1 = vpc -> vis_chk flags c ps1 cj (nth JPAR G.BLS []) (nth j G.BLS []) = Some ci -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok JPAR c ps1.
Proof.
  intros vpc flags mk VIS_OK HMK c k ps1 j cj ci IL Hret Hcj Hgh Hie Hpc Hchk Hnx. unfold vis_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb Hsl]. apply andb_prop in Hb as [Hb Hsd]. apply andb_prop in Hb as [Hb Hvt]. apply andb_prop in Hb as [Hb HBL].
  apply andb_prop in Hb as [Ha0e Ha1e]. apply expr_eqb_eq in Ha0e, Ha1e.
  assert (Hc : nth_error G.CPS JPAR = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  pose proof (gpn_lt JPAR c Hc eq_refl) as Hgp.
  assert (Hc' : c = nth JPAR G.CPS G.cp0) by exact (eq_sym (nth_error_nth _ _ G.cp0 Hc)).
  assert (HNF : (GT.NF <= CC.cp_nx c)%nat) by (rewrite Hc'; vm_compute; lia).
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OV as (OV1 & OV2 & OV3).
  assert (ESV : forall Ex, env_agree GT.NF E0 Ex -> forall q, estart Ex (SA Vb q) = V + q).
  { intros Ex Hx q. destruct (FRZ Ex Hx) as (_ & _ & _ & GV & _). unfold estart. cbn [a_base a_off]. fold (uv Ex Vb). rewrite GV. reflexivity. }
  assert (ESS : forall Ex, env_agree GT.NF E0 Ex -> forall q, estart Ex (SA (EVar 2) q) = sp + q).
  { intros Ex Hx q. destruct (FRZ Ex Hx) as (G2x & _). unfold estart. cbn [a_base a_off]. fold (uv Ex (EVar 2)). rewrite G2x. reflexivity. }
  assert (ELN : forall Ex z, 0 <= z < 2 ^ 64 -> elenZ Ex (ELit z) = z) by (intros Ex z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K XI DEF0 CRED_BLK
           vpc PMS.VIS_SCR 0%nat [(Vb, 8, ELit 40)] (vis_news flags) (Some (ELit 1)) [(V + 8, 40)] JPAR c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
  - intros w a [<-|[]] Hin. exists (V + 8, 40). split; [unfold W, PMS.W_parc, PML.W_par; cbn [app]; right; right; right; right; left; reflexivity | exact Hin].
  - intros E' HagE' w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (Vb, 8, ELit 40). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite (ESV E' HagE' 8), (ELN E' 40 ltac:(lia)). lia.
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
    destruct (FRZ E' HagE') as (G2 & GP' & GE & GV & _). destruct (FRZA E' HagE') as (GS & GL & _).
    assert (Ra0 : PML.a0 R' V).
    { unfold PML.a0. rewrite (HRL 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Ha0e.
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' Vb)). fold (uv E' Vb). rewrite GV. reflexivity. }
    assert (Hsv : uv E' (APC.eaddz (EVar 2) SVK) = sp + SVK).
    { rewrite PB.uv_eaddz. rewrite G2. unfold SVK in *. rewrite Z.mod_small by lia. reflexivity. }
    pose proof (reg_arg E' R' _ 11%bv 11%nat _ (sp + SVK) HRL eq_refl eq_refl Ha1e Hsv) as Ra1.
    assert (HSD : L5.u64_at RSEGS M' (sp + SVK) s).
    { pose proof (PB2.kword64_elim E' M' _ _ (sp + SVK) (PB.has_ok E' M' _ _ HK Hsd) (ESS E' HagE' SVK)) as T. rewrite GS in T. exact T. }
    assert (HSL : L5.u64_at RSEGS M' (sp + SVK + 8) len).
    { assert (Q : estart E' (SA (EVar 2) (SVK + 8)) = sp + SVK + 8) by (rewrite (ESS E' HagE'); lia).
      pose proof (PB2.kword64_elim E' M' _ _ (sp + SVK + 8) (PB.has_ok E' M' _ _ HK Hsl) Q) as T. rewrite GL in T. exact T. }
    assert (HVT : PML.u64 M' V PML.VT_VISITOR).
    { pose proof (PB2.kword64_elim E' M' _ _ V (PB.has_ok E' M' _ _ HK Hvt)) as T. rewrite PB2.uv_lit in T by (unfold PML.VT_VISITOR; lia). apply T. rewrite (ESV E' HagE' 0). lia. }
    assert (HdV' : L5.defined M' V 48) by (apply (kit SPT.amb_def GT.NF G.BLS Cred JPAR E1 M' model1 V 48 HA' (proj2 HVIS)); left; lia).
    assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame JPAR c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
    destruct (ghost_at JPAR c E1 E' M1 Hc eq_refl eq_refl Hag HX) as (rest & x & Hs & HGx).
    apply (VIS_OK V (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model1 K Hmh Hml HKnil HFP).
    { split; [exact Hent|]. split; [exact Ra0|]. split; [split; [exact HVT | exact HdV']|]. split; [unfold PML.obj_on_stack; repeat split; lia|].
      exists (sp + SVK), s, len. split; [exact Ra1|]. split; [exact HSD|]. split; [exact HSL|]. unfold SVK. lia. }
    intros fx2 R2 M2 HFP2 (Ha0' & e & (sv & p & n & Hsv1 & Hp & Hn & ->) & Hev) HRP HFB HGR.
    assert (Wsv : Z_to_bv 64 sv = Z_to_bv 64 (sp + SVK)) by (unfold PML.a1 in Hsv1; rewrite <- Hsv1; exact Ra1).
    assert (Hp' : L5.u64_at RSEGS M' (sp + SVK) p) by (unfold PML.u64, L5.u64_at in Hp |- *; rewrite <- Wsv; exact Hp).
    assert (Hn' : L5.u64_at RSEGS M' (sp + SVK + 8) n) by (unfold PML.u64, L5.u64_at in Hn |- *; rewrite <- (z2bv_add sv (sp + SVK) 8 Wsv); exact Hn).
    destruct (HMK M2 p n Hev) as (H8 & H32 & H40).
    pose proof (u64_transfer M' M2 _ _ p s Hp' HSD H32) as H32s. pose proof (u64_transfer M' M2 _ _ n len Hn' HSL H40) as H40s.
    set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
    assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [apply CH2.retEx_agree | lia]]).
    assert (HLOW2 : forall a, 0 <= a < hl_ceil L -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
    { destruct Hent as (_ & _ & _ & _ & Hstk'). pose proof (L5C.stk_window _ _ _ _ Hstk') as (SW1 & _).
      intros a Ha. apply HFB. rewrite L5.unsigned_lit by (unfold hl_ceil in *; lia). intros rg [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; unfold hl_ceil, PMS.VIS_SCR in *; lia. }
    apply (RET fx2 R2 M2 [] eq_refl HFP2 HRP HFB HGR).
    + cbn [edenot]. unfold PML.a0 in Ha0'. exact Ha0'.
    + intros X HXin. destruct (FRZA E2 HagE2) as (GS2 & GL2 & _). rewrite LS. unfold vis_news, VSU.fl in HXin. destruct HXin as [<-|[<-|[<-|[]]]].
      * eapply CL5.kword64_intro with (A := V + 8) (z := flags); [rewrite (ESV E2 HagE2); lia | lia | lia | reflexivity | exact H8].
      * eapply CL5.kword64_intro with (A := V + 32) (z := s); [rewrite (ESV E2 HagE2); lia | lia | lia | exact (PB.edenot_of_uv E2 _ _ GS2) | exact H32s].
      * eapply CL5.kword64_intro with (A := V + 40) (z := len); [rewrite (ESV E2 HagE2); lia | lia | lia | exact (PB.edenot_of_uv E2 _ _ GL2) | exact H40s].
    + intros _. unfold XI. rewrite Hie. cbv iota. unfold XI in HX. change (is_err JPAR) with false in HX. cbv iota in HX. destruct HX as (HXL & _). split.
      * intros a Ha. rewrite (HLOW2 a Ha), (HLOW a Ha). exact (HXL a Ha).
      * intros _. exists rest, x. split; [exact Hs|]. fold E2.
        rewrite (PB.uv_agree (CH2.ci_nx ci) E' E2 GP (CH2.retEx_agree _ _ _ _) ltac:(unfold GP; cbn [APC.expr_vars_lt]; apply Nat.ltb_lt; lia)). exact HGx.
Qed.

Lemma rot_val : forall E' x, uv E' GP = x -> In x [0; 8; 14; 16] -> uv E' ROT = (if Z.eqb x 0 then 0 else if Z.eqb x 8 then 4 else if Z.eqb x 14 then 7 else 8).
Proof.
  intros E' x Hx Hin. assert (Hg : ev E' GPN = Z_to_bv 64 x) by (rewrite <- Hx; unfold PB.uv, GP; cbn [edenot]; symmetry; apply Z_to_bv_bv_unsigned).
  unfold PB.uv, ROT, GP. cbn [edenot]. rewrite Hg. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; reflexivity.
Qed.
Lemma last_in : forall rest x, PML.ps_stack ps = rest ++ [x] -> In x [0; 8; 14; 16].
Proof. intros rest x Hs. destruct (LAST rest x Hs) as [(-> & _)|[(-> & _)|([->| ->] & _)]]; unfold PML.ST_MEMBER_NAME; cbn [In]; tauto. Qed.
Lemma leaf_dead : forall c k ps1, is_leaf JPAR c k ps1 (CC.TOther DEADPC) -> rot_dead (SR.ps_cells ps1) = true -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok JPAR c ps1.
Proof.
  intros c k ps1 IL HD fx' E1 R1 M1 model1 E' R' M' HAt [HAmb HX] HFP Hag HLF _. exfalso.
  assert (Hc : nth_error G.CPS JPAR = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct (ghost_at JPAR c E1 E' M1 Hc eq_refl eq_refl Hag HX) as (rest & x & Hs & Hx).
  pose proof (last_in rest x Hs) as Hin. pose proof (rot_val E' x Hx Hin) as HR.
  unfold rot_dead in HD. destruct (CX.range3 (SR.ps_cells ps1) ROT) as [[lo hi]|] eqn:Hr; [|discriminate]. rewrite forallb_forall in HD.
  pose proof (CX.range3_sound RSEGS E' M' _ _ _ _ HK Hr) as Hrg. fold (uv E' ROT) in Hrg.
  assert (NE : forall cst, In cst [0; 4; 7; 8] -> uv E' ROT <> cst) by (intros cst Hc4; apply (SPW.ne_chk_sound E' M' _ ROT lo hi cst HK (HD _ Hc4) Hrg); cbn [In] in Hc4; lia).
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [Z.eqb Pos.eqb] in HR; [apply (NE 0) | apply (NE 4) | apply (NE 7) | apply (NE 8)]; cbn [In]; tauto || exact HR.
Qed.

Lemma exit_gen : forall i c k ps1 pc stv morev sendv,
  is_leaf i c k ps1 (CC.TOther pc) -> PB.exit_base_chk GT.NF RETPC c ps1 = true -> CH2.blocks_eqb (nth i G.BLS []) SPT.BL0 = true -> view_chk (SR.ps_cells ps1) stv morev sendv = true ->
  (forall E1 E' R' (M1 M' : mem) model1, env_agree (CC.cp_nx c) E1 E' -> CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' -> XI i E1 M1 -> HAMB i E1 M' model1 -> env_agree GT.NF E0 E' ->
      L5.defined M' E 16 -> (forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      exists (more' : bool) (stack' : list Z) (code : Z) (g' : PML.ls_state),
        uv E' morev = PML.b2z more' /\ L5.bytes_at RSEGS M' sb stack' /\ uv E' sendv = sb + Z.of_nat (length stack') /\ Z.of_nat (length stack') <= scap /\
        PML.ec_at M' E code /\ (code <> 0 -> more' = false) /\ PML.ls_ok g' M' /\ (g' = g \/ g' = PML.regJ g /\ code <> 0) /\
        forall buf, Z.of_nat (length buf) = size0 -> let ps' := PML.PS (uv E' stv) (PML.ps_sst ps) (PML.ps_nst ps) more' (PML.ps_done ps) level stack' sb scap bcap bptr buf (PML.ps_win ps) in
          PMCUR.wf_c ps' /\ PML.buf_need ps' = 0 /\
          ((code = 0 /\ more' = false /\ In (uv E' stv) [PML.ST_EXPECT_COLON; PML.ST_EXPECT_COMMA_OR_END; PML.ST_ACCEPT]) \/ In code [25; 26; 27; 28; 29]) /\
          PMCUR.cur_post RSEGS ps ps' code M' V) ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc stv morev sendv IL Hbase HBL HV HKIND fx' E1 R1 M1 model1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct Hentry as (Hra & Hraok & _).
  assert (HSC : SCRC = 512) by reflexivity.
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  apply (PB.exit_ret L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K XI DEF0 (fun _ => 0) (fun _ => 0) SCRC
           ltac:(rewrite SCRV; lia) ltac:(lia) S5 R (SPT.EV0 mw B ps R line0 pos0 XV SPT.noeb) r Hra Hraok heap_ok3 RETPC i c k ps1 _ ret_at IL Hbase fx' E1 R1 M1 model1 E' R' M' HAt HAmb Hag HLF).
  intros HRP HP HA' HagE'.
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct OP as (OP1 & OP2 & OP3), OE as (OE1 & OE2 & OE3).
  pose proof (SPT.pa_def _ _ _ HPA) as HdefP. destruct HEC as (_ & HEd & _).
  assert (HdP' : L5.defined M' P 272) by (apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 P 272 HA' HdefP); left; lia).
  assert (HdE' : L5.defined M' E 16) by (apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 E 16 HA' HEd); left; lia).
  assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (apply (below_frame i c E' M1 M' Hc HagE'); exact (CC.lf_frame _ _ _ _ _ _ _ HLF)).
  destruct (HKIND E1 E' R' M1 M' model1 Hag HLF HX HA' HagE' HdE' HLOW) as (more' & stack' & code & g' & Hmo' & Hby' & Hse & Hle & Hec' & Hcm & Hls' & Hg' & HPS).
  destruct (view_gen _ _ _ _ E' M' more' stack' HV HK HagE' HdP' Hmo' Hby' Hse Hle) as (buf & HPA' & Hlen').
  set (ps' := PML.PS (uv E' stv) (PML.ps_sst ps) (PML.ps_nst ps) more' (PML.ps_done ps) level stack' sb scap bcap bptr buf (PML.ps_win ps)) in *.
  destruct (HPS buf Hlen') as (Hwf' & Hneed' & HREL & HCUR). fold ps' in Hwf', Hneed', HREL, HCUR.
  assert (Hden' : CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps') by (rewrite (CH2.blocks_eqb_eq _ _ HBL), (kit SPT.den_BL0 E1 (amb_agree _ _ _ _ HA')); reflexivity).
  pose proof HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr & Hdf). unfold Cred in HC1. subst cr1.
  unfold CH2.cur in HH1. rewrite Hden' in HH1.
  apply (Hcont fx' R' M' model1 (PML.ps_blocks ps' ++ LBo) cr LBo W HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH1].
  exists ps', code, g'.
  split; [split; [exact HPA' | reflexivity]|]. split; [exact Hwf'|].
  split; [apply (SPT.win_ok_tr M M' LBo ps ps' eq_refl HWIN); intros ch p n Hch C1 C2 Hwd;
          apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 p n HA' Hwd); right; exists ch; split; [exact Hch | lia]|].
  split; [destruct HBB as (HB1 & HB2 & HB3); unfold PML.buf_bound; rewrite Hneed'; unfold PML.winlen in *; unfold ps'; cbn [PML.ps_win PML.ps_buf]; fold size0 in HB1; rewrite Hlen'; split; [lia | exact HB2]|].
  split; [exact Hec'|]. split; [intros Q; exact (Hcm Q)|]. split; [exact Hls'|]. split; [exact Hg'|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HPC|].
  split; [|exact HCUR].
  destruct HREL as [(Q1 & Q2 & Q3)|Q]; [left | right; exact Q]. split; [exact Q1|]. split; [unfold ps'; cbn [PML.ps_more]; exact Q2|]. split; [reflexivity | exact Q3].
Qed.

Lemma ecell : forall E' (M' : mem) cells, know_ok RSEGS E' M' cells -> env_agree GT.NF E0 E' -> PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) = true -> L5.defined M' E 16 -> PML.ec_at M' E 0.
Proof.
  intros E' M' cells HK Hag Y1 HdE'. destruct (FRZ E' Hag) as (_ & _ & GE & _). destruct OE as (OE1 & OE2 & OE3). pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & _).
  split; [|split; [exact HdE' | left; reflexivity]].
  pose proof (PB2.kword32_elim E' M' _ _ E (PB.has_ok E' M' _ _ HK Y1)) as T. rewrite PB2.uv_lit in T by lia. apply T. unfold estart. cbn [a_base a_off]. fold (uv E' Eb). rewrite GE. lia.
Qed.

Lemma wf_exit : forall stz buf stack' C, stack' = PML.ST_ROOT :: C -> Forall PML.is_container C -> Z.of_nat (length C) = level -> (length stack' <= 1027)%nat ->
  In stz [PML.ST_EXPECT_COLON; PML.ST_EXPECT_COMMA_OR_END; PML.ST_ACCEPT] -> (stz = PML.ST_EXPECT_COMMA_OR_END -> 1 <= level) ->
  PML.wf_ps (PML.PS stz (PML.ps_sst ps) (PML.ps_nst ps) true (PML.ps_done ps) level stack' sb scap bcap bptr buf (PML.ps_win ps)).
Proof.
  intros stz buf stack' C HSC HCC HCL Hl Hin Hlv. pose proof WFM as (F1 & F2 & F3 & F4 & _).
  unfold PML.wf_ps. cbn [PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st PML.ps_buf].
  split; [exact F3|]. split; [exact F4|]. split; [exact Hl|]. split; [exact F2|]. exists C, []. rewrite app_nil_r. split; [exact HSC|]. split; [exact HCC|]. intros _.
  split; [exact HCL|]. split; [exact F1|].
  unfold PML.handled, PML.transient, PML.comment_or_cr, PML.ST_EXPECT_COLON, PML.ST_EXPECT_COMMA_OR_END, PML.ST_ACCEPT, PML.ST_CR, PML.ST_NUMBER in *. cbn [In] in Hin.
  split; [lia|]. split; [left; split; [reflexivity | lia]|]. split; [intros [Q|[]]; exact (Hlv Q) | intros Q; lia].
Qed.

Lemma leaf_exit_err : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> is_err i = true -> PB.exit_base_chk GT.NF RETPC c ps1 = true -> CH2.blocks_eqb (nth i G.BLS []) SPT.BL0 = true ->
  existsb (fun code => PB.has (SR.ps_cells ps1) (KWord (SA Eb 0) 4 (ELit code))) CODES = true -> PB.has (SR.ps_cells ps1) (KWord (SA Eb 8) 8 (ELit PML.OBJ_JSON_CATEGORY)) = true ->
  view_chk (SR.ps_cells ps1) (ELit 15) (ELit 0) SEND0 = true -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc IL Hi Hbase HBL Hcodes Hec8 HV. apply (exit_gen i c k ps1 pc _ _ _ IL Hbase HBL HV).
  intros E1 E' R' M1 M' model1 Hag HLF HX HA' HagE' HdE' HLOW.
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  apply existsb_exists in Hcodes as (code & Hcin & Hec0). assert (Hcr : 25 <= code <= 29) by (unfold CODES in Hcin; cbn [In] in Hcin; lia).
  unfold XI in HX. rewrite Hi in HX. destruct HX as (HLS2 & HBY).
  destruct (FRZ E' HagE') as (_ & _ & GE & _). destruct (stack_exprs E' HagE') as (GSE & GSM & NS & B0 & B4).
  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct OE as (OE1 & OE2 & OE3).
  assert (ES : forall q, estart E' (SA Eb q) = E + q) by (intros q; unfold estart; cbn [a_base a_off]; fold (uv E' Eb); rewrite GE; reflexivity).
  exists false, (PML.ps_stack ps), code, (PML.regJ g).
  split; [rewrite PB2.uv_lit by lia; reflexivity|]. split; [exact (stack_below M1 M' HLOW HBY)|]. split; [exact GSE|]. split; [fold slen; lia|].
  split.
  { split; [|split; [exact HdE' | right; split; [lia|]]].
    - pose proof (PB2.kword32_elim E' M' _ _ E (PB.has_ok E' M' _ _ HK Hec0)) as T. rewrite PB2.uv_lit in T by lia. apply T. rewrite ES. lia.
    - pose proof (PB2.kword64_elim E' M' _ _ (E + 8) (PB.has_ok E' M' _ _ HK Hec8)) as T. rewrite PB2.uv_lit in T by (unfold PML.OBJ_JSON_CATEGORY; lia). apply T. apply ES. }
  split; [intros _; reflexivity|].
  split; [exact (kit SPT.ls_below M1 M' (PML.regJ g) ltac:(destruct g; discriminate) HLOW HLS2)|].
  split; [right; split; [reflexivity | lia]|].
  intros buf _. cbv zeta.
  split; [split; [|apply SCU.lvl_ok_stop; reflexivity]|].
  { pose proof WFM as (F1 & F2 & F3 & F4 & F5 & C & T & HSC & HCC & _).
    unfold PML.wf_ps. cbn [PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st PML.ps_buf].
    split; [exact F3|]. split; [exact F4|]. split; [exact F5|]. split; [exact F2|]. exists C, T. split; [exact HSC|]. split; [exact HCC|]. intros Q; discriminate Q. }
  split; [reflexivity|]. split; [right; unfold CODES in Hcin; exact Hcin | apply SCU.cur_post_err; lia].
Qed.

Lemma leaf_exit_ok : forall i c k ps1 pc stz sendv rv flags, is_leaf i c k ps1 (CC.TOther pc) -> has_gh i = true -> is_err i = false ->
  PB.exit_base_chk GT.NF RETPC c ps1 = true -> CH2.blocks_eqb (nth i G.BLS []) SPT.BL0 = true ->
  PB.has (SR.ps_cells ps1) (KWord (SA Eb 0) 4 (ELit 0)) = true -> view_chk (SR.ps_cells ps1) (ELit stz) (ELit 0) sendv = true -> SPW.eq_chk (SR.ps_cells ps1) ROT rv = true ->
  ev_chk (SR.ps_cells ps1) flags = true ->
  (stz = PML.ST_EXPECT_COLON /\ sendv = SENDM1 /\ rv = 8 /\ flags = 4097) \/ (sendv = SEND0 /\ flags = 1 /\ ((stz = PML.ST_ACCEPT /\ rv = 0) \/ (stz = PML.ST_EXPECT_COMMA_OR_END /\ (rv = 4 \/ rv = 7)))) ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc stz sendv rv flags IL Hij Hie Hbase HBL Hec HV HROT HEV HCASE. apply (exit_gen i c k ps1 pc _ _ _ IL Hbase HBL HV).
  intros E1 E' R' M1 M' model1 Hag HLF HX HA' HagE' HdE' HLOW.
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  pose proof (xlow_tr M1 M' HLOW (xi_low i E1 M1 Hie HX)) as HXL.
  destruct (ghost_at i c E1 E' M1 Hc Hij Hie Hag HX) as (rest & x & Hs & Hx).
  pose proof (last_in rest x Hs) as Hin. pose proof (rot_val E' x Hx Hin) as HR.
  assert (Hrv : 0 <= rv < 2 ^ 64) by (destruct HCASE as [(_ & _ & -> & _)|(_ & _ & [(_ & ->)|(_ & [->| ->])])]; lia).
  rewrite (SPW.eq_chk_sound E' M' _ ROT rv HK HROT Hrv) in HR.
  destruct (stack_exprs E' HagE') as (GSE & GSM & NS & B0 & B4). pose proof WFM as (F1 & F2 & F3 & F4 & F5 & _).
  assert (Hstz : In stz [PML.ST_EXPECT_COLON; PML.ST_EXPECT_COMMA_OR_END; PML.ST_ACCEPT]) by (destruct HCASE as [(-> & _)|(_ & _ & [(-> & _)|(-> & _)])]; cbn [In]; tauto).
  assert (Hstr : 0 <= stz < 2 ^ 64) by (unfold PML.ST_EXPECT_COLON, PML.ST_EXPECT_COMMA_OR_END, PML.ST_ACCEPT in Hstz; cbn [In] in Hstz; lia).

  pose proof (kit SPT.SPF) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). pose proof OV as (OV1 & OV2 & OV3).
  destruct (FRZ E' HagE') as (_ & _ & _ & GV & _). destruct (FRZA E' HagE') as (GS & GL & _).
  assert (ESV : forall q, estart E' (SA Vb q) = V + q) by (intros q; unfold estart; cbn [a_base a_off]; fold (uv E' Vb); rewrite GV; reflexivity).
  unfold ev_chk in HEV. apply andb_prop in HEV as [HEV Hn]. apply andb_prop in HEV as [Hfl Hp].
  assert (Hfr : 0 <= flags < 2 ^ 64) by (destruct HCASE as [(_ & _ & _ & ->)|(_ & -> & _)]; lia).
  assert (HFL : L5.u64_at RSEGS M' (V + 8) flags).
  { assert (Q : estart E' (SA Vb (0 + 8)) = V + 8) by (rewrite ESV; lia).
    pose proof (PB2.kword64_elim E' M' _ _ (V + 8) (PB.has_ok E' M' _ _ HK Hfl) Q) as T. rewrite PB2.uv_lit in T by exact Hfr. exact T. }
  assert (HPX : L5.u64_at RSEGS M' (V + 32) s).
  { pose proof (PB2.kword64_elim E' M' _ _ (V + 32) (PB.has_ok E' M' _ _ HK Hp) (ESV 32)) as T. rewrite GS in T. exact T. }
  assert (HNX : L5.u64_at RSEGS M' (V + 40) len).
  { pose proof (PB2.kword64_elim E' M' _ _ (V + 40) (PB.has_ok E' M' _ _ HK Hn) (ESV 40)) as T. rewrite GL in T. exact T. }
  assert (HdV' : L5.defined M' (V + 8) 40).
  { apply (kit SPT.amb_def GT.NF G.BLS Cred i E1 M' model1 (V + 8) 40 HA'); [eapply (L5.defined_sub _ _ _ _ _ (proj2 HVIS)); lia | left; lia]. }
  destruct HCASE as [(-> & -> & -> & ->)|(-> & -> & HC2)].
  -
    assert (Hx16 : x = 16) by (destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; vm_compute in HR; first [discriminate HR | reflexivity]).
    destruct (LAST rest x Hs) as [(_ & C & HRC & HCC & HCL)|[(Q & _)|([Q|Q] & _)]]; [|lia|lia|lia].
    assert (Hrl : Z.of_nat (length rest) = slen - 1) by (unfold slen; rewrite Hs, length_app; cbn [length]; lia).
    assert (HL1 : 1 <= level).
    { apply (HLV Hmore). right. exists x. split; [rewrite Hs; apply in_or_app; right; left; reflexivity|].
      rewrite Hx16. unfold PMCUR.ICS. cbn [In]. unfold PML.ST_EXPECT_COMMA_OR_END, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON, PML.ST_EXPECT_VALUE_OR_END, PML.ST_EXPECT_VALUE, PML.ST_MEMBER_NAME. lia. }
    exists false, rest, 0, g.
    split; [rewrite PB2.uv_lit by lia; reflexivity|].
    split; [apply (SPT.bytes_prefix M' sb rest [x]); rewrite <- Hs; exact (xlow_stack M' HXL)|]. split; [rewrite GSM, Hrl; lia|]. split; [lia|].
    split; [exact (ecell E' M' _ HK HagE' Hec HdE')|]. split; [intros Q; exfalso; apply Q; reflexivity|]. split; [exact (xlow_ls M' HXL)|]. split; [left; reflexivity|].
    intros buf Hbl. cbv zeta. rewrite PB2.uv_lit by exact Hstr.
    match goal with |- PMCUR.wf_c ?q /\ _ => set (psq := q) end.
    assert (WT : PML.wf_ps (PMCUR.ps_set_more psq true)).
    { unfold psq. cbn [PMCUR.ps_set_more PML.ps_st PML.ps_sst PML.ps_nst PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win].
      apply (wf_exit _ buf rest C HRC HCC HCL); [apply Nat2Z.inj_le; rewrite Hrl; unfold slen; lia | exact Hstz | unfold PML.ST_EXPECT_COLON, PML.ST_EXPECT_COMMA_OR_END; lia]. }
    assert (LT : PMCUR.lvl_ok (PMCUR.ps_set_more psq true)).
    { apply (SCU.lvl_ok_rootc _ C); [unfold psq; cbn [PMCUR.ps_set_more PML.ps_stack]; exact HRC | exact HCC | intros _ _; unfold psq; cbn [PMCUR.ps_set_more PML.ps_level]; exact HL1]. }
    split; [exact (SCU.wf_c_stop psq eq_refl WT)|].
    split; [reflexivity|].
    split; [left; split; [reflexivity|]; split; [reflexivity | exact Hstz]|].
    apply (SCU.cur_post_event RSEGS ps psq M' V (PMCUR.EvKey s len) eq_refl (conj WT LT)).
    + unfold PMCUR.ev_at. split; [exact HdV'|]. split; [exact HFL|]. split; [exact HPX | exact HNX].
    + unfold PMCUR.ev_rel, psq. cbn [PML.ps_st PML.ps_level]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HL1|].
      destruct Htok as [(Q1 & Q2)|Q]; [left; cbn [PML.ps_bptr PML.ps_buf]; split; [exact Q1 | rewrite Hbl; exact Q2] | right; exact Q].
  -
    assert (HXC : (x = 0 /\ stz = PML.ST_ACCEPT) \/ ((x = 8 \/ x = 14) /\ stz = PML.ST_EXPECT_COMMA_OR_END)).
    { destruct HC2 as [(-> & ->)|(-> & [->| ->])]; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; vm_compute in HR; first [discriminate HR | left; split; reflexivity | right; split; [lia | reflexivity]]. }
    assert (HSTK : exists C, PML.ps_stack ps = PML.ST_ROOT :: C /\ Forall PML.is_container C /\ Z.of_nat (length C) = level /\ (stz = PML.ST_EXPECT_COMMA_OR_END -> 1 <= level)).
    { destruct (LAST rest x Hs) as [(Q & _)|[(Q & QL & C & HSC & HCC & HCL)|(Q & QL & C & HSC & HCC & HCL)]].
      - unfold PML.ST_MEMBER_NAME in Q. lia.
      - exists C. split; [exact HSC|]. split; [exact HCC|]. split; [exact HCL|]. intros Q2. unfold PML.ST_ACCEPT, PML.ST_EXPECT_COMMA_OR_END in *. lia.
      - exists C. split; [exact HSC|]. split; [exact HCC|]. split; [exact HCL|]. intros _. exact QL. }
    destruct HSTK as (C & HSC & HCC & HCL & HLV1).
    exists false, (PML.ps_stack ps), 0, g.
    split; [rewrite PB2.uv_lit by lia; reflexivity|]. split; [exact (xlow_stack M' HXL)|]. split; [exact GSE|]. split; [fold slen; lia|].
    split; [exact (ecell E' M' _ HK HagE' Hec HdE')|]. split; [intros Q; exfalso; apply Q; reflexivity|]. split; [exact (xlow_ls M' HXL)|]. split; [left; reflexivity|].
    intros buf Hbl. cbv zeta. rewrite PB2.uv_lit by exact Hstr.
    match goal with |- PMCUR.wf_c ?q /\ _ => set (psq := q) end.
    assert (WT : PML.wf_ps (PMCUR.ps_set_more psq true)).
    { unfold psq. cbn [PMCUR.ps_set_more PML.ps_st PML.ps_sst PML.ps_nst PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win].
      exact (wf_exit _ buf _ C HSC HCC HCL F5 Hstz HLV1). }
    assert (LT : PMCUR.lvl_ok (PMCUR.ps_set_more psq true)).
    { apply (SCU.lvl_ok_rootc _ C); [unfold psq; cbn [PMCUR.ps_set_more PML.ps_stack]; exact HSC | exact HCC |].
      intros Hin' _. unfold psq in Hin' |- *. cbn [PMCUR.ps_set_more PML.ps_st PML.ps_level] in Hin' |- *.
      destruct HC2 as [(Hz & _)|(Hz & _)]; [exfalso; subst stz; unfold PMCUR.ICS in Hin'; cbn in Hin'; unfold PML.ST_ACCEPT, PML.ST_EXPECT_COMMA_OR_END, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON, PML.ST_EXPECT_VALUE_OR_END, PML.ST_EXPECT_VALUE, PML.ST_MEMBER_NAME in Hin'; lia | exact (HLV1 Hz)]. }
    split; [exact (SCU.wf_c_stop psq eq_refl WT)|].
    split; [unfold PML.buf_need, psq; cbn [PML.ps_more PML.ps_st]; destruct (Z.eqb_spec stz PML.ST_STRING) as [Q|_]; [|reflexivity];
            unfold PML.ST_STRING, PML.ST_EXPECT_COLON, PML.ST_EXPECT_COMMA_OR_END, PML.ST_ACCEPT in *; cbn [In] in Hstz; lia|].
    split; [left; split; [reflexivity|]; split; [reflexivity | exact Hstz]|].
    apply (SCU.cur_post_event RSEGS ps psq M' V (PMCUR.EvStr s len) eq_refl (conj WT LT)).
    + unfold PMCUR.ev_at. split; [exact HdV'|]. split; [exact HFL|]. split; [exact HPX | exact HNX].
    + unfold PMCUR.ev_rel, PMCUR.after_value_st, psq. cbn [PML.ps_st PML.ps_level]. split; [destruct HC2 as [(-> & _)|(-> & _)]; cbn; tauto|]. split; [reflexivity|].
      destruct Htok as [(Q1 & Q2)|Q]; [left; cbn [PML.ps_bptr PML.ps_buf]; split; [exact Q1 | rewrite Hbl; exact Q2] | right; exact Q].
Qed.

Lemma leaves : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. cbn [leaf_chk] in X.
  destruct (Z.eqb pc VALIDATE || Z.eqb pc PARENT || Z.eqb pc POP || Z.eqb pc SETEC || Z.eqb pc VISS || Z.eqb pc VISK)%bool eqn:HPC'.
  - apply andb_prop in X as [Hpc XR]. apply Z.eqb_eq in Hpc.
    destruct (CH2.ret_of G.RETS i k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate]. cbv zeta in XR.
    destruct (Z.eqb_spec pc VALIDATE) as [->|N1]; [|destruct (Z.eqb_spec pc PARENT) as [->|N2]; [|destruct (Z.eqb_spec pc POP) as [->|N3];
      [|destruct (Z.eqb_spec pc VISS) as [->|N4]; [|destruct (Z.eqb_spec pc VISK) as [->|N5]]]]].
    + apply andb_prop in XR as [XR XC]. apply andb_prop in XR as [Hi Hj]. apply Nat.eqb_eq in Hi, Hj. subst i.
      destruct (validate_chk c ps1 cj (nth 0 G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. cbn [ghost_ok] in XC. apply andb_prop in XC as [XC1 XC2]. apply Nat.eqb_eq in XC1. apply Nat.leb_le in XC2.
      exact (leaf_validate c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk XC1 XC2).
    + apply andb_prop in XR as [XR XC]. apply andb_prop in XR as [Hi Hj]. apply Nat.eqb_eq in Hi, Hj. subst i.
      destruct (parent_chk c ps1 cj (nth JVAL G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. cbn [ghost_ok] in XC. apply andb_prop in XC as [XC1 XC2]. apply Nat.eqb_eq in XC1. apply Nat.leb_le in XC2.
      exact (leaf_parent c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk XC1 XC2).
    + apply andb_prop in XR as [XR XG]. apply andb_prop in XR as [XR XC]. apply andb_prop in XR as [Hi Hj]. apply Nat.eqb_eq in Hi, Hj. subst i.
      destruct (pop_chk c ps1 cj (nth JVK G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. cbn [ghost_ok] in XC. apply andb_prop in XC as [XC1 XC2]. apply Nat.eqb_eq in XC1. apply Nat.leb_le in XC2.
      apply Nat.ltb_lt in XG. exact (leaf_pop c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk XC1 XC2 XG).
    + apply andb_prop in XR as [XR XV]. apply andb_prop in XR as [Hi Hj]. apply Nat.eqb_eq in Hi. subst i. unfold vis_ok in XV.
      destruct (vis_chk 1 c ps1 cj (nth JPAR G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. apply Nat.leb_le in XV.
      exact (leaf_vis VISS 1 PMCUR.EvStr VISS_OK vis_evs c k ps1 j cj ci IL Hret Hcj (has_gh_jvs j Hj) (jvs_not_err j Hj) Hpc Hchk XV).
    + apply andb_prop in XR as [XR XV]. apply andb_prop in XR as [Hi Hj]. apply Nat.eqb_eq in Hi, Hj. subst i j. unfold vis_ok in XV.
      destruct (vis_chk 4097 c ps1 cj (nth JPAR G.BLS []) (nth JVK G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. apply Nat.leb_le in XV.
      exact (leaf_vis VISK 4097 PMCUR.EvKey VISK_OK vis_evk c k ps1 JVK cj ci IL Hret Hcj eq_refl eq_refl Hpc Hchk XV).
    + assert (Hs : pc = SETEC) by (destruct (Z.eqb_spec pc SETEC) as [Q|Q]; [exact Q|]; destruct (Z.eqb_spec pc VALIDATE); [contradiction|]; destruct (Z.eqb_spec pc PARENT); [contradiction|];
                                   destruct (Z.eqb_spec pc POP); [contradiction|]; destruct (Z.eqb_spec pc VISS); [contradiction|]; destruct (Z.eqb_spec pc VISK); [contradiction | discriminate HPC']).
      rewrite Hs in IL, Hpc. clear HPC'. apply andb_prop in XR as [XR XC]. apply andb_prop in XR as [Hi Hj]. apply Nat.eqb_eq in Hi. subst i.
      unfold setec_any in XC. apply existsb_exists in XC as (code & Hcin & XC).
      destruct (setec_chk code c ps1 cj (nth JVAL G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. apply Nat.leb_le in XC.
      exact (leaf_setec c k ps1 j cj code ci IL Hret Hcj Hj Hpc Hchk XC Hcin).
  - destruct (Z.eqb_spec pc DEADPC) as [->|ND].
    + apply andb_prop in X as [Hi HD]. apply Nat.eqb_eq in Hi. subst i. exact (leaf_dead c k ps1 IL HD).
    + apply andb_prop in X as [X XR]. apply andb_prop in X as [Hbase HBL]. destruct (is_err i) eqn:Hie.
      * apply andb_prop in XR as [XR HV]. apply andb_prop in XR as [Hcodes Hec8]. exact (leaf_exit_err i c k ps1 pc IL Hie Hbase HBL Hcodes Hec8 HV).
      * apply andb_prop in XR as [Hec XR]. destruct (Nat.eqb_spec i JPOP) as [->|HiP].
        -- apply andb_prop in XR as [XR HE]. apply andb_prop in XR as [HV HR].
           apply (leaf_exit_ok JPOP c k ps1 pc _ _ 8 4097 IL eq_refl eq_refl Hbase HBL Hec HV HR HE). left. repeat split; reflexivity.
        -- apply andb_prop in XR as [XR XC]. apply andb_prop in XR as [Hi HE]. pose proof (has_gh_jvs i Hi) as Hgh. apply orb_prop in XC as [XC|XC]; apply andb_prop in XC as [HV HR].
           ++ apply (leaf_exit_ok i c k ps1 pc _ _ 0 1 IL Hgh Hie Hbase HBL Hec HV HR HE). right. split; [reflexivity|]. split; [reflexivity|]. left. split; reflexivity.
           ++ apply orb_prop in HR as [HR|HR].
              ** apply (leaf_exit_ok i c k ps1 pc _ _ 4 1 IL Hgh Hie Hbase HBL Hec HV HR HE). right. split; [reflexivity|]. split; [reflexivity|]. right. split; [reflexivity | left; reflexivity].
              ** apply (leaf_exit_ok i c k ps1 pc _ _ 7 1 IL Hgh Hie Hbase HBL Hec HV HR HE). right. split; [reflexivity|]. split; [reflexivity|]. right. split; [reflexivity | right; reflexivity].
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
  - assert (Hden0 : CH2.den E0 (nth 0 G.BLS []) = PML.ps_blocks ps) by (change (nth 0 G.BLS []) with SPT.BL0; exact (kit SPT.den_BL0 E0 (CC.env_agree_refl _ _))).
    split.
    + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr. split; [unfold CH2.cur; rewrite Hden0; exact HH | reflexivity].
    + unfold XI. change (is_err 0) with false. cbv iota. split; [intros a _; reflexivity | intros Q; discriminate Q].
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
Hypothesis VALIDATE_OK : PMS.validate_spec L.
Hypothesis PARENT_OK : PMS.parent_spec L.
Hypothesis POP_OK : PMS.pop_state_spec L.
Hypothesis SETEC_OK : PMS.set_ec_spec L.
Hypothesis VISS_OK : PMS.visit_string_spec L PMS.PC_VIS_STRING.
Hypothesis VISK_OK : PMS.visit_key_spec L PMS.PC_VIS_KEY.

Theorem end_string_value_ok : PMS.end_string_value_spec L HI.
Proof.
  unfold PMS.end_string_value_spec, PMS.ptrans_stale, PMS.ptrans_gb. intros mw LBo cr sp r P V E B kx bx g ps. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & (Ha0 & Ha3 & Ha4 & Hmore & Hst & (s & len & Ha1 & Ha2 & Hlen & Htxt & Hsrg1 & Hsrg2 & Htok)) & HPA & (HWF & HLV) & HWIN & HBB & HVIS & HEC & HLS & HG & HPC & OP & OV & OE & AP1 & AP2 & AP3) Hcont.
  pose proof (SPT.pa_def _ _ _ HPA) as HdP.
  destruct (PB2.cell_exists M (P + 160) 8 ltac:(lia)) as (line0 & Rc1 & Hc1); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  destruct (PB2.cell_exists M (P + 168) 8 ltac:(lia)) as (pos0 & Rc2 & Hc2); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  destruct OP as (OP1 & OP2 & OP3). destruct Hentry as (E1 & E2 & E3 & E4 & Hstk). pose proof (L5C.stk_floor _ _ _ _ Hstk) as FL. pose proof Hstk as (S1 & S2 & S3 & S4 & S5).
  assert (HP0 : 0 <= P + 220) by (unfold PMS.ESV_SCR in *; lia). assert (HP1 : P + 220 + Z.of_nat 1 <= 2 ^ 64) by (cbn [Z.of_nat Pos.of_succ_nat]; lia).
  destruct (PB3.bytes_of_defined_r M 1%nat (P + 220) HP0 HP1) as (tb & Htl & Htb & Htr); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  destruct tb as [|tag0 [|? ?]]; try discriminate Htl. inversion Htr as [|? ? Rc3 _]; subst.
  assert (Hc3 : PML.u8 M (P + 220) tag0) by (specialize (Htb 0%nat ltac:(cbn; lia)); cbn [nth Z.of_nat] in Htb; rewrite Z.add_0_r in Htb; exact Htb).
  exact (main L HI HIok LAY FPM VALIDATE_OK PARENT_OK POP_OK SETEC_OK VISS_OK VISK_OK mw LBo cr sp r P V E B kx bx g ps fx R M model K s len HH Hmo HKnil Hfp (conj E1 (conj E2 (conj E3 (conj E4 Hstk)))) Ha0 Ha1 Ha2 Ha3 Ha4 Hmore Hst Hlen Htxt (conj Hsrg1 Hsrg2) Htok
           HPA HWF HLV HWIN HBB HVIS HEC HLS HG HPC (conj OP1 (conj OP2 OP3)) OV OE AP1 AP2 AP3 Hcont line0 pos0 tag0 Hc1 Hc2 Hc3 (conj Rc1 (conj Rc2 Rc3))).
Qed.
End Final.
End EndStringValueProof.

