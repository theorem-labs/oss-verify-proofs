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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_psome_cboth_T Cut_psome_cboth_D Cut_psome_cboth.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsoInstCB PsoSemA PsoSemCA PsoKnCB ParseSomeChkCB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_cboth.

Module PSOX.
Section X.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation LK := (PSOI.iLK I).   Local Abbreviation cr := (PSOI.icr I).
Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).      Local Abbreviation V := (PSOI.iV I).     Local Abbreviation E := (PSOI.iE I).     Local Abbreviation B := (PSOI.iB I).
Local Abbreviation kx := (PSOI.ikx I).   Local Abbreviation bx := (PSOI.ibx I).    Local Abbreviation g := (PSOI.ig I).     Local Abbreviation ps := (PSOI.ips I).
Local Abbreviation M0 := (PSOI.iM I).    Local Abbreviation ch := (PSOI.ich I).
Let E0 := PSOI.E0 I.
Let st0 := PSOI.st0 I.
Let wlen := PSOI.wlen I.
Let wp0 := PSOI.wp0 I.
Let we0 := PSOI.we0 I.

Definition bptrI (i : nat) (Ex : env) : Z := CL5A.uv Ex (fst (PSO.blk0 i)).
Definition bcapI (i : nat) (Ex : env) : Z := CL5A.uv Ex (snd (PSO.blk0 i)).
Definition sbI (i : nat) (Ex : env) : Z := CL5A.uv Ex (fst (PSO.blk1 i)).
Definition scapI (i : nat) (Ex : env) : Z := CL5A.uv Ex (snd (PSO.blk1 i)).

Definition stk_kx (sc : Z) : Z := Z.log2 (1056 / sc) * hl_k_per_malloc L.
Definition stk_bx (sc : Z) : Z := hl_b_lin L * (2112 - 2 * sc) + Z.log2 (1056 / sc) * hl_b_overhead L.
Definition Cred (i : nat) (Ex : env) (cr1 : credit) : Prop := PMSA.bufcredA L cr1 (bcapI i Ex) (stk_kx (scapI i Ex) + kx) (stk_bx (scapI i Ex) + bx).

Definition FLF (Ex : env) : Prop := ar_fs ar <= CL5A.uv Ex FLE < ar_fs ar + 11571200 /\ ~ aclient L ar LBo FF sp (CH.hd_scr GT.HDECL) (CL5A.uv Ex FLE).

Definition WIN (ps1 : PML.pstate) : Prop :=
  match PML.ps_win ps with
  | Some (p0, e0) => exists p1, PML.ps_win ps1 = Some (p1, e0) /\ p0 <= p1 <= e0
  | None => PML.ps_win ps1 = None
  end.

Definition QOK (ps1 : PML.pstate) : Prop := In (PML.ps_st ps1) QSTATES \/ (PML.ps_st ps1 = PML.ST_NUMBER /\ PMSA.win_exhausted ps1).

Definition STOPOK (ps1 : PML.pstate) (Mx : mem) : Prop := PML.ps_more ps1 = false ->
  (PML.ws_ok ps1 /\ PML.ps_done ps1 = true /\ PML.ps_st ps1 = PML.ST_DONE) \/
  (PMCUR.wf_c (PMCUR.ps_set_more ps1 true) /\ PMCUR.evp (hl_segs L) Mx V (PML.ps_level ps) (PML.ps_win ps) ps1).

Definition PTRJ (pc : Z) (ps1 : PML.pstate) (code : Z) : Prop :=
  code = 0 -> PML.ps_more ps1 = true ->
   (pc = PNUMBER -> In (PML.ps_st ps1) [PML.ST_NUMBER; PML.ST_ACCEPT; PML.ST_EXPECT_COMMA_OR_END] /\ (PML.ps_st ps1 = PML.ST_NUMBER -> PMSA.win_exhausted ps1)) /\
   (pc = ENDINT \/ pc = ENDFRAC -> In (PML.ps_st ps1) [PML.ST_ACCEPT; PML.ST_EXPECT_COMMA_OR_END]).

Definition PTR (pc : Z) (ps1 : PML.pstate) (code : Z) (Mx : mem) : Prop :=
  code = 0 ->
  (PML.ps_more ps1 = true ->
   (pc = PNUMBER -> In (PML.ps_st ps1) [PML.ST_NUMBER; PML.ST_ACCEPT; PML.ST_EXPECT_COMMA_OR_END] /\ (PML.ps_st ps1 = PML.ST_NUMBER -> PMSA.win_exhausted ps1)) /\
   (pc = ENDINT \/ pc = ENDFRAC -> In (PML.ps_st ps1) [PML.ST_ACCEPT; PML.ST_EXPECT_COMMA_OR_END])) /\
  STOPOK ps1 Mx.
Lemma PTR_of : forall pc ps1 code Mx, PTRJ pc ps1 code -> (code = 0 -> STOPOK ps1 Mx) -> PTR pc ps1 code Mx.
Proof. intros pc ps1 code Mx H1 H2 Hc. split; [exact (H1 Hc) | exact (H2 Hc)]. Qed.

Definition REL (ps1 : PML.pstate) (code : Z) (Mx : mem) : Prop :=
  (code <> 0 \/ PML.ps_more ps1 = false \/ PMSA.win_exhausted ps1) /\
  (PML.ps_st ps = PML.ST_ACCEPT -> code = 0 /\ PML.ps_more ps1 = false /\ PML.ps_done ps1 = true) /\
  (PMSA.win_exhausted ps -> code = 0 -> PML.ps_more ps1 = true -> In (PML.ps_st ps) [PML.ST_NUMBER; PML.ST_CR] /\ ~ In (PML.ps_st ps1) [PML.ST_NUMBER; PML.ST_CR]) /\
  PMCUR.cur_post (hl_segs L) ps ps1 code Mx V.

Definition a0reg (i : nat) : expr := nth 10 (CC.cp_regs (PSO.cutn i)) (ELit 0).

Definition retk (k : PSO.kind) : bool := match k with PSO.KRetx | PSO.KSetsh => true | _ => false end.
Definition wlk (k : PSO.kind) : bool := match k with PSO.KRetx | PSO.KSetsh | PSO.KSe | PSO.KSetec => false | _ => true end.

Definition vpx (i : nat) : Z :=
  match PSO.src_of i with
  | Some (i0, k0, _) => match CAX.cell_at (PSO.leaf_cells i0 k0) (EVar 2) (-105) 1 with Some (ELit z) => z | _ => -1 end
  | None => -1
  end.
Lemma set_win_self : forall psx, PML.ps_set_win psx (PML.ps_win psx) = psx.
Proof. intros psx; destruct psx; reflexivity. Qed.
Record CORE (i : nat) (Ex : env) (M : mem) (mw : option (Z * Z)) (ps1 : PML.pstate) (code : Z) (g1 : PML.ls_state) : Prop := MKCORE {
  c_pa : PMLA.parser_at (hl_segs L) IC M P (PML.ps_set_win ps1 mw);
  c_mw : (PSO.curk (PSO.kind_of i) = false /\ mw = PML.ps_win ps1) \/
         (PSO.curk (PSO.kind_of i) = true /\ exists pm pn e, mw = Some (pm, e) /\ PML.ps_win ps1 = Some (pn, e) /\ pm <= pn /\ CL5A.uv Ex (a0reg i) = pn) \/
         (PSO.kind_of i = PSO.KPushb /\ exists p e, mw = Some (p, e) /\ PML.ps_win ps1 = Some (p + 1, e));
  c_sh : PMLA.parser_sh M ps1;
  c_win : WIN ps1;
  c_bb : PML.buf_bound ps1 B;
  c_ec : PMLA.ec_at (hl_segs L) IC M E code;
  c_ls : PMLA.ls_ok (hl_segs L) IC g1 M;
  c_g : g1 = g \/ (g1 = PML.regJ g /\ code <> 0);
  c_lv : PML.ps_more ps1 = true -> PML.ps_level ps1 = PML.ps_level ps;
  c_blk : PML.ps_blocks ps1 = [(bptrI i Ex, bcapI i Ex); (sbI i Ex, scapI i Ex)];
  c_na : PSO.u0 i = false -> retk (PSO.kind_of i) = false -> st0 <> PML.ST_ACCEPT;
  c_wl : PSO.u0 i = false -> wlk (PSO.kind_of i) = true -> 1 <= wlen;
  c_e0 : PSO.u0 i = true -> env_agree 60 E0 Ex }.

Definition POSTP (i : nat) (Ex : env) (M : mem) : Prop :=
  exists ps1 code g1, CORE i Ex M (PML.ps_win ps1) ps1 code g1 /\ PMCUR.wf_c ps1 /\ (code <> 0 -> PML.ps_more ps1 = false) /\ REL ps1 code M.

Record XI_R (i : nat) (Ex : env) (M : mem) : Prop := MKXI {
  xi_flf : (2 <= i)%nat -> FLF Ex;
  xi_entry : PSO.kind_of i = PSO.KEntry -> env_agree 60 E0 Ex /\ M = M0;
  xi_sm : PSO.kind_of i = PSO.KSm -> CORE i Ex M (PML.ps_win ps) ps 0 g;
  xi_loop : PSO.is_loopk (PSO.kind_of i) = true ->
      exists ps1 g1, CORE i Ex M (PML.ps_win ps1) ps1 0 g1 /\ PMCUR.wf_c ps1 /\ STOPOK ps1 M /\ (PSO.isQcut i = true -> PML.ps_more ps1 = true -> QOK ps1);
  xi_errh : PSO.kind_of i = PSO.KErrh \/ PSO.kind_of i = PSO.KParent -> exists ps1 g1, CORE i Ex M (PML.ps_win ps1) ps1 0 g1 /\ PMCUR.wf_c ps1 /\ PML.ps_more ps1 = true;
  xi_se : PSO.kind_of i = PSO.KSe -> exists ps1 g1, CORE i Ex M (PML.ps_win ps1) ps1 0 g1 /\ PMCUR.wf_c ps1 /\ PML.ps_more ps1 = false;
  xi_setec : PSO.kind_of i = PSO.KSetec -> exists ps1 code g1, CORE i Ex M (PML.ps_win ps1) ps1 code g1 /\ PMCUR.wf_c ps1 /\ 1 <= code <= 31 /\ g1 = PML.regJ g;
  xi_pt : forall pc, PSO.kind_of i = PSO.KPt pc ->
      exists ps1 mw code g1, CORE i Ex M mw ps1 code g1 /\ PMCUR.wf_c ps1 /\ (code <> 0 -> PML.ps_more ps1 = false) /\ 0 <= code <= 31 /\ PTR pc ps1 code M;
  xi_pushb : PSO.kind_of i = PSO.KPushb ->
      exists ps1 p e g1 c, CORE i Ex M (Some (p, e)) ps1 0 g1 /\ PML.ps_win ps1 = Some (p + 1, e) /\ PMCUR.wf_c ps1 /\ PML.ps_more ps1 = true /\
                           PML.ps_st ps1 <> PML.ST_NUMBER /\ PML.ps_buf ps1 = [c];
  xi_vpush : PSO.kind_of i = PSO.KVpush ->
      exists ps1 g1 x stk, CORE i Ex M (PML.ps_win ps1) ps1 0 g1 /\ PML.ps_more ps1 = true /\ PML.ps_stack ps1 = stk ++ [x] /\ (length stk <= 1026)%nat /\ x = vpx i /\
        PMCUR.wf_c (PML.PS (PML.ps_st ps1) (PML.ps_sst ps1) (PML.ps_nst ps1) true (PML.ps_done ps1) (PML.ps_level ps1) stk (PML.ps_sb ps1) (PML.ps_scap ps1)
                          (PML.ps_bcap ps1) (PML.ps_bptr ps1) (PML.ps_buf ps1) (PML.ps_win ps1)) /\
        ((PML.is_expect (PML.ps_st ps1) /\ x = PML.ps_st ps1) \/ (PML.ps_st ps1 = PML.ST_SLASH_STAR /\ x = PML.ST_SLASH_STAR) \/
         ((PML.ps_st ps1 = PML.ST_EXPECT_MEMBER_NAME_OR_END \/ PML.ps_st ps1 = PML.ST_EXPECT_MEMBER_NAME) /\ x = PML.ST_MEMBER_NAME));
  xi_pop : PSO.kind_of i = PSO.KPop ->
      exists ps1 g1 x, CORE i Ex M (PML.ps_win ps1) ps1 0 g1 /\ PML.ps_more ps1 = true /\ PML.comment_or_cr (PML.ps_st ps1) /\
        PMCUR.wf_c (PML.PS (PML.ps_st ps1) (PML.ps_sst ps1) (PML.ps_nst ps1) true (PML.ps_done ps1) (PML.ps_level ps1) (PML.ps_stack ps1 ++ [x]) (PML.ps_sb ps1) (PML.ps_scap ps1)
                          (PML.ps_bcap ps1) (PML.ps_bptr ps1) (PML.ps_buf ps1) (PML.ps_win ps1)) /\
        CL5A.uv Ex (EVar (CC.cp_nx (PSO.cutn i) - APC.NCS - 2)) = x;
  xi_post : PSO.kind_of i = PSO.KRetx \/ PSO.kind_of i = PSO.KSetsh -> POSTP i Ex M;
  xi_vis : PSO.kind_of i = PSO.KVis ->
      exists ps1 g1 e, CORE i Ex M (PML.ps_win ps1) ps1 0 g1 /\ PMCUR.wf_c ps1 /\ PML.ps_more ps1 = true /\ PMCUR.ev_at (hl_segs L) M V e /\
                       (e = PMCUR.EvNull \/ exists b, e = PMCUR.EvBool b);
  xi_dead : PSO.kind_of i = PSO.KDead -> False }.
Definition XI (i : nat) (Ex : env) (A1 : list (Z * Z)) (M : mem) (m1 : Model) : Prop := XI_R i Ex M.
End X.
End PSOX.
