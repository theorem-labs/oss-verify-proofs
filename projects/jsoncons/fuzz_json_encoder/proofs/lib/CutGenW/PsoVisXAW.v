(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtC CutRtD CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecs PmEncSpecs PmLibSpecsXA PmLibSpecsX PmLibSpecsW PmRef PmRefFacts PmRefXA PmLibSpecsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA PtKitB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_psome_xasan_T Cut_psome_xasan_D Cut_psome_xasan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PsKitA XKitXA PsoInstXA PsoSemXA PsoKnXA ParseSomeChkXA PsoAuxXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import PsoInstXAW PsoBaseXAW PsoXiXAW PsoLinkXAW PsoFrmXAW PsoExitXAW PsoStXAW PsoCkXAW PsoCallXAW PsoKnOkXAW PsoPtXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import PsoWTabXA PsoWKitXA PsoWKit2XA PsoWTab2XA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmRefNonneg.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation RSEGS := Pm4PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_xasan.

Module PSOVIS.
Import PSOCALL.

(* [comment removed for export] *)
Definition vis_leaf (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (kinb (PSO.kind_of i) [PSO.KCsl] && bshz_ok i && more1 c (SR.ps_cells ps))%bool.
Definition vis_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TOther pc => (negb (Z.eqb pc VNULL || Z.eqb pc VBOOL) || PSO.dead_chk i ps pc || vis_leaf i c ps)%bool | _ => true end.
Lemma VIS_all : CH2.leaves_all G.CPS G.TAGS vis_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma VISL : forall pc i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> pc = VNULL \/ pc = VBOOL -> PSO.dead_chk i ps0 pc = false -> vis_leaf i c ps0 = true.
Proof.
  intros pc i c k ps0 IL Hpc Hd. pose proof (CH2.leaves_all_sound _ _ _ VIS_all _ _ _ _ _ IL) as X. cbn [vis_chk] in X.
  assert (E : (Z.eqb pc VNULL || Z.eqb pc VBOOL)%bool = true) by (destruct Hpc as [-> | ->]; reflexivity). rewrite E, Hd in X. exact X.
Qed.

(* [comment removed for export] *)
Lemma depth_scalar : forall es ev, match ev with PMES.EvNull | PMES.EvBool _ => True | _ => False end -> PMES.depth (PMES.estep es ev) = PMES.depth es.
Proof.
  intros es ev Hev. destruct ev; try contradiction; unfold PMES.estep, PMES.depth; (destruct es as [|c0 r0]; [reflexivity|]); cbn [PMES.pre_scalar snd]; destruct (PMES.ec_arr c0); cbn [PMES.bump length]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma CORE_reg {SCFG_P : ScfgP} : forall (J : PSOIW.inst) g' i Ex (M : mem) mw ps code g1,
  PSOX.CORE J i Ex M mw ps code g1 -> PSOIW.xinv J M g' -> (code = 0 -> PMXA.enc_sync ps g') -> PSOX.CORE (PSOIW.setg J g') i Ex M mw ps code g1.
Proof. intros J g' i Ex M mw ps code g1 CO HX HS. destruct CO. constructor; assumption. Qed.

(* [comment removed for export] *)
Lemma XI_VIS {SCFG_P : ScfgP} : forall (J : PSOIW.inst) j E2 (M2 : mem) ps g1 pc, PSO.kind_of j = PSO.KVis pc -> PSOX.FLF J E2 ->
  PSOX.CORE J j E2 M2 (PML.ps_win ps) ps 0 g1 -> PML.wf_ps ps -> PML.ps_more ps = true -> PSOX.WCORE J j E2 M2 ps 0 -> PSOX.XI_R J j E2 M2.
Proof.
  intros J j E2 M2 ps g1 pc HK HFL CO WF Hm WCO.
  constructor; try (intros _; exact HFL); try (intros Hk; exfalso; rewrite HK in Hk; first [discriminate Hk | destruct Hk as [Hk|Hk]; discriminate Hk]);
    try (intros pc0 Hk; exfalso; rewrite HK in Hk; discriminate Hk).
  intros pc0 _. exists ps, g1. split; [exact CO|]. split; [exact WCO|]. split; [exact WF | exact Hm].
Qed.

Section V.
Context {SCFG_P : ScfgP}.
Variable I : PSOIW.inst.
Hypothesis IETA : PSOIW.setg I (PSOIW.ig1 I) = I.      (* [comment removed for export] *)
Local Abbreviation L := (PSOIW.iL I).     Local Abbreviation ar := (PSOIW.iar I).    Local Abbreviation C := (PSOIW.iC I).     Local Abbreviation HI := (PSOIW.iHI I).
Local Abbreviation LBo := (PSOIW.iLBo I). Local Abbreviation FF := (PSOIW.iFF I).    Local Abbreviation LK := (PSOIW.iLK I).   Local Abbreviation A := (PSOIW.iA I).
Local Abbreviation sp := (PSOIW.isp I).   Local Abbreviation P := (PSOIW.iP I).      Local Abbreviation V := (PSOIW.iV I).     Local Abbreviation E := (PSOIW.iE I).
Local Abbreviation B := (PSOIW.iB I).     Local Abbreviation M := (PSOIW.iM I).      Local Abbreviation model := (PSOIW.imodel I). Local Abbreviation K := (PSOIW.iK I).
Local Abbreviation HIok := (PSOIW.iHIok I). Local Abbreviation SQ := (PSOIW.iSQ I).   Local Abbreviation kx := (PSOIW.ikx I).   Local Abbreviation bx := (PSOIW.ibx I).
Local Abbreviation E0 := (PSOIW.E0 I).      Local Abbreviation LB := (PSOIW.LB I).       Local Abbreviation WW := (PSOIW.WW I).       Local Abbreviation Wo := (Wo I).      Local Abbreviation LBV := (PSOIW.LBV I (PSOIW.ig1 I)).
Local Abbreviation Cred := (PSOX.Cred I). Local Abbreviation XI := (PSOX.XI I).
Local Abbreviation bptrI := (PSOX.bptrI).  Local Abbreviation bcapI := (PSOX.bcapI). Local Abbreviation sbI := (PSOX.sbI). Local Abbreviation scapI := (PSOX.scapI).

(* [comment removed for export] *)
Definition KXV (bc sc : Z) : Z := kx + PSOX.stk_kx I sc + Z.log2 (2 ^ 27 / bc) * hl_k_per_malloc L.
Definition BXV (bc sc : Z) : Z := bx + PSOX.stk_bx I sc + hl_b_lin L * (2 ^ 28 - 2 * bc) + Z.log2 (2 ^ 27 / bc) * hl_b_overhead L.
Lemma CRD_E : forall g1 cr1 bc sc, In sc [66; 132; 264; 528; 1056] ->
  PMSA.bufcredA L cr1 bc (PSOX.stk_kx I sc + PSOIW.KXG I g1) (PSOX.stk_bx I sc + PSOIW.BXG I g1) ->
  PMXA.ecreditA L (PSOIW.ibenc I) cr1 g1 (KXV bc sc) (BXV bc sc)
  /\ forall cr' g', PMXA.ecreditA L (PSOIW.ibenc I) cr' g' (KXV bc sc) (BXV bc sc) -> PMSA.bufcredA L cr' bc (PSOX.stk_kx I sc + PSOIW.KXG I g') (PSOX.stk_bx I sc + PSOIW.BXG I g').
Proof.
  intros g1 cr1 bc sc Hsc HC. unfold PMSA.bufcredA, PMXA.ecreditA, KXV, BXV, PSOIW.KXG, PSOIW.BXG in *. cbn [fst snd] in *.
  destruct (L5A.aly_cost L C (PSOIW.iLAY I)) as (Q1 & Q2 & Q3). pose proof (stk_pot_nonneg I sc Hsc) as [K0 B0]. pose proof (PSOIW.iHkx I) as KX0. pose proof (PSOIW.iHbx I) as BX0.
  pose proof (Z.log2_nonneg (2 ^ 27 / bc)) as L1. pose proof (Z.mul_nonneg_nonneg _ _ L1 Q1) as KP0. pose proof (Z.mul_nonneg_nonneg _ _ L1 Q3) as BP2.
  destruct HC as (C27 & K1 & B1 & CK & CB).
  assert (L2 : 0 <= 2 ^ 28 - 2 * bc) by (clear - C27; lia). pose proof (Z.mul_nonneg_nonneg _ _ Q2 L2) as BP1.
  set (kp := Z.log2 (2 ^ 27 / bc) * hl_k_per_malloc L) in *. clearbody kp. set (bp1 := hl_b_lin L * (2 ^ 28 - 2 * bc)) in *. clearbody bp1.
  set (bp2 := Z.log2 (2 ^ 27 / bc) * hl_b_overhead L) in *. clearbody bp2. set (skx := PSOX.stk_kx I sc) in *. clearbody skx. set (sbx := PSOX.stk_bx I sc) in *. clearbody sbx.
  pose proof (PSOIW.KENC0 I g1) as E1. pose proof (PSOIW.iBENC0 I g1) as E2.
  split; [clear - C27 K1 B1 CK CB KP0 BP1 BP2 E1 E2 KX0 BX0 K0 B0; lia|].
  intros cr' g' (F1 & F2 & F3 & F4). pose proof (PSOIW.KENC0 I g') as E3. pose proof (PSOIW.iBENC0 I g') as E4. clear - C27 F1 F2 F3 F4 E3 E4 KP0 BP1 BP2 KX0 BX0 K0 B0. lia.
Qed.

(* [comment removed for export] *)
Lemma SUPP_geomO : forall i E1 A1 M1 m1 a, (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 ->
  SUPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a ->
  0 <= a < 2 ^ 64 /\ a < sp - SCR /\ aclient L ar ([(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] ++ LBo) (CHA.curF FF sp PSO.FFS i E1) (sp + PSO.CSP) 256 a.
Proof.
  intros i E1 A1 M1 m1 a Hi HA Ha. pose_facts I.
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (HcB & HcF & HagE & F0 & F1 & F64 & F2 & F3 & F4 & FAP & (crX & LKX & HHX & _)).
  set (F := CL5A.uv E1 FE) in *. rewrite HcF.
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHX) as WFX.
  assert (OBJ : forall o n, CL5A.ainfr FF o n -> 0 < n -> o <= a < o + n ->
            0 <= a < 2 ^ 64 /\ a < sp - SCR /\ aclient L ar ([(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] ++ LBo) ((F, 4, sp + PSO.CSP + 32) :: FF) (sp + PSO.CSP) 256 a).
  { intros o n Hfr Hn Hx. destruct (CL5A.infr_rng L ar LB FF o n RFx Hfr Hn) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). pose proof Hfr as (f & Hf & G1 & G2).
    split; [clear - Hx X3 X6; lia|]. split; [unfold SCR; clear - Hx X4 S2; lia|].
    right; right; right; left; exists f; split; [right; exact Hf|]; clear - Hx G1 G2; lia. }
  assert (BLK : forall u n, In (u, n) ([(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] ++ LBo) -> (u <= a < u + n \/ in_shadow_of u n a) ->
            0 <= a < 2 ^ 64 /\ a < sp - SCR /\ aclient L ar ([(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] ++ LBo) ((F, 4, sp + PSO.CSP + 32) :: FF) (sp + PSO.CSP) 256 a).
  { intros u n Hun Hx.
    assert (HunV : In (u, n) ([(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] ++ LBV)).
    { apply in_app_or in Hun as [Hun|Hun]; apply in_or_app; [left; exact Hun | right; unfold PSOIW.LBV; apply in_or_app; left; exact Hun]. }
    destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFX (u, n) HunV) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _). cbn [fst snd] in D0, D1, D16, D3, D4, D5, D6, D7.
    destruct Hx as [Hx|Hx].
    - split; [clear - Hx D5 D7; lia|]. split; [unfold SCR; clear - Hx D4 S2; lia|]. left; exists (u, n); split; [exact Hun | cbn [fst snd]; exact Hx].
    - pose proof (SHR u n a D5 D3 D7 Hx) as RG. split; [clear - RG; lia|]. split; [unfold SCR; clear - RG S2 CL; lia|]. do 6 right; exists (u, n); split; [exact Hun | exact Hx]. }
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|(u & n & Hun & Ha)]]]]]]].
  - exact (OBJ P 272 Pfr ltac:(clear; lia) Ha).
  - exact (OBJ E 16 Efr ltac:(clear; lia) Ha).
  - exact (BLK _ _ (or_introl eq_refl) (or_introl Ha)).
  - exact (BLK _ _ (or_introl eq_refl) (or_intror Ha)).
  - exact (BLK _ _ (or_intror (or_introl eq_refl)) (or_introl Ha)).
  - exact (BLK _ _ (or_intror (or_introl eq_refl)) (or_intror Ha)).
  - pose proof (STATIC_lo I a Ha) as RG. split; [clear - RG; lia|]. split; [unfold SCR; clear - RG S2 CL FSLO; lia | exact (STCL I a _ _ _ _ Ha)].
  - exact (BLK u n ltac:(apply in_or_app; right; exact Hun) Ha).
Qed.

(* [comment removed for export] *)
Lemma CORE_mvg : forall g' i Ex (M1 M2 : mem) mw ps1 code g1 LBx FFx LKx crx Ax Mx Vx,
  ri_inv HI LBx FFx LKx crx Ax Mx Vx -> In (bptrI i Ex, bcapI i Ex) LBx -> In (sbI i Ex, scapI i Ex) LBx -> PML.wf_ps ps1 ->
  (forall a, SUPP I (bptrI i Ex) (bcapI i Ex) (sbI i Ex) (scapI i Ex) a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  PSOIW.xinv I M2 g' -> (code = 0 -> PMXA.enc_sync ps1 g') ->
  PSOX.CORE I i Ex M1 mw ps1 code g1 -> PSOX.CORE (PSOIW.setg I g') i Ex M2 mw ps1 code g1.
Proof.
  intros g' i Ex M1 M2 mw ps1 code g1 LBx FFx LKx crx Ax Mx Vx HHx INb INs WF AG HX HS CO.
  pose proof (PSOX.c_blk _ _ _ _ _ _ _ _ CO) as CB. unfold PML.ps_blocks in CB. injection CB as Esc Esb Ebc Ebp.
  assert (HG : g1 <> PML.LS0) by (destruct (PSOX.c_g _ _ _ _ _ _ _ _ CO) as [-> | [-> _]]; [exact (PSOIW.iHG I) | discriminate]).
  pose proof (PSSA.wf_shape ps1 WF) as (_ & _ & SL & _).
  constructor.      (* [comment removed for export] *)
  - apply (parser_at_mv I M1 M2 _ _ _ _ AG LBx FFx LKx crx Ax Mx Vx HHx INb INs (PML.ps_set_win ps1 mw)); try exact (PSOX.c_pa _ _ _ _ _ _ _ _ CO).
    all: destruct ps1; cbn [PML.ps_set_win PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap] in *; first [exact Ebp | exact Ebc | exact Esb | exact Esc].
  - exact (PSOX.c_mw _ _ _ _ _ _ _ _ CO).
  - apply (parser_sh_mv I M1 M2 _ _ _ _ AG LBx FFx LKx crx Ax Mx Vx HHx INb INs ps1); try exact (PSOX.c_sh _ _ _ _ _ _ _ _ CO); try first [exact Ebp | exact Ebc | exact Esb | exact Esc].
    pose proof (PTB.pa_slen L IC _ _ _ (PSOX.c_pa _ _ _ _ _ _ _ _ CO)) as SL2. clear - SL2. destruct ps1; cbn [PML.ps_set_win PML.ps_scap PML.ps_stack] in *. exact SL2.
  - exact (PSOX.c_win _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_bb _ _ _ _ _ _ _ _ CO).
  - exact (ec_at_mv I M1 M2 _ _ _ _ AG code (PSOX.c_ec _ _ _ _ _ _ _ _ CO)).
  - exact (ls_ok_mv I M1 M2 _ _ _ _ AG g1 HG (PSOX.c_ls _ _ _ _ _ _ _ _ CO)).
  - exact (PSOX.c_g _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_blk _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_na _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_wl _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_e0 _ _ _ _ _ _ _ _ CO).
  - exact HX.
  - exact HS.
Qed.

(* [comment removed for export] *)
Section GENV.
Variables (pc : Z) (xa : CAXA.xsumA) (EV : bool -> PMES.eev) (ARGS : bool -> list (Z * Z) -> list fframe -> Z -> Z -> Z -> bvmap 5 word -> PMSA.mem -> Prop).
Hypothesis HPCV : pc = VNULL \/ pc = VBOOL.
Hypothesis Hxs : PSOK.xs_at pc = Some xa.
Hypothesis HRK : PSO.ret_kind pc = PSO.KVis pc.
Hypothesis XSCR : CAX.xs_scr (PSOK.x_of xa) = XKA.VIS.
Hypothesis XNG : CAX.xs_ng (PSOK.x_of xa) = 0%nat.
Hypothesis XKEEP : forall regs BL, CAX.xs_keep (PSOK.x_of xa) regs BL = BL.
Hypothesis XWRG : forall regs, CAX.xs_wregs (PSOK.x_of xa) regs = PSOP.WRX.
Hypothesis XA0 : forall regs g0, CAX.xs_a0 (PSOK.x_of xa) regs g0 = Some (ELit 1).
Hypothesis XBLK : forall regs cells g0 BL, PSOK.blk_of xa regs cells g0 BL = BL.
Hypothesis XNEWS : forall regs cells g0 BL, PSOK.news_of xa regs cells g0 BL = PSOK.STATICS_ISH ++ PSOK.MEASNEWS cells ++ PSOK.BSHZ ++ PSOK.FLAGC cells.
Hypothesis VT : forall b, PMXA.vtransA L ar HI IC (PSOIW.ienc_invA I) XKA.VIS XKA.VISD (PSOIW.ibenc I) (PSOIW.ieroomA I) pc (EV b) (ARGS b).
Hypothesis EVSC : forall b, match EV b with PMES.EvNull | PMES.EvBool _ => True | _ => False end.
Hypothesis HARG : forall b LBx FFx spx Vx S2x R Mx, (pc = VBOOL -> PMSA.a1 R (PML.b2z b)) -> ARGS b LBx FFx spx Vx S2x R Mx.

Lemma L_VISG : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> PSO.call_chk i c k ps0 pc = true -> PSO.dead_chk i ps0 pc = false ->
  forall M0c, OKVt I M0c -> PSOP.LEAFV I (PSOIW.ig1 I) M0c i c ps0.
Proof.
  intros i c k ps0 IL CHK HD. pose_facts I. pose_U I. pose proof (PSOIW.VV I) as (_ & V4 & _).
  destruct (PSOCK.CALL_UNPACK pc xa i c k ps0 IL CHK HD Hxs) as (j & cj & ci & Hret & CU).
  destruct CU as [Hci Hcj Hpc HKj HND Hchk Hcsp Hblk HFj HPC HVS].
  rewrite XSCR, XNG, XKEEP, XWRG, XA0, XNEWS in Hchk. rewrite XKEEP, XBLK in Hblk.
  pose proof (VISL pc i c k ps0 IL HPCV HD) as SIDE. unfold vis_leaf in SIDE.
  apply andb_prop in SIDE as [SIDE Smore]. apply andb_prop in SIDE as [Skind Sbshz].
  apply kinb_in in Skind. cbn [In] in Skind. destruct Skind as [Hki|[]]. symmetry in Hki. unfold bshz_ok in Sbshz. apply expr_eqb_eq in Sbshz.
  assert (HKj' : PSO.kind_of j = PSO.KVis pc) by (rewrite HKj; exact HRK).
  assert (Hck : PSO.curk (PSO.kind_of i) = false) by (rewrite Hki; reflexivity).
  pose proof (ge2_of_kind i c _ Hci eq_refl ltac:(rewrite Hki; discriminate)) as Hi.
  pose proof (ge2_of_kind j cj _ Hcj HKj' ltac:(discriminate)) as Hj.
  assert (Hfeq : CHA.frames_eqb (nth j PSO.FFS []) (nth i PSO.FFS []) = true) by (rewrite (ffs_i i Hi), (ffs_i j Hj); reflexivity).
  assert (HPCL : In pc PSOCK.PCALLEES) by (destruct HPCV as [-> | ->]; cbn; tauto).
  destruct (PSOCK.CK_NEWS pc i c k ps0 IL HPCL HD) as (SMEAS & SFLAG).
  destruct (PSO.pview (CC.cp_know c)) as [t|] eqn:Ht; [|unfold PSO.pre_chk in HPC; rewrite Ht in HPC; discriminate HPC].
  destruct (PSO.pview (SR.ps_cells ps0)) as [l|] eqn:Hl; [|unfold PSO.pre_chk in HPC; rewrite Ht, Hl in HPC; discriminate HPC].
  assert (HNE1 : pc <> PSTRING) by (destruct HPCV as [-> | ->]; discriminate). assert (HNE2 : pc <> PNUMBER) by (destruct HPCV as [-> | ->]; discriminate).
  pose proof (pclass_psame i c ps0 pc t l HPC HNE1 HNE2 Ht Hl) as HCL.
  (* [comment removed for export] *)
  pose proof HVS as HVS0. assert (EPC : (Z.eqb pc VNULL || Z.eqb pc VBOOL)%bool = true) by (destruct HPCV as [-> | ->]; reflexivity). rewrite EPC in HVS0. cbn [negb orb] in HVS0.
  unfold PSO.vis_pre in HVS0. apply andb_prop in HVS0 as [HVS0 _]. apply andb_prop in HVS0 as [HVS0 _]. apply andb_prop in HVS0 as [Sreg10 Sreg11].
  assert (HB : exists b : bool, pc = VBOOL -> CL.ps_reg_is ps0 11 (ELit (PML.b2z b)) = true).
  { apply orb_prop in Sreg11 as [S01|R1]; [apply orb_prop in S01 as [PN|R0]|].
    - exists true. intros Hpb. exfalso. apply Z.eqb_eq in PN. rewrite Hpb in PN. discriminate PN.
    - exists false. intros _. exact R0.
    - exists true. intros _. exact R1. }
  destruct HB as (b & Hb).
  intros M0c OKV fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAXV HFP Hag HLF HIHV.
  pose proof HAXV as HAX. rewrite (PSOP.AMBXV_E I IETA M0c) in HAX. pose proof HAX as [HA0 HXI].
  assert (HA : AAMB I i E1 A1 M1 m1) by (exists M0c; split; [exact OKV | exact HA0]).
  pose proof (PSOX.xi_flf _ _ _ _ HXI (proj1 Hi)) as HFL.
  destruct (SRC I i E1 A1 M1 m1 HXI ltac:(rewrite Hki; cbn [In]; tauto)) as (ps1 & g1 & CO & WF & WCO1).
  destruct (PSOCK.PSAME I pc i c k ps0 E1 R1 A1 M1 m1 E' R' M' m' (PML.ps_win ps1) ps1 0 g1 t l IL HPCL HD HPC Ht Hl HCL Hi Hck HAt HA Hag HLF HFL CO eq_refl WF)
    as (ps2 & CL2 & WFL & PSF).
  (* [comment removed for export] *)
  destruct (PSOWT2.VISW pc i c k ps0 IL HPCV HD j t l Hret Ht Hl) as (wst & wbv & wa & HLD & Hwa & HWO & HF220 & WNS & WNN).
  destruct WCO1 as (cp & cp2 & tg & XC1 & WS1). unfold PSOX.WSIM in WS1. rewrite Hki in WS1. destruct WS1 as (cc & evs & al & BE & MT).
  destruct (PSOWK2.leaf_decides I i c k ps0 _ E1 R1 A1 M1 m1 E' R' M' m' ps1 0 g1 cc evs al _ wst wbv wa IL Hi HAt HA Hag HLF CO WF BE (proj1 MT) HLD)
    as (bb & HR1 & HBV & Hbb & HST1 & HCST & HDIS). rewrite Hwa in HDIS.
  pose proof BE as (HATH & HSY & HCM & _). assert (HMO1 : PML.ps_more ps1 = true) by (destruct (proj1 MT) as (_ & R2 & _); rewrite <- R2; exact HCM).
  assert (HATH' : PMRF.hreach (PSOX.c0 I) (PSOX.w0 I) cc (bb :: PSOX.rem I ps1 (PSOX.WO i + 1)) evs al) by (unfold PSOX.ATH in HATH; rewrite HR1 in HATH; exact HATH).
  assert (HM2 : PML.ps_more ps2 = true).
  { rewrite (PSOCK.pf_eq _ _ _ _ _ PSF). cbn [PSOST.ps_upd PML.ps_more]. unfold more1 in Smore. rewrite Ht in Smore.
    destruct (PSOCK.more_pin c (SR.ps_cells ps0) t) as [z|] eqn:Hz; [|discriminate Smore]. destruct z as [|[| |]|]; try discriminate Smore.
    pose proof (PSOCK.pf_more _ _ _ _ _ PSF 1 Hz) as X. destruct (PML.ps_more ps1); [reflexivity | discriminate X]. }
  destruct (LEAFK I i c ps0 E1 A1 M1 m1 E' R' M' m' Hi Hci (PSOST.cpf_of i c Hci) HA Hag HLF) as (FZ & W65 & W60 & CELLS & REGS & _).
  assert (W10 : bv_unsigned (ev E' 10) = P) by (rewrite (FZ 10%nat ltac:(clear; lia)); exact U10).
  assert (W11 : bv_unsigned (ev E' 11) = V) by (rewrite (FZ 11%nat ltac:(clear; lia)); exact U11).
  assert (W37 : bv_unsigned (ev E' 37) = SQ) by (rewrite (FZ 37%nat ltac:(clear; lia)); exact U37).
  refine (CHV.callee_leafV L ar C HI HIok (LYI I) (LYR I) GT.NF E0 M model A LBo FF LK sp G.HDECL WW Wo G.BLS PSO.FFS 11 PMES.eghost PMES.g_lbv (PSOP.CredV I) (PSOP.XIv I)
            (STKF I) SCRP NF32 U2 V4 (WINC I) (WOKo I) (PSOIW.iHffrs I) (CRS_OKo I) (WRS_OK I) (IMG_OK I)
            G.CPS K PMSA.fp_ok (DEF0 I) S6 GT.SCELLS GT.GLO GT.GHI (SCOK I) (GOTOK I) (PSOIW.iHKnil I) (PSOIW.ig1 I) M0c
            pc XKA.VIS 0%nat (nth i G.BLS []) PSOP.WRX _ (Some (ELit 1)) XKA.VISD i c ps0 j cj ci OKV Hcj Hchk Hpc Hfeq ltac:(rewrite (ffs_i i Hi); unfold XKA.VISD; cbn [length Z.of_nat Pos.of_succ_nat]; clear; lia)
            fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAXV HFP Hag HLF HIHV _).
  rewrite !(PSOP.LBVE I), (PSOP.CredE I IETA). intros cr1 LK1 CF HH1 HLK1 HC1.
  destruct CF as [HAm HR Hreq HV HK' [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
  rewrite Hcsp in *.
  pose proof (PSOCK.akag_of I i E1 A1 M' m' (ex_intro _ M0c (conj OKV HAm))) as AK.
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (HcB & HcF & _).
  pose proof (PSOX.c_pa _ _ _ _ _ _ _ _ CL2) as PA2. rewrite PSOX.set_win_self in PA2.
  pose proof (PSOX.c_sh _ _ _ _ _ _ _ _ CL2) as SH2.
  pose proof (PSOX.c_blk _ _ _ _ _ _ _ _ CL2) as BK2. unfold PML.ps_blocks in BK2. injection BK2 as Ebp Ebc Esb Esc.
  pose proof (PSSA.wf_shape ps2 WFL) as (_ & _ & SL & SC).
  pose proof (PSOX.c_x _ _ _ _ _ _ _ _ CL2) as [XINV' XLIT']. pose proof (PSOX.c_sync _ _ _ _ _ _ _ _ CL2 eq_refl) as [XD XK].
  assert (HDEN : CH2.den E1 (nth i G.BLS []) = [(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)]) by (pose proof HcB as X; unfold CHA.curB in X; exact (app_inv_tail _ _ _ X)).
  (* [comment removed for export] *)
  unfold PSOX.Cred in HC1. rewrite Esc in SC. destruct (CRD_E (PSOIW.ig1 I) cr1 _ _ SC HC1) as [HEC1 HECR].
  rewrite HcB, HcF.
  eexists. eexists. split; [exact (VT b ([(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] ++ LBo) ((CL5A.uv E1 FE, 4, sp + PSO.CSP + 32) :: FF) LK1 cr1 A1 (sp + PSO.CSP) (CC.cp_pc cj) V SQ
                                   (KXV (bcapI i E1) (scapI i E1)) (BXV (bcapI i E1) (scapI i E1)) (PSOIW.ig1 I))|].
  split.
  { (* [comment removed for export] *)
    unfold PMSA.fobj, PMES.ENC_SIZE. change (408 / 8) with 51. change (24 / 8) with 3.
    split; [exact (REGS 10%nat VE V Sreg10 ltac:(unfold VE, PSOC.VE; cbn [edenot]; exact W11))|].
    split; [apply HARG; intros Hpb; exact (REGS 11%nat (ELit (PML.b2z b)) (PML.b2z b) (Hb Hpb) ltac:(cbn [edenot]; apply L5.unsigned_lit; destruct b; cbn; clear; lia))|].
    split; [destruct (proj1 (Z.mod_divide sp 32 ltac:(clear; lia)) (PSOIW.iHsp32 I)) as [q Hq]; rewrite Hq; unfold PSO.CSP; replace (q * 32 + -672) with ((q - 21) * 32) by (clear; lia); apply Z_mod_mult|].
    split; [exact (PSOCK.STKSH I M' XKA.VIS AK ltac:(unfold XKA.VIS; clear; lia) eq_refl ltac:(unfold XKA.VIS; clear; lia))|].
    split; [exact XINV'|].
    split; [pose proof (EVSC b) as ES; destruct (EV b); try contradiction; exact Logic.I|].
    split; [apply (PSOWK.room_lit I cc bb (PSOX.rem I ps1 (PSOX.WO i + 1)) evs al (EV b) HATH' HSY (PSOWK2.SIq_of_match I cc ps1 cp cp2 tg MT WF HMO1) HCM HDIS);
           pose proof (EVSC b) as ES; destruct (EV b); try contradiction; [left; reflexivity | right; eexists; reflexivity]|].
    split; [destruct (PSOX.c_ls _ _ _ _ _ _ _ _ CL2) as [IMG _]; exact IMG|].
    split; [exact XLIT'|].
    split; [exact HEC1|].
    assert (INF : incl FF ((CL5A.uv E1 FE, 4, sp + PSO.CSP + 32) :: FF)) by (intros f Hf; right; exact Hf).
    split; [exact (PSOCK.FOBJ I M' _ V 408 AK (PSOIW.iOVX I) INF ltac:(clear; lia) ltac:(clear - VQ3 VQ6; lia))|].
    split; [exact (PSOCK.FOBJ I M' _ SQ 24 AK (PSOIW.iOS2 I) INF ltac:(clear; lia) ltac:(clear - SR3 SR6; lia))|].
    exact (PSOIW.iAP5 I). }
  (* [comment removed for export] *)
  intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (g' & pay & Ha0' & HINV2 & Hes & Hpay & Hlen & HLIT2 & -> & -> & -> & HCR2) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  exists [], g'. split; [reflexivity|]. cbv zeta.
  set (gx := CH2.ci_nx ci) in *. set (E2 := CH2.retEx E' gx [] R2).
  pose proof (CH2.retEx_agree E' gx [] R2 : env_agree gx E' E2) as Hag2. fold E2 in Hag2.
  destruct HV as (_ & _ & HV3 & _).
  assert (Hag12 : env_agree (CC.cp_nx c) E1 E2) by (eapply CC.env_agree_trans; [exact Hag | eapply CC.env_agree_le; [exact Hag2 | exact HV3]]).
  pose proof (PSOST.nx66 i c Hi Hci) as NX.
  destruct (BLKEQ I i j c E1 E2 Hci ltac:(clear - Hi; lia) Hblk Hag12) as (QJ1 & QJ2 & QJ3 & QJ4 & QJB).
  assert (HDENJ : CH2.den E2 (nth j G.BLS []) = [(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)]).
  { pose proof QJB as X. unfold CHA.curB in X. rewrite <- HDEN. exact (app_inv_tail _ _ _ X). }
  split; [unfold PMSA.a0 in Ha0'; cbn [edenot]; rewrite Ha0'; reflexivity|].
  split; [rewrite HdenB, HDEN; apply incl_refl|].
  split.
  { intros w a Hw Hin. exact (PSOP.WR_X I E' ltac:(unfold CL5A.uv; cbn [edenot]; exact W11) ltac:(unfold CL5A.uv; cbn [edenot]; exact W37) w a Hw Hin). }
  split; [intros w a Hw Hin (_ & _ & Ko); apply (Ko w); [unfold PSOIW.WW; apply in_or_app; right; exact Hw | exact Hin]|].
  split; [unfold CHA.curB; rewrite HDENJ; exact HH2|].
  (* [comment removed for export] *)
  assert (WX : forall w a, In w (PMXA.W_encA IC V SQ) -> L5.in_rng w a -> PSOIW.xfoot I (PSOIW.ig1 I) a).
  { intros w a Hw Hin. unfold PMXA.W_encA, PMES.O_STACK, PMES.O_DEPTH in Hw. unfold L5.in_rng in Hin. unfold PSOIW.xfoot, XKA.xfoot, PMXA.efootA, PMES.ENC_SIZE.
    destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [left; left; clear - Hin; lia | left; left; clear - Hin; lia | left; right; left; clear - Hin; lia | right; clear - Hin; lia]. }
  assert (WSUPP : forall w a, In w (PMXA.W_encA IC V SQ) -> L5.in_rng w a -> SUPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a -> False).
  { intros w a Hw Hin Ha. destruct (XGEOM I i E1 A1 M1 m1 a Hi HA (WX w a Hw Hin)) as (_ & _ & _ & _ & XP & _ & _ & XB1 & XB2 & XS1 & XS2 & XE & XST).
    destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|(u & n & Hun & Ha)]]]]]]].
    - exact (XP Ha). - exact (XE Ha). - exact (XB1 Ha). - exact (XB2 Ha). - exact (XS1 Ha). - exact (XS2 Ha).
    - destruct (IMGCL I a Ha) as [RG _]. pose proof (NLIT a Ha) as NL. exact (XST a 1 ltac:(clear - RG; lia) ltac:(clear - RG; lia) ltac:(clear - NL; lia) ltac:(clear; lia)).
    - destruct (KLB I u n a Hun Ha) as (_ & _ & KO). exact (KO w ltac:(unfold PSOIW.WW; apply in_or_app; right; exact Hw) Hin). }
  assert (AGS : forall a, SUPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha. destruct (SUPP_geomO i E1 A1 M1 m1 a Hi HA Ha) as (RG & X1 & X4). rewrite HcF in X4. apply (proj1 HP a). split; [exact RG|]. split.
    - apply (CHA.aclient_scr_pt _ _ _ _ _ _ (sp + PSO.CSP) 256); [exact X4 | unfold PSO.CSP, SCR, XKA.VIS in *; clear - X1; lia].
    - intros w Hw Hin. exact (WSUPP w a Hw Hin Ha). }
  (* [comment removed for export] *)
  assert (CL3 : PSOX.CORE (PSOIW.setg I g') i E1 M2 (PML.ps_win ps2) ps2 0 g1).
  { rewrite HcB in HH1.
    apply (CORE_mvg g' i E1 M' M2 (PML.ps_win ps2) ps2 0 g1 _ _ _ _ _ _ _ HH1 (or_introl eq_refl) (or_intror (or_introl eq_refl)) WFL AGS); [| |exact CL2].
    - split; [exact HINV2 | exact HLIT2].
    - intros _. split; [rewrite Hes, (depth_scalar _ _ (EVSC b)); exact XD | exact XK]. }
  assert (CL4 : PSOX.CORE (PSOIW.setg I g') j E2 M2 (PML.ps_win ps2) ps2 0 g1).
  { apply (PSOCK.CORE_RE (PSOIW.setg I g') i j E1 E2 M2 _ ps2 0 g1 CL3); [rewrite HKj'; reflexivity | reflexivity | exact QJ1 | exact QJ2 | exact QJ3 | exact QJ4 | exact (PSOCK.U0RET i k j Hret)
      | intros _; rewrite Hki; reflexivity | intros _; rewrite Hki; reflexivity
      | intros _; eapply CC.env_agree_le; [exact Hag12 | clear - NX; lia]]. }
  assert (T65 : CL5A.uv E2 FE = CL5A.uv E1 FE) by (unfold CL5A.uv, FE, FEV; cbn [edenot]; rewrite <- (proj1 Hag12 65%nat) by (clear - NX; lia); reflexivity).
  assert (T60 : CL5A.uv E2 FLE = CL5A.uv E1 FLE) by (unfold CL5A.uv, FLE, FLV; cbn [edenot]; rewrite <- (proj1 Hag12 60%nat) by (clear - NX; lia); reflexivity).
  split.
  { (* [comment removed for export] *)
    unfold PSOP.CredV, PSOX.Cred. rewrite QJ2, QJ4. exact (HECR cr' g' HCR2). }
  split.
  { unfold PSOP.XIv, PSOX.XI. apply (XI_VIS (PSOIW.setg I g') j E2 M2 ps2 g1 pc HKj'); [| exact CL4 | exact WFL | exact HM2 |].
    2:{ (* [comment removed for export] *)
        destruct (PSOWK2.XCELLS_leaf I i c ps0 E1 A1 M1 m1 E' R' M' m' cp cp2 tg Hi Hci HA HFL Hag HLF XC1) as (_ & _ & XCL). specialize (XCL HF220).
        exists cp, cp2, tg. split; [exact (XCELLS_mv I M' M2 _ _ _ _ AGS cp cp2 tg XCL)|].
        unfold PSOX.WSIM. rewrite HKj'. exists cc, bb, evs, al. unfold PSOX.MID.
        pose proof (PSOWK2.rem_shift_core I i E1 M1 (PML.ps_win ps1) ps1 0 g1 ps2 _ (PSOX.WO j) CO (PSOCK.pf_adv _ _ _ _ _ PSF l Hl)) as RS1.
        pose proof (PSOWK2.rem_shift_core I i E1 M1 (PML.ps_win ps1) ps1 0 g1 ps2 _ (PSOX.WO j + 1) CO (PSOCK.pf_adv _ _ _ _ _ PSF l Hl)) as RS2.
        unfold PSOX.WO in RS1, RS2, HR1, HATH' |- *. rewrite HWO in RS1. replace (PSOWT.woff j + 1 + Z.max 0 (PSO.d_adv (PSO.mkdelta (SR.ps_cells ps0) t l))) with (PSOWT.woff i + 1) in RS2 by (clear - HWO; lia).
        change (PSOX.rem (PSOIW.setg I g')) with (PSOX.rem I). change (PSOX.c0 (PSOIW.setg I g')) with (PSOX.c0 I). change (PSOX.w0 (PSOIW.setg I g')) with (PSOX.w0 I).
        split; [split; [rewrite RS1, RS2; exact HR1 | split; [rewrite RS1, HR1; exact HATH' | split; [exact HCM | exact HDIS]]]|].
        split; [rewrite (PSOCK.pf_eq _ _ _ _ _ PSF); apply PSOWK2.MATCH_upd; [rewrite HST1; exact WNS | rewrite HST1; exact WNN | exact MT]|].
        exact (PSOWK2.sync_lit I g' evs al (EV b) pay HSY (EVSC b) Hes Hpay Hlen). }
    unfold PSOX.FLF. rewrite T60. exact HFL. }
  (* [comment removed for export] *)
  intros X HX _.
  apply in_app_or in HX as [HX|HX]; [exact (proj1 (Forall_forall _ _) (PSOCK.NEWS_SI I E2 A2 m2 M2 _ _ _ _ HH2) X HX)|].
  apply in_app_or in HX as [HX|HX]; [exact (proj1 (Forall_forall _ _) (PSOCK.NEWS_KR I c ps0 E' R' A1 M1 m1 M' m' E2 _ _ HLF (CC.env_agree_le _ _ _ _ Hag2 HV3) SMEAS) X HX)|].
  apply in_app_or in HX as [HX|HX].
  { destruct HX as [<-|[]]. pose proof (PSOX.c_sh _ _ _ _ _ _ _ _ CL4) as [SHB _].
    apply (PSOCK.NEWS_BSHZ I E2 A2 m2 M2 _ _ _ _ (bptrI i E1) (bcapI i E1) HH2); [left; reflexivity | | | rewrite <- Ebp, <- Ebc; exact SHB].
    - unfold PSOX.bptrI in *. rewrite Sbshz in *. unfold CL5A.uv. cbn [edenot]. rewrite <- (proj1 Hag12 56%nat) by (clear - NX; lia). reflexivity.
    - rewrite <- Ebc. exact (PTB.pa_bcap L IC _ _ _ PA2). }
  unfold PSOK.FLAGC in HX. rewrite SFLAG in HX.
  assert (FLC : L5.u64_at (hl_segs L) M' (CL5A.uv E1 FE + 1016) (CL5A.uv E1 FLE)).
  { pose proof (cell_at_has _ _ _ _ _ SFLAG) as Hin. pose proof (CELLS _ Hin) as KF.
    pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (CL5A.uv E1 FE + 1016) KF ltac:(unfold estart; cbn [a_base a_off]; change (bv_unsigned (edenot E' (EVar 65))) with (CL5A.uv E' FE); rewrite W65; reflexivity)) as G0.
    pose proof (CBA.amb_off L ar C HI HIok (LYB I) GT.NF E0 M0c model A LBV FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 11 i E1 A1 M1 m1 HA0) as Hoff1.
    assert (Hoff : H_off_segments (hl_segs L) (ahid A1 m')) by (rewrite (L5LZ.sbm_ahid A1 m1 m' (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)); exact Hoff1).
    apply (CL5A.u64_full (hl_segs L) _ Hoff) in G0. change (CL5A.uv E' (EVar 60)) with (CL5A.uv E' FLE) in G0. rewrite W60 in G0. exact G0. }
  rewrite <- HcF in HH2.
  exact (proj1 (Forall_forall _ _) (PSOCK.NEWS_FLAGC I i E1 A1 M1 m1 E2 A2 m2 M' M2 m' _ _ _ _ _ _ Hi HA HFL HH1 HH2 FLC T65 T60) X HX).
Qed.
End GENV.

(* [comment removed for export] *)
Lemma L_VNULL : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther VNULL) -> PSO.call_chk i c k ps0 VNULL = true -> PSO.dead_chk i ps0 VNULL = false ->
  forall M0c, OKVt I M0c -> PSOP.LEAFV I (PSOIW.ig1 I) M0c i c ps0.
Proof.
  exact (L_VISG VNULL PSOK.XS_VNULL (fun _ => PMES.EvNull) (fun _ => PMXA.argT) (or_introl eq_refl) eq_refl eq_refl eq_refl eq_refl (fun _ _ => eq_refl) (fun _ => eq_refl) (fun _ _ => eq_refl)
           (fun _ _ _ _ => eq_refl) (fun _ _ _ _ => eq_refl) (fun _ => PSOIW.iVNULL I) (fun _ => Logic.I) (fun _ _ _ _ _ _ _ _ _ => Logic.I)).
Qed.
Lemma L_VBOOL : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther VBOOL) -> PSO.call_chk i c k ps0 VBOOL = true -> PSO.dead_chk i ps0 VBOOL = false ->
  forall M0c, OKVt I M0c -> PSOP.LEAFV I (PSOIW.ig1 I) M0c i c ps0.
Proof.
  exact (L_VISG VBOOL PSOK.XS_VBOOL (fun b => PMES.EvBool b) (fun b _ _ _ _ _ R _ => PMSA.a1 R (PML.b2z b)) (or_intror eq_refl) eq_refl eq_refl eq_refl eq_refl (fun _ _ => eq_refl) (fun _ => eq_refl)
           (fun _ _ => eq_refl) (fun _ _ _ _ => eq_refl) (fun _ _ _ _ => eq_refl) (PSOIW.iVBOOL I) (fun _ => Logic.I) (fun b _ _ _ _ _ R _ H => H eq_refl)).
Qed.
Definition PTV : list Z := [VNULL; VBOOL].
Lemma L_VIS : forall pc, In pc PTV -> forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> PSO.call_chk i c k ps0 pc = true -> PSO.dead_chk i ps0 pc = false ->
  forall M0c, OKVt I M0c -> PSOP.LEAFV I (PSOIW.ig1 I) M0c i c ps0.
Proof. intros pc Hpc. unfold PTV in Hpc. cbn [In] in Hpc. destruct Hpc as [<-|[<-|[]]]; [exact L_VNULL | exact L_VBOOL]. Qed.
End V.
End PSOVIS.
