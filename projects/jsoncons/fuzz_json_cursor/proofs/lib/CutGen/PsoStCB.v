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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtC CutRtD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA PtKitB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_psome_cboth_T Cut_psome_cboth_D Cut_psome_cboth.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsKitA PsoInstCB PsoSemA PsoSemCA PsoKnCB ParseSomeChkCB PsoBaseCB PsoAuxCB PsoXiCB PsoLinkCB PsoFrmCB PsoExitCB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_cboth.

Module PSOST.
Section S.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation LK := (PSOI.iLK I).   Local Abbreviation A := (PSOI.iA I).
Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).      Local Abbreviation V := (PSOI.iV I).     Local Abbreviation E := (PSOI.iE I).
Local Abbreviation M := (PSOI.iM I).     Local Abbreviation model := (PSOI.imodel I).
Local Abbreviation HIok := (PSOI.iHIok I).
Local Abbreviation E0 := (PSOI.E0 I).      Local Abbreviation LB := (PSOI.LB I).
Local Abbreviation WW := (WW I).            Local Abbreviation Cred := (PSOX.Cred I).
Local Abbreviation bptrI := (PSOX.bptrI).  Local Abbreviation bcapI := (PSOX.bcapI). Local Abbreviation sbI := (PSOX.sbI). Local Abbreviation scapI := (PSOX.scapI).

Definition ps_upd (ps1 : PML.pstate) (st2 sst2 nst2 : Z) (more2 done2 : bool) (buf2 : list Z) (w2 : option (Z * Z)) : PML.pstate :=
  PML.PS st2 sst2 nst2 more2 done2 (PML.ps_level ps1) (PML.ps_stack ps1) (PML.ps_sb ps1) (PML.ps_scap ps1) (PML.ps_bcap ps1) (PML.ps_bptr ps1) buf2 w2.

Record MEM (Mx : mem) (mw : option (Z * Z)) (psx : PML.pstate) (code : Z) (g1 : PML.ls_state) : Prop := MKMEM {
  m_pa : PMLA.parser_at (hl_segs L) IC Mx P (PML.ps_set_win psx mw);
  m_sh : PMLA.parser_sh Mx psx;
  m_ec : PMLA.ec_at (hl_segs L) IC Mx E code;
  m_ls : PMLA.ls_ok (hl_segs L) IC g1 Mx }.

Definition FPC (a : Z) : Prop := P + 148 <= a < P + 192 \/ P + 200 <= a < P + 216 \/ P + 220 <= a < P + 224 \/ P + 232 <= a < P + 240.

Lemma cutn_of : forall i c, nth_error G.CPS i = Some c -> PSO.cutn i = c.
Proof. intros i c H. unfold PSO.cutn. exact (nth_error_nth _ _ CA.dummy_cp H). Qed.
Lemma cpf_of : forall i c, nth_error G.CPS i = Some c -> PSO.cpf_ok i (CC.cp_F c) = true.
Proof.
  intros i c Hci. assert (Hi : (i < PSO.NCUT)%nat) by (rewrite <- len_cps; apply nth_error_Some; rewrite Hci; discriminate).
  pose proof (proj1 (forallb_forall _ _) PSOA.cpf_all i ltac:(apply in_seq; clear - Hi; lia)) as X. cbv beta in X. rewrite (cutn_of i c Hci) in X. exact X.
Qed.
Lemma nx66 : forall i c, (2 <= i < PSO.NCUT)%nat -> nth_error G.CPS i = Some c -> (66 <= CC.cp_nx c)%nat.
Proof.
  intros i c Hi Hci.
  assert (X : forallb (fun k => Nat.leb 66 (CC.cp_nx (nth k G.CPS CA.dummy_cp))) (seq 2 (PSO.NCUT - 2)) = true) by vmc_refl.
  rewrite forallb_forall in X. specialize (X i ltac:(apply in_seq; clear - Hi; lia)). apply Nat.leb_le in X. rewrite (nth_error_nth _ _ CA.dummy_cp Hci) in X. exact X.
Qed.

Lemma AGX : forall i c ps0 E1 A1 M1 m1 E' R' M' m', (2 <= i < PSO.NCUT)%nat -> nth_error G.CPS i = Some c ->
  AAMB I i E1 A1 M1 m1 -> PSOX.FLF I E1 -> env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  forall a, SUPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a ->
  (forall o n, In (PE, o, ELit n) (CC.cp_F c) -> ~ (P + o <= a < P + o + n)) -> (PSO.has_bufbyte (CC.cp_F c) = true -> a <> bptrI i E1) ->
  M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof.
  intros i c ps0 E1 A1 M1 m1 E' R' M' m' Hi Hci HA HFL Hag HLF a Ha HPR HBB.
  destruct (SUPP_geom I i E1 A1 M1 m1 a Hi HA Ha) as (RG & X1 & X2 & X3 & _ & X5).
  pose proof (X5 HFL) as NFL. pose proof (nx66 i c Hi Hci) as NX. pose proof (cpf_of i c Hci) as CF.
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (_ & _ & _ & F0 & F1 & F64 & _).
  pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6 i c E1 E' A1 M1 m1 HA (G.NF_le i c Hci) Hag) as HagE'.
  pose_U I. assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite <- (proj1 HagE' 2%nat ltac:(unfold GT.NF, Cut_psome_cboth_T.NF; clear; lia)); exact U2).
  assert (W10 : bv_unsigned (ev E' 10) = P) by (rewrite <- (proj1 HagE' 10%nat ltac:(unfold GT.NF, Cut_psome_cboth_T.NF; clear; lia)); exact U10).
  assert (W65 : CL5A.uv E' FE = CL5A.uv E1 FE) by (unfold CL5A.uv, FE, FEV; cbn [edenot]; rewrite <- (proj1 Hag 65%nat) by (clear - NX; lia); reflexivity).
  assert (W60 : CL5A.uv E' FLE = CL5A.uv E1 FLE) by (unfold CL5A.uv, FLE, FLV; cbn [edenot]; rewrite <- (proj1 Hag 60%nat) by (clear - NX; lia); reflexivity).
  destruct (BLKAG i c E1 E' Hci Hag) as (B1 & _).
  assert (F8 : CL5A.uv E1 FE mod 8 = 0) by (exact (CHA.mod8_of_64 _ F64)).
  assert (SHF : ~ (CL5A.uv E1 FE / 8 + 2147450880 <= a < CL5A.uv E1 FE / 8 + 2147450880 + 128)).
  { intros Hs. apply X3. unfold in_shadow_of, S, SB. set (F := CL5A.uv E1 FE) in *.
    assert (Q : (F + 1024 - 1) / 8 = F / 8 + 127).
    { rewrite (Z.div_mod F 8) at 1 by lia. rewrite F8. replace (8 * (F / 8) + 0 + 1024 - 1) with (7 + (F / 8 + 127) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    rewrite Q. clear - Hs. lia. }
  assert (X2' : ~ (CL5A.uv E' FE <= a < CL5A.uv E' FE + 1024)) by (rewrite W65; exact X2).
  assert (SHF' : ~ (CL5A.uv E' FE / 8 + 2147450880 <= a < CL5A.uv E' FE / 8 + 2147450880 + 128)) by (rewrite W65; exact SHF).
  assert (NFL' : a <> CL5A.uv E' FLE) by (rewrite W60; exact NFL).
  apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF).
  unfold PSO.cpf_ok in CF. rewrite forallb_forall in CF.
  unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hr. specialize (CF _ Hr). apply orb_prop in CF.
  rewrite L5.unsigned_lit by exact RG.
  pose proof (CL5A.uv_range E' FE) as R65.
  unfold CL5A.uv, FE, FLE in X2', SHF', NFL', R65; cbn [edenot] in X2', SHF', NFL', R65.
  destruct CF as [CF|CF].
  - apply existsb_exists in CF as (u & Hu & He).
    destruct u as [[ub ulo] ulen]. unfold PSO.region_eqb in He. cbn [fst snd] in He. apply andb_prop in He as [He E3]. apply andb_prop in He as [E1' E2]. apply expr_eqb_eq in E1', E3. apply Z.eqb_eq in E2. subst rb rlo rlen.
    unfold PSO.F_NB, PSO.FP, PSO.UEXTRA, PSO.F_STK, PSO.MORE in Hu. cbn [In app] in Hu.
    destruct Hu as [Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[]]]]]]]]]]]]]]; injection Hu as <- <- <-;
      try (pose proof (HPR _ _ Hr) as HP'); unfold PE, FE, FLE, CHA.SRL3, SBz, SCR; rewrite ?CL5A.estart_srl3'; unfold estart, elenZ, CL5A.uv; cbn [a_base a_off edenot]; rewrite ?W2, ?W10; rewrite ?u64_of_Z by (clear; lia).
    + clear - X1. unfold SCR in X1. lia.
    + clear - X2'. lia.
    + clear - X2'. lia.
    + clear - SHF' R65. pose proof (Z.div_pos (bv_unsigned (ev E' FEV)) 8). lia.
    + clear - HP'. lia.
    + clear - HP'. lia.
    + clear - HP'. lia.
    + clear - HP'. lia.
    + clear - HP'. lia.
    + clear - NFL'. lia.
    + clear - HP'. lia.
    + clear - HP'. lia.
    + clear - X2'. lia.
  - unfold PSO.region_eqb in CF. cbn [fst snd] in CF. apply andb_prop in CF as [CF E3]. apply andb_prop in CF as [E1' E2]. apply expr_eqb_eq in E1', E3. apply Z.eqb_eq in E2. subst rb rlo rlen.
    assert (HB : PSO.has_bufbyte (CC.cp_F c) = true).
    { destruct (bvar_i i ltac:(clear - Hi; lia)) as (v & Hv & Hv2). unfold PSO.has_bufbyte. apply existsb_exists.
      exists (fst (PSO.blk0 i), 0, ELit 1). split; [exact Hr|]. rewrite Hv. apply negb_true_iff, Nat.eqb_neq. exact Hv2. }
    specialize (HBB HB). unfold PSOX.bptrI, CL5A.uv in B1, HBB.
    unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite u64_of_Z by (clear; lia). rewrite B1. clear - HBB. lia.
Qed.

Definition p272b (F : list SGP.region) : bool :=
  forallb (fun r => match r with (EVar v, o, ELit n) => if Nat.eqb v 10 then (Z.leb 0 o && Z.leb (o + n) 272)%bool else true | _ => true end) F.
Lemma P272_all : forallb (fun k => p272b (CC.cp_F (PSO.cutn k))) (seq 0 PSO.NCUT) = true. Proof. vmc_refl. Qed.
Lemma F_P272 : forall i c, nth_error G.CPS i = Some c -> forall o n, In (PE, o, ELit n) (CC.cp_F c) -> 0 <= o /\ o + n <= 272.
Proof.
  intros i c Hci o n Hin. assert (Hi : (i < PSO.NCUT)%nat) by (unfold PSO.NCUT; rewrite <- PSO.len_cps; apply nth_error_Some; rewrite Hci; discriminate).
  pose proof (proj1 (forallb_forall _ _) P272_all i ltac:(apply in_seq; clear - Hi; lia)) as X. cbv beta in X.
  unfold PSO.cutn in X. rewrite (nth_error_nth _ _ CA.dummy_cp Hci) in X. unfold p272b in X. rewrite forallb_forall in X. specialize (X _ Hin).
  cbv beta iota in X. unfold PE in X. rewrite Nat.eqb_refl in X. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1, X2. split; assumption.
Qed.

Lemma AGV : forall i c ps0 E1 A1 M1 m1 E' R' M' m', (2 <= i < PSO.NCUT)%nat -> nth_error G.CPS i = Some c ->
  AAMB I i E1 A1 M1 m1 -> PSOX.FLF I E1 -> env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  forall a, V + 8 <= a < V + 48 -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof.
  intros i c ps0 E1 A1 M1 m1 E' R' M' m' Hi Hci HA HFL Hag HLF a Ha.
  apply (AGX i c ps0 E1 A1 M1 m1 E' R' M' m' Hi Hci HA HFL Hag HLF a); [do 8 right; exact Ha | |].
  - intros o n Hin Hx. destruct (F_P272 i c Hci o n Hin) as (Ho1 & Ho2). pose proof (PSOI.iAP1 I) as AP. unfold PMLA.apart in AP. clear - Ha Hx Ho1 Ho2 AP. lia.
  - intros _ Hb. pose_facts I.
    destruct (FRM I i E1 A1 M1 m1 Hi HA) as (HcB & HcF & _ & _ & _ & _ & _ & _ & _ & _ & (crX & LKX & HHX & _)).
    pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHX) as WFX.
    destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFX (bptrI i E1, bcapI i E1) (or_introl eq_refl)) as ((D0 & _ & _ & D3 & _) & _ & _ & _ & Dfap). cbn [fst snd] in D0, D3, Dfap.
    destruct Vfr as (f & Hf & F1 & F2). pose proof (Dfap f ltac:(apply in_or_app; left; right; exact Hf)) as AF.
    pose proof (PSOI.VV I) as _. clear - Ha Hb F1 F2 AF D3. lia.
Qed.

Record GEOF (i : nat) (E1 : env) (M1 : mem) : Prop := MKGEO {
  g_bc : 0 < bcapI i E1 /\ bptrI i E1 mod 16 = 0 /\ 0 <= bptrI i E1 /\ bptrI i E1 + bcapI i E1 <= 2 ^ 47;
  g_sc : 0 < scapI i E1 /\ sbI i E1 mod 16 = 0 /\ 0 <= sbI i E1 /\ sbI i E1 + scapI i E1 <= 2 ^ 47;
  g_bdef : HeapIface.defined M1 (bptrI i E1) (bcapI i E1);
  g_Pb : ~ (P <= bptrI i E1 < P + 272);
  g_bP : forall a, bptrI i E1 <= a < bptrI i E1 + bcapI i E1 -> ~ (P <= a < P + 272);
  g_sP : forall a, sbI i E1 <= a < sbI i E1 + scapI i E1 -> ~ (P <= a < P + 272) /\ a <> bptrI i E1;
  g_EP : forall a, E <= a < E + 16 -> ~ (P <= a < P + 272) /\ a <> bptrI i E1;
  g_shP : forall a, in_shadow_of (bptrI i E1) (bcapI i E1) a \/ in_shadow_of (sbI i E1) (scapI i E1) a -> ~ (P <= a < P + 272) /\ a <> bptrI i E1;
  g_stP : forall a, STATIC a -> ~ (P <= a < P + 272) /\ a <> bptrI i E1;
  g_P : 0 <= P /\ P + 272 <= 2 ^ 47 /\ 0 <= E /\ E + 16 <= 2 ^ 47 }.
Lemma GEO : forall i E1 A1 M1 m1, (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 -> GEOF i E1 M1.
Proof.
  intros i E1 A1 M1 m1 Hi HA. pose_facts I.
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (HcB & HcF & HagE & F0 & F1 & F64 & F2 & F3 & F4 & FAP & (crX & LKX & HHX & _)).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHX) as WFX.
  set (bp := bptrI i E1) in *. set (bc := bcapI i E1) in *. set (sbp := sbI i E1) in *. set (sc := scapI i E1) in *.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFX (bp, bc) (or_introl eq_refl)) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & Ddef & _ & Dbap & Dfap).
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFX (sbp, sc) (or_intror (or_introl eq_refl))) as ((G0 & G1 & G16 & G3 & G4 & (G5 & G6 & G7)) & _ & _ & _ & Gfap).
  cbn [fst snd] in D0, D1, D16, D3, D4, D5, D6, D7, Ddef, Dbap, Dfap, G0, G1, G16, G3, G4, G5, G6, G7, Gfap.
  unfold BIGSHADOW_LO, BIGSHADOW_HI in D6, G6. unfold hid in O5, O7, Q5, Q7.
  destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ WFX) as (ND1 & _).
  assert (NEQ : sbp <> bp).
  { intros e. cbn [map fst app] in ND1. apply list_relations.list.NoDup_cons in ND1 as [Hni _]. apply Hni. rewrite e. apply list_elem_of_In. left. reflexivity. }
  assert (BAP : bp + bc <= sbp \/ sbp + sc <= bp).
  { pose proof (Dbap (sbp, sc) (L5C.in_lb_remove_neq bp sbp sc ([(bp, bc); (sbp, sc)] ++ LBo) (or_intror (or_introl eq_refl)) NEQ)) as X. cbn [fst snd] in X. exact X. }

  assert (INF : forall f, In f FF -> In f (((CL5A.uv E1 FE, 4, sp + PSO.CSP + 32) :: FF) ++ LKX)) by (intros f Hf; apply in_or_app; left; right; exact Hf).
  destruct Pfr as (fP & HfP & PF1 & PF2). destruct Efr as (fE & HfE & EF1 & EF2).
  pose proof (Dfap fP (INF fP HfP)) as DP. pose proof (Dfap fE (INF fE HfE)) as DE.
  pose proof (Gfap fP (INF fP HfP)) as GP.
  pose proof (PSOI.iAP2 I) as AP2. unfold PMLA.apart in AP2.
  constructor.
  - split; [exact D3|]. split; [exact D16|]. split; [clear - D5; lia | clear - D7; lia].
  - split; [exact G3|]. split; [exact G16|]. split; [clear - G5; lia | clear - G7; lia].
  - exact Ddef.
  - clear - DP PF1 PF2 D3. lia.
  - intros a Ha. clear - DP PF1 PF2 Ha. lia.
  - intros a Ha. split; [clear - GP PF1 PF2 Ha; lia | clear - BAP Ha D3 G3; lia].
  - intros a Ha. split; [clear - AP2 Ha; lia | clear - DE EF1 EF2 Ha D3; lia].
  - intros a Ha. destruct Ha as [Ha|Ha].
    + pose proof (SHR bp bc a ltac:(clear - D5; lia) D3 ltac:(clear - D7; lia) Ha) as RG. split; [clear - RG O5; lia | clear - RG D6 D3; lia].
    + pose proof (SHR sbp sc a ltac:(clear - G5; lia) G3 ltac:(clear - G7; lia) Ha) as RG. split; [clear - RG O5; lia | clear - RG D6 D3; lia].
  - intros a Ha. pose proof (IMGCL I a Ha) as (RG & _). split; [clear - RG O1 FSLO; lia|]. rewrite ILO, IHI in D1. clear - RG D1 D3. lia.
  - split; [clear - O3; lia|]. split; [clear - O6; lia|]. split; [clear - Q3; lia | clear - Q6; lia].
Qed.

Lemma U8BV : forall (Mx : mem) a v1 v2, L5.u8_at (hl_segs L) Mx a v1 -> L5.u8_at (hl_segs L) Mx a v2 -> Z_to_bv 8 v1 = Z_to_bv 8 v2.
Proof. intros Mx a v1 v2 H1 H2. unfold L5.u8_at in H1, H2. rewrite H1 in H2. congruence. Qed.
Lemma u64_modw : forall (Mx : mem) a v, L5.u64_at (hl_segs L) Mx a v -> L5.u64_at (hl_segs L) Mx a (v mod 2 ^ 64).
Proof.
  intros Mx a v H. unfold L5.u64_at in *. rewrite H. do 2 f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma U64M : forall (Mx : mem) a v1 v2, L5.u64_at (hl_segs L) Mx a v1 -> L5.u64_at (hl_segs L) Mx a v2 -> v1 mod 2 ^ 64 = v2 mod 2 ^ 64.
Proof.
  intros Mx a v1 v2 H1 H2. apply (U64INJ I Mx a); [exact (u64_modw _ _ _ H1) | exact (u64_modw _ _ _ H2) | apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia].
Qed.

Lemma PA_213 : forall (Mx : mem) psx, PMLA.parser_at (hl_segs L) IC Mx P psx ->
  L5.u8_at (hl_segs L) Mx (P + 213) 1 /\ (forall k, 0 <= k < 272 -> Mx (Z_to_bv 64 (P + k)) <> None).
Proof.
  intros Mx psx H. unfold PMLA.parser_at, PMLA.u64, PMLA.u32, PMLA.u8 in H. destruct psx; cbn in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X213 & _ & _ & _ & _ & _ & _ & _ & _ & D).
  split; [exact X213 | exact D].
Qed.
Lemma PA_buf : forall (Mx : mem) psx, PMLA.parser_at (hl_segs L) IC Mx P psx ->
  L5.bytes_at (hl_segs L) Mx (PML.ps_bptr psx) (PML.ps_buf psx) /\ L5.u8_at (hl_segs L) Mx (PML.ps_bptr psx + Z.of_nat (length (PML.ps_buf psx))) 0 /\
  Z.of_nat (length (PML.ps_buf psx)) < PML.ps_bcap psx.
Proof.
  intros Mx psx H. unfold PMLA.parser_at, PMLA.u64, PMLA.u32, PMLA.u8 in H. destruct psx; cbn in H |- *.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstr & _).
  destruct Hstr as ((_ & _ & _ & _ & BY & TM) & _ & LT). split; [exact BY|]. split; [exact TM | exact LT].
Qed.

Definition SG (i : nat) (E1 : env) (hb : bool) (a : Z) : Prop :=
  SUPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a /\ ~ FPC a /\ (hb = true -> a <> bptrI i E1).

Definition preg_ok (r : SGP.region) : bool :=
  match r with
  | (EVar 10, o, ELit n) => existsb (fun on : Z * Z => (Z.eqb o (fst on) && Z.eqb n (snd on))%bool) [(148, 44); (200, 16); (220, 4); (232, 8); (211, 1); (208, 1); (212, 1)]
  | _ => true
  end.
Lemma preg_all : forallb (fun k => forallb preg_ok (CC.cp_F (PSO.cutn k))) (seq 0 PSO.NCUT) = true.
Proof. vmc_refl. Qed.
Lemma preg_menu : forall i c, nth_error G.CPS i = Some c -> forall o n, In (PE, o, ELit n) (CC.cp_F c) ->
  In (o, n) [(148, 44); (200, 16); (220, 4); (232, 8); (211, 1); (208, 1); (212, 1)].
Proof.
  intros i c Hci o n Hr. assert (Hi : (i < PSO.NCUT)%nat) by (rewrite <- len_cps; apply nth_error_Some; rewrite Hci; discriminate).
  pose proof (proj1 (forallb_forall _ _) preg_all i ltac:(apply in_seq; clear - Hi; lia)) as X. cbv beta in X. rewrite (cutn_of i c Hci) in X.
  rewrite forallb_forall in X. specialize (X _ Hr). unfold preg_ok, PE in X. apply existsb_exists in X as ([o' n'] & Hin & He). cbn [fst snd] in He.
  apply andb_prop in He as [H1 H2]. apply Z.eqb_eq in H1, H2. subst o' n'. exact Hin.
Qed.
Lemma preg_i : forall i c, nth_error G.CPS i = Some c -> forall o n, In (PE, o, ELit n) (CC.cp_F c) -> forall a, P + o <= a < P + o + n -> FPC a.
Proof.
  intros i c Hci o n Hr a Ha. pose proof (preg_menu i c Hci o n Hr) as Hin. unfold FPC.
  cbn [In] in Hin. destruct Hin as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[]]]]]]]]; injection Hx as <- <-; clear - Ha; lia.
Qed.
Lemma SG_ag : forall i c ps0 E1 A1 M1 m1 E' R' M' m', (2 <= i < PSO.NCUT)%nat -> nth_error G.CPS i = Some c ->
  AAMB I i E1 A1 M1 m1 -> PSOX.FLF I E1 -> env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  forall a, SG i E1 (PSO.has_bufbyte (CC.cp_F c)) a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof.
  intros i c ps0 E1 A1 M1 m1 E' R' M' m' Hi Hci HA HFL Hag HLF a (Ha & HF & HB).
  apply (AGX i c ps0 E1 A1 M1 m1 E' R' M' m' Hi Hci HA HFL Hag HLF a Ha); [|exact HB].
  intros o n Hr Hin. apply HF. exact (preg_i i c Hci o n Hr a Hin).
Qed.

Lemma SG_P : forall i E1 M1 hb, GEOF i E1 M1 -> forall a, P <= a < P + 272 -> ~ FPC a -> SG i E1 hb a.
Proof. intros i E1 M1 hb GE a Ha HF. split; [left; exact Ha|]. split; [exact HF|]. intros _ e. apply (g_Pb _ _ _ GE). rewrite <- e. exact Ha. Qed.
Lemma SG_S : forall i E1 M1 hb, GEOF i E1 M1 -> forall a, sbI i E1 <= a < sbI i E1 + scapI i E1 -> SG i E1 hb a.
Proof.
  intros i E1 M1 hb GE a Ha. destruct (g_sP _ _ _ GE a Ha) as (N1 & N2).
  split; [do 4 right; left; exact Ha|]. split; [unfold FPC; clear - N1; lia | intros _; exact N2].
Qed.
Lemma SG_B : forall i E1 M1 hb, GEOF i E1 M1 -> forall a, bptrI i E1 <= a < bptrI i E1 + bcapI i E1 -> (hb = true -> a <> bptrI i E1) -> SG i E1 hb a.
Proof. intros i E1 M1 hb GE a Ha HB. pose proof (g_bP _ _ _ GE a Ha) as N1. split; [right; right; left; exact Ha|]. split; [unfold FPC; clear - N1; lia | exact HB]. Qed.
Lemma SG_E : forall i E1 M1 hb, GEOF i E1 M1 -> forall a, E <= a < E + 16 -> SG i E1 hb a.
Proof.
  intros i E1 M1 hb GE a Ha. destruct (g_EP _ _ _ GE a Ha) as (N1 & N2).
  split; [right; left; exact Ha|]. split; [unfold FPC; clear - N1; lia | intros _; exact N2].
Qed.
Lemma SG_SH : forall i E1 M1 hb, GEOF i E1 M1 -> forall a, in_shadow_of (bptrI i E1) (bcapI i E1) a \/ in_shadow_of (sbI i E1) (scapI i E1) a -> SG i E1 hb a.
Proof.
  intros i E1 M1 hb GE a Ha. destruct (g_shP _ _ _ GE a Ha) as (N1 & N2).
  split; [destruct Ha as [Ha|Ha]; [do 3 right; left; exact Ha | do 5 right; left; exact Ha]|]. split; [unfold FPC; clear - N1; lia | intros _; exact N2].
Qed.
Lemma SG_ST : forall i E1 M1 hb, GEOF i E1 M1 -> forall a, STATIC a -> SG i E1 hb a.
Proof.
  intros i E1 M1 hb GE a Ha. destruct (g_stP _ _ _ GE a Ha) as (N1 & N2).
  split; [do 6 right; left; exact Ha|]. split; [unfold FPC; clear - N1; lia | intros _; exact N2].
Qed.

Record TV (Ex : env) (v : PSO.pv) (mw : option (Z * Z)) (ps1 : PML.pstate) : Prop := MKTV {
  tv_st : Z_to_bv 8 (CL5A.uv Ex (PSO.v_st v)) = Z_to_bv 8 (PML.ps_st ps1);
  tv_sst : Z_to_bv 8 (CL5A.uv Ex (PSO.v_sst v)) = Z_to_bv 8 (PML.ps_sst ps1);
  tv_nst : Z_to_bv 8 (CL5A.uv Ex (PSO.v_nst v)) = Z_to_bv 8 (PML.ps_nst ps1);
  tv_more : Z_to_bv 8 (CL5A.uv Ex (PSO.v_more v)) = Z_to_bv 8 (PML.b2z (PML.ps_more ps1));
  tv_done : Z_to_bv 8 (CL5A.uv Ex (PSO.v_done v)) = Z_to_bv 8 (PML.b2z (PML.ps_done ps1));
  tv_wptr : CL5A.uv Ex (PSO.v_wptr v) = PSOI.wlo mw mod 2 ^ 64;
  tv_wend : CL5A.uv Ex (PSO.v_wend v) = PSOI.whi mw mod 2 ^ 64;
  tv_size : CL5A.uv Ex (PSO.v_size v) = Z.of_nat (length (PML.ps_buf ps1));
  tv_bptr : CL5A.uv Ex (PSO.v_bptr v) = PML.ps_bptr ps1 }.
Lemma cut_env : forall i E1 A1 M1 m1, (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 -> bv_unsigned (ev E1 10) = P /\ bv_unsigned (ev E1 2) = sp.
Proof.
  intros i E1 A1 M1 m1 Hi HA. destruct (FRM I i E1 A1 M1 m1 Hi HA) as (_ & _ & HagE & _). pose_U I.
  split; [rewrite <- (proj1 HagE 10%nat ltac:(unfold GT.NF, Cut_psome_cboth_T.NF; clear; lia)); exact U10 | rewrite <- (proj1 HagE 2%nat ltac:(unfold GT.NF, Cut_psome_cboth_T.NF; clear; lia)); exact U2].
Qed.
Lemma TVAL : forall i c E1 R1 A1 M1 m1 mw ps1 code g1 t, nth_error G.CPS i = Some c -> (2 <= i < PSO.NCUT)%nat ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> AAMB I i E1 A1 M1 m1 -> PSOX.CORE I i E1 M1 mw ps1 code g1 ->
  PSO.pview (CC.cp_know c) = Some t -> TV E1 t mw ps1.
Proof.
  intros i c E1 R1 A1 M1 m1 mw ps1 code g1 t Hci Hi HAt HA CO Ht.
  pose proof (CBA.amb_off L ar C HI HIok (LYB I) GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6 i E1 A1 M1 m1 HA) as Hoff1.
  destruct (cut_env i E1 A1 M1 m1 Hi HA) as (U10E1 & _).
  destruct HAt as [_ HKN]. unfold know_ok in HKN. rewrite Forall_forall in HKN.
  pose proof (PSOLK.VIEW_RD I E1 A1 m1 M1 (CC.cp_know c) t Hoff1 U10E1 HKN Ht) as VR.
  pose proof (PSOX.c_pa _ _ _ _ _ _ _ _ CO) as PA1.
  destruct (PSOLK.PA_cells I M1 ps1 mw PA1) as (Ast & Asst & Anst & Amore & Adone & Awlo & Awhi & Asz & Acap & Abp & Asb & Asend & Ascend).
  pose proof (GEO i E1 A1 M1 m1 Hi HA) as GE. destruct (g_bc _ _ _ GE) as (GB0 & _ & GB1 & GB2).
  pose proof (PSOX.c_blk _ _ _ _ _ _ _ _ CO) as CB. unfold PML.ps_blocks in CB. injection CB as Ebp Ebc Esb Esc.
  destruct (PA_buf M1 _ PA1) as (_ & _ & LT). cbn [PML.ps_set_win PML.ps_buf PML.ps_bcap] in LT.
  constructor.
  - exact (U8BV _ _ _ _ (PSOLK.vr_st _ _ _ _ VR) Ast).
  - exact (U8BV _ _ _ _ (PSOLK.vr_sst _ _ _ _ VR) Asst).
  - exact (U8BV _ _ _ _ (PSOLK.vr_nst _ _ _ _ VR) Anst).
  - exact (U8BV _ _ _ _ (PSOLK.vr_more _ _ _ _ VR) Amore).
  - exact (U8BV _ _ _ _ (PSOLK.vr_done _ _ _ _ VR) Adone).
  - pose proof (U64M _ _ _ _ (PSOLK.vr_wptr _ _ _ _ VR) Awlo) as X. rewrite Z.mod_small in X by (apply UVR). exact X.
  - pose proof (U64M _ _ _ _ (PSOLK.vr_wend _ _ _ _ VR) Awhi) as X. rewrite Z.mod_small in X by (apply UVR). exact X.
  - apply (U64INJ I M1 (P + 232)); [exact (PSOLK.vr_size _ _ _ _ VR) | exact Asz | apply UVR | clear - LT Ebc GB2 GB1; lia].
  - apply (U64INJ I M1 (P + 240)); [exact (PSOLK.vr_bptr _ _ _ _ VR) | exact Abp | apply UVR | clear - Ebp GB1 GB2 GB0; lia].
Qed.

Lemma fdelta_same : forall a b, PSO.is_same (PSO.fdelta a b) = true -> b = a.
Proof.
  intros a b H. unfold PSO.fdelta in H. destruct (expr_eqb a b) eqn:X; [apply expr_eqb_eq in X; symmetry; exact X|].
  destruct b; discriminate H.
Qed.
Lemma fdelta_lit : forall a b z, PSO.fdelta a b = PSO.Lit z -> b = ELit z.
Proof.
  intros a b z H. unfold PSO.fdelta in H. destruct (expr_eqb a b); [discriminate H|]. destruct b; try discriminate H. injection H as ->. reflexivity.
Qed.
Lemma fnorm_same : forall cells f, PSO.fnorm cells f = PSO.Same -> f = PSO.Same.
Proof.
  intros cells f H. destruct f as [| z | v |]; cbn [PSO.fnorm] in H; try discriminate H; [reflexivity|].
  destruct (CX.range3 cells (EVar v)) as [[lo hi]|]; [destruct (Z.eqb lo hi); discriminate H | discriminate H].
Qed.
Lemma is_same_eq : forall f, PSO.is_same f = true <-> f = PSO.Same.
Proof. intros f. destruct f; cbn; split; intros H; first [reflexivity | discriminate H]. Qed.
Lemma uv_agree : forall nx Ex Ey e, env_agree nx Ex Ey -> APC.expr_vars_lt nx e = true -> CL5A.uv Ey e = CL5A.uv Ex e.
Proof. intros nx Ex Ey e Hag Hv. unfold CL5A.uv. rewrite (SR.edenot_agree_AP nx Ex Ey e Hag Hv). reflexivity. Qed.

Record VAG (Ex Ey : env) (v : PSO.pv) : Prop := MKVAG {
  va_wend : CL5A.uv Ey (PSO.v_wend v) = CL5A.uv Ex (PSO.v_wend v);  va_wptr : CL5A.uv Ey (PSO.v_wptr v) = CL5A.uv Ex (PSO.v_wptr v);
  va_st : CL5A.uv Ey (PSO.v_st v) = CL5A.uv Ex (PSO.v_st v);        va_sst : CL5A.uv Ey (PSO.v_sst v) = CL5A.uv Ex (PSO.v_sst v);
  va_nst : CL5A.uv Ey (PSO.v_nst v) = CL5A.uv Ex (PSO.v_nst v);      va_more : CL5A.uv Ey (PSO.v_more v) = CL5A.uv Ex (PSO.v_more v);
  va_done : CL5A.uv Ey (PSO.v_done v) = CL5A.uv Ex (PSO.v_done v);   va_size : CL5A.uv Ey (PSO.v_size v) = CL5A.uv Ex (PSO.v_size v);
  va_bptr : CL5A.uv Ey (PSO.v_bptr v) = CL5A.uv Ex (PSO.v_bptr v) }.
Lemma view_agree : forall nx cells v Ex Ey, PSO.view_ok nx cells v = true -> env_agree nx Ex Ey -> VAG Ex Ey v.
Proof.
  intros nx cells v Ex Ey Hv Hag. unfold PSO.view_ok in Hv. cbn [forallb] in Hv.
  repeat match type of Hv with (_ && _)%bool = true => apply andb_prop in Hv as [? Hv] end.
  constructor; apply (uv_agree nx); assumption.
Qed.

Record SAMEF (E' : env) (cells : list kentry) (t l : PSO.pv) (mw : option (Z * Z)) (ps1 : PML.pstate) : Prop := MKSAME {
  s_st : PSO.d_st (PSO.mkdelta cells t l) = PSO.Same -> Z_to_bv 8 (CL5A.uv E' (PSO.v_st l)) = Z_to_bv 8 (PML.ps_st ps1);
  s_sst : PSO.d_sst (PSO.mkdelta cells t l) = PSO.Same -> Z_to_bv 8 (CL5A.uv E' (PSO.v_sst l)) = Z_to_bv 8 (PML.ps_sst ps1);
  s_nst : PSO.d_nst (PSO.mkdelta cells t l) = PSO.Same -> Z_to_bv 8 (CL5A.uv E' (PSO.v_nst l)) = Z_to_bv 8 (PML.ps_nst ps1);
  s_more : PSO.d_more (PSO.mkdelta cells t l) = PSO.Same -> Z_to_bv 8 (CL5A.uv E' (PSO.v_more l)) = Z_to_bv 8 (PML.b2z (PML.ps_more ps1));
  s_done : PSO.d_done (PSO.mkdelta cells t l) = PSO.Same -> Z_to_bv 8 (CL5A.uv E' (PSO.v_done l)) = Z_to_bv 8 (PML.b2z (PML.ps_done ps1));
  s_wptr : PSO.d_wptr (PSO.mkdelta cells t l) = PSO.Same -> CL5A.uv E' (PSO.v_wptr l) = PSOI.wlo mw mod 2 ^ 64;
  s_adv : PSO.d_adv (PSO.mkdelta cells t l) = 1 -> CL5A.uv E' (PSO.v_wptr l) = (PSOI.wlo mw + 1) mod 2 ^ 64;
  s_wend : PSO.d_wend (PSO.mkdelta cells t l) = PSO.Same -> CL5A.uv E' (PSO.v_wend l) = PSOI.whi mw mod 2 ^ 64;
  s_size : PSO.d_size (PSO.mkdelta cells t l) = PSO.Same -> CL5A.uv E' (PSO.v_size l) = Z.of_nat (length (PML.ps_buf ps1));
  s_bptr : PSO.d_bptr (PSO.mkdelta cells t l) = PSO.Same -> CL5A.uv E' (PSO.v_bptr l) = PML.ps_bptr ps1 }.
Lemma STRETCH_same : forall i c ps0 E1 R1 A1 M1 m1 E' R' M' m' mw ps1 code g1 t l,
  nth_error G.CPS i = Some c -> (2 <= i < PSO.NCUT)%nat ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> AAMB I i E1 A1 M1 m1 -> env_agree (CC.cp_nx c) E1 E' ->
  CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> PSOX.CORE I i E1 M1 mw ps1 code g1 ->
  PSO.pview (CC.cp_know c) = Some t -> PSO.view_ok (CC.cp_nx c) (CC.cp_know c) t = true ->
  SAMEF E' (SR.ps_cells ps0) t l mw ps1.
Proof.
  intros i c ps0 E1 R1 A1 M1 m1 E' R' M' m' mw ps1 code g1 t l Hci Hi HAt HA Hag HLF CO Ht HVt.
  pose proof (TVAL i c E1 R1 A1 M1 m1 mw ps1 code g1 t Hci Hi HAt HA CO Ht) as TV1.
  pose proof (view_agree _ _ _ E1 E' HVt Hag) as VA.
  assert (SF : forall a b, PSO.fdelta a b = PSO.Same -> b = a) by (intros a b H; apply fdelta_same; rewrite H; reflexivity).
  constructor; unfold PSO.mkdelta; cbn [PSO.d_st PSO.d_sst PSO.d_nst PSO.d_more PSO.d_done PSO.d_wptr PSO.d_adv PSO.d_wend PSO.d_size PSO.d_bptr]; intros D.
  - rewrite (SF _ _ D), (va_st _ _ _ VA). exact (tv_st _ _ _ _ TV1).
  - rewrite (SF _ _ (fnorm_same _ _ D)), (va_sst _ _ _ VA). exact (tv_sst _ _ _ _ TV1).
  - rewrite (SF _ _ (fnorm_same _ _ D)), (va_nst _ _ _ VA). exact (tv_nst _ _ _ _ TV1).
  - rewrite (SF _ _ (fnorm_same _ _ D)), (va_more _ _ _ VA). exact (tv_more _ _ _ _ TV1).
  - rewrite (SF _ _ (fnorm_same _ _ D)), (va_done _ _ _ VA). exact (tv_done _ _ _ _ TV1).
  - rewrite (SF _ _ D), (va_wptr _ _ _ VA). exact (tv_wptr _ _ _ _ TV1).
  - destruct (expr_eqb (PSO.v_wptr t) (PSO.v_wptr l)); cbn beta iota in D; [discriminate D|].
    unfold PSO.rng_is in D. destruct (CX.range3 (SR.ps_cells ps0) (APC.esub (PSO.v_wptr l) (PSO.v_wptr t))) as [[lo hi]|] eqn:HR; [|discriminate D].
    destruct (Z.eqb_spec lo 1) as [->|]; [|discriminate D]. destruct (Z.eqb_spec hi 1) as [->|]; [|discriminate D].
    assert (KN : know_ok (hl_segs L) E' (CCA.vis A1 m' M') (SR.ps_cells ps0)).
    { unfold know_ok. apply Forall_forall. intros X HX. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX). }
    pose proof (CX.range3_sound _ _ _ _ _ _ _ KN HR) as RG. change (bv_unsigned (edenot E' (APC.esub (PSO.v_wptr l) (PSO.v_wptr t)))) with (CL5A.uv E' (APC.esub (PSO.v_wptr l) (PSO.v_wptr t))) in RG.
    rewrite uv_esub, (va_wptr _ _ _ VA), (tv_wptr _ _ _ _ TV1) in RG.
    pose proof (UVR E' (PSO.v_wptr l)) as R1'. set (x := CL5A.uv E' (PSO.v_wptr l)) in *. set (w := PSOI.wlo mw) in *.
    rewrite <- Zplus_mod_idemp_l. set (w' := w mod 2 ^ 64) in *.
    assert (WM : 0 <= w' < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    destruct (Z_le_gt_dec w' x) as [LE|GT].
    + rewrite Z.mod_small in RG by lia. rewrite Z.mod_small by lia. lia.
    + assert (E1x : (x - w') mod 2 ^ 64 = x - w' + 2 ^ 64).
      { rewrite <- (Z.mod_add (x - w') 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
      rewrite E1x in RG.
      assert (E2x : (w' + 1) mod 2 ^ 64 = w' + 1 - 2 ^ 64).
      { rewrite <- (Z.mod_add (w' + 1) (-1) (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
      rewrite E2x. lia.
  - rewrite (SF _ _ D), (va_wend _ _ _ VA). exact (tv_wend _ _ _ _ TV1).
  - rewrite (SF _ _ D), (va_size _ _ _ VA). exact (tv_size _ _ _ _ TV1).
  - rewrite (SF _ _ D), (va_bptr _ _ _ VA). exact (tv_bptr _ _ _ _ TV1).
Qed.

Lemma STRETCH : forall i c ps0 E1 R1 A1 M1 m1 E' R' M' m' mw ps1 code g1 t l,
  nth_error G.CPS i = Some c -> (2 <= i < PSO.NCUT)%nat ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> AAMB I i E1 A1 M1 m1 -> env_agree (CC.cp_nx c) E1 E' ->
  CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> PSOX.FLF I E1 ->
  PSOX.CORE I i E1 M1 mw ps1 code g1 ->
  PSO.pview (CC.cp_know c) = Some t -> PSO.pview (SR.ps_cells ps0) = Some l ->
  PSO.view_ok (CC.cp_nx c) (CC.cp_know c) t = true ->
  PSO.frame_same (PSO.mkdelta (SR.ps_cells ps0) t l) = true ->
  PSO.size_ok c (SR.ps_cells ps0) l (PSO.mkdelta (SR.ps_cells ps0) t l) = true ->
  (PSO.has_bufbyte (CC.cp_F c) = false \/ PSO.has (SR.ps_cells ps0) (KWord (SA (APC.eadd (PSO.v_size l) (PSO.v_bptr l)) 0) 1 (ELit 0)) = true) ->
  (PSO.has (SR.ps_cells ps0) (KWord (SA PE 213) 1 (ELit 1)) = true \/ existsb (PSO.region_eqb (PE, 200, ELit 16)) (CC.cp_F c) = false) ->
  forall st2 sst2 nst2 (more2 done2 : bool) w2,
  Z_to_bv 8 (CL5A.uv E' (PSO.v_st l)) = Z_to_bv 8 st2 -> Z_to_bv 8 (CL5A.uv E' (PSO.v_sst l)) = Z_to_bv 8 sst2 ->
  Z_to_bv 8 (CL5A.uv E' (PSO.v_nst l)) = Z_to_bv 8 nst2 ->
  Z_to_bv 8 (CL5A.uv E' (PSO.v_more l)) = Z_to_bv 8 (PML.b2z more2) -> Z_to_bv 8 (CL5A.uv E' (PSO.v_done l)) = Z_to_bv 8 (PML.b2z done2) ->
  PSOI.wlo w2 = CL5A.uv E' (PSO.v_wptr l) -> PSOI.whi w2 = PSOI.whi mw -> match w2 with Some (p, e) => p <= e | None => mw = None end ->
  exists buf2, MEM M' w2 (ps_upd ps1 st2 sst2 nst2 more2 done2 buf2 w2) code g1 /\
    (PSO.d_size (PSO.mkdelta (SR.ps_cells ps0) t l) = PSO.Same -> length buf2 = length (PML.ps_buf ps1) /\ (PSO.has_bufbyte (CC.cp_F c) = false -> buf2 = PML.ps_buf ps1)) /\
    (PSO.d_size (PSO.mkdelta (SR.ps_cells ps0) t l) <> PSO.Same -> buf2 = []).
Proof.
  intros i c ps0 E1 R1 A1 M1 m1 E' R' M' m' mw ps1 code g1 t l Hci Hi HAt HA Hag HLF HFL CO Ht Hl HVt HFS HSZ HTERM H213
         st2 sst2 nst2 more2 done2 w2 HST HSST HNST HMO HDO HWP HWE HW.
  pose proof (STRETCH_same i c ps0 E1 R1 A1 M1 m1 E' R' M' m' mw ps1 code g1 t l Hci Hi HAt HA Hag HLF CO Ht HVt) as SMF.
  set (cells := SR.ps_cells ps0) in *. set (d := PSO.mkdelta cells t l) in *. set (hb := PSO.has_bufbyte (CC.cp_F c)) in *.
  pose proof (GEO i E1 A1 M1 m1 Hi HA) as GE. destruct (g_bc _ _ _ GE) as (GB0 & GB16 & GB1 & GB2). destruct (g_sc _ _ _ GE) as (GS0 & GS16 & GS1 & GS2).
  destruct (g_P _ _ _ GE) as (GP0 & GP1 & GE0 & GE1).
  pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6 i c E1 E' A1 M1 m1 HA (G.NF_le i c Hci) Hag) as HagE'.
  pose_U I. assert (W10' : bv_unsigned (ev E' 10) = P) by (rewrite <- (proj1 HagE' 10%nat ltac:(unfold GT.NF, Cut_psome_cboth_T.NF; clear; lia)); exact U10).
  pose proof (CBA.amb_off L ar C HI HIok (LYB I) GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6 i E1 A1 M1 m1 HA) as Hoff1.
  assert (Hoff' : H_off_segments (hl_segs L) (ahid A1 m')) by (rewrite (L5LZ.sbm_ahid A1 m1 m' (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)); exact Hoff1).
  assert (HKL : forall X, In X cells -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X) by (intros X HX; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX)).
  pose proof (PSOLK.VIEW_RD I E' A1 m' M' cells l Hoff' W10' HKL Hl) as VRl.
  pose proof (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF) as GROW.
  pose proof (PSOX.c_pa _ _ _ _ _ _ _ _ CO) as PA1.
  pose proof (PSOX.c_blk _ _ _ _ _ _ _ _ CO) as CB. unfold PML.ps_blocks in CB. injection CB as Ebp Ebc Esb Esc.
  destruct (PA_213 M1 _ PA1) as (Z213 & DEF1).
  destruct (PA_buf M1 _ PA1) as (BY1 & TM1 & LT1). cbn [PML.ps_set_win PML.ps_buf PML.ps_bcap PML.ps_bptr] in BY1, TM1, LT1.
  assert (AG : forall a, SG i E1 hb a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (exact (SG_ag i c ps0 E1 A1 M1 m1 E' R' M' m' Hi Hci HA HFL Hag HLF)).
  unfold PSO.frame_same in HFS. apply andb_prop in HFS as [HFS _]. apply andb_prop in HFS as [HFS _]. apply andb_prop in HFS as [HFS _].
  apply andb_prop in HFS as [HFS _]. apply andb_prop in HFS as [_ HBPs].
  pose proof (s_bptr _ _ _ _ _ _ SMF (proj1 (is_same_eq _) HBPs)) as BPl. fold cells d in BPl.

  assert (BUF : exists buf2, L5.bytes_at (hl_segs L) M' (PML.ps_bptr ps1) buf2 /\ L5.u8_at (hl_segs L) M' (PML.ps_bptr ps1 + Z.of_nat (length buf2)) 0 /\
                  Z.of_nat (length buf2) < PML.ps_bcap ps1 /\ L5.u64_at (hl_segs L) M' (P + 232) (Z.of_nat (length buf2)) /\
                  (PSO.d_size d = PSO.Same -> length buf2 = length (PML.ps_buf ps1) /\ (hb = false -> buf2 = PML.ps_buf ps1)) /\ (PSO.d_size d <> PSO.Same -> buf2 = [])).
  { unfold PSO.size_ok in HSZ. fold d in HSZ. destruct (PSO.d_size d) as [|z|v|] eqn:DS.
    - pose proof (s_size _ _ _ _ _ _ SMF DS) as SZl. pose proof (PSOLK.vr_size _ _ _ _ VRl) as C232. fold cells d in SZl. rewrite SZl in C232.
      destruct hb eqn:HB.
      + destruct (defined_bytes_r (hl_segs L) M' (PML.ps_bptr ps1) (length (PML.ps_buf ps1))) as (buf2 & Hlen & HBY & _).
        { intros k Hk. apply GROW. rewrite Ebp. apply (g_bdef _ _ _ GE). rewrite <- Ebc. clear - Hk LT1. lia. }
        exists buf2. rewrite Hlen. split; [exact HBY|]. split.
        * destruct HTERM as [HTERM|HTERM]; [discriminate HTERM|].
          apply CC.has_cell_In in HTERM. pose proof (HKL _ HTERM) as K0.
          pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ _ K0 eq_refl) as U0. apply (CL5A.u8_full (hl_segs L) _ Hoff') in U0.
          unfold estart in U0. cbn [a_base a_off] in U0.
          change (bv_unsigned (edenot E' (APC.eadd (PSO.v_size l) (PSO.v_bptr l)))) with (CL5A.uv E' (APC.eadd (PSO.v_size l) (PSO.v_bptr l))) in U0.
          rewrite uv_eadd, SZl, BPl in U0. rewrite uv_lit in U0 by (clear; lia). rewrite Z.add_0_r in U0.
          rewrite Z.mod_small in U0 by (clear - Ebp Ebc LT1 GB1 GB2; lia).
          replace (PML.ps_bptr ps1 + Z.of_nat (length (PML.ps_buf ps1))) with (Z.of_nat (length (PML.ps_buf ps1)) + PML.ps_bptr ps1) by (clear; lia). exact U0.
        * split; [exact LT1|]. split; [exact C232|]. split; [intros _; split; [reflexivity | intros X; discriminate X] | intros X; exfalso; apply X; reflexivity].
      + exists (PML.ps_buf ps1). split.
        * apply (PTA.bytes_ag (hl_segs L) M1 M' (SG i E1 false) AG); [|exact BY1]. split; [clear - Ebp GB1; lia|]. split; [clear - Ebp Ebc GB1 GB2 LT1; lia|].
          intros a Ha. apply (SG_B i E1 M1 false GE); [rewrite <- Ebp, <- Ebc; clear - Ha LT1; lia | intros X; discriminate X].
        * split.
          { apply (PTA.u8_ag (hl_segs L) M1 M' (SG i E1 false) AG); [|exact TM1]. split; [clear - Ebp GB1; lia|]. split; [clear - Ebp Ebc GB1 GB2 LT1; lia|].
            intros a Ha. apply (SG_B i E1 M1 false GE); [rewrite <- Ebp, <- Ebc; clear - Ha LT1; lia | intros X; discriminate X]. }
          split; [exact LT1|]. split; [exact C232|]. split; [intros _; split; [reflexivity | intros _; reflexivity] | intros X; exfalso; apply X; reflexivity].
    - destruct z as [|zp|zn]; try discriminate HSZ.
      assert (VS0 : PSO.v_size l = ELit 0).
      { unfold d, PSO.mkdelta in DS. cbn [PSO.d_size] in DS. exact (fdelta_lit _ _ _ DS). }
      pose proof (PSOLK.vr_size _ _ _ _ VRl) as C232. rewrite VS0, uv_lit in C232 by (clear; lia).
      apply CC.has_cell_In in HSZ. pose proof (HKL _ HSZ) as K0.
      pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ _ K0 eq_refl) as U0. apply (CL5A.u8_full (hl_segs L) _ Hoff') in U0.
      unfold estart in U0. cbn [a_base a_off] in U0. change (bv_unsigned (edenot E' (PSO.v_bptr l))) with (CL5A.uv E' (PSO.v_bptr l)) in U0.
      rewrite BPl, uv_lit, Z.add_0_r in U0 by (clear; lia).
      exists []. split; [intros k Hk; cbn in Hk; lia|]. cbn [length]. rewrite Z.add_0_r. split; [exact U0|]. split; [clear - Ebc GB0; lia|].
      split; [exact C232|]. split; [intros X; discriminate X | intros _; reflexivity].
    - discriminate HSZ.
    - discriminate HSZ. }
  destruct BUF as (buf2 & BY2 & TM2 & LT2 & SZ2 & BS & BN). exists buf2. split; [|split; [exact BS | exact BN]].

  assert (Z213' : L5.u8_at (hl_segs L) M' (P + 213) 1).
  { destruct H213 as [H|H].
    - apply CC.has_cell_In in H. pose proof (RD8 I E' A1 m' M' 213 (ELit 1) Hoff' W10' (HKL _ H)) as X. rewrite uv_lit in X by (clear; lia). exact X.
    - assert (AG213 : forall a, a = P + 213 -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a ->. apply (AGX i c ps0 E1 A1 M1 m1 E' R' M' m' Hi Hci HA HFL Hag HLF (P + 213)).
        - left. clear; lia.
        - intros o n Hr Hin. pose proof (preg_menu i c Hci o n Hr) as Hm. cbn [In] in Hm.
          destruct Hm as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[]]]]]]]]; injection Hx as <- <-; [clear - Hin; lia | | clear - Hin; lia | clear - Hin; lia | clear - Hin; lia | clear - Hin; lia | clear - Hin; lia].
          assert (X : existsb (PSO.region_eqb (PE, 200, ELit 16)) (CC.cp_F c) = true) by (apply existsb_exists; exists (PE, 200, ELit 16); split; [exact Hr | vm_compute; reflexivity]).
          rewrite X in H. discriminate H.
        - intros _ X. apply (g_Pb _ _ _ GE). rewrite <- X. clear; lia. }
      apply (PTA.u8_ag (hl_segs L) M1 M' (fun a => a = P + 213) AG213); [|exact Z213]. split; [clear - GP0; lia|]. split; [clear - GP1; lia|]. intros a Ha. clear - Ha. lia. }
  constructor.
  - unfold ps_upd.
    apply (PSOLK.PA_UPD I M1 M' (SG i E1 hb) AG ps1 mw w2 st2 sst2 nst2 more2 done2 buf2).
    + split; [clear - GP0; lia|]. split; [clear - GP1; lia|]. intros a Ha. apply (SG_P i E1 M1 hb GE); [clear - Ha; lia | unfold FPC; clear - Ha; lia].
    + split; [clear - GP0; lia|]. split; [clear - GP1; lia|]. intros a Ha. apply (SG_P i E1 M1 hb GE); [clear - Ha; lia | unfold FPC; clear - Ha; lia].
    + split; [clear - GP0; lia|]. split; [clear - GP1; lia|]. intros a Ha. apply (SG_P i E1 M1 hb GE); [clear - Ha; lia | unfold FPC; clear - Ha; lia].
    + split; [clear - GP0; lia|]. split; [clear - GP1; lia|]. intros a Ha. apply (SG_P i E1 M1 hb GE); [clear - Ha; lia | unfold FPC; clear - Ha; lia].
    + split; [clear - GP0; lia|]. split; [clear - GP1; lia|]. intros a Ha. apply (SG_P i E1 M1 hb GE); [clear - Ha; lia | unfold FPC; clear - Ha; lia].
    + rewrite Esb, Esc. split; [clear - GS1; lia|]. split; [clear - GS1 GS2; lia|]. intros a Ha. exact (SG_S i E1 M1 hb GE a Ha).
    + exact PA1.
    + exact HWE.
    + exact HW.
    + rewrite HWP. exact (PSOLK.vr_wptr _ _ _ _ VRl).
    + pose proof (PSOLK.vr_st _ _ _ _ VRl) as X. unfold L5.u8_at in X |- *. rewrite <- HST. exact X.
    + pose proof (PSOLK.vr_sst _ _ _ _ VRl) as X. unfold L5.u8_at in X |- *. rewrite <- HSST. exact X.
    + pose proof (PSOLK.vr_nst _ _ _ _ VRl) as X. unfold L5.u8_at in X |- *. rewrite <- HNST. exact X.
    + pose proof (PSOLK.vr_more _ _ _ _ VRl) as X. unfold L5.u8_at in X |- *. rewrite <- HMO. exact X.
    + pose proof (PSOLK.vr_done _ _ _ _ VRl) as X. unfold L5.u8_at in X |- *. rewrite <- HDO. exact X.
    + exact Z213'.
    + exact SZ2.
    + exact BY2.
    + exact TM2.
    + exact LT2.
    + intros k Hk. apply GROW. exact (DEF1 k Hk).
  - pose proof (PSOX.c_sh _ _ _ _ _ _ _ _ CO) as SH1.
    pose proof (PTB.pa_slen L IC _ _ _ PA1) as SL2. cbn [PML.ps_set_win PML.ps_stack PML.ps_scap] in SL2.
    assert (X : PMLA.parser_sh M' ps1).
    { apply (PTA.parser_sh_ag M1 M' (SG i E1 hb) AG ps1); [clear - Ebc GB0; lia | clear - SL2; lia | rewrite Ebp; exact (CHA.mod8_of_16 _ GB16) | rewrite Esb; exact (CHA.mod8_of_16 _ GS16)
        | intros a Ha; apply (SG_SH i E1 M1 hb GE); left; rewrite <- Ebp, <- Ebc; exact Ha | intros a Ha; apply (SG_SH i E1 M1 hb GE); right; rewrite <- Esb, <- Esc; exact Ha | exact SH1]. }
    unfold PMLA.parser_sh in X |- *. exact X.
  - apply (PTA.ec_at_ag (hl_segs L) IC M1 M' (SG i E1 hb) AG E code); [|exact (PSOX.c_ec _ _ _ _ _ _ _ _ CO)].
    split; [clear - GE0; lia|]. split; [clear - GE1; lia|]. intros a Ha. exact (SG_E i E1 M1 hb GE a Ha).
  - assert (HG : g1 <> PML.LS0) by (destruct (PSOX.c_g _ _ _ _ _ _ _ _ CO) as [-> | [-> _]]; [exact (PSOI.iHG I) | apply PSSC.regJ_nz]).
    apply (LS_mv I g1 M1 M'); [intros a Ha; apply AG; exact (SG_ST i E1 M1 hb GE a Ha) | exact HG | exact (PSOX.c_ls _ _ _ _ _ _ _ _ CO)].
Qed.

End S.
End PSOST.
