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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsKitA PsoInstCB PsoSemA PsoSemCA PsoKnCB ParseSomeChkCB PsoBaseCB PsoAuxCB PsoXiCB PsoLinkCB PsoFrmCB PsoExitCB PsoStCB PsoCkCB PsoCallCB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_cboth.

Module PSOVIS.

Definition vis_arg (pc : Z) (a1 : expr) : bool :=
  match a1 with ELit z => (Z.leb 0 z && Z.ltb z 256 && (negb (Z.eqb pc VBOOL) || Z.eqb z 0 || Z.eqb z 1))%bool | _ => false end.
Definition vis_leaf (pc : Z) (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (PSO.kind_eqb (PSO.kind_of i) PSO.KCsl && PSOCALL.bshz_ok i && expr_eqb (PSO.reg_of ps 10) (EVar 11) && vis_arg pc (PSO.reg_of ps 11)
   && PSOCALL.more1 c (SR.ps_cells ps))%bool.
Definition vs_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TOther pc => (negb (Z.eqb pc VNULL || Z.eqb pc VBOOL) || PSO.dead_chk i ps pc || vis_leaf pc i c ps)%bool | CC.TGoto _ _ => true end.
Lemma VS_all : CH2.leaves_all G.CPS G.TAGS vs_chk = true. Proof. vmc_refl. Qed.
Lemma VS : forall pc i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> (pc = VNULL \/ pc = VBOOL) -> PSO.dead_chk i ps0 pc = false ->
  vis_leaf pc i c ps0 = true.
Proof.
  intros pc i c k ps0 IL Hpc Hd. pose proof (CH2.leaves_all_sound _ _ _ VS_all _ _ _ _ _ IL) as X. cbn [vs_chk] in X. rewrite Hd in X.
  assert (HB : (Z.eqb pc VNULL || Z.eqb pc VBOOL)%bool = true) by (destruct Hpc as [-> | ->]; reflexivity). rewrite HB in X. exact X.
Qed.
Lemma vis_arg_rng : forall pc z, vis_arg pc (ELit z) = true -> 0 <= z < 256.
Proof.
  intros pc z X. unfold vis_arg in X. apply andb_prop in X as [X _]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
Qed.
Lemma vis_arg_bool : forall z, vis_arg VBOOL (ELit z) = true -> z = 0 \/ z = 1.
Proof.
  intros z X. unfold vis_arg in X. rewrite Z.eqb_refl in X. cbn [negb orb] in X. apply andb_prop in X as [_ X].
  apply orb_prop in X as [X|X]; apply Z.eqb_eq in X; [left | right]; exact X.
Qed.

Section V.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation LK := (PSOI.iLK I).   Local Abbreviation A := (PSOI.iA I).
Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).      Local Abbreviation V := (PSOI.iV I).     Local Abbreviation E := (PSOI.iE I).
Local Abbreviation B := (PSOI.iB I).     Local Abbreviation M := (PSOI.iM I).      Local Abbreviation model := (PSOI.imodel I). Local Abbreviation K := (PSOI.iK I).
Local Abbreviation HIok := (PSOI.iHIok I).
Local Abbreviation E0 := (PSOI.E0 I).      Local Abbreviation WW := (WW I).            Local Abbreviation Wo := (Wo I).         Local Abbreviation Cred := (PSOX.Cred I). Local Abbreviation XI := (PSOX.XI I).
Local Abbreviation bptrI := (PSOX.bptrI).  Local Abbreviation bcapI := (PSOX.bcapI). Local Abbreviation sbI := (PSOX.sbI). Local Abbreviation scapI := (PSOX.scapI).

Lemma GEO_EV : forall i E1 A1 M1 m1 a, (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 ->
  PSOCK.SUPPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a \/ (E <= a < E + 16) \/ STATIC a -> ~ (V + 8 <= a < V + 48).
Proof.
  intros i E1 A1 M1 m1 a Hi HA Ha. pose_facts I.
  pose proof (PSOI.iAP1 I) as AP1. pose proof (PSOI.iAP3 I) as AP3. unfold PMLA.apart in AP1, AP3. unfold hid in VR5.
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (HcB & _ & _ & _ & _ & _ & _ & _ & _ & _ & (crX & LKX & HHX & _)).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHX) as WFX.
  destruct Vfr as (fV & HfV & FV1 & FV2).
  assert (BK : forall u n, In (u, n) ([(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] ++ LBo) ->
             0 <= u /\ 0 < n /\ u + n <= 2 ^ 47 /\ (u + n <= ff_addr fV \/ ff_addr fV + ff_bytes (ff_class fV) <= u)).
  { intros u n Hun. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFX (u, n) Hun) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _ & _ & _ & Dfap).
    cbn [fst snd] in *. pose proof (Dfap fV ltac:(apply in_or_app; left; right; exact HfV)) as DF.
    split; [exact D5|]. split; [exact D3|]. split; [exact D7 | exact DF]. }
  intros HV.
  destruct Ha as [[Ha|[Ha|[Ha|[Ha|[Ha|(u & n & Hun & Ha)]]]]]|[Ha|Ha]].
  - clear - Ha HV AP1. lia.
  - destruct (BK _ _ ltac:(left; reflexivity)) as (B0 & B1 & B2 & B3). clear - Ha HV B3 FV1 FV2. lia.
  - destruct (BK _ _ ltac:(left; reflexivity)) as (B0 & B1 & B2 & B3). pose proof (SHR _ _ a B0 B1 B2 Ha) as RG. clear - RG HV VR5. lia.
  - destruct (BK _ _ ltac:(right; left; reflexivity)) as (B0 & B1 & B2 & B3). clear - Ha HV B3 FV1 FV2. lia.
  - destruct (BK _ _ ltac:(right; left; reflexivity)) as (B0 & B1 & B2 & B3). pose proof (SHR _ _ a B0 B1 B2 Ha) as RG. clear - RG HV VR5. lia.
  - destruct (BK u n ltac:(right; right; exact Hun)) as (B0 & B1 & B2 & B3). destruct Ha as [Ha|Ha].
    + clear - Ha HV B3 FV1 FV2. lia.
    + pose proof (SHR _ _ a B0 B1 B2 Ha) as RG. clear - RG HV VR5. lia.
  - clear - Ha HV AP3. lia.
  - pose proof (STATIC_lo I a Ha) as RG. clear - RG HV VR1 FSLO. lia.
Qed.

Lemma AGX_V : forall i E1 A1 M1 m1 (Mx M2 : mem) LBk, (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 ->
  CHA.ahpres L ar LBk (CHA.curF FF sp PSO.FFS i E1) (sp + PSO.CSP) PMSA.VIS_SCR [(V + 8, 40)] Mx M2 -> incl (CHA.curB LBo G.BLS i E1) LBk ->
  forall a, PSOCK.SUPPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a \/ (E <= a < E + 16) \/ STATIC a -> M2 (Z_to_bv 64 a) = Mx (Z_to_bv 64 a).
Proof.
  intros i E1 A1 M1 m1 Mx M2 LBk Hi HA HP Hinc a Ha.
  apply (PSOCK.SUPP_AHP I i E1 A1 M1 m1 Mx M2 LBk PMSA.VIS_SCR [(V + 8, 40)] Hi HA HP Hinc ltac:(unfold PMSA.VIS_SCR; clear; lia) a).
  - destruct Ha as [Ha|[Ha|Ha]]; [exact (PSOCK.SUPPP_SUPP I _ _ _ _ a Ha) | right; left; exact Ha | do 6 right; left; exact Ha].
  - intros r [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (GEO_EV i E1 A1 M1 m1 a Hi HA Ha ltac:(clear - Hin; lia)).
Qed.

Lemma CORE_VIS : forall i E1 A1 M1 m1 (Mx M2 : mem) LBk ps2 g1 LBx FFx LKx crx Ax Vx, (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 ->
  CHA.ahpres L ar LBk (CHA.curF FF sp PSO.FFS i E1) (sp + PSO.CSP) PMSA.VIS_SCR [(V + 8, 40)] Mx M2 -> incl (CHA.curB LBo G.BLS i E1) LBk ->
  ri_inv HI LBx FFx LKx crx Ax Mx Vx -> In (bptrI i E1, bcapI i E1) LBx -> In (sbI i E1, scapI i E1) LBx ->
  PSOX.CORE I i E1 Mx (PML.ps_win ps2) ps2 0 g1 -> PSOX.CORE I i E1 M2 (PML.ps_win ps2) ps2 0 g1.
Proof.
  intros i E1 A1 M1 m1 Mx M2 LBk ps2 g1 LBx FFx LKx crx Ax Vx Hi HA HP Hinc HHx INb INs CO.
  pose proof (AGX_V i E1 A1 M1 m1 Mx M2 LBk Hi HA HP Hinc) as AG.
  assert (HG : g1 <> PML.LS0) by (destruct (PSOX.c_g _ _ _ _ _ _ _ _ CO) as [-> | [-> _]]; [exact (PSOI.iHG I) | apply PSSC.regJ_nz]).
  pose_facts I.
  apply (PSOCK.CORE_mvx I i E1 Mx M2 (PML.ps_win ps2) ps2 0 g1 0 g1 LBx FFx LKx crx Ax Mx Vx HHx INb INs).
  - intros a Ha. exact (AG a (or_introl Ha)).
  - apply (PTA.ec_at_ag (hl_segs L) IC Mx M2 (fun a => E <= a < E + 16) (fun a Ha => AG a (or_intror (or_introl Ha))) E 0); [|exact (PSOX.c_ec _ _ _ _ _ _ _ _ CO)].
    split; [clear - Q3; lia|]. split; [clear - Q6; lia|]. intros x Hx. exact Hx.
  - exact (LS_mv I g1 Mx M2 (fun a Ha => AG a (or_intror (or_intror Ha))) HG (PSOX.c_ls _ _ _ _ _ _ _ _ CO)).
  - exact (PSOX.c_g _ _ _ _ _ _ _ _ CO).
  - exact CO.
Qed.

Lemma XI_VIS : forall j E2 (M2 : mem) ps g1 e, PSO.kind_of j = PSO.KVis -> PSOX.FLF I E2 ->
  PSOX.CORE I j E2 M2 (PML.ps_win ps) ps 0 g1 -> PMCUR.wf_c ps -> PML.ps_more ps = true -> PMCUR.ev_at (hl_segs L) M2 V e ->
  (e = PMCUR.EvNull \/ exists b, e = PMCUR.EvBool b) -> PSOX.XI_R I j E2 M2.
Proof.
  intros j E2 M2 ps g1 e HK HFL CO WF Hm HEV HE.
  constructor; try (intros _; exact HFL); try (intros Hk; exfalso; rewrite HK in Hk; first [discriminate Hk | destruct Hk as [Hk|Hk]; discriminate Hk]);
    try (intros pc0 Hk; exfalso; rewrite HK in Hk; discriminate Hk).
  intros _. exists ps, g1, e. split; [exact CO|]. split; [exact WF|]. split; [exact Hm|]. split; [exact HEV | exact HE].
Qed.

Section VG.
Variables (pc : Z) (xa : CAXA.xsumA) (xok : Z -> Prop) (evf : Z -> PMCUR.sevent).
Hypothesis Hxa : PSOK.xs_at pc = Some xa.
Hypothesis XSPEC : PMSA.visit_scalar_specA L ar HI IC pc xok evf.
Hypothesis XPC : pc = VNULL \/ pc = VBOOL.
Hypothesis XCAL : In pc PSOCK.PCALLEES.
Hypothesis XNS : pc <> PSTRING.
Hypothesis XNN : pc <> PNUMBER.
Hypothesis XRK : PSO.ret_kind pc = PSO.KVis.
Hypothesis XSCR : CAX.xs_scr (PSOK.x_of xa) = PMSA.VIS_SCR.
Hypothesis XNG : CAX.xs_ng (PSOK.x_of xa) = 0%nat.
Hypothesis XKEEP : forall regs BL, CAX.xs_keep (PSOK.x_of xa) regs BL = BL.
Hypothesis XWR : forall regs, CAX.xs_wregs (PSOK.x_of xa) regs = [(EVar 11, 8, ELit 40)].
Hypothesis XA0 : forall regs g, CAX.xs_a0 (PSOK.x_of xa) regs g = Some (ELit 1).
Hypothesis XBLK : forall regs cells g BLk, PSOK.blk_of xa regs cells g BLk = BLk.
Hypothesis XNEWS : forall regs cells g BLk, PSOK.news_of xa regs cells g BLk = PSOK.STATICS_ISH ++ PSOK.MEASNEWS cells ++ PSOK.BSHZ ++ PSOK.FLAGC cells.
Hypothesis XOK : forall z, vis_arg pc (ELit z) = true -> xok z.
Hypothesis XEV : forall z, xok z -> evf z = PMCUR.EvNull \/ exists b, evf z = PMCUR.EvBool b.

Lemma L_VG : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> PSO.call_chk i c k ps0 pc = true -> PSO.dead_chk i ps0 pc = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  intros i c k ps0 IL CHK HD. pose_facts I. pose_U I. pose proof (PSOI.VV I) as (_ & V4 & _).
  destruct (PSOCK.CALL_UNPACK pc xa i c k ps0 IL CHK HD Hxa) as (j & cj & ci & Hret & CU).
  destruct CU as [Hci Hcj Hpc HKj HND Hchk Hcsp Hblk HFj HPC].
  rewrite XSCR, XNG, XKEEP, XWR, XA0, XNEWS in Hchk. rewrite XKEEP, XBLK in Hblk.
  pose proof (VS pc i c k ps0 IL XPC HD) as SIDE. unfold vis_leaf in SIDE.
  apply andb_prop in SIDE as [SIDE Smore]. apply andb_prop in SIDE as [SIDE Sarg]. apply andb_prop in SIDE as [SIDE Sreg10]. apply andb_prop in SIDE as [Skind Sbshz].
  apply PSO.kind_eqb_eq in Skind. apply expr_eqb_eq in Sreg10. unfold PSOCALL.bshz_ok in Sbshz. apply expr_eqb_eq in Sbshz.
  destruct (PSO.reg_of ps0 11) as [z| | | | | | |] eqn:Sreg11; try discriminate Sarg.
  pose proof (XOK z Sarg) as HXOK. pose proof (vis_arg_rng pc z Sarg) as Z0.
  assert (HKj' : PSO.kind_of j = PSO.KVis) by (rewrite HKj, XRK; reflexivity).
  assert (Hck : PSO.curk (PSO.kind_of i) = false) by (rewrite Skind; reflexivity).
  pose proof (ge2_of_kind i c _ Hci Skind ltac:(discriminate)) as Hi.
  pose proof (ge2_of_kind j cj _ Hcj HKj' ltac:(discriminate)) as Hj.
  assert (Hfeq : CHA.frames_eqb (nth j PSO.FFS []) (nth i PSO.FFS []) = true) by (rewrite (ffs_i i Hi), (ffs_i j Hj); reflexivity).
  destruct (PSOCK.CK_NEWS pc i c k ps0 IL XCAL HD) as (SMEAS & SFLAG).
  destruct (PSO.pview (CC.cp_know c)) as [t|] eqn:Ht; [|unfold PSO.pre_chk in HPC; rewrite Ht in HPC; discriminate HPC].
  destruct (PSO.pview (SR.ps_cells ps0)) as [l|] eqn:Hl; [|unfold PSO.pre_chk in HPC; rewrite Ht, Hl in HPC; discriminate HPC].
  pose proof (PSOCALL.pclass_psame i c ps0 pc t l HPC XNS XNN Ht Hl) as HCL.
  intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI].
  pose proof (PSOX.xi_flf _ _ _ _ HXI (proj1 Hi)) as HFL.
  destruct (PSOCALL.SRC I i E1 A1 M1 m1 HXI ltac:(rewrite Skind; cbn [In]; tauto)) as (ps1 & g1 & CO & WF).
  destruct (PSOCK.PSAME I pc i c k ps0 E1 R1 A1 M1 m1 E' R' M' m' (PML.ps_win ps1) ps1 0 g1 t l IL XCAL HD HPC Ht Hl HCL Hi Hck HAt HA Hag HLF HFL CO eq_refl WF)
    as (ps2 & CL2 & WFL & PSF).
  assert (HM2 : PML.ps_more ps2 = true).
  { rewrite (PSOCK.pf_eq _ _ _ _ _ PSF). cbn [PSOST.ps_upd PML.ps_more]. unfold PSOCALL.more1 in Smore. rewrite Ht in Smore.
    destruct (PSOCK.more_pin c (SR.ps_cells ps0) t) as [zz|] eqn:Hz; [|discriminate Smore]. destruct zz as [|[| |]|]; try discriminate Smore.
    pose proof (PSOCK.pf_more _ _ _ _ _ PSF 1 Hz) as X. destruct (PML.ps_more ps1); [reflexivity | discriminate X]. }
  destruct (LEAFK I i c ps0 E1 A1 M1 m1 E' R' M' m' Hi Hci (PSOST.cpf_of i c Hci) HA Hag HLF) as (FZ & W65 & W60 & CELLS & REGS & _).
  assert (W11 : bv_unsigned (ev E' 11) = V) by (rewrite (FZ 11%nat ltac:(clear; lia)); exact U11).
  refine (CBA.callee_leaf L ar C HI HIok (LYI I) (LYR I) GT.NF E0 M model A LBo FF LK sp G.HDECL WW Wo G.BLS PSO.FFS Cred 6 (STKF I) SCRP NF32 U2 V4 (WINC I) (WOKo I) (PSOI.iHffrs I) (CRS_OKo I) (WRS_OK I) (IMG_OK I)
            G.CPS K PMSA.fp_ok (DEF0 I) S6 GT.SCELLS GT.GLO GT.GHI (SCOK I) (GOTOK I) XI (PSOI.iHKnil I)
            pc PMSA.VIS_SCR 0 (nth i G.BLS []) [(EVar 11, 8, ELit 40)] _ (Some (ELit 1)) 0 i c ps0 j cj ci Hcj Hchk Hpc Hfeq ltac:(rewrite (ffs_i i Hi); cbn; clear; lia)
            fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _).
  intros cr1 LK1 CF HH1 HLK1 HC1.
  destruct CF as [HAm HR Hreq HV HK' [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
  rewrite Hcsp in *.
  pose proof (PSOCK.akag_of I i E1 A1 M' m' HAm) as AK. pose proof (PSOCK.defg_of I i E1 A1 M' m' HAm) as DG.
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (HcB & HcF & _).
  pose proof (PSOX.c_pa _ _ _ _ _ _ _ _ CL2) as PA2. rewrite PSOX.set_win_self in PA2.
  pose proof (PSOX.c_blk _ _ _ _ _ _ _ _ CL2) as BK2. unfold PML.ps_blocks in BK2. injection BK2 as Ebp Ebc Esb Esc.
  eexists. eexists. split; [exact (XSPEC (CHA.curB LBo G.BLS i E1) (CHA.curF FF sp PSO.FFS i E1) LK1 cr1 A1 V z (sp + PSO.CSP) (CC.cp_pc cj))|].
  split.
  {
    split; [exact (REGS 10%nat (EVar 11) V (PSOCALL.reg_of_is ps0 10 (EVar 11) Sreg10 ltac:(discriminate)) W11)|].
    split; [exact (REGS 11%nat (ELit z) z (PSOCALL.reg_of_is ps0 11 (ELit z) Sreg11 ltac:(intros X; injection X; clear - Z0; lia))
                        ltac:(cbn [edenot]; rewrite u_lit64a; apply Z.mod_small; clear - Z0; lia))|].
    split; [exact HXOK|].
    split; [exact (PSOCK.VISAT I M' AK DG)|].
    split; [exact (PSOCK.FOBJ I M' (CHA.curF FF sp PSO.FFS i E1) V 48 AK (PSOI.iOV I) ltac:(rewrite HcF; intros f Hf; right; exact Hf) ltac:(clear; lia) ltac:(clear - VR6; lia))|].
    exact (PSOCK.STKSH I M' PMSA.VIS_SCR AK ltac:(unfold PMSA.VIS_SCR; clear; lia) ltac:(reflexivity) ltac:(unfold PMSA.VIS_SCR; clear; lia)). }

  intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0 & HEV & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  exists []. split; [reflexivity|]. cbv zeta.
  set (gx := CH2.ci_nx ci) in *. set (E2 := CH2.retEx E' gx [] R2).
  pose proof (CH2.retEx_agree E' gx [] R2 : env_agree gx E' E2) as Hag2. fold E2 in Hag2.
  destruct HV as (_ & _ & HV3 & _).
  assert (Hag12 : env_agree (CC.cp_nx c) E1 E2) by (eapply CC.env_agree_trans; [exact Hag | eapply CC.env_agree_le; [exact Hag2 | exact HV3]]).
  pose proof (PSOST.nx66 i c Hi Hci) as NX.
  destruct (PSOCALL.BLKEQ I i j c E1 E2 Hci ltac:(clear - Hi; lia) Hblk Hag12) as (QJ1 & QJ2 & QJ3 & QJ4 & QJB).
  split; [cbn [edenot]; exact Ha0|].
  split; [rewrite HdenB; unfold CHA.curB; apply incl_refl|].
  split.
  { intros w a [<-|[]] Hin. exists (EVar 11, 8, ELit 40). split; [left; reflexivity|]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
    unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite W11. rewrite u64_of_Z by (clear; lia). clear - Hin. lia. }
  split.
  { intros w a [<-|[]] Hin (_ & _ & HO). apply (HO (V + 8, 40)); [|exact Hin].
    unfold PsoBaseCB.WW, PMSA.W_parEc. apply in_or_app. right. left. reflexivity. }
  split; [rewrite QJB; exact HH2|].
  split; [unfold Cred, PSOX.Cred; rewrite QJ2, QJ4; exact HC1|].

  assert (CL3 : PSOX.CORE I i E1 M2 (PML.ps_win ps2) ps2 0 g1).
  { rewrite HcB, HcF in HH1.
    exact (CORE_VIS i E1 A1 M1 m1 M' M2 (CHA.curB LBo G.BLS i E1) ps2 g1 _ _ _ _ _ _ Hi HA HP (incl_refl _) HH1 (or_introl eq_refl) (or_intror (or_introl eq_refl)) CL2). }
  assert (CL4 : PSOX.CORE I j E2 M2 (PML.ps_win ps2) ps2 0 g1).
  { apply (PSOCK.CORE_RE I i j E1 E2 M2 _ ps2 0 g1 CL3); [rewrite HKj'; reflexivity | reflexivity | exact QJ1 | exact QJ2 | exact QJ3 | exact QJ4 | exact (PSOCK.U0RET i k j Hret)
      | intros _; rewrite Skind; reflexivity | intros _; rewrite Skind; reflexivity
      | intros _; eapply CC.env_agree_le; [exact Hag12 | clear - NX; lia]]. }
  assert (T65 : CL5A.uv E2 FE = CL5A.uv E1 FE) by (unfold CL5A.uv, FE, FEV; cbn [edenot]; rewrite <- (proj1 Hag12 65%nat) by (clear - NX; lia); reflexivity).
  assert (T60 : CL5A.uv E2 FLE = CL5A.uv E1 FLE) by (unfold CL5A.uv, FLE, FLV; cbn [edenot]; rewrite <- (proj1 Hag12 60%nat) by (clear - NX; lia); reflexivity).
  split.
  { apply (XI_VIS j E2 M2 ps2 g1 (evf z) HKj'); [| exact CL4 | exact WFL | exact HM2 | exact HEV | exact (XEV z HXOK)].
    unfold PSOX.FLF. rewrite T60. exact HFL. }

  intros X HX _.
  apply in_app_or in HX as [HX|HX]; [exact (proj1 (Forall_forall _ _) (PSOCK.NEWS_SI I E2 A2 m2 M2 _ _ _ _ HH2) X HX)|].
  apply in_app_or in HX as [HX|HX]; [exact (proj1 (Forall_forall _ _) (PSOCK.NEWS_KR I c ps0 E' R' A1 M1 m1 M' m' E2 _ _ HLF (CC.env_agree_le _ _ _ _ Hag2 HV3) SMEAS) X HX)|].
  apply in_app_or in HX as [HX|HX].
  { destruct HX as [<-|[]]. pose proof (PSOX.c_sh _ _ _ _ _ _ _ _ CL4) as [SHB _].
    apply (PSOCK.NEWS_BSHZ I E2 A2 m2 M2 _ _ _ _ (bptrI i E1) (bcapI i E1) HH2); [rewrite HcB; left; reflexivity | | | rewrite <- Ebp, <- Ebc; exact SHB].
    - unfold PSOX.bptrI in *. rewrite Sbshz in *. unfold CL5A.uv. cbn [edenot]. rewrite <- (proj1 Hag12 56%nat) by (clear - NX; lia). reflexivity.
    - rewrite <- Ebc. exact (PTB.pa_bcap L IC _ _ _ PA2). }
  unfold PSOK.FLAGC in HX. rewrite SFLAG in HX.
  assert (FLC : L5.u64_at (hl_segs L) M' (CL5A.uv E1 FE + 1016) (CL5A.uv E1 FLE)).
  { pose proof (cell_at_has _ _ _ _ _ SFLAG) as Hin. pose proof (CELLS _ Hin) as KF.
    pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (CL5A.uv E1 FE + 1016) KF ltac:(unfold estart; cbn [a_base a_off]; change (bv_unsigned (edenot E' (EVar 65))) with (CL5A.uv E' FE); rewrite W65; reflexivity)) as G0.
    pose proof (CBA.amb_off L ar C HI HIok (LYB I) GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6 i E1 A1 M1 m1 HA) as Hoff1.
    assert (Hoff : H_off_segments (hl_segs L) (ahid A1 m')) by (rewrite (L5LZ.sbm_ahid A1 m1 m' (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)); exact Hoff1).
    apply (CL5A.u64_full (hl_segs L) _ Hoff) in G0. change (CL5A.uv E' (EVar 60)) with (CL5A.uv E' FLE) in G0. rewrite W60 in G0. exact G0. }
  exact (proj1 (Forall_forall _ _) (PSOCK.NEWS_FLAGC I i E1 A1 M1 m1 E2 A2 m2 M' M2 m' _ _ _ _ _ _ Hi HA HFL HH1 HH2 FLC T65 T60) X HX).
Qed.
End VG.

Lemma L_VNULL : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther VNULL) -> PSO.call_chk i c k ps0 VNULL = true -> PSO.dead_chk i ps0 VNULL = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  exact (L_VG VNULL PSOK.XS_VNULL (fun _ => True) (fun _ => PMCUR.EvNull) eq_refl (PSOI.iVNULL I) (or_introl eq_refl)
           ltac:(unfold PSOCK.PCALLEES; cbn [In]; tauto) ltac:(discriminate) ltac:(discriminate) eq_refl eq_refl eq_refl (fun _ _ => eq_refl) (fun _ => eq_refl)
           (fun _ _ => eq_refl) (fun _ _ _ _ => eq_refl) (fun _ _ _ _ => eq_refl) (fun _ _ => Logic.I) (fun _ _ => or_introl eq_refl)).
Qed.
Lemma L_VBOOL : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther VBOOL) -> PSO.call_chk i c k ps0 VBOOL = true -> PSO.dead_chk i ps0 VBOOL = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  exact (L_VG VBOOL PSOK.XS_VBOOL (fun x => x = 0 \/ x = 1) (fun x => PMCUR.EvBool (Z.eqb x 1)) eq_refl (PSOI.iVBOOL I) (or_intror eq_refl)
           ltac:(unfold PSOCK.PCALLEES; cbn [In]; tauto) ltac:(discriminate) ltac:(discriminate) eq_refl eq_refl eq_refl (fun _ _ => eq_refl) (fun _ => eq_refl)
           (fun _ _ => eq_refl) (fun _ _ _ _ => eq_refl) (fun _ _ _ _ => eq_refl) vis_arg_bool (fun z _ => or_intror (ex_intro _ (Z.eqb z 1) eq_refl))).
Qed.
End V.
End PSOVIS.
