(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecs PmEncSpecs PmLibSpecsXA PmLibSpecsX PmLibSpecsW PmRef PmRefFacts PmRefXA PmLibSpecsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_psome_xboth_T Cut_psome_xboth_D Cut_psome_xboth.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA PtKitB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PsKitA XKitXA PsoInstXB PsoSemXB ParseSomeChkXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import PsoInstXBW PsoBaseXBW PsoXiXBW.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation RSEGS := Pm5PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_xboth.

(* [comment removed for export] *)
Lemma ffs_i : forall i, (2 <= i < PSO.NCUT)%nat -> nth i PSO.FFS [] = [PSO.FR].
Proof.
  intros i Hi. unfold PSO.FFS.
  assert (X : forallb (fun k => match nth k PSO.FFS [] with [f] => CHA.frames_eqb [f] [PSO.FR] | _ => false end) (seq 2 (PSO.NCUT - 2)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in X. specialize (X i ltac:(apply in_seq; clear - Hi; lia)). unfold PSO.FFS in X.
  destruct (nth i _ []) as [|f [|f2 r]]; try discriminate X. apply CHA.frames_eqb_eq in X. exact X.
Qed.
Lemma ffs_0 : nth 0 PSO.FFS [] = []. Proof. vm_compute. reflexivity. Qed.
Lemma ffs_1 : nth 1 PSO.FFS [] = []. Proof. vm_compute. reflexivity. Qed.
Lemma bls_i : forall i, (i < PSO.NCUT)%nat -> nth i G.BLS [] = [PSO.blk0 i; PSO.blk1 i].
Proof.
  intros i Hi.
  assert (X : forallb (fun k => match nth k G.BLS [] with [_; _] => true | _ => false end) (seq 0 PSO.NCUT) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in X. specialize (X i ltac:(apply in_seq; clear - Hi; lia)). unfold PSO.blk0, PSO.blk1.
  destruct (nth i G.BLS []) as [|b0 [|b1 [|b2 rr]]]; try discriminate X. reflexivity.
Qed.

Lemma len_cps : length G.CPS = PSO.NCUT. Proof. vm_compute. reflexivity. Qed.
Lemma blv_all : forallb (fun i => CH2.blocks_vars_lt (CC.cp_nx (nth i G.CPS CA.dummy_cp)) (nth i G.BLS [])) (seq 0 PSO.NCUT) = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma BLKAG : forall i c E1 E', nth_error G.CPS i = Some c -> env_agree (CC.cp_nx c) E1 E' ->
  PSOX.bptrI i E' = PSOX.bptrI i E1 /\ PSOX.bcapI i E' = PSOX.bcapI i E1 /\ PSOX.sbI i E' = PSOX.sbI i E1 /\ PSOX.scapI i E' = PSOX.scapI i E1.
Proof.
  intros i c E1 E' Hci Hag.
  assert (Hi : (i < PSO.NCUT)%nat) by (rewrite <- len_cps; apply nth_error_Some; rewrite Hci; discriminate).
  pose proof (proj1 (forallb_forall _ _) blv_all i ltac:(apply in_seq; clear - Hi; lia)) as X. cbv beta in X. rewrite (nth_error_nth _ _ CA.dummy_cp Hci) in X.
  pose proof (CH2.den_agree (CC.cp_nx c) E1 E' _ Hag X) as D. rewrite (bls_i i Hi) in D.
  unfold PSOX.bptrI, PSOX.bcapI, PSOX.sbI, PSOX.scapI, CL5A.uv. destruct (PSO.blk0 i) as [b0 c0]; destruct (PSO.blk1 i) as [b1 c1]. unfold CH2.den in D. cbn [map fst snd] in D |- *.
  injection D as D1 D2 D3 D4. rewrite D1, D2, D3, D4. repeat split; reflexivity.
Qed.
(* [comment removed for export] *)
Lemma kind01 : PSO.kind_of 0 = PSO.KEntry /\ PSO.kind_of 1 = PSO.KEntry. Proof. vm_compute. split; reflexivity. Qed.
Lemma ge2_of_kind : forall i c kd, nth_error G.CPS i = Some c -> PSO.kind_of i = kd -> kd <> PSO.KEntry -> (2 <= i < PSO.NCUT)%nat.
Proof.
  intros i c kd Hci Hk Hne. pose proof kind01 as [K0 K1].
  assert (Hi : (i < PSO.NCUT)%nat) by (rewrite <- len_cps; apply nth_error_Some; rewrite Hci; discriminate).
  split; [|exact Hi]. destruct i as [|[|i]]; [exfalso; apply Hne; rewrite <- Hk; exact K0 | exfalso; apply Hne; rewrite <- Hk; exact K1 | clear; lia].
Qed.

(* [comment removed for export] *)
Lemma u0_retire_all : forallb (fun i => negb (PSO.u0 i) || negb (PSO.kind_eqb (PSO.kind_of i) PSO.KRetx || PSO.kind_eqb (PSO.kind_of i) PSO.KSetsh))%bool (seq 0 PSO.NCUT) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u0_retire : forall i c, nth_error G.CPS i = Some c -> PSO.kind_of i = PSO.KRetx \/ PSO.kind_of i = PSO.KSetsh -> PSO.u0 i = false.
Proof.
  intros i c Hci Hk. assert (Hi : (i < PSO.NCUT)%nat) by (rewrite <- len_cps; apply nth_error_Some; rewrite Hci; discriminate).
  pose proof (proj1 (forallb_forall _ _) u0_retire_all i ltac:(apply in_seq; clear - Hi; lia)) as X. cbv beta in X.
  destruct (PSO.u0 i); [|reflexivity]. exfalso. cbn [negb orb] in X. destruct Hk as [Hk|Hk]; rewrite Hk in X; discriminate X.
Qed.

Section F.
Context {SCFG_P : ScfgP}.
Variable I : PSOIW.inst.
Local Abbreviation L := (PSOIW.iL I).     Local Abbreviation ar := (PSOIW.iar I).    Local Abbreviation C := (PSOIW.iC I).     Local Abbreviation HI := (PSOIW.iHI I).
Local Abbreviation LBo := (PSOIW.iLBo I). Local Abbreviation FF := (PSOIW.iFF I).    Local Abbreviation LK := (PSOIW.iLK I).   Local Abbreviation cr := (PSOIW.icr I).   Local Abbreviation A := (PSOIW.iA I).
Local Abbreviation sp := (PSOIW.isp I).   Local Abbreviation P := (PSOIW.iP I).      Local Abbreviation V := (PSOIW.iV I).     Local Abbreviation E := (PSOIW.iE I).     Local Abbreviation B := (PSOIW.iB I).
Local Abbreviation R := (PSOIW.iR I).     Local Abbreviation M := (PSOIW.iM I).      Local Abbreviation model := (PSOIW.imodel I).
Local Abbreviation HIok := (PSOIW.iHIok I). Local Abbreviation LAY := (PSOIW.iLAY I). Local Abbreviation HH := (PSOIW.iHH I).
Local Abbreviation E0 := (PSOIW.E0 I).      Local Abbreviation LB := (PSOIW.LB I).
Local Abbreviation WW := (PSOIW.WW I).       Local Abbreviation Cred := (PSOX.Cred I).      Local Abbreviation gx := (PSOIW.ig1 I).   Local Abbreviation LBV := (PSOIW.LBV I gx).
Local Abbreviation bptrI := (PSOX.bptrI).  Local Abbreviation bcapI := (PSOX.bcapI). Local Abbreviation sbI := (PSOX.sbI). Local Abbreviation scapI := (PSOX.scapI).

(* [comment removed for export] *)
Definition OKVt (M0c : mem) : Prop := CHV.okV L ar M LBo FF sp G.HDECL WW M0c.
Definition AAMBc (M0c : mem) := CHA.aamb L ar HI GT.NF E0 M0c model A LBV FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 11.
Definition AMBXc (M0c : mem) := CHA.ambX L ar HI GT.NF E0 M0c model A LBV FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 11 (PSOX.XI I).
Definition AAMB (i : nat) (E1 : env) (A1 : list (Z * Z)) (M1 : mem) (m1 : Model) : Prop := exists M0c, OKVt M0c /\ AAMBc M0c i E1 A1 M1 m1.

Definition AMBX (i : nat) (E1 : env) (A1 : list (Z * Z)) (M1 : mem) (m1 : Model) : Prop := exists M0c, OKVt M0c /\ AMBXc M0c i E1 A1 M1 m1.
Lemma OKV0 : OKVt M. Proof. pose_facts I. exact (CHV.okV_refl L ar M LBo FF sp G.HDECL WW (DEF0 I) S6). Qed.
Lemma AMBX_aamb : forall i E1 A1 M1 m1, AMBX i E1 A1 M1 m1 -> AAMB i E1 A1 M1 m1 /\ PSOX.XI I i E1 A1 M1 m1.
Proof. intros i E1 A1 M1 m1 (M0c & OKV & [HA HX]). split; [exists M0c; split; [exact OKV | exact HA] | exact HX]. Qed.
Lemma AMBX_intro : forall i E1 A1 M1 m1, AAMB i E1 A1 M1 m1 -> PSOX.XI I i E1 A1 M1 m1 -> AMBX i E1 A1 M1 m1.
Proof. intros i E1 A1 M1 m1 (M0c & OKV & HA) HX. exists M0c. split; [exact OKV | split; [exact HA | exact HX]]. Qed.
(* [comment removed for export] *)
Lemma DEF0V : forall M0c, OKVt M0c -> L5.defined M0c (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL). Proof. intros M0c OKV. exact (CHV.okV_def0 L ar M LBo FF sp G.HDECL WW M0c OKV). Qed.
Lemma DEFUPV : forall M0c, OKVt M0c -> L5.defined M0c sp (ar_stack_top ar - sp). Proof. intros M0c OKV. exact (CHV.okV_defup L ar M LBo FF sp G.HDECL WW M0c OKV). Qed.
Lemma WOKV : forall (w : L5.range) (a : Z), In w (Wo I) -> L5.in_rng w a ->
  0 <= a < 2 ^ 64 /\ aclientw L ar LBV FF sp (CH.hd_scr GT.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof. exact (CHV.Wo_okV L ar LBo FF sp G.HDECL (Wo I) PMES.eghost PMES.g_lbv (WOKo I) gx). Qed.
Lemma CRSV : forall rg : SGP.region, In rg (CH.hd_crs GT.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LBV FF sp GT.HDECL a).
Proof. exact (CHV.CRS_okV L ar GT.NF E0 LBo FF sp G.HDECL PMES.eghost PMES.g_lbv (CRS_OKo I) gx). Qed.
(* [comment removed for export] *)
Lemma IH_at : forall M0c mu, OKVt M0c -> CCA.IH (hl_segs L) G.CPS AMBX (PSOIW.iK I) PMSA.fp_ok mu -> CCA.IH (hl_segs L) G.CPS (AMBXc M0c) (PSOIW.iK I) PMSA.fp_ok mu.
Proof. intros M0c mu OKV H j cj fx2 E2 R2 A2 M2 model2 Hcj HAt HAmb HFP Hlt. exact (H j cj fx2 E2 R2 A2 M2 model2 Hcj HAt (ex_intro _ M0c (conj OKV HAmb)) HFP Hlt). Qed.
(* [comment removed for export] *)
Lemma leaf_ok_at : forall i c ps0, (forall M0c, OKVt M0c -> CCA.leaf_ok (hl_segs L) G.CPS (AMBXc M0c) (PSOIW.iK I) PMSA.fp_ok i c ps0) -> CCA.leaf_ok (hl_segs L) G.CPS AMBX (PSOIW.iK I) PMSA.fp_ok i c ps0.
Proof. intros i c ps0 H fx' E1 R1 A1 M1 m1 E' R' M' m' HAt (M0c & OKV & HAX) HFP Hag HLF HIH. exact (H M0c OKV fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF (IH_at M0c _ OKV HIH)). Qed.
(* [comment removed for export] *)
Lemma FRAME00 : forall i E1 A1 M1 m1, AAMB i E1 A1 M1 m1 ->
  (forall a, CHA.akept L ar LBo FF sp (CH.hd_scr G.HDECL) WW a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBo FF sp 0 a -> M (Z_to_bv 64 a) <> None -> M1 (Z_to_bv 64 a) <> None).
Proof.
  intros i E1 A1 M1 m1 (M0c & OKV & HA).
  exact (CHV.frame00 L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS 11 PMES.eghost PMES.g_lbv (fun g => PSOX.Cred (PSOIW.setg I g)) gx M0c i E1 A1 M1 m1 OKV HA).
Qed.
(* [comment removed for export] *)
Definition LEAF (pc : Z) : Prop := forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> CCA.leaf_ok (hl_segs L) G.CPS AMBX (PSOIW.iK I) PMSA.fp_ok i c ps0.

(* [comment removed for export] *)
Lemma FRM : forall i E1 A1 M1 m1, (2 <= i < PSO.NCUT)%nat -> AAMB i E1 A1 M1 m1 ->
  let F := CL5A.uv E1 FE in let ob := [(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] in
  CHA.curB LBV G.BLS i E1 = ob ++ LBV /\ CHA.curF FF sp PSO.FFS i E1 = (F, 4, sp + PSO.CSP + 32) :: FF /\ env_agree GT.NF E0 E1 /\
  0 <= F /\ F + 1024 <= 140737488355328 /\ F mod 64 = 0 /\ (F + 1024 <= 2147446784 \/ 17594333495296 <= F) /\ ar_fs ar <= F /\ F + 1024 <= ar_fs ar + 11571200 /\ fframes_apart F 1024 FF /\
  (exists crX LKX, ri_inv HI (ob ++ LBV) ((F, 4, sp + PSO.CSP + 32) :: FF) LKX crX A1 M1 (vml_of m1) /\ Cred i E1 crX).
Proof.
  intros i E1 A1 M1 m1 Hi (M0c & OKV & HA). cbv zeta.
  pose proof HA as (_ & _ & _ & HagE & (cra & LKa & HHa & _ & HCa & _) & _).
  assert (HcB : CHA.curB LBV G.BLS i E1 = [(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] ++ LBV).
  { unfold CHA.curB. rewrite (bls_i i ltac:(clear - Hi; lia)). unfold CH2.den, PSOX.bptrI, PSOX.bcapI, PSOX.sbI, PSOX.scapI, CL5A.uv. cbn [map fst snd app].
    destruct (PSO.blk0 i) as [b0 c0]; destruct (PSO.blk1 i) as [b1 c1]; reflexivity. }
  assert (HcF : CHA.curF FF sp PSO.FFS i E1 = (CL5A.uv E1 FE, 4, sp + PSO.CSP + 32) :: FF) by (unfold CHA.curF; rewrite (ffs_i i Hi); reflexivity).
  rewrite HcB, HcF in HHa.
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHa) as WFa. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFa) as RFa.
  destruct (CHA.rf_frm _ _ _ _ RFa _ (or_introl eq_refl)) as (G1 & G2 & G3 & _). unfold ff_addr, ff_class in G1, G2, G3. cbn [fst snd] in G1, G2, G3. change (ff_bytes 4) with 1024 in G2.
  destruct (CHA.rf_fs _ _ _ _ RFa) as ((G0 & G4 & G5) & _). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
  destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WFa _ (or_introl eq_refl)) as (_ & _ & _ & _ & _ & FAP). cbn [ff_addr ff_class fst snd ff_remove] in FAP. rewrite Z.eqb_refl in FAP. change (ff_bytes 4) with 1024 in FAP.
  split; [exact HcB|]. split; [exact HcF|]. split; [exact HagE|]. split; [clear - G0 G1; lia|]. split; [clear - G2 G5; lia|]. split; [exact G3|].
  split; [clear - G1 G2 G4; lia|]. split; [exact G1|]. split; [exact G2|]. split; [intros f Hf; apply FAP; apply in_or_app; left; exact Hf|]. exists cra, LKa. split; [exact HHa | exact HCa].
Qed.

(* [comment removed for export] *)
Definition outU (Fr : list SGP.region) (E' : env) (bp : Z) (a : Z) : Prop :=
  let F := CL5A.uv E' FE in let fl := CL5A.uv E' FLE in
  (a < sp - SCR \/ sp <= a) /\ ~ (F <= a < F + 24) /\ ~ (F + 32 <= a < F + 1016) /\ ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 128) /\
  ~ (P + 148 <= a < P + 192) /\ ~ (P + 200 <= a < P + 216) /\ ~ (P + 220 <= a < P + 224) /\ ~ (P + 232 <= a < P + 240) /\ a <> fl /\
  (PSO.has_bufbyte Fr = true -> a <> bp).   (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bvar_all : forallb (fun k => match fst (PSO.blk0 k) with EVar v => negb (Nat.eqb v 2) | _ => false end) (seq 0 PSO.NCUT) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bvar_i : forall i, (i < PSO.NCUT)%nat -> exists v, fst (PSO.blk0 i) = EVar v /\ v <> 2%nat.
Proof.
  intros i Hi. pose proof (proj1 (forallb_forall _ _) bvar_all i ltac:(apply in_seq; clear - Hi; lia)) as X. cbv beta in X.
  destruct (fst (PSO.blk0 i)) as [z|v|op a b|op a b|op a b|op a b|sx lo n e|sx k j n]; try discriminate X. exists v. split; [reflexivity|]. apply negb_true_iff, Nat.eqb_neq in X. exact X.
Qed.
(* [comment removed for export] *)
Lemma LEAFK : forall i c ps0 E1 A1 M1 m1 E' R' M' m', (2 <= i < PSO.NCUT)%nat -> nth_error G.CPS i = Some c -> PSO.cpf_ok i (CC.cp_F c) = true ->
  AAMB i E1 A1 M1 m1 -> env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  (forall k, (k < 40)%nat -> ev E' k = ev E0 k) /\ CL5A.uv E' FE = CL5A.uv E1 FE /\ CL5A.uv E' FLE = CL5A.uv E1 FLE
  /\ (forall X0, In X0 (SR.ps_cells ps0) -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0)
  /\ (forall (q : nat) (e0 : expr) (z : Z), CL.ps_reg_is ps0 q e0 = true -> bv_unsigned (edenot E' e0) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z)
  /\ (forall a, 0 <= a < 2 ^ 64 -> outU (CC.cp_F c) E' (CL5A.uv E' (fst (PSO.blk0 i))) a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
Proof.
  intros i c ps0 E1 A1 M1 m1 E' R' M' m' Hi Hci CF (M0c & OKV & HA) Hag HLF.
  pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M0c model A LBV FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 11 i c E1 E' A1 M1 m1 HA (G.NF_le i c Hci) Hag) as HagE'.
  assert (NX : (66 <= CC.cp_nx c)%nat).
  { assert (X : forallb (fun k => Nat.leb 66 (CC.cp_nx (nth k G.CPS CA.dummy_cp))) (seq 2 (PSO.NCUT - 2)) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in X. specialize (X i ltac:(apply in_seq; clear - Hi; lia)). apply Nat.leb_le in X. rewrite (nth_error_nth _ _ CA.dummy_cp Hci) in X. exact X. }
  assert (FZ : forall k, (k < 40)%nat -> ev E' k = ev E0 k) by (intros k Hk; symmetry; apply (proj1 HagE'); unfold GT.NF, Cut_psome_xboth_T.NF; exact Hk).
  assert (W65 : CL5A.uv E' FE = CL5A.uv E1 FE) by (unfold CL5A.uv, FE, FEV; cbn [edenot]; rewrite <- (proj1 Hag 65%nat) by (clear - NX; lia); reflexivity).
  assert (W60 : CL5A.uv E' FLE = CL5A.uv E1 FLE) by (unfold CL5A.uv, FLE, FLV; cbn [edenot]; rewrite <- (proj1 Hag 60%nat) by (clear - NX; lia); reflexivity).
  split; [exact FZ|]. split; [exact W65|]. split; [exact W60|].
  split; [intros X0 HX0; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0)|].
  split; [intros q e0 z Hq Hz; rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq); rewrite <- Hz; symmetry; apply Z_to_bv_bv_unsigned|].
  intros a Ha Hout. apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF).
  unfold PSO.cpf_ok in CF. rewrite forallb_forall in CF.
  unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hr. specialize (CF _ Hr). apply orb_prop in CF.
  rewrite L5.unsigned_lit by exact Ha. pose proof (UU I) as (U2 & U10 & _).
  assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite (FZ 2%nat ltac:(clear; lia)); exact U2).
  assert (W10 : bv_unsigned (ev E' 10) = P) by (rewrite (FZ 10%nat ltac:(clear; lia)); exact U10).
  unfold outU in Hout. cbv zeta in Hout. unfold PSOC.SCR in Hout |- *. destruct Hout as (X1 & X2 & X3 & X4 & X5a & X5b & X5c & X5d & X6 & X7).
  pose proof (CL5A.uv_range E' FE) as R65.
  destruct CF as [CF|CF].
  - apply existsb_exists in CF as (u & Hu & He).
    destruct u as [[ub ulo] ulen]. unfold PSO.region_eqb in He. cbn [fst snd] in He. apply andb_prop in He as [He E3]. apply andb_prop in He as [E1' E2]. apply expr_eqb_eq in E1', E3. apply Z.eqb_eq in E2. subst rb rlo rlen.
    unfold PSO.F_NB, PSO.FP, PSO.UEXTRA, PSO.F_STK, PSO.MORE in Hu. cbn [In app] in Hu.
    unfold CL5A.uv, FE, FLE in X2, X3, X4, X6, R65; cbn [edenot] in X2, X3, X4, X6, R65.
    destruct Hu as [Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[Hu|[]]]]]]]]]]]]]]; injection Hu as <- <- <-; unfold PE, FE, FLE, CHA.SRL3, SBz, SCR; rewrite ?CL5A.estart_srl3';
      unfold estart, elenZ, CL5A.uv; cbn [a_base a_off edenot]; rewrite ?W2, ?W10; rewrite ?u64_of_Z by (clear; lia).
    + clear - X1. lia.
    + clear - X2. lia.
    + clear - X3. lia.
    + clear - X4 R65. pose proof (Z.div_pos (bv_unsigned (ev E' FEV)) 8). lia.
    + clear - X5a. lia.
    + clear - X5b. lia.
    + clear - X5d. lia.
    + clear - X5c. lia.
    + clear - X5b. lia.
    + clear - X6. lia.
    + clear - X5b. lia.
    + clear - X5b. lia.
    + clear - X2. lia.
  - (* [comment removed for export] *)
    unfold PSO.region_eqb in CF. cbn [fst snd] in CF. apply andb_prop in CF as [CF E3]. apply andb_prop in CF as [E1' E2]. apply expr_eqb_eq in E1', E3. apply Z.eqb_eq in E2. subst rb rlo rlen.
    assert (HB : PSO.has_bufbyte (CC.cp_F c) = true).
    { destruct (bvar_i i ltac:(clear - Hi; lia)) as (v & Hv & Hv2). unfold PSO.has_bufbyte. apply existsb_exists.
      exists (fst (PSO.blk0 i), 0, ELit 1). split; [exact Hr|]. rewrite Hv. apply negb_true_iff, Nat.eqb_neq. exact Hv2. }
    specialize (X7 HB).
    unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite u64_of_Z by (clear; lia). unfold CL5A.uv in X7. clear - X7. lia.
Qed.

(* [comment removed for export] *)
Lemma stk_pot_nonneg : forall sc, In sc [66; 132; 264; 528; 1056] -> 0 <= PSOX.stk_kx I sc /\ 0 <= PSOX.stk_bx I sc.
Proof.
  intros sc Hsc. destruct (L5A.aly_cost L C LAY) as (P1 & P2 & P3). unfold PSOX.stk_kx, PSOX.stk_bx. pose proof (Z.log2_nonneg (1056 / sc)) as L0.
  set (b := Z.log2 (1056 / sc)) in *. cbn [In] in Hsc.
  assert (X1 : 0 <= b * hl_k_per_malloc L) by (apply Z.mul_nonneg_nonneg; [exact L0 | clear - P1; lia]).
  assert (X2 : 0 <= b * hl_b_overhead L) by (apply Z.mul_nonneg_nonneg; [exact L0 | clear - P3; lia]).
  assert (X3 : 0 <= hl_b_lin L * (2112 - 2 * sc)) by (apply Z.mul_nonneg_nonneg; [clear - P2; lia | clear - Hsc; lia]).
  clear - X1 X2 X3. split; lia.
Qed.
Lemma pcredit_bufcred : forall cr1 ps1, In (PML.ps_scap ps1) [66; 132; 264; 528; 1056] ->
  PMLA.pcredit_xA L cr1 ps1 (PSOIW.KXG I gx) (PSOIW.BXG I gx) <-> PMSA.bufcredA L cr1 (PML.ps_bcap ps1) (PSOX.stk_kx I (PML.ps_scap ps1) + PSOIW.KXG I gx) (PSOX.stk_bx I (PML.ps_scap ps1) + PSOIW.BXG I gx).      (* [comment removed for export] *)
Proof.
  intros cr1 ps1 Hsc. pose proof (stk_pot_nonneg _ Hsc) as [K0 B0]. pose proof (PSOIW.KXG0 I gx) as [KX1 BX1]. pose proof (PSOIW.iHkx I) as KX0. pose proof (PSOIW.iHbx I) as BX0.
  set (KX := PSOIW.KXG I gx) in *. set (BXX := PSOIW.BXG I gx) in *. clearbody KX BXX.
  unfold PMLA.pcredit_xA, PMLA.pcreditA, PMSA.bufcredA, PML.kleft, PML.bleft in *. unfold PSOX.stk_kx, PSOX.stk_bx in *. cbn [fst snd].
  set (a := Z.log2 (2 ^ 27 / PML.ps_bcap ps1)) in *. set (b := Z.log2 (1056 / PML.ps_scap ps1)) in *.
  set (kpm := hl_k_per_malloc L) in *. set (bov := hl_b_overhead L) in *. set (blin := hl_b_lin L) in *.
  rewrite !Z.mul_add_distr_r in *. rewrite !Z.mul_add_distr_l in *.
  set (ak := a * kpm) in *. set (bk := b * kpm) in *. set (ao := a * bov) in *. set (bo := b * bov) in *.
  clearbody ak bk ao bo. clear - K0 B0 KX0 BX0 KX1 BX1. split; intros H; [destruct H as (_ & _ & H1 & H2 & H3) | destruct H as (H1 & _ & _ & H2 & H3)]; repeat split; lia.
Qed.

(* [comment removed for export] *)
Definition SUPP (bp bc sbp sc : Z) (a : Z) : Prop :=
  (P <= a < P + 272) \/ (E <= a < E + 16) \/ (bp <= a < bp + bc) \/ in_shadow_of bp bc a \/ (sbp <= a < sbp + sc) \/ in_shadow_of sbp sc a \/ STATIC a
  \/ (exists u n, In (u, n) LBo /\ (u <= a < u + n \/ in_shadow_of u n a)).      (* [comment removed for export] *)
Section Mv.
Variables (M1 M2 : mem) (bp bc sbp sc : Z).
Hypothesis AG : forall a, SUPP bp bc sbp sc a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
(* [comment removed for export] *)
Variables (LBx : list (Z * Z)) (FFx LKx : list fframe) (crx : credit) (Ax : list (Z * Z)) (Mx : mem) (Vx : vml).
Hypothesis HHx : ri_inv HI LBx FFx LKx crx Ax Mx Vx.
Hypothesis INb : In (bp, bc) LBx.
Hypothesis INs : In (sbp, sc) LBx.
Let Sx := SUPP bp bc sbp sc.
Lemma OUTP : PTA.out Sx P 272. Proof. pose_facts I. split; [clear - O3; lia|]. split; [clear - O6; lia|]. intros i Hi. left. exact Hi. Qed.
Lemma OUTE : PTA.out Sx E 16. Proof. pose_facts I. split; [clear - Q3; lia|]. split; [clear - Q6; lia|]. intros i Hi. right; left. exact Hi. Qed.
Lemma OUTB : PTA.out Sx bp bc.
Proof.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) (bp, bc) INb) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _). cbn [fst snd] in D0, D3, D5, D7.
  split; [clear - D5; lia|]. split; [clear - D7; lia|]. intros i Hi. right; right; left. exact Hi.
Qed.
Lemma OUTS : PTA.out Sx sbp sc.
Proof.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) (sbp, sc) INs) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _). cbn [fst snd] in D0, D3, D5, D7.
  split; [clear - D5; lia|]. split; [clear - D7; lia|]. intros i Hi. do 4 right; left. exact Hi.
Qed.
Lemma parser_at_mv : forall psx, PML.ps_bptr psx = bp -> PML.ps_bcap psx = bc -> PML.ps_sb psx = sbp -> PML.ps_scap psx = sc ->
  PMLA.parser_at (hl_segs L) IC M1 P psx -> PMLA.parser_at (hl_segs L) IC M2 P psx.
Proof.
  intros psx Hb Hc Hs Hsc H.
  assert (ST : L5.u8_at (hl_segs L) M2 (P + 208) (PML.ps_st psx)).
  { pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). apply (PTA.u8_ag (hl_segs L) M1 M2 Sx AG); [apply (PTA.out_sub _ _ _ _ _ OUTP); lia | exact X]. }
  assert (DF : M2 (Z_to_bv 64 (P + 208)) <> None).
  { pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D).
    rewrite (AG (P + 208) ltac:(left; lia)). exact (D 208 ltac:(lia)). }
  pose proof (PTA.parser_at_st (hl_segs L) IC M1 M2 Sx AG P psx (PML.ps_st psx) ltac:(intros k n Hk Hn _; apply (PTA.out_sub _ _ _ _ _ OUTP); lia)
                ltac:(rewrite Hb, Hc; exact OUTB) ltac:(rewrite Hs, Hsc; exact OUTS) H ST DF) as G.
  destruct psx; exact G.
Qed.
Lemma parser_sh_mv : forall psx, PML.ps_bptr psx = bp -> PML.ps_bcap psx = bc -> PML.ps_sb psx = sbp -> PML.ps_scap psx = sc -> Z.of_nat (length (PML.ps_stack psx)) <= PML.ps_scap psx ->
  PMLA.parser_sh M1 psx -> PMLA.parser_sh M2 psx.
Proof.
  intros psx Hb Hc Hs Hsc Hsl H.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) (bp, bc) INb) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _). cbn [fst snd] in D3, D16.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) (sbp, sc) INs) as ((G0 & G1 & G16 & G3 & G4 & (G5 & G6 & G7)) & _). cbn [fst snd] in G3, G16.
  apply (PTA.parser_sh_ag M1 M2 Sx AG psx); [rewrite Hc; clear - D3; lia | clear - Hsl; lia | rewrite Hb; exact (CHA.mod8_of_16 _ D16) | rewrite Hs; exact (CHA.mod8_of_16 _ G16)
    | rewrite Hb, Hc; intros a Ha; do 3 right; left; exact Ha | rewrite Hs, Hsc; intros a Ha; do 5 right; left; exact Ha | exact H].
Qed.
Lemma ec_at_mv : forall code, PMLA.ec_at (hl_segs L) IC M1 E code -> PMLA.ec_at (hl_segs L) IC M2 E code.
Proof. intros code H. exact (PTA.ec_at_ag (hl_segs L) IC M1 M2 Sx AG E code OUTE H). Qed.
Lemma XCELLS_mv : forall cp cp2 tg, PSOX.XCELLS I M1 cp cp2 tg -> PSOX.XCELLS I M2 cp cp2 tg.      (* [comment removed for export] *)
Proof. intros cp cp2 tg. pose proof OUTP as (O0 & O1 & O2). apply (PSOX.XCELLS_ag I M1 M2 cp cp2 tg); [clear - O0; lia | clear - O1; lia | intros a Ha; exact (AG a (O2 a Ha))]. Qed.
Lemma ls_ok_mv : forall g1, g1 <> PML.LS0 -> PMLA.ls_ok (hl_segs L) IC g1 M1 -> PMLA.ls_ok (hl_segs L) IC g1 M2.
Proof. intros g1 Hg H. apply (LS_mv I g1 M1 M2); [intros a Ha; apply AG; do 6 right; left; exact Ha | exact Hg | exact H]. Qed.
End Mv.

(* [comment removed for export] *)
Lemma CORE_mv : forall i Ex (M1 M2 : mem) mw ps1 code g1 LBx FFx LKx crx Ax Mx Vx,
  ri_inv HI LBx FFx LKx crx Ax Mx Vx -> In (bptrI i Ex, bcapI i Ex) LBx -> In (sbI i Ex, scapI i Ex) LBx -> PML.wf_ps ps1 ->
  (forall a, SUPP (bptrI i Ex) (bcapI i Ex) (sbI i Ex) (scapI i Ex) a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, PSOIW.xfoot I gx a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->      (* [comment removed for export] *)
  PSOX.CORE I i Ex M1 mw ps1 code g1 -> PSOX.CORE I i Ex M2 mw ps1 code g1.
Proof.
  intros i Ex M1 M2 mw ps1 code g1 LBx FFx LKx crx Ax Mx Vx HHx INb INs WF AG XAG CO.
  pose proof (PSOX.c_blk _ _ _ _ _ _ _ _ CO) as CB. unfold PML.ps_blocks in CB. injection CB as Esc Esb Ebc Ebp.
  assert (HG : g1 <> PML.LS0) by (destruct (PSOX.c_g _ _ _ _ _ _ _ _ CO) as [-> | [-> _]]; [exact (PSOIW.iHG I) | discriminate]).
  pose proof (PSSA.wf_shape ps1 WF) as (_ & _ & SL & _).
  constructor.
  - apply (parser_at_mv M1 M2 _ _ _ _ AG LBx FFx LKx crx Ax Mx Vx HHx INb INs (PML.ps_set_win ps1 mw)); try exact (PSOX.c_pa _ _ _ _ _ _ _ _ CO).
    all: destruct ps1; cbn [PML.ps_set_win PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap] in *; first [exact Ebp | exact Ebc | exact Esb | exact Esc].
  - exact (PSOX.c_mw _ _ _ _ _ _ _ _ CO).
  - apply (parser_sh_mv M1 M2 _ _ _ _ AG LBx FFx LKx crx Ax Mx Vx HHx INb INs ps1); try exact (PSOX.c_sh _ _ _ _ _ _ _ _ CO); try first [exact Ebp | exact Ebc | exact Esb | exact Esc].
    pose proof (PTB.pa_slen L IC _ _ _ (PSOX.c_pa _ _ _ _ _ _ _ _ CO)) as SL2. clear - SL2. destruct ps1; cbn [PML.ps_set_win PML.ps_scap PML.ps_stack] in *. exact SL2.
  - exact (PSOX.c_win _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_bb _ _ _ _ _ _ _ _ CO).
  - exact (ec_at_mv M1 M2 _ _ _ _ AG code (PSOX.c_ec _ _ _ _ _ _ _ _ CO)).
  - exact (ls_ok_mv M1 M2 _ _ _ _ AG g1 HG (PSOX.c_ls _ _ _ _ _ _ _ _ CO)).
  - exact (PSOX.c_g _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_blk _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_na _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_wl _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_e0 _ _ _ _ _ _ _ _ CO).
  - exact (PSOIW.XKEEP I M1 M2 gx XAG (PSOX.c_x _ _ _ _ _ _ _ _ CO)).
  - exact (PSOX.c_sync _ _ _ _ _ _ _ _ CO).
Qed.
(* [comment removed for export] *)
Lemma WCORE_mv : forall i Ex (M1 M2 : mem) ps1 code bp bc sbp sc, (forall a, SUPP bp bc sbp sc a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  PSOX.WCORE I i Ex M1 ps1 code -> PSOX.WCORE I i Ex M2 ps1 code.
Proof. intros i Ex M1 M2 ps1 code bp bc sbp sc AG (cp & cp2 & tg & XC & WS). exists cp, cp2, tg. split; [exact (XCELLS_mv M1 M2 _ _ _ _ AG cp cp2 tg XC) | exact WS]. Qed.
Lemma POSTP_mv : forall i Ex (M1 M2 : mem) LBx FFx LKx crx Ax Mx Vx,
  ri_inv HI LBx FFx LKx crx Ax Mx Vx -> In (bptrI i Ex, bcapI i Ex) LBx -> In (sbI i Ex, scapI i Ex) LBx ->
  (forall a, SUPP (bptrI i Ex) (bcapI i Ex) (sbI i Ex) (scapI i Ex) a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, PSOIW.xfoot I gx a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  PSOX.POSTP I i Ex M1 -> PSOX.POSTP I i Ex M2.
Proof.
  intros i Ex M1 M2 LBx FFx LKx crx Ax Mx Vx HHx INb INs AG XAG (ps1 & code & g1 & CO & WCO & WF & MO & RL).
  exists ps1, code, g1. split; [exact (CORE_mv i Ex M1 M2 _ ps1 code g1 _ _ _ _ _ _ _ HHx INb INs WF AG XAG CO)|]. split; [exact (WCORE_mv i Ex M1 M2 ps1 code _ _ _ _ AG WCO)|]. split; [exact WF|]. split; [exact MO | exact RL].
Qed.

(* [comment removed for export] *)
Lemma BLKW : forall LBX FFX LKX crX AX MX VX u n, ri_inv HI LBX FFX LKX crX AX MX VX -> In (u, n) LBX ->
        (4096 <= u /\ 0 < n /\ u + n <= ahl_ceil ar /\ u mod 16 = 0 /\ (u + n <= 2147446784 \/ 17594333495296 <= u) /\ u + n <= 140737488355328)
        /\ (u + n <= hl_img_lo L \/ hl_img_hi L <= u) /\ fframes_apart u n FFX /\ (u + n <= ar_fs ar \/ ar_fs ar + 11571200 <= u) /\ HeapIface.defined MX u n.
Proof.
  intros LBX FFX LKX crX AX MX VX u n HHX Hun.
    destruct (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHX) as (WB & _). destruct (WB (u, n) Hun) as (B1 & B2 & _ & _ & _ & B6 & B7). cbn [fst snd] in B1, B2, B6, B7.
    destruct B1 as (R1 & R2 & R3 & R4 & R5 & (R6 & R7 & R8)). unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
    split; [clear - R1 R3 R4 R5 R7 R8; lia|]. split; [exact R2|]. split; [intros f Hf; apply B6; apply in_or_app; left; exact Hf|]. split; [exact B7 | exact B2].
Qed.
Definition GRNG : Prop := forall b, In b (PMES.g_lbv gx) -> 4096 <= fst b /\ 0 < snd b /\ fst b + snd b <= ahl_ceil ar /\ fst b mod 16 = 0 /\ fst b + snd b <= 2 ^ 47 /\ (fst b + snd b <= hl_img_lo L \/ hl_img_hi L <= fst b) /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + 11571200 <= fst b).
Lemma XRNG : forall LBX FFX LKa cra A1 (M1 : word -> option byte) m1, ri_inv HI LBX FFX LKa cra A1 M1 (vml_of m1) -> incl (PMES.g_lbv gx) LBX -> GRNG.
Proof.
  intros LBX FFX LKa cra A1 M1 m1 HHa HiG b Hb. destruct b as [u n].
    destruct (BLKW _ _ _ _ _ _ _ u n HHa (HiG _ Hb)) as ((R1 & R4 & R5 & R16 & R6 & R7) & RI & _ & BFS & _).
    cbn [fst snd]. split; [exact R1|]. split; [exact R4|]. split; [exact R5|]. split; [exact R16|]. split; [exact R7|]. split; [exact RI | exact BFS].
Qed.
(* [comment removed for export] *)
Lemma GRNG_of : forall i E1 A1 M1 m1, (2 <= i < PSO.NCUT)%nat -> AAMB i E1 A1 M1 m1 -> GRNG.
Proof.
  intros i E1 A1 M1 m1 Hi HA. destruct (FRM i E1 A1 M1 m1 Hi HA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (crX & LKX & HHX & _)).
  exact (XRNG _ _ _ _ _ _ _ HHX ltac:(intros y Hy; apply in_or_app; right; unfold PSOIW.LBV; apply in_or_app; right; exact Hy)).
Qed.
Lemma FLNV : forall fl', GRNG -> ar_fs ar <= fl' < ar_fs ar + 11571200 -> ~ aclient L ar LBo FF sp (CH.hd_scr G.HDECL) fl' -> ~ aclient L ar LBV FF sp (CH.hd_scr G.HDECL) fl'.
Proof.
  pose_facts I.
  intros fl' HGB Hfl NC AC. apply NC. pose proof (CHA.rf_fs _ _ _ _ RFx) as ((_ & FSAPP' & _) & _ & _). unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in FSAPP'.
    destruct AC as [AX|[AX|[AX|[AX|[AX|[AX|AX]]]]]].
    - destruct AX as (b & Hb & Hr). unfold PSOIW.LBV in Hb. apply in_app_or in Hb as [Hb|Hb]; [left; exists b; split; [exact Hb | exact Hr]|]. exfalso.
      destruct (HGB b Hb) as (R1 & R4 & _ & _ & _ & _ & BFS). destruct b as [u n]. cbn [fst snd] in Hr, R1, R4, BFS. clear - Hr Hfl BFS R4. lia.
    - right; left; exact AX.
    - right; right; left; exact AX.
    - right; right; right; left; exact AX.
    - do 4 right; left; exact AX.
    - do 5 right; left; exact AX.
    - destruct AX as (b & Hb & Hr). unfold PSOIW.LBV in Hb. apply in_app_or in Hb as [Hb|Hb]; [do 6 right; exists b; split; [exact Hb | exact Hr]|]. exfalso.
      destruct (HGB b Hb) as (R1 & R4 & R5 & R16 & R7 & _). destruct b as [u n]. cbn [fst snd] in Hr, R1, R4, R5, R7.
      pose proof (SHR u n fl' ltac:(clear - R1; lia) R4 R7 Hr) as RG. clear - RG Hfl FSAPP'. lia.
Qed.
(* [comment removed for export] *)
Lemma XK : forall a LBX FFX sp' scr' Wc, PSOIW.xfoot I gx a -> GRNG -> incl LBV LBX -> incl FF FFX -> (forall x, sp' - scr' <= x < sp' -> sp - 17600 <= x < sp) ->
          (forall w, In w Wc -> L5.in_rng w a -> False) -> CHA.akept L ar LBX FFX sp' scr' Wc a.
Proof.
  pose_facts I. pose proof (RFO I) as RFo.
  intros a LBX FFX sp' scr' Wc Ha HGB HiB HiF HstkW HWc.
    destruct (XKA.xfoot_cases IC V (PSOIW.iSQ I) gx a Ha) as [Hv|[Hs|[(b & Hb & Hr)|[Hsh|Hl]]]].
    - destruct (CL5A.infr_wok L ar LBo FF sp 17600 V 408 a RFo VfrX ltac:(unfold PMES.ENC_SIZE in Hv; exact Hv)) as (G1 & G2 & _). split; [exact G1|].
      split; [eapply CHA.aclient_scr; [eapply CHA.aclient_incl; [intros y Hy; apply HiB; unfold PSOIW.LBV; apply in_or_app; left; exact Hy | exact HiF | exact (aclientw_client _ _ _ _ _ _ _ G2)] | exact HstkW]|].
      intros w Hw Hin. exact (False_ind _ (HWc w Hw Hin)).
    - destruct (CL5A.infr_wok L ar LBo FF sp 17600 (PSOIW.iSQ I) 24 a RFo S2fr Hs) as (G1 & G2 & _). split; [exact G1|].
      split; [eapply CHA.aclient_scr; [eapply CHA.aclient_incl; [intros y Hy; apply HiB; unfold PSOIW.LBV; apply in_or_app; left; exact Hy | exact HiF | exact (aclientw_client _ _ _ _ _ _ _ G2)] | exact HstkW]|].
      intros w Hw Hin. exact (False_ind _ (HWc w Hw Hin)).
    - destruct (HGB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
      assert (HbX : In b LBX) by (apply HiB; unfold PSOIW.LBV; apply in_or_app; right; exact Hb).
      assert (AR : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [clear - Hr B1 B5; lia | pose proof (SHR (fst b) (snd b) a ltac:(clear - B1; lia) B2 B5 Hr); clear - H; lia]).
      split; [exact AR|]. split; [destruct Hr as [Hr|Hr]; [left; exists b; split; [exact HbX | exact Hr] | do 6 right; exists b; split; [exact HbX | exact Hr]]|].
      intros w Hw Hin. exact (False_ind _ (HWc w Hw Hin)).
    - assert (G : 0 <= a < 2 ^ 64 /\ aclientw L ar LBo FF sp 17600 a).
      { destruct Hsh as [Hsh|Hsh]; [destruct (CL5A.infr_sh_wok L ar LBo FF sp 17600 V 408 a RFo VfrX ltac:(clear; lia) ltac:(unfold PMES.ENC_SIZE in Hsh; exact Hsh)) as (G1 & G2 & _)
                                     | destruct (CL5A.infr_sh_wok L ar LBo FF sp 17600 (PSOIW.iSQ I) 24 a RFo S2fr ltac:(clear; lia) Hsh) as (G1 & G2 & _)]; exact (conj G1 G2). }
      destruct G as (G1 & G2). split; [exact G1|].
      split; [eapply CHA.aclient_scr; [eapply CHA.aclient_incl; [intros y Hy; apply HiB; unfold PSOIW.LBV; apply in_or_app; left; exact Hy | exact HiF | exact (aclientw_client _ _ _ _ _ _ _ G2)] | exact HstkW]|].
      intros w Hw Hin. exact (False_ind _ (HWc w Hw Hin)).
    - unfold PMLA.LIT_LO, PMLA.LIT_HI in Hl. cbn in Hl. destruct (LITCL I a ltac:(clear - Hl; lia)) as (RG & CLa). split; [clear - RG; lia|].
      split; [eapply CHA.aclient_scr; [eapply CHA.aclient_incl; [intros y Hy; apply HiB; unfold PSOIW.LBV; apply in_or_app; left; exact Hy | exact HiF | exact (CLa LBo sp 17600)] | exact HstkW]|].
      intros w Hw Hin. exact (False_ind _ (HWc w Hw Hin)).
Qed.
End F.
