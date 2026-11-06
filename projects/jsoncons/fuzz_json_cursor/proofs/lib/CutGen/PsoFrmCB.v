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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA PtKitB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsKitA PsoInstCB PsoSemA PsoSemCA ParseSomeChkCB PsoBaseCB PsoXiCB.
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

Lemma ffs_i : forall i, (2 <= i < PSO.NCUT)%nat -> nth i PSO.FFS [] = [PSO.FR].
Proof.
  intros i Hi. unfold PSO.FFS.
  assert (X : forallb (fun k => match nth k PSO.FFS [] with [f] => CHA.frames_eqb [f] [PSO.FR] | _ => false end) (seq 2 (PSO.NCUT - 2)) = true) by vmc_refl.
  rewrite forallb_forall in X. specialize (X i ltac:(apply in_seq; clear - Hi; lia)). unfold PSO.FFS in X.
  destruct (nth i _ []) as [|f [|f2 r]]; try discriminate X. apply CHA.frames_eqb_eq in X. exact X.
Qed.
Lemma ffs_0 : nth 0 PSO.FFS [] = []. Proof. vmc_refl. Qed.
Lemma ffs_1 : nth 1 PSO.FFS [] = []. Proof. vmc_refl. Qed.
Lemma bls_i : forall i, (i < PSO.NCUT)%nat -> nth i G.BLS [] = [PSO.blk0 i; PSO.blk1 i].
Proof.
  intros i Hi.
  assert (X : forallb (fun k => match nth k G.BLS [] with [_; _] => true | _ => false end) (seq 0 PSO.NCUT) = true) by vmc_refl.
  rewrite forallb_forall in X. specialize (X i ltac:(apply in_seq; clear - Hi; lia)). unfold PSO.blk0, PSO.blk1.
  destruct (nth i G.BLS []) as [|b0 [|b1 [|b2 rr]]]; try discriminate X. reflexivity.
Qed.

Lemma len_cps : length G.CPS = PSO.NCUT. Proof. vmc_refl. Qed.
Lemma blv_all : forallb (fun i => CH2.blocks_vars_lt (CC.cp_nx (nth i G.CPS CA.dummy_cp)) (nth i G.BLS [])) (seq 0 PSO.NCUT) = true.
Proof. vmc_refl. Qed.

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

Lemma kind01 : PSO.kind_of 0 = PSO.KEntry /\ PSO.kind_of 1 = PSO.KEntry. Proof. vm_compute. split; reflexivity. Qed.
Lemma ge2_of_kind : forall i c kd, nth_error G.CPS i = Some c -> PSO.kind_of i = kd -> kd <> PSO.KEntry -> (2 <= i < PSO.NCUT)%nat.
Proof.
  intros i c kd Hci Hk Hne. pose proof kind01 as [K0 K1].
  assert (Hi : (i < PSO.NCUT)%nat) by (rewrite <- len_cps; apply nth_error_Some; rewrite Hci; discriminate).
  split; [|exact Hi]. destruct i as [|[|i]]; [exfalso; apply Hne; rewrite <- Hk; exact K0 | exfalso; apply Hne; rewrite <- Hk; exact K1 | clear; lia].
Qed.

Lemma u0_retire_all : forallb (fun i => negb (PSO.u0 i) || negb (PSO.kind_eqb (PSO.kind_of i) PSO.KRetx || PSO.kind_eqb (PSO.kind_of i) PSO.KSetsh))%bool (seq 0 PSO.NCUT) = true.
Proof. vmc_refl. Qed.
Lemma u0_retire : forall i c, nth_error G.CPS i = Some c -> PSO.kind_of i = PSO.KRetx \/ PSO.kind_of i = PSO.KSetsh -> PSO.u0 i = false.
Proof.
  intros i c Hci Hk. assert (Hi : (i < PSO.NCUT)%nat) by (rewrite <- len_cps; apply nth_error_Some; rewrite Hci; discriminate).
  pose proof (proj1 (forallb_forall _ _) u0_retire_all i ltac:(apply in_seq; clear - Hi; lia)) as X. cbv beta in X.
  destruct (PSO.u0 i); [|reflexivity]. exfalso. cbn [negb orb] in X. destruct Hk as [Hk|Hk]; rewrite Hk in X; discriminate X.
Qed.

Section F.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation LK := (PSOI.iLK I).   Local Abbreviation cr := (PSOI.icr I).   Local Abbreviation A := (PSOI.iA I).
Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).      Local Abbreviation V := (PSOI.iV I).     Local Abbreviation E := (PSOI.iE I).     Local Abbreviation B := (PSOI.iB I).
Local Abbreviation R := (PSOI.iR I).     Local Abbreviation M := (PSOI.iM I).      Local Abbreviation model := (PSOI.imodel I).
Local Abbreviation HIok := (PSOI.iHIok I). Local Abbreviation LAY := (PSOI.iLAY I). Local Abbreviation HH := (PSOI.iHH I).
Local Abbreviation E0 := (PSOI.E0 I).      Local Abbreviation LB := (PSOI.LB I).
Local Abbreviation WW := (WW I).            Local Abbreviation Cred := (PSOX.Cred I).
Local Abbreviation bptrI := (PSOX.bptrI).  Local Abbreviation bcapI := (PSOX.bcapI). Local Abbreviation sbI := (PSOX.sbI). Local Abbreviation scapI := (PSOX.scapI).

Definition AAMB := CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6.

Definition AMBX := CHA.ambX L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6 (PSOX.XI I).

Definition LEAF (pc : Z) : Prop := forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> CCA.leaf_ok (hl_segs L) G.CPS AMBX (PSOI.iK I) PMSA.fp_ok i c ps0.

Lemma FRM : forall i E1 A1 M1 m1, (2 <= i < PSO.NCUT)%nat -> AAMB i E1 A1 M1 m1 ->
  let F := CL5A.uv E1 FE in let ob := [(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] in
  CHA.curB LBo G.BLS i E1 = ob ++ LBo /\ CHA.curF FF sp PSO.FFS i E1 = (F, 4, sp + PSO.CSP + 32) :: FF /\ env_agree GT.NF E0 E1 /\
  0 <= F /\ F + 1024 <= 140737488355328 /\ F mod 64 = 0 /\ (F + 1024 <= 2147446784 \/ 17594333495296 <= F) /\ ar_fs ar <= F /\ F + 1024 <= ar_fs ar + 11571200 /\ fframes_apart F 1024 FF /\
  (exists crX LKX, ri_inv HI (ob ++ LBo) ((F, 4, sp + PSO.CSP + 32) :: FF) LKX crX A1 M1 (vml_of m1) /\ Cred i E1 crX).
Proof.
  intros i E1 A1 M1 m1 Hi HA. cbv zeta.
  pose proof HA as (_ & _ & _ & HagE & (cra & LKa & HHa & _ & HCa & _) & _).
  assert (HcB : CHA.curB LBo G.BLS i E1 = [(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] ++ LBo).
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

Definition outU (Fr : list SGP.region) (E' : env) (bp : Z) (a : Z) : Prop :=
  let F := CL5A.uv E' FE in let fl := CL5A.uv E' FLE in
  (a < sp - SCR \/ sp <= a) /\ ~ (F <= a < F + 24) /\ ~ (F + 32 <= a < F + 1016) /\ ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 128) /\
  ~ (P + 148 <= a < P + 192) /\ ~ (P + 200 <= a < P + 216) /\ ~ (P + 220 <= a < P + 224) /\ ~ (P + 232 <= a < P + 240) /\ a <> fl /\
  (PSO.has_bufbyte Fr = true -> a <> bp).

Lemma bvar_all : forallb (fun k => match fst (PSO.blk0 k) with EVar v => negb (Nat.eqb v 2) | _ => false end) (seq 0 PSO.NCUT) = true.
Proof. vmc_refl. Qed.
Lemma bvar_i : forall i, (i < PSO.NCUT)%nat -> exists v, fst (PSO.blk0 i) = EVar v /\ v <> 2%nat.
Proof.
  intros i Hi. pose proof (proj1 (forallb_forall _ _) bvar_all i ltac:(apply in_seq; clear - Hi; lia)) as X. cbv beta in X.
  destruct (fst (PSO.blk0 i)) as [z|v|op a b|op a b|op a b|op a b|sx lo n e|sx k j n]; try discriminate X. exists v. split; [reflexivity|]. apply negb_true_iff, Nat.eqb_neq in X. exact X.
Qed.

Lemma LEAFK : forall i c ps0 E1 A1 M1 m1 E' R' M' m', (2 <= i < PSO.NCUT)%nat -> nth_error G.CPS i = Some c -> PSO.cpf_ok i (CC.cp_F c) = true ->
  AAMB i E1 A1 M1 m1 -> env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  (forall k, (k < 40)%nat -> ev E' k = ev E0 k) /\ CL5A.uv E' FE = CL5A.uv E1 FE /\ CL5A.uv E' FLE = CL5A.uv E1 FLE
  /\ (forall X0, In X0 (SR.ps_cells ps0) -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0)
  /\ (forall (q : nat) (e0 : expr) (z : Z), CL.ps_reg_is ps0 q e0 = true -> bv_unsigned (edenot E' e0) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z)
  /\ (forall a, 0 <= a < 2 ^ 64 -> outU (CC.cp_F c) E' (CL5A.uv E' (fst (PSO.blk0 i))) a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
Proof.
  intros i c ps0 E1 A1 M1 m1 E' R' M' m' Hi Hci CF HA Hag HLF.
  pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6 i c E1 E' A1 M1 m1 HA (G.NF_le i c Hci) Hag) as HagE'.
  assert (NX : (66 <= CC.cp_nx c)%nat).
  { assert (X : forallb (fun k => Nat.leb 66 (CC.cp_nx (nth k G.CPS CA.dummy_cp))) (seq 2 (PSO.NCUT - 2)) = true) by vmc_refl.
    rewrite forallb_forall in X. specialize (X i ltac:(apply in_seq; clear - Hi; lia)). apply Nat.leb_le in X. rewrite (nth_error_nth _ _ CA.dummy_cp Hci) in X. exact X. }
  assert (FZ : forall k, (k < 40)%nat -> ev E' k = ev E0 k) by (intros k Hk; symmetry; apply (proj1 HagE'); unfold GT.NF, Cut_psome_cboth_T.NF; exact Hk).
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
    + clear - X5c. lia.
    + clear - X5d. lia.
    + clear - X5b. lia.
    + clear - X6. lia.
    + clear - X5b. lia.
    + clear - X5b. lia.
    + clear - X2. lia.
  -
    unfold PSO.region_eqb in CF. cbn [fst snd] in CF. apply andb_prop in CF as [CF E3]. apply andb_prop in CF as [E1' E2]. apply expr_eqb_eq in E1', E3. apply Z.eqb_eq in E2. subst rb rlo rlen.
    assert (HB : PSO.has_bufbyte (CC.cp_F c) = true).
    { destruct (bvar_i i ltac:(clear - Hi; lia)) as (v & Hv & Hv2). unfold PSO.has_bufbyte. apply existsb_exists.
      exists (fst (PSO.blk0 i), 0, ELit 1). split; [exact Hr|]. rewrite Hv. apply negb_true_iff, Nat.eqb_neq. exact Hv2. }
    specialize (X7 HB).
    unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite u64_of_Z by (clear; lia). unfold CL5A.uv in X7. clear - X7. lia.
Qed.

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
  PMLA.pcredit_xA L cr1 ps1 (PSOI.ikx I) (PSOI.ibx I) <-> PMSA.bufcredA L cr1 (PML.ps_bcap ps1) (PSOX.stk_kx I (PML.ps_scap ps1) + PSOI.ikx I) (PSOX.stk_bx I (PML.ps_scap ps1) + PSOI.ibx I).
Proof.
  intros cr1 ps1 Hsc. pose proof (stk_pot_nonneg _ Hsc) as [K0 B0]. pose proof (PSOI.iHPC I) as (KX0 & BX0 & _).
  unfold PMLA.pcredit_xA, PMLA.pcreditA, PMSA.bufcredA, PML.kleft, PML.bleft in *. unfold PSOX.stk_kx, PSOX.stk_bx in *. cbn [fst snd].
  set (a := Z.log2 (2 ^ 27 / PML.ps_bcap ps1)) in *. set (b := Z.log2 (1056 / PML.ps_scap ps1)) in *.
  set (kpm := hl_k_per_malloc L) in *. set (bov := hl_b_overhead L) in *. set (blin := hl_b_lin L) in *.
  rewrite !Z.mul_add_distr_r in *. rewrite !Z.mul_add_distr_l in *.
  set (ak := a * kpm) in *. set (bk := b * kpm) in *. set (ao := a * bov) in *. set (bo := b * bov) in *.
  clearbody ak bk ao bo. clear - K0 B0 KX0 BX0. split; intros H; [destruct H as (_ & _ & H1 & H2 & H3) | destruct H as (H1 & _ & _ & H2 & H3)]; repeat split; lia.
Qed.

Definition SUPP (bp bc sbp sc : Z) (a : Z) : Prop :=
  (P <= a < P + 272) \/ (E <= a < E + 16) \/ (bp <= a < bp + bc) \/ in_shadow_of bp bc a \/ (sbp <= a < sbp + sc) \/ in_shadow_of sbp sc a \/ STATIC a
  \/ (exists u n, In (u, n) LBo /\ (u <= a < u + n \/ in_shadow_of u n a))
  \/ (V + 8 <= a < V + 48).
Section Mv.
Variables (M1 M2 : mem) (bp bc sbp sc : Z).
Hypothesis AG : forall a, SUPP bp bc sbp sc a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).

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
Lemma ls_ok_mv : forall g1, g1 <> PML.LS0 -> PMLA.ls_ok (hl_segs L) IC g1 M1 -> PMLA.ls_ok (hl_segs L) IC g1 M2.
Proof. intros g1 Hg H. apply (LS_mv I g1 M1 M2); [intros a Ha; apply AG; do 6 right; left; exact Ha | exact Hg | exact H]. Qed.

Lemma OUTV : PTA.out Sx (V + 8) 40. Proof. pose_facts I. split; [clear - VR3; lia|]. split; [clear - VR6; lia|]. intros i Hi. do 8 right. clear - Hi; lia. Qed.
Lemma ev_at_mv : forall e, PMCUR.ev_at (hl_segs L) M1 V e -> PMCUR.ev_at (hl_segs L) M2 V e.
Proof.
  intros e (D & H). split.
  - apply (CL5A.defined_same M1 M2); [intros x Hx; apply AG; do 8 right; clear - Hx; lia | exact D].
  - assert (U64 : forall o v, 8 <= o -> o + 8 <= 48 -> L5.u64_at (hl_segs L) M1 (V + o) v -> L5.u64_at (hl_segs L) M2 (V + o) v).
    { intros o v Ho1 Ho2 X. apply (PTA.u64_ag (hl_segs L) M1 M2 Sx AG); [apply (PTA.out_sub _ _ _ _ _ OUTV); clear - Ho1 Ho2; lia | exact X]. }
    assert (U8 : forall o v, 8 <= o -> o + 1 <= 48 -> L5.u8_at (hl_segs L) M1 (V + o) v -> L5.u8_at (hl_segs L) M2 (V + o) v).
    { intros o v Ho1 Ho2 X. apply (PTA.u8_ag (hl_segs L) M1 M2 Sx AG); [apply (PTA.out_sub _ _ _ _ _ OUTV); clear - Ho1 Ho2; lia | exact X]. }
    destruct e; cbn iota beta in H |- *; repeat match goal with X : _ /\ _ |- _ => destruct X end;
      repeat split; first [ apply (U64 8); [lia | lia | assumption] | apply (U64 32); [lia | lia | assumption] | apply (U64 40); [lia | lia | assumption]
                          | apply (U8 32); [lia | lia | assumption] ].
Qed.
Lemma evp_mv : forall lv w ps', PMCUR.evp (hl_segs L) M1 V lv w ps' -> PMCUR.evp (hl_segs L) M2 V lv w ps'.
Proof. intros lv w ps' (e & H1 & H2). exists e. split; [exact (ev_at_mv e H1) | exact H2]. Qed.
Lemma cur_post_mv : forall psa ps' code, PMCUR.cur_post (hl_segs L) psa ps' code M1 V -> PMCUR.cur_post (hl_segs L) psa ps' code M2 V.
Proof. intros psa ps' code (H1 & H2). split; [exact H1|]. intros Hc Hm. destruct (H2 Hc Hm) as [X|(X & Y)]; [left; exact X | right; split; [exact X | exact (evp_mv _ _ _ Y)]]. Qed.
Lemma STOPOK_mv : forall ps1, PSOX.STOPOK I ps1 M1 -> PSOX.STOPOK I ps1 M2.
Proof. intros ps1 H Hm. destruct (H Hm) as [X|(X & Y)]; [left; exact X | right; split; [exact X | exact (evp_mv _ _ _ Y)]]. Qed.
Lemma REL_mv : forall ps1 code, PSOX.REL I ps1 code M1 -> PSOX.REL I ps1 code M2.
Proof. intros ps1 code (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [exact R3 | exact (cur_post_mv _ _ _ R4)]. Qed.
Lemma PTR_mv : forall pc ps1 code, PSOX.PTR I pc ps1 code M1 -> PSOX.PTR I pc ps1 code M2.
Proof. intros pc ps1 code H Hc. destruct (H Hc) as (H1 & H2). split; [exact H1 | exact (STOPOK_mv _ H2)]. Qed.
End Mv.

Section MvV.
Variables (M1 M2 : mem).
Hypothesis AGV : forall a, V + 8 <= a < V + 48 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Let SV := fun a => V + 8 <= a < V + 48.
Lemma OUTVV : PTA.out SV (V + 8) 40. Proof. pose_facts I. split; [clear - VR3; lia|]. split; [clear - VR6; lia|]. intros x Hx. unfold SV. clear - Hx; lia. Qed.
Lemma ev_at_agV : forall e, PMCUR.ev_at (hl_segs L) M1 V e -> PMCUR.ev_at (hl_segs L) M2 V e.
Proof.
  intros e (D & H). split.
  - apply (CL5A.defined_same M1 M2); [intros x Hx; apply AGV; clear - Hx; lia | exact D].
  - assert (U64 : forall o v, 8 <= o -> o + 8 <= 48 -> L5.u64_at (hl_segs L) M1 (V + o) v -> L5.u64_at (hl_segs L) M2 (V + o) v).
    { intros o v Ho1 Ho2 X. apply (PTA.u64_ag (hl_segs L) M1 M2 SV AGV); [apply (PTA.out_sub _ _ _ _ _ OUTVV); clear - Ho1 Ho2; lia | exact X]. }
    assert (U8 : forall o v, 8 <= o -> o + 1 <= 48 -> L5.u8_at (hl_segs L) M1 (V + o) v -> L5.u8_at (hl_segs L) M2 (V + o) v).
    { intros o v Ho1 Ho2 X. apply (PTA.u8_ag (hl_segs L) M1 M2 SV AGV); [apply (PTA.out_sub _ _ _ _ _ OUTVV); clear - Ho1 Ho2; lia | exact X]. }
    destruct e; cbn iota beta in H |- *; repeat match goal with X : _ /\ _ |- _ => destruct X end;
      repeat split; first [ apply (U64 8); [lia | lia | assumption] | apply (U64 32); [lia | lia | assumption] | apply (U64 40); [lia | lia | assumption]
                          | apply (U8 32); [lia | lia | assumption] ].
Qed.
Lemma evp_agV : forall lv w ps', PMCUR.evp (hl_segs L) M1 V lv w ps' -> PMCUR.evp (hl_segs L) M2 V lv w ps'.
Proof. intros lv w ps' (e & H1 & H2). exists e. split; [exact (ev_at_agV e H1) | exact H2]. Qed.
Lemma STOPOK_agV : forall ps1, PSOX.STOPOK I ps1 M1 -> PSOX.STOPOK I ps1 M2.
Proof. intros ps1 H Hm. destruct (H Hm) as [X|(X & Y)]; [left; exact X | right; split; [exact X | exact (evp_agV _ _ _ Y)]]. Qed.
Lemma PTR_agV : forall pc ps1 code, PSOX.PTR I pc ps1 code M1 -> PSOX.PTR I pc ps1 code M2.
Proof. intros pc ps1 code H Hc. destruct (H Hc) as (H1 & H2). split; [exact H1 | exact (STOPOK_agV _ H2)]. Qed.
Lemma REL_agV : forall ps1 code, PSOX.REL I ps1 code M1 -> PSOX.REL I ps1 code M2.
Proof.
  intros ps1 code (R1 & R2 & R3 & (R4 & R5)). split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  intros Hc Hm. destruct (R5 Hc Hm) as [X|(X & Y)]; [left; exact X | right; split; [exact X | exact (evp_agV _ _ _ Y)]].
Qed.
End MvV.

Lemma CORE_mv : forall i Ex (M1 M2 : mem) mw ps1 code g1 LBx FFx LKx crx Ax Mx Vx,
  ri_inv HI LBx FFx LKx crx Ax Mx Vx -> In (bptrI i Ex, bcapI i Ex) LBx -> In (sbI i Ex, scapI i Ex) LBx -> PML.wf_ps ps1 ->
  (forall a, SUPP (bptrI i Ex) (bcapI i Ex) (sbI i Ex) (scapI i Ex) a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  PSOX.CORE I i Ex M1 mw ps1 code g1 -> PSOX.CORE I i Ex M2 mw ps1 code g1.
Proof.
  intros i Ex M1 M2 mw ps1 code g1 LBx FFx LKx crx Ax Mx Vx HHx INb INs WF AG CO.
  pose proof (PSOX.c_blk _ _ _ _ _ _ _ _ CO) as CB. unfold PML.ps_blocks in CB. injection CB as Esc Esb Ebc Ebp.
  assert (HG : g1 <> PML.LS0) by (destruct (PSOX.c_g _ _ _ _ _ _ _ _ CO) as [-> | [-> _]]; [exact (PSOI.iHG I) | apply PSSC.regJ_nz]).
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
  - exact (PSOX.c_lv _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_blk _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_na _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_wl _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_e0 _ _ _ _ _ _ _ _ CO).
Qed.
Lemma POSTP_mv : forall i Ex (M1 M2 : mem) LBx FFx LKx crx Ax Mx Vx,
  ri_inv HI LBx FFx LKx crx Ax Mx Vx -> In (bptrI i Ex, bcapI i Ex) LBx -> In (sbI i Ex, scapI i Ex) LBx ->
  (forall a, SUPP (bptrI i Ex) (bcapI i Ex) (sbI i Ex) (scapI i Ex) a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  PSOX.POSTP I i Ex M1 -> PSOX.POSTP I i Ex M2.
Proof.
  intros i Ex M1 M2 LBx FFx LKx crx Ax Mx Vx HHx INb INs AG (ps1 & code & g1 & CO & WF & MO & RL).
  exists ps1, code, g1. split; [exact (CORE_mv i Ex M1 M2 _ ps1 code g1 _ _ _ _ _ _ _ HHx INb INs (proj1 WF) AG CO)|]. split; [exact WF|]. split; [exact MO | exact (REL_mv M1 M2 _ _ _ _ AG _ _ RL)].
Qed.
End F.
