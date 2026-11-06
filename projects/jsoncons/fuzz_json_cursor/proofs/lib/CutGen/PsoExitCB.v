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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsKitA PsoInstCB PsoSemA PsoSemCA PsoKnCB ParseSomeChkCB PsoBaseCB PsoXiCB PsoFrmCB.
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

Section X.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation LK := (PSOI.iLK I).   Local Abbreviation cr := (PSOI.icr I).   Local Abbreviation A := (PSOI.iA I).
Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).      Local Abbreviation V := (PSOI.iV I).     Local Abbreviation E := (PSOI.iE I).     Local Abbreviation B := (PSOI.iB I).
Local Abbreviation kx := (PSOI.ikx I).   Local Abbreviation bx := (PSOI.ibx I).    Local Abbreviation g := (PSOI.ig I).     Local Abbreviation ps := (PSOI.ips I).
Local Abbreviation R := (PSOI.iR I).     Local Abbreviation M := (PSOI.iM I).      Local Abbreviation model := (PSOI.imodel I). Local Abbreviation K := (PSOI.iK I).
Local Abbreviation r := (PSOI.ir I).
Local Abbreviation HIok := (PSOI.iHIok I). Local Abbreviation LAY := (PSOI.iLAY I). Local Abbreviation HH := (PSOI.iHH I).
Local Abbreviation E0 := (PSOI.E0 I).      Local Abbreviation LB := (PSOI.LB I).
Local Abbreviation WW := (WW I).            Local Abbreviation Wo := (Wo I).         Local Abbreviation Cred := (PSOX.Cred I). Local Abbreviation XI := (PSOX.XI I).
Local Abbreviation bptrI := (PSOX.bptrI).  Local Abbreviation bcapI := (PSOX.bcapI). Local Abbreviation sbI := (PSOX.sbI). Local Abbreviation scapI := (PSOX.scapI).

Lemma SUPP_geom : forall i E1 A1 M1 m1 a, (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 ->
  SUPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a ->
  let F := CL5A.uv E1 FE in
  0 <= a < 2 ^ 64 /\ a < sp - SCR /\ ~ (F <= a < F + 1024) /\ ~ in_shadow_of F 1024 a /\
  aclient L ar (CHA.curB LBo G.BLS i E1) (CHA.curF FF sp PSO.FFS i E1) (sp + PSO.CSP) 256 a /\ (PSOX.FLF I E1 -> a <> CL5A.uv E1 FLE).
Proof.
  intros i E1 A1 M1 m1 a Hi HA Ha. cbv zeta. pose_facts I.
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (HcB & HcF & HagE & F0 & F1 & F64 & F2 & F3 & F4 & FAP & (crX & LKX & HHX & _)).
  set (F := CL5A.uv E1 FE) in *. rewrite HcB, HcF.
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHX) as WFX. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFX) as RFX.
  assert (F8 : F mod 8 = 0) by (exact (CHA.mod8_of_64 _ F64)).

  pose proof (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHX) as [WB _].
  destruct (CHA.rf_fs _ _ _ _ RFx) as ((FQ0 & FQ1 & FQ2) & _ & _). unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in FQ1.
  assert (OBJ : forall o n, CL5A.ainfr FF o n -> 0 < n -> o <= a < o + n ->
            0 <= a < 2 ^ 64 /\ a < sp - SCR /\ ~ (F <= a < F + 1024) /\ ~ in_shadow_of F 1024 a /\
            aclient L ar ([(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] ++ LBo) ((F, 4, sp + PSO.CSP + 32) :: FF) (sp + PSO.CSP) 256 a /\ (PSOX.FLF I E1 -> a <> CL5A.uv E1 FLE)).
  { intros o n Hfr Hn Hx. destruct (CL5A.infr_rng L ar LB FF o n RFx Hfr Hn) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). pose proof Hfr as (f & Hf & G1 & G2).
    pose proof (FAP f Hf) as AF. destruct (CHA.rf_frm _ _ _ _ RFx f Hf) as (R1 & R2 & _). unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
    split; [clear - Hx X3 X6; lia|]. split; [unfold SCR; clear - Hx X4 S2; lia|]. split; [clear - Hx G1 G2 AF; lia|].
    split; [intros Hs; pose proof (SHR F 1024 a F0 ltac:(clear; lia) ltac:(clear - F1; lia) Hs) as RG; clear - RG Hx X5; lia|].
    split; [right; right; right; left; exists f; split; [right; exact Hf|]; clear - Hx G1 G2; lia|].
    intros [FLR FLNC] HX. apply FLNC. rewrite <- HX. right; right; right; left. exists f. split; [exact Hf|]. clear - G1 G2 Hx R1 R2. lia. }

  assert (BLK : forall u n, In (u, n) ([(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] ++ LBo) -> (u <= a < u + n \/ in_shadow_of u n a) ->
            0 <= a < 2 ^ 64 /\ a < sp - SCR /\ ~ (F <= a < F + 1024) /\ ~ in_shadow_of F 1024 a /\
            aclient L ar ([(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] ++ LBo) ((F, 4, sp + PSO.CSP + 32) :: FF) (sp + PSO.CSP) 256 a /\ (PSOX.FLF I E1 -> a <> CL5A.uv E1 FLE)).
  { intros u n Hun Hx. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFX (u, n) Hun) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _ & _ & _ & Dfap). cbn [fst snd] in D0, D1, D16, D3, D4, D5, D6, D7, Dfap.
    pose proof (Dfap (F, 4, sp + PSO.CSP + 32) ltac:(apply in_or_app; left; left; reflexivity)) as AF. cbn [ff_addr ff_class fst snd] in AF. change (ff_bytes 4) with 1024 in AF.
    destruct (WB (u, n) Hun) as (_ & _ & _ & _ & _ & _ & B7). cbn [fst snd] in B7. unfold FS_BYTES in B7.
    unfold BIGSHADOW_LO, BIGSHADOW_HI in D6. destruct Hx as [Hx|Hx].
    - split; [clear - Hx D5 D7; lia|]. split; [unfold SCR; clear - Hx D4 S2; lia|]. split; [clear - Hx AF; lia|].
      split; [intros Hs; pose proof (SHR F 1024 a F0 ltac:(clear; lia) ltac:(clear - F1; lia) Hs) as RG; clear - RG Hx D6; lia|].
      split; [left; exists (u, n); split; [exact Hun | cbn [fst snd]; exact Hx]|].
      intros [FLR FLNC] HX. unfold FS_BYTES in FLR. clear - Hx HX FLR B7. lia.
    - pose proof (SHR u n a D5 D3 D7 Hx) as RG. split; [clear - RG; lia|]. split; [unfold SCR; clear - RG S2 CL; lia|].
      split; [clear - RG F2; lia|].
      split; [intros Hs; exact (CL5A.sh_apart2 u n F 1024 a D5 F0 D3 ltac:(clear; lia) (CHA.mod8_of_16 _ D16) F8 ltac:(clear - AF; lia) Hx Hs)|].
      split; [do 6 right; exists (u, n); split; [exact Hun | exact Hx]|].
      intros [FLR FLNC] HX. unfold FS_BYTES in FLR. clear - RG HX FLR FQ0 FQ1. lia. }
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[(u & n & Hun & Ha)|Ha]]]]]]]].
  - exact (OBJ P 272 Pfr ltac:(clear; lia) Ha).
  - exact (OBJ E 16 Efr ltac:(clear; lia) Ha).
  - exact (BLK _ _ (or_introl eq_refl) (or_introl Ha)).
  - exact (BLK _ _ (or_introl eq_refl) (or_intror Ha)).
  - exact (BLK _ _ (or_intror (or_introl eq_refl)) (or_introl Ha)).
  - exact (BLK _ _ (or_intror (or_introl eq_refl)) (or_intror Ha)).
  - shelve.
  - exact (BLK u n ltac:(apply in_or_app; right; exact Hun) Ha).
  - exact (OBJ V 48 Vfr ltac:(clear; lia) ltac:(clear - Ha; lia)).
  Unshelve.
  pose proof (STATIC_lo I a Ha) as RG. split; [clear - RG; lia|]. split; [unfold SCR; clear - RG S2 CL FSLO; lia|]. split; [clear - RG F3 FSLO; lia|].
    split; [intros Hs; pose proof (SHR F 1024 a F0 ltac:(clear; lia) ltac:(clear - F1; lia) Hs) as RG2; clear - RG RG2; lia|].
    split; [exact (STCL I a _ _ _ _ Ha)|]. intros [FLR FLNC] HX. clear - RG HX FLR FSLO. lia.
Qed.

Lemma SUPP_stretch : forall i c ps0 E1 A1 M1 m1 E' R' M' m' Fx hb, (2 <= i < PSO.NCUT)%nat -> nth_error G.CPS i = Some c ->
  AAMB I i E1 A1 M1 m1 -> PSOX.FLF I E1 -> env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  CC.cp_F c = PSO.F_STK :: Fx -> (forall rg, In rg Fx -> rg = (FE, 0, ELit hb) \/ rg = (FLE, 0, ELit 1)) -> 0 <= hb <= 1024 ->
  forall a, SUPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof.
  intros i c ps0 E1 A1 M1 m1 E' R' M' m' Fx hb Hi Hci HA HFL Hag HLF HF HFx Hhb a Ha.
  destruct (SUPP_geom i E1 A1 M1 m1 a Hi HA Ha) as (RG & X1 & X2 & X3 & X4 & X5).
  pose proof (X5 HFL) as NFL.
  assert (NX : (66 <= CC.cp_nx c)%nat).
  { assert (X : forallb (fun k => Nat.leb 66 (CC.cp_nx (nth k G.CPS CA.dummy_cp))) (seq 2 (PSO.NCUT - 2)) = true) by vmc_refl.
    rewrite forallb_forall in X. specialize (X i ltac:(apply in_seq; clear - Hi; lia)). apply Nat.leb_le in X. rewrite (nth_error_nth _ _ CA.dummy_cp Hci) in X. exact X. }
  pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6 i c E1 E' A1 M1 m1 HA (G.NF_le i c Hci) Hag) as HagE'.
  pose_U I. assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite <- (proj1 HagE' 2%nat ltac:(unfold GT.NF, Cut_psome_cboth_T.NF; clear; lia)); exact U2).
  assert (W65 : CL5A.uv E' FE = CL5A.uv E1 FE) by (unfold CL5A.uv, FE, FEV; cbn [edenot]; rewrite <- (proj1 Hag 65%nat) by (clear - NX; lia); reflexivity).
  assert (W60 : CL5A.uv E' FLE = CL5A.uv E1 FLE) by (unfold CL5A.uv, FLE, FLV; cbn [edenot]; rewrite <- (proj1 Hag 60%nat) by (clear - NX; lia); reflexivity).
  apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). rewrite HF. unfold SGP.outside. apply Forall_forall. intros rg Hrg. rewrite L5.unsigned_lit by exact RG.
  destruct Hrg as [<-|Hrg].
  - unfold PSO.F_STK, estart, elenZ. cbn [fst snd a_base a_off edenot]. rewrite W2. unfold SCR. rewrite u64_of_Z by (clear; lia). unfold SCR in X1. clear - X1. lia.
  - destruct (HFx rg Hrg) as [-> | ->]; unfold estart, elenZ; cbn [fst snd a_base a_off edenot]; rewrite u64_of_Z by (clear - Hhb; lia).
    + change (bv_unsigned (edenot E' FE)) with (CL5A.uv E' FE). rewrite W65. clear - X2 Hhb. lia.
    + change (bv_unsigned (edenot E' FLE)) with (CL5A.uv E' FLE). rewrite W60. clear - NFL. lia.
Qed.

Lemma L_SETSH : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther SETSH) -> PSO.setsh_chk i c k ps0 = true ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  intros i c k ps0 IL CHK. pose_facts I. pose_U I. pose proof (PSOI.VV I) as (_ & V4 & _).
  assert (Hci : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hc & _); exact Hc).
  unfold PSO.setsh_chk in CHK. unfold PSO.ret_of in CHK.
  destruct (CH2.ret_of G.RETS i k) as [j|] eqn:Hret'; [|discriminate CHK]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate CHK].
  apply andb_prop in CHK as [X Yfl]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y18]. apply andb_prop in X as [X YBeq].
  apply andb_prop in X as [X Ychk]. apply andb_prop in X as [X YFoot]. apply andb_prop in X as [X XF]. apply andb_prop in X as [X XKj]. apply andb_prop in X as [Y0 XKi].
  apply Z.eqb_eq in Y0. apply PSO.kind_eqb_eq in XKi. apply PSO.kind_eqb_eq in XKj. apply CBA.regions_eqb_eq in XF.
  destruct (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 256 0 (nth i G.BLS []) (nth i PSO.FFS []) [(CHA.SRL3 FE, SBz, ELit 128)] PSO.SETSH_NEWS None c ps0 cj
              (nth i G.BLS []) (nth i PSO.FFS []) (nth j G.BLS []) (nth j PSO.FFS [])) as [ci|] eqn:Hchk; [|discriminate Ychk].
  apply andb_prop in Ychk as [Ycsp Ynx]. apply Z.eqb_eq in Ycsp. apply Nat.leb_le in Ynx.
  pose proof (ge2_of_kind i c _ Hci XKi ltac:(discriminate)) as Hi. pose proof (ge2_of_kind j cj _ Hcj XKj ltac:(discriminate)) as Hj.
  intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI].
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (HcB & HcF & HagE & F0 & F1 & F64 & F2 & F3 & F4 & FAP & (crX & LKX & HHX & HCX)).
  set (F := CL5A.uv E1 FE) in *.
  pose proof (PSOX.xi_flf _ _ _ _ HXI (proj1 Hi)) as HFL. pose proof HFL as [HFL1 HFL2].
  assert (NX : (66 <= CC.cp_nx c)%nat).
  { assert (X : forallb (fun k0 => Nat.leb 66 (CC.cp_nx (nth k0 G.CPS CA.dummy_cp))) (seq 2 (PSO.NCUT - 2)) = true) by vmc_refl.
    rewrite forallb_forall in X. specialize (X i ltac:(apply in_seq; clear - Hi; lia)). apply Nat.leb_le in X. rewrite (nth_error_nth _ _ CA.dummy_cp Hci) in X. exact X. }
  assert (W60 : CL5A.uv E' FLE = CL5A.uv E1 FLE) by (unfold CL5A.uv, FLE, FLV; cbn [edenot]; rewrite <- (proj1 Hag 60%nat) by (clear - NX; lia); reflexivity).
  refine (CRSH2.setsh_leaf L ar C HI HIok (LYI I) (LYR I) (LYB I) GT.NF E0 M model A LBo FF LK sp G.HDECL WW Wo G.BLS PSO.FFS Cred 6 (STKF I) SCRP NF32 U2 V4 (WINC I) (WOKo I) (PSOI.iHffrs I) (CRS_OKo I) (WRS_OK I) (IMG_OK I)
            G.CPS K PMSA.fp_ok (DEF0 I) S6 GT.SCELLS GT.GLO GT.GHI (SCOK I) (GOTOK I) XI (PSOI.iHKnil I)
            SETSH 245 256 (PSOI.iSETSH I) 256 PSO.SETSH_NEWS i c ps0 j cj ci FE 4 PSO.CSP FLE (EAlu Instr.ALU_ADD (CHA.SRL3 FE) (ELit SBz))
            Hcj _ Y0 ltac:(clear; lia) (ffs_i i Hi) _ YBeq ltac:(clear; lia) Y10 _ Y11 _ Yfl (le_n _) _
            fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH ltac:(rewrite W60; unfold FS_BYTES; exact HFL1) _ _).
  - exact Hchk.
  - rewrite (ffs_i i Hi), (ffs_i j Hj). reflexivity.
  - intros Ex. unfold CL5A.uv. cbn [edenot]. rewrite AX2S.u_add64. unfold CHA.SRL3. rewrite (CL5A.elen_srl3' Ex FE : bv_unsigned (edenot Ex (EAlu Instr.ALU_SRL FE (ELit 3))) = CL5A.uv Ex FE / 8).
    unfold SBz, SB. rewrite u64_of_Z by (clear; lia). pose proof (CL5A.uv_range Ex FE) as UR. unfold CL5A.uv in UR |- *.
    apply Z.mod_small. split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; clear - UR; lia | clear; lia]|]. pose proof (CL5A.div8_le _ _ (proj2 (conj (proj1 UR) (Z.lt_le_incl _ _ (proj2 UR))))) as D8.
    change (2 ^ 64 / 8) with 2305843009213693952 in D8. clear - D8. lia.
  -
    assert (ST : forallb (CHA.static_chk GT.SCELLS GT.GLO GT.GHI) PSOK.STATICS_UAR = true) by vmc_refl. rewrite forallb_forall in ST.
    intros X0 HX0. unfold PSO.SETSH_NEWS in HX0. apply in_app_or in HX0. destruct HX0 as [HX0|HX0]; [left; exact (ST X0 HX0)|].
    cbn [In] in HX0. destruct HX0 as [<-|[<-|[]]]; [right; left; reflexivity | right; right; reflexivity].
  -
    intros Ea Eb crx HC HagC. unfold PSOX.Cred in HC |- *.
    destruct (BLKAG i c Ea Eb Hci HagC) as (_ & B2 & _ & B4).
    assert (BQ : PSO.blk0 j = PSO.blk0 i /\ PSO.blk1 j = PSO.blk1 i) by (apply CH2.blocks_eqb_eq in YBeq; unfold PSO.blk0, PSO.blk1; rewrite YBeq; split; reflexivity).
    destruct BQ as [BQ0 BQ1]. unfold PSOX.bcapI, PSOX.scapI in *. rewrite BQ0, BQ1, B2, B4. exact HC.
  - intros Ea Eb Hg. unfold CL5A.uv, FLE, FLV. cbn [edenot]. rewrite (proj1 Hg 60%nat) by (clear - NX; lia). reflexivity.
  -
    cbv zeta. intros R2 M2 m2 A2 LK2 crx HRP HP1 HP3 HPOI HA2 Hmo2 Hrt2 HH2.
    pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
    set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
    assert (HagEE2 : env_agree (CC.cp_nx c) E1 E2) by (eapply CC.env_agree_trans; [exact Hag|]; eapply CC.env_agree_le; [exact Hag2 | exact Ynx]).
    destruct (BLKAG i c E1 E2 Hci HagEE2) as (BG1 & BG2 & BG3 & BG4).
    assert (BQ : PSO.blk0 j = PSO.blk0 i /\ PSO.blk1 j = PSO.blk1 i) by (apply CH2.blocks_eqb_eq in YBeq; unfold PSO.blk0, PSO.blk1; rewrite YBeq; split; reflexivity).
    destruct BQ as [BQ0 BQ1].
    assert (QJ : bptrI j E2 = bptrI i E1 /\ bcapI j E2 = bcapI i E1 /\ sbI j E2 = sbI i E1 /\ scapI j E2 = scapI i E1).
    { unfold PSOX.bptrI, PSOX.bcapI, PSOX.sbI, PSOX.scapI in *. rewrite BQ0, BQ1. exact (conj BG1 (conj BG2 (conj BG3 BG4))). }
    destruct QJ as (QJ1 & QJ2 & QJ3 & QJ4).

    assert (AG1 : forall a, SUPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { exact (SUPP_stretch i c ps0 E1 A1 M1 m1 E' R' M' m' [(FE, 0, ELit 8)] 8 Hi Hci HA HFL Hag HLF XF ltac:(intros rg [<-|[]]; left; reflexivity) ltac:(clear; lia)). }
    assert (AG2 : forall a, SUPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
    { intros a Ha. destruct (SUPP_geom i E1 A1 M1 m1 a Hi HA Ha) as (RG & X1 & X2 & X3 & X4 & _). apply HP1. rewrite Ycsp.
      split; [exact RG|]. split; [exact X4|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. apply X3.
      apply (CL5A.blk_shadow_in F 1024 a (CHA.mod8_of_64 _ F64) ltac:(clear; lia)). change ((1024 + 7) / 8) with 128. change (ff_bytes 4 / 8) with 128 in Hin. exact Hin. }
    constructor; try (intros Hk; rewrite XKj in Hk; first [discriminate Hk | destruct Hk as [Hk|Hk]; discriminate Hk]); try (intros pc0 Hk; rewrite XKj in Hk; discriminate Hk).
    + intros _. unfold PSOX.FLF. replace (CL5A.uv E2 FLE) with (CL5A.uv E1 FLE); [exact HFL|].
      unfold CL5A.uv, FLE, FLV. cbn [edenot]. rewrite (proj1 HagEE2 60%nat) by (clear - NX; lia). reflexivity.
    + intros _. pose proof (PSOX.xi_post _ _ _ _ HXI (or_introl XKi)) as HPOST.
      destruct HPOST as (ps1 & code & g1 & CO & WF & MO & RL).
      exists ps1, code, g1. split; [|split; [exact WF | split; [exact MO | exact (REL_mv I M1 M2 _ _ _ _ (fun a Ha => eq_trans (AG2 a Ha) (AG1 a Ha)) _ _ RL)]]].

      pose proof (CORE_mv I i E1 M1 M2 (PML.ps_win ps1) ps1 code g1 _ _ _ _ _ _ _ HHX (or_introl eq_refl) (or_intror (or_introl eq_refl)) (proj1 WF)
                    ltac:(intros a Ha; rewrite (AG2 a Ha); exact (AG1 a Ha)) CO) as CO2.
      constructor.
      * exact (PSOX.c_pa _ _ _ _ _ _ _ _ CO2).
      * left. split; [rewrite XKj; reflexivity | reflexivity].
      * exact (PSOX.c_sh _ _ _ _ _ _ _ _ CO2).
      * exact (PSOX.c_win _ _ _ _ _ _ _ _ CO2).
      * exact (PSOX.c_bb _ _ _ _ _ _ _ _ CO2).
      * exact (PSOX.c_ec _ _ _ _ _ _ _ _ CO2).
      * exact (PSOX.c_ls _ _ _ _ _ _ _ _ CO2).
      * exact (PSOX.c_g _ _ _ _ _ _ _ _ CO2).
      * exact (PSOX.c_lv _ _ _ _ _ _ _ _ CO2).
      * rewrite QJ1, QJ2, QJ3, QJ4. exact (PSOX.c_blk _ _ _ _ _ _ _ _ CO2).
      * intros _ Hr. exfalso. rewrite XKj in Hr. cbn in Hr. discriminate Hr.
      * intros _ Hw. exfalso. rewrite XKj in Hw. cbn in Hw. discriminate Hw.
      * intros Hu. exfalso. rewrite (u0_retire j cj Hcj (or_intror XKj)) in Hu. discriminate Hu.
Qed.

Lemma ret_at : CL.is_ret_at RSEGS RET.
Proof. CL.solve_is_ret. Qed.

Lemma L_EXIT : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther RET) -> PSO.exit_chk i c ps0 = true ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  intros i c k ps0 IL CHK. pose_facts I. pose_U I.
  assert (Hci : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hc & _); exact Hc).
  unfold PSO.exit_chk in CHK.
  apply andb_prop in CHK as [X Yrc]. apply andb_prop in X as [X XF]. apply andb_prop in X as [X Yfl0]. apply andb_prop in X as [XK Xbase].
  apply PSO.kind_eqb_eq in XK. apply CBA.regions_eqb_eq in XF.
  destruct (CHA.retire_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i PSO.FFS [])) as [fle|] eqn:Hrc; [|discriminate Yrc]. apply expr_eqb_eq in Yrc. subst fle.
  pose proof (ge2_of_kind i c _ Hci XK ltac:(discriminate)) as Hi.
  intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI].
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (HcB & HcF & HagE & F0 & F1 & F64 & F2 & F3 & F4 & FAP & (crX & LKX & HHX & HCX)).
  set (F := CL5A.uv E1 FE) in *.
  pose proof (PSOX.xi_flf _ _ _ _ HXI (proj1 Hi)) as HFL. pose proof HFL as [HFL1 HFL2].
  pose proof (PSOX.xi_post _ _ _ _ HXI (or_intror XK)) as HPOST.
  assert (NX : (66 <= CC.cp_nx c)%nat).
  { assert (X : forallb (fun k0 => Nat.leb 66 (CC.cp_nx (nth k0 G.CPS CA.dummy_cp))) (seq 2 (PSO.NCUT - 2)) = true) by vmc_refl.
    rewrite forallb_forall in X. specialize (X i ltac:(apply in_seq; clear - Hi; lia)). apply Nat.leb_le in X. rewrite (nth_error_nth _ _ CA.dummy_cp Hci) in X. exact X. }
  refine (CRA.exit_retire L ar C HI HIok (LYI I) (LYB I) (LYN I) GT.NF E0 M model A LBo FF LK sp G.HDECL WW Wo G.BLS PSO.FFS Cred 6 (STKF I) SCRP NF32 U2 (WINC I) (WOKo I) (WRS_OK I) K (DEF0 I) R r (PSOI.EV0 I) (PSOI.iHra I) (PSOI.iHraok I)
            RET i c ps0 FLE FE 4 PSO.CSP ltac:(rewrite LS; exact ret_at) Xbase (ffs_i i Hi) _ Yfl0 fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF HFL1 HFL2 _).
  { exact Hrc. }
  intros m2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE'.

  assert (AG1 : forall a, SUPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { exact (SUPP_stretch i c ps0 E1 A1 M1 m1 E' R' M' m' [(FE, 0, ELit 8); (FLE, 0, ELit 1)] 8 Hi Hci HA HFL Hag HLF XF
             ltac:(intros rg [<-|[<-|[]]]; [left | right]; reflexivity) ltac:(clear; lia)). }
  pose proof (POSTP_mv I i E1 M1 M' _ _ _ _ _ _ _ HHX (or_introl eq_refl) (or_intror (or_introl eq_refl)) AG1 HPOST) as (ps1 & code & g1 & CO & WF & MO & RL).
  rewrite HcB in HH1.
  pose proof (PSOX.c_blk _ _ _ _ _ _ _ _ CO) as CB.
  unfold PMSA.cfg in *.
  apply (PSOI.iHcont I fx' R' M' m2 (PML.ps_blocks ps1 ++ LBo) cr1 LBo WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | rewrite CB; exact HH1].
  exists ps1, code, g1.
  pose proof (PSOX.c_mw _ _ _ _ _ _ _ _ CO) as MW.
  assert (PA : PMLA.parser_at (hl_segs L) IC M' P ps1).
  { pose proof (PSOX.c_pa _ _ _ _ _ _ _ _ CO) as PA0. rewrite (PSOX.set_win_self ps1) in PA0. exact PA0. }
  split; [exact PA|]. split; [exact (PSOX.c_sh _ _ _ _ _ _ _ _ CO)|]. split; [exact WF|].
  split.
  {
    pose proof (PSOX.c_win _ _ _ _ _ _ _ _ CO) as WN. unfold PSOX.WIN in WN. unfold PMLA.win_okA.
    destruct (PSOI.win I) as [[p0 e0]|] eqn:Hw.
    - unfold PSOI.win in Hw. rewrite Hw in WN. destruct WN as (p1 & W1 & W2). rewrite W1. pose_win I Hw.
      exists (PSOI.ich I). split; [exact INCo|]. split; [clear - CH1 W2 WP0E; lia|]. split; [clear - CH2 WE0E; lia|].
      assert (AGc : forall a, (PSOI.ich I <= a < PSOI.ich I + 16384 \/ in_shadow_of (PSOI.ich I) 16384 a) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha. pose proof (KLB I _ _ a INCo Ha) as Ka. pose proof HA as (_ & _ & _ & _ & _ & HKEPT & _). rewrite <- (HKEPT a Ka).
        apply AG1. do 7 right. left. exists (PSOI.ich I), 16384. split; [exact INCo | exact Ha]. }
      split.
      + intros y Hy Hn. rewrite (AGc (p1 + y) ltac:(left; clear - Hy CH1 CH2 W2 WP0E WE0E; lia)) in Hn.
        exact (WDEF (p1 - p0 + y) ltac:(clear - Hy W2 WP0E WE0E; lia) ltac:(replace (p0 + (p1 - p0 + y)) with (p1 + y) by (clear; lia); exact Hn)).
      + apply (PTA.shadow_blk_ag M M' (fun a => PSOI.ich I <= a < PSOI.ich I + 16384 \/ in_shadow_of (PSOI.ich I) 16384 a) AGc (PSOI.ich I) 16384 ltac:(clear; lia) ltac:(intros a Ha; right; exact Ha) KC8 CHSH).
    - unfold PSOI.win in Hw. rewrite Hw in WN. rewrite WN. exact Logic.I. }
  split; [exact (PSOX.c_bb _ _ _ _ _ _ _ _ CO)|]. split; [exact (PSOX.c_ec _ _ _ _ _ _ _ _ CO)|]. split; [exact MO|].
  split; [exact (PSOX.c_ls _ _ _ _ _ _ _ _ CO)|]. split; [exact (PSOX.c_g _ _ _ _ _ _ _ _ CO)|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  {
    pose proof (PSSA.wf_shape ps1 (proj1 WF)) as (_ & _ & _ & SC5). unfold PML.ps_blocks in CB. injection CB as E4 E3 E2 E1'.
    apply (proj2 (pcredit_bufcred I cr1 ps1 SC5)). unfold PSOX.Cred in HC1.
    first [rewrite E3, E1' | rewrite E4, E2 | rewrite E2, E4 | rewrite E1', E3]; try exact HC1.
    all: revert HC1; rewrite <- ?E1', <- ?E2, <- ?E3, <- ?E4; intros HC1; exact HC1. }
  destruct RL as (RL1 & RL2 & RL3 & RL4). split; [exact (conj RL1 (conj RL2 RL3)) | exact RL4].
Qed.

End X.
