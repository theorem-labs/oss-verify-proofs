(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA PtKitB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_psome_casan_T.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsoInstCA PsoSemA PsoSemCA PsoKnCA PsoBaseCA PsoKnOkCA PsoAuxCA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSOC.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_casan.

Module PSOAT.
Section A.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation LK := (PSOI.iLK I).   Local Abbreviation cr := (PSOI.icr I).   Local Abbreviation A := (PSOI.iA I).
Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).      Local Abbreviation V := (PSOI.iV I).     Local Abbreviation E := (PSOI.iE I).     Local Abbreviation B := (PSOI.iB I).
Local Abbreviation ps := (PSOI.ips I).   Local Abbreviation R := (PSOI.iR I).      Local Abbreviation M := (PSOI.iM I).     Local Abbreviation model := (PSOI.imodel I).
Local Abbreviation ch := (PSOI.ich I).   Local Abbreviation winb := (PSOI.iwinb I).
Local Abbreviation HIok := (PSOI.iHIok I). Local Abbreviation LAY := (PSOI.iLAY I). Local Abbreviation HH := (PSOI.iHH I).
Local Abbreviation E0 := (PSOI.E0 I).      Local Abbreviation LB := (PSOI.LB I).     Local Abbreviation win := (PSOI.win I).
Local Abbreviation wp0 := (PSOI.wp0 I).    Local Abbreviation we0 := (PSOI.we0 I).   Local Abbreviation wlen := (PSOI.wlen I). Local Abbreviation chg := (PSOI.chg I).
Local Abbreviation bcap := (PSOI.bcap I).  Local Abbreviation k0 := (PSOI.k0 I).     Local Abbreviation bptr := (PSOI.bptr I). Local Abbreviation buf := (PSOI.buf I).   Local Abbreviation size0 := (PSOI.size0 I).
Local Abbreviation sb := (PSOI.sb I).      Local Abbreviation scap := (PSOI.scap I). Local Abbreviation stack := (PSOI.stack I). Local Abbreviation slen := (PSOI.slen I).
Local Abbreviation level := (PSOI.level I). Local Abbreviation st0 := (PSOI.st0 I).  Local Abbreviation sst0 := (PSOI.sst0 I). Local Abbreviation nst0 := (PSOI.nst0 I). Local Abbreviation done0 := (PSOI.done0 I).
Local Abbreviation segs := (hl_segs L).
Local Abbreviation Mv := (CCA.vis A model M).

Definition xWP : expr := APC.esub (APC.eadd (EVar 36) (EVar 32)) (EVar 46).

Lemma SWID : forall q, PML.ps_set_win q (PML.ps_win q) = q. Proof. intros []; reflexivity. Qed.
Lemma KH0 : PSOKK.knh I E0 M A model FF LK cr ps (PML.ps_win ps) bptr bcap sb scap
              (EVar 53) PSOK.WE xWP (EVar 48) (EVar 49) (EVar 50) (ELit 1) (EVar 52) (EVar 54) (EVar 55) (EVar 56) (EVar 57) (EVar 58) (EVar 59).
Proof.
  pose_facts I. pose_U I.
  assert (UV : forall n z, bv_unsigned (ev E0 n) = z -> CL5A.uv E0 (EVar n) = z) by (intros n z Hn; unfold CL5A.uv; cbn [edenot]; exact Hn).
  constructor; try reflexivity.
  - exact HH.
  - intros x Hx; exact Hx.
  - rewrite SWID. exact (PSOI.iHPA I).
  - exact (PSOI.iHPSH I).
  - exact (proj1 (PSOI.iHWF I)).
  - clear - BC1. lia.
  - clear - BB1 BB2 BB3. unfold PSOI.size0, PSOI.buf in BB1. lia.
  - exact (UV _ _ U10).
  - exact (UV _ _ U11).
  - exact (UV _ _ U12).
  - exact (UV _ _ U2).
  - exact (UV _ _ U32).
  - exact (UV _ _ U34).
  - exact (UV _ _ U35).
  - exact (UV _ _ U36).
  - rewrite (UV _ _ U53). unfold PSOI.level in *. rewrite Z.mod_small; [reflexivity | clear - WF7; lia].
  - unfold PSOK.WE. rewrite uv_eadd, (UV _ _ U36), (UV _ _ U32). change (PSOI.whi (PML.ps_win ps)) with we0.
    rewrite Z.mod_small; [clear - WI6; lia | clear - WI0 WI1 WI2; lia].
  - unfold xWP. rewrite uv_esub, uv_eadd, (UV _ _ U36), (UV _ _ U32), (UV _ _ U46). rewrite (Z.mod_small (wp0 + wlen)) by (clear - WI0 WI1 WI2; lia).
    replace (wp0 + wlen - wlen) with wp0 by (clear; lia). change (PSOI.wlo (PML.ps_win ps)) with wp0. rewrite Z.mod_small by (clear - WI0 WI1 WI2; lia). reflexivity.
  - rewrite (UV _ _ U48). unfold PSOI.st0 in *. rewrite Z.mod_small; [reflexivity | clear - WF9; lia].
  - exact (UV _ _ U49).
  - exact (UV _ _ U50).
  - rewrite (PSOI.iHMORE I). cbn [PML.b2z]. apply uv_lit. clear; lia.
  - exact (UV _ _ U52).
  - exact (UV _ _ U54).
  - exact (UV _ _ U55).
  - exact (UV _ _ U56).
  - exact (UV _ _ U57).
  - exact (UV _ _ U58).
  - exact (UV _ _ U59).
Qed.

Lemma VIS0 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar ([(bptr, bcap); (sb, scap)] ++ LBo) FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) ->
  ahid A model (Z_to_bv 64 a) = false.
Proof. intros a H1 H2 H3. eapply PSOKK.VIS; [exact KH0 | exact H1 | exact H2 | exact H3]. Qed.
Lemma VISP0 : forall k n, 0 <= k -> k + n <= 272 -> CL5A.visr (ahid A model) (P + k) n.
Proof. intros k n H1 H2. eapply PSOKK.VISP; [exact KH0 | exact H1 | exact H2]. Qed.
Lemma VISE0 : forall k n, 0 <= k -> k + n <= 16 -> CL5A.visr (ahid A model) (E + k) n.
Proof. intros k n H1 H2. eapply PSOKK.VISE; [exact KH0 | exact H1 | exact H2]. Qed.
Lemma VISV0 : CL5A.visr (ahid A model) V 8.
Proof. eapply PSOKK.VISV; exact KH0. Qed.
Lemma VISB0 : forall u n, In (u, n) ([(bptr, bcap); (sb, scap)] ++ LBo) -> CL5A.visr (ahid A model) u n.
Proof. intros u n H1. eapply PSOKK.VISB; [exact KH0 | exact H1]. Qed.
Lemma VISBS0 : forall u n a, In (u, n) ([(bptr, bcap); (sb, scap)] ++ LBo) -> in_shadow_of u n a -> ahid A model (Z_to_bv 64 a) = false.
Proof. intros u n a H1 H2. eapply PSOKK.VISBS; [exact KH0 | exact H1 | exact H2]. Qed.

Lemma UVn : forall n z, bv_unsigned (ev E0 n) = z -> CL5A.uv E0 (EVar n) = z.
Proof. intros n z Hn; unfold CL5A.uv; cbn [edenot]; exact Hn. Qed.
Lemma UL0 : forall z, 0 <= z < 2 ^ 64 -> CL5A.uv E0 (ELit z) = z.
Proof. intros z Hz; exact (uv_lit E0 z Hz). Qed.

Lemma ISLOT_ok : forall a, In a ISLOTS -> (forall x, in_shadow_of a 8 x -> byte_at M x 0) /\ shadow_allowed A a 8.
Proof.
  intros a Ha. pose proof (PSOI.iPOI I) as POI. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  apply (PSOI.iISH I _ _ _ _ _ _ _ HH a 8).
  - rewrite ILO. unfold ISLOTS, VT_FUNC, VT_VISITOR in Ha. cbn [In] in Ha. clear - Ha. lia.
  - rewrite IHI. unfold ISLOTS, VT_FUNC, VT_VISITOR in Ha. cbn [In] in Ha. clear - Ha. lia.
  - clear; lia.
  - apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) POI r Hr) as X. exact (proj1 (Forall_forall _ _) X a Ha).
Qed.

Lemma KOBJ_ok : Forall (kentry_ok segs E0 Mv) PSOK.KOBJ.
Proof.
  pose_facts I. pose_U I. pose proof KH0 as KH. pose proof (PSOKK.FX KH) as FXX. destruct FXX as [FP FV FE FFS FB FS FBS FW Fps Fimg].
  pose proof (UVn _ _ U10) as UV10. pose proof (UVn _ _ U11) as UV11. pose proof (UVn _ _ U12) as UV12. pose proof (UVn _ _ U2) as UV2. pose proof (UVn _ _ U33) as UV33.
  pose proof (PSOI.iHVIS I) as HVIS. unfold PMLA.vis_at, PMLA.u64 in HVIS. pose proof (PSOI.iHEC I) as (HE0 & HdefE & _).
  pose proof (PSOI.iHsp32 I) as Hsp32. pose proof (PSOI.PDEFM I) as PDEF.
  pose proof (PSOI.iAP1 I) as AP1. pose proof (PSOI.iAP2 I) as AP2. pose proof (PSOI.iAP3 I) as AP3. unfold PMLA.apart in AP1, AP2, AP3.
  assert (LYI0 : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
    by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
  assert (VS : CL5A.visr (ahid A model) (sp - 10496) 10496).
  { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
    apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hq S2 CL. lia. }
  assert (SLOTZ : forall a, In a ISLOTS -> kentry_ok segs E0 Mv (KZero (SA (ELit 0) (a / 8 + SB)) (ELit 1))).
  { intros a Ha. destruct (ISLOT_ok a Ha) as [BZ BA]. unfold ISLOTS, VT_FUNC, VT_VISITOR in Ha. cbn [In] in Ha.
    assert (ISX : in_shadow_of a 8 (a / 8 + SB)).
    { unfold in_shadow_of, S, SB. destruct Ha as [<-|[<-|[<-|[<-|[]]]]]; cbn; clear; lia. }
    eapply CL5A.kzero_intro with (A := a / 8 + SB) (N := 1); [reflexivity | reflexivity | | | |].
    - unfold SB. destruct Ha as [<-|[<-|[<-|[<-|[]]]]]; cbn; clear; lia.
    - unfold SB. destruct Ha as [<-|[<-|[<-|[<-|[]]]]]; cbn; clear; lia.
    - unfold SB. destruct Ha as [<-|[<-|[<-|[<-|[]]]]]; cbn; clear; lia.
    - intros jj Hjj. replace (a / 8 + SB + jj) with (a / 8 + SB) by (clear - Hjj; lia).
      apply CL5A.byte_vis; [apply CHA.vis_allowed; exact (BA _ ISX) | exact (BZ _ ISX)]. }
  assert (STAT : forall K, CHA.static_chk GT.SCELLS GT.GLO GT.GHI K = true -> kentry_ok segs E0 Mv K)
    by (intros K HK; exact (CHA.static_sound L ar C HI HIok LYI0 GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI (SCOK I) (GOTOK I) _ _ _ _ _ _ _ E0 K HH HK)).
  destruct FP as (P0 & P1 & P8' & P2 & P3 & P4 & P5). destruct FV as (V0 & V1' & V8' & V2' & V3 & V4). destruct FE as (E0' & E1 & E8' & E2 & E3 & E4).
  destruct FFS as (FS0 & FS1 & FS2 & FS3 & FS4 & FS5 & FS6). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
  unfold PSOK.KOBJ. fold Mv. set (Hv := ahid A model).
  change Mv with (mrestrict Hv M).

  apply Forall_cons; [apply (KIMG I); [exact (IRM I) | clear; lia | clear; lia]|].
  apply Forall_cons; [apply STAT; reflexivity|].
  apply Forall_cons; [apply STAT; reflexivity|].
  apply Forall_cons; [exact (SLOTZ (VT_FUNC + 48) ltac:(unfold ISLOTS; left; reflexivity))|].
  apply Forall_cons; [exact (SLOTZ (VT_VISITOR + 56) ltac:(unfold ISLOTS; right; left; reflexivity))|].
  apply Forall_cons; [exact (SLOTZ (VT_VISITOR + 104) ltac:(unfold ISLOTS; right; right; left; reflexivity))|].
  apply Forall_cons; [exact (SLOTZ (VT_VISITOR + 112) ltac:(unfold ISLOTS; right; right; right; left; reflexivity))|].
  apply Forall_cons; [apply (KIMG I); [exact (IRM I) | clear; lia | clear; lia]|].
  apply Forall_cons; [apply (KIMG I); [exact (IRM I) | clear; lia | clear; lia]|].

  assert (VOB : forall o n, CL5A.ainfr FF o n -> 0 < n -> CL5A.visr Hv o n /\ (forall a, in_shadow_of o n a -> Hv (Z_to_bv 64 a) = false)).
  { intros o n Hfr Hn. split.
    - intros q Hq. destruct (CL5A.infr_wok L ar LB FF sp 0 o n (o + q) RFx Hfr ltac:(clear - Hq; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3).
    - intros a Ha. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o n a RFx Hfr Hn Ha) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  destruct (VOB P 272 Pfr ltac:(clear; lia)) as (VP & VSP). destruct (VOB E 16 Efr ltac:(clear; lia)) as (VE & VSE). destruct (VOB V 48 Vfr ltac:(clear; lia)) as (VV & VSV).
  change (272 / 8) with 34 in Psh. change (16 / 8) with 2 in Esh. change (48 / 8) with 6 in Vsh.
  pose proof (Z_div_mod_eq_full P 8) as PDV. rewrite P8, Z.add_0_r in PDV.
  assert (PK : forall k, (P + k) / 8 = P / 8 + k / 8) by (intros k; rewrite PDV at 1; rewrite Z.mul_comm, Z.div_add_l by (clear; lia); reflexivity).
  assert (USHP : forall k, 0 <= k <= 264 -> kentry_ok segs E0 (mrestrict Hv M) (KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) k) (ELit 3)) 2147450880) (ELit 1))).
  { intros k Hk. apply (CL5A.shz_intro segs E0 (mrestrict Hv M) _ 1 (P + k)); [rewrite uv_eaddz, UV10; apply Z.mod_small; clear - Hk P0 P1; lia | clear; lia | clear - P0 P1 Hk; lia |].
    intros j Hj. unfold S. rewrite (PK k). replace (P / 8 + k / 8 + SB + j) with (S P + k / 8) by (unfold S; clear - Hj; lia).
    assert (K8 : 0 <= k / 8 < 34) by (split; [apply Z.div_pos; clear - Hk; lia | apply Z.div_lt_upper_bound; clear - Hk; lia]).
    apply CL5A.byte_vis; [apply VSP; apply (CL5A.shreg_in_shadow P 34); [exact P8 | clear; lia | unfold S, SB; clear - K8; lia] | exact (Psh (k / 8) K8)]. }
  apply Forall_cons; [apply (PSOKK.KWR segs E0 Hv M (EVar 10) 0 (ELit 272) P 272 UV10 (UL0 272 ltac:(clear; lia))); [clear - P0 P1; lia | clear - P0 P1; lia | clear - P0 P1; lia
     | rewrite Z.add_0_r; exact VP | rewrite Z.add_0_r; exact PDEF]|].
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ UV10); clear - P2 FS0 P1 P5 FS5; lia|].
  apply Forall_cons; [apply (PSOKK.KA segs E0 _ _ _ _ UV10); [clear; lia | exact P8']|].
  apply Forall_cons; [apply (CL5A.shz_intro segs E0 (mrestrict Hv M) _ 34 P UV10); [clear; lia | clear - P0 P1; lia |];
    intros j Hj; apply CL5A.byte_vis; [apply VSP; apply (CL5A.shreg_in_shadow P 34); [exact P8 | clear; lia | unfold S, SB; clear - Hj; lia] | exact (Psh j Hj)]|].
  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (ELit 0) 2147446784 (ELit 17592186048512) (EVar 10) 0 (ELit 272) 0 17592186048512 P 272 (UL0 0 ltac:(clear; lia)) (UL0 17592186048512 ltac:(clear; lia)) UV10 (UL0 272 ltac:(clear; lia)));
    clear - P4; lia|].
  apply Forall_cons; [apply (USHP 209); clear; lia|].
  apply Forall_cons; [apply (USHP 210); clear; lia|].
  apply Forall_cons; [apply (USHP 211); clear; lia|].
  apply Forall_cons; [apply (USHP 212); clear; lia|].
  apply Forall_cons; [apply (USHP 213); clear; lia|].
  apply Forall_cons; [apply (USHP 220); clear; lia|].

  apply Forall_cons; [apply (PSOKK.KW64 segs E0 Hv M (EVar 11) 0 (ELit 1365216) V 1365216 UV11 (UL0 1365216 ltac:(clear; lia))); [clear - V0 V1'; lia | clear - V0 V1'; lia | rewrite Z.add_0_r; exact (fun q Hq => VV q ltac:(clear - Hq; lia)) | rewrite Z.add_0_r; exact (proj1 HVIS)]|].
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ UV11); clear - V2' FS0 V1' VR4 FS5; lia|].
  apply Forall_cons; [apply (PSOKK.KA segs E0 _ _ _ _ UV11); [clear; lia | exact V8']|].
  apply Forall_cons; [apply (CL5A.shz_intro segs E0 (mrestrict Hv M) _ 1 V UV11); [clear; lia | clear - V0 V1'; lia |];
    intros j Hj; apply CL5A.byte_vis; [apply VSV; apply (CL5A.shreg_in_shadow V 6); [exact V8 | clear; lia | unfold S, SB; clear - Hj; lia] | exact (Vsh j ltac:(clear - Hj; lia))]|].
  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (ELit 0) 2147446784 (ELit 17592186048512) (EVar 11) 0 (ELit 8) 0 17592186048512 V 8 (UL0 0 ltac:(clear; lia)) (UL0 17592186048512 ltac:(clear; lia)) UV11 (UL0 8 ltac:(clear; lia)));
    clear - V4; lia|].

  apply Forall_cons; [apply (PSOKK.KWR segs E0 Hv M (EVar 12) 0 (ELit 16) E 16 UV12 (UL0 16 ltac:(clear; lia))); [clear - E0' E1; lia | clear - E0' E1; lia | clear - E0' E1; lia
     | rewrite Z.add_0_r; exact VE | rewrite Z.add_0_r; exact HdefE]|].
  apply Forall_cons; [apply (PSOKK.KU segs E0 Hv M (EVar 12) 0 (ELit 16) E 16 UV12 (UL0 16 ltac:(clear; lia))); [clear - E0' E1; lia | clear - E0' E1; lia | clear - E0' E1; lia
     | rewrite Z.add_0_r; exact VE | rewrite Z.add_0_r; exact HdefE]|].
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ UV12); clear - E2 FS0 E1 Q4 FS5; lia|].
  apply Forall_cons; [apply (PSOKK.KA segs E0 _ _ _ _ UV12); [clear; lia | exact E8']|].
  apply Forall_cons; [apply (CL5A.shz_intro segs E0 (mrestrict Hv M) _ 2 E UV12); [clear; lia | clear - E0' E1; lia |];
    intros j Hj; apply CL5A.byte_vis; [apply VSE; apply (CL5A.shreg_in_shadow E 2); [exact E8 | clear; lia | unfold S, SB; clear - Hj; lia] | exact (Esh j Hj)]|].
  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (ELit 0) 2147446784 (ELit 17592186048512) (EVar 12) 0 (ELit 16) 0 17592186048512 E 16 (UL0 0 ltac:(clear; lia)) (UL0 17592186048512 ltac:(clear; lia)) UV12 (UL0 16 ltac:(clear; lia)));
    clear - E4; lia|].

  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ UV33); clear - BB1 BB2 BB3 BLT; unfold PSOI.size0 in *; pose proof (Zle_0_nat (length (PSOI.buf I))); lia|].

  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ UV2); clear - S2 S3 CL SP1; lia|].
  apply Forall_cons; [apply (PSOKK.KA segs E0 _ _ _ _ UV2); [clear; lia | exact Hsp32]|].
  apply Forall_cons; [apply (PSOKK.KWR segs E0 Hv M (EVar 2) (-10496) (ELit 10496) sp 10496 UV2 (UL0 10496 ltac:(clear; lia))); [clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia
     | replace (sp + -10496) with (sp - 10496) by (clear; lia); exact VS | replace (sp + -10496) with (sp - 10496) by (clear; lia); exact S5]|].
  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (EVar 2) (-10496) (ELit 10496) (EVar 10) 0 (ELit 272) sp 10496 P 272 UV2 (UL0 10496 ltac:(clear; lia)) UV10 (UL0 272 ltac:(clear; lia))); clear - P3 FS1 FS3; lia|].
  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (EVar 2) (-10496) (ELit 10496) (EVar 12) 0 (ELit 16) sp 10496 E 16 UV2 (UL0 10496 ltac:(clear; lia)) UV12 (UL0 16 ltac:(clear; lia))); clear - E3 FS1 FS3; lia|].
  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (EVar 2) (-10496) (ELit 10496) (EVar 11) 0 (ELit 8) sp 10496 V 8 UV2 (UL0 10496 ltac:(clear; lia)) UV11 (UL0 8 ltac:(clear; lia))); clear - V3 FS1 FS3; lia|].

  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (EVar 10) 0 (ELit 272) (EVar 12) 0 (ELit 16) P 272 E 16 UV10 (UL0 272 ltac:(clear; lia)) UV12 (UL0 16 ltac:(clear; lia))); clear - AP2; lia|].
  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (EVar 10) 0 (ELit 272) (EVar 11) 0 (ELit 8) P 272 V 8 UV10 (UL0 272 ltac:(clear; lia)) UV11 (UL0 8 ltac:(clear; lia))); clear - AP1; lia|].
  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (EVar 12) 0 (ELit 16) (EVar 11) 0 (ELit 8) E 16 V 8 UV12 (UL0 16 ltac:(clear; lia)) UV11 (UL0 8 ltac:(clear; lia))); clear - AP3; lia|].

  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (EVar 2) (-10496) (ELit 10496) (EVar 11) 8 (ELit 40) sp 10496 V 40 UV2 (UL0 10496 ltac:(clear; lia)) UV11 (UL0 40 ltac:(clear; lia))); clear - V3 FS1 FS3; lia|].
  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (EVar 10) 0 (ELit 272) (EVar 11) 8 (ELit 40) P 272 V 40 UV10 (UL0 272 ltac:(clear; lia)) UV11 (UL0 40 ltac:(clear; lia))); clear - AP1; lia|].
  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (EVar 12) 0 (ELit 16) (EVar 11) 8 (ELit 40) E 16 V 40 UV12 (UL0 16 ltac:(clear; lia)) UV11 (UL0 40 ltac:(clear; lia))); clear - AP3; lia|].
  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (EVar 11) 0 (ELit 8) (EVar 11) 8 (ELit 40) V 8 V 40 UV11 (UL0 8 ltac:(clear; lia)) UV11 (UL0 40 ltac:(clear; lia))); clear; lia|].
  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (ELit 0) 2147446784 (ELit 17592186048512) (EVar 11) 8 (ELit 40) 0 17592186048512 V 40 (UL0 0 ltac:(clear; lia)) (UL0 17592186048512 ltac:(clear; lia)) UV11 (UL0 40 ltac:(clear; lia))); clear - V4; lia|].
  apply Forall_nil.
Qed.

Lemma SHD_OBJ : forall x l1 o n, 0 <= x <= 2 ^ 47 - 2 ^ 23 -> 0 <= l1 <= 2048 -> 0 <= n -> (o + n <= 2147446784 \/ 17594333495296 <= o) ->
  x / 8 + SB + l1 <= o \/ o + n <= x / 8 + SB.
Proof.
  intros x l1 o n Hx Hl Hn Ho. assert (D : 0 <= x / 8 <= 2 ^ 44 - 2 ^ 20) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). unfold SB. lia.
Qed.
Lemma UPK0 : forall k, 0 <= k <= 272 -> CL5A.uv E0 (APC.eaddz (EVar 10) k) = P + k.
Proof. intros k Hk. eapply PSOKK.UPK; [exact KH0 | exact Hk]. Qed.

Lemma EC_ok : kentry_ok segs E0 Mv (KWord (SA (EVar 12) 0) 4 (ELit 0)).
Proof.
  pose_U I. pose proof (PSOI.iHEC I) as (HE0 & _ & _). unfold PMLA.u32 in HE0. pose proof (PSOKK.FX KH0) as FXX. destruct FXX as [_ _ FE _ _ _ _ _ _ _].
  destruct FE as (E0' & E1 & _). unfold CCA.vis.
  apply (PSOKK.KW32 segs E0 (ahid A model) M (EVar 12) 0 (ELit 0) E 0 (UVn _ _ U12) (UL0 0 ltac:(clear; lia))); [clear - E0' E1; lia | clear - E0' E1; lia
    | exact (VISE0 0 4 ltac:(clear; lia) ltac:(clear; lia)) | rewrite Z.add_0_r; exact HE0].
Qed.

Lemma STR_ok : Forall (kentry_ok segs E0 Mv) PSOK.STRANGES.
Proof.
  pose_facts I. pose_U I. unfold PSOK.STRANGES.
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ (UVn _ _ U48)); clear - WF9; lia|].
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ (UVn _ _ U49)); clear - WF1; lia|].
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ (UVn _ _ U50)); clear - WF2; lia|].
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ (UVn _ _ U52)); clear - WF8; lia|].
  apply Forall_nil.
Qed.

Lemma COMMON_ok : Forall (kentry_ok segs E0 Mv) PSOK.KN_COMMON.
Proof.
  unfold PSOK.KN_COMMON. apply Forall_app; split; [exact KOBJ_ok|].
  apply Forall_app; split; [apply Forall_cons; [exact EC_ok | apply Forall_nil]|].
  apply Forall_app; split; [exact (PSOKK.PCONST_ok KH0)|].
  apply Forall_app; split; [exact (PSOKK.BLOCKS_KN0_ok KH0) | exact STR_ok].
Qed.

Lemma PST_ok : Forall (kentry_ok segs E0 Mv) (PSOK.PSTATE (EVar 53) PSOK.WE xWP (EVar 48) (EVar 49) (EVar 50) (ELit 1) (EVar 52) (EVar 54) (EVar 55) (EVar 56) (EVar 57) (EVar 58) (EVar 59)).
Proof. exact (PSOKK.PSTATE_ok KH0). Qed.

Ltac uvx UVS := first [ exact UVS | apply UPK0; clear; lia | apply UL0; clear; lia ].
Lemma SURV_common : forall ent, In ent PSOK.SURV_N -> kentry_ok segs E0 Mv ent.
Proof.
  pose_facts I. pose_U I. pose proof (PSOKK.FX KH0) as FXX. destruct FXX as [FP FV FE FFS _ _ _ _ _ _].
  destruct FP as (P0 & P1 & P8' & P2 & P3 & P4 & P5). destruct FV as (V0 & V1' & V8' & V2' & V3 & V4). destruct FE as (E0' & E1 & E8' & E2 & E3 & E4).
  destruct FFS as (FS0 & FS1 & FS2 & FS3 & FS4 & FS5 & FS6). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
  pose proof (UVn _ _ U10) as UV10. pose proof (UVn _ _ U11) as UV11. pose proof (UVn _ _ U12) as UV12.
  intros ent Hin. unfold PSOK.SURV_N in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [<-|Hin]; [eapply PSOKK.KDsh1; [first [exact UV10 | exact UV11 | exact UV12 | apply UPK0; clear; lia]
                                                           | apply UL0; clear; lia | first [exact UV10 | exact UV12 | exact UV11 | apply UL0; clear; lia] | apply UL0; clear; lia |];
                                         apply SHD_OBJ; clear - P0 P1 P4 P5 E0' E1 E4 Q4 V0 V1' V4 VR4 FS5; lia |]).
  destruct Hin.
Qed.
Lemma SURVN_ok : Forall (kentry_ok segs E0 Mv) PSOK.SURV_N.
Proof. apply Forall_forall. exact SURV_common. Qed.

Section S.
Variables (p e : Z).
Hypothesis Hw : PML.ps_win ps = Some (p, e).
Lemma HwS : win = Some (p, e). Proof. exact Hw. Qed.

Record wfacts : Prop := WFS {
  w_p : wp0 = p;  w_e : we0 = e;  w_chg : chg = 2048;  w_inc : In (ch, 16384) LB;  w_ch1 : ch <= p;  w_ch2 : e <= ch + 16384;  w_def : L5.defined M p (e - p);
  w_sh : shadow_blk M ch 16384;  w_pe : p <= e;  w_k0 : 4096 <= ch;  w_k16 : ch mod 16 = 0;  w_k4 : ch + 16384 <= ahl_ceil ar;
  w_k6 : ch + 16384 <= 2147446784 \/ 17594333495296 <= ch;  w_img : ch + 16384 <= 65536 \/ 7024640 <= ch;
  w_fs : ch + 16384 <= ar_fs ar \/ ar_fs ar + FS_BYTES <= ch;  w_len : wlen = e - p }.
Lemma WF0 : wfacts.
Proof.
  pose_facts I. pose proof HwS as Hw'. pose_win I Hw'.
  pose proof (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as [WBx _]. destruct (WBx (ch, 16384) INC) as (_ & _ & _ & _ & _ & _ & D9). cbn [fst snd] in D9.
  unfold hid in KC6. rewrite ILO, IHI in KC1.
  constructor; first [assumption | (unfold PSOI.wlen; rewrite WP0E, WE0E; reflexivity)].
Qed.

Lemma SURVS_ok : Forall (kentry_ok segs E0 Mv) PSOK.SURV_S.
Proof.
  pose_facts I. pose_U I. pose proof (PSOKK.FX KH0) as FXX. destruct FXX as [FP FV FE FFS _ _ _ _ _ _].
  destruct FP as (P0 & P1 & P8' & P2 & P3 & P4 & P5). destruct FV as (V0 & V1' & V8' & V2' & V3 & V4). destruct FE as (E0' & E1 & E8' & E2 & E3 & E4).
  destruct FFS as (FS0 & FS1 & FS2 & FS3 & FS4 & FS5 & FS6). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
  destruct WF0 as [WP WE WCHG WINC WCH1 WCH2 WDEF WSH WPE WK0 WK16 WK4 WK6 WIMG WFS WLEN]. unfold FS_BYTES in WFS.
  pose proof (UVn _ _ U10) as UV10. pose proof (UVn _ _ U11) as UV11. pose proof (UVn _ _ U12) as UV12.
  pose proof (UVn _ _ U32) as UV32. pose proof (UVn _ _ U34) as UV34. pose proof (UVn _ _ U35) as UV35. pose proof (UVn _ _ U36) as UV36.
  apply Forall_forall. intros ent Hin. unfold PSOK.SURV_S in Hin. cbn [In] in Hin.

  do 3 (destruct Hin as [<-|Hin];
    [eapply (PSOKK.KD segs E0 _ (EVar 36) 0 (EVar 32) (ELit 0) _ (ELit _) wp0 wlen 0 _ UV36 UV32 (UL0 0 ltac:(clear; lia))); [apply UL0; clear; lia | clear - WP WE WCH1 WCH2 WIMG WLEN WI6; lia] |]).

  destruct Hin as [<-|Hin];
    [apply (PSOKK.KD segs E0 _ (EVar 36) 0 (EVar 32) (EVar 11) 8 (ELit 40) wp0 wlen V 40 UV36 UV32 UV11 (UL0 40 ltac:(clear; lia))); clear - WP WPE WCH1 WCH2 WFS V2' V3 WLEN; lia |].
  repeat (destruct Hin as [<-|Hin]; [eapply PSOKK.KDsh1; [first [exact UV10 | exact UV11 | exact UV12 | exact UV34 | apply UPK0; clear; lia]
                                                           | first [exact UV35 | apply UL0; clear; lia] | first [exact UV10 | exact UV12 | exact UV11 | apply UL0; clear; lia] | apply UL0; clear; lia |];
                                         apply SHD_OBJ; clear - P0 P1 P4 P5 E0' E1 E4 Q4 V0 V1' V4 VR4 FS5 WK0 WK4 WI5 WCHG; lia |]).
  destruct Hin.
Qed.

Lemma WIN_ok : Forall (kentry_ok segs E0 Mv) PSOK.WIN_KN.
Proof.
  pose_facts I. pose_U I. pose proof (PSOKK.FX KH0) as FXX. destruct FXX as [FP FV FE FFS _ _ _ _ _ _].
  destruct FP as (P0 & P1 & P8' & P2 & P3 & P4 & P5). destruct FE as (E0' & E1 & E8' & E2 & E3 & E4).
  destruct FFS as (FS0 & FS1 & FS2 & FS3 & FS4 & FS5 & FS6). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
  destruct WF0 as [WP WE WCHG WINC WCH1 WCH2 WDEF WSH WPE WK0 WK16 WK4 WK6 WIMG WFS WLEN]. unfold FS_BYTES in WFS.
  pose proof (UVn _ _ U10) as UV10. pose proof (UVn _ _ U12) as UV12. pose proof (UVn _ _ U2) as UV2.
  pose proof (UVn _ _ U32) as UV32. pose proof (UVn _ _ U34) as UV34. pose proof (UVn _ _ U35) as UV35. pose proof (UVn _ _ U36) as UV36.
  pose proof (PSOI.iHwinb I) as (WBS & WBL0). change (PSOI.wlo (PML.ps_win ps)) with wp0 in WBS.
  assert (WBL : Z.of_nat (length winb) = wlen) by exact WBL0. clear WBL0.
  set (Hv := ahid A model).
  assert (VCH : CL5A.visr Hv ch 16384) by exact (VISB0 ch 16384 WINC).
  assert (VW : CL5A.visr Hv wp0 wlen) by (apply (CL5A.visr_sub Hv ch 16384); [exact VCH | clear - WP WCH1; lia | clear - WP WE WCH2 WLEN WI6; lia]).
  assert (DW : L5.defined M wp0 wlen) by (rewrite WP, WLEN; exact WDEF).
  unfold PSOK.WIN_KN, CCA.vis. fold Hv.

  apply Forall_cons; [apply (CL5.kblob_intro segs E0 (mrestrict Hv M) _ _ 1 wp0 winb)|].
  { unfold estart. cbn [a_base a_off edenot]. rewrite U36. clear; lia. }
  { unfold elenZ. cbn [edenot]. rewrite U32, WBL. reflexivity. }
  { clear - WI0; lia. }
  { rewrite WBL. clear - WI0 WI1 WI2; lia. }
  { clear - WI0 WI1 WI2; lia. }
  { reflexivity. }
  { apply (CL5A.bytes_vis segs Hv M wp0 winb); [clear - WI0; lia | rewrite WBL; clear - WI0 WI1 WI2; lia | rewrite WBL; exact VW | exact WBS]. }
  { rewrite WBL. apply (CL5A.defined_vis Hv M wp0 _ VW DW). }

  apply Forall_cons; [apply (PSOKK.KU segs E0 Hv M (EVar 36) 0 (EVar 32) wp0 wlen UV36 UV32); [clear - WI0; lia | clear - WI0 WI1; lia | clear - WI0 WI1 WI2; lia
     | rewrite Z.add_0_r; exact VW | rewrite Z.add_0_r; exact DW]|].

  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ UV32); clear - WI2; lia|].
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ UV36); clear - WP WK0 WCH1 WCH2 WPE WK4 FS5 SP1; lia|].

  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (ELit 0) 2147446784 (ELit 17592186048512) (EVar 36) 0 (EVar 32) 0 17592186048512 wp0 wlen (UL0 0 ltac:(clear; lia)) (UL0 17592186048512 ltac:(clear; lia)) UV36 UV32);
    clear - WK6 WP WCH1 WCH2 WLEN WE WI6; lia|].

  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ UV34); clear - WK0 WK4 FS5 SP1; lia|].
  apply Forall_cons; [apply (PSOKK.KA segs E0 _ _ _ _ UV34); [clear; lia | exact WK16]|].
  apply Forall_cons; [apply (PSOKK.KZsh segs E0 Hv M (EVar 34) (EVar 35) ch chg UV34 UV35); [clear - WI5; lia | clear - WK0 WK4 FS5 SP1; lia | | rewrite WCHG; exact (proj1 WSH)]|].
  { intros j Hj. apply (VISBS0 ch 16384 _ WINC). unfold in_shadow_of, S. rewrite WCHG in Hj. clear - Hj. lia. }
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ UV35); clear - WCHG; lia|].

  apply Forall_cons; [apply (PSOKK.KR segs E0 _ (APC.esub (EVar 36) (EVar 34)) (wp0 - ch)); [rewrite uv_esub, UV36, UV34; apply Z.mod_small; clear - WP WCH1 WCH2 WPE; lia | clear - WP WCH1 WCH2 WPE; lia]|].
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ (wp0 - ch + wlen)); [|clear - WP WCH1 WCH2 WPE WLEN WE; lia]|].
  { rewrite uv_esub, uv_eadd, uv_esub, UV36, UV34, UV32, (UL0 0 ltac:(clear; lia)). rewrite (Z.mod_small (wp0 - ch)) by (clear - WP WCH1 WCH2 WPE; lia).
    rewrite (Z.mod_small (wp0 - ch + wlen)) by (clear - WP WCH1 WCH2 WPE WLEN WE; lia). rewrite Z.sub_0_r. apply Z.mod_small. clear - WP WCH1 WCH2 WPE WLEN WE; lia. }

  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (EVar 2) (-10496) (ELit 10496) (EVar 36) 0 (EVar 32) sp 10496 wp0 wlen UV2 (UL0 10496 ltac:(clear; lia)) UV36 UV32);
    clear - WP WE WCH2 WK4 WLEN WI6 S2; lia|].
  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (EVar 10) 0 (ELit 272) (EVar 36) 0 (EVar 32) P 272 wp0 wlen UV10 (UL0 272 ltac:(clear; lia)) UV36 UV32);
    clear - WP WE WCH1 WCH2 WLEN WI6 WFS P2 P3; lia|].
  apply Forall_cons; [apply (PSOKK.KD segs E0 _ (EVar 12) 0 (ELit 16) (EVar 36) 0 (EVar 32) E 16 wp0 wlen UV12 (UL0 16 ltac:(clear; lia)) UV36 UV32);
    clear - WP WE WCH1 WCH2 WLEN WI6 WFS E2 E3; lia|].

  do 3 (apply Forall_cons; [eapply (PSOKK.KD segs E0 _ (EVar 36) 0 (EVar 32) (ELit 0) _ (ELit _) wp0 wlen 0 _ UV36 UV32 (UL0 0 ltac:(clear; lia))); [apply UL0; clear; lia | clear - WP WE WCH1 WCH2 WIMG WLEN WI6; lia] |]).
  apply Forall_nil.
Qed.

Lemma TAILS_ok : Forall (kentry_ok segs E0 Mv)
  [KRange (EVar 46) 0 16384; KRange (APC.esub (EVar 32) (EVar 46)) 0 0; KRange (APC.esub (EVar 33) (APC.eadd (EVar 55) (EVar 46))) 0 67108864; KUnk (SA (EVar 2) (-10496)) (ELit 10496)].
Proof.
  pose_facts I. pose_U I. pose proof (UVn _ _ U32) as UV32. pose proof (UVn _ _ U33) as UV33. pose proof (UVn _ _ U46) as UV46. pose proof (UVn _ _ U55) as UV55. pose proof (UVn _ _ U2) as UV2.
  set (Hv := ahid A model). unfold CCA.vis. fold Hv.
  assert (SZ0 : 0 <= size0) by (unfold PSOI.size0; clear; lia).
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ UV46); clear - WI2; lia|].
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ 0); [rewrite uv_esub, UV32, UV46, Z.sub_diag; reflexivity | clear; lia]|].
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ (B - (size0 + wlen))); [|clear - BB1 BB2 BB3 SZ0; lia]|].
  { rewrite uv_esub, uv_eadd, UV33, UV55, UV46. rewrite (Z.mod_small (size0 + wlen)) by (clear - BB1 BB2 BB3 SZ0; lia). apply Z.mod_small. clear - BB1 BB2 BB3 SZ0; lia. }
  apply Forall_cons; [|apply Forall_nil].
  assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> Hv (Z_to_bv 64 a) = false)
    by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
  assert (VS : CL5A.visr Hv (sp - 10496) 10496).
  { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
    apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hq S2 CL. lia. }
  apply (PSOKK.KU segs E0 Hv M (EVar 2) (-10496) (ELit 10496) sp 10496 UV2 (UL0 10496 ltac:(clear; lia))); [clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia
     | replace (sp + -10496) with (sp - 10496) by (clear; lia); exact VS | replace (sp + -10496) with (sp - 10496) by (clear; lia); exact S5].
Qed.

Lemma At0S : CC.At segs GT.t0 E0 R Mv.
Proof.
  split; [exact (regs_ok_id R _ _)|]. unfold know_ok. assert (T0 : CC.cp_know GT.t0 = PSOK.KN0S) by exact PSOA.t0_kn. rewrite T0. unfold PSOK.KN0S.
  apply Forall_app; split; [exact COMMON_ok|]. apply Forall_app; split; [exact SURVS_ok|]. apply Forall_app; split; [exact PST_ok|].
  apply Forall_app; split; [exact WIN_ok | exact TAILS_ok].
Qed.
End S.

Lemma TAILN_ok : PML.ps_win ps = None -> Forall (kentry_ok segs E0 Mv)
  [KRange (EVar 36) 0 0; KRange (EVar 32) 0 0; KRange (EVar 46) 0 0; KRange (APC.esub (EVar 33) (EVar 55)) 0 67108864; KUnk (SA (EVar 2) (-10496)) (ELit 10496)].
Proof.
  intros Hw. pose proof (PSOI.WNONE I Hw) as (W0 & W1 & W2 & W3 & W4).
  pose_facts I. pose_U I. pose proof (UVn _ _ U32) as UV32. pose proof (UVn _ _ U33) as UV33. pose proof (UVn _ _ U36) as UV36. pose proof (UVn _ _ U46) as UV46.
  pose proof (UVn _ _ U55) as UV55. pose proof (UVn _ _ U2) as UV2.
  set (Hv := ahid A model). unfold CCA.vis. fold Hv.
  assert (SZ0 : 0 <= size0) by (unfold PSOI.size0; clear; lia).
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ UV36); clear - W0; lia|].
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ UV32); clear - W2; lia|].
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ _ _ _ UV46); clear - W2; lia|].
  apply Forall_cons; [apply (PSOKK.KR segs E0 _ _ (B - size0)); [rewrite uv_esub, UV33, UV55; apply Z.mod_small; clear - BB1 BB2 BB3 SZ0; lia | clear - BB1 BB2 BB3 SZ0; lia]|].
  apply Forall_cons; [|apply Forall_nil].
  assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> Hv (Z_to_bv 64 a) = false)
    by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
  assert (VS : CL5A.visr Hv (sp - 10496) 10496).
  { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
    apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hq S2 CL. lia. }
  apply (PSOKK.KU segs E0 Hv M (EVar 2) (-10496) (ELit 10496) sp 10496 UV2 (UL0 10496 ltac:(clear; lia))); [clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia
     | replace (sp + -10496) with (sp - 10496) by (clear; lia); exact VS | replace (sp + -10496) with (sp - 10496) by (clear; lia); exact S5].
Qed.

Lemma At0 : forall p e, PML.ps_win (PSOI.ips I) = Some (p, e) -> CC.At (hl_segs (PSOI.iL I)) GT.t0 (PSOI.E0 I) (PSOI.iR I) (CCA.vis (PSOI.iA I) (PSOI.imodel I) (PSOI.iM I)).
Proof. intros p e Hw. exact (At0S p e Hw). Qed.
Lemma At1 : PML.ps_win (PSOI.ips I) = None -> CC.At (hl_segs (PSOI.iL I)) GT.t1 (PSOI.E0 I) (PSOI.iR I) (CCA.vis (PSOI.iA I) (PSOI.imodel I) (PSOI.iM I)).
Proof.
  intros Hw. split; [exact (regs_ok_id R _ _)|]. unfold know_ok. assert (T1 : CC.cp_know GT.t1 = PSOK.KN0N) by exact PSOA.t1_kn. rewrite T1. unfold PSOK.KN0N.
  apply Forall_app; split; [exact COMMON_ok|]. apply Forall_app; split; [exact SURVN_ok|]. apply Forall_app; split; [exact PST_ok | exact (TAILN_ok Hw)].
Qed.
End A.
End PSOAT.
