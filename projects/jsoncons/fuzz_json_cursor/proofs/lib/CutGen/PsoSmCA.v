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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA PtKitB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_psome_casan_T Cut_psome_casan_D Cut_psome_casan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsKitA PsSmA2 PsoInstCA PsoSemA PsoSemCA PsoKnCA ParseSomeChkCA PsoBaseCA PsoXiCA PsoFrmCA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_casan.

Lemma u0_sm_all : forallb (fun i => negb (PSO.kind_eqb (PSO.kind_of i) PSO.KSm) || PSO.u0 i)%bool (seq 0 PSO.NCUT) = true.
Proof. vmc_refl. Qed.
Lemma u0_sm : forall i c, nth_error G.CPS i = Some c -> PSO.kind_of i = PSO.KSm -> PSO.u0 i = true.
Proof.
  intros i c Hci Hk. assert (Hi : (i < PSO.NCUT)%nat) by (rewrite <- len_cps; apply nth_error_Some; rewrite Hci; discriminate).
  pose proof (proj1 (forallb_forall _ _) u0_sm_all i ltac:(apply in_seq; clear - Hi; lia)) as X. cbv beta in X. rewrite Hk in X. cbn [negb orb PSO.kind_eqb] in X. exact X.
Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation LK := (PSOI.iLK I).   Local Abbreviation cr := (PSOI.icr I).   Local Abbreviation A := (PSOI.iA I).
Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).      Local Abbreviation V := (PSOI.iV I).     Local Abbreviation E := (PSOI.iE I).     Local Abbreviation B := (PSOI.iB I).
Local Abbreviation kx := (PSOI.ikx I).   Local Abbreviation bx := (PSOI.ibx I).    Local Abbreviation g := (PSOI.ig I).     Local Abbreviation ps := (PSOI.ips I).
Local Abbreviation R := (PSOI.iR I).     Local Abbreviation M := (PSOI.iM I).      Local Abbreviation model := (PSOI.imodel I). Local Abbreviation K := (PSOI.iK I).
Local Abbreviation HIok := (PSOI.iHIok I). Local Abbreviation LAY := (PSOI.iLAY I). Local Abbreviation HH := (PSOI.iHH I).
Local Abbreviation E0 := (PSOI.E0 I).      Local Abbreviation LB := (PSOI.LB I).
Local Abbreviation WW := (WW I).            Local Abbreviation Wo := (Wo I).         Local Abbreviation Cred := (PSOX.Cred I). Local Abbreviation XI := (PSOX.XI I).
Local Abbreviation bptrI := (PSOX.bptrI).  Local Abbreviation bcapI := (PSOX.bcapI). Local Abbreviation sbI := (PSOX.sbI). Local Abbreviation scapI := (PSOX.scapI).

Lemma U8EQ : forall (M1 M2 : mem) a v, L5.u8_at (hl_segs L) M1 a v -> L5.u8_at (hl_segs L) M2 a v -> hl_img_hi L <= a -> 0 <= a < 2 ^ 64 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof.
  intros M1 M2 a v H1 H2 Ha Hr. unfold L5.u8_at in H1, H2. cbn [rdn] in H1, H2.
  unfold seg_rom, memory_read in H1, H2. rewrite L5.unsigned_lit in H1, H2 by exact Hr. change (Z.of_N 1) with 1 in H1, H2.
  rewrite (find_segment1_none_above (hl_segs L) (hl_img_hi L) a (LYB I) Ha) in H1, H2.
  destruct (M1 (Z_to_bv 64 a)) as [b1|]; [|discriminate H1]. destruct (M2 (Z_to_bv 64 a)) as [b2|]; [|discriminate H2].
  cbn in H1, H2. injection H1 as H1. injection H2 as H2. rewrite <- H2 in H1. f_equal. symmetry. exact H1.
Qed.

Lemma entry_lt2_all : forallb (fun i => negb (PSO.kind_eqb (PSO.kind_of i) PSO.KEntry) || Nat.ltb i 2)%bool (seq 0 PSO.NCUT) = true.
Proof. vmc_refl. Qed.
Lemma entry_lt2 : forall i c, nth_error G.CPS i = Some c -> PSO.kind_of i = PSO.KEntry -> (i < 2)%nat.
Proof.
  intros i c Hci Hk. assert (Hi : (i < PSO.NCUT)%nat) by (rewrite <- len_cps; apply nth_error_Some; rewrite Hci; discriminate).
  pose proof (proj1 (forallb_forall _ _) entry_lt2_all i ltac:(apply in_seq; clear - Hi; lia)) as X. cbv beta in X. rewrite Hk in X. cbn [negb orb PSO.kind_eqb] in X.
  apply Nat.ltb_lt in X. exact X.
Qed.
Lemma BLK01 : nth 0 G.BLS [] = [(EVar 56, EMd Instr.M_MUL (ELit 2) (EVar 54)); (EVar 57, EVar 59)] /\ nth 1 G.BLS [] = nth 0 G.BLS [].
Proof. vm_compute. split; reflexivity. Qed.

Lemma ACL : forall a sp' scr',
  SUPP I (PSOI.bptr I) (PSOI.bcap I) (PSOI.sb I) (PSOI.scap I) a -> 0 <= a < 2 ^ 64 /\ aclient L ar LB FF sp' scr' a /\ a < sp - SCR.
Proof.
  pose_facts I. intros a sp' scr' Ha. unfold SCR.
  assert (FRI : forall o n, CL5A.ainfr FF o n -> 0 < n -> o <= a < o + n -> 0 <= a < 2 ^ 64 /\ aclient L ar LB FF sp' scr' a /\ a < sp - 10496).
  { intros o n Hfr Hn Hx. destruct (CL5A.infr_rng L ar LB FF o n RFx Hfr Hn) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). destruct Hfr as (f & Hf & G1 & G2).
    destruct (CHA.rf_frm _ _ _ _ RFx f Hf) as (R1 & R2 & R3 & R4 & R5).
    split; [clear - Hx X3 X6; lia|]. split; [right; right; right; left; exists f; split; [exact Hf|]; clear - Hx G1 G2 R5; lia|].
    clear - Hx X4 S2; lia. }
  assert (BLI : forall u n, In (u, n) LB -> (u <= a < u + n \/ in_shadow_of u n a) -> 0 <= a < 2 ^ 64 /\ aclient L ar LB FF sp' scr' a /\ a < sp - 10496).
  { intros u n Hun Hx. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (u, n) Hun) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _). cbn [fst snd] in D0, D1, D3, D4, D5, D7. destruct Hx as [Hx|Hx].
    - split; [clear - Hx D5 D7; lia|]. split; [left; exists (u, n); split; [exact Hun | cbn [fst snd]; exact Hx]|]. clear - Hx D4 S2; lia.
    - pose proof (SHR u n a D5 D3 D7 Hx) as RG. split; [clear - RG; lia|]. split; [do 6 right; exists (u, n); split; [exact Hun | cbn [fst snd]; exact Hx]|].
      clear - RG S2 CL; lia. }
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[(u & n & Hun & Ha)|Ha]]]]]]]].
  - exact (FRI P 272 Pfr ltac:(clear; lia) Ha).
  - exact (FRI E 16 Efr ltac:(clear; lia) Ha).
  - exact (BLI _ _ (INB I) (or_introl Ha)).
  - exact (BLI _ _ (INB I) (or_intror Ha)).
  - exact (BLI _ _ (INS I) (or_introl Ha)).
  - exact (BLI _ _ (INS I) (or_intror Ha)).
  - destruct (IMGCL I a Ha) as [RG CL']. split; [clear - RG; lia|]. split; [exact (CL' sp' scr')|]. clear - RG S2 CL FSLO; lia.
  - exact (BLI u n ltac:(unfold PSOI.LB; apply in_or_app; right; exact Hun) Ha).
  - exact (FRI V 48 Vfr ltac:(clear; lia) ltac:(clear - Ha; lia)).
Qed.

Lemma L_SM : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther SM4) -> PSO.sm_chk i c k ps0 = true ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  intros i c k ps0 IL CHK. pose_facts I. pose_U I. pose proof (PSOI.VV I) as (_ & V4 & _).
  assert (Hci : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hc & _); exact Hc).
  unfold PSO.sm_chk, PSO.ret_of in CHK.
  destruct (CH2.ret_of G.RETS i k) as [j|] eqn:Hret'; [|discriminate CHK]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate CHK].
  apply andb_prop in CHK as [X Y212]. apply andb_prop in X as [X Y211]. apply andb_prop in X as [X Y208].
  apply andb_prop in X as [X XF]. apply andb_prop in X as [X YBeq]. apply andb_prop in X as [X Ychk]. apply andb_prop in X as [X XKj]. apply andb_prop in X as [Y0 XKi].
  apply Z.eqb_eq in Y0. apply PSO.kind_eqb_eq in XKi. apply PSO.kind_eqb_eq in XKj. apply CBA.regions_eqb_eq in XF.
  destruct (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 1 (nth i G.BLS []) (nth i PSO.FFS []) [] (List.filter (PSO.sm_ok ps0) (CC.cp_know cj)) None c ps0 cj
              (nth i G.BLS []) (nth i PSO.FFS []) (nth j G.BLS []) (nth j PSO.FFS [])) as [ci|] eqn:Hchk; [|discriminate Ychk].
  apply andb_prop in Ychk as [Ynx Ycsp]. apply Nat.eqb_eq in Ynx. apply Z.eqb_eq in Ycsp.
  pose proof (entry_lt2 i c Hci XKi) as Hi2. pose proof (ge2_of_kind j cj _ Hcj XKj ltac:(discriminate)) as Hj.
  assert (FFS0 : nth i PSO.FFS [] = []) by (destruct i as [|[|i]]; [reflexivity | reflexivity | exfalso; clear - Hi2; lia]).
  assert (BLSi : nth i G.BLS [] = [(EVar 56, EMd Instr.M_MUL (ELit 2) (EVar 54)); (EVar 57, EVar 59)]) by (pose proof BLK01 as [B0 B1]; destruct i as [|[|i]]; [exact B0 | rewrite B1; exact B0 | exfalso; clear - Hi2; lia]).
  assert (BLSj : nth j G.BLS [] = nth i G.BLS []) by (apply CH2.blocks_eqb_eq in YBeq; exact YBeq).
  assert (LYH' : IMGHI <= hl_img_hi L /\ hl_img_lo L < FS_BYTES) by (rewrite ILO, IHI; unfold IMGHI, FS_BYTES; clear; lia).
  assert (NX : (60 <= CC.cp_nx c)%nat).
  { assert (X0 : forallb (fun k0 => Nat.leb 60 (CC.cp_nx (nth k0 G.CPS CA.dummy_cp))) (seq 0 2) = true) by vmc_refl.
    rewrite forallb_forall in X0. specialize (X0 i ltac:(apply in_seq; clear - Hi2; lia)). apply Nat.leb_le in X0. rewrite (nth_error_nth _ _ CA.dummy_cp Hci) in X0. exact X0. }
  intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI].
  destruct (PSOX.xi_entry _ _ _ _ HXI XKi) as [HagE60 HM1]. subst M1.
  pose proof (CRX2.smalloc_leaf_x L ar C HI HIok (LYI I) (LYR I) IMGHI LYH' GT.NF E0 M model A LBo FF LK sp G.HDECL WW Wo G.BLS PSO.FFS Cred 6 (STKF I) SCRP NF32 U2 V4 (WINC I) (WOKo I) (PSOI.iHffrs I) (CRS_OKo I) (WRS_OK I) (IMG_OK I)
                G.CPS K PMSA.fp_ok (DEF0 I) S6 GT.SCELLS GT.GLO GT.GHI (SCOK I) (GOTOK I) XI (PSOI.iHKnil I)
                (fun X0 => In X0 (PSO.ISHL ++ PSO.SMUSER)) 4 (List.filter (PSO.sm_ok ps0) (CC.cp_know cj)) i c ps0 j cj ci) as SML.
  rewrite (L5A.aly_scr_sm L C LAY), (PSOI.iSM4 I) in SML.
  refine (SML ltac:(vm_compute; repeat (first [left; reflexivity | right])) Hcj Hchk Y0 _ YBeq _ _ _ fx' E1 R1 A1 M m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _ _); clear SML.
  - rewrite (ffs_i j Hj), FFS0, Ynx, Ycsp. vm_compute. reflexivity.
  - intros X0 HX0. apply filter_In in HX0 as [_ HX0]. unfold PSO.sm_ok in HX0. rewrite Ynx, FFS0, BLSi. rewrite <- (proj1 BLK01).
    apply orb_prop in HX0. destruct HX0 as [HX0|HX0]; [left; exact HX0 | right; exact (CC.has_cell_In _ _ HX0)].
  - rewrite FFS0. cbn [length]. clear; lia.
  - intros Ea Eb crx HC HagC. unfold PSOX.Cred in HC |- *. destruct (BLKAG i c Ea Eb Hci HagC) as (_ & B2 & _ & B4).
    unfold PSOX.bcapI, PSOX.scapI, PSO.blk0, PSO.blk1 in *. rewrite BLSj, B2, B4. exact HC.
  -
    intros X0 R2 M2 m2 F fl LK' cr1 HX0 HRP Ha0r SMF HH2. rewrite Ynx, Ycsp in *.
    set (E2 := CH2.retEx E' 60 [Z_to_bv 64 fl] R2) in *.
    destruct SMF as [Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Zp]. change (ff_bytes 4) with 1024 in *.
    pose proof (CH2.retEx_agree E' 60 [Z_to_bv 64 fl] R2 : env_agree 60 E' E2) as Hag2.
    assert (HagE2 : env_agree 60 E0 E2) by (eapply CC.env_agree_trans; [exact HagE60 | eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact NX] | exact Hag2]]).
    assert (TV : forall v z, (v < 60)%nat -> bv_unsigned (ev E0 v) = z -> bv_unsigned (ev E2 v) = z) by (intros v z Hv Hz; rewrite <- (proj1 HagE2 v Hv); exact Hz).
    destruct (CHA.rf_fs _ _ _ _ RFx) as ((FQ0 & FQ1 & FQ2) & FQ3 & _). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in Z1, Z7, FQ1, FQ3.
    assert (FR : 0 <= F < 2 ^ 64) by (destruct Z1 as (G1 & G2 & _ & _ & G5); clear - G1 G2 FQ0 CL SP1 G5; lia).
    assert (T65 : bv_unsigned (ev E2 65) = F).
    { pose proof (CH2.retEx_a0 E' 60 [Z_to_bv 64 fl] R2) as G0. cbn [length Nat.add] in G0. unfold E2. rewrite G0, Ha0r. apply u64_of_Z. exact FR. }
    assert (T60 : bv_unsigned (ev E2 60) = fl).
    { pose proof (CH2.retEx_ghost E' 60 [Z_to_bv 64 fl] R2 0 ltac:(cbn; clear; lia)) as G0. rewrite Nat.add_0_r in G0. cbn [nth] in G0. unfold E2. rewrite G0. apply u64_of_Z. clear - Z7 FQ0 FQ3 CL SP1. lia. }
    assert (CB0 : CHA.curB LBo G.BLS i E1 = LB).
    { unfold CHA.curB. rewrite BLSi. unfold CH2.den. cbn [map fst snd].
      rewrite <- (SR.edenot_agree_AP _ E0 E1 (EVar 56) HagE60 ltac:(vm_compute; reflexivity)), <- (SR.edenot_agree_AP _ E0 E1 (EMd Instr.M_MUL (ELit 2) (EVar 54)) HagE60 ltac:(vm_compute; reflexivity)),
              <- (SR.edenot_agree_AP _ E0 E1 (EVar 57) HagE60 ltac:(vm_compute; reflexivity)), <- (SR.edenot_agree_AP _ E0 E1 (EVar 59) HagE60 ltac:(vm_compute; reflexivity)).
      pose proof (UBC I) as UBC'. cbn [edenot] in UBC' |- *. rewrite UBC', U56, U57, U59. reflexivity. }
    assert (CF0 : CHA.curF FF sp PSO.FFS i E1 = FF) by (unfold CHA.curF; rewrite FFS0; reflexivity).
    rewrite CF0 in Z3, Z8, Zp, HH2. rewrite CB0 in Z4, Z8, Zp, HH2.

    assert (FAPB : forall u n, In (u, n) LB -> F + 1024 <= u \/ u + n <= F) by (intros u n Hun; exact (Z4 (u, n) Hun)).
    pose proof (TV 32%nat _ ltac:(clear; lia) U32) as T32. pose proof (TV 34%nat _ ltac:(clear; lia) U34) as T34. pose proof (TV 35%nat _ ltac:(clear; lia) U35) as T35.
    pose proof (TV 36%nat _ ltac:(clear; lia) U36) as T36. pose proof (TV 56%nat _ ltac:(clear; lia) U56) as T56. pose proof (TV 57%nat _ ltac:(clear; lia) U57) as T57.
    pose proof (TV 59%nat _ ltac:(clear; lia) U59) as T59.
    assert (F8 : F mod 8 = 0).
    { destruct Z1 as (_ & _ & G3 & _). apply Z.mod_divide in G3; [|clear; lia]. destruct G3 as [q Hq]. rewrite Hq. replace (q * 1024) with ((q * 128) * 8) by (clear; lia). apply Z_mod_mult. }

    assert (ISHZ : forall slot sh, In slot ISLOTS -> 65536 <= slot -> slot + 8 <= 7024640 -> sh = slot / 8 + SB -> slot mod 8 = 0 ->
              kentry_ok (hl_segs L) E2 (CCA.vis A1 m2 M2) (KZero (SA (ELit 0) sh) (ELit 1))).
    { intros slot sh Hin Hlo Hhi Hsh Hal.
      assert (POIs : Forall (fun r : Z * Z => slot + 8 <= fst r \/ snd r <= slot) (icl_poison (PSOI.iIL I))).
      { apply (Forall_impl (P := fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) ISLOTS)); [|exact (PSOI.iPOI I)]. intros r Hr. exact (proj1 (Forall_forall _ _) Hr slot Hin). }
      destruct (PSOI.iISH I _ _ _ _ _ _ _ HH2 slot 8 ltac:(rewrite ILO; clear - Hlo; lia) ltac:(rewrite IHI; clear - Hhi; lia) ltac:(clear; lia) POIs) as [BZ BA].
      assert (ISX : in_shadow_of slot 8 sh) by (unfold in_shadow_of, S; rewrite Hsh; pose proof (Z_div_mod_eq_full slot 8); clear - H Hal; split; [lia|]; apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
      assert (SH0 : 0 <= sh < 2 ^ 64) by (rewrite Hsh; unfold SB; clear - Hlo Hhi; split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia | lia] | pose proof (Z.div_le_upper_bound slot 8 1067244 ltac:(lia) ltac:(lia)); lia]).
      eapply CL5A.kzero_intro with (A := sh) (N := 1); [unfold estart; cbn [a_base a_off edenot]; rewrite L5.unsigned_lit by (clear; lia); clear - SH0; lia | reflexivity | clear - SH0; lia | clear - SH0; lia | clear - SH0; lia |].
      intros jj Hjj. replace (sh + jj) with sh by (clear - Hjj; lia). apply CL5A.byte_vis; [apply CHA.vis_allowed; exact (BA _ ISX) | exact (BZ _ ISX)]. }
    pose proof WIC as WIC'.
    unfold PSO.ISHL, PSO.SMUSER, PSOK.ISH in HX0. cbn [app In] in HX0.
    destruct HX0 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]].
    + apply (ISHZ (VT_FUNC + 48)); [left; reflexivity | unfold VT_FUNC, VT_VISITOR; clear; lia | unfold VT_FUNC, VT_VISITOR; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity].
    + apply (ISHZ (VT_VISITOR + 56)); [right; left; reflexivity | unfold VT_FUNC, VT_VISITOR; clear; lia | unfold VT_FUNC, VT_VISITOR; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity].
    + apply (ISHZ (VT_VISITOR + 104)); [right; right; left; reflexivity | unfold VT_FUNC, VT_VISITOR; clear; lia | unfold VT_FUNC, VT_VISITOR; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity].
    + apply (ISHZ (VT_VISITOR + 112)); [right; right; right; left; reflexivity | unfold VT_FUNC, VT_VISITOR; clear; lia | unfold VT_FUNC, VT_VISITOR; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity].
    +
      destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2) (PSOI.bptr I, PSOI.bcap I) (INB I)) as (_ & _ & BSHA & _). cbn [fst snd] in BSHA.
      pose proof (PSOI.iHPSH I) as [[BZ0 _] _]. cbn [PML.ps_bptr PML.ps_bcap] in BZ0.
      assert (AGS : forall a, in_shadow_of (PSOI.bptr I) (PSOI.bcap I) a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha. destruct (ACL a (sp + PSO.CSP) 512 ltac:(do 3 right; left; exact Ha)) as (RG & CLa & BLW). rewrite (proj1 Zp a RG CLa).
        apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). rewrite XF. unfold PSO.F0, PSO.F_STK, SGP.outside. apply Forall_forall.
        pose proof (SHR _ _ a KB5 KB3 KB7 Ha) as SRG. pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6 i c E1 E' A1 M m1 HA (G.NF_le i c Hci) Hag) as HagE'.
        assert (W2' : bv_unsigned (ev E' 2) = sp) by (rewrite <- (proj1 HagE' 2%nat ltac:(unfold GT.NF, Cut_psome_casan_T.NF; clear; lia)); exact U2).
        assert (W10' : bv_unsigned (ev E' 10) = P) by (rewrite <- (proj1 HagE' 10%nat ltac:(unfold GT.NF, Cut_psome_casan_T.NF; clear; lia)); exact U10).
        intros rg [<-|[<-|[<-|[<-|[]]]]]; unfold estart, elenZ, PE, SCR; cbn [fst snd a_base a_off edenot]; rewrite ?W2', ?W10'; rewrite L5.unsigned_lit by exact RG; rewrite u64_of_Z by (clear; lia);
          [unfold SCR in BLW; clear - BLW; lia | unfold hid in O5; clear - SRG O5; lia | unfold hid in O5; clear - SRG O5; lia | unfold hid in O5; clear - SRG O5; lia]. }
      apply (CL5A.shz_intro (hl_segs L) E2 _ (EVar 56) 33 (PSOI.bptr I) ltac:(unfold CL5A.uv; cbn [edenot]; exact T56)); [clear; lia | clear - KB0 KB3 KB7; lia |].
      intros jj Hjj. assert (ISX : in_shadow_of (PSOI.bptr I) (PSOI.bcap I) (HeapIfaceA.S (PSOI.bptr I) + jj)).
      { apply (CL5A.in_shadow_mono (PSOI.bptr I) (8 * 33)); [clear; lia | clear - BC1; lia | clear; lia |]. apply (CL5A.shreg_in_shadow _ 33 _ KB8); [clear; lia | unfold HeapIfaceA.S; clear - Hjj; lia]. }
      apply CL5A.byte_vis; [apply CHA.vis_allowed; exact (BSHA _ ISX) |]. unfold byte_at. rewrite (AGS _ ISX). exact (BZ0 jj ltac:(change (0 <= jj < PSOI.bcap I / 8); clear - Hjj BC1 BC8; split; [lia|]; apply (Z.lt_le_trans _ 33); [lia|]; apply Z.div_le_lower_bound; lia)).
    +
      cbn [kentry_ok]. unfold estart, elenZ, FE, FEV, WP0, WP0V, WLEN, WLENV. cbn [a_base a_off edenot]. rewrite T65, T36, T32, u64_of_Z by (clear; lia).
      destruct WIC' as [Hw|(INC & C1 & C2 & _)]; [pose proof (PSOI.WNONE I Hw) as (W0 & _ & W2 & _); rewrite W0, W2; right; clear - FR; lia|].
      destruct (FAPB _ _ INC) as [G0|G0]; [left; clear - G0 C1; lia | right; clear - G0 C2 WI6; lia].
    +
      cbn [kentry_ok]. unfold estart, elenZ, FLE, FLV, WP0, WP0V, WLEN, WLENV. cbn [a_base a_off edenot]. rewrite T60, T36, T32, u64_of_Z by (clear; lia).
      destruct WIC' as [Hw|(INC & C1 & C2 & _)]; [pose proof (PSOI.WNONE I Hw) as (W0 & _ & W2 & _); rewrite W0, W2; right; clear - Z7 FQ0; lia|].
      destruct (Z_lt_dec fl (PSOI.wp0 I)) as [G0|G0]; [left; clear - G0; lia|]. destruct (Z_le_dec (PSOI.wp0 I + PSOI.wlen I) fl) as [G1|G1]; [right; clear - G1; lia|]. exfalso.
      apply Z8. left. exists (PSOI.ich I, 16384). split; [exact INC | cbn [fst snd]; clear - G0 G1 C1 C2 WI6; lia].
    +
      cbn [kentry_ok]. rewrite ?CL5A.estart_srl3, ?CL5A.estart_srl3'. unfold elenZ, CL5A.uv, FE, FEV, CH, CHV, CHG, CHGV. cbn [edenot]. rewrite T65, T34, T35, u64_of_Z by (clear; lia).
      destruct WIC' as [Hw|(INC & C1 & C2 & C3 & C16)]; [pose proof (PSOI.WNONE I Hw) as (_ & _ & _ & W3 & W4); rewrite W3, W4; right; change (0 / 8) with 0; pose proof (Z.div_pos F 8 (proj1 FR) ltac:(clear; lia)); clear - H; lia|].
      rewrite C3. pose proof (Z_div_mod_eq_full F 8) as DF. pose proof (Z_div_mod_eq_full (PSOI.ich I) 8) as DC. pose proof (CHA.mod8_of_16 _ C16) as CH8.
      destruct (FAPB _ _ INC) as [G0|G0]; [left | right]; clear - G0 DF DC F8 CH8; lia.
    +
      cbn [kentry_ok]. rewrite ?CL5A.estart_srl3, ?CL5A.estart_srl3'. unfold elenZ, CL5A.uv, FE, FEV, PPV. cbn [edenot]. rewrite T65, T56, (u64_of_Z 128), (u64_of_Z 33) by (clear; lia).
      pose proof (Z_div_mod_eq_full F 8) as DF. pose proof (Z_div_mod_eq_full (PSOI.bptr I) 8) as DB.
      destruct (FAPB _ _ (INB I)) as [G0|G0]; [left | right]; clear - G0 DF DB F8 KB8 BC1; lia.
    +
      cbn [kentry_ok]. rewrite ?CL5A.estart_srl3, ?CL5A.estart_srl3'. unfold elenZ, CHA.SRL3. rewrite (CL5A.elen_srl3' E2 (EAlu Instr.ALU_ADD (EVar SCAPV) (ELit 7)) : bv_unsigned (edenot E2 (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar SCAPV) (ELit 7)) (ELit 3))) = CL5A.uv E2 (EAlu Instr.ALU_ADD (EVar SCAPV) (ELit 7)) / 8).
      rewrite (uv_add_lit E2 (PSOI.scap I) 7 SCAPV T59 ltac:(clear - WF5; lia) ltac:(clear; lia) ltac:(clear - WF5; lia)).
      unfold CL5A.uv, FE, FEV, SBV. cbn [edenot]. rewrite T65, T57, (u64_of_Z 128) by (clear; lia).
      pose proof (Z_div_mod_eq_full F 8) as DF. pose proof (Z_div_mod_eq_full (PSOI.sb I) 8) as DS. pose proof (Z_div_mod_eq_full (PSOI.scap I + 7) 8) as DQ. pose proof (Z.mod_pos_bound (PSOI.scap I + 7) 8 ltac:(clear; lia)) as MQ.
      destruct (FAPB _ _ (INS I)) as [G0|G0]; [left | right]; clear - G0 DF DS DQ MQ F8 KS8 WF5; lia.
    +
      pose proof (TV 11%nat _ ltac:(clear; lia) U11) as T11. pose proof (PSOI.iOV I) as (Vfr' & _). destruct Vfr' as (f & Hf & F1 & F2).
      cbn [kentry_ok]. unfold estart, elenZ, FE, FEV, VE. cbn [a_base a_off edenot]. rewrite T65, T11, u64_of_Z, u64_of_Z by (clear; lia).
      destruct (Z3 f (in_or_app _ _ _ (or_introl Hf))) as [G0|G0]; [left | right]; clear - G0 F1 F2; lia.
    +
      pose proof (TV 11%nat _ ltac:(clear; lia) U11) as T11. pose proof (PSOI.iOV I) as (Vfr' & _).
      cbn [kentry_ok]. unfold estart, elenZ, FLE, FLV, VE. cbn [a_base a_off edenot]. rewrite T60, T11, u64_of_Z, u64_of_Z by (clear; lia).
      destruct (Z_lt_dec fl (PSOI.iV I + 8)) as [G0|G0]; [left; clear - G0; lia|]. destruct (Z_le_dec (PSOI.iV I + 48) fl) as [G1|G1]; [right; clear - G1; lia|]. exfalso.
      apply Z8. apply (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LB ((F, 4, sp + PSO.CSP + 32) :: FF) 0 0 (PSOI.iV I) 48 fl
        ltac:(destruct Vfr' as (f & Hf & F1 & F2); exists f; split; [right; exact Hf | split; assumption]) ltac:(clear - G0 G1; lia))).
  -
    intros R2 M2 m2 F fl LK' cr1 HRP Ha0r SMF HH2. rewrite Ynx, Ycsp in *.
    set (E2 := CH2.retEx E' 60 [Z_to_bv 64 fl] R2) in *.
    destruct SMF as [Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Zp]. change (ff_bytes 4) with 1024 in *.
    pose proof (CH2.retEx_agree E' 60 [Z_to_bv 64 fl] R2 : env_agree 60 E' E2) as Hag2.
    assert (HagE2 : env_agree 60 E0 E2) by (eapply CC.env_agree_trans; [exact HagE60 | eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact NX] | exact Hag2]]).
    assert (TV : forall v z, (v < 60)%nat -> bv_unsigned (ev E0 v) = z -> bv_unsigned (ev E2 v) = z) by (intros v z Hv Hz; rewrite <- (proj1 HagE2 v Hv); exact Hz).
    destruct (CHA.rf_fs _ _ _ _ RFx) as ((FQ0 & FQ1 & FQ2) & FQ3 & _). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in Z1, Z7, FQ1, FQ3.
    assert (T60 : bv_unsigned (ev E2 60) = fl).
    { pose proof (CH2.retEx_ghost E' 60 [Z_to_bv 64 fl] R2 0 ltac:(cbn; clear; lia)) as G0. rewrite Nat.add_0_r in G0. cbn [nth] in G0. unfold E2. rewrite G0. apply u64_of_Z. clear - Z7 FQ0 FQ3 CL SP1. lia. }
    assert (CB0 : CHA.curB LBo G.BLS i E1 = LB).
    { unfold CHA.curB. rewrite BLSi. unfold CH2.den. cbn [map fst snd].
      rewrite <- (SR.edenot_agree_AP _ E0 E1 (EVar 56) HagE60 ltac:(vm_compute; reflexivity)), <- (SR.edenot_agree_AP _ E0 E1 (EMd Instr.M_MUL (ELit 2) (EVar 54)) HagE60 ltac:(vm_compute; reflexivity)),
              <- (SR.edenot_agree_AP _ E0 E1 (EVar 57) HagE60 ltac:(vm_compute; reflexivity)), <- (SR.edenot_agree_AP _ E0 E1 (EVar 59) HagE60 ltac:(vm_compute; reflexivity)).
      pose proof (UBC I) as UBC'. cbn [edenot] in UBC' |- *. rewrite UBC', U56, U57, U59. reflexivity. }
    assert (CF0 : CHA.curF FF sp PSO.FFS i E1 = FF) by (unfold CHA.curF; rewrite FFS0; reflexivity).
    rewrite CF0 in Z3, Z8, Zp, HH2. rewrite CB0 in Z4, Z8, Zp, HH2.

    pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6 i c E1 E' A1 M m1 HA (G.NF_le i c Hci) Hag) as HagE'.
    assert (W2' : bv_unsigned (ev E' 2) = sp) by (rewrite <- (proj1 HagE' 2%nat ltac:(unfold GT.NF, Cut_psome_casan_T.NF; clear; lia)); exact U2).
    assert (W10' : bv_unsigned (ev E' 10) = P) by (rewrite <- (proj1 HagE' 10%nat ltac:(unfold GT.NF, Cut_psome_casan_T.NF; clear; lia)); exact U10).
    pose proof (CBA.amb_off L ar C HI HIok (LYB I) GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6 i E1 A1 M m1 HA) as Hoff.
    rewrite <- (L5LZ.sbm_ahid A1 m1 m' (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)) in Hoff.
    assert (CELL : forall X0, PSO.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
    { intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0). }
    assert (AG : forall a, SUPP I (PSOI.bptr I) (PSOI.bcap I) (PSOI.sb I) (PSOI.scap I) a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. destruct (ACL a (sp + PSO.CSP) 512 Ha) as (RG & CLa & BLW). rewrite (proj1 Zp a RG CLa).

      assert (T48 : bv_unsigned (ev E' 48) = PSOI.st0 I) by (rewrite <- (proj1 Hag 48%nat ltac:(clear - NX; lia)), <- (proj1 HagE60 48%nat ltac:(clear; lia)); exact U48).
      assert (T52 : bv_unsigned (ev E' 52) = PSOI.done0 I) by (rewrite <- (proj1 Hag 52%nat ltac:(clear - NX; lia)), <- (proj1 HagE60 52%nat ltac:(clear; lia)); exact U52).
      assert (PIMG : hl_img_hi L <= P) by (rewrite IHI; clear - O1 FSLO; lia).
      destruct (Z.eq_dec a (P + 208)) as [->|N1].
      { exact (U8EQ M M' (P + 208) (PSOI.st0 I) (PTB.pa_st L IC _ _ _ (PSOI.iHPA I)) ltac:(pose proof (RD8 I E' A1 m' M' 208 (EVar STV) Hoff W10' (CELL _ Y208)) as G0; unfold CL5A.uv, STV in G0; cbn [edenot] in G0; rewrite T48 in G0; exact G0) ltac:(clear - PIMG; lia) RG). }
      destruct (Z.eq_dec a (P + 211)) as [->|N2].
      { pose proof (PTB.pa_more L IC _ _ _ (PSOI.iHPA I)) as G1. rewrite (PSOI.iHMORE I) in G1. cbn [PML.b2z] in G1.
        exact (U8EQ M M' (P + 211) 1 G1 ltac:(pose proof (RD8 I E' A1 m' M' 211 (ELit 1) Hoff W10' (CELL _ Y211)) as G0; unfold CL5A.uv in G0; cbn [edenot] in G0; rewrite L5.unsigned_lit in G0 by (clear; lia); exact G0) ltac:(clear - PIMG; lia) RG). }
      destruct (Z.eq_dec a (P + 212)) as [->|N3].
      { exact (U8EQ M M' (P + 212) (PSOI.done0 I) (PTB.pa_done L IC _ _ _ (PSOI.iHPA I)) ltac:(pose proof (RD8 I E' A1 m' M' 212 (EVar DONEV) Hoff W10' (CELL _ Y212)) as G0; unfold CL5A.uv, DONEV in G0; cbn [edenot] in G0; rewrite T52 in G0; exact G0) ltac:(clear - PIMG; lia) RG). }
      apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). rewrite XF. unfold PSO.F0, PSO.F_STK, SGP.outside. apply Forall_forall.
      intros rg [<-|[<-|[<-|[<-|[]]]]]; unfold estart, elenZ, PE, SCR; cbn [fst snd a_base a_off edenot]; rewrite ?W2', ?W10'; rewrite L5.unsigned_lit by exact RG; rewrite u64_of_Z by (clear; lia);
        [unfold SCR in BLW; clear - BLW; lia | clear - N1; lia | clear - N2; lia | clear - N3; lia]. }
    constructor; try (intros Hk; rewrite XKj in Hk; first [discriminate Hk | destruct Hk as [Hk|Hk]; discriminate Hk]); try (intros pc0 Hk; rewrite XKj in Hk; discriminate Hk).
    + intros _. unfold PSOX.FLF. unfold CL5A.uv, FLE, FLV. cbn [edenot]. rewrite T60. split; [clear - Z7; lia|]. intros HC. apply Z8.
      eapply CHA.aclient_scr; [eapply CHA.aclient_incl; [intros y Hy; unfold PSOI.LB; apply in_or_app; right; exact Hy | apply incl_tl, incl_refl | exact HC] | intros y Hy; clear - Hy; lia].
    + intros _. pose proof (PSOI.iHPA I) as PA. pose proof (PSOX.set_win_self ps) as SWS.
      assert (BJ : bptrI j E2 = PSOI.bptr I /\ bcapI j E2 = PSOI.bcap I /\ sbI j E2 = PSOI.sb I /\ scapI j E2 = PSOI.scap I).
      { unfold PSOX.bptrI, PSOX.bcapI, PSOX.sbI, PSOX.scapI, PSO.blk0, PSO.blk1. rewrite BLSj, BLSi. cbn [hd tl fst snd]. unfold CL5A.uv.
        rewrite <- (SR.edenot_agree_AP _ E0 E2 (EVar 56) HagE2 ltac:(vm_compute; reflexivity)), <- (SR.edenot_agree_AP _ E0 E2 (EMd Instr.M_MUL (ELit 2) (EVar 54)) HagE2 ltac:(vm_compute; reflexivity)),
                <- (SR.edenot_agree_AP _ E0 E2 (EVar 57) HagE2 ltac:(vm_compute; reflexivity)), <- (SR.edenot_agree_AP _ E0 E2 (EVar 59) HagE2 ltac:(vm_compute; reflexivity)).
        pose proof (UBC I) as UBC'. cbn [edenot] in UBC' |- *. rewrite UBC', U56, U57, U59. repeat split; reflexivity. }
      destruct BJ as (BJ1 & BJ2 & BJ3 & BJ4).
      constructor.
      * rewrite SWS. apply (parser_at_mv I M M2 _ _ _ _ AG LB FF LK cr A M (vml_of model) HH (INB I) (INS I) ps); [reflexivity | reflexivity | reflexivity | reflexivity | exact PA].
      * left. split; [rewrite XKj; reflexivity | reflexivity].
      * apply (parser_sh_mv I M M2 _ _ _ _ AG LB FF LK cr A M (vml_of model) HH (INB I) (INS I) ps); [reflexivity | reflexivity | reflexivity | reflexivity | exact (PTB.pa_slen L IC _ _ _ PA) | exact (PSOI.iHPSH I)].
      * unfold PSOX.WIN. destruct (PML.ps_win ps) as [[p0 e0]|] eqn:Hw; [|reflexivity]. exists p0. split; [reflexivity|].
        pose proof (PSOI.WSOME I p0 e0 Hw) as (_ & _ & _ & _ & _ & _ & _ & _ & PLE). clear - PLE. lia.
      * exact (PSOI.iHBB I).
      * exact (ec_at_mv I M M2 _ _ _ _ AG 0 (PSOI.iHEC I)).
      * exact (ls_ok_mv I M M2 _ _ _ _ AG (PSOI.ig I) (PSOI.iHG I) (PSOI.iHLS I)).
      * left. reflexivity.
      * intros _. reflexivity.
      * rewrite BJ1, BJ2, BJ3, BJ4. reflexivity.
      * intros Hu. rewrite (u0_sm j cj Hcj XKj) in Hu. discriminate Hu.
      * intros Hu. rewrite (u0_sm j cj Hcj XKj) in Hu. discriminate Hu.
      * intros _. exact HagE2.
Qed.
End S.
