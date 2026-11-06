(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto HeapIface HeapIfaceA L5Defs L5Core L5LazyA
  Pm9PlanKit Pm9L5DefsA FrmInv Pm9FrmInv PmHeapIfaceA PmLibDefs PmLibDefsA PmLibSpecsA CutVFXM DecIface DecJson DecScanPure DecOkDefsM DecOkSemM DecIfaceA StrtodPure StrtodIface FloatLazyA
  Pm9FloatscanOk.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutVF.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD CutCertA CutHeapA CutL5A CutBridgeA CutPureA CutVFA CutVFT Pm9CutKitD DecAssume StrtodAssume
  Pm9Leaf_trunctfdf2.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_strtod_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module STOA.
Module G := Cut_strtod_cboth.
Definition AD : PDC.addrs := PDCA.cboth.
Definition ENTRY : Z := 1333096.   Definition FS_PC : Z := 1315664.   Definition TR_PC : Z := 1284484.   Definition RET_PC : Z := 1333252.
Definition GADDR : Z := 7019984.   Definition TPV : Z := 6888848.
Definition IMG_LO : Z := 65536.    Definition IMG_HI : Z := 1400832.
Definition GLO : Z := 1368064.     Definition GHI : Z := 1368064.
Definition NFs : nat := 34.        Definition WIN : Z := 8672.
Lemma ad_ok : PDC.a_TP AD = TPV /\ PDC.a_G AD = GADDR /\ PDC.a_img_lo AD = IMG_LO /\ PDC.a_img_hi AD = IMG_HI. Proof. repeat split; reflexivity. Qed.

Definition ps0 : SR.post_spec := Eval vm_compute in (nth 0 (CC.cp_PSS G.cp0) (SR.PS 0 [] [] [])).
Definition ps1 : SR.post_spec := Eval vm_compute in (nth 0 (CC.cp_PSS G.cp1) (SR.PS 0 [] [] [])).
Definition ps2 : SR.post_spec := Eval vm_compute in (nth 0 (CC.cp_PSS G.cp2) (SR.PS 0 [] [] [])).
Lemma pss_ok : CC.cp_PSS G.cp0 = [ps0] /\ CC.cp_PSS G.cp1 = [ps1] /\ CC.cp_PSS G.cp2 = [ps2]. Proof. repeat split; reflexivity. Qed.
Lemma tags_eq : G.TAGS = [[CC.TOther FS_PC]; [CC.TOther TR_PC]; [CC.TOther RET_PC]]. Proof. reflexivity. Qed.
Lemma pcs_ok : CC.cp_pc G.cp0 = ENTRY /\ SR.ps_pc ps0 = FS_PC /\ SR.ps_pc ps1 = TR_PC /\ SR.ps_pc ps2 = RET_PC /\ (CC.cp_nx G.cp1 = 51)%nat /\ (CC.cp_nx G.cp2 = 67)%nat.
Proof. repeat split; reflexivity. Qed.

Lemma heap_ok : CHA.heap_chkA NFs G.HDECL (CPA.NOB G.CPS) (CPA.NOF G.CPS) G.CPS G.TAGS = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma pure_ok : CH2.leaves_all G.CPS G.TAGS (CPA.pure_leaf_chk NFs G.HDECL [RET_PC]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma foot_ok : CC.cps_all G.CPS (fun _ c => CHA.foot_chk NFs G.HDECL c [] []) = true.
Proof. vmc_refl. Qed.
Lemma hd_ok : CH.hd_scr G.HDECL = 8944 /\ CH.hd_wrs G.HDECL = [(EVar 11, 0, ELit 8); (EVar 4, -164, ELit 4)]
  /\ CH.hd_crs G.HDECL = [(EVar 10, 0, EAlu ALU_ADD (EVar 33) (ELit 1)); (ELit 0, GADDR, ELit 8)] /\ CH.hd_img G.HDECL = [(IMG_LO, IMG_HI)].
Proof. repeat split; reflexivity. Qed.
Lemma ret_pc_ok : CL.is_ret_at RSEGS RET_PC.
Proof. CL.solve_is_ret. Qed.

Lemma lems : G.LEMS_OK. Proof. unfold G.LEMS_OK, CXD.LEMS_OK, G.LEMS. apply Forall_nil. Qed.

Definition FSW : list SGP.region := [(EVar 2, -264, ELit 8); (EVar 4, -164, ELit 4)].
Definition FSNEWS : list kentry := [KWord (SA (EVar 2) (-264)) 8 (EVar 34)].
Definition fs_custom : option CH2.cinfo := CHA.custom_chk NFs G.HDECL [] GLO GHI WIN 1 [] [] FSW FSNEWS None G.cp0 ps0 G.cp1 [] [] [] [].
Definition FSCI : CH2.cinfo := Eval vm_compute in (match fs_custom with Some ci => ci | None => CH2.CI [] 0 0 0 end).
Lemma fs_ci : fs_custom = Some FSCI. Proof. vmc_refl. Qed.
Lemma fs_ci_facts : CH2.ci_nx FSCI = 34%nat /\ CH2.ci_csp FSCI = -272 /\ CH2.ci_regs FSCI = CA.ps_reglist ps0. Proof. repeat split; reflexivity. Qed.
Lemma fs_leaf_facts :
  nth 10 (CA.ps_reglist ps0) (ELit 0) = APC.eaddz (EVar 2) (-272) /\ nth 11 (CA.ps_reglist ps0) (ELit 0) = ELit 1 /\ nth 12 (CA.ps_reglist ps0) (ELit 0) = ELit 1
  /\ has (SR.ps_cells ps0) (KWord (SA (EVar 2) (-264)) 8 (EVar 10)) = true /\ has (SR.ps_cells ps0) (KWord (SA (EVar 2) (-88)) 8 (ELit 18446744073709551615)) = true
  /\ has (SR.ps_cells ps0) (KWord (SA (EVar 2) (-80)) 8 (ELit 0)) = true /\ has (SR.ps_cells ps0) (KWord (SA (ELit 0) GADDR) 8 (EVar 32)) = true
  /\ has (SR.ps_cells ps0) (KImg IMG_LO IMG_HI) = true.
Proof. repeat split; reflexivity. Qed.

Definition tr_custom : option CH2.cinfo := CHA.custom_chk NFs G.HDECL [] GLO GHI 0 0 [] [] [] [] None G.cp1 ps1 G.cp2 [] [] [] [].
Definition TRCI : CH2.cinfo := Eval vm_compute in (match tr_custom with Some ci => ci | None => CH2.CI [] 0 0 0 end).
Lemma tr_ci : tr_custom = Some TRCI. Proof. vmc_refl. Qed.

Lemma exit_fact : has (SR.ps_cells ps2) (KWord (SA (EVar 11) 0) 8 (EVar 34)) = true. Proof. reflexivity. Qed.

Lemma reg_read : forall regs E' R' n e, regs_ok E' regs R' -> (0 < n < 32)%nat -> nth n regs (ELit 0) = e -> getr R' (PDC.reg_of n) = edenot E' e.
Proof.
  intros regs E' R' n e HR Hn He. rewrite (HR (PDC.reg_of n)). unfold sr_get.
  assert (Hu : bv_unsigned (PDC.reg_of n) = Z.of_nat n) by (unfold PDC.reg_of; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; lia).
  assert (Hb : bv_eqb (PDC.reg_of n) 0 = false) by (unfold bv_eqb; rewrite Hu; change (bv_unsigned (0%bv : bv 5)) with 0; apply Z.eqb_neq; lia).
  rewrite Hb. unfold ridx. rewrite Hu, Nat2Z.id, He. reflexivity.
Qed.

Lemma guard_readable : forall M : word -> option byte, exists CAN, L5.u64_at RSEGS M GADDR CAN /\ 0 <= CAN < 2 ^ 64.
Proof.
  intros M. assert (H : exists bs, rdn RSEGS M (Z_to_bv 64 GADDR) 8 = Some bs /\ length bs = 8%nat).
  { assert (GR : forall n a, (forall i, (i < n)%nat -> seg_rom RSEGS (Z_to_bv 64 (a + Z.of_nat i)) <> None) -> exists bs, rdn RSEGS M (Z_to_bv 64 a) n = Some bs /\ length bs = n).
    { induction n as [|n IH]; intros a Hr; [exists []; split; reflexivity|]. cbn [rdn].
      assert (Hb : exists b, match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 a) end = Some b).
      { destruct (M (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|]. specialize (Hr 0%nat ltac:(lia)). replace (a + Z.of_nat 0) with a in Hr by lia.
        destruct (seg_rom RSEGS (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | contradiction]. }
      destruct Hb as [b ->].
      replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
      2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_unsigned (1%bv : bv 64)) with 1. rewrite <- Zplus_mod_idemp_l. reflexivity. }
      destruct (IH (a + 1)) as (bs & -> & Hl); [intros i Hi; replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia; apply Hr; lia|].
      exists (b :: bs). split; [reflexivity | cbn; lia]. }
    apply GR. intros i Hi. do 8 (destruct i as [|i]; [vm_compute; discriminate|]). lia. }
  destruct H as (bs & Hr & Hl). exists (bytes_le_to_Z bs). split.
  - unfold L5.u64_at. rewrite Hr. f_equal. symmetry. rewrite <- Hl at 1. apply APSX.word_to_le_bytes_of_bytes. lia.
  - pose proof (AX2S.bytes_le_to_Z_bound bs) as B. rewrite Hl in B. exact B.
Qed.

Definition ghost (CAN N : Z) (n : nat) : word := match n with 32 => Z_to_bv 64 CAN | 33 => Z_to_bv 64 N | _ => Z_to_bv 64 0 end%nat.
Definition mkE (R : bvmap 5 word) (CAN N : Z) : env := Env (reg_ev R (ghost CAN N)) (fun _ => []).

Definition XI (v : Z) (i : nat) (E : env) : Prop := match i with 0%nat => True | _ => ev E 34 = Z_to_bv 64 v end.

Definition hide (P : Prop) : Prop := P.
Ltac hidehyp H := let T := type of H in change T with (hide T) in H.

Section Final.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout. Variable ar : asan_run. Variable C : asan_statics_cells. Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FL : PDCA.float_layoutA L AD.

Theorem strtod_okA : PMSA.strtod_specA L ar HI PMLA.C_cboth ENTRY.
Proof.
  intros LB FF LK cr A s endp sp r txt fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs Hpre Hcont.
  unfold PMSA.STRTOD_SCR, PML.STRTOD_SCR_V in *.
  destruct Hpre as (Ha0 & Ha1 & Himg & Tb & Tn & Hnf & Hlen & Dend & Hcobj & Ap1 & Ap2 & Ap3 & Tdef & Hblk).
  unfold PMSA.a0, PMSA.a1, PMSA.u8, PMSA.acobj, PMLA.img_ro in *. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_cboth] in Himg.
  clear Ap1. hidehyp Ap2. hidehyp Ap3.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (FPM : forall (fx fx' : FPState) R0 pc M0 R' pc' M', msteps (hl_segs L) (@mkst fx R0 (Z_to_bv 64 pc) M0 (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx').
  { rewrite LS. intros fx0 fx' R0 pc M0 R' pc' M' H Hf. exact (Pm9FrmInv.msteps_fp_ok fx0 fx' R0 _ M0 _ R' _ M' _ H Hf). }
  pose proof FL as [TP CELLS]. cbn [PDC.a_TP PDC.a_G PDC.a_img_lo PDC.a_img_hi AD PDCA.cboth] in TP, CELLS.
  assert (DEFS : TPV = 6888848 /\ GADDR = 7019984 /\ IMG_LO = 65536 /\ IMG_HI = 1400832 /\ WIN = 8672) by (repeat split; reflexivity). destruct DEFS as (Dtpv & Dg & Dlo & Dhi & Dwin).
  pose proof LYI as [LI0 LI1].
  pose proof (FLA.rng L ar C HI HIok _ _ _ _ _ _ _ HH) as RFx. destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct (CHA.rf_fs _ _ _ _ RFx) as ((AF0 & _ & _) & AF3 & _).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  set (N := Z.of_nat (length txt)) in *. assert (HN0 : 0 <= N) by (unfold N; lia).
  assert (HN1 : 1 <= N) by (destruct (PSP.final_shape txt Hnf) as [(c0 & r0 & -> & _) | (c1 & r0 & -> & _)]; unfold N; cbn [length]; lia).
  assert (Hblk' : PDCA.textblk LB s (N + 1)) by (destruct Hblk as (b & Hb & B1 & B2); exists b; split; [exact Hb | lia]).
  destruct (FLA.txt_facts L ar C HI HIok _ _ _ _ _ _ _ s (N + 1) HH Hblk') as (TB1 & TB2 & TB3 & TB4 & TB5). clear TB3. hidehyp TB4.
  destruct (guard_readable M) as (CAN & Hguard & RCAN). rewrite <- LS in Hguard.
  pose proof (CL5A.acobj_rng L ar LB FF sp endp 8 RFx ltac:(lia) Hcobj ltac:(lia)) as (EA1 & EA2 & _ & EA4 & EA5).
  assert (EA6 : 32 <= endp) by (clear - EA4 AF0 CL; lia). clear EA4. hidehyp EA5.
  assert (EAI : hide (endp + 8 <= hl_img_lo L \/ hl_img_hi L <= endp)).
  { destruct Hcobj as [HIf | [H1 H2]]; [| right; clear - H1 IHI CL S2; lia]. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (CL5A.infr_rng L ar LB FF endp 8 RFx HIf ltac:(lia)))))))). }
  set (E0 := mkE R CAN N).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (Usp : bv_unsigned (getr R 2%bv) = sp) by (rewrite Hsp; apply u64_of_Z; lia).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by exact Usp.
  assert (U10 : bv_unsigned (ev E0 10) = s) by (change (ev E0 10) with (getr R 10%bv); rewrite Ha0; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = endp) by (change (ev E0 11) with (getr R 11%bv); rewrite Ha1; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = CAN) by (change (ev E0 32) with (Z_to_bv 64 CAN); apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = N) by (change (ev E0 33) with (Z_to_bv 64 N); apply u64_of_Z; lia).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (U4 : bv_unsigned (ev E0 4) = TPV) by (rewrite V4, TP; apply u64_of_Z; unfold TPV; lia).
  destruct hd_ok as (SCRV & HWRS & HCRS & HIMG).
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= NFs)%nat) by (unfold NFs; lia).
  set (W := [(endp, 8); (hl_tp L - 164, 4)] : list L5.range).
  assert (WOK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a Hw Hin. unfold W in Hw. cbn [In] in Hw. rewrite SCRV. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    - exact (CL5A.acobj_wok L ar LB FF sp 8944 endp 8 a RFx ltac:(lia) Hcobj ltac:(lia)).
    - rewrite TP in Hin. destruct (CELLS a ltac:(lia)) as (C1 & C2 & C3 & _). split; [lia|].
      split; [right; right; left; split; [exact C1 | intros [X|X]; [exact (C2 X) | exact (C3 X)]]|]. apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). lia. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt NFs rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { rewrite HWRS. intros rg Hrg. cbn [In] in Hrg. destruct Hrg as [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U11 in Ha. rewrite u64_of_Z in Ha by lia. exists (endp, 8). split; [unfold W; cbn; tauto | unfold L5.in_rng; cbn [fst snd]; lia].
    - rewrite U4 in Ha. rewrite u64_of_Z in Ha by lia. exists (hl_tp L - 164, 4). split; [unfold W; cbn; tauto | unfold L5.in_rng; cbn [fst snd]; rewrite TP; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt NFs rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { rewrite HCRS. intros rg Hrg. cbn [In] in Hrg. destruct Hrg as [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha; unfold CHA.sclientA; rewrite SCRV.
    - rewrite u_add64, U10, U33 in Ha. rewrite u64_of_Z in Ha by lia. rewrite Z.mod_small in Ha by lia.
      destruct Hblk as (b & Hb & B1 & B2). split; [lia|]. split; [left; exists b; split; [exact Hb | lia]|]. apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). unfold hide in TB4. clear - TB4 Ha. lia.
    - rewrite !u64_of_Z in Ha by lia. unfold GADDR in Ha. destruct (CELLS a ltac:(lia)) as (C1 & C2 & C3 & _). split; [lia|]. split; [right; right; left; split; [exact C1 | exact C2]|].
      apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). lia. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { rewrite HIMG. intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. unfold IMG_LO, IMG_HI in Ha. rewrite ILO, IHI. split; [lia | intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); lia]. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SC_OK : incl (@nil (Z * Z * Z)) (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) (@nil (Z * Z * Z)))
    by (split; [intros x [] | apply Forall_nil]).
  assert (GOT_OK : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L)
    by (unfold GLO, GHI; rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI; lia).

  set (H := ahid A model). set (Mv := CCA.vis A model M).
  assert (VS : CL5A.visr H (sp - 8944) 8944) by (apply (FLA.stk_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH); lia).
  assert (VT : CL5A.visr H s (N + 1)) by (exact (FLA.txt_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH Hblk')).
  assert (VG : CL5A.visr H GADDR 8) by (intros i Hi; apply (CHA.img_vis L ar C HI HIok LYI NFs sp NF32 _ _ _ _ _ _ _ (GADDR + i) HH); rewrite IHI; unfold GADDR; lia).
  assert (VE : CL5A.visr H endp 8).
  { intros i Hi. destruct (CL5A.acobj_wok L ar LB FF sp 8944 endp 8 (endp + i) RFx ltac:(lia) Hcobj ltac:(lia)) as (X1 & X2 & X3).
    apply (CHA.client_vis L ar C HI HIok LB FF LK cr A M model sp 8944 (endp + i) HH X1); [| exact X3].
    unfold aclient. unfold aclientw in X2. refine (aclient_g_mono _ _ _ _ L ar LB FF sp 8944 (endp + i) _ _ X2); [intros q n x [] | intros x Hx; left; exact Hx]. }
  assert (DS : L5.defined Mv (sp - 8944) 8944) by (exact (CL5A.defined_vis H M _ _ VS S5)).
  assert (DT : L5.defined Mv s (N + 1)) by (apply (CL5A.defined_vis H M _ _ VT); unfold N; exact Tdef).
  assert (DE : L5.defined Mv endp 8) by (exact (CL5A.defined_vis H M _ _ VE Dend)).

  assert (LEAF : forall i c ps E E' R1 R' A1 M1 m1 M2 m2, nth_error G.CPS i = Some c ->
            CCA.AtV (hl_segs L) c E R1 A1 M1 m1 -> CHA.aamb L ar HI NFs E0 M model A LB FF LK sp G.HDECL W (CPA.NOB G.CPS) (CPA.NOF G.CPS) (CPA.Cred0 cr) 0 i E A1 M1 m1 ->
            env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A1 M1 m1 M2 m2 ->
            CHA.aamb L ar HI NFs E0 M model A LB FF LK sp G.HDECL W (CPA.NOB G.CPS) (CPA.NOF G.CPS) (CPA.Cred0 cr) 0 i E A1 M2 m2).
  { intros i c ps E E' R1 R' A1 M1 m1 M2 m2 Hc HAt1 HA1 Hag HLF.
    refine (CHA.leaf_amb L ar C HI HIok LYI LYR NFs E0 M model A LB FF LK sp G.HDECL W W _ _ _ 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK i c ps E E' R1 R' A1 M1 m1 M2 m2 _ HAt1 HA1 Hag HLF).
    rewrite CPA.NOBnil, CPA.NOFnil. exact (CC.cps_all_sound _ _ foot_ok i c Hc). }
  assert (AMBP : forall i E A1 M1 m1, CHA.aamb L ar HI NFs E0 M model A LB FF LK sp G.HDECL W (CPA.NOB G.CPS) (CPA.NOF G.CPS) (CPA.Cred0 cr) 0 i E A1 M1 m1 ->
            env_agree NFs E0 E /\ (exists LK1, ri_inv HI LB FF LK1 cr A1 M1 (vml_of m1)) /\
            (forall a, CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\
            (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> M (Z_to_bv 64 a) <> None -> M1 (Z_to_bv 64 a) <> None)).
  { intros i E A1 M1 m1 HA1. pose proof HA1 as (_ & _ & _ & HagE & (cr1 & LK1 & HH1 & _ & HC1 & _) & Hfr1 & Hdf1).
    unfold CHA.curB, CHA.curF in HH1. rewrite CPA.NOBnil, CPA.NOFnil in HH1. cbn [CH2.den CHA.denF map app] in HH1. unfold CPA.Cred0 in HC1. subst cr1.
    split; [exact HagE|]. split; [exists LK1; exact HH1|]. split; [exact Hfr1 | exact Hdf1]. }
  assert (TXTK : forall a, s <= a < s + (N + 1) -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) W a).
  { intros a Ha. rewrite SCRV. apply (FLA.txt_kept L ar C HI HIok _ _ _ _ _ _ _ s (N + 1) _ _ _ _ HH Hblk'); [lia | | exact Ha].
    intros w Hw. unfold W in Hw. cbn [In] in Hw. unfold hide in Ap2, Ap3. destruct Hw as [<-|[<-|[]]]; cbn [fst snd]; [clear - Ap2; lia | clear - Ap3; lia]. }
  destruct pcs_ok as (Hpc0 & Hps0 & Hps1 & Hps2 & Hnx1 & Hnx2). destruct pss_ok as (PS0 & PS1 & PS2).
  unfold PMSA.cfg. rewrite <- Hpc0.
  eapply (CPA.pure_cert_soundA L ar C HI HIok LYI LYR LYB LYN NFs E0 M model A LB FF LK cr sp G.HDECL W W 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS G.TAGS K PMSA.fp_ok DEF0 (fun i E _ _ _ => XI (s + N) i E) R r EV Hra Hraok [RET_PC] FPM) with (i := 0%nat).
  - rewrite LS. exact (G.plans lems).
  - exact G.tags_ok.
  - exact heap_ok.
  - exact pure_ok.
  - rewrite LS. intros pc [<-|[]]. exact ret_pc_ok.
  -
    intros i c1 k ps j sb IL. exfalso. destruct IL as (tags & Hc1 & Htags & Hps & Htag). rewrite tags_eq in Htags.
    destruct i as [|[|[|i]]]; cbn [nth_error] in Htags; [| | | destruct i; discriminate Htags]; injection Htags as <-; destruct k as [|[|k]]; cbn [nth_error] in Htag; discriminate Htag.
  -
    intros i c1 k ps pc IL Hex. destruct IL as (tags & Hc1 & Htags & Hps & Htag). rewrite tags_eq in Htags.
    destruct i as [|[|[|i]]]; cbv [G.CPS nth_error] in Hc1; [| | | destruct i; discriminate Hc1]; injection Hc1 as <-; cbn [nth_error] in Htags; injection Htags as <-;
      (destruct k as [|[|k]]; cbn [nth_error] in Htag; try discriminate Htag); injection Htag as <-; [rewrite PS0 in Hps | rewrite PS1 in Hps | exfalso; vm_compute in Hex; discriminate Hex];
      cbn [nth_error] in Hps; injection Hps as <-.
    +
      intros fx' E R1 A1 M1 m1 E' R' M2 m2 HAt1 HAX HFP Hag HLF HIH. pose proof HAX as [HA1 HX].
      pose proof (LEAF 0%nat G.cp0 ps0 E E' R1 R' A1 M1 m1 M2 m2 eq_refl HAt1 HA1 Hag HLF) as HA2.
      destruct (AMBP _ _ _ _ _ HA2) as (HagE & (LK2 & HH2) & Hfr2 & Hdf2).
      pose proof (CBA.amb_off L ar C HI HIok LYB NFs E0 M model A LB FF LK sp G.HDECL W (CPA.NOB G.CPS) (CPA.NOF G.CPS) (CPA.Cred0 cr) 0 0%nat E A1 M2 m2 HA2) as Hoff.
      destruct fs_ci_facts as (Xnx & Xcsp & Xregs). destruct fs_leaf_facts as (X10 & X11 & X12 & Krp & K184 & K192 & Kg & Kimg).
      set (F := sp - 272).
      refine (CVFA.callee_leafLB L ar C HI HIok LYI LYR NFs E0 M model A LB FF LK cr sp G.HDECL W W 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                G.CPS K PMSA.fp_ok DEF0 S6 [] GLO GHI SC_OK GOT_OK (fun i E _ _ _ => XI (s + N) i E) HKnil FS_PC WIN 1 0 [(F + 8, 8); (PDC.a_TP AD - 164, 4)] FSW FSNEWS None
                0%nat G.cp0 ps0 1%nat G.cp1 FSCI (PDCA.fs_preA L ar AD (sp + CH2.ci_csp FSCI) F s CAN txt) (PDCA.fs_postA L F s txt) eq_refl fs_ci Hps0 (Z.le_refl 0)
                fx' E R1 A1 M1 m1 E' R' M2 m2 HAt1 HAX HFP Hag HLF HIH _ _).
      * intros LB' FF' LK' cr' A'. exact (FSOA.floatscan_okA L ar C HI HIok LAY FL (CC.cp_pc G.cp1) (sp + CH2.ci_csp FSCI) F s CAN txt LB' FF' LK' cr' A').
      * intros LKu CF HHu HLKu.
        pose proof (CHA.ca_regs L ar HI NFs E0 M model A LB FF LK sp G.HDECL W (CPA.NOB G.CPS) (CPA.NOF G.CPS) (CPA.Cred0 cr) 0 WIN 1 G.cp0 ps0 G.cp1 FSCI 0 E E' R' A1 M2 m2 CF) as HR.
        pose proof (CHA.ca_know L ar HI NFs E0 M model A LB FF LK sp G.HDECL W (CPA.NOB G.CPS) (CPA.NOF G.CPS) (CPA.Cred0 cr) 0 WIN 1 G.cp0 ps0 G.cp1 FSCI 0 E E' R' A1 M2 m2 CF) as HK.
        clear Hcont LEAF AMBP CELLS WOK WRS_OK CRS_OK IMG_OK HIH HLF HAX HA1 HA2 HAt1 CF VS VT VG VE DS DT DE.
        rewrite Xregs in HR. set (regs := CA.ps_reglist ps0) in *.
        assert (HagE1 : env_agree NFs E0 E') by (eapply CC.env_agree_trans; [exact HagE | eapply CC.env_agree_le; [exact Hag | vm_compute; lia]]).
        assert (EVf : forall n, (n < 34)%nat -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE1); exact Hn).
        assert (U2' : bv_unsigned (ev E' 2) = sp) by (rewrite EVf by lia; exact U2).
        assert (Hm272 : forall e, bv_unsigned (edenot E' e) = sp -> bv_unsigned (edenot E' (APC.eaddz e (-272))) = sp - 272).
        { intros e He. unfold APC.eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite He. change (bv_unsigned (Z_to_bv 64 (-272))) with (2 ^ 64 - 272).
          replace (sp + (2 ^ 64 - 272)) with (sp - 272 + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
        assert (G10 : PDC.rz R' 10 = F) by (unfold PDC.rz; rewrite (reg_read regs E' R' 10 _ HR ltac:(lia) X10); apply Hm272; exact U2').
        assert (G11 : PDC.rz R' 11 = 1) by (unfold PDC.rz; rewrite (reg_read regs E' R' 11 _ HR ltac:(lia) X11); cbn [edenot]; apply u64_of_Z; lia).
        assert (G12 : PDC.rz R' 12 = 1) by (unfold PDC.rz; rewrite (reg_read regs E' R' 12 _ HR ltac:(lia) X12); cbn [edenot]; apply u64_of_Z; lia).
        assert (ESr : forall o, estart E' (SA (EVar 2) o) = sp + o) by (intros o; apply (DOS.estart_reg E' 2 o sp U2')).
        assert (CELL : forall o z, has (SR.ps_cells ps0) (KWord (SA (EVar 2) o) 8 (ELit z)) = true -> 0 <= z < 2 ^ 64 -> L5.u64_at (hl_segs L) M2 (sp + o) z).
        { intros o z Hc Hz. apply (CL5A.u64_full (hl_segs L) _ Hoff).
          apply (CL5.kword64_elim (hl_segs L) E' _ _ _ (sp + o) _ (proj1 (Forall_forall _ _) HK _ (has_In _ _ Hc)) (ESr o)). cbn [edenot]. apply u64_of_Z. exact Hz. }
        assert (Hrp : L5.u64_at (hl_segs L) M2 (F + 8) s).
        { replace (F + 8) with (sp + -264) by (unfold F; lia). apply (CL5A.u64_full (hl_segs L) _ Hoff).
          apply (CL5.kword64_elim (hl_segs L) E' _ _ _ (sp + -264) _ (proj1 (Forall_forall _ _) HK _ (has_In _ _ Krp)) (ESr (-264))). cbn [edenot]. rewrite EVf by lia. exact U10. }
        assert (Hgd : L5.u64_at (hl_segs L) M2 GADDR CAN).
        { apply (CL5A.u64_full (hl_segs L) _ Hoff).
          apply (CL5.kword64_elim (hl_segs L) E' _ _ _ GADDR _ (proj1 (Forall_forall _ _) HK _ (has_In _ _ Kg))); [rewrite DOS.estart_lit by (unfold GADDR; lia); lia|].
          cbn [edenot]. rewrite EVf by lia. exact U32. }
        assert (IMGC2 : L5.img_clear M2 IMG_LO IMG_HI).
        { pose proof (proj1 (Forall_forall _ _) HK _ (has_In _ _ Kimg)) as HKi. cbn [kentry_ok] in HKi. destruct HKi as (_ & _ & I3). intros a Ha. specialize (I3 a Ha).
          unfold CCA.vis, mrestrict in I3. rewrite (CHA.img_vis L ar C HI HIok LYI NFs sp NF32 _ _ _ _ _ _ _ a HH2 ltac:(rewrite IHI; unfold IMG_LO, IMG_HI in Ha; lia)) in I3. exact I3. }
        assert (DEFf : forall d, 0 <= d < 272 -> M2 (Z_to_bv 64 (sp - 272 + d)) <> None).
        { intros d Hd. apply Hdf2; [lia | right; left; split; lia |]. replace (sp - 272 + d) with (sp - 8944 + (8672 + d)) by lia. apply S5. lia. }
        assert (TXT2 : PDC.text_ok (hl_segs L) M2 s txt).
        { unfold PDC.text_ok. fold N. split; [|split; [|split; [lia | split; [lia | split; [lia | split]]]]].
          - intros j Hj. apply (u8_at_same (hl_segs L) M M2 (s + Z.of_nat j) _ ltac:(lia) ltac:(unfold N in *; lia)); [|exact (Tb j Hj)].
            intros x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hfr2. apply TXTK. unfold N in *. lia.
          - apply (u8_at_same (hl_segs L) M M2 (s + N) _ ltac:(lia) ltac:(lia)); [|exact Tn]. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hfr2. apply TXTK. lia.
          - intros d Hd. destruct Hblk as (b & Hb & B1 & B2). apply Hdf2; [lia | left; exists b; split; [exact Hb | lia] | apply Tdef; lia].
          - exact (PSP.final_bytes txt Hnf). }
        split.
        --
           unfold PDCA.fs_preA. rewrite Xcsp. cbn [PDC.a_G PDC.a_img_lo PDC.a_img_hi AD PDCA.cboth].
           split; [exact G10|]. split; [exact G11|]. split; [exact G12|]. split.
           { unfold PDC.file_ok, PDC.STK_FLOOR. split; [exact Hrp|]. split.
             { replace (F + 184) with (sp + -88) by (unfold F; lia). apply (CELL (-88) _ K184). lia. }
             split; [replace (F + 192) with (sp + -80) by (unfold F; lia); apply (CELL (-80) _ K192); lia|]. split; [|unfold F; lia].
             apply (L5C.writable_of_defined (hl_segs L) M2 (F + 8) 8); [|unfold F; lia | unfold F; lia]. intros d Hd. unfold F. replace (sp - 272 + 8 + d) with (sp - 272 + (8 + d)) by lia. apply DEFf. lia. }
           split; [unfold F; lia|]. split; [intros d Hd; unfold F; replace (sp - 272 + 8 + d) with (sp - 272 + (8 + d)) by lia; apply DEFf; lia|].
           split; [exact Hgd|]. split; [exact RCAN|]. split; [exact TXT2|]. split; [fold N; left; exact Hblk'|].
           split; [unfold PDC.apart; left; unfold F; clear - TB2 S2 CL; lia|]. split; [exact Hnf | exact IMGC2].
        --
           intros R2 M3 model3 LK3 A3 HPo HRP2 HP3 HH3. unfold PDCA.fs_postA in HPo. fold N in HPo.
           exists [Z_to_bv 64 (s + N)]. split; [reflexivity|]. cbv zeta. rewrite Xnx.
           set (E2 := CH2.retEx E' 34 [Z_to_bv 64 (s + N)] R2).
           assert (Gh : ev E2 34 = Z_to_bv 64 (s + N)) by (exact (CH2.retEx_ghost E' 34 [Z_to_bv 64 (s + N)] R2 0 ltac:(cbn; lia))).
           pose proof (CH2.retEx_agree E' 34 [Z_to_bv 64 (s + N)] R2 : env_agree 34 E' E2) as Hag2.
           assert (U2e : bv_unsigned (ev E2 2) = sp) by (rewrite <- (proj1 Hag2 2%nat) by lia; exact U2').
           split; [exact I|]. split; [|split; [|split]].
           ++ intros w a Hw Hin. cbn [In] in Hw. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
              ** exists (EVar 2, -264, ELit 8). split; [left; reflexivity|]. unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite U2'. rewrite u64_of_Z by lia. unfold F in Hin. lia.
              ** exists (EVar 4, -164, ELit 4). split; [right; left; reflexivity|]. unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite EVf by lia. rewrite U4. rewrite u64_of_Z by lia.
                 cbn [PDC.a_TP AD PDCA.cboth] in Hin. unfold TPV. lia.
           ++ intros w a Hw Hin [_ [Hc Ho]]. cbn [In] in Hw. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
              ** rewrite SCRV in Hc. unfold F in Hin. destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
                 +++ destruct Hc as (b & Hb & Hc). destruct (FLA.blk_facts L ar C HI HIok _ _ _ _ _ _ _ b HH Hb) as (B1 & B2 & _). lia.
                 +++ lia.
                 +++ lia.
                 +++ destruct Hc as (f & Hf & X1 & X2). destruct (CHA.rf_frm _ _ _ _ RFx f Hf) as (F1 & F2 & _). lia.
                 +++ pose proof (CHA.shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(lia) ltac:(lia) ltac:(lia) Hc). lia.
                 +++ destruct Hc as (f & Hf & X). destruct (CHA.rf_frm _ _ _ _ RFx f Hf) as (F1 & F2 & _ & _ & F5).
                     pose proof (CHA.shadow_range (ff_addr f) (ff_bytes (ff_class f)) a ltac:(lia) ltac:(lia) ltac:(lia) X). lia.
                 +++ destruct Hc as (b & Hb & X). destruct (FLA.blk_facts L ar C HI HIok _ _ _ _ _ _ _ b HH Hb) as (B1 & B2 & B3 & B4 & B5 & B6).
                     pose proof (CHA.shadow_range (fst b) (snd b) a ltac:(lia) ltac:(lia) ltac:(lia) X). lia.
              ** apply (Ho (hl_tp L - 164, 4)); [unfold W; cbn; tauto|]. unfold L5.in_rng; cbn [fst snd]. cbn [PDC.a_TP AD PDCA.cboth] in Hin. rewrite TP. lia.
           ++ unfold XI. exact Gh.
           ++ intros X HXn _. unfold FSNEWS in HXn. cbn [In] in HXn. destruct HXn as [<-|[]].
              assert (VF3 : CL5A.visr (ahid A3 model3) (F + 8) 8) by (apply (FLA.stk_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH3); unfold F; lia).
              apply (CL5.kword64_intro (hl_segs L) E2 _ _ _ (F + 8) (s + N)); [rewrite (DOS.estart_reg E2 2 (-264) sp U2e); unfold F; lia | unfold F; lia | unfold F; lia | cbn [edenot]; exact Gh |].
              exact (CL5A.u64_vis (hl_segs L) (ahid A3 model3) M3 (F + 8) (s + N) ltac:(unfold F; lia) ltac:(unfold F; lia) VF3 HPo).
    +
      intros fx' E R1 A1 M1 m1 E' R' M2 m2 HAt1 HAX HFP Hag HLF HIH. pose proof HAX as [HA1 HX].
      refine (CPA.pure_callee_leaf L ar C HI HIok LYI LYR NFs E0 M model A LB FF LK cr sp G.HDECL W W 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                G.CPS K PMSA.fp_ok DEF0 S6 [] GLO GHI SC_OK GOT_OK (fun i E _ _ _ => XI (s + N) i E) HKnil TR_PC 0 0 [] [] [] None 1%nat G.cp1 ps1 2%nat G.cp2 TRCI
                (fun _ Mx => CVF.img_pre_of None Mx) (fun _ _ _ _ => True) eq_refl tr_ci Hps1 (Z.le_refl 0) fx' E R1 A1 M1 m1 E' R' M2 m2 HAt1 HAX HFP Hag HLF HIH _ _).
      * exact (Leaf_trunctfdf2_cboth.ok L ar C HI HIok LAY (CC.cp_pc G.cp2) (sp + CH2.ci_csp TRCI)).
      * intros LKu CF HHu HLKu. split; [exact I|]. intros R2 M3 model3 LK3 A3 _ _ _ _. cbv zeta.
        split; [exact I|]. split; [intros w a []|]. split; [intros w a []|]. split; [|intros X []].
        pose proof (CHA.ca_vars L ar HI NFs E0 M model A LB FF LK sp G.HDECL W (CPA.NOB G.CPS) (CPA.NOF G.CPS) (CPA.Cred0 cr) 0 0 0 G.cp1 ps1 G.cp2 TRCI 1 E E' R' A1 M2 m2 CF) as (_ & _ & W3 & _).
        rewrite Hnx1 in W3. unfold XI. unfold XI in HX.
        rewrite <- (proj1 (CH2.retEx_agree E' (CH2.ci_nx TRCI) [] R2) 34%nat) by lia. rewrite <- (proj1 Hag 34%nat) by (rewrite Hnx1; lia). exact HX.
  -
    intros i c1 k ps pc IL Hin fx' E R1 A1 M1 m1 E' R' M2 m2 HAt1 HAX HFP1 Hag HLF model2 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HagE' HA'.
    pose proof HAX as [HA1 HX]. destruct IL as (tags & Hc1 & Htags & Hps & Htag). rewrite tags_eq in Htags.
    destruct i as [|[|[|i]]]; cbv [G.CPS nth_error] in Hc1; [| | | destruct i; discriminate Hc1]; injection Hc1 as <-; cbn [nth_error] in Htags; injection Htags as <-;
      (destruct k as [|[|k]]; cbn [nth_error] in Htag; try discriminate Htag); injection Htag as <-; [exfalso; destruct Hin as [Hin|[]]; discriminate Hin | exfalso; destruct Hin as [Hin|[]]; discriminate Hin |].
    rewrite PS2 in Hps. cbn [nth_error] in Hps. injection Hps as <-.
    pose proof (CBA.amb_off L ar C HI HIok LYB NFs E0 M model A LB FF LK sp G.HDECL W (CPA.NOB G.CPS) (CPA.NOF G.CPS) (CPA.Cred0 cr) 0 2%nat E A1 M2 m2 HA') as Hoff.
    destruct (AMBP _ _ _ _ _ HA1) as (HagE & _ & _ & _).
    assert (U11' : bv_unsigned (ev E' 11) = endp) by (rewrite <- (proj1 Hag 11%nat) by (rewrite Hnx2; lia); rewrite <- (proj1 HagE 11%nat) by (unfold NFs; lia); exact U11).
    assert (E34 : ev E' 34 = Z_to_bv 64 (s + N)) by (rewrite <- (proj1 Hag 34%nat) by (rewrite Hnx2; lia); unfold XI in HX; exact HX).
    assert (Hend : L5.u64_at (hl_segs L) M2 endp (s + N)).
    { apply (CL5A.u64_full (hl_segs L) _ Hoff).
      apply (CL5.kword64_elim (hl_segs L) E' _ _ _ endp _ (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ (has_In _ _ exit_fact))).
      - rewrite (DOS.estart_reg E' 11 0 endp U11'). lia.
      - cbn [edenot]. rewrite E34. apply u64_of_Z. lia. }
    rewrite SCRV in HP.
    apply (Hcont fx' R' M2 model2 LB cr LB W LK1 A1 HFP1); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    split; [unfold PMSA.u64; fold N; exact Hend|]. repeat split; reflexivity.
  - reflexivity.
  -
    split.
    + apply DOK.regs_ok_tmpl. intros n Hn. do 32 (destruct n as [|n]; [first [reflexivity | lia]|]). lia.
    + change (CCA.vis A model M) with Mv.
      assert (ES2 : forall o, estart E0 (SA (EVar 2) o) = sp + o) by (intros o; apply (DOS.estart_reg E0 2 o sp U2)).
      assert (ES11 : forall o, estart E0 (SA (EVar 11) o) = endp + o) by (intros o; apply (DOS.estart_reg E0 11 o endp U11)).
      assert (ES4 : forall o, estart E0 (SA (EVar 4) o) = TPV + o) by (intros o; apply (DOS.estart_reg E0 4 o TPV U4)).
      assert (EL : forall z, 0 <= z < 2 ^ 64 -> elenZ E0 (ELit z) = z) by (intros z Hz; apply DOS.elen_lit; exact Hz).
      assert (ERR : hl_img_lo L <= TPV - 164 /\ TPV - 164 + 4 <= hl_img_hi L) by (destruct (CELLS (TPV - 164) ltac:(lia)) as [X _]; destruct (CELLS (TPV - 164 + 3) ltac:(lia)) as [Y _]; lia).
      assert (GR : hl_img_lo L <= GADDR /\ GADDR + 8 <= hl_img_hi L) by (destruct (CELLS GADDR ltac:(lia)) as [X _]; destruct (CELLS (GADDR + 7) ltac:(lia)) as [Y _]; lia).
      clear Hcont LEAF AMBP WOK WRS_OK CRS_OK IMG_OK TXTK FPM SC_OK GOT_OK CELLS LYR LYB LYN EV.
      (let k := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with k). unfold know_ok.
      apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; lia|].
      apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; split; [lia | exact S1]|].
      apply Forall_cons; [cbn [kentry_ok]; split; [lia | split; [lia |]]; intros a Ha; unfold Mv, CCA.vis, mrestrict; destruct (ahid A model (Z_to_bv 64 a)); [reflexivity | exact (Himg a Ha)]|].
      apply Forall_cons; [apply (CL5.kwr_intro (hl_segs L) E0 Mv _ _ (sp - 8944) 8944); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | exact DS]|].
      apply Forall_cons; [apply (CL5.kunk_intro (hl_segs L) E0 Mv _ _ (sp - 8944) 8944); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | exact DS]|].
      apply Forall_cons; [apply (CL5.kword64_intro (hl_segs L) E0 Mv _ _ GADDR CAN); [rewrite DOS.estart_lit by lia; lia | lia | lia | reflexivity | apply (CL5A.u64_vis _ H M); [lia | lia | exact VG | exact Hguard]]|].
      apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U10; lia|].
      apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U33; lia|].
      apply Forall_cons; [apply (CL5.kwr_intro (hl_segs L) E0 Mv _ _ endp 8); [rewrite ES11; lia | apply EL; lia | lia | lia | lia | exact DE]|].
      apply Forall_cons; [apply (CL5.kunk_intro (hl_segs L) E0 Mv _ _ endp 8); [rewrite ES11; lia | apply EL; lia | lia | lia | lia | exact DE]|].
      apply Forall_cons; [cbn [kentry_ok]; rewrite ES11, ES2, !EL by lia; unfold hide in EA5; clear - EA5 S2; lia|].
      apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U11; lia|].
      apply Forall_cons; [cbn [kentry_ok]; rewrite ES11, DOS.estart_lit, !EL by lia; unfold hide in EAI; clear - EAI GR Dg; lia|].
      apply Forall_cons; [cbn [kentry_ok]; rewrite ES11, ES4, !EL by lia; unfold hide in EAI; clear - EAI ERR Dtpv; lia|].
      apply Forall_cons; [cbn [kentry_ok]; rewrite ES4, ES2, !EL by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U4; unfold TPV; lia | constructor].
  - exact I.
  - exact HH.
  - exact Hmo.
  - exact Hroom.
  - exact Hfp.
Qed.
End Final.
End STOA.
