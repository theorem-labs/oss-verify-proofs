(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto HeapIface HeapIfaceA L5Defs L5Core L5LazyA
  Pm5PlanKit Pm5L5DefsA FrmInv Pm5FrmInv FpBridge Pm5FpSites PmHeapIfaceA PmLibDefs PmLibDefsA PmLibSpecsA CutVFXM DecIface DecJson DecScanPure DecOkDefsM DecOkSemM DecIfaceA StrtodPure
  StrtodIface FloatLazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutVF.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD CutCertA CutHeapA CutL5A CutBridgeA CutPureA CutVFA CutVFT Pm5CutKitD DecAssume
  Pm5Leaf_extendsftf2.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_fsinf_xboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FSIA.
Module G := Cut_fsinf_xboth.
Definition AD : PDC.addrs := PDCA.xboth.
Definition ENTRY : Z := 1381192.   Definition RET_PC : Z := 1384048.   Definition XS_PC : Z := 1327220.
Definition GADDR : Z := 7084240.   Definition TPV : Z := 6953104.
Definition IMG_LO : Z := 65536.    Definition IMG_HI : Z := 1466368.
Definition GLO : Z := 1433600.     Definition GHI : Z := 1433600.
Definition NFs : nat := 34.        Definition WIN : Z := 8672.
Definition INL : list Z := [1383880; 1383888; 1383892; 1383296].      (* [comment removed for export] *)
Lemma ad_ok : PDC.a_TP AD = TPV /\ PDC.a_G AD = GADDR /\ PDC.a_img_lo AD = IMG_LO /\ PDC.a_img_hi AD = IMG_HI. Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Definition TXT_INF : list Z := [105; 110; 102].   Definition TXT_NAN : list Z := [110; 97; 110].
Definition infnan (txt : list Z) : Prop := In txt [TXT_INF; 45 :: TXT_INF; TXT_NAN; 45 :: TXT_NAN].
Definition idx_of (txt : list Z) : nat := match txt with 45 :: 105 :: _ => 1 | 110 :: _ => 2 | 45 :: _ => 3 | _ => 0 end.

(* [comment removed for export] *)
Lemma heap_ok : CHA.heap_chkA NFs G.HDECL (CPA.NOB G.CPS) (CPA.NOF G.CPS) G.CPS G.TAGS = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma pure_ok : CH2.leaves_all G.CPS G.TAGS (CPA.pure_leaf_chk NFs G.HDECL [RET_PC]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma foot_ok : CC.cps_all G.CPS (fun _ c => CHA.foot_chk NFs G.HDECL c [] []) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hd_ok : CH.hd_scr G.HDECL = 8672 /\ CH.hd_wrs G.HDECL = [(EVar 10, 8, ELit 8)] /\ CH.hd_crs G.HDECL = [(ELit 0, GADDR, ELit 8)] /\ CH.hd_img G.HDECL = [(IMG_LO, IMG_HI)].
Proof. repeat split; reflexivity. Qed.
Lemma ret_pc_ok : CL.is_ret_at RSEGS RET_PC.
Proof. CL.solve_is_ret. Qed.
Lemma lems : G.LEMS_OK. Proof. unfold G.LEMS_OK, CXD.LEMS_OK, G.LEMS. apply Forall_nil. Qed.

(* [comment removed for export] *)
Definition lchk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc RET_PC then true else
      existsb (fun e : nat * nat * nat * Z => let '(j, i', k', pc') := e in
                 (Nat.eqb i' i && Nat.eqb k' k && Z.eqb pc' pc && Bool.eqb (Nat.odd i) (Nat.odd j) &&
                  CHA.foot_chk NFs G.HDECL c [] [] && Nat.leb NFs (CC.cp_nx c) && Z.eqb (SR.ps_pc ps) pc &&
                  match nth_error G.CPS j with
                  | Some cj => if existsb (Z.eqb pc) INL then CVF.inl_chk c ps cj 4 [] None
                               else (Z.eqb pc XS_PC && CVFA.call_chkA NFs G.HDECL [] GLO GHI c ps cj 0 None)%bool
                  | None => false
                  end)%bool) G.RETS
  end.
Lemma leaves_ok : CH2.leaves_all G.CPS G.TAGS lchk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
(* [comment removed for export] *)
Definition xchk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc => if Z.eqb pc RET_PC then has (SR.ps_cells ps) (KWord (SA (EVar 10) 8) 8 (EAlu ALU_ADD (EVar 32) (ELit (if Nat.odd i then 4 else 3)))) else true
  | _ => true
  end.
Lemma exits_ok : CH2.leaves_all G.CPS G.TAGS xchk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma inl_sites : forall q, existsb (Z.eqb q) INL = true -> FPB.inl_step RSEGS q 4 [].
Proof.
  intros q Hq. unfold INL in Hq. cbn [existsb] in Hq.
  destruct (Z.eqb q 1383880) eqn:E1; [apply Z.eqb_eq in E1; subst q; exact Pm5FpSites.site_151d8c|].
  destruct (Z.eqb q 1383888) eqn:E2; [apply Z.eqb_eq in E2; subst q; exact Pm5FpSites.site_151d94|].
  destruct (Z.eqb q 1383892) eqn:E3; [apply Z.eqb_eq in E3; subst q; exact Pm5FpSites.site_151d98|].
  destruct (Z.eqb q 1383296) eqn:E4; [apply Z.eqb_eq in E4; subst q; exact Pm5FpSites.site_151b44|].
  discriminate Hq.
Qed.

Definition ghost (s CAN : Z) (n : nat) : word := match n with 32 => Z_to_bv 64 s | 33 => Z_to_bv 64 CAN | _ => Z_to_bv 64 0 end%nat.
Definition mkE (R : bvmap 5 word) (s CAN : Z) : env := Env (reg_ev R (ghost s CAN)) (fun _ => []).

Section Final.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout. Variable ar : asan_run. Variable C : asan_statics_cells. Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FL : PDCA.float_layoutA L AD.

(* [comment removed for export] *)
Definition txt_homeA (LB : list (Z * Z)) (FF : list fframe) (sp s n : Z) : Prop := PDCA.txt_home ar LB FF sp s n.   (* [comment removed for export] *)
Definition fs_pre_nf (sp F s CAN : Z) (txt : list Z) (LB : list (Z * Z)) (FF : list fframe) (R : bvmap 5 word) (M : PDCA.mem) : Prop :=
  PDC.rz R 10 = F /\ PDC.rz R 11 = 1 /\ PDC.rz R 12 = 1 /\ PDC.file_ok (hl_segs L) M F s /\ sp <= F + 8 /\ L5.defined M (F + 8) 8 /\
  L5.u64_at (hl_segs L) M (PDC.a_G AD) CAN /\ 0 <= CAN < 2 ^ 64 /\
  PDC.text_ok (hl_segs L) M s txt /\ txt_homeA LB FF sp s (Z.of_nat (length txt) + 1) /\ PDC.apart s (Z.of_nat (length txt) + 1) (F + 8) 192 /\
  infnan txt /\ L5.img_clear M (PDC.a_img_lo AD) (PDC.a_img_hi AD).
Definition floatscan_nf_contractA (pc : Z) : Prop :=
  forall r sp F s CAN txt, PDCA.cps_pureLB L ar HI PMSA.fp_ok pc r sp PSI.WIN 0 [(F + 8, 8); (PDC.a_TP AD - 164, 4)] (fs_pre_nf sp F s CAN txt) (PDCA.fs_postA L F s txt).

Theorem floatscan_nf_okA : floatscan_nf_contractA ENTRY.
Proof.
  intros r sp F s CAN txt LB FF LK cr A fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs Hpre Hcont.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (FPM : forall (fx fx' : FPState) R0 pc M0 R' pc' M', msteps (hl_segs L) (@mkst fx R0 (Z_to_bv 64 pc) M0 (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx').
  { rewrite LS. intros fx0 fx' R0 pc M0 R' pc' M' H Hf. exact (Pm5FrmInv.msteps_fp_ok fx0 fx' R0 _ M0 _ R' _ M' _ H Hf). }
  pose proof FL as [TP CELLS]. cbn [PDC.a_TP PDC.a_G PDC.a_img_lo PDC.a_img_hi AD PDCA.xboth] in TP, CELLS.
  destruct Hpre as (RF & R11 & R12 & Hfile & HspF & Hfd8 & Hguard & RCAN & Htext & Hhome & Hapf & Hin & Himg).
  destruct Hfile as (Hf8 & Hf184 & Hf192 & Hfw & HF1 & HF2). destruct Htext as (Tb & Tn & TQ1 & TQ2 & TQ3 & Td & Tr).
  cbn [PDC.a_G PDC.a_TP PDC.a_img_lo PDC.a_img_hi AD PDCA.xboth] in Hguard, Himg.
  set (N := Z.of_nat (length txt)) in *. assert (HN0 : 0 <= N) by (unfold N; lia).
  assert (HNv : N = 3 \/ N = 4) by (unfold N; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia).
  pose proof (FLA.rng L ar C HI HIok _ _ _ _ _ _ _ HH) as RFx. destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6). unfold PSI.WIN, PDC.STK_FLOOR in *.
  (* [comment removed for export] *)
  assert (TXR : 4096 <= s /\ s + (N + 1) <= 2 ^ 47 /\ (s + (N + 1) <= ahl_ceil ar \/ sp <= s) /\ (s + (N + 1) <= hl_img_lo L \/ hl_img_hi L <= s)).
  { unfold txt_homeA, PDCA.txt_home in Hhome. destruct Hhome as [Hb|Ho].
    - destruct (FLA.txt_facts L ar C HI HIok _ _ _ _ _ _ _ s (N + 1) HH Hb) as (TB1 & TB2 & TB3 & TB4 & TB5). lia.
    - pose proof (CL5A.acobj_rng L ar LB FF sp s (N + 1) RFx ltac:(lia) Ho ltac:(lia)) as (O1 & O2 & O3 & O4 & O5).
      split; [lia|]. split; [lia|]. split; [exact O5|].
      destruct Ho as [Hf|[H1 H2]]; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (CL5A.infr_rng L ar LB FF s (N + 1) RFx Hf ltac:(lia)))))))) |].
      right. rewrite IHI. pose proof (L5A.aly_img_hi L C LAY) as X. clear - H1 CL S2 IHI. lia. }
  destruct TXR as (TX1 & TX2 & TX3 & TX4).
  assert (TXS : s + (N + 1) <= sp - 8672 \/ sp <= s) by (clear - TX3 S2 CL; lia).
  (* [comment removed for export] *)
  set (H := ahid A model). set (Mv := CCA.vis A model M).
  assert (VS : CL5A.visr H (sp - 8672) 8672) by (apply (FLA.stk_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH); lia).
  assert (VG : CL5A.visr H GADDR 8).
  { intros i Hi. apply (CHA.img_vis L ar C HI HIok LYI NFs sp ltac:(unfold NFs; lia) _ _ _ _ _ _ _ (GADDR + i) HH). rewrite IHI. unfold GADDR. lia. }
  assert (VF : CL5A.visr H (F + 8) 192) by (apply (FLA.stk_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH); lia).
  assert (VT : CL5A.visr H s (N + 1)).
  { unfold txt_homeA, PDCA.txt_home in Hhome. destruct Hhome as [Hb|Ho]; [exact (FLA.txt_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH Hb)|].
    intros i Hi. destruct (CL5A.acobj_wok L ar LB FF sp 8672 s (N + 1) (s + i) RFx ltac:(lia) Ho ltac:(lia)) as (X1 & X2 & X3).
    apply (CHA.client_vis L ar C HI HIok LB FF LK cr A M model sp 8672 (s + i) HH X1); [| exact X3].
    unfold aclient. unfold aclientw in X2. refine (aclient_g_mono _ _ _ _ L ar LB FF sp 8672 (s + i) _ _ X2); [intros q n x [] | intros x Hx; left; exact Hx]. }
  assert (DS : L5.defined Mv (sp - 8672) 8672) by (exact (CL5A.defined_vis H M _ _ VS S5)).
  assert (DT : L5.defined Mv s (N + 1)) by (apply (CL5A.defined_vis H M _ _ VT); unfold N; exact Td).
  assert (DF8 : L5.defined Mv (F + 8) 8) by (apply (CL5A.defined_vis H M); [apply (CL5A.visr_sub _ (F + 8) 192 (F + 8) 8 VF); lia | exact Hfd8]).
  (* [comment removed for export] *)
  set (E0 := mkE R s CAN).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (Usp : bv_unsigned (getr R 2%bv) = sp) by (rewrite Hsp; apply u64_of_Z; lia).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by exact Usp.
  assert (U10 : bv_unsigned (ev E0 10) = F) by (change (ev E0 10) with (getr R 10%bv); exact RF).
  assert (U32 : bv_unsigned (ev E0 32) = s) by (change (ev E0 32) with (Z_to_bv 64 s); apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = CAN) by (change (ev E0 33) with (Z_to_bv 64 CAN); apply u64_of_Z; lia).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  destruct hd_ok as (SCRV & HWRS & HCRS & HIMG).
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= NFs)%nat) by (unfold NFs; lia).
  set (W := [(F + 8, 8); (hl_tp L - 164, 4)] : list L5.range).
  assert (WOK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a Hw Hin'. unfold W in Hw. cbn [In] in Hw. rewrite SCRV. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin'; cbn [fst snd] in Hin'.
    - split; [lia|]. split; [right; left; split; lia|]. apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). unfold BIGSHADOW_HI. lia.
    - rewrite TP in Hin'. destruct (CELLS a ltac:(lia)) as (C1 & C2 & C3 & _). split; [lia|].
      split; [right; right; left; split; [exact C1 | intros [X|X]; [exact (C2 X) | exact (C3 X)]]|]. apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). lia. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt NFs rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { rewrite HWRS. intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (F + 8, 8). split; [unfold W; cbn; tauto | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt NFs rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { rewrite HCRS. intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha. unfold CHA.sclientA; rewrite SCRV.
    rewrite !u64_of_Z in Ha by lia. unfold GADDR in Ha. destruct (CELLS a ltac:(lia)) as (C1 & C2 & C3 & _). split; [lia|]. split; [right; right; left; split; [exact C1 | exact C2]|].
    apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). lia. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { rewrite HIMG. intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. unfold IMG_LO, IMG_HI in Ha. rewrite ILO, IHI. split; [lia | intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); lia]. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SC_OK : incl (@nil (Z * Z * Z)) (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) (@nil (Z * Z * Z)))
    by (split; [intros x [] | apply Forall_nil]).
  assert (GOT_OK : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L)
    by (unfold GLO, GHI; rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI; lia).
  (* [comment removed for export] *)
  set (XI := fun (i : nat) (_ : env) (_ : list (Z * Z)) (_ : PDCA.mem) (_ : Model) => Nat.odd i = Nat.eqb (length txt) 4).
  set (c0 := nth (idx_of txt) G.CPS G.cp0).
  assert (Hc0 : nth_error G.CPS (idx_of txt) = Some c0) by (unfold c0; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; reflexivity).
  assert (Hpc0 : CC.cp_pc c0 = ENTRY) by (unfold c0; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; reflexivity).
  unfold PMSA.cfg. rewrite <- Hpc0.
  eapply (CPA.pure_cert_soundA L ar C HI HIok LYI LYR LYB LYN NFs E0 M model A LB FF LK cr sp G.HDECL W W 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS G.TAGS K PMSA.fp_ok DEF0 XI R r EV Hra Hraok [RET_PC] FPM) with (i := idx_of txt).
  - rewrite LS. exact (G.plans lems).
  - exact G.tags_ok.
  - exact heap_ok.
  - exact pure_ok.
  - rewrite LS. intros pc [<-|[]]. exact ret_pc_ok.
  - (* [comment removed for export] *)
    intros i c1 k ps j sb IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaves_ok _ _ _ _ _ IL) as X. discriminate X.
  - (* [comment removed for export] *)
    intros i c1 k ps pc IL Hex. pose proof (CH2.leaves_all_sound _ _ _ leaves_ok _ _ _ _ _ IL) as X. unfold lchk in X.
    cbn [existsb] in Hex. rewrite orb_false_r in Hex. rewrite Hex in X.
    apply existsb_exists in X as ([[[j i'] k'] pc'] & _ & X). do 7 (apply andb_prop in X as [X ?Y]).
    apply Nat.eqb_eq in X. apply Nat.eqb_eq in Y5. apply Z.eqb_eq in Y4. apply Bool.eqb_prop in Y3. apply Nat.leb_le in Y1. apply Z.eqb_eq in Y0. subst i' k' pc'.
    destruct IL as (tags & Hc1 & Htags & Hps & Htag).
    destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate Y].
    assert (XL : CVFA.xi_leafA NFs E0 XI i j c1) by (intros Ea Eb Ec Aa Ab Ma Mb ma mb HXa _ _ _ _; unfold XI in *; rewrite <- Y3; exact HXa).
    destruct (existsb (Z.eqb pc) INL) eqn:HI'.
    + pose proof (inl_sites pc HI') as Hst. rewrite <- LS, <- Y0 in Hst.
      exact (CVFA.inl_leaf_okA L ar C HI HIok LYI LYR LYB LYN NFs E0 M model A LB FF LK cr sp G.HDECL W W 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
               G.CPS K PMSA.fp_ok XI (fun _ x => x) FPM i c1 ps j cj 4 [] Hcj Y Y2 Y1 XL Hst).
    + apply andb_prop in Y as [Yx Y]. apply Z.eqb_eq in Yx.
      assert (XC : CVFA.xi_callA L ar NFs E0 LB FF sp G.HDECL XI i j c1 0) by (intros Ea Eb Ec Aa Ab Ma Mb Mc ma mb csp HXa _ _ _ _ _ _ _ _; unfold XI in *; rewrite <- Y3; exact HXa).
      refine (CVFA.call_leaf_okA L ar C HI HIok LYI LYR NFs E0 M model A LB FF LK cr sp G.HDECL W W 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
               G.CPS K PMSA.fp_ok DEF0 S6 [] GLO GHI SC_OK GOT_OK XI HKnil i c1 ps j cj 0 None Hcj Y (Z.le_refl 0) XC _).
      rewrite Y0, Yx. exact (Leaf_extendsftf2_xboth.ok L ar C HI HIok LAY).
  - (* [comment removed for export] *)
    intros i c1 k ps pc IL Hinr fx' E R1 A1 M1 m1 E' R' M2 m2 HAt1 HAX HFP1 Hag HLF model2 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HagE' HA'.
    pose proof HAX as [HA1 HX]. destruct Hinr as [<-|[]].
    pose proof (CH2.leaves_all_sound _ _ _ exits_ok _ _ _ _ _ IL) as X. unfold xchk in X. rewrite Z.eqb_refl in X.
    pose proof (CBA.amb_off L ar C HI HIok LYB NFs E0 M model A LB FF LK sp G.HDECL W (CPA.NOB G.CPS) (CPA.NOF G.CPS) (CPA.Cred0 cr) 0 i E A1 M2 m2 HA') as Hoff.
    destruct IL as (tags & Hc1 & Htags & Hps & Htag).
    assert (Hnx : (NFs <= CC.cp_nx c1)%nat) by exact (G.NF_le i c1 Hc1).
    assert (U10' : bv_unsigned (ev E' 10) = F) by (rewrite <- (proj1 HagE' 10%nat) by (unfold NFs; lia); exact U10).
    assert (U32' : bv_unsigned (ev E' 32) = s).
    { pose proof (proj1 HagE' 32%nat ltac:(unfold NFs; lia)) as Z32. rewrite <- Z32. exact U32. }
    assert (Hrp : L5.u64_at (hl_segs L) M2 (F + 8) (s + N)).
    { apply (CL5A.u64_full (hl_segs L) _ Hoff).
      apply (CL5.kword64_elim (hl_segs L) E' _ _ _ (F + 8) _ (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ (has_In _ _ X))).
      - rewrite (DOS.estart_reg E' 10 8 F U10'). lia.
      - unfold XI in HX.
        assert (HN : (if Nat.odd i then 4 else 3) = N).
        { destruct (Nat.odd i); symmetry in HX; [apply Nat.eqb_eq in HX | apply Nat.eqb_neq in HX]; unfold N in *; destruct HNv as [E3|E4]; lia. }
        rewrite HN. cbn [edenot]. rewrite u_add64. rewrite U32'. rewrite !u64_of_Z by lia. apply Z.mod_small. lia. }
    rewrite SCRV in HP.
    apply (Hcont fx' R' M2 model2 LB cr LB [(F + 8, 8); (PDC.a_TP AD - 164, 4)] LK1 A1 HFP1); [| exact HRP | | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    + split; [unfold PDCA.fs_postA; fold N; exact Hrp|]. repeat split; reflexivity.
    + cbn [PDC.a_TP AD PDCA.xboth]. rewrite <- TP. exact HP.
  - exact Hc0.
  - (* [comment removed for export] *)
    split.
    + apply DOK.regs_ok_tmpl. intros n Hn.
      assert (Rg : CC.cp_regs c0 = [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; ELit 1; ELit 1; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17;
                                    EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31])
        by (unfold c0; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; reflexivity).
      rewrite Rg.
      pose proof (DOK.rz_word R 11 _ R11) as W11. pose proof (DOK.rz_word R 12 _ R12) as W12.
      do 32 (destruct n as [|n]; [first [reflexivity | lia | (symmetry; first [exact W11 | exact W12])]|]). lia.
    + change (CCA.vis A model M) with Mv.
      assert (ES2 : forall o, estart E0 (SA (EVar 2) o) = sp + o) by (intros o; apply (DOS.estart_reg E0 2 o sp U2)).
      assert (ES10 : forall o, estart E0 (SA (EVar 10) o) = F + o) by (intros o; apply (DOS.estart_reg E0 10 o F U10)).
      assert (ES32 : forall o, estart E0 (SA (EVar 32) o) = s + o) by (intros o; apply (DOS.estart_reg E0 32 o s U32)).
      assert (EL : forall z, 0 <= z < 2 ^ 64 -> elenZ E0 (ELit z) = z) by (intros z Hz; apply DOS.elen_lit; exact Hz).
      assert (BYTE : forall i b, 0 <= i <= N -> nth (Z.to_nat i) (txt ++ [0]) 0 = b -> kentry_ok (hl_segs L) E0 Mv (KWord (SA (EVar 32) i) 1 (ELit b))).
      { intros i b Hi Hb.
        assert (Hm : L5.u8_at (hl_segs L) M (s + i) b /\ 0 <= b < 256).
        { subst b. destruct (Z.eq_dec i N) as [->|Hne].
          - rewrite app_nth2 by (unfold N; lia). replace (Z.to_nat N - length txt)%nat with 0%nat by (unfold N; lia). cbn [nth]. split; [exact Tn | lia].
          - assert (Hi' : (Z.to_nat i < length txt)%nat) by (unfold N in *; lia).
            rewrite app_nth1 by exact Hi'. split.
            + pose proof (Tb (Z.to_nat i) Hi') as B. rewrite Z2Nat.id in B by lia. exact B.
            + rewrite Forall_forall in Tr. apply Tr. apply nth_In. exact Hi'. }
        destruct Hm as [Hm Hbr].
        apply (CL5A.kword8_intro (hl_segs L) E0 Mv _ _ (s + i) b); [rewrite ES32; reflexivity | lia | lia | cbn [edenot]; reflexivity | lia |].
        exact (CL5A.u8_vis (hl_segs L) H M (s + i) b ltac:(lia) ltac:(lia) (CL5A.visr_sub _ s (N + 1) (s + i) 1 VT ltac:(lia) ltac:(lia)) Hm). }
      assert (COMMON : forall n1 tail, n1 = N + 1 -> know_ok (hl_segs L) E0 Mv tail ->
                know_ok (hl_segs L) E0 Mv
                  ([KRange (EVar 2) 140735332491744 140737488355328; KAlign (EVar 2) 16; KImg 65536 1466368; KWr (SA (EVar 2) (-8672)) (ELit 8672); KUnk (SA (EVar 2) (-8672)) (ELit 8672);
                    KWr (SA (EVar 10) 8) (ELit 8); KRange (EVar 10) 140735332483072 140737488355072; KDisj (SA (EVar 10) 8) (ELit 192) (SA (EVar 2) (-8672)) (ELit 8672);
                    KRange (EVar 32) 4096 140737488355328; KWord (SA (EVar 10) 8) 8 (EVar 32); KWord (SA (EVar 10) 184) 8 (ELit 18446744073709551615);
                    KWord (SA (EVar 10) 192) 8 (ELit 0); KWord (SA (ELit 0) 7084240) 8 (EVar 33);
                    KDisj (SA (EVar 32) 0) (ELit n1) (SA (EVar 2) (-8672)) (ELit 8672); KDisj (SA (EVar 32) 0) (ELit n1) (SA (EVar 10) 8) (ELit 192)] ++ tail)).
      { intros n1 tail Hn1 Htail. subst n1. unfold PDC.apart in *. unfold know_ok. cbn [app].
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; lia|].
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; split; [lia | exact S1]|].
        apply Forall_cons; [cbn [kentry_ok]; split; [lia | split; [lia |]]; intros a Ha; unfold Mv, CCA.vis, mrestrict; destruct (ahid A model (Z_to_bv 64 a)); [reflexivity | exact (Himg a Ha)]|].
        apply Forall_cons; [apply (CL5.kwr_intro (hl_segs L) E0 Mv _ _ (sp - 8672) 8672); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | exact DS]|].
        apply Forall_cons; [apply (CL5.kunk_intro (hl_segs L) E0 Mv _ _ (sp - 8672) 8672); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | exact DS]|].
        apply Forall_cons; [apply (CL5.kwr_intro (hl_segs L) E0 Mv _ _ (F + 8) 8); [rewrite ES10; lia | apply EL; lia | lia | lia | lia | exact DF8]|].
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U10; lia|].
        apply Forall_cons; [cbn [kentry_ok]; rewrite ES10, ES2, !EL by lia; lia|].
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U32; lia|].
        apply Forall_cons; [apply (CL5.kword64_intro (hl_segs L) E0 Mv _ _ (F + 8) s); [rewrite ES10; lia | lia | lia | reflexivity | apply (CL5A.u64_vis _ H M); [lia | lia | apply (CL5A.visr_sub _ (F + 8) 192 (F + 8) 8 VF); lia | exact Hf8]]|].
        apply Forall_cons; [apply (CL5.kword64_intro (hl_segs L) E0 Mv _ _ (F + 184) (2 ^ 64 - 1)); [rewrite ES10; lia | lia | lia | reflexivity | apply (CL5A.u64_vis _ H M); [lia | lia | apply (CL5A.visr_sub _ (F + 8) 192 (F + 184) 8 VF); lia | exact Hf184]]|].
        apply Forall_cons; [apply (CL5.kword64_intro (hl_segs L) E0 Mv _ _ (F + 192) 0); [rewrite ES10; lia | lia | lia | reflexivity | apply (CL5A.u64_vis _ H M); [lia | lia | apply (CL5A.visr_sub _ (F + 8) 192 (F + 192) 8 VF); lia | exact Hf192]]|].
        apply Forall_cons; [apply (CL5.kword64_intro (hl_segs L) E0 Mv _ _ 7084240 CAN); [rewrite DOS.estart_lit by lia; lia | lia | lia | reflexivity | apply (CL5A.u64_vis _ H M); [lia | lia | exact VG | exact Hguard]]|].
        apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES2, !EL by lia; lia|].
        apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES10, !EL by lia; lia|].
        exact Htail. }
      unfold c0. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [idx_of nth];
        (match goal with |- know_ok _ _ _ (CC.cp_know ?c) => let k := eval vm_compute in (CC.cp_know c) in change (CC.cp_know c) with k end);
        (match goal with |- know_ok _ _ _ (?a1 :: ?a2 :: ?a3 :: ?a4 :: ?a5 :: ?a6 :: ?a7 :: ?a8 :: ?a9 :: ?a10 :: ?a11 :: ?a12 :: ?a13 :: ?a14 :: ?a15 :: ?t) =>
           change (know_ok (hl_segs L) E0 Mv ([a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13; a14; a15] ++ t)) end);
        (eapply COMMON; [unfold N; reflexivity|]); unfold know_ok;
        repeat (apply Forall_cons; [apply BYTE; [unfold N; cbn; lia | reflexivity] |]); apply Forall_nil.
  - unfold XI. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; reflexivity.
  - exact HH.
  - exact Hmo.
  - exact Hroom.
  - exact Hfp.
Qed.
End Final.
End FSIA.
