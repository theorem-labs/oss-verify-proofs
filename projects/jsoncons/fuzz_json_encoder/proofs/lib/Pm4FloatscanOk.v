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
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto HeapIface HeapIfaceA L5Defs L5Core L5LazyA
  Pm4PlanKit Pm4L5DefsA FrmInv Pm4FrmInv PmHeapIfaceA PmLibDefsA PmLibSpecsA CutVFXM DecIface DecJson DecScanPure DecOkDefsM DecOkSemM DecOkSemA DecIfaceA StrtodPure StrtodIface FloatLazyA
  FsHeadLazyA Pm4DecfloatPre Pm4DecfloatAt Pm4DecfloatOk.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutVF.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD CutCertA CutHeapA CutL5A CutBridgeA CutPureA CutVFA Pm4CutKitD DecAssume.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_fshead_xasan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FSOA.
Definition AD : PDC.addrs := PDCA.xasan.
Definition ENTRY : Z := 0x14d930.
Definition HEXPC : Z := 0x14db10.
Definition lchk (q : Z) (i0 : nat) := FHLA.leaf_chk (PDC.a_G AD) (PDC.a_E1 AD) (PDC.a_E2 AD) HEXPC q i0.
Lemma leaves0_ok : CH2.leaves_all CPS TAGS (lchk 0 0%nat) = true. Proof. vm_compute. reflexivity. Qed.
Lemma leaves1_ok : CH2.leaves_all CPS TAGS (lchk 1 1%nat) = true. Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA FHLA.NFh HDECL (CPA.NOB CPS) (CPA.NOF CPS) CPS TAGS = true. Proof. vm_compute. reflexivity. Qed.
Lemma foot_ok : CC.cps_all CPS (fun _ c => CHA.foot_chk FHLA.NFh HDECL c [] []) = true. Proof. vm_compute. reflexivity. Qed.
Lemma tags_ok34 : CC.tags_chk CPS TAGS FHLA.NFh = true. Proof. vm_compute. reflexivity. Qed.
Lemma hd_ok : CH.hd_scr HDECL = 8672 /\ CH.hd_wrs HDECL = [(EVar 10, 8, ELit 8)] /\ CH.hd_img HDECL = [(PDC.a_img_lo AD, PDC.a_img_hi AD)]. Proof. repeat split; reflexivity. Qed.
Lemma lems : LEMS_OK. Proof. unfold LEMS_OK, CXD.LEMS_OK, LEMS. apply Forall_nil. Qed.
Lemma cp_ok : nth_error CPS 0 = Some cp0 /\ nth_error CPS 1 = Some cp1 /\ CC.cp_pc cp0 = ENTRY /\ CC.cp_pc cp1 = ENTRY. Proof. repeat split; reflexivity. Qed.

Definition ghost (s CAN va vb : Z) (n : nat) : word :=
  match n with 32 => Z_to_bv 64 s | 33 => Z_to_bv 64 CAN | 34 => Z_to_bv 64 va | 35 => Z_to_bv 64 vb | _ => Z_to_bv 64 0 end%nat.
Definition mkE (R : bvmap 5 word) (s CAN va vb : Z) : env := Env (reg_ev R (ghost s CAN va vb)) (fun _ => []).
Lemma not45 : forall c (r : list Z), c <> 45 -> match c :: r with 45 :: _ => 1 | _ => 0 end = 0.
Proof. intros c r H. destruct c as [|p|p]; try reflexivity. do 6 (destruct p as [p|p|]; try reflexivity). exfalso; apply H; reflexivity. Qed.

Section Final.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout. Variable ar : asan_run. Variable C : asan_statics_cells. Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FL : PDCA.float_layoutA L AD.

Theorem floatscan_okA : PDCA.floatscan_contractA L ar HI PMSA.fp_ok AD ENTRY.
Proof.
  intros r sp F s CAN txt LB FF LK cr A fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs Hpre Hcont.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (FPM : forall (fx fx' : FPState) R0 pc M0 R' pc' M', msteps (hl_segs L) (@mkst fx R0 (Z_to_bv 64 pc) M0 (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx').
  { rewrite LS. intros fx0 fx' R0 pc M0 R' pc' M' H Hf. exact (Pm4FrmInv.msteps_fp_ok fx0 fx' R0 _ M0 _ R' _ M' _ H Hf). }
  assert (IMGR : hl_img_lo L <= PDC.a_img_lo AD /\ PDC.a_img_hi AD <= hl_img_hi L /\ forall a, PDC.a_img_lo AD <= a < PDC.a_img_hi AD -> ~ hl_rt_static L a).
  { cbn [PDC.a_img_lo PDC.a_img_hi AD PDCA.xasan]. rewrite ILO, IHI. split; [lia|]. split; [lia|]. intros a Ha Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). lia. }
  assert (ERRW : forall M0 : PDCA.mem, L5.writable (hl_segs L) M0 (PDC.a_TP AD - 164) 4) by (rewrite LS; intros M0; exact (DFAA.errno_writable M0)).
  pose proof Hpre as (RF & R11 & R12 & Hfile & HspF & Hfd8 & Hguard & RCAN & Htext & Hblk & Hapf & Hnumf & Himg).
  pose proof Hfile as (Hf8 & Hf184 & Hf192 & Hfw & HF1 & HF2). pose proof Htext as (Tb & Tn & TQ1 & TQ2 & TQ3 & Td & Tr).
  cbn [PDC.a_G PDC.a_TP PDC.a_img_lo PDC.a_img_hi AD PDCA.xasan] in Hguard, Himg.
  pose proof (PDJ.json_full txt Hnumf) as Hfull. cbv zeta in Hfull. change (PDJ.len txt) with (Z.of_nat (length txt)) in Hfull.
  destruct (PSP.final_after0 txt Hnumf) as [A0 A1].
  set (N := Z.of_nat (length txt)) in *. assert (HN0 : 0 <= N) by (unfold N; lia).
  pose proof (FLA.rng L ar C HI HIok _ _ _ _ _ _ _ HH) as RFx. destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  pose proof Hstk as (S1 & S2 & S3 & S4 & S5 & S6). unfold PSI.WIN, PDC.STK_FLOOR in *.
  destruct (FLA.txt_facts_h L ar C HI HIok LYI _ _ _ _ _ _ _ sp s (N + 1) HH ltac:(lia) Hblk ltac:(lia)) as (TB1 & TB2 & TB3 & TB4 & TB5).
  assert (TBS : FHLA.hideP (s + (N + 1) <= sp - 8672 \/ sp <= s)) by (unfold FHLA.hideP; lia). clear TB2.
  assert (TAF : FHLA.hideP (s + (N + 1) <= F + 8 \/ F + 8 + 192 <= s)) by (unfold FHLA.hideP, PDC.apart in *; lia). clear Hapf.
  assert (Usp : bv_unsigned (getr R 2%bv) = sp) by (rewrite Hsp; apply u64_of_Z; lia).
  set (H := ahid A model). set (Mv := CCA.vis A model M).
  assert (VS : CL5A.visr H (sp - 8672) 8672) by (apply (FLA.stk_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH); lia).
  assert (VF : CL5A.visr H (F + 8) 192) by (apply (FLA.stk_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH); lia).
  assert (VT : CL5A.visr H s (N + 1)) by (exact (FLA.txt_visr_h L ar C HI HIok LYI _ _ _ _ _ _ _ sp _ _ HH ltac:(lia) Hblk)).
  assert (VG : CL5A.visr H 7069712 8) by (intros i Hi; apply (CHA.img_vis L ar C HI HIok LYI 48%nat sp ltac:(lia) _ _ _ _ _ _ _ (7069712 + i) HH); rewrite IHI; lia).
  assert (DS : L5.defined Mv (sp - 8672) 8672) by (exact (CL5A.defined_vis H M _ _ VS S5)).
  assert (DT : L5.defined Mv s (N + 1)) by (exact (CL5A.defined_vis H M _ _ VT Td)).
  assert (DF8 : L5.defined Mv (F + 8) 8) by (apply (CL5A.defined_vis H M); [apply (CL5A.visr_sub _ (F + 8) 192 (F + 8) 8 VF); lia | exact Hfd8]).
  (* [comment removed for export] *)
  assert (COMMON : forall va vb nb tail, 2 <= nb <= 3 -> nb <= N + 1 ->
            let E0 := mkE R s CAN va vb in know_ok (hl_segs L) E0 Mv tail ->
            know_ok (hl_segs L) E0 Mv
              ([KRange (EVar 2) 140735332491744 140737488355328; KAlign (EVar 2) 16; KImg 65536 1449984; KWr (SA (EVar 2) (-8672)) (ELit 8672); KUnk (SA (EVar 2) (-8672)) (ELit 8672);
                KWr (SA (EVar 10) 8) (ELit 8); KRange (EVar 10) 140735332483072 140737488355072; KDisj (SA (EVar 10) 8) (ELit 192) (SA (EVar 2) (-8672)) (ELit 8672);
                KRange (EVar 32) 4096 140737488355328; KWord (SA (EVar 10) 8) 8 (EVar 32); KWord (SA (EVar 10) 184) 8 (ELit 18446744073709551615);
                KWord (SA (EVar 10) 192) 8 (ELit 0); KWord (SA (ELit 0) 7069712) 8 (EVar 33);
                KDisj (SA (EVar 32) 0) (ELit nb) (SA (EVar 2) (-8672)) (ELit 8672); KDisj (SA (EVar 32) 0) (ELit nb) (SA (EVar 10) 8) (ELit 192)] ++ tail)).
  { intros va vb nb tail Hnb HnbN E0 Htail. unfold PDC.apart in *.
    assert (U2 : bv_unsigned (ev E0 2) = sp) by exact Usp.
    assert (U10 : bv_unsigned (ev E0 10) = F) by exact RF.
    assert (U32 : bv_unsigned (ev E0 32) = s) by (change (ev E0 32) with (Z_to_bv 64 s); apply u64_of_Z; lia).
    assert (ES2 : forall o, estart E0 (SA (EVar 2) o) = sp + o) by (intros o; apply (DOS.estart_reg E0 2 o sp U2)).
    assert (ES10 : forall o, estart E0 (SA (EVar 10) o) = F + o) by (intros o; apply (DOS.estart_reg E0 10 o F U10)).
    assert (ES32 : forall o, estart E0 (SA (EVar 32) o) = s + o) by (intros o; apply (DOS.estart_reg E0 32 o s U32)).
    assert (EL : forall z, 0 <= z < 2 ^ 64 -> elenZ E0 (ELit z) = z) by (intros z Hz; apply DOS.elen_lit; exact Hz).
    unfold know_ok. cbn [app].
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
    apply Forall_cons; [apply (CL5.kword64_intro (hl_segs L) E0 Mv _ _ 7069712 CAN); [rewrite DOS.estart_lit by lia; lia | lia | lia | reflexivity | apply (CL5A.u64_vis _ H M); [lia | lia | exact VG | exact Hguard]]|].
    apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES2, !EL by lia; unfold FHLA.hideP in TBS; lia|].
    apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES10, !EL by lia; unfold FHLA.hideP in TAF; lia|].
    exact Htail. }
  assert (REGS : forall va vb regs, regs = CC.cp_regs cp0 -> regs_ok (mkE R s CAN va vb) regs R).
  { intros va vb regs ->. apply DOK.regs_ok_tmpl. intros n Hn.
    pose proof (DOK.rz_word R 11 _ R11) as W11. pose proof (DOK.rz_word R 12 _ R12) as W12.
    do 32 (destruct n as [|n]; [first [lia | reflexivity | (symmetry; first [exact W11 | exact W12])]|]); lia. }
  assert (BYTE : forall i, 0 <= i <= N -> L5.u8_at (hl_segs L) Mv (s + i) (nth (Z.to_nat i) (txt ++ [0]) 0) /\ 0 <= nth (Z.to_nat i) (txt ++ [0]) 0 < 256).
  { intros i Hi.
    assert (Hm : L5.u8_at (hl_segs L) M (s + i) (nth (Z.to_nat i) (txt ++ [0]) 0) /\ 0 <= nth (Z.to_nat i) (txt ++ [0]) 0 < 256).
    { destruct (Z.eq_dec i N) as [->|Hne].
      - rewrite app_nth2 by (unfold N; lia). replace (Z.to_nat N - length txt)%nat with 0%nat by (unfold N; lia). cbn [nth]. split; [exact Tn | lia].
      - assert (Hlt : (Z.to_nat i < length txt)%nat) by (unfold N in *; lia). rewrite app_nth1 by exact Hlt. split.
        + pose proof (Tb (Z.to_nat i) Hlt) as B. rewrite Z2Nat.id in B by lia. exact B.
        + rewrite Forall_forall in Tr. apply Tr. apply nth_In. exact Hlt. }
    destruct Hm as [Hm Rm]. split; [|exact Rm]. apply (CL5A.u8_vis (hl_segs L) H M); [lia | lia | apply (CL5A.visr_sub _ s (N + 1) (s + i) 1 VT); lia | exact Hm]. }
  assert (KB : forall va vb o cv v, 0 <= o <= N -> bv_unsigned (ev (mkE R s CAN va vb) cv) = v -> v = nth (Z.to_nat o) (txt ++ [0]) 0 ->
            kentry_ok (hl_segs L) (mkE R s CAN va vb) Mv (KWord (SA (EVar 32) o) 1 (EVar cv))).
  { intros va vb o cv v Ho Hv ->. destruct (BYTE o Ho) as [B1 B2].
    apply (DOK.kword8_intro (hl_segs L) (mkE R s CAN va vb) Mv (SA (EVar 32) o) (EVar cv) (s + o) (nth (Z.to_nat o) (txt ++ [0]) 0)); [| lia | lia | exact Hv | exact B2 | exact B1].
    apply (DOS.estart_reg (mkE R s CAN va vb) 32 o s). change (ev (mkE R s CAN va vb) 32) with (Z_to_bv 64 s). apply u64_of_Z. lia. }
  destruct cp_ok as (Hc0 & Hc1 & Hp0 & Hp1). destruct hd_ok as (HD1 & HD2 & HD3).
  assert (RUN : forall (i0 : nat) (q : Z) c0 va vb, (q = 0 \/ q = 1) -> nth_error CPS i0 = Some c0 -> CC.cp_pc c0 = ENTRY -> CH2.leaves_all CPS TAGS (lchk q i0) = true ->
            q < N -> q + PD.dec_len (skipn (Z.to_nat q) txt) = N -> (nth (Z.to_nat q) (txt ++ [0]) 0 = 48 -> PSP.after0_ok (nth (Z.to_nat (q + 1)) (txt ++ [0]) 0)) ->
            CCA.AtV (hl_segs L) c0 (mkE R s CAN va vb) R A M model ->
            srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 ENTRY) M (seg_rom (hl_segs L))) model) K).
  { intros i0 q c0 va vb Hq Hci Hpc HL HqN Hfull' Haft HAt. rewrite <- Hpc.
    refine (FHLA.head_runA L ar C HI HIok LYI LYR LYB LYN PMSA.fp_ok FPM AD CPS TAGS HDECL HEXPC _ tags_ok34 heap_ok foot_ok HD1 HD2
              (DFTA.decfloat_okA L ar C HI HIok LAY FL) IMGR FL ERRW i0 q c0 LB FF LK cr A fx R M model K r sp F s CAN txt (mkE R s CAN va vb)
              Hq Hci HL HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs Hpre HqN Hfull' Haft _ _ _ HAt _).
    5:{ intros fx' R' M' model' LK' A' HFP' HPo HRP HP Hrt HA' Hmo' HLK HH'.
        exact (Hcont fx' R' M' model' LB cr LB (PDCA.DW AD F) LK' A' HFP' (conj HPo (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))) HRP HP Hrt HA' Hmo' HLK HH'). }
    - rewrite LS. exact (plans lems).
    - intros x. apply CL5.ev_reg.
    - change (ev (mkE R s CAN va vb) 32) with (Z_to_bv 64 s). apply u64_of_Z. lia.
    - reflexivity. }
  destruct (PSP.final_shape txt Hnumf) as [(c0 & rr & Et & Hd) | (c1 & rr & Et & Hd)].
  - (* [comment removed for export] *)
    assert (Hc45 : c0 <> 45) by (intros ->; discriminate Hd).
    assert (HN1 : 1 <= N) by (unfold N; rewrite Et; cbn [length]; lia).
    assert (Hfull0 : 0 + PD.dec_len (skipn (Z.to_nat 0) txt) = N).
    { clear - Hfull Et Hc45. rewrite Et in Hfull |- *. destruct c0 as [|p|p]; try exact Hfull. do 6 (destruct p as [p|p|]; try exact Hfull). exfalso; apply Hc45; reflexivity. }
    assert (Rc0 : 48 <= c0 <= 57) by (unfold PD.is_dig in Hd; apply andb_prop in Hd as [D1 D2]; apply Z.leb_le in D1, D2; lia).
    set (c1 := nth 1 (txt ++ [0]) 0). destruct (BYTE 1 ltac:(lia)) as [_ Rc1]. change (Z.to_nat 1) with 1%nat in Rc1. fold c1 in Rc1.
    apply (RUN 0%nat 0 cp0 c0 c1 (or_introl eq_refl) Hc0 Hp0 leaves0_ok ltac:(lia) Hfull0).
    + intros H48. apply (A0 rr). change (Z.to_nat 0) with 0%nat in H48. rewrite Et in H48. cbn [app nth] in H48. rewrite Et, H48. reflexivity.
    + split; [apply (REGS c0 c1); reflexivity|]. (let k := eval vm_compute in (CC.cp_know cp0) in change (CC.cp_know cp0) with k).
      apply (COMMON c0 c1 2 [KWord (SA (EVar 32) 0) 1 (EVar 34); KRange (EVar 34) 48 57; KWord (SA (EVar 32) 1) 1 (EVar 35); KRange (EVar 35) 0 255] ltac:(lia) ltac:(lia)).
      assert (V34 : bv_unsigned (ev (mkE R s CAN c0 c1) 34) = c0) by (change (ev (mkE R s CAN c0 c1) 34) with (Z_to_bv 64 c0); apply u64_of_Z; lia).
      assert (V35 : bv_unsigned (ev (mkE R s CAN c0 c1) 35) = c1) by (change (ev (mkE R s CAN c0 c1) 35) with (Z_to_bv 64 c1); apply u64_of_Z; lia).
      apply Forall_cons; [apply (KB c0 c1 0 34%nat c0 ltac:(lia) V34); rewrite Et; reflexivity|].
      apply Forall_cons; [cbn [kentry_ok]; change (edenot ?e (EVar 34)) with (ev e 34); rewrite V34; lia|].
      apply Forall_cons; [apply (KB c0 c1 1 35%nat c1 ltac:(lia) V35); reflexivity|].
      apply Forall_cons; [cbn [kentry_ok]; change (edenot ?e (EVar 35)) with (ev e 35); rewrite V35; lia | constructor].
  - (* [comment removed for export] *)
    assert (HN2 : 2 <= N) by (unfold N; rewrite Et; cbn [length]; lia).
    assert (Hfull1 : 1 + PD.dec_len (skipn (Z.to_nat 1) txt) = N) by (clear - Hfull Et; rewrite Et in Hfull |- *; exact Hfull).
    assert (Rc1 : 48 <= c1 <= 57) by (unfold PD.is_dig in Hd; apply andb_prop in Hd as [D1 D2]; apply Z.leb_le in D1, D2; lia).
    set (c2 := nth 2 (txt ++ [0]) 0). destruct (BYTE 2 ltac:(lia)) as [_ Rc2]. change (Z.to_nat 2) with 2%nat in Rc2. fold c2 in Rc2.
    apply (RUN 1%nat 1 cp1 c1 c2 (or_intror eq_refl) Hc1 Hp1 leaves1_ok ltac:(lia) Hfull1).
    + intros H48. assert (E48 : c1 = 48) by (change (Z.to_nat 1) with 1%nat in H48; rewrite Et in H48; cbn [app nth] in H48; exact H48). subst c1. exact (A1 rr Et).
    + split; [apply (REGS c1 c2); reflexivity|]. (let k := eval vm_compute in (CC.cp_know cp1) in change (CC.cp_know cp1) with k).
      apply (COMMON c1 c2 3 [KWord (SA (EVar 32) 0) 1 (ELit 45); KWord (SA (EVar 32) 1) 1 (EVar 34); KRange (EVar 34) 48 57; KWord (SA (EVar 32) 2) 1 (EVar 35); KRange (EVar 35) 0 255] ltac:(lia) ltac:(lia)).
      assert (V34 : bv_unsigned (ev (mkE R s CAN c1 c2) 34) = c1) by (change (ev (mkE R s CAN c1 c2) 34) with (Z_to_bv 64 c1); apply u64_of_Z; lia).
      assert (V35 : bv_unsigned (ev (mkE R s CAN c1 c2) 35) = c2) by (change (ev (mkE R s CAN c1 c2) 35) with (Z_to_bv 64 c2); apply u64_of_Z; lia).
      apply Forall_cons.
      { destruct (BYTE 0 ltac:(lia)) as [B1 B2].
        apply (DOK.kword8_intro (hl_segs L) (mkE R s CAN c1 c2) Mv _ _ (s + 0) 45); [| lia | lia | reflexivity | lia |].
        - apply (DOS.estart_reg (mkE R s CAN c1 c2) 32 0 s). change (ev (mkE R s CAN c1 c2) 32) with (Z_to_bv 64 s). apply u64_of_Z. lia.
        - change (Z.to_nat 0) with 0%nat in B1. rewrite Et in B1. cbn [app nth] in B1. exact B1. }
      apply Forall_cons; [apply (KB c1 c2 1 34%nat c1 ltac:(lia) V34); rewrite Et; reflexivity|].
      apply Forall_cons; [cbn [kentry_ok]; change (edenot ?e (EVar 34)) with (ev e 34); rewrite V34; lia|].
      apply Forall_cons; [apply (KB c1 c2 2 35%nat c2 ltac:(lia) V35); reflexivity|].
      apply Forall_cons; [cbn [kentry_ok]; change (edenot ?e (EVar 35)) with (ev e 35); rewrite V35; lia | constructor].
Qed.
End Final.
End FSOA.
