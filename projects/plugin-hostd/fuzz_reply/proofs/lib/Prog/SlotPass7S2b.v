From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c
  RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps SlotHead
  SlotHeadP SlotRes KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotHeadQ RelayRunT RelayRunF HarnessGlue
  relay_event_b_c check_shape_event_c strnlen_c memcpy_c SlotPass7D SlotPass7RV SlotPass7R SlotPass7S SlotPass7T1
  SlotPass7T2 SlotPass7 SlotPass7S2.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayCap SlotEntry.
Import ListNotations.
Local Open Scope Z_scope.

Lemma s2_keep : forall rc B API K sp E F L A mem md L' A' mem' md' q k,
  rmid (rc := rc) B API K sp E F L A mem md L' A' mem' md' -> In (q, k) (blocks L A) -> 0 < k -> ~ F q ->
  In (q, k) (blocks L' A').
Proof.
  intros rc B API K sp E F L A mem md L' A' mem' md' q k (_ & _ & _ & _ & _ & PA & SV & _) Hin Hk NF.
  unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & EQ & Hp). cbn [fst snd] in EQ.
  injection EQ as <- <-.
  pose proof (SV p k' Hp Hk NF) as Hp'. pose proof (PA p k' Hp Hp' NF) as EA.
  rewrite <- EA. unfold blocks. exact (in_map (fun b => (ptr_addr L' (fst b), snd b)) _ (p, k') Hp').
Qed.

Lemma s2_mid : forall (b1 b2 : list (Z * Z)) x y, In y (b1 ++ x :: b2) -> y = x \/ In y (b1 ++ b2).
Proof.
  intros b1 b2 x y H. apply in_app_or in H. destruct H as [H|[H|H]].
  - right. apply in_or_app. left. exact H.
  - left. symmetry. exact H.
  - right. apply in_or_app. right. exact H.
Qed.

Lemma s2_mid_in : forall (b1 b2 : list (Z * Z)) x y, In y (b1 ++ b2) -> In y (b1 ++ x :: b2).
Proof.
  intros b1 b2 x y H. apply in_app_or in H. apply in_or_app.
  destruct H as [H|H]; [left; exact H|right; right; exact H].
Qed.

Lemma s2_nd_out : forall (b1 b2 : list (Z * Z)) q m d n, List.NoDup (map fst (b1 ++ (d, n) :: b2)) ->
  In (q, m) (b1 ++ b2) -> q <> d.
Proof.
  intros b1 b2 q m d n ND Hin ->. rewrite map_app in ND. cbn [map fst] in ND. apply NoDup_remove_2 in ND.
  apply ND. rewrite <- map_app. exact (in_map fst _ (d, m) Hin).
Qed.

Lemma s2_apart : forall q m res EL, 0 <= EL -> q <> res ->
  (forall i, 0 <= i < m -> ~ (res <= q + i < res + EL + 1)) -> 0 < m ->
  res + EL + 1 <= q \/ q + m <= res.
Proof.
  intros q m res EL HE NE D Hm.
  destruct (Z.le_gt_cases (res + EL + 1) q) as [X|X]; [left; exact X|].
  destruct (Z.le_gt_cases (q + m) res) as [Y|Y]; [right; exact Y|].
  exfalso. destruct (Z.le_gt_cases res q) as [Z1|Z1].
  - apply (D 0); lia.
  - apply (D (res - q)); lia.
Qed.

Ltac s2u := cbv beta delta [G_RELAY_LO G_LOCK_HI relay_event_c.G_LOCK Statement.G_LOCK G_CLIENT G_BROKEN G_DEAD
  G_EINTR G_OUTV relay_finish_b_c.G_LISTEN].

Ltac s2_reg PRES GR r :=
  etransitivity; [exact (PRES r ltac:(unfold callee_saved; lia))|]; rewrite GR.

Ltac s2_kunf := unfold OP7_K, RELAY_EVENT_K, RELAY_EVENT_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK,
  ALLOC_STACK in *.

Theorem op7_c2_holds : forall F RI, op7_c2_stmt F RI.
Proof.
  intros F RI B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es
    hj c HF MC HRE HC HP1.
  destruct (op7_frame B API LS SH SK ra empty rc fx j E CS HF) as (SEG & ERR & GPL & AX & BW & SPLO & SPHI & IMGL).
  pose proof HF as (FF & _ & PRE & _).
  assert (ETP : ms_tp B = 0x31290) by (unfold frame_facts in FF; tauto).
  assert (EOFF : ms_errno_off B = -164) by (unfold frame_facts in FF; tauto).
  assert (EMP : empty = 0x30fa0) by (unfold frame_facts in FF; tauto).
  pose proof FF as FFA. do 30 (destruct FFA as [_ FFA]). specialize (FFA rc fx').
  do 5 (destruct FFA as [_ FFA]). destruct FFA as (BSP & CTX & BLO & NDB & _).
  destruct PRE as (((_ & _ & _ & _ & _ & SPAL & _ & _ & _ & TP0 & _ & _ & _ & INP & _) & _ & _ & _) &
    _ & _ & _ & _ & _ & NT & _).
  destruct HC as (FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd &
    HOUT & HREL & Hes & Hcost & HRI).
  destruct HR as (NO0 & _).
  destruct HP1 as (L1 & A1 & R1 & m1 & md1 & K0 & M & EL & res & e & -> & HR1 & G18 & G118 & G119 & G123 & G110 &
    HK0 & HM0 & HKM & HKS & HEL & ELE & ELZ & BE1 & RM1 & INI1 & RO1 & NZ & AL16 & FRB & (b1 & b2 & BL1 & BL2) & RSEP &
    (bnd & RF1 & ROOM & POST)).
  destruct HR1 as ((Q2 & Q3 & Q4 & Q20) & Q21 & Q22 & Q24 & Q25 & Q26 & Q27).
  pose proof (aa_laws (API rc)) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof HDK as (DK1 & _).
  destruct HOUT as ((O & junko & HOC) & HCAP).
  pose proof HGL as (GL1 & GL2 & GL3 & GL4 & GL5 & GL6 & GL7 & GL8 & GL9 & GL10 & GL11 & GL12 & GL13 & GL14 &
    HCL & HBR & HGN & HDD & HEI & HGONE & HMX).
  unfold INPUT_MAX in Hn.
  assert (SB1 : YM05.alloc_ceiling + 65344 <= slot_sp E) by (unfold slot_sp, SLOT_FRAME; unfold SLOT_STACK in SPLO; lia).
  assert (SB2 : slot_sp E < 2 ^ 63) by (unfold slot_sp, SLOT_FRAME; lia).
  assert (SB3 : slot_sp E mod 16 = 0) by (unfold slot_sp, SLOT_FRAME; Z.div_mod_to_equations; lia).
  assert (HKK : YM05.alloc_ceiling <= slot_sp E - OP7_K) by (change OP7_K with 8384; lia).
  pose proof FRB as (FR1 & FR2 & FR3).
  assert (NIMG : forall a, res <= a < res + EL + 1 -> ~ in_img B a).
  { intros a Ha. replace a with (res + (a - res)) by lia. apply FR3. lia. }
  assert (O0 : O = []).
  { destruct HOC as [(_ & _ & _ & X)|(_ & _ & _ & _ & _ & X & _)]; [exact X|].
    rewrite NO0 in X. apply length_zero_iff_nil. lia. }
  subst O.
  assert (RNO : res <> bv_unsigned out).
  { destruct HOC as [(_ & X & _)|(_ & _ & IN & _)]; [rewrite X; exact NZ|].
    intros X. apply (proj1 (RSEP _ _ IN)). symmetry. exact X. }
  assert (INS : 0 <= ss_p E + K0 < 2 ^ 64 /\ (ss_p E + K0 + EL <= res \/ res + EL <= ss_p E + K0)).
  { destruct INP as [(HN00 & HP0) | (HN0 & q & Hq & Eq)].
    - rewrite HP0, EMP. split; lia.
    - destruct (DK1 q (ss_n E) Hq) as (_ & q' & Hq' & Eq').
      { rewrite Eq. exact (NT HN0). }
      assert (INB : In (ss_p E, ss_n E) (blocks L A)).
      { unfold blocks. apply in_map_iff. exists (q', ss_n E).
        split; [cbv beta; cbn [fst snd]; rewrite Eq', Eq; reflexivity|exact Hq']. }
      destruct (block_facts B (aa_MR (API rc)) LAWS L A mem md (ss_p E) (ss_n E) 0 HMR INB ltac:(lia))
        as (_ & PLO & PHI & _).
      split; [lia|].
      exact (op7_src_sep (ss_p E) (ss_n E) K0 EL res L A RSEP INB ltac:(lia) ltac:(lia)). }
  pose proof RM1 as (MR1 & WF1 & BD1 & _ & _ & PA1 & SV1 & _ & _ & _ & _ & _ & SC1).
  assert (KEQ : known_at L1 A1 (bv_unsigned out) = known_at L A (bv_unsigned out)).
  { apply op7_known_keep.
    - first [exact (NDB L A mem md HMR) | apply (proj2 (stdpp.base.NoDup_ListNoDup _)); exact (NDB L A mem md HMR)].
    - first [exact (NDB L1 A1 m1 md1 MR1)
      | apply (proj2 (stdpp.base.NoDup_ListNoDup _)); exact (NDB L1 A1 m1 md1 MR1)].
    - intros pk nk Hpk Hnk. exact (SV1 pk nk Hpk Hnk (fun X => X)).
    - intros pk nk Hpk Hpk1. exact (PA1 pk nk Hpk Hpk1 (fun X => X)).
    - destruct HOC as [(_ & XO & _)|(CPO & _ & INO & _)].
      + right. rewrite XO. split; intros mk Hmk.
        * pose proof (BLO L A mem md 0 mk HMR Hmk). lia.
        * pose proof (BLO L1 A1 m1 md1 0 mk MR1 Hmk). lia.
      + left. exists (bv_unsigned cap). split; [exact CPO|exact INO]. }
  destruct (mr_model _ _ LAWS _ _ _ _ MR1) as (Hh1 & Hl1 & _).
  assert (INR : In (res, EL + 1) (blocks L1 A1)) by (rewrite BL1; apply in_or_app; right; left; reflexivity).
  assert (PRS : forall i, 0 <= i < EL + 1 -> present m1 (res + i)).
  { intros i Hi. exact (proj1 (block_facts B (aa_MR (API rc)) LAWS L1 A1 m1 md1 res (EL + 1) i MR1 INR Hi)). }
  assert (RO1r : ro_agree rsegs m1) by (rewrite <- SEG; exact RO1).
  destruct (present_rw_cells rsegs m1 res (Z.to_nat EL) ltac:(lia) ltac:(lia)) as (junk & DJ1).
  { intros i Hi. apply PRS. lia. }
  destruct (present_rw_cells rsegs m1 (res + EL) 1%nat ltac:(lia) ltac:(lia)) as (jj & DJ2).
  { intros i Hi. replace (res + EL + i) with (res + (EL + i)) by lia. apply PRS. lia. }
  assert (LJJ : length jj = 1%nat) by (destruct DJ2 as [[[X _] _] _]; exact X).
  destruct jj as [|j1 [|j2 jj]]; [discriminate LJJ| |discriminate LJJ].
  assert (DSTn : rw_cells rsegs (normalize rsegs m1) res [CB (Z.to_nat EL) junk; CB 1 [j1]]).
  { apply rw_cells_normalize; [exact RO1r| |].
    - apply (hg_join rsegs m1 res (res + EL) [CB (Z.to_nat EL) junk] [CB 1 [j1]] DJ1 DJ2).
      cbn [cells_size csize]. lia.
    - intros i Hi. cbn [cells_size csize] in Hi. apply (ro_addr_out B SEG); [lia|]. apply NIMG. lia. }
  assert (BEn : bytes_at rsegs (normalize rsegs m1) (ss_p E + K0) e).
  { apply bytes_at_normalize; [exact RO1r|]. rewrite <- SEG. exact BE1. }
  assert (E8 : reg_get R1 8 = Z_to_bv 64 (ss_p E + K0)) by exact G18.
  assert (E10 : reg_get R1 10 = Z_to_bv 64 res) by exact G110.
  assert (E18 : reg_get R1 18 = Z_to_bv 64 M) by exact G118.
  assert (E19 : reg_get R1 19 = Z_to_bv 64 EL) by exact G119.
  assert (E23 : reg_get R1 23 = Z_to_bv 64 (ss_n E - K0)) by exact G123.
  rewrite SEG.
  eapply (kseg R1 (Z_to_bv 64 0x1408c) m1 md1); [exact wx_apart_rsegs|exact RO1r|exact Hh1|exact Hl1| | |].
  - unfold Regs6ss.mkR_of. rewrite E8, E10, E18, E19, E23.
    apply (op7_s2_run MC res (ss_p E + K0) M (ss_n E - K0) EL e junk j1);
      [lia|lia|lia|lia|lia|exact BEn|exact ELE|exact DSTn|lia|apply mem_inv_normalize].
  - intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m0 & -> & _).
    do 3 eexists. reflexivity.
  - intros Rm pc m0 regs1 m2 (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m0' & EQ & MU &
      WM & CEL) GR MREL ROS.
    injection EQ as ER EP EM. subst Rm pc m0.
    assert (H1y : YK11.getr regs1 1 = Z_to_bv 64 0x140b8) by (rewrite GR; reflexivity).
    assert (H2y : YK11.getr regs1 2 = Z_to_bv 64 (slot_sp E)) by (rewrite GR; exact Q2).
    assert (H4y : YK11.getr regs1 4 = YK11.getr (ss_regs E) 4) by (rewrite GR; exact Q4).
    assert (H10y : YK11.getr regs1 10 = Z_to_bv 64 res) by (rewrite GR; reflexivity).
    assert (H1r : getr regs1 1 = Z_to_bv 64 0x140b8) by exact H1y.
    assert (H2r : getr regs1 2 = Z_to_bv 64 (slot_sp E)) by exact H2y.
    assert (H10r : getr regs1 10 = Z_to_bv 64 res) by exact H10y.
    assert (SP1 : spZ regs1 = slot_sp E) by (unfold spZ; rewrite H2y; apply unsigned_lit; lia).
    assert (CEL2 : rw_cells rsegs m2 res [CB (Z.to_nat EL) e; C1 (Z_to_bv 8 0)])
      by exact (rw_cells_of_rel rsegs m2 m0' res _ MREL CEL).
    destruct (rmid_norm B (API rc) OP7_K (slot_sp E) (fun a => res <= a < res + EL + 1) (fun _ => False)
      L1 A1 m1 md1 m0' m2 [(res, res + EL + 1)] SEG RO1r MREL ROS MU WM MR1 WF1 BD1 HKK SC1) as (RM12 & _ & _).
    { intros x Hx HO. destruct (hg_not_out _ _ HO) as (lo & hi & [EQ|[]] & HX). injection EQ as <- <-.
      right. exact HX. }
    { intros a Ho. apply hg_out. intros lo hi [EQ|[]]. injection EQ as <- <-.
      destruct (Z.lt_ge_cases a res) as [X|X]; [left; exact X|].
      destruct (Z.lt_ge_cases a (res + EL + 1)) as [Y|Y]; [|right; exact Y].
      exfalso. destruct (block_facts B (aa_MR (API rc)) LAWS L1 A1 m1 md1 res (EL + 1) (a - res) MR1 INR
        ltac:(lia)) as (_ & _ & _ & NOW).
      apply NOW. replace (res + (a - res)) with a by lia. exact Ho. }
    { intros p n i Hp Hi HO. destruct (hg_not_out _ _ HO) as (lo & hi & [EQ|[]] & HX). injection EQ as <- <-.
      apply (present_of_writable_out B SEG); [lia|apply NIMG; lia|].
      eapply op7_cells_writable; [exact CEL2|]. cbn [cells_size csize]. lia. }
    pose proof RM12 as (MR12 & _).
    pose proof (rmid_seq B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM1 RM12) as RM02.
    assert (RO2 : ro_agree rsegs m2) by exact (ro_agree_same rsegs _ _ RO1r ROS).
    assert (TRG : forall a cs, rw_cells (ms_segs B) mem a cs ->
        (forall i, 0 <= i < Z.of_nat (cells_size cs) -> in_globals G_reply (a + i)) -> rw_cells (ms_segs B) m2 a cs).
    { intros a cs H D. eapply (rmid_rw_img B (API rc) AX); [exact IMGL|exact HKK|exact HMR|exact RM02|exact H|].
      intros i Hi. pose proof (GPL _ (D i Hi)) as P. split; [exact P|].
      intros [X|X]; [exact X|]. destruct P as (PI & _). exact (NIMG _ X PI). }
    assert (GB : forall a, 0x30fc0 <= a < 0x311c0 -> in_globals G_reply a) by (intros a Ha; apply in_G_bss; lia).
    pose proof (TRG _ _ GL12 ltac:(intros i Hi; cbn [cells_size csize] in Hi; apply GB; s2u; lia)) as CLK.
    pose proof (TRG _ _ GL4 ltac:(intros i Hi; cbn [cells_size csize] in Hi; apply GB; s2u; lia)) as CBR.
    pose proof (TRG _ _ GL6 ltac:(intros i Hi; cbn [cells_size csize] in Hi; apply GB; s2u; lia)) as CDD.
    pose proof (TRG _ _ GL7 ltac:(intros i Hi; cbn [cells_size csize] in Hi; apply GB; s2u; lia)) as CEI.
    pose proof (TRG _ _ GL11 ltac:(intros i Hi; cbn [cells_size csize] in Hi; apply GB; s2u; lia)) as COV.
    pose proof (TRG _ _ GL1 ltac:(intros i Hi; cbn [cells_size csize] in Hi; exists 0x20d38, 16;
      split; [left; reflexivity|s2u; lia])) as CLI0.
    destruct (hg_cut (ms_segs B) m2 _ [C4 (Z_to_bv 64 (-1))] [C4 (Z_to_bv 64 cl)] CLI0) as (_ & CLI).
    destruct (SlotEntry.entry_errno_cells B SEG ETP EOFF m2) as (ev & CEV). rewrite <- SEG in CEV.
    assert (GIMG : forall a, 0x30fc0 <= a < 0x311c0 -> in_img B a) by (intros a Ha; exact (proj1 (GPL a (GB a Ha)))).
    assert (EIMG : forall a, errno_addr B <= a < errno_addr B + 4 -> in_img B a)
      by (intros a Ha; exact (proj1 (SlotEntry.entry_errno_image B SEG ETP EOFF a Ha))).
    assert (BE2 : bytes_at (ms_segs B) m2 res (e ++ [Z_to_bv 8 0])).
    { rewrite SEG. pose proof CEL2 as [[_ X] _]. cbn [cells_bytes cbytes app] in X. exact X. }
    pose proof (Z.mod_pos_bound (- (res + EL + 1)) 8 ltac:(lia)) as R8.
    assert (BS : bytes_at (ms_segs B) m2 res
        (e ++ Z_to_bv 8 0 :: slack_at (ms_segs B) m2 (res + EL + 1) (Z.to_nat ((- (res + EL + 1)) mod 8)))).
    { apply bytes_split3; [exact BE2|]. rewrite ELE.
      apply slack_at_bytes; [lia|rewrite Z2Nat.id by lia; lia|].
      intros i Hi. rewrite Z2Nat.id in Hi by lia.
      apply (BSP L1 A1 m2 md1 res (EL + 1) _ MR12 INR).
      assert (E8' : forall N, 8 * ((N + 7) / 8) = N + (- N) mod 8) by (intros N; Z.div_mod_to_equations; lia).
      replace (res + (EL + 1)) with (res + EL + 1) by lia. rewrite E8'. lia. }
    assert (CPK : call_pre_k B (aa_MR (API rc)) RELAY_EVENT_K L1 A1 regs1 m2 md1).
    { eapply (cpk_of_rmid B (API rc)); [exact RM02|exact INI1| | | | | | | |].
      - rewrite H1y. apply ret_ok_even. vm_compute. reflexivity.
      - rewrite H4y. exact TP0.
      - rewrite SP1. exact SB3.
      - rewrite SP1. s2_kunf. lia.
      - rewrite SP1. lia.
      - s2_kunf. lia.
      - rewrite SP1. s2_kunf. lia.
      - rewrite SP1. exact SB2. }
    pose proof (HRE fx') as REC. unfold relay_event_contract in REC.
    specialize (REC L1 A1 regs1 m2 md1 bnd e
      (slack_at (ms_segs B) m2 (res + EL + 1) (Z.to_nat ((- (res + EL + 1)) mod 8))) [] junko cl br dd ei mx nout cap
      out ev).
    cbv zeta in REC.
    rewrite H10r, H2r in REC.
    rewrite (hg_unsigned res) in REC by lia.
    rewrite (hg_unsigned (slot_sp E)) in REC by lia.
    rewrite ELE, NO0 in REC.
    change (send_live cl br dd (EL + 1)) with (op7_live cl br dd EL) in REC.
    rewrite KEQ in REC.
    rewrite <- SEG.
    eapply SR_mono.
    { apply REC.
      - exact SEG.
      - exact CPK.
      - exact INI1.
      - unfold errno_addr, ERRNO_OFF. rewrite EOFF. reflexivity.
      - rewrite ERR. unfold G_LOCK_HI. lia.
      - rewrite SEG. exact RO2.
      - exact BS.
      - exact ELZ.
      - rewrite slack_at_len, Z2Nat.id by lia. lia.
      - s2u. destruct (Z.le_gt_cases (res + (EL + 1)) 0x30fc0) as [X|X]; [left; exact X|].
        destruct (Z.le_gt_cases 0x31040 res) as [Y|Y]; [right; exact Y|]. exfalso.
        destruct (Z.le_gt_cases res 0x30fc0) as [Z1|Z1];
          [apply (NIMG 0x30fc0); [lia|apply GIMG; lia]|apply (NIMG res); [lia|apply GIMG; lia]].
      - rewrite ERR. destruct (Z.le_gt_cases (res + (EL + 1)) 0x311ec) as [X|X]; [left; exact X|].
        destruct (Z.le_gt_cases (0x311ec + 4) res) as [Y|Y]; [right; exact Y|]. exfalso.
        destruct (Z.le_gt_cases res 0x311ec) as [Z1|Z1];
          [apply (NIMG 0x311ec); [lia|apply EIMG; rewrite ERR; lia]
          |apply (NIMG res); [lia|apply EIMG; rewrite ERR; lia]].
      - left. s2_kunf. lia.
      - intros a Ha. apply GPL, GB. revert Ha. s2u. lia.
      - intros a Ha. apply GPL. exists 0x20d38, 16. split; [left; reflexivity|revert Ha; s2u; lia].
      - exact EIMG.
      - exists res, (EL + 1). split; [exact INR|]. split; [exact FRB|]. split; [lia|]. split; [lia|]. exact RNO.
      - exact CLK.
      - exact HCL.
      - exact HBR.
      - exact HDD.
      - exact HEI.
      - exact CLI.
      - exact CBR.
      - exact CDD.
      - exact CEI.
      - exact COV.
      - exact CEV.
      - destruct HOC as [C0|(CP & NC & IN & FB & BY & LO & LJ)]; [left; rewrite NO0 in C0; exact C0|right].
        destruct (RSEP _ _ IN) as (NR & DJ).
        split; [exact CP|]. split; [lia|].
        split; [eapply s2_keep; [exact RM02|exact IN|exact CP|intros [X|X]; exact X]|].
        split; [exact FB|].
        split.
        { eapply (rmid_bytes_block B (API rc) BW); [exact RM02|exact IN|exact CP|intros [X|X]; exact X|exact BY|lia
            |cbn [app]; lia|].
          intros i Hi [X|X]; [exact X|]. cbn [app] in Hi. exact (DJ i ltac:(lia) X). }
        split; [reflexivity|]. split; [lia|].
        pose proof (s2_apart _ _ res EL ltac:(lia) NR DJ CP). lia.
      - lia.
      - exact RF1.
      - exact ROOM. }
    intros c' (L2 & A2 & R2 & m3 & md2 & OUT' & CAP' & junk' & -> & RP & INI2 & (qs & LEN2 & OK2 & LIVE2) & RO3 & BY3 &
      LCK3 & CLI3 & BRC3 & DDC3 & EIC3 & LVF & LVT).
    destruct (rp_split B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as (RM23 & PRES).
    rewrite SP1 in RM23.
    pose proof (rmid_seq B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM02 RM23) as RM03.
    assert (RM : rmid (rc := rc) B (API rc) OP7_K (slot_sp E)
        (op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL)
        (fun q => op7_live cl br dd EL = true /\ q = bv_unsigned out) L A mem md L2 A2 m3 md2).
    { apply (rmid_EF B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ RM03).
      - intros a [[X|X]|X]; [destruct X|left; exact X|right; exact X].
      - intros q [[X|X]|X]; [destruct X|destruct X|exact X]. }
    assert (INR2 : In (res, EL + 1) (blocks L2 A2)).
    { eapply s2_keep; [exact RM23|exact INR|lia|]. intros (_ & X). exact (RNO X). }
    assert (BLA : forall q m, In (q, m) (blocks L A) -> In (q, m) (blocks L1 A1)).
    { intros q m H. rewrite BL1. apply s2_mid_in. rewrite <- BL2. exact H. }
    assert (REGS : op7_regs1 E t R2 /\ getr R2 8 = Z_to_bv 64 (ss_p E + K0) /\
        getr R2 18 = Z_to_bv 64 (ss_p E + (K0 + M)) /\ getr R2 9 = Z_to_bv 64 res /\
        getr R2 23 = Z_to_bv 64 (ss_n E - (K0 + M))).
    { split.
      { unfold op7_regs1, base_regs. repeat split.
        - s2_reg PRES GR 2. exact Q2.
        - s2_reg PRES GR 3. exact Q3.
        - s2_reg PRES GR 4. exact Q4.
        - s2_reg PRES GR 20. exact Q20.
        - s2_reg PRES GR 21. exact Q21.
        - s2_reg PRES GR 22. exact Q22.
        - s2_reg PRES GR 24. exact Q24.
        - s2_reg PRES GR 25. exact Q25.
        - s2_reg PRES GR 26. exact Q26.
        - s2_reg PRES GR 27. exact Q27. }
      split; [s2_reg PRES GR 8; reflexivity|].
      split; [s2_reg PRES GR 18; replace (ss_p E + (K0 + M)) with (ss_p E + K0 + M) by lia; reflexivity|].
      split; [s2_reg PRES GR 9; reflexivity|].
      s2_reg PRES GR 23. replace (ss_n E - (K0 + M)) with (ss_n E - K0 - M) by lia. reflexivity. }
    destruct REGS as (RG1 & RG8 & RG18 & RG9 & RG23).
    pose proof (POST L2 A2 qs LEN2 OK2) as RT. unfold op7_S2 in RT.
    unfold op7_P2. cbv zeta.
    destruct (op7_live cl br dd EL) eqn:LV.
    + destruct (LVT eq_refl) as (CPB & CPE & FBO & (ev2 & CEV3) & NOUT & (bb1 & bb2 & c1 & c2 & BL3 & CE & BLC) &
        BYO & LJ' & COV3).
      pose proof FBO as (FO1 & FO2 & _).
      assert (UO : bv_unsigned (Z_to_bv 64 OUT') = OUT') by (apply hg_unsigned; lia).
      assert (UC : bv_unsigned (Z_to_bv 64 CAP') = CAP') by (apply hg_unsigned; lia).
      assert (UN : bv_unsigned (Z_to_bv 64 (0 + (EL + 1))) = EL + 1) by (rewrite hg_unsigned by lia; lia).
      assert (ND1 : List.NoDup (map fst (blocks L1 A1))).
      { first [exact (NDB L1 A1 m2 md1 MR12) | apply NoDup_ListNoDup; exact (NDB L1 A1 m2 md1 MR12)]. }
      assert (BL13 : forall q m, In (q, m) (c1 ++ c2) -> In (q, m) (blocks L1 A1) /\ q <> bv_unsigned out).
      { intros q m H. rewrite CE in H. destruct BLC as [(C0 & BLE)|(CP & BLE)].
        - split; [rewrite BLE; exact H|].
          destruct HOC as [(_ & X & _)|(CP & _)]; [|lia]. rewrite X.
          rewrite <- BLE in H. pose proof (BLO L1 A1 m2 md1 q m MR12 H). lia.
        - rewrite BLE in ND1. split; [rewrite BLE; apply s2_mid_in; exact H|].
          exact (s2_nd_out _ _ _ _ _ _ ND1 H). }
      exists L2, A2, R2, m3, md2, K0, M, EL, res, e, (Z_to_bv 64 (0 + (EL + 1))), (Z_to_bv 64 CAP'),
        (Z_to_bv 64 OUT'), ev2.
      rewrite LV.
      split; [first [rewrite H1r|rewrite H1y]; reflexivity|].
      split; [exact RG1|]. split; [exact RG8|]. split; [exact RG18|]. split; [exact RG9|]. split; [exact RG23|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HKS|]. split; [lia|].
      split; [exact ELE|]. split; [exact ELZ|]. split; [exact BY3|].
      split; [exact RM|].
      split; [exact INI2|]. split; [exact RO3|].
      split; [exact NZ|]. split; [exact AL16|]. split; [exact FRB|]. split; [exact INR2|].
      split; [exact RSEP|].
      split.
      { intros q m Hq. rewrite BL3 in Hq. apply s2_mid in Hq. destruct Hq as [EQ|Hq].
        - injection EQ as -> ->. right. right. rewrite UO, UC. split; [reflexivity|]. split; reflexivity.
        - destruct (BL13 q m Hq) as (HQ1 & HQO). rewrite BL1 in HQ1. apply s2_mid in HQ1.
          destruct HQ1 as [EQ|HQ1].
          + injection EQ as -> ->. right. left. split; reflexivity.
          + left. split; [rewrite BL2; exact HQ1|]. intros (_ & X). exact (HQO X). }
      split; [exact BRC3|]. split; [exact EIC3|]. split; [exact COV3|]. split; [exact CEV3|]. split; [exact LCK3|].
      split; [intros X; discriminate X|].
      split; [|exists qs; rewrite UO, UC; split;
        [first [exact LIVE2|rewrite LV in LIVE2; exact LIVE2]
        |rewrite CPE; first [exact RT|rewrite LV in RT; exact RT]]].
      intros _. rewrite UN, UO, UC.
      split; [reflexivity|].
      split.
      { pose proof (RelayCap.send_line_cap_le true (bv_unsigned mx) 0 (bv_unsigned cap) (EL + 1))
          as SCL.
        pose proof (Z.max_spec (bv_unsigned cap) (2 * (0 + (EL + 1)))) as MS. unfold TBBYTES in *. lia. }
      split; [rewrite BL3; apply in_or_app; right; left; reflexivity|].
      split; [exact FBO|].
      split; [intros X; exact (NOUT res (EL + 1) INR RNO ltac:(lia) (eq_sym X))|].
      split; [exists junk'; split; [exact BYO|lia]|].
      intros q m Hq HO Hm. exact (NOUT q m (BLA q m Hq) HO Hm).
    + destruct (LVF eq_refl) as (BLE & CEV3 & COV3).
      exists L2, A2, R2, m3, md2, K0, M, EL, res, e, nout, cap, out.
      eexists. rewrite LV.
      split; [first [rewrite H1r|rewrite H1y]; reflexivity|].
      split; [exact RG1|]. split; [exact RG8|]. split; [exact RG18|]. split; [exact RG9|]. split; [exact RG23|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HKS|]. split; [lia|].
      split; [exact ELE|]. split; [exact ELZ|]. split; [exact BY3|].
      split; [exact RM|].
      split; [exact INI2|]. split; [exact RO3|].
      split; [exact NZ|]. split; [exact AL16|]. split; [exact FRB|]. split; [exact INR2|].
      split; [exact RSEP|].
      split.
      { intros q m Hq. rewrite BLE, BL1 in Hq. apply s2_mid in Hq. destruct Hq as [EQ|Hq].
        - injection EQ as -> ->. right. left. split; reflexivity.
        - left. split; [rewrite BL2; exact Hq|]. intros (X & _). discriminate X. }
      split; [exact BRC3|]. split; [exact EIC3|]. split; [exact COV3|]. split; [exact CEV3|]. split; [exact LCK3|].
      split; [intros _; split; [reflexivity|split; reflexivity]|].
      split; [intros X; discriminate X|].
      exists qs. split; [intros X; discriminate X|first [exact RT|rewrite LV in RT; exact RT]].
Qed.
