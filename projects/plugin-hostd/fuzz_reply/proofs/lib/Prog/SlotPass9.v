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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c
  RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps SlotHead SlotHeadP SlotRes KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotHeadRun SlotHeadPick SlotHeadQ SlotWalk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotPass1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require SlotPass9G.
Import ListNotations.
Local Open Scope Z_scope.

Lemma land1_even : forall z, Z.even z = true -> Z.land z 1 = 0.
Proof.
  intros z H. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite Zmod_even, H. reflexivity.
Qed.

Lemma op9d_run : forall (P N K : Z)
    (x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (b : byte),
  0 <= K <= N -> N < 2 ^ 26 ->
  (K < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K)) 1 = Some [b]) ->
  (K < N -> Z.even (bv_unsigned b) = true) ->
  store_ok rsegs m (Z_to_bv 64 0x30fcc) 1 = true ->
  store_ok rsegs (write_to_mem m (Z_to_bv 64 0x30fcc) (le1 (Z_to_bv 64 1))) (Z_to_bv 64 0x30fc8) 1 = true ->
  evt rsegs (fun ms => exists (s0 s1 s7 a0 : word) (K' : Z),
      ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 s0 s1 a0 x11 x12 x13 x14 (Z_to_bv 64 1) x16 x17 x18 x19
        (Z_to_bv 64 0x30fc0) x21 x22 s7 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None
        (write_to_mem (write_to_mem m (Z_to_bv 64 0x30fcc) (le1 (Z_to_bv 64 1))) (Z_to_bv 64 0x30fc8)
          (le1 (Z_to_bv 64 1))) ro /\
      s0 = Z_to_bv 64 (P + K') /\ s7 = Z_to_bv 64 (N - K') /\
      ((K < N /\ K' = K + 1) \/ (K = N /\ K' = K)))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K)) x9 x10 x11 x12 x13 x14 (Z_to_bv 64 1) x16 x17 x18 x19
      (Z_to_bv 64 0x30fc0) x21 x22 (Z_to_bv 64 (N - K)) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13e0c) fc None m ro).
Proof.
  intros P N K x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro b HK HN RB EV S1 S2.
  step. if_cases HC.
  - assert (HKN : K = N).
    { unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia. apply Z.eqb_eq in HC. lia. }
    step. step. step. step. step.
    apply evt_done. do 4 eexists. exists K. split; [reflexivity|].
    split; [f_equal; lia|]. split; [f_equal; lia|]. right. split; [exact HKN|reflexivity].
  - assert (HKN : K < N).
    { unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia. apply Z.eqb_neq in HC. lia. }
    specialize (RB HKN). specialize (EV HKN).
    step. step. step. step. step. if_cases HC2.
    + step. step. step. step.
      apply evt_done. do 4 eexists. exists (K + 1). split; [reflexivity|].
      split; [f_equal; lia|]. split; [f_equal; lia|]. left. split; [exact HKN|reflexivity].
    + exfalso. zify_cond HC2. apply HC2.
      pose proof (bv_unsigned_in_range 8 b) as RB8. unfold bv_modulus in RB8. change (2 ^ Z.of_N 8) with 256 in RB8.
      rewrite (unsigned_lit (bv_unsigned b)) by lia. rewrite (land1_even _ EV). reflexivity.
Qed.

Lemma globals_op9d : forall B m cl br gn dd ei N G nfd mx no cap out,
  errno_addr B = 0x311ec ->
  globals_at B m cl br gn dd ei N G nfd mx no cap out ->
  globals_at B (write_to_mem (write_to_mem m (Z_to_bv 64 0x30fcc) (le1 (Z_to_bv 64 1))) (Z_to_bv 64 0x30fc8)
    (le1 (Z_to_bv 64 1))) cl br 1 1 ei N G nfd mx no cap out.
Proof.
  intros B m cl br gn dd ei N G nfd mx no cap out ERR
    (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & ER & HCL & HBR & HGN & HDD & HEI & HGG & HMX).
  set (m1 := write_to_mem m (Z_to_bv 64 0x30fcc) (le1 (Z_to_bv 64 1))).
  assert (W1 : forall A cs, rw_cells (ms_segs B) m A cs ->
    (A + Z.of_nat (cells_size cs) <=? 0x30fcc) || (0x30fcd <=? A) = true -> rw_cells (ms_segs B) m1 A cs).
  { intros A cs H D. apply orb_true_iff in D. rewrite !Z.leb_le in D. pose proof (rw_cells_bound _ _ _ _ H) as BD.
    unfold m1. apply rw_cells_frame; [exact H|lia|rewrite length_le1; lia|rewrite length_le1; lia]. }
  assert (W2 : forall A cs, rw_cells (ms_segs B) m1 A cs ->
    (A + Z.of_nat (cells_size cs) <=? 0x30fc8) || (0x30fc9 <=? A) = true ->
    rw_cells (ms_segs B) (write_to_mem m1 (Z_to_bv 64 0x30fc8) (le1 (Z_to_bv 64 1))) A cs).
  { intros A cs H D. apply orb_true_iff in D. rewrite !Z.leb_le in D. pose proof (rw_cells_bound _ _ _ _ H) as BD.
    apply rw_cells_frame; [exact H|lia|rewrite length_le1; lia|rewrite length_le1; lia]. }
  assert (G6' : rw_cells (ms_segs B) m1 G_DEAD [C1 (Z_to_bv 8 1)]).
  { exact (rw_cells_write _ _ _ _ 0%nat (C1 (Z_to_bv 8 dd)) (C1 (Z_to_bv 8 1)) G6 eq_refl eq_refl I). }
  assert (G5' : rw_cells (ms_segs B) m1 G_GONE [C1 (Z_to_bv 8 gn)]).
  { apply W1; [exact G5|vm_compute; reflexivity]. }
  unfold globals_at.
  split; [apply W2; [apply W1; [exact G1|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G2|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G3|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G4|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [exact (rw_cells_write _ _ _ _ 0%nat (C1 (Z_to_bv 8 gn)) (C1 (Z_to_bv 8 1)) G5' eq_refl eq_refl I)|].
  split; [apply W2; [exact G6'|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G7|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G8|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G9|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G10|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G11|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G12|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G13|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split.
  { destruct ER as [ev ER]. exists ev. rewrite ERR in ER |- *.
    apply W2; [apply W1; [exact ER|vm_compute; reflexivity]|vm_compute; reflexivity]. }
  split; [exact HCL|]. split; [exact HBR|]. split; [right; reflexivity|]. split; [right; reflexivity|].
  split; [exact HEI|].
  split; [split; [intros H; discriminate H|intros _; right; right; reflexivity]|exact HMX].
Qed.

Lemma MI_op9d : forall B API LS SH SK ra empty rc fx j E CS RI t K s c,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> check_bounded_contract -> RI_mono RI ->
  (K < ss_n E -> Z.even (in_byte E K) = true) -> walk_at (ss_pl E) (t + 1) (if K <? ss_n E then K + 1 else K) ->
  MI (rc := rc) B (API rc) E RI t K 0x13e0c (fun _ hj no regs => no = 0 /\ disp_src 9 s hj /\ disp_regs E t K s regs) c ->
  SR (ms_segs B) c (fun c' => exists k', LI (rc := rc) B (API rc) E RI (t + 1) k' c').
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t K s c HF CB RIM HEV HW HM.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  pose proof FF as FFG. do 26 (destruct FFG as [_ FFG]). destruct FFG as [FG _].
  assert (ERR : errno_addr B = 0x311ec).
  { pose proof FF as FTP. do 16 (destruct FTP as [_ FTP]). destruct FTP as (TP & EO & _).
    unfold errno_addr. rewrite TP, EO. reflexivity. }
  assert (GA : forall a, 0x30fc0 <= a < 0x311c0 -> in_globals frame_G a).
  { intros a Ha. apply in_G_bss. lia. }
  assert (IMG : forall a, 0x30fc0 <= a < 0x311c0 -> in_img B a).
  { intros a Ha. exact (proj1 (FG a (GA a Ha))). }
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  replace (t + (if (0x13e0c =? TAIL_CHECK) || (0x13e0c =? TAIL_STEP) then 1 else 0)) with t in HREL
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  destruct HR as (_ & _ & (B2 & B3 & B4 & B20) & (F19 & F21 & F24 & F25 & F26 & F27) & R8 & R23 & R22 & _ & R15).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  assert (RB : K < ss_n E -> ov_read_bytes rsegs mem (Z_to_bv 64 (ss_p E + K)) 1 =
    Some [nth (Z.to_nat K) (ss_pl E) (Z_to_bv 8 0)]).
  { intros HK1. rewrite <- SEG. eapply input_read with (fx := fx); [exact HF|exact HDK|lia]. }
  pose proof HGL as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  assert (S1 : store_ok rsegs mem (Z_to_bv 64 0x30fcc) 1 = true).
  { rewrite <- SEG. change (Z_to_bv 64 0x30fcc) with (wa (G_DEAD + Z.of_nat 0)).
    eapply (rw_cells_store_ok _ _ _ _ 0%nat (C1 (Z_to_bv 8 dd))); [exact G6|reflexivity|reflexivity]. }
  assert (G5' : rw_cells (ms_segs B) (write_to_mem mem (Z_to_bv 64 0x30fcc) (le1 (Z_to_bv 64 1))) G_GONE
    [C1 (Z_to_bv 8 gn)]).
  { pose proof (rw_cells_bound _ _ _ _ G5) as BD.
    apply rw_cells_frame; [exact G5|lia|rewrite length_le1; lia|left; apply Z.leb_le; vm_compute; reflexivity]. }
  assert (S2 : store_ok rsegs (write_to_mem mem (Z_to_bv 64 0x30fcc) (le1 (Z_to_bv 64 1))) (Z_to_bv 64 0x30fc8) 1
    = true).
  { rewrite <- SEG. change (Z_to_bv 64 0x30fc8) with (wa (G_GONE + Z.of_nat 0)).
    eapply (rw_cells_store_ok _ _ _ _ 0%nat (C1 (Z_to_bv 8 gn))); [exact G5'|reflexivity|reflexivity]. }
  assert (E2 : reg_get regs 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
  assert (E3 : reg_get regs 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs 4 = getr (ss_regs E) 4) by exact B4.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (ss_p E + K)) by exact R8.
  assert (E15 : reg_get regs 15 = Z_to_bv 64 1) by exact R15.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 (slot_sp E + 32)) by exact F19.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 G_RELAY_LO) by exact B20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 DIV10) by exact F21.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 t) by exact R22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (ss_n E - K)) by exact R23.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 (slot_sp E + 16)) by exact F24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 4) by exact F25.
  assert (E26 : reg_get regs 26 = Z_to_bv 64 (G_S + 4)) by exact F26.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (G_S + SRC_SIZE * SOURCES_MAX + 4)) by exact F27.
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E15, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    eapply (op9d_run (ss_p E) (ss_n E) K); [lia|unfold INPUT_MAX in Hn; lia|exact RB|exact HEV|exact S1|exact S2]. }
  intros ms1 (can1 & (s0 & s1 & s7 & a0 & K' & -> & E0 & E7 & HCASE) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1). subst s0 s7.
  assert (KR : K <= K' <= ss_n E) by (destruct HCASE as [(H1 & H2)|(H1 & H2)]; lia).
  assert (HW' : walk_at (ss_pl E) (t + 1) K').
  { destruct HCASE as [(HK1 & ->)|(HK1 & ->)].
    - rewrite (proj2 (Z.ltb_lt _ _) HK1) in HW. exact HW.
    - rewrite (proj2 (Z.ltb_ge K (ss_n E)) ltac:(lia)) in HW. exact HW. }
  clear HCASE.
  remember (write_to_mem mem (Z_to_bv 64 0x30fcc) (le1 (Z_to_bv 64 1))) as m1 eqn:EM1.
  remember (write_to_mem m1 (Z_to_bv 64 0x30fc8) (le1 (Z_to_bv 64 1))) as m2 eqn:EM2.
  assert (MU1 : munch [(0x30fcc, 0x30fcd)] mem m1).
  { rewrite EM1. change (Z_to_bv 64 0x30fcc) with (wa 0x30fcc).
    eapply munch_write; [apply munch_refl|lia|rewrite length_le1; lia|cbn [inside]; left; rewrite length_le1; lia]. }
  assert (WM1 : wmono (ms_segs B) mem m1) by (rewrite EM1; apply wmono_write, wmono_refl).
  assert (MU2 : munch [(0x30fc8, 0x30fc9)] m1 m2).
  { rewrite EM2. change (Z_to_bv 64 0x30fc8) with (wa 0x30fc8).
    eapply munch_write; [apply munch_refl|lia|rewrite length_le1; lia|cbn [inside]; left; rewrite length_le1; lia]. }
  assert (WM2 : wmono (ms_segs B) m1 m2) by (rewrite EM2; apply wmono_write, wmono_refl).
  destruct (gs_keep B API LS SH SK ra empty rc fx j E CS L A mem m1 md (target_addrs G (bv_unsigned out) es hj)
    0x30fcc 0x30fcd HF MU1 WM1 ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; eapply cells_writable; [exact G6|change (0x30fcc <= a < 0x30fcc + 1); lia])
    HMR HRO HIK HST HDK) as (MR1 & RO1 & IK1 & ST1 & DK1).
  destruct (gs_keep B API LS SH SK ra empty rc fx j E CS L A m1 m2 md (target_addrs G (bv_unsigned out) es hj)
    0x30fc8 0x30fc9 HF MU2 WM2 ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; eapply cells_writable; [exact G5'|change (0x30fc8 <= a < 0x30fc8 + 1); lia])
    MR1 RO1 IK1 ST1 DK1) as (MR2 & RO2 & IK2 & ST2 & DK2).
  pose proof (gs_relay B mem m1 0x30fcc 0x30fcd MU1 WM1 IMG ltac:(lia) ltac:(lia) L A t nfd G (bv_unsigned out) es hj
    ltac:(unfold G_S; lia) HREL) as REL1.
  pose proof (gs_relay B m1 m2 0x30fc8 0x30fc9 MU2 WM2 IMG ltac:(lia) ltac:(lia) L A t nfd G (bv_unsigned out)
    (map short_entry es) hj ltac:(unfold G_S; lia) REL1) as REL2.
  pose proof (gs_output B mem m1 0x30fcc 0x30fcd MU1 IMG ltac:(lia) ltac:(lia) L A nout cap out HOUT) as OUT1.
  pose proof (gs_output B m1 m2 0x30fc8 0x30fc9 MU2 IMG ltac:(lia) ltac:(lia) L A nout cap out OUT1) as OUT2.
  assert (GL2 : globals_at B m2 cl br 1 1 ei (Z.of_nat (length es)) G nfd mx nout cap out).
  { rewrite EM2, EM1. exact (globals_op9d B mem cl br gn dd ei _ G nfd mx nout cap out ERR HGL). }
  rewrite <- SEG.
  eapply SR_mono; [eapply (MI_tail B API LS SH SK ra empty rc fx j E CS RI t K' (fun _ _ _ r => tail_regs E t K' r));
    [exact HF|exact CB|intros; assumption|exact HW'|]|intros c' HC; exists K'; exact HC].
  exists fx', L, A, R1, m2, md, cl, br, 1, 1, ei, G, nfd, mx, nout, cap, out, (map short_entry (map short_entry es)), hj.
  split; [rewrite ?SEG; reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [lia|]. split; [exact Hn|].
  split; [unfold tail_regs, base_regs, fix_regs; repeat split; geq X1|].
  split; [exact MR2|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
  split; [exact RO2|]. split; [exact IK2|]. split; [exact ST2|].
  split; [rewrite !short_target; exact DK2|].
  split; [rewrite !length_map; exact GL2|].
  split; [(revert Hnfd; cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia)|].
  split; [exact OUT2|].
  split; [eapply relay_at_t; [exact REL2|cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia]|].
  split; [rewrite !length_map; exact Hes|]. split; [rewrite !short_cost; lia|].
  rewrite ?short_view. eapply RIM; [exact HRI|lia].
Qed.

Theorem pass9_dead_holds : check_bounded_contract -> forall RI, RI_mono RI -> pass9_dead_ok RI.
Proof.
  intros CB RI RIM B API LS SH SK ra empty rc fx j E CS HF t k c HL Ht Hk Hop. cbv beta in Hop.
  destruct Hop as [Hop9 Hev].
  eapply SR_bind; [exact (LI_dispatch B API LS SH SK ra empty rc fx j E CS RI t k c HF RIM HL Ht Hk)|].
  intros c' [(s & HM)|(k'' & HL')]; [|apply SR_ret; exists k''; exact HL'].
  rewrite Hop9 in HM. change (jt_target 9) with 0x13e0c in HM. change (disp_k E 9 k) with (k + 1) in HM.
  eapply (MI_op9d B API LS SH SK ra empty rc fx j E CS RI t (k + 1) s c' HF CB RIM); [| |exact HM].
  - intros HK1. destruct Hev as [Hev|Hev]; [lia|exact Hev].
  - replace (k + 1 + 1) with (k + 2) by lia.
    exact (walk_one E t k 9 (LI_walk _ _ _ _ _ _ _ _ HL) (frame_len B API LS SH SK ra empty rc fx j E CS HF) Hk Hop9
      (or_intror (or_intror eq_refl))).
Qed.

Theorem pass9_holds : check_bounded_contract -> pthread_mutex_lock_contract -> pthread_mutex_unlock_contract ->
  forall RI, RI_mono RI -> pass_ok RI 9.
Proof.
  intros CB LCK ULK RI RIM. apply pass9_of_branches.
  - exact (pass9_dead_holds CB RI RIM).
  - exact (SlotPass9G.pass9_gone_holds CB LCK ULK RI RIM).
Qed.
