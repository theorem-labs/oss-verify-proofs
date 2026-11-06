From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c disco_table hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_master_only_cadence_ns_c reac_rate_snap_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_hunt_step_c reac_hunt_verdict_name_c check_table_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_hunt_role_c reac_hunt_heard_anything_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib.
Import ListNotations.
Open Scope Z_scope.

Definition LATCH : Z := 0x1446c.

Lemma uslot_R16 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spz i n : Z),
  sp = Z_to_bv 64 spz -> s7 = Z_to_bv 64 n ->
  0 <= spz -> spz + 168 <= 2 ^ 64 -> 0 <= i < MAX_OPS -> 0 <= n < 2 ^ 64 ->
  rw_cells rsegs m (spz + 160) [C8 (Z_to_bv 64 i)] ->
  evt rsegs
    (fun ms' => ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (if i <? MAX_OPS - 1 then i + 1 else i)) t1 t2 s0 s1
                              (Z_to_bv 64 510) a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 (if (i <? MAX_OPS - 1) && negb (n =? 0) then HDR else EXIT)) fc None m
                         (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 LATCH) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spz i n Esp Es7 Hsp0 Hsp1 Hi Hn RI.
  subst sp s7. unfold LATCH, MAX_OPS in *. unfold HDR, EXIT.
  step. step. step.
  rewrite ltu_lit by lia.
  destruct (Z.ltb_spec 510 i) as [Hx|Hx].
  - replace (i <? 511) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
    apply evt_done. reflexivity.
  - replace (i <? 511) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
    step. rewrite ?(unsigned_lit i) by lia. rewrite swrap32_id by lia. step.
    rewrite eqb_lit by lia.
    destruct (Z.eqb_spec n 0) as [Hz|Hz]; cbn [negb].
    + apply evt_done. reflexivity.
    + step. apply evt_done. reflexivity.
Qed.

Lemma R15_ro : forall m a bs, mem_inv rsegs m ->
  (ro_bytes_b rsegs a bs && (0 <=? a) && (a + Z.of_nat (length bs) <=? 2 ^ 64))%bool = true ->
  bytes_at rsegs m a bs.
Proof.
  intros m a bs Hm H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H2. apply Z.leb_le in H3.
  apply ro_bytes_at; [exact Hm | exact H2 | exact H3 |]. apply ro_bytes_b_sound. exact H1.
Qed.

Lemma R15_rodata : forall m, mem_inv rsegs m ->
  bytes_at rsegs m RT RATES /\ bytes_at rsegs m A_P6000 (le8 (Z_to_bv 64 D6000)) /\
  bytes_at rsegs m A_P3837 (le8 (Z_to_bv 64 D3837)) /\
  bytes_at rsegs m TB (le4 (Z_to_bv 64 (-422))) /\
  bytes_at rsegs m (TB + 4) (le4 (Z_to_bv 64 (-313))) /\
  bytes_at rsegs m (TB + 8) (le4 (Z_to_bv 64 (-477))) /\
  bytes_at rsegs m A_MASTER S_MASTER /\ bytes_at rsegs m A_SLAVE S_SLAVE /\
  bytes_at rsegs m A_REFUSED S_REFUSED /\ bytes_at rsegs m A_HUNTING S_HUNTING.
Proof.
  intros m MI. repeat match goal with |- _ /\ _ => split end; apply R15_ro; try exact MI; vm_compute; reflexivity.
Qed.

Lemma R15_ch : forall c : bool, bv_ltu (Z_to_bv 64 (if c then 0 else 1)) (Z_to_bv 64 2) = true.
Proof. intros []; vm_compute; reflexivity. Qed.

Lemma R15_name : forall v, bv_eqb (Z_to_bv 64 (reac_hunt_verdict_name_model v)) (Z_to_bv 64 0) = false.
Proof.
  intros v. unfold reac_hunt_verdict_name_model.
  destruct (v =? 1); [|destruct (v =? 2); [|destruct (v =? 3)]]; vm_compute; reflexivity.
Qed.

Lemma R15_bytes : forall m a n bs, rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof. intros m a n bs [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

Lemma R15_tbl : forall m h H', bytes_at rsegs m h H' -> length H' = 480%nat -> bytes_at rsegs m h (firstn 400 H').
Proof.
  intros m h H' B L. rewrite <- (firstn_skipn 400 H') in B. apply bytes_at_app in B. destruct B as [B _]. exact B.
Qed.

Lemma R15_le4 : forall bs k, 0 <= k -> k + 4 <= Z.of_nat (length bs) -> le4 (Z_to_bv 64 (s32_at bs k)) = sub bs k 4.
Proof.
  intros bs k Hk Hl. pose proof (length_sub bs k 4 Hk Hl) as L.
  unfold s32_at, u_at. revert L. generalize (sub bs k 4) as w. intros w Lw.
  pose proof (ble_range w) as R. rewrite Lw in R. change (8 * Z.of_nat 4) with 32 in R.
  unfold le4. rewrite unsigned_lit_wrap.
  rewrite (Z_to_le_bytes_mod 4 _ 64) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 _ 32) by lia.
  replace (bv_swrap 32 (bytes_le_to_Z w) mod 2 ^ 32) with (bytes_le_to_Z w).
  - pose proof (Z_to_le_bytes_to_Z w) as E. rewrite Lw in E. exact E.
  - unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
    Z.div_mod_to_equations. lia.
Qed.

Lemma R15_field : forall m h H' k, bytes_at rsegs m h H' -> 0 <= k -> k + 4 <= Z.of_nat (length H') ->
  bytes_at rsegs m (h + k) (le4 (Z_to_bv 64 (s32_at H' k))).
Proof. intros m h H' k B Hk Hl. rewrite R15_le4 by assumption. apply bytes_at_sub; assumption. Qed.

Lemma R15_ch1 : forall c : bool, bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 (if c then 0 else 1)) = false.
Proof. intros []; vm_compute; reflexivity. Qed.

Ltac cfalse := lazymatch goal with |- evt _ _ (MS _ _ (if ?cc then _ else _) _ _ _ _) =>
  replace cc with false by (vm_compute; reflexivity) end; cbv iota.

Lemma uslot_R15 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo h n p now : Z) (H : list byte),
  reac_hunt_step_contract -> reac_hunt_verdict_name_contract -> check_table_contract ->
  reac_hunt_role_contract -> reac_hunt_heard_anything_contract ->
  sp = Z_to_bv 64 X -> s11 = Z_to_bv 64 1 ->
  0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 -> 0 <= now < 2 ^ 64 ->
  0 < h -> h mod 16 = 0 -> h + 480 <= lo -> lo + REAC_HUNT_STEP_K <= X -> RT + 12 <= lo ->
  rw_cells rsegs m (X + 128) [C8 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (X + 136) [C8 (Z_to_bv 64 n)] ->
  rw_cells rsegs m (X + 152) [C8 (Z_to_bv 64 p)] ->
  rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 h)] ->
  rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 now)] ->
  rw_cells rsegs m h [CB 480 H] -> hunt_ok H ->
  mem_inv rsegs m -> stk rsegs m lo X ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (F' : bvmap 5 word) (m' : word -> option byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 h) (Z_to_bv 64 now) a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 (Z_to_bv 64 p) s6 (Z_to_bv 64 n) s8 s9 s10 s11 t3' t4' t5' t6')
                F' (Z_to_bv 64 LATCH) fc None m' (seg_rom rsegs) /\
       freg_kept F F' /\
       munch [(lo, X); (h, h + 480)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
       rw_cells rsegs m' (X + 128) [C8 (Z_to_bv 64 0)] /\ rw_cells rsegs m' (X + 136) [C8 (Z_to_bv 64 n)] /\
       rw_cells rsegs m' (X + 152) [C8 (Z_to_bv 64 p)] /\ rw_cells rsegs m' (X + 168) [C8 (Z_to_bv 64 h)] /\
       rw_cells rsegs m' (X + 224) [C8 (Z_to_bv 64 now)] /\
       rw_cells rsegs m' h [CB 480 (hs_hunt h H now)] /\ hunt_ok (hs_hunt h H now))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1417c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X lo h n p now H HSC VNC CTC RLC HAC Esp Es11 HX0 HX16 HX1 Hnow Hh0 Hh16 Hhlo Hlo HRT
    R128 R136 R152 R168 R224 RH HOK MI ST.
  subst sp s11. unfold LATCH. unfold REAC_HUNT_STEP_K in Hlo.
  pose proof (R15_rodata m MI) as (R1 & R2 & R3 & _).
  pose proof (munch_refl [(lo, X); (h, h + 480)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step.
  eapply evt_cut.
  { eapply HSC with (lo := lo) (h := h) (now := now) (H := H);
      first [ reflexivity | assumption
            | unfold off_window, REAC_HUNT_STEP_K; rewrite ?(unsigned_lit X) by lia;
              first [ assumption | lia | Z.div_mod_to_equations; lia ] ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & m2 &
              Eq & FK & MUc & WMc & MI2 & ST2 & RH2 & HOK2).
  subst ms'. clear R1 R2 R3.
  rewrite (unsigned_lit X) in MUc, ST2 by lia. unfold REAC_HUNT_STEP_K in MUc.
  transport_after_call rsegs m m2 MUc WMc. clear MUc WMc MI.
  rewrite (ret_pc_even 82316) by (first [lia | reflexivity]).
  remember (hs_hunt h H now) as H' eqn:EH'.
  pose proof HOK2 as (LH & (T1 & T2 & T3 & T4) & LK & VR).
  pose proof (R15_bytes m2 h 480 H' RH2) as BH.
  step. step. step.
  rewrite R15_ch1. cbn [negb].
  step. step.
  cfalse.
  step. step.
  rewrite lw_val by (rewrite length_firstn, length_skipn, LH; reflexivity).
  step.
  pose proof (R15_rodata m2 MI2) as (_ & _ & _ & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  eapply evt_cut.
  { eapply VNC with (v := s32_at H' 440); [reflexivity | apply s32_range | eassumption ..]. }
  intros ms' (b1 & Eq & BN). subst ms'. clear Q1 Q2 Q3 Q4 Q5 Q6 Q7 BN.
  rewrite (ret_pc_even 82348) by (first [lia | reflexivity]).
  step.
  rewrite R15_name. cbv iota.
  step. step. step.
  eapply evt_cut.
  { eapply CTC with (lo := lo) (t := h) (T := firstn 400 H');
      first [ reflexivity | assumption | exact (R15_tbl m2 h H' BH LH)
            | rewrite length_firstn, LH; reflexivity
            | unfold off_window, CHECK_TABLE_K; rewrite ?(unsigned_lit X) by lia;
              first [ assumption | lia | Z.div_mod_to_equations; lia ] ]. }
  intros ms' (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & c14 & m3 &
              Eq & MUc & WMc & MI3 & ST3).
  subst ms'. clear BH.
  rewrite (unsigned_lit X) in MUc, ST3 by lia. unfold CHECK_TABLE_K in MUc.
  transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc MI2.
  rewrite (ret_pc_even 82364) by (first [lia | reflexivity]).
  pose proof (R15_bytes m3 h 480 H' RH2) as BH.
  step. step.
  eapply evt_cut.
  { eapply RLC with (h := h) (v := s32_at H' 440);
      [ reflexivity | lia | Z.div_mod_to_equations; lia | apply s32_range | apply R15_field; [exact BH | lia | rewrite LH; lia] ]. }
  intros ms' (b2 & Eq). subst ms'.
  rewrite (ret_pc_even 82372) by (first [lia | reflexivity]).
  step. step.
  eapply evt_cut.
  { eapply HAC with (h := h) (n := s32_at H' 384);
      [ reflexivity | lia | Z.div_mod_to_equations; lia | apply s32_range | apply R15_field; [exact BH | lia | rewrite LH; lia] ]. }
  intros ms' (b3 & Eq). subst ms'.
  rewrite (ret_pc_even 82380) by (first [lia | reflexivity]).
  step.
  apply evt_done. do 18 eexists.
  split; [reflexivity |].
  subst H'.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ HOK2)))))))))));
    eassumption.
Qed.
