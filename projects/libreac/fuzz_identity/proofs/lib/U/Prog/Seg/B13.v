From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac ZBridge
Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab1 UTac_uab2.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Ltac sb2_br b rw :=
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; rw; solve_cond]
  end.

Ltac xtrap := match goal with H : Z.lxor (Z.b2z (?a <? ?b)) (Z.b2z (?c <? ?d)) = 0 |- _ =>
  rewrite (proj2 (Z.ltb_lt a b)) in H by lia; rewrite (proj2 (Z.ltb_ge c d)) in H by lia; discriminate H end.
Ltac ubr := let H := fresh "HB" in if_cases H; zify_cond H; try (exfalso; lia); try xtrap;
  try (exfalso; rewrite Z.mod_small in H by lia; lia).

Section Seg.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma seg_B13_body : forall g i t c,
  Inv_U13270_at B APIf ra empty g i t c ->
  Hrec B APIf ra (Inv_U132a4_at B APIf ra empty) i ->
  (forall c', t < 3 -> Inv_U13270_at B APIf ra empty g i (t + 1) c' -> Rz (ms_segs B) c' (Post B APIf ra g)) ->
  Rz (ms_segs B) c (Post B APIf ra g).
Proof.
  intros g i t c [pl (L & A & regs & mem & md & -> & HFR & HPERM & (Ht & HFWL))] H HL.
  destruct HFWL as (HRB & HS6 & HFALL & HRR & HFWA & H10 & H11 & H12 & HD).
  pose proof HFR as HFR'. unfold FR in HFR'. cbv zeta in HFR'.
  destruct HFR' as (HGV & H2s & _ & _ & _ & _ & _ & _ & HMR & _).
  pose proof (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hlz & _).
  pose proof HRB as (HREC & H20 & H26 & H21 & HPLB & HID & HAGN & HBEF & HLPm).
  assert (Hpl : In (pl, rec_k (g_in g) i) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
  destruct (t_block_range B APIf ra empty FF L A mem md _ _ HMR Hpl) as [PL1 PL2].
  pose proof alloc_ceiling_value as AC.
  destruct HFWA as [FR1 FA0].
  destruct (sb2_rec_fw (g_in g) i FR1) as (_ & K4 & DIG & _ & _ & _);
    [rewrite FA0; unfold ADDR_FIRMWARE, ADDR_MODEL_NAME; lia | rewrite FA0; unfold ADDR_FIRMWARE, ADDR_REAC_VERSION; lia |].
  pose proof (rec_pl_length (g_in g) i) as PLL.
  assert (DT : bv_unsigned (nth (Z.to_nat t) (rec_pl (g_in g) i) (zb 0)) <= 9)
    by (exact (DIG (Z.to_nat t) ltac:(lia))).
  assert (RD : ov_read_bytes rsegs mem (wa (pl + t)) 1 = Some [nth (Z.to_nat t) (rec_pl (g_in g) i) (zb 0)]).
  { apply (sb2_bytes_at_rd1' rsegs mem pl _ (Z.to_nat t) _ HPLB); [lia | lia]. }
  assert (G10 : reg_get regs 10 = Z_to_bv 64 (4 - t)) by exact H10.
  assert (G11 : reg_get regs 11 = Z_to_bv 64 (pl + t)) by exact H11.
  assert (G12 : reg_get regs 12 = Z_to_bv 64 (pl + t)) by exact H12.
  assert (G21 : reg_get regs 21 = Z_to_bv 64 pl) by exact H21.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat t) (rec_pl (g_in g) i) (zb 0))) as BR.
  change (bv_modulus 8) with 256 in BR.
  destruct (Z.eq_dec t 3) as [E3|N3].
  - subst t. change (Z.to_nat 3) with 3%nat in *.
    eapply (sb2_seg_run B APIf ra empty FF regs 0x13270 mem md _
      (fun R pc' m' => pc' = 0x132a4 /\ m' = mem /\
         sb2_agree regs R [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] /\
         getr R 10 = Z_to_bv 64 0 /\ getr R 11 = Z_to_bv 64 (pl + 4) /\ getr R 12 = Z_to_bv 64 (pl + 4)) Hh Hlz).
    + unfold Regs6ss.mkR_of. rewrite G10, G11, G12, G21.
      step. ubr. step. step. step. step. ubr. step. ubr.
      step. step. step.
      sb2_br false ltac:(unfold bv_ltu, zxb; rewrite !MState.unsigned_lit by lia).
      step. step. step. step.
      sb2_br false ltac:(unfold bv_eqb; rewrite !MState.unsigned_lit by lia).
      apply evt_done. do 3 eexists. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [intros k Hk; cbn [In] in Hk; repeat destruct Hk as [<-|Hk]; try contradiction;
              first [reflexivity | rewrite <- G21; reflexivity]|].
      split; [reflexivity|]. split; f_equal; lia.
    + intros R R' pc' m' (-> & -> & AG & HA10 & HA11 & HA12) XR.
      assert (AG' : sb2_agree regs R' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27])
        by (apply (sb2_agree_eqv regs R R' _ AG XR); intros k Hk; cbn [In] in Hk;
            repeat destruct Hk as [<-|Hk]; try contradiction; lia).
      apply H. exists pl, L, A, R', mem, md. split; [reflexivity|].
      split; [apply (sb2_FR_regs B APIf ra empty FF g _ _ L A regs mem md R' HFR HPERM);
              apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [exact HPERM|].
      split; [apply (sb2_RB12 g i pl regs R' mem HRB); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [apply (sb2_S6A g i regs R' HS6); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [apply (sb2_FALL g i regs R' HFALL); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [apply (sb2_RRr g i regs R' HRR); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [split; [exact FR1 | exact FA0]|].
      split; [rewrite (sb2_getr_x R R' _ XR) by reflexivity; exact HA10|].
      split; [rewrite (sb2_getr_x R R' _ XR) by reflexivity; exact HA11|].
      split; [rewrite (sb2_getr_x R R' _ XR) by reflexivity; exact HA12|].
      intros j Hj. apply DIG. lia.
  - assert (T3 : 0 <= t < 3) by lia.
    eapply (sb2_seg_run B APIf ra empty FF regs 0x13270 mem md _
      (fun R pc' m' => pc' = 0x13270 /\ m' = mem /\
         sb2_agree regs R [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] /\
         getr R 10 = Z_to_bv 64 (4 - (t + 1)) /\ getr R 11 = Z_to_bv 64 (pl + (t + 1)) /\
         getr R 12 = Z_to_bv 64 (pl + (t + 1))) Hh Hlz).
    + unfold Regs6ss.mkR_of. rewrite G10, G11, G12, G21.
      step. ubr. step. step. step. step. ubr. step. ubr.
      step. step. step.
      sb2_br false ltac:(unfold bv_ltu, zxb; rewrite !MState.unsigned_lit by lia).
      step. step. step. step.
      sb2_br true ltac:(unfold bv_eqb; rewrite !MState.unsigned_lit by lia).
      replace (4 - t + -1) with (4 - (t + 1)) by lia. replace (pl + t + 1) with (pl + (t + 1)) by lia.
      apply evt_done. do 3 eexists. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [intros k Hk; cbn [In] in Hk; repeat destruct Hk as [<-|Hk]; try contradiction;
              first [reflexivity | rewrite <- G21; reflexivity]|].
      split; [reflexivity|]. split; reflexivity.
    + intros R R' pc' m' (-> & -> & AG & HA10 & HA11 & HA12) XR.
      assert (AG' : sb2_agree regs R' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27])
        by (apply (sb2_agree_eqv regs R R' _ AG XR); intros k Hk; cbn [In] in Hk;
            repeat destruct Hk as [<-|Hk]; try contradiction; lia).
      apply HL; [lia|]. exists pl, L, A, R', mem, md. split; [reflexivity|].
      split; [apply (sb2_FR_regs B APIf ra empty FF g _ _ L A regs mem md R' HFR HPERM);
              apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [exact HPERM|].
      split; [lia|].
      split; [apply (sb2_RB12 g i pl regs R' mem HRB); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [apply (sb2_S6A g i regs R' HS6); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [apply (sb2_FALL g i regs R' HFALL); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [apply (sb2_RRr g i regs R' HRR); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [split; [exact FR1 | exact FA0]|].
      split; [rewrite (sb2_getr_x R R' _ XR) by reflexivity; exact HA10|].
      split; [rewrite (sb2_getr_x R R' _ XR) by reflexivity; exact HA11|].
      split; [rewrite (sb2_getr_x R R' _ XR) by reflexivity; exact HA12|].
      intros j Hj. apply DIG. lia.
Qed.

Lemma seg_B13 : forall i t,
  Hrec B APIf ra (Inv_U132a4_at B APIf ra empty) i ->
  Hrec B APIf ra (fun g i c => Inv_U13270_at B APIf ra empty g i t c) i.
Proof.
  intros i t H g c Hc.
  assert (IND : forall n t c, (Z.to_nat (3 - t) <= n)%nat -> Inv_U13270_at B APIf ra empty g i t c ->
                  Rz (ms_segs B) c (Post B APIf ra g)).
  { induction n as [|n IH]; intros t0 c0 Hn Hc0;
      apply (seg_B13_body g i t0 c0 Hc0 H); intros c' Ht Hc'.
    - exfalso. lia.
    - apply (IH (t0 + 1) c'); [lia | exact Hc']. }
  exact (IND _ t c (le_n _) Hc).
Qed.

End Seg.
