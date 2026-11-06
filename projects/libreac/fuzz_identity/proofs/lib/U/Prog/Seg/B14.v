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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require reac_identity_fw_str_c.
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
Ltac ubr := let H := fresh "HU" in if_cases H; zify_cond H; try (exfalso; lia); try xtrap;
  try (exfalso; rewrite Z.mod_small in H by lia; lia).

Section Seg.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis FWS : lib.U.Prog.reac_identity_fw_str_c.reac_identity_fw_str_contract.

Lemma seg_B14 : forall i,
  Hrec B APIf ra (Inv_U13304_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U132a4_at B APIf ra empty) i.
Proof.
  intros i H g c (pl & L & A & regs & mem & md & -> & HFR & HPERM & HP).
  destruct HP as (HRB & HS6 & HFALL & HRR & HFWA & H10 & H11 & H12 & HD).
  destruct (sb2_FR_basics B APIf ra empty FF g _ _ L A regs mem md HFR)
    as (HAC & HSK & HS47 & HSm & Efsp & G2 & HSTK & HRO & Hh & Hlz & HMR).
  pose proof (sb2_pl_low B APIf g i pl L A mem md _ HMR HPERM) as PLO.
  assert (Hpl : In (pl, rec_k (g_in g) i) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
  destruct (t_block_range B APIf ra empty FF L A mem md _ _ HMR Hpl) as [PL1 PL2].
  pose proof HRB as (HREC & H20 & H26 & H21 & HPLB & HID & HAGN & HBEF & HLPm).
  destruct HFWA as [FR1 FA0].
  destruct (sb2_rec_fw (g_in g) i FR1) as (_ & K4 & DIG & _ & FWM & FWR);
    [rewrite FA0; unfold ADDR_FIRMWARE, ADDR_MODEL_NAME; lia | rewrite FA0; unfold ADDR_FIRMWARE, ADDR_REAC_VERSION; lia |].
  pose proof (rec_pl_length (g_in g) i) as PLL.
  pose proof (rec_k_range (g_in g) i) as KR.
  unfold fw_value, bz, nthb in FWM, FWR, DIG.
  set (p0 := nth 0 (rec_pl (g_in g) i) (zb 0)) in *.
  set (p1 := nth 1 (rec_pl (g_in g) i) (zb 0)) in *.
  set (p2 := nth 2 (rec_pl (g_in g) i) (zb 0)) in *.
  set (p3 := nth 3 (rec_pl (g_in g) i) (zb 0)) in *.
  pose proof (DIG 0%nat ltac:(lia)) as D0. pose proof (DIG 1%nat ltac:(lia)) as D1.
  pose proof (DIG 2%nat ltac:(lia)) as D2. pose proof (DIG 3%nat ltac:(lia)) as D3.
  fold p0 in D0. fold p1 in D1. fold p2 in D2. fold p3 in D3.
  pose proof (bv_unsigned_in_range 8 p0) as B0. pose proof (bv_unsigned_in_range 8 p1) as B1.
  pose proof (bv_unsigned_in_range 8 p2) as B2. pose proof (bv_unsigned_in_range 8 p3) as B3.
  change (bv_modulus 8) with 256 in B0, B1, B2, B3.
  assert (RP0 : ov_read_bytes rsegs mem (wa pl) 1 = Some [p0]).
  { apply (sb2_bytes_at_rd1' rsegs mem pl _ 0 _ HPLB); [lia | lia]. }
  assert (RP1 : ov_read_bytes rsegs mem (wa (pl + 1)) 1 = Some [p1]).
  { apply (sb2_bytes_at_rd1' rsegs mem pl _ 1 _ HPLB); [lia | lia]. }
  assert (RP2 : ov_read_bytes rsegs mem (wa (pl + 2)) 1 = Some [p2]).
  { apply (sb2_bytes_at_rd1' rsegs mem pl _ 2 _ HPLB); [lia | lia]. }
  assert (RP3 : ov_read_bytes rsegs mem (wa (pl + 3)) 1 = Some [p3]).
  { apply (sb2_bytes_at_rd1' rsegs mem pl _ 3 _ HPLB); [lia | lia]. }
  assert (G21 : reg_get regs 21 = Z_to_bv 64 pl) by exact H21.
  assert (G23 : reg_get regs 23 = Z_to_bv 64 (bv_unsigned p0 * 1000 + bv_unsigned p1 * 100 +
                                              bv_unsigned p2 * 10 + bv_unsigned p3)).
  { rewrite <- FWM. exact (proj1 (proj1 HFALL)). }
  assert (WR : wr_at rsegs mem (fsp g + 192) 8) by (apply (sb2_stk_wr rsegs mem _ _ _ _ HSTK); lia).
  eapply (sb2_seg_run B APIf ra empty FF regs 0x132a4 mem md _
    (fun R pc' m' => pc' = 0x13304 /\
       sb2_agree regs R [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] /\
       getr R 10 = Z_to_bv 64 5 /\ sb2_keep mem m' (fsp g + 192) (fsp g + 198) /\ wmono rsegs mem m' /\
       cstr m' (spk g 192) (lib.Prog.reac_identity_fw_str_c.FW
         (bv_unsigned p0 * 1000 + bv_unsigned p1 * 100 + bv_unsigned p2 * 10 + bv_unsigned p3))) Hh Hlz).
  - unfold Regs6ss.mkR_of. rewrite G2, G21, G23.
    step. step. ubr. step. step. ubr. step. step. ubr.
    step. step. step. step. step. step. step. step. step. step. step. step.
    step. step. sb2_br false ltac:(unfold bv_eqb, zxb;
      rewrite (MState.unsigned_lit (bv_unsigned p0)), (MState.unsigned_lit (bv_unsigned p1)),
              (MState.unsigned_lit (bv_unsigned p2)), (MState.unsigned_lit (bv_unsigned p3)) by lia;
      rewrite !MState.unsigned_lit by lia).
    step. step. step. step.
    eapply evt_cut;
      [eapply FWS; [reflexivity | reflexivity | reflexivity | lia | lia | lia | intros _ _; exact WR] |].
    intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                WM & _ & HOK).
    destruct (HOK ltac:(lia) ltac:(lia)) as (Er & HB & MU).
    destruct (lib.Prog.reac_identity_fw_str_c.reac_identity_fw_str_c3_len
                (bv_unsigned p0 * 1000 + bv_unsigned p1 * 100 + bv_unsigned p2 * 10 + bv_unsigned p3) ltac:(lia))
      as [_ EL].
    destruct (Z.ltb_spec (bv_unsigned p0 * 1000 + bv_unsigned p1 * 100 + bv_unsigned p2 * 10 + bv_unsigned p3) 10000)
      as [LT|LT]; [|lia].
    rewrite EL in Er, MU. subst r.
    rewrite (ret_pc_even 0x13304) by first [lia | reflexivity].
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    split; [intros k Hk; cbn [In] in Hk; repeat destruct Hk as [<-|Hk]; try contradiction;
            first [reflexivity | rewrite <- G2; reflexivity | rewrite <- G21; reflexivity |
                   rewrite <- G23; reflexivity]|].
    split; [reflexivity|].
    split; [intros x Hx; apply MU; cbn [outside]; split; [lia | exact I]|].
    split; [exact WM|].
    unfold cstr. exact HB.
  - intros R R' pc' m' (-> & AG & HA10 & K & WM & HC) XR.
    assert (AG' : sb2_agree regs R' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27])
      by (apply (sb2_agree_eqv regs R R' _ AG XR); intros k Hk; cbn [In] in Hk;
          repeat destruct Hk as [<-|Hk]; try contradiction; lia).
    apply H. exists pl, L, A, R', m', md. split; [reflexivity|].
    split; [apply (sb2_FR_mem B APIf ra empty FF g _ _ L A regs mem md R' m' (fsp g + 192) (fsp g + 198)
                     HFR HPERM); [unfold SLOT_K, SLOT_STACK; lia | lia | exact K | exact WM |
                                  apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto]|].
    split; [exact HPERM|].
    split.
    { apply (sb2_RB12_mem g i pl R' mem m' (fsp g + 192) (fsp g + 198)).
      - apply (sb2_RB12 g i pl regs R' mem HRB). apply (sb2_agree_sub regs R' _ _ AG'). cbn [In]. tauto.
      - exact K.
      - left. unfold spk. lia.
      - lia. }
    split; [apply (sb2_S6A g i regs R' HS6); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
    split; [apply (sb2_FALL g i regs R' HFALL); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
    split; [apply (sb2_RRr g i regs R' HRR); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
    split; [split; [exact FR1 | exact FA0]|].
    split; [unfold idS; rewrite FWM; lia|].
    split; [rewrite (sb2_getr_x R R' _ XR) by reflexivity; exact HA10|].
    unfold idS. rewrite FWM. exact HC.
Qed.

End Seg.
