(* Segment Q06 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13ed4, 0x13f94], U13ee0 (v1.9 pc
   0x13ed4) -> U13fa4 (v1.9 pc 0x13f98) (r_p = 0). The check_ports tests #80, #81, #81b (in_ch, out_ch, unk are
   multiples of 4), #82 (first), #83 (the sum is 48, C5.6), #84, #85 (in_ch = 4 n_in, out_ch = 4 n_out), #86
   (headamp_base = 16 blk[7]) and the UBSan checks T60-T65 (CNT: every count is at most 12, every sum at most 192)
   and T66 (blk + 7 does not wrap) are not taken. blk is s8, unk is s10 (v1.8 s7, s9). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u7.
Import ListNotations.
Open Scope Z_scope.

(* Branch conditions with shifts (srliw 30, slliw 2, slli 4). *)
Ltac q06_bool :=
  u7_rng; u7_unf; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  try change (2 ^ 30) with 1073741824; try change (2 ^ 2) with 4; try change (2 ^ 4) with 16; u7_zdec.
Ltac q06_nt := u7_br false ltac:(q06_bool).

Lemma q06_byte_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* 0x13ed4 -> 0x13f98 for counts NI (in), NO (out), NE (empty), NU (unknown) of the 12 codes, first unknown code FC
   and blk[7] = B7. *)
Lemma q06_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv blk NI NO NE NU FC B7 : Z),
    sp = Z_to_bv 64 spv -> s8 = Z_to_bv 64 blk -> a1 = Z_to_bv 64 NI -> a0 = Z_to_bv 64 NO -> a2 = Z_to_bv 64 NE ->
    a7 = Z_to_bv 64 FC -> s10 = Z_to_bv 64 (4 * NU) ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> 1 <= blk -> blk + 20 <= 2 ^ 64 ->
    0 <= NI -> 0 <= NO -> 0 <= NE -> 0 <= NU -> NI + NO + NE + NU = 12 -> 0 <= FC < 256 -> 0 <= B7 < 256 ->
    ov_read_bytes rsegs m (Z_to_bv 64 (spv + 1688)) 4 = Some (le4 (Z_to_bv 64 (4 * NI))) ->
    ov_read_bytes rsegs m (Z_to_bv 64 (spv + 1692)) 4 = Some (le4 (Z_to_bv 64 (4 * NO))) ->
    ov_read_bytes rsegs m (Z_to_bv 64 (spv + 1696)) 4 = Some (le4 (Z_to_bv 64 (16 * B7))) ->
    ov_read_bytes rsegs m (Z_to_bv 64 (spv + 1792)) 1 = Some [Z_to_bv 8 FC] ->
    ov_read_bytes rsegs m (Z_to_bv 64 (blk + 7)) 1 = Some [Z_to_bv 8 B7] ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x13f98) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13ed4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv blk NI NO NE NU FC B7 -> -> -> -> -> -> -> Hs0 Hs1 Hb0 Hb1 HI HO HE HU Hsum HF HB7 R0 R1 R2 R3 R4.
  step. step. step. q06_nt.
  step. step. step. q06_nt.
  step. step. q06_nt.
  step. step. step. q06_nt.
  step. step. step. q06_nt.
  step. step. step. step. q06_nt.
  step. step. step. step. q06_nt.
  step. step. step. step. step. q06_nt.
  step. step. step. q06_nt.
  step. step. step. step. q06_nt.
  step. step. q06_nt.
  step. step. step. step. q06_nt.
  step. step. q06_nt.
  step. step. step. q06_nt.
  step. step. step. step. q06_nt.
  apply evt_done. do 7 eexists. reflexivity.
Qed.

Section Q06.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_Q06 : forall j, Hat B APIf ra (Inv_U13f98_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13ed4_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP &
                  (HQB & H26 & Hrp & Hunk & H11 & H10 & H12 & H17)).
  pose proof HQB as (HEQ & H27 & HPO & H1792).
  pose proof HEQ as (HFT & H7 & H2 & HVC & HIFS & H88).
  pose proof HFT as (HLK & HFC & H23 & Hphi & H18).
  pose proof HVC as (H24 & H16 & HB).
  pose proof (u7_big_8819 _ _ H88) as Hbig.
  rewrite (u7_big_true _ _ H88) in H24.
  destruct (u7_S_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (HSa & HSb & HSc & Hsp & HMI).
  destruct (u7_phi_bnd B APIf ra empty g _ L A regs mem md phi _ HFR HP ltac:(lia)) as (Hp1 & Hp2).
  pose proof alloc_ceiling_value as Hac.
  destruct (u7_unk_rp0 _ _ Hrp) as (Eunk & Efirst).
  rewrite Eunk in H26. rewrite Efirst in H1792.
  destruct HPO as (HP0 & _). destruct (HP0 Hrp) as (U0 & U1 & U2).
  set (pbs := t_pbs (g_in g) j) in *.
  pose proof (u7_codes_sum pbs 12) as Hsum.
  pose proof (u7_cnt_range RcLeaf.is_in pbs 12) as RI.
  pose proof (u7_cnt_range RcLeaf.is_out pbs 12) as RO.
  pose proof (u7_cnt_range is_empty pbs 12) as RE.
  pose proof (u7_nunk_nonneg pbs 12) as RU.
  destruct (u7_first_spec pbs 12) as (_ & RF).
  pose proof (u7_byte_range (nth 7 pbs (Z_to_bv 8 0))) as R7.
  assert (Hpbs : bytes_at rsegs (normalize rsegs mem) (phi + 18) pbs).
  { apply u7_norm; [exact HMI|]. apply u7_pbs_bytes. apply u7_g_bytes; [exact Hphi | exact Hbig]. }
  pose proof (u7_rd1 _ _ _ 7 (Z_to_bv 8 0) Hpbs ltac:(unfold pbs; rewrite u7_pbs_length; lia)) as RB7.
  rewrite <- (q06_byte_self (nth 7 pbs (Z_to_bv 8 0))) in RB7.
  change (phi + 18 + Z.of_nat 7) with (phi + 18 + 7) in RB7.
  eapply (u7_mid B APIf ra empty FF g _ L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x _ O. exfalso. apply O. exact I.
  - rewrite sl_mkR_of.
    apply q06_evt with (spv := fsp g) (blk := phi + 18) (NI := RcLeaf.n_in pbs) (NO := RcLeaf.n_out pbs)
      (NE := RcLeaf.cnt is_empty pbs 12) (NU := RcPorts.pu_nunk pbs 12) (FC := RcPorts.pu_first pbs 12)
      (B7 := RcLeaf.bt pbs 7).
    + exact Hsp.
    + exact H24.
    + exact H11.
    + exact H10.
    + exact H12.
    + exact H17.
    + exact H26.
    + unfold fsp, SLOT_FRAME. lia.
    + unfold fsp, SLOT_FRAME. lia.
    + lia.
    + lia.
    + exact (proj1 RI).
    + exact (proj1 RO).
    + exact (proj1 RE).
    + exact RU.
    + unfold RcLeaf.n_in, RcLeaf.n_out. lia.
    + exact RF.
    + exact R7.
    + pose proof (u7_rdn _ _ _ (u7_norm mem _ _ HMI U0)) as R. rewrite length_le4 in R. exact R.
    + pose proof (u7_rdn _ _ _ (u7_norm mem _ _ HMI U1)) as R. rewrite length_le4 in R. exact R.
    + pose proof (u7_rdn _ _ _ (u7_norm mem _ _ HMI U2)) as R. rewrite length_le4 in R. exact R.
    + exact (u7_rdn _ _ _ (u7_norm mem _ _ HMI H1792)).
    + exact RB7.
  - intros ms (a0' & a1' & a2' & a3' & a4' & a5' & a6' & ->).
    do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (a0' & a1' & a2' & a3' & a4' & a5' & a6' & HE).
    destruct (u7_MS_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE) as (ER & Epc & Em). subst R pc' m0'.
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    apply u7_EQ_CC. apply (u7_EQ g j phi regs mem regs' m' [] HEQ (u7_mt _ _ _ MU') (u7_DJE_nil g j phi)).
    unfold EQR. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; reflexivity.
Qed.

End Q06.
