From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac ZBridge
Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_identity_fw_str_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sb2.
Import ListNotations.
Open Scope Z_scope.

Ltac sb2_br b rw :=
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; rw; solve_cond]
  end.

Lemma sb2_dg_unsigned : forall x, 0 <= x <= 9 -> bv_unsigned (dg x) = 48 + x.
Proof.
  intros x Hx. unfold dg. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. lia.
Qed.

Section Seg.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_B16 : forall i,
  Hrec B APIf ra (Inv_K134c8_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13230_at B APIf ra empty) i.
Proof.
  intros i H g c (pl & L & A & regs & mem & md & -> & HFR & HPERM & HP).
  destruct HP as (HRB & HS7 & HFALL & H9 & HFWA & HV & HS).
  pose proof HFR as HFR'. unfold FR in HFR'. cbv zeta in HFR'.
  destruct HFR' as (HGV & H2s & _ & _ & _ & _ & _ & _ & HMR & _).
  pose proof (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hlz & _).
  pose proof HRB as (HREC & H21 & H20 & H22 & HPLB & HID & HAGN & HBEF & HLPm).
  destruct HFWA as [FR1 FA0].
  destruct (sb2_rec_fw (g_in g) i FR1) as (_ & K4 & DIG & _ & FWM & FWR);
    [rewrite FA0; unfold ADDR_FIRMWARE, ADDR_MODEL_NAME; lia | rewrite FA0; unfold ADDR_FIRMWARE, ADDR_REAC_VERSION; lia |].
  pose proof (rec_pl_length (g_in g) i) as PLL.
  pose proof (rec_k_range (g_in g) i) as KR.
  assert (PL4 : (4 <= length (rec_pl (g_in g) i))%nat) by lia.
  assert (ALLD : all_digits (firstn 4 (rec_pl (g_in g) i)) = true).
  { unfold all_digits. apply forallb_forall. intros b Hb.
    apply In_nth with (d := zb 0) in Hb. destruct Hb as (j & Hj & <-).
    rewrite length_firstn in Hj. rewrite nth_first by lia. apply Z.leb_le. apply DIG. lia. }
  unfold idS in HS. rewrite FWM, (sb2_FW_digits _ PL4 ALLD) in HS.
  unfold cstr in HS. cbn [app] in HS.
  unfold bz, nthb in DIG, HS.
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
  assert (U0 : bv_unsigned (dg (bv_unsigned p0)) = 48 + bv_unsigned p0) by (apply sb2_dg_unsigned; lia).
  assert (U1 : bv_unsigned (dg (bv_unsigned p1)) = 48 + bv_unsigned p1) by (apply sb2_dg_unsigned; lia).
  assert (U2 : bv_unsigned (dg (bv_unsigned p2)) = 48 + bv_unsigned p2) by (apply sb2_dg_unsigned; lia).
  assert (U3 : bv_unsigned (dg (bv_unsigned p3)) = 48 + bv_unsigned p3) by (apply sb2_dg_unsigned; lia).
  assert (RP0 : ov_read_bytes rsegs mem (wa pl) 1 = Some [p0]).
  { apply (sb2_bytes_at_rd1' rsegs mem pl _ 0 _ HPLB); [lia | lia]. }
  assert (RP1 : ov_read_bytes rsegs mem (wa (pl + 1)) 1 = Some [p1]).
  { apply (sb2_bytes_at_rd1' rsegs mem pl _ 1 _ HPLB); [lia | lia]. }
  assert (RP2 : ov_read_bytes rsegs mem (wa (pl + 2)) 1 = Some [p2]).
  { apply (sb2_bytes_at_rd1' rsegs mem pl _ 2 _ HPLB); [lia | lia]. }
  assert (RP3 : ov_read_bytes rsegs mem (wa (pl + 3)) 1 = Some [p3]).
  { apply (sb2_bytes_at_rd1' rsegs mem pl _ 3 _ HPLB); [lia | lia]. }
  assert (RS0 : ov_read_bytes rsegs mem (wa (fsp g + 176)) 1 = Some [dg (bv_unsigned p0)]).
  { apply (sb2_bytes_at_rd1' rsegs mem (spk g 176) _ 0 _ HS); [cbn; lia | unfold spk; lia]. }
  assert (RS1 : ov_read_bytes rsegs mem (wa (fsp g + 177)) 1 = Some [Z_to_bv 8 0x2e]).
  { apply (sb2_bytes_at_rd1' rsegs mem (spk g 176) _ 1 _ HS); [cbn; lia | unfold spk; lia]. }
  assert (RS2 : ov_read_bytes rsegs mem (wa (fsp g + 178)) 1 = Some [dg (bv_unsigned p1)]).
  { apply (sb2_bytes_at_rd1' rsegs mem (spk g 176) _ 2 _ HS); [cbn; lia | unfold spk; lia]. }
  assert (RS3 : ov_read_bytes rsegs mem (wa (fsp g + 179)) 1 = Some [dg (bv_unsigned p2)]).
  { apply (sb2_bytes_at_rd1' rsegs mem (spk g 176) _ 3 _ HS); [cbn; lia | unfold spk; lia]. }
  assert (RS4 : ov_read_bytes rsegs mem (wa (fsp g + 180)) 1 = Some [dg (bv_unsigned p3)]).
  { apply (sb2_bytes_at_rd1' rsegs mem (spk g 176) _ 4 _ HS); [cbn; lia | unfold spk; lia]. }
  assert (RL : ov_read_bytes rsegs mem (wa (fsp g + 40)) 8 = Some (le8 (Z_to_bv 64 (rec_Lp (g_in g) i)))).
  { unfold LPm, q64 in HLPm. replace (fsp g + 40) with (spk g 40 + 0) by (unfold spk; lia).
    rewrite (bytes_at_read rsegs mem (spk g 40) _ 0 8 HLPm) by (rewrite ?length_le8; lia).
    rewrite skipn_O, firstn_all2 by (rewrite length_le8; lia). reflexivity. }
  assert (G2 : reg_get regs 2 = Z_to_bv 64 (fsp g)) by exact H2s.
  assert (G9 : reg_get regs 9 = Z_to_bv 64 5) by exact H9.
  assert (G22 : reg_get regs 22 = Z_to_bv 64 pl) by exact H22.
  eapply (sb2_seg_run B APIf ra empty FF regs 0x13230 mem md _
    (fun R pc' m' => pc' = 0x134c8 /\ m' = mem /\
       sb2_agree regs R [2; 3; 4; 19; 20; 21; 22] /\ getr R 18 = Z_to_bv 64 (rec_Lp (g_in g) i)) Hh Hlz).
  - unfold Regs6ss.mkR_of. rewrite G2, G9, G22.
    step. step. sb2_br false idtac.
    step. step. step. step. sb2_br false ltac:(unfold bv_eqb, zxb; rewrite U0, (MState.unsigned_lit (bv_unsigned p0)) by lia; rewrite !MState.unsigned_lit by lia).
    step. step. step. sb2_br false idtac.
    step. step. step. step. sb2_br false ltac:(unfold bv_eqb, zxb; rewrite U1, (MState.unsigned_lit (bv_unsigned p1)) by lia; rewrite !MState.unsigned_lit by lia).
    step. step. step. step. sb2_br false ltac:(unfold bv_eqb, zxb; rewrite U2, (MState.unsigned_lit (bv_unsigned p2)) by lia; rewrite !MState.unsigned_lit by lia).
    step. step. step. step. sb2_br false ltac:(unfold bv_eqb, zxb; rewrite U3, (MState.unsigned_lit (bv_unsigned p3)) by lia; rewrite !MState.unsigned_lit by lia).
    step. step.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
    intros k Hk. cbn [In] in Hk. repeat destruct Hk as [<-|Hk]; try contradiction;
      first [reflexivity | rewrite <- G2; reflexivity | rewrite <- G22; reflexivity].
  - intros R R' pc' m' (-> & -> & AG & HA18) XR.
    assert (AG' : sb2_agree regs R' [2; 3; 4; 19; 20; 21; 22])
      by (apply (sb2_agree_eqv regs R R' _ AG XR); intros k Hk; cbn [In] in Hk;
          repeat destruct Hk as [<-|Hk]; try contradiction; lia).
    pose proof HREC as (HNR & H19 & HNRb & HG16 & HHW).
    apply H. exists pl, L, A, R', mem, md. split; [reflexivity|].
    split; [apply (sb2_FR_regs B APIf ra empty FF g _ _ L A regs mem md R' HFR HPERM);
            apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
    split; [exact HPERM|].
    split; [exact HNR|].
    split; [sb2_ag AG' 19; exact H19|].
    split; [exact HNRb|]. split; [exact HG16|].
    split.
    { unfold HWb, rec_have, rec_hwb in *. rewrite sb2_rec_hw_keep; [exact HHW|].
      rewrite FA0. unfold ADDR_FIRMWARE, ADDR_REAC_VERSION. lia. }
    split; [exact HID|].
    split; [sb2_ag AG' 20; exact H20|].
    split; [sb2_ag AG' 21; exact H21|].
    split; [rewrite (sb2_getr_x R R' _ XR) by reflexivity; exact HA18|].
    sb2_ag AG' 22. exact H22.
Qed.

End Seg.
