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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sb2.
Import ListNotations.
Open Scope Z_scope.

Ltac sb2_br b rw :=
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; rw; solve_cond]
  end.

Section Seg.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis BC : bcmp_c.bcmp_contract.

Lemma seg_B11 : forall i,
  Hrec B APIf ra (Inv_K13188_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13144_at B APIf ra empty) i.
Proof.
  intros i H g c (pl & L & A & regs & mem & md & -> & HFR & HPERM & HP).
  destruct HP as (HB03 & HID & HBEF & HRR & HLPm & HAGN & H25 & HF11 & HF0 & H10).
  destruct (sb2_FR_basics B APIf ra empty FF g _ _ L A regs mem md HFR)
    as (HAC & HSK & HS47 & HSm & Efsp & G2 & HSTK & HRO & Hh & Hlz & HMR).
  pose proof (sb2_pl_low B APIf g i pl L A mem md _ HMR HPERM) as PLO.
  set (idb := rec_id (g_in g) (S i)) in *.
  assert (LID : length idb = 38%nat) by (unfold idb; rewrite rec_id_length; reflexivity).
  unfold IDb, AGN in HID, HAGN. fold idb in HID, HAGN.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HID) as IDn.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HAGN) as AGn.
  assert (RA20 : ov_read_bytes rsegs (normalize rsegs mem) (wa (fsp g + 246)) 1 = Some [nth 20 idb (zb 0)]).
  { apply (sb2_bytes_at_rd1' rsegs _ (spk g 226) idb 20 _ AGn); [lia | unfold spk; lia]. }
  assert (RI20 : ov_read_bytes rsegs (normalize rsegs mem) (wa (fsp g + 150)) 1 = Some [nth 20 idb (zb 0)]).
  { apply (sb2_bytes_at_rd1' rsegs _ (spk g 130) idb 20 _ IDn); [lia | unfold spk; lia]. }
  assert (RA22 : ov_read_bytes rsegs (normalize rsegs mem) (wa (fsp g + 248)) 2 = Some (le2 (Z_to_bv 64 (major idb)))).
  { apply (sb2_bytes_at_rd2 rsegs _ (spk g 226) idb 22 _ AGn); [lia | unfold spk; lia]. }
  assert (RI22 : ov_read_bytes rsegs (normalize rsegs mem) (wa (fsp g + 152)) 2 = Some (le2 (Z_to_bv 64 (major idb)))).
  { apply (sb2_bytes_at_rd2 rsegs _ (spk g 130) idb 22 _ IDn); [lia | unfold spk; lia]. }
  assert (RA24 : ov_read_bytes rsegs (normalize rsegs mem) (wa (fsp g + 250)) 2 = Some (le2 (Z_to_bv 64 (minor idb)))).
  { apply (sb2_bytes_at_rd2 rsegs _ (spk g 226) idb 24 _ AGn); [lia | unfold spk; lia]. }
  assert (RI24 : ov_read_bytes rsegs (normalize rsegs mem) (wa (fsp g + 154)) 2 = Some (le2 (Z_to_bv 64 (minor idb)))).
  { apply (sb2_bytes_at_rd2 rsegs _ (spk g 130) idb 24 _ IDn); [lia | unfold spk; lia]. }
  assert (RA26 : ov_read_bytes rsegs (normalize rsegs mem) (wa (fsp g + 252)) 2 = Some (le2 (Z_to_bv 64 (patch idb)))).
  { apply (sb2_bytes_at_rd2 rsegs _ (spk g 226) idb 26 _ AGn); [lia | unfold spk; lia]. }
  assert (RI26 : ov_read_bytes rsegs (normalize rsegs mem) (wa (fsp g + 156)) 2 = Some (le2 (Z_to_bv 64 (patch idb)))).
  { apply (sb2_bytes_at_rd2 rsegs _ (spk g 130) idb 26 _ IDn); [lia | unfold spk; lia]. }
  set (rw := firstn 8 (skipn 28 idb)).
  assert (NA : bytes_at rsegs (normalize rsegs mem) (bv_unsigned (Z_to_bv 64 (fsp g + 254))) rw).
  { rewrite MState.unsigned_lit by lia. replace (fsp g + 254) with (spk g 226 + Z.of_nat 28) by (unfold spk; lia).
    apply sb2_bytes_at_sub; [exact AGn | lia]. }
  assert (NI : bytes_at rsegs (normalize rsegs mem) (bv_unsigned (Z_to_bv 64 (fsp g + 158))) rw).
  { rewrite MState.unsigned_lit by lia. replace (fsp g + 158) with (spk g 130 + Z.of_nat 28) by (unfold spk; lia).
    apply sb2_bytes_at_sub; [exact IDn | lia]. }
  assert (MC : StrFun.memcmp_model rw rw (Z.to_nat (bv_unsigned (Z_to_bv 64 8))) = Some 0).
  { rewrite MState.unsigned_lit by lia. apply sb2_memcmp_refl. unfold rw. rewrite length_firstn, length_skipn. lia. }
  pose proof (sb2_le16_range (nthb idb 22) (nthb idb 23)) as R22.
  pose proof (sb2_le16_range (nthb idb 24) (nthb idb 25)) as R24.
  pose proof (sb2_le16_range (nthb idb 26) (nthb idb 27)) as R26.
  assert (G10 : reg_get regs 10 = Z_to_bv 64 0) by exact H10.
  eapply (sb2_seg_run_norm B APIf ra empty FF regs 0x13144 mem md _
    (fun R pc' m0 => pc' = 0x13188 /\
       sb2_agree regs R [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 27] /\
       getr R 18 = Z_to_bv 64 (has_model_name idb) /\ getr R 24 = Z_to_bv 64 (major idb) /\
       getr R 25 = Z_to_bv 64 (minor idb) /\ getr R 26 = Z_to_bv 64 (patch idb) /\
       getr R 10 = Z_to_bv 64 0 /\ munch [] (normalize rsegs mem) m0) HRO Hh Hlz).
  - unfold Regs6ss.mkR_of. rewrite G2, G10.
    step. sb2_br false idtac.
    step. step. step. sb2_br false idtac.
    step. step. rewrite sb2_zx16 by (unfold major; exact R22). step. sb2_br false idtac.
    step. step. rewrite sb2_zx16 by (unfold minor; exact R24). step. sb2_br false idtac.
    step. step. rewrite sb2_zx16 by (unfold patch; exact R26). step. sb2_br false idtac.
    step. step. step. step.
    eapply evt_cut; [eapply (BC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rw rw 0); [exact NA | exact NI | exact MC | apply mem_inv_normalize] |].
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                MU & _ & _ & _ & _).
    rewrite (ret_pc_even 0x13188) by first [lia | reflexivity].
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    split; [intros k Hk; cbn [In] in Hk; repeat destruct Hk as [<-|Hk]; try contradiction;
            first [reflexivity | rewrite <- G2; reflexivity]|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. exact MU.
  - intros R R' pc' m0 m' (-> & AG & H18 & H24 & H25' & H26 & H10' & MU) XR MREL ROS.
    assert (AG' : sb2_agree regs R' [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 27])
      by (apply (sb2_agree_eqv regs R R' _ AG XR); intros k Hk; cbn [In] in Hk;
          repeat destruct Hk as [<-|Hk]; try contradiction; lia).
    pose proof (mem_rel_normalize rsegs mem HRO) as MR0.
    pose proof (munch_rel rsegs [] mem (normalize rsegs mem) m' m0 MR0 MREL ROS MU) as MU'.
    assert (K : sb2_keep mem m' (fsp g + 168) (fsp g + 168)) by (intros x _; apply MU'; exact I).
    assert (WIN : sb2_win g (fsp g + 168) (fsp g + 168)) by (left; unfold spk; lia).
    pose proof HB03 as ((HREC & H23 & H21 & H20) & H26o & H22 & HPLB).
    apply H. exists pl, L, A, R', m', md. split; [reflexivity|].
    split; [apply (sb2_FR_mem B APIf ra empty FF g _ _ L A regs mem md R' m' (fsp g + 168) (fsp g + 168)
                     HFR HPERM); [unfold SLOT_K, SLOT_STACK; lia | lia | exact K |
                                  apply sb2_wmono_eq; intros x; apply MU'; exact I |
                                  apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto]|].
    split; [exact HPERM|].
    split.
    { split; [apply (sb2_REC_mem g i R' mem m' _ _ (sb2_REC g i regs R' mem HREC
                ltac:(apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto)) K WIN)|].
      split; [sb2_ag AG' 21; exact H21|]. split; [sb2_ag AG' 20; exact H20|]. split; [sb2_ag AG' 22; exact H22|].
      split; [exact (sb2_PLB_mem g i pl mem m' _ _ HPLB K ltac:(lia))|].
      split; [exact (sb2_ID_mem g (S i) 130 mem m' _ _ HID K WIN ltac:(lia))|].
      split; [exact (sb2_ID_mem g (S i) 226 mem m' _ _ HAGN K WIN ltac:(lia))|].
      split; [exact (sb2_ID_mem g i 48 mem m' _ _ HBEF K WIN ltac:(lia))|].
      exact (sb2_LPm_mem g i mem m' _ _ HLPm K WIN). }
    split; [unfold S7A; sb2_ag AG' 23; exact H23|].
    split.
    { unfold FALL, F11, F0, F2, F8, F9, F10, idS. fold idb. unfold F11, F0, idS in HF11, HF0. fold idb in HF11, HF0.
      split; [sb2_ag AG' 27; exact HF11|]. split; [sb2_ag AG' 8; exact HF0|].
      rewrite !(sb2_getr_x R R' _ XR) by reflexivity.
      split; [exact H18|]. split; [exact H24|]. split; [exact H25'|]. exact H26. }
    split; [apply (sb2_RRr g i regs R' HRR); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
    rewrite (sb2_getr_x R R' _ XR) by reflexivity. exact H10'.
Qed.

End Seg.
