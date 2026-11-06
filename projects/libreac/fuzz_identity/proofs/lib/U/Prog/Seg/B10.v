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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab2.
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

Section Seg.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis BC : bcmp_c.bcmp_contract.

Lemma seg_B10 : forall i,
  Hrec B APIf ra (Inv_U131ec_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U131b8_at B APIf ra empty) i.
Proof.
  intros i H g c (pl & L & A & regs & mem & md & -> & HFR & HPERM & HP).
  destruct HP as (HB03 & HLPm & HID & HBEF & HRR & HAGN & H25).
  destruct (sb2_FR_basics B APIf ra empty FF g _ _ L A regs mem md HFR)
    as (HAC & HSK & HS47 & HSm & Efsp & G2 & HSTK & HRO & Hh & Hlz & HMR).
  pose proof (sb2_pl_low B APIf g i pl L A mem md _ HMR HPERM) as PLO.
  set (idb := rec_id (g_in g) (S i)) in *.
  assert (LID : length idb = 38%nat) by (unfold idb; rewrite rec_id_length; reflexivity).
  unfold IDb, AGN in HID, HAGN. fold idb in HID, HAGN.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HID) as IDn.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HAGN) as AGn.
  assert (RA0 : ov_read_bytes rsegs (normalize rsegs mem) (wa (fsp g + 242)) 2 =
                Some (le2 (Z_to_bv 64 (fw_milli idb)))).
  { apply (sb2_bytes_at_rd2 rsegs _ (spk g 242) idb 0 _ AGn); [lia | unfold spk; lia]. }
  assert (RI0 : ov_read_bytes rsegs (normalize rsegs mem) (wa (fsp g + 146)) 2 =
                Some (le2 (Z_to_bv 64 (fw_milli idb)))).
  { apply (sb2_bytes_at_rd2 rsegs _ (spk g 146) idb 0 _ IDn); [lia | unfold spk; lia]. }
  assert (RA2 : ov_read_bytes rsegs (normalize rsegs mem) (wa (fsp g + 244)) 1 = Some [nth 2 idb (zb 0)]).
  { apply (sb2_bytes_at_rd1' rsegs _ (spk g 242) idb 2 _ AGn); [lia | unfold spk; lia]. }
  assert (RI2 : ov_read_bytes rsegs (normalize rsegs mem) (wa (fsp g + 148)) 1 = Some [nth 2 idb (zb 0)]).
  { apply (sb2_bytes_at_rd1' rsegs _ (spk g 146) idb 2 _ IDn); [lia | unfold spk; lia]. }
  set (nm := firstn 17 (skipn 3 idb)).
  assert (NA : bytes_at rsegs (normalize rsegs mem) (bv_unsigned (Z_to_bv 64 (fsp g + 245))) nm).
  { rewrite MState.unsigned_lit by lia. replace (fsp g + 245) with (spk g 242 + Z.of_nat 3) by (unfold spk; lia).
    apply sb2_bytes_at_sub; [exact AGn | lia]. }
  assert (NI : bytes_at rsegs (normalize rsegs mem) (bv_unsigned (Z_to_bv 64 (fsp g + 149))) nm).
  { rewrite MState.unsigned_lit by lia. replace (fsp g + 149) with (spk g 146 + Z.of_nat 3) by (unfold spk; lia).
    apply sb2_bytes_at_sub; [exact IDn | lia]. }
  assert (MC : StrFun.memcmp_model nm nm (Z.to_nat (bv_unsigned (Z_to_bv 64 17))) = Some 0).
  { rewrite MState.unsigned_lit by lia. apply sb2_memcmp_refl. unfold nm. rewrite length_firstn, length_skipn. lia. }
  pose proof (sb2_le16_range (nthb idb 0) (nthb idb 1)) as FWR.
  assert (G25 : reg_get regs 25 = Z_to_bv 64 (rec_r (g_in g) i)) by exact H25.
  assert (G24 : reg_get regs 24 = Z_to_bv 64 (rec_r (g_in g) i)) by exact HRR.
  eapply (sb2_seg_run_norm B APIf ra empty FF regs 0x131b8 mem md _
    (fun R pc' m0 => pc' = 0x131ec /\
       sb2_agree regs R [2; 3; 4; 9; 20; 21; 22; 24; 25; 26] /\
       getr R 23 = Z_to_bv 64 (fw_milli idb) /\ getr R 18 = Z_to_bv 64 (has_fw idb) /\
       getr R 10 = Z_to_bv 64 0 /\ munch [] (normalize rsegs mem) m0) HRO Hh Hlz).
  - unfold Regs6ss.mkR_of. rewrite G2, G25, G24.
    step. sb2_br true idtac.
    step. step. rewrite sb2_zx16 by (unfold fw_milli; exact FWR).
    step. sb2_br true idtac.
    step. step. step. sb2_br false idtac.
    step. step. step. step.
    eapply evt_cut; [eapply (BC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ nm nm 0); [exact NA | exact NI | exact MC | apply mem_inv_normalize] |].
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                MU & _ & _ & _ & _).
    rewrite (ret_pc_even 0x131ec) by first [lia | reflexivity].
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    split; [intros k Hk; cbn [In] in Hk; repeat destruct Hk as [<-|Hk]; try contradiction;
            first [reflexivity | rewrite <- G2; reflexivity | rewrite <- G25; reflexivity |
                   rewrite <- G24; reflexivity]|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact MU.
  - intros R R' pc' m0 m' (-> & AG & H23 & H18 & H10 & MU) XR MREL ROS.
    assert (AG' : sb2_agree regs R' [2; 3; 4; 9; 20; 21; 22; 24; 25; 26])
      by (apply (sb2_agree_eqv regs R R' _ AG XR); intros k Hk; cbn [In] in Hk;
          repeat destruct Hk as [<-|Hk]; try contradiction; lia).
    pose proof (mem_rel_normalize rsegs mem HRO) as MR0.
    pose proof (munch_rel rsegs [] mem (normalize rsegs mem) m' m0 MR0 MREL ROS MU) as MU'.
    assert (K : sb2_keep mem m' (fsp g + 184) (fsp g + 184)) by (intros x _; apply MU'; exact I).
    assert (WIN : sb2_win g (fsp g + 184) (fsp g + 184)) by (left; unfold spk; lia).
    apply H. exists pl, L, A, R', m', md. split; [reflexivity|].
    split; [apply (sb2_FR_mem B APIf ra empty FF g _ _ L A regs mem md R' m' (fsp g + 184) (fsp g + 184)
                     HFR HPERM); [unfold SLOT_K, SLOT_STACK; lia | lia | exact K |
                                  apply sb2_wmono_eq; intros x; apply MU'; exact I |
                                  apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto]|].
    split; [exact HPERM|].
    split; [apply (sb2_B03_mem g i pl R' mem m' _ _ (sb2_B03 g i pl regs R' mem HB03
              ltac:(apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto)) K WIN); lia|].
    split; [exact (sb2_LPm_mem g i mem m' _ _ HLPm K WIN)|].
    split; [exact (sb2_ID_mem g (S i) 146 mem m' _ _ HID K WIN ltac:(lia))|].
    split; [exact (sb2_ID_mem g i 64 mem m' _ _ HBEF K WIN ltac:(lia))|].
    split; [apply (sb2_RRr g i regs R' HRR); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
    split; [exact (sb2_ID_mem g (S i) 242 mem m' _ _ HAGN K WIN ltac:(lia))|].
    split; [sb2_ag AG' 25; exact H25|].
    split; [unfold F7, idS; fold idb; rewrite (sb2_getr_x R R' _ XR) by reflexivity; exact H23|].
    split; [unfold F2, idS; fold idb; rewrite (sb2_getr_x R R' _ XR) by reflexivity; exact H18|].
    rewrite (sb2_getr_x R R' _ XR) by reflexivity. exact H10.
Qed.

End Seg.
