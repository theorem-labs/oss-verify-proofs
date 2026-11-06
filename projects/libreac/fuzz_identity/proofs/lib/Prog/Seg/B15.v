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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_identity_fw_str_c check_str_c.
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
Hypothesis CHK : check_str_c.check_str_contract.

Lemma seg_B15 : forall i,
  Hrec B APIf ra (Inv_K13230_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13220_at B APIf ra empty) i.
Proof.
  intros i H g c (pl & L & A & regs & mem & md & -> & HFR & HPERM & HP).
  destruct HP as (HRB & HS7 & HFALL & HRR & HFWA & HV & H10 & HS).
  destruct (sb2_FR_basics B APIf ra empty FF g _ _ L A regs mem md HFR)
    as (HAC & HSK & HS47 & HSm & Efsp & G2 & HSTK & HRO & Hh & Hlz & HMR).
  pose proof (sb2_pl_low B APIf g i pl L A mem md _ HMR HPERM) as PLO.
  set (v := RcIdentModel.fw_milli (idS g i)) in *.
  assert (V0 : 0 <= v) by (unfold v, RcIdentModel.fw_milli, bz; pose proof (bv_unsigned_in_range 8 (nthb (idS g i) 0));
                           pose proof (bv_unsigned_in_range 8 (nthb (idS g i) 1)); lia).
  destruct (reac_identity_fw_str_c.reac_identity_fw_str_c3_len v ltac:(lia)) as [_ EL].
  destruct (Z.ltb_spec v 10000) as [LT|LT]; [|lia].
  assert (LFW : length (reac_identity_fw_str_c.FW v) = 5%nat).
  { pose proof EL as EL'. unfold reac_identity_fw_str_c.L in EL'. lia. }
  assert (NZ : ~ In (Z_to_bv 8 0) (reac_identity_fw_str_c.FW v)).
  { intros Hin. apply (reac_identity_fw_str_c.reac_identity_fw_str_c3_nz v ltac:(lia) _ Hin). reflexivity. }
  destruct HSTK as (S1 & S2 & S3).
  destruct (S3 (fsp g + 182) ltac:(lia)) as [_ [b6 E6]].
  destruct (S3 (fsp g + 183) ltac:(lia)) as [_ [b7 E7]].
  assert (HSL : bytes_at rsegs mem (fsp g + 182) [b6; b7]).
  { split; [lia|]. split; [cbn [length]; lia|]. intros j Hj. destruct j as [|[|j]]; cbn [nth_error].
    - replace (fsp g + 182 + Z.of_nat 0) with (fsp g + 182) by lia. exact E6.
    - replace (fsp g + 182 + Z.of_nat 1) with (fsp g + 183) by lia. exact E7.
    - cbn [length] in Hj. lia. }
  assert (HALL : bytes_at rsegs mem (fsp g + 176) (reac_identity_fw_str_c.FW v ++ Z_to_bv 8 0 :: [b6; b7])).
  { unfold cstr in HS. replace (reac_identity_fw_str_c.FW v ++ Z_to_bv 8 0 :: [b6; b7])
      with ((reac_identity_fw_str_c.FW v ++ [z8]) ++ [b6; b7]) by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact HS|].
    rewrite length_app, LFW. cbn [length]. replace (fsp g + 176 + Z.of_nat (5 + 1)) with (fsp g + 182) by lia. exact HSL. }
  assert (G10 : reg_get regs 10 = Z_to_bv 64 5) by exact H10.
  eapply (sb2_seg_run_norm B APIf ra empty FF regs 0x13220 mem md _
    (fun R pc' m0 => pc' = 0x13230 /\
       sb2_agree regs R [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] /\
       getr R 9 = Z_to_bv 64 5 /\ munch [(fsp g - 16, fsp g)] (normalize rsegs mem) m0 /\
       wmono rsegs (normalize rsegs mem) m0) HRO Hh Hlz).
  - unfold Regs6ss.mkR_of. rewrite G2, G10.
    step. step. step. step.
    eapply evt_cut;
      [eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 5 (fsp g + 176) 8
                 (g_S g - 65536) (reac_identity_fw_str_c.FW v) [b6; b7]);
         [lia | reflexivity | lia | reflexivity | lia | reflexivity | | | | ] |].
    + intros _. split; [lia|]. split; [rewrite LFW; reflexivity|].
      split; [apply bytes_at_normalize; [exact HRO | exact HALL]|].
      split; [exact NZ|]. split; [cbn [length]; Z.div_mod_to_equations; lia|].
      right. rewrite MState.unsigned_lit by lia. lia.
    + rewrite MState.unsigned_lit by lia. apply sb2_stk_norm; [|lia].
      apply (sb2_stk_sub rsegs mem (g_S g - 65536) (g_S g)); [split; [exact S1 | split; [exact S2 | exact S3]] | lia | lia | lia].
    + unfold check_str_c.CHECK_STR_FRAME. rewrite MState.unsigned_lit by lia. lia.
    + apply mem_inv_normalize.
    + intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                  MU & WM & _ & _).
      rewrite (ret_pc_even 0x13230) by first [lia | reflexivity].
      apply evt_done. do 3 eexists. split; [reflexivity|].
      split; [reflexivity|].
      split; [intros k Hk; cbn [In] in Hk; repeat destruct Hk as [<-|Hk]; try contradiction;
              first [reflexivity | rewrite <- G2; reflexivity]|].
      split; [reflexivity|].
      rewrite MState.unsigned_lit in MU by lia.
      split; [exact MU | exact WM].
  - intros R R' pc' m0 m' (-> & AG & H9' & MU & WM) XR MREL ROS.
    assert (AG' : sb2_agree regs R' [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27])
      by (apply (sb2_agree_eqv regs R R' _ AG XR); intros k Hk; cbn [In] in Hk;
          repeat destruct Hk as [<-|Hk]; try contradiction; lia).
    pose proof (mem_rel_normalize rsegs mem HRO) as MR0.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' m0 MR0 MREL ROS MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' m0 MR0 MREL ROS WM) as WM'.
    assert (K : sb2_keep mem m' (fsp g - 16) (fsp g))
      by (intros x Hx; apply MU'; cbn [outside]; split; [exact Hx | exact I]).
    apply H. exists pl, L, A, R', m', md. split; [reflexivity|].
    split; [apply (sb2_FR_mem B APIf ra empty FF g _ _ L A regs mem md R' m' (fsp g - 16) (fsp g)
                     HFR HPERM); [unfold SLOT_K, SLOT_STACK; lia | lia | exact K | exact WM' |
                                  apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto]|].
    split; [exact HPERM|].
    split.
    { apply (sb2_RB12_mem g i pl R' mem m' (fsp g - 16) (fsp g)).
      - apply (sb2_RB12 g i pl regs R' mem HRB). apply (sb2_agree_sub regs R' _ _ AG'). cbn [In]. tauto.
      - exact K.
      - right. unfold spk. lia.
      - lia. }
    split; [apply (sb2_S7A g i regs R' HS7); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
    split; [apply (sb2_FALL g i regs R' HFALL); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
    split; [rewrite (sb2_getr_x R R' _ XR) by reflexivity; exact H9'|].
    split; [exact HFWA|].
    split; [exact HV|].
    apply (sb2_bytes_at_keep rsegs mem m' (fsp g - 16) (fsp g) _ _ HS K). left. unfold spk. lia.
Qed.

End Seg.
