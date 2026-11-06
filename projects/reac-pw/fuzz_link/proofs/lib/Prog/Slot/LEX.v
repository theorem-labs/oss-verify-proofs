(* The slot's EXIT (arm `en`, prefix LE): the three segments of 0x1413c .. 0x14188.

     EXa  0x1413c  mv a0, s7 ; jal free            -> the cut at free (marks), ra 0x14144
     EXb  0x14144  mv a0, s0 ; jal free            -> the cut at free (m),     ra 0x1414c
     EXc  0x1414c  mv a0, zero ; the 13 reloads ; addi sp, sp, 0x1e0 ; ret

   Neither segment writes memory, so each post carries `seg_fp (e_S E) hp m m` for every hp
   (LDefs' seg_fp, with the empty window). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr Image FP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LEDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the 104 saved bytes, read as the 13 words the epilogue reloads *)
Lemma saved_cells : forall m A (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
  bytes_at rsegs m A (saved_bytes ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  ro_cells rsegs m A [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2;
                      C8 s1; C8 s0; C8 ra].
Proof.
  intros m A ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H.
  split; [cbn [cells_wf cell_wf]; repeat split; exact I|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
Qed.

Lemma lr_cells : forall m A (R : lregs),
  bytes_at rsegs m A (lr_bytes R) ->
  ro_cells rsegs m A [C8 (r_s11 R); C8 (r_s10 R); C8 (r_s9 R); C8 (r_s8 R); C8 (r_s7 R);
                      C8 (r_s6 R); C8 (r_s5 R); C8 (r_s4 R); C8 (r_s3 R); C8 (r_s2 R);
                      C8 (r_s1 R); C8 (r_s0 R); C8 (r_ra R)].
Proof. intros m A R H. apply saved_cells. exact H. Qed.

(* ==========================================================================
   EXa: 0x1413c -> the call free (marks)
   ========================================================================== *)

Lemma le_EXa : forall (E : lenv) (R : lregs) (gp : word) (ms : machine_state),
  e_saved E = lr_bytes R ->
  wr_at rsegs (ms_mem ms) (e_S E - 104) 104 ->
  ex_ms E gp ms ->
  evt rsegs (fun ms' => le_free1 (e_S E) gp R (e_md E) (e_mk E) ms' /\
                        forall hp, seg_fp (e_S E) hp (ms_mem ms) (ms_mem ms')) ms.
Proof.
  intros E R gp ms HSV HW HX.
  destruct HX as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s1 & s2 & s3 & s4 & s5
    & s6 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & j & EQ & FC & FRc & SB & ER & GD
    & LA & MI & TM & ST).
  subst ms. cbn [ms_mem] in HW |- *.
  rewrite HSV in SB.
  unfold wz, L_EXIT. do 2 step.
  apply evt_done. split.
  - unfold le_free1. do 25 eexists. exists F, fc, m.
    split; [reflexivity|]. split; [exact FC|].
    unfold le_tail_mem. split; [exists j; exact FRc|]. split; [exact SB|]. split; [exact HW|].
    split; [exact ER|]. split; [exact GD|]. split; [exact LA|].
    split; [exact MI|]. split; [exact TM|]. exact ST.
  - intros hp. apply seg_fp_nil.
Qed.

(* ==========================================================================
   EXb: 0x14144 -> the call free (m)
   ========================================================================== *)

Lemma le_EXb : forall (S md : Z) (R : lregs) (gp : word) (ms : machine_state),
  le_free1r S gp R md ms ->
  evt rsegs (fun ms' => le_free2 S gp R md ms' /\
                        forall hp, seg_fp S hp (ms_mem ms) (ms_mem ms')) ms.
Proof.
  intros S md R gp ms HC.
  destruct HC as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s1 & s2 & s3 & s4 & s5
    & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & EQ & FC & TM).
  subst ms. cbn [ms_mem] in TM |- *.
  unfold wz, L_FREE1_RA. do 2 step.
  apply evt_done. split.
  - unfold le_free2. do 26 eexists. exists F, fc, m.
    split; [reflexivity|]. split; [exact FC|]. exact TM.
  - intros hp. apply seg_fp_nil.
Qed.

(* ==========================================================================
   EXc: 0x1414c -> the slot's ret
   ========================================================================== *)

Lemma le_EXc : forall (S : Z) (R : lregs) (gp : word) (ms : machine_state),
  0x960e0 + SLOT_STACK_Z <= S -> S <= 2 ^ 47 ->
  le_free2r S gp R ms ->
  evt rsegs (fun ms' => le_fin S gp R ms' /\
                        forall hp, seg_fp S hp (ms_mem ms) (ms_mem ms')) ms.
Proof.
  intros S R gp ms HS1 HS2 HC.
  destruct HC as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s0 & s1 & s2 & s3 & s4
    & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & EQ & FC & TM).
  subst ms. cbn [ms_mem] in TM |- *.
  destruct TM as ((j & FRc) & SB & HW & ER & GD & LA & MI & TMEM & ST).
  pose proof (lr_cells m (S - 104) R SB) as SC.
  replace (S - 104) with (S - SLOT_FRAME + 376) in SC by (unfold SLOT_FRAME; lia).
  pose proof (stk_release rsegs m (S - SLOT_STACK_Z) (S - SLOT_FRAME) [CB 376 j] ST FRc
                ltac:(unfold SLOT_STACK_Z, SLOT_FRAME; lia)) as ST1.
  cbn [cells_size csize] in ST1.
  assert (STsv : stk rsegs m (S - 104) S).
  { split; [unfold SLOT_STACK_Z in HS1; lia|]. split; [lia|].
    intros a Ha. split.
    - destruct HW as (_ & _ & HWa). specialize (HWa (a - (S - 104)) ltac:(lia)).
      replace (S - 104 + (a - (S - 104))) with a in HWa by lia. exact HWa.
    - destruct SB as (_ & HL & HB).
      assert (HI : (Z.to_nat (a - (S - 104)) < length (lr_bytes R))%nat).
      { unfold lr_bytes, saved_bytes. rewrite !app_length, !length_le8. lia. }
      specialize (HB (Z.to_nat (a - (S - 104))) HI).
      replace (S - 104 + Z.of_nat (Z.to_nat (a - (S - 104)))) with a in HB by lia.
      destruct (nth_error (lr_bytes R) (Z.to_nat (a - (S - 104)))) as [b|] eqn:EN.
      + exists b. exact HB.
      + exfalso. apply nth_error_None in EN. lia. }
  pose proof (stk_merge rsegs m (S - SLOT_STACK_Z) (S - 104) S
                ltac:(replace (S - 104) with (S - SLOT_FRAME + 376) by (unfold SLOT_FRAME; lia); exact ST1)
                STsv ltac:(unfold SLOT_STACK_Z; lia)) as STall.
  unfold wz, L_FREE2_RA. do 16 step.
  replace (S - SLOT_FRAME + 480) with S by (unfold SLOT_FRAME; lia).
  apply evt_done. split.
  - unfold le_fin. do 14 eexists. exists F, fc, m.
    split; [reflexivity|]. split; [exact FC|]. split; [exact ER|]. split; [exact GD|].
    split; [exact LA|]. split; [exact MI|]. split; [exact TMEM|]. exact STall.
  - intros hp. apply seg_fp_nil.
Qed.
