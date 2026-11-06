(* Segment B2 of the op_write arm, last part: 0x14044 (the refusal test is over) to the call of
   free(own) at 0x1405c, over check_write (0x15d58) and check_requests (0x15284). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Frame Step Tac Bytes Arr Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  link_mem check_write_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import
  LDefs LC1Defs LC1Call LC1B2Lib LC1B2Tab LC1B2Rc LC1B2St.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Reading an `mkR` register file
   ========================================================================== *)

Section MkR.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Let R := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Lemma c1b2_g10 : getr R 10 = a0. Proof. reflexivity. Qed.
Lemma c1b2_g11 : getr R 11 = a1. Proof. reflexivity. Qed.
Lemma c1b2_arg0 : arg R 0 = bv_unsigned a0. Proof. reflexivity. Qed.
Lemma c1b2_arg1 : arg R 1 = bv_unsigned a1. Proof. reflexivity. Qed.
Lemma c1b2_spZ : spZ R = bv_unsigned sp. Proof. reflexivity. Qed.
Lemma c1b2_errno : errno_at R = bv_unsigned tp + ERRNO_TP_OFF. Proof. reflexivity. Qed.
End MkR.

(* ==========================================================================
   2. A one-interval or three-interval footprint
   ========================================================================== *)

Lemma c1b2_inside1 : forall a b x, ~ outside [(a, b)] x -> a <= x < b.
Proof.
  intros a b x H. destruct (classic (a <= x < b)) as [K|K]; [exact K|].
  exfalso. apply H. cbn [outside]. split; [exact K | exact I].
Qed.

Lemma c1b2_inside3 : forall a b c d e f x, ~ outside [(a, b); (c, d); (e, f)] x ->
  (a <= x < b) \/ (c <= x < d) \/ (e <= x < f).
Proof.
  intros a b c d e f x H.
  destruct (classic (a <= x < b)) as [K1|K1]; [left; exact K1|].
  destruct (classic (c <= x < d)) as [K2|K2]; [right; left; exact K2|].
  destruct (classic (e <= x < f)) as [K3|K3]; [right; right; exact K3|].
  exfalso. apply H. cbn [outside]. repeat split; assumption.
Qed.

(* ==========================================================================
   3. The walk
   ========================================================================== *)

Section B2Tail.

Hypothesis CHECK_WRITE_OK : check_write_contract.
Hypothesis CHECK_REQUESTS_OK : check_requests_contract.

Lemma c1b2_tail : forall E i gp own nb rm op0 s rl (t sl : list byte) m0 ms,
  lenv_ok E -> c1b2_s44 E i gp own nb rm op0 s rl t sl m0 ms ->
  evt rsegs (eqv_cl (c1b2_post E i gp own m0)) ms.
Proof.
  intros E i gp own nb rm op0 s rl t sl m0 ms HE HS.
  destruct HS as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6
                  & F & fc & m & P & N & kbs & mbs & gbs & -> & FRM & Hi & HNn & HRM & HRL & HRQ & CAR).
  assert (SB : 0x960e0 + 65536 <= e_S E <= 2 ^ 47)
    by (unfold lenv_ok, SLOT_STACK_Z in HE; lia).
  assert (BMD : blk_out (e_S E) (e_md E) MD_SIZE).
  { unfold lenv_ok in HE. destruct HE as (_ & _ & _ & X & _). exact X. }
  assert (MDH : e_md E + 8856 <= e_S E - 65536).
  { pose proof (c1b2_blk_hi _ _ _ BMD) as H. unfold MD_SIZE, SLOT_STACK_Z in H. lia. }
  assert (MDL : 4096 <= e_md E) by exact (c1b2_blk_lo0 _ _ _ BMD).
  assert (MDG : e_md E + 8856 <= 203648 \/ 475640 <= e_md E).
  { pose proof c1b2_pages_ge as PG. destruct BMD as (B1 & B2 & BF).
    destruct (c1b2_img_free_bound (e_md E) MD_SIZE ltac:(lia) ltac:(unfold MD_SIZE; lia) BF) as [H|H].
    - left. unfold MD_SIZE in H. lia.
    - right. lia. }
  assert (USP : bv_unsigned (Z_to_bv 64 (e_S E - SLOT_FRAME)) = e_S E - SLOT_FRAME)
    by (apply unsigned_lit; unfold SLOT_FRAME; lia).
  assert (REST : c1b2_rest E P N mbs gbs m)
    by (unfold c1b2_car in CAR; destruct CAR as (X & _); exact X).
  assert (NL : c1b2_nl (i + 1) kbs m)
    by (unfold c1b2_car in CAR; destruct CAR as (_ & X & _); exact X).
  assert (MI : mem_inv rsegs m)
    by (unfold c1b2_car in CAR; destruct CAR as (_ & _ & _ & _ & _ & X & _); exact X).
  assert (ST : stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME))
    by (unfold c1b2_car in CAR; destruct CAR as (_ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (HK : nlk_at m kbs) by (unfold c1b2_nl in NL; destruct NL as (X & _); exact X).
  assert (HKW : nlk_wf kbs) by (unfold c1b2_nl in NL; destruct NL as (_ & X & _); exact X).
  assert (HM : model_at m (e_md E) mbs).
  { unfold c1b2_rest in REST.
    destruct REST as (_ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  assert (HMW : model_wf mbs).
  { unfold c1b2_rest in REST.
    destruct REST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  unfold wz.
  do 3 step.
  (* ---- check_write ---- *)
  eapply leaf_call_eqv.
  { exact CHECK_WRITE_OK. }
  { unfold same_rc_regs. rewrite c1b2_g10, c1b2_g11.
    destruct (c1b2_same_rc_vals rl HRL) as [W1 W2]. unfold wz in W1, W2.
    rewrite HRM. split; [exact W1 | exact W2]. }
  { exact MI. }
  { rewrite USP. exact ST. }
  { rewrite USP. unfold SLOT_STACK_Z, SLOT_FRAME. lia. }
  { rewrite USP. unfold SLOT_FRAME. lia. }
  intros ra1 t01 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 m1
         (regs1 & HR1 & HP1) MU1 WM1 MI1 ST1.
  unfold unchanged in HP1. subst m1.
  rewrite (ret_pc_even 82000 ltac:(lia) ltac:(reflexivity)).
  do 2 step.
  (* ---- check_requests ---- *)
  eapply leaf_call_eqv.
  { exact CHECK_REQUESTS_OK. }
  { exists kbs, mbs. rewrite c1b2_arg0.
    rewrite (unsigned_lit (e_md E)) by lia.
    unfold frame_apart_gnl, apart_frame, apart_gnl. rewrite c1b2_spZ, USP.
    split; [exact HK|].
    split; [unfold A_G_NL, NK_SIZE, SLOT_FRAME; lia|].
    split; [exact HM|].
    split; [exact HKW|].
    split; [exact HMW|].
    split; [exact HRQ|].
    split; [unfold MD_SIZE, SLOT_FRAME; lia|].
    destruct MDG as [G|G]; unfold A_G_NL, NK_SIZE, MD_SIZE; lia. }
  { exact MI. }
  { rewrite USP. exact ST. }
  { rewrite USP. unfold SLOT_STACK_Z, SLOT_FRAME. lia. }
  { rewrite USP. unfold SLOT_FRAME. lia. }
  intros ra2 t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 t32 t42 t52 t62 m2
         (regs2 & HR2 & HP2) MU2 WM2 MI2 ST2.
  unfold writes_nothing in MU2. rewrite USP in MU2, ST2.
  assert (CAR2 : c1b2_car E i own s t sl P N kbs mbs gbs m0 m2).
  { eapply c1b2_car_keep with (W := [(e_S E - SLOT_FRAME - 48, e_S E - SLOT_FRAME)]);
      [exact HE | exact CAR | exact MU2 | exact WM2 | exact MI2 | exact ST2 |].
    intros x Hx. apply c1b2_inside1 in Hx. unfold SLOT_STACK_Z, SLOT_FRAME in *. lia. }
  assert (REST2 : c1b2_rest E P N mbs gbs m2)
    by (unfold c1b2_car in CAR2; destruct CAR2 as (X & _); exact X).
  assert (NL2 : c1b2_nl (i + 1) kbs m2)
    by (unfold c1b2_car in CAR2; destruct CAR2 as (_ & X & _); exact X).
  assert (CELLS2 : rw_cells rsegs m2 (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)])
    by (unfold c1b2_car in CAR2; destruct CAR2 as (_ & _ & X & _); exact X).
  assert (OWN2 : bytes_at rsegs m2 (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)))
    by (unfold c1b2_car in CAR2; destruct CAR2 as (_ & _ & _ & X & _); exact X).
  assert (MI2' : mem_inv rsegs m2)
    by (unfold c1b2_car in CAR2; destruct CAR2 as (_ & _ & _ & _ & _ & X & _); exact X).
  assert (TM2 : MemNorm.task_mem rsegs m2)
    by (unfold c1b2_car in CAR2; destruct CAR2 as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (ST2' : stk rsegs m2 (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME))
    by (unfold c1b2_car in CAR2; destruct CAR2 as (_ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (FP2 : seg_fp (e_S E) (c1_hp E) m0 m2)
    by (unfold c1b2_car in CAR2; destruct CAR2 as (_ & _ & _ & _ & _ & _ & _ & _ & X); exact X).
  rewrite (ret_pc_even 82008 ltac:(lia) ltac:(reflexivity)).
  (* ---- ld a0, 0x78(sp); jal free ---- *)
  pose proof (c1b2_read8 m2 (e_S E - SLOT_FRAME + FO_B256) (wz own) OWN2) as HRD.
  unfold FO_B256, SLOT_FRAME in HRD.
  do 2 step.
  apply evt_eqv_done. unfold c1b2_post. split; [|exact FP2].
  unfold c1_173d4. do 19 eexists. exists F, fc, m2, P, N, kbs, mbs, gbs.
  split; [reflexivity|].
  split; [exact FRM|]. split; [lia|]. split; [lia|].
  split; [exact (c1b2_lh_join E (i + 1) P N kbs mbs gbs m2 REST2 NL2)|].
  split; [exact CELLS2|]. split; [exact MI2'|]. split; [exact TM2 | exact ST2'].
Qed.

End B2Tail.
