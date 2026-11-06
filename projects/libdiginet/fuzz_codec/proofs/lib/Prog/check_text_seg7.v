From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells
  diginet_seg7_c owed_seg7_c check_text_seg7_c.
Import ListNotations.
Open Scope Z_scope.

Module CheckSeg7W.

Lemma land255 : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia. Qed.

(* The flag update of 0x14d64-0x14d74 when the two results agree: s2 = ((x != x) - 1) & 1 = 1. *)
Lemma s2_one : forall x,
  Z.land (bv_swrap 32 (Z.b2z (0 <? Z.lxor x x) + -1) mod 18446744073709551616) 1 = 1.
Proof. intros x. rewrite Z.lxor_nilpotent. vm_compute. reflexivity. Qed.

(* A memory that agrees with m outside W keeps the RELRO tables when W does not meet them. *)
Lemma relro_img_munch : forall W m m',
  relro_img m -> munch W m m' -> disjoint_from W RELRO_BASE RELRO_LEN -> relro_img m'.
Proof.
  intros W m m' H Hm Hd i Hi. unfold mrd in *. rewrite Hm.
  - apply H. exact Hi.
  - eapply disjoint_outside; [exact Hd|]. rewrite wa_unsigned; unfold RELRO_BASE, RELRO_LEN in *; lia.
Qed.

Section CS.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
Hypothesis LO : lo + 48 <= bv_unsigned sp.
Hypothesis HRL0 : relro_img m.
Hypothesis DJ : disj lo (bv_unsigned sp - lo) RELRO_BASE RELRO_LEN.
Hypothesis HMI0 : mem_inv rsegs m.
Hypothesis ST0 : stk rsegs m lo (bv_unsigned sp).
Hypothesis AG : forall c, 0 <= c < 256 -> seg7_spec c = owed_seg7_spec c.
Hypothesis SEG7 : diginet_seg7_contract.
Hypothesis OWED : owed_seg7_contract.

Definition saved (j : list byte) : list cell := [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition Qk (ms' : machine_state) : Prop :=
  exists (a0' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp).

(* The epilogue (0x14d7c): s2 = 1, so `beqz s2` does not reach abort; restore and return. *)
Lemma c_exit : forall (ra' s0' s1' a0' a1' a2' a3' a4' a5' a6' : word) (j : list byte) (m1 : word -> option byte),
  rw_cells rsegs m1 (bv_unsigned sp + -48) (saved j) ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0' s1' a0' a1' a2' a3' a4' a5' a6' a7
             (Z_to_bv 64 1) (Z_to_bv 64 256) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14d7c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' s0' s1' a0' a1' a2' a3' a4' a5' a6' j m1 FR ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold saved in FR.
  zstep. if_cases K; [ exfalso; zify_cond K; lia | ].
  do 6 zstep.
  eapply stk_release in FR; [ | exact ST | lia ].
  cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in FR by lia.
  clear ST.
  zstep.
  finish.
Qed.

Definition loop_ok (n : nat) : Prop :=
  forall (ra' s1' a0' a1' a2' a3' a4' a5' a6' : word) (k : Z) (j : list byte) (m1 : word -> option byte),
  Z.of_nat n = 256 - k -> 0 <= k < 256 ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) (saved j) ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> relro_img m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 k) s1' a0' a1' a2' a3' a4' a5' a6' a7
             (Z_to_bv 64 1) (Z_to_bv 64 256) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14d50) fc None m1 (seg_rom rsegs)).

(* One char c = k (0x14d50-0x14d78): diginet_seg7 and owed_seg7 agree, so the flag s2 stays 1. *)
Lemma iter_ok : forall n, loop_ok n -> loop_ok (S n).
Proof.
  intros n LOOP ra' s1' a0' a1' a2' a3' a4' a5' a6' k j m1 Hn Hk FR ST MU WM HMI HRL.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold diginet_seg7_contract, diginet_seg7_pre, DIGINET_SEG7 in SEG7.
  unfold owed_seg7_contract, owed_seg7_pre, OWED_SEG7 in OWED.
  do 2 zstep.
  eapply evt_cut; [ eapply SEG7; exact HMI | ].
  intros ms' [a1x ->].
  replace (ret_pc (Z_to_bv 64 0x14d58)) with (Z_to_bv 64 0x14d58) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  rewrite (land255 k), unsigned_lit, Z.mod_small by lia. rewrite (AG k Hk).
  do 3 zstep.
  eapply evt_cut; [ eapply OWED with (c := k); repeat split; first [ lia | reflexivity | assumption ] | ].
  intros ms' [a1y [a2y [a3y [a4y [a5y [a6y ->]]]]]].
  replace (ret_pc (Z_to_bv 64 0x14d64)) with (Z_to_bv 64 0x14d64) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  do 6 zstep.
  rewrite s2_one.
  rewrite (bv_swrap_small 32 (k + 1)) by (change (bv_half_modulus 32) with 2147483648; lia).
  if_cases K.
  - zify_cond K.
    eapply LOOP with (k := k + 1); try eassumption; lia.
  - zify_cond K.
    eapply c_exit; eassumption.
Qed.

Lemma loop_all : forall n, loop_ok n.
Proof.
  induction n as [|n IH].
  - intros ra' s1' a0' a1' a2' a3' a4' a5' a6' k j m1 Hn Hk. exfalso. cbn in Hn. lia.
  - apply iter_ok. exact IH.
Qed.

(* The prologue (0x14d2c-0x14d4c): the frame of 48 bytes, s0 = 0, s2 = 1, s3 = 256. *)
Lemma c_entry : forall (a0 a1 a2 a3 a4 a5 a6 : word),
  evt rsegs Qk
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14d2c) fc None m (seg_rom rsegs)).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6.
  pose proof HMI0 as HMI. pose proof ST0 as ST. pose proof HRL0 as HRL.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST0 as [Hlo _].
  carve_frame 48%nat ST.
  assert (MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  do 9 zstep.
  match goal with MU' : munch _ m ?m1 |- _ =>
    assert (HRL1 : relro_img m1)
      by (apply (relro_img_munch _ m m1 HRL0 MU'); cbn [disjoint_from]; unfold disj in DJ; lia)
  end.
  eapply (loop_all 256) with (k := 0); try eassumption; lia.
Qed.

End CS.
End CheckSeg7W.

Theorem check_text_seg7_holds : diginet_seg7_contract -> owed_seg7_contract -> check_text_seg7_contract.
Proof.
  intros SEG7 OWED. unfold check_text_seg7_contract, check_text_seg7_pre, CHECK_TEXT_SEG7, CHECK_TEXT_SEG7_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo [HRL [DJ [HMI [ST [LO AG]]]]].
  change (evt rsegs (CheckSeg7W.Qk ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14d2c) fc None m (seg_rom rsegs))).
  eapply CheckSeg7W.c_entry; eassumption.
Qed.
