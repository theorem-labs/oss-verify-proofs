(** ent_build's kind 6 (pod.h:340-348): type t[v % 4] of (LONG, DOUBLE, ID, NONE), size 8, 8, 4, 0, the body the
    next size input bytes (zeros past the end). From the jump table's target 0x137ac to the join 0x13504 (through
    0x139f4 when no byte is left, 0x13b18 / 0x13b1c, and the shared tail 0x13b50 .. 0x13b80 with memcpy at 0x13b78).
    The tail from 0x13b54 is shared with kind 7 (Ent7.v). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleBuild Require Import EntCut EntFacts Ent5.
Import ListNotations.
Open Scope Z_scope.

(** e's bytes after type, size and a body of at most size bytes put over zeros. *)
Lemma ent_fill : forall ty sz bs, (length bs <= Z.to_nat sz)%nat -> (Z.to_nat sz <= 96)%nat ->
  upd_bytes (upd_bytes (upd_bytes (zeros 104) 0 (le32 ty)) 4 (le32 sz)) (Z.to_nat 8) bs
  = ent_mem (Ent ty sz (bs ++ zeros (Z.to_nat sz - length bs))).
Proof.
  intros ty sz bs H1 H2.
  replace (upd_bytes (upd_bytes (zeros 104) 0 (le32 ty)) 4 (le32 sz)) with ((le32 ty ++ le32 sz) ++ zeros 96)
    by reflexivity.
  rewrite (upd_tail (le32 ty ++ le32 sz) 96 bs) by (reflexivity || lia).
  unfold ent_mem. cbn [e_type e_size e_body]. rewrite <- !app_assoc.
  do 3 apply f_equal. rewrite length_app, length_zeros. unfold zeros. rewrite <- repeat_app. f_equal; lia.
Qed.

(** Name the current MemC hypothesis MC. *)
Local Ltac mcname :=
  lazymatch goal with H : MemC _ _ _ _ _ _ _ _ |- _ => let X := fresh "X" in rename H into X; rename X into MC end.

Section Case6.
Variables (sp gp tp s7 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.

Local Abbreviation QE := (QJ sp gp tp s7 s9 F fc m r src pp lo (ent_build r)).
Local Abbreviation S0 := (Z_to_bv 64 (bv_unsigned sp + 0x128)).
Local Abbreviation S1 := (Z_to_bv 64 (bv_unsigned sp + 0xf0)).
Local Abbreviation S2 := (Z_to_bv 64 (0xcccccccd * 2^32)).
Local Abbreviation S8 := (Z_to_bv 64 95).
Local Abbreviation S10 := (Z_to_bv 64 10).

(** 0x13b64: the cursor and the bytes left past c = min(size, left) bytes, memcpy(e.body, src + j, c), to 0x13504. *)
Lemma tail_13b64 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) m1
    (j : nat) (ty sz c : Z),
  (j <= length r)%nat -> 0 <= ty < 2^32 -> 0 <= sz <= 96 -> c = Z.min sz (Z.of_nat (length r) - Z.of_nat j) ->
  ent_build r = (Ent ty sz (firstn (Z.to_nat sz) (skipn j r) ++ zeros (Z.to_nat sz - length (firstn (Z.to_nat sz) (skipn j r)))),
                 skipn (Z.to_nat sz) (skipn j r)) ->
  a0 = Z_to_bv 64 (Z.of_nat (length r) - Z.of_nat j) -> a2 = Z_to_bv 64 c -> a5 = Z_to_bv 64 (src + Z.of_nat j) ->
  s3 = Z_to_bv 64 ty -> s4 = Z_to_bv 64 sz -> s5 = Z_to_bv 64 0x4000 -> s11 = Z_to_bv 64 pp ->
  MemC sp m r src pp lo m1 (upd_bytes (upd_bytes (zeros 104) 0 (le32 ty)) 4 (le32 sz)) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 s3 s4 s5 s6 s7 S8 s9 S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b64) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 m1 j ty sz c Hj Hty Hsz Hc Eb
    -> -> -> -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (bytes_at_sub _ src r j (Z.to_nat c) (MemC_in sp m r src pp lo _ _ MC) ltac:(lia)) as BS.
  set (bs := firstn (Z.to_nat c) (skipn j r)) in BS.
  assert (Lbs : length bs = Z.to_nat c) by (subst bs; rewrite length_firstn, length_skipn; lia).
  assert (Ebs : firstn (Z.to_nat sz) (skipn j r) = bs).
  { subst bs. destruct (Z.le_ge_cases sz (Z.of_nat (length r) - Z.of_nat j)) as [X|X].
    - replace c with sz by lia. reflexivity.
    - rewrite !firstn_all2 by (rewrite length_skipn; lia). reflexivity. }
  rewrite Ebs in Eb. clear Ebs.
  (* 0x13b64 add s6,a5,a2; sub a0,a0,a2; sd a0,0x78(sp) *)
  do 2 step.
  pre_store HE (bv_unsigned sp + 120) 8%nat. step. mstore_out HE.
  (* addi a0,sp,0x90; mv a1,a5; jal memcpy *)
  do 3 step.
  mcname.
  lazymatch goal with MC : MemC _ _ _ _ _ _ ?mc ?eb |- _ =>
    destruct (MemC_cells sp m r src pp lo HE mc eb (bv_unsigned sp + 144) (Z.to_nat c) MC ltac:(lia)
                ltac:(unfold FRAME_LOCALS; lia)) as (junk & Lj & CJ) end.
  eapply evt_cut.
  { eapply MCPY with (src := bs) (junk := junk).
    - rewrite !unsigned_lit by lia. exact BS.
    - rewrite !unsigned_lit by lia. exact Lbs.
    - rewrite !unsigned_lit by lia. exact CJ.
    - rewrite !unsigned_lit by lia. left. lia.
    - exact (MemC_mem_inv _ _ _ _ _ _ _ _ MC). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & RC2 & _).
  subst ms'. rewrite !unsigned_lit in MU2, RC2 by lia.
  apply rw_CB_bytes in RC2 as [B2 L2].
  pose proof (MemC_call_e sp m r src pp lo HE _ m2 _ _ c _ MC MU2 WM2 MI2 B2
                ltac:(rewrite L2; lia) ltac:(lia) ltac:(lia)) as MC2.
  replace (bv_unsigned sp + 144 - (bv_unsigned sp + 136)) with 8 in MC2 by lia.
  pose proof (bytes_at_transport rsegs _ _ m2 _ _ HW MU2
                ltac:(cbn [disjoint_from]; rewrite length_le8; split; [lia | exact I])) as H78.
  clear MU2 WM2 MI2 B2 L2 MC CJ Lj junk HW BS.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x13b7c ld a6,0x80(sp); j 0x13504 *)
  mcells.
  do 2 step.
  eapply join_13504.
  - exact Eb.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal. rewrite ?unsigned_lit by lia. rewrite !length_skipn. lia.
  - reflexivity.
  - eapply MemC_e_ext; [exact MC2|]. apply ent_fill; lia.
  - rewrite !length_skipn. rewrite !unsigned_lit in H78 by lia.
    replace (Z.of_nat (length r - j - Z.to_nat sz)) with (Z.of_nat (length r) - Z.of_nat j - c) by lia. exact H78.
Qed.

(** 0x13b54: the size put in e, c = min(size, left), to 0x13b64. *)
Lemma tail_13b54 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) m1
    (j : nat) (ty sz : Z),
  (j <= length r)%nat -> 0 <= ty < 2^32 -> 0 <= sz <= 96 ->
  ent_build r = (Ent ty sz (firstn (Z.to_nat sz) (skipn j r) ++ zeros (Z.to_nat sz - length (firstn (Z.to_nat sz) (skipn j r)))),
                 skipn (Z.to_nat sz) (skipn j r)) ->
  a0 = Z_to_bv 64 (Z.of_nat (length r) - Z.of_nat j) -> a5 = Z_to_bv 64 (src + Z.of_nat j) ->
  s3 = Z_to_bv 64 ty -> s4 = Z_to_bv 64 sz -> s5 = Z_to_bv 64 0x4000 -> s11 = Z_to_bv 64 pp ->
  MemC sp m r src pp lo m1 (upd_bytes (zeros 104) 0 (le32 ty)) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 s3 s4 s5 s6 s7 S8 s9 S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b54) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 m1 j ty sz Hj Hty Hsz Eb
    -> -> -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13b54 sw s4,0x8c(sp) *)
  pre_store HE (bv_unsigned sp + 140) 4%nat. step. mstore_e HE 4.
  (* mv a2,s4; bltu s4,a0 *)
  do 2 step.
  unfold bv_ltu. rewrite (unsigned_lit sz) by lia.
  rewrite (unsigned_lit (Z.of_nat (length r) - Z.of_nat j)) by lia.
  destruct (Z.lt_ge_cases sz (Z.of_nat (length r) - Z.of_nat j)) as [X|X].
  - if_true.
    eapply (tail_13b64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j ty sz sz).
    + exact Hj.
    + exact Hty.
    + exact Hsz.
    + lia.
    + exact Eb.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply MemC_e_ext; [eassumption|]. rewrite le4_any. reflexivity.
  - if_false.
    step.
    eapply (tail_13b64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j ty sz (Z.of_nat (length r) - Z.of_nat j)).
    + exact Hj.
    + exact Hty.
    + exact Hsz.
    + lia.
    + exact Eb.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply MemC_e_ext; [eassumption|]. rewrite le4_any. reflexivity.
Qed.

Lemma case6_ok : case_at sp gp tp s7 s9 F fc m r src pp lo 6 0x137ac.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 b rest m1 Er Hk KS -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R. clear KS.
  assert (Hk' : Z.to_nat (bv_unsigned b mod 10) = 6%nat) by (rewrite Hk; reflexivity).
  (* 0x137ac beqz s5 *)
  step.
  unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r) - 1)) by (rewrite Er in *; cbn [length] in *; lia).
  destruct rest as [|v rest].
  - (* no byte left: t = 0, LONG, size 8, no body byte *)
    assert (Lr : length r = 1%nat) by (rewrite Er; reflexivity).
    if_true.
    (* 0x139f4 mv a0,zero; addi s4,zero,8; addi s3,zero,5; ld s11,0x50(sp); lui s5,4; j 0x13b50 *)
    mcells. do 6 step.
    (* 0x13b50 sw s3,0x88(sp) *)
    pre_store HE (bv_unsigned sp + 136) 4%nat. step. mstore_e HE 0.
    eapply (tail_13b54 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 5 8).
    + lia.
    + lia.
    + lia.
    + rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity.
    + f_equal. rewrite Lr. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply MemC_e_ext; [eassumption|]. rewrite le4_any. reflexivity.
  - (* t = the byte after kind; 0x137b0 lbu a1,1(s6); andi a1,a1,3 *)
    assert (Lr : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    if_false.
    assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 1)) 1 = Some [v]).
    { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 1 MC) by lia. rewrite Er. reflexivity. }
    step. clear HR.
    step.
    match goal with |- context [Z.land ?E 3] =>
      replace (Z.land E 3) with (bv_unsigned v mod 4) by (clear - v; revert v; byte_eq) end.
    assert (Ht : bv_unsigned v mod 4 = 0 \/ bv_unsigned v mod 4 = 1 \/ bv_unsigned v mod 4 = 2 \/
                 bv_unsigned v mod 4 = 3) by (pose proof (Z.mod_pos_bound (bv_unsigned v) 4); lia).
    (* addi a0,zero,2; beq a1,a0 *)
    do 2 step.
    mcells. mmi.
    destruct Ht as [Ht|[Ht|[Ht|Ht]]]; rewrite Ht.
    + (* LONG, 8: addi a2,zero,8; j 0x13b1c; 0x13b1c .. 0x13b4c: s11, s5, a0 = left, a5, s3 = t[0], s4 = 8 *)
      if_false. do 2 step. do 13 step.
      pre_store HE (bv_unsigned sp + 136) 4%nat. step. mstore_e HE 0.
      eapply (tail_13b54 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 5 8).
      * lia.
      * lia.
      * lia.
      * rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk'. cbn [fuzz_u8]. rewrite Ht. reflexivity.
      * f_equal; lia.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * eapply MemC_e_ext; [eassumption|]. vm_compute. reflexivity.
    + (* DOUBLE, 8 *)
      if_false. do 2 step. do 13 step.
      pre_store HE (bv_unsigned sp + 136) 4%nat. step. mstore_e HE 0.
      eapply (tail_13b54 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 7 8).
      * lia.
      * lia.
      * lia.
      * rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk'. cbn [fuzz_u8]. rewrite Ht. reflexivity.
      * f_equal; lia.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * eapply MemC_e_ext; [eassumption|]. vm_compute. reflexivity.
    + (* ID, 4: 0x13b18 addi a2,zero,4 *)
      if_true. step. do 13 step.
      pre_store HE (bv_unsigned sp + 136) 4%nat. step. mstore_e HE 0.
      eapply (tail_13b54 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 3 4).
      * lia.
      * lia.
      * lia.
      * rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk'. cbn [fuzz_u8]. rewrite Ht. reflexivity.
      * f_equal; lia.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * eapply MemC_e_ext; [eassumption|]. vm_compute. reflexivity.
    + (* NONE, 0 *)
      if_false. do 2 step. do 13 step.
      pre_store HE (bv_unsigned sp + 136) 4%nat. step. mstore_e HE 0.
      eapply (tail_13b54 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 1 0).
      * lia.
      * lia.
      * lia.
      * rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk'. cbn [fuzz_u8]. rewrite Ht. reflexivity.
      * f_equal; lia.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * eapply MemC_e_ext; [eassumption|]. vm_compute. reflexivity.
Qed.

End Case6.
