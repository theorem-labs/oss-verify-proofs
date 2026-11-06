(** ent_build's kind 5 (pod.h:333-338): a String of the next n % 32 input bytes, n = fuzz_u8, NUL-terminated
    unless kind's bit 7 is set (ent_text). From the jump table's target 0x138dc through memcpy(e.body, in, n') at
    0x13b10 to the join 0x13758. Ported from reac-pw/fuzz_role's Prog/RoleBuild/Ent5.v (role 0x13794 / 0x139b4 / 0x139dc / 0x134f0 = rate 0x138dc / 0x13b00 / 0x13b28 / 0x13758) at rate's
    registers (role s3 s4 s5 s6 s11 = rate s5 s6 s7 s8 s1) and frame cells (cursor spill 0x58, bytes left 0xa8, e
    0xb8, e.body 0xc0). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** ** Byte-list facts *)
Lemma skipn_zeros : forall k n, skipn k (zeros n) = zeros (n - k).
Proof.
  unfold zeros. intros k. induction k as [|k IH]; intros n.
  - cbn [skipn]. rewrite Nat.sub_0_r. reflexivity.
  - destruct n as [|n]; [reflexivity|]. cbn [skipn repeat]. rewrite IH. reflexivity.
Qed.

(** Bytes bs put at the end of l, over zeros. *)
Lemma upd_tail : forall l n bs k, k = length l -> (length bs <= n)%nat ->
  upd_bytes (l ++ zeros n) k bs = l ++ bs ++ zeros (n - length bs).
Proof.
  intros l n bs k -> H. unfold upd_bytes.
  rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all.
  rewrite skipn_app. replace (length l + length bs - length l)%nat with (length bs) by lia.
  rewrite skipn_all2 by lia. rewrite skipn_zeros. reflexivity.
Qed.

(** ent_text of at most 95 bytes. *)
Lemma ent_text_short : forall s nul, (length s <= 95)%nat ->
  ent_text s nul = Ent POD_STRING (Z.of_nat (length (if nul then s ++ [NUL] else s))) (if nul then s ++ [NUL] else s).
Proof. intros s nul H. unfold ent_text. rewrite firstn_all2 by exact H. reflexivity. Qed.

(** Name the current MemC hypothesis MC. *)
Local Ltac mcname :=
  lazymatch goal with H : MemC _ _ _ _ _ _ _ _ |- _ => let X := fresh "X" in rename H into X; rename X into MC end.

Section Case5.
Variables (sp gp tp s2 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.

Local Abbreviation QE := (QJ sp gp tp s2 s9 F fc m r src pp lo (ent_build r)).
Local Abbreviation S0 := (Z_to_bv 64 95).
Local Abbreviation S3 := (Z_to_bv 64 10).
Local Abbreviation S4 := (Z_to_bv 64 (0xcccccccd * 2^32)).
Local Abbreviation S10 := (Z_to_bv 64 (bv_unsigned sp + 0x158)).
Local Abbreviation S11 := (Z_to_bv 64 (bv_unsigned sp + 0x120)).

(** 0x13b28: s8 = the spilled cursor + n', the bytes left, type 8, to 0x13758. *)
Lemma tail5_13b28 : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 : word) m1
    (j c : nat) (body : list byte),
  (j + c <= length r)%nat -> (length body <= 96)%nat ->
  ent_build r = (Ent POD_STRING (Z.of_nat (length body)) body, skipn (j + c) r) ->
  s6 = Z_to_bv 64 (Z.of_nat (length body)) -> s7 = Z_to_bv 64 (Z.of_nat c) ->
  s5 = Z_to_bv 64 (Z.of_nat (length r) - Z.of_nat j) ->
  MemC sp m r src pp lo m1 (zeros 8 ++ body ++ zeros (96 - length body)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 88) (le8 (Z_to_bv 64 (src + Z.of_nat j))) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 S3 S4 s5 s6 s7 s8 s9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b28) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 m1 j c body Hjc Hb Eb -> -> -> MC H58.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (bytes_at_rw_C8 m1 _ _ lo (bv_unsigned sp + FRAME_LOCALS) H58 (MemC_stk _ _ _ _ _ _ _ _ MC)
                ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as C58.
  (* 0x13b28 ld s8,0x58(sp); add s8,s8,s7; sub a0,s5,s7; sd a0,0xa8(sp) *)
  do 3 step.
  pre_store HE (bv_unsigned sp + 168) 8%nat. step. mstore_out HE.
  (* addi s5,zero,8; j 0x13758 *)
  do 2 step.
  eapply (join_13758 sp gp tp s2 s9 F fc m r src pp lo HE) with (h := zeros 8).
  - exact Eb.
  - reflexivity.
  - cbn [e_type]. unfold POD_STRING. lia.
  - cbn [e_size]. lia.
  - reflexivity.
  - reflexivity.
  - f_equal. rewrite ?unsigned_lit by lia. rewrite length_skipn. lia.
  - eassumption.
  - rewrite length_skipn. rewrite !unsigned_lit in HW by lia.
    replace (Z.of_nat (length r - (j + c))) with (Z.of_nat (length r) - Z.of_nat j - Z.of_nat c) by lia. exact HW.
Qed.

(** 0x13b00: memcpy(e.body, src + j, c), the NUL unless s1 < 0, to 0x13b28. *)
Lemma tail5_13b00 : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 : word) m1
    (j c : nat) (nul : bool),
  (j + c <= length r)%nat -> (c <= 31)%nat ->
  ent_build r = (ent_text (firstn c (skipn j r)) nul, skipn (j + c) r) ->
  (bv_signed s1 < 0 <-> nul = false) ->
  a5 = Z_to_bv 64 (src + Z.of_nat j) -> s7 = Z_to_bv 64 (Z.of_nat c) ->
  s5 = Z_to_bv 64 (Z.of_nat (length r) - Z.of_nat j) -> s8 = Z_to_bv 64 (bv_unsigned sp + 192) ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 S3 S4 s5 s6 s7 s8 s9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b00) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 m1 j c nul Hjc Hc Eb KS -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (bytes_at_sub _ src r j c (MemC_in sp m r src pp lo _ _ MC) ltac:(lia)) as BS.
  set (bs := firstn c (skipn j r)) in Eb, BS.
  assert (Lbs : length bs = c) by (subst bs; rewrite length_firstn, length_skipn; lia).
  rewrite ent_text_short in Eb by lia.
  (* 0x13b00 mv a0,s8; sd a5,0x58(sp) *)
  step.
  pre_store HE (bv_unsigned sp + 88) 8%nat. step. mstore_out HE.
  (* mv a1,a5; mv a2,s7; jal memcpy *)
  do 3 step.
  mcname.
  lazymatch goal with MC : MemC _ _ _ _ _ _ ?mc ?eb |- _ =>
    destruct (MemC_cells sp m r src pp lo HE mc eb (bv_unsigned sp + 192) c MC ltac:(lia)
                ltac:(unfold FRAME_LOCALS; lia)) as (junk & Lj & CJ) end.
  eapply evt_cut.
  { eapply MCPY with (src := bs) (junk := junk).
    - rewrite !unsigned_lit by lia. exact BS.
    - rewrite !unsigned_lit by lia. rewrite Nat2Z.id. exact Lbs.
    - rewrite !unsigned_lit by lia. rewrite Nat2Z.id. exact CJ.
    - rewrite !unsigned_lit by lia. left. lia.
    - exact (MemC_mem_inv _ _ _ _ _ _ _ _ MC). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & RC2 & _).
  subst ms'. rewrite !unsigned_lit in MU2, RC2 by lia.
  apply rw_CB_bytes in RC2 as [B2 L2].
  pose proof (MemC_call_e sp m r src pp lo HE _ m2 _ _ (Z.of_nat c) _ MC MU2 WM2 MI2 B2
                ltac:(rewrite L2; lia) ltac:(lia) ltac:(lia)) as MC2.
  replace (bv_unsigned sp + 192 - (bv_unsigned sp + 184)) with 8 in MC2 by lia.
  pose proof (bytes_at_transport rsegs _ _ m2 _ _ HW MU2
                ltac:(cbn [disjoint_from]; rewrite length_le8; split; [lia | exact I])) as H58.
  clear MU2 WM2 MI2 B2 L2 MC CJ Lj junk HW BS.
  apply (MemC_e_ext _ _ _ _ _ _ _ _ (zeros 8 ++ bs ++ zeros (96 - length bs))) in MC2;
    [|replace (zeros 104) with (zeros 8 ++ zeros 96) by reflexivity; apply upd_tail; [reflexivity | lia]].
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x13b14 mv s6,s7; bltz s1 *)
  do 2 step.
  destruct nul; cbv iota in Eb.
  - (* NUL: 0x13b1c addi s6,s7,1; add a0,s8,s7; sb zero,0(a0) *)
    assert (NS : 0 <= bv_signed s1)
      by (destruct (Z.lt_ge_cases (bv_signed s1) 0) as [X|X]; [apply KS in X; discriminate X | exact X]).
    clear KS.
    if_false.
    do 2 step.
    pre_store HE (bv_unsigned sp + 192 + Z.of_nat c) 1%nat. step. mstore_e HE (8 + Z.of_nat c).
    eapply (tail5_13b28 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j c (bs ++ [NUL])).
    + exact Hjc.
    + rewrite length_app, Lbs. cbn [length]. lia.
    + exact Eb.
    + f_equal. rewrite length_app, Lbs. cbn [length]. lia.
    + reflexivity.
    + reflexivity.
    + eapply MemC_e_ext; [eassumption|].
      try change (le1 (Z_to_bv 64 0)) with [NUL].
      rewrite app_assoc.
      rewrite (upd_tail (zeros 8 ++ bs) (96 - length bs) [NUL]) by (rewrite ?length_app, ?length_zeros; cbn [length]; lia).
      rewrite <- !app_assoc. rewrite length_app. cbn [length].
      replace (96 - (length bs + 1))%nat with (96 - length bs - 1)%nat by lia. reflexivity.
    + exact H58.
  - (* no NUL: 0x13b28 *)
    assert (NS : bv_signed s1 < 0) by (apply KS; reflexivity).
    clear KS.
    if_true.
    eapply (tail5_13b28 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j c bs).
    + exact Hjc.
    + lia.
    + exact Eb.
    + rewrite Lbs. reflexivity.
    + reflexivity.
    + reflexivity.
    + exact MC2.
    + exact H58.
Qed.

Lemma case5_ok : case_at sp gp tp s2 s9 F fc m r src pp lo 5 0x138dc.
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 b rest m1 Er Hk KS -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  rewrite <- Bool.negb_false_iff in KS.
  (* 0x138dc beqz s7 *)
  step.
  unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r) - 1)) by (rewrite Er in *; cbn [length] in *; lia).
  destruct rest as [|v rest].
  - (* no byte left: n = 0; 0x13af0 mv s5,zero; 0x13af4 addi s8,sp,0xc0; bltu s7,s5; mv s7,s5 *)
    assert (Lr : length r = 1%nat) by (rewrite Er; reflexivity).
    if_true.
    do 3 step.
    unfold bv_ltu. rewrite (unsigned_lit (Z.of_nat (length r) - 1)) by lia.
    if_false.
    step.
    eapply (tail5_13b00 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 0 (negb (Z.testbit (bv_unsigned b) 7))).
    + lia.
    + lia.
    + rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity.
    + exact KS.
    + reflexivity.
    + reflexivity.
    + f_equal. rewrite Lr. reflexivity.
    + reflexivity.
    + exact MC.
  - (* n = the byte after kind; 0x138e0 lbu a0,1(s8) *)
    assert (Lr : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    if_false.
    assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 1)) 1 = Some [v]).
    { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 1 MC) by lia. rewrite Er. reflexivity. }
    step. clear HR.
    (* addi s5,s6,-2; addi a5,s8,2; andi s7,a0,0x1f; j 0x13af4 *)
    do 4 step.
    match goal with |- context [Z.land ?E 31] =>
      replace (Z.land E 31) with (bv_unsigned v mod 32) by (clear - v; revert v; byte_eq) end.
    pose proof (Z.mod_pos_bound (bv_unsigned v) 32 ltac:(lia)) as Hm.
    assert (Eb0 : ent_build r = (ent_text (firstn (Z.to_nat (bv_unsigned v mod 32)) rest)
                                   (negb (Z.testbit (bv_unsigned b) 7)),
                                 skipn (Z.to_nat (bv_unsigned v mod 32)) rest))
      by (rewrite Er; unfold ent_build; cbn [fuzz_u8]; rewrite Hk; reflexivity).
    (* 0x13af4 addi s8,sp,0xc0; bltu s7,s5 *)
    do 2 step.
    unfold bv_ltu. rewrite (unsigned_lit (bv_unsigned v mod 32)) by lia.
    rewrite (unsigned_lit (Z.of_nat (length r) + -2)) by lia.
    destruct (Z.lt_ge_cases (bv_unsigned v mod 32) (Z.of_nat (length r) + -2)) as [Hlt|Hge].
    + (* n % 32 bytes *)
      if_true.
      eapply (tail5_13b00 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 (Z.to_nat (bv_unsigned v mod 32))
                (negb (Z.testbit (bv_unsigned b) 7))).
      * lia.
      * lia.
      * rewrite Eb0, Er. reflexivity.
      * exact KS.
      * reflexivity.
      * f_equal; lia.
      * f_equal; lia.
      * reflexivity.
      * exact MC.
    + (* the bytes left *)
      if_false.
      step.
      eapply (tail5_13b00 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 (length rest)
                (negb (Z.testbit (bv_unsigned b) 7))).
      * lia.
      * lia.
      * rewrite Eb0, Er. change (skipn 2 (b :: v :: rest)) with rest.
        change (skipn (2 + length rest) (b :: v :: rest)) with (skipn (length rest) rest).
        rewrite firstn_all, skipn_all. rewrite firstn_all2, skipn_all2 by lia. reflexivity.
      * exact KS.
      * reflexivity.
      * f_equal; lia.
      * f_equal; lia.
      * reflexivity.
      * exact MC.
Qed.

End Case5.
