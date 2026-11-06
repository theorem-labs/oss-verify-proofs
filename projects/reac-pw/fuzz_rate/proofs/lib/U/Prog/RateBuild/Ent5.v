(** ent_build's kind 5 in the UBSan image (pod.h:335-338): a String of the next (n & 31) input bytes, with a
    NUL unless bit 7 of the kind is set. From the jump table's target 0x137d0 to the join 0x13ee4 (through 0x13a0c
    when no byte is left for n, 0x13a10 the clamp of n to the bytes left, 0x13a30 memcpy, 0x13a64 s8 / s11 reloaded).
    The form is reac-pw/fuzz_role's U/Prog/RoleBuild/Ent5.v re-walked at
    rate's registers: n in s8, the bytes left in s10, the
    source cursor in s7, the body sp + 0xf0 in s9. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** A pointer-overflow check `bltu (not p), n` with p + n below 2^64: not taken. The `not` of a register
    leaves an lxor with the ones; a complement frame cell leaves [Z.lnot]. *)
Lemma not_lt_false : forall x y, 0 <= x -> 0 <= y -> x + y < 2^64 ->
  bv_ltu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615)) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hx Hy Hxy. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  rewrite (Z.mod_small x) by lia. rewrite zb_lxor_ones by lia.
  rewrite (Z.mod_small (18446744073709551615 - x)) by lia. rewrite (Z.mod_small y) by lia.
  apply Z.ltb_ge. lia.
Qed.

Lemma lnot_lt_false : forall x y, 0 <= x -> 0 <= y -> x + y < 2^64 ->
  bv_ltu (Z_to_bv 64 (Z.lnot x)) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hx Hy Hxy. unfold bv_ltu. rewrite (unsigned_lnot x) by lia. rewrite unsigned_lit_wrap.
  rewrite (Z.mod_small y) by lia. apply Z.ltb_ge. lia.
Qed.

(** A zero-extended byte's value. *)
Lemma zxb_un : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. apply unsigned_lit. pose proof (byte_range b). lia. Qed.

(** The byte a `sb zero` store writes. *)
Lemma le1_nul : le1 (Z_to_bv 64 0) = [NUL].
Proof. vm_compute. reflexivity. Qed.

(** `bltz w` tests the sign of w. *)
Lemma lts0_signed : forall w : word, bv_lts w (Z_to_bv 64 0) = (bv_signed w <? 0).
Proof. intros w. unfold bv_lts. f_equal; vm_compute; reflexivity. Qed.

(** `n & 31` is n mod 32. *)
Lemma land31 : forall z, Z.land z 31 = z mod 32.
Proof. intros z. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

Section Case5.
Variables (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.

(** 0x13a1c -> the join: the copy of the nn bytes p at cur (s7) into the body (s9 = sp + 0xf0), the NUL when the
    kind's bit 7 is clear, the String's type and size, the cursor s9 = cur + nn and t1 = left - nn. *)
Lemma tail5 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m1
    (cur nn left : Z) (p r' : list byte) (nul : bool) (e : ent),
  ent_build r = (e, r') -> e = ent_text p nul -> nul = negb (bv_signed s11 <? 0) ->
  nn = Z.of_nat (length p) -> left = Z.of_nat (length r') + nn ->
  cur = src + Z.of_nat (length r) - Z.of_nat (length r') - nn ->
  s7 = Z_to_bv 64 cur -> s8 = Z_to_bv 64 nn -> s9 = Z_to_bv 64 (bv_unsigned sp + 0xf0) -> s10 = Z_to_bv 64 left ->
  cur + nn <= lo -> (length p <= 95)%nat -> bytes_at rsegs m1 cur p ->
  MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
  evt rsegs (QJ sp gp tp s3 F fc m r src pp lo (ent_build r))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x188)) (Z_to_bv 64 4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 95) s3 (Z_to_bv 64 (0xcccccccd * 2^32)) (Z_to_bv 64 10) (Z_to_bv 64 0x4000) s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a1c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1 cur nn left p r' nul e EB Ee Enul Enn
    Eleft Ecur E7 E8 E9 E10 Hcl Hp95 HB MC.
  subst s7 s8 s9 s10.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof HB as (HB0 & HB1 & _).
  (* 0x13a1c not a0,s7; 0x13a20 bltu a0,s8 (trap, not taken) *)
  step. step. rewrite not_lt_false by lia. cbv iota.
  (* 0x13a24 mv a0,s9; mv a1,s7; mv a2,s8; jal memcpy *)
  do 4 step.
  destruct (MemC_cells sp m r src pp lo HE _ _ _ _ (bv_unsigned sp + 240) (length p) MC
              ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as (junk & Lj & CJ).
  eapply evt_cut.
  { eapply MCPY;
      [ rewrite unsigned_lit by lia; exact HB
      | rewrite unsigned_lit by lia; lia
      | rewrite !unsigned_lit by lia; replace (Z.to_nat nn) with (length p) by lia; exact CJ
      | rewrite !unsigned_lit by lia; lia
      | exact (MemC_mem_inv _ _ _ _ _ _ _ MC) ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E &
              MU2 & WM2 & MI2 & CE2 & SB2).
  subst ms'. rewrite ret_pc_even by (first [lia | reflexivity]).
  rewrite !unsigned_lit in MU2, CE2 by lia.
  assert (MC2 : MemC sp m lo m2 (Z_to_bv 64 0) (Z_to_bv 64 0) (upd_bytes (zeros 96) 0 p)).
  { eapply (MemC_call_bd sp m r src pp lo HE m1 m2 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96)
              (bv_unsigned sp + 240) 0%nat p MC);
      [ replace (Z.of_nat (length p)) with nn by lia; exact MU2 | exact WM2 | exact MI2
      | exact (proj1 (rw_CB_bytes m2 _ _ _ CE2))
      | cbn [Z.of_nat]; lia | cbn [length]; lia ]. }
  clear MC MU2 WM2 MI2 CE2 SB2. rename MC2 into MC.
  rewrite (upd_zeros0 p 96) in MC by lia.
  (* 0x13a34 mv a0,s8; 0x13a38 bltz s11 *)
  step. step. rewrite lts0_signed.
  destruct (bv_signed s11 <? 0) eqn:Hsg; cbv iota.
  - (* bit 7 of the kind: no NUL *)
    assert (Enul' : nul = false) by (rewrite Enul; reflexivity).
    (* 0x13a50 add s9,s7,s8; sub t1,s10,s8; addi a1,zero,8; sw a1,0xe8(sp); sw a0,0xec(sp) *)
    do 3 step. est_t HE MC. est_sz HE MC.
    (* 0x13a64 ld s8,0xd8(sp); ld s11,0xc8(sp); j 0x13ee4 *)
    pose proof (MemC_cd8 sp m r src pp lo HE _ _ _ _ MC) as Rd8. step. clear Rd8.
    pose proof (MemC_cc8 sp m r src pp lo HE _ _ _ _ MC) as Rc8. step. clear Rc8.
    step.
    eapply join_13ee4; [exact EB | | | exact MC | | | ].
    + f_equal. rewrite ?unsigned_lit by lia. lia.
    + f_equal. rewrite ?unsigned_lit by lia. lia.
    + rewrite Ee, Enul'. cbn [ent_text e_type]. unfold POD_STRING. apply le4_le32.
    + rewrite Ee, Enul'. cbn [ent_text e_size]. rewrite firstn_all2 by lia.
      replace (Z.of_nat (length p)) with nn by lia. apply le4_le32.
    + rewrite Ee, Enul'. cbn [ent_text e_body]. rewrite firstn_all2 by lia. reflexivity.
  - (* the NUL *)
    assert (Enul' : nul = true) by (rewrite Enul; reflexivity).
    (* 0x13a3c ld a0,0xa0(sp); bltu a0,s8 (trap); add a1,s9,s8; addi a0,s8,1; sb zero,0(a1) *)
    pose proof (MemC_ca0 sp m r src pp lo HE _ _ _ _ MC) as Ra0. step. step.
    rewrite lnot_lt_false by (unfold FRAME_LOCALS in *; lia). cbv iota. clear Ra0. do 2 step.
    est_bd HE MC (bv_unsigned sp + 240 + nn) (length p) 1%nat.
    (* 0x13a50 .. 0x13a6c *)
    do 3 step. est_t HE MC. est_sz HE MC.
    pose proof (MemC_cd8 sp m r src pp lo HE _ _ _ _ MC) as Rd8. step. clear Rd8.
    pose proof (MemC_cc8 sp m r src pp lo HE _ _ _ _ MC) as Rc8. step. clear Rc8.
    step.
    eapply join_13ee4; [exact EB | | | exact MC | | | ].
    + f_equal. rewrite ?unsigned_lit by lia. lia.
    + f_equal. rewrite ?unsigned_lit by lia. lia.
    + rewrite Ee, Enul'. cbn [ent_text e_type]. unfold POD_STRING. apply le4_le32.
    + rewrite Ee, Enul'. cbn [ent_text e_size]. rewrite firstn_all2 by lia.
      rewrite length_app. cbn [length]. replace (Z.of_nat (length p + 1)) with (nn + 1) by lia. apply le4_le32.
    + rewrite Ee, Enul'. cbn [ent_text e_body]. rewrite firstn_all2 by lia.
      rewrite (upd_app_zeros p (le1 (Z_to_bv 64 0)) (96 - length p)) by (rewrite length_le1; lia).
      rewrite le1_nul, length_app. cbn [length].
      replace (96 - length p - 1)%nat with (96 - (length p + 1))%nat by lia.
      rewrite <- app_assoc. reflexivity.
Qed.

Lemma case5_ok_sec : case_at sp gp tp s3 F fc m r src pp lo 5 0x137d0.
Proof.
  intros ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 b rest m1 Er Hk Hs MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (byte_range b) as Rb.
  assert (HR : bytes_at rsegs m1 src r) by exact (MemC_in sp m r src pp lo HE _ _ _ _ MC).
  destruct rest as [|c rest2].
  - (* no byte for n: n = 0, p = [] *)
    assert (L : length r = 1%nat) by (rewrite Er; reflexivity).
    assert (EB : ent_build r = (ent_text [] (negb (Z.testbit (bv_unsigned b) 7)), [])).
    { rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. cbn [Z.to_nat]. unfold fuzz_take.
      cbn [firstn skipn]. reflexivity. }
    (* 0x137d0 beqz s8 (taken); 0x13a0c mv s10,zero; 0x13a10 addi s9,sp,0xf0; 0x13a14 bltu s8,s10 (not taken);
       0x13a18 mv s8,s10 *)
    step. brt. do 2 step. step. brf. step.
    eapply (tail5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (src + 1) 0 0 [] []
              (negb (Z.testbit (bv_unsigned b) 7)) _ EB eq_refl);
      [ rewrite Hs; reflexivity | reflexivity | reflexivity | rewrite L; cbn [length]; lia
      | reflexivity | reflexivity | f_equal; lia | reflexivity
      | lia | cbn [length]; lia | apply bytes_at_nil; lia | exact MC ].
  - (* n = byte 1 *)
    assert (L : length r = S (S (length rest2))) by (rewrite Er; reflexivity).
    pose proof (byte_range c) as Rc.
    set (k := Z.to_nat (bv_unsigned c mod 32)) in *.
    assert (EB : ent_build r = (ent_text (firstn k rest2) (negb (Z.testbit (bv_unsigned b) 7)), skipn k rest2)).
    { rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. cbn [Z.to_nat]. unfold fuzz_take. reflexivity. }
    assert (Lp : length (firstn k rest2) = Nat.min k (length rest2)) by apply length_firstn.
    assert (Lr : length (skipn k rest2) = (length rest2 - k)%nat) by apply length_skipn.
    assert (HB2 : bytes_at rsegs m1 (src + 2) rest2).
    { rewrite Er in HR. change (b :: c :: rest2) with ([b; c] ++ rest2) in HR.
      apply bytes_at_app in HR as [_ HR2]. cbn [length] in HR2.
      replace (src + Z.of_nat 2) with (src + 2) in HR2 by lia. exact HR2. }
    assert (HBp : bytes_at rsegs m1 (src + 2) (firstn k rest2)).
    { rewrite <- (firstn_skipn k rest2) in HB2. apply bytes_at_app in HB2 as [HB3 _]. exact HB3. }
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 1 MC ltac:(lia)) as HB1. rewrite Er in HB1. cbn [nth] in HB1.
    (* 0x137d0 beqz s8 (not taken); addi s7,s7,1; addi a0,zero,1; bgeu a0,s7 (trap); lbu a0,1(s9) *)
    step. brf. do 2 step. step. brf. step.
    (* 0x137e4 addi s10,t1,-2; addi s7,s9,2; andi s8,a0,0x1f; j 0x13a10; addi s9,sp,0xf0; bltu s8,s10 *)
    do 3 step. rewrite land31, zxb_un.
    do 2 step.
    step. if_cases T; zify_cond T.
    + (* n mod 32 < bytes left *)
      eapply (tail5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (src + 2) (Z.of_nat (length (firstn k rest2)))
                (Z.of_nat (length rest2)) (firstn k rest2) (skipn k rest2)
                (negb (Z.testbit (bv_unsigned b) 7)) _ EB eq_refl);
        [ rewrite Hs; reflexivity | reflexivity | rewrite Lr, Lp; lia
        | rewrite L, Lr, Lp; lia | f_equal; lia | f_equal; rewrite Lp; unfold k in *; lia | f_equal; lia
        | f_equal; rewrite L; lia
        | rewrite Lp; lia | rewrite Lp; unfold k in *; lia | exact HBp | exact MC ].
    + (* clamped: s8 := s10 *)
      step.
      eapply (tail5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (src + 2) (Z.of_nat (length (firstn k rest2)))
                (Z.of_nat (length rest2)) (firstn k rest2) (skipn k rest2)
                (negb (Z.testbit (bv_unsigned b) 7)) _ EB eq_refl);
        [ rewrite Hs; reflexivity | reflexivity | rewrite Lr, Lp; lia
        | rewrite L, Lr, Lp; lia | f_equal; lia | f_equal; rewrite Lp, L; unfold k in *; lia | f_equal; lia
        | f_equal; rewrite L; lia
        | rewrite Lp; lia | rewrite Lp; unfold k in *; lia | exact HBp | exact MC ].
Qed.

End Case5.

Theorem case5_ok : forall (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte) (src pp lo : Z), ent_pre sp m r src pp lo -> memcpy_contract -> case_at sp gp tp s3 F fc m r src pp lo 5 0x137d0.
Proof. intros. apply case5_ok_sec; assumption. Qed.
