(** ent_build's kind 7 in the UBSan image (pod.h:352-356): a pod of type t % 21 whose size is s % 12 and whose
    body is the next size input bytes, zero-padded. From the jump table's target 0x13654 to the join 0x13df0
    (through 0x13908 when no byte is left for the type, and the tail 0x13cd8 kind 6 proves). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadBuild Require Import EntCut EntFacts Ent5 Ent6.
Import ListNotations.
Open Scope Z_scope.

(** ent_build's kind 7, for the three lengths of input left after the kind byte. *)
Lemma eb7_nil : forall (b : byte), bv_unsigned b mod 10 = 7 ->
  ent_build [b] = (Ent 0 0 (firstn 0 (@nil byte) ++ zeros (0 - length (firstn 0 (@nil byte)))), skipn 0 (@nil byte)).
Proof.
  intros b Hk. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. cbn [Z.to_nat]. unfold fuzz_take.
  cbn [firstn skipn length Z.to_nat]. reflexivity.
Qed.

Lemma eb7_one : forall (b c : byte), bv_unsigned b mod 10 = 7 ->
  ent_build [b; c] =
  (Ent (bv_unsigned c mod 21) 0 (firstn 0 (@nil byte) ++ zeros (0 - length (firstn 0 (@nil byte)))),
   skipn 0 (@nil byte)).
Proof.
  intros b c Hk. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. cbn [Z.to_nat]. unfold fuzz_take.
  cbn [firstn skipn length Z.to_nat]. reflexivity.
Qed.

Lemma eb7 : forall (b c d : byte) (rest3 : list byte), bv_unsigned b mod 10 = 7 ->
  ent_build (b :: c :: d :: rest3) =
  (Ent (bv_unsigned c mod 21) (bv_unsigned d mod 12)
     (firstn (Z.to_nat (bv_unsigned d mod 12)) rest3
      ++ zeros (Z.to_nat (bv_unsigned d mod 12) - length (firstn (Z.to_nat (bv_unsigned d mod 12)) rest3))),
   skipn (Z.to_nat (bv_unsigned d mod 12)) rest3).
Proof.
  intros b c d rest3 Hk. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. cbn [Z.to_nat]. unfold fuzz_take.
  reflexivity.
Qed.

Section Case7.
Variables (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.

Lemma case7_ok_sec : case_at sp gp tp s1 F fc m r src pp lo 7 0x13654.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 b rest m1 Er Hk Hs MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (byte_range b) as Rb.
  destruct rest as [|c rest2].
  - (* no byte for the type *)
    assert (L : length r = 1%nat) by (rewrite Er; reflexivity).
    (* 0x13654 beqz s6 (taken); 0x13908 mv a4,zero; mv a2,zero; addi a0,sp,0xc0; j 0x13cd8 *)
    step. brt. do 4 step.
    eapply (tail67 sp gp tp s1 F fc m r src pp lo HE MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 1%nat
              (src + 1) 0 0 _ _ _);
      [ rewrite Er; cbn [skipn]; exact (eb7_nil b Hk) | apply le4_le32 | reflexivity | reflexivity
      | lia | lia | cbn [Z.of_nat]; lia | rewrite L; cbn [Z.of_nat]; lia
      | rewrite Er; cbn [skipn]; reflexivity | rewrite Er; cbn [skipn]; reflexivity | exact MC ].
  - assert (L : length r = S (S (length rest2))) by (rewrite Er; reflexivity).
    pose proof (byte_range c) as Rc.
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 1 MC ltac:(lia)) as HB1.
    rewrite Er in HB1. cbn [nth] in HB1.
    (* 0x13654 beqz s6 (not taken); addi s5,s5,1; addi a0,zero,1; bltu a0,s5,8 over the trap (taken); lbu a0,1(s10) *)
    step. brf. do 2 step. step. brt. step.
    (* 0x1366c addi s5,s10,2; 0x13670-0x136a0 t % 21 *)
    do 14 step.
    match goal with |- context [Z_to_bv 64 (Z.land ?X 255)] =>
      replace (Z.land X 255) with (bv_unsigned c mod 21) by (symmetry; byte_eq c) end.
    (* 0x136a4 sw a0,0xb8(sp); 0x136a8 addi a0,sp,0xc0; 0x136ac addi a1,zero,2; 0x136b0 bne s2,a1 *)
    est_t HE MC. step. step.
    destruct rest2 as [|d rest3].
    + (* no byte for the size: size 0 *)
      cbn [length] in L. step. brf.
      (* 0x136b4 mv a4,zero; 0x136b8 mv a2,zero; j 0x13cd8 *)
      do 3 step.
      eapply (tail67 sp gp tp s1 F fc m r src pp lo HE MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat
                (src + 2) 0 0 _ _ _);
        [ rewrite Er; exact (eb7_one b c Hk) | apply le4_le32 | reflexivity | reflexivity
        | lia | lia | cbn [Z.of_nat]; lia | rewrite L; cbn [Z.of_nat]; lia
        | rewrite Er; cbn [skipn]; reflexivity | rewrite Er; cbn [skipn]; reflexivity | exact MC ].
    + (* the size byte *)
      cbn [length] in L. pose proof (byte_range d) as Rd.
      step. brt.
      pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 2 MC ltac:(rewrite L; cbn [length]; lia)) as HB2.
      rewrite Er in HB2. cbn [nth] in HB2.
      pose proof (MemC_c0 sp m r src pp lo HE _ _ _ _ MC) as HC0.
      (* 0x13ca4 addi s5,s5,1; addi a1,zero,1; bgeu a1,s5 (trap); lbu a2,2(s10) *)
      do 2 step. step. brf. step.
      (* 0x13cb4 addi a4,s2,-3; addi s5,s10,3; ld a1,0(sp); the s % 12 multiply *)
      do 9 step.
      match goal with |- context [Z_to_bv 64 (bv_unsigned (zxb d) + ?X)] =>
        replace (bv_unsigned (zxb d) + X) with (bv_unsigned d mod 12) by (symmetry; byte_eq d) end.
      eapply (tail67 sp gp tp s1 F fc m r src pp lo HE MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3%nat
                (src + 3) (Z.of_nat (length r) + -3) (bv_unsigned d mod 12) _ _ _);
        [ rewrite Er; exact (eb7 b c d rest3 Hk) | apply le4_le32 | reflexivity | reflexivity
        | lia | lia | cbn [Z.of_nat]; lia | rewrite L; cbn [Z.of_nat]; lia
        | rewrite Er; cbn [skipn]; reflexivity | rewrite Er; cbn [skipn]; reflexivity | exact MC ].
Qed.

End Case7.

Theorem case7_ok : forall (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (r : list byte) (src pp lo : Z),
  ent_pre sp m r src pp lo -> memcpy_contract -> case_at sp gp tp s1 F fc m r src pp lo 7 0x13654.
Proof. intros. apply case7_ok_sec; assumption. Qed.
