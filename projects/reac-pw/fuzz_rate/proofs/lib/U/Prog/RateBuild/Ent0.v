(** ent_build's kind 0 in the UBSan image (ent_headamp_key, pod.h:224-262), its entries: the jump table's target
    0x135d4 and 0x13ac4 (the input empty at the head). c = fuzz_u8 and p = fuzz_u8 by how many bytes are left (the
    UBSan checks on the cursor not taken), then Ent0C.c_ok (c > 199 or not) or, with no byte for c, Ent0C.nil_ok
    (0x13ac4, the digits of 0); from the cut 0x13b64 on, Ent0T.case0_mid_ok. The form is reac-pw/fuzz_role's
    U/Prog/RoleBuild/Ent0.v, re-walked on rate's code, with the cut discharged here. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c
  strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import EntCut EntFacts Ent0Mid Ent0C
  Ent0T.
Import ListNotations.
Open Scope Z_scope.

(** ** ent_build for kind 0, by how many bytes follow kind *)
Lemma ent0_nil : ent_build [] = (ent_text (key0 0 0) true, []).
Proof. reflexivity. Qed.

Lemma ent0_b : forall b : byte, bv_unsigned b mod 10 = 0 -> ent_build [b] = (ent_text (key0 0 0) true, []).
Proof. intros b H. unfold ent_build. cbn [fuzz_u8]. rewrite H. reflexivity. Qed.

Lemma ent0_c1 : forall b c : byte, bv_unsigned b mod 10 = 0 ->
  ent_build [b; c] = (ent_text (key0 (bv_unsigned c) 0) true, []).
Proof. intros b c H. unfold ent_build. cbn [fuzz_u8]. rewrite H. reflexivity. Qed.

Lemma ent0_cp : forall (b c pb : byte) rest, bv_unsigned b mod 10 = 0 ->
  ent_build (b :: c :: pb :: rest) = (ent_text (key0 (bv_unsigned c) (bv_unsigned pb)) true, rest).
Proof. intros b c pb rest H. unfold ent_build. cbn [fuzz_u8]. rewrite H. reflexivity. Qed.

Section Case0.
Variables (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.
Hypothesis STRL : strlen_contract.

Lemma case0_ok_sec : case_at sp gp tp s3 F fc m r src pp lo 0 0x135d4.
Proof.
  intros ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 b rest m1 Er Hk Hs MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (case0_mid_ok sp gp tp s3 F fc m r src pp lo HE MCPY STRL) as MID.
  destruct rest as [|cb [|pb rest2]].
  - (* only kind: c = p = 0 *)
    assert (L : length r = 1%nat) by (rewrite Er; reflexivity).
    (* 0x135d4 beqz s8 -> 0x13ac0 mv s9,s7 *)
    step. brt. step.
    eapply (nil_ok sp gp tp s3 F fc m r src pp lo HE MID);
      [ rewrite Er, (ent0_b b Hk); reflexivity | f_equal; rewrite L; cbn [Z.of_nat]; lia | exact MC ].
  - (* kind and c: p = 0 *)
    assert (L : length r = 2%nat) by (rewrite Er; reflexivity).
    (* 0x135d4 beqz s8; addi s7,s7,1; addi s6,sp,0x170; addi a0,zero,1; addi a7,sp,0x150; addi t0,zero,9;
       bltu a0,s7 (over the trap) *)
    step. brf. do 6 step. brt.
    (* 0x135f4 lbu a0,1(s9): c *)
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 1 MC ltac:(lia)) as HB. rewrite Er in HB. cbn [nth] in HB.
    step. clear HB.
    (* 0x135f8 addi s10,s9,2; addi a1,zero,2; bne t1,a1 (two bytes: not taken) *)
    do 3 step. brf.
    (* 0x13604 mv t1,zero; mv s8,zero; j 0x13ca4 *)
    do 3 step.
    pose proof (byte_range cb) as Hcb.
    eapply (c_ok sp gp tp s3 F fc m r src pp lo HE MCPY STRL MID (bv_unsigned cb) 0 []);
      [ lia | lia | rewrite Er, (ent0_c1 b cb Hk); reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | f_equal; rewrite L; cbn [length]; lia | reflexivity | reflexivity | exact MC ].
  - (* kind, c, p *)
    assert (L : length r = S (S (S (length rest2)))) by (rewrite Er; reflexivity).
    step. brf. do 6 step. brt.
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 1 MC ltac:(lia)) as HB. rewrite Er in HB. cbn [nth] in HB.
    step. clear HB.
    (* 0x135f8 addi s10,s9,2; addi a1,zero,2; bne t1,a1 (taken) *)
    do 3 step. brt.
    (* 0x13c8c addi s10,s10,1; addi a1,zero,1; bgeu a1,s10 (trap) *)
    do 3 step. brf.
    (* 0x13c98 lbu s8,2(s9): p *)
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 2 MC ltac:(lia)) as HB. rewrite Er in HB. cbn [nth] in HB.
    step. clear HB.
    (* 0x13c9c addi t1,t1,-3; addi s10,s9,3 *)
    do 2 step.
    pose proof (byte_range cb) as Hcb. pose proof (byte_range pb) as Hpb.
    eapply (c_ok sp gp tp s3 F fc m r src pp lo HE MCPY STRL MID (bv_unsigned cb) (bv_unsigned pb) rest2);
      [ lia | lia | rewrite Er, (ent0_cp b cb pb rest2 Hk); reflexivity | reflexivity | reflexivity | reflexivity
      | f_equal; rewrite L; lia | f_equal; rewrite L; lia | reflexivity | reflexivity | exact MC ].
Qed.

Lemma case0_nil_sec : case0_nil_at sp gp tp s3 F fc m r src pp lo.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s11 t3 t4 t5 t6 m1 Er MC.
  pose proof (case0_mid_ok sp gp tp s3 F fc m r src pp lo HE MCPY STRL) as MID.
  eapply (nil_ok sp gp tp s3 F fc m r src pp lo HE MID);
    [ rewrite Er; reflexivity | f_equal; rewrite Er; cbn [length]; lia | exact MC ].
Qed.

End Case0.

Theorem case0_ok : forall (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte) (src pp lo : Z), ent_pre sp m r src pp lo -> memcpy_contract -> strlen_contract -> case_at sp gp tp s3 F fc m r src pp lo 0 0x135d4.
Proof. intros. apply case0_ok_sec; assumption. Qed.

Theorem case0_nil_ok : forall (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte) (src pp lo : Z), ent_pre sp m r src pp lo -> memcpy_contract -> strlen_contract -> case0_nil_at sp gp tp s3 F fc m r src pp lo.
Proof. intros. apply case0_nil_sec; assumption. Qed.
