(** ent_build's kind 0 in the UBSan image (ent_headamp_key, pod.h:224-262), its entries: the jump table's target
    0x133d0 and 0x13878 (the input empty at the head). c = fuzz_u8 and p = fuzz_u8 by how many bytes are left (the
    UBSan checks on the cursor not taken), then Ent0C.c_ok (c > 199 or not) or, with no byte for c, the digits of 0;
    from the cut 0x13914 on, [Ent0Mid.case0_mid_at] is a premise. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c
  strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.RoleBuild Require Import EntCut EntFacts Ent0Mid Ent0C.
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
Variables (sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.
Hypothesis STRL : strlen_contract.
Hypothesis MID : case0_mid_at sp gp tp s11 F fc m r src pp lo.

Lemma case0_ok_sec : case_at sp gp tp s11 F fc m r src pp lo 0 0x133d0.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 b rest m1 Er Hk Hs MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  destruct rest as [|cb [|pb rest2]].
  - (* only kind: c = p = 0 *)
    assert (L : length r = 1%nat) by (rewrite Er; reflexivity).
    (* 0x133d0 beqz s6 -> 0x13874 mv s9,s5; 0x13878 addi a7,sp,0x120; addi t0,zero,9; addi t1,zero,10;
       mv s1,zero; mv s7,zero; mv a0,zero *)
    step. brt. do 7 step.
    eapply (digits_ok sp gp tp s11 F fc m r src pp lo HE MID 0 0 []);
      [ lia | lia | rewrite Er, (ent0_b b Hk); reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | f_equal; rewrite L; cbn [length]; lia | reflexivity | reflexivity | exact MC ].
  - (* kind and c: p = 0 *)
    assert (L : length r = 2%nat) by (rewrite Er; reflexivity).
    (* 0x133d0 beqz s6; addi s5,s5,1; addi a0,zero,1; addi a7,sp,0x120; addi t0,zero,9; addi t1,zero,10;
       bgeu a0,s5 (trap) *)
    step. brf. do 6 step. brf.
    (* 0x133ec lbu a0,1(s9): c *)
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 1 MC ltac:(lia)) as HB. rewrite Er in HB. cbn [nth] in HB.
    step. clear HB.
    (* 0x133f0 addi s5,s9,2; addi a1,zero,2; bne s1,a1 (two bytes: not taken) *)
    do 3 step. brf.
    (* 0x133fc mv s1,zero; mv s7,zero; j 0x13a3c *)
    do 3 step.
    pose proof (byte_range cb) as Hcb.
    eapply (c_ok sp gp tp s11 F fc m r src pp lo HE MCPY STRL MID (bv_unsigned cb) 0 []);
      [ lia | lia | rewrite Er, (ent0_c1 b cb Hk); reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | f_equal; rewrite L; cbn [length]; lia | reflexivity | exact MC ].
  - (* kind, c, p *)
    assert (L : length r = S (S (S (length rest2)))) by (rewrite Er; reflexivity).
    step. brf. do 6 step. brf.
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 1 MC ltac:(lia)) as HB. rewrite Er in HB. cbn [nth] in HB.
    step. clear HB.
    (* 0x133f0 addi s5,s9,2; addi a1,zero,2; bne s1,a1 (taken) *)
    do 3 step. brt.
    (* 0x13a24 addi s5,s5,1; addi a1,zero,1; bgeu a1,s5 (trap) *)
    do 3 step. brf.
    (* 0x13a30 lbu s7,2(s9): p *)
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 2 MC ltac:(lia)) as HB. rewrite Er in HB. cbn [nth] in HB.
    step. clear HB.
    (* 0x13a34 addi s1,s1,-3; addi s5,s9,3 *)
    do 2 step.
    pose proof (byte_range cb) as Hcb. pose proof (byte_range pb) as Hpb.
    eapply (c_ok sp gp tp s11 F fc m r src pp lo HE MCPY STRL MID (bv_unsigned cb) (bv_unsigned pb) rest2);
      [ lia | lia | rewrite Er, (ent0_cp b cb pb rest2 Hk); reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | f_equal; rewrite L; lia | f_equal; rewrite L; lia | reflexivity | exact MC ].
Qed.

Lemma case0_nil_sec : case0_nil_at sp gp tp s11 F fc m r src pp lo.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 m1 Er MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13878 addi a7,sp,0x120; addi t0,zero,9; addi t1,zero,10; mv s1,zero; mv s7,zero; mv a0,zero *)
  do 6 step.
  eapply (digits_ok sp gp tp s11 F fc m r src pp lo HE MID 0 0 []);
    [ lia | lia | rewrite Er; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | f_equal; rewrite Er; cbn [length]; lia | f_equal; rewrite Er; cbn [length]; lia | reflexivity
    | exact MC ].
Qed.

End Case0.

Theorem case0_ok : forall (sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (r : list byte) (src pp lo : Z),
  ent_pre sp m r src pp lo -> memcpy_contract -> strlen_contract -> case0_mid_at sp gp tp s11 F fc m r src pp lo ->
  case_at sp gp tp s11 F fc m r src pp lo 0 0x133d0.
Proof. intros. apply case0_ok_sec; assumption. Qed.

Theorem case0_nil_ok : forall (sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (r : list byte) (src pp lo : Z),
  ent_pre sp m r src pp lo -> memcpy_contract -> strlen_contract -> case0_mid_at sp gp tp s11 F fc m r src pp lo ->
  case0_nil_at sp gp tp s11 F fc m r src pp lo.
Proof. intros. apply case0_nil_sec; assumption. Qed.
