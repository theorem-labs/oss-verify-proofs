(** ent_build's kind 4 (pod.h:327-331): a Bool of v % 3, v = fuzz_u8. From the jump table's target 0x13734 to the
    join 0x13618 (through 0x13940 when no byte is left, and 0x13948). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

Section Case4.
Variables (sp gp tp s1 s8 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Lemma case4_ok : case_at sp gp tp s1 s8 F fc m r src pp lo 4 0x13734.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 b rest m1 Er Hk Hs -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  mcells.
  (* 0x13734 ld a6,0x78(sp); ld a7,0x70(sp); beqz s5 *)
  do 3 step.
  unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r) - 1)) by (rewrite Er in *; cbn [length] in *; lia).
  destruct rest as [|v rest].
  - (* no byte left: v = 0; 0x13940 sd zero,0x88(sp); mv a0,zero *)
    assert (Lr : length r = 1%nat) by (rewrite Er; reflexivity).
    if_true.
    pre_store HE (bv_unsigned sp + 136) 8%nat. step. mstore_out HE.
    step.
    (* 0x13948 ld s2,0x50(sp); s3 = 2; s4 = 4; sw s3,0x90(sp); sw s4,0x94(sp); sw a0,0x98(sp) *)
    mcells. do 3 step.
    pre_store HE (bv_unsigned sp + 144) 4%nat. step. mstore_e HE 0.
    pre_store HE (bv_unsigned sp + 148) 4%nat. step. mstore_e HE 4.
    pre_store HE (bv_unsigned sp + 152) 4%nat. step. mstore_e HE 8.
    (* mv s6,a5; ld s5,0x58(sp); j 0x13618 *)
    mcells. do 3 step.
    eapply join_13618.
    + rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + f_equal. rewrite Lr. cbn [length Z.of_nat]. lia.
    + eapply MemC_e_ext; [eassumption|]. rewrite !le4_any. reflexivity.
    + exact HW.
  - (* v = the byte after kind; 0x13740 lbu a0,1(s6) *)
    assert (Lr : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    if_false.
    assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 1)) 1 = Some [v]).
    { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 1 MC) by lia. rewrite Er. reflexivity. }
    step. clear HR.
    (* addi s4,s4,-2; sd s4,0x88(sp) *)
    step.
    pre_store HE (bv_unsigned sp + 136) 8%nat. step. mstore_out HE.
    (* addi a5,s6,2; v % 3 (0x13750-0x13768); j 0x13948 *)
    do 9 step.
    match goal with |- context [Z.land ?E 255] =>
      replace (Z.land E 255) with (bv_unsigned v mod 3) by (clear - v; revert v; byte_eq) end.
    (* 0x13948 ld s2,0x50(sp); s3 = 2; s4 = 4; sw s3,0x90(sp); sw s4,0x94(sp); sw a0,0x98(sp) *)
    mcells. do 3 step.
    pre_store HE (bv_unsigned sp + 144) 4%nat. step. mstore_e HE 0.
    pre_store HE (bv_unsigned sp + 148) 4%nat. step. mstore_e HE 4.
    pre_store HE (bv_unsigned sp + 152) 4%nat. step. mstore_e HE 8.
    (* mv s6,a5; ld s5,0x58(sp); j 0x13618 *)
    mcells. do 3 step.
    eapply join_13618.
    + rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + f_equal. rewrite Lr. cbn [length]. lia.
    + eapply MemC_e_ext; [eassumption|]. rewrite !le4_any. reflexivity.
    + replace (Z.of_nat (length rest)) with (Z.of_nat (length r) + -2) by lia. exact HW.
Qed.

End Case4.
