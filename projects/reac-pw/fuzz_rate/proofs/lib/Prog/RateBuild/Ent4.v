(** ent_build's kind 4 (pod.h:327-331): a Bool of v % 3, v = fuzz_u8. From the jump table's target 0x13770 to the
    join 0x13cec (through 0x139a8 when no byte is left, and 0x139b0, 0x13ae8). Ported from reac-pw/fuzz_role's
    Prog/RoleBuild/Ent4.v at rate's registers, frame cells and pcs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

Section Case4.
Variables (sp gp tp s2 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Lemma case4_ok : case_at sp gp tp s2 s9 F fc m r src pp lo 4 0x13770.
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 b rest m1 Er Hk Hs -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  mcells.
  (* 0x13770 ld a6,0xb0(sp); ld a7,0x98(sp); ld t0,0x90(sp); beqz s7 *)
  do 4 step.
  unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r) - 1)) by (rewrite Er in *; cbn [length] in *; lia).
  destruct rest as [|v rest].
  - (* no byte left: v = 0; 0x139a8 sd zero,0xa8(sp); mv a0,zero *)
    assert (Lr : length r = 1%nat) by (rewrite Er; reflexivity).
    if_true.
    pre_store HE (bv_unsigned sp + 168) 8%nat. step. mstore_out HE.
    step.
    (* 0x139b0 ld s1,0x80(sp); s5 = 2; s6 = 4; sw s5,0xb8(sp); sw s6,0xbc(sp); sw a0,0xc0(sp) *)
    mcells. do 3 step.
    pre_store HE (bv_unsigned sp + 184) 4%nat. step. mstore_e HE 0.
    pre_store HE (bv_unsigned sp + 188) 4%nat. step. mstore_e HE 4.
    pre_store HE (bv_unsigned sp + 192) 4%nat. step. mstore_e HE 8.
    (* mv s8,a5; j 0x13ae8; lui s7,0x4; j 0x13cec *)
    do 4 step.
    eapply join_13cec.
    + rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + f_equal. rewrite Lr. cbn [length Z.of_nat]. lia.
    + reflexivity.
    + eapply MemC_e_ext; [eassumption|]. rewrite !le4_any. reflexivity.
    + exact HW.
  - (* v = the byte after kind; 0x13780 lbu a0,1(s8) *)
    assert (Lr : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    if_false.
    assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 1)) 1 = Some [v]).
    { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 1 MC) by lia. rewrite Er. reflexivity. }
    step. clear HR.
    (* addi s6,s6,-2; sd s6,0xa8(sp) *)
    step.
    pre_store HE (bv_unsigned sp + 168) 8%nat. step. mstore_out HE.
    (* addi a5,s8,2; v % 3 (0x13790-0x137a8); j 0x139b0 *)
    do 9 step.
    match goal with |- context [Z.land ?E 255] =>
      replace (Z.land E 255) with (bv_unsigned v mod 3) by (clear - v; revert v; byte_eq) end.
    (* 0x139b0 ld s1,0x80(sp); s5 = 2; s6 = 4; sw s5,0xb8(sp); sw s6,0xbc(sp); sw a0,0xc0(sp) *)
    mcells. do 3 step.
    pre_store HE (bv_unsigned sp + 184) 4%nat. step. mstore_e HE 0.
    pre_store HE (bv_unsigned sp + 188) 4%nat. step. mstore_e HE 4.
    pre_store HE (bv_unsigned sp + 192) 4%nat. step. mstore_e HE 8.
    (* mv s8,a5; j 0x13ae8; lui s7,0x4; j 0x13cec *)
    do 4 step.
    eapply join_13cec.
    + rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + f_equal. rewrite Lr. cbn [length]. lia.
    + reflexivity.
    + eapply MemC_e_ext; [eassumption|]. rewrite !le4_any. reflexivity.
    + replace (Z.of_nat (length rest)) with (Z.of_nat (length r) + -2) by lia. exact HW.
Qed.

End Case4.
