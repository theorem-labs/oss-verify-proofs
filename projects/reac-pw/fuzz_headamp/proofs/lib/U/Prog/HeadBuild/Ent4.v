(** ent_build's kind 4 in the UBSan image (pod.h:326-332): a Bool of v % 3, v = fuzz_u8. From the jump table's
    target 0x1356c to the join 0x13df0 (through 0x138c8 when no byte is left, 0x138d0 and 0x139c4). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

Section Case4.
Variables (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Lemma case4_ok_sec : case_at sp gp tp s1 F fc m r src pp lo 4 0x1356c.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 b rest m1 Er Hk Hs MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  destruct rest as [|c rest].
  - (* no byte for v: v = 0 *)
    assert (L : length r = 1%nat) by (rewrite Er; reflexivity).
    (* 0x1356c beqz s6 *)
    step. brt.
    (* 0x138c8 mv s2,zero; mv a0,zero; addi a1,zero,2 *)
    do 3 step.
    (* 0x138d4 sw a1,0xb8(sp); sw s11,0xbc(sp); sw a0,0xc0(sp) *)
    est_t HE MC. est_sz HE MC. est_bd HE MC (bv_unsigned sp + 192) 0%nat 4%nat.
    (* 0x138e0 j; 0x139c4 mv s10,s5; j *)
    do 3 step.
    eapply join_13df0; [eb_tac Er Hk | | | reflexivity | exact MC | | | ].
    + reflexivity.
    + f_equal. rewrite L. cbn [length]. lia.
    + apply le4_le32.
    + apply le4_le32.
    + vm_compute. reflexivity.
  - assert (L : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    (* 0x1356c beqz s6; addi s5,s5,1; addi a0,zero,1; bltu a0,s5,8 over the trap (taken) *)
    step. brf. do 2 step. step. brt.
    (* 0x13580 lbu a0,1(s10) *)
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 1 MC ltac:(lia)) as HB1. rewrite Er in HB1. cbn [nth] in HB1.
    step.
    (* 0x13584 addi s2,s2,-2; addi s5,s10,2; v % 3 (0x1358c-0x135a4); j 0x138d0 *)
    do 10 step.
    match goal with |- context [Z_to_bv 64 (Z.land ?X 255)] =>
      replace (Z.land X 255) with (bv_unsigned c mod 3) by (symmetry; byte_eq c) end.
    (* 0x138d0 addi a1,zero,2; sw a1,0xb8(sp); sw s11,0xbc(sp); sw a0,0xc0(sp) *)
    step. est_t HE MC. est_sz HE MC. est_bd HE MC (bv_unsigned sp + 192) 0%nat 4%nat.
    do 3 step.
    eapply join_13df0; [eb_tac Er Hk | | | reflexivity | exact MC | | | ].
    + f_equal. rewrite L. lia.
    + f_equal. rewrite L. lia.
    + apply le4_le32.
    + apply le4_le32.
    + cbn [e_body]. rewrite le4_le32, length_le32. apply upd_zeros0. rewrite length_le32. lia.
Qed.

End Case4.

Theorem case4_ok : forall (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (r : list byte) (src pp lo : Z),
  ent_pre sp m r src pp lo -> case_at sp gp tp s1 F fc m r src pp lo 4 0x1356c.
Proof. intros. apply case4_ok_sec; assumption. Qed.
