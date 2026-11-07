(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib Require Import NElim. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require RegFold. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require RProgAt. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require JunkAbs.


From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.H Require Import GldProof.
Import ListNotations.
Open Scope bv_scope.


Definition gldp_prog : RStep.ptree :=
  (PNode 112%Z
    (PNode 56%Z
      (PNode 28%Z
        (PLeaf
          (PJ_Store_SZ4_nnn 0 12 0 0 4
          (PJ_Branch_BC_GE_nnn 4 0 11 52 4
          (PJ_Load_SZ1_true_nnn 8 13 10 0 4
          (PJ_Branch_BC_LT_nnn 12 13 0 52 4
          (PJ_OpImm_ALU_ADD_nnn 16 13 0 1 4
          (PJ_Store_SZ4_nnn 20 12 13 0 4
          (PJ_Load_SZ1_false_nnn 24 14 10 0 4 nil))))))))
        (PLeaf
          (PJ_Branch_BC_LT_nnn 28 13 0 64 4
          (PJ_Lui_nn 32 10 524288 4
          (PJ_OpImm32_nnn 36 10 10 4095 4
          (PJ_Op_ALU_XOR_nnn 40 10 13 10 4
          (PJ_Branch_BC_GEU_nnn 44 10 14 48 4
          (PJ_OpImm_ALU_ADD_nnn 48 10 0 4094 4
          (PJ_Jalr_nnn 52 0 1 0 4 nil)))))))))
      (PNode 84%Z
        (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 56 10 0 0 4
          (PJ_Jalr_nnn 60 0 1 0 4
          (PJ_OpImm_ALU_AND_nnn 64 13 13 255 4
          (PJ_OpImm_ALU_AND_nnn 68 14 13 127 4
          (PJ_Branch_BC_EQ_nnn 72 14 0 40 4
          (PJ_OpImm_ALU_ADD_nnn 76 13 0 1 4
          (PJ_Branch_BC_NE_nnn 80 11 13 48 4 nil))))))))
        (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 84 14 0 0 4
          (PJ_Store_SZ4_nnn 88 12 13 0 4
          (PJ_Op32_ALU_ADD_nnn 92 13 13 14 4
          (PJ_Branch_BC_GE_nnn 96 11 13 8 4
          (PJ_OpImm_ALU_ADD_nnn 100 14 0 4092 4
          (PJ_OpImm_ALU_ADD_nnn 104 10 14 0 4
          (PJ_Jalr_nnn 108 0 1 0 4 nil))))))))))
    (PNode 168%Z
      (PNode 140%Z
        (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 112 10 0 1 4
          (PJ_Store_SZ4_nnn 116 12 10 0 4
          (PJ_OpImm_ALU_ADD_nnn 120 10 0 4095 4
          (PJ_Jalr_nnn 124 0 1 0 4
          (PJ_OpImm_ALU_ADD_nnn 128 13 14 4095 4
          (PJ_OpImm32_nnn 132 14 11 4094 4
          (PJ_Branch_BC_LTU_nnn 136 13 14 8 4 nil))))))))
        (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 140 13 14 0 4
          (PJ_OpImm_ALU_ADD_nnn 144 14 0 0 4
          (PJ_OpImm32_nnn 148 13 13 2 4
          (PJ_ShiftImm_ALU_SLL_nnn 152 15 13 32 4
          (PJ_ShiftImm_ALU_SRL_nnn 156 16 15 32 4
          (PJ_OpImm_ALU_ADD_nnn 160 15 10 1 4
          (PJ_OpImm_ALU_ADD_nnn 164 16 16 4095 4 nil)))))))))
      (PNode 196%Z
        (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 168 10 0 4094 4
          (PJ_ShiftImm32_ALU_SRL_nnn 172 17 14 24 4
          (PJ_Branch_BC_NE_nnn 176 17 0 8068 4
          (PJ_Load_SZ1_false_nnn 180 17 15 0 4
          (PJ_ShiftImm32_ALU_SLL_nnn 184 14 14 8 4
          (PJ_OpImm_ALU_ADD_nnn 188 16 16 4095 4
          (PJ_Op_ALU_OR_nnn 192 14 14 17 4 nil))))))))
        (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 196 15 15 1 4
          (PJ_Branch_BC_NE_nnn 200 16 0 8164 4
          (PJ_Lui_nn 204 15 524288 4
          (PJ_OpImm32_nnn 208 15 15 4094 4
          (PJ_Store_SZ4_nnn 212 12 13 0 4
          (PJ_Branch_BC_GEU_nnn 216 15 14 8004 4
          (PJ_Jal_nn 220 0 2096984 4 nil))))))))))).

Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.solve_load ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.solve_cond ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.step ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.stepz ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.simp_regs ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.

Ltac blia := rewrite ?andb_false_iff, ?andb_true_iff, ?orb_false_iff, ?orb_true_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq, ?Z.eqb_neq; lia.
Ltac brk H := if_cases H; zify_cond H.

(* The plain build of the same function: identical control flow without the five
   UBSan checks, so none of the non-null or alignment hypotheses are needed. *)
Section Img.
  Context {IMG : RImg}.
  Context {CODE_gldp : CodeAtT img_segs (sym 0x12a7c) gldp_prog}.
  Context {RB_gldp : RelCode (sym 0x12a7c) 224}.
  Collection ImgHyps := IMG CODE_gldp RB_gldp.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (p q : word) (der : list byte) (m : word -> option byte).
  Hypothesis LEN : (1 <= length der <= 512)%nat.
  Hypothesis DISJ : (bv_unsigned q + 4 <= bv_unsigned p \/ bv_unsigned p + Z.of_nat (length der) <= bv_unsigned q)%Z.
  Abbreviation W := [(bv_unsigned q, bv_unsigned q + 4)%Z].
  Abbreviation POST := (gld_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p q der m).
  Abbreviation ST off r a3 a4 a5 a6 a7 mm :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r (Z_to_bv 64 (Z.of_nat (length der))) q a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x12a7c + off)) fc None mm (seg_rom img_segs)).

  (* 0x12ad8: sum = ans + *len (a 32-bit add that cannot trap here), then sum > der_len. *)
  Lemma gldp_tail : forall mm v (X : word) (L : Z) r a5 a6 a7,
    bytes_at img_segs mm (bv_unsigned p) der -> rw_cells img_segs mm (bv_unsigned q) [C4 v] -> munch W m mm -> wmono img_segs m mm ->
    evt img_segs POST (ST 92 r (Z_to_bv 64 L) X a5 a6 a7 mm).
  Proof.
    intros mm v X L r a5 a6 a7 DER LC MU WM.
    zstep. zstep. brk K.
    - zstep. zstep. finish. eassumption.
    - zstep. zstep. zstep. finish. eassumption.
  Qed.

  (* 0x12a98: the INT_MAX guard, (INT_MAX xor len) >=u ans. *)
  Lemma gldp_guard : forall mm v (X : word) (L : Z) r a5 a6 a7,
    bytes_at img_segs mm (bv_unsigned p) der -> rw_cells img_segs mm (bv_unsigned q) [C4 v] -> munch W m mm -> wmono img_segs m mm ->
    (1 <= L <= 128)%Z ->
    evt img_segs POST (ST 28 r (Z_to_bv 64 L) X a5 a6 a7 mm).
  Proof.
    intros mm v X L r a5 a6 a7 DER LC MU WM HL.
    zstep. brk K. { exfalso. revert K. blia. }
    zstep. zstep. zstep. zstep. brk K2.
    - eapply gldp_tail; eauto.
    - zstep. zstep. finish. eassumption.
  Qed.

  (* 0x12b28: the definite-length loop; a3 = *len to be, a4 = accumulator. *)
  Lemma gldp_loop : forall (n : nat) (i L : Z) mm v (Acc : word) T,
    n = Z.to_nat (L - 1 - i) -> (0 <= i < L - 1)%Z -> (2 <= L <= 128)%Z -> (L <= Z.of_nat (length der))%Z ->
    bytes_at img_segs mm (bv_unsigned p) der -> rw_cells img_segs mm (bv_unsigned q) [C4 v] -> munch W m mm -> wmono img_segs m mm ->
    evt img_segs POST (ST 172 (Z_to_bv 64 (-2)) (Z_to_bv 64 L) Acc
                          (Z_to_bv 64 (bv_unsigned p + 1 + i)) (Z_to_bv 64 (L - 1 - i)) T mm).
  Proof.
    induction n as [|n IH]; intros i L mm v Acc T Hn Hi HL HLd DER LC MU WM; [lia|].
    pose proof (bytes_at_bound _ _ _ _ DER) as PB.
    zstep. zstep. brk K. { zstep. finish. eassumption. }
    destruct (nth_error der (Z.to_nat (1 + i))) as [b|] eqn:Nb; [|apply nth_error_None in Nb; lia].
    pose proof (u8ro_read img_segs mm (bv_unsigned p) der (1 + i) b _ DER Nb ltac:(lia) ltac:(f_equal; lia)) as RD.
    zstep. zstep. zstep. zstep. zstep. zstep. brk K3.
    - replace (bv_unsigned p + 1 + i + 1)%Z with (bv_unsigned p + 1 + (i + 1))%Z by lia.
      replace (L - 1 - i + -1)%Z with (L - 1 - (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z L mm v); eauto; lia.
    - zstep. zstep. zstep. zstep. brk K4.
      + eapply gldp_guard; eauto; lia.
      + zstep. zstep. finish. eassumption.
  Qed.
End Proofs.

Lemma gldp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (der : list byte) (bs : list byte),
  bytes_at img_segs m (bv_unsigned a0) der ->
  a1 = Z_to_bv 64 (Z.of_nat (length der)) -> (length der <= 512)%nat ->
  rw_cells img_segs m (bv_unsigned a2) [CB 4 bs] ->
  (bv_unsigned a2 + 4 <= bv_unsigned a0 \/ bv_unsigned a0 + Z.of_nat (length der) <= bv_unsigned a2)%Z ->
  evt img_segs (gld_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 der m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x12a7c)) fc None m (seg_rom img_segs)).
Proof.
  intros until bs. intros DER -> LEN LC DISJ.
  pose proof (munch_refl [(bv_unsigned a2, bv_unsigned a2 + 4)%Z] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ DER) as PB.
  zstep.   (* *len = 0 *)
  destruct (Nat.eq_dec (length der) 0) as [L0|L0].
  { rewrite L0. zstep. if_true. zstep. zstep. finish. eassumption. }
  zstep. brk K3. { exfalso. revert K3. blia. }
  destruct (nth_error der 0) as [b0|] eqn:N0; [|apply nth_error_None in N0; lia].
  pose proof (u8ro_read img_segs _ (bv_unsigned a0) der 0 b0 a0 DER N0 ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
  zstep. zstep. brk K5.
  2:{ (* short form *)
    zstep. zstep. clear RD.
    match goal with D : bytes_at _ ?mm (bv_unsigned a0) der |- _ =>
      pose proof (u8ro_read img_segs mm (bv_unsigned a0) der 0 b0 a0 D N0 ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD end.
    zstep. eapply gldp_guard; eauto; lia. }
  zstep. zstep.
  remember (Z.land (Z.land (bv_unsigned (sxb b0)) 255) 127) as k eqn:Ek.
  assert (Hk : (0 <= k <= 127)%Z).
  { subst k. set (x := Z.land (bv_unsigned (sxb b0)) 255).
    replace (Z.land x 127) with (x mod 2^7) by (change 127%Z with (Z.ones 7); rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z.mod_pos_bound x (2^7) ltac:(lia)). lia. }
  clear Ek.
  zstep. brk K6.
  { zstep. zstep. zstep. zstep. finish. eassumption. }
  zstep. zstep. brk K7.
  2:{ zstep. zstep. eapply gldp_tail; eauto; lia. }
  zstep. zstep.
  rewrite (bv_swrap_small 32 (Z.of_nat (length der) + -2)) by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  zstep. brk K8.
  - zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (bv_swrap_small 32 (k + 1)) by (change (bv_half_modulus 32) with (2^31)%Z; lia).
    replace (((k + 1) mod 18446744073709551616) mod 4294967296 + -1)%Z with ((k + 1) - 1 - 0)%Z
      by (rewrite !Z.mod_small by lia; lia).
    replace (bv_unsigned a0 + 1)%Z with (bv_unsigned a0 + 1 + 0)%Z by lia.
    eapply gldp_loop with (i := 0%Z) (L := (k + 1)%Z); eauto; lia.
  - zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite Z.add_0_r.
    rewrite (bv_swrap_small 32 (Z.of_nat (length der))) by (change (bv_half_modulus 32) with (2^31)%Z; lia).
    replace ((Z.of_nat (length der) mod 18446744073709551616) mod 4294967296 + -1)%Z
      with (Z.of_nat (length der) - 1 - 0)%Z by (rewrite !Z.mod_small by lia; lia).
    replace (bv_unsigned a0 + 1)%Z with (bv_unsigned a0 + 1 + 0)%Z by lia.
    eapply gldp_loop with (i := 0%Z) (L := Z.of_nat (length der)); eauto; lia.
Qed.
End Img.
