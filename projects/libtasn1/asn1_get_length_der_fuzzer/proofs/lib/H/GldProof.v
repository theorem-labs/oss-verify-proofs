(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib Require Import NElim. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require RegFold. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require RProgAt. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require JunkAbs.


Import ListNotations.
Open Scope bv_scope.


Definition gld_prog : RStep.ptree :=
  (PNode 132%Z
    (PNode 64%Z
      (PNode 32%Z
        (PLeaf
          (PJ_Branch_BC_EQ_nnn 0 12 0 264 4
          (PJ_OpImm_ALU_AND_nnn 4 13 12 3 4
          (PJ_Branch_BC_NE_nnn 8 13 0 256 4
          (PJ_Store_SZ4_nnn 12 12 0 0 4
          (PJ_Branch_BC_GE_nnn 16 0 11 56 4
          (PJ_Branch_BC_EQ_nnn 20 10 0 244 4
          (PJ_Load_SZ1_true_nnn 24 13 10 0 4
          (PJ_Branch_BC_LT_nnn 28 13 0 52 4 nil)))))))))
        (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 32 14 0 1 4
          (PJ_Store_SZ4_nnn 36 12 14 0 4
          (PJ_Load_SZ1_false_nnn 40 13 10 0 4
          (PJ_Branch_BC_LT_nnn 44 14 0 64 4
          (PJ_Lui_nn 48 10 524288 4
          (PJ_OpImm32_nnn 52 10 10 4095 4
          (PJ_Op_ALU_XOR_nnn 56 10 14 10 4
          (PJ_Branch_BC_GEU_nnn 60 10 13 48 4 nil))))))))))
      (PNode 96%Z
        (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 64 10 0 4094 4
          (PJ_Jalr_nnn 68 0 1 0 4
          (PJ_OpImm_ALU_ADD_nnn 72 10 0 0 4
          (PJ_Jalr_nnn 76 0 1 0 4
          (PJ_OpImm_ALU_AND_nnn 80 13 13 255 4
          (PJ_OpImm_ALU_AND_nnn 84 13 13 127 4
          (PJ_Branch_BC_EQ_nnn 88 13 0 52 4
          (PJ_OpImm_ALU_ADD_nnn 92 14 0 1 4 nil)))))))))
        (PNode 112%Z
          (PLeaf
            (PJ_Branch_BC_NE_nnn 96 11 14 60 4
            (PJ_OpImm_ALU_ADD_nnn 100 13 0 0 4
            (PJ_Store_SZ4_nnn 104 12 14 0 4
            (PJ_Op_ALU_ADD_nnn 108 10 13 14 4 nil)))))
          (PLeaf
            (PJ_Op32_ALU_ADD_nnn 112 14 13 14 4
            (PJ_Branch_BC_NE_nnn 116 14 10 148 4
            (PJ_OpImm32_nnn 120 10 10 0 4
            (PJ_Branch_BC_GE_nnn 124 11 10 8 4
            (PJ_OpImm_ALU_ADD_nnn 128 13 0 4092 4 nil)))))))))
    (PNode 196%Z
      (PNode 164%Z
        (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 132 10 13 0 4
          (PJ_Jalr_nnn 136 0 1 0 4
          (PJ_OpImm_ALU_ADD_nnn 140 10 0 1 4
          (PJ_Store_SZ4_nnn 144 12 10 0 4
          (PJ_OpImm_ALU_ADD_nnn 148 10 0 4095 4
          (PJ_Jalr_nnn 152 0 1 0 4
          (PJ_OpImm_ALU_ADD_nnn 156 14 13 4095 4
          (PJ_OpImm32_nnn 160 13 11 4094 4 nil)))))))))
        (PLeaf
          (PJ_Branch_BC_LTU_nnn 164 14 13 8 4
          (PJ_OpImm_ALU_ADD_nnn 168 14 13 0 4
          (PJ_OpImm_ALU_ADD_nnn 172 13 0 0 4
          (PJ_OpImm32_nnn 176 14 14 2 4
          (PJ_ShiftImm_ALU_SLL_nnn 180 15 14 32 4
          (PJ_ShiftImm_ALU_SRL_nnn 184 16 15 32 4
          (PJ_OpImm_ALU_ADD_nnn 188 15 10 1 4
          (PJ_OpImm_ALU_ADD_nnn 192 16 16 4095 4 nil))))))))))
      (PNode 228%Z
        (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 196 17 15 0 4
          (PJ_OpImm_ALU_ADD_nnn 200 10 0 4094 4
          (PJ_ShiftImm32_ALU_SRL_nnn 204 5 13 24 4
          (PJ_Branch_BC_NE_nnn 208 5 0 8052 4
          (PJ_Branch_BC_EQ_nnn 212 17 0 52 4
          (PJ_Load_SZ1_false_nnn 216 5 15 0 4
          (PJ_ShiftImm32_ALU_SLL_nnn 220 13 13 8 4
          (PJ_OpImm_ALU_ADD_nnn 224 17 17 1 4 nil)))))))))
        (PNode 244%Z
          (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 228 16 16 4095 4
            (PJ_Op_ALU_OR_nnn 232 13 13 5 4
            (PJ_OpImm_ALU_ADD_nnn 236 15 15 1 4
            (PJ_Branch_BC_NE_nnn 240 16 0 8156 4 nil)))))
          (PLeaf
            (PJ_Lui_nn 244 15 524288 4
            (PJ_OpImm32_nnn 248 15 15 4094 4
            (PJ_Store_SZ4_nnn 252 12 14 0 4
            (PJ_Branch_BC_GEU_nnn 256 15 13 7980 4
            (PJ_Jal_nn 260 0 2096960 4 nil)))))))))).

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

(* The compiler writes INT_MAX - len as INT_MAX xor len; they agree for 0 <= len < 2^31. *)
Lemma lxor_int_max : forall L, (0 <= L < 2^31)%Z -> Z.lxor L 2147483647 = (2147483647 - L)%Z.
Proof.
  intros L HL. change 2147483647%Z with (Z.ones 31).
  assert (E : Z.lxor L (Z.ones 31) = (Z.lnot L) mod 2^31).
  { rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases i 31).
    - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
      apply (testbit_high_false L 31); lia. }
  rewrite E. unfold Z.lnot. rewrite Z.ones_equiv.
  replace (Z.pred (- L)) with ((2^31 - 1 - L) + (-1) * 2^31)%Z by lia.
  rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

Section Img.
  Context {IMG : RImg}.
  Context {CODE_gld : CodeAtT img_segs (sym 0x12a7c) gld_prog}.
  Context {RB_gld : RelCode (sym 0x12a7c) 264}.
  Collection ImgHyps := IMG CODE_gld RB_gld.

(* After the call: every callee-saved register is unchanged, control is back at ra,
   memory differs from the original only in the 4 bytes of *len, the input bytes are
   intact, and *len still holds a 4-byte cell. *)
Definition gld_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p q : word) (der : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 r a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' v',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned q, bv_unsigned q + 4)%Z] m m' /\ wmono img_segs m m'
    /\ bytes_at img_segs m' (bv_unsigned p) der /\ rw_cells img_segs m' (bv_unsigned q) [C4 v'].

Section Proofs.
  Variables (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (p q : word) (der : list byte) (m : word -> option byte).
  Hypothesis LEN : (1 <= length der <= 512)%nat.
  Hypothesis DISJ : (bv_unsigned q + 4 <= bv_unsigned p \/ bv_unsigned p + Z.of_nat (length der) <= bv_unsigned q)%Z.
  Abbreviation W := [(bv_unsigned q, bv_unsigned q + 4)%Z].
  Abbreviation POST := (gld_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p q der m).
  Abbreviation ST off t0 r a3 a4 a5 a6 a7 mm :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r (Z_to_bv 64 (Z.of_nat (length der))) q a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x12a7c + off)) fc None mm (seg_rom img_segs)).

  (* 0x12ae8: sum = ans + *len, with the UBSan signed-overflow check on the 32-bit add,
     then the sum > der_len test.  ans + *len <= INT_MAX is what rules the trap out. *)
  Lemma gld_tail : forall mm v (X : word) (L : Z) t0 r a5 a6 a7,
    bytes_at img_segs mm (bv_unsigned p) der -> rw_cells img_segs mm (bv_unsigned q) [C4 v] -> munch W m mm -> wmono img_segs m mm ->
    (1 <= L <= 128)%Z -> (bv_unsigned X <= 2147483647 - L)%Z ->
    evt img_segs POST (ST 108 t0 r X (Z_to_bv 64 L) a5 a6 a7 mm).
  Proof.
    intros mm v X L t0 r a5 a6 a7 DER LC MU WM HL HX.
    pose proof (bv_unsigned_in_range 64 X) as RX. unfold bv_modulus in RX.
    zstep. zstep. zstep.
    rewrite (bv_swrap_small 32 (bv_unsigned X + L)) by (change (bv_half_modulus 32) with (2^31)%Z; lia).
    brk K. { exfalso. apply K. reflexivity. }
    zstep. zstep. brk K2.
    - zstep. zstep. finish. eassumption.
    - zstep. zstep. zstep. finish. eassumption.
  Qed.

  (* 0x12aa8: the ans >= INT_MAX / INT_ADD_OVERFLOW guard, compiled as
     (INT_MAX xor len) >=u ans. *)
  Lemma gld_guard : forall mm v (X : word) (L : Z) t0 r a5 a6 a7,
    bytes_at img_segs mm (bv_unsigned p) der -> rw_cells img_segs mm (bv_unsigned q) [C4 v] -> munch W m mm -> wmono img_segs m mm ->
    (1 <= L <= 128)%Z ->
    evt img_segs POST (ST 44 t0 r X (Z_to_bv 64 L) a5 a6 a7 mm).
  Proof.
    intros mm v X L t0 r a5 a6 a7 DER LC MU WM HL.
    zstep. brk K. { exfalso. revert K. blia. }
    zstep. zstep. zstep. zstep. brk K2.
    - rewrite lxor_int_max in K2 by lia. eapply gld_tail; eauto.
    - zstep. zstep. finish. eassumption.
  Qed.

  (* 0x12b48: the definite-length loop.  i bytes after the first have been consumed,
     L - 1 - i iterations remain, and a5 = a7 = &der[1 + i].  Only the bounds matter:
     the accumulator is left arbitrary. *)
  Lemma gld_loop : forall (n : nat) (i L : Z) mm v (Acc : word) T,
    n = Z.to_nat (L - 1 - i) -> (0 <= i < L - 1)%Z -> (2 <= L <= 128)%Z -> (L <= Z.of_nat (length der))%Z ->
    bytes_at img_segs mm (bv_unsigned p) der -> rw_cells img_segs mm (bv_unsigned q) [C4 v] -> munch W m mm -> wmono img_segs m mm ->
    evt img_segs POST (ST 204 T (Z_to_bv 64 (-2)) Acc (Z_to_bv 64 L)
                          (Z_to_bv 64 (bv_unsigned p + 1 + i)) (Z_to_bv 64 (L - 1 - i))
                          (Z_to_bv 64 (bv_unsigned p + 1 + i)) mm).
  Proof.
    induction n as [|n IH]; intros i L mm v Acc T Hn Hi HL HLd DER LC MU WM; [lia|].
    pose proof (bytes_at_bound _ _ _ _ DER) as PB.
    zstep. zstep. brk K. { zstep. finish. eassumption. }
    zstep. brk K2. { exfalso. lia. }
    destruct (nth_error der (Z.to_nat (1 + i))) as [b|] eqn:Nb; [|apply nth_error_None in Nb; lia].
    pose proof (u8ro_read img_segs mm (bv_unsigned p) der (1 + i) b _ DER Nb ltac:(lia) ltac:(f_equal; lia)) as RD.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. brk K3.
    - replace (bv_unsigned p + 1 + i + 1)%Z with (bv_unsigned p + 1 + (i + 1))%Z by lia.
      replace (L - 1 - i + -1)%Z with (L - 1 - (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z L mm v); eauto; lia.
    - zstep. zstep. zstep. zstep. brk K4.
      + eapply gld_guard; eauto; lia.
      + zstep. zstep. finish. eassumption.
  Qed.
End Proofs.

Lemma gld_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (der : list byte) (bs : list byte),
  bytes_at img_segs m (bv_unsigned a0) der ->
  bv_unsigned a0 <> 0%Z ->
  a1 = Z_to_bv 64 (Z.of_nat (length der)) -> (length der <= 512)%nat ->
  rw_cells img_segs m (bv_unsigned a2) [CB 4 bs] ->
  bv_unsigned a2 <> 0%Z -> (bv_unsigned a2 mod 4 = 0)%Z ->
  (bv_unsigned a2 + 4 <= bv_unsigned a0 \/ bv_unsigned a0 + Z.of_nat (length der) <= bv_unsigned a2)%Z ->
  evt img_segs (gld_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 der m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x12a7c)) fc None m (seg_rom img_segs)).
Proof.
  intros until bs. intros DER A0NZ -> LEN LC A2NZ A2AL DISJ.
  pose proof (munch_refl [(bv_unsigned a2, bv_unsigned a2 + 4)%Z] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ DER) as PB.
  (* UBSan: len != NULL and len 4-byte aligned *)
  zstep. brk K. { exfalso. apply A2NZ. revert K. zb_masks. lia. }
  zstep. zstep. brk K2.
  { exfalso. apply K2. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. exact A2AL. }
  zstep.   (* *len = 0 *)
  destruct (Nat.eq_dec (length der) 0) as [L0|L0].
  { (* der_len <= 0: return 0 *) rewrite L0. zstep. if_true. zstep. zstep. finish. eassumption. }
  zstep. brk K3. { exfalso. revert K3. blia. }
  (* UBSan: der != NULL *)
  zstep. brk K4. { exfalso. exact (A0NZ K4). }
  destruct (nth_error der 0) as [b0|] eqn:N0; [|apply nth_error_None in N0; lia].
  pose proof (u8ro_read img_segs _ (bv_unsigned a0) der 0 b0 a0 DER N0 ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
  zstep. zstep. brk K5.
  2:{ (* short form: *len = 1, ans = der[0] *)
    zstep. zstep. clear RD.
    match goal with D : bytes_at _ ?mm (bv_unsigned a0) der |- _ =>
      pose proof (u8ro_read img_segs mm (bv_unsigned a0) der 0 b0 a0 D N0 ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD end.
    zstep. eapply gld_guard; eauto; lia. }
  (* long form *)
  zstep. zstep.
  remember (Z.land (Z.land (bv_unsigned (sxb b0)) 255) 127) as k eqn:Ek.
  assert (Hk : (0 <= k <= 127)%Z).
  { subst k. set (x := Z.land (bv_unsigned (sxb b0)) 255).
    replace (Z.land x 127) with (x mod 2^7) by (change 127%Z with (Z.ones 7); rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z.mod_pos_bound x (2^7) ltac:(lia)). lia. }
  clear Ek.
  zstep. brk K6.
  { (* indefinite length: *len = 1, return -1 *) zstep. zstep. zstep. zstep. finish. eassumption. }
  zstep. zstep. brk K7.
  2:{ (* der_len = 1: ans = 0, *len = 1 *)
    zstep. zstep. eapply gld_tail; eauto; try lia. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. }
  zstep. zstep.
  rewrite (bv_swrap_small 32 (Z.of_nat (length der) + -2)) by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  zstep. brk K8.
  - (* k - 1 < der_len - 2: the loop reads k bytes *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (bv_swrap_small 32 (k + 1)) by (change (bv_half_modulus 32) with (2^31)%Z; lia).
    replace (((k + 1) mod 18446744073709551616) mod 4294967296 + -1)%Z with ((k + 1) - 1 - 0)%Z
      by (rewrite !Z.mod_small by lia; lia).
    replace (bv_unsigned a0 + 1)%Z with (bv_unsigned a0 + 1 + 0)%Z by lia.
    eapply gld_loop with (i := 0%Z) (L := (k + 1)%Z); eauto; lia.
  - (* otherwise: the loop reads der_len - 1 bytes *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite Z.add_0_r.
    rewrite (bv_swrap_small 32 (Z.of_nat (length der))) by (change (bv_half_modulus 32) with (2^31)%Z; lia).
    replace ((Z.of_nat (length der) mod 18446744073709551616) mod 4294967296 + -1)%Z
      with (Z.of_nat (length der) - 1 - 0)%Z by (rewrite !Z.mod_small by lia; lia).
    replace (bv_unsigned a0 + 1)%Z with (bv_unsigned a0 + 1 + 0)%Z by lia.
    eapply gld_loop with (i := 0%Z) (L := Z.of_nat (length der)); eauto; lia.
Qed.
End Img.
