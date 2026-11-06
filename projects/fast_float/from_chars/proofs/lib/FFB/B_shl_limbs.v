(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl Ubsan_chk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_shl_limbs_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_copy_bwd_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_shl_limbs_stmt.

Module B_asan_memmove2_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_rt_stmt.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation BSEGS := AsanUbsan.M.loaded_segments.

Definition asan_memmove2_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v : rt_vals) (bs old : list byte) (shlo shn shlo2 shn2 : Z),
    bytes_at BSEGS m (bv_unsigned a1) bs ->
    u8arr BSEGS m (bv_unsigned a0) old ->
    length old = length bs ->
    Z.of_nat (length bs) = bv_unsigned a2 ->
    (bv_unsigned a0 mod 8 = 0)%Z -> (bv_unsigned a1 mod 8 = 0)%Z -> (bv_unsigned a2 mod 8 = 0)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2 + 8))%Z -> (bv_unsigned a0 + bv_unsigned a2 + 8 <= KTOP)%Z ->
    (app2r (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2 + 8))%Z -> (bv_unsigned a1 + bv_unsigned a2 + 8 <= KTOP)%Z ->
    (bv_unsigned a2 <= 2^40)%Z ->
    shz BSEGS m (ASAN_B + bv_unsigned a0 / 8) (bv_unsigned a2 / 8) ->
    shz BSEGS m (ASAN_B + bv_unsigned a1 / 8) (bv_unsigned a2 / 8) ->
    rdbl BSEGS m shlo shn ->
    (shlo + 8 <= ASAN_B + bv_unsigned a0 / 8)%Z -> (ASAN_B + (bv_unsigned a0 + bv_unsigned a2) / 8 + 8 <= shlo + shn)%Z ->
    rdbl BSEGS m shlo2 shn2 ->
    (shlo2 + 8 <= ASAN_B + bv_unsigned a1 / 8)%Z -> (ASAN_B + (bv_unsigned a1 + bv_unsigned a2) / 8 + 8 <= shlo2 + shn2)%Z ->
    stk BSEGS m (bv_unsigned sp - IMEMMOVE_NEED) (bv_unsigned sp) ->
    (IMG_END <= bv_unsigned sp - IMEMMOVE_NEED)%Z -> (KHI <= bv_unsigned sp - IMEMMOVE_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned sp - IMEMMOVE_NEED)%Z ->
    (bv_unsigned sp <= bv_unsigned a1 \/ bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp - IMEMMOVE_NEED)%Z ->
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    RT m v -> rt_disj v (bv_unsigned sp - IMEMMOVE_NEED) (bv_unsigned sp) ->
    rt_disj v (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt BSEGS (asan_memmove_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a2) bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 B_IMEMMOVE) fc None m (seg_rom BSEGS)).

(* [comment removed for export] *)
Lemma asan_memmove2_to_1 : asan_memmove2_stmt -> asan_memmove_stmt.
Proof.
  unfold asan_memmove2_stmt, asan_memmove_stmt. intros H. intros.
  eapply H; eassumption.
Qed.
End B_asan_memmove2_stmt.

Module B_copy_bwd.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Ubsan_chk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_copy_bwd_impl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_copy_bwd_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac solve_W_ok_rt := solve_W_rt.  (* [comment removed for export] *)

Section Main.
  Hypothesis copy_bwd_impl_spec : copy_bwd_impl_stmt.

  #[using="copy_bwd_impl_spec"] Lemma copy_bwd_spec : copy_bwd_stmt.
  Proof. LiaFast.lf_pins (fun (copy_bwd_impl_spec : LiaFast.U) => LiaFast.u0).
    unfold copy_bwd_stmt. intros until shn2.
    intros ST Ha1 Ha2 Hn Hn8 SRC Lbs DST Lold A08 D8 RA KD1 KD2 KS1 KS2 SHD SHS RD RDL1 RDL2 RDs RDL3 RDL4
           SP1 SP2 SP3 AL16 SEPD SEPS PRG PRT RTH RDJ1 RDJ2.
    pose proof (munch_refl (copy_bwd_W (bv_unsigned sp) (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))
                                        (bv_unsigned a1 - bv_unsigned a0)) m) as MU.
    cbv delta [copy_bwd_W] in MU.
    replace (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))%Z with D in MU by lia.
    replace (bv_unsigned a1 - bv_unsigned a0)%Z with n in MU by lia.
    pose proof (wmono_refl BSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0.
    pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1.
    pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2.
    carve_frame 32%nat ST.
    do 4 step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply copy_bwd_impl_spec with (v := v) (n := n) (D := D) (bs := bs) (old := old)
                               (shlo := shlo) (shn := shn) (shlo2 := shlo2) (shn2 := shn2)
                      | post_call BSEGS mc ] end.
    all: rewrite ?ULs.
    1:{ replace (bv_unsigned sp + -32 - COPY_BWD_IMPL_NEED)%Z with (bv_unsigned sp - 2288)%Z by lia. exact ST. }
    1:{ exact Ha1. } 1:{ exact Ha2. } 1:{ exact Hn. } 1:{ exact Hn8. } 1:{ exact SRC. } 1:{ exact Lbs. } 1:{ exact DST. } 1:{ exact Lold. }
    1:{ exact A08. } 1:{ exact D8. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    1:{ exact KD1. } 1:{ exact KD2. } 1:{ exact KS1. } 1:{ exact KS2. }
    1:{ exact SHD. } 1:{ exact SHS. }
    1:{ exact RD. } 1:{ exact RDL1. } 1:{ exact RDL2. }
    1:{ exact RDs. } 1:{ exact RDL3. } 1:{ exact RDL4. }
    1:{ lia. } 1:{ lia. } 1:{ lia. }
    1:{ Z.div_mod_to_equations. lia. }
    1:{ lia. } 1:{ lia. }
    1:{ exact PRG. } 1:{ exact PRT. }
    1:{ eapply RT_transport; [exact RTH | exact MU | solve_W_ok_rt]. }
    1:{ eapply rt_disj_sub; [exact RDJ1 | lia | lia]. }
    1:{ exact RDJ2. }
    rewrite ?ULs in *.
    replace (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))%Z with D in * by lia.
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc.
    { exfalso. cond_cleanup Hc. replace (bv_unsigned a2) with (D + n)%Z in Hc by lia.
      destruct (Z.eq_dec n 0) as [N0|N1].
      - rewrite N0, Z.add_0_r, Z.sub_diag, Z.mod_0_l, Z.lxor_0_l in Hc by lia. decide_ltb_in Hc. discriminate.
      - replace ((D - (D + n)) mod 18446744073709551616)%Z with (18446744073709551616 - n)%Z in Hc
          by (symmetry; symmetry; apply (Z.mod_unique_pos _ _ (-1)); lia).
        rewrite lxor_high' in Hc by lia. decide_ltb_in Hc. discriminate. }
    clear Hc.
    do 5 step. (* [comment removed for export] *)
    match goal with H : stk BSEGS _ _ _ |- _ => rename H into ST' end.
    try replace (bv_unsigned sp + -32 - COPY_BWD_IMPL_NEED)%Z with (bv_unsigned sp - 2288)%Z in ST' by lia.
    release_frame FR ST' (bv_unsigned sp).
    unfold copy_bwd_post. replace (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))%Z with D by lia.
    replace (bv_unsigned a1 - bv_unsigned a0)%Z with n by lia.
    finish.
    all: try eassumption. all: try lia.
    all: try (split; assumption).
  Qed.
End Main.
End B_copy_bwd.

Module B_copy_bwd_impl.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Ubsan_chk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_shl_limbs.B_asan_memmove2_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_copy_bwd_impl_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac solve_W_ok_rt := solve_W_rt.  (* [comment removed for export] *)

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Section Main.
  Hypothesis asan_memmove2_spec : asan_memmove2_stmt.

  #[using="asan_memmove2_spec"] Lemma copy_bwd_impl_spec : copy_bwd_impl_stmt.
  Proof. LiaFast.lf_pins (fun (asan_memmove2_spec : LiaFast.U) => LiaFast.u0).
    unfold copy_bwd_impl_stmt. intros until shn2.
    intros ST Ha1 Ha2 Hn Hn8 SRC Lbs DST Lold A08 D8 RA KD1 KD2 KS1 KS2 SHD SHS RD RDL1 RDL2 RDs RDL3 RDL4
           SP1 SP2 SP3 AL16 SEPD SEPS PRG PRT RTH RDJ1 RDJ2.
    pose proof (munch_refl (copy_bwd_impl_W (bv_unsigned sp) (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))
                                             (bv_unsigned a1 - bv_unsigned a0)) m) as MU.
    cbv delta [copy_bwd_impl_W] in MU.
    replace (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))%Z with D in MU by lia.
    replace (bv_unsigned a1 - bv_unsigned a0)%Z with n in MU by lia.
    pose proof (wmono_refl BSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0.
    pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1.
    pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2.
    pose proof (bytes_at_bound _ _ _ _ SRC) as Bs. destruct DST as [DB DW]. pose proof (bytes_at_bound _ _ _ _ DB) as Bd.
    assert (DST : u8arr BSEGS m D old) by (split; assumption). clear DB DW.
    rewrite Lold in Bd.
    carve_frame 32%nat ST.
    do 4 step. (* [comment removed for export] *)
    step. step. step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    replace (bv_unsigned a1 - bv_unsigned a0)%Z with n by lia.
    zstep. (* [comment removed for export] *)
    replace (bv_unsigned a2 - n)%Z with D by lia.
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    zstep. (* [comment removed for export] *)
    rewrite lm_signed_lit by lia. rewrite (Z.shiftr_div_pow2 n 3) by lia. change (2 ^ 3)%Z with 8%Z.
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    assert (Hq : (0 <= n / 8 < 2 ^ 37)%Z). { split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia. }
    rewrite (Z.shiftr_div_pow2 _ 61) by lia. rewrite (Z.div_small (n / 8 + 1152921504606846975) (2 ^ 61)) by lia.
    step. (* [comment removed for export] *)
    try kill_check.
    step. (* [comment removed for export] *)
    kill_check.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned a2 + ?x)%Z] =>
      replace (Z_to_bv 64 (bv_unsigned a2 + x)%Z) with (Z_to_bv 64 D)
        by (apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3)%Z with 8%Z; Z.div_mod_to_equations; lia) end.
    step. (* [comment removed for export] *)
    if_cases Hz.
    - (* [comment removed for export] *)
      cond_cleanup Hz.
      step. step. (* [comment removed for export] *)
      do 5 step.
      release_frame FR ST (bv_unsigned sp).
      unfold copy_bwd_impl_post. replace (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))%Z with D by lia.
      replace (bv_unsigned a1 - bv_unsigned a0)%Z with n by lia.
      finish.
      all: try eassumption. all: try lia.
      assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in Lbs; lia]).
      assert (old = []) as -> by (destruct old; [reflexivity| cbn in Lold; lia]). all: try exact DST. all: try assumption.
    - cond_cleanup Hz.
      zstep. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      rewrite (land7_lor_aligned D (bv_unsigned a0)) by lia.
      step. (* [comment removed for export] *)
      try kill_check.
      step. (* [comment removed for export] *)
      pose proof (unsigned_lit D ltac:(lia)) as ULD. pose proof (unsigned_lit n ltac:(lia)) as ULn.
      pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as ULs.
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply evt_cut; [ eapply asan_memmove2_spec with (v := v) (bs := bs) (old := old)
                                 (shlo := shlo) (shn := shn) (shlo2 := shlo2) (shn2 := shn2)
                        | post_call BSEGS mc ] end.
      all: rewrite ?ULD, ?ULn, ?ULs.
      1:{ exact SRC. } 1:{ exact DST. } 1:{ exact Lold. } 1:{ exact Lbs. }
      1:{ exact D8. } 1:{ exact A08. } 1:{ exact Hn8. }
      1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
      1:{ exact SHD. } 1:{ exact SHS. }
      1:{ exact RD. } 1:{ lia. } 1:{ lia. }
      1:{ exact RDs. } 1:{ lia. } 1:{ lia. }
      1:{ replace (bv_unsigned sp + -32 - IMEMMOVE_NEED)%Z with (bv_unsigned sp - 2256)%Z by lia. exact ST. }
      1:{ lia. } 1:{ lia. } 1:{ lia. }
      1:{ Z.div_mod_to_equations. lia. }
      1:{ lia. } 1:{ lia. }
      1:{ exact PRG. } 1:{ exact PRT. }
      1:{ eapply RT_transport; [exact RTH | exact MU | solve_W_ok_rt]. }
      1:{ eapply rt_disj_sub; [exact RDJ1 | lia | lia]. }
      1:{ exact RDJ2. }
      1:{ rewrite unsigned_lit by lia. reflexivity. }
      rewrite ?ULD, ?ULn, ?ULs in *.
      step. step. (* [comment removed for export] *)
      do 5 step.
      match goal with H : stk BSEGS _ _ _ |- _ => rename H into ST' end.
      try replace (bv_unsigned sp + -32 - IMEMMOVE_NEED)%Z with (bv_unsigned sp - 2256)%Z in ST' by lia.
      release_frame FR ST' (bv_unsigned sp).
      unfold copy_bwd_impl_post. replace (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))%Z with D by lia.
      replace (bv_unsigned a1 - bv_unsigned a0)%Z with n by lia.
      finish.
      all: try eassumption. all: try lia.
      all: split; assumption.
  Qed.
End Main.
End B_copy_bwd_impl.

Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac solve_W_ok_rt := solve_W_rt.  (* [comment removed for export] *)

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Lemma list_eq_repeat : forall (l : list word) (x : word) n,
  length l = n -> (forall j, (j < n)%nat -> nth j l w0 = x) -> l = repeat x n.
Proof.
  intros l x n Hl H. revert l Hl H. induction n as [|n IH]; intros l Hl H.
  - destruct l; [reflexivity| cbn in Hl; lia].
  - destruct l as [|y l]; [cbn in Hl; lia|]. cbn. f_equal.
    + exact (H 0%nat ltac:(lia)).
    + apply IH; [cbn in Hl; lia|]. intros j Hj. exact (H (S j) ltac:(lia)).
Qed.

Section Fill.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x15 x16 x17 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (A : Z) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (n : Z).
  Hypothesis Hn : (0 < n <= 62)%Z.
  Hypothesis HA : (app2r (A) (A + 504) /\ A + 504 <= KTOP)%Z.
  Hypothesis A8 : (A mod 8 = 0)%Z.

  (* [comment removed for export] *)
  Definition fill_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (a0 a1 a4 s2 s5 : word) (m' : word -> option byte),
      ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 a1 (Z_to_bv 64 (-8)) (Z_to_bv 64 1) a4 x15 x16 x17
                   s2 x19 x20 s5 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x98800) fc None m' (seg_rom BSEGS)
      /\ munch [(A, A + 8 * n)]%Z m m'
      /\ wmono BSEGS m m'
      /\ u64arr BSEGS m' A (repeat (Z_to_bv 64 0) (Z.to_nat n))
      /\ shz BSEGS m' (ASAN_B + A / 8) 63.

  Definition fill_ok (k : nat) : Prop :=
    forall (i : nat) (p x14 : word) (cur : list word) (m : word -> option byte),
      (Z.to_nat n - i = k)%nat -> (i < Z.to_nat n)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      u64arr BSEGS m A cur -> length cur = Z.to_nat n ->
      (forall j, (j < i)%nat -> nth j cur w0 = Z_to_bv 64 0) ->
      munch [(A, A + 8 * n)]%Z m0 m -> wmono BSEGS m0 m ->
      shz BSEGS m (ASAN_B + A / 8) 63 ->
      evt BSEGS (fill_post m0)
        (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 p (Z_to_bv 64 (n + 1 - Z.of_nat i)) (Z_to_bv 64 (-8)) (Z_to_bv 64 1) x14 x15 x16 x17
                 p x19 x20 (Z_to_bv 64 (ASAN_B + A / 8 + Z.of_nat i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x987dc) fc None m (seg_rom BSEGS)).

  #[using="Hn HA A8"] Lemma fill_body : forall k, fill_ok k -> fill_ok (S k).
  Proof. LiaFast.lf_pins (fun (Hn HA A8 : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold fill_ok. intros i p x14 cur m Hk Hi Hp CUR Hcur Hz MU WM SHZ.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (bv_unsigned_in_range 64 p) as Rp. unfold bv_modulus in Rp.
    pose proof (shz_bound _ _ _ _ SHZ) as Bsh.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    try if_false.
    pose proof (u64arr_store_ok BSEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write BSEGS m A cur (Z.of_nat i) (Z_to_bv 64 0) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    (* [comment removed for export] *)
    first [ change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)) | idtac ].
    store_done.
    step. (* [comment removed for export] *)
    try kill_check. try if_not_taken.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hmore.
    - cond_cleanup Hmore. rewrite ?lm_signed_lit, ?signed_lit in Hmore by lia.
      replace (n + 1 - Z.of_nat i + -1)%Z with (n + 1 - Z.of_nat (S i))%Z by lia.
      replace (ASAN_B + A / 8 + Z.of_nat i + 1)%Z with (ASAN_B + A / 8 + Z.of_nat (S i))%Z by lia.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8)) _ (upd cur i (Z_to_bv 64 0))); try eassumption; try lia.
      all: first [ rewrite unsigned_lit by lia; lia
                 | rewrite upd_length; exact Hcur
                 | intros j Hj; destruct (Nat.eq_dec j i) as [->|NE]; [apply nth_upd_same; rewrite Hcur; lia| rewrite nth_upd_other by lia; apply Hz; lia]
                 | idtac ].
    - cond_cleanup Hmore. rewrite ?lm_signed_lit, ?signed_lit in Hmore by lia.
      apply evt_done. unfold fill_post. do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [| assumption].
      replace (repeat (Z_to_bv 64 0) (Z.to_nat n)) with (upd cur i (Z_to_bv 64 0)); [exact CUR'|].
      apply list_eq_repeat. { rewrite upd_length. exact Hcur. }
      intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]. { apply nth_upd_same. rewrite Hcur. lia. }
      rewrite nth_upd_other by lia. apply Hz. lia.
  Qed.

  #[using="Hn HA A8"] Lemma fill_loop : forall k, fill_ok k.
  Proof. LiaFast.lf_pins (fun (Hn HA A8 : LiaFast.U) => LiaFast.u0). induction k as [|k IH]. - unfold fill_ok; intros; exfalso; lia. - apply fill_body; exact IH. Qed.

  #[using="Hn HA A8"] Lemma fill_run : forall (p x14 : word) (cur : list word),
    bv_unsigned p = A ->
    u64arr BSEGS m0 A cur -> length cur = Z.to_nat n -> shz BSEGS m0 (ASAN_B + A / 8) 63 ->
    evt BSEGS (fill_post m0)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 p (Z_to_bv 64 (n + 1)) (Z_to_bv 64 (-8)) (Z_to_bv 64 1) x14 x15 x16 x17
               p x19 x20 (Z_to_bv 64 (ASAN_B + A / 8)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x987dc) fc None m0 (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (Hn HA A8 : LiaFast.U) => LiaFast.u0).
    intros p x14 cur Hp CUR Hcur SHZ. replace (n + 1)%Z with (n + 1 - Z.of_nat 0)%Z by lia.
    replace (Z_to_bv 64 (ASAN_B + A / 8)) with (Z_to_bv 64 (ASAN_B + A / 8 + Z.of_nat 0)) by (f_equal; lia).
    eapply (fill_loop (Z.to_nat n) 0%nat p x14 cur); try eassumption; try lia.
    all: first [intros j Hj; exfalso; lia | apply munch_refl | apply wmono_refl].
  Qed.
End Fill.

Section Main.
  Hypothesis copy_bwd_spec : copy_bwd_stmt.

  #[using="copy_bwd_spec"] Lemma shl_limbs_spec : shl_limbs_stmt.
  Proof. LiaFast.lf_pins (fun (copy_bwd_spec : LiaFast.U) => LiaFast.u0).
    unfold shl_limbs_stmt. intros until v. intros ST AL16 LIMBS L62 LENC Hlen A8 Hn SEP PRG PRT RTH RDJ1 RDJ2 SP1 SP2 SP3 KA0 KA1 SHZ RBX.
    pose proof (munch_refl (shl_limbs_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU.
    cbv delta [shl_limbs_W] in MU.
    pose proof (wmono_refl BSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a1) as Rn. unfold bv_modulus in Rn.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    remember (bv_unsigned a1) as n eqn:En.
    open_RT_keep RTH.
    clear RT2 RT2b RT3 RT4 RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb RTP.
    carve_frame 64%nat ST.
    do 9 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    try if_false.
    step. (* [comment removed for export] *)
    rewrite ?zx16_lit_small by lia.
    zstep. (* [comment removed for export] *)
    rewrite <- ?En.
    (* [comment removed for export] *)
    assert (EXIT : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x28 x29 x30 x31 : word) (m' : word -> option byte)
                          (ws' : list word) (len' : Z),
      u64arr BSEGS m' (bv_unsigned a0) ws' -> length ws' = 62%nat ->
      rw_cells BSEGS m' (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len')] -> (0 <= len' <= 62)%Z ->
      ((n + len <= 62)%Z -> bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) * 2 ^ (64 * n))%Z
                            /\ (bnorm ws (Z.to_nat len) -> bnorm ws' (Z.to_nat len'))) ->
      rw_cells BSEGS m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk BSEGS m' (bv_unsigned sp - 2352) (bv_unsigned sp + -64) ->
      munch [(bv_unsigned sp - 2352, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 498)]%Z m m' -> wmono BSEGS m m' ->
      evt BSEGS (shl_limbs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) n ws len m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 (bv_unsigned a0 + 496)) a1
                 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 (n + len)) (Z_to_bv 64 ((bv_unsigned a0 + 496) / 8 + ASAN_B)) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x98814) fc None m' (seg_rom BSEGS))).
    { intros * XA' L' LENC' Hl' VALC FR' ST' MU' WM'.
      step. (* [comment removed for export] *)
      rewrite v_sltiu_b2z. rewrite ?unsigned_lit by lia.
      pose proof (zb_b2z_range (n + len <? 63)%Z) as Rb.
      do 10 step. (* [comment removed for export] *)
      release_frame FR' ST' (bv_unsigned sp).
      unfold shl_limbs_post. finish.
      all: try eassumption. all: try lia.
      - intros Hb. apply VALC. destruct (Z.ltb_spec0 (n + len) 63); cbn in Hb; lia.
      - intros Hc. replace (n + len <? 63)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. (* [comment removed for export] *)
    if_cases Hz.
    - cond_cleanup Hz.
      eapply EXIT; try eassumption; try lia.
      all: intros _; rewrite Hz; change (Z.to_nat 0) with 0%nat; rewrite !bval_0; split; [ring| intros B; exact B].
    - cond_cleanup Hz.
      destruct (Z_of_nat_complete len ltac:(lia)) as [ln El].
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov.
      + cond_cleanup Hov.
        eapply EXIT; try eassumption; try lia. all: intros Hc; exfalso; lia.
      + cond_cleanup Hov.
        destruct (Z_of_nat_complete n ltac:(lia)) as [dn Ed].
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        kill_check.
        zstep. (* [comment removed for export] *)
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
        zstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        kill_check.
        zstep. (* [comment removed for export] *)
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        kill_check.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        kill_check.
        zstep. (* [comment removed for export] *)
        zstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        (* [comment removed for export] *)
        rewrite <- ?En.
        name_mem mc1.
        pose proof (u64arr_prefix_bytes BSEGS mc1 _ ws ln ltac:(rewrite L62; lia) LIMBS) as SRC.
        destruct (u64arr_split3 BSEGS mc1 _ ws dn ln ltac:(rewrite L62; lia) LIMBS) as (U1 & U2 & U3).
        pose proof (u8arr_of_u64arr BSEGS _ _ _ U2) as DST.
        destruct (u64arr_len_split3 ws dn ln ltac:(rewrite L62; lia)) as (Ews & Ld & Ll & Lr). rewrite L62 in Lr.
        clear LIMBS U2.
        pose proof (unsigned_lit (bv_unsigned a0 + n * 8) ltac:(lia)) as UL1.
        pose proof (unsigned_lit (bv_unsigned a0 + len * 8) ltac:(lia)) as UL2.
        pose proof (unsigned_lit (bv_unsigned a0 + n * 8 + len * 8) ltac:(lia)) as UL3.
        pose proof (unsigned_lit (bv_unsigned sp + -64) ltac:(lia)) as ULs.
        step. (* [comment removed for export] *)
        eapply evt_cut; [ eapply copy_bwd_spec with (v := v) (n := (8 * len)%Z) (D := (bv_unsigned a0 + 8 * n)%Z)
                                                    (bs := u64s (firstn ln ws))
                                                    (shlo := (ASAN_B + bv_unsigned a0 / 8 - 8)%Z) (shn := 79%Z)
                                                    (shlo2 := (ASAN_B + bv_unsigned a0 / 8 - 8)%Z) (shn2 := 79%Z)
                        | post_call BSEGS mc1 ].
        all: rewrite ?ULs, ?UL1, ?UL2, ?UL3.
        1:{ replace (bv_unsigned sp + -64 - COPY_BWD_NEED)%Z with (bv_unsigned sp - 2352)%Z by lia. exact ST. }
        1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ rewrite Z.mul_comm. apply Z_mod_mult. }
        1:{ exact SRC. } 1:{ rewrite u64s_length, firstn_length, L62. lia. }
        1:{ eapply u8arr_at_eq; [exact DST| lia]. } 1:{ rewrite !u64s_length, Ll, firstn_length, L62. lia. }
        1:{ exact A8. } 1:{ rewrite Z.add_mod, A8, Z.mul_comm, Z_mod_mult by lia. reflexivity. }
        1:{ rewrite unsigned_lit by lia. reflexivity. }
        1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
        1:{ eapply shz_sub; [exact SHZ | Z.div_mod_to_equations; lia | lia | Z.div_mod_to_equations; lia]. }
        1:{ eapply shz_sub; [exact SHZ | lia | lia | Z.div_mod_to_equations; lia]. }
        1:{ exact RBX. } 1:{ Z.div_mod_to_equations; lia. } 1:{ Z.div_mod_to_equations; lia. }
        1:{ exact RBX. } 1:{ lia. } 1:{ Z.div_mod_to_equations; lia. }
        1:{ lia. } 1:{ lia. } 1:{ lia. }
        1:{ Z.div_mod_to_equations. lia. }
        1:{ lia. } 1:{ lia. }
        1:{ exact PRG. } 1:{ exact PRT. }
        1:{ eapply RT_transport; [exact RTH | exact MU | solve_W_ok_rt]. }
        1:{ eapply rt_disj_sub; [exact RDJ1 | lia | lia]. }
        1:{ eapply rt_disj_sub; [exact RDJ2 | lia | lia]. }
        rewrite ?UL1, ?UL2, ?UL3, ?ULs in *.
        name_mem mc2.
        match goal with H : u8arr BSEGS mc2 _ (u64s (firstn ln ws)) |- _ =>
          pose proof (u64arr_of_u8arr BSEGS mc2 _ ln (u64s (firstn ln ws)) H
                      ltac:(rewrite u64s_length, firstn_length, L62; lia)) as MID; clear H end.
        rewrite words_of_bytes_u64s in MID.
        replace (bv_unsigned a0 + n * 8 + len * 8 - (bv_unsigned a0 + len * 8 - bv_unsigned a0))%Z with (bv_unsigned a0 + 8 * Z.of_nat dn)%Z in MID by lia.
        step. (* [comment removed for export] *)
        kill_check.
        assert (Lm : length (firstn ln ws) = ln) by (rewrite firstn_length, L62; lia).
        step. (* [comment removed for export] *)
        if_cases Hn0.
        * cond_cleanup Hn0.
          (* [comment removed for export] *)
          assert (dn = 0%nat) as Dn0 by lia. rewrite Dn0 in U3, MID. cbn [Nat.add] in U3.
          assert (CUR2 : u64arr BSEGS mc2 (bv_unsigned a0) (firstn ln ws ++ skipn ln ws)).
          { apply u64arr_app. rewrite Lm. split.
            - eapply u64arr_at_eq; [exact MID| lia].
            - eapply u64arr_at_eq; [exact U3| lia]. }
          rewrite firstn_skipn in CUR2.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          try if_false.
          step. (* [comment removed for export] *)
          rewrite ?sx16_lit_small by lia.
          zstep. (* [comment removed for export] *)
          rewrite <- ?En.
          step. (* [comment removed for export] *)
          replace (len + n)%Z with len by lia.
          eapply EXIT; try eassumption; try lia.
          all: first [ assumption
                     | eapply stk_at_eq; [eassumption | lia | lia]
                     | eapply rw_cells_at_eq + idtac; [eassumption | lia]
                     | intros _; replace n with 0%Z by lia; rewrite ?Z.add_0_r, Z.mul_0_r, Z.pow_0_r, Z.mul_1_r; split; [reflexivity| intros B; exact B]
                     | idtac ].
        * cond_cleanup Hn0.
          step. (* [comment removed for export] *) shr3.
          zstep. (* [comment removed for export] *)
          rewrite <- ?En.
          step. (* [comment removed for export] *)
          zstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          name_mem mc3.
          replace (Z_to_bv 64 (bv_unsigned a0 / 8 + ASAN_B)) with (Z_to_bv 64 (ASAN_B + bv_unsigned a0 / 8)) by (f_equal; lia).
          match goal with Hs : shz BSEGS mc3 _ 63 |- _ => rename Hs into SHZ3 end.
          eapply evt_cut; [ eapply (fill_run) with (A := bv_unsigned a0) (n := n) | post_call BSEGS mc3 ].
          all: try lia.
          all: try exact U1. all: try (rewrite Ld; lia). all: try exact SHZ3.
          name_mem mc4.
          assert (Z1 : u64arr BSEGS mc4 (bv_unsigned a0) (repeat (Z_to_bv 64 0) (Z.to_nat n))) by assumption.
          assert (CUR2 : u64arr BSEGS mc4 (bv_unsigned a0) (repeat (Z_to_bv 64 0) dn ++ firstn ln ws ++ skipn (dn + ln) ws)).
          { eapply (u64arr_join3 BSEGS mc4 _ _ _ _ dn ln); [rewrite repeat_length; reflexivity | exact Lm | | exact MID | exact U3].
            replace dn with (Z.to_nat n) by lia. exact Z1. }
          set (ws2 := repeat (Z_to_bv 64 0) dn ++ firstn ln ws ++ skipn (dn + ln) ws) in CUR2.
          assert (L2 : length ws2 = 62%nat). { subst ws2. rewrite !app_length, repeat_length, Lm, Lr. lia. }
          clear Z1 MID U3.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          try if_false.
          step. (* [comment removed for export] *)
          rewrite ?sx16_lit_small by lia.
          zstep. (* [comment removed for export] *)
          rewrite <- ?En.
          step. (* [comment removed for export] *)
          eapply EXIT; try eassumption; try lia.
          all: try (eapply stk_at_eq; [eassumption | lia | lia]).
          intros _.
          assert (Hhi : forall j, (j < ln)%nat -> nth (dn + j) ws2 w0 = nth j ws w0).
          { intros j Hj. subst ws2. rewrite nth_repeat_app_hi. rewrite app_nth1 by (rewrite Lm; exact Hj).
            rewrite <- (firstn_skipn ln ws) at 2. rewrite app_nth1 by (rewrite Lm; exact Hj). reflexivity. }
          split.
          -- replace (Z.to_nat (len + n)) with (dn + ln)%nat by lia.
             rewrite (bval_shift_limbs ws ws2 ln dn).
             ++ replace ln with (Z.to_nat len) by lia. rewrite <- Ed. reflexivity.
             ++ intros j Hj. unfold limbZ. subst ws2. rewrite nth_repeat_app_lo by exact Hj. apply unsigned_lit. lia.
             ++ exact Hhi.
          -- intros BN. right. replace (Z.to_nat (len + n) - 1)%nat with (dn + (ln - 1))%nat by lia.
             unfold limbZ. rewrite Hhi by lia.
             pose proof (bnorm_top ws (Z.to_nat len) ltac:(lia) BN) as T. unfold limbZ in T.
             replace (Z.to_nat len - 1)%nat with (ln - 1)%nat in T by lia. exact T.
  Qed.
End Main.
