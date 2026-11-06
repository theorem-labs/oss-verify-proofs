(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_kit AF_depot1.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanConsts AsanState AsanOps AsanDepot.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac cstep := stepA; try first [if_true | if_false].

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma shl_shr_field : forall x a c, 0 <= x -> 0 <= c <= a -> a <= 64 ->
  Z.shiftr ((Z.shiftl x a) mod 18446744073709551616) (a - c) = (x mod 2^(64 - a)) * 2^c.
Proof. aceil.
  intros x a c Hx Hc Ha. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace 18446744073709551616 with (2^(64 - a) * 2^a). 2:{ rewrite <- Z.pow_add_r by lia. replace (64 - a + a) with 64 by lia. reflexivity. }
  assert (P1 : 0 < 2^(64-a)) by (apply Z.pow_pos_nonneg; lia). assert (P2 : 0 < 2^(a-c)) by (apply Z.pow_pos_nonneg; lia). assert (P3 : 0 < 2^c) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.mul_mod_distr_r by lia.
  replace (2^a) with (2^c * 2^(a - c)). 2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite Z.mul_assoc, Z.div_mul by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_c8_split : forall segs m A v w rest, 0 <= v < 2^32 -> 0 <= w < 2^32 ->
  rw_cells segs m A (C8 (Z_to_bv 64 (v + 2^32 * w)) :: rest) -> rw_cells segs m A (C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 w) :: rest).
Proof. aceil.
  intros segs m A v w rest Hv Hw H. pose proof H as [[WF _] _]. destruct WF as [_ WFr].
  eapply rw_cells_recast; [exact H| cbn; split; [exact I| split; [exact I| exact WFr]] | | reflexivity].
  cbn [cells_bytes]. rewrite app_assoc. f_equal. pose proof (c8_c4c4 v w Hv Hw) as E. cbn [cells_bytes] in E. rewrite !app_nil_r in E. symmetry. exact E.
Qed.
Lemma rw_cells_c8_join : forall segs m A v w rest, 0 <= v < 2^32 -> 0 <= w < 2^32 ->
  rw_cells segs m A (C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 w) :: rest) -> rw_cells segs m A (C8 (Z_to_bv 64 (v + 2^32 * w)) :: rest).
Proof. aceil.
  intros segs m A v w rest Hv Hw H. pose proof H as [[WF _] _]. destruct WF as (_ & _ & WFr).
  eapply rw_cells_recast; [exact H| cbn; split; [exact I| exact WFr] | | reflexivity].
  cbn [cells_bytes]. rewrite app_assoc. f_equal. pose proof (c8_c4c4 v w Hv Hw) as E. cbn [cells_bytes] in E. rewrite !app_nil_r in E. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section STORE.
Variable P : acc -> Prop.

Definition store_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo NA ARGS SS b sb fr len h : Z) (j1 : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (bs' : list byte) (sid : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (NA, NA + 16); (SS, SS + 8); (SS + 24 + 16 * b, SS + 28 + 16 * b);
              (sb + 8 * (fr mod 2^20), sb + 8 * (fr mod 2^20) + 8 * (len + 1))] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' NA [C8 (Z_to_bv 64 h); C4 j1; C4 sid]                                (* [comment removed for export] *)
    /\ rw_cells asegs m' SS [C8 (Z_to_bv 64 (fr + (len + 1)))]                              (* [comment removed for export] *)
    /\ rw_cells asegs m' (SS + 16 + 16 * b) [C8 (Z_to_bv 64 sb); C4 (Z_to_bv 64 (fr - b * 2^20 + (len + 1)))]   (* [comment removed for export] *)
    /\ u8arr asegs m' sb bs' /\ Z.of_nat (length bs') = kStoreBlockBytes.

(* [comment removed for export] *)
End STORE.
End RC__1.
