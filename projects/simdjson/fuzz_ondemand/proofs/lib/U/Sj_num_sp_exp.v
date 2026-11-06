(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumber SjNumSwar SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_kitw Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_pdefs Sj_num_sp_pns Sj_num_sp_acc Sj_num_sp_acc2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Lemma shr64_small : forall x, (0 <= x < 18446744073709551616)%Z -> Z.shiftr x 64 = 0%Z.
Proof. intros x H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 64)%Z with 18446744073709551616%Z. apply Z.div_small. exact H. Qed.
Lemma shr63_small : forall x, (0 <= x < 9223372036854775808)%Z -> Z.shiftr x 63 = 0%Z.
Proof. intros x H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 63)%Z with 9223372036854775808%Z. apply Z.div_small. exact H. Qed.
Ltac xnorm :=
  repeat match goal with
  | |- context [bv_signed (Z_to_bv 64 ?z)] => rewrite (num_signed_of_Z z) by lia
  | |- context [Z.shiftr ?x 64] => rewrite (shr64_small x) by lia
  | |- context [Z.shiftr ?x 63] => rewrite (shr63_small x) by lia
  end.
Ltac nnorm_x := nnorm_w; xnorm.
Local Ltac nnorm ::= nnorm_x.

Section SPUEXP.
  Variable E : spuenv.
  Hypothesis OK : spu_ok E.
  Hypothesis HSET : spu_memset_stmt.
  Hypothesis HPM : spu_pm_stmt.
  Hypothesis HPDC : spu_pdc_stmt.
  Hypothesis HNDC : spu_ndc_stmt.
  Notation A := (q_A E).
  Notation LAST := (q_LAST E).
  Notation OUT := (q_OUT E).

  Notation XS pc IP IL FPT FL ex wv c0 xra xt2 xs0 xa0 xa3 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm :=
    (SPS E pc xra (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 IL) xt2 xs0 (Z_to_bv 64 ex) xa0 (Z_to_bv 64 LAST) (Z_to_bv 64 FPT) xa3 wv c0 (Z_to_bv 64 IP) (Z_to_bv 64 46)
         xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 OUT) xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) (Z_to_bv 64 (IL + FL)) xt5 xt6 xF xfc mm).

  Ltac exp_cuts INV PF :=
    fun pc => lazymatch pc with
      | 0x46208%Z => u_trap_b pc
      | 0x454a8%Z => first [ eapply evt_eq; [| eapply (spu_400 E OK HSET HPM HPDC HNDC)]; [num_st_eq | exact INV | assumption | unfold EN_MAX in *; lia | exact PF] | fail 100 "cut" pc ]
      | 0x453fc%Z => first [ eapply evt_eq; [| eapply (spu_354 E OK HSET HPM HPDC HNDC)]; [num_st_eq | exact INV | assumption | exact PF | unfold EN_MAX in *; lia | unfold EN_MAX in *; lia] | fail 100 "cut" pc ]
      end.

  Lemma spu_338 : forall (IP IL FPT FL ex en : Z) (wv c0 spl : word) xra xt2 xs0 xa0 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (-2147483648 <= ex <= 0)%Z -> (- EN_MAX <= en <= EN_MAX)%Z ->
    evt usegs (spu_post E) (XS 0x453e0 IP IL FPT FL ex wv c0 xra xt2 xs0 xa0 (Z_to_bv 64 en) xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM PF Hex Hen. pose proof Hen as Hen'. unfold EN_MAX in Hen'.
    kwalk ltac:(exp_cuts INV PF).
  Qed.

  Lemma spu_330 : forall (IP IL FPT FL ex en : Z) (wv c0 spl : word) xra xt2 xs0 xa0 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (-2147483648 <= ex <= 0)%Z -> (0 <= en <= EN_MAX)%Z ->
    evt usegs (spu_post E) (XS 0x453d8 IP IL FPT FL ex wv c0 xra xt2 xs0 xa0 (Z_to_bv 64 en) xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM PF Hex Hen.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x453e0%Z => first [ eapply evt_eq; [| eapply (spu_338 IP IL FPT FL ex _ wv c0 spl)]; [num_st_eq | exact INV | assumption | exact PF | lia | unfold EN_MAX in *; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_L4 : forall (f : nat) (IP IL FPT FL ex en e : Z) (wv c0 spl : word) xra xt2 xs5 xs6 xs8 xs9 xs10 xs11 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (-2147483648 <= ex <= 0)%Z -> (0 <= en <= EN_MAX)%Z ->
    (A <= e < LAST)%Z -> (LAST - e <= Z.of_nat f)%Z ->
    evt usegs (spu_post E) (XS 0x4537c IP IL FPT FL ex wv c0 xra xt2 (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 en) (Z_to_bv 64 268435455) (Z_to_bv 64 2) (Z_to_bv 64 e)
                               xs5 xs6 xs8 xs9 xs10 xs11 (Z_to_bv 64 e) xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM PF Hex Hen He Hf; [exfalso; lia|].
    pose proof INV as INV0. spu_open0 INV0. spu_env OK. unfold EN_MAX in Hen.
    pose proof (sp_tb_range E e) as Re. unfold sp_tb in Re.
    assert (DR : forall x, (0 <= Z.land x 255 < 256)%Z) by (intros x; rewrite land_255; apply Z.mod_pos_bound; lia).
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x46208%Z => u_trap_b pc
      | 0x453d8%Z => first [ eapply evt_eq; [| eapply (spu_330 IP IL FPT FL ex _ wv c0 spl)]; [num_st_eq | exact INV | assumption | exact PF | lia |];
                             unfold EN_MAX;
                             repeat match goal with |- context [Z.land ?x 255] => pose proof (DR x); rewrite (land_255 x) in * end; lia
                           | fail 100 "cut" pc ]
      | 0x4537c%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT FL ex _ (e + 1)%Z wv c0 spl)]; [num_st_eq | exact INV | assumption | exact PF | lia | | lia | lia];
                             unfold EN_MAX;
                             repeat match goal with |- context [Z.land ?x 255] => pose proof (DR x); rewrite (land_255 x) in * end; lia
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_31c : forall (IP IL FPT FL ex : Z) (wv c0 spl : word) xra xt2 xs0 xa0 xa3 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (-2147483648 <= ex <= 0)%Z ->
    evt usegs (spu_post E) (XS 0x453c4 IP IL FPT FL ex wv c0 xra xt2 xs0 xa0 xa3 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM PF Hex.
    kwalk ltac:(exp_cuts INV PF).
  Qed.

  Ltac exp_31c INV PF := first [ eapply evt_eq; [| eapply (spu_31c _ _ _ _ _)]; [num_st_eq | exact INV | assumption | exact PF | lia] | fail 100 "cut 31c" ].

  Lemma spu_2ac : forall (IP IL FPT FL ex e : Z) (wv c0 spl : word) xra xt2 xs0 xa0 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (-2147483648 <= ex <= 0)%Z -> (A <= e < LAST)%Z ->
    evt usegs (spu_post E) (XS 0x45354 IP IL FPT FL ex wv c0 xra xt2 xs0 xa0 (Z_to_bv 64 53) xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 (Z_to_bv 64 e) xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM PF Hex He.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x46208%Z => u_trap_b pc
      | 0x453c4%Z => exp_31c INV PF
      | 0x4537c%Z => first [ eapply evt_eq; [| eapply (spu_L4 (Z.to_nat LAST) IP IL FPT FL ex 0%Z e wv c0 spl)];
                             [num_st_eq | exact INV | assumption | exact PF | lia | unfold EN_MAX; lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_238 : forall (IP IL FPT FL ex e : Z) (wv c0 spl : word) xra xt2 xs0 xa0 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (-2147483648 <= ex <= 0)%Z -> (A <= e <= LAST)%Z ->
    evt usegs (spu_post E) (XS 0x452e0 IP IL FPT FL ex wv c0 xra xt2 xs0 xa0 (Z_to_bv 64 53) xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 (Z_to_bv 64 e) xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM PF Hex He.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x46208%Z => u_trap_b pc
      | 0x453c4%Z => exp_31c INV PF
      | 0x45354%Z => first [ eapply evt_eq; [| eapply (spu_2ac IP IL FPT FL ex _ wv c0 spl)]; [num_st_eq | exact INV | assumption | exact PF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_200 : forall (IP IL FPT FL ex p : Z) (wv c0 spl : word) xra xt2 xs0 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (-2147483648 <= ex <= 0)%Z -> (A <= p < LAST)%Z ->
    evt usegs (spu_post E) (XS 0x452a8 IP IL FPT FL ex wv c0 xra xt2 xs0 (Z_to_bv 64 p) (Z_to_bv 64 53) xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM PF Hex Hp.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x46208%Z => u_trap_b pc
      | 0x452e0%Z => first [ eapply evt_eq; [| eapply (spu_238 IP IL FPT FL ex _ wv c0 spl)]; [num_st_eq | exact INV | assumption | exact PF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_1b0 : forall (IP IL FPT FL ex p : Z) (wv c0 spl : word) xra xt2 xs0 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (-2147483648 <= ex <= 0)%Z -> (A <= p <= LAST)%Z ->
    evt usegs (spu_post E) (XS 0x45258 IP IL FPT FL ex wv c0 xra xt2 xs0 (Z_to_bv 64 p) (Z_to_bv 64 53) xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM PF Hex Hp.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x46208%Z => u_trap_b pc
      | 0x453c4%Z => exp_31c INV PF
      | 0x452a8%Z => first [ eapply evt_eq; [| eapply (spu_200 IP IL FPT FL ex p wv c0 spl)]; [num_st_eq | exact INV | assumption | exact PF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End SPUEXP.
