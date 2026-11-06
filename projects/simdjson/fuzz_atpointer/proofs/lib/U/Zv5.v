(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe Zpd SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Zsr Zsp Zss Zve Zvd Zvj Zvk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_w.

Definition EN_MAX : Z := 2684354559.

Section SPUACC.
  Variable E : spuenv.
  Hypothesis OK : spu_ok E.
  Hypothesis HSET : spu_memset_stmt.
  Hypothesis HPM : spu_pm_stmt.
  Hypothesis HPDC : spu_pdc_stmt.
  Hypothesis HNDC : spu_ndc_stmt.
  Notation A := (q_A E).
  Notation LAST := (q_LAST E).
  Notation OUT := (q_OUT E).

  Lemma spu_400 : forall (q IP IL FPT FL : Z) (wv c0 spl : word) xra xt0 xt2 xs0 xa0 xa1 xa3 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> (-9223372036854775808 <= q < 9223372036854775808)%Z -> sp_pfacts E IP IL FPT FL ->
    evt usegs (spu_post E) (SPS E 0x4456c xra xt0 (Z_to_bv 64 IL) xt2 xs0 (Z_to_bv 64 q) xa0 xa1 (Z_to_bv 64 FPT) xa3 wv c0 (Z_to_bv 64 IP) xa7
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 OUT) xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM Hq PF.
    kstep. kstep.
    eapply evt_eq; [| eapply (spu_488 E OK HSET HPM HPDC HNDC q IP IL FPT FL wv (Z_to_bv 64 0) c0 spl)]; [num_st_eq | exact INV | assumption | lia | exact PF |].
    intros C. exfalso. apply C. reflexivity.
  Qed.

  Lemma spu_474 : forall (d en IP IL FPT FL : Z) (wv c0 spl : word) xra xt0 xt2 xs0 xs1 xa0 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL ->
    (-2147483648 <= d <= 2147483648)%Z -> (- EN_MAX <= en <= EN_MAX)%Z -> (1 <= bv_unsigned wv <= 18446744073709551614)%Z ->
    evt usegs (spu_post E) (SPS E 0x445e0 xra xt0 (Z_to_bv 64 IL) xt2 xs0 xs1 xa0 (Z_to_bv 64 d) (Z_to_bv 64 FPT) (Z_to_bv 64 en) wv c0 (Z_to_bv 64 IP) xa7
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 OUT) xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM PF Hd Hen HW. unfold EN_MAX in Hen.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x452cc%Z => u_trap_b pc
      | 0x445f4%Z => first [ eapply evt_eq; [| eapply (spu_488 E OK HSET HPM HPDC HNDC (d + en)%Z IP IL FPT FL wv (Z_to_bv 64 1) c0 spl)];
                             [num_st_eq | exact INV | assumption | lia | exact PF | intros _; exact HW] | fail 100 "cut" pc ]
      end).
  Qed.

  Notation RS pc IP IL FPT FL en c0 xra xt0 xt2 xs0 xs1 xa0 xa1 xa4 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm :=
    (SPS E pc xra xt0 (Z_to_bv 64 IL) xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 FPT) (Z_to_bv 64 en) xa4 c0 (Z_to_bv 64 IP) xa7
         xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 OUT) xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) xt4 xt5 xt6 xF xfc mm).

  Lemma spu_L7 : forall (f : nat) (IP IL FPT FL en z k w : Z) (c0 spl : word) xra xt2 xs0 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> sp_nz E IP IL FPT FL z -> (- EN_MAX <= en <= EN_MAX)%Z ->
    (FPT <> 0)%Z -> (0 <= k < FL)%Z -> (0 <= w <= 999999999999999999)%Z -> (1 <= w \/ FPT + k <= z)%Z -> (FL - k <= Z.of_nat f)%Z ->
    evt usegs (spu_post E) (RS 0x445a4 IP IL FPT FL en c0 xra (Z_to_bv 64 (-1)) xt2 xs0 xs1 xa0 (Z_to_bv 64 999999999999999999) (Z_to_bv 64 w) (Z_to_bv 64 (FPT + k))
                               xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 (Z_to_bv 64 10) (Z_to_bv 64 (FL - 1 - k)) (Z_to_bv 64 (FPT + k)) xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM PF NZ Hen HF Hk Hw Hz Hf; [exfalso; lia|].
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    pose proof PF as ((P1 & P2 & P3) & G1 & [[PA PB] | [(PA & PB & PC & PD) G2]]); [exfalso; lia|].
    pose proof (G2 (FPT + k)%Z ltac:(lia)) as Gk. pose proof (sp_tb_range E (FPT + k)) as Rk.
    destruct NZ as [NZ1 NZ2]. pose proof NZ1 as NZ1'.
    unfold sp_tb in Gk, Rk.
    assert (NZk : (z = FPT + k -> 49 <= bv_unsigned (nth (Z.to_nat (FPT + k - A)) (q_txt E) (Z_to_bv 8 0)))%Z) by (intros ->; exact NZ1').
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x452cc%Z => u_trap_b pc
      | 0x445e0%Z => first [ eapply evt_eq; [| eapply (spu_474 (FPT - (FPT + k + 1))%Z en IP IL FPT FL
                                                          (Z_to_bv 64 (w * 10 + bv_unsigned (nth (Z.to_nat (FPT + k - A)) (q_txt E) (Z_to_bv 8 0)) - 48)) c0 spl)];
                             [num_st_eq | exact INV | assumption | exact PF | lia | exact Hen |];
                             rewrite unsigned_lit by lia; destruct (Z.eq_dec z (FPT + k)); lia
                           | fail 100 "cut" pc ]
      | 0x445a4%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT FL en z (k + 1)%Z
                                                          (w * 10 + bv_unsigned (nth (Z.to_nat (FPT + k - A)) (q_txt E) (Z_to_bv 8 0)) - 48)%Z c0 spl)];
                             [num_st_eq | exact INV | assumption | exact PF | split; assumption | exact Hen | lia | lia | lia
                             | destruct (Z.eq_dec z (FPT + k)); lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_408 : forall (IP IL FPT FL en z w : Z) (c0 spl : word) xra xt0 xt2 xs0 xs1 xa0 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> sp_nz E IP IL FPT FL z -> (- EN_MAX <= en <= EN_MAX)%Z ->
    (0 <= w <= 999999999999999999)%Z -> (1 <= w \/ IP + IL <= z)%Z ->
    evt usegs (spu_post E) (RS 0x44574 IP IL FPT FL en c0 xra xt0 xt2 xs0 xs1 xa0 (Z_to_bv 64 999999999999999999) (Z_to_bv 64 w) xa7
                               xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM PF NZ Hen Hw Hz.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    pose proof PF as ((P1 & P2 & P3) & G1 & PFR). destruct NZ as [NZ1 NZ2]. pose proof NZ1 as NZ1'.
    destruct PFR as [[-> ->] | [(PA & PB & PC & PD) G2]].
    - kwalk ltac:(fun pc => lazymatch pc with
        | 0x452cc%Z => u_trap_b pc
        | 0x445e0%Z => first [ eapply evt_eq; [| eapply (spu_474 0%Z en IP IL 0%Z 0%Z (Z_to_bv 64 w) c0 spl)];
                               [num_st_eq | exact INV | assumption | exact PF | lia | exact Hen | rewrite unsigned_lit by lia; lia]
                             | fail 100 "cut" pc ]
        end).
    - kwalk ltac:(fun pc => lazymatch pc with
        | 0x452cc%Z => u_trap_b pc
        | 0x445e0%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0x445a4%Z => first [ eapply evt_eq; [| eapply (spu_L7 (Z.to_nat FL) IP IL FPT FL en z 0%Z w c0 spl)];
                               [num_st_eq | exact INV | assumption | exact PF | split; assumption | exact Hen | lia | lia | lia | lia | lia]
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma spu_L6 : forall (f : nat) (IP IL FPT FL en z k w : Z) (c0 spl : word) xra xt2 xs0 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> sp_nz E IP IL FPT FL z -> (- EN_MAX <= en <= EN_MAX)%Z ->
    (0 <= k < IL)%Z -> (0 <= w <= 999999999999999999)%Z -> (1 <= w \/ IP + k <= z)%Z -> (IL - k <= Z.of_nat f)%Z ->
    evt usegs (spu_post E) (RS 0x44524 IP IL FPT FL en c0 xra (Z_to_bv 64 (IP + IL)) xt2 xs0 xs1 xa0 (Z_to_bv 64 999999999999999999) (Z_to_bv 64 w) (Z_to_bv 64 (IP + k))
                               xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 (Z_to_bv 64 2) (Z_to_bv 64 10) (Z_to_bv 64 (IP + k + 1)) xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM PF NZ Hen Hk Hw Hz Hf; [exfalso; lia|].
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    pose proof PF as ((P1 & P2 & P3) & G1 & PFR).
    pose proof (G1 (IP + k)%Z ltac:(lia)) as Gk. pose proof (sp_tb_range E (IP + k)) as Rk.
    destruct NZ as [NZ1 NZ2]. pose proof NZ1 as NZ1'.
    unfold sp_tb in Gk, Rk.
    assert (NZk : (z = IP + k -> 49 <= bv_unsigned (nth (Z.to_nat (IP + k - A)) (q_txt E) (Z_to_bv 8 0)))%Z) by (intros ->; exact NZ1').
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x452cc%Z => u_trap_b pc
      | 0x445e0%Z => first [ eapply evt_eq; [| eapply (spu_474 (IP + IL - (IP + k + 1))%Z en IP IL FPT FL
                                                          (Z_to_bv 64 (w * 10 + bv_unsigned (nth (Z.to_nat (IP + k - A)) (q_txt E) (Z_to_bv 8 0)) - 48)) c0 spl)];
                             [num_st_eq | exact INV | assumption | exact PF | lia | exact Hen |];
                             rewrite unsigned_lit by lia; destruct (Z.eq_dec z (IP + k)); lia
                           | fail 100 "cut" pc ]
      | 0x44574%Z => first [ eapply evt_eq; [| eapply (spu_408 IP IL FPT FL en z
                                                          (w * 10 + bv_unsigned (nth (Z.to_nat (IP + k - A)) (q_txt E) (Z_to_bv 8 0)) - 48)%Z c0 spl)];
                             [num_st_eq | exact INV | assumption | exact PF | split; assumption | exact Hen | lia
                             | destruct (Z.eq_dec z (IP + k)); lia]
                           | fail 100 "cut" pc ]
      | 0x44524%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT FL en z (k + 1)%Z
                                                          (w * 10 + bv_unsigned (nth (Z.to_nat (IP + k - A)) (q_txt E) (Z_to_bv 8 0)) - 48)%Z c0 spl)];
                             [num_st_eq | exact INV | assumption | exact PF | split; assumption | exact Hen | lia | lia
                             | destruct (Z.eq_dec z (IP + k)); lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_394 : forall (IP IL FPT FL en z : Z) (c0 spl : word) xra xt2 xs0 xs1 xa0 xa1 xa4 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> sp_nz E IP IL FPT FL z -> (- EN_MAX <= en <= EN_MAX)%Z ->
    evt usegs (spu_post E) (RS 0x44500 IP IL FPT FL en c0 xra (Z_to_bv 64 (IP + IL)) xt2 xs0 xs1 xa0 xa1 xa4 xa7
                               xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM PF NZ Hen.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    pose proof PF as ((P1 & P2 & P3) & G1 & PFR).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x452cc%Z => u_trap_b pc
      | 0x44524%Z => first [ eapply evt_eq; [| eapply (spu_L6 (Z.to_nat IL) IP IL FPT FL en z 0%Z 0%Z c0 spl)];
                             [num_st_eq | exact INV | assumption | exact PF | exact NZ | exact Hen | lia | lia | destruct NZ as [_ [?|[? ?]]]; destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.
End SPUACC.
