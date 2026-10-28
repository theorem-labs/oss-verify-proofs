(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber SjNumSwar SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_kitw Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_pdefs Sj_num_sp_pns Sj_num_sp_exp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_w.

Lemma digit_zextb : forall b, (0 <= b < 256)%Z -> (((b + -48) mod 18446744073709551616) mod 256 <= 9)%Z -> (48 <= b <= 57)%Z.
Proof. intros b Hb H. Z.div_mod_to_equations. lia. Qed.

Section SPUFRAC.
  Variable E : spuenv.
  Hypothesis OK : spu_ok E.
  Hypothesis HSET : spu_memset_stmt.
  Hypothesis HPM : spu_pm_stmt.
  Hypothesis HPDC : spu_pdc_stmt.
  Hypothesis HNDC : spu_ndc_stmt.
  Notation A := (q_A E).
  Notation LAST := (q_LAST E).
  Notation OUT := (q_OUT E).

  Notation FS pc IP IL p c0 xra xt2 xs0 xs1 xa4 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
    (SPS E pc xra (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 IL) xt2 xs0 xs1 (Z_to_bv 64 p) (Z_to_bv 64 LAST) (Z_to_bv 64 (IP + IL + 1)) (Z_to_bv 64 53) xa4 c0 (Z_to_bv 64 IP) (Z_to_bv 64 46)
         xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Lemma spu_18c : forall (IP IL p : Z) (c0 spl : word) xra xt2 xs0 xs1 xa4 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_ffacts E IP IL p ->
    evt usegs (spu_post E) (FS 0x5bed8 IP IL p c0 xra xt2 xs0 xs1 xa4 xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 OUT) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM FF.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x5ceac%Z => u_trap_b pc
      | 0x5c328%Z => first [ eapply evt_eq; [| eapply (spu_5dc E OK HSET HPM HPDC HNDC spl)]; [num_st_eq | exact INV | assumption] | fail 100 "cut" pc ]
      | 0x5befc%Z => first [ eapply evt_eq; [| eapply (spu_1b0 E OK HSET HPM HPDC HNDC IP IL (IP + IL + 1)%Z (p - (IP + IL + 1))%Z (IP + IL + 1 - p)%Z p _ c0 spl)];
                             [num_st_eq | exact INV | assumption | apply sp_ffacts_pfacts; [exact FF | lia] | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_L3 : forall (f : nat) (IP IL p : Z) (c0 spl : word) xra xt2 xs0 xs1 xa4 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_ffacts E IP IL p -> (p < LAST)%Z -> (LAST - p <= Z.of_nat f)%Z ->
    evt usegs (spu_post E) (FS 0x5beb0 IP IL p c0 xra xt2 xs0 xs1 xa4 xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 OUT) xs8 xs9 xs10 xs11 (Z_to_bv 64 9) (Z_to_bv 64 (-1)) (Z_to_bv 64 10) xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM FF Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    pose proof (sp_tb_range E p) as Rp. unfold sp_tb in Rp.
    pose proof (digit_zextb _ Rp) as DG.
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x5ceac%Z => u_trap_b pc
      | 0x5bed8%Z => first [ eapply evt_eq; [| eapply (spu_18c IP IL _ c0 spl)]; [num_st_eq | exact INV | assumption |];
                             first [ exact FF
                                   | replace (q_LAST E) with (p + 1)%Z by lia;
                                     apply sp_ffacts_app; [exact FF | lia | lia | apply sp_ge48_1; unfold sp_tb; lia] ]
                           | fail 100 "cut" pc ]
      | 0x5beb0%Z => first [ eapply evt_eq; [| eapply (IH IP IL (p + 1)%Z c0 spl)];
                             [num_st_eq | exact INV | assumption | apply sp_ffacts_app; [exact FF | lia | lia | apply sp_ge48_1; unfold sp_tb; lia] | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_150 : forall (IP IL p : Z) (c0 : word) xra xt2 xs0 xs1 xa4 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm (Z_to_bv 64 OUT) -> frm0 xfc -> sp_ffacts E IP IL p ->
    evt usegs (spu_post E) (FS 0x5be9c IP IL p c0 xra xt2 xs0 xs1 xa4 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM FF.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x5ceac%Z => u_trap_b pc
      | 0x5bed8%Z => first [ eapply evt_eq; [| eapply (spu_18c IP IL p c0 (Z_to_bv 64 OUT))]; [num_st_eq | exact INV | assumption | exact FF] | fail 100 "cut" pc ]
      | 0x5beb0%Z => first [ eapply evt_eq; [| eapply (spu_L3 (Z.to_nat LAST) IP IL p c0 (Z_to_bv 64 OUT))]; [num_st_eq | exact INV | assumption | exact FF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_0d4 : forall (IP IL p hi : Z) (c0 xs8 : word) xra xt2 xs0 xs1 xa4 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm (Z_to_bv 64 OUT) -> frm0 xfc -> sp_ffacts E IP IL p -> (p + 4 <= LAST)%Z ->
    bv_unsigned xs8 = (sp_tb E p + 256 * (sp_tb E (p + 1) + 256 * (sp_tb E (p + 2) + 256 * (sp_tb E (p + 3) + 256 * hi))))%Z ->
    evt usegs (spu_post E) (FS 0x5be20 IP IL p c0 xra xt2 xs0 xs1 xa4 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 p) xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM FF Hp HW.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    pose proof (bv_unsigned_in_range 64 xs8) as R8. unfold bv_modulus in R8. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R8.
    hide HW.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x5ceac%Z => u_trap_b pc
      | 0x5be9c%Z => first [ eapply evt_eq; [| eapply (spu_150 IP IL _ c0)]; [num_st_eq | exact INV | assumption |];
                             first [ exact FF
                                   | apply sp_ffacts_app; [exact FF | lia | lia |];
                                     reveal;
                                     lazymatch goal with KB : Z.land _ _ = 0%Z |- _ =>
                                       rewrite <- (Z.mod_small (bv_unsigned xs8) 18446744073709551616) in KB by lia;
                                       exact (sp_swar4 E p (bv_unsigned xs8) hi _ HW KB) end ]
                           | fail 100 "cut" pc ]
      end).
  Qed.
End SPUFRAC.
