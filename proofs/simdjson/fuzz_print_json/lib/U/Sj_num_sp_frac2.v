(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumSwar SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_kitw Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_pdefs Sj_num_sp_pns Sj_num_sp_exp Sj_num_sp_frac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_w.

Lemma le4z_word : forall b0 b1 b2 b3, (0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  bv_unsigned (Z_to_bv 64 (le4z b0 b1 b2 b3)) = b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * 0))))%Z.
Proof. intros b0 b1 b2 b3 H0 H1 H2 H3. rewrite le4z_eq by assumption. rewrite unsigned_lit by lia. lia. Qed.
Lemma le8z_word : forall b0 b1 b2 b3 b4 b5 b6 b7,
  (0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 ->
  bv_unsigned (Z_to_bv 64 (le8z b0 b1 b2 b3 b4 b5 b6 b7)) = b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7)))))))%Z.
Proof. intros b0 b1 b2 b3 b4 b5 b6 b7 H0 H1 H2 H3 H4 H5 H6 H7. rewrite le8z_eq by assumption. rewrite unsigned_lit by lia. reflexivity. Qed.

Section SPUFRAC2.
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

  Lemma spu_0a4 : forall (IP IL p : Z) (c0 : word) xra xt2 xs0 xs1 xa4 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPUINV0 E mm (Z_to_bv 64 OUT) -> frm0 xfc -> sp_ffacts E IP IL p ->
    evt usegs (spu_post E) (FS 0x5c100 IP IL p c0 xra xt2 xs0 xs1 xa4 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 p) (Z_to_bv 64 (LAST - p)) xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM FF.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x5d1bc%Z => u_trap_b pc
      | 0x5c1ac%Z => first [ eapply evt_eq; [| eapply (spu_150 E OK HSET HPM HPDC HNDC IP IL p c0)]; [num_st_eq | exact INV | assumption | exact FF] | fail 100 "cut" pc ]
      | 0x5c130%Z => first [ eapply evt_eq; [| eapply (spu_0d4 E OK HSET HPM HPDC HNDC IP IL p 0%Z c0 _)]; [num_st_eq | exact INV | assumption | exact FF | lia |];
                             apply (le4z_word (sp_tb E p) (sp_tb E (p + 1)) (sp_tb E (p + 2)) (sp_tb E (p + 3))); apply sp_tb_range
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_L2 : forall (f : nat) (IP IL p : Z) (c0 : word) xra xt2 xs0 xs1 xa4 xs2 xs3 xs6 xs8 xs9 xs10 xs11 xF xfc mm,
    SPUINV0 E mm (Z_to_bv 64 OUT) -> frm0 xfc -> sp_ffacts E IP IL p -> (p + 8 <= LAST)%Z -> (LAST - p <= 8 * Z.of_nat f)%Z ->
    evt usegs (spu_post E) (FS 0x5bd88 IP IL p c0 xra xt2 xs0 xs1 xa4 xs2 xs3 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 5063812098665367110) xs6 (Z_to_bv 64 7)
                               xs8 xs9 xs10 xs11 (Z_to_bv 64 p) (Z_to_bv 64 (LAST - p)) (Z_to_bv 64 8) (Z_to_bv 64 9259542123273814144) xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM FF Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x5d1bc%Z => u_trap_b pc
      | 0x5c130%Z => first [ eapply evt_eq; [| eapply (spu_0d4 E OK HSET HPM HPDC HNDC IP IL p
                                                          (sp_tb E (p + 4) + 256 * (sp_tb E (p + 5) + 256 * (sp_tb E (p + 6) + 256 * sp_tb E (p + 7))))%Z c0 _)];
                             [num_st_eq | exact INV | assumption | exact FF | lia |];
                             apply (le8z_word (sp_tb E p) (sp_tb E (p + 1)) (sp_tb E (p + 2)) (sp_tb E (p + 3)) (sp_tb E (p + 4)) (sp_tb E (p + 5)) (sp_tb E (p + 6)) (sp_tb E (p + 7)));
                             apply sp_tb_range
                           | fail 100 "cut" pc ]
      | 0x5c100%Z => first [ eapply evt_eq; [| eapply (spu_0a4 IP IL (p + 8)%Z c0)]; [num_st_eq | exact INV | assumption |];
                             apply sp_ffacts_app; [exact FF | lia | lia |];
                             lazymatch goal with KB : Z.land _ 9259542123273814144 = 0%Z |- _ => exact (sp_swar8 E p _ KB) end
                           | fail 100 "cut" pc ]
      | 0x5bd88%Z => first [ eapply evt_eq; [| eapply (IH IP IL (p + 8)%Z c0)]; [num_st_eq | exact INV | assumption | | lia | lia];
                             apply sp_ffacts_app; [exact FF | lia | lia |];
                             lazymatch goal with KB : Z.land _ 9259542123273814144 = 0%Z |- _ => exact (sp_swar8 E p _ KB) end
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_c98 : forall (IP IL : Z) (c0 spl : word) xra xt2 xs0 xs1 xa0 xa2 xa4 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> (A <= IP)%Z -> (1 <= IL)%Z -> (IP + IL <= LAST)%Z -> sp_ge48 E IP (IP + IL) ->
    evt usegs (spu_post E) (SPS E 0x5bcf4 xra (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 IL) xt2 xs0 xs1 xa0 (Z_to_bv 64 LAST) xa2 (Z_to_bv 64 53) xa4 c0 (Z_to_bv 64 IP) (Z_to_bv 64 46)
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 OUT) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM H1 H2 H3 G1.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    assert (PF0 : sp_pfacts E IP IL 0 0) by (split; [lia|]; split; [exact G1|]; left; split; reflexivity).
    assert (FF0 : bv_unsigned (nth (Z.to_nat (IP + IL - A)) (q_txt E) (Z_to_bv 8 0)) = 46%Z -> (IP + IL < LAST)%Z -> sp_ffacts E IP IL (IP + IL + 1)).
    { intros D L. split; [lia|]. split; [exact G1|]. split; [exact D|]. apply sp_ge48_nil. }
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x5d1bc%Z => u_trap_b pc
      | 0x5c20c%Z => first [ eapply evt_eq; [| eapply (spu_1b0 E OK HSET HPM HPDC HNDC IP IL 0%Z 0%Z 0%Z (IP + IL)%Z _ c0 spl)];
                             [num_st_eq | exact INV | assumption | exact PF0 | lia | lia] | fail 100 "cut" pc ]
      | 0x5c100%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SPUINV0 E m1 (Z_to_bv 64 OUT)) by spu_close0);
                             eapply evt_eq; [| eapply (spu_0a4 IP IL (IP + IL + 1)%Z c0)]; [num_st_eq | exact INV1 | assumption | apply FF0; [assumption | lia]]
                           | fail 100 "cut" pc ]
      | 0x5bd88%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SPUINV0 E m1 (Z_to_bv 64 OUT)) by spu_close0);
                             eapply evt_eq; [| eapply (spu_L2 (Z.to_nat LAST) IP IL (IP + IL + 1)%Z c0)];
                             [num_st_eq | exact INV1 | assumption | apply FF0; [assumption | lia] | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.
End SPUFRAC2.
