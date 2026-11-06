(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_sp_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Section SPUCL.
  Variable E : spuenv.
  Hypothesis OK : spu_ok E.

  Lemma spu_d00 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc ->
    evt usegs (spu_post E) (SPS E 0x5cd5c xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until FL. intros INV FRM. pose proof INV as INV0. spu_open INV0. spu_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5d140%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SPUINV E m1 nb IP IL FPT FL) by spu_close); eapply (spu_exit E OK); [exact INV1 | assumption] | fail 100 "cut" pc ]
      end).
  Qed.
  Lemma spu_8fc : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc ->
    evt usegs (spu_post E) (SPS E 0x5c958 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until FL. intros INV FRM. pose proof INV as INV0. spu_open INV0. spu_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5d1bc%Z => u_trap pc
      | 0x5d140%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SPUINV E m1 nb IP IL FPT FL) by spu_close); eapply (spu_exit E OK); [exact INV1 | assumption] | fail 100 "cut" pc ]
      end).
  Qed.
  Lemma spu_148 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc ->
    evt usegs (spu_post E) (SPS E 0x5d1a4 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until FL. intros INV FRM. pose proof INV as INV0. spu_open INV0. spu_env OK. assert (D3 : IsData xa3) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5d1bc%Z => u_trap pc
      | 0x5d140%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SPUINV E m1 nb IP IL FPT FL) by spu_close); eapply (spu_exit E OK); [exact INV1 | assumption] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_8c8 : forall (q : Z) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> (-22 <= q <= 22)%Z ->
    evt usegs (spu_post E) (SPS E 0x5c924 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until FL. intros INV FRM HQ. pose proof INV as INV0. spu_open INV0. spu_env OK.
    assert (D3 : IsData xa3) by exact I. assert (D4 : IsData xa4) by exact I.
    destruct (image_readable_b usegs mm (Z.to_nat 184) 0x1ca00 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TBL & TB).
    assert (TBZ : Z.of_nat (length tb) = 184%Z) by (rewrite TBL; apply Z2Nat.id; lia). clear TBL.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5d1bc%Z => u_trap pc
      | 0x5cd5c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SPUINV E m1 nb IP IL FPT FL) by spu_close); eapply evt_eq; [| eapply spu_d00]; [num_st_eq | exact INV1 | assumption] | fail 100 "cut" pc ]
      | 0x5c958%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SPUINV E m1 nb IP IL FPT FL) by spu_close); eapply evt_eq; [| eapply spu_8fc]; [num_st_eq | exact INV1 | assumption] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_040 : forall (q : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> (0 <= q <= 22)%Z ->
    evt usegs (spu_post E) (SPS E 0x5d09c xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (8 * q)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until FL. intros INV FRM HQ. pose proof INV as INV0. spu_open INV0. spu_env OK.
    assert (D3 : IsData xa3) by exact I. assert (D4 : IsData xa4) by exact I.
    destruct (image_readable_b usegs mm (Z.to_nat 184) 0x1ca00 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TBL & TB).
    assert (TBZ : Z.of_nat (length tb) = 184%Z) by (rewrite TBL; apply Z2Nat.id; lia). clear TBL.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5d1bc%Z => u_trap pc
      | 0x5d1a4%Z => first [ eapply evt_eq; [| eapply spu_148]; [num_st_eq | exact INV | assumption] | fail 100 "cut" pc ]
      | 0x5cd5c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SPUINV E m1 nb IP IL FPT FL) by spu_close); eapply evt_eq; [| eapply spu_d00]; [num_st_eq | exact INV1 | assumption] | fail 100 "cut" pc ]
      | 0x5c958%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SPUINV E m1 nb IP IL FPT FL) by spu_close); eapply evt_eq; [| eapply spu_8fc]; [num_st_eq | exact INV1 | assumption] | fail 100 "cut" pc ]
      end).
  Qed.
End SPUCL.
