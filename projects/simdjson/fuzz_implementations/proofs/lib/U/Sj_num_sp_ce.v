(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_sp_defs Sj_num_sp_dc.
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

Lemma lor_even_1 : forall k, (0 <= k -> Z.lor (2 * k) 1 = 2 * k + 1)%Z.
Proof.
  intros k Hk. pose proof (Z.add_lor_land (2 * k) 1) as A.
  assert (L : Z.land (2 * k) 1 = 0%Z). { change 1%Z with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1)%Z with 2%Z. Z.div_mod_to_equations. lia. }
  lia.
Qed.
Lemma lor_16_8 : forall k, (0 <= k -> Z.lor (8 * (2 * k)) 8 = 8 * (2 * k) + 8)%Z.
Proof.
  intros k Hk. replace (8 * (2 * k))%Z with (Z.shiftl (2 * k) 3) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  change 8%Z with (Z.shiftl 1 3) at 1. rewrite <- Z.shiftl_lor. rewrite lor_even_1 by lia. rewrite !Z.shiftl_mul_pow2 by lia. lia.
Qed.
Ltac nnorm_ce :=
  repeat match goal with
  | |- context [Z.lor (2 * ?k) 1] => rewrite (lor_even_1 k) by lia
  | |- context [Z.lor (8 * (2 * ?k)) 8] => rewrite (lor_16_8 k) by lia
  end; nnorm_u.
Local Ltac nnorm ::= nnorm_ce.

Section SPUCE.
  Variable E : spuenv.
  Hypothesis OK : spu_ok E.
  Hypothesis HSET : spu_memset_stmt.
  Hypothesis HPM : spu_pm_stmt.
  Hypothesis HPDC : spu_pdc_stmt.
  Hypothesis HNDC : spu_ndc_stmt.

  Lemma spu_dc8 : forall (q : Z) (wv : word) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    (-342 <= q <= 308)%Z -> (bv_unsigned wv <> 0)%Z ->
    evt usegs (spu_post E) (SPS E 0x5fd80 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 xa2 xa3 wv xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until FL. intros INV FRM SPN HQ HW. pose proof INV as INV0. spu_open INV0. spu_env OK.
    zstep. if_cases KW; zify_cond KW; [exfalso; lia|].
    assert (DW : IsData wv) by exact I.
    destruct (image_readable_b usegs mm (Z.to_nat 10416) 0x1aa50 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TBL & TB).
    assert (TBZ : Z.of_nat (length tb) = 10416%Z) by (rewrite TBL; apply Z2Nat.id; lia). clear TBL.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x60118%Z => u_trap pc
      | 0x5fee0%Z => idtac
      end).
    all: lazymatch goal with |- context [Z_to_bv 64 ((bv_swrap 32 (Z.shiftr (?qq * 217706) 16) mod 18446744073709551616 - ?hf + -31692) mod 18446744073709551616 - ?hf0)] =>
           replace (Z_to_bv 64 ((bv_swrap 32 (Z.shiftr (qq * 217706) 16) mod 18446744073709551616 - hf + -31692) mod 18446744073709551616 - hf0))
             with (Z_to_bv 64 (qq * 217706 / 65536 - hf - 31692 - hf0))
             by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 16)%Z with 65536%Z; rewrite swrap32_id by (Z.div_mod_to_equations; lia);
                 apply Z_to_bv_eqm; Z.div_mod_to_equations; lia);
           assert (PR : (-1000000 <= qq * 217706 / 65536 - hf - 31692 - hf0 <= 1000000)%Z) by (Z.div_mod_to_equations; lia)
         end.
    all: uwalk ltac:(fun pc => lazymatch pc with
      | 0x60060%Z => first [ eapply evt_eq; [| eapply (spu_0a8 E OK)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut" pc ]
      | 0x5fee4%Z => first [ eapply evt_eq; [| eapply (spu_f2c E OK HSET HPM HPDC HNDC)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | exact PR] | fail 100 "cut" pc ]
      end).
  Qed.
End SPUCE.
