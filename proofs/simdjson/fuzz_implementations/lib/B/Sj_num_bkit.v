(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU SjNumN.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.U Require Export Sj_num_kitu Sj_num_kitn Sj_num_kitw.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Export Sj_num_amem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition b_consts (m : word -> option byte) : Prop :=
  ro_cells bsegs m 1572552 [C8 (Z_to_bv 64 1612152)] /\ ro_cells bsegs m 1612152 [C8 (Z_to_bv 64 2147450880)].

Lemma b_consts_of : forall m, client_consts m -> b_consts m.
Proof. intros m (G1 & G2 & _). split; [exact G1| exact G2]. Qed.

Lemma shz_read_ptr : forall (m : word -> option byte) a n Ea adr, shz m a n -> a <= 8 * (Ea - 2147450880) < a + n -> adr = wa Ea ->
  ov_read_bytes bsegs m adr 1 = Some [Z_to_bv 8 0].
Proof.
  intros m a n Ea adr H HE ->. pose proof (H (8 * (Ea - 2147450880)) HE) as R.
  replace (8 * (Ea - 2147450880) / 8 + 2147450880) with Ea in R by (rewrite Z.mul_comm, Z.div_mul by lia; lia). exact R.
Qed.

Ltac asan_ptr_hook :=
  match goal with
  | |- context [ov_read_bytes bsegs ?m ?a 1] =>
      let Ea := addr_expr a in
      match goal with
      | SHP : (forall m', munch ?W ?m0 m' -> wmono bsegs ?m0 m' -> shz m' ?a0 ?n0), MU : munch ?W ?m0 m, WM : wmono bsegs ?m0 m |- _ =>
          rewrite (shz_read_ptr m a0 n0 Ea a (SHP m MU WM) ltac:(Z.div_mod_to_equations; lia) ltac:(reflexivity))
      end
  end;
  load_post.

Ltac bstep := nstep; anorm.
Ltac bkstep := ukstep; anorm.

Ltac bwalk_fuel n K :=
  lazymatch n with
  | O => lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 100 "bwalk: out of fuel at" pc end
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (bstep; bwalk_fuel n' K) ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H; unorm_in H;
          tryif num_is_data H then (clear H; bwalk_fuel n' K) else first [ solve [exfalso; lia] | bwalk_fuel n' K ]
      end
  end.
Ltac bwalk K := bwalk_fuel 400%nat K.

Ltac bwalkd_fuel n K :=
  lazymatch n with
  | O => idtac "bwalkd: out of fuel"
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (bstep; bwalkd_fuel n' K) | idtac "STUCK at" pc ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H; unorm_in H;
          tryif num_is_data H then (clear H; bwalkd_fuel n' K) else first [ solve [exfalso; lia] | bwalkd_fuel n' K ]
      end
  end.
Ltac bwalkd K := bwalkd_fuel 400%nat K.

Ltac bkwalk_fuel n K :=
  lazymatch n with
  | O => lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 100 "bkwalk: out of fuel at" pc end
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (bkstep; bkwalk_fuel n' K) ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H; unorm_in H;
          first [ solve [exfalso; lia] | bkwalk_fuel n' K ]
      end
  end.
Ltac bkwalk K := bkwalk_fuel 200%nat K.

Ltac bkwalkd_fuel n K :=
  lazymatch n with
  | O => idtac "bkwalkd: out of fuel"
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (bkstep; bkwalkd_fuel n' K) | idtac "STUCK at" pc ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H; unorm_in H;
          first [ solve [exfalso; lia] | bkwalkd_fuel n' K ]
      end
  end.
Ltac bkwalkd K := bkwalkd_fuel 200%nat K.
