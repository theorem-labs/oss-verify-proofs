(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumU SjNumN SjNumSwar.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_tail Sj_num_fc_dc Sj_num_fc_dc2 Sj_num_fc_dc3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
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

Section FCBCE.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Hypothesis PV : fcb_prov E.
  Variable Q : machine_state -> Prop.
  Hypothesis KF5 : fcb_kf5 E Q.
  Hypothesis KMSET : fcb_kmset E Q.
  Notation OUT := (q_OUT E).
  Notation f := (q_f E).

  Lemma fcb_5a0 : forall (s : Z) (wv : word) xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs9 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc ->
    fcb_spans E IP IL FPT FL -> (-342 <= s <= 308)%Z -> (bv_unsigned wv <> 0)%Z ->
    evt bsegs Q (FCB E 0xe9620 xra xt0 xt1 xt2 xa0 wv xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7 (Z_to_bv 64 s) xs9 (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KF5 KMSET.
    intros until FL. intros INV FRM SPN HQ HW. pose proof INV as INV0. fc_open INV0. fcb_env OK. fcb_prov_tbl PV.
    zstep. if_cases KW; zify_cond KW; [exfalso; lia|].
    assert (DW : IsData wv) by exact I.
    destruct (image_readable_b bsegs mm (Z.to_nat 10416) 0x28700 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TBL & TB).
    assert (TBZ : Z.of_nat (length tb) = 10416%Z) by (rewrite TBL; apply Z2Nat.id; lia). clear TBL.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xe9bd8%Z => u_trap pc
      | 0xe97a0%Z => idtac
      end).
    all: lazymatch goal with |- context [Z_to_bv 64 ((bv_swrap 32 (Z.shiftr (?qq * 217706) 16) mod 18446744073709551616 - ?hf + -31692) mod 18446744073709551616 - ?hf0)] =>
           replace (Z_to_bv 64 ((bv_swrap 32 (Z.shiftr (qq * 217706) 16) mod 18446744073709551616 - hf + -31692) mod 18446744073709551616 - hf0))
             with (Z_to_bv 64 (qq * 217706 / 65536 - hf - 31692 - hf0))
             by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 16)%Z with 65536%Z; rewrite swrap32_id by (Z.div_mod_to_equations; lia);
                 apply Z_to_bv_eqm; Z.div_mod_to_equations; lia);
           assert (PR : (-962468 <= qq * 217706 / 65536 - hf - 31692 - hf0 <= 962468)%Z) by (Z.div_mod_to_equations; lia)
         end.
    all: bwalk ltac:(fun pc => lazymatch pc with
      | 0xe9adc%Z => first [ eapply evt_eq; [| eapply (fcb_a5c E OK PV Q KF5) with (bg := true)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut" pc ]
      | 0xe97a4%Z => first [ eapply evt_eq; [| eapply (fcb_724 E OK PV Q KMSET)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | exact PR] | fail 100 "cut" pc ]
      end).
  Qed.
End FCBCE.
