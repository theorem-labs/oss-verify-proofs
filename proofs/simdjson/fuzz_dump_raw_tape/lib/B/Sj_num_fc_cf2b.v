(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU SjNumN SjNumSwar.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_tail Sj_num_fc_dc Sj_num_fc_dc2 Sj_num_fc_dc3 Sj_num_fc_ce Sj_num_fc_cf2.
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
Local Ltac nnorm ::= nnorm_cf.

Section FCBCF2B.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Hypothesis PV : fcb_prov E.
  Variable Q : machine_state -> Prop.
  Hypothesis KF5 : fcb_kf5 E Q.
  Hypothesis KMSET : fcb_kmset E Q.
  Notation OUT := (q_OUT E).
  Notation f := (q_f E).

  Lemma fcb_25c : forall (s : Z) (wv : word) xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs5 (xs6 : word) xs7 (xs9 : word) xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc -> fcb_spans E IP IL FPT FL ->
    (-9223372036854775808 <= s < 9223372036854775808)%Z -> (1 <= bv_unsigned wv <= 18446744073709551614)%Z -> cf1b_out s xs6 xs9 ->
    evt bsegs Q (FCB E 0xe9660 xra xt0 xt1 xt2 xa0 wv xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7 (Z_to_bv 64 s) xs9 (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KF5 KMSET.
    intros until FL. intros INV FRM SPN Hq HW R. pose proof OK as OK'. fcb_env OK'.
    assert (W1 : ((bv_unsigned wv + 1) mod 18446744073709551616 = bv_unsigned wv + 1)%Z) by (apply Z.mod_small; lia).
    assert (HW0 : (bv_unsigned wv <> 0)%Z) by lia.
    destruct R as [R | [(R & -> & ->) | (R & -> & ->)]].
    - bwalk ltac:(fun pc => lazymatch pc with
        | 0xe9f5c%Z => u_trap pc
        | 0xe9694%Z => first [ eapply evt_eq; [| eapply (cf2_290 E OK PV Q KF5 KMSET s wv)]; [num_st_eq | exact INV | assumption | exact SPN | lia | exact HW0] | fail 100 "cut" pc ]
        end).
    - bwalk ltac:(fun pc => lazymatch pc with
        | 0xe9f5c%Z => u_trap pc
        | 0xe9e60%Z => first [ eapply evt_eq; [| eapply (fcb_a5c E OK PV Q KF5) with (bg := true)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut" pc ]
        end).
    - bwalk ltac:(fun pc => lazymatch pc with
        | 0xe9f5c%Z => u_trap pc
        | 0xe9e60%Z => first [ eapply evt_eq; [| eapply (fcb_a5c E OK PV Q KF5) with (bg := true)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut" pc ]
        end).
  Qed.
End FCBCF2B.
