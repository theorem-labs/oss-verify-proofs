(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe SjNumU SjNumN Zpd.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks D_defs D_kit D_clx Zpm Zpl Zq2 Sj_rtf Zqc Zqd
  Zsl Zqh Zqf Zuj Zr0 Zs5 Zqx Zqy Zqz Zql Zqn.
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
    evt bsegs Q (FCB E 0xd2298 xra xt0 xt1 xt2 xa0 wv xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7 (Z_to_bv 64 s) xs9 (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KF5 KMSET.
    intros until FL. intros INV FRM SPN Hq HW R. pose proof OK as OK'. fcb_env OK'.
    assert (W1 : ((bv_unsigned wv + 1) mod 18446744073709551616 = bv_unsigned wv + 1)%Z) by (apply Z.mod_small; lia).
    assert (HW0 : (bv_unsigned wv <> 0)%Z) by lia.
    destruct R as [R | [(R & -> & ->) | (R & -> & ->)]].
    - bwalk ltac:(fun pc => lazymatch pc with
        | 0xd2b94%Z => u_trap pc
        | 0xd22cc%Z => first [ eapply evt_eq; [| eapply (cf2_290 E OK PV Q KF5 KMSET s wv)]; [num_st_eq | exact INV | assumption | exact SPN | lia | exact HW0] | fail 100 "cut" pc ]
        end).
    - bwalk ltac:(fun pc => lazymatch pc with
        | 0xd2b94%Z => u_trap pc
        | 0xd2a98%Z => first [ eapply evt_eq; [| eapply (fcb_a5c E OK PV Q KF5) with (bg := true)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut" pc ]
        end).
    - bwalk ltac:(fun pc => lazymatch pc with
        | 0xd2b94%Z => u_trap pc
        | 0xd2a98%Z => first [ eapply evt_eq; [| eapply (fcb_a5c E OK PV Q KF5) with (bg := true)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut" pc ]
        end).
  Qed.
End FCBCF2B.
