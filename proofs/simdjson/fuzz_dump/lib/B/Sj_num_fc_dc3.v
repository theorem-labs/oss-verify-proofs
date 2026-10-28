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
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_tail Sj_num_fc_dc Sj_num_fc_dc2.
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

Section FCBDC3.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Hypothesis PV : fcb_prov E.
  Variable Q : machine_state -> Prop.
  Hypothesis KMSET : fcb_kmset E Q.
  Notation OUT := (q_OUT E).
  Notation f := (q_f E).

  Lemma fcb_LC : forall (s p2 v : Z) xra xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc ->
    fcb_spans E IP IL FPT FL -> (-342 <= s <= 326)%Z -> (-962468 <= p2 <= 962468)%Z -> (0 <= v <= 99)%Z ->
    evt bsegs Q (FCB E 0xe9840 xra xt0 xt1 xt2 (Z_to_bv 64 v) (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 99) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7
                     (Z_to_bv 64 s) (Z_to_bv 64 p2) (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KMSET.
    intros until FL. intros INV FRM SPN HS HP2 HV. pose proof OK as OK'. fcb_env OK'.
    bkstep.
    bkwalk ltac:(fun pc => lazymatch pc with
      | 0xe9bd8%Z => u_trap pc
      | 0xe9840%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0xe985c%Z => first [ eapply evt_eq; [| eapply (fcb_7dc E OK PV Q KMSET (s + 1)%Z p2)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_794 : forall (s p2 v : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc ->
    fcb_spans E IP IL FPT FL -> (-342 <= s <= 326)%Z -> (-962468 <= p2 <= 962468)%Z -> (0 <= v <= 99)%Z ->
    evt bsegs Q (FCB E 0xe9814 xra xt0 xt1 xt2 (Z_to_bv 64 v) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7
                     (Z_to_bv 64 s) (Z_to_bv 64 p2) (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KMSET.
    intros until FL. intros INV FRM SPN HS HP2 HV. pose proof OK as OK'. fcb_env OK'.
    bkwalk ltac:(fun pc => lazymatch pc with
      | 0xe9bd8%Z => u_trap pc
      | 0xe9840%Z => first [ eapply evt_eq; [| eapply (fcb_LC s p2 v)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | lia] | fail 100 "cut" pc ]
      | 0xe985c%Z => first [ eapply evt_eq; [| eapply (fcb_7dc E OK PV Q KMSET (s)%Z p2)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_7a0 : forall (s p2 v : Z) xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc ->
    fcb_spans E IP IL FPT FL -> (-342 <= s <= 326)%Z -> (-962468 <= p2 <= 962468)%Z -> (0 <= v <= 99)%Z ->
    evt bsegs Q (FCB E 0xe9820 xra xt0 xt1 xt2 xa0 (Z_to_bv 64 v) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7
                     (Z_to_bv 64 s) (Z_to_bv 64 p2) (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KMSET.
    intros until FL. intros INV FRM SPN HS HP2 HV. pose proof OK as OK'. fcb_env OK'.
    bkwalk ltac:(fun pc => lazymatch pc with
      | 0xe9bd8%Z => u_trap pc
      | 0xe9840%Z => first [ eapply evt_eq; [| eapply (fcb_LC s p2 v)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | lia] | fail 100 "cut" pc ]
      | 0xe985c%Z => first [ eapply evt_eq; [| eapply (fcb_7dc E OK PV Q KMSET (s)%Z p2)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_LB : forall (s p2 v : Z) xra xt0 xt1 xt2 xa0 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc ->
    fcb_spans E IP IL FPT FL -> (-342 <= s <= 324)%Z -> (-962468 <= p2 <= 962468)%Z -> (0 <= v <= 9999)%Z ->
    evt bsegs Q (FCB E 0xe97f0 xra xt0 xt1 xt2 xa0 (Z_to_bv 64 v) (Z_to_bv 64 2951479051793528259) (Z_to_bv 64 624) xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7
                     (Z_to_bv 64 s) (Z_to_bv 64 p2) (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KMSET.
    intros until FL. intros INV FRM SPN HS HP2 HV. pose proof OK as OK'. fcb_env OK'.
    bkstep.
    bkwalk ltac:(fun pc => lazymatch pc with
      | 0xe9bd8%Z => u_trap pc
      | 0xe97f0%Z => first [ exfalso; shr2div; Z.div_mod_to_equations; lia | fail 100 "cut" pc ]
      | 0xe9814%Z => first [ rewrite !(magic_100_m v) by lia;
                             eapply evt_eq; [| eapply (fcb_794 (s + 2)%Z p2 (v / 100)%Z)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_75c : forall (s p2 v : Z) xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc ->
    fcb_spans E IP IL FPT FL -> (-342 <= s <= 324)%Z -> (-962468 <= p2 <= 962468)%Z -> (0 <= v <= 9999)%Z ->
    evt bsegs Q (FCB E 0xe97dc xra xt0 xt1 xt2 xa0 (Z_to_bv 64 v) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7
                     (Z_to_bv 64 s) (Z_to_bv 64 p2) (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KMSET.
    intros until FL. intros INV FRM SPN HS HP2 HV. pose proof INV as INV0. fc_open INV0. pose proof OK as OK'. fcb_env OK'.
    bkwalk ltac:(fun pc => lazymatch pc with
      | 0xe9bd8%Z => u_trap pc
      | 0xe9820%Z => first [ eapply evt_eq; [| eapply (fcb_7a0 s p2 v)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | lia] | fail 100 "cut" pc ]
      | 0xe97f0%Z => first [ eapply evt_eq; [| eapply (fcb_LB s p2 v)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Definition laB (n : nat) : Z := match n with O => 100000000 | 1%nat => 1000000000000 | 2%nat => 10000000000000000 | _ => 18446744073709551616 end.
  Lemma fcb_LA : forall (n : nat) (s p2 v : Z) xra xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc ->
    fcb_spans E IP IL FPT FL -> (-342 <= s)%Z -> (s + 4 * (Z.of_nat n + 1) <= 324)%Z -> (-962468 <= p2 <= 962468)%Z -> (0 <= v < laB n)%Z -> (n <= 3)%nat ->
    evt bsegs Q (FCB E 0xe97c0 xra xt0 xt1 xt2 (Z_to_bv 64 3777893186295716171) (Z_to_bv 64 v) (Z_to_bv 64 99999999) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7
                     (Z_to_bv 64 s) (Z_to_bv 64 p2) (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KMSET.
    intros n. induction n as [|n IH]; intros until FL; intros INV FRM SPN HS1 HS2 HP2 HV Hn; pose proof OK as OK'; fcb_env OK'.
    - cbn [laB] in HV. bkstep.
      bkwalk ltac:(fun pc => lazymatch pc with
        | 0xe9bd8%Z => u_trap pc
        | 0xe97c0%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0xe97dc%Z => first [ rewrite !(magic_10000_m v) by lia;
                               eapply evt_eq; [| eapply (fcb_75c (s + 4)%Z p2 (v / 10000)%Z)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
        end).
    - assert (HVB : (0 <= v < 18446744073709551616)%Z) by (destruct n as [|[|[|n]]]; cbn [laB] in HV; lia).
      bkstep.
      bkwalk ltac:(fun pc => lazymatch pc with
        | 0xe9bd8%Z => u_trap pc
        | 0xe97c0%Z => first [ rewrite !(magic_10000_m v) by lia;
                               eapply evt_eq; [| eapply (IH (s + 4)%Z p2 (v / 10000)%Z)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | lia | | lia];
                               destruct n as [|[|[|n]]]; cbn [laB] in HV |- *; [Z.div_mod_to_equations; lia .. | exfalso; lia] | fail 100 "cut" pc ]
        | 0xe97dc%Z => first [ rewrite !(magic_10000_m v) by lia;
                               eapply evt_eq; [| eapply (fcb_75c (s + 4)%Z p2 (v / 10000)%Z)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma fcb_724 : forall (s p2 : Z) (wv : word) xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc ->
    fcb_spans E IP IL FPT FL -> (-342 <= s <= 308)%Z -> (-962468 <= p2 <= 962468)%Z ->
    evt bsegs Q (FCB E 0xe97a4 xra xt0 xt1 xt2 xa0 wv xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7
                     (Z_to_bv 64 s) (Z_to_bv 64 p2) (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KMSET.
    intros until FL. intros INV FRM SPN HQ HP2. pose proof INV as INV0. fc_open INV0. pose proof OK as OK'. fcb_env OK'.
    pose proof (bv_unsigned_in_range 64 wv) as WR. unfold bv_modulus in WR. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in WR.
    rewrite <- (Z_to_bv_bv_unsigned wv). set (wz := bv_unsigned wv) in *. clearbody wz.
    bkwalk ltac:(fun pc => lazymatch pc with
      | 0xe9bd8%Z => u_trap pc
      | 0xe97c0%Z => first [ eapply evt_eq; [| eapply (fcb_LA 3%nat s p2 wz)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | lia | cbn [laB]; lia | lia] | fail 100 "cut" pc ]
      | 0xe97dc%Z => first [ shr2div; eapply evt_eq; [| eapply (fcb_75c s p2 wz)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | lia | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
      end).
  Qed.
End FCBDC3.
