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
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_tail Sj_num_fc_k14 Sj_num_fc_dc Sj_num_fc_dc2 Sj_num_fc_dc3 Sj_num_fc_ce Sj_num_fc_cf2 Sj_num_fc_cf2b Sj_num_fc_cl Sj_num_fc_cf1.
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

Section FCBTOP14.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Hypothesis PV : fcb_prov E.
  Variable Q : machine_state -> Prop.
  Hypothesis KF5 : fcb_kf5 E Q.
  Hypothesis KMSET : fcb_kmset E Q.
  Notation OUT := (q_OUT E).
  Notation f := (q_f E).

  Ltac to_tail INV FRM := first [ eapply evt_eq; [| eapply (fcb_a5c E OK PV Q KF5) with (bg := true)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut tail" ].
  Ltac to_cf2 s wv INV FRM TMD :=
    first [ lazymatch type of TMD with fcb_tmd _ ?t _ _ _ _ _ =>
              let A2N := fresh "A2N" in assert (A2N : t <> 0%Z) by lia;
              let SPN := fresh "SPN" in let HWD := fresh "HWD" in destruct (TMD A2N) as [SPN HWD];
              eapply evt_eq; [| eapply (fcb_25c E OK PV Q KF5 KMSET s wv)];
              [num_st_eq | exact INV | assumption | exact SPN | lia | exact HWD
              | first [ exfalso; lia | left; lia | right; left; split; [lia | split; reflexivity] | right; right; split; [lia | split; reflexivity] ] ] end
          | fail 100 "cut cf2" ].

  Lemma fcb_f2c : forall (t2 : Z) xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc -> fcb_tmd E t2 w IP IL FPT FL ->
    (-9223372036854775808 <= q < 9223372036854775808)%Z ->
    evt bsegs Q (FCB E 0xe9330 xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 t2) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KF5 KMSET.
    intros until FL. intros INV FRM TMD Hq. pose proof INV as INV0. fc_open INV0. fcb_env OK. fcb_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap pc
      | 0xe9e60%Z => to_tail INV FRM
      | 0xe9660%Z => to_cf2 q w INV FRM TMD
      | 0xe9458%Z => first [ eapply evt_eq; [| eapply (cf1_054 E OK PV Q KF5 KMSET q t2 w)]; [num_st_eq | exact INV | assumption | exact TMD | lia] | fail 100 "cut" pc ]
      end).
  Qed.
  Ltac cl_table mm :=
    let tb := fresh "tb" in let TBL := fresh "TBL" in let TB := fresh "TB" in let TBZ := fresh "TBZ" in
    destruct (image_readable_b bsegs mm (Z.to_nat 368) 0x2b6a8 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TBL & TB);
    assert (TBZ : Z.of_nat (length tb) = 368%Z) by (rewrite TBL; apply Z2Nat.id; lia); clear TBL.
  Ltac to_cl L INVc := first [ eapply evt_eq; [| eapply (L E OK PV Q KF5)]; [num_st_eq | exact INVc | assumption] | fail 100 "cut cl" ].

  Lemma fcb_49c : forall (s : Z) xra xt0 xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc -> (-22 <= s < 0)%Z ->
    evt bsegs Q (FCB E 0xe98a0 xra xt0 xt1 xt2 (Z_to_bv 64 s) xa1 (Z_to_bv 64 (OUT / 8 + 2147450880)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 OUT)
                     xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KF5.
    intros until FL. intros INV FRM HS. pose proof INV as INV0. fc_open INV0. fcb_env OK. fcb_prov_tbl PV. cl_table mm.
    assert (D1 : IsData xa1) by exact I.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap pc
      | 0xe9404%Z => to_cl fcb_000 INV
      end).
  Qed.

  Lemma fcb_fac : forall (s : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc -> (-22 <= s <= 22)%Z ->
    evt bsegs Q (FCB E 0xe93b0 xra xt0 xt1 xt2 (Z_to_bv 64 s) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KF5.
    intros until FL. intros INV FRM HS. pose proof INV as INV0. fc_open INV0. fcb_env OK. fcb_prov_tbl PV. cl_table mm.
    assert (D1 : IsData xa1) by exact I. assert (D3 : IsData xa3) by exact I.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap pc
      | 0xe9404%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : FCINV E m1 true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL) by fc_close); to_cl fcb_000 INV1 | fail 100 "cut" pc ]
      | 0xe98a0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : FCINV E m1 true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL) by fc_close);
                             eapply evt_eq; [| eapply (fcb_49c s)]; [num_st_eq | exact INV1 | assumption | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_400 : forall (s t2 : Z) (wv : word) xra xt0 xt1 xt2 xa1 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q wv lm nb tm IP IL FPT FL -> frm0 xfc -> fcb_tmd E t2 wv IP IL FPT FL ->
    (-9223372036854775808 <= q < 9223372036854775808)%Z -> (-22 <= s <= 22)%Z ->
    evt bsegs Q (FCB E 0xe9804 xra xt0 xt1 xt2 (Z_to_bv 64 s) xa1 (Z_to_bv 64 t2) wv xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KF5 KMSET.
    intros until FL. intros INV FRM TMD Hq HS. pose proof INV as INV0. fc_open INV0. fcb_env OK. fcb_prov_tbl PV. cl_table mm.
    assert (D1 : IsData xa1) by exact I.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap pc
      | 0xe9330%Z => first [ eapply evt_eq; [| eapply (fcb_f2c t2)]; [num_st_eq | exact INV | assumption | exact TMD | exact Hq] | fail 100 "cut" pc ]
      | 0xe9f4c%Z => to_cl fcb_b48 INV
      | 0xe9414%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : FCINV E m1 true js c0 c8 c16 c24 c32 c40 c48 c56 q wv lm nb tm IP IL FPT FL) by fc_close); to_cl fcb_010 INV1 | fail 100 "cut" pc ]
      | 0xe9888%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : FCINV E m1 true js c0 c8 c16 c24 c32 c40 c48 c56 q wv lm nb tm IP IL FPT FL) by fc_close); to_cl fcb_484 INV1 | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_f60 : forall (t2 : Z) xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc -> fcb_tmd E t2 w IP IL FPT FL ->
    (-9223372036854775808 <= q < 9223372036854775808)%Z ->
    evt bsegs Q (FCB E 0xe9364 xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 t2) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KF5 KMSET.
    intros until FL. intros INV FRM TMD Hq. pose proof INV as INV0. fc_open INV0. fcb_env OK. fcb_prov PV.
    pose proof (unsigned_lit8 nb ltac:(lia)) as HT8.
    assert (DW : IsData w) by exact I.
    destruct (image_readable_b bsegs mm 4 0x173280 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (fmin & FML & FMIN).
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap pc
      | 0xe9330%Z => first [ eapply evt_eq; [| eapply (fcb_f2c t2)]; [num_st_eq | exact INV | assumption | exact TMD | exact Hq] | fail 100 "cut" pc ]
      | 0xe93b0%Z => first [ eapply evt_eq; [| eapply (fcb_fac q)]; [num_st_eq | exact INV | assumption | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
      | 0xe9804%Z => first [ eapply evt_eq; [| eapply (fcb_400 q t2 w)]; [num_st_eq | exact INV | assumption | exact TMD | exact Hq | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Theorem fcb_f14 : fcb_kf14 E Q.
  Proof using OK PV KF5 KMSET.
    unfold fcb_kf14. intros until FL. intros INV FRM HTM Hq. pose proof INV as INV0. fc_open INV0. fcb_env OK. fcb_prov PV.
    assert (TMC : (tm = 0 \/ tm = 1)%Z) by lia.
    destruct TMC as [-> | ->].
    - bwalk ltac:(fun pc => lazymatch pc with
        | 0xe9f5c%Z => u_trap pc
        | 0xe9364%Z => first [ eapply evt_eq; [| eapply (fcb_f60 0%Z)]; [num_st_eq | exact INV | assumption | intros HH; exfalso; lia | exact Hq] | fail 100 "cut" pc ]
        | 0xe9330%Z => first [ eapply evt_eq; [| eapply (fcb_f2c 0%Z)]; [num_st_eq | exact INV | assumption | intros HH; exfalso; lia | exact Hq] | fail 100 "cut" pc ]
        end).
    - bwalk ltac:(fun pc => lazymatch pc with
        | 0xe9f5c%Z => u_trap pc
        | 0xe9364%Z => first [ eapply evt_eq; [| eapply (fcb_f60 1%Z)]; [num_st_eq | exact INV | assumption | intros _; apply HTM; lia | exact Hq] | fail 100 "cut" pc ]
        | 0xe9330%Z => first [ eapply evt_eq; [| eapply (fcb_f2c 1%Z)]; [num_st_eq | exact INV | assumption | intros _; apply HTM; lia | exact Hq] | fail 100 "cut" pc ]
        end).
  Qed.
End FCBTOP14.
