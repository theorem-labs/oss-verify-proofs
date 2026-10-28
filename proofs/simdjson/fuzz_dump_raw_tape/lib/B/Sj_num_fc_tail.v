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
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs.
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

Notation FCB E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 xF xfc mm :=
  (FCS E pc xra xt0 xt1 xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) xs5 xs6 xs7 xs8 xs9 xs10
       (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).

Definition fcb_kf5 (E : fcbenv) (Q : machine_state -> Prop) : Prop :=
  forall xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 xF xfc mm bg js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm bg js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc ->
    evt bsegs Q (FCB E 0x82b14 (Z_to_bv 64 0xe9ed4) xt0 xt1 xt2 (Z_to_bv 64 (q_S E)) (Z_to_bv 64 128) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (q_f E)) xs5 xs6 xs7 xs8 xs9 xs10
                     xt3 xt4 xt5 xt6 xF xfc mm).

Section FCBTAIL.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Hypothesis PV : fcb_prov E.
  Variable Q : machine_state -> Prop.
  Hypothesis KF5 : fcb_kf5 E Q.
  Notation OUT := (q_OUT E).
  Notation f := (q_f E).

  Lemma fcb_a5c : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm bg js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm bg js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc ->
    evt bsegs Q (FCB E 0xe9e60 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KF5.
    intros until FL. intros INV FRM.
    destruct bg;
    ( pose proof INV as INV0; fc_open INV0; pose proof OK as OK'; fcb_env OK'; fcb_prov PV;
      pose proof (unsigned_lit8 nb ltac:(lia)) as HT8;
      assert (D1 : IsData xs6) by exact I; assert (D2 : IsData xs9) by exact I; assert (D3 : IsData w) by exact I;
      bwalk ltac:(fun pc => lazymatch pc with
        | 0xe9f5c%Z => u_trap pc
        | 0x82b14%Z => first [ num_cur_mem ltac:(fun m1 => lazymatch goal with INV : FCINV E _ ?b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
                                 assert (INV1 : FCINV E m1 b js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL) by fc_close end);
                               eapply evt_eq; [| eapply KF5]; [num_st_eq | exact INV1 | exact FRM] | fail 100 "cut" pc ]
        end) ).
  Qed.

  Lemma fcb_950 : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm false js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc ->
    evt bsegs Q (FCB E 0xe9d54 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KF5.
    intros until FL. intros INV FRM. pose proof INV as INV0. fc_open INV0. fcb_env OK. fcb_prov PV.
    assert (D1 : IsData xa0) by exact I. assert (D2 : IsData xa1) by exact I.
    apply (rw_cells_split_CB bsegs _ _ [] 63 js [] (repeat 1%nat 63)) in BSH; [| reflexivity]. cbn [app] in BSH. rewrite app_nil_r in BSH.
    cbn [mk_CB_cells repeat] in BSH.
    repeat match type of BSH with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in BSH; clearbody j end.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap pc
      | 0xe9e60%Z => first [ pose proof (fcb_merge_all _ _ _ BSH) as BSH'; clear BSH; cbn [cells_size csize Nat.add cells_bytes cbytes app] in BSH';
                             num_cur_mem ltac:(fun m1 => eassert (INV1 : FCINV E m1 false _ c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL) by fc_close);
                             eapply evt_eq; [| eapply fcb_a5c]; [num_st_eq | exact INV1 | exact FRM] | fail 100 "cut" pc ]
      end).
  Qed.
End FCBTAIL.
