(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU SjNumN.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_pm_defs Sj_num_pm_round.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.
Local Ltac unorm_in H ::= unorm_in_n H.

Section PMBTF.
  Variable E : pmbenv.
  Hypothesis OK : pmb_ok E.
  Hypothesis PV : pmb_prov E.
  Notation X := (p_X E).
  Notation DGA := (p_DG E).
  Notation IP := (p_IP E).
  Notation IL := (p_IL E).
  Notation FPT := (p_FPT E).
  Notation FL := (p_FL E).

  Lemma pm_tf_Z1e : forall (f : nat) (p : Z) xra xt2 xs0 xs1 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (FPT <= p < FPT + FL)%Z ->
    (FPT + FL - p <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xeba24 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 (Z_to_bv 64 48) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 p) (Z_to_bv 64 DGA) (Z_to_bv 64 p) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (FPT + FL)) xt5 xt6 mm).
  Proof using OK PV.
    intros f. induction f as [|f IH]; intros until w48; intros INV HF Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xebc38%Z => u_trap pc
      | 0xeba64%Z => first [ eapply evt_eq; [| eapply (pm_roundB E OK PV) with (len := len)]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0xebbfc%Z => first [ eapply (pm_exit E OK) with (dg := 769%Z) (len := len); [exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0xeba24%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z) with (len := len)]; [num_st_eq | exact INV | exact HF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_610 : forall xra xt2 xs0 xs1 xa0 xa2 xa5 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 mm len w8 w16 w24 w32 w40 w48 p,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xeba14 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + 496)) xa2 (Z_to_bv 64 DGA) (Z_to_bv 64 p) xa5 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (FPT + FL)) xt5 xt6 mm).
  Proof using OK PV.
    intros until p. intros INV HF Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xebc38%Z => u_trap pc
      | 0xebbfc%Z => first [ eapply (pm_exit E OK) with (dg := 769%Z) (len := len); [exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0xeba24%Z => first [ eapply evt_eq; [| eapply (pm_tf_Z1e (Z.to_nat (FPT + FL - p)) p) with (len := len)]; [num_st_eq | exact INV | exact HF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_Z8e : forall (f : nat) (p0 k : Z) xra xt2 xa0 xa5 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (FPT <= p0)%Z ->
    (0 <= k)%Z ->
    (p0 + 8 * k + 8 <= FPT + FL)%Z ->
    (FPT + FL - (p0 + 8 * k) <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xeb960 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 7) xa0 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (p0 + 8 * k)) (Z_to_bv 64 DGA) (Z_to_bv 64 (p0 + 8 * k)) xa5 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (FPT + FL - (p0 + 8 * k))) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 (2147450880 + p0 / 8 + k)) mm).
  Proof using OK PV.
    intros f. induction f as [|f IH]; intros until w48; intros INV HF Hp Hk Hp8 Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xebc38%Z => u_trap pc
      | 0xeba64%Z => first [ eapply evt_eq; [| eapply (pm_roundB E OK PV) with (len := len)]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0xeba14%Z => first [ eapply evt_eq; [| eapply pm_tf_610 with (len := len) (p := (p0 + 8 * k + 8)%Z)]; [num_st_eq | exact INV | exact HF | lia] | fail 100 "cut" pc ]
      | 0xeb960%Z => first [ eapply evt_eq; [| eapply (IH p0 (k + 1)%Z) with (len := len)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_52c : forall xra xt2 xs0 xs1 xa0 xa2 xa5 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 mm len w8 w16 w24 w32 w40 w48 p,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xeb930 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + 496)) xa2 (Z_to_bv 64 DGA) (Z_to_bv 64 p) xa5 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (FPT + FL)) xt5 xt6 mm).
  Proof using OK PV.
    intros until p. intros INV HF Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xebc38%Z => u_trap pc
      | 0xeba14%Z => first [ eapply evt_eq; [| eapply pm_tf_610 with (len := len) (p := p)]; [num_st_eq | exact INV | exact HF | lia] | fail 100 "cut" pc ]
      | 0xeb960%Z => first [ eapply evt_eq; [| eapply (pm_tf_Z8e (Z.to_nat (FPT + FL - p)) p 0%Z) with (len := len)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_4f8 : forall xra xt2 xs0 xs1 xa0 xa2 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 mm len w8 w16 w24 w32 w40 w48 p,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    (len <= 61)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xeb8fc xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + 496)) xa2 (Z_to_bv 64 DGA) (Z_to_bv 64 p) (Z_to_bv 64 len) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (FPT + FL)) xt5 xt6 mm).
  Proof using OK PV.
    intros until p. intros INV HF Hp Hl. pm_open INV. pm_env OK. pm_prov PV. assert (DV : IsData xs7) by exact I.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xebc38%Z => u_trap pc
      | 0xeb930%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 (len + 1) 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_tf_52c with (len := (len + 1)%Z) (p := p)]; [num_st_eq | exact INV1 | exact HF | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_4ec : forall xra xt2 xs0 xs1 xa0 xa2 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 mm len w8 w16 w24 w32 w40 w48 p,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xeb8f0 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + 496)) xa2 (Z_to_bv 64 DGA) (Z_to_bv 64 p) (Z_to_bv 64 len) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (FPT + FL)) xt5 xt6 mm).
  Proof using OK PV.
    intros until p. intros INV HF Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xeb930%Z => first [ eapply evt_eq; [| eapply pm_tf_52c with (len := len) (p := p)]; [num_st_eq | exact INV | exact HF | lia] | fail 100 "cut" pc ]
      | 0xeb8fc%Z => first [ eapply evt_eq; [| eapply pm_tf_4f8 with (len := len) (p := p)]; [num_st_eq | exact INV | exact HF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_CA : forall (f : nat) (j : Z) xra xs0 xs1 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 mm len w8 w16 w24 w32 w40 w48 p,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    (0 <= j <= len - 1)%Z ->
    (len - 1 - j <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xeb3a4 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (18446744073709551112 + 8 * j)) xs0 xs1 (Z_to_bv 64 (X + 8 + 8 * j)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (X + 8 + 8 * j)) (Z_to_bv 64 DGA) (Z_to_bv 64 p) (Z_to_bv 64 len) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 (len - 1 - j)) xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (FPT + FL)) xt5 xt6 mm).
  Proof using OK PV.
    intros f. induction f as [|f IH]; intros until p; intros INV HF Hp Hj Hf.
    - pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. bstep.
      bwalk ltac:(fun pc => lazymatch pc with
      | 0xebc38%Z => u_trap pc
      | 0xeb8f0%Z => first [ eapply evt_eq; [| eapply pm_tf_4ec with (len := len) (p := p)]; [num_st_eq | exact INV | exact HF | lia] | fail 100 "cut" pc ]
      end).
    - pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. bstep.
      bwalk ltac:(fun pc => lazymatch pc with
      | 0xebc38%Z => u_trap pc
      | 0xeb8f0%Z => first [ eapply evt_eq; [| eapply pm_tf_4ec with (len := len) (p := p)]; [num_st_eq | exact INV | exact HF | lia] | fail 100 "cut" pc ]
      | 0xeb930%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_tf_52c with (len := len) (p := p)]; [num_st_eq | exact INV1 | exact HF | lia] | fail 100 "cut" pc ]
      | 0xeb3a4%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply (IH (j + 1)%Z) with (len := len) (p := p)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_f50 : forall xra xt2 xs0 xs1 xa0 xa2 xa5 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 mm len w8 w16 w24 w32 w40 w48 p,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xeb354 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + 496)) xa2 (Z_to_bv 64 DGA) (Z_to_bv 64 p) xa5 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (FPT + FL)) xt5 xt6 mm).
  Proof using OK PV.
    intros until p. intros INV HF Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. assert (DV : IsData xs7) by exact I.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xebc38%Z => u_trap pc
      | 0xeb930%Z => first [ first [ eapply evt_eq; [| eapply pm_tf_52c with (len := len) (p := p)]; [num_st_eq | exact INV | exact HF | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_tf_52c with (len := len) (p := p)]; [num_st_eq | exact INV1 | exact HF | lia] ] | fail 100 "cut" pc ]
      | 0xeb8fc%Z => first [ eapply evt_eq; [| eapply pm_tf_4f8 with (len := len) (p := p)]; [num_st_eq | exact INV | exact HF | lia | lia] | fail 100 "cut" pc ]
      | 0xeb3a4%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply (pm_tf_CA (Z.to_nat len) 0%Z) with (len := len) (p := p)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_f10 : forall xra xt2 xs0 xs1 xa0 xa2 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 mm len w8 w16 w24 w32 w40 w48 p,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xeb314 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + 496)) xa2 (Z_to_bv 64 DGA) (Z_to_bv 64 p) (Z_to_bv 64 len) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (FPT + FL)) xt5 xt6 mm).
  Proof using OK PV.
    intros until p. intros INV HF Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. assert (DC : IsData xt3) by exact I.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xebc38%Z => u_trap pc
      | 0xeb354%Z => first [ first [ eapply evt_eq; [| eapply pm_tf_f50 with (len := len) (p := p)]; [num_st_eq | exact INV | exact HF | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 (len + 1) 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_tf_f50 with (len := (len + 1)%Z) (p := p)]; [num_st_eq | exact INV1 | exact HF | lia] ] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_SM : forall (f : nat) (i : Z) xra xt2 xs0 xs1 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt6 mm len w8 w16 w24 w32 w40 w48 p,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    (0 <= i < len)%Z ->
    (len - i <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xeb2d0 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 DGA) (Z_to_bv 64 p) (Z_to_bv 64 len) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 (63 - i)) xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 (len - i)) xt6 mm).
  Proof using OK PV.
    intros f. induction f as [|f IH]; intros until p; intros INV HF Hp Hi Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. assert (DC : IsData xt3) by exact I. assert (DY : IsData xt2) by exact I.
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xebc38%Z => u_trap pc
      | 0xeb314%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_tf_f10 with (len := len) (p := p)]; [num_st_eq | exact INV1 | exact HF | lia] | fail 100 "cut" pc ]
      | 0xeb2d0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply (IH (i + 1)%Z) with (len := len) (p := p)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf : forall xra xt2 xs0 xs1 xa0 xa2 xa5 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 mm len w8 w16 w24 w32 w40 w48 p cn,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    (0 <= cn <= 19)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xeb278 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + 496)) xa2 (Z_to_bv 64 DGA) (Z_to_bv 64 p) xa5 (Z_to_bv 64 cn) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 177376) (Z_to_bv 64 (FPT + FL)) xt5 xt6 mm).
  Proof using OK PV.
    intros until cn. intros INV HF Hp Hc. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xebc38%Z => u_trap pc
      | 0xeb354%Z => first [ eapply evt_eq; [| eapply pm_tf_f50 with (len := len) (p := p)]; [num_st_eq | exact INV | exact HF | lia] | fail 100 "cut" pc ]
      | 0xeb2d0%Z => first [ eapply evt_eq; [| eapply (pm_tf_SM (Z.to_nat len) 0%Z) with (len := len) (p := p)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMBTF.
