(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_ff_defs Sj_num_ff_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Lemma wz_signed : forall w : word, Z_to_bv 64 (bv_signed w) = w.
Proof.
  intros w. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in *. change (18446744073709551616 / 2)%Z with 9223372036854775808%Z.
  Z.div_mod_to_equations. lia.
Qed.

Section FFPN.
  Hypothesis HSPATH : ff_spath_stmt.
  Variable E : ffenv.
  Hypothesis OK : ff_ok E.
  Notation A := (f_A E).
  Notation TL := (f_TL E).
  Notation FIRST := (f_FIRST E).
  Notation LAST := (f_LAST E).

  Lemma ff_620w : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 (xa3 : word) xa4 xa5 xa6 (xa7 : word) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc ->
    evt psegs (ff_post E) (FFS E 0x3c514 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM.
    rewrite <- (wz_signed xa7).
    pose proof (bv_signed_in_range 64 xa7 ltac:(lia)) as R. unfold bv_half_modulus, bv_modulus in R.
    change (2 ^ Z.of_N 64 / 2)%Z with 9223372036854775808%Z in R.
    eapply (ff_620 E OK (bv_signed xa7)); [exact INV | exact FRM | lia].
  Qed.

  Lemma ff_L5 : forall (f : nat) (p4 : Z) xra xt1 xt2 xs0 xs1 xa2 xa3 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 < LAST)%Z -> (LAST - p4 <= Z.of_nat f)%Z ->
    evt psegs (ff_post E) (FFS E 0x3c500 xra (Z_to_bv 64 46) xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 p4) xa5 (Z_to_bv 64 48) xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM Hp Hl Hf; [exfalso; lia|].
    pose proof INV as INV0. ff_open INV0. ff_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c82c%Z => first [ eapply (ff_938 HSPATH E OK); [exact INV | assumption | lia] | fail 100 "cut" pc ]
      | 0x3c514%Z => first [ eapply ff_620w; [exact INV | assumption] | fail 100 "cut" pc ]
      | 0x3c500%Z => first [ eapply evt_eq; [| eapply (IH (p4 + 1)%Z)]; [num_st_eq | exact INV | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_5e4 : forall (p4 dc : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 <= LAST)%Z -> (-9223372036854775808 <= dc <= LAST - p4)%Z ->
    evt psegs (ff_post E) (FFS E 0x3c4d8 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 p4) (Z_to_bv 64 dc) xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM Hp Hl Hdc. pose proof INV as INV0. ff_open INV0. ff_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c514%Z => first [ eapply ff_620w; [exact INV | assumption] | fail 100 "cut" pc ]
      | 0x3c500%Z => first [ eapply (ff_L5 (Z.to_nat (LAST - p4)) p4); [exact INV | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_5d8 : forall (p4 dc : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 <= LAST)%Z -> (-9223372036854775808 <= dc <= LAST - p4)%Z ->
    evt psegs (ff_post E) (FFS E 0x3c4cc xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 p4) (Z_to_bv 64 dc) xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM Hp Hl Hdc.
    assert (IsData xt1) by exact I. assert (IsData xa6) by exact I.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c4d8%Z => first [ eapply (ff_5e4 p4 dc); [exact INV | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_L4 : forall (f : nat) (p p4 dc : Z) xra xt1 xs0 xs1 xa2 xa3 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 <= LAST)%Z -> (-9223372036854775808 <= dc <= LAST - p4)%Z ->
    (A <= p < LAST)%Z -> (LAST - p <= Z.of_nat f)%Z ->
    evt psegs (ff_post E) (FFS E 0x3c4ac xra (Z_to_bv 64 p) xt1 (Z_to_bv 64 9) xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 p4) (Z_to_bv 64 dc) xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 10) (Z_to_bv 64 268435456) xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM Hp4 Hl Hdc Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. ff_open INV0. ff_env OK.
    assert (DT1 : IsData xt1) by exact I.
    nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c4cc%Z => first [ eapply (ff_5d8 p4 dc); [exact INV | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x3c4ac%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_54c : forall (p p4 dc : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 <= LAST)%Z -> (-9223372036854775808 <= dc <= LAST - p4)%Z -> (A <= p < LAST)%Z ->
    evt psegs (ff_post E) (FFS E 0x3c440 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 p4) (Z_to_bv 64 dc) (Z_to_bv 64 p) xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM Hp4 Hl Hdc Hp. pose proof INV as INV0. ff_open INV0. ff_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c4d8%Z => first [ eapply (ff_5e4 p4 dc); [exact INV | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x3c4ac%Z => first [ eapply evt_eq; [| eapply (ff_L4 (Z.to_nat LAST) _ p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_53c : forall (p bf p4 dc : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (0 <= dc)%Z -> (p4 + dc < bf)%Z -> (bf <= p <= LAST)%Z ->
    evt psegs (ff_post E) (FFS E 0x3c430 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 p4) (Z_to_bv 64 dc) (Z_to_bv 64 p) (Z_to_bv 64 bf)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM Hp4 Hdc Hbf Hp. pose proof INV as INV0. ff_open INV0. ff_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c7c4%Z => first [ eapply (ff_exit E OK); [exact INV | assumption] | fail 100 "cut" pc ]
      | 0x3c4d8%Z => first [ eapply evt_eq; [| eapply (ff_5e4 p4 (dc - (bf - p))%Z)]; [num_st_eq | exact INV | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x3c440%Z => first [ eapply evt_eq; [| eapply (ff_54c p p4 (dc - (bf - p))%Z)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_L3 : forall (f : nat) (p bf p4 dc : Z) xra xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (0 <= dc)%Z -> (p4 + dc < bf)%Z -> (bf <= p < LAST)%Z -> (LAST - p <= Z.of_nat f)%Z ->
    evt psegs (ff_post E) (FFS E 0x3c40c xra (Z_to_bv 64 9) (Z_to_bv 64 10) xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 p4) (Z_to_bv 64 dc) (Z_to_bv 64 p) (Z_to_bv 64 bf)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM Hp4 Hdc Hbf Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. ff_open INV0. ff_env OK.
    assert (DA3 : IsData xa3) by exact I.
    nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c430%Z => first [ eapply evt_eq; [| eapply (ff_53c _ bf p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x3c40c%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z bf p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_50c : forall (p bf p4 dc : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (0 <= dc)%Z -> (p4 + dc < bf)%Z -> (bf <= p <= LAST)%Z ->
    evt psegs (ff_post E) (FFS E 0x3c400 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 p4) (Z_to_bv 64 dc) (Z_to_bv 64 p) (Z_to_bv 64 bf)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM Hp4 Hdc Hbf Hp. pose proof INV as INV0. ff_open INV0. ff_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c430%Z => first [ eapply evt_eq; [| eapply (ff_53c _ bf p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x3c40c%Z => first [ eapply (ff_L3 (Z.to_nat LAST) p bf p4 dc); [exact INV | assumption | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_4a0 : forall (p bf p4 dc : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (0 <= dc)%Z -> (p4 + dc < bf)%Z -> (bf <= p)%Z -> (p + 4 <= LAST)%Z ->
    evt psegs (ff_post E) (FFS E 0x3c394 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 p4) (Z_to_bv 64 dc) (Z_to_bv 64 p) (Z_to_bv 64 bf)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM Hp4 Hdc Hbf Hp Hl.
    assert (DS3 : IsData xs3) by exact I. assert (DA3 : IsData xa3) by exact I.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c400%Z => first [ eapply evt_eq; [| eapply (ff_50c _ bf p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_470 : forall (p bf p4 dc : Z) xra xt1 xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (0 <= dc)%Z -> (p4 + dc < bf)%Z -> (bf <= p <= LAST)%Z ->
    evt psegs (ff_post E) (FFS E 0x3c364 xra (Z_to_bv 64 (LAST - p)) xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 p4) (Z_to_bv 64 dc) (Z_to_bv 64 p) (Z_to_bv 64 bf)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM Hp4 Hdc Hbf Hp. pose proof INV as INV0. ff_open INV0. ff_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c400%Z => first [ eapply evt_eq; [| eapply (ff_50c p bf p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x3c394%Z => first [ eapply evt_eq; [| eapply (ff_4a0 p bf p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_L2 : forall (f : nat) (p bf p4 dc : Z) xra xt1 xt2 xs0 xs1 xa2 xa3 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (0 <= dc)%Z -> (p4 + dc < bf)%Z -> (bf <= p)%Z -> (p + 8 <= LAST)%Z -> (LAST - p <= 8 * Z.of_nat f)%Z ->
    evt psegs (ff_post E) (FFS E 0x3c2a8 xra (Z_to_bv 64 (LAST - p)) xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 p4) (Z_to_bv 64 dc) (Z_to_bv 64 p) (Z_to_bv 64 bf)
                               (Z_to_bv 64 7) xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM Hp4 Hdc Hbf Hp Hl Hf; [exfalso; lia|].
    pose proof INV as INV0. ff_open INV0. ff_env OK.
    assert (DA3 : IsData xa3) by exact I. assert (DT1 : IsData xt1) by exact I. assert (DT2 : IsData xt2) by exact I.
    assert (DT3 : IsData xt3) by exact I. assert (DT4 : IsData xt4) by exact I. assert (DT5 : IsData xt5) by exact I. assert (DT6 : IsData xt6) by exact I.
    assert (DS0 : IsData xs0) by exact I. assert (DS1 : IsData xs1) by exact I.
    nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c394%Z => first [ eapply evt_eq; [| eapply (ff_4a0 p bf p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x3c364%Z => first [ eapply evt_eq; [| eapply (ff_470 (p + 8)%Z bf p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x3c2a8%Z => first [ eapply evt_eq; [| eapply (IH (p + 8)%Z bf p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End FFPN.
