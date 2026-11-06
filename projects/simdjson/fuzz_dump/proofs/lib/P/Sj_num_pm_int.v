(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_pm_defs Sj_num_pm_ti Sj_num_pm_fent.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section PMINT.
  Variable E : pmenv.
  Hypothesis OK : pm_ok E.
  Notation X := (p_X E).
  Notation A := (p_A E).
  Notation TL := (p_TL E).
  Notation IP := (p_IP E).
  Notation PE := (p_IP E + p_IL E)%Z.

  Variables c0 c1 c2 c5 c6 : word.

  Notation PMI pc p xa7 xs4 xs5 xs6 xs7 xs8 xs9 xs10 mm :=
    (PMX E pc (Z_to_bv 64 761) (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) c0 c1 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 106880) (Z_to_bv 64 PE)
         (Z_to_bv 64 p) xa7 c2 (Z_to_bv 64 61) xs4 xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 10) (Z_to_bv 64 17) c5 c6 mm).

  Definition ibot_k (p0 : Z) : Prop :=
    forall (p' len' dg' : Z) xa7 xs4 xs5 xs6 xs7 xs8 xs9 xs10 mm',
      PMINV E mm' len' dg' -> (p0 < p' <= PE)%Z -> (0 <= dg' < 769)%Z ->
      evt psegs (pm_post E) (PMI 0x4e60c p' xa7 xs4 xs5 xs6 xs7 xs8 xs9 xs10 mm').

  Lemma pm_i_push : forall (p0 p len dg : Z) xs4 xs5 xs6 xs7 xs8 xs9 xs10 mm,
    ibot_k p0 -> PMINV E mm len dg -> (len <= 61)%Z -> (p0 < p <= PE)%Z -> (0 <= dg < 769)%Z ->
    evt psegs (pm_post E) (PMI 0x4e5f8 p (Z_to_bv 64 len) xs4 xs5 xs6 xs7 xs8 xs9 xs10 mm).
  Proof using OK.
    intros until mm. intros HBOT INV Hl Hp Hd. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x4e60c%Z => first [ eapply (HBOT p); [pm_close | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_i_car : forall (f : nat) (p0 p k len dg : Z) xs6 xs7 xs8 xs9 xs10 mm,
    ibot_k p0 -> PMINV E mm len dg -> (1 <= k <= len)%Z -> (len - k <= Z.of_nat f)%Z -> (p0 < p <= PE)%Z -> (0 <= dg < 769)%Z ->
    evt psegs (pm_post E) (PMI 0x4e83c p (Z_to_bv 64 len) (Z_to_bv 64 (len - k + 1)) (Z_to_bv 64 (X + 8 * k)) xs6 xs7 xs8 xs9 xs10 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until mm; intros HBOT INV Hk Hf Hp Hd.
    - pm_open INV. pm_env OK. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x4e60c%Z => first [ eapply (HBOT p); [pm_close | lia | lia] | fail 100 "cut" pc ]
        | 0x4e5f8%Z => first [ eapply (pm_i_push p0 p); [exact HBOT | pm_close | lia | lia | lia] | fail 100 "cut" pc ]
        end).
    - pm_open INV. pm_env OK. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x4e60c%Z => first [ eapply (HBOT p); [pm_close | lia | lia] | fail 100 "cut" pc ]
        | 0x4e5f8%Z => first [ eapply (pm_i_push p0 p); [exact HBOT | pm_close | lia | lia | lia] | fail 100 "cut" pc ]
        | 0x4e83c%Z => first [ eapply evt_eq; [| eapply (IH p0 p (k + 1)%Z len dg)]; [num_st_eq | exact HBOT | pm_close | lia | lia | lia | lia] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma pm_i_mul : forall (f : nat) (p0 p i len dg : Z) xs4 xs6 xs7 xs9 xs10 mm,
    ibot_k p0 -> PMINV E mm len dg -> (0 <= i < len)%Z -> (len - i <= Z.of_nat f)%Z -> (p0 < p <= PE)%Z -> (0 <= dg < 769)%Z ->
    evt psegs (pm_post E) (PMI 0x4e7e8 p (Z_to_bv 64 len) xs4 (Z_to_bv 64 (X + 8 * len)) xs6 xs7 (Z_to_bv 64 (X + 8 * i)) xs9 xs10 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until mm; intros HBOT INV Hi Hf Hp Hd; [exfalso; lia|].
    pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x4e60c%Z => first [ eapply (HBOT p); [pm_close | lia | lia] | fail 100 "cut" pc ]
      | 0x4e7e8%Z => first [ eapply evt_eq; [| eapply (IH p0 p (i + 1)%Z len dg)]; [num_st_eq | exact HBOT | pm_close | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x4e83c%Z => first [ eapply evt_eq; [| eapply (pm_i_car 62 p0 p 1%Z _ dg)]; [num_st_eq | exact HBOT | pm_close | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Definition idbc_k (p0 : Z) : Prop :=
    forall (p' dg' cnt' len : Z) xa7 xs4 xs7 xs8 xs9 xs10 mm',
      PMINV E mm' len dg' -> (p0 <= p' <= PE)%Z -> (0 <= cnt' <= 19)%Z -> (0 <= dg' <= 769)%Z -> (dg' = 769 \/ p0 < p')%Z ->
      evt psegs (pm_post E) (PMI 0x4e7c0 p' xa7 xs4 (Z_to_bv 64 dg') (Z_to_bv 64 cnt') xs7 xs8 xs9 xs10 mm').

  Lemma pm_i_dbc : forall p0, (IP <= p0)%Z -> ibot_k p0 -> idbc_k p0.
  Proof using OK.
    intros p0 Hp0 HBOT. unfold idbc_k. intros until mm'. intros INV Hp Hc Hd Hprog.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x4eb60%Z => first [ eapply (pm_trunc_int E OK cnt' p' PE); [exact INV0 | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x4e60c%Z => first [ eapply (HBOT p'); [pm_close | lia | lia] | fail 100 "cut" pc ]
      | 0x4e5f8%Z => first [ eapply evt_eq; [| eapply (pm_i_push p0 p' len dg')]; [num_st_eq | exact HBOT | exact INV0 | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x4e7e8%Z => first [ eapply evt_eq; [| eapply (pm_i_mul (Z.to_nat len) p0 p' 0%Z len dg')]; [num_st_eq | exact HBOT | exact INV0 | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_i_1d : forall (f : nat) (p0 p cnt len dg : Z) xa7 xs4 xs7 xs8 xs9 xs10 mm,
    idbc_k p0 -> PMINV E mm len dg -> (IP <= p0 <= p)%Z -> (p < PE)%Z -> (0 <= cnt <= 18)%Z -> (0 <= dg < 769)%Z -> (PE - p <= Z.of_nat f)%Z ->
    evt psegs (pm_post E) (PMI 0x4e790 p xa7 xs4 (Z_to_bv 64 dg) (Z_to_bv 64 cnt) xs7 xs8 xs9 xs10 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until mm; intros HDBC INV Hp Hpe Hc Hd Hf; [exfalso; lia|].
    pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x4e7c0%Z => first [ eapply evt_eq; [| eapply (HDBC (p + 1)%Z _ (cnt + 1)%Z)]; [num_st_eq | pm_close | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x4e790%Z => first [ eapply evt_eq; [| eapply (IH p0 (p + 1)%Z (cnt + 1)%Z)]; [num_st_eq | exact HDBC | pm_close | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Definition pm_i_head_stmt (f : nat) : Prop :=
    forall (p len dg : Z) xa7 xs4 xs5 xs6 xs7 xs8 xs9 xs10 mm,
      PMINV E mm len dg -> (IP <= p < PE)%Z -> (0 <= dg < 769)%Z -> (PE - p <= Z.of_nat f)%Z ->
      evt psegs (pm_post E) (PMI 0x4e610 p xa7 xs4 xs5 xs6 xs7 xs8 xs9 xs10 mm).

  Lemma pm_i_bot : forall f p0, pm_i_head_stmt f -> (IP <= p0)%Z -> (PE - p0 <= Z.of_nat (S f))%Z -> ibot_k p0.
  Proof using OK.
    intros f p0 HH Hp0 Hf. unfold ibot_k. intros until mm'. intros INV Hp Hd.
    pose proof INV as INV0. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x4e86c%Z => first [ eapply (pm_int_done E OK); [exact INV0 | lia] | fail 100 "cut" pc ]
      | 0x4e610%Z => first [ eapply (HH p'); [exact INV0 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Theorem pm_i_head : forall f, pm_i_head_stmt f.
  Proof using OK.
    intros f. induction f as [|f IH]; unfold pm_i_head_stmt; intros until mm; intros INV Hp Hd Hf; [exfalso; lia|].
    assert (HBOT : ibot_k p) by (eapply (pm_i_bot f); [exact IH | lia | lia]).
    assert (HDBC : idbc_k p) by (eapply pm_i_dbc; [lia | exact HBOT]).
    pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x4e7c0%Z => first [ eapply evt_eq; [| eapply (HDBC _ _ _)]; [num_st_eq | pm_close | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x4e790%Z => first [ eapply evt_eq; [| eapply (pm_i_1d (Z.to_nat (PE - p)) p _ _)]; [num_st_eq | exact HDBC | pm_close | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMINT.
