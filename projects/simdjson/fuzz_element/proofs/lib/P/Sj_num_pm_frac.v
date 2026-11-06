(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_pm_defs Sj_num_pm_tf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section PMFRAC.
  Variable E : pmenv.
  Hypothesis OK : pm_ok E.
  Hypothesis HF : (p_FPT E <> 0)%Z.
  Notation X := (p_X E).
  Notation A := (p_A E).
  Notation TL := (p_TL E).
  Notation FE := (p_FPT E + p_FL E)%Z.

  Variables c0 c1 c4 c5 c6 cs10 : word.

  Notation PMF pc p xa6 xs3 xs4 xs5 xs6 xs7 xs8 xs9 mm :=
    (PMX E pc (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) (Z_to_bv 64 10) c0 c1 (Z_to_bv 64 FE) (Z_to_bv 64 769) (Z_to_bv 64 110104) (Z_to_bv 64 p) xa6
         (Z_to_bv 64 761) (Z_to_bv 64 61) xs3 xs4 xs5 xs6 xs7 xs8 xs9 cs10 (Z_to_bv 64 17) c4 c5 c6 mm).

  Definition fbot_k (p0 : Z) : Prop :=
    forall (p' len' dg' : Z) xa6 xs3 xs4 xs5 xs6 xs7 xs8 xs9 mm',
      PMINV E mm' len' dg' -> (p0 < p' <= FE)%Z -> (0 <= dg' < 769)%Z ->
      evt psegs (pm_post E) (PMF 0x51d9c p' xa6 xs3 xs4 xs5 xs6 xs7 xs8 xs9 mm').

  Lemma pm_f_push : forall (p0 p len dg : Z) xs3 xs4 xs5 xs6 xs7 xs8 xs9 mm,
    fbot_k p0 -> PMINV E mm len dg -> (len <= 61)%Z -> (p0 < p <= FE)%Z -> (0 <= dg < 769)%Z ->
    evt psegs (pm_post E) (PMF 0x51d88 p (Z_to_bv 64 len) xs3 xs4 xs5 xs6 xs7 xs8 xs9 mm).
  Proof using OK HF.
    intros until mm. intros HBOT INV Hl Hp Hd. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x51d9c%Z => first [ eapply (HBOT p); [pm_close | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_f_car : forall (f : nat) (p0 p k len dg : Z) xs5 xs6 xs7 xs8 xs9 mm,
    fbot_k p0 -> PMINV E mm len dg -> (1 <= k <= len)%Z -> (len - k <= Z.of_nat f)%Z -> (p0 < p <= FE)%Z -> (0 <= dg < 769)%Z ->
    evt psegs (pm_post E) (PMF 0x51fcc p (Z_to_bv 64 len) (Z_to_bv 64 (len - k + 1)) (Z_to_bv 64 (X + 8 * k)) xs5 xs6 xs7 xs8 xs9 mm).
  Proof using OK HF.
    intros f. induction f as [|f IH]; intros until mm; intros HBOT INV Hk Hf Hp Hd.
    - pm_open INV. pm_env OK. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x51d9c%Z => first [ eapply (HBOT p); [pm_close | lia | lia] | fail 100 "cut" pc ]
        | 0x51d88%Z => first [ eapply (pm_f_push p0 p); [exact HBOT | pm_close | lia | lia | lia] | fail 100 "cut" pc ]
        end).
    - pm_open INV. pm_env OK. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x51d9c%Z => first [ eapply (HBOT p); [pm_close | lia | lia] | fail 100 "cut" pc ]
        | 0x51d88%Z => first [ eapply (pm_f_push p0 p); [exact HBOT | pm_close | lia | lia | lia] | fail 100 "cut" pc ]
        | 0x51fcc%Z => first [ eapply evt_eq; [| eapply (IH p0 p (k + 1)%Z len dg); [exact HBOT | pm_close | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma pm_f_mul : forall (f : nat) (p0 p i len dg : Z) xs3 xs5 xs6 xs8 xs9 mm,
    fbot_k p0 -> PMINV E mm len dg -> (0 <= i < len)%Z -> (len - i <= Z.of_nat f)%Z -> (p0 < p <= FE)%Z -> (0 <= dg < 769)%Z ->
    evt psegs (pm_post E) (PMF 0x51f78 p (Z_to_bv 64 len) xs3 (Z_to_bv 64 (X + 8 * len)) xs5 xs6 (Z_to_bv 64 (X + 8 * i)) xs8 xs9 mm).
  Proof using OK HF.
    intros f. induction f as [|f IH]; intros until mm; intros HBOT INV Hi Hf Hp Hd; [exfalso; lia|].
    pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x51d9c%Z => first [ eapply (HBOT p); [pm_close | lia | lia] | fail 100 "cut" pc ]
      | 0x51f78%Z => first [ eapply evt_eq; [| eapply (IH p0 p (i + 1)%Z len dg); [exact HBOT | pm_close | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0x51fcc%Z => first [ eapply evt_eq; [| eapply (pm_f_car 62 p0 p 1%Z _ dg); [exact HBOT | pm_close | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Definition f0a4_k (p0 : Z) : Prop :=
    forall (p' dg' cnt' len : Z) xa6 xs3 xs6 xs7 xs8 xs9 mm',
      PMINV E mm' len dg' -> (p0 <= p' <= FE)%Z -> (0 <= cnt' <= 19)%Z -> (0 <= dg' <= 769)%Z -> (dg' = 769 \/ p0 < p')%Z ->
      evt psegs (pm_post E) (PMF 0x51f50 p' xa6 xs3 (Z_to_bv 64 dg') (Z_to_bv 64 cnt') xs6 xs7 xs8 xs9 mm').

  Lemma pm_f_0a4 : forall p0, (p_FPT E <= p0)%Z -> fbot_k p0 -> f0a4_k p0.
  Proof using OK HF.
    intros p0 Hp0 HBOT. unfold f0a4_k. intros until mm'. intros INV Hp Hc Hd Hprog.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x52134%Z => first [ eapply (pm_trunc_frac E OK cnt' p' FE); [exact INV0 | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x51d9c%Z => first [ eapply (HBOT p'); [pm_close | lia | lia] | fail 100 "cut" pc ]
      | 0x51d88%Z => first [ eapply evt_eq; [| eapply (pm_f_push p0 p' len dg'); [exact HBOT | exact INV0 | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0x51f78%Z => first [ eapply evt_eq; [| eapply (pm_f_mul (Z.to_nat len) p0 p' 0%Z len dg'); [exact HBOT | exact INV0 | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_f_1d : forall (f : nat) (p0 p cnt len dg : Z) xa6 xs3 xs6 xs7 xs8 xs9 mm,
    f0a4_k p0 -> PMINV E mm len dg -> (p_FPT E <= p0 <= p)%Z -> (p < FE)%Z -> (0 <= cnt <= 18)%Z -> (0 <= dg < 769)%Z -> (FE - p <= Z.of_nat f)%Z ->
    evt psegs (pm_post E) (PMF 0x51f20 p xa6 xs3 (Z_to_bv 64 dg) (Z_to_bv 64 cnt) xs6 xs7 xs8 xs9 mm).
  Proof using OK HF.
    intros f. induction f as [|f IH]; intros until mm; intros H0A4 INV Hp Hpe Hc Hd Hf; [exfalso; lia|].
    pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x51f50%Z => first [ eapply evt_eq; [| eapply (H0A4 (p + 1)%Z _ (cnt + 1)%Z); [pm_close | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0x51f20%Z => first [ eapply evt_eq; [| eapply (IH p0 (p + 1)%Z (cnt + 1)%Z); [exact H0A4 | pm_close | lia | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Definition pm_f_head_stmt (f : nat) : Prop :=
    forall (p len dg : Z) xa6 xs3 xs4 xs5 xs6 xs7 xs8 xs9 mm,
      PMINV E mm len dg -> (p_FPT E <= p < FE)%Z -> (0 <= dg < 769)%Z -> (FE - p <= Z.of_nat f)%Z ->
      evt psegs (pm_post E) (PMF 0x51da0 p xa6 xs3 xs4 xs5 xs6 xs7 xs8 xs9 mm).

  Lemma pm_f_bot : forall f p0, pm_f_head_stmt f -> (p_FPT E <= p0)%Z -> (FE - p0 <= Z.of_nat (S f))%Z -> fbot_k p0.
  Proof using OK HF.
    intros f p0 HH Hp0 Hf. unfold fbot_k. intros until mm'. intros INV Hp Hd.
    pose proof INV as INV0. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x525fc%Z => first [ eapply (pm_exit E OK); exact INV0 | fail 100 "cut" pc ]
      | 0x51da0%Z => first [ eapply (HH p'); [exact INV0 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Theorem pm_f_head : forall f, pm_f_head_stmt f.
  Proof using OK HF.
    intros f. induction f as [|f IH]; unfold pm_f_head_stmt; intros until mm; intros INV Hp Hd Hf; [exfalso; lia|].
    assert (HBOT : fbot_k p) by (eapply (pm_f_bot f); [exact IH | lia | lia]).
    assert (H0A4 : f0a4_k p) by (eapply pm_f_0a4; [lia | exact HBOT]).
    pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x51f50%Z => first [ eapply evt_eq; [| eapply (H0A4 _ _ _)]; [num_st_eq | pm_close | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x51f20%Z => first [ eapply evt_eq; [| eapply (pm_f_1d (Z.to_nat (FE - p)) p _ _)]; [num_st_eq | exact H0A4 | pm_close | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMFRAC.
