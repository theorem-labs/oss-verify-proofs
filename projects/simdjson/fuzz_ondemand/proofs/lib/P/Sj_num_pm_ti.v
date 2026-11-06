(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_pm_defs Sj_num_pm_round.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section PMTI.
  Variable E : pmenv.
  Hypothesis OK : pm_ok E.
  Notation X := (p_X E).
  Notation A := (p_A E).
  Notation TL := (p_TL E).

  Lemma pm_if8 : forall (Q : machine_state -> Prop) (f : nat) (q r : Z)
      xt2 xs0 xs1 xa2 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm,
    bytes_at psegs mm A (p_txt E) -> (A <= q)%Z -> (q + r <= A + TL)%Z -> (8 <= r)%Z -> (r <= 8 * Z.of_nat f)%Z ->
    (forall xt1' xt2' xs0' xa1' xt3' xt4' xt5' xt6',
       evt psegs Q (PMX E 0x3c1f0 (Z_to_bv 64 7) xt1' xt2' xs0' xs1 xa1' xa2 xa4 xa5 (Z_to_bv 64 3472328296227680304) xa7
                        xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3' xt4' xt5' xt6' mm)) ->
    (forall (q' r' : Z) xt2' xs0' xt3' xt4' xt5' xt6', (q <= q')%Z -> (q' + r' = q + r)%Z -> (0 <= r' < 8)%Z ->
       evt psegs Q (PMX E 0x3c1d0 (Z_to_bv 64 7) (Z_to_bv 64 r') xt2' xs0' xs1 (Z_to_bv 64 q') xa2 xa4 xa5 (Z_to_bv 64 3472328296227680304) xa7
                        xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3' xt4' xt5' xt6' mm)) ->
    evt psegs Q (PMX E 0x3c168 (Z_to_bv 64 7) (Z_to_bv 64 r) xt2 xs0 xs1 (Z_to_bv 64 q) xa2 xa4 xa5 (Z_to_bv 64 3472328296227680304) xa7
                     xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros Q f. induction f as [|f IH]; intros until mm; intros TXT Hq Hr H8 Hf HR HD; [exfalso; lia|].
    pm_env OK.
    nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c1f0%Z => first [ apply HR | fail 100 "cut" pc ]
      | 0x3c1d0%Z => first [ eapply evt_eq; [| eapply (HD (q + 8)%Z (r - 8)%Z); lia]; num_st_eq | fail 100 "cut" pc ]
      | 0x3c168%Z => first [ eapply evt_eq; [| eapply (IH (q + 8)%Z (r - 8)%Z); [exact TXT | lia | lia | lia | lia | exact HR |]]; [num_st_eq|];
                             intros q' r' xt2' xs0' xt3' xt4' xt5' xt6' H1 H2 H3; eapply (HD q' r'); lia | fail 100 "cut" pc ]
      end).
  Qed.

  Notation FPT := (p_FPT E).
  Notation FL := (p_FL E).

  Lemma pm_64c : forall xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg ->
    evt psegs (pm_post E) (PMX E 0x3c1ec xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa4 xa5 xa6 (Z_to_bv 64 len) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c2f0%Z => first [ eapply (pm_exit E OK); exact INV | fail 100 "cut" pc ]
      | 0x3c1f0%Z => first [ eapply (pm_roundA E OK); exact INV | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ifb : forall (f : nat) (q fe : Z) xt0 xt1 xt2 xs0 xs1 xa2 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (A <= q < fe)%Z -> (fe <= A + TL)%Z -> (fe - q <= Z.of_nat f)%Z ->
    evt psegs (pm_post E) (PMX E 0x3c1dc xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 q) xa2 (Z_to_bv 64 fe) (Z_to_bv 64 48) xa6 (Z_to_bv 64 len)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until dg; intros INV Hq Hfe Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV. pm_env OK.
    nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c1f0%Z => first [ eapply (pm_roundA E OK); exact INV0 | fail 100 "cut" pc ]
      | 0x3c1ec%Z => first [ eapply pm_64c; exact INV0 | fail 100 "cut" pc ]
      | 0x3c1dc%Z => first [ eapply evt_eq; [| eapply (IH (q + 1)%Z fe); [exact INV0 | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_630 : forall (q : Z) xt0 xt1 xt2 xs0 xs1 xa2 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (FPT <> 0)%Z -> (FPT <= q <= FPT + FL)%Z ->
    evt psegs (pm_post E) (PMX E 0x3c1d0 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 q) xa2 (Z_to_bv 64 FPT) (Z_to_bv 64 FL) xa6 (Z_to_bv 64 len)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV HF Hq.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c1ec%Z => first [ eapply pm_64c; exact INV0 | fail 100 "cut" pc ]
      | 0x3c1dc%Z => first [ eapply evt_eq; [| eapply (pm_ifb (Z.to_nat (FPT + FL - q)) q (FPT + FL)%Z); [exact INV0 | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_5ac : forall xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (FPT <> 0)%Z -> (8 <= FL)%Z ->
    evt psegs (pm_post E) (PMX E 0x3c14c xt0 xt1 xt2 xs0 xs1 xa1 xa2 (Z_to_bv 64 FPT) (Z_to_bv 64 FL) xa6 (Z_to_bv 64 len)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV HF H8.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c168%Z => idtac
      end).
    eapply evt_eq; [| eapply (pm_if8 (pm_post E) (Z.to_nat FL) FPT FL); [exact TXT | lia | lia | lia | lia | |]]; [num_st_eq | |].
    - intros. eapply (pm_roundA E OK); exact INV0.
    - intros q' r' xt2' xs0' xt3' xt4' xt5' xt6' H1 H2 H3.
      eapply pm_630; [exact INV0 | exact HF | lia].
  Qed.

  Ltac ti_disp INV0 HF :=
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c2f0%Z => first [ eapply (pm_exit E OK); exact INV0 | fail 100 "cut" pc ]
      | 0x3c1ec%Z => first [ eapply pm_64c; exact INV0 | fail 100 "cut" pc ]
      | 0x3c1d0%Z => first [ eapply (pm_630 FPT); [exact INV0 | lia | lia] | fail 100 "cut" pc ]
      | 0x3c14c%Z => first [ eapply pm_5ac; [exact INV0 | lia | lia] | fail 100 "cut" pc ]
      end).

  Lemma pm_418 : forall xt0 xt1 xt2 xs0 xs1 xa2 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg ->
    evt psegs (pm_post E) (PMX E 0x3bfb8 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) xa2 xa4 xa5 xa6 (Z_to_bv 64 len)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV. pose proof INV as INV0. pm_open INV. pm_env OK. ti_disp INV0 I.
  Qed.

  Lemma pm_424 : forall xt0 xt1 xt2 xs0 xs1 xa2 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg ->
    evt psegs (pm_post E) (PMX E 0x3bfc4 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) xa2 xa4 xa5 xa6 (Z_to_bv 64 len)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV. pose proof INV as INV0. pm_open INV. pm_env OK. ti_disp INV0 I.
  Qed.

  Lemma pm_590 : forall xt0 xt1 xt2 xs0 xs1 xa2 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg ->
    evt psegs (pm_post E) (PMX E 0x3c130 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) xa2 xa4 xa5 xa6 (Z_to_bv 64 len)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV. pose proof INV as INV0. pm_open INV. pm_env OK. ti_disp INV0 I.
  Qed.

  Lemma pm_itb : forall (f : nat) (q pe : Z) xt0 xt1 xt2 xs0 xs1 xa2 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (A < q <= pe)%Z -> (pe <= A + TL)%Z -> (pe - q <= Z.of_nat f)%Z ->
    evt psegs (pm_post E) (PMX E 0x3bf9c xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) xa2 (Z_to_bv 64 48) (Z_to_bv 64 pe) (Z_to_bv 64 q) (Z_to_bv 64 len)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until dg; intros INV Hq Hpe Hf.
    - pose proof INV as INV0. pm_open INV. pm_env OK. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x3bfb8%Z => first [ eapply pm_418; exact INV0 | fail 100 "cut" pc ]
        end).
    - pose proof INV as INV0. pm_open INV. pm_env OK. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x3bfb8%Z => first [ eapply pm_418; exact INV0 | fail 100 "cut" pc ]
        | 0x3bf9c%Z => first [ eapply evt_eq; [| eapply (IH (q + 1)%Z pe); [exact INV0 | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma pm_3f0 : forall (q pe : Z) xt0 xt1 xt2 xs0 xs1 xa2 xa4 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (A <= q <= pe)%Z -> (pe <= A + TL)%Z ->
    evt psegs (pm_post E) (PMX E 0x3bf90 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) xa2 xa4 (Z_to_bv 64 pe) (Z_to_bv 64 q) (Z_to_bv 64 len)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV Hq Hpe.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3bfc4%Z => first [ eapply pm_424; exact INV0 | fail 100 "cut" pc ]
      | 0x3bf9c%Z => first [ eapply evt_eq; [| eapply (pm_itb (Z.to_nat (pe - q)) (q + 1)%Z pe); [exact INV0 | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_it8 : forall (f : nat) (q pe : Z) xt1 xt2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (A <= q)%Z -> (pe <= A + TL)%Z -> (8 <= pe - q)%Z -> (pe - q <= 8 * Z.of_nat f)%Z ->
    evt psegs (pm_post E) (PMX E 0x3bf28 (Z_to_bv 64 7) xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 (pe - q)) (Z_to_bv 64 3472328296227680304)
                               (Z_to_bv 64 pe) (Z_to_bv 64 q) (Z_to_bv 64 len)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until dg; intros INV Hq Hpe H8 Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c130%Z => first [ eapply pm_590; exact INV0 | fail 100 "cut" pc ]
      | 0x3bf90%Z => first [ eapply (pm_3f0 (q + 8)%Z pe); [exact INV0 | lia | lia] | fail 100 "cut" pc ]
      | 0x3bf28%Z => first [ eapply evt_eq; [| eapply (IH (q + 8)%Z pe); [exact INV0 | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_368 : forall (q pe : Z) xt0 xt1 xt2 xs0 xs1 xa2 xa4 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (A <= q <= pe)%Z -> (pe <= A + TL)%Z ->
    evt psegs (pm_post E) (PMX E 0x3bf08 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) xa2 xa4 (Z_to_bv 64 pe) (Z_to_bv 64 q) (Z_to_bv 64 len)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV Hq Hpe.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3bf90%Z => first [ eapply (pm_3f0 q pe); [exact INV0 | lia | lia] | fail 100 "cut" pc ]
      | 0x3bf28%Z => first [ eapply evt_eq; [| eapply (pm_it8 (Z.to_nat (pe - q)) q pe); [exact INV0 | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ct : forall (f : nat) (p q pe : Z) xt0 xt1 xt2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (1 <= p <= len)%Z -> (len - p <= Z.of_nat f)%Z -> (A <= q <= pe)%Z -> (pe <= A + TL)%Z ->
    evt psegs (pm_post E) (PMX E 0x3bd74 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 (len - p + 1)) (Z_to_bv 64 (X + 8 * p))
                               (Z_to_bv 64 pe) (Z_to_bv 64 q) (Z_to_bv 64 len)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until dg; intros INV Hp Hf Hq Hpe.
    - pm_open INV. pm_env OK. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x3bf08%Z => first [ eapply (pm_368 q pe); [pm_close | lia | lia] | fail 100 "cut" pc ]
        end).
    - pm_open INV. pm_env OK. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x3bf08%Z => first [ eapply (pm_368 q pe); [pm_close | lia | lia] | fail 100 "cut" pc ]
        | 0x3bd74%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z q pe); [pm_close | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma pm_mt : forall (f : nat) (i q pe : Z) xt0 xt2 xs0 xs1 xa4 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (0 <= i < len)%Z -> (len - i <= Z.of_nat f)%Z -> (A <= q <= pe)%Z -> (pe <= A + TL)%Z ->
    evt psegs (pm_post E) (PMX E 0x3bd1c xt0 (Z_to_bv 64 (X + 8 * i)) xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 (X + 8 * len)) xa4
                               (Z_to_bv 64 pe) (Z_to_bv 64 q) (Z_to_bv 64 len)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until dg; intros INV Hi Hf Hq Hpe; [exfalso; lia|].
    pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3bf08%Z => first [ eapply (pm_368 q pe); [pm_close | lia | lia] | fail 100 "cut" pc ]
      | 0x3bd1c%Z => first [ eapply evt_eq; [| eapply (IH (i + 1)%Z q pe); [pm_close | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0x3bd74%Z => first [ num_cur_mem ltac:(fun m1 => lazymatch goal with XN1 : rw_cells _ m1 (X + 496) [C2 (Z_to_bv 64 ?l)] |- _ =>
                               eapply evt_eq; [| eapply (pm_ct (Z.to_nat l) 1 q pe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 l dg); [pm_close | lia | lia | lia | lia]]; num_st_eq end)
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_trunc_int : forall (cnt q pe : Z) xt0 xt1 xt2 xs0 xs1 xa2 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (0 <= cnt <= 19)%Z -> (A <= q <= pe)%Z -> (pe <= A + TL)%Z ->
    evt psegs (pm_post E) (PMX E 0x3bcfc xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) xa2 (Z_to_bv 64 106416)
                               (Z_to_bv 64 pe) (Z_to_bv 64 q) (Z_to_bv 64 len)
                               xs2 xs3 xs4 xs5 (Z_to_bv 64 cnt) xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV Hc Hq Hpe.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3bf08%Z => first [ eapply (pm_368 q pe); [pm_close | lia | lia] | fail 100 "cut" pc ]
      | 0x3bd1c%Z => first [ eapply evt_eq; [| eapply (pm_mt (Z.to_nat len) 0 q pe); [exact INV0 | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End PMTI.
