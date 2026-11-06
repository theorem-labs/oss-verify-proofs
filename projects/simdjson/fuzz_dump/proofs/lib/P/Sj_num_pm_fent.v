(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_pm_defs Sj_num_pm_frac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section PMFENT.
  Variable E : pmenv.
  Hypothesis OK : pm_ok E.
  Notation X := (p_X E).
  Notation A := (p_A E).
  Notation TL := (p_TL E).
  Notation FPT := (p_FPT E).
  Notation FE := (p_FPT E + p_FL E)%Z.

  Section NONNULL.
  Hypothesis HF : (FPT <> 0)%Z.

  Lemma pm_e80 : forall (q : Z) xt0 xt1 xt2 xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (FPT <= q <= FE)%Z -> (0 <= dg < 769)%Z ->
    evt psegs (pm_post E) (PMX E 0x4e884 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FE) (Z_to_bv 64 769) (Z_to_bv 64 106880) (Z_to_bv 64 q) xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK HF.
    intros until dg. intros INV Hq Hd.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x4f154%Z => first [ eapply (pm_exit E OK); exact INV0 | fail 100 "cut" pc ]
      | 0x4e8f8%Z => first [ eapply evt_eq; [| eapply (pm_f_head E OK HF _ _ _ _ _ _ (Z.to_nat (FE - q)) q len dg)]; [num_st_eq | exact INV0 | lia | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_szfb : forall (f : nat) (q : Z) xt0 xt1 xt2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (FPT <= q < FE)%Z -> (0 <= dg < 769)%Z -> (FE - q <= Z.of_nat f)%Z ->
    evt psegs (pm_post E) (PMX E 0x4ed3c xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FE) (Z_to_bv 64 769) (Z_to_bv 64 106880) (Z_to_bv 64 q) (Z_to_bv 64 FE) (Z_to_bv 64 48)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK HF.
    intros f. induction f as [|f IH]; intros until dg; intros INV Hq Hd Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x4e884%Z => first [ eapply evt_eq; [| eapply (pm_e80 _)]; [num_st_eq | exact INV0 | lia | lia] | fail 100 "cut" pc ]
      | 0x4ed3c%Z => first [ eapply evt_eq; [| eapply (IH (q + 1)%Z)]; [num_st_eq | exact INV0 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_328 : forall (q : Z) xt0 xt1 xt2 xs0 xs1 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (FPT <= q <= FE)%Z -> (0 <= dg < 769)%Z ->
    evt psegs (pm_post E) (PMX E 0x4ed2c xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FE) (Z_to_bv 64 769) (Z_to_bv 64 106880) (Z_to_bv 64 q) xa6 (Z_to_bv 64 q)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK HF.
    intros until dg. intros INV Hq Hd.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x4f154%Z => first [ eapply (pm_exit E OK); exact INV0 | fail 100 "cut" pc ]
      | 0x4ed3c%Z => first [ eapply evt_eq; [| eapply (pm_szfb (Z.to_nat (FE - q)) q)]; [num_st_eq | exact INV0 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_szf8 : forall (f : nat) (q : Z) xt2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (FPT <= q)%Z -> (8 <= FE - q)%Z -> (0 <= dg < 769)%Z -> (FE - q <= 8 * Z.of_nat f)%Z ->
    evt psegs (pm_post E) (PMX E 0x4ec1c (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 7) xt2 xs0 xs1 (Z_to_bv 64 FE) (Z_to_bv 64 769) (Z_to_bv 64 106880)
                               (Z_to_bv 64 q) (Z_to_bv 64 (FE - q)) (Z_to_bv 64 q)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK HF.
    intros f. induction f as [|f IH]; intros until dg; intros INV Hq H8 Hd Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x4ed2c%Z => first [ eapply evt_eq; [| eapply (pm_328 _)]; [num_st_eq | exact INV0 | lia | lia] | fail 100 "cut" pc ]
      | 0x4ec1c%Z => first [ eapply evt_eq; [| eapply (IH (q + 8)%Z)]; [num_st_eq | exact INV0 | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
  End NONNULL.

  Lemma pm_int_done : forall xt0 xt1 xt2 xs0 xs1 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (0 <= dg < 769)%Z ->
    evt psegs (pm_post E) (PMX E 0x4e86c xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 106880) xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV Hd.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x4f154%Z => first [ eapply (pm_exit E OK); exact INV0 | fail 100 "cut" pc ]
      | 0x4e884%Z => first [ eapply evt_eq; [| eapply (pm_e80 ltac:(lia) FPT)]; [num_st_eq | exact INV0 | lia | lia] | fail 100 "cut" pc ]
      | 0x4ed2c%Z => first [ eapply evt_eq; [| eapply (pm_328 ltac:(lia) FPT)]; [num_st_eq | exact INV0 | lia | lia] | fail 100 "cut" pc ]
      | 0x4ec1c%Z => first [ eapply evt_eq; [| eapply (pm_szf8 ltac:(lia) (Z.to_nat (p_FL E)) FPT)]; [num_st_eq | exact INV0 | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMFENT.
