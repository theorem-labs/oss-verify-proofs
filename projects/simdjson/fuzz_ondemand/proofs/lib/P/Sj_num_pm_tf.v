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

Section PMTF.
  Variable E : pmenv.
  Hypothesis OK : pm_ok E.
  Notation X := (p_X E).
  Notation A := (p_A E).
  Notation TL := (p_TL E).

  Lemma pm_igb : forall (f : nat) (q fe : Z) xt0 xt1 xt2 xs0 xs1 xa4 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (A <= q < fe)%Z -> (fe <= A + TL)%Z -> (fe - q <= Z.of_nat f)%Z ->
    evt psegs (pm_post E) (PMX E 0x3c08c xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 fe) (Z_to_bv 64 48) xa4 (Z_to_bv 64 q) (Z_to_bv 64 len) xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until dg; intros INV Hq Hfe Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c0a0%Z => first [ eapply (pm_roundB E OK); exact INV0 | fail 100 "cut" pc ]
      | 0x3c2f0%Z => first [ eapply (pm_exit E OK); exact INV0 | fail 100 "cut" pc ]
      | 0x3c08c%Z => first [ eapply evt_eq; [| eapply (IH (q + 1)%Z fe); [exact INV0 | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_4e4 : forall (q fe : Z) xt0 xt1 xt2 xs0 xs1 xa2 xa4 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (A <= q <= fe)%Z -> (fe <= A + TL)%Z ->
    evt psegs (pm_post E) (PMX E 0x3c084 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 fe) xa2 xa4 (Z_to_bv 64 q) (Z_to_bv 64 len) xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV Hq Hfe.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c2f0%Z => first [ eapply (pm_exit E OK); exact INV0 | fail 100 "cut" pc ]
      | 0x3c08c%Z => first [ eapply evt_eq; [| eapply (pm_igb (Z.to_nat (fe - q)) q fe); [exact INV0 | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ig8 : forall (f : nat) (q fe : Z) xt0 xt1 xt2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (A <= q)%Z -> (fe <= A + TL)%Z -> (8 <= fe - q)%Z -> (fe - q <= 8 * Z.of_nat f)%Z ->
    evt psegs (pm_post E) (PMX E 0x3c01c xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 fe) (Z_to_bv 64 (fe - q)) (Z_to_bv 64 3472328296227680304)
                               (Z_to_bv 64 q) (Z_to_bv 64 len) (Z_to_bv 64 7)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until dg; intros INV Hq Hfe H8 Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c0a0%Z => first [ eapply (pm_roundB E OK); exact INV0 | fail 100 "cut" pc ]
      | 0x3c084%Z => first [ eapply (pm_4e4 (q + 8)%Z fe); [exact INV0 | lia | lia] | fail 100 "cut" pc ]
      | 0x3c01c%Z => first [ eapply evt_eq; [| eapply (IH (q + 8)%Z fe); [exact INV0 | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_45c : forall (q fe : Z) xt0 xt1 xt2 xs0 xs1 xa2 xa4 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (A <= q <= fe)%Z -> (fe <= A + TL)%Z ->
    evt psegs (pm_post E) (PMX E 0x3bffc xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 fe) xa2 xa4 (Z_to_bv 64 q) (Z_to_bv 64 len) xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV Hq Hfe.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c084%Z => first [ eapply (pm_4e4 q fe); [exact INV0 | lia | lia] | fail 100 "cut" pc ]
      | 0x3c01c%Z => first [ eapply evt_eq; [| eapply (pm_ig8 (Z.to_nat (fe - q)) q fe); [exact INV0 | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_cf : forall (f : nat) (p q fe : Z) xt0 xt1 xt2 xs0 xs1 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (1 <= p <= len)%Z -> (len - p <= Z.of_nat f)%Z -> (A <= q <= fe)%Z -> (fe <= A + TL)%Z ->
    evt psegs (pm_post E) (PMX E 0x3bea0 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 fe) (Z_to_bv 64 (len - p + 1)) (Z_to_bv 64 (X + 8 * p))
                               (Z_to_bv 64 q) (Z_to_bv 64 len) xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until dg; intros INV Hp Hf Hq Hfe.
    - pm_open INV. pm_env OK. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x3bffc%Z => first [ eapply (pm_45c q fe); [pm_close | lia | lia] | fail 100 "cut" pc ]
        end).
    - pm_open INV. pm_env OK. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x3bffc%Z => first [ eapply (pm_45c q fe); [pm_close | lia | lia] | fail 100 "cut" pc ]
        | 0x3bea0%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z q fe); [pm_close | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma pm_mf : forall (f : nat) (i q fe : Z) xt1 xt2 xs0 xs1 xa4 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (0 <= i < len)%Z -> (len - i <= Z.of_nat f)%Z -> (A <= q <= fe)%Z -> (fe <= A + TL)%Z ->
    evt psegs (pm_post E) (PMX E 0x3be48 (Z_to_bv 64 (X + 8 * i)) xt1 xt2 xs0 xs1 (Z_to_bv 64 fe) (Z_to_bv 64 (X + 8 * len)) xa4
                               (Z_to_bv 64 q) (Z_to_bv 64 len) xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until dg; intros INV Hi Hf Hq Hfe; [exfalso; lia|].
    pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3bffc%Z => first [ eapply (pm_45c q fe); [pm_close | lia | lia] | fail 100 "cut" pc ]
      | 0x3be48%Z => first [ eapply evt_eq; [| eapply (IH (i + 1)%Z q fe); [pm_close | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0x3bea0%Z => first [ num_cur_mem ltac:(fun m1 => lazymatch goal with XN1 : rw_cells _ m1 (X + 496) [C2 (Z_to_bv 64 ?l)] |- _ =>
                               eapply evt_eq; [| eapply (pm_cf (Z.to_nat l) 1 q fe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 l dg); [pm_close | lia | lia | lia | lia]]; num_st_eq end)
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_trunc_frac : forall (cnt q fe : Z) xt0 xt1 xt2 xs0 xs1 xa2 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (0 <= cnt <= 19)%Z -> (A <= q <= fe)%Z -> (fe <= A + TL)%Z ->
    evt psegs (pm_post E) (PMX E 0x3be28 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 fe) xa2 (Z_to_bv 64 106416)
                               (Z_to_bv 64 q) (Z_to_bv 64 len) xa7
                               xs2 xs3 xs4 (Z_to_bv 64 cnt) xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV Hc Hq Hfe.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3bffc%Z => first [ eapply (pm_45c q fe); [pm_close | lia | lia] | fail 100 "cut" pc ]
      | 0x3be48%Z => first [ eapply evt_eq; [| eapply (pm_mf (Z.to_nat len) 0 q fe); [exact INV0 | lia | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End PMTF.
