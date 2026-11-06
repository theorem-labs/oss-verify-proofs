(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_pm_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section PMROUND.
  Variable E : pmenv.
  Hypothesis OK : pm_ok E.
  Notation X := (p_X E).

  Lemma pm_inc : forall xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg ->
    evt psegs (pm_post E) (PMX E 0x525f0 xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x525fc%Z => first [ eapply (pm_exit E OK); pm_close | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_mulA : forall (Q : machine_state -> Prop) (f : nat) (i n : Z)
      xt0 xt1 xt2 xs0 xs1 xa2 xa4 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (0 <= i < n)%Z -> (n <= 62)%Z -> (n - i <= Z.of_nat f)%Z ->
    (forall xt0' xa2' xa5' xa6' mm', PMINV E mm' len dg ->
       evt psegs Q (PMX E 0x52538 xt0' xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + 8 * n)) xa2' xa4 xa5' xa6' xa7
                        xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm')) ->
    evt psegs Q (PMX E 0x52514 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + 8 * n)) xa2 xa4 (Z_to_bv 64 (X + 8 * i)) xa6 xa7
                     xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros Q f. induction f as [|f IH]; intros until dg; intros INV Hi Hn Hf HK; [exfalso; lia|].
    pm_open INV. pm_env OK.
    nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x52514%Z => first [ eapply evt_eq; [| eapply (IH (i + 1)%Z n); [pm_close | lia | lia | lia | exact HK]]; num_st_eq | fail 100 "cut" pc ]
      | 0x52538%Z => first [ apply HK; pm_close | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_carA : forall (Q : machine_state -> Prop) (f : nat) (p : Z)
      xt0 xt1 xt2 xs0 xs1 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (1 <= p <= len)%Z -> (len - p <= Z.of_nat f)%Z ->
    (forall xa1' xa2' xa4' xa5' mm', PMINV E mm' len dg ->
       evt psegs Q (PMX E 0x5259c xt0 xt1 xt2 xs0 xs1 xa1' xa2' xa4' xa5' xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm')) ->
    (forall xa1' xa2' xa4' xa5' mm', PMINV E mm' len dg ->
       evt psegs Q (PMX E 0x525f0 xt0 xt1 xt2 xs0 xs1 xa1' xa2' xa4' xa5' xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm')) ->
    evt psegs Q (PMX E 0x52568 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (len - p + 1)) (Z_to_bv 64 (X + 8 * p)) xa4 xa5 xa6 xa7
                     xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros Q f. induction f as [|f IH]; intros until dg; intros INV Hp Hf HPUSH HINC.
    - pm_open INV. pm_env OK. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x5259c%Z => first [ apply HPUSH; pm_close | fail 100 "cut" pc ]
        end).
    - pm_open INV. pm_env OK. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x5259c%Z => first [ apply HPUSH; pm_close | fail 100 "cut" pc ]
        | 0x525f0%Z => first [ apply HINC; pm_close | fail 100 "cut" pc ]
        | 0x52568%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z); [pm_close | lia | lia | exact HPUSH | exact HINC]]; num_st_eq | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma pm_push1A : forall xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (len <= 61)%Z ->
    evt psegs (pm_post E) (PMX E 0x525a4 xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa4 xa5 xa6 (Z_to_bv 64 len) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV Hl. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x525f0%Z => first [ eapply pm_inc; pm_close | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_roundA : forall xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg ->
    evt psegs (pm_post E) (PMX E 0x524fc xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa4 xa5 xa6 (Z_to_bv 64 len) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV. pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x525a4%Z => first [ eapply pm_push1A; [exact INV0 | lia] | fail 100 "cut" pc ]
      | 0x52514%Z => idtac
      end).
    eapply evt_eq; [| eapply (pm_mulA (pm_post E) (Z.to_nat len) 0 len); [exact INV0 | lia | lia | lia |]]; [num_st_eq|].
    pm_forget. clear INV0. intros xt0' xa2' xa5' xa6' mm1 INV. pm_open INV.
    walk ltac:(fun pc => lazymatch pc with
      | 0x525f0%Z => first [ eapply pm_inc; pm_close | fail 100 "cut" pc ]
      | 0x52568%Z => idtac
      end).
    all: num_cur_mem ltac:(fun m1 => lazymatch goal with XN1 : rw_cells _ m1 (X + 496) [C2 (Z_to_bv 64 ?l)] |- _ =>
           assert (INV1 : PMINV E m1 l dg) by pm_close;
           eapply evt_eq; [| eapply (pm_carA (pm_post E) (Z.to_nat l) 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l dg INV1); [lia | lia | |]]; [num_st_eq | |] end).
    all: intros ya1 ya2 ya4 ya5 mm2 INV2.
    all: try (eapply pm_inc; exact INV2).
    all: pm_forget; pm_open INV2.
    all: walk ltac:(fun pc => lazymatch pc with
      | 0x525f0%Z => first [ eapply pm_inc; pm_close | fail 100 "cut" pc ]
      | 0x525a4%Z => first [ eapply pm_push1A; [pm_close | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_mulB : forall (Q : machine_state -> Prop) (f : nat) (i n : Z)
      xt0 xt1 xt2 xs0 xs1 xa2 xa4 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (0 <= i < n)%Z -> (n <= 62)%Z -> (n - i <= Z.of_nat f)%Z ->
    (forall xt0' xa2' xa5' xa7' mm', PMINV E mm' len dg ->
       evt psegs Q (PMX E 0x523e8 xt0' xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + 8 * n)) xa2' xa4 xa5' xa6 xa7'
                        xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm')) ->
    evt psegs Q (PMX E 0x523c4 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + 8 * n)) xa2 xa4 (Z_to_bv 64 (X + 8 * i)) xa6 xa7
                     xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros Q f. induction f as [|f IH]; intros until dg; intros INV Hi Hn Hf HK; [exfalso; lia|].
    pm_open INV. pm_env OK.
    nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x523c4%Z => first [ eapply evt_eq; [| eapply (IH (i + 1)%Z n); [pm_close | lia | lia | lia | exact HK]]; num_st_eq | fail 100 "cut" pc ]
      | 0x523e8%Z => first [ apply HK; pm_close | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_carB : forall (Q : machine_state -> Prop) (f : nat) (p : Z)
      xt0 xt1 xt2 xs0 xs1 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (1 <= p <= len)%Z -> (len - p <= Z.of_nat f)%Z ->
    (forall xa1' xa2' xa4' xa5' mm', PMINV E mm' len dg ->
       evt psegs Q (PMX E 0x525d0 xt0 xt1 xt2 xs0 xs1 xa1' xa2' xa4' xa5' xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm')) ->
    (forall xa1' xa2' xa4' xa5' mm', PMINV E mm' len dg ->
       evt psegs Q (PMX E 0x525f0 xt0 xt1 xt2 xs0 xs1 xa1' xa2' xa4' xa5' xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm')) ->
    evt psegs Q (PMX E 0x52418 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (len - p + 1)) (Z_to_bv 64 (X + 8 * p)) xa4 xa5 xa6 xa7
                     xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros Q f. induction f as [|f IH]; intros until dg; intros INV Hp Hf HPUSH HINC.
    - pm_open INV. pm_env OK. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x525d0%Z => first [ apply HPUSH; pm_close | fail 100 "cut" pc ]
        end).
    - pm_open INV. pm_env OK. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x525d0%Z => first [ apply HPUSH; pm_close | fail 100 "cut" pc ]
        | 0x525f0%Z => first [ apply HINC; pm_close | fail 100 "cut" pc ]
        | 0x52418%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z); [pm_close | lia | lia | exact HPUSH | exact HINC]]; num_st_eq | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma pm_push1B : forall xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (len <= 61)%Z ->
    evt psegs (pm_post E) (PMX E 0x525d8 xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa4 xa5 (Z_to_bv 64 len) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV Hl. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x525f0%Z => first [ eapply pm_inc; pm_close | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_roundB : forall xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg ->
    evt psegs (pm_post E) (PMX E 0x523ac xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa4 xa5 (Z_to_bv 64 len) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV. pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x525d8%Z => first [ eapply pm_push1B; [exact INV0 | lia] | fail 100 "cut" pc ]
      | 0x523c4%Z => idtac
      end).
    eapply evt_eq; [| eapply (pm_mulB (pm_post E) (Z.to_nat len) 0 len); [exact INV0 | lia | lia | lia |]]; [num_st_eq|].
    pm_forget. clear INV0. intros xt0' xa2' xa5' xa7' mm1 INV. pm_open INV.
    walk ltac:(fun pc => lazymatch pc with
      | 0x525f0%Z => first [ eapply pm_inc; pm_close | fail 100 "cut" pc ]
      | 0x52418%Z => idtac
      end).
    all: num_cur_mem ltac:(fun m1 => lazymatch goal with XN1 : rw_cells _ m1 (X + 496) [C2 (Z_to_bv 64 ?l)] |- _ =>
           assert (INV1 : PMINV E m1 l dg) by pm_close;
           eapply evt_eq; [| eapply (pm_carB (pm_post E) (Z.to_nat l) 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l dg INV1); [lia | lia | |]]; [num_st_eq | |] end).
    all: intros ya1 ya2 ya4 ya5 mm2 INV2.
    all: try (eapply pm_inc; exact INV2).
    all: pm_forget; pm_open INV2.
    all: walk ltac:(fun pc => lazymatch pc with
      | 0x525f0%Z => first [ eapply pm_inc; pm_close | fail 100 "cut" pc ]
      | 0x525d8%Z => first [ eapply pm_push1B; [pm_close | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMROUND.
