(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumSwar.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_sp_defs Sj_num_sp_cl Sj_num_sp_dc Sj_num_sp_cf1 Sj_num_sp_pdefs Sj_num_sp_acc Sj_num_sp_exp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section SPFRAC.
  Hypothesis HSET : sp_memset_stmt.
  Hypothesis HPM : sp_pm_stmt.
  Hypothesis HPDC : sp_pdc_stmt.
  Hypothesis HNDC : sp_ndc_stmt.
  Variable E : spenv.
  Hypothesis OK : sp_ok E.
  Notation A := (q_A E).
  Notation LAST := (q_LAST E).
  Notation OUT := (q_OUT E).

  Notation FS pc IP IL p xra xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
    (SPS E pc xra (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL + 1)) xs0 xs1 (Z_to_bv 64 p) (Z_to_bv 64 LAST) (Z_to_bv 64 OUT) (Z_to_bv 64 53)
         (Z_to_bv 64 SPATH_A4) (Z_to_bv 64 IL) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Lemma sp_f04 : forall (IP IL p : Z) xra xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_ffacts E IP IL p ->
    evt psegs (sp_post E) (FS 0x54778 IP IL p xra xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM FF.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x54840%Z => first [ eapply (sp_fcc E OK); [exact INV | assumption] | fail 100 "cut" pc ]
      | 0x54790%Z => first [ eapply evt_eq; [| eapply (sp_f1c HSET HPM HPDC HNDC E OK IP IL (IP + IL + 1)%Z (p - (IP + IL + 1))%Z p)];
                             [num_st_eq | exact INV | assumption | apply sp_ffacts_pfacts; [exact FF | lia] | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_L3 : forall (f : nat) (IP IL p : Z) xra xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_ffacts E IP IL p -> (p < LAST)%Z -> (LAST - p <= Z.of_nat f)%Z ->
    evt psegs (sp_post E) (FS 0x54754 IP IL p xra xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 9) (Z_to_bv 64 10) xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM FF Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    pose proof (sp_tb_range E p) as Rp. unfold sp_tb in Rp.
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x54778%Z => first [ eapply evt_eq; [| eapply (sp_f04 IP IL _)]; [num_st_eq | exact INV | assumption |];
                             first [ exact FF
                                   | replace (q_LAST E) with (p + 1)%Z by lia;
                                     apply sp_ffacts_app; [exact FF | lia | lia | apply sp_ge48_1; unfold sp_tb; lia] ]
                           | fail 100 "cut" pc ]
      | 0x54754%Z => first [ eapply evt_eq; [| eapply (IH IP IL (p + 1)%Z)];
                             [num_st_eq | exact INV | assumption | apply sp_ffacts_app; [exact FF | lia | lia | apply sp_ge48_1; unfold sp_tb; lia] | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_ed4 : forall (IP IL p : Z) xra xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_ffacts E IP IL p ->
    evt psegs (sp_post E) (FS 0x54748 IP IL p xra xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM FF.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x54778%Z => first [ eapply evt_eq; [| eapply (sp_f04 IP IL p)]; [num_st_eq | exact INV | assumption | exact FF] | fail 100 "cut" pc ]
      | 0x54754%Z => first [ eapply evt_eq; [| eapply (sp_L3 (Z.to_nat LAST) IP IL p)]; [num_st_eq | exact INV | assumption | exact FF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_e68 : forall (IP IL p w hi : Z) xra xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_ffacts E IP IL p -> (p + 4 <= LAST)%Z ->
    w = (sp_tb E p + 256 * (sp_tb E (p + 1) + 256 * (sp_tb E (p + 2) + 256 * (sp_tb E (p + 3) + 256 * hi))))%Z ->
    evt psegs (sp_post E) (FS 0x546dc IP IL p xra xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 (Z_to_bv 64 w) xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM FF Hp HW.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x54748%Z => first [ eapply evt_eq; [| eapply (sp_ed4 IP IL _)]; [num_st_eq | exact INV | assumption |];
                             first [ exact FF
                                   | apply sp_ffacts_app; [exact FF | lia | lia |];
                                     lazymatch goal with KB : Z.land _ _ = 0%Z |- _ => exact (sp_swar4 E p w hi _ HW KB) end ]
                           | fail 100 "cut" pc ]
      end).
  Qed.
End SPFRAC.
