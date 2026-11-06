(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumSwar.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_sp_defs Sj_num_sp_cl Sj_num_sp_dc Sj_num_sp_cf1 Sj_num_sp_pdefs Sj_num_sp_acc Sj_num_sp_exp Sj_num_sp_frac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section SPFRAC2.
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

  Lemma sp_e38 : forall (IP IL p : Z) xra xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_ffacts E IP IL p ->
    evt psegs (sp_post E) (FS 0x51c84 IP IL p xra xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (LAST - p)) xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM FF.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x51d20%Z => first [ eapply evt_eq; [| eapply (sp_ed4 HSET HPM HPDC HNDC E OK IP IL p)]; [num_st_eq | exact INV | assumption | exact FF] | fail 100 "cut" pc ]
      | 0x51cb4%Z => first [ eapply evt_eq; [| eapply (sp_e68 HSET HPM HPDC HNDC E OK IP IL p _ 0%Z)]; [num_st_eq | exact INV | assumption | exact FF | lia |];
                             transitivity (le4z (sp_tb E p) (sp_tb E (p + 1)) (sp_tb E (p + 2)) (sp_tb E (p + 3)));
                             [reflexivity | rewrite le4z_eq by apply sp_tb_range; lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_L2 : forall (f : nat) (IP IL p : Z) xra xs0 xs1 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_ffacts E IP IL p -> (p + 8 <= LAST)%Z -> (LAST - p <= 8 * Z.of_nat f)%Z ->
    evt psegs (sp_post E) (FS 0x51818 IP IL p xra xs0 xs1 xa6 xa7 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 5063812098665367110) xs4 (Z_to_bv 64 7)
                               xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (LAST - p)) (Z_to_bv 64 9259542123273814144) xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM FF Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x51cb4%Z => first [ eapply evt_eq; [| eapply (sp_e68 HSET HPM HPDC HNDC E OK IP IL p _
                                                          (sp_tb E (p + 4) + 256 * (sp_tb E (p + 5) + 256 * (sp_tb E (p + 6) + 256 * sp_tb E (p + 7))))%Z)];
                             [num_st_eq | exact INV | assumption | exact FF | lia |];
                             transitivity (le8z (sp_tb E p) (sp_tb E (p + 1)) (sp_tb E (p + 2)) (sp_tb E (p + 3)) (sp_tb E (p + 4)) (sp_tb E (p + 5)) (sp_tb E (p + 6)) (sp_tb E (p + 7)));
                             [reflexivity | rewrite le8z_eq by apply sp_tb_range; reflexivity]
                           | fail 100 "cut" pc ]
      | 0x51c84%Z => first [ eapply evt_eq; [| eapply (sp_e38 IP IL (p + 8)%Z)]; [num_st_eq | exact INV | assumption |];
                             apply sp_ffacts_app; [exact FF | lia | lia |];
                             lazymatch goal with KB : Z.land _ 9259542123273814144 = 0%Z |- _ => exact (sp_swar8 E p _ KB) end
                           | fail 100 "cut" pc ]
      | 0x51818%Z => first [ eapply evt_eq; [| eapply (IH IP IL (p + 8)%Z)]; [num_st_eq | exact INV | assumption | | lia | lia];
                             apply sp_ffacts_app; [exact FF | lia | lia |];
                             lazymatch goal with KB : Z.land _ 9259542123273814144 = 0%Z |- _ => exact (sp_swar8 E p _ KB) end
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_948 : forall (IP IL : Z) xra xt1 xt2 xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> (A <= IP)%Z -> (1 <= IL)%Z -> (IP + IL <= LAST)%Z -> sp_ge48 E IP (IP + IL) ->
    evt psegs (sp_post E) (SPS E 0x51794 xra (Z_to_bv 64 (IP + IL)) xt1 xt2 xs0 xs1 (Z_to_bv 64 IP) (Z_to_bv 64 LAST) (Z_to_bv 64 OUT) (Z_to_bv 64 53)
                               (Z_to_bv 64 SPATH_A4) (Z_to_bv 64 IL) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM H1 H2 H3 G1.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    assert (PF0 : sp_pfacts E IP IL 0 0) by (split; [lia|]; split; [exact G1|]; left; split; reflexivity).
    assert (FF0 : bv_unsigned (nth (Z.to_nat (IP + IL - A)) (q_txt E) (Z_to_bv 8 0)) = 46%Z -> (IP + IL < LAST)%Z -> sp_ffacts E IP IL (IP + IL + 1)).
    { intros D L. split; [lia|]. split; [exact G1|]. split; [exact D|]. apply sp_ge48_nil. }
    unfold SPATH_A4.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x51d68%Z => first [ eapply evt_eq; [| eapply (sp_f1c HSET HPM HPDC HNDC E OK IP IL 0%Z 0%Z (IP + IL)%Z)];
                             [unfold SPATH_A4; num_st_eq | exact INV | assumption | exact PF0 | lia] | fail 100 "cut" pc ]
      | 0x51c84%Z => first [ eapply evt_eq; [| eapply (sp_e38 IP IL (IP + IL + 1)%Z)]; [unfold SPATH_A4; num_st_eq | exact INV | assumption | apply FF0; [assumption | lia]]
                           | fail 100 "cut" pc ]
      | 0x51818%Z => first [ eapply evt_eq; [| eapply (sp_L2 (Z.to_nat LAST) IP IL (IP + IL + 1)%Z)];
                             [unfold SPATH_A4; num_st_eq | exact INV | assumption | apply FF0; [assumption | lia] | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.
End SPFRAC2.
