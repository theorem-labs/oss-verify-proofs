(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Zsr Zsp Zve Zvd Zv7 Zva.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac num_abstract_data ::= num_abstract_data_u.
Local Ltac nnorm ::= nnorm_cf.

Definition spu_tmd (E : spuenv) (xa7 wv : word) (IP IL FPT FL : Z) : Prop :=
  (bv_unsigned xa7 <> 0 -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL /\ 1 <= bv_unsigned wv <= 18446744073709551614)%Z.

Section SPUCF1.
  Variable E : spuenv.
  Hypothesis OK : spu_ok E.
  Hypothesis HSET : spu_memset_stmt.
  Hypothesis HPM : spu_pm_stmt.
  Hypothesis HPDC : spu_pdc_stmt.
  Hypothesis HNDC : spu_ndc_stmt.

  Ltac num_mark_words :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact I
    end.
  Ltac cfu_tables mm :=
    let tb := fresh "tb" in let TBL := fresh "TBL" in let TB := fresh "TB" in let TBZ := fresh "TBZ" in
    destruct (image_readable_b usegs mm (Z.to_nat 10416) 0x171a8 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TBL & TB);
    assert (TBZ : Z.of_nat (length tb) = 10416%Z) by (rewrite TBL; apply Z2Nat.id; lia); clear TBL.

  Definition cf1u_k (pc : Z) : Prop :=
    forall (q : Z) (wv xa7 : word) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
      SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> (-342 <= q <= 308)%Z -> spu_tmd E xa7 wv IP IL FPT FL ->
      evt usegs (spu_post E) (SPS E pc xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 xa2 xa3 wv xa5 xa6 xa7
                                 xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Ltac cf1_start :=
    unfold cf1u_k; intros until FL; intros INV FRM Hq HTM;
    lazymatch goal with INVh : SPUINV _ ?m _ _ _ _ _ |- _ => let INV0 := fresh "INV0" in pose proof INVh as INV0; spu_open INV0; spu_env OK; cfu_tables m end;
    lazymatch goal with H7 : spu_tmd _ ?x7 _ _ _ _ _ |- _ =>
      let M7 := fresh "KEEP" in assert (M7 : IsData x7) by exact I; num_mark_words; clear M7 end.
  Ltac cf1_cut K q wv xa7 INV FRM HTM := first [ eapply evt_eq; [| eapply (K q wv xa7)]; [num_st_eq | exact INV | assumption | lia | exact HTM] | fail 100 "cut" ].

  Ltac cf1_tail INV FRM := first [ eapply evt_eq; [| eapply (spu_0a8 E OK)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut tail" ].
  Ltac cf1_b50 q wv INV FRM HTM :=
    first [ match goal with KB : (bv_unsigned _ <> 0)%Z |- _ =>
              let SPN := fresh "SPN" in let HW := fresh "HW" in
              destruct (HTM KB) as [SPN HW];
              eapply evt_eq; [| eapply (spu_b50 E OK HSET HPM HPDC HNDC q wv)]; [num_st_eq | exact INV | assumption | exact SPN | lia | exact HW | left; lia]
            end
          | fail 100 "cut b50" ].

  Lemma cf1_b4c : cf1u_k 0x44cb8.
  Proof using OK HSET HPM HPDC HNDC.
    cf1_start.
    uwalk ltac:(fun pc => lazymatch pc with | 0x45214%Z => cf1_tail INV FRM | 0x44cbc%Z => cf1_b50 q wv INV FRM HTM end).
  Qed.
  Lemma cf1_b40 : cf1u_k 0x44cac.
  Proof using OK HSET HPM HPDC HNDC.
    cf1_start. nstep.
    uwalk ltac:(fun pc => lazymatch pc with | 0x452cc%Z => u_trap pc | 0x44cb8%Z => cf1_cut cf1_b4c q wv xa7 INV FRM HTM end).
  Qed.
  Lemma cf1_afc : cf1u_k 0x44c68.
  Proof using OK HSET HPM HPDC HNDC.
    cf1_start. nstep.
    uwalk ltac:(fun pc => lazymatch pc with | 0x452cc%Z => u_trap pc | 0x44cac%Z => cf1_cut cf1_b40 q wv xa7 INV FRM HTM end).
  Qed.
  Lemma cf1_abc : cf1u_k 0x44c28.
  Proof using OK HSET HPM HPDC HNDC.
    cf1_start. nstep.
    uwalk ltac:(fun pc => lazymatch pc with | 0x452cc%Z => u_trap pc | 0x44c68%Z => cf1_cut cf1_afc q wv xa7 INV FRM HTM end).
  Qed.
  Lemma cf1_a70 : cf1u_k 0x44bdc.
  Proof using OK HSET HPM HPDC HNDC.
    cf1_start. nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x452cc%Z => u_trap pc
      | 0x44c28%Z => cf1_cut cf1_abc q wv xa7 INV FRM HTM
      | 0x45214%Z => cf1_tail INV FRM
      | 0x44cbc%Z => cf1_b50 q wv INV FRM HTM
      end).
  Qed.
  Lemma cf1_968 : cf1u_k 0x44ad4.
  Proof using OK HSET HPM HPDC HNDC.
    cf1_start. nstep.
    uwalk ltac:(fun pc => lazymatch pc with | 0x452cc%Z => u_trap pc | 0x44bdc%Z => cf1_cut cf1_a70 q wv xa7 INV FRM HTM end).
  Qed.

  Lemma spu_930 : forall (q : Z) (wv xa7 : word) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> (-9223372036854775808 <= q < 9223372036854775808)%Z -> spu_tmd E xa7 wv IP IL FPT FL ->
    evt usegs (spu_post E) (SPS E 0x44a9c xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 xa2 xa3 wv xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until FL. intros INV FRM Hq HTM.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x452cc%Z => u_trap pc
      | 0x44ad4%Z => cf1_cut cf1_968 q wv xa7 INV FRM HTM
      | 0x45214%Z => cf1_tail INV FRM
      | 0x44cbc%Z =>
          first [ match goal with KB : (bv_unsigned xa7 <> 0)%Z |- _ =>
                    let SPN := fresh "SPN" in let HW := fresh "HW" in
                    destruct (HTM KB) as [SPN HW];
                    first [ exfalso; lia
                          | eapply evt_eq; [| eapply (spu_b50 E OK HSET HPM HPDC HNDC q wv)];
                            [num_st_eq | exact INV | assumption | exact SPN | lia | exact HW
                            | unfold cf1u_out; first [ right; left; split; [lia | split; reflexivity] | right; right; split; [lia | split; reflexivity] ] ] ]
                  end
                | fail 100 "cut b50" pc ]
      end).
  Qed.
End SPUCF1.
