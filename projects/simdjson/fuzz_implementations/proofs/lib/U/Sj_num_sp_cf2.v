(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_ce.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac num_abstract_data ::= num_abstract_data_u.

Lemma lor_q684_1 : forall q, (0 <= 2 * q + 684 -> Z.lor (2 * q + 684) 1 = 2 * q + 685)%Z.
Proof. intros q H. replace (2 * q + 684)%Z with (2 * (q + 342))%Z by lia. rewrite lor_even_1 by lia. lia. Qed.
Lemma lor_q684_8 : forall q, (0 <= 2 * q + 684 -> Z.lor (8 * (2 * q + 684)) 8 = 8 * (2 * q + 684) + 8)%Z.
Proof. intros q H. replace (2 * q + 684)%Z with (2 * (q + 342))%Z by lia. rewrite lor_16_8 by lia. lia. Qed.
Ltac nnorm_cf :=
  repeat match goal with
  | |- context [Z.lor (2 * ?q + 684) 1] => rewrite (lor_q684_1 q) by lia
  | |- context [Z.lor (8 * (2 * ?q + 684)) 8] => rewrite (lor_q684_8 q) by lia
  end; nnorm_ce.
Local Ltac nnorm ::= nnorm_cf.

Section SPUCF2.
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
    destruct (image_readable_b usegs mm (Z.to_nat 10416) 0x1aa50 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TBL & TB);
    assert (TBZ : Z.of_nat (length tb) = 10416%Z) by (rewrite TBL; apply Z2Nat.id; lia); clear TBL.

  Lemma spu_dc0 : forall (q : Z) (wv : word) xra xt0 xt1 xt2 (xs0 : word) xa0 xa1 xa2 xa3 (xa5 xa6 : word) xa7 (xs2 : word) xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    ((-342 <= q <= 308)%Z \/ (xs0 = xa6 /\ xs2 = xa5)) -> (bv_unsigned wv <> 0)%Z ->
    evt usegs (spu_post E) (SPS E 0x5fd78 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 xa2 xa3 wv xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until FL. intros INV FRM SPN [Hq | [E1 E2]] HW.
    - assert (D0 : IsData xs0) by exact I. assert (D2 : IsData xs2) by exact I. assert (D5 : IsData xa5) by exact I. assert (D6 : IsData xa6) by exact I.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x60060%Z => first [ eapply evt_eq; [| eapply (spu_0a8 E OK)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut" pc ]
        | 0x5fd80%Z => first [ eapply evt_eq; [| eapply (spu_dc8 E OK HSET HPM HPDC HNDC q wv)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | exact HW] | fail 100 "cut" pc ]
        end).
    - subst xa6 xa5.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x60060%Z => first [ eapply evt_eq; [| eapply (spu_0a8 E OK)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut" pc ]
        end).
  Qed.

  Definition cf2u_k (pc : Z) : Prop :=
    forall (q : Z) (wv : word) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
      SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL -> (-342 <= q <= 308)%Z -> (bv_unsigned wv <> 0)%Z ->
      evt usegs (spu_post E) (SPS E pc xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 xa2 xa3 wv xa5 xa6 xa7
                                 xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Ltac cf2_start :=
    unfold cf2u_k; intros until FL; intros INV FRM SPN Hq HW;
    lazymatch goal with INVh : SPUINV _ ?m _ _ _ _ _ |- _ => let INV0 := fresh "INV0" in pose proof INVh as INV0; spu_open INV0; spu_env OK; cfu_tables m end;
    num_mark_words.
  Ltac cf2_cut K q wv INV FRM SPN HW := first [ eapply evt_eq; [| eapply (K q wv)]; [num_st_eq | exact INV | assumption | exact SPN | lia | exact HW] | fail 100 "cut" ].

  Lemma cf2_dc0 : cf2u_k 0x5fd78.
  Proof using OK HSET HPM HPDC HNDC.
    unfold cf2u_k. intros until FL. intros INV FRM SPN Hq HW.
    eapply (spu_dc0 q wv); [exact INV | exact FRM | exact SPN | left; lia | exact HW].
  Qed.
  Lemma cf2_dc4 : cf2u_k 0x5fd7c.
  Proof using OK HSET HPM HPDC HNDC.
    cf2_start. nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x60060%Z => first [ eapply evt_eq; [| eapply (spu_0a8 E OK)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut" pc ]
      | 0x5fd80%Z => first [ eapply evt_eq; [| eapply (spu_dc8 E OK HSET HPM HPDC HNDC q wv)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | exact HW] | fail 100 "cut" pc ]
      end).
  Qed.
  Lemma cf2_db4 : cf2u_k 0x5fd6c.
  Proof using OK HSET HPM HPDC HNDC.
    cf2_start. nstep.
    uwalk ltac:(fun pc => lazymatch pc with | 0x60118%Z => u_trap pc | 0x5fd78%Z => cf2_cut cf2_dc0 q wv INV FRM SPN HW end).
  Qed.
  Lemma cf2_d70 : cf2u_k 0x5fd28.
  Proof using OK HSET HPM HPDC HNDC.
    cf2_start. nstep.
    uwalk ltac:(fun pc => lazymatch pc with | 0x60118%Z => u_trap pc | 0x5fd6c%Z => cf2_cut cf2_db4 q wv INV FRM SPN HW end).
  Qed.
  Lemma cf2_d30 : cf2u_k 0x5fce8.
  Proof using OK HSET HPM HPDC HNDC.
    cf2_start. nstep.
    uwalk ltac:(fun pc => lazymatch pc with | 0x60118%Z => u_trap pc | 0x5fd28%Z => cf2_cut cf2_d70 q wv INV FRM SPN HW end).
  Qed.
  Lemma cf2_c8c : cf2u_k 0x5fc44.
  Proof using OK HSET HPM HPDC HNDC.
    cf2_start. nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x60118%Z => u_trap pc
      | 0x5fce8%Z => cf2_cut cf2_d30 q wv INV FRM SPN HW
      | 0x5fd7c%Z => cf2_cut cf2_dc4 q wv INV FRM SPN HW
      | 0x5fd80%Z => first [ eapply evt_eq; [| eapply (spu_dc8 E OK HSET HPM HPDC HNDC q wv)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | exact HW] | fail 100 "cut" pc ]
      end).
  Qed.
  Lemma cf2_b84 : cf2u_k 0x5fb3c.
  Proof using OK HSET HPM HPDC HNDC.
    cf2_start. nstep.
    uwalk ltac:(fun pc => lazymatch pc with | 0x60118%Z => u_trap pc | 0x5fc44%Z => cf2_cut cf2_c8c q wv INV FRM SPN HW end).
  Qed.

  Definition cf1u_out (q : Z) (s0v s2v : word) : Prop :=
    (-342 <= q <= 308)%Z \/ (q < -342 /\ s0v = Z_to_bv 64 0 /\ s2v = Z_to_bv 64 0)%Z \/ (308 < q /\ s0v = Z_to_bv 64 0 /\ s2v = Z_to_bv 64 2047)%Z.

  Lemma spu_b50 : forall (q : Z) (wv : word) xra xt0 xt1 xt2 (xs0 : word) xa0 xa1 xa2 xa3 xa5 xa6 xa7 (xs2 : word) xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    (-9223372036854775808 <= q < 9223372036854775808)%Z -> (1 <= bv_unsigned wv <= 18446744073709551614)%Z -> cf1u_out q xs0 xs2 ->
    evt usegs (spu_post E) (SPS E 0x5fb08 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 xa2 xa3 wv xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until FL. intros INV FRM SPN Hq HW R.
    assert (W1 : ((bv_unsigned wv + 1) mod 18446744073709551616 = bv_unsigned wv + 1)%Z) by (apply Z.mod_small; lia).
    assert (HW0 : (bv_unsigned wv <> 0)%Z) by lia.
    destruct R as [R | [(R & -> & ->) | (R & -> & ->)]].
    - uwalk ltac:(fun pc => lazymatch pc with
        | 0x5fb3c%Z => first [ eapply evt_eq; [| eapply (cf2_b84 q wv)]; [num_st_eq | exact INV | assumption | exact SPN | lia | exact HW0] | fail 100 "cut" pc ]
        end).
    - uwalk ltac:(fun pc => lazymatch pc with
        | 0x5fd78%Z => first [ eapply evt_eq; [| eapply (spu_dc0 q wv)]; [num_st_eq | exact INV | assumption | exact SPN | right; split; reflexivity | exact HW0] | fail 100 "cut" pc ]
        end).
    - uwalk ltac:(fun pc => lazymatch pc with
        | 0x60060%Z => first [ eapply evt_eq; [| eapply (spu_0a8 E OK)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut" pc ]
        end).
  Qed.
End SPUCF2.
