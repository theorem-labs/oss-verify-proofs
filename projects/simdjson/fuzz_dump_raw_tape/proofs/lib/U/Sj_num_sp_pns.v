(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumSwar SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_cl Sj_num_sp_ce Sj_num_sp_cf2 Sj_num_sp_cf1 Sj_num_sp_clg Sj_num_sp_pdefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Ltac pns_peel H N :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A0 (?c :: ?rest) =>
      change (c :: rest) with ([c] ++ rest) in H; apply num_rw_cells_app in H; destruct H as [N H];
      cbn [cells_size csize Nat.add] in H;
      lazymatch type of H with
      | rw_cells _ _ (?b + ?k + Z.of_nat ?n)%Z _ =>
          let v := eval vm_compute in (k + Z.of_nat n)%Z in replace (b + k + Z.of_nat n)%Z with (b + v)%Z in H by lia
      end
  end.

Lemma rw_cells_c2_zero : forall segs (m : mem) A rest,
  rw_cells segs m A (C2 (Z_to_bv 64 0) :: rest) -> rw_cells segs m A (C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: rest).
Proof.
  intros segs m A rest H. eapply rw_cells_recell; [ | | exact H].
  - destruct H as [[WF _] _]. cbn in WF |- *. tauto.
  - reflexivity.
Qed.

Section SPUPNS.
  Variable E : spuenv.
  Hypothesis OK : spu_ok E.
  Hypothesis HSET : spu_memset_stmt.
  Hypothesis HPM : spu_pm_stmt.
  Hypothesis HPDC : spu_pdc_stmt.
  Hypothesis HNDC : spu_ndc_stmt.

  Lemma spu_488 : forall (q IP IL FPT FL : Z) (wv xa7 c0 spl : word) xra xt0 xt2 xs0 xa0 xa1 xa3 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> (-9223372036854775808 <= q < 9223372036854775808)%Z -> sp_pfacts E IP IL FPT FL ->
    (bv_unsigned xa7 <> 0 -> 1 <= bv_unsigned wv <= 18446744073709551614)%Z ->
    evt usegs (spu_post E) (SPS E 0x5756c xra xt0 (Z_to_bv 64 IL) xt2 xs0 (Z_to_bv 64 q) xa0 xa1 (Z_to_bv 64 FPT) xa3 wv c0 (Z_to_bv 64 IP) xa7
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM Hq PF HTM. spu_open0 INV. spu_env OK.
    pose proof (sp_pfacts_spans E IP IL FPT FL OK PF) as SPN.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x58244%Z => u_trap pc
      | _ => lazymatch pc with 0x57a14%Z => idtac | 0x57974%Z => idtac end;
             lazymatch goal with NEGB : rw_cells _ _ _ (C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.b2z ?b)))) :: _) |- _ =>
          first [ assert (NBR : (0 <= Z.b2z b <= 1)%Z) by (destruct b; cbn; lia);
                  rewrite (unsigned_lit (Z.b2z b)) in NEGB by lia;
                  pns_peel NEGB NEG;
                  num_cur_mem ltac:(fun m1 => assert (INV1 : SPUINV E m1 (Z.b2z b) IP IL FPT FL) by spu_close);
                  assert (TMD : spu_tmd E xa7 wv IP IL FPT FL) by (intros K; split; [exact SPN | exact (HTM K)]);
                  lazymatch pc with
                  | 0x57a14%Z => eapply evt_eq; [| eapply (spu_930 E OK HSET HPM HPDC HNDC q wv xa7)]; [num_st_eq | exact INV1 | assumption | lia | exact TMD]
                  | 0x57974%Z => eapply evt_eq; [| eapply (spu_890 E OK HSET HPM HPDC HNDC q wv xa7)]; [num_st_eq | exact INV1 | assumption | lia | exact TMD]
                  end
                | fail 100 "cut" pc ]
          end
      end).
  Qed.

  Ltac err_cut INV0h FRMh :=
    fun pc => lazymatch pc with
      | 0x58244%Z => u_trap pc
      | 0x57974%Z =>
          first [ let NEG := fresh "NEG" in let INV1 := fresh "INV1" in let TMD := fresh "TMD" in
                  lazymatch goal with NEGB : rw_cells _ _ _ (C2 (Z_to_bv 64 0) :: _) |- _ => apply rw_cells_c2_zero in NEGB; pns_peel NEGB NEG end;
                  num_cur_mem ltac:(fun m1 => assert (INV1 : SPUINV E m1 0 0 0 0 0) by spu_close);
                  assert (TMD : spu_tmd E (Z_to_bv 64 0) (Z_to_bv 64 0) 0 0 0 0) by (let K := fresh "K" in intros K; exfalso; apply K; reflexivity);
                  eapply evt_eq; [| eapply (spu_890 E OK HSET HPM HPDC HNDC 0%Z (Z_to_bv 64 0) (Z_to_bv 64 0))]; [num_st_eq | exact INV1 | assumption | lia | exact TMD]
                | fail 100 "cut" pc ]
      end.
  Ltac err_proof := let INV := fresh "INV" in let FRM := fresh "FRM" in intros until mm; intros INV FRM; spu_open0 INV; spu_env OK; kwalk ltac:(err_cut INV FRM).

  Lemma spu_8a4 : forall (spl : word) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc ->
    evt usegs (spu_post E) (SPS E 0x56988 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC. err_proof. Qed.

  Lemma spu_a90 : forall (spl : word) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc ->
    evt usegs (spu_post E) (SPS E 0x56b74 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC. err_proof. Qed.

  Lemma spu_c50 : forall (spl : word) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc ->
    evt usegs (spu_post E) (SPS E 0x56d34 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC. err_proof. Qed.

  Lemma spu_69c : forall (spl : word) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc ->
    evt usegs (spu_post E) (SPS E 0x57780 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC. err_proof. Qed.

  Lemma spu_5dc : forall (spl : word) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc ->
    evt usegs (spu_post E) (SPS E 0x576c0 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 0) xa0 xa1 xa2 xa3 (Z_to_bv 64 0) xa5 xa6 (Z_to_bv 64 0)
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC. err_proof. Qed.

  Lemma spu_f34 : forall (spl : word) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc ->
    evt usegs (spu_post E) (SPS E 0x57018 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC. err_proof. Qed.
  Lemma spu_5c8 : forall (spl : word) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc ->
    evt usegs (spu_post E) (SPS E 0x576ac xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC. err_proof. Qed.
End SPUPNS.
