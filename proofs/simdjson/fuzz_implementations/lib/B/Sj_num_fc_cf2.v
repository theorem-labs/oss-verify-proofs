(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU SjNumN SjNumSwar.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_tail Sj_num_fc_dc Sj_num_fc_dc2 Sj_num_fc_dc3 Sj_num_fc_ce.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.
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

Definition cf1b_out (q : Z) (s6v s9v : word) : Prop :=
  (-342 <= q <= 308)%Z \/ (q < -342 /\ s6v = Z_to_bv 64 0 /\ s9v = Z_to_bv 64 0)%Z \/ (308 < q /\ s6v = Z_to_bv 64 0 /\ s9v = Z_to_bv 64 2047)%Z.

Section FCBCF2.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Hypothesis PV : fcb_prov E.
  Variable Q : machine_state -> Prop.
  Hypothesis KF5 : fcb_kf5 E Q.
  Hypothesis KMSET : fcb_kmset E Q.
  Notation OUT := (q_OUT E).
  Notation f := (q_f E).

  Ltac num_mark_words :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact I
    end.
  Ltac cfb_tables mm :=
    let tb := fresh "tb" in let TBL := fresh "TBL" in let TB := fresh "TB" in let TBZ := fresh "TBZ" in
    destruct (image_readable_b bsegs mm (Z.to_nat 10416) 0x2d060 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TBL & TB);
    assert (TBZ : Z.of_nat (length tb) = 10416%Z) by (rewrite TBL; apply Z2Nat.id; lia); clear TBL.

  Definition cf2b_k (pc : Z) : Prop :=
    forall (s : Z) (wv : word) xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs9 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
      FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc -> fcb_spans E IP IL FPT FL -> (-342 <= s <= 308)%Z -> (bv_unsigned wv <> 0)%Z ->
      evt bsegs Q (FCB E pc xra xt0 xt1 xt2 xa0 wv xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7 (Z_to_bv 64 s) xs9 (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Ltac cf2_start :=
    unfold cf2b_k; intros until FL; intros INV FRM SPN Hq HW;
    lazymatch goal with INVh : FCINV _ ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let INV0 := fresh "INV0" in pose proof INVh as INV0; fc_open INV0; fcb_env OK; fcb_prov_tbl PV; cfb_tables m end;
    num_mark_words.
  Ltac cf2_cut K s wv INV FRM SPN HW := first [ eapply evt_eq; [| eapply (K s wv)]; [num_st_eq | exact INV | assumption | exact SPN | lia | exact HW] | fail 100 "cut" ].
  Ltac to_tail INV FRM := first [ eapply evt_eq; [| eapply (fcb_a5c E OK PV Q KF5) with (bg := true)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut tail" ].
  Ltac to_ce s wv INV FRM SPN HW := first [ eapply evt_eq; [| eapply (fcb_5a0 E OK PV Q KF5 KMSET s wv)]; [num_st_eq | exact INV | exact FRM | exact SPN | lia | exact HW] | fail 100 "cut ce" ].

  Lemma cf2_59c : cf2b_k 0xf8704.
  Proof using OK PV KF5 KMSET.
    cf2_start.
    bwalk ltac:(fun pc => lazymatch pc with | 0xf8cc0%Z => u_trap pc | 0xf8bc4%Z => to_tail INV FRM | 0xf8708%Z => to_ce s wv INV FRM SPN HW end).
  Qed.
  Lemma cf2_598 : cf2b_k 0xf8700.
  Proof using OK PV KF5 KMSET.
    cf2_start.
    bwalk ltac:(fun pc => lazymatch pc with | 0xf8cc0%Z => u_trap pc | 0xf8704%Z => cf2_cut cf2_59c s wv INV FRM SPN HW | 0xf8708%Z => to_ce s wv INV FRM SPN HW end).
  Qed.
  Lemma cf2_58c : cf2b_k 0xf86f4.
  Proof using OK PV KF5 KMSET.
    cf2_start.
    bwalk ltac:(fun pc => lazymatch pc with | 0xf8cc0%Z => u_trap pc | 0xf8700%Z => cf2_cut cf2_598 s wv INV FRM SPN HW end).
  Qed.
  Lemma cf2_548 : cf2b_k 0xf86b0.
  Proof using OK PV KF5 KMSET.
    cf2_start.
    bwalk ltac:(fun pc => lazymatch pc with | 0xf8cc0%Z => u_trap pc | 0xf86f4%Z => cf2_cut cf2_58c s wv INV FRM SPN HW end).
  Qed.
  Lemma cf2_508 : cf2b_k 0xf8670.
  Proof using OK PV KF5 KMSET.
    cf2_start.
    bwalk ltac:(fun pc => lazymatch pc with | 0xf8cc0%Z => u_trap pc | 0xf86b0%Z => cf2_cut cf2_548 s wv INV FRM SPN HW end).
  Qed.
  Lemma cf2_3b8 : cf2b_k 0xf8520.
  Proof using OK PV KF5 KMSET.
    cf2_start.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xf8cc0%Z => u_trap pc
      | 0xf8670%Z => cf2_cut cf2_508 s wv INV FRM SPN HW
      | 0xf8704%Z => cf2_cut cf2_59c s wv INV FRM SPN HW
      | 0xf8708%Z => to_ce s wv INV FRM SPN HW
      end).
  Qed.
  Lemma cf2_290 : cf2b_k 0xf83f8.
  Proof using OK PV KF5 KMSET.
    cf2_start.
    bwalk ltac:(fun pc => lazymatch pc with | 0xf8cc0%Z => u_trap pc | 0xf8520%Z => cf2_cut cf2_3b8 s wv INV FRM SPN HW end).
  Qed.
End FCBCF2.
