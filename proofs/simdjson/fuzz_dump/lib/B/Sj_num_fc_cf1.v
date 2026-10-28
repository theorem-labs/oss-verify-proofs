(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumU SjNumN SjNumSwar.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_tail Sj_num_fc_dc Sj_num_fc_dc2 Sj_num_fc_dc3 Sj_num_fc_ce Sj_num_fc_cf2 Sj_num_fc_cf2b.
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
Local Ltac nnorm ::= nnorm_cf.

Definition fcb_tmd (E : fcbenv) (t2 : Z) (wv : word) (IP IL FPT FL : Z) : Prop :=
  (t2 <> 0 -> fcb_spans E IP IL FPT FL /\ 1 <= bv_unsigned wv <= 18446744073709551614)%Z.

Section FCBCF1.
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
    destruct (image_readable_b bsegs mm (Z.to_nat 10416) 0x28700 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TBL & TB);
    assert (TBZ : Z.of_nat (length tb) = 10416%Z) by (rewrite TBL; apply Z2Nat.id; lia); clear TBL.

  Definition cf1b_k (pc : Z) : Prop :=
    forall (s t2 : Z) (wv : word) xra xt0 xt1 xt2 xa0 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs9 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
      FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc -> fcb_tmd E t2 wv IP IL FPT FL -> (-342 <= s <= 308)%Z ->
      evt bsegs Q (FCB E pc xra xt0 xt1 xt2 xa0 wv (Z_to_bv 64 t2) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7 (Z_to_bv 64 s) xs9 (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6 xF xfc mm).
  Ltac cf1_start :=
    unfold cf1b_k; intros until FL; intros INV FRM TMD Hq;
    lazymatch goal with INVh : FCINV _ ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let INV0 := fresh "INV0" in pose proof INVh as INV0; fc_open INV0; fcb_env OK; fcb_prov_tbl PV; cfb_tables m end;
    num_mark_words.
  Ltac cf1_cut K s t2 wv INV FRM TMD := first [ eapply evt_eq; [| eapply (K s t2 wv)]; [num_st_eq | exact INV | assumption | exact TMD | lia] | fail 100 "cut" ].
  Ltac to_tail INV FRM := first [ eapply evt_eq; [| eapply (fcb_a5c E OK PV Q KF5) with (bg := true)]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut tail" ].

  Ltac to_cf2 s wv INV FRM TMD R :=
    first [ lazymatch type of TMD with fcb_tmd _ ?t _ _ _ _ _ =>
              let A2N := fresh "A2N" in assert (A2N : t <> 0%Z) by lia;
              let SPN := fresh "SPN" in let HWD := fresh "HWD" in destruct (TMD A2N) as [SPN HWD];
              eapply evt_eq; [| eapply (fcb_25c E OK PV Q KF5 KMSET s wv)]; [num_st_eq | exact INV | assumption | exact SPN | lia | exact HWD | R] end
          | fail 100 "cut cf2" ].
  Ltac cf1_exits s wv INV FRM TMD :=
    fun pc => lazymatch pc with
      | 0xe9bd8%Z => u_trap pc
      | 0xe9adc%Z => to_tail INV FRM
      | 0xe92dc%Z => to_cf2 s wv INV FRM TMD ltac:(left; lia)
      end.

  Lemma cf1_258 : cf1b_k 0xe92d8.
  Proof using OK PV KF5 KMSET.
    cf1_start. bwalk ltac:(cf1_exits s wv INV FRM TMD).
  Qed.
  Lemma cf1_24c : cf1b_k 0xe92cc.
  Proof using OK PV KF5 KMSET.
    cf1_start. bwalk ltac:(fun pc => lazymatch pc with | 0xe92d8%Z => cf1_cut cf1_258 s t2 wv INV FRM TMD | _ => cf1_exits s wv INV FRM TMD pc end).
  Qed.
  Lemma cf1_208 : cf1b_k 0xe9288.
  Proof using OK PV KF5 KMSET.
    cf1_start. bwalk ltac:(fun pc => lazymatch pc with | 0xe92cc%Z => cf1_cut cf1_24c s t2 wv INV FRM TMD | _ => cf1_exits s wv INV FRM TMD pc end).
  Qed.
  Lemma cf1_1c8 : cf1b_k 0xe9248.
  Proof using OK PV KF5 KMSET.
    cf1_start. bwalk ltac:(fun pc => lazymatch pc with | 0xe9288%Z => cf1_cut cf1_208 s t2 wv INV FRM TMD | _ => cf1_exits s wv INV FRM TMD pc end).
  Qed.
  Lemma cf1_17c : cf1b_k 0xe91fc.
  Proof using OK PV KF5 KMSET.
    cf1_start. bwalk ltac:(fun pc => lazymatch pc with | 0xe9248%Z => cf1_cut cf1_1c8 s t2 wv INV FRM TMD | _ => cf1_exits s wv INV FRM TMD pc end).
  Qed.
  Lemma cf1_054 : cf1b_k 0xe90d4.
  Proof using OK PV KF5 KMSET.
    cf1_start. bwalk ltac:(fun pc => lazymatch pc with | 0xe91fc%Z => cf1_cut cf1_17c s t2 wv INV FRM TMD | _ => cf1_exits s wv INV FRM TMD pc end).
  Qed.
End FCBCF1.
