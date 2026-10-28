(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU SjNumN SjNumSwar.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_pdefs Sj_num_fc_tail Sj_num_fc_k14 Sj_num_fc_pp1 Sj_num_fc_pp2 Sj_num_fc_pp2b Sj_num_fc_pp2c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Lemma fcb_shr64_small : forall x, (0 <= x < 18446744073709551616)%Z -> Z.shiftr x 64 = 0%Z.
Proof. intros x H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 64)%Z with 18446744073709551616%Z. apply Z.div_small. exact H. Qed.
Lemma fcb_shr63_small : forall x, (0 <= x < 9223372036854775808)%Z -> Z.shiftr x 63 = 0%Z.
Proof. intros x H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 63)%Z with 9223372036854775808%Z. apply Z.div_small. exact H. Qed.
Ltac fcb_xnorm :=
  repeat match goal with
  | |- context [bv_signed (Z_to_bv 64 ?z)] => rewrite (num_signed_of_Z z) by lia
  | |- context [Z.shiftr ?x 64] => rewrite (fcb_shr64_small x) by lia
  | |- context [Z.shiftr ?x 63] => rewrite (fcb_shr63_small x) by lia
  end.
Ltac fcb_nnorm_x := nnorm_w; fcb_xnorm.
Local Ltac nnorm ::= fcb_nnorm_x.

Local Ltac num_abstract_data ::= num_abstract_data_u.

Section FCBPP3.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Hypothesis PV : fcb_prov E.
  Variable Q : machine_state -> Prop.
  Hypothesis K14 : fcb_kf14 E Q.
  Notation A := (q_A E).
  Notation FIRST := (q_FIRST E).
  Notation LAST := (q_LAST E).
  Notation OUT := (q_OUT E).
  Notation f := (q_f E).
  Notation P2 L := (L E OK PV Q K14) (only parsing).

  Lemma fcb_7f0 : forall (IP IL FPT FL ex en : Z) c0 c8 c16 c24 c32 c48 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xs7 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> (-2147483648 <= ex <= 0)%Z -> (- FCB_EN_MAX <= en <= FCB_EN_MAX)%Z ->
    evt bsegs Q (FCS E 0xe8bf4 (Z_to_bv 64 (46)) (Z_to_bv 64 (IL + FL)) (Z_to_bv 64 (en)) xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (FL)) (Z_to_bv 64 (ex)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (IP + IL)) xs9 (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros until mm. intros INV FRM PF HIP Hex Hen. pose proof Hen as Hen'. unfold FCB_EN_MAX in Hen'.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0xe8c0c%Z => first [ eapply evt_eq; [| eapply (P2 fcb_808 IP IL FPT FL (ex + en)%Z en c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia | unfold FCB_EN_MAX in *; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_7e4 : forall (IP IL FPT FL ex en : Z) c0 c8 c16 c24 c32 c48 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xs9 xs10 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> (-2147483648 <= ex <= 0)%Z -> (0 <= en <= FCB_EN_MAX)%Z ->
    evt bsegs Q (FCS E 0xe8be8 (Z_to_bv 64 (46)) (Z_to_bv 64 (IL + FL)) (Z_to_bv 64 (en)) xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (FL)) (Z_to_bv 64 (ex)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) (Z_to_bv 64 (OUT)) (Z_to_bv 64 (IP + IL)) xs9 xs10 (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros until mm. intros INV FRM PF HIP Hex Hen.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe8bf4%Z => first [ eapply evt_eq; [| eapply (fcb_7f0 IP IL FPT FL ex _ c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia | unfold FCB_EN_MAX in *; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_L4 : forall (f : nat) (IP IL FPT FL ex en e : Z) c0 c8 c16 c24 c32 c48 xa1 xa2 xa3 xa4 xs9 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> (-2147483648 <= ex <= 0)%Z -> (0 <= en <= FCB_EN_MAX)%Z -> (FIRST <= e < LAST)%Z -> (LAST - e <= Z.of_nat f)%Z ->
    evt bsegs Q (FCS E 0xe8afc (Z_to_bv 64 (46)) (Z_to_bv 64 (IL + FL)) (Z_to_bv 64 (en)) (Z_to_bv 64 (10)) (q_sp E) (Z_to_bv 64 (q_spq E)) (Z_to_bv 64 (e)) xa1 xa2 xa3 xa4 (Z_to_bv 64 (9)) (Z_to_bv 64 (FL)) (Z_to_bv 64 (ex)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) (Z_to_bv 64 (OUT)) (Z_to_bv 64 (IP + IL)) xs9 (Z_to_bv 64 (e)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 (268435455)) (Z_to_bv 64 (2)) xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM PF HIP Hex Hen He Hf; [exfalso; lia|].
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV. unfold FCB_EN_MAX in Hen.
    pose proof (sp_tb_range E e) as Re. unfold sp_tb in Re.
    assert (DR : forall x, (0 <= Z.land x 255 < 256)%Z) by (intros x; rewrite land_255; apply Z.mod_pos_bound; lia).
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0xe8be8%Z => first [ eapply evt_eq; [| eapply (fcb_7e4 IP IL FPT FL ex _ c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia |];
                             unfold FCB_EN_MAX;
                             repeat match goal with |- context [Z.land ?x 255] => pose proof (DR x); rewrite (land_255 x) in * end; lia
                           | fail 100 "cut" pc ]
      | 0xe8afc%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT FL ex _ (e + 1)%Z c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia | | lia | lia];
                             unfold FCB_EN_MAX;
                             repeat match goal with |- context [Z.land ?x 255] => pose proof (DR x); rewrite (land_255 x) in * end; lia
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_798 : forall (IP IL FPT FL ex : Z) c0 c8 c16 c24 c32 c48 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xs9 xs10 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> (-2147483648 <= ex <= 0)%Z ->
    evt bsegs Q (FCS E 0xe8b9c (Z_to_bv 64 (46)) (Z_to_bv 64 (IL + FL)) xt1 xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (FL)) (Z_to_bv 64 (ex)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) (Z_to_bv 64 (OUT)) (Z_to_bv 64 (IP + IL)) xs9 xs10 (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros until mm. intros INV FRM PF HIP Hex.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe8c0c%Z => first [ eapply evt_eq; [| eapply (P2 fcb_808 IP IL FPT FL ex 0%Z c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia | unfold FCB_EN_MAX in *; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_67c : forall (IP IL FPT FL ex : Z) c0 c8 c16 c24 c32 c48 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xs7 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> (-2147483648 <= ex <= 0)%Z ->
    evt bsegs Q (FCS E 0xe8a80 (Z_to_bv 64 (46)) (Z_to_bv 64 (IL + FL)) xt1 xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (FL)) (Z_to_bv 64 (ex)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (IP + IL)) xs9 (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros until mm. intros INV FRM PF HIP Hex.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe8c0c%Z => first [ eapply evt_eq; [| eapply (P2 fcb_808 IP IL FPT FL ex 0%Z c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia | unfold FCB_EN_MAX in *; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_6b8 : forall (IP IL FPT FL ex e : Z) c0 c8 c16 c24 c32 c48 xt1 xa0 xa1 xa2 xa3 xa4 xa5 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> (-2147483648 <= ex <= 0)%Z -> (FIRST <= e <= LAST)%Z ->
    evt bsegs Q (FCS E 0xe8abc (Z_to_bv 64 (46)) (Z_to_bv 64 (IL + FL)) xt1 (Z_to_bv 64 (53)) (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (FL)) (Z_to_bv 64 (ex)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) (Z_to_bv 64 (OUT)) (Z_to_bv 64 (IP + IL)) xs9 (Z_to_bv 64 (e)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros until mm. intros INV FRM PF HIP Hex He.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0xe8b9c%Z => first [ eapply evt_eq; [| eapply (fcb_798 IP IL FPT FL ex c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia] | fail 100 "cut 798" ]
      | 0xe8afc%Z => first [ eapply evt_eq; [| eapply (fcb_L4 (Z.to_nat LAST) IP IL FPT FL ex 0%Z e c0 c8 c16 c24 c32 c48)];
                             [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia | unfold FCB_EN_MAX; lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_624 : forall (IP IL FPT FL ex e : Z) c0 c8 c16 c24 c32 c48 xt1 xa0 xa1 xa2 xa3 xa4 xa5 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> (-2147483648 <= ex <= 0)%Z -> (FIRST <= e <= LAST)%Z ->
    evt bsegs Q (FCS E 0xe8a28 (Z_to_bv 64 (46)) (Z_to_bv 64 (IL + FL)) xt1 (Z_to_bv 64 (53)) (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (FL)) (Z_to_bv 64 (ex)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) (Z_to_bv 64 (OUT)) (Z_to_bv 64 (IP + IL)) xs9 (Z_to_bv 64 (e)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros until mm. intros INV FRM PF HIP Hex He.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0xe8abc%Z => first [ eapply evt_eq; [| eapply (fcb_6b8 IP IL FPT FL ex _ c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_5e4 : forall (IP IL FPT FL ex p : Z) c0 c8 c16 c24 c32 c48 xt1 xa0 xa1 xa2 xa3 xa4 xa5 xs7 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> (-2147483648 <= ex <= 0)%Z -> (FIRST <= p < LAST)%Z ->
    evt bsegs Q (FCS E 0xe89e8 (Z_to_bv 64 (46)) (Z_to_bv 64 (IL + FL)) xt1 (Z_to_bv 64 (53)) (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (FL)) (Z_to_bv 64 (ex)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 (p)) (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros until mm. intros INV FRM PF HIP Hex Hp.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0xe8a28%Z => first [ eapply evt_eq; [| eapply (fcb_624 IP IL FPT FL ex _ c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_56c : forall (IP IL FPT FL ex p : Z) c0 c8 c16 c24 c32 c48 xt1 xa0 xa1 xa2 xa3 xa4 xa5 xs7 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> (-2147483648 <= ex <= 0)%Z -> (FIRST <= p <= LAST)%Z ->
    evt bsegs Q (FCS E 0xe8970 (Z_to_bv 64 (46)) (Z_to_bv 64 (IL + FL)) xt1 (Z_to_bv 64 (53)) (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (FL)) (Z_to_bv 64 (ex)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 (p)) (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros until mm. intros INV FRM PF HIP Hex Hp.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0xe8a80%Z => first [ eapply evt_eq; [| eapply (fcb_67c IP IL FPT FL ex c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia] | fail 100 "cut 67c" ]
      | 0xe89e8%Z => first [ eapply evt_eq; [| eapply (fcb_5e4 IP IL FPT FL ex p c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End FCBPP3.
