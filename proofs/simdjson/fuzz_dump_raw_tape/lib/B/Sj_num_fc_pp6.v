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
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_pdefs Sj_num_fc_tail Sj_num_fc_k14 Sj_num_fc_pp1 Sj_num_fc_pp2 Sj_num_fc_pp2b Sj_num_fc_pp2c Sj_num_fc_pp3 Sj_num_fc_pp4 Sj_num_fc_pp5 Sj_num_fc_pp5b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_w.

Local Ltac num_abstract_data ::= num_abstract_data_u.

Section FCBPP6.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Hypothesis PV : fcb_prov E.
  Variable Q : machine_state -> Prop.
  Hypothesis K14 : fcb_kf14 E Q.
  Hypothesis KERR1 : fcb_kerr1 E Q.
  Notation A := (q_A E).
  Notation FIRST := (q_FIRST E).
  Notation LAST := (q_LAST E).
  Notation OUT := (q_OUT E).
  Notation f := (q_f E).
  Notation P4 L := (L E OK PV Q K14 KERR1) (only parsing).
  Ltac cut_err INV FRM := first [ eapply evt_eq; [| eapply KERR1]; [num_st_eq | unfold FCB_ERR1; cbn [In]; repeat (first [left; reflexivity | right]) | exact INV | exact FRM | reflexivity] | fail 100 "cut err" ].

  Lemma fcb_d90 : forall (IP IL : Z) c0 c8 c16 c24 c32 c40 c48 c56 xt1 xa0 xa1 xa2 xa3 xa4 xa6 xa7 xs7 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 c40 c48 c56 -> frm0 xfc -> (FIRST <= IP)%Z -> (1 <= IL)%Z -> (IP + IL <= LAST)%Z -> sp_ge48 E IP (IP + IL) ->
    evt bsegs Q (FCS E 0xe8194 (Z_to_bv 64 (46)) (Z_to_bv 64 (IL)) xt1 (Z_to_bv 64 (53)) (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 (IP / 8)) xa6 xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (IP + IL)) xs9 (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14 KERR1.
    intros until mm. intros INV FRM HIP H2 H3 G1.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0x7f338%Z => cut_err INV FRM
      | 0xe83c0%Z => first [ eapply evt_eq; [| eapply (P4 fcb_fbc IP IL c0 c8 c16 c24 c32 c40 c48 c56)]; [num_st_eq | exact INV | assumption | exact HIP | lia | lia | exact G1] | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac int_cuts INV FRM HIP IP :=
    fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0x7f338%Z => cut_err INV FRM
      | 0xe8194%Z => first [ eapply evt_eq; [| eapply (fcb_d90 IP _ _ _ _ _ _ _ _ _)]; [num_st_eq | exact INV | assumption | exact HIP | lia | lia |];
                             first [ assumption
                                   | lazymatch goal with G : sp_ge48 E IP ?pe |- sp_ge48 E IP ?pe' => replace pe' with pe by lia; exact G end ]
                           | fail 100 "cut" pc ]
      end.

  Lemma fcb_d88 : forall (IP pe : Z) c0 c8 c16 c24 c32 c40 c48 c56 xt0 xt1 xa0 xa1 xa2 xa3 xa4 xa6 xa7 xs7 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 c40 c48 c56 -> frm0 xfc -> (FIRST <= IP)%Z -> (IP <= pe)%Z -> (pe <= LAST)%Z -> sp_ge48 E IP pe ->
    evt bsegs Q (FCS E 0xe818c (Z_to_bv 64 (46)) xt0 xt1 (Z_to_bv 64 (53)) (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 (IP / 8)) xa6 xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (pe)) xs9 (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14 KERR1.
    intros until mm. intros INV FRM HIP H1 H2 G1.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    kwalk ltac:(int_cuts INV FRM HIP IP).
  Qed.

  Lemma fcb_L1 : forall (f : nat) (IP pe : Z) c0 c8 c16 c24 c32 c40 c48 c56 xt0 xt1 xa1 xa2 xa7 xs7 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 c40 c48 c56 -> frm0 xfc -> (FIRST <= IP)%Z -> (IP < pe)%Z -> (pe <= LAST)%Z -> sp_ge48 E IP pe -> (LAST - pe <= Z.of_nat f)%Z ->
    evt bsegs Q (FCS E 0xe7ee4 (Z_to_bv 64 (46)) xt0 xt1 (Z_to_bv 64 (53)) (q_sp E) (Z_to_bv 64 (q_spq E)) (Z_to_bv 64 (pe)) xa1 xa2 (Z_to_bv 64 (2)) (Z_to_bv 64 (10)) (Z_to_bv 64 (IP / 8)) (Z_to_bv 64 (9)) xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (pe)) xs9 (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14 KERR1.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM HIP H1 H2 G1 Hf.
    {   assert (pe = LAST) by lia. subst pe.
      pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
      kwalk ltac:(int_cuts INV FRM HIP IP). }
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    pose proof (sp_tb_range E pe) as Rp. unfold sp_tb in Rp.
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0x7f338%Z => first [ exfalso; lia | cut_err INV FRM ]
      | 0xe8194%Z => first [ eapply evt_eq; [| eapply (fcb_d90 IP _ c0 c8 c16 c24 c32 c40 c48 c56)]; [num_st_eq | exact INV | assumption | exact HIP | lia | lia |];
                             lazymatch goal with G : sp_ge48 E IP ?pe0 |- sp_ge48 E IP ?pe' => replace pe' with pe0 by lia; exact G end
                           | fail 100 "cut" pc ]
      | 0xe818c%Z => first [ eapply evt_eq; [| eapply (fcb_d88 IP pe c0 c8 c16 c24 c32 c40 c48 c56)]; [num_st_eq | exact INV | assumption | exact HIP | lia | lia | exact G1] | fail 100 "cut" pc ]
      | 0xe7ee4%Z => first [ eapply evt_eq; [| eapply (IH IP (pe + 1)%Z c0 c8 c16 c24 c32 c40 c48 c56)]; [num_st_eq | exact INV | assumption | exact HIP | lia | lia | | lia];
                             apply sp_ge48_snoc; [exact G1 | unfold sp_tb; lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac ge48_peel IP :=
    let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
    assert (C : (i = IP \/ i = IP + 1 \/ i = IP + 2 \/ i = IP + 3 \/ i = IP + 4)%Z) by lia;
    destruct C as [-> | [-> | [-> | [-> | ->]]]]; unfold sp_tb; lia.

  Lemma fcb_970 : forall (IP : Z) c0 c8 c16 c24 c32 c40 c48 c56 xt0 xt1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 c40 c48 c56 -> frm0 xfc -> (FIRST <= IP < LAST)%Z ->
    evt bsegs Q (FCS E 0xe7d74 (Z_to_bv 64 (46)) xt0 xt1 (Z_to_bv 64 (53)) (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 xs8 xs9 (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14 KERR1.
    intros until mm. intros INV FRM H1.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    assert (HIP : (FIRST <= IP)%Z) by lia.
    pose proof (sp_tb_range E IP) as R0. pose proof (sp_tb_range E (IP + 1)) as R1. pose proof (sp_tb_range E (IP + 2)) as R2.
    pose proof (sp_tb_range E (IP + 3)) as R3. pose proof (sp_tb_range E (IP + 4)) as R4.
    unfold sp_tb in R0, R1, R2, R3, R4.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0xe818c%Z => first [ eapply evt_eq; [| eapply (fcb_d88 IP _ c0 c8 c16 c24 c32 c40 c48 c56)]; [num_st_eq | exact INV | assumption | exact HIP | lia | lia | first [ge48_peel IP | apply sp_ge48_nil]] | fail 100 "cut" pc ]
      | 0xe7ee4%Z => first [ eapply evt_eq; [| eapply (fcb_L1 (Z.to_nat LAST) IP (IP + 5)%Z c0 c8 c16 c24 c32 c40 c48 c56)]; [num_st_eq | exact INV | assumption | exact HIP | lia | lia | ge48_peel IP | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Theorem fcb_parse : forall xra xt0 xt1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 xF xfc mm c0 c8 c16 c24 c32 c40 c48 c56,
    FCPINV E mm c0 c8 c16 c24 c32 c40 c48 c56 -> frm0 xfc ->
    evt bsegs Q (FCB E 0xe7d0c xra xt0 xt1 (Z_to_bv 64 53) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 (q_FIRST E)) (Z_to_bv 64 (q_LAST E)) xs7
                     (Z_to_bv 64 1) (Z_to_bv 64 42949673006) (Z_to_bv 64 (q_OUT E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14 KERR1.
    intros until c56. intros INV FRM.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0x7f338%Z => cut_err INV FRM
      | 0xe7d74%Z => first [ eapply evt_eq; [| eapply (fcb_970 _ c0 c8 c16 c24 c32 c40 c48 c56)]; [num_st_eq | exact INV | assumption | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End FCBPP6.
