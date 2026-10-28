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
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_pdefs Sj_num_fc_tail Sj_num_fc_k14 Sj_num_fc_pp1.
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

Definition FCB_EN_MAX : Z := 2684354559.

Section FCBPP2.
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
  Notation P1 L := (L E OK Q K14) (only parsing).

  Lemma fcb_904 : forall (q IP IL FPT FL : Z) c0 c8 c16 c24 c32 c48 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> (-9223372036854775808 <= q < 9223372036854775808)%Z -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z ->
    evt bsegs Q (FCS E 0xf7a6c xra xt0 xt1 xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (FL)) (Z_to_bv 64 (q)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 xs8 xs9 (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros until mm. intros INV FRM Hq PF HIP.
    kstep. kstep.
    eapply evt_eq; [| eapply (P1 fcb_9d8 q IP IL FPT FL 0%Z c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | lia | exact PF | exact HIP | lia |].
    intros C. exfalso. apply C. reflexivity.
  Qed.

  Lemma fcb_9c0 : forall (d en IP IL FPT FL : Z) c0 c8 c16 c24 c32 c48 xra xt0 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> (-2147483648 <= d <= 2147483648)%Z -> (- FCB_EN_MAX <= en <= FCB_EN_MAX)%Z -> (1 <= bv_unsigned xa2 <= 18446744073709551614)%Z ->
    evt bsegs Q (FCS E 0xf7b28 xra xt0 (Z_to_bv 64 (en)) xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) (Z_to_bv 64 (d)) xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (FL)) xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 xs8 xs9 (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros until mm. intros INV FRM PF HIP Hd Hen HW. unfold FCB_EN_MAX in Hen.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xf8cc0%Z => u_trap_b pc
      | 0xf7b40%Z => first [ eapply evt_eq; [| eapply (P1 fcb_9d8 (d + en)%Z IP IL FPT FL 1%Z c0 c8 c16 c24 c32 c48)];
                             [num_st_eq | exact INV | assumption | lia | exact PF | exact HIP | lia | intros _; exact HW] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_L7 : forall (f : nat) (IP IL FPT FL en z k w : Z) c0 c8 c16 c24 c32 c48 xra xa1 xa4 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> sp_nz E IP IL FPT FL z -> (- FCB_EN_MAX <= en <= FCB_EN_MAX)%Z -> (FPT <> 0)%Z -> (0 <= k < FL)%Z -> (0 <= w <= 999999999999999999)%Z -> (1 <= w \/ FPT + k <= z)%Z -> (FL - k <= Z.of_nat f)%Z ->
    evt bsegs Q (FCS E 0xf7abc xra (Z_to_bv 64 (10)) (Z_to_bv 64 (en)) (Z_to_bv 64 (FPT + k)) (q_sp E) (Z_to_bv 64 (q_spq E)) (Z_to_bv 64 (FPT + k)) xa1 (Z_to_bv 64 (w)) (Z_to_bv 64 (999999999999999999)) xa4 (Z_to_bv 64 (-1)) (Z_to_bv 64 (FL)) (Z_to_bv 64 (FL - 1 - k)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 xs8 xs9 (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM PF HIP NZ Hen HF Hk Hw Hz Hf; [exfalso; lia|].
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    pose proof PF as ((P1a & P2a & P3a) & G1 & [[PA PB] | [(PA & PB & PC & PD) G2]]); [exfalso; lia|].
    pose proof (G2 (FPT + k)%Z ltac:(lia)) as Gk. pose proof (sp_tb_range E (FPT + k)) as Rk.
    destruct NZ as [NZ1 NZ2]. pose proof NZ1 as NZ1'.
    unfold sp_tb in Gk, Rk.
    assert (NZk : (z = FPT + k -> 49 <= bv_unsigned (nth (Z.to_nat (FPT + k - A)) (q_txt E) (Z_to_bv 8 0)))%Z) by (intros ->; exact NZ1').
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xf8cc0%Z => u_trap_b pc
      | 0xf7b28%Z => first [ eapply evt_eq; [| eapply (fcb_9c0 (FPT - (FPT + k + 1))%Z en IP IL FPT FL c0 c8 c16 c24 c32 c48)];
                             [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia | exact Hen |];
                             rewrite unsigned_lit by lia; destruct (Z.eq_dec z (FPT + k)); lia
                           | fail 100 "cut" pc ]
      | 0xf7abc%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT FL en z (k + 1)%Z (w * 10 + bv_unsigned (nth (Z.to_nat (FPT + k - A)) (q_txt E) (Z_to_bv 8 0)) - 48)%Z c0 c8 c16 c24 c32 c48)];
                             [num_st_eq | exact INV | assumption | exact PF | exact HIP | split; assumption | exact Hen | lia | lia | lia
                             | destruct (Z.eq_dec z (FPT + k)); lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_90c : forall (IP IL FPT FL en z w : Z) c0 c8 c16 c24 c32 c48 xra xt0 xt2 xa0 xa1 xa3 xa4 xa5 xa7 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> sp_nz E IP IL FPT FL z -> (- FCB_EN_MAX <= en <= FCB_EN_MAX)%Z -> (0 <= w <= 999999999999999999)%Z -> (1 <= w \/ IP + IL <= z)%Z ->
    evt bsegs Q (FCS E 0xf7a74 xra xt0 (Z_to_bv 64 (en)) xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 (Z_to_bv 64 (w)) xa3 xa4 xa5 (Z_to_bv 64 (FL)) xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 xs8 xs9 (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros until mm. intros INV FRM PF HIP NZ Hen Hw Hz.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    pose proof PF as ((P1a & P2a & P3a) & G1 & PFR). destruct NZ as [NZ1 NZ2]. pose proof NZ1 as NZ1'.
    destruct PFR as [[-> ->] | [(PA & PB & PC & PD) G2]].
    - kwalk ltac:(fun pc => lazymatch pc with
        | 0xf8cc0%Z => u_trap_b pc
        | 0xf7b28%Z => first [ eapply evt_eq; [| eapply (fcb_9c0 0%Z en IP IL 0%Z 0%Z c0 c8 c16 c24 c32 c48)];
                               [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia | exact Hen | rewrite unsigned_lit by lia; lia]
                             | fail 100 "cut" pc ]
        end).
    - kwalk ltac:(fun pc => lazymatch pc with
        | 0xf8cc0%Z => u_trap_b pc
        | 0xf7b28%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0xf7abc%Z => first [ eapply evt_eq; [| eapply (fcb_L7 (Z.to_nat FL) IP IL FPT FL en z 0%Z w c0 c8 c16 c24 c32 c48)];
                               [num_st_eq | exact INV | assumption | exact PF | exact HIP | split; assumption | exact Hen | lia | lia | lia | lia | lia]
                             | fail 100 "cut" pc ]
        end).
  Qed.

End FCBPP2.
