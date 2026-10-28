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
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_pdefs Sj_num_fc_tail Sj_num_fc_k14 Sj_num_fc_pp1 Sj_num_fc_pp2 Sj_num_fc_pp2b.
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

Section FCBPP2C.
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

  Notation P2 L := (L E OK PV Q K14) (only parsing).

  Notation cs IL FL d := (Z.min d IL + Z.max 0 (Z.min (d - IL - 1) FL))%Z.
  Lemma fcb_L5 : forall (f : nat) (IP IL FPT FL q en c cnt : Z) c0 c8 c16 c24 c32 c48 xa1 xa2 xa4 xs7 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> (-9223372036854775808 <= q < 9223372036854775808)%Z -> (- FCB_EN_MAX <= en <= FCB_EN_MAX)%Z -> (IP <= c < LAST)%Z -> (IL + FL - (c - IP) <= cnt <= IL + FL - cs IL FL (c - IP))%Z -> (LAST - c <= Z.of_nat f)%Z ->
    evt bsegs Q (FCS E 0xe88a4 (Z_to_bv 64 (46)) (Z_to_bv 64 (cnt)) (Z_to_bv 64 (en)) (Z_to_bv 64 (c)) (q_sp E) (Z_to_bv 64 (q_spq E)) (Z_to_bv 64 (c)) xa1 xa2 (Z_to_bv 64 (48)) xa4 (Z_to_bv 64 (-1)) (Z_to_bv 64 (FL)) (Z_to_bv 64 (q)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (IP + IL)) xs9 (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM PF HIP Hq Hen Hc Hcnt Hf; [exfalso; lia|].
    hide Hcnt.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    pose proof PF as ((P1a & P2a & P3a) & G1 & PFR).
    pose proof (sp_tb_range E c) as Rc.
    assert (FR0 : (FPT = 0 -> FL = 0)%Z) by (destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia).
    assert (FR1 : (FPT <> 0 -> FPT = IP + IL + 1 /\ 1 <= FL /\ FPT + FL <= LAST)%Z) by (destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia).
    assert (S1 : (IP <= c < IP + IL -> 48 <= sp_tb E c)%Z) by (intros X; apply G1; lia).
    assert (S2 : (FPT <> 0 -> FPT <= c < FPT + FL -> 48 <= sp_tb E c)%Z).
    { intros X Y. destruct PFR as [[? ?] | [_ G2]]; [lia | apply G2; lia]. }
    assert (D1 : (FPT <> 0 -> c = IP + IL -> sp_tb E c = 46)%Z).
    { intros X ->. destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; [lia | assumption]. }
    unfold sp_tb in Rc, S1, S2, D1.
    assert (FLRG : (0 <= FL < 2147483648)%Z) by lia.
    unfold hidden in Hcnt. destruct Hcnt as [Hlo Hhi]. assert (Hhi' : (cnt <= IL + FL)%Z) by (clear - Hhi FLRG P2a Hc; lia).

    hide Hhi. hide S1. hide S2. hide D1. hide FR0. hide FR1. clear PFR.
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9bd8%Z => u_trap_b pc
      | 0xe8984%Z => first [ eapply evt_eq; [| eapply (P2 fcb_904 q IP IL FPT FL c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | lia | exact PF | exact HIP] | fail 100 "cut" pc ]
      | 0xe8900%Z => first [ reveal; assert (SPAN : (IP <= c < IP + IL \/ (FPT <> 0 /\ FPT <= c < FPT + FL))%Z) by lia;
                             eapply evt_eq; [| eapply (P2 fcb_880 IP IL FPT FL en c c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | exact PF | exact HIP | | exact Hen];
                             split; [unfold sp_tb; lia | exact SPAN]
                           | fail 100 "cut" pc ]
      | 0xe88a4%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT FL q en (c + 1)%Z _ c0 c8 c16 c24 c32 c48)];
                             [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia | exact Hen | lia | reveal; lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_808 : forall (IP IL FPT FL q en : Z) c0 c8 c16 c24 c32 c48 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xs7 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> (-9223372036854775808 <= q < 9223372036854775808)%Z -> (- FCB_EN_MAX <= en <= FCB_EN_MAX)%Z ->
    evt bsegs Q (FCS E 0xe8888 (Z_to_bv 64 (46)) (Z_to_bv 64 (IL + FL)) (Z_to_bv 64 (en)) xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (FL)) (Z_to_bv 64 (q)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (IP + IL)) xs9 (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14.
    intros until mm. intros INV FRM PF HIP Hq Hen.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    pose proof PF as ((P1a & P2a & P3a) & G1 & PFR).
    assert (FR0 : (FPT = 0 -> FL = 0)%Z) by (destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia).
    assert (FR1 : (FPT <> 0 -> FPT = IP + IL + 1 /\ 1 <= FL /\ FPT + FL <= LAST)%Z) by (destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9bd8%Z => u_trap_b pc
      | 0xe8984%Z => first [ eapply evt_eq; [| eapply (P2 fcb_904 q IP IL FPT FL c0 c8 c16 c24 c32 c48)]; [num_st_eq | exact INV | assumption | lia | exact PF | exact HIP] | fail 100 "cut" pc ]
      | 0xe8900%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0xe88a4%Z => first [ eapply evt_eq; [| eapply (fcb_L5 (Z.to_nat LAST) IP IL FPT FL q en IP (IL + FL)%Z c0 c8 c16 c24 c32 c48)];
                             [num_st_eq | exact INV | assumption | exact PF | exact HIP | lia | exact Hen | lia | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

End FCBPP2C.
