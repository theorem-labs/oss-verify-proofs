(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumSwar SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_kitw Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_pdefs Sj_num_sp_pns Sj_num_sp_acc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_w.

Section SPUACC2.
  Variable E : spuenv.
  Hypothesis OK : spu_ok E.
  Hypothesis HSET : spu_memset_stmt.
  Hypothesis HPM : spu_pm_stmt.
  Hypothesis HPDC : spu_pdc_stmt.
  Hypothesis HNDC : spu_ndc_stmt.
  Notation A := (q_A E).
  Notation LAST := (q_LAST E).
  Notation OUT := (q_OUT E).

  Notation LS pc IP IL FPT FL q en wv c0 xra xt2 xs0 xa0 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt4 xF xfc mm :=
    (SPS E pc xra (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 IL) xt2 xs0 (Z_to_bv 64 q) xa0 (Z_to_bv 64 LAST) (Z_to_bv 64 FPT) (Z_to_bv 64 en) wv c0 (Z_to_bv 64 IP) (Z_to_bv 64 46)
         xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 OUT) xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) xt4 (Z_to_bv 64 48) (Z_to_bv 64 (-1)) xF xfc mm).

  Notation cs IL FL d := (Z.min d IL + Z.max 0 (Z.min (d - IL - 1) FL))%Z.
  Lemma spu_L5 : forall (f : nat) (IP IL FPT FL q en c cnt : Z) (wv c0 spl : word) xra xt2 xa0 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (-9223372036854775808 <= q < 9223372036854775808)%Z -> (- EN_MAX <= en <= EN_MAX)%Z ->
    (IP <= c < LAST)%Z -> (IL + FL - (c - IP) <= cnt <= IL + FL - cs IL FL (c - IP))%Z -> (LAST - c <= Z.of_nat f)%Z ->
    evt usegs (spu_post E) (LS 0x5735c IP IL FPT FL q en wv c0 xra xt2 (Z_to_bv 64 c) xa0 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 (Z_to_bv 64 cnt) xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM PF Hq Hen Hc Hcnt Hf; [exfalso; lia|].
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    pose proof PF as ((P1 & P2 & P3) & G1 & PFR).
    pose proof (sp_tb_range E c) as Rc.
    assert (FR0 : (FPT = 0 -> FL = 0)%Z) by (destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia).
    assert (FR1 : (FPT <> 0 -> FPT = IP + IL + 1 /\ 1 <= FL /\ FPT + FL <= LAST)%Z) by (destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia).
    assert (S1 : (IP <= c < IP + IL -> 48 <= sp_tb E c)%Z) by (intros X; apply G1; lia).
    assert (S2 : (FPT <> 0 -> FPT <= c < FPT + FL -> 48 <= sp_tb E c)%Z).
    { intros X Y. destruct PFR as [[? ?] | [_ G2]]; [lia | apply G2; lia]. }
    assert (D1 : (FPT <> 0 -> c = IP + IL -> sp_tb E c = 46)%Z).
    { intros X ->. destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; [lia | assumption]. }
    unfold sp_tb in Rc, S1, S2, D1.
    destruct Hcnt as [Hlo Hhi]. assert (Hhi' : (cnt <= IL + FL)%Z) by lia. assert (FLR : (0 <= FL < 2147483648)%Z) by lia.

    hide Hhi. hide S1. hide S2. hide D1. hide FR0. hide FR1. clear PFR.
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x58158%Z => u_trap_b pc
      | 0x573f8%Z => first [ eapply evt_eq; [| eapply (spu_400 E OK HSET HPM HPDC HNDC q IP IL FPT FL wv c0 spl)]; [num_st_eq | exact INV | assumption | lia | exact PF] | fail 100 "cut" pc ]
      | 0x5738c%Z => first [ reveal; assert (SPAN : (IP <= c < IP + IL \/ (FPT <> 0 /\ FPT <= c < FPT + FL))%Z) by lia;
                             eapply evt_eq; [| eapply (spu_394 E OK HSET HPM HPDC HNDC IP IL FPT FL en c c0 spl)]; [num_st_eq | exact INV | assumption | exact PF | | exact Hen];
                             split; [unfold sp_tb; lia | exact SPAN]
                           | fail 100 "cut" pc ]
      | 0x5735c%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT FL q en (c + 1)%Z _ wv c0 spl)];
                             [num_st_eq | exact INV | assumption | exact PF | lia | exact Hen | lia | reveal; lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_354 : forall (IP IL FPT FL q en : Z) (wv c0 spl : word) xra xt2 xs0 xa0 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (-9223372036854775808 <= q < 9223372036854775808)%Z -> (- EN_MAX <= en <= EN_MAX)%Z ->
    evt usegs (spu_post E) (SPS E 0x5734c xra (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 IL) xt2 xs0 (Z_to_bv 64 q) xa0 (Z_to_bv 64 LAST) (Z_to_bv 64 FPT) (Z_to_bv 64 en) wv c0
                               (Z_to_bv 64 IP) (Z_to_bv 64 46) xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 OUT) xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) (Z_to_bv 64 (IL + FL)) xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM PF Hq Hen.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    pose proof PF as ((P1 & P2 & P3) & G1 & PFR).
    assert (FR0 : (FPT = 0 -> FL = 0)%Z) by (destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia).
    assert (FR1 : (FPT <> 0 -> FPT = IP + IL + 1 /\ 1 <= FL /\ FPT + FL <= LAST)%Z) by (destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x58158%Z => u_trap_b pc
      | 0x5738c%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x5735c%Z => first [ eapply evt_eq; [| eapply (spu_L5 (Z.to_nat LAST) IP IL FPT FL q en IP (IL + FL)%Z wv c0 spl)];
                             [num_st_eq | exact INV | assumption | exact PF | lia | exact Hen | lia | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.
End SPUACC2.
