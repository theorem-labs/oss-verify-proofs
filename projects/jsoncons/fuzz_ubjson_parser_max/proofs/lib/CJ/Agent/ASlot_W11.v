(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2 Malloc_iface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_A3 ASlot_W1 ASlot_W10.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_W11 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."], [["1nat"; "2and"; "2eq"; "3Z"; "0F"; "4halve_big"; "4halve_even"; "4med_cnt"; "4small_cnt"; "5land"; "5le"; "5lt"; "5modulo"; "0cnt"; "0cnt0"; "0cnt1"]; ["0i"; "0sc"; "0sz"; "0u"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section SE.
Local Abbreviation SEC_T_small_cnt_range := (ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W11 "J'3'1&:zr2%3221&;+9%2241%8241+3%5271%;271+4&8r4r3%3221%@251+O%B231%D231p0:1p0>1pQ2H1pQ4I1")) (only parsing).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_small_cnt_range) 0%nat 0%nat).
Variable i : ltac:(sec_ty2 constr:(SEC_T_small_cnt_range) 1%nat 0%nat).
Lemma small_cnt_range : ltac:(sec_stmt2 constr:(SEC_T_small_cnt_range) 2%nat 0%nat).
Proof.
intros Hsc Hi.
assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). destruct Hs as (n & -> & Hn).
assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). destruct Hi' as (k & -> & Hk).
unfold small_cnt. rewrite !Nat2Z.id.
do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [cbn [nth small_cnt_tab]; lia|]); lia |]). lia.
Qed.
End SE.
Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.
Definition cnt_regs (ra sp gp tp t0 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
mkR ra sp gp tp t0 (wz size) t2 s0 s1 (wz 4096) (Z_to_bv 64 8) (wz usage) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
End HALVE.
Lemma med_cnt_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W11 "I'3'1&:zr1%3221&;+4%2241%8241+D&7r2%211%<241+Q0%>231%@231'2&<%127=%33E1B%E251p0>1pQ2H1").
Proof. intros i.
intros Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
destruct C as [->|[->|[->| ->]]]; [change (med_cnt 0) with 28| change (med_cnt 1) with 24| change (med_cnt 2) with 20| change (med_cnt 3) with 32]; (split; [lia| reflexivity]).
Qed.
Lemma halve_even_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W11 "B'0'3&:+1r2%3221'1&6r4r3%33216%9281%:223%7221p091pQ8>1pL?1p:A1").
Proof. intros F.
induction F as [|F IH]; intros cnt u Hc; cbn [halve_even]; [lia|].
destruct (Z.even cnt && (u <? 4 * cnt)) eqn:E; [|lia].
apply andb_prop in E. destruct E as [E _]. rewrite even_of_land1 in E. apply Z.eqb_eq in E. rewrite land1_mod2 in E.
rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
pose proof (IH (cnt / 2) u ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed.
Lemma halve_big_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W11 "B'0'3&:zr2%3221'1&5r4r3%33216%9281%:223%7221p091pQ6>1pL?1p:A1").
Proof. intros F.
induction F as [|F IH]; intros cnt sz Hc; cbn [halve_big]; [lia|].
destruct (_ <=? _); [|lia]. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
pose proof (IH (cnt / 2) sz ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed.
Lemma land3_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W11 "<'3'1&:z&9r1+3%3221%6251%7223%9221pQ:;1").
Proof. intros x.
split; [apply Z.land_nonneg; right; lia|].
apply Z.ldiff_le; [lia|]. apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
destruct (Z.testbit x n), (Z.testbit 3 n); reflexivity.
Qed.
Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.
Lemma cnt0_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W11 "8'1&:zv>%3221+Q0%5231%7231").
Proof.
unfold cnt0. destruct (Z.ltb_spec sc 9).
- unfold small_cnt_pick. pose proof (small_cnt_range sc 0). pose proof (small_cnt_range sc 1). pose proof (small_cnt_range sc 2).
destruct (negb _); [lia|]. destruct (negb _); lia.
- pose proof (med_cnt_range (Z.land sc 3) ltac:(pose proof (land3_range sc); lia)) as [X _].
pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)).
pose proof (halve_big_range 8 (halve_even 8 (med_cnt (Z.land sc 3)) u) size ltac:(lia)). lia.
Qed.
End COUNT.
Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.
Lemma cnt1_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W11 "8'1&:zv?%3221+Q0%5231%7231").
Proof. unfold cnt1. destruct (_ && _); lia. Qed.
End CNT2.
End CEIL_WRAP_1.
