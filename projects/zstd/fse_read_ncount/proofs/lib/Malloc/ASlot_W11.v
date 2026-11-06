(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import Malloc_fp MallocKit_A2 Malloc_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocKit_A3 ASlot_W1.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma small_cnt_range sc i : 0 <= sc < 9 -> 0 <= i < 3 -> 4 <= small_cnt sc i <= 31.
Proof.
intros Hsc Hi.
assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). destruct Hs as (n & -> & Hn).
assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). destruct Hi' as (k & -> & Hk).
unfold small_cnt. rewrite !Nat2Z.id.
do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [cbn [nth small_cnt_tab]; lia|]); lia |]). lia.
Qed.
Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.
End HALVE.
#[using="Type"] Lemma med_cnt_range i : 0 <= i < 4 -> 20 <= med_cnt i <= 32 /\ med_cnt i mod 4 = 0.
Proof.
intros Hi. Local Ltac2 Set LiaHints.tbl := fun () => "0050=15680004686.318040671932.238099106492.244038689468.258150950588.2000004005006007008S2HiSSSS".
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
destruct C as [->|[->|[->| ->]]]; [change (med_cnt 0) with 28| change (med_cnt 1) with 24| change (med_cnt 2) with 20| change (med_cnt 3) with 32]; (split; [lia| reflexivity]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma halve_even_range F : forall cnt u, 1 <= cnt -> 1 <= halve_even F cnt u <= cnt.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>42612348361.1548769709624.1459814634076.7 59816653630.4 6757834505.7  00000;00C00G00K00LS2Hc1E1H2H0S2Hc1E1HS2HcS2HcS".
induction F as [|F IH]; intros cnt u Hc; cbn [halve_even]; [lia|].
destruct (Z.even cnt && (u <? 4 * cnt)) eqn:E; [|lia].
apply andb_prop in E. destruct E as [E _]. rewrite even_of_land1 in E. apply Z.eqb_eq in E. rewrite land1_mod2 in E.
rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
pose proof (IH (cnt / 2) u ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma halve_big_range F : forall cnt sz, 0 <= cnt -> 0 <= halve_big F cnt sz <= cnt.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>39170548780.1344174797218.4 44174797218.6 61448771183.146755913323.6  00000900=00A00M00NS2Hc1H2H0S2HcS2HcS2Hc1H2H02H1S".
induction F as [|F IH]; intros cnt sz Hc; cbn [halve_big]; [lia|].
destruct (_ <=? _); [|lia]. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
pose proof (IH (cnt / 2) sz ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma land3_range x : 0 <= Z.land x 3 <= 3.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0010=29782099606.2000001S".
split; [apply Z.land_nonneg; right; lia|].
apply Z.ldiff_le; [lia|]. apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
destruct (Z.testbit x n), (Z.testbit 3 n); reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.
End COUNT.
Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.
#[using="C0"] Lemma cnt1_range : 0 <= cnt1 <= 32.
Proof. unfold cnt1. destruct (_ && _); lia. Qed.
End CNT2.
End CANSEC1.
