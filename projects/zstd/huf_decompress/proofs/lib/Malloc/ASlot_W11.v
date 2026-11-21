(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (small_cnt_range, med_cnt_range, halve_even_range and 4 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2 Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3 ASlot_W1 ASlot_W10.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W11 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init9Datatypes3nat02C47Corelib4Init5Peano2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc9small_cntC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib5Lists7ListDef3nthC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith4Znat5Nat2Z2idC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec6Malloc=small_cnt_tabC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6Malloc7med_cntC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc:halve_evenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4evenC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6shiftrC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib6Malloc<MallocKit_A3=even_of_land1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib6Malloc<MallocKit_A3:land1_mod2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init9Datatypes7nat_indI47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc9halve_bigC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;land_nonnegK47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z8ldiff_leC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C59OSSVerify5KrLib4Spec6Malloc>small_cnt_pickC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W11?small_cnt_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegc59OSSVerify5KrLib6Malloc9ASlot_W11;land3_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W11=med_cnt_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W11@halve_even_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W11?halve_big_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition SMALL_CNT : Z := 0x18150.

Lemma small_cnt_range sc i : 0 <= sc < 9 -> 0 <= i < 3 -> 4 <= small_cnt sc i <= 31.
Proof.
  intros Hsc Hi.
  assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). destruct Hs as (n & -> & Hn).
  assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). destruct Hi' as (k & -> & Hk).
  unfold small_cnt. rewrite !Nat2Z.id.
  do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [cbn [nth small_cnt_tab]; lia|]); lia |]). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

(* [comment removed for export] *)
Definition cnt_regs (ra sp gp tp t0 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 (wz size) t2 s0 s1 (wz 4096) (Z_to_bv 64 8) (wz usage) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
End HALVE.

Lemma med_cnt_range i : 0 <= i < 4 -> 20 <= med_cnt i <= 32 /\ med_cnt i mod 4 = 0.
Proof.
  intros Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct C as [->|[->|[->| ->]]]; [change (med_cnt 0) with 28| change (med_cnt 1) with 24| change (med_cnt 2) with 20| change (med_cnt 3) with 32]; (split; [lia| reflexivity]).
Qed.

Lemma halve_even_range F : forall cnt u, 1 <= cnt -> 1 <= halve_even F cnt u <= cnt.
Proof.
  induction F as [|F IH]; intros cnt u Hc; cbn [halve_even]; [lia|].
  destruct (Z.even cnt && (u <? 4 * cnt)) eqn:E; [|lia].
  apply andb_prop in E. destruct E as [E _]. rewrite even_of_land1 in E. apply Z.eqb_eq in E. rewrite land1_mod2 in E.
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  pose proof (IH (cnt / 2) u ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed.

Lemma halve_big_range F : forall cnt sz, 0 <= cnt -> 0 <= halve_big F cnt sz <= cnt.
Proof.
  induction F as [|F IH]; intros cnt sz Hc; cbn [halve_big]; [lia|].
  destruct (_ <=? _); [|lia]. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  pose proof (IH (cnt / 2) sz ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed.

Lemma land3_range x : 0 <= Z.land x 3 <= 3.
Proof.
  split; [apply Z.land_nonneg; right; lia|].
  apply Z.ldiff_le; [lia|]. apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
  destruct (Z.testbit x n), (Z.testbit 3 n); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.

Lemma cnt0_range : 0 <= cnt0 <= 32.
Proof.
  unfold cnt0. destruct (Z.ltb_spec sc 9).
  - unfold small_cnt_pick. pose proof (small_cnt_range sc 0). pose proof (small_cnt_range sc 1). pose proof (small_cnt_range sc 2).
    destruct (negb _); [lia|]. destruct (negb _); lia.
  - pose proof (med_cnt_range (Z.land sc 3) ltac:(pose proof (land3_range sc); lia)) as [X _].
    pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)).
    pose proof (halve_big_range 8 (halve_even 8 (med_cnt (Z.land sc 3)) u) size ltac:(lia)). lia.
Qed.
End COUNT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.

Lemma cnt1_range : 0 <= cnt1 <= 32.
Proof. unfold cnt1. destruct (_ && _); lia. Qed.
End CNT2.


End CANSEC1.
