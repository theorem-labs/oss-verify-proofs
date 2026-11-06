(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acache3 ASecFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From Stdlib Require NArith.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ASecSlog.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acache3 ASecFacts. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bwin (x i n : Z) : Prop := exists d, 0 <= d < n /\ Z.testbit x (i + d) = true.

Lemma bwin_step : forall y x n, 0 <= n -> (forall i, 0 <= i -> (Z.testbit y i = true <-> bwin x i n)) ->
  forall i, 0 <= i -> (Z.testbit (Z.lor y (Z.shiftr y n)) i = true <-> bwin x i (2 * n)).
Proof.
  intros y x n Hn H i Hi. rewrite Z.lor_spec, Z.shiftr_spec by lia. rewrite orb_true_iff, (H i Hi), (H (i + n) ltac:(lia)).
  unfold bwin. split.
  - intros [(d & Hd & B)|(d & Hd & B)]; [exists d; split; [lia| exact B] | exists (n + d); split; [lia| replace (i + (n + d)) with (i + n + d) by lia; exact B]].
  - intros (d & Hd & B). destruct (Z.lt_ge_cases d n) as [L|L].
    + left. exists d. split; [lia| exact B].
    + right. exists (d - n). split; [lia| replace (i + n + (d - n)) with (i + d) by lia; exact B].
Qed.

Lemma bwin_1 : forall x i, 0 <= i -> (Z.testbit x i = true <-> bwin x i 1).
Proof.
  intros x i Hi. unfold bwin. split.
  - intros B. exists 0. split; [lia| rewrite Z.add_0_r; exact B].
  - intros (d & Hd & B). replace d with 0 in B by lia. rewrite Z.add_0_r in B. exact B.
Qed.

Lemma bwin_log2 : forall x i, 0 < x < 2^32 -> 0 <= i -> (bwin x i 64 <-> i <= Z.log2 x).
Proof.
  intros x i Hx Hi. pose proof (Z.log2_nonneg x) as L0. assert (L1 : Z.log2 x < 32) by (apply Z.log2_lt_pow2; lia).
  unfold bwin. split.
  - intros (d & Hd & B). destruct (Z.le_gt_cases (i + d) (Z.log2 x)) as [L|L]; [lia|].
    rewrite Z.bits_above_log2 in B by lia. discriminate.
  - intros L. exists (Z.log2 x - i). split; [lia|]. replace (i + (Z.log2 x - i)) with (Z.log2 x) by lia. apply Z.bit_log2. lia.
Qed.

Lemma smear_ones : forall s, 0 < s < 2^32 ->
  (let x1 := Z.lor s (Z.shiftr s 1) in let x2 := Z.lor x1 (Z.shiftr x1 2) in let x3 := Z.lor x2 (Z.shiftr x2 4) in
   let x4 := Z.lor x3 (Z.shiftr x3 8) in let x5 := Z.lor x4 (Z.shiftr x4 16) in Z.lor x5 (Z.shiftr x5 32)) = Z.ones (Z.log2 s + 1).
Proof.
  intros s Hs. cbv zeta.
  pose proof (bwin_1 s) as W1.
  pose proof (bwin_step s s 1 ltac:(lia) W1) as W2. cbn [Z.mul] in W2.
  pose proof (bwin_step _ s 2 ltac:(lia) W2) as W4. cbn [Z.mul] in W4.
  pose proof (bwin_step _ s 4 ltac:(lia) W4) as W8. cbn [Z.mul] in W8.
  pose proof (bwin_step _ s 8 ltac:(lia) W8) as W16. cbn [Z.mul] in W16.
  pose proof (bwin_step _ s 16 ltac:(lia) W16) as W32. cbn [Z.mul] in W32.
  pose proof (bwin_step _ s 32 ltac:(lia) W32) as W64. cbn [Z.mul] in W64.
  change (2 * 32) with 64 in W64.
  apply Z.bits_inj'. intros i Hi. rewrite Z.testbit_ones by (pose proof (Z.log2_nonneg s); lia).
  apply eq_true_iff_eq. rewrite (W64 i Hi), (bwin_log2 s i Hs Hi). rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition slog_ok (j : Z) : bool :=
  let y := cb_sm (4096 * j) in let k := cb_clz y in (34 <=? k) && (k <=? 47) && (0 <=? y) && (y <? 18446744073709551616).
(* [comment removed for export] *)
Definition slog_ok_f (j : Z) : bool :=
  let y := cb_sm (4096 * j) in let k := cb_clz_f y in (34 <=? k) && (k <=? 47) && (0 <=? y) && (y <? 18446744073709551616).
#[using="Type"] Lemma slog_ok_f_eq : forall j, slog_ok j = slog_ok_f j.
Proof. intros j. unfold slog_ok, slog_ok_f. rewrite cb_clz_f_eq. reflexivity. Qed.
#[using="Type"] Lemma cb_sm_log : forall s, 0 < s < 2^32 -> cb_sm s = Z.lxor (Z.ones (Z.log2 s + 1)) 18446744073709551615.
Proof. intros s Hs. pose proof (smear_ones s Hs) as E. unfold cb_sm. cbv zeta in E |- *. rewrite E. reflexivity. Qed.
Definition slog_g (L : Z) : bool :=
  let y := Z.lxor (Z.ones (L + 1)) 18446744073709551615 in let k := cb_clz y in (34 <=? k) && (k <=? 47) && (0 <=? y) && (y <? 18446744073709551616).
#[using="Type"] Lemma slog_ok_g : forall j, 0 < j < 1048576 -> slog_ok j = slog_g (Z.log2 (4096 * j)).
Proof. intros j Hj. unfold slog_ok, slog_g. rewrite (cb_sm_log (4096 * j)) by lia. reflexivity. Qed.
Definition slog_t (L : Z) : bool := if (16 <=? L) && (L <=? 28) then true else slog_g L.
#[using="Type"] Lemma slog_t_eq : forall L, slog_t L = slog_g L.
Proof.
  intros L. unfold slog_t. destruct ((16 <=? L) && (L <=? 28)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  assert (C : L = 16 \/ L = 17 \/ L = 18 \/ L = 19 \/ L = 20 \/ L = 21 \/ L = 22 \/ L = 23 \/ L = 24 \/ L = 25 \/ L = 26 \/ L = 27 \/ L = 28) by lia.
  repeat destruct C as [C|C]; subst L; vm_compute; reflexivity.
Qed.
Definition slog_ok_h (j : Z) : bool := if (0 <? j) && (j <? 1048576) then slog_t (Z.log2 (4096 * j)) else slog_ok j.
#[using="Type"] Lemma slog_ok_h_eq : forall j, slog_ok j = slog_ok_h j.
Proof.
  intros j. unfold slog_ok_h. destruct ((0 <? j) && (j <? 1048576)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. rewrite slog_t_eq. apply slog_ok_g. lia.
Qed.
#[using="Type"] Lemma slog_ok_all : forallb_range slog_ok 18 (Z.to_nat (131060 - 18 + 1)) = true.
Proof. rewrite (forallb_range_ext slog_ok slog_ok_h slog_ok_h_eq). vm_cast_no_check (eq_refl true). Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Opaque cb_sm cb_clz.
Local Strategy expand [slog_ok].
#[using="Type"] Lemma slog_ok_sound : forall z, slog_ok z = true -> 0 <= cb_sm (4096 * z) < 2^64 /\ 34 <= cb_clz (cb_sm (4096 * z)) <= 47.
Proof.
  intros z Hz. unfold slog_ok in Hz. cbv zeta in Hz.
  rewrite !Bool.andb_true_iff in Hz. destruct Hz as [[[H1 H2] H3] H4].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
  change (2^64) with 18446744073709551616. repeat split; assumption.
Qed.

#[using="Type"] Lemma slog_range : forall z, 18 <= z <= 131060 ->
  0 <= cb_sm (4096 * z) < 2^64 /\ 34 <= cb_clz (cb_sm (4096 * z)) <= 47.
Proof.
  exact (range_by_compute (fun j => 0 <= cb_sm (4096 * j) < 2^64 /\ 34 <= cb_clz (cb_sm (4096 * j)) <= 47) slog_ok 18 131060 slog_ok_sound slog_ok_all).
Qed.

#[using="Type"] Lemma slog_facts : forall ms, 73728 <= ms <= 536821760 -> ms mod 4096 = 0 ->
  0 <= cb_sm ms < 2^64 /\ 34 <= cb_clz (cb_sm ms) <= 47.
Proof.
  intros ms R M.
  assert (E : ms = 4096 * (ms / 4096)) by (Z.div_mod_to_equations; lia). rewrite E.
  apply slog_range. Z.div_mod_to_equations; lia.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition slog_ok (j : Z) : bool :=
  let y := cb_sm (4096 * j) in let k := cb_clz y in (34 <=? k) && (k <=? 47) && (0 <=? y) && (y <? 18446744073709551616).
#[using="Type"] Lemma slog_ok_all : forallb_range slog_ok 18 (Z.to_nat (131060 - 18 + 1)) = true.
Proof.   (* [comment removed for export] *)
  assert (E1 : cb_sm = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.cb_sm) by reflexivity.
  assert (E2 : cb_clz = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.cb_clz) by reflexivity.
  assert (E : slog_ok = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.ASecSlog.slog_ok) by (unfold slog_ok, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.ASecSlog.slog_ok; rewrite E1, E2; reflexivity).
  assert (E0 : forallb_range = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.forallb_range) by reflexivity.   (* [comment removed for export] *)
  rewrite E0, E. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.ASecSlog.slog_ok_all.
Qed.

(* [comment removed for export] *)
Local Opaque cb_sm cb_clz.
Local Strategy expand [slog_ok].
#[using="Type"] Lemma slog_ok_sound : forall z, slog_ok z = true -> 0 <= cb_sm (4096 * z) < 2^64 /\ 34 <= cb_clz (cb_sm (4096 * z)) <= 47.
Proof.
  intros z Hz. unfold slog_ok in Hz. cbv zeta in Hz.
  rewrite !Bool.andb_true_iff in Hz. destruct Hz as [[[H1 H2] H3] H4].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
  change (2^64) with 18446744073709551616. repeat split; assumption.
Qed.

#[using="Type"] Lemma slog_range : forall z, 18 <= z <= 131060 ->
  0 <= cb_sm (4096 * z) < 2^64 /\ 34 <= cb_clz (cb_sm (4096 * z)) <= 47.
Proof.
  exact (range_by_compute (fun j => 0 <= cb_sm (4096 * j) < 2^64 /\ 34 <= cb_clz (cb_sm (4096 * j)) <= 47) slog_ok 18 131060 slog_ok_sound slog_ok_all).
Qed.

#[using="Type"] Lemma slog_facts : forall ms, 73728 <= ms <= 536821760 -> ms mod 4096 = 0 ->
  0 <= cb_sm ms < 2^64 /\ 34 <= cb_clz (cb_sm ms) <= 47.
Proof.
  intros ms R M.
  assert (E : ms = 4096 * (ms / 4096)) by (Z.div_mod_to_equations; lia). rewrite E.
  apply slog_range. Z.div_mod_to_equations; lia.
Qed.
End CANSEC1.
End TwB.
End ASecSlog.

(* [comment removed for export] *)
Module F_acache4.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acache3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition calloc_hit_gen__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 spacebeg)] ->      (* [comment removed for export] *)
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38388) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 34).
Variable t : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 35).
Variable size : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 36).
Variable c : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 37).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 38).
Variable spacebeg : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 39).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 40).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 41).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 42).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 43).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 44).
Variable idxw : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 45).
#[using="Type"] Lemma calloc_hit_gen__body : ltac:(let T := type of (fun (h : calloc_hit_gen__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t size c cnt spacebeg lo maxc csz stj chunks idxw) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (t, (size, (c, (cnt, (spacebeg, (lo, (maxc, (csz, (stj, (chunks, idxw)))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> -> -> SZ M8 HC SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RTLS RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF. (nd_pre CF 6%nat; intros C1 CS1 CS2 CS3 CSM CBG; nd_post).
  word_range sp SPR. word_range idxw IXR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.                                        (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].  (* [comment removed for export] *)
  do 2 step. step. if_lit.                          (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  1: eapply evtF_cut; [eapply (classblock_spec RNG); [lia | assumption | exact RIMG | exact RTLS] |].
  1: cbv beta; intros msB PB; (nd_pre PB 8%nat; intros a2b a4b a5b a6b a7b t0b t1b ndR1__; nd_post; revert ndR1__; intros ->); rewrite HC.
  2: do 2 zstep; rewrite <- (CSM ltac:(lia)); step.
  (* [comment removed for export] *)
  all: step.
  all: if_cases K3; zify_cond K3; [exfalso; lia|].
  all: step.
  all: step.
  all: if_cases K4; zify_cond K4; [exfalso; lia|].
  all: step.
  all: zstep.
  all: zstep.
  all: assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 2688) by lia.
  all: remember (t + 208 + c * 80) as R eqn:HR.
  all: lstep.
  all: step.
  all: if_cases K5; zify_cond K5; [exfalso; lia|].
  all: do 3 zstep.
  all: step.
  all: zstep.
  all: step.
  all: zstep.
  all: zstep.
  all: replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  all: pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
  all: step.
  all: clear RD.
  all: rewrite (zx32_small idxw) by lia.
  all: assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
  all: amo_stepA AMO.
  all: step.
  all: do 4 zstep.
  all: step.
  all: step.
  all: if_lit.
  all: do 8 step.
  all: release_frame FR ST (bv_unsigned sp).
  all: subst R.
  all: setreg 10 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw))
    ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; zeq).
  all: finish.
  all: eexists.
  all: exact STS.
Qed.
End Zd1.
#[using="Type"] Lemma calloc_hit_gen : ltac:(let t := eval cbv delta [calloc_hit_gen__stmt] in calloc_hit_gen__stmt in exact t).
Proof. exact calloc_hit_gen__body. Qed.

#[using="Type"] Lemma calloc_pre_gen : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c lo : Z) (maxc csz : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (calloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38388) fc None m (seg_rom asegs)).
Proof.
  intros until csz. intros ST CEIL LO MI -> -> -> -> SZ M8 HC CR T0 T1 RIMG RTLS RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF. (nd_pre CF 6%nat; intros C1 CS1 CS2 CS3 CSM CBG; nd_post).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.                                        (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].  (* [comment removed for export] *)
  do 2 step. step. if_lit.                          (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  1: eapply evtF_cut; [eapply (classblock_spec RNG); [lia | assumption | exact RIMG | exact RTLS] |].
  1: cbv beta; intros msB PB; (nd_pre PB 8%nat; intros a2b a4b a5b a6b a7b t0b t1b ndR1__; nd_post; revert ndR1__; intros ->); rewrite HC.
  2: do 2 zstep; rewrite <- (CSM ltac:(lia)); step.
  (* [comment removed for export] *)
  all: step.
  all: if_cases K3; zify_cond K3; [exfalso; lia|].
  all: step.
  all: step.
  all: if_cases K4; zify_cond K4; [exfalso; lia|].
  all: step.
  all: zstep.
  all: zstep.
  all: assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 2688) by lia.
  all: remember (t + 208 + c * 80) as R eqn:HR.
  all: lstep.
  all: step.
  all: if_cases K5; zify_cond K5; [| exfalso; apply K5; reflexivity].
  all: do 7 step.
  all: step.
  all: subst R.
  all: finish.
Qed.

#[using="Type"] Lemma calloc_popj_gen : forall RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v rv : word)
    (F : bvmap 5 word) fc (m : amem) (t c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk asegs m lo (bv_unsigned sp - 48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  bv_unsigned rv <> 0 ->
  1 <= c <= 30 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 spacebeg)] ->      (* [comment removed for export] *)
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR (Z_to_bv 64 0x38638) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
             (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
             rv a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38638) fc None m (seg_rom asegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI RV C1 FR SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RTLS RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  word_range sp SPR. word_range idxw IXR. word_range rv RVR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 2688) by lia.
  remember (t + 208 + c * 80) as R eqn:HR.
  step. if_cases K0; zify_cond K0. { exfalso. apply RV. exact K0. }   (* [comment removed for export] *)
  lstep.                                            (* [comment removed for export] *)
  do 3 step.                                        (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  zstep. step. zstep. zstep.                        (* [comment removed for export] *)
  replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
  step. clear RD. rewrite (zx32_small idxw) by lia.  (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO.                                   (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  do 4 zstep.                                       (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  do 8 step.                                        (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). subst R.
  setreg 10 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw))
    ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; zeq).
  finish. eexists. exact STS.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition calloc_hit_gen__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 spacebeg)] ->      (* [comment removed for export] *)
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x383f0) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 34).
Variable t : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 35).
Variable size : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 36).
Variable c : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 37).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 38).
Variable spacebeg : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 39).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 40).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 41).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 42).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 43).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 44).
Variable idxw : ltac2:(SecDietF.SzSecF.ty 'calloc_hit_gen__stmt 45).
#[using="Type"] Lemma calloc_hit_gen__body : ltac:(let T := type of (fun (h : calloc_hit_gen__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t size c cnt spacebeg lo maxc csz stj chunks idxw) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (t, (size, (c, (cnt, (spacebeg, (lo, (maxc, (csz, (stj, (chunks, idxw)))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> -> -> SZ M8 HC SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RTLS RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF. (nd_pre CF 6%nat; intros C1 CS1 CS2 CS3 CSM CBG; nd_post).
  word_range sp SPR. word_range idxw IXR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.                                        (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].  (* [comment removed for export] *)
  do 2 step. step. if_lit.                          (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  1: eapply evtF_cut; [eapply (classblock_spec RNG); [lia | assumption | exact RIMG | exact RTLS] |].
  1: cbv beta; intros msB PB; (nd_pre PB 8%nat; intros a2b a4b a5b a6b a7b t0b t1b ndR1__; nd_post; revert ndR1__; intros ->); rewrite HC.
  2: do 2 zstep; rewrite <- (CSM ltac:(lia)); step.
  (* [comment removed for export] *)
  all: step.
  all: if_cases K3; zify_cond K3; [exfalso; lia|].
  all: step.
  all: step.
  all: if_cases K4; zify_cond K4; [exfalso; lia|].
  all: step.
  all: zstep.
  all: zstep.
  all: assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 2688) by lia.
  all: remember (t + 208 + c * 80) as R eqn:HR.
  all: lstep.
  all: step.
  all: if_cases K5; zify_cond K5; [exfalso; lia|].
  all: do 3 zstep.
  all: step.
  all: zstep.
  all: step.
  all: zstep.
  all: zstep.
  all: replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  all: pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
  all: step.
  all: clear RD.
  all: rewrite (zx32_small idxw) by lia.
  all: assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
  all: amo_stepA AMO.
  all: step.
  all: do 4 zstep.
  all: step.
  all: step.
  all: if_lit.
  all: do 8 step.
  all: release_frame FR ST (bv_unsigned sp).
  all: subst R.
  all: setreg 10 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw))
    ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; zeq).
  all: finish.
  all: eexists.
  all: exact STS.
Qed.
End Zd1.
#[using="Type"] Lemma calloc_hit_gen : ltac:(let t := eval cbv delta [calloc_hit_gen__stmt] in calloc_hit_gen__stmt in exact t).
Proof. exact calloc_hit_gen__body. Qed.

#[using="Type"] Lemma calloc_pre_gen : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c lo : Z) (maxc csz : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (calloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x383f0) fc None m (seg_rom asegs)).
Proof.
  intros until csz. intros ST CEIL LO MI -> -> -> -> SZ M8 HC CR T0 T1 RIMG RTLS RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF. (nd_pre CF 6%nat; intros C1 CS1 CS2 CS3 CSM CBG; nd_post).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.                                        (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].  (* [comment removed for export] *)
  do 2 step. step. if_lit.                          (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  1: eapply evtF_cut; [eapply (classblock_spec RNG); [lia | assumption | exact RIMG | exact RTLS] |].
  1: cbv beta; intros msB PB; (nd_pre PB 8%nat; intros a2b a4b a5b a6b a7b t0b t1b ndR1__; nd_post; revert ndR1__; intros ->); rewrite HC.
  2: do 2 zstep; rewrite <- (CSM ltac:(lia)); step.
  (* [comment removed for export] *)
  all: step.
  all: if_cases K3; zify_cond K3; [exfalso; lia|].
  all: step.
  all: step.
  all: if_cases K4; zify_cond K4; [exfalso; lia|].
  all: step.
  all: zstep.
  all: zstep.
  all: assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 2688) by lia.
  all: remember (t + 208 + c * 80) as R eqn:HR.
  all: lstep.
  all: step.
  all: if_cases K5; zify_cond K5; [| exfalso; apply K5; reflexivity].
  all: do 7 step.
  all: step.
  all: subst R.
  all: finish.
Qed.

#[using="Type"] Lemma calloc_popj_gen : forall RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v rv : word)
    (F : bvmap 5 word) fc (m : amem) (t c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk asegs m lo (bv_unsigned sp - 48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  bv_unsigned rv <> 0 ->
  1 <= c <= 30 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 spacebeg)] ->      (* [comment removed for export] *)
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR (Z_to_bv 64 0x386a0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
             (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
             rv a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x386a0) fc None m (seg_rom asegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI RV C1 FR SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RTLS RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  word_range sp SPR. word_range idxw IXR. word_range rv RVR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 2688) by lia.
  remember (t + 208 + c * 80) as R eqn:HR.
  step. if_cases K0; zify_cond K0. { exfalso. apply RV. exact K0. }   (* [comment removed for export] *)
  lstep.                                            (* [comment removed for export] *)
  do 3 step.                                        (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  zstep. step. zstep. zstep.                        (* [comment removed for export] *)
  replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
  step. clear RD. rewrite (zx32_small idxw) by lia.  (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO.                                   (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  do 4 zstep.                                       (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  do 8 step.                                        (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). subst R.
  setreg 10 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw))
    ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; zeq).
  finish. eexists. exact STS.
Qed.
End CANSEC1.
End TwB.
End F_acache4.

(* [comment removed for export] *)
Module F_aclass2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acache3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma classblock2_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size : Z),
  513 <= size <= 65536 -> size mod 8 = 0 ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => exists a2' a3' a4' a5' a6',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (class_id size)) a2' a3' a4' a5' a6' a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x34298) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x341bc) fc None m (seg_rom asegs)).
Proof.
  intros until size. intros SZ M8 RIMG RTLS. pose proof (cb_sm_range size SZ M8) as [CBR CLZ].
  do 29 zstep. setreg 11 (Z_to_bv 64 (cb_sm size)) ltac:(reflexivity).            (* [comment removed for export] *)
  do 14 zstep. setreg 11 (Z_to_bv 64 (cb_clz (cb_sm size))) ltac:(reflexivity).   (* [comment removed for export] *)
  do 12 zstep. setreg 11 (Z_to_bv 64 (cb_fin size)) ltac:(reflexivity).            (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (class_id size))
    ltac:(symmetry; revert M8; revert SZ; clear; revert size; exact cb_fin_class_all).   (* [comment removed for export] *)
  apply evtF_done. do 5 eexists. reflexivity.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma classblock2_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size : Z),
  513 <= size <= 65536 -> size mod 8 = 0 ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => exists a2' a3' a4' a5' a6',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (class_id size)) a2' a3' a4' a5' a6' a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x34300) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x34224) fc None m (seg_rom asegs)).
Proof.
  intros until size. intros SZ M8 RIMG RTLS. pose proof (cb_sm_range size SZ M8) as [CBR CLZ].
  do 29 zstep. setreg 11 (Z_to_bv 64 (cb_sm size)) ltac:(reflexivity).            (* [comment removed for export] *)
  do 14 zstep. setreg 11 (Z_to_bv 64 (cb_clz (cb_sm size))) ltac:(reflexivity).   (* [comment removed for export] *)
  do 12 zstep. setreg 11 (Z_to_bv 64 (cb_fin size)) ltac:(reflexivity).            (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (class_id size))
    ltac:(symmetry; revert M8; revert SZ; clear; revert size; exact cb_fin_class_all).   (* [comment removed for export] *)
  apply evtF_done. do 5 eexists. reflexivity.
Qed.
End CANSEC1.
End TwB.
End F_aclass2.

(* [comment removed for export] *)
Module F_aalloc1.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
(* [comment removed for export] *)
Local Ltac fp_base8 := lazymatch goal with |- (?a <= ?b /\ _)%Z => let X := leftmost a in let Y := leftmost b in first [ constr_eq X Y | is_Zlit X; is_Zlit Y ] end.
Local Ltac fp_find8s := first [ apply Exists_cons_hd; cbn [fst snd]; fp_base8; split; lia | apply Exists_cons_tl; fp_find8s ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8s | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition allocate_entry := 0x33c08%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rz_ladder_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n : Z),
  0 <= n < 2^40 ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => exists a0',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (rz_log n)) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x33d74) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 49) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x33ca0) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros N RIMG RTLS. unfold rz_log.
  step. if_cases K0; zify_cond K0.
  2: { replace (n <=? 48) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
  step. step. if_cases K1; zify_cond K1.
  2: { replace (n <=? 96) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 96) with false by (symmetry; apply Z.leb_gt; lia).
  step. step. if_cases K2; zify_cond K2.
  2: { replace (n <=? 448) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 448) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K3; zify_cond K3.
  2: { replace (n <=? 3968) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 3968) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K4; zify_cond K4.
  2: { replace (n <=? 16128) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 16128) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K5; zify_cond K5.
  2: { replace (n <=? 32256) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 32256) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. zstep. zstep.
  apply evtF_done. destruct (Z.leb_spec n 64512) as [K6|K6]; eexists.
  - replace (n <? 64513) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - replace (n <? 64513) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rz_clamp_spec : forall RNG ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n rz : Z),
  0 <= n < 2^40 -> 0 <= rz <= 7 ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x33dbc) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 7) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x33da0) fc None m (seg_rom asegs)).
Proof.
  intros until rz. intros N RZ RIMG RTLS.
  step. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1.
    + (* [comment removed for export] *) step. step. step. if_cases K2; zify_cond K2.
      * replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
      * step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
    + (* [comment removed for export] *) step. replace rz with 7 by lia. step. step. step. if_cases K2; zify_cond K2.
      * step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
      * step. replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
  - (* [comment removed for export] *) step. replace rz with 0 by lia. step. if_lit. step. step. step. if_cases K2; zify_cond K2.
    + replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
    + step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition allocA_cells (m : amem) (ctx t : Z) : Prop :=
     rw_cells asegs m AINITED [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m ARSSLIM [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0xabdb8 (* [comment removed for export] *) [C8 (Z_to_bv 64 (2^40)); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)]
  /\ rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)].






End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
(* [comment removed for export] *)
Local Ltac fp_base8 := lazymatch goal with |- (?a <= ?b /\ _)%Z => let X := leftmost a in let Y := leftmost b in first [ constr_eq X Y | is_Zlit X; is_Zlit Y ] end.
Local Ltac fp_find8s := first [ apply Exists_cons_hd; cbn [fst snd]; fp_base8; split; lia | apply Exists_cons_tl; fp_find8s ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8s | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition allocate_entry := 0x33c70%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rz_ladder_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n : Z),
  0 <= n < 2^40 ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => exists a0',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (rz_log n)) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x33ddc) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 49) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x33d08) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros N RIMG RTLS. unfold rz_log.
  step. if_cases K0; zify_cond K0.
  2: { replace (n <=? 48) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
  step. step. if_cases K1; zify_cond K1.
  2: { replace (n <=? 96) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 96) with false by (symmetry; apply Z.leb_gt; lia).
  step. step. if_cases K2; zify_cond K2.
  2: { replace (n <=? 448) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 448) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K3; zify_cond K3.
  2: { replace (n <=? 3968) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 3968) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K4; zify_cond K4.
  2: { replace (n <=? 16128) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 16128) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K5; zify_cond K5.
  2: { replace (n <=? 32256) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 32256) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. zstep. zstep.
  apply evtF_done. destruct (Z.leb_spec n 64512) as [K6|K6]; eexists.
  - replace (n <? 64513) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - replace (n <? 64513) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rz_clamp_spec : forall RNG ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n rz : Z),
  0 <= n < 2^40 -> 0 <= rz <= 7 ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x33e24) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 7) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x33e08) fc None m (seg_rom asegs)).
Proof.
  intros until rz. intros N RZ RIMG RTLS.
  step. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1.
    + (* [comment removed for export] *) step. step. step. if_cases K2; zify_cond K2.
      * replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
      * step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
    + (* [comment removed for export] *) step. replace rz with 7 by lia. step. step. step. if_cases K2; zify_cond K2.
      * step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
      * step. replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
  - (* [comment removed for export] *) step. replace rz with 0 by lia. step. if_lit. step. step. step. if_cases K2; zify_cond K2.
    + replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
    + step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition allocA_cells (m : amem) (ctx t : Z) : Prop :=
     rw_cells asegs m AINITED [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m ARSSLIM [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0xac1b8 (* [comment removed for export] *) [C8 (Z_to_bv 64 (2^40)); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)]
  /\ rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)].






End CANSEC1.
End TwB.
End F_aalloc1.

(* [comment removed for export] *)
Module AFn_iface.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode SysStep Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition DEALLOCATE_ENTRY : Z := 0x338f4.    (* [comment removed for export] *)

Section Stmts.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition allocfn_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo SO pc : Z) (trc : list Z) (tb : list word)
         (RESV : list (Z * Z)),
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 SO -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX ->
  (* [comment removed for export] *)
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 -> bv_unsigned sp + 2144 < 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = pc :: trc ->
  In (pc :: trc) (al_U L) -> (length trc <= 29)%nat ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG SO 2056 ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).

Definition deallocfn_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word),
  AHEAP L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb) = pc :: trt ->
  In (pc :: trt) (al_U L) -> (length trt <= 29)%nat ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG SO 2056 ->
  4096 <= bv_unsigned ra ->      (* [comment removed for export] *)
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DEALLOCATE_ENTRY) fc None m (seg_rom asegs)).
End Stmts.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition DEALLOCATE_ENTRY : Z := 0x3395c.    (* [comment removed for export] *)

Section Stmts.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition allocfn_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo SO pc : Z) (trc : list Z) (tb : list word)
         (RESV : list (Z * Z)),
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 SO -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX ->
  (* [comment removed for export] *)
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 -> bv_unsigned sp + 2144 < 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = pc :: trc ->
  In (pc :: trc) (al_U L) -> (length trc <= 29)%nat ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG SO 2056 ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).

Definition deallocfn_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word),
  AHEAP L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb) = pc :: trt ->
  In (pc :: trt) (al_U L) -> (length trt <= 29)%nat ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG SO 2056 ->
  4096 <= bv_unsigned ra ->      (* [comment removed for export] *)
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DEALLOCATE_ENTRY) fc None m (seg_rom asegs)).
End Stmts.
End CANSEC1.
End TwB.
End AFn_iface.

(* [comment removed for export] *)
Module F_aalloc1b0.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition allocA_pre_post0 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x38388) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 128)
    /\ (exists j0, rw_cells asegs m' (bv_unsigned sp - 128)
         [CB 8 j0 (* [comment removed for export] *); C8 (Z_to_bv 64 0) (* [comment removed for export] *); C8 (Z_to_bv 64 16) (* [comment removed for export] *);
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Definition allocA_pre_spec0__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S ctx t lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 0 ->
  1 <= n -> is_primary n = true -> 0 < S < 2^64 ->
  allocA_cells m ctx t ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (allocA_pre_post0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 34).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 35).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 36).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 37).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 39).
#[using="Type"] Lemma allocA_pre_spec0__body : ltac:(let T := type of (fun (h : allocA_pre_spec0__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n S ctx t lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (S, (ctx, (t, lo)))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI TP -> -> -> -> -> -> N PRIM0 HS AC C0 C1 T0 T1 TAL CT2 RIMG RTLS RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  (nd_pre AC 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, allocate_entry in *.
  (pose proof (prim_facts n N PRIM0) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR0 RSR RSM NSR; nd_post).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 128%nat ST.
  do 14 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.     (* [comment removed for export] *)
  step. callp rss_spec; [exact RSS|]. step. if_lit.             (* [comment removed for export] *)
  step. if_cases KS; zify_cond KS. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step. if_lit.                                      (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                    (* [comment removed for export] *)
  step. step. zstep. zstep. zstep. step. zstep. zstep. zstep.    (* [comment removed for export] *)
  lstep. zstep. zstep. zstep.                               (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. zstep. zstep. step. if_lit.                              (* [comment removed for export] *)
  step. zstep. step. step.                                       (* [comment removed for export] *)
  callp rz_ladder_spec; [lia|].                                  (* [comment removed for export] *)
  lstep. step. step. zstep. zstep.                        (* [comment removed for export] *)
  step. call_sp rz2log16_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  step. lstep. step. zstep.                                      (* [comment removed for export] *)
  step. call_sp rz2log2048_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  callp rz_clamp_spec; [lia| exact RLR0 |].   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  change ((Z.b2z (8 <? 9) + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l, Z.add_0_r.
  rewrite land_align8 by lia.
  setreg 10 (Z_to_bv 64 (rounded_size n)) ltac:(f_equal; rewrite rounded_size_align; lia).
  zstep. step. if_cases KA; zify_cond KA. { exfalso. apply KA. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. exact RSM. }   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep. zstep.                                                  (* [comment removed for export] *)
  first [rewrite (sllw_rz_gen2 n) | rewrite (sllw_rz_gen n)].   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  zstep. replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].   (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  rewrite <- NS.
  zstep. zstep. zstep. zstep. step. zstep.                       (* [comment removed for export] *)
  replace (needed_size n <? 65537) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change ((Z.land 1 1 + -1) mod 18446744073709551616) with 0. change (Z.land 1 1) with 1. rewrite Z.land_0_l, Z.add_0_l.
  step. if_cases KB; zify_cond KB. { exfalso. lia. }            (* [comment removed for export] *)
  step. if_cases KC; zify_cond KC. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_cases KD; zify_cond KD. 2: { exfalso. lia. }   (* [comment removed for export] *)
  box RT.
  step. call_sp get_current_thread_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  unbox RT. rename POST into ST.
  step. step. if_cases KE; zify_cond KE. { exfalso. lia. }      (* [comment removed for export] *)
  zstep. step. step. step.                                       (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  apply evtF_done. unfold allocA_pre_post0. do 12 eexists. split; [reflexivity|].
  repeat lazymatch goal with |- _ /\ _ => split end.
  all: try assumption. all: eexists; eassumption.
Qed.
End Zd1.
#[using="Type"] Lemma allocA_pre_spec0 : ltac:(let t := eval cbv delta [allocA_pre_spec0__stmt] in allocA_pre_spec0__stmt in exact t).
Proof. exact allocA_pre_spec0__body. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition allocA_pre_post0 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x383f0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 128)
    /\ (exists j0, rw_cells asegs m' (bv_unsigned sp - 128)
         [CB 8 j0 (* [comment removed for export] *); C8 (Z_to_bv 64 0) (* [comment removed for export] *); C8 (Z_to_bv 64 16) (* [comment removed for export] *);
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Definition allocA_pre_spec0__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S ctx t lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 0 ->
  1 <= n -> is_primary n = true -> 0 < S < 2^64 ->
  allocA_cells m ctx t ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (allocA_pre_post0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 34).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 35).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 36).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 37).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec0__stmt 39).
#[using="Type"] Lemma allocA_pre_spec0__body : ltac:(let T := type of (fun (h : allocA_pre_spec0__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n S ctx t lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (S, (ctx, (t, lo)))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI TP -> -> -> -> -> -> N PRIM0 HS AC C0 C1 T0 T1 TAL CT2 RIMG RTLS RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  (nd_pre AC 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, allocate_entry in *.
  (pose proof (prim_facts n N PRIM0) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR0 RSR RSM NSR; nd_post).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 128%nat ST.
  do 14 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.     (* [comment removed for export] *)
  step. callp rss_spec; [exact RSS|]. step. if_lit.             (* [comment removed for export] *)
  step. if_cases KS; zify_cond KS. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step. if_lit.                                      (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                    (* [comment removed for export] *)
  step. step. zstep. zstep. zstep. step. zstep. zstep. zstep.    (* [comment removed for export] *)
  lstep. zstep. zstep. zstep.                               (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. zstep. zstep. step. if_lit.                              (* [comment removed for export] *)
  step. zstep. step. step.                                       (* [comment removed for export] *)
  callp rz_ladder_spec; [lia|].                                  (* [comment removed for export] *)
  lstep. step. step. zstep. zstep.                        (* [comment removed for export] *)
  step. call_sp rz2log16_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  step. lstep. step. zstep.                                      (* [comment removed for export] *)
  step. call_sp rz2log2048_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  callp rz_clamp_spec; [lia| exact RLR0 |].   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  change ((Z.b2z (8 <? 9) + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l, Z.add_0_r.
  rewrite land_align8 by lia.
  setreg 10 (Z_to_bv 64 (rounded_size n)) ltac:(f_equal; rewrite rounded_size_align; lia).
  zstep. step. if_cases KA; zify_cond KA. { exfalso. apply KA. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. exact RSM. }   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep. zstep.                                                  (* [comment removed for export] *)
  first [rewrite (sllw_rz_gen2 n) | rewrite (sllw_rz_gen n)].   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  zstep. replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].   (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  rewrite <- NS.
  zstep. zstep. zstep. zstep. step. zstep.                       (* [comment removed for export] *)
  replace (needed_size n <? 65537) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change ((Z.land 1 1 + -1) mod 18446744073709551616) with 0. change (Z.land 1 1) with 1. rewrite Z.land_0_l, Z.add_0_l.
  step. if_cases KB; zify_cond KB. { exfalso. lia. }            (* [comment removed for export] *)
  step. if_cases KC; zify_cond KC. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_cases KD; zify_cond KD. 2: { exfalso. lia. }   (* [comment removed for export] *)
  box RT.
  step. call_sp get_current_thread_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  unbox RT. rename POST into ST.
  step. step. if_cases KE; zify_cond KE. { exfalso. lia. }      (* [comment removed for export] *)
  zstep. step. step. step.                                       (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  apply evtF_done. unfold allocA_pre_post0. do 12 eexists. split; [reflexivity|].
  repeat lazymatch goal with |- _ /\ _ => split end.
  all: try assumption. all: eexists; eassumption.
Qed.
End Zd1.
#[using="Type"] Lemma allocA_pre_spec0 : ltac:(let t := eval cbv delta [allocA_pre_spec0__stmt] in allocA_pre_spec0__stmt in exact t).
Proof. exact allocA_pre_spec0__body. Qed.
End CANSEC1.
End TwB.
End F_aalloc1b0.
