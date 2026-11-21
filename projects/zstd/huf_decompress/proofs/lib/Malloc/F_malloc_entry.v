(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (8 recorded proofs replaced by written proofs (srliw_small, lor_small, shiftr_small and 5 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_malloc_entry () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions8bv_swrapI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z8le_transC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib3Lib7SysStep=swrap32_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC59OSSVerify5KrLib3Lib7ZBridge:zb_lor_eq0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib6Malloc@F_malloc_enframe4zseqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbc59OSSVerify5KrLib6Malloc>F_malloc_entry6clz_fnC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib6Malloc@F_malloc_enframe<forallb_zseqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc>F_malloc_entry7clz_powC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbc59OSSVerify5KrLib6Malloc>F_malloc_entry8clz_notvC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib6Malloc>F_malloc_entry>clz_check_trueC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc>F_malloc_entry6stc_fnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc>F_malloc_entry5stc_qC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool8orb_propI47Corelib4Init5Logic2or00c59OSSVerify5KrLib6Malloc>F_malloc_entry?size_to_class_qC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc>F_malloc_entry>stc_check_trueC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma srliw_small a k : 0 <= a < 2^31 -> 0 <= k -> bv_swrap 32 (Z.shiftr (bv_wrap 32 a) k) = Z.shiftr a k.
Proof.
  intros Ha Hk. change (bv_wrap 32 a) with (a mod 2^32). rewrite Z.mod_small by lia.
  apply swrap32_small. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia]|].
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma lor_small n a b : 0 <= n -> 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros Hn Ha Hb. pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)) as NN. split; [exact NN|].
  destruct (Z.eq_dec a 0) as [->|A0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|B0]; [rewrite Z.lor_0_r; lia|].
  assert (P : 0 < Z.lor a b).
  { destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [apply zb_lor_eq0 in E; lia|]. lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n P)).
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
  - apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia.
  - apply (proj1 (Z.log2_lt_pow2 b n ltac:(lia))). lia.
Qed.

Lemma shiftr_small n a k : 0 <= a < 2^n -> 0 <= k -> 0 <= Z.shiftr a k < 2^n.
Proof.
  intros Ha Hk. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Definition clz_pow (x : Z) : Z :=
  let v1 := Z.lor (Z.shiftr x 2) (Z.shiftr x 1) in
  let v2 := Z.lor v1 (Z.shiftr v1 2) in
  let v3 := Z.lor v2 (Z.shiftr v2 4) in
  let v4 := Z.lor v3 (Z.shiftr v3 8) in
  Z.land (v4 + 1) (Z.lxor v4 18446744073709551615).
Definition clz_notv (x : Z) : Z :=
  let v1 := Z.lor (Z.shiftr x 2) (Z.shiftr x 1) in
  let v2 := Z.lor v1 (Z.shiftr v1 2) in
  let v3 := Z.lor v2 (Z.shiftr v2 4) in
  let v4 := Z.lor v3 (Z.shiftr v3 8) in
  Z.lxor v4 18446744073709551615.
Definition clz_fn (x : Z) : bool := (clz_pow x =? 2 ^ Z.log2 x) && (0 <=? clz_notv x) && (clz_notv x <? 2^64).
Lemma clz_check_true : forallb clz_fn (zseq 11 8181) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma clz_pow_eq x : 11 <= x < 8192 -> clz_pow x = 2 ^ Z.log2 x /\ 0 <= clz_notv x < 2^64.
Proof.
  intros Hx. pose proof (forallb_zseq clz_fn 11 8181 x clz_check_true ltac:(lia) ltac:(lia)) as X. unfold clz_fn in X.
  apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
  apply Z.eqb_eq in X1. apply Z.leb_le in X2. apply Z.ltb_lt in X3. split; [exact X1| split; [exact X2| exact X3]].
Qed.

(* [comment removed for export] *)
Definition stc_q (q : Z) : Z :=
  if q <? 10 then q else
    let x := q + 1 in
    let i := 4 * Z.log2 x - 4 in
    let i := if size_class (i + 1) <? x then i + 2 else i in
    if size_class i <? x then i + 1 else i.
Definition stc_fn (q : Z) : bool :=
  let sc := stc_q q in (0 <=? sc) && (sc <? 48) && (q + 1 <=? size_class sc)
                    && ((q <? 10) || ((3 <=? Z.log2 (q + 1)) && (Z.log2 (q + 1) <=? 12))).
Lemma stc_check_true : forallb stc_fn (zseq 0 8191) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma size_to_class_q n : 0 <= n -> size_to_class n = stc_q ((n + 3) / 16).
Proof.
  intros Hn. unfold size_to_class, stc_q, IB, clz32.
  replace (Z.shiftr (n + 4 - 1) 4) with ((n + 3) / 16) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 4) with 16; f_equal; lia).
  set (q := (n + 3) / 16). cbv zeta.
  replace ((28 - (31 - Z.log2 (q + 1))) * 4 + 8) with (4 * Z.log2 (q + 1) - 4) by lia.
  reflexivity.
Qed.

Lemma size_to_class_props n : 0 <= n < MMAP_THRESHOLD ->
  0 <= size_to_class n < 48 /\ n + 4 <= 16 * size_class (size_to_class n)
  /\ (10 <= (n + 3) / 16 -> 3 <= Z.log2 ((n + 3) / 16 + 1) <= 12).
Proof.
  intros Hn. unfold MMAP_THRESHOLD in Hn. rewrite size_to_class_q by lia.
  assert (Q : 0 <= (n + 3) / 16 < 8191) by (Z.div_mod_to_equations; lia).
  pose proof (forallb_zseq stc_fn 0 8191 ((n + 3) / 16) stc_check_true ltac:(lia) ltac:(lia)) as X. unfold stc_fn in X. cbv zeta in X.
  apply andb_prop in X. destruct X as [X X4]. apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
  apply Z.leb_le in X1. apply Z.ltb_lt in X2. apply Z.leb_le in X3.
  split; [lia|]. split; [Z.div_mod_to_equations; lia|].
  intros HQ. apply orb_prop in X4. destruct X4 as [X4|X4]; [apply Z.ltb_lt in X4; lia|].
  apply andb_prop in X4. destruct X4 as [X5 X6]. apply Z.leb_le in X5. apply Z.leb_le in X6. lia.
Qed.

End CANSEC1.
