(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import F_syscalls_u MallocRep_u F_malloc_free_u F_malloc_fast_u F_malloc_enframe_u MallocTree_u MallocFacts_A_u MallocKit_A_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import Malloc_fp_u.
Import ListNotations.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)

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

Definition entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists a2 a3 a4 junk m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz n) s1 (Z_to_bv 64 n) a1 a2 a3 a4 (Z_to_bv 64 (size_to_class n)) a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x16e88) fc None m' (seg_rom asegs)
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 48 junk; C8 s0; C8 ra]
    /\ length junk = 48%nat
    /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'.
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition entry_big_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists junk m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz n) s1 (Z_to_bv 64 n) a1 a2 a3 a4 (Z_to_bv 64 131051) a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x16d60) fc None m' (seg_rom asegs)
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 48 junk; C8 s0; C8 ra]
    /\ length junk = 48%nat
    /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'.
End CEIL_WRAP_1.

(* [comment removed for export] *)
