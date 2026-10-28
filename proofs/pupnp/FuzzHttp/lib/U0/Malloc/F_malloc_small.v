(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import Malloc_fp F_malloc_enf AllocSlot_iface Malloc_iface F_malloc_join.
Import ListNotations.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

Definition coarse_sc (st : mstate) (sc : Z) : Z :=
  match active st sc with
  | Some _ => sc
  | None =>
    if (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) then
      let usage1 := usage st (Z.lor sc 1) in
      let usage1 := match active st (Z.lor sc 1) with
                    | None => usage1 + 3
                    | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
                                if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                    end in
      if usage1 <=? 12 then Z.lor sc 1 else sc
    else sc
  end.

Lemma malloc_small_ctrl_eq {R} lay st n (k : mstate -> option (aptr * Z) -> Malloc.M R) bail :
  malloc_small_ctrl lay st n k bail =
  let sc := coarse_sc st (size_to_class n) in
  let g := active st sc in
  let mask := match g with Some gp => m_avail (get_meta_rec st gp) | None => 0 end in
  let first := lowbit mask in
  match g, negb (first =? 0) with
  | Some gp, true => k (upd_meta gp (m_set_avail (mask - first)) st) (Some (gp, ctz32 first))
  | _, _ =>
    alloc_slot lay FUEL st sc n (fun st1 idx =>
      if idx <? 0 then k st1 None
      else match active st1 sc with
           | Some gp => k st1 (Some (gp, idx))
           | None => SVis (EUndef UBadPtr) (fun _ => bail)
           end) bail
  end.
Proof. reflexivity. Qed.

Lemma usages_length : forall st, length (usages st) = 48%nat.
Proof. intros. unfold usages. rewrite length_map, length_seq. reflexivity. Qed.
Lemma usages_nth : forall st sc, 0 <= sc < 48 -> nth_error (usages st) (Z.to_nat sc) = Some (wz (usage st sc)).
Proof.
  intros st sc Hsc. unfold usages. rewrite nth_error_map, nth_error_seq.
  replace (Z.to_nat sc <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma lxor_sign_small x : 0 <= x < 2^63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros Hx. change 9223372036854775808 with (2^63).
  rewrite <- Z.add_nocarry_lxor. 2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec i 63) as [->|NE].
    - replace (Z.testbit x 63) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
      destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
    - rewrite Z.pow2_bits_false by lia. apply andb_false_r. }
  reflexivity.
Qed.

Lemma land_ones64 y : Z.land y 18446744073709551615 = y mod 2^64.
Proof. change 18446744073709551615 with (Z.ones 64). apply Z.land_ones. lia. Qed.

Lemma land_1_even x : (Z.land x 1 = 0) <-> Z.even x = true.
Proof.
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2^1) with 2.
  rewrite Z.even_spec. split.
  - intros H. exists (x / 2). lia.
  - intros [k ->]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

Section COARSE.
Variables (st : mstate) (LB : list block) (m1 : mem) (t : N).
Let st1 := set_tick t st.
End COARSE.

Definition lor1_check : bool :=
  forallb (fun sc => negb ((4 <=? sc) && (sc <? 32) && Z.even sc) || (size_class sc <=? size_class (Z.lor sc 1))) (zseq 0 48).
Lemma lor1_check_true : lor1_check = true.
Proof. vm_compute. reflexivity. Qed.

Lemma size_class_lor1 sc : 4 <= sc < 32 -> Z.even sc = true -> size_class sc <= size_class (Z.lor sc 1).
Proof.
  intros H E. pose proof (forallb_zseq _ 0 48 sc lor1_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
  replace (4 <=? sc) with true in X by (symmetry; apply Z.leb_le; lia).
  replace (sc <? 32) with true in X by (symmetry; apply Z.ltb_lt; lia). rewrite E in X. cbn [andb negb orb] in X.
  apply Z.leb_le. exact X.
Qed.

Definition lor1_range_check : bool := forallb (fun sc => (0 <=? Z.lor sc 1) && (Z.lor sc 1 <? 48)) (zseq 0 48).
Lemma lor1_range_check_true : lor1_range_check = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lor1_range sc : 0 <= sc < 48 -> 0 <= Z.lor sc 1 < 48.
Proof.
  intros H. pose proof (forallb_zseq _ 0 48 sc lor1_range_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
  apply andb_prop in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
Qed.

Lemma coarse_sc_cases st sc : 0 <= sc < 48 ->
  coarse_sc st sc = sc \/ (coarse_sc st sc = Z.lor sc 1 /\ 4 <= sc < 32 /\ Z.even sc = true).
Proof.
  intros H. unfold coarse_sc. destruct (active st sc); [left; reflexivity|].
  destruct ((4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0)) eqn:E; [|left; reflexivity].
  apply andb_prop in E. destruct E as [E E5]. apply andb_prop in E. destruct E as [E E4].
  apply andb_prop in E. destruct E as [E E3]. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  cbv zeta. destruct (_ <=? 12); [right|left]; auto.
Qed.

Section SMALL.
Context {HCEIL : HasCeiling}.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis TP : tp = Z_to_bv 64 0x1b708.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.
End SMALL.