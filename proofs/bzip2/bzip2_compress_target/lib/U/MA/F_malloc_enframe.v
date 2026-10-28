(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac Image ZBridge SysStep SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition smear (s : Z) : Z :=
  let m1 := Z.lor s (Z.shiftr s 1) in
  let m2 := Z.lor m1 (Z.shiftr m1 2) in
  Z.lor m2 (Z.shiftr m2 4).

Lemma fold_off_eq off slack :
  fold_off off slack =
  (if slack <? off then
     let x := Z.land off (smear slack) in if slack <? x then x - (slack + 1) else x
   else off).
Proof. reflexivity. Qed.

Lemma smear_nonneg s : 0 <= s -> 0 <= smear s.
Proof.
  intros. unfold smear.
  repeat (apply Z.lor_nonneg; split); repeat apply Z.shiftr_nonneg; repeat (apply Z.lor_nonneg; split);
    repeat apply Z.shiftr_nonneg; try lia; repeat (apply Z.lor_nonneg; split); try apply Z.shiftr_nonneg; try lia.
  all: try (apply Z.lor_nonneg; split); try apply Z.shiftr_nonneg; try lia.
Qed.

Lemma land_le_l a b : 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
  intros. rewrite <- (Z.lor_ldiff_and a b) at 2.
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia).
  assert (0 <= Z.land a b) by (apply Z.land_nonneg; lia).
  assert (Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by assumption. lia.
Qed.

(* [comment removed for export] *)
Definition zseq (a n : Z) : list Z := map Z.of_nat (seq (Z.to_nat a) (Z.to_nat n)).

(* [comment removed for export] *)
Definition fold_fn1 (s off : Z) : bool :=
  let x := Z.land off (smear s) in (negb (s <? x)) || (x - (s + 1) <=? s).
Definition fold_fn (s : Z) : bool := forallb (fold_fn1 s) (zseq 0 256).
(* [comment removed for export] *)

Lemma fold_check_true : forallb fold_fn (zseq 0 128) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma forallb_zseq (f : Z -> bool) a n x : forallb f (zseq a n) = true -> 0 <= a -> a <= x < a + n -> f x = true.
Proof.
  intros H Ha Hx. unfold zseq in H. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma fold_assert_ok off slack : 0 <= off < 256 -> 0 <= slack ->
  slack < Z.land off (smear slack) -> Z.land off (smear slack) - (slack + 1) <= slack.
Proof.
  intros Ho Hs Hlt.
  pose proof (smear_nonneg slack Hs) as Sm.
  assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
  destruct (Z.lt_ge_cases slack 128).
  - pose proof (forallb_zseq fold_fn 0 128 slack fold_check_true ltac:(lia) ltac:(lia)) as H1. unfold fold_fn in H1.
    pose proof (forallb_zseq (fold_fn1 slack) 0 256 off H1 ltac:(lia) ltac:(lia)) as H2. unfold fold_fn1 in H2. cbv zeta in H2.
    apply orb_prop in H2. destruct H2 as [H2|H2].
    + apply negb_true_iff in H2. apply Z.ltb_ge in H2. lia.
    + apply Z.leb_le in H2. exact H2.
  - lia.
Qed.

(* [comment removed for export] *)

Lemma fold_off_le_slack off slack : 0 <= off < 256 -> 0 <= slack -> 0 <= fold_off off slack <= slack.
Proof.
  intros Ho Hs. rewrite fold_off_eq. pose proof (smear_nonneg slack Hs) as Sm.
  assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
  assert (LB : 0 <= Z.land off (smear slack)) by (apply Z.land_nonneg; lia).
  destruct (Z.ltb_spec slack off); [|lia]. cbv zeta.
  destruct (Z.ltb_spec slack (Z.land off (smear slack))); [|lia].
  pose proof (fold_assert_ok off slack Ho Hs ltac:(lia)). lia.
Qed.

Lemma land_126 y : Z.land y 126 = 2 * Z.land (Z.shiftr y 1) 63.
Proof.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|].
  - rewrite Z.testbit_even_0. change 126 with (2 * 63). rewrite Z.testbit_even_0. apply andb_false_r.
  - replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ by lia.
    change 126 with (2 * 63). rewrite Z.testbit_even_succ by lia. rewrite Z.land_spec, Z.shiftr_spec by lia.
    replace (i - 1 + 1) with i by lia. replace (Z.succ (i - 1)) with i by lia. reflexivity.
Qed.

Lemma mword_sc last_idx freeable sc maplen :
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen ->
  Z.land (Z.shiftr (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) 5) 126 = 2 * sc.
Proof.
  intros. rewrite land_126. rewrite Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia. change (2 ^ (5 + 1)) with 64.
  change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2^6) with 64.
  replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) / 64) with (sc + 64 * maplen) by (Z.div_mod_to_equations; lia).
  replace ((sc + 64 * maplen) mod 64) with sc by (Z.div_mod_to_equations; lia). reflexivity.
Qed.
End ACeilS1.



(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sdk :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     | _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
     end);
    (try lazymatch goal with
     | HI : mem_inv segs m, HS : store_ok segs m ?a' ?n = true |- _ =>
        apply (mem_inv_store segs m (wa E) bs) in HI;
        [ | first [ exact HS
                  | replace (wa E) with a' by (first [reflexivity | addr_eq_tac | symmetry; addr_eq_tac]);
                    first [ exact HS | simpl_sizes; exact HS ] ] ]
     end);
    transport_chunks segs m E bs;
    repeat match goal with
    | STq : stk segs m ?loq ?hiq |- _ =>
        first [ apply (stk_write segs m loq hiq E bs) in STq; [ | lia | simpl_sizes; slia ]
              | fail 100 "sdk: cannot transport stk hypothesis" STq ]
    | MU : munch ?Wq ?mq m |- _ =>
        first [ apply (munch_write Wq mq m E bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
              | fail 100 "sdk: store outside the declared footprint" ]
    | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa E) bs) in WMo
    end;
    repeat match goal with
    | H : store_ok segs m _ _ = true |- _ => clear H
    | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
    end;
    let m' := fresh "m" in let Eq := fresh "EQ" m' in
    remember (write_to_mem m (wa E) bs) as m' eqn:Eq
  end.
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Lemma le1_wz v : 0 <= v < 256 -> le1 (wz v) = [b8 v].
Proof. intros. cbn. rewrite (wz_unsigned v) by lia. reflexivity. Qed.

Lemma le1_neg32 : le1 (Z_to_bv 64 (-32)) = [b8 224].
Proof. cbn. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FASTMODEL.
Context {O : Type}.
Variable pans : O -> aptr -> Z -> Z -> Z.
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.
Let pupd : O -> ev -> Z -> O := fun o _ _ => o.
Local Notation prun := (prun pans pupd).

(* [comment removed for export] *)
Definition rdv (o : O) (st : mstate) (q : aptr) : Z :=
  match cell_read (get_shadow st (fst q)) (snd q) with
  | Known v => v
  | Unknown h => pans o q (conc st q) h
  end.

Lemma rd8_oracle {R} o st q (k : Z -> M R) : prun o (rd8 st q k) = prun o (k (rdv o st q)).
Proof.
  unfold rd8, rdv. destruct (cell_read _ _) as [v|h]; [reflexivity|].
  unfold MallocCtrl.prun. cbn [eruns psel].
  pose proof (Hpans o q (conc st q) h).
  replace (peek_answer_ok (pans o q (conc st q) h)) with true.
  2:{ symmetry. unfold peek_answer_ok. apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
  reflexivity.
Qed.

Lemma rd16_oracle {R} o st q (k : Z -> M R) :
  prun o (rd16 st q k) = prun o (k (rdv o st q + 256 * rdv o st (aadd q 1))).
Proof. unfold rd16. rewrite rd8_oracle, rd8_oracle. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma get_meta_rec_upd_same st g f : get_meta_rec (upd_meta g f st) g = f (get_meta_rec st g).
Proof. unfold get_meta_rec at 1. unfold upd_meta, put_meta. cbn. rewrite lookup_insert_eq. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End FASTMODEL.
End ACeilS2.
