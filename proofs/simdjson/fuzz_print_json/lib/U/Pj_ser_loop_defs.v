(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit Pj_defs Pj_stmts Pj_ser_defs Pj_ser_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition kbyte (k : bool) : byte := Z_to_bv 8 (if k then 1 else 0).
Definition kinds_rel (ks : list bool) (isobj : list byte) : Prop :=
  nth_error isobj 0 = Some (Z_to_bv 8 0)
  /\ forall j k, nth_error (rev ks) j = Some k -> nth_error isobj (j + 1) = Some (kbyte k).

Lemma kinds_rel_push : forall ks isobj k, kinds_rel ks isobj -> (length ks + 1 < length isobj)%nat ->
  kinds_rel (k :: ks) (upd isobj (length ks + 1) (kbyte k)).
Proof.
  intros ks isobj k [H0 H] HL. split.
  - rewrite nth_error_upd_other by lia. exact H0.
  - intros j x Hj. cbn [rev] in Hj. destruct (Nat.lt_ge_cases j (length ks)) as [L|L].
    + rewrite nth_error_app1 in Hj by (rewrite length_rev; exact L). rewrite nth_error_upd_other by lia. apply H. exact Hj.
    + rewrite nth_error_app2 in Hj by (rewrite length_rev; exact L). rewrite length_rev in Hj.
      destruct (j - length ks)%nat as [|q] eqn:Eq; [| destruct q; discriminate].
      cbn in Hj. inversion Hj; subst x. replace j with (length ks) by lia. apply nth_error_upd_same. exact HL.
Qed.
Lemma kinds_rel_pop : forall k ks isobj, kinds_rel (k :: ks) isobj -> kinds_rel ks isobj.
Proof.
  intros k ks isobj [H0 H]. split; [exact H0|]. intros j x Hj. apply H. cbn [rev]. rewrite nth_error_app1; [exact Hj|].
  apply nth_error_Some. congruence.
Qed.
Lemma kinds_rel_top : forall k ks isobj, kinds_rel (k :: ks) isobj -> nth_error isobj (length ks + 1) = Some (kbyte k).
Proof.
  intros k ks isobj [_ H]. apply (H (length ks) k). cbn [rev]. rewrite nth_error_app2 by (rewrite length_rev; lia).
  rewrite length_rev, Nat.sub_diag. reflexivity.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition item_ok (E : senv) (ks : list bool) (d0 : nat) : Z -> Z -> Z -> Z -> Prop :=
  match ks with
  | [] => elemS (e_T E) (e_S E) (e_sn E) ck_any d0
  | k :: _ => itemS (e_T E) (e_S E) (e_sn E) k d0
  end.

Notation REST E := (rest_ok (e_T E) (e_S E) (e_sn E)).

Definition exit_K (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) : Prop :=
  forall (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32) (e64 e72 e80 spill : word) (isobj : list byte)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    SERM E e64 e72 e80 spill isobj st s m -> frm0 fc -> sb_size st <= 41 * (e_j E - 1) + 6 * e_c' E + 2 ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3eeb4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).

Definition head_stmt (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (D : nat) (f : nat) : Prop :=
  forall (d0 : nat) (ks : list bool) (i i2 c c2 : Z) (after : bool) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (e64 e72 e80 spill : word)
         (xs3 xs8 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    e_j E - i <= Z.of_nat f -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    item_ok E ks d0 i i2 c c2 -> REST E d0 ks i2 c2 (e_j E) (e_c' E) -> (ks = [] -> after = false) -> 1 <= i -> 0 <= c ->
    SERM E e64 e72 e80 spill isobj st s m -> frm0 fc -> sb_size st <= 41 * (i - 1) + 6 * c + (if after then 2 else 3) ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E PJ_HEAD i (Z.of_nat (length ks)) xs3 xs8 xra xt0 xt1 xt2 (Z_to_bv 64 (Z.b2z after)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xt3 xt4 xt5 xt6 F fc m).

Definition disp_stmt (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (D : nat) (f : nat) : Prop :=
  forall (d0 : nat) (ks : list bool) (i i2 c c2 : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (spill : word)
         (xs8 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    e_j E - i <= Z.of_nat f -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    elemS (e_T E) (e_S E) (e_sn E) ck_any d0 i i2 c c2 -> REST E d0 ks i2 c2 (e_j E) (e_c' E) -> 1 <= i -> 0 <= c ->
    SERMC E spill isobj st s m -> frm0 fc -> sb_size st <= 41 * (i - 1) + 6 * c + 3 ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E PJ_DISP i (Z.of_nat (length ks)) (Z_to_bv 64 PJ_NE_TAB) xs8 xra xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xt3 xt4 xt5 xt6 F fc m).

Definition aval_stmt (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (D : nat) (f : nat) : Prop :=
  forall (pc : Z) (d0 : nat) (ks : list bool) (i2 c2 : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (spill : word)
         (xs3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    av_pc_ok pc -> (pc = PJ_AV0 \/ xs3 = Z_to_bv 64 PJ_TMASK) ->
    e_j E - i2 <= Z.of_nat f -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    REST E d0 ks i2 c2 (e_j E) (e_c' E) -> 2 <= i2 -> 0 <= c2 ->
    SERMC E spill isobj st s m -> frm0 fc -> sb_size st <= 41 * (i2 - 1) + 6 * c2 + 2 ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E pc (i2 - 1) (Z.of_nat (length ks)) xs3 (Z_to_bv 64 PJ_RBR56) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m).

Definition open_stmt (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (D : nat) (f : nat) (k : bool) : Prop :=
  forall (d' : nat) (ks : list bool) (i e n c c2 : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (spill : word)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    e_j E - (i + 1) <= Z.of_nat f -> (S d' + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    ty (e_T E) i = (if k then t_obj else t_arr) -> tnext (e_T E i) = e + 1 -> ty (e_T E) e = end_ty k ->
    tilesS (itemS (e_T E) (e_S E) (e_sn E) k d') (i + 1) e n c c2 ->
    REST E (S d') ks (e + 1) c2 (e_j E) (e_c' E) -> 1 <= i -> 0 <= c ->
    SERMC E spill isobj st s m -> frm0 fc -> sb_size st <= 41 * (i - 1) + 6 * c + 3 ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E (if k then 0x3e498 else 0x3e338) i (Z.of_nat (length ks)) (Z_to_bv 64 PJ_TMASK) (Z_to_bv 64 PJ_RBR56) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xt3 xt4 xt5 xt6 F fc m).

Definition rec_ok (D : nat) : Prop := forall (k : bool) (d' : nat), (d' + 16 <= D)%nat -> cont_stmt k d'.

End WithCeiling0.
