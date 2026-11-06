(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface XRep XPRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive tokres : Type :=
| TK_end                      (* [comment removed for export] *)
| TK_err                      (* [comment removed for export] *)
| TK_tok (k l : nat).         (* [comment removed for export] *)

Definition tk_shift (r : tokres) : tokres :=
  match r with TK_tok k l => TK_tok (S k) l | _ => r end.

(* [comment removed for export] *)
Fixpoint tspan (s : list Z) : nat :=
  match s with
  | c :: s' => if is_tchar c then S (tspan s') else 0%nat
  | [] => 0%nat
  end.

(* [comment removed for export] *)
Fixpoint tok_next (nc : bool) (s : list Z) : tokres :=
  match s with
  | [] => TK_end
  | c :: s' =>
      if is_ws c then tk_shift (tok_next nc s')
      else if is_tchar c then (if nc then TK_err else TK_tok 0 (S (tspan s')))
      else if c =? 44 then tk_shift (tok_next false s')
      else TK_err
  end.

(* [comment removed for export] *)
Fixpoint opt_valid_from (fuel : nat) (nc : bool) (s : list Z) : bool :=
  match fuel with
  | 0%nat => true
  | S f => match tok_next nc s with
           | TK_end => true
           | TK_err => false
           | TK_tok k l => opt_valid_from f true (skipn (k + l) s)
           end
  end.
Definition opt_token_list_valid (s : list Z) : bool := opt_valid_from (S (length s)) false s.

(* [comment removed for export] *)
Fixpoint toks_from (fuel : nat) (nc : bool) (s : list Z) : list (list Z) :=
  match fuel with
  | 0%nat => []
  | S f => match tok_next nc s with
           | TK_tok k l => firstn l (skipn k s) :: toks_from f true (skipn (k + l) s)
           | _ => []
           end
  end.
Definition token_list_of (s : list Z) : list (list Z) := toks_from (S (length s)) false s.

(* [comment removed for export] *)
Fixpoint tl_ieqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (lowerc x =? lowerc y) && tl_ieqb a' b'
  | _, _ => false
  end.
Definition token_list_exists (s t : list Z) : bool := existsb (tl_ieqb t) (token_list_of s).

(* [comment removed for export] *)
Lemma tspan_le : forall s, (tspan s <= length s)%nat.
Proof. induction s as [|c s IH]; cbn; [lia|]. destruct (is_tchar c); lia. Qed.

Lemma tok_next_tok_bound : forall nc s k l, tok_next nc s = TK_tok k l -> (k + l <= length s)%nat /\ (1 <= l)%nat.
Proof.
  intros nc s. revert nc. induction s as [|c s IH]; intros nc k l H; cbn in H; [discriminate|].
  destruct (is_ws c).
  - destruct (tok_next nc s) eqn:E; cbn in H; try discriminate. injection H as <- <-.
    destruct (IH _ _ _ E). cbn. lia.
  - destruct (is_tchar c).
    + destruct nc; [discriminate|]. injection H as <- <-. pose proof (tspan_le s). cbn. lia.
    + destruct (c =? 44); [|discriminate].
      destruct (tok_next false s) eqn:E; cbn in H; try discriminate. injection H as <- <-.
      destruct (IH _ _ _ E). cbn. lia.
Qed.

Lemma tspan_tchar : forall s j, (j < tspan s)%nat -> is_tchar (nth j s 0) = true.
Proof.
  induction s as [|c s IH]; intros j Hj; cbn in Hj; [lia|].
  destruct (is_tchar c) eqn:T; [|lia]. destruct j as [|j]; cbn; [exact T|]. apply IH. lia.
Qed.

Lemma tok_next_tok_chars : forall nc s k l, tok_next nc s = TK_tok k l ->
  forall j, (k <= j < k + l)%nat -> is_tchar (nth j s 0) = true.
Proof.
  intros nc s. revert nc. induction s as [|c s IH]; intros nc k l H j Hj; cbn in H; [discriminate|].
  destruct (is_ws c).
  - destruct (tok_next nc s) eqn:E; cbn in H; try discriminate. injection H as <- <-.
    destruct j as [|j]; [lia|]. cbn. eapply IH; [exact E | lia].
  - destruct (is_tchar c) eqn:T.
    + destruct nc; [discriminate|]. injection H as <- <-.
      destruct j as [|j]; cbn; [exact T|]. apply tspan_tchar. lia.
    + destruct (c =? 44); [|discriminate].
      destruct (tok_next false s) eqn:E; cbn in H; try discriminate. injection H as <- <-.
      destruct j as [|j]; [lia|]. cbn. eapply IH; [exact E | lia].
Qed.

Lemma tl_ieqb_length : forall a b, tl_ieqb a b = true -> length a = length b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; try reflexivity.
  apply andb_prop in H. destruct H as [_ H]. cbn. f_equal. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Fixpoint wspan (s : list Z) : nat :=
  match s with
  | c :: s' => if is_ws c then S (wspan s') else 0%nat
  | [] => 0%nat
  end.

Lemma wspan_le : forall s, (wspan s <= length s)%nat.
Proof. induction s as [|c s IH]; cbn; [lia|]. destruct (is_ws c); lia. Qed.

Lemma wspan_ws : forall s j, (j < wspan s)%nat -> is_ws (nth j s 0) = true.
Proof.
  induction s as [|c s IH]; intros j Hj; cbn in Hj; [lia|].
  destruct (is_ws c) eqn:W; [|lia]. destruct j as [|j]; cbn; [exact W|]. apply IH. lia.
Qed.

Lemma wspan_stop : forall s, (wspan s < length s)%nat -> is_ws (nth (wspan s) s 0) = false.
Proof.
  induction s as [|c s IH]; intros H; cbn in H |- *; [lia|].
  destruct (is_ws c) eqn:W; [| exact W]. cbn. apply IH. lia.
Qed.

(* [comment removed for export] *)
Fixpoint tk_shiftn (n : nat) (r : tokres) : tokres := match n with 0%nat => r | S n' => tk_shift (tk_shiftn n' r) end.

Lemma tok_next_wspan : forall nc s, tok_next nc s = tk_shiftn (wspan s) (tok_next nc (skipn (wspan s) s)).
Proof.
  intros nc s. revert nc. induction s as [|c s IH]; intros nc; [reflexivity|].
  cbn [wspan]. destruct (is_ws c) eqn:W.
  - cbn [tk_shiftn skipn]. rewrite <- IH. cbn [tok_next]. rewrite W. reflexivity.
  - cbn [tk_shiftn skipn]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition tokit_cells_after (r : tokres) (it0 last : Z) : list cell :=
  match r with
  | TK_tok k l => TokItCells (it0 + Z.of_nat k) (Z.of_nat l) (it0 + Z.of_nat k + Z.of_nat l) it0 last
  | _ => TokItCells 0 0 last last last
  end.

(* [comment removed for export] *)
Definition optit_cells_after (r : tokres) (lst it0 err : Z) (pad7 : list byte) : list cell :=
  match r with
  | TK_end => OptItCells lst 0 0 0 err pad7
  | TK_err => OptItCells lst 0 0 0 1 pad7
  | TK_tok k l => OptItCells lst (it0 + Z.of_nat k + Z.of_nat l) (it0 + Z.of_nat k) (Z.of_nat l) err pad7
  end.

(* [comment removed for export] *)
Definition tok_suffix (W p : Z) (wbs : list byte) : list Z := zbytes (skipn (Z.to_nat (p - W)) wbs).

Definition SZ_TOKIT : Z := 40.
Definition TOKIT_STACK : Z := 64.                 (* [comment removed for export] *)
Definition VALIDATE_LIST_STACK : Z := 144.        (* [comment removed for export] *)
Definition FINDIF_STACK : Z := 128.               (* [comment removed for export] *)
Definition TOKEN_LIST_EXISTS_STACK : Z := 320.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_UB_SKIP_OWS : Z := 0x359e0.

Definition skip_ows_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (C p La W : Z) (wbs : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz C) (wz La) a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(C, C + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' C [C8 (wz (p + Z.of_nat (wspan (tok_suffix W p wbs))))]
    /\ bytes_at usegs m' W wbs.

Definition skip_ows_stmt : Prop :=
  forall (C p La W : Z) (wbs : list byte)
    ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells usegs m C [C8 (wz p)] ->
  bytes_at usegs m W wbs -> W <= p <= La -> La = W + Z.of_nat (length wbs) -> La < 2^64 ->
  (C + 8 <= W \/ W + Z.of_nat (length wbs) <= C) ->
  ((0 < length wbs)%nat -> 0 < W) ->                                            (* [comment removed for export] *)
  mem_inv usegs m ->
  evt usegs (skip_ows_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc C p La W wbs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz C) (wz La) a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_UB_SKIP_OWS) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tokit_ctor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A Fi La W : Z) (wbs : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (A, A + SZ_TOKIT)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' A (tokit_cells_after (tok_next false (tok_suffix W Fi wbs)) Fi La)
    /\ bytes_at usegs m' W wbs.

Definition tokit_ctor_stmt : Prop :=
  forall (A Fi La W : Z) (wbs : list byte) (cs : list cell) (lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells usegs m A cs -> cells_size cs = 40%nat ->
  bytes_at usegs m W wbs -> W <= Fi <= La -> La = W + Z.of_nat (length wbs) -> La < 2^64 ->
  (A + SZ_TOKIT <= W \/ W + Z.of_nat (length wbs) <= A) ->
  (* [comment removed for export] *)
  stk usegs m lo (bv_unsigned sp) -> lo + TOKIT_STACK <= bv_unsigned sp -> 0xb8000 <= lo ->
  (bv_unsigned sp <= A \/ A + SZ_TOKIT <= lo) -> (bv_unsigned sp <= W \/ W + Z.of_nat (length wbs) <= lo) ->
  ((0 < length wbs)%nat -> 0 < W) ->                                            (* [comment removed for export] *)
  mem_inv usegs m ->
  evt usegs (tokit_ctor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A Fi La W wbs lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz Fi) (wz La) a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_TOKEN_LIST_ITER_CTOR) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tokit_incr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A it fst La W : Z) (wbs : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (A, A + SZ_TOKIT)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' A (tokit_cells_after (tok_next (negb (it =? fst)) (tok_suffix W it wbs)) it La)
    /\ bytes_at usegs m' W wbs.

Definition tokit_incr_stmt : Prop :=
  forall (A vp vl it fst La W : Z) (wbs : list byte) (lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells usegs m A (TokItCells vp vl it fst La) ->
  bytes_at usegs m W wbs -> W <= it <= La -> La = W + Z.of_nat (length wbs) -> La < 2^64 -> 0 <= fst < 2^64 ->
  (A + SZ_TOKIT <= W \/ W + Z.of_nat (length wbs) <= A) ->
  (* [comment removed for export] *)
  stk usegs m lo (bv_unsigned sp) -> lo + TOKIT_STACK <= bv_unsigned sp -> 0xb8000 <= lo ->
  (bv_unsigned sp <= A \/ A + SZ_TOKIT <= lo) -> (bv_unsigned sp <= W \/ W + Z.of_nat (length wbs) <= lo) ->
  ((0 < length wbs)%nat -> 0 < W) ->                                            (* [comment removed for export] *)
  mem_inv usegs m ->
  evt usegs (tokit_incr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A it fst La W wbs lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_TOKEN_LIST_ITER_INCR) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition optit_incr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A lst it err SP : Z) (pad7 : list byte) (sbs : list byte) (lrest : list cell) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (A, A + SZ_TOKIT)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' A (optit_cells_after (tok_next (negb (it =? SP)) (tok_suffix SP it sbs)) lst it err pad7)
    /\ rw_cells usegs m' lst (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: lrest)
    /\ bytes_at usegs m' SP sbs.

Definition optit_incr_stmt : Prop :=
  forall (A lst it vp vl err SP : Z) (pad7 : list byte) (sbs : list byte) (lrest : list cell) (lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells usegs m A (OptItCells lst it vp vl err pad7) ->
  rw_cells usegs m lst (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: lrest) ->
  bytes_at usegs m SP sbs -> SP <= it <= SP + Z.of_nat (length sbs) -> SP + Z.of_nat (length sbs) < 2^64 ->
  (A + SZ_TOKIT <= SP \/ SP + Z.of_nat (length sbs) <= A) ->
  (A + SZ_TOKIT <= lst \/ lst + Z.of_nat (cells_size (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: lrest)) <= A) ->
  (* [comment removed for export] *)
  stk usegs m lo (bv_unsigned sp) -> lo + TOKIT_STACK <= bv_unsigned sp -> 0xb8000 <= lo ->
  (bv_unsigned sp <= A \/ A + SZ_TOKIT <= lo) -> (bv_unsigned sp <= SP \/ SP + Z.of_nat (length sbs) <= lo) ->
  (bv_unsigned sp <= lst \/ lst + Z.of_nat (cells_size (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: lrest)) <= lo) ->
  ((0 < length sbs)%nat -> 0 < SP) ->                                           (* [comment removed for export] *)
  0 < lst -> lst mod 8 = 0 ->                                                 (* [comment removed for export] *)
  mem_inv usegs m ->
  evt usegs (optit_incr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A lst it err SP pad7 sbs lrest lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_OPT_TOKEN_LIST_INCR) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition validate_list_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LST SP : Z) (sbs : list byte) (lrest : list cell) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (if opt_token_list_valid (zbytes sbs) then 1 else 0)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' LST (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: lrest)
    /\ bytes_at usegs m' SP sbs.

Definition validate_list_stmt : Prop :=
  forall (LST SP : Z) (sbs : list byte) (lrest : list cell) (lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells usegs m LST (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: lrest) ->
  bytes_at usegs m SP sbs -> SP + Z.of_nat (length sbs) < 2^64 ->
  stk usegs m lo (bv_unsigned sp) -> lo + VALIDATE_LIST_STACK <= bv_unsigned sp -> 0xb8000 <= lo ->
  (bv_unsigned sp <= LST \/ LST + Z.of_nat (cells_size (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: lrest)) <= lo) ->
  (bv_unsigned sp <= SP \/ SP + Z.of_nat (length sbs) <= lo) ->
  ((0 < length sbs)%nat -> 0 < SP) ->                                           (* [comment removed for export] *)
  0 < LST -> LST mod 8 = 0 ->                                                 (* [comment removed for export] *)
  mem_inv usegs m ->
  evt usegs (validate_list_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LST SP sbs lrest lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz LST) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_VALIDATE_OPT_TOKEN_LIST) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_UB_TL_FINDIF : Z := 0x36b30.

Definition findif_found (t : list Z) (r : tokres) (i : nat) (s : list Z) : bool :=
  match r with
  | TK_tok k l => tl_ieqb t (firstn l (skipn (i + k) s))
                  || existsb (tl_ieqb t) (toks_from (S (length s - (i + k + l))) true (skipn (i + k + l) s))
  | _ => false
  end.

Definition findif_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R IT EA T SP TP : Z) (sbs tbs : list byte) (trest : list cell) (r : tokres) (i : nat) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (vp vl itv fv : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (R, R + SZ_TOKIT); (IT, IT + SZ_TOKIT)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' R (TokItCells vp vl itv fv (SP + Z.of_nat (length sbs)))
    /\ rw_cells usegs m' IT (TokItCells vp vl itv fv (SP + Z.of_nat (length sbs)))
    /\ rw_cells usegs m' EA (TokItCells 0 0 (SP + Z.of_nat (length sbs)) (SP + Z.of_nat (length sbs)) (SP + Z.of_nat (length sbs)))
    /\ rw_cells usegs m' T (C8 (wz TP) :: C8 (wz (Z.of_nat (length tbs))) :: trest)
    /\ bytes_at usegs m' SP sbs /\ bytes_at usegs m' TP tbs
    /\ 0 <= itv < 2^64 /\ 0 <= fv < 2^64
    /\ findif_found (zbytes tbs) r i (zbytes sbs) = negb ((itv =? SP + Z.of_nat (length sbs)) && (fv =? SP + Z.of_nat (length sbs))).

Definition findif_stmt : Prop :=
  forall (R IT EA T SP TP : Z) (sbs tbs : list byte) (trest rjunk : list cell) (r : tokres) (i : nat) (lo hi : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells usegs m R rjunk -> cells_size rjunk = 40%nat ->
  rw_cells usegs m IT (tokit_cells_after r (SP + Z.of_nat i) (SP + Z.of_nat (length sbs))) ->
  (i <= length sbs)%nat -> (forall k l, r = TK_tok k l -> (i + k + l <= length sbs)%nat /\ (1 <= l)%nat) ->
  rw_cells usegs m EA (TokItCells 0 0 (SP + Z.of_nat (length sbs)) (SP + Z.of_nat (length sbs)) (SP + Z.of_nat (length sbs))) ->
  rw_cells usegs m T (C8 (wz TP) :: C8 (wz (Z.of_nat (length tbs))) :: trest) ->
  bytes_at usegs m SP sbs -> bytes_at usegs m TP tbs -> SP + Z.of_nat (length sbs) < 2^64 -> TP + Z.of_nat (length tbs) < 2^64 ->
  stk usegs m lo (bv_unsigned sp) -> lo + FINDIF_STACK <= bv_unsigned sp -> 0xb8000 <= lo ->
  (* [comment removed for export] *)
  bv_unsigned sp <= EA -> EA + SZ_TOKIT <= IT -> IT + SZ_TOKIT <= R -> R + SZ_TOKIT <= hi ->
  (hi <= T \/ T + Z.of_nat (cells_size (C8 (wz TP) :: C8 (wz (Z.of_nat (length tbs))) :: trest)) <= lo) ->
  (hi <= SP \/ SP + Z.of_nat (length sbs) <= lo) -> (hi <= TP \/ TP + Z.of_nat (length tbs) <= lo) ->
  ((0 < length sbs)%nat -> 0 < SP) -> ((0 < length tbs)%nat -> 0 < TP) ->      (* [comment removed for export] *)
  IT mod 8 = 0 -> EA mod 8 = 0 ->                                               (* [comment removed for export] *)
  mem_inv usegs m ->
  evt usegs (findif_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R IT EA T SP TP sbs tbs trest r i lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz R) (wz IT) (wz EA) (wz T) a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_UB_TL_FINDIF) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition token_list_exists_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (TL T SP TP : Z) (sbs tbs : list byte) (tlrest trest : list cell) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (if token_list_exists (zbytes sbs) (zbytes tbs) then 1 else 0))
                  a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' TL (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: tlrest)
    /\ rw_cells usegs m' T (C8 (wz TP) :: C8 (wz (Z.of_nat (length tbs))) :: trest)
    /\ bytes_at usegs m' SP sbs /\ bytes_at usegs m' TP tbs.

Definition token_list_exists_stmt : Prop :=
  forall (TL T SP TP : Z) (sbs tbs : list byte) (tlrest trest : list cell) (lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells usegs m TL (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: tlrest) ->
  rw_cells usegs m T (C8 (wz TP) :: C8 (wz (Z.of_nat (length tbs))) :: trest) ->
  bytes_at usegs m SP sbs -> bytes_at usegs m TP tbs -> SP + Z.of_nat (length sbs) < 2^64 -> TP + Z.of_nat (length tbs) < 2^64 ->
  stk usegs m lo (bv_unsigned sp) -> lo + TOKEN_LIST_EXISTS_STACK <= bv_unsigned sp -> 0xb8000 <= lo ->
  (bv_unsigned sp <= TL \/ TL + Z.of_nat (cells_size (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: tlrest)) <= lo) ->
  (bv_unsigned sp <= T \/ T + Z.of_nat (cells_size (C8 (wz TP) :: C8 (wz (Z.of_nat (length tbs))) :: trest)) <= lo) ->
  (bv_unsigned sp <= SP \/ SP + Z.of_nat (length sbs) <= lo) ->
  (bv_unsigned sp <= TP \/ TP + Z.of_nat (length tbs) <= lo) ->
  ((0 < length sbs)%nat -> 0 < SP) -> ((0 < length tbs)%nat -> 0 < TP) ->        (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 ->                                                (* [comment removed for export] *)
  mem_inv usegs m ->
  evt usegs (token_list_exists_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc TL T SP TP sbs tbs tlrest trest lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz TL) (wz T) a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_TOKEN_LIST_EXISTS) fc None m (seg_rom usegs)).

End HCW.
