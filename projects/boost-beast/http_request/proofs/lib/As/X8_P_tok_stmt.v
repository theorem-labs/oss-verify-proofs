(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXRep AXRep2 AXPRep AXPRep2 AXRep_leafP.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8LeafKit.
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
Lemma skipn_at_nth' : forall {X} (l : list X) j x, nth_error l j = Some x -> skipn j l = x :: skipn (S j) l.
Proof.
  intros X l. induction l as [|y l IH]; intros [|j] x H; cbn in H |- *; try discriminate.
  - inversion H. reflexivity.
  - apply IH. exact H.
Qed.

Lemma zbytes_skipn : forall j bs, zbytes (skipn j bs) = skipn j (zbytes bs).
Proof. intros j bs. unfold zbytes. rewrite skipn_map. reflexivity. Qed.

Lemma skipn_zbytes_nth : forall bs j b, nth_error bs j = Some b -> skipn j (zbytes bs) = zb b :: skipn (S j) (zbytes bs).
Proof. intros bs j b N. rewrite <- !zbytes_skipn, (skipn_at_nth' bs j b N). reflexivity. Qed.

Lemma length_zbytes : forall bs, length (zbytes bs) = length bs.
Proof. intros bs. unfold zbytes. apply length_map. Qed.

Lemma tspan_cons_t : forall c s, is_tchar c = true -> tspan (c :: s) = S (tspan s).
Proof. intros c s H. cbn. rewrite H. reflexivity. Qed.
Lemma tspan_cons_f : forall c s, is_tchar c = false -> tspan (c :: s) = 0%nat.
Proof. intros c s H. cbn. rewrite H. reflexivity. Qed.

Lemma ws_not_tchar : forall c, is_ws c = true -> is_tchar c = false.
Proof.
  intros c H. unfold is_ws in H. apply Bool.orb_true_iff in H. destruct H as [H|H]; apply Z.eqb_eq in H; subst; reflexivity.
Qed.
Lemma comma_not_tchar : is_tchar 44 = false. Proof. reflexivity. Qed.
Lemma comma_not_ws : is_ws 44 = false. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma tok_next_ws : forall nc c s, is_ws c = true -> tok_next nc (c :: s) = tk_shift (tok_next nc s).
Proof. intros nc c s H. cbn. rewrite H. reflexivity. Qed.
Lemma tok_next_tchar : forall nc c s, is_ws c = false -> is_tchar c = true ->
  tok_next nc (c :: s) = if nc then TK_err else TK_tok 0 (S (tspan s)).
Proof. intros nc c s H1 H2. cbn. rewrite H1, H2. reflexivity. Qed.
Lemma tok_next_comma : forall nc s, tok_next nc (44 :: s) = tk_shift (tok_next false s).
Proof. intros nc s. reflexivity. Qed.
Lemma tok_next_other : forall nc c s, is_ws c = false -> is_tchar c = false -> c <> 44 -> tok_next nc (c :: s) = TK_err.
Proof.
  intros nc c s H1 H2 H3. cbn. rewrite H1, H2. replace (c =? 44) with false by (symmetry; apply Z.eqb_neq; exact H3). reflexivity.
Qed.


(* [comment removed for export] *)
Lemma tchar_load : forall c, 0 <= c < 256 ->
  zxb (Z_to_bv 8 (nth (Z.to_nat c) TAB_IS_TOKEN_CHAR 0)) = wz (if is_tchar c then 1 else 0).
Proof.
  intros c Hc. unfold is_tchar. pose proof (tchar01 c) as H.
  remember (nth (Z.to_nat c) TAB_IS_TOKEN_CHAR 0) as v eqn:EV. clear EV.
  assert (E : v = 0 \/ v = 1) by lia. destruct E as [-> | ->]; reflexivity.
Qed.
Lemma tchar_not_ws : forall c, is_tchar c = true -> is_ws c = false.
Proof. intros c H. destruct (is_ws c) eqn:W; [| reflexivity]. rewrite (ws_not_tchar c W) in H. discriminate. Qed.

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
Definition TOKIT_STACK : Z := 80 + AINTRIN_STACK.           (* [comment removed for export] *)
Definition VALIDATE_LIST_STACK : Z := 64 + TOKIT_STACK.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tokit_ctor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A Fi La W lo : Z) (wbs : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',          (* [comment removed for export] *)
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (A, A + SZ_TOKIT)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' A (tokit_cells_after (tok_next false (tok_suffix W Fi wbs)) Fi La)
    /\ bytes_at asegs m' W wbs
    /\ ACONST m' /\ aobj m' A SZ_TOKIT /\ accessible m' W (Z.of_nat (length wbs)).     (* [comment removed for export] *)

Definition tokit_ctor_stmt : Prop :=
  forall (A Fi La W lo : Z) (wbs : list byte) (cs : list cell)
    ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells asegs m A cs -> cells_size cs = 40%nat ->
  bytes_at asegs m W wbs -> W <= Fi <= La -> La = W + Z.of_nat (length wbs) -> La < 2^64 ->
  (A + SZ_TOKIT <= W \/ W + Z.of_nat (length wbs) <= A) ->
  stk asegs m lo (bv_unsigned sp) -> lo + TOKIT_STACK <= bv_unsigned sp -> aceil <= lo ->      (* [comment removed for export] *)
  (bv_unsigned sp <= A \/ A + SZ_TOKIT <= lo) ->
  (bv_unsigned sp <= W \/ W + Z.of_nat (length wbs) <= lo) ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  ACONST m -> aobj m A SZ_TOKIT -> A mod 8 = 0 -> accessible m W (Z.of_nat (length wbs)) ->
  evt asegs (tokit_ctor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A Fi La W lo wbs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz Fi) (wz La) a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_TOKEN_LIST_ITER_CTOR) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tokit_incr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A it fst La W lo : Z) (wbs : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (A, A + SZ_TOKIT)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' A (tokit_cells_after (tok_next (negb (it =? fst)) (tok_suffix W it wbs)) it La)
    /\ bytes_at asegs m' W wbs
    /\ ACONST m' /\ aobj m' A SZ_TOKIT /\ accessible m' W (Z.of_nat (length wbs)).     (* [comment removed for export] *)

Definition tokit_incr_stmt : Prop :=
  forall (A vp vl it fst La W lo : Z) (wbs : list byte)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells asegs m A (TokItCells vp vl it fst La) ->
  bytes_at asegs m W wbs -> W <= it <= La -> La = W + Z.of_nat (length wbs) -> La < 2^64 -> 0 <= fst < 2^64 ->
  (A + SZ_TOKIT <= W \/ W + Z.of_nat (length wbs) <= A) ->
  stk asegs m lo (bv_unsigned sp) -> lo + TOKIT_STACK <= bv_unsigned sp -> aceil <= lo ->      (* [comment removed for export] *)
  (bv_unsigned sp <= A \/ A + SZ_TOKIT <= lo) ->
  (bv_unsigned sp <= W \/ W + Z.of_nat (length wbs) <= lo) ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  ACONST m -> aobj m A SZ_TOKIT -> A mod 8 = 0 -> accessible m W (Z.of_nat (length wbs)) ->
  evt asegs (tokit_incr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A it fst La W lo wbs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_TOKEN_LIST_ITER_INCR) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition optit_incr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A lst it err SP lo : Z) (pad7 : list byte) (sbs : list byte) (lrest : list cell) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',          (* [comment removed for export] *)
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (A, A + SZ_TOKIT)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' A (optit_cells_after (tok_next (negb (it =? SP)) (tok_suffix SP it sbs)) lst it err pad7)
    /\ rw_cells asegs m' lst (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: lrest)
    /\ bytes_at asegs m' SP sbs
    /\ ACONST m' /\ aobj m' A SZ_TOKIT /\ accessible m' SP (Z.of_nat (length sbs)) /\ accessible m' lst 16.     (* [comment removed for export] *)

Definition optit_incr_stmt : Prop :=
  forall (A lst it vp vl err SP lo : Z) (pad7 : list byte) (sbs : list byte) (lrest : list cell)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells asegs m A (OptItCells lst it vp vl err pad7) ->
  rw_cells asegs m lst (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: lrest) ->
  bytes_at asegs m SP sbs -> SP <= it <= SP + Z.of_nat (length sbs) -> SP + Z.of_nat (length sbs) < 2^64 ->
  (A + SZ_TOKIT <= SP \/ SP + Z.of_nat (length sbs) <= A) ->
  (A + SZ_TOKIT <= lst \/ lst + Z.of_nat (cells_size (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: lrest)) <= A) ->
  stk asegs m lo (bv_unsigned sp) -> lo + TOKIT_STACK <= bv_unsigned sp -> aceil <= lo ->      (* [comment removed for export] *)
  (bv_unsigned sp <= A \/ A + SZ_TOKIT <= lo) ->
  (bv_unsigned sp <= SP \/ SP + Z.of_nat (length sbs) <= lo) ->
  (bv_unsigned sp <= lst \/ lst + Z.of_nat (cells_size (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: lrest)) <= lo) ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  ACONST m -> aobj m A SZ_TOKIT -> A mod 8 = 0 -> accessible m SP (Z.of_nat (length sbs)) ->
  accessible m lst 16 -> lst mod 8 = 0 ->
  evt asegs (optit_incr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A lst it err SP lo pad7 sbs lrest m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_OPT_TOKEN_LIST_INCR) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition validate_list_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LST SP : Z) (sbs : list byte) (lrest : list cell) (lo shi : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (if opt_token_list_valid (zbytes sbs) then 1 else 0)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' LST (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: lrest)
    /\ bytes_at asegs m' SP sbs
    /\ ACONST m' /\ stack0 m' lo shi.                                  (* [comment removed for export] *)

Definition validate_list_stmt : Prop :=
  forall (LST SP : Z) (sbs : list byte) (lrest : list cell) (lo shi : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells asegs m LST (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: lrest) ->
  bytes_at asegs m SP sbs -> SP + Z.of_nat (length sbs) < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo + VALIDATE_LIST_STACK <= bv_unsigned sp -> aceil <= lo ->   (* [comment removed for export] *)
  (bv_unsigned sp <= LST \/ LST + Z.of_nat (cells_size (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: lrest)) <= lo) ->
  (bv_unsigned sp <= SP \/ SP + Z.of_nat (length sbs) <= lo) ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 ->
  ACONST m -> stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
  accessible m SP (Z.of_nat (length sbs)) -> accessible m LST 16 -> LST mod 8 = 0 ->
  evt asegs (validate_list_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LST SP sbs lrest lo shi m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz LST) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_VALIDATE_OPT_TOKEN_LIST) fc None m (seg_rom asegs)).

End HCW.
