(** * ZReproQ6F — Q6 stage 2: the FIXED tables agree with canonical decode.

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-19; claimed in
    the window registry).  The keystone's final three-class form
    (settled with an earlier development run/an earlier development run: SYMBOL op&64=0, EOB op=96/val=0,
    EXCLUDED op&64<>0/op<>96) instantiated at the two inffixed.h literal
    tables — decided by one vm_compute each, then extracted to the
    consumer-shaped forall with the [In (codeword, sym) (code_table ...)]
    facts [Huff.hdecode_complete] eats.

    The codeword spelling is the agreed stream-order form:
    [write_bits (c_bits E) (idx mod 2^(c_bits E))] — replication across
    the 9-bit (resp. 5-bit) root is quotiented by the mod.  The pair
    correspondence is stated directly against [decode_lit_len]'s own
    arrays ([length_base]/[length_extra], [dist_base]/[dist_extra]), so
    the walk's LEN-arm agreement needs no further array bridging.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec InflateFast Inflate.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Reflection plumbing.
   ========================================================================== *)

Fixpoint zr_blist_eqb (a b : list bool) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Bool.eqb x y && zr_blist_eqb a' b'
  | _, _ => false
  end.

Lemma zr_blist_eqb_eq : forall a b, zr_blist_eqb a b = true -> a = b.
Proof.
  induction a as [|x a' IH]; intros [|y b'] H; try discriminate;
    [reflexivity|].
  cbn in H. apply andb_prop in H as [Hx Hr].
  apply eqb_prop in Hx. f_equal; auto.
Qed.

Fixpoint zr_tbl_find (cw : list bool) (t : list (list bool * nat))
  : option nat :=
  match t with
  | [] => None
  | (c, s) :: t' => if zr_blist_eqb cw c then Some s else zr_tbl_find cw t'
  end.

Lemma zr_tbl_find_in : forall cw t s,
  zr_tbl_find cw t = Some s -> In (cw, s) t.
Proof.
  intros cw t; induction t as [|[c s0] t' IH]; intros s H; [discriminate|].
  cbn in H. destruct (zr_blist_eqb cw c) eqn:E.
  - injection H as <-. left. f_equal. symmetry. now apply zr_blist_eqb_eq.
  - right. now apply IH.
Qed.

(** The agreed stream-order codeword of the entry at [idx]. *)
Definition zr_cw (E : Code) (idx : Z) : list bool :=
  write_bits (Z.to_nat (c_bits E)) (idx mod 2 ^ c_bits E).

(* ==========================================================================
   1b. FAST-SHADOW hoist (fastshadow/ZReproQ6F, 2026-08-31).

   [code_table] is quadratic (its own COMPLEXITY note in Huff.v) and was
   recomputed at EVERY index inside [zr_lenfix_all]'s decision vm_compute —
   512 builds, PAID TWICE (tactic pass + Qed vm-cast recheck): the census's
   only two hot commands, 159.9 s + 158.8 s of the 320.8 s total.  Build the
   literal/length table ONCE as a literal constant, prove the checker
   pointwise equal to a literal-table twin, and decide the twin.  The
   distfix decision is sub-second (30-symbol table, 32 indices) and is left
   untouched.  NO existing statement, name, or definition changes;
   consumers see the identical lemmas.
   ========================================================================== *)

Definition zrf_lit_table : list (list bool * nat) :=
  Eval vm_compute in code_table fixed_lit_lengths 15%nat.

Lemma zrf_lit_table_eq : code_table fixed_lit_lengths 15%nat = zrf_lit_table.
Proof. vm_compute. reflexivity. Qed.

Lemma zrf_forallb_ext : forall (A : Type) (f g : A -> bool) (l : list A),
  (forall a, f a = g a) -> forallb f l = forallb g l.
Proof.
  intros A f g l H; induction l as [|x l IH]; cbn [forallb];
    [reflexivity | now rewrite H, IH].
Qed.

(* ==========================================================================
   2.  The checkers, in the final three-class form.
   ========================================================================== *)

Definition zr_len_pair_ok (E : Code) (sym : nat) : bool :=
  if (sym <? 256)%nat then (c_op E =? 0) && (c_val E =? Z.of_nat sym)
  else if (sym =? 256)%nat then false  (* EOB belongs to the op-96 class *)
  else match nth_error length_base (sym - 257)%nat,
             nth_error length_extra (sym - 257)%nat with
       | Some b0, Some e0 =>
           (c_val E =? Z.of_nat b0) && (c_op E =? 16 + Z.of_nat e0)
       | _, _ => false
       end.

Definition zr_lenfix_ok_at (i : nat) : bool :=
  let idx := Z.of_nat i in
  let E := lenfix idx in
  if Z.land (c_op E) 64 =? 0 then
    (1 <=? c_bits E) && (c_bits E <=? 9)
    && match zr_tbl_find (zr_cw E idx)
               (code_table fixed_lit_lengths 15%nat) with
       | Some sym => zr_len_pair_ok E sym
       | None => false
       end
  else if (c_op E =? 96) && (c_val E =? 0) then
    (1 <=? c_bits E) && (c_bits E <=? 9)
    && match zr_tbl_find (zr_cw E idx)
               (code_table fixed_lit_lengths 15%nat) with
       | Some sym => (sym =? 256)%nat
       | None => false
       end
  else true.

Definition zr_dist_pair_ok (E : Code) (sym : nat) : bool :=
  match nth_error dist_base sym, nth_error dist_extra sym with
  | Some b0, Some e0 =>
      (c_val E =? Z.of_nat b0) && (c_op E =? 16 + Z.of_nat e0)
  | _, _ => false
  end.

Definition zr_distfix_ok_at (i : nat) : bool :=
  let idx := Z.of_nat i in
  let E := distfix idx in
  if Z.land (c_op E) 64 =? 0 then
    (1 <=? c_bits E) && (c_bits E <=? 5)
    && match zr_tbl_find (zr_cw E idx)
               (code_table fixed_dist_lengths 15%nat) with
       | Some sym => zr_dist_pair_ok E sym
       | None => false
       end
  else true.  (* distfix has no EOB class; its two op-64 slots are excluded *)

(* FAST-SHADOW twin (lenfix only — the census's two hot commands both live in
   [zr_lenfix_all]; the distfix decision is sub-second and stays untouched):
   byte-identical body except the two [code_table fixed_lit_lengths 15]
   occurrences are the hoisted literal constant. *)
Definition zrf_lenfix_ok_at (i : nat) : bool :=
  let idx := Z.of_nat i in
  let E := lenfix idx in
  if Z.land (c_op E) 64 =? 0 then
    (1 <=? c_bits E) && (c_bits E <=? 9)
    && match zr_tbl_find (zr_cw E idx) zrf_lit_table with
       | Some sym => zr_len_pair_ok E sym
       | None => false
       end
  else if (c_op E =? 96) && (c_val E =? 0) then
    (1 <=? c_bits E) && (c_bits E <=? 9)
    && match zr_tbl_find (zr_cw E idx) zrf_lit_table with
       | Some sym => (sym =? 256)%nat
       | None => false
       end
  else true.

Lemma zrf_lenfix_ok_at_eq : forall i, zr_lenfix_ok_at i = zrf_lenfix_ok_at i.
Proof.
  intro i. unfold zr_lenfix_ok_at, zrf_lenfix_ok_at. cbv zeta.
  now rewrite zrf_lit_table_eq.
Qed.

(** THE two decisions. *)
Lemma zr_lenfix_all : forallb zr_lenfix_ok_at (seq 0 512) = true.
Proof.
  transitivity (forallb zrf_lenfix_ok_at (seq 0 512)).
  - exact (zrf_forallb_ext nat zr_lenfix_ok_at zrf_lenfix_ok_at
             (seq 0 512) zrf_lenfix_ok_at_eq).
  - vm_compute. reflexivity.
Qed.

Lemma zr_distfix_all : forallb zr_distfix_ok_at (seq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   3.  Consumer-shaped extraction.
   ========================================================================== *)

Lemma zr_lenfix_canon : forall idx,
  0 <= idx < 512 ->
  (Z.land (c_op (lenfix idx)) 64 = 0 ->
     1 <= c_bits (lenfix idx) <= 9
     /\ exists sym,
          In (zr_cw (lenfix idx) idx, sym)
             (code_table fixed_lit_lengths 15%nat)
          /\ zr_len_pair_ok (lenfix idx) sym = true)
  /\ (c_op (lenfix idx) = 96 ->
     c_val (lenfix idx) = 0
     /\ 1 <= c_bits (lenfix idx) <= 9
     /\ In (zr_cw (lenfix idx) idx, 256%nat)
           (code_table fixed_lit_lengths 15%nat)).
Proof.
  intros idx Hidx.
  pose proof (proj1 (forallb_forall zr_lenfix_ok_at (seq 0 512))
                zr_lenfix_all (Z.to_nat idx)) as HF.
  rewrite in_seq in HF.
  specialize (HF ltac:(lia)).
  unfold zr_lenfix_ok_at in HF. cbv zeta in HF.
  rewrite Z2Nat.id in HF by lia.
  split.
  - intro Hop. rewrite (proj2 (Z.eqb_eq _ _) Hop) in HF.
    apply andb_prop in HF as [HB HT].
    apply andb_prop in HB as [HB1 HB2].
    apply Z.leb_le in HB1. apply Z.leb_le in HB2.
    split; [lia|].
    destruct (zr_tbl_find (zr_cw (lenfix idx) idx)
                (code_table fixed_lit_lengths 15%nat)) as [sym|] eqn:EF;
      [|discriminate].
    exists sym. split; [now apply zr_tbl_find_in | exact HT].
  - intro Hop.
    (* val = 0 first, by its own reflection pass *)
    assert (HV : c_val (lenfix idx) = 0).
    { assert (HD : forallb (fun i =>
                if c_op (lenfix (Z.of_nat i)) =? 96
                then c_val (lenfix (Z.of_nat i)) =? 0 else true)
                (seq 0 512) = true) by (vm_compute; reflexivity).
      pose proof (proj1 (forallb_forall _ (seq 0 512)) HD (Z.to_nat idx))
        as HD1.
      rewrite in_seq in HD1. specialize (HD1 ltac:(lia)).
      rewrite Z2Nat.id in HD1 by lia.
      rewrite (proj2 (Z.eqb_eq _ _) Hop) in HD1.
      now apply Z.eqb_eq. }
    assert (H64 : (Z.land (c_op (lenfix idx)) 64 =? 0) = false)
      by (rewrite Hop; reflexivity).
    rewrite H64 in HF. cbv beta iota in HF.
    rewrite Hop, HV in HF.
    change ((96 =? 96) && (0 =? 0)) with true in HF.
    cbv beta iota in HF.
    apply andb_prop in HF as [HB HT].
    apply andb_prop in HB as [HB1 HB2].
    apply Z.leb_le in HB1. apply Z.leb_le in HB2.
    split; [exact HV|]. split; [lia|].
    destruct (zr_tbl_find (zr_cw (lenfix idx) idx)
                (code_table fixed_lit_lengths 15%nat)) as [sym|] eqn:EF;
      [|discriminate].
    apply Nat.eqb_eq in HT. subst sym.
    now apply zr_tbl_find_in.
Qed.

Lemma zr_distfix_canon : forall idx,
  0 <= idx < 32 ->
  Z.land (c_op (distfix idx)) 64 = 0 ->
  1 <= c_bits (distfix idx) <= 5
  /\ exists sym,
       In (zr_cw (distfix idx) idx, sym)
          (code_table fixed_dist_lengths 15%nat)
       /\ zr_dist_pair_ok (distfix idx) sym = true.
Proof.
  intros idx Hidx Hop.
  pose proof (proj1 (forallb_forall zr_distfix_ok_at (seq 0 32))
                zr_distfix_all (Z.to_nat idx)) as HF.
  rewrite in_seq in HF.
  specialize (HF ltac:(lia)).
  unfold zr_distfix_ok_at in HF. cbv zeta in HF.
  rewrite Z2Nat.id in HF by lia.
  rewrite (proj2 (Z.eqb_eq _ _) Hop) in HF.
  apply andb_prop in HF as [HB HT].
  apply andb_prop in HB as [HB1 HB2].
  apply Z.leb_le in HB1. apply Z.leb_le in HB2.
  split; [lia|].
  destruct (zr_tbl_find (zr_cw (distfix idx) idx)
              (code_table fixed_dist_lengths 15%nat)) as [sym|] eqn:EF;
    [|discriminate].
  exists sym. split; [now apply zr_tbl_find_in | exact HT].
Qed.

Print Assumptions zr_lenfix_canon.
Print Assumptions zr_distfix_canon.
