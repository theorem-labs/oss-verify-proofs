(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: new for LPS 727298f3: the one generator of the auxiliary vector this tree's claims describe (auxv_vals, auxv_words_Z, auxv_vec_bytes and their lemmas), in the order StackLayout.auxv_entries writes it, 27 or 29 pairs by la_rseq, so the claim definitions cannot drift apart from each other or from the model. *)

(* THE TABLE.  [StackLayout.auxv_entries] writes, in this order:
     AT_SYSINFO_EHDR 33, then the eight riscv64 cache words 40 41 42 43 44 45 46 47,
     then AT_MINSIGSTKSZ 51  -- these ten are ARCH_DLINFO, which binfmt_elf.c expands
     before its own entries -- then 16 6 17 3 4 5 7 8 9 11 12 13 14 23, then
     AT_RANDOM 25 and AT_EXECFN 31, then AT_RSEQ_FEATURE_SIZE 27 and AT_RSEQ_ALIGN 28
     WHEN the kernel build has CONFIG_RSEQ, then AT_NULL 0.
   That is 27 pairs without the rseq pairs and 29 with, so the terminator's position is
   NOT a constant: [r] below is [la_rseq], and this tree does not pin it (the tree's own
   refusals to pin are at AsMainIfaceAuxv.v:248 and AsanPlanCore.v:4176).  AT_RANDOM is
   pair 24 in both shapes, because the two rseq pairs sit after AT_EXECFN.

   This file is a LEAF: it names only Stdlib and the model, never this tree's tactic or
   segment files, so every layer (Agent, Ref, Ub, As, Both/As) can read the same table. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
(* StackLayout is EXPORTED, not merely imported: a consumer of this table needs
   [auxv_count] and [auxv_entries] to state its own length facts, and this file is the
   one place the tree is meant to reach the model's auxv through. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Export StackLayout.
Import ListNotations.
Open Scope Z_scope.

(* The 24 value slots whose key is fixed.  AT_RANDOM and AT_EXECFN are arguments of
   [auxv_words_Z] rather than fields, because a claim quantifies over their addresses
   separately from the rest of the vector. *)
Record auxv_vals : Type := mkAuxv {
  ax_sysinfo : Z;
  ax_l1i     : Z;
  ax_l1ig    : Z;
  ax_l1d     : Z;
  ax_l1dg    : Z;
  ax_l2      : Z;
  ax_l2g     : Z;
  ax_l3      : Z;
  ax_l3g     : Z;
  ax_minsig  : Z;
  ax_hwcap   : Z;
  ax_pagesz  : Z;
  ax_clktck  : Z;
  ax_phdr    : Z;
  ax_phent   : Z;
  ax_phnum   : Z;
  ax_base    : Z;
  ax_flags   : Z;
  ax_entry   : Z;
  ax_uid     : Z;
  ax_euid    : Z;
  ax_gid     : Z;
  ax_egid    : Z;
  ax_secure  : Z
}.

(* The vector as a flat list of 64-bit values, key then value, lowest address first. *)
Definition auxv_words_Z (v : auxv_vals) (rnd execfn : Z) (r : bool) : list Z :=
  [33; ax_sysinfo v; 40; ax_l1i v; 41; ax_l1ig v; 42; ax_l1d v; 43; ax_l1dg v;
   44; ax_l2 v; 45; ax_l2g v; 46; ax_l3 v; 47; ax_l3g v; 51; ax_minsig v;
   16; ax_hwcap v; 6; ax_pagesz v; 17; ax_clktck v;
   3; ax_phdr v; 4; ax_phent v; 5; ax_phnum v;
   7; ax_base v; 8; ax_flags v; 9; ax_entry v;
   11; ax_uid v; 12; ax_euid v; 13; ax_gid v; 14; ax_egid v;
   23; ax_secure v; 25; rnd; 31; execfn]
  ++ (if r then [27; 28; 28; 32] else [])
  ++ [0; 0].

Definition auxv_list (v : auxv_vals) (rnd execfn : Z) (r : bool) : list word :=
  map (Z_to_bv 64) (auxv_words_Z v rnd execfn r).

(* The vector's byte length: 16 bytes a pair, 27 pairs or 29.  Named [auxv_vec_bytes]
   because Common/RefLayout already has an [auxv_bytes] for the model's byte list.
   Stated as a function of [r] with both arms, never as two pinned numerals, so that
   the length test (54/58 words, 432/464 bytes ported; 20 words, 160 bytes stale) reads
   off the definition without pinning kb_rseq. *)
Definition auxv_vec_bytes (r : bool) : Z := if r then 464 else 432.

Lemma length_auxv_words_Z : forall v rnd execfn r,
  length (auxv_words_Z v rnd execfn r) = (2 * auxv_count r)%nat.
Proof. intros v rnd execfn [|]; reflexivity. Qed.

Lemma length_auxv_list : forall v rnd execfn r,
  length (auxv_list v rnd execfn r) = (2 * auxv_count r)%nat.
Proof.
  intros v rnd execfn r. unfold auxv_list. rewrite length_map.
  apply length_auxv_words_Z.
Qed.

Lemma auxv_vec_bytes_length : forall v rnd execfn r,
  auxv_vec_bytes r = 8 * Z.of_nat (length (auxv_words_Z v rnd execfn r)).
Proof. intros v rnd execfn [|]; reflexivity. Qed.

(* For a consumer that only needs "the vector is short": [lia] cannot see through the
   [if], so hand it this and keep [r] opaque instead of case-splitting. *)
Lemma auxv_vec_bytes_range : forall r, 432 <= auxv_vec_bytes r <= 464.
Proof. intros [|]; unfold auxv_vec_bytes; lia. Qed.

(* ------------------------------------------------------------------ *)
(* THE KEYS ALONE, GENERATED                                           *)
(* ------------------------------------------------------------------ *)

(* AsMainIfaceAuxv carries a MIRROR of this table for its reflective [auxv_check].  Before
   the revision that mirror was hand-written and it drifted: it read pair 0 as key 3 while
   the plan read pair 13 as key 3 -- two incompatible readings of one address range.  The
   ruling in that file forbids hand-writing it a second time and names the remedy: ONE
   table generating both the claim list and the mirror.  [auxv_keys_gen] is that remedy --
   the mirror is the even positions of the very list the claims use, so the two cannot
   disagree without the kernel saying so. *)

(* Keys do not depend on the value record, so any record generates them; take the zero one. *)
Definition auxv_v0 : auxv_vals :=
  mkAuxv 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0.

Fixpoint auxv_evens (l : list Z) : list Z :=
  match l with
  | k :: _ :: t => k :: auxv_evens t
  | k :: nil => [k]
  | nil => nil
  end.

(* [auxv_count r] keys: the 26 claimed pairs, then AT_NULL.  The terminator is deliberately
   INCLUDED so a consumer bounded by [i < 26] never reaches it and no [firstn] is needed. *)
Definition auxv_keys_gen (r : bool) : list Z := auxv_evens (auxv_words_Z auxv_v0 0 0 r).

Lemma auxv_keys_gen_false :
  auxv_keys_gen false
  = [33; 40; 41; 42; 43; 44; 45; 46; 47; 51; 16; 6; 17; 3; 4; 5; 7; 8; 9; 11; 12; 13; 14; 23; 25; 31; 0].
Proof. reflexivity. Qed.

Lemma auxv_keys_gen_true :
  auxv_keys_gen true
  = [33; 40; 41; 42; 43; 44; 45; 46; 47; 51; 16; 6; 17; 3; 4; 5; 7; 8; 9; 11; 12; 13; 14; 23; 25; 31; 27; 28; 0].
Proof. reflexivity. Qed.

Lemma length_auxv_keys_gen : forall r, length (auxv_keys_gen r) = auxv_count r.
Proof. intros [|]; reflexivity. Qed.

(* The first 26 keys are the same under both kernel builds -- the two rseq pairs land after
   AT_EXECFN, so nothing before pair 26 moves.  This is what lets the mirror be stated
   without [r] while the vector's LENGTH still depends on it. *)
Lemma auxv_keys_gen_pre26 : forall r i,
  (i < 26)%nat -> nth i (auxv_keys_gen r) 0 = nth i (auxv_keys_gen false) 0.
Proof.
  intros [|] i Hi; [|reflexivity].
  do 26 (destruct i as [|i]; [reflexivity|]). exfalso. revert Hi. apply Nat.nlt_ge. lia.
Qed.

Lemma auxv_keys_gen_range : forall r, Forall (fun k => 0 <= k < 2 ^ 64) (auxv_keys_gen r).
Proof. intros [|]; repeat (constructor; [lia|]); constructor. Qed.

(* AT_RANDOM sits at pair 24 -- word 48 for the key, word 49 for the value -- whether or
   not the kernel has CONFIG_RSEQ, because the two rseq pairs follow AT_EXECFN.  The walk
   proofs (RF_am_E) lean on this, so it is stated rather than recomputed. *)
Lemma auxv_random_at_48 : forall v rnd execfn r,
  nth 48 (auxv_words_Z v rnd execfn r) 0 = 25
  /\ nth 49 (auxv_words_Z v rnd execfn r) 0 = rnd.
Proof. intros v rnd execfn [|]; split; reflexivity. Qed.

Lemma auxv_execfn_at_50 : forall v rnd execfn r,
  nth 50 (auxv_words_Z v rnd execfn r) 0 = 31
  /\ nth 51 (auxv_words_Z v rnd execfn r) 0 = execfn.
Proof. intros v rnd execfn [|]; split; reflexivity. Qed.

(* AT_SYSINFO_EHDR is pair 0, which is what makes musl's [__vdsosym] find the vDSO at
   LPS 75d69e00 where the pre-revision table had no key 33 at all. *)
Lemma auxv_sysinfo_at_0 : forall v rnd execfn r,
  nth 0 (auxv_words_Z v rnd execfn r) 0 = 33
  /\ nth 1 (auxv_words_Z v rnd execfn r) 0 = ax_sysinfo v.
Proof. intros v rnd execfn [|]; split; reflexivity. Qed.

(* The terminator.  Without CONFIG_RSEQ it is pair 26 (words 52, 53); with it the two
   rseq pairs push it to pair 28 (words 56, 57).  This is the whole reason a claim
   cannot pin the vector's length, and the reason the walk proofs case-split [r]. *)
Lemma auxv_null_pair : forall v rnd execfn (r : bool),
  let i := (if r then 56 else 52)%nat in
  nth i (auxv_words_Z v rnd execfn r) 0 = 0
  /\ nth (S i) (auxv_words_Z v rnd execfn r) 0 = 0.
Proof. intros v rnd execfn [|]; cbn; split; reflexivity. Qed.

Lemma auxv_rseq_pairs : forall v rnd execfn,
  nth 52 (auxv_words_Z v rnd execfn true) 0 = 27
  /\ nth 53 (auxv_words_Z v rnd execfn true) 0 = 28
  /\ nth 54 (auxv_words_Z v rnd execfn true) 0 = 28
  /\ nth 55 (auxv_words_Z v rnd execfn true) 0 = 32.
Proof. intros v rnd execfn. repeat split; reflexivity. Qed.

(* Every value slot fits in a 64-bit word.  A claim carries this about its own
   existentials; [auxv_words_Z_range] is what a reader of any slot needs, and it is
   stated once here rather than re-derived at each of the nine claim sites. *)
Definition auxv_vals_ok (v : auxv_vals) : Prop :=
  0 <= ax_sysinfo v < 2^64 /\ 0 <= ax_l1i v < 2^64 /\ 0 <= ax_l1ig v < 2^64
  /\ 0 <= ax_l1d v < 2^64 /\ 0 <= ax_l1dg v < 2^64 /\ 0 <= ax_l2 v < 2^64
  /\ 0 <= ax_l2g v < 2^64 /\ 0 <= ax_l3 v < 2^64 /\ 0 <= ax_l3g v < 2^64
  /\ 0 <= ax_minsig v < 2^64 /\ 0 <= ax_hwcap v < 2^64 /\ 0 <= ax_pagesz v < 2^64
  /\ 0 <= ax_clktck v < 2^64 /\ 0 <= ax_phdr v < 2^64 /\ 0 <= ax_phent v < 2^64
  /\ 0 <= ax_phnum v < 2^64 /\ 0 <= ax_base v < 2^64 /\ 0 <= ax_flags v < 2^64
  /\ 0 <= ax_entry v < 2^64 /\ 0 <= ax_uid v < 2^64 /\ 0 <= ax_euid v < 2^64
  /\ 0 <= ax_gid v < 2^64 /\ 0 <= ax_egid v < 2^64 /\ 0 <= ax_secure v < 2^64.

Lemma auxv_words_Z_range : forall v rnd execfn r,
  auxv_vals_ok v -> 0 <= rnd < 2^64 -> 0 <= execfn < 2^64 ->
  Forall (fun z => 0 <= z < 2^64) (auxv_words_Z v rnd execfn r).
Proof.
  intros v rnd execfn r HV HR HE. unfold auxv_vals_ok in HV.
  destruct v; cbn in HV |- *.
  destruct HV as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12
                  & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22
                  & H23 & H24).
  destruct r; unfold auxv_words_Z; cbn [ax_sysinfo ax_l1i ax_l1ig ax_l1d ax_l1dg
    ax_l2 ax_l2g ax_l3 ax_l3g ax_minsig ax_hwcap ax_pagesz ax_clktck ax_phdr
    ax_phent ax_phnum ax_base ax_flags ax_entry ax_uid ax_euid ax_gid ax_egid
    ax_secure app]; repeat (constructor; [lia|]); constructor.
Qed.

(* ------------------------------------------------------------------ *)
(* THE BRIDGE TO THE MODEL                                             *)
(* ------------------------------------------------------------------ *)

(* The values [StackLayout.auxv_entries] puts in those 24 slots, as Z. *)
Definition auxv_vals_of (la : LaunchAuxv) (ph : PhdrInfo)
    (entry uid gid hwcap : word) : auxv_vals :=
  let c := la_cache la in
  mkAuxv (bv_unsigned (la_sysinfo_ehdr la))
         (bv_unsigned (cw_l1i_size c)) (bv_unsigned (cw_l1i_geom c))
         (bv_unsigned (cw_l1d_size c)) (bv_unsigned (cw_l1d_geom c))
         (bv_unsigned (cw_l2_size c))  (bv_unsigned (cw_l2_geom c))
         (bv_unsigned (cw_l3_size c))  (bv_unsigned (cw_l3_geom c))
         (bv_unsigned (la_minsigstksz la))
         (bv_unsigned hwcap) 4096 100
         (Z.of_N (ph_addr ph)) (Z.of_N (ph_ent ph)) (Z.of_N (ph_num ph))
         0 0 (bv_unsigned entry)
         (bv_unsigned uid) (bv_unsigned uid)
         (bv_unsigned gid) (bv_unsigned gid)
         0.
(* [auxv_vals_ok] holds of the record the model's own launch builds: every slot is a
   [bv_unsigned], and the three [PhdrInfo] fields are [N]s the caller bounds. *)
Lemma auxv_vals_ok_of : forall la ph entry uid gid hwcap,
  (Z.of_N (ph_addr ph) < 2^64) -> (Z.of_N (ph_ent ph) < 2^64) ->
  (Z.of_N (ph_num ph) < 2^64) ->
  auxv_vals_ok (auxv_vals_of la ph entry uid gid hwcap).
Proof.
  intros la ph entry uid gid hwcap H1 H2 H3.
  unfold auxv_vals_ok, auxv_vals_of; cbn.
  pose proof (bv_unsigned_in_range _ (la_sysinfo_ehdr la)).
  pose proof (bv_unsigned_in_range _ (cw_l1i_size (la_cache la))).
  pose proof (bv_unsigned_in_range _ (cw_l1i_geom (la_cache la))).
  pose proof (bv_unsigned_in_range _ (cw_l1d_size (la_cache la))).
  pose proof (bv_unsigned_in_range _ (cw_l1d_geom (la_cache la))).
  pose proof (bv_unsigned_in_range _ (cw_l2_size (la_cache la))).
  pose proof (bv_unsigned_in_range _ (cw_l2_geom (la_cache la))).
  pose proof (bv_unsigned_in_range _ (cw_l3_size (la_cache la))).
  pose proof (bv_unsigned_in_range _ (cw_l3_geom (la_cache la))).
  pose proof (bv_unsigned_in_range _ (la_minsigstksz la)).
  pose proof (bv_unsigned_in_range _ hwcap).
  pose proof (bv_unsigned_in_range _ entry).
  pose proof (bv_unsigned_in_range _ uid).
  pose proof (bv_unsigned_in_range _ gid).
  pose proof (N2Z.is_nonneg (ph_addr ph)).
  pose proof (N2Z.is_nonneg (ph_ent ph)).
  pose proof (N2Z.is_nonneg (ph_num ph)).
  change (bv_modulus 64) with (2^64) in *.
  repeat split; lia.
Qed.


(* THE KERNEL CHECK.  Every key and every value of the table above is the one
   [StackLayout.auxv_entries] writes, BY NAME and in order, in both rseq shapes.  A
   claim that uses [auxv_list] therefore describes the model's vector and not a
   hand-kept copy of it; this is what RefLayout.auxv_words_eq feeds the producer. *)
Lemma auxv_list_eq : forall la ph entry uid gid hwcap ar ae,
  auxv_list (auxv_vals_of la ph entry uid gid hwcap)
            (bv_unsigned ar) (bv_unsigned ae) (la_rseq la)
  = flat_map (fun e => [fst e; snd e])
      (auxv_entries la ph entry uid gid hwcap ar ae).
Proof.
  intros [ehdr [l1is l1ig l1ds l1dg l2s l2g l3s l3g] msz [|]]
         ph entry uid gid hwcap ar ae;
    unfold auxv_list, auxv_words_Z, auxv_vals_of, auxv_entries;
    cbn - [Z_to_bv bv_unsigned Z.of_N];
    rewrite ?Z_to_bv_bv_unsigned; reflexivity.
Qed.

(* The byte length agrees with the model's own [auxv_size]. *)
Lemma auxv_vec_bytes_auxv_size : forall r,
  auxv_vec_bytes r = Z.of_nat (auxv_size r).
Proof. intros [|]; reflexivity. Qed.
