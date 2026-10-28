(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRecs.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition numa_flds (nalloc n rc arr : Z) : list fld :=
  [(4%nat, nalloc); (4%nat, n); (4%nat, rc); (4%nat, 0); (4%nat, 0x3f800000); (4%nat, 0); (8%nat, arr)].

(* [comment removed for export] *)
Definition NUMA_NMAX : Z := 2 ^ 24.

(* [comment removed for export] *)
Definition numa_n0 (n : Z) : Z := if (1 <=? n) && (n <=? 100000000) then n else 50.

(* [comment removed for export] *)
Definition f32i (v : Z) : Z := fst (fp_of_int fmt_single RNE true 32 v).

Section WithSegs.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout}.
Variable segs : list Segment.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition numa_at (C : lctx) (A : AS) (m : word -> option byte) (na nalloc n arr : Z) : Prop :=
  RECat m na (numa_flds nalloc n 1 arr) /\ na mod 16 = 0 /\ 1 <= arr /\ arr mod 16 = 0 /\ arr <> na /\
  1 <= nalloc <= NUMA_NMAX /\ 0 <= n <= nalloc /\
  live A (Z_to_bv 64 na) = Some 32 /\ live (c_A0 C) (Z_to_bv 64 na) = None /\
  live A (Z_to_bv 64 arr) = Some (4 * nalloc) /\ live (c_A0 C) (Z_to_bv 64 arr) = None.

(* [comment removed for export] *)
Definition numa_new (C : lctx) (A A' : AS) (m' : word -> option byte) (na nalloc arr : Z) : Prop :=
  numa_at C A' m' na nalloc 0 arr /\
  live A (Z_to_bv 64 na) = None /\ live A (Z_to_bv 64 arr) = None /\
  (forall q, q <> Z_to_bv 64 na -> q <> Z_to_bv 64 arr -> live A' q = live A q).

(* [comment removed for export] *)
Definition ncell (m : word -> option byte) (arr i z : Z) : Prop :=
  rdn segs m (Z_to_bv 64 (arr + 4 * i)) 4 = Some (Z_to_le_bytes 4 z).

(* [comment removed for export] *)
Definition prof_cells (m : word -> option byte) (arr n lo hi : Z) : Prop :=
  forall i, 0 <= i < n -> exists v, lo <= v <= hi /\ ncell m arr i (f32i v).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma NUMA_rd_nalloc : forall m na nalloc n rc arr, RECat m na (numa_flds nalloc n rc arr) ->
  rdn segs m (Z_to_bv 64 na) 4 = Some (Z_to_le_bytes 4 nalloc).
Proof. intros m na nalloc n rc arr R. eapply (REC_rd' segs _ _ (numa_flds nalloc n rc arr) 0 4); [exact R | cbn; lia | reflexivity | cbn [fld_off numa_flds Z.of_nat]; f_equal; lia | reflexivity]. Qed.
Lemma NUMA_rd_n : forall m na nalloc n rc arr, RECat m na (numa_flds nalloc n rc arr) ->
  rdn segs m (Z_to_bv 64 (na + 4)) 4 = Some (Z_to_le_bytes 4 n).
Proof. intros m na nalloc n rc arr R. eapply (REC_rd' segs _ _ (numa_flds nalloc n rc arr) 1 4); [exact R | cbn; lia | reflexivity | reflexivity | reflexivity]. Qed.
Lemma NUMA_rd_rc : forall m na nalloc n rc arr, RECat m na (numa_flds nalloc n rc arr) ->
  rdn segs m (Z_to_bv 64 (na + 8)) 4 = Some (Z_to_le_bytes 4 rc).
Proof. intros m na nalloc n rc arr R. eapply (REC_rd' segs _ _ (numa_flds nalloc n rc arr) 2 4); [exact R | cbn; lia | reflexivity | reflexivity | reflexivity]. Qed.
Lemma NUMA_rd_arr : forall m na nalloc n rc arr, RECat m na (numa_flds nalloc n rc arr) ->
  rdn segs m (Z_to_bv 64 (na + 24)) 8 = Some (Z_to_le_bytes 8 arr).
Proof. intros m na nalloc n rc arr R. eapply (REC_rd' segs _ _ (numa_flds nalloc n rc arr) 6 8); [exact R | cbn; lia | reflexivity | reflexivity | reflexivity]. Qed.
Lemma NUMA_wf : forall m na nalloc n rc arr, RECat m na (numa_flds nalloc n rc arr) ->
  0 <= nalloc < 2 ^ 32 /\ 0 <= n < 2 ^ 32 /\ 0 <= rc < 2 ^ 32 /\ 0 <= arr < 2 ^ 64 /\ 0 <= na /\ na + 32 < 2 ^ 64.
Proof. intros m na nalloc n rc arr (H0 & H1 & WF & _). cbn in H1, WF. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma RECat_livk : forall A m m' p fs k, RECat m p fs -> LIVK A m m' -> live A (Z_to_bv 64 p) = Some k ->
  Z.of_nat (flds_len fs) <= k -> RECat m' p fs.
Proof.
  intros A m m' p fs k R LK Lp Hk. pose proof (RECat_range _ _ _ R) as [Hp0 Hp1].
  apply (RECat_frame m); [exact R|]. intros x Hx.
  replace x with (at_ (Z_to_bv 64 p) (u x - p)).
  - apply (LK (Z_to_bv 64 p) k (u x - p) Lp). lia.
  - unfold at_. apply bv_eq. rewrite u_Z2bv; rewrite u_Z2bv by lia; lia.
Qed.

Lemma numa_at_keep : forall C A A' m m' na nalloc n arr,
  numa_at C A m na nalloc n arr -> sub_live A A' -> LIVK A m m' -> numa_at C A' m' na nalloc n arr.
Proof.
  intros C A A' m m' na nalloc n arr (R & Hal & Harr & Hala & NE & Hna & Hn & L1 & L01 & L2 & L02) SUB LK.
  split; [exact (RECat_livk A m m' na _ 32 R LK L1 ltac:(cbn; lia))|].
  repeat (split; [assumption|]). split; [exact (SUB _ _ L1)|]. split; [assumption|]. split; [exact (SUB _ _ L2)|]. assumption.
Qed.

Lemma ncell_livk : forall A m m' arr k i z, ncell m arr i z -> LIVK A m m' -> live A (Z_to_bv 64 arr) = Some k ->
  0 <= arr -> arr + k < 2 ^ 64 -> 0 <= i -> 4 * i + 4 <= k -> ncell m' arr i z.
Proof.
  intros A m m' arr k i z NC LK La Ha Hk Hi Hik. unfold ncell in *. rewrite <- NC.
  apply rdn_ext; rewrite u_Z2bv by lia; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
  replace x with (at_ (Z_to_bv 64 arr) (u x - arr)).
  - apply (LK (Z_to_bv 64 arr) k (u x - arr) La). lia.
  - unfold at_. apply bv_eq. rewrite u_Z2bv; rewrite u_Z2bv by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma numa_at_mem : forall C A m m' na nalloc n arr, numa_at C A m na nalloc n arr ->
  (forall x : word, na <= u x < na + 32 -> m' x = m x) -> numa_at C A m' na nalloc n arr.
Proof.
  intros C A m m' na nalloc n arr (R & REST) E. split; [| exact REST].
  apply (RECat_frame m); [exact R | intros x Hx; apply E; cbn in Hx; lia].
Qed.

(* [comment removed for export] *)
Lemma numa_at_livk : forall C A A' m m' na nalloc n arr, numa_at C A m na nalloc n arr ->
  live A' (Z_to_bv 64 na) = Some 32 -> live A' (Z_to_bv 64 arr) = Some (4 * nalloc) -> LIVK A' m m' ->
  numa_at C A' m' na nalloc n arr.
Proof.
  intros C A A' m m' na nalloc n arr (R & Hal & Harr & Hala & NE & Hna & Hn & L1 & L01 & L2 & L02) L1' L2' LK.
  split; [exact (RECat_livk A' m m' na _ 32 R LK L1' ltac:(cbn; lia))|].
  repeat (split; [assumption|]). assumption.
Qed.

End WithSegs.
