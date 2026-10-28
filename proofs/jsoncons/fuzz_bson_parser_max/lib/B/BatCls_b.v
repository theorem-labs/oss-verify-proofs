(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatInitCache_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Record art_cls : Type := CLS {
  cl_cache : list Z;     (* [comment removed for export] *)
  cl_free  : list Z;     (* [comment removed for export] *)
  cl_au    : Z;          (* [comment removed for export] *)
  cl_mu    : Z;          (* [comment removed for export] *)
  cl_mfa   : Z;          (* [comment removed for export] *)
  cl_na    : Z;          (* [comment removed for export] *)
  cl_nfr   : Z           (* [comment removed for export] *)
}.
Definition art_cls0 : art_cls := CLS [] [] 0 0 0 0 0.

(* [comment removed for export] *)
Definition art_cache_rep (ca c : Z) (cache : list Z) (M : word -> option byte) : Prop :=
  cellA M (ca + 80 * c) 4 (Z.of_nat (length cache))
  /\ (forall j, (j < length cache)%nat -> cellA M (ca + 80 * c + 16 + 4 * Z.of_nat j) 4 (nth j cache 0)).
Definition art_region_rep (spb ris c mx : Z) (cl : art_cls) (M : word -> option byte) : Prop :=
  cellA M (ris + 128 * c) 8 mx
  /\ cellA M (ris + 128 * c + 16) 8 (Z.of_nat (length (cl_free cl)))
  /\ cellA M (ris + 128 * c + 24) 8 (cl_mfa cl)
  /\ cellA M (ris + 128 * c + 32) 8 (cl_au cl)
  /\ cellA M (ris + 128 * c + 40) 8 0
  /\ cellA M (ris + 128 * c + 48) 8 (cl_mu cl)
  /\ cellA M (ris + 128 * c + 56) 8 0
  /\ cellA M (ris + 128 * c + 72) 8 (cl_na cl)
  /\ cellA M (ris + 128 * c + 80) 8 (cl_nfr cl)
  /\ (forall j, (j < length (cl_free cl))%nat -> cellA M (spb + c * 2 ^ 32 + 3758096384 + 4 * Z.of_nat j) 4 (nth j (cl_free cl) 0))
  /\ wrA M (ris + 128 * c) 128
  /\ wrA M (spb + c * 2 ^ 32 + 3758096384) (cl_mfa cl)
  /\ wrA M (spb + c * 2 ^ 32) (cl_mu cl).
Definition art_cls_rep (ca spb ris c : Z) (cl : art_cls) (M : word -> option byte) : Prop :=
  art_cache_rep ca c (cl_cache cl) M /\ art_region_rep spb ris c 0 cl M.

(* [comment removed for export] *)
Definition art_cls_foot (ca spb ris c : Z) (cl : art_cls) (x : Z) : Prop :=
  (ca + 80 * c <= x < ca + 80 * c + 4) \/ (ca + 80 * c + 16 <= x < ca + 80 * c + 80) \/ (ris + 128 * c <= x < ris + 128 * c + 128)
  \/ (spb + c * 2 ^ 32 + 3758096384 <= x < spb + c * 2 ^ 32 + 3758096384 + 4 * Z.of_nat (length (cl_free cl))).

(* [comment removed for export] *)
Definition art_cptr_ok (sz au w : Z) : Prop := 0 <= w /\ 16 * w + sz <= au /\ exists i, 16 * w = sz * i.

Definition art_cls_ok (c : Z) (cl : art_cls) : Prop :=
  let sz := AsanTab.class_size c in
  (length (cl_cache cl) <= 16)%nat
  /\ 0 <= cl_au cl <= cl_mu cl /\ cl_mu cl - cl_au cl < sz
  /\ (exists k, cl_mu cl = 262144 * k) /\ (exists k, cl_au cl = sz * k) /\ cl_mu cl <= 3758096384
  /\ (exists k, cl_mfa cl = 262144 * k) /\ 0 <= cl_mfa cl <= 536870912 /\ 4 * Z.of_nat (length (cl_free cl)) <= cl_mfa cl
  /\ Forall (art_cptr_ok sz (cl_au cl)) (cl_cache cl ++ cl_free cl)
  /\ NoDup (cl_cache cl ++ cl_free cl).

(* [comment removed for export] *)
Definition art_pc_hdr (ca : Z) (inited : bool) (M : word -> option byte) : Prop :=
  forall c, 1 <= c <= 31 ->
    cellA M (ca + 80 * c + 4) 4 (if inited then art_ic_mc c else 0) /\ cellA M (ca + 80 * c + 8) 8 (if inited then art_ic_size c else 0).
Definition art_pc_hdr_foot (ca : Z) (x : Z) : Prop := exists c, 1 <= c <= 31 /\ ca + 80 * c + 4 <= x < ca + 80 * c + 16.

(* [comment removed for export] *)
Definition art_prim_consts (spb ris : Z) (M : word -> option byte) : Prop :=
  cellA M (1295832 + 32) 8 spb /\ cellA M (1295832 + 48) 8 ris /\ cellA M (1295832 + 40) 4 0xffffffff /\ cellA M (1295832 + 56) 1 0
  /\ cellA M 0x10420 8 0xafffff00000fffff
  (* [comment removed for export] *)
  /\ cellA M 0x1374a0 8 0x1cf6e0 /\ cellA M 0x1cf6e0 8 4096 /\ cellA M (0x1d1768 + 260) 1 0 /\ cellA M (0x1d1768 + 144) 8 0.

(* [comment removed for export] *)
Definition art_geo (HI t ctx tp tsd spb ris qs : Z) : Prop :=
  0x10007fff8000 <= HI /\ HI + 8388608 <= 2 ^ 47
  /\ spb = 65536 * qs /\ 0x10007fff8000 <= spb /\ ris = spb + 2 ^ 37 /\ ris + 4096 <= HI
  /\ 4096 <= t /\ t + 4096 <= HI /\ (t + 4096 <= 0x10000 \/ 0x696000 <= t) /\ (t + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= t)
  /\ apart t 4096 spb (2 ^ 37 + 4096) /\ (exists qt, t = 4096 * qt)
  /\ 4096 <= ctx /\ ctx + 4096 <= HI /\ (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx) /\ (ctx + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= ctx)
  /\ apart ctx 4096 spb (2 ^ 37 + 4096) /\ apart t 4096 ctx 4096
  /\ 0x10100 <= tp /\ tp + 8 <= 0x696000 /\ 0x10000 <= tsd /\ tsd + 1024 <= 0x696000.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_carved (au sz : Z) (new : nat) : list Z :=
  map (fun k => (au + (Z.of_nat new - 1 - Z.of_nat k) * sz) / 16) (seq 0 new).
Definition art_cls_new (c : Z) (cl : art_cls) : Z := (cl_mu cl + 262144 - cl_au cl) / AsanTab.class_size c.
Definition art_cls_mfa' (cl : art_cls) (tot : Z) : Z := if 4 * tot <=? cl_mfa cl then cl_mfa cl else (4 * tot + 262143) / 262144 * 262144.
Definition art_cls_populate (c : Z) (cl : art_cls) : art_cls :=
  let sz := AsanTab.class_size c in
  let new := art_cls_new c cl in
  CLS (cl_cache cl) (cl_free cl ++ art_carved (cl_au cl) sz (Z.to_nat new)) (cl_au cl + new * sz) (cl_mu cl + 262144)
      (art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + new)) (cl_na cl) (cl_nfr cl).
(* [comment removed for export] *)
Definition art_cls_take (n : nat) (cl : art_cls) : art_cls :=
  let k := (length (cl_free cl) - n)%nat in
  CLS (skipn k (cl_free cl)) (firstn k (cl_free cl)) (cl_au cl) (cl_mu cl) (cl_mfa cl) (cl_na cl + Z.of_nat n) (cl_nfr cl).
Definition art_refill_n (c : Z) : nat := Z.to_nat (art_ic_mc c / 2).
Definition art_cls_needs_populate (c : Z) (cl : art_cls) : bool := (length (cl_free cl) <? art_refill_n c)%nat.
Definition art_cls_refill (c : Z) (cl : art_cls) : art_cls :=
  art_cls_take (art_refill_n c) (if art_cls_needs_populate c cl then art_cls_populate c cl else cl).
(* [comment removed for export] *)
Definition art_refill_events (spb c : Z) (cl : art_cls) : list aev :=
  if art_cls_needs_populate c cl then
    let tot := Z.of_nat (length (cl_free cl)) + art_cls_new c cl in
    AMmapFixed (spb + c * 2 ^ 32 + cl_mu cl) 262144
    :: (if 4 * tot <=? cl_mfa cl then [] else [AMmapFixed (spb + c * 2 ^ 32 + 3758096384 + cl_mfa cl) (art_cls_mfa' cl tot - cl_mfa cl)])
  else [].
(* [comment removed for export] *)
Fixpoint art_evok_list (EVOK : list aev -> aev -> Prop) (log : list aev) (evs : list aev) : Prop :=
  match evs with [] => True | e :: r => EVOK log e /\ art_evok_list EVOK (log ++ [e]) r end.

(* [comment removed for export] *)
Definition art_refill_fp (sp t spb ris qs c km : Z) (x : Z) : Prop :=
  (sp - 672 <= x < sp)
  \/ (t + 208 + 80 * c <= x < t + 208 + 80 * c + 80) \/ art_pc_hdr_foot (t + 208) x \/ (t + 208 + 2584 <= x < t + 208 + 2592)
  \/ (ris + 128 * c <= x < ris + 128 * c + 128)
  \/ (spb + c * 2 ^ 32 + 262144 * km <= x < spb + c * 2 ^ 32 + 262144 * km + 262144)
  \/ (spb + c * 2 ^ 32 + 3758096384 <= x < spb + c * 2 ^ 32 + 4294967296)
  \/ (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km <= x < 2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + 32768)
  \/ (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048 <= x < 2147450880 + 8192 * qs + c * 2 ^ 29 + 536870912)
  \/ (t + 2872 <= x < t + 2888).

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition art_refill_rspec : Prop :=
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
         (sp HI t ctx tp key tsd spb ris qs c km : Z) (inited : bool) (cl : art_cls),
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp ->
    getr regs 10 = Z_to_bv 64 (t + 208) -> getr regs 11 = Z_to_bv 64 (t + 208 + 80 * c) -> getr regs 12 = Z_to_bv 64 1295832 -> getr regs 13 = Z_to_bv 64 c ->
    1 <= c <= 30 -> HI <= sp - 672 -> sp < 2 ^ 47 -> art_geo HI t ctx tp tsd spb ris qs ->
    wrA M (sp - 672) 672 -> wrA M t 4096 ->
    art_prim_consts spb ris M -> art_layout M -> art_tsd M tp key tsd ctx t ->
    art_pc_hdr (t + 208) inited M -> art_cls_rep (t + 208) spb ris c cl M -> art_cls_ok c cl -> cl_cache cl = [] -> cl_mu cl = 262144 * km ->
    (exists m1 m2 sv, cellA M (t + 2872) 8 m1 /\ cellA M (t + 2880) 8 m2 /\ cellA M (t + 208 + 2584) 8 sv) ->
    (* [comment removed for export] *)
    (art_cls_needs_populate c cl = true ->
       cl_mu cl + 262144 <= 3758096384
       /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912
       /\ wrA M (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km) 32768
       /\ wrA M (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048) 67108864) ->
    art_evok_list EVOK log (art_refill_events spb c cl) ->
    (forall regs' (M' : word -> option byte),
        getr regs' 10 = Z_to_bv 64 1 -> getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
        mem_grows M M' ->
        (forall x : word, ~ art_refill_fp sp t spb ris qs c km (U x) -> M' x = M x) ->
        art_pc_hdr (t + 208) true M' -> art_cls_rep (t + 208) spb ris c (art_cls_refill c cl) M' -> art_cls_ok c (art_cls_refill c cl) ->
        (art_cls_needs_populate c cl = true ->
           forall j, 0 <= j < 32768 -> cellA M' (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + j) 1 250) ->
        Q (log ++ art_refill_events spb c cl) (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x5748c : word) M rom).

End Spec.

(* [comment removed for export] *)
Lemma art_refill_n_range : forall c, 1 <= c <= 31 -> (1 <= art_refill_n c <= 8)%nat.
Proof.
  intros c Hc. unfold art_refill_n. pose proof (art_ic_mc_range c Hc) as R.
  assert (1 <= art_ic_mc c / 2 <= 8). { split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
  lia.
Qed.

Lemma art_carved_length : forall au sz new, length (art_carved au sz new) = new.
Proof. intros. unfold art_carved. rewrite length_map, length_seq. reflexivity. Qed.

Lemma art_carved_nth : forall au sz new k, (k < new)%nat -> nth k (art_carved au sz new) 0 = (au + (Z.of_nat new - 1 - Z.of_nat k) * sz) / 16.
Proof.
  intros au sz new k Hk. unfold art_carved.
  set (f := fun k0 : nat => (au + (Z.of_nat new - 1 - Z.of_nat k0) * sz) / 16).
  rewrite (nth_indep (map f (seq 0 new)) 0 (f O)) by (rewrite length_map, length_seq; exact Hk).
  rewrite (map_nth f (seq 0 new) O k). rewrite seq_nth by exact Hk. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_cls_rep_frame : forall ca spb ris c cl M M',
  0x696000 <= ca -> ca + 4096 < 2 ^ 64 -> 1 <= c <= 31 -> 0 <= ris -> ris + 128 * 64 < 2 ^ 47 -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 ->
  (length (cl_cache cl) <= 16)%nat -> Z.of_nat (length (cl_free cl)) < 2 ^ 27 ->
  art_cls_rep ca spb ris c cl M -> mem_grows M M' ->
  (forall x : word, art_cls_foot ca spb ris c cl (U x) -> M' x = M x) ->
  art_cls_rep ca spb ris c cl M'.
Proof.
  intros ca spb ris c cl M M' Hca Hca' Hc Hris Hris' Hspb Hspb' Hlc Hlf R G AG.
  destruct R as ((C1 & CW) & (C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & CF & W1 & W2 & W3)).
  pose proof (Nat2Z.is_nonneg (length (cl_cache cl))) as L0. pose proof (proj1 (Nat2Z.inj_le _ _) Hlc) as L1. cbn in L1.
  pose proof (Nat2Z.is_nonneg (length (cl_free cl))) as L2.
  assert (Hc32 : 0 <= c * 2 ^ 32 <= 31 * 2 ^ 32) by nia.
  assert (T : forall a n v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> (forall i, a <= i < a + Z.of_nat n -> art_cls_foot ca spb ris c cl i) -> cellA M a n v -> cellA M' a n v).
  { intros a n v Ha Hn F C. apply (cell_agree M M'); [|exact Ha|exact Hn|exact C]. intros x Hx. apply AG. apply F. exact Hx. }
  unfold art_cls_rep, art_cache_rep, art_region_rep. repeat split.
  - apply T; [lia|cbn; lia| |exact C1]. intros i Hi. cbn in Hi. unfold art_cls_foot. lia.
  - intros j Hj. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. apply T; [lia|cbn; lia| |exact (CW j Hj)]. intros i Hi. cbn in Hi. unfold art_cls_foot. lia.
  - apply T; [lia|cbn; lia| |exact C2]. intros i Hi. cbn in Hi. unfold art_cls_foot. lia.
  - apply T; [lia|cbn; lia| |exact C3]. intros i Hi. cbn in Hi. unfold art_cls_foot. lia.
  - apply T; [lia|cbn; lia| |exact C4]. intros i Hi. cbn in Hi. unfold art_cls_foot. lia.
  - apply T; [lia|cbn; lia| |exact C5]. intros i Hi. cbn in Hi. unfold art_cls_foot. lia.
  - apply T; [lia|cbn; lia| |exact C6]. intros i Hi. cbn in Hi. unfold art_cls_foot. lia.
  - apply T; [lia|cbn; lia| |exact C7]. intros i Hi. cbn in Hi. unfold art_cls_foot. lia.
  - apply T; [lia|cbn; lia| |exact C8]. intros i Hi. cbn in Hi. unfold art_cls_foot. lia.
  - apply T; [lia|cbn; lia| |exact C9]. intros i Hi. cbn in Hi. unfold art_cls_foot. lia.
  - apply T; [lia|cbn; lia| |exact C10]. intros i Hi. cbn in Hi. unfold art_cls_foot. lia.
  - intros j Hj. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. apply T; [lia|cbn; lia| |exact (CF j Hj)]. intros i Hi. cbn in Hi. unfold art_cls_foot. lia.
  - eapply wr_grows; [exact G|exact W1].
  - eapply wr_grows; [exact G|exact W2].
  - eapply wr_grows; [exact G|exact W3].
Qed.

Lemma art_pc_hdr_frame : forall ca inited M M', 0x696000 <= ca -> ca + 4096 < 2 ^ 64 ->
  art_pc_hdr ca inited M -> (forall x : word, art_pc_hdr_foot ca (U x) -> M' x = M x) -> art_pc_hdr ca inited M'.
Proof.
  intros ca inited M M' Hca Hca' H AG c Hc. destruct (H c Hc) as [C1 C2]. split.
  - apply (cell_agree M M'); [|lia|cbn; lia|exact C1]. intros x Hx. apply AG. exists c. cbn in Hx. lia.
  - apply (cell_agree M M'); [|lia|cbn; lia|exact C2]. intros x Hx. apply AG. exists c. cbn in Hx. lia.
Qed.
