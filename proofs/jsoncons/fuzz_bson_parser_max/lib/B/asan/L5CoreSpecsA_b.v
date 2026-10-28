(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx
     L5Defs L5Core L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5CSA.
Import L5CA.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.

Definition MALLOC_SCR : Z := 4096.  Definition SM_SCR : Z := 512.  Definition MEM_SCR : Z := 2560.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OPNEW : Z := 0x130338.
Definition OPNEW_SCR : Z := 16 + MALLOC_SCR.

Definition opnew_spec (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n sp r : Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 -> acredit_ok L cr n ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp OPNEW_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)) (q : Z),
        getr R' 10%bv = Z_to_bv 64 q -> regs_preserved R R' ->
        afresh L ar LB (FF ++ LK) M' q n ->
        ahpres L ar LB FF sp OPNEW_SCR [] M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' ->
        ri_inv HI ((q, n) :: LB) FF LK (adebit L cr n) A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R OPNEW M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OPDEL : Z := 0xd39a8.
Definition OPDEL_SIZED : Z := 0xd39ac.
Definition OPDEL_SCR : Z := MALLOC_SCR.

Definition opdel_spec_at (pc : Z) (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (q n sp r : Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    In (q, n) LB -> getr R 10%bv = Z_to_bv 64 q ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp OPDEL_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)),
        regs_preserved R R' ->
        ahpres L ar (lb_remove q LB) FF sp OPDEL_SCR [] M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' ->
        ri_inv HI (lb_remove q LB) FF LK cr A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R pc M model) K.
Definition opdel_spec := opdel_spec_at OPDEL.
Definition opdel_sized_spec := opdel_spec_at OPDEL_SIZED.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ROUNDUP : Z := 0x90bd8.
Definition ROUNDUP_SCR : Z := 96 + SM_SCR.
Definition round_up (i : Z) : Z := 8 * (i / 8) + 8.

Definition roundup_spec (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (i sp r : Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 i -> 0 <= i <= 2 ^ 60 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp ROUNDUP_SCR ->
    ffr FF LK 2 -> ffrs FF sp ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        getr R' 10%bv = Z_to_bv 64 (round_up i) -> regs_preserved R R' ->
        ahpres L ar LB FF sp ROUNDUP_SCR [] M M' ->
        model_rt model model' -> amodel_ok A model' -> incl LK' LK ->
        ri_inv HI LB FF LK' cr A M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R ROUNDUP M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ARESERVE : Z := 0xaed4c.
Definition ARESERVE_SCR : Z := 144 + OPNEW_SCR.      (* [comment removed for export] *)

Definition areserve_spec (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o n sp r : Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 n -> 1 <= n <= 2 ^ 23 -> acredit_ok L cr (8 * round_up n) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 16 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp ARESERVE_SCR ->
    ffr FF LK 3 -> ffrs FF sp ->
    aobj FF o 32 -> shadow_zero M o 4 ->
    L5.u64_at RSEGS M (o + 8) 0 -> L5.u64_at RSEGS M (o + 24) 0 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (A' : list (Z * Z)) (q : Z),
        regs_preserved R R' ->
        afresh L ar LB (FF ++ LK') M' q (8 * round_up n) ->
        L5.u64_at RSEGS M' (o + 16) (round_up n) /\ L5.u64_at RSEGS M' (o + 24) q ->
        ahpres L ar LB FF sp ARESERVE_SCR [(o + 16, 16)] M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI ((q, 8 * round_up n) :: LB) FF LK' (adebit L cr (8 * round_up n)) A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R ARESERVE M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RESERVE : Z := 0x903a8.
Definition RESERVE_SCR : Z := 112 + ARESERVE_SCR.

Definition reserve_post (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit)
           (M M' : word -> option byte) (R R' : bvmap 5 word) (o sp n : Z) (b : L5.bigobj) (g : growth) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  match g with
  | Same => (L5.bo_dyn b = true \/ n <= 2) /\ LB' = LB /\ cr' = cr
            /\ L5.big_at RSEGS M' o b
            /\ ahpres L ar LB FF sp RESERVE_SCR [] M M'
  | Grown q cap => L5.bo_dyn b = false /\ 3 <= n /\ cap = round_up n /\ LB' = (q, 8 * cap) :: LB /\ cr' = adebit L cr (8 * cap)
            /\ afresh L ar LB (FF ++ LKq) M' q (8 * cap)
            /\ (exists v0 v1, L5.bo_st b = L5.BInl v0 v1 /\ L5.u64_at RSEGS M' q v0 /\ L5.u64_at RSEGS M' (q + 8) v1)
            /\ L5.big_at RSEGS M' o (L5.BO (Z.lor (L5.bo_fb b) 1) (L5.bo_len b) (L5.BDyn cap q))
            /\ ahpres L ar LB FF sp RESERVE_SCR [(o, 32)] M M'
  end.

Definition reserve_spec (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o n sp r : Z) (b : L5.bigobj),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n <= 2 ^ 23 ->
    (L5.bo_dyn b = true -> n <= L5.bo_cap b) ->
    (L5.bo_dyn b = false -> 3 <= n -> acredit_ok L cr (8 * round_up n)) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp RESERVE_SCR ->
    ffr FF LK 3 -> ffrs FF sp ->
    L5.big_at RSEGS M o b -> aobj FF o 32 -> shadow_zero M o 4 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        reserve_post L ar LB FF LK' cr M M' R R' o sp n b g LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R RESERVE M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RESIZE : Z := 0x8ffac.
Definition RESIZE_SCR : Z := 128 + RESERVE_SCR.

Definition resize_limbs (ws : list Z) (n : nat) : list Z := firstn n ws ++ repeat 0 (n - length ws).

Definition resize_post (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit)
           (M M' : word -> option byte) (R R' : bvmap 5 word) (o sp : Z) (n : nat) (b : L5.bigobj) (ws : list Z) (g : growth)
           (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  match g with
  | Same => (L5.bo_dyn b = true \/ (n <= 2)%nat) /\ LB' = LB /\ cr' = cr
            /\ (exists st', L5.big_at RSEGS M' o (L5.BO (L5.bo_fb b) n st') /\ L5C.obj_limbs RSEGS M' (L5.BO (L5.bo_fb b) n st') (resize_limbs ws n)
                           /\ match L5.bo_st b, st' with
                              | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
                              | L5.BInl _ _, L5.BInl _ _ => True
                              | _, _ => False end)
            /\ ahpres L ar LB FF sp RESIZE_SCR [(o, 32); (L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b), 8 * Z.max 0 (Z.of_nat n - Z.of_nat (L5.bo_len b)))] M M'
  | Grown q cap => L5.bo_dyn b = false /\ (3 <= n)%nat /\ cap = round_up (Z.of_nat n) /\ LB' = (q, 8 * cap) :: LB /\ cr' = adebit L cr (8 * cap)
            /\ afresh L ar LB (FF ++ LKq) M' q (8 * cap)
            /\ L5.big_at RSEGS M' o (L5.BO (Z.lor (L5.bo_fb b) 1) n (L5.BDyn cap q))
            /\ L5C.obj_limbs RSEGS M' (L5.BO (Z.lor (L5.bo_fb b) 1) n (L5.BDyn cap q)) (resize_limbs ws n)
            /\ ahpres L ar LB FF sp RESIZE_SCR [(o, 32)] M M'
  end.

Definition resize_spec (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r : Z) (n : nat) (b : L5.bigobj) (ws : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 (Z.of_nat n) -> Z.of_nat n <= 2 ^ 23 ->
    (L5.bo_dyn b = true -> Z.of_nat n <= L5.bo_cap b) ->
    ((3 <= n)%nat -> L5.bo_dyn b = false -> acredit_ok L cr (8 * round_up (Z.of_nat n))) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp RESIZE_SCR ->
    ffr FF LK 4 -> ffrs FF sp ->
    L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> aobj FF o 32 -> shadow_zero M o 4 ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        resize_post L ar LB FF LK' cr M M' R R' o sp n b ws g LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R RESIZE M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASSIGN : Z := 0x8fe2c.
Definition ASSIGN_SCR : Z := 64 + Z.max RESIZE_SCR MEM_SCR.

Definition assign_fb (fb fb' : Z) (leny : nat) (grown : bool) : Z :=
  let f0 := if grown then Z.lor fb 1 else fb in
  if Nat.eqb leny 0 then f0 else Z.lor (Z.land f0 253) (Z.land fb' 2).

Definition assign_post (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit)
           (M M' : word -> option byte) (R R' : bvmap 5 word) (o o' sp : Z) (b b' : L5.bigobj) (ws' : list Z) (g : growth)
           (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 o /\
  let n := L5.bo_len b' in
  match g with
  | Same => (L5.bo_dyn b = true \/ (n <= 2)%nat) /\ LB' = LB /\ cr' = cr
            /\ (exists st', L5.big_at RSEGS M' o (L5.BO (assign_fb (L5.bo_fb b) (L5.bo_fb b') n false) n st')
                           /\ L5C.obj_limbs RSEGS M' (L5.BO (assign_fb (L5.bo_fb b) (L5.bo_fb b') n false) n st') ws'
                           /\ match L5.bo_st b, st' with
                              | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
                              | L5.BInl _ _, L5.BInl _ _ => True
                              | _, _ => False end)
            /\ ahpres L ar LB FF sp ASSIGN_SCR [(o, 32); (L5.bo_data o b, 8 * Z.of_nat n)] M M'
  | Grown q cap => L5.bo_dyn b = false /\ (3 <= n)%nat /\ cap = round_up (Z.of_nat n) /\ LB' = (q, 8 * cap) :: LB /\ cr' = adebit L cr (8 * cap)
            /\ afresh L ar LB (FF ++ LKq) M' q (8 * cap)
            /\ L5.big_at RSEGS M' o (L5.BO (assign_fb (L5.bo_fb b) (L5.bo_fb b') n true) n (L5.BDyn cap q))
            /\ L5C.obj_limbs RSEGS M' (L5.BO (assign_fb (L5.bo_fb b) (L5.bo_fb b') n true) n (L5.BDyn cap q)) ws'
            /\ ahpres L ar LB FF sp ASSIGN_SCR [(o, 32)] M M'
  end.

Definition assign_spec (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o o' sp r : Z) (b b' : L5.bigobj) (ws' : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 o' -> Z.of_nat (L5.bo_len b') <= 2 ^ 23 ->
    (L5.bo_dyn b = true -> Z.of_nat (L5.bo_len b') <= L5.bo_cap b) ->
    ((3 <= L5.bo_len b')%nat -> L5.bo_dyn b = false -> acredit_ok L cr (8 * round_up (Z.of_nat (L5.bo_len b')))) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp ASSIGN_SCR ->
    ffr FF LK 4 -> ffrs FF sp ->
    L5.big_at RSEGS M o b -> aobj FF o 32 -> shadow_zero M o 4 ->
    L5.big_at RSEGS M o' b' -> L5C.obj_limbs RSEGS M b' ws' -> aobj FF o' 32 -> shadow_zero M o' 4 ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall cap q, L5.bo_st b' = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (o + 32 <= o' \/ o' + 32 <= o) ->
    (forall c q c' q', L5.bo_st b = L5.BDyn c q -> L5.bo_st b' = L5.BDyn c' q' -> q + 8 * c <= q' \/ q' + 8 * c' <= q) ->   (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        assign_post L ar LB FF LK' cr M M' R R' o o' sp b b' ws' g LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R ASSIGN M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition COPY : Z := 0x91f98.
Definition COPYA : Z := 0x94084.
Definition ACOPY : Z := 0x92104.
Definition COPY_SCR : Z := 16 + 128 + Z.max OPNEW_SCR MEM_SCR.

Definition copy_fb (fbo fb' : Z) (dyn : bool) : Z :=
  Z.lor (Z.lor (Z.land fbo 252) (if dyn then 1 else 0)) (Z.land fb' 2).

Definition copy_post (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit)
           (M M' : word -> option byte) (R R' : bvmap 5 word) (o o' sp fbo : Z) (b' : L5.bigobj) (ws' : list Z) (g : growth)
           (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  match g with
  | Same => L5.bo_dyn b' = false /\ LB' = LB /\ cr' = cr
            /\ L5.big_at RSEGS M' o (L5.BO (copy_fb fbo (L5.bo_fb b') false) (L5.bo_len b') (L5.bo_st b'))
            /\ ahpres L ar LB FF sp COPY_SCR [(o, 32)] M M'
  | Grown q cap => L5.bo_dyn b' = true /\ cap = L5.bo_cap b' /\ LB' = (q, 8 * cap) :: LB /\ cr' = adebit L cr (8 * cap)
            /\ afresh L ar LB (FF ++ LKq) M' q (8 * cap)
            /\ L5.big_at RSEGS M' o (L5.BO (copy_fb fbo (L5.bo_fb b') true) (L5.bo_len b') (L5.BDyn cap q))
            /\ L5C.obj_limbs RSEGS M' (L5.BO (copy_fb fbo (L5.bo_fb b') true) (L5.bo_len b') (L5.BDyn cap q)) ws'
            /\ ahpres L ar LB FF sp COPY_SCR [(o, 32)] M M'
  end.

Definition copy_spec_at (pc : Z) (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o o' sp r fbo : Z) (b' : L5.bigobj) (ws' : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 o' ->
    (L5.bo_dyn b' = true -> 8 * L5.bo_cap b' <= 2 ^ 27 /\ acredit_ok L cr (8 * L5.bo_cap b')) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp COPY_SCR ->
    ffr FF LK 2 -> ffrs FF sp ->
    L5.u8_at RSEGS M o fbo -> 0 <= fbo < 256 -> aobj FF o 32 -> shadow_zero M o 4 ->
    L5.big_at RSEGS M o' b' -> L5C.obj_limbs RSEGS M b' ws' -> aobj FF o' 32 -> shadow_zero M o' 4 ->
    (forall cap q, L5.bo_st b' = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (o + 32 <= o' \/ o' + 32 <= o) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        copy_post L ar LB FF LK' cr M M' R R' o o' sp fbo b' ws' g LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R pc M model) K.
Definition copy_spec := copy_spec_at COPY.
Definition copya_spec := copy_spec_at COPYA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STRINIT : Z := 0xa8a0c.
Definition STRINIT_SCR : Z := 64 + Z.max OPNEW_SCR MEM_SCR.
Definition str_cap (n : Z) : Z := if Z.eqb (Z.lor n 7) 23 then 26 else Z.lor n 7 + 1.

Definition strinit_post (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit)
           (M M' : word -> option byte) (R R' : bvmap 5 word) (o sp n : Z) (cs : list byte) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  (n <= 22 ->
     LB' = LB /\ cr' = cr /\ L5.u8_at RSEGS M' o (2 * n)
     /\ (forall i, 0 <= i < n -> exists c, nth_error cs (Z.to_nat i) = Some c /\ M' (Z_to_bv 64 (o + 1 + i)) = Some c) /\ L5.u8_at RSEGS M' (o + 1 + n) 0
     /\ ahpres L ar LB FF sp STRINIT_SCR [(o, 24)] M M')
  /\ (23 <= n -> exists p, let cap := str_cap n in
     LB' = (p, cap) :: LB /\ cr' = adebit L cr cap /\ afresh L ar LB (FF ++ LKq) M' p cap
     /\ L5.u64_at RSEGS M' o (cap + 1) /\ L5.u64_at RSEGS M' (o + 8) n /\ L5.u64_at RSEGS M' (o + 16) p
     /\ (forall i, 0 <= i < n -> exists c, nth_error cs (Z.to_nat i) = Some c /\ M' (Z_to_bv 64 (p + i)) = Some c) /\ L5.u8_at RSEGS M' (p + n) 0
     /\ ahpres L ar LB FF sp STRINIT_SCR [(o, 24)] M M').

Definition strinit_spec (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o s n sp r : Z) (cs : list byte),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 s -> getr R 12%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 ->
    (23 <= n -> acredit_ok L cr (str_cap n)) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp STRINIT_SCR ->
    aobj FF o 24 -> shadow_zero M o 3 ->
    rdn RSEGS M (Z_to_bv 64 s) (Z.to_nat n) = Some cs ->
    (n = 0 \/ exists b m, In (b, m) LB /\ b <= s /\ s + n <= b + m) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        strinit_post L ar LB FF LK' cr M M' R R' o sp n cs LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R STRINIT M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MUL10 : Z := 0x8f788.
Definition MUL10_SCR : Z := 64 + RESIZE_SCR.
Definition ADDD : Z := 0x8f984.
Definition ADDD_SCR : Z := 160 + RESIZE_SCR.

Definition reduced (ws : list Z) : Prop := ws = [] \/ nth (length ws - 1) ws 0 <> 0.

Definition arith_post (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit)
           (M M' : word -> option byte) (R R' : bvmap 5 word) (o sp SCR : Z) (b : L5.bigobj) (V' : Z) (g : growth)
           (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 o /\
  exists (ws' : list Z) (st' : L5.bstore),
    L5.limbs_val ws' = V' /\ reduced ws' /\ (Z.of_nat (length ws') <= Z.of_nat (L5.bo_len b) + 1) /\
    let b1 := L5.BO (match g with Same => L5.bo_fb b | Grown _ _ => Z.lor (L5.bo_fb b) 1 end) (length ws') st' in
    L5.big_at RSEGS M' o b1 /\ L5C.obj_limbs RSEGS M' b1 ws' /\
    match g with
    | Same => (L5.bo_dyn b = true \/ (L5.bo_len b <= 1)%nat) /\ LB' = LB /\ cr' = cr
              /\ match L5.bo_st b, st' with
                 | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
                 | L5.BInl _ _, L5.BInl _ _ => True
                 | _, _ => False end
              /\ ahpres L ar LB FF sp SCR [(o, 32); (L5.bo_data o b, 8 * (Z.of_nat (L5.bo_len b) + 1))] M M'
    | Grown q cap => L5.bo_dyn b = false /\ L5.bo_len b = 2%nat /\ cap = 8 /\ st' = L5.BDyn 8 q /\ LB' = (q, 64) :: LB /\ cr' = adebit L cr 64
              /\ afresh L ar LB (FF ++ LKq) M' q 64
              /\ ahpres L ar LB FF sp SCR [(o, 32)] M M'
    end.

Definition arith_spec_at (pc SCR : Z) (d : Z) (VAL : list Z -> Z -> Z) (y : Z) (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r : Z) (b : L5.bigobj) (ws : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 y -> Z.of_nat (L5.bo_len b) < 2 ^ 23 ->
    (L5.bo_dyn b = true -> Z.of_nat (L5.bo_len b) + 1 <= L5.bo_cap b) ->
    (L5.bo_dyn b = false -> L5.bo_len b = 2%nat -> acredit_ok L cr 64) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp SCR ->
    ffr FF LK d -> ffrs FF sp ->
    L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> L5.bo_neg b = false -> aobj FF o 32 -> shadow_zero M o 4 ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        arith_post L ar LB FF LK' cr M M' R R' o sp SCR b (VAL ws y) g LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R pc M model) K.
(* [comment removed for export] *)
Definition mul10_spec := arith_spec_at MUL10 MUL10_SCR 4 (fun ws _ => 10 * L5.limbs_val ws) 10.
Definition addd_spec (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall d, 0 <= d <= 9 -> arith_spec_at ADDD ADDD_SCR 5 (fun ws d => L5.limbs_val ws + d) d L ar HI.
End SCFG_1.
End L5CSA.
