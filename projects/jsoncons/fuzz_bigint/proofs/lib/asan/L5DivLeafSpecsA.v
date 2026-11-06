(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AsanAcct L5Defs L5Kn L5KnA L5Core L5Words L5LazyA L5DefsA L5CoreA L5CoreSpecsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5DLA.
Import L5A. Import L5CA. Import L5CSA. Import L5W.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition resize_post_at (c : Z) (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit)
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
            /\ ahpres L ar LB FF sp (RESIZE_SCR + c) [(o, 32); (L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b), 8 * Z.max 0 (Z.of_nat n - Z.of_nat (L5.bo_len b)))] M M'
  | Grown q cap => L5.bo_dyn b = false /\ (3 <= n)%nat /\ cap = round_up (Z.of_nat n) /\ LB' = (q, 8 * cap) :: LB /\ cr' = adebit L cr (8 * cap)
            /\ afresh L ar LB (FF ++ LKq) M' q (8 * cap)
            /\ L5.big_at RSEGS M' o (L5.BO (Z.lor (L5.bo_fb b) 1) n (L5.BDyn cap q))
            /\ L5C.obj_limbs RSEGS M' (L5.BO (Z.lor (L5.bo_fb b) 1) n (L5.BDyn cap q)) (resize_limbs ws n)
            /\ ahpres L ar LB FF sp (RESIZE_SCR + c) [(o, 32)] M M'
  end.

Definition resize_spec_at (c : Z) (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r : Z) (n : nat) (b : L5.bigobj) (ws : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 (Z.of_nat n) -> Z.of_nat n <= 2 ^ 23 ->
    (L5.bo_dyn b = true -> Z.of_nat n <= L5.bo_cap b) ->
    ((3 <= n)%nat -> L5.bo_dyn b = false -> acredit_ok L cr (8 * round_up (Z.of_nat n))) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = c -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp (RESIZE_SCR + c) ->
    ffr FF LK 4 -> ffrs FF sp ->
    L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> aobj FF o 32 -> shadow_zero M o 4 ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        resize_post_at c L ar LB FF LK' cr M M' R R' o sp n b ws g LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R RESIZE M model) K.

Lemma resize_spec_at_0 L ar HI : resize_spec L ar HI -> resize_spec_at 0 L ar HI.
Proof. intros H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MULM : Z := 0x93d1c.
Definition MULM_SCR : Z := 64 + RESIZE_SCR.

Definition mulm_postA_at (c : Z) (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit)
           (M M' : word -> option byte) (R R' : bvmap 5 word) (o sp y : Z) (b : L5.bigobj) (ws : list Z) (g : growth)
           (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 o /\
  let m := Datatypes.S (L5.bo_len b) in
  let rw := mulw_words ws y in
  let n' := rlen rw in
  let fbg := match g with Same => L5.bo_fb b | Grown _ _ => Z.lor (L5.bo_fb b) 1 end in
  let fb' := if Nat.eqb n' 0 then Z.land fbg 253 else fbg in
  length rw = m /\ words_ok rw /\ (n' <= m)%nat /\
  exists st',
    L5.big_at RSEGS M' o (L5.BO fb' n' st') /\ L5C.obj_limbs RSEGS M' (L5.BO fb' m st') rw /\
    match g with
    | Same => (L5.bo_dyn b = true \/ (m <= 2)%nat) /\ LB' = LB /\ cr' = cr
              /\ match L5.bo_st b, st' with
                 | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
                 | L5.BInl _ _, L5.BInl _ _ => True
                 | _, _ => False end
              /\ ahpres L ar LB FF sp (MULM_SCR + c) [(o, 32); (L5.bo_data o b, 8 * (Z.of_nat (L5.bo_len b) + 1))] M M'
    | Grown q cap => L5.bo_dyn b = false /\ L5.bo_len b = 2%nat /\ cap = 8 /\ st' = L5.BDyn 8 q /\ LB' = (q, 64) :: LB /\ cr' = adebit L cr 64
              /\ afresh L ar LB (FF ++ LKq) M' q 64
              /\ ahpres L ar LB FF sp (MULM_SCR + c) [(o, 32)] M M'
    end.

Definition mulm_specA_at (c : Z) (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r y : Z) (b : L5.bigobj) (ws : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 y -> 0 <= y < 2 ^ 64 ->
    (1 <= L5.bo_len b)%nat -> Z.of_nat (L5.bo_len b) < 2 ^ 23 ->
    (L5.bo_dyn b = true -> Z.of_nat (L5.bo_len b) + 1 <= L5.bo_cap b) ->
    (L5.bo_dyn b = false -> L5.bo_len b = 2%nat -> acredit_ok L cr 64) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = c -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp (MULM_SCR + c) ->
    ffr FF LK 4 -> ffrs FF sp ->
    L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> aobj FF o 32 -> shadow_zero M o 4 ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        mulm_postA_at c L ar LB FF LK' cr M M' R R' o sp y b ws g LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R MULM M model) K.
Definition mulm_postA := mulm_postA_at 0.
Definition mulm_specA := mulm_specA_at 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SHL : Z := 0x93a50.
Definition SHL_SCR : Z := 64 + RESIZE_SCR.
Definition shl_result (ws : list Z) (k : Z) : list Z := if k =? 0 then ws else shl_words ws k.

Definition shl_postA_at (c : Z) (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit)
           (M M' : word -> option byte) (R R' : bvmap 5 word) (o sp k : Z) (b : L5.bigobj) (ws : list Z) (g : growth)
           (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 o /\
  let rw := shl_result ws k in
  let m := length rw in
  let n' := rlen rw in
  let fbg := match g with Same => L5.bo_fb b | Grown _ _ => Z.lor (L5.bo_fb b) 1 end in
  let fb' := if Nat.eqb n' 0 then Z.land fbg 253 else fbg in
  words_ok rw /\ (n' <= m)%nat /\
  exists st',
    L5.big_at RSEGS M' o (L5.BO fb' n' st') /\ L5C.obj_limbs RSEGS M' (L5.BO fb' m st') rw /\
    match g with
    | Same => (L5.bo_dyn b = true \/ (m <= 2)%nat) /\ LB' = LB /\ cr' = cr
              /\ match L5.bo_st b, st' with
                 | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
                 | L5.BInl _ _, L5.BInl _ _ => True
                 | _, _ => False end
              /\ ahpres L ar LB FF sp (SHL_SCR + c) [(o, 32); (L5.bo_data o b, 8 * Z.of_nat m)] M M'
    | Grown q cap => L5.bo_dyn b = false /\ L5.bo_len b = 2%nat /\ 1 <= k /\ cap = 8 /\ st' = L5.BDyn 8 q /\ LB' = (q, 64) :: LB /\ cr' = adebit L cr 64
              /\ afresh L ar LB (FF ++ LKq) M' q 64
              /\ ahpres L ar LB FF sp (SHL_SCR + c) [(o, 32)] M M'
    end.

Definition shl_specA_at (c : Z) (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r k : Z) (b : L5.bigobj) (ws : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 k -> 0 <= k <= 63 ->
    (1 <= L5.bo_len b)%nat -> Z.of_nat (L5.bo_len b) < 2 ^ 23 ->
    (L5.bo_dyn b = true -> Z.of_nat (L5.bo_len b) + 1 <= L5.bo_cap b) ->
    (1 <= k -> L5.bo_dyn b = false -> L5.bo_len b = 2%nat -> acredit_ok L cr 64) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = c -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp (SHL_SCR + c) ->
    ffr FF LK 4 -> ffrs FF sp ->
    L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> aobj FF o 32 -> shadow_zero M o 4 ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        shl_postA_at c L ar LB FF LK' cr M M' R R' o sp k b ws g LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R SHL M model) K.
Definition shl_postA := shl_postA_at 0.
Definition shl_specA := shl_specA_at 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NORM : Z := 0x932a0.
Definition NORM_SCR : Z := 80 + (MULM_SCR + 16).
Definition MAXW : Z := 18446744073709551615.

Definition clz_of (w : Z) : Z := 63 - Z.log2 w.
(* [comment removed for export] *)
Definition second (nd : nat) (D : list Z) : bool := (2 <=? nd)%nat && (nth_w D (nd - 1) <? nth_w D (nd - 2)).
(* [comment removed for export] *)
Definition norm_words (ws : list Z) (c : Z) (sec : bool) : list Z :=
  let D := shl_result ws c in if sec then mulw_words (firstn (rlen D) D) MAXW else D.

Definition blocks_of (g : growth) : list (Z * Z) := match g with Same => [] | Grown A cap => [(A, 8 * cap)] end.
Definition obj_after (M' : word -> option byte) (o : Z) (b : L5.bigobj) (rw : list Z) (g : growth) (st' : L5.bstore) : Prop :=
  let m := length rw in let n' := rlen rw in
  let fbg := match g with Same => L5.bo_fb b | Grown _ _ => Z.lor (L5.bo_fb b) 1 end in
  let fb' := if Nat.eqb n' 0 then Z.land fbg 253 else fbg in
  words_ok rw /\ (n' <= m)%nat /\
  L5.big_at RSEGS M' o (L5.BO fb' n' st') /\ L5C.obj_limbs RSEGS M' (L5.BO fb' m st') rw /\
  (match st' with L5.BDyn cap _ => Z.of_nat m <= cap | L5.BInl _ _ => (m <= 2)%nat end) /\
  match g with
  | Same => match L5.bo_st b, st' with
            | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
            | L5.BInl _ _, L5.BInl _ _ => True
            | _, _ => False end
  | Grown A cap => L5.bo_dyn b = false /\ cap = 8 /\ st' = L5.BDyn cap A
  end.
Definition dyn_area (o : Z) (b : L5.bigobj) : list L5.range :=
  match L5.bo_st b with L5.BDyn cap q => [(q, 8 * cap)] | L5.BInl _ _ => [] end.
Definition norm_W (od on px : Z) (bd bn : L5.bigobj) : list L5.range :=
  [(od, 32); (on, 32); (px, 4)] ++ dyn_area od bd ++ dyn_area on bn.
Definition cnt (b : L5.bigobj) : Z := if L5.bo_dyn b then 0 else 1.
Fixpoint adebl (L : asan_layout) (cr : credit) (bl : list (Z * Z)) : credit :=
  match bl with [] => cr | (A, n) :: bl' => adebit L (adebl L cr bl') n end.
(* [comment removed for export] *)
Definition acredits (L : asan_layout) (cr : credit) (k : Z) : Prop :=
  k * hl_k_per_malloc L <= fst cr /\ k * (hl_b_lin L * 64 + hl_b_overhead L) <= snd cr.

Definition norm_postA (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit)
           (M M' : word -> option byte) (R R' : bvmap 5 word)
           (od on px sp : Z) (bd bn : L5.bigobj) (wd wn : list Z) (c : Z) (gd gn : growth) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  let nd := L5.bo_len bd in
  c = clz_of (nth_w wd (nd - 1)) /\ 0 <= c <= 63 /\ 2 ^ 63 <= nth_w wd (nd - 1) * 2 ^ c < 2 ^ 64 /\
  let D := shl_result wd c in
  let sec := second nd D in
  getr R' 10%bv = Z_to_bv 64 (if sec then 1 else 0) /\
  L5.u32_at RSEGS M' px c /\
  (exists std stn, obj_after M' od bd (norm_words wd c sec) gd std /\ obj_after M' on bn (norm_words wn c sec) gn stn) /\
  LB' = blocks_of gn ++ blocks_of gd ++ LB /\ cr' = adebl L cr (blocks_of gn ++ blocks_of gd) /\
  (match gd with Same => True | Grown A cap => afresh L ar LB (FF ++ LKq) M' A (8 * cap) end) /\
  (match gn with Same => True | Grown A cap => afresh L ar (blocks_of gd ++ LB) (FF ++ LKq) M' A (8 * cap) end) /\
  ahpres L ar LB FF sp NORM_SCR (norm_W od on px bd bn) M M' /\
  (match gd with Same => True | Grown _ _ => (3 <= length D)%nat \/ sec = true end) /\
  (match gn with Same => True | Grown _ _ => (3 <= length (shl_result wn c))%nat \/ sec = true end).

Definition norm_specA (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (od on px sp r : Z) (bd bn : L5.bigobj) (wd wn : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 11%bv = Z_to_bv 64 od -> getr R 12%bv = Z_to_bv 64 on -> getr R 13%bv = Z_to_bv 64 px ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp NORM_SCR ->
    ffr FF LK 4 -> ffrs FF sp ->
    (* [comment removed for export] *)
    L5.big_at RSEGS M od bd -> L5C.obj_limbs RSEGS M bd wd -> (1 <= L5.bo_len bd <= 290)%nat ->
    nth_w wd (L5.bo_len bd - 1) <> 0 -> ((2 <= L5.bo_len bd)%nat -> nth_w wd (L5.bo_len bd - 1) < 2 ^ 63) ->
    L5.big_at RSEGS M on bn -> L5C.obj_limbs RSEGS M bn wn -> (1 <= L5.bo_len bn <= 290)%nat ->
    ((2 <= L5.bo_len bd)%nat -> (2 <= L5.bo_len bn)%nat /\ exists i, (i < L5.bo_len bn)%nat /\ nth_w wn i <> 0) ->
    aobj FF od 32 -> shadow_zero M od 4 -> aobj FF on 32 -> shadow_zero M on 4 -> (od + 32 <= on \/ on + 32 <= od) ->
    px mod 4 = 0 -> sp <= px -> L5.defined M px 4 -> px + 4 <= ar_sptop ar -> shadow_zero M px 1 ->          (* [comment removed for export] *)
          (* [comment removed for export] *)
    (forall cap q, L5.bo_st bd = L5.BDyn cap q -> In (q, 8 * cap) LB /\ Z.of_nat (L5.bo_len bd) + 1 <= cap) ->
    (forall cap q, L5.bo_st bn = L5.BDyn cap q -> In (q, 8 * cap) LB /\ Z.of_nat (L5.bo_len bn) + 1 <= cap) ->
    (* [comment removed for export] *)
    (second (L5.bo_len bd) (shl_result wd (clz_of (nth_w wd (L5.bo_len bd - 1)))) = true ->
       (L5.bo_dyn bd = true -> Z.of_nat (L5.bo_len bd) + 2 <= L5.bo_cap bd) /\ (L5.bo_dyn bn = true -> Z.of_nat (L5.bo_len bn) + 2 <= L5.bo_cap bn)) ->
    (forall cd qd cn qn, L5.bo_st bd = L5.BDyn cd qd -> L5.bo_st bn = L5.BDyn cn qn -> qd + 8 * cd <= qn \/ qn + 8 * cn <= qd) ->
    acredits L cr (cnt bd + cnt bn) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (c : Z) (gd gn : growth) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        norm_postA L ar LB FF LK' cr M M' R R' od on px sp bd bn wd wn c gd gn LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R NORM M model) K.

End SCFG_1.
End L5DLA.
