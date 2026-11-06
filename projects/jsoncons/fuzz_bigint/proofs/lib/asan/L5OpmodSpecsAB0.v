(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA LibIface
     AsanAcct L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5CoreBB0 L5ParseSpecsAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5OMA.
Import L5A. Import L5CA. Import L5CSA. Import L5CB. Import L5PSA.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Definition acredit_for (L : asan_layout) (cr : credit) (k bytes : Z) : Prop :=
  k * hl_k_per_malloc L <= fst cr /\ hl_b_lin L * bytes + k * hl_b_overhead L <= snd cr.
Definition adebits (L : asan_layout) (cr : credit) (k bytes : Z) : credit :=
  (fst cr - k * hl_k_per_malloc L, snd cr - (hl_b_lin L * bytes + k * hl_b_overhead L)).
Definition acredit_after (L : asan_layout) (cr : credit) (k bytes : Z) (cr' : credit) : Prop := credit_le (adebits L cr k bytes) cr'.

Lemma adebits_1 L cr n : adebits L cr 1 n = adebit L cr n.
Proof. unfold adebits, adebit. f_equal; ring. Qed.
Lemma adebits_add L cr k1 b1 k2 b2 : adebits L (adebits L cr k1 b1) k2 b2 = adebits L cr (k1 + k2) (b1 + b2).
Proof. unfold adebits. cbn [fst snd]. f_equal; ring. Qed.
Lemma adebits_mono L c c' k b : credit_le c c' -> credit_le (adebits L c k b) (adebits L c' k b).
Proof. unfold credit_le, adebits. cbn [fst snd]. lia. Qed.
Lemma adebits_le L c k b k' b' : as0_layout2 L -> k' <= k -> b' <= b -> credit_le (adebits L c k b) (adebits L c k' b').
Proof. intros [_ (K & B & O)] Hk Hb. unfold credit_le, adebits. cbn [fst snd]. nia. Qed.
Lemma acredit_for_mono L c c' k b : acredit_for L c k b -> credit_le c c' -> acredit_for L c' k b.
Proof. unfold acredit_for, credit_le. lia. Qed.
Lemma acredit_for_le L c k b k' b' : as0_layout2 L -> acredit_for L c k b -> k' <= k -> b' <= b -> acredit_for L c k' b'.
Proof. intros [_ (K & B & O)] [H1 H2] Hk Hb. unfold acredit_for. split; nia. Qed.
(* [comment removed for export] *)
Lemma acredit_for_take L c k b n : as0_layout2 L -> acredit_for L c k b -> 1 <= k -> 0 <= n <= b ->
  acredit_ok L c n /\ acredit_for L (adebit L c n) (k - 1) (b - n).
Proof. intros [_ (K & B & O)] [H1 H2] Hk Hn. unfold acredit_ok, acredit_for, adebit. cbn [fst snd]. split; split; nia. Qed.
(* [comment removed for export] *)
Lemma acredit_for_split L c k b k1 b1 : as0_layout2 L -> acredit_for L c k b -> 0 <= k1 <= k -> 0 <= b1 <= b ->
  acredit_for L c k1 b1 /\ acredit_for L (adebits L c k1 b1) (k - k1) (b - b1).
Proof. intros [_ (K & B & O)] [H1 H2] Hk Hn. unfold acredit_for, adebits. cbn [fst snd]. split; split; nia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stksh (ar : asan_run) (M : word -> option byte) (lo : Z) : Prop := shadow_zero M lo ((Z.max (ar_sptop ar) (ar_stack_top ar) - lo) / 8).

Section Specs.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Definition OPMOD : Z := 0x9270c.
Definition TOP_PAD : Z := 0x8e580.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition OMF : Z := 0x8eb0c.
Definition OMF_INNER_RET : Z := 0x8eb34.  (* [comment removed for export] *)
Definition OMF1_RET : Z := 0x8e304.       (* [comment removed for export] *)
Definition OMF2_RET : Z := 0x8e344.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition landed_regs (R R' : bvmap 5 word) (sp rt8 : Z) : Prop :=
  getr R' 2%bv = Z_to_bv 64 (sp + 16) /\ getr R' 8%bv = Z_to_bv 64 rt8 /\
  (forall r : bv 5, In (bv_unsigned r) [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr R' r = getr R r).

(* [comment removed for export] *)
Definition x_is_a (M : word -> option byte) (xo fbx : Z) : Prop :=
  L5.big_at RSEGS M xo (L5.BO fbx 2 (L5.BInl A0 A1)) /\ Z.testbit fbx 1 = false.
(* [comment removed for export] *)
Definition b_ok (LB : list (Z * Z)) (M : word -> option byte) (bo : Z) (bb : L5.bigobj) (wb : list Z) : Prop :=
  L5.big_at RSEGS M bo bb /\ L5C.obj_limbs RSEGS M bb wb /\ reduced wb /\
  match L5.bo_st bb with L5.BInl _ _ => True | L5.BDyn cap q => In (q, 8 * cap) LB end.
(* [comment removed for export] *)
Definition x_after (LB : list (Z * Z)) (FFq : list fframe) (M' : word -> option byte) (xo : Z) (LB' : list (Z * Z)) : Prop :=
  exists bx wx, L5.big_at RSEGS M' xo bx /\ L5C.obj_limbs RSEGS M' bx wx /\ L5.bo_neg bx = false /\
    match L5.bo_st bx with
    | L5.BInl _ _ => LB' = LB
    | L5.BDyn cap q => cap = 8 /\ LB' = (q, 64) :: LB /\ afresh L ar LB FFq M' q 64
    end.

(* [comment removed for export] *)
Variable XS : Type.
Variable xs_pre : XS -> (word -> option byte) -> Prop.
Variable xs_foot : list L5.range.
Variable e2_landed e3_landed : XS -> list (Z * Z) -> list fframe -> list fframe -> credit -> Z -> (word -> option byte) -> bvmap 5 word ->
                               list (Z * Z) -> credit -> list fframe -> Prop.
Variables (SCRo D1 D2 D3 K1 K2 : Z) (bytes1 bytes2 : Z -> Z).

Definition opmod1A_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (xo bo sp r fbx rt8 : Z) (bb : L5.bigobj) (wb : list Z) (st : XS),
    let capb := L5.bo_cap bb in
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 xo -> getr R 11%bv = Z_to_bv 64 bo ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    r = OMF_INNER_RET -> getr R 9%bv = Z_to_bv 64 (sp + 16) ->          (* [comment removed for export] *)
    L5.u64_at RSEGS M sp rt8 -> L5.u64_at RSEGS M (sp + 8) OMF1_RET ->   (* [comment removed for export] *)
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 16 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp SCRo ->
    getr R 3%bv = Z_to_bv 64 67584 -> stksh ar M (sp - SCRo) ->          (* [comment removed for export] *)
    ffrk 1 FF LK D1 -> ffrk 2 FF LK D2 -> ffrk 3 FF LK D3 -> ffrs FF sp ->
    L5.img_clear M 0x10000 0x3c000 ->
    x_is_a M xo fbx -> aobj FF xo 32 -> shadow_zero M xo 4 ->
    b_ok LB M bo bb wb -> aobj FF bo 32 -> shadow_zero M bo 4 ->
    (xo + 32 <= bo \/ bo + 32 <= xo) ->                    (* [comment removed for export] *)
    L5.bo_cap bb <= 268 -> (L5.bo_dyn bb = true -> (3 <= L5.bo_len bb)%nat) ->
    acredit_for L cr K1 (bytes1 capb) ->
    xs_pre st M ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 xo ->
        x_after LB (FF ++ LK') M' xo LB' ->
        L5.big_at RSEGS M' bo bb -> L5C.obj_limbs RSEGS M' bb wb -> (1 <= L5.bo_len bb)%nat ->
        acredit_after L cr K1 (bytes1 capb) cr' ->
        ahpres L ar LB FF sp SCRo [(xo, 32)] M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        landed_regs R R' sp rt8 ->                  (* [comment removed for export] *)
        e2_landed st LB FF LK cr (sp + 16) M' R' LB' cr' LK' ->
        x_is_a M' xo fbx -> L5.big_at RSEGS M' bo bb -> L5C.obj_limbs RSEGS M' bb wb ->
        ahpres L ar LB FF sp SCRo ((xo, 32) :: xs_foot) M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' TOP_PAD M' model') K) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z))
            fbx' nx qx cr1,
        landed_regs R R' sp rt8 ->
        L5.big_at RSEGS M' xo (L5.BO fbx' nx (L5.BDyn 8 qx)) -> afresh L ar LB (FF ++ LK') M' qx 64 ->
        acredit_after L cr K1 (bytes1 capb) cr1 ->
        e3_landed st ((qx, 64) :: LB) FF LK cr1 (sp + 16) M' R' LB' cr' LK' ->
        L5.big_at RSEGS M' bo bb -> L5C.obj_limbs RSEGS M' bb wb ->
        ahpres L ar LB FF sp SCRo ((xo, 32) :: xs_foot) M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' TOP_PAD M' model') K) ->
    srealizes RSEGS SCFG (cfg R OPMOD M model) K.

(* [comment removed for export] *)
Definition a_ok (M : word -> option byte) (ao fba : Z) : Prop :=
  L5.big_at RSEGS M ao (L5.BO fba 2 (L5.BInl A0 A1)) /\ Z.testbit fba 1 = false.
(* [comment removed for export] *)
Definition y_ok (LB : list (Z * Z)) (M : word -> option byte) (yo : Z) (by_ : L5.bigobj) (wy : list Z) : Prop :=
  L5.big_at RSEGS M yo by_ /\ L5C.obj_limbs RSEGS M by_ wy /\ reduced wy /\
  match L5.bo_st by_ with
  | L5.BInl _ _ => True
  | L5.BDyn cap q => In (q, 8 * cap) LB /\ Z.of_nat (L5.bo_len by_) + 1 <= cap
  end.
(* [comment removed for export] *)
Definition y_after (LB : list (Z * Z)) (FFq : list fframe) (M' : word -> option byte) (yo : Z) (by_ : L5.bigobj) (LB' : list (Z * Z)) : Prop :=
  exists by' wy', L5.big_at RSEGS M' yo by' /\ L5C.obj_limbs RSEGS M' by' wy' /\
    match L5.bo_st by_, L5.bo_st by' with
    | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q /\ LB' = LB
    | L5.BInl _ _, L5.BInl _ _ => LB' = LB
    | L5.BInl _ _, L5.BDyn cap' q' => cap' = 8 /\ LB' = (q', 64) :: LB /\ afresh L ar LB FFq M' q' 64
    | L5.BDyn _ _, L5.BInl _ _ => False
    end.

Definition opmod2A_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (yo ao sp r fba : Z) (by_ : L5.bigobj) (wy : list Z),
    let capy := L5.bo_cap by_ in
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 yo -> getr R 11%bv = Z_to_bv 64 ao ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 16 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp SCRo ->
    stksh ar M (sp - SCRo) ->                                             (* [comment removed for export] *)
    ffrk 1 FF LK D1 -> ffrk 2 FF LK D2 -> ffrk 3 FF LK D3 -> ffrs FF sp ->
    L5.img_clear M 0x10000 0x3c000 ->
    y_ok LB M yo by_ wy -> aobj FF yo 32 -> shadow_zero M yo 4 -> (1 <= L5.bo_len by_)%nat -> L5.bo_cap by_ <= 268 ->
    a_ok M ao fba -> aobj FF ao 32 -> shadow_zero M ao 4 ->
    (yo + 32 <= ao \/ ao + 32 <= yo) ->
    acredit_for L cr K2 (bytes2 capy) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 yo ->
        y_after LB (FF ++ LK') M' yo by_ LB' ->
        a_ok M' ao fba ->
        acredit_after L cr K2 (bytes2 capy) cr' ->
        ahpres L ar LB FF sp SCRo [(yo, 32); (L5.bo_data yo by_, 8 * L5.bo_cap by_)] M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R OPMOD M model) K.
End Specs.
End SCFG_1.
End L5OMA.
