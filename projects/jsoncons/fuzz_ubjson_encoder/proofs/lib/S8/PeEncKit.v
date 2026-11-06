(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk HeapIface L5Defs L5Core L5CoreKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmSpecs PmStep PmKeep PmFrame PmParKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCFrame.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEEK.

Definition ebump (r : list eitem) : list eitem :=
  match r with [] => [] | e :: r' => EI (ei_kind e) (ei_len e) ((ei_cnt e + 1) mod TWO64) :: r' end.
Lemma ebump_length r : length (ebump r) = length r.
Proof. destruct r; reflexivity. Qed.
Lemma nth_top (rr : list eitem) e0 d : nth (length rr) (rev rr ++ [e0]) d = e0.
Proof. rewrite <- (length_rev rr). apply nth_middle. Qed.

Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.
Variable E : pe_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KL : PMK.klayout segs L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Abbreviation enc_at := (PEC.enc_at segs E L PMSP.T3 PMSP.T4).

Lemma heap_perm l1 l2 cr M VM : Permutation l1 l2 -> hi_heap HI l1 cr M VM -> hi_heap HI l2 cr M VM.
Proof.
  intros PERM HH. apply (hio_perm L SCFG HI HIok _ _ cr M VM HH).
  - intros b0. split; apply Permutation_in; [exact PERM| apply Permutation_sym; exact PERM].
  - apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_map fst PERM)). apply NoDup_ListNoDup. exact (PMPK.heap_nodup L HI HIok _ cr M _ HH).
Qed.

Lemma own_not_client OWN LB cr M VM B m a sp scr :
  hi_heap HI (OWN ++ LB) cr M VM -> In (B, m) OWN -> B <= a < B + m -> ~ client_addr L LB sp scr a.
Proof.
  intros HH Hin Ha. assert (BR : PMFR.brange L (OWN ++ LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  destruct (BR B m (in_or_app _ _ _ (or_introl Hin))) as (Z0 & Z1 & Z4).
  intros [((B' & m') & Hb & Hr)|[[S1 _]|[IM _]]]; [|lia|lia]. cbn in Hr.
  assert (NE : B <> B') by (apply (PMPK.fst_neq_app OWN LB B m B' m' (PMPK.heap_nodup L HI HIok _ _ _ _ HH) Hin Hb)).
  destruct (PMPK.blocks_apart_heap L HI HIok _ cr M _ B m B' m' HH (in_or_app _ _ _ (or_introl Hin)) (in_or_app _ _ _ (or_intror Hb)) NE); lia.
Qed.

Lemma ek_piece_own OWN LB cr M0 VM sp scr W M M' (Pf : Z -> Prop) B m :
  hi_heap HI (OWN ++ LB) cr M0 VM -> In (B, m) OWN ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Pf a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  hl_ceil L <= sp - scr -> 0x7fff80000000 <= hl_sptop L ->
  (forall a, Pf a -> (sp - scr <= a < sp) \/ PMK.inW W a \/ (B <= a < B + m)) -> PMK.ek L LB sp scr W M M'.
Proof.
  intros HH Hin FRZ Hc Hw FP. pose proof (PMK.kl_img segs L KL) as KI. unfold hl_ceil in Hc.
  assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M0 _ HH); apply incl_appr; apply incl_refl).
  apply (PMK.ek_piece L LB sp scr W M M' Pf FRZ). intros a Ha CA NE OW Pa. destruct (FP a Pa) as [S|[I|Bk]].
  - destruct CA as [((b & m') & Hb & Hr)|[[S1 S2]|[IM _]]]; [pose proof (PMFR.brange_hi L LB BR _ Hb) as X; cbn in X, Hr; lia| exact (S2 S)| lia].
  - exact (PMK.inW_not_outside W a I OW).
  - exact (own_not_client OWN LB cr M0 VM B m a sp scr HH Hin Bk CA).
Qed.
Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & EQ). apply Nat.eqb_eq in EQ. subst x. exact Hx.
Qed.
Lemma al8_item eb n : eb mod 8 = 0 -> (eb + 24 * n) mod 8 = 0.
Proof. intros H. rewrite Z.add_mod, H by lia. replace (24 * n) with ((3 * n) * 8) by lia. rewrite Z.mod_mul by lia. reflexivity. Qed.

Lemma m8_of16 fb c : fb mod 16 = 0 -> c mod 8 = 0 -> (fb + c) mod 8 = 0.
Proof. intros H1 H2. rewrite Z.add_mod, H2, Z.add_0_r, Z.mod_mod by lia. apply PMPK.m16_8. exact H1. Qed.
Lemma perm4 (a b c d : list (Z * Z)) : Permutation (a ++ b ++ c ++ d) (c ++ a ++ b ++ d).
Proof. rewrite (app_assoc a b (c ++ d)), (app_assoc a b d). apply Permutation_app_swap_app. Qed.

Lemma enc_depth (M M' : word -> option byte) ov fb eb ek stk d d' :
  enc_at M ov fb (PEC.ENC eb ek stk d) ->
  0 <= ov -> ov + 56 <= 2 ^ 64 -> (0 < ek -> 0 <= eb /\ eb + PEC.ESZ * PEC.ecap ek <= 2 ^ 64) ->
  (forall i, 0 <= i < 2 ^ 64 -> ov <= i < ov + 56 -> ~ (ov + 48 <= i < ov + 52) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (0 < ek -> forall i, 0 <= i < 2 ^ 64 -> eb <= i < eb + PEC.ESZ * PEC.ecap ek -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  mem_grows M M' -> L5.u32_at segs M' (ov + 48) d' -> 0 <= d' <= MAX_DEPTH + 1 ->
  enc_at M' ov fb (PEC.ENC eb ek stk d').
Proof.
  intros EA Ho Ho' BB AGO AGB MG U48 Hd'. unfold PEC.enc_at in EA |- *. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EA |- *.
  destruct EA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & _ & Hk & Hlen & Hd & Hk0 & HB & HIT). pose proof (PEC.ecap_nonneg ek) as CN.
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 48 -> L5C.agree_on M M' a n) by (intros a n X1 X2 i Hi; apply AGO; lia).
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V32]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V40]|].
  split; [exact U48|]. split; [exact (L5.defined_grows M M' _ _ MG D)|]. split; [exact I|].
  split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hd'|]. split; [exact Hk0|]. split.
  - intros Hp. destruct (HB Hp) as (AL & DB & BR & _ & _). split; [exact AL|]. split; [exact (L5.defined_grows M M' _ _ MG DB)|]. split; [exact BR|]. split; exact I.
  - intros i Hi. pose proof (HIT i Hi) as IT.
    assert (Hp : 0 < ek).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in Hlen. rewrite Z0 in Hlen. cbn in Hlen. lia. }
    destruct (BB Hp) as (B0 & B1).
    apply (PECF.eitem_at_agree segs M M'); [| unfold PEC.ESZ in *; lia | unfold PEC.ESZ in *; lia | exact IT].
    intros j Hj. apply (AGB Hp); unfold PEC.ESZ in *; lia.
Qed.

Definition cc_rng (eb : Z) (rr : list eitem) (i : Z) : Prop :=
  match rr with [] => False | _ :: rr' => eb + PEC.ESZ * Z.of_nat (length rr') + 16 <= i < eb + PEC.ESZ * Z.of_nat (length rr') + 24 end.
Lemma cc_rng_dec eb rr i : {cc_rng eb rr i} + {~ cc_rng eb rr i}.
Proof. destruct rr; cbn; [right; tauto| apply PMK.rng_dec]. Qed.
Lemma cc_rng_in eb rr i : cc_rng eb rr i -> 1 <= Z.of_nat (length rr) /\ eb + PEC.ESZ * (Z.of_nat (length rr) - 1) + 16 <= i < eb + PEC.ESZ * Z.of_nat (length rr).
Proof. destruct rr as [|e rr']; cbn [cc_rng length]; [tauto|]. unfold PEC.ESZ. lia. Qed.

Lemma enc_pop (M M' : word -> option byte) ov fb eb ek rr e0 d d' :
  enc_at M ov fb (PEC.ENC eb ek (rev rr ++ [e0]) d) ->
  0 <= ov -> ov + 56 <= 2 ^ 64 -> (0 < ek -> 0 <= eb /\ eb + PEC.ESZ * PEC.ecap ek <= 2 ^ 64) ->
  (forall i, 0 <= i < 2 ^ 64 -> ov <= i < ov + 56 -> ~ (ov + 32 <= i < ov + 40) -> ~ (ov + 48 <= i < ov + 52) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (0 < ek -> forall i, 0 <= i < 2 ^ 64 -> eb <= i < eb + PEC.ESZ * PEC.ecap ek -> ~ cc_rng eb rr i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  mem_grows M M' ->
  L5.u64_at segs M' (ov + 32) (eb + PEC.ESZ * Z.of_nat (length rr)) ->
  L5.u32_at segs M' (ov + 48) d' -> 0 <= d' <= MAX_DEPTH + 1 ->
  (forall e2 rr', rr = e2 :: rr' -> L5.u64_at segs M' (eb + PEC.ESZ * Z.of_nat (length rr') + 16) ((ei_cnt e2 + 1) mod TWO64)) ->
  enc_at M' ov fb (PEC.ENC eb ek (rev (ebump rr)) d').
Proof.
  intros EA Ho Ho' BB AGO AGB MG U32 U48 Hd' UCC. unfold PEC.enc_at in EA |- *. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EA |- *.
  destruct EA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & _ & Hk & Hlen & Hd & Hk0 & HB & HIT). pose proof (PEC.ecap_nonneg ek) as CN.
  rewrite length_app, length_rev in Hlen, HB, HIT. cbn [length] in Hlen, HB, HIT.
  assert (LEN' : length (rev (ebump rr)) = length rr) by (rewrite length_rev; apply ebump_length).
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 32 -> L5C.agree_on M M' a n) by (intros a n X1 X2 i Hi; apply AGO; lia).
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [rewrite LEN'; exact U32|].
  split; [apply (L5C.u64_at_agree segs M M'); [intros i Hi; apply AGO; lia|lia|lia| exact V40]|].
  split; [exact U48|]. split; [exact (L5.defined_grows M M' _ _ MG D)|]. split; [exact I|].
  split; [exact Hk|]. split; [rewrite LEN'; lia|]. split; [exact Hd'|]. split; [exact Hk0|]. split.
  - intros Hp. destruct (HB Hp) as (AL & DB & BR & _ & _). split; [exact AL|]. split; [exact (L5.defined_grows M M' _ _ MG DB)|]. split; [exact BR|]. split; exact I.
  - rewrite LEN'. intros i Hi.
    assert (Hp : 0 < ek).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in Hlen. rewrite Z0 in Hlen. cbn in Hlen. lia. }
    destruct (BB Hp) as (B0 & B1).
    destruct rr as [|e2 rr']; [cbn in Hi; lia|]. cbn [ebump rev]. cbn [length] in Hi, Hlen, HB, HIT.
    assert (ORIG : forall j, (j <= length rr')%nat -> PEC.eitem_at segs M (eb + PEC.ESZ * Z.of_nat j) (nth j (rev rr' ++ [e2]) (EI 0 0 0))).
    { intros j Hj. specialize (HIT j ltac:(lia)). cbn [rev] in HIT. rewrite (app_nth1 (rev rr' ++ [e2]) [e0]) in HIT; [exact HIT|].
      rewrite length_app, length_rev. cbn. lia. }
    destruct (Nat.lt_ge_cases i (length rr')) as [LT|GE].
    + rewrite app_nth1 by (rewrite length_rev; exact LT). specialize (ORIG i ltac:(lia)). rewrite app_nth1 in ORIG by (rewrite length_rev; exact LT).
      apply (PECF.eitem_at_agree segs M M'); [| unfold PEC.ESZ in *; lia | unfold PEC.ESZ in *; lia | exact ORIG].
      intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [cc_rng]. unfold PEC.ESZ in *. lia.
    + assert (EI_ : i = length rr') by lia. subst i. rewrite nth_top. specialize (ORIG (length rr') ltac:(lia)). rewrite nth_top in ORIG.
      destruct ORIG as (K0c & K8c & _). split; [|split].
      * cbn [ei_kind]. apply (PMF.u32_at_agree segs M M'); [| unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia| exact K0c].
        intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [cc_rng]. unfold PEC.ESZ in *. lia.
      * cbn [ei_len]. apply (L5C.u64_at_agree segs M M'); [| unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia| exact K8c].
        intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [cc_rng]. unfold PEC.ESZ in *. lia.
      * cbn [ei_cnt]. exact (UCC e2 rr' eq_refl).
Qed.

Lemma enc_bump (M M' : word -> option byte) ov fb eb ek rr d :
  enc_at M ov fb (PEC.ENC eb ek (rev rr) d) ->
  0 <= ov -> ov + 56 <= 2 ^ 64 -> (0 < ek -> 0 <= eb /\ eb + PEC.ESZ * PEC.ecap ek <= 2 ^ 64) ->
  (forall i, 0 <= i < 2 ^ 64 -> ov <= i < ov + 56 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (0 < ek -> forall i, 0 <= i < 2 ^ 64 -> eb <= i < eb + PEC.ESZ * PEC.ecap ek -> ~ cc_rng eb rr i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  mem_grows M M' ->
  (forall e2 rr', rr = e2 :: rr' -> L5.u64_at segs M' (eb + PEC.ESZ * Z.of_nat (length rr') + 16) ((ei_cnt e2 + 1) mod TWO64)) ->
  enc_at M' ov fb (PEC.ENC eb ek (rev (ebump rr)) d).
Proof.
  intros EA Ho Ho' BB AGO AGB MG UCC. unfold PEC.enc_at in EA |- *. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EA |- *.
  destruct EA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & _ & Hk & Hlen & Hd & Hk0 & HB & HIT). pose proof (PEC.ecap_nonneg ek) as CN.
  rewrite length_rev in Hlen, HB, HIT, V32.
  assert (LEN' : length (rev (ebump rr)) = length rr) by (rewrite length_rev; apply ebump_length).
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 56 -> L5C.agree_on M M' a n) by (intros a n X1 X2 i Hi; apply AGO; lia).
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [rewrite LEN'; apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V32]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V40]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V48]|].
  split; [exact (L5.defined_grows M M' _ _ MG D)|]. split; [exact I|].
  split; [exact Hk|]. split; [rewrite LEN'; lia|]. split; [exact Hd|]. split; [exact Hk0|]. split.
  - intros Hp. destruct (HB Hp) as (AL & DB & BR & _ & _). split; [exact AL|]. split; [exact (L5.defined_grows M M' _ _ MG DB)|]. split; [exact BR|]. split; exact I.
  - rewrite LEN'. intros i Hi.
    assert (Hp : 0 < ek).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in Hlen. rewrite Z0 in Hlen. cbn in Hlen. lia. }
    destruct (BB Hp) as (B0 & B1).
    destruct rr as [|e2 rr']; [cbn in Hi; lia|]. cbn [ebump rev]. cbn [length rev] in Hi, Hlen, HB, HIT.
    destruct (Nat.lt_ge_cases i (length rr')) as [LT|GE].
    + rewrite app_nth1 by (rewrite length_rev; exact LT). specialize (HIT i ltac:(lia)). rewrite app_nth1 in HIT by (rewrite length_rev; exact LT).
      apply (PECF.eitem_at_agree segs M M'); [| unfold PEC.ESZ in *; lia | unfold PEC.ESZ in *; lia | exact HIT].
      intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [cc_rng]. unfold PEC.ESZ in *. lia.
    + assert (EI_ : i = length rr') by lia. subst i. rewrite nth_top. specialize (HIT (length rr') ltac:(lia)). rewrite nth_top in HIT.
      destruct HIT as (K0c & K8c & _). split; [|split].
      * cbn [ei_kind]. apply (PMF.u32_at_agree segs M M'); [| unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia| exact K0c].
        intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [cc_rng]. unfold PEC.ESZ in *. lia.
      * cbn [ei_len]. apply (L5C.u64_at_agree segs M M'); [| unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia| exact K8c].
        intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [cc_rng]. unfold PEC.ESZ in *. lia.
      * cbn [ei_cnt]. exact (UCC e2 rr' eq_refl).
Qed.

Lemma enc_upd (M M' : word -> option byte) ov fb eb ek stk d d' :
  enc_at M ov fb (PEC.ENC eb ek stk d) ->
  0 <= ov -> ov + 56 <= 2 ^ 64 -> (0 < ek -> 0 <= eb /\ eb + PEC.ESZ * PEC.ecap ek <= 2 ^ 64) ->
  (forall i, 0 <= i < 2 ^ 64 -> ov <= i < ov + 56 -> ~ (ov + 32 <= i < ov + 40) -> ~ (ov + 48 <= i < ov + 52) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (0 < ek -> forall i, 0 <= i < 2 ^ 64 -> eb <= i < eb + PEC.ESZ * PEC.ecap ek -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  mem_grows M M' ->
  L5.u64_at segs M' (ov + 32) (eb + PEC.ESZ * Z.of_nat (length stk)) ->
  L5.u32_at segs M' (ov + 48) d' -> 0 <= d' <= MAX_DEPTH + 1 ->
  enc_at M' ov fb (PEC.ENC eb ek stk d').
Proof.
  intros EA Ho Ho' BB AGO AGB MG U32 U48 Hd'. unfold PEC.enc_at in EA |- *. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EA |- *.
  destruct EA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & _ & Hk & Hlen & Hd & Hk0 & HB & HIT). pose proof (PEC.ecap_nonneg ek) as CN.
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 32 -> L5C.agree_on M M' a n) by (intros a n X1 X2 i Hi; apply AGO; lia).
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [exact U32|].
  split; [apply (L5C.u64_at_agree segs M M'); [intros i Hi; apply AGO; lia|lia|lia| exact V40]|].
  split; [exact U48|]. split; [exact (L5.defined_grows M M' _ _ MG D)|]. split; [exact I|].
  split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hd'|]. split; [exact Hk0|]. split.
  - intros Hp. destruct (HB Hp) as (AL & DB & BR & _ & _). split; [exact AL|]. split; [exact (L5.defined_grows M M' _ _ MG DB)|]. split; [exact BR|]. split; exact I.
  - intros i Hi. pose proof (HIT i Hi) as IT.
    assert (Hp : 0 < ek).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in Hlen. rewrite Z0 in Hlen. cbn in Hlen. lia. }
    destruct (BB Hp) as (B0 & B1).
    apply (PECF.eitem_at_agree segs M M'); [| unfold PEC.ESZ in *; lia | unfold PEC.ESZ in *; lia | exact IT].
    intros j Hj. apply (AGB Hp); unfold PEC.ESZ in *; lia.
Qed.

Lemma enc_push (M M' : word -> option byte) ov fb eb ek stk d d' it :
  enc_at M ov fb (PEC.ENC eb ek stk d) ->
  0 <= ov -> ov + 56 <= 2 ^ 64 -> (0 < ek -> 0 <= eb /\ eb + PEC.ESZ * PEC.ecap ek <= 2 ^ 64) ->
  (forall i, 0 <= i < 2 ^ 64 -> ov <= i < ov + 56 -> ~ (ov + 32 <= i < ov + 40) -> ~ (ov + 48 <= i < ov + 52) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (0 < ek -> forall i, 0 <= i < 2 ^ 64 -> eb <= i < eb + PEC.ESZ * Z.of_nat (length stk) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  mem_grows M M' ->
  L5.u64_at segs M' (ov + 32) (eb + PEC.ESZ * (Z.of_nat (length stk) + 1)) ->
  L5.u32_at segs M' (ov + 48) d' -> 0 <= d' <= MAX_DEPTH + 1 ->
  Z.of_nat (length stk) + 1 <= PEC.ecap ek ->
  PEC.eitem_at segs M' (eb + PEC.ESZ * Z.of_nat (length stk)) it ->
  enc_at M' ov fb (PEC.ENC eb ek (stk ++ [it]) d').
Proof.
  intros EA Ho Ho' BB AGO AGB MG U32 U48 Hd' ROOM NEW. unfold PEC.enc_at in EA |- *. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EA |- *.
  destruct EA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & _ & Hk & Hlen & Hd & Hk0 & HB & HIT). pose proof (PEC.ecap_nonneg ek) as CN.
  rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. change (Z.pos 1) with 1.
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 32 -> L5C.agree_on M M' a n) by (intros a n X1 X2 i Hi; apply AGO; lia).
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [exact U32|].
  split; [apply (L5C.u64_at_agree segs M M'); [intros i Hi; apply AGO; lia|lia|lia| exact V40]|].
  split; [exact U48|]. split; [exact (L5.defined_grows M M' _ _ MG D)|]. split; [exact I|].
  split; [exact Hk|]. split; [lia|]. split; [exact Hd'|]. split; [exact Hk0|].
  assert (Hp : 0 < ek).
  { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in ROOM. rewrite Z0 in ROOM. cbn in ROOM. lia. }
  split.
  - intros _. destruct (HB Hp) as (AL & DB & BR & _ & _). split; [exact AL|]. split; [exact (L5.defined_grows M M' _ _ MG DB)|]. split; [exact BR|]. split; exact I.
  - intros i Hi. destruct (BB Hp) as (B0 & B1).
    destruct (Nat.lt_ge_cases i (length stk)) as [LT|GE].
    + rewrite app_nth1 by exact LT. pose proof (HIT i LT) as IT.
      apply (PECF.eitem_at_agree segs M M'); [| unfold PEC.ESZ in *; lia | unfold PEC.ESZ in *; lia | exact IT].
      intros j Hj. apply (AGB Hp); unfold PEC.ESZ in *; lia.
    + assert (EI_ : i = length stk) by lia. subst i. rewrite nth_middle. exact NEW.
Qed.

Lemma enc_grow (M M' : word -> option byte) ov fb eb ek stk d d' it B :
  enc_at M ov fb (PEC.ENC eb ek stk d) ->
  0 <= ov -> ov + 56 <= 2 ^ 64 ->
  (forall i, 0 <= i < 2 ^ 64 -> ov <= i < ov + 24 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  mem_grows M M' ->
  ek <= 11 ->
  L5.u64_at segs M' (ov + 24) B ->
  L5.u64_at segs M' (ov + 32) (B + PEC.ESZ * (Z.of_nat (length stk) + 1)) ->
  L5.u64_at segs M' (ov + 40) (B + PEC.ESZ * PEC.ecap (ek + 1)) ->
  L5.u32_at segs M' (ov + 48) d' -> 0 <= d' <= MAX_DEPTH + 1 ->
  Z.of_nat (length stk) + 1 <= PEC.ecap (ek + 1) ->
  B mod 8 = 0 -> L5.defined M' B (PEC.ESZ * PEC.ecap (ek + 1)) -> block_range L B (PEC.ESZ * PEC.ecap (ek + 1)) ->
  (forall i, (i < length stk)%nat -> PEC.eitem_at segs M' (B + PEC.ESZ * Z.of_nat i) (nth i stk (EI 0 0 0))) ->
  PEC.eitem_at segs M' (B + PEC.ESZ * Z.of_nat (length stk)) it ->
  enc_at M' ov fb (PEC.ENC B (ek + 1) (stk ++ [it]) d').
Proof.
  intros EA Ho Ho' AGO MG K10 U24 U32 U40 U48 Hd' ROOM AL DB BR OLD NEW. unfold PEC.enc_at in EA |- *. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EA |- *.
  destruct EA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & _ & Hk & Hlen & Hd & Hk0 & HB & HIT).
  rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. change (Z.pos 1) with 1.
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 24 -> L5C.agree_on M M' a n) by (intros a n X1 X2 i Hi; apply AGO; lia).
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [exact U24|]. split; [exact U32|]. split; [exact U40|]. split; [exact U48|].
  split; [exact (L5.defined_grows M M' _ _ MG D)|]. split; [exact I|].
  split; [lia|]. split; [lia|]. split; [exact Hd'|]. split; [intros X; lia|]. split.
  - intros _. split; [exact AL|]. split; [exact DB|]. split; [exact BR|]. split; exact I.
  - intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [LT|GE].
    + rewrite app_nth1 by exact LT. exact (OLD i LT).
    + assert (EI_ : i = length stk) by lia. subst i. rewrite nth_middle. exact NEW.
Qed.

End Kit.
End PEEK.
