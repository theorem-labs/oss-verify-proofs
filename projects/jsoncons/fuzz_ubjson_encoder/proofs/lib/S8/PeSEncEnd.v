(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmSpecs PeSpecsS PmStep PmKeep PmFrame PmParKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCStatics PeCSpecs PeCSpecsS PeCFrame PeCKitS PeCKeep PeSEncEndP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Es0_code_35818_3581c Es0_code_35f84_35f88.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PESENC.
Import PMS.
Abbreviation CAD := PeCLayoutS.CADDR_S.
Abbreviation EE := PeCLayoutS.EADDR_S.

#[local] Transparent e_end_value.

Definition ebump (r : list eitem) : list eitem :=
  match r with [] => [] | e :: r' => EI (ei_kind e) (ei_len e) ((ei_cnt e + 1) mod TWO64) :: r' end.
Lemma ebump_length r : length (ebump r) = length r.
Proof. destruct r; reflexivity. Qed.
Lemma eev_w_estk r s : e_end_value (w_estk r s) = w_estk (ebump r) s.
Proof. unfold e_end_value. cbn [s_estk w_estk]. destruct r as [|e r']; [destruct s; reflexivity| reflexivity]. Qed.

Lemma e_end_indef X e0 rr : s_estk X = e0 :: rr -> ei_indef e0 = true ->
  e_end X = ST (s_stk X) (s_pos X) (s_more X) (s_done X) (s_halt X) (s_depth X) (s_ec X) (ebump rr) (s_edepth X - 1) (s_lo X + 1) (s_hi X + 1) (s_bad X).
Proof. intros H1 H2. unfold e_end. rewrite H1, H2. cbv zeta. rewrite eev_w_estk. destruct X; reflexivity. Qed.
Lemma e_end_lt X e0 rr : s_estk X = e0 :: rr -> ei_indef e0 = false -> ei_cnt e0 < ei_len e0 ->
  e_end X = ST (s_stk X) (s_pos X) (s_more X) (s_done X) (s_halt X) (s_depth X) true (s_estk X) (s_edepth X - 1) (s_lo X) (s_hi X) (s_bad X).
Proof. intros H1 H2 H3. unfold e_end. rewrite H1, H2. cbv zeta. replace (ei_cnt e0 <? ei_len e0) with true by (symmetry; apply Z.ltb_lt; exact H3). destruct X; cbn in H1 |- *. subst. reflexivity. Qed.
Lemma e_end_gt X e0 rr : s_estk X = e0 :: rr -> ei_indef e0 = false -> ei_len e0 < ei_cnt e0 ->
  e_end X = ST (s_stk X) (s_pos X) (s_more X) (s_done X) (s_halt X) (s_depth X) true (s_estk X) (s_edepth X - 1) (s_lo X) (s_hi X) (s_bad X).
Proof.
  intros H1 H2 H3. unfold e_end. rewrite H1, H2. cbv zeta. replace (ei_cnt e0 <? ei_len e0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (ei_len e0 <? ei_cnt e0) with true by (symmetry; apply Z.ltb_lt; exact H3). destruct X; cbn in H1 |- *. subst. reflexivity.
Qed.
Lemma e_end_eq X e0 rr : s_estk X = e0 :: rr -> ei_indef e0 = false -> ei_cnt e0 = ei_len e0 ->
  e_end X = ST (s_stk X) (s_pos X) (s_more X) (s_done X) (s_halt X) (s_depth X) (s_ec X) (ebump rr) (s_edepth X - 1) (s_lo X) (s_hi X) (s_bad X).
Proof.
  intros H1 H2 H3. unfold e_end. rewrite H1, H2. cbv zeta. replace (ei_cnt e0 <? ei_len e0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (ei_len e0 <? ei_cnt e0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite eev_w_estk. destruct X; reflexivity.
Qed.
Lemma e_end_nil X : s_estk X = [] -> s_bad (e_end X) = true.
Proof. intros H. unfold e_end. rewrite H. reflexivity. Qed.

Lemma Forall_ebump rr : Forall ei_ok rr -> Forall ei_ok (ebump rr).
Proof. intros H. destruct rr as [|e r]; [constructor| exact (Forall_ei_bump e r H)]. Qed.

Lemma nth_top (rr : list eitem) e0 d : nth (length rr) (rev rr ++ [e0]) d = e0.
Proof. rewrite <- (length_rev rr). apply nth_middle. Qed.
Lemma nth_below (rr : list eitem) e0 d i : (i < length rr)%nat -> nth i (rev rr ++ [e0]) d = nth i (rev rr) d.
Proof. intros Hi. apply app_nth1. rewrite length_rev. exact Hi. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : PESK.sink_policy.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis PO : PESK.sink_policy_ok P.
Let KL := PECKS.klayout_S L LY.
Let SF := PECKS.sfoot_S L LY.
Abbreviation enc_at := (PEC.enc_at RSEGS EE L PMSP.T3 PMSP.T4).

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
  intros HH Hin FRZ Hc Hw FP. pose proof (PMK.kl_img RSEGS L KL) as KI. unfold hl_ceil in Hc.
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
  mem_grows M M' -> L5.u32_at RSEGS M' (ov + 48) d' -> 0 <= d' <= MAX_DEPTH + 1 ->
  enc_at M' ov fb (PEC.ENC eb ek stk d').
Proof.
  intros EA Ho Ho' BB AGO AGB MG U48 Hd'. unfold PEC.enc_at in EA |- *. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EA |- *.
  destruct EA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & _ & Hk & Hlen & Hd & Hk0 & HB & HIT). pose proof (PEC.ecap_nonneg ek) as CN.
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 48 -> L5C.agree_on M M' a n) by (intros a n X1 X2 i Hi; apply AGO; lia).
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V32]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V40]|].
  split; [exact U48|]. split; [exact (L5.defined_grows M M' _ _ MG D)|]. split; [exact I|].
  split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hd'|]. split; [exact Hk0|]. split.
  - intros Hp. destruct (HB Hp) as (AL & DB & BR & _ & _). split; [exact AL|]. split; [exact (L5.defined_grows M M' _ _ MG DB)|]. split; [exact BR|]. split; exact I.
  - intros i Hi. pose proof (HIT i Hi) as IT.
    assert (Hp : 0 < ek).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in Hlen. rewrite Z0 in Hlen. cbn in Hlen. lia. }
    destruct (BB Hp) as (B0 & B1).
    apply (PECF.eitem_at_agree RSEGS M M'); [| unfold PEC.ESZ in *; lia | unfold PEC.ESZ in *; lia | exact IT].
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
  L5.u64_at RSEGS M' (ov + 32) (eb + PEC.ESZ * Z.of_nat (length rr)) ->
  L5.u32_at RSEGS M' (ov + 48) d' -> 0 <= d' <= MAX_DEPTH + 1 ->
  (forall e2 rr', rr = e2 :: rr' -> L5.u64_at RSEGS M' (eb + PEC.ESZ * Z.of_nat (length rr') + 16) ((ei_cnt e2 + 1) mod TWO64)) ->
  enc_at M' ov fb (PEC.ENC eb ek (rev (ebump rr)) d').
Proof.
  intros EA Ho Ho' BB AGO AGB MG U32 U48 Hd' UCC. unfold PEC.enc_at in EA |- *. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EA |- *.
  destruct EA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & _ & Hk & Hlen & Hd & Hk0 & HB & HIT). pose proof (PEC.ecap_nonneg ek) as CN.
  rewrite length_app, length_rev in Hlen, HB, HIT. cbn [length] in Hlen, HB, HIT.
  assert (LEN' : length (rev (ebump rr)) = length rr) by (rewrite length_rev; apply ebump_length).
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 32 -> L5C.agree_on M M' a n) by (intros a n X1 X2 i Hi; apply AGO; lia).
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [rewrite LEN'; exact U32|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AGO; lia|lia|lia| exact V40]|].
  split; [exact U48|]. split; [exact (L5.defined_grows M M' _ _ MG D)|]. split; [exact I|].
  split; [exact Hk|]. split; [rewrite LEN'; lia|]. split; [exact Hd'|]. split; [exact Hk0|]. split.
  - intros Hp. destruct (HB Hp) as (AL & DB & BR & _ & _). split; [exact AL|]. split; [exact (L5.defined_grows M M' _ _ MG DB)|]. split; [exact BR|]. split; exact I.
  - rewrite LEN'. intros i Hi.
    assert (Hp : 0 < ek).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in Hlen. rewrite Z0 in Hlen. cbn in Hlen. lia. }
    destruct (BB Hp) as (B0 & B1).
    destruct rr as [|e2 rr']; [cbn in Hi; lia|]. cbn [ebump rev]. cbn [length] in Hi, Hlen, HB, HIT.
    assert (ORIG : forall j, (j <= length rr')%nat -> PEC.eitem_at RSEGS M (eb + PEC.ESZ * Z.of_nat j) (nth j (rev rr' ++ [e2]) (EI 0 0 0))).
    { intros j Hj. specialize (HIT j ltac:(lia)). cbn [rev] in HIT. rewrite (app_nth1 (rev rr' ++ [e2]) [e0]) in HIT; [exact HIT|].
      rewrite length_app, length_rev. cbn. lia. }
    destruct (Nat.lt_ge_cases i (length rr')) as [LT|GE].
    + rewrite app_nth1 by (rewrite length_rev; exact LT). specialize (ORIG i ltac:(lia)). rewrite app_nth1 in ORIG by (rewrite length_rev; exact LT).
      apply (PECF.eitem_at_agree RSEGS M M'); [| unfold PEC.ESZ in *; lia | unfold PEC.ESZ in *; lia | exact ORIG].
      intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [cc_rng]. unfold PEC.ESZ in *. lia.
    + assert (EI_ : i = length rr') by lia. subst i. rewrite nth_top. specialize (ORIG (length rr') ltac:(lia)). rewrite nth_top in ORIG.
      destruct ORIG as (K0c & K8c & _). split; [|split].
      * cbn [ei_kind]. apply (PMF.u32_at_agree RSEGS M M'); [| unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia| exact K0c].
        intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [cc_rng]. unfold PEC.ESZ in *. lia.
      * cbn [ei_len]. apply (L5C.u64_at_agree RSEGS M M'); [| unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia| exact K8c].
        intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [cc_rng]. unfold PEC.ESZ in *. lia.
      * cbn [ei_cnt]. exact (UCC e2 rr' eq_refl).
Qed.

Definition CSL : list nat := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Local Ltac insub := intros ? Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto.

Local Ltac post_of P := destruct P as (fxpq & Rpq & Mpq & HPpq); exists fxpq, Rpq, Mpq; decompose [and] HPpq; repeat (split; [assumption|]); assumption.
Local Ltac post_of_v P v := destruct P as (fxpq & Rpq & Mpq & HPpq); exists fxpq, Rpq, Mpq, v; decompose [and] HPpq; repeat (split; [first [assumption | (clear; Lia.lia)]|]); assumption.

Theorem v_end_arr_ok :
  PESK.push_back_spec RSEGS CAD EE L HI PMSP.T3 PMSP.T4 P -> PECSS.make_ec_spec L HI -> PECSS.v_end_arr_spec L HI P.
Proof.
  intros PB MKEC. unfold PECSS.v_end_arr_spec, PECS.v_end_arr_spec, PECS.eslot_spec.
  intros SPM [] fx R M model K LBX cr sp r fb cat p X s str sm en k e HH MOK K0 ENT FOK A10 A12 CPRE INCS POK MP NB HB CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame CAD PeCLayoutS.CADDR_S] in F2.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  unfold PECS.args_t2 in A12.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI).
  destruct MP as ((LOHI & XBAD & FA & EDR) & ED1).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl12 in A12.
  unfold PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_ec, PMSP.o_v, PESK.o_sink in *.
  cbn [pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S] in *.
  change (PMSP.pm_scr 4) with 20480 in *.
  assert (SC0 : 0 <= 20480) by lia.
  set (LB := PEC.owned s en k ++ LBX) in *.
  assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
  pose proof (L5C.stk_writable RSEGS _ M sp 20480 STK) as WR.
  assert (PINC : incl (PM.parser_own s) LB) by (unfold LB, PEC.owned; intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx).
  assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
  assert (EINC : incl (PEC.enc_own en) LB).
  { unfold LB, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. exact Hx. }
  assert (KINC : incl (PESK.sink_own k) LB).
  { unfold LB, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hx. }

  destruct en as [eb ek estk edepth].
  pose proof EA as (EV0 & EV8 & EV16 & EV24 & EV32 & EV40 & EV48 & EDEF & _ & EK & ELEN & EDEP & EKB & EBLK & EITEMS).
  cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EV24, EV32, EV40, EV48, EK, ELEN, EDEP, EKB, EBLK, EITEMS.

  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [PEC.en_stk PEC.en_depth] in Lestk, Ledepth.
  destruct (s_estk X) as [|e0 rr] eqn:HES; [exfalso; rewrite (e_end_nil X HES) in NB; discriminate|].
  cbn [rev] in Lestk.
  pose proof (Forall_inv FA) as E0OK. pose proof (Forall_inv_tail FA) as RROK. unfold ei_ok in E0OK.
  destruct e0 as [kd ln cn]. cbn [ei_kind ei_len ei_cnt] in E0OK.
  set (n := Z.of_nat (length rr)).
  assert (HLEN : Z.of_nat (length estk) = n + 1) by (rewrite Lestk, length_app, length_rev; cbn [length]; lia).
  assert (EKP : 0 < ek).
  { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in ELEN. rewrite Z0 in ELEN. cbn in ELEN. lia. }
  destruct (EBLK EKP) as (EBAL & EBDEF & EBR & _ & _).
  pose proof (PEC.ecap_nonneg ek) as CN.
  assert (BIN : In (eb, PEC.ESZ * PEC.ecap ek) LB).
  { apply EINC. unfold PEC.enc_own. cbn [PEC.en_k PEC.en_b]. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  destruct (BR _ _ BIN) as (B0 & B1 & B4). unfold hl_ceil in B4. unfold PEC.ESZ in B1, B4.

  pose proof (EITEMS (length rr) ltac:(rewrite Lestk, length_app, length_rev; cbn [length]; lia)) as ETOP.
  rewrite Lestk, nth_top in ETOP. destruct ETOP as (T0 & T8 & T16). cbn [ei_kind ei_len ei_cnt] in T0, T8, T16. unfold PEC.ESZ in T0, T8, T16.
  fold n in T0, T8, T16.
  assert (ALov : (fb + 440) mod 8 = 0) by (apply (m8_of16 fb); [exact F3| reflexivity]).
  assert (ALsk : (fb + 496) mod 8 = 0) by (apply (m8_of16 fb); [exact F3| reflexivity]).
  assert (ALec : (fb + 16) mod 8 = 0) by (apply (m8_of16 fb); [exact F3| reflexivity]).
  assert (ALend : (eb + 24 * (n + 1)) mod 8 = 0) by (apply al8_item; exact EBAL).
  assert (HO : bv_unsigned (getr R (PMK.reg 10)) = fb + 440) by (rewrite A10; apply L5.unsigned_lit; lia).
  assert (HEC : bv_unsigned (getr R (PMK.reg 12)) = fb + 16) by (rewrite A12; apply L5.unsigned_lit; lia).
  rewrite HLEN in EV32. unfold PEC.ESZ in EV32, EV40, EBDEF, ELEN.
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as RB1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as RB8.
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as RB9. change (bv_modulus 64) with (2 ^ 64) in RB1, RB8, RB9.
  unfold PMSP.cfg. cbn [pe_end_arr EE PeCLayoutS.EADDR_S].
  pose proof (ly_img_lo L LY) as IMLO. pose proof (ly_img_hi L LY) as IMHI.

  set (LBc0 := PM.parser_own s ++ LBX).
  assert (BRc0 : PMFR.brange L LBc0) by (apply (PMFR.brange_incl L LBc0 LB BR); unfold LBc0, LB, PEC.owned; intros x Hx; apply in_app_or in Hx;
     apply in_or_app; destruct Hx as [Hx|Hx]; [left; apply in_or_app; left; exact Hx| right; exact Hx]).
  assert (PINC0 : incl (PM.parser_own s) LBc0) by (unfold LBc0; apply incl_appl; apply incl_refl).
  assert (SINC0 : incl (PM.vs_own str) LBc0) by (unfold LBc0; apply incl_appr; exact INCS).
  set (WEC := fun a : Z => (fb + 440 <= a < fb + 520) \/ (fb + 16 <= a < fb + 16 + 16) \/ (0xc9640 <= a < 0xc9640 + 2) \/ (0xeb088 <= a < 0xeb088 + 544)).
  assert (KEEPF : forall W M', PMK.ek L LBc0 sp 20480 W M M' -> (forall a, PMK.inW W a -> WEC a) ->
            PM.parser_at RSEGS CAD PMSP.T3 PMSP.T4 M' (fb + 48) (fb + 520) s /\ PM.iss_at RSEGS CAD PMSP.T3 M' (fb + 520) str sm
            /\ L5.u64_at RSEGS M' (fb + 48 + 384) (fb + 440) /\ PMST.base_ok RSEGS CAD M' /\ PEC.content_ok RSEGS CAD M' fb p (PM.p_src s) str sm).
  { intros W M' EKW WC.
    assert (WHI : forall a, PMK.inW W a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WC in I; unfold WEC in I; rewrite IMLO, IMHI; clear - I F1; Lia.lia).
    assert (NW : forall i, ~ WEC i -> ~ PMK.inW W i) by (intros i Hi I; apply Hi; apply WC; exact I).
    split; [apply (PMFR.parser_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 BRc0 WHI); [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact PINC0| exact PA]|].
    split; [apply (PMFR.iss_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 BRc0 WHI); [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact SINC0| exact IA]|].
    split; [apply (PMFR.u64_keep RSEGS L KL LBc0 sp 20480 W M M' EKW STK SC0); [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact VREF]|].
    split; [apply (PMKP.base_ok_keep RSEGS CAD L KL SF LBc0 sp 20480 W M M' EKW); [| | | | exact BASE];
            intros a Ha; apply PMFR.outside_of_not_inW; apply NW; unfold WEC;
            cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock CAD PeCLayoutS.CADDR_S] in Ha; clear - Ha SLO STOP F1; lia|].
    apply (PECF.content_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 BRc0 WHI fb p s str sm (fb + 48));
      unfold PMSP.o_is; cbn [pa_off_is CAD PeCLayoutS.CADDR_S]; [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact SINC0| exact PINC0| exact IA| exact PA| exact CONT]. }

  set (WOB := fun a : Z => (fb + 440 <= a < fb + 520)).
  assert (KEEPE : forall W M', PMK.ek L LBc0 sp 20480 W M M' -> (forall a, PMK.inW W a -> WOB a) ->
            PEST.err_ok RSEGS CAD EE M' e /\ PEC.ec_state RSEGS CAD M' fb (s_ec X) cat).
  { intros W M' EKW WC.
    assert (NW : forall i, ~ WOB i -> ~ PMK.inW W i) by (intros i Hi I; apply Hi; apply WC; exact I).
    split; [apply (PECKP.err_ok_keep RSEGS CAD EE L KL SF LBc0 sp 20480 W M M' EKW); [| | exact ERR];
            intros a Ha; apply PMFR.outside_of_not_inW; apply NW; unfold WOB;
            cbn [pa_errcat_guard pa_atexit CAD PeCLayoutS.CADDR_S] in Ha; clear - Ha SLO STOP F1 IMLO IMHI; lia|].
    apply (PECF.ec_state_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 fb (s_ec X) cat);
      unfold PMSP.o_ec; cbn [pa_off_ec CAD PeCLayoutS.CADDR_S]; [lia|lia| intros i' Hi'; apply NW; unfold WOB; lia| exact ECS]. }

  assert (WCE : forall a, PMK.inW (PEC.W_enc CAD EE fb) a -> WEC a).
  { intros a (r0 & Hin & Hr). unfold PEC.W_enc, PMSP.err_W, PMSP.o_v, PMSP.o_ec, PESK.o_sink in Hin.
    cbn [pa_off_v pa_off_ec pe_off_sink pa_errcat_guard pa_atexit CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S app] in Hin.
    unfold L5.in_rng in Hr. unfold WEC. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; lia. }

  assert (KPM0 : 0 <= hl_k_per_malloc L) by (pose proof (ly_kpm L LY); lia).
  assert (BOV0 : 0 <= hl_b_overhead L) by (pose proof (ly_bov L LY); lia).
  assert (PEN : 0 <= fst (PEC.pot_estack L ek) /\ 0 <= snd (PEC.pot_estack L ek)).
  { clear - KPM0 BOV0 EK. unfold PEC.pot_estack, PEC.ESZ. cbn [fst snd]. assert (P2 : 2 ^ ek <= 2 ^ 12) by (apply Z.pow_le_mono_r; Lia.lia). split; Lia.nia. }
  assert (CREDk : PMSP.credit_le (PESK.sink_pot P (PESK.sk_c k)) cr).
  { unfold PMSP.credit_le, PEC.pot_enc, PEC.credit_add in CRED |- *. cbn [fst snd PEC.en_k] in CRED |- *. lia. }
  assert (ECAPB : PEC.ecap ek <= 2048).
  { clear - EK EKP. unfold PEC.ecap. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; Lia.lia). change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; Lia.lia. }
  rewrite HLEN in ELEN. unfold MAX_DEPTH, MAX_ITEMS, TWO64 in EDR, EDEP, E0OK.
  assert (WRov : L5.writable RSEGS M (fb + 440) 56) by (apply (L5C.writable_of_defined RSEGS); [exact EDEF|lia|lia]).
  pose proof SKA as (_ & _ & _ & _ & _ & KZ & KCAP & KC0 & KBLK).
  set (en := PEC.ENC eb ek estk edepth) in *.
  set (LBY := PM.parser_own s ++ PEC.enc_own en ++ LBX).
  assert (XINCY : incl LBc0 LBY) by (unfold LBc0, LBY; insub).
  assert (EINCY : incl (PEC.enc_own en) LBY) by (unfold LBY; insub).
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; insub).
  assert (PERM1 : Permutation LB (PESK.sink_own k ++ LBY)) by (unfold LB, LBY, PEC.owned; rewrite <- !app_assoc; apply perm4).
  subst estk.
  assert (KD4 : (kd = 1 \/ kd = 3) \/ (kd = 0 \/ kd = 2)) by lia.
  destruct KD4 as [KDI|KDC].
  -
    assert (EIND : ei_indef (EI kd ln cn) = true) by (unfold ei_indef; cbn [ei_kind]; destruct KDI as [-> | ->]; reflexivity).
    rewrite (e_end_indef X _ rr HES EIND) in NB, HB, KONT. cbn [s_bad s_hi] in NB, HB.

    assert (POSTI : exists fx1 R1 M1, mem_grows M M1
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ (msteps RSEGS (@mkst fx R (Z_to_bv 64 0x357c4) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x372d8) M1 (seg_rom RSEGS))
          /\ (forall x, In x PESENDP.KS_encEAI1 -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
          /\ getr R1 (PMK.reg 1) = Z_to_bv 64 219156
          /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 48)
          /\ getr R1 (PMK.reg 8) = getr R (PMK.reg 10)
          /\ getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 496)
          /\ getr R1 (PMK.reg 11) = Z_to_bv 64 (sp - 48)
          /\ L5.u32_at RSEGS M1 (fb + 440 + 48) (edepth - 1)
          /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))
          /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
          /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))))).
    { destruct KDI as [KD|KD]; subst kd.
      + pose proof (PESENDP.encEAI1_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                     | 39%nat => cn | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
        PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                               | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN; unfold hl_ceil in *; lia) ]).
        post_of P1.
      + pose proof (PESENDP.encEAI3_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                     | 39%nat => cn | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
        PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                               | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN; unfold hl_ceil in *; lia) ]).
        post_of P1. }
    PMK.pvz_hg ltac:(idtac; destruct POSTI as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG1 & FRZ1 & MS1 & KS1 & X1_1 & X2_1 & X8_1 & X10_1 & X11_1 & C48 & S24 & S16 & S8)); PMK.pvz_clrT.
    rewrite A10 in X8_1.
    set (P1 := fun a => (sp - 48 <= a < sp - 48 + 48) \/ (fb + 440 + 48 <= a < fb + 440 + 48 + 4)).
    assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ1; [exact Ha| |]; intros X'; apply N; unfold P1; [left| right]; exact X'. }
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x357c4 R1 0x372d8 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
    { intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P1 in Pa. clear - Pa SLO SHI F1 F2. Lia.lia. }
    { intros a. unfold P1. apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    set (W1 := [(fb + 440 + 48, 4)] : list L5.range).
    assert (WHI1 : forall a, PMK.inW W1 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
    assert (NW1 : forall i, ~ (fb + 440 + 48 <= i < fb + 440 + 52) -> ~ PMK.inW W1 i) by (intros i Hi I; apply PMFR.inW_inv1 in I; lia).
    assert (EK1 : PMK.ek L LB sp 20480 W1 M M1).
    { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W1 M M1 P1 FRZ1' STK (PMFR.brange_hi L LB BR)).
      intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
    assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by exact (PMK.stk_grows L M M1 sp 20480 MG1 STK).
    assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 48) 12288).
    { apply (PMK.stk_call L M1 sp 20480 (sp - 48) 12288 STK1); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    assert (SKA1 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M1 (fb + 496) k).
    { apply (PECF.sink_keep RSEGS L KL LB sp 20480 W1 M M1 EK1 STK SC0 BR WHI1); [lia|lia| intros i' Hi'; apply NW1; lia| exact KINC| exact SKA]. }
    assert (EA1 : enc_at M1 (fb + 440) fb (PEC.ENC eb ek (rev rr ++ [EI kd ln cn]) (edepth - 1))).
    { apply (enc_depth M M1 (fb + 440) fb eb ek _ edepth (edepth - 1) EA); [lia|lia| intros _; unfold PEC.ESZ; lia| | | exact MG1| exact C48| unfold MAX_DEPTH; lia].
      - intros i Hi Ri Ni. apply FRZ1'; [exact Hi|]. unfold P1. clear - Ri Ni F1. Lia.lia.
      - intros _ i Hi Ri. apply FRZ1'; [exact Hi|]. unfold P1, PEC.ESZ in *. clear - Ri B4 SLO F1 SHI STOP. lia. }

    pose proof PB as PBX. unfold PESK.push_back_spec in PBX. cbn [pe_push_back EE PeCLayoutS.EADDR_S] in PBX.
    apply (PBX SPM fx1 R1 M1 model K LBY cr (fb + 496) (sp - 48) (sp - 48) 219156 k); clear PBX.
    { apply (heap_perm LB); [exact PERM1| exact HH1]. }
    { exact MOK. }
    { exact K0. }
    { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1_1|]. split; [clear; unfold L5.ra_ok; Lia.lia|]. split; [exact X2_1|].
      split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
    { rewrite L5K.rl10. exact X10_1. }
    { rewrite L5K.rl11. exact X11_1. }
    { exact SKA1. }
    { lia. } { lia. } { exact ALsk. } { lia. } { lia. } { left; lia. }
    { destruct STK1 as (_ & _ & _ & _ & D1). apply (L5.defined_sub M1 (sp - 20480) 20480 (sp - 48) 1 D1); lia. }
    { intros ZC. apply (PESK.spo_next P PO (PESK.sk_c k) (s_hi X + 1) KCAP); [intros Hc; exact (proj1 (proj2 (proj2 (proj2 (proj2 (KBLK Hc))))))| exact HB| lia]. }
    { exact CREDk. }
    intros fx2 R2 M2 model2 cr2 b2 RP2 SKA2 HP2 CK2 MB2 HH2.
    change (PMSP.pm_scr 0) with 12288 in HP2.
    set (k2 := PESK.sk_push k b2) in *.
    pose proof (bv_unsigned_in_range 64 (getr R2 (PMK.reg 10))) as RBj. change (bv_modulus 64) with (2 ^ 64) in RBj.
    pose proof (PMFR.model_ok_but_vm model model2 MOK MB2) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & Mm2).
    assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by (apply (PMK.stk_after RSEGS L KL LBY M1 M2 sp 20480 (sp - 48) 12288 _ STK1 HP2); lia).
    pose proof (L5C.stk_writable RSEGS _ M2 sp 20480 STK2) as WR2.
    pose proof (PMK.ek_of_hpres L LBY (sp - 48) 12288 [(fb + 496, 24)] M1 M2 HP2) as EK2.
    assert (BRY2 : PMFR.brange L (PESK.sink_own k2 ++ LBY)) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr2 M2 _ HH2); apply incl_refl).
    assert (BRY : PMFR.brange L LBY) by (apply (PMFR.brange_incl L LBY _ BRY2); apply incl_appr; apply incl_refl).
    assert (WHI2 : forall a, PMK.inW [(fb + 496, 24)] a -> sp - 48 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
    assert (SC2 : 0 <= 12288) by lia.
    assert (EA2 : enc_at M2 (fb + 440) fb (PEC.ENC eb ek (rev rr ++ [EI kd ln cn]) (edepth - 1))).
    { apply (PECF.enc_keep RSEGS EE L KL LBY (sp - 48) 12288 [(fb + 496, 24)] M1 M2 EK2 STKc SC2 BRY WHI2); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact EINCY| exact EA1]. }
    assert (S24b : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))).
    { apply (PMFR.u64_keep RSEGS L KL LBY (sp - 48) 12288 _ M1 M2 EK2 STKc SC2); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S24]. }
    assert (S16b : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))).
    { apply (PMFR.u64_keep RSEGS L KL LBY (sp - 48) 12288 _ M1 M2 EK2 STKc SC2); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S16]. }
    assert (S8b : L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))).
    { apply (PMFR.u64_keep RSEGS L KL LBY (sp - 48) 12288 _ M1 M2 EK2 STKc SC2); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S8]. }
    pose proof EA2 as (_ & _ & _ & EV24b & EV32b & _ & EV48b & EDEFb & _ & _ & _ & _ & _ & EBLKb & EITEMSb).
    cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EV24b, EV32b, EV48b, EBLKb, EITEMSb. unfold PEC.ESZ in EV32b. rewrite HLEN in EV32b.
    assert (WRov2 : L5.writable RSEGS M2 (fb + 440) 56) by (apply (L5C.writable_of_defined RSEGS); [exact EDEFb|lia|lia]).
    destruct (EBLKb EKP) as (_ & EBDEFb & _ & _ & _). unfold PEC.ESZ in EBDEFb.
    assert (WRblk2 : L5.writable RSEGS M2 eb (24 * PEC.ecap ek)) by (apply (L5C.writable_of_defined RSEGS); [exact EBDEFb|lia|lia]).

    assert (POSTJ : exists fx3 R3 M3, mem_grows M2 M3
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) -> ~ cc_rng eb rr i -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i))
      /\ (msteps RSEGS (@mkst fx2 R2 (Z_to_bv 64 0x35814) M2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0x35870) M3 (seg_rom RSEGS))
      /\ (forall x, In x CSL -> getr R3 (PMK.reg x) = getr R2 (PMK.reg x))
      /\ getr R3 (PMK.reg 1) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 1)))
      /\ getr R3 (PMK.reg 2) = Z_to_bv 64 sp
      /\ getr R3 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8)))
      /\ getr R3 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9)))
      /\ L5.u64_at RSEGS M3 (fb + 440 + 32) (eb + 24 * n)
      /\ (forall e2 rr', rr = e2 :: rr' -> L5.u64_at RSEGS M3 (eb + PEC.ESZ * Z.of_nat (length rr') + 16) ((ei_cnt e2 + 1) mod TWO64)))).
    { destruct rr as [|e2 rr'].
      -
        unfold n in *. cbn [length] in T0, T8, T16, HLEN, ELEN, EV32, EV32b, ALend |- *. change (Z.of_nat 0) with 0 in *.
        pose proof (PESENDP.encEAJ1_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb
            | 44%nat => bv_unsigned (getr R (PMK.reg 1)) | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
            | 55%nat => bv_unsigned (getr R2 (PMK.reg 10)) | _ => 0 end)) as P3. cbn beta iota in P3.
        PMK.feed P3 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact EBAL]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN; unfold hl_ceil in *; lia) ]).
        assert (POST1 : exists fx3 R3 M3, mem_grows M2 M3
          /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i))
          /\ (msteps RSEGS (@mkst fx2 R2 (Z_to_bv 64 0x35814) M2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0x35870) M3 (seg_rom RSEGS))
          /\ (forall x, In x PESENDP.KS_encEAJ1 -> getr R3 (PMK.reg x) = getr R2 (PMK.reg x))
          /\ getr R3 (PMK.reg 1) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 1)))
          /\ getr R3 (PMK.reg 2) = Z_to_bv 64 sp
          /\ getr R3 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8)))
          /\ getr R3 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9)))
          /\ L5.u64_at RSEGS M3 (fb + 440 + 32) eb)) by post_of P3.
        destruct POST1 as (fx3 & R3 & M3 & MG & FRZ & MS & KS & Y1 & Y2 & Y8 & Y9 & C32).
        exists fx3, R3, M3. split; [exact MG|]. split; [intros i Hi N1 _; apply FRZ; [exact Hi| exact N1]|]. split; [exact MS|].
        split; [intros x Hx; apply KS; exact (sub_in PESENDP.KS_encEAJ1 CSL ltac:(vm_compute; reflexivity) x Hx)|].
        split; [exact Y1|]. split; [exact Y2|]. split; [exact Y8|]. split; [exact Y9|]. split; [| intros e2 rr' H'; discriminate H'].
        replace (eb + 24 * 0) with eb by (clear; Lia.lia). exact C32.
      -
        set (m := Z.of_nat (length rr')) in *.
        assert (HNM : n = m + 1) by (unfold n, m; cbn [length]; rewrite Nat2Z.inj_succ; lia).
        assert (WRtop2 : L5.writable RSEGS M2 (eb + 24 * (n + 1) - 48) 48) by (apply (L5.writable_sub _ M2 eb (24 * PEC.ecap ek) _ _ WRblk2); lia).
        pose proof (EITEMSb (length rr') ltac:(rewrite length_app, length_rev; cbn [length]; lia)) as E2.
        cbn [rev] in E2. rewrite (app_nth1 (rev rr' ++ [e2]) [EI kd ln cn]) in E2 by (rewrite length_app, length_rev; cbn [length]; lia).
        rewrite nth_top in E2. destruct E2 as (_ & _ & U16). unfold PEC.ESZ in U16. fold m in U16.
        destruct e2 as [k2_ l2 c2]. cbn [ei_kind ei_len ei_cnt] in U16 |- *.
        pose proof (Forall_inv RROK) as E2OK. unfold ei_ok in E2OK. cbn [ei_kind ei_len ei_cnt] in E2OK. unfold MAX_ITEMS, TWO64 in E2OK.
        replace (eb + 24 * m + 16) with (eb + 24 * (n + 1) - 32) in U16 by lia.
        assert (POST2 : exists fx3 R3 M3, mem_grows M2 M3
          /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) -> ~ (eb + 24 * (n + 1) - 32 <= i < eb + 24 * (n + 1) - 32 + 8) -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i))
          /\ (msteps RSEGS (@mkst fx2 R2 (Z_to_bv 64 0x35814) M2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0x35870) M3 (seg_rom RSEGS))
          /\ (forall x, In x PESENDP.KS_encEAJ2 -> getr R3 (PMK.reg x) = getr R2 (PMK.reg x))
          /\ getr R3 (PMK.reg 1) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 1)))
          /\ getr R3 (PMK.reg 2) = Z_to_bv 64 sp
          /\ getr R3 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8)))
          /\ getr R3 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9)))
          /\ L5.u64_at RSEGS M3 (eb + 24 * (n + 1) - 32) ((c2 + 1) mod TWO64)
          /\ L5.u64_at RSEGS M3 (fb + 440 + 32) (eb + 24 * (n + 1) - 24))).
        { destruct (Z.eq_dec c2 18446744073709551615) as [CW|CNW].
          + rewrite CW in U16 |- *. change ((18446744073709551615 + 1) mod TWO64) with 0.
            pose proof (PESENDP.encEAJ2w_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 34%nat => eb + 24 * (n + 1)
                | 44%nat => bv_unsigned (getr R (PMK.reg 1)) | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
                | 55%nat => bv_unsigned (getr R2 (PMK.reg 10)) | _ => 0 end)) as P3. cbn beta iota in P3.
            PMK.feed P3 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact EBAL | exact ALend]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                                   | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN HNM; unfold hl_ceil in *; lia) ]).
            post_of P3.
          + pose proof (PESENDP.encEAJ2_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 42%nat => c2
                | 44%nat => bv_unsigned (getr R (PMK.reg 1)) | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
                | 55%nat => bv_unsigned (getr R2 (PMK.reg 10)) | _ => 0 end)) as P3. cbn beta iota in P3.
            PMK.feed P3 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact EBAL | exact ALend]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                                   | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN HNM E2OK CNW; unfold hl_ceil in *; lia) ]).
            rewrite Z.mod_small by (unfold TWO64; lia). post_of P3. }
        destruct POST2 as (fx3 & R3 & M3 & MG & FRZ & MS & KS & Y1 & Y2 & Y8 & Y9 & CCc & C32).
        exists fx3, R3, M3. split; [exact MG|]. split.
        { intros i Hi N1 N2. apply FRZ; [exact Hi| exact N1|]. cbn [cc_rng] in N2. unfold PEC.ESZ in N2. fold m in N2. intros X'. apply N2. lia. }
        split; [exact MS|]. split; [intros x Hx; apply KS; exact (sub_in PESENDP.KS_encEAJ2 CSL ltac:(vm_compute; reflexivity) x Hx)|].
        split; [exact Y1|]. split; [exact Y2|]. split; [exact Y8|]. split; [exact Y9|]. split; [replace (eb + 24 * n) with (eb + 24 * (n + 1) - 24) by lia; exact C32|].
        intros e2 rr'' H'. injection H' as <- <-. cbn [ei_cnt]. unfold PEC.ESZ. fold m. replace (eb + 24 * m + 16) with (eb + 24 * (n + 1) - 32) by lia. exact CCc. }
    PMK.pvz_hg ltac:(idtac; destruct POSTJ as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG3 & FRZ3 & MS3 & KS3 & Y1 & Y2 & Y8 & Y9 & C32c & CC3)); PMK.pvz_clrT.
    set (P3 := fun a => (fb + 440 + 32 <= a < fb + 440 + 32 + 8) \/ cc_rng eb rr a).
    assert (FRZ3' : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ3; [exact Ha| |]; intros X'; apply N; unfold P3; [left| right]; exact X'. }
    assert (CCB : forall a, cc_rng eb rr a -> eb <= a < eb + 24 * n) by (intros a Ha; apply cc_rng_in in Ha; unfold PEC.ESZ in Ha; unfold n; clear - Ha; Lia.lia).
    assert (INeo : In (eb, PEC.ESZ * PEC.ecap ek) (PEC.enc_own en)).
    { unfold PEC.enc_own, en. cbn [PEC.en_k PEC.en_b]. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
    assert (BIN2 : In (eb, PEC.ESZ * PEC.ecap ek) (PESK.sink_own k2 ++ LBY)) by (apply in_or_app; right; apply EINCY; exact INeo).
    apply (PMK.spiece RSEGS L HI KL HIok (PESK.sink_own k2 ++ LBY) cr2 M2 model2 fx2 fx3 R2 0x35814 R3 0x35870 M3 P3 K HH2 Mh2 Ml2 ltac:(lia) MS3 MG3 FRZ3').
    { intros a [Pa|Pa]; [apply (PMK.cwr_stack L _ M2 sp 20480 a STK2); clear - Pa SLO SHI F1 F2; Lia.lia|].
      apply (PMK.cwr_block L _ eb (PEC.ESZ * PEC.ecap ek) a BIN2). apply CCB in Pa. unfold PEC.ESZ. clear - Pa ELEN CN. Lia.lia. }
    { intros a. unfold P3. apply PMK.or_dec; [apply PMK.rng_dec| apply cc_rng_dec]. }
    intros HH3.

    set (W3 := [(fb + 440 + 32, 8)] : list L5.range).
    set (LBc3 := PESK.sink_own k2 ++ PM.parser_own s ++ LBX).
    assert (PERM3 : Permutation (PESK.sink_own k2 ++ LBY) (PEC.enc_own en ++ LBc3)) by (unfold LBY, LBc3; apply perm4).
    pose proof (heap_perm _ _ cr2 M3 _ PERM3 HH3) as HH3e.
    assert (BR3 : PMFR.brange L LBc3) by (apply (PMFR.brange_of_heap L HI HIok _ LBc3 cr2 M3 _ HH3e); apply incl_appr; apply incl_refl).
    assert (EK3 : PMK.ek L LBc3 sp 20480 W3 M2 M3).
    { apply (PMK.ek_piece L LBc3 sp 20480 W3 M2 M3 P3 FRZ3'). intros a Ha CA NE OW [Pa|Pa].
      - apply (OW (fb + 440 + 32, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      - refine (own_not_client (PEC.enc_own en) LBc3 cr2 M3 _ eb (PEC.ESZ * PEC.ecap ek) a sp 20480 HH3e INeo _ CA).
        apply CCB in Pa. unfold PEC.ESZ. clear - Pa ELEN CN. Lia.lia. }
    assert (WHI3 : forall a, PMK.inW W3 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
    assert (STK3 : L5C.stk (hl_sptop L) M3 sp 20480) by exact (PMK.stk_grows L M2 M3 sp 20480 MG3 STK2).

    eapply (L5.cps_of_msteps RSEGS); [exact Mh2| exact Ml2| |].
    { apply (PMK.ret_to RSEGS fx3 R3 M3 0x35870 W_35818 r F_35818 eq_refl D_35818); [rewrite Y1, PMPK.word_id; exact Rra| lia| exact Hr2]. }

    set (Ws := [(fb + 440, 56); (fb + 496, 24)] : list L5.range).
    assert (INC03 : incl LBc0 LBc3) by (unfold LBc0, LBc3; insub).
    assert (EKT : PMK.ek L LBc0 sp 20480 Ws M M3).
    { apply (PMK.ek_trans L LBc0 sp 20480 Ws M M1 M3).
      { apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 Ws W1 M M1 EK1); [exact INC0| intros x Hx; exact Hx|].
        intros a O r0 Hr0 Hin. unfold W1 in Hr0. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
        apply (O (fb + 440, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
      apply (PMK.ek_trans L LBc0 sp 20480 Ws M1 M2 M3).
      { apply (PMK.ek_callee_in' RSEGS L KL LBc0 LBY sp 20480 (sp - 48) 12288 Ws [(fb + 496, 24)] M1 M2 HP2 XINCY);
          [lia|lia| unfold hl_ceil; lia| lia| exact (PMFR.brange_hi L LBc0 BRc0)|].
        intros a I. apply PMFR.inW_inv1 in I. right. apply PMK.inW_next. apply PMK.inW_here. lia. }
      apply (PMK.ek_weaken L LBc0 LBc3 sp 20480 sp 20480 Ws W3 M2 M3 EK3); [exact INC03| intros x Hx; exact Hx|].
      intros a O r0 Hr0 Hin. unfold W3 in Hr0. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      apply (O (fb + 440, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    destruct (KEEPF Ws M3 EKT) as (PA3 & IA3 & VREF3 & BASE3 & CONT3).
    { intros a (r0 & Hin & Hr). unfold Ws in Hin. unfold L5.in_rng in Hr. unfold WEC. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
    destruct (KEEPE Ws M3 EKT) as (ERR3 & ECS3).
    { intros a (r0 & Hin & Hr). unfold Ws in Hin. unfold L5.in_rng in Hr. unfold WOB. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
    assert (SKA3 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M3 (fb + 496) k2).
    { apply (PECF.sink_keep RSEGS L KL LBc3 sp 20480 W3 M2 M3 EK3 STK2 SC0 BR3 WHI3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| unfold LBc3; insub| exact SKA2]. }
    assert (U48c : L5.u32_at RSEGS M3 (fb + 440 + 48) (edepth - 1)).
    { apply (PMF.u32_at_agree RSEGS M2 M3); [|lia|lia| exact EV48b]. intros i Hi. apply FRZ3'; [lia|]. unfold P3. intros [X'|X']; [lia|]. apply CCB in X'.
      clear - X' Hi B4 ELEN CN SLO F1. Lia.lia. }
    assert (EA3 : enc_at M3 (fb + 440) fb (PEC.ENC eb ek (rev (ebump rr)) (edepth - 1))).
    { apply (enc_pop M2 M3 (fb + 440) fb eb ek rr (EI kd ln cn) (edepth - 1) (edepth - 1) EA2); [lia|lia| intros _; unfold PEC.ESZ; lia| | | exact MG3| | exact U48c| unfold MAX_DEPTH; lia| exact CC3].
      - intros i Hi Ri N1 N2. apply FRZ3'; [exact Hi|]. unfold P3. intros [X'|X']; [clear - X' N1; Lia.lia|]. apply CCB in X'. clear - X' Ri B4 ELEN CN SLO F1. Lia.lia.
      - intros _ i Hi Ri Ni. apply FRZ3'; [exact Hi|]. unfold P3. intros [X'|X']; [| exact (Ni X')]. unfold PEC.ESZ in Ri. clear - X' Ri B4 CN SLO F1. Lia.lia.
      - unfold PEC.ESZ. exact C32c. }
    apply (KONT fx3 R3 M3 model2 (PEC.ENC eb ek (rev (ebump rr)) (edepth - 1)) k2 e cr2).
    + apply PMK.preserved_by_index. intros k0 Hk0.
      destruct (Nat.eq_dec k0 2) as [->|N2]; [rewrite Y2; symmetry; exact Rsp|].
      destruct (Nat.eq_dec k0 8) as [->|N8]; [rewrite Y8; apply PMPK.word_id|].
      destruct (Nat.eq_dec k0 9) as [->|N9]; [rewrite Y9; apply PMPK.word_id|].
      assert (IN3 : In k0 CSL /\ In k0 PESENDP.KS_encEAI1) by (cbn in Hk0; decompose [or] Hk0; subst; try (exfalso; congruence); (split; PMK.inl)).
      destruct IN3 as [I3 I1]. rewrite (KS3 k0 I3), (PMK.cs_of_preserved R1 R2 k0 RP2 Hk0), (KS1 k0 I1). reflexivity.
    + unfold PEC.crun_pre. unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PESK.o_sink. cbn [pa_off_p pa_off_is pa_off_v pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S].
      split; [exact PA3|]. split; [exact IA3|]. split; [exact EA3|]. split; [exact VREF3|]. split; [exact SKA3|].
      split; [exact BASE3|]. split; [exact ERR3|]. split; [exact TBOK|]. split; [exact CONT3|].
      split.
      { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PEC.en_stk PEC.en_depth].
        split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
        split; [reflexivity|]. split; [lia|]. split; [|exact Lbad].
        unfold k2, PESK.sk_push. destruct (PESK.sk_z k <? PESK.sk_c k); cbn [PESK.sk_z]; lia. }
      split; [exact ECS3| exact ECI].
    + intros X'; exact X'.
    + apply (PMK.hpres_of L LBc0 sp 20480 _ M M3).
      * apply (PMK.ek_weaken L LBc0 LBc0 sp 20480 sp 20480 _ Ws M M3 EKT); [apply incl_refl| intros x Hx; exact Hx|].
        intros a O r0 Hr0 Hin. unfold PEC.W_enc, PMSP.o_v, PMSP.o_ec, PESK.o_sink in O.
        cbn [pa_off_v pa_off_ec pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S app] in O.
        unfold Ws in Hr0. destruct Hr0 as [<-|[<-|[]]]; [apply (O (fb + 440, 56)); [left; reflexivity| exact Hin] | apply (O (fb + 496, 24)); [right; left; reflexivity| exact Hin]].
      * destruct STK3 as (_ & _ & _ & _ & D3). exact D3.
      * apply (PMK.dk_trans L LBc0 sp 20480 M M1 M3 (PMK.dk_grows L LBc0 sp 20480 M M1 MG1)).
        apply (PMK.dk_trans L LBc0 sp 20480 M1 M2 M3); [| apply (PMK.dk_grows L LBc0 sp 20480 M2 M3 MG3)].
        apply (PMK.dk_callee L LBc0 LBY sp 20480 (sp - 48) 12288 _ M1 M2 HP2 XINCY); lia.
    + unfold PMSP.credit_keep, PEC.pot_enc, PEC.credit_add in CK2 |- *. change (PEC.en_k en) with ek. cbn [fst snd PEC.en_k] in CK2 |- *. clear - CK2. Lia.lia.
    + exact MB2.
    + refine (heap_perm _ _ cr2 M3 _ _ HH3). change (PEC.enc_own (PEC.ENC eb ek (rev (ebump rr)) (edepth - 1))) with (PEC.enc_own en).
      unfold PEC.owned, LBY. rewrite <- !app_assoc. apply Permutation_sym. apply perm4.
  -
    assert (EIND : ei_indef (EI kd ln cn) = false) by (unfold ei_indef; cbn [ei_kind]; destruct KDC as [-> | ->]; reflexivity).
    destruct (Z.eq_dec cn ln) as [CEQ|CNE].
    +
      rewrite (e_end_eq X _ rr HES EIND CEQ) in NB, HB, KONT. cbn [s_bad s_hi] in NB, HB. subst cn.
      assert (WRblk : L5.writable RSEGS M eb (24 * PEC.ecap ek)) by (apply (L5C.writable_of_defined RSEGS); [exact EBDEF|lia|lia]).
      assert (POSTE : exists fx1 R1 M1, mem_grows M M1
        /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) ->
              ~ cc_rng eb rr i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
        /\ (msteps RSEGS (@mkst fx R (Z_to_bv 64 0x357c4) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x35870) M1 (seg_rom RSEGS))
        /\ (forall x, In x PESENDP.KS_encEACe10 -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
        /\ L5.u64_at RSEGS M1 (fb + 440 + 32) (eb + 24 * n)
        /\ L5.u32_at RSEGS M1 (fb + 440 + 48) (edepth - 1)
        /\ (forall e2 rr', rr = e2 :: rr' -> L5.u64_at RSEGS M1 (eb + PEC.ESZ * Z.of_nat (length rr') + 16) ((ei_cnt e2 + 1) mod TWO64)))).
      { destruct rr as [|e2 rr'].
        -
          unfold n in *. cbn [length] in T0, T8, T16, HLEN, ELEN, EV32, ALend |- *. change (Z.of_nat 0) with 0 in *.
          assert (POST1 : exists fx1 R1 M1, mem_grows M M1
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) ->
                  M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
            /\ (msteps RSEGS (@mkst fx R (Z_to_bv 64 0x357c4) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x35870) M1 (seg_rom RSEGS))
            /\ (forall x, In x PESENDP.KS_encEACe10 -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
            /\ L5.u64_at RSEGS M1 (fb + 440 + 32) eb /\ L5.u32_at RSEGS M1 (fb + 440 + 48) (edepth - 1))).
          { destruct KDC as [KD|KD]; subst kd.
            + pose proof (PESENDP.encEACe10_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 36%nat => edepth | 38%nat => ln | 41%nat => fb + 496 | _ => 0 end)) as P1.
              cbn beta iota in P1. rewrite !HO in P1.
              PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL]) | PMK.sc
                                     | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN; unfold hl_ceil in *; lia) ]).
              post_of P1.
            + pose proof (PESENDP.encEACe12_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 36%nat => edepth | 38%nat => ln | 41%nat => fb + 496 | _ => 0 end)) as P1.
              cbn beta iota in P1. rewrite !HO in P1.
              PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL]) | PMK.sc
                                     | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN; unfold hl_ceil in *; lia) ]).
              post_of P1. }
          destruct POST1 as (fx1 & R1 & M1 & MG & FRZ & MS & KS & C32 & C48).
          exists fx1, R1, M1. split; [exact MG|]. split; [intros i Hi N1 N2 N3 _; exact (FRZ i Hi N1 N2 N3)|]. split; [exact MS|]. split; [exact KS|].
          split; [replace (eb + 24 * 0) with eb by (clear; Lia.lia); exact C32|]. split; [exact C48| intros e2 rr' H'; discriminate H'].
        -
          set (m := Z.of_nat (length rr')) in *.
          assert (HNM : n = m + 1) by (unfold n, m; cbn [length]; rewrite Nat2Z.inj_succ; lia).
          assert (WRtop : L5.writable RSEGS M (eb + 24 * (n + 1) - 48) 48) by (apply (L5.writable_sub _ M eb (24 * PEC.ecap ek) _ _ WRblk); lia).
          pose proof (EITEMS (length rr') ltac:(rewrite length_app, length_rev; cbn [length]; lia)) as E2.
          cbn [rev] in E2. rewrite (app_nth1 (rev rr' ++ [e2]) [EI kd ln ln]) in E2 by (rewrite length_app, length_rev; cbn [length]; lia).
          rewrite nth_top in E2. destruct E2 as (_ & _ & U16). unfold PEC.ESZ in U16. fold m in U16.
          destruct e2 as [k2_ l2 c2]. cbn [ei_kind ei_len ei_cnt] in U16 |- *.
          pose proof (Forall_inv RROK) as E2OK. unfold ei_ok in E2OK. cbn [ei_kind ei_len ei_cnt] in E2OK. unfold MAX_ITEMS, TWO64 in E2OK.
          replace (eb + 24 * m + 16) with (eb + 24 * (n + 1) - 32) in U16 by lia.
          assert (POST2 : exists fx1 R1 M1, mem_grows M M1
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) ->
                  ~ (eb + 24 * (n + 1) - 32 <= i < eb + 24 * (n + 1) - 32 + 8) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
            /\ (msteps RSEGS (@mkst fx R (Z_to_bv 64 0x357c4) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x35870) M1 (seg_rom RSEGS))
            /\ (forall x, In x PESENDP.KS_encEACe10 -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
            /\ L5.u64_at RSEGS M1 (eb + 24 * (n + 1) - 32) ((c2 + 1) mod TWO64)
            /\ L5.u64_at RSEGS M1 (fb + 440 + 32) (eb + 24 * (n + 1) - 24)
            /\ L5.u32_at RSEGS M1 (fb + 440 + 48) (edepth - 1))).
          { destruct (Z.eq_dec c2 18446744073709551615) as [CW|CNW].
            + rewrite CW in U16 |- *. change ((18446744073709551615 + 1) mod TWO64) with 0.
              destruct KDC as [KD|KD]; subst kd.
              * pose proof (PESENDP.encEACe20w_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                    | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
                PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                       | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN HNM; unfold hl_ceil in *; lia) ]).
                post_of P1.
              * pose proof (PESENDP.encEACe22w_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                    | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
                PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                       | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN HNM; unfold hl_ceil in *; lia) ]).
                post_of P1.
            + destruct KDC as [KD|KD]; subst kd.
              * pose proof (PESENDP.encEACe20_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                    | 41%nat => fb + 496 | 42%nat => c2 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
                PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                       | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN HNM E2OK CNW; unfold hl_ceil in *; lia) ]).
                rewrite Z.mod_small by (unfold TWO64; lia). post_of P1.
              * pose proof (PESENDP.encEACe22_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                    | 41%nat => fb + 496 | 42%nat => c2 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
                PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                       | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN HNM E2OK CNW; unfold hl_ceil in *; lia) ]).
                rewrite Z.mod_small by (unfold TWO64; lia). post_of P1. }
          destruct POST2 as (fx1 & R1 & M1 & MG & FRZ & MS & KS & CCc & C32 & C48).
          exists fx1, R1, M1. split; [exact MG|]. split.
          { intros i Hi N1 N2 N3 N4. apply FRZ; [exact Hi| exact N1| exact N2| exact N3|]. cbn [cc_rng] in N4. unfold PEC.ESZ in N4. fold m in N4. intros X'. apply N4. lia. }
          split; [exact MS|]. split; [exact KS|]. split; [replace (eb + 24 * n) with (eb + 24 * (n + 1) - 24) by lia; exact C32|]. split; [exact C48|].
          intros e2 rr'' H'. injection H' as <- <-. cbn [ei_cnt]. unfold PEC.ESZ. fold m. replace (eb + 24 * m + 16) with (eb + 24 * (n + 1) - 32) by lia. exact CCc. }
      PMK.pvz_hg ltac:(idtac; destruct POSTE as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                       destruct pvzP as (MG1 & FRZ1 & MS1 & KS1 & C32c & C48c & CC1)); PMK.pvz_clrT.
      set (P1 := fun a => (sp - 48 <= a < sp - 48 + 48) \/ (fb + 440 + 48 <= a < fb + 440 + 48 + 4) \/ (fb + 440 + 32 <= a < fb + 440 + 32 + 8) \/ cc_rng eb rr a).
      assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha N. apply FRZ1; [exact Ha| | | |]; intros X'; apply N; unfold P1; [left| right; left| right; right; left| right; right; right]; exact X'. }
      assert (CCB : forall a, cc_rng eb rr a -> eb <= a < eb + 24 * n) by (intros a Ha; apply cc_rng_in in Ha; unfold PEC.ESZ in Ha; unfold n; clear - Ha; Lia.lia).
      assert (INeo : In (eb, PEC.ESZ * PEC.ecap ek) (PEC.enc_own en)).
      { unfold PEC.enc_own, en. cbn [PEC.en_k PEC.en_b]. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x357c4 R1 0x35870 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
      { intros a [Pa|[Pa|[Pa|Pa]]]; [apply (PMK.cwr_stack L LB M sp 20480 a STK); clear - Pa SLO SHI F1 F2; Lia.lia
          | apply (PMK.cwr_stack L LB M sp 20480 a STK); clear - Pa SLO SHI F1 F2; Lia.lia | apply (PMK.cwr_stack L LB M sp 20480 a STK); clear - Pa SLO SHI F1 F2; Lia.lia |].
        apply (PMK.cwr_block L _ eb (PEC.ESZ * PEC.ecap ek) a BIN). apply CCB in Pa. unfold PEC.ESZ. clear - Pa ELEN CN. Lia.lia. }
      { intros a. unfold P1. repeat (apply PMK.or_dec; [apply PMK.rng_dec|]). apply cc_rng_dec. }
      intros HH1.
      set (WsE := [(fb + 440, 56)] : list L5.range).
      set (LBcE := PESK.sink_own k ++ PM.parser_own s ++ LBX).
      assert (PERME : Permutation LB (PEC.enc_own en ++ LBcE)) by (unfold LB, LBcE, PEC.owned; rewrite <- !app_assoc; apply Permutation_sym; apply perm4).
      pose proof (heap_perm _ _ cr M1 _ PERME HH1) as HH1e.
      assert (BRE : PMFR.brange L LBcE) by (apply (PMFR.brange_of_heap L HI HIok _ LBcE cr M1 _ HH1e); apply incl_appr; apply incl_refl).
      assert (EK1 : PMK.ek L LBcE sp 20480 WsE M M1).
      { apply (ek_piece_own (PEC.enc_own en) LBcE cr M1 _ sp 20480 WsE M M1 P1 eb (PEC.ESZ * PEC.ecap ek) HH1e INeo FRZ1' ltac:(unfold hl_ceil; lia) ltac:(lia)).
        intros a [Pa|[Pa|[Pa|Pa]]]; [left; lia| right; left; apply PMK.inW_here; lia| right; left; apply PMK.inW_here; lia|].
        right. right. apply CCB in Pa. unfold PEC.ESZ. clear - Pa ELEN CN. Lia.lia. }
      assert (WHIE : forall a, PMK.inW WsE a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
      assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by exact (PMK.stk_grows L M M1 sp 20480 MG1 STK).

      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
      { apply (PMK.ret_to RSEGS fx1 R1 M1 0x35870 W_35818 r F_35818 eq_refl D_35818); [rewrite (KS1 1%nat) by PMK.inl; exact Rra| lia| exact Hr2]. }

      assert (INC0E : incl LBc0 LBcE) by (unfold LBc0, LBcE; insub).
      assert (EKT : PMK.ek L LBc0 sp 20480 WsE M M1).
      { apply (PMK.ek_weaken L LBc0 LBcE sp 20480 sp 20480 WsE WsE M M1 EK1); [exact INC0E| intros x Hx; exact Hx| intros a O; exact O]. }
      destruct (KEEPF WsE M1 EKT) as (PA1 & IA1 & VREF1 & BASE1 & CONT1).
      { intros a I. apply PMFR.inW_inv1 in I. unfold WEC. lia. }
      destruct (KEEPE WsE M1 EKT) as (ERR1 & ECS1).
      { intros a I. apply PMFR.inW_inv1 in I. unfold WOB. lia. }
      assert (SKA1 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M1 (fb + 496) k).
      { apply (PECF.sink_keep RSEGS L KL LBcE sp 20480 WsE M M1 EK1 STK SC0 BRE WHIE); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| unfold LBcE; insub| exact SKA]. }
      assert (EA1 : enc_at M1 (fb + 440) fb (PEC.ENC eb ek (rev (ebump rr)) (edepth - 1))).
      { apply (enc_pop M M1 (fb + 440) fb eb ek rr (EI kd ln ln) edepth (edepth - 1) EA); [lia|lia| intros _; unfold PEC.ESZ; lia| | | exact MG1| | exact C48c| unfold MAX_DEPTH; lia| exact CC1].
        - intros i Hi Ri N1 N2. apply FRZ1'; [exact Hi|]. unfold P1. intros [X'|[X'|[X'|X']]]; [clear - X' Ri F1; Lia.lia| apply N2; clear - X'; Lia.lia| apply N1; clear - X'; Lia.lia|].
          apply CCB in X'. clear - X' Ri B4 ELEN CN SLO F1. Lia.lia.
        - intros _ i Hi Ri Ni. apply FRZ1'; [exact Hi|]. unfold P1. unfold PEC.ESZ in Ri. intros [X'|[X'|[X'|X']]]; [clear - X' Ri B4 CN SLO; Lia.lia| clear - X' Ri B4 CN SLO F1; Lia.lia| clear - X' Ri B4 CN SLO F1; Lia.lia| exact (Ni X')].
        - unfold PEC.ESZ. exact C32c. }
      apply (KONT fx1 R1 M1 model (PEC.ENC eb ek (rev (ebump rr)) (edepth - 1)) k e cr).
      * apply PMK.preserved_by_index. intros k0 Hk0. apply KS1. exact (sub_in PESENDP.KS_encEACe10 PMK.cs_all ltac:(vm_compute; reflexivity) k0 Hk0).
      * unfold PEC.crun_pre. unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PESK.o_sink. cbn [pa_off_p pa_off_is pa_off_v pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S].
        split; [exact PA1|]. split; [exact IA1|]. split; [exact EA1|]. split; [exact VREF1|]. split; [exact SKA1|].
        split; [exact BASE1|]. split; [exact ERR1|]. split; [exact TBOK|]. split; [exact CONT1|].
        split.
        { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PEC.en_stk PEC.en_depth].
          split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
          split; [reflexivity|]. split; [lia|]. split; [exact Lz| exact Lbad]. }
        split; [exact ECS1| exact ECI].
      * intros X'; exact X'.
      * apply (PMK.hpres_of L LBc0 sp 20480 _ M M1).
        -- apply (PMK.ek_weaken L LBc0 LBc0 sp 20480 sp 20480 _ WsE M M1 EKT); [apply incl_refl| intros x Hx; exact Hx|].
           intros a O r0 Hr0 Hin. unfold PEC.W_enc, PMSP.o_v, PMSP.o_ec, PESK.o_sink in O.
           cbn [pa_off_v pa_off_ec pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S app] in O.
           unfold WsE in Hr0. destruct Hr0 as [<-|[]]. apply (O (fb + 440, 56)); [left; reflexivity| exact Hin].
        -- destruct STK1 as (_ & _ & _ & _ & D1). exact D1.
        -- apply (PMK.dk_grows L LBc0 sp 20480 M M1 MG1).
      * unfold PMSP.credit_keep, PEC.pot_enc, PEC.credit_add. change (PEC.en_k en) with ek. cbn [fst snd PEC.en_k]. clear. Lia.lia.
      * apply L5C.model_but_vm_refl.
      * change (PEC.enc_own (PEC.ENC eb ek (rev (ebump rr)) (edepth - 1))) with (PEC.enc_own en). exact HH1.
    +
      assert (EEND : e_end X = ST (s_stk X) (s_pos X) (s_more X) (s_done X) (s_halt X) (s_depth X) true (s_estk X) (s_edepth X - 1) (s_lo X) (s_hi X) (s_bad X)).
      { destruct (Z_lt_le_dec cn ln) as [LT|GE]; [exact (e_end_lt X _ rr HES EIND LT)| apply (e_end_gt X _ rr HES EIND); cbn [ei_len ei_cnt]; lia]. }
      rewrite EEND in NB, HB, KONT. cbn [s_bad s_hi] in NB, HB. rewrite HES in KONT.

      assert (POSTC : exists fx1 R1 M1 (v : Z), mem_grows M M1
        /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
        /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 0x357c4) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x36f18) M1 (seg_rom RSEGS))
        /\ (forall x, In x PESENDP.KS_encEAI1 -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
        /\ getr R1 (PMK.reg 1) = Z_to_bv 64 219228
        /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 48)
        /\ getr R1 (PMK.reg 8) = getr R (PMK.reg 10)
        /\ getr R1 (PMK.reg 10) = getr R (PMK.reg 12)
        /\ getr R1 (PMK.reg 11) = Z_to_bv 64 v /\ 1 <= v <= 64
        /\ L5.u32_at RSEGS M1 (fb + 440 + 48) (edepth - 1)
        /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))
        /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
        /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))).
      { destruct (Z_lt_le_dec cn ln) as [LT|GE].
        -
          destruct KDC as [KD|KD]; subst kd.
          + pose proof (PESENDP.encEAClt0_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                | 39%nat => cn | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
            PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                   | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN E0OK LT; unfold hl_ceil in *; lia) ]).
            post_of_v P1 9.
          + pose proof (PESENDP.encEAClt2_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                | 39%nat => cn | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
            PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                   | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN E0OK LT; unfold hl_ceil in *; lia) ]).
            post_of_v P1 9.
        - destruct (Z_lt_le_dec cn 18446744073692774400) as [LOW|HIGH].
          +
            destruct KDC as [KD|KD]; subst kd.
            * pose proof (PESENDP.encEACgt0_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                  | 41%nat => fb + 496 | 43%nat => cn - ln | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
              PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                     | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN E0OK GE CNE LOW; unfold hl_ceil in *; lia) ]).
              post_of_v P1 8.
            * pose proof (PESENDP.encEACgt2_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                  | 41%nat => fb + 496 | 43%nat => cn - ln | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
              PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                     | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN E0OK GE CNE LOW; unfold hl_ceil in *; lia) ]).
              post_of_v P1 8.
          +
            destruct KDC as [KD|KD]; subst kd.
            * pose proof (PESENDP.encEACgth0_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                  | 39%nat => cn | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
              PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                     | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN E0OK GE HIGH; unfold hl_ceil in *; lia) ]).
              post_of_v P1 8.
            * pose proof (PESENDP.encEACgth2_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                  | 39%nat => cn | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
              PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                     | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN E0OK GE HIGH; unfold hl_ceil in *; lia) ]).
              post_of_v P1 8. }
      PMK.pvz_hg ltac:(idtac; destruct POSTC as (fx1 & R1 & M1 & v & pvzP); PMK.pvz_lin pvzP;
                       destruct pvzP as (MG1 & FRZ1 & MS1 & KS1 & X1_1 & X2_1 & X8_1 & X10_1 & X11_1 & HV & C48 & S24 & S16 & S8)); PMK.pvz_clrT.
      rewrite A10 in X8_1. rewrite A12 in X10_1.
      set (P1 := fun a => (sp - 48 <= a < sp - 48 + 48) \/ (fb + 440 + 48 <= a < fb + 440 + 48 + 4)).
      assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha N. apply FRZ1; [exact Ha| |]; intros X'; apply N; unfold P1; [left| right]; exact X'. }
      apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x357c4 R1 0x36f18 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
      { intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P1 in Pa. clear - Pa SLO SHI F1 F2. Lia.lia. }
      { intros a. unfold P1. apply PMK.or_dec; apply PMK.rng_dec. }
      intros HH1.
      set (W1 := [(fb + 440 + 48, 4)] : list L5.range).
      assert (WHI1 : forall a, PMK.inW W1 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
      assert (NW1 : forall i, ~ (fb + 440 + 48 <= i < fb + 440 + 52) -> ~ PMK.inW W1 i) by (intros i Hi I; apply PMFR.inW_inv1 in I; lia).
      assert (EK1 : PMK.ek L LB sp 20480 W1 M M1).
      { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W1 M M1 P1 FRZ1' STK (PMFR.brange_hi L LB BR)).
        intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
      assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by exact (PMK.stk_grows L M M1 sp 20480 MG1 STK).
      assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 48) 14336).
      { apply (PMK.stk_call L M1 sp 20480 (sp - 48) 14336 STK1); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
      assert (EKT1 : PMK.ek L LBc0 sp 20480 W1 M M1) by (apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 W1 W1 M M1 EK1); [exact INC0| intros x Hx; exact Hx| intros a O; exact O]).
      destruct (KEEPF W1 M1 EKT1) as (_ & _ & _ & BASE1 & _). { intros a I. apply PMFR.inW_inv1 in I. unfold WEC. lia. }
      destruct (KEEPE W1 M1 EKT1) as (ERR1 & _). { intros a I. apply PMFR.inW_inv1 in I. unfold WOB. lia. }
      assert (ECD : L5.defined M (fb + 16) 16).
      { unfold PEC.ec_state, PMSP.o_ec in ECS. cbn [pa_off_ec CAD PeCLayoutS.CADDR_S] in ECS.
        destruct (s_ec X); [destruct ECS as (v0 & _ & (_ & _ & D0)); exact D0| destruct ECS as (_ & _ & D0); exact D0]. }
      assert (SKA1 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M1 (fb + 496) k).
      { apply (PECF.sink_keep RSEGS L KL LB sp 20480 W1 M M1 EK1 STK SC0 BR WHI1); [lia|lia| intros i' Hi'; apply NW1; lia| exact KINC| exact SKA]. }
      assert (EA1 : enc_at M1 (fb + 440) fb (PEC.ENC eb ek (rev rr ++ [EI kd ln cn]) (edepth - 1))).
      { apply (enc_depth M M1 (fb + 440) fb eb ek _ edepth (edepth - 1) EA); [lia|lia| intros _; unfold PEC.ESZ; lia| | | exact MG1| exact C48| unfold MAX_DEPTH; lia].
        - intros i Hi Ri Ni. apply FRZ1'; [exact Hi|]. unfold P1. clear - Ri Ni F1. Lia.lia.
        - intros _ i Hi Ri. apply FRZ1'; [exact Hi|]. unfold P1, PEC.ESZ in *. clear - Ri B4 SLO F1 SHI STOP. lia. }

      pose proof MKEC as MKX. unfold PECSS.make_ec_spec, PECS.make_ec_spec in MKX. cbn [pa_make_ec PECSS.AD PeCLayoutS.CADDR_S] in MKX.
      apply (MKX fx1 R1 M1 model K LB cr (fb + 16) v (sp - 48) 219228 e HH1 MOK K0); clear MKX.
      { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1_1|]. split; [clear; unfold L5.ra_ok; Lia.lia|]. split; [exact X2_1|].
        split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
      { rewrite L5K.rl10. exact X10_1. }
      { rewrite L5K.rl11. exact X11_1. }
      { exact HV. } { lia. } { lia. } { exact ALec. }
      { exact (L5.defined_grows M M1 _ _ MG1 ECD). }
      { exact BASE1. }
      { exact ERR1. }
      intros fx2 R2 M2 RP2 EC2 ERR2 HP2 HH2.
      change (PMSP.pm_scr 1) with 14336 in HP2.
      set (W2 := (fb + 16, 16) :: (if e then [] else PMSP.err_W CAD)) in HP2.
      assert (WC2 : forall a, PMK.inW W2 a -> (fb + 16 <= a < fb + 16 + 16) \/ (0xc9640 <= a < 0xc9640 + 2) \/ (0xeb088 <= a < 0xeb088 + 544)).
      { intros a (r0 & Hin & Hr). unfold W2 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|].
        destruct e; [destruct Hin|]. unfold PMSP.err_W in Hin. cbn [pa_errcat_guard pa_atexit CAD PeCLayoutS.CADDR_S] in Hin.
        destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
      pose proof (PMK.stk_after RSEGS L KL LB M1 M2 sp 20480 (sp - 48) 14336 _ STK1 HP2 ltac:(lia) ltac:(lia) ltac:(lia)) as STK2.
      pose proof (L5C.stk_writable RSEGS _ M2 sp 20480 STK2) as WR2.
      pose proof (PMK.ek_of_hpres L LB (sp - 48) 14336 W2 M1 M2 HP2) as EK2.
      assert (SC2 : 0 <= 14336) by lia.
      assert (WHI2 : forall a, PMK.inW W2 a -> sp - 48 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WC2 in I; rewrite IMLO, IMHI; clear - I F1; Lia.lia).
      assert (NW2 : forall i, (sp - 48 <= i < fb + 16 \/ fb + 16 + 16 <= i <= 2 ^ 64) -> ~ PMK.inW W2 i) by (intros i Hi I; apply WC2 in I; clear - Hi I IMLO IMHI F1 F2 STOP SLO; Lia.lia).
      assert (S24b : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))).
      { apply (PMFR.u64_keep RSEGS L KL LB (sp - 48) 14336 _ M1 M2 EK2 STKc SC2); [lia|lia| intros i Hi; apply NW2; lia| exact S24]. }
      assert (S16b : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))).
      { apply (PMFR.u64_keep RSEGS L KL LB (sp - 48) 14336 _ M1 M2 EK2 STKc SC2); [lia|lia| intros i Hi; apply NW2; lia| exact S16]. }
      assert (S8b : L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))).
      { apply (PMFR.u64_keep RSEGS L KL LB (sp - 48) 14336 _ M1 M2 EK2 STKc SC2); [lia|lia| intros i Hi; apply NW2; lia| exact S8]. }
      pose proof (bv_unsigned_in_range 64 (getr R2 (PMK.reg 10))) as RBj. change (bv_modulus 64) with (2 ^ 64) in RBj.

      pose proof (PESENDP.encEAR_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 10%nat => fb + 440
          | 44%nat => bv_unsigned (getr R (PMK.reg 1)) | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
          | 55%nat => bv_unsigned (getr R2 (PMK.reg 10)) | _ => 0 end)) as P3. cbn beta iota in P3.
      PMK.feed P3 ltac:(first [(unfold PESENDP.aligned; exact A16) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                             | (clear - SLO STOP SHI F1 F2; unfold hl_ceil in *; lia) ]).
      destruct P3 as (fx3 & R3 & M3 & _ & FRW3 & _ & MS3 & KS3 & Y1 & Y2 & Y8 & Y9 & Y10).
      assert (EM : M3 = M2) by (apply functional_extensionality; exact FRW3). subst M3.
      apply (PMK.spiece_ro RSEGS model fx2 fx3 R2 219228 R3 0x35870 M2 K Mh Ml MS3).
      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
      { apply (PMK.ret_to RSEGS fx3 R3 M2 0x35870 W_35818 r F_35818 eq_refl D_35818); [rewrite Y1, PMPK.word_id; exact Rra| lia| exact Hr2]. }

      assert (EKT : PMK.ek L LBc0 sp 20480 (PEC.W_enc CAD EE fb) M M2).
      { apply (PMK.ek_trans L LBc0 sp 20480 _ M M1 M2).
        { apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 _ W1 M M1 EK1); [exact INC0| intros x Hx; exact Hx|].
          intros a O r0 Hr0 Hin. unfold W1 in Hr0. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
          unfold PEC.W_enc, PMSP.o_v in O. cbn [pa_off_v CAD PeCLayoutS.CADDR_S app] in O.
          apply (O (fb + 440, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
        apply (PMK.ek_callee_in' RSEGS L KL LBc0 LB sp 20480 (sp - 48) 14336 _ W2 M1 M2 HP2 INC0);
          [lia|lia| unfold hl_ceil; lia| lia| exact (PMFR.brange_hi L LBc0 BRc0)|].
        intros a I. apply WC2 in I. right. unfold PEC.W_enc, PMSP.err_W, PMSP.o_v, PMSP.o_ec, PESK.o_sink.
        cbn [pa_off_v pa_off_ec pe_off_sink pa_errcat_guard pa_atexit CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S app].
        destruct I as [I|[I|I]]; [do 2 apply PMK.inW_next; apply PMK.inW_here; lia| do 3 apply PMK.inW_next; apply PMK.inW_here; lia| do 4 apply PMK.inW_next; apply PMK.inW_here; lia]. }
      destruct (KEEPF _ M2 EKT WCE) as (PA2 & IA2 & VREF2 & BASE2 & CONT2).
      assert (SKA2 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M2 (fb + 496) k).
      { apply (PECF.sink_keep RSEGS L KL LB (sp - 48) 14336 W2 M1 M2 EK2 STKc SC2 (PMFR.brange_incl L LB LB BR ltac:(apply incl_refl)) WHI2); [lia|lia| intros i Hi; apply NW2; lia| exact KINC| exact SKA1]. }
      assert (EA2 : enc_at M2 (fb + 440) fb (PEC.ENC eb ek (rev rr ++ [EI kd ln cn]) (edepth - 1))).
      { apply (PECF.enc_keep RSEGS EE L KL LB (sp - 48) 14336 W2 M1 M2 EK2 STKc SC2 BR WHI2); [lia|lia| intros i Hi; apply NW2; lia| exact EINC| exact EA1]. }
      apply (KONT fx3 R3 M2 model (PEC.ENC eb ek (rev rr ++ [EI kd ln cn]) (edepth - 1)) k true cr).
      * apply PMK.preserved_by_index. intros k0 Hk0.
        destruct (Nat.eq_dec k0 2) as [->|N2]; [rewrite Y2; symmetry; exact Rsp|].
        destruct (Nat.eq_dec k0 8) as [->|N8]; [rewrite Y8; apply PMPK.word_id|].
        destruct (Nat.eq_dec k0 9) as [->|N9]; [rewrite Y9; apply PMPK.word_id|].
        assert (IN3 : In k0 PESENDP.KS_encEAR /\ In k0 PESENDP.KS_encEAI1) by (cbn in Hk0; decompose [or] Hk0; subst; try (exfalso; congruence); (split; PMK.inl)).
        destruct IN3 as [I3 I1]. rewrite (KS3 k0 I3), (PMK.cs_of_preserved R1 R2 k0 RP2 Hk0), (KS1 k0 I1). reflexivity.
      * unfold PEC.crun_pre. unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PESK.o_sink. cbn [pa_off_p pa_off_is pa_off_v pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S].
        split; [exact PA2|]. split; [exact IA2|]. split; [exact EA2|]. split; [exact VREF2|]. split; [exact SKA2|].
        split; [exact BASE2|]. split; [exact ERR2|]. split; [exact TBOK|]. split; [exact CONT2|].
        split.
        { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PEC.en_stk PEC.en_depth rev].
          split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
          split; [reflexivity|]. split; [lia|]. split; [exact Lz| exact Lbad]. }
        split; [| intros _; reflexivity].
        unfold PEC.ec_state, PMSP.o_ec. cbn [pa_off_ec CAD PeCLayoutS.CADDR_S]. exists v. split; [exact HV| exact EC2].
      * intros _; reflexivity.
      * apply (PMK.hpres_of L LBc0 sp 20480 _ M M2); [exact EKT| destruct STK2 as (_ & _ & _ & _ & D2); exact D2|].
        apply (PMK.dk_trans L LBc0 sp 20480 M M1 M2 (PMK.dk_grows L LBc0 sp 20480 M M1 MG1)).
        apply (PMK.dk_callee L LBc0 LB sp 20480 (sp - 48) 14336 _ M1 M2 HP2 INC0); lia.
      * unfold PMSP.credit_keep, PEC.pot_enc, PEC.credit_add. change (PEC.en_k en) with ek. cbn [fst snd PEC.en_k]. clear. Lia.lia.
      * apply L5C.model_but_vm_refl.
      * change (PEC.enc_own (PEC.ENC eb ek (rev rr ++ [EI kd ln cn]) (edepth - 1))) with (PEC.enc_own en). exact HH2.
Qed.

Theorem v_end_obj_ok :
  PESK.push_back_spec RSEGS CAD EE L HI PMSP.T3 PMSP.T4 P -> PECSS.make_ec_spec L HI -> PECSS.v_end_obj_spec L HI P.
Proof.
  intros PB MKEC. unfold PECSS.v_end_obj_spec, PECS.v_end_obj_spec, PECS.eslot_spec.
  intros SPM [] fx R M model K LBX cr sp r fb cat p X s str sm en k e HH MOK K0 ENT FOK A10 A12 CPRE INCS POK MP NB HB CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame CAD PeCLayoutS.CADDR_S] in F2.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  unfold PECS.args_t2 in A12.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI).
  destruct MP as ((LOHI & XBAD & FA & EDR) & ED1).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl12 in A12.
  unfold PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_ec, PMSP.o_v, PESK.o_sink in *.
  cbn [pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S] in *.
  change (PMSP.pm_scr 4) with 20480 in *.
  assert (SC0 : 0 <= 20480) by lia.
  set (LB := PEC.owned s en k ++ LBX) in *.
  assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
  pose proof (L5C.stk_writable RSEGS _ M sp 20480 STK) as WR.
  assert (PINC : incl (PM.parser_own s) LB) by (unfold LB, PEC.owned; intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx).
  assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
  assert (EINC : incl (PEC.enc_own en) LB).
  { unfold LB, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. exact Hx. }
  assert (KINC : incl (PESK.sink_own k) LB).
  { unfold LB, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hx. }

  destruct en as [eb ek estk edepth].
  pose proof EA as (EV0 & EV8 & EV16 & EV24 & EV32 & EV40 & EV48 & EDEF & _ & EK & ELEN & EDEP & EKB & EBLK & EITEMS).
  cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EV24, EV32, EV40, EV48, EK, ELEN, EDEP, EKB, EBLK, EITEMS.

  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [PEC.en_stk PEC.en_depth] in Lestk, Ledepth.
  destruct (s_estk X) as [|e0 rr] eqn:HES; [exfalso; rewrite (e_end_nil X HES) in NB; discriminate|].
  cbn [rev] in Lestk.
  pose proof (Forall_inv FA) as E0OK. pose proof (Forall_inv_tail FA) as RROK. unfold ei_ok in E0OK.
  destruct e0 as [kd ln cn]. cbn [ei_kind ei_len ei_cnt] in E0OK.
  set (n := Z.of_nat (length rr)).
  assert (HLEN : Z.of_nat (length estk) = n + 1) by (rewrite Lestk, length_app, length_rev; cbn [length]; lia).
  assert (EKP : 0 < ek).
  { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in ELEN. rewrite Z0 in ELEN. cbn in ELEN. lia. }
  destruct (EBLK EKP) as (EBAL & EBDEF & EBR & _ & _).
  pose proof (PEC.ecap_nonneg ek) as CN.
  assert (BIN : In (eb, PEC.ESZ * PEC.ecap ek) LB).
  { apply EINC. unfold PEC.enc_own. cbn [PEC.en_k PEC.en_b]. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  destruct (BR _ _ BIN) as (B0 & B1 & B4). unfold hl_ceil in B4. unfold PEC.ESZ in B1, B4.

  pose proof (EITEMS (length rr) ltac:(rewrite Lestk, length_app, length_rev; cbn [length]; lia)) as ETOP.
  rewrite Lestk, nth_top in ETOP. destruct ETOP as (T0 & T8 & T16). cbn [ei_kind ei_len ei_cnt] in T0, T8, T16. unfold PEC.ESZ in T0, T8, T16.
  fold n in T0, T8, T16.
  assert (ALov : (fb + 440) mod 8 = 0) by (apply (m8_of16 fb); [exact F3| reflexivity]).
  assert (ALsk : (fb + 496) mod 8 = 0) by (apply (m8_of16 fb); [exact F3| reflexivity]).
  assert (ALec : (fb + 16) mod 8 = 0) by (apply (m8_of16 fb); [exact F3| reflexivity]).
  assert (ALend : (eb + 24 * (n + 1)) mod 8 = 0) by (apply al8_item; exact EBAL).
  assert (HO : bv_unsigned (getr R (PMK.reg 10)) = fb + 440) by (rewrite A10; apply L5.unsigned_lit; lia).
  assert (HEC : bv_unsigned (getr R (PMK.reg 12)) = fb + 16) by (rewrite A12; apply L5.unsigned_lit; lia).
  rewrite HLEN in EV32. unfold PEC.ESZ in EV32, EV40, EBDEF, ELEN.
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as RB1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as RB8.
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as RB9. change (bv_modulus 64) with (2 ^ 64) in RB1, RB8, RB9.
  unfold PMSP.cfg. cbn [pe_end_obj EE PeCLayoutS.EADDR_S].
  pose proof (ly_img_lo L LY) as IMLO. pose proof (ly_img_hi L LY) as IMHI.

  set (LBc0 := PM.parser_own s ++ LBX).
  assert (BRc0 : PMFR.brange L LBc0) by (apply (PMFR.brange_incl L LBc0 LB BR); unfold LBc0, LB, PEC.owned; intros x Hx; apply in_app_or in Hx;
     apply in_or_app; destruct Hx as [Hx|Hx]; [left; apply in_or_app; left; exact Hx| right; exact Hx]).
  assert (PINC0 : incl (PM.parser_own s) LBc0) by (unfold LBc0; apply incl_appl; apply incl_refl).
  assert (SINC0 : incl (PM.vs_own str) LBc0) by (unfold LBc0; apply incl_appr; exact INCS).
  set (WEC := fun a : Z => (fb + 440 <= a < fb + 520) \/ (fb + 16 <= a < fb + 16 + 16) \/ (0xc9640 <= a < 0xc9640 + 2) \/ (0xeb088 <= a < 0xeb088 + 544)).
  assert (KEEPF : forall W M', PMK.ek L LBc0 sp 20480 W M M' -> (forall a, PMK.inW W a -> WEC a) ->
            PM.parser_at RSEGS CAD PMSP.T3 PMSP.T4 M' (fb + 48) (fb + 520) s /\ PM.iss_at RSEGS CAD PMSP.T3 M' (fb + 520) str sm
            /\ L5.u64_at RSEGS M' (fb + 48 + 384) (fb + 440) /\ PMST.base_ok RSEGS CAD M' /\ PEC.content_ok RSEGS CAD M' fb p (PM.p_src s) str sm).
  { intros W M' EKW WC.
    assert (WHI : forall a, PMK.inW W a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WC in I; unfold WEC in I; rewrite IMLO, IMHI; clear - I F1; Lia.lia).
    assert (NW : forall i, ~ WEC i -> ~ PMK.inW W i) by (intros i Hi I; apply Hi; apply WC; exact I).
    split; [apply (PMFR.parser_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 BRc0 WHI); [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact PINC0| exact PA]|].
    split; [apply (PMFR.iss_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 BRc0 WHI); [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact SINC0| exact IA]|].
    split; [apply (PMFR.u64_keep RSEGS L KL LBc0 sp 20480 W M M' EKW STK SC0); [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact VREF]|].
    split; [apply (PMKP.base_ok_keep RSEGS CAD L KL SF LBc0 sp 20480 W M M' EKW); [| | | | exact BASE];
            intros a Ha; apply PMFR.outside_of_not_inW; apply NW; unfold WEC;
            cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock CAD PeCLayoutS.CADDR_S] in Ha; clear - Ha SLO STOP F1; lia|].
    apply (PECF.content_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 BRc0 WHI fb p s str sm (fb + 48));
      unfold PMSP.o_is; cbn [pa_off_is CAD PeCLayoutS.CADDR_S]; [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact SINC0| exact PINC0| exact IA| exact PA| exact CONT]. }

  set (WOB := fun a : Z => (fb + 440 <= a < fb + 520)).
  assert (KEEPE : forall W M', PMK.ek L LBc0 sp 20480 W M M' -> (forall a, PMK.inW W a -> WOB a) ->
            PEST.err_ok RSEGS CAD EE M' e /\ PEC.ec_state RSEGS CAD M' fb (s_ec X) cat).
  { intros W M' EKW WC.
    assert (NW : forall i, ~ WOB i -> ~ PMK.inW W i) by (intros i Hi I; apply Hi; apply WC; exact I).
    split; [apply (PECKP.err_ok_keep RSEGS CAD EE L KL SF LBc0 sp 20480 W M M' EKW); [| | exact ERR];
            intros a Ha; apply PMFR.outside_of_not_inW; apply NW; unfold WOB;
            cbn [pa_errcat_guard pa_atexit CAD PeCLayoutS.CADDR_S] in Ha; clear - Ha SLO STOP F1 IMLO IMHI; lia|].
    apply (PECF.ec_state_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 fb (s_ec X) cat);
      unfold PMSP.o_ec; cbn [pa_off_ec CAD PeCLayoutS.CADDR_S]; [lia|lia| intros i' Hi'; apply NW; unfold WOB; lia| exact ECS]. }

  assert (WCE : forall a, PMK.inW (PEC.W_enc CAD EE fb) a -> WEC a).
  { intros a (r0 & Hin & Hr). unfold PEC.W_enc, PMSP.err_W, PMSP.o_v, PMSP.o_ec, PESK.o_sink in Hin.
    cbn [pa_off_v pa_off_ec pe_off_sink pa_errcat_guard pa_atexit CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S app] in Hin.
    unfold L5.in_rng in Hr. unfold WEC. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; lia. }

  assert (KPM0 : 0 <= hl_k_per_malloc L) by (pose proof (ly_kpm L LY); lia).
  assert (BOV0 : 0 <= hl_b_overhead L) by (pose proof (ly_bov L LY); lia).
  assert (PEN : 0 <= fst (PEC.pot_estack L ek) /\ 0 <= snd (PEC.pot_estack L ek)).
  { clear - KPM0 BOV0 EK. unfold PEC.pot_estack, PEC.ESZ. cbn [fst snd]. assert (P2 : 2 ^ ek <= 2 ^ 12) by (apply Z.pow_le_mono_r; Lia.lia). split; Lia.nia. }
  assert (CREDk : PMSP.credit_le (PESK.sink_pot P (PESK.sk_c k)) cr).
  { unfold PMSP.credit_le, PEC.pot_enc, PEC.credit_add in CRED |- *. cbn [fst snd PEC.en_k] in CRED |- *. lia. }
  assert (ECAPB : PEC.ecap ek <= 2048).
  { clear - EK EKP. unfold PEC.ecap. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; Lia.lia). change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; Lia.lia. }
  rewrite HLEN in ELEN. unfold MAX_DEPTH, MAX_ITEMS, TWO64 in EDR, EDEP, E0OK.
  assert (WRov : L5.writable RSEGS M (fb + 440) 56) by (apply (L5C.writable_of_defined RSEGS); [exact EDEF|lia|lia]).
  pose proof SKA as (_ & _ & _ & _ & _ & KZ & KCAP & KC0 & KBLK).
  set (en := PEC.ENC eb ek estk edepth) in *.
  set (LBY := PM.parser_own s ++ PEC.enc_own en ++ LBX).
  assert (XINCY : incl LBc0 LBY) by (unfold LBc0, LBY; insub).
  assert (EINCY : incl (PEC.enc_own en) LBY) by (unfold LBY; insub).
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; insub).
  assert (PERM1 : Permutation LB (PESK.sink_own k ++ LBY)) by (unfold LB, LBY, PEC.owned; rewrite <- !app_assoc; apply perm4).
  subst estk.
  assert (KD4 : (kd = 1 \/ kd = 3) \/ (kd = 0 \/ kd = 2)) by lia.
  destruct KD4 as [KDI|KDC].
  -
    assert (EIND : ei_indef (EI kd ln cn) = true) by (unfold ei_indef; cbn [ei_kind]; destruct KDI as [-> | ->]; reflexivity).
    rewrite (e_end_indef X _ rr HES EIND) in NB, HB, KONT. cbn [s_bad s_hi] in NB, HB.

    assert (POSTI : exists fx1 R1 M1, mem_grows M M1
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ (msteps RSEGS (@mkst fx R (Z_to_bv 64 0x35f30) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x372d8) M1 (seg_rom RSEGS))
          /\ (forall x, In x PESENDP.KS_encEOI1 -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
          /\ getr R1 (PMK.reg 1) = Z_to_bv 64 221056
          /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 48)
          /\ getr R1 (PMK.reg 8) = getr R (PMK.reg 10)
          /\ getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 496)
          /\ getr R1 (PMK.reg 11) = Z_to_bv 64 (sp - 48)
          /\ L5.u32_at RSEGS M1 (fb + 440 + 48) (edepth - 1)
          /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))
          /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
          /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))))).
    { destruct KDI as [KD|KD]; subst kd.
      + pose proof (PESENDP.encEOI1_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                     | 39%nat => cn | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
        PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                               | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN; unfold hl_ceil in *; lia) ]).
        post_of P1.
      + pose proof (PESENDP.encEOI3_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                     | 39%nat => cn | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
        PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                               | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN; unfold hl_ceil in *; lia) ]).
        post_of P1. }
    PMK.pvz_hg ltac:(idtac; destruct POSTI as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG1 & FRZ1 & MS1 & KS1 & X1_1 & X2_1 & X8_1 & X10_1 & X11_1 & C48 & S24 & S16 & S8)); PMK.pvz_clrT.
    rewrite A10 in X8_1.
    set (P1 := fun a => (sp - 48 <= a < sp - 48 + 48) \/ (fb + 440 + 48 <= a < fb + 440 + 48 + 4)).
    assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ1; [exact Ha| |]; intros X'; apply N; unfold P1; [left| right]; exact X'. }
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x35f30 R1 0x372d8 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
    { intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P1 in Pa. clear - Pa SLO SHI F1 F2. Lia.lia. }
    { intros a. unfold P1. apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    set (W1 := [(fb + 440 + 48, 4)] : list L5.range).
    assert (WHI1 : forall a, PMK.inW W1 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
    assert (NW1 : forall i, ~ (fb + 440 + 48 <= i < fb + 440 + 52) -> ~ PMK.inW W1 i) by (intros i Hi I; apply PMFR.inW_inv1 in I; lia).
    assert (EK1 : PMK.ek L LB sp 20480 W1 M M1).
    { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W1 M M1 P1 FRZ1' STK (PMFR.brange_hi L LB BR)).
      intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
    assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by exact (PMK.stk_grows L M M1 sp 20480 MG1 STK).
    assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 48) 12288).
    { apply (PMK.stk_call L M1 sp 20480 (sp - 48) 12288 STK1); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    assert (SKA1 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M1 (fb + 496) k).
    { apply (PECF.sink_keep RSEGS L KL LB sp 20480 W1 M M1 EK1 STK SC0 BR WHI1); [lia|lia| intros i' Hi'; apply NW1; lia| exact KINC| exact SKA]. }
    assert (EA1 : enc_at M1 (fb + 440) fb (PEC.ENC eb ek (rev rr ++ [EI kd ln cn]) (edepth - 1))).
    { apply (enc_depth M M1 (fb + 440) fb eb ek _ edepth (edepth - 1) EA); [lia|lia| intros _; unfold PEC.ESZ; lia| | | exact MG1| exact C48| unfold MAX_DEPTH; lia].
      - intros i Hi Ri Ni. apply FRZ1'; [exact Hi|]. unfold P1. clear - Ri Ni F1. Lia.lia.
      - intros _ i Hi Ri. apply FRZ1'; [exact Hi|]. unfold P1, PEC.ESZ in *. clear - Ri B4 SLO F1 SHI STOP. lia. }

    pose proof PB as PBX. unfold PESK.push_back_spec in PBX. cbn [pe_push_back EE PeCLayoutS.EADDR_S] in PBX.
    apply (PBX SPM fx1 R1 M1 model K LBY cr (fb + 496) (sp - 48) (sp - 48) 221056 k); clear PBX.
    { apply (heap_perm LB); [exact PERM1| exact HH1]. }
    { exact MOK. }
    { exact K0. }
    { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1_1|]. split; [clear; unfold L5.ra_ok; Lia.lia|]. split; [exact X2_1|].
      split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
    { rewrite L5K.rl10. exact X10_1. }
    { rewrite L5K.rl11. exact X11_1. }
    { exact SKA1. }
    { lia. } { lia. } { exact ALsk. } { lia. } { lia. } { left; lia. }
    { destruct STK1 as (_ & _ & _ & _ & D1). apply (L5.defined_sub M1 (sp - 20480) 20480 (sp - 48) 1 D1); lia. }
    { intros ZC. apply (PESK.spo_next P PO (PESK.sk_c k) (s_hi X + 1) KCAP); [intros Hc; exact (proj1 (proj2 (proj2 (proj2 (proj2 (KBLK Hc))))))| exact HB| lia]. }
    { exact CREDk. }
    intros fx2 R2 M2 model2 cr2 b2 RP2 SKA2 HP2 CK2 MB2 HH2.
    change (PMSP.pm_scr 0) with 12288 in HP2.
    set (k2 := PESK.sk_push k b2) in *.
    pose proof (bv_unsigned_in_range 64 (getr R2 (PMK.reg 10))) as RBj. change (bv_modulus 64) with (2 ^ 64) in RBj.
    pose proof (PMFR.model_ok_but_vm model model2 MOK MB2) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & Mm2).
    assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by (apply (PMK.stk_after RSEGS L KL LBY M1 M2 sp 20480 (sp - 48) 12288 _ STK1 HP2); lia).
    pose proof (L5C.stk_writable RSEGS _ M2 sp 20480 STK2) as WR2.
    pose proof (PMK.ek_of_hpres L LBY (sp - 48) 12288 [(fb + 496, 24)] M1 M2 HP2) as EK2.
    assert (BRY2 : PMFR.brange L (PESK.sink_own k2 ++ LBY)) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr2 M2 _ HH2); apply incl_refl).
    assert (BRY : PMFR.brange L LBY) by (apply (PMFR.brange_incl L LBY _ BRY2); apply incl_appr; apply incl_refl).
    assert (WHI2 : forall a, PMK.inW [(fb + 496, 24)] a -> sp - 48 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
    assert (SC2 : 0 <= 12288) by lia.
    assert (EA2 : enc_at M2 (fb + 440) fb (PEC.ENC eb ek (rev rr ++ [EI kd ln cn]) (edepth - 1))).
    { apply (PECF.enc_keep RSEGS EE L KL LBY (sp - 48) 12288 [(fb + 496, 24)] M1 M2 EK2 STKc SC2 BRY WHI2); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact EINCY| exact EA1]. }
    assert (S24b : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))).
    { apply (PMFR.u64_keep RSEGS L KL LBY (sp - 48) 12288 _ M1 M2 EK2 STKc SC2); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S24]. }
    assert (S16b : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))).
    { apply (PMFR.u64_keep RSEGS L KL LBY (sp - 48) 12288 _ M1 M2 EK2 STKc SC2); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S16]. }
    assert (S8b : L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))).
    { apply (PMFR.u64_keep RSEGS L KL LBY (sp - 48) 12288 _ M1 M2 EK2 STKc SC2); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S8]. }
    pose proof EA2 as (_ & _ & _ & EV24b & EV32b & _ & EV48b & EDEFb & _ & _ & _ & _ & _ & EBLKb & EITEMSb).
    cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EV24b, EV32b, EV48b, EBLKb, EITEMSb. unfold PEC.ESZ in EV32b. rewrite HLEN in EV32b.
    assert (WRov2 : L5.writable RSEGS M2 (fb + 440) 56) by (apply (L5C.writable_of_defined RSEGS); [exact EDEFb|lia|lia]).
    destruct (EBLKb EKP) as (_ & EBDEFb & _ & _ & _). unfold PEC.ESZ in EBDEFb.
    assert (WRblk2 : L5.writable RSEGS M2 eb (24 * PEC.ecap ek)) by (apply (L5C.writable_of_defined RSEGS); [exact EBDEFb|lia|lia]).

    assert (POSTJ : exists fx3 R3 M3, mem_grows M2 M3
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) -> ~ cc_rng eb rr i -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i))
      /\ (msteps RSEGS (@mkst fx2 R2 (Z_to_bv 64 0x35f80) M2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0x35fdc) M3 (seg_rom RSEGS))
      /\ (forall x, In x CSL -> getr R3 (PMK.reg x) = getr R2 (PMK.reg x))
      /\ getr R3 (PMK.reg 1) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 1)))
      /\ getr R3 (PMK.reg 2) = Z_to_bv 64 sp
      /\ getr R3 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8)))
      /\ getr R3 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9)))
      /\ L5.u64_at RSEGS M3 (fb + 440 + 32) (eb + 24 * n)
      /\ (forall e2 rr', rr = e2 :: rr' -> L5.u64_at RSEGS M3 (eb + PEC.ESZ * Z.of_nat (length rr') + 16) ((ei_cnt e2 + 1) mod TWO64)))).
    { destruct rr as [|e2 rr'].
      -
        unfold n in *. cbn [length] in T0, T8, T16, HLEN, ELEN, EV32, EV32b, ALend |- *. change (Z.of_nat 0) with 0 in *.
        pose proof (PESENDP.encEOJ1_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb
            | 44%nat => bv_unsigned (getr R (PMK.reg 1)) | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
            | 55%nat => bv_unsigned (getr R2 (PMK.reg 10)) | _ => 0 end)) as P3. cbn beta iota in P3.
        PMK.feed P3 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact EBAL]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN; unfold hl_ceil in *; lia) ]).
        assert (POST1 : exists fx3 R3 M3, mem_grows M2 M3
          /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i))
          /\ (msteps RSEGS (@mkst fx2 R2 (Z_to_bv 64 0x35f80) M2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0x35fdc) M3 (seg_rom RSEGS))
          /\ (forall x, In x PESENDP.KS_encEOJ1 -> getr R3 (PMK.reg x) = getr R2 (PMK.reg x))
          /\ getr R3 (PMK.reg 1) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 1)))
          /\ getr R3 (PMK.reg 2) = Z_to_bv 64 sp
          /\ getr R3 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8)))
          /\ getr R3 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9)))
          /\ L5.u64_at RSEGS M3 (fb + 440 + 32) eb)) by post_of P3.
        destruct POST1 as (fx3 & R3 & M3 & MG & FRZ & MS & KS & Y1 & Y2 & Y8 & Y9 & C32).
        exists fx3, R3, M3. split; [exact MG|]. split; [intros i Hi N1 _; apply FRZ; [exact Hi| exact N1]|]. split; [exact MS|].
        split; [intros x Hx; apply KS; exact (sub_in PESENDP.KS_encEOJ1 CSL ltac:(vm_compute; reflexivity) x Hx)|].
        split; [exact Y1|]. split; [exact Y2|]. split; [exact Y8|]. split; [exact Y9|]. split; [| intros e2 rr' H'; discriminate H'].
        replace (eb + 24 * 0) with eb by (clear; Lia.lia). exact C32.
      -
        set (m := Z.of_nat (length rr')) in *.
        assert (HNM : n = m + 1) by (unfold n, m; cbn [length]; rewrite Nat2Z.inj_succ; lia).
        assert (WRtop2 : L5.writable RSEGS M2 (eb + 24 * (n + 1) - 48) 48) by (apply (L5.writable_sub _ M2 eb (24 * PEC.ecap ek) _ _ WRblk2); lia).
        pose proof (EITEMSb (length rr') ltac:(rewrite length_app, length_rev; cbn [length]; lia)) as E2.
        cbn [rev] in E2. rewrite (app_nth1 (rev rr' ++ [e2]) [EI kd ln cn]) in E2 by (rewrite length_app, length_rev; cbn [length]; lia).
        rewrite nth_top in E2. destruct E2 as (_ & _ & U16). unfold PEC.ESZ in U16. fold m in U16.
        destruct e2 as [k2_ l2 c2]. cbn [ei_kind ei_len ei_cnt] in U16 |- *.
        pose proof (Forall_inv RROK) as E2OK. unfold ei_ok in E2OK. cbn [ei_kind ei_len ei_cnt] in E2OK. unfold MAX_ITEMS, TWO64 in E2OK.
        replace (eb + 24 * m + 16) with (eb + 24 * (n + 1) - 32) in U16 by lia.
        assert (POST2 : exists fx3 R3 M3, mem_grows M2 M3
          /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) -> ~ (eb + 24 * (n + 1) - 32 <= i < eb + 24 * (n + 1) - 32 + 8) -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i))
          /\ (msteps RSEGS (@mkst fx2 R2 (Z_to_bv 64 0x35f80) M2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0x35fdc) M3 (seg_rom RSEGS))
          /\ (forall x, In x PESENDP.KS_encEOJ2 -> getr R3 (PMK.reg x) = getr R2 (PMK.reg x))
          /\ getr R3 (PMK.reg 1) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 1)))
          /\ getr R3 (PMK.reg 2) = Z_to_bv 64 sp
          /\ getr R3 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8)))
          /\ getr R3 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9)))
          /\ L5.u64_at RSEGS M3 (eb + 24 * (n + 1) - 32) ((c2 + 1) mod TWO64)
          /\ L5.u64_at RSEGS M3 (fb + 440 + 32) (eb + 24 * (n + 1) - 24))).
        { destruct (Z.eq_dec c2 18446744073709551615) as [CW|CNW].
          + rewrite CW in U16 |- *. change ((18446744073709551615 + 1) mod TWO64) with 0.
            pose proof (PESENDP.encEOJ2w_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 34%nat => eb + 24 * (n + 1)
                | 44%nat => bv_unsigned (getr R (PMK.reg 1)) | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
                | 55%nat => bv_unsigned (getr R2 (PMK.reg 10)) | _ => 0 end)) as P3. cbn beta iota in P3.
            PMK.feed P3 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact EBAL | exact ALend]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                                   | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN HNM; unfold hl_ceil in *; lia) ]).
            post_of P3.
          + pose proof (PESENDP.encEOJ2_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 42%nat => c2
                | 44%nat => bv_unsigned (getr R (PMK.reg 1)) | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
                | 55%nat => bv_unsigned (getr R2 (PMK.reg 10)) | _ => 0 end)) as P3. cbn beta iota in P3.
            PMK.feed P3 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact EBAL | exact ALend]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                                   | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN HNM E2OK CNW; unfold hl_ceil in *; lia) ]).
            rewrite Z.mod_small by (unfold TWO64; lia). post_of P3. }
        destruct POST2 as (fx3 & R3 & M3 & MG & FRZ & MS & KS & Y1 & Y2 & Y8 & Y9 & CCc & C32).
        exists fx3, R3, M3. split; [exact MG|]. split.
        { intros i Hi N1 N2. apply FRZ; [exact Hi| exact N1|]. cbn [cc_rng] in N2. unfold PEC.ESZ in N2. fold m in N2. intros X'. apply N2. lia. }
        split; [exact MS|]. split; [intros x Hx; apply KS; exact (sub_in PESENDP.KS_encEOJ2 CSL ltac:(vm_compute; reflexivity) x Hx)|].
        split; [exact Y1|]. split; [exact Y2|]. split; [exact Y8|]. split; [exact Y9|]. split; [replace (eb + 24 * n) with (eb + 24 * (n + 1) - 24) by lia; exact C32|].
        intros e2 rr'' H'. injection H' as <- <-. cbn [ei_cnt]. unfold PEC.ESZ. fold m. replace (eb + 24 * m + 16) with (eb + 24 * (n + 1) - 32) by lia. exact CCc. }
    PMK.pvz_hg ltac:(idtac; destruct POSTJ as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG3 & FRZ3 & MS3 & KS3 & Y1 & Y2 & Y8 & Y9 & C32c & CC3)); PMK.pvz_clrT.
    set (P3 := fun a => (fb + 440 + 32 <= a < fb + 440 + 32 + 8) \/ cc_rng eb rr a).
    assert (FRZ3' : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ3; [exact Ha| |]; intros X'; apply N; unfold P3; [left| right]; exact X'. }
    assert (CCB : forall a, cc_rng eb rr a -> eb <= a < eb + 24 * n) by (intros a Ha; apply cc_rng_in in Ha; unfold PEC.ESZ in Ha; unfold n; clear - Ha; Lia.lia).
    assert (INeo : In (eb, PEC.ESZ * PEC.ecap ek) (PEC.enc_own en)).
    { unfold PEC.enc_own, en. cbn [PEC.en_k PEC.en_b]. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
    assert (BIN2 : In (eb, PEC.ESZ * PEC.ecap ek) (PESK.sink_own k2 ++ LBY)) by (apply in_or_app; right; apply EINCY; exact INeo).
    apply (PMK.spiece RSEGS L HI KL HIok (PESK.sink_own k2 ++ LBY) cr2 M2 model2 fx2 fx3 R2 0x35f80 R3 0x35fdc M3 P3 K HH2 Mh2 Ml2 ltac:(lia) MS3 MG3 FRZ3').
    { intros a [Pa|Pa]; [apply (PMK.cwr_stack L _ M2 sp 20480 a STK2); clear - Pa SLO SHI F1 F2; Lia.lia|].
      apply (PMK.cwr_block L _ eb (PEC.ESZ * PEC.ecap ek) a BIN2). apply CCB in Pa. unfold PEC.ESZ. clear - Pa ELEN CN. Lia.lia. }
    { intros a. unfold P3. apply PMK.or_dec; [apply PMK.rng_dec| apply cc_rng_dec]. }
    intros HH3.

    set (W3 := [(fb + 440 + 32, 8)] : list L5.range).
    set (LBc3 := PESK.sink_own k2 ++ PM.parser_own s ++ LBX).
    assert (PERM3 : Permutation (PESK.sink_own k2 ++ LBY) (PEC.enc_own en ++ LBc3)) by (unfold LBY, LBc3; apply perm4).
    pose proof (heap_perm _ _ cr2 M3 _ PERM3 HH3) as HH3e.
    assert (BR3 : PMFR.brange L LBc3) by (apply (PMFR.brange_of_heap L HI HIok _ LBc3 cr2 M3 _ HH3e); apply incl_appr; apply incl_refl).
    assert (EK3 : PMK.ek L LBc3 sp 20480 W3 M2 M3).
    { apply (PMK.ek_piece L LBc3 sp 20480 W3 M2 M3 P3 FRZ3'). intros a Ha CA NE OW [Pa|Pa].
      - apply (OW (fb + 440 + 32, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      - refine (own_not_client (PEC.enc_own en) LBc3 cr2 M3 _ eb (PEC.ESZ * PEC.ecap ek) a sp 20480 HH3e INeo _ CA).
        apply CCB in Pa. unfold PEC.ESZ. clear - Pa ELEN CN. Lia.lia. }
    assert (WHI3 : forall a, PMK.inW W3 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
    assert (STK3 : L5C.stk (hl_sptop L) M3 sp 20480) by exact (PMK.stk_grows L M2 M3 sp 20480 MG3 STK2).

    eapply (L5.cps_of_msteps RSEGS); [exact Mh2| exact Ml2| |].
    { apply (PMK.ret_to RSEGS fx3 R3 M3 0x35fdc W_35f84 r F_35f84 eq_refl D_35f84); [rewrite Y1, PMPK.word_id; exact Rra| lia| exact Hr2]. }

    set (Ws := [(fb + 440, 56); (fb + 496, 24)] : list L5.range).
    assert (INC03 : incl LBc0 LBc3) by (unfold LBc0, LBc3; insub).
    assert (EKT : PMK.ek L LBc0 sp 20480 Ws M M3).
    { apply (PMK.ek_trans L LBc0 sp 20480 Ws M M1 M3).
      { apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 Ws W1 M M1 EK1); [exact INC0| intros x Hx; exact Hx|].
        intros a O r0 Hr0 Hin. unfold W1 in Hr0. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
        apply (O (fb + 440, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
      apply (PMK.ek_trans L LBc0 sp 20480 Ws M1 M2 M3).
      { apply (PMK.ek_callee_in' RSEGS L KL LBc0 LBY sp 20480 (sp - 48) 12288 Ws [(fb + 496, 24)] M1 M2 HP2 XINCY);
          [lia|lia| unfold hl_ceil; lia| lia| exact (PMFR.brange_hi L LBc0 BRc0)|].
        intros a I. apply PMFR.inW_inv1 in I. right. apply PMK.inW_next. apply PMK.inW_here. lia. }
      apply (PMK.ek_weaken L LBc0 LBc3 sp 20480 sp 20480 Ws W3 M2 M3 EK3); [exact INC03| intros x Hx; exact Hx|].
      intros a O r0 Hr0 Hin. unfold W3 in Hr0. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      apply (O (fb + 440, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    destruct (KEEPF Ws M3 EKT) as (PA3 & IA3 & VREF3 & BASE3 & CONT3).
    { intros a (r0 & Hin & Hr). unfold Ws in Hin. unfold L5.in_rng in Hr. unfold WEC. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
    destruct (KEEPE Ws M3 EKT) as (ERR3 & ECS3).
    { intros a (r0 & Hin & Hr). unfold Ws in Hin. unfold L5.in_rng in Hr. unfold WOB. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
    assert (SKA3 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M3 (fb + 496) k2).
    { apply (PECF.sink_keep RSEGS L KL LBc3 sp 20480 W3 M2 M3 EK3 STK2 SC0 BR3 WHI3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| unfold LBc3; insub| exact SKA2]. }
    assert (U48c : L5.u32_at RSEGS M3 (fb + 440 + 48) (edepth - 1)).
    { apply (PMF.u32_at_agree RSEGS M2 M3); [|lia|lia| exact EV48b]. intros i Hi. apply FRZ3'; [lia|]. unfold P3. intros [X'|X']; [lia|]. apply CCB in X'.
      clear - X' Hi B4 ELEN CN SLO F1. Lia.lia. }
    assert (EA3 : enc_at M3 (fb + 440) fb (PEC.ENC eb ek (rev (ebump rr)) (edepth - 1))).
    { apply (enc_pop M2 M3 (fb + 440) fb eb ek rr (EI kd ln cn) (edepth - 1) (edepth - 1) EA2); [lia|lia| intros _; unfold PEC.ESZ; lia| | | exact MG3| | exact U48c| unfold MAX_DEPTH; lia| exact CC3].
      - intros i Hi Ri N1 N2. apply FRZ3'; [exact Hi|]. unfold P3. intros [X'|X']; [clear - X' N1; Lia.lia|]. apply CCB in X'. clear - X' Ri B4 ELEN CN SLO F1. Lia.lia.
      - intros _ i Hi Ri Ni. apply FRZ3'; [exact Hi|]. unfold P3. intros [X'|X']; [| exact (Ni X')]. unfold PEC.ESZ in Ri. clear - X' Ri B4 CN SLO F1. Lia.lia.
      - unfold PEC.ESZ. exact C32c. }
    apply (KONT fx3 R3 M3 model2 (PEC.ENC eb ek (rev (ebump rr)) (edepth - 1)) k2 e cr2).
    + apply PMK.preserved_by_index. intros k0 Hk0.
      destruct (Nat.eq_dec k0 2) as [->|N2]; [rewrite Y2; symmetry; exact Rsp|].
      destruct (Nat.eq_dec k0 8) as [->|N8]; [rewrite Y8; apply PMPK.word_id|].
      destruct (Nat.eq_dec k0 9) as [->|N9]; [rewrite Y9; apply PMPK.word_id|].
      assert (IN3 : In k0 CSL /\ In k0 PESENDP.KS_encEOI1) by (cbn in Hk0; decompose [or] Hk0; subst; try (exfalso; congruence); (split; PMK.inl)).
      destruct IN3 as [I3 I1]. rewrite (KS3 k0 I3), (PMK.cs_of_preserved R1 R2 k0 RP2 Hk0), (KS1 k0 I1). reflexivity.
    + unfold PEC.crun_pre. unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PESK.o_sink. cbn [pa_off_p pa_off_is pa_off_v pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S].
      split; [exact PA3|]. split; [exact IA3|]. split; [exact EA3|]. split; [exact VREF3|]. split; [exact SKA3|].
      split; [exact BASE3|]. split; [exact ERR3|]. split; [exact TBOK|]. split; [exact CONT3|].
      split.
      { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PEC.en_stk PEC.en_depth].
        split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
        split; [reflexivity|]. split; [lia|]. split; [|exact Lbad].
        unfold k2, PESK.sk_push. destruct (PESK.sk_z k <? PESK.sk_c k); cbn [PESK.sk_z]; lia. }
      split; [exact ECS3| exact ECI].
    + intros X'; exact X'.
    + apply (PMK.hpres_of L LBc0 sp 20480 _ M M3).
      * apply (PMK.ek_weaken L LBc0 LBc0 sp 20480 sp 20480 _ Ws M M3 EKT); [apply incl_refl| intros x Hx; exact Hx|].
        intros a O r0 Hr0 Hin. unfold PEC.W_enc, PMSP.o_v, PMSP.o_ec, PESK.o_sink in O.
        cbn [pa_off_v pa_off_ec pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S app] in O.
        unfold Ws in Hr0. destruct Hr0 as [<-|[<-|[]]]; [apply (O (fb + 440, 56)); [left; reflexivity| exact Hin] | apply (O (fb + 496, 24)); [right; left; reflexivity| exact Hin]].
      * destruct STK3 as (_ & _ & _ & _ & D3). exact D3.
      * apply (PMK.dk_trans L LBc0 sp 20480 M M1 M3 (PMK.dk_grows L LBc0 sp 20480 M M1 MG1)).
        apply (PMK.dk_trans L LBc0 sp 20480 M1 M2 M3); [| apply (PMK.dk_grows L LBc0 sp 20480 M2 M3 MG3)].
        apply (PMK.dk_callee L LBc0 LBY sp 20480 (sp - 48) 12288 _ M1 M2 HP2 XINCY); lia.
    + unfold PMSP.credit_keep, PEC.pot_enc, PEC.credit_add in CK2 |- *. change (PEC.en_k en) with ek. cbn [fst snd PEC.en_k] in CK2 |- *. clear - CK2. Lia.lia.
    + exact MB2.
    + refine (heap_perm _ _ cr2 M3 _ _ HH3). change (PEC.enc_own (PEC.ENC eb ek (rev (ebump rr)) (edepth - 1))) with (PEC.enc_own en).
      unfold PEC.owned, LBY. rewrite <- !app_assoc. apply Permutation_sym. apply perm4.
  -
    assert (EIND : ei_indef (EI kd ln cn) = false) by (unfold ei_indef; cbn [ei_kind]; destruct KDC as [-> | ->]; reflexivity).
    destruct (Z.eq_dec cn ln) as [CEQ|CNE].
    +
      rewrite (e_end_eq X _ rr HES EIND CEQ) in NB, HB, KONT. cbn [s_bad s_hi] in NB, HB. subst cn.
      assert (WRblk : L5.writable RSEGS M eb (24 * PEC.ecap ek)) by (apply (L5C.writable_of_defined RSEGS); [exact EBDEF|lia|lia]).
      assert (POSTE : exists fx1 R1 M1, mem_grows M M1
        /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) ->
              ~ cc_rng eb rr i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
        /\ (msteps RSEGS (@mkst fx R (Z_to_bv 64 0x35f30) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x35fdc) M1 (seg_rom RSEGS))
        /\ (forall x, In x PESENDP.KS_encEOCe10 -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
        /\ L5.u64_at RSEGS M1 (fb + 440 + 32) (eb + 24 * n)
        /\ L5.u32_at RSEGS M1 (fb + 440 + 48) (edepth - 1)
        /\ (forall e2 rr', rr = e2 :: rr' -> L5.u64_at RSEGS M1 (eb + PEC.ESZ * Z.of_nat (length rr') + 16) ((ei_cnt e2 + 1) mod TWO64)))).
      { destruct rr as [|e2 rr'].
        -
          unfold n in *. cbn [length] in T0, T8, T16, HLEN, ELEN, EV32, ALend |- *. change (Z.of_nat 0) with 0 in *.
          assert (POST1 : exists fx1 R1 M1, mem_grows M M1
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) ->
                  M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
            /\ (msteps RSEGS (@mkst fx R (Z_to_bv 64 0x35f30) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x35fdc) M1 (seg_rom RSEGS))
            /\ (forall x, In x PESENDP.KS_encEOCe10 -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
            /\ L5.u64_at RSEGS M1 (fb + 440 + 32) eb /\ L5.u32_at RSEGS M1 (fb + 440 + 48) (edepth - 1))).
          { destruct KDC as [KD|KD]; subst kd.
            + pose proof (PESENDP.encEOCe10_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 36%nat => edepth | 38%nat => ln | 41%nat => fb + 496 | _ => 0 end)) as P1.
              cbn beta iota in P1. rewrite !HO in P1.
              PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL]) | PMK.sc
                                     | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN; unfold hl_ceil in *; lia) ]).
              post_of P1.
            + pose proof (PESENDP.encEOCe12_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 36%nat => edepth | 38%nat => ln | 41%nat => fb + 496 | _ => 0 end)) as P1.
              cbn beta iota in P1. rewrite !HO in P1.
              PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL]) | PMK.sc
                                     | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN; unfold hl_ceil in *; lia) ]).
              post_of P1. }
          destruct POST1 as (fx1 & R1 & M1 & MG & FRZ & MS & KS & C32 & C48).
          exists fx1, R1, M1. split; [exact MG|]. split; [intros i Hi N1 N2 N3 _; exact (FRZ i Hi N1 N2 N3)|]. split; [exact MS|]. split; [exact KS|].
          split; [replace (eb + 24 * 0) with eb by (clear; Lia.lia); exact C32|]. split; [exact C48| intros e2 rr' H'; discriminate H'].
        -
          set (m := Z.of_nat (length rr')) in *.
          assert (HNM : n = m + 1) by (unfold n, m; cbn [length]; rewrite Nat2Z.inj_succ; lia).
          assert (WRtop : L5.writable RSEGS M (eb + 24 * (n + 1) - 48) 48) by (apply (L5.writable_sub _ M eb (24 * PEC.ecap ek) _ _ WRblk); lia).
          pose proof (EITEMS (length rr') ltac:(rewrite length_app, length_rev; cbn [length]; lia)) as E2.
          cbn [rev] in E2. rewrite (app_nth1 (rev rr' ++ [e2]) [EI kd ln ln]) in E2 by (rewrite length_app, length_rev; cbn [length]; lia).
          rewrite nth_top in E2. destruct E2 as (_ & _ & U16). unfold PEC.ESZ in U16. fold m in U16.
          destruct e2 as [k2_ l2 c2]. cbn [ei_kind ei_len ei_cnt] in U16 |- *.
          pose proof (Forall_inv RROK) as E2OK. unfold ei_ok in E2OK. cbn [ei_kind ei_len ei_cnt] in E2OK. unfold MAX_ITEMS, TWO64 in E2OK.
          replace (eb + 24 * m + 16) with (eb + 24 * (n + 1) - 32) in U16 by lia.
          assert (POST2 : exists fx1 R1 M1, mem_grows M M1
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) ->
                  ~ (eb + 24 * (n + 1) - 32 <= i < eb + 24 * (n + 1) - 32 + 8) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
            /\ (msteps RSEGS (@mkst fx R (Z_to_bv 64 0x35f30) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x35fdc) M1 (seg_rom RSEGS))
            /\ (forall x, In x PESENDP.KS_encEOCe10 -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
            /\ L5.u64_at RSEGS M1 (eb + 24 * (n + 1) - 32) ((c2 + 1) mod TWO64)
            /\ L5.u64_at RSEGS M1 (fb + 440 + 32) (eb + 24 * (n + 1) - 24)
            /\ L5.u32_at RSEGS M1 (fb + 440 + 48) (edepth - 1))).
          { destruct (Z.eq_dec c2 18446744073709551615) as [CW|CNW].
            + rewrite CW in U16 |- *. change ((18446744073709551615 + 1) mod TWO64) with 0.
              destruct KDC as [KD|KD]; subst kd.
              * pose proof (PESENDP.encEOCe20w_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                    | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
                PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                       | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN HNM; unfold hl_ceil in *; lia) ]).
                post_of P1.
              * pose proof (PESENDP.encEOCe22w_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                    | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
                PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                       | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN HNM; unfold hl_ceil in *; lia) ]).
                post_of P1.
            + destruct KDC as [KD|KD]; subst kd.
              * pose proof (PESENDP.encEOCe20_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                    | 41%nat => fb + 496 | 42%nat => c2 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
                PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                       | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN HNM E2OK CNW; unfold hl_ceil in *; lia) ]).
                rewrite Z.mod_small by (unfold TWO64; lia). post_of P1.
              * pose proof (PESENDP.encEOCe22_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                    | 41%nat => fb + 496 | 42%nat => c2 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
                PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                       | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN HNM E2OK CNW; unfold hl_ceil in *; lia) ]).
                rewrite Z.mod_small by (unfold TWO64; lia). post_of P1. }
          destruct POST2 as (fx1 & R1 & M1 & MG & FRZ & MS & KS & CCc & C32 & C48).
          exists fx1, R1, M1. split; [exact MG|]. split.
          { intros i Hi N1 N2 N3 N4. apply FRZ; [exact Hi| exact N1| exact N2| exact N3|]. cbn [cc_rng] in N4. unfold PEC.ESZ in N4. fold m in N4. intros X'. apply N4. lia. }
          split; [exact MS|]. split; [exact KS|]. split; [replace (eb + 24 * n) with (eb + 24 * (n + 1) - 24) by lia; exact C32|]. split; [exact C48|].
          intros e2 rr'' H'. injection H' as <- <-. cbn [ei_cnt]. unfold PEC.ESZ. fold m. replace (eb + 24 * m + 16) with (eb + 24 * (n + 1) - 32) by lia. exact CCc. }
      PMK.pvz_hg ltac:(idtac; destruct POSTE as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                       destruct pvzP as (MG1 & FRZ1 & MS1 & KS1 & C32c & C48c & CC1)); PMK.pvz_clrT.
      set (P1 := fun a => (sp - 48 <= a < sp - 48 + 48) \/ (fb + 440 + 48 <= a < fb + 440 + 48 + 4) \/ (fb + 440 + 32 <= a < fb + 440 + 32 + 8) \/ cc_rng eb rr a).
      assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha N. apply FRZ1; [exact Ha| | | |]; intros X'; apply N; unfold P1; [left| right; left| right; right; left| right; right; right]; exact X'. }
      assert (CCB : forall a, cc_rng eb rr a -> eb <= a < eb + 24 * n) by (intros a Ha; apply cc_rng_in in Ha; unfold PEC.ESZ in Ha; unfold n; clear - Ha; Lia.lia).
      assert (INeo : In (eb, PEC.ESZ * PEC.ecap ek) (PEC.enc_own en)).
      { unfold PEC.enc_own, en. cbn [PEC.en_k PEC.en_b]. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x35f30 R1 0x35fdc M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
      { intros a [Pa|[Pa|[Pa|Pa]]]; [apply (PMK.cwr_stack L LB M sp 20480 a STK); clear - Pa SLO SHI F1 F2; Lia.lia
          | apply (PMK.cwr_stack L LB M sp 20480 a STK); clear - Pa SLO SHI F1 F2; Lia.lia | apply (PMK.cwr_stack L LB M sp 20480 a STK); clear - Pa SLO SHI F1 F2; Lia.lia |].
        apply (PMK.cwr_block L _ eb (PEC.ESZ * PEC.ecap ek) a BIN). apply CCB in Pa. unfold PEC.ESZ. clear - Pa ELEN CN. Lia.lia. }
      { intros a. unfold P1. repeat (apply PMK.or_dec; [apply PMK.rng_dec|]). apply cc_rng_dec. }
      intros HH1.
      set (WsE := [(fb + 440, 56)] : list L5.range).
      set (LBcE := PESK.sink_own k ++ PM.parser_own s ++ LBX).
      assert (PERME : Permutation LB (PEC.enc_own en ++ LBcE)) by (unfold LB, LBcE, PEC.owned; rewrite <- !app_assoc; apply Permutation_sym; apply perm4).
      pose proof (heap_perm _ _ cr M1 _ PERME HH1) as HH1e.
      assert (BRE : PMFR.brange L LBcE) by (apply (PMFR.brange_of_heap L HI HIok _ LBcE cr M1 _ HH1e); apply incl_appr; apply incl_refl).
      assert (EK1 : PMK.ek L LBcE sp 20480 WsE M M1).
      { apply (ek_piece_own (PEC.enc_own en) LBcE cr M1 _ sp 20480 WsE M M1 P1 eb (PEC.ESZ * PEC.ecap ek) HH1e INeo FRZ1' ltac:(unfold hl_ceil; lia) ltac:(lia)).
        intros a [Pa|[Pa|[Pa|Pa]]]; [left; lia| right; left; apply PMK.inW_here; lia| right; left; apply PMK.inW_here; lia|].
        right. right. apply CCB in Pa. unfold PEC.ESZ. clear - Pa ELEN CN. Lia.lia. }
      assert (WHIE : forall a, PMK.inW WsE a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
      assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by exact (PMK.stk_grows L M M1 sp 20480 MG1 STK).

      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
      { apply (PMK.ret_to RSEGS fx1 R1 M1 0x35fdc W_35f84 r F_35f84 eq_refl D_35f84); [rewrite (KS1 1%nat) by PMK.inl; exact Rra| lia| exact Hr2]. }

      assert (INC0E : incl LBc0 LBcE) by (unfold LBc0, LBcE; insub).
      assert (EKT : PMK.ek L LBc0 sp 20480 WsE M M1).
      { apply (PMK.ek_weaken L LBc0 LBcE sp 20480 sp 20480 WsE WsE M M1 EK1); [exact INC0E| intros x Hx; exact Hx| intros a O; exact O]. }
      destruct (KEEPF WsE M1 EKT) as (PA1 & IA1 & VREF1 & BASE1 & CONT1).
      { intros a I. apply PMFR.inW_inv1 in I. unfold WEC. lia. }
      destruct (KEEPE WsE M1 EKT) as (ERR1 & ECS1).
      { intros a I. apply PMFR.inW_inv1 in I. unfold WOB. lia. }
      assert (SKA1 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M1 (fb + 496) k).
      { apply (PECF.sink_keep RSEGS L KL LBcE sp 20480 WsE M M1 EK1 STK SC0 BRE WHIE); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| unfold LBcE; insub| exact SKA]. }
      assert (EA1 : enc_at M1 (fb + 440) fb (PEC.ENC eb ek (rev (ebump rr)) (edepth - 1))).
      { apply (enc_pop M M1 (fb + 440) fb eb ek rr (EI kd ln ln) edepth (edepth - 1) EA); [lia|lia| intros _; unfold PEC.ESZ; lia| | | exact MG1| | exact C48c| unfold MAX_DEPTH; lia| exact CC1].
        - intros i Hi Ri N1 N2. apply FRZ1'; [exact Hi|]. unfold P1. intros [X'|[X'|[X'|X']]]; [clear - X' Ri F1; Lia.lia| apply N2; clear - X'; Lia.lia| apply N1; clear - X'; Lia.lia|].
          apply CCB in X'. clear - X' Ri B4 ELEN CN SLO F1. Lia.lia.
        - intros _ i Hi Ri Ni. apply FRZ1'; [exact Hi|]. unfold P1. unfold PEC.ESZ in Ri. intros [X'|[X'|[X'|X']]]; [clear - X' Ri B4 CN SLO; Lia.lia| clear - X' Ri B4 CN SLO F1; Lia.lia| clear - X' Ri B4 CN SLO F1; Lia.lia| exact (Ni X')].
        - unfold PEC.ESZ. exact C32c. }
      apply (KONT fx1 R1 M1 model (PEC.ENC eb ek (rev (ebump rr)) (edepth - 1)) k e cr).
      * apply PMK.preserved_by_index. intros k0 Hk0. apply KS1. exact (sub_in PESENDP.KS_encEOCe10 PMK.cs_all ltac:(vm_compute; reflexivity) k0 Hk0).
      * unfold PEC.crun_pre. unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PESK.o_sink. cbn [pa_off_p pa_off_is pa_off_v pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S].
        split; [exact PA1|]. split; [exact IA1|]. split; [exact EA1|]. split; [exact VREF1|]. split; [exact SKA1|].
        split; [exact BASE1|]. split; [exact ERR1|]. split; [exact TBOK|]. split; [exact CONT1|].
        split.
        { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PEC.en_stk PEC.en_depth].
          split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
          split; [reflexivity|]. split; [lia|]. split; [exact Lz| exact Lbad]. }
        split; [exact ECS1| exact ECI].
      * intros X'; exact X'.
      * apply (PMK.hpres_of L LBc0 sp 20480 _ M M1).
        -- apply (PMK.ek_weaken L LBc0 LBc0 sp 20480 sp 20480 _ WsE M M1 EKT); [apply incl_refl| intros x Hx; exact Hx|].
           intros a O r0 Hr0 Hin. unfold PEC.W_enc, PMSP.o_v, PMSP.o_ec, PESK.o_sink in O.
           cbn [pa_off_v pa_off_ec pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S app] in O.
           unfold WsE in Hr0. destruct Hr0 as [<-|[]]. apply (O (fb + 440, 56)); [left; reflexivity| exact Hin].
        -- destruct STK1 as (_ & _ & _ & _ & D1). exact D1.
        -- apply (PMK.dk_grows L LBc0 sp 20480 M M1 MG1).
      * unfold PMSP.credit_keep, PEC.pot_enc, PEC.credit_add. change (PEC.en_k en) with ek. cbn [fst snd PEC.en_k]. clear. Lia.lia.
      * apply L5C.model_but_vm_refl.
      * change (PEC.enc_own (PEC.ENC eb ek (rev (ebump rr)) (edepth - 1))) with (PEC.enc_own en). exact HH1.
    +
      assert (EEND : e_end X = ST (s_stk X) (s_pos X) (s_more X) (s_done X) (s_halt X) (s_depth X) true (s_estk X) (s_edepth X - 1) (s_lo X) (s_hi X) (s_bad X)).
      { destruct (Z_lt_le_dec cn ln) as [LT|GE]; [exact (e_end_lt X _ rr HES EIND LT)| apply (e_end_gt X _ rr HES EIND); cbn [ei_len ei_cnt]; lia]. }
      rewrite EEND in NB, HB, KONT. cbn [s_bad s_hi] in NB, HB. rewrite HES in KONT.

      assert (POSTC : exists fx1 R1 M1 (v : Z), mem_grows M M1
        /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
        /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 0x35f30) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x36f18) M1 (seg_rom RSEGS))
        /\ (forall x, In x PESENDP.KS_encEOI1 -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
        /\ getr R1 (PMK.reg 1) = Z_to_bv 64 221128
        /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 48)
        /\ getr R1 (PMK.reg 8) = getr R (PMK.reg 10)
        /\ getr R1 (PMK.reg 10) = getr R (PMK.reg 12)
        /\ getr R1 (PMK.reg 11) = Z_to_bv 64 v /\ 1 <= v <= 64
        /\ L5.u32_at RSEGS M1 (fb + 440 + 48) (edepth - 1)
        /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))
        /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
        /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))).
      { destruct (Z_lt_le_dec cn ln) as [LT|GE].
        -
          destruct KDC as [KD|KD]; subst kd.
          + pose proof (PESENDP.encEOClt0_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                | 39%nat => cn | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
            PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                   | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN E0OK LT; unfold hl_ceil in *; lia) ]).
            post_of_v P1 9.
          + pose proof (PESENDP.encEOClt2_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                | 39%nat => cn | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
            PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                   | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN E0OK LT; unfold hl_ceil in *; lia) ]).
            post_of_v P1 9.
        - destruct (Z_lt_le_dec cn 18446744073692774400) as [LOW|HIGH].
          +
            destruct KDC as [KD|KD]; subst kd.
            * pose proof (PESENDP.encEOCgt0_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                  | 41%nat => fb + 496 | 43%nat => cn - ln | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
              PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                     | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN E0OK GE CNE LOW; unfold hl_ceil in *; lia) ]).
              post_of_v P1 8.
            * pose proof (PESENDP.encEOCgt2_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                  | 41%nat => fb + 496 | 43%nat => cn - ln | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
              PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                     | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN E0OK GE CNE LOW; unfold hl_ceil in *; lia) ]).
              post_of_v P1 8.
          +
            destruct KDC as [KD|KD]; subst kd.
            * pose proof (PESENDP.encEOCgth0_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                  | 39%nat => cn | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
              PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                     | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN E0OK GE HIGH; unfold hl_ceil in *; lia) ]).
              post_of_v P1 8.
            * pose proof (PESENDP.encEOCgth2_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => eb | 34%nat => eb + 24 * (n + 1) | 36%nat => edepth | 38%nat => ln
                  | 39%nat => cn | 41%nat => fb + 496 | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
              PMK.feed P1 ltac:(first [(unfold PESENDP.aligned; first [exact A16 | exact ALov | exact ALsk | exact EBAL | exact ALend]) | PMK.sc
                                     | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ECAPB CN E0OK GE HIGH; unfold hl_ceil in *; lia) ]).
              post_of_v P1 8. }
      PMK.pvz_hg ltac:(idtac; destruct POSTC as (fx1 & R1 & M1 & v & pvzP); PMK.pvz_lin pvzP;
                       destruct pvzP as (MG1 & FRZ1 & MS1 & KS1 & X1_1 & X2_1 & X8_1 & X10_1 & X11_1 & HV & C48 & S24 & S16 & S8)); PMK.pvz_clrT.
      rewrite A10 in X8_1. rewrite A12 in X10_1.
      set (P1 := fun a => (sp - 48 <= a < sp - 48 + 48) \/ (fb + 440 + 48 <= a < fb + 440 + 48 + 4)).
      assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha N. apply FRZ1; [exact Ha| |]; intros X'; apply N; unfold P1; [left| right]; exact X'. }
      apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x35f30 R1 0x36f18 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
      { intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P1 in Pa. clear - Pa SLO SHI F1 F2. Lia.lia. }
      { intros a. unfold P1. apply PMK.or_dec; apply PMK.rng_dec. }
      intros HH1.
      set (W1 := [(fb + 440 + 48, 4)] : list L5.range).
      assert (WHI1 : forall a, PMK.inW W1 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
      assert (NW1 : forall i, ~ (fb + 440 + 48 <= i < fb + 440 + 52) -> ~ PMK.inW W1 i) by (intros i Hi I; apply PMFR.inW_inv1 in I; lia).
      assert (EK1 : PMK.ek L LB sp 20480 W1 M M1).
      { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W1 M M1 P1 FRZ1' STK (PMFR.brange_hi L LB BR)).
        intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
      assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by exact (PMK.stk_grows L M M1 sp 20480 MG1 STK).
      assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 48) 14336).
      { apply (PMK.stk_call L M1 sp 20480 (sp - 48) 14336 STK1); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
      assert (EKT1 : PMK.ek L LBc0 sp 20480 W1 M M1) by (apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 W1 W1 M M1 EK1); [exact INC0| intros x Hx; exact Hx| intros a O; exact O]).
      destruct (KEEPF W1 M1 EKT1) as (_ & _ & _ & BASE1 & _). { intros a I. apply PMFR.inW_inv1 in I. unfold WEC. lia. }
      destruct (KEEPE W1 M1 EKT1) as (ERR1 & _). { intros a I. apply PMFR.inW_inv1 in I. unfold WOB. lia. }
      assert (ECD : L5.defined M (fb + 16) 16).
      { unfold PEC.ec_state, PMSP.o_ec in ECS. cbn [pa_off_ec CAD PeCLayoutS.CADDR_S] in ECS.
        destruct (s_ec X); [destruct ECS as (v0 & _ & (_ & _ & D0)); exact D0| destruct ECS as (_ & _ & D0); exact D0]. }
      assert (SKA1 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M1 (fb + 496) k).
      { apply (PECF.sink_keep RSEGS L KL LB sp 20480 W1 M M1 EK1 STK SC0 BR WHI1); [lia|lia| intros i' Hi'; apply NW1; lia| exact KINC| exact SKA]. }
      assert (EA1 : enc_at M1 (fb + 440) fb (PEC.ENC eb ek (rev rr ++ [EI kd ln cn]) (edepth - 1))).
      { apply (enc_depth M M1 (fb + 440) fb eb ek _ edepth (edepth - 1) EA); [lia|lia| intros _; unfold PEC.ESZ; lia| | | exact MG1| exact C48| unfold MAX_DEPTH; lia].
        - intros i Hi Ri Ni. apply FRZ1'; [exact Hi|]. unfold P1. clear - Ri Ni F1. Lia.lia.
        - intros _ i Hi Ri. apply FRZ1'; [exact Hi|]. unfold P1, PEC.ESZ in *. clear - Ri B4 SLO F1 SHI STOP. lia. }

      pose proof MKEC as MKX. unfold PECSS.make_ec_spec, PECS.make_ec_spec in MKX. cbn [pa_make_ec PECSS.AD PeCLayoutS.CADDR_S] in MKX.
      apply (MKX fx1 R1 M1 model K LB cr (fb + 16) v (sp - 48) 221128 e HH1 MOK K0); clear MKX.
      { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1_1|]. split; [clear; unfold L5.ra_ok; Lia.lia|]. split; [exact X2_1|].
        split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
      { rewrite L5K.rl10. exact X10_1. }
      { rewrite L5K.rl11. exact X11_1. }
      { exact HV. } { lia. } { lia. } { exact ALec. }
      { exact (L5.defined_grows M M1 _ _ MG1 ECD). }
      { exact BASE1. }
      { exact ERR1. }
      intros fx2 R2 M2 RP2 EC2 ERR2 HP2 HH2.
      change (PMSP.pm_scr 1) with 14336 in HP2.
      set (W2 := (fb + 16, 16) :: (if e then [] else PMSP.err_W CAD)) in HP2.
      assert (WC2 : forall a, PMK.inW W2 a -> (fb + 16 <= a < fb + 16 + 16) \/ (0xc9640 <= a < 0xc9640 + 2) \/ (0xeb088 <= a < 0xeb088 + 544)).
      { intros a (r0 & Hin & Hr). unfold W2 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|].
        destruct e; [destruct Hin|]. unfold PMSP.err_W in Hin. cbn [pa_errcat_guard pa_atexit CAD PeCLayoutS.CADDR_S] in Hin.
        destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
      pose proof (PMK.stk_after RSEGS L KL LB M1 M2 sp 20480 (sp - 48) 14336 _ STK1 HP2 ltac:(lia) ltac:(lia) ltac:(lia)) as STK2.
      pose proof (L5C.stk_writable RSEGS _ M2 sp 20480 STK2) as WR2.
      pose proof (PMK.ek_of_hpres L LB (sp - 48) 14336 W2 M1 M2 HP2) as EK2.
      assert (SC2 : 0 <= 14336) by lia.
      assert (WHI2 : forall a, PMK.inW W2 a -> sp - 48 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WC2 in I; rewrite IMLO, IMHI; clear - I F1; Lia.lia).
      assert (NW2 : forall i, (sp - 48 <= i < fb + 16 \/ fb + 16 + 16 <= i <= 2 ^ 64) -> ~ PMK.inW W2 i) by (intros i Hi I; apply WC2 in I; clear - Hi I IMLO IMHI F1 F2 STOP SLO; Lia.lia).
      assert (S24b : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))).
      { apply (PMFR.u64_keep RSEGS L KL LB (sp - 48) 14336 _ M1 M2 EK2 STKc SC2); [lia|lia| intros i Hi; apply NW2; lia| exact S24]. }
      assert (S16b : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))).
      { apply (PMFR.u64_keep RSEGS L KL LB (sp - 48) 14336 _ M1 M2 EK2 STKc SC2); [lia|lia| intros i Hi; apply NW2; lia| exact S16]. }
      assert (S8b : L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))).
      { apply (PMFR.u64_keep RSEGS L KL LB (sp - 48) 14336 _ M1 M2 EK2 STKc SC2); [lia|lia| intros i Hi; apply NW2; lia| exact S8]. }
      pose proof (bv_unsigned_in_range 64 (getr R2 (PMK.reg 10))) as RBj. change (bv_modulus 64) with (2 ^ 64) in RBj.

      pose proof (PESENDP.encEOR_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 10%nat => fb + 440
          | 44%nat => bv_unsigned (getr R (PMK.reg 1)) | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
          | 55%nat => bv_unsigned (getr R2 (PMK.reg 10)) | _ => 0 end)) as P3. cbn beta iota in P3.
      PMK.feed P3 ltac:(first [(unfold PESENDP.aligned; exact A16) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                             | (clear - SLO STOP SHI F1 F2; unfold hl_ceil in *; lia) ]).
      destruct P3 as (fx3 & R3 & M3 & _ & FRW3 & _ & MS3 & KS3 & Y1 & Y2 & Y8 & Y9 & Y10).
      assert (EM : M3 = M2) by (apply functional_extensionality; exact FRW3). subst M3.
      apply (PMK.spiece_ro RSEGS model fx2 fx3 R2 221128 R3 0x35fdc M2 K Mh Ml MS3).
      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
      { apply (PMK.ret_to RSEGS fx3 R3 M2 0x35fdc W_35f84 r F_35f84 eq_refl D_35f84); [rewrite Y1, PMPK.word_id; exact Rra| lia| exact Hr2]. }

      assert (EKT : PMK.ek L LBc0 sp 20480 (PEC.W_enc CAD EE fb) M M2).
      { apply (PMK.ek_trans L LBc0 sp 20480 _ M M1 M2).
        { apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 _ W1 M M1 EK1); [exact INC0| intros x Hx; exact Hx|].
          intros a O r0 Hr0 Hin. unfold W1 in Hr0. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
          unfold PEC.W_enc, PMSP.o_v in O. cbn [pa_off_v CAD PeCLayoutS.CADDR_S app] in O.
          apply (O (fb + 440, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
        apply (PMK.ek_callee_in' RSEGS L KL LBc0 LB sp 20480 (sp - 48) 14336 _ W2 M1 M2 HP2 INC0);
          [lia|lia| unfold hl_ceil; lia| lia| exact (PMFR.brange_hi L LBc0 BRc0)|].
        intros a I. apply WC2 in I. right. unfold PEC.W_enc, PMSP.err_W, PMSP.o_v, PMSP.o_ec, PESK.o_sink.
        cbn [pa_off_v pa_off_ec pe_off_sink pa_errcat_guard pa_atexit CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S app].
        destruct I as [I|[I|I]]; [do 2 apply PMK.inW_next; apply PMK.inW_here; lia| do 3 apply PMK.inW_next; apply PMK.inW_here; lia| do 4 apply PMK.inW_next; apply PMK.inW_here; lia]. }
      destruct (KEEPF _ M2 EKT WCE) as (PA2 & IA2 & VREF2 & BASE2 & CONT2).
      assert (SKA2 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M2 (fb + 496) k).
      { apply (PECF.sink_keep RSEGS L KL LB (sp - 48) 14336 W2 M1 M2 EK2 STKc SC2 (PMFR.brange_incl L LB LB BR ltac:(apply incl_refl)) WHI2); [lia|lia| intros i Hi; apply NW2; lia| exact KINC| exact SKA1]. }
      assert (EA2 : enc_at M2 (fb + 440) fb (PEC.ENC eb ek (rev rr ++ [EI kd ln cn]) (edepth - 1))).
      { apply (PECF.enc_keep RSEGS EE L KL LB (sp - 48) 14336 W2 M1 M2 EK2 STKc SC2 BR WHI2); [lia|lia| intros i Hi; apply NW2; lia| exact EINC| exact EA1]. }
      apply (KONT fx3 R3 M2 model (PEC.ENC eb ek (rev rr ++ [EI kd ln cn]) (edepth - 1)) k true cr).
      * apply PMK.preserved_by_index. intros k0 Hk0.
        destruct (Nat.eq_dec k0 2) as [->|N2]; [rewrite Y2; symmetry; exact Rsp|].
        destruct (Nat.eq_dec k0 8) as [->|N8]; [rewrite Y8; apply PMPK.word_id|].
        destruct (Nat.eq_dec k0 9) as [->|N9]; [rewrite Y9; apply PMPK.word_id|].
        assert (IN3 : In k0 PESENDP.KS_encEOR /\ In k0 PESENDP.KS_encEOI1) by (cbn in Hk0; decompose [or] Hk0; subst; try (exfalso; congruence); (split; PMK.inl)).
        destruct IN3 as [I3 I1]. rewrite (KS3 k0 I3), (PMK.cs_of_preserved R1 R2 k0 RP2 Hk0), (KS1 k0 I1). reflexivity.
      * unfold PEC.crun_pre. unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PESK.o_sink. cbn [pa_off_p pa_off_is pa_off_v pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S].
        split; [exact PA2|]. split; [exact IA2|]. split; [exact EA2|]. split; [exact VREF2|]. split; [exact SKA2|].
        split; [exact BASE2|]. split; [exact ERR2|]. split; [exact TBOK|]. split; [exact CONT2|].
        split.
        { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PEC.en_stk PEC.en_depth rev].
          split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
          split; [reflexivity|]. split; [lia|]. split; [exact Lz| exact Lbad]. }
        split; [| intros _; reflexivity].
        unfold PEC.ec_state, PMSP.o_ec. cbn [pa_off_ec CAD PeCLayoutS.CADDR_S]. exists v. split; [exact HV| exact EC2].
      * intros _; reflexivity.
      * apply (PMK.hpres_of L LBc0 sp 20480 _ M M2); [exact EKT| destruct STK2 as (_ & _ & _ & _ & D2); exact D2|].
        apply (PMK.dk_trans L LBc0 sp 20480 M M1 M2 (PMK.dk_grows L LBc0 sp 20480 M M1 MG1)).
        apply (PMK.dk_callee L LBc0 LB sp 20480 (sp - 48) 14336 _ M1 M2 HP2 INC0); lia.
      * unfold PMSP.credit_keep, PEC.pot_enc, PEC.credit_add. change (PEC.en_k en) with ek. cbn [fst snd PEC.en_k]. clear. Lia.lia.
      * apply L5C.model_but_vm_refl.
      * change (PEC.enc_own (PEC.ENC eb ek (rev rr ++ [EI kd ln cn]) (edepth - 1))) with (PEC.enc_own en). exact HH2.
Qed.

End WithHeap.
End PESENC.
