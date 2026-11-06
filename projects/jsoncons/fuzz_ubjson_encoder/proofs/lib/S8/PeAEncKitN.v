(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceA LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5CoreSpecsAS8 L5StepARS8 L5CoreBRS8 L5ADetailHRS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PnStatics PmModelFactsA PmStep PeStepA PmParStep PmParKit PeASrcKit PeAParKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeShZ PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrameA PeEncKit PeACReset1 PmAUarK PmAUar PeAEncNtbSpec PeASnkAnn PeAEstkAnn PeSEncEnd.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEAEKN.
#[local] Transparent e_end_value.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)).

Abbreviation SBL := 2147450880.
Abbreviation SM1 := 0x5e588.
Abbreviation PBPC := 0xaf02c.
Abbreviation MKPC := 0xae310.
Abbreviation SHRPC := 0xaeb80.

Fixpoint owns (js : list nat) (E : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  match js with
  | [] => True
  | j :: js' => L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R (reg j))) /\ owns js' (E - 8) R M
  end.
Definition ocell (E n : Z) (a : Z) : Prop := E - 8 * n <= a < E.
Lemma owns_agree js : forall E R M1 M1', 0 <= E - 8 * Z.of_nat (length js) -> E <= 2 ^ 64 ->
  owns js E R M1 -> (forall a, ocell E (Z.of_nat (length js)) a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> owns js E R M1'.
Proof.
  induction js as [|j js IH]; intros E R M1 M1' H0 H1 OW AG; [exact I|]. cbn [owns length] in *. rewrite Nat2Z.inj_succ in H0, AG.
  destruct OW as [C1 OW]. split.
  - eapply L5C.u64_at_agree; [| | | exact C1]; [intros i Hi; apply AG; unfold ocell; lia| lia| lia].
  - apply (IH (E - 8) R M1 M1'); [lia| lia| exact OW|]. intros a Ha. apply AG. unfold ocell in Ha |- *. lia.
Qed.

Fixpoint rest (js : list nat) (R0 R' : bvmap 5 word) : Prop :=
  match js with
  | [] => True
  | j :: js' => getr R' (reg j) = getr R0 (reg j) /\ rest js' R0 R'
  end.
Lemma rest_in js R0 R' j : rest js R0 R' -> In j js -> getr R' (reg j) = getr R0 (reg j).
Proof. induction js as [|i js IH]; intros RS Hj; [destruct Hj|]. destruct RS as [E RS]. destruct Hj as [<-|Hj]; [exact E| exact (IH RS Hj)]. Qed.

Definition SV9 : list nat := [1; 8; 9; 18; 19; 20; 21; 22; 23]%nat.
Definition SV11 : list nat := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%nat.
Definition SV13 : list nat := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma wid (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma wrng (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.
Lemma byte_at_of_u8 (M : word -> option byte) a : L5.u8_at RSEGS M a 0 -> M (Z_to_bv 64 a) <> None -> byte_at M a 0.
Proof.
  intros U D. unfold L5.u8_at in U. cbn [rdn] in U. unfold byte_at. destruct (M (Z_to_bv 64 a)) as [b|]; [|congruence].
  cbn in U. congruence.
Qed.
Lemma u8_at_of_defined (M : word -> option byte) a : 0 <= a < 2 ^ 64 -> M (Z_to_bv 64 a) <> None -> exists b, 0 <= b <= 255 /\ L5.u8_at RSEGS M a b.
Proof.
  intros Ha D. destruct (M (Z_to_bv 64 a)) as [bb|] eqn:E; [|congruence]. exists (bv_unsigned bb).
  pose proof (bv_unsigned_in_range 8 bb) as NB. change (bv_modulus 8) with 256 in NB. split; [lia|].
  unfold L5.u8_at. cbn [rdn]. rewrite E. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma enc_eta (e0 : PEC.enc) : e0 = PEC.ENC (PEC.en_b e0) (PEC.en_k e0) (PEC.en_stk e0) (PEC.en_depth e0).
Proof. destruct e0; reflexivity. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMA.ly_as0 L C LY.

Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.
Hypothesis MKEC : PECSA.make_ec_spec L ar HI.
Hypothesis ESHR : PEAEKAN.ann_shrink_e_spec RSEGS AD L ar HI SHRPC.

Lemma ri_perm l1 l2 FF LK cr Aw M V : Permutation l1 l2 -> ri_inv HI l1 FF LK cr Aw M V -> ri_inv HI l2 FF LK cr Aw M V.
Proof.
  intros PERM HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
  apply (HAJ.aior_perm _ _ _ _ _ HIok _ l2 FF FF LK cr Aw M V HH).
  - intros b. split; apply Permutation_in; [exact PERM| apply Permutation_sym; exact PERM].
  - apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_map fst PERM)). apply NoDup_ListNoDup. exact ND.
  - intros f. tauto.
  - rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.

Lemma content_keepA' LB FF sp scr W M M' fb p s str sm op :
  L5SAR.ek L ar LB FF sp scr W M M' -> PMKA.wapp W ->
  (forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  PMSPA.aobjA FF (PMSPA.o_is AD fb) 272 -> (forall i, PMSPA.o_is AD fb + 80 <= i < PMSPA.o_is AD fb + 80 + 24 -> L5.outside W i) ->
  incl (PM.vs_own str) LB -> In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB ->
  (forall q m, In (q, m) LB -> PMKA.blk_out W q m) ->
  PM.iss_at RSEGS AD PMSPA.accA M (PMSPA.o_is AD fb) str sm -> PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M op (PMSPA.o_is AD fb) s ->
  PEC.content_ok RSEGS AD M fb p (PM.p_src s) str sm -> PEC.content_ok RSEGS AD M' fb p (PM.p_src s) str sm.
Proof.
  intros EK WAPP FRB BRB AO OW INCS QIN OB IA PA.
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). pose proof VS as (_ & _ & VSF).
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _). pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
  apply (PECFA.content_keepA RSEGS AD L ar LB FF sp scr W M M' EK WAPP FRB BRB fb p s str sm AO OW INCS).
  - intros c n q ->. cbn in VSF. destruct VSF as (_ & _ & _ & Hn & Hc & _ & _ & _). split; [lia|]. apply OB. apply INCS. cbn. left. reflexivity.
  - intros n ->. cbn in VSF. lia.
  - exact QIN.
  - apply OB. exact QIN.
  - exact G1.
  - exact G2.
  - exact G3.
Qed.

Lemma enc_bumpA (M M' : word -> option byte) ov fb eb ek rr d :
  PECA.enc_atA RSEGS EE L ar M ov fb (PEC.ENC eb ek (rev rr) d) ->
  0 <= ov -> ov + 56 <= 2 ^ 64 -> (0 < ek -> 0 <= eb /\ eb + PEC.ESZ * PEC.ecap ek <= 2 ^ 64) ->
  PMFA.agA M M' ov 56 ->
  (0 < ek -> forall i, 0 <= i < 2 ^ 64 -> eb <= i < eb + PEC.ESZ * PEC.ecap ek -> ~ PEEK.cc_rng eb rr i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (0 < ek -> PMFA.agsh M M' eb (PEC.ESZ * PEC.ecap ek)) ->
  mem_grows M M' ->
  (forall e2 rr', rr = e2 :: rr' -> L5.u64_at RSEGS M' (eb + PEC.ESZ * Z.of_nat (length rr') + 16) ((ei_cnt e2 + 1) mod TWO64)) ->
  PECA.enc_atA RSEGS EE L ar M' ov fb (PEC.ENC eb ek (rev (PEEK.ebump rr)) d).
Proof.
  intros EA Ho Ho' BB [AGO SHO] AGB SHB MG UCC. unfold PECA.enc_atA in EA |- *. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EA |- *.
  destruct EA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & CC & Hk & Hlen & Hd & Hk0 & HB & HIT). pose proof (PEC.ecap_nonneg ek) as CN.
  rewrite length_rev in Hlen, HB, HIT, V32.
  assert (LEN' : length (rev (PEEK.ebump rr)) = length rr) by (rewrite length_rev; apply PEEK.ebump_length).
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 56 -> L5C.agree_on M M' a n) by (intros a n X1 X2 i Hi; apply AGO; lia).
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [rewrite LEN'; apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V32]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V40]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V48]|].
  split; [exact (L5.defined_grows M M' _ _ MG D)|]. split; [exact (PMFA.accA_agree M M' ov 56 SHO CC)|].
  split; [exact Hk|]. split; [rewrite LEN'; lia|]. split; [exact Hd|]. split; [exact Hk0|]. split.
  - intros Hp. destruct (HB Hp) as (AL & DB & BR & ACCB & ANB). destruct (BB Hp) as (B0 & B1). pose proof (SHB Hp) as SB'.
    split; [exact AL|]. split; [exact (L5.defined_grows M M' _ _ MG DB)|]. split; [exact BR|]. rewrite LEN'. split.
    + apply (PMFA.accA_agree M M'); [| exact ACCB]. intros x Hx. apply SB'. unfold PEC.ESZ in *. nia.
    + apply (PECFA.annA_agree M M'); [unfold PEC.ESZ in *; nia| exact AL| exact SB'| exact ANB].
  - rewrite LEN'. intros i Hi.
    assert (Hp : 0 < ek).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in Hlen. rewrite Z0 in Hlen. cbn in Hlen. lia. }
    destruct (BB Hp) as (B0 & B1).
    destruct rr as [|e2 rr']; [cbn in Hi; lia|]. cbn [PEEK.ebump rev]. cbn [length rev] in Hi, Hlen, HB, HIT.
    destruct (Nat.lt_ge_cases i (length rr')) as [LT|GE].
    + rewrite app_nth1 by (rewrite length_rev; exact LT). specialize (HIT i ltac:(lia)). rewrite app_nth1 in HIT by (rewrite length_rev; exact LT).
      apply (PECF.eitem_at_agree RSEGS M M'); [| unfold PEC.ESZ in *; lia | unfold PEC.ESZ in *; lia | exact HIT].
      intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [PEEK.cc_rng]. unfold PEC.ESZ in *. lia.
    + assert (EI_ : i = length rr') by lia. subst i. rewrite PEEK.nth_top. specialize (HIT (length rr') ltac:(lia)). rewrite PEEK.nth_top in HIT.
      destruct HIT as (K0c & K8c & _). split; [|split].
      * cbn [ei_kind]. apply (PMF.u32_at_agree RSEGS M M'); [| unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia| exact K0c].
        intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [PEEK.cc_rng]. unfold PEC.ESZ in *. lia.
      * cbn [ei_len]. apply (L5C.u64_at_agree RSEGS M M'); [| unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia| exact K8c].
        intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [PEEK.cc_rng]. unfold PEC.ESZ in *. lia.
      * cbn [ei_cnt]. exact (UCC e2 rr' eq_refl).
Qed.

Lemma enc_depthA (M M' : word -> option byte) ov fb eb ek stk d d' :
  PECA.enc_atA RSEGS EE L ar M ov fb (PEC.ENC eb ek stk d) ->
  0 <= ov -> ov + 56 <= 2 ^ 64 -> (0 < ek -> 0 <= eb /\ eb + PEC.ESZ * PEC.ecap ek <= 2 ^ 64) ->
  (forall i, 0 <= i < 2 ^ 64 -> ov <= i < ov + 56 -> ~ (ov + 48 <= i < ov + 52) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  PMFA.agsh M M' ov 56 ->
  (0 < ek -> PMFA.agA M M' eb (PEC.ESZ * PEC.ecap ek)) ->
  mem_grows M M' -> L5.u32_at RSEGS M' (ov + 48) d' -> 0 <= d' <= MAX_DEPTH + 1 ->
  PECA.enc_atA RSEGS EE L ar M' ov fb (PEC.ENC eb ek stk d').
Proof.
  intros EA Ho Ho' BB AGO SHO AGB MG U48 Hd'. unfold PECA.enc_atA in EA |- *. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EA |- *.
  destruct EA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & CC & Hk & Hlen & Hd & Hk0 & HB & HIT). pose proof (PEC.ecap_nonneg ek) as CN.
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 48 -> L5C.agree_on M M' a n) by (intros a n X1 X2 i Hi; apply AGO; lia).
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V32]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V40]|].
  split; [exact U48|]. split; [exact (L5.defined_grows M M' _ _ MG D)|]. split; [exact (PMFA.accA_agree M M' ov 56 SHO CC)|].
  split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hd'|]. split; [exact Hk0|]. split.
  - intros Hp. destruct (HB Hp) as (AL & DB & BR & ACCB & ANB). destruct (AGB Hp) as [AB SB']. destruct (BB Hp) as [B0 B1].
    split; [exact AL|]. split; [exact (L5.defined_grows M M' _ _ MG DB)|]. split; [exact BR|]. split.
    + apply (PMFA.accA_agree M M'); [| exact ACCB]. intros x Hx. apply SB'. unfold PEC.ESZ in *. nia.
    + apply (PECFA.annA_agree M M'); [unfold PEC.ESZ in *; nia| exact AL| exact SB'| exact ANB].
  - intros i Hi. pose proof (HIT i Hi) as IT.
    assert (Hp : 0 < ek). { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in Hlen. rewrite Z0 in Hlen. cbn in Hlen. lia. }
    destruct (BB Hp) as (B0 & B1). destruct (AGB Hp) as [AB SB'].
    apply (PECF.eitem_at_agree RSEGS M M'); [| unfold PEC.ESZ in *; lia | unfold PEC.ESZ in *; lia | exact IT].
    eapply L5C.agree_on_sub; [exact AB| unfold PEC.ESZ; lia| unfold PEC.ESZ in *; lia].
Qed.

Lemma enc_popA (M M' : word -> option byte) ov fb eb ek rr e1 d :
  PECA.enc_atA RSEGS EE L ar M ov fb (PEC.ENC eb ek (rev rr ++ [e1]) d) ->
  0 <= ov -> ov + 56 <= 2 ^ 64 -> (0 < ek -> 0 <= eb /\ eb + PEC.ESZ * PEC.ecap ek <= 2 ^ 64) ->
  (forall i, 0 <= i < 2 ^ 64 -> ov <= i < ov + 56 -> ~ (ov + 32 <= i < ov + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  PMFA.agsh M M' ov 56 ->
  (0 < ek -> L5C.agree_on M M' eb (PEC.ESZ * PEC.ecap ek)) ->
  L5.u64_at RSEGS M' (ov + 32) (eb + PEC.ESZ * Z.of_nat (length rr)) -> L5.defined M' ov 56 ->
  (0 < ek -> L5.defined M' eb (PEC.ESZ * PEC.ecap ek) /\ PMSPA.accA M' eb (PEC.ESZ * Z.of_nat (length rr)) /\ PMSPA.annA M' eb (PEC.ESZ * Z.of_nat (length rr)) (PEC.ESZ * PEC.ecap ek)) ->
  PECA.enc_atA RSEGS EE L ar M' ov fb (PEC.ENC eb ek (rev rr) d).
Proof.
  intros EA Ho Ho' BB AGO SHO AGB U32 D' HB'. unfold PECA.enc_atA in EA |- *. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EA |- *.
  destruct EA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & CC & Hk & Hlen & Hd & Hk0 & HB & HIT). pose proof (PEC.ecap_nonneg ek) as CN.
  rewrite length_app, length_rev in Hlen, HB, HIT. cbn [length] in Hlen, HB, HIT. rewrite length_rev.
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 56 -> (a + n <= ov + 32 \/ ov + 40 <= a) -> L5C.agree_on M M' a n) by (intros a n X1 X2 X3 i Hi; apply AGO; lia).
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [exact U32|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V40]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V48]|].
  split; [exact D'|]. split; [exact (PMFA.accA_agree M M' ov 56 SHO CC)|].
  split; [exact Hk|]. split; [lia|]. split; [exact Hd|]. split; [exact Hk0|]. split.
  - intros Hp. destruct (HB Hp) as (AL & DB & BR & ACCB & ANB). destruct (HB' Hp) as (DB' & ACC' & ANN').
    split; [exact AL|]. split; [exact DB'|]. split; [exact BR|]. split; [exact ACC'| exact ANN'].
  - intros i Hi.
    assert (Hp : 0 < ek). { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in Hlen. rewrite Z0 in Hlen. cbn in Hlen. lia. }
    destruct (BB Hp) as (B0 & B1). pose proof (AGB Hp) as AB.
    specialize (HIT i ltac:(lia)). rewrite (app_nth1 (rev rr) [e1]) in HIT by (rewrite length_rev; exact Hi).
    apply (PECF.eitem_at_agree RSEGS M M'); [| unfold PEC.ESZ in *; lia | unfold PEC.ESZ in *; lia | exact HIT].
    eapply L5C.agree_on_sub; [exact AB| unfold PEC.ESZ; lia| unfold PEC.ESZ in *; lia].
Qed.

Lemma ffroomA_mono h h' FF LK LK2 : PMSPA.ffroomA h FF LK -> incl LK2 LK -> NoDup (map ff_addr (FF ++ LK2)) -> h' <= h -> PMSPA.ffroomA h' FF LK2.
Proof.
  intros FR INC ND Hh kk Hk. specialize (FR kk Hk). rewrite L5SAR.ff_count_app in FR. rewrite L5SAR.ff_count_app.
  pose proof (L5SAR.ff_count_incl kk LK2 LK INC (L5SAR.nodup_of_map_app_r FF LK2 ND)) as C2. lia.
Qed.

Section Call.
Variables (FR NB : Z) (SAVED CSK : list nat).
Hypothesis HFR : FR = 96 \/ FR = 128.
Hypothesis HSV : SAVED = SV9 \/ SAVED = SV11 \/ SAVED = SV13.
Hypothesis HNB : 0 <= NB.
Hypothesis CSK3 : In 3%nat CSK.
Hypothesis CSK4 : In 4%nat CSK.
Hypothesis CSKall : forall j, In j CSK -> In j L5SAR.cs_all.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z).
Variables (xstk : list pstate) (xpos : Z) (xmore xdone xhalt : bool) (xdepth : Z) (xec : bool) (xestk : list eitem) (xedepth xlo xhi : Z) (xbad : bool).
Variables (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Let X : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad.

Let XS (a : Z) : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + a) (xhi + a) xbad.
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 4.
Hypothesis FRM : PMSPA.ffroomA 4 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_v AD fb).
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis POK : PECSPA.payload_ok p.
Hypothesis MP : PECSPA.mp_enc p X.
Hypothesis HBN : PESKA.spa_hb P (xhi + NB).
Hypothesis CRED : PMSP.credit_le (PECA.pot_encA L ar P en k) cr.

Variable XF : st.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p XF s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Let LB : list (Z * Z) := PEC.owned s en k ++ LBX.

Let LBc0 : list (Z * Z) := PM.parser_own s ++ LBX.

Definition EBX (ki : PESK.sink) : list (Z * Z) := PEC.enc_own en ++ PESK.sink_own ki.

Let Wk : list L5.range := (PMSPA.o_v AD fb, 56) :: (PESK.o_sink EE fb, 24) :: PEC.enc_own en.
Let spc : Z := sp - FR.
Let NSV : Z := Z.of_nat (length SAVED).

Hypothesis HNF : 8 * NSV <= FR.
Definition csk (Ri : bvmap 5 word) : Prop := forall j, In j CSK -> getr Ri (reg j) = getr R (reg j).

Local Ltac name_objs :=
  set (op := PMSPA.o_p AD fb) in *; set (ov := PMSPA.o_v AD fb) in *; set (oec := PMSPA.o_ec AD fb) in *; set (ois := PMSPA.o_is AD fb) in *;
  set (osk := PESK.o_sink EE fb) in *;
  assert (Eop : op = fb + 592) by reflexivity; assert (Eov : ov = fb + 496) by reflexivity; assert (Eoec : oec = fb + 1120) by reflexivity;
  assert (Eois : ois = fb + 96) by reflexivity; assert (Eosk : osk = fb + 432) by reflexivity.

Local Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH; change (20480 / 8) with 2560 in STKSH;
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp; rewrite L5K.rl3 in Rgp; rewrite L5K.rl4 in Rtp;
  pose proof FOK as ((rs & Hfb) & Fal);
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & STOP & ND & NDF & _);
  pose proof (WF _ Hfb) as (F1 & F2 & F3 & F4 & F5 & F6); cbn [ff_addr ff_class fst snd] in F1, F2, F3, F4, F5, F6; change (ff_bytes 5) with 2048 in F1, F2, F3, F4, F5, F6;
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP; unfold FS_BYTES in F1, F2, F3, F4, F5, F6, FSAPP, FSCEIL, FSIMG.

Lemma NSVv : NSV = 9 \/ NSV = 11 \/ NSV = 13.
Proof. unfold NSV. destruct HSV as [-> |[-> | ->]]; [left|right; left|right; right]; reflexivity. Qed.

Lemma AOF a n : fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n.
Proof. intros H1 H2. destruct FOK as ((rs & Hfb) & Fal). exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. Qed.
Lemma FB8 j : (fb + 8 * j) mod 8 = 0.
Proof.
  destruct FOK as (_ & Fal). pose proof (Z.div_mod fb 2048 ltac:(lia)) as E0. rewrite Fal, Z.add_0_r in E0. rewrite E0.
  replace (2048 * (fb / 2048) + 8 * j) with ((256 * (fb / 2048) + j) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma A16' : sp mod 16 = 0.
Proof. pose proof (Z.div_mod sp 32 ltac:(lia)) as E0. rewrite SP32, Z.add_0_r in E0. rewrite E0. replace (32 * (sp / 32)) with ((2 * (sp / 32)) * 16) by lia. apply Z_mod_mult. Qed.
Lemma SPd8 d : d mod 8 = 0 -> (sp - d) mod 8 = 0.
Proof.
  intros Hd. pose proof (Z.div_mod sp 32 ltac:(lia)) as E0. rewrite SP32, Z.add_0_r in E0. pose proof (Z.div_mod d 8 ltac:(lia)) as E1. rewrite Hd, Z.add_0_r in E1.
  rewrite E0, E1. replace (32 * (sp / 32) - 8 * (d / 8)) with ((4 * (sp / 32) - d / 8) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma SPd16 d : d mod 16 = 0 -> (sp - d) mod 16 = 0.
Proof.
  intros Hd. pose proof (Z.div_mod sp 32 ltac:(lia)) as E0. rewrite SP32, Z.add_0_r in E0. pose proof (Z.div_mod d 16 ltac:(lia)) as E1. rewrite Hd, Z.add_0_r in E1.
  rewrite E0, E1. replace (32 * (sp / 32) - 16 * (d / 16)) with ((2 * (sp / 32) - d / 16) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma SPC32 : spc mod 32 = 0.
Proof. unfold spc. destruct HFR as [-> | ->]; [replace (sp - 96) with (sp + (-3) * 32) by lia| replace (sp - 128) with (sp + (-4) * 32) by lia]; rewrite Z_mod_plus_full; exact SP32. Qed.
Lemma SPC16 : spc mod 16 = 0.
Proof. unfold spc. apply SPd16. destruct HFR as [-> | ->]; reflexivity. Qed.
Lemma ws_wenc a : L5.outside (PEC.W_enc AD EE fb) a -> L5.outside [(PESK.o_sink EE fb, 24)] a.
Proof. intros O r0 [<-|[]]. apply O. unfold PEC.W_enc. cbn [app]. right; left; reflexivity. Qed.

Lemma eblk_facts q m : In (q, m) (PEC.enc_own en) ->
  In (q, m) LB /\ 0 < PEC.en_k en /\ q = PEC.en_b en /\ m = PEC.ESZ * PEC.ecap (PEC.en_k en)
  /\ 0 <= q /\ q + m <= 2 ^ 47 /\ (q + m <= 2147446784 \/ 2147446784 + 17592186048512 <= q) /\ q + m <= ahl_ceil ar
  /\ (forall o n, PMSPA.aobjA FF o n -> q + m <= o \/ o + n <= q)
  /\ (forall q' m', In (q', m') LBc0 -> q' + m' <= q \/ q + m <= q').
Proof.
  intros Hq. entry_facts. unfold PEC.enc_own in Hq.
  destruct (Z.eqb_spec (PEC.en_k en) 0) as [Z0|NZ]; [destruct Hq|]. destruct Hq as [Hq|[]]. injection Hq as E1 E2.
  pose proof CPRE as (_ & _ & EA & _). pose proof EA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EK & _).
  assert (IN : In (q, m) LB).
  { unfold LB, PEC.owned. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. unfold PEC.enc_own.
    replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). left. rewrite E1, E2. reflexivity. }
  destruct (WB _ IN) as ((B0 & _ & _ & _ & BCEIL & (_ & BAPP & B47)) & _). cbn [fst snd] in B0, BCEIL, BAPP, B47. unfold BIGSHADOW_LO, BIGSHADOW_HI in BAPP.
  split; [exact IN|]. split; [clear - EK NZ; lia|]. split; [symmetry; exact E1|]. split; [symmetry; exact E2|].
  split; [clear - B0; lia|]. split; [exact B47|]. split; [exact BAPP|]. split; [exact BCEIL|]. split.
  - intros o n AO. exact (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m o n HH IN AO).
  - intros q' m' Hq'. apply (PMASK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ q' m' q m HH); [| exact IN|].
    + unfold LB, PEC.owned. unfold LBc0 in Hq'. apply in_app_or in Hq'. destruct Hq' as [Y|Y]; apply in_or_app; [left; apply in_or_app; left; exact Y| right; exact Y].
    + unfold LBc0 in Hq'. apply in_app_or in Hq'. destruct Hq' as [Y|Y].
      * apply (PMASK.fst_neq_appA (PM.parser_own s) (PEC.enc_own en ++ PESK.sink_own k ++ LBX) q' m' q m); [| exact Y|].
        { unfold LB, PEC.owned in ND. rewrite <- !app_assoc in ND. exact (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ ltac:(unfold LB, PEC.owned in HH; rewrite <- !app_assoc in HH; exact HH)). }
        apply in_or_app. left. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). left. rewrite E1, E2. reflexivity.
      * apply not_eq_sym. apply (PMASK.fst_neq_appA (PM.parser_own s ++ PEC.enc_own en ++ PESK.sink_own k) LBX q m q' m'); [| | exact Y].
        { exact (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH). }
        apply in_or_app; right. apply in_or_app; left. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). left. rewrite E1, E2. reflexivity.
Qed.

Lemma ws_wapp : PMKA.wapp Wk.
Proof.
  entry_facts. unfold Wk. apply PMKA.wapp_cons.
  - cbn [fst snd]. unfold PMSPA.o_v. cbn [pa_off_v PeCLayoutA.CADDR_A]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - F1 F2 FSAPP. lia.
  - apply PMKA.wapp_cons.
    + cbn [fst snd pe_off_sink PeCLayoutA.EADDR_A]. unfold PESK.o_sink. cbn [pe_off_sink PeCLayoutA.EADDR_A]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - F1 F2 FSAPP. lia.
    + intros rr Hr. destruct rr as [q m]. destruct (eblk_facts q m Hr) as (_ & _ & _ & _ & B0 & B47 & BAPP & _). cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - B0 B47 BAPP. lia.
Qed.

Lemma wk_out a : ~ (PMSPA.o_v AD fb <= a < PMSPA.o_v AD fb + 56) -> ~ (PESK.o_sink EE fb <= a < PESK.o_sink EE fb + 24) ->
  (forall q m, In (q, m) (PEC.enc_own en) -> ~ (q <= a < q + m)) -> L5.outside Wk a.
Proof.
  intros N0 N1 N2 rr [<-|[<-|Hr]]; [unfold L5.in_rng; cbn [fst snd]; exact N0| unfold L5.in_rng; cbn [fst snd]; exact N1|].
  destruct rr as [q m]. unfold L5.in_rng. cbn [fst snd]. exact (N2 q m Hr).
Qed.
Lemma wk_out_obj o n : PMSPA.aobjA FF o n -> (o + n <= PESK.o_sink EE fb \/ PESK.o_sink EE fb + 24 <= o) -> (o + n <= PMSPA.o_v AD fb \/ PMSPA.o_v AD fb + 56 <= o) ->
  forall i, o <= i < o + n -> L5.outside Wk i.
Proof.
  intros AO Ho Hv i Hi. apply wk_out; [clear - Hv Hi; lia| clear - Ho Hi; lia|]. intros q m Hq. destruct (eblk_facts q m Hq) as (_ & _ & _ & _ & _ & _ & _ & _ & AP & _).
  destruct (AP o n AO); clear - H Hi; lia.
Qed.
Lemma wk_out_blk q m : In (q, m) LBc0 -> PMKA.blk_out Wk q m.
Proof.
  intros Hq i Hi. entry_facts. name_objs.
  assert (INq : In (q, m) LB) by (unfold LB, PEC.owned; unfold LBc0 in Hq; apply in_app_or in Hq; destruct Hq as [Y|Y]; apply in_or_app; [left; apply in_or_app; left; exact Y| right; exact Y]).
  apply wk_out.
  - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m ov 56 HH INq (AOF ov 56 ltac:(lia) ltac:(lia))) as [Y|Y]; clear - Y Hi; lia.
  - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m osk 24 HH INq (AOF osk 24 ltac:(lia) ltac:(lia))) as [Y|Y]; clear - Y Hi; lia.
  - intros q' m' Hq'. destruct (eblk_facts q' m' Hq') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AP). destruct (AP q m Hq); clear - H Hi; lia.
Qed.

Lemma keepf Mi : L5SAR.ek L ar LBc0 FF sp 20480 Wk M Mi ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mi (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s /\ PM.iss_at RSEGS AD PMSPA.accA Mi (PMSPA.o_is AD fb) str sm
  /\ L5.u64_at RSEGS Mi (PMSPA.o_p AD fb + 384) (PMSPA.o_v AD fb) /\ PMSTA.base_okA RSEGS AD Mi /\ PESTA.err_okA RSEGS AD AAD EE Mi e
  /\ PEC.content_ok RSEGS AD Mi fb p (PM.p_src s) str sm /\ PECA.ec_stateA RSEGS AD Mi fb xec cat /\ PMSPA.accA Mi (PMSPA.o_p AD fb) PECA.RDR_BYTES.
Proof.
  intros EK. entry_facts. name_objs.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR). cbn [s_ec X] in ECS.
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (BRc0 : forall x, In x LBc0 -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by (intros x Hx; apply BRB; apply INC0; exact Hx).
  assert (PINC : incl (PM.parser_own s) LBc0) by (unfold LBc0; apply incl_appl; apply incl_refl).
  assert (SINC : incl (PM.vs_own str) LBc0) by (unfold LBc0; apply incl_appr; exact INCS).
  pose proof ws_wapp as WAPP.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model osk 24 sp 20480 HH (PMKA.aobj_of_aobjA FF osk 24 (AOF osk 24 ltac:(lia) ltac:(lia)) ltac:(rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8)) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & _).
  pose proof wk_out_blk as OUTB.
  assert (OUTO : forall a m, PMSPA.aobjA FF a m -> (a + m <= osk \/ osk + 24 <= a) -> (a + m <= ov \/ ov + 56 <= a) -> forall i, a <= i < a + m -> L5.outside Wk i) by exact wk_out_obj.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 sp 20480 HH (PMKA.aobj_of_aobjA FF ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) ltac:(rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8)) ltac:(lia) ltac:(reflexivity)) as ((Q1 & _) & _).
  assert (Iq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LBc0) by (apply PINC; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (SDEP : forall a, PMST.dep AD a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside Wk a).
  { intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
    split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply wk_out; [clear - DI Q1; lia| clear - DI K1; lia|].
    intros q m Hq. destruct (eblk_facts q m Hq) as (INq & _). destruct (WB _ INq) as ((_ & BIMG & _) & _). cbn [fst snd] in BIMG.
    rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BIMG. clear - DI BIMG. lia. }
  split.
  { apply (PMKA.parser_keepA RSEGS AD L ar LBc0 FF sp 20480 Wk M Mi EK WAPP FRB BRc0 op ois s (AOF op 384 ltac:(lia) ltac:(lia)) PINC); [| | | | exact PA].
    - apply (OUTO op 384 (AOF op 384 ltac:(lia) ltac:(lia))); [clear - Eop Eosk; lia| clear - Eop Eov; lia].
    - apply OUTB. exact Iq.
    - apply OUTB. apply PINC. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
    - intros c n q E1. apply OUTB. apply PINC. unfold PM.parser_own, PM.vs_own. rewrite E1. right; right; left. reflexivity. }
  split.
  { apply (PMKA.iss_keepA RSEGS AD L ar LBc0 FF sp 20480 Wk M Mi EK WAPP FRB BRc0 ois str sm (AOF ois 272 ltac:(lia) ltac:(lia)) SINC); [| | exact IA].
    - apply (OUTO ois 272 (AOF ois 272 ltac:(lia) ltac:(lia))); [clear - Eois Eosk; lia| clear - Eois Eov; lia].
    - intros c n0 q E1. refine (OUTB q c _). apply SINC. unfold PM.vs_own. rewrite E1. left. reflexivity. }
  split.
  { apply (PMKA.u64_keepA RSEGS L ar LBc0 FF sp 20480 Wk M Mi EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF].
    apply (OUTO (op + 384) 8 (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [clear - Eop Eosk; lia| clear - Eop Eov; lia]. }
  split.
  { change (PMSTA.base_okA RSEGS PMA.AD Mi). apply (PMASK.base_keep L ar C LY LBc0 FF sp 20480 Wk M Mi EK); [| exact BASE]. intros a Ha. apply wk_out; [clear - Ha Q1; lia| clear - Ha K1; lia|].
    intros q m Hq. destruct (eblk_facts q m Hq) as (INq & _). destruct (WB _ INq) as ((_ & BIMG & _) & _). cbn [fst snd] in BIMG.
    rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BIMG. clear - Ha BIMG. lia. }
  split.
  { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBc0 FF sp 20480 Wk M Mi EK e PECSA.addrs_wf_A); [exact SDEP| exact ERR]. }
  split.
  { apply (content_keepA' LBc0 FF sp 20480 Wk M Mi fb p s str sm op EK WAPP FRB BRc0 (AOF ois 272 ltac:(lia) ltac:(lia))); [| exact SINC| exact Iq| exact OUTB| exact IA| exact PA| exact CONT].
    fold ois. intros i Hi. apply (OUTO ois 272 (AOF ois 272 ltac:(lia) ltac:(lia))); [clear - Eois Eosk; lia| clear - Eois Eov; lia| clear - Hi; lia]. }
  split.
  { apply (PECFA.ec_state_keepA RSEGS AD L ar LBc0 FF sp 20480 Wk M Mi EK WAPP FRB fb xec cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
    fold oec. apply (OUTO oec 16 (AOF oec 16 ltac:(lia) ltac:(lia))); [clear - Eoec Eosk; lia| clear - Eoec Eov; lia]. }
  exact (PMKA.acc_keepA' L ar LBc0 FF sp 20480 Wk M Mi EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACCR).
Qed.

Let We : list L5.range := Wk ++ ((PMSPA.o_ec AD fb, 16) :: PMSPA.err_W AD).
Lemma we_wapp : PMKA.wapp We.
Proof.
  entry_facts. unfold We. apply PMKA.wapp_app; [exact ws_wapp|]. apply PMKA.wapp_cons.
  - cbn [fst snd]. unfold PMSPA.o_ec. cbn [pa_off_ec PeCLayoutA.CADDR_A]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - F1 F2 FSAPP. lia.
  - intros rr Hin. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PeCLayoutA.CADDR_A] in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI.
    destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia.
Qed.
Lemma we_wk a : L5.outside We a -> L5.outside Wk a.
Proof. intros O r0 Hr. apply O. unfold We. apply in_or_app. left. exact Hr. Qed.

Lemma we_rng rr a : In rr ((PMSPA.o_ec AD fb, 16) :: PMSPA.err_W AD) -> L5.in_rng rr a ->
  (PMSPA.o_ec AD fb <= a < PMSPA.o_ec AD fb + 16) \/ (0x674080 <= a < 0x674082) \/ (0x695ad0 <= a < 0x695cf0).
Proof.
  intros Hin Hr. unfold L5.in_rng in Hr. destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; left; exact Hr|].
  right. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PeCLayoutA.CADDR_A] in Hin.
  destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; [left; exact Hr| right; clear - Hr; lia].
Qed.
Lemma we_out a : L5.outside Wk a -> ~ (PMSPA.o_ec AD fb <= a < PMSPA.o_ec AD fb + 16) -> ~ (0x674080 <= a < 0x674082) -> ~ (0x695ad0 <= a < 0x695cf0) -> L5.outside We a.
Proof.
  intros O N1 N2 N3 rr Hin Hr. unfold We in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (O rr Hin Hr)|].
  destruct (we_rng rr a Hin Hr) as [Y|[Y|Y]]; [exact (N1 Y)| exact (N2 Y)| exact (N3 Y)].
Qed.
Lemma we_wenc a : (forall q m, In (q, m) (PEC.enc_own en) -> ~ (q <= a < q + m)) -> L5.outside (PEC.W_enc AD EE fb) a -> L5.outside We a.
Proof.
  intros NB0 O. apply we_out.
  - apply wk_out; [| | exact NB0].
    + intros X'. apply (O (PMSPA.o_v AD fb, 56)); [unfold PEC.W_enc; cbn [app]; left; reflexivity| exact X'].
    + intros X'. apply (O (PESK.o_sink EE fb, 24)); [unfold PEC.W_enc; cbn [app]; right; left; reflexivity| exact X'].
  - intros X'. apply (O (PMSPA.o_ec AD fb, 16)); [unfold PEC.W_enc; cbn [app]; right; right; left; reflexivity| exact X'].
  - intros X'. apply (O (0x674080, 2)); [unfold PEC.W_enc, PMSPA.err_W; cbn [app pa_errcat_guard pa_atexit PeCLayoutA.CADDR_A]; right; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X'; lia].
  - intros X'. apply (O (0x695ad0, 544)); [unfold PEC.W_enc, PMSPA.err_W; cbn [app pa_errcat_guard pa_atexit PeCLayoutA.CADDR_A]; right; right; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X'; lia].
Qed.

Lemma keepf_ec Mi : L5SAR.ek L ar LBc0 FF sp 20480 We M Mi ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mi (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s /\ PM.iss_at RSEGS AD PMSPA.accA Mi (PMSPA.o_is AD fb) str sm
  /\ L5.u64_at RSEGS Mi (PMSPA.o_p AD fb + 384) (PMSPA.o_v AD fb) /\ PMSTA.base_okA RSEGS AD Mi
  /\ PEC.content_ok RSEGS AD Mi fb p (PM.p_src s) str sm /\ PMSPA.accA Mi (PMSPA.o_p AD fb) PECA.RDR_BYTES.
Proof.
  intros EK. entry_facts. name_objs.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (BRc0 : forall x, In x LBc0 -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by (intros x Hx; apply BRB; apply INC0; exact Hx).
  assert (PINC : incl (PM.parser_own s) LBc0) by (unfold LBc0; apply incl_appl; apply incl_refl).
  assert (SINC : incl (PM.vs_own str) LBc0) by (unfold LBc0; apply incl_appr; exact INCS).
  pose proof we_wapp as WAPP.
  assert (I8 : ois mod 8 = 0) by (rewrite Eois; replace (fb + 96) with (fb + 8 * 12) by (clear; lia); apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ois 272 sp 20480 HH (PMKA.aobj_of_aobjA FF ois 272 (AOF ois 272 ltac:(lia) ltac:(lia)) I8) ltac:(clear; lia) ltac:(reflexivity)) as ((I1 & _) & _).
  assert (OUTB : forall q m, In (q, m) LBc0 -> PMKA.blk_out We q m).
  { intros q m Hq i Hi. pose proof (INC0 _ Hq) as HqLB. apply we_out; [exact (wk_out_blk q m Hq i Hi)| | |].
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m oec 16 HH HqLB (AOF oec 16 ltac:(lia) ltac:(lia))) as [Xb|Xb]; clear - Xb Hi; lia.
    - destruct (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH HqLB) as [Xc|Xc]; clear - Xc Hi; lia.
    - destruct (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH HqLB) as [Xc|Xc]; clear - Xc Hi; lia. }
  assert (OUTO : forall a m, PMSPA.aobjA FF a m -> (a + m <= osk \/ osk + 24 <= a) -> (a + m <= ov \/ ov + 56 <= a) -> (a + m <= oec \/ oec + 16 <= a) -> 0x698000 <= a ->
                 forall i, a <= i < a + m -> L5.outside We i).
  { intros a m AO Xa Xb Xc Xd i Hi. apply we_out; [exact (wk_out_obj a m AO Xa Xb i Hi)| clear - Xc Hi; lia| clear - Xd Hi; lia| clear - Xd Hi; lia]. }
  assert (Iq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LBc0) by (apply PINC; unfold PM.parser_own, PM.src_own; left; reflexivity).
  split.
  { apply (PMKA.parser_keepA RSEGS AD L ar LBc0 FF sp 20480 We M Mi EK WAPP FRB BRc0 op ois s (AOF op 384 ltac:(lia) ltac:(lia)) PINC); [| | | | exact PA].
    - apply (OUTO op 384 (AOF op 384 ltac:(lia) ltac:(lia))); clear - Eop Eosk Eov Eoec Eois I1; lia.
    - apply OUTB. exact Iq.
    - apply OUTB. apply PINC. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
    - intros c n0 q E1. apply OUTB. apply PINC. unfold PM.parser_own, PM.vs_own. rewrite E1. right; right; left. reflexivity. }
  split.
  { apply (PMKA.iss_keepA RSEGS AD L ar LBc0 FF sp 20480 We M Mi EK WAPP FRB BRc0 ois str sm (AOF ois 272 ltac:(lia) ltac:(lia)) SINC); [| | exact IA].
    - apply (OUTO ois 272 (AOF ois 272 ltac:(lia) ltac:(lia))); clear - Eosk Eov Eoec Eois I1; lia.
    - intros c n0 q E1. refine (OUTB q c _). apply SINC. unfold PM.vs_own. rewrite E1. left. reflexivity. }
  split.
  { apply (PMKA.u64_keepA RSEGS L ar LBc0 FF sp 20480 We M Mi EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF].
    apply (OUTO (op + 384) 8 (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); clear - Eop Eov Eosk Eoec Eois I1; lia. }
  split.
  { change (PMSTA.base_okA RSEGS PMA.AD Mi). apply (PMAPAR.base_keepW L ar C LY LBc0 FF sp 20480 We M Mi EK); [| | | | exact BASE].
    - intros a Ha. apply we_out; [apply wk_out; [clear - Ha Eov I1 Eois; lia| clear - Ha Eosk I1 Eois; lia|] | clear - Ha Eoec Eois I1; lia| clear - Ha; lia| clear - Ha; lia].
      intros q m Hq. destruct (eblk_facts q m Hq) as (INq & _). destruct (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH INq) as [Xc|Xc]; clear - Ha Xc; lia.
    - intros a Ha. apply we_out; [apply wk_out; [clear - Ha Eov I1 Eois; lia| clear - Ha Eosk I1 Eois; lia|] | clear - Ha Eoec Eois I1; lia| clear - Ha; lia| clear - Ha; lia].
      intros q m Hq. destruct (eblk_facts q m Hq) as (INq & _). destruct (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH INq) as [Xc|Xc]; clear - Ha Xc; lia.
    - apply we_out; [apply wk_out; [clear - Eov I1 Eois; lia| clear - Eosk I1 Eois; lia|] | clear - Eoec Eois I1; lia| clear; lia| clear; lia].
      intros q m Hq. destruct (eblk_facts q m Hq) as (INq & _). destruct (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH INq) as [Xc|Xc]; clear - Xc; lia.
    - intros a Ha. apply we_out; [apply wk_out; [clear - Ha Eov I1 Eois; lia| clear - Ha Eosk I1 Eois; lia|] | clear - Ha Eoec Eois I1; lia| clear - Ha; lia| clear - Ha; lia].
      intros q m Hq. destruct (eblk_facts q m Hq) as (INq & _). destruct (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH INq) as [Xc|Xc]; clear - Ha Xc; lia. }
  split.
  { apply (content_keepA' LBc0 FF sp 20480 We M Mi fb p s str sm op EK WAPP FRB BRc0 (AOF ois 272 ltac:(lia) ltac:(lia))); [| exact SINC| exact Iq| exact OUTB| exact IA| exact PA| exact CONT].
    fold ois. intros i Hi. apply (OUTO ois 272 (AOF ois 272 ltac:(lia) ltac:(lia))); [clear - Eois Eosk; lia| clear - Eois Eov; lia| clear - Eois Eoec; lia| exact I1| clear - Hi; lia]. }
  exact (PMKA.acc_keepA' L ar LBc0 FF sp 20480 We M Mi EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACCR).
Qed.

Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Let G_ := PMAUK.gctx L ar HI LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k).
Hypothesis G : G_.
Let FF' : list fframe := (F, 1, spc + 32) :: FF.
Let BINV (ki : PESK.sink) := PMAUK.binv L ar HI M model LBc0 FF LK Aw sp 20480 spc (owns SAVED sp R) F 1 Wk (EBX ki).

Hypothesis APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (EBX k ++ LBc0) FF sp0 scr0 (a + i)) -> 0 < n ->
    (a + n <= F \/ F + 128 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + 16 <= a) /\ (a + n <= fl \/ fl + 1 <= a).

Definition inv (Mi : word -> option byte) (mdi : Model) (LKi : list fframe) (Awi : list (Z * Z)) (cri : credit) (ki : PESK.sink) (a : Z) (eni : PEC.enc) : Prop :=
  BINV ki Mi mdi LKi cri Awi /\ shadow_zero Mi (sp - 20480) 2560
  /\ (PEC.en_b eni = PEC.en_b en /\ PEC.en_k eni = PEC.en_k en)
  /\ PECA.enc_atA RSEGS EE L ar Mi (PMSPA.o_v AD fb) fb eni /\ PESKA.sink_atA RSEGS L ar P Mi (PESK.o_sink EE fb) ki
  /\ xlo + a <= PESK.sk_z ki <= xhi + a
  /\ PMSP.credit_keep cr cri (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en ki).

Local Ltac cut_facts INV kq :=
  let BI := fresh "BI" in
  pose proof INV as (BI & SZq & ESq & EAq & SKAq & CLq & CKq);
  pose proof BI as (HHq & AMq & MRTq & IAWq & ILKq & ASTKq & EKq & DKq & OWNq & FSDq); change (ff_bytes 1 / 8) with 16 in FSDq;
  pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _);
  set (LBq := EBX kq ++ LBc0) in HHq.

Lemma perm_q kq : Permutation (EBX kq ++ LBc0) (PEC.owned s en kq ++ LBX).
Proof. unfold EBX, LBc0, PEC.owned. rewrite <- !app_assoc. apply PEEK.perm4. Qed.

Lemma perm_qe kq enq : PEC.en_b enq = PEC.en_b en -> PEC.en_k enq = PEC.en_k en -> Permutation (EBX kq ++ LBc0) (PEC.owned s enq kq ++ LBX).
Proof. intros Hb Hk. unfold PEC.owned. replace (PEC.enc_own enq) with (PEC.enc_own en) by (unfold PEC.enc_own; rewrite Hb, Hk; reflexivity). exact (perm_q kq). Qed.
Lemma HHp : ri_inv HI (EBX k ++ LBc0) FF LK cr Aw M (vml_of model).
Proof. exact (ri_perm _ _ FF LK cr Aw M _ (Permutation_sym (perm_q k)) HH). Qed.

Lemma g_facts :
  let ov := PMSPA.o_v AD fb in let osk := PESK.o_sink EE fb in
  4096 <= F /\ F + 128 <= 2 ^ 47 /\ 6914048 <= F /\ F mod 32 = 0 /\ F / 8 * 8 = F /\ (2147446784 + 17592186048512 <= F \/ F + 128 <= 2147446784)
  /\ 4096 <= fl /\ fl + 1 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) /\ (F + 128 <= fl \/ fl + 1 <= F)
  /\ F + 128 <= ahl_ceil ar /\ fl + 1 <= ahl_ceil ar /\ incl LK2 LK
  /\ (ov + 56 <= F \/ F + 128 <= ov) /\ (ov + 56 <= F / 8 + SB \/ F / 8 + SB + 16 <= ov) /\ (ov + 56 <= fl \/ fl + 1 <= ov)
  /\ (osk + 24 <= F \/ F + 128 <= osk) /\ (osk + 24 <= F / 8 + SB \/ F / 8 + SB + 16 <= osk) /\ (osk + 24 <= fl \/ fl + 1 <= osk)
  /\ ar_fs ar <= F /\ F + 128 <= ar_fs ar + FS_BYTES /\ 8 * NSV <= FR /\ (NSV = 9 \/ NSV = 11 \/ NSV = 13) /\ (ar_fs ar <= fl < ar_fs ar + FS_BYTES).
Proof.
  entry_facts. name_objs. pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *.
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 sp 20480 HHp (PMKA.aobj_of_aobjA FF ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m) ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & _ & _ & QCL & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model osk 24 sp 20480 HHp (PMKA.aobj_of_aobjA FF osk 24 (AOF osk 24 ltac:(lia) ltac:(lia)) K8) ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & _ & _ & KCL & _).
  destruct (APART ov 56 sp 20480 QCL ltac:(clear; lia)) as (AvF & AvS & AvL).
  destruct (APART osk 24 sp 20480 KCL ltac:(clear; lia)) as (AkF & AkS & AkL).
  pose proof NSVv as NV.
  repeat split; first [assumption | clear - GFR; lia | clear - GF8; lia | clear - GFLR; lia | exact HNF | clear - GFLP; lia].
Qed.

Lemma frame_agree (Ma Mb : word -> option byte) (Wp : Z -> Prop) :
  (forall a, Wp a -> (spc <= a < sp) \/ (F <= a < F + 128) \/ (F / 8 + SB <= a < F / 8 + SB + 16)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
  (forall a, 0 <= a -> a + 1 <= ahl_ceil ar -> (a + 1 <= F \/ F + 128 <= a) -> (2147446784 + 17592186048512 <= a \/ a + 1 <= 2147446784) ->
      Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a))
  /\ (forall x, 0 <= x -> x + 1 <= 2 ^ 47 -> (x + 1 <= F \/ F + 128 <= x) -> Mb (Z_to_bv 64 (HeapIfaceA.S x)) = Ma (Z_to_bv 64 (HeapIfaceA.S x))).
Proof.
  intros WP AG. entry_facts.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & _).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  split.
  - intros a H0 H1 H2 H3. apply AG; [clear - H0 H1 SPT; Lia.lia|]. intros X'. destruct (WP a X') as [Y|[Y|Y]].
    + unfold spc in Y. clear - Y H1 SLO HFR. Lia.lia.
    + clear - Y H2. Lia.lia.
    + unfold SB in Y. clear - Y H3 GF1 GF2 GF8. Lia.lia.
  - intros x H0 H1 H2. apply AG; [unfold HeapIfaceA.S, SB; clear - H0 H1; Lia.lia|]. intros X'. destruct (WP _ X') as [Y|[Y|Y]]; unfold HeapIfaceA.S, SB in Y.
    + unfold spc in Y. clear - Y H0 H1 SLO SPT HFR. Lia.lia.
    + clear - Y H0 H1 GFBIG. Lia.lia.
    + clear - Y H2 GF8. Lia.lia.
Qed.

Lemma blk_facts Ma LKc crc Awc V kc q m : ri_inv HI (EBX kc ++ LBc0) FF' LKc crc Awc Ma V -> In (q, m) (EBX kc ++ LBc0) ->
  4096 <= q /\ q + m <= 2 ^ 47 /\ (q + m <= 2147446784 \/ 2147446784 + 17592186048512 <= q) /\ q + m <= ahl_ceil ar /\ (q + m <= ar_fs ar \/ ar_fs ar + FS_BYTES <= q).
Proof.
  intros HHc IN. destruct (L5ADHR.blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ (EBX kc ++ LBc0) [] HHc (eq_sym (app_nil_r _)) _ IN) as ((B0 & _ & _ & _ & BCEIL & (_ & BAPP & B47)) & BFS).
  cbn [fst snd] in B0, BCEIL, BAPP, B47, BFS. unfold BIGSHADOW_LO, BIGSHADOW_HI in BAPP. repeat split; assumption.
Qed.

Lemma inv_agree (Ma Mb : word -> option byte) (Wp : Z -> Prop) mda mdb LKc crc Awc kc a enq :
  inv Ma mda LKc Awc crc kc a enq ->
  ri_inv HI (EBX kc ++ LBc0) FF' LKc crc Awc Mb (vml_of mdb) -> L5CA.amodel_ok Awc mdb -> model_rt mda mdb -> mem_grows Ma Mb ->
  (forall a0, Wp a0 -> (spc <= a0 < sp /\ ~ ocell sp NSV a0) \/ (F <= a0 < F + 128) \/ (F / 8 + SB <= a0 < F / 8 + SB + 16)) ->
  (forall a0, 0 <= a0 < 2 ^ 64 -> ~ Wp a0 -> Mb (Z_to_bv 64 a0) = Ma (Z_to_bv 64 a0)) ->
  inv Mb mdb LKc Awc crc kc a enq.
Proof.
  intros INV HHb AMb RTb MG WP AG. entry_facts. name_objs. cut_facts INV kc.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & _ & _ & GFLP).
  assert (WP' : forall a0, Wp a0 -> (spc <= a0 < sp) \/ (F <= a0 < F + 128) \/ (F / 8 + SB <= a0 < F / 8 + SB + 16)) by (intros a0 X'; destruct (WP a0 X') as [[Y _]|[Y|Y]]; [left| right; left| right; right]; exact Y).
  destruct (frame_agree Ma Mb Wp WP' AG) as [AGa AGs].
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKc crc Awc Ma mda ov 56 sp 20480 HHq (PMKA.aobj_of_aobjA FF' ov 56 (PMAUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia))) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2 & Q3 & _) & QBIG & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKc crc Awc Ma mda osk 24 sp 20480 HHq (PMKA.aobj_of_aobjA FF' osk 24 (PMAUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & KBIG & _).
  unfold inv. split.
  { apply (PMAUK.binv_piece L ar HI M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
             Wk (EBX kc) Ma mda LKc crc Awc Mb mdb Wp BI HHb AMb RTb MG AG).
    intros a0 X'. destruct (WP a0 X') as [Y|[Y|Y]]; [left; exact Y| right; left; change (ff_bytes 1) with 128; exact Y| right; right; change (ff_bytes 1 / 8) with 16; exact Y]. }
  split.
  { intros jj Hjj. pose proof (SZq jj Hjj) as Z0. unfold byte_at in Z0 |- *.
    replace (HeapIfaceA.S (sp - 20480) + jj) with (HeapIfaceA.S (sp - 20480 + jj * 8)) in Z0 |- * by (unfold HeapIfaceA.S; rewrite Z.div_add by (clear; lia); clear; lia).
    rewrite (AGs (sp - 20480 + jj * 8)); [exact Z0| clear - Hjj SLO SPT; lia| clear - Hjj SHI SPT; lia| clear - Hjj GFC SLO; lia]. }
  split; [exact ESq|].
  split.
  { apply (PECFA.enc_atA_agree RSEGS EE L ar Ma Mb ov fb enq); [clear - Q1; lia| clear - Q3; lia| | | exact EAq].
    - split; [intros i Hi; apply AGa; clear - Hi Q1 Q2 Q3 QBIG AvF; lia| intros x Hx; apply AGs; clear - Hx Q1 Q3 AvF; lia].
    - intros Hp. destruct ESq as [ESb ESk]. rewrite ESk in Hp. rewrite ESb, ESk. assert (IN : In (PEC.en_b en, PEC.ESZ * PEC.ecap (PEC.en_k en)) (EBX kc ++ LBc0)).
      { apply in_or_app; left. unfold EBX. apply in_or_app; left. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
      destruct (blk_facts Ma LKc crc Awc _ kc _ _ HHq IN) as (B0 & B47 & BAPP & BCEIL & BFS). unfold FS_BYTES in BFS, GFS2.
      split; [clear - B0; lia|]. split; [clear - B47; lia|].
      split; [intros i Hi; apply AGa; clear - Hi B0 BCEIL BAPP BFS GFS1 GFS2; lia| intros x Hx; apply AGs; clear - Hx B0 B47 BFS GFS1 GFS2; lia]. }
  split.
  { apply (PECFA.sink_atA_agree RSEGS L ar Ma Mb P osk kc); [clear - K1; lia| clear - K3; lia| | | exact SKAq].
    - split; [intros i Hi; apply AGa; clear - Hi K1 K2 K3 KBIG AkF; lia| intros x Hx; apply AGs; clear - Hx K1 K3 AkF; lia].
    - intros Hp. assert (IN : In (PESK.sk_b kc, PESK.sk_c kc) (EBX kc ++ LBc0)).
      { apply in_or_app; left. unfold EBX. apply in_or_app; right. unfold PESK.sink_own. replace (PESK.sk_c kc =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
      destruct (blk_facts Ma LKc crc Awc _ kc _ _ HHq IN) as (B0 & B47 & BAPP & BCEIL & BFS). unfold FS_BYTES in BFS, GFS2.
      split; [clear - B0; lia|]. split; [clear - B47; lia|].
      split; [intros i Hi; apply AGa; clear - Hi B0 BCEIL BAPP BFS GFS1 GFS2; lia| intros x Hx; apply AGs; clear - Hx B0 B47 BFS GFS1 GFS2; lia]. }
  split; [exact CLq| exact CKq].
Qed.

Lemma inv_cpre Mi mdi LKi Awi cri ki a lo hi eni esi edi : inv Mi mdi LKi Awi cri ki a eni -> lo = xlo + a -> hi = xhi + a ->
  PEC.en_stk eni = rev esi -> PEC.en_depth eni = edi ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p (ST xstk xpos xmore xdone xhalt xdepth xec esi edi lo hi xbad) s str sm eni ki e cat.
Proof.
  intros INV Hlo Hhi HSTK HED. cut_facts INV ki.
  destruct (keepf Mi EKq) as (PA' & IA' & VREF' & BASE' & ERR' & CONT' & ECS' & ACCR').
  destruct CPRE as (_ & _ & _ & _ & _ & _ & _ & TBOK & _ & CL & _ & ECI & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad). cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad] in *.
  unfold PECA.crun_preA.
  split; [exact PA'|]. split; [exact IA'|]. split; [exact EAq|]. split; [exact VREF'|]. split; [exact SKAq|].
  split; [exact BASE'|]. split; [exact ERR'|]. split; [exact TBOK|]. split; [exact CONT'|].
  split.
  { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad].
    split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
    split; [exact HSTK|]. split; [exact HED|]. split; [clear - CLq Hlo Hhi; lia| exact Lbad]. }
  cbn [s_ec]. split; [exact ECS'|]. split; [exact ECI| exact ACCR'].
Qed.

Definition sfacts (MV : word -> option byte) : Prop :=
  L5.img_clear MV 1253376 1286144 /\ L5.u64_at RSEGS MV 1317368 SBL /\ L5.u32_at RSEGS MV 1317376 1 /\
  140735332487168 + 20480 <= sp <= 140737488355328 /\ sp mod 32 = 0 /\ L5.writable RSEGS MV (sp - FR) FR.
Definition ffacts (MV : word -> option byte) (zsh : bool) : Prop :=
  4096 <= F <= 140737488355200 /\ F mod 32 = 0 /\ L5.defined MV F 128 /\ L5.writable RSEGS MV F 128 /\
  (2147446784 + 17592186048512 <= F \/ F + 128 <= 2147446784) /\ L5.writable RSEGS MV (F / 8 + SBL) 16 /\
  (if zsh then L5KA.zeros_at MV (F / 8 + SBL) 16 else True) /\
  L5.u64_at RSEGS MV (F + 120) fl /\ 4096 <= fl <= 140737488355327 /\ L5.writable RSEGS MV fl 1 /\
  (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) /\ (F + 128 <= fl \/ fl + 1 <= F) /\
  ((sp - FR) + FR <= F \/ F + 128 <= sp - FR) /\ ((sp - FR) + FR <= fl \/ fl + 1 <= sp - FR).
Definition ofacts (MV : word -> option byte) (eni : PEC.enc) : Prop :=
  let ov := PMSPA.o_v AD fb in let osk := PESK.o_sink EE fb in
  4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at MV (ov / 8 + SBL) 7
  /\ L5.writable RSEGS MV ov 56 /\ ((sp - FR) + FR <= ov \/ ov + 56 <= (sp - FR))
  /\ L5KA.zeros_at MV ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at MV ((ov + 24) / 8 + SBL) 1 /\ L5KA.zeros_at MV ((ov + 32) / 8 + SBL) 1
  /\ L5.u64_at RSEGS MV (ov + 8) osk /\ 4096 <= osk <= 140737488355304 /\ osk mod 8 = 0 /\ osk + 24 <= ov
  /\ L5.u64_at RSEGS MV (ov + 24) (PEC.en_b eni) /\ L5.u64_at RSEGS MV (ov + 32) (PEC.en_b eni + 24 * Z.of_nat (length (PEC.en_stk eni))) /\ 0 <= PEC.en_b eni <= 2 ^ 47
  /\ (ov + 56 <= F \/ F + 128 <= ov) /\ (ov + 56 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= ov) /\ (ov + 56 <= fl \/ fl + 1 <= ov)
  /\ (osk + 24 <= F \/ F + 128 <= osk) /\ (osk + 24 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= osk) /\ (osk + 24 <= fl \/ fl + 1 <= osk)
  /\ L5.u32_at RSEGS MV (ov + 48) (PEC.en_depth eni).

Lemma vis_facts Mq mdq LKq Awq crq kq a enq : inv Mq mdq LKq Awq crq kq a enq ->
  let H := ahid Awq mdq in let MV := mrestrict H Mq in
  sfacts MV /\ ffacts MV false /\ owns SAVED sp R MV /\ ofacts MV enq
  /\ (forall a0 n, spc <= a0 -> a0 + n <= sp -> L5A.avis H a0 n) /\ L5A.avis H F 128 /\ L5A.avis H (F / 8 + SB) 16 /\ L5A.avis H fl 1
  /\ L5A.avis H (PMSPA.o_v AD fb) 56 /\ L5A.avis H (PESK.o_sink EE fb) 24.
Proof.
  intros INV H MV. entry_facts. name_objs. cut_facts INV kq.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & GNF & GNV & GFLP).
  destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
              Wk (EBX kq) Mq mdq LKq crq Awq BI)
    as ((W0 & W1 & W2 & W3 & W4) & OWNv & (FD & FW & FSW & FLC & FLW) & (_ & VFL & VF & VS & VSH)).
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. fold H in W0, W1, W2, W3, W4, OWNv, FD, FW, FSW, FLC, FLW, VFL, VF, VS, VSH. fold MV in W0, W1, W2, W3, W4, OWNv, FD, FW, FSW, FLC, FLW.
  replace (sp - spc) with FR in W0, VS by (unfold spc; clear; lia).
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq HHq) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _). fold H in VIS, VIMG, VFS, VBLK, VBSH.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKA.aobj_of_aobjA FF' ov 56 (PMAUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia))) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2' & Q3 & Q4 & Q5) & QBIG & QDEF & QVIS & QSHV & QCL & QSHCL). fold H in QVIS, QSHV.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKA.aobj_of_aobjA FF' osk 24 (PMAUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & _ & _ & KVIS & _). fold H in KVIS.
  assert (CVv : forall a0 m0, ov <= a0 -> a0 + m0 <= ov + 56 -> L5A.avis H a0 m0) by (intros a0 m0 X1 X2; eapply L5A.avis_sub; [exact QVIS| lia| lia]).
  pose proof EAq as (EV0 & EV8 & EV16 & EV24 & EV32 & EV40 & EV48 & EDEF & EACC & EK & ELEN & EDEP & EKB & EBLK & _). fold osk in EV8. unfold PEC.ESZ in EV32.
  pose proof (PEC.ecap_nonneg (PEC.en_k enq)) as CN.
  pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq ov 56 HHq (PMAUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia))) Q8m ltac:(lia) ltac:(reflexivity) EACC) as Zov.
  unfold SB in Zov. change (56 / 8) with 7 in Zov. fold H MV in Zov.
  assert (D8 : forall j, (ov + 8 * j) / 8 = ov / 8 + j).
  { intros j. rewrite <- Q5 at 1. replace (ov / 8 * 8 + 8 * j) with ((ov / 8 + j) * 8) by lia. apply Z.div_mul. clear; lia. }
  assert (ZG : forall j, 0 <= j < 7 -> L5KA.zeros_at MV ((ov + 8 * j) / 8 + SBL) 1).
  { intros j Hj. rewrite D8. intros i Hi. replace (ov / 8 + j + SBL + i) with (ov / 8 + SBL + (j + i)) by lia. apply Zov. lia. }
  pose proof (ZG 1 ltac:(lia)) as Z8. pose proof (ZG 3 ltac:(lia)) as Z24. pose proof (ZG 4 ltac:(lia)) as Z32.
  replace (ov + 8 * 1) with (ov + 8) in Z8 by lia. replace (ov + 8 * 3) with (ov + 24) in Z24 by lia. replace (ov + 8 * 4) with (ov + 32) in Z32 by lia.
  assert (EB : 0 <= PEC.en_b enq <= 2 ^ 47).
  { destruct (Z.eq_dec (PEC.en_k enq) 0) as [Z0|NZ]; [rewrite (EKB Z0); clear; lia|]. destruct (EBLK ltac:(lia)) as (_ & _ & BR0 & _). destruct BR0 as (X1 & _ & _ & _ & X5 & _). unfold PEC.ESZ in X5. clear - X1 X5 SPT CN; lia. }
  split. { split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [clear - SLO SHI SPT; lia|]. split; [exact SP32| unfold spc in W0; exact W0]. }
  split. { unfold ffacts. replace (F + 120) with (F + 128 - 8) by (clear; lia).
           repeat split; first [exact FD | exact FW | exact FSW | exact FLC | exact FLW | exact I | clear - GF1 GF2 GF32 GFBIG GL1 GL2 GLBIG GFLA GFC GLC SLO HFR; lia]. }
  split. exact OWNv.
  split. { unfold ofacts. fold ov osk.
    split; [clear - Q1 Q3; lia|]. split; [exact Q8m|]. split; [exact QBIG|]. split; [exact Zov|].
    split; [apply (proj2 (L5A.writable_vis H Mq ov 56 QVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact QDEF| lia| lia]|].
    split; [clear - Q2' SLO HFR; lia|]. split; [exact Z8|]. split; [exact Z24|]. split; [exact Z32|].
    split; [apply (proj2 (L5A.u64_at_vis H Mq (ov + 8) osk (CVv (ov + 8) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV8|].
    split; [clear - K1 K3; lia|]. split; [exact K8|]. split; [clear - Eov Eosk; lia|].
    split; [apply (proj2 (L5A.u64_at_vis H Mq (ov + 24) _ (CVv (ov + 24) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV24|].
    split; [apply (proj2 (L5A.u64_at_vis H Mq (ov + 32) _ (CVv (ov + 32) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV32|].
    split; [exact EB|]. unfold SB in AvS, AkS. repeat split; try assumption. apply (proj2 (L5A.u32_at_vis H Mq (ov + 48) _ (CVv (ov + 48) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV48. }
  split. { intros a0 n H1 H2. replace a0 with (spc + (a0 - spc)) by (clear; lia). eapply L5A.avis_sub; [exact VS| clear - H1; lia| clear - H1 H2; lia]. }
  split. exact VF. split. exact VSH. split. exact VFL. split. exact QVIS. exact KVIS.
Qed.

Definition tfacts (MV : word -> option byte) (enq : PEC.enc) (e1 : eitem) (rr : list eitem) : Prop :=
  let ov := PMSPA.o_v AD fb in let eb := PEC.en_b enq in let ed := eb + 24 * (Z.of_nat (length rr) + 1) in
  Z.of_nat (length (PEC.en_stk enq)) = Z.of_nat (length rr) + 1 /\ 0 < PEC.en_k enq
  /\ 4096 <= eb /\ ed <= 140737488355328 /\ ed mod 8 = 0 /\ 24 <= ed - eb <= 100000 /\ L5.writable RSEGS MV (ed - 24) 24
  /\ (2147446784 + 17592186048512 <= ed - 24 \/ (ed - 24) + 24 <= 2147446784) /\ L5KA.zeros_at MV ((ed - 8) / 8 + SBL) 1
  /\ ((ed - 24) + 24 <= (sp - FR) \/ (sp - FR) + FR <= (ed - 24)) /\ ((ed - 24) + 24 <= ov \/ ov + 56 <= (ed - 24))
  /\ L5.u64_at RSEGS MV (ed - 8) (ei_cnt e1) /\ 0 <= ei_cnt e1 < 2 ^ 64 /\ ei_ok e1
  /\ In (eb, 24 * PEC.ecap (PEC.en_k enq)) (PEC.enc_own en) /\ ed <= eb + 24 * PEC.ecap (PEC.en_k enq) /\ eb + 24 * PEC.ecap (PEC.en_k enq) <= 2 ^ 47
  /\ ((ed - 24) + 24 <= F \/ F + 128 <= (ed - 24)) /\ ((ed - 24) + 24 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= (ed - 24)) /\ ((ed - 24) + 24 <= fl \/ fl + 1 <= (ed - 24))
  /\ L5KA.zeros_at MV ((ed - 24) / 8 + SBL) 3 /\ L5.u32_at RSEGS MV (ed - 24) (ei_kind e1) /\ L5.u64_at RSEGS MV (ed - 16) (ei_len e1).

Lemma vis_facts_top Mq mdq LKq Awq crq kq a e1 rr enq : inv Mq mdq LKq Awq crq kq a enq -> PEC.en_stk enq = rev (e1 :: rr) -> ei_ok e1 ->
  let H := ahid Awq mdq in let MV := mrestrict H Mq in
  tfacts MV enq e1 rr /\ L5A.avis H (PEC.en_b enq + 24 * (Z.of_nat (length rr) + 1) - 24) 24.
Proof.
  intros INV HSTK E1OK. entry_facts. name_objs. cut_facts INV kq.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & GNF & GNV & GFLP).
  destruct ESq as [ESb ESk].
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq HHq) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _).
  set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *.
  pose proof EAq as (EV0 & EV8 & EV16 & EV24 & EV32 & EV40 & EV48 & EDEF & EACC & EK & ELEN & EDEP & EKB & EBLK & EITEMS).
  set (eb := PEC.en_b enq) in *. set (ek := PEC.en_k enq) in *.
  pose proof (PEC.ecap_nonneg ek) as CN. unfold PEC.ESZ in EV32, EV40, ELEN, EBLK, EITEMS.
  pose proof HSTK as Lestk.
  assert (HLEN : length (PEC.en_stk enq) = Datatypes.S (length rr)) by (rewrite Lestk, length_rev; reflexivity).
  rewrite HLEN in ELEN, EITEMS, EBLK. rewrite Nat2Z.inj_succ in ELEN, EBLK.
  set (m := Z.of_nat (length rr)) in *. assert (M0 : 0 <= m) by (unfold m; clear; lia).
  assert (EKP : 0 < ek) by (destruct (Z.eq_dec ek 0) as [Z0|NZ]; [exfalso; unfold PEC.ecap in ELEN; rewrite Z0 in ELEN; cbn in ELEN; clear - ELEN M0; lia| clear - EK NZ; lia]).
  destruct (EBLK EKP) as (EBAL & EBDEF & EBR & EBACC & EBANN). destruct EBR as (EB1 & EB2 & EB3 & EB4 & EB5 & EB6).
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in EB2. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in EB6.
  assert (ECAPB : PEC.ecap ek <= 2048).
  { clear - EK EKP. unfold PEC.ecap. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; lia. }
  assert (BINe : In (eb, 24 * PEC.ecap ek) (PEC.enc_own en)).
  { unfold PEC.enc_own. rewrite <- ESb, <- ESk. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  assert (BINq : In (eb, 24 * PEC.ecap ek) LBq) by (unfold LBq, EBX; apply in_or_app; left; apply in_or_app; left; exact BINe).
  pose proof (EITEMS (length rr) ltac:(clear; lia)) as TOP. rewrite Lestk in TOP. cbn [rev] in TOP. rewrite PEEK.nth_top in TOP. fold m in TOP.
  destruct TOP as (TK & TL & TC).
  pose proof E1OK as (_ & E1C & _). unfold TWO64 in E1C.
  set (ed := eb + 24 * (m + 1)).
  assert (ALend : ed mod 8 = 0) by (unfold ed; apply PEEK.al8_item; exact EBAL).
  replace (eb + 24 * m + 16) with (ed - 8) in TC by (unfold ed; clear; lia).
  replace (eb + 24 * m + 8) with (ed - 16) in TL by (unfold ed; clear; lia).
  replace (eb + 24 * m) with (ed - 24) in TK by (unfold ed; clear; lia).
  assert (OVA : eb + 24 * PEC.ecap ek <= ov \/ ov + 56 <= eb) by exact (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ eb (24 * PEC.ecap ek) ov 56 HHq BINq (PMAUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia)))).
  assert (BV : forall a0 n0, eb <= a0 -> a0 + n0 <= eb + 24 * PEC.ecap ek -> L5A.avis H a0 n0) by (intros a0 n0 X1 X2; exact (VBLK eb (24 * PEC.ecap ek) a0 n0 BINq X1 X2)).
  assert (AL8 : (ed - 8) mod 8 = 0) by (replace (ed - 8) with (ed + (-1) * 8) by lia; rewrite Z_mod_plus_full; exact ALend).
  assert (AL24 : (ed - 24) mod 8 = 0) by (replace (ed - 24) with (ed + (-3) * 8) by lia; rewrite Z_mod_plus_full; exact ALend).
  assert (ACC8 : PMSPA.accA Mq (ed - 8) 8) by (intros x Hx; apply EBACC; unfold ed in Hx; clear - Hx M0; lia).
  assert (ACC24 : PMSPA.accA Mq (ed - 24) 24) by (intros x Hx; apply EBACC; unfold ed in Hx; clear - Hx M0; lia).
  pose proof (PMKA.blk_shadow_vis L ar C HI LYa HIok LBq FF' LKq crq Awq Mq mdq eb (24 * PEC.ecap ek) (ed - 8) 8 HHq BINq ltac:(unfold ed; lia) ltac:(unfold ed; lia) AL8
                ltac:(clear; lia) ltac:(reflexivity) ACC8) as ZC.
  unfold SB in ZC. change (8 / 8) with 1 in ZC. fold H MV in ZC.
  pose proof (PMKA.blk_shadow_vis L ar C HI LYa HIok LBq FF' LKq crq Awq Mq mdq eb (24 * PEC.ecap ek) (ed - 24) 24 HHq BINq ltac:(unfold ed; lia) ltac:(unfold ed; lia) AL24
                ltac:(clear; lia) ltac:(reflexivity) ACC24) as ZC3.
  unfold SB in ZC3. change (24 / 8) with 3 in ZC3. fold H MV in ZC3.

  destruct (blk_facts Mq LKq crq Awq _ kq _ _ HHq BINq) as (B0 & B47 & BAPP & BCEIL & BFS). unfold FS_BYTES in BFS, GFS2.
  split; [| apply (BV (ed - 24) 24); unfold ed; clear - M0 ELEN; lia].
  unfold tfacts. cbv zeta. fold ov eb ek m. fold ed.
  split; [rewrite HLEN, Nat2Z.inj_succ; unfold m; clear; lia|]. split; [exact EKP|].
  split; [exact EB1|]. split; [unfold ed; clear - EB5 SPT M0 ELEN; lia|]. split; [exact ALend|]. split; [unfold ed; clear - M0 ELEN ECAPB; lia|].
  split.
  { apply (proj2 (L5A.writable_vis H Mq (ed - 24) 24 (BV (ed - 24) 24 ltac:(unfold ed; lia) ltac:(unfold ed; lia)) ltac:(unfold ed; lia) ltac:(unfold ed; lia))).
    apply (L5.writable_sub _ Mq eb (24 * PEC.ecap ek)); [apply (L5C.writable_of_defined RSEGS); [exact EBDEF| lia| lia]| unfold ed; lia| unfold ed; lia]. }
  split; [unfold ed; clear - EB6 M0 ELEN; lia|]. split; [exact ZC|].
  split; [unfold ed; clear - EB5 SLO M0 ELEN HFR; lia|]. split; [unfold ed; clear - OVA M0 ELEN; lia|].
  split; [apply (proj2 (L5A.u64_at_vis H Mq (ed - 8) _ (BV (ed - 8) 8 ltac:(unfold ed; lia) ltac:(unfold ed; lia)) ltac:(unfold ed; lia) ltac:(unfold ed; lia))); exact TC|].
  split; [exact E1C|]. split; [exact E1OK|]. split; [exact BINe|]. split; [unfold ed; clear - ELEN; lia|]. split; [clear - EB5 SPT; lia|].
  split; [unfold ed; clear - BFS GFS1 GFS2 M0 ELEN; lia|]. split; [unfold ed; clear - BAPP GF1 GF2 GF8 M0 ELEN B0; lia|]. split; [unfold ed, FS_BYTES in *; clear - BFS GFLP M0 ELEN; lia|].
  split; [exact ZC3|].
  split; [apply (proj2 (L5A.u32_at_vis H Mq (ed - 24) _ (BV (ed - 24) 4 ltac:(unfold ed; lia) ltac:(unfold ed; lia)) ltac:(unfold ed; lia) ltac:(unfold ed; lia))); exact TK|].
  apply (proj2 (L5A.u64_at_vis H Mq (ed - 16) _ (BV (ed - 16) 8 ltac:(unfold ed; lia) ltac:(unfold ed; lia)) ltac:(unfold ed; lia) ltac:(unfold ed; lia))); exact TL.
Qed.

Let LBe : list (Z * Z) := PEC.enc_own en ++ LBc0.
Let Wc : list L5.range := [(PESK.o_sink EE fb, 24)].
Lemma perm_e kq : Permutation (PESK.sink_own kq ++ LBe) (EBX kq ++ LBc0).
Proof. unfold LBe, EBX. rewrite <- !app_assoc. apply (Permutation_app_swap_app (PESK.sink_own kq) (PEC.enc_own en)). Qed.
Lemma wc_wapp : PMKA.wapp Wc.
Proof. intros rr [<-|[]]. exact (ws_wapp _ (or_intror (or_introl eq_refl))). Qed.

Lemma after_callee Mq mdq LKq Awq crq kq a Mx mdx LKx Awx crx kx d SCRc enq :
  inv Mq mdq LKq Awq crq kq a enq ->
  L5CA.ahpres L ar LBe FF' spc SCRc Wc Mq Mx -> 0 <= SCRc -> SCRc + FR <= 20480 ->
  ri_inv HI (PESK.sink_own kx ++ LBe) FF' LKx crx Awx Mx (vml_of mdx) -> L5CA.amodel_ok Awx mdx -> model_rt mdq mdx -> incl Awq Awx -> incl LKx LKq ->
  PESKA.sink_atA RSEGS L ar P Mx (PESK.o_sink EE fb) kx -> xlo + (a + d) <= PESK.sk_z kx <= xhi + (a + d) ->
  PMSP.credit_keep crq crx (PECA.pot_encA L ar P en kq) (PECA.pot_encA L ar P en kx) ->
  inv Mx mdx LKx Awx crx kx (a + d) enq /\ (forall a0, spc <= a0 < sp -> Mx (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
Proof.
  intros INV HP HS0 HS1 HHx AMx RTx IAx ILx SKAx CLx CKx. entry_facts. name_objs. cut_facts INV kq.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & GNF & GNV & GFLP).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKA.aobj_of_aobjA FF' osk 24 (PMAUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))) ltac:(rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8)) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & _).
  pose proof (ri_perm _ _ FF' LKx crx Awx Mx _ (perm_e kx) HHx) as HHx'.
  assert (OWs : forall a0, sp - 20480 <= a0 < sp -> L5.outside Wc a0) by (intros a0 Ha0 r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; fold osk; clear - Ha0 K2 SLO; lia).
  assert (BIx : BINV kx Mx mdx LKx crx Awx).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
             Wk Wk (EBX kq) (PEC.enc_own en) (EBX kx) Mq mdq LKq crq Awq Mx mdx LKx crx Awx SCRc Wc BI HP HHx' AMx RTx IAx ILx HS0).
    - unfold spc. clear - HS1; lia.
    - intros r0 a0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. fold osk in Hr. change (ff_bytes 1 / 8) with 16. unfold ocell. split; [clear - Hr K2 SLO GNF GNV; lia| unfold SB in AkS |- *; clear - Hr AkS; lia].
    - intros a0 _ Oa r0 [<-|[]]. exact (Oa _ (or_intror (or_introl eq_refl))).
    - intros a0 Oa. exact Oa. }
  assert (EK12 : L5SAR.ek L ar LBe FF' sp 20480 Wc Mq Mx).
  { apply (L5SAR.ek_callee L ar LBe [] FF' [] sp 20480 spc SCRc Wc Wc Mq Mx HP); [unfold spc; clear - HS1; lia| unfold spc; clear - HFR; lia| intros a0 _ O; exact O]. }
  assert (FRBq : forall f, In f FF' -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
  assert (BRBe : forall x, In x LBe -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
  { intros x Hx. apply (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHx). apply in_or_app. right. exact Hx. }
  split.
  - unfold inv. split; [exact BIx|]. split; [| split; [exact ESq|]].
    { apply (PMKA.stksh_keepA L ar LBe FF' sp 20480 Wc Mq Mx EK12 wc_wapp (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZq]. }
    split.
    { apply (PECFA.enc_keepA RSEGS EE L ar LBe FF' sp 20480 Wc Mq Mx EK12 wc_wapp FRBq BRBe ov fb enq (PMAUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia)))); [| | | exact EAq].
      - intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk. clear - Hi Eov Eosk; lia.
      - unfold LBe. destruct ESq as [ESb ESk]. unfold PEC.enc_own. rewrite ESb, ESk. apply incl_appl; apply incl_refl.
      - intros Hp i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk. destruct ESq as [ESb ESk]. rewrite ESk in Hp. rewrite ESb, ESk in Hi.
        destruct (eblk_facts (PEC.en_b en) (PEC.ESZ * PEC.ecap (PEC.en_k en)) ltac:(unfold PEC.enc_own; replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia); left; reflexivity))
          as (_ & _ & _ & _ & _ & _ & _ & _ & AP & _). destruct (AP osk 24 (AOF osk 24 ltac:(lia) ltac:(lia))); clear - H Hi; lia. }
    split; [exact SKAx|]. split; [exact CLx|]. unfold PMSP.credit_keep in CKq, CKx |- *. clear - CKq CKx. lia.
  - intros a0 Ha0. pose proof HP as (P2 & _). apply P2. split; [unfold spc in Ha0; clear - Ha0 SLO SHI SPT HFR; lia|]. split.
    + unfold aclient, aclient_g. right; left. split; [unfold spc in Ha0; clear - Ha0 SLO SHI SPT HFR; lia| intros Y; clear - Ha0 Y; lia].
    + apply OWs. unfold spc in Ha0; clear - Ha0 HFR; lia.
Qed.

Lemma pen_nonneg : 0 <= fst (PMSPA.scA L (PEC.pot_estack (PMSPA.HV L ar) (PEC.en_k en))) /\ 0 <= snd (PMSPA.scA L (PEC.pot_estack (PMSPA.HV L ar) (PEC.en_k en))).
Proof.
  pose proof CPRE as (_ & _ & EA & _). pose proof EA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EK & _).
  pose proof (PMA.ly_cost L C LY) as (KPM & BLIN & BOV).
  unfold PMSPA.scA, PEC.pot_estack, PEC.ESZ, PMSPA.HV, LibIfaceAB.heap_view. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead]. rewrite KPM, BOV, BLIN.
  assert (P2 : 2 ^ PEC.en_k en <= 2 ^ 12) by (apply Z.pow_le_mono_r; clear - EK; lia). clear - EK P2. split; nia.
Qed.

Lemma pb_call (a pv h ra0 : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq enq :
  inv Mq mdq LKq Awq crq kq a enq -> PESKA.spa_hb P h -> xhi + a <= h -> spc <= pv -> pv + 1 <= sp -> L5.ra_ok ra0 ->
  getr Rq (reg 1) = Z_to_bv 64 ra0 -> getr Rq (reg 2) = Z_to_bv 64 spc ->
  getr Rq (reg 10) = Z_to_bv 64 (PESK.o_sink EE fb) -> getr Rq (reg 11) = Z_to_bv 64 pv -> csk Rq ->
  (forall (fx2 : FPState) R2 Mx mdx LKx Awx crx kx, inv Mx mdx LKx Awx crx kx (a + 1) enq -> regs_preserved Rq R2 ->
      (forall a0, spc <= a0 < sp -> Mx (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R2 ra0 Mx mdx) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq PBPC Mq mdq) K.
Proof.
  intros INV HBh Ha PV1 PV2 RA0 Q1 Q2 Q10 Q11 QCS KX. entry_facts. name_objs. cut_facts INV kq. pose proof RA0 as (Hra1 & Hra2).
  pose proof (ri_perm _ _ FF' LKq crq Awq Mq _ (Permutation_sym (perm_e kq)) HHq) as HHY.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKA.aobj_of_aobjA FF' osk 24 (PMAUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & _).
  pose proof SKAq as (_ & _ & _ & _ & _ & KZCq & KCAPq & KC0q & KBLKq).
  pose proof pen_nonneg as PEN.
  pose proof PB as PBX. unfold PESKA.push_back_specA in PBX. cbn [pe_push_back EE PeCLayoutA.EADDR_A] in PBX.
  apply (PBX PMODE fxq Rq Mq mdq K LBe FF' LKq Awq crq osk pv spc ra0 kq HHY AMq K0); clear PBX.
  {
    split; [rewrite L5K.rl1; exact Q1|]. split; [exact RA0|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536. split.
    - unfold spc. apply (L5SAR.astk_sub ar Mq Mq sp 20480 FR 12288 ASTKq (mem_grows_refl Mq)); [clear - HFR; lia| clear; lia| clear - HFR; lia| exact SPC16].
    - unfold spc. apply (PMKA.shadow_zero_sub Mq (sp - 20480) 2560); [apply SPd8; reflexivity| | clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZq].
      replace (sp - FR - 12288) with (sp - (FR + 12288)) by lia. apply SPd8. clear - HFR; destruct HFR as [-> | ->]; reflexivity. }
  { apply (PMAUAR.ffroomA_push 4 0 FF LK LKq _ FRM ILKq); [exact NDFq| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp spc F 1 (spc + 32) FRS); [clear; lia| unfold spc; clear - HFR; lia]. }
  { rewrite L5K.rl10. exact Q10. }
  { rewrite L5K.rl11. exact Q11. }
  { exact SKAq. }
  { exact (PMAUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))). }
  { exact K8. }
  {
    split; [apply (L5.defined_sub Mq (sp - 20480) 20480 pv 1 SDEFq); unfold spc in PV1; clear - PV1 PV2 HFR; lia|].
    split; [apply (PESHZ.bat0_of_shadow_zero Mq (sp - 20480) 2560 pv SZq); [apply SPd8; reflexivity| unfold spc in PV1; clear - PV1 HFR; lia| clear - PV2; lia]|].
    split; [right; unfold spc in PV1; clear - K2 SLO PV1 HFR; lia|]. left. split; [exact PV1| clear - PV2 SHI; lia]. }
  { intros ZC. apply (PESKA.spao_next L P PO (PESK.sk_c kq) h KCAPq); [intros Hc; exact (proj1 (proj2 (proj2 (proj2 (proj2 (KBLKq Hc))))))| exact HBh| clear - ZC CLq Ha; lia]. }
  { unfold PMSP.credit_le, PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CRED, CKq |- *. cbn [fst snd] in CRED, CKq |- *. clear - CRED CKq PEN. lia. }
  intros fx2 R2 Mx mdx LKx Awx crx b2 RP2 SKA2 HP2 CK2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2.
  destruct (after_callee Mq mdq LKq Awq crq kq a Mx mdx LKx Awx crx (PESK.sk_push kq b2) 1 12288 enq INV HP2 ltac:(clear; lia) ltac:(clear - HFR; lia) HH2 AM2 MRT2 IAW2 ILK2 SKA2) as [INVx AGx].
  - unfold PESK.sk_push. destruct (PESK.sk_z kq <? PESK.sk_c kq); cbn [PESK.sk_z]; clear - CLq; lia.
  - unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CK2 |- *. cbn [fst snd] in CK2 |- *. clear - CK2. lia.
  - exact (KX fx2 R2 Mx mdx LKx Awx crx _ INVx RP2 AGx).
Qed.

Lemma ahpres_wenc Mf : L5CA.ahpres L ar LBc0 FF sp 20480 Wk M Mf -> L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M Mf.
Proof.
  intros (E & D & DK). change (PMSPA.pm_scr 4) with 20480. split; [| split; [exact D| exact DK]].
  intros a (Ha & Hc & Ho). apply E. split; [exact Ha|]. split; [exact Hc|]. apply wk_out.
  - intros X'. apply (Ho (PMSPA.o_v AD fb, 56)); [| unfold L5.in_rng; cbn [fst snd]; exact X']. unfold PEC.W_enc. cbn [app]. left; reflexivity.
  - intros X'. apply (Ho (PESK.o_sink EE fb, 24)); [| unfold L5.in_rng; cbn [fst snd]; exact X']. unfold PEC.W_enc. cbn [app]. right; left; reflexivity.
  - intros q m Hq X'. pose proof HHp as HHe. unfold EBX in HHe. rewrite <- app_assoc in HHe.
    exact (PMARS1.own_not_aclient L ar C HI HIok (PEC.enc_own en) (PESK.sink_own k ++ LBc0) FF LK cr Aw M _ q m a sp 20480 HHe Hq X' (L5SAR.aclient_appb L ar LBc0 (PESK.sink_own k) FF sp 20480 a Hc)).
Qed.

Lemma retire_agree (Ma Mb : word -> option byte) (Wx : Z -> Prop) :
  (forall a0, 0 <= a0 < 2 ^ 64 -> ~ PMAUK.WretX F fl 1 Wx a0 -> Mb (Z_to_bv 64 a0) = Ma (Z_to_bv 64 a0)) ->
  (forall a0, Wx a0 -> 0 <= a0 /\ (2147446784 + 17592186048512 <= a0 \/ a0 + 1 <= 2147446784)) ->
  (forall a0, 0 <= a0 -> a0 + 1 <= 2 ^ 47 -> (a0 + 1 <= F \/ F + 128 <= a0) -> (2147446784 + 17592186048512 <= a0 \/ a0 + 1 <= 2147446784) ->
      (a0 + 1 <= fl \/ fl + 1 <= a0) -> ~ Wx a0 -> Mb (Z_to_bv 64 a0) = Ma (Z_to_bv 64 a0))
  /\ (forall x, 0 <= x -> x + 1 <= 2 ^ 47 -> (x + 1 <= F \/ F + 128 <= x) -> Mb (Z_to_bv 64 (HeapIfaceA.S x)) = Ma (Z_to_bv 64 (HeapIfaceA.S x))).
Proof.
  intros AG WXa. pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & _).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  split.
  - intros a0 H0 H1 H2 H3 H4 H5. apply AG; [clear - H0 H1; Lia.lia|]. unfold PMAUK.WretX, PMAUK.Wret. change (ff_bytes 1) with 128. change (128 / 8) with 16. unfold SB.
    intros [[[Y|Y]|Y]|Y]; [clear - Y H2; Lia.lia| clear - Y H3 GF1 GF2 GF8; Lia.lia| clear - Y H4; Lia.lia| exact (H5 Y)].
  - intros x H0 H1 H2. apply AG; [unfold HeapIfaceA.S, SB; clear - H0 H1; Lia.lia|]. unfold PMAUK.WretX, PMAUK.Wret. change (ff_bytes 1) with 128. change (128 / 8) with 16. unfold SB.
    intros [[[Y|Y]|Y]|Y]; unfold HeapIfaceA.S, SB in Y; [clear - Y H0 H1 GFBIG; Lia.lia| clear - Y H2 GF8; Lia.lia| clear - Y H0 H1 GLBIG; Lia.lia|].
    destruct (WXa _ Y) as [W0 W1]. clear - W0 W1 H0 H1. Lia.lia.
Qed.

Lemma sink_retire Mq mdq LKq Awq crq kq a (Mf : word -> option byte) (Wx : Z -> Prop) enq :
  inv Mq mdq LKq Awq crq kq a enq ->
  (forall a0, 0 <= a0 < 2 ^ 64 -> ~ PMAUK.WretX F fl 1 Wx a0 -> Mf (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)) ->
  (forall a0, Wx a0 -> exists q m, In (q, m) (PEC.enc_own en) /\ q <= a0 < q + m) ->
  PESKA.sink_atA RSEGS L ar P Mf (PESK.o_sink EE fb) kq.
Proof.
  intros INV FZf WXin. entry_facts. name_objs. cut_facts INV kq.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & GNF & GNV & GFLP).
  assert (WXa : forall a0, Wx a0 -> 0 <= a0 /\ (2147446784 + 17592186048512 <= a0 \/ a0 + 1 <= 2147446784)).
  { intros a0 Xa. destruct (WXin a0 Xa) as (q & m & Hq & Xq). destruct (eblk_facts q m Hq) as (_ & _ & _ & _ & B0 & B47 & BAPP & _). clear - Xq B0 B47 BAPP; lia. }
  destruct (retire_agree Mq Mf Wx FZf WXa) as [AGa AGs].
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKA.aobj_of_aobjA FF' osk 24 (PMAUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & KBIG & _).
  apply (PECFA.sink_atA_agree RSEGS L ar Mq Mf P osk kq); [clear - K1; lia| clear - K3; lia| | | exact SKAq].
  - split; [| intros x Hx; apply AGs; clear - Hx K1 K3 AkF; lia].
    intros i Hi. apply AGa; [clear - Hi K1; lia| clear - Hi K3; lia| clear - Hi AkF; lia| clear - Hi KBIG; lia| clear - Hi AkL; lia|].
    intros Xi. destruct (WXin i Xi) as (q & m & Hq & Xq). destruct (eblk_facts q m Hq) as (_ & _ & _ & _ & _ & _ & _ & _ & AP & _).
    destruct (AP osk 24 (AOF osk 24 ltac:(lia) ltac:(lia))); clear - H Hi Xq; lia.
  - intros Hp. assert (IN : In (PESK.sk_b kq, PESK.sk_c kq) (EBX kq ++ LBc0)).
    { apply in_or_app; left. unfold EBX. apply in_or_app; right. unfold PESK.sink_own. replace (PESK.sk_c kq =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
    destruct (blk_facts Mq LKq crq Awq _ kq _ _ HHq IN) as (B0 & B47 & BAPP & BCEIL & BFS). unfold FS_BYTES in BFS, GFS2, GFLP.
    split; [clear - B0; lia|]. split; [clear - B47; lia|].
    split; [| intros x Hx; apply AGs; clear - Hx B0 B47 BFS GFS1 GFS2; lia].
    intros i Hi. apply AGa; [clear - Hi B0; lia| clear - Hi B47; lia| clear - Hi BFS GFS1 GFS2; lia| clear - Hi BAPP B0; lia| clear - Hi BFS GFLP; lia|].
    intros Xi. destruct (WXin i Xi) as (q & m & Hq & Xq). destruct (eblk_facts q m Hq) as (INq & EKP & Eq & Em & _).

    assert (NE : PESK.sk_b kq <> q).
    { intros E. pose proof (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HHq) as NDq. unfold LBq, EBX in NDq. rewrite map_app in NDq |- * || idtac. rewrite <- app_assoc in NDq.
      apply (PMASK.fst_neq_appA (PEC.enc_own en) (PESK.sink_own kq ++ LBc0) q m (PESK.sk_b kq) (PESK.sk_c kq) NDq Hq); [| symmetry; exact E].
      apply in_or_app; left. unfold PESK.sink_own. replace (PESK.sk_c kq =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
    destruct (PMASK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ (PESK.sk_b kq) (PESK.sk_c kq) q m HHq IN ltac:(apply in_or_app; left; unfold EBX; apply in_or_app; left; exact Hq) NE); clear - H Hi Xq; lia.
Qed.

Lemma finish_ro pcq (fxq : FPState) Rq Mq mdq LKq Awq crq kq (fx3 : FPState) R3 M3v enq edq :
  inv Mq mdq LKq Awq crq kq NB enq -> PEC.en_stk enq = [] -> PEC.en_depth enq = edq ->
  XF = ST xstk xpos xmore xdone xhalt xdepth xec [] edq (xlo + NB) (xhi + NB) xbad ->
  msteps RSEGS (mst fxq Rq pcq (mrestrict (ahid Awq mdq) Mq)) (mst fx3 R3 r M3v) -> mem_grows (mrestrict (ahid Awq mdq) Mq) M3v ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ PMAUK.Wret F fl 1 i -> M3v (Z_to_bv 64 i) = mrestrict (ahid Awq mdq) Mq (Z_to_bv 64 i)) ->
  L5.u8_at RSEGS M3v fl 0 -> regs_preserved R R3 ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcq Mq mdq) K.
Proof.
  intros INV HSTK HED HXF MS3 MG3 FRZ3 FL0 RP3. entry_facts. name_objs. cut_facts INV kq.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & GNF & GNV & GFLP).
  destruct ESq as [ESb ESk].
  pose proof KONT as KT. rewrite HXF in KT.
  unfold PMSPA.cfg.
  apply (PMAUK.retire_core L ar C HI LYa HIok M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
           Wk (EBX kq) Mq mdq LKq crq Awq fxq fx3 Rq pcq R3 r M3v K BI MS3 MG3 FRZ3 FL0).
  intros Mf mdf FZf AHf MRTf AMf HHf.
  assert (FZf' : forall a0, 0 <= a0 < 2 ^ 64 -> ~ PMAUK.WretX F fl 1 (fun _ => False) a0 -> Mf (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha N. apply FZf; [exact Ha|]. intros X'. apply N. left. exact X'. }
  destruct (retire_agree Mq Mf (fun _ => False) FZf' ltac:(intros a0 [])) as [AGa AGs].
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKA.aobj_of_aobjA FF' ov 56 (PMAUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia))) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2 & Q3 & _) & QBIG & _).
  assert (EAf : PECA.enc_atA RSEGS EE L ar Mf ov fb enq).
  { apply (PECFA.enc_atA_agree RSEGS EE L ar Mq Mf ov fb enq); [clear - Q1; lia| clear - Q3; lia| | | exact EAq].
    - split; [| intros x Hx; apply AGs; clear - Hx Q1 Q3 AvF; lia].
      intros i Hi. apply AGa; [clear - Hi Q1; lia| clear - Hi Q3; lia| clear - Hi AvF; lia| clear - Hi QBIG; lia| clear - Hi AvL; lia| intros []].
    - intros Hp. rewrite ESk in Hp. rewrite ESb, ESk. assert (IN : In (PEC.en_b en, PEC.ESZ * PEC.ecap (PEC.en_k en)) (EBX kq ++ LBc0)).
      { apply in_or_app; left. unfold EBX. apply in_or_app; left. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
      destruct (blk_facts Mq LKq crq Awq _ kq _ _ HHq IN) as (B0 & B47 & BAPP & BCEIL & BFS). unfold FS_BYTES in BFS, GFS2, GFLP.
      split; [clear - B0; lia|]. split; [clear - B47; lia|].
      split; [| intros x Hx; apply AGs; clear - Hx B0 B47 BFS GFS1 GFS2; lia].
      intros i Hi. apply AGa; [clear - Hi B0; lia| clear - Hi B47; lia| clear - Hi BFS GFS1 GFS2; lia| clear - Hi BAPP B0; lia| clear - Hi BFS GFLP; lia| intros []]. }
  pose proof (sink_retire Mq mdq LKq Awq crq kq NB Mf (fun _ => False) enq INV FZf' ltac:(intros a0 [])) as SKAf.
  destruct (keepf Mf (proj1 AHf)) as (PA' & IA' & VREF' & BASE' & ERR' & CONT' & ECS' & ACCR').
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & TBOK & _ & CL & _ & ECI & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad X] in Lmore, Ldone, Ldepth, Lstk, Lpos, Lestk, Ledepth, Lz, Lbad.
  apply (KT fx3 R3 Mf mdf LKq Awq enq kq e crq).
  - exact RP3.
  - unfold PECA.crun_preA. fold op ov ois osk.
    split; [exact PA'|]. split; [exact IA'|]. split; [exact EAf|]. split; [exact VREF'|]. split; [exact SKAf|].
    split; [exact BASE'|]. split; [exact ERR'|]. split; [exact TBOK|]. split; [exact CONT'|].
    split.
    { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad].
      split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
      split; [rewrite HSTK; reflexivity|]. split; [exact HED|]. split; [clear - CLq; lia| exact Lbad]. }
    cbn [s_ec]. split; [exact ECS'|]. split; [exact ECI| exact ACCR'].
  - intros E1; exact E1.
  - exact (ahpres_wenc Mf AHf).
  - unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CKq |- *. cbn [fst snd] in CKq |- *. rewrite ESk. clear - CKq. lia.
  - exact MRTf.
  - exact ILKq.
  - exact IAWq.
  - exact AMf.
  - exact (ri_perm _ _ FF LKq crq Awq Mf _ (perm_qe kq enq ESb ESk) HHf).
Qed.

Lemma finish_bump pcq (fxq : FPState) Rq Mq mdq LKq Awq crq kq (fx3 : FPState) R3 M3v e1 rr enq edq :
  inv Mq mdq LKq Awq crq kq NB enq -> PEC.en_stk enq = rev (e1 :: rr) -> ei_ok e1 -> PEC.en_depth enq = edq ->
  XF = ST xstk xpos xmore xdone xhalt xdepth xec (PEEK.ebump (e1 :: rr)) edq (xlo + NB) (xhi + NB) xbad ->
  let ed := PEC.en_b enq + 24 * (Z.of_nat (length rr) + 1) in
  msteps RSEGS (mst fxq Rq pcq (mrestrict (ahid Awq mdq) Mq)) (mst fx3 R3 r M3v) -> mem_grows (mrestrict (ahid Awq mdq) Mq) M3v ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ PMAUK.Wret F fl 1 i -> ~ (ed - 8 <= i < ed - 8 + 8) -> M3v (Z_to_bv 64 i) = mrestrict (ahid Awq mdq) Mq (Z_to_bv 64 i)) ->
  L5.u64_at RSEGS M3v (ed - 8) ((ei_cnt e1 + 1) mod 2 ^ 64) -> L5.u8_at RSEGS M3v fl 0 -> regs_preserved R R3 ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcq Mq mdq) K.
Proof.
  intros INV HSTK E1OK HED HXF ed MS3 MG3 FRZ3 C8 FL0 RP3. entry_facts. name_objs. cut_facts INV kq.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & GNF & GNV & GFLP).
  destruct (vis_facts_top Mq mdq LKq Awq crq kq NB e1 rr enq INV HSTK E1OK) as ((HLEN & EKP & EB1 & ED2 & ALend & ED3 & _ & EB6 & _ & EDS & OVA & _ & E1C & _ & BINe & EDC & EBC & EDF & EDSH & EDFL & _) & EDV).
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & TBOK & _ & CL & _ & ECI & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad X] in Lmore, Ldone, Ldepth, Lstk, Lpos, Lestk, Ledepth, Lz, Lbad.
  pose proof KONT as KT. rewrite HXF in KT.
  pose proof (enc_eta enq) as EN.
  pose proof EAq as EAq'. rewrite EN in EAq'. rewrite HSTK, HED in EAq'.
  destruct ESq as [ESb ESk].
  set (eb := PEC.en_b enq) in *. set (ek := PEC.en_k enq) in *.
  set (m := Z.of_nat (length rr)) in *. assert (M0 : 0 <= m) by (unfold m; clear; lia).
  destruct e1 as [kd ln cn]. cbn [ei_kind ei_len ei_cnt] in C8, E1C, KT.
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKA.aobj_of_aobjA FF' ov 56 (PMAUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia))) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2' & Q3 & Q4 & Q5) & QBIG & _).
  assert (BINq : In (eb, 24 * PEC.ecap ek) LBq) by (unfold LBq, EBX; apply in_or_app; left; apply in_or_app; left; exact BINe).
  destruct (blk_facts Mq LKq crq Awq _ kq _ _ HHq BINq) as (B0 & B47 & BAPP & BCEIL & BFS). unfold FS_BYTES in BFS, GFS2, GFLP.
  set (Wx := fun a0 => ed - 8 <= a0 < ed - 8 + 8).
  unfold PMSPA.cfg.
  apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
           Wk (EBX kq) Mq mdq LKq crq Awq Wx fxq fx3 Rq pcq R3 r M3v K BI).
  { intros a0 Xa. unfold Wx in Xa. split.
    - unfold aclientw, aclient_g. left. exists (eb, 24 * PEC.ecap ek). split; [exact BINq|]. cbn [fst snd]. unfold ed in Xa. clear - Xa M0 EDC; lia.
    - intros O. apply (O (eb, 24 * PEC.ecap ek)); [right; right; exact BINe| unfold L5.in_rng; cbn [fst snd]; unfold ed in Xa; clear - Xa M0 EDC; lia]. }
  { intros a0. unfold Wx. clear. lia. }
  { exact MS3. }
  { exact MG3. }
  { intros a0 Ha N. apply FRZ3; [exact Ha| intros X'; apply N; left; exact X'| intros X'; apply N; right; exact X']. }
  { exact FL0. }
  intros Mf mdf FZf MGf VISf AHf MRTf AMf HHf.
  assert (WXin : forall a0, Wx a0 -> exists q m0, In (q, m0) (PEC.enc_own en) /\ q <= a0 < q + m0).
  { intros a0 Xa. exists eb, (24 * PEC.ecap ek). split; [exact BINe|]. unfold Wx, ed in Xa. clear - Xa M0 EDC; lia. }
  assert (WXa : forall a0, Wx a0 -> 0 <= a0 /\ (2147446784 + 17592186048512 <= a0 \/ a0 + 1 <= 2147446784)) by (intros a0 Xa; unfold Wx, ed in Xa; clear - Xa B0 B47 BAPP M0 EDC; lia).
  destruct (retire_agree Mq Mf Wx FZf WXa) as [AGa AGs].
  assert (EDR : 4096 <= ed - 24 /\ ed <= 140737488355328) by (unfold ed; clear - EB1 ED2 M0; lia).
  assert (C8' : L5.u64_at RSEGS Mf (ed - 8) ((cn + 1) mod 2 ^ 64)).
  { apply (proj1 (L5A.u64_at_vis (ahid Awq mdq) Mf (ed - 8) _ (L5A.avis_sub _ (ed - 24) 24 (ed - 8) 8 EDV ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - EDR; lia) ltac:(clear - EDR; lia))).
    rewrite VISf. exact C8. }
  assert (EA3 : PECA.enc_atA RSEGS EE L ar Mf ov fb (PEC.ENC eb ek (rev (PEEK.ebump (EI kd ln cn :: rr))) edq)).
  { apply (enc_bumpA Mq Mf ov fb eb ek (EI kd ln cn :: rr) edq); [exact EAq'| clear - Q1; lia| clear - Q3; lia| intros _; unfold PEC.ESZ; clear - EB1 EBC; lia| | | | exact MGf|].
    - split; [| intros x Hx; apply AGs; clear - Hx Q1 Q3 AvF; lia]. intros i Hi. apply AGa; [clear - Hi Q1; lia| clear - Hi Q3; lia| clear - Hi AvF; lia| clear - Hi QBIG; lia| clear - Hi AvL; lia|].
      unfold Wx, ed. clear - Hi OVA M0. lia.
    - intros _ i Hi Ri Ni. apply AGa; [clear - Hi; lia| unfold PEC.ESZ in Ri; clear - Ri EBC; lia| unfold PEC.ESZ in Ri; clear - Ri BFS GFS1 GFS2; lia| unfold PEC.ESZ in Ri; clear - Ri BAPP B0; lia| unfold PEC.ESZ in Ri; clear - Ri BFS GFLP; lia|].
      cbn [PEEK.cc_rng length] in Ni. fold m in Ni. unfold PEC.ESZ in Ni. unfold Wx, ed. clear - Ni. lia.
    - intros _ x Hx. apply AGs; unfold PEC.ESZ in Hx; [clear - Hx EB1; lia| clear - Hx EBC; lia| clear - Hx BFS GFS1 GFS2; lia].
    - intros e2 rr' Hc. injection Hc as <- <-. cbn [ei_cnt]. fold m. unfold PEC.ESZ, TWO64. replace (eb + 24 * m + 16) with (ed - 8) by (unfold ed; clear; lia). exact C8'. }
  cbn [PEEK.ebump ei_kind ei_len ei_cnt] in EA3.
  pose proof (sink_retire Mq mdq LKq Awq crq kq NB Mf Wx enq INV FZf WXin) as SKAf.
  destruct (keepf Mf (proj1 AHf)) as (PA3 & IA3 & VREF3 & BASE3 & ERR3 & CONT3 & ECS3 & ACC3).
  apply (KT fx3 R3 Mf mdf LKq Awq (PEC.ENC eb ek (rev rr ++ [EI kd ln ((cn + 1) mod TWO64)]) edq) kq e crq).
  + exact RP3.
  + unfold PECA.crun_preA. fold op ov ois osk.
    split; [exact PA3|]. split; [exact IA3|]. split; [unfold TWO64; exact EA3|]. split; [exact VREF3|]. split; [exact SKAf|].
    split; [exact BASE3|]. split; [exact ERR3|]. split; [exact TBOK|]. split; [exact CONT3|].
    split.
    { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PEC.en_stk PEC.en_depth rev PEEK.ebump ei_kind ei_len ei_cnt].
      split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
      split; [reflexivity|]. split; [reflexivity|]. split; [clear - CLq; lia| exact Lbad]. }
    cbn [s_ec]. split; [exact ECS3|]. split; [exact ECI| exact ACC3].
  + intros E1; exact E1.
  + exact (ahpres_wenc Mf AHf).
  + unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CKq |- *. cbn [fst snd PEC.en_k] in CKq |- *. rewrite ESk. clear - CKq. lia.
  + exact MRTf.
  + exact ILKq.
  + exact IAWq.
  + exact AMf.
  + exact (ri_perm _ _ FF LKq crq Awq Mf _ (perm_qe kq (PEC.ENC eb ek (rev rr ++ [EI kd ln ((cn + 1) mod TWO64)]) edq) ESb ESk) HHf).
Qed.

Lemma frame_agreeX (Ma Mb : word -> option byte) (Wp Wx : Z -> Prop) :
  (forall a, Wp a -> (spc <= a < sp) \/ (F <= a < F + 128) \/ (F / 8 + SB <= a < F / 8 + SB + 16) \/ Wx a) ->
  (forall a, Wx a -> 0 <= a /\ (2147446784 + 17592186048512 <= a \/ a + 1 <= 2147446784)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
  (forall a, 0 <= a -> a + 1 <= ahl_ceil ar -> (a + 1 <= F \/ F + 128 <= a) -> (2147446784 + 17592186048512 <= a \/ a + 1 <= 2147446784) -> ~ Wx a ->
      Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a))
  /\ (forall x, 0 <= x -> x + 1 <= 2 ^ 47 -> (x + 1 <= F \/ F + 128 <= x) -> Mb (Z_to_bv 64 (HeapIfaceA.S x)) = Ma (Z_to_bv 64 (HeapIfaceA.S x))).
Proof.
  intros WP WXa AG. entry_facts.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & _).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  split.
  - intros a H0 H1 H2 H3 H4. apply AG; [clear - H0 H1 SPT; Lia.lia|]. intros X'. destruct (WP a X') as [Y|[Y|[Y|Y]]].
    + unfold spc in Y. clear - Y H1 SLO HFR. Lia.lia.
    + clear - Y H2. Lia.lia.
    + unfold SB in Y. clear - Y H3 GF1 GF2 GF8. Lia.lia.
    + exact (H4 Y).
  - intros x H0 H1 H2. apply AG; [unfold HeapIfaceA.S, SB; clear - H0 H1; Lia.lia|]. intros X'. destruct (WP _ X') as [Y|[Y|[Y|Y]]]; unfold HeapIfaceA.S, SB in Y.
    + unfold spc in Y. clear - Y H0 H1 SLO SPT HFR. Lia.lia.
    + clear - Y H0 H1 GFBIG. Lia.lia.
    + clear - Y H2 GF8. Lia.lia.
    + destruct (WXa _ Y) as [W0 W1]. unfold HeapIfaceA.S, SB in W0, W1. clear - W0 W1 H0 H1. Lia.lia.
Qed.

Lemma inv_depthw (Ma Mb : word -> option byte) (Wp : Z -> Prop) mda mdb LKc crc Awc kc a enq d' :
  inv Ma mda LKc Awc crc kc a enq ->
  ri_inv HI (EBX kc ++ LBc0) FF' LKc crc Awc Mb (vml_of mdb) -> L5CA.amodel_ok Awc mdb -> model_rt mda mdb -> mem_grows Ma Mb ->
  (forall a0, Wp a0 -> (spc <= a0 < sp /\ ~ ocell sp NSV a0) \/ (F <= a0 < F + 128) \/ (F / 8 + SB <= a0 < F / 8 + SB + 16)
                      \/ (PMSPA.o_v AD fb + 48 <= a0 < PMSPA.o_v AD fb + 52)) ->
  (forall a0, 0 <= a0 < 2 ^ 64 -> ~ Wp a0 -> Mb (Z_to_bv 64 a0) = Ma (Z_to_bv 64 a0)) ->
  L5.u32_at RSEGS Mb (PMSPA.o_v AD fb + 48) d' -> 0 <= d' <= MAX_DEPTH + 1 ->
  inv Mb mdb LKc Awc crc kc a (PEC.ENC (PEC.en_b enq) (PEC.en_k enq) (PEC.en_stk enq) d').
Proof.
  intros INV HHb AMb RTb MG WP AG U48 Hd'. entry_facts. name_objs. cut_facts INV kc.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & _ & _ & GFLP).
  destruct ESq as [ESb ESk].
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKc crc Awc Ma mda ov 56 sp 20480 HHq (PMKA.aobj_of_aobjA FF' ov 56 (PMAUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia))) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2 & Q3 & _) & QBIG & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKc crc Awc Ma mda osk 24 sp 20480 HHq (PMKA.aobj_of_aobjA FF' osk 24 (PMAUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & KBIG & _).
  set (Wx := fun a0 => ov + 48 <= a0 < ov + 52).
  assert (WP' : forall a0, Wp a0 -> (spc <= a0 < sp) \/ (F <= a0 < F + 128) \/ (F / 8 + SB <= a0 < F / 8 + SB + 16) \/ Wx a0).
  { intros a0 X'. destruct (WP a0 X') as [[Y _]|[Y|[Y|Y]]]; [left| right; left| right; right; left| right; right; right]; exact Y. }
  assert (WXa : forall a0, Wx a0 -> 0 <= a0 /\ (2147446784 + 17592186048512 <= a0 \/ a0 + 1 <= 2147446784)) by (intros a0 Xa; unfold Wx in Xa; clear - Xa Q1 QBIG; lia).
  destruct (frame_agreeX Ma Mb Wp Wx WP' WXa AG) as [AGa AGs].
  unfold inv. split.
  { apply (PMAUK.binv_pieceW L ar HI M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
             Wk (EBX kc) Ma mda LKc crc Awc Mb mdb Wp BI HHb AMb RTb MG AG).
    intros a0 X'. destruct (WP a0 X') as [[Y N]|[Y|[Y|Y]]].
    - split; [exact N| left; exact Y].
    - split; [unfold ocell; clear - Y GFC SLO HNF HFR; lia| right; left; change (ff_bytes 1) with 128; exact Y].
    - split; [unfold ocell, SB in Y |- *; clear - Y GF1 GF2 GF8 SLO SPT HNF HFR; Lia.lia| right; right; left; change (ff_bytes 1 / 8) with 16; exact Y].
    - split; [unfold ocell; clear - Y Q2 SLO HNF HFR; lia| right; right; right]. intros O. apply (O (ov, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
  split.
  { intros jj Hjj. pose proof (SZq jj Hjj) as Z0. unfold byte_at in Z0 |- *.
    replace (HeapIfaceA.S (sp - 20480) + jj) with (HeapIfaceA.S (sp - 20480 + jj * 8)) in Z0 |- * by (unfold HeapIfaceA.S; rewrite Z.div_add by (clear; lia); clear; lia).
    rewrite (AGs (sp - 20480 + jj * 8)); [exact Z0| clear - Hjj SLO SPT; lia| clear - Hjj SHI SPT; lia| clear - Hjj GFC SLO; lia]. }
  split; [split; [exact ESb| exact ESk]|].
  split.
  { pose proof (enc_eta enq) as EN. rewrite EN in EAq.
    apply (enc_depthA Ma Mb ov fb (PEC.en_b enq) (PEC.en_k enq) (PEC.en_stk enq) (PEC.en_depth enq) d' EAq); [clear - Q1; lia| clear - Q3; lia| | | | | exact MG| exact U48| exact Hd'].
    - intros Hp. rewrite ESk in Hp. rewrite ESb, ESk.
      assert (IN : In (PEC.en_b en, PEC.ESZ * PEC.ecap (PEC.en_k en)) (EBX kc ++ LBc0)).
      { apply in_or_app; left. unfold EBX. apply in_or_app; left. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
      destruct (blk_facts Ma LKc crc Awc _ kc _ _ HHq IN) as (B0 & B47 & _). clear - B0 B47; lia.
    - intros i Hi Ri Ni. apply AGa; [clear - Hi Q1; lia| clear - Ri Q2; lia| clear - Ri AvF; lia| clear - Ri QBIG; lia| unfold Wx; exact Ni].
    - intros x Hx. apply AGs; [clear - Hx Q1; lia| clear - Hx Q3; lia| clear - Hx AvF; lia].
    - intros Hp. rewrite ESk in Hp. rewrite ESb, ESk.
      assert (IN : In (PEC.en_b en, PEC.ESZ * PEC.ecap (PEC.en_k en)) (EBX kc ++ LBc0)).
      { apply in_or_app; left. unfold EBX. apply in_or_app; left. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
      destruct (blk_facts Ma LKc crc Awc _ kc _ _ HHq IN) as (B0 & B47 & BAPP & BCEIL & BFS). unfold FS_BYTES in BFS, GFS2.
      pose proof (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ ov 56 HHq IN (PMAUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia)))) as BOV.
      split; [intros i Hi; apply AGa; [clear - Hi B0; lia| clear - Hi BCEIL; lia| clear - Hi B0 BFS GFS1 GFS2; lia| clear - Hi BAPP B0; lia| unfold Wx; clear - Hi BOV; lia] | intros x Hx; apply AGs; clear - Hx B0 B47 BFS GFS1 GFS2; lia]. }
  split.
  { apply (PECFA.sink_atA_agree RSEGS L ar Ma Mb P osk kc); [clear - K1; lia| clear - K3; lia| | | exact SKAq].
    - split; [intros i Hi; apply AGa; [clear - Hi K1; lia| clear - Hi K2; lia| clear - Hi AkF; lia| clear - Hi KBIG; lia| unfold Wx; clear - Hi Eov Eosk; lia] | intros x Hx; apply AGs; clear - Hx K1 K3 AkF; lia].
    - intros Hp. assert (IN : In (PESK.sk_b kc, PESK.sk_c kc) (EBX kc ++ LBc0)).
      { apply in_or_app; left. unfold EBX. apply in_or_app; right. unfold PESK.sink_own. replace (PESK.sk_c kc =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
      destruct (blk_facts Ma LKc crc Awc _ kc _ _ HHq IN) as (B0 & B47 & BAPP & BCEIL & BFS). unfold FS_BYTES in BFS, GFS2.
      pose proof (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ (PESK.sk_b kc) (PESK.sk_c kc) ov 56 HHq IN (PMAUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia)))) as KOV.
      split; [clear - B0; lia|]. split; [clear - B47; lia|].
      split; [intros i Hi; apply AGa; [clear - Hi B0; lia| clear - Hi BCEIL; lia| clear - Hi B0 BCEIL BAPP BFS GFS1 GFS2; lia| clear - Hi BAPP B0; lia| unfold Wx; clear - Hi KOV; lia] | intros x Hx; apply AGs; clear - Hx B0 B47 BFS GFS1 GFS2; lia]. }
  split; [exact CLq| exact CKq].
Qed.

Definition pop_run (pcq ra0 : Z) (QR : bvmap 5 word -> Prop) (fxq : FPState) (Rq : bvmap 5 word) (enq : PEC.enc) (e1 : eitem) (rr : list eitem) : Prop :=
  forall (MV : word -> option byte),
    sfacts MV -> L5.img_clear MV 65536 1286144 -> L5.writable RSEGS MV (spc - 16) 16 -> PMSPA.o_v AD fb + 56 <= spc - 16 -> ffacts MV false -> owns SAVED sp R MV -> ofacts MV enq -> tfacts MV enq e1 rr ->
    exists (fx3 : FPState) (R3 : bvmap 5 word) (M3v : word -> option byte),
      msteps RSEGS (mst fxq Rq pcq MV) (mst fx3 R3 SHRPC M3v) /\ mem_grows MV M3v
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (PMSPA.o_v AD fb + 32 <= i < PMSPA.o_v AD fb + 40) -> ~ (spc - 16 <= i < spc) -> M3v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
      /\ L5.u64_at RSEGS M3v (PMSPA.o_v AD fb + 32) (PEC.en_b enq + 24 * Z.of_nat (length rr))
      /\ getr R3 (reg 10) = Z_to_bv 64 (PMSPA.o_v AD fb + 24) /\ getr R3 (reg 11) = Z_to_bv 64 (Z.of_nat (length rr) + 1)
      /\ getr R3 (reg 1) = Z_to_bv 64 ra0 /\ getr R3 (reg 2) = Z_to_bv 64 spc /\ csk R3 /\ QR R3.

Lemma pop_call (pcq ra0 : Z) (QR : bvmap 5 word -> Prop) (fxq : FPState) Rq Mq mdq LKq Awq crq kq a enq e1 rr :
  inv Mq mdq LKq Awq crq kq a enq -> PEC.en_stk enq = rev (e1 :: rr) -> ei_ok e1 -> L5.ra_ok ra0 ->
  pop_run pcq ra0 QR fxq Rq enq e1 rr ->
  (forall (fx4 : FPState) R3 R4 M4 md4 LK4 Aw4,
      inv M4 md4 LK4 Aw4 crq kq a (PEC.ENC (PEC.en_b enq) (PEC.en_k enq) (rev rr) (PEC.en_depth enq)) -> QR R3 -> regs_preserved R3 R4 ->
      (forall a0, spc <= a0 < sp -> M4 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx4) R4 ra0 M4 md4) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcq Mq mdq) K.
Proof.
  intros INV HSTK E1OK RA0 RUN KX. entry_facts. name_objs. cut_facts INV kq. pose proof RA0 as (Hra1 & Hra2).
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & GNF & GNV & GFLP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  destruct (vis_facts Mq mdq LKq Awq crq kq a enq INV) as (SF & FFc & OWN & OF & VSv & VFv & VSHv & VFLv & QVIS & KVIS).
  destruct (vis_facts_top Mq mdq LKq Awq crq kq a e1 rr enq INV HSTK E1OK) as (TF & EDV).
  pose proof TF as (HLEN & EKP & EB1 & ED2 & ALend & ED3 & _ & EB6 & _ & EDS & OVA & _ & E1C & _ & BINe & EDC & EBC & EDF & EDSH & EDFL & _).
  set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *.
  destruct (keepf Mq EKq) as (_ & _ & _ & BASEq & _).
  assert (RO3 : L5.img_clear MV 65536 1286144) by (apply L5A.img_clear_mrestrict; exact (proj1 BASEq)).
  assert (WR16 : L5.writable RSEGS MV (spc - 16) 16).
  { destruct (PMASK.stk_vis L ar C HI LY HIok _ FF' LKq crq Awq Mq mdq sp 20480 (FR + 16) HHq ASTKq ltac:(clear - HFR; lia)) as (_ & _ & SWR16).
    unfold spc. apply (L5.writable_sub _ _ (sp - (FR + 16)) (FR + 16)); [exact SWR16| clear; lia| clear - HFR; lia]. }
  destruct ESq as [ESb ESk].
  set (eb := PEC.en_b enq) in *. set (ek := PEC.en_k enq) in *.
  set (m := Z.of_nat (length rr)) in *. assert (M0 : 0 <= m) by (unfold m; clear; lia).
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKA.aobj_of_aobjA FF' ov 56 (PMAUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia))) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1' & Q2' & Q3' & _) & QBIG & QDEF & _).
  destruct (RUN MV SF RO3 WR16 ltac:(unfold spc; clear - Q2' SLO HFR; lia) FFc OWN OF TF) as (fx3 & R3 & M3v & MS3 & MG3 & FRZ3 & U32v & Q10 & Q11 & Q1 & Q2 & QCS & HQR). clear RUN.
  assert (BINq : In (eb, 24 * PEC.ecap ek) LBq) by (unfold LBq, EBX; apply in_or_app; left; apply in_or_app; left; exact BINe).
  destruct (blk_facts Mq LKq crq Awq _ kq _ _ HHq BINq) as (B0 & B47 & BAPP & BCEIL & BFS). unfold FS_BYTES in BFS, GFS2.
  pose proof EAq as (EV0 & EV8 & EV16 & EV24 & EV32 & EV40 & EV48 & EDEF & EACC & EK & ELEN & EDEP & EKB & EBLK & EITEMS). fold eb ek in EV24, EV32, EV40, EK, ELEN, EKB, EBLK, EITEMS.
  destruct (EBLK EKP) as (EBAL & EBDEF & EBR & EBACC & EBANN). rewrite HSTK, length_rev in EV32, ELEN, EBACC, EBANN. cbn [length] in EV32, ELEN, EBACC, EBANN.
  rewrite Nat2Z.inj_succ in EV32, ELEN, EBACC, EBANN. fold m in EV32, ELEN, EBACC, EBANN. unfold PEC.ESZ in EV32, EV40, ELEN, EBDEF, EBACC, EBANN.

  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq fxq fx3 Rq pcq R3 SHRPC M3v (fun a0 => ov + 32 <= a0 < ov + 40 \/ spc - 16 <= a0 < spc) K HHq AMq MS3 MG3).
  { intros a0 Ha N. apply FRZ3; [exact Ha| intros X'; apply N; left; exact X'| intros X'; apply N; right; exact X']. }
  { intros a0 Ha [Wa|Wa].
    - split; [| clear - Wa Q1'; lia]. unfold aclientw, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [right; exact Hfb|].
      cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. split; [clear - Wa Eov; lia| intros Y; clear - Wa Y Eov; lia].
    - split; [| unfold spc in Wa; clear - Wa SLO SPT HFR Q1' Q2'; lia]. unfold aclientw, aclient_g. right; left. split; [unfold spc in Wa; clear - Wa SLO SHI SPT HFR; lia| intros Y; clear - Y; lia]. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (BI3 : BINV kq M3 md3 LKq crq Awq).
  { pose proof G as G'. destruct G' as [_ _ _ _ _ GOCR GOWNAG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    destruct BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold BINV, PMAUK.binv.
    split; [exact HH3|]. split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans _ _ _ B3 MRT3)|]. split; [exact B4|]. split; [exact B5|].
    split; [exact (L5SAR.astk_grows ar Mq M3 sp 20480 B6 MGM3)|].
    split. { eapply L5SAR.ek_trans; [exact B7|]. intros a0 (Ha & Hc & Ho). apply FR3; [exact Ha|]. intros [Y|Y].
             - apply (Ho (ov, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia].
             - destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 20480 a0 HHp SPT (L5SAR.aclient_appb L ar LBc0 (EBX k) FF sp 20480 a0 Hc)) as [Z1|Z1];
                 unfold spc in Y; [clear - Y Z1 HFR; lia| clear - Y Z1 SLO HFR; lia]. }
    split. { eapply L5SAR.dk_trans; [exact B8|]. apply L5SAR.dk_grows. exact MGM3. }
    split. { apply (GOWNAG Mq M3 B9). intros a0 Ha. apply FR3; [pose proof (GOCR a0 Ha) as OC; clear - OC SLO SHI SPT HNF HFR; lia|]. intros [Y|Y]; pose proof (GOCR a0 Ha) as OC; unfold ocell in OC; [clear - Y OC Q2' SLO HNF HFR; lia| unfold spc in Y; clear - Y OC HNF HFR; lia]. }
    eapply L5.defined_grows; [exact MGM3| exact B10]. }
  pose proof BI3 as (_ & _ & _ & _ & _ & ASTK3 & EK3 & DK3 & OWN3 & FSD3). pose proof ASTK3 as (_ & _ & _ & _ & SDEF3 & _).
  assert (AG3 : forall a0, 0 <= a0 -> a0 + 1 <= 2 ^ 64 -> ~ (ov + 32 <= a0 < ov + 40) -> ~ (spc - 16 <= a0 < spc) -> M3 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0))
    by (intros a0 X1 X2 N N'; apply FR3; [clear - X1 X2; lia| intros [Y|Y]; [exact (N Y)| exact (N' Y)]]).

  assert (NSS : forall x, 0 <= x -> x + 1 <= 2 ^ 47 -> ~ (spc - 16 <= HeapIfaceA.S x < spc)) by (intros x X1 X2; unfold HeapIfaceA.S, SB, spc; clear - X1 X2 SLO SHI SPT HFR; lia).
  assert (NSC : forall a0, a0 + 1 <= ahl_ceil ar -> ~ (spc - 16 <= a0 < spc)) by (intros a0 X1; unfold spc; clear - X1 SLO HFR; lia).
  assert (SZ3 : shadow_zero M3 (sp - 20480) 2560).
  { intros jj Hjj. pose proof (SZq jj Hjj) as Z0. unfold byte_at in Z0 |- *. rewrite AG3; [exact Z0| unfold HeapIfaceA.S, SB; clear - Hjj SLO SPT; lia| unfold HeapIfaceA.S, SB; clear - Hjj SHI SPT; lia| unfold HeapIfaceA.S, SB; clear - Hjj QBIG SLO SHI SPT; lia| unfold HeapIfaceA.S, SB, spc; clear - Hjj SLO SHI SPT HFR; lia]. }
  assert (U32 : L5.u64_at RSEGS M3 (ov + 32) (eb + 24 * m)).
  { apply (proj1 (L5A.u64_at_vis H M3 (ov + 32) _ (L5A.avis_sub _ ov 56 (ov + 32) 8 QVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - Q1'; lia) ltac:(clear - Q3'; lia))). unfold H. rewrite VIS3. exact U32v. }

  assert (PERM3 : Permutation (EBX kq ++ LBc0) ([(eb, 24 * PEC.ecap ek)] ++ (PESK.sink_own kq ++ LBc0))).
  { unfold EBX. unfold PEC.enc_own. rewrite <- ESb, <- ESk. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; clear - EKP; lia). rewrite <- app_assoc. apply Permutation_refl. }
  pose proof (ri_perm _ _ FF' LKq crq Awq M3 _ PERM3 HH3) as HH3'.
  pose proof ESHR as SHX. unfold PEAEKAN.ann_shrink_e_spec in SHX.
  apply (SHX fx3 R3 M3 md3 K (PESK.sink_own kq ++ LBc0) FF' LKq Awq crq (ov + 24) (m + 1) eb (24 * m) (24 * PEC.ecap ek) spc ra0 HH3' AM3 K0); clear SHX.
  {
    split; [rewrite L5K.rl1; exact Q1|]. split; [exact RA0|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536. split.
    - unfold spc. apply (L5SAR.astk_sub ar M3 M3 sp 20480 FR 12288 ASTK3 (mem_grows_refl M3)); [clear - HFR; lia| clear; lia| clear - HFR; lia| exact SPC16].
    - unfold spc. apply (PMKA.shadow_zero_sub M3 (sp - 20480) 2560); [apply SPd8; reflexivity| | clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZ3].
      replace (sp - FR - 12288) with (sp - (FR + 12288)) by lia. apply SPd8. clear - HFR; destruct HFR as [-> | ->]; reflexivity. }
  { apply (PMAUAR.ffrsA_push FF sp spc F 1 (spc + 32) FRS); [clear; lia| unfold spc; clear - HFR; lia]. }
  { rewrite L5K.rl10. exact Q10. }
  { rewrite L5K.rl11. unfold m. exact Q11. }
  { exact (PMAUAR.aobjA_push FF (ov + 24) 24 _ (AOF (ov + 24) 24 ltac:(lia) ltac:(lia))). }
  { rewrite Eov. replace (fb + 496 + 24) with (fb + 8 * 65) by (clear; lia). apply FB8. }
  { intros x Hx. unfold byte_at, HeapIfaceA.S. rewrite AG3; [exact (EACC x ltac:(clear - Hx; lia))| unfold SB; clear - Hx Q1'; lia| unfold SB; clear - Hx Q3'; lia| unfold SB; clear - Hx Q1' Q3' QBIG; lia| apply NSS; clear - Hx Q1' Q3'; lia]. }
  {
    split; [apply (L5.defined_sub M3 ov 56); [exact (L5.defined_grows Mq M3 _ _ MGM3 EDEF)| clear; lia| clear; lia]|].
    split; [apply (L5C.u64_at_agree RSEGS Mq M3); [intros i Hi; apply AG3; [clear - Hi Q1' Q3'; lia| clear - Hi Q1' Q3'; lia| clear - Hi Q1' Q3'; lia| apply NSC; clear - Hi Q2'; lia]| clear - Q1'; lia| clear - Q3'; lia| exact EV24]|].
    split; [replace (ov + 24 + 8) with (ov + 32) by (clear; lia); exact U32|].
    split; [replace (ov + 24 + 16) with (ov + 40) by (clear; lia); apply (L5C.u64_at_agree RSEGS Mq M3); [intros i Hi; apply AG3; [clear - Hi Q1' Q3'; lia| clear - Hi Q1' Q3'; lia| clear - Hi Q1' Q3'; lia| apply NSC; clear - Hi Q2'; lia]| clear - Q1'; lia| clear - Q3'; lia| exact EV40]|].
    split; [clear - M0 ELEN; lia|]. split; [pose proof (PEC.ecap_nonneg ek); clear - H0 ELEN M0; lia|]. split; [exact EB1|].
    split; [exact (proj1 (proj2 (proj2 EBR)))|]. exact (L5.defined_grows Mq M3 _ _ MGM3 EBDEF). }
  { clear - M0 ELEN; lia. }
  { split.
    - intros x Hx. unfold byte_at, HeapIfaceA.S. rewrite AG3; [exact (EBACC x ltac:(clear - Hx; lia))| unfold SB; clear - Hx EB1; lia| unfold SB; clear - Hx EBC M0 ELEN; lia| unfold SB; clear - Hx B0 B47 M0 ELEN Q1' Q3' QBIG; lia| apply NSS; clear - Hx EB1 EBC M0 ELEN; lia].
    - apply (PECFA.annA_agree Mq M3); [clear - M0 ELEN; pose proof (PEC.ecap_nonneg ek); lia| exact EBAL| | exact EBANN].
      intros x Hx. unfold HeapIfaceA.S. apply AG3; [unfold SB; clear - Hx EB1; lia| unfold SB; clear - Hx EBC; lia| unfold SB; clear - Hx B0 B47 Q1' Q3' QBIG; lia| apply NSS; clear - Hx EB1 EBC; lia]. }
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 BAT4 BLK4 HP4 MRT4 ILK4 IAW4 AM4 HH4.
  change (PMSPA.pm_scr 0) with 12288 in HP4.
  pose proof (ri_perm _ _ FF' LK4 crq Aw4 M4 _ (Permutation_sym PERM3) HH4) as HH4'.

  assert (BI4 : BINV kq M4 md4 LK4 crq Aw4).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
             Wk Wk (EBX kq) (PESK.sink_own kq) (EBX kq) M3 md3 LKq crq Awq M4 md4 LK4 crq Aw4 12288 [] BI3 HP4 HH4' AM4 MRT4 IAW4 ILK4);
      [clear; lia| unfold spc; clear - HFR; lia| intros r0 a0 []| intros a0 _ _ r0 []| intros a0 Oa; exact Oa]. }
  assert (EK34 : L5SAR.ek L ar (PESK.sink_own kq ++ LBc0) FF sp 20480 [] M3 M4).
  { apply (L5SAR.ek_callee L ar (PESK.sink_own kq ++ LBc0) [] FF [(F, 1, spc + 32)] sp 20480 spc 12288 [] [] M3 M4); [exact HP4| unfold spc; clear - HFR; lia| unfold spc; clear - HFR; lia| intros a0 _ O; exact O]. }
  assert (FRB3 : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (BRB3 : forall x, In x (PESK.sink_own kq ++ LBc0) -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
  { intros x Hx. apply (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH3). unfold LBq, EBX. rewrite ?in_app_iff. rewrite in_app_iff in Hx. clear - Hx. tauto. }
  destruct (PMKA.agA_obj L ar (PESK.sink_own kq ++ LBc0) FF sp 20480 [] M3 M4 EK34 PMKA.wapp_nil FRB3 ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) ltac:(intros i _ r0 [])) as [AG34 SH34].
  pose proof (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ ov 56 HHq BINq (PMAUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia)))) as BOV.
  assert (SKA3 : PESKA.sink_atA RSEGS L ar P M3 osk kq).
  { pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKA.aobj_of_aobjA FF' osk 24 (PMAUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))) K8) ltac:(lia) ltac:(reflexivity))
      as ((K1 & K2 & K3 & _) & KBIG & _).
    apply (PECFA.sink_atA_agree RSEGS L ar Mq M3 P osk kq); [clear - K1; lia| clear - K3; lia| | | exact SKAq].
    - split; [intros i Hi; apply AG3; [clear - Hi K1 K3 Eov Eosk; lia| clear - Hi K1 K3 Eov Eosk; lia| clear - Hi K1 K3 Eov Eosk; lia| apply NSC; clear - Hi K2; lia]
             | intros x Hx; unfold HeapIfaceA.S; apply AG3; [unfold SB; clear - Hx K1 K3 Q1' Q3' QBIG; lia| unfold SB; clear - Hx K1 K3 Q1' Q3' QBIG; lia| unfold SB; clear - Hx K1 K3 Q1' Q3' QBIG; lia| apply NSS; clear - Hx K1 K3; lia]].
    - intros Hp. assert (IN : In (PESK.sk_b kq, PESK.sk_c kq) (EBX kq ++ LBc0)).
      { apply in_or_app; left. unfold EBX. apply in_or_app; right. unfold PESK.sink_own. replace (PESK.sk_c kq =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
      destruct (blk_facts Mq LKq crq Awq _ kq _ _ HHq IN) as (C0 & C47 & CAPP & CCEIL & _).
      pose proof (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ ov 56 HHq IN (PMAUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia)))) as KOV.
      split; [clear - C0; lia|]. split; [clear - C47; lia|].
      split; [intros i Hi; apply AG3; [clear - Hi C0 C47 KOV; lia| clear - Hi C0 C47 KOV; lia| clear - Hi C0 C47 KOV; lia| apply NSC; clear - Hi CCEIL; lia]
             | intros x Hx; unfold HeapIfaceA.S; apply AG3; [unfold SB; clear - Hx C0 C47 CAPP Q1' Q3' QBIG; lia| unfold SB; clear - Hx C0 C47 CAPP Q1' Q3' QBIG; lia| unfold SB; clear - Hx C0 C47 CAPP Q1' Q3' QBIG; lia| apply NSS; clear - Hx C0 C47; lia]]. }
  assert (INV4 : inv M4 md4 LK4 Aw4 crq kq a (PEC.ENC eb ek (rev rr) (PEC.en_depth enq))).
  { unfold inv. split; [exact BI4|].
    split; [apply (PMKA.stksh_keepA L ar (PESK.sink_own kq ++ LBc0) FF sp 20480 [] M3 M4 EK34 PMKA.wapp_nil (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZ3]|].
    split; [cbn [PEC.en_b PEC.en_k]; split; [exact ESb| exact ESk]|].
    split.
    { pose proof (enc_eta enq) as EN. pose proof EAq as EA0. rewrite EN, HSTK in EA0. cbn [rev] in EA0. fold eb ek in EA0.
      apply (enc_popA Mq M4 ov fb eb ek rr e1 (PEC.en_depth enq) EA0); [clear - Q1'; lia| clear - Q3'; lia| intros _; clear - B0 B47; unfold PEC.ESZ; lia| | | | | |].
      - intros i Hi Ri Ni. rewrite (AG34 i ltac:(clear - Ri; lia)). apply AG3; [clear - Hi; lia| clear - Hi; lia| exact Ni| apply NSC; clear - Ri Q2'; lia].
      - intros x Hx. rewrite (SH34 x Hx). unfold HeapIfaceA.S. apply AG3; [unfold SB; clear - Hx Q1'; lia| unfold SB; clear - Hx Q3'; lia| unfold SB; clear - Hx Q1' Q3' QBIG; lia| apply NSS; clear - Hx Q1' Q3'; lia].
      - intros _ i Hi. unfold PEC.ESZ in Hi. rewrite (BLK4 i Hi). apply AG3; [clear - Hi B0; lia| clear - Hi B47; lia| clear - Hi BOV; lia| apply NSC; clear - Hi BCEIL; lia].
      - apply (L5C.u64_at_agree RSEGS M3 M4); [eapply L5C.agree_on_sub; [exact AG34| clear; lia| clear; lia] | clear - Q1'; lia| clear - Q3'; lia| exact U32].
      - exact (PMKA.defined_keepA L ar (PESK.sink_own kq ++ LBc0) FF sp 20480 [] M3 M4 EK34 PMKA.wapp_nil FRB3 ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) ltac:(intros i _ r0 []) (L5.defined_grows Mq M3 _ _ MGM3 EDEF)).
      - intros _. destruct BAT4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BD4 & BA4 & BN4). unfold PEC.ESZ. split; [exact BD4|]. split; [exact BA4| exact BN4]. }
    split.
    { apply (PECFA.sink_keepA RSEGS L ar (PESK.sink_own kq ++ LBc0) FF sp 20480 [] M3 M4 EK34 PMKA.wapp_nil FRB3 BRB3 P osk kq (AOF osk 24 ltac:(lia) ltac:(lia))); [intros i _ r0 []| apply incl_appl; apply incl_refl| intros _ i _ r0 []| exact SKA3]. }
    split; [exact CLq| exact CKq]. }
  apply (KX fx4 R3 R4 M4 md4 LK4 Aw4 INV4 HQR RP4).
  intros a0 Ha0. pose proof HP4 as (P4 & _). rewrite P4.
  - apply AG3; [unfold spc in Ha0; clear - Ha0 Q1' Q2' SLO HFR; lia| clear - Ha0 SHI SPT; lia| unfold spc in Ha0; clear - Ha0 Q2' SLO HFR; lia| clear - Ha0; lia].
  - split; [unfold spc in Ha0; clear - Ha0 SLO SHI SPT HFR; lia|]. split; [| intros r0 []].
    unfold aclient, aclient_g. right; left. split; [unfold spc in Ha0; clear - Ha0 SLO SHI SPT HFR; lia| intros Y; clear - Ha0 Y; lia].
Qed.

Definition retire_run (ra0 : Z) (Rq : bvmap 5 word) : Prop :=
  forall (fx2 : FPState) (R2 : bvmap 5 word) (MV : word -> option byte),
    regs_preserved Rq R2 -> sfacts MV -> ffacts MV false -> owns SAVED sp R MV ->
    exists (fx3 : FPState) (R3 : bvmap 5 word) (M3v : word -> option byte),
      msteps RSEGS (mst fx2 R2 ra0 MV) (mst fx3 R3 r M3v) /\ mem_grows MV M3v
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ PMAUK.Wret F fl 1 i -> M3v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
      /\ L5.u8_at RSEGS M3v fl 0 /\ regs_preserved R R3.

Lemma mkec_finish (v ra0 : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq enq esq edq :
  inv Mq mdq LKq Awq crq kq NB enq -> PEC.en_stk enq = rev esq -> PEC.en_depth enq = edq ->
  XF = ST xstk xpos xmore xdone xhalt xdepth true esq edq (xlo + NB) (xhi + NB) xbad ->
  getr Rq (reg 10) = Z_to_bv 64 (PMSPA.o_ec AD fb) -> getr Rq (reg 11) = Z_to_bv 64 v -> 1 <= v <= 64 ->
  getr Rq (reg 1) = Z_to_bv 64 ra0 -> L5.ra_ok ra0 -> getr Rq (reg 2) = Z_to_bv 64 spc -> csk Rq ->
  retire_run ra0 Rq ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq MKPC Mq mdq) K.
Proof.
  intros INV HSTK HED HXF Q10 Q11 Hv Q1 RA0 Q2 QCS XRUN. entry_facts. name_objs. cut_facts INV kq. pose proof RA0 as (Hra1 & Hra2).
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & GNF & GNV & GFLP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  destruct ESq as [ESb ESk].
  pose proof KONT as KT. rewrite HXF in KT.
  destruct (keepf Mq EKq) as (PAq & IAq & VREFq & BASEq & ERRq & CONTq & ECSq & ACCRq).
  assert (E8 : oec mod 8 = 0) by (rewrite Eoec; replace (fb + 1120) with (fb + 8 * 140) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq oec 16 sp 20480 HHq (PMKA.aobj_of_aobjA FF' oec 16 (PMAUAR.aobjA_push FF oec 16 _ (AOF oec 16 ltac:(lia) ltac:(lia))) E8) ltac:(lia) ltac:(reflexivity))
    as ((E1 & E2 & E3 & _) & EBIG & _ & _ & _ & ECL & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model oec 16 sp 20480 HHp (PMKA.aobj_of_aobjA FF oec 16 (AOF oec 16 ltac:(lia) ltac:(lia)) E8) ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & _ & _ & ECL0 & _).
  destruct (APART oec 16 sp 20480 ECL0 ltac:(clear; lia)) as (AeF & AeS & AeL).

  assert (ECD : L5.defined Mq oec 16 /\ PMSPA.accA Mq oec 16).
  { unfold PECA.ec_stateA in ECSq. destruct xec; [destruct ECSq as (v0 & _ & (_ & _ & ED & EC))| destruct ECSq as (_ & _ & ED & EC)]; (split; [exact ED| exact EC]). }
  destruct ECD as [ECD ECA].
  pose proof MKEC as MKX. unfold PECSA.make_ec_spec, PECSPA.make_ec_spec in MKX. cbn [pa_make_ec PECSA.AD PeCLayoutA.CADDR_A] in MKX.
  unfold PMSPA.cfg.
  apply (MKX fxq Rq Mq mdq K (EBX kq ++ LBc0) FF' LKq Awq crq oec v spc ra0 e HHq AMq K0); clear MKX.
  {
    split; [rewrite L5K.rl1; exact Q1|]. split; [exact RA0|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792. split.
    - unfold spc. apply (L5SAR.astk_sub ar Mq Mq sp 20480 FR 14336 ASTKq (mem_grows_refl Mq)); [clear - HFR; lia| clear; lia| clear - HFR; lia| exact SPC16].
    - unfold spc. apply (PMKA.shadow_zero_sub Mq (sp - 20480) 2560); [apply SPd8; reflexivity| | clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZq].
      replace (sp - FR - 14336) with (sp - (FR + 14336)) by lia. apply SPd8. clear - HFR; destruct HFR as [-> | ->]; reflexivity. }
  { apply (PMAUAR.ffroomA_push 4 1 FF LK LKq _ FRM ILKq); [exact NDFq| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp spc F 1 (spc + 32) FRS); [clear; lia| unfold spc; clear - HFR; lia]. }
  { rewrite L5K.rl10. exact Q10. }
  { rewrite L5K.rl11. exact Q11. }
  { exact Hv. }
  { exact (PMAUAR.aobjA_push FF oec 16 _ (AOF oec 16 ltac:(lia) ltac:(lia))). }
  { exact E8. }
  { exact ECD. }
  { exact ECA. }
  { exact BASEq. }
  { exact ERRq. }
  intros fx2 R2 Mx mdx LKx Awx RP2 ECAT2 ERR2 HP2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 1) with 14336 in HP2.

  assert (HP2' : L5CA.ahpres L ar (EBX kq ++ LBc0) FF' spc 14336 ((oec, 16) :: PMSPA.err_W AD) Mq Mx).
  { destruct HP2 as (P2 & D2 & K2). split; [| split; [exact D2| exact K2]]. intros a0 (Ha & Hc & Ho). apply P2. split; [exact Ha|]. split; [exact Hc|].
    intros r0 Hr. apply Ho. destruct Hr as [<-|Hr]; [left; reflexivity| right]. destruct e; [destruct Hr| exact Hr]. }
  assert (BIx : PMAUK.binv L ar HI M model LBc0 FF LK Aw sp 20480 spc (owns SAVED sp R) F 1 We (EBX kq) Mx mdx LKx crq Awx).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
             Wk We (EBX kq) (EBX kq) (EBX kq) Mq mdq LKq crq Awq Mx mdx LKx crq Awx 14336 ((oec, 16) :: PMSPA.err_W AD) BI HP2' HH2 AM2 MRT2 IAW2 ILK2);
      [clear; lia| unfold spc; clear - HFR; lia| | | exact we_wk].
    - intros r0 a0 Hin Hr. pose proof NSVv as NV. change (ff_bytes 1 / 8) with 16. unfold ocell.
      destruct (we_rng r0 a0 Hin Hr) as [Y|[Y|Y]]; (split; [unfold SB in *; clear - Y E1 E2 SLO NV; lia| unfold SB in AeS |- *; clear - Y AeS GF3 GF8; Lia.lia]).
    - intros a0 _ Oa r0 Hr. apply Oa. unfold We. apply in_or_app. right. exact Hr. }

  destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
              We (EBX kq) Mx mdx LKx crq Awx BIx)
    as ((W0 & W1 & W2 & W3 & W4) & OWNx & (FD & FW & FSW & FLC & FLW) & (_ & VFL & VF & VS & VSH)).
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  set (Hh := ahid Awx mdx) in *. set (MVx := mrestrict Hh Mx) in *.
  replace (sp - spc) with FR in W0, VS by (unfold spc; clear; lia).
  pose proof BIx as (HHx & AMx & MRTx & IAWx & ILKx & ASTKx & EKx & DKx & _ & _).
  pose proof ASTKx as (_ & _ & _ & _ & SDEFx & _).
  assert (SFx : sfacts MVx).
  { split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [clear - SLO SHI SPT; lia|]. split; [exact SP32| unfold spc in W0; exact W0]. }
  assert (FFx : ffacts MVx false).
  { unfold ffacts. replace (F + 120) with (F + 128 - 8) by (clear; lia).
    repeat split; first [exact FD | exact FW | exact FSW | exact FLC | exact FLW | exact I | clear - GF1 GF2 GF32 GFBIG GL1 GL2 GLBIG GFLA GFC GLC SLO HFR; lia]. }
  destruct (XRUN fx2 R2 MVx RP2 SFx FFx OWNx) as (fx3 & R3 & M3v & MS3 & MG3 & FRZ3 & FL3 & RP3).

  apply (PMAUK.retire_core L ar C HI LYa HIok M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
           We (EBX kq) Mx mdx LKx crq Awx fx2 fx3 R2 ra0 R3 r M3v K BIx MS3 MG3 FRZ3 FL3).
  intros Mf mdf FZf AHf MRTf AMf HHf.
  assert (FZf' : forall a0, 0 <= a0 < 2 ^ 64 -> ~ PMAUK.WretX F fl 1 (fun _ => False) a0 -> Mf (Z_to_bv 64 a0) = Mx (Z_to_bv 64 a0)).
  { intros a0 Ha N. apply FZf; [exact Ha|]. intros X'. apply N. left. exact X'. }
  destruct (retire_agree Mx Mf (fun _ => False) FZf' ltac:(intros a0 [])) as [AGa AGs].
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKA.aobj_of_aobjA FF' ov 56 (PMAUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia))) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1' & Q2' & Q3' & _) & QBIG & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKA.aobj_of_aobjA FF' osk 24 (PMAUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & KBIG & _).

  assert (EKqx : L5SAR.ek L ar (EBX kq ++ LBc0) FF sp 20480 ((oec, 16) :: PMSPA.err_W AD) Mq Mx).
  { apply (L5SAR.ek_callee L ar (EBX kq ++ LBc0) [] FF [(F, 1, spc + 32)] sp 20480 spc 14336 ((oec, 16) :: PMSPA.err_W AD) ((oec, 16) :: PMSPA.err_W AD) Mq Mx); [exact HP2'| unfold spc; clear - HFR; lia| unfold spc; clear - HFR; lia| intros a0 _ O; exact O]. }
  assert (WAPPe : PMKA.wapp ((oec, 16) :: PMSPA.err_W AD)) by (intros r0 Hr; apply we_wapp; unfold We; apply in_or_app; right; exact Hr).
  assert (FRBq : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (BRBq : forall x, In x (EBX kq ++ LBc0) -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
  assert (OUTe : forall a m, (a + m <= oec \/ oec + 16 <= a) -> (a + m <= 0x674080 \/ 0x698000 <= a) -> forall i, a <= i < a + m -> L5.outside ((oec, 16) :: PMSPA.err_W AD) i).
  { intros a m Xa Xb i Hi r0 Hr Y. destruct (we_rng r0 i Hr Y) as [Z1|[Z1|Z1]]; clear - Xa Xb Hi Z1; lia. }
  assert (EAx : PECA.enc_atA RSEGS EE L ar Mx ov fb enq).
  { apply (PECFA.enc_keepA RSEGS EE L ar (EBX kq ++ LBc0) FF sp 20480 ((oec, 16) :: PMSPA.err_W AD) Mq Mx EKqx WAPPe FRBq BRBq ov fb enq (AOF ov 56 ltac:(lia) ltac:(lia))); [| | | exact EAq].
    - apply OUTe; [clear - Eov Eoec; lia| right; exact Q1'].
    - unfold EBX. unfold PEC.enc_own. rewrite ESb, ESk. intros x Hx. apply in_or_app; left. apply in_or_app; left. exact Hx.
    - intros Hp i Hi. rewrite ESk in Hp. rewrite ESb, ESk in Hi.
      destruct (eblk_facts (PEC.en_b en) (PEC.ESZ * PEC.ecap (PEC.en_k en)) ltac:(unfold PEC.enc_own; replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia); left; reflexivity))
        as (INb & _ & _ & _ & _ & _ & _ & _ & AP & _).
      destruct (AP oec 16 (AOF oec 16 ltac:(lia) ltac:(lia))) as [Y|Y]; destruct (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ _ _ HH INb) as [Z1|Z1]; apply (OUTe (PEC.en_b en) (PEC.ESZ * PEC.ecap (PEC.en_k en))); first [clear - Y; lia | clear - Z1; lia | exact Hi]. }
  assert (SKAx : PESKA.sink_atA RSEGS L ar P Mx osk kq).
  { apply (PECFA.sink_keepA RSEGS L ar (EBX kq ++ LBc0) FF sp 20480 ((oec, 16) :: PMSPA.err_W AD) Mq Mx EKqx WAPPe FRBq BRBq P osk kq (AOF osk 24 ltac:(lia) ltac:(lia))); [| | | exact SKAq].
    - apply OUTe; [clear - Eosk Eoec; lia| right; exact K1].
    - unfold EBX. intros x Hx. apply in_or_app; left. apply in_or_app; right. exact Hx.
    - intros Hp i Hi. assert (IN : In (PESK.sk_b kq, PESK.sk_c kq) (EBX kq ++ LBc0)).
      { apply in_or_app; left. unfold EBX. apply in_or_app; right. unfold PESK.sink_own. replace (PESK.sk_c kq =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
      destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ oec 16 HHq IN (PMAUAR.aobjA_push FF oec 16 _ (AOF oec 16 ltac:(lia) ltac:(lia)))) as [Y|Y]; destruct (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ _ _ HHq IN) as [Z1|Z1]; apply (OUTe (PESK.sk_b kq) (PESK.sk_c kq)); first [clear - Y; lia | clear - Z1; lia | exact Hi]. }
  assert (EAf : PECA.enc_atA RSEGS EE L ar Mf ov fb enq).
  { apply (PECFA.enc_atA_agree RSEGS EE L ar Mx Mf ov fb enq); [clear - Q1'; lia| clear - Q3'; lia| | | exact EAx].
    - split; [| intros x Hx; apply AGs; clear - Hx Q1' Q3' AvF; lia].
      intros i Hi. apply AGa; [clear - Hi Q1'; lia| clear - Hi Q3'; lia| clear - Hi AvF; lia| clear - Hi QBIG; lia| clear - Hi AvL; lia| intros []].
    - intros Hp. rewrite ESk in Hp. rewrite ESb, ESk. assert (IN : In (PEC.en_b en, PEC.ESZ * PEC.ecap (PEC.en_k en)) (EBX kq ++ LBc0)).
      { apply in_or_app; left. unfold EBX. apply in_or_app; left. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
      destruct (blk_facts Mq LKq crq Awq _ kq _ _ HHq IN) as (B0 & B47 & BAPP & BCEIL & BFS). unfold FS_BYTES in BFS, GFS2, GFLP.
      split; [clear - B0; lia|]. split; [clear - B47; lia|].
      split; [| intros x Hx; apply AGs; clear - Hx B0 B47 BFS GFS1 GFS2; lia].
      intros i Hi. apply AGa; [clear - Hi B0; lia| clear - Hi B47; lia| clear - Hi BFS GFS1 GFS2; lia| clear - Hi BAPP B0; lia| clear - Hi BFS GFLP; lia| intros []]. }
  assert (SKAf : PESKA.sink_atA RSEGS L ar P Mf osk kq).
  { apply (PECFA.sink_atA_agree RSEGS L ar Mx Mf P osk kq); [clear - K1; lia| clear - K3; lia| | | exact SKAx].
    - split; [| intros x Hx; apply AGs; clear - Hx K1 K3 AkF; lia].
      intros i Hi. apply AGa; [clear - Hi K1; lia| clear - Hi K3; lia| clear - Hi AkF; lia| clear - Hi KBIG; lia| clear - Hi AkL; lia| intros []].
    - intros Hp. assert (IN : In (PESK.sk_b kq, PESK.sk_c kq) (EBX kq ++ LBc0)).
      { apply in_or_app; left. unfold EBX. apply in_or_app; right. unfold PESK.sink_own. replace (PESK.sk_c kq =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
      destruct (blk_facts Mq LKq crq Awq _ kq _ _ HHq IN) as (B0 & B47 & BAPP & BCEIL & BFS). unfold FS_BYTES in BFS, GFS2, GFLP.
      split; [clear - B0; lia|]. split; [clear - B47; lia|].
      split; [| intros x Hx; apply AGs; clear - Hx B0 B47 BFS GFS1 GFS2; lia].
      intros i Hi. apply AGa; [clear - Hi B0; lia| clear - Hi B47; lia| clear - Hi BFS GFS1 GFS2; lia| clear - Hi BAPP B0; lia| clear - Hi BFS GFLP; lia| intros []]. }

  assert (ECSf : PECA.ec_stateA RSEGS AD Mf fb true cat).
  { apply (PECFA.ec_stateA_agree RSEGS AD Mx Mf fb true cat); [clear - E1; lia| clear - E3; lia| | exists v; split; [exact Hv| exact ECAT2]].
    split; [| intros x Hx; apply AGs; clear - Hx E1 E3 AeF; lia].
    intros i Hi. apply AGa; [clear - Hi E1; lia| clear - Hi E3; lia| clear - Hi AeF; lia| clear - Hi EBIG; lia| clear - Hi AeL; lia| intros []]. }
  assert (ERRf : PESTA.err_okA RSEGS AD AAD EE Mf true).
  { pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GFLR' _ _ _].
    apply (PESTA.err_okA_frame RSEGS AD AAD EE PECSA.addrs_wf_A Mx Mf); [| exact ERR2]. intros a0 Ha D.
    pose proof (PMASK.dep_img a0 D) as DI. apply AGa; [clear - DI; lia| clear - DI; lia| clear - DI GF3; lia| clear - DI; lia| clear - DI GFLR'; lia| intros []]. }
  destruct (keepf_ec Mf (proj1 AHf)) as (PA' & IA' & VREF' & BASE' & CONT' & ACCR').
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & TBOK & _ & CL & _ & ECI & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad X] in Lmore, Ldone, Ldepth, Lstk, Lpos, Lestk, Ledepth, Lz, Lbad.
  apply (KT fx3 R3 Mf mdf LKx Awx enq kq true crq).
  - exact RP3.
  - unfold PECA.crun_preA. fold op ov ois osk.
    split; [exact PA'|]. split; [exact IA'|]. split; [exact EAf|]. split; [exact VREF'|]. split; [exact SKAf|].
    split; [exact BASE'|]. split; [exact ERRf|]. split; [exact TBOK|]. split; [exact CONT'|].
    split.
    { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad].
      split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
      split; [exact HSTK|]. split; [exact HED|]. split; [clear - CLq; lia| exact Lbad]. }
    cbn [s_ec]. split; [exact ECSf|]. split; [intros _; reflexivity| exact ACCR'].
  - intros _; reflexivity.
  -
    destruct AHf as (E & D & DK). change (PMSPA.pm_scr 4) with 20480. split; [| split; [exact D| exact DK]].
    intros a0 (Ha & Hc & Ho). apply E. split; [exact Ha|]. split; [exact Hc|]. apply we_wenc; [| exact Ho].
    intros q m Hq X'. pose proof HHp as HHe. unfold EBX in HHe. rewrite <- app_assoc in HHe.
    exact (PMARS1.own_not_aclient L ar C HI HIok (PEC.enc_own en) (PESK.sink_own k ++ LBc0) FF LK cr Aw M _ q m a0 sp 20480 HHe Hq X' (L5SAR.aclient_appb L ar LBc0 (PESK.sink_own k) FF sp 20480 a0 Hc)).
  - unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CKq |- *. cbn [fst snd] in CKq |- *. rewrite ESk. clear - CKq. lia.
  - exact MRTf.
  - intros x Hx0. apply ILKq. apply ILK2. exact Hx0.
  - intros x Hx0. apply IAW2. apply IAWq. exact Hx0.
  - exact AMf.
  - exact (ri_perm _ _ FF LKx crq Awx Mf _ (perm_qe kq enq ESb ESk) HHf).
Qed.
End Frame.

Lemma vis_entry :
  let H := ahid Aw model in let MV := mrestrict H M in
  sfacts MV /\ getr R (reg 2) = Z_to_bv 64 sp /\ getr R (reg 10) = Z_to_bv 64 (PMSPA.o_v AD fb) /\ getr R (reg 1) = Z_to_bv 64 r /\ L5.ra_ok r
  /\ 4096 <= PMSPA.o_v AD fb <= 140737488355272.
Proof.
  entry_facts. name_objs.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 20480 FR HH ASTK ltac:(clear - HFR; lia)) as (_ & _ & SWR).
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 sp 20480 HH (PMKA.aobj_of_aobjA FF ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m) ltac:(lia) ltac:(reflexivity)) as ((Q1 & Q2' & Q3 & _) & _).
  pose proof A10 as B10. rewrite L5K.rl10 in B10.
  split. { split; [apply L5A.img_clear_mrestrict; exact GOT|].
    split; [apply (proj2 (L5A.u64_at_vis H M 1317368 SBL (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB|].
    split; [apply (proj2 (L5A.u32_at_vis H M 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR|].
    split; [clear - SLO SHI SPT; lia|]. split; [exact SP32| exact SWR]. }
  split; [exact Rsp|]. split; [exact B10|]. split; [exact Rra|]. split; [exact RAok|]. clear - Q1 Q3; lia.
Qed.

Lemma start (pc0 smra : Z) (fx1 : FPState) R1 M1v :
  msteps RSEGS (mst fx R pc0 (mrestrict (ahid Aw model) M)) (mst fx1 R1 SM1 M1v) -> mem_grows (mrestrict (ahid Aw model) M) M1v ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - FR <= i < sp - FR + FR) -> M1v (Z_to_bv 64 i) = mrestrict (ahid Aw model) M (Z_to_bv 64 i)) ->
  owns SAVED sp R M1v -> getr R1 (reg 1) = Z_to_bv 64 smra -> getr R1 (reg 2) = Z_to_bv 64 spc -> getr R1 (reg 4) = getr R (reg 4) ->
  0 <= smra < 2 ^ 64 -> smra mod 2 = 0 ->
  (forall F fl LK2 M2 model2 R2
      (G : PMAUK.gctx L ar HI LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k))
      (APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (EBX k ++ LBc0) FF sp0 scr0 (a + i)) -> 0 < n ->
                 (a + n <= F \/ F + 128 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + 16 <= a) /\ (a + n <= fl \/ fl + 1 <= a)),
      inv F M2 model2 LK2 Aw cr k 0 en -> regs_preserved R1 R2 -> getr R2 (reg 10) = Z_to_bv 64 F ->
      L5KA.zeros_at (mrestrict (ahid Aw model2) M2) (F / 8 + SBL) 16 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx1) R2 smra M2 model2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R pc0 M model) K.
Proof.
  intros MS1 MG1 FRZ1 OWN1v T1 T2 T4 SMR SM2 KF. entry_facts. name_objs. pose proof AM as (Mh & MI).
  pose proof NSVv as NV.
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 20480 FR HH ASTK ltac:(clear - HFR; lia)) as (SLF & SHF & SWR).

  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R pc0 R1 SM1 M1v (fun a => sp - FR <= a < sp - FR + FR) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|clear - Wa SLF SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SLF SHI SPT; lia| intros X'; clear - X' Wa; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (NCS0 : forall a, sp - FR <= a < sp -> ~ aclient L ar LB FF sp 20480 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 20480 a HH SPT Hc) as [Y|Y]; [clear - Xa Y HFR; lia| clear - Xa Y SLF HFR; lia]. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 20480 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 20480 [] M M1 (fun a => sp - FR <= a < sp - FR + FR) FR1). intros a Ha Hc _ X'. apply (NCS0 a); [clear - X'; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 20480 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKA.ek_sublb L ar LB LBc0 FF sp 20480 [] M M1 INC0 EK01f) as EK01.
  pose proof (PMKA.dk_sublb L ar LB LBc0 FF sp 20480 M M1 INC0 DK01f) as DK01.
  assert (OWN1 : owns SAVED sp R M1).
  { apply (owns_agree SAVED sp R M1v M1 ltac:(pose proof NSVv as NV'; unfold NSV in NV'; clear - SLF SPT NV' HFR; lia) ltac:(clear - SHI SPT; lia) OWN1v). intros a Ha. unfold ocell in Ha. pose proof NSVv as NV'; unfold NSV in NV'.
    symmetry. rewrite <- VIS1. apply mrestrict_visible. replace a with ((sp - FR) + (a - (sp - FR))) by (clear; lia). apply (VIS (sp - FR) FR); [clear - SLF; lia| clear - SHF SHI SPT; lia| clear - Ha NV' HFR HNF; lia]. }

  assert (FRk0 : ff_room 1 FF LK) by (pose proof (FRM 1 ltac:(right; left; reflexivity)) as X'; unfold ff_room; clear - X'; lia).
  change SM1 with (PMA.SM_PC 1).
  apply (PMAUAR.uar_sm L ar C HI LY HIok 1 LBc0 (EBX k) FF LK cr Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R)
           fx1 R1 M M1 model model1 K smra ltac:(right; left; reflexivity) HHp (ri_perm _ _ FF LK cr Aw M1 _ (Permutation_sym (perm_q k)) HH1) AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite T4. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { exact SM2. }
  { exact SMR. }
  { exact SPC16. }
  { unfold spc; clear - HFR; lia. } { unfold spc; clear - HFR NV HNF; lia. } { clear - NV; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (owns_agree SAVED sp R Ma Mb ltac:(pose proof NSVv as NV'; unfold NSV in NV'; clear - SLF SPT NV' HFR; lia) ltac:(clear - SHI SPT; lia) OW). exact AG. }
  { exact FRk0. }
  { intros f Hf. exact (FRS f Hf). }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. change (128 - 8) with 120 in *.
  pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *.

  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (EINC : incl (PEC.enc_own en) LB) by (unfold LB, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (KINC : incl (PESK.sink_own k) LB) by (unfold LB, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad). cbn [s_lo s_hi X] in Lz.
  assert (INCp : incl LB (EBX k ++ LBc0)) by (intros x Hx; apply (Permutation_in x (Permutation_sym (perm_q k))); exact Hx).
  pose proof (L5SAR.ek_trans L ar LB FF sp 20480 [] M M1 M2 EK01f (PMKA.ek_sublb L ar (EBX k ++ LBc0) LB FF sp 20480 [] M1 M2 INCp EK12f)) as EK02f.
  assert (INV2 : inv F M2 model2 LK2 Aw cr k 0 en).
  { unfold inv. split.
    - unfold PMAUK.binv. split; [exact GHH2|]. split; [exact AM2|]. split; [exact (L5LZ.model_rt_trans _ _ _ MRT1 MRT2)|].
      split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact ASTK2|].
      split; [apply (L5SAR.ek_W L ar LBc0 FF sp 20480 Wk [] M M2 EK02); intros a _ r0 []|].
      split; [exact DK02|].
      split; [apply (owns_agree SAVED sp R M1 M2 ltac:(pose proof NSVv as NV'; unfold NSV in NV'; clear - SLF SPT NV' HFR; lia) ltac:(clear - SHI SPT; lia) OWN1); intros a Ha; unfold ocell in Ha; apply AGF; pose proof NSVv as NV'; unfold NSV in NV'; unfold spc; clear - Ha NV' HFR HNF; lia|].
      change (ff_bytes 1 / 8) with 16. apply (proj1 (L5A.defined_vis (ahid Aw model2) M2 (F / 8 + SB) 16 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. rewrite Z0. discriminate.
    - split; [apply (PMKA.stksh_keepA L ar LB FF sp 20480 [] M M2 EK02f PMKA.wapp_nil (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact STKSH]|].
      split; [split; reflexivity|].
      split; [apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp 20480 [] M M2 EK02f PMKA.wapp_nil FRB BRB ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact EINC| intros _ i _ r0 []| exact EA]|].
      split; [apply (PECFA.sink_keepA RSEGS L ar LB FF sp 20480 [] M M2 EK02f PMKA.wapp_nil FRB BRB P osk k (AOF osk 24 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact KINC| intros _ i _ r0 []| exact SKA]|].
      split; [clear - Lz; lia|]. unfold PMSP.credit_keep. clear. lia. }
  exact (KF F fl LK2 M2 model2 R2 G APART INV2 RP2 ltac:(rewrite <- L5K.rl10; exact G10) FSHZ).
Qed.
End Call.
End WithHeap.
End PEAEKN.
