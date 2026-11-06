(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5CoreSpecsAB0S9 L5StepARB0S9 L5CoreBRB0S9 L5ADetailHRB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAb PmModelFactsA PmStep PeStepAB0 PmParKit PeBSrcKit PeBParKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCSinkA PeShZ PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCFrame PeCFrameA PeEncKit PeBCReset1 PeCEPushSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBEKG.
#[local] Transparent e_end_value.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).

Abbreviation SBL := 2147450880.

Definition CSK : list nat := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMB.ly_as0 L C LY.

Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.
Hypothesis MKEC : PECSB.make_ec_spec L ar HI.
Hypothesis PUTL : PECSB.put_length_spec L ar HI P.

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
  L5SAR.ek L ar LB FF sp scr W M M' -> PMKB.wapp W ->
  (forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  PMSPA.aobjA FF (PMSPA.o_is AD fb) 272 -> (forall i, PMSPA.o_is AD fb + 80 <= i < PMSPA.o_is AD fb + 80 + 24 -> L5.outside W i) ->
  incl (PM.vs_own str) LB -> In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB ->
  (forall q m, In (q, m) LB -> PMKB.blk_out W q m) ->
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

Lemma enc_eta en0 : en0 = PEC.ENC (PEC.en_b en0) (PEC.en_k en0) (PEC.en_stk en0) (PEC.en_depth en0).
Proof. destruct en0; reflexivity. Qed.

Lemma blk_facts' LBi FFi Ma LKc crc Awc V q m : ri_inv HI LBi FFi LKc crc Awc Ma V -> In (q, m) LBi ->
  4096 <= q /\ q + m <= 2 ^ 47 /\ (q + m <= 2147446784 \/ 2147446784 + 17592186048512 <= q) /\ q + m <= ahl_ceil ar /\ (q + m <= ar_fs ar \/ ar_fs ar + FS_BYTES <= q).
Proof.
  intros HHc IN. destruct (L5ADHR.blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ LBi [] HHc (eq_sym (app_nil_r _)) _ IN) as ((B0 & _ & _ & _ & BCEIL & (_ & BAPP & B47)) & BFS).
  cbn [fst snd] in B0, BCEIL, BAPP, B47, BFS. unfold BIGSHADOW_LO, BIGSHADOW_HI in BAPP. repeat split; assumption.
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
Variables (FR NB : Z) (CSK : list nat).
Hypothesis HFR : FR = 32 \/ FR = 64 \/ FR = 80 \/ FR = 96.
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
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 4.
Hypothesis FRM : PMSPA.ffroomA 4 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_v AD fb).

Variable FC : (word -> option byte) -> Prop.
Hypothesis FC_frame : forall M1 M2, (forall a, sp - FR <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> FC M1 -> FC M2.

Variable XF : st.
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis POK : PECSPA.payload_ok p.
Hypothesis MP : PECSPA.mp_enc p X.
Hypothesis HBN : PESKA.spa_hb P (xhi + NB).
Hypothesis CRED : PMSP.credit_le (PECA.pot_encA L ar P en k) cr.
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

Definition LBY (eni : PEC.enc) : list (Z * Z) := PM.parser_own s ++ PEC.enc_own eni ++ LBX.

Let Ws : list L5.range := [(PMSPA.o_v AD fb, 56); (PESK.o_sink EE fb, 24)].

Let Wpb : list L5.range := [(PESK.o_sink EE fb, 24)].
Let Wov : list L5.range := [(PMSPA.o_v AD fb, 56)].

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
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & STOP & ND & _);
  pose proof (WF _ Hfb) as (F1 & F2 & F3 & F4 & F5 & F6); cbn [ff_addr ff_class fst snd] in F1, F2, F3, F4, F5, F6; change (ff_bytes 5) with 2048 in F1, F2, F3, F4, F5, F6;
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP; unfold FS_BYTES in F1, F2, F3, F4, F5, F6, FSAPP, FSCEIL, FSIMG.

Lemma AOF a n : fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n.
Proof. intros H1 H2. destruct FOK as ((rs & Hfb) & Fal). exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. Qed.
Lemma FB8 j : (fb + 8 * j) mod 8 = 0.
Proof.
  destruct FOK as (_ & Fal). pose proof (Z.div_mod fb 2048 ltac:(lia)) as E0. rewrite Fal, Z.add_0_r in E0. rewrite E0.
  replace (2048 * (fb / 2048) + 8 * j) with ((256 * (fb / 2048) + j) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma SP16 j : (sp - 16 * j) mod 8 = 0.
Proof.
  pose proof (Z.div_mod sp 32 ltac:(lia)) as E0. rewrite SP32, Z.add_0_r in E0. rewrite E0.
  replace (32 * (sp / 32) - 16 * j) with ((4 * (sp / 32) - 2 * j) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma A16' : sp mod 16 = 0.
Proof. pose proof (Z.div_mod sp 32 ltac:(lia)) as E0. rewrite SP32, Z.add_0_r in E0. rewrite E0. replace (32 * (sp / 32)) with ((2 * (sp / 32)) * 16) by lia. apply Z_mod_mult. Qed.
Lemma SPd8 d : d mod 8 = 0 -> (sp - d) mod 8 = 0.
Proof.
  intros Hd. pose proof (Z.div_mod sp 32 ltac:(lia)) as E0. rewrite SP32, Z.add_0_r in E0. pose proof (Z.div_mod d 8 ltac:(lia)) as E1. rewrite Hd, Z.add_0_r in E1.
  rewrite E0, E1. replace (32 * (sp / 32) - 8 * (d / 8)) with ((4 * (sp / 32) - d / 8) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma SPF16 : (sp - FR) mod 16 = 0.
Proof. destruct HFR as [-> | [-> | [-> | ->]]]; [replace (sp - 32) with (sp + (-2) * 16) by lia| replace (sp - 64) with (sp + (-4) * 16) by lia| replace (sp - 80) with (sp + (-5) * 16) by lia| replace (sp - 96) with (sp + (-6) * 16) by lia]; rewrite Z_mod_plus_full; exact A16'. Qed.
Lemma ws_wpb a : L5.outside Ws a -> L5.outside Wpb a.
Proof. intros O r0 [<-|[]]. apply O. right; left; reflexivity. Qed.
Lemma ws_wov a : L5.outside Ws a -> L5.outside Wov a.
Proof. intros O r0 [<-|[]]. apply O. left; reflexivity. Qed.
Lemma wpb_wapp : PMKB.wapp Wpb.
Proof.
  entry_facts. unfold Wpb. apply PMKB.wapp_cons; [| apply PMKB.wapp_nil]. cbn [fst snd pe_off_sink PeCLayoutB.EADDR_B]. unfold PESK.o_sink. cbn [pe_off_sink PeCLayoutB.EADDR_B].
  unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - F1 F2 FSAPP. lia.
Qed.
Lemma wov_wapp : PMKB.wapp Wov.
Proof.
  entry_facts. unfold Wov. apply PMKB.wapp_cons; [| apply PMKB.wapp_nil]. cbn [fst snd]. unfold PMSPA.o_v. cbn [pa_off_v PeCLayoutB.CADDR_B]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - F1 F2 FSAPP. lia.
Qed.
Lemma ws_wenc a : L5.outside (PEC.W_enc AD EE fb) a -> L5.outside Ws a.
Proof. intros O r0 [<-|[<-|[]]]; apply O; unfold PEC.W_enc; cbn [app]; [left; reflexivity| right; left; reflexivity]. Qed.
Lemma ws_wapp : PMKB.wapp Ws.
Proof.
  entry_facts. unfold Ws. apply PMKB.wapp_cons.
  - cbn [fst snd]. unfold PMSPA.o_v. cbn [pa_off_v PeCLayoutB.CADDR_B]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - F1 F2 FSAPP. lia.
  - apply PMKB.wapp_cons; [| apply PMKB.wapp_nil]. cbn [fst snd pe_off_sink PeCLayoutB.EADDR_B]. unfold PESK.o_sink. cbn [pe_off_sink PeCLayoutB.EADDR_B].
    unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - F1 F2 FSAPP. lia.
Qed.

Definition inv (Mi : word -> option byte) (mdi : Model) (LKi : list fframe) (Awi : list (Z * Z)) (cri : credit) (ki : PESK.sink) (a : Z) (eni : PEC.enc) : Prop :=
  FC Mi /\ L5CA.astk ar Mi sp 20480 /\ shadow_zero Mi (sp - 20480) 2560
  /\ model_rt model mdi /\ L5CA.amodel_ok Awi mdi /\ incl LKi LK /\ incl Aw Awi
  /\ ri_inv HI (PEC.owned s eni ki ++ LBX) FF LKi cri Awi Mi (vml_of mdi)
  /\ PECA.enc_atA RSEGS EE L ar Mi (PMSPA.o_v AD fb) fb eni /\ PESKA.sink_atA RSEGS L ar P Mi (PESK.o_sink EE fb) ki
  /\ xlo + a <= PESK.sk_z ki <= xhi + a
  /\ L5SAR.ek L ar LBc0 FF sp 20480 Ws M Mi /\ L5SAR.dk L ar LBc0 FF sp 20480 M Mi
  /\ PMSP.credit_keep cr cri (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P eni ki).

Lemma keepf Mi : L5SAR.ek L ar LBc0 FF sp 20480 Ws M Mi ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mi (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s /\ PM.iss_at RSEGS AD PMSPA.accA Mi (PMSPA.o_is AD fb) str sm
  /\ L5.u64_at RSEGS Mi (PMSPA.o_p AD fb + 384) (PMSPA.o_v AD fb) /\ PMSTA.base_okA RSEGS AD Mi /\ PESTA.err_okA RSEGS AD AAD EE Mi e
  /\ PEC.content_ok RSEGS AD Mi fb p (PM.p_src s) str sm /\ PECA.ec_stateA RSEGS AD Mi fb xec cat /\ PMSPA.accA Mi (PMSPA.o_p AD fb) PECA.RDR_BYTES.
Proof.
  intros EK. entry_facts. name_objs.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR). cbn [s_ec X] in ECS.
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (BRc0 : forall x, In x LBc0 -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by (intros x Hx; apply BRB; apply INC0; exact Hx).
  assert (PINC : incl (PM.parser_own s) LBc0) by (unfold LBc0; apply incl_appl; apply incl_refl).
  assert (SINC : incl (PM.vs_own str) LBc0) by (unfold LBc0; apply incl_appr; exact INCS).
  pose proof ws_wapp as WAPP.
  assert (OUT : forall i, ~ (ov <= i < ov + 56) -> ~ (osk <= i < osk + 24) -> L5.outside Ws i) by (intros i N0 N r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; [clear - N0; lia| clear - N; lia]).
  assert (AOV : PMSPA.aobjA FF ov 56) by (apply AOF; clear - Eov; lia).
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 sp 20480 HH (PMKB.aobj_of_aobjA FF ov 56 AOV Q8m) ltac:(lia) ltac:(reflexivity)) as ((Q1 & Q2 & Q3 & Q4 & Q5) & _).
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply AOF; clear - Eosk; lia).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model osk 24 sp 20480 HH (PMKB.aobj_of_aobjA FF osk 24 AOSK K8) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & _).
  assert (OUTB : forall q m, In (q, m) LBc0 -> PMKB.blk_out Ws q m).
  { intros q m Hq i Hi. destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m osk 24 HH (INC0 _ Hq) AOSK) as [Xa|Xa];
      destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m ov 56 HH (INC0 _ Hq) AOV) as [Xb|Xb]; apply OUT; first [clear - Xa Hi; lia | clear - Xb Hi; lia]. }
  assert (OUTO : forall a m, (a + m <= osk \/ osk + 24 <= a) -> (a + m <= ov \/ ov + 56 <= a) -> forall i, a <= i < a + m -> L5.outside Ws i) by (intros a m Xa Xb i Hi; apply OUT; [clear - Xb Hi; lia| clear - Xa Hi; lia]).
  assert (Iq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LBc0) by (apply PINC; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (SDEP : forall a, PMST.dep AD a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside Ws a).
  { intros a D. change (PMST.dep PMB.AD a) in D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
    split; [clear - DI; lia|]. split; [exact (PMB.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OUT; [clear - DI Q1; lia| clear - DI K1; lia]. }
  split.
  { apply (PMKB.parser_keepA RSEGS AD L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB BRc0 op ois s (AOF op 384 ltac:(lia) ltac:(lia)) PINC); [| | | | exact PA].
    - apply OUTO; [clear - Eop Eosk; lia| clear - Eop Eov; lia].
    - apply OUTB. exact Iq.
    - apply OUTB. apply PINC. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
    - intros c n q E1. apply OUTB. apply PINC. unfold PM.parser_own, PM.vs_own. rewrite E1. right; right; left. reflexivity. }
  split.
  { apply (PMKB.iss_keepA RSEGS AD L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB BRc0 ois str sm (AOF ois 272 ltac:(lia) ltac:(lia)) SINC); [| | exact IA].
    - apply OUTO; [clear - Eois Eosk; lia| clear - Eois Eov; lia].
    - intros c n0 q E1. refine (OUTB q c _). apply SINC. unfold PM.vs_own. rewrite E1. left. reflexivity. }
  split.
  { apply (PMKB.u64_keepA RSEGS L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF]. apply OUTO; [clear - Eop Eosk; lia| clear - Eop Eov; lia]. }
  split.
  { change (PMSTA.base_okA RSEGS PMB.AD Mi). apply (PMBSK.base_keep L ar C LY LBc0 FF sp 20480 Ws M Mi EK); [| exact BASE]. intros a Ha. apply OUT; [clear - Ha Q1; lia| clear - Ha K1; lia]. }
  split.
  { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBc0 FF sp 20480 Ws M Mi EK e PECSB.addrs_wf_B); [exact SDEP| exact ERR]. }
  split.
  { apply (content_keepA' LBc0 FF sp 20480 Ws M Mi fb p s str sm op EK WAPP FRB BRc0 (AOF ois 272 ltac:(lia) ltac:(lia))); [| exact SINC| exact Iq| exact OUTB| exact IA| exact PA| exact CONT].
    fold ois. apply OUTO; [clear - Eois Eosk; lia| clear - Eois Eov; lia]. }
  split.
  { apply (PECFA.ec_state_keepA RSEGS AD L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB fb xec cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
    fold oec. apply OUTO; [clear - Eoec Eosk; lia| clear - Eoec Eov; lia]. }
  exact (PMKB.acc_keepA' L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACCR).
Qed.

Lemma inv_cpre Mi mdi LKi Awi cri ki a lo hi eni esi edi : inv Mi mdi LKi Awi cri ki a eni -> lo = xlo + a -> hi = xhi + a ->
  PEC.en_stk eni = rev esi -> PEC.en_depth eni = edi ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p (ST xstk xpos xmore xdone xhalt xdepth xec esi edi lo hi xbad) s str sm eni ki e cat.
Proof.
  intros (FCi & ASTKi & SZi & MRTi & AMi & ILKi & IAWi & HHi & EAi & SKAi & CLi & EKi & DKi & CKi) Hlo Hhi HSTK HED.
  destruct (keepf Mi EKi) as (PA' & IA' & VREF' & BASE' & ERR' & CONT' & ECS' & ACCR').
  destruct CPRE as (_ & _ & _ & _ & _ & _ & _ & TBOK & _ & CL & _ & ECI & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad). cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad] in *.
  unfold PECA.crun_preA.
  split; [exact PA'|]. split; [exact IA'|]. split; [exact EAi|]. split; [exact VREF'|]. split; [exact SKAi|].
  split; [exact BASE'|]. split; [exact ERR'|]. split; [exact TBOK|]. split; [exact CONT'|].
  split.
  { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad].
    split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
    split; [exact HSTK|]. split; [exact HED|]. split; [clear - CLi Hlo Hhi; lia| exact Lbad]. }
  cbn [s_ec]. split; [exact ECS'|]. split; [exact ECI| exact ACCR'].
Qed.

Lemma pb_call (a pv h ra0 : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq enq :
  inv Mq mdq LKq Awq crq kq a enq -> PESKA.spa_hb P h -> xhi + a <= h -> sp - FR <= pv -> pv + 1 <= sp -> L5.ra_ok ra0 ->
  getr Rq (reg 1) = Z_to_bv 64 ra0 -> getr Rq (reg 2) = Z_to_bv 64 (sp - FR) ->
  getr Rq (reg 10) = Z_to_bv 64 (PESK.o_sink EE fb) -> getr Rq (reg 11) = Z_to_bv 64 pv -> csk Rq ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 cr2 k2, inv M2 md2 LK2 Aw2 cr2 k2 (a + 1) enq -> regs_preserved Rq R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R2 ra0 M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq 0xb120c Mq mdq) K.
Proof.
  intros INV HBh Ha PV1 PV2 RA0 Q1 Q2 Q10 Q11 QCS KX. entry_facts. name_objs. pose proof RA0 as (Hra1 & Hra2).
  pose proof INV as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  set (LBq := PEC.owned s enq kq ++ LBX) in HHq.
  assert (PERMq : Permutation LBq (PESK.sink_own kq ++ LBY enq)) by (unfold LBq, LBY, PEC.owned; rewrite <- !app_assoc; apply PEEK.perm4).
  pose proof (ri_perm _ _ FF LKq crq Awq Mq _ PERMq HHq) as HHY.
  assert (XINCq : incl LBc0 (LBY enq)) by (unfold LBc0, LBY; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (EINCq : incl (PEC.enc_own enq) (LBY enq)) by (unfold LBY; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (BRBY : forall x, In x (LBY enq) -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
  { intros x Hx. apply (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHY). apply in_or_app. right. exact Hx. }
  assert (FRBq : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply AOF; clear - Eosk; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKB.aobj_of_aobjA FF osk 24 AOSK K8) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & KBIG & _).
  pose proof SKAq as (_ & _ & _ & _ & _ & KZCq & KCAPq & KC0q & KBLKq).
  pose proof EAq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EKq' & _).
  pose proof (PMB.ly_cost L C LY) as (KPM & BLIN & BOV).
  assert (PEN : 0 <= fst (PMSPA.scA L (PEC.pot_estack (PMSPA.HV L ar) (PEC.en_k enq))) /\ 0 <= snd (PMSPA.scA L (PEC.pot_estack (PMSPA.HV L ar) (PEC.en_k enq)))).
  { unfold PMSPA.scA, PEC.pot_estack, PEC.ESZ, PMSPA.HV, LibIfaceAB.heap_view. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead]. rewrite KPM, BOV, BLIN.
    assert (P2 : 2 ^ PEC.en_k enq <= 2 ^ 12) by (apply Z.pow_le_mono_r; clear - EKq'; lia). clear - EKq' P2. split; nia. }
  pose proof PB as PBX. unfold PESKA.push_back_specA in PBX. cbn [pe_push_back EE PeCLayoutB.EADDR_B] in PBX.
  apply (PBX PMODE fxq Rq Mq mdq K (LBY enq) FF LKq Awq crq osk pv (sp - FR) ra0 kq HHY AMq K0); clear PBX.
  {
    split; [rewrite L5K.rl1; exact Q1|]. split; [exact RA0|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536. split.
    - apply (L5SAR.astk_sub ar Mq Mq sp 20480 FR 12288 ASTKq); [intros w D; exact D| clear - HFR; lia| clear; lia| clear - HFR; lia| exact SPF16].
    - apply (PMKB.shadow_zero_sub Mq (sp - 20480) 2560); [apply SPd8; reflexivity| | clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZq].
      replace (sp - FR - 12288) with (sp - (FR + 12288)) by lia. apply SPd8. clear - HFR; destruct HFR as [-> | [-> | [-> | ->]]]; reflexivity. }
  { apply (ffroomA_mono 4 0 FF LK LKq FRM ILKq NDFq). clear; lia. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS HFR; lia. }
  { rewrite L5K.rl10. exact Q10. }
  { rewrite L5K.rl11. exact Q11. }
  { exact SKAq. }
  { exact AOSK. }
  { exact K8. }
  {
    split; [apply (L5.defined_sub Mq (sp - 20480) 20480 pv 1 SDEFq); clear - PV1 PV2 HFR; lia|].
    split; [apply (PESHZ.bat0_of_shadow_zero Mq (sp - 20480) 2560 pv SZq); [apply SPd8; reflexivity| clear - PV1 HFR; lia| clear - PV2; lia]|].
    split; [right; clear - K2 SLO PV1 HFR; lia|]. left. split; [exact PV1| clear - PV2 SHI; lia]. }
  { intros ZC. apply (PESKA.spao_next L P PO (PESK.sk_c kq) h KCAPq); [intros Hc; exact (proj1 (proj2 (proj2 (proj2 (proj2 (KBLKq Hc))))))| exact HBh| clear - ZC CLq Ha; lia]. }
  { unfold PMSP.credit_le, PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CRED, CKq |- *. cbn [fst snd] in CRED, CKq |- *. clear - CRED CKq PEN. lia. }
  intros fx2 R2 M2 md2 LK2 Aw2 cr2 b2 RP2 SKA2 HP2 CK2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2. set (k2 := PESK.sk_push kq b2) in *.

  assert (OWs : forall a0, sp - 20480 <= a0 < sp -> L5.outside Wpb a0).
  { intros a0 Ha0 r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk. clear - Ha0 K2 SLO; lia. }
  assert (FRAME12 : forall a0, sp - FR <= a0 < sp -> M2 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT HFR; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT HFR; lia| intros Y; clear - Ha0 Y; lia].
    - apply OWs. clear - Ha0 HFR; lia. }
  assert (EKpb : L5SAR.ek L ar (LBY enq) FF sp 20480 Wpb Mq M2).
  { apply (L5SAR.ek_callee L ar (LBY enq) [] FF [] sp 20480 (sp - FR) 12288 Wpb Wpb Mq M2 HP2); [clear - HFR; lia| clear - HFR; lia| intros a0 _ O; exact O]. }
  assert (EK12 : L5SAR.ek L ar (LBY enq) FF sp 20480 Ws Mq M2) by (apply (L5SAR.ek_W L ar (LBY enq) FF sp 20480 Ws Wpb Mq M2 EKpb); exact ws_wpb).
  assert (DK12 : L5SAR.dk L ar (LBY enq) FF sp 20480 Mq M2) by (apply (L5SAR.dk_callee L ar (LBY enq) [] FF [] sp 20480 (sp - FR) 12288 Wpb Mq M2 HP2); clear - HFR; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480).
  { apply (PMKB.astk_after_ahpres L ar (LBY enq) FF Mq M2 sp 20480 (sp - FR) 12288 Wpb ASTKq HP2); [clear - HFR; lia| clear - HFR; lia| clear; lia| exact STOP]. }
  pose proof ws_wapp as WAPP.
  assert (SZ2 : shadow_zero M2 (sp - 20480) 2560).
  { apply (PMKB.stksh_keepA L ar (LBY enq) FF sp 20480 Ws Mq M2 EK12 WAPP (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZq]. }
  assert (OUTO : forall a1 m, (a1 + m <= osk \/ osk + 24 <= a1) -> forall i, a1 <= i < a1 + m -> L5.outside Wpb i).
  { intros a1 m Xa i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk. clear - Xa Hi; lia. }
  assert (OUTBY : forall q m, In (q, m) (LBY enq) -> PMKB.blk_out Wpb q m).
  { intros q m Hq. destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m osk 24 HHY (in_or_app _ _ _ (or_intror Hq)) AOSK) as [Xa|Xa];
      (intros i Hi; apply (OUTO q m); [clear - Xa; lia| exact Hi]). }
  apply (KX fx2 R2 M2 md2 LK2 Aw2 cr2 k2); [| exact RP2].
  unfold inv. split; [exact (FC_frame Mq M2 FRAME12 FCq)|]. split; [exact ASTK2|]. split; [exact SZ2|].
  split; [exact (L5LZ.model_rt_trans model mdq md2 MRTq MRT2)|]. split; [exact AM2|].
  split; [intros x Hx; apply ILKq; apply ILK2; exact Hx|]. split; [intros x Hx; apply IAW2; apply IAWq; exact Hx|].
  split; [refine (ri_perm _ _ FF LK2 cr2 Aw2 M2 _ _ HH2); unfold PEC.owned, LBY; rewrite <- !app_assoc; apply Permutation_sym; apply PEEK.perm4|].
  split.
  { apply (PECFA.enc_keepA RSEGS EE L ar (LBY enq) FF sp 20480 Wpb Mq M2 EKpb wpb_wapp FRBq BRBY ov fb enq (AOF ov 56 ltac:(lia) ltac:(lia))); [| exact EINCq| | exact EAq].
    - apply OUTO. clear - Eov Eosk; lia.
    - intros Hp. apply OUTBY. apply EINCq. unfold PEC.enc_own. replace (PEC.en_k enq =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
  split; [exact SKA2|].
  split; [unfold k2, PESK.sk_push; destruct (PESK.sk_z kq <? PESK.sk_c kq); cbn [PESK.sk_z]; clear - CLq; lia|].
  split; [exact (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mq M2 EKq (PMKB.ek_sublb L ar (LBY enq) LBc0 FF sp 20480 Ws Mq M2 XINCq EK12))|].
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M2 DKq (PMKB.dk_sublb L ar (LBY enq) LBc0 FF sp 20480 Mq M2 XINCq DK12))|].
  unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CKq, CK2 |- *. cbn [fst snd] in CKq, CK2 |- *. clear - CKq CK2. lia.
Qed.

Lemma inv_frame Mi Mj mdi mdj LKi Awi cri ki a lo hi eni : inv Mi mdi LKi Awi cri ki a eni -> sp - FR <= lo -> hi <= sp ->
  mem_grows Mi Mj -> (forall i, 0 <= i < 2 ^ 64 -> ~ (lo <= i < hi) -> Mj (Z_to_bv 64 i) = Mi (Z_to_bv 64 i)) -> FC Mj ->
  ri_inv HI (PEC.owned s eni ki ++ LBX) FF LKi cri Awi Mj (vml_of mdj) -> L5CA.amodel_ok Awi mdj -> model_rt mdi mdj ->
  inv Mj mdj LKi Awi cri ki a eni.
Proof.
  intros INV Hlo Hhi MG FRZ FCj HHj AMj MRTj. entry_facts. name_objs.
  pose proof INV as (FCi & ASTKi & SZi & MRTi & AMi & ILKi & IAWi & HHi & EAi & SKAi & CLi & EKi & DKi & CKi).
  set (LBi := PEC.owned s eni ki ++ LBX) in *.
  assert (EK1 : L5SAR.ek L ar LBi FF sp 20480 [] Mi Mj).
  { apply (PMKB.ek_own_frame L ar C HI LYa HIok LBi FF LKi cri Awi Mi Mj _ sp 20480 [] lo hi HHi SPT); [clear - Hlo SLO HFR; lia| clear - Hlo HFR; lia| exact Hhi| exact FRZ]. }
  assert (BRBi : forall x, In x LBi -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi).
  assert (FRBi : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHi).
  assert (INC0 : incl LBc0 LBi) by (unfold LBc0, LBi, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (EINC : incl (PEC.enc_own eni) LBi) by (unfold LBi, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (KINC : incl (PESK.sink_own ki) LBi) by (unfold LBi, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  unfold inv. split; [exact FCj|]. split; [exact (L5SAR.astk_grows ar Mi Mj sp 20480 ASTKi MG)|].
  split; [apply (PMKB.stksh_keepA L ar LBi FF sp 20480 [] Mi Mj EK1 PMKB.wapp_nil (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZi]|].
  split; [exact (L5LZ.model_rt_trans model mdi mdj MRTi MRTj)|]. split; [exact AMj|]. split; [exact ILKi|]. split; [exact IAWi|]. split; [exact HHj|].
  split; [apply (PECFA.enc_keepA RSEGS EE L ar LBi FF sp 20480 [] Mi Mj EK1 PMKB.wapp_nil FRBi BRBi ov fb eni (AOF ov 56 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact EINC| intros _ i _ r0 []| exact EAi]|].
  split; [apply (PECFA.sink_keepA RSEGS L ar LBi FF sp 20480 [] Mi Mj EK1 PMKB.wapp_nil FRBi BRBi P osk ki (AOF osk 24 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact KINC| intros _ i _ r0 []| exact SKAi]|].
  split; [exact CLi|].
  split; [apply (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mi Mj EKi); apply (L5SAR.ek_W L ar LBc0 FF sp 20480 Ws [] Mi Mj); [exact (PMKB.ek_sublb L ar LBi LBc0 FF sp 20480 [] Mi Mj INC0 EK1)| intros a0 _ r0 []]|].
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mi Mj DKi (L5SAR.dk_grows L ar LBc0 FF sp 20480 Mi Mj MG))| exact CKi].
Qed.

Local Ltac cut_facts INV kq enq :=
  pose proof INV as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq);
  pose proof AMq as (Mhq & MIq); pose proof ASTKq as (A16q & SLOq & SHIq & SPTq & SDEFq & SUPq);
  set (LBq := PEC.owned s enq kq ++ LBX) in HHq.

Lemma vis_facts Mq mdq LKq Awq crq kq a enq : inv Mq mdq LKq Awq crq kq a enq ->
  let H := ahid Awq mdq in let MV := mrestrict H Mq in let ov := PMSPA.o_v AD fb in let osk := PESK.o_sink EE fb in
  L5.img_clear MV 1273856 1306624 /\ L5.u64_at RSEGS MV 1335544 SBL /\ L5.u32_at RSEGS MV 1335552 1
  /\ 140735332487168 + 20480 <= sp <= 140737488355328 /\ sp mod 16 = 0 /\ L5.writable RSEGS MV (sp - FR) FR
  /\ 4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at MV (ov / 8 + SBL) 7
  /\ L5.writable RSEGS MV ov 56 /\ ((sp - FR) + FR <= ov \/ ov + 56 <= (sp - FR))
  /\ L5KA.zeros_at MV ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at MV ((ov + 16) / 8 + SBL) 1 /\ L5KA.zeros_at MV ((ov + 48) / 8 + SBL) 1
  /\ L5.u64_at RSEGS MV (ov + 8) osk /\ 4096 <= osk <= 140737488355304 /\ osk mod 8 = 0 /\ osk + 24 <= ov
  /\ L5.u32_at RSEGS MV (ov + 16) MAX_DEPTH /\ L5.u32_at RSEGS MV (ov + 48) (PEC.en_depth enq) /\ 0 <= PEC.en_depth enq <= MAX_DEPTH + 1
  /\ (forall a0 v, sp - FR <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS Mq a0 v -> L5.u64_at RSEGS MV a0 v) /\ FC Mq.
Proof.
  intros INV. entry_facts. name_objs. cut_facts INV kq enq.
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq HHq) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _).
  set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKB.aobj_of_aobjA FF ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2' & Q3 & Q4 & Q5) & QBIG & QDEF & QVIS & QSHV & QCL & QSHCL).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKB.aobj_of_aobjA FF osk 24 (AOF osk 24 ltac:(lia) ltac:(lia)) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C Mq LYa ST) as (GOT & CSB & CUAR & _).
  assert (CVv : forall a0 m0, ov <= a0 -> a0 + m0 <= ov + 56 -> L5A.avis H a0 m0) by (intros a0 m0 X1 X2; eapply L5A.avis_sub; [exact QVIS| lia| lia]).
  pose proof EAq as (EV0 & EV8 & EV16 & EV24 & EV32 & EV40 & EV48 & EDEF & EACC & EK & ELEN & EDEP & EKB & EBLK & _). fold osk in EV8. unfold PEC.ESZ in EV32.
  pose proof (PEC.ecap_nonneg (PEC.en_k enq)) as CN.
  pose proof (PMKB.obj_shadow_vis L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq ov 56 HHq (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m ltac:(lia) ltac:(reflexivity) EACC) as Zov.
  unfold SB in Zov. change (56 / 8) with 7 in Zov. fold H MV in Zov.
  assert (D8 : forall j, (ov + 8 * j) / 8 = ov / 8 + j).
  { intros j. rewrite <- Q5 at 1. replace (ov / 8 * 8 + 8 * j) with ((ov / 8 + j) * 8) by lia. apply Z.div_mul. clear; lia. }
  assert (ZG : forall j, 0 <= j < 7 -> L5KA.zeros_at MV ((ov + 8 * j) / 8 + SBL) 1).
  { intros j Hj. rewrite D8. intros i Hi. replace (ov / 8 + j + SBL + i) with (ov / 8 + SBL + (j + i)) by lia. apply Zov. lia. }
  pose proof (ZG 1 ltac:(lia)) as Z8. pose proof (ZG 2 ltac:(lia)) as Z16. pose proof (ZG 6 ltac:(lia)) as Z48.
  replace (ov + 8 * 1) with (ov + 8) in Z8 by lia. replace (ov + 8 * 2) with (ov + 16) in Z16 by lia. replace (ov + 8 * 6) with (ov + 48) in Z48 by lia.
  pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LKq crq Awq Mq mdq sp 20480 FR HHq ASTKq ltac:(clear - HFR; lia)) as (_ & _ & SWR).
  split; [apply L5A.img_clear_mrestrict; exact GOT|].
  split; [apply (proj2 (L5A.u64_at_vis H Mq 1335544 SBL (VIMG 1335544 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB|].
  split; [apply (proj2 (L5A.u32_at_vis H Mq 1335552 1 (VIMG 1335552 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR|].
  split; [clear - SLO SHI SPT; lia|]. split; [exact A16'|]. split; [exact SWR|].
  split; [clear - Q1 Q3; lia|]. split; [exact Q8m|]. split; [exact QBIG|]. split; [exact Zov|].
  split; [apply (proj2 (L5A.writable_vis H Mq ov 56 QVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact QDEF| lia| lia]|].
  split; [clear - Q2' SLO HFR; lia|]. split; [exact Z8|]. split; [exact Z16|]. split; [exact Z48|].
  split; [apply (proj2 (L5A.u64_at_vis H Mq (ov + 8) osk (CVv (ov + 8) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV8|].
  split; [clear - K1 K3; lia|]. split; [exact K8|]. split; [clear - Eov Eosk; lia|].
  split; [apply (proj2 (L5A.u32_at_vis H Mq (ov + 16) _ (CVv (ov + 16) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV16|].
  split; [apply (proj2 (L5A.u32_at_vis H Mq (ov + 48) _ (CVv (ov + 48) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV48|].
  split; [exact EDEP|].
  split; [| exact FCq].
  intros a0 v Ha1 Ha2 U. apply (proj2 (L5A.u64_at_vis H Mq a0 v (VIS a0 8 ltac:(clear - Ha1 SLO HFR; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO SPT HFR; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact U.
Qed.

Lemma finish_ro a pcq (fxq : FPState) Rq Mq mdq LKq Awq crq kq (fx3 : FPState) R3 M3v enq esq edq :
  inv Mq mdq LKq Awq crq kq a enq -> PEC.en_stk enq = rev esq -> PEC.en_depth enq = edq ->
  XF = ST xstk xpos xmore xdone xhalt xdepth xec esq edq (xlo + a) (xhi + a) xbad ->
  msteps RSEGS (mst fxq Rq pcq (mrestrict (ahid Awq mdq) Mq)) (mst fx3 R3 r M3v) -> mem_grows (mrestrict (ahid Awq mdq) Mq) M3v ->
  (forall i, 0 <= i < 2 ^ 64 -> M3v (Z_to_bv 64 i) = mrestrict (ahid Awq mdq) Mq (Z_to_bv 64 i)) -> regs_preserved R R3 ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcq Mq mdq) K.
Proof.
  intros INV HSTK HED HXF MS3 MG3 FRZ3 RP3. entry_facts. name_objs. cut_facts INV kq enq.
  pose proof KONT as KT. rewrite HXF in KT.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LBq FF LKq crq Awq Mq mdq fxq fx3 Rq pcq R3 r M3v K HHq AMq MS3 MG3 FRZ3).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 AG3. pose proof (L5SAR.mem_eq_of_agree Mq M3 AG3) as EM. subst M3.
  apply (KT fx3 R3 Mq md3 LKq Awq enq kq e crq).
  - exact RP3.
  - exact (inv_cpre Mq mdq LKq Awq crq kq a _ _ enq esq edq INV eq_refl eq_refl HSTK HED).
  - intros E1; exact E1.
  - change (PMSPA.pm_scr 4) with 20480. apply (L5SAR.ahpres_of L ar LBc0 FF sp 20480 _ M Mq); [| exact SDEFq| exact DKq].
    apply (L5SAR.ek_W L ar LBc0 FF sp 20480 _ Ws M Mq EKq). exact ws_wenc.
  - exact CKq.
  - exact (L5LZ.model_rt_trans model mdq md3 MRTq MRT3).
  - exact ILKq.
  - exact IAWq.
  - exact AM3.
  - exact HH3.
Qed.

Lemma vis_entry :
  let H := ahid Aw model in let MV := mrestrict H M in let ov := PMSPA.o_v AD fb in let osk := PESK.o_sink EE fb in
  L5.img_clear MV 1273856 1306624 /\ L5.u64_at RSEGS MV 1335544 SBL /\ L5.u32_at RSEGS MV 1335552 1
  /\ 140735332487168 + 20480 <= sp <= 140737488355328 /\ sp mod 16 = 0 /\ L5.writable RSEGS MV (sp - FR) FR
  /\ 4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at MV (ov / 8 + SBL) 7
  /\ L5.writable RSEGS MV ov 56 /\ ((sp - FR) + FR <= ov \/ ov + 56 <= (sp - FR))
  /\ L5KA.zeros_at MV ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at MV ((ov + 16) / 8 + SBL) 1 /\ L5KA.zeros_at MV ((ov + 48) / 8 + SBL) 1
  /\ L5.u64_at RSEGS MV (ov + 8) osk /\ 4096 <= osk <= 140737488355304 /\ osk mod 8 = 0 /\ osk + 24 <= ov
  /\ L5.u32_at RSEGS MV (ov + 16) MAX_DEPTH /\ L5.u32_at RSEGS MV (ov + 48) (PEC.en_depth en) /\ PEC.en_depth en = xedepth
  /\ getr R (reg 2) = Z_to_bv 64 sp /\ getr R (reg 10) = Z_to_bv 64 ov /\ getr R (reg 1) = Z_to_bv 64 r /\ L5.ra_ok r
  /\ (forall M1 a0 v, sp - FR <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS (mrestrict H M1) a0 v -> L5.u64_at RSEGS M1 a0 v).
Proof.
  entry_facts. name_objs.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 sp 20480 HH (PMKB.aobj_of_aobjA FF ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2' & Q3 & Q4 & Q5) & QBIG & QDEF & QVIS & QSHV & QCL & QSHCL).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model osk 24 sp 20480 HH (PMKB.aobj_of_aobjA FF osk 24 (AOF osk 24 ltac:(lia) ltac:(lia)) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (CVv : forall a0 m0, ov <= a0 -> a0 + m0 <= ov + 56 -> L5A.avis H a0 m0) by (intros a0 m0 X1 X2; eapply L5A.avis_sub; [exact QVIS| lia| lia]).
  pose proof EA as (_ & EV8 & EV16 & _ & _ & _ & EV48 & EDEF & EACC & _). fold osk in EV8.
  destruct CL as (_ & _ & _ & _ & _ & _ & Ledepth & _). cbn [s_edepth X] in Ledepth.
  pose proof (PMKB.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 HH (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m ltac:(lia) ltac:(reflexivity) EACC) as Zov.
  unfold SB in Zov. change (56 / 8) with 7 in Zov. fold H MV in Zov.
  assert (D8 : forall j, (ov + 8 * j) / 8 = ov / 8 + j).
  { intros j. rewrite <- Q5 at 1. replace (ov / 8 * 8 + 8 * j) with ((ov / 8 + j) * 8) by lia. apply Z.div_mul. clear; lia. }
  assert (ZG : forall j, 0 <= j < 7 -> L5KA.zeros_at MV ((ov + 8 * j) / 8 + SBL) 1).
  { intros j Hj. rewrite D8. intros i Hi. replace (ov / 8 + j + SBL + i) with (ov / 8 + SBL + (j + i)) by lia. apply Zov. lia. }
  pose proof (ZG 1 ltac:(lia)) as Z8. pose proof (ZG 2 ltac:(lia)) as Z16. pose proof (ZG 6 ltac:(lia)) as Z48.
  replace (ov + 8 * 1) with (ov + 8) in Z8 by lia. replace (ov + 8 * 2) with (ov + 16) in Z16 by lia. replace (ov + 8 * 6) with (ov + 48) in Z48 by lia.
  pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 20480 FR HH ASTK ltac:(clear - HFR; lia)) as (_ & _ & SWR).
  pose proof A10 as B10. rewrite L5K.rl10 in B10.
  split; [apply L5A.img_clear_mrestrict; exact GOT|].
  split; [apply (proj2 (L5A.u64_at_vis H M 1335544 SBL (VIMG 1335544 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB|].
  split; [apply (proj2 (L5A.u32_at_vis H M 1335552 1 (VIMG 1335552 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR|].
  split; [clear - SLO SHI SPT; lia|]. split; [exact A16'|]. split; [exact SWR|].
  split; [clear - Q1 Q3; lia|]. split; [exact Q8m|]. split; [exact QBIG|]. split; [exact Zov|].
  split; [apply (proj2 (L5A.writable_vis H M ov 56 QVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact QDEF| lia| lia]|].
  split; [clear - Q2' SLO HFR; lia|]. split; [exact Z8|]. split; [exact Z16|]. split; [exact Z48|].
  split; [apply (proj2 (L5A.u64_at_vis H M (ov + 8) osk (CVv (ov + 8) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV8|].
  split; [clear - K1 K3; lia|]. split; [exact K8|]. split; [clear - Eov Eosk; lia|].
  split; [apply (proj2 (L5A.u32_at_vis H M (ov + 16) _ (CVv (ov + 16) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV16|].
  split; [apply (proj2 (L5A.u32_at_vis H M (ov + 48) _ (CVv (ov + 48) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV48|].
  split; [exact Ledepth|].
  split; [exact Rsp|]. split; [exact B10|]. split; [exact Rra|]. split; [exact RAok|].
  intros M1 a0 v Ha1 Ha2 U. apply (proj1 (L5A.u64_at_vis H M1 a0 v (VIS a0 8 ltac:(clear - Ha1 SLO HFR; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO SPT HFR; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact U.
Qed.

Lemma inv_startw M1 md1 d' : mem_grows M M1 ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - FR <= i < sp - FR + FR) -> ~ (PMSPA.o_v AD fb + 48 <= i < PMSPA.o_v AD fb + 52) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> FC M1 ->
  ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M1 (vml_of md1) -> L5CA.amodel_ok Aw md1 -> model_rt model md1 ->
  L5.u32_at RSEGS M1 (PMSPA.o_v AD fb + 48) d' -> 0 <= d' <= MAX_DEPTH + 1 ->
  inv M1 md1 LK Aw cr k 0 (PEC.ENC (PEC.en_b en) (PEC.en_k en) (PEC.en_stk en) d').
Proof.
  intros MG FR1 FC1 HH1 AM1 MRT1 U48 Hd'. entry_facts. name_objs.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad). cbn [s_lo s_hi X] in Lz.
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  assert (AOV : PMSPA.aobjA FF ov 56) by (apply AOF; clear - Eov; lia).
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply AOF; clear - Eosk; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 sp 20480 HH (PMKB.aobj_of_aobjA FF ov 56 AOV Q8m) ltac:(lia) ltac:(reflexivity)) as ((Q1 & Q2 & Q3 & Q4 & Q5) & QBIG & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model osk 24 sp 20480 HH (PMKB.aobj_of_aobjA FF osk 24 AOSK K8) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & KBIG & _).
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (EINC : incl (PEC.enc_own en) LB) by (unfold LB, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (KINC : incl (PESK.sink_own k) LB) by (unfold LB, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).

  assert (EK01 : L5SAR.ek L ar LB FF sp 20480 Wov M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 20480 Wov M M1 (fun a => (sp - FR <= a < sp - FR + FR) \/ (ov + 48 <= a < ov + 52))).
    - intros a Ha N. apply FR1; [exact Ha| intros X1; apply N; left; exact X1| intros X1; apply N; right; exact X1].
    - intros a Ha Hc Ho [X1|X1].
      + destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 20480 a HH SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; clear - X1 HFR; lia| clear - X1 Y SLO HFR; lia].
      + apply (Ho (ov, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X1; lia]. }
  unfold inv. split; [exact FC1|]. split; [exact (L5SAR.astk_grows ar M M1 sp 20480 ASTK MG)|].
  split; [apply (PMKB.stksh_keepA L ar LB FF sp 20480 Wov M M1 EK01 wov_wapp (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact STKSH]|].
  split; [exact MRT1|]. split; [exact AM1|]. split; [apply incl_refl|]. split; [apply incl_refl|]. split; [exact HH1|].
  split.
  { rewrite (enc_eta en) in EA.
    apply (enc_depthA M M1 ov fb (PEC.en_b en) (PEC.en_k en) (PEC.en_stk en) (PEC.en_depth en) d' EA); [clear - Q1; lia| clear - Q3; lia| | | | | exact MG| exact U48| exact Hd'].
    - intros Hp. assert (IN : In (PEC.en_b en, PEC.ESZ * PEC.ecap (PEC.en_k en)) LB).
      { apply EINC. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
      destruct (BRB _ IN) as [B0 B47]. cbn [fst snd] in B0, B47. clear - B0 B47; lia.
    - intros i Hi Ri Ni. apply FR1; [exact Hi| clear - Ri Q2 SLO HFR; lia| exact Ni].
    - intros x Hx. apply FR1; [unfold HeapIfaceA.S, SB; clear - Hx Q1 Q3; lia| unfold HeapIfaceA.S, SB; clear - Hx Q1 Q3 SLO SPT HFR; lia| unfold HeapIfaceA.S, SB; clear - Hx Q1 Q3 QBIG; lia].
    - intros Hp. assert (IN : In (PEC.en_b en, PEC.ESZ * PEC.ecap (PEC.en_k en)) LB).
      { apply EINC. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
      destruct (blk_facts' LB FF M LK cr Aw _ _ _ HH IN) as (B0 & B47 & BAPP & BCEIL & BFS).
      pose proof (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ ov 56 HH IN AOV) as BOV.
      split; [intros i Hi; apply FR1; [clear - Hi B0 B47; lia| clear - Hi BCEIL SLO HFR; lia| clear - Hi BOV; lia]
            | intros x Hx; apply FR1; [unfold HeapIfaceA.S, SB; clear - Hx B0 B47; lia| unfold HeapIfaceA.S, SB; clear - Hx B0 B47 SLO SPT HFR; lia| unfold HeapIfaceA.S, SB; clear - Hx B0 B47 Q1 QBIG; lia]]. }
  split.
  { apply (PECFA.sink_keepA RSEGS L ar LB FF sp 20480 Wov M M1 EK01 wov_wapp FRB BRB P osk k AOSK); [| exact KINC| | exact SKA].
    - intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold ov. clear - Hi Eov Eosk; lia.
    - intros Hc i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold ov.
      assert (IN : In (PESK.sk_b k, PESK.sk_c k) LB).
      { apply KINC. unfold PESK.sink_own. replace (PESK.sk_c k =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hc; lia). left. reflexivity. }
      destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ ov 56 HH IN AOV) as [Xa|Xa]; clear - Xa Hi; lia. }
  split; [clear - Lz; lia|].
  split; [apply (L5SAR.ek_W L ar LBc0 FF sp 20480 Ws Wov M M1); [exact (PMKB.ek_sublb L ar LB LBc0 FF sp 20480 Wov M M1 INC0 EK01)| exact ws_wov]|].
  split; [apply L5SAR.dk_grows; exact MG|]. unfold PMSP.credit_keep, PECA.pot_encA. cbn [PEC.en_k]. clear. lia.
Qed.

Lemma estk_credit Mq enq kq crq : 0 <= PEC.en_k enq <= 11 -> PESKA.sink_atA RSEGS L ar P Mq (PESK.o_sink EE fb) kq ->
  PMSP.credit_le (PECA.pot_encA L ar P enq kq) crq ->
  acredit_ok L crq (PEC.ESZ * PEC.ecap (PEC.en_k enq + 1))
  /\ forall en2, PEC.en_k en2 = PEC.en_k enq + 1 ->
       PMSP.credit_keep crq (adebit L crq (PEC.ESZ * PEC.ecap (PEC.en_k enq + 1))) (PECA.pot_encA L ar P enq kq) (PECA.pot_encA L ar P en2 kq).
Proof.
  intros Hk SKAq (CR1 & CR2). pose proof (PMB.ly_cost L C LY) as (K8 & B3 & BO). pose proof (PESKA.sink_potA_nonneg RSEGS L ar P Mq (PESK.o_sink EE fb) kq PO SKAq) as [SP1 SP2].
  assert (EC : PEC.ecap (PEC.en_k enq + 1) = 2 ^ PEC.en_k enq).
  { unfold PEC.ecap. replace (PEC.en_k enq + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). f_equal. lia. }
  rewrite EC.
  assert (PW : 2 ^ (PEC.en_k enq + 1) = 2 * 2 ^ PEC.en_k enq) by (rewrite Z.pow_add_r by lia; lia).
  assert (P11 : 2 ^ PEC.en_k enq <= 2048) by (change 2048 with (2 ^ 11); apply Z.pow_le_mono_r; lia).
  assert (P0 : 1 <= 2 ^ PEC.en_k enq) by (pose proof (Zpow_facts.Zpower_le_monotone 2 0 (PEC.en_k enq)); lia).
  unfold PECA.pot_encA, PEC.credit_add in *. unfold PEC.pot_estack, PMSPA.HV, LibIfaceAB.heap_view in *. unfold PMSPA.scA, PEC.ESZ in *.
  cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in *. rewrite K8, B3, BO in *.
  split.
  - unfold acredit_ok. rewrite K8, B3, BO. split; lia.
  - intros en2 Ek2. unfold PMSP.credit_keep, adebit. rewrite K8, B3, BO. cbn [fst snd]. rewrite Ek2, PW. split; lia.
Qed.

Lemma epush_call (pc a ra0 : Z) cells (it : eitem) (fxq : FPState) Rq Mq mdq LKq Awq crq kq enq :
  PECEPA.epush_spec_at RSEGS AD EE L ar HI pc cells ->
  inv Mq mdq LKq Awq crq kq a enq -> Z.of_nat (length (PEC.en_stk enq)) <= MAX_DEPTH -> L5.ra_ok ra0 ->
  getr Rq (reg 1) = Z_to_bv 64 ra0 -> getr Rq (reg 2) = Z_to_bv 64 (sp - FR) -> getr Rq (reg 10) = Z_to_bv 64 (PMSPA.o_v AD fb + 24) -> csk Rq ->
  cells FF (sp - FR) (PMSPA.o_v AD fb) Mq Rq it ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 cr2 en2, inv M2 md2 LK2 Aw2 cr2 kq a en2 ->
      PEC.en_stk en2 = PEC.en_stk enq ++ [it] -> PEC.en_depth en2 = PEC.en_depth enq -> regs_preserved Rq R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R2 ra0 M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq pc Mq mdq) K.
Proof.
  intros EP INV HLEN RA0 Q1 Q2 Q10 QCS CELLS KX. entry_facts. name_objs. pose proof RA0 as (Hra1 & Hra2).
  pose proof INV as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  set (LBq := PEC.owned s enq kq ++ LBX) in HHq.

  set (LBZ := PM.parser_own s ++ PESK.sink_own kq ++ LBX).
  assert (PERMq : Permutation LBq (PEC.enc_own enq ++ LBZ)).
  { unfold LBq, LBZ, PEC.owned. rewrite <- !app_assoc. apply Permutation_app_swap_app. }
  pose proof (ri_perm _ _ FF LKq crq Awq Mq _ PERMq HHq) as HHZ.
  assert (ZINCq : incl LBc0 LBZ) by (unfold LBc0, LBZ; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (KINCq : incl (PESK.sink_own kq) LBZ) by (unfold LBZ; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (BRBZ : forall x, In x LBZ -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
  { intros x Hx. apply (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHZ). apply in_or_app. right. exact Hx. }
  assert (FRBq : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
  pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply AOF; clear - Eosk; lia).
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (AOV : PMSPA.aobjA FF ov 56) by (apply AOF; clear - Eov; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKB.aobj_of_aobjA FF osk 24 AOSK K8) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & KBIG & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKB.aobj_of_aobjA FF ov 56 AOV Q8m) ltac:(lia) ltac:(reflexivity)) as ((Q1' & Q2' & Q3' & Q4' & Q5') & QBIG' & _).
  pose proof EAq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EKq' & ELENq & _).
  destruct (keepf Mq EKq) as (_ & _ & _ & BASEq & _).

  assert (CRq : PMSP.credit_le (PECA.pot_encA L ar P enq kq) crq).
  { unfold PMSP.credit_le, PMSP.credit_keep in CRED, CKq |- *. clear - CRED CKq. lia. }
  assert (K11 : Z.of_nat (length (PEC.en_stk enq)) = PEC.ecap (PEC.en_k enq) -> 0 <= PEC.en_k enq <= 11).
  { intros HFULL. destruct (Z.eq_dec (PEC.en_k enq) 12) as [E12|NE]; [| clear - EKq' NE; lia].
    exfalso. rewrite E12 in HFULL. unfold PEC.ecap in HFULL. cbn in HFULL. clear - HFULL HLEN. unfold MAX_DEPTH in HLEN. lia. }
  pose proof EP as EPX. unfold PECEPA.epush_spec_at in EPX.
  apply (EPX fxq Rq Mq mdq K LBZ FF LKq Awq crq ov fb enq it (sp - FR) ra0 HHZ AMq K0); clear EPX.
  {
    split; [rewrite L5K.rl1; exact Q1|]. split; [exact RA0|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536. split.
    - apply (L5SAR.astk_sub ar Mq Mq sp 20480 FR 12288 ASTKq); [intros w D; exact D| clear - HFR; lia| clear; lia| clear - HFR; lia| exact SPF16].
    - apply (PMKB.shadow_zero_sub Mq (sp - 20480) 2560); [apply SPd8; reflexivity| | clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZq].
      replace (sp - FR - 12288) with (sp - (FR + 12288)) by lia. apply SPd8. clear - HFR; destruct HFR as [-> | [-> | [-> | ->]]]; reflexivity. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS HFR; lia. }
  { rewrite L5K.rl10. exact Q10. }
  { exact AOV. }
  { exact Q8m. }
  { exact EAq. }
  { exact HLEN. }
  { exact BASEq. }
  { exact CELLS. }
  { intros HFULL. exact (proj1 (estk_credit Mq enq kq crq (K11 HFULL) SKAq CRq)). }
  intros fx2 R2 M2 md2 LK2 Aw2 en2 cr2 RP2 EA2 HSTK2 HED2 HOUT HP2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2.

  assert (OWs : forall a0, sp - 20480 <= a0 < sp -> L5.outside [(ov + 24, 24)] a0).
  { intros a0 Ha0 r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha0 Q2' SLO; lia. }
  assert (FRAME12 : forall a0, sp - FR <= a0 < sp -> M2 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT HFR; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT HFR; lia| intros Y; clear - Ha0 Y; lia].
    - apply OWs. clear - Ha0 HFR; lia. }
  assert (EKe : L5SAR.ek L ar LBZ FF sp 20480 [(ov + 24, 24)] Mq M2).
  { apply (L5SAR.ek_callee L ar LBZ [] FF [] sp 20480 (sp - FR) 12288 [(ov + 24, 24)] [(ov + 24, 24)] Mq M2 HP2); [clear - HFR; lia| clear - HFR; lia| intros a0 _ O; exact O]. }
  assert (EK12 : L5SAR.ek L ar LBZ FF sp 20480 Ws Mq M2).
  { apply (L5SAR.ek_W L ar LBZ FF sp 20480 Ws _ Mq M2 EKe). intros a0 O r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. intros Y.
    apply (O (ov, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
  assert (DK12 : L5SAR.dk L ar LBZ FF sp 20480 Mq M2) by (apply (L5SAR.dk_callee L ar LBZ [] FF [] sp 20480 (sp - FR) 12288 [(ov + 24, 24)] Mq M2 HP2); clear - HFR; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480).
  { apply (PMKB.astk_after_ahpres L ar LBZ FF Mq M2 sp 20480 (sp - FR) 12288 [(ov + 24, 24)] ASTKq HP2); [clear - HFR; lia| clear - HFR; lia| clear; lia| exact STOP]. }
  pose proof ws_wapp as WAPP.
  assert (SZ2 : shadow_zero M2 (sp - 20480) 2560).
  { apply (PMKB.stksh_keepA L ar LBZ FF sp 20480 Ws Mq M2 EK12 WAPP (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZq]. }
  assert (WAPPe : PMKB.wapp [(ov + 24, 24)]).
  { apply PMKB.wapp_cons; [| apply PMKB.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - QBIG'. lia. }
  apply (KX fx2 R2 M2 md2 LK2 Aw2 cr2 en2); [| exact HSTK2| exact HED2| exact RP2].
  unfold inv. split; [exact (FC_frame Mq M2 FRAME12 FCq)|]. split; [exact ASTK2|]. split; [exact SZ2|].
  split; [exact (L5LZ.model_rt_trans model mdq md2 MRTq MRT2)|]. split; [exact AM2|].
  split; [intros x Hx; apply ILKq; apply ILK2; exact Hx|]. split; [intros x Hx; apply IAW2; apply IAWq; exact Hx|].
  split; [refine (ri_perm _ _ FF LK2 cr2 Aw2 M2 _ _ HH2); unfold PEC.owned, LBZ; rewrite <- !app_assoc; apply Permutation_app_swap_app|].
  split; [exact EA2|].
  split.
  { apply (PECFA.sink_keepA RSEGS L ar LBZ FF sp 20480 [(ov + 24, 24)] Mq M2 EKe WAPPe FRBq BRBZ P osk kq AOSK); [| exact KINCq| | exact SKAq].
    - intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Hi Eov Eosk; lia.
    - intros Hc i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd].
      assert (IN : In (PESK.sk_b kq, PESK.sk_c kq) (PEC.enc_own enq ++ LBZ)).
      { apply in_or_app. right. apply KINCq. unfold PESK.sink_own. replace (PESK.sk_c kq =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hc; lia). left. reflexivity. }
      destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ ov 56 HHZ IN AOV) as [Xa|Xa]; clear - Xa Hi; lia. }
  split; [clear - CLq; lia|].
  split; [exact (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mq M2 EKq (PMKB.ek_sublb L ar LBZ LBc0 FF sp 20480 Ws Mq M2 ZINCq EK12))|].
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M2 DKq (PMKB.dk_sublb L ar LBZ LBc0 FF sp 20480 Mq M2 ZINCq DK12))|].
  destruct HOUT as [(HLT & Hb2 & Hk2 & Hcr)|(HEQ & Hk2 & Hcr)]; rewrite Hcr.
  - unfold PMSP.credit_keep, PECA.pot_encA in CKq |- *. rewrite Hk2. clear - CKq. lia.
  - pose proof (proj2 (estk_credit Mq enq kq crq (K11 HEQ) SKAq CRq) en2 Hk2) as CK2.
    unfold PMSP.credit_keep in CKq, CK2 |- *. clear - CKq CK2. lia.
Qed.

Lemma econe_call (pc a ra0 : Z) cells (it : eitem) (fxq : FPState) Rq Mq mdq LKq Awq crq kq enq :
  PECEPA.econe_spec_at RSEGS AD EE L ar HI pc cells ->
  inv Mq mdq LKq Awq crq kq a enq -> Z.of_nat (length (PEC.en_stk enq)) < PEC.ecap (PEC.en_k enq) -> L5.ra_ok ra0 ->
  getr Rq (reg 1) = Z_to_bv 64 ra0 -> getr Rq (reg 2) = Z_to_bv 64 (sp - FR) -> getr Rq (reg 10) = Z_to_bv 64 (PMSPA.o_v AD fb + 24) -> csk Rq ->
  cells FF (sp - FR) (PMSPA.o_v AD fb) Mq Rq it ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2, inv M2 md2 LK2 Aw2 crq kq a (PEC.ENC (PEC.en_b enq) (PEC.en_k enq) (PEC.en_stk enq ++ [it]) (PEC.en_depth enq)) ->
      regs_preserved Rq R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R2 ra0 M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq pc Mq mdq) K.
Proof.
  intros EP INV HLT RA0 Q1 Q2 Q10 QCS CELLS KX. entry_facts. name_objs. pose proof RA0 as (Hra1 & Hra2).
  pose proof INV as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  set (LBq := PEC.owned s enq kq ++ LBX) in HHq.
  set (LBZ := PM.parser_own s ++ PESK.sink_own kq ++ LBX).
  assert (PERMq : Permutation LBq (PEC.enc_own enq ++ LBZ)).
  { unfold LBq, LBZ, PEC.owned. rewrite <- !app_assoc. apply Permutation_app_swap_app. }
  pose proof (ri_perm _ _ FF LKq crq Awq Mq _ PERMq HHq) as HHZ.
  assert (ZINCq : incl LBc0 LBZ) by (unfold LBc0, LBZ; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (KINCq : incl (PESK.sink_own kq) LBZ) by (unfold LBZ; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (BRBZ : forall x, In x LBZ -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
  { intros x Hx. apply (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHZ). apply in_or_app. right. exact Hx. }
  assert (FRBq : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
  pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply AOF; clear - Eosk; lia).
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (AOV : PMSPA.aobjA FF ov 56) by (apply AOF; clear - Eov; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKB.aobj_of_aobjA FF osk 24 AOSK K8) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & KBIG & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKB.aobj_of_aobjA FF ov 56 AOV Q8m) ltac:(lia) ltac:(reflexivity)) as ((Q1' & Q2' & Q3' & Q4' & Q5') & QBIG' & _).
  destruct (keepf Mq EKq) as (_ & _ & _ & BASEq & _).
  pose proof EP as EPX. unfold PECEPA.econe_spec_at in EPX.
  apply (EPX fxq Rq Mq mdq K LBZ FF LKq Awq crq ov fb enq it (sp - FR) ra0 HHZ AMq K0); clear EPX.
  {
    split; [rewrite L5K.rl1; exact Q1|]. split; [exact RA0|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536. split.
    - apply (L5SAR.astk_sub ar Mq Mq sp 20480 FR 12288 ASTKq); [intros w D; exact D| clear - HFR; lia| clear; lia| clear - HFR; lia| exact SPF16].
    - apply (PMKB.shadow_zero_sub Mq (sp - 20480) 2560); [apply SPd8; reflexivity| | clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZq].
      replace (sp - FR - 12288) with (sp - (FR + 12288)) by lia. apply SPd8. clear - HFR; destruct HFR as [-> | [-> | [-> | ->]]]; reflexivity. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS HFR; lia. }
  { rewrite L5K.rl10. exact Q10. }
  { exact AOV. }
  { exact Q8m. }
  { exact EAq. }
  { exact HLT. }
  { exact BASEq. }
  { exact CELLS. }
  intros fx2 R2 M2 md2 LK2 Aw2 RP2 EA2 HP2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2.

  assert (OWs : forall a0, sp - 20480 <= a0 < sp -> L5.outside [(ov + 24, 24)] a0).
  { intros a0 Ha0 r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha0 Q2' SLO; lia. }
  assert (FRAME12 : forall a0, sp - FR <= a0 < sp -> M2 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT HFR; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT HFR; lia| intros Y; clear - Ha0 Y; lia].
    - apply OWs. clear - Ha0 HFR; lia. }
  assert (EKe : L5SAR.ek L ar LBZ FF sp 20480 [(ov + 24, 24)] Mq M2).
  { apply (L5SAR.ek_callee L ar LBZ [] FF [] sp 20480 (sp - FR) 12288 [(ov + 24, 24)] [(ov + 24, 24)] Mq M2 HP2); [clear - HFR; lia| clear - HFR; lia| intros a0 _ O; exact O]. }
  assert (EK12 : L5SAR.ek L ar LBZ FF sp 20480 Ws Mq M2).
  { apply (L5SAR.ek_W L ar LBZ FF sp 20480 Ws _ Mq M2 EKe). intros a0 O r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. intros Y.
    apply (O (ov, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
  assert (DK12 : L5SAR.dk L ar LBZ FF sp 20480 Mq M2) by (apply (L5SAR.dk_callee L ar LBZ [] FF [] sp 20480 (sp - FR) 12288 [(ov + 24, 24)] Mq M2 HP2); clear - HFR; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480).
  { apply (PMKB.astk_after_ahpres L ar LBZ FF Mq M2 sp 20480 (sp - FR) 12288 [(ov + 24, 24)] ASTKq HP2); [clear - HFR; lia| clear - HFR; lia| clear; lia| exact STOP]. }
  pose proof ws_wapp as WAPP.
  assert (SZ2 : shadow_zero M2 (sp - 20480) 2560).
  { apply (PMKB.stksh_keepA L ar LBZ FF sp 20480 Ws Mq M2 EK12 WAPP (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZq]. }
  assert (WAPPe : PMKB.wapp [(ov + 24, 24)]).
  { apply PMKB.wapp_cons; [| apply PMKB.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - QBIG'. lia. }
  apply (KX fx2 R2 M2 md2 LK2 Aw2); [| exact RP2].
  unfold inv. split; [exact (FC_frame Mq M2 FRAME12 FCq)|]. split; [exact ASTK2|]. split; [exact SZ2|].
  split; [exact (L5LZ.model_rt_trans model mdq md2 MRTq MRT2)|]. split; [exact AM2|].
  split; [intros x Hx; apply ILKq; apply ILK2; exact Hx|]. split; [intros x Hx; apply IAW2; apply IAWq; exact Hx|].
  split.
  { assert (EO : PEC.enc_own (PEC.ENC (PEC.en_b enq) (PEC.en_k enq) (PEC.en_stk enq ++ [it]) (PEC.en_depth enq)) = PEC.enc_own enq) by (unfold PEC.enc_own; cbn [PEC.en_b PEC.en_k]; reflexivity).
    refine (ri_perm _ _ FF LK2 crq Aw2 M2 _ _ HH2). unfold PEC.owned, LBZ. rewrite EO, <- !app_assoc. apply Permutation_app_swap_app. }
  split; [exact EA2|].
  split.
  { apply (PECFA.sink_keepA RSEGS L ar LBZ FF sp 20480 [(ov + 24, 24)] Mq M2 EKe WAPPe FRBq BRBZ P osk kq AOSK); [| exact KINCq| | exact SKAq].
    - intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Hi Eov Eosk; lia.
    - intros Hc i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd].
      assert (IN : In (PESK.sk_b kq, PESK.sk_c kq) (PEC.enc_own enq ++ LBZ)).
      { apply in_or_app. right. apply KINCq. unfold PESK.sink_own. replace (PESK.sk_c kq =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hc; lia). left. reflexivity. }
      destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ ov 56 HHZ IN AOV) as [Xa|Xa]; clear - Xa Hi; lia. }
  split; [clear - CLq; lia|].
  split; [exact (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mq M2 EKq (PMKB.ek_sublb L ar LBZ LBc0 FF sp 20480 Ws Mq M2 ZINCq EK12))|].
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M2 DKq (PMKB.dk_sublb L ar LBZ LBc0 FF sp 20480 Mq M2 ZINCq DK12))|].
  unfold PMSP.credit_keep, PECA.pot_encA in CKq |- *. cbn [PEC.en_k]. clear - CKq. lia.
Qed.

Lemma eslow_call (pc a ra0 : Z) cells (it : eitem) (fxq : FPState) Rq Mq mdq LKq Awq crq kq enq :
  PECEPA.eslow_spec_at RSEGS AD EE L ar HI pc cells ->
  inv Mq mdq LKq Awq crq kq a enq -> Z.of_nat (length (PEC.en_stk enq)) = PEC.ecap (PEC.en_k enq) -> Z.of_nat (length (PEC.en_stk enq)) <= MAX_DEPTH -> L5.ra_ok ra0 ->
  getr Rq (reg 1) = Z_to_bv 64 ra0 -> getr Rq (reg 2) = Z_to_bv 64 (sp - FR) -> getr Rq (reg 10) = Z_to_bv 64 (PMSPA.o_v AD fb + 24) -> csk Rq ->
  cells FF (sp - FR) (PMSPA.o_v AD fb) Mq Rq it ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 B, inv M2 md2 LK2 Aw2 (adebit L crq (PEC.ESZ * PEC.ecap (PEC.en_k enq + 1))) kq a
                                            (PEC.ENC B (PEC.en_k enq + 1) (PEC.en_stk enq ++ [it]) (PEC.en_depth enq)) ->
      regs_preserved Rq R2 -> getr R2 (reg 10) = Z_to_bv 64 (B + PEC.ESZ * Z.of_nat (length (PEC.en_stk enq)) + PEC.ESZ) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R2 ra0 M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq pc Mq mdq) K.
Proof.
  intros EP INV HEQ HLEN RA0 Q1 Q2 Q10 QCS CELLS KX. entry_facts. name_objs. pose proof RA0 as (Hra1 & Hra2).
  pose proof INV as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  set (LBq := PEC.owned s enq kq ++ LBX) in HHq.
  set (LBZ := PM.parser_own s ++ PESK.sink_own kq ++ LBX).
  assert (PERMq : Permutation LBq (PEC.enc_own enq ++ LBZ)).
  { unfold LBq, LBZ, PEC.owned. rewrite <- !app_assoc. apply Permutation_app_swap_app. }
  pose proof (ri_perm _ _ FF LKq crq Awq Mq _ PERMq HHq) as HHZ.
  assert (ZINCq : incl LBc0 LBZ) by (unfold LBc0, LBZ; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (KINCq : incl (PESK.sink_own kq) LBZ) by (unfold LBZ; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (BRBZ : forall x, In x LBZ -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
  { intros x Hx. apply (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHZ). apply in_or_app. right. exact Hx. }
  assert (FRBq : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
  pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply AOF; clear - Eosk; lia).
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (AOV : PMSPA.aobjA FF ov 56) by (apply AOF; clear - Eov; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKB.aobj_of_aobjA FF osk 24 AOSK K8) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & KBIG & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKB.aobj_of_aobjA FF ov 56 AOV Q8m) ltac:(lia) ltac:(reflexivity)) as ((Q1' & Q2' & Q3' & Q4' & Q5') & QBIG' & _).
  pose proof EAq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EKq' & ELENq & _).
  destruct (keepf Mq EKq) as (_ & _ & _ & BASEq & _).

  assert (CRq : PMSP.credit_le (PECA.pot_encA L ar P enq kq) crq).
  { unfold PMSP.credit_le, PMSP.credit_keep in CRED, CKq |- *. clear - CRED CKq. lia. }
  assert (K11 : 0 <= PEC.en_k enq <= 11).
  { destruct (Z.eq_dec (PEC.en_k enq) 12) as [E12|NE]; [| clear - EKq' NE; lia].
    exfalso. rewrite E12 in HEQ. unfold PEC.ecap in HEQ. cbn in HEQ. clear - HEQ HLEN. unfold MAX_DEPTH in HLEN. lia. }
  pose proof EP as EPX. unfold PECEPA.eslow_spec_at in EPX.
  apply (EPX fxq Rq Mq mdq K LBZ FF LKq Awq crq ov fb enq it (sp - FR) ra0 HHZ AMq K0); clear EPX.
  {
    split; [rewrite L5K.rl1; exact Q1|]. split; [exact RA0|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536. split.
    - apply (L5SAR.astk_sub ar Mq Mq sp 20480 FR 12288 ASTKq); [intros w D; exact D| clear - HFR; lia| clear; lia| clear - HFR; lia| exact SPF16].
    - apply (PMKB.shadow_zero_sub Mq (sp - 20480) 2560); [apply SPd8; reflexivity| | clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZq].
      replace (sp - FR - 12288) with (sp - (FR + 12288)) by lia. apply SPd8. clear - HFR; destruct HFR as [-> | [-> | [-> | ->]]]; reflexivity. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS HFR; lia. }
  { rewrite L5K.rl10. exact Q10. }
  { exact AOV. }
  { exact Q8m. }
  { exact EAq. }
  { exact HEQ. }
  { exact HLEN. }
  { exact BASEq. }
  { exact CELLS. }
  { exact (proj1 (estk_credit Mq enq kq crq K11 SKAq CRq)). }
  intros fx2 R2 M2 md2 LK2 Aw2 B RP2 EA2 RA10 HP2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2.

  assert (OWs : forall a0, sp - 20480 <= a0 < sp -> L5.outside [(ov + 24, 24)] a0).
  { intros a0 Ha0 r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha0 Q2' SLO; lia. }
  assert (FRAME12 : forall a0, sp - FR <= a0 < sp -> M2 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT HFR; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT HFR; lia| intros Y; clear - Ha0 Y; lia].
    - apply OWs. clear - Ha0 HFR; lia. }
  assert (EKe : L5SAR.ek L ar LBZ FF sp 20480 [(ov + 24, 24)] Mq M2).
  { apply (L5SAR.ek_callee L ar LBZ [] FF [] sp 20480 (sp - FR) 12288 [(ov + 24, 24)] [(ov + 24, 24)] Mq M2 HP2); [clear - HFR; lia| clear - HFR; lia| intros a0 _ O; exact O]. }
  assert (EK12 : L5SAR.ek L ar LBZ FF sp 20480 Ws Mq M2).
  { apply (L5SAR.ek_W L ar LBZ FF sp 20480 Ws _ Mq M2 EKe). intros a0 O r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. intros Y.
    apply (O (ov, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
  assert (DK12 : L5SAR.dk L ar LBZ FF sp 20480 Mq M2) by (apply (L5SAR.dk_callee L ar LBZ [] FF [] sp 20480 (sp - FR) 12288 [(ov + 24, 24)] Mq M2 HP2); clear - HFR; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480).
  { apply (PMKB.astk_after_ahpres L ar LBZ FF Mq M2 sp 20480 (sp - FR) 12288 [(ov + 24, 24)] ASTKq HP2); [clear - HFR; lia| clear - HFR; lia| clear; lia| exact STOP]. }
  pose proof ws_wapp as WAPP.
  assert (SZ2 : shadow_zero M2 (sp - 20480) 2560).
  { apply (PMKB.stksh_keepA L ar LBZ FF sp 20480 Ws Mq M2 EK12 WAPP (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZq]. }
  assert (WAPPe : PMKB.wapp [(ov + 24, 24)]).
  { apply PMKB.wapp_cons; [| apply PMKB.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - QBIG'. lia. }
  apply (KX fx2 R2 M2 md2 LK2 Aw2 B); [| exact RP2| exact RA10].
  unfold inv. split; [exact (FC_frame Mq M2 FRAME12 FCq)|]. split; [exact ASTK2|]. split; [exact SZ2|].
  split; [exact (L5LZ.model_rt_trans model mdq md2 MRTq MRT2)|]. split; [exact AM2|].
  split; [intros x Hx; apply ILKq; apply ILK2; exact Hx|]. split; [intros x Hx; apply IAW2; apply IAWq; exact Hx|].
  split; [refine (ri_perm _ _ FF LK2 _ Aw2 M2 _ _ HH2); unfold PEC.owned, LBZ; rewrite <- !app_assoc; apply Permutation_app_swap_app|].
  split; [exact EA2|].
  split.
  { apply (PECFA.sink_keepA RSEGS L ar LBZ FF sp 20480 [(ov + 24, 24)] Mq M2 EKe WAPPe FRBq BRBZ P osk kq AOSK); [| exact KINCq| | exact SKAq].
    - intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Hi Eov Eosk; lia.
    - intros Hc i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd].
      assert (IN : In (PESK.sk_b kq, PESK.sk_c kq) (PEC.enc_own enq ++ LBZ)).
      { apply in_or_app. right. apply KINCq. unfold PESK.sink_own. replace (PESK.sk_c kq =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hc; lia). left. reflexivity. }
      destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ ov 56 HHZ IN AOV) as [Xa|Xa]; clear - Xa Hi; lia. }
  split; [clear - CLq; lia|].
  split; [exact (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mq M2 EKq (PMKB.ek_sublb L ar LBZ LBc0 FF sp 20480 Ws Mq M2 ZINCq EK12))|].
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M2 DKq (PMKB.dk_sublb L ar LBZ LBc0 FF sp 20480 Mq M2 ZINCq DK12))|].
  pose proof (proj2 (estk_credit Mq enq kq crq K11 SKAq CRq) (PEC.ENC B (PEC.en_k enq + 1) (PEC.en_stk enq ++ [it]) (PEC.en_depth enq)) eq_refl) as CK2.
  unfold PMSP.credit_keep in CKq, CK2 |- *. clear - CKq CK2. lia.
Qed.

Let Wt : list L5.range := (PMSPA.o_v AD fb, 56) :: (PESK.o_sink EE fb, 24) :: (PMSPA.o_ec AD fb, 16) :: PMSPA.err_W AD.
Lemma wt_wapp : PMKB.wapp Wt.
Proof.
  entry_facts. unfold Wt. apply PMKB.wapp_cons; [cbn [fst snd]; unfold PMSPA.o_v; cbn [pa_off_v PeCLayoutB.CADDR_B]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - F1 F2 FSAPP; lia|].
  apply PMKB.wapp_cons; [cbn [fst snd pe_off_sink PeCLayoutB.EADDR_B]; unfold PESK.o_sink; cbn [pe_off_sink PeCLayoutB.EADDR_B]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - F1 F2 FSAPP; lia|].
  apply PMKB.wapp_cons; [cbn [fst snd]; unfold PMSPA.o_ec; cbn [pa_off_ec PeCLayoutB.CADDR_B]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - F1 F2 FSAPP; lia|].
  unfold PMSPA.err_W. cbn [pa_errcat_guard pa_atexit PeCLayoutB.CADDR_B].
  apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear; lia|]. apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear; lia|]. apply PMKB.wapp_nil.
Qed.
Lemma wt_ws a : L5.outside Wt a -> L5.outside Ws a.
Proof. intros O rr [<-|[<-|[]]]; apply O; unfold Wt; [left; reflexivity| right; left; reflexivity]. Qed.
Lemma wt_wenc a : L5.outside (PEC.W_enc AD EE fb) a -> L5.outside Wt a.
Proof.
  intros O rr Hin. apply O. unfold Wt in Hin. unfold PEC.W_enc. cbn [app].
  destruct Hin as [<-|[<-|[<-|Hin]]]; [left; reflexivity| right; left; reflexivity| right; right; left; reflexivity| right; right; right; exact Hin].
Qed.
Lemma wt_rng rr a : In rr Wt -> L5.in_rng rr a ->
  (PMSPA.o_v AD fb <= a < PMSPA.o_v AD fb + 56) \/ (PESK.o_sink EE fb <= a < PESK.o_sink EE fb + 24) \/ (PMSP.o_ec AD fb <= a < PMSP.o_ec AD fb + 16)
  \/ (0x678780 <= a < 0x678782) \/ (0x69a1d0 <= a < 0x69a3f0).
Proof.
  intros Hin Hr. unfold Wt in Hin. unfold L5.in_rng in Hr.
  destruct Hin as [<-|[<-|[<-|Hin]]]; [cbn [fst snd] in Hr; left; exact Hr| cbn [fst snd] in Hr; right; left; exact Hr| cbn [fst snd] in Hr; right; right; left; exact Hr|].
  right; right; right. unfold PMSPA.err_W, PMSP.err_W in Hin. cbn [pa_errcat_guard pa_atexit PeCLayoutB.CADDR_B] in Hin.
  destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; [left; exact Hr| right; clear - Hr; lia].
Qed.

Lemma keepf2 Mi : L5SAR.ek L ar LBc0 FF sp 20480 Wt M Mi ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mi (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s /\ PM.iss_at RSEGS AD PMSPA.accA Mi (PMSPA.o_is AD fb) str sm
  /\ L5.u64_at RSEGS Mi (PMSPA.o_p AD fb + 384) (PMSPA.o_v AD fb) /\ PMSTA.base_okA RSEGS AD Mi
  /\ PEC.content_ok RSEGS AD Mi fb p (PM.p_src s) str sm /\ PMSPA.accA Mi (PMSPA.o_p AD fb) PECA.RDR_BYTES.
Proof.
  intros EK. entry_facts. name_objs.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (BRc0 : forall x, In x LBc0 -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by (intros x Hx; apply BRB; apply INC0; exact Hx).
  assert (PINC : incl (PM.parser_own s) LBc0) by (unfold LBc0; apply incl_appl; apply incl_refl).
  assert (SINC : incl (PM.vs_own str) LBc0) by (unfold LBc0; apply incl_appr; exact INCS).
  pose proof wt_wapp as WAPP.
  assert (AOV : PMSPA.aobjA FF ov 56) by (apply AOF; clear - Eov; lia).
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply AOF; clear - Eosk; lia).
  assert (AOEC : PMSPA.aobjA FF oec 16) by (apply AOF; clear - Eoec; lia).
  assert (AOIS : PMSPA.aobjA FF ois 272) by (apply AOF; clear - Eois; lia).
  assert (I8 : ois mod 8 = 0) by (rewrite Eois; replace (fb + 96) with (fb + 8 * 12) by (clear; lia); apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ois 272 sp 20480 HH (PMKB.aobj_of_aobjA FF ois 272 AOIS I8) ltac:(clear; lia) ltac:(reflexivity)) as ((I1 & _) & _).
  assert (OUT : forall i, ~ (ov <= i < ov + 56) -> ~ (osk <= i < osk + 24) -> ~ (oec <= i < oec + 16) -> ~ (0x678780 <= i < 0x678782) -> ~ (0x69a1d0 <= i < 0x69a3f0) -> L5.outside Wt i).
  { intros i N0 N1 N2 N3 N4 rr Hin Hr. destruct (wt_rng rr i Hin Hr) as [Y|[Y|[Y|[Y|Y]]]]; [exact (N0 Y)| exact (N1 Y)| exact (N2 Y)| exact (N3 Y)| exact (N4 Y)]. }
  assert (OUTB : forall q m, In (q, m) LBc0 -> PMKB.blk_out Wt q m).
  { intros q m Hq i Hi. pose proof (INC0 _ Hq) as HqLB.
    destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m ov 56 HH HqLB AOV) as [Xo|Xo];
    destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m osk 24 HH HqLB AOSK) as [Xa|Xa];
    destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m oec 16 HH HqLB AOEC) as [Xb|Xb];
    destruct (PMBSK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH HqLB) as [Xc|Xc]; apply OUT; clear - Xo Xa Xb Xc Hi; lia. }
  assert (OUTO : forall a m, (a + m <= ov \/ ov + 56 <= a) -> (a + m <= osk \/ osk + 24 <= a) -> (a + m <= oec \/ oec + 16 <= a) -> 0x69c000 <= a -> forall i, a <= i < a + m -> L5.outside Wt i)
    by (intros a m Xo Xa Xb Xc i Hi; apply OUT; clear - Xo Xa Xb Xc Hi; lia).
  assert (Iq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LBc0) by (apply PINC; unfold PM.parser_own, PM.src_own; left; reflexivity).
  split.
  { apply (PMKB.parser_keepA RSEGS AD L ar LBc0 FF sp 20480 Wt M Mi EK WAPP FRB BRc0 op ois s (AOF op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia)) PINC); [| | | | exact PA].
    - apply OUTO; clear - Eop Eov Eosk Eoec Eois I1; lia.
    - apply OUTB. exact Iq.
    - apply OUTB. apply PINC. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
    - intros c n0 q E1. apply OUTB. apply PINC. unfold PM.parser_own, PM.vs_own. rewrite E1. right; right; left. reflexivity. }
  split.
  { apply (PMKB.iss_keepA RSEGS AD L ar LBc0 FF sp 20480 Wt M Mi EK WAPP FRB BRc0 ois str sm AOIS SINC); [| | exact IA].
    - apply OUTO; clear - Eov Eosk Eoec Eois I1; lia.
    - intros c n0 q E1. refine (OUTB q c _). apply SINC. unfold PM.vs_own. rewrite E1. left. reflexivity. }
  split.
  { apply (PMKB.u64_keepA RSEGS L ar LBc0 FF sp 20480 Wt M Mi EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF].
    apply OUTO; clear - Eop Eov Eosk Eoec Eois I1; lia. }
  split.
  { apply (PMBPAR.base_keepW L ar C LY LBc0 FF sp 20480 Wt M Mi EK); [| | | | exact BASE].
    - intros a Ha. apply OUT; clear - Ha Eov Eosk Eoec Eois I1; lia.
    - intros a Ha. apply OUT; clear - Ha Eov Eosk Eoec Eois I1; lia.
    - apply OUT; clear - Eov Eosk Eoec Eois I1; lia.
    - intros a Ha. apply OUT; clear - Ha Eov Eosk Eoec Eois I1; lia. }
  split.
  { apply (content_keepA' LBc0 FF sp 20480 Wt M Mi fb p s str sm op EK WAPP FRB BRc0 AOIS); [| exact SINC| exact Iq| exact OUTB| exact IA| exact PA| exact CONT].
    fold ois. apply OUTO; clear - Eov Eosk Eoec Eois I1; lia. }
  exact (PMKB.acc_keepA' L ar LBc0 FF sp 20480 Wt M Mi EK WAPP FRB op 392 (AOF op 392 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia)) ACCR).
Qed.

Definition inve (Mi : word -> option byte) (mdi : Model) (LKi : list fframe) (Awi : list (Z * Z)) (cri : credit) (ki : PESK.sink) (a : Z) (eni : PEC.enc) (v : Z) : Prop :=
  FC Mi /\ L5CA.astk ar Mi sp 20480 /\ shadow_zero Mi (sp - 20480) 2560
  /\ model_rt model mdi /\ L5CA.amodel_ok Awi mdi /\ incl LKi LK /\ incl Aw Awi
  /\ ri_inv HI (PEC.owned s eni ki ++ LBX) FF LKi cri Awi Mi (vml_of mdi)
  /\ PECA.enc_atA RSEGS EE L ar Mi (PMSPA.o_v AD fb) fb eni /\ PESKA.sink_atA RSEGS L ar P Mi (PESK.o_sink EE fb) ki
  /\ xlo + a <= PESK.sk_z ki <= xhi + a
  /\ L5SAR.ek L ar LBc0 FF sp 20480 Wt M Mi /\ L5SAR.dk L ar LBc0 FF sp 20480 M Mi
  /\ PMSP.credit_keep cr cri (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P eni ki)
  /\ PMSPA.ec_at RSEGS Mi (PMSPA.o_ec AD fb) v (pa_errcat_obj AD) /\ PESTA.err_okA RSEGS AD AAD EE Mi true.

Lemma mkec_call (a ra0 v : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq enq :
  inv Mq mdq LKq Awq crq kq a enq -> L5.ra_ok ra0 -> 1 <= v <= 64 ->
  getr Rq (reg 1) = Z_to_bv 64 ra0 -> getr Rq (reg 2) = Z_to_bv 64 (sp - FR) -> getr Rq (reg 10) = Z_to_bv 64 (PMSPA.o_ec AD fb) -> getr Rq (reg 11) = Z_to_bv 64 v -> csk Rq ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2, inve M2 md2 LK2 Aw2 crq kq a enq v -> regs_preserved Rq R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 ra0 M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xafda8 Mq mdq) K.
Proof.
  intros INV RA0 HV Q1 Q2 Q10 Q11 QCS KX. entry_facts. name_objs.
  pose proof INV as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  destruct (keepf Mq EKq) as (_ & _ & _ & BASEq & ERRq & _ & ECSq & _).
  assert (ECD : L5.defined Mq oec 16 /\ PMSPA.accA Mq oec 16).
  { unfold PECA.ec_stateA in ECSq. fold oec in ECSq.
    destruct xec; [destruct ECSq as (v0 & _ & (_ & _ & D' & A')); exact (conj D' A')| destruct ECSq as (_ & _ & D' & A'); exact (conj D' A')]. }
  set (LBq := PEC.owned s enq kq ++ LBX) in *.
  assert (XINCq : incl LBc0 LBq) by (unfold LBc0, LBq, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (EINCq : incl (PEC.enc_own enq) LBq) by (unfold LBq, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (KINCq : incl (PESK.sink_own kq) LBq) by (unfold LBq, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHq) as BRBq.
  pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq) as FRBq.
  assert (AOV : PMSPA.aobjA FF ov 56) by (apply AOF; clear - Eov; lia).
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply AOF; clear - Eosk; lia).
  assert (AOEC : PMSPA.aobjA FF oec 16) by (apply AOF; clear - Eoec; lia).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by (clear; lia); apply FB8).
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by (clear; lia); apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKB.aobj_of_aobjA FF osk 24 AOSK K8) ltac:(clear; lia) ltac:(reflexivity)) as ((KOSK & _) & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKB.aobj_of_aobjA FF ov 56 AOV Q8m) ltac:(clear; lia) ltac:(reflexivity)) as ((Q1' & Q2' & Q3' & _) & QBIG' & _).
  pose proof MKEC as MX. unfold PECSB.make_ec_spec, PECSPA.make_ec_spec in MX.
  unfold PMSPA.cfg.
  apply (MX fxq Rq Mq mdq K LBq FF LKq Awq crq oec v (sp - FR) ra0 e HHq AMq K0); clear MX.
  { split; [rewrite L5K.rl1; exact Q1|]. split; [exact RA0|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3, (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4, (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792. split.
    - apply (L5SAR.astk_sub ar Mq Mq sp 20480 FR 14336 ASTKq); [intros w D; exact D| clear - HFR; lia| clear; lia| clear - HFR; lia| exact SPF16].
    - apply (PMKB.shadow_zero_sub Mq (sp - 20480) 2560); [apply SPd8; reflexivity| | clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZq].
      replace (sp - FR - 14336) with (sp - (FR + 14336)) by lia. apply SPd8. clear - HFR; destruct HFR as [-> | [-> | [-> | ->]]]; reflexivity. }
  { apply (ffroomA_mono 4 1 FF LK LKq FRM ILKq NDFq). clear; lia. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS HFR; lia. }
  { rewrite L5K.rl10. exact Q10. }
  { rewrite L5K.rl11. exact Q11. }
  { exact HV. }
  { exact AOEC. }
  { rewrite Eoec. replace (fb + 1120) with (fb + 8 * 140) by (clear; lia). apply FB8. }
  { exact (proj1 ECD). }
  { exact (proj2 ECD). }
  { exact BASEq. }
  { exact ERRq. }
  intros fx6 R6 M6 md6 LK6 Aw6 RP6 EC6 ERR6 HP6 MRT6 ILK6 IAW6 AM6 HH6.
  change (PMSPA.pm_scr 1) with 14336 in HP6.
  set (W2 := (oec, 16) :: (if e then [] else PMSPA.err_W AD)) in HP6.
  assert (W2R : forall rr a0, In rr W2 -> L5.in_rng rr a0 -> (oec <= a0 < oec + 16) \/ (0x678780 <= a0 < 0x678782) \/ (0x69a1d0 <= a0 < 0x69a3f0)).
  { intros rr a0 Hin Hr. unfold W2 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|Hin]; [left; cbn [fst snd] in Hr; exact Hr|]. right. destruct e; [destruct Hin|].
    unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PeCLayoutB.CADDR_B] in Hin.
    destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; [left; exact Hr| right; clear - Hr; lia]. }
  assert (WT2 : forall a0, L5.outside Wt a0 -> L5.outside W2 a0).
  { intros a0 O rr Hin. unfold W2 in Hin. destruct Hin as [<-|Hin]; [apply O; unfold Wt; right; right; left; reflexivity|]. destruct e; [destruct Hin|].
    apply O. unfold Wt. right; right; right. exact Hin. }
  assert (OW2 : forall a0, sp - 20480 <= a0 < sp -> L5.outside W2 a0).
  { intros a0 Ha0 rr Hin Hr. destruct (W2R rr a0 Hin Hr) as [Y|[Y|Y]]; clear - Ha0 Y Eoec Eosk KOSK F2 FSCEIL SLO; lia. }
  assert (FRAME12 : forall a0, sp - FR <= a0 < sp -> M6 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP6 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT HFR; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT HFR; lia| intros Y; clear - Ha0 Y; lia].
    - apply OW2. clear - Ha0 HFR; lia. }
  assert (EK6 : L5SAR.ek L ar LBq FF sp 20480 W2 Mq M6).
  { apply (L5SAR.ek_callee L ar LBq [] FF [] sp 20480 (sp - FR) 14336 W2 W2 Mq M6 HP6); [clear - HFR; lia| clear - HFR; lia| intros a0 _ O; exact O]. }
  assert (DK6 : L5SAR.dk L ar LBq FF sp 20480 Mq M6) by (apply (L5SAR.dk_callee L ar LBq [] FF [] sp 20480 (sp - FR) 14336 W2 Mq M6 HP6); clear - HFR; lia).
  assert (ASTK6 : L5CA.astk ar M6 sp 20480).
  { apply (PMKB.astk_after_ahpres L ar LBq FF Mq M6 sp 20480 (sp - FR) 14336 W2 ASTKq HP6); [clear - HFR; lia| clear - HFR; lia| clear; lia| exact STOP]. }
  assert (WAPP2 : PMKB.wapp W2).
  { intros rr Hin. unfold W2 in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|Hin]; [cbn [fst snd]; clear - Eoec F1 F2 FSAPP; lia|].
    destruct e; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PeCLayoutB.CADDR_B] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia. }
  assert (SZ6 : shadow_zero M6 (sp - 20480) 2560).
  { apply (PMKB.stksh_keepA L ar LBq FF sp 20480 W2 Mq M6 EK6 WAPP2 (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZq]. }
  assert (OUTB2 : forall q m, In (q, m) LBq -> forall i, q <= i < q + m -> L5.outside W2 i).
  { intros q m Hq i Hi rr Hin Hr. destruct (W2R rr i Hin Hr) as [Y|[Y|Y]].
    - destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m oec 16 HHq Hq AOEC) as [Z'|Z']; clear - Hi Y Z'; lia.
    - destruct (PMBSK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HHq Hq) as [Z'|Z']; clear - Hi Y Z'; lia.
    - destruct (PMBSK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HHq Hq) as [Z'|Z']; clear - Hi Y Z'; lia. }
  assert (EA6 : PECA.enc_atA RSEGS EE L ar M6 ov fb enq).
  { apply (PECFA.enc_keepA RSEGS EE L ar LBq FF sp 20480 W2 Mq M6 EK6 WAPP2 FRBq BRBq ov fb enq AOV); [| exact EINCq| | exact EAq].
    - intros i Hi rr Hin Hr. destruct (W2R rr i Hin Hr) as [Y|[Y|Y]]; clear - Hi Y Eov Eoec Eosk KOSK Q1'; lia.
    - intros Hk. hnf. apply OUTB2. apply EINCq. unfold PEC.enc_own. destruct (Z.eqb_spec (PEC.en_k enq) 0) as [E0|E0]; [exfalso; clear - Hk E0; lia| left; reflexivity]. }
  assert (SKA6 : PESKA.sink_atA RSEGS L ar P M6 osk kq).
  { apply (PECFA.sink_keepA RSEGS L ar LBq FF sp 20480 W2 Mq M6 EK6 WAPP2 FRBq BRBq P osk kq AOSK); [| exact KINCq| | exact SKAq].
    - intros i Hi rr Hin Hr. destruct (W2R rr i Hin Hr) as [Y|[Y|Y]]; clear - Hi Y Eoec Eosk KOSK; lia.
    - intros Hk. hnf. apply OUTB2. apply KINCq. unfold PESK.sink_own. destruct (Z.eqb_spec (PESK.sk_c kq) 0) as [E0|E0]; [exfalso; clear - Hk E0; lia| left; reflexivity]. }
  apply (KX fx6 R6 M6 md6 LK6 Aw6); [| exact RP6].
  unfold inve. split; [exact (FC_frame Mq M6 FRAME12 FCq)|]. split; [exact ASTK6|]. split; [exact SZ6|].
  split; [exact (L5LZ.model_rt_trans model mdq md6 MRTq MRT6)|]. split; [exact AM6|].
  split; [intros x Hx; apply ILKq; apply ILK6; exact Hx|]. split; [intros x Hx; apply IAW6; apply IAWq; exact Hx|].
  split; [exact HH6|].
  split; [exact EA6|]. split; [exact SKA6|]. split; [exact CLq|].
  split.
  { apply (L5SAR.ek_trans L ar LBc0 FF sp 20480 Wt M Mq M6).
    - exact (L5SAR.ek_W L ar LBc0 FF sp 20480 Wt Ws M Mq EKq wt_ws).
    - exact (L5SAR.ek_W L ar LBc0 FF sp 20480 Wt W2 Mq M6 (PMKB.ek_sublb L ar LBq LBc0 FF sp 20480 W2 Mq M6 XINCq EK6) WT2). }
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M6 DKq (PMKB.dk_sublb L ar LBq LBc0 FF sp 20480 Mq M6 XINCq DK6))|].
  split; [exact CKq|]. split; [exact EC6| exact ERR6].
Qed.

Lemma vis_facts_e Mq mdq LKq Awq crq kq a enq v : inve Mq mdq LKq Awq crq kq a enq v ->
  let H := ahid Awq mdq in let MV := mrestrict H Mq in
  L5.img_clear MV 1273856 1306624 /\ L5.u64_at RSEGS MV 1335544 SBL /\ L5.u32_at RSEGS MV 1335552 1
  /\ 140735332487168 + 20480 <= sp <= 140737488355328 /\ sp mod 16 = 0 /\ L5.writable RSEGS MV (sp - FR) FR
  /\ (forall a0 v0, sp - FR <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS Mq a0 v0 -> L5.u64_at RSEGS MV a0 v0) /\ FC Mq.
Proof.
  intros INV6. entry_facts.
  pose proof INV6 as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq HHq) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _).
  set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C Mq LYa ST) as (GOT & CSB & CUAR & _).
  pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LKq crq Awq Mq mdq sp 20480 FR HHq ASTKq ltac:(clear - HFR; lia)) as (_ & _ & SWR).
  split; [apply L5A.img_clear_mrestrict; exact GOT|].
  split; [apply (proj2 (L5A.u64_at_vis H Mq 1335544 SBL (VIMG 1335544 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB|].
  split; [apply (proj2 (L5A.u32_at_vis H Mq 1335552 1 (VIMG 1335552 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR|].
  split; [clear - SLO SHI SPT; lia|]. split; [exact A16'|]. split; [exact SWR|].
  split; [| exact FCq].
  intros a0 v0 Ha1 Ha2 U. apply (proj2 (L5A.u64_at_vis H Mq a0 v0 (VIS a0 8 ltac:(clear - Ha1 SLO HFR; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO SPT HFR; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact U.
Qed.

Lemma finish_err a pcq (fxq : FPState) Rq Mq mdq LKq Awq crq kq (fx3 : FPState) R3 M3v enq v esq edq :
  inve Mq mdq LKq Awq crq kq a enq v -> 1 <= v <= 64 -> PEC.en_stk enq = rev esq -> PEC.en_depth enq = edq ->
  XF = ST xstk xpos xmore xdone xhalt xdepth true esq edq (xlo + a) (xhi + a) xbad ->
  msteps RSEGS (mst fxq Rq pcq (mrestrict (ahid Awq mdq) Mq)) (mst fx3 R3 r M3v) -> mem_grows (mrestrict (ahid Awq mdq) Mq) M3v ->
  (forall i, 0 <= i < 2 ^ 64 -> M3v (Z_to_bv 64 i) = mrestrict (ahid Awq mdq) Mq (Z_to_bv 64 i)) -> regs_preserved R R3 ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcq Mq mdq) K.
Proof.
  intros INV6 HV HSTK HED HXF MS3 MG3 FRZ3 RP3. entry_facts.
  pose proof INV6 as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq & ECq & ERRq).
  pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _).
  destruct (keepf2 Mq EKq) as (PA' & IA' & VREF' & BASE' & CONT' & ACCR').
  destruct CPRE as (_ & _ & _ & _ & _ & _ & _ & TBOK & _ & CL & _ & _ & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad X] in Lmore, Ldone, Ldepth, Lstk, Lpos, Lestk, Ledepth, Lz, Lbad.
  pose proof KONT as KT. rewrite HXF in KT.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq fxq fx3 Rq pcq R3 r M3v K HHq AMq MS3 MG3 FRZ3).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 AG3. pose proof (L5SAR.mem_eq_of_agree Mq M3 AG3) as EM. subst M3.
  apply (KT fx3 R3 Mq md3 LKq Awq enq kq true crq).
  - exact RP3.
  - unfold PECA.crun_preA.
    split; [exact PA'|]. split; [exact IA'|]. split; [exact EAq|]. split; [exact VREF'|]. split; [exact SKAq|].
    split; [exact BASE'|]. split; [exact ERRq|]. split; [exact TBOK|]. split; [exact CONT'|].
    split.
    { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad].
      split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
      split; [exact HSTK|]. split; [exact HED|]. split; [clear - CLq; lia| exact Lbad]. }
    cbn [s_ec]. split; [unfold PECA.ec_stateA; exists v; split; [exact HV| exact ECq]|]. split; [intros _; reflexivity| exact ACCR'].
  - intros _; reflexivity.
  - change (PMSPA.pm_scr 4) with 20480. apply (L5SAR.ahpres_of L ar LBc0 FF sp 20480 _ M Mq); [| exact SDEFq| exact DKq].
    apply (L5SAR.ek_W L ar LBc0 FF sp 20480 _ Wt M Mq EKq). exact wt_wenc.
  - exact CKq.
  - exact (L5LZ.model_rt_trans model mdq md3 MRTq MRT3).
  - exact ILKq.
  - exact IAWq.
  - exact AM3.
  - exact HH3.
Qed.

Lemma pl_call (a ra0 n : Z) esq edq (fxq : FPState) Rq Mq mdq LKq Awq crq kq enq :
  inv Mq mdq LKq Awq crq kq a enq -> PEC.en_stk enq = rev esq -> PEC.en_depth enq = edq ->
  PECSPA.mp_enc p (ST xstk xpos xmore xdone xhalt xdepth xec esq edq (xlo + a) (xhi + a) xbad) ->
  PESKA.spa_hb P (xhi + a + pl_size n) -> 0 <= n <= UbjRef.INT64_MAX -> L5.ra_ok ra0 ->
  getr Rq (reg 1) = Z_to_bv 64 ra0 -> getr Rq (reg 2) = Z_to_bv 64 (sp - FR) -> getr Rq (reg 10) = Z_to_bv 64 (PMSPA.o_v AD fb) -> getr Rq (reg 11) = Z_to_bv 64 n -> csk Rq ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 cr2 k2, inv M2 md2 LK2 Aw2 cr2 k2 (a + pl_size n) enq -> regs_preserved Rq R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 ra0 M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xafe84 Mq mdq) K.
Proof.
  intros INV HSTK HED MPX HBX HN RA0 Q1 Q2 Q10 Q11 QCS KX. entry_facts. name_objs.
  pose proof INV as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  pose proof (inv_cpre Mq mdq LKq Awq crq kq a _ _ enq esq edq INV eq_refl eq_refl HSTK HED) as CPq.
  assert (XINCq : incl LBc0 (LBY enq)) by (unfold LBc0, LBY; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (EINCq : incl (PEC.enc_own enq) (LBY enq)) by (unfold LBY; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (FRBq : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply AOF; clear - Eosk; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKB.aobj_of_aobjA FF osk 24 AOSK K8) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & KBIG & _).
  pose proof PUTL as PX. unfold PECSB.put_length_spec, PECSPA.put_length_spec in PX. cbn [pe_put_length EE PeCLayoutB.EADDR_B] in PX.
  unfold PMSPA.cfg.
  apply (PX PMODE fxq Rq Mq mdq K LBX FF LKq Awq crq (sp - FR) ra0 fb cat n p (ST xstk xpos xmore xdone xhalt xdepth xec esq edq (xlo + a) (xhi + a) xbad) s str sm enq kq e HHq AMq K0); clear PX.
  { split; [rewrite L5K.rl1; exact Q1|]. split; [exact RA0|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3, (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4, (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 3) with 18432. change (18432 / 8) with 2304. split.
    - apply (L5SAR.astk_sub ar Mq Mq sp 20480 FR 18432 ASTKq); [intros w D; exact D| clear - HFR; lia| clear; lia| clear - HFR; lia| exact SPF16].
    - apply (PMKB.shadow_zero_sub Mq (sp - 20480) 2560); [apply SPd8; reflexivity| | clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZq].
      replace (sp - FR - 18432) with (sp - (FR + 18432)) by lia. apply SPd8. clear - HFR; destruct HFR as [-> | [-> | [-> | ->]]]; reflexivity. }
  { apply (ffroomA_mono 4 3 FF LK LKq FRM ILKq NDFq). clear; lia. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS HFR; lia. }
  { exact FOK. }
  { exact SPF16. }
  { rewrite L5K.rl10. exact Q10. }
  { rewrite L5K.rl11. exact Q11. }
  { exact HN. }
  { exact CPq. }
  { exact INCS. }
  { exact POK. }
  { exact MPX. }
  { cbn [s_hi]. exact HBX. }
  { unfold PMSP.credit_le, PMSP.credit_keep in CRED, CKq |- *. clear - CRED CKq. lia. }
  intros fx2 R2 M2 md2 LK2 Aw2 k2 cr2 RP2 CP2 HP2 CK2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 3) with 18432 in HP2. change (PM.parser_own s ++ PEC.enc_own enq ++ LBX) with (LBY enq) in HP2.

  assert (OWs : forall a0, sp - 20480 <= a0 < sp -> L5.outside Wpb a0).
  { intros a0 Ha0 r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk. clear - Ha0 K2 SLO; lia. }
  assert (FRAME12 : forall a0, sp - FR <= a0 < sp -> M2 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT HFR; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT HFR; lia| intros Y; clear - Ha0 Y; lia].
    - apply OWs. clear - Ha0 HFR; lia. }
  assert (EKpb : L5SAR.ek L ar (LBY enq) FF sp 20480 Wpb Mq M2).
  { apply (L5SAR.ek_callee L ar (LBY enq) [] FF [] sp 20480 (sp - FR) 18432 Wpb Wpb Mq M2 HP2); [clear - HFR; lia| clear - HFR; lia| intros a0 _ O; exact O]. }
  assert (EK12 : L5SAR.ek L ar (LBY enq) FF sp 20480 Ws Mq M2) by (apply (L5SAR.ek_W L ar (LBY enq) FF sp 20480 Ws Wpb Mq M2 EKpb); exact ws_wpb).
  assert (DK12 : L5SAR.dk L ar (LBY enq) FF sp 20480 Mq M2) by (apply (L5SAR.dk_callee L ar (LBY enq) [] FF [] sp 20480 (sp - FR) 18432 Wpb Mq M2 HP2); clear - HFR; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480).
  { apply (PMKB.astk_after_ahpres L ar (LBY enq) FF Mq M2 sp 20480 (sp - FR) 18432 Wpb ASTKq HP2); [clear - HFR; lia| clear - HFR; lia| clear; lia| exact STOP]. }
  pose proof ws_wapp as WAPP.
  assert (SZ2 : shadow_zero M2 (sp - 20480) 2560).
  { apply (PMKB.stksh_keepA L ar (LBY enq) FF sp 20480 Ws Mq M2 EK12 WAPP (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZq]. }
  pose proof CP2 as (_ & _ & EA2 & _ & SKA2 & _ & _ & _ & _ & CL2 & _).
  destruct CL2 as (_ & _ & _ & _ & _ & _ & _ & Lz2 & _). cbn [s_lo s_hi w_out] in Lz2.
  apply (KX fx2 R2 M2 md2 LK2 Aw2 cr2 k2); [| exact RP2].
  unfold inv. split; [exact (FC_frame Mq M2 FRAME12 FCq)|]. split; [exact ASTK2|]. split; [exact SZ2|].
  split; [exact (L5LZ.model_rt_trans model mdq md2 MRTq MRT2)|]. split; [exact AM2|].
  split; [intros x Hx; apply ILKq; apply ILK2; exact Hx|]. split; [intros x Hx; apply IAW2; apply IAWq; exact Hx|].
  split; [exact HH2|].
  split; [exact EA2|]. split; [exact SKA2|].
  split; [clear - Lz2; lia|].
  split; [exact (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mq M2 EKq (PMKB.ek_sublb L ar (LBY enq) LBc0 FF sp 20480 Ws Mq M2 XINCq EK12))|].
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M2 DKq (PMKB.dk_sublb L ar (LBY enq) LBc0 FF sp 20480 Mq M2 XINCq DK12))|].
  unfold PMSP.credit_keep in CKq, CK2 |- *. clear - CKq CK2. lia.
Qed.
End Call.
End WithHeap.
End PEBEKG.
