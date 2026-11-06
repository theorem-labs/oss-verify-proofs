(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5CoreSpecsAB0S9 L5StepARB0S9 L5CoreBRB0S9 L5ADetailHRB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAb PnStatics PmModelFactsA PmStep PeStepAB0 PmParStep PmParKit PeBSrcKit PeBParKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeShZ PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCFrameA PeEncKit PeBCReset1 PmBUarK PmBUar PeBPbIndSpec PeBEncNtbSpec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBEK1.
#[local] Transparent e_end_value.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).

Abbreviation SBL := 2147450880.
Abbreviation SM1 := 0x5edb0.
Abbreviation PBPC := 0xb120c.
Abbreviation PBIPC := 0xb2794.

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
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMB.ly_as0 L C LY.

Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.
Hypothesis PBI : PEPBI.push_back_indZ_specA RSEGS AD L ar HI PBIPC P.

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

Lemma ffroomA_mono h h' FF LK LK2 : PMSPA.ffroomA h FF LK -> incl LK2 LK -> NoDup (map ff_addr (FF ++ LK2)) -> h' <= h -> PMSPA.ffroomA h' FF LK2.
Proof.
  intros FR INC ND Hh kk Hk. specialize (FR kk Hk). rewrite L5SAR.ff_count_app in FR. rewrite L5SAR.ff_count_app.
  pose proof (L5SAR.ff_count_incl kk LK2 LK INC (L5SAR.nodup_of_map_app_r FF LK2 ND)) as C2. lia.
Qed.

Section Call.
Variables (FR NB : Z) (SAVED CSK : list nat).
Hypothesis HFR : FR = 96 \/ FR = 128.
Hypothesis HSV : SAVED = SV9 \/ SAVED = SV11.
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
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (e_end_value (XS NB)) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Let LB : list (Z * Z) := PEC.owned s en k ++ LBX.

Let LBc0 : list (Z * Z) := PM.parser_own s ++ LBX.

Definition EBX (ki : PESK.sink) : list (Z * Z) := PEC.enc_own en ++ PESK.sink_own ki.

Let Wk : list L5.range := (PESK.o_sink EE fb, 24) :: PEC.enc_own en.
Let spc : Z := sp - FR.
Let NSV : Z := Z.of_nat (length SAVED).
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

Lemma NSVv : NSV = 9 \/ NSV = 11.
Proof. unfold NSV. destruct HSV as [-> | ->]; [left|right]; reflexivity. Qed.

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
  - intros o n AO. exact (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m o n HH IN AO).
  - intros q' m' Hq'. apply (PMBSK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ q' m' q m HH); [| exact IN|].
    + unfold LB, PEC.owned. unfold LBc0 in Hq'. apply in_app_or in Hq'. destruct Hq' as [Y|Y]; apply in_or_app; [left; apply in_or_app; left; exact Y| right; exact Y].
    + unfold LBc0 in Hq'. apply in_app_or in Hq'. destruct Hq' as [Y|Y].
      * apply (PMBSK.fst_neq_appA (PM.parser_own s) (PEC.enc_own en ++ PESK.sink_own k ++ LBX) q' m' q m); [| exact Y|].
        { unfold LB, PEC.owned in ND. rewrite <- !app_assoc in ND. exact (PMBSK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ ltac:(unfold LB, PEC.owned in HH; rewrite <- !app_assoc in HH; exact HH)). }
        apply in_or_app. left. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). left. rewrite E1, E2. reflexivity.
      * apply not_eq_sym. apply (PMBSK.fst_neq_appA (PM.parser_own s ++ PEC.enc_own en ++ PESK.sink_own k) LBX q m q' m'); [| | exact Y].
        { exact (PMBSK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH). }
        apply in_or_app; right. apply in_or_app; left. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). left. rewrite E1, E2. reflexivity.
Qed.

Lemma ws_wapp : PMKB.wapp Wk.
Proof.
  entry_facts. unfold Wk. apply PMKB.wapp_cons.
  - cbn [fst snd pe_off_sink PeCLayoutB.EADDR_B]. unfold PESK.o_sink. cbn [pe_off_sink PeCLayoutB.EADDR_B]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - F1 F2 FSAPP. lia.
  - intros rr Hr. destruct rr as [q m]. destruct (eblk_facts q m Hr) as (_ & _ & _ & _ & B0 & B47 & BAPP & _). cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - B0 B47 BAPP. lia.
Qed.

Lemma wk_out a : ~ (PESK.o_sink EE fb <= a < PESK.o_sink EE fb + 24) -> (forall q m, In (q, m) (PEC.enc_own en) -> ~ (q <= a < q + m)) -> L5.outside Wk a.
Proof. intros N1 N2 rr [<-|Hr]; [unfold L5.in_rng; cbn [fst snd]; exact N1|]. destruct rr as [q m]. unfold L5.in_rng. cbn [fst snd]. exact (N2 q m Hr). Qed.
Lemma wk_out_obj o n : PMSPA.aobjA FF o n -> (o + n <= PESK.o_sink EE fb \/ PESK.o_sink EE fb + 24 <= o) -> forall i, o <= i < o + n -> L5.outside Wk i.
Proof.
  intros AO Ho i Hi. apply wk_out; [clear - Ho Hi; lia|]. intros q m Hq. destruct (eblk_facts q m Hq) as (_ & _ & _ & _ & _ & _ & _ & _ & AP & _).
  destruct (AP o n AO); clear - H Hi; lia.
Qed.
Lemma wk_out_blk q m : In (q, m) LBc0 -> PMKB.blk_out Wk q m.
Proof.
  intros Hq i Hi. entry_facts. name_objs. apply wk_out.
  - assert (INq : In (q, m) LB) by (unfold LB, PEC.owned; unfold LBc0 in Hq; apply in_app_or in Hq; destruct Hq as [Y|Y]; apply in_or_app; [left; apply in_or_app; left; exact Y| right; exact Y]).
    destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m osk 24 HH INq (AOF osk 24 ltac:(lia) ltac:(lia))) as [Y|Y]; clear - Y Hi; lia.
  - intros q' m' Hq'. destruct (eblk_facts q' m' Hq') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AP). destruct (AP q m Hq); clear - H Hi; lia.
Qed.

Lemma keepf Mi : L5SAR.ek L ar LBc0 FF sp 20480 Wk M Mi ->
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
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model osk 24 sp 20480 HH (PMKB.aobj_of_aobjA FF osk 24 (AOF osk 24 ltac:(lia) ltac:(lia)) ltac:(rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8)) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & _).
  pose proof wk_out_blk as OUTB.
  assert (OUTO : forall a m, PMSPA.aobjA FF a m -> (a + m <= osk \/ osk + 24 <= a) -> forall i, a <= i < a + m -> L5.outside Wk i) by exact wk_out_obj.
  assert (Iq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LBc0) by (apply PINC; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (SDEP : forall a, PMST.dep AD a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside Wk a).
  { intros a D. change (PMST.dep PMB.AD a) in D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
    split; [clear - DI; lia|]. split; [exact (PMB.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply wk_out; [clear - DI K1; lia|].
    intros q m Hq. destruct (eblk_facts q m Hq) as (INq & _). destruct (WB _ INq) as ((_ & BIMG & _) & _). cbn [fst snd] in BIMG.
    rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BIMG. clear - DI BIMG. lia. }
  split.
  { apply (PMKB.parser_keepA RSEGS AD L ar LBc0 FF sp 20480 Wk M Mi EK WAPP FRB BRc0 op ois s (AOF op 384 ltac:(lia) ltac:(lia)) PINC); [| | | | exact PA].
    - apply (OUTO op 384 (AOF op 384 ltac:(lia) ltac:(lia))). clear - Eop Eosk; lia.
    - apply OUTB. exact Iq.
    - apply OUTB. apply PINC. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
    - intros c n q E1. apply OUTB. apply PINC. unfold PM.parser_own, PM.vs_own. rewrite E1. right; right; left. reflexivity. }
  split.
  { apply (PMKB.iss_keepA RSEGS AD L ar LBc0 FF sp 20480 Wk M Mi EK WAPP FRB BRc0 ois str sm (AOF ois 272 ltac:(lia) ltac:(lia)) SINC); [| | exact IA].
    - apply (OUTO ois 272 (AOF ois 272 ltac:(lia) ltac:(lia))). clear - Eois Eosk; lia.
    - intros c n0 q E1. refine (OUTB q c _). apply SINC. unfold PM.vs_own. rewrite E1. left. reflexivity. }
  split.
  { apply (PMKB.u64_keepA RSEGS L ar LBc0 FF sp 20480 Wk M Mi EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF].
    apply (OUTO (op + 384) 8 (AOF (op + 384) 8 ltac:(lia) ltac:(lia))). clear - Eop Eosk; lia. }
  split.
  { change (PMSTA.base_okA RSEGS PMB.AD Mi). apply (PMBSK.base_keep L ar C LY LBc0 FF sp 20480 Wk M Mi EK); [| exact BASE]. intros a Ha. apply wk_out; [clear - Ha K1; lia|].
    intros q m Hq. destruct (eblk_facts q m Hq) as (INq & _). destruct (WB _ INq) as ((_ & BIMG & _) & _). cbn [fst snd] in BIMG.
    rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BIMG. clear - Ha BIMG. lia. }
  split.
  { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBc0 FF sp 20480 Wk M Mi EK e PECSB.addrs_wf_B); [exact SDEP| exact ERR]. }
  split.
  { apply (content_keepA' LBc0 FF sp 20480 Wk M Mi fb p s str sm op EK WAPP FRB BRc0 (AOF ois 272 ltac:(lia) ltac:(lia))); [| exact SINC| exact Iq| exact OUTB| exact IA| exact PA| exact CONT].
    fold ois. intros i Hi. apply (OUTO ois 272 (AOF ois 272 ltac:(lia) ltac:(lia))); [clear - Eois Eosk; lia| clear - Hi; lia]. }
  split.
  { apply (PECFA.ec_state_keepA RSEGS AD L ar LBc0 FF sp 20480 Wk M Mi EK WAPP FRB fb xec cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
    fold oec. apply (OUTO oec 16 (AOF oec 16 ltac:(lia) ltac:(lia))). clear - Eoec Eosk; lia. }
  exact (PMKB.acc_keepA' L ar LBc0 FF sp 20480 Wk M Mi EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACCR).
Qed.

Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Let G_ := PMBUK.gctx L ar HI LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k).
Hypothesis G : G_.
Let FF' : list fframe := (F, 1, spc + 32) :: FF.
Let BINV (ki : PESK.sink) := PMBUK.binv L ar HI M model LBc0 FF LK Aw sp 20480 spc (owns SAVED sp R) F 1 Wk (EBX ki).

Hypothesis APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (EBX k ++ LBc0) FF sp0 scr0 (a + i)) -> 0 < n ->
    (a + n <= F \/ F + 128 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + 16 <= a) /\ (a + n <= fl \/ fl + 1 <= a).

Definition inv (Mi : word -> option byte) (mdi : Model) (LKi : list fframe) (Awi : list (Z * Z)) (cri : credit) (ki : PESK.sink) (a : Z) : Prop :=
  BINV ki Mi mdi LKi cri Awi /\ shadow_zero Mi (sp - 20480) 2560
  /\ PECA.enc_atA RSEGS EE L ar Mi (PMSPA.o_v AD fb) fb en /\ PESKA.sink_atA RSEGS L ar P Mi (PESK.o_sink EE fb) ki
  /\ xlo + a <= PESK.sk_z ki <= xhi + a
  /\ PMSP.credit_keep cr cri (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en ki).

Local Ltac cut_facts INV kq :=
  let BI := fresh "BI" in
  pose proof INV as (BI & SZq & EAq & SKAq & CLq & CKq);
  pose proof BI as (HHq & AMq & MRTq & IAWq & ILKq & ASTKq & EKq & DKq & OWNq & FSDq); change (ff_bytes 1 / 8) with 16 in FSDq;
  pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _);
  set (LBq := EBX kq ++ LBc0) in HHq.

Lemma perm_q kq : Permutation (EBX kq ++ LBc0) (PEC.owned s en kq ++ LBX).
Proof. unfold EBX, LBc0, PEC.owned. rewrite <- !app_assoc. apply PEEK.perm4. Qed.
Lemma HHp : ri_inv HI (EBX k ++ LBc0) FF LK cr Aw M (vml_of model).
Proof. exact (ri_perm _ _ FF LK cr Aw M _ (Permutation_sym (perm_q k)) HH). Qed.

Lemma g_facts :
  let ov := PMSPA.o_v AD fb in let osk := PESK.o_sink EE fb in
  4096 <= F /\ F + 128 <= 2 ^ 47 /\ 6930432 <= F /\ F mod 32 = 0 /\ F / 8 * 8 = F /\ (2147446784 + 17592186048512 <= F \/ F + 128 <= 2147446784)
  /\ 4096 <= fl /\ fl + 1 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) /\ (F + 128 <= fl \/ fl + 1 <= F)
  /\ F + 128 <= ahl_ceil ar /\ fl + 1 <= ahl_ceil ar /\ incl LK2 LK
  /\ (ov + 56 <= F \/ F + 128 <= ov) /\ (ov + 56 <= F / 8 + SB \/ F / 8 + SB + 16 <= ov) /\ (ov + 56 <= fl \/ fl + 1 <= ov)
  /\ (osk + 24 <= F \/ F + 128 <= osk) /\ (osk + 24 <= F / 8 + SB \/ F / 8 + SB + 16 <= osk) /\ (osk + 24 <= fl \/ fl + 1 <= osk)
  /\ ar_fs ar <= F /\ F + 128 <= ar_fs ar + FS_BYTES /\ 8 * NSV <= FR /\ (NSV = 9 \/ NSV = 11) /\ (ar_fs ar <= fl < ar_fs ar + FS_BYTES).
Proof.
  entry_facts. name_objs. pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *.
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 sp 20480 HHp (PMKB.aobj_of_aobjA FF ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m) ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & _ & _ & QCL & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model osk 24 sp 20480 HHp (PMKB.aobj_of_aobjA FF osk 24 (AOF osk 24 ltac:(lia) ltac:(lia)) K8) ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & _ & _ & KCL & _).
  destruct (APART ov 56 sp 20480 QCL ltac:(clear; lia)) as (AvF & AvS & AvL).
  destruct (APART osk 24 sp 20480 KCL ltac:(clear; lia)) as (AkF & AkS & AkL).
  pose proof NSVv as NV.
  repeat split; first [assumption | clear - GFR; lia | clear - GF8; lia | clear - GFLR; lia | clear - HFR NV; lia | clear - GFLP; lia].
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

Lemma inv_agree (Ma Mb : word -> option byte) (Wp : Z -> Prop) mda mdb LKc crc Awc kc a :
  inv Ma mda LKc Awc crc kc a ->
  ri_inv HI (EBX kc ++ LBc0) FF' LKc crc Awc Mb (vml_of mdb) -> L5CA.amodel_ok Awc mdb -> model_rt mda mdb -> mem_grows Ma Mb ->
  (forall a0, Wp a0 -> (spc <= a0 < sp /\ ~ ocell sp NSV a0) \/ (F <= a0 < F + 128) \/ (F / 8 + SB <= a0 < F / 8 + SB + 16)) ->
  (forall a0, 0 <= a0 < 2 ^ 64 -> ~ Wp a0 -> Mb (Z_to_bv 64 a0) = Ma (Z_to_bv 64 a0)) ->
  inv Mb mdb LKc Awc crc kc a.
Proof.
  intros INV HHb AMb RTb MG WP AG. entry_facts. name_objs. cut_facts INV kc.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & _ & _ & GFLP).
  assert (WP' : forall a0, Wp a0 -> (spc <= a0 < sp) \/ (F <= a0 < F + 128) \/ (F / 8 + SB <= a0 < F / 8 + SB + 16)) by (intros a0 X'; destruct (WP a0 X') as [[Y _]|[Y|Y]]; [left| right; left| right; right]; exact Y).
  destruct (frame_agree Ma Mb Wp WP' AG) as [AGa AGs].
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKc crc Awc Ma mda ov 56 sp 20480 HHq (PMKB.aobj_of_aobjA FF' ov 56 (PMBUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia))) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2 & Q3 & _) & QBIG & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKc crc Awc Ma mda osk 24 sp 20480 HHq (PMKB.aobj_of_aobjA FF' osk 24 (PMBUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & KBIG & _).
  unfold inv. split.
  { apply (PMBUK.binv_piece L ar HI M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
             Wk (EBX kc) Ma mda LKc crc Awc Mb mdb Wp BI HHb AMb RTb MG AG).
    intros a0 X'. destruct (WP a0 X') as [Y|[Y|Y]]; [left; exact Y| right; left; change (ff_bytes 1) with 128; exact Y| right; right; change (ff_bytes 1 / 8) with 16; exact Y]. }
  split.
  { intros jj Hjj. pose proof (SZq jj Hjj) as Z0. unfold byte_at in Z0 |- *.
    replace (HeapIfaceA.S (sp - 20480) + jj) with (HeapIfaceA.S (sp - 20480 + jj * 8)) in Z0 |- * by (unfold HeapIfaceA.S; rewrite Z.div_add by (clear; lia); clear; lia).
    rewrite (AGs (sp - 20480 + jj * 8)); [exact Z0| clear - Hjj SLO SPT; lia| clear - Hjj SHI SPT; lia| clear - Hjj GFC SLO; lia]. }
  split.
  { apply (PECFA.enc_atA_agree RSEGS EE L ar Ma Mb ov fb en); [clear - Q1; lia| clear - Q3; lia| | | exact EAq].
    - split; [intros i Hi; apply AGa; clear - Hi Q1 Q2 Q3 QBIG AvF; lia| intros x Hx; apply AGs; clear - Hx Q1 Q3 AvF; lia].
    - intros Hp. assert (IN : In (PEC.en_b en, PEC.ESZ * PEC.ecap (PEC.en_k en)) (EBX kc ++ LBc0)).
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

Lemma inv_cpre Mi mdi LKi Awi cri ki a lo hi : inv Mi mdi LKi Awi cri ki a -> lo = xlo + a -> hi = xhi + a ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth lo hi xbad) s str sm en ki e cat.
Proof.
  intros INV Hlo Hhi. cut_facts INV ki.
  destruct (keepf Mi EKq) as (PA' & IA' & VREF' & BASE' & ERR' & CONT' & ECS' & ACCR').
  destruct CPRE as (_ & _ & _ & _ & _ & _ & _ & TBOK & _ & CL & _ & ECI & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad). cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad] in *.
  unfold PECA.crun_preA.
  split; [exact PA'|]. split; [exact IA'|]. split; [exact EAq|]. split; [exact VREF'|]. split; [exact SKAq|].
  split; [exact BASE'|]. split; [exact ERR'|]. split; [exact TBOK|]. split; [exact CONT'|].
  split.
  { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad].
    split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
    split; [exact Lestk|]. split; [exact Ledepth|]. split; [clear - CLq Hlo Hhi; lia| exact Lbad]. }
  cbn [s_ec]. split; [exact ECS'|]. split; [exact ECI| exact ACCR'].
Qed.

Definition sfacts (MV : word -> option byte) : Prop :=
  L5.img_clear MV 1273856 1306624 /\ L5.u64_at RSEGS MV 1335544 SBL /\ L5.u32_at RSEGS MV 1335552 1 /\
  140735332487168 + 20480 <= sp <= 140737488355328 /\ sp mod 32 = 0 /\ L5.writable RSEGS MV (sp - FR) FR.
Definition ffacts (MV : word -> option byte) (zsh : bool) : Prop :=
  4096 <= F <= 140737488355200 /\ F mod 32 = 0 /\ L5.defined MV F 128 /\ L5.writable RSEGS MV F 128 /\
  (2147446784 + 17592186048512 <= F \/ F + 128 <= 2147446784) /\ L5.writable RSEGS MV (F / 8 + SBL) 16 /\
  (if zsh then L5KA.zeros_at MV (F / 8 + SBL) 16 else True) /\
  L5.u64_at RSEGS MV (F + 120) fl /\ 4096 <= fl <= 140737488355327 /\ L5.writable RSEGS MV fl 1 /\
  (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) /\ (F + 128 <= fl \/ fl + 1 <= F) /\
  ((sp - FR) + FR <= F \/ F + 128 <= sp - FR) /\ ((sp - FR) + FR <= fl \/ fl + 1 <= sp - FR).
Definition ofacts (MV : word -> option byte) : Prop :=
  let ov := PMSPA.o_v AD fb in let osk := PESK.o_sink EE fb in
  4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at MV (ov / 8 + SBL) 7
  /\ L5.writable RSEGS MV ov 56 /\ ((sp - FR) + FR <= ov \/ ov + 56 <= (sp - FR))
  /\ L5KA.zeros_at MV ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at MV ((ov + 24) / 8 + SBL) 1 /\ L5KA.zeros_at MV ((ov + 32) / 8 + SBL) 1
  /\ L5.u64_at RSEGS MV (ov + 8) osk /\ 4096 <= osk <= 140737488355304 /\ osk mod 8 = 0 /\ osk + 24 <= ov
  /\ L5.u64_at RSEGS MV (ov + 24) (PEC.en_b en) /\ L5.u64_at RSEGS MV (ov + 32) (PEC.en_b en + 24 * Z.of_nat (length (PEC.en_stk en))) /\ 0 <= PEC.en_b en <= 2 ^ 47
  /\ (ov + 56 <= F \/ F + 128 <= ov) /\ (ov + 56 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= ov) /\ (ov + 56 <= fl \/ fl + 1 <= ov)
  /\ (osk + 24 <= F \/ F + 128 <= osk) /\ (osk + 24 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= osk) /\ (osk + 24 <= fl \/ fl + 1 <= osk).

Lemma vis_facts Mq mdq LKq Awq crq kq a : inv Mq mdq LKq Awq crq kq a ->
  let H := ahid Awq mdq in let MV := mrestrict H Mq in
  sfacts MV /\ ffacts MV false /\ owns SAVED sp R MV /\ ofacts MV
  /\ (forall a0 n, spc <= a0 -> a0 + n <= sp -> L5A.avis H a0 n) /\ L5A.avis H F 128 /\ L5A.avis H (F / 8 + SB) 16 /\ L5A.avis H fl 1
  /\ L5A.avis H (PMSPA.o_v AD fb) 56 /\ L5A.avis H (PESK.o_sink EE fb) 24.
Proof.
  intros INV H MV. entry_facts. name_objs. cut_facts INV kq.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & GNF & GNV & GFLP).
  destruct (PMBUK.vis_facts L ar C HI LYa HIok M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
              Wk (EBX kq) Mq mdq LKq crq Awq BI)
    as ((W0 & W1 & W2 & W3 & W4) & OWNv & (FD & FW & FSW & FLC & FLW) & (_ & VFL & VF & VS & VSH)).
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. fold H in W0, W1, W2, W3, W4, OWNv, FD, FW, FSW, FLC, FLW, VFL, VF, VS, VSH. fold MV in W0, W1, W2, W3, W4, OWNv, FD, FW, FSW, FLC, FLW.
  replace (sp - spc) with FR in W0, VS by (unfold spc; clear; lia).
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq HHq) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _). fold H in VIS, VIMG, VFS, VBLK, VBSH.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKB.aobj_of_aobjA FF' ov 56 (PMBUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia))) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2' & Q3 & Q4 & Q5) & QBIG & QDEF & QVIS & QSHV & QCL & QSHCL). fold H in QVIS, QSHV.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKB.aobj_of_aobjA FF' osk 24 (PMBUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & _ & _ & KVIS & _). fold H in KVIS.
  assert (CVv : forall a0 m0, ov <= a0 -> a0 + m0 <= ov + 56 -> L5A.avis H a0 m0) by (intros a0 m0 X1 X2; eapply L5A.avis_sub; [exact QVIS| lia| lia]).
  pose proof EAq as (EV0 & EV8 & EV16 & EV24 & EV32 & EV40 & EV48 & EDEF & EACC & EK & ELEN & EDEP & EKB & EBLK & _). fold osk in EV8. unfold PEC.ESZ in EV32.
  pose proof (PEC.ecap_nonneg (PEC.en_k en)) as CN.
  pose proof (PMKB.obj_shadow_vis L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq ov 56 HHq (PMBUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia))) Q8m ltac:(lia) ltac:(reflexivity) EACC) as Zov.
  unfold SB in Zov. change (56 / 8) with 7 in Zov. fold H MV in Zov.
  assert (D8 : forall j, (ov + 8 * j) / 8 = ov / 8 + j).
  { intros j. rewrite <- Q5 at 1. replace (ov / 8 * 8 + 8 * j) with ((ov / 8 + j) * 8) by lia. apply Z.div_mul. clear; lia. }
  assert (ZG : forall j, 0 <= j < 7 -> L5KA.zeros_at MV ((ov + 8 * j) / 8 + SBL) 1).
  { intros j Hj. rewrite D8. intros i Hi. replace (ov / 8 + j + SBL + i) with (ov / 8 + SBL + (j + i)) by lia. apply Zov. lia. }
  pose proof (ZG 1 ltac:(lia)) as Z8. pose proof (ZG 3 ltac:(lia)) as Z24. pose proof (ZG 4 ltac:(lia)) as Z32.
  replace (ov + 8 * 1) with (ov + 8) in Z8 by lia. replace (ov + 8 * 3) with (ov + 24) in Z24 by lia. replace (ov + 8 * 4) with (ov + 32) in Z32 by lia.
  assert (EB : 0 <= PEC.en_b en <= 2 ^ 47).
  { destruct (Z.eq_dec (PEC.en_k en) 0) as [Z0|NZ]; [rewrite (EKB Z0); clear; lia|]. destruct (EBLK ltac:(lia)) as (_ & _ & BR0 & _). destruct BR0 as (X1 & _ & _ & _ & X5 & _). unfold PEC.ESZ in X5. clear - X1 X5 SPT CN; lia. }
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
    split; [exact EB|]. unfold SB in AvS, AkS. repeat split; assumption. }
  split. { intros a0 n H1 H2. replace a0 with (spc + (a0 - spc)) by (clear; lia). eapply L5A.avis_sub; [exact VS| clear - H1; lia| clear - H1 H2; lia]. }
  split. exact VF. split. exact VSH. split. exact VFL. split. exact QVIS. exact KVIS.
Qed.

Lemma vis_facts_top Mq mdq LKq Awq crq kq a e1 rr : inv Mq mdq LKq Awq crq kq a -> xestk = e1 :: rr ->
  let H := ahid Awq mdq in let MV := mrestrict H Mq in let ov := PMSPA.o_v AD fb in let eb := PEC.en_b en in
  let ed := eb + 24 * (Z.of_nat (length rr) + 1) in
  Z.of_nat (length (PEC.en_stk en)) = Z.of_nat (length rr) + 1 /\ 0 < PEC.en_k en
  /\ 4096 <= eb /\ ed <= 140737488355328 /\ ed mod 8 = 0 /\ 24 <= ed - eb <= 100000 /\ L5.writable RSEGS MV (ed - 24) 24
  /\ (2147446784 + 17592186048512 <= ed - 24 \/ (ed - 24) + 24 <= 2147446784) /\ L5KA.zeros_at MV ((ed - 8) / 8 + SBL) 1
  /\ ((ed - 24) + 24 <= (sp - FR) \/ (sp - FR) + FR <= (ed - 24)) /\ ((ed - 24) + 24 <= ov \/ ov + 56 <= (ed - 24))
  /\ L5.u64_at RSEGS MV (ed - 8) (ei_cnt e1) /\ 0 <= ei_cnt e1 < 2 ^ 64 /\ ei_ok e1
  /\ In (eb, 24 * PEC.ecap (PEC.en_k en)) (PEC.enc_own en) /\ ed <= eb + 24 * PEC.ecap (PEC.en_k en) /\ eb + 24 * PEC.ecap (PEC.en_k en) <= 2 ^ 47
  /\ ((ed - 24) + 24 <= F \/ F + 128 <= (ed - 24)) /\ ((ed - 24) + 24 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= (ed - 24)) /\ ((ed - 24) + 24 <= fl \/ fl + 1 <= (ed - 24))
  /\ L5A.avis H (ed - 24) 24.
Proof.
  intros INV HXS. entry_facts. name_objs. cut_facts INV kq.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & GNF & GNV & GFLP).
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (_ & _ & _ & _ & _ & Lestk & _). cbn [s_estk X] in Lestk.
  destruct MP as (_ & _ & FA & _). cbn [s_estk X] in FA. rewrite HXS in FA, Lestk.
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq HHq) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _).
  set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *.
  pose proof EAq as (EV0 & EV8 & EV16 & EV24 & EV32 & EV40 & EV48 & EDEF & EACC & EK & ELEN & EDEP & EKB & EBLK & EITEMS).
  set (eb := PEC.en_b en) in *. set (ek := PEC.en_k en) in *.
  pose proof (PEC.ecap_nonneg ek) as CN. unfold PEC.ESZ in EV32, EV40, ELEN, EBLK, EITEMS.
  assert (HLEN : length (PEC.en_stk en) = Datatypes.S (length rr)) by (rewrite Lestk, length_rev; reflexivity).
  rewrite HLEN in ELEN, EITEMS, EBLK. rewrite Nat2Z.inj_succ in ELEN, EBLK.
  set (m := Z.of_nat (length rr)) in *. assert (M0 : 0 <= m) by (unfold m; clear; lia).
  assert (EKP : 0 < ek) by (destruct (Z.eq_dec ek 0) as [Z0|NZ]; [exfalso; unfold PEC.ecap in ELEN; rewrite Z0 in ELEN; cbn in ELEN; clear - ELEN M0; lia| clear - EK NZ; lia]).
  destruct (EBLK EKP) as (EBAL & EBDEF & EBR & EBACC & EBANN). destruct EBR as (EB1 & EB2 & EB3 & EB4 & EB5 & EB6).
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in EB2. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in EB6.
  assert (ECAPB : PEC.ecap ek <= 2048).
  { clear - EK EKP. unfold PEC.ecap. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; lia. }
  assert (BINe : In (eb, 24 * PEC.ecap ek) (PEC.enc_own en)).
  { unfold PEC.enc_own. fold ek eb. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  assert (BINq : In (eb, 24 * PEC.ecap ek) LBq) by (unfold LBq, EBX; apply in_or_app; left; apply in_or_app; left; exact BINe).
  pose proof (EITEMS (length rr) ltac:(clear; lia)) as TOP. rewrite Lestk in TOP. cbn [rev] in TOP. rewrite PEEK.nth_top in TOP. fold m in TOP.
  destruct TOP as (TK & TL & TC).
  assert (E1OK : ei_ok e1) by (inversion FA; assumption). pose proof E1OK as (_ & E1C & _). unfold TWO64 in E1C.
  set (ed := eb + 24 * (m + 1)).
  assert (ALend : ed mod 8 = 0) by (unfold ed; apply PEEK.al8_item; exact EBAL).
  replace (eb + 24 * m + 16) with (ed - 8) in TC by (unfold ed; clear; lia).
  assert (OVA : eb + 24 * PEC.ecap ek <= ov \/ ov + 56 <= eb) by exact (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ eb (24 * PEC.ecap ek) ov 56 HHq BINq (PMBUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia)))).
  assert (BV : forall a0 n0, eb <= a0 -> a0 + n0 <= eb + 24 * PEC.ecap ek -> L5A.avis H a0 n0) by (intros a0 n0 X1 X2; exact (VBLK eb (24 * PEC.ecap ek) a0 n0 BINq X1 X2)).
  assert (AL8 : (ed - 8) mod 8 = 0) by (replace (ed - 8) with (ed + (-1) * 8) by lia; rewrite Z_mod_plus_full; exact ALend).
  assert (ACC8 : PMSPA.accA Mq (ed - 8) 8) by (intros x Hx; apply EBACC; unfold ed in Hx; clear - Hx M0; lia).
  pose proof (PMKB.blk_shadow_vis L ar C HI LYa HIok LBq FF' LKq crq Awq Mq mdq eb (24 * PEC.ecap ek) (ed - 8) 8 HHq BINq ltac:(unfold ed; lia) ltac:(unfold ed; lia) AL8
                ltac:(clear; lia) ltac:(reflexivity) ACC8) as ZC.
  unfold SB in ZC. change (8 / 8) with 1 in ZC. fold H MV in ZC.

  destruct (blk_facts Mq LKq crq Awq _ kq _ _ HHq BINq) as (B0 & B47 & BAPP & BCEIL & BFS). unfold FS_BYTES in BFS, GFS2.
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
  apply (BV (ed - 24) 24); unfold ed; clear - M0 ELEN; lia.
Qed.

Let LBe : list (Z * Z) := PEC.enc_own en ++ LBc0.
Let Wc : list L5.range := [(PESK.o_sink EE fb, 24)].
Lemma perm_e kq : Permutation (PESK.sink_own kq ++ LBe) (EBX kq ++ LBc0).
Proof. unfold LBe, EBX. rewrite <- !app_assoc. apply (Permutation_app_swap_app (PESK.sink_own kq) (PEC.enc_own en)). Qed.
Lemma wc_wapp : PMKB.wapp Wc.
Proof. intros rr [<-|[]]. exact (ws_wapp _ (or_introl eq_refl)). Qed.

Lemma after_callee Mq mdq LKq Awq crq kq a Mx mdx LKx Awx crx kx d SCRc :
  inv Mq mdq LKq Awq crq kq a ->
  L5CA.ahpres L ar LBe FF' spc SCRc Wc Mq Mx -> 0 <= SCRc -> SCRc + FR <= 20480 ->
  ri_inv HI (PESK.sink_own kx ++ LBe) FF' LKx crx Awx Mx (vml_of mdx) -> L5CA.amodel_ok Awx mdx -> model_rt mdq mdx -> incl Awq Awx -> incl LKx LKq ->
  PESKA.sink_atA RSEGS L ar P Mx (PESK.o_sink EE fb) kx -> xlo + (a + d) <= PESK.sk_z kx <= xhi + (a + d) ->
  PMSP.credit_keep crq crx (PECA.pot_encA L ar P en kq) (PECA.pot_encA L ar P en kx) ->
  inv Mx mdx LKx Awx crx kx (a + d) /\ (forall a0, spc <= a0 < sp -> Mx (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
Proof.
  intros INV HP HS0 HS1 HHx AMx RTx IAx ILx SKAx CLx CKx. entry_facts. name_objs. cut_facts INV kq.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & GNF & GNV & GFLP).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKB.aobj_of_aobjA FF' osk 24 (PMBUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))) ltac:(rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8)) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & _).
  pose proof (ri_perm _ _ FF' LKx crx Awx Mx _ (perm_e kx) HHx) as HHx'.
  assert (OWs : forall a0, sp - 20480 <= a0 < sp -> L5.outside Wc a0) by (intros a0 Ha0 r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; fold osk; clear - Ha0 K2 SLO; lia).
  assert (BIx : BINV kx Mx mdx LKx crx Awx).
  { apply (PMBUK.binv_callee L ar C HI HIok M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
             Wk Wk (EBX kq) (PEC.enc_own en) (EBX kx) Mq mdq LKq crq Awq Mx mdx LKx crx Awx SCRc Wc BI HP HHx' AMx RTx IAx ILx HS0).
    - unfold spc. clear - HS1; lia.
    - intros r0 a0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. fold osk in Hr. change (ff_bytes 1 / 8) with 16. unfold ocell. split; [clear - Hr K2 SLO GNF GNV; lia| unfold SB in AkS |- *; clear - Hr AkS; lia].
    - intros a0 _ Oa r0 [<-|[]]. exact (Oa _ (or_introl eq_refl)).
    - intros a0 Oa. exact Oa. }
  assert (EK12 : L5SAR.ek L ar LBe FF' sp 20480 Wc Mq Mx).
  { apply (L5SAR.ek_callee L ar LBe [] FF' [] sp 20480 spc SCRc Wc Wc Mq Mx HP); [unfold spc; clear - HS1; lia| unfold spc; clear - HFR; lia| intros a0 _ O; exact O]. }
  assert (FRBq : forall f, In f FF' -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
  assert (BRBe : forall x, In x LBe -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
  { intros x Hx. apply (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHx). apply in_or_app. right. exact Hx. }
  split.
  - unfold inv. split; [exact BIx|]. split.
    { apply (PMKB.stksh_keepA L ar LBe FF' sp 20480 Wc Mq Mx EK12 wc_wapp (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZq]. }
    split.
    { apply (PECFA.enc_keepA RSEGS EE L ar LBe FF' sp 20480 Wc Mq Mx EK12 wc_wapp FRBq BRBe ov fb en (PMBUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia)))); [| unfold LBe; apply incl_appl; apply incl_refl| | exact EAq].
      - intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk. clear - Hi Eov Eosk; lia.
      - intros Hp i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk.
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
  pose proof (PMB.ly_cost L C LY) as (KPM & BLIN & BOV).
  unfold PMSPA.scA, PEC.pot_estack, PEC.ESZ, PMSPA.HV, LibIfaceAB.heap_view. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead]. rewrite KPM, BOV, BLIN.
  assert (P2 : 2 ^ PEC.en_k en <= 2 ^ 12) by (apply Z.pow_le_mono_r; clear - EK; lia). clear - EK P2. split; nia.
Qed.

Lemma pb_call (a pv h ra0 : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  inv Mq mdq LKq Awq crq kq a -> PESKA.spa_hb P h -> xhi + a <= h -> spc <= pv -> pv + 1 <= sp -> L5.ra_ok ra0 ->
  getr Rq (reg 1) = Z_to_bv 64 ra0 -> getr Rq (reg 2) = Z_to_bv 64 spc ->
  getr Rq (reg 10) = Z_to_bv 64 (PESK.o_sink EE fb) -> getr Rq (reg 11) = Z_to_bv 64 pv -> csk Rq ->
  (forall (fx2 : FPState) R2 Mx mdx LKx Awx crx kx, inv Mx mdx LKx Awx crx kx (a + 1) -> regs_preserved Rq R2 ->
      (forall a0, spc <= a0 < sp -> Mx (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R2 ra0 Mx mdx) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq PBPC Mq mdq) K.
Proof.
  intros INV HBh Ha PV1 PV2 RA0 Q1 Q2 Q10 Q11 QCS KX. entry_facts. name_objs. cut_facts INV kq. pose proof RA0 as (Hra1 & Hra2).
  pose proof (ri_perm _ _ FF' LKq crq Awq Mq _ (Permutation_sym (perm_e kq)) HHq) as HHY.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKB.aobj_of_aobjA FF' osk 24 (PMBUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & _).
  pose proof SKAq as (_ & _ & _ & _ & _ & KZCq & KCAPq & KC0q & KBLKq).
  pose proof pen_nonneg as PEN.
  pose proof PB as PBX. unfold PESKA.push_back_specA in PBX. cbn [pe_push_back EE PeCLayoutB.EADDR_B] in PBX.
  apply (PBX PMODE fxq Rq Mq mdq K LBe FF' LKq Awq crq osk pv spc ra0 kq HHY AMq K0); clear PBX.
  {
    split; [rewrite L5K.rl1; exact Q1|]. split; [exact RA0|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536. split.
    - unfold spc. apply (L5SAR.astk_sub ar Mq Mq sp 20480 FR 12288 ASTKq (mem_grows_refl Mq)); [clear - HFR; lia| clear; lia| clear - HFR; lia| exact SPC16].
    - unfold spc. apply (PMKB.shadow_zero_sub Mq (sp - 20480) 2560); [apply SPd8; reflexivity| | clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZq].
      replace (sp - FR - 12288) with (sp - (FR + 12288)) by lia. apply SPd8. clear - HFR; destruct HFR as [-> | ->]; reflexivity. }
  { apply (PMBUAR.ffroomA_push 4 0 FF LK LKq _ FRM ILKq); [exact NDFq| clear; lia]. }
  { apply (PMBUAR.ffrsA_push FF sp spc F 1 (spc + 32) FRS); [clear; lia| unfold spc; clear - HFR; lia]. }
  { rewrite L5K.rl10. exact Q10. }
  { rewrite L5K.rl11. exact Q11. }
  { exact SKAq. }
  { exact (PMBUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))). }
  { exact K8. }
  {
    split; [apply (L5.defined_sub Mq (sp - 20480) 20480 pv 1 SDEFq); unfold spc in PV1; clear - PV1 PV2 HFR; lia|].
    split; [apply (PESHZ.bat0_of_shadow_zero Mq (sp - 20480) 2560 pv SZq); [apply SPd8; reflexivity| unfold spc in PV1; clear - PV1 HFR; lia| clear - PV2; lia]|].
    split; [right; unfold spc in PV1; clear - K2 SLO PV1 HFR; lia|]. left. split; [exact PV1| clear - PV2 SHI; lia]. }
  { intros ZC. apply (PESKA.spao_next L P PO (PESK.sk_c kq) h KCAPq); [intros Hc; exact (proj1 (proj2 (proj2 (proj2 (proj2 (KBLKq Hc))))))| exact HBh| clear - ZC CLq Ha; lia]. }
  { unfold PMSP.credit_le, PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CRED, CKq |- *. cbn [fst snd] in CRED, CKq |- *. clear - CRED CKq PEN. lia. }
  intros fx2 R2 Mx mdx LKx Awx crx b2 RP2 SKA2 HP2 CK2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2.
  destruct (after_callee Mq mdq LKq Awq crq kq a Mx mdx LKx Awx crx (PESK.sk_push kq b2) 1 12288 INV HP2 ltac:(clear; lia) ltac:(clear - HFR; lia) HH2 AM2 MRT2 IAW2 ILK2 SKA2) as [INVx AGx].
  - unfold PESK.sk_push. destruct (PESK.sk_z kq <? PESK.sk_c kq); cbn [PESK.sk_z]; clear - CLq; lia.
  - unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CK2 |- *. cbn [fst snd] in CK2 |- *. clear - CK2. lia.
  - exact (KX fx2 R2 Mx mdx LKx Awx crx _ INVx RP2 AGx).
Qed.

Lemma pbi_call (a q pv h ra0 : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  inv Mq mdq LKq Awq crq kq a -> PESKA.spa_hb P h -> xhi + a <= h -> spc <= pv -> pv + 1 <= sp -> L5.ra_ok ra0 ->
  F + 32 <= q -> q + 8 <= F + 120 -> q mod 8 = 0 -> L5.u64_at RSEGS Mq q (PMSPA.o_v AD fb + 8) -> L5.u8_at RSEGS Mq (q / 8 + SBL) 0 ->
  getr Rq (reg 1) = Z_to_bv 64 ra0 -> getr Rq (reg 2) = Z_to_bv 64 spc ->
  getr Rq (reg 10) = Z_to_bv 64 q -> getr Rq (reg 11) = Z_to_bv 64 pv -> csk Rq ->
  (forall (fx2 : FPState) R2 Mx mdx LKx Awx crx kx, inv Mx mdx LKx Awx crx kx (a + 1) -> regs_preserved Rq R2 ->
      (forall a0, spc <= a0 < sp -> Mx (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R2 ra0 Mx mdx) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq PBIPC Mq mdq) K.
Proof.
  intros INV HBh Ha PV1 PV2 RA0 HQ1 HQ2 HQ8 UQ USH Q1 Q2 Q10 Q11 QCS KX. entry_facts. name_objs. cut_facts INV kq. pose proof RA0 as (Hra1 & Hra2).
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & _).
  pose proof (ri_perm _ _ FF' LKq crq Awq Mq _ (Permutation_sym (perm_e kq)) HHq) as HHY.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (Q8v : (ov + 8) mod 8 = 0) by (rewrite Eov; replace (fb + 496 + 8) with (fb + 8 * 63) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKB.aobj_of_aobjA FF' osk 24 (PMBUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq (ov + 8) 8 sp 20480 HHq (PMKB.aobj_of_aobjA FF' (ov + 8) 8 (PMBUAR.aobjA_push FF (ov + 8) 8 _ (AOF (ov + 8) 8 ltac:(lia) ltac:(lia))) Q8v) ltac:(lia) ltac:(reflexivity))
    as ((R1' & _ & _ & _) & _ & RDEF & _).
  destruct (vis_facts Mq mdq LKq Awq crq kq a INV) as (_ & (_ & _ & FDv & _) & _ & _ & VS & VF & VSH & VFL & _).
  pose proof SKAq as (_ & _ & _ & _ & _ & KZCq & KCAPq & KC0q & KBLKq).
  pose proof EAq as (_ & EV8 & _ & _ & _ & _ & _ & _ & EACC & _). fold osk in EV8.
  pose proof pen_nonneg as PEN.
  pose proof PBI as PBX. unfold PEPBI.push_back_indZ_specA in PBX.
  apply (PBX PMODE fxq Rq Mq mdq K LBe FF' LKq Awq crq q (ov + 8) osk pv spc ra0 kq HHY AMq K0); clear PBX.
  - split; [rewrite L5K.rl1; exact Q1|]. split; [exact RA0|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792. split.
    + unfold spc. apply (L5SAR.astk_sub ar Mq Mq sp 20480 FR 14336 ASTKq (mem_grows_refl Mq)); [clear - HFR; lia| clear; lia| clear - HFR; lia| exact SPC16].
    + unfold spc. apply (PMKB.shadow_zero_sub Mq (sp - 20480) 2560); [apply SPd8; reflexivity| | clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZq].
      replace (sp - FR - 14336) with (sp - (FR + 14336)) by lia. apply SPd8. clear - HFR; destruct HFR as [-> | ->]; reflexivity.
  - apply (PMBUAR.ffroomA_push 4 1 FF LK LKq _ FRM ILKq); [exact NDFq| clear; lia].
  - apply (PMBUAR.ffrsA_push FF sp spc F 1 (spc + 32) FRS); [clear; lia| unfold spc; clear - HFR; lia].
  - rewrite L5K.rl10. exact Q10.
  - rewrite L5K.rl11. exact Q11.
  - exact UQ.
  - exact Q8v.
  - clear - R1'; lia.
  - exact EV8.
  - clear - K1; lia.
  - apply (proj1 (L5A.defined_vis (ahid Awq mdq) Mq q 8 (L5A.avis_sub _ F 128 q 8 VF ltac:(clear - HQ1; lia) ltac:(clear - HQ2; lia)))).
    intros i Hi. replace (q + i) with (F + (q - F + i)) by (clear; lia). apply FDv. clear - Hi HQ1 HQ2; lia.
  - intros x Hx. left. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    replace (HeapIfaceA.S x) with (q / 8 + SBL) by (unfold HeapIfaceA.S, SB; clear - Hx HQ8; Lia.lia).
    apply byte_at_of_u8; [exact USH|]. replace (q / 8 + SBL) with (F / 8 + SB + (q / 8 - F / 8)) by (unfold SB; clear; lia). apply FSDq. clear - HQ1 HQ2 HQ8 GF8; Lia.lia.
  - exists (F, 1, spc + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 1) with 128. clear - HQ1 HQ2; lia.
  - exact HQ8.
  - exact (PMBUAR.aobjA_push FF (ov + 8) 8 _ (AOF (ov + 8) 8 ltac:(lia) ltac:(lia))).
  - exact RDEF.
  - intros x Hx. apply EACC. clear - Hx; lia.
  - exact SKAq.
  - exact (PMBUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))).
  - exact K8.
  - split; [apply (L5.defined_sub Mq (sp - 20480) 20480 pv 1 SDEFq); unfold spc in PV1; clear - PV1 PV2 HFR; lia|].
    split; [right; unfold spc in PV1; clear - K2 SLO PV1 HFR; lia|].
    left. split; [exact PV1|]. split; [clear - PV2 SHI; lia|].
    assert (E8 : sp - 20480 = 8 * ((sp - 20480) / 8)) by (pose proof (Z.div_mod (sp - 20480) 8 ltac:(clear; lia)) as X'; pose proof (SPd8 20480 eq_refl) as Y; clear - X' Y; lia).
    pose proof (SZq ((pv - (sp - 20480)) / 8) ltac:(unfold spc in PV1; split; [apply Z.div_pos; clear - PV1 HFR; lia| apply Z.div_lt_upper_bound; clear - PV2; lia])) as Z0.
    replace (HeapIfaceA.S (sp - 20480) + (pv - (sp - 20480)) / 8) with (HeapIfaceA.S pv) in Z0; [exact Z0|].
    unfold HeapIfaceA.S. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - E8 PV1 HFR. Lia.lia.
  - intros ZC. apply (PESKA.spao_next L P PO (PESK.sk_c kq) h KCAPq); [intros Hc; exact (proj1 (proj2 (proj2 (proj2 (proj2 (KBLKq Hc))))))| exact HBh| clear - ZC CLq Ha; lia].
  - unfold PMSP.credit_le, PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CRED, CKq |- *. cbn [fst snd] in CRED, CKq |- *. clear - CRED CKq PEN. lia.
  - intros fx2 R2 Mx mdx LKx Awx crx b2 RP2 SKA2 HP2 CK2 MRT2 ILK2 IAW2 AM2 HH2.
    change (PMSPA.pm_scr 1) with 14336 in HP2.
    destruct (after_callee Mq mdq LKq Awq crq kq a Mx mdx LKx Awx crx (PESK.sk_push kq b2) 1 14336 INV HP2 ltac:(clear; lia) ltac:(clear - HFR; lia) HH2 AM2 MRT2 IAW2 ILK2 SKA2) as [INVx AGx].
    + unfold PESK.sk_push. destruct (PESK.sk_z kq <? PESK.sk_c kq); cbn [PESK.sk_z]; clear - CLq; lia.
    + unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CK2 |- *. cbn [fst snd] in CK2 |- *. clear - CK2. lia.
    + exact (KX fx2 R2 Mx mdx LKx Awx crx _ INVx RP2 AGx).
Qed.

Lemma wr_call (a kb pcw h ra0 : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  PENTBB.ntb_specB RSEGS AD L ar HI pcw kb P ->
  inv Mq mdq LKq Awq crq kq a -> PESKA.spa_hb P h -> xhi + a + kb <= h -> 0 <= kb -> L5.ra_ok ra0 ->
  getr Rq (reg 1) = Z_to_bv 64 ra0 -> getr Rq (reg 2) = Z_to_bv 64 spc ->
  getr Rq (reg 11) = Z_to_bv 64 (PMSPA.o_v AD fb + 8) -> csk Rq ->
  (forall (fx2 : FPState) R2 Mx mdx LKx Awx crx kx, inv Mx mdx LKx Awx crx kx (a + kb) -> regs_preserved Rq R2 ->
      (forall a0, spc <= a0 < sp -> Mx (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R2 ra0 Mx mdx) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq pcw Mq mdq) K.
Proof.
  intros NTB INV HBh Ha KB0 RA0 Q1 Q2 Q11 QCS KX. entry_facts. name_objs. cut_facts INV kq. pose proof RA0 as (Hra1 & Hra2).
  pose proof (ri_perm _ _ FF' LKq crq Awq Mq _ (Permutation_sym (perm_e kq)) HHq) as HHY.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  assert (Q8v : (ov + 8) mod 8 = 0) by (rewrite Eov; replace (fb + 496 + 8) with (fb + 8 * 63) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof SKAq as (_ & _ & _ & _ & _ & KZCq & KCAPq & KC0q & KBLKq).
  pose proof EAq as (_ & EV8 & _ & _ & _ & _ & _ & _ & EACC & _). fold osk in EV8.
  pose proof pen_nonneg as PEN.
  unfold PENTBB.ntb_specB in NTB.
  apply (NTB PMODE fxq Rq Mq mdq K LBe FF' LKq Awq crq (ov + 8) osk spc ra0 h kq HHY AMq K0); clear NTB.
  { split; [rewrite L5K.rl1; exact Q1|]. split; [exact RA0|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 2) with 16384. change (16384 / 8) with 2048. split.
    - unfold spc. apply (L5SAR.astk_sub ar Mq Mq sp 20480 FR 16384 ASTKq (mem_grows_refl Mq)); [clear - HFR; lia| clear; lia| clear - HFR; lia| exact SPC16].
    - unfold spc. apply (PMKB.shadow_zero_sub Mq (sp - 20480) 2560); [apply SPd8; reflexivity| | clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZq].
      replace (sp - FR - 16384) with (sp - (FR + 16384)) by lia. apply SPd8. clear - HFR; destruct HFR as [-> | ->]; reflexivity. }
  { apply (PMBUAR.ffroomA_push 4 2 FF LK LKq _ FRM ILKq); [exact NDFq| clear; lia]. }
  { apply (PMBUAR.ffrsA_push FF sp spc F 1 (spc + 32) FRS); [clear; lia| unfold spc; clear - HFR; lia]. }
  { exact SPC32. }
  { rewrite L5K.rl11. exact Q11. }
  { exact EV8. }
  { exact Q8v. }
  { exact (PMBUAR.aobjA_push FF (ov + 8) 8 _ (AOF (ov + 8) 8 ltac:(lia) ltac:(lia))). }
  { intros x Hx. apply EACC. clear - Hx; lia. }
  { left. clear - Eov Eosk; lia. }
  { exact SKAq. }
  { exact (PMBUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))). }
  { exact K8. }
  { exact HBh. }
  { clear - CLq Ha; lia. }
  { unfold PMSP.credit_le, PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CRED, CKq |- *. cbn [fst snd] in CRED, CKq |- *. clear - CRED CKq PEN. lia. }
  intros fx2 R2 Mx mdx LKx Awx crx kx RP2 ZK2 SKA2 HP2 CK2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 2) with 16384 in HP2.
  destruct (after_callee Mq mdq LKq Awq crq kq a Mx mdx LKx Awx crx kx kb 16384 INV HP2 ltac:(clear; lia) ltac:(clear - HFR; lia) HH2 AM2 MRT2 IAW2 ILK2 SKA2) as [INVx AGx].
  - clear - CLq ZK2 KB0; lia.
  - unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CK2 |- *. cbn [fst snd] in CK2 |- *. clear - CK2. lia.
  - exact (KX fx2 R2 Mx mdx LKx Awx crx _ INVx RP2 AGx).
Qed.

Lemma ahpres_wenc Mf : L5CA.ahpres L ar LBc0 FF sp 20480 Wk M Mf -> L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M Mf.
Proof.
  intros (E & D & DK). change (PMSPA.pm_scr 4) with 20480. split; [| split; [exact D| exact DK]].
  intros a (Ha & Hc & Ho). apply E. split; [exact Ha|]. split; [exact Hc|]. apply wk_out.
  - intros X'. apply (Ho (PESK.o_sink EE fb, 24)); [| unfold L5.in_rng; cbn [fst snd]; exact X']. unfold PEC.W_enc. cbn [app]. right; left; reflexivity.
  - intros q m Hq X'. pose proof HHp as HHe. unfold EBX in HHe. rewrite <- app_assoc in HHe.
    exact (PMBRS1.own_not_aclient L ar C HI HIok (PEC.enc_own en) (PESK.sink_own k ++ LBc0) FF LK cr Aw M _ q m a sp 20480 HHe Hq X' (L5SAR.aclient_appb L ar LBc0 (PESK.sink_own k) FF sp 20480 a Hc)).
Qed.

Lemma retire_agree (Ma Mb : word -> option byte) (Wx : Z -> Prop) :
  (forall a0, 0 <= a0 < 2 ^ 64 -> ~ PMBUK.WretX F fl 1 Wx a0 -> Mb (Z_to_bv 64 a0) = Ma (Z_to_bv 64 a0)) ->
  (forall a0, Wx a0 -> 0 <= a0 /\ (2147446784 + 17592186048512 <= a0 \/ a0 + 1 <= 2147446784)) ->
  (forall a0, 0 <= a0 -> a0 + 1 <= 2 ^ 47 -> (a0 + 1 <= F \/ F + 128 <= a0) -> (2147446784 + 17592186048512 <= a0 \/ a0 + 1 <= 2147446784) ->
      (a0 + 1 <= fl \/ fl + 1 <= a0) -> ~ Wx a0 -> Mb (Z_to_bv 64 a0) = Ma (Z_to_bv 64 a0))
  /\ (forall x, 0 <= x -> x + 1 <= 2 ^ 47 -> (x + 1 <= F \/ F + 128 <= x) -> Mb (Z_to_bv 64 (HeapIfaceA.S x)) = Ma (Z_to_bv 64 (HeapIfaceA.S x))).
Proof.
  intros AG WXa. pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & _).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  split.
  - intros a0 H0 H1 H2 H3 H4 H5. apply AG; [clear - H0 H1; Lia.lia|]. unfold PMBUK.WretX, PMBUK.Wret. change (ff_bytes 1) with 128. change (128 / 8) with 16. unfold SB.
    intros [[[Y|Y]|Y]|Y]; [clear - Y H2; Lia.lia| clear - Y H3 GF1 GF2 GF8; Lia.lia| clear - Y H4; Lia.lia| exact (H5 Y)].
  - intros x H0 H1 H2. apply AG; [unfold HeapIfaceA.S, SB; clear - H0 H1; Lia.lia|]. unfold PMBUK.WretX, PMBUK.Wret. change (ff_bytes 1) with 128. change (128 / 8) with 16. unfold SB.
    intros [[[Y|Y]|Y]|Y]; unfold HeapIfaceA.S, SB in Y; [clear - Y H0 H1 GFBIG; Lia.lia| clear - Y H2 GF8; Lia.lia| clear - Y H0 H1 GLBIG; Lia.lia|].
    destruct (WXa _ Y) as [W0 W1]. clear - W0 W1 H0 H1. Lia.lia.
Qed.

Lemma sink_retire Mq mdq LKq Awq crq kq a (Mf : word -> option byte) (Wx : Z -> Prop) :
  inv Mq mdq LKq Awq crq kq a ->
  (forall a0, 0 <= a0 < 2 ^ 64 -> ~ PMBUK.WretX F fl 1 Wx a0 -> Mf (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)) ->
  (forall a0, Wx a0 -> exists q m, In (q, m) (PEC.enc_own en) /\ q <= a0 < q + m) ->
  PESKA.sink_atA RSEGS L ar P Mf (PESK.o_sink EE fb) kq.
Proof.
  intros INV FZf WXin. entry_facts. name_objs. cut_facts INV kq.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & GNF & GNV & GFLP).
  assert (WXa : forall a0, Wx a0 -> 0 <= a0 /\ (2147446784 + 17592186048512 <= a0 \/ a0 + 1 <= 2147446784)).
  { intros a0 Xa. destruct (WXin a0 Xa) as (q & m & Hq & Xq). destruct (eblk_facts q m Hq) as (_ & _ & _ & _ & B0 & B47 & BAPP & _). clear - Xq B0 B47 BAPP; lia. }
  destruct (retire_agree Mq Mf Wx FZf WXa) as [AGa AGs].
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKB.aobj_of_aobjA FF' osk 24 (PMBUAR.aobjA_push FF osk 24 _ (AOF osk 24 ltac:(lia) ltac:(lia))) K8) ltac:(lia) ltac:(reflexivity))
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
    { intros E. pose proof (PMBSK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HHq) as NDq. unfold LBq, EBX in NDq. rewrite map_app in NDq |- * || idtac. rewrite <- app_assoc in NDq.
      apply (PMBSK.fst_neq_appA (PEC.enc_own en) (PESK.sink_own kq ++ LBc0) q m (PESK.sk_b kq) (PESK.sk_c kq) NDq Hq); [| symmetry; exact E].
      apply in_or_app; left. unfold PESK.sink_own. replace (PESK.sk_c kq =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
    destruct (PMBSK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ (PESK.sk_b kq) (PESK.sk_c kq) q m HHq IN ltac:(apply in_or_app; left; unfold EBX; apply in_or_app; left; exact Hq) NE); clear - H Hi Xq; lia.
Qed.

Lemma finish_ro pcq (fxq : FPState) Rq Mq mdq LKq Awq crq kq (fx3 : FPState) R3 M3v :
  inv Mq mdq LKq Awq crq kq NB -> xestk = [] ->
  msteps RSEGS (mst fxq Rq pcq (mrestrict (ahid Awq mdq) Mq)) (mst fx3 R3 r M3v) -> mem_grows (mrestrict (ahid Awq mdq) Mq) M3v ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ PMBUK.Wret F fl 1 i -> M3v (Z_to_bv 64 i) = mrestrict (ahid Awq mdq) Mq (Z_to_bv 64 i)) ->
  L5.u8_at RSEGS M3v fl 0 -> regs_preserved R R3 ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcq Mq mdq) K.
Proof.
  intros INV HXS MS3 MG3 FRZ3 FL0 RP3. entry_facts. name_objs. cut_facts INV kq.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & GNF & GNV & GFLP).
  pose proof KONT as KT. unfold e_end_value in KT. cbn [s_estk XS] in KT. rewrite HXS in KT.
  unfold PMSPA.cfg.
  apply (PMBUK.retire_core L ar C HI LYa HIok M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
           Wk (EBX kq) Mq mdq LKq crq Awq fxq fx3 Rq pcq R3 r M3v K BI MS3 MG3 FRZ3 FL0).
  intros Mf mdf FZf AHf MRTf AMf HHf.
  assert (FZf' : forall a0, 0 <= a0 < 2 ^ 64 -> ~ PMBUK.WretX F fl 1 (fun _ => False) a0 -> Mf (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha N. apply FZf; [exact Ha|]. intros X'. apply N. left. exact X'. }
  destruct (retire_agree Mq Mf (fun _ => False) FZf' ltac:(intros a0 [])) as [AGa AGs].
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKB.aobj_of_aobjA FF' ov 56 (PMBUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia))) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2 & Q3 & _) & QBIG & _).
  assert (EAf : PECA.enc_atA RSEGS EE L ar Mf ov fb en).
  { apply (PECFA.enc_atA_agree RSEGS EE L ar Mq Mf ov fb en); [clear - Q1; lia| clear - Q3; lia| | | exact EAq].
    - split; [| intros x Hx; apply AGs; clear - Hx Q1 Q3 AvF; lia].
      intros i Hi. apply AGa; [clear - Hi Q1; lia| clear - Hi Q3; lia| clear - Hi AvF; lia| clear - Hi QBIG; lia| clear - Hi AvL; lia| intros []].
    - intros Hp. assert (IN : In (PEC.en_b en, PEC.ESZ * PEC.ecap (PEC.en_k en)) (EBX kq ++ LBc0)).
      { apply in_or_app; left. unfold EBX. apply in_or_app; left. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
      destruct (blk_facts Mq LKq crq Awq _ kq _ _ HHq IN) as (B0 & B47 & BAPP & BCEIL & BFS). unfold FS_BYTES in BFS, GFS2, GFLP.
      split; [clear - B0; lia|]. split; [clear - B47; lia|].
      split; [| intros x Hx; apply AGs; clear - Hx B0 B47 BFS GFS1 GFS2; lia].
      intros i Hi. apply AGa; [clear - Hi B0; lia| clear - Hi B47; lia| clear - Hi BFS GFS1 GFS2; lia| clear - Hi BAPP B0; lia| clear - Hi BFS GFLP; lia| intros []]. }
  pose proof (sink_retire Mq mdq LKq Awq crq kq NB Mf (fun _ => False) INV FZf' ltac:(intros a0 [])) as SKAf.
  destruct (keepf Mf (proj1 AHf)) as (PA' & IA' & VREF' & BASE' & ERR' & CONT' & ECS' & ACCR').
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & TBOK & _ & CL & _ & ECI & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad X] in Lmore, Ldone, Ldepth, Lstk, Lpos, Lestk, Ledepth, Lz, Lbad.
  apply (KT fx3 R3 Mf mdf LKq Awq en kq e crq).
  - exact RP3.
  - unfold PECA.crun_preA. fold op ov ois osk.
    split; [exact PA'|]. split; [exact IA'|]. split; [exact EAf|]. split; [exact VREF'|]. split; [exact SKAf|].
    split; [exact BASE'|]. split; [exact ERR'|]. split; [exact TBOK|]. split; [exact CONT'|].
    split.
    { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad XS].
      split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
      split; [first [exact Lestk | rewrite HXS in Lestk; exact Lestk]|]. split; [exact Ledepth|]. split; [clear - CLq; lia| exact Lbad]. }
    cbn [s_ec XS]. split; [exact ECS'|]. split; [exact ECI| exact ACCR'].
  - intros E1; exact E1.
  - exact (ahpres_wenc Mf AHf).
  - exact CKq.
  - exact MRTf.
  - exact ILKq.
  - exact IAWq.
  - exact AMf.
  - exact (ri_perm _ _ FF LKq crq Awq Mf _ (perm_q kq) HHf).
Qed.

Lemma finish_bump pcq (fxq : FPState) Rq Mq mdq LKq Awq crq kq (fx3 : FPState) R3 M3v e1 rr :
  inv Mq mdq LKq Awq crq kq NB -> xestk = e1 :: rr ->
  let ed := PEC.en_b en + 24 * (Z.of_nat (length rr) + 1) in
  msteps RSEGS (mst fxq Rq pcq (mrestrict (ahid Awq mdq) Mq)) (mst fx3 R3 r M3v) -> mem_grows (mrestrict (ahid Awq mdq) Mq) M3v ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ PMBUK.Wret F fl 1 i -> ~ (ed - 8 <= i < ed - 8 + 8) -> M3v (Z_to_bv 64 i) = mrestrict (ahid Awq mdq) Mq (Z_to_bv 64 i)) ->
  L5.u64_at RSEGS M3v (ed - 8) ((ei_cnt e1 + 1) mod 2 ^ 64) -> L5.u8_at RSEGS M3v fl 0 -> regs_preserved R R3 ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcq Mq mdq) K.
Proof.
  intros INV HXS ed MS3 MG3 FRZ3 C8 FL0 RP3. entry_facts. name_objs. cut_facts INV kq.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AvF & AvS & AvL & AkF & AkS & AkL & GFS1 & GFS2 & GNF & GNV & GFLP).
  destruct (vis_facts_top Mq mdq LKq Awq crq kq NB e1 rr INV HXS) as (HLEN & EKP & EB1 & ED2 & ALend & ED3 & _ & EB6 & _ & EDS & OVA & _ & E1C & E1OK & BINe & EDC & EBC & EDF & EDSH & EDFL & EDV).
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & TBOK & _ & CL & _ & ECI & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad X] in Lmore, Ldone, Ldepth, Lstk, Lpos, Lestk, Ledepth, Lz, Lbad. rewrite HXS in Lestk.
  pose proof KONT as KT. unfold e_end_value in KT. cbn [s_estk XS] in KT. rewrite HXS in KT.
  pose proof (enc_eta en) as EN.
  pose proof EAq as EAq'. rewrite EN in EAq'.
  set (eb := PEC.en_b en) in *. set (ek := PEC.en_k en) in *. set (estk := PEC.en_stk en) in *. set (edepth := PEC.en_depth en) in *.
  cbn [PEC.en_stk PEC.en_depth] in Lestk, Ledepth.
  set (m := Z.of_nat (length rr)) in *. assert (M0 : 0 <= m) by (unfold m; clear; lia).
  destruct e1 as [kd ln cn]. cbn [ei_kind ei_len ei_cnt] in C8, E1C, KT.
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKB.aobj_of_aobjA FF' ov 56 (PMBUAR.aobjA_push FF ov 56 _ (AOF ov 56 ltac:(lia) ltac:(lia))) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2' & Q3 & Q4 & Q5) & QBIG & _).
  assert (BINq : In (eb, 24 * PEC.ecap ek) LBq) by (unfold LBq, EBX; apply in_or_app; left; apply in_or_app; left; exact BINe).
  destruct (blk_facts Mq LKq crq Awq _ kq _ _ HHq BINq) as (B0 & B47 & BAPP & BCEIL & BFS). unfold FS_BYTES in BFS, GFS2, GFLP.
  set (Wx := fun a0 => ed - 8 <= a0 < ed - 8 + 8).
  unfold PMSPA.cfg.
  apply (PMBUK.retire_coreW L ar C HI LYa HIok M model LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k) G
           Wk (EBX kq) Mq mdq LKq crq Awq Wx fxq fx3 Rq pcq R3 r M3v K BI).
  { intros a0 Xa. unfold Wx in Xa. split.
    - unfold aclientw, aclient_g. left. exists (eb, 24 * PEC.ecap ek). split; [exact BINq|]. cbn [fst snd]. unfold ed in Xa. clear - Xa M0 EDC; lia.
    - intros O. apply (O (eb, 24 * PEC.ecap ek)); [right; exact BINe| unfold L5.in_rng; cbn [fst snd]; unfold ed in Xa; clear - Xa M0 EDC; lia]. }
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
  assert (EA3 : PECA.enc_atA RSEGS EE L ar Mf ov fb (PEC.ENC eb ek (rev (PEEK.ebump (EI kd ln cn :: rr))) edepth)).
  { apply (enc_bumpA Mq Mf ov fb eb ek (EI kd ln cn :: rr) edepth); [rewrite <- Lestk; exact EAq'| clear - Q1; lia| clear - Q3; lia| intros _; unfold PEC.ESZ; clear - EB1 EBC; lia| | | | exact MGf|].
    - split; [| intros x Hx; apply AGs; clear - Hx Q1 Q3 AvF; lia]. intros i Hi. apply AGa; [clear - Hi Q1; lia| clear - Hi Q3; lia| clear - Hi AvF; lia| clear - Hi QBIG; lia| clear - Hi AvL; lia|].
      unfold Wx, ed. clear - Hi OVA M0. lia.
    - intros _ i Hi Ri Ni. apply AGa; [clear - Hi; lia| unfold PEC.ESZ in Ri; clear - Ri EBC; lia| unfold PEC.ESZ in Ri; clear - Ri BFS GFS1 GFS2; lia| unfold PEC.ESZ in Ri; clear - Ri BAPP B0; lia| unfold PEC.ESZ in Ri; clear - Ri BFS GFLP; lia|].
      cbn [PEEK.cc_rng length] in Ni. fold m in Ni. unfold PEC.ESZ in Ni. unfold Wx, ed. clear - Ni. lia.
    - intros _ x Hx. apply AGs; unfold PEC.ESZ in Hx; [clear - Hx EB1; lia| clear - Hx EBC; lia| clear - Hx BFS GFS1 GFS2; lia].
    - intros e2 rr' Hc. injection Hc as <- <-. cbn [ei_cnt]. fold m. unfold PEC.ESZ, TWO64. replace (eb + 24 * m + 16) with (ed - 8) by (unfold ed; clear; lia). exact C8'. }
  cbn [PEEK.ebump ei_kind ei_len ei_cnt] in EA3.
  pose proof (sink_retire Mq mdq LKq Awq crq kq NB Mf Wx INV FZf WXin) as SKAf.
  destruct (keepf Mf (proj1 AHf)) as (PA3 & IA3 & VREF3 & BASE3 & ERR3 & CONT3 & ECS3 & ACC3).
  apply (KT fx3 R3 Mf mdf LKq Awq (PEC.ENC eb ek (rev rr ++ [EI kd ln ((cn + 1) mod TWO64)]) edepth) kq e crq).
  + exact RP3.
  + unfold PECA.crun_preA. fold op ov ois osk.
    split; [exact PA3|]. split; [exact IA3|]. split; [unfold TWO64; exact EA3|]. split; [exact VREF3|]. split; [exact SKAf|].
    split; [exact BASE3|]. split; [exact ERR3|]. split; [exact TBOK|]. split; [exact CONT3|].
    split.
    { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PEC.en_stk PEC.en_depth rev w_estk XS].
      split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
      split; [reflexivity|]. split; [exact Ledepth|]. split; [clear - CLq; lia| exact Lbad]. }
    cbn [s_ec w_estk XS]. split; [exact ECS3|]. split; [exact ECI| exact ACC3].
  + intros E1; exact E1.
  + exact (ahpres_wenc Mf AHf).
  + unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CKq |- *. cbn [fst snd PEC.en_k] in CKq |- *. change (PEC.en_k en) with ek in CKq |- *. clear - CKq. lia.
  + exact MRTf.
  + exact ILKq.
  + exact IAWq.
  + exact AMf.
  + exact (ri_perm _ _ FF LKq crq Awq Mf _ (perm_q kq) HHf).
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
  pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 20480 FR HH ASTK ltac:(clear - HFR; lia)) as (_ & _ & SWR).
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 sp 20480 HH (PMKB.aobj_of_aobjA FF ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m) ltac:(lia) ltac:(reflexivity)) as ((Q1 & Q2' & Q3 & _) & _).
  pose proof A10 as B10. rewrite L5K.rl10 in B10.
  split. { split; [apply L5A.img_clear_mrestrict; exact GOT|].
    split; [apply (proj2 (L5A.u64_at_vis H M 1335544 SBL (VIMG 1335544 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB|].
    split; [apply (proj2 (L5A.u32_at_vis H M 1335552 1 (VIMG 1335552 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR|].
    split; [clear - SLO SHI SPT; lia|]. split; [exact SP32| exact SWR]. }
  split; [exact Rsp|]. split; [exact B10|]. split; [exact Rra|]. split; [exact RAok|]. clear - Q1 Q3; lia.
Qed.

Lemma start (pc0 smra : Z) (fx1 : FPState) R1 M1v :
  msteps RSEGS (mst fx R pc0 (mrestrict (ahid Aw model) M)) (mst fx1 R1 SM1 M1v) -> mem_grows (mrestrict (ahid Aw model) M) M1v ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - FR <= i < sp - FR + FR) -> M1v (Z_to_bv 64 i) = mrestrict (ahid Aw model) M (Z_to_bv 64 i)) ->
  owns SAVED sp R M1v -> getr R1 (reg 1) = Z_to_bv 64 smra -> getr R1 (reg 2) = Z_to_bv 64 spc -> getr R1 (reg 4) = getr R (reg 4) ->
  0 <= smra < 2 ^ 64 -> smra mod 2 = 0 ->
  (forall F fl LK2 M2 model2 R2
      (G : PMBUK.gctx L ar HI LBc0 FF LK Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R) F fl 1 LK2 M2 model2 cr (EBX k))
      (APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (EBX k ++ LBc0) FF sp0 scr0 (a + i)) -> 0 < n ->
                 (a + n <= F \/ F + 128 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + 16 <= a) /\ (a + n <= fl \/ fl + 1 <= a)),
      inv F M2 model2 LK2 Aw cr k 0 -> regs_preserved R1 R2 -> getr R2 (reg 10) = Z_to_bv 64 F ->
      L5KA.zeros_at (mrestrict (ahid Aw model2) M2) (F / 8 + SBL) 16 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx1) R2 smra M2 model2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R pc0 M model) K.
Proof.
  intros MS1 MG1 FRZ1 OWN1v T1 T2 T4 SMR SM2 KF. entry_facts. name_objs. pose proof AM as (Mh & MI).
  pose proof NSVv as NV.
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 20480 FR HH ASTK ltac:(clear - HFR; lia)) as (SLF & SHF & SWR).

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
  pose proof (PMKB.ek_sublb L ar LB LBc0 FF sp 20480 [] M M1 INC0 EK01f) as EK01.
  pose proof (PMKB.dk_sublb L ar LB LBc0 FF sp 20480 M M1 INC0 DK01f) as DK01.
  assert (OWN1 : owns SAVED sp R M1).
  { apply (owns_agree SAVED sp R M1v M1 ltac:(pose proof NSVv as NV'; unfold NSV in NV'; clear - SLF SPT NV' HFR; lia) ltac:(clear - SHI SPT; lia) OWN1v). intros a Ha. unfold ocell in Ha. pose proof NSVv as NV'; unfold NSV in NV'.
    symmetry. rewrite <- VIS1. apply mrestrict_visible. replace a with ((sp - FR) + (a - (sp - FR))) by (clear; lia). apply (VIS (sp - FR) FR); [clear - SLF; lia| clear - SHF SHI SPT; lia| clear - Ha NV' HFR; lia]. }

  assert (FRk0 : ff_room 1 FF LK) by (pose proof (FRM 1 ltac:(right; left; reflexivity)) as X'; unfold ff_room; clear - X'; lia).
  change SM1 with (PMB.SM_PC 1).
  apply (PMBUAR.uar_sm L ar C HI LY HIok 1 LBc0 (EBX k) FF LK cr Aw sp 20480 spc (sp - 8 * NSV) sp (ocell sp NSV) (owns SAVED sp R)
           fx1 R1 M M1 model model1 K smra ltac:(right; left; reflexivity) HHp (ri_perm _ _ FF LK cr Aw M1 _ (Permutation_sym (perm_q k)) HH1) AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite T4. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { exact SM2. }
  { exact SMR. }
  { exact SPC16. }
  { unfold spc; clear - HFR; lia. } { unfold spc; clear - HFR NV; lia. } { clear - NV; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (owns_agree SAVED sp R Ma Mb ltac:(pose proof NSVv as NV'; unfold NSV in NV'; clear - SLF SPT NV' HFR; lia) ltac:(clear - SHI SPT; lia) OW). exact AG. }
  { exact FRk0. }
  { intros f Hf. exact (FRS f Hf). }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. change (128 - 8) with 120 in *.
  pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *.

  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (EINC : incl (PEC.enc_own en) LB) by (unfold LB, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (KINC : incl (PESK.sink_own k) LB) by (unfold LB, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad). cbn [s_lo s_hi X] in Lz.
  assert (INCp : incl LB (EBX k ++ LBc0)) by (intros x Hx; apply (Permutation_in x (Permutation_sym (perm_q k))); exact Hx).
  pose proof (L5SAR.ek_trans L ar LB FF sp 20480 [] M M1 M2 EK01f (PMKB.ek_sublb L ar (EBX k ++ LBc0) LB FF sp 20480 [] M1 M2 INCp EK12f)) as EK02f.
  assert (INV2 : inv F M2 model2 LK2 Aw cr k 0).
  { unfold inv. split.
    - unfold PMBUK.binv. split; [exact GHH2|]. split; [exact AM2|]. split; [exact (L5LZ.model_rt_trans _ _ _ MRT1 MRT2)|].
      split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact ASTK2|].
      split; [apply (L5SAR.ek_W L ar LBc0 FF sp 20480 Wk [] M M2 EK02); intros a _ r0 []|].
      split; [exact DK02|].
      split; [apply (owns_agree SAVED sp R M1 M2 ltac:(pose proof NSVv as NV'; unfold NSV in NV'; clear - SLF SPT NV' HFR; lia) ltac:(clear - SHI SPT; lia) OWN1); intros a Ha; unfold ocell in Ha; apply AGF; pose proof NSVv as NV'; unfold NSV in NV'; unfold spc; clear - Ha NV' HFR; lia|].
      change (ff_bytes 1 / 8) with 16. apply (proj1 (L5A.defined_vis (ahid Aw model2) M2 (F / 8 + SB) 16 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. rewrite Z0. discriminate.
    - split; [apply (PMKB.stksh_keepA L ar LB FF sp 20480 [] M M2 EK02f PMKB.wapp_nil (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact STKSH]|].
      split; [apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp 20480 [] M M2 EK02f PMKB.wapp_nil FRB BRB ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact EINC| intros _ i _ r0 []| exact EA]|].
      split; [apply (PECFA.sink_keepA RSEGS L ar LB FF sp 20480 [] M M2 EK02f PMKB.wapp_nil FRB BRB P osk k (AOF osk 24 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact KINC| intros _ i _ r0 []| exact SKA]|].
      split; [clear - Lz; lia|]. unfold PMSP.credit_keep. clear. lia. }
  exact (KF F fl LK2 M2 model2 R2 G APART INV2 RP2 ltac:(rewrite <- L5K.rl10; exact G10) FSHZ).
Qed.
End Call.
End WithHeap.
End PEBEK1.
