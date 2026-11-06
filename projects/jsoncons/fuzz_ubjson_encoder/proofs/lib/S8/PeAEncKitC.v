(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PmModelFactsA PmStep PeStepA PmParKit PeASrcKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCSinkA PeShZ PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrame PeCFrameA PeEncKit PeACReset1 PeAEncNtbSpec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEAEKC.
#[local] Transparent e_end_value.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)).

Abbreviation SBL := 2147450880.

Definition CSK : list nat := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMA.ly_as0 L C LY.

Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.

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

Variable FC : (word -> option byte) -> Prop.
Hypothesis FC_frame : forall M1 M2, (forall a, sp - FR <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> FC M1 -> FC M2.
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

Let LBY : list (Z * Z) := PM.parser_own s ++ PEC.enc_own en ++ LBX.

Let Ws : list L5.range := [(PESK.o_sink EE fb, 24)].

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
Lemma ws_wenc a : L5.outside (PEC.W_enc AD EE fb) a -> L5.outside Ws a.
Proof. intros O r0 [<-|[]]. apply O. unfold PEC.W_enc. cbn [app]. right; left; reflexivity. Qed.
Lemma ws_wapp : PMKA.wapp Ws.
Proof.
  entry_facts. unfold Ws. apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd pe_off_sink PeCLayoutA.EADDR_A]. unfold PESK.o_sink. cbn [pe_off_sink PeCLayoutA.EADDR_A].
  unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - F1 F2 FSAPP. lia.
Qed.

Definition inv (Mi : word -> option byte) (mdi : Model) (LKi : list fframe) (Awi : list (Z * Z)) (cri : credit) (ki : PESK.sink) (a : Z) : Prop :=
  FC Mi /\ L5CA.astk ar Mi sp 20480 /\ shadow_zero Mi (sp - 20480) 2560
  /\ model_rt model mdi /\ L5CA.amodel_ok Awi mdi /\ incl LKi LK /\ incl Aw Awi
  /\ ri_inv HI (PEC.owned s en ki ++ LBX) FF LKi cri Awi Mi (vml_of mdi)
  /\ PECA.enc_atA RSEGS EE L ar Mi (PMSPA.o_v AD fb) fb en /\ PESKA.sink_atA RSEGS L ar P Mi (PESK.o_sink EE fb) ki
  /\ xlo + a <= PESK.sk_z ki <= xhi + a
  /\ L5SAR.ek L ar LBc0 FF sp 20480 Ws M Mi /\ L5SAR.dk L ar LBc0 FF sp 20480 M Mi
  /\ PMSP.credit_keep cr cri (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en ki).

Lemma keepf Mi : L5SAR.ek L ar LBc0 FF sp 20480 Ws M Mi ->
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
  assert (OUT : forall i, ~ (osk <= i < osk + 24) -> L5.outside Ws i) by (intros i N r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; clear - N; lia).
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply AOF; clear - Eosk; lia).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model osk 24 sp 20480 HH (PMKA.aobj_of_aobjA FF osk 24 AOSK K8) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & _).
  assert (OUTB : forall q m, In (q, m) LBc0 -> PMKA.blk_out Ws q m).
  { intros q m Hq i Hi. destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m osk 24 HH (INC0 _ Hq) AOSK) as [Xa|Xa]; apply OUT; clear - Xa Hi; lia. }
  assert (OUTO : forall a m, (a + m <= osk \/ osk + 24 <= a) -> forall i, a <= i < a + m -> L5.outside Ws i) by (intros a m Xa i Hi; apply OUT; clear - Xa Hi; lia).
  assert (Iq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LBc0) by (apply PINC; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (SDEP : forall a, PMST.dep AD a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside Ws a).
  { intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
    split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OUT. clear - DI K1; lia. }
  split.
  { apply (PMKA.parser_keepA RSEGS AD L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB BRc0 op ois s (AOF op 384 ltac:(lia) ltac:(lia)) PINC); [| | | | exact PA].
    - apply OUTO. clear - Eop Eosk; lia.
    - apply OUTB. exact Iq.
    - apply OUTB. apply PINC. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
    - intros c n q E1. apply OUTB. apply PINC. unfold PM.parser_own, PM.vs_own. rewrite E1. right; right; left. reflexivity. }
  split.
  { apply (PMKA.iss_keepA RSEGS AD L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB BRc0 ois str sm (AOF ois 272 ltac:(lia) ltac:(lia)) SINC); [| | exact IA].
    - apply OUTO. clear - Eois Eosk; lia.
    - intros c n0 q E1. refine (OUTB q c _). apply SINC. unfold PM.vs_own. rewrite E1. left. reflexivity. }
  split.
  { apply (PMKA.u64_keepA RSEGS L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF]. apply OUTO. clear - Eop Eosk; lia. }
  split.
  { change (PMSTA.base_okA RSEGS PMA.AD Mi). apply (PMASK.base_keep L ar C LY LBc0 FF sp 20480 Ws M Mi EK); [| exact BASE]. intros a Ha. apply OUT. clear - Ha K1; lia. }
  split.
  { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBc0 FF sp 20480 Ws M Mi EK e PECSA.addrs_wf_A); [exact SDEP| exact ERR]. }
  split.
  { apply (content_keepA' LBc0 FF sp 20480 Ws M Mi fb p s str sm op EK WAPP FRB BRc0 (AOF ois 272 ltac:(lia) ltac:(lia))); [| exact SINC| exact Iq| exact OUTB| exact IA| exact PA| exact CONT].
    fold ois. apply OUTO. clear - Eois Eosk; lia. }
  split.
  { apply (PECFA.ec_state_keepA RSEGS AD L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB fb xec cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
    fold oec. apply OUTO. clear - Eoec Eosk; lia. }
  exact (PMKA.acc_keepA' L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACCR).
Qed.

Lemma inv_cpre Mi mdi LKi Awi cri ki a lo hi : inv Mi mdi LKi Awi cri ki a -> lo = xlo + a -> hi = xhi + a ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth lo hi xbad) s str sm en ki e cat.
Proof.
  intros (FCi & ASTKi & SZi & MRTi & AMi & ILKi & IAWi & HHi & EAi & SKAi & CLi & EKi & DKi & CKi) Hlo Hhi.
  destruct (keepf Mi EKi) as (PA' & IA' & VREF' & BASE' & ERR' & CONT' & ECS' & ACCR').
  destruct CPRE as (_ & _ & _ & _ & _ & _ & _ & TBOK & _ & CL & _ & ECI & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad). cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad] in *.
  unfold PECA.crun_preA.
  split; [exact PA'|]. split; [exact IA'|]. split; [exact EAi|]. split; [exact VREF'|]. split; [exact SKAi|].
  split; [exact BASE'|]. split; [exact ERR'|]. split; [exact TBOK|]. split; [exact CONT'|].
  split.
  { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad].
    split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
    split; [exact Lestk|]. split; [exact Ledepth|]. split; [clear - CLi Hlo Hhi; lia| exact Lbad]. }
  cbn [s_ec]. split; [exact ECS'|]. split; [exact ECI| exact ACCR'].
Qed.

Lemma pb_call (a pv h ra0 : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  inv Mq mdq LKq Awq crq kq a -> PESKA.spa_hb P h -> xhi + a <= h -> sp - FR <= pv -> pv + 1 <= sp -> L5.ra_ok ra0 ->
  getr Rq (reg 1) = Z_to_bv 64 ra0 -> getr Rq (reg 2) = Z_to_bv 64 (sp - FR) ->
  getr Rq (reg 10) = Z_to_bv 64 (PESK.o_sink EE fb) -> getr Rq (reg 11) = Z_to_bv 64 pv -> csk Rq ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 cr2 k2, inv M2 md2 LK2 Aw2 cr2 k2 (a + 1) -> regs_preserved Rq R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R2 ra0 M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq 0xaf02c Mq mdq) K.
Proof.
  intros INV HBh Ha PV1 PV2 RA0 Q1 Q2 Q10 Q11 QCS KX. entry_facts. name_objs. pose proof RA0 as (Hra1 & Hra2).
  pose proof INV as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  set (LBq := PEC.owned s en kq ++ LBX) in HHq.
  assert (PERMq : Permutation LBq (PESK.sink_own kq ++ LBY)) by (unfold LBq, LBY, PEC.owned; rewrite <- !app_assoc; apply PEEK.perm4).
  pose proof (ri_perm _ _ FF LKq crq Awq Mq _ PERMq HHq) as HHY.
  assert (XINCq : incl LBc0 LBY) by (unfold LBc0, LBY; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (EINCq : incl (PEC.enc_own en) LBY) by (unfold LBY; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (BRBY : forall x, In x LBY -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
  { intros x Hx. apply (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHY). apply in_or_app. right. exact Hx. }
  assert (FRBq : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply AOF; clear - Eosk; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKA.aobj_of_aobjA FF osk 24 AOSK K8) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & KBIG & _).
  pose proof SKAq as (_ & _ & _ & _ & _ & KZCq & KCAPq & KC0q & KBLKq).
  pose proof EAq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EKq' & _).
  pose proof (PMA.ly_cost L C LY) as (KPM & BLIN & BOV).
  assert (PEN : 0 <= fst (PMSPA.scA L (PEC.pot_estack (PMSPA.HV L ar) (PEC.en_k en))) /\ 0 <= snd (PMSPA.scA L (PEC.pot_estack (PMSPA.HV L ar) (PEC.en_k en)))).
  { unfold PMSPA.scA, PEC.pot_estack, PEC.ESZ, PMSPA.HV, LibIfaceAB.heap_view. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead]. rewrite KPM, BOV, BLIN.
    assert (P2 : 2 ^ PEC.en_k en <= 2 ^ 12) by (apply Z.pow_le_mono_r; clear - EKq'; lia). clear - EKq' P2. split; nia. }
  pose proof PB as PBX. unfold PESKA.push_back_specA in PBX. cbn [pe_push_back EE PeCLayoutA.EADDR_A] in PBX.
  apply (PBX PMODE fxq Rq Mq mdq K LBY FF LKq Awq crq osk pv (sp - FR) ra0 kq HHY AMq K0); clear PBX.
  {
    split; [rewrite L5K.rl1; exact Q1|]. split; [exact RA0|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536. split.
    - apply (L5SAR.astk_sub ar Mq Mq sp 20480 FR 12288 ASTKq); [intros w D; exact D| clear - HFR; lia| clear; lia| clear - HFR; lia| exact SPF16].
    - apply (PMKA.shadow_zero_sub Mq (sp - 20480) 2560); [apply SPd8; reflexivity| | clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZq].
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

  assert (OWs : forall a0, sp - 20480 <= a0 < sp -> L5.outside Ws a0).
  { intros a0 Ha0 r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk. clear - Ha0 K2 SLO; lia. }
  assert (FRAME12 : forall a0, sp - FR <= a0 < sp -> M2 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT HFR; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT HFR; lia| intros Y; clear - Ha0 Y; lia].
    - apply OWs. clear - Ha0 HFR; lia. }
  assert (EK12 : L5SAR.ek L ar LBY FF sp 20480 Ws Mq M2).
  { apply (L5SAR.ek_callee L ar LBY [] FF [] sp 20480 (sp - FR) 12288 Ws Ws Mq M2 HP2); [clear - HFR; lia| clear - HFR; lia| intros a0 _ O; exact O]. }
  assert (DK12 : L5SAR.dk L ar LBY FF sp 20480 Mq M2) by (apply (L5SAR.dk_callee L ar LBY [] FF [] sp 20480 (sp - FR) 12288 Ws Mq M2 HP2); clear - HFR; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480).
  { apply (PMKA.astk_after_ahpres L ar LBY FF Mq M2 sp 20480 (sp - FR) 12288 Ws ASTKq HP2); [clear - HFR; lia| clear - HFR; lia| clear; lia| exact STOP]. }
  pose proof ws_wapp as WAPP.
  assert (SZ2 : shadow_zero M2 (sp - 20480) 2560).
  { apply (PMKA.stksh_keepA L ar LBY FF sp 20480 Ws Mq M2 EK12 WAPP (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZq]. }
  assert (OUTO : forall a1 m, (a1 + m <= osk \/ osk + 24 <= a1) -> forall i, a1 <= i < a1 + m -> L5.outside Ws i).
  { intros a1 m Xa i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk. clear - Xa Hi; lia. }
  assert (OUTBY : forall q m, In (q, m) LBY -> PMKA.blk_out Ws q m).
  { intros q m Hq. destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m osk 24 HHY (in_or_app _ _ _ (or_intror Hq)) AOSK) as [Xa|Xa];
      (intros i Hi; apply (OUTO q m); [clear - Xa; lia| exact Hi]). }
  apply (KX fx2 R2 M2 md2 LK2 Aw2 cr2 k2); [| exact RP2].
  unfold inv. split; [exact (FC_frame Mq M2 FRAME12 FCq)|]. split; [exact ASTK2|]. split; [exact SZ2|].
  split; [exact (L5LZ.model_rt_trans model mdq md2 MRTq MRT2)|]. split; [exact AM2|].
  split; [intros x Hx; apply ILKq; apply ILK2; exact Hx|]. split; [intros x Hx; apply IAW2; apply IAWq; exact Hx|].
  split; [refine (ri_perm _ _ FF LK2 cr2 Aw2 M2 _ _ HH2); unfold PEC.owned, LBY; rewrite <- !app_assoc; apply Permutation_sym; apply PEEK.perm4|].
  split.
  { apply (PECFA.enc_keepA RSEGS EE L ar LBY FF sp 20480 Ws Mq M2 EK12 WAPP FRBq BRBY ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [| exact EINCq| | exact EAq].
    - apply OUTO. clear - Eov Eosk; lia.
    - intros Hp. apply OUTBY. apply EINCq. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
  split; [exact SKA2|].
  split; [unfold k2, PESK.sk_push; destruct (PESK.sk_z kq <? PESK.sk_c kq); cbn [PESK.sk_z]; clear - CLq; lia|].
  split; [exact (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mq M2 EKq (PMKA.ek_sublb L ar LBY LBc0 FF sp 20480 Ws Mq M2 XINCq EK12))|].
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M2 DKq (PMKA.dk_sublb L ar LBY LBc0 FF sp 20480 Mq M2 XINCq DK12))|].
  unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CKq, CK2 |- *. cbn [fst snd] in CKq, CK2 |- *. clear - CKq CK2. lia.
Qed.

Lemma wr_call (a kb pcw h ra0 : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  PENTBA.ntb_specA RSEGS AD L ar HI pcw kb P ->
  inv Mq mdq LKq Awq crq kq a -> PESKA.spa_hb P h -> xhi + a + kb <= h -> 0 <= kb -> L5.ra_ok ra0 ->
  getr Rq (reg 1) = Z_to_bv 64 ra0 -> getr Rq (reg 2) = Z_to_bv 64 (sp - FR) ->
  getr Rq (reg 11) = Z_to_bv 64 (PMSPA.o_v AD fb + 8) -> csk Rq ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 cr2 k2, inv M2 md2 LK2 Aw2 cr2 k2 (a + kb) -> regs_preserved Rq R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R2 ra0 M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq pcw Mq mdq) K.
Proof.
  intros NTB INV HBh Ha KB0 RA0 Q1 Q2 Q11 QCS KX. entry_facts. name_objs. pose proof RA0 as (Hra1 & Hra2).
  pose proof INV as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  set (LBq := PEC.owned s en kq ++ LBX) in HHq.
  assert (PERMq : Permutation LBq (PESK.sink_own kq ++ LBY)) by (unfold LBq, LBY, PEC.owned; rewrite <- !app_assoc; apply PEEK.perm4).
  pose proof (ri_perm _ _ FF LKq crq Awq Mq _ PERMq HHq) as HHY.
  assert (XINCq : incl LBc0 LBY) by (unfold LBc0, LBY; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (EINCq : incl (PEC.enc_own en) LBY) by (unfold LBY; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (BRBY : forall x, In x LBY -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
  { intros x Hx. apply (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHY). apply in_or_app. right. exact Hx. }
  assert (FRBq : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply AOF; clear - Eosk; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKA.aobj_of_aobjA FF osk 24 AOSK K8) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & KBIG & _).
  pose proof SKAq as (_ & _ & _ & _ & _ & KZCq & KCAPq & KC0q & KBLKq).
  pose proof EAq as (_ & EV8 & _ & _ & _ & _ & _ & _ & EACC & EKq' & _). fold osk in EV8.
  assert (Q8v : (ov + 8) mod 8 = 0) by (rewrite Eov; replace (fb + 496 + 8) with (fb + 8 * 63) by lia; apply FB8).
  pose proof (PMA.ly_cost L C LY) as (KPM & BLIN & BOV).
  assert (PEN : 0 <= fst (PMSPA.scA L (PEC.pot_estack (PMSPA.HV L ar) (PEC.en_k en))) /\ 0 <= snd (PMSPA.scA L (PEC.pot_estack (PMSPA.HV L ar) (PEC.en_k en)))).
  { unfold PMSPA.scA, PEC.pot_estack, PEC.ESZ, PMSPA.HV, LibIfaceAB.heap_view. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead]. rewrite KPM, BOV, BLIN.
    assert (P2 : 2 ^ PEC.en_k en <= 2 ^ 12) by (apply Z.pow_le_mono_r; clear - EKq'; lia). clear - EKq' P2. split; nia. }
  unfold PENTBA.ntb_specA in NTB.
  apply (NTB PMODE fxq Rq Mq mdq K LBY FF LKq Awq crq (ov + 8) osk (sp - FR) ra0 h kq HHY AMq K0); clear NTB.
  {
    split; [rewrite L5K.rl1; exact Q1|]. split; [exact RA0|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 2) with 16384. change (16384 / 8) with 2048. split.
    - apply (L5SAR.astk_sub ar Mq Mq sp 20480 FR 16384 ASTKq); [intros w D; exact D| clear - HFR; lia| clear; lia| clear - HFR; lia| exact SPF16].
    - apply (PMKA.shadow_zero_sub Mq (sp - 20480) 2560); [apply SPd8; reflexivity| | clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZq].
      replace (sp - FR - 16384) with (sp - (FR + 16384)) by lia. apply SPd8. clear - HFR; destruct HFR as [-> | [-> | [-> | ->]]]; reflexivity. }
  { apply (ffroomA_mono 4 2 FF LK LKq FRM ILKq NDFq). clear; lia. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS HFR; lia. }
  { exact SPF16. }
  { rewrite L5K.rl11. exact Q11. }
  { exact EV8. }
  { exact Q8v. }
  { apply AOF; clear - Eov; lia. }
  { intros x Hx. apply EACC. clear - Hx; lia. }
  { left. clear - Eov Eosk; lia. }
  { exact SKAq. }
  { exact AOSK. }
  { exact K8. }
  { exact HBh. }
  { clear - CLq Ha; lia. }
  { unfold PMSP.credit_le, PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CRED, CKq |- *. cbn [fst snd] in CRED, CKq |- *. clear - CRED CKq PEN. lia. }
  intros fx2 R2 M2 md2 LK2 Aw2 cr2 k2 RP2 ZK2 SKA2 HP2 CK2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 2) with 16384 in HP2.

  assert (OWs : forall a0, sp - 20480 <= a0 < sp -> L5.outside Ws a0).
  { intros a0 Ha0 r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk. clear - Ha0 K2 SLO; lia. }
  assert (FRAME12 : forall a0, sp - FR <= a0 < sp -> M2 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT HFR; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT HFR; lia| intros Y; clear - Ha0 Y; lia].
    - apply OWs. clear - Ha0 HFR; lia. }
  assert (EK12 : L5SAR.ek L ar LBY FF sp 20480 Ws Mq M2).
  { apply (L5SAR.ek_callee L ar LBY [] FF [] sp 20480 (sp - FR) 16384 Ws Ws Mq M2 HP2); [clear - HFR; lia| clear - HFR; lia| intros a0 _ O; exact O]. }
  assert (DK12 : L5SAR.dk L ar LBY FF sp 20480 Mq M2) by (apply (L5SAR.dk_callee L ar LBY [] FF [] sp 20480 (sp - FR) 16384 Ws Mq M2 HP2); clear - HFR; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480).
  { apply (PMKA.astk_after_ahpres L ar LBY FF Mq M2 sp 20480 (sp - FR) 16384 Ws ASTKq HP2); [clear - HFR; lia| clear - HFR; lia| clear; lia| exact STOP]. }
  pose proof ws_wapp as WAPP.
  assert (SZ2 : shadow_zero M2 (sp - 20480) 2560).
  { apply (PMKA.stksh_keepA L ar LBY FF sp 20480 Ws Mq M2 EK12 WAPP (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZq]. }
  assert (OUTO : forall a1 m, (a1 + m <= osk \/ osk + 24 <= a1) -> forall i, a1 <= i < a1 + m -> L5.outside Ws i).
  { intros a1 m Xa i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk. clear - Xa Hi; lia. }
  assert (OUTBY : forall q m, In (q, m) LBY -> PMKA.blk_out Ws q m).
  { intros q m Hq. destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m osk 24 HHY (in_or_app _ _ _ (or_intror Hq)) AOSK) as [Xa|Xa];
      (intros i Hi; apply (OUTO q m); [clear - Xa; lia| exact Hi]). }
  apply (KX fx2 R2 M2 md2 LK2 Aw2 cr2 k2); [| exact RP2].
  unfold inv. split; [exact (FC_frame Mq M2 FRAME12 FCq)|]. split; [exact ASTK2|]. split; [exact SZ2|].
  split; [exact (L5LZ.model_rt_trans model mdq md2 MRTq MRT2)|]. split; [exact AM2|].
  split; [intros x Hx; apply ILKq; apply ILK2; exact Hx|]. split; [intros x Hx; apply IAW2; apply IAWq; exact Hx|].
  split; [refine (ri_perm _ _ FF LK2 cr2 Aw2 M2 _ _ HH2); unfold PEC.owned, LBY; rewrite <- !app_assoc; apply Permutation_sym; apply PEEK.perm4|].
  split.
  { apply (PECFA.enc_keepA RSEGS EE L ar LBY FF sp 20480 Ws Mq M2 EK12 WAPP FRBq BRBY ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [| exact EINCq| | exact EAq].
    - apply OUTO. clear - Eov Eosk; lia.
    - intros Hp. apply OUTBY. apply EINCq. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
  split; [exact SKA2|].
  split; [clear - CLq ZK2 KB0; lia|].
  split; [exact (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mq M2 EKq (PMKA.ek_sublb L ar LBY LBc0 FF sp 20480 Ws Mq M2 XINCq EK12))|].
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M2 DKq (PMKA.dk_sublb L ar LBY LBc0 FF sp 20480 Mq M2 XINCq DK12))|].
  unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CKq, CK2 |- *. cbn [fst snd] in CKq, CK2 |- *. clear - CKq CK2. lia.
Qed.

Lemma inv_frame Mi Mj mdi mdj LKi Awi cri ki a lo hi : inv Mi mdi LKi Awi cri ki a -> sp - FR <= lo -> hi <= sp ->
  mem_grows Mi Mj -> (forall i, 0 <= i < 2 ^ 64 -> ~ (lo <= i < hi) -> Mj (Z_to_bv 64 i) = Mi (Z_to_bv 64 i)) -> FC Mj ->
  ri_inv HI (PEC.owned s en ki ++ LBX) FF LKi cri Awi Mj (vml_of mdj) -> L5CA.amodel_ok Awi mdj -> model_rt mdi mdj ->
  inv Mj mdj LKi Awi cri ki a.
Proof.
  intros INV Hlo Hhi MG FRZ FCj HHj AMj MRTj. entry_facts. name_objs.
  pose proof INV as (FCi & ASTKi & SZi & MRTi & AMi & ILKi & IAWi & HHi & EAi & SKAi & CLi & EKi & DKi & CKi).
  set (LBi := PEC.owned s en ki ++ LBX) in *.
  assert (EK1 : L5SAR.ek L ar LBi FF sp 20480 [] Mi Mj).
  { apply (PMKA.ek_own_frame L ar C HI LYa HIok LBi FF LKi cri Awi Mi Mj _ sp 20480 [] lo hi HHi SPT); [clear - Hlo SLO HFR; lia| clear - Hlo HFR; lia| exact Hhi| exact FRZ]. }
  assert (BRBi : forall x, In x LBi -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi).
  assert (FRBi : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHi).
  assert (INC0 : incl LBc0 LBi) by (unfold LBc0, LBi, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (EINC : incl (PEC.enc_own en) LBi) by (unfold LBi, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (KINC : incl (PESK.sink_own ki) LBi) by (unfold LBi, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  unfold inv. split; [exact FCj|]. split; [exact (L5SAR.astk_grows ar Mi Mj sp 20480 ASTKi MG)|].
  split; [apply (PMKA.stksh_keepA L ar LBi FF sp 20480 [] Mi Mj EK1 PMKA.wapp_nil (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZi]|].
  split; [exact (L5LZ.model_rt_trans model mdi mdj MRTi MRTj)|]. split; [exact AMj|]. split; [exact ILKi|]. split; [exact IAWi|]. split; [exact HHj|].
  split; [apply (PECFA.enc_keepA RSEGS EE L ar LBi FF sp 20480 [] Mi Mj EK1 PMKA.wapp_nil FRBi BRBi ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact EINC| intros _ i _ r0 []| exact EAi]|].
  split; [apply (PECFA.sink_keepA RSEGS L ar LBi FF sp 20480 [] Mi Mj EK1 PMKA.wapp_nil FRBi BRBi P osk ki (AOF osk 24 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact KINC| intros _ i _ r0 []| exact SKAi]|].
  split; [exact CLi|].
  split; [apply (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mi Mj EKi); apply (L5SAR.ek_W L ar LBc0 FF sp 20480 Ws [] Mi Mj); [exact (PMKA.ek_sublb L ar LBi LBc0 FF sp 20480 [] Mi Mj INC0 EK1)| intros a0 _ r0 []]|].
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mi Mj DKi (L5SAR.dk_grows L ar LBc0 FF sp 20480 Mi Mj MG))| exact CKi].
Qed.

Local Ltac cut_facts INV kq :=
  pose proof INV as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq);
  pose proof AMq as (Mhq & MIq); pose proof ASTKq as (A16q & SLOq & SHIq & SPTq & SDEFq & SUPq);
  set (LBq := PEC.owned s en kq ++ LBX) in HHq.

Lemma vis_facts Mq mdq LKq Awq crq kq a : inv Mq mdq LKq Awq crq kq a ->
  let H := ahid Awq mdq in let MV := mrestrict H Mq in let ov := PMSPA.o_v AD fb in let osk := PESK.o_sink EE fb in
  L5.img_clear MV 1253376 1286144 /\ L5.u64_at RSEGS MV 1317368 SBL /\ L5.u32_at RSEGS MV 1317376 1
  /\ 140735332487168 + 20480 <= sp <= 140737488355328 /\ sp mod 16 = 0 /\ L5.writable RSEGS MV (sp - FR) FR
  /\ 4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at MV (ov / 8 + SBL) 7
  /\ L5.writable RSEGS MV ov 56 /\ ((sp - FR) + FR <= ov \/ ov + 56 <= (sp - FR))
  /\ L5KA.zeros_at MV ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at MV ((ov + 24) / 8 + SBL) 1 /\ L5KA.zeros_at MV ((ov + 32) / 8 + SBL) 1
  /\ L5.u64_at RSEGS MV (ov + 8) osk /\ 4096 <= osk <= 140737488355304 /\ osk mod 8 = 0 /\ osk + 24 <= ov
  /\ L5.u64_at RSEGS MV (ov + 24) (PEC.en_b en) /\ L5.u64_at RSEGS MV (ov + 32) (PEC.en_b en + 24 * Z.of_nat (length (PEC.en_stk en))) /\ 0 <= PEC.en_b en <= 2 ^ 47
  /\ (forall a0 v, sp - FR <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS Mq a0 v -> L5.u64_at RSEGS MV a0 v) /\ FC Mq.
Proof.
  intros INV. entry_facts. name_objs. cut_facts INV kq.
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq HHq) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _).
  set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKA.aobj_of_aobjA FF ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2' & Q3 & Q4 & Q5) & QBIG & QDEF & QVIS & QSHV & QCL & QSHCL).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKA.aobj_of_aobjA FF osk 24 (AOF osk 24 ltac:(lia) ltac:(lia)) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C Mq LYa ST) as (GOT & CSB & CUAR & _).
  assert (CVv : forall a0 m0, ov <= a0 -> a0 + m0 <= ov + 56 -> L5A.avis H a0 m0) by (intros a0 m0 X1 X2; eapply L5A.avis_sub; [exact QVIS| lia| lia]).
  pose proof EAq as (EV0 & EV8 & EV16 & EV24 & EV32 & EV40 & EV48 & EDEF & EACC & EK & ELEN & EDEP & EKB & EBLK & _). fold osk in EV8. unfold PEC.ESZ in EV32.
  pose proof (PEC.ecap_nonneg (PEC.en_k en)) as CN.
  pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq ov 56 HHq (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m ltac:(lia) ltac:(reflexivity) EACC) as Zov.
  unfold SB in Zov. change (56 / 8) with 7 in Zov. fold H MV in Zov.
  assert (D8 : forall j, (ov + 8 * j) / 8 = ov / 8 + j).
  { intros j. rewrite <- Q5 at 1. replace (ov / 8 * 8 + 8 * j) with ((ov / 8 + j) * 8) by lia. apply Z.div_mul. clear; lia. }
  assert (ZG : forall j, 0 <= j < 7 -> L5KA.zeros_at MV ((ov + 8 * j) / 8 + SBL) 1).
  { intros j Hj. rewrite D8. intros i Hi. replace (ov / 8 + j + SBL + i) with (ov / 8 + SBL + (j + i)) by lia. apply Zov. lia. }
  pose proof (ZG 1 ltac:(lia)) as Z8. pose proof (ZG 3 ltac:(lia)) as Z24. pose proof (ZG 4 ltac:(lia)) as Z32.
  replace (ov + 8 * 1) with (ov + 8) in Z8 by lia. replace (ov + 8 * 3) with (ov + 24) in Z24 by lia. replace (ov + 8 * 4) with (ov + 32) in Z32 by lia.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LKq crq Awq Mq mdq sp 20480 FR HHq ASTKq ltac:(clear - HFR; lia)) as (_ & _ & SWR).
  assert (EB : 0 <= PEC.en_b en <= 2 ^ 47).
  { destruct (Z.eq_dec (PEC.en_k en) 0) as [Z0|NZ]; [rewrite (EKB Z0); clear; lia|]. destruct (EBLK ltac:(lia)) as (_ & _ & BR0 & _). destruct BR0 as (X1 & _ & _ & _ & X5 & _). unfold PEC.ESZ in X5. clear - X1 X5 SPT CN; lia. }
  split; [apply L5A.img_clear_mrestrict; exact GOT|].
  split; [apply (proj2 (L5A.u64_at_vis H Mq 1317368 SBL (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB|].
  split; [apply (proj2 (L5A.u32_at_vis H Mq 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR|].
  split; [clear - SLO SHI SPT; lia|]. split; [exact A16'|]. split; [exact SWR|].
  split; [clear - Q1 Q3; lia|]. split; [exact Q8m|]. split; [exact QBIG|]. split; [exact Zov|].
  split; [apply (proj2 (L5A.writable_vis H Mq ov 56 QVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact QDEF| lia| lia]|].
  split; [clear - Q2' SLO HFR; lia|]. split; [exact Z8|]. split; [exact Z24|]. split; [exact Z32|].
  split; [apply (proj2 (L5A.u64_at_vis H Mq (ov + 8) osk (CVv (ov + 8) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV8|].
  split; [clear - K1 K3; lia|]. split; [exact K8|]. split; [clear - Eov Eosk; lia|].
  split; [apply (proj2 (L5A.u64_at_vis H Mq (ov + 24) _ (CVv (ov + 24) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV24|].
  split; [apply (proj2 (L5A.u64_at_vis H Mq (ov + 32) _ (CVv (ov + 32) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV32|].
  split; [exact EB|].
  split; [| exact FCq].
  intros a0 v Ha1 Ha2 U. apply (proj2 (L5A.u64_at_vis H Mq a0 v (VIS a0 8 ltac:(clear - Ha1 SLO HFR; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO SPT HFR; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact U.
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
  /\ (forall n, eb <= ed - 24 -> L5A.avis H (ed - 8) n -> True).
Proof.
  intros INV HXS. entry_facts. name_objs. cut_facts INV kq.
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (_ & _ & _ & _ & _ & Lestk & _). cbn [s_estk X] in Lestk.
  destruct MP as (_ & _ & FA & _). cbn [s_estk X] in FA. rewrite HXS in FA, Lestk.
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq HHq) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _).
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
  assert (BINq : In (eb, 24 * PEC.ecap ek) LBq).
  { unfold LBq, PEC.owned. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact BINe. }
  pose proof (EITEMS (length rr) ltac:(clear; lia)) as TOP. rewrite Lestk in TOP. cbn [rev] in TOP. rewrite PEEK.nth_top in TOP. fold m in TOP.
  destruct TOP as (TK & TL & TC).
  assert (E1OK : ei_ok e1) by (inversion FA; assumption). pose proof E1OK as (_ & E1C & _). unfold TWO64 in E1C.
  set (ed := eb + 24 * (m + 1)).
  assert (ALend : ed mod 8 = 0) by (unfold ed; apply PEEK.al8_item; exact EBAL).
  replace (eb + 24 * m + 16) with (ed - 8) in TC by (unfold ed; clear; lia).
  assert (OVA : eb + 24 * PEC.ecap ek <= ov \/ ov + 56 <= eb) by exact (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ eb (24 * PEC.ecap ek) ov 56 HHq BINq (AOF ov 56 ltac:(lia) ltac:(lia))).
  assert (BV : forall a0 n0, eb <= a0 -> a0 + n0 <= eb + 24 * PEC.ecap ek -> L5A.avis H a0 n0) by (intros a0 n0 X1 X2; exact (VBLK eb (24 * PEC.ecap ek) a0 n0 BINq X1 X2)).
  assert (AL8 : (ed - 8) mod 8 = 0) by (replace (ed - 8) with (ed + (-1) * 8) by lia; rewrite Z_mod_plus_full; exact ALend).
  assert (ACC8 : PMSPA.accA Mq (ed - 8) 8) by (intros x Hx; apply EBACC; unfold ed in Hx; clear - Hx M0; lia).
  pose proof (PMKA.blk_shadow_vis L ar C HI LYa HIok LBq FF LKq crq Awq Mq mdq eb (24 * PEC.ecap ek) (ed - 8) 8 HHq BINq ltac:(unfold ed; lia) ltac:(unfold ed; lia) AL8
                ltac:(clear; lia) ltac:(reflexivity) ACC8) as ZC.
  unfold SB in ZC. change (8 / 8) with 1 in ZC. fold H MV in ZC.
  split; [rewrite HLEN, Nat2Z.inj_succ; unfold m; clear; lia|]. split; [exact EKP|].
  split; [exact EB1|]. split; [unfold ed; clear - EB5 SPT M0 ELEN; lia|]. split; [exact ALend|]. split; [unfold ed; clear - M0 ELEN ECAPB; lia|].
  split.
  { apply (proj2 (L5A.writable_vis H Mq (ed - 24) 24 (BV (ed - 24) 24 ltac:(unfold ed; lia) ltac:(unfold ed; lia)) ltac:(unfold ed; lia) ltac:(unfold ed; lia))).
    apply (L5.writable_sub _ Mq eb (24 * PEC.ecap ek)); [apply (L5C.writable_of_defined RSEGS); [exact EBDEF| lia| lia]| unfold ed; lia| unfold ed; lia]. }
  split; [unfold ed; clear - EB6 M0 ELEN; lia|]. split; [exact ZC|].
  split; [unfold ed; clear - EB5 SLO M0 ELEN HFR; lia|]. split; [unfold ed; clear - OVA M0 ELEN; lia|].
  split; [apply (proj2 (L5A.u64_at_vis H Mq (ed - 8) _ (BV (ed - 8) 8 ltac:(unfold ed; lia) ltac:(unfold ed; lia)) ltac:(unfold ed; lia) ltac:(unfold ed; lia))); exact TC|].
  split; [exact E1C|]. split; [exact E1OK|]. split; [exact BINe|]. split; [unfold ed; clear - ELEN; lia|]. split; [clear - EB5 SPT; lia|].
  intros; exact I.
Qed.

Lemma finish_ro a pcq (fxq : FPState) Rq Mq mdq LKq Awq crq kq (fx3 : FPState) R3 M3v :
  inv Mq mdq LKq Awq crq kq a -> xestk = [] -> a = NB ->
  msteps RSEGS (mst fxq Rq pcq (mrestrict (ahid Awq mdq) Mq)) (mst fx3 R3 r M3v) -> mem_grows (mrestrict (ahid Awq mdq) Mq) M3v ->
  (forall i, 0 <= i < 2 ^ 64 -> M3v (Z_to_bv 64 i) = mrestrict (ahid Awq mdq) Mq (Z_to_bv 64 i)) -> regs_preserved R R3 ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcq Mq mdq) K.
Proof.
  intros INV HXS Ha MS3 MG3 FRZ3 RP3. entry_facts. name_objs. cut_facts INV kq.
  pose proof KONT as KT. unfold e_end_value in KT. cbn [s_estk XS] in KT. rewrite HXS in KT.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LBq FF LKq crq Awq Mq mdq fxq fx3 Rq pcq R3 r M3v K HHq AMq MS3 MG3 FRZ3).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 AG3. pose proof (L5SAR.mem_eq_of_agree Mq M3 AG3) as EM. subst M3.
  apply (KT fx3 R3 Mq md3 LKq Awq en kq e crq).
  - exact RP3.
  - subst a. exact (inv_cpre Mq mdq LKq Awq crq kq NB _ _ INV eq_refl eq_refl).
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

Lemma finish_bump a pcq (fxq : FPState) Rq Mq mdq LKq Awq crq kq (fx3 : FPState) R3 M3v e1 rr :
  inv Mq mdq LKq Awq crq kq a -> xestk = e1 :: rr -> a = NB ->
  let ed := PEC.en_b en + 24 * (Z.of_nat (length rr) + 1) in
  msteps RSEGS (mst fxq Rq pcq (mrestrict (ahid Awq mdq) Mq)) (mst fx3 R3 r M3v) -> mem_grows (mrestrict (ahid Awq mdq) Mq) M3v ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (ed - 8 <= i < ed - 8 + 8) -> M3v (Z_to_bv 64 i) = mrestrict (ahid Awq mdq) Mq (Z_to_bv 64 i)) ->
  L5.u64_at RSEGS M3v (ed - 8) ((ei_cnt e1 + 1) mod 2 ^ 64) -> regs_preserved R R3 ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcq Mq mdq) K.
Proof.
  intros INV HXS Ha ed MS3 MG3 FRZ3 C8 RP3. entry_facts. name_objs. cut_facts INV kq.
  destruct (vis_facts_top Mq mdq LKq Awq crq kq a e1 rr INV HXS) as (HLEN & EKP & EB1 & ED2 & ALend & ED3 & _ & EB6 & _ & EDS & OVA & _ & E1C & E1OK & BINe & EDC & EBC & _).
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & TBOK & _ & CL & _ & ECI & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad X] in Lmore, Ldone, Ldepth, Lstk, Lpos, Lestk, Ledepth, Lz, Lbad. rewrite HXS in Lestk.
  pose proof KONT as KT. unfold e_end_value in KT. cbn [s_estk XS] in KT. rewrite HXS in KT.
  assert (EN : en = PEC.ENC (PEC.en_b en) (PEC.en_k en) (PEC.en_stk en) (PEC.en_depth en)) by (destruct en; reflexivity).
  pose proof EAq as EAq'. rewrite EN in EAq'.
  set (eb := PEC.en_b en) in *. set (ek := PEC.en_k en) in *. set (estk := PEC.en_stk en) in *. set (edepth := PEC.en_depth en) in *.
  cbn [PEC.en_stk PEC.en_depth] in Lestk, Ledepth.
  set (m := Z.of_nat (length rr)) in *. assert (M0 : 0 <= m) by (unfold m; clear; lia).
  destruct e1 as [kd ln cn]. cbn [ei_kind ei_len ei_cnt] in C8, E1C, KT.
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq HHq) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _).
  set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKA.aobj_of_aobjA FF ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2' & Q3 & Q4 & Q5) & _).
  assert (BINq : In (eb, 24 * PEC.ecap ek) LBq).
  { unfold LBq, PEC.owned. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact BINe. }
  assert (BV : forall a0 n0, eb <= a0 -> a0 + n0 <= eb + 24 * PEC.ecap ek -> L5A.avis H a0 n0) by (intros a0 n0 X1 X2; exact (VBLK eb (24 * PEC.ecap ek) a0 n0 BINq X1 X2)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LBq FF LKq crq Awq Mq mdq fxq fx3 Rq pcq R3 r M3v (fun a0 => ed - 8 <= a0 < ed - 8 + 8) K HHq AMq MS3 MG3).
  { intros a0 Ha0 Hn. apply FRZ3; [exact Ha0| exact Hn]. }
  { intros a0 Ha0 Wa. split.
    - unfold aclientw, aclient_g. left. exists (eb, 24 * PEC.ecap ek). split; [exact BINq|]. cbn [fst snd]. unfold ed in Wa. clear - Wa M0 EDC; lia.
    - unfold ed in Wa. pose proof EAq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EBLK & _). destruct (EBLK EKP) as (_ & _ & (_ & EB2 & _) & _).
      rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in EB2. unfold PEC.ESZ in EB2. fold eb ek in EB2. clear - Wa M0 EDC EBC EB1 EB2. lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H M3 = M3v) in VIS3.
  assert (C8' : L5.u64_at RSEGS M3 (ed - 8) ((cn + 1) mod 2 ^ 64)).
  { apply (proj1 (L5A.u64_at_vis H M3 (ed - 8) _ (BV (ed - 8) 8 ltac:(unfold ed; lia) ltac:(unfold ed; lia)) ltac:(unfold ed; lia) ltac:(unfold ed; lia))). rewrite VIS3. exact C8. }

  set (LBr := PESK.sink_own kq ++ LBc0).
  assert (PERMr : Permutation LBq (PEC.enc_own en ++ LBr)).
  { unfold LBq, LBr, LBc0, PEC.owned. rewrite <- !app_assoc. etransitivity; [apply Permutation_app_swap_app|]. apply Permutation_app_head. apply Permutation_app_swap_app. }
  pose proof (ri_perm _ _ FF LKq crq Awq Mq _ PERMr HHq) as HHr.
  assert (EK23r : L5SAR.ek L ar LBr FF sp 20480 [] Mq M3).
  { apply (L5SAR.ek_piece L ar LBr FF sp 20480 [] Mq M3 (fun a0 => ed - 8 <= a0 < ed - 8 + 8) FR3).
    intros a0 Ha0 Hc _ Xa. exact (PMARS1.own_not_aclient L ar C HI HIok (PEC.enc_own en) LBr FF LKq crq Awq Mq _ eb (24 * PEC.ecap ek) a0 sp 20480 HHr BINe ltac:(unfold ed in Xa; clear - Xa M0 EDC; lia) Hc). }
  assert (INCr : incl LBc0 LBr) by (unfold LBr; apply incl_appr; apply incl_refl).
  assert (EK23 : L5SAR.ek L ar LBc0 FF sp 20480 Ws Mq M3).
  { apply (L5SAR.ek_W L ar LBc0 FF sp 20480 Ws [] Mq M3); [exact (PMKA.ek_sublb L ar LBr LBc0 FF sp 20480 [] Mq M3 INCr EK23r)| intros a0 _ r0 []]. }
  pose proof (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mq M3 EKq EK23) as EKT.
  assert (DK23 : L5SAR.dk L ar LBc0 FF sp 20480 Mq M3) by (apply L5SAR.dk_grows; exact MGM3).
  assert (SHM3 : forall a0 n0, 0 <= a0 -> a0 + n0 <= 2 ^ 47 -> PMFA.agsh Mq M3 a0 n0).
  { intros a0 n0 Ha0 Hn0 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
    apply FR3; [clear - SX; lia| intros Y; unfold ed in Y; clear - Y SX EB6 M0; lia]. }
  assert (BRBr : forall x, In x LBr -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
  { intros x Hx. apply (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHr). apply in_or_app. right. exact Hx. }
  assert (FRBq : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
  assert (EA3 : PECA.enc_atA RSEGS EE L ar M3 ov fb (PEC.ENC eb ek (rev (PEEK.ebump (EI kd ln cn :: rr))) edepth)).
  { apply (enc_bumpA Mq M3 ov fb eb ek (EI kd ln cn :: rr) edepth); [rewrite <- Lestk; exact EAq'| lia| lia| intros _; unfold PEC.ESZ; clear - EB1 EBC; lia| | | | exact MGM3|].
    - split; [| apply SHM3; clear - Q1 Q3; lia]. intros i Hi. apply FR3; [clear - Hi Q1 Q3; lia|]. intros Y. unfold ed in Y. clear - Y Hi OVA M0. lia.
    - intros _ i Hi Ri Ni. apply FR3; [exact Hi|]. cbn [PEEK.cc_rng length] in Ni. fold m in Ni. unfold PEC.ESZ in Ni. unfold ed. clear - Ni. lia.
    - intros _. apply SHM3; unfold PEC.ESZ; clear - EB1 EBC; lia.
    - intros e2 rr' Hc. injection Hc as <- <-. cbn [ei_cnt]. fold m. unfold PEC.ESZ, TWO64. replace (eb + 24 * m + 16) with (ed - 8) by (unfold ed; clear; lia). exact C8'. }
  cbn [PEEK.ebump ei_kind ei_len ei_cnt] in EA3.
  assert (SKA3 : PESKA.sink_atA RSEGS L ar P M3 osk kq).
  { apply (PECFA.sink_keepA RSEGS L ar LBr FF sp 20480 [] Mq M3 EK23r PMKA.wapp_nil FRBq BRBr P osk kq (AOF osk 24 ltac:(lia) ltac:(lia))); [intros i _ r0 []| | intros _ i _ r0 []| exact SKAq].
    unfold LBr. apply incl_appl. apply incl_refl. }
  assert (ASTK3 : L5CA.astk ar M3 sp 20480) by exact (L5SAR.astk_grows ar Mq M3 sp 20480 ASTKq MGM3).
  pose proof ASTK3 as (_ & _ & _ & _ & SDEF3 & _).
  destruct (keepf M3 EKT) as (PA3 & IA3 & VREF3 & BASE3 & ERR3 & CONT3 & ECS3 & ACC3).
  apply (KT fx3 R3 M3 md3 LKq Awq (PEC.ENC eb ek (rev rr ++ [EI kd ln ((cn + 1) mod TWO64)]) edepth) kq e crq).
  + exact RP3.
  + unfold PECA.crun_preA. fold op ov ois osk.
    split; [exact PA3|]. split; [exact IA3|]. split; [unfold TWO64; exact EA3|]. split; [exact VREF3|]. split; [exact SKA3|].
    split; [exact BASE3|]. split; [exact ERR3|]. split; [exact TBOK|]. split; [exact CONT3|].
    split.
    { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PEC.en_stk PEC.en_depth rev w_estk XS].
      split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
      split; [reflexivity|]. split; [exact Ledepth|]. split; [subst a; clear - CLq; lia| exact Lbad]. }
    cbn [s_ec w_estk XS]. split; [exact ECS3|]. split; [exact ECI| exact ACC3].
  + intros E1; exact E1.
  + change (PMSPA.pm_scr 4) with 20480. apply (L5SAR.ahpres_of L ar LBc0 FF sp 20480 _ M M3); [| exact SDEF3| exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M3 DKq DK23)].
    apply (L5SAR.ek_W L ar LBc0 FF sp 20480 _ Ws M M3 EKT). exact ws_wenc.
  + unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CKq |- *. cbn [fst snd PEC.en_k] in CKq |- *. change (PEC.en_k en) with ek in CKq |- *. clear - CKq. lia.
  + exact (L5LZ.model_rt_trans model mdq md3 MRTq MRT3).
  + exact ILKq.
  + exact IAWq.
  + exact AM3.
  + exact HH3.
Qed.

Lemma vis_entry :
  let H := ahid Aw model in let MV := mrestrict H M in let ov := PMSPA.o_v AD fb in let osk := PESK.o_sink EE fb in
  L5.img_clear MV 1253376 1286144 /\ L5.u64_at RSEGS MV 1317368 SBL /\ L5.u32_at RSEGS MV 1317376 1
  /\ 140735332487168 + 20480 <= sp <= 140737488355328 /\ sp mod 16 = 0 /\ L5.writable RSEGS MV (sp - FR) FR
  /\ 4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at MV (ov / 8 + SBL) 7
  /\ L5.writable RSEGS MV ov 56 /\ ((sp - FR) + FR <= ov \/ ov + 56 <= (sp - FR))
  /\ L5KA.zeros_at MV ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at MV ((ov + 24) / 8 + SBL) 1 /\ L5KA.zeros_at MV ((ov + 32) / 8 + SBL) 1
  /\ L5.u64_at RSEGS MV (ov + 8) osk /\ 4096 <= osk <= 140737488355304 /\ osk mod 8 = 0 /\ osk + 24 <= ov
  /\ getr R (reg 2) = Z_to_bv 64 sp /\ getr R (reg 10) = Z_to_bv 64 ov /\ getr R (reg 1) = Z_to_bv 64 r /\ L5.ra_ok r
  /\ (forall M1 a0 v, sp - FR <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS (mrestrict H M1) a0 v -> L5.u64_at RSEGS M1 a0 v).
Proof.
  entry_facts. name_objs.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 sp 20480 HH (PMKA.aobj_of_aobjA FF ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2' & Q3 & Q4 & Q5) & QBIG & QDEF & QVIS & QSHV & QCL & QSHCL).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model osk 24 sp 20480 HH (PMKA.aobj_of_aobjA FF osk 24 (AOF osk 24 ltac:(lia) ltac:(lia)) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & _) & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (CVv : forall a0 m0, ov <= a0 -> a0 + m0 <= ov + 56 -> L5A.avis H a0 m0) by (intros a0 m0 X1 X2; eapply L5A.avis_sub; [exact QVIS| lia| lia]).
  pose proof EA as (_ & EV8 & _ & _ & _ & _ & _ & EDEF & EACC & _). fold osk in EV8.
  pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 HH (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m ltac:(lia) ltac:(reflexivity) EACC) as Zov.
  unfold SB in Zov. change (56 / 8) with 7 in Zov. fold H MV in Zov.
  assert (D8 : forall j, (ov + 8 * j) / 8 = ov / 8 + j).
  { intros j. rewrite <- Q5 at 1. replace (ov / 8 * 8 + 8 * j) with ((ov / 8 + j) * 8) by lia. apply Z.div_mul. clear; lia. }
  assert (ZG : forall j, 0 <= j < 7 -> L5KA.zeros_at MV ((ov + 8 * j) / 8 + SBL) 1).
  { intros j Hj. rewrite D8. intros i Hi. replace (ov / 8 + j + SBL + i) with (ov / 8 + SBL + (j + i)) by lia. apply Zov. lia. }
  pose proof (ZG 1 ltac:(lia)) as Z8. pose proof (ZG 3 ltac:(lia)) as Z24. pose proof (ZG 4 ltac:(lia)) as Z32.
  replace (ov + 8 * 1) with (ov + 8) in Z8 by lia. replace (ov + 8 * 3) with (ov + 24) in Z24 by lia. replace (ov + 8 * 4) with (ov + 32) in Z32 by lia.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 20480 FR HH ASTK ltac:(clear - HFR; lia)) as (_ & _ & SWR).
  pose proof A10 as B10. rewrite L5K.rl10 in B10.
  split; [apply L5A.img_clear_mrestrict; exact GOT|].
  split; [apply (proj2 (L5A.u64_at_vis H M 1317368 SBL (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB|].
  split; [apply (proj2 (L5A.u32_at_vis H M 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR|].
  split; [clear - SLO SHI SPT; lia|]. split; [exact A16'|]. split; [exact SWR|].
  split; [clear - Q1 Q3; lia|]. split; [exact Q8m|]. split; [exact QBIG|]. split; [exact Zov|].
  split; [apply (proj2 (L5A.writable_vis H M ov 56 QVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact QDEF| lia| lia]|].
  split; [clear - Q2' SLO HFR; lia|]. split; [exact Z8|]. split; [exact Z24|]. split; [exact Z32|].
  split; [apply (proj2 (L5A.u64_at_vis H M (ov + 8) osk (CVv (ov + 8) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV8|].
  split; [clear - K1 K3; lia|]. split; [exact K8|]. split; [clear - Eov Eosk; lia|].
  split; [exact Rsp|]. split; [exact B10|]. split; [exact Rra|]. split; [exact RAok|].
  intros M1 a0 v Ha1 Ha2 U. apply (proj1 (L5A.u64_at_vis H M1 a0 v (VIS a0 8 ltac:(clear - Ha1 SLO HFR; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO SPT HFR; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact U.
Qed.

Lemma inv_start M1 md1 : mem_grows M M1 -> (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - FR <= i < sp - FR + FR) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> FC M1 ->
  ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M1 (vml_of md1) -> L5CA.amodel_ok Aw md1 -> model_rt model md1 -> inv M1 md1 LK Aw cr k 0.
Proof.
  intros MG FR1 FC1 HH1 AM1 MRT1. entry_facts. name_objs.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad). cbn [s_lo s_hi X] in Lz.
  assert (EK01n : L5SAR.ek L ar LB FF sp 20480 [] M M1).
  { apply (PMKA.ek_own_frame L ar C HI LYa HIok LB FF LK cr Aw M M1 _ sp 20480 [] (sp - FR) (sp - FR + FR) HH SPT); [clear - SLO HFR; lia| clear - HFR; lia| clear; lia| exact FR1]. }
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (EINC : incl (PEC.enc_own en) LB) by (unfold LB, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (KINC : incl (PESK.sink_own k) LB) by (unfold LB, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  unfold inv. split; [exact FC1|]. split; [exact (L5SAR.astk_grows ar M M1 sp 20480 ASTK MG)|].
  split; [apply (PMKA.stksh_keepA L ar LB FF sp 20480 [] M M1 EK01n PMKA.wapp_nil (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact STKSH]|].
  split; [exact MRT1|]. split; [exact AM1|]. split; [apply incl_refl|]. split; [apply incl_refl|]. split; [exact HH1|].
  split; [apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp 20480 [] M M1 EK01n PMKA.wapp_nil FRB BRB ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact EINC| intros _ i _ r0 []| exact EA]|].
  split; [apply (PECFA.sink_keepA RSEGS L ar LB FF sp 20480 [] M M1 EK01n PMKA.wapp_nil FRB BRB P osk k (AOF osk 24 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact KINC| intros _ i _ r0 []| exact SKA]|].
  split; [clear - Lz; lia|].
  split; [apply (L5SAR.ek_W L ar LBc0 FF sp 20480 Ws [] M M1); [exact (PMKA.ek_sublb L ar LB LBc0 FF sp 20480 [] M M1 INC0 EK01n)| intros a0 _ r0 []]|].
  split; [apply L5SAR.dk_grows; exact MG|]. unfold PMSP.credit_keep. clear. lia.
Qed.
End Call.
End WithHeap.
End PEAEKC.
