(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcRead1_b PnAReset1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PgTxtKitA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgV8A_b PgV8KitA_b PnRunA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGVWA1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation pot := (fun L ar (x : PGV8.v8) (g : Z) => PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) x g)).
Abbreviation v8_atA := (PGV8.v8_at RSEGS PMSPA.accA PGV8A.annA).

Lemma nodup_perm (l l' : list (Z * Z)) : Permutation l l' -> base.NoDup (map fst l) -> base.NoDup (map fst l').
Proof.
  intros P ND. apply NoDup_ListNoDup. apply NoDup_ListNoDup in ND.
  eapply Permutation_NoDup; [|exact ND]. apply Permutation_map. exact P.
Qed.
Lemma own2 (src : PM.srcst) (x : PGV8.v8) (OB LB : list (Z * Z)) : PM.src_own src ++ PGV8.v8_own x ++ OB ++ LB = (PM.src_own src ++ PGV8.v8_own x) ++ (OB ++ LB).
Proof. rewrite <- !app_assoc. reflexivity. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma perm_v8 (src : PM.srcst) (x : PGV8.v8) (OB LB : list (Z * Z)) FF LK cr Aw M V :
  ri_inv HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LB) FF LK cr Aw M V ->
  ri_inv HI (PGV8.v8_own x ++ (PM.src_own src ++ OB ++ LB)) FF LK cr Aw M V.
Proof.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
  apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF FF LK cr Aw M V HH).
  - intros b. rewrite !in_app_iff. tauto.
  - apply (nodup_perm (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LB)); [|exact ND].
    rewrite (app_assoc (PM.src_own src) (PGV8.v8_own x)). rewrite (app_assoc (PGV8.v8_own x) (PM.src_own src)).
    apply Permutation_app_tail. apply Permutation_app_comm.
  - intros f. tauto.
  - rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.
Lemma perm_v8_back (src : PM.srcst) (x : PGV8.v8) (OB LB : list (Z * Z)) FF LK cr Aw M V :
  ri_inv HI (PGV8.v8_own x ++ (PM.src_own src ++ OB ++ LB)) FF LK cr Aw M V ->
  ri_inv HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LB) FF LK cr Aw M V.
Proof.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
  apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF FF LK cr Aw M V HH).
  - intros b. rewrite !in_app_iff. tauto.
  - apply (nodup_perm (PGV8.v8_own x ++ (PM.src_own src ++ OB ++ LB))); [|exact ND].
    rewrite (app_assoc (PM.src_own src) (PGV8.v8_own x)). rewrite (app_assoc (PGV8.v8_own x) (PM.src_own src)).
    apply Permutation_app_tail. apply Permutation_app_comm.
  - intros f. tauto.
  - rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.

(* [comment removed for export] *)
Lemma ek_drop BX LB FF sp scr W M M' : L5SAR.ek L ar (BX ++ LB) FF sp scr W M M' -> L5SAR.ek L ar LB FF sp scr W M M'.
Proof. induction BX as [|b BX IH]; intros E; [exact E|]. apply IH. apply (L5SAR.ek_tl L ar (BX ++ LB) b FF sp scr W M M'). exact E. Qed.
Lemma dk_drop BX LB FF sp scr M M' : L5SAR.dk L ar (BX ++ LB) FF sp scr M M' -> L5SAR.dk L ar LB FF sp scr M M'.
Proof.
  intros D a Ha Hc HM. apply D; [exact Ha| |exact HM].
  apply L5SAR.aclient_appb. exact Hc.
Qed.

Section Call.
Variables (LBX : list (Z * Z)) (FF : list fframe) (T : PGV8.vowner) (OB : list (Z * Z)).
(* [comment removed for export] *)
Definition os : Z := PGV8.vw_os T.
Definition ois : Z := PGV8.vw_ois T.
Definition tb : Z := PGV8.vw_ov T.
Definition lo : Z := PGV8.vw_lo T.
Definition hi : Z := PGV8.vw_hi T.
Hypothesis TOK : PGV8A.vowner_ok RSEGS AD L ar HI T.
Hypothesis OFR : PGSA.ofr FF lo hi.
(* [comment removed for export] *)
Definition W0 : list L5.range := PGS.W_srcfG os ois ++ [(tb, 24)].
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lay : lo <= os /\ os + 296 <= hi /\ lo <= ois /\ ois + 272 <= hi /\ lo <= tb /\ tb + 24 <= hi /\ hi <= ar_sptop ar /\ hi <= 2 ^ 47
            /\ os mod 8 = 0 /\ ois mod 8 = 0 /\ tb mod 8 = 0 /\ 4096 <= lo
            /\ (os + 296 <= ois \/ ois + 272 <= os) /\ (tb + 24 <= os \/ os + 296 <= tb) /\ (tb + 24 <= ois \/ ois + 272 <= tb).
Proof using TOK. exact (PGV8A.vo_lay _ _ _ _ _ _ TOK). Qed.
Lemma tsrc M src x g : PGV8.vw_at T M src x g OB ->
  PM.src_fields_at RSEGS PMSPA.accA M os ois (ois + 16) src /\ PM.nullis_at RSEGS AD PMSPA.accA M (os + 8) /\ L5.defined M os 296
  /\ v8_atA M tb x /\ PGV8.v8_ok x g.
Proof using TOK. exact (PGV8A.vo_src _ _ _ _ _ _ TOK M src x g OB). Qed.
Lemma aobjs : PMSPA.aobjA FF os 296 /\ PMSPA.aobjA FF ois 272 /\ PMSPA.aobjA FF tb 24.
Proof using TOK OFR.
  pose proof lay as (L1 & L2 & L3 & L4 & L5' & L6 & _).
  split; [|split]; (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| lia| lia]).
Qed.
Lemma inW_W0 a : (exists r0, In r0 W0 /\ L5.in_rng r0 a) -> (os + 256 <= a < os + 296) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (tb <= a < tb + 24).
Proof.
  intros (r0 & Hin & Hr). unfold W0, PGS.W_srcfG in Hin. cbn [app] in Hin. unfold L5.in_rng in Hr.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma outside_W0 a : (a < lo \/ hi <= a) -> L5.outside W0 a.
Proof using TOK. intros Ha r0 Hr0 Hin. assert (I : exists r1, In r1 W0 /\ L5.in_rng r1 a) by (exists r0; split; assumption). apply inW_W0 in I. pose proof lay. lia. Qed.
(* [comment removed for export] *)
Lemma frame_app LB LK cr Aw M V : ri_inv HI LB FF LK cr Aw M V ->
  6905856 <= lo /\ hi <= 2 ^ 47 /\ (hi <= BIGSHADOW_LO \/ BIGSHADOW_HI <= lo) /\ lo <= hi /\ hi <= ahl_ceil ar.
Proof using TOK OFR HIok LY.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & FSCEIL & _).
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof OFR as (f & Hf & X1 & X2). destruct (WF _ Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in FSAPP, FSCEIL, Y2. pose proof lay. lia.
Qed.
Lemma wapp_W0 LB LK cr Aw M V : ri_inv HI LB FF LK cr Aw M V -> PMKA.wapp W0.
Proof using TOK OFR HIok LY.
  intros HH r0 Hr. destruct (frame_app _ _ _ _ _ _ HH) as (F1 & F2 & F3 & F4 & F5). pose proof lay.
  unfold W0, PGS.W_srcfG in Hr. cbn [app] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; (destruct F3; [left|right]; lia).
Qed.

(* [comment removed for export] *)
Lemma tw_side M (src : PM.srcst) (x : PGV8.v8) LK cr Aw V :
  ri_inv HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) FF LK cr Aw M V ->
  Forall (fun b => fst b + snd b <= lo \/ hi <= fst b) (PM.src_own src ++ PGV8.v8_own x ++ OB)
  /\ (forall b, In b OB -> (fst b + snd b <= PM.sr_qc src \/ PM.sr_qc src + PM.CHUNK <= fst b)
                          /\ (forall B' m', In (B', m') (PGV8.v8_own x) -> fst b + snd b <= B' \/ B' + m' <= fst b)).
Proof using TOK OFR HIok.
  intros HH. pose proof (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH) as ND.
  assert (IN3 : forall b, In b (PM.src_own src ++ PGV8.v8_own x ++ OB) -> In b (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)).
  { intros b Hb. rewrite !in_app_iff in Hb. rewrite !in_app_iff. tauto. }
  split.
  - apply Forall_forall. intros [B m] Hin. cbn [fst snd].
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M V B m lo (hi - lo) HH (IN3 _ Hin) OFR) as [X|X]; [left; exact X| right; lia].
  - intros [B m] Hin. cbn [fst snd].
    assert (HB : In (B, m) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply IN3; rewrite !in_app_iff; tauto).
    split.
    + assert (NE : PM.sr_qc src <> B).
      { apply (PMASK.fst_neq_appA (PM.src_own src) (PGV8.v8_own x ++ OB ++ LBX) (PM.sr_qc src) PM.CHUNK B m); [exact ND| left; reflexivity| apply in_or_app; right; apply in_or_app; left; exact Hin]. }
      destruct (PMASK.blk_apart L ar C HI HIok _ FF LK cr Aw M V (PM.sr_qc src) PM.CHUNK B m HH ltac:(left; reflexivity) HB NE); lia.
    + intros B' m' Hin'.
      assert (NE : B' <> B).
      { apply (PMASK.fst_neq_appA (PM.src_own src ++ PGV8.v8_own x) (OB ++ LBX) B' m' B m); [rewrite <- own2; exact ND| apply in_or_app; right; exact Hin'| apply in_or_app; left; exact Hin]. }
      destruct (PMASK.blk_apart L ar C HI HIok _ FF LK cr Aw M V B' m' B m HH ltac:(apply in_or_app; right; apply in_or_app; left; exact Hin') HB NE); lia.
Qed.

(* [comment removed for export] *)
Lemma tw_xferA M M' src src' x x' g g' LK cr Aw VM sp' scr' (Wx : list L5.range) :
  PGV8.vw_at T M src x g OB -> ri_inv HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) FF LK cr Aw M VM ->
  L5CA.ahpres L ar (OB ++ LBX) FF sp' scr' (PGS.W_srcfG os ois ++ [(tb, 24)] ++ Wx) M M' ->
  Forall (fun r => (fst r + snd r <= lo \/ hi <= fst r) /\ (forall B m, In (B, m) OB -> fst r + snd r <= B \/ B + m <= fst r) /\ app_mem (fst r) (snd r)) Wx ->
  PM.src_fields_at RSEGS PMSPA.accA M' os ois (ois + 16) src' -> PM.sr_qc src' = PM.sr_qc src -> v8_atA M' tb x' -> PGV8.v8_ok x' g' ->
  PGV8.vw_at T M' src' x' g' OB.
Proof using TOK OFR HIok.
  intros AT HH HP FW SFq QC VS TB. destruct (tw_side M src x LK cr Aw VM HH) as (FA & FB).
  exact (PGV8A.vo_upd _ _ _ _ _ _ TOK LBX sp' scr' Wx M M' src src' x x' g g' OB FF LK Aw cr VM OFR AT HH FA FB FW HP SFq QC VS TB).
Qed.

(* [comment removed for export] *)
Lemma stw_ok x g : PGSA.owner_ok RSEGS AD L ar HI (PGV8A.src_of_vw T x g).
Proof using TOK HIok LY. exact (PGV8KA.src_of_vw_okA L ar C HI HIok T x g TOK). Qed.

End Call.
End WithHeap.
End PGVWA1.
