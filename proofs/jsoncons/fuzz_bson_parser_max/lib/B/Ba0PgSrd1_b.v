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
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcRead1_b PnAReset1_b PnASrdP_b Ba0_code_rb1550_b1554_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PgTxtKitA_b PnRunA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSSRA1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation pot := (fun L ar (tx : PM.vstr) (tg : Z) => PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) tx tg)).

Lemma nodup_perm (l l' : list (Z * Z)) : Permutation l l' -> base.NoDup (map fst l) -> base.NoDup (map fst l').
Proof.
  intros P ND. apply NoDup_ListNoDup. apply NoDup_ListNoDup in ND.
  eapply Permutation_NoDup; [|exact ND]. apply Permutation_map. exact P.
Qed.
Lemma own2 (src : PM.srcst) (tx : PM.vstr) (OB LB : list (Z * Z)) : PM.src_own src ++ PM.vs_own tx ++ OB ++ LB = (PM.src_own src ++ PM.vs_own tx) ++ (OB ++ LB).
Proof. rewrite <- !app_assoc. reflexivity. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma perm_tb (src : PM.srcst) (tx : PM.vstr) (OB LB : list (Z * Z)) FF LK cr Aw M V :
  ri_inv HI (PM.src_own src ++ PM.vs_own tx ++ OB ++ LB) FF LK cr Aw M V ->
  ri_inv HI (PM.vs_own tx ++ (PM.src_own src ++ OB ++ LB)) FF LK cr Aw M V.
Proof.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
  apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF FF LK cr Aw M V HH).
  - intros b. rewrite !in_app_iff. tauto.
  - apply (nodup_perm (PM.src_own src ++ PM.vs_own tx ++ OB ++ LB)); [|exact ND].
    rewrite (app_assoc (PM.src_own src) (PM.vs_own tx)). rewrite (app_assoc (PM.vs_own tx) (PM.src_own src)).
    apply Permutation_app_tail. apply Permutation_app_comm.
  - intros f. tauto.
  - rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.
Lemma perm_tb_back (src : PM.srcst) (tx : PM.vstr) (OB LB : list (Z * Z)) FF LK cr Aw M V :
  ri_inv HI (PM.vs_own tx ++ (PM.src_own src ++ OB ++ LB)) FF LK cr Aw M V ->
  ri_inv HI (PM.src_own src ++ PM.vs_own tx ++ OB ++ LB) FF LK cr Aw M V.
Proof.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
  apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF FF LK cr Aw M V HH).
  - intros b. rewrite !in_app_iff. tauto.
  - apply (nodup_perm (PM.vs_own tx ++ (PM.src_own src ++ OB ++ LB))); [|exact ND].
    rewrite (app_assoc (PM.src_own src) (PM.vs_own tx)). rewrite (app_assoc (PM.vs_own tx) (PM.src_own src)).
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
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r len : Z) (T : PGS.towner) (OB : list (Z * Z)) (src0 : PM.srcst) (tx0 : PM.vstr) (tg0 : Z) (str : PM.vstr) (sm0 : PM.strm).
(* [comment removed for export] *)
Definition os : Z := PGS.tw_os T.
Definition ois : Z := PGS.tw_ois T.
Definition tb : Z := PGS.tw_otb T.
Definition lo : Z := PGS.tw_lo T.
Definition hi : Z := PGS.tw_hi T.
Hypothesis TOK : PGSA.towner_ok RSEGS AD L ar HI T.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis FRM0 : PGSA.ffroomB PNRA.FCB 5 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis OFR : PGSA.ofr FF lo hi.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UNS0 : PM.vs_size tx0 + PM.unread src0 sm0 < 2 ^ 26.
Hypothesis STKSH0 : shadow_zero M0 (S - 22528) 2816.
Hypothesis RSZ : PMA.str_resize_spec L ar HI.
Hypothesis SRD : PGSA.src_read_specG RSEGS AD L ar HI PNRA.FCB.
Hypothesis FBT : PGSA.fill_buffer_tb_specG RSEGS AD L ar HI PNRA.FCB.
(* [comment removed for export] *)
Definition W0 : list L5.range := PGS.W_srcfG os ois ++ [(tb, 24)].
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
                         (src' : PM.srcst) (tx' : PM.vstr) (tg' : Z) (sm' : PM.strm) (cr' : credit) (d : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
  PMSP.consumed src0 src' sm0 sm' = d -> PM.vs_size tx' = PM.vs_size tx0 + d ->
  PGS.tw_at T M' src' tx' tg' OB -> PM.iss_at RSEGS AD PMSPA.accA M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 5) W0 M0 M' ->
  PMSP.credit_keep cr0 cr' (pot L ar tx0 tg0) (pot L ar tx' tg') ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
  ri_inv HI (PM.src_own src' ++ PM.vs_own tx' ++ OB ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Definition U (x : nat) : Z := bv_unsigned (getr R0 (reg x)).
(* [comment removed for export] *)
Definition saves13 (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (U 1) /\ L5.u64_at RSEGS M (S - 16) (U 8) /\ L5.u64_at RSEGS M (S - 24) (U 9) /\ L5.u64_at RSEGS M (S - 32) (U 18)
  /\ L5.u64_at RSEGS M (S - 40) (U 19) /\ L5.u64_at RSEGS M (S - 48) (U 20) /\ L5.u64_at RSEGS M (S - 56) (U 21) /\ L5.u64_at RSEGS M (S - 64) (U 22)
  /\ L5.u64_at RSEGS M (S - 72) (U 23) /\ L5.u64_at RSEGS M (S - 80) (U 24) /\ L5.u64_at RSEGS M (S - 88) (U 25) /\ L5.u64_at RSEGS M (S - 96) (U 26)
  /\ L5.u64_at RSEGS M (S - 104) (U 27).
Definition locals (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 168) 0 /\ L5.u64_at RSEGS M (S - 160) len /\ L5.u64_at RSEGS M (S - 152) ((os + 256) / 8 + 2147450880)
  /\ L5.u64_at RSEGS M (S - 144) (os + 256) /\ L5.u64_at RSEGS M (S - 136) ((tb + 8) / 8 + 2147450880)
  /\ L5.u64_at RSEGS M (S - 128) ((tb + 16) / 8 + 2147450880) /\ L5.u64_at RSEGS M (S - 120) (tb + 16)
  /\ L5.u64_at RSEGS M (S - 112) (tb + 8).
Definition kept_rs (R : bvmap 5 word) : Prop := forall x, In x [3; 4]%nat -> getr R (reg x) = getr R0 (reg x).
(* [comment removed for export] *)
Definition memrel (M : word -> option byte) : Prop :=
  L5SAR.ek L ar (OB ++ LBX) FF S 22528 W0 M0 M /\ L5SAR.dk L ar (OB ++ LBX) FF S 22528 M0 M /\ L5CA.astk ar M S 22528.
(* [comment removed for export] *)
Definition fields_eq (src : PM.srcst) (tx : PM.vstr) (tg : Z) : Prop := True.
(* [comment removed for export] *)
Definition acct (src : PM.srcst) (tx : PM.vstr) (tg : Z) (sm : PM.strm) (w : Z) : Prop :=
  PMSP.consumed src0 src sm0 sm = len - w /\ PM.vs_size tx = PM.vs_size tx0 + (len - w) /\ PMSP.src_step src0 src sm0 sm /\ fields_eq src tx tg.
Definition st_ok (M : word -> option byte) (model : Model) (src : PM.srcst) (tx : PM.vstr) (tg : Z) (sm : PM.strm) (cr : credit) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  memrel M /\ saves13 M /\ locals M /\ PGS.tw_at T M src tx tg OB /\ PM.iss_at RSEGS AD PMSPA.accA M ois str sm
  /\ PMSTA.base_okA RSEGS AD M /\ PM.tb_ok tx tg
  /\ ri_inv HI (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) FF LK cr Aw M (vml_of model) /\ L5CA.amodel_ok Aw model /\ model_rt model0 model
  /\ incl LK LK0 /\ incl Aw0 Aw
  /\ PMSPA.credit_le (pot L ar tx tg) cr /\ PMSPA.credit_keep cr0 cr (pot L ar tx0 tg0) (pot L ar tx tg).
(* [comment removed for export] *)
Definition lregs (R : bvmap 5 word) (w : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 176) /\ getr R (reg 9) = Z_to_bv 64 tb /\ getr R (reg 18) = Z_to_bv 64 os
  /\ getr R (reg 19) = Z_to_bv 64 (os + 272) /\ getr R (reg 20) = Z_to_bv 64 (tb / 8 + 2147450880) /\ getr R (reg 21) = Z_to_bv 64 (os + 288)
  /\ getr R (reg 23) = Z_to_bv 64 ((os + 272) / 8 + 2147450880) /\ getr R (reg 26) = Z_to_bv 64 (tb + 1)
  /\ getr R (reg 27) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) /\ getr R (reg 8) = Z_to_bv 64 w /\ kept_rs R.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lay : lo <= os /\ os + 296 <= hi /\ lo <= ois /\ ois + 272 <= hi /\ lo <= tb /\ tb + 24 <= hi /\ hi <= ar_sptop ar /\ hi <= 2 ^ 47
            /\ os mod 8 = 0 /\ ois mod 8 = 0 /\ tb mod 8 = 0 /\ 4096 <= lo
            /\ (os + 296 <= ois \/ ois + 272 <= os) /\ (tb + 24 <= os \/ os + 296 <= tb) /\ (tb + 24 <= ois \/ ois + 272 <= tb).
Proof using TOK. exact (PGSA.to_lay _ _ _ _ _ _ TOK). Qed.
Lemma tsrc M src tx tg : PGS.tw_at T M src tx tg OB ->
  PM.src_fields_at RSEGS PMSPA.accA M os ois (ois + 16) src /\ PM.nullis_at RSEGS AD PMSPA.accA M (os + 8) /\ L5.defined M os 296
  /\ PM.vstr_at RSEGS PMSPA.accA M tb tx /\ PM.tb_ok tx tg.
Proof using TOK. exact (PGSA.to_src _ _ _ _ _ _ TOK M src tx tg OB). Qed.
Lemma aobjs : PMSPA.aobjA FF os 296 /\ PMSPA.aobjA FF ois 272 /\ PMSPA.aobjA FF tb 24.
Proof using TOK OFR.
  clear Hlen UNS0 STKSH0. pose proof lay as (L1 & L2 & L3 & L4 & L5' & L6 & _).
  split; [|split]; (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| lia| lia]).
Qed.
Lemma inW_W0 a : (exists r0, In r0 W0 /\ L5.in_rng r0 a) -> (os + 256 <= a < os + 296) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (tb <= a < tb + 24).
Proof.
  intros (r0 & Hin & Hr). unfold W0, PGS.W_srcfG in Hin. cbn [app] in Hin. unfold L5.in_rng in Hr.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma outside_W0 a : (a < lo \/ hi <= a) -> L5.outside W0 a.
Proof using TOK. clear Hlen UNS0 STKSH0. intros Ha r0 Hr0 Hin. assert (I : exists r1, In r1 W0 /\ L5.in_rng r1 a) by (exists r0; split; assumption). apply inW_W0 in I. pose proof lay. lia. Qed.
(* [comment removed for export] *)
Lemma frame_app LB LK cr Aw M V : ri_inv HI LB FF LK cr Aw M V ->
  6905856 <= lo /\ hi <= 2 ^ 47 /\ (hi <= BIGSHADOW_LO \/ BIGSHADOW_HI <= lo) /\ lo <= hi /\ hi <= ahl_ceil ar.
Proof using TOK OFR HIok LY.
  intros HH. clear Hlen UNS0 STKSH0. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & FSCEIL & _).
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof OFR as (f & Hf & X1 & X2). destruct (WF _ Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in FSAPP, FSCEIL, Y2. pose proof lay. lia.
Qed.
Lemma wapp_W0 LB LK cr Aw M V : ri_inv HI LB FF LK cr Aw M V -> PMKA.wapp W0.
Proof using TOK OFR HIok LY.
  intros HH r0 Hr. clear Hlen UNS0 STKSH0. destruct (frame_app _ _ _ _ _ _ HH) as (F1 & F2 & F3 & F4 & F5). pose proof lay.
  unfold W0, PGS.W_srcfG in Hr. cbn [app] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; (destruct F3; [left|right]; lia).
Qed.

(* [comment removed for export] *)
Lemma tw_side M (src : PM.srcst) (tx : PM.vstr) LK cr Aw V :
  ri_inv HI (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) FF LK cr Aw M V ->
  Forall (fun b => fst b + snd b <= lo \/ hi <= fst b) (PM.src_own src ++ PM.vs_own tx ++ OB)
  /\ (forall b, In b OB -> (fst b + snd b <= PM.sr_qc src \/ PM.sr_qc src + PM.CHUNK <= fst b)
                          /\ (forall B' m', In (B', m') (PM.vs_own tx) -> fst b + snd b <= B' \/ B' + m' <= fst b)).
Proof using TOK OFR HIok.
  intros HH. clear Hlen UNS0 STKSH0. pose proof (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH) as ND.
  assert (IN3 : forall b, In b (PM.src_own src ++ PM.vs_own tx ++ OB) -> In b (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX)).
  { intros b Hb. rewrite !in_app_iff in Hb. rewrite !in_app_iff. tauto. }
  split.
  - apply Forall_forall. intros [B m] Hin. cbn [fst snd].
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M V B m lo (hi - lo) HH (IN3 _ Hin) OFR) as [X|X]; [left; exact X| right; lia].
  - intros [B m] Hin. cbn [fst snd].
    assert (HB : In (B, m) (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX)) by (apply IN3; rewrite !in_app_iff; tauto).
    split.
    + assert (NE : PM.sr_qc src <> B).
      { apply (PMASK.fst_neq_appA (PM.src_own src) (PM.vs_own tx ++ OB ++ LBX) (PM.sr_qc src) PM.CHUNK B m); [exact ND| left; reflexivity| apply in_or_app; right; apply in_or_app; left; exact Hin]. }
      destruct (PMASK.blk_apart L ar C HI HIok _ FF LK cr Aw M V (PM.sr_qc src) PM.CHUNK B m HH ltac:(left; reflexivity) HB NE); lia.
    + intros B' m' Hin'.
      assert (NE : B' <> B).
      { apply (PMASK.fst_neq_appA (PM.src_own src ++ PM.vs_own tx) (OB ++ LBX) B' m' B m); [rewrite <- own2; exact ND| apply in_or_app; right; exact Hin'| apply in_or_app; left; exact Hin]. }
      destruct (PMASK.blk_apart L ar C HI HIok _ FF LK cr Aw M V B' m' B m HH ltac:(apply in_or_app; right; apply in_or_app; left; exact Hin') HB NE); lia.
Qed.

(* [comment removed for export] *)
Lemma tw_xferA M M' src src' tx tx' tg tg' LK cr Aw VM sp' scr' (Wx : list L5.range) :
  PGS.tw_at T M src tx tg OB -> ri_inv HI (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) FF LK cr Aw M VM ->
  L5CA.ahpres L ar (OB ++ LBX) FF sp' scr' (PGS.W_srcfG os ois ++ [(tb, 24)] ++ Wx) M M' ->
  Forall (fun r => (fst r + snd r <= lo \/ hi <= fst r) /\ (forall B m, In (B, m) OB -> fst r + snd r <= B \/ B + m <= fst r) /\ app_mem (fst r) (snd r)) Wx ->
  PM.src_fields_at RSEGS PMSPA.accA M' os ois (ois + 16) src' -> PM.sr_qc src' = PM.sr_qc src -> PM.vstr_at RSEGS PMSPA.accA M' tb tx' -> PM.tb_ok tx' tg' ->
  PGS.tw_at T M' src' tx' tg' OB.
Proof using TOK OFR HIok.
  intros AT HH HP FW SFq QC VS TB. destruct (tw_side M src tx LK cr Aw VM HH) as (FA & FB).
  exact (PGSA.to_upd _ _ _ _ _ _ TOK LBX sp' scr' Wx M M' src src' tx tx' tg tg' OB FF LK Aw cr VM OFR AT HH FA FB FW HP SFq QC VS TB).
Qed.

(* [comment removed for export] *)
Lemma stw_ok tx tg : PGSA.owner_ok RSEGS AD L ar HI (PGSA.src_of_tw T tx tg).
Proof using TOK HIok LY. exact (PGTKA.src_of_tw_okA L ar C HI HIok T tx tg TOK). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma finish (fx : FPState) R M model src tx tg sm cr LK Aw (w : Z) :
  getr R (reg 1) = Z_to_bv 64 (U 1) -> getr R (reg 2) = Z_to_bv 64 S ->
  (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg x) = Z_to_bv 64 (U x)) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 (len - w) -> 0 <= w <= len ->
  st_ok M model src tx tg sm cr LK Aw -> acct src tx tg sm w ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb53b8 M model) K.
Proof using All.
  intros E1 E2 ES KP E10 Hw ((EK & DK & STK) & _ & _ & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK) (CONS & SZ & STEP & _).
  pose proof RAok as (Hr1 & Hr2).
  assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1; unfold U; rewrite Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMSP.cfg.
  apply (PMASK.ret_exit L ar C HI LY HIok fx R M model K _ FF LK cr Aw 0xb53b8 r W_b3ae4 HH AM F_b3ae4 eq_refl D_b3ae4 RA ltac:(lia) Hr2).
  intros model1 MRT1 AM1 HH1.
  apply (KONT fx R M model1 LK Aw src tx tg sm cr (len - w)); try assumption; try lia.
  - apply L5SAR.preserved_by_index. intros x Hx. unfold L5SAR.cs_all in Hx.
    destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
    destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
    rewrite (ES x) by (cbn in Hx; cbn; tauto). unfold U. apply Z_to_bv_bv_unsigned.
  - change (PMSPA.pm_scr 5) with 22528. apply (L5SAR.ahpres_of L ar LBX FF S 22528 _ M0 M).
    + exact (ek_drop OB LBX FF S 22528 W0 M0 M EK).
    + destruct STK as (_ & _ & _ & _ & D & _); exact D.
    + exact (dk_drop OB LBX FF S 22528 M0 M DK).
  - eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma callee_mem M M' (BX : list (Z * Z)) scr' (W' : list L5.range) :
  memrel M -> saves13 M -> locals M -> 0 <= scr' -> 176 + scr' <= 22528 -> ar_stack_top ar <= 2 ^ 47 ->
  L5CA.ahpres L ar (BX ++ (OB ++ LBX)) FF (S - 176) scr' W' M M' ->
  (forall a, aclient L ar (OB ++ LBX) FF S 22528 a -> L5.outside W0 a -> L5.outside W' a) -> (forall a, S - 176 <= a < S -> L5.outside W' a) ->
  memrel M' /\ saves13 M' /\ locals M' /\ L5SAR.ek L ar (OB ++ LBX) FF S 22528 W0 M M'.
Proof using All.
  intros (EK & DK & STK) SV LC Hs Hs2 TOP HP HW HWS.
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  assert (EKn : L5SAR.ek L ar (OB ++ LBX) FF S 22528 W0 M M').
  { apply (L5SAR.ek_callee L ar (OB ++ LBX) BX FF [] S 22528 (S - 176) scr' W0 W' M M' HP); [lia|lia| exact HW]. }
  assert (DKn : L5SAR.dk L ar (OB ++ LBX) FF S 22528 M M') by (apply (L5SAR.dk_callee L ar (OB ++ LBX) BX FF [] S 22528 (S - 176) scr' W' M M' HP); lia).
  assert (KEEPS : forall k v, 8 <= k <= 176 -> L5.u64_at RSEGS M (S - k) v -> L5.u64_at RSEGS M' (S - k) v).
  { intros k v Hk X. apply (L5C.u64_at_agree RSEGS M M'); [|lia|lia|exact X].
    intros i Hi. destruct HP as (P & _). apply P. split; [lia|]. split.
    - apply (L5SAR.stack_client L ar (BX ++ (OB ++ LBX)) FF (S - 176) scr' i); lia.
    - apply HWS. lia. }
  split; [split; [|split]|].
  - exact (L5SAR.ek_trans L ar (OB ++ LBX) FF S 22528 W0 M0 M M' EK EKn).
  - exact (L5SAR.dk_trans L ar (OB ++ LBX) FF S 22528 M0 M M' DK DKn).
  - apply (PMKA.astk_after_ahpres L ar _ FF M M' S 22528 (S - 176) scr' W' STK HP); lia.
  - split; [|split; [|exact EKn]].
    + destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
      repeat split; (apply KEEPS; [lia| assumption]).
    + destruct LC as (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8).
      repeat split; (apply KEEPS; [lia| assumption]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma centry (R : bvmap 5 word) M model src tx tg sm cr LK Aw (X h : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 176) -> kept_rs R -> st_ok M model src tx tg sm cr LK Aw -> 1 <= h <= 4 ->
  PMSPA.entryA AD L ar R M (S - 176) X h /\ PGSA.ffroomB PNRA.FCB h FF LK /\ PMSPA.ffrsA FF (S - 176).
Proof using All.
  intros A1 RAX A2 KP SO Hh.
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  assert (STKr : L5CA.astk ar M (S - 176) (PMSPA.pm_scr h)).
  { apply (L5SAR.astk_sub ar M M S 22528 176 (PMSPA.pm_scr h) STK (fun _ Y => Y)); unfold PMSPA.pm_scr; [lia|lia|lia|].
    replace (S - 176) with (S + (-11) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof (wapp_W0 _ _ _ _ _ _ HH) as WAPP0.
  assert (STKSH : shadow_zero M (S - 176 - PMSPA.pm_scr h) (PMSPA.pm_scr h / 8)).
  { assert (M8a : (S - 22528) mod 8 = 0) by (apply PMKA.mod16_8'; replace (S - 22528) with (S + (-1408) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    assert (M8b : (S - 176 - PMSPA.pm_scr h) mod 8 = 0).
    { apply PMKA.mod16_8'. unfold PMSPA.pm_scr. replace (S - 176 - (12288 + 2048 * h)) with (S + (-(779 + 128 * h)) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    assert (G8 : PMSPA.pm_scr h / 8 = 1536 + 256 * h).
    { unfold PMSPA.pm_scr. replace (12288 + 2048 * h) with ((1536 + 256 * h) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
    rewrite G8. unfold PMSPA.pm_scr in M8b |- *.
    apply (PMKA.shadow_zero_sub M (S - 22528) 2816); [exact M8a| exact M8b| lia| lia| lia|].
    apply (PMKA.stksh_keepA L ar (OB ++ LBX) FF S 22528 W0 M0 M EK WAPP0 (S - 22528) 2816); [lia|lia|lia| exact M8a| lia| exact STKSH0]. }
  assert (FRM : PGSA.ffroomB PNRA.FCB h FF LK) by (apply (PGTKA.ffroom_incl PNRA.FCB 5 h FF LK0 LK FRM0 ILK NDF); lia).
  split; [|split; [exact FRM| intros f Hf; specialize (FRS f Hf); lia]].
  unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
  split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0|].
  split; [exact STKr| exact STKSH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma call_resize (fx : FPState) R M model src tx tg sm cr LK Aw (nn X : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 176) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 tb -> getr R (reg 11) = Z_to_bv 64 nn ->
  0 <= nn <= PM.vs_size tx + PM.CHUNK -> nn < 2 ^ 26 + PM.CHUNK ->
  st_ok M model src tx tg sm cr LK Aw ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (tx' : PM.vstr) (tg' : Z) (cr' : credit),
     regs_preserved R R' -> PM.vs_size tx' = nn -> (nn <= PM.vs_cap tx -> PM.vs_own tx' = PM.vs_own tx /\ tg' = tg) ->
     st_ok M' model' src tx' tg' sm cr' LK' Aw' ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xd628c M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 Hn1 Hn2 SO NEXT.
  destruct (centry R M model src tx tg sm cr LK Aw X 1 A1 RAX A2 KP SO ltac:(lia)) as (ENT & FRM & FRS').
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  pose proof lay as LAY. pose proof aobjs as (AO & AOI & AT).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (tsrc M src tx tg PA) as (PSF & PNI & PD & VS & _).
  pose proof (PGTKA.tb_visG L ar C HI LY HIok _ FF LK cr Aw M model tb tx HH AT ltac:(lia) VS) as ((T1 & T8 & TBIG) & _ & _ & _ & _ & _ & TFS1 & TFS2).
  unfold app_mem, FS_BYTES in FSAPP, FSCEIL, TFS1, TFS2.
  set (LB' := PM.src_own src ++ OB ++ LBX).
  pose proof (perm_tb src tx OB LBX FF LK cr Aw M _ HH) as HH'. fold LB' in HH'.
  assert (QIN : In (PM.sr_qc src, PM.CHUNK) LB') by (unfold LB', PM.src_own; left; reflexivity).
  destruct (BRB _ ltac:(left; reflexivity)) as (QB0 & QB1). cbn [fst snd] in QB0, QB1.
  pose proof RSZ as RS. unfold PMA.str_resize_spec, PMSPA.str_resize_spec in RS. cbn [pa_str_resize AD PMA.AD ADDR_A] in RS.
  apply (RS fx R M model K LB' FF LK Aw cr tb nn (S - 176) X tg tx HH' AM K0 ENT FRM FRS').
  { rewrite L5K.rl10. exact A10. }
  { rewrite L5SAR.r11. exact A11. }
  { exact AT. } { exact T8. } { exact VS. } { exact TBOK. } { exact Hn1. } { exact Hn2. } { exact CRL. }
  intros fx' R' M' model' LK' Aw' tx' tg' cr' RP VS' SZ TB' OWN HP CK MRT' ILK' IAW' AM' HH2.
  change (PMSPA.pm_scr 1) with 14336 in HP.
  apply (NEXT fx' R' M' model' LK' Aw' tx' tg' cr' RP SZ OWN).
  assert (HPc : L5CA.ahpres L ar (PM.src_own src ++ (OB ++ LBX)) FF (S - 176) 14336 [(tb, 24)] M M') by exact HP.
  destruct (callee_mem M M' _ 14336 [(tb, 24)] MR SV LC ltac:(lia) ltac:(lia) TOP HPc) as (MR' & SV' & LC' & EKn).
  { intros a _ Oq r0 [<-|[]] Hin. apply (Oq (tb, 24)); [unfold W0; apply in_or_app; right; left; reflexivity| exact Hin]. }
  { intros a Ha r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia. }
  set (Wt := [(tb, 24)]).
  assert (WAPPt : PMKA.wapp Wt) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct TBIG; [right| left]; lia| apply PMKA.wapp_nil]).
  pose proof HP as (EKr & DSr & DKr).
  assert (EKt : L5SAR.ek L ar LB' FF (S - 176) 14336 Wt M M') by exact EKr.
  assert (BRB' : forall b, In b LB' -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47).
  { intros b Hb. apply BRB. unfold LB' in Hb. rewrite !in_app_iff in Hb. rewrite !in_app_iff. tauto. }
  (* [comment removed for export] *)
  assert (SF' : PM.src_fields_at RSEGS PMSPA.accA M' os ois (ois + 16) src).
  { apply (PGSKA.src_fields_keepG M M' os ois (ois + 16) src PSF); [lia| lia| | |].
    - apply (PMKA.agA_obj L ar LB' FF (S - 176) 14336 Wt M M' EKt WAPPt FRB os 296 AO). intros i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
    - apply (PMASK.agsh_blk L ar LB' FF (S - 176) 14336 Wt M M' _ _ EKt WAPPt QIN); lia.
    - apply (PMASK.defined_dk L ar LB' FF (S - 176) 14336 M M' _ _ DKr); [intros i Hi; apply (L5SAR.block_client L ar LB' FF (S - 176) 14336 _ _ i QIN Hi)| lia| lia|].
      destruct PSF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DCH & _). exact DCH. }
  assert (HPw : L5CA.ahpres L ar (OB ++ LBX) FF (S - 176) 14336 (PGS.W_srcfG os ois ++ [(tb, 24)] ++ []) M M').
  { apply (L5SAR.ahpres_of L ar (OB ++ LBX) FF (S - 176) 14336 _ M M').
    - apply (L5SAR.ek_callee L ar (OB ++ LBX) (PM.src_own src) FF [] (S - 176) 14336 (S - 176) 14336 _ _ M M' HPc); [lia| lia|].
      intros a _ Oq r0 [<-|[]] Hin. apply (Oq (tb, 24)); [apply in_or_app; right; left; reflexivity| exact Hin].
    - exact DSr.
    - apply (L5SAR.dk_callee L ar (OB ++ LBX) (PM.src_own src) FF [] (S - 176) 14336 (S - 176) 14336 _ M M' HPc); lia. }
  assert (PA' : PGS.tw_at T M' src tx' tg' OB).
  { exact (tw_xferA M M' src src tx tx' tg tg' LK cr Aw (vml_of model) (S - 176) 14336 [] PA HH HPw ltac:(constructor) SF' eq_refl VS' TB'). }
  assert (IA' : PM.iss_at RSEGS AD PMSPA.accA M' ois str sm).
  { apply (PMKA.iss_keepA RSEGS AD L ar LB' FF (S - 176) 14336 Wt M M' EKt WAPPt FRB BRB' _ _ _ AOI); [| | |exact IA].
    - intros x Hx. unfold LB'. rewrite !in_app_iff. right; right. apply INCS. exact Hx.
    - intros i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
    - intros c n p E i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      destruct (PMASK.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ p c tb 24 HH ltac:(rewrite !in_app_iff; right; right; right; apply INCS; rewrite E; left; reflexivity) AT); lia. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact LC'|]. split; [exact PA'|]. split; [exact IA'|].
  split.
  { apply (PMASK.base_keep L ar C LY (OB ++ LBX) FF S 22528 W0 M M' EKn); [| exact BASE].
    intros a Ha. apply outside_W0. pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. destruct (frame_app _ _ _ _ _ _ HH). lia. }
  split; [exact TB'|]. split; [apply perm_tb_back; exact HH2|]. split; [exact AM'|].
  split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
  split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
  unfold PMSPA.credit_keep, PMSPA.credit_le in *. destruct CRL as (CL1 & CL2). destruct CK as (CK1 & CK2). destruct CRK as (CR1 & CR2). split; split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tbdst (tx : PM.vstr) (p k : Z) : Prop :=
  ((exists n, tx = PM.VShort n) /\ tb + 1 <= p /\ p + k <= tb + 24)
  \/ (exists c n q, tx = PM.VLong c n q /\ q <= p /\ p + k <= q + c).

(* [comment removed for export] *)
Lemma call_srcread (fx : FPState) R M model src tx tg sm cr LK Aw (p k X : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 176) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 k ->
  1 <= k <= PM.CHUNK -> tbdst tx p k -> st_ok M model src tx tg sm cr LK Aw ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (src' : PM.srcst) (sm' : PM.strm) (d : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 d -> 0 <= d <= k ->
     PMSP.consumed src src' sm sm' = d -> (1 <= PM.sr_rem src -> 1 <= d) ->
     (d = 0 -> PM.sr_rem src' = 0 /\ PM.sm_st sm' = 2) -> PMSP.src_step src src' sm sm' ->
     st_ok M' model' src' tx tg sm' cr LK' Aw' ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xaed4c M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 Hk DST SO NEXT.
  destruct (centry R M model src tx tg sm cr LK Aw X 4 A1 RAX A2 KP SO ltac:(lia)) as (ENT & FRM & FRS').
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  pose proof lay as LAY. pose proof aobjs as (AO & AOI & AT). destruct (frame_app _ _ _ _ _ _ HH) as (F1 & F2 & F3 & F4 & F5).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (QIN : In (PM.sr_qc src, PM.CHUNK) (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX)) by (left; reflexivity).
  assert (DSTB : 0 <= p /\ p + k <= 2 ^ 47 /\ forall a, p <= a < p + k -> (tb <= a < tb + 24) \/ exists B m, In (B, m) (PM.src_own src ++ PM.vs_own tx) /\ B <= a < B + m).
  { destruct DST as [(_ & D1 & D2)|(c & n & q & E & D1 & D2)].
    - split; [lia|]. split; [lia|]. intros a Ha. left. lia.
    - assert (IN : In (q, c) (PM.src_own src ++ PM.vs_own tx)) by (rewrite E; apply in_or_app; right; left; reflexivity).
      destruct (BRB (q, c) ltac:(rewrite own2; apply in_or_app; left; exact IN)) as (Q0 & Q4). cbn [fst snd] in Q0, Q4.
      split; [lia|]. split; [lia|]. intros a Ha. right. exists q, c. split; [exact IN| lia]. }
  destruct DSTB as (Dp0 & Dp1 & DIN).
  pose proof SRD as SR. unfold PGSA.src_read_specG, PGSA.src_specG in SR. cbn [pa_src_read AD PMA.AD ADDR_A] in SR.
  apply (SR (PGSA.src_of_tw T tx tg) (stw_ok tx tg) fx R M model K (PM.vs_own tx ++ OB) LBX FF LK Aw cr (S - 176) X src str sm [(p, k)]);
    cbn [PGS.ow_at PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi PGS.ow_win PGSA.src_of_tw].
  { replace (PM.src_own src ++ (PM.vs_own tx ++ OB) ++ LBX) with (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) by (rewrite <- !app_assoc; reflexivity). exact HH. }
  { exact AM. } { exact K0. } { exact ENT. } { exact FRM. } { exact FRS'. } { exact OFR. }
  { rewrite L5K.rl10. exact A10. }
  { unfold PGSA.read_args. exists p, k. rewrite L5SAR.r11, L5SAR.r12. split; [exact A11|]. split; [exact A12|]. split; [exact Hk|].
    unfold PGSA.dst_okG. right. cbn [PGS.ow_win PGSA.src_of_tw]. split; [lia| exact DST]. }
  { unfold PMPS.read_W. exists p, k. rewrite L5SAR.r11, L5SAR.r12. split; [exact A11|]. split; [exact A12|]. split; [lia|]. split; [unfold PM.CHUNK in Hk; lia| reflexivity]. }
  { exists OB. split; [reflexivity| exact PA]. }
  { exact IA. } { exact BASE. } { exact INCS. }
  intros fx' R' M' model' LK' Aw' src' sm' RP (OB1 & EOB & PA') IA' STEP RES HP MRT' ILK' IAW' AM' HH'.
  apply app_inv_head in EOB. subst OB1.
  change (PMSPA.pm_scr 4) with 20480 in HP.
  unfold PMPS.read_res in RES. destruct RES as (p' & k' & d & Y11 & Y12 & Hp' & Hk' & Y10 & Hd & CONS & _ & POS & ZERO).
  assert (pk : p' = p /\ k' = k).
  { rewrite L5SAR.r11 in Y11. rewrite L5SAR.r12 in Y12. rewrite A11 in Y11. rewrite A12 in Y12. apply (f_equal bv_unsigned) in Y11, Y12.
    unfold PM.CHUNK in Hk, Hk'. rewrite !L5.unsigned_lit in Y11, Y12 by lia. split; congruence. }
  destruct pk as (-> & ->).
  assert (QC : PM.sr_qc src' = PM.sr_qc src) by (destruct STEP as (E & _); exact E).
  rewrite L5K.rl10 in Y10.
  apply (NEXT fx' R' M' model' LK' Aw' src' sm' d RP Y10 Hd CONS POS ZERO STEP).
  replace (PM.src_own src ++ (PM.vs_own tx ++ OB) ++ LBX) with ((PM.src_own src ++ PM.vs_own tx) ++ (OB ++ LBX)) in HP by (rewrite <- !app_assoc; reflexivity).
  destruct (callee_mem M M' (PM.src_own src ++ PM.vs_own tx) 20480 (PGS.W_srcG os ois src ++ [(p, k)]) MR SV LC ltac:(lia) ltac:(lia) TOP HP) as (MR' & SV' & LC' & EKn).
  { intros a CA OW r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - unfold PGS.W_srcG in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
      + apply (OW r0); [unfold W0; apply in_or_app; left; exact Hr0| exact Hin].
      + apply (PMARS1.own_not_aclient L ar C HI HIok (PM.src_own src ++ PM.vs_own tx) (OB ++ LBX) FF LK cr Aw M _ (PM.sr_qc src) PM.CHUNK a S 22528 ltac:(rewrite <- own2; exact HH));
          [apply in_or_app; left; left; reflexivity| unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin| exact CA].
    - unfold L5.in_rng in Hin. cbn [fst snd] in Hin. destruct (DIN a Hin) as [X0|(B & m & HB & Ha)].
      + apply (OW (tb, 24)); [unfold W0; apply in_or_app; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; exact X0].
      + apply (PMARS1.own_not_aclient L ar C HI HIok (PM.src_own src ++ PM.vs_own tx) (OB ++ LBX) FF LK cr Aw M _ B m a S 22528 ltac:(rewrite <- own2; exact HH) HB Ha CA). }
  { intros a Ha r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - unfold PGS.W_srcG in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
      + exact (outside_W0 a ltac:(lia) r0 ltac:(unfold W0; apply in_or_app; left; exact Hr0) Hin).
      + destruct (WB _ QIN) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PM.CHUNK in *. lia.
    - unfold L5.in_rng in Hin. cbn [fst snd] in Hin. destruct (DIN a Hin) as [X0|(B & m & HB & Ha')]; [lia|].
      destruct (WB (B, m) ltac:(rewrite own2; apply in_or_app; left; exact HB)) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. lia. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact LC'|]. split; [exact PA'|]. split; [exact IA'|].
  split.
  { apply (PMASK.base_keep L ar C LY (OB ++ LBX) FF S 22528 W0 M M' EKn); [| exact BASE].
    intros a Ha. apply outside_W0. pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
  split; [exact TBOK|].
  split; [unfold PM.src_own; rewrite QC; replace ([(PM.sr_qc src, PM.CHUNK)] ++ PM.vs_own tx ++ OB ++ LBX) with (PM.src_own src ++ (PM.vs_own tx ++ OB) ++ LBX) by (unfold PM.src_own; rewrite <- !app_assoc; reflexivity); exact HH'|].
  split; [exact AM'|].
  split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
  split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
  split; [exact CRL| exact CRK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma call_filltb (fx : FPState) R M model src tx tg sm cr LK Aw (p X c0 n0 q0 : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 176) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 PM.CHUNK ->
  tx = PM.VLong c0 n0 q0 -> q0 <= p -> p + PM.CHUNK <= q0 + c0 -> st_ok M model src tx tg sm cr LK Aw ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (sm' : PM.strm) (c : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> PM.sm_g sm' = PM.sm_g sm + c ->
     (PM.sm_st sm = 0 -> c = Z.min PM.CHUNK (PM.sm_eg sm - PM.sm_g sm) /\ PM.sm_st sm' = (if Z.ltb c PM.CHUNK then 2 else 0)) ->
     (PM.sm_st sm = 2 -> c = 0 /\ PM.sm_st sm' = 2) ->
     PMSP.src_step src src sm sm' ->
     st_ok M' model' src tx tg sm' cr LK' Aw' ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb29f8 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 ETB D1 D2 SO NEXT.
  destruct (centry R M model src tx tg sm cr LK Aw X 3 A1 RAX A2 KP SO ltac:(lia)) as (ENT & FRM & FRS').
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  pose proof lay as LAY. pose proof aobjs as (AO & AOI & AT). destruct (frame_app _ _ _ _ _ _ HH) as (F1 & F2 & F3 & F4 & F5).
  assert (QIN : In (PM.sr_qc src, PM.CHUNK) (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX)) by (left; reflexivity).
  assert (IN : In (q0, c0) (PM.src_own src ++ PM.vs_own tx)) by (rewrite ETB; apply in_or_app; right; left; reflexivity).
  destruct (WB (q0, c0) ltac:(rewrite own2; apply in_or_app; left; exact IN)) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4.
  pose proof FBT as SR. unfold PGSA.fill_buffer_tb_specG, PGSA.src_specG in SR. cbn [pa_fill_buffer AD PMA.AD ADDR_A] in SR.
  apply (SR (PGSA.src_of_tw T tx tg) (stw_ok tx tg) fx R M model K (PM.vs_own tx ++ OB) LBX FF LK Aw cr (S - 176) X src str sm [(p, PM.CHUNK)]);
    cbn [PGS.ow_at PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi PGS.ow_win PGSA.src_of_tw].
  { replace (PM.src_own src ++ (PM.vs_own tx ++ OB) ++ LBX) with (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) by (rewrite <- !app_assoc; reflexivity). exact HH. }
  { exact AM. } { exact K0. } { exact ENT. } { exact FRM. } { exact FRS'. } { exact OFR. }
  { rewrite L5K.rl10. exact A10. }
  { unfold PGSA.tbfill_args. exists p. rewrite L5SAR.r11, L5SAR.r12. split; [exact A11|]. split; [exact A12|].
    cbn [PGS.ow_win PGSA.src_of_tw]. split; [unfold PM.CHUNK; lia|]. right. exists c0, n0, q0. split; [exact ETB| lia]. }
  { unfold PMTXS.tbfill_W. exists p. rewrite L5SAR.r11. split; [exact A11|]. split; [unfold PM.CHUNK in *; lia| reflexivity]. }
  { exists OB. split; [reflexivity| exact PA]. }
  { exact IA. } { exact BASE. } { exact INCS. }
  intros fx' R' M' model' LK' Aw' src' sm' RP (OB1 & EOB & PA') IA' STEP RES HP MRT' ILK' IAW' AM' HH'.
  apply app_inv_head in EOB. subst OB1.
  change (PMSPA.pm_scr 3) with 18432 in HP.
  destruct RES as ((-> & c & Y10 & Hc & G & ST0 & ST2) & _).
  rewrite L5K.rl10 in Y10.
  apply (NEXT fx' R' M' model' LK' Aw' sm' c RP Y10 Hc G ST0 ST2 STEP).
  replace (PM.src_own src ++ (PM.vs_own tx ++ OB) ++ LBX) with ((PM.src_own src ++ PM.vs_own tx) ++ (OB ++ LBX)) in HP by (rewrite <- !app_assoc; reflexivity).
  destruct (callee_mem M M' (PM.src_own src ++ PM.vs_own tx) 18432 (PGS.W_srcG os ois src ++ [(p, PM.CHUNK)]) MR SV LC ltac:(lia) ltac:(lia) TOP HP) as (MR' & SV' & LC' & EKn).
  { intros a CA OW r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - unfold PGS.W_srcG in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
      + apply (OW r0); [unfold W0; apply in_or_app; left; exact Hr0| exact Hin].
      + apply (PMARS1.own_not_aclient L ar C HI HIok (PM.src_own src ++ PM.vs_own tx) (OB ++ LBX) FF LK cr Aw M _ (PM.sr_qc src) PM.CHUNK a S 22528 ltac:(rewrite <- own2; exact HH));
          [apply in_or_app; left; left; reflexivity| unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin| exact CA].
    - unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      apply (PMARS1.own_not_aclient L ar C HI HIok (PM.src_own src ++ PM.vs_own tx) (OB ++ LBX) FF LK cr Aw M _ q0 c0 a S 22528 ltac:(rewrite <- own2; exact HH) IN ltac:(unfold PM.CHUNK in *; lia) CA). }
  { intros a Ha r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - unfold PGS.W_srcG in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
      + exact (outside_W0 a ltac:(lia) r0 ltac:(unfold W0; apply in_or_app; left; exact Hr0) Hin).
      + destruct (WB _ QIN) as ((Q0' & _ & _ & _ & Q4' & _) & _). cbn [fst snd] in Q0', Q4'. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PM.CHUNK in *. lia.
    - unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PM.CHUNK in *. lia. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact LC'|]. split; [exact PA'|]. split; [exact IA'|].
  split.
  { apply (PMASK.base_keep L ar C LY (OB ++ LBX) FF S 22528 W0 M M' EKn); [| exact BASE].
    intros a Ha. apply outside_W0. pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
  split; [exact TBOK|].
  split; [replace (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) with (PM.src_own src ++ (PM.vs_own tx ++ OB) ++ LBX) by (rewrite <- !app_assoc; reflexivity); exact HH'|].
  split; [exact AM'|].
  split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
  split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
  split; [exact CRL| exact CRK].
Qed.

(* [comment removed for export] *)
Lemma unread_nn M model src tx tg sm cr LK Aw : st_ok M model src tx tg sm cr LK Aw ->
  0 <= PM.unread src sm /\ (PM.sm_st sm = 0 \/ PM.sm_st sm = 2) /\ 0 <= PM.sr_rem src <= PM.CHUNK /\ PM.sm_g sm <= PM.sm_eg sm.
Proof using All.
  intros (_ & _ & _ & PA & IA & _).
  destruct (tsrc M src tx tg PA) as ((_ & _ & _ & _ & _ & _ & _ & Q8 & Q9 & Q10 & _) & _).
  destruct IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & ST) & _ & G1 & G2).
  unfold PM.unread. split; [lia|]. split; [exact ST|]. split; [unfold PM.CHUNK in *; lia| exact G2].
Qed.

(* [comment removed for export] *)
Lemma lregs_keep R R1 w : lregs R w -> (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x)) -> lregs R1 w.
Proof.
  intros (A2 & A9 & A18 & A19 & A20 & A21 & A23 & A26 & A27 & A8 & KP) E.
  unfold lregs. rewrite !E by (cbn; tauto). repeat split; try assumption.
  intros x Hx. rewrite E by (cbn in Hx |- *; tauto). apply KP. exact Hx.
Qed.
Lemma lregs_pres R R' w : regs_preserved R R' -> lregs R w -> lregs R' w.
Proof. intros RP LR. apply (lregs_keep R R' w LR). intros x Hx. apply (L5SAR.cs_of_preserved R R' x RP). unfold L5SAR.cs_all. cbn in Hx |- *. tauto. Qed.

Lemma lregs_set R R1 w w' : lregs R w -> (forall x, In x [2; 3; 4; 9; 18; 19; 20; 21; 23; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x)) ->
  getr R1 (reg 8) = Z_to_bv 64 w' -> lregs R1 w'.
Proof.
  intros (A2 & A9 & A18 & A19 & A20 & A21 & A23 & A26 & A27 & A8 & KP) E E8.
  unfold lregs. rewrite !E by (cbn; tauto). repeat split; try assumption.
  intros x Hx. rewrite E by (cbn in Hx |- *; tauto). apply KP. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma ro_step (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) M model src tx tg sm cr LK Aw (M1v : word -> option byte) :
  st_ok M model src tx tg sm cr LK Aw ->
  msteps RSEGS (L5SAR.st fx R pc (mrestrict (ahid Aw model) M)) (L5SAR.st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid Aw model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> M1v (Z_to_bv 64 a) = mrestrict (ahid Aw model) M (Z_to_bv 64 a)) ->
  (forall model1, st_ok M model1 src tx tg sm cr LK Aw -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M model1) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
Proof using All.
  intros SO MS MG FRZ NEXT.
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  unfold PMSP.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R pc R1 pc1 M1v K HH AM MS MG FRZ).
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  apply NEXT. split; [exact MR|]. split; [exact SV|]. split; [exact LC|]. split; [exact PA|]. split; [exact IA|]. split; [exact BASE|].
  split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|].
  split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|]. split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL| exact CRK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma vpack M model src tx tg sm cr LK Aw :
  st_ok M model src tx tg sm cr LK Aw ->
  let H := ahid Aw model in let MV := mrestrict H M in
  L5.img_clear MV 65536 1282048 /\ L5.u64_at RSEGS MV 1309752 2147450880 /\ L5.u32_at RSEGS MV 1309760 1
  /\ (140735332487360 <= S <= 2 ^ 47 /\ S mod 16 = 0 /\ L5.writable RSEGS MV (S - 192) 192)
  /\ (forall k v, 8 <= k <= 192 -> L5.u64_at RSEGS M (S - k) v -> L5.u64_at RSEGS MV (S - k) v)
  /\ (6905856 <= os <= 140737488355032 /\ os mod 8 = 0 /\ (2147446784 + 17592186048512 <= os \/ os + 296 <= 2147446784))
  /\ L5KA.zeros_at MV ((os + 8) / 8 + 2147450880) 36 /\ L5.writable RSEGS MV os 296 /\ (forall a n, os <= a -> a + n <= os + 296 -> L5A.avis H a n)
  /\ (6905856 <= tb <= 140737488355304 /\ tb mod 8 = 0 /\ (2147446784 + 17592186048512 <= tb \/ tb + 24 <= 2147446784))
  /\ L5KA.zeros_at MV (tb / 8 + 2147450880) 3 /\ L5.writable RSEGS MV tb 24 /\ (forall a n, tb <= a -> a + n <= tb + 24 -> L5A.avis H a n)
  /\ os + 296 <= S - 192 /\ tb + 24 <= S - 192 /\ PMSPA.aobjA FF os 296 /\ PMSPA.aobjA FF tb 24.
Proof using All.
  intros (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK) H MV.
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof lay as LAY. pose proof aobjs as (AO & AOI & AT). destruct (frame_app _ _ _ _ _ _ HH) as (F1 & F2 & F3 & F4 & F5).
  pose proof (tsrc M src tx tg PA) as (PSF & PNI & PD & VS & _).
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model S 22528 192 HH STK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (PGSKA.src_visG L ar C HI LY HIok _ FF LK cr Aw M model os _ _ src S 22528 HH AO ltac:(lia) PSF PNI STK)
    as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & _ & OFS1 & OFS2).
  pose proof (PGTKA.tb_visG L ar C HI LY HIok _ FF LK cr Aw M model tb tx HH AT ltac:(lia) VS)
    as ((T1 & T8 & TBIG) & TZ & TW & TCE & TAV & _ & TFS1 & TFS2).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VIS & _).
  split; [exact V0|]. split; [exact V1|]. split; [exact V2|].
  split; [split; [lia| split; [exact A16| exact V3]]|].
  split.
  { intros k v Hk X. apply (proj2 (L5A.u64_at_vis H M (S - k) v (VIS (S - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  split; [split; [lia| split; [exact O8| exact OBIG]]|]. split; [exact OZ|]. split; [exact OW|]. split; [exact OAV|].
  split; [split; [lia| split; [exact T8| exact TBIG]]|]. split; [exact TZ|]. split; [exact TW|]. split; [exact TAV|].
  split; [lia|]. split; [lia|]. split; [exact AO| exact AT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lstate (R : bvmap 5 word) (M : word -> option byte) (model : Model) (src : PM.srcst) (tx : PM.vstr) (tg : Z) (sm : PM.strm) (cr : credit) (LK : list fframe) (Aw : list (Z * Z)) (w : Z) : Prop :=
  lregs R w /\ st_ok M model src tx tg sm cr LK Aw /\ acct src tx tg sm w /\ 1 <= w <= len.
Definition IHt (mu0 : Z) : Prop :=
  forall (fx : FPState) R M model src tx tg sm cr LK Aw w, PM.mu_src src sm < mu0 -> lstate R M model src tx tg sm cr LK Aw w ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb51a0 M model) K.

End Call.
End WithHeap.
End PGSSRA1.
