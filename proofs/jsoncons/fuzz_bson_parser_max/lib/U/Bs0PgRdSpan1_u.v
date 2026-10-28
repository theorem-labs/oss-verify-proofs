(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnParSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParKit
     PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnTxtKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PgSrd1_u PnSRdSpanP_u Bs0_code_r36ef4_36ef8_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgSrcKit.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSRS1.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Ltac kept_tac KS KP := intros x Hx; rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity); apply KP; exact Hx.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
#[local] Abbreviation own2 := PGSSR1.own2.

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (cr0 : credit).
Variables (S r len : Z) (T : PGS.towner) (OB : list (Z * Z)) (src0 : PM.srcst) (tb0 : PM.vstr) (tg0 : Z) (str : PM.vstr) (sm0 : PM.strm).
#[local] Abbreviation os := (PGS.tw_os T).
#[local] Abbreviation ois := (PGS.tw_ois T).
#[local] Abbreviation otb := (PGS.tw_otb T).
#[local] Abbreviation lo := (PGS.tw_lo T).
#[local] Abbreviation hi := (PGS.tw_hi T).
Hypothesis TOK : PGS.towner_ok RSEGS AD L HI T.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis K0 : K [].
Hypothesis SPLO : S <= lo.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UN0 : PM.unread src0 sm0 < 2 ^ 26.
Hypothesis FBS : PGS.fill_buffer_specG RSEGS AD L HI.
Hypothesis SRDS : PGS.srd_read_specG RSEGS AD L HI (pa_srd_read AD).
#[local] Abbreviation W0 := (PGSSR1.W0 T).
#[local] Abbreviation lay := (PGSSR1.lay L HI T TOK).
#[local] Abbreviation lay0 := (PGSSR1.lay0 L HI T TOK).
#[local] Abbreviation tsrc := (PGSSR1.tsrc L HI T OB TOK).
#[local] Abbreviation inW_W0' := (PGSSR1.inW_W0' L HI T TOK).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (tb' : PM.vstr) (tg' : Z)
                         (sm' : PM.strm) (cr' : credit) (ptr n : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
  ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src' ++ PM.vs_own tb' ++ OB) ptr n \/ (otb + 1 <= ptr /\ ptr + n <= otb + 24)) ->
  L5.defined M' ptr n ->
  PGS.tw_at T M' src' tb' tg' OB -> PM.iss_at RSEGS AD T3 M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5C.hpres L LBX S (PMSP.pm_scr 6) (PGS.W_srcfG os ois ++ [(otb, 24)]) M0 M' ->
  PMSP.credit_keep cr0 cr' (PM.pot_text L tb0 tg0) (PM.pot_text L tb' tg') ->
  model_but_vm model0 model' -> hi_heap HI (PM.src_own src' ++ PM.vs_own tb' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition saves4 (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18))).
Definition kept_rs (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
Definition memrel (M : word -> option byte) : Prop :=
  PMK.ek L LBX S 24576 W0 M0 M /\ PMK.dk L LBX S 24576 M0 M /\ L5C.stk (hl_sptop L) M S 24576.
Definition st_ok (M : word -> option byte) (model : Model) (src : PM.srcst) (tb : PM.vstr) (tg : Z) (sm : PM.strm) (cr : credit) : Prop :=
  memrel M /\ saves4 M /\ PGS.tw_at T M src tb tg OB /\ PM.iss_at RSEGS AD T3 M ois str sm
  /\ PMST.base_ok RSEGS AD M /\ PM.tb_ok tb tg
  /\ hi_heap HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) cr M (m_vmmaps model) /\ PMSP.model_ok model /\ model_but_vm model0 model
  /\ PMSP.credit_le (PM.pot_text L tb tg) cr
  /\ PMSP.credit_keep cr0 cr (PM.pot_text L tb0 tg0) (PM.pot_text L tb tg).
(* [comment removed for export] *)
Definition bregs (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 32) /\ getr R (reg 8) = Z_to_bv 64 len /\ getr R (reg 9) = Z_to_bv 64 os
  /\ getr R (reg 18) = Z_to_bv 64 otb /\ kept_rs R.

Lemma outside_W0 a : a < S -> L5.outside W0 a.
Proof using TOK SPLO. intros Ha r0 Hr0 Hin. assert (I : PMK.inW W0 a) by (exists r0; split; assumption). apply inW_W0' in I. lia. Qed.
Lemma base_keep M M' : PMK.ek L LBX S 24576 W0 M M' -> L5C.stk (hl_sptop L) M S 24576 -> PMST.base_ok RSEGS AD M -> PMST.base_ok RSEGS AD M'.
Proof using TOK SPLO KL SF LY.
  intros E (_ & SLO & _ & STOP & _) B. apply (PMKP.base_ok_keep RSEGS AD L KL SF LBX S 24576 W0 M M' E); [| | | |exact B].
  all: intros a Ha; apply outside_W0; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S] in Ha; destruct STOP; lia.
Qed.
Lemma unread_nn M model src tb tg sm cr : st_ok M model src tb tg sm cr ->
  0 <= PM.unread src sm /\ (PM.sm_st sm = 0 \/ PM.sm_st sm = 2) /\ 0 <= PM.sr_rem src <= PM.CHUNK /\ PM.sm_g sm <= PM.sm_eg sm.
Proof using All.
  intros (_ & _ & PA & IA & _).
  destruct (tsrc M src tb tg PA) as ((_ & _ & _ & _ & _ & _ & _ & Q8 & Q9 & Q10 & _) & _).
  destruct IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & ST) & _ & G1 & G2).
  unfold PM.unread. split; [lia|]. split; [exact ST|]. split; [unfold PM.CHUNK in *; lia| exact G2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma finish_rs (fx : FPState) R M model src tb tg sm cr (ptr n : Z) :
  getr R (reg 1) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 1))) -> getr R (reg 2) = Z_to_bv 64 S ->
  getr R (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 ptr -> getr R (reg 11) = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
  ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src ++ PM.vs_own tb ++ OB) ptr n \/ (otb + 1 <= ptr /\ ptr + n <= otb + 24)) ->
  L5.defined M ptr n -> st_ok M model src tb tg sm cr -> PMSP.src_step src0 src sm0 sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39384 M model) K.
Proof using All.
  intros E1 E2 E8 E9 E18 KP E10 E11 Hn Hn2 LOC DEF ((EK & DK & STK) & _ & PA & IA & BASE & TBOK & HH & MOK & MB & _ & CK) STEP.
  pose proof MOK as (Mh & Ml & Mm). pose proof RAok as (Hr1 & Hr2).
  assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMSP.cfg.
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx R M 0x39384 W_381ac r F_381ac ltac:(reflexivity) D_381ac RA Hr1 Hr2)|].
  apply (KONT fx R M model src tb tg sm cr ptr n); try assumption.
  - apply PMK.preserved_by_index. intros x Hx. unfold PMK.cs_all in Hx. cbn in Hx.
    destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
    destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
    destruct Hx as [<-|Hx]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite E18; apply Z_to_bv_bv_unsigned|].
    apply KP. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn; auto 12.
  - apply (PMK.hpres_of L LBX S 24576 W0 M0 M EK); [destruct STK as (_ & _ & _ & _ & D); exact D| exact DK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma src_callee_mem M M' src tb cr VM scr' (W' : list L5.range) :
  memrel M -> saves4 M -> hi_heap HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) cr M VM -> 0 <= scr' <= 24576 - 32 ->
  L5C.hpres L (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) (S - 32) scr' W' M M' ->
  (forall a, PMK.inW W' a -> PMK.inW W0 a \/ exists B m, In (B, m) (PM.src_own src ++ PM.vs_own tb) /\ B <= a < B + m) ->
  memrel M' /\ saves4 M' /\ PMK.ek L LBX S 24576 W0 M M'.
Proof using TOK SPLO HIok KL.
  intros (EK & DK & STK) SV HH Hs HP FP.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  set (LBc := PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) in *.
  assert (BR : PMFR.brange L LBc) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  pose proof (PGSSR1.own_apart L HI HIok (PM.src_own src ++ PM.vs_own tb) (OB ++ LBX) cr M VM ltac:(unfold LBc in HH; rewrite <- own2; exact HH)) as OWNF.
  assert (OWNLO : forall a B m, In (B, m) (PM.src_own src ++ PM.vs_own tb) -> B <= a < B + m -> a < S - 24576).
  { intros a B m Hin Ha. destruct (OWNF B m Hin) as (Q & _). lia. }
  assert (EKr : PMK.ek L LBc (S - 32) scr' W' M M') by (apply (PMK.ek_of_hpres L); exact HP).
  assert (STKr : L5C.stk (hl_sptop L) M (S - 32) scr').
  { apply (PMK.stk_call L M S 24576 (S - 32) scr' STK); [lia|lia|lia|]. replace (S - 32) with (S + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  assert (SC0 : 0 <= scr') by lia.
  assert (INC : incl LBX LBc) by (intros x Hx; unfold LBc; apply PGSSR1.in4; exact Hx).
  assert (EKn : PMK.ek L LBX S 24576 W0 M M').
  { apply (PMK.ek_weaken L LBX (OB ++ LBX) S 24576 S 24576 W0 W0 M M'); [| intros x Hx; apply in_or_app; right; exact Hx| intros x Hx; exact Hx| intros a Ha; exact Ha].
    apply (PMPK.ek_drop_own L (PM.src_own src ++ PM.vs_own tb) (OB ++ LBX) S 24576 W0 (W0 ++ (PM.src_own src ++ PM.vs_own tb)) M M').
    - rewrite <- own2. apply (PMK.ek_callee_in' RSEGS L KL LBc LBc S 24576 (S - 32) scr' (W0 ++ (PM.src_own src ++ PM.vs_own tb)) W' M M' HP (incl_refl _));
        [lia|lia|lia| destruct STOP; lia| exact (PMFR.brange_hi L LBc BR)|].
      intros a I. right. destruct (FP a I) as [(r0 & Hr0 & Hin)|(B & m & Hin & Ha)].
      + exists r0. split; [apply in_or_app; left; exact Hr0| exact Hin].
      + exists (B, m). split; [apply in_or_app; right; exact Hin| unfold L5.in_rng; cbn [fst snd]; lia].
    - exact OWNF.
    - intros a O. apply PGSSR1.outside_own. exact O. }
  assert (NOTW : forall a n, S - 32 <= a -> a + n <= S -> forall i, a <= i < a + n -> ~ PMK.inW W' i).
  { intros a n H1 H2 i Hi I. destruct (FP i I) as [I'|(B & m & Hin & Ha)]; [apply inW_W0' in I'; lia| apply (OWNLO i B m Hin) in Ha; lia]. }
  split; [split; [|split]|].
  - exact (PMK.ek_trans L LBX S 24576 W0 M0 M M' EK EKn).
  - apply (PMK.dk_trans L LBX S 24576 M0 M M' DK).
    apply (PMK.dk_callee L LBX LBc S 24576 (S - 32) scr' W' M M' HP INC); [lia| lia].
  - apply (PMK.stk_after RSEGS L KL LBc M M' S 24576 (S - 32) scr' W' STK HP); lia.
  - split; [|exact EKn].
    destruct SV as (S8 & S16 & S24 & S32).
    unfold saves4. repeat split; (apply (PMFR.u64_keep RSEGS L KL LBc (S - 32) scr' W' M M' EKr STKr SC0); [lia|lia| apply NOTW; lia| eassumption]).
Qed.

(* [comment removed for export] *)
Lemma stw_ok M tb tg : L5C.stk (hl_sptop L) M S 24576 -> PGS.owner_ok RSEGS AD L HI (PGS.src_of_tw T tb tg).
Proof using TOK SPLO HIok KL. intros (_ & SLO & _ & STOP & _). apply (PGSK.src_of_tw_ok RSEGS AD L HI KL HIok T tb tg TOK); [unfold hl_ceil; lia| lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma call_fill (fx : FPState) R M model src tb tg sm cr (X : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 32) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 (PM.sr_qc src) -> getr R (reg 12) = Z_to_bv 64 PM.CHUNK ->
  st_ok M model src tb tg sm cr ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (sm' : PM.strm) (c : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> PM.sm_g sm' = PM.sm_g sm + c ->
     (PM.sm_st sm = 0 -> c = Z.min PM.CHUNK (PM.sm_eg sm - PM.sm_g sm) /\ PM.sm_st sm' = (if Z.ltb c PM.CHUNK then 2 else 0)) ->
     (PM.sm_st sm = 2 -> c = 0 /\ PM.sm_st sm' = 2) ->
     PMSP.src_step src src sm sm' ->
     st_ok M' model src tb tg sm' cr ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x382d4 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 SO NEXT.
  pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  assert (STKr : L5C.stk (hl_sptop L) M (S - 32) (PMSP.pm_scr 3)).
  { apply (PMK.stk_call L M S 24576 (S - 32) (PMSP.pm_scr 3) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
    replace (S - 32) with (S + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof FBS as SR. unfold PGS.fill_buffer_specG, PGS.src_specG in SR. cbn [pa_fill_buffer AD PnLayoutS_u.ADDR_S] in SR.
  apply (SR (PGS.src_of_tw T tb tg) (stw_ok M tb tg STK) fx R M model K (PM.vs_own tb ++ OB) LBX cr (S - 32) X src str sm []);
    cbn [PGS.ow_at PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi PGS.ow_win PGS.src_of_tw].
  { rewrite <- app_assoc. exact HH. }
  { exact MOK. }
  { exact K0. }
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
    split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0| exact STKr]. }
  { lia. }
  { rewrite L5K.rl10. exact A10. }
  { unfold PGS.fill_args. rewrite L5K.rl11, L5K.rl12. split; [exact A11| exact A12]. }
  { reflexivity. }
  { exists OB. split; [reflexivity| exact PA]. }
  { exact IA. }
  { exact BASE. }
  { exact INCS. }
  intros fx' R' M' src' sm' RP (OB1 & EOB & PA') IA' STEP RES HP HH'.
  apply app_inv_head in EOB. subst OB1.
  change (PMSP.pm_scr 3) with 18432 in HP. rewrite app_nil_r in HP.
  destruct RES as (-> & c & Y10 & Hc & G & ST0 & ST2).
  apply (NEXT fx' R' M' sm' c RP Y10 Hc G ST0 ST2 STEP).
  rewrite <- app_assoc in HP, HH'.
  destruct (src_callee_mem M M' src tb cr _ 18432 (PGS.W_srcG os ois src) MR SV HH ltac:(lia) HP) as (MR' & SV' & EKn).
  { intros a I. destruct (PGSSR1.W_src_in T src a I) as [I'|I']; [left; exact I'| right].
    exists (PM.sr_qc src), PM.CHUNK. split; [unfold PM.src_own; left; reflexivity| exact I']. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact PA'|]. split; [exact IA'|].
  split; [exact (base_keep M M' EKn STK BASE)|]. split; [exact TBOK|].
  split; [exact HH'|]. split; [exact MOK|]. split; [exact MB|]. split; [exact CRL| exact CRK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma call_srd (fx : FPState) R M model src tb tg sm cr (X : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 32) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 otb -> getr R (reg 12) = Z_to_bv 64 len ->
  st_ok M model src tb tg sm cr -> PM.unread src sm < 2 ^ 26 -> PM.vs_size tb + PM.unread src sm < 2 ^ 26 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (tb' : PM.vstr) (tg' : Z) (sm' : PM.strm) (cr' : credit) (d : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 d -> 0 <= d <= len ->
     PMSP.consumed src src' sm sm' = d -> PM.vs_size tb' = PM.vs_size tb + d ->
     PMSP.src_step src src' sm sm' ->
     st_ok M' model' src' tb' tg' sm' cr' ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39398 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 SO UN UNS NEXT.
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  assert (STKr : L5C.stk (hl_sptop L) M (S - 32) (PMSP.pm_scr 5)).
  { apply (PMK.stk_call L M S 24576 (S - 32) (PMSP.pm_scr 5) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
    replace (S - 32) with (S + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof SRDS as SR. unfold PGS.srd_read_specG in SR. cbn [pa_srd_read AD PnLayoutS_u.ADDR_S] in SR.
  apply (SR T TOK fx R M model K OB LBX cr (S - 32) X len src tb tg str sm HH MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
    split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0| exact STKr]. }
  { lia. }
  { rewrite L5K.rl10. exact A10. }
  { rewrite L5K.rl11. exact A11. }
  { rewrite L5K.rl12. exact A12. }
  { exact Hlen. }
  { exact PA. }
  { exact IA. }
  { exact BASE. } { exact INCS. } { exact UN. } { exact UNS. } { exact CRL. }
  intros fx' R' M' model' src' tb' tg' sm' cr' d RP Y10 Hd CONS SZ PA' IA' STEP HP CK MB' HH'.
  change (PMSP.pm_scr 5) with 22528 in HP.
  apply (NEXT fx' R' M' model' src' tb' tg' sm' cr' d RP Y10 Hd CONS SZ STEP).
  assert (EKr : PMK.ek L LBX (S - 32) 22528 W0 M M') by (apply (PMK.ek_of_hpres L); exact HP).
  assert (SC0 : 0 <= 22528) by lia.
  assert (BR : PMFR.brange L LBX) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); intros x Hx; apply PGSSR1.in4; exact Hx).
  assert (EKn : PMK.ek L LBX S 24576 W0 M M').
  { apply (PMK.ek_callee_in' RSEGS L KL LBX LBX S 24576 (S - 32) 22528 W0 W0 M M' HP (incl_refl _));
      [lia|lia|lia| destruct STOP; lia| exact (PMFR.brange_hi L LBX BR)|].
    intros a I. right. exact I. }
  assert (NOTW : forall a n, S - 32 <= a -> a + n <= S -> forall i, a <= i < a + n -> ~ PMK.inW W0 i).
  { intros a n H1 H2 i Hi I. apply inW_W0' in I. lia. }
  pose proof (tsrc M' src' tb' tg' PA') as (_ & _ & _ & _ & TB').
  split; [split; [|split]|].
  - exact (PMK.ek_trans L LBX S 24576 W0 M0 M M' EK EKn).
  - apply (PMK.dk_trans L LBX S 24576 M0 M M' DK).
    apply (PMK.dk_callee L LBX LBX S 24576 (S - 32) 22528 W0 M M' HP); [apply incl_refl| lia| lia].
  - apply (PMK.stk_after RSEGS L KL LBX M M' S 24576 (S - 32) 22528 W0 STK HP); lia.
  - split.
    { destruct SV as (S8 & S16 & S24 & S32).
      unfold saves4. repeat split; (apply (PMFR.u64_keep RSEGS L KL LBX (S - 32) 22528 W0 M M' EKr ltac:(apply (PMK.stk_call L M S 24576 (S - 32) 22528 STK); [lia|lia|lia| replace (S - 32) with (S + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact A16]) SC0); [lia|lia| apply NOTW; lia| eassumption]). }
    split; [exact PA'|]. split; [exact IA'|].
    split; [exact (base_keep M M' EKn STK BASE)|]. split; [exact TB'|].
    split; [exact HH'|]. split; [exact (PMFR.model_ok_but_vm model model' MOK MB')|].
    split; [exact (L5C.model_but_vm_trans _ _ _ MB MB')|].
    split; [apply (PMPK.credit_le_keep cr cr' _ _ CRL CK)|].
    unfold PMSP.credit_keep in *. destruct CRK, CK. split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma st_piece M M1 model src src' tb tb' tg sm cr (P : Z -> Prop) :
  st_ok M model src tb tg sm cr -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, P a -> (os + 256 <= a < os + 296) \/ (otb <= a < otb + 24) \/ (exists c n q, tb = PM.VLong c n q /\ q <= a < q + c)) ->
  PM.src_fields_at RSEGS T3 M1 os ois (ois + 16) src' -> PM.sr_qc src' = PM.sr_qc src ->
  PM.vstr_at RSEGS T3 M1 otb tb' -> PM.tb_ok tb' tg -> PM.vs_own tb' = PM.vs_own tb -> PM.vs_cap tb' = PM.vs_cap tb ->
  hi_heap HI (PM.src_own src' ++ PM.vs_own tb' ++ OB ++ LBX) cr M1 (m_vmmaps model) ->
  st_ok M1 model src' tb' tg sm cr.
Proof using All.
  intros SO MG FRZ FP SF' QC VS' TB' OWN CAP HH1.
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  pose proof lay as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DJ1 & DJ2 & DJ3).
  set (LBc := PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) in HH.
  assert (BR : PMFR.brange L LBc) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  assert (HHo : hi_heap HI ((PM.src_own src ++ PM.vs_own tb) ++ (OB ++ LBX)) cr M (m_vmmaps model)) by (rewrite <- own2; exact HH).
  pose proof (PGSSR1.own_apart L HI HIok (PM.src_own src ++ PM.vs_own tb) (OB ++ LBX) cr M _ HHo) as OWNF.
  (* [comment removed for export] *)
  assert (NP : forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= os + 256 \/ os + 296 <= a) -> (a + 1 <= otb \/ otb + 24 <= a) ->
               (forall c n q, tb = PM.VLong c n q -> a + 1 <= q \/ q + c <= a) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha X Y W. apply FRZ; [exact Ha|]. intros Pa. destruct (FP a Pa) as [I|[I|(c & n & q & E & I)]]; [lia|lia|]. destruct (W c n q E); lia. }
  assert (TBB : forall c n q, tb = PM.VLong c n q -> In (q, c) LBc /\ 4096 <= q /\ q + c <= hl_ceil L /\
               forall B' m', In (B', m') (OB ++ LBX) -> q + c <= B' \/ B' + m' <= q).
  { intros c n q E. assert (IN : In (q, c) LBc) by (unfold LBc; rewrite E; apply in_or_app; right; left; reflexivity).
    destruct (BR _ _ IN) as (Q0 & _ & Q4). destruct (OWNF q c ltac:(rewrite E; apply in_or_app; right; left; reflexivity)) as (_ & _ & AP).
    split; [exact IN|]. split; [exact Q0|]. split; [exact Q4| exact AP]. }
  assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= os + 256 \/ os + 296 <= a) -> (a + m <= otb \/ otb + 24 <= a) -> hl_ceil L <= a ->
               L5C.agree_on M M1 a m).
  { intros a m Ha Hm X Y Wc i Hi. apply NP; [lia|lia|lia|]. intros c n q E. destruct (TBB c n q E) as (_ & _ & Q4 & _). lia. }
  assert (AGX : forall B m, In (B, m) (OB ++ LBX) -> L5C.agree_on M M1 B m).
  { intros B m Hin i Hi. destruct (BR B m ltac:(unfold LBc; rewrite own2; apply in_or_app; right; exact Hin)) as (Z0 & _ & Z4). unfold hl_ceil in Z4.
    apply NP; [lia|lia|lia|]. intros c n q E. destruct (TBB c n q E) as (_ & _ & _ & AP). destruct (AP B m Hin); lia. }
  assert (EKw : forall LB sp scr, incl LB (OB ++ LBX) -> PMK.ek L LB sp scr W0 M M1).
  { intros LB sp scr INC. apply (PMK.ek_piece L LB sp scr W0 M M1 P FRZ).
    intros a Ha CA NE OW Pa. destruct (FP a Pa) as [I|[I|(c & n & q & E & I)]].
    - apply (OW (os + 256, 40)); [unfold PGSSR1.W0, PGS.W_srcfG; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
    - apply (OW (otb, 24)); [unfold PGSSR1.W0; apply in_or_app; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
    - refine (PGSSR1.own_not_client L HI HIok (PM.src_own src ++ PM.vs_own tb) (OB ++ LBX) cr M _ q c a sp scr HHo _ I _).
      + rewrite E. apply in_or_app. right. left. reflexivity.
      + apply (PMK.client_mono L LB (OB ++ LBX) sp scr sp scr a CA INC). intros x Hx. exact Hx. }
  assert (HHn : hi_heap HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) cr M1 (m_vmmaps model)).
  { unfold PM.src_own. rewrite <- QC, <- OWN. unfold PM.src_own in HH1. exact HH1. }
  split; [split; [|split]|].
  - exact (PMK.ek_trans L LBX S 24576 W0 M0 M M1 EK (EKw LBX S 24576 ltac:(intros x Hx; apply in_or_app; right; exact Hx))).
  - apply (PMK.dk_trans L LBX S 24576 M0 M M1 DK). apply PMK.dk_grows. exact MG.
  - exact (PMK.stk_grows L M M1 S 24576 MG STK).
  - split; [destruct SV as (S8 & S16 & S24 & S32); unfold saves4; repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| eassumption])|].
    split.
    { apply (PGSSR1.tw_xfer L HI HIok LBX S T OB TOK SPLO M M1 src src' tb tb' tg tg cr (m_vmmaps model) 24576 S 0 [] PA HH STK); [lia|lia|lia| |constructor| exact SF'| exact QC| exact VS'| exact TB'].
      apply (PMK.hpres_of L (OB ++ LBX) S 0 _ M M1).
      + rewrite app_nil_r. exact (EKw (OB ++ LBX) S 0 (incl_refl _)).
      + intros i Hi. lia.
      + apply PMK.dk_grows. exact MG. }
    split.
    { apply (PMF.iss_at_agree RSEGS AD M M1 ois str sm); [lia|lia| apply AG; lia| |exact IA].
      intros c n p E. apply AGX. apply in_or_app. right. apply INCS. rewrite E. left. reflexivity. }
    split; [exact (base_keep M M1 (EKw LBX S 24576 ltac:(intros x Hx; apply in_or_app; right; exact Hx)) STK BASE)|].
    split; [exact TB'|]. split; [exact HH1|]. split; [exact MOK|]. split; [exact MB|].
    unfold PM.pot_text in *. rewrite CAP. split; [exact CRL| exact CRK].
Qed.

(* [comment removed for export] *)
Lemma src_keep_P M M1 model src tb tg sm cr (P : Z -> Prop) :
  st_ok M model src tb tg sm cr -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, P a -> ~ (os + 240 <= a < os + 296)) ->
  PM.src_fields_at RSEGS T3 M1 os ois (ois + 16) src.
Proof using All.
  intros SO MG FRZ NP. pose proof SO as ((EK & DK & STK) & SV & PA & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  destruct (tsrc M src tb tg PA) as ((F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _) & _).
  assert (AG : L5C.agree_on M M1 (os + 240) 56) by (intros i Hi; apply FRZ; [lia| intros Pa; apply (NP i Pa); lia]).
  unfold PM.src_fields_at.
  split; [apply (L5C.u64_at_agree RSEGS M M1); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact F1]|].
  split; [apply (L5C.u64_at_agree RSEGS M M1); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact F2]|].
  split; [apply (L5.defined_grows M M1 _ _ MG); exact F3|].
  split; [apply (L5C.u64_at_agree RSEGS M M1); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact F4]|].
  split; [apply (L5C.u64_at_agree RSEGS M M1); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact F5]|].
  split; [apply (L5C.u64_at_agree RSEGS M M1); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact F6]|].
  split; [apply (L5C.u64_at_agree RSEGS M M1); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact F7]|].
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split; [apply (L5.defined_grows M M1 _ _ MG); exact DC|]. split; exact I.
Qed.
Lemma vstr_keep_P M M1 model src tb tg sm cr (P : Z -> Prop) :
  st_ok M model src tb tg sm cr -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, P a -> ~ (otb <= a < otb + 24) /\ forall c n q, tb = PM.VLong c n q -> ~ (q <= a < q + c)) ->
  PM.vstr_at RSEGS T3 M1 otb tb.
Proof using All.
  intros SO MG FRZ NP. pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  destruct (tsrc M src tb tg PA) as (_ & _ & _ & VS & _).
  assert (BR : PMFR.brange L (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  apply (PMF.vstr_at_agree RSEGS M M1 otb tb); [lia|lia| | |exact VS].
  - intros i Hi. apply FRZ; [lia|]. intros Pa. apply (proj1 (NP i Pa)). lia.
  - intros c n p E. destruct (BR p c ltac:(rewrite E; apply in_or_app; right; apply in_or_app; left; left; reflexivity)) as (Q0 & _ & Q4). unfold hl_ceil in Q4.
    intros i Hi. apply FRZ; [lia|]. intros Pa. apply (proj2 (NP i Pa) c n p E). lia.
Qed.

End Call.
End WithHeap.
End PGSRS1.
