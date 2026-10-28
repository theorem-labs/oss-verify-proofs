(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8 PnLayout PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnTopS_u PnSHarnessStmts_u PnSHarnessKit_u PnSHarnessP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNH9.
Import PMS. Import PNH.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)

Section Stage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Variable R0 : bvmap 5 word.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variables (sp ra n : Z).
Variable LB0 : list (Z * Z).
Variable cr0 : credit.
Variable g : PNST.st.
Hypothesis Hn : 0 <= n < 2 ^ 26.
Hypothesis Hcr0 : PMSP.credit_le (PNTS.TOPK, PNTS.TOPB n) cr0.
Hypothesis Hgp : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Htp : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).

Lemma m16_2 x : x mod 16 = 0 -> x mod 2 = 0.
Proof. intros H. apply Z.mod_divide in H; [|lia]. destruct H as (q & ->). replace (q * 16) with ((q * 8) * 2) by lia. apply Z.mod_mul. lia. Qed.

(* [comment removed for export] *)
Definition H8b (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (src : PM.srcst) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  PNH.hcore L R0 M0 model0 sp ra LB0 R M model /\ PNHK.vstr_at M (PNH.fb sp + 744) s /\ PM.vs_size s = n
  /\ PNHK.iss_at M (PNH.fb sp + 472) s2 sm
  /\ PM.src_fields_at RSEGS PNH.T3 M (PNH.fb sp + 56) (PNH.fb sp + 472) (PNH.fb sp + 488) src /\ PM.nullis_at RSEGS AD PNH.T3 M (PNH.fb sp + 64)
  /\ PNH.hstat M true true ax /\ PNST.bax_le (PNST.st_ax g) ax
  /\ hi_heap HI (PM.src_own src ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr (PNH.P0 L n) PMSP.cr0
  /\ getr R (reg 1) = Z_to_bv 64 215064 /\ getr R (reg 10) = Z_to_bv 64 (sp - 728).

Lemma bytes_gone :
  PMS.opdel_spec L HI ->
  forall (fx : FPState) R M model cr s s2 src bb sm ax K,
    PNH.H8 L HI R0 M0 model0 sp ra n LB0 cr0 g R M model cr s s2 src bb sm ax -> K [] ->
    (forall (fx1 : FPState) R1 M1 model1,
        H8b R1 M1 model1 cr s s2 src sm ax ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x35cd0 M1 model1) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x34800 M model) K.
Proof using All.
  intros OPD fx R M model cr s s2 src bb sm ax K (CORE & VS & SZ & IA & SRC & NI & BBS & HST & EMONO & HH & CK) K0 KONT.
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
  pose proof STK as (A16f & SLO & SHI & STOP & _).
  pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & (Mh & Ml & Mm)).
  unfold PNH.fb, FRAME in BBS.
  destruct bb as [| b nb c].
  - (* [comment removed for export] *)
    destruct BBS as (_ & _ & (W0 & _ & _)). replace (sp - 784 + 360) with (sp - 424) in W0 by lia.
    cbn [PGV8.v8_own app] in HH.
    set (LBc := PM.src_own src ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
    assert (Bq : In (PM.sr_qc src, PM.CHUNK) LBc) by (unfold LBc, PM.src_own; cbn; auto).
    assert (BRc : PNHK.brange L LBc) by (apply (PNHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
    assert (LBhic : forall x, In x LBc -> fst x + snd x <= hl_ceil L) by (intros (B & m) Hx; destruct (BRc B m Hx) as (_ & _ & Q); exact Q).
    assert (SCx : 0 <= 65536 - 784) by lia.
    LeanFeed.pfeed P (PNSHP.bhnVn_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A10 & A12 & C768)); PMK.pvz_clrT.
    set (P := fun a => sp - 768 <= a < sp - 768 + 8).
    assert (PF : forall a, P a -> PNH.fb sp <= a < PNH.fb sp + 784) by (intros a X; unfold P in X; unfold PNH.fb, FRAME; lia).
    unfold PMSP.cfg.
    apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x34800 R1 0x35cd0 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
    { intros a Pa. apply PF in Pa. unfold PNH.fb, FRAME in Pa. left. lia. }
    { intros a. apply PMK.rng_dec. }
    intros HH1.
    apply (KONT fx1 R1 M1 model). unfold H8b.
    split. { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 P CORE MG FRZ); [intros a X; unfold P in X; unfold PNH.fb, FRAME; lia| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
             intros k Hk. apply KS. revert k Hk. apply PNH.CSK_in. vm_compute. reflexivity. }
    split. { eapply (PNHK.vstr_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VS].
             - intros i Hi X. unfold P in X. unfold PNH.fb, FRAME in Hi. lia.
             - intros x Hx; unfold LBc; rewrite !in_app_iff; auto 12. }
    split; [exact SZ|].
    split. { eapply (PNHK.iss_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact IA].
             - intros i Hi X. unfold P in X. unfold PNH.fb, FRAME in Hi. lia.
             - intros x Hx; unfold LBc; rewrite !in_app_iff; auto 12. }
    split. { eapply (PNHK.src_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact Bq|exact SRC].
             intros i Hi X. unfold P in X. unfold PNH.fb, FRAME in Hi. lia. }
    split. { eapply (PNHK.nullis_keep_p M M1 P FRZ); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact NI]. intros i Hi X. unfold P in X. unfold PNH.fb, FRAME in Hi. lia. }
    split. { apply (PNHK.hstat_piece L LY sp LBc M M1 P FRZ PF true _ _ STK LBhic HST). }
    split; [exact EMONO|]. split; [exact HH1|]. split; [exact CK|].
    split; [exact A1| exact A10].
  - (* [comment removed for export] *)
    destruct BBS as (_ & _ & (W0 & W8 & W16 & Hnb & Hc & Hb & Hal & DB & _)).
    replace (sp - 784 + 360) with (sp - 424) in W0 by lia. replace (sp - 784 + 360 + 16) with (sp - 408) in W16 by lia.
    assert (W8' : L5.u64_at RSEGS M (sp - 416) (b - (2 ^ 64 - 1 - nb) + 18446744073709551615)).
    { replace (sp - 416) with (sp - 784 + 360 + 8) by lia. replace (b - (2 ^ 64 - 1 - nb) + 18446744073709551615) with (b + nb) by lia. exact W8. }
    set (LBX := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
    set (LBc := PM.src_own src ++ PGV8.v8_own (PGV8.V8Blk b nb c) ++ LBX) in *.
    set (LB7 := PM.src_own src ++ LBX).
    assert (Bt : In (b, c) LBc) by (unfold LBc; rewrite !in_app_iff; cbn [PGV8.v8_own In]; auto 10).
    assert (Bq : In (PM.sr_qc src, PM.CHUNK) LBc) by (unfold LBc, PM.src_own; cbn; auto).
    assert (BRc : PNHK.brange L LBc) by (apply (PNHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
    assert (LBhic : forall x, In x LBc -> fst x + snd x <= hl_ceil L) by (intros (B & m) Hx; destruct (BRc B m Hx) as (_ & _ & Q); exact Q).
    assert (SCx : 0 <= 65536 - 784) by lia.
    destruct (BRc _ _ Bt) as (Pb0 & Pb1 & Pb4).
    assert (Hb47 : b < 2 ^ 47) by lia.
    pose proof (m16_2 b Hal) as Hal2.
    LeanFeed.pfeed P (PNSHP.bhnVl_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => b | 34%nat => b + c | 38%nat => 2 ^ 64 - 1 - nb | _ => 0 end)) ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ0 & HX)); PMK.pvz_clrT.
    lazymatch type of HX with
    | (?MSt /\ _ /\ ?A1t /\ ?A10t /\ ?A11t /\ _ /\ ?C0t /\ _ /\ _) \/ _ =>
        assert (HXc : MSt /\ (forall k, In k PNH.CSK -> getr R1 (reg k) = getr R (reg k)) /\ getr R1 (reg 2) = getr R (reg 2) /\ A1t /\ A10t /\ A11t /\ C0t)
    end.
    { destruct HX as [(MS & KS & A1 & A10 & A11 & _ & C0 & _ & _) | (MS & KS & A1 & A10 & A11 & _ & _ & _ & C0 & _ & _)];
        (split; [exact MS|]); (split; [intros k Hk; apply KS; revert k Hk; apply PNH.CSK_in; vm_compute; reflexivity|]);
        (split; [apply KS; PMK.inl|]); exact (conj A1 (conj A10 (conj A11 C0))). }
    clear HX. destruct HXc as (MS & KSc & R1sp & A1 & A10 & A11 & C0).
    set (P := fun a => sp - 768 <= a < sp - 768 + 8 \/ sp - 416 <= a < sp - 416 + 8).
    assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha NP. unfold P in NP. apply FRZ0; [exact Ha| |]; intros X; apply NP; lia. }
    assert (PF : forall a, P a -> PNH.fb sp <= a < PNH.fb sp + 784) by (intros a X; unfold P in X; unfold PNH.fb, FRAME; lia).
    unfold PMSP.cfg.
    apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x34800 R1 0x56720 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
    { intros a Pa. apply PF in Pa. unfold PNH.fb, FRAME in Pa. left. lia. }
    { intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    assert (CORE1 : PNH.hcore L R0 M0 model0 sp ra LB0 R1 M1 model).
    { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 P CORE MG FRZ); [intros a X; unfold P in X; unfold PNH.fb, FRAME; lia| rewrite R1sp; exact Rsp|].
      exact KSc. }
    assert (VS1 : PNHK.vstr_at M1 (PNH.fb sp + 744) s).
    { eapply (PNHK.vstr_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VS].
      - intros i Hi X. unfold P in X. unfold PNH.fb, FRAME in Hi. lia.
      - intros x Hx; unfold LBc, LBX; rewrite !in_app_iff; auto 12. }
    assert (IA1 : PNHK.iss_at M1 (PNH.fb sp + 472) s2 sm).
    { eapply (PNHK.iss_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact IA].
      - intros i Hi X. unfold P in X. unfold PNH.fb, FRAME in Hi. lia.
      - intros x Hx; unfold LBc, LBX; rewrite !in_app_iff; auto 12. }
    assert (SRC1 : PM.src_fields_at RSEGS PNH.T3 M1 (PNH.fb sp + 56) (PNH.fb sp + 472) (PNH.fb sp + 488) src).
    { eapply (PNHK.src_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact Bq|exact SRC].
      intros i Hi X. unfold P in X. unfold PNH.fb, FRAME in Hi. lia. }
    assert (NI1 : PM.nullis_at RSEGS AD PNH.T3 M1 (PNH.fb sp + 64)).
    { eapply (PNHK.nullis_keep_p M M1 P FRZ); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact NI]. intros i Hi X. unfold P in X. unfold PNH.fb, FRAME in Hi. lia. }
    assert (HST1 : PNH.hstat M1 true true ax) by (apply (PNHK.hstat_piece L LY sp LBc M M1 P FRZ PF true _ _ STK LBhic HST)).
    pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M1 model CORE1) as (_ & Rsp1 & _ & _ & _ & STK1).
    pose proof CORE1 as (_ & Hcs1 & _).
    assert (STKd : L5C.stk (hl_sptop L) M1 (sp - 784) PMSP.OPDEL_SCR).
    { apply (PMK.stk_call L M1 (sp - 784) (65536 - 784) (sp - 784) PMSP.OPDEL_SCR STK1); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia| exact A16f]. }
    unfold PMS.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OPD.
    apply (OPD fx1 R1 M1 model K LBc cr b c (sp - 784) 215056 HH1).
    { repeat split; assumption. }
    { exact K0. }
    { exact Bt. }
    { rewrite L5K.rl10. exact A10. }
    { rewrite L5K.rl1. exact A1. }
    { split; [lia| reflexivity]. }
    { rewrite L5K.rl2. exact Rsp1. }
    { rewrite L5K.rl4. rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto). exact Htp. }
    { exact STKd. }
    intros fx2 R2 M2 model2 RP HP MB HH2.
    assert (ELB : lb_remove b LBc = LB7).
    { pose proof (proj1 (proj2 (hio_wf L SCFG HI HIok LBc cr M _ HH))) as ND.
      unfold LBc, LB7. apply (PNHK.lb_remove_mid b c); exact ND. }
    rewrite ELB in HP, HH2.
    assert (EKd : PMK.ek L LB7 (sp - 784) PMSP.OPDEL_SCR [] M1 M2) by (apply (PMK.ek_of_hpres L); exact HP).
    assert (SCd : 0 <= PMSP.OPDEL_SCR) by (unfold PMSP.OPDEL_SCR; lia).
    assert (BR7 : PNHK.brange L LB7) by (apply (PNHK.brange_of_heap L HI LY HIok LB7 LB7 cr M2 _ HH2); apply incl_refl).
    assert (WSTD : forall a, PMK.inW [] a -> PNH.fb sp <= a \/ 65536 <= a < 962560) by (intros a (r & [] & _)).
    assert (N0 : forall a, ~ PMK.inW [] a) by (intros a (r & [] & _)).
    assert (CORE2 : PNH.hcore L R0 M0 model0 sp ra LB0 R2 M2 model2).
    { apply (PNHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M1 model R2 M2 model2 LB7 PMSP.OPDEL_SCR [] CORE1 RP HP);
        [unfold LB7, LBX; repeat apply incl_appr; apply incl_refl| unfold PMSP.OPDEL_SCR, SCR, FRAME; lia| |exact MB].
      intros a I. destruct (N0 a I). }
    assert (VS2 : PNHK.vstr_at M2 (PNH.fb sp + 744) s).
    { eapply (PNHK.vstr_keep L LY sp LB7 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR7 WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VS1].
      - intros i _. apply N0.
      - intros x Hx; unfold LB7, LBX; rewrite !in_app_iff; auto 12. }
    assert (IA2 : PNHK.iss_at M2 (PNH.fb sp + 472) s2 sm).
    { eapply (PNHK.iss_keep L LY sp LB7 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR7 WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact IA1].
      - intros i _. apply N0.
      - intros x Hx; unfold LB7, LBX; rewrite !in_app_iff; auto 12. }
    assert (SRC2 : PM.src_fields_at RSEGS PNH.T3 M2 (PNH.fb sp + 56) (PNH.fb sp + 472) (PNH.fb sp + 488) src).
    { eapply (PNHK.src_keep L LY sp LB7 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR7 WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact SRC1].
      - intros i _. apply N0.
      - unfold LB7, PM.src_own. cbn. auto. }
    assert (NI2 : PM.nullis_at RSEGS AD PNH.T3 M2 (PNH.fb sp + 64)).
    { eapply (PNHK.nullis_keep L LY sp LB7 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact NI1]. intros i _. apply N0. }
    assert (HST2 : PNH.hstat M2 true true ax).
    { apply (PNHK.hstat_keep L LY LB7 (sp - 784) PMSP.OPDEL_SCR [] M1 M2 EKd); [|exact HST1]. intros a I. destruct (N0 a I). }
    (* [comment removed for export] *)
    pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R2 M2 model2 CORE2) as (_ & Rsp2 & _ & _ & WR2 & _).
    pose proof CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Mh2 & Ml2 & Mm2)).
    LeanFeed.pfeed PI (PNSHP.bhnI_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct PI as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & A1i & A10i)); PMK.pvz_clrT.
    assert (EM : M3 = M2) by (apply functional_extensionality; exact FR3). subst M3.
    apply (PMK.spiece_ro RSEGS model2 fx2 fx3 R2 0x34810 R3 0x35cd0 M2 K Mh2 Ml2 MS3).
    apply (KONT fx3 R3 M2 model2). unfold H8b.
    split. { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R2 M2 model2 R3 M2 (fun _ => False) CORE2 MG3); [intros a Ha _; reflexivity| intros a []| rewrite (KS3 2%nat) by PMK.inl; exact Rsp2|].
             intros k Hk. apply KS3. revert k Hk. apply PNH.CSK_in. vm_compute. reflexivity. }
    fold LBX. fold LB7.
    do 9 (split; [assumption|]). split; [exact A1i| exact A10i].
Qed.

Lemma stage9 :
  PMS.opdel_spec L HI -> PMS.src_dtor_spec L HI ->
  forall (fx : FPState) R M model cr s s2 src bb sm ax K,
    PNH.H8 L HI R0 M0 model0 sp ra n LB0 cr0 g R M model cr s s2 src bb sm ax -> K [] ->
    (forall (fx1 : FPState) R1 M1 model1,
        PNH.H9 L HI R0 M0 model0 sp ra n LB0 cr0 g R1 M1 model1 cr s s2 sm ax ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x34818 M1 model1) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x34800 M model) K.
Proof using All.
  intros OPD SDT fx R M model cr s s2 src bb sm ax K H8 K0 KONT.
  apply (bytes_gone OPD fx R M model cr s s2 src bb sm ax K H8 K0).
  clear fx R M model H8. intros fx R M model (CORE & VS & SZ & IA & SRC & NI & HST & EMONO & HH & CK & A1 & A10).
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
  pose proof STK as (A16f & SLO & SHI & STOP & _).
  pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & MOK).
  set (LBX := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
  set (LBc := PM.src_own src ++ LBX) in *.
  assert (Bq : In (PM.sr_qc src, PM.CHUNK) LBc) by (unfold LBc, PM.src_own; cbn; auto).
  assert (SC2 : 0 <= PMSP.pm_scr 2) by (unfold PMSP.pm_scr; lia).
  assert (STKc : L5C.stk (hl_sptop L) M (sp - 784) (PMSP.pm_scr 2)).
  { apply (PMK.stk_call L M (sp - 784) (65536 - 784) (sp - 784) (PMSP.pm_scr 2) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16f]. }
  unfold PNH.fb, FRAME in SRC, NI.
  unfold PMS.src_dtor_spec, PMSP.src_dtor_spec in SDT.
  apply (SDT fx R M model K LBc cr (sp - 784 + 56) (sp - 784 + 472) (sp - 784 + 488) (sp - 784) 215064 src HH MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp|].
    split; [rewrite (Hcs 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKc. }
  { rewrite L5K.rl10. rewrite A10. f_equal. lia. }
  { lia. }
  { lia. }
  { replace (sp - 784 + 56) with (sp - 784 + 7 * 8) by lia. rewrite Z.mod_add by lia. apply Z.mod_divide in A16f; [|lia]. destruct A16f as (q & ->). replace (q * 16) with ((q * 2) * 8) by lia. apply Z.mod_mul. lia. }
  { exact SRC. }
  { replace (sp - 784 + 56 + 8) with (sp - 784 + 64) by lia. exact NI. }
  { exact Bq. }
  { exact BASE. }
  intros fx2 R2 M2 model2 RP HP MB HH2.
  assert (ELB : lb_remove (PM.sr_qc src) LBc = LBX).
  { unfold LBc, PM.src_own. cbn [app lb_remove fst]. rewrite Z.eqb_refl. reflexivity. }
  rewrite ELB in HP, HH2.
  set (W2 := [(sp - 784 + 56, 296)] : list L5.range) in *.
  assert (WC2 : forall a, PMK.inW W2 a -> sp - 784 + 56 <= a < sp - 784 + 352).
  { intros a (r & Hin & Hr). destruct Hin as [<-|[]]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (EK2 : PMK.ek L LBX (sp - 784) (PMSP.pm_scr 2) W2 M M2) by (apply (PMK.ek_of_hpres L); exact HP).
  assert (BRX : PNHK.brange L LBX) by (apply (PNHK.brange_of_heap L HI LY HIok LBX LBX cr M2 _ HH2); apply incl_refl).
  assert (WSTD : forall a, PMK.inW W2 a -> PNH.fb sp <= a \/ 65536 <= a < 962560) by (intros a I; apply WC2 in I; left; unfold PNH.fb, FRAME; lia).
  apply (KONT fx2 R2 M2 model2). unfold PNH.H9.
  split. { apply (PNHK.hcore_call L LY R0 M0 model0 sp ra LB0 R M model R2 M2 model2 LBX (PMSP.pm_scr 2) W2 CORE RP HP);
             [unfold LBX; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |exact MB].
           intros a I. left. apply WC2 in I. unfold PNH.fb, FRAME. lia. }
  split. { eapply (PNHK.vstr_keep L LY sp LBX (PMSP.pm_scr 2) W2 M M2 EK2 STKc SC2 BRX WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VS].
           - intros i Hi I. apply WC2 in I. unfold PNH.fb, FRAME in Hi. lia.
           - unfold LBX. apply incl_appr. apply incl_appl. apply incl_refl. }
  split; [exact SZ|].
  split. { eapply (PNHK.iss_keep L LY sp LBX (PMSP.pm_scr 2) W2 M M2 EK2 STKc SC2 BRX WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact IA].
           - intros i Hi I. apply WC2 in I. unfold PNH.fb, FRAME in Hi. lia.
           - unfold LBX. apply incl_appl. apply incl_refl. }
  split. { apply (PNHK.hstat_keep L LY LBX (sp - 784) (PMSP.pm_scr 2) W2 M M2 EK2); [|exact HST]. intros a I. apply WC2 in I. left. lia. }
  split; [exact EMONO|]. split; [exact HH2| exact CK].
Qed.

End Stage.
End PNH9.
