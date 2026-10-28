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

Module PNH10.
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


(* [comment removed for export] *)
Lemma iosb_revptr (M M' : word -> option byte) o vp vp' rdb st :
  0 <= o -> o + 152 <= 2 ^ 64 -> L5C.agree_on M M' (o + 8) 144 -> L5.u64_at RSEGS M' o vp' -> L5.defined M' o 152 ->
  PM.iosb_at RSEGS AD PNH.T3 M o vp rdb st -> PM.iosb_at RSEGS AD PNH.T3 M' o vp' rdb st.
Proof.
  intros Ho Ho' AG V D' (H0 & H32 & H36 & H40 & H48 & Z & D & _ & ST).
  assert (S : forall a' n', o + 8 <= a' -> a' + n' <= o + 152 -> L5C.agree_on M M' a' n') by (intros a' n' X Y; apply (L5C.agree_on_sub M M' (o + 8) 144 a' n' AG); lia).
  split; [exact V|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply S; lia|lia|lia|exact H32]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply S; lia|lia|lia|exact H36]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply S; lia|lia|lia|exact H40]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply S; lia|lia|lia|exact H48]|].
  split; [apply (PMF.zeros_at_agree M M'); [apply S; lia|exact Z]|].
  split; [exact D'|]. split; [exact I| exact ST].
Qed.

(* [comment removed for export] *)
Definition H7b (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s : PM.vstr) (be : PNST.bax) : Prop :=
  PNH.hcore L R0 M0 model0 sp ra LB0 R M model /\ PNHK.vstr_at M (PNH.fb sp + 744) s
  /\ L5.u64_at RSEGS M (PNH.fb sp + 496) (pa_classic_imp AD)
  /\ (exists vp st, PM.iosb_at RSEGS AD PNH.T3 M (PNH.fb sp + 592) vp (PNH.fb sp + 488) st)
  /\ PNH.hstat M true true be /\ PNST.bax_le (PNST.st_ax g) be
  /\ hi_heap HI (PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr (PNH.P0 L n) PMSP.cr0
  /\ getr R (reg 1) = Z_to_bv 64 215168 /\ getr R (reg 10) = Z_to_bv 64 (sp - 288).

Lemma strbuf_gone :
  PMS.opdel_spec L HI ->
  forall (fx : FPState) R M model cr s s2 sm be K,
    PNH.H9 L HI R0 M0 model0 sp ra n LB0 cr0 g R M model cr s s2 sm be -> K [] ->
    (forall (fx1 : FPState) R1 M1 model1,
        H7b R1 M1 model1 cr s be ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x81cb4 M1 model1) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x34818 M model) K.
Proof using All.
  intros OPD fx R M model cr s s2 sm be K (CORE & VS & SZ & IA & HST & EMONO & HH & CK) K0 KONT.
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
  pose proof STK as (A16f & SLO & SHI & STOP & _).
  pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & (Mh & Ml & Mm)).
  pose proof BASE as (IMG & _). change (L5.img_clear M 65536 754672) in IMG.
  set (LBc := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
  assert (BRc : PNHK.brange L LBc) by (apply (PNHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
  assert (LBhic : forall x, In x LBc -> fst x + snd x <= hl_ceil L) by (intros (B & m) Hx; destruct (BRc B m Hx) as (_ & _ & Q); exact Q).
  assert (SCx : 0 <= 65536 - 784) by lia.
  assert (INCs : incl (PM.vs_own s) LBc) by (unfold LBc; apply incl_appr; apply incl_appl; apply incl_refl).
  unfold PNH.fb, FRAME in IA.
  destruct IA as (I0 & ID & _ & I16 & I24 & I32 & I40 & I48 & I64 & IVS & I104 & I112 & IOS & IEG & IG).
  set (P := fun a => (sp - 312 <= a < sp - 312 + 8) \/ (sp - 296 <= a < sp - 296 + 8) \/ (sp - 192 <= a < sp - 192 + 8)).
  assert (PF : forall a, P a -> PNH.fb sp <= a < PNH.fb sp + 784) by (intros a [X|[X|X]]; unfold PNH.fb, FRAME; lia).
  assert (PF6 : forall a, P a -> PNH.fb sp <= a < PNH.fb sp + 768) by (intros a [X|[X|X]]; unfold PNH.fb, FRAME; lia).
  assert (PDEC : forall a, {P a} + {~ P a}) by (intros a; apply PMK.or_dec; [apply PMK.rng_dec| apply PMK.or_dec; apply PMK.rng_dec]).
  assert (AFTER : forall R1 M1, mem_grows M M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
            getr R1 (reg 2) = Z_to_bv 64 (PNH.fb sp) -> (forall k, In k CSK -> getr R1 (reg k) = getr R (reg k)) -> L5.u64_at RSEGS M1 (sp - 192) 740832 ->
            PNH.hcore L R0 M0 model0 sp ra LB0 R1 M1 model /\ PNHK.vstr_at M1 (PNH.fb sp + 744) s /\ L5.u64_at RSEGS M1 (PNH.fb sp + 496) (pa_classic_imp AD)
            /\ PM.iosb_at RSEGS AD PNH.T3 M1 (PNH.fb sp + 592) 740832 (PNH.fb sp + 488) (PM.sm_st sm) /\ PNH.hstat M1 true true be).
  { intros R1 M1 MG FRZ Rsp1 KS1 C192.
    split. { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 P CORE MG FRZ PF6 Rsp1 KS1). }
    split. { eapply (PNHK.vstr_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact INCs|exact VS].
             intros i Hi [X|[X|X]]; unfold PNH.fb, FRAME in Hi; lia. }
    split. { unfold PNH.fb, FRAME. eapply (PNHK.u64_keep_p M M1 P FRZ); [lia|lia| |replace (sp - 784 + 496) with (sp - 784 + 472 + 24) by lia; exact I24]. intros i Hi [X|[X|X]]; lia. }
    split. { unfold PNH.fb, FRAME. replace (sp - 784 + 488) with (sp - 784 + 472 + 16) by lia. replace (sp - 784 + 592) with (sp - 784 + 472 + 120) by lia.
             apply (iosb_revptr M M1 _ (pa_vp_iss_ios AD) 740832 _ _); [lia|lia| | | |exact IOS].
             - apply (PNHK.agp M M1 P FRZ); [lia|lia|]. intros i Hi [X|[X|X]]; lia.
             - replace (sp - 784 + 472 + 120) with (sp - 192) by lia. exact C192.
             - destruct IOS as (_ & _ & _ & _ & _ & _ & D & _). intros i Hi. apply MG. apply D. exact Hi. }
    apply (PNHK.hstat_piece L LY sp LBc M M1 P FRZ PF true _ _ STK LBhic HST). }
  destruct IVS as (SD & _ & IVS). destruct s2 as [n2 | c2 n2 p2].
  - (* [comment removed for export] *)
    destruct IVS as (Hn2 & SB0).
    pose proof (PMF.even_byte n2) as EVB.
    LeanFeed.pfeed PJ (PNSHP.bhnJs_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => 2 * n2 | _ => 0 end)) ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct PJ as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ0 & MS & KS & A1 & A8 & A10 & A11 & A12 & C296 & C192 & C312)); PMK.pvz_clrT.
    assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; left; exact X| intro X; apply N; right; right; exact X]. }
    unfold PMSP.cfg.
    apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x34818 R1 0x81cb4 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
    { intros a Pa. apply PF in Pa. unfold PNH.fb, FRAME in Pa. left. lia. }
    { exact PDEC. }
    intros HH1.
    destruct (AFTER R1 M1 MG FRZ) as (CORE1 & VS1 & LC1 & IOS1 & HST1); [rewrite (KS 2%nat) by PMK.inl; exact Rsp| |exact C192|].
    { intros k0 Hk0. apply KS. revert k0 Hk0. apply PNH.CSK_in. vm_compute. reflexivity. }
    apply (KONT fx1 R1 M1 model). unfold H7b.
    split; [exact CORE1|]. split; [exact VS1|]. split; [exact LC1|]. split; [exists 740832, (PM.sm_st sm); exact IOS1|].
    split; [exact HST1|]. split; [exact EMONO|]. split; [exact HH1|]. split; [exact CK|]. split; [exact A1| exact A10].
  - (* [comment removed for export] *)
    destruct IVS as (SW0 & SW8 & SW16 & Hn2 & Hc & Hc2 & SBP & _).
    assert (Bt : In (p2, c2) LBc) by (unfold LBc, PM.vs_own; cbn; auto).
    assert (Hc64 : 0 <= c2 + 1 < 2 ^ 64) by lia.
    pose proof (PMF.u8_of_u64 RSEGS M _ _ Hc64 SW0) as SB0.
    pose proof (PMF.odd_byte c2 Hc2 ltac:(lia)) as ODB.
    pose proof (Z.mod_pos_bound (c2 + 1) 256 ltac:(lia)) as HVB.
    set (vb := (c2 + 1) mod 256) in *.
    destruct (BRc _ _ Bt) as (Pb0 & Pb1 & Pb4).
    assert (Hp47 : p2 < 2 ^ 47) by lia.
    LeanFeed.pfeed PJ (PNSHP.bhnJl_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => vb | 37%nat => p2 | _ => 0 end)) ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct PJ as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ0 & MS & KS & A1 & A8 & A10 & A12 & C296 & C192 & C312)); PMK.pvz_clrT.
    assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; left; exact X| intro X; apply N; right; right; exact X]. }
    unfold PMSP.cfg.
    apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x34818 R1 0x56720 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
    { intros a Pa. apply PF in Pa. unfold PNH.fb, FRAME in Pa. left. lia. }
    { exact PDEC. }
    intros HH1.
    destruct (AFTER R1 M1 MG FRZ) as (CORE1 & VS1 & LC1 & IOS1 & HST1); [rewrite (KS 2%nat) by PMK.inl; exact Rsp| |exact C192|].
    { intros k0 Hk0. apply KS. revert k0 Hk0. apply PNH.CSK_in. vm_compute. reflexivity. }
    clear AFTER.
    (* [comment removed for export] *)
    pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M1 model CORE1) as (_ & Rsp1 & _ & _ & _ & STK1).
    pose proof CORE1 as (_ & Hcs1 & _).
    assert (STKd : L5C.stk (hl_sptop L) M1 (sp - 784) PMSP.OPDEL_SCR).
    { apply (PMK.stk_call L M1 (sp - 784) (65536 - 784) (sp - 784) PMSP.OPDEL_SCR STK1); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia| exact A16f]. }
    unfold PMS.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OPD.
    apply (OPD fx1 R1 M1 model K LBc cr p2 c2 (sp - 784) 215144 HH1).
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
    set (LB8 := PM.vs_own s ++ LB0) in *.
    assert (ELB : lb_remove p2 LBc = LB8).
    { unfold LBc, PM.vs_own at 1. cbn [app lb_remove fst]. rewrite Z.eqb_refl. reflexivity. }
    rewrite ELB in HP, HH2.
    assert (EKd : PMK.ek L LB8 (sp - 784) PMSP.OPDEL_SCR [] M1 M2) by (apply (PMK.ek_of_hpres L); exact HP).
    assert (SCd : 0 <= PMSP.OPDEL_SCR) by (unfold PMSP.OPDEL_SCR; lia).
    assert (BR8 : PNHK.brange L LB8) by (apply (PNHK.brange_of_heap L HI LY HIok LB8 LB8 cr M2 _ HH2); apply incl_refl).
    assert (LBhi8 : forall x, In x LB8 -> fst x + snd x <= hl_ceil L) by (intros (B & m) Hx; destruct (BR8 B m Hx) as (_ & _ & Q); exact Q).
    assert (WSTD : forall a, PMK.inW [] a -> PNH.fb sp <= a \/ 65536 <= a < 962560) by (intros a (r & [] & _)).
    assert (N0 : forall a, ~ PMK.inW [] a) by (intros a (r & [] & _)).
    assert (CORE2 : PNH.hcore L R0 M0 model0 sp ra LB0 R2 M2 model2).
    { apply (PNHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M1 model R2 M2 model2 LB8 PMSP.OPDEL_SCR [] CORE1 RP HP);
        [unfold LB8; apply incl_appr; apply incl_refl| unfold PMSP.OPDEL_SCR, SCR, FRAME; lia| |exact MB].
      intros a I. destruct (N0 a I). }
    assert (VS2 : PNHK.vstr_at M2 (PNH.fb sp + 744) s).
    { eapply (PNHK.vstr_keep L LY sp LB8 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR8 WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VS1].
      - intros i _. apply N0.
      - unfold LB8. apply incl_appl. apply incl_refl. }
    assert (LC2 : L5.u64_at RSEGS M2 (PNH.fb sp + 496) (pa_classic_imp AD)).
    { eapply (PNHK.u64_keep L LY sp LB8 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact LC1]. intros i _. apply N0. }
    assert (IOS2 : PM.iosb_at RSEGS AD PNH.T3 M2 (PNH.fb sp + 592) 740832 (PNH.fb sp + 488) (PM.sm_st sm)).
    { apply (PMF.iosb_at_agree RSEGS AD M1 M2); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact IOS1].
      apply (PNHK.ag_frame L LY sp LB8 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia|]. intros i _. apply N0. }
    assert (HST2 : PNH.hstat M2 true true be).
    { apply (PNHK.hstat_keep L LY LB8 (sp - 784) PMSP.OPDEL_SCR [] M1 M2 EKd); [|exact HST1]. intros a I. destruct (N0 a I). }
    (* [comment removed for export] *)
    pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R2 M2 model2 CORE2) as (_ & Rsp2 & _ & _ & WR2 & STK2).
    pose proof CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BASE2 & _ & (Mh2 & Ml2 & Mm2)).
    pose proof BASE2 as (IMG2 & _). change (L5.img_clear M2 65536 754672) in IMG2.
    LeanFeed.pfeed PK (PNSHP.bhnK_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct PK as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & A1k & A10k & C296k)); PMK.pvz_clrT.
    set (PK := fun a => sp - 296 <= a < sp - 296 + 8).
    assert (PFK : forall a, PK a -> PNH.fb sp <= a < PNH.fb sp + 784) by (intros a X; unfold PK in X; unfold PNH.fb, FRAME; lia).
    apply (PMK.spiece RSEGS L HI KL HIok LB8 cr M2 model2 fx2 fx3 R2 0x34868 R3 0x81cb4 M3 PK K HH2 Mh2 Ml2 ltac:(lia) MS3 MG3 FRZ3).
    { intros a Pa. apply PFK in Pa. unfold PNH.fb, FRAME in Pa. left. lia. }
    { intros a. apply PMK.rng_dec. }
    intros HH3.
    apply (KONT fx3 R3 M3 model2). unfold H7b.
    split. { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R2 M2 model2 R3 M3 PK CORE2 MG3 FRZ3); [intros a X; unfold PK in X; unfold PNH.fb, FRAME; lia| rewrite (KS3 2%nat) by PMK.inl; exact Rsp2|].
             intros k0 Hk0. apply KS3. revert k0 Hk0. apply PNH.CSK_in. vm_compute. reflexivity. }
    split. { eapply (PNHK.vstr_keep_p L sp LB8 M2 M3 PK (65536 - 784) FRZ3 PFK STK2 SCx BR8); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VS2].
             - intros i Hi X. unfold PK in X. unfold PNH.fb, FRAME in Hi. lia.
             - unfold LB8. apply incl_appl. apply incl_refl. }
    split. { eapply (PNHK.u64_keep_p M2 M3 PK FRZ3); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact LC2]. intros i Hi X. unfold PK in X. unfold PNH.fb, FRAME in Hi. lia. }
    split. { exists 740832, (PM.sm_st sm). apply (PMF.iosb_at_agree RSEGS AD M2 M3); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact IOS2].
             apply (PNHK.agp M2 M3 PK FRZ3); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia|]. intros i Hi X. unfold PK in X. unfold PNH.fb, FRAME in Hi. lia. }
    split. { apply (PNHK.hstat_piece L LY sp LB8 M2 M3 PK FRZ3 PFK true _ _ STK2 LBhi8 HST2). }
    split; [exact EMONO|]. split; [exact HH3|]. split; [exact CK|]. split; [exact A1k| exact A10k].
Qed.

Lemma stage10 :
  PMS.opdel_spec L HI -> PMS.locale_dtor_spec L -> PMS.ios_dtor_spec L HI ->
  forall (fx : FPState) R M model cr s s2 sm be K,
    PNH.H9 L HI R0 M0 model0 sp ra n LB0 cr0 g R M model cr s s2 sm be -> K [] ->
    (forall (fx1 : FPState) R1 M1 model1,
        PNH.H10 L HI R0 M0 model0 sp ra n LB0 cr0 g R1 M1 model1 cr s be ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x34894 M1 model1) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x34818 M model) K.
Proof using All.
  intros OPD LDT IDT fx R M model cr s s2 sm be K H7 K0 KONT.
  apply (strbuf_gone OPD fx R M model cr s s2 sm be K H7 K0).
  clear fx R M model H7. intros fx R M model (CORE & VS & LC & (vp & st & IOS) & HST & EMONO & HH & CK & A1 & A10).
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
  pose proof STK as (A16f & SLO & SHI & STOP & _).
  pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & MOK).
  pose proof MOK as (Mh & Ml & Mm).
  set (LBc := PM.vs_own s ++ LB0) in *.
  (* [comment removed for export] *)
  assert (STK0 : L5C.stk (hl_sptop L) M (sp - 784) (PMSP.pm_scr 0)).
  { apply (PMK.stk_call L M (sp - 784) (65536 - 784) (sp - 784) (PMSP.pm_scr 0) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16f]. }
  unfold PMS.locale_dtor_spec, PMSP.locale_dtor_spec in LDT.
  apply (LDT fx R M model K (sp - 784 + 496) (sp - 784) 215168 Mh Ml K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp|].
    split; [rewrite (Hcs 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STK0. }
  { rewrite L5K.rl10. rewrite A10. f_equal. lia. }
  { lia. }
  { lia. }
  { exact LC. }
  intros fx1 R1 RP1.
  assert (CORE1 : PNH.hcore L R0 M0 model0 sp ra LB0 R1 M model).
  { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M (fun _ => False) CORE); [intros a X; exact X| intros a Ha _; reflexivity| intros a []| |].
    - rewrite (PMK.cs_of_preserved R R1 2 RP1 ltac:(PMK.inl)). exact Rsp.
    - intros k Hk. apply (PMK.cs_of_preserved R R1 k RP1). unfold CSK in Hk. cbn in Hk. repeat (destruct Hk as [<-|Hk]; [PMK.inl|]). destruct Hk. }
  (* [comment removed for export] *)
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M model CORE1) as (_ & Rsp1 & _ & _ & _ & _).
  LeanFeed.pfeed PL (PNSHP.bhnL_conc fx1 R1 M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct PL as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG2 & FR2 & FRZ2 & MS2 & KS2 & A1l & A10l & A11l)); PMK.pvz_clrT.
  assert (EM : M2 = M) by (apply functional_extensionality; exact FR2). subst M2.
  apply (PMK.spiece_ro RSEGS model fx1 fx2 R1 0x34880 R2 0x5d4d0 M K Mh Ml MS2).
  assert (CORE2 : PNH.hcore L R0 M0 model0 sp ra LB0 R2 M model).
  { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R1 M model R2 M (fun _ => False) CORE1 MG2); [intros a Ha _; reflexivity| intros a []| rewrite (KS2 2%nat) by PMK.inl; exact Rsp1|].
    intros k Hk. apply KS2. revert k Hk. apply PNH.CSK_in. vm_compute. reflexivity. }
  (* [comment removed for export] *)
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R2 M model CORE2) as (_ & Rsp2 & _ & _ & _ & _).
  pose proof CORE2 as (_ & Hcs2 & _).
  assert (SC1 : 0 <= PMSP.pm_scr 1) by (unfold PMSP.pm_scr; lia).
  assert (STKc : L5C.stk (hl_sptop L) M (sp - 784) (PMSP.pm_scr 1)).
  { apply (PMK.stk_call L M (sp - 784) (65536 - 784) (sp - 784) (PMSP.pm_scr 1) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16f]. }
  unfold PNH.fb, FRAME in IOS.
  unfold PMS.ios_dtor_spec, PMSP.ios_dtor_spec in IDT.
  apply (IDT fx2 R2 M model K LBc cr (sp - 784 + 592) vp (sp - 784 + 488) st (sp - 784) 215188 HH MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1l|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp2|].
    split; [rewrite (Hcs2 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs2 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKc. }
  { rewrite L5K.rl10. rewrite A10l. f_equal. lia. }
  { lia. }
  { lia. }
  { replace (sp - 784 + 592) with (sp - 784 + 74 * 8) by lia. rewrite Z.mod_add by lia. apply Z.mod_divide in A16f; [|lia]. destruct A16f as (q & ->). replace (q * 16) with ((q * 2) * 8) by lia. apply Z.mod_mul. lia. }
  { exact IOS. }
  { exact BASE. }
  intros fx3 R3 M3 RP3 HP3 HH3.
  set (W3 := [(sp - 784 + 592, 152)] : list L5.range) in *.
  assert (WC3 : forall a, PMK.inW W3 a -> sp - 784 + 592 <= a < sp - 784 + 744).
  { intros a (r & Hin & Hr). destruct Hin as [<-|[]]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (EK3 : PMK.ek L LBc (sp - 784) (PMSP.pm_scr 1) W3 M M3) by (apply (PMK.ek_of_hpres L); exact HP3).
  assert (BRc : PNHK.brange L LBc) by (apply (PNHK.brange_of_heap L HI LY HIok LBc LBc cr M3 _ HH3); apply incl_refl).
  assert (WSTD : forall a, PMK.inW W3 a -> PNH.fb sp <= a \/ 65536 <= a < 962560) by (intros a I; apply WC3 in I; left; unfold PNH.fb, FRAME; lia).
  apply (KONT fx3 R3 M3 model). unfold PNH.H10.
  split. { apply (PNHK.hcore_call L LY R0 M0 model0 sp ra LB0 R2 M model R3 M3 model LBc (PMSP.pm_scr 1) W3 CORE2 RP3 HP3);
             [unfold LBc; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |apply L5C.model_but_vm_refl].
           intros a I. left. apply WC3 in I. unfold PNH.fb, FRAME. lia. }
  split. { eapply (PNHK.vstr_keep L LY sp LBc (PMSP.pm_scr 1) W3 M M3 EK3 STKc SC1 BRc WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VS].
           - intros i Hi I. apply WC3 in I. unfold PNH.fb, FRAME in Hi. lia.
           - unfold LBc. apply incl_appl. apply incl_refl. }
  split. { apply (PNHK.hstat_keep L LY LBc (sp - 784) (PMSP.pm_scr 1) W3 M M3 EK3); [|exact HST]. intros a I. apply WC3 in I. left. lia. }
  split; [exact EMONO|]. split; [exact HH3| exact CK].
Qed.

End Stage.
End PNH10.
