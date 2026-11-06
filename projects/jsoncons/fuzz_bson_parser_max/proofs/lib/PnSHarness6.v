(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
     PmLayout PnLayoutS PmModel PmModelFacts PmStatics PmSpecs PnSpecsS PmStep PmKeep PnKitS
     PgSrc PgV8 PnLayout PnModel PnModelFacts PnStatics PnKeep PnRun PnRunS PnTopS PnSHarnessStmts PnSHarnessKit PnSHarnessP.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNH6.
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

Lemma stage6 :
  PMS.opdel_spec L HI ->
  forall (fx : FPState) R M model cr s s2 p sm ax K,
    PNH.H5 L HI R0 M0 model0 sp ra n LB0 cr0 g R M model cr s s2 p sm ax -> K [] ->
    (forall (fx1 : FPState) R1 M1 model1,
        PNH.H6 L HI R0 M0 model0 sp ra n LB0 cr0 g R1 M1 model1 cr s s2 (PNM.b_src p) (PNM.b_bb p) (PNM.b_nb p) (PNM.b_tb p) sm ax ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x344b4 M1 model1) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x34490 M model) K.
Proof using All.
  intros OPD fx R M model cr s s2 p sm ax K (CORE & VS & SZ & IA & PA & HST & EMONO & HH & CK) K0 KONT.
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
  pose proof STK as (A16f & SLO & SHI & STOP & _).
  pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & (Mh & Ml & Mm)).
  set (LBX := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
  set (LBc := PNM.bparser_own p ++ LBX) in *.
  set (LB6 := PM.src_own (PNM.b_src p) ++ PGV8.v8_own (PNM.b_bb p) ++ PM.vs_own (PNM.b_nb p) ++ PM.vs_own (PNM.b_tb p) ++ LBX).
  assert (BRc : PNHK.brange L LBc) by (apply (PNHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
  assert (LBhic : forall x, In x LBc -> fst x + snd x <= hl_ceil L) by (intros (B & m) Hx; destruct (BRc B m Hx) as (_ & _ & Q); exact Q).
  assert (SCx : 0 <= 65536 - 784) by lia.
  unfold PNH.fb, FRAME in PA.
  destruct PA as (H0 & D & _ & H8 & H9 & H10 & H12 & NI & SRC & H312 & _ & BB & NB & TB & VEC & _).
  unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  destruct VEC as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL).
  set (b := PNM.b_sb p) in *. set (k := PNM.b_sk p) in *. unfold PNM.BSZ in V16.
  assert (Bv : In (b, 40 * 2 ^ k) LBc) by (unfold LBc, PNM.bparser_own, PNM.brest_own, PNM.bvec_own, PM.src_own, PNM.BSZ; cbn; auto).
  assert (Bq : In (PM.sr_qc (PNM.b_src p), PM.CHUNK) LBc) by (unfold LBc, PNM.bparser_own, PM.src_own; cbn; auto).
  destruct (BRc _ _ Bv) as (Vb0 & Vb1 & Vb4). pose proof (PM.pow2_pos k ltac:(lia)) as P2k.
  replace (sp - 784 + 40 + 392) with (sp - 352) in V0 by lia. replace (sp - 784 + 40 + 392 + 16) with (sp - 336) in V16 by lia.
  pose proof (m16_2 b Hal) as Hal2.
  LeanFeed.pfeed P (PNSHP.bhnG_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => b | 34%nat => b + 40 * 2 ^ k | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ0 & MS & KS & A1 & A10 & A11 & C0 & C1)); PMK.pvz_clrT.
  set (P := fun a => (sp - 744 <= a < sp - 744 + 8) \/ (sp - 344 <= a < sp - 344 + 8)).
  assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
  assert (PF : forall a, P a -> PNH.fb sp <= a < PNH.fb sp + 784) by (intros a [X|X]; unfold PNH.fb, FRAME; lia).
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x34490 R1 0x55138 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
  { intros a Pa. apply PF in Pa. unfold PNH.fb, FRAME in Pa. left. lia. }
  { intros a. apply PMK.or_dec; apply PMK.rng_dec. }
  intros HH1.
  assert (CORE1 : PNH.hcore L R0 M0 model0 sp ra LB0 R1 M1 model).
  { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 P CORE MG FRZ); [intros a [X|X]; unfold PNH.fb, FRAME; lia| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
    intros k0 Hk0. apply KS. revert k0 Hk0. apply PNH.CSK_in. vm_compute. reflexivity. }
  assert (VS1 : PM.vstr_at RSEGS PNH.T3 M1 (sp - 784 + 744) s).
  { eapply (PNHK.vstr_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [lia|lia| | |exact VS].
    - intros i Hi [X|X]; lia.
    - unfold LBc, LBX. apply incl_appr. apply incl_appr. apply incl_appl. apply incl_refl. }
  assert (IA1 : PM.iss_at RSEGS AD PNH.T3 M1 (sp - 784 + 472) s2 sm).
  { eapply (PNHK.iss_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [lia|lia| | |exact IA].
    - intros i Hi [X|X]; lia.
    - unfold LBc, LBX. apply incl_appr. apply incl_appl. apply incl_refl. }
  assert (INCR : incl (PNM.brest_own p) LBc) by (unfold LBc, PNM.bparser_own; apply incl_appl; apply incl_appr; apply incl_refl).
  assert (TB1 : PM.vstr_at RSEGS PNH.T3 M1 (sp - 784 + 40 + 368) (PNM.b_tb p)).
  { eapply (PNHK.vstr_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [lia|lia| | |exact TB].
    - intros i Hi [X|X]; lia.
    - intros x Hx. apply INCR. unfold PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hx. }
  assert (NB1 : PM.vstr_at RSEGS PNH.T3 M1 (sp - 784 + 40 + 344) (PNM.b_nb p)).
  { eapply (PNHK.vstr_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [lia|lia| | |exact NB].
    - intros i Hi [X|X]; lia.
    - intros x Hx. apply INCR. unfold PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hx. }
  assert (BB1 : PGV8.v8_at RSEGS PNH.T3 PNH.T4 M1 (sp - 784 + 40 + 320) (PNM.b_bb p)).
  { eapply (PNHK.v8_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [lia|lia| | |exact BB].
    - intros i Hi [X|X]; lia.
    - intros x Hx. apply INCR. unfold PNM.brest_own. apply in_or_app. right. apply in_or_app. left. exact Hx. }
  assert (SRC1 : PM.src_fields_at RSEGS PNH.T3 M1 (sp - 784 + 40 + 16) (sp - 784 + 472) (sp - 784 + 472 + 16) (PNM.b_src p)).
  { eapply (PNHK.src_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [lia|lia| |exact Bq|exact SRC]. intros i Hi [X|X]; lia. }
  assert (NI1 : PM.nullis_at RSEGS AD PNH.T3 M1 (sp - 784 + 40 + 16 + 8)).
  { eapply (PNHK.nullis_keep_p M M1 P FRZ); [lia|lia| |exact NI]. intros i Hi [X|X]; lia. }
  assert (HST1 : PNH.hstat M1 true true ax) by (apply (PNHK.hstat_piece L LY sp LBc M M1 P FRZ PF true _ _ STK LBhic HST)).
  (* [comment removed for export] *)
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M1 model CORE1) as (_ & Rsp1 & _ & _ & _ & STK1).
  pose proof CORE1 as (_ & Hcs1 & _).
  assert (STKd : L5C.stk (hl_sptop L) M1 (sp - 784) PMSP.OPDEL_SCR).
  { apply (PMK.stk_call L M1 (sp - 784) (65536 - 784) (sp - 784) PMSP.OPDEL_SCR STK1); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia| exact A16f]. }
  unfold PMS.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OPD.
  apply (OPD fx1 R1 M1 model K LBc cr b (40 * 2 ^ k) (sp - 784) 214196 HH1).
  { repeat split; assumption. }
  { exact K0. }
  { exact Bv. }
  { rewrite L5K.rl10. exact A10. }
  { rewrite L5K.rl1. exact A1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. exact Rsp1. }
  { rewrite L5K.rl4. rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto). exact Htp. }
  { exact STKd. }
  intros fx2 R2 M2 model2 RP HP MB HH2.
  assert (ELB : lb_remove b LBc = LB6).
  { pose proof (proj1 (proj2 (hio_wf L SCFG HI HIok LBc cr M _ HH))) as ND.
    unfold LBc, LB6, PNM.bparser_own, PNM.brest_own, PNM.bvec_own, PM.src_own, PNM.BSZ in *. cbn [app map fst] in *. fold b k in ND |- *.
    cbn [lb_remove fst]. inversion ND as [|x0 l0 NI0 ND0].
    destruct (Z.eqb (PM.sr_qc (PNM.b_src p)) b) eqn:EQ; [apply Z.eqb_eq in EQ; exfalso; apply NI0; rewrite EQ; constructor|].
    rewrite Z.eqb_refl. rewrite <- !app_assoc. reflexivity. }
  rewrite ELB in HP, HH2.
  assert (EKd : PMK.ek L LB6 (sp - 784) PMSP.OPDEL_SCR [] M1 M2) by (apply (PMK.ek_of_hpres L); exact HP).
  assert (SCd : 0 <= PMSP.OPDEL_SCR) by (unfold PMSP.OPDEL_SCR; lia).
  assert (BR6 : PNHK.brange L LB6) by (apply (PNHK.brange_of_heap L HI LY HIok LB6 LB6 cr M2 _ HH2); apply incl_refl).
  assert (WSTD : forall a, PMK.inW [] a -> PNH.fb sp <= a \/ 65536 <= a < 958464) by (intros a (r & [] & _)).
  assert (N0 : forall a, ~ PMK.inW [] a) by (intros a (r & [] & _)).
  apply (KONT fx2 R2 M2 model2). unfold PNH.H6, PNH.fb, FRAME.
  split. { apply (PNHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M1 model R2 M2 model2 LB6 PMSP.OPDEL_SCR [] CORE1 RP HP);
             [unfold LB6, LBX; do 6 apply incl_appr; apply incl_refl| unfold PMSP.OPDEL_SCR, SCR, FRAME; lia| |exact MB].
           intros a I. destruct (N0 a I). }
  split. { eapply (PNHK.vstr_keep L LY sp LB6 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR6 WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VS1].
           - intros i _. apply N0.
           - unfold LB6, LBX. do 5 apply incl_appr. apply incl_appl. apply incl_refl. }
  split; [exact SZ|].
  split. { eapply (PNHK.iss_keep L LY sp LB6 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR6 WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact IA1].
           - intros i _. apply N0.
           - unfold LB6, LBX. do 4 apply incl_appr. apply incl_appl. apply incl_refl. }
  split. { unfold PNH.prest_at, PNH.fb, FRAME.
    split. { replace (sp - 784 + 56) with (sp - 784 + 40 + 16) by lia. replace (sp - 784 + 488) with (sp - 784 + 472 + 16) by lia.
             eapply (PNHK.src_keep L LY sp LB6 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR6 WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact SRC1].
             - intros i _. apply N0.
             - unfold LB6, PM.src_own. cbn. auto. }
    split. { replace (sp - 784 + 64) with (sp - 784 + 40 + 16 + 8) by lia.
             eapply (PNHK.nullis_keep L LY sp LB6 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact NI1]. intros i _. apply N0. }
    split. { replace (sp - 784 + 360) with (sp - 784 + 40 + 320) by lia.
             eapply (PNHK.v8_keep L LY sp LB6 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR6 WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact BB1].
             - intros i _. apply N0.
             - unfold LB6. apply incl_appr. apply incl_appl. apply incl_refl. }
    split. { replace (sp - 784 + 384) with (sp - 784 + 40 + 344) by lia.
             eapply (PNHK.vstr_keep L LY sp LB6 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR6 WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact NB1].
             - intros i _. apply N0.
             - unfold LB6. apply incl_appr. apply incl_appr. apply incl_appl. apply incl_refl. }
    replace (sp - 784 + 408) with (sp - 784 + 40 + 368) by lia.
    eapply (PNHK.vstr_keep L LY sp LB6 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR6 WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact TB1].
    - intros i _. apply N0.
    - unfold LB6. apply incl_appr. apply incl_appr. apply incl_appr. apply incl_appl. apply incl_refl. }
  split. { apply (PNHK.hstat_keep L LY LB6 (sp - 784) PMSP.OPDEL_SCR [] M1 M2 EKd); [|exact HST1]. intros a I. destruct (N0 a I). }
  split; [exact EMONO|]. split; [exact HH2| exact CK].
Qed.

End Stage.
End PNH6.
