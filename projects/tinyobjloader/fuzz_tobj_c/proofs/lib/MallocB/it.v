(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From Stdlib Require NArith PArith FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillJ.

(* [comment removed for export] *)
Module CSecBump.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "bool"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cache_inited"; "aa_cls"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_geom"; "aa_internal_inited"; "aa_live"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "aa_sec"; "aa_frames"; "budget_bound"; "budget_ok_alloc"; "ageom"; "class_state"; "depot_state"; "mkAA"; "qbatch"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kPtrArrayCommit"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "budget_boundD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Open Scope Z_scope.

Definition bumpP (A : AA) : AA := ltac2:(tb__ "0|0|
S1eS11VA;A1SdVA;A1ScVA;A1S17VA;A1S22S14VA;A1S21A2S13VA;A1S16VA;A1S15VA;A1SeVA;A1S10VA;A1SfVA;A1S12VA;A1SbVA;A1SaVA;A1S9VA;A1Af").
Lemma bumpP_same : ltac2:(tb__ "0|3|
S8S1S0S1bS11S7R1A1M0A1S11R1A1A3S1S0S4S1cA1SdG0A1SdR1A1A3S1S0S5ScG0A1ScR1A1A3S1S0S4S20A1S17G0A1S17R1A1A3S1S0S3S14G0A1S22S14R1A1S21A2A3S1S0S4S6S3S3A2A1M1S13G0A1S13R1A1A3S1S0S4S1fA1M2S16G0A1S16R1A1A3S1S0G2S15G0A1S15R1A1A3S1S0S1dSeG0A1SeR1A1A3S1S0S4S3A1S10G0A1S10R1A1A3S1S0S4G1A1SfG0A1SfR1A1A3S1S0S5S12G0A1S12R1A1A3S1S0G1S18G0A1S18R1A1A3S1S0S3SbG0A1SbR1A1A3S1S0S3SaG0A1SaR1A1A3S0S3S9G0A1S9R1A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2FA;").
Proof. intros A. repeat split; reflexivity. Qed.
Lemma bumpP_bumpV : ltac2:(tb__ "0|0|
S8S3S0S8S7S23R2R1A2A1S23S7R2A1R1A2A3Fn;FA;").
Proof. intros A n. reflexivity. Qed.
Lemma budget_boundD_bumpP : ltac2:(tb__ "0|0|
S8S0S3S24S7R1A1A1S22S24R1A1S21A2A3FA;").
Proof. intros A. unfold budget_boundD. cbn [aa_V aa_Km aa_Kf aa_ptr_committed aa_depot bumpP]. lia. Qed.
Lemma budget_bound_bumpP : ltac2:(tb__ "0|0|
S8S0S3S19S7R1A1A1S19R1A1A3FA;").
Proof. intros A. reflexivity. Qed.
Lemma budget_ok_alloc_bumpP : ltac2:(tb__ "0|0|
S8S3S2S1aS7R2A1R1A2S1aR2R1A2A2Fn;FA;").
Proof. intros A n. unfold budget_ok_alloc. cbn [aa_V aa_Km aa_Kf bumpP]. tauto. Qed.
End CSecBump.

(* [comment removed for export] *)
Module SpineMallocS5.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Fixpoint zseq1 (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: zseq1 (lo + 1) n' end.
Lemma in_zseq1 : forall lo n z, lo <= z < lo + Z.of_nat n -> In z (zseq1 lo n).
Proof.
  intros lo n. revert lo. induction n as [|n IH]; intros lo z Hz; [lia|]. cbn [zseq1].
  destruct (Z.eq_dec z lo) as [->|Hne]; [left; reflexivity | right]. rewrite Nat2Z.inj_succ in Hz. apply IH. lia.
Qed.
Definition tab1_ok (i : positive) (e : sv) (g : Z -> Z) (lo : Z) (n : nat) : bool :=
  forallb (fun z => Z.eqb (bv_unsigned (eval (rho_one i (Z_to_bv 64 z)) e)) (g z)) (zseq1 lo n).
Lemma tab1_ok_sound : forall i e g lo n rho z,
  tab1_ok i e g lo n = true -> only_var i e = true ->
  rw rho i = Z_to_bv 64 z -> lo <= z < lo + Z.of_nat n ->
  eval rho e = Z_to_bv 64 (g z).
Proof.
  intros i e g lo n rho z Ht Ho Hi Hz.
  pose proof (proj1 (forallb_forall _ _) Ht z (in_zseq1 lo n z Hz)) as T. cbn beta in T. apply Z.eqb_eq in T.
  rewrite (eval_only_var i e rho Ho), Hi. rewrite <- T. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Definition depot_only (A A' : AA) : Prop :=
  aa_geom A' = aa_geom A /\ aa_cls A' = aa_cls A /\ aa_cache_inited A' = aa_cache_inited A /\ aa_sec A' = aa_sec A
  /\ aa_ptr_committed A' = aa_ptr_committed A /\ aa_live A' = aa_live A /\ aa_q_thread A' = aa_q_thread A
  /\ aa_q_global A' = aa_q_global A /\ aa_internal_inited A' = aa_internal_inited A
  /\ aa_fs_busy A' = aa_fs_busy A /\ aa_fs_hint A' = aa_fs_hint A
  /\ aa_V A' = aa_V A /\ aa_Km A' = aa_Km A /\ aa_Kf A' = aa_Kf A.
Lemma depot_only_refl : forall A, depot_only A A.
Proof. intros A. unfold depot_only. repeat split; reflexivity. Qed.

Definition depot_onlyK (A A' : AA) : Prop :=
  aa_geom A' = aa_geom A /\ aa_cls A' = aa_cls A /\ aa_cache_inited A' = aa_cache_inited A /\ aa_sec A' = aa_sec A
  /\ aa_ptr_committed A' = aa_ptr_committed A /\ aa_live A' = aa_live A /\ aa_q_thread A' = aa_q_thread A
  /\ aa_q_global A' = aa_q_global A /\ aa_internal_inited A' = aa_internal_inited A
  /\ aa_fs_busy A' = aa_fs_busy A /\ aa_fs_hint A' = aa_fs_hint A
  /\ aa_V A' = aa_V A /\ aa_Km A' = aa_Km A + 1 /\ aa_Kf A' = aa_Kf A.

Definition clsp_e : sv := SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SVar V_CLS) (SLit 32)) (SAlu ALU_SLL (SVar V_CH) (SLit 4))) (SLit 32).
Definition clsp_e31 : sv := SAlu ALU_AND clsp_e (SLit 31).

Lemma clsp_eval : forall rho c x, rw rho V_CLS = Z_to_bv 64 c -> rw rho V_CH = Z_to_bv 64 x -> 0 <= c <= 30 -> 0 <= x < 2 ^ 28 ->
  eval rho clsp_e = Z_to_bv 64 c /\ eval rho clsp_e31 = Z_to_bv 64 c.
Proof.
  intros rho c x Hc Hx Bc Bx.
  assert (E : eval rho clsp_e = Z_to_bv 64 c).
  { unfold clsp_e. cbn [eval]. rewrite Hc, Hx. apply bv_eq.
    rewrite srl_val, add_val, sll_val, sll_val, !u64_lit by lia. change (32 mod 64) with 32. change (4 mod 64) with 4.
    rewrite !Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
    rewrite (Z.mod_small (c * 2 ^ 32)) by lia. rewrite (Z.mod_small (x * 2 ^ 4)) by lia. rewrite (Z.mod_small (c * 2 ^ 32 + x * 2 ^ 4)) by lia.
    replace (c * 2 ^ 32 + x * 2 ^ 4) with (x * 2 ^ 4 + c * 2 ^ 32) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  split; [exact E|]. unfold clsp_e31. cbn [eval]. fold clsp_e. rewrite E. apply bv_eq. rewrite and_val, !u64_lit by lia.
  change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Section S5.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := J_alloc_preT AInv W st A Kc (SVar 12).

Lemma JG_rigid : forall A Kc rho rhoE tp tr md,
  JG W st A Kc rho rhoE tp tr md ->
  rw rhoE 12%positive = rw rho 12%positive
  /\ rw rhoE 148%positive = Z_to_bv 64 (Size (cls_of (bv_unsigned (rw rho 12%positive))))
  /\ rw rhoE 149%positive = Z_to_bv 64 (cnt_of A (bv_unsigned (rw rho 12%positive)))
  /\ rw rhoE 150%positive = Z_to_bv 64 (rz (bv_unsigned (rw rho 12%positive)))
  /\ rw rhoE 158%positive = Z_to_bv 64 (cls_of (bv_unsigned (rw rho 12%positive)))
  /\ rw rhoE 159%positive = Z_to_bv 64 (chk_of A (bv_unsigned (rw rho 12%positive))).
Proof.
  intros A Kc rho rhoE tp tr md [Hag HJ]. destruct Hag as (Hagw & Hagl & Hagm).
  split; [rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 148%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 149%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 150%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 158%positive) by (unfold GW; lia); reflexivity|].
  rewrite <- (Hagw 159%positive) by (unfold GW; lia); reflexivity.
Qed.

Lemma JG_stable : forall A Kc rho, stopJ_stable W st -> Kc_ok Kc -> stableA segs GW (JG W st A Kc rho).
Proof.
  intros A Kc rho HUS HKc.
  apply stableA_withG; [intros r1 r2 Hg Hag; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
Qed.

Lemma JG_model : forall A Kc rho rhoE tp tr md,
  JG W st A Kc rho rhoE tp tr md ->
  let nv := bv_unsigned (rw rho 12%positive) in
  AInvA segs A rhoE tp md /\ 1 <= nv < 2 ^ 39.
Proof.
  intros A Kc rho rhoE tp tr md [Hag HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  destruct Hag as (Hagw & _ & _). cbn zeta. rewrite <- (Hagw 12%positive) in HN by (unfold GW; lia). exact (conj HA HN).
Qed.

Lemma fact_of_state : forall A Kc rho rhoE tp w (E : axst) p,
  SPA segs (JG W st A Kc rho) E rhoE tp w -> In p (ss_facts (ax_S E)) -> holds rhoE p.
Proof.
  intros A Kc rho rhoE tp w E p [HsmA _] Hp.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  exact (proj1 (Forall_forall _ _) (smatch_facts_hold _ _ _ _ Hsm) p Hp).
Qed.

Lemma cnt_pos_of_fact : forall A Kc rho rhoE tp w (E : axst),
  SPA segs (JG W st A Kc rho) E rhoE tp w -> In (SPUle (SLit 1) (SVar V_CNT)) (ss_facts (ax_S E)) ->
  1 <= cnt_of A (bv_unsigned (rw rho 12%positive)).
Proof.
  intros A Kc rho rhoE tp w E H Hin. destruct w as [tr [ms md]].
  pose proof (JG_rigid A Kc rho rhoE tp tr md (proj2 H)) as (_ & _ & E149 & _).
  pose proof (fact_of_state A Kc rho rhoE tp _ E _ H Hin) as F. cbn [holds eval] in F. unfold V_CNT in F. rewrite E149 in F.
  rewrite (u64_lit 1) in F by lia.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as C0. unfold cnt_of in F |- *.
  set (len := Z.of_nat _) in F, C0 |- *.
  destruct (Z_lt_dec len (2 ^ 64)); [rewrite u64_lit in F by lia; exact F | lia].
Qed.

Definition J_alloc_preB (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) (n : sv) : jpredA :=
  fun rho tp tr md =>
    AInv A rho tp md /\ Kc tr md /\ tp_ok A rho /\ unwind_stopJ W st rho
    /\ True
    /\ 1 <= bv_unsigned (eval rho n) < 2 ^ 39
    /\ top_high A rho.
Definition JGb (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) (rho : valuation) : jpredA :=
  withGA (fun r => agree_below GW (rhoM_of A rho) r) (J_alloc_preB W st A Kc (SVar 12)).

Lemma JB_agree : forall A Kc rho rho' tp tr md,
  stopJ_stable W st -> agree_below NF rho rho' -> J_alloc_preB W st A Kc (SVar 12) rho tp tr md -> J_alloc_preB W st A Kc (SVar 12) rho' tp tr md.
Proof.
  intros A Kc rho rho' tp tr md HUS Hag (HA & HK & Htp & HU & HB & HN & Htop). pose proof Hag as (Hw & Hl & Hm).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  assert (E12 : eval rho' (SVar 12) = eval rho (SVar 12)) by (cbn; symmetry; apply Hw; unfold NF; lia).
  split; [unfold AInv, AInvA in *; rewrite Erm; exact HA|]. split; [exact HK|].
  split; [unfold tp_ok in *; rewrite <- (Hw 24%positive) by (unfold NF; lia); exact Htp|].
  split; [exact (HUS rho rho' Hag HU)|].
  rewrite E12. split; [exact I |]. split; [exact HN|].
  unfold top_high in *. rewrite <- (Hw 10%positive) by (unfold NF; lia). rewrite <- (Hw V_DEPTH) by (unfold NF, V_DEPTH; lia). exact Htop.
Qed.
Lemma JB_stableA : forall A Kc, stopJ_stable W st -> Kc_ok Kc -> stableA segs GW (J_alloc_preB W st A Kc (SVar 12)).
Proof.
  intros A Kc HUS HKc rho rho' tp tr md md' Hag Hme HJ.
  pose proof (JB_agree A Kc rho rho' tp tr md HUS ltac:(eapply agree_below_le; [|exact Hag]; cbv; discriminate) HJ) as (HA & HK & Htp & HU & HB & HN & Htop).
  split; [apply (AInvA_mat segs A rho' tp md md'); [exact HA | exact Hme]|].
  split; [destruct Hme as ((mat' & ->) & _); rewrite with_vm_backing_with_vm; apply HKc; exact HK|].
  split; [exact Htp|]. split; [exact HU|]. split; [exact I|]. split; [exact HN | exact Htop].
Qed.
Lemma JG_JGb : forall A Kc rho rhoE tp tr md, JG W st A Kc rho rhoE tp tr md -> JGb W st A Kc rho rhoE tp tr md.
Proof.
  intros A Kc rho rhoE tp tr md [Hag (HA & HK & Htp & HU & HB & HN & Htop)]. split; [exact Hag|].
  exact (conj HA (conj HK (conj Htp (conj HU (conj I (conj HN Htop)))))).
Qed.
Lemma JGb_rigid : forall A Kc rho rhoE tp tr md,
  JGb W st A Kc rho rhoE tp tr md ->
  rw rhoE 12%positive = rw rho 12%positive
  /\ rw rhoE 148%positive = Z_to_bv 64 (Size (cls_of (bv_unsigned (rw rho 12%positive))))
  /\ rw rhoE 149%positive = Z_to_bv 64 (cnt_of A (bv_unsigned (rw rho 12%positive)))
  /\ rw rhoE 150%positive = Z_to_bv 64 (rz (bv_unsigned (rw rho 12%positive)))
  /\ rw rhoE 158%positive = Z_to_bv 64 (cls_of (bv_unsigned (rw rho 12%positive)))
  /\ rw rhoE 159%positive = Z_to_bv 64 (chk_of A (bv_unsigned (rw rho 12%positive))).
Proof.
  intros A Kc rho rhoE tp tr md [Hag HJ]. destruct Hag as (Hagw & Hagl & Hagm).
  split; [rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 148%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 149%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 150%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 158%positive) by (unfold GW; lia); reflexivity|].
  rewrite <- (Hagw 159%positive) by (unfold GW; lia); reflexivity.
Qed.
Lemma JGb_stable : forall A Kc rho, stopJ_stable W st -> Kc_ok Kc -> stableA segs GW (JGb W st A Kc rho).
Proof.
  intros A Kc rho HUS HKc.
  apply stableA_withG; [intros r1 r2 Hg Hag; eapply agree_below_trans; eauto | apply JB_stableA; [exact HUS | exact HKc]].
Qed.
Lemma JGb_model : forall A Kc rho rhoE tp tr md,
  JGb W st A Kc rho rhoE tp tr md ->
  let nv := bv_unsigned (rw rho 12%positive) in
  AInvA segs A rhoE tp md /\ 1 <= nv < 2 ^ 39.
Proof.
  intros A Kc rho rhoE tp tr md [Hag HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  destruct Hag as (Hagw & _ & _). cbn zeta. rewrite <- (Hagw 12%positive) in HN by (unfold GW; lia). exact (conj HA HN).
Qed.
Lemma fact_of_stateB : forall A Kc rho rhoE tp w (E : axst) p,
  SPA segs (JGb W st A Kc rho) E rhoE tp w -> In p (ss_facts (ax_S E)) -> holds rhoE p.
Proof.
  intros A Kc rho rhoE tp w E p [HsmA _] Hp.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  exact (proj1 (Forall_forall _ _) (smatch_facts_hold _ _ _ _ Hsm) p Hp).
Qed.
Lemma cnt_pos_of_factB : forall A Kc rho rhoE tp w (E : axst),
  SPA segs (JGb W st A Kc rho) E rhoE tp w -> In (SPUle (SLit 1) (SVar V_CNT)) (ss_facts (ax_S E)) ->
  1 <= cnt_of A (bv_unsigned (rw rho 12%positive)).
Proof.
  intros A Kc rho rhoE tp w E H Hin. destruct w as [tr [ms md]].
  pose proof (JGb_rigid A Kc rho rhoE tp tr md (proj2 H)) as (_ & _ & E149 & _).
  pose proof (fact_of_stateB A Kc rho rhoE tp _ E _ H Hin) as F. cbn [holds eval] in F. unfold V_CNT in F. rewrite E149 in F.
  rewrite (u64_lit 1) in F by lia.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as C0. unfold cnt_of in F |- *.
  set (len := Z.of_nat _) in F, C0 |- *.
  destruct (Z_lt_dec len (2 ^ 64)); [rewrite u64_lit in F by lia; exact F | lia].
Qed.

Section B3S.
Hypothesis Cert3p : check_cfgA segsA 4000%nat [0x40e58; 0x3c614] GW [C2p W st tmax] [E3p W st tmax] = true.
Hypothesis SKY : map skel (ss_objs (ax_S (E3p W st tmax))) = map skel ((((sw_s1 :: unwind_objs W ++ A_globals) ++ RT_m1) ++ [O_pcc; O_pcs; O_pck; O_st])).
Hypothesis YX : ax_X (E3p W st tmax) = [].
Hypothesis YF : incl (((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_s1) ++ F_gen) (ss_facts (ax_S (E3p W st tmax))).
Hypothesis YP : In (SPUle (SLit 1) (SVar V_CNT)) (ss_facts (ax_S (E3p W st tmax))).
Hypothesis WY1 : swf (ax_S (Y1 (E3p W st tmax))) = true.
Hypothesis WY2 : swf (ax_S (Y2 (E3p W st tmax))) = true.
Hypothesis WY3 : swf (ax_S (Y3 (E3p W st tmax))) = true.
Hypothesis WY4 : swf (ax_S (Y4 (E3p W st tmax))) = true.
Hypothesis WY5 : swf (ax_S (Y5 (E3p W st tmax))) = true.
Hypothesis WY6 : swf (ax_S (Y6 (E3p W st tmax))) = true.
Hypothesis WY7 : swf (ax_S (Y7 (E3p W st tmax))) = true.
Variable s3 : wsub.
Hypothesis ENT3 : entailsA (Y7 (E3p W st tmax)) (C3 W st tmax) s3 = true.
Hypothesis SID3 : wsub_id_below s3 GW = true.

Theorem spine_s3p : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  (st = UStopLeOrPc -> W = []) -> stopJ_stable W st -> Kc_ok Kc -> sep_geom (aa_geom A) -> ok_frameA segs ok (J W st A Kc) ->
  (forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (C3 W st tmax) rhoE tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (C2p W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HW HUS HKc HSEP Hokf HC rhoE.
  apply (cfg_soundA segs 4000%nat [0x40e58; 0x3c614] GW [C2p W st tmax] [E3p W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. exact (Hokf r t tr ms md msv' HJ HMI Hh Hp Hs).
  - apply JG_stable; [exact HUS | exact HKc].
  - exact Cert3p.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s3))].
    apply (b3_carve nW st tmax (E3p W st tmax) SKY YX YF WY1 WY2 WY3 WY4 WY5 WY6 WY7 s3 ENT3 SID3 A Kc rho tp w rhoX HW HUS HKc HSEP); [|exact Hw].
    exact (cnt_pos_of_fact A Kc rho rhoX tp w _ Hw YP).
  - left. reflexivity.
Qed.
End B3S.

Section B2S.
Hypothesis Cert3r : check_cfgA segsA 4000%nat [0x40e58; 0x3c614] GW [C2r W st tmax] [E3r W st tmax] = true.
Theorem spine_s3r : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (J W st A Kc) ->
  (forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (E3r W st tmax) rhoE tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (C2r W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HR rhoE.
  apply (cfg_soundA segs 4000%nat [0x40e58; 0x3c614] GW [C2r W st tmax] [E3r W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. exact (Hokf r t tr ms md msv' HJ HMI Hh Hp Hs).
  - apply JG_stable; [exact HUS | exact HKc].
  - exact Cert3r.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HR].
  - left. reflexivity.
Qed.
End B2S.

Section B4S.
Hypothesis Cert4 : check_cfgA segsA 4000%nat [0x7e9e4] GW [C3 W st tmax] [E4d W st tmax] = true.

Definition hd_link (keep : Z -> Prop) (rho rho' : valuation) : Prop :=
  (forall i, rw rho' i = rw rho i) /\ (forall l, rl rho' l = rl rho l)
  /\ (forall a, keep (bv_unsigned a) -> rm rho' a = rm rho a)
  /\ (forall a, SHADOW_BAND_LO <= bv_unsigned a < SHADOW_BAND_HI -> rm rho a <> None -> rm rho' a <> None).
Lemma hd_link_refl : forall keep rho, hd_link keep rho rho.
Proof. intros keep rho. repeat split; intros; auto. Qed.

Definition HD_stmt (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho : valuation) (Q : assn) : Prop :=
  forall rhoE tp,
    (forall A' rho' rhoX tp', depot_onlyK A A' -> hd_link keep rho rho' ->
       triple segs ok (SPA segs (JGb W st A' Kc rho') (C5 W st tmax) rhoX tp') Q) ->
    triple segs ok (SPA segs (JG W st A Kc rho) (E4d W st tmax) rhoE tp) Q.

Theorem spine_s4 : forall keep (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (J W st A Kc) ->
  HD_stmt keep ok A Kc rho Q ->
  (forall A' rho' rhoX tp', depot_onlyK A A' -> hd_link keep rho rho' ->
     triple segs ok (SPA segs (JGb W st A' Kc rho') (C5 W st tmax) rhoX tp') Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (C3 W st tmax) rhoE tp) Q.
Proof.
  intros keep ok A Kc rho tp Q HUS HKc Hokf HD HC rhoE.
  apply (cfg_soundA segs 4000%nat [0x7e9e4] GW [C3 W st tmax] [E4d W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. exact (Hokf r t tr ms md msv' HJ HMI Hh Hp Hs).
  - apply JG_stable; [exact HUS | exact HKc].
  - exact Cert4.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HD; exact HC].
  - left. reflexivity.
Qed.
End B4S.

Section B5S.
Hypothesis Cert5 : check_cfgA segsA 4000%nat [0x3c774; 0x3c80c] GW [C5 W st tmax] [E5n W st tmax; E5f W st tmax] = true.
Variable s6n : wsub.
Hypothesis ENT6n : entailsA (E5n W st tmax) (C6 W st tmax) s6n = true.
Hypothesis SID6n : wsub_id_below s6n GW = true.
Hypothesis W5b : swf (ax_S (C5b W st tmax)) = true.
Hypothesis D5b : state_diff (ax_S (E5f W st tmax)) (ax_S (C5b W st tmax)) = Some ([(clsp_e31, SVar V_CLS); (clsp_e, SVar V_CLS)], []).
Hypothesis NX5b : ss_next (ax_S (C5b W st tmax)) = ss_next (ax_S (E5f W st tmax)).
Hypothesis F5f64 : In (SPUle (SVar 12) (SLit 64512)) (ss_facts (ax_S (E5f W st tmax))).

Theorem spine_s5 : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (liftKA Kc) ->
  1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) ->
  (forall rhoX, triple segs ok (SPA segs (JGb W st A Kc rho) (C6 W st tmax) rhoX tp) Q) ->
  (forall rhoX, triple segs ok (SPA segs (JGb W st A Kc rho) (C5b W st tmax) rhoX tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JGb W st A Kc rho) (C5 W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf Hcnt H6 H5b rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c774; 0x3c80c] GW [C5 W st tmax] [E5n W st tmax; E5f W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert5.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    +
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (H6 (rho_sub rhoX s6n))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5n W st tmax) (C6 W st tmax) s6n rhoX tp w ENT6n SID6n); [|exact Hw].
      apply JGb_stable; [exact HUS | exact HKc].
    +
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (H5b rhoX)].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB A Kc rho rhoX tp _ _ _ Hw F5f64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, E148, E149, E150, E158, E159, Hcnt |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      pose proof (pc_entry_facts segs A rhoX tp md nv HA ltac:(lia) Hcnt) as PF. cbn zeta in PF. destruct PF as (_ & _ & _ & _ & _ & Hch & _ & _).
      destruct (clsp_eval rhoX (cls_of nv) (chk_of A nv) E158 E159 ltac:(lia) Hch) as [EV1 EV2].
      unfold C5b, upd. lazy zeta. eapply SPA_restate; [exact W5b | exact D5b | exact NX5b | | constructor | exact Hw].
      unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold V_CLS; cbn [eval]; rewrite ?EV1, ?EV2, E158; reflexivity.
  - left. reflexivity.
Qed.
End B5S.

Section B6S.
Hypothesis Cert5b : check_cfgA segsA 4000%nat [0x3c7e0] GW [C5b W st tmax] [E5s1 W st tmax; E5s2 W st tmax] = true.

Definition E5s1' : axst := upd W st tmax (E5s1 W st tmax) 0x3c7e0 [(8%nat, SVar V_SIZE)] [] false [].
Definition E5s2' : axst := upd W st tmax (E5s2 W st tmax) 0x3c7e0 [(8%nat, SVar V_SIZE)] [] false [].
Hypothesis OV1 : only_var 158 (sreg1 W st tmax) = true.
Hypothesis OV2 : only_var 158 (sreg2 W st tmax) = true.
Hypothesis TAB1 : tab1_ok 158 (sreg1 W st tmax) Size 17 14%nat = true.
Hypothesis TAB2 : tab1_ok 158 (sreg2 W st tmax) Size 1 16%nat = true.
Hypothesis W1' : swf (ax_S E5s1') = true.
Hypothesis W2' : swf (ax_S E5s2') = true.
Hypothesis D1' : state_diff (ax_S (E5s1 W st tmax)) (ax_S E5s1') = Some ([(sreg1 W st tmax, SVar V_SIZE)], []).
Hypothesis D2' : state_diff (ax_S (E5s2 W st tmax)) (ax_S E5s2') = Some ([(sreg2 W st tmax, SVar V_SIZE)], []).
Hypothesis NX1' : ss_next (ax_S E5s1') = ss_next (ax_S (E5s1 W st tmax)).
Hypothesis NX2' : ss_next (ax_S E5s2') = ss_next (ax_S (E5s2 W st tmax)).
Hypothesis F1gt : In (SPBranch BC_LTU (SLit 16) (SVar V_CLS)) (ss_facts (ax_S (E5s1 W st tmax))).
Hypothesis F2le : In (SPNot (SPBranch BC_LTU (SLit 16) (SVar V_CLS))) (ss_facts (ax_S (E5s2 W st tmax))).
Hypothesis F1_64 : In (SPUle (SVar 12) (SLit 64512)) (ss_facts (ax_S (E5s1 W st tmax))).
Hypothesis F2_64 : In (SPUle (SVar 12) (SLit 64512)) (ss_facts (ax_S (E5s2 W st tmax))).
Variables s1 s2 : wsub.
Hypothesis ENT1 : entailsA E5s1' (C5c W st tmax) s1 = true.
Hypothesis ENT2 : entailsA E5s2' (C5c W st tmax) s2 = true.
Hypothesis SID1 : wsub_id_below s1 GW = true.
Hypothesis SID2 : wsub_id_below s2 GW = true.

Theorem spine_s5b : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (liftKA Kc) ->
  (forall rhoX, triple segs ok (SPA segs (JGb W st A Kc rho) (C5c W st tmax) rhoX tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JGb W st A Kc rho) (C5b W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c7e0] GW [C5b W st tmax] [E5s1 W st tmax; E5s2 W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert5b.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s1))].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB A Kc rho rhoX tp _ _ _ Hw F1_64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      pose proof (fact_of_stateB A Kc rho rhoX tp _ _ _ Hw F1gt) as Fgt. cbn [holds eval] in Fgt. unfold V_CLS in Fgt. rewrite E158 in Fgt.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, Fgt, E148, E149, E150, E158, E159 |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      rewrite bt_ltu_lit in Fgt by lia. apply Z.ltb_lt in Fgt.
      assert (H' : SPA segs (JGb W st A Kc rho) E5s1' rhoX tp (tr, mkCfg ms md)).
      { unfold E5s1', upd. lazy zeta. eapply SPA_restate; [exact W1' | exact D1' | exact NX1' | | constructor | exact Hw].
        unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold V_SIZE. cbn [eval]. rewrite E148.
        exact (tab1_ok_sound 158 _ Size 17 14%nat rhoX (cls_of nv) TAB1 OV1 E158 ltac:(cbn; lia)). }
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E5s1' (C5c W st tmax) s1 rhoX tp _ ENT1 SID1); [|exact H'].
      apply JGb_stable; [exact HUS | exact HKc].
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s2))].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB A Kc rho rhoX tp _ _ _ Hw F2_64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      pose proof (fact_of_stateB A Kc rho rhoX tp _ _ _ Hw F2le) as Fle. cbn [holds eval] in Fle. unfold V_CLS in Fle. rewrite E158 in Fle.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, Fle, E148, E149, E150, E158, E159 |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      rewrite bt_ltu_lit in Fle by lia.
      assert (Hle : cls_of nv <= 16) by (destruct (Z.ltb_spec 16 (cls_of nv)); [exfalso; apply Fle; reflexivity | lia]).
      assert (H' : SPA segs (JGb W st A Kc rho) E5s2' rhoX tp (tr, mkCfg ms md)).
      { unfold E5s2', upd. lazy zeta. eapply SPA_restate; [exact W2' | exact D2' | exact NX2' | | constructor | exact Hw].
        unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold V_SIZE. cbn [eval]. rewrite E148.
        exact (tab1_ok_sound 158 _ Size 1 16%nat rhoX (cls_of nv) TAB2 OV2 E158 ltac:(cbn; lia)). }
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E5s2' (C5c W st tmax) s2 rhoX tp _ ENT2 SID2); [|exact H'].
      apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End B6S.
End S5.
End SpineMallocS5.

(* [comment removed for export] *)
Module SpineMallocR1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "nat"; "app"; "list"; "nil"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "rw"; "valuation"; "holds"; "ss_facts"; "ss_objs"; "SLit"; "agree_below"; "obj_range"; "ranges_disjoint"; "smatch"; "sprop_below"; "ss_next"; "sstate"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "bv_signed"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "ag_spacebeg"; "ag_thread"; "aa_cache_inited"; "aa_geom"; "ag_ctx"; "ageom"; "class_state"; "cs_allocated_user"; "cs_mapped_free_array"; "cs_mapped_user"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1"; "r0_of"; "ghostl"; "NR0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "ulink"; "unwind_objs"; "F_sp_high"; "KcA"; "UStopLeOrPc"; "V_DEPTH"; "chain_pre"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "ustop"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "w_cfg"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "F_gen"; "O_pcc0"; "O_st"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "F_r0"; "F_r1"; "GR"; "O_pcm"; "O_ri"; "cR0"; "cR0a"; "vAU"; "vMC"; "vMFA"; "vMU"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kSpaceSize"; "max_count"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "geom_ok"; "sep_geom3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "FAb"; "JR"; "entryR"; "gh_chx"; "gh_new"; "gh_nf"; "ghosts"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cnt_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1.ZONE"; "armint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ZONE.
Let segs : list Segment := segsA.
Variable W : list ulink.

Definition armint (G : ageom) (lo hi : Z) : Prop := ltac2:(tb__ "0|2|
S1eS1dS23S24S2aVG;A1M0Z120A2Vlo;A2S23Vhi;S24G0Zc60A2A2A2S1eS1dS23S29VG;A1M1Vlo;A2S23Vhi;S24S24G1S65A2Z1000A2A2A2S1dS23S64Vlo;A2S23Vhi;S63A2A2A2A2").

Lemma base_zone : ltac2:(tb__ "0|3|
S2eSdS18S2S5S4cA1S4bA2S5S9A1S1aS1aS68R7A1S69R8A1S15Vsegs;R8R7R6A4S9S38S9R1R7A3S38S9R2S10RaA1A3F_;Fo;S1cS5S2S2SaSaA2SaA2M0A1S25S9G0S34R7A4S25S9G0S34S4S9S1S9S3dS4S9S40VW;A1S3eA3A3S3cA3A4A3SeRbS41A2S26SbSeRcA1S45VW;A1A3S23S33ReA1S24S21Q40M1ScRdPaA2A2S22G1ScRdS44A2A2A2A2S1cS20G1A1M2ScReP97A2S1fG1S2aRfA1A2A3S1cG2ScRfP98A2S1fG1S2dR10A1A2A3S76R11RcRbA3S26S9S9S14S13R12R1A2S0S1aS1aReRdA4A2Lo';ReA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fobjs;Fw;FS;FrhoE;FG;").
Proof.
  intros G rhoE S w objs lo hi HG0 HS3 Hsm Hsub HSK Hhigh HCH Htop E151 E152 HI.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  clear G15 G16 G17 G18 G20 G21 G1 G2 G3 G4 G10 G11.
  pose proof (geom_bands _ HG0) as (_ & TB & CB & _ & TI & CI & _). unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in TB, CB, TI, CI.
  destruct HS3 as (PS1 & PS2 & _). rewrite kSpaceSize_val in PS1, PS2.
  pose proof (topG_range G) as TG.
  unfold armint, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in HI. rewrite kSpaceSize_val in HI.
  destruct objs as [|osw orest]; [cbn [map] in HSK; exfalso; clear -HSK; discriminate HSK|].
  cbn [map] in HSK.
  assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) HSK).
  assert (SKrest : map skel orest = map skel ((unwind_objs W ++ A_globals) ++ RT_m1)) by exact (f_equal (@tl _) HSK).
  destruct (sw_range_gen _ rhoE _ _ osw Hsm (Hsub osw (or_introl eq_refl)) SKsw Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG G <= fst (obj_range rhoE osw)) by (rewrite (sw_lo_gen rhoE osw SKsw); exact Htop).
  assert (LNK : Forall (fun o => topG G + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG G)); [exact HCH | clear -SW0 SW2 SW3; lia | clear -TG; lia]. }
  constructor.
  - clear -SW0 G14 HI G6 TG. unfold ranges_disjoint. cbn [fst snd]. lia.
  - apply (Forall_ranges_skel rhoE (fun r => ranges_disjoint r (lo, hi)) orest _ SKrest).
    apply Forall_app. split.
    + apply Forall_app. split.
      * eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
        unfold ranges_disjoint. rewrite !obj_range_mk by (clear -B TG; lia). cbn [fst snd]. clear -B G14 HI G6 TG. lia.
      * unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia;
          clear -HI G5 G13 TI; lia.
    + unfold RT_m1, RT_m0, O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_self_tsd, O_tsd0, O_ctx8, O_ctx98, O_T0, O_T40, O_T3168, O_cfa, O_pga, O_pgb, O_mcs,
             O_insta, O_insta2, O_instb, O_rss, O_cfb, O_cfc, O_rms, O_ppf, O_hooks, O_lsan, O_cft, O_afl, O_csd, O_die.
      unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval];
        rewrite ?E151, ?E152, ?u64_lit by (first [ clear -G5 G6 TG; lia | clear -G8 G9 TG; lia | lia ]);
        (first [ clear -HI G5 G13 TI; lia | clear -HI G5 G6 TB TI PS1 G13 TG; lia | clear -HI G8 G9 CB CI PS2 G13 G24 TG G5 G6 G19; lia ]).
Qed.
End ZONE.

Definition NR0 : list carve_spec := ltac2:(tb__ "0|b|
S1S2S2S2SaS1aA2M0S1aA2M1S5S2S2S1aS3A2M2SaA2M3A1M4A2M5S0G1G4S0G0S1aS0SaS1aS55Z4M6A4Z8A4S1G3S0G2SaS0S1aS3G6U4A4S5eA4S6G3A1M7A3A4S1G5S0G1G4S0G0S1aS0SaS1aS62Z0M8A4Z80A4S1G3S0G2SaS0S1aS3G8U8M9A4S11G8A1MaA4S1G3S0G2SaS0S1aS3Z10G9A4S61A4S1G3S0G2SaS0S1aS3Z18G9A4S5fA4S1G3S0G2SaS0S1aS3Z20G9A4S5dA4S1G3S0G2SaS0S1aS3Z28G9A4GaA4S1G3S0G2SaS0S1aS3Z30G9A4S60A4S1G3S0G2SaS0S1aS3Z38G9A4GaA4S1G3S0G2SaS0S1aS3Z44U1A4GaA4G7A3A3A3A3A3A3A3A3A4S6G5A1A3A3").
Lemma NR0_objs : ltac2:(tb__ "0|0|
S1cS5S9A1S25S50S9S4fS37A4S1S9S59S1S9S5aS6S9A1A3A3A3"). Proof. reflexivity. Qed.

Definition ghostl (A : AA) (rb : valuation) : list (positive * word) := ltac2:(tb__ "0|3|
S21Q40M0ScVrb;PcA2A2S1aS73R1A1S1aS75VA;R2A2S2fS29S2cVA;A1A1S1aS1S2S1bS20G0A1M1A2M2S0S1bG1PdcS1fG0S66R3A1A2A4S1G2S0S1bG1PddS1fG0S6fVA;Vrb;A2A2A4S1G2S0S1bG1PdeS1fG0S31R2A1A2A4S1G2S0S1bG1PdfS1fG0S30R2A1A2A4S1G2S0S1bG1Pe0S1fG0S32R2A1A2A4S1G2S0S1bG1Pe1S1fG0S67R1R3A2A2A4S1G2S0S1bG1Pe2S1fG0S6aVA;Vrb;A2A2A4S1G2S0S1bG1Pe3S1fG0S72R3A1A2A4S1G2S0S1bG1Pe4S1fG0S6eVA;Vrb;A2A2A4S1G2S0S1bG1Pe5S1fG0S6dVA;Vrb;A2A2A4S6G2A1A3A3A3A3A3A3A3A3A3A3TSB;Tcs;Tc;Tnv;").
Definition r0_of (A : AA) (rb : valuation) : valuation := ltac2:(tb__ "0|0|
S51Vrb;S36VA;Vrb;A2A2").

Lemma ghostl_ge : ltac2:(tb__ "0|1|
S28SdS1bS20Q40A1M0S38S2S1bG0A2S0S1bG0R2R1A4S36R4R3A2A3S78PdcR3A2F_;Fv;Fj;Frb;FA;").
Proof. intros A rb j v H. unfold ghostl in H. cbn [In] in H. repeat (destruct H as [H|H]; [injection H as <- _; lia|]). destruct H. Qed.
Lemma r0_agree : ltac2:(tb__ "0|0|
S28SdS12PdcR1S35R2R1A2A3Frb;FA;").
Proof. intros A rb. apply agree_below_rho_sets. apply ghostl_ge. Qed.
Lemma r0_ghosts : ltac2:(tb__ "0|0|
S28SdS70R2R1S35R2R1A2A3Frb;FA;").
Proof.
  intros A rb. unfold ghosts, r0_of.
  assert (ND : List.NoDup (map fst (ghostl A rb))).
  { unfold ghostl. cbn [map fst]. repeat (constructor; [cbn [In]; intros H; repeat (destruct H as [H|H]; [discriminate H|]); exact H|]). constructor. }
  repeat split; apply (rw_rho_sets_in rb (ghostl A rb) _ _ ND); unfold ghostl; cbn [In]; tauto.
Qed.

Section ENTRY.
Let segs : list Segment := segsA.
Variable nW : nat. Variable st : ustop.
Let W : list ulink := Wcan nW.

Variable E3 : axst.
Hypothesis SK3 : ltac2:(tb__ "0|1|
S1cS5S2S2SaSaA2SaA2M0A1S25S9G0S34S10S27VE3;A1A1A4S25S9G0S34S4S9S4S9S1S9S3dS4S9S40VW;A1S3eA3A3S3cA3S1S9S53S1S9S54S6S9A1A3A3A3A4A3").
Hypothesis XX3 : ax_X E3 = [].
Hypothesis XF3 : ltac2:(tb__ "0|0|
S3aSbS4SbS4SbS48VW;Vst;A2S47S46A1A3S52A3SfS27VE3;A1A1A3").
Hypothesis NX3 : ltac2:(tb__ "0|0|
S1cS7S79S17S27VE3;A1A1PdcA2S8A3").
Hypothesis WR0a : ltac2:(tb__ "0|0|
S1cS7S19S27S5cVE3;A1A1A1S8A3").
Hypothesis FB0 : ltac2:(tb__ "0|0|
S1cS7S39SbS16S58A1S4SbSfS27VE3;A1A1S4SbS56S57A3A3A3S8A3").

Lemma refill_entry : ltac2:(tb__ "0|2|
S28S42SdSdS5S20Q40M0A1A1S4eS1cS49Vst;S43A3S1cS5S3fA1VW;S6S3fA1A3F_;S1cS7S2bR7A1S8A3S1cS1aS74R8S21G0ScR6PcA2A2A2Z0A3S3bVsegs;S77VW;Vst;R9R8R7A5VE3;R6R5R4A6S1dS6cRaR7R6S4aS4dR5A1A1M1VW;Vst;R8A7S3bVsegs;S6bRaR9R7R6G1S71A6S5bVE3;A1S35RaR7A2R6R5A6A2F_;F_;F_;F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w HW Hini Hcnt H.
  pose proof H as [HsmA [Hag HJ]]. pose proof Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN, HB.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite <- E12 in Hcnt. set (nv := bv_unsigned (rw rhoE 12%positive)) in *.
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). cbn. rewrite <- E12. reflexivity. }
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p ((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_gen) -> holds rhoE p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa p (XF3 p Hp)). }
  assert (Hnv : nv <= 64512).
  { pose proof (HFX (SPUle (SVar 12) (SLit 64512)) ltac:(apply in_or_app; right; unfold F_gen; cbn; tauto)) as F. cbn [holds eval] in F.
    rewrite u64_lit in F by lia. exact F. }
  pose proof (cls_facts nv ltac:(lia)) as (C1 & C2 & C3 & C4).
  destruct (kchunks_facts _ C1) as (K1 & K2 & K3).
  split.
  { unfold entryR. split; [exact Hag|]. split; [exact HA|]. split; [exact Htp|]. split; [exact HU|]. split; [exact HB|]. split; [lia|]. split; [exact Htop|]. split; [exact Hcnt|].
    exact (MI_ivs_wf segs _ _ (proj1 (proj2 HsmA))). }
  idtac "entry:1".

  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT). pose proof HG as HG0.
  destruct HRest as (Hsep & Hlive & Hprim & _ & _ & _ & _ & HTH & _).
  destruct Hprim as (_ & _ & _ & P4). specialize (P4 (cls_of nv) C1).
  pose proof (proj1 HI3) as HS3.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (_ & _ & _ & _ & G5 & G6 & _ & _ & _ & _ & _ & G12 & G13 & G14 & _).
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _ & _). unfold IMG_LO, IMG_HI in TI.
  pose proof (topG_range (aa_geom A)) as TG.
  set (G := aa_geom A) in *. set (c := cls_of nv) in *. set (T := ag_thread G) in *. set (SB := ag_spacebeg G) in *.
  assert (MT : forall z, T <= z < T + 0x1000 -> maskv (fs_footb G) (view segs (rm rhoE)) z = view segs (rm rhoE) z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  assert (MS : forall z, SB <= z < SB + kSpaceSize + 4096 -> maskv (fs_footb G) (view segs (rm rhoE)) z = view segs (rm rhoE) z).
  { intros z Hz. apply maskv_out. apply fs_footb_space; [exact HG | exact Hz]. }
  unfold class_repr in P4. fold G SB in P4.
  destruct P4 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & _ & _ & _ & PE & _ & _ & CI & _).
  destruct (CI Hini) as (_ & D2 & _).
  set (cs := nthZ (aa_cls A) c cs_empty) in *.
  idtac "entry:2".
  set (r0 := r0_of A rhoE).
  pose proof (r0_agree A rhoE) as AG0. pose proof (r0_ghosts A rhoE) as GH0. fold r0 in AG0, GH0.
  assert (Erm0 : rm r0 = rm rhoE) by (unfold r0, r0_of; apply rm_rho_sets).

  assert (Ha : SPA segs (JR A Kc rhoE tp (cfg_model (w_cfg w)) ph0) E3 r0 tp w).
  { split.
    - eapply smatchA_agree; [|exact HsmA]. eapply agree_below_le; [|exact AG0]. apply Pos.leb_le. exact NX3.
    - unfold JR. split; [|split; [exact GH0|split; [exact HK|split; [|split]]]].
      + destruct AG0 as (Aw & Al & _). split; [exact Aw | exact Al].
      + unfold mlink, ph0, committed, revealedp, subU, subF. cbn [ph_u ph_f Nat.leb].
        repeat (split; [reflexivity|]). exists []. cbn [app length Z.of_nat]. split; [reflexivity|]. split; [intros p []|]. split; [lia | lia].
      + rewrite Erm0. unfold rlink, zoneR, ph0, revealedp, releasedp. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb].
        split; [intros; reflexivity|]. split.
        { intros z [[X _]|[[X _]|[[X _]|[[X _]|[[_ X]|[X|[[X _]|[X _]]]]]]]]; try discriminate X; exfalso; lia. }
        split; [intros j Hj; exfalso; lia|]. split; [intros i Hi; exfalso; lia|]. split; intros X; discriminate X.
      + intros a _. rewrite Erm0. reflexivity. }
  idtac "entry:3".

  destruct AG0 as (A0w & A0l & A0m).
  assert (R151 : rw r0 151%positive = Z_to_bv 64 T) by (rewrite <- (A0w 151%positive) by (clear; lia); exact E151).
  assert (R152 : rw r0 152%positive = Z_to_bv 64 (ag_ctx G)) by (rewrite <- (A0w 152%positive) by (clear; lia); exact E152).
  assert (R158 : rw r0 158%positive = Z_to_bv 64 c) by (rewrite <- (A0w 158%positive) by (clear; lia); exact E158).
  assert (R10 : rw r0 10%positive = rw rhoE 10%positive) by (rewrite <- (A0w 10%positive) by (clear; lia); reflexivity).
  assert (R15 : rw r0 V_DEPTH = rw rhoE V_DEPTH) by (rewrite <- (A0w V_DEPTH) by (unfold V_DEPTH; clear; lia); reflexivity).
  destruct GH0 as (Q220 & Q221 & Q222 & Q223 & Q224 & Q225 & Q226 & Q227 & Q228 & Q229).
  unfold gh_nf, FAb, cst_of in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227.
  fold nv in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227. fold c in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227.
  fold cs in Q221, Q222, Q223, Q224. fold G in Q225, Q226. fold SB in Q225, Q226.
  assert (EB : bv_unsigned (eval r0 pc_base) = T + 208 + 80 * c).
  { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite R151, R158. rewrite add_val, add_val, mul_val, !u64_lit by (clear -C1 G5 G6 TG; lia).
    rewrite (Z.mod_small (c * 80)) by (clear -C1; lia). rewrite (Z.mod_small (T + 208)) by (clear -G5 G6 TG; lia). rewrite Z.mod_small by (clear -C1 G5 G6 TG; lia). clear; lia. }
  pose proof kSpaceSize_val as KSV.
  assert (RIr : SB + kSpaceSize <= region_info SB c /\ region_info SB c + 128 <= SB + kSpaceSize + 4096).
  { unfold region_info, kRegionInfoStride. clear -C1. lia. }
  assert (ERI : bv_unsigned (eval r0 vRI) = region_info SB c).
  { unfold vRI. cbn [eval]. rewrite Q225. apply u64_lit. rewrite kSpaceSize_val in *. clear -RIr G13 G14 TG. unfold HIGH_SHADOW_END in *. lia. }
  pose proof (proj1 Ha) as HsmA0. pose proof (proj1 HsmA0) as Hsm0. unfold virt in Hsm0. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm0.
  pose proof (smatch_facts_hold _ _ _ _ Hsm0) as HFa0.
  assert (HFX0 : forall p, In p ((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_gen) -> holds r0 p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa0 p (XF3 p Hp)). }

  destruct (map_eq_app _ _ _ _ ltac:(rewrite <- map_app; exact SK3)) as (ob & ox & EO & SKb & SKx).
  destruct ox as [|oc [|os [|? ?]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence).
  assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (RNc : obj_range r0 oc = (T + 208 + 80 * c, T + 208 + 80 * c + 4)).
  { rewrite (obj_range_skel r0 oc O_pcc0 SKc). unfold O_pcc0. rewrite obj_range_mk by (clear; lia). rewrite EB. f_equal; clear; lia. }
  assert (RNs : obj_range r0 os = (T + 2768, T + 3168)).
  { rewrite (obj_range_skel r0 os O_st SKs). unfold O_st, vT. rewrite obj_range_mk by (clear; lia). cbn [eval]. rewrite R151, u64_lit by (clear -G5 G6 TG; lia). reflexivity. }
  assert (BZ : forall lo hi, armint G lo hi -> Forall (fun o' => ranges_disjoint (obj_range r0 o') (lo, hi)) ob).
  { intros lo hi HI. apply (base_zone W G r0 (ax_S E3) _ ob lo hi HG0 HS3 Hsm0); [intros o Ho; rewrite EO; apply in_or_app; left; exact Ho | exact SKb | | | | exact R151 | exact R152 | exact HI].
    - apply HFX0. apply in_or_app; left. apply in_or_app; right. cbn; tauto.
    - apply Forall_forall. intros p Hp. apply HFX0. apply in_or_app; left. apply in_or_app; left.
      destruct st; [apply chain_pre_in; exact Hp|]. rewrite (HW eq_refl) in Hp. destruct Hp.
    - rewrite R10, R15. exact Htop. }
  idtac "entry:4".

  assert (PRT : forall z, T <= z < T + 4096 -> (exists b, view segs (rm rhoE) z = Some b) ->
            wok_of segs (rm r0) (Z_to_bv 64 z) = true /\ exists x, rd_of segs (rm r0) (Z_to_bv 64 z) = Some x).
  { intros z Hz [b Hb]. rewrite Erm0. rewrite view_in in Hb by (clear -Hz G5 G6 TG; lia).
    eapply wok_rd_off_image2; [| |exact Hb]; [clear -Hz G5 G6 TG; lia | clear -Hz TI; lia]. }
  assert (PRS : forall z, SB <= z < SB + kSpaceSize + 4096 -> (exists b, view segs (rm rhoE) z = Some b) ->
            wok_of segs (rm r0) (Z_to_bv 64 z) = true /\ exists x, rd_of segs (rm r0) (Z_to_bv 64 z) = Some x).
  { intros z Hz [b Hb]. rewrite kSpaceSize_val in Hz. rewrite Erm0. rewrite view_in in Hb by (clear -Hz G13 G14 TG; unfold HIGH_SHADOW_END in *; lia).
    eapply wok_rd_off_image; [|exact Hb]. clear -Hz G13 G14 TG. unfold HIGH_SHADOW_END in *. lia. }

  assert (CVT : forall a k v (e : sv), T <= a -> a + Z.of_nat k <= T + 4096 -> eval r0 e = Z_to_bv 64 v ->
            cell_ok (maskv (fs_footb G) (view segs (rm rhoE))) (mkACell a k v) ->
            forall j, (j < k)%nat -> rd_of segs (rm r0) (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j (enc_bytes k (eval r0 e)) (Z_to_bv 8 0))).
  { intros a k v e Ha1 Ha2 Ee Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    rewrite MT in Hc by (clear -Ha1 Ha2 Hj; lia). rewrite view_in in Hc by (clear -Ha1 Ha2 Hj G5 G6 TG; lia). rewrite Erm0, Ee. exact Hc. }
  assert (CVS : forall a k v (e : sv), SB <= a -> a + Z.of_nat k <= SB + kSpaceSize + 4096 -> eval r0 e = Z_to_bv 64 v ->
            cell_ok (maskv (fs_footb G) (view segs (rm rhoE))) (mkACell a k v) ->
            forall j, (j < k)%nat -> rd_of segs (rm r0) (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j (enc_bytes k (eval r0 e)) (Z_to_bv 8 0))).
  { intros a k v e Ha1 Ha2 Ee Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    rewrite MS in Hc by (clear -Ha1 Ha2 Hj; lia). rewrite kSpaceSize_val in Ha2.
    rewrite view_in in Hc by (clear -Ha1 Ha2 Hj G13 G14 TG; unfold HIGH_SHADOW_END in *; lia). rewrite Erm0, Ee. exact Hc. }
  idtac "entry:5".
  assert (Hb : SPA segs (JR A Kc rhoE tp (cfg_model (w_cfg w)) ph0) (cR0a E3) r0 tp w).
  { apply (SPA_carve_list segs _ r0 E3 tp w NR0 GR Ha WR0a).
    - apply Pos.leb_le in NX3. clear -NX3. unfold GR. lia.
    - unfold NR0. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + rewrite EB. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear -C1 G5 TG; lia|]. split; [clear -C1 G5 G6 TG; lia|].
        split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
        split.
        { intros off Hoff. apply PRT; [clear -Hoff C1; lia|]. destruct (PE (T + 208 + 80 * c + off) ltac:(unfold T, G, c; clear -Hoff; lia)) as [b Hb']. exists b. rewrite <- MT by (clear -Hoff C1; lia). exact Hb'. }
        split; [|unfold xwords_clear; rewrite XX3; intros rr y j []].
        apply Forall_cons; [|apply Forall_nil]. intros j Hj.
        exact (CVT (T + 208 + 80 * c + 4) 4%nat (max_count c) vMC ltac:(clear -C1; lia) ltac:(clear -C1; lia) Q220 D2 j Hj).
      + rewrite ERI. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|].
        split; [clear -RIr G13; unfold HIGH_SHADOW_END in *; rewrite kSpaceSize_val in *; lia|].
        split; [clear -RIr G13 G14 TG; unfold HIGH_SHADOW_END in *; rewrite kSpaceSize_val in *; lia|].
        split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
        split.
        { intros off Hoff. apply PRS; [clear -Hoff RIr KSV; lia|]. destruct (PRI (region_info SB c + off) ltac:(unfold kRegionInfoStride; clear -Hoff; lia)) as [b Hb']. exists b. rewrite <- MS by (clear -Hoff RIr KSV; lia). exact Hb'. }
        split; [|unfold xwords_clear; rewrite XX3; intros rr y j []].
        unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted in *.
        repeat apply Forall_cons; try apply Forall_nil; intros j Hj.
        * exact (CVS (region_info SB c + 0) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R1 j Hj).
        * exact (CVS (region_info SB c + 16) 8%nat _ vNF ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q221 R2 j Hj).
        * exact (CVS (region_info SB c + 24) 8%nat _ vMFA ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q222 R3 j Hj).
        * exact (CVS (region_info SB c + 32) 8%nat _ vAU ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q223 R4 j Hj).
        * exact (CVS (region_info SB c + 40) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R5 j Hj).
        * exact (CVS (region_info SB c + 48) 8%nat _ vMU ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q224 R6 j Hj).
        * exact (CVS (region_info SB c + 56) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R7 j Hj).
        * exact (CVS (region_info SB c + 68) 1%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R8 j Hj).
    - idtac "entry:6". cbn [map carve_obj NR0].
      assert (RNm : obj_range r0 (carved pc_base 4 8 [(4, 4%nat, vMC)]) = (T + 208 + 80 * c + 4, T + 208 + 80 * c + 8)).
      { unfold carved. rewrite obj_range_mk by (clear; lia). rewrite EB. reflexivity. }
      assert (RNr : obj_range r0 (carved vRI 0 128 [(0, 8%nat, SLit 0); (16, 8%nat, vNF); (24, 8%nat, vMFA); (32, 8%nat, vAU); (40, 8%nat, SLit 0); (48, 8%nat, vMU); (56, 8%nat, SLit 0); (68, 1%nat, SLit 0)])
                    = (region_info SB c + 0, region_info SB c + 128)).
      { unfold carved. rewrite obj_range_mk by (clear; lia). rewrite ERI. reflexivity. }
      destruct HS3 as (PS1 & _). fold T SB in PS1.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; rewrite EO; apply Forall_app; split.
      + rewrite RNm. apply BZ. left. fold T. clear -C1. lia.
      + rewrite RNm. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; [rewrite RNc | rewrite RNs]; unfold ranges_disjoint; cbn [fst snd]; clear -C1; lia.
      + rewrite RNr. apply BZ. right; left. fold SB. clear -RIr KSV. lia.
      + rewrite RNr. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; [rewrite RNc | rewrite RNs]; unfold ranges_disjoint; cbn [fst snd]; clear -C1 RIr KSV PS1; lia.
    - cbn [map carve_obj NR0 pairwise_disjoint]. split; [|split; [constructor | exact I]].
      apply Forall_cons; [|apply Forall_nil]. unfold carved. rewrite !obj_range_mk by (clear; lia). rewrite EB, ERI.
      destruct HS3 as (PS1 & _). fold T SB in PS1. unfold ranges_disjoint; cbn [fst snd]. clear -C1 RIr KSV PS1. lia. }
  idtac "entry:7".

  unfold cR0. apply (SPA_refacts segs _ r0 (cR0a E3) _ tp w Hb FB0).
  intros HF0. apply Forall_app. split; [exact HF0|].
  assert (E155 : rw r0 155%positive = Z_to_bv 64 SB) by (rewrite <- (A0w 155%positive) by (clear; lia); rewrite <- (Hagw 155%positive) by (unfold GW; clear; lia); reflexivity).
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize, kFreeArrayMapSize in N1, N2, N3, N5, N6.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0.
  assert (DSB : exists q, SB = q * 2 ^ 16) by (apply Z.mod_divide in G12; [destruct G12 as [q Hq]; exists q; exact Hq | clear; lia]).
  destruct DSB as [q Hq].
  unfold F_r0, F_r1, vMC, vK, vNF, vAU, vMU. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval].
  - rewrite Q220, !u64_lit by (clear -C4; lia). clear -K1 K2. lia.
  - rewrite Q220, !u64_lit by (clear -C4; lia). clear -C4. lia.
  - split; [clear; lia|]. rewrite Q225, u64_lit by (clear -RIr KSV G13 G14 TG; unfold HIGH_SHADOW_END in *; lia).
    unfold region_info, kRegionInfoStride. rewrite KSV, Hq. replace (q * 2 ^ 16 + 2 ^ 37 + c * 128) with ((q * 512 + 2 ^ 30 + c) * 2 ^ 7) by (clear; lia). apply Z_mod_mult.
  - split; [clear; lia|]. rewrite Q226.
    unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize.
    rewrite u64_lit by (clear -C1 G13 G14 TG KSV; unfold HIGH_SHADOW_END in *; lia).
    rewrite Hq. replace (q * 2 ^ 16 + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)) with ((q * 16 + c * 2 ^ 20 + (2 ^ 20 - 2 ^ 17)) * 2 ^ 12) by (clear; lia). apply Z_mod_mult.
  - rewrite Q227, !u64_lit by (clear -K1; lia). clear -K1. lia.
  - rewrite Q227, !u64_lit by (clear -K1; lia). clear -K1. lia.
  - rewrite Q221, !u64_lit by (clear -N6 NF0; lia). clear -N6. lia.
  - rewrite Q223, Q224, !u64_lit by (clear -N2 N3; lia). clear -N2. lia.
  - split; [clear; lia|]. rewrite Q224, u64_lit by (clear -N2 N3; lia). exact N1.
  - split; [clear; lia|]. rewrite E155, u64_lit by (clear -G13 G14 TG KSV; unfold HIGH_SHADOW_END in *; lia). exact G12.
Qed.
End ENTRY.
End SpineMallocR1.

(* [comment removed for export] *)
Module SpineCallocS3.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "entailsA"; "axst"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "true"; "prod"; "list"; "app"; "cons"; "pair"; "andb"; "nil"; "Some"; "option"; "fst"; "length"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "swf"; "valuation"; "SVar"; "ss_next"; "ss_facts"; "SLit"; "obj_range"; "rw"; "ss_objs"; "sprop_below"; "SPBranch"; "holds"; "ob_base"; "ob_hi"; "ob_lo"; "rm"; "sstate"; "SPNot"; "eval"; "mkSS"; "smatch"; "sprop_eqb"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "leb"; "mul"; "modulo"; "pow"; "eqb"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "X2"; "X2r"; "X1"; "X1b"; "X1c"; "X1r"; "cls_ok8"; "inclb"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "E2a"; "E2b"; "C2p0"; "C2r0"; "F_gen"; "F_cls"; "creg_a"; "creg_b"; "C1g"; "C2p"; "C2r"; "F_pop"; "V_CLS"; "V_ND"; "@Stdlib.Lists.List"; "incl"; "forallb"; "In"; "existsb"; "nth_error"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "ag_thread"; "aa_geom"; "ageom"; "aa_cache_inited"; "class_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "cls_of"; "stopJ_stable"; "needed8"; "chk_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "unwind_objs"; "A_globals"; "KcA"; "Kc_ok"; "V_DEPTH"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "F_sp_high"; "J_alloc_preT"; "chain_pre"; "ulink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "present"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2"; "E2a'"; "E2b'"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "Size"; "max_count"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3.B1B"; "X2"; "X2r"; "X1"; "X1b"; "X1c"; "X1r";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "tab_ok"; "@Corelib.Init.Nat"; "of_num_uint"; "sub"; "@Corelib.Init.Number"; "UIntDecimal"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac liaL := first [ solve [ repeat match goal with K : _ |- _ => clear K end; lia ] | lia ].
Local Ltac liaZ := lazymatch goal with |- gcells_inside _ _ _ _ => fail | |- cells_inside _ _ _ => fail | |- Forall _ _ => fail | |- cells_in_view _ _ _ _ => fail | |- xwords_clear _ _ _ _ => fail | |- forall _, _ => fail | |- (_ <= _)%positive => fail | |- _ => liaL end.

Definition cls_ok8 (n : Z) : bool := ltac2:(tb__ "0|5|
S8dS6fVn;A1M0A1S33SdSdSdSdSdSdSdS37Z1M1R1A2S37R1Z1eA2A2S37Z18G0A2A2S37G0S8eR1A1M2A2A2S37G2Z10000A2A2S3bS39G2Z10M3A2Z0A2A2S37S8fR1A1M4G3A2A2S37G1G4A2A2Tc;").
Lemma cls_ok8_all : ltac2:(tb__ "0|0|
S33S1S35Z1R1A2S35R1Zfc00A2A2S0S6S45R2A1S7A3F_;Fn;").
Proof. intros n Hn. apply (forall_rangeZ_ok cls_ok8 1 64512); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cls_facts : ltac2:(tb__ "0|6|
S33S1S35Z1M0R1A2S35R1Zfc00A2A2S1S1S35G0S6dR2A1M1A2S35G1Z1eA2A2S1S1S1S35Z18S6fR2A1M2A2S35G2S8eG1A1M3A2A2S35G3Z10000A2A2S1S0S33S39G3Z10M4A2Z0A3S1S35G0S8fG1A1M5A2S35G5G4A2A2A2A2A2F_;Fn;").
Proof.
  intros n Hn. pose proof (cls_ok8_all n Hn) as H. unfold cls_ok8, cls_of in *.
  repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with K : (_ <=? _) = true |- _ => apply Z.leb_le in K | K : (_ =? _) = true |- _ => apply Z.eqb_eq in K end. lia.
Qed.

Definition skel (o : sobj) : sv * sv * sv := ltac2:(tb__ "0|0|
ScS8S14S14A2S14ScS14S14S23Vo;A1S25Vo;A1A4S24Vo;A1A4").
Lemma obj_range_skel : ltac2:(tb__ "0|0|
S18S15S15S0S8S8S14S14A2S14A2S3eR2A1S3eR1A1A3S0S8S33S33A2S1dR4R3A2S1dR4R2A2A3F_;Fo';Fo;Frho;").
Proof. intros rho [b l h c d] [b' l' h' c' d'] E. cbn in E. injection E as -> -> ->. reflexivity. Qed.
Lemma Forall_ranges_skel : ltac2:(tb__ "0|2|
S18S8S33S33A2OF_;S9S15A1M0G0S0S9S8S8S14S14A2S14A2M1A1S47S15G1S3eR2A4S47S15G1S3eR1A4A3S48S15S15R5S1dR6R1A2A1Lo;R2A3S48S15S15R6S1dR7R1A2A1Lo;R4A3F_;F_;Fl';Fl;FP;Frho;").
Proof.
  intros rho P l. induction l as [|o l IH]; intros [|o' l'] E H; cbn in E; try discriminate; [constructor|].
  assert (Es : skel o = skel o') by congruence. assert (El : map skel l = map skel l') by congruence.
  apply Forall_cons_iff in H as [Ha Hb]. constructor; [rewrite (obj_range_skel rho o o' Es); exact Ha | exact (IH l' El Hb)].
Qed.

Lemma nth_error_last : ltac2:(tb__ "0|1|
S9S33A1Sa4U0S12S33R1A2A2S0S10S33A1S62S33R2Sa2S12S33R2A2U1A2M0A3SfS33S49S33G0R2Z0A4A2A3F_;Fl;").
Proof.
  intros l Hl. destruct (nth_error l (length l - 1)) as [x|] eqn:E.
  - f_equal. symmetry. apply nth_error_nth. exact E.
  - apply nth_error_None in E. lia.
Qed.

Definition inclb (l1 l2 : list sprop) : bool := ltac2:(tb__ "0|0|
S5fS16S16S61S16S2cR1A1Vl2;A3Lp;Vl1;A3").
Lemma inclb_incl : ltac2:(tb__ "0|1|
S9S16A1M0G0S0S6S46R2R1A2S7A3S5eS16R3R2A3F_;Fl2;Fl1;").
Proof.
  intros l1 l2 H p Hp. pose proof (proj1 (forallb_forall _ _) H p Hp) as E. apply existsb_sprop_eqb in E. exact E.
Qed.

Lemma sw_range_gen : ltac2:(tb__ "0|5|
S9S85A1S18S27S8S9S96A1Sa5A2S15S2bR5R4R3R2A4S60S15R2S1fR4A1A3S0S8S8S14S14A2M0S14A2S3eR3A1ScG0S14ScS14S14S19PaM1A1S19S76A1A4S1cZ0A1A4A3S22R7S7aA2S1S35Z7fff7f800000S11S33S33S1dR8R5A2M2A3M3A2S1S0S33S13S33S33G2A3M4S63Q40S1eR8G1A2A2A3S35G3G4A2A2A2F_;F_;F_;F_;Fo;Fw;FS;Frho;Fsegs;").
Proof.
  intros segs rho S w o Hsm Hin Hsk Hf.
  destruct o as [ob olo ohi ocs od]. cbn in Hsk. injection Hsk as -> -> ->.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
  pose proof (proj1 (Forall_forall _ _) Hall _ Hin) as Ho.
  pose proof (stack_win_range segs rho (mkSS 0 [] [] FcsrFrm0 None [stack_win] [] NW2 false) w) as SW.
  unfold obj_holds, obj_lo_of, obj_hi_of in Ho. cbn [ob_base ob_lo ob_hi] in Ho.
  destruct Ho as ((B1 & B2 & B3 & B4) & _).
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
  rewrite soff_lit in *. replace (snorm 0) with 0 in * by reflexivity.
  cbn [eval] in *. unfold holds, F_sp_high in Hf. cbn [eval] in Hf. rewrite add_val in Hf.
  rewrite u64_lit in Hf by lia.
  rewrite soff_snorm in *. unfold U in *. cbn [eval] in *.
  pose proof (urange (rw rho 10%positive)) as R10. pose proof (urange (rw rho V_DEPTH)) as R15.
  unfold snorm in *.
  rewrite (Z.mod_small (bv_unsigned (rw rho V_DEPTH)) (2 ^ 64)) in * by lia.
  destruct (Z.ltb_spec (bv_unsigned (rw rho V_DEPTH)) (2 ^ 63)).
  - assert (bv_unsigned (rw rho V_DEPTH) = 0) by lia. rewrite H0 in *. rewrite Z.add_0_r, Z.mod_small in Hf by lia. lia.
  - replace ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) mod 2 ^ 64)
      with (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) in Hf.
    2:{ symmetry. replace (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) with
          ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    lia.
Qed.

Lemma pc_entry_facts : ltac2:(tb__ "0|7|
S9S85A1S66S18S9S64Q40A1A1S95S33S90R6R5R4R3R2A5S1S35Z1M0R2A2S35R2Zfc00A2A2S35G0S6cR7R3A2A2S68R8A1S69S6dR5A1S33S71RaR6A2S6bS36S36S67R3A1Zd0A2S38Z50M1R2A2A2S33S82RdS26RbA1A2S81S1S0S6S6aRdA1S7A3S1S7eR1S7fR2U4M2S6cRdR9A2M3A3A2S1S7eR1S7fS36R2Z8A2U8S8eR4A1A3A2S1S7eR1S7fS36S36R2Z10M4A2S38Z4S3dG3G0A2A2A2G2S70RdR9A2M5A3A2S1S35G3G4A2S1S1S35Z0G5A2S3cG5S3aZ2Z1cA2A2A2S1S80R1R2S36R2G1A2A3S80R1S36S67R5A1M6Zad0A2S36G6Zc60A2A3A2A2A2A2A2A2A2Tm;Te;Tcs;Tc;TG;F_;F_;F_;Fnv;Fmd;Ftp;Frho;FA;Fsegs;").
Proof.
  intros segs A rho tp md nv HA Hnv Hcnt G c cs e m. unfold e, m, cs, c, G. clear G c cs e m.
  pose proof (cls_facts nv Hnv) as (C1 & C2 & C3 & C4).
  unfold chk_of, cnt_of, cst_of in *.
  set (G := aa_geom A) in *. set (c := cls_of nv) in *. set (m := view segs (rm rho)) in *.
  pose proof HA as (HG & HR & HF & HRest & HM).
  destruct HRest as (Hsep & Hlive & Hprim & _ & _ & _ & _ & HTH & _).
  destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  assert (MT : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> maskv (fs_footb G) (view segs (rm rho)) z = m z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & N7 & _ & _ & PE & ND & LV & CI & CN & _ & _ & _ & _).
  set (cs := nthZ (aa_cls A) c cs_empty) in *.
  assert (Hci : aa_cache_inited A = true).
  { destruct (aa_cache_inited A) eqn:E; [reflexivity|]. exfalso. destruct (CN eq_refl) as [Hc0 _].
    rewrite Hc0 in Hcnt. cbn in Hcnt. lia. }
  destruct (CI Hci) as (D1 & D2 & D3 & D4 & D5).
  assert (ER : forall k a v, ag_thread G + 0xd0 <= a -> a + Z.of_nat k <= ag_thread G + 0x1000 ->
             cell_ok (maskv (fs_footb G) (view segs (rm rho))) (mkACell a k v) -> cell_ok m (mkACell a k v)).
  { intros k a v Ha1 Ha2 Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w c_val] in Hc, Hj |- *. rewrite MT in Hc by lia. exact Hc. }
  split; [exact Hci|].
  split; [apply (ER 4%nat); [lia| cbn; lia | exact D1]|].
  split; [apply (ER 8%nat); [lia | cbn; lia | exact D3]|].
  split.
  { pose proof (nth_error_last (cs_cache cs) ltac:(lia)) as NE.
    specialize (D4 (length (cs_cache cs) - 1)%nat _ NE).
    replace (Z.of_nat (length (cs_cache cs) - 1)) with (Z.of_nat (length (cs_cache cs)) - 1) in D4 by lia.
    apply (ER 4%nat); [lia | cbn; lia | exact D4]. }
  split; [lia|].
  split.
  { assert (Hin : In (nth (length (cs_cache cs) - 1)%nat (cs_cache cs) 0) (cs_free_array cs ++ cs_cache cs)).
    { apply in_or_app. right. apply nth_In. lia. }
    destruct (N7 _ Hin) as (X1 & X2 & X3). unfold kCompactPtrScale in X3. rewrite Z.shiftl_mul_pow2 in X3 by lia.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in N2, N3. clear -X1 X3 N2 N3 C2. lia. }
  split.
  { intros z Hz. destruct (PE z Hz) as [b Hb]. exists b. rewrite <- (MT z) by lia. exact Hb. }
  unfold thread_inv in HTH. destruct HTH as [_ HTS]. intros z Hz. assert (Hz' : ag_thread (aa_geom A) + 2688 <= z < ag_thread (aa_geom A) + 3168) by (unfold G in Hz; clear -Hz; lia). destruct (HTS z Hz') as [b Hb]. exists b. rewrite <- (MT z) by lia. exact Hb.
Qed.

Lemma pc_entry_facts0 : ltac2:(tb__ "0|3|
S9S85A1S66S18S9S64Q40A1A1S95S33S90R6R5R4R3R2A5S1S35Z1R2A2S35R2Zfc00A2A2S0S33S6cR7R3A2Z0M0A3S68R8A1S69S6dR5A1S33S36S36S67R2A1Zd0A2S38Z50M1R1A2A2S33S82RcS26RaA1A2S81S1S7eR1S7fR2U4G0A3A2S1S80R1R2S36R2G1A2A3S80R1S36S67R4A1M2Zad0A2S36G2Zc60A2A3A2A2Tm;Te;Tc;TG;F_;F_;F_;Fnv;Fmd;Ftp;Frho;FA;Fsegs;").
Proof.
  intros segs A rho tp md nv HA Hnv Hcnt G c e m. unfold e, m, c, G. clear G c e m.
  pose proof (cls_facts nv Hnv) as (C1 & C2 & C3 & C4).
  unfold cnt_of, cst_of in *.
  set (G := aa_geom A) in *. set (c := cls_of nv) in *. set (m := view segs (rm rho)) in *.
  pose proof HA as (HG & HR & HF & HRest & HM).
  destruct HRest as (Hsep & Hlive & Hprim & _ & _ & _ & _ & HTH & _).
  destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  assert (MT : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> maskv (fs_footb G) (view segs (rm rho)) z = m z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & N7 & _ & _ & PE & ND & LV & CI & CN & _ & _ & _ & _).
  set (cs := nthZ (aa_cls A) c cs_empty) in *.
  split.
  { assert (D : cell_ok (maskv (fs_footb G) (view segs (rm rho))) (mkACell (ag_thread G + 208 + 80 * c) 4 0)).
    { destruct (aa_cache_inited A) eqn:E.
      - destruct (CI eq_refl) as (D1 & _). rewrite Hcnt in D1. exact D1.
      - destruct (CN eq_refl) as [_ FL]. intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
        etransitivity; [apply FL; subst G c; lia|].
        rewrite nth_enc_bytes by lia. unfold MallocInv.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l, Z.mod_0_l by lia. reflexivity. }
    intros j Hj. specialize (D j Hj). cbn [c_addr c_w RtCells.c_val] in D, Hj |- *. rewrite MT in D by lia. exact D. }
  split.
  { intros z Hz. destruct (PE z Hz) as [b Hb]. exists b. rewrite <- (MT z) by lia. exact Hb. }
  unfold thread_inv in HTH. destruct HTH as [_ HTS]. intros z Hz. assert (Hz' : ag_thread (aa_geom A) + 2688 <= z < ag_thread (aa_geom A) + 3168) by (unfold G in Hz; clear -Hz; lia). destruct (HTS z Hz') as [b Hb]. exists b. rewrite <- (MT z) by lia. exact Hb.
Qed.

Lemma sw_lo_gen : ltac2:(tb__ "0|3|
S18S15S0S8S8S14S14A2M0S14A2S3eR1A1ScG0S14ScS14S14S19PaM1A1S19S76A1A4S1cZ0A1A4A3S0S33S11S33S33S1dR3R2A2A3S36S63Q40M2S1eR3G1A2A2S65G2S1eR3S76A2A2A2A3F_;Fo;Frho;").
Proof. intros rho [ob olo ohi ocs od] Hsk. cbn in Hsk. injection Hsk as -> -> ->. reflexivity. Qed.

Lemma unwind_objs_above : ltac2:(tb__ "0|3|
S9S7dA1S18S33S48S16S22R2A1S7cR3A1A3S35R2S63Q40M0S1eR3PaA2A2A2S35Z0M1R3A2S48S15S15S1S1S35S36R5Z10A2S63G0S29R6S23R1A1A2A2M2A2S35G2S3aZ2Z2fA2A2A2S1S0S14S25R1A1S1cN10A1A3S0S14S24R1A1S1cG1A1A3A2A2Lo;S72R6A1A3F_;F_;F_;FT;Frho;FW;").
Proof.
  intros W rho T HC Hsp HT0. unfold unwind_objs. destruct W as [|l W']; [constructor|].
  unfold chain_pre in HC. cbn [app] in HC.
  pose proof (Forall_inv HC) as X0. pose proof (Forall_inv (Forall_inv_tail HC)) as X1c.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as X2. do 3 apply Forall_inv_tail in HC.
  cbn [holds eval] in X0, X1c, X2. rewrite u64_lit in X0 by lia. rewrite add_val, !u64_lit in X1c by lia. rewrite u64_lit in X2 by lia.
  pose proof (urange (rw rho 10%positive)). rewrite Z.mod_small in X1c by lia.
  eapply Forall_impl; [|apply (chain_facts_bases rho (SVar 28) (l :: W') HC); cbn [eval]; lia].
  intros o (B & L & Hh). cbn [eval] in B. repeat split; try assumption; lia.
Qed.

Section B1B.
Let segs : list Segment := segsA.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.

Variable X : axst.
Hypothesis HXskel : ltac2:(tb__ "0|1|
S0S9S8S8S14S14A2S14A2M0A1S47S15G0S3eS1fS2VX;A1A1A4S47S15G0S3eSaS15SbS15S8bSaS15S72VW;A1S73A3A3S8cA3A4A3").
Hypothesis HXX : ax_X X = [].
Hypothesis HXF : ltac2:(tb__ "0|0|
S5eS16SaS16SaS16SaS16S79VW;Vst;A2S78S77A1A3S8aA3S54A3S1bS2VX;A1A1A3").

Definition addobj (A : axst) (o : sobj) : axst := ltac2:(tb__ "0|0|
S2VA;A1S27S5VA;S2aS30R1A1S31R1A1S2eR1A1S2dR1A1S32R1A1SaS15S1fR1A1SbS15Vo;SeS15A1A3A3S1bR1A1S1aR1A1S2fR1A1A9A2TS;").

Definition X1 : axst := addobj X O_pcc.
Definition X1b : axst := addobj X1 O_pcs.
Definition X1c : axst := addobj X1b O_pck.
Definition X2 : axst := addobj X1c O_st.
Definition X1r : axst := addobj X O_pcc0.
Definition X2r : axst := addobj X1r O_st.
Hypothesis W1 : ltac2:(tb__ "0|0|
S0S6S17S2S9bA1A1S7A3").
Hypothesis W1b : ltac2:(tb__ "0|0|
S0S6S17S2S9cA1A1S7A3").
Hypothesis W1c : ltac2:(tb__ "0|0|
S0S6S17S2S9dA1A1S7A3").
Hypothesis W2 : ltac2:(tb__ "0|0|
S0S6S17S2S99A1A1S7A3").
Hypothesis W1r : ltac2:(tb__ "0|0|
S0S6S17S2S9eA1A1S7A3").
Hypothesis W2r : ltac2:(tb__ "0|0|
S0S6S17S2S9aA1A1S7A3").

Variable s sr : wsub.
Hypothesis ENT : ltac2:(tb__ "0|0|
S0S6S3S99S52VW;Vst;Vtmax;A3Vs;A3S7A3").
Hypothesis SID : ltac2:(tb__ "0|0|
S0S6S4eVs;S4cA2S7A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S6S5fS16S20S1aS2S52VW;Vst;Vtmax;A3A1A1A1SaS16S55S5bA3A3S7A3").
Hypothesis ENTr : ltac2:(tb__ "0|0|
S0S6S3S9aS53VW;Vst;Vtmax;A3Vsr;A3S7A3").
Hypothesis SIDr : ltac2:(tb__ "0|0|
S0S6S4eVsr;S4cA2S7A3").
Hypothesis FBr : ltac2:(tb__ "0|0|
S0S6S5fS16S20S1aS2S53VW;Vst;Vtmax;A3A1A1A1S55A3S7A3").

Lemma b1_pop : ltac2:(tb__ "0|1|
S66S74S18S9S64Q40M0A1A1S87S18S89VW;Vst;A2S6eVW;Vst;A2S75R7A1S35Z1S6cR9S63G0S1eR7PcA2A2A2A2S4aVsegs;S4dVW;Vst;RaR9R8A5VX;R5R7R6A6S4aVsegs;S4dVW;Vst;RbRaR9A5S59VW;Vst;Vtmax;A3S4fR6Vs;A2R8R7A6F_;F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoE HW HUS HKc Hcnt H.
  pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }

  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in HN, Hcnt |- *.
  assert (E148 : rw rhoE 148%positive = Z_to_bv 64 (Size (cls_of nv))). { rewrite <- (Hagw 148%positive) by (unfold GW; lia). reflexivity. }
  assert (E149 : rw rhoE 149%positive = Z_to_bv 64 (cnt_of A nv)). { rewrite <- (Hagw 149%positive) by (unfold GW; lia). reflexivity. }
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  assert (E159 : rw rhoE 159%positive = Z_to_bv 64 (chk_of A nv)). { rewrite <- (Hagw 159%positive) by (unfold GW; lia). reflexivity. }

  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p (((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_s1) ++ F_gen) -> holds rhoE p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa p (HXF p Hp)). }
  assert (Hnv : nv <= 64512).
  { pose proof (HFX (SPUle (SVar 12) (SLit 64512)) ltac:(apply in_or_app; right; unfold F_gen; cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity)) as F. cbn [holds eval] in F.
    rewrite E12, u64_lit in F by lia. exact F. }
  pose proof (cls_facts nv ltac:(lia)) as (C1 & C2 & C3 & C4).
  pose proof (pc_entry_facts segs A rhoE tp _ nv HA ltac:(lia) Hcnt) as PF. cbn zeta in PF.
  destruct PF as (Hci & Kcnt & Ksz & Kch & Hc16 & Hch & PE & PS).
  pose proof HA as (HG & HR & HF & HRest & HM). pose proof HG as HG0.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  clear G15 G16 G17 G18 G20 G21.
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _ & _). unfold IMG_LO, IMG_HI in TI.

  assert (EB : bv_unsigned (eval rhoE pc_base) = ag_thread (aa_geom A) + 208 + 80 * cls_of nv).
  { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
    rewrite (Z.mod_small (cls_of nv * 80)) by lia. rewrite (Z.mod_small (ag_thread (aa_geom A) + 208)) by lia. rewrite Z.mod_small by lia. lia. }

  assert (Hhigh : holds rhoE F_sp_high) by (apply HFX; apply in_or_app; left; apply in_or_app; left; apply in_or_app; right; cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity).
  cbn [map app] in HXskel.
  destruct (ss_objs (ax_S X)) as [|osw orest] eqn:EO; [cbn [map] in HXskel; exfalso; clear -HXskel; discriminate HXskel|].
  cbn [map] in HXskel.
  assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) HXskel).
  assert (SKrest : map skel orest = map skel ((unwind_objs W ++ A_globals) ++ RT_m1)) by exact (f_equal (@tl _) HXskel).
  destruct (sw_range_gen _ rhoE _ _ osw Hsm ltac:(rewrite EO; left; reflexivity) SKsw Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoE osw)) by (rewrite (sw_lo_gen rhoE osw SKsw); exact Htop).

  assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear TI G19; lia|clear TI G19; lia]. apply Forall_forall. intros p Hp.
    assert (Hp' : In p (unwind_factsS W st)).
    { destruct st; [apply chain_pre_in; exact Hp|]. exact (chain_pre_factsS' _ _ _ Hp). }
    apply HFX. apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. exact Hp'. }

  assert (DISJ : forall lo' hi', 288 <= lo' -> lo' <= hi' <= 3168 ->
            Forall (fun o' => ranges_disjoint (obj_range rhoE o') (ag_thread (aa_geom A) + lo', ag_thread (aa_geom A) + hi')) (ss_objs (ax_S X))).
  { intros lo' hi' Hlo' Hhi'. rewrite EO. constructor.
    - clear -SW0 G6 Hlo' Hhi'. unfold ranges_disjoint. cbn [fst snd]. lia.
    - apply (Forall_ranges_skel rhoE (fun r => ranges_disjoint r (ag_thread (aa_geom A) + lo', ag_thread (aa_geom A) + hi')) orest _ SKrest).
      apply Forall_app. split.
      + apply Forall_app. split.
        * eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
          unfold ranges_disjoint. rewrite !obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi' B; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]). cbn [fst snd]. (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi' B; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]).
        * unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
          repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); cbn [fst snd eval]; rewrite ?u64_lit by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]).
      + unfold RT_m1, RT_m0, O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_self_tsd, O_tsd0, O_ctx8, O_ctx98, O_T0, O_T40, O_T3168, O_cfa, O_pga, O_pgb, O_mcs,
               O_insta, O_insta2, O_instb, O_rss, O_cfb, O_cfc, O_rms, O_ppf, O_hooks, O_lsan, O_cft, O_afl, O_csd, O_die.
        unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); cbn [fst snd eval];
          rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]). }

  assert (PRES : forall lo' hi', 0 <= lo' -> hi' <= 4096 -> present (view segs (rm rhoE)) (ag_thread (aa_geom A) + lo') (ag_thread (aa_geom A) + hi') ->
            forall off, lo' <= off < hi' -> wok_of segs (rm rhoE) (Z_to_bv 64 (ag_thread (aa_geom A) + off)) = true
                                       /\ exists x, rd_of segs (rm rhoE) (Z_to_bv 64 (ag_thread (aa_geom A) + off)) = Some x).
  { intros lo' hi' Hlo0 Hhi0 HP off Hoff. destruct (HP (ag_thread (aa_geom A) + off) ltac:(lia)) as [b Hb].
    clear -Hb G5 G6 G24 TI Hlo0 Hhi0 Hoff. rewrite view_in in Hb by (clear TI; lia).

    eapply wok_rd_off_image2; [| |exact Hb]; [clear TI; lia | lia]. }

  assert (ECH : soff rhoE choff = 16 + 4 * (cnt_of A nv - 1)).
  { unfold choff, V_CNT. rewrite soff_snorm. unfold U. cbn [eval]. rewrite E149. rewrite add_val, sll_val, add_val, !u64_lit by lia.
    replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
    replace ((cnt_of A nv + (2 ^ 64 - 1)) mod 2 ^ 64) with (cnt_of A nv - 1) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
    change (2 mod 64) with 2. rewrite ?u64_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia.
    unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec ((cnt_of A nv - 1) * 2 ^ 2 + 16) (2 ^ 63)); lia. }
  assert (E80 : soff rhoE (SLit 80) = 80) by (apply soff_lit_small; lia).

  assert (H1 : SPA segs (JG W st A Kc rho) X1 rhoE tp w).
  { unfold X1, addobj.
    apply (SPA_carve_gen segs (JG W st A Kc rho) rhoE X tp w pc_base 0 4 _ (ss_next (ax_S X)) H W1 ltac:(lia)); rewrite ?EB; try liaZ.
    - unfold gcells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width c_val]; rewrite ?soff_lit_small by lia; lia.
    - replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 0) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv)) by lia.
      replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 4) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + 4)) by lia.
      apply DISJ; lia.
    - intros off Hoff. replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + off) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + off)) by lia.
      apply (PRES (208 + 80 * cls_of nv) (208 + 80 * cls_of nv + 80) ltac:(lia) ltac:(lia)); [|lia].
      intros z Hz. apply PE. lia.
    - unfold gcells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val Z.to_nat Pos.to_nat]; rewrite ?soff_lit_small by lia.
      intros j Hj. unfold V_CNT. cbn [eval]. rewrite E149. specialize (Kcnt j Hj). cbn [c_addr c_w c_val] in Kcnt.
      rewrite view_in in Kcnt by lia. rewrite Z.add_0_r. exact Kcnt.
    - unfold xwords_clear. rewrite HXX. intros rr y j [].
  }
  assert (NX1 : ss_next (ax_S X1) = ss_next (ax_S X)) by reflexivity.
  assert (OB1 : ss_objs (ax_S X1) = ss_objs (ax_S X) ++ [O_pcc]) by reflexivity.

  assert (H1b : SPA segs (JG W st A Kc rho) X1b rhoE tp w).
  { unfold X1b, addobj.
    apply (SPA_carve_gen segs (JG W st A Kc rho) rhoE X1 tp w pc_base 8 16 _ (ss_next (ax_S X)) H1 W1b ltac:(rewrite NX1; lia)); rewrite ?EB; try liaZ.
    - unfold gcells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width c_val]; rewrite ?soff_lit_small by lia; lia.
    - rewrite OB1. apply Forall_app. split.
      + replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 8) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + 8)) by lia.
        replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 16) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + 16)) by lia.
        apply DISJ; lia.
      + constructor; [|constructor]. unfold O_pcc, ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EB. clear. lia.
    - intros off Hoff. replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + off) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + off)) by lia.
      apply (PRES (208 + 80 * cls_of nv) (208 + 80 * cls_of nv + 80) ltac:(lia) ltac:(lia)); [|lia].
      intros z Hz. apply PE. lia.
    - unfold gcells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val Z.to_nat Pos.to_nat]; rewrite ?soff_lit_small by lia.
      intros j Hj. unfold V_SIZE. cbn [eval]. rewrite E148. specialize (Ksz j Hj). cbn [c_addr c_w c_val] in Ksz.
      rewrite view_in in Ksz by lia. exact Ksz.
    - unfold xwords_clear, X1, addobj. cbn [ax_X ax_setS]. rewrite HXX. intros rr y j [].
  }
  assert (NX1b : ss_next (ax_S X1b) = ss_next (ax_S X)) by reflexivity.
  assert (OB1b : ss_objs (ax_S X1b) = (ss_objs (ax_S X) ++ [O_pcc]) ++ [O_pcs]) by reflexivity.

  assert (H1c : SPA segs (JG W st A Kc rho) X1c rhoE tp w).
  { unfold X1c, addobj.
    apply (SPA_carve_gsym segs (JG W st A Kc rho) rhoE X1b tp w pc_base choff (SLit 80) _ (ss_next (ax_S X)) H1b W1c ltac:(rewrite NX1b; lia));
      rewrite ?EB, ?ECH, ?E80; try liaZ.
    - unfold gcells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width c_val]; rewrite ?ECH; lia.
    - rewrite OB1b. apply Forall_app. split; [apply Forall_app; split|].
      + replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + (16 + 4 * (cnt_of A nv - 1))) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + (16 + 4 * (cnt_of A nv - 1)))) by lia.
        replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 80) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + 80)) by lia.
        apply DISJ; lia.
      + constructor; [|constructor]. unfold O_pcc, ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EB. clear -Hcnt. lia.
      + constructor; [|constructor]. unfold O_pcs, ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EB. clear -Hcnt. lia.
    - intros off Hoff. replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + off) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + off)) by lia.
      apply (PRES (208 + 80 * cls_of nv) (208 + 80 * cls_of nv + 80) ltac:(lia) ltac:(lia)); [|lia].
      intros z Hz. apply PE. lia.
    - unfold gcells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val Z.to_nat Pos.to_nat]; rewrite ?ECH.
      intros j Hj. unfold V_CH. cbn [eval]. rewrite E159. specialize (Kch j Hj). cbn [c_addr c_w c_val] in Kch.
      rewrite view_in in Kch by lia.
      replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + (16 + 4 * (cnt_of A nv - 1)) + Z.of_nat j)
        with (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 16 + 4 * (cnt_of A nv - 1) + Z.of_nat j) by lia. exact Kch.
    - unfold xwords_clear, X1b, X1, addobj. cbn [ax_X ax_setS]. rewrite HXX. intros rr y j [].
  }
  assert (NX1c : ss_next (ax_S X1c) = ss_next (ax_S X)) by reflexivity.
  assert (OB1c : ss_objs (ax_S X1c) = ((ss_objs (ax_S X) ++ [O_pcc]) ++ [O_pcs]) ++ [O_pck]) by reflexivity.

  assert (H2 : SPA segs (JG W st A Kc rho) X2 rhoE tp w).
  { unfold X2, addobj.
    apply (SPA_carve_gen segs (JG W st A Kc rho) rhoE X1c tp w vT 2768 3168 [] (ss_next (ax_S X)) H1c W2 ltac:(rewrite NX1c; lia));
      unfold vT; cbn [eval]; rewrite ?E151, ?u64_lit by lia; try liaZ.
    - unfold gcells_inside. constructor.
    - rewrite OB1c. apply Forall_app. split; [apply Forall_app; split; [apply Forall_app; split; [apply DISJ; lia|]|]|];
        (constructor; [|constructor]); unfold O_pcc, O_pcs, O_pck, ranges_disjoint.
      + rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EB. clear -C1. lia.
      + rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EB. clear -C1. lia.
      + unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite ECH, E80, EB. clear -C1 Hcnt. lia.
    - intros off Hoff. apply (PRES 2768 3168 ltac:(lia) ltac:(lia) PS). exact Hoff.
    - unfold gcells_in_view. constructor.
    - unfold xwords_clear, X1c, X1b, X1, addobj. cbn [ax_X ax_setS]. rewrite HXX. intros rr y j [].
  }

  unfold C2p.
  apply (SPA_entails_sem segs (JG W st A Kc rho) GW X2 (C2p0 W st tmax) (F_cls ++ F_pop) s rhoE tp w ENT SID).
  - apply stableA_withG; [intros r1 r2 Hg Hag; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
  - exact FB.
  - intros rho' tp' tr' md' [Hag' _] _.
    assert (AG : agree_below GW (rhoM_of A rho) (rho_sub rho' s)).
    { eapply agree_below_trans; [exact Hag' | apply rho_sub_agree; exact SID]. }
    destruct AG as (AGw & _ & _).
    assert (R148 : rw (rho_sub rho' s) 148%positive = Z_to_bv 64 (Size (cls_of nv))) by (rewrite <- (AGw 148%positive) by (unfold GW; lia); reflexivity).
    assert (R149 : rw (rho_sub rho' s) 149%positive = Z_to_bv 64 (cnt_of A nv)) by (rewrite <- (AGw 149%positive) by (unfold GW; lia); reflexivity).
    assert (R157 : rw (rho_sub rho' s) 157%positive = Z_to_bv 64 (needed8 nv)) by (rewrite <- (AGw 157%positive) by (unfold GW; lia); reflexivity).
    assert (R158 : rw (rho_sub rho' s) 158%positive = Z_to_bv 64 (cls_of nv)) by (rewrite <- (AGw 158%positive) by (unfold GW; lia); reflexivity).
    assert (R159 : rw (rho_sub rho' s) 159%positive = Z_to_bv 64 (chk_of A nv)) by (rewrite <- (AGw 159%positive) by (unfold GW; lia); reflexivity).
    clear -R148 R149 R157 R158 R159 C1 C2 C3 C4 Hcnt Hc16 Hch.
    unfold F_cls, F_pop, V_CLS, V_ND, V_SIZE, V_CNT, V_CH. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?R148, ?R149, ?R157, ?R158, ?R159; rewrite ?u64_lit by lia; lia.
  - exact H2.
Qed.

Lemma b1_refill : ltac2:(tb__ "0|1|
S66S74S18S9S64Q40M0A1A1S87S18S89VW;Vst;A2S6eVW;Vst;A2S75R7A1S0S33S6cR9S63G0S1eR7PcA2A2A2Z0A3S4aVsegs;S4dVW;Vst;RaR9R8A5VX;R5R7R6A6S4aVsegs;S4dVW;Vst;RbRaR9A5S5aVW;Vst;Vtmax;A3S4fR6Vsr;A2R8R7A6F_;F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoE HW HUS HKc Hcnt H.
  pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }

  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in HN, Hcnt |- *.
  assert (E148 : rw rhoE 148%positive = Z_to_bv 64 (Size (cls_of nv))). { rewrite <- (Hagw 148%positive) by (unfold GW; lia). reflexivity. }
  assert (E149 : rw rhoE 149%positive = Z_to_bv 64 (cnt_of A nv)). { rewrite <- (Hagw 149%positive) by (unfold GW; lia). reflexivity. }
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  assert (E159 : rw rhoE 159%positive = Z_to_bv 64 (chk_of A nv)). { rewrite <- (Hagw 159%positive) by (unfold GW; lia). reflexivity. }

  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p (((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_s1) ++ F_gen) -> holds rhoE p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa p (HXF p Hp)). }
  assert (Hnv : nv <= 64512).
  { pose proof (HFX (SPUle (SVar 12) (SLit 64512)) ltac:(apply in_or_app; right; unfold F_gen; cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity)) as F. cbn [holds eval] in F.
    rewrite E12, u64_lit in F by lia. exact F. }
  pose proof (cls_facts nv ltac:(lia)) as (C1 & C2 & C3 & C4).
  pose proof (pc_entry_facts0 segs A rhoE tp _ nv HA ltac:(lia) Hcnt) as PF. cbn zeta in PF.
  destruct PF as (K0 & PE & PS).
  pose proof HA as (HG & HR & HF & HRest & HM). pose proof HG as HG0.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  clear G15 G16 G17 G18 G20 G21.
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _ & _). unfold IMG_LO, IMG_HI in TI.

  assert (EB : bv_unsigned (eval rhoE pc_base) = ag_thread (aa_geom A) + 208 + 80 * cls_of nv).
  { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
    rewrite (Z.mod_small (cls_of nv * 80)) by lia. rewrite (Z.mod_small (ag_thread (aa_geom A) + 208)) by lia. rewrite Z.mod_small by lia. lia. }

  assert (Hhigh : holds rhoE F_sp_high) by (apply HFX; apply in_or_app; left; apply in_or_app; left; apply in_or_app; right; cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity).
  cbn [map app] in HXskel.
  destruct (ss_objs (ax_S X)) as [|osw orest] eqn:EO; [cbn [map] in HXskel; exfalso; clear -HXskel; discriminate HXskel|].
  cbn [map] in HXskel.
  assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) HXskel).
  assert (SKrest : map skel orest = map skel ((unwind_objs W ++ A_globals) ++ RT_m1)) by exact (f_equal (@tl _) HXskel).
  destruct (sw_range_gen _ rhoE _ _ osw Hsm ltac:(rewrite EO; left; reflexivity) SKsw Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoE osw)) by (rewrite (sw_lo_gen rhoE osw SKsw); exact Htop).

  assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear TI G19; lia|clear TI G19; lia]. apply Forall_forall. intros p Hp.
    assert (Hp' : In p (unwind_factsS W st)).
    { destruct st; [apply chain_pre_in; exact Hp|]. exact (chain_pre_factsS' _ _ _ Hp). }
    apply HFX. apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. exact Hp'. }

  assert (DISJ : forall lo' hi', 288 <= lo' -> lo' <= hi' <= 3168 ->
            Forall (fun o' => ranges_disjoint (obj_range rhoE o') (ag_thread (aa_geom A) + lo', ag_thread (aa_geom A) + hi')) (ss_objs (ax_S X))).
  { intros lo' hi' Hlo' Hhi'. rewrite EO. constructor.
    - clear -SW0 G6 Hlo' Hhi'. unfold ranges_disjoint. cbn [fst snd]. lia.
    - apply (Forall_ranges_skel rhoE (fun r => ranges_disjoint r (ag_thread (aa_geom A) + lo', ag_thread (aa_geom A) + hi')) orest _ SKrest).
      apply Forall_app. split.
      + apply Forall_app. split.
        * eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
          unfold ranges_disjoint. rewrite !obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi' B; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]). cbn [fst snd]. (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi' B; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]).
        * unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
          repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); cbn [fst snd eval]; rewrite ?u64_lit by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]).
      + unfold RT_m1, RT_m0, O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_self_tsd, O_tsd0, O_ctx8, O_ctx98, O_T0, O_T40, O_T3168, O_cfa, O_pga, O_pgb, O_mcs,
               O_insta, O_insta2, O_instb, O_rss, O_cfb, O_cfc, O_rms, O_ppf, O_hooks, O_lsan, O_cft, O_afl, O_csd, O_die.
        unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); cbn [fst snd eval];
          rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]). }

  assert (PRES : forall lo' hi', 0 <= lo' -> hi' <= 4096 -> present (view segs (rm rhoE)) (ag_thread (aa_geom A) + lo') (ag_thread (aa_geom A) + hi') ->
            forall off, lo' <= off < hi' -> wok_of segs (rm rhoE) (Z_to_bv 64 (ag_thread (aa_geom A) + off)) = true
                                       /\ exists x, rd_of segs (rm rhoE) (Z_to_bv 64 (ag_thread (aa_geom A) + off)) = Some x).
  { intros lo' hi' Hlo0 Hhi0 HP off Hoff. destruct (HP (ag_thread (aa_geom A) + off) ltac:(lia)) as [b Hb].
    clear -Hb G5 G6 G24 TI Hlo0 Hhi0 Hoff. rewrite view_in in Hb by (clear TI; lia).

    eapply wok_rd_off_image2; [| |exact Hb]; [clear TI; lia | lia]. }

  assert (H1 : SPA segs (JG W st A Kc rho) X1r rhoE tp w).
  { unfold X1r, addobj.
    apply (SPA_carve_gen segs (JG W st A Kc rho) rhoE X tp w pc_base 0 4 _ (ss_next (ax_S X)) H W1r ltac:(lia)); rewrite ?EB; try liaZ.
    - unfold gcells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width c_val]; rewrite ?soff_lit_small by lia; lia.
    - replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 0) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv)) by lia.
      replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 4) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + 4)) by lia.
      apply DISJ; lia.
    - intros off Hoff. replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + off) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + off)) by lia.
      apply (PRES (208 + 80 * cls_of nv) (208 + 80 * cls_of nv + 80) ltac:(lia) ltac:(lia)); [|lia].
      intros z Hz. apply PE. lia.
    - unfold gcells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val Z.to_nat Pos.to_nat]; rewrite ?soff_lit_small by lia.
      intros j Hj. cbn [eval]. specialize (K0 j Hj). cbn [c_addr c_w c_val] in K0.
      rewrite view_in in K0 by lia. rewrite Z.add_0_r. exact K0.
    - unfold xwords_clear. rewrite HXX. intros rr y j [].
  }

  assert (NX1r : ss_next (ax_S X1r) = ss_next (ax_S X)) by reflexivity.
  assert (OB1 : ss_objs (ax_S X1r) = ss_objs (ax_S X) ++ [O_pcc0]) by reflexivity.
  assert (H2 : SPA segs (JG W st A Kc rho) X2r rhoE tp w).
  { unfold X2r, addobj.
    apply (SPA_carve_gen segs (JG W st A Kc rho) rhoE X1r tp w vT 2768 3168 [] (ss_next (ax_S X)) H1 W2r ltac:(rewrite NX1r; lia));
      unfold vT; cbn [eval]; rewrite ?E151, ?u64_lit by lia; try liaZ.
    - unfold gcells_inside. constructor.
    - rewrite OB1. apply Forall_app. split; [apply DISJ; lia|]. constructor; [|constructor].
      unfold O_pcc0, ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EB. clear -C1. lia.
    - intros off Hoff. apply (PRES 2768 3168 ltac:(lia) ltac:(lia) PS). exact Hoff.
    - unfold gcells_in_view. constructor.
    - unfold xwords_clear, X1r, addobj. cbn [ax_X ax_setS]. rewrite HXX. intros rr y j [].
  }

  unfold C2r.
  apply (SPA_entails_sem segs (JG W st A Kc rho) GW X2r (C2r0 W st tmax) F_cls sr rhoE tp w ENTr SIDr).
  - apply stableA_withG; [intros r1 r2 Hg Hag; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
  - exact FBr.
  - intros rho' tp' tr' md' [Hag' _] _.
    assert (AG : agree_below GW (rhoM_of A rho) (rho_sub rho' sr)).
    { eapply agree_below_trans; [exact Hag' | apply rho_sub_agree; exact SIDr]. }
    destruct AG as (AGw & _ & _).
    assert (R148 : rw (rho_sub rho' sr) 148%positive = Z_to_bv 64 (Size (cls_of nv))) by (rewrite <- (AGw 148%positive) by (unfold GW; lia); reflexivity).
    assert (R149 : rw (rho_sub rho' sr) 149%positive = Z_to_bv 64 (cnt_of A nv)) by (rewrite <- (AGw 149%positive) by (unfold GW; lia); reflexivity).
    assert (R157 : rw (rho_sub rho' sr) 157%positive = Z_to_bv 64 (needed8 nv)) by (rewrite <- (AGw 157%positive) by (unfold GW; lia); reflexivity).
    assert (R158 : rw (rho_sub rho' sr) 158%positive = Z_to_bv 64 (cls_of nv)) by (rewrite <- (AGw 158%positive) by (unfold GW; lia); reflexivity).
    assert (R159 : rw (rho_sub rho' sr) 159%positive = Z_to_bv 64 (chk_of A nv)) by (rewrite <- (AGw 159%positive) by (unfold GW; lia); reflexivity).
    clear -R148 R149 R157 R158 R159 C1 C2 C3 C4 Hcnt.
    unfold F_cls, V_CLS, V_ND, V_SIZE, V_CNT, V_CH. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?R148, ?R149, ?R157, ?R158, ?R159; rewrite ?u64_lit by lia; lia.
  - exact H2.
Qed.
End B1B.

Section SPINE2.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S7bS90Vsegs;A1VW;Vst;VA;VKc;S19PcA1A6").
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let Xa : axst := ltac2:(tb__ "0|0|
S5S50VW;Vst;Vtmax;A3S2S83VnW;Vst;Vtmax;A3A1A2").
Let Xb : axst := ltac2:(tb__ "0|0|
S5S51VW;Vst;Vtmax;A3S2S84VnW;Vst;Vtmax;A3A1A2").

Hypothesis Cert2 : ltac2:(tb__ "0|1|
S0S6Sa6Sa7Ufa0SbS33Z40d40SeS33A1A3S4cSbS4S58VW;Vst;Vtmax;A3SeS4A1M0A3SbS4S50VW;Vst;Vtmax;A3SbS4S51VW;Vst;Vtmax;A3G0A3A3A6S7A3").

Hypothesis OVa : ltac2:(tb__ "0|0|
S0S6S9fP9dS56VW;Vst;Vtmax;A3A2S7A3").
Hypothesis OVb : ltac2:(tb__ "0|0|
S0S6S9fP9dS57VW;Vst;Vtmax;A3A2S7A3").
Hypothesis TABa : ltac2:(tb__ "0|0|
S0S6Sa0P9dS56VW;Vst;Vtmax;A3S8dZ208Sa1Sa3S91S92S93S91S94A1A1A1A1A1A1A5S7A3").
Hypothesis TABb : ltac2:(tb__ "0|0|
S0S6Sa0P9dS57VW;Vst;Vtmax;A3S8dZ18U3eA5S7A3").
Hypothesis Wa' : ltac2:(tb__ "0|0|
S0S6S17S2S83VnW;Vst;Vtmax;A3A1A1S7A3").
Hypothesis Wb' : ltac2:(tb__ "0|0|
S0S6S17S2S84VnW;Vst;Vtmax;A3A1A1S7A3").
Hypothesis Da' : ltac2:(tb__ "0|4|
S0S10S8S9S8S14S14A2M0A1M1S9S16A1M2A2M3A1S98S2S50VW;Vst;Vtmax;A3A1S2S83VnW;Vst;Vtmax;A3A1A2SfG3ScG1G2SbG0ScS14S14S56VW;Vst;Vtmax;A3S19S5cA1A4SeG0A1A3SeS16A1A4A2A3").
Hypothesis Db' : ltac2:(tb__ "0|4|
S0S10S8S9S8S14S14A2M0A1M1S9S16A1M2A2M3A1S98S2S51VW;Vst;Vtmax;A3A1S2S84VnW;Vst;Vtmax;A3A1A2SfG3ScG1G2SbG0ScS14S14S57VW;Vst;Vtmax;A3S19S5cA1A4SeG0A1A3SeS16A1A4A2A3").
Hypothesis NXa : ltac2:(tb__ "0|0|
S0S34S1aS2S83VnW;Vst;Vtmax;A3A1A1S1aS2S50VW;Vst;Vtmax;A3A1A1A3").
Hypothesis NXb : ltac2:(tb__ "0|0|
S0S34S1aS2S84VnW;Vst;Vtmax;A3A1A1S1aS2S51VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fa : ltac2:(tb__ "0|0|
S60S16S21S97S1cZ200A1S19S5dA1A3S1bS2S50VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S60S16S28S21S97S1cZ200A1S19S5dA1A3A1S1bS2S51VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Ga : ltac2:(tb__ "0|0|
S5eS16S54S1bS2S50VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Gb : ltac2:(tb__ "0|0|
S5eS16S54S1bS2S51VW;Vst;Vtmax;A3A1A1A3").

Hypothesis SKa : ltac2:(tb__ "0|1|
S0S9S8S8S14S14A2S14A2M0A1S47S15G0S3eS1fS2VXa;A1A1A4S47S15G0S3eSaS15SbS15S8bSaS15S72VW;A1S73A3A3S8cA3A4A3").
Hypothesis SKb : ltac2:(tb__ "0|1|
S0S9S8S8S14S14A2S14A2M0A1S47S15G0S3eS1fS2VXb;A1A1A4S47S15G0S3eSaS15SbS15S8bSaS15S72VW;A1S73A3A3S8cA3A4A3").
Hypothesis XXa : ax_X Xa = [].
Hypothesis XXb : ax_X Xb = [].
Hypothesis XFa : ltac2:(tb__ "0|0|
S5eS16SaS16SaS16SaS16S79VW;Vst;A2S78S77A1A3S8aA3S54A3S1bS2VXa;A1A1A3").
Hypothesis XFb : ltac2:(tb__ "0|0|
S5eS16SaS16SaS16SaS16S79VW;Vst;A2S78S77A1A3S8aA3S54A3S1bS2VXb;A1A1A3").
Hypothesis W1a : ltac2:(tb__ "0|0|
S0S6S17S2S41VXa;A1A1A1S7A3").   Hypothesis W1ba : ltac2:(tb__ "0|0|
S0S6S17S2S42VXa;A1A1A1S7A3").  Hypothesis W1ca : ltac2:(tb__ "0|0|
S0S6S17S2S43VXa;A1A1A1S7A3").  Hypothesis W2a : ltac2:(tb__ "0|0|
S0S6S17S2S3fVXa;A1A1A1S7A3").
Hypothesis W1ra : ltac2:(tb__ "0|0|
S0S6S17S2S44VXa;A1A1A1S7A3"). Hypothesis W2ra : ltac2:(tb__ "0|0|
S0S6S17S2S40VXa;A1A1A1S7A3").
Hypothesis W1b : ltac2:(tb__ "0|0|
S0S6S17S2S41VXb;A1A1A1S7A3").   Hypothesis W1bb : ltac2:(tb__ "0|0|
S0S6S17S2S42VXb;A1A1A1S7A3").  Hypothesis W1cb : ltac2:(tb__ "0|0|
S0S6S17S2S43VXb;A1A1A1S7A3").  Hypothesis W2b : ltac2:(tb__ "0|0|
S0S6S17S2S3fVXb;A1A1A1S7A3").
Hypothesis W1rb : ltac2:(tb__ "0|0|
S0S6S17S2S44VXb;A1A1A1S7A3"). Hypothesis W2rb : ltac2:(tb__ "0|0|
S0S6S17S2S40VXb;A1A1A1S7A3").
Variables sa sra sb srb : wsub.
Hypothesis ENTa : ltac2:(tb__ "0|0|
S0S6S3S3fVXa;A1S52VW;Vst;Vtmax;A3Vsa;A3S7A3").
Hypothesis ENTra : ltac2:(tb__ "0|0|
S0S6S3S40VXa;A1S53VW;Vst;Vtmax;A3Vsra;A3S7A3").
Hypothesis ENTb : ltac2:(tb__ "0|0|
S0S6S3S3fVXb;A1S52VW;Vst;Vtmax;A3Vsb;A3S7A3").
Hypothesis ENTrb : ltac2:(tb__ "0|0|
S0S6S3S40VXb;A1S53VW;Vst;Vtmax;A3Vsrb;A3S7A3").
Hypothesis SIDa : ltac2:(tb__ "0|0|
S0S6S4eVsa;S4cA2S7A3").   Hypothesis SIDra : ltac2:(tb__ "0|0|
S0S6S4eVsra;S4cA2S7A3").
Hypothesis SIDb : ltac2:(tb__ "0|0|
S0S6S4eVsb;S4cA2S7A3").   Hypothesis SIDrb : ltac2:(tb__ "0|0|
S0S6S4eVsrb;S4cA2S7A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S6S5fS16S20S1aS2S52VW;Vst;Vtmax;A3A1A1A1SaS16S55S5bA3A3S7A3").
Hypothesis FBr : ltac2:(tb__ "0|0|
S0S6S5fS16S20S1aS2S53VW;Vst;Vtmax;A3A1A1A1S55A3S7A3").

Theorem spine_s2 : ltac2:(tb__ "0|0|
S87OF_;S66S74S18S9S64Q40A1A1S88S89VW;Vst;A2S6eVW;Vst;A2S75R6A1S4bVsegs;R9VJ;VW;Vst;R8R7A4A3S18S86Vsegs;RbS4aVsegs;S4dVW;Vst;RaR9R8A5S59VW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;S18S86Vsegs;RcS4aVsegs;S4dVW;Vst;RbRaR9A5S5aVW;Vst;Vtmax;A3R1R8A5R7A4FrhoE;S18S86Vsegs;RdS4aVsegs;S4dVW;Vst;RcRbRaA5S58VW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HW HUS HKc Hokf HP HR rhoE.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as Hc0.
  change (0 <= cnt_of A (bv_unsigned (rw rho 12%positive))) in Hc0.
  apply (cfg_soundA segs 4000%nat [0x40d40] GW [C1g W st tmax] [E2a W st tmax; E2b W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hokf; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
  - exact Cert2.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sa))].
        apply (b1_pop nW st tmax Xa SKa XXa XFa W1a W1ba W1ca W2a sa sra ENTa SIDa FB ENTra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR (rho_sub rhoX sra))].
        apply (b1_refill nW st tmax Xa SKa XXa XFa W1ra W2ra sa sra ENTa FB ENTra SIDra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sb))].
        apply (b1_pop nW st tmax Xb SKb XXb XFb W1b W1bb W1cb W2b sb srb ENTb SIDb FB ENTrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR (rho_sub rhoX srb))].
        apply (b1_refill nW st tmax Xb SKb XXb XFb W1rb W2rb sb srb ENTb FB ENTrb SIDrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
  - left. reflexivity.
Qed.
End SPINE2.
End SpineCallocS3.

