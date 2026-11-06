(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0236. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAHarnessSK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0249. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAHarness1 PnAHarness2 PnAHarness3 PnAHarness3b PnAHarness4 PnAHarness5 PnAHarness6 PnAHarness7 PnAHarness8 PnAHarness8b PnAHarness9 PnAHarness10 PnAHarness11. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.LibIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5AFrameKR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.LibIfaceAB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunHA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnTopS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.PnTopAL OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.NTopAsmA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.StrictOfB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.PnRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnRunNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnCDtorSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0236.PnASnkAnn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0236.PnAEstkAnn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0236.PnASnkDtor OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0236.PnAEstkDtor OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.PnAHarnessStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206.PnAHarnessKit4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarnessSK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0249.PnAHarnessKit3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAHarnessKit5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarness1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarness2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarness3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarness3b OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarness4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarness5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarness6 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarness7 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarness8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarness8b OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarness9 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarness10 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarness11.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PQHA.
Import L5A. Import L5CA. Import L5SAR. Import PQHAS. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RSEGS := Asan.M.loaded_segments.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.

(* [comment removed for export] *)
Definition WF : list L5.range := map (fun iv => (fst iv, snd iv - fst iv)) PNTAL.foot_a ++ [(0x693a5c, 4)].      (* [comment removed for export] *)
Lemma WF_eq : WF = [(0x692100, 2); (0x692330, 2); (0x692332, 1854); (0x693198, 88); (0x6b3b50, 544); (0x693a5c, 4)].
Proof. unfold WF. rewrite PNTAL.foot_a_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ffc_app k (l l' : list fframe) : ff_count k (l ++ l') = (ff_count k l + ff_count k l')%nat.
Proof. unfold ff_count. rewrite list_basics.list.filter_app. apply length_app. Qed.
Lemma ffc_incl k (l l' : list fframe) : base.NoDup l -> incl l l' -> (ff_count k l <= ff_count k l')%nat.
Proof.
  intros ND HI. unfold ff_count. apply list_relations.list.submseteq_length. apply list_relations.list.NoDup_submseteq. apply list_relations.list.NoDup_filter. exact ND.
  intros x Hx. apply list_basics.list.list_elem_of_filter in Hx. apply list_basics.list.list_elem_of_filter. destruct Hx as [P Hx]. split. exact P.
  apply base.list_elem_of_In. apply HI. apply base.list_elem_of_In. exact Hx.
Qed.
Lemma nodup_lk (FF LK : list fframe) : base.NoDup (map ff_addr (FF ++ LK)) -> base.NoDup LK.
Proof. intros ND. apply base.NoDup_ListNoDup. apply base.NoDup_ListNoDup in ND. apply NoDup_map_inv in ND. apply NoDup_app_remove_l in ND. exact ND. Qed.

(* [comment removed for export] *)
Lemma res_nonneg (tsp : list (list Z) -> list Z -> credit) (RES : credit) :
  (forall D RC, PmSpecs.PMSP.credit_le PmSpecs.PMSP.cr0 (tsp D RC) /\ PmSpecs.PMSP.credit_le (tsp D RC) RES) -> 0 <= fst RES /\ 0 <= snd RES.
Proof. intros H. destruct (H [] []) as [(A1 & A2) (B1 & B2)]. unfold PmSpecs.PMSP.cr0 in *. cbn [fst snd] in *. split; lia. Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.

Section TOP.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HIR : asan_iface) (IL : icpt_layout) (RES : credit).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HIR.
Hypothesis ICok : aicpt_ok L ar IL SCFG HIR.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HIR PMA.EXT.
Hypothesis RES0 : 0 <= fst RES /\ 0 <= snd RES.
Let LYa := PMA.ly_as0 L C LY.
Hypothesis DEPS : NTASMA.harness_depsS L ar HIR RES.

(* [comment removed for export] *)
Lemma wapp_WF : PMKA.wapp WF.
Proof. intros r Hr. rewrite WF_eq in Hr. cbn in Hr. unfold BIGSHADOW_LO, BIGSHADOW_HI. repeat (destruct Hr as [<-|Hr]; [cbn; lia|]). destruct Hr. Qed.
Lemma wloc_WF : forall a, L5.outside WF a -> L5.outside (PMSPA.loc_W PMA.AD) a.
Proof.
  intros a Ho r Hr. apply Ho. unfold PMSPA.loc_W in Hr. cbn in Hr. rewrite WF_eq. cbn.
  destruct Hr as [<-|[<-|[]]]; [right; right; left; reflexivity| right; right; right; left; reflexivity].
Qed.
Lemma wsys_WF : forall a, L5.outside WF a -> L5.outside [(0x692330, 2)] a.
Proof. intros a Ho r [<-|[]]. apply Ho. rewrite WF_eq. cbn. right; left; reflexivity. Qed.
Lemma werr_WF : forall a, L5.outside WF a -> L5.outside (PmSpecs.PMSP.err_W PMA.AD) a.
Proof.
  intros a Ho r Hr. apply Ho. unfold PmSpecs.PMSP.err_W in Hr. cbn in Hr. rewrite WF_eq. cbn.
  destruct Hr as [<-|[<-|[]]]; [left; reflexivity| do 4 right; left; reflexivity].
Qed.
Lemma wjnk_WF : forall a, L5.outside WF a -> L5.outside [(6896220, 4)] a.      (* [comment removed for export] *)
Proof. intros a Ho r [<-|[]]. apply Ho. rewrite WF_eq. cbn. do 5 right; left; reflexivity. Qed.

(* [comment removed for export] *)
Lemma room_of (FF LK : list fframe) F rs :
  (forall k, In k [0; 1; 2; 3; 4; 5] -> Z.of_nat (ff_count k (FF ++ LK)) + FRAMES k <= ff_cap k) ->
  forall LKc, incl LKc LK -> base.NoDup (map ff_addr ((F, 5, rs) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, rs) :: FF) LKc.
Proof.
  intros RM LKc INC ND k Hk. cbn [app].
  assert (ND' : base.NoDup (FF ++ LKc)).
  { apply base.NoDup_ListNoDup. apply base.NoDup_ListNoDup in ND. apply NoDup_map_inv in ND. inversion ND; assumption. }
  assert (INC' : incl (FF ++ LKc) (FF ++ LK)) by (intros x Hx; apply in_app_or in Hx; apply in_or_app; destruct Hx as [Hx|Hx]; [left; exact Hx| right; apply INC; exact Hx]).
  assert (HD : ff_count k (((F, 5, rs) : fframe) :: FF ++ LKc) = ((if Z.eqb 5 k then 1 else 0) + ff_count k (FF ++ LKc))%nat).
  { unfold ff_count. rewrite list_basics.list.filter_cons. cbn [ff_class fst snd]. destruct (base.decide _) as [X|X]; destruct (Z.eqb 5 k) eqn:E; cbn [length]; try reflexivity; exfalso; first [exact X | exact (X I)]. }
  assert (Hk' : In k [0; 1; 2; 3; 4; 5]) by (cbn in Hk |- *; tauto).
  rewrite HD. pose proof (ffc_incl k _ _ ND' INC') as LE. pose proof (RM k Hk') as X. unfold FRAMES in X.
  destruct (Z.eqb 5 k) eqn:E; cbn [Nat.add]; rewrite ?Nat2Z.inj_succ; lia.
Qed.

Lemma stksh_of (M : word -> option byte) sp : sp <= ar_sptop ar ->
  shadow_zero M (sp - STK) ((Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - STK)) / 8) -> shadow_zero M (sp - STK) 4608.
Proof.
  intros H SZ j Hj. apply SZ. split; [lia|]. unfold STK in *.
  assert (4608 <= (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 36864)) / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma spa0 : NESKA.spa_pot (NESKA.PMEA L) 0 = (hl_k_per_malloc L * 30, hl_b_lin L * (2 ^ 30 - 1) + hl_b_overhead L * 30).
Proof.
  unfold NESKA.PMEA, NESKA.SP_TA. cbn [NESKA.spa_pot]. unfold NESKA.potT, NESK.ZMAX.
  rewrite (NESKA.steps_pow2 29), NESKA.steps_0, NESKA.cum2_0, (NESKA.cum2_pos (2 ^ 29)) by lia.
  f_equal; lia.
Qed.
Section Credit.
Variables (n : Z) (cr cr4 cr5 cr6 cr9 : credit) (qc b b' : Z).
Hypothesis NR : 0 <= n < 2 ^ 26.
Hypothesis C0 : credit_le (CREDIT RES n) cr.
Let HV := PMSPA.HV L ar.
Lemma cr_facts : hl_k_per_malloc L = 8 /\ hl_b_lin L = 3 /\ hl_b_overhead L = 2 ^ 21.
Proof. exact (PMA.ly_cost L C LY). Qed.
Ltac crt := pose proof cr_facts as (KP & BL & BO); pose proof RES0 as (RK & RB);
  unfold PMSPA.credit_le, PMSPA.credit_keep, PMSPA.scA, PMSPA.cr0, PmSpecs.PMSP.credit_le, PmSpecs.PMSP.credit_keep, PmSpecs.PMSP.cr0, credit_le, credit_sub, CREDIT,
         PQRHA.rdr_cost, PNRNA.pot_runA, NEMA.pot_aeA, PQHA7.AST0, NEM.pot_estack, NEM.EKMAX, NEM.ESZ, PNRNA.TSRES_ME, PNRN.TSRES_ME,
         PQMA.pot_run, PQMA.pot_mparser, PQMA.pot_adaptor, PQMA.pot_vstack, PQMA.pot_textM, PGV8.pot_v8, PGV8.v8_cap, PQMA.pot_ks, PQMA.ks_alloc,
         PQMA.TSRES, PQMA.GMAX, PQMA.SMK, PQMA.SMB, PM.credit_add, PM.cost1, PM.CHUNK, PQMA.PSZ, PQMA.LSZ, PQRHA.mparser_init, PQRHA.ast_init in *;
  rewrite ?spa0 in *;
  cbn [fst snd PQMA.p_sk PQMA.p_tb PQMA.p_bb PQMA.p_bg PQMA.a_lk PQMA.a_key PQMA.a_kg PQMA.a_kb PQMA.a_kbg NEMA.ae_a NEMA.ae_e NEMA.ae_s NEM.en_k NEM.enc0 NESK.sk_c NESK.sink0] in *;
  rewrite ?spa0 in *; unfold PMSPA.scA, PM.credit_add in *; cbn [fst snd] in *;
  subst HV; cbn [HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead LibIfaceAB.heap_view PMSPA.HV] in *;
  rewrite ?KP, ?BL, ?BO in *;
  change (2 ^ 12) with 4096 in *; change (2 ^ (0 + 1)) with 2 in *; change (2 ^ 0) with 1 in *; change (2 ^ 28) with 268435456 in *; change (2 ^ 30) with 1073741824 in *;
  change (2 ^ 29) with 536870912 in *; change (2 ^ 27) with 134217728 in *; change (2 ^ 21) with 2097152 in *; change (2 ^ 26) with 67108864 in *; change (2 ^ 20) with 1048576 in *; lia.
Lemma cr2 : PMSPA.credit_le (PMSPA.scA L (PM.cost1 HV (n + 16))) cr.
Proof. crt. Qed.
Hypothesis K2 : PMSPA.credit_keep cr cr4 (PMSPA.scA L (PM.cost1 HV (n + 16))) PMSPA.cr0.
Lemma cr3 : PMSPA.credit_le (PMSPA.scA L (PM.cost1 HV (n + 32))) cr4.
Proof. crt. Qed.
Hypothesis K3 : PMSPA.credit_keep cr4 cr5 (PMSPA.scA L (PM.cost1 HV (n + 32))) PMSPA.cr0.
Lemma cr4' : PMSPA.credit_le (PMSPA.scA L (PQRHA.rdr_cost HV)) cr5.
Proof. crt. Qed.
Hypothesis K4 : PMSPA.credit_keep cr5 cr6 (PMSPA.scA L (PQRHA.rdr_cost HV)) PMSPA.cr0.
Lemma cr7 : PmSpecs.PMSP.credit_le (PM.credit_add (PM.credit_add (PNRNA.pot_runA L ar (PQRHA.mparser_init qc b) (PQHA7.AST0 b')) (PMSPA.scA L PNRNA.TSRES_ME)) RES) cr6.
Proof. crt. Qed.
Hypothesis K7 : PmSpecs.PMSP.credit_keep cr6 cr9 (PM.credit_add (PNRNA.pot_runA L ar (PQRHA.mparser_init qc b) (PQHA7.AST0 b')) RES) PmSpecs.PMSP.cr0.
Lemma crF : credit_le (credit_sub cr (CREDIT RES n)) cr9.
Proof. crt. Qed.
End Credit.

Local Notation LSt := (PQSTA.TopLSA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A).

Theorem harness_call_okA : lib_call_okA (LayA RES L) ar SCFG (HAJ.strict_of HIR) LSt.
Proof.
  destruct DEPS as [STR ISS RDC SYS RST PARSE RDD OPD LCD IOD].
  pose proof (HAJ.aex_stack_free _ _ _ _ _ EXT) as SF. cbn [HAJ.ec_sf_pc HAJ.ec_sf_scr PMA.EXT] in SF.
  (* [comment removed for export] *)
  pose proof (PEAEKD.estk_dtor_ok L ar C HIR LY HIok (PEAEKAN.ann_shrink_e_ok L ar C HIR LY HIok EXT) (PEAEKAN.ann_delete_e_ok L ar C HIR LY HIok EXT) OPD) as ESTK.
  pose proof (PEASKD.sink_dtor_ok L ar C HIR (NESKA.PMEA L) LY HIok (PEASKAN.ann_shrink_b_ok L ar C HIR LY HIok EXT) (PEASKAN.ann_delete_b_ok L ar C HIR LY HIok EXT) OPD) as SNK.
  unfold lib_call_okA. intros fx g LB FF LK cr A sp ptr ra payload R M model K PRE HHs HALT MI HK KONT.
  destruct PRE as [pra praok psp pgp ptp pa0 pa1 plen pptr ppay pstack pcredit pffroom pffrs pstksh pstat].
  cbn [lla_L lla_gp lla_empty lla_stack lla_frames lla_credit LayA PNTAL.TopLayA_a] in *.
  destruct HHs as (HH & SBLK & CLS13).
  destruct pstack as (A16 & SLO & SHI & SPT & DSCR & DUP).
  set (n := Z.of_nat (length payload)) in *.
  assert (NR : 0 <= n < 2 ^ 26) by (subst n; clear - plen; lia).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WFF & _ & _ & _ & _ & _ & _ & _ & TOP47 & NDB & NDF & _).
  assert (DRG : 0 <= ptr < 2 ^ 64).
  { destruct pptr as [(P0 & PE)|(P0 & INB)]; [rewrite PE; unfold PNTAL.TopLayA_a; cbn; lia|].
    destruct (WB _ INB) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. clear - Q0 Q4 SPT. lia. }
  unfold lib_cfgA in KONT |- *. cbn [lla_L lla_entry LayA PNTAL.TopLayA_a] in KONT |- *. rewrite (L5A.aly_segs L C LYa) in *.
  change (mkCfg (@mkst fx R (Z_to_bv 64 0xaeecc) M (seg_rom RSEGS)) model) with (@L5A.cfg fx R 0xaeecc M model).
  assert (FF5 : ff_room 5 FF LK).
  { unfold ff_room. pose proof (pffroom 5 ltac:(cbn; tauto)) as X. unfold FRAMES in X. lia. }
  apply (PQHA1.entry L ar C HIR LY HIok WF fx R M model K LB FF LK cr A ptr n sp ra g HH (conj HALT MI) HK).
  - exact pa0.
  - exact pa1.
  - exact NR.
  - exact DRG.
  - exact pra.
  - exact praok.
  - exact psp.
  - exact A16.
  - exact ptp.
  - split; [exact A16|]. split; [exact SLO|]. split; [exact SHI|]. split; [exact SPT|]. split; [exact DSCR| exact DUP].
  - exact FF5.
  - exact pffrs.
  - exact pstat.
  - intros V2 cls F fl LK2 M2 model2 fx3 R3 M3 model3 G SE CLS V2A V2R V2S BI3 RI3 Q1 Q10 Q11 Q12 Q20 Q18 Q22 Q23 SZS FAL HSTKb3 LS3.
    assert (GP : getr R (reg 3) = Z_to_bv 64 (pa_gp PMA.AD)) by (rewrite <- L5K.rl3; exact pgp).
    assert (TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite <- L5K.rl4; exact ptp).
    assert (FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f) by (intros f Hf; rewrite <- SE; exact (pffrs f Hf)).
    assert (ROOM : forall LKc, incl LKc LK -> base.NoDup (map ff_addr ((F, 5, V2 - 160 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, V2 - 160 + 32) :: FF) LKc)
      by exact (room_of FF LK F (V2 - 160 + 32) (fun k Hk => pffroom k Hk)).
    assert (STKSH : shadow_zero M (V2 + cls - 36864) 4608) by (rewrite <- SE; exact (stksh_of M sp SHI pstksh)).
    assert (UR1 : U R 1 = ra) by (apply U_of; [rewrite <- L5K.rl1; exact pra| destruct praok; lia]).
    assert (RAok : L5.ra_ok (U R 1)) by (rewrite UR1; exact praok).
    assert (G2R : getr R (reg 2) = Z_to_bv 64 (V2 + cls)) by (rewrite <- SE, <- L5K.rl2; exact psp).
    assert (SRCB : n = 0 \/ (exists B m, In (B, m) LB /\ B <= ptr /\ ptr + n <= B + m)).
    { destruct pptr as [(P0 & _)|(P0 & INB)]; [left; subst n; rewrite P0; reflexivity| right; exists ptr, n; split; [exact INB| lia]]. }
    assert (ACCd : aacc M3 ptr n).
    { destruct pptr as [(P0 & _)|(P0 & INB)]; [subst n; rewrite P0; intros x Hx; cbn in Hx; lia|].
      pose proof BI3 as (_ & _ & _ & _ & _ & _ & EK3 & _).
      destruct (WB _ INB) as ((B0 & _ & B3 & B4 & B5 & B6) & _). cbn [fst snd] in *. unfold app_mem in B6.
      rewrite Forall_forall in SBLK. pose proof (SBLK _ INB) as SB0. cbn [fst snd] in SB0.
      apply (PMFA.accA_agree M M3 ptr n); [| apply (L5CBR.aacc_of_blk M ptr n ptr n SB0); [apply PMKA.mod16_8'; exact B3| lia| lia| lia]].
      intros x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. apply EK3. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split.
      - do 6 right. exists (ptr, n). split; [exact INB|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKA.S_mono; lia.
      - intros rr Hr Hin. rewrite WF_eq in Hr. cbn in Hr. unfold L5.in_rng in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
        repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Hin; lia|]). destruct Hr. }
    (* [comment removed for export] *)
    apply (PQHA2.stage2 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF STR fx3 R3 M3 model3 K ptr n g
             BI3 RI3 HK LS3 Q1 Q10 Q11 Q12 Q20 Q18 Q22 Q23 SZS NR DRG SRCB ACCd HSTKb3 (cr2 n cr NR pcredit)).
    intros fx4 R4 M4 model4 LK4 cr4 A4 s BI4 RI4 S1 S10 S11 S12 S20 S18 S22 S23 VSTR SIZE SSH SLG CK2 SZI4 HSTKa4 HSTKb4 LS4.
    assert (LONG : forall c n0 p, s = PM.VLong c n0 p -> 23 <= n0).
    { intros c n0 p E. destruct (Z_le_gt_dec n 22) as [X|X]; [rewrite (SSH X) in E; discriminate|]. rewrite E in SIZE. cbn in SIZE. lia. }
    (* [comment removed for export] *)
    apply (PQHA3.stage3 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF wloc_WF ISS fx4 R4 M4 model4 K LK4 cr4 A4 s ptr n g
             BI4 RI4 HK LS4 S1 S10 S11 S12 S20 S18 S22 S23 VSTR SIZE LONG NR DRG (cr3 n cr cr4 NR pcredit CK2) SZI4 HSTKa4 HSTKb4).
    intros fx5 R5 M5 model5 LK5 cr5 A5 s' sm BI5 RI5 LS5 P1 P10 P11 P12 P20 P18 P22 P23 P24 VS5 IS5 SIZE5 SMG SMST CK3 SZK5 SZI5 HSTKa5 HSTKb5.
    set (g1 := PMST.ST true (PMST.st_sys g) (PMST.st_err g)) in *.
    (* [comment removed for export] *)
    apply (PQHA3B.stage3b L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A TP fx5 R5 M5 model5 K LK5 cr5 A5 s s' sm ptr n g
             BI5 RI5 HK LS5 P1 P10 P11 P12 P20 P18 P22 P23 P24 DRG VS5 IS5 SIZE5 SMG SMST SZK5 SZI5 HSTKa5 HSTKb5).
    intros fx6 R6 M6 model6 BI6 RI6 LS6 T1 T10 T11 T12 T13 T14 T18 T20 T22 T23 T24 T25 T26 HB6 SIZE6 SMG6 SMST6 HSE6 UO1 UO2 UO3 SZK6 SZE6 SZR6 SZO6 HSTKa6 HSTKb6.
    (* [comment removed for export] *)
    apply (PQHA4.stage4 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF FAL RDC fx6 R6 M6 model6 K LK5 cr5 A5 s s' sm n g
             BI6 RI6 HK LS6 T1 T10 T11 T12 T13 T14 T18 T20 T22 T23 T24 T25 T26 HB6 SIZE6 SMG6 SMST6 HSE6 UO1 UO2 UO3 SZK6 SZE6 SZR6 SZO6 HSTKa6 HSTKb6
             (cr4' n cr cr4 cr5 NR pcredit CK2 CK3)).
    intros fx7 R7 M7 model7 LK7 cr6 A7 qc b b' BI7 RI7 LS7 U1 U18 U20 U21 U22 U23 U24 U25 U26 HB7 SIZE7 SMG7 SMST7 HP7 CK4 HSE7 EC7 SZec7 SZK7 SZE7 HSTKa7 HSTKb7.
    (* [comment removed for export] *)
    apply (PQHA5.stage5 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF wsys_WF SYS fx7 R7 M7 model7 K LK7 cr6 A7 s s' sm
             (PQRHA.mparser_init qc b) (PQRHA.ast_init b') g1 BI7 RI7 HK LS7 U1 U18 U20 U21 U22 U23 U24 U25 U26 HB7 HP7 HSE7 EC7 SZec7 HSTKa7 HSTKb7).
    intros fx8 R8 M8 model8 LK8 A8 BI8 RI8 LS8 W1 W10 W18 W20 W21 W22 W23 W24 W25 W26 HB8 HP8 HEC8 HSE8 HSTKa8 HSTKb8.
    set (g2 := PMST.ST (PMST.st_loc g1) true (PMST.st_err g1)) in *.
    (* [comment removed for export] *)
    apply (PQHA6.stage6 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF FAL RST fx8 R8 M8 model8 K LK8 cr6 A8 s s' sm qc b b' g2
             0 (pa_syscat_obj PMA.AD) BI8 RI8 HK LS8 W1 W10 W18 W20 W21 W22 W23 W24 W25 W26 HB8 HP8 HEC8 HSE8 HSTKa8 HSTKb8).
    intros fx9 R9 M9 model9 LK9 A9 BI9 RI9 LS9 X1 X10 X11 X12 X18 X20 X21 X22 X23 X24 X25 X26 HB9 HP9 HEC9 HSE9 HSTKa9 HSTKb9.
    (* [comment removed for export] *)
    assert (ACCT : PQMA.acct n (PQRHA.mparser_init qc b) (PQRHA.ast_init b') sm).
    { pose proof HB9 as (_ & ISX & _). destruct ISX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IE1 & IE2).
      unfold PQMA.acct, PQMA.kbsize, PQMA.nlv, PM.unread, PQRHA.mparser_init, PQRHA.ast_init. cbn [PQMA.a_kb PQMA.a_lv PQMA.p_src PM.sr_rem PM.vs_size length].
      rewrite IE1, SMG, SIZE5. clear - NR. lia. }
    assert (OACCT : NEMA.oacct n (PQRHA.mparser_init qc b) (PQHA7.AST0 b') sm).
    { pose proof HB9 as (_ & ISX & _). destruct ISX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IE1 & IE2).
      unfold NEMA.oacct, NEMA.phi, NEMA.zsize, NEMA.kbsize, NEMA.nlv, PQHA7.AST0, PQMA.kbsize, PQMA.nlv, PM.unread, PQRHA.mparser_init, PQRHA.ast_init.
      cbn [NEMA.ae_a NEMA.ae_s NESK.sk_z NESK.sink0 PQMA.a_kb PQMA.a_lv PQMA.p_src PM.sr_rem PM.vs_size length].
      rewrite IE1, SMG, SIZE5. clear - NR. lia. }
    apply (PQHA7.stage7 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF FAL werr_WF wjnk_WF RES PARSE fx9 R9 M9 model9 K LK9 cr6 A9
             s s' sm qc b b' g2 (pa_syscat_obj PMA.AD) n BI9 RI9 HK LS9 X1 X10 X11 X12 X18 X20 X21 X22 X23 X24 X25 X26 HB9 HP9 HEC9 HSE9 ACCT OACCT HSTKa9 HSTKb9
             (cr7 n cr cr4 cr5 cr6 qc b b' NR pcredit CK2 CK3 CK4)).
    intros fx10 R10 M10 model10 LK10 cr9 A10 s9 st9 sm9 e9 b9 BI10 RI10 LS10 EMONO Y1 Y10 Y18 Y20 Y21 Y22 Y23 Y24 Y25 Y26 HB10 HP10 GR10 AOK10 HSF10 CK7 HSTKa10 HSTKb10.
    set (g3 := PMST.ST (PMST.st_loc g2) (PMST.st_sys g2) e9) in *.
    (* [comment removed for export] *)
    apply (PQHA8.stage8 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF FAL RDD fx10 R10 M10 model10 K LK10 cr9 A10
             s s' sm9 s9 st9 g3 BI10 RI10 HK LS10 Y1 Y10 Y18 Y20 Y21 Y22 Y23 Y24 Y25 Y26 HB10 HP10 GR10 AOK10 HSF10 HSTKa10 HSTKb10).
    intros fx11 R11 M11 model11 LK11 A11 BI11 RI11 LS11 Z18 Z20 Z21 Z22 Z23 Z24 Z25 Z26 HB11 HSF11 HSTKa11 HSTKb11.
    (* [comment removed for export] *)
    apply (PQHA8B.stage8b L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF FAL ESTK SNK fx11 R11 M11 model11 K LK11 cr9 A11
             s s' sm9 (NEMA.ae_e st9) (NEMA.ae_s st9) g3 BI11 RI11 HK LS11 Z18 Z20 Z21 Z22 Z23 Z24 Z25 Z26 HB11 HSF11 HSTKa11 HSTKb11).
    intros fx12 R12 M12 model12 LK12 A12 BI12 RI12 LS12 V18 V20 V21 V22 V23 V24 V25 V26 HB12 HSTKa12 HSTKb12.
    (* [comment removed for export] *)
    apply (PQHA9.stage9m L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A fx12 R12 M12 model12 K LK12 cr9 A12 s s' sm9 g3
             BI12 RI12 HK LS12 V18 V20 V21 V22 V23 V24 V25 V26 HB12 HSTKa12 HSTKb12).
    intros fx13 R13 M13 model13 LK13 A13 BI13 RI13 LS13 J18 J20 J21 J22 J23 J24 J25 J26 HB13 HSTKa13 HSTKb13.
    apply (PQHA9.stage9a L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A TP STKSH wapp_WF IL ICok ILY OPD fx13 R13 M13 model13 K LK13 cr9 A13 s s' sm9 g3
             BI13 RI13 HK LS13 J18 J20 J21 J22 J23 J24 J25 J26 HB13 HSTKa13 HSTKb13).
    intros fx14 R14 M14 model14 LK14 A14 BI14 RI14 LS14 I1 I10 I18 I20 I21 I22 I23 I24 I25 I26 HF14 HSTKa14 HSTKb14.
    (* [comment removed for export] *)
    apply (PQHA10.stage10 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF LCD IOD OPD fx14 R14 M14 model14 K LK14 cr9 A14
             s (PM.sm_st sm9) g3 BI14 RI14 HK LS14 I1 I10 I18 I20 I21 I22 I23 I24 I25 I26 HF14 HSTKa14 HSTKb14).
    intros fx15 R15 M15 model15 LK15 A15 BI15 RI15 LS15 N18 N20 N21 N22 N23 N24 N25 N26 HSTKb15.
    (* [comment removed for export] *)
    apply (PQHA11.harness_tail L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A TP RAok G2R SF
             fx15 R15 M15 model15 [] LK15 cr9 A15 K g3 BI15 RI15 HK LS15 N18 N20 N21 N22 N23 N24 N25 N26 HSTKb15).
    intros fxf Rf Mf modelf RPf A0f LSf AHf RTf AMf HHf.
    pose proof BI15 as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5 & BQ6 & BQ7 & BQ8 & BQ9 & BQ10).
    cbn [app] in HHf.
    rewrite UR1.
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHf) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDf & _).
    apply (KONT fxf g3 Rf Mf modelf cr9 LK15 A15).
    + constructor.
      * rewrite L5K.rl10. exact A0f.
      * exact RPf.
      * cbn [lla_credit LayA PNTAL.TopLayA_a]. fold n. exact (crF n cr cr4 cr5 cr6 cr9 qc b b' NR CK2 CK3 CK4 CK7).
      * intros a Ha Hc NF NJ. apply (proj1 AHf). split; [exact Ha|]. split; [rewrite <- SE; exact Hc|].
        intros rr Hr Hin. unfold WF in Hr. apply in_app_or in Hr. destruct Hr as [Hr|[<-|[]]].
        -- apply NF. apply in_map_iff in Hr. destruct Hr as (iv & <- & Hiv). exists iv. split; [exact Hiv|]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
        -- apply NJ. exists (0x693a5c, 0x693a60). split; [cbn [lla_junk LayA PNTAL.TopLayA_a]; left; reflexivity|]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. cbn [fst snd]. lia.   (* [comment removed for export] *)
      * cbn [lla_stack LayA PNTAL.TopLayA_a]. rewrite SE. exact (proj1 (proj2 AHf)).
      * intros a Ha Hc. rewrite SE in Hc. exact (proj2 (proj2 AHf) a Ha Hc).
      * cbn [lla_stack LayA PNTAL.TopLayA_a] in *. intros j Hj. unfold byte_at. rewrite (proj1 AHf); [exact (pstksh j Hj)|].
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        assert (AR : HeapIfaceA.S (ahl_ceil ar) <= HeapIfaceA.S (sp - STK) + j <= HeapIfaceA.S (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1)
                     /\ 2147450880 <= HeapIfaceA.S (sp - STK) + j < 2 ^ 64).
        { unfold HeapIfaceA.S, HeapIfaceA.SB, STK in *. clear - Hj SLO SHI SPT TOP47. lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        split; [clear - AR; lia|]. split; [rewrite <- SE; right; right; right; right; left; exact (proj1 AR)|].
        intros rr Hr X. rewrite WF_eq in Hr. cbn in Hr. unfold L5.in_rng in X. destruct AR as [_ AR].
        repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in X; clear - X AR; lia|]). destruct Hr.
      * exact LSf.
    + exact RTf.
    + exact BQ4.
    + exact (proj1 AMf).
    + exact (proj2 AMf).
    + intros k Hk. cbn [lla_leak LayA PNTAL.TopLayA_a]. unfold LEAK.
      pose proof (ffc_incl k LK15 LK (nodup_lk FF LK15 NDf) BQ5) as X. lia.
    + split; [exact HHf|]. split.
      * apply (sj_keep L ar LB FF LK15 M Mf).
        -- pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHf) as (WBf & WFf & W3 & _ & _ & _ & _ & _ & (_ & _ & WW9 & WW10) & _).
           split; [|split; [|split; [exact W3|exact (conj WW9 WW10)]]].
           ++ intros bb0 Hb. destruct (WBf bb0 Hb) as (Q1' & _ & _ & _ & _ & Q6 & _). exact (conj Q1' Q6).
           ++ intros f Hf. destruct (WFf f Hf) as (Q1' & Q2' & Q3' & Q4' & _). exact (conj Q1' (conj Q2' (conj Q3' Q4'))).
        -- intros bb0 a Hb Ha. destruct (WB bb0 Hb) as ((Y0 & _ & _ & Y4 & _ & Y6) & _). unfold app_mem in Y6.
           assert (SR : BIGSHADOW_LO <= a < BIGSHADOW_HI).
           { unfold in_shadow_of in Ha. pose proof (PMKA.S_in_shadow (fst bb0) ltac:(lia)) as SS1. pose proof (PMKA.S_in_shadow (fst bb0 + snd bb0 - 1) ltac:(lia)) as SS2. lia. }
           apply (proj1 AHf). split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SR; lia|]. split.
           ++ rewrite <- SE. do 6 right. exists bb0. split; [exact Hb| exact Ha].
           ++ intros rr Hr X. rewrite WF_eq in Hr. cbn in Hr. unfold L5.in_rng in X. unfold BIGSHADOW_LO, BIGSHADOW_HI in SR.
              repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in X; clear - X SR; lia|]). destruct Hr.
        -- exact SBLK.
      * rewrite Forall_forall in *. intros f Hf. apply CLS13. apply in_app_or in Hf. apply in_or_app. destruct Hf as [Hf|Hf]; [left; exact Hf| right; apply BQ5; exact Hf].
Qed.
End TOP.

(* [comment removed for export] *)
Theorem harness_call_ok (RES : credit) : 0 <= fst RES -> 0 <= snd RES -> PQHAS.harness_call_stmt RES.
Proof.
  intros R1 R2 L C IL ar HI LY ILY IOK DEPS.
  destruct IOK as (HIok & ICok & EXT & _).
  exact (harness_call_okA L ar C HI IL RES LY HIok ICok ILY EXT (conj R1 R2) DEPS).
Qed.
End SCFG_1.
End PQHA.
