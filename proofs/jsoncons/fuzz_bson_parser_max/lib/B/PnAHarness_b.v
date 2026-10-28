(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface LibIfaceA
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b L5AFrameKR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx LibIfaceAB PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnSpecsAX_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnTopS. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnTopAL_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import StrictOfB. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAHarnessStmts_b PnAHarnessKit_b PnAHarnessKit2_b PnAHarnessSK_b PnAHarnessKit3_b
     PnAHarness1_b PnAHarness2_b PnAHarness3_b PnAHarness4_b PnAHarness5_b PnAHarness6_b PnAHarness7_b PnAHarness8_b PnAHarness8b_b PnAHarness8c_b PnAHarness9_b PnAHarness10_b PnAHarness11_b PnAResetBStmts_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PNHA.
Import L5A. Import L5CA. Import L5SAR. Import PNHAS.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.

(* [comment removed for export] *)
Definition LayA (L : asan_layout) : lib_layoutA := PNTAL.TopLayA_a STK FRAMES LEAK CREDIT L.
Definition WF : list L5.range := map (fun iv => (fst iv, snd iv - fst iv)) PNTAL.foot_a.
Lemma WF_eq : WF = [(0x6722c0, 2); (0x672530, 2); (0x672532, 1854); (0x673398, 88); (0x693d50, 544); (0x6722e0, 8); (0x6722c8, 24); (0x672300, 8); (0x6722e8, 24)].
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

Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Definition harness_depsA (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  PMA.str_ctor_spec L ar HI /\ PMA.iss_ctor_spec L ar HI /\ PNRAa.reader_ctor_spec L ar HI /\ PMA.syscat_spec L ar HI /\ PNARBS.reset_spec L ar HI
  /\ PNRAa.parse_spec L ar HI /\ PNSAX.vec_dtor_spec RSEGS PMA.AD L ar HI 0xab620 /\ PNSAX.vu8_dtor_spec RSEGS PMA.AD L ar HI 0xab9e0 /\ PMA.opdel_spec L ar HI
  /\ PMA.src_dtor_spec L ar HI /\ PMA.locale_dtor_spec L ar HI /\ PMA.ios_dtor_spec L ar HI /\ HAJ.astack_free_spec L ar SCFG HI 0x5e2e8 16 5.

Section TOP.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HIR : asan_iface) (IL : icpt_layout).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HIR.
Hypothesis ICok : aicpt_ok L ar IL SCFG HIR.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Hypothesis DEPS : harness_depsA L ar HIR.

(* [comment removed for export] *)
Lemma wapp_WF : PMKA.wapp WF.
Proof. intros r Hr. rewrite WF_eq in Hr. cbn in Hr. unfold BIGSHADOW_LO, BIGSHADOW_HI. repeat (destruct Hr as [<-|Hr]; [cbn; lia|]). destruct Hr. Qed.
Lemma wloc_WF : forall a, L5.outside WF a -> L5.outside (PMSPA.loc_W PMA.AD) a.
Proof.
  intros a Ho r Hr. apply Ho. unfold PMSPA.loc_W in Hr. cbn in Hr. rewrite WF_eq. cbn.
  destruct Hr as [<-|[<-|[]]]; [right; right; left; reflexivity| right; right; right; left; reflexivity].
Qed.
Lemma wsys_WF : forall a, L5.outside WF a -> L5.outside [(0x672530, 2)] a.
Proof. intros a Ho r [<-|[]]. apply Ho. rewrite WF_eq. cbn. right; left; reflexivity. Qed.
Lemma werr_WF : forall a, L5.outside WF a -> L5.outside (PNST.berr_W PMA.AD PMA.AN) a.
Proof.
  intros a Ho r Hr. apply Ho. unfold PNST.berr_W, PNST.cat_W, PNST.dec_W in Hr. cbn in Hr. rewrite WF_eq. cbn.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
    [left; reflexivity| do 4 right; left; reflexivity| do 5 right; left; reflexivity| do 7 right; left; reflexivity
    | do 6 right; left; reflexivity| do 8 right; left; reflexivity| do 4 right; left; reflexivity].
Qed.

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
Section Credit.
Variables (n : Z) (cr cr4 cr5 cr6 cr9 : credit) (qc b : Z).
Hypothesis NR : 0 <= n < 2 ^ 26.
Hypothesis C0 : credit_le (CREDIT n) cr.
Let HV := PMSPA.HV L ar.
Lemma cr_facts : hl_k_per_malloc L = 8 /\ hl_b_lin L = 3 /\ hl_b_overhead L = 2 ^ 21.
Proof. exact (PMA.ly_cost L C LY). Qed.
Ltac crt := pose proof cr_facts as (KP & BL & BO);
  unfold PMSPA.credit_le, PMSPA.credit_keep, PMSPA.scA, PMSPA.cr0, credit_le, credit_sub, CREDIT, PNTS.TOPK, PNTS.TOPB, PNRA.pot_bparser, PNRA.pot_bstack, PNRA.bpst_reset, PNRA.bparser_init,
         PM.credit_add, PM.cost1, PM.pot_text, PGV8.pot_v8, PGV8.v8_clear, PNRA.vs_clear, PM.vs_cap, PGV8.v8_cap, PM.CHUNK, PNM.BSZ in *;
  cbn [fst snd PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg PNM.b_src] in *; subst HV; cbn [HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead LibIfaceAB.heap_view PMSPA.HV] in *;
  rewrite ?KP, ?BL, ?BO in *;
  change (2 ^ 12) with 4096 in *; change (2 ^ (0 + 1)) with 2 in *; change (2 ^ 28) with 268435456 in *; change (2 ^ 30) with 1073741824 in *;
  change (2 ^ 29) with 536870912 in *; change (2 ^ 21) with 2097152 in *; change (2 ^ 26) with 67108864 in *; lia.
Lemma cr2 : PMSPA.credit_le (PMSPA.scA L (PM.cost1 HV (n + 16))) cr.
Proof. crt. Qed.
Hypothesis K2 : PMSPA.credit_keep cr cr4 (PMSPA.scA L (PM.cost1 HV (n + 16))) PMSPA.cr0.
Lemma cr3 : PMSPA.credit_le (PMSPA.scA L (PM.cost1 HV (n + 32))) cr4.
Proof. crt. Qed.
Hypothesis K3 : PMSPA.credit_keep cr4 cr5 (PMSPA.scA L (PM.cost1 HV (n + 32))) PMSPA.cr0.
Lemma cr4' : PMSPA.credit_le (PMSPA.scA L (PM.credit_add (PM.cost1 HV PM.CHUNK) (PM.cost1 HV PNM.BSZ))) cr5.
Proof. crt. Qed.
Hypothesis K4 : PMSPA.credit_keep cr5 cr6 (PMSPA.scA L (PM.credit_add (PM.cost1 HV PM.CHUNK) (PM.cost1 HV PNM.BSZ))) PMSPA.cr0.
Lemma cr7 : PMSPA.credit_le (PMSPA.scA L (PNRA.pot_bparser L ar (PNRA.bpst_reset (PNRA.bparser_init qc b)))) cr6.
Proof. crt. Qed.
Hypothesis K7 : PMSPA.credit_keep cr6 cr9 (PMSPA.scA L (PNRA.pot_bparser L ar (PNRA.bpst_reset (PNRA.bparser_init qc b)))) PMSPA.cr0.
Lemma crF : credit_le (credit_sub cr (CREDIT n)) cr9.
Proof. crt. Qed.
End Credit.

Local Notation LSt := (PNSTA.TopLSA RSEGS PMA.AD PMA.AAD PMA.AN).

Theorem harness_call_okA : lib_call_okA (LayA L) ar SCFG (HAJ.strict_of HIR) LSt.
Proof.
  destruct DEPS as (STR & ISS & RDC & SYS & RST & PARSE & VDT & V8D & OPD & SRCD & LCD & IOD & SF).
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
  change (mkCfg (@mkst fx R (Z_to_bv 64 0xa7fa4) M (seg_rom RSEGS)) model) with (@L5A.cfg fx R 0xa7fa4 M model).
  assert (FF5 : ff_room 5 FF LK).
  { unfold ff_room. pose proof (pffroom 5 ltac:(cbn; tauto)) as X. unfold FRAMES in X. lia. }
  apply (PNHA1.entry L ar C HIR LY HIok WF fx R M model K LB FF LK cr A ptr n sp ra g HH (conj HALT MI) HK).
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
  - intros V2 cls F fl LK2 M2 model2 fx3 R3 M3 model3 G SE CLS V2A V2R V2S BI3 RI3 Q1 Q10 Q11 Q12 Q21 Q22 Q23 SZS FAL LS3.
    assert (GP : getr R (reg 3) = Z_to_bv 64 (pa_gp PMA.AD)) by (rewrite <- L5K.rl3; exact pgp).
    assert (TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite <- L5K.rl4; exact ptp).
    assert (FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f) by (intros f Hf; rewrite <- SE; exact (pffrs f Hf)).
    assert (ROOM : forall LKc, incl LKc LK -> base.NoDup (map ff_addr ((F, 5, V2 - 128 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, V2 - 128 + 32) :: FF) LKc)
      by exact (room_of FF LK F (V2 - 128 + 32) (fun k Hk => pffroom k Hk)).
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
    apply (PNHA2.stage2 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF STR fx3 R3 M3 model3 K ptr n g BI3 RI3 HK LS3 Q1 Q10 Q11 Q12 Q21 Q22 Q23 SZS NR DRG SRCB ACCd (cr2 n cr NR pcredit)).
    intros fx4 R4 M4 model4 LK4 cr4 A4 s BI4 RI4 S1 S10 S11 S12 S21 S22 S23 VSTR SIZE SSH SLG CK2 SZ4 LS4.
    assert (LONG : forall c n0 p, s = PM.VLong c n0 p -> 23 <= n0).
    { intros c n0 p E. destruct (Z_le_gt_dec n 22) as [X|X]; [rewrite (SSH X) in E; discriminate|]. rewrite E in SIZE. cbn in SIZE. lia. }
    apply (PNHA3.stage3 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF wloc_WF ISS fx4 R4 M4 model4 K LK4 cr4 A4 s ptr n g BI4 RI4 HK LS4 S1 S10 S11 S12 S21 S22 S23 VSTR SIZE LONG NR DRG
             (cr3 n cr cr4 NR pcredit CK2) SZ4).
    intros fx5 R5 M5 model5 LK5 cr5 A5 s' sm BI5 RI5 LS5 P1 P10 P11 P12 P13 P21 P22 P23 P26 VS5 IS5 SIZE5 SMG SMST CK3 V432 O960 O968 O976 O980 SZV SZP SZO SZI.
    set (g1 := PNST.ST true (PNST.st_sys g) (PNST.st_ax g)) in *.
    apply (PNHA4.stage4 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF FAL RDC fx5 R5 M5 model5 K LK5 cr5 A5 s s' sm ptr g1 BI5 RI5 HK eq_refl LS5
             P1 P10 P11 P12 P13 P21 P22 P23 P26 DRG VS5 IS5 (cr4' n cr cr4 cr5 NR pcredit CK2 CK3) V432 O960 O976 SZV SZP SZO SZI).
    intros fx6 R6 M6 model6 LK6 cr6 A6 qc b BI6 RI6 LS6 T1 T21 T22 T23 T26 VS6 IS6 PA6 CK4 V432' SZV' REF6 ACC6 EC6 SZE6 SZI6.
    apply (PNHA5.stage5 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF wsys_WF SYS fx6 R6 M6 model6 K LK6 cr6 A6 s s' sm (PNRA.bparser_init qc b) g1 BI6 RI6 HK LS6 T1 T21 T22 T23 T26
             (conj VS6 (conj IS6 (conj V432' (conj SZV' SZI6)))) (conj PA6 (conj REF6 ACC6)) EC6 SZE6).
    intros fx7 R7 M7 model7 LK7 A7 BI7 RI7 LS7 U1 U10 U21 U22 U23 U26 HB7 HQ7 HE7.
    set (g2 := PNST.ST (PNST.st_loc g1) true (PNST.st_ax g1)) in *.
    apply (PNHA6.stage6 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF FAL RST fx7 R7 M7 model7 K LK7 cr6 A7 s s' sm (PNRA.bparser_init qc b) g2 0 (pa_syscat_obj PMA.AD) BI7 RI7 HK LS7
             U1 U10 U21 U22 U23 U26 HB7 HQ7 HE7).
    intros fx8 R8 M8 model8 LK8 A8 BI8 RI8 LS8 W1 W10 W11 W12 W21 W22 W23 W26 HB8 HQ8 HE8.
    rewrite PNHAK3.reset_initA in HQ8.
    assert (INV : PNRA.binv (PNRA.bparser_init qc b)).
    { unfold PNRA.binv, PNRA.bparser_init. cbn [PNM.b_done PNM.b_stk]. split; [reflexivity|].
      unfold PNRA.bstack_shape. cbn [length nth]. split; [lia|]. split; [unfold PNM.MAX_DEPTH; lia|]. split; [unfold PNRA.bmode_bottom; cbn; left; reflexivity|].
      split; [intros i Hi; lia|]. intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [nth]. unfold PNM.bstate_ok, PNM.bs_root. cbn. lia. }
    assert (GROW : PNM.bgrow_ok (PNRA.bparser_init qc b)).
    { unfold PNM.bgrow_ok, PNRA.bparser_init. cbn [PNM.b_nb PNM.b_ng PNM.b_tb PNM.b_tg PNM.b_bb PNM.b_bg]. unfold PM.tb_ok, PGV8.v8_ok. cbn. repeat split; lia. }
    assert (UNR : PM.unread (PNM.b_src (PNRA.bparser_init qc b)) sm < 2 ^ 26).
    { pose proof HB8 as (_ & ISX & _). destruct ISX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IE1 & IE2).
      unfold PM.unread, PNRA.bparser_init. cbn [PNM.b_src PM.sr_rem]. rewrite IE1, SMG. rewrite SIZE5. lia. }
    assert (BBR : PNRA.bb_room (PNRA.bparser_init qc b) sm).
    { unfold PNRA.bb_room, PNRA.bparser_init. cbn [PNM.b_bb PNM.b_src]. unfold PGV8.v8_room. cbn. exact I. }
    apply (PNHA7.stage7 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF FAL werr_WF PARSE fx8 R8 M8 model8 K LK8 cr6 A8 s s' sm (PNRA.bparser_init qc b) g2 (pa_syscat_obj PMA.AD)
             BI8 RI8 HK LS8 W1 W10 W11 W12 W21 W22 W23 W26 HB8 HQ8 HE8 INV UNR GROW BBR).
    { rewrite <- (PNHAK3.reset_initA qc b). exact (cr7 n cr cr4 cr5 cr6 qc b NR pcredit CK2 CK3 CK4). }
    intros fx9 R9 M9 model9 LK9 cr9 A9 ps' sm' ax' BI9 RI9 LS9 AXLE X1 X10 X21 X22 X23 X26 HB9 HS9 TB9 NB9 BB9 HV9 FT9 VP9 CK7.
    set (g3 := PNST.ST (PNST.st_loc g2) (PNST.st_sys g2) ax') in *.
    assert (EQL : PNM.bparser_own ps' ++ PM.vs_own s' ++ PM.vs_own s
                  = (PM.sr_qc (PNM.b_src ps'), PM.CHUNK) :: (PNM.b_sb ps', 40 * 2 ^ PNM.b_sk ps') :: PGV8.v8_own (PNM.b_bb ps') ++ PM.vs_own (PNM.b_nb ps') ++ PM.vs_own (PNM.b_tb ps') ++ PM.vs_own s' ++ PM.vs_own s).
    { unfold PNM.bparser_own, PNM.brest_own, PM.src_own, PNM.bvec_own, PNM.BSZ. cbn [app]. rewrite <- ?app_assoc. reflexivity. }
    rewrite EQL in BI9.
    apply (PNHA8.stage8 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF VDT OPD fx9 R9 M9 model9 K LK9 cr9 A9
             s s' (PNM.b_tb ps') (PNM.b_nb ps') (PNM.b_bb ps') sm' (PNM.b_src ps') (PNM.b_sb ps') (PNM.b_sk ps') (PNM.b_stk ps') g3
             BI9 RI9 HK LS9 X1 X10 X21 X22 X23 X26 HB9 HS9 TB9 NB9 BB9 HV9 FT9).
    intros fx10 R10 M10 model10 LK10 A10 BI10 RI10 LS10 Y21 Y22 Y23 Y26 HB10 HS10 NB10 BB10.
    apply (PNHA8b.stage8b L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A TP STKSH wapp_WF OPD fx10 R10 M10 model10 K LK10 cr9 A10
             s s' (PNM.b_nb ps') (PNM.b_bb ps') sm' (PNM.b_src ps') g3 BI10 RI10 HK LS10 Y21 Y22 Y23 Y26 HB10 HS10 NB10 BB10).
    intros fx11 R11 M11 model11 LK11 A11 BI11 RI11 LS11 Z1 Z10 Z21 Z22 Z23 Z26 HB11 HS11 BB11 FT11.
    apply (PNHA8c.stage8c L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF V8D fx11 R11 M11 model11 K LK11 cr9 A11
             s s' (PNM.b_bb ps') sm' (PNM.b_src ps') g3 BI11 RI11 HK LS11 Z1 Z10 Z21 Z22 Z23 Z26 HB11 HS11 BB11 FT11).
    intros fx12 R12 M12 model12 LK12 A12 BI12 RI12 LS12 Y1' Y10' Y21' Y22' Y23' Y26' HB12 HS12.
    apply (PNHA9.stage9 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF IL ICok ILY SRCD OPD fx12 R12 M12 model12 K LK12 cr9 A12
             s s' sm' (PNM.b_src ps') g3 BI12 RI12 HK LS12 Y1' Y10' Y21' Y22' Y23' Y26' HB12 HS12).
    intros fx13 R13 M13 model13 LK13 A13 BI13 RI13 LS13 Z1' Z10' Z21' Z22' Z23' Z26' HF13.
    apply (PNHA10.stage10 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF LCD IOD OPD fx13 R13 M13 model13 K LK13 cr9 A13
             s (PM.sm_st sm') g3 BI13 RI13 HK LS13 Z1' Z10' Z21' Z22' Z23' Z26' HF13).
    intros fx14 R14 M14 model14 LK14 A14 BI14 RI14 LS14 V21 V22 V23 V26.
    apply (PNHA11.harness_tail L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A TP RAok G2R SF
             fx14 R14 M14 model14 [] LK14 cr9 A14 K g3 BI14 RI14 HK LS14 V21 V22 V23 V26).
    intros fxf Rf Mf modelf RPf A0f LSf AHf RTf AMf HHf.
    pose proof BI14 as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5 & BQ6 & BQ7 & BQ8 & BQ9 & BQ10).
    cbn [app] in HHf.
    rewrite UR1.
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHf) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDf & _).
    apply (KONT fxf g3 Rf Mf modelf cr9 LK14 A14).
    + constructor.
      * rewrite L5K.rl10. exact A0f.
      * exact RPf.
      * cbn [lla_credit LayA PNTAL.TopLayA_a]. fold n. exact (crF n cr cr4 cr5 cr6 cr9 qc b NR CK2 CK3 CK4 CK7).
      * intros a Ha Hc NF NJ. apply (proj1 AHf). split; [exact Ha|]. split; [rewrite <- SE; exact Hc|].
        intros rr Hr Hin. apply NF. unfold WF in Hr. apply in_map_iff in Hr. destruct Hr as (iv & <- & Hiv).
        exists iv. split; [exact Hiv|]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
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
      pose proof (ffc_incl k LK14 LK (nodup_lk FF LK14 NDf) BQ5) as X. lia.
    + split; [exact HHf|]. split.
      * apply (sj_keep L ar LB FF LK14 M Mf).
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
End SCFG_1.
End PNHA.
