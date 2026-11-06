(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface LibIfaceA AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9 L5CoreBRB0S9 L5ADetailHRB0S9 L5AFrameKRB0S9 HeapIfaceAEx LibIfaceAB LibIfaceAE.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA PnLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmModelFactsA PmStatics PmStaticsA PnStatics PnStaticsA PmSpecs PmSpecsA PeSpecsAb PeStepAB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCStaticsA PeCSink PeCSinkA PeCModel PeCModelA PeCFrameA PeCSpecs PeCSpecsA PeCSpecsAb PeCRdReadSpecZ PeCDtorSpecsA PeTopAL PeCTopB StrictOfB PeBCHarnessStmts PeBCHarnessKit PeBCHarnessKit2 PeBCHarnessKit4 PeBCHarnessSK PeBCHarnessKit3 PeBCHarnessKit5 PeBCHarness1 PeBCHarness2 PeBCHarness3 PeBCHarness3b PeBCHarness4 PeBCHarness5 PeBCHarness7 PeBCHarness8 PeBCHarness9 PeBCHarness10 PeBCHarness10b PeBCHarness11.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PEBCHN.
Import L5A. Import L5CA. Import L5SAR. Import PEBCH.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.

Lemma ffc_incl k (l l' : list fframe) : base.NoDup l -> incl l l' -> (ff_count k l <= ff_count k l')%nat.
Proof.
  intros ND HI. unfold ff_count. apply list_relations.list.submseteq_length. apply list_relations.list.NoDup_submseteq. apply list_relations.list.NoDup_filter. exact ND.
  intros x Hx. apply list_basics.list.list_elem_of_filter in Hx. apply list_basics.list.list_elem_of_filter. destruct Hx as [P Hx]. split. exact P.
  apply base.list_elem_of_In. apply HI. apply base.list_elem_of_In. exact Hx.
Qed.
Lemma nodup_lk (FF LK : list fframe) : base.NoDup (map ff_addr (FF ++ LK)) -> base.NoDup LK.
Proof. intros ND. apply base.NoDup_ListNoDup. apply base.NoDup_ListNoDup in ND. apply NoDup_map_inv in ND. apply NoDup_app_remove_l in ND. exact ND. Qed.

Lemma bytes_ok_p (payload : list byte) : bytes_ok (p payload).
Proof.
  unfold bytes_ok, p. induction payload as [|b l IH]; cbn; constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. lia.
Qed.

Lemma wloc_WF : forall a, L5.outside WF a -> L5.outside (PMSPA.loc_W AD) a.
Proof.
  intros a Ho r Hr. apply Ho. unfold PMSPA.loc_W in Hr. cbn in Hr. rewrite WF_eq. cbn.
  destruct Hr as [<-|[<-|[]]]; [right; right; left; reflexivity| right; right; right; left; reflexivity].
Qed.
Lemma wsys_WF : forall a, L5.outside WF a -> L5.outside [(0x6789b0, 2)] a.
Proof. intros a Ho r [<-|[]]. apply Ho. rewrite WF_eq. cbn. right; left; reflexivity. Qed.
Lemma werr_WF : forall a, L5.outside WF a -> L5.outside (PMSPA.err_W AD) a.
Proof.
  intros a Ho r Hr. apply Ho. unfold PMSPA.err_W in Hr. cbn in Hr. rewrite WF_eq. cbn.
  destruct Hr as [<-|[<-|[]]]; [left; reflexivity| do 4 right; left; reflexivity].
Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.

Section TOP.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMB.EXT.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Hypothesis PMODE : PESKA.spa_mode P.
Let LYa := PMB.ly_as0 L C LY.

Hypothesis STR : PECSB.str_ctor_c_spec L ar HI.
Hypothesis ISS : PECSB.iss_ctor_c_spec L ar HI.
Hypothesis RDC : PECSB.reader_ctor_spec L ar HI.
Hypothesis SYS : PMSPA.syscat_spec RSEGS AD L ar HI.
Hypothesis READ : PECRRZ.reader_read_specZ RSEGS AD AAD EE L ar HI P.
Hypothesis VEC : PMSPA.vec_dtor_spec RSEGS AD L ar HI.
Hypothesis OPD : PMSPA.opdel_spec RSEGS AD L ar HI.
Hypothesis SRC : PMSPA.src_dtor_spec RSEGS AD L ar HI.
Hypothesis LCD : PMSPA.locale_dtor_spec RSEGS AD L ar HI.
Hypothesis IOD : PMSPA.ios_dtor_spec RSEGS AD L ar HI.
Hypothesis ESTK : PECDTA.estk_dtor_spec RSEGS AD EE L ar HI 0xb4794.
Hypothesis SNK : PECDTA.sink_dtor_spec RSEGS AD L ar HI P 0xaafe4.

Definition tk : Z := 1024 + fst (PESKA.spa_pot P 0).
Definition tb : Z := 2 ^ 32 + snd (PESKA.spa_pot P 0).
Local Notation LayA := (PECTB.LayA tk tb L).
Local Notation LSt := PECTB.TopLSA.

Lemma room_of (FF LK : list fframe) F rs :
  (forall k, In k [0; 1; 2; 3; 4; 5] -> Z.of_nat (ff_count k (FF ++ LK)) + PECTB.FRAMES k <= ff_cap k) ->
  forall LKc, incl LKc LK -> base.NoDup (map ff_addr ((F, 5, rs) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, rs) :: FF) LKc.
Proof.
  intros RM LKc INC ND k Hk. cbn [app].
  assert (ND' : base.NoDup (FF ++ LKc)).
  { apply base.NoDup_ListNoDup. apply base.NoDup_ListNoDup in ND. apply NoDup_map_inv in ND. inversion ND; assumption. }
  assert (INC' : incl (FF ++ LKc) (FF ++ LK)) by (intros x Hx; apply in_app_or in Hx; apply in_or_app; destruct Hx as [Hx|Hx]; [left; exact Hx| right; apply INC; exact Hx]).
  assert (HD : ff_count k (((F, 5, rs) : fframe) :: FF ++ LKc) = ((if Z.eqb 5 k then 1 else 0) + ff_count k (FF ++ LKc))%nat).
  { unfold ff_count. rewrite list_basics.list.filter_cons. cbn [ff_class fst snd]. destruct (base.decide _) as [X|X]; destruct (Z.eqb 5 k) eqn:E; cbn [length]; try reflexivity; exfalso; first [exact X | exact (X I)]. }
  assert (Hk' : In k [0; 1; 2; 3; 4; 5]) by (cbn in Hk |- *; tauto).
  rewrite HD. pose proof (ffc_incl k _ _ ND' INC') as LE. pose proof (RM k Hk') as X. unfold PECTB.FRAMES in X.
  destruct (Z.eqb 5 k) eqn:E; cbn [Nat.add]; rewrite ?Nat2Z.inj_succ; lia.
Qed.

Lemma stksh_of (M : word -> option byte) sp : sp <= ar_sptop ar ->
  shadow_zero M (sp - STK) ((Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - STK)) / 8) -> shadow_zero M (sp - STK) 4608.
Proof.
  intros H SZ j Hj. apply SZ. split; [lia|]. unfold STK, PECTB.STK in *.
  assert (4608 <= (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 36864)) / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Section Credit.
Variables (n : Z) (cr cr4 cr5 cr6 cr9 : credit) (qc b ck : Z).
Hypothesis NR : 0 <= n < 2 ^ 26.
Hypothesis C0 : credit_le (tk, tb) cr.
Let HV := PMSPA.HV L ar.
Lemma cr_facts : hl_k_per_malloc L = 8 /\ hl_b_lin L = 3 /\ hl_b_overhead L = 2 ^ 21.
Proof. exact (PMB.ly_cost L C LY). Qed.
Lemma pot0_nonneg : 0 <= fst (PESKA.spa_pot P 0) /\ 0 <= snd (PESKA.spa_pot P 0).
Proof. apply (PESKA.spao_pot_nonneg L P PO 0); [left; reflexivity| pose proof (PESKA.spao_nmax_pos L P PO); lia]. Qed.
Ltac crt := pose proof cr_facts as (KP & BL & BO); pose proof pot0_nonneg as (PK0 & PB0);
  unfold PECA.pot_allA, PEC.credit_add, PEC.pot_estack, PEC.ESZ, PM.pot_parser, PM.pot_stack, PM.pot_text, PM.vs_cap, PM.credit_add, PM.cost1, PM.CHUNK, PMSPA.pst_reset, PMSPA.parser_init in *;
  unfold PMSPA.credit_le, PMSPA.credit_keep, PMSPA.scA, PMSPA.cr0, PmSpecs.PMSP.credit_le, PmSpecs.PMSP.credit_keep, PmSpecs.PMSP.cr0, credit_le, credit_sub, tk, tb in *;
  cbn [fst snd PM.p_k PM.p_tb PM.p_tg PM.p_src PM.p_b PEC.en_k PEC.enc0 PESK.sk_c PESK.sink0] in *; subst HV; cbn [HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead LibIfaceAB.heap_view PMSPA.HV] in *;
  rewrite ?KP, ?BL, ?BO in *;
  change (2 ^ 12) with 4096 in *; change (2 ^ (0 + 1)) with 2 in *; change (2 ^ 0) with 1 in *; change (2 ^ 28) with 268435456 in *; change (2 ^ 30) with 1073741824 in *;
  change (2 ^ 29) with 536870912 in *; change (2 ^ 27) with 134217728 in *; change (2 ^ 21) with 2097152 in *; change (2 ^ 26) with 67108864 in *; change (2 ^ 20) with 1048576 in *;
  change (2 ^ 32) with 4294967296 in *; lia.
Lemma cr2 : PMSPA.credit_le (PMSPA.scA L (PM.cost1 HV (n + 16))) cr.
Proof. crt. Qed.
Hypothesis K2 : PMSPA.credit_keep cr cr4 (PMSPA.scA L (PM.cost1 HV (n + 16))) PMSPA.cr0.
Lemma cr3 : PMSPA.credit_le (PMSPA.scA L (PM.cost1 HV (n + 32))) cr4.
Proof. crt. Qed.
Hypothesis K3 : PMSPA.credit_keep cr4 cr5 (PMSPA.scA L (PM.cost1 HV (n + 32))) PMSPA.cr0.
Lemma cr4' : PMSPA.credit_le (PMSPA.scA L (PM.credit_add (PM.cost1 HV PM.CHUNK) (PM.cost1 HV 32))) cr5.
Proof. crt. Qed.
Hypothesis K4 : PMSPA.credit_keep cr5 cr6 (PMSPA.scA L (PM.credit_add (PM.cost1 HV PM.CHUNK) (PM.cost1 HV 32))) PMSPA.cr0.
Lemma cr7 : PMSPA.credit_le (PECA.pot_allA L ar P (PMSPA.pst_reset (PMSPA.parser_init qc b)) PEC.enc0 PESK.sink0) cr6.
Proof. crt. Qed.
Hypothesis CKN : 0 <= fst (PESKA.spa_pot P ck) /\ 0 <= snd (PESKA.spa_pot P ck).
Hypothesis K7 : PMSPA.credit_keep cr6 cr9 (PECA.pot_allA L ar P (PMSPA.pst_reset (PMSPA.parser_init qc b)) PEC.enc0 PESK.sink0) (PESKA.spa_pot P ck).
Lemma crF : credit_le (credit_sub cr (tk, tb)) cr9.
Proof. pose proof CKN as (PK1 & PB1). crt. Qed.
End Credit.

Theorem harness_call_okA : forall (PayOk PayExport : list byte -> Prop),
  PECSB.pay_in P PayOk -> PECSB.pay_out P PayExport ->
  lib_call_okA_x LayA ar SCFG (HAJ.strict_of HI) LSt PayOk PayExport.
Proof.
  intros PayOk PayExport PIN POUT.
  pose proof (HAJ.aex_stack_free _ _ _ _ _ EXT) as SF. cbn [HAJ.ec_sf_pc HAJ.ec_sf_scr PMB.EXT] in SF.
  unfold lib_call_okA_x. intros fx g LB FF LK cr A sp ptr ra payload R M model K PRE POK HHs HALT MI HK KONT.
  destruct PRE as [pra praok psp pgp ptp pa0 pa1 plen pptr ppay pstack pcredit pffroom pffrs pstksh pstat].
  cbn [lla_L lla_gp lla_empty lla_stack lla_frames lla_credit PECTB.LayA PECTB.STK PECTB.LEAK PECTB.CREDIT PNTAL.TopLayA_b] in *.
  destruct HHs as (HH & SBLK & CLS13).
  pose proof pstack as (A16 & SLO & SHI & SPT & DSCR & DUP).
  change (Z.of_nat (length payload)) with (n payload) in *.
  set (nn0 := n payload) in *.
  assert (NR : 0 <= nn0 < 2 ^ 26) by (subst nn0; unfold n in *; clear - plen; lia).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WFF & _ & _ & _ & _ & _ & _ & _ & TOP47 & NDB & NDF & _).
  assert (DRG : 0 <= ptr < 2 ^ 64).
  { destruct pptr as [(P0 & PE)|(P0 & INB)]; [rewrite PE; cbn; lia|].
    destruct (WB _ INB) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. clear - Q0 Q4 SPT SLO SHI NR. lia. }
  unfold lib_cfgA in KONT |- *. cbn [lla_L lla_entry PECTB.LayA PNTAL.TopLayA_b] in KONT |- *. rewrite (L5A.aly_segs L C LYa) in *.
  change (mkCfg (@mkst fx R (Z_to_bv 64 0xa9150) M (seg_rom RSEGS)) model) with (@L5A.cfg fx R 0xa9150 M model).
  assert (FF5 : ff_room 5 FF LK).
  { unfold ff_room. pose proof (pffroom 5 ltac:(cbn; tauto)) as X. unfold PECTB.FRAMES in X. lia. }

  assert (HB : forall k, PESKA.spa_hb P (s_hi (run k (p payload) UbjRef.init))).
  { intros k. unfold p. apply (PIN payload); [change (Z.of_nat (length payload)) with nn0; clear - NR; lia| exact POK]. }
  apply (PEBCH1.entry L ar C HI LY HIok WF fx R M model K LB FF LK cr A ptr nn0 sp ra g HH (conj HALT MI) HK).
  - exact pa0.
  - exact pa1.
  - exact NR.
  - exact DRG.
  - exact pra.
  - exact praok.
  - exact psp.
  - exact A16.
  - exact ptp.
  - exact pstack.
  - exact FF5.
  - exact pffrs.
  - exact pstat.
  - intros V2 cls F fl LK2 M2 model2 fx3 R3 M3 model3 G SE CLS V2A V2R V2S BI3 RI3 Q1 Q10 Q11 Q12 Q18 Q22 Q23 SZS FAL HSTK3 LS3.
    assert (GP : getr R (reg 3) = Z_to_bv 64 (pa_gp AD)) by (rewrite <- L5K.rl3; exact pgp).
    assert (TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite <- L5K.rl4; exact ptp).
    assert (FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f) by (intros f Hf; rewrite <- SE; exact (pffrs f Hf)).
    assert (ROOM : forall LKc, incl LKc LK -> base.NoDup (map ff_addr ((F, 5, V2 - 160 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, V2 - 160 + 32) :: FF) LKc)
      by exact (room_of FF LK F (V2 - 160 + 32) (fun k Hk => pffroom k Hk)).
    assert (STKSH : shadow_zero M (V2 + cls - 36864) 4608) by (rewrite <- SE; exact (stksh_of M sp SHI pstksh)).
    assert (UR1 : U R 1 = ra) by (apply U_of; [rewrite <- L5K.rl1; exact pra| destruct praok; lia]).
    assert (RAok : L5.ra_ok (U R 1)) by (rewrite UR1; exact praok).
    assert (G2R : getr R (reg 2) = Z_to_bv 64 (V2 + cls)) by (rewrite <- SE, <- L5K.rl2; exact psp).
    assert (SRCB : nn0 = 0 \/ (exists B m, In (B, m) LB /\ B <= ptr /\ ptr + nn0 <= B + m)).
    { destruct pptr as [(P0 & _)|(P0 & INB)]; [left; subst nn0; unfold n; rewrite P0; reflexivity| right; exists ptr, nn0; split; [exact INB| lia]]. }
    pose proof BI3 as (_ & _ & _ & _ & _ & _ & EK3 & _).
    assert (ACCd : aacc M3 ptr nn0).
    { destruct pptr as [(P0 & _)|(P0 & INB)]; [subst nn0; unfold n; rewrite P0; intros x Hx; cbn in Hx; lia|].
      destruct (WB _ INB) as ((B0 & _ & B3 & B4 & B5 & B6) & _). cbn [fst snd] in *. unfold app_mem in B6.
      rewrite Forall_forall in SBLK. pose proof (SBLK _ INB) as SB0. cbn [fst snd] in SB0.
      apply (PMFA.accA_agree M M3 ptr nn0); [| apply (L5CBR.aacc_of_blk M ptr nn0 ptr nn0 SB0); [apply PMKB.mod16_8'; exact B3| lia| lia| lia]].
      intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. apply EK3. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split.
      - do 6 right. exists (ptr, nn0). split; [exact INB|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKB.S_mono; lia.
      - intros rr Hr Hin. rewrite WF_eq in Hr. cbn in Hr. unfold L5.in_rng in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
        repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Hin; lia|]). destruct Hr. }

    assert (PAYB3 : L5.bytes_at RSEGS M3 ptr (p payload)).
    { destruct pptr as [(P0 & _)|(P0 & INB)].
      - intros i Hi. unfold p in Hi. rewrite length_map in Hi. rewrite P0 in Hi. exfalso. clear - Hi. lia.
      - destruct (WB _ INB) as ((B0 & B1 & B3 & B4 & B5 & B6) & _). cbn [fst snd] in *.
        rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in B1.
        assert (PAYB : L5.bytes_at RSEGS M ptr (p payload)).
        { unfold p. apply (L5C.rdn_bytes_at RSEGS M payload ptr); [clear - B0; lia| change (Z.of_nat (length payload)) with nn0; clear - B5 SLO SHI SPT; lia| exact ppay]. }
        apply (L5C.bytes_at_agree RSEGS M M3 ptr); [| clear - B0; lia| unfold p; rewrite length_map; change (Z.of_nat (length payload)) with nn0; clear - B5 SLO SHI SPT; lia| exact PAYB].
        intros i Hi. unfold p in Hi. rewrite length_map in Hi. change (Z.of_nat (length payload)) with nn0 in Hi.
        apply EK3. split; [clear - Hi B0 B5 SLO SHI SPT; lia|]. split.
        + left. exists (ptr, nn0). split; [exact INB| cbn [fst snd]; clear - Hi; lia].
        + intros rr Hr Hin. rewrite WF_eq in Hr. cbn in Hr. unfold L5.in_rng in Hin.
          repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Hin; clear - Hin Hi B1; lia|]). destruct Hr. }
    apply (PEBCH2.stage2 L ar C HI LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF payload STR fx3 R3 M3 model3 K ptr g
             BI3 RI3 HK LS3 Q1 Q10 Q11 Q12 Q18 Q22 Q23 SZS NR DRG SRCB ACCd PAYB3 HSTK3 (cr2 nn0 cr NR pcredit)).
    intros fx4 R4 M4 model4 LK4 cr4 A4 s BI4 RI4 S1 S10 S11 S12 S18 S22 S23 HSP SSH SLG CK2 SZI4 HSTKa4 HSTKb4 LS4.
    apply (PEBCH3.stage3 L ar C HI LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF wloc_WF payload ISS fx4 R4 M4 model4 K LK4 cr4 A4 s ptr g
             BI4 RI4 HK LS4 S1 S10 S11 S12 S18 S22 S23 HSP NR DRG (cr3 nn0 cr cr4 NR pcredit CK2) SZI4 HSTKa4 HSTKb4).
    intros fx5 R5 M5 model5 LK5 cr5 A5 s' sm BI5 RI5 LS5 P1 P10 P11 P12 P18 P22 P23 VS5 HIS5 CK3 SZS5 SZI5 HSTKa5 HSTKb5.
    set (g1 := PMST.ST true (PMST.st_sys g) (PMST.st_err g)) in *.
    apply (PEBCH3b.stage3b L ar C HI LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A TP P payload fx5 R5 M5 model5 K LK5 cr5 A5 s s' sm g1
             BI5 RI5 HK LS5 P1 P10 P11 P12 P18 P22 P23 VS5 HIS5 SZS5 SZI5 HSTKa5 HSTKb5).
    intros fx6 R6 M6 model6 BI6 RI6 LS6 T1 T10 T11 T12 T13 T18 T20 T22 T23 T24 T25 VS6 HIS6 HSE6 UO1 UO2 UO3 UO4 DP6 SZP6 SZO6 SZI6 SZS6 SZE6 HSTKa6 HSTKb6.
    apply (PEBCH4.stage4 L ar C HI LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF FAL P payload RDC fx6 R6 M6 model6 K LK5 cr5 A5 s s' sm g1
             BI6 RI6 HK eq_refl LS6 T1 T10 T11 T12 T13 T18 T20 T22 T23 T24 T25 VS6 HIS6 HSE6 UO1 UO2 UO3 UO4 DP6 SZP6 SZO6 SZI6 SZS6 SZE6 HSTKa6 HSTKb6
             (cr4' nn0 cr cr4 cr5 NR pcredit CK2 CK3)).
    intros fx7 R7 M7 model7 LK7 crR A7 qc b BI7 RI7 LS7 U1 U18 U20 U22 U23 U24 U25 VS7 HIS7 HSE7 PA7 U976 CK4 EC0 SZec DEFec SZP7 SZI7 SZS7 SZE7 HSTKa7 HSTKb7.
    pose proof HIS7 as (IS7 & SIZE7 & SMG7 & SMST7 & PAYB7).
    assert (HB7 : PEBHK2.hbase F M7 s s' sm) by (split; [exact VS7| split; [exact IS7| exact SZI7]]).
    apply (PEBCH5.stage5 L ar C HI LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF wsys_WF P payload SYS fx7 R7 M7 model7 K LK7 crR A7
             s s' sm qc b g1 BI7 RI7 HK LS7 U1 U18 U20 U22 U23 U24 U25 HB7 SIZE7 PAYB7 HSE7 PA7 U976 EC0 SZec SZP7 HSTKa7 HSTKb7).
    intros fx9 R9 M9 model9 LK9 A9 BI9 RI9 LS9 X1 X10 X11 X18 X20 X22 X23 X24 X25 HB9 PAYB9 HSE9 PA9 U976'' HEC9 SZP9 HSTKa9 HSTKb9.
    set (g2 := PMST.ST (PMST.st_loc g1) true (PMST.st_err g1)) in *.
    apply (PEBCH7.stage7 L ar C HI LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF FAL werr_WF P payload READ PMODE fx9 R9 M9 model9 K LK9 crR A9
             s s' sm qc b g2 (pa_syscat_obj AD) BI9 RI9 HK LS9 X1 X10 X11 X18 X20 X22 X23 X24 X25 HB9 SIZE7 SMG7 SMST7 PAYB9 HSE9 PA9 U976'' HEC9 SZP9 HSTKa9 HSTKb9 NR HB
             (cr7 nn0 cr cr4 cr5 crR qc b NR pcredit CK2 CK3 CK4)).
    intros fx10 R10 M10 model10 LK10 cr10 A10 nn s1 sm1 en1 k1 e1 BI10 RI10 LS10 EMONO Y18 Y20 Y22 Y23 Y24 Y25 HB10 HP10 CK7 SZP10 HSTKa10 HSTKb10.
    set (g3 := PMST.ST (PMST.st_loc g2) (PMST.st_sys g2) e1) in *.

    assert (CKN : 0 <= fst (PESKA.spa_pot P (PESK.sk_c k1)) /\ 0 <= snd (PESKA.spa_pot P (PESK.sk_c k1))).
    { pose proof HP10 as (_ & _ & _ & KA & _). exact (PESKA.sink_potA_nonneg RSEGS L ar P M10 (F + 432) k1 PO KA). }
    assert (PEX : PayExport payload).
    { pose proof HP10 as (_ & _ & _ & KA & _ & _ & _ & HALT' & SINK).
      pose proof KA as (_ & _ & _ & _ & _ & Hzc & HCAP & _ & SB).
      pose proof (bytes_ok_p payload) as BOK.
      destruct (UbjRefFactsS9.halted_is_final (p payload) nn BOK HALT') as (ELO & _ & _).
      pose proof (UbjRefFactsS9.gi_lo _ _ (UbjRefFactsS9.run_ginv (p payload) BOK (UbjRefFactsS9.fuel (p payload)) UbjRef.init (UbjRefFactsS9.ginv_init _))) as GLO.
      change (0 <= UbjRefFactsS9.F (p payload) <= s_hi (UbjRefFactsS9.final (p payload))) in GLO.
      apply (POUT payload (PESK.sk_c k1)); [change (Z.of_nat (length payload)) with nn0; clear - NR; lia| exact HCAP| intros Hc; destruct (SB Hc) as (_ & _ & _ & _ & X & _); exact X|].
      unfold p in ELO, GLO, SINK. lia. }
    apply (PEBCH8.stage8 L ar C HI LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF FAL P payload VEC OPD SRC fx10 R10 M10 model10 K LK10 cr10 A10
             s s' s1 sm1 en1 k1 e1 nn g3 BI10 RI10 HK LS10 Y18 Y20 Y22 Y23 Y24 Y25 HB10 HP10 SZP10 HSTKa10 HSTKb10).
    intros fx11 R11 M11 model11 LK11 A11 BI11 RI11 LS11 Z18 Z20 Z22 Z23 Z24 Z25 HB11 EA11 KA11 HSTKa11 HSTKb11.
    apply (PEBCH9.stage9 L ar C HI LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF FAL P ESTK SNK fx11 R11 M11 model11 K LK11 cr10 A11
             s s' sm1 en1 k1 g3 BI11 RI11 HK LS11 Z18 Z20 Z22 Z23 Z24 Z25 HB11 EA11 KA11 HSTKa11 HSTKb11).
    intros fx12 R12 M12 model12 LK12 A12 BI12 RI12 LS12 V18 V20 V22 V23 V24 V25 HB12 HSTKa12 HSTKb12.
    apply (PEBCH10.stage10a L ar C HI LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A TP STKSH wapp_WF IL ICok ILY OPD fx12 R12 M12 model12 K LK12 cr10 A12
             s s' sm1 g3 BI12 RI12 HK LS12 V18 V20 V22 V23 V24 V25 HB12 HSTKa12 HSTKb12).
    intros fx13 R13 M13 model13 LK13 A13 BI13 RI13 LS13 J1 J10 J18 J20 J22 J23 J24 J25 HF13 HSTKa13 HSTKb13.
    apply (PEBCH10B.stage10b L ar C HI LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF LCD IOD OPD fx13 R13 M13 model13 K LK13 cr10 A13
             s (PM.sm_st sm1) g3 BI13 RI13 HK LS13 J1 J10 J18 J20 J22 J23 J24 J25 HF13 HSTKa13 HSTKb13).
    intros fx14 R14 M14 model14 LK14 A14 BI14 RI14 LS14 I18 I20 I22 I23 I24 I25 HSTKb14.
    apply (PEBCH11.harness_tail L ar C HI LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A TP RAok G2R SF
             fx14 R14 M14 model14 [] LK14 cr10 A14 K g3 BI14 RI14 HK LS14 I18 I20 I22 I23 I24 I25 HSTKb14).
    intros fxf Rf Mf modelf RPf A0f LSf AHf RTf AMf HHf.
    pose proof BI14 as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5 & BQ6 & BQ7 & BQ8 & BQ9 & BQ10).
    cbn [app] in HHf.
    rewrite UR1.
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHf) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDf & _).
    apply (KONT fxf g3 Rf Mf modelf cr10 LK14 A14).
    + constructor.
      * rewrite L5K.rl10. exact A0f.
      * exact RPf.
      * cbn [lla_credit PECTB.LayA PECTB.CREDIT PNTAL.TopLayA_b]. exact (crF nn0 cr cr4 cr5 crR cr10 qc b (PESK.sk_c k1) NR CK2 CK3 CK4 CKN CK7).
      * intros a Ha Hc NF NJ. apply (proj1 AHf). split; [exact Ha|]. split; [rewrite <- SE; exact Hc|].
        intros rr Hr Hin. unfold WF in Hr. apply NF. apply in_map_iff in Hr. destruct Hr as (iv & <- & Hiv). exists iv. split; [exact Hiv|]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
      * cbn [lla_stack PECTB.LayA PNTAL.TopLayA_b]. rewrite SE. exact (proj1 (proj2 AHf)).
      * intros a Ha Hc. rewrite SE in Hc. exact (proj2 (proj2 AHf) a Ha Hc).
      * cbn [lla_stack PECTB.LayA PNTAL.TopLayA_b] in *. unfold PECTB.STK in *. intros j Hj. unfold byte_at. rewrite (proj1 AHf); [exact (pstksh j Hj)|].
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        assert (AR : HeapIfaceA.S (ahl_ceil ar) <= HeapIfaceA.S (sp - 36864) + j <= HeapIfaceA.S (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1)
                     /\ 2147450880 <= HeapIfaceA.S (sp - 36864) + j < 2 ^ 64).
        { unfold HeapIfaceA.S, HeapIfaceA.SB in *. clear - Hj SLO SHI SPT TOP47. lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        split; [clear - AR; lia|]. split; [rewrite <- SE; right; right; right; right; left; exact (proj1 AR)|].
        intros rr Hr X. rewrite WF_eq in Hr. cbn in Hr. unfold L5.in_rng in X. destruct AR as [_ AR].
        repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in X; clear - X AR; lia|]). destruct Hr.
      * exact LSf.
    + exact PEX.
    + exact RTf.
    + exact BQ4.
    + exact (proj1 AMf).
    + exact (proj2 AMf).
    + intros k Hk. cbn [lla_leak PECTB.LayA PECTB.LEAK PNTAL.TopLayA_b]. unfold PECTB.LEAK.
      pose proof (ffc_incl k LK14 LK (nodup_lk FF LK14 NDf) BQ5) as X. lia.
    + split; [exact HHf|]. split.
      * apply (sj_keep L ar LB FF LK14 M Mf).
        -- pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHf) as (WBf & WFf & W3 & _ & _ & _ & _ & _ & (_ & _ & WW9 & WW10) & _).
           split; [|split; [|split; [exact W3|exact (conj WW9 WW10)]]].
           ++ intros bb0 Hb. destruct (WBf bb0 Hb) as (Q1' & _ & _ & _ & _ & Q6 & _). exact (conj Q1' Q6).
           ++ intros f Hf. destruct (WFf f Hf) as (Q1' & Q2' & Q3' & Q4' & _). exact (conj Q1' (conj Q2' (conj Q3' Q4'))).
        -- intros bb0 a Hb Ha. destruct (WB bb0 Hb) as ((Y0 & _ & _ & Y4 & _ & Y6) & _). unfold app_mem in Y6.
           assert (SR : BIGSHADOW_LO <= a < BIGSHADOW_HI).
           { unfold in_shadow_of in Ha. pose proof (PMKB.S_in_shadow (fst bb0) ltac:(lia)) as SS1. pose proof (PMKB.S_in_shadow (fst bb0 + snd bb0 - 1) ltac:(lia)) as SS2. lia. }
           apply (proj1 AHf). split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SR; lia|]. split.
           ++ rewrite <- SE. do 6 right. exists bb0. split; [exact Hb| exact Ha].
           ++ intros rr Hr X. rewrite WF_eq in Hr. cbn in Hr. unfold L5.in_rng in X. unfold BIGSHADOW_LO, BIGSHADOW_HI in SR.
              repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in X; clear - X SR; lia|]). destruct Hr.
        -- exact SBLK.
      * rewrite Forall_forall in *. intros f Hf. apply CLS13. apply in_app_or in Hf. apply in_or_app. destruct Hf as [Hf|Hf]; [left; exact Hf| right; apply BQ5; exact Hf].
Qed.
End TOP.

Theorem harness_call_ok (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface) (P : PESKA.sink_policyA) :
  PMB.layout L C -> HAJ.asan_iface_okR L ar C SCFG HI -> aicpt_ok L ar IL SCFG HI -> as0_icpt_layout IL -> HAJ.asan_ext_ok L ar SCFG HI PMB.EXT ->
  PESKA.sink_policyA_ok L P -> PESKA.spa_mode P ->
  PECSB.str_ctor_c_spec L ar HI -> PECSB.iss_ctor_c_spec L ar HI -> PECSB.reader_ctor_spec L ar HI -> PMSPA.syscat_spec RSEGS AD L ar HI ->
  PECRRZ.reader_read_specZ RSEGS AD AAD EE L ar HI P ->
  PMSPA.vec_dtor_spec RSEGS AD L ar HI -> PMSPA.opdel_spec RSEGS AD L ar HI -> PMSPA.src_dtor_spec RSEGS AD L ar HI ->
  PMSPA.locale_dtor_spec RSEGS AD L ar HI -> PMSPA.ios_dtor_spec RSEGS AD L ar HI ->
  PECDTA.estk_dtor_spec RSEGS AD EE L ar HI 0xb4794 -> PECDTA.sink_dtor_spec RSEGS AD L ar HI P 0xaafe4 ->
  forall (PayOk PayExport : list byte -> Prop),
    PECSB.pay_in P PayOk -> PECSB.pay_out P PayExport ->
    lib_call_okA_x (PECTB.LayA (tk P) (tb P) L) ar SCFG (HAJ.strict_of HI) PECTB.TopLSA PayOk PayExport.
Proof.
  intros LY HIok ICok ILY EXT PO PMODE STR ISS RDC SYS READ VEC OPD SRC LCD IOD ESTK SNK.
  exact (harness_call_okA L ar C IL HI P LY HIok ICok ILY EXT PO PMODE STR ISS RDC SYS READ VEC OPD SRC LCD IOD ESTK SNK).
Qed.
End SCFG_1.
End PEBCHN.
