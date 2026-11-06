(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From Stdlib Require NArith PArith FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1 j1.

(* [comment removed for export] *)
Module RefillCL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "of_nat"; "lt"; "mul"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "@Corelib.Init.Datatypes"; "length"; "bool"; "list"; "true"; "nil"; "prod"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qall"; "q_ids"; "qitems"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "cs_mapped_user"; "AA"; "aa_geom"; "class_state"; "ag_spacebeg"; "cs_cache"; "cs_free_array"; "cs_mapped_free_array"; "ag_thread"; "ageom"; "qbatch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kUserMapSize"; "Sh"; "kFreeArraySize"; "kFreeArrayMapSize"; "kQuarantineBatchCount"; "kRegionInfoStride"; "kRegionSize"; "kUserSpaceSize"; "region_beg"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "qmax"; "MUCAP"; "NBQ"; "QCAP"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "needs_populate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "isum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "refill_zone"; "rf_grows"; "rf_new"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells SegQ_defs PrimCredit PrimCreditLaws Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.PrimRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma q_ids_bound_of_counts : ltac2:(tb__ "0|3|
S14S5S6S0Z1M0R1A2S0R1Z1eA2A2S0S2S9S1dS10R3A1A2A1S2aA2S0S2S9SeS5S5A2M1S12S10R4A1A1A2A1S4S22S2aA2A2S0S32S12S10R5A1A1A1S2bA2G1S36G1R1S12S10R7A1M2A1A3S0G0SfS5S5R2A3A2F_;Fit;S0S2S9S5S11S15R7A1G2R6A3A2A1S28R6A1A2F_;F_;F_;F_;F_;Fc;FA;").
Proof.
  intros A c Hc NB NI IS I1.
  unfold q_ids, qmax. rewrite length_app, !length_map, Nat2Z.inj_add.
  set (p := fun it : Z * Z => is_primary (snd it) && (it_cls it =? c)).
  assert (ITEMS : Z.of_nat (length (List.filter p (qitems (qall A)))) <= (if nmin c =? 0 then 0 else Z.min (kQuarantineBatchCount * NBQ) (QCAP / nmin c))).
  { assert (PN : forall it, In it (qitems (qall A)) -> p it = true -> 1 <= nmin c <= snd it).
    { intros it Hit Hp. unfold p in Hp. apply andb_prop in Hp as [Hp1 Hp2]. apply Z.eqb_eq in Hp2. unfold it_cls in Hp2.
      pose proof (I1 it Hit) as H1.
      assert (H2 : snd it <= 64512).
      { destruct (Z_le_dec (snd it) 64512) as [L|G]; [exact L|]. rewrite (not_primary_large (snd it)) in Hp1 by lia. discriminate Hp1. }
      pose proof (nmin_ok (snd it) (conj H1 H2)) as NM. rewrite Hp2 in NM. exact NM. }
    destruct (Z.eqb_spec (nmin c) 0) as [E0|NE].
    -
      destruct (List.filter p (qitems (qall A))) as [|it l] eqn:EF; [cbn; lia|]. exfalso.
      assert (Hin : In it (List.filter p (qitems (qall A)))) by (rewrite EF; left; reflexivity). apply filter_In in Hin as [Hi Hp].
      pose proof (PN it Hi Hp). lia.
    - apply Z.min_glb.
      + pose proof (filter_length_le p (qitems (qall A))) as FL. apply Nat2Z.inj_le in FL. lia.
      + assert (NP : 1 <= nmin c).
        { destruct (List.filter p (qitems (qall A))) as [|it l] eqn:EF.
          -   unfold nmin in *. clear -NE Hc.
            assert (C : forall k, In k nmin_tab -> 0 <= k) by (intros k Hk; unfold nmin_tab in Hk; repeat (destruct Hk as [<-|Hk]; [lia|]); destruct Hk).
            assert (0 <= nth (Z.to_nat (c - 1)) nmin_tab 0) by (apply C; apply nth_In; unfold nmin_tab; cbn [length]; lia). lia.
          - assert (Hin : In it (List.filter p (qitems (qall A)))) by (rewrite EF; left; reflexivity). apply filter_In in Hin as [Hi Hp]. exact (proj1 (PN it Hi Hp)). }
        apply Z.div_le_lower_bound; [lia|].
        pose proof (isum_filter_ge p (nmin c) (qitems (qall A)) (fun it Hit => ltac:(pose proof (I1 it Hit); lia)) (fun it Hit Hp => proj2 (PN it Hit Hp))) as W. lia. }
  destruct (c =? 24); [rewrite length_map | cbn [length]]; fold p; lia.
Qed.

Theorem populate_roomQ : ltac2:(tb__ "0|0|
S14S2dSbS31Q40A1A1S2cS5S2eR5R4R3R2A4S6S0Z1R2A2S0R2Z1eA2A2S30R7R3A2S16S7SbS5A1S18R1A1SdS5A1A3S0S2S9S5S19R2A1A2A1Z7A2S0S2S9S5S11S15RaA1S10RaA1R6A3A2A1S28R6A1A2S0S1S13R4A1S1eA2S29R7A1A2F_;F_;F_;Tcs;F_;F_;Fc;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md c HA Hc cs Hcache Hfa QB.
  destruct HA as (_ & _ & _ & HRest & _ & HI3 & _).
  destruct HRest as (_ & _ & HPR & _). destruct HPR as (_ & _ & _ & PC). pose proof (PC c Hc) as P4. change (nthZ (aa_cls A) c cs_empty) with cs in P4.
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N2 & _ & N4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TI & CV & _ & _).
  destruct HI3 as (_ & _ & _ & _ & _ & _ & _ & SL & _).
  pose proof (live_ids_bound (aa_geom A) A c) as LB.
  destruct (cap_facts c Hc) as (HS & _ & MCU & _).
  rewrite Hcache in CV. cbn [length] in CV. unfold slots in CV.
  assert (Eau : cs_allocated_user cs = Size c * (cs_allocated_user cs / Size c)) by (apply Z.div_exact; [clear -HS; lia | exact N4]).
  rewrite !Nat2Z.inj_add in CV. cbn [Z.of_nat] in CV.
  unfold MUCAP. set (S := Size c) in *. set (sl := cs_allocated_user cs / S) in *. set (mu := cs_mapped_user cs) in *. set (au := cs_allocated_user cs) in *.
  set (nf := Z.of_nat (length (cs_free_array cs))) in *. set (nl := Z.of_nat (length (live_ids (aa_geom A) A c))) in *. set (nq := Z.of_nat (length (q_ids (aa_geom A) (qall A) c))) in *.
  set (q := qmax c) in *. set (sv := small_live A) in *. unfold PRIM_LIVE_MAX in *. unfold kUserMapSize.
  clearbody S sl mu au nf nl nq q sv. clear -HS TI CV Eau Hfa QB LB SL. nia.
Qed.

Corollary rfacts_room : ltac2:(tb__ "0|0|
S14S2dSbS31Q40A1A1S2cS5S2eR5R4R3R2A4S6S0Z1R2A2S0R2Z1eA2A2S30R7R3A2S16S7SbS5A1S18R1A1SdS5A1A3S0S2S9S5S11S15R9A1S10R9A1R5A3A2A1S28R5A1A2S7SaS2fR6R3A2ScA3S0S1S13R4A1S1eA2S29R7A1A2F_;F_;F_;Tcs;F_;F_;Fc;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md c HA Hc cs Hcache QB NP. apply (populate_roomQ A rho tp md c HA Hc Hcache); [|exact QB].
  unfold needs_populate in NP. apply Z.ltb_lt in NP. destruct (kchunks_facts c Hc) as (K1 & _). subst cs. clear -NP K1. lia.
Qed.

Lemma refill_zone_where : ltac2:(tb__ "0|4|
S1cSaS5S16S5S6S0Z1R3A2S0R3Z1eA2A2S0Z0M0S17R6A1A2S0G0S13R4A1A2S0G0S1aR5A1A2S7SaS2fR7R6A2ScA3S6S0S1S13R7A1S1eA2S25A2S6S0G0S35R8R7A2M1A2S0S4Z4S1S2S9S5S19R7A1A2A1G1A2A2S20A2A2A2F_;S7SaS34R8R7A2ScA3S0S1S1aR8A1S21A2S20A2F_;S33RbRaR9R8R7A5S1bRcA1S5S17RdA1S5S26R1RcA2S5S8S6S0S1R3Z120A2RbA2S3RbS1R3Zad0A2A2A2S8S6S0S27R2RdA2M2RbA2S3RbS1G2S23A2A2A2S8S6S0R1RbA2S3RbS1R1S24A2M3A2A2S6S0S1fR1A1RbA2S3RbS1fG3A1A2A2A2A2A2Trb;TSB;TT;F_;F_;F_;F_;F_;F_;F_;Fz;Fcs;Fc;Finited;FG;").
Proof.
  intros G inited c cs z Hc HSB HMU HMF HP HG HZ T SB rb. unfold refill_zone in HZ. cbn zeta in HZ. fold T SB in HZ.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0. destruct (kchunks_facts c Hc) as (K1 & _).
  assert (RB0 : 0 <= rb) by (unfold rb, region_beg, kRegionSize; fold SB; lia).
  assert (SHP : forall a, rb <= a -> a + 262144 <= rb + 2 ^ 32 -> Sh rb <= Sh a /\ Sh a + 32768 <= Sh (rb + 2 ^ 32)).
  { intros a A1 A2. split; [apply Geometry.Sh_mono; exact A1|]. unfold Sh.
    pose proof (Z.div_le_mono (a + 262144) (rb + 2 ^ 32) 8 ltac:(lia) A2) as D.
    replace (a + 262144) with (a + 32768 * 8) in D by lia. rewrite Z.div_add in D by lia. lia. }
  unfold free_array in HZ. fold rb in HZ. unfold kRegionInfoStride, kRegionSize, kUserSpaceSize, kFreeArraySize, kFreeArrayMapSize, kUserMapSize, kRegionSize in *.
  destruct HZ as [H|[H|[H|[(NP & H)|[(GR & H)|(_ & H)]]]]].
  - left. lia.
  - left. lia.
  - right; left. lia.
  - destruct (HP NP) as (P1 & P2 & P3). destruct H as [H|[H|H]].
    + right; right; left. lia.
    + right; right; right. destruct (SHP (rb + cs_mapped_user cs) ltac:(lia) ltac:(lia)) as [S1 S2]. lia.
    + right; right; left. lia.
  - specialize (HG GR). destruct H as [H|H].
    + right; right; left. lia.
    + right; right; right. destruct (SHP (rb + (2 ^ 32 - 2 ^ 29) + cs_mapped_free_array cs) ltac:(lia) ltac:(lia)) as [S1 S2]. lia.
  - left. exact H.
Qed.
End RefillCL.

(* [comment removed for export] *)
Module F0A_instokC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "nat"; "pair"; "cons"; "bool"; "true"; "prod"; "list"; "nil"; "app"; "fst"; "snd"; "orb"; "negb"; "option"; "andb"; "false"; "length"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "rho_sets"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "opp"; "pow"; "sub"; "modulo"; "mul"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "rw"; "sprop"; "SLit"; "rm"; "obj_range"; "valuation"; "holds"; "rl"; "agree_below"; "SAlu"; "SPUlt"; "SVar"; "eval"; "pairwise_disjoint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "in_zone"; "zcheck"; "@Stdlib.Lists.List"; "forallb"; "In"; "Forall2"; "existsb"; "tl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "NRT"; "carve_ok"; "spec_zone"; "zone_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "topG"; "aa_q_thread"; "ag_thread"; "ag_ctx"; "ag_spacebeg"; "aa_geom"; "aa_live"; "cs_mapped_user"; "qb_items"; "@stdpp.bitvector.definitions"; "bv"; "bv_signed"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "ZD_NRT"; "zhiF"; "zloF"; "img_okb"; "cache24"; "spec_ne"; "rhoF_of"; "cnt24"; "hw_of"; "j_min"; "j_qb"; "j_qf"; "j_st"; "lastq"; "top24"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "offp"; "ZUC"; "NVN"; "K_i1"; "K_i2"; "K_pcc"; "VFC"; "ZD_NVC"; "K_bhf"; "K_qc"; "K_qce"; "VFN"; "eRIS"; "qcondCx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone"; "img_okD"; "zoneF"; "rng_below"; "same_rng"; "winpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "V_DEPTH"; "chain_pre"; "free_depth"; "top_high"; "ulink"; "ustop"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "vQB"; "vQF"; "vQS"; "vBS"; "vNX"; "vQN"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "F_pc"; "cls_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "instG_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC.FACTSC"; "rd_okG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_pins"; "spec_on"; "sprop_on"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "F_cas"; "cA"; "cQ"; "O_blkN"; "O_sh"; "QBe"; "QBf"; "VFACT"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "kSpaceSize"; "IMG_HI"; "IMG_LO"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kQuarantineBatchCount"; "kUserMapSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "needs_populate"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@LinuxProcessSemantics.Riscv.Instr";
"ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC.FACTSC.VARIANT"; "rd_okG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "QG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_pins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2 PrimCredit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition eRIS : sv := ltac2:(tb__ "0|0|
S2eSa1S85S27S97A1A3").
Definition K_pcc : carve_spec := ltac2:(tb__ "0|4|
S3S7S7S23S0A2M0S0A2S8S7S7S0S2A2M1S23A2M2A1S3G0S0S3S23S0S8eZ780M3A4Z784A4S4G2S3G1S23S3S0S2G3U4A4S27Z0A1A4S9G2A1A3A4").
Definition K_i1 : carve_spec := ltac2:(tb__ "0|4|
S3S7S7S23S0A2M0S0A2S8S7S7S0S2A2M1S23A2M2A1S3G0S0S3S23S0S27Z0A1Zeaa80M3A4Zeaa84A4S4G2S3G1S23S3S0S2G3U4A4S27ZffffffffA1A4S9G2A1A3A4").
Definition K_i2 : carve_spec := ltac2:(tb__ "0|5|
S3S7S7S23S0A2M0S0A2S8S7S7S0S2A2M1S23A2M2A1S3G0S0S3S23S0S27Z0A1M3Zeaa88M4A4Zeaa91A4S4G2S3G1S23S3S0S2G4U8A4S6cA4S4G2S3G1S23S3S0S2Zeaa90U1A4G3A4S9G2A1A3A3A4").
Definition K_qce : carve_spec := ltac2:(tb__ "0|5|
S3S7S7S23S0A2M0S0A2S8S7S7S0S2A2M1S23A2M2A1S3G0S0S3S23S0S8fZ0M3A4Z20A4S4G2S3G1S23S3S0S2G3U8M4A4S27G3A1A4S4G2S3G1S23S3S0S2Z8G4A4S80A4S4G2S3G1S23S3S0S2Z10G4A4S7fA4S4G2S3G1S23S3S0S2Z18G4A4S81A4S9G2A1A3A3A3A3A4").
Definition K_qc : carve_spec := ltac2:(tb__ "0|5|
S3S7S7S23S0A2M0S0A2S8S7S7S0S2A2M1S23A2M2A1S3G0S0S3S23S0S8fZ0M3A4Z20A4S4G2S3G1S23S3S0S2G3U8M4A4S84A4S4G2S3G1S23S3S0S2Z8G4A4S80A4S4G2S3G1S23S3S0S2Z10G4A4S7fA4S4G2S3G1S23S3S0S2Z18G4A4S81A4S9G2A1A3A3A3A3A4").
Definition K_bhf : carve_spec := ltac2:(tb__ "0|5|
S3S7S7S23S0A2M0S0A2S8S7S7S0S2A2M1S23A2M2A1S3G0S0S3S23S0S7fZ0M3A4Z18A4S4G2S3G1S23S3S0S2G3U8M4A4S83A4S4G2S3G1S23S3S0S2Z8G4A4S82A4S4G2S3G1S23S3S0S2Z10G4A4S27Z3fdA1A4S9G2A1A3A3A3A4").

Definition NVC (f : bool) : list carve_spec := ltac2:(tb__ "0|1|
S5S8S17A1Lf;Vf;S4S17S69S4S17S68S4S17S65S4S17S63S4S17S64S9S17A1A3A3A3M0A3A3S4S17S6aG0A3X5x2").
Definition VFC (f : bool) : list sprop := ltac2:(tb__ "0|0|
S94S5S95Lf;Vf;S93S92X5x2A1").
Definition NVN : list carve_spec := [].
Definition BIGF : sprop := ltac2:(tb__ "0|0|
S2fS27S96A1S30PdA1A2").
Definition VFN : list sprop := [BIGF].

Definition qcondCx (f : bool) (A : AA) : Prop := ltac2:(tb__ "0|1|
S14S5OLf;Vf;S14S16S13S8S3fA1S41VA;A1S9S3fA1A3M0A1S13S0S22S12S7S0S0A2S48S5bVA;A1A1A2A1S9cA3A2G0X5x2S13S8S0A1S52VA;A1S9S0A1A3A2").
Definition ZD_NVC (f : bool) : list zdesc := ltac2:(tb__ "0|6|
S5S8S33A1Lf;Vf;S4S7S7S2S0A2M0S0A2M1S3G0S0S3S2S0U1M2Z50A4Z70A4M3S4G1S3G0S0S3S2S0U4Z0A4Z18A4S4G1S3G0S0S3S2S0G2Z850A4Z854A4S4G1S3G0S0S3S2S0U0M4Zeaa80A4Zeaa84A4S4G1S3G0S0S3S2S0G4Zeaa88A4Zeaa91A4S9G1A1A3A3A3M5A3A3S4G1G3G5A3X5x2").
Definition ZUC (f : bool) : list nat := ltac2:(tb__ "0|5|
S5S8S2A1Lf;Vf;S4S2U0M0S4S2U1M1S4S2U2M2S4S2U3M3S4S2U4S9S2A1M4A3A3A3A3A3S4S2G0S4S2G1S4S2G2S4S2G3G4A3A3A3A3X5x2").
Lemma ZD_chkC : ltac2:(tb__ "0|1|
S5S14S13S5S35SaS33S4eS67R1A1A3M0A1S6A3S14S13S5S36S33S51G0A3S6A3S14S13S5S36S17S53SaS17S3bS5fR1A1A3A3S6A3S13S5S36S33S72G0A3S6A3A2A2A2Ff;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma ZD_chkN : ltac2:(tb__ "0|0|
S14S13S5S35S4eA1S6A3S14S13S5S36S33S51S4eA3S6A3S14S13S5S36S17S53S3bA3S6A3S13S5S36S33S72S4eA3S6A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition offp (i : positive) : bool := ltac2:(tb__ "0|0|
S10SeSa0Vi;P7fA2A1SeSa0Vi;P82A2A1A2").
Lemma offp_chk : ltac2:(tb__ "0|1|
S5S14S13S5S36S17S8bS60A1SaS17S3bS5fR1A1A3A3S6A3S14S13S5S36S26S8cS60A1M0SaS26S86SaS26S3aS26S87S6A1A2S8dA3A3A3S6A3S13S5S36S26G0SaS26S86SaS26S3aS26S87S11A1A2S8dA3A3A3S6A3A2A2Ff;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Section FACTSC.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Variables (A : AA) (rho : valuation) (tp : list word) (md : Model) (p n : Z).
Hypothesis HA : ltac2:(tb__ "0|0|
VAInv;VA;Vrho;Vtp;Vmd;A4").
Hypothesis HL : ltac2:(tb__ "0|0|
S37S7S0S0A2S3S0S0Vp;Vn;A4S46VA;A1A3").
Hypothesis HCL : blk_cls p n.
Hypothesis Hii : aa_internal_inited A = true.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S13S0S4bQ40S25Vrho;PcA2A2Vp;A3").
Hypothesis Hn13 : ltac2:(tb__ "0|0|
S13S0S4bQ40S25Vrho;PdA2A2Vn;A3").
Variable t : Z.
Hypothesis Ht : ltac2:(tb__ "0|2|
S14S14S1aZ0Vt;A2S1cVt;Z100A2A2S14S13S0S20Vt;Z4A2Z1A3S14S6fS71Vsegs;S28Vrho;A1A2M0S70S1fVp;Z10A2U4M1S56Vt;Vn;A2A3A2S6fG0S70S1fVp;ZcA2G1S20Vn;S1eZ2Z20A2A2A3A2A2A2A2").
Variable jv : junkF.
Hypothesis Hjv : ltac2:(tb__ "0|9|
S14S14S1aZ0M0S57Vjv;A1M1A2S1cG1S1eZ2Z40A2M2A2A2S14S14S1aG0S5aVjv;A1M3A2S1cG3G2A2A2S14S14S1aG0S59Vjv;A1M4A2S1cG4G2A2A2S14S14S1aG0S58Vjv;A1M5A2S1cG5G2A2A2S14S6fS71Vsegs;S28Vrho;A1A2M6S70S1bSa3Z48A2U8M7G1A3A2S14S6fG6S70S1bS42S45VA;A1A1M8Zae0A2G7G3A3A2S13S8S3fA1S41VA;A1S9S3fA1A3S14S6fG6S70S1bG8Z58A2G7G4A3A2S6fG6S70S1bG8Z60A2G7G5A3A2A2F_;A2A2A2A2A2A2").
Let G : ageom := aa_geom A.
Let m : bview := ltac2:(tb__ "0|0|
S71Vsegs;S28Vrho;A1A2").
Let rho1 : valuation := ltac2:(tb__ "0|0|
S54VA;Vrho;Vp;Vn;Vt;Vjv;A6").

Definition rhoC_of : valuation := ltac2:(tb__ "0|0|
S54S9eVA;Z18A2Vrho;Vp;Vn;Vt;Vjv;A6").
Let rho1R : valuation := rhoC_of.

Lemma rw_rho_sets_pw : ltac2:(tb__ "0|4|
S8S7S1S49Q40A1M0A2M1A1M2G2S2aS2aS1S38G1G1G1G1S14S13S1SbS1G0R2A3M3SbS1G0R1A3A3S13S1G3R3A3S13G0ScS1G0R3A3ScS1G0R2A3A3F_;A2Lb;La;R5R4A5S13G0S25R4R2A2S25R3R2A2A3S13G0S25S19R5R7A2R3A2S25S19R4R6A2R3A2A3F_;F_;Fi;Fr';Fr;Fl';Fl;").
Proof.
  intros l l' r r' i HF. revert r r'. induction HF as [|[k v] [k' v'] l l' [Ek Ev] HF IH]; intros r r' Hr; cbn [rho_sets]; [exact Hr|].
  cbn [fst snd] in Ek, Ev. subst k'. apply IH. unfold rho_set_rw. cbn [rw]. destruct (Pos.eqb_spec i k) as [->|NE]; [exact (Ev eq_refl) | exact Hr].
Qed.
Lemma pins_off : ltac2:(tb__ "0|0|
S1S13S5S60R1A1S6A3S13S49Q40A1S25Vrho1R;R2A2S25Vrho1;R2A2A3F_;Fi;").
Proof.
  intros i Hi. unfold offp in Hi. apply andb_prop in Hi as [H1 H2]. apply negb_true_iff in H1, H2. apply Pos.eqb_neq in H1, H2.
  unfold rho1R, rhoC_of, rho1, rhoF_of. apply rw_rho_sets_pw; [|reflexivity].
  repeat (apply Forall2_cons; [cbn [fst snd]; split; [reflexivity | intros E; first [reflexivity | exfalso; congruence]]|]). apply Forall2_nil.
Qed.
Lemma pins_rl : ltac2:(tb__ "0|0|
S1S13S8S49Q8A1A1S2cVrho1R;R1A2S2cVrho1;R1A2A3Fl;").
Proof. intros l. unfold rho1R, rhoC_of, rho1, rhoF_of. rewrite !rl_rho_sets. reflexivity. Qed.
Lemma pins_rm : ltac2:(tb__ "0|0|
S13S49Q40A1SfS49Q8A1A1F_;S28Vrho1R;A1S28Vrho1;A1A3").
Proof. unfold rho1R, rhoC_of, rho1, rhoF_of. rewrite !rm_rho_sets. reflexivity. Qed.
Lemma pins_rm0 : ltac2:(tb__ "0|0|
S13S49Q40A1SfS49Q8A1A1F_;S28Vrho1R;A1S28Vrho;A1A3"). Proof. unfold rho1R, rhoC_of, rhoF_of. apply rm_rho_sets. Qed.

Lemma geoT : ltac2:(tb__ "0|4|
S14S1aZ1000M0S42VG;A1M1A2S14S1aS1bG1G0A2M2S40VG;A1M3A2S14S15S1aG2Z10000A2S1aZ643000G1A2A2S1aG3Z7fffff800000A2A2A2A2").
Proof.
  pose proof (geomF A rho tp md n HA t) as (T1 & T2 & _). pose proof (geomTI A rho tp md HA) as TI. pose proof (topG_range G) as TR. unfold G in *. split; [lia|]. split; [lia|]. split; [exact TI | lia].
Qed.
Lemma EcA1 : ltac2:(tb__ "0|0|
S13S0S4bQ40S31Vrho1;S8eA2A2S1bS42VG;A1Zd0A2A3").
Proof.
  pose proof geoT as (T1 & T2 & _ & T4). cbn [eval cA vT]. change (rw rho1 151%positive) with (Z_to_bv 64 (ag_thread G)).
  rewrite add_val, !u64_lit by lia. apply Z.mod_small. lia.
Qed.

Lemma carve_pcc : ltac2:(tb__ "0|0|
S13S8S0A1S52VA;A1S9S0A1A3S3cVrho1;S65A2F_;").
Proof.
  intros HC0. pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT). destruct HRest as (Hsep & HLB & HPR & _).
  destruct HPR as (_ & _ & _ & PC). specialize (PC 24 ltac:(lia)). unfold class_repr in PC.
  destruct PC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PE & _ & _ & CI & CN & _).
  pose proof geoT as (T1 & T2 & TI & T4). fold G in PE, CI, CN.
  assert (MVT : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = view segs (rm rho) z) by (intros z Hz; apply (MV_T A rho tp md HA); exact Hz).
  assert (CW : cell_ok m (mkACell (ag_thread G + 208 + 1920) 4 0)).
  { unfold cache24 in HC0. destruct (aa_cache_inited A) eqn:ECI.
    - destruct (CI eq_refl) as (C1 & _). rewrite HC0 in C1. cbn [length Z.of_nat] in C1.
      intros j Hj. specialize (C1 j Hj). cbn [c_addr c_w RtCells.c_val] in C1, Hj |- *. rewrite MVT in C1 by lia. replace (ag_thread G + 208 + 1920 + Z.of_nat j) with (ag_thread G + 208 + 80 * 24 + Z.of_nat j) by lia. exact C1.
    - destruct (CN eq_refl) as (_ & FZ). intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
      rewrite nth_enc_bytes by lia. unfold le_byte. rewrite Z.mod_0_l by lia. rewrite Z.shiftr_0_l, Z.mod_0_l by (cbn; lia).
      specialize (FZ (ag_thread G + 208 + 1920 + Z.of_nat j) ltac:(lia)). rewrite MVT in FZ by lia. exact FZ. }
  unfold K_pcc, carve_ok. cbn zeta. rewrite EcA1.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
  split.
  - intros off Hoff. change (rm rho1) with (rm rho). apply (cell_wok_rd2 (rm rho) (ag_thread G + 208 + 1920) 4 0 (ag_thread G + 208 + off) CW); cbn [Z.of_nat]; lia.
  - unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil. change (rm rho1) with (rm rho).
    exact (civ_cell rho1 (rm rho) (ag_thread G + 208) 1920 4 0 (SLit 0) CW eq_refl ltac:(lia) ltac:(lia)).
Qed.

Lemma carve_inst : ltac2:(tb__ "0|0|
S14S3cVrho1;S63A2S3cVrho1;S64A2A2").
Proof.
  pose proof HA as (HG & HR & _). pose proof (geomF A rho tp md n HA t) as (_ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  pose proof (topG_range (aa_geom A)) as ACV.
  assert (E155 : rw rho1 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A))) by reflexivity.
  assert (ERIS : eval rho1 eRIS = Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize)).
  { unfold eRIS, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states.vSB. cbn [eval]. rewrite E155. rewrite kSpaceSize_val. apply bv_eq. rewrite add_val, !u64_lit by lia. apply Z.mod_small. lia. }
  assert (Erm : rm rho1 = rm rho) by reflexivity.
  split; unfold K_i1, K_i2, carve_ok; cbn zeta; cbn [eval]; rewrite ?u64_lit by lia.
  all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
  all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
  all: rewrite ?Erm.
  all: split; [intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]|].
  all: unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil.
  all: try (rewrite ERIS; rewrite kSpaceSize_val).
  all: cbn [eval]; civ_any2 HR.
Qed.

Let qbF : Z := qb_addr (lastq A).
Let nbF : Z := ltac2:(tb__ "0|0|
S1bS1bS44VG;A1S21Z18S1eZ2Z20A2A2A2S21Z10S5cVA;A1A2A2").
Let zbF (z : nat) : Z := ltac2:(tb__ "0|0|
S2S0Lz;Vz;Z0S2S2S0Ln0;R1S42VG;A1S2S2S0Ln1;R1S43VG;A1S2S2S0Ln2;R1Vp;S2S2S0Ln3;R1VqbF;S2VnbF;Ln4;X2x2Ln3;X2x2Ln2;X2x2Ln1;X2x2Ln0;X2x2").

Section VARIANT.
Variables (NV : list carve_spec) (ZD : list zdesc) (ZU : list nat).
Hypothesis HZU : ltac2:(tb__ "0|0|
S2S37S2R1VZU;A3S5dR2U4A2F_;Fz;").
Hypothesis HZ4 : ltac2:(tb__ "0|0|
S37S2U4VZU;A3S16S13S8S3fA1S41VA;A1S9S3fA1A3A1F_;").
Hypothesis H03 : ltac2:(tb__ "0|0|
S2S5dR1U3A2S37S2R2VZU;A3F_;Fz;").
Hypothesis HINZ : ltac2:(tb__ "0|0|
S38S24S33S34Vrho1;VzbF;S50S4fVZU;A5S4dS17S24S18VNV;A4VZD;A5").
Hypothesis HCHK : ltac2:(tb__ "0|1|
S14S13S5S35SaS33S4eVZD;A3M0A1S6A3S14S13S5S36S33S51G0A3S6A3S14S13S5S36S17S53SaS17S3bVNV;A3A3S6A3S13S5S36S33S72G0A3S6A3A2A2A2").
Hypothesis HCARVE : ltac2:(tb__ "0|0|
S4cS17S3cVrho1;A1VNV;A3").

Lemma Q4facts : ltac2:(tb__ "0|5|
S37S2U4VZU;A3S14S15S1aS1bVqbF;Z2000A2M0S42VG;A1M1A2S1aS1bG1Z1000M2A2VqbF;A2A2S14S15S1aG0S43VG;A1M3A2S1aS1bG3G2A2VqbF;A2A2S14S15S1aS1bVp;S6eVn;A1A2VqbF;A2S1aG0S1fVp;Z10A2A2A2S14S1aS44VG;A1M4VqbF;A2S1aG0S1bG4S97A2A2A2A2A2A2F_;").
Proof.
  intros H4. pose proof (HZ4 H4) as HNE. pose proof (qF A rho tp md p n HA HL) as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & _ & _ & QL).
  destruct (QL HNE) as (_ & _ & _ & _ & _ & _ & _ & _ & BS1 & BS2 & BT' & BC' & BP'). unfold kQuarantineBatchSize in *. unfold qbF, lastq, G.
  split; [exact BT'|]. split; [exact BC'|]. split; [exact BP'|]. split; [exact BS1 | exact BS2].
Qed.
Lemma zsepC : ltac2:(tb__ "0|3|
S2S2S37S2R2VZU;A3M0G0S16S13S2R4R3A3A1S15S1aS1bVzbF;R5A1M1S4fR5A1A2S1bVzbF;R4A1M2S50R4A1A2A2S1aS1bG2S4fR4A1A2S1bG1S50R5A1A2A2A2F_;F_;F_;Fz';Fz;").
Proof.
  assert (HZ : forall y, In y ZU -> (y = 0 \/ y = 1 \/ y = 2 \/ y = 3 \/ (y = 4 /\ In 4 ZU))%nat).
  { intros y Hy. pose proof (HZU y Hy). destruct y as [|[|[|[|[|y]]]]]; try lia. do 4 right. split; [reflexivity | exact Hy]. }
  pose proof (geomF A rho tp md n HA t) as (T1 & T2 & _ & C1 & C2 & S1 & S2 & _ & _ & _ & TC & TR & TI & CI & TB & CB).
  pose proof (blkF_geom A rho tp md p n HA HL HCL) as (B1 & _ & B3 & B4 & BT & BC & BN & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & _).
  rewrite kSpaceSize_val in S2. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, HIGH_SHADOW_END, IMG_LO, IMG_HI, LOW_SHADOW_BEG in *.
  unfold G in *.
  assert (P01 : 0 + 0x643000 <= ag_thread (aa_geom A) + 0 \/ ag_thread (aa_geom A) + 0x1000 <= 0 + 0xe1000) by (clear -TI; lia).
  assert (P02 : 0 + 0x643000 <= ag_ctx (aa_geom A) + 8 \/ ag_ctx (aa_geom A) + 0x1000 <= 0 + 0xe1000) by (clear -CI; lia).
  assert (P03 : 0 + 0x643000 <= p + -16 \/ p + 0 <= 0 + 0xe1000) by (clear -B1; lia).
  assert (P12 : ag_thread (aa_geom A) + 0x1000 <= ag_ctx (aa_geom A) + 8 \/ ag_ctx (aa_geom A) + 0x1000 <= ag_thread (aa_geom A) + 0) by (clear -TC; lia).
  assert (P13 : ag_thread (aa_geom A) + 0x1000 <= p + -16 \/ p + 0 <= ag_thread (aa_geom A) + 0) by (clear -BT N1 B3; lia).
  assert (P23 : ag_ctx (aa_geom A) + 0x1000 <= p + -16 \/ p + 0 <= ag_ctx (aa_geom A) + 8) by (clear -BC B3; lia).
  assert (P4 : In 4%nat ZU ->
     (0 + 0x643000 <= qbF + 0 \/ qbF + 8192 <= 0 + 0xe1000)
     /\ (ag_thread (aa_geom A) + 0x1000 <= qbF + 0 \/ qbF + 8192 <= ag_thread (aa_geom A) + 0)
     /\ (ag_ctx (aa_geom A) + 0x1000 <= qbF + 0 \/ qbF + 8192 <= ag_ctx (aa_geom A) + 8)
     /\ (p + 0 <= qbF + 0 \/ qbF + 8192 <= p + -16)).
  { intros H4. destruct (Q4facts H4) as (X1 & X2 & X3 & X4 & _). unfold G in *. split; [clear -X4 S1; lia|]. split; [clear -X1; lia|]. split; [clear -X2; lia|]. clear -X3 N1 B3; lia. }
  assert (SYM : forall a b c d : Z, a <= b \/ c <= d -> c <= d \/ a <= b) by (clear; intros; lia).
  clear T1 T2 C1 C2 S1 S2 TC TR TI CI TB CB B1 B3 B4 BT BC BN N1.
  intros z z' Hz Hz' NE.
  destruct (HZ z Hz) as [-> |[-> |[-> |[-> |[-> H4]]]]]; destruct (HZ z' Hz') as [-> |[-> |[-> |[-> |[-> H4']]]]];
    try (exfalso; apply NE; reflexivity); cbn [zbF zloF zhiF];
    try match goal with H : In 4%nat ZU |- _ => pose proof (P4 H) as (P04 & P14 & P24 & P34) end;
    first [ assumption | apply SYM; assumption ].
Qed.
Lemma inz_G : ltac2:(tb__ "0|0|
S38S24S33S34Vrho1;VzbF;S50S4fVZU;A5S4dS17S24S18SaS17S3bVNV;A3A4SaS33S4eVZD;A3A5").
Proof. rewrite map_app. apply Forall2_app; [|exact HINZ]. exact (inz_NRT A rho tp md p n HA HL HCL Hp12 t Ht jv ZU H03). Qed.
Theorem pd_G : ltac2:(tb__ "0|0|
S32Vrho1;S4dS17S24S18SaS17S3bVNV;A3A4A2").
Proof. apply (zones_pd rho1 zbF zloF zhiF ZU zsepC _ (ZD_NRT ++ ZD)); [exact inz_G | exact (proj1 HCHK)]. Qed.
Lemma zfactsC : ltac2:(tb__ "0|3|
S2S37S2R1VZU;A3S16S13S2R2U0A3A1S14S1aZ1000S1bVzbF;R3A1M0S50R3A1A2M1A2S14S1aS1bG0S4fR3A1A2M2S40VG;A1A2S14S15S1aG2S99A2S1aS98G1A2A2S14S15S1aG2S9bA2S1aS9aG1A2A2S15S1aG2Vp;A2S1aS1bVp;S6eVn;A1A2G1A2A2A2A2A2A2F_;F_;Fz;").
Proof.
  intros z Hz NZ.
  assert (HZ : (z = 1 \/ z = 2 \/ z = 3 \/ (z = 4 /\ In 4 ZU))%nat).
  { pose proof (HZU z Hz). destruct z as [|[|[|[|[|z]]]]]; try lia. do 3 right. split; [reflexivity | exact Hz]. }
  pose proof (topG_range G) as ACV.
  pose proof (geomF A rho tp md n HA t) as (T1 & T2 & _ & C1 & C2 & S1 & S2 & _ & _ & _ & TC & TR & TI & CI & TB & CB).
  pose proof (blkF_geom A rho tp md p n HA HL HCL) as (B1 & _ & B3 & B4 & BT & BC & BN & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & _).
  rewrite kSpaceSize_val in S2. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, HIGH_SHADOW_END, IMG_LO, IMG_HI, LOW_SHADOW_BEG in *. fold G in T1, T2, C1, C2, S1, S2, TC, TR, TI, CI, TB, CB, B4, BT, BC.
  destruct HZ as [-> |[-> |[-> |[-> H4]]]]; cbn [zbF zloF zhiF].
  - clear -T1 T2 TI TB BT N1 B3. lia.
  - clear -C1 C2 CI CB BC N1 B3. lia.
  - clear -B1 B3 B4 N1 ACV. lia.
  - destruct (Q4facts H4) as (_ & _ & BP' & BS1 & BS2). rewrite kSpaceSize_val in BS2. clear -BS1 BS2 BP' S1 S2 N1 B3. lia.
Qed.
Lemma zone_of_inzC : ltac2:(tb__ "0|2|
S24S33S34Vrho1;VzbF;S50S4fVZU;R2R1A7S13S5S51R2A1S6A3S1cSbS0S0S29Vrho1;R4A2M0A3ScS0S0G0A3A2S3eS40VG;A1Vp;S6eVn;A1SbS0S0S29Vrho1;R5A2M1A3ScS0S0G1A3A5F_;F_;F_;Fd;Fo;").
Proof.
  intros o [[z lo] hi] (HU & L1 & L2 & R) Hi NE. unfold img_okb in Hi. unfold zone_ok.
  destruct R as [R|[R1 R2]]; [lia|]. split; [lia|].
  destruct (Nat.eqb_spec z 0) as [->|NZ].
  - left. cbn [zbF zloF zhiF] in *. repeat (apply andb_prop in Hi as [Hi ?X]).
    repeat match goal with H : (_ || _) = true |- _ => apply Bool.orb_prop in H | H : (_ <=? _) = true |- _ => apply Z.leb_le in H end.
    all: repeat match goal with H : (_ <=? _) = true \/ _ |- _ => destruct H as [H|H] | H : (_ <=? _) = true |- _ => apply Z.leb_le in H end.
    all: lia.
  - right. destruct (zfactsC z HU NZ) as (F1 & F2 & F3 & F4 & F5). repeat split; lia.
Qed.
Theorem carve_G : ltac2:(tb__ "0|0|
S4cS17S3cVrho1;A1SaS17S3bVNV;A3A3").
Proof. apply Forall_app. split; [exact (carve_NRT A rho tp md p n HA HL HCL Hii Hp12 t Ht jv Hjv) | exact HCARVE]. Qed.
Theorem zone_G : ltac2:(tb__ "0|0|
S4cS17S3dVrho1;S40VG;A1Vp;S6eVn;A1A4SaS17S3bVNV;A3A3").
Proof.
  pose proof inz_G as HF2. destruct HCHK as (_ & Himg & Hne & _).
  apply Forall_forall. intros k Hk.
  destruct (Forall2_In_l _ _ _ (carve_obj k) HF2 (in_map _ _ _ Hk)) as (d & Hd & Hin).
  pose proof (proj1 (forallb_forall _ _) Himg d Hd) as Hi. pose proof (proj1 (forallb_forall _ _) Hne k Hk) as Hn.
  pose proof (proj1 (Forall_forall _ _) carve_G k Hk) as Ck.
  destruct k as [[[base lo] hi] cs]. unfold spec_zone. unfold spec_ne in Hn. apply Z.ltb_lt in Hn. unfold carve_ok in Ck. destruct Ck as (C1 & C2 & C3 & _).
  pose proof (zone_of_inzC _ d Hin Hi) as ZZ. cbn [carve_obj] in ZZ. unfold carved in ZZ. rewrite obj_range_mk in ZZ by lia. cbn [fst snd] in ZZ.
  apply ZZ. lia.
Qed.

Theorem nfs_zoneG : ltac2:(tb__ "0|1|
S17S37S17R1SaS17S3bVNV;A3A3S0S14S1aSbS0S0S29Vrho1;S18R3A1A2M0A3R1A2S1cR1ScS0S0G0A3A2A2S73VA;R2A2F_;Fa;F_;Fk;").
Proof.
  intros k Hk a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.zoneF. cbn zeta.
  destruct (Forall2_In_l _ _ _ (carve_obj k) inz_G (in_map carve_obj _ _ Hk)) as (d & Hd & IZ).
  pose proof (proj1 (forallb_forall _ _) (proj2 (proj2 (proj2 HCHK))) d Hd) as OKd.
  destruct d as [ [z lo] hi]. unfold in_zone in IZ. destruct IZ as (HU & L1 & L2 & R). destruct R as [R|[R1 R2]]; [lia|].
  assert (Z5 : (z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4)%nat) by (pose proof (HZU z HU); lia).
  destruct Z5 as [-> | [-> | [-> | [-> | ->] ] ] ]; cbn [zloF zhiF] in L1, L2; cbn [zbF] in R1, R2.
  - unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.img_okD in OKd. cbn [Nat.eqb] in OKd. apply andb_prop in OKd as [OK1 OK3]. apply andb_prop in OK1 as [OK1 OK2].
    apply Z.leb_le in OK1, OK2. left. split; [lia|]. apply Bool.orb_prop in OK3 as [OK3|OK3]; apply Z.leb_le in OK3; lia.
  - right. left. unfold G in *. lia.
  - right. right. left. unfold G in *. lia.
  - apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.chunk_zoneF A rho tp md p n a HA HL : (fun P => P) _). pose proof (N8_facts n) as NF. destruct (blkF_geom A rho tp md p n HA HL HCL) as (_ & _ & N1 & _). specialize (NF N1). lia.
  - destruct (Q4facts HU) as (_ & _ & _ & S1 & S2). unfold qbF in *. do 3 right. left. unfold G in *. lia.
Qed.

Definition rd_okG (nW : nat) (o : sobj) : bool := ltac2:(tb__ "0|1|
SdSdSdSdS39S24S75Vo;A1M0S4dS17S24S18SaS17S3bVNV;A3A4A3S75Vo;S91A2A2S75Vo;S90A2A2S76Vo;A1A2S39S24G0S7eS77VnW;A1A1A3A2").
Variable rr : valuation.
Hypothesis HRW : ltac2:(tb__ "0|0|
S1S13S5S60R1A1S6A3S13S49Q40A1S25Vrr;R2A2S25Vrho1;R2A2A3F_;Fi;").
Hypothesis HRL : ltac2:(tb__ "0|0|
S1S13S8S49Q8A1A1S2cVrr;R1A2S2cVrho1;R1A2A3Fl;").
Hypothesis HON : ltac2:(tb__ "0|0|
S13S5S36S17S8bS60A1SaS17S3bVNV;A3A3S6A3").
Theorem rd_zoneG : ltac2:(tb__ "0|1|
S2S2aS2dS5eVrr;R1A3S7bVA;R2A2S1aS4aQ40S25R3S78A2A2S1dS7aA1A2S4cS26S2bR4A1S79S77R5A1A1A3S24S13S5Sa2R7R1A2S6A3S13S5S74S5eR2A2S6A3S0S14S1aSbS0S0S29R9R4A2M0A3R1A2S1cR1ScS0S0G0A3A2A2S73VA;R2A2F_;Fa;F_;F_;Fo;F_;F_;F_;F_;FrhoE;FnW;").
Proof.
  intros nW rhoE HAG HTOP HDEP HCH o Hok Hb a Ha. rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.rng_below_agree GW rr rhoE o HAG Hb) in Ha.
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.BNDz A rho tp md p n HA HL HCL t Ht) as (B1 & B2 & B3 & B4 & B5). unfold blk_geo in B1.
  unfold rd_okG in Hok. apply Bool.orb_prop in Hok as [Hok|Hok]; [apply Bool.orb_prop in Hok as [Hok|Hok]; [apply Bool.orb_prop in Hok as [Hok|Hok]; [apply Bool.orb_prop in Hok as [Hok|Hok]|]|]|].
  - apply existsb_exists in Hok as (o' & Ho' & Hs). rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.same_rng_range rr o o' Hs) in Ha.
    apply in_map_iff in Ho' as (k & <- & Hk). rewrite (carve_range_on offp rho1 rr HRW HRL k (proj1 (forallb_forall _ _) HON k Hk)) in Ha. exact (nfs_zoneG k Hk a Ha).
  - rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.same_rng_range rr o O_sh Hok), (obj_range_on offp rho1 rr HRW HRL O_sh eq_refl) in Ha.
    change (obj_range rho1 O_sh) with (obj_range (rhoF_of A rho p n t jv) O_sh) in Ha. rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.R_sh1 A rho tp md p n HA HL HCL Hp12 t jv Ht) in Ha. cbn [fst snd] in Ha.
    unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.zoneF. cbn zeta. do 5 right. left.
    pose proof (Sh_in_band p ltac:(unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1; lia)) as S1. pose proof (Sh_in_band (p + N8 n) ltac:(unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1; lia)) as S2.
    assert (S3 : Sh p + N8 n / 8 <= Sh (p + N8 n)).
    { unfold Sh. pose proof (N8_facts n B2) as (_ & _ & _ & N4). rewrite <- N4 at 2. rewrite Z.div_add by lia. lia. }
    lia.
  - rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.same_rng_range rr o O_blkN Hok), (obj_range_on offp rho1 rr HRW HRL O_blkN eq_refl) in Ha.
    change (obj_range rho1 O_blkN) with (obj_range (rhoF_of A rho p n t jv) O_blkN) in Ha. rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.R_blk1 A rho tp md p n HA HL HCL Hp12 t jv Ht) in Ha. cbn [fst snd] in Ha.
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.chunk_zoneF A rho tp md p n a HA HL). lia.
  - unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.winpb in Hok. destruct o as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in Hok.
    destruct ob as [| v | | | | | | ]; try discriminate. destruct v as [v|v|]; try discriminate. do 3 (destruct v as [v|v|]; try discriminate).
    destruct olo as [lo| | | | | | | ]; try discriminate. destruct ohi as [hi| | | | | | | ]; try discriminate.
    apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [H1 H2]. apply Z.leb_le in H1, H2, H3. unfold free_depth in *.
    rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha.
    assert (E10 : rw rr 10%positive = rw rhoE 10%positive) by (apply (proj1 HAG); unfold GW; lia). rewrite E10 in Ha.
    unfold top_high in HTOP. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.zoneF. cbn zeta. do 6 right. lia.
  - apply existsb_exists in Hok as (o' & Ho' & Hs). rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.same_rng_range rr o o' Hs) in Ha.
    assert (LNK : Forall (fun o => bv_unsigned (rw rhoE 10%positive) + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs (Wcan nW))).
    { unfold unwind_objs. destruct (Wcan nW) as [|l W'] eqn:EW; [constructor|].
      unfold chain_pre in HCH. cbn [app] in HCH.
      pose proof (Forall_inv HCH) as C0. pose proof (Forall_inv (Forall_inv_tail HCH)) as C1.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HCH))) as C2. do 3 apply Forall_inv_tail in HCH.
      cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
      pose proof (urange (rw rhoE 10%positive)). rewrite Z.mod_small in C1 by lia.
      eapply Forall_impl; [|apply (chain_facts_bases rhoE (SVar 28) (l :: W') HCH); cbn [eval]; lia].
      intros o0 (B & L & Hh). cbn [eval] in B. repeat split; try assumption; lia. }
    pose proof (proj1 (Forall_forall _ _) LNK o' Ho') as (L1 & L2 & L3).
    assert (WF' : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.rng_below GW o' = true).
    { unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.rng_below in Hb |- *. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.same_rng in Hs. apply andb_prop in Hs as [Hs S3]. apply andb_prop in Hs as [S1 S2].
      apply sv_eqb_sound in S1, S2, S3. rewrite <- S1, <- S2, <- S3. exact Hb. }
    rewrite <- (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.rng_below_agree GW rr rhoE o' HAG WF') in Ha.
    destruct o' as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in L1, L2, L3. subst olo ohi. rewrite obj_range_mk in Ha by lia. cbn [fst snd] in Ha.
    unfold top_high in HTOP. unfold free_depth in HDEP. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.zoneF. cbn zeta. do 6 right. lia.
Qed.
End VARIANT.

Lemma room24 : ltac2:(tb__ "0|2|
S13S8S0A1S52VA;A1S9S0A1A3S13S5S9fZ18M0Sa5VA;G0A2M1A2S6A3S1aS1bS47G1A1S9dA2Sa4G0A1A2F_;F_;").
Proof.
  intros HC0. pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & HQR & _).
  destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.PrimRoom.quarantine_counts _ A HQR) as (Q1 & Q2 & Q3 & Q4).
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.RefillCL.rfacts_room A rho tp md 24 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC.AInvA_QC A rho tp md HA) ltac:(lia) HC0).
  exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.RefillCL.q_ids_bound_of_counts A 24 ltac:(lia) Q1 Q2 Q3 Q4).
Qed.
Lemma cnt24R : ltac2:(tb__ "0|0|
S13S8S0A1S52VA;A1S9S0A1A3S13S0S55S9eVA;Z18A2A1Z1A3F_;").
Proof.
  intros HC0. pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & HPR & _ & HQR & _).
  destruct HPR as (PL & _ & _ & PC). pose proof (PC 24 ltac:(lia)) as P24.
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP.entry_cls_pure _ A 24 ltac:(lia) HG P24 HQR) as CP.
  destruct (refill_pure 24 _ _ ltac:(lia) CP HC0 (room24 HC0)) as (_ & K).
  unfold cnt24, cache24, refillA, nthZ. cbn [aa_cls]. change (Z.to_nat 24) with 24%nat. rewrite nth_list_upd_same by (rewrite PL; lia).
  unfold nthZ in K. change (Z.to_nat 24) with 24%nat in K. rewrite K. reflexivity.
Qed.

Section CF.
Variable f : bool.
Hypothesis QC : qcondCx f A.
Lemma HC0 : cache24 A = []. Proof. exact (proj2 QC). Qed.
Lemma carve_NVC : ltac2:(tb__ "0|0|
S4cS17S3cVrho1;A1S5fVf;A1A3").
Proof.
  destruct carve_inst as [CI1 CI2]. pose proof (carve_pcc HC0) as CP. destruct QC as [QT _]. unfold NVC. destruct f.
  - destruct QT as [HNE HK]. repeat apply Forall_cons; try apply Forall_nil; try assumption.
    + exact (carve_cQ A rho tp md p n HA HL t Ht jv Hjv HNE).
    + exact (carve_bhf A rho tp md p n HA HL t Ht jv Hjv HNE HK).
  - repeat apply Forall_cons; try apply Forall_nil; try assumption.
    exact (carve_cQe A rho tp md p n HA HL t Ht jv Hjv QT).
Qed.
Lemma inz_NVC : ltac2:(tb__ "0|0|
S38S24S33S34Vrho1;VzbF;S50S4fS61Vf;A1A5S4dS17S24S18S5fVf;A1A4S67Vf;A1A5").
Proof.
  pose proof (topG_range G) as ACV. pose proof geoT as (T1 & T2 & _ & T4). assert (EQ : bv_unsigned (eval rho1 cQ) = ag_thread G + 80) by exact (E_cQ A rho tp md p n HA t Ht jv). pose proof EcA1 as EA.
  assert (HB : aa_q_thread A <> [] -> bv_unsigned (eval rho1 vQB) = qbF /\ HIGH_SHADOW_END <= qbF /\ qbF + kQuarantineBatchSize <= 140737479966720).
  { intros HNE. pose proof (qF A rho tp md p n HA HL) as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & _ & _ & QL).
    destruct (QL HNE) as (_ & _ & _ & _ & _ & _ & _ & _ & BS1 & BS2 & _). clear QL.
    pose proof (geomF A rho tp md n HA t) as (_ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2, BS2. fold G in S1, S2, BS1, BS2.
    unfold qbF, lastq, HIGH_SHADOW_END, kQuarantineBatchSize in *. change (eval rho1 vQB) with (eval (rhoF_of A rho p n t jv) vQB). rewrite (E_vQB A rho p n t jv Hjv HNE). unfold lastq. rewrite u64_lit by lia. repeat split; lia. }
  destruct QC as [QT _]. unfold NVC, ZD_NVC, ZUC, K_qc, K_qce, K_bhf, K_pcc, K_i1, K_i2. destruct f; cbn [map carve_obj].
  - destruct QT as [HNE HK]. destruct (HB HNE) as (EB & Q1 & Q2). unfold kQuarantineBatchSize, HIGH_SHADOW_END in *.
    repeat apply Forall2_cons; try apply Forall2_nil.
    all: unfold in_zone; split; [cbn; tauto | split; [cbn; lia | split; [cbn; lia | right]]].
    all: unfold carved; rewrite obj_range_mk by lia; cbn [fst snd zbF]; rewrite ?EQ, ?EB, ?EA; cbn [eval]; rewrite ?u64_lit by lia; unfold G in *; lia.
  - repeat apply Forall2_cons; try apply Forall2_nil.
    all: unfold in_zone; split; [cbn; tauto | split; [cbn; lia | split; [cbn; lia | right]]].
    all: unfold carved; rewrite obj_range_mk by lia; cbn [fst snd zbF]; rewrite ?EQ, ?EA; cbn [eval]; rewrite ?u64_lit by lia; unfold G in *; lia.
Qed.
Lemma ZUC_le : ltac2:(tb__ "0|0|
S2S37S2R1S61Vf;A1A3S5dR2U4A2F_;Fz;"). Proof. intros z Hz. unfold ZUC in Hz. destruct f; cbn in Hz; lia. Qed.
Lemma ZUC_4 : ltac2:(tb__ "0|0|
S37S2U4S61Vf;A1A3S16S13S8S3fA1S41VA;A1S9S3fA1A3A1F_;").
Proof. intros H4. destruct QC as [QT _]. unfold ZUC in H4. destruct f; [exact (proj1 QT) | cbn in H4; exfalso; lia]. Qed.
Lemma ZUC_03 : ltac2:(tb__ "0|0|
S2S5dR1U3A2S37S2R2S61Vf;A1A3F_;Fz;").
Proof. intros z Hz. unfold ZUC. destruct z as [|[|[|[|z]]]]; [| | | |lia]; destruct f; cbn; tauto. Qed.

Lemma holds_VFC : ltac2:(tb__ "0|0|
S4cS26S2bVrho1R;A1S66Vf;A1A3").
Proof.
  pose proof (topG_range G) as ACV. pose proof (geomF A rho tp md n HA t) as (_ & _ & _ & _ & _ & S1 & S2 & S3 & _). rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1. fold G in S1, S2, S3.
  assert (E127 : rw rho1R 127%positive = Z_to_bv 64 1) by (change (rw rho1R 127%positive) with (Z_to_bv 64 (cnt24 (refillA A 24))); rewrite (cnt24R HC0); reflexivity).
  assert (E155 : rw rho1R 155%positive = Z_to_bv 64 (ag_spacebeg G)) by reflexivity.
  assert (E120 : rw rho1R 120%positive = Z_to_bv 64 (Z.of_nat (length (aa_q_thread A)))) by reflexivity.
  assert (HFQB : Forall (holds rho1R) F_QB).
  { unfold F_QB, vPK, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states.vSB. unfold HIGH_SHADOW_END. rewrite kSpaceSize_val.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E127, ?E155, ?u64_lit by lia; try lia.
    all: split; [lia | exact S3]. }
  destruct QC as [QT _]. unfold VFC. destruct f; cbn [VFACT]; [|exact HFQB].
  destruct QT as [HNE HK]. apply Forall_app. split; [exact HFQB|].
  pose proof (qF A rho tp md p n HA HL) as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & QS & QLB & QL).
  destruct (QL HNE) as (_ & _ & _ & _ & _ & BK & _ & B16a & BS1 & BS2 & _). clear QL. unfold kQuarantineCacheMax in QS. rewrite kSpaceSize_val in BS2. fold G in BS1, BS2.
  assert (E122 : rw rho1R 122%positive = Z_to_bv 64 (qb_addr (lastq A))).
  { change (rw rho1R 122%positive) with (Z_to_bv 64 (match aa_q_thread A with [] => j_qb jv | _ => qb_addr (lastq A) end)). destruct (aa_q_thread A); [congruence | reflexivity]. }
  assert (A8 : qb_addr (lastq A) mod 8 = 0) by (unfold lastq; rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2; reflexivity); rewrite B16a; reflexivity).
  assert (LN : 0 < Z.of_nat (length (aa_q_thread A)) <= 128) by (destruct (aa_q_thread A); [congruence|]; cbn [length] in *; lia).
  assert (QB64 : 0 <= qb_addr (lastq A) < 2 ^ 64) by (unfold lastq, kQuarantineBatchSize in *; lia).
  unfold vQN. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval branch_taken]; unfold bv_eqb; rewrite ?E120, ?E122, ?u64_lit by lia; try lia.
  all: try (rewrite Z.eqb_eq; lia).
  all: split; [lia | exact A8].
Qed.

Theorem instG_here_C : ltac2:(tb__ "0|0|
S5S8S7cA1S7dS88R3Vp;Vn;A3S89R4R3R2S5fVf;A1S66Vf;A1Vrho1R;Vp;Vn;S6eVn;A1S40VG;A1AaF_;Fst;FW;Fkhi;").
Proof.
  intros khi W st HK. pose proof (topG_range G) as ACV. pose proof (blkF_geom A rho tp md p n HA HL HCL) as (B1 & B2 & B3 & B4 & _ & _ & BN & _ & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & N2 & N3 & N4).
  pose proof (blkF_mem A rho tp md p n HA HL HCL) as (t' & _ & _ & _ & _ & HSH & HPAD). unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  destruct (offp_chk f) as (OK1 & OK2 & OK3).
  pose proof (fun i Hi => pins_off i Hi) as PW.
  constructor.
  - change (rw rho1R 12%positive) with (rw rho 12%positive). rewrite <- Hp12. symmetry. apply Z_to_bv_bv_unsigned.
  - change (rw rho1R 13%positive) with (rw rho 13%positive). rewrite <- Hn13. symmetry. apply Z_to_bv_bv_unsigned.
  - reflexivity.
  - reflexivity.
  - split; [unfold blk_geo, IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact B1|]. fold G in B4. repeat split; lia.
  - apply (Forall_carve_ok_on offp rho1 rho1R PW pins_rl pins_rm _ OK1). exact (carve_G (NVC f) carve_NVC).
  - apply (Forall_spec_zone_on offp rho1 rho1R PW pins_rl _ _ _ _ OK1). exact (zone_G (NVC f) (ZD_NVC f) (ZUC f) ZUC_le ZUC_4 ZUC_03 inz_NVC (ZD_chkC f) carve_NVC).
  - apply (pd_on offp rho1 rho1R PW pins_rl _ OK1). exact (pd_G (NVC f) (ZD_NVC f) (ZUC f) ZUC_le ZUC_4 ZUC_03 inz_NVC (ZD_chkC f)).
  - intros z Hz. destruct (HSH z Hz) as [x Hx]. exists x. rewrite pins_rm0. rewrite view_in in Hx; [exact Hx|].
    unfold Sh, SHADOW_OFF in *. split; [lia|]. pose proof (Z.div_lt_upper_bound (p + N8 n) 8 (2 ^ 50) ltac:(fold G in B4; lia) ltac:(fold G in B4; lia)). pose proof (Z.div_le_mono p (p + N8 n) 8 ltac:(lia) ltac:(lia)).
    assert (N8 n / 8 <= (p + N8 n) / 8) by (apply Z.div_le_mono; lia). lia.
  - intros z Hz. destruct (HPAD z Hz) as [x Hx]. exists x. rewrite pins_rm0. rewrite view_in in Hx; [exact Hx | fold G in B4; lia].
  - apply Forall_app. split; [|apply Forall_app; split; [|apply Forall_app; split; [|exact holds_VFC]]].
    + apply (Forall_holds_on offp rho1 rho1R PW pins_rl F_geom_fn); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact (holds_geom A rho tp md p n HA t Ht jv)].
    + apply (Forall_holds_on offp rho1 rho1R PW pins_rl (tl (F_pc khi))); [destruct khi; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact (holds_p A rho tp md p n HA HL HCL Hp12 Hn13 t Ht jv khi HK)].
    + apply (Forall_holds_on offp rho1 rho1R PW pins_rl F_cas); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact (holds_cas A rho tp md p n HA HL HCL Hp12 t Ht jv)].
  - intros rho' Hag. pose proof (rig_F A rho tp md p n HA HL HCL Hp12 Hn13 t Ht jv rho') as RG.
    assert (AG1 : agree_vals NF rho' rho1).
    { destruct Hag as [Aw Al]. split; [intros i Hi; rewrite (Aw i Hi); apply pins_off; unfold offp; unfold NF in Hi; destruct (Pos.eqb_spec i 127), (Pos.eqb_spec i 130); subst; try reflexivity; lia | intros l; rewrite (Al l); apply pins_rl]. }
    destruct (RG AG1) as [_ R2 R3 R4 R5 R6 R7 R8 R9 R10].
    pose proof (pins_off 12 eq_refl) as P12. pose proof (pins_off 13 eq_refl) as P13. pose proof (pins_off 103 eq_refl) as P103. pose proof (pins_off 104 eq_refl) as P104.
    pose proof (pins_off 105 eq_refl) as P105. pose proof (pins_off 106 eq_refl) as P106. pose proof (pins_off 107 eq_refl) as P107.
    constructor; [exact Hag | | | | | | | | | ]; rewrite ?P12, ?P13, ?P103, ?P104, ?P105, ?P106, ?P107; assumption.
Qed.
End CF.

Theorem rd_zone_C : ltac2:(tb__ "0|1|
S5S6dR1VA;A2S2S2aS2dS5eVrho1R;R1A3S7bVA;R2A2S1aS4aQ40S25R3S78A2A2S1dS7aA1A2S4cS26S2bR4A1S79S77R5A1A1A3S24S13S5S8aS5fR9A1R7R1A3S6A3S13S5S74S5eR2A2S6A3S0S14S1aSbS0S0S29R9R4A2M0A3R1A2S1cR1ScS0S0G0A3A2A2S73VA;R2A2F_;Fa;F_;F_;Fo;F_;F_;F_;F_;FrhoE;FnW;F_;Ff;").
Proof.
  intros f QC.
  refine (rd_zoneG (NVC f) (ZD_NVC f) (ZUC f) _ _ _ _ (ZD_chkC f) rho1R pins_off pins_rl (proj1 (offp_chk f))).
  - first [exact (ZUC_le f QC) | exact (ZUC_le f)].
  - first [exact (ZUC_4 f QC) | exact (ZUC_4 f)].
  - first [exact (ZUC_03 f QC) | exact (ZUC_03 f)].
  - exact (inz_NVC f QC).
Qed.

Lemma ZD_chkN0 : ltac2:(tb__ "0|1|
S14S13S5S35SaS33S4eS9S33A1A3M0A1S6A3S14S13S5S36S33S51G0A3S6A3S14S13S5S36S17S53SaS17S3bS62A3A3S6A3S13S5S36S33S72G0A3S6A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma ZUN_le : ltac2:(tb__ "0|0|
S2S37S2R1S4S2U0S4S2U1S4S2U2S4S2U3S9S2A1A3A3A3A3A3S5dR2U4A2F_;Fz;"). Proof. intros z Hz. cbn in Hz. lia. Qed.
Lemma ZUN_4 : ltac2:(tb__ "0|0|
S37S2U4S4S2U0S4S2U1S4S2U2S4S2U3S9S2A1A3A3A3A3A3S16S13S8S3fA1S41VA;A1S9S3fA1A3A1F_;"). Proof. intros H4. cbn in H4. exfalso. lia. Qed.
Lemma ZUN_03 : ltac2:(tb__ "0|1|
S2S5dR1U3M0A2S37S2R2S4S2U0S4S2U1S4S2U2S4S2G0S9S2A1A3A3A3A3A3F_;Fz;"). Proof. intros z Hz. destruct z as [|[|[|[|z]]]]; cbn; try tauto. lia. Qed.
Theorem instG_here_N : ltac2:(tb__ "0|0|
S5S8S7cA1S7dS88R3Vp;Vn;A3S1cS96Vn;A2S89R5R4R3S62S6bVrho1;Vp;Vn;S6eVn;A1S40VG;A1AaF_;F_;Fst;FW;Fkhi;").
Proof.
  intros khi W st HK HBG. pose proof (topG_range G) as ACV. pose proof (blkF_geom A rho tp md p n HA HL HCL) as (B1 & B2 & B3 & B4 & _ & _ & BN & _ & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & N2 & N3 & N4).
  pose proof (blkF_mem A rho tp md p n HA HL HCL) as (t' & _ & _ & _ & _ & HSH & HPAD). unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. fold G in B4.
  assert (HIN : Forall2 (in_zone rho1 zbF zloF zhiF [0; 1; 2; 3]%nat) (map carve_obj NVN) []) by constructor.
  constructor.
  - change (rw rho1 12%positive) with (rw rho 12%positive). rewrite <- Hp12. symmetry. apply Z_to_bv_bv_unsigned.
  - change (rw rho1 13%positive) with (rw rho 13%positive). rewrite <- Hn13. symmetry. apply Z_to_bv_bv_unsigned.
  - reflexivity.
  - reflexivity.
  - split; [unfold blk_geo, IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact B1|]. repeat split; lia.
  - exact (carve_G NVN (Forall_nil _)).
  - exact (zone_G NVN [] [0; 1; 2; 3]%nat ZUN_le ZUN_4 ZUN_03 HIN ZD_chkN0 (Forall_nil _)).
  - exact (pd_G NVN [] [0; 1; 2; 3]%nat ZUN_le ZUN_4 ZUN_03 HIN ZD_chkN0).
  - intros z Hz. destruct (HSH z Hz) as [x Hx]. exists x. change (rm rho1) with (rm rho). rewrite view_in in Hx; [exact Hx|].
    unfold Sh, SHADOW_OFF in *. split; [lia|]. pose proof (Z.div_lt_upper_bound (p + N8 n) 8 (2 ^ 50) ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono p (p + N8 n) 8 ltac:(lia) ltac:(lia)).
    assert (N8 n / 8 <= (p + N8 n) / 8) by (apply Z.div_le_mono; lia). lia.
  - intros z Hz. destruct (HPAD z Hz) as [x Hx]. exists x. change (rm rho1) with (rm rho). rewrite view_in in Hx; [exact Hx | lia].
  - apply Forall_app. split; [exact (holds_geom A rho tp md p n HA t Ht jv)|]. apply Forall_app. split; [exact (holds_p A rho tp md p n HA HL HCL Hp12 Hn13 t Ht jv khi HK)|].
    apply Forall_app. split; [exact (holds_cas A rho tp md p n HA HL HCL Hp12 t Ht jv)|].
    unfold VFN, BIGF. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. change (rw rho1 13%positive) with (rw rho 13%positive). rewrite Hn13, u64_lit by (unfold kQuarantineMax; lia). exact HBG.
  - exact (rig_F A rho tp md p n HA HL HCL Hp12 Hn13 t Ht jv).
Qed.
Theorem rd_zone_N : ltac2:(tb__ "0|1|
S2S2aS2dS5eVrho1;R1A3S7bVA;R2A2S1aS4aQ40S25R3S78A2A2S1dS7aA1A2S4cS26S2bR4A1S79S77R5A1A1A3S24S13S5S8aS62R7R1A3S6A3S13S5S74S5eR2A2S6A3S0S14S1aSbS0S0S29R9R4A2M0A3R1A2S1cR1ScS0S0G0A3A2A2S73VA;R2A2F_;Fa;F_;F_;Fo;F_;F_;F_;F_;FrhoE;FnW;").
Proof.
  assert (HIN : Forall2 (in_zone rho1 zbF zloF zhiF [0; 1; 2; 3]%nat) (map carve_obj NVN) []) by constructor.
  exact (rd_zoneG NVN [] [0; 1; 2; 3]%nat ZUN_le ZUN_4 ZUN_03 HIN ZD_chkN0 rho1 (fun _ _ => eq_refl) (fun _ => eq_refl) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)).
Qed.
End FACTSC.
End F0A_instokC.

(* [comment removed for export] *)
Module F0A_masm.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "junkF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_live"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "cons"; "fst"; "nat"; "nil"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "set_inited"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_free"; "L_free"; "UStopLe"; "Wcan"; "KcA"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull"; "rt_zone2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull RebuildSM SMGlue SpineMallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma rho_sets_id : ltac2:(tb__ "0|2|
S12S14S1SfQ40A1M0A2M1A1S2S30G1G1S5G0S3R2S16S1G0R1A3A2S1aS1G0R1A3A3Liv;R2A3S5S2S32R2R3A2R2A3F_;Frho;Fl;").
Proof.
  induction l as [|[i v] t IH]; intros rho HF; [reflexivity|]. cbn [rho_sets].
  pose proof (Forall_inv HF) as H1. pose proof (Forall_inv_tail HF) as H2. cbn [fst snd] in H1.
  assert (E : rho_set_rw rho i v = rho).
  { destruct rho as [w l0 m]. unfold rho_set_rw. cbn [rw rl rm] in *. f_equal. apply functional_extensionality. intros j.
    destruct (Pos.eqb_spec j i) as [->|NE]; [symmetry; exact H1 | reflexivity]. }
  rewrite E. apply IH. exact H2.
Qed.

Lemma rhoF_of_id : ltac2:(tb__ "0|0|
ScS2S2S0S0S0SbS27S9SaR7R6R4R3R2R1A6R5A3S5S2SaS20R8A1R6R5R4R3R2A6R6A3F_;Fjv;Ft;Fn;Fp;Frho2;Frho;FA;").
Proof.
  intros A rho rho2 p n t jv [Hw _]. unfold rhoF_of at 1. apply rho_sets_id.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (rewrite <- Hw by (unfold GW; lia); reflexivity).
Qed.

Lemma mid_link_pn : ltac2:(tb__ "0|3|
ScS2S2S0S0S0SbS29R7SaR7R6R4R3R2R1A6R5A3S6S5S0S10Q40M0S3R6PcM1A2A2S10G0S3R7G1A2A2A3S5S0S10G0S3R6PdM2A2A2S10G0S3R7G2A2A2A3A2F_;Fjv;Ft;Fn;Fp;Frho2;Frho;FA;").
Proof.
  intros A rho rho2 p n t jv ([Hw _] & _). split; [rewrite <- (Hw 12%positive) by (unfold GW; lia) | rewrite <- (Hw 13%positive) by (unfold GW; lia)]; reflexivity.
Qed.

Section MASM.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S34VCST;R1A2S6S7S6S23S21R2A2S24R2S22A2A2A1S7S6S23Z17db48R2A2S24R2Z17db4cA2A2A1A2F_;Fa;").

Lemma tjv_ok_mid : ltac2:(tb__ "0|0|
ScS2S2S12SfQ40A1A1S26S0S0S0SbS1fS8R9R8R6R5A5S35S14S0S0A2S13S0S0R5R4A4SeRaA1A3S29RbSaRbRaR6R5R4R3A6R9A3S28RcRbR7R6R5R4A6S28S20RdA1RbR8R7R6R5A6F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd;Ftp;Frho2;Frho0;FA;").
Proof.
  intros A rho0 rho2 tp md p n t jv HA HL (_ & VQ & _) ((T1 & T2 & T3 & T4) & (J1 & J2 & J3 & J4 & C1 & C2 & C3)).
  pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (Hsep & _). destruct (Hsep p n HL) as (S1 & S2 & _). unfold IMG_HI in S2.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI.
  assert (Erm : rm (rhoF_of A rho0 p n t jv) = rm rho0) by reflexivity. rewrite Erm in VQ.
  assert (X : forall c, (forall k, (k < c_w c)%nat -> ~ ia_zone (c_addr c + Z.of_nat k)) -> cell_ok (view segsA (rm rho0)) c -> cell_ok (view segsA (rm rho2)) c).
  { intros c Hc Hok. eapply cell_ok_agree; [|exact Hok]. intros k Hk. apply VQ. exact (Hc k Hk). }
  unfold tjv_ok. change (aa_geom (set_inited A)) with (aa_geom A). change (aa_q_thread (set_inited A)) with (aa_q_thread A).
  split; [split; [exact T1|]; split; [exact T2|]; split|].
  - apply X; [|exact T3]. cbn [c_addr c_w]. intros k Hk. unfold ia_zone, IA_BEG, IA_END. lia.
  - apply X; [|exact T4]. cbn [c_addr c_w]. intros k Hk. unfold ia_zone, IA_BEG, IA_END. lia.
  - split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|]. split; [|split].
    + apply X; [|exact C1]. cbn [c_addr c_w]. intros k Hk. unfold ia_zone, IA_BEG, IA_END, QG. lia.
    + apply X; [|exact C2]. cbn [c_addr c_w]. intros k Hk. unfold ia_zone, IA_BEG, IA_END. lia.
    + intros HE. destruct (C3 HE) as [C3a C3b]. split; (apply X; [|assumption]); cbn [c_addr c_w]; intros k Hk; unfold ia_zone, IA_BEG, IA_END; lia.
Qed.

Lemma post_mid : ltac2:(tb__ "0|6|
S17ScS2fS2S2S12SfQ40M0A1A1M1G1S26S31S1fS8R8R6R3R2A5S27S1bR7R6A3S0S6S23Z0R1A2S24R1S25Z2Z40A2A2A2S7S33SdRcA1R2A2A1S5S19SfQ8A1A1S4RaS11G0R3A2M2A2S4RbG2A2A3F_;F_;Fa;S1eS8S1bR8R7S15S14S1cS1dA2M3S13S1cS1dS2cS2aS2eRcA1S2dA3S2bS1fS8A1M4VCST;VXGL;S20RbA1RaA5A4S18G3A1M5A3R4A6S1eS8S1bRaR8S15G3S13S1cS1dS2cS2aS2eRdA1S2dA3S2bG4VCST;VXGL;RcRbA5A4G5A3R5A6F_;F_;F_;F_;Fw;Fmd0;Ftp0;Ftp;Frho2;Frho0;FKc;FA;FnW;").
Proof.
  intros nW A Kc rho0 rho2 tp tp0 md0 w HA0 [AGw AGl] RMO (L & JL & rho' & tp' & Hin & [Hw' Hl'] & Hsm & HJL).
  destruct Hin as [E|[]]. injection E as <- <-.
  pose proof HA0 as (HG & _ & HF & HRest & _). pose proof (proj1 HRest) as Hsep.
  exists (L_free AE_A (Wcan nW) UStopLe), (JL_free (AInvA segsA) CST XGL A Kc), rho', tp'.
  split; [left; reflexivity|]. split; [split; [intros i Hi; rewrite (AGw i Hi); exact (Hw' i Hi) | intros l; rewrite (AGl l); exact (Hl' l)]|]. split; [exact Hsm|].
  destruct HJL as (A' & l1 & l2 & HA' & ELV & ELV' & EF & EV & EKm & EKf & EG & MK & HKc & CK).
  exists A', l1, l2. split; [exact HA'|].
  split; [rewrite (AGw 12%positive) by (unfold NF; lia); rewrite (AGw 13%positive) by (unfold NF; lia); exact ELV|].
  split; [exact ELV'|]. split; [exact EF|]. split; [exact EV|]. split; [exact EKm|]. split; [exact EKf|]. split; [exact EG|].
  split; [|split; [exact HKc | exact CK]].
  destruct MK as [MK1 MK2]. change (client_addrA CST (set_inited A)) with (client_addrA CST A) in MK1, MK2.
  change (client_shadowA CST XGL (set_inited A)) with (client_shadowA CST XGL A) in MK1.
  split.
  - intros a Ba Hcl.
    assert (NZ : ~ rt_zone2 (aa_geom A) a).
    { destruct Hcl as [[C1 _]|[C1 _]]; [exact (client_not_rt2 CST HCST HCST2 A a _ HG HF Hsep C1)|].
      pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B. exact (shadow_not_rt2 A a HG B). }
    rewrite <- (RMO a Ba NZ). apply MK1; [exact Ba|].
    destruct Hcl as [H1|(H1 & H2 & H3)]; [left; exact H1 | right; split; [exact H1|]; split; [exact H2|]; rewrite (RMO a Ba NZ); exact H3].
  - intros x j Hx Hj Hdef. apply (MK2 x j Hx Hj).
    assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
    { destruct Hx as [[C1 C2]|GX].
      - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. lia.
      - destruct (HXGL x GX). unfold IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. lia. }
    unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
    destruct (word_byte_range (Sh x) j ltac:(lia) Hj) as (W1 & W2 & W3).
    unfold word_byte in *. rewrite RMO; [exact Hdef | lia |].
    apply (shadow_not_rt2 A _ HG). lia.
Qed.
End MASM.
End F0A_masm.

(* [comment removed for export] *)
Module F0A_hbN_stepU.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "rm"; "valuation"; "holds"; "sprop"; "ss_objs"; "agree_below"; "eval"; "rw"; "ss_facts"; "@Corelib.Init.Datatypes"; "nat"; "list"; "pair"; "prod"; "length"; "app"; "bool"; "option"; "true"; "@Corelib.Numbers.BinNums"; "positive"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue"; "dspec"; "dobj"; "keepN"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_hbN_zones"; "in_zoneW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib"; "s_C"; "s_bs"; "s_Cd"; "s_F"; "s_M"; "s_N"; "s_T"; "s_ZDn"; "s_ZDo"; "s_k"; "s_okU"; "strans"; "unk_ok"; "uobj"; "@Stdlib.Lists.List"; "Forall2"; "In"; "combine"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.F0A_hbN_step"; "ro_condW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip"; "carve_okq"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 SegQS_lib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_hbN_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.F0A_hbN_step.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section StepUW.
Variables (Zn TZ : Z -> Prop).
Variable J : jpredA.
Hypothesis HST : ltac2:(tb__ "0|0|
S28S5S2dVJ;A3").
Let JWn : jpredA := ltac2:(tb__ "0|0|
S45S5VZn;VTZ;VJ;A4").
Variables (zb zlo zhi : nat -> Z) (ZU : list nat).
Hypothesis Hsep : ltac2:(tb__ "0|3|
S11S11S3dS11R2VZU;A3M0G0S3S1S11R4R3A3A1S4S23S22Vzb;R5A1M1Vzhi;R5A1A2S22Vzb;R4A1M2Vzlo;R4A1A2A2S23S22G2Vzhi;R4A1A2S22G1Vzlo;R5A1A2A2A2F_;F_;F_;Fz';Fz;").

Lemma s_stepUW : ltac2:(tb__ "0|8|
S39S14S14S7S7A2S7A2S24S12S1fA1S12S3fQ40A1M0A1M1S9G1S12S42A1M2S40S41S1S17S38RaR9R8A3S19A3S1S12S6A1ScS29S2eRbA1M3A1A1S16S6S21G3S37RbA1A2S1cS1fS6S20R8A4A3A3S1S11S15G0R8A2S15S1aS2fRcA1A2A3S27S5VJWn;S2eRdA1R8R7S13G2S25R6S26R5R4A2A4A6S1bS1fS46VTZ;R9A2RbA3S43RaS1cS1fS6S20RcA4S44R6R9R7A3A3S9S47R1S3eS1aG0S2fR10A1RcA4A2S9S1S1eS1dS5S8R2A1A2S1dS5S8RcA1A2A3VJWn;R2RcRbR9A4S0S3aR3R12A2S0S1bS2aS48R3A1S33R13A1M4A3S0S2cR3Vzb;Vzlo;Vzhi;VZU;S3bR12A1R11A7S0S3cS6S24S2cR3Vzb;Vzlo;Vzhi;VZU;A5M5S1cS2aS6S2bG4A4S35R13A1A5S0S3cS6S24G5ScS29S30R13A1A1M6A1S36R13A1A5S1bSbSaR3A1S10G6A1A3S1bSbSaR4A1S31R14A1A3F_;A2A2A2A2A2F_;F_;S2S9S9S0S27S5VJWn;S34R13A1R1RdS13G2S25RcS26RbRaA2A4A6S0S1aS7S3dS14S1aS7A2S13S1aS7R2R1A4S32R15A1A3S1G0SfR4R3A2SeR6R2A2A3F_;Fe;Fv;S0S1G0S18S3fQ8A1A1F_;S8R1A1S8R4A1M7A3S0SdS2dR3R1A3S1S1eS1dS5G7A2S1dS5S8ReA1A2A3A2A2A2A2Lrho5;A2F_;Trho4;Trho3;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fvals;FdsD;Fzdu;Fu;Ft;").
Proof.
  intros t u zdu dsD vals rho tp tr ms md HOK HOBJ HLEN HS HDC rho3 rho4 HCONT.
  pose proof (JW_stable segsA NPRE Zn TZ J HST) as HSTW. fold JWn in HSTW.
  unfold s_okU in HOK. repeat (apply andb_prop in HOK as [HOK ?]).
  match goal with H : forallb (zdisjb zdu) _ = true |- _ => rename H into OKZU end.
  match goal with H : forallb (fun d => forallb _ _) _ = true |- _ => rename H into OKZX end.
  match goal with H : zcheck _ = true |- _ => rename H into OKZC end.
  match goal with H : entsM _ _ _ = true |- _ => rename H into OKENT end.
  match goal with H : forallb (sprop_below _) _ = true |- _ => rename H into OKBEL end.
  match goal with H : swf (with_objs _ [uobj u]) = true |- _ => rename H into OKSWF1 end.
  match goal with H : swf (with_objs _ (map carve_obj _)) = true |- _ => rename H into OKSWF2 end.
  match goal with H : forallb _ (s_bs t) = true |- _ => rename H into OKBS end.
  match goal with H : sv_vars_all _ _ = true |- _ => rename H into OKV2 end.
  match goal with H : state_vars_all _ _ = true |- _ => rename H into OKV1 end.
  assert (HX : ax_X (s_C t) = []) by (destruct (ax_X (s_C t)); [reflexivity | discriminate HOK]).
  destruct (ro_dissolveW Zn TZ J (s_C t) (keepN (s_C t) (s_k t)) dsD rho tp tr ms md HOBJ HS HDC) as (H1 & RW3 & RL3 & EV).
  fold rho3 in H1, RW3, RL3, EV. change (SPA segsA JWn (s_Cd t) rho3 tp (tr, mkCfg ms md)) in H1.
  assert (MF : map fst (combine (s_bs t) vals) = s_bs t).
  { clear - HLEN. revert vals HLEN. induction (s_bs t) as [|b r IH]; intros vals HLEN; destruct vals as [|x vs]; cbn in *; try reflexivity; try discriminate. f_equal. apply IH. lia. }
  assert (H2 : SPA segsA JWn (s_Cd t) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_bindV segsA _ NPRE (s_Cd t) rho3 tp _ _ HX HSTW); [| rewrite MF; exact OKV1 | rewrite MF; exact OKV2 | exact H1].
    intros v Hv. rewrite MF in Hv. pose proof (proj1 (forallb_forall _ _) OKBS v Hv) as X. apply Pos.leb_le. exact X. }
  destruct (HCONT EV (proj2 H2)) as (UOK & CC & ZUo & ZN & ZO & HFN).
  pose proof (SPA_facts_hold segsA _ rho4 (s_Cd t) tp _ H2) as HFa.
  destruct u as [[ub ulo] uhi]. cbn [uobj unk_ok] in *. destruct UOK as (U1 & U2 & U3 & U4 & U5).
  assert (H2u : SPA segsA JWn (s_Cu t (ub, ulo, uhi)) rho4 tp (tr, mkCfg ms md)).
  { pose proof (SPA_carve_unk segsA JWn rho4 (s_Cd t) tp (tr, mkCfg ms md) ub ulo uhi (ss_next (ax_S (s_Cd t))) H2) as Y. cbn zeta in Y. apply Y; clear Y.
    - exact OKSWF1.
    - apply Pos.le_refl.
    - exact U1.
    - exact U2.
    - exact U3.
    - exact U4.
    - pose proof (zonesW_cross rho4 zb zlo zhi ZU Hsep [mkObj ub ulo uhi [] DUnknown] [zdu] _ _ (Forall2_cons _ _ ZUo (Forall2_nil _)) ZO ltac:(cbn [forallb]; rewrite OKZU; reflexivity)) as ZC.
      apply Forall_cons_iff in ZC as [ZC _]. exact ZC.
    - exact U5.
    - assert (HXd : ax_X (s_Cd t) = []) by exact HX. intros rr y j Hin. rewrite HXd in Hin. destruct Hin. }
  assert (H3 : SPA segsA JWn (s_CaU t (ub, ulo, uhi)) rho4 tp (tr, mkCfg ms md)).
  { pose proof (SPA_carve_list segsA JWn rho4 (s_Cu t (ub, ulo, uhi)) tp _ (s_N t) (ss_next (ax_S (s_Cu t (ub, ulo, uhi)))) H2u) as Y. cbn zeta in Y. apply Y; clear Y.
    - exact OKSWF2.
    - apply Pos.le_refl.
    - apply carve_okq_list; [exact HX | exact CC].
    - apply (zonesW_cross rho4 zb zlo zhi ZU Hsep _ _ (ss_objs (ax_S (s_Cd t)) ++ [mkObj ub ulo uhi [] DUnknown]) (s_ZDo t ++ [zdu]) ZN); [|exact OKZX]. apply Forall2_app; [exact ZO | exact (Forall2_cons _ _ ZUo (Forall2_nil _))].
    - exact (zonesW_pd rho4 zb zlo zhi ZU Hsep _ _ ZN OKZC). }
  assert (H4 : SPA segsA JWn (s_CcU t (ub, ulo, uhi)) rho4 tp (tr, mkCfg ms md)).
  { unfold s_CcU, addF. apply SPA_refacts; [exact H3 | exact OKBEL |]. intros HF4. apply Forall_app. split; [exact HF4 | apply HFN; exact HFa]. }
  destruct (entM_SPA JWn _ (s_T t) (s_M t) rho4 tp _ OKENT HSTW H4) as (H5 & AG5 & V5 & RM5).
  eexists. split; [exact H5|]. split; [exact V5|]. split; [|split; [exact AG5 | exact EV]]. rewrite RM5. unfold rho4. apply rm_rho_sets.
Qed.
End StepUW.
End F0A_hbN_stepU.

(* [comment removed for export] *)
Module F0T_asm.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "Some"; "nil"; "option"; "pair"; "prod"; "cons"; "length"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "AE_A"; "KcA"; "UStopLe"; "ulink"; "ustop"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sv"; "swf"; "sprop"; "SLit"; "SVar"; "sprop_below"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "HBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_stack_top"; "topG"; "aa_Kf"; "aa_Km"; "aa_internal_inited"; "budget_ok_free"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "NV"; "instF_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "J_free_tol_preT"; "JT"; "objs_le"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "VFACT"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG"; "sa_t"; "sb_t"; "sc_t"; "sd_t"; "se_t"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "P0T_c"; "FACTS_Tg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm"; "entry_pureF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "cls_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "instG_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_asm"; "geomT_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition geomT_stmt : Prop := ltac2:(tb__ "0|2|
S20S13S0S28Q40A1A1S41S4fS1cR4R3R2R1A5SbS31Z1S22S21R5A1M0A1M1A2S31G1S1fS23G0A1A1A2A2F_;Fmd;Ftp;Frho;FA;").

Lemma entry_budget_T : ltac2:(tb__ "0|0|
S20SeS13S0S28Q40A1A1S2bS1dS1cS2eR5R4A2S1eSdA1R3R2R1A6S27R6A1F_;Fw;Ftp;Frho;FKc;FA;").
Proof. intros A Kc rho tp w [_ [HJ _]]. destruct HJ as (_ & _ & _ & _ & _ & HB & _). exact HB. Qed.
Lemma entry_KM_T : ltac2:(tb__ "0|0|
S20SeS13S0S28Q40A1A1S2bS1dS1cS2eR5R4A2S1eSdA1R3R2R1A6S31S32S25R6A1S24R6A1A2S45A2F_;Fw;Ftp;Frho;FKc;FA;").
Proof. intros A Kc rho tp w [_ [_ [HK _]]]. exact HK. Qed.
Lemma entry_pure_T : ltac2:(tb__ "0|1|
S1S34S20SeS13S0S28Q40M0A1A1S2bS49R7S29G0S14R3PcA2A2S29G0S14R3PdA2A2A3SaS1S26R6A1S2A3S39R8R7A2S1dS1cS2eR8R7A2S1eSdA1R6R5R4A6S48RbScU0A1SfRaR9R7A6F_;F_;F_;F_;Fw;Ftp;Frho;FKc;FA;Fq;Fkhi;").
Proof.
  intros khi q A Kc rho tp w HHI Hii QC [_ [HJ _]]. destruct HJ as (HA & _ & HL & _).
  split; [exact HL|]. split; [exists tp, (cfg_model (w_cfg w)); exact HA|].
  exact (instF_facts_ok3 khi (Wcan 0) UStopLe q A rho tp _ _ _ HA HL HHI Hii QC eq_refl eq_refl).
Qed.
Lemma entry_geom_T : ltac2:(tb__ "0|2|
S4eS20SeS13S0S28Q40A1A1S2bS1dS1cS2eR5R4A2S1eSdA1R3R2R1A6SbS31Z1S22S21R6A1M0A1M1A2S31G1S1fS23G0A1A1A2A2F_;Fw;Ftp;Frho;FKc;FA;F_;").
Proof. intros HG A Kc rho tp w [_ [HJ _]]. destruct HJ as (HA & _). exact (HG A rho tp _ HA). Qed.

Lemma instG_of_F : ltac2:(tb__ "0|0|
S1S0S10A1S11S34S13S12S12S12S12S2dR9R8R7R6R5R4R3R2R1A9S4bRaScU0A1SfS2cR7A1S33R7A1R6R5R4R3R2AaF_;Ftop;Fn8;Fn;Fp;Frho1;Fq;Fst;FW;Fkhi;").
Proof. intros khi W st q rho1 p n n8 top [X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12]. constructor; assumption. Qed.

Section TQ.
Variable khi : bool. Variable q : qvar.
Hypothesis Wa : ltac2:(tb__ "0|0|
SaS1S16S3aScU0A1A1A1S2A3").
Hypothesis Da : ltac2:(tb__ "0|4|
SaS5S7S0S7S15S15A2M0A1M1S0S17A1M2A2M3A1S42S35S1eSdA1A1S3aScU0A1A1A2S3G3S6G1G2S8G0S6S15S15S19P18A1S18S47A1A4S4G0A1A3S4S17A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
SaS1S16S3bScU0A1S2cVq;A1A2A1S2A3").
Hypothesis Wc : ltac2:(tb__ "0|0|
SaS1S16S3cScU0A1S2cVq;A1A2A1S2A3").
Hypothesis Wd : ltac2:(tb__ "0|0|
SaS1S16S3dScU0A1S2cVq;A1A2A1S2A3").
Hypothesis Fe : ltac2:(tb__ "0|0|
SaS1S50S17S1aS46A1S40Vkhi;S33Vq;A1A2A3S2A3").
Hypothesis AXI : ltac2:(tb__ "0|2|
SaS5S36A1S43S3eVkhi;ScU0M0A1S2cVq;A1M1S33Vq;A1A4S4aG0S9S44G1A2A2A2S3S36S3fVkhi;Vq;A2A2A3").

Theorem tq_instantiate : ltac2:(tb__ "0|4|
S20SeS13S0S28Q40M0A1M1A1S2bS12S12S12S38S2dVkhi;ScU0A1SfVq;S37R9R7R4R3R2R1A6R4R3S4cR3A1S23S21R9A1A1A9S1dS1cS2eRaR9A2S1eSdA1R8R7R6A6SbS4dR9S37RbR9R6R5R4R3A6M2A2SbS1dS1cS2fRbRaG2A3S3fVkhi;Vq;A2M3G2R8R7A6SbS30G2S29G0S14G2PaA2A2S1bS35G3A1A1A3SaG1S14G2P99A2S2aG0S22S21RbA1A1A2A3A2A2A2F_;F_;Fjv;Ft;Fn;Fp;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w p n t jv IFF Hw.
  assert (AXI' : apply_axforms (se_t khi (Wcan 0) (NV q) (VFACT q)) (XIg 0 (length (NV q))) = Some (P0T_g khi (map carve_obj (NV q)) (VFACT q))).
  { rewrite AXI. unfold P0T_c. rewrite NV_ok. reflexivity. }
  destruct (t_instantiate khi (NV q) (VFACT q) Wa Da Wb Wc Wd Fe AXI' A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              (rhoF_agree A rho p n t jv) (instG_of_F khi _ _ q _ p n (N8 n) _ IFF) Hw) as (HR & HS & HO).
  unfold P0T_c. rewrite <- (NV_ok q).
  split; [exact HR|]. split; [exact HS|]. split; [exact HO | reflexivity].
Qed.
End TQ.
End F0T_asm.

(* [comment removed for export] *)
Module F0T_masm.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "junkF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_live"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "cons"; "fst"; "nat"; "nil"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "set_inited"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "JL_free"; "AE_A"; "KcA"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull"; "rt_zone2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull RebuildSM SMGlue SpineMallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j1.UnwT_pres.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma rho_sets_id : ltac2:(tb__ "0|2|
S12S14S1SfQ40A1M0A2M1A1S2S2dG1G1S5G0S3R2S16S1G0R1A3A2S1aS1G0R1A3A3Liv;R2A3S5S2S2fR2R3A2R2A3F_;Frho;Fl;").
Proof.
  induction l as [|[i v] t IH]; intros rho HF; [reflexivity|]. cbn [rho_sets].
  pose proof (Forall_inv HF) as H1. pose proof (Forall_inv_tail HF) as H2. cbn [fst snd] in H1.
  assert (E : rho_set_rw rho i v = rho).
  { destruct rho as [w l0 m]. unfold rho_set_rw. cbn [rw rl rm] in *. f_equal. apply functional_extensionality. intros j.
    destruct (Pos.eqb_spec j i) as [->|NE]; [symmetry; exact H1 | reflexivity]. }
  rewrite E. apply IH. exact H2.
Qed.

Lemma rhoF_of_id : ltac2:(tb__ "0|0|
ScS2S2S0S0S0SbS27S9SaR7R6R4R3R2R1A6R5A3S5S2SaS20R8A1R6R5R4R3R2A6R6A3F_;Fjv;Ft;Fn;Fp;Frho2;Frho;FA;").
Proof.
  intros A rho rho2 p n t jv [Hw _]. unfold rhoF_of at 1. apply rho_sets_id.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (rewrite <- Hw by (unfold GW; lia); reflexivity).
Qed.

Lemma mid_link_pn : ltac2:(tb__ "0|3|
ScS2S2S0S0S0SbS29R7SaR7R6R4R3R2R1A6R5A3S6S5S0S10Q40M0S3R6PcM1A2A2S10G0S3R7G1A2A2A3S5S0S10G0S3R6PdM2A2A2S10G0S3R7G2A2A2A3A2F_;Fjv;Ft;Fn;Fp;Frho2;Frho;FA;").
Proof.
  intros A rho rho2 p n t jv ([Hw _] & _). split; [rewrite <- (Hw 12%positive) by (unfold GW; lia) | rewrite <- (Hw 13%positive) by (unfold GW; lia)]; reflexivity.
Qed.

Section MASM.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S32VCST;R1A2S6S7S6S23S21R2A2S24R2S22A2A2A1S7S6S23Z17db48R2A2S24R2Z17db4cA2A2A1A2F_;Fa;").

Lemma tjv_ok_mid : ltac2:(tb__ "0|0|
ScS2S2S12SfQ40A1A1S26S0S0S0SbS1fS8R9R8R6R5A5S33S14S0S0A2S13S0S0R5R4A4SeRaA1A3S29RbSaRbRaR6R5R4R3A6R9A3S28RcRbR7R6R5R4A6S28S20RdA1RbR8R7R6R5A6F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd;Ftp;Frho2;Frho0;FA;").
Proof.
  intros A rho0 rho2 tp md p n t jv HA HL (_ & VQ & _) ((T1 & T2 & T3 & T4) & (J1 & J2 & J3 & J4 & C1 & C2 & C3)).
  pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (Hsep & _). destruct (Hsep p n HL) as (S1 & S2 & _). unfold IMG_HI in S2.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI.
  assert (Erm : rm (rhoF_of A rho0 p n t jv) = rm rho0) by reflexivity. rewrite Erm in VQ.
  assert (X : forall c, (forall k, (k < c_w c)%nat -> ~ ia_zone (c_addr c + Z.of_nat k)) -> cell_ok (view segsA (rm rho0)) c -> cell_ok (view segsA (rm rho2)) c).
  { intros c Hc Hok. eapply cell_ok_agree; [|exact Hok]. intros k Hk. apply VQ. exact (Hc k Hk). }
  unfold tjv_ok. change (aa_geom (set_inited A)) with (aa_geom A). change (aa_q_thread (set_inited A)) with (aa_q_thread A).
  split; [split; [exact T1|]; split; [exact T2|]; split|].
  - apply X; [|exact T3]. cbn [c_addr c_w]. intros k Hk. unfold ia_zone, IA_BEG, IA_END. lia.
  - apply X; [|exact T4]. cbn [c_addr c_w]. intros k Hk. unfold ia_zone, IA_BEG, IA_END. lia.
  - split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|]. split; [|split].
    + apply X; [|exact C1]. cbn [c_addr c_w]. intros k Hk. unfold ia_zone, IA_BEG, IA_END, QG. lia.
    + apply X; [|exact C2]. cbn [c_addr c_w]. intros k Hk. unfold ia_zone, IA_BEG, IA_END. lia.
    + intros HE. destruct (C3 HE) as [C3a C3b]. split; (apply X; [|assumption]); cbn [c_addr c_w]; intros k Hk; unfold ia_zone, IA_BEG, IA_END; lia.
Qed.

Lemma post_mid : ltac2:(tb__ "0|7|
S17ScS2cS2S2S12SfQ40M0A1A1M1G1S26S2eS1fS8R8R6R3R2A5S27S1bR7R6A3S0S6S23Z0R1A2S24R1S25Z2Z40A2A2A2S7S30SdRcA1R2A2A1S5S19SfQ8A1A1S4RaS11G0R3A2M2A2S4RbG2A2A3F_;F_;Fa;S1eS8S1bR8R7S15S14S1cS1dA2M3S13S1cS1dS31S2bA1M4S2aS1fS8A1M5VCST;VXGL;S20RbA1RaA5A4S18G3A1M6A3R4A6S1eS8S1bRaR8S15G3S13S1cS1dG4S2aG5VCST;VXGL;RcRbA5A4G6A3R5A6F_;F_;F_;F_;Fw;Fmd0;Ftp0;Ftp;Frho2;Frho0;FKc;FA;FnW;").
Proof.
  intros nW A Kc rho0 rho2 tp tp0 md0 w HA0 [AGw AGl] RMO (L & JL & rho' & tp' & Hin & [Hw' Hl'] & Hsm & HJL).
  destruct Hin as [E|[]]. injection E as <- <-.
  pose proof HA0 as (HG & _ & HF & HRest & _). pose proof (proj1 HRest) as Hsep.
  exists (L_free_tol AE_A), (JL_free (AInvA segsA) CST XGL A Kc), rho', tp'.
  split; [left; reflexivity|]. split; [split; [intros i Hi; rewrite (AGw i Hi); exact (Hw' i Hi) | intros l; rewrite (AGl l); exact (Hl' l)]|]. split; [exact Hsm|].
  destruct HJL as (A' & l1 & l2 & HA' & ELV & ELV' & EF & EV & EKm & EKf & EG & MK & HKc & CK).
  exists A', l1, l2. split; [exact HA'|].
  split; [rewrite (AGw 12%positive) by (unfold NF; lia); rewrite (AGw 13%positive) by (unfold NF; lia); exact ELV|].
  split; [exact ELV'|]. split; [exact EF|]. split; [exact EV|]. split; [exact EKm|]. split; [exact EKf|]. split; [exact EG|].
  split; [|split; [exact HKc | exact CK]].
  destruct MK as [MK1 MK2]. change (client_addrA CST (set_inited A)) with (client_addrA CST A) in MK1, MK2.
  change (client_shadowA CST XGL (set_inited A)) with (client_shadowA CST XGL A) in MK1.
  split.
  - intros a Ba Hcl.
    assert (NZ : ~ rt_zone2 (aa_geom A) a).
    { destruct Hcl as [[C1 _]|[C1 _]]; [exact (client_not_rt2 CST HCST HCST2 A a _ HG HF Hsep C1)|].
      pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B. exact (shadow_not_rt2 A a HG B). }
    rewrite <- (RMO a Ba NZ). apply MK1; [exact Ba|].
    destruct Hcl as [H1|(H1 & H2 & H3)]; [left; exact H1 | right; split; [exact H1|]; split; [exact H2|]; rewrite (RMO a Ba NZ); exact H3].
  - intros x j Hx Hj Hdef. apply (MK2 x j Hx Hj).
    assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
    { destruct Hx as [[C1 C2]|GX].
      - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. lia.
      - destruct (HXGL x GX). unfold IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. lia. }
    unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
    destruct (word_byte_range (Sh x) j ltac:(lia) Hj) as (W1 & W2 & W3).
    unfold word_byte in *. rewrite RMO; [exact Hdef | lia |].
    apply (shadow_not_rt2 A _ HG). lia.
Qed.
End MASM.
End F0T_masm.

