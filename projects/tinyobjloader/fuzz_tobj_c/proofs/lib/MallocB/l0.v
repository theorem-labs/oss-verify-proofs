(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l3 li.

(* [comment removed for export] *)
Module InvQ11.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "sub"; "of_nat"; "div"; "modulo"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "sec_chunk"; "sc_map_beg"; "aa_sec"; "aa_live"; "AA"; "sc_map_size"; "aa_geom"; "ag_pab"; "ageom"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cache_inited"; "aa_cls"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "mkAA"; "sc_size"; "@Corelib.Init.Datatypes"; "prod"; "bool"; "false"; "app"; "pair"; "list"; "Some"; "option"; "cons"; "fst"; "nat"; "snd"; "length"; "None"; "negb"; "@Stdlib.Lists.List"; "In"; "nth_error"; "filter"; "NoDup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "is_primary"; "rz"; "Sh"; "round_up"; "kQuarantineMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "cell_ok"; "mkACell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "rl"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4"; "chunk_sh_zone"; "chunk_zone"; "sec_junk_zone"; "sec_tbl_zone"; "swap_remove"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "live_ids"; "SEC_INST"; "q_foot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qall"; "qitems"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.InvQ10b"; "RZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l0.InvQ11"; "freeBigA"; "@Corelib.Init.Nat"; "sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt SoundA SummaryA MmapFixedA MmapFixedA2 MadviseSpecA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws ContractFreeNull SMGlue RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.RebuildS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import PlacementA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.InvQ10a OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.InvQ10b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.InvQ10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition freeBigA (A : AA) (l1 l2 : list (Z * Z)) (i : nat) : AA := ltac2:(tb__ "0|0|
S25S16VA;A1S1dVA;A1S1cVA;A1S4cS10S12VA;A1Vi;A3S22VA;A1S2aS27S0S0A2Vl1;Vl2;A3S24VA;A1S23VA;A1S1eVA;A1S20VA;A1S1fVA;A1S21VA;A1S1bVA;A1S1aVA;A1S19VA;A1Af").

Lemma big_not_primary : ltac2:(tb__ "0|0|
S0S9S3fR1A2S2S28S3bR2A1S29A3F_;Fn;").
Proof.
  intros n Hn. destruct (is_primary n) eqn:E; [exfalso | reflexivity]. unfold is_primary in E. apply Z.leb_le in E.
  unfold needed in E. pose proof (rz_bound n) as RB. unfold kQuarantineMax in Hn.
  assert (R8 : n <= round_up (Z.max n kChunkHeader2Size) 8) by (unfold round_up; pose proof (Z.div_mod (Z.max n kChunkHeader2Size + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Z.max n kChunkHeader2Size + 7) 8 ltac:(lia)); lia).
  unfold kMaxSize in E. lia.
Qed.
Lemma nonprimary_large : ltac2:(tb__ "0|0|
S0S8Z1R1A2S2S28S3bR2A1S29A3S8Zfc01R3A2F_;F_;Fn;").
Proof. intros n H1 HP. destruct (Z_le_dec 64513 n) as [L|L]; [exact L|]. rewrite (primary_small n) in HP by lia. discriminate HP. Qed.

Section PureLive.
Variables (A : AA) (l1 l2 : list (Z * Z)) (p n : Z) (i : nat) (ch : sec_chunk).
Hypothesis HLV : ltac2:(tb__ "0|1|
S2S2cS27S0S0A2M0A1S13VA;A1S2aG0Vl1;S2fG0S2bS0S0Vp;Vn;A4Vl2;A3A3A3").
Hypothesis HPn : is_primary n = false.
Hypothesis Hn1 : 1 <= n.
Hypothesis Hi : ltac2:(tb__ "0|0|
S2S2eS10A1S37S10S12VA;A1Vi;A3S2dS10Vch;A2A3").
Hypothesis Hu : ltac2:(tb__ "0|0|
S2S0Vp;S7S7S11Vch;A1S3aA2Z800A2A3").
Hypothesis HQP : q_pure A.
Hypothesis HI3 : inv3 A.
Local Abbreviation A' := (freeBigA A l1 l2 i).
Local Abbreviation secf := (fun bn : Z * Z => negb (is_primary (snd bn))).

Lemma PL_in : ltac2:(tb__ "0|1|
S27S0S0A2M0S36G0R1S2aG0Vl1;Vl2;A3A3S36G0R2S13VA;A1A3F_;Fbn;").
Proof. intros bn H. rewrite HLV. apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. Qed.

Lemma PL_nodup : ltac2:(tb__ "0|4|
S3S39S0S2aS0S55S27S0S0A2M0S0S30S0S0A2M1S38G0G0S35S3bS32S0S0R1A3A1A1Lbn;M2S2aG0Vl1;Vl2;A3A3A4S55G0S0G1S38G0G2S54S53VA;A1A1A3A4A3M3A2S4S36S0Vp;G3A3A1A2").
Proof.
  destruct HI3 as (_ & _ & _ & _ & _ & ND & _). apply (proj1 (NoDup_ListNoDup _)) in ND.
  rewrite HLV in ND. rewrite !List.filter_app in ND. cbn [List.filter snd] in ND. rewrite HPn in ND. cbn [negb] in ND.
  rewrite !List.filter_app. rewrite !map_app in ND. rewrite !map_app. cbn [map fst] in ND.
  rewrite <- app_assoc in ND. cbn [app] in ND. rewrite <- app_assoc.
  exact (NoDup_remove _ _ _ ND).
Qed.
Lemma PL_live_other : ltac2:(tb__ "0|1|
S0S0S36S27S0S0A2M0S2bS0S0R2R1A4S2aG0Vl1;Vl2;A3A3S2S28S3bR2A1S29A3S4S2S0R4Vp;A3A1F_;F_;Fm;Fb;").
Proof.
  intros b m Hin HP E. destruct PL_nodup as [_ NI]. apply NI. apply in_or_app. left. apply in_map_iff. exists (b, m). split; [exact E|].
  apply filter_In. split; [exact Hin|]. cbn. rewrite HP. reflexivity.
Qed.
Lemma PL_item_other : ltac2:(tb__ "0|1|
S27S0S0A2M0S36G0R1S54S53VA;A1A1A3S2S28S3bS32S0S0R2A3A1S29A3S4S2S0S30S0S0R3A3Vp;A3A1F_;F_;Fit;").
Proof.
  intros it Hin HP E. destruct PL_nodup as [_ NI]. apply NI. apply in_or_app. right. apply in_map_iff. exists it. split; [exact E|].
  apply filter_In. split; [exact Hin|]. rewrite HP. reflexivity.
Qed.
Lemma PL_chunk_stays : ltac2:(tb__ "0|0|
S10S0S36S10R2S12VA;A1A3S2S0R2S7S7S11R3A1S3aA2Z800A2A3S4S2S0R3Vp;A3A1S36S10R5S12S5bVA;Vl1;Vl2;Vi;A4A1A3F_;F_;F_;Fu;Fc;").
Proof.
  intros c u Hc Eu NE. change (aa_sec A') with (swap_remove (aa_sec A) i). destruct (In_nth_error _ _ Hc) as [j Hj].
  apply (swap_remove_In _ i ch j c Hi Hj). intros ->. rewrite Hi in Hj. injection Hj as <-. apply NE. rewrite Eu, Hu. reflexivity.
Qed.
Lemma QP_live : q_pure A'.
Proof.
  destruct HQP as [QF QN]. unfold q_pure. change (qall A') with (qall A). split; [|exact QN].
  apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) QF b Hb) as (B1 & B2 & B3 & B4).
  unfold batch_pure. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
  apply Forall_forall. intros it Hit. pose proof (proj1 (Forall_forall _ _) B4 it Hit) as (I1 & I2 & I3 & I4).
  unfold item_pure. cbv zeta. split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
  intros HP. destruct (I4 HP) as (c & Hc & Eu & Es). exists c. split; [|exact (conj Eu Es)].
  apply (PL_chunk_stays c (fst it) Hc Eu). apply PL_item_other; [|exact HP]. unfold qitems. apply in_flat_map. exists b. split; [exact Hb | exact Hit].
Qed.

Lemma I3_live : inv3 A'.
Proof.
  pose proof HI3 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold inv3. cbv zeta.
  change (aa_geom A') with (aa_geom A). change (aa_live A') with (l1 ++ l2). change (aa_sec A') with (swap_remove (aa_sec A) i).
  change (aa_cls A') with (aa_cls A). change (aa_depot A') with (aa_depot A). change (aa_cache_inited A') with (aa_cache_inited A).
  split; [exact I1|].
  split.
  { intros b m Hin. destruct (I2 b m (PL_in _ Hin)) as [P|(c & Hc & Eb & Es)]; [left; exact P|].
    destruct (is_primary m) eqn:EP; [left; reflexivity | right]. exists c. split; [|exact (conj Eb Es)].
    exact (PL_chunk_stays c b Hc Eb (PL_live_other b m Hin EP)). }
  split.
  { intros j c Hj. destruct (swap_remove_nth _ i ch j c Hi Hj) as (LTj & ORj).
    assert (OLDj : exists j0, nth_error (aa_sec A) j0 = Some c /\ j0 <> i /\ ((j <> i /\ j0 = j) \/ (j = i /\ j0 = (length (aa_sec A) - 1)%nat))).
    { destruct ORj as [[N E]|(E1 & LT & E)]; [exists j; split; [exact E | split; [exact N | left; split; [exact N | reflexivity]]]|].
      exists (length (aa_sec A) - 1)%nat. split; [exact E | split; [lia | right; split; [exact E1 | reflexivity]]]. }
    destruct OLDj as (j0 & Hj0 & Nj0 & Cj). destruct (I3 j0 c Hj0) as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [|exact (conj X6 X7)].
    intros j2 c2 Hj2 Nj. destruct (swap_remove_nth _ i ch j2 c2 Hi Hj2) as (LTj2 & ORj2).
    destruct ORj2 as [[N2 E2]|(E21 & LT2 & E2)].
    - apply (X5 j2 c2 E2). destruct Cj as [[_ ->]|[_ ->]]; [exact Nj | lia].
    - apply (X5 _ c2 E2). destruct Cj as [[Nji ->]|[Eji _]]; [lia | exfalso; apply Nj; rewrite Eji, E21; reflexivity]. }
  split; [exact I4|].
  split.
  { intros bn Hbn. destruct (I5 bn Hbn) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|]. split; [exact D7|].
    intros c Hc. destruct (swap_remove_incl _ i ch c Hi Hc) as (j & _ & Hj). exact (D8 c (nth_error_In _ _ Hj)). }
  split.
  { apply (proj2 (NoDup_ListNoDup _)). exact (proj1 PL_nodup). }
  split.
  { rewrite (swap_remove_length _ i ch Hi). change (qlarge A') with (qlarge A).
    pose proof (large_live_remove A A' l1 l2 p n HLV eq_refl) as LL. pose proof (nonprimary_large n Hn1 HPn) as LN.
    destruct (64513 <=? n) eqn:E; [|apply Z.leb_gt in E; exfalso; lia].
    pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite Hi; discriminate)) as LI. lia. }
  split.
  { pose proof (small_live_remove A A' l1 l2 p n HLV eq_refl) as SL. pose proof (nonprimary_large n Hn1 HPn) as LN.
    destruct (64513 <=? n) eqn:E; [|apply Z.leb_gt in E; exfalso; lia]. lia. }
  exact I9.
Qed.
End PureLive.

Section GeoLive.
Variables (A : AA) (m : bview).
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HLS : live_sep A.
Hypothesis HPR : primary_repr m A.
Hypothesis HSR : secondary_repr m A.
Hypothesis HI3 : inv3 A.
Variables (i : nat) (ch : sec_chunk).
Hypothesis Hi : ltac2:(tb__ "0|0|
S2S2eS10A1S37S10S12VA;A1Vi;A3S2dS10Vch;A2A3").

Lemma blk_in_chunk : ltac2:(tb__ "0|2|
S0S0S36S27S0S0A2S2bS0S0R2R1A4S13VA;A1A3S2S28S3bR2A1S29A3S2S0R4S7S7S11Vch;A1M0S3aA2Z800M1A2A3S3S2S0S3cR4A1G1A3S3S8Z1R4A2S8S7S7R5R4A2G1A2S7G0S15Vch;A1A2A2A2A2F_;F_;F_;Fn;Fp;").
Proof.
  intros p n Hin HP Hu. destruct (live_sec_map A m HLS HSR HI3 p n Hin HP) as (j & c & Hj & Eb & RZn & N1 & BN & _).
  assert (Eji : j = i).
  { destruct (Nat.eq_dec j i) as [E|NE]; [exact E | exfalso]. destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j c Hj) as (_ & _ & _ & _ & X5 & _).
    pose proof (X5 i ch Hi NE) as AP. destruct (ch_nums A m HSR j c Hj) as (_ & C2 & _). destruct (ch_nums A m HSR i ch Hi) as (_ & C2' & _). lia. }
  subst j. rewrite Hi in Hj. injection Hj as <-. split; [exact RZn|]. split; [exact N1 | exact BN].
Qed.

Lemma blk_foot_chunk : ltac2:(tb__ "0|1|
S0S0S0S36S27S0S0A2S2bS0S0R3R2A4S13VA;A1A3S2S28S3bR3A1S29A3S2S0R5S7S7S11Vch;A1S3aA2Z800A2A3S3S3S8SaR6S3cR5A1A2R4A2S9R4S7R6R5A2A2A2S49Vch;R5A2F_;S3S8S3dR6A1M0R4A2S9R4S7G0ScS7R5Z7A2Z8A2A2A2A2S48Vch;R5A2F_;A2F_;F_;F_;Fz;Fn;Fp;").
Proof.
  intros p n z Hin HP Hu. destruct (blk_in_chunk p n Hin HP Hu) as (RZn & N1 & BN). destruct (ch_nums A m HSR i ch Hi) as (C1 & C2 & C3 & _ & C5 & C6 & C7).
  unfold chunk_zone, chunk_sh_zone, PG in *. split; [intros Hz; lia|]. intros Hz. rewrite C7.
  pose proof (Geometry.Sh_mono (sc_map_beg ch) p ltac:(lia)) as M1.
  assert (M2 : Sh p + (n + 7) / 8 <= Sh (sc_map_beg ch) + sc_map_size ch / 8).
  { unfold Sh in *. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as MB.
    pose proof (Z.div_le_mono (p + (n + 7) / 8 * 8) (sc_map_beg ch + sc_map_size ch) 8 ltac:(lia) ltac:(lia)) as X. rewrite Z.div_add in X by lia.
    assert (E : (sc_map_beg ch + sc_map_size ch) / 8 = sc_map_beg ch / 8 + sc_map_size ch / 8).
    { pose proof (Z.div_mod (sc_map_size ch) 8 ltac:(lia)) as D2. rewrite C6 in D2. replace (sc_map_beg ch + sc_map_size ch) with (sc_map_beg ch + sc_map_size ch / 8 * 8) by lia. apply Z.div_add. lia. }
    lia. }
  lia.
Qed.

Section SubLive.
Variable L : list (Z * Z).
Hypothesis HLin : ltac2:(tb__ "0|1|
S27S0S0A2M0S36G0R1VL;A3S36G0R2S13VA;A1A3F_;Fbn;").
Hypothesis HNL : ltac2:(tb__ "0|0|
S0S0S36S27S0S0A2S2bS0S0R2R1A4VL;A3S2S28S3bR2A1S29A3S4S2S0R4S7S7S11Vch;A1S3aA2Z800A2A3A1F_;F_;Fn;Fb;").
Lemma nRZ_liveL : ltac2:(tb__ "0|1|
S0S0S0S36S27S0S0A2S2bS0S0R3R2A4VL;A3S6S3S8SaR4S3cR3A1A2R2A2S9R2S7R4R3A2A2A2S3S8S3dR4A1M0R2A2S9R2S7G0ScS7R3Z7A2Z8A2A2A2A2A2S4S5aVA;Vi;Vch;R3A4A1F_;F_;Fz;Fn;Fb;").
Proof.
  intros b n z HinL Hz. pose proof (HLin _ HinL) as Hin. destruct (space_nums A HG) as (S1 & S2 & _). destruct (is_primary n) eqn:HP.
  - pose proof HI3 as (H3 & _). pose proof (live_prim_czone A HG H3 m HLS HPR b n Hin HP) as LP. cbv zeta in LP.
    destruct LP as (C1 & O0 & OM & OE & _ & _ & CZ).
    destruct (czone_where A HG H3 _ _ z C1 O0 OM OE (CZ z Hz)) as [W|[W _]].
    + apply (nRZ_space A m HG HSR HI3 i ch Hi). clear -W. lia.
    + apply (nRZ_space_sh A m HG HSR HI3 i ch Hi (ag_spacebeg (aa_geom A)) (ag_spacebeg (aa_geom A) + 2 ^ 37) z); [lia | lia | lia | exact W].
  - destruct (live_sec_map A m HLS HSR HI3 b n Hin HP) as (j & c & Hj & Eb & RZn & N1 & BN & _).
    assert (Nji : j <> i) by (intros ->; rewrite Hi in Hj; injection Hj as <-; exact (HNL b n HinL HP Eb)).
    destruct (ch_nums A m HSR j c Hj) as (C1 & C2 & C3 & _). unfold PG in Eb.
    destruct Hz as [Hz|Hz].
    + apply (nRZ_chunk A m HSR HI3 i ch Hi j c z Hj Nji); [rewrite RZn in Hz; lia | intros _; rewrite RZn in Hz; lia].
    + destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j c Hj) as (_ & _ & _ & _ & X5 & _). pose proof (X5 i ch Hi Nji) as AP.
      apply (nRZ_sh A m HSR i ch Hi b n z); [lia | lia | lia | lia | exact Hz].
Qed.
End SubLive.

Hypothesis HQP : q_pure A.
Hypothesis HNI : ltac2:(tb__ "0|1|
S27S0S0A2M0S36G0R1S54S53VA;A1A1A3S2S28S3bS32S0S0R2A3A1S29A3S4S2S0S30S0S0R3A3S7S7S11Vch;A1S3aA2Z800A2A3A1F_;F_;Fit;").
Lemma nRZ_qfoot : ltac2:(tb__ "0|0|
S0S52VA;R1A2S4S5aVA;Vi;Vch;R2A4A1F_;Fz;").
Proof.
  intros z Hz. pose proof HI3 as (H3 & _). destruct (space_nums A HG) as (S1 & S2 & _).
  assert (HAU : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A c) <= kUserSpaceSize).
  { intros c Hc. destruct HPR as (_ & _ & _ & P4). pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold cls_of, kUserMapSize in *. lia. }
  assert (PRIM : qzone A z -> ~ RZ A i ch z).
  { intros QZ. destruct (qzone_czone A HG H3 HQP HAU z QZ) as (c & o & (C1 & O0 & OM & OE & _) & CZ).
    destruct (czone_where A HG H3 _ _ z C1 O0 OM OE CZ) as [W|[W _]].
    - apply (nRZ_space A m HG HSR HI3 i ch Hi). clear -W. lia.
    - apply (nRZ_space_sh A m HG HSR HI3 i ch Hi (ag_spacebeg (aa_geom A)) (ag_spacebeg (aa_geom A) + 2 ^ 37) z); [lia | lia | lia | exact W]. }
  unfold q_foot in Hz. fold (qall A) in Hz. apply Exists_exists in Hz as (b & Hb & Hz). destruct Hz as [Hz|Hz].
  - apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | left; exact Hz].
  - apply Exists_exists in Hz as (it & Hit & Hz). destruct (is_primary (snd it)) eqn:EP.
    + apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | right]. apply Exists_exists. exists it. split; [exact Hit|]. split; [exact EP | exact Hz].
    + destruct HQP as [QP _]. pose proof (proj1 (Forall_forall _ _) QP b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _ & IP4).
      destruct (IP4 EP) as (c & Hc & Eu & Esz). destruct (In_nth_error _ _ Hc) as [j Hj].
      assert (Hitq : In it (qitems (qall A))) by (unfold qitems; apply in_flat_map; exists b; split; [exact Hb | exact Hit]).
      assert (Nji : j <> i) by (intros ->; rewrite Hi in Hj; injection Hj as <-; exact (HNI it Hitq EP Eu)).
      pose proof HSR as (HS1 & _). destruct (HS1 j c Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
      pose proof (rz_sec (snd it) IP2 EP) as RZn. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot.round_up_ge8 (snd it)) as R8. destruct (ch_nums A m HSR j c Hj) as (C1 & C2 & C3 & _). unfold PG in *.
      destruct Hz as [Hz|Hz].
      * apply (nRZ_chunk A m HSR HI3 i ch Hi j c z Hj Nji); [lia | intros _; lia].
      * destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j c Hj) as (_ & _ & _ & _ & X5 & _). pose proof (X5 i ch Hi Nji) as AP.
        apply (nRZ_sh A m HSR i ch Hi (fst it) (snd it) z); [lia | lia | lia | lia | exact Hz].
Qed.
End GeoLive.

Lemma live_ids_remove_sec : ltac2:(tb__ "0|3|
S18S14S14S2cS27S0S0A2M0A1M1G1S0S0S0S2G1S13R7A1M2S2aG0R5S2fG0S2bS0S0R3R2A4R4A3A3A3S2G1G2S2aG0R6R5A3A3S2S28S3bR4A1S29A3S2S2cS0A1S50RbR9R4A3S50RbRaR4A3A3F_;F_;F_;Fc;Fn;Fp;Fl2;Fl1;FA';FA;FG;").
Proof.
  intros G A A' l1 l2 p n c E E' HP. rewrite !F0A_rebuild.live_ids_LI, E, E', !F0A_rebuild.LI_app, F0A_rebuild.LI_cons.
  unfold F0A_rebuild.Pc at 1. cbn [snd]. rewrite HP. reflexivity.
Qed.

Theorem AInvA_unmap_live : ltac2:(tb__ "0|18|
S14S45S45S2cS4eQ40M0A1M1A1S56S2cS27S0S0A2M2A1M3G3S0S0S31S10S4fS40RbRaR8R7A5S2G3S13RcA1S2aG2R7S2fG2S2bS0S0R5R4A4R6A3A3A3S2S28S3bR5A1S29A3S2S2eS10A1M4S37S10S12ReA1R5A3S2dS10R4A2A3S2S0R8S7S7S11R5A1S3aA2Z800A2A3S16R10A1S18SbS33S10S12R11A1A2A1S0S1S2G1S47R11R1A2S47R12R1A2A3Fi0;S1S2S2cS4eQ8A1M5A1S46R12R1A2S46R13R1A2A3Fl;S0S4S4aR1A1M6A1S4S4bR16RdR2A3A1S4S49RdR3A2A1S4S48ReR4A2A1S2S2eG5A1M7S41S40S44R17A1R5A3S41S40S44R18A1R5A3A3F_;F_;F_;F_;Fz;S0S6G6S48RcR1A2A2S4S2G7S41S40S44R16A1M8R2A3S34G5A1M9A3A1S4S2G7S41S40G8R3A3G9A3A1F_;F_;Fz;S42S41S40S44R14A1A2S43S7S51Z38A2U8MaSaR5Z1MbA2A3A2S42S41S40S44R15A1A2S43Zead00U4Z0A3A2S10S2G4S37S10S12R19A1McS5cS33S10GcA2U1A2A3S2dS10R1A2A3S3S9SbR11A1MdSaR9GbA2MeA2S3S42S41S40S44R19A1A2MfS43S7S17RbA1SeZ8M10SbR12A1M11A2A2GaS11R3A1M12A3A2S42GfS43S7G12Z18A2GaG11A3A2A2F_;S2S0GdGeA3S0S3S8S7S17RcA1SeG10SbR13A1A2A2M13R1A2S9R1S7G13G10A2A2A2S2G7S41S40S44R1bA1R2A3S41S40S44R1cA1R2A3A3F_;Fz;F_;A2F_;Flst;S8S59S57R15S4dG0S11RfA1M14A2S4dG0S15RfA1M15A2A3S58G14S7G14G15A2R16A3A2S59R15R16A2A2S4fS40S5bR1aR15R14R11A4R18S58S11R10A1M16S7G16S15R10A1M17A2R17A3S57R16S4dG0G16A2S4dG0G17A2A3A5F_;F_;F_;F_;F_;F_;F_;F_;Tnch;TG;F_;F_;F_;F_;F_;Fch;Fi;Fn;Fp;Fl2;Fl1;Fmd;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp md l1 l2 p n i ch HAA HLV HPn Hi Hu. cbv zeta. intros Hw Hl HOUT0 HIN CN CM CL HPAID.
  set (A' := freeBigA A l1 l2 i).
  set (tp' := tp_forget (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) tp).
  set (md' := munmap_model md (Z_to_bv 64 (sc_map_beg ch)) (Z_to_bv 64 (sc_map_size ch))).
  pose proof (AInvA_Q A rho tp md HAA) as HA.
  pose proof HAA as (HG & _ & _ & HRestA & _). destruct HRestA as (_ & _ & _ & _ & HQR & _).
  pose proof HA as (_ & _ & _ & HRest & HM & HI3 & _). cbv zeta in HRest. destruct HRest as (HLS & R2 & HPR & HSR & (HQP & _) & _).
  set (mm := maskv (fs_footb (aa_geom A)) (view segsA (rm rho))) in *. set (mm' := maskv (fs_footb (aa_geom A)) (view segsA (rm rho'))).
  assert (Hin : In (p, n) (aa_live A)) by (rewrite HLV; apply in_or_app; right; left; reflexivity).
  assert (Hn1 : 1 <= n) by exact (proj1 (HLS p n Hin)).
  assert (HOUT : forall z, ~ RZ A i ch z -> view segsA (rm rho') z = view segsA (rm rho) z).
  { intros z NR. apply HOUT0; intros X; apply NR; [left | right; left | right; right; left | right; right; right]; exact X. }
  assert (HNL : forall b m0, In (b, m0) (l1 ++ l2) -> is_primary m0 = false -> b <> sc_map_beg ch + PG + 2048).
  { intros b m0 Hb HP. rewrite <- Hu. exact (PL_live_other A l1 l2 p n HLV HPn HI3 b m0 Hb HP). }
  assert (HNI : forall it, In it (qitems (qall A)) -> is_primary (snd it) = false -> fst it <> sc_map_beg ch + PG + 2048).
  { intros it Hit HP. rewrite <- Hu. exact (PL_item_other A l1 l2 p n HLV HPn HI3 it Hit HP). }
  assert (OUTM : forall z, ~ RZ A i ch z -> mm' z = mm z) by (intros z NR; exact (X_out A rho rho' i ch (RZ A i ch) (fun _ H => H) HOUT z NR)).
  destruct (blk_in_chunk A mm HLS HSR HI3 i ch Hi p n Hin HPn Hu) as (RZn & _ & BN).
  assert (HCH : forall j c, nth_error (aa_sec A) j = Some c -> 0 < sc_map_size c /\ dyn_in (topG (aa_geom A)) (sc_map_beg c) (sc_map_size c)).
  { intros j c Hj. destruct HSR as (S1 & _). destruct (S1 j c Hj) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & D10 & _). split; [unfold PG in D8; lia | exact D10]. }

  assert (HQ' : AInvQ A' rho' tp' md').
  { unfold AInvQ. cbv zeta. change (aa_geom A') with (aa_geom A). fold mm'.
    split; [exact HG|].
    split; [exact (X_rtc A rho rho' tp md i ch (RZ A i ch) HA Hi (fun _ H => H) HOUT)|].
    split; [exact (X_fs A rho rho' tp md i ch (RZ A i ch) HA Hi (fun _ H => H) HOUT)|].
    split; [|split; [exact (model_unmap A tp md i ch (aa_q_thread A) (aa_q_global A) HM HI3 Hi HCH HPAID) | split]].
    -
      split; [intros b m0 Hb; exact (HLS b m0 (PL_in A l1 l2 p n HLV _ Hb))|].
      split.
      { assert (R2' : live_block_repr mm A') by (intros b m0 Hb; exact (R2 b m0 (PL_in A l1 l2 p n HLV _ Hb))).
        apply (live_block_repr_agree mm mm' A' A' eq_refl); [| | exact R2'].
        - intros b m0 z Hb Hz. apply OUTM. exact (nRZ_liveL A mm HG HLS HPR HSR HI3 i ch Hi (l1 ++ l2) (PL_in A l1 l2 p n HLV) HNL b m0 z Hb Hz).
        - intros b m0 Hb. exact (proj1 (HLS b m0 (PL_in A l1 l2 p n HLV _ Hb))). }
      split.
      { pose proof HPR as (Q1 & Q2 & Q3 & P4). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. intros c Hc.
        apply (class_repr_agree_gen mm mm' (aa_geom A) A A' c _ Hc eq_refl (live_ids_remove_sec (aa_geom A) A A' l1 l2 p n c HLV eq_refl HPn) eq_refl);
          [intros b m0 Hb _ _; exact (PL_in A l1 l2 p n HLV _ Hb) | | | exact (P4 c Hc)].
        - intros z Hz. apply OUTM. apply (nRZ_cls A mm HG HPR HSR HI3 i ch Hi c z Hc). unfold cls_meta in Hz. unfold cls_foot. cbv zeta in *.
          destruct Hz as [H|[H|[H|H]]]; [left | right; left | right; right; right; left | right; right; right; right]; exact H.
        - pose proof (P4 c Hc) as PC. unfold class_repr in PC. destruct PC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PU & _).
          intros z Hz Hn'.
          assert (NRz : ~ RZ A i ch z) by (apply (nRZ_cls A mm HG HPR HSR HI3 i ch Hi c z Hc); unfold cls_foot; cbv zeta; right; right; left; exact Hz).
          rewrite (OUTM z NRz). apply PU; [exact Hz|]. intros (b & m0 & Hb & Hbz). rewrite HLV in Hb. apply in_app_or in Hb as [Hb|[Hb|Hb]].
          + apply Hn'. exists b, m0. split; [apply in_or_app; left; exact Hb | exact Hbz].
          + injection Hb as <- <-. apply NRz. right. right. left. unfold chunk_zone. unfold PG in *. lia.
          + apply Hn'. exists b, m0. split; [apply in_or_app; right; exact Hb | exact Hbz]. }
      split.
      { pose proof (X_sec_unmap A rho rho' tp md i ch (aa_q_thread A) (aa_q_global A) HA Hi HOUT HIN CN CM CL) as VS. fold mm' in VS.
        destruct VS as (S1 & SR). split; [|exact SR].
        intros j c Hj. destruct (S1 j c Hj) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & PB & PS).
        split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|]. split; [exact E7|]. split; [exact E8|].
        split; [exact E9|]. split; [exact E10|]. split; [exact E11|]. split; [exact E12|]. split; [|exact PS].
        intros z Hz Hn'. apply PB; [exact Hz|]. intros (b & m0 & Hb & Hbz). change (aa_live (unmap_sec (set_q A (aa_q_thread A) (aa_q_global A)) i)) with (aa_live A) in Hb.
        rewrite HLV in Hb. apply in_app_or in Hb as [Hb|[Hb|Hb]].
        + apply Hn'. exists b, m0. split; [apply in_or_app; left; exact Hb | exact Hbz].
        + injection Hb as <- <-.
          change (aa_sec A') with (swap_remove (aa_sec A) i) in Hj. destruct (swap_remove_nth _ i ch j c Hi Hj) as (_ & ORj).
          assert (OLD : exists j0, nth_error (aa_sec A) j0 = Some c /\ j0 <> i).
          { destruct ORj as [[N E]|(E1' & LT & E)]; [exists j; split; [exact E | exact N] | exists (length (aa_sec A) - 1)%nat; split; [exact E | lia]]. }
          destruct OLD as (j0 & Hj0 & Nj0). destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j0 c Hj0) as (_ & _ & _ & _ & X5 & _).
          pose proof (X5 i ch Hi Nj0) as AP. unfold PG in *. lia.
        + apply Hn'. exists b, m0. split; [apply in_or_app; right; exact Hb | exact Hbz]. }
      split; [split; [exact (QP_live A l1 l2 p n i ch HLV HPn Hi Hu HQP HI3) | exact (X_qmin A rho rho' tp md i ch (RZ A i ch) HA Hi (fun _ H => H) HOUT)]|].
      split; [exact (X_depot A rho rho' tp md i ch (RZ A i ch) HA Hi (fun _ H => H) HOUT)|].
      split; [exact (X_ia A rho rho' tp md i ch (RZ A i ch) HA Hi (fun _ H => H) HOUT)|].
      split; [exact (X_thread A rho rho' tp md i ch (RZ A i ch) HA Hi (fun _ H => H) HOUT) | exact (X_misc A rho rho' tp md i ch (RZ A i ch) HA Hi (fun _ H => H) HOUT)].
    - exact (I3_live A l1 l2 p n i ch HLV HPn Hn1 Hi Hu HI3).
    - apply (X_bandtp A rho rho' tp md (RZ A i ch) (fun z => sec_junk_zone z \/ chunk_sh_zone ch z) HA (RZ_dec A i ch) HOUT (fun z _ HP => HIN z HP)
               (fun z HZ HB => or_intror (RZ_band A mm HSR i ch Hi z HZ HB))).
      intros q Hq. unfold tp', tp_forget in Hq. apply filter_In in Hq. exact (proj1 Hq). }

  destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_rebuildW.AInvB_Q kQuarantineCacheMax A rho tp md HAA) as (_ & QM & QB1 & QB2).
  apply (AInvQ_back A' rho' tp' md' HQ'); [| exact QB1 | exact QB2].
  change (q_mem (view segsA (rm rho')) A).
  apply (q_mem_frame A (view segsA (rm rho)) (view segsA (rm rho')) HQP); [| | | exact QM].
  - intros z Hz. apply HOUT. exact (nRZ_qfoot A mm HG HPR HSR HI3 i ch Hi HQP HNI z Hz).
  - intros z Hz. apply HOUT. apply (nRZ_T A mm HG HSR HI3 i ch Hi z). lia.
  - intros z Hz. apply HOUT. apply (nRZ_low A mm HSR i ch Hi z); unfold QG, SEC_INST in *; lia.
Qed.

Theorem live_big_chunk : ltac2:(tb__ "0|8|
S14S45S2cS4eQ40A1A1S56S0S0S4fS40R6R5R4R3A5S36S27S0S0A2S2bS0S0R3R2A4S13R7A1A3S2S28S3bR3A1S29A3S5S31S31S5S10S10S3S2S2eS10A1S37S10S12RbA1R2A3S2dS10R1A2A3S3S2S0R7S7S7S11R1A1M0S3aA2Z800M1A2A3S3S2S0S26R1A1S7S3eR6Z8M2A2Z1000A2M3A3S3S2S0S15R1A1M4S7S3eG3S3aA2S3aA2A3S3S2S0SdG0S3aA2Z0M5A3S3S2S0SdG4S3aA2G5A3S3S3S9G5G4A2S9G4SfZ2Z3eA2A2A2S3S8Z643000G0A2S3S8S7G0G4A2M6Z7fffff800000A2S3S2S0S3cR6A1G1A3S3S8Z1R6A2S3S8S7S7R7R6A2G1A2G6A2S3S0S3S8SaR8S3cR7A1A2R1A2S9R1S7R8R7A2A2A2S49R3R2A2F_;Fz;S0S3S8S3dR8A1M7R1A2S9R1S7G7ScS7R7Z7A2G2A2A2A2A2S48R3R2A2F_;Fz;A2A2A2A2A2A2A2A2A2A2A2A2A2Lch;A2Li;A2F_;F_;F_;Fn;Fp;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md p n HAA Hin HP. pose proof (AInvA_Q A rho tp md HAA) as HA.
  pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _). cbv zeta in HRest. destruct HRest as (HLS & _ & HPR & HSR & _).
  pose proof HI3 as (_ & LIV3 & _). destruct (LIV3 p n Hin) as [E|(ch & Hch & Eb & Esz)]; [rewrite E in HP; discriminate|].
  destruct (In_nth_error _ _ Hch) as (i & Hi). exists i, ch.
  pose proof HSR as (S1 & _). destruct (S1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
  destruct (ch_nums A _ HSR i ch Hi) as (C1 & C2 & C3 & _).
  destruct (blk_in_chunk A _ HLS HSR HI3 i ch Hi p n Hin HP Eb) as (RZn & N1 & BN).
  split; [exact Hi|]. split; [exact Eb|]. split; [exact Esz|]. split; [rewrite <- Esz; exact D11|]. split; [exact D6|]. split; [exact D7|].
  split; [lia|]. split; [exact C1|]. split; [exact C3|]. split; [exact RZn|]. split; [exact N1|]. split; [exact BN|].
  split; intros z Hz; [exact (proj1 (blk_foot_chunk A _ HLS HSR HI3 i ch Hi p n z Hin HP Eb) Hz) | exact (proj2 (blk_foot_chunk A _ HLS HSR HI3 i ch Hi p n z Hin HP Eb) Hz)].
Qed.
End InvQ11.

(* [comment removed for export] *)
Module MallocHitTail2.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E3p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "KcA"; "Kc_ok"; "JL_malloc_ok"; "J_alloc_preT"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CertMallocSPc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CertMallocSPd OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.SpineMallocS5iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.SpineMallocS6iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.SpineMallocS7iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS8iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS9iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocS9jW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l3.DepotCallHW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocS5t.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section HIT0T.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S9S8VCST;R1A2S8S20R2A2S1dF_;F_;Fa;").

Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9S8VCST;R1A2S1eS21R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S17VAInv;VW;Vst;VA;VKc;S1PcA1A6").

Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x17fbdc 4 0) := AInvA_die.
Let law_inv3 : forall A rho tp md, AInv A rho tp md -> inv3 A := AInvA_inv3.
Let W0 : list ulink := Wcan 2.
Let st0 : ustop := UStopLe.

Definition KEEP (A : AA) (a : Z) : Prop := ltac2:(tb__ "0|0|
S1fVCST;VXGL;VA;Va;A4").

Theorem malloc_hit_tail_2_P : ltac2:(tb__ "0|1|
ScOF_;S1aS14S0S5S1cQ40A1A1S5S7SeS10A2M0A1SfVsegs;SdR3R2R1A5SaS22G0S6SeS10S18S13VW0;Vst0;A3S16VAInv;VCST;VXGL;R6R5A5A4R2A3S15R6A1S4Vsegs;R9S2R7A1A3S11Vsegs;RaS2R8A1A3S0SbVsegs;RcS3Vsegs;S1bVW0;Vst0;RbRaR9A5S12VW0;Vst0;Z4A3R1R8A5R6A4FrhoX;F_;F_;F_;F_;TQ;FPosts;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Posts Q HPin HKc Hokl Hokpl.
  pose proof (depot_call_HD_2 CST XGL HCST HXGL HCSTD ok A Kc rho Q HKc Hokl Hokpl) as HD.
  assert (Hokf : forall A', ok_frameA segs ok (J W0 st0 A' Kc)).
  { intros A' r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  assert (HUS : stopJ_stable W0 st0) by (apply stopJ_stable_le).
  assert (HW : st0 = UStopLeOrPc -> W0 = []) by (intros E; discriminate E).
  set (nv := bv_unsigned (rw rho 12%positive)).

  apply (spine_s3p_tail 2%nat st0 4 SKY_0 YX_0 YF_0 YP_0 WY1_0 WY2_0 WY3_0 WY4_0 WY5_0 WY6_0 WY7_0 s3_0 ENT3_0 SID3_0 ok A Kc rho tp Q HW HUS HKc).
  intros Hcnt HSEP HPRM0 rhoE3.

  apply (spine_s4 2%nat st0 4 Cert4_0 (KEEP A) ok A Kc rho tp Q HUS HKc (Hokf A) HD).
  intros A' rho' rhoX5 tp' HDO HL.
  assert (Enu : bv_unsigned (rw rho' 12%positive) = nv) by (destruct HL as [HLw _]; rewrite (HLw 12%positive); reflexivity).
  assert (HPRM' : prim_room A') by exact (prim_room_same A A' (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HDO)))))) HPRM0).
  assert (Hcnt' : 1 <= cnt_of A' (bv_unsigned (rw rho' 12%positive))).
  { rewrite Enu. unfold cnt_of, cst_of. rewrite (proj1 (proj2 HDO)). exact Hcnt. }
  pose proof Hokl as HokA'.

  assert (K7 : forall tpY rhoY, triple segs ok (SPA segs (JGb W0 st0 A' Kc rho') (C7 W0 st0 4) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (spine_s7 2%nat st0 4 Cert7_0 OV7a_0 OV7b_0 TAB7a_0 TAB7b_0 W7a_0 W7b_0 D7a_0 D7b_0 NX7a_0 NX7b_0 G7a_0 G7b_0 F7a_0 F7b_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS8iW2.s8a_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS8iW2.s8b_0
             ENT8a_0 ENT8b_0 SID8a_0 SID8b_0 G7p_0 F7p_0 W7p_0 D7p_0 NX7p_0 F7an_0 F7bn_0 ok A' Kc rho' tpY Q HUS HKc HokA' Hcnt').
    - intros Hm0 rhoY8.
      apply (spine_s8_gen 2%nat st0 4 (C8 W0 st0 4) (C9 W0 st0 4) (E8a W0 st0 4) (E8b W0 st0 4) CC8ma_0 Cert8_0 HCC8ma_0 W8a_0 D8a_0 NX8a_0 s8_0 sd8_0 R8_0 T8_0 He8_0 Hchk8_0 HT8_0 FBC8_0 FBT8_0 ENT8_0 SID8_0 NXC8_0 i8_0 S8s_0 SPL8_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS9iW2.s8b_0 sd8b_0 R8b_0 T8b_0 He8b_0 Hchk8b_0 HT8b_0 FBC8b_0 FBT8b_0 NXC8b_0 i9_0 SU_0 SM_0 ENTU_0 SIDU_0 MRG_0 s9m_0 ENTM_0 SIDM_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY9 tpY9.
      exact (spine_s9_P 2%nat st0 CST XGL HCST HXGL HCSTM law_die false (C9 W0 st0 4) F9a_nf F9b_nf Cert9a_0 Cert9b_0 NX9_0 FGC_0
               swc_a scells_a hcells_a swc_b scells_b hcells_b s9_a s9_b FH_a_0 FH_b_0 ok A A' Kc rho rho' (KEEP A) tp Posts HPin HW HUS HKc HokA' HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm0 rhoY9 tpY9).
    - intros Hm8 rhoY7.
      apply (spine_s7p 2%nat st0 4 Cert7p_0 OV7c_0 OV7d_0 TAB7c_0 TAB7d_0 W7c_0 W7d_0 D7c_0 D7d_0 NX7c_0 NX7d_0 G7c_0 G7d_0 F7c_0 F7d_0 s8c_0 s8d_0
               ENT8c_0 ENT8d_0 SID8c_0 SID8d_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY8.
      apply (spine_s8_gen 2%nat st0 4 (C8p W0 st0 4) (C9p W0 st0 4) (E8pa W0 st0 4) (E8pb W0 st0 4) CC8map_0 Cert8p_0 HCC8map_0 W8ap_0 D8ap_0 NX8ap_0 s8p_0 sd8p_0 R8p_0 T8p_0 He8p_0 Hchk8p_0 HT8p_0 FBC8p_0 FBT8p_0 ENT8p_0 SID8p_0 NXC8p_0 i8p_0 S8sp_0 SPL8p_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS9iW2.s8bp_0 sd8bp_0 R8bp_0 T8bp_0 He8bp_0 Hchk8bp_0 HT8bp_0 FBC8bp_0 FBT8bp_0 NXC8bp_0 i9p_0 SUp_0 SMp_0 ENTUp_0 SIDUp_0 MRGp_0 s9mp_0 ENTMp_0 SIDMp_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY9 tpY9.
      exact (spine_s9_P 2%nat st0 CST XGL HCST HXGL HCSTM law_die true (C9p W0 st0 4) F9pa_nf F9pb_nf Cert9pa_0 Cert9pb_0 NX9p_0 FGCp_0
               swc_pa scells_pa hcells_pa swc_pb scells_pb hcells_pb s9_pa s9_pb FH_pa_0 FH_pb_0 ok A A' Kc rho rho' (KEEP A) tp Posts HPin HW HUS HKc HokA' HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm8 rhoY9 tpY9). }

  assert (K6 : forall tpY rhoY, triple segs ok (SPA segs (JGb W0 st0 A' Kc rho') (C6 W0 st0 4) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (spine_s6 2%nat st0 4 Cert6_0 k6_0 NTH6s_0 ZC6s_0 s7s_0 ENT7s_0 SID7s_0 G6l_0 W6l_0 D6l_0 NX6l_0 ok A' Kc rho' tpY Q HUS HKc HokA' Hcnt'); [exact (K7 tpY)|].
    intros rhoY6l.
    apply (spine_s6l 2%nat st0 4 Cert6l_0 W6m_0 D6m_0 NX6m_0 s6_0 sd6_0 R6_0 T6_0 He6_0 Hchk6_0 HT6_0 FBC6_0 FBT6_0 ENT6_0 SID6_0 NXC6_0 ok A' Kc rho' tpY Q HUS HKc HokA').
    intros rhoY6b tpY6b.
    apply (spine_s6b 2%nat st0 4 Cert6b_0 s7j_0 ENT7j_0 SID7j_0 ok A' Kc rho' tpY6b Q HUS HKc HokA'). exact (K7 tpY6b). }

  apply (spine_s5 2%nat st0 4 Cert5_0 s6n_0 ENT6n_0 SID6n_0 W5b_0 D5b_0 NX5b_0 F5f64_0 ok A' Kc rho' tp' Q HUS HKc HokA' Hcnt'); [exact (K6 tp')|].
  intros rhoX5b.
  apply (spine_s5b 2%nat st0 4 Cert5b_0 OV1_0 OV2_0 TAB1_0 TAB2_0 W1'_0 W2'_0 D1'_0 D2'_0 NX1'_0 NX2'_0 F1gt_0 F2le_0 F1_64_0 F2_64_0 s1_0 s2_0 ENT1_0 ENT2_0 SID1_0 SID2_0
           ok A' Kc rho' tp' Q HUS HKc HokA').
  intros rhoX5c.
  apply (spine_s5c 2%nat st0 4 Cert5c_0 G5m1_0 W5m1_0 D5m1_0 NX5m1_0 s51_0 sd51_0 R51_0 T51_0 He51_0 Hchk51_0 HT51_0 FBC51_0 FBT51_0 ENT51_0 SID51_0 NXC51_0
           ok A' Kc rho' tp' Q HUS HKc HokA' Hcnt').
  intros rhoX5d tp5d.
  apply (spine_s5d 2%nat st0 4 Cert5d_0 G5m2_0 W5m2_0 D5m2_0 NX5m2_0 s52_0 sd52_0 R52_0 T52_0 He52_0 Hchk52_0 HT52_0 FBC52_0 FBT52_0 ENT52_0 SID52_0 NXC52_0
           ok A' Kc rho' tp5d Q HUS HKc HokA' Hcnt').
  intros rhoX5e tp5e.
  apply (spine_s5e 2%nat st0 4 Cert5e_0 s6j_0 ENT6j_0 SID6j_0 ok A' Kc rho' tp5e Q HUS HKc HokA'). exact (K6 tp5e).
Qed.

Theorem malloc_hit_tail_2 : ltac2:(tb__ "0|0|
ScOF_;S1aS14S0S5S1cQ40A1A1SfVsegs;SdR2R1S19S13VAInv;VCST;VXGL;VW0;Vst0;R4R3A8A5SaS15R4A1S4Vsegs;R7S2R5A1A3S11Vsegs;R8S2R6A1A3S0SbVsegs;RaS3Vsegs;S1bVW0;Vst0;R9R8R7A5S12VW0;Vst0;Z4A3R1R6A5R5A4FrhoX;F_;F_;F_;TQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp. exact (malloc_hit_tail_2_P ok A Kc rho tp (Posts_malloc AE_A AInv CST XGL W0 st0 A Kc) (or_intror (or_introl eq_refl))).
Qed.
End HIT0T.
End MallocHitTail2.

(* [comment removed for export] *)
Module F0A_mL0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "pair"; "false"; "option"; "prod"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be"; "q_L0Be"; "Ebg_L0Be"; "ED_L0Be_1"; "ED_L0Be_2"; "Edr_L0Be"; "TD_L0Be_1"; "TD_L0Be_2"; "Xf_L0Be"; "exits1_L0Be"; "W_L0Be"; "st_L0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l0.F0A_mL0Be"; "PMID_L0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL0Be"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "XI";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require la.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require li.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l9.F0A_qL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.la.F0A_xiL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_dL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.li.F0A_aL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_L0Be : ltac2:(tb__ "0|0|
SbS14S1eS58S1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Dai_L0Be : ltac2:(tb__ "0|5|
SbS1aS1bS17S1bS20S20A2M0A1M1S17S22A1M2A2M3A1S6aS12S6S2S1U0A1M4S0A3A1S58G4S0A2A2S1cG3S18G1G2S13G0S18S20S20S23P18A1S21S6dA1A4S15G0A1A3S15S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_L0Be : ltac2:(tb__ "0|0|
SbS14S1eS5aS1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Wci_L0Be : ltac2:(tb__ "0|0|
SbS14S1eS5bS1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Definition Certi_L0Be__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S5eSaUbb8S55S57U0S0A2A4").
Lemma Certi_L0Be : ltac2:(tb__ "0|1|
SbS14S3bSaUbb8S55S46S57U0M0S0A2S13S10S56S1G0A1S0A2S15S10A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_L0Be__runs); [unfold Certi_L0Be__runs; reflexivity | vmr]. Qed.
Lemma ECerti_L0Be : ltac2:(tb__ "0|2|
SbS14S3cSaUbb8S55S46S59U0M0S0A2S13S39S3aS56S1G0A1S0A2Z0M1S21G1A1A3S15S39A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_L0Be__runs); [unfold Certi_L0Be__runs; reflexivity | vmr]. Qed.

Definition PMID_L0Be : axst := ltac2:(tb__ "0|0|
S62S19S2dS2eS24A4").
Definition Cert1m_L0Be__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S5eSaS5dS13S9S5cS15S9A1A3S13S10S3dS15S10A1A3A4").
Lemma Cert1m_L0Be : ltac2:(tb__ "0|0|
SbS14S3bSaS5dS13S9S5cS15S9A1A3S46S13S10S3dS15S10A1A3S2cA6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_L0Be] exits1_L0Be Cert1m_L0Be__runs); [unfold Cert1m_L0Be__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_L0Be : ltac2:(tb__ "0|2|
SbS14S3cSaS5dS13S9S5cS15S9A1A3S46S13S39S3aS3dZ1S21Z0M0A1M1A3S15S39A1A3S69S10S39S10S3aR1G0G1A3LE;S2cA4A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_L0Be 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_L0Be) Cert1m_L0Be__runs); [unfold Cert1m_L0Be__runs; reflexivity | vmr]. Qed.

Lemma Wbm_L0Be : ltac2:(tb__ "0|0|
SbS14S1eS63S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wcm_L0Be : ltac2:(tb__ "0|0|
SbS14S1eS64S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wdm_L0Be : ltac2:(tb__ "0|0|
SbS14S1eS65S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma XIm_L0Be : ltac2:(tb__ "0|2|
SbS1aS10A1S6cS66S19S1U0M0A1M1S0S24A4S70G0S24A2A2S1cS10S62S19G1S0S24A4A2A3"). Proof. vmr. Qed.

Section ML0Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S4cU0S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_L0Be : ltac2:(tb__ "0|1|
S9OF_;S52OF_;S4dS4S1dS1dS17S4fQ40A1A1S51S5R5A1S45Vsegs;R8S44R6A1A3S49R6R5A2S4aU0M0S0RbRaR9R8R6S26S29R4AaS4aG0S0RcRbRaR9R7S27S2aR5AaS47RdRcRbRaR8S25R6A7S47ReRdRcRbR9S28R7A7S47RfReRdRcRaS2bR8A7S1dS54Vsegs;R10S43Vsegs;VJFi;S16RfReRcA4S3dR1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L0Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L0Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_L0Be C3_L0Be Ems_L0Be C4_L0Be TM0_L0Be run4_L0Be RM_L0Be D3_L0Be W3_L0Be EQ3_L0Be NX3b_L0Be RUN4_L0Be L4_L0Be D4_L0Be W4_L0Be EQ4_L0Be
             HeM_L0Be HchkM_L0Be HTM_L0Be FBM_L0Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L0Be.
    apply (f0_s5 0%nat st q_L0Be false TM_L0Be Eq_L0Be EQ_L0Be TQ0_L0Be run5_L0Be RQ_L0Be NX5_L0Be RUN5_L0Be L5_L0Be AXQ_L0Be HeQ_L0Be HchkQ_L0Be HTQ_L0Be FBQ_L0Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L0Be.
    apply (f0_s6 0%nat st false TQ_L0Be Edr_L0Be Xf_L0Be run6_L0Be NX6_L0Be RUN6_L0Be L6_L0Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 0%nat st true PMID_L0Be exits1_L0Be Cert1m_L0Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L0Be in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_L0Be_1 C2_L0Be_1 EfD_L0Be_1 ED_L0Be_1 run2_L0Be_1 D2_L0Be_1 W2_L0Be_1 NX2_L0Be_1 EQ2_L0Be_1 RUN2_L0Be_1 L2_L0Be_1 AXD_L0Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0Be_1 TDr_L0Be_1 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_1 ENTD_L0Be_1 RUN3_L0Be L3_L0Be NX3_L0Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_L0Be_2 C2_L0Be_2 EfD_L0Be_2 ED_L0Be_2 run2_L0Be_2 D2_L0Be_2 W2_L0Be_2 NX2_L0Be_2 EQ2_L0Be_2 RUN2_L0Be_2 L2_L0Be_2 AXD_L0Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0Be_2 TDr_L0Be_2 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_2 ENTD_L0Be_2 RUN3_L0Be L3_L0Be NX3_L0Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_L0Be : ltac2:(tb__ "0|1|
S9OF_;S4dS4S1dS1dS17S4fQ40A1A1S52OF_;S5R5A1S49R5R4A2S4bU0M0S0R9R8R7R5S26S29R3A9S4bG0S0RaR9R8R6S27S2aR4A9S48RbRaR9R7S25R5A6S48RcRbRaR8S28R6A6S48RdRcRbR9S2bR7A6S1dS53Vsegs;S43Vsegs;VJFi;S16ReRdRbA4S3dR1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L0Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L0Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_L0Be C3_L0Be Ems_L0Be C4_L0Be TM0_L0Be run4_L0Be RM_L0Be D3_L0Be W3_L0Be EQ3_L0Be NX3b_L0Be RUN4_L0Be L4_L0Be D4_L0Be W4_L0Be EQ4_L0Be
             HeM_L0Be HchkM_L0Be HTM_L0Be FBM_L0Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L0Be.
    apply (ef0_s5 0%nat st q_L0Be false TM_L0Be Eq_L0Be EQ_L0Be TQ0_L0Be run5_L0Be RQ_L0Be NX5_L0Be RUN5_L0Be L5_L0Be AXQ_L0Be HeQ_L0Be HchkQ_L0Be HTQ_L0Be FBQ_L0Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L0Be.
    apply (ef0_s6 0%nat st false TQ_L0Be Edr_L0Be Xf_L0Be run6_L0Be NX6_L0Be RUN6_L0Be L6_L0Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 0%nat st true PMID_L0Be exits1_L0Be (eq_refl : (GW <=? ss_next (ax_S PMID_L0Be))%positive = true) ECert1m_L0Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L0Be in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_L0Be_1 C2_L0Be_1 EfD_L0Be_1 ED_L0Be_1 run2_L0Be_1 D2_L0Be_1 W2_L0Be_1 NX2_L0Be_1 EQ2_L0Be_1 RUN2_L0Be_1 L2_L0Be_1 AXD_L0Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0Be_1 TDr_L0Be_1 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_1 ENTD_L0Be_1 RUN3_L0Be L3_L0Be NX3_L0Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_L0Be_2 C2_L0Be_2 EfD_L0Be_2 ED_L0Be_2 run2_L0Be_2 D2_L0Be_2 W2_L0Be_2 NX2_L0Be_2 EQ2_L0Be_2 RUN2_L0Be_2 L2_L0Be_2 AXD_L0Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0Be_2 TDr_L0Be_2 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_2 ENTD_L0Be_2 RUN3_L0Be L3_L0Be NX3_L0Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SfS3eS71R2A2ScS3fS37R2A2S40R2S38A2A2A2SeF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SdS73R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SdS72R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2ScSdScS3fS37R2A2S40R2S38A2A2A1SdScS3fZ17db48R2A2S40R2Z17db4cA2A2A1A2F_;Fa;").

Theorem free_lo_ia0_0Be : ltac2:(tb__ "0|7|
S52OF_;S4dS4S1dS17S4fQ40M0A1A1S50G0S1fR2PcA2A2S9S50G0S1fR3PdA2A2S9S30SaS42R4R3S13S1bS10S2fA2M1S18S10S2fS8S2S1U0A1M2S0A3M3S3S36SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S51S5R6A1S45SaR9S44R7A1A3S6bSaRaS44R8A1A3S3fS41R6R5A2S67A2SbS14S4eRbA1S19A3S34S24RcA2S1dS9S33S61R10S31R10ReRcRbR2R1A6R3A3S60S35R11A1R4RdRcR3R2A6SbS9S32R3A1S68A3S49R6S31S35R13A1R6RfReR5R4A6A2S47S5fVCST;VXGL;S35R14A1M6A3R15G6R13S31G6R7R10RfR6R5A6S25S30SaS42R7R11S13G1S18S10S2fG3S3G4VCST;VXGL;G6R13A5A4G5A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S6eRfRdA2S54SaR10S43SaS7G4G2S0RfReA5S6S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 0 Wai_L0Be Dai_L0Be Wbi_L0Be Wci_L0Be Certi_L0Be ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 0) UStopLe q_L0Be (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe q_L0Be HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid false 0 UStopLe q_L0Be Wbm_L0Be Wcm_L0Be Wdm_L0Be Fb_L0Be XIm_L0Be A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_L0Be (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_L0Be_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L0Be_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_L0Be CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_L0Be CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_ia0_0Be : ltac2:(tb__ "0|7|
S4dS4S1dS17S4fQ40M0A1A1S50G0S1fR2PcA2A2S9S50G0S1fR3PdA2A2S9S30SaS42R4R3S13S1bS10S2fA2M1S18S10S2fS8S2S1U0A1M2S0A3M3S3S36SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S51S5R6A1S3fS41R4R3A2S67A2SbS14S4eR9A1S19A3S34S24RaA2S1dS9S33S61ReS31ReRcRaR9R2R1A6R3A3S60S35RfA1R4RbRaR3R2A6SbS9S32R3A1S68A3S49R6S31S35R11A1R6RdRcR5R4A6A2S48S5fVCST;VXGL;S35R12A1M6A3G6R11S31G6R7ReRdR6R5A6S25S30SaS42R7RfS13G1S18S10S2fG3S3G4VCST;VXGL;G6R11A5A4G5A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S6fRbA1S53SaS43SaS7G4G2S0RdRcA5S6S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 0 Wai_L0Be Dai_L0Be Wbi_L0Be Wci_L0Be ECerti_L0Be A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 0) UStopLe q_L0Be (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe q_L0Be HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid false 0 UStopLe q_L0Be Wbm_L0Be Wcm_L0Be Wdm_L0Be Fb_L0Be XIm_L0Be A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_L0Be (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_L0Be_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L0Be_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_L0Be CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_L0Be CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ML0Be.
End F0A_mL0Be.

(* [comment removed for export] *)
Module F0A_mL0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "pair"; "false"; "option"; "prod"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0A"; "q_L0A"; "Ebg_L0A"; "ED_L0A_1"; "ED_L0A_2"; "Edr_L0A"; "TD_L0A_1"; "TD_L0A_2"; "Xf_L0A"; "exits1_L0A"; "W_L0A"; "st_L0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l0.F0A_mL0A"; "PMID_L0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL0A"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "XI";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require la.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require li.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l9.F0A_qL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.la.F0A_xiL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_dL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.li.F0A_aL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_L0A : ltac2:(tb__ "0|0|
SbS14S1eS58S1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Dai_L0A : ltac2:(tb__ "0|5|
SbS1aS1bS17S1bS20S20A2M0A1M1S17S22A1M2A2M3A1S6aS12S6S2S1U0A1M4S0A3A1S58G4S0A2A2S1cG3S18G1G2S13G0S18S20S20S23P18A1S21S6dA1A4S15G0A1A3S15S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_L0A : ltac2:(tb__ "0|0|
SbS14S1eS5aS1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Wci_L0A : ltac2:(tb__ "0|0|
SbS14S1eS5bS1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Definition Certi_L0A__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S5eSaUbb8S55S57U0S0A2A4").
Lemma Certi_L0A : ltac2:(tb__ "0|1|
SbS14S3bSaUbb8S55S46S57U0M0S0A2S13S10S56S1G0A1S0A2S15S10A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_L0A__runs); [unfold Certi_L0A__runs; reflexivity | vmr]. Qed.
Lemma ECerti_L0A : ltac2:(tb__ "0|2|
SbS14S3cSaUbb8S55S46S59U0M0S0A2S13S39S3aS56S1G0A1S0A2Z0M1S21G1A1A3S15S39A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_L0A__runs); [unfold Certi_L0A__runs; reflexivity | vmr]. Qed.

Definition PMID_L0A : axst := ltac2:(tb__ "0|0|
S62S19S2dS2eS24A4").
Definition Cert1m_L0A__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S5eSaS5dS13S9S5cS15S9A1A3S13S10S3dS15S10A1A3A4").
Lemma Cert1m_L0A : ltac2:(tb__ "0|0|
SbS14S3bSaS5dS13S9S5cS15S9A1A3S46S13S10S3dS15S10A1A3S2cA6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_L0A] exits1_L0A Cert1m_L0A__runs); [unfold Cert1m_L0A__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_L0A : ltac2:(tb__ "0|2|
SbS14S3cSaS5dS13S9S5cS15S9A1A3S46S13S39S3aS3dZ1S21Z0M0A1M1A3S15S39A1A3S69S10S39S10S3aR1G0G1A3LE;S2cA4A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_L0A 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_L0A) Cert1m_L0A__runs); [unfold Cert1m_L0A__runs; reflexivity | vmr]. Qed.

Lemma Wbm_L0A : ltac2:(tb__ "0|0|
SbS14S1eS63S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wcm_L0A : ltac2:(tb__ "0|0|
SbS14S1eS64S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wdm_L0A : ltac2:(tb__ "0|0|
SbS14S1eS65S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma XIm_L0A : ltac2:(tb__ "0|2|
SbS1aS10A1S6cS66S19S1U0M0A1M1S0S24A4S70G0S24A2A2S1cS10S62S19G1S0S24A4A2A3"). Proof. vmr. Qed.

Section ML0A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S4cU0S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_L0A : ltac2:(tb__ "0|1|
S9OF_;S52OF_;S4dS4S1dS1dS17S4fQ40A1A1S51S5R5A1S45Vsegs;R8S44R6A1A3S49R6R5A2S4aU0M0S0RbRaR9R8R6S26S29R4AaS4aG0S0RcRbRaR9R7S27S2aR5AaS47RdRcRbRaR8S25R6A7S47ReRdRcRbR9S28R7A7S47RfReRdRcRaS2bR8A7S1dS54Vsegs;R10S43Vsegs;VJFi;S16RfReRcA4S3dR1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L0A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L0A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_L0A C3_L0A Ems_L0A C4_L0A TM0_L0A run4_L0A RM_L0A D3_L0A W3_L0A EQ3_L0A NX3b_L0A RUN4_L0A L4_L0A D4_L0A W4_L0A EQ4_L0A
             HeM_L0A HchkM_L0A HTM_L0A FBM_L0A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L0A.
    apply (f0_s5 0%nat st q_L0A false TM_L0A Eq_L0A EQ_L0A TQ0_L0A run5_L0A RQ_L0A NX5_L0A RUN5_L0A L5_L0A AXQ_L0A HeQ_L0A HchkQ_L0A HTQ_L0A FBQ_L0A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L0A.
    apply (f0_s6 0%nat st false TQ_L0A Edr_L0A Xf_L0A run6_L0A NX6_L0A RUN6_L0A L6_L0A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 0%nat st true PMID_L0A exits1_L0A Cert1m_L0A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L0A in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_L0A_1 C2_L0A_1 EfD_L0A_1 ED_L0A_1 run2_L0A_1 D2_L0A_1 W2_L0A_1 NX2_L0A_1 EQ2_L0A_1 RUN2_L0A_1 L2_L0A_1 AXD_L0A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0A_1 TDr_L0A_1 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_1 ENTD_L0A_1 RUN3_L0A L3_L0A NX3_L0A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_L0A_2 C2_L0A_2 EfD_L0A_2 ED_L0A_2 run2_L0A_2 D2_L0A_2 W2_L0A_2 NX2_L0A_2 EQ2_L0A_2 RUN2_L0A_2 L2_L0A_2 AXD_L0A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0A_2 TDr_L0A_2 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_2 ENTD_L0A_2 RUN3_L0A L3_L0A NX3_L0A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_L0A : ltac2:(tb__ "0|1|
S9OF_;S4dS4S1dS1dS17S4fQ40A1A1S52OF_;S5R5A1S49R5R4A2S4bU0M0S0R9R8R7R5S26S29R3A9S4bG0S0RaR9R8R6S27S2aR4A9S48RbRaR9R7S25R5A6S48RcRbRaR8S28R6A6S48RdRcRbR9S2bR7A6S1dS53Vsegs;S43Vsegs;VJFi;S16ReRdRbA4S3dR1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L0A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L0A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_L0A C3_L0A Ems_L0A C4_L0A TM0_L0A run4_L0A RM_L0A D3_L0A W3_L0A EQ3_L0A NX3b_L0A RUN4_L0A L4_L0A D4_L0A W4_L0A EQ4_L0A
             HeM_L0A HchkM_L0A HTM_L0A FBM_L0A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L0A.
    apply (ef0_s5 0%nat st q_L0A false TM_L0A Eq_L0A EQ_L0A TQ0_L0A run5_L0A RQ_L0A NX5_L0A RUN5_L0A L5_L0A AXQ_L0A HeQ_L0A HchkQ_L0A HTQ_L0A FBQ_L0A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L0A.
    apply (ef0_s6 0%nat st false TQ_L0A Edr_L0A Xf_L0A run6_L0A NX6_L0A RUN6_L0A L6_L0A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 0%nat st true PMID_L0A exits1_L0A (eq_refl : (GW <=? ss_next (ax_S PMID_L0A))%positive = true) ECert1m_L0A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L0A in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_L0A_1 C2_L0A_1 EfD_L0A_1 ED_L0A_1 run2_L0A_1 D2_L0A_1 W2_L0A_1 NX2_L0A_1 EQ2_L0A_1 RUN2_L0A_1 L2_L0A_1 AXD_L0A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0A_1 TDr_L0A_1 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_1 ENTD_L0A_1 RUN3_L0A L3_L0A NX3_L0A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_L0A_2 C2_L0A_2 EfD_L0A_2 ED_L0A_2 run2_L0A_2 D2_L0A_2 W2_L0A_2 NX2_L0A_2 EQ2_L0A_2 RUN2_L0A_2 L2_L0A_2 AXD_L0A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0A_2 TDr_L0A_2 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_2 ENTD_L0A_2 RUN3_L0A L3_L0A NX3_L0A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SfS3eS71R2A2ScS3fS37R2A2S40R2S38A2A2A2SeF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SdS73R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SdS72R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2ScSdScS3fS37R2A2S40R2S38A2A2A1SdScS3fZ17db48R2A2S40R2Z17db4cA2A2A1A2F_;Fa;").

Theorem free_lo_ia0_0A : ltac2:(tb__ "0|7|
S52OF_;S4dS4S1dS17S4fQ40M0A1A1S50G0S1fR2PcA2A2S9S50G0S1fR3PdA2A2S9S30SaS42R4R3S13S1bS10S2fA2M1S18S10S2fS8S2S1U0A1M2S0A3M3S3S36SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S51S5R6A1S45SaR9S44R7A1A3S6bSaRaS44R8A1A3S3fS41R6R5A2S67A2SbS14S4eRbA1S19A3S34S24RcA2S1dS9S33S61R10S31R10ReRcRbR2R1A6R3A3S60S35R11A1R4RdRcR3R2A6SbS9S32R3A1S68A3S49R6S31S35R13A1R6RfReR5R4A6A2S47S5fVCST;VXGL;S35R14A1M6A3R15G6R13S31G6R7R10RfR6R5A6S25S30SaS42R7R11S13G1S18S10S2fG3S3G4VCST;VXGL;G6R13A5A4G5A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S6eRfRdA2S54SaR10S43SaS7G4G2S0RfReA5S6S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 0 Wai_L0A Dai_L0A Wbi_L0A Wci_L0A Certi_L0A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 0) UStopLe q_L0A (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe q_L0A HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid false 0 UStopLe q_L0A Wbm_L0A Wcm_L0A Wdm_L0A Fb_L0A XIm_L0A A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_L0A (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_L0A_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L0A_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_L0A CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_L0A CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_ia0_0A : ltac2:(tb__ "0|7|
S4dS4S1dS17S4fQ40M0A1A1S50G0S1fR2PcA2A2S9S50G0S1fR3PdA2A2S9S30SaS42R4R3S13S1bS10S2fA2M1S18S10S2fS8S2S1U0A1M2S0A3M3S3S36SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S51S5R6A1S3fS41R4R3A2S67A2SbS14S4eR9A1S19A3S34S24RaA2S1dS9S33S61ReS31ReRcRaR9R2R1A6R3A3S60S35RfA1R4RbRaR3R2A6SbS9S32R3A1S68A3S49R6S31S35R11A1R6RdRcR5R4A6A2S48S5fVCST;VXGL;S35R12A1M6A3G6R11S31G6R7ReRdR6R5A6S25S30SaS42R7RfS13G1S18S10S2fG3S3G4VCST;VXGL;G6R11A5A4G5A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S6fRbA1S53SaS43SaS7G4G2S0RdRcA5S6S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 0 Wai_L0A Dai_L0A Wbi_L0A Wci_L0A ECerti_L0A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 0) UStopLe q_L0A (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe q_L0A HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid false 0 UStopLe q_L0A Wbm_L0A Wcm_L0A Wdm_L0A Fb_L0A XIm_L0A A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_L0A (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_L0A_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L0A_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_L0A CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_L0A CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ML0A.
End F0A_mL0A.

(* [comment removed for export] *)
Module F0A_mL0Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "pair"; "false"; "option"; "prod"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf"; "q_L0Bf"; "Ebg_L0Bf"; "ED_L0Bf_1"; "ED_L0Bf_2"; "Edr_L0Bf"; "TD_L0Bf_1"; "TD_L0Bf_2"; "Xf_L0Bf"; "exits1_L0Bf"; "W_L0Bf"; "st_L0Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l0.F0A_mL0Bf"; "PMID_L0Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL0Bf"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "XI";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require la.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require li.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l9.F0A_qL0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.la.F0A_xiL0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_dL0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.li.F0A_aL0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_L0Bf : ltac2:(tb__ "0|0|
SbS14S1eS58S1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Dai_L0Bf : ltac2:(tb__ "0|5|
SbS1aS1bS17S1bS20S20A2M0A1M1S17S22A1M2A2M3A1S6aS12S6S2S1U0A1M4S0A3A1S58G4S0A2A2S1cG3S18G1G2S13G0S18S20S20S23P18A1S21S6dA1A4S15G0A1A3S15S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_L0Bf : ltac2:(tb__ "0|0|
SbS14S1eS5aS1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Wci_L0Bf : ltac2:(tb__ "0|0|
SbS14S1eS5bS1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Definition Certi_L0Bf__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S5eSaUbb8S55S57U0S0A2A4").
Lemma Certi_L0Bf : ltac2:(tb__ "0|1|
SbS14S3bSaUbb8S55S46S57U0M0S0A2S13S10S56S1G0A1S0A2S15S10A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_L0Bf__runs); [unfold Certi_L0Bf__runs; reflexivity | vmr]. Qed.
Lemma ECerti_L0Bf : ltac2:(tb__ "0|2|
SbS14S3cSaUbb8S55S46S59U0M0S0A2S13S39S3aS56S1G0A1S0A2Z0M1S21G1A1A3S15S39A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_L0Bf__runs); [unfold Certi_L0Bf__runs; reflexivity | vmr]. Qed.

Definition PMID_L0Bf : axst := ltac2:(tb__ "0|0|
S62S19S2dS2eS24A4").
Definition Cert1m_L0Bf__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S5eSaS5dS13S9S5cS15S9A1A3S13S10S3dS15S10A1A3A4").
Lemma Cert1m_L0Bf : ltac2:(tb__ "0|0|
SbS14S3bSaS5dS13S9S5cS15S9A1A3S46S13S10S3dS15S10A1A3S2cA6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_L0Bf] exits1_L0Bf Cert1m_L0Bf__runs); [unfold Cert1m_L0Bf__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_L0Bf : ltac2:(tb__ "0|2|
SbS14S3cSaS5dS13S9S5cS15S9A1A3S46S13S39S3aS3dZ1S21Z0M0A1M1A3S15S39A1A3S69S10S39S10S3aR1G0G1A3LE;S2cA4A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_L0Bf 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_L0Bf) Cert1m_L0Bf__runs); [unfold Cert1m_L0Bf__runs; reflexivity | vmr]. Qed.

Lemma Wbm_L0Bf : ltac2:(tb__ "0|0|
SbS14S1eS63S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wcm_L0Bf : ltac2:(tb__ "0|0|
SbS14S1eS64S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wdm_L0Bf : ltac2:(tb__ "0|0|
SbS14S1eS65S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma XIm_L0Bf : ltac2:(tb__ "0|2|
SbS1aS10A1S6cS66S19S1U0M0A1M1S0S24A4S70G0S24A2A2S1cS10S62S19G1S0S24A4A2A3"). Proof. vmr. Qed.

Section ML0Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S4cU0S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_L0Bf : ltac2:(tb__ "0|1|
S9OF_;S52OF_;S4dS4S1dS1dS17S4fQ40A1A1S51S5R5A1S45Vsegs;R8S44R6A1A3S49R6R5A2S4aU0M0S0RbRaR9R8R6S26S29R4AaS4aG0S0RcRbRaR9R7S27S2aR5AaS47RdRcRbRaR8S25R6A7S47ReRdRcRbR9S28R7A7S47RfReRdRcRaS2bR8A7S1dS54Vsegs;R10S43Vsegs;VJFi;S16RfReRcA4S3dR1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L0Bf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L0Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_L0Bf C3_L0Bf Ems_L0Bf C4_L0Bf TM0_L0Bf run4_L0Bf RM_L0Bf D3_L0Bf W3_L0Bf EQ3_L0Bf NX3b_L0Bf RUN4_L0Bf L4_L0Bf D4_L0Bf W4_L0Bf EQ4_L0Bf
             HeM_L0Bf HchkM_L0Bf HTM_L0Bf FBM_L0Bf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L0Bf.
    apply (f0_s5 0%nat st q_L0Bf false TM_L0Bf Eq_L0Bf EQ_L0Bf TQ0_L0Bf run5_L0Bf RQ_L0Bf NX5_L0Bf RUN5_L0Bf L5_L0Bf AXQ_L0Bf HeQ_L0Bf HchkQ_L0Bf HTQ_L0Bf FBQ_L0Bf
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L0Bf.
    apply (f0_s6 0%nat st false TQ_L0Bf Edr_L0Bf Xf_L0Bf run6_L0Bf NX6_L0Bf RUN6_L0Bf L6_L0Bf ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 0%nat st true PMID_L0Bf exits1_L0Bf Cert1m_L0Bf ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L0Bf in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_L0Bf_1 C2_L0Bf_1 EfD_L0Bf_1 ED_L0Bf_1 run2_L0Bf_1 D2_L0Bf_1 W2_L0Bf_1 NX2_L0Bf_1 EQ2_L0Bf_1 RUN2_L0Bf_1 L2_L0Bf_1 AXD_L0Bf_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0Bf_1 TDr_L0Bf_1 CD_L0Bf Eps_L0Bf Ebg_L0Bf run3_L0Bf AXDr_L0Bf_1 ENTD_L0Bf_1 RUN3_L0Bf L3_L0Bf NX3_L0Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_L0Bf_2 C2_L0Bf_2 EfD_L0Bf_2 ED_L0Bf_2 run2_L0Bf_2 D2_L0Bf_2 W2_L0Bf_2 NX2_L0Bf_2 EQ2_L0Bf_2 RUN2_L0Bf_2 L2_L0Bf_2 AXD_L0Bf_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0Bf_2 TDr_L0Bf_2 CD_L0Bf Eps_L0Bf Ebg_L0Bf run3_L0Bf AXDr_L0Bf_2 ENTD_L0Bf_2 RUN3_L0Bf L3_L0Bf NX3_L0Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_L0Bf : ltac2:(tb__ "0|1|
S9OF_;S4dS4S1dS1dS17S4fQ40A1A1S52OF_;S5R5A1S49R5R4A2S4bU0M0S0R9R8R7R5S26S29R3A9S4bG0S0RaR9R8R6S27S2aR4A9S48RbRaR9R7S25R5A6S48RcRbRaR8S28R6A6S48RdRcRbR9S2bR7A6S1dS53Vsegs;S43Vsegs;VJFi;S16ReRdRbA4S3dR1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L0Bf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L0Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_L0Bf C3_L0Bf Ems_L0Bf C4_L0Bf TM0_L0Bf run4_L0Bf RM_L0Bf D3_L0Bf W3_L0Bf EQ3_L0Bf NX3b_L0Bf RUN4_L0Bf L4_L0Bf D4_L0Bf W4_L0Bf EQ4_L0Bf
             HeM_L0Bf HchkM_L0Bf HTM_L0Bf FBM_L0Bf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L0Bf.
    apply (ef0_s5 0%nat st q_L0Bf false TM_L0Bf Eq_L0Bf EQ_L0Bf TQ0_L0Bf run5_L0Bf RQ_L0Bf NX5_L0Bf RUN5_L0Bf L5_L0Bf AXQ_L0Bf HeQ_L0Bf HchkQ_L0Bf HTQ_L0Bf FBQ_L0Bf
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L0Bf.
    apply (ef0_s6 0%nat st false TQ_L0Bf Edr_L0Bf Xf_L0Bf run6_L0Bf NX6_L0Bf RUN6_L0Bf L6_L0Bf A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 0%nat st true PMID_L0Bf exits1_L0Bf (eq_refl : (GW <=? ss_next (ax_S PMID_L0Bf))%positive = true) ECert1m_L0Bf A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L0Bf in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_L0Bf_1 C2_L0Bf_1 EfD_L0Bf_1 ED_L0Bf_1 run2_L0Bf_1 D2_L0Bf_1 W2_L0Bf_1 NX2_L0Bf_1 EQ2_L0Bf_1 RUN2_L0Bf_1 L2_L0Bf_1 AXD_L0Bf_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0Bf_1 TDr_L0Bf_1 CD_L0Bf Eps_L0Bf Ebg_L0Bf run3_L0Bf AXDr_L0Bf_1 ENTD_L0Bf_1 RUN3_L0Bf L3_L0Bf NX3_L0Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_L0Bf_2 C2_L0Bf_2 EfD_L0Bf_2 ED_L0Bf_2 run2_L0Bf_2 D2_L0Bf_2 W2_L0Bf_2 NX2_L0Bf_2 EQ2_L0Bf_2 RUN2_L0Bf_2 L2_L0Bf_2 AXD_L0Bf_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0Bf_2 TDr_L0Bf_2 CD_L0Bf Eps_L0Bf Ebg_L0Bf run3_L0Bf AXDr_L0Bf_2 ENTD_L0Bf_2 RUN3_L0Bf L3_L0Bf NX3_L0Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SfS3eS71R2A2ScS3fS37R2A2S40R2S38A2A2A2SeF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SdS73R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SdS72R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2ScSdScS3fS37R2A2S40R2S38A2A2A1SdScS3fZ17db48R2A2S40R2Z17db4cA2A2A1A2F_;Fa;").

Theorem free_lo_ia0_0Bf : ltac2:(tb__ "0|7|
S52OF_;S4dS4S1dS17S4fQ40M0A1A1S50G0S1fR2PcA2A2S9S50G0S1fR3PdA2A2S9S30SaS42R4R3S13S1bS10S2fA2M1S18S10S2fS8S2S1U0A1M2S0A3M3S3S36SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S51S5R6A1S45SaR9S44R7A1A3S6bSaRaS44R8A1A3S3fS41R6R5A2S67A2SbS14S4eRbA1S19A3S34S24RcA2S1dS9S33S61R10S31R10ReRcRbR2R1A6R3A3S60S35R11A1R4RdRcR3R2A6SbS9S32R3A1S68A3S49R6S31S35R13A1R6RfReR5R4A6A2S47S5fVCST;VXGL;S35R14A1M6A3R15G6R13S31G6R7R10RfR6R5A6S25S30SaS42R7R11S13G1S18S10S2fG3S3G4VCST;VXGL;G6R13A5A4G5A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S6eRfRdA2S54SaR10S43SaS7G4G2S0RfReA5S6S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 0 Wai_L0Bf Dai_L0Bf Wbi_L0Bf Wci_L0Bf Certi_L0Bf ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 0) UStopLe q_L0Bf (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe q_L0Bf HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid false 0 UStopLe q_L0Bf Wbm_L0Bf Wcm_L0Bf Wdm_L0Bf Fb_L0Bf XIm_L0Bf A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_L0Bf (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_L0Bf_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L0Bf_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_L0Bf CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_L0Bf CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_ia0_0Bf : ltac2:(tb__ "0|7|
S4dS4S1dS17S4fQ40M0A1A1S50G0S1fR2PcA2A2S9S50G0S1fR3PdA2A2S9S30SaS42R4R3S13S1bS10S2fA2M1S18S10S2fS8S2S1U0A1M2S0A3M3S3S36SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S51S5R6A1S3fS41R4R3A2S67A2SbS14S4eR9A1S19A3S34S24RaA2S1dS9S33S61ReS31ReRcRaR9R2R1A6R3A3S60S35RfA1R4RbRaR3R2A6SbS9S32R3A1S68A3S49R6S31S35R11A1R6RdRcR5R4A6A2S48S5fVCST;VXGL;S35R12A1M6A3G6R11S31G6R7ReRdR6R5A6S25S30SaS42R7RfS13G1S18S10S2fG3S3G4VCST;VXGL;G6R11A5A4G5A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S6fRbA1S53SaS43SaS7G4G2S0RdRcA5S6S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 0 Wai_L0Bf Dai_L0Bf Wbi_L0Bf Wci_L0Bf ECerti_L0Bf A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 0) UStopLe q_L0Bf (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe q_L0Bf HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid false 0 UStopLe q_L0Bf Wbm_L0Bf Wcm_L0Bf Wdm_L0Bf Fb_L0Bf XIm_L0Bf A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_L0Bf (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_L0Bf_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L0Bf_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_L0Bf CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_L0Bf CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ML0Bf.
End F0A_mL0Bf.

(* [comment removed for export] *)
Module F0A_mL1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "pair"; "false"; "option"; "prod"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL1A"; "q_L1A"; "Ebg_L1A"; "ED_L1A_1"; "ED_L1A_2"; "ED_L1A_3"; "Edr_L1A"; "TD_L1A_1"; "TD_L1A_2"; "TD_L1A_3"; "Xf_L1A"; "exits1_L1A"; "W_L1A"; "st_L1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l0.F0A_mL1A"; "PMID_L1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL1A"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst";
"XI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require li.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.F0A_qL1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lb.F0A_xiL1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kl.F0A_dL1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.li.F0A_aL1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL1A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_L1A : ltac2:(tb__ "0|0|
SbS14S1eS5aS1U1A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Dai_L1A : ltac2:(tb__ "0|5|
SbS1aS1bS17S1bS20S20A2M0A1M1S17S22A1M2A2M3A1S6cS12S6S2S1U1A1M4S0A3A1S5aG4S0A2A2S1cG3S18G1G2S13G0S18S20S20S23P18A1S21S6fA1A4S15G0A1A3S15S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_L1A : ltac2:(tb__ "0|0|
SbS14S1eS5cS1U1A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Wci_L1A : ltac2:(tb__ "0|0|
SbS14S1eS5dS1U1A1S0A2A1S16A3"). Proof. vmr. Qed.
Definition Certi_L1A__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S60SaUbb8S57S59U1S0A2A4").
Lemma Certi_L1A : ltac2:(tb__ "0|1|
SbS14S3dSaUbb8S57S48S59U1M0S0A2S13S10S58S1G0A1S0A2S15S10A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 1 UStopLe) [MIDx (Wcan 1) UStopLe] Certi_L1A__runs); [unfold Certi_L1A__runs; reflexivity | vmr]. Qed.
Lemma ECerti_L1A : ltac2:(tb__ "0|2|
SbS14S3eSaUbb8S57S48S5bU1M0S0A2S13S3bS3cS58S1G0A1S0A2Z0M1S21G1A1A3S15S3bA1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 1 UStopLe) [mkVNA (MIDx (Wcan 1) UStopLe) 0 (SLit 0)] Certi_L1A__runs); [unfold Certi_L1A__runs; reflexivity | vmr]. Qed.

Definition PMID_L1A : axst := ltac2:(tb__ "0|0|
S64S19S2fS30S24A4").
Definition Cert1m_L1A__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S60SaS5fS13S9S5eS15S9A1A3S13S10S3fS15S10A1A3A4").
Lemma Cert1m_L1A : ltac2:(tb__ "0|0|
SbS14S3dSaS5fS13S9S5eS15S9A1A3S48S13S10S3fS15S10A1A3S2eA6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_L1A] exits1_L1A Cert1m_L1A__runs); [unfold Cert1m_L1A__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_L1A : ltac2:(tb__ "0|2|
SbS14S3eSaS5fS13S9S5eS15S9A1A3S48S13S3bS3cS3fZ1S21Z0M0A1M1A3S15S3bA1A3S6bS10S3bS10S3cR1G0G1A3LE;S2eA4A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_L1A 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_L1A) Cert1m_L1A__runs); [unfold Cert1m_L1A__runs; reflexivity | vmr]. Qed.

Lemma Wbm_L1A : ltac2:(tb__ "0|0|
SbS14S1eS65S1U1A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wcm_L1A : ltac2:(tb__ "0|0|
SbS14S1eS66S1U1A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wdm_L1A : ltac2:(tb__ "0|0|
SbS14S1eS67S1U1A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma XIm_L1A : ltac2:(tb__ "0|2|
SbS1aS10A1S6eS68S19S1U1M0A1M1S0S24A4S72G0S24A2A2S1cS10S64S19G1S0S24A4A2A3"). Proof. vmr. Qed.

Section ML1A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 1.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S4eU1S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_L1A : ltac2:(tb__ "0|1|
S9OF_;S54OF_;S4fS4S1dS1dS17S51Q40A1A1S53S5R5A1S47Vsegs;R8S46R6A1A3S4bR6R5A2S4cU1M0S0RbRaR9R8R6S26S2aR4AaS4cG0S0RcRbRaR9R7S27S2bR5AaS4cG0S0RdRcRbRaR8S28S2cR6AaS49ReRdRcRbR9S25R7A7S49RfReRdRcRaS29R8A7S49R10RfReRdRbS2dR9A7S1dS56Vsegs;R11S45Vsegs;VJFi;S16R10RfRdA4S3fR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L1A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L1A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1%nat st false Eps_L1A C3_L1A Ems_L1A C4_L1A TM0_L1A run4_L1A RM_L1A D3_L1A W3_L1A EQ3_L1A NX3b_L1A RUN4_L1A L4_L1A D4_L1A W4_L1A EQ4_L1A
             HeM_L1A HchkM_L1A HTM_L1A FBM_L1A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L1A.
    apply (f0_s5 1%nat st q_L1A false TM_L1A Eq_L1A EQ_L1A TQ0_L1A run5_L1A RQ_L1A NX5_L1A RUN5_L1A L5_L1A AXQ_L1A HeQ_L1A HchkQ_L1A HTQ_L1A FBQ_L1A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L1A.
    apply (f0_s6 1%nat st false TQ_L1A Edr_L1A Xf_L1A run6_L1A NX6_L1A RUN6_L1A L6_L1A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 1%nat st true PMID_L1A exits1_L1A Cert1m_L1A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L1A in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1%nat st true S1c_L1A_1 C2_L1A_1 EfD_L1A_1 ED_L1A_1 run2_L1A_1 D2_L1A_1 W2_L1A_1 NX2_L1A_1 EQ2_L1A_1 RUN2_L1A_1 L2_L1A_1 AXD_L1A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1A_1 TDr_L1A_1 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_1 ENTD_L1A_1 RUN3_L1A L3_L1A NX3_L1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1A_2 C2_L1A_2 EfD_L1A_2 ED_L1A_2 run2_L1A_2 D2_L1A_2 W2_L1A_2 NX2_L1A_2 EQ2_L1A_2 RUN2_L1A_2 L2_L1A_2 AXD_L1A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1A_2 TDr_L1A_2 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_2 ENTD_L1A_2 RUN3_L1A L3_L1A NX3_L1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1A_3 C2_L1A_3 EfD_L1A_3 ED_L1A_3 run2_L1A_3 D2_L1A_3 W2_L1A_3 NX2_L1A_3 EQ2_L1A_3 RUN2_L1A_3 L2_L1A_3 AXD_L1A_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1A_3 TDr_L1A_3 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_3 ENTD_L1A_3 RUN3_L1A L3_L1A NX3_L1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_L1A : ltac2:(tb__ "0|1|
S9OF_;S4fS4S1dS1dS17S51Q40A1A1S54OF_;S5R5A1S4bR5R4A2S4dU1M0S0R9R8R7R5S26S2aR3A9S4dG0S0RaR9R8R6S27S2bR4A9S4dG0S0RbRaR9R7S28S2cR5A9S4aRcRbRaR8S25R6A6S4aRdRcRbR9S29R7A6S4aReRdRcRaS2dR8A6S1dS55Vsegs;S45Vsegs;VJFi;S16RfReRcA4S3fR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L1A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L1A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1%nat st false Eps_L1A C3_L1A Ems_L1A C4_L1A TM0_L1A run4_L1A RM_L1A D3_L1A W3_L1A EQ3_L1A NX3b_L1A RUN4_L1A L4_L1A D4_L1A W4_L1A EQ4_L1A
             HeM_L1A HchkM_L1A HTM_L1A FBM_L1A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L1A.
    apply (ef0_s5 1%nat st q_L1A false TM_L1A Eq_L1A EQ_L1A TQ0_L1A run5_L1A RQ_L1A NX5_L1A RUN5_L1A L5_L1A AXQ_L1A HeQ_L1A HchkQ_L1A HTQ_L1A FBQ_L1A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L1A.
    apply (ef0_s6 1%nat st false TQ_L1A Edr_L1A Xf_L1A run6_L1A NX6_L1A RUN6_L1A L6_L1A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 1%nat st true PMID_L1A exits1_L1A (eq_refl : (GW <=? ss_next (ax_S PMID_L1A))%positive = true) ECert1m_L1A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L1A in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1%nat st true S1c_L1A_1 C2_L1A_1 EfD_L1A_1 ED_L1A_1 run2_L1A_1 D2_L1A_1 W2_L1A_1 NX2_L1A_1 EQ2_L1A_1 RUN2_L1A_1 L2_L1A_1 AXD_L1A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1A_1 TDr_L1A_1 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_1 ENTD_L1A_1 RUN3_L1A L3_L1A NX3_L1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1A_2 C2_L1A_2 EfD_L1A_2 ED_L1A_2 run2_L1A_2 D2_L1A_2 W2_L1A_2 NX2_L1A_2 EQ2_L1A_2 RUN2_L1A_2 L2_L1A_2 AXD_L1A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1A_2 TDr_L1A_2 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_2 ENTD_L1A_2 RUN3_L1A L3_L1A NX3_L1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1A_3 C2_L1A_3 EfD_L1A_3 ED_L1A_3 run2_L1A_3 D2_L1A_3 W2_L1A_3 NX2_L1A_3 EQ2_L1A_3 RUN2_L1A_3 L2_L1A_3 AXD_L1A_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1A_3 TDr_L1A_3 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_3 ENTD_L1A_3 RUN3_L1A L3_L1A NX3_L1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S9S40VCST;R1A2SfS40S73R2A2ScS41S39R2A2S42R2S3aA2A2A2SeF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9S40VCST;R1A2SdS75R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S9S40VCST;R1A2SdS74R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S9S40VCST;R1A2ScSdScS41S39R2A2S42R2S3aA2A2A1SdScS41Z17db48R2A2S42R2Z17db4cA2A2A1A2F_;Fa;").

Theorem free_lo_ia0_1A : ltac2:(tb__ "0|7|
S54OF_;S4fS4S1dS17S51Q40M0A1A1S52G0S1fR2PcA2A2S9S52G0S1fR3PdA2A2S9S32SaS44R4R3S13S1bS10S31A2M1S18S10S31S8S2S1U1A1M2S0A3M3S3S38SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S53S5R6A1S47SaR9S46R7A1A3S6dSaRaS46R8A1A3S41S43R6R5A2S69A2SbS14S50RbA1S19A3S36S24RcA2S1dS9S35S63R10S33R10ReRcRbR2R1A6R3A3S62S37R11A1R4RdRcR3R2A6SbS9S34R3A1S6aA3S4bR6S33S37R13A1R6RfReR5R4A6A2S49S61VCST;VXGL;S37R14A1M6A3R15G6R13S33G6R7R10RfR6R5A6S25S32SaS44R7R11S13G1S18S10S31G3S3G4VCST;VXGL;G6R13A5A4G5A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S70RfRdA2S56SaR10S45SaS7G4G2S0RfReA5S6S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 1 Wai_L1A Dai_L1A Wbi_L1A Wci_L1A Certi_L1A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 1 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 1) UStopLe q_L1A (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 1) UStopLe q_L1A HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid false 1 UStopLe q_L1A Wbm_L1A Wcm_L1A Wdm_L1A Fb_L1A XIm_L1A A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_L1A (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_L1A_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L1A_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L1A_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_L1A CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_L1A CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_ia0_1A : ltac2:(tb__ "0|7|
S4fS4S1dS17S51Q40M0A1A1S52G0S1fR2PcA2A2S9S52G0S1fR3PdA2A2S9S32SaS44R4R3S13S1bS10S31A2M1S18S10S31S8S2S1U1A1M2S0A3M3S3S38SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S53S5R6A1S41S43R4R3A2S69A2SbS14S50R9A1S19A3S36S24RaA2S1dS9S35S63ReS33ReRcRaR9R2R1A6R3A3S62S37RfA1R4RbRaR3R2A6SbS9S34R3A1S6aA3S4bR6S33S37R11A1R6RdRcR5R4A6A2S4aS61VCST;VXGL;S37R12A1M6A3G6R11S33G6R7ReRdR6R5A6S25S32SaS44R7RfS13G1S18S10S31G3S3G4VCST;VXGL;G6R11A5A4G5A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S71RbA1S55SaS45SaS7G4G2S0RdRcA5S6S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 1 Wai_L1A Dai_L1A Wbi_L1A Wci_L1A ECerti_L1A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 1 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 1) UStopLe q_L1A (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 1) UStopLe q_L1A HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid false 1 UStopLe q_L1A Wbm_L1A Wcm_L1A Wdm_L1A Fb_L1A XIm_L1A A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_L1A (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_L1A_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L1A_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L1A_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_L1A CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_L1A CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ML1A.
End F0A_mL1A.

