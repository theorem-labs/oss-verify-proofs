(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "pair"; "nat"; "cons"; "prod"; "list"; "nil"; "bool"; "true"; "length"; "option"; "Some"; "andb"; "app"; "false"; "fst"; "orb"; "snd"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "of_nat"; "mul"; "modulo"; "sub"; "leb"; "div"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "aa_q_thread"; "ag_thread"; "qb_addr"; "topG"; "ag_spacebeg"; "qb_items"; "aa_geom"; "ag_ctx"; "aa_cache_inited"; "ag_fsb"; "ageom"; "qb_size"; "AA"; "aa_live"; "ag_stack_bottom"; "ag_stack_top"; "aa_cls"; "aa_internal_inited"; "class_state"; "cs_cache"; "cs_empty"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "rm"; "sobj"; "rw"; "sprop"; "holds"; "valuation"; "SLit"; "enc_bytes"; "obj_range"; "agree_below"; "pairwise_disjoint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "present"; "view"; "bview"; "maskv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "qvar"; "cQ"; "cp_baseF"; "VFACT"; "cA"; "m8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "qcond"; "lastq"; "zhiF"; "zloF"; "ZU"; "cache24"; "j_qb"; "j_qf"; "junkF"; "top24"; "cnt24"; "ZD_NRT"; "ZD_NV"; "hw_of"; "j_min"; "j_st"; "rhoF_of"; "firstq"; "img_okb"; "spec_ne"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "carve_ok"; "NFS"; "NRT"; "NV"; "instF_facts"; "spec_zone"; "zone_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "in_zone"; "zcheck"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "rho_sets"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@Stdlib.Lists.List"; "In"; "last"; "Forall2"; "forallb"; "hd"; "tl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineBatchCount"; "HIGH_SHADOW_END"; "kSpaceSize"; "IMG_HI"; "FS_total"; "IMG_LO"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Size"; "kQuarantineBatchSize"; "max_count"; "Sh"; "LOW_SHADOW_BEG"; "PG"; "kQuarantineCacheMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "fs_footb"; "qb_dflt"; "qsize"; "QG"; "geom_ok"; "batch_repr"; "nthZ"; "qlinks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "vQB"; "vQF"; "vBS"; "vNX"; "vQS"; "item_base"; "nb_base"; "vCP"; "vCS"; "vK"; "vMX"; "vPK"; "vQN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "cls_hyp"; "F_pc"; "blk_geo"; "@Corelib.Init.Peano"; "lt"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "ustop"; "GOT_HI"; "GOT_LO"; "RTC_HI"; "RTC_LO"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "rigF"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section BLK.
Let segs : list Segment := segsA.

Lemma fs_footb_hi : ltac2:(tb__ "0|1|
S2eS0S95R2A1S15S1aR2S8eA2S18S83R2A2A2S15S1aR3S2dR4A1M0A2S18S19G0S86A2R3A2A2S14S8S91R5R4A2SfA3F_;F_;F_;Fz;FG;").
Proof.
  intros G z HG Hz Hd. pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  unfold LOW_SHADOW_BEG, HIGH_SHADOW_END in Hz. rewrite FS_total_val in Hd. pose proof (topG_range G) as ACV.
  destruct HG' as (G1 & G2 & G3 & _).
  pose proof (Sh_lt_HSE (ag_fsb G + FS_total) ltac:(rewrite FS_total_val; lia)) as S1. unfold HIGH_SHADOW_END in S1. rewrite FS_total_val in S1.
  assert (S0 : 2147450880 <= Sh (ag_fsb G + FS_frames_off)) by (unfold Sh, SHADOW_OFF; rewrite FS_frames_off_val; pose proof (Z.div_pos (ag_fsb G + 36864) 8); lia).
  pose proof (Sh_mono (ag_fsb G + FS_frames_off) (ag_fsb G + FS_total) ltac:(rewrite FS_total_val, FS_frames_off_val; lia)) as S2. rewrite FS_total_val in S2. rewrite FS_frames_off_val in S0, S2.
  apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_frames_off_val; unfold FS_kFlagsOffset; lia.
Qed.
Lemma fs_footb_sh : ltac2:(tb__ "0|1|
S2eS0S0S95R3A1S13S18Z0R2A2S1aR2Z7fffff800000A2A2S15S1aR3S2dR5A1M0A2S18S19G0S86A2R3A2A2S14S0R5S8dR4A1A3S14S8S91R7R6A2SfA3F_;F_;F_;F_;Fa;Fz;FG;").
Proof.
  intros G z a HG Ha Hd ->. pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  rewrite FS_total_val in Hd. pose proof (topG_range G) as ACV.
  destruct HG' as (G1 & G2 & G3 & _).
  pose proof (Sh_lt_HSE a ltac:(lia)) as S1. unfold HIGH_SHADOW_END in S1.

  pose proof (proj1 (geom_bands _ HG0)) as FB. rewrite FS_total_val in FB. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in FB.
  assert (S0 : 2147450880 <= Sh a) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos a 8); lia).
  apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_frames_off_val; unfold FS_kFlagsOffset; [lia | lia |].
  destruct Hd as [Hd|Hd].
  - left. unfold Sh. pose proof (Z.div_lt_upper_bound a 8 ((ag_fsb G + 36864) / 8) ltac:(lia)). pose proof (Z.div_mod (ag_fsb G) 8 ltac:(lia)).
    assert (ag_fsb G mod 8 = 0) by (rewrite <- (Z.mod_mod_divide _ 4096 8) by (exists 512; reflexivity); rewrite G1; reflexivity).
    assert ((ag_fsb G + 36864) / 8 = ag_fsb G / 8 + 4608) by (replace (ag_fsb G + 36864) with (ag_fsb G + 4608 * 8) by lia; rewrite Z.div_add by lia; lia). lia.
  - right. pose proof (Sh_mono (ag_fsb G + 11571200) a Hd). lia.
Qed.

Lemma present_cell8F : ltac2:(tb__ "0|0|
S4dS0S4bR2R1S19R1Z8A2A3S17S0S0S13S13S18Z0R1A2S1aR1S1bZ2Z40A2A2A2S49R4S4aR3U8R1A3A2A2Lv;A2F_;Fa;Fm;").
Proof.
  intros m a Hp.
  destruct (Hp a ltac:(lia)) as [b0 H0]. destruct (Hp (a + 1) ltac:(lia)) as [b1 H1]. destruct (Hp (a + 2) ltac:(lia)) as [b2 H2]. destruct (Hp (a + 3) ltac:(lia)) as [b3 H3].
  destruct (Hp (a + 4) ltac:(lia)) as [b4 H4]. destruct (Hp (a + 5) ltac:(lia)) as [b5 H5]. destruct (Hp (a + 6) ltac:(lia)) as [b6 H6]. destruct (Hp (a + 7) ltac:(lia)) as [b7 H7].
  exists (bv_unsigned (le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7])).
  assert (E : Z_to_bv 64 (bv_unsigned (le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7])) = le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7]) by apply Z_to_bv_bv_unsigned.
  split; [pose proof (urange (le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7])); lia|].
  unfold cell_ok. cbn [c_addr c_w RtCells.c_val]. intros k Hk. rewrite E. rewrite (enc_bytes_le_word 8) by (reflexivity || lia).
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; cbn [nth]; rewrite ?Z.add_0_r; try assumption. cbn in Hk. lia.
Qed.

Lemma cell_ok_present : ltac2:(tb__ "0|0|
S4dS0S3S0S49R4S4aR3R2R1A3A2S4bR5R4S19R4S1cR3A1A2A3F_;Fv;Fk;Fa;Fm;").
Proof.
  intros m a k v Hc z Hz. pose proof (Hc (Z.to_nat (z - a)) ltac:(cbn [c_w]; lia)) as X. cbn [c_addr c_w RtCells.c_val] in X.
  rewrite Z2Nat.id in X by lia. replace (a + (z - a)) with z in X by lia. eexists. exact X.
Qed.

End BLK.

Record junkF := mkJF { j_min : Z; j_st : Z; j_qf : Z; j_qb : Z }.
Definition cache24 (A : AA) : list Z := ltac2:(tb__ "0|0|
S37S97S36S34VA;A1Z18S38A4A1").
Definition cnt24 (A : AA) : Z := Z.of_nat (length (cache24 A)).
Definition top24 (A : AA) : Z := ltac2:(tb__ "0|1|
S79S0Sb2SaS0S5aVA;A1M0A2U1A2G0Z0A4").
Definition lastq (A : AA) : qbatch := last (aa_q_thread A) qb_dflt.
Definition firstq (A : AA) : qbatch := hd qb_dflt (aa_q_thread A).
Definition hw_of (t n : Z) : Z := ltac2:(tb__ "0|1|
S19S19Z2M0S1dZ100Vt;A2A2S1dZ10000S21Vn;S1bG0Z20A2A2A2A2").
Definition rhoF_of (A : AA) (rho : valuation) (p n t : Z) (jv : junkF) : valuation := ltac2:(tb__ "0|a|
S2aVA;A1S2eS76Vrho;S4S5S1S3aQ40M0A1M1A2M2S2S1G1P97S39G0S25R1A1A2A4S4G2S2S1G1P98S39G0S2bR1A1A2A4S4G2S2S1G1P99S39G0S33R1A1A2A4S4G2S2S1G1P9aS39G0S32R1A1A2A4S4G2S2S1G1P9bS39G0S28R1A1A2A4S4G2S2S1G1P88S39G0S63Vjv;A1A2A4S4G2S2S1G1P83S39G0S64Vjv;A1A2A4S4G2S2S1G1P67S39G0S1eVn;S1bZ2Z20A2A2A2A4S4G2S2S1G1P68S39G0S62Vt;Vn;A2M3A2A4S4G2S2S1G1P69S39G0S70Vn;A1M4A2A4S4G2S2S1G1P6aS39G0S21G4Z8A2A2A4S4G2S2S1G1P6bS39G0S19G3Z1A2A2A4S4G2S2S1G1P78S39G0S1cSaS23S24VA;A1M5A2A1A2A4S4G2S2S1G1P79S39G0S6S23A1M6S0Lx;M7G5S5cVjv;A1S23G6S26S66VA;A1A1Ll;Lq;X6x2A2A4S4G2S2S1G1P7aS39G0G7G5S5bVjv;A1S23G6S26S56VA;A1M8A1Ll;Lq;X6x2A2A4S4G2S2S1G1P7bS39G0S93G5A1A2A4S4G2S2S1G1P7cS39G0Z0A2A4S4G2S2S1G1P7dS39G0S2fG8A1A2A4S4G2S2S1G1P7eS39G0S1cSaS5S0S0A2S29G8A1A2A1A2A4S4G2S2S1G1P7fS39G0S5fVA;A1A2A4S4G2S2S1G1P80S39G0S8cZ18M9A1A2A4S4G2S2S1G1P81S39G0S8aG9A1A2A4S4G2S2S1G1P82S39G0S5eVA;A1A2A4S7G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2TG;").

Lemma rhoF_agree : ltac2:(tb__ "0|0|
S30S43S0S0S0S5dS47SabR5S65R6R5R4R3R2R1A6A3Fjv;Ft;Fn;Fp;Frho;FA;").
Proof.
  intros. apply agree_below_rho_sets. intros j v Hin. cbn in Hin. unfold NF.
  repeat (destruct Hin as [E|Hin]; [injection E; intros; subst; cbv; discriminate|]). destruct Hin.
Qed.

Definition qcond (q : qvar) (A : AA) : Prop := ltac2:(tb__ "0|4|
S4fOLq;Vq;S13S16S14S6S23A1S24VA;A1S7S23A1A3M0A1M1S1aS1cSaS5S0S0A2S29S56VA;A1A1A2A1M2S82A2A2S13G0S13S14S8S2cVA;A1S9A3S16S14S6S0A1S5aVA;A1S7S0A1A3A1A2M3A2S13G1S13S14S0G2S82A3G3A2A2X4fx3").

Definition ZD_NRT : list zdesc := ltac2:(tb__ "0|9|
S4S5S5S3S0A2M0S0A2M1S2G0S0S2S3S0U0M2Z180e88A4Z180e8aA4S4G1S2G0S0S2S3S0G2Zf20d8A4Zf20daA4S4G1S2G0S0S2S3S0G2Zf20e0A4Zf20f8A4S4G1S2G0S0S2S3S0G2Zf0c5cA4Zf0c5dA4S4G1S2G0S0S2S3S0G2Zf0c60A4Zf0c61A4S4G1S2G0S0S2S3S0G2Zf0c64A4Zf0c68A4S4G1S2G0S0S2S3S0G2Z624560A4Z624568A4S4G1S2G0S0S2S3S0G2Z645960A4Z645968A4S4G1S2G0S0S2S3S0U2M3Z8A4ZcA4S4G1S2G0S0S2S3S0G3Z98A4Za0A4S4G1S2G0S0S2S3S0U1M4Z0A4Z18A4S4G1S2G0S0S2S3S0G4Z28A4Z29A4S4G1S2G0S0S2S3S0G4Zc60M5A4Zc61A4S4G1S2G0S0S2S3S0G2Z182f4aA4Z182f4bA4S4G1S2G0S0S2S3S0G2Z180e98A4Z180e9cA4S4G1S2G0S0S2S3S0G2Z180ea0A4Z180ea8A4S4G1S2G0S0S2S3S0G2Zf20fcA4Zf2100A4S4G1S2G0S0S2S3S0G2Z183018A4Z18301cA4S4G1S2G0S0S2S3S0G2Z182f1cA4Z182f20A4S4G1S2G0S0S2S3S0G2Z18302cA4Z18302dA4S4G1S2G0S0S2S3S0G2Z182fb8A4Z182fc0A4S4G1S2G0S0S2S3S0G2Z182ec0A4Z182ed0A4S4G1S2G0S0S2S3S0G2Ze9af0A4Ze9af8A4S4G1S2G0S0S2S3S0G2Z182fa0A4Z182fa8A4S4G1S2G0S0S2S3S0G2Zeec24A4Zeec30A4S4G1S2G0S0S2S3S0G2Zee0c0M6A4Zee0c8A4S4G1S2G0S0S2S3S0G2Zee0b0A4G6A4S4G1S2G0S0S2S3S0G2Zeddb8A4Zeddc0A4S4G1S2G0S0S2S3S0G4Zad0A4Zae0M7A4S4G1S2G0S0S2S3S0G4G7A4Zae8M8A4S4G1S2G0S0S2S3S0G4G8A4G5A4S4G1S2G0S0S2S3S0G2Zf2608A4Z132610A4S4G1S2G0S0S2S3S0U3N10A4N8A4S7G1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition ZD_NV (q : qvar) : list zdesc := ltac2:(tb__ "0|c|
S4fS6S71A1Lq;Vq;S4S5S5S3S0A2M0S0A2M1S2G0S0S2S3S0U1M2Z50A4Z70A4M3S4G1S2G0S0S2S3S0U4M4Z0M5A4Z18M6A4M7S4G1S2G0S0S2S3S0G4G6A4Z2000M8A4S7G1A1M9A3A3A3S4G1G3S4G1S2G0S0S2S3S0G2Z850A4Z860MaA4S4G1S2G0S0S2S3S0G2GaA4Z868A4S4G1S2G0S0S2S3S0U5G5A4G8A4G9A3A3A3MbA3S4G1G3S4G1G7GbA3A3X4fx3").
Definition ZU (q : qvar) : list nat := ltac2:(tb__ "0|7|
S4fS6S3A1Lq;Vq;S4S3U0M0S4S3U1M1S4S3U2M2S4S3U3M3S4S3U4M4S7S3A1M5A3A3A3A3A3S4S3G0S4S3G1S4S3G2S4S3G3S4S3U5G5A3M6A3A3A3A3S4S3G0S4S3G1S4S3G2S4S3G3S4S3G4G6A3A3A3A3A3X4fx3").
Definition zloF (z : nat) : Z := match z with 0%nat => 0xe4000 | 2%nat => 8 | 3%nat => -16 | _ => 0 end.
Definition zhiF (z : nat) : Z := match z with 0%nat => 0x646000 | 1%nat | 2%nat => 0x1000 | 3%nat => 0 | _ => 8192 end.
Definition img_okb (d : zdesc) : bool := ltac2:(tb__ "0|1|
S5S5S3S0A2M0S0A2S8Ld;Vd;G0S0G0S8Lp;R2S3S0S8S8L_;Sb7R2U0A2SdSdSdS20Ze4000R1A2S20R3S85A2A2S11S20R3SafA2S20SaeR1A2A2A2S11S20R3Sb1A2S20Sb0R1A2A2A2S9X8x2Llo;Lz;X5x1Lhi;Lp;X5x1").
Definition spec_ne (k : carve_spec) : bool := ltac2:(tb__ "0|3|
S5S5S5S3cS0A2M0S0A2M1S6S5S5S0S3A2S3cA2A1M2A2S8Lk;Vk;G1G2G1S8Lp;R2G0S0G0S8Lp0;R2S3cS0S22R1R3A2Llo;Ls;X5x1Lhi;Lp0;X5x1Ll;Lp;X5x1").
Lemma ZD_chk : ltac2:(tb__ "0|2|
S4fS13S14S8S73SeS71S60S61R1A1A3M0A1S9A3S13S14S8S7dS71S67G0A3S9A3S13S14S8S7dS74S68S6aR1A1M1A3S9A3S14S3SaS3fS78S74S3fS75G1A4A2SaS71G0A2A3A2A2A2Fq;").
Proof. intros [| |]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma Forall2_In_l : forall {X Y : Type} (R : X -> Y -> Prop) l ds x, Forall2 R l ds -> In x l -> exists d, In d ds /\ R x d.
Proof.
  intros X Y R l ds x HF. induction HF as [|a d l' ds' Had HF IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists d; split; [left; reflexivity | exact Had]|].
  destruct (IH Hin) as (d' & Hd' & HR). exists d'. split; [right; exact Hd' | exact HR].
Qed.

Section INSTOK.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Section FACTS.
Variables (A : AA) (rho : valuation) (tp : list word) (md : Model) (p n : Z).
Hypothesis HA : ltac2:(tb__ "0|0|
VAInv;VA;Vrho;Vtp;Vmd;A4").
Hypothesis HL : ltac2:(tb__ "0|0|
S7aS5S0S0A2S2S0S0Vp;Vn;A4S31VA;A1A3").

Hypothesis HCL : blk_cls p n.
Let G : ageom := aa_geom A.
Let m : bview := ltac2:(tb__ "0|0|
S4cVsegs;S3eVrho;A1A2").
Let mm : bview := ltac2:(tb__ "0|0|
S4eS91S2aVA;A1A1S4cVsegs;S3eVrho;A1A2A2").

Lemma blkF_geom : ltac2:(tb__ "0|9|
S13Sa8Vp;S70Vn;A1M0A2S13S14S0S1eVp;Z10M1A2Z0A3S13S18Z1Vn;A2S13S1aS19Vp;G0A2M2S27VG;A1A2S13S15S18G2S25VG;A1M3A2S18S19G3Z1000M4A2S1fVp;G1A2M5A2A2S13S15S18S19Vp;Vn;A2M6S2bVG;A1M7A2S18S19G7G4A2G5A2A2S13S1aG0S19Vn;Z8A2A2S13S15S18G2S2dVG;A1M8A2S18S19G8S86A2G5A2A2S4bVmm;G6G2A3A2A2A2A2A2A2A2A2").
Proof.
  unfold G. pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT). destruct HRest as (Hsep & HLB & HPR & HSR & HQR & _ & HIA & HTH & HMI).
  destruct (Hsep p n HL) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8). pose proof (topG_range (aa_geom A)) as ACV.
  pose proof HCL as S2'. unfold blk_cls, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in S2'. clear S8.
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & _).
  pose proof (N8_facts n S1) as (N1 & N2 & N3 & N4).
  destruct HI3 as (_ & HPS & _ & _).
  assert (CORE : p mod 16 = 0 /\ p + N8 n < topG (aa_geom A) /\ present mm (p + n) (p + N8 n)).
  { destruct (HPS p n HL) as [Hprim | (ch & Hch & Eb & Esz)].
    -
      destruct (needed_fits n S1 Hprim) as (F1 & F2 & F3). set (c := ClassID (needed n)) in *.
      destruct HPR as (_ & _ & _ & HCR). specialize (HCR c F2). unfold class_repr in HCR.
      destruct HCR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & M4 & _ & _ & _ & _ & _ & PU & PSH & PE & ND & LV & _).
      destruct (LV p n HL Hprim eq_refl) as (L1 & L2 & L3). fold c in L1, L2, L3 |- *.
      pose proof (size_ok_all c F2) as [SZ1 SZ2]. pose proof (rz_mod16 n) as RZ. pose proof (rz_bound n) as RB.
      unfold kUserSpaceSize, kUserMapSize, kFreeArraySize in *. unfold region_beg in *. unfold kRegionSize in *. change (2 ^ 32) with 4294967296 in *.
      set (SB := ag_spacebeg (aa_geom A)) in *. set (cs := nthZ (aa_cls A) c cs_empty) in *.
      split; [|split].
      +
        clear -L2 G12 SZ2 RZ RB SZ1 L1.
        destruct (proj1 (Z.mod_divide _ (Size c) ltac:(lia)) L2) as [k Hk]. destruct (proj1 (Z.mod_divide _ 16 ltac:(lia)) SZ2) as [s' Hs].
        destruct (proj1 (Z.mod_divide _ 16 ltac:(lia)) RZ) as [r Hr]. destruct (proj1 (Z.mod_divide _ (2 ^ 16) ltac:(lia)) G12) as [u Hu].
        change (2 ^ 16) with 65536 in Hu. replace p with ((k * s' + r + u * 4096 + c * 268435456) * 16) by nia. apply Z.mod_mul. lia.
      + clear -L1 L3 M2 M3 G14 F1 F2 F3 ACV RB N1 S1. lia.
      + intros z Hz. unfold mm. apply (PU z); [clear -Hz L1 L3 M2 F1 F2 F3 RB N1 S1; lia|]. apply (chunk_not_other_live A rho tp md p n z HA HL); clear -Hz N1 RB S1; lia.
    -
      destruct HSR as (HS & _). destruct (In_nth_error _ _ Hch) as [i Hi]. specialize (HS i ch Hi).
      destruct HS as (_ & _ & _ & _ & _ & B1 & B2 & B3 & B4 & B5 & B6 & B7 & PM & _).
      pose proof (round_up_ge (sc_size ch) PG ltac:(unfold PG; lia)) as RU. unfold PG in *. clear B5.
      assert (EN : N8 n = round_up n 8) by (unfold N8, round_up; replace (n + 8 - 1) with (n + 7) by lia; reflexivity).
      split; [|split].
      + rewrite Eb. clear -B1. rewrite <- Zplus_mod_idemp_l, <- Zplus_mod_idemp_l with (a := sc_map_beg ch), <- (Z.mod_mod_divide (sc_map_beg ch) 4096 16) by (exists 256; reflexivity).
        rewrite B1. reflexivity.
      + clear -Eb Esz B3 B6 B7 RU EN N1. lia.
      + intros z Hz. unfold mm. apply (PM z); [clear -Hz Eb Esz B3 B6 B7 RU EN N1 S1; lia|]. pose proof (rz_bound n) as RB. apply (chunk_not_other_live A rho tp md p n z HA HL); clear -Hz N1 RB S1; lia. }
  destruct CORE as (C1 & C2 & C3).
  assert (P8 : p mod 8 = 0) by (rewrite <- (Z.mod_mod_divide p 16 8) by (exists 2; reflexivity); rewrite C1; reflexivity).
  assert (BG : blk_geo p (N8 n)).
  { unfold blk_geo. destruct S2' as [LO|HI]; [left | right; unfold HIGH_SHADOW_END; clear -HI; lia]. split; [exact S2|].
    apply (lo_round8 p n (N8 n) P8 N2); [clear -N1; lia | unfold LOW_SHADOW_BEG; exact LO]. }
  unfold HIGH_SHADOW_END in *.
  split; [exact BG|]. repeat split; try assumption; clear HPS HQR HPR HSR HLB HIA Hsep; try lia.
Qed.

Lemma blkF_mem : ltac2:(tb__ "0|5|
S17S0S0S13S13S18Z0R1A2S1aR1Z100A2A2S13S14S0S1eR1Z4A2Z1A3S13S49Vm;S4aS1fVp;Z10A2U4M0S62R1Vn;A2A3A2S13S49Vm;S4aS1fVp;ZcA2G0S1eVn;S1bZ2Z20A2A2A3A2S13S0S13S18S8dVp;A1M1R1A2S1aR1S19G1S21S70Vn;A1M2Z8A2A2A2A2S17S3aQ8A1M3G3S14SbG3A1Vm;R3A1ScG3R1A2A3Lx;A2M4F_;Fz;S0S13S18S19Vp;Vn;A2R1A2S1aR1S19Vp;G2A2A2A2G4F_;Fz;A2A2A2A2A2Lt;A2").
Proof.
  pose proof blkF_geom as (B1 & B2 & B3 & B4 & BT & BC & BN & BF & BP). unfold blk_geo in B1.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT). destruct HRest as (Hsep & HLB & _).
  destruct (HLB p n HL) as (Hst & Hlo & Hhi & Hsh & _). destruct (law_G1 A rho tp md p n HA HL) as (t & Ht1 & Ht2 & Hty).
  pose proof (topG_range (aa_geom A)) as ACV. pose proof (N8_facts n B3) as (N1 & N2 & N3 & N4). unfold G, m in *. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  assert (MM : forall z, p - 16 <= z < p + N8 n -> maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = view segs (rm rho) z).
  { intros z Hz. apply maskv_out. apply fs_footb_hi; [exact HG | unfold LOW_SHADOW_BEG, HIGH_SHADOW_END; lia | rewrite FS_total_val in *; lia]. }
  assert (Q15 : 0 <= n / 2 ^ 32 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  exists t. split; [exact Ht1|]. split; [exact Ht2|]. split; [|split; [|split]].
  -
    intros k Hk. cbn [c_addr c_w RtCells.c_val] in Hk |- *. rewrite <- MM by lia. rewrite nth_enc_bytes by lia.
    set (q2 := n / 2 ^ 32) in *. unfold hw_of. fold q2.
    assert (LB : forall j, le_byte (2 + 256 * t + 65536 * q2) 4 j = nth j [2; t; q2 mod 256; q2 / 256] 0 \/ (4 <= j)%nat).
    { intros j. unfold le_byte. rewrite (Z.mod_small (2 + 256 * t + 65536 * q2)) by (change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia).
      destruct j as [|[|[|[|j]]]]; [left|left|left|left|right; lia]; cbn [nth Z.of_nat Z.mul Pos.mul]; rewrite Z.shiftr_div_pow2 by lia.
      - rewrite Z.pow_0_r, Z.div_1_r. replace (2 + 256 * t + 65536 * q2) with (2 + (t + 256 * q2) * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
      - change (2 ^ 8) with 256. replace (2 + 256 * t + 65536 * q2) with (2 + (t + 256 * q2) * 256) by lia. rewrite Z.div_add by lia. change (2 / 256) with 0.
        rewrite Z.add_0_l. replace (t + 256 * q2) with (t + q2 * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
      - change (2 ^ 16) with 65536. replace (2 + 256 * t + 65536 * q2) with ((2 + 256 * t) + q2 * 65536) by lia. rewrite Z.div_add by lia.
        rewrite (Z.div_small (2 + 256 * t)) by lia. rewrite Z.add_0_l. reflexivity.
      - change (2 ^ 24) with (65536 * 256). rewrite <- (Z.div_div _ 65536 256) by lia. replace (2 + 256 * t + 65536 * q2) with ((2 + 256 * t) + q2 * 65536) by lia.
        rewrite Z.div_add by lia. rewrite (Z.div_small (2 + 256 * t)) by lia. rewrite Z.add_0_l. apply Z.mod_small.
        split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    destruct (LB 0%nat) as [L0|L0]; [|lia]. destruct (LB 1%nat) as [L1|L1]; [|lia]. destruct (LB 2%nat) as [L2|L2]; [|lia]. destruct (LB 3%nat) as [L3|L3]; [|lia].
    cbn [nth] in L0, L1, L2, L3. destruct k as [|[|[|[|k]]]]; [| | | |lia].
    + rewrite L0. replace (p - 16 + Z.of_nat 0) with (p - 16) by lia. exact Hst.
    + rewrite L1. replace (p - 16 + Z.of_nat 1) with (p - 15) by lia. exact Hty.
    + rewrite L2. pose proof (Hhi 0%nat ltac:(cbn; lia)) as X. cbn [c_addr c_w RtCells.c_val] in X.
      replace (p - 16 + Z.of_nat 2) with (p - 14 + Z.of_nat 0) by lia. rewrite X. rewrite nth_enc_bytes by lia. f_equal. apply Z_to_bv8_eq.
      unfold le_byte. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 16) with 65536. rewrite (Z.mod_small q2 65536) by lia. reflexivity.
    + rewrite L3. pose proof (Hhi 1%nat ltac:(cbn; lia)) as X. cbn [c_addr c_w RtCells.c_val] in X.
      replace (p - 16 + Z.of_nat 3) with (p - 14 + Z.of_nat 1) by lia. rewrite X. rewrite nth_enc_bytes by lia. f_equal. apply Z_to_bv8_eq.
      unfold le_byte. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 1) with 8. change (2 ^ 16) with 65536. rewrite (Z.mod_small q2 65536) by lia.
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
  - intros k Hk. cbn [c_addr c_w RtCells.c_val] in Hk |- *. rewrite <- MM by lia. exact (Hlo k Hk).
  -
    intros z Hz. destruct Hsh as [SZ SP].
    assert (EZ : z = Sh (p + 8 * (z - Sh p))).
    { unfold Sh in *. pose proof (Z.div_mod p 8 ltac:(lia)) as DP. assert (P8 : p mod 8 = 0) by (clear -B2; rewrite <- (Z.mod_mod_divide p 16 8) by (exists 2; reflexivity); rewrite B2; reflexivity).
      replace (p + 8 * (z - (p / 8 + SHADOW_OFF))) with ((z - (p / 8 + SHADOW_OFF) + p / 8) * 8) by lia. rewrite Z.div_mul by lia. lia. }
    assert (MS : maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = view segs (rm rho) z).
    { apply maskv_out. apply (fs_footb_sh _ z (p + 8 * (z - Sh p))); [exact HG | split; [lia|] | rewrite FS_total_val in *|exact EZ].
      - pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). unfold N8 in *. lia.
      - unfold N8 in *. lia. }
    rewrite <- MS. destruct (Z_lt_dec (z - Sh p) (n / 8)) as [LT|GE].
    + exists (Z_to_bv 8 0). rewrite <- (SZ (z - Sh p)) by lia. f_equal. lia.
    + assert (NZ : n mod 8 <> 0 /\ z - Sh p = n / 8).
      { unfold N8 in Hz. pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
        pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
        rewrite Z.div_mul in Hz by lia. split; lia. }
      destruct NZ as [NZ1 NZ2]. exists (Z_to_bv 8 (n mod 8)). rewrite <- (SP NZ1). f_equal. lia.
  - intros z Hz. rewrite <- MM by lia. exact (BP z Hz).
Qed.

Lemma MV_space : ltac2:(tb__ "0|3|
S0S13S18S28S2aVA;A1M0A1M1R1A2S1aR1S19S19G1S84A2Z1000A2A2A2S14SbS3aQ8A1A1S4eS91G0A1S4cVsegs;S3eVrho;A1M2A2R2A3S4cVsegs;G2R2A3A3F_;Fz;").
Proof. intros z Hz. apply maskv_out. apply fs_footb_space; [exact (proj1 HA) | exact Hz]. Qed.
Lemma MV_T : ltac2:(tb__ "0|3|
S0S13S18S25S2aVA;A1M0A1M1R1A2S1aR1S19G1Z1000A2A2A2S14SbS3aQ8A1A1S4eS91G0A1S4cVsegs;S3eVrho;A1M2A2R2A3S4cVsegs;G2R2A3A3F_;Fz;").
Proof. intros z Hz. apply maskv_out. apply fs_footb_thread; [exact (proj1 HA) | exact Hz]. Qed.
Lemma MV_img : ltac2:(tb__ "0|1|
S0S1aR1Z646000A2S14SbS3aQ8A1A1S4eS91S2aVA;A1A1S4cVsegs;S3eVrho;A1M0A2R2A3S4cVsegs;G0R2A3A3F_;Fz;").
Proof. intros z Hz. apply maskv_out. apply fs_footb_img; [exact (proj1 HA) | exact Hz]. Qed.

Lemma qlinks_last : ltac2:(tb__ "0|1|
S4dS6S23A1M0S98R2R1A2S16S14G0R2S7S23A1A3A1S49R4S4aS26S7bS23R3S92A3A1U8Z0A3A2F_;F_;Fl;Fmq;").
Proof.
  intros mq l. induction l as [|b r IH]; intros Hq Hne; [congruence|].
  cbn [qlinks] in Hq. destruct Hq as [Hb Hr]. destruct r as [|b' r'].
  - cbn. exact Hb.
  - change (last (b :: b' :: r') qb_dflt) with (last (b' :: r') qb_dflt). apply IH; [exact Hr | discriminate].
Qed.
Lemma last_In : ltac2:(tb__ "0|1|
S6S23A1M0S23S16S14G0R2S7S23A1A3A1S7aS23S7bS23R3R2A3R3A3F_;Fd;Fl;").
Proof.
  intros l d. induction l as [|b r IH]; intros Hne; [congruence|]. destruct r as [|b' r']; [left; reflexivity|].
  right. change (last (b :: b' :: r') d) with (last (b' :: r') d). apply IH. discriminate.
Qed.

Lemma qsize_lb : ltac2:(tb__ "0|0|
S4dS6S23A1S77S23S96R2VA;A2R1A3S18S1dZ2000S1cSaS23R2A2A1A2S93R2A1A2F_;Fl;Fmq;").
Proof.
  intros mq l. induction l as [|b r IH]; intros HB; [cbn; lia|].
  apply Forall_cons_iff in HB as [Hb Hr]. cbn [qsize fold_right length]. fold (qsize r). rewrite Nat2Z.inj_succ.
  destruct Hb as (_ & _ & _ & _ & Hsz & _ & Hit & _).
  assert (POS : 0 <= fold_right (fun it acc => snd it + acc) 0 (qb_items b)).
  { clear -Hit. assert (K : forall i it, nth_error (qb_items b) i = Some it -> 1 <= snd it) by (intros i it Hi; destruct (Hit i it Hi) as [_ (_ & Q & _)]; exact Q).
    clear Hit. induction (qb_items b) as [|it r' IH']; [cbn; lia|]. cbn [fold_right].
    pose proof (K 0%nat it eq_refl). pose proof (IH' ltac:(intros i it' Hi; exact (K (S i) it' Hi))). lia. }
  unfold kQuarantineBatchSize in Hsz. pose proof (IH Hr). lia.
Qed.

Lemma qF : ltac2:(tb__ "0|f|
S24VA;A1S6S23A1M0S19S25VG;A1M1Z50A2S0S13S49Vm;S4aR1U8M2S1cSaS23R2A2A1M3A3A2S13S4bVm;S19R1Z8M4A2M5S19R1Z18A2M6A3S13S49Vm;S4aG6G2S93R2A1M7A3A2S13S13S18Z0M8G7A2S18G7S90A2A2S13S18S1dZ2000G3A2G7A2S16S14G0R2S7S23A1A3A1S7bS23R3S92A3S23S26R1A1S0S13S49Vm;S4aS19R4G4A2G2S26S7eS23S92R5A3A1A3A2S13S49Vm;S4aS19R4Z10M9A2G2R1A3A2S13S49Vm;S4aR1G2G8A3A2S13S49Vm;S4aG5G2S2fR2A1A3A2S13S49Vm;S4aS19R1G9A2G2S1cSaS5S0S0A2S29R2A1A2A1MaA3A2S13S18GaS82A2S13S4bVm;G6S19R1S8bA2MbA3S13S14S0S1eR1G9A2G8A3S13S18S28VG;A1McR1A2S13S18GbS19GcS84A2A2S13S15S18GbG1A2S18S19G1Z1000MdA2R1A2A2S13S15S18GbS2bVG;A1MeA2S18S19GeGdA2R1A2A2S15S18S19Vp;S70Vn;A1A2R1A2S18GbS1fVp;G9A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Tqb;Tb;F_;A2A2A2A2A2Thdr;Tl;").
Proof.
  unfold G, m. pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT). destruct HRest as (Hsep & HLB & HPR & HSR & HQR & _ & HIA & HTH & HMI).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & _).
  destruct HQR as (QB & QL1 & QL2 & QH1 & QH2 & QM & QMIN & QS1 & QS2 & QND).
  destruct QH1 as (H1 & H2 & H3 & H4). pose proof (topG_range (aa_geom A)) as ACV.
  assert (MT : forall z, ag_thread (aa_geom A) + 80 <= z < ag_thread (aa_geom A) + 112 -> mm z = view segs (rm rho) z) by (intros z Hz; apply MV_T; lia).
  apply Forall_app in QB as [QBt QBg]. pose proof (qsize_lb _ _ QBt) as QLB.
  set (l := aa_q_thread A) in *. cbn zeta.
  split; [intros k Hk; cbn [c_addr c_w RtCells.c_val] in Hk |- *; rewrite <- MT by lia; exact (H1 k Hk)|].
  split; [intros z Hz; rewrite <- MT by lia; exact (H3 z Hz)|].
  split; [intros k Hk; cbn [c_addr c_w RtCells.c_val] in Hk |- *; rewrite <- MT by lia; exact (H4 k Hk)|].
  split; [lia|]. split; [exact QLB|].
  intros Hne. destruct (H2 Hne) as [H2a H2b].
  set (b := last l qb_dflt) in *. pose proof (last_In l qb_dflt Hne) as Hin. fold b in Hin.
  pose proof (proj1 (Forall_forall _ _) QBt b Hin) as HBR. pose proof (qlinks_last _ l QL1 Hne) as HNX. fold b in HNX.
  destruct HBR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & (x & X1 & X2 & XM & X3)).
  destruct HI3 as (SG3 & _ & _ & QF & _). destruct SG3 as (T1 & T2 & _).
  destruct HPR as (_ & _ & _ & HCR). pose proof (HCR 24 ltac:(lia)) as C24. unfold class_repr in C24.
  destruct C24 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _).
  unfold region_beg, kUserSpaceSize, kUserMapSize, kFreeArraySize in *. unfold kRegionSize in *. change (2 ^ 32) with 4294967296 in *.
  set (SB := ag_spacebeg (aa_geom A)) in *. set (qb := qb_addr b) in *.
  assert (QR : SB <= qb /\ qb + kQuarantineBatchSize <= SB + 2 ^ 37 /\ qb mod 16 = 0).
  { unfold kQuarantineBatchSize in *. split; [clear -X1 X2; lia|]. split; [clear -X1 X2 X3 M2 M3; lia|].
    rewrite X1. clear -X2 G12. destruct (proj1 (Z.mod_divide _ (2 ^ 16) ltac:(lia)) G12) as [u Hu]. change (2 ^ 16) with 65536 in Hu.
    replace (SB + 24 * 4294967296 + 16 * x) with ((u * 4096 + 24 * 268435456 + x) * 16) by lia. apply Z.mod_mul. lia. }
  destruct QR as (QR1 & QR2 & QR3).
  assert (MS : forall z, qb <= z < qb + kQuarantineBatchSize -> mm z = view segs (rm rho) z).
  { intros z Hz. apply MV_space. rewrite kSpaceSize_val. clear -Hz QR1 QR2. lia. }
  assert (In2 : In b (aa_q_thread A ++ aa_q_global A)) by (apply in_or_app; left; exact Hin).
  unfold kQuarantineBatchSize in *.
  split; [intros k Hk; cbn [c_addr c_w RtCells.c_val] in Hk |- *; rewrite <- MT by lia; exact (H2a k Hk)|].
  split; [intros k Hk; cbn [c_addr c_w RtCells.c_val] in Hk |- *; rewrite <- MT by lia; exact (H2b k Hk)|].
  split; [intros k Hk; cbn [c_addr c_w RtCells.c_val] in Hk |- *; rewrite <- MS by lia; exact (HNX k Hk)|].
  split; [intros k Hk; cbn [c_addr c_w RtCells.c_val] in Hk |- *; rewrite <- MS by lia; exact (R2 k Hk)|].
  split; [intros k Hk; cbn [c_addr c_w RtCells.c_val] in Hk |- *; rewrite <- MS by lia; exact (R3 k Hk)|].
  split; [exact R4|].
  split; [intros z Hz; rewrite <- MS by lia; exact (R6 z Hz)|].
  split; [exact QR3|]. split; [exact QR1|]. split; [rewrite kSpaceSize_val; exact QR2|].
  split; [|split].
  -
    destruct (Z_le_dec (qb + 8192) (ag_thread (aa_geom A))) as [|NE1]; [left; assumption|].
    destruct (Z_le_dec (ag_thread (aa_geom A) + 4096) qb) as [|NE2]; [right; assumption|]. exfalso.
    destruct (Z_lt_dec qb (ag_thread (aa_geom A))) as [LT|GE].
    + assert (QFT : q_foot A (ag_thread (aa_geom A))).
      { unfold q_foot. apply Exists_exists. exists b. split; [exact In2|]. left. fold qb. unfold kQuarantineBatchSize. lia. }
      apply (proj1 (QF _ QFT)). lia.
    + assert (QFT : q_foot A qb).
      { unfold q_foot. apply Exists_exists. exists b. split; [exact In2|]. left. fold qb. unfold kQuarantineBatchSize. lia. }
      apply (proj1 (QF _ QFT)). lia.
  - clear -T2 QR1 QR2. rewrite kSpaceSize_val in T2. lia.
  - pose proof (law_G3a A rho tp md p n b HA HL In2) as L. unfold kQuarantineBatchSize in L. exact L.
Qed.

Lemma Size24 : Size 24 = 8192. Proof. reflexivity. Qed.
Lemma max_count24 : max_count 24 = 2. Proof. reflexivity. Qed.
Lemma cF : ltac2:(tb__ "0|f|
S14S8S2cVA;A1S9A3S16S14S6S0A1S5aVA;A1S7S0A1A3A1S19S25VG;A1M0Z850A2S0S5eVA;A1S0S19S19S28VG;A1M1S1dZ18M2S1bZ2M3Z20A2A2A2S1dZ10M4R1A2A2S0S13S49Vm;S4aR3U4M5S5fVA;A1M6A3A2S13S49Vm;S4aS19R3Z4M7A2G5S8cG2A1A3A2S13S49Vm;S4aS19R3Z8A2U8S8aG2A1A3A2S13S49Vm;S4aS19S19R3G4A2S1dG7S1fG6Z1M8A2A2A2G5R2A3A2S13S13S18G8G6A2S18G6G3A2A2S13S13S18Z0M9R2A2S1aR2S1bG3Z1cA2A2A2S13S4bVm;R1S19R1Z2000MaA2MbA3S13S15S18GbG0A2S18S19G0Z1000McA2R1A2A2S13S15S18GbS2bVG;A1MdA2S18S19GdGcA2R1A2A2S13S15S18S19Vp;S70Vn;A1A2R1A2S18GbS1fVp;G4A2A2A2S13S16S14S6S23A1S24VA;A1MeS7S23A1A3A1S26S7bS23GeS92A3A1S0S15S18S19R1S8bA2R3A2S18S19R3GaA2R1A2A2Tqb;F_;S13S18S19S19G1S84A2GcA2S27VG;A1A2S13S18S83G1A2S14S0S1eG1S1bG3G4A2A2G9A3A2A2A2A2A2A2A2A2A2A2A2A2A2Tnb;Tx;Tpc;F_;F_;").
Proof.
  intros HCI HNE. cbn zeta. unfold G, m, cnt24, top24 in *. unfold cache24 in *. pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT). destruct HRest as (Hsep & HLB & HPR & HSR & HQR & _ & HIA & HTH & HMI).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & _). pose proof (topG_range (aa_geom A)) as ACV.
  destruct HI3 as (SG3 & _ & _ & QF & _). destruct SG3 as (T1 & T2 & _).
  destruct HPR as (_ & _ & _ & HCR). pose proof (HCR 24 ltac:(lia)) as C24. unfold class_repr in C24.
  destruct C24 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & _ & _ & _ & _ & N7 & PU & PSH & PE & ND & LV & CI & _).
  destruct (CI HCI) as (K1 & K2 & K3 & K4 & K5). rewrite Size24, max_count24 in *.
  set (cs := nthZ (aa_cls A) 24 cs_empty) in *.
  set (x := nth (length (cs_cache cs) - 1) (cs_cache cs) 0) in *.
  assert (Hlen : (0 < length (cs_cache cs))%nat) by (destruct (cs_cache cs); [congruence | cbn; lia]).
  assert (Hx : In x (cs_free_array cs ++ cs_cache cs)) by (apply in_or_app; right; unfold x; apply nth_In; lia).
  destruct (N7 x Hx) as (X1 & X2 & X3). unfold kCompactPtrScale in X2, X3. rewrite Z.shiftl_mul_pow2 in X2, X3 by lia. change (2 ^ 4) with 16 in X2, X3.
  unfold region_beg, kUserSpaceSize, kUserMapSize, kFreeArraySize in *. unfold kRegionSize in *. change (2 ^ 32) with 4294967296 in *.
  set (SB := ag_spacebeg (aa_geom A)) in *.
  assert (MT : forall z, ag_thread (aa_geom A) + 2128 <= z < ag_thread (aa_geom A) + 2208 -> mm z = view segs (rm rho) z) by (intros z Hz; apply MV_T; lia).
  assert (NBR : SB <= SB + 24 * 4294967296 + 16 * x /\ SB + 24 * 4294967296 + 16 * x + 8192 <= SB + 2 ^ 37) by (clear -X1 X3 M2 M3; lia).
  assert (MS : forall z, SB + 24 * 4294967296 + 16 * x <= z < SB + 24 * 4294967296 + 16 * x + 8192 -> mm z = view segs (rm rho) z).
  { intros z Hz. apply MV_space. rewrite kSpaceSize_val. clear -Hz NBR. lia. }
  pose proof (K4 (length (cs_cache cs) - 1)%nat x ltac:(unfold x; apply nth_error_nth'; lia)) as K4'.
  replace (ag_thread (aa_geom A) + 208 + 80 * 24 + 16 + 4 * Z.of_nat (length (cs_cache cs) - 1)) with (ag_thread (aa_geom A) + 2128 + 16 + 4 * (Z.of_nat (length (cs_cache cs)) - 1)) in K4' by lia.
  replace (ag_thread (aa_geom A) + 208 + 80 * 24) with (ag_thread (aa_geom A) + 2128) in K1, K2, K3 by lia.
  split; [intros k Hk; cbn [c_addr c_w RtCells.c_val] in Hk |- *; rewrite <- MT by lia; exact (K1 k Hk)|].
  split; [intros k Hk; cbn [c_addr c_w RtCells.c_val] in Hk |- *; rewrite <- MT by lia; exact (K2 k Hk)|].
  split; [intros k Hk; cbn [c_addr c_w RtCells.c_val] in Hk |- *; rewrite <- MT by lia; exact (K3 k Hk)|].
  split; [intros k Hk; cbn [c_addr c_w RtCells.c_val] in Hk |- *; rewrite <- MT by lia; exact (K4' k Hk)|].
  split; [lia|]. split; [clear -X1 X3 M2 M3; lia|].
  split; [intros z Hz; rewrite <- MS by exact Hz; apply PU;
          [clear -Hz X1 X3 M2; lia
          | apply (slot_not_live _ A rho tp md 24 x z HA ltac:(lia) Hx); unfold region_beg, kRegionSize; rewrite Size24; change (2 ^ 32) with 4294967296; fold SB; clear -Hz; lia]|].
  split; [clear -T1 NBR; rewrite kSpaceSize_val in T1; lia|].
  split; [clear -T2 NBR; rewrite kSpaceSize_val in T2; lia|].
  assert (HxIn : In x (cs_cache (nthZ (aa_cls A) 24 cs_empty))) by (fold cs; unfold x; apply nth_In; lia).
  split; [pose proof (law_G3b A rho tp md p n 24 x HA HL ltac:(lia) HxIn) as L; cbn zeta in L; rewrite Size24 in L;
          unfold region_beg, kRegionSize in L; change (2 ^ 32) with 4294967296 in L; exact L|].
  split; [intros Hne; pose proof (law_G3c A rho tp md (last (aa_q_thread A) qb_dflt) x HA ltac:(apply in_or_app; left; apply last_In; exact Hne) HxIn) as L;
          cbn zeta in L; unfold region_beg, kRegionSize in L; change (2 ^ 32) with 4294967296 in L; exact L|].
  rewrite kSpaceSize_val. unfold HIGH_SHADOW_END. clear -G12 G13 G14. repeat split; lia.
Qed.

Lemma junkF_ok : ltac2:(tb__ "0|8|
S17S5dS5dS13S13S18Z0M0S63R1A1M1A2S1aG1S1bZ2Z40A2M2A2A2S13S13S18G0S64R1A1M3A2S1aG3G2A2A2S13S13S18G0S5cR1A1M4A2S1aG4G2A2A2S13S13S18G0S5bR1A1M5A2S1aG5G2A2A2S13S49Vm;S4aS19S94Z48A2U8M6G1A3A2S13S49Vm;S4aS19S25VG;A1M7Zae0A2G6G3A3A2S14S6S23A1S24VA;A1S7S23A1A3S13S49Vm;S4aS19G7Z58A2G6S5cR2A1A3A2S49Vm;S4aS19G7Z60A2G6S5bR2A1A3A2A2F_;A2A2A2A2A2A2Ljv;A2").
Proof.
  unfold G, m. pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT). destruct HRest as (Hsep & HLB & HPR & HSR & HQR & _ & HIA & HTH & HMI).
  destruct HQR as (QB & QL1 & QL2 & QH1 & QH2 & QM & QMIN & QS1 & QS2 & QND). destruct QH1 as (H1 & H2 & H3 & H4).
  destruct HTH as [_ HTS].

  assert (P1 : present (view segs (rm rho)) (QG + 72) (QG + 72 + 8)) by (intros z Hz; rewrite <- MV_img by (unfold QG in Hz; lia); apply (cell_ok_present _ _ _ _ QMIN); exact Hz).
  assert (P2 : present (view segs (rm rho)) (ag_thread (aa_geom A) + 2784) (ag_thread (aa_geom A) + 2784 + 8)) by (intros z Hz; rewrite <- MV_T by lia; apply HTS; lia).
  assert (P3 : present (view segs (rm rho)) (ag_thread (aa_geom A) + 88) (ag_thread (aa_geom A) + 88 + 8)) by (intros z Hz; rewrite <- MV_T by lia; apply H3; lia).
  assert (P4 : present (view segs (rm rho)) (ag_thread (aa_geom A) + 96) (ag_thread (aa_geom A) + 96 + 8)) by (intros z Hz; rewrite <- MV_T by lia; apply H3; lia).
  destruct (present_cell8F _ _ P1) as (v1 & R1 & C1). destruct (present_cell8F _ _ P2) as (v2 & R2 & C2).
  destruct (present_cell8F _ _ P3) as (v3 & R3 & C3). destruct (present_cell8F _ _ P4) as (v4 & R4 & C4).
  exists (mkJF v1 v2 v3 v4). cbn [j_min j_st j_qf j_qb]. repeat split; try assumption; lia.
Qed.

Section CARVE.
Hypothesis Hii : aa_internal_inited A = true.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S14S0S3bQ40S40Vrho;PcA2A2Vp;A3").
Hypothesis Hn13 : ltac2:(tb__ "0|0|
S14S0S3bQ40S40Vrho;PdA2A2Vn;A3").
Variable t : Z.
Hypothesis Ht : ltac2:(tb__ "0|1|
S13S13S18Z0Vt;A2S1aVt;Z100A2A2S13S14S0S1eVt;Z4A2Z1A3S13S49Vm;S4aS1fVp;Z10A2U4M0S62Vt;Vn;A2A3A2S49Vm;S4aS1fVp;ZcA2G0S1eVn;S1bZ2Z20A2A2A3A2A2A2A2").
Variable jv : junkF.
Hypothesis Hjv : ltac2:(tb__ "0|8|
S13S13S18Z0M0S63Vjv;A1M1A2S1aG1S1bZ2Z40A2M2A2A2S13S13S18G0S64Vjv;A1M3A2S1aG3G2A2A2S13S13S18G0S5cVjv;A1M4A2S1aG4G2A2A2S13S13S18G0S5bVjv;A1M5A2S1aG5G2A2A2S13S49Vm;S4aS19S94Z48A2U8M6G1A3A2S13S49Vm;S4aS19S25VG;A1M7Zae0A2G6G3A3A2S14S6S23A1S24VA;A1S7S23A1A3S13S49Vm;S4aS19G7Z58A2G6G4A3A2S49Vm;S4aS19G7Z60A2G6G5A3A2A2F_;A2A2A2A2A2A2").
Let rho1 : valuation := ltac2:(tb__ "0|0|
S65VA;Vrho;Vp;Vn;Vt;Vjv;A6").

Lemma civF : ltac2:(tb__ "0|4|
S0S0S3S0S3cS49Vm;S4aS19R5R4A2R3R2A3A2S14S3aQ40M0A1S3dVrho1;R2A2S39G0R3A2A3S18Z0M1S19R7R6A2A2S18S19S19R8R7A2S1cR6A1A2S1bZ2Z40A2A2S3Sa9R1R8A2S14SbS3aQ8M2A1M3A1S80Vsegs;S3eVrho1;A1S39G0S19S19RbRaA2S1cR2A1A2A2A3ScG3S79G3R2S45R9S3dVrho1;R7A2A2S39G2G1A2A4A2A3F_;Fj;F_;F_;F_;F_;Fe;Fv;Fk;Foff;Fb;").
Proof. intros b off k v e Hc He B1 B2. eapply civ_cell; eauto. Qed.
Lemma wrF : ltac2:(tb__ "0|3|
S0S3S0S0S49Vm;S4aR4R3R2A3A2S13S18R5R2A2S1aR2S19R5S1cR4A1A2A2A2S18Z646000R6A2S18S19R7S1cR6A1A2S1bZ2Z40A2A2S13S14S8S81Vsegs;S3eVrho1;A1M0S39Q40M1R5A2A3S9A3S17S3aQ8A1M2G2S14SbG2A1S80Vsegs;G0S39G1R6A2A3ScG2R1A2A3Ly;A2A2F_;F_;F_;F_;Fz;Fv;Fk;Fa;").
Proof. intros a k v z Hc Hz Ha Hk. eapply cell_wok_rd; eauto. Qed.
Lemma wrP : ltac2:(tb__ "0|3|
S0S0S0S4bVm;R3R2A3S13S18R4R2A2S1aR2R3A2A2S18Z646000R5A2S18R5S1bZ2Z40A2A2S13S14S8S81Vsegs;S3eVrho1;A1M0S39Q40M1R5A2A3S9A3S17S3aQ8A1M2G2S14SbG2A1S80Vsegs;G0S39G1R6A2A3ScG2R1A2A3Ly;A2A2F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hp Hz Hlo Hhi. destruct (Hp z Hz) as [b Hb]. unfold m in Hb. rewrite view_in in Hb by lia.
  change (rm rho1) with (rm rho). eapply wok_rd_off_image; [lia | exact Hb].
Qed.

Lemma wrF2 : ltac2:(tb__ "0|3|
S0S3S0S0S49Vm;S4aR4R3R2A3A2S13S18R5R2A2S1aR2S19R5S1cR4A1A2A2A2S18Z0R6A2S15S18S19R7S1cR6A1A2Z10000A2S18Z646000R7A2A2S18S19R8S1cR7A1A2S1bZ2Z40A2A2S13S14S8S81Vsegs;S3eVrho1;A1M0S39Q40M1R6A2A3S9A3S17S3aQ8A1M2G2S14SbG2A1S80Vsegs;G0S39G1R7A2A3ScG2R1A2A3Ly;A2A2F_;F_;F_;F_;F_;Fz;Fv;Fk;Fa;").
Proof. intros a k v z Hc Hz Ha Ho Hk. eapply cell_wok_rd2; eauto. Qed.
Lemma wrP2 : ltac2:(tb__ "0|3|
S0S0S0S4bVm;R3R2A3S13S18R4R2A2S1aR2R3A2A2S18Z0R5A2S15S18R5Z10000A2S18Z646000R6A2A2S18R6S1bZ2Z40A2A2S13S14S8S81Vsegs;S3eVrho1;A1M0S39Q40M1R6A2A3S9A3S17S3aQ8A1M2G2S14SbG2A1S80Vsegs;G0S39G1R7A2A3ScG2R1A2A3Ly;A2A2F_;F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hp Hz Hlo Ho Hhi. destruct (Hp z Hz) as [b Hb]. unfold m in Hb. rewrite view_in in Hb by lia.
  change (rm rho1) with (rm rho). eapply wok_rd_off_image2; [lia | lia | exact Hb].
Qed.

Local Ltac civ_try2F HR n :=
  eapply (civ_nth2 _ _ n); [exact HR | reflexivity | unfold fs_log_cell, fs_needs_gc_cell; reflexivity | unfold fs_log_cell, fs_needs_gc_cell; lia | unfold fs_log_cell, fs_needs_gc_cell; lia].
Local Ltac civ_any2F HR := first [ civ_try2F HR 43%nat | civ_try2F HR 44%nat | civ_try2F HR 45%nat | civ_try2F HR 46%nat | civ_try2F HR 47%nat | civ_try2F HR 48%nat | civ_try2F HR 49%nat | civ_try2F HR 50%nat | civ_try2F HR 51%nat | civ_try2F HR 52%nat | civ_try2F HR 53%nat | civ_try2F HR 54%nat | civ_try2F HR 0%nat | civ_try2F HR 1%nat | civ_try2F HR 2%nat | civ_try2F HR 3%nat | civ_try2F HR 4%nat | civ_try2F HR 5%nat | civ_try2F HR 6%nat | civ_try2F HR 7%nat | civ_try2F HR 8%nat | civ_try2F HR 9%nat | civ_try2F HR 10%nat | civ_try2F HR 11%nat | civ_try2F HR 12%nat | civ_try2F HR 13%nat | civ_try2F HR 14%nat | civ_try2F HR 15%nat | civ_try2F HR 16%nat | civ_try2F HR 17%nat | civ_try2F HR 18%nat | civ_try2F HR 19%nat | civ_try2F HR 20%nat | civ_try2F HR 21%nat | civ_try2F HR 22%nat | civ_try2F HR 23%nat | civ_try2F HR 24%nat | civ_try2F HR 25%nat | civ_try2F HR 26%nat | civ_try2F HR 27%nat | civ_try2F HR 28%nat | civ_try2F HR 29%nat | civ_try2F HR 30%nat | civ_try2F HR 31%nat | civ_try2F HR 32%nat | civ_try2F HR 33%nat | civ_try2F HR 34%nat | civ_try2F HR 35%nat | civ_try2F HR 36%nat | civ_try2F HR 37%nat | civ_try2F HR 38%nat | civ_try2F HR 39%nat | civ_try2F HR 40%nat | civ_try2F HR 41%nat | civ_try2F HR 42%nat ].

Local Ltac lia_only v := repeat match goal with H : context [v] |- _ => revert H end; clear - v; intros; lia.
Local Ltac wr_cell2F HR n off tacW :=
  eapply (cell_wok_rd2 _ _ _ _ _ (cells_ok_nth _ _ n _ HR eq_refl)); cbn [c_addr c_w Z.of_nat]; unfold fs_log_cell, fs_needs_gc_cell;
  [ lazymatch goal with |- ?x + _ <= ?x + _ < _ => idtac end; lia_only off | lia | tacW | lia ].
Local Ltac wr_any2F HR off tacW := first [ wr_cell2F HR 43%nat off tacW | wr_cell2F HR 44%nat off tacW | wr_cell2F HR 45%nat off tacW | wr_cell2F HR 46%nat off tacW | wr_cell2F HR 47%nat off tacW | wr_cell2F HR 48%nat off tacW | wr_cell2F HR 49%nat off tacW | wr_cell2F HR 50%nat off tacW | wr_cell2F HR 51%nat off tacW | wr_cell2F HR 52%nat off tacW | wr_cell2F HR 53%nat off tacW | wr_cell2F HR 54%nat off tacW ].

Lemma carve_NRT : ltac2:(tb__ "0|0|
S77S74S69Vrho1;A1S6bA3").
Proof.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT). destruct HRest as (Hsep & HLB & HPR & HSR & HQR & _ & HIA & HTH & HMI).
  pose proof (topG_range (aa_geom A)) as ACV. pose proof blkF_geom as (B1 & B2 & B3 & B4 & _ & _ & BN & _ & BP). unfold blk_geo in B1. unfold G in *.
  pose proof (N8_facts n B3) as (N1 & N2 & N3 & N4).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & _ & _ & _ & _ & _ & _ & _ & _ & G23).

  unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  assert (Erm : rm rho1 = rm rho) by reflexivity.
  assert (E151 : rw rho1 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))) by reflexivity.
  assert (E152 : rw rho1 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))) by reflexivity.
  assert (E153 : rw rho1 153%positive = Z_to_bv 64 (ag_stack_top (aa_geom A))) by reflexivity.
  assert (E154 : rw rho1 154%positive = Z_to_bv 64 (ag_stack_bottom (aa_geom A))) by reflexivity.
  assert (E155 : rw rho1 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A))) by reflexivity.
  assert (E136 : rw rho1 136%positive = Z_to_bv 64 (j_min jv)) by reflexivity.
  assert (E131 : rw rho1 131%positive = Z_to_bv 64 (j_st jv)) by reflexivity.
  assert (E103 : rw rho1 103%positive = Z_to_bv 64 (n mod 2 ^ 32)) by reflexivity.
  assert (E104 : rw rho1 104%positive = Z_to_bv 64 (hw_of t n)) by reflexivity.
  assert (E12 : rw rho1 12%positive = rw rho 12%positive) by reflexivity.

  unfold ia_inv in HIA. rewrite Hii in HIA. destruct HIA as (IA9 & IAa & IAb & IA8 & IAM).
  unfold thread_inv in HTH. destruct HTH as [HTH HTS].
  rewrite MV_img in IA9, IAa, IAb, IA8 by (unfold IA_BEG, IA_END; lia).
  assert (IAM' : forall z, IA_MAP1 <= z < IA_MAP1 + IA_MAP1_SZ -> view segs (rm rho) z = Some (Z_to_bv 8 0)).
  { intros z Hz. rewrite <- MV_img by (unfold IA_MAP1, IA_MAP1_SZ in Hz; lia). exact (IAM z Hz). }
  rewrite MV_T in HTH by lia.
  assert (HTS' : present m (ag_thread (aa_geom A) + 2768) (ag_thread (aa_geom A) + 3168)).
  { intros z Hz. rewrite <- MV_T by lia. exact (HTS z ltac:(lia)). }
  destruct HMI as [HMIc _].
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HMIc))) as HCSD.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HMIc)))) as HDIE.
  assert (HCSD' : cell_ok m (mkACell (0 + 0x183018) 4 0)) by (intros j Hj; specialize (HCSD j Hj); cbn [c_addr c_w RtCells.c_val] in HCSD, Hj |- *; rewrite Z.add_0_l; rewrite MV_img in HCSD by lia; exact HCSD).
  assert (HDIE' : cell_ok m (mkACell (0 + 0x182f1c) 4 0)) by (intros j Hj; specialize (HDIE j Hj); cbn [c_addr c_w RtCells.c_val] in HDIE, Hj |- *; rewrite Z.add_0_l; rewrite MV_img in HDIE by lia; exact HDIE).
  destruct Ht as (T1 & T2 & HHW & HNLO). destruct Hjv as (J1 & J2 & J3 & J4 & HJmin & HJst & HJq).

  pose proof (urange (rw rho 12%positive)) as U12.
  assert (Eiam : bv_unsigned (alu64 ALU_SLL (alu64 ALU_SRL (rw rho 12%positive) (Z_to_bv 64 32)) (Z_to_bv 64 3)) = 8 * (p / 2 ^ 32)).
  { rewrite sll_val, srl_val, Hp12. change (32 mod 64) with 32. change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
    pose proof (Z.div_pos p (2 ^ 32) ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound p (2 ^ 32) (2 ^ 15) ltac:(lia) ltac:(lia)).
    rewrite Z.mod_small by lia. lia. }
  assert (P15 : 0 <= p / 2 ^ 32 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (HHW' : cell_ok m (mkACell (p + -16) 4 (hw_of t n))) by (replace (p + -16) with (p - 16) by lia; exact HHW).
  assert (HNLO' : cell_ok m (mkACell (p + -12) 4 (n mod 2 ^ 32))) by (replace (p + -12) with (p - 12) by lia; exact HNLO).
  assert (HJst' : cell_ok m (mkACell (ag_thread (aa_geom A) + 208 + 2576) 8 (j_st jv))) by (replace (ag_thread (aa_geom A) + 208 + 2576) with (ag_thread (aa_geom A) + 2784) by lia; exact HJst).
  assert (HJmin' : cell_ok m (mkACell (0 + (QG + 72)) 8 (j_min jv))) by (rewrite Z.add_0_l; exact HJmin).
  assert (IAMc : cell_ok m (mkACell (8 * (p / 2 ^ 32) + 992776) 8 0)).
  { intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *. rewrite nth_enc_bytes by lia. unfold le_byte. rewrite Z.mod_0_l by lia. rewrite Z.shiftr_0_l, Z.mod_0_l by (cbn; lia). apply IAM'.
    unfold IA_MAP1, IA_MAP1_SZ. lia. }
  assert (EcA : bv_unsigned (eval rho1 cA) = ag_thread (aa_geom A) + 208) by (cbn [eval cA vT]; rewrite E151, add_val, !u64_lit by lia; apply Z.mod_small; lia).
  unfold NRT, N_rest, N_fn. cbn [tl app]. unfold iam_base. unfold vT, vCTX, vTOP, vBOT, vSB, vMINq, vST, vHW, vNLO.
  repeat apply Forall_cons; try apply Forall_nil; unfold carve_ok; cbn [eval]; rewrite ?E151, ?E152, ?E155, ?E12, ?Eiam, ?EcA, ?Hp12, ?u64_lit by lia.
  all: cbn zeta.
  all: split; [unfold QG, DPMCELL, MLIMCELL; lia|]. all: split; [unfold QG, DPMCELL, MLIMCELL; lia|]. all: split; [unfold QG, DPMCELL, MLIMCELL; lia|].
  all: split; [unfold QG, DPMCELL, MLIMCELL; lia|]. all: split; [unfold QG, DPMCELL, MLIMCELL; lia|].
  all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
  all: rewrite ?Erm.

  all: clear G1 G7 G12 B2 N2 N4 T2 Eiam EcA HJq U12 Hsep HLB HPR HSR HQR HF HM HI3 IAM' HTS HCSD HDIE HBT.
  all: split.
  all: pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & _). all: unfold IMG_LO, IMG_HI in TI, CI.

  all: try match goal with
       | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; unfold QG, DPMCELL, MLIMCELL in Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
       | |- forall off, 3168 <= off < 3169 -> _ => intros off Hoff; replace off with 3168 by lia; eapply wok_rd_off_image2; [lia| clear -TI; lia |]; rewrite <- view_in by lia; exact HTH
       | |- forall off, 2768 <= off < 2784 -> _ => intros off Hoff; apply (wrP2 _ _ _ HTS'); clear -TI Hoff G5 G6 ACV; lia
       | |- forall off, 2576 <= off < 2584 -> _ => intros off Hoff; apply (wrP2 _ _ _ HTS'); clear -TI Hoff G5 G6 ACV; lia
       | |- forall off, 2792 <= off < 3168 -> _ => intros off Hoff; apply (wrP2 _ _ _ HTS'); clear -TI Hoff G5 G6 ACV; lia
       | |- forall off, 992776 <= off < 992784 -> _ => intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
       | |- forall off, -16 <= off < -8 -> _ =>
           intros off Hoff; destruct (Z_lt_dec off (-12)); [apply (wrF _ _ _ _ HHW); cbn [Z.of_nat]; lia | apply (wrF _ _ _ _ HNLO); cbn [Z.of_nat]; lia]
       | |- forall off, _ -> wok_of _ _ _ = true /\ _ =>
           intros off Hoff; first [ wr_any2F HR off ltac:(clear -TI CI; lia) | destruct (Z_lt_dec off 8); [wr_any2F HR off ltac:(clear -TI CI; lia) | destruct (Z_lt_dec off 16); wr_any2F HR off ltac:(clear -TI CI; lia)] ]
       end.

  all: try (unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil).
  all: try match goal with
       | |- forall j, (j < 1)%nat -> rd_of _ _ (Z_to_bv 64 (0 + 1576584 + _)) = _ =>
           intros j Hj; replace j with 0%nat by lia; cbn [Z.of_nat]; rewrite ?Z.add_0_r, ?Z.add_0_l; rewrite <- view_in by lia; cbn [eval]; rewrite nth0_enc1_one'; exact IA8
       | |- forall j, (j < 1)%nat -> rd_of _ _ (Z_to_bv 64 (0 + 1576585 + _)) = _ =>
           intros j Hj; replace j with 0%nat by lia; cbn [Z.of_nat]; rewrite ?Z.add_0_r, ?Z.add_0_l; rewrite <- view_in by lia; cbn [eval]; rewrite nth0_enc1_zero'; exact IA9
       | |- forall j, (j < 1)%nat -> rd_of _ _ (Z_to_bv 64 (ag_thread _ + 3168 + _)) = _ =>
           intros j Hj; replace j with 0%nat by lia; cbn [eval]; rewrite nth0_enc1_zero'; cbn [Z.of_nat]; rewrite Z.add_0_r; rewrite <- view_in by lia; exact HTH
       | |- forall j, _ -> rd_of _ _ (Z_to_bv 64 (0 + 1585176 + _)) = _ => exact (civF 0 0x183018 4 0 (SLit 0) HCSD' eq_refl ltac:(lia) ltac:(lia))
       | |- forall j, _ -> rd_of _ _ (Z_to_bv 64 (0 + 1584924 + _)) = _ => exact (civF 0 0x182f1c 4 0 (SLit 0) HDIE' eq_refl ltac:(lia) ltac:(lia))
       | |- forall j, _ -> rd_of _ _ (Z_to_bv 64 (0 + (QG + 72) + _)) = _ => exact (civF 0 (QG + 72) 8 _ (SVar 136) HJmin' ltac:(cbn [eval]; rewrite E136; reflexivity) ltac:(unfold QG; lia) ltac:(unfold QG; lia))
       | |- forall j, _ -> rd_of _ _ (Z_to_bv 64 (ag_thread _ + 208 + 2576 + _)) = _ => exact (civF _ 2576 8 _ (SVar 131) HJst' ltac:(cbn [eval]; rewrite E131; reflexivity) ltac:(lia) ltac:(lia))
       | |- forall j, _ -> rd_of _ _ (Z_to_bv 64 (8 * _ + 992776 + _)) = _ => exact (civF _ 992776 8 0 (SLit 0) IAMc eq_refl ltac:(lia) ltac:(lia))
       | |- forall j, _ -> rd_of _ _ (Z_to_bv 64 (p + -16 + _)) = _ => exact (civF p (-16) 4 _ (SVar 104) HHW' ltac:(cbn [eval]; rewrite E104; reflexivity) ltac:(lia) ltac:(lia))
       | |- forall j, _ -> rd_of _ _ (Z_to_bv 64 (p + -12 + _)) = _ => exact (civF p (-12) 4 _ (SVar 103) HNLO' ltac:(cbn [eval]; rewrite E103; reflexivity) ltac:(lia) ltac:(lia))
       | |- forall j, _ -> rd_of _ _ _ = _ => cbn [eval]; unfold QG, DPMCELL, MLIMCELL; rewrite ?E151, ?E152, ?E153, ?E154, ?E155; civ_any2F HR
       end.
Qed.

Lemma civF' : ltac2:(tb__ "0|4|
S0S0S0S3S0S3cS49Vm;S4aR6R3R2A3A2S14S0R7S19R6R5A2A3S14S3aQ40M0A1S3dVrho1;R3A2S39G0R4A2A3S18Z0M1R9A2S18S19RaS1cR7A1A2S1bZ2Z40A2A2S3Sa9R1R9A2S14SbS3aQ8M2A1M3A1S80Vsegs;S3eVrho1;A1S39G0S19S19RcRbA2S1cR2A1A2A2A3ScG3S79G3R2S45RaS3dVrho1;R8A2A2S39G2G1A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;Fe;Fv;Fk;Foff;Fb;Fa;").
Proof. intros a b off k v e Hc -> He B1 B2. eapply civ_cell; eauto. Qed.

Lemma geomF : ltac2:(tb__ "0|b|
S13S18Z1000M0S25VG;A1M1A2S13S18S19G1G0A2M2S27VG;A1M3A2S13S14S0S1eG1S8fA2Z0M4A3S13S18G0S2bVG;A1M5A2S13S18S19G5G0A2M6G3A2S13S18S83S28VG;A1M7A2S13S18S19S19G7S84A2G0A2G3A2S13S14S0S1eG7S1bZ2M8Z10A2A2G4A3S13S13S18G4S32VG;A1M9A2S1aG9S33VG;A1MaA2A2S13S18GaS1bG8Z2fA2A2S13S15S18G2G5A2S18G6G1A2A2S13S13S18Z7fff7f800000G3A2S18G3Z7fffff800000A2A2S13S15S18G2S87A2S18S85G1A2A2S13S15S18G6S87A2S18S85G5A2A2S13S15S18G2S89A2S18S88G1A2A2S15S18G6S89A2S18S88G5A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  unfold G. pose proof HA as (HG & _). pose proof (geom_old _ HG) as HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23).
  pose proof (geom_bands _ HG) as (_ & TB & CB & _ & TI & CI & _). pose proof (topG_range (aa_geom A)) as TR.
  repeat split; assumption || lia.
Qed.

Lemma geomTI : ltac2:(tb__ "0|1|
S15S18S19S25VG;A1M0Z1000A2Z10000A2S18Z646000G0A2A2").
Proof. unfold G. pose proof HA as (HG & _). pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI. exact TI. Qed.

Lemma E_cQ : ltac2:(tb__ "0|0|
S14S0S3bQ40S3dVrho1;S50A2A2S19S25VG;A1Z50A2A3").
Proof.
  pose proof geomF as (T1 & T2 & _). pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. unfold HIGH_SHADOW_END in T1. unfold G in *.
  cbn [eval cQ vT]. change (rw rho1 151%positive) with (Z_to_bv 64 (ag_thread (aa_geom A))).
  rewrite add_val, !u64_lit by lia. apply Z.mod_small. lia.
Qed.
Lemma E_vQB : ltac2:(tb__ "0|1|
S16S14S6S23A1S24VA;A1S7S23A1A3A1S14S3aQ40M0A1S3dVrho1;S99A2S39G0S26S56VA;A1A1A2A3F_;").
Proof. intros HNE. cbn [eval vQB]. change (rw rho1 122%positive) with (Z_to_bv 64 (match aa_q_thread A with [] => j_qb jv | _ => qb_addr (lastq A) end)). destruct (aa_q_thread A); [congruence | reflexivity]. Qed.
Lemma E_vQF : ltac2:(tb__ "0|1|
S16S14S6S23A1S24VA;A1S7S23A1A3A1S14S3aQ40M0A1S3dVrho1;S9aA2S39G0S26S66VA;A1A1A2A3F_;").
Proof. intros HNE. cbn [eval vQF]. change (rw rho1 121%positive) with (Z_to_bv 64 (match aa_q_thread A with [] => j_qf jv | _ => qb_addr (firstq A) end)). destruct (aa_q_thread A); [congruence | reflexivity]. Qed.
Lemma E_vQBe : ltac2:(tb__ "0|1|
S14S6S23A1S24VA;A1S7S23A1A3S14S3aQ40M0A1S3dVrho1;S99A2S39G0S5bVjv;A1A2A3F_;").
Proof. intros HE. cbn [eval vQB]. change (rw rho1 122%positive) with (Z_to_bv 64 (match aa_q_thread A with [] => j_qb jv | _ => qb_addr (lastq A) end)). rewrite HE. reflexivity. Qed.
Lemma E_vQFe : ltac2:(tb__ "0|1|
S14S6S23A1S24VA;A1S7S23A1A3S14S3aQ40M0A1S3dVrho1;S9aA2S39G0S5cVjv;A1A2A3F_;").
Proof. intros HE. cbn [eval vQF]. change (rw rho1 121%positive) with (Z_to_bv 64 (match aa_q_thread A with [] => j_qf jv | _ => qb_addr (firstq A) end)). rewrite HE. reflexivity. Qed.
Lemma E_vQN : ltac2:(tb__ "0|1|
S14S3aQ40M0A1S3dVrho1;Sa5A2S39G0S1cSaS23S24VA;A1A2A1A2A3"). Proof. reflexivity. Qed.
Lemma E_vQS : ltac2:(tb__ "0|1|
S14S3aQ40M0A1S3dVrho1;S9dA2S39G0S93S24VA;A1A1A2A3"). Proof. reflexivity. Qed.
Lemma E_vNX : ltac2:(tb__ "0|1|
S14S3aQ40M0A1S3dVrho1;S9cA2S39G0Z0A2A3"). Proof. reflexivity. Qed.
Lemma E_vBS : ltac2:(tb__ "0|1|
S14S3aQ40M0A1S3dVrho1;S9bA2S39G0S2fS56VA;A1A1A2A3"). Proof. reflexivity. Qed.
Lemma E_vK : ltac2:(tb__ "0|1|
S14S3aQ40M0A1S3dVrho1;Sa2A2S39G0S1cSaS5S0S0A2S29S56VA;A1A1A2A1A2A3"). Proof. reflexivity. Qed.
Lemma E_vPK : ltac2:(tb__ "0|1|
S14S3aQ40M0A1S3dVrho1;Sa4A2S39G0S5fVA;A1A2A3"). Proof. reflexivity. Qed.
Lemma E_vMX : ltac2:(tb__ "0|1|
S14S3aQ40M0A1S3dVrho1;Sa3A2S39G0S8cZ18A1A2A3"). Proof. reflexivity. Qed.
Lemma E_vCS : ltac2:(tb__ "0|1|
S14S3aQ40M0A1S3dVrho1;Sa1A2S39G0S8aZ18A1A2A3"). Proof. reflexivity. Qed.
Lemma E_vCP : ltac2:(tb__ "0|1|
S14S3aQ40M0A1S3dVrho1;Sa0A2S39G0S5eVA;A1A2A3"). Proof. reflexivity. Qed.

Lemma E_item : ltac2:(tb__ "0|1|
S16S14S6S23A1S24VA;A1S7S23A1A3A1S26S56VA;A1M0A1S0S1cSaS5S0S0A2S29G0A1A2A1S0S18S83R2A2S18S19R3S8bA2Z7fffff800000A2S18R3S82A2S14S0S3bQ40S3dVrho1;S9eA2A2S19R5S1dZ8R4A2A2A3F_;F_;F_;Tk;Tqb;F_;").
Proof.
  intros HNE qb k Q1 Q2 Q3. pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. unfold HIGH_SHADOW_END, kQuarantineBatchSize, kQuarantineBatchCount in *.
  cbn [eval item_base add]. rewrite (E_vQB HNE). fold vK. rewrite E_vK. fold qb k.
  rewrite add_val, sll_val, !u64_lit by lia. change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (k * 2 ^ 3)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma E_cp : ltac2:(tb__ "0|2|
S13S18Z1M0S5fVA;A1M1A2S18G1Z2A2A2S14S0S3bQ40S3dVrho1;S51A2A2S19S19S25VG;A1Zd0A2S1dZ4S1fG1G0A2A2A2A3F_;").
Proof.
  intros HC. pose proof geomF as (T1 & T2 & _). pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. unfold HIGH_SHADOW_END in T1. unfold G in *.
  cbn [eval cp_baseF cA vT]. change (rw rho1 151%positive) with (Z_to_bv 64 (ag_thread (aa_geom A))). fold vPK. rewrite E_vPK.
  rewrite !add_val, sll_val, add_val, (lit_unsigned (-1)), !u64_lit by lia. change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by lia.
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
  replace ((cnt24 A + (2 ^ 64 - 1)) mod 2 ^ 64) with (cnt24 A - 1)
    by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
  rewrite (Z.mod_small ((cnt24 A - 1) * 2 ^ 2)) by lia. rewrite (Z.mod_small (ag_thread (aa_geom A) + 208)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma E_nb : ltac2:(tb__ "0|3|
S13S18Z0S5eVA;A1M0A2S1aG0S1bZ2M1Z1cA2A2A2S18S83S28VG;A1M2A2S18S19S19G2S84A2Z1000A2Z7fffff800000A2S14S0S3bQ40S3dVrho1;S9fA2A2S19S19G2S1dZ18S1bG1Z20A2A2A2S1dZ10G0A2A2A3F_;F_;F_;").
Proof.
  intros HX S1 S2. pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1. unfold G in *.
  cbn [eval nb_base add OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states.vSB]. change (rw rho1 155%positive) with (Z_to_bv 64 (ag_spacebeg (aa_geom A))). fold vCP. rewrite E_vCP.
  rewrite (ext_low_small false 32) by (rewrite ?u64_lit by lia; cbn; lia).
  rewrite !add_val, sll_val, !u64_lit by (unfold C24OFF; lia). change (4 mod 64) with 4. rewrite Z.shiftl_mul_pow2 by lia. unfold C24OFF.
  rewrite (Z.mod_small (top24 A * 2 ^ 4)) by lia. rewrite (Z.mod_small (ag_spacebeg (aa_geom A) + 24 * 2 ^ 32)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Ltac carve_hdr E :=
  unfold carve_ok; rewrite !E;
  split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|];
  split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|];
  change (rm rho1) with (rm rho); split; [|unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; cbn beta iota].

Lemma carve_cQ : ltac2:(tb__ "0|5|
S16S14S6S23A1S24VA;A1S7S23A1A3A1S69Vrho1;S2S5S5S3cS0A2M0S0A2S6S5S5S0S3A2M1S3cA2M2A1S2G0S0S2S3cS0S50Z0M3A4Z20A4S4G2S2G1S3cS2S0S3G3U8M4A4Sa5A4S4G2S2G1S3cS2S0S3Z8G4A4S9aA4S4G2S2G1S3cS2S0S3Z10G4A4S99A4S4G2S2G1S3cS2S0S3Z18G4A4S9dA4S7G2A1A3A3A3A3A4A2F_;").
Proof.
  intros HNE. pose proof geomF as (T1 & T2 & _). pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. unfold HIGH_SHADOW_END in T1.
  pose proof qF as QF. cbn zeta in QF. destruct QF as (Qn & Qp & Qs & _ & _ & QL). destruct (QL HNE) as (Qf & Qb & _). clear QL.
  pose proof E_cQ as E. pose proof geomTI as TI. unfold G in *.
  carve_hdr E.
  - intros off Hoff. destruct (Z_lt_dec off 8); [apply (wrF2 _ _ _ _ Qn); cbn [Z.of_nat]; lia|].
    destruct (Z_lt_dec off 24); [apply (wrP2 _ _ _ Qp); lia|]. apply (wrF2 _ _ _ _ Qs); cbn [Z.of_nat]; lia.
  - eapply (civF' _ _ _ _ _ _ Qn); [lia | apply E_vQN | lia | cbn [Z.of_nat]; lia].
  - eapply (civF' _ _ _ _ _ _ Qf); [lia | apply (E_vQF HNE) | lia | cbn [Z.of_nat]; lia].
  - eapply (civF' _ _ _ _ _ _ Qb); [lia | apply (E_vQB HNE) | lia | cbn [Z.of_nat]; lia].
  - eapply (civF' _ _ _ _ _ _ Qs); [lia | apply E_vQS | lia | cbn [Z.of_nat]; lia].
Qed.
Lemma carve_cQe : ltac2:(tb__ "0|5|
S14S6S23A1S24VA;A1S7S23A1A3S69Vrho1;S2S5S5S3cS0A2M0S0A2S6S5S5S0S3A2M1S3cA2M2A1S2G0S0S2S3cS0S50Z0M3A4Z20A4S4G2S2G1S3cS2S0S3G3U8M4A4S44G3A1A4S4G2S2G1S3cS2S0S3Z8G4A4S9aA4S4G2S2G1S3cS2S0S3Z10G4A4S99A4S4G2S2G1S3cS2S0S3Z18G4A4S9dA4S7G2A1A3A3A3A3A4A2F_;").
Proof.
  intros HE. pose proof geomF as (T1 & T2 & _). pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. unfold HIGH_SHADOW_END in T1.
  pose proof qF as QF. cbn zeta in QF. destruct QF as (Qn & Qp & Qs & _). rewrite HE in Qn, Qs. cbn [length Z.of_nat qsize] in Qn, Qs.
  destruct Hjv as (_ & _ & _ & _ & _ & _ & HJq). destruct (HJq HE) as [Qf Qb].
  pose proof E_cQ as E. pose proof geomTI as TI. unfold G in *.
  carve_hdr E.
  - intros off Hoff. destruct (Z_lt_dec off 8); [apply (wrF2 _ _ _ _ Qn); cbn [Z.of_nat]; lia|].
    destruct (Z_lt_dec off 24); [apply (wrP2 _ _ _ Qp); lia|]. apply (wrF2 _ _ _ _ Qs); cbn [Z.of_nat]; lia.
  - eapply (civF' _ _ _ _ _ _ Qn); [lia | reflexivity | lia | cbn [Z.of_nat]; lia].
  - eapply (civF' _ _ _ _ _ _ Qf); [lia | apply (E_vQFe HE) | lia | cbn [Z.of_nat]; lia].
  - eapply (civF' _ _ _ _ _ _ Qb); [lia | apply (E_vQBe HE) | lia | cbn [Z.of_nat]; lia].
  - eapply (civF' _ _ _ _ _ _ Qs); [lia | rewrite E_vQS, HE; reflexivity | lia | cbn [Z.of_nat]; lia].
Qed.
Lemma carve_bh : ltac2:(tb__ "0|5|
S16S14S6S23A1S24VA;A1S7S23A1A3A1S69Vrho1;S2S5S5S3cS0A2M0S0A2S6S5S5S0S3A2M1S3cA2M2A1S2G0S0S2S3cS0S99Z0M3A4Z18A4S4G2S2G1S3cS2S0S3G3U8M4A4S9cA4S4G2S2G1S3cS2S0S3Z8G4A4S9bA4S4G2S2G1S3cS2S0S3Z10G4A4Sa2A4S7G2A1A3A3A3A4A2F_;").
Proof.
  intros HNE. pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2.
  pose proof qF as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & _ & _ & QL).
  destruct (QL HNE) as (_ & _ & B0 & B8 & B16 & BK & BP & B16a & BS1 & BS2 & _). clear QL.
  pose proof geomF as (_ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2, BS2. unfold HIGH_SHADOW_END, kQuarantineBatchSize in *.
  assert (E : bv_unsigned (eval rho1 vQB) = qb_addr (last (aa_q_thread A) qb_dflt)) by (rewrite (E_vQB HNE); unfold lastq; apply u64_lit; lia).
  unfold G in *.
  carve_hdr E.
  - intros off Hoff. destruct (Z_lt_dec off 8); [apply (wrF _ _ _ _ B0); cbn [Z.of_nat]; lia|].
    destruct (Z_lt_dec off 16); [apply (wrF _ _ _ _ B8); cbn [Z.of_nat]; lia|]. apply (wrF _ _ _ _ B16); cbn [Z.of_nat]; lia.
  - eapply (civF' _ _ _ _ _ _ B0); [lia | apply E_vNX | lia | cbn [Z.of_nat]; lia].
  - eapply (civF' _ _ _ _ _ _ B8); [lia | apply E_vBS | lia | cbn [Z.of_nat]; lia].
  - eapply (civF' _ _ _ _ _ _ B16); [lia | apply E_vK | lia | cbn [Z.of_nat]; lia].
Qed.
Lemma carve_bhf : ltac2:(tb__ "0|5|
S16S14S6S23A1S24VA;A1S7S23A1A3A1S14S0S1cSaS5S0S0A2S29S56VA;A1A1A2A1S82A3S69Vrho1;S2S5S5S3cS0A2M0S0A2S6S5S5S0S3A2M1S3cA2M2A1S2G0S0S2S3cS0S99Z0M3A4Z18A4S4G2S2G1S3cS2S0S3G3U8M4A4S9cA4S4G2S2G1S3cS2S0S3Z8G4A4S9bA4S4G2S2G1S3cS2S0S3Z10G4A4S44Z3fdA1A4S7G2A1A3A3A3A4A2F_;F_;").
Proof.
  intros HNE HK. pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2.
  pose proof qF as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & _ & _ & QL).
  destruct (QL HNE) as (_ & _ & B0 & B8 & B16 & BK & BP & B16a & BS1 & BS2 & _). clear QL.
  pose proof geomF as (_ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2, BS2. unfold HIGH_SHADOW_END, kQuarantineBatchSize in *.
  assert (E : bv_unsigned (eval rho1 vQB) = qb_addr (last (aa_q_thread A) qb_dflt)) by (rewrite (E_vQB HNE); unfold lastq; apply u64_lit; lia).
  unfold lastq, kQuarantineBatchCount in HK. rewrite HK in B16. unfold G in *.
  carve_hdr E.
  - intros off Hoff. destruct (Z_lt_dec off 8); [apply (wrF _ _ _ _ B0); cbn [Z.of_nat]; lia|].
    destruct (Z_lt_dec off 16); [apply (wrF _ _ _ _ B8); cbn [Z.of_nat]; lia|]. apply (wrF _ _ _ _ B16); cbn [Z.of_nat]; lia.
  - eapply (civF' _ _ _ _ _ _ B0); [lia | apply E_vNX | lia | cbn [Z.of_nat]; lia].
  - eapply (civF' _ _ _ _ _ _ B8); [lia | apply E_vBS | lia | cbn [Z.of_nat]; lia].
  - eapply (civF' _ _ _ _ _ _ B16); [lia | reflexivity | lia | cbn [Z.of_nat]; lia].
Qed.
Lemma carve_item : ltac2:(tb__ "0|2|
S16S14S6S23A1S24VA;A1S7S23A1A3A1S1aS1cSaS5S0S0A2S29S56VA;A1A1A2A1S82A2S69Vrho1;S2S5S5S3cS0A2M0S0A2S6S5S5S0S3A2S3cA2M1A1S2G0S0S2S3cS0S9eZ18A4Z20A4S7G1A1A4A2F_;F_;").
Proof.
  intros HNE HK. pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2.
  pose proof qF as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & _ & _ & QL).
  destruct (QL HNE) as (_ & _ & B0 & B8 & B16 & BK & BP & B16a & BS1 & BS2 & _). clear QL.
  pose proof geomF as (_ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2, BS2. unfold HIGH_SHADOW_END in *.
  pose proof (E_item HNE) as E. cbn zeta in E. unfold lastq, kQuarantineBatchCount, kQuarantineBatchSize, HIGH_SHADOW_END in *.
  specialize (E ltac:(lia) ltac:(lia) ltac:(lia)). unfold G in *.
  carve_hdr E.
  intros off Hoff. apply (wrP _ _ _ BP); lia.
Qed.
Lemma carve_pc : ltac2:(tb__ "0|5|
S14S8S2cVA;A1S9A3S16S14S6S0A1S5aVA;A1S7S0A1A3A1S69Vrho1;S2S5S5S3cS0A2M0S0A2S6S5S5S0S3A2M1S3cA2M2A1S2G0S0S2S3cS0S53Z780M3A4Z790A4S4G2S2G1S3cS2S0S3G3U4M4A4Sa4A4S4G2S2G1S3cS2S0S3Z784G4A4Sa3A4S4G2S2G1S3cS2S0S3Z788U8A4Sa1A4S7G2A1A3A3A3A4A2F_;F_;").
Proof.
  intros HCI HNE. pose proof geomF as (T1 & T2 & _). pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. unfold HIGH_SHADOW_END in T1.
  pose proof (cF HCI HNE) as CF. cbn zeta in CF. destruct CF as (C0 & C4 & C8 & _).
  assert (E : bv_unsigned (eval rho1 cA) = ag_thread G + 208).
  { cbn [eval cA vT]. change (rw rho1 151%positive) with (Z_to_bv 64 (ag_thread G)). unfold G in *. rewrite add_val, !u64_lit by lia. apply Z.mod_small. lia. }
  pose proof geomTI as TI. unfold G in *.
  carve_hdr E.
  - intros off Hoff. destruct (Z_lt_dec off 1924); [apply (wrF2 _ _ _ _ C0); cbn [Z.of_nat]; lia|].
    destruct (Z_lt_dec off 1928); [apply (wrF2 _ _ _ _ C4); cbn [Z.of_nat]; lia|]. apply (wrF2 _ _ _ _ C8); cbn [Z.of_nat]; lia.
  - eapply (civF' _ _ _ _ _ _ C0); [lia | apply E_vPK | lia | cbn [Z.of_nat]; lia].
  - eapply (civF' _ _ _ _ _ _ C4); [lia | apply E_vMX | lia | cbn [Z.of_nat]; lia].
  - eapply (civF' _ _ _ _ _ _ C8); [lia | apply E_vCS | lia | cbn [Z.of_nat]; lia].
Qed.
Lemma carve_pck : ltac2:(tb__ "0|4|
S14S8S2cVA;A1S9A3S16S14S6S0A1S5aVA;A1S7S0A1A3A1S69Vrho1;S2S5S5S3cS0A2M0S0A2S6S5S5S0S3A2M1S3cA2M2A1S2G0S0S2S3cS0S51Z790M3A4Z794A4S4G2S2G1S3cS2S0S3G3U4A4Sa0A4S7G2A1A3A4A2F_;F_;").
Proof.
  intros HCI HNE. pose proof geomF as (T1 & T2 & _). pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. unfold HIGH_SHADOW_END in T1.
  pose proof (cF HCI HNE) as CF. cbn zeta in CF. destruct CF as (_ & _ & _ & CX & CN & _).
  pose proof (E_cp CN) as E. pose proof geomTI as TI. unfold G in *.
  carve_hdr E.
  - intros off Hoff. apply (wrF2 _ _ _ _ CX); cbn [Z.of_nat]; lia.
  - eapply (civF' _ _ _ _ _ _ CX); [lia | apply E_vCP | lia | cbn [Z.of_nat]; lia].
Qed.
Lemma carve_nb : ltac2:(tb__ "0|2|
S14S8S2cVA;A1S9A3S16S14S6S0A1S5aVA;A1S7S0A1A3A1S69Vrho1;S2S5S5S3cS0A2M0S0A2S6S5S5S0S3A2S3cA2M1A1S2G0S0S2S3cS0S9fZ0A4Z2000A4S7G1A1A4A2F_;F_;").
Proof.
  intros HCI HNE. pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2.
  pose proof (cF HCI HNE) as CF. cbn zeta in CF. destruct CF as (_ & _ & _ & _ & CN & CX & NP & _ & _ & _ & _ & S2 & S1 & _).
  pose proof (E_nb CX S1 ltac:(clear -S2 ACV; lia)) as E. rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1. unfold G in *.
  carve_hdr E.
  intros off Hoff. apply (wrP _ _ _ NP); lia.
Qed.

Theorem carve_NV : ltac2:(tb__ "0|0|
S4fS55R1VA;A2S77S74S69Vrho1;A1S6cR2A1A3F_;Fq;").
Proof.
  intros [| |] QC; cbn [qcond] in QC; unfold NV.
  - destruct QC as [HNE HK]. repeat apply Forall_cons; [apply (carve_cQ HNE) | apply (carve_bh HNE) | apply (carve_item HNE HK) | apply Forall_nil].
  - destruct QC as (HE & HCI & HNE). repeat apply Forall_cons; [apply (carve_cQe HE) | apply (carve_pc HCI HNE) | apply (carve_pck HCI HNE) | apply (carve_nb HCI HNE) | apply Forall_nil].
  - destruct QC as (HNE & HK & HCI & HNC). repeat apply Forall_cons;
      [apply (carve_cQ HNE) | apply (carve_bhf HNE HK) | apply (carve_pc HCI HNC) | apply (carve_pck HCI HNC) | apply (carve_nb HCI HNC) | apply Forall_nil].
Qed.

Let qbF : Z := qb_addr (lastq A).
Let nbF : Z := ltac2:(tb__ "0|0|
S19S19S28VG;A1S1dZ18S1bZ2Z20A2A2A2S1dZ10S5eVA;A1A2A2").
Let zbF (z : nat) : Z := ltac2:(tb__ "0|0|
S3S0Lz;Vz;Z0S3S3S0Ln0;R1S25VG;A1S3S3S0Ln1;R1S2bVG;A1S3S3S0Ln2;R1Vp;S3S3S0Ln3;R1VqbF;S3VnbF;Ln4;X3x2Ln3;X3x2Ln2;X3x2Ln1;X3x2Ln0;X3x2").

Lemma zsepF : ltac2:(tb__ "0|2|
S4fS55R1VA;A2S3S3S7aS3R2S59R4A1A3S7aS3R2S59R5A1A3S16S14S3R4R3A3A1S15S18S19VzbF;R5A1M0S57R5A1A2S19VzbF;R4A1M1S58R4A1A2A2S18S19G1S57R4A1A2S19G0S58R5A1A2A2A2F_;F_;F_;Fz';Fz;F_;Fq;").
Proof.

  intros q QC.
  assert (Q4 : In 4%nat (ZU q) -> nbF = nbF /\ (qbF + 8192 <= ag_thread G \/ ag_thread G + 0x1000 <= qbF) /\ (qbF + 8192 <= ag_ctx G \/ ag_ctx G + 0x1000 <= qbF)
                                /\ (p + N8 n <= qbF \/ qbF + 8192 <= p - 16) /\ ag_spacebeg G <= qbF).
  { intros H4. assert (HNE : aa_q_thread A <> []) by (destruct q; cbn in H4, QC; intuition congruence || (exfalso; intuition lia)).
    pose proof qF as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & _ & _ & QL).
    destruct (QL HNE) as (_ & _ & _ & _ & _ & _ & _ & _ & BS1 & _ & BT' & BC' & BP'). unfold kQuarantineBatchSize in *. unfold qbF, lastq.
    split; [reflexivity|]. split; [exact BT'|]. split; [exact BC'|]. split; [exact BP'|]. exact BS1. }
  assert (Q5 : In 5%nat (ZU q) -> (nbF + 8192 <= ag_thread G \/ ag_thread G + 0x1000 <= nbF) /\ (nbF + 8192 <= ag_ctx G \/ ag_ctx G + 0x1000 <= nbF)
                                /\ (p + N8 n <= nbF \/ nbF + 8192 <= p - 16) /\ (In 4%nat (ZU q) -> qbF + 8192 <= nbF \/ nbF + 8192 <= qbF) /\ ag_spacebeg G <= nbF).
  { intros H5. assert (HC : aa_cache_inited A = true /\ cache24 A <> []) by (destruct q; cbn in H5, QC; intuition congruence || (exfalso; intuition lia)).
    destruct HC as [HCI HNC]. pose proof (cF HCI HNC) as CF. cbn zeta in CF. destruct CF as (_ & _ & _ & _ & _ & CX & _ & NT & NC & NP & NQ & _).
    unfold nbF, qbF, lastq. unfold kQuarantineBatchSize in NQ.
    split; [exact NT|]. split; [exact NC|]. split; [exact NP|]. split; [|clear -CX; unfold G; lia].
    intros H4. apply NQ. clear -H4 QC. destruct q; cbn in H4, QC; intuition congruence || (exfalso; intuition lia). }
  assert (HZ : forall y, In y (ZU q) -> (y = 0 \/ y = 1 \/ y = 2 \/ y = 3 \/ (y = 4 /\ In 4 (ZU q)) \/ (y = 5 /\ In 5 (ZU q)))%nat).
  { clear Q4 Q5. intros y Hy. destruct q; cbn in Hy |- *; intuition lia. }
  pose proof geomF as (T1 & T2 & _ & C1 & C2 & S1 & S2 & _ & _ & _ & TC & TR & TI & CI & TB & CB).
  pose proof blkF_geom as (B1 & _ & B3 & B4 & BT & BC & BN & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & _).
  rewrite kSpaceSize_val in S2. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, HIGH_SHADOW_END, IMG_LO, IMG_HI, LOW_SHADOW_BEG in *.
  unfold G in *.

  assert (P01 : 0 + 0x646000 <= ag_thread (aa_geom A) + 0 \/ ag_thread (aa_geom A) + 0x1000 <= 0 + 0xe4000) by (clear -TI; lia).
  assert (P02 : 0 + 0x646000 <= ag_ctx (aa_geom A) + 8 \/ ag_ctx (aa_geom A) + 0x1000 <= 0 + 0xe4000) by (clear -CI; lia).
  assert (P03 : 0 + 0x646000 <= p + -16 \/ p + 0 <= 0 + 0xe4000) by (clear -B1; lia).
  assert (P12 : ag_thread (aa_geom A) + 0x1000 <= ag_ctx (aa_geom A) + 8 \/ ag_ctx (aa_geom A) + 0x1000 <= ag_thread (aa_geom A) + 0) by (clear -TC; lia).
  assert (P13 : ag_thread (aa_geom A) + 0x1000 <= p + -16 \/ p + 0 <= ag_thread (aa_geom A) + 0) by (clear -BT N1 B3; lia).
  assert (P23 : ag_ctx (aa_geom A) + 0x1000 <= p + -16 \/ p + 0 <= ag_ctx (aa_geom A) + 8) by (clear -BC B3; lia).
  assert (P4 : In 4%nat (ZU q) ->
     (0 + 0x646000 <= qbF + 0 \/ qbF + 8192 <= 0 + 0xe4000)
     /\ (ag_thread (aa_geom A) + 0x1000 <= qbF + 0 \/ qbF + 8192 <= ag_thread (aa_geom A) + 0)
     /\ (ag_ctx (aa_geom A) + 0x1000 <= qbF + 0 \/ qbF + 8192 <= ag_ctx (aa_geom A) + 8)
     /\ (p + 0 <= qbF + 0 \/ qbF + 8192 <= p + -16)).
  { intros H4. destruct (Q4 H4) as (_ & X1 & X2 & X3 & X4). split; [clear -X4 S1; lia|]. split; [clear -X1; lia|]. split; [clear -X2; lia|]. clear -X3 N1 B3; lia. }
  assert (P5 : In 5%nat (ZU q) ->
     (0 + 0x646000 <= nbF + 0 \/ nbF + 8192 <= 0 + 0xe4000)
     /\ (ag_thread (aa_geom A) + 0x1000 <= nbF + 0 \/ nbF + 8192 <= ag_thread (aa_geom A) + 0)
     /\ (ag_ctx (aa_geom A) + 0x1000 <= nbF + 0 \/ nbF + 8192 <= ag_ctx (aa_geom A) + 8)
     /\ (p + 0 <= nbF + 0 \/ nbF + 8192 <= p + -16)
     /\ (In 4%nat (ZU q) -> qbF + 8192 <= nbF + 0 \/ nbF + 8192 <= qbF + 0)).
  { intros H5. destruct (Q5 H5) as (X1 & X2 & X3 & X4 & X5). split; [clear -X5 S1; lia|]. split; [clear -X1; lia|]. split; [clear -X2; lia|].
    split; [clear -X3 N1 B3; lia|]. intros H4. specialize (X4 H4). clear -X4. lia. }
  assert (SYM : forall a b c d : Z, a <= b \/ c <= d -> c <= d \/ a <= b) by (clear; intros; lia).
  clear Q4 Q5 T1 T2 C1 C2 S1 S2 TC TR TI CI TB CB B1 B3 B4 BT BC BN N1.
  intros z z' Hz Hz' NE.
  destruct (HZ z Hz) as [-> |[-> |[-> |[-> |[[-> H4]|[-> H5]]]]]]; destruct (HZ z' Hz') as [-> |[-> |[-> |[-> |[[-> H4']|[-> H5']]]]]];
    try (exfalso; apply NE; reflexivity); cbn [zbF zloF zhiF];
    try match goal with H : In 4%nat (ZU q) |- _ => pose proof (P4 H) as (P04 & P14 & P24 & P34) end;
    try match goal with H : In 5%nat (ZU q) |- _ => pose proof (P5 H) as (P05 & P15 & P25 & P35 & P45Q) end;
    try match goal with H : In 4%nat (ZU q), H' : In 5%nat (ZU q) |- _ => pose proof (P45Q H) as P45 end;
    first [ assumption | apply SYM; assumption ].
Qed.
Lemma inz_NRT : ltac2:(tb__ "0|0|
S6S3A1S3SaaR1U3A2S7aS3R2R3A3F_;Fz;S7cS3fS71S72Vrho1;VzbF;S58S57R2A5S78S74S3fS75S6bA4S60A5F_;Fzused;").
Proof.
  intros zused HU. pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. pose proof geomF as (T1 & T2 & _). unfold HIGH_SHADOW_END in T1.
  pose proof blkF_geom as (B1 & B2 & B3 & B4 & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & _). unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  assert (E151 : rw rho1 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))) by reflexivity.
  assert (E152 : rw rho1 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))) by reflexivity.
  assert (E12 : rw rho1 12%positive = rw rho 12%positive) by reflexivity.
  pose proof (urange (rw rho 12%positive)) as U12.
  assert (P15 : 0 <= p / 2 ^ 32 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Eiam : bv_unsigned (alu64 ALU_SLL (alu64 ALU_SRL (rw rho 12%positive) (Z_to_bv 64 32)) (Z_to_bv 64 3)) = 8 * (p / 2 ^ 32)).
  { rewrite sll_val, srl_val, Hp12. change (32 mod 64) with 32. change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
    rewrite Z.mod_small by lia. lia. }
  pose proof geomF as (_ & _ & _ & C1 & C2 & _). unfold HIGH_SHADOW_END in C1. unfold G in *. clear B2.
  assert (EcA : bv_unsigned (eval rho1 cA) = ag_thread (aa_geom A) + 208) by (cbn [eval cA vT]; rewrite E151, add_val, !u64_lit by lia; apply Z.mod_small; lia).
  unfold NRT, N_rest, N_fn, ZD_NRT. cbn [tl app map carve_obj]. unfold iam_base. unfold vT, vCTX, vTOP, vBOT, vSB, vMINq, vST, vHW, vNLO. unfold QG, DPMCELL, MLIMCELL.
  repeat apply Forall2_cons; try apply Forall2_nil.
  all: unfold in_zone; split; [apply HU; lia | split; [cbn; lia | split; [cbn; lia | right]]].
  all: unfold carved; rewrite obj_range_mk by lia; cbn [fst snd eval zbF]; rewrite ?E151, ?E152, ?E12, ?Hp12, ?Eiam, ?EcA, ?u64_lit by lia; lia.
Qed.

Lemma inz_NV : ltac2:(tb__ "0|0|
S4fS55R1VA;A2S7cS3fS71S72Vrho1;VzbF;S58S57S59R2A1A5S78S74S3fS75S6cR2A1A4S61R2A1A5F_;Fq;").
Proof.
  intros q QC. pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. pose proof geomF as (T1 & T2 & _ & _ & _ & S1 & S2 & _). unfold HIGH_SHADOW_END in T1.
  pose proof E_cQ as EQ.
  assert (EcA : bv_unsigned (eval rho1 cA) = ag_thread (aa_geom A) + 208).
  { cbn [eval cA vT]. change (rw rho1 151%positive) with (Z_to_bv 64 (ag_thread G)). unfold G in *. rewrite add_val, !u64_lit by lia. apply Z.mod_small. lia. }
  assert (HB : aa_q_thread A <> [] -> bv_unsigned (eval rho1 vQB) = qbF /\ HIGH_SHADOW_END <= qbF /\ qbF + kQuarantineBatchSize <= 140737479966720
                                     /\ Z.of_nat (length (qb_items (lastq A))) <= kQuarantineBatchCount).
  { intros HNE. pose proof qF as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & _ & _ & QL).
    destruct (QL HNE) as (_ & _ & _ & _ & _ & BK & _ & _ & BS1 & BS2 & _). clear QL. rewrite kSpaceSize_val in S2, BS2.
    unfold qbF, lastq, HIGH_SHADOW_END, kQuarantineBatchSize in *. rewrite (E_vQB HNE). unfold lastq. rewrite u64_lit by lia. repeat split; lia. }
  assert (HC : aa_cache_inited A = true -> cache24 A <> [] -> bv_unsigned (eval rho1 cp_baseF) = ag_thread G + 208 + 4 * (cnt24 A - 1) /\ 1 <= cnt24 A <= 2
                                     /\ bv_unsigned (eval rho1 nb_base) = nbF).
  { intros HCI HNC. pose proof (cF HCI HNC) as CF. cbn zeta in CF. destruct CF as (_ & _ & _ & _ & CN & CX & _ & _ & _ & _ & _ & S2' & S1' & _).
    split; [exact (E_cp CN)|]. split; [exact CN|]. exact (E_nb CX S1' ltac:(clear -S2' ACV; lia)). }
  unfold G in *.
  destruct q; cbn [qcond] in QC; unfold NV, ZD_NV; cbn [map carve_obj].
  - destruct QC as [HNE HK]. destruct (HB HNE) as (EB & Q1 & Q2 & Q3). pose proof (E_item HNE Q1 Q2 Q3) as EI.
    unfold kQuarantineBatchCount, kQuarantineBatchSize, HIGH_SHADOW_END in *.
    repeat apply Forall2_cons; try apply Forall2_nil.
    all: unfold in_zone; split; [cbn; tauto | split; [cbn; lia | split; [cbn; lia | right]]].
    all: unfold carved; rewrite obj_range_mk by lia; cbn [fst snd zbF]; rewrite ?EQ, ?EB, ?EI; unfold qbF; lia.
  - destruct QC as (HE & HCI & HNC). destruct (HC HCI HNC) as (EP & CN & EN).
    repeat apply Forall2_cons; try apply Forall2_nil.
    all: unfold in_zone; split; [cbn; tauto | split; [cbn; lia | split; [cbn; lia | right]]].
    all: unfold carved; rewrite obj_range_mk by lia; cbn [fst snd zbF]; rewrite ?EQ, ?EcA, ?EP, ?EN; lia.
  - destruct QC as (HNE & HK & HCI & HNC). destruct (HB HNE) as (EB & Q1 & Q2 & Q3). destruct (HC HCI HNC) as (EP & CN & EN).
    repeat apply Forall2_cons; try apply Forall2_nil.
    all: unfold in_zone; split; [cbn; tauto | split; [cbn; lia | split; [cbn; lia | right]]].
    all: unfold carved; rewrite obj_range_mk by lia; cbn [fst snd zbF]; rewrite ?EQ, ?EB, ?EcA, ?EP, ?EN; unfold qbF; lia.
Qed.

Lemma inz_NFS : ltac2:(tb__ "0|0|
S4fS55R1VA;A2S7cS3fS71S72Vrho1;VzbF;S58S57S59R2A1A5S78S74S3fS75S6aR2A1A4SeS71S60S61R2A1A3A5F_;Fq;").
Proof.
  intros q QC. unfold NFS. rewrite map_app. apply Forall2_app; [|exact (inz_NV q QC)].
  apply inz_NRT. intros z Hz. destruct z as [|[|[|[|z]]]]; [| | | |lia]; destruct q; cbn; tauto.
Qed.

Theorem pd_NFS : ltac2:(tb__ "0|0|
S4fS55R1VA;A2S48Vrho1;S78S74S3fS75S6aR2A1A4A2F_;Fq;").
Proof.
  intros q QC. apply (zones_pd rho1 zbF zloF zhiF (ZU q) (zsepF q QC) _ (ZD_NRT ++ ZD_NV q)); [exact (inz_NFS q QC) | apply (ZD_chk q)].
Qed.

Lemma zfacts : ltac2:(tb__ "0|3|
S4fS55R1VA;A2S3S7aS3R1S59R3A1A3S16S14S3R2U0A3A1S13S18Z1000S19VzbF;R3A1M0S58R3A1A2M1A2S13S18S19G0S57R3A1A2M2S27VG;A1A2S13S15S18G2S87A2S18S85G1A2A2S13S15S18G2S89A2S18S88G1A2A2S15S18G2Vp;A2S18S19Vp;S70Vn;A1A2G1A2A2A2A2A2A2F_;F_;Fz;F_;Fq;").
Proof.
  intros q QC z Hz NZ.
  assert (HZ : (z = 1 \/ z = 2 \/ z = 3 \/ (z = 4 /\ aa_q_thread A <> []) \/ (z = 5 /\ aa_cache_inited A = true /\ cache24 A <> []))%nat).
  { destruct q; cbn in Hz, QC; intuition (subst; lia || congruence). }
  pose proof (topG_range G) as ACV.
  pose proof geomF as (T1 & T2 & _ & C1 & C2 & S1 & S2 & _ & _ & _ & TC & TR & TI & CI & TB & CB).
  pose proof blkF_geom as (B1 & _ & B3 & B4 & BT & BC & BN & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & _).
  rewrite kSpaceSize_val in S2. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, HIGH_SHADOW_END, IMG_LO, IMG_HI, LOW_SHADOW_BEG in *.
  destruct HZ as [-> |[-> |[-> |[[-> HNE]|[-> [HCI HNC]]]]]]; cbn [zbF zloF zhiF].
  - clear -T1 T2 TI TB BT N1 B3. lia.
  - clear -C1 C2 CI CB BC N1 B3. lia.
  - clear -B1 B3 B4 N1 ACV. lia.
  - pose proof qF as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & _ & _ & QL).
    destruct (QL HNE) as (_ & _ & _ & _ & _ & _ & _ & _ & BS1 & BS2 & _ & _ & BP'). rewrite kSpaceSize_val in BS2. unfold qbF, lastq, kQuarantineBatchSize in *.
    clear -BS1 BS2 BP' S1 S2 N1 B3. lia.
  - pose proof (cF HCI HNC) as CF. cbn zeta in CF. destruct CF as (_ & _ & _ & _ & _ & CX & _ & _ & _ & NP & _). unfold nbF in *.
    clear -CX NP S1 S2 N1 B3. lia.
Qed.

Lemma zone_of_inz : ltac2:(tb__ "0|2|
S4fS3fS71S55R3VA;A2S72Vrho1;VzbF;S58S57S59R4A1R3R2A7S14S8S67R3A1S9A3S1aS10S0S0S46Vrho1;R5A2M0A3S12S0S0G0A3A2S6fS27VG;A1Vp;S70Vn;A1S10S0S0S46Vrho1;R6A2M1A3S12S0S0G1A3A5F_;F_;F_;F_;Fd;Fo;Fq;").
Proof.
  intros q o [[z lo] hi] QC (HU & L1 & L2 & R) Hi NE. unfold img_okb in Hi. unfold zone_ok.
  destruct R as [R|[R1 R2]]; [lia|]. split; [lia|].
  destruct (Nat.eqb_spec z 0) as [->|NZ].
  - left. cbn [zbF zloF zhiF] in *. repeat (apply andb_prop in Hi as [Hi ?X]).
    repeat match goal with H : (_ || _) = true |- _ => apply Bool.orb_prop in H | H : (_ <=? _) = true |- _ => apply Z.leb_le in H end.
    all: repeat match goal with H : (_ <=? _) = true \/ _ |- _ => destruct H as [H|H] | H : (_ <=? _) = true |- _ => apply Z.leb_le in H end.
    all: lia.
  - right. destruct (zfacts q QC z HU NZ) as (F1 & F2 & F3 & F4 & F5). repeat split; lia.
Qed.

Theorem zone_NFS : ltac2:(tb__ "0|0|
S4fS55R1VA;A2S77S74S6eVrho1;S27VG;A1Vp;S70Vn;A1A4S6aR2A1A3F_;Fq;").
Proof.
  intros q QC. pose proof (inz_NFS q QC) as HF2. destruct (ZD_chk q) as (_ & Himg & Hne & _).
  assert (CALL : Forall (carve_ok rho1) (NFS q)) by (unfold NFS; apply Forall_app; split; [exact carve_NRT | exact (carve_NV q QC)]).
  apply Forall_forall. intros k Hk.
  destruct (Forall2_In_l _ _ _ (carve_obj k) HF2 (in_map _ _ _ Hk)) as (d & Hd & Hin).
  pose proof (proj1 (forallb_forall _ _) Himg d Hd) as Hi. pose proof (proj1 (forallb_forall _ _) Hne k Hk) as Hn.
  pose proof (proj1 (Forall_forall _ _) CALL k Hk) as Ck.
  destruct k as [[[base lo] hi] cs]. unfold spec_zone. unfold spec_ne in Hn. apply Z.ltb_lt in Hn. unfold carve_ok in Ck. destruct Ck as (C1 & C2 & C3 & _).
  pose proof (zone_of_inz q _ d QC Hin Hi) as ZZ. cbn [carve_obj] in ZZ. unfold carved in ZZ. rewrite obj_range_mk in ZZ by lia. cbn [fst snd] in ZZ.
  apply ZZ. lia.
Qed.

Lemma holds_geom : ltac2:(tb__ "0|0|
S77S41S42Vrho1;A1Sb5A3").
Proof.
  pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. pose proof geomF as (T1 & T2 & T3 & C1 & C2 & _ & _ & _ & ST & ST2 & _). unfold HIGH_SHADOW_END, PG in *. unfold G in *.
  assert (E151 : rw rho1 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))) by reflexivity.
  assert (E152 : rw rho1 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))) by reflexivity.
  assert (E153 : rw rho1 153%positive = Z_to_bv 64 (ag_stack_top (aa_geom A))) by reflexivity.
  assert (E154 : rw rho1 154%positive = Z_to_bv 64 (ag_stack_bottom (aa_geom A))) by reflexivity.
  unfold F_geom_fn, vBOT, vTOP, vT, vCTX. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval];
    rewrite ?E151, ?E152, ?E153, ?E154, ?u64_lit by lia; try lia.
  all: split; [lia|]; change (2 ^ 12) with 4096; exact T3.
Qed.

Lemma holds_p : ltac2:(tb__ "0|0|
S8Sa6R1Vp;Vn;A3S77S41S42Vrho1;A1S7fS41Sa7R2A1A2A3F_;Fkhi;").
Proof.
  intros khi HK. unfold cls_hyp, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in HK.
  pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. pose proof blkF_geom as (B1 & B2 & B3 & B4 & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & N2 & N3 & N4). unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  assert (E12 : rw rho1 12%positive = rw rho 12%positive) by reflexivity.
  assert (E13 : rw rho1 13%positive = rw rho 13%positive) by reflexivity.
  assert (E105 : rw rho1 105%positive = Z_to_bv 64 (N8 n)) by reflexivity.
  assert (E106 : rw rho1 106%positive = Z_to_bv 64 (N8 n / 8)) by reflexivity.
  assert (D1 : 0 <= N8 n / 8) by (apply Z.div_pos; lia). assert (D2 : N8 n / 8 <= N8 n) by (apply Z.div_le_upper_bound; lia).
  destruct khi; unfold F_pc, F_p, F_pL, vN8, vN8g; cbn [tl]; unfold HIGH_SHADOW_END, IMG_HI, LOW_SHADOW_BEG; repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval branch_taken]; unfold bv_eqb;
    rewrite ?add_val, ?sll_val, ?E12, ?E13, ?E105, ?E106, ?Hp12, ?Hn13, ?u64_lit by lia; try lia.

  all: try (rewrite Z.mod_small by lia; lia).
  all: try (rewrite Z.eqb_eq; lia).
  all: apply bv_eq; rewrite sll_val, !u64_lit by lia; change (3 mod 64) with 3; rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia; lia.
Qed.

Lemma m8_shift0 : ltac2:(tb__ "0|1|
S14S0S1eS1eS3bQ40S3dVrho1;S54A2A2S1bZ2Z20M0A2A2G0A2Z0A3").
Proof.
  pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. pose proof blkF_geom as (B1 & B2 & B3 & B4 & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & _). unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  unfold m8. rewrite U_sll2, U_add, !U_lit. cbn [eval]. change (rw rho1 12%positive) with (rw rho 12%positive). rewrite Hp12. unfold M64v.
  change ((-16) mod 18446744073709551616) with 18446744073709551600. change (3 mod 2 ^ 64) with 3.
  replace ((p + 18446744073709551600) mod 18446744073709551616) with (p - 16) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
  change (3 mod 64) with 3. rewrite (Z.mod_small ((p - 16) * 2 ^ 3)) by lia.
  rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists (2 ^ 27); reflexivity).
  destruct (proj1 (Z.mod_divide p 16 ltac:(lia)) B2) as [k Hk]. rewrite Hk. replace ((k * 16 - 16) * 2 ^ 3) with ((k - 1) * 4 * 32) by lia.
  apply Z_mod_mult.
Qed.

Lemma holds_cas : Forall (holds rho1) F_cas.
Proof.
  pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. pose proof blkF_geom as (B1 & B2 & B3 & B4 & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & _). unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  destruct Ht as (T1 & T2 & _). pose proof m8_shift0 as M8.
  assert (Q15 : 0 <= n / 2 ^ 32 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (EHW : bv_unsigned (eval rho1 vHW) = hw_of t n) by (cbn [eval vHW]; apply u64_lit; unfold hw_of; lia).
  assert (HWB : 0 <= hw_of t n < 2 ^ 31) by (unfold hw_of; lia).
  unfold F_cas, hw2. repeat apply Forall_cons; try apply Forall_nil; cbn [holds branch_taken]; unfold bv_eqb.
  - rewrite Bool.negb_true_iff, Z.eqb_neq. intros NE. apply NE. rewrite U_and2, U_sext_e, EHW, !U_lit by (cbv; congruence || discriminate).
    change (Z.of_N 32) with 32. unfold zsext, M64v. rewrite (Z.mod_small (hw_of t n)) by lia.
    destruct (Z.ltb_spec (hw_of t n) (2 ^ (32 - 1))); [|exfalso; change (2 ^ (32 - 1)) with (2 ^ 31) in *; lia].
    change (255 mod 18446744073709551616) with (Z.ones 8). rewrite Z.land_ones by lia. unfold hw_of.
    replace (2 + 256 * t + 65536 * (n / 2 ^ 32)) with (2 + (t + 256 * (n / 2 ^ 32)) * 2 ^ 8) by lia. rewrite Z_mod_plus_full. reflexivity.
  - rewrite EHW, U_lit. unfold M64v. change ((2 ^ 32) mod 18446744073709551616) with (2 ^ 32). lia.
  - rewrite Z.eqb_eq, U_sllw, M8, !U_lit. reflexivity.
  - rewrite Z.eqb_eq, U_sllw, M8, !U_lit. reflexivity.
  - rewrite Z.eqb_eq, U_sllw, M8, !U_lit. reflexivity.
Qed.

Lemma holds_V : ltac2:(tb__ "0|0|
S4fS55R1VA;A2S77S41S42Vrho1;A1S52R2A1A3F_;Fq;").
Proof.
  intros q QC. pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. pose proof geomF as (_ & _ & _ & _ & _ & S1 & S2 & S3 & _). rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  assert (HQ : aa_q_thread A <> [] -> rw rho1 122%positive = Z_to_bv 64 (qb_addr (lastq A)) /\ qb_addr (lastq A) mod 8 = 0
             /\ 0 < Z.of_nat (length (aa_q_thread A)) <= 128 /\ Z.of_nat (length (qb_items (lastq A))) <= kQuarantineBatchCount
             /\ 0 <= qb_addr (lastq A) < 2 ^ 64).
  { intros HNE. pose proof qF as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & QS & QLB & QL).
    destruct (QL HNE) as (_ & _ & _ & _ & _ & BK & _ & B16a & BS1 & BS2 & _). clear QL. unfold kQuarantineCacheMax in QS.
    split; [exact (E_vQB HNE)|]. unfold lastq. split; [rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2; reflexivity); rewrite B16a; reflexivity|].
    split; [|split; [exact BK | rewrite kSpaceSize_val in BS2; unfold kQuarantineBatchSize in BS2; unfold G in *; clear -BS1 BS2 S1 S2 ACV2; lia]]. destruct (aa_q_thread A); [congruence|]. cbn [length] in *. lia. }
  assert (HC : aa_cache_inited A = true -> cache24 A <> [] -> 1 <= cnt24 A <= 2).
  { intros HCI HNC. pose proof (cF HCI HNC) as CF. cbn zeta in CF. destruct CF as (_ & _ & _ & _ & CN & _). exact CN. }
  assert (E120 : rw rho1 120%positive = Z_to_bv 64 (Z.of_nat (length (aa_q_thread A)))) by reflexivity.
  assert (E126 : rw rho1 126%positive = Z_to_bv 64 (Z.of_nat (length (qb_items (lastq A))))) by reflexivity.
  assert (E127 : rw rho1 127%positive = Z_to_bv 64 (cnt24 A)) by reflexivity.
  assert (E155 : rw rho1 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A))) by reflexivity.
  unfold G, kQuarantineBatchCount in *.
  assert (HFQB : aa_cache_inited A = true -> cache24 A <> [] -> Forall (holds rho1) F_QB).
  { intros HCI HNC. destruct (HC HCI HNC) as [CN1 CN2].
    unfold F_QB, vPK, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states.vSB. unfold HIGH_SHADOW_END. rewrite kSpaceSize_val.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E127, ?E155, ?u64_lit by lia; try lia.
    all: split; [lia | exact S3]. }
  destruct q; cbn [qcond] in QC; unfold VFACT.
  - destruct QC as [HNE HK]. destruct (HQ HNE) as (E122 & A8 & LN & BK & QB64). unfold kQuarantineBatchCount in HK.
    unfold vQN, vK. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval branch_taken]; unfold bv_eqb; rewrite ?E120, ?E122, ?E126, ?u64_lit by lia; try lia.
    all: try (rewrite Z.eqb_eq; lia).
    all: split; [lia | exact A8].
  - destruct QC as (HE & HCI & HNC). exact (HFQB HCI HNC).
  - destruct QC as (HNE & HK & HCI & HNC). destruct (HQ HNE) as (E122 & A8 & LN & BK & QB64). unfold kQuarantineBatchCount in HK. apply Forall_app. split; [exact (HFQB HCI HNC)|].
    unfold vQN. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval branch_taken]; unfold bv_eqb; rewrite ?E120, ?E122, ?u64_lit by lia; try lia.
    all: try (rewrite Z.eqb_eq; lia).
    all: split; [lia | exact A8].
Qed.

Lemma rig_F : ltac2:(tb__ "0|0|
S43Sb4SabR1Vrho1;A3Sb6R2Vrho1;A2F_;Frho';").
Proof.
  intros rho' Hag. pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. pose proof blkF_geom as (B1 & B2 & B3 & B4 & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & N2 & N3 & N4).
  unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. destruct Ht as (T1 & T2 & _).
  assert (Q15 : 0 <= n / 2 ^ 32 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (U12 : bv_unsigned (rw rho1 12%positive) = p) by exact Hp12.
  assert (U13 : bv_unsigned (rw rho1 13%positive) = n) by exact Hn13.
  assert (U103 : bv_unsigned (rw rho1 103%positive) = n mod 2 ^ 32) by (apply u64_lit; pose proof (Z.mod_pos_bound n (2 ^ 32)); lia).
  assert (U104 : bv_unsigned (rw rho1 104%positive) = hw_of t n) by (apply u64_lit; unfold hw_of; lia).
  assert (U105 : bv_unsigned (rw rho1 105%positive) = N8 n) by (apply u64_lit; lia).
  assert (U106 : bv_unsigned (rw rho1 106%positive) = N8 n / 8) by (apply u64_lit; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (U107 : bv_unsigned (rw rho1 107%positive) = hw_of t n + 1) by (apply u64_lit; unfold hw_of; lia).
  constructor; rewrite ?U12, ?U13, ?U103, ?U104, ?U105, ?U106, ?U107; unfold aceilF; try lia.
  all: try exact Hag.
  all: try (exists t; unfold hw_of; repeat split; lia).
  all: unfold N8; first [reflexivity | lia].
Qed.

Theorem instF_here : ltac2:(tb__ "0|0|
S8S6SacA1SadS4fSa6R4Vp;Vn;A3S55R2VA;A2S6dR6R5R4R3Vrho1;Vp;Vn;S70Vn;A1S27VG;A1A9F_;F_;Fq;Fst;FW;Fkhi;").
Proof.
  intros khi W st q HK QC. pose proof (topG_range G) as ACV. pose proof (topG_range (aa_geom A)) as ACV2. pose proof blkF_geom as (B1 & B2 & B3 & B4 & _ & _ & BN & _ & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & N2 & N3 & N4).
  pose proof blkF_mem as (t' & _ & _ & _ & _ & HSH & HPAD). unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  constructor.
  - change (rw rho1 12%positive) with (rw rho 12%positive). rewrite <- Hp12. symmetry. apply Z_to_bv_bv_unsigned.
  - change (rw rho1 13%positive) with (rw rho 13%positive). rewrite <- Hn13. symmetry. apply Z_to_bv_bv_unsigned.
  - reflexivity.
  - reflexivity.
  - split; [unfold blk_geo, IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact B1|]. repeat split; lia.
  - unfold NFS. apply Forall_app. split; [exact carve_NRT | exact (carve_NV q QC)].
  - exact (zone_NFS q QC).
  - exact (pd_NFS q QC).
  - intros z Hz. destruct (HSH z Hz) as [x Hx]. exists x. change (rm rho1) with (rm rho). unfold m in Hx. rewrite view_in in Hx; [exact Hx|].
    unfold Sh, SHADOW_OFF in *. split; [lia|]. pose proof (Z.div_lt_upper_bound (p + N8 n) 8 (2 ^ 50) ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono p (p + N8 n) 8 ltac:(lia) ltac:(lia)).
    assert (N8 n / 8 <= (p + N8 n) / 8) by (apply Z.div_le_mono; lia). lia.
  - intros z Hz. destruct (HPAD z Hz) as [x Hx]. exists x. change (rm rho1) with (rm rho). unfold m in Hx. rewrite view_in in Hx; [exact Hx | lia].
  - apply Forall_app. split; [exact holds_geom|]. apply Forall_app. split; [exact (holds_p khi HK)|]. apply Forall_app. split; [exact holds_cas | exact (holds_V q QC)].
  - exact rig_F.
Qed.
End CARVE.

End FACTS.

Theorem instF_facts_ok : ltac2:(tb__ "0|1|
S8S6SacA1SadS4fS30S43S6S3aQ40M0A1A1Sb3S0S0VAInv;R6R5R4R3A4S7aS5S0S0A2S2S0S0R3R2A4S31R7A1A3Sa6RcR4R3A3S14S8S35R9A1S9A3S55RbRaA2S14S0S3bG0S40RaPcA2A2R7A3S14S0S3bG0S40RbPdA2A2R7A3S17S0S0S17S5dS5dS6dR13R12R11R10S65RfReRbRaR2R1A6RbRaS70RaA1S27S2aRfA1A1A9Ljv;A2Lt;A2F_;F_;F_;F_;F_;F_;F_;Fn;Fp;Fmd;Ftp;Frho;FA;Fq;Fst;FW;Fkhi;").
Proof.
  intros khi W st q A rho tp md p n HA HL HK Hii QC Hp Hn. pose proof (cls_hyp_blk khi p n HK) as HCL.
  destruct (blkF_mem A rho tp md p n HA HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok A rho tp md HA) as [jv Hjv].
  exists t, jv. exact (instF_here A rho tp md p n HA HL HCL Hii Hp Hn t (conj T1 (conj T2 (conj T3 T4))) jv Hjv khi W st q HK QC).
Qed.
End INSTOK.
