(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "False"; "ex"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "mul"; "pow"; "modulo"; "of_nat"; "div"; "eqb"; "shiftr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "qb_addr"; "sec_chunk"; "class_state"; "aa_q_thread"; "sc_map_beg"; "ageom"; "cs_cache"; "cs_empty"; "aa_cls"; "aa_geom"; "aa_live"; "qb_items"; "sc_map_size"; "topG"; "cs_allocated_user"; "cs_free_array"; "qb_size"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_sec"; "cs_mapped_user"; "AA"; "aa_frames"; "ag_thread"; "ag_ctx"; "ag_dtls"; "ag_pab"; "cs_mapped_free_array"; "mkQB"; "aa_cache_inited"; "aa_depot"; "aa_internal_inited"; "aa_q_global"; "ag_fsb"; "ag_spacebeg"; "cls_kept_freeA"; "sc_size"; "aa_fs_busy"; "aa_fs_hint"; "aa_ptr_committed"; "list_upd"; "mkAA"; "@Corelib.Init.Datatypes"; "app"; "list"; "bool"; "prod"; "nil"; "true"; "cons"; "pair"; "nat"; "length"; "option"; "false"; "Some"; "snd"; "fst"; "None"; "andb"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "bview"; "in_rangesZ"; "view"; "maskv"; "present"; "cst_ok"; "restrictv"; "xgl_ok"; "rtc_inv"; "@Stdlib.Lists.List"; "In"; "last"; "nth_error"; "removelast"; "hd"; "fold_right"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "qvar"; "QA"; "QBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "chg_f"; "Pc"; "idf"; "LI"; "QI"; "freeQ"; "IMG_F"; "AInvB"; "rt_zoneF"; "freeA"; "nb_addr"; "qrepr_B"; "freeCls"; "free_rebuild_stmt"; "free_rebuild_stmtB"; "leaf_cells"; "rest_B"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qall"; "qitems"; "qb_id"; "it_id"; "q_ids"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "enc_bytes"; "@Corelib.Lists.ListDef"; "map"; "nth"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild.RB"; "csA"; "CZ"; "mapzone"; "nbQ"; "kA"; "chg_common"; "lbQ"; "pc24"; "BZ"; "NZ"; "TZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "rz"; "Size"; "is_primary"; "Sh"; "kQuarantineBatchSize"; "region_beg"; "IMG_HI"; "ClassID"; "needed"; "kPtrArrayReserve"; "IMG_LO"; "kQuarantineCacheMax"; "max_count"; "FS_total"; "kQuarantineBatchCount"; "round_up"; "kQuarantineMax"; "kQuarantineMin"; "ptr_to_compact"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "nthZ"; "qsize"; "qb_dflt"; "live_ids"; "fs_footb"; "qlinks"; "batch_repr"; "IA_BEG"; "IA_END"; "QG"; "fs_inv"; "q_item_ok"; "model_inv"; "present_but"; "qhdr_repr"; "slot_zone"; "AInvA"; "bandtp_inv"; "class_repr"; "depot_wf"; "geom_ok"; "ia_inv"; "inv3"; "live_block_repr"; "live_sep"; "misc_inv"; "primary_repr"; "secondary_repr"; "thread_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@stdpp.base"; "NoDup"; "filter"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "czone"; "pop_cls"; "cz_env";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "lastq"; "top24"; "cache24"; "cnt24"; "qcond"; "@Corelib.Init.Peano"; "lt"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "mem_keptA"; "client_addrA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "blk_geo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild.STMT"; "leaf_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM"; "rt_zone"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require SymSoundM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells SegQ_defs Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition nb_addr (A : AA) : Z := ltac2:(tb__ "0|0|
S9S92S37S1dVA;A1A1Z18A2ScZ10Sc8VA;A1A2A2").

Definition freeQ (q : qvar) (A : AA) (p n : Z) : list qbatch := ltac2:(tb__ "0|5|
S63S40S13A1Lq;Vq;S5dS13S17VA;A1M0Sa3A3S13S3fS13S5fS13G0A2S45S13S31S14R1A1S3fS42S0S0A2M1S1fR1A1S45G1S46S0S0Vp;Vn;A4S43G1A1A3M2A3S9S24R1A1Vn;A2A3S43S13A1M3A3A3Tb;S45S13S31S70VA;A1G2S9S91Vn;A2A3G3A3M4S3fS13G0G4A3X63x3").

Definition freeCls (q : qvar) (A : AA) : list class_state := ltac2:(tb__ "0|2|
S63S40S16A1Lq;Vq;S1cVA;A1M0S3dS16G0U18Sc5Sa1S16G0Z18S1bA4A1A4M1G1X63x3").

Definition freeA (q : qvar) (A : AA) (l1 l2 : list (Z * Z)) (p n : Z) : AA := ltac2:(tb__ "0|0|
S3eS1dVA;A1S72Vq;VA;A2S32VA;A1S28VA;A1S3cVA;A1S3fS42S0S0A2Vl1;Vl2;A3S6bVq;VA;Vp;Vn;A4S35VA;A1S33VA;A1S3bVA;A1S3aVA;A1S34VA;A1S27VA;A1S26VA;A1S25VA;A1Af").

Definition chg_f (q : qvar) (A : AA) (p n : Z) (z : Z) : Prop := ltac2:(tb__ "0|13|
S1dVA;A1S19S2cR1A1S0S4S1S8SbVp;Z10M0A2Vz;A2SaVz;SbVp;Z8M1A2A2A2S4S1S8Vp;Vz;A2SaVz;S9Vp;SbeVn;A1M2A2A2A2S4S1S8S90Vp;A1M3Vz;A2SaVz;S9G3S10G2G1A2A2A2A2S4S1S8S9R1Z50M4A2Vz;A2SaVz;S9R1Z70A2A2A2S4S1S8S9R1Zad0A2Vz;A2SaVz;S9R1Zc60A2A2A2S63OLq;Vq;S5dS13S17VA;A1Sa3A3M5S13SfS48S42S0S0A2S1fR1A1A2A1S0S4S1S8S14R2A1M6Vz;A2SaVz;S9G6Z18M7A2M8A2A2S1S8S9G8ScG1R1A2M9A2Vz;A2SaVz;S9S9G6Z20A2G9A2A2A2A2Tk;Tb;S4S1S8S9S9R1Zd0A2ScG4G7A2A2MaVz;A2SaVz;S9GaG0A2MbA2A2McS4S1S8S9GbScZ4MdSbScaVA;A1MeZ1A2A2A2Vz;A2SaVz;S9GbScGdGeA2A2A2A2MfS1S8S70VA;A1M10Vz;A2SaVz;S9G10Z2000A2A2A2M11A2A2S4GcS4GfS4G11G5S13S1S8S14R1A1M12Vz;A2SaVz;S9G12G7A2A2A2Tb;A2A2A2X63x3A2A2A2A2A2TT;TG;").

Definition IMG_F : list (Z * Z) := RebuildM.lit_ranges OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst.NRT.
Definition rt_zoneF (G : ageom) (a : Z) : Prop := ltac2:(tb__ "0|0|
S4Sd7VG;Va;A2S4S54S6cVa;A2S1S8Sa8Va;A2SaVa;Sa9A2A2A2A2").
Lemma IMG_F_lt : ltac2:(tb__ "0|0|
S0S54S6cR1A2S1S8S97R2A2SaR2S93A2A2F_;Fa;").
Proof.
  intros a (lo & len & Hr & Ha). unfold IMG_F in Hr.
  assert (OK : forallb (fun r => (IMG_LO <=? fst r) && (fst r + snd r <=? IMG_HI)) (RebuildM.lit_ranges OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst.NRT) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (proj1 (forallb_forall _ _) OK (lo, len) Hr) as X. cbn beta in X. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2.
  cbn [fst snd] in *. lia.
Qed.

Definition qrepr_B (B : Z) (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|3|
S1S81S13Sa7Vm;VA;A2S3fS13S17VA;A1M0S35VA;A1M1A3M2A3S1Sa6Vm;G0A2S1Sa6Vm;G1A2S1SafVm;S9S2cS1dVA;A1A1Z50A2G0A3S1SafVm;S9SaaZa0A2G1A3S1S51Vm;S52S9SaaZ98A2U4Z0A3A2S1S51Vm;S52S9SaaZ48A2U8S9eA3A2S1S8Sa2G0A1VB;A2S1S8Sa2G1A1S9dA2SbfS0S7fS13S0S14G2A4A2A2A2A2A2A2A2A2A2A2").
Definition rest_B (B : Z) (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|0|
S1Sb9VA;A1S1Sb8Vm;VA;A2S1SbbVm;VA;A2S1SbcVm;VA;A2S1S71VB;Vm;VA;A3S1Sb4Vm;VA;A2S1Sb6Vm;VA;A2S1SbdVm;S1dVA;A1A2SbaVm;A1A2A2A2A2A2A2A2A2").
Definition AInvB (B : Z) (A : AA) (rho : valuation) (tp : list word) (md : Model) : Prop := ltac2:(tb__ "0|1|
S55Sd1S7cVrho;A1A2S53S1dVA;A1S19S1Sb5R1A1S1S5bR2R1A2S1SabS59Sa5R1A1M0R2A2VA;A2S1S76VB;S56G0R2A2VA;A3S1SadSd1VA;Vtp;Vmd;A4S1Sb7VA;A1Sb2R2Vtp;A2A2A2A2A2A2A2TG;Tm;").
Lemma AInvB_std : ltac2:(tb__ "0|0|
S2aS7dS40Sc2Q40A1A1Sd0S2OS6dS98R4R3R2R1A5Sb1Sd1R4R3R2R1A5A3Fmd;Ftp;Frho;FA;"). Proof. reflexivity. Qed.

Section STMT.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition leaf_cells (q : qvar) (A : AA) (p n : Z) (v3 : bview) : Prop := ltac2:(tb__ "0|1d|
S1dVA;A1S19S2cR1A1S0S17VA;A1S40S13A1S63OLq;Vq;S5dS13R1Sa3A3S13SfS48S42S0S0A2S1fR1A1A2A1M0S0S1S51Vv3;S52S9R4Z50M1A2M2U8M3SfS48S13R3A2A1M4A3A2S1S51Vv3;S52S9G2Z8M5A2G3S14S60S13Sa3R3A3A1A3A2M6S1S51Vv3;S52S9G2Z10M7A2M8G3S14R2A1M9A3A2S1S51Vv3;S52S9G2Z18MaA2MbG3S9Sa2R3A1McVn;A2A3A2S1S51Vv3;S52S9G9G5A2G3S9S24R2A1Vn;A2A3A2S1S51Vv3;S52S9G9G7A2G3S9R1Z1MdA2A3A2S1S51Vv3;S52S9S9G9GaA2ScG5R1A2A2G3SbVp;G7A2MeA3A2S51Vv3;S52G9G3Z0MfA3A2A2A2A2A2A2A2A2Tk;Tb;S70VA;A1M10S0S1S51Vv3;S52S9R3G1A2M11G3GdA3A2S1S51Vv3;S52S9G11G5A2G3R1A3A2S1S51Vv3;S52S9G11G7A2G3R1A3A2S1S51Vv3;S52S9G11GaA2G3S9Sa2R2A1S9Vn;S91A2M12A2A3A2S1S51Vv3;S52S9S9R3Zd0M13A2ScG1GaA2M14A2M15U4M16SbSfS48S0Sc9VA;A1A2A1GdA2M17A3A2S1S51Vv3;S52R1G3GfA3A2S1S51Vv3;S52S9R1G5A2G3G12A3A2S1S51Vv3;S52S9R1G7A2G3GdA3A2S1S51Vv3;S52S9R1GaA2G3GeA3A2S1S51Vv3;S52S9G15Z4M18A2G16S99GaA1M19A3A2S51Vv3;S52S9G15G5A2G3S8eGaA1M1aA3A2A2A2A2A2A2A2A2A2A2A2Tnb;G10S0S5dS13R2Sa3A3S13S1S51Vv3;S52G2G3S9G4GdA2A3A2S1G6S1S51Vv3;S52G8G3R2A3A2S1S51Vv3;S52GbG3S9GcG12A2A3A2S1S51Vv3;S52S14R1A1M1bG3R2A3A2S1S51Vv3;S52S9S9R4G13A2G14A2M1cG16G17A3A2S1S51Vv3;S52R2G3GfA3A2S1S51Vv3;S52S9R2G5A2G3G12A3A2S1S51Vv3;S52S9R2G7A2G3GdA3A2S1S51Vv3;S52S9R2GaA2G3GeA3A2S1S51Vv3;S52S9G1cG18A2G16G19A3A2S1S51Vv3;S52S9G1cG5A2G3G1aA3A2S1S51Vv3;S52S9G1bG5A2G3S24R1A1A3A2S51Vv3;S52S9G1bG7A2G3G0A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2Tb;Tnb;X63x3Tl;TT;TG;").

Definition free_rebuild_stmt (CST XGL : list (Z * Z)) : Prop := ltac2:(tb__ "0|d|
S63S2aS7dS7dS40Sc2Q40M0A1A1Sd0S0S0S40S42S0S0A2M1A1M2G2S0VAInv;RaR9R7R6A4S2G2S1eRbA1S3fG1R4S45G1S46S0S0R6R5A4R3A3A3A3Sd2R7R6A2S2S41S34RdA1S44A3ScbRfReA2S1dRfA1S19S2cR1A1S0S55Vsegs;S7cRfA1A2S53S55Vsegs;S7cR11A1A2S53S1S8Z0M3RaA2SaRaZ100M4A2A2S2S0SeRbZ4A2Z1A3S51R4S52SbR10Z10A2U4M5S9S9Z3ScG4RcA2A2ScZ10000S10RfSdZ2M6Z20A2M7A2A2A2A3A2S51R5S52SbR11ZcA2G5SeR10G7A2A3A2S0S66R19R18R13R12R1A5S6Sc2Q8A1M8G8S2S49G8A1M9R9R3A1S4bG8R1A2A3Lb;A2F_;Fz;Sd4R19R18R13R12R7A5S0S3S66R1bR1aR15R14R1A5A1S2G9RaR2A1R9R2A1A3F_;Fz;S0S1S8G3R1A2SaR1SdG6Z40A2A2MaA2S3S66R1dR1cR17R16R2A5A1S3S6eReR3A2A1S2G9S7cR1cSc1G0R4A2MbA2S7cR1dGbA2A3F_;F_;F_;Fa;S0S1S8S93R1A2GaA2S3S2G9S7cR1cSc1G0R2A2A2S4eG8A1McA3A1S3S2G9S7cR1cSc1G0R3A2A2GcA3A1F_;F_;Fa;S8Sa2S6bR1dR1cR17R16A4A1S98A2S6fR1eR1dR16R15R18R17A6S2aS1VAInv;R1R1cR1bR1aA4S1S2G2S1eR1A1S3fG1R17R16A3A3S1S2G2S2bR1A1S2bR1eA1A3S1S2S0S27R1A1S27R1eA1A3S1S2S0S26R1A1S26R1eA1A3S1S2S0S25R1A1S25R1eA1A3S1S2S19S1dR1A1S1dR1eA1A3S1SceVCST;VXGL;R1eR1S7cR1dA1S7cR1cA1A6S38R1eR1A2A2A2A2A2A2A2A2A2TA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TvE;Tv3;TT;TG;F_;F_;F_;F_;F_;Ft;Fl2;Fl1;Fn;Fp;Fmd;Ftp;Frho3;FrhoE;FA;Fq;").

Definition free_rebuild_stmtB (CST XGL : list (Z * Z)) : Prop := ltac2:(tb__ "0|d|
S0S63S2aS7dS7dS40Sc2Q40M0A1A1Sd0S0S0S40S42S0S0A2M1A1M2G2S0VAInv;RaR9R7R6A4S2G2S1eRbA1S3fG1R4S45G1S46S0S0R6R5A4R3A3A3A3Sd2R7R6A2S2S41S34RdA1S44A3ScbRfReA2S1dRfA1S19S2cR1A1S0S55Vsegs;S7cRfA1A2S53S55Vsegs;S7cR11A1A2S53S1S8Z0M3RaA2SaRaZ100M4A2A2S2S0SeRbZ4A2Z1A3S51R4S52SbR10Z10A2U4M5S9S9Z3ScG4RcA2A2ScZ10000S10RfSdZ2M6Z20A2M7A2A2A2A3A2S51R5S52SbR11ZcA2G5SeR10G7A2A3A2S0S66R19R18R13R12R1A5S6Sc2Q8A1M8G8S2S49G8A1M9R9R3A1S4bG8R1A2A3Lb;A2F_;Fz;Sd4R19R18R13R12R7A5S0S3S66R1bR1aR15R14R1A5A1S2G9RaR2A1R9R2A1A3F_;Fz;S0S1S8G3R1A2SaR1SdG6Z40A2A2MaA2S3S66R1dR1cR17R16R2A5A1S3S6eReR3A2A1S2G9S7cR1cSc1G0R4A2MbA2S7cR1dGbA2A3F_;F_;F_;Fa;S0S1S8S93R1A2GaA2S3S2G9S7cR1cSc1G0R2A2A2S4eG8A1McA3A1S3S2G9S7cR1cSc1G0R3A2A2GcA3A1F_;F_;Fa;S8Sa2S6bR1dR1cR17R16A4A1R1eA2S6fR1eR1dR16R15R18R17A6S2aS1S6dR20R1R1cR1bR1aA5S1S2G2S1eR1A1S3fG1R17R16A3A3S1S2G2S2bR1A1S2bR1eA1A3S1S2S0S27R1A1S27R1eA1A3S1S2S0S26R1A1S26R1eA1A3S1S2S0S25R1A1S25R1eA1A3S1S2S19S1dR1A1S1dR1eA1A3S1SceVCST;VXGL;R1eR1S7cR1dA1S7cR1cA1A6S38R1eR1A2A2A2A2A2A2A2A2A2TA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TvE;Tv3;TT;TG;F_;F_;F_;F_;F_;Ft;Fl2;Fl1;Fn;Fp;Fmd;Ftp;Frho3;FrhoE;FA;Fq;FQB;").
End STMT.

Lemma qsize_app : ltac2:(tb__ "0|1|
S40S13A1M0G0S2S0Sa2S3fS13R2R1A3A1S9Sa2R2A1Sa2R1A1A2A3Fl2;Fl1;").
Proof. intros l1 l2. unfold qsize. induction l1 as [|b r IH]; cbn; [reflexivity | rewrite IH; lia]. Qed.
Lemma qsize_removelast_last : ltac2:(tb__ "0|1|
S40S13A1M0S3S2G0R1S43S13A1A3A1S2S0Sa2R2A1S9Sa2S5fS13R2A2A1S24S5dS13R2Sa3A3A1A2A3F_;Fl;").
Proof.
  intros l Hl. rewrite (removelast_split l qb_dflt) at 1 by (destruct l; [congruence | cbn; lia]).
  rewrite qsize_app. rewrite <- last_nth. unfold qsize at 2. cbn. lia.
Qed.
Lemma last_app1 : forall {T} (l : list T) (x d : T), last (l ++ [x]) d = x.
Proof. intros T l x d. rewrite last_last. reflexivity. Qed.
Lemma In_removelast_last : ltac2:(tb__ "0|0|
S40S13A1S13S5cS13R1R2A3S4S5cS13R2S5fS13R3A2A3S2S13R2S5dS13R3Sa3A3A3A2F_;Fx;Fl;").
Proof.
  intros l x Hx. destruct l as [|b r] eqn:El; [destruct Hx|]. rewrite <- El in Hx |- *.
  assert (NE : (0 < length l)%nat) by (subst l; cbn; lia).
  rewrite (removelast_split l qb_dflt NE) in Hx. apply in_app_or in Hx as [Hx|[Hx|[]]]; [left; exact Hx | right]. rewrite last_nth. symmetry. exact Hx.
Qed.

Definition Pc (c : Z) (bn : Z * Z) : bool := ltac2:(tb__ "0|1|
S4fS8fS4cS0S0Vbn;A3M0A1S11S94S95G0A1A1Vc;A2A2").
Definition idf (G : ageom) (c : Z) (bn : Z * Z) : Z := ltac2:(tb__ "0|0|
S10SbSbS4dS0S0Vbn;A3S8dS4cS0S0Vbn;A3A1A2S92S37VG;A1Vc;A2A2Z10A2").
Definition LI (G : ageom) (c : Z) (l : list (Z * Z)) : list Z := ltac2:(tb__ "0|2|
S7fS42S0S0A2M0S0S68VG;Vc;A2Sc0G0S40G0A1SdaG0A1G0Sd8S67Vc;R1A2M1A1Lbn;G0Sd9G1A1Lx;Vl;A6A4").
Lemma live_ids_LI : ltac2:(tb__ "0|0|
S19S2aS0S2S40S0A1Sa4R3R2R1A3S69R3R1S1eR2A1A3A3Fc;FA;FG;").
Proof. intros. reflexivity. Qed.
Lemma LI_app : ltac2:(tb__ "0|2|
S19S0S40S42S0S0A2M0A1M1G1S2S40S0A1S69R4R3S3fG0R2R1A3A3S3fS0S69R4R3R2A3S69R4R3R1A3A3A3Fl2;Fl1;Fc;FG;").
Proof. intros. unfold LI. rewrite list_basics.list.filter_app, map_app. reflexivity. Qed.
Lemma LI_cons : ltac2:(tb__ "0|3|
S19S0S42S0S0A2M0S40G0A1S2S40S0A1M1S69R4R3S45G0R2R1A3A3S3fS0S41G1L_;S67R3R2A2S45S0S68R4R3R2A3S43S0A1M2A3G2X41x2S69R4R3R1A3A3A3Fl;Fb;Fc;FG;").
Proof. intros. unfold LI. cbn [filter list_basics.list.list_filter decide Is_true_dec]. destruct (Pc c b); reflexivity. Qed.
Lemma LI_in : ltac2:(tb__ "0|1|
S19S0S42S0S0A2M0S40G0A1S5cG0R2R1A3S2S41S67R4R3A2S44A3S5cS0S68R6R5R4A3S69R6R5R3A3A3F_;F_;Fl;Fb;Fc;FG;").
Proof.
  intros G c b l Hin Hb. unfold LI. apply in_map_iff. exists b. split; [reflexivity|].
  apply (proj1 (list_elem_of_In _ _)). apply (proj2 (list_basics.list.list_elem_of_filter _ _ _)). split; [rewrite Hb; exact I|]. apply list_elem_of_In. exact Hin.
Qed.
Lemma qitems_app : ltac2:(tb__ "0|2|
S40S13A1M0G0S2S40S42S0S0A2M1A1S78S3fS13R2R1A3A1S3fG1S78R2A1S78R1A1A3A3Fl2;Fl1;").
Proof. intros. unfold qitems. rewrite flat_map_app. reflexivity. Qed.

Definition QI (G : ageom) (c : Z) (l : list (Z * Z)) : list Z := ltac2:(tb__ "0|1|
S7fS42S0S0A2M0S0S7aVG;A1S62G0G0S67Vc;R1A2Lit;Vl;A3A4").
Lemma QI_app : ltac2:(tb__ "0|2|
S19S0S40S42S0S0A2M0A1M1G1S2S40S0A1S6aR4R3S3fG0R2R1A3A3S3fS0S6aR4R3R2A3S6aR4R3R1A3A3A3Fl2;Fl1;Fc;FG;").
Proof. intros. unfold QI. rewrite List.filter_app, map_app. reflexivity. Qed.
Lemma QI_cons : ltac2:(tb__ "0|3|
S19S0S42S0S0A2M0S40G0A1S2S40S0A1M1S6aR4R3S45G0R2R1A3A3S3fS0S41G1L_;S67R3R2A2S45S0S7aR4R2A2S43S0A1M2A3G2X41x2S6aR4R3R1A3A3A3Fl;Fb;Fc;FG;").
Proof. intros. unfold QI. cbn [List.filter]. destruct (Pc c b); reflexivity. Qed.
Lemma QI_nil : ltac2:(tb__ "0|0|
S19S0S2S40S0A1S6aR2R1S43S42S0S0A2A1A3S43S0A1A3Fc;FG;"). Proof. reflexivity. Qed.
Lemma q_ids_QI : ltac2:(tb__ "0|1|
S19S40S13A1S0S2S40S0A1M0S7bR3R2R1A3S3fS0S6aR3R1S78R2A1A3S41G0L_;S11R1Z18A2S7fS13S0S79R3A1R2A4S43S0A1X41x2A3A3Fc;Fl;FG;").
Proof. intros. unfold q_ids, QI, Pc, it_cls. reflexivity. Qed.
Lemma QI_in : ltac2:(tb__ "0|1|
S19S0S42S0S0A2M0S40G0A1S5cG0R2R1A3S2S41S67R4R3A2S44A3S5cS0S7aR6R4A2S6aR6R5R3A3A3F_;F_;Fl;Fit;Fc;FG;").
Proof.
  intros G c it l Hin Hb. unfold QI. apply in_map_iff. exists it. split; [reflexivity|]. apply List.filter_In. split; [exact Hin | exact Hb].
Qed.

Lemma it_id_idf : ltac2:(tb__ "0|0|
S19S0S42S0S0A2S2S41S67R2R1A2S44A3S2S0S7aR4R2A2S12SbSbS4dS0S0R2A3S8dS4cS0S0R2A3A1A2S92S37R4A1R3A2A2Z4A2A3F_;Fit;Fc;FG;").
Proof.
  intros G c it Hb. unfold it_id, ptr_to_compact, it_ab, it_cls, kCompactPtrScale. unfold Pc in Hb. apply andb_prop in Hb as [_ Hb]. apply Z.eqb_eq in Hb. rewrite Hb. reflexivity.
Qed.

Lemma ND_app_l : ltac2:(tb__ "0|1|
S40S0A1M0G0SbfS0S3fS0R2R1A3A2SbfS0R3A2F_;Fk;Fl;").
Proof. intros l k H. apply (proj1 (list_relations.list.NoDup_app _ _)) in H as (H & _). exact H. Qed.
Lemma ND_app_r : ltac2:(tb__ "0|1|
S40S0A1M0G0SbfS0S3fS0R2R1A3A2SbfS0R2A2F_;Fk;Fl;").
Proof. intros l k H. apply (proj1 (list_relations.list.NoDup_app _ _)) in H as (_ & _ & H). exact H. Qed.
Lemma ND_app_disj : ltac2:(tb__ "0|2|
S40S0A1M0G0S0S0SbfS0S3fS0R4R3A3A2S5cS0R3R5A3M1G1S3S2S0R5R4A3A1F_;F_;F_;Fy;Fx;Fk;Fl;").
Proof.
  intros l k x y ND Hx Hy ->. apply (proj1 (list_relations.list.NoDup_app _ _)) in ND as (_ & HD & _).
  apply (HD y); apply (proj2 (list_elem_of_In _ _)); assumption.
Qed.
Lemma ND_mid : ltac2:(tb__ "0|1|
S40S0A1M0G0S0S0SbfS0S3fS0R4S45S0R2R3A3A3A2S5cS0R2S3fS0R5R4A3A3S3S2S0R3R4A3A1F_;F_;Fy;Fx;Fk;Fl;").
Proof.
  intros l k x y ND Hy E. subst y. apply (proj1 (list_relations.list.NoDup_app _ _)) in ND as (_ & HD & ND2).
  apply in_app_or in Hy as [Hy|Hy].
  - apply (HD x); [apply (proj2 (list_elem_of_In _ _)); exact Hy | left].
  - apply (proj1 (list_relations.list.NoDup_cons _ _)) in ND2 as [NI _]. apply NI. apply (proj2 (list_elem_of_In _ _)). exact Hy.
Qed.
Lemma ND_perm : ltac2:(tb__ "0|1|
S40S0A1M0G0Sc3S0R2R1A3SbfS0R2A2SbfS0R4A2F_;F_;Fk;Fl;").
Proof.
  intros l k HP ND. apply (proj2 (NoDup_ListNoDup _)). apply (Permutation_NoDup (Permutation_sym HP)). apply (proj1 (NoDup_ListNoDup _)). exact ND.
Qed.

Section RB.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S54VCST;R1A2S4S54S6cR2A2S1S8Sa8R2A2SaR2Sa9A2A2A2S5F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Variables (q : qvar) (A : AA) (rhoE rho3 : valuation) (tp : list word) (md : Model) (p n : Z) (l1 l2 : list (Z * Z)) (t : Z).
Hypothesis HA : ltac2:(tb__ "0|0|
VAInv;VA;VrhoE;Vtp;Vmd;A4").
Hypothesis HLV : ltac2:(tb__ "0|1|
S2S40S42S0S0A2M0A1S1eVA;A1S3fG0Vl1;S45G0S46S0S0Vp;Vn;A4Vl2;A3A3A3").
Hypothesis HCLS : blk_cls p n.
Hypothesis Hii : aa_internal_inited A = true.
Hypothesis QC : qcond q A.
Let G : ageom := aa_geom A.
Let T : Z := ag_thread G.
Let SB : Z := ag_spacebeg G.
Let v3 : bview := ltac2:(tb__ "0|0|
S55Vsegs;S7cVrho3;A1A2").
Let vE : bview := ltac2:(tb__ "0|0|
S55Vsegs;S7cVrhoE;A1A2").
Let m3 : bview := ltac2:(tb__ "0|0|
S56Sa5VG;A1Vv3;A2").
Let mE : bview := ltac2:(tb__ "0|0|
S56Sa5VG;A1VvE;A2").
Hypothesis Ht : 0 <= t < 256.
Hypothesis Ht4 : t mod 4 = 1.
Hypothesis VHW : ltac2:(tb__ "0|0|
S51Vv3;S52SbVp;Z10A2U4S9S9Z3ScZ100Vt;A2A2ScZ10000S10Vn;SdZ2Z20A2A2A2A2A3A2").
Hypothesis VHL : ltac2:(tb__ "0|0|
S51Vv3;S52SbVp;ZcA2U4SeVn;SdZ2Z20A2A2A3A2").
Hypothesis PRES : ltac2:(tb__ "0|1|
S0S66Vq;VA;Vp;Vn;R1A5S6Sc2Q8A1M0G0S2S49G0A1Vv3;R3A1S4bG0R1A2A3Lb;A2F_;Fz;").
Hypothesis LC : ltac2:(tb__ "0|0|
S75Vq;VA;Vp;Vn;Vv3;A5").
Hypothesis VO : ltac2:(tb__ "0|0|
S0S3S66Vq;VA;Vp;Vn;R1A5A1S2S49Sc2Q8A1A1Vv3;R2A1VvE;R2A1A3F_;Fz;").
Hypothesis RMO : ltac2:(tb__ "0|1|
S0S1S8Z0R1A2SaR1SdZ2Z40A2A2A2S3S66Vq;VA;Vp;Vn;R2A5A1S3S6eVG;R3A2A1S2S49Sc2Q8A1A1S7cVrho3;Sc1Q40R4A2M0A2S7cVrhoE;G0A2A3F_;F_;F_;Fa;").
Hypothesis DEFM : ltac2:(tb__ "0|4|
S0S1S8S93R1A2SaR1SdZ2Z40A2A2A2S3S2S49Sc2Q8A1M0A1M1S7cVrhoE;Sc1Q40M2R2A2A2S4eG0A1M3A3A1S3S2G1S7cVrho3;Sc1G2R3A2A2G3A3A1F_;F_;Fa;").
Variable QBD : Z.
Hypothesis QSZ : ltac2:(tb__ "0|0|
S8Sa2S6bVq;VA;Vp;Vn;A4A1VQBD;A2").
Let A' : AA := ltac2:(tb__ "0|0|
S6fVq;VA;Vl1;Vl2;Vp;Vn;A6").
Let qbF : Z := qb_addr (lastq A).
Let nbF : Z := nb_addr A.

Lemma HL : ltac2:(tb__ "0|0|
S5cS42S0S0A2S46S0S0Vp;Vn;A4S1eVA;A1A3").
Proof. rewrite HLV. apply in_or_app. right. left. reflexivity. Qed.

Lemma GEO : ltac2:(tb__ "0|f|
S1S8Z1000M0VT;A2S1S8S9VT;G0A2M1S21VG;A1M2A2S1S8Z10007fff8000M3VSB;A2S1S8S9S9VSB;SdZ2M4Z25A2A2G0A2M5G2A2S1S2S0SeVSB;Z8A2Z0M6A3S1S2S0SeVSB;SdG4Z10A2A2G6A3S1S4S8G1VSB;A2S8G5VT;A2A2S1S4S8G1Z7fff7000M7A2S8G3VT;A2A2S1S4S8G1Z10000A2S8Z646000M8VT;A2A2S1S1S8Z7fff7f800000G2A2S8G2Z7fffff800000A2A2S1S8G8S36VG;A1M9A2S1S8S9G9Zb09000A2MaG2A2S1S4S8GaVT;A2S8G1G9A2A2S1S4S8GaVSB;A2S8G5G9A2A2S1S4S8GaG7A2S8G3G9A2A2S1S8G0S2dVG;A1MbA2S1S8S9GbG0A2McG2A2S1S4S8G1GbA2S8GcVT;A2A2S1S4S8GcVSB;A2S8G5GbA2A2S1S8G0S2eVG;A1MdA2S1S8S9GdG0A2MeG2A2S1S4S8G1GdA2S8GeVT;A2A2S4S8GeVSB;A2S8G5GdA2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof HA as (HG & _ & _ & _ & _ & HI3 & _).
  pose proof (geom_numsS _ HG) as (F0 & F1 & F2 & T1 & T2 & C1 & C2 & D1 & D2 & FT & FC & FD & TC & TD & CD & _ & _ & TG).
  pose proof (geom_old _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16 & S1 & S2 & _ & _ & _ & FS & _).
  pose proof (geom_bands _ HG) as (FB & TB & _ & _ & TI & _).
  destruct HI3 as ((ST & SC & SD & _) & _). fold G in ST, SC, SD. rewrite kSpaceSize_val in ST, SC, SD.
  rewrite FS_total_val, kSpaceSize_val in FS. rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in FB, TB, TI. rewrite FS_total_val in FB.
  fold G T SB in F0, F1, F2, T1, T2, C1, C2, D1, D2, FT, FC, FD, TC, TD, CD, TG, S16, S1, S2, FS, FB, TB, TI, ST, SC, SD |- *.
  assert (S8 : SB mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (2 ^ 16)); [exists (2 ^ 13); reflexivity | apply Z.mod_divide; [lia | exact S16]]. }
  split; [exact T1|]. split; [exact T2|]. split; [exact S1|]. split; [exact S2|]. split; [exact S8|]. split; [exact S16|].
  split; [exact ST|]. split; [exact TB|]. split; [exact TI|]. split; [exact TG|].
  split; [exact F1|]. split; [exact F2|]. split; [exact FT|]. split; [exact FS|]. split; [exact FB|].
  split; [exact C1|]. split; [exact C2|]. split; [exact TC|]. split; [exact SC|].
  split; [exact D1|]. split; [exact D2|]. split; [exact TD | exact SD].
Qed.

Lemma BLK : ltac2:(tb__ "0|5|
S1Sd3Vp;SbeVn;A1M0A2S1S2S0SeVp;Z10M1A2Z0M2A3S1S8Z1Vn;A2S1SaS9Vp;G0A2S21VG;A1A2S1S1S8Vn;G0A2SaG0S9Vn;Z8M3A2A2A2S1S2S0SeG0G3A2G2A3S1S8G3G0A2S1S1S8G1S8dVn;A1M4A2S8G4Z800A2A2S1S2S0SeG4G1A2G2A3S2S0SeVp;G3A2G2A3A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof (blkF_geom A rhoE tp md p n HA HL HCLS) as (B1 & B2 & B3 & B4 & _ & _ & BN & _). pose proof (N8_facts n B3) as (N1 & N2 & N3 & _).
  pose proof (rz_bound n) as RB. pose proof (rz_mod16 n) as RM.
  assert (P8 : p mod 8 = 0) by (rewrite <- (Z.mod_mod_divide p 16 8) by (exists 2; reflexivity); rewrite B2; reflexivity).
  repeat split; try assumption; try lia.
Qed.

Definition CZ (z : Z) : Prop := ltac2:(tb__ "0|2|
S4S1S8SbVp;S8dVn;A1A2Vz;A2SaVz;S9Vp;SbeVn;A1M0A2A2A2S1S8S90Vp;A1M1Vz;A2SaVz;S9G1S10G0Z8A2A2A2A2A2").
Definition TZ (z : Z) : Prop := ltac2:(tb__ "0|0|
S1S8S9VT;Z50A2Vz;A2SaVz;S9VT;Zc60A2A2A2").
Definition BZ (z : Z) : Prop := ltac2:(tb__ "0|0|
S1S3S2S40S13A1S17VA;A1S43S13A1A3A1S1S8VqbF;Vz;A2SaVz;S9VqbF;S91A2A2A2A2").
Definition NZ (z : Z) : Prop := ltac2:(tb__ "0|0|
S1S3S2S63Vq;S64A3A1S1S8VnbF;Vz;A2SaVz;S9VnbF;Z2000A2A2A2A2").

Lemma QNE : ltac2:(tb__ "0|0|
S3S2S63Vq;S65A3A1S3S2S40S13A1S17VA;A1S43S13A1A3A1F_;").
Proof. intros Hq. destruct q; cbn in QC; [exact (proj1 QC) | congruence | exact (proj1 QC)]. Qed.
Lemma QB24 : ltac2:(tb__ "0|0|
S3S2S63Vq;S64A3A1S1S2S41S32VA;A1S44A3S3S2S40S0A1Sc9VA;A1S43S0A1A3A1A2F_;").
Proof. intros Hq. destruct q; cbn in QC; [congruence | exact (proj2 QC) | exact (proj2 (proj2 QC))]. Qed.
Lemma QK : ltac2:(tb__ "0|0|
S2S63Vq;S64A3SaSfS48S42S0S0A2S1fSc7VA;A1A1A2A1S9bA2F_;").
Proof. intros ->. exact (proj2 QC). Qed.
Lemma NBF_cnt : ltac2:(tb__ "0|1|
S3S2S63Vq;S64A3A1S1S8Z1ScaVA;A1M0A2S8G0Z2A2A2F_;").
Proof.
  intros Hq. destruct (QB24 Hq) as [HCI HNC]. pose proof (cF A rhoE tp md p n HA HL HCI HNC) as CF. cbn zeta in CF.
  destruct CF as (_ & _ & _ & _ & CN & _). exact CN.
Qed.

Lemma QDEC : ltac2:(tb__ "0|1|
S4S2S63Vq;S64A3M0S3G0A1A2").
Proof. clear. destruct q; [left; reflexivity | right; discriminate | right; discriminate]. Qed.

Definition kA : Z := ltac2:(tb__ "0|0|
SfS48S42S0S0A2S1fSc7VA;A1A1A2A1").
Definition chg_common (z : Z) : Prop := ltac2:(tb__ "0|3|
S4S1S8SbVp;Z10A2Vz;A2SaVz;SbVp;Z8M0A2A2A2S4S1S8Vp;Vz;A2SaVz;S9Vp;SbeVn;A1M1A2A2A2S4S1S8S90Vp;A1M2Vz;A2SaVz;S9G2S10G1G0A2A2A2A2S4S1S8S9VT;Z50A2Vz;A2SaVz;S9VT;Z70A2A2A2S1S8S9VT;Zad0A2Vz;A2SaVz;S9VT;Zc60A2A2A2A2A2A2A2").
Definition pc24 (z : Z) : Prop := ltac2:(tb__ "0|4|
S4S1S8S9S9VT;Zd0A2ScZ50Z18A2A2M0Vz;A2SaVz;S9G0Z10A2M1A2A2S1S8S9G1ScZ4M2SbScaVA;A1M3Z1A2A2A2Vz;A2SaVz;S9G1ScG2G3A2A2A2A2A2").
Lemma CHG_QA : ltac2:(tb__ "0|2|
S2S63Vq;S64A3S0S7S66Vq;VA;Vp;Vn;R1A5S4S87R1A1S4S1S8VqbF;R1A2SaR1S9VqbF;Z18A2M0A2A2S1S8S9G0ScZ8S86A2M1A2R1A2SaR1S9S9VqbF;Z20A2G1A2A2A2A2A2A2Fz;F_;").
Proof.
  intros HQ z. unfold chg_f, chg_common. rewrite HQ. lazy iota zeta beta. fold G T (lastq A). fold qbF kA. clear. tauto.
Qed.
Lemma CHG_QB : ltac2:(tb__ "0|0|
S3S2S63Vq;S64A3A1S0S7S66Vq;VA;Vp;Vn;R1A5S4S87R1A1S4S89R1A1S4S1S8VnbF;R1A2SaR1S9VnbF;Z2000A2A2A2S1S3S2S40S13A1S17VA;A1S43S13A1A3A1S1S8VqbF;R1A2SaR1S9VqbF;Z18A2A2A2A2A2A2A2A2Fz;F_;").
Proof.
  intros HQ z. pose proof QC as Y. unfold qcond in Y. unfold chg_f, chg_common, pc24. lazy iota zeta beta. fold G T (lastq A). fold qbF nbF. clear -HQ Y.
  destruct q; [congruence| |]; lazy iota zeta beta; [destruct Y as [E _] | destruct Y as [NE _]]; tauto.
Qed.

Lemma CHGE : ltac2:(tb__ "0|0|
S0S66Vq;VA;Vp;Vn;R1A5S4S83R2A1S4S8cR2A1S4S8aR2A1S8bR2A1A2A2A2F_;Fz;").
Proof.
  intros z Hz. pose proof BLK as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold blk_geo in B1. unfold CZ, TZ, BZ, NZ.
  destruct QDEC as [HQ|HQ].
  - apply (proj1 (CHG_QA HQ z)) in Hz. unfold chg_common in Hz. pose proof (QNE ltac:(rewrite HQ; discriminate)) as HNE.
    pose proof (QK HQ) as K. unfold kA in Hz. unfold kQuarantineBatchSize, kQuarantineBatchCount in *.
    clear -Hz HNE K B3 B5 B7 B8. destruct Hz as [Hz|[Hz|Hz]]; [lia | right; right; left; split; [exact HNE | lia] | right; right; left; split; [exact HNE | lia]].
  - apply (proj1 (CHG_QB HQ z)) in Hz. unfold chg_common, pc24 in Hz. pose proof (NBF_cnt HQ) as N1. unfold kQuarantineBatchSize in *.
    clear -Hz HQ N1 B3 B5 B7 B8. destruct Hz as [Hz|[Hz|[Hz|[HNE Hz]]]]; [lia | lia | right; right; right; split; [exact HQ | lia] | right; right; left; split; [exact HNE | lia]].
Qed.
Lemma CHGD : ltac2:(tb__ "0|1|
S0S4S66Vq;VA;Vp;Vn;R1A5M0S3G0A1A2Fz;").
Proof. intros z. unfold chg_f. clear. destruct q; cbn zeta; lia. Qed.

Lemma NBF : ltac2:(tb__ "0|f|
S3S2S63Vq;S64A3A1S1S1S8Z1ScaVA;A1M0A2S8G0Z2M1A2A2S1S1S8Z0M2Sc8VA;A1M3A2SaG3SdG1Z1cA2A2A2S1S2S0VnbF;S9S9VSB;ScZ18M4SdG1Z20A2M5A2A2M6ScZ10M7G3A2M8A2A3S1S2S0SeVnbF;G7A2G2A3S1S8G6VnbF;A2S1S8S9G8Z2000M9A2S22Sa1S16S1cVA;A1G4S1bA4MaA1MbA2S1S8GbS29GaA1McA2S1S8S9GcSdG1Z12A2MdA2S9SbG5SdG1Z1dA2A2GdA2A2S1S2S0SeG8G9A2G2A3S1S5cS0G3Sc9VA;A1A3S1S4S8S9VnbF;G9A2MeVT;A2S8S9VT;Z1000A2VnbF;A2A2S1S4S8S9Vp;SbeVn;A1A2VnbF;A2S8GeSbVp;G7A2A2A2S3S2S40S13A1S17VA;A1S43S13A1A3A1S4S8S9VqbF;S91A2VnbF;A2S8GeVqbF;A2A2F_;A2A2A2A2A2A2A2A2A2A2A2A2F_;").
Proof.
  intros Hq. destruct (QB24 Hq) as [HCI HNC]. pose proof (cF A rhoE tp md p n HA HL HCI HNC) as CF. cbn zeta in CF. fold G T SB in CF.
  destruct CF as (_ & _ & _ & _ & CN & CX & _ & NT & _ & NP & NQ & S2 & S1 & S16).
  pose proof HA as (HG & HR & HF & HRest & _). destruct HRest as (_ & _ & HPR & _). destruct HPR as (_ & _ & _ & HCR).
  pose proof (HCR 24 ltac:(lia)) as C24. destruct C24 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & _ & _ & _ & _ & N7 & _).
  unfold kUserSpaceSize, kUserMapSize, kFreeArraySize, kRegionSize in M3. fold G in N7, M2, M3.
  assert (HXin : In (top24 A) (cache24 A)).
  { unfold top24, cache24 in *. set (cs := cs_cache (nthZ (aa_cls A) 24 cs_empty)) in *. apply nth_In. destruct cs; [congruence | cbn; lia]. }
  destruct (N7 (top24 A) ltac:(apply in_or_app; right; exact HXin)) as (X0 & XM & XA). unfold kCompactPtrScale in XM, XA.
  rewrite Z.shiftl_mul_pow2 in XM, XA by lia. change (2 ^ 4) with 16 in XM, XA. change (Size 24) with 8192 in XM, XA. rewrite Z.mul_comm in XM, XA.
  unfold nbF, nb_addr, region_beg, kRegionSize. fold G SB. change (2 ^ 32) with 4294967296 in *.
  destruct GEO as (_ & _ & SB1 & _ & SB8 & _).
  repeat match goal with |- _ /\ _ => split end; try assumption; try (clear -CN CX X0 XA M2 M3 SB1; lia).
  - rewrite <- Zplus_mod_idemp_l. replace ((SB + 24 * 4294967296) mod 16) with 0; [rewrite Z.add_0_l; rewrite <- (Z.mod_mod_divide _ 8192 16) by (exists 512; reflexivity); rewrite XM; reflexivity|].
    symmetry. rewrite <- Zplus_mod_idemp_l. replace (SB mod 16) with 0; [reflexivity|]. symmetry. rewrite <- (Z.mod_mod_divide SB (2 ^ 16) 16) by (exists (2 ^ 12); reflexivity).
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 GEO)))))). reflexivity.
Qed.

Lemma QBF : ltac2:(tb__ "0|11|
S3S2S40S13A1S17VA;A1M0S43S13A1A3A1Sc7VA;A1S13S1S5cS13R1G0A3S1S2S0SeVqbF;Z10M1A2Z0M2A3S1S8S9VSB;ScZ18M3SdZ2M4Z20A2M5A2A2M6VqbF;A2S1S8SfS48S42S0S0A2M7S1fR1A1M8A2A1S9bA2S1S6S0S0S1S2S0VqbF;S9G6ScG1R1A2M9A2A3S1S8G2R1A2S1S2S0SeR1Z200A2G2A3S8S9G9Z2000MaA2S22Sa1S16S1cVA;A1G3S1bA4MbA1McA2A2A2A2Lx;A2S1S8GcS29GbA1MdA2S1S8S9GdSdG4Z12A2MeA2S9SbG5SdG4Z1dA2A2GeA2A2S1S4S8S9VqbF;S91A2MfVT;A2S8S9VT;Z1000A2VqbF;A2A2S1S4S8S9Vp;SbeVn;A1A2VqbF;A2S8GfSbVp;G1A2A2A2S1S2S0S24R1A1S9S91S61S0G7G7S0S9S4cS0S0R2A3R1A2Lacc;Lit;G2G8A5A2A3S1S8ScGaSfS48S13G0A2A1A2Sa2G0A1M10A2S1S8G2G10A2S8G10S98A2A2A2A2A2A2A2A2A2A2A2A2A2Tb;F_;").
Proof.
  intros HNE b. pose proof (qF A rhoE tp md p n HA HL) as QF. cbn zeta in QF. fold G T SB in QF.
  destruct QF as (_ & _ & _ & QS & QLB & QL). destruct (QL HNE) as (_ & _ & _ & _ & _ & BK & _ & B16 & BS1 & BS2 & BT & _ & BP). clear QL.
  pose proof HA as (HG & HR & HF & HRest & _). destruct HRest as (_ & _ & HPR & _ & HQR & _). destruct HPR as (_ & _ & _ & HCR).
  pose proof (HCR 24 ltac:(lia)) as C24. destruct C24 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _).
  unfold kUserSpaceSize, kUserMapSize, kFreeArraySize, kRegionSize in M3. fold G in M2, M3.
  destruct HQR as (QB & _). pose proof (last_In (aa_q_thread A) qb_dflt HNE) as Hin.
  pose proof (proj1 (Forall_forall _ _) QB (lastq A) ltac:(apply in_or_app; left; exact Hin)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & (x & X1 & X2 & XM & X3)).
  fold G in X1, X3. unfold region_beg, kRegionSize, kQuarantineBatchSize in X1, X3. change (2 ^ 32) with 4294967296 in *.
  unfold b, qbF, lastq in *. change (2 ^ 32) with 4294967296.
  split; [exact Hin|]. split; [exact B16|]. split; [clear -X1 X2; lia|]. split; [exact R4|].
  split; [exists x; split; [exact X1|]; split; [exact X2|]; split; [exact XM | exact X3]|].
  split; [clear -M2; lia|]. split; [clear -M3; lia|]. split; [exact BT|]. split; [exact BP|]. split; [exact R5|]. split; [exact QLB | exact QS].
Qed.

Definition mapzone (ch : sec_chunk) (z : Z) : Prop := ltac2:(tb__ "0|2|
S4S1S8S18Vch;A1M0Vz;A2SaVz;S9G0S20Vch;A1A2M1A2A2S1S8S90G0A1Vz;A2SaVz;S90G1A1A2A2A2").

Lemma KP : ltac2:(tb__ "0|9|
S2S41S8fVn;A1S44A3S94S95Vn;A1A1S0SbSbVp;S8dVn;A1M0A2S9VSB;ScR1SdZ2M1Z20A2M2A2A2A2S0S10R1Z10M3A2S0S8eR3A1S0S1Sc6VSB;R4R2R1S21VG;A1A5S1S2S0R3ScG3R2A2A3S1S8Z0M4R3A2S1S2S0SeR3R1A2G4A3S1S8S9R3R1A2S22Sa1S16S1cVA;A1R4S1bA4M5A1M6A2S1S8G6S29G5A1M7A2S1S8S9G7SdG1Z12A2M8A2S9SbG2SdG1Z1dA2A2G8A2A2S1S5cS0R2Sa4VG;VA;R4A3A3S1S1S8Z1R4A2S8R4Z1eA2A2S1S1S8G3R1A2S8R1Z10000A2A2S1S2S0SeR1G3A2G4A3S1S8S9SbeVn;A1G0A2R1A2S0S83R1A1Sc4VSB;R6ScG3R4A2R3R2A5F_;Fz;A2A2A2A2A2A2A2A2A2A2A2A2Tsz;Tx;To;Tc;F_;").
Proof.
  intros HP c o x sz. pose proof BLK as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold blk_geo in B1.
  pose proof (live_slot A rhoE tp md p n HA HL HP) as LS. cbn zeta in LS. fold G c in LS.
  destruct LS as (C1 & O0 & OM & OA & LO & HI & IDin & O16). unfold region_beg, kRegionSize in O0, OM, OA, LO, HI, IDin, O16. fold SB in O0, OM, OA, LO, HI, IDin, O16.
  change (2 ^ 32) with 4294967296 in O0, OM, OA, LO, HI, IDin, O16. fold o in O0, OM, OA, LO, HI, IDin, O16.
  pose proof (needed_fits n B3 HP) as (F1 & F2 & F3). fold c in F1, F2. pose proof (size_ok_all c C1) as [SZ1 SZ2]. fold sz in F1, SZ1, SZ2, OM, OA, HI.
  pose proof HA as (HG & HR & HF & HRest & _). destruct HRest as (_ & _ & HPR & _). destruct HPR as (_ & _ & _ & HCR).
  pose proof (HCR c C1) as Cc. destruct Cc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _). fold G in M2, M3.
  unfold kUserSpaceSize, kUserMapSize, kFreeArraySize, kRegionSize in M3.
  destruct GEO as (_ & _ & SB1 & SB2 & SB8 & _ & _ & _ & _ & TG & _).
  assert (EO : o = 16 * x) by (unfold x; clear -O16; pose proof (Z.div_mod o 16); lia).
  split; [unfold cz_env; clear -SB1 SB2 SB8 C1 O0 EO SZ1 SZ2 OA M2 M3 TG; lia|].
  split; [exact EO|]. split; [exact O0|]. split; [exact OM|]. split; [exact OA|]. split; [clear -M2; lia|]. split; [clear -M3; lia|].
  split; [exact IDin|].
  split; [exact C1|]. split; [exact SZ1|]. split; [exact SZ2|]. split; [clear -F1 F3; lia|].
  intros z Hz. unfold czone. cbn zeta. rewrite <- EO. unfold CZ in Hz.
  assert (AB : SB + c * 4294967296 + o = p - rz n) by (unfold o; clear; lia). change (2 ^ 32) with 4294967296. rewrite AB.
  assert (AB8 : (p - rz n) mod 8 = 0).
  { destruct (proj1 (Z.mod_divide p 8 ltac:(lia)) B10) as [u Hu]. destruct (proj1 (Z.mod_divide (rz n) 16 ltac:(lia)) B9) as [v Hv].
    apply Z.mod_divide; [lia|]. exists (u - 2 * v). clear -Hu Hv. lia. }
  destruct Hz as [Hz|Hz]; [left; clear -Hz B8 F1 F3 B5; lia | right].
  replace p with (p - rz n + rz n) in Hz at 1 2 by (clear; lia). rewrite (Sh_SB (p - rz n) (rz n) AB8) in Hz.
  assert (D1 : rz n / 8 + N8 n / 8 <= sz / 8).
  { destruct (proj1 (Z.mod_divide (rz n) 16 ltac:(lia)) B9) as [v Hv]. destruct (proj1 (Z.mod_divide (N8 n) 8 ltac:(lia)) B6) as [w Hw].
    rewrite Hv, Hw. replace (v * 16) with (2 * v * 8) by (clear; lia). rewrite !Z.div_mul by (clear; lia).
    apply Z.div_le_lower_bound; [clear; lia|]. clear -Hv Hw F1 F3. lia. }
  pose proof (Z.div_pos (rz n) 8 ltac:(clear -B8; lia) ltac:(clear; lia)) as D0. clear -Hz D1 D0. lia.
Qed.

Lemma KS : ltac2:(tb__ "0|d|
S2S41S8fVn;A1S4aA3S6S47S47S6S15S15S1S2S49S15A1S5eS15S28VA;A1M0R2A3S4bS15R1A2A3M1S1S5cS15R1G0A3S1S2S0Vp;S9S9S18R1A1M2Z1000M3A2Z800A2A3S1S2S0S39R1A1M4S9S9cVn;Z8A2G3A2A3S1S2S0SeG2G3A2Z0A3S1S8S9G3G4A2S20R1A1M5A2S1S8S9G2G5A2M6S21VG;A1A2S1S8Z646000G2A2S1S4S8G6Z7fff7000A2S8Z10007fff8000G2A2A2S1S4S8G6VSB;A2S8S9S9VSB;SdZ2Z25A2A2G3A2G2A2A2S1S4S8G6VT;A2S8S9VT;G3A2G2A2A2S1S4S8G6S2fVG;A1M7A2S8S9G7S96A2G2A2A2S1S4S8G6S36VG;A1M8A2S8S9G8S9aA2G2A2A2S1S4S8G6S2dVG;A1M9A2S8S9G9G3A2G2A2A2S1S4S8G6S2eVG;A1MaA2S8S9GaG3A2G2A2A2S1S47S15G1S3S2S47R5R3A3A1S4S8S9S18R5A1MbS20R5A1A2S18R3A1McA2S8S9GcS20R3A1A2GbA2A2F_;F_;Fch';Fj;S0S83R1A1S84R3R2A2F_;Fz;A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Lch;A2Li;A2F_;").
Proof.
  intros HP. pose proof BLK as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold blk_geo in B1.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & _). destruct HRest as (Hsep & _ & _ & HSR & _).
  destruct HI3 as (_ & HPS & SEC3 & _). fold G in SEC3.
  destruct (HPS p n HL) as [Hp' | (ch & Hch & Eb & Esz)]; [rewrite HP in Hp'; discriminate|].
  destruct (In_nth_error _ _ Hch) as [i Hi]. destruct HSR as (HS & _). pose proof (HS i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
  fold G in D10, D12. destruct (SEC3 i ch Hi) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). fold SB T in X1, X2. rewrite kSpaceSize_val in X1.
  pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; clear -D8 D9; lia)) as MB. destruct D10 as (_ & _ & _ & _ & WB).
  unfold PG, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  exists i, ch. split; [exact Hi|]. split; [exact Hch|]. split; [exact Eb|]. split; [exact Esz|]. split; [exact D6|]. split; [exact D8|]. split; [exact D12|].
  split; [exact MB|]. split; [exact WB|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X6|]. split; [exact X7|]. split; [exact X5|].
  intros z Hz. unfold mapzone. unfold CZ in Hz.
  pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU. assert (EN : N8 n = round_up n 8) by (unfold N8, round_up; replace (n + 8 - 1) with (n + 7) by (clear; lia); reflexivity).
  destruct Hz as [Hz|Hz]; [left; clear -Hz Eb Esz D8 EN B3 B8; lia | right].
  pose proof (Sh_mono (sc_map_beg ch) p ltac:(clear -Eb; lia)) as M1.
  assert (M2 : Sh p + N8 n / 8 <= Sh (sc_map_beg ch + sc_map_size ch)).
  { unfold Sh. destruct (proj1 (Z.mod_divide p 8 ltac:(clear; lia)) B10) as [u Hu]. rewrite Hu. rewrite Z.div_mul by (clear; lia).
    pose proof (Z.div_le_mono (p + N8 n) (sc_map_beg ch + sc_map_size ch) 8 ltac:(clear; lia) ltac:(clear -Eb Esz D8 EN; lia)) as DM.
    rewrite Hu in DM. destruct (proj1 (Z.mod_divide (N8 n) 8 ltac:(clear; lia)) B6) as [w Hw]. rewrite Hw in DM |- *.
    replace (u * 8 + w * 8) with ((u + w) * 8) in DM by (clear; lia). rewrite !Z.div_mul in DM |- * by (clear; lia). clear -DM. lia. }
  clear -Hz M1 M2. lia.
Qed.

Lemma CZN : ltac2:(tb__ "0|6|
S0S83R1A1S4S1S4S1S8S9Z646000Z1000A2Vp;A2S8S9Vp;SbeVn;A1M0A2M1Z7fff7000A2A2S8S9Z10007fff8000Z10A2Vp;A2A2S1S1S8SbVp;S8dVn;A1M2A2R2A2SaR2G1A2A2S1S8G2Z800A2S1SaG1S21VG;A1M3A2S8G3Z7fffff800000A2A2A2A2A2S1S8Z800c0c00R2A2S1S1S8S90Vp;A1M4R2A2SaR2S9G4S10G0Z8A2A2M5A2A2S8G5Z10007fef8000A2A2A2A2F_;Fz;").
Proof.
  intros z Hz. pose proof BLK as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold blk_geo in B1. destruct GEO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TG & _).
  unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. unfold CZ in Hz. destruct Hz as [Hz|Hz]; [left; clear -Hz B1 B4 B8 TG; lia | right].
  unfold Sh, SHADOW_OFF in *. pose proof (Z.div_le_mono 6582272 p 8 ltac:(clear; lia) ltac:(clear -B1; lia)) as D1.
  destruct (proj1 (Z.mod_divide p 8 ltac:(clear; lia)) B10) as [u Hu]. destruct (proj1 (Z.mod_divide (N8 n) 8 ltac:(clear; lia)) B6) as [w Hw].
  pose proof (Z.div_le_mono (p + N8 n) 140737479966720 8 ltac:(clear; lia) ltac:(clear -B4 TG; lia)) as D2.
  rewrite Hu, Hw in *. rewrite !Z.div_mul in * by (clear; lia). replace (u * 8 + w * 8) with ((u + w) * 8) in D2 by (clear; lia).
  rewrite Z.div_mul in D2 by (clear; lia). change (6582272 / 8) with 822784 in D1. change (140737479966720 / 8) with 17592184995840 in D2.
  clear -Hz D1 D2. lia.
Qed.

Lemma NCH_img : ltac2:(tb__ "0|0|
S0S1S8S97R1A2SaR1S93A2A2S3S66Vq;VA;Vp;Vn;R2A5A1F_;Fz;").
Proof.
  intros z Hz Hc. unfold IMG_LO, IMG_HI in Hz. destruct GEO as (_ & _ & SB1 & _ & _ & _ & _ & _ & TI & _).
  destruct (CHGE z Hc) as [K|[K|[K|K]]].
  - destruct (CZN z K) as [K'|K']; clear -Hz K'; lia.
  - unfold TZ in K. clear -Hz K TI. lia.
  - destruct K as [HNE K]. pose proof (QBF HNE) as (_ & _ & Q3 & _). clear -Hz K Q3 SB1. lia.
  - destruct K as [HQ K]. pose proof (NBF HQ) as (_ & _ & _ & _ & N5 & _). clear -Hz K N5 SB1. lia.
Qed.

Lemma NCH_top : ltac2:(tb__ "0|0|
S0S8S21VG;A1R1A2S3S66Vq;VA;Vp;Vn;R2A5A1F_;Fz;").
Proof.
  intros z Hz Hc. destruct GEO as (_ & T2 & SB1 & SB2 & _ & _ & _ & _ & _ & TG & _).
  destruct (CHGE z Hc) as [K|[K|[K|K]]].
  - destruct (CZN z K) as [K'|K']; clear -Hz K' TG; lia.
  - unfold TZ in K. clear -Hz K T2. lia.
  - destruct K as [HNE K]. pose proof (QBF HNE) as (_ & _ & _ & _ & (x & X1 & X2 & _ & X3) & M2 & M3 & _). unfold kQuarantineBatchSize in K. clear -Hz K X1 X2 X3 M2 M3 SB2. lia.
  - destruct K as [HQ K]. pose proof (NBF HQ) as (_ & _ & N3 & _ & _ & N6 & N7 & N8 & _). clear -Hz K N3 N6 N7 N8 SB2. lia.
Qed.

Lemma NCH_T : ltac2:(tb__ "0|0|
S0S4S1S8VT;R1A2SaR1S9VT;Z50A2A2A2S4S1S8S9VT;Z70A2R1A2SaR1S9VT;Z850A2A2A2S4S1S8S9VT;Z8a0A2R1A2SaR1S9VT;Zad0A2A2A2S1S8S9VT;Zc60A2R1A2SaR1S9VT;Z1000A2A2A2A2A2A2S3S66Vq;VA;Vp;Vn;R2A5A1F_;Fz;").
Proof.
  intros z Hz Hc. pose proof (blkF_geom A rhoE tp md p n HA HL HCLS) as (_ & _ & _ & _ & BT & _). fold G T in BT.
  destruct GEO as (_ & _ & SB1 & _ & _ & _ & ST & TB & _). pose proof BLK as (B1 & _ & B3 & _ & B5 & _ & B7 & B8 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  assert (NSH : ~ (Sh p <= z < Sh p + N8 n / 8)).
  { intros Hs. destruct (CZN z ltac:(right; exact Hs)) as [K|K]; [clear -Hs K; unfold Sh, SHADOW_OFF in Hs; lia | clear -Hz K TB; lia]. }
  destruct QDEC as [HQ|HQ].
  - apply (proj1 (CHG_QA HQ z)) in Hc. unfold chg_common in Hc.
    pose proof (QBF (QNE ltac:(rewrite HQ; discriminate))) as (_ & _ & _ & Q4 & _ & _ & _ & QT & _). pose proof (QK HQ) as QK'. unfold kA in Hc.
    unfold kQuarantineBatchSize, kQuarantineBatchCount in *. clear -Hz Hc NSH BT QT QK' B5 B7 B8. lia.
  - apply (proj1 (CHG_QB HQ z)) in Hc. unfold chg_common, pc24 in Hc.
    pose proof (NBF HQ) as (N1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & NT & _ & NQ).
    assert (NL : aa_q_thread A <> [] -> ~ (qbF <= z < qbF + 24)).
    { intros HNE Hb. pose proof (QBF HNE) as (_ & _ & _ & _ & _ & _ & _ & QT & _). unfold kQuarantineBatchSize in QT. clear -Hz Hb QT. lia. }
    clear -Hz Hc NSH BT NT NL N1 B5 B7 B8. destruct Hc as [Hc|[Hc|[Hc|[HNE Hc]]]]; [lia | lia | lia | exact (NL HNE Hc)].
Qed.
Lemma NCH_cnt24 : ltac2:(tb__ "0|0|
S2S63Vq;S64A3S0S1S8S9VT;Z850A2R1A2SaR1S9VT;Z8a0A2A2A2S3S66Vq;VA;Vp;Vn;R2A5A1F_;Fz;F_;").
Proof.
  intros HQ z Hz Hc. pose proof (blkF_geom A rhoE tp md p n HA HL HCLS) as (_ & _ & _ & _ & BT & _). fold G T in BT.
  destruct GEO as (_ & _ & SB1 & _ & _ & _ & ST & TB & _). pose proof BLK as (B1 & _ & B3 & _ & B5 & _ & B7 & B8 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  assert (NSH : ~ (Sh p <= z < Sh p + N8 n / 8)).
  { intros Hs. destruct (CZN z ltac:(right; exact Hs)) as [K|K]; [clear -Hs K; unfold Sh, SHADOW_OFF in Hs; lia | clear -Hz K TB; lia]. }
  apply (proj1 (CHG_QA HQ z)) in Hc. unfold chg_common in Hc.
  pose proof (QBF (QNE ltac:(rewrite HQ; discriminate))) as (_ & _ & _ & Q4 & _ & _ & _ & QT & _). pose proof (QK HQ) as QK'. unfold kA in Hc.
  unfold kQuarantineBatchSize, kQuarantineBatchCount in *. clear -Hz Hc NSH BT QT QK' B5 B7 B8. lia.
Qed.

Lemma CZI : ltac2:(tb__ "0|d|
S1S4S8S9Vp;SbeVn;A1A2M0VT;A2S8S9VT;Z1000M1A2SbVp;S8dVn;A1A2M2A2A2S1S4S8G0S2dVG;A1M3A2S8S9G3G1A2G2A2A2S1S4S8G0S2eVG;A1M4A2S8S9G4G1A2G2A2A2S1S4S8G0S36VG;A1M5A2S8S9G5S9aA2G2A2A2S1S4S8G0S2fVG;A1M6A2S8S9G6S96A2G2A2A2S1S4S8G0S9VSB;SdZ2M7Z25A2A2M8A2S8S9G8G1A2G2A2A2S1S0S0S5cS42S0S0A2S46S0S0R2R1A4Sd5S33VA;A1A1A3S4S8G0R3A2S8S9R3R2A2G2A2A2F_;FL;Fbb;S1S47S15S2S49S15A1S5eS15S28VA;A1R2A3S4bS15R1A2A3S4S8G0S18R2A1M9A2S8S9G9Z20MaA2G2A2A2F_;Fch';Fj;S1S0S1S8Z1R1A2S8R1Z1eA2A2S4S8G0S9S9VSB;ScR2SdG7GaA2MbA2A2McSbGbSdG7Z1dA2A2A2A2S8S9GcGbA2G2A2A2F_;Fc';S1S4S1S8S9Z646000G1A2Vp;A2S8G0Z7fff7000A2A2S8S9Z10007fff8000Z10A2Vp;A2A2SaG0S21VG;A1A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof BLK as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _). destruct HRest as (_ & _ & _ & (HS & _) & _).
  destruct HI3 as ((S1 & S2 & S3 & S4 & _) & _ & SEC3 & _ & DEP3 & _). fold G T SB in S1, S2, S3, S4, SEC3, DEP3.
  rewrite kSpaceSize_val in S1, S2, S3, S4. unfold kPtrArrayReserve in S4 |- *. rewrite FS_total_val.
  destruct GEO as (T1 & T2 & SB1 & SB2 & SB8 & _ & ST & TB & TI & TG & F1 & F2 & FT & FS & FB & C1 & C2 & TC & SC & D1 & D2 & TD & SD).
  destruct (is_primary n) eqn:HP.
  - pose proof (KP HP) as KK. cbn zeta in KK. destruct KK as (CE & EO & O0 & OM & OA & M2 & M3 & IDin & CC & SZ & SZM & FIT & KC).
    set (c := ClassID (needed n)) in *. set (o := p - rz n - (SB + c * 2 ^ 32)) in *.

    assert (SL : SB + c * 2 ^ 32 <= p - rz n /\ p + N8 n <= p - rz n + Size c /\ p - rz n + Size c <= SB + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)).
    { unfold o in O0, OA. clear -O0 OA M2 M3 FIT B8. lia. }
    destruct SL as (SL1 & SL2 & SL3).
    assert (INS : SB <= p - rz n /\ p - rz n + Size c <= SB + 31 * 2 ^ 32) by (clear -SL1 SL3 CC; nia).
    split; [clear -INS SL2 ST B8; lia|]. split; [clear -INS SL2 SC B8; lia|]. split; [clear -INS SL2 SD B8; lia|]. split; [clear -INS SL2 FS B8; lia|].
    split; [clear -INS SL2 S4 B8; lia|]. split; [clear -INS SL2 B8; lia|]. split.
    { intros bb L Hbb. destruct (DEP3 (bb, L) Hbb) as (_ & _ & _ & _ & _ & SS & _). unfold sepZ in SS. cbn [fst snd] in SS. rewrite kSpaceSize_val in SS. clear -INS SL2 SS B8. lia. }
    split.
    { intros j ch' Hj. destruct (SEC3 j ch' Hj) as (X1 & _). rewrite kSpaceSize_val in X1.
      pose proof (HS j ch' Hj) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & _). unfold PG in D8. clear -INS SL2 X1 D8 D9 B8. lia. }
    split; [|clear -B1 B4; lia].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [clear -SL1 SL2 SL3 B8; lia|].
    assert (CC' : c' + 1 <= c \/ c + 1 <= c') by (clear -NE; lia). clear -SL1 SL2 SL3 CC' Hc' CC B8. nia.
  - destruct (KS HP) as (i & ch & Hi & Hch & Eb & Esz & D6 & D8 & D12 & MB & WB & X1 & X2 & X3 & X4 & X6 & X7 & X5 & KC).
    rewrite FS_total_val in X4. unfold kPtrArrayReserve in X3.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU. assert (EN : N8 n = round_up n 8) by (unfold N8, round_up; replace (n + 8 - 1) with (n + 7) by (clear; lia); reflexivity).
    assert (MP : sc_map_beg ch + 32 <= p - rz n /\ p + N8 n <= sc_map_beg ch + sc_map_size ch) by (clear -Eb Esz D8 EN B3 B8; lia).
    destruct MP as [MP1 MP2].
    split; [clear -MP1 MP2 X2; lia|]. split; [clear -MP1 MP2 X6; lia|]. split; [clear -MP1 MP2 X7; lia|]. split; [clear -MP1 MP2 X4; lia|].
    split; [clear -MP1 MP2 X3; lia|]. split; [clear -MP1 MP2 X1; lia|]. split.
    { intros bb L Hbb. destruct (DEP3 (bb, L) Hbb) as (_ & _ & _ & _ & _ & _ & _ & SM). pose proof (SM ch Hch) as SS. unfold sepZ in SS. cbn [fst snd] in SS. clear -MP1 MP2 SS. lia. }
    split.
    { intros j ch' Hj. destruct (Nat.eq_dec i j) as [<-|NE].
      - rewrite Hi in Hj. injection Hj as E. subst ch'. right. exact MP1.
      - pose proof (HS j ch' Hj) as (_ & _ & _ & _ & _ & _ & _ & D8' & D9' & _). unfold PG in D8'.
        destruct (X5 j ch' Hj NE) as [Y|Y]; clear -MP1 MP2 Y D8' D9'; lia. }
    split; [|clear -B1 B4; lia]. intros c' Hc'. clear -MP1 MP2 X1 Hc'. nia.
Qed.

Lemma PRZ : ltac2:(tb__ "0|1|
S4S1S8Z646000SbVp;S8dVn;A1A2M0A2S8S9Vp;SbeVn;A1A2Z7fff7000A2A2S8Z10007fff8000G0A2A2").
Proof.
  pose proof BLK as (B1 & _ & B3 & _ & _ & _ & _ & B8 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. destruct GEO as (_ & _ & SB1 & _).
  destruct (is_primary n) eqn:HP.
  - right. pose proof (KP HP) as KK. cbn zeta in KK. destruct KK as (_ & EO & O0 & _ & _ & _ & _ & _ & CC & _). clear -EO O0 SB1 CC. nia.
  - destruct (KS HP) as (i & ch & Hi & Hch & Eb & Esz & D6 & D8 & D12 & MB & WB & _).
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU. clear -Eb Esz D8 MB WB B1 B3 B8 RU. lia.
Qed.

Lemma CZA : ltac2:(tb__ "0|a|
S0S1S8SbVp;S8dVn;A1A2R1A2SaR1S9Vp;SbeVn;A1A2A2A2S1S3S1S8VT;R2A2SaR2S9VT;Z1000M0A2A2A2A1S1S3S1S8S2dVG;A1M1R2A2SaR2S9G1G0A2A2A2A1S1S3S1S8S2eVG;A1M2R2A2SaR2S9G2G0A2A2A2A1S1S2S41Sa5VG;R2A2S4aA3S1S3S1S8S2fVG;A1M3R2A2SaR2S9G3S96A2A2A2A1S1S3S1S8S9VSB;SdZ2M4Z25A2A2M5R2A2SaR2S9G5G0A2A2A2A1S1S0S0S5cS42S0S0A2S46S0S0R2R1A4Sd5S33VA;A1A1A3S3S1S8R3R5A2SaR5S9R3R2A2A2A2A1F_;FL;Fbb;S1S47S15S2S49S15A1S5eS15S28VA;A1R2A3S4bS15R1A2A3S3S1S8S18R2A1M6R5A2SaR5S9G6Z20M7A2A2A2A1F_;Fch';Fj;S1S0S1S8Z1R1A2S8R1Z1eA2A2S3S1S8S9S9VSB;ScR2SdG4G7A2M8A2A2M9SbG8SdG4Z1dA2A2A2R4A2SaR4S9G9G8A2A2A2A1F_;Fc';S1S1S4S1S8Z646000R2A2SaR2Z7fff7000A2A2S8Z10007fff8000R2A2A2SaR2S21VG;A1A2A2S3S1S8S97R2A2SaR2S93A2A2A1A2A2A2A2A2A2A2A2A2A2F_;Fz;").
Proof.
  intros z Hz. pose proof CZI as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11). pose proof HA as (HG & _). pose proof BLK as (_ & _ & _ & _ & _ & _ & _ & B8 & _).
  pose proof PRZ as PZ.
  split; [clear -Hz I1 B8; lia|]. split; [clear -Hz I2 B8; lia|]. split; [clear -Hz I3 B8; lia|].
  split; [apply fs_footb_hi; [exact HG | unfold LOW_SHADOW_BEG, HIGH_SHADOW_END; clear -Hz PZ; lia | clear -Hz I4 B8; lia]|].
  split; [clear -Hz I5 B8; lia|]. split; [clear -Hz I6 B8; lia|].
  split; [intros bb L Hbb; pose proof (I7 bb L Hbb); clear -Hz H B8; lia|].
  split; [intros j ch' Hj; pose proof (I8 j ch' Hj); clear -Hz H B8; lia|].
  split; [intros c' Hc'; pose proof (I9 c' Hc'); clear -Hz H B8; lia|].
  unfold IMG_LO, IMG_HI. clear -Hz PZ I11. lia.
Qed.

Lemma CZS : ltac2:(tb__ "0|1|
S0S1S8S90Vp;A1M0R1A2SaR1S9G0S10SbeVn;A1Z8A2A2A2A2S1S1S8Z800c0c00R2A2SaR2Z10007fef8000A2A2S2S41Sa5VG;R2A2S4aA3A2F_;Fz;").
Proof.
  intros z Hz. destruct (CZN z ltac:(right; exact Hz)) as [K|K]; [exfalso|].
  { pose proof BLK as (B1 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. clear -Hz K B1. unfold Sh, SHADOW_OFF in Hz.
    pose proof (Z.div_lt_upper_bound p 8 (2 ^ 45) ltac:(lia) ltac:(lia)). lia. }
  split; [clear -K; lia|].
  pose proof BLK as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold blk_geo in B1. destruct GEO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TG & _).
  pose proof HA as (HG & _). pose proof CZI as (_ & _ & _ & I4 & _ & _ & _ & _ & _ & I10 & I11). rewrite FS_total_val in I4.

  destruct (proj1 (Z.mod_divide p 8 ltac:(clear; lia)) B10) as [u Hu]. destruct (proj1 (Z.mod_divide (N8 n) 8 ltac:(clear; lia)) B6) as [w Hw].
  assert (Ha : p <= p + 8 * (z - Sh p) < p + N8 n).
  { unfold Sh in Hz |- *. rewrite Hu, Hw in *. rewrite Z.div_mul in * by (clear; lia). clear -Hz. lia. }
  assert (Ea : z = Sh (p + 8 * (z - Sh p))).
  { unfold Sh. rewrite Hu. rewrite Z.div_mul by (clear; lia).
    replace (u * 8 + 8 * (z - (u + SHADOW_OFF))) with ((z - SHADOW_OFF) * 8) by (clear; lia). rewrite Z.div_mul by (clear; lia). clear; lia. }
  apply (fs_footb_sh G z (p + 8 * (z - Sh p)) HG); [clear -Ha I10 I11 TG; lia | rewrite FS_total_val; clear -Ha I4 B5 B8; lia | exact Ea].
Qed.

Lemma NCH_out : ltac2:(tb__ "0|1|
S0S0S0S1S8R3R1A2SaR1R2A2A2S4S8S9Vp;SbeVn;A1A2R4A2S8R3SbVp;S8dVn;A1A2A2A2S4S8R4Z7fff7000A2S8Z10007fff8000R5A2A2S4S8S9VT;Z1000M0A2R6A2S8R5VT;A2A2S4S8R6VSB;A2S8S9S9VSB;SdZ2Z25A2A2G0A2R7A2A2S3S66Vq;VA;Vp;Vn;R6A5A1F_;F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hz SP SBD ST SS Hc. pose proof BLK as (_ & _ & _ & _ & _ & _ & _ & B8 & _). destruct GEO as (_ & _ & SB1 & _).
  destruct (CHGE z Hc) as [K|[K|[K|K]]].
  - destruct (CZN z K) as [K'|K']; [clear -Hz K' SP B8; lia | clear -Hz K' SBD; lia].
  - unfold TZ in K. clear -Hz K ST. lia.
  - destruct K as [HNE K]. pose proof (QBF HNE) as (_ & _ & Q3 & _ & (x & X1 & X2 & XM & X3) & M2 & M3 & _). unfold kQuarantineBatchSize in K. clear -Hz K SS Q3 X1 X2 X3 M2 M3. lia.
  - destruct K as [HQ K]. pose proof (NBF HQ) as (_ & _ & N3 & _ & N5 & N6 & N7 & N8' & _). clear -Hz K SS N3 N5 N6 N7 N8'. lia.
Qed.

Lemma NCH_meta : ltac2:(tb__ "0|1|
S0S1S8S9VSB;SdZ2Z25A2A2M0R1A2SaR1S9G0Z1000A2A2A2S3S66Vq;VA;Vp;Vn;R2A5A1F_;Fz;").
Proof.
  intros z Hz Hc. pose proof BLK as (_ & _ & _ & _ & _ & _ & _ & B8 & _). destruct GEO as (_ & _ & SB1 & _ & _ & _ & ST & _).
  pose proof CZI as (_ & _ & _ & _ & _ & I6 & _).
  destruct (CHGE z Hc) as [K|[K|[K|K]]].
  - destruct (CZN z K) as [K'|K']; [clear -Hz K' I6 B8; lia | clear -Hz K' SB1; lia].
  - unfold TZ in K. clear -Hz K ST. lia.
  - destruct K as [HNE K]. pose proof (QBF HNE) as (_ & _ & Q3 & _ & (x & X1 & X2 & XM & X3) & M2 & M3 & _). unfold kQuarantineBatchSize in K. clear -Hz K Q3 X1 X2 X3 M2 M3. lia.
  - destruct K as [HQ K]. pose proof (NBF HQ) as (_ & _ & N3 & _ & N5 & N6 & N7 & N8' & _). clear -Hz K N3 N5 N6 N7 N8'. lia.
Qed.

Lemma NCH_fa : ltac2:(tb__ "0|3|
S0S0S1S8Z1R2A2S8R2Z1eA2A2S1S8S9S9VSB;ScR3SdZ2M0Z20A2M1A2A2M2SbG1SdG0Z1dA2A2A2R2A2SaR2S9G2G1A2A2A2S3S66Vq;VA;Vp;Vn;R3A5A1F_;F_;Fz;Fc';").
Proof.
  intros c' z Hc' Hz Hc. pose proof BLK as (_ & _ & _ & _ & _ & _ & _ & B8 & _). destruct GEO as (_ & _ & SB1 & _ & _ & _ & ST & _).
  pose proof CZI as (_ & _ & _ & _ & _ & _ & _ & _ & I9 & _). specialize (I9 c' Hc').
  destruct (CHGE z Hc) as [K|[K|[K|K]]].
  - destruct (CZN z K) as [K'|K']; [clear -Hz K' I9 B8; lia | clear -Hz K' SB1 Hc'; nia].
  - unfold TZ in K. clear -Hz K ST Hc'. nia.
  - destruct K as [HNE K]. pose proof (QBF HNE) as (_ & _ & Q3 & _ & (x & X1 & X2 & XM & X3) & M2 & M3 & _). unfold kQuarantineBatchSize in K.
    assert (CC : c' = 24 \/ c' + 1 <= 24 \/ 25 <= c') by (clear -Hc'; lia). clear -Hz K Q3 X1 X2 X3 M2 M3 CC. destruct CC as [->|[CC|CC]]; nia.
  - destruct K as [HQ K]. pose proof (NBF HQ) as (_ & _ & N3 & _ & N5 & N6 & N7 & N8' & _).
    assert (CC : c' = 24 \/ c' + 1 <= 24 \/ 25 <= c') by (clear -Hc'; lia). clear -Hz K N3 N5 N6 N7 N8' CC. destruct CC as [->|[CC|CC]]; nia.
Qed.

Lemma CHF : ltac2:(tb__ "0|0|
S0S66Vq;VA;Vp;Vn;R1A5S2S41Sa5VG;R2A2S4aA3F_;Fz;").
Proof.
  intros z Hc. pose proof HA as (HG & _). pose proof BLK as (_ & _ & _ & _ & B5 & _ & B7 & B8 & _).
  destruct (CHGE z Hc) as [K|[K|[K|K]]].
  - destruct K as [K|K]; [exact (proj1 (proj2 (proj2 (proj2 (CZA z ltac:(clear -K; lia)))))) | exact (proj2 (CZS z K))].
  - unfold TZ in K. apply fs_footb_T; [exact HG | unfold T in K |- *; clear -K; lia].
  - destruct K as [HNE K]. pose proof (QBF HNE) as (_ & _ & Q3 & _ & (x & X1 & X2 & XM & X3) & M2 & M3 & _). unfold kQuarantineBatchSize in K.
    apply fs_footb_space; [exact HG | rewrite kSpaceSize_val; unfold SB in *; clear -K Q3 X1 X2 X3 M2 M3; lia].
  - destruct K as [HQ K]. pose proof (NBF HQ) as (_ & _ & N3 & _ & N5 & N6 & N7 & N8' & _).
    apply fs_footb_space; [exact HG | rewrite kSpaceSize_val; unfold SB in *; clear -K N3 N5 N6 N7 N8'; lia].
Qed.
Lemma AGm : ltac2:(tb__ "0|0|
S0S3S66Vq;VA;Vp;Vn;R1A5A1S2S49Sc2Q8A1A1Vm3;R2A1VmE;R2A1A3F_;Fz;").
Proof. intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity | exact (VO z Hz)]. Qed.
Lemma CHm : ltac2:(tb__ "0|0|
S0S66Vq;VA;Vp;Vn;R1A5S2S49Sc2Q8A1A1Vm3;R2A1Vv3;R2A1A3F_;Fz;").
Proof. intros z Hz. unfold m3. apply maskv_out. exact (CHF z Hz). Qed.
Lemma CELL : ltac2:(tb__ "0|0|
S0S47S0S47SccR1R3A2S3S66Vq;VA;Vp;Vn;S9R5SfR2A1A2A5A1F_;Fk;S51VmE;S52R4R3R2A3A2S51Vm3;S52R5R4R3A3A2F_;F_;Fv;Fw;Fa;").
Proof. intros a w v Hn Hc. eapply cell_ok_agree; [|exact Hc]. cbn [c_addr c_w]. intros k Hk. apply AGm. exact (Hn k Hk). Qed.
Lemma CELL3 : ltac2:(tb__ "0|0|
S0S47S0S47SccR1R3A2S66Vq;VA;Vp;Vn;S9R5SfR2A1A2A5F_;Fk;S51Vv3;S52R4R3R2A3A2S51Vm3;S52R5R4R3A3A2F_;F_;Fv;Fw;Fa;").
Proof. intros a w v Hn Hc. eapply cell_ok_agree; [|exact Hc]. cbn [c_addr c_w]. intros k Hk. apply CHm. exact (Hn k Hk). Qed.
Lemma PRESX : ltac2:(tb__ "0|0|
S0S0S57VmE;R2R1A3S57Vm3;R3R2A3F_;Fhi;Flo;").
Proof.
  intros lo hi Hp z Hz. destruct (CHGD z) as [Hc|Hnc].
  - destruct (PRES z Hc) as [b' Hb]. exists b'. rewrite (CHm z Hc). exact Hb.
  - rewrite (AGm z Hnc). exact (Hp z Hz).
Qed.

Lemma PRESB : ltac2:(tb__ "0|0|
S0S0SaeVmE;R2R1S1eVA;A1A4SaeVm3;R3R2S1eVA';A1A4F_;Fhi;Flo;").
Proof.
  intros lo hi Hp z Hz Hn. destruct (CHGD z) as [Hc|Hnc].
  - destruct (PRES z Hc) as [b' Hb]. exists b'. rewrite (CHm z Hc). exact Hb.
  - rewrite (AGm z Hnc). apply (Hp z Hz). intros (b & m & Hin & Hb). rewrite HLV in Hin. apply in_app_or in Hin as [Hin|[E|Hin]].
    + apply Hn. exists b, m. split; [change (aa_live A') with (l1 ++ l2); apply in_or_app; left; exact Hin | exact Hb].
    + inversion E; subst b m. apply Hnc. pose proof BLK as (_ & _ & _ & _ & B5 & _).
      destruct QDEC as [HQ|HQ]; [apply (proj2 (CHG_QA HQ _)) | apply (proj2 (CHG_QB HQ _))]; left; unfold chg_common; clear -Hb B5; lia.
    + apply Hn. exists b, m. split; [change (aa_live A') with (l1 ++ l2); apply in_or_app; right; exact Hin | exact Hb].
Qed.
Lemma CELLr : ltac2:(tb__ "0|0|
S0S0S0S47S0S8R5R3A2S8S9R4SfR3A1A2R5A2S0S1S8R8R1A2SaR1R7A2A2S3S66Vq;VA;Vp;Vn;R2A5A1F_;Fz;S51VmE;S52R6R5R4A3A2S51Vm3;S52R7R6R5A3A2F_;F_;F_;F_;Fv;Fw;Fa;Fhi;Flo;").
Proof. intros lo hi a w v H1 H2 Hn Hc. apply CELL; [|exact Hc]. intros k Hk. apply Hn. lia. Qed.

Lemma T_pp : ltac2:(tb__ "0|7|
S0S0S0S0S0S0S0S1S8Z1M0R7A2S8R7Z1eM1A2A2S1S8G0R5A2S8R5G1A2A2S8Z0M2R8A2S8G2R6A2S8S9ScZ10M3RaA2R9A2SbSdZ2M4Z20A2SdG4Z1dA2A2M5A2S8S9ScG3R8A2R7A2G5A2S8G3RbA2S8G3R9A2S2S0SeRdG3A2G2A3S2S0SeRbG3A2G2A3S2S0SeScG3R10A2RfA2G2A3S2S0SeScG3ReA2RdA2G2A3S2S0R13R10A3M6S2S0R12RfA3F_;S4S3S2S0R14R11A3A1S3G6A1A2Sc4VSB;R15ScG3R14A2R13RfA5Sc4VSB;R13ScG3R12A2R11R10A5S5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fz;Fs2;Fx2;Fc2;Fs1;Fx1;Fc1;").
Proof.
  intros c1 x1 s1 c2 x2 s2 z C1 C2 X1 X2 E1 E2 S1 S2 M1 M2 A1 A2 ES NE Z1 Z2.
  destruct GEO as (_ & _ & SB1 & SB2 & SB8 & _ & _ & _ & _ & TG & _).
  assert (SEP : c1 <> c2 \/ 16 * x1 + s1 <= 16 * x2 \/ 16 * x2 + s2 <= 16 * x1).
  { destruct NE as [NE|NE]; [left; exact NE|]. destruct (Z.eq_dec c1 c2) as [EC|NC]; [right | left; exact NC].
    specialize (ES EC). subst s2. assert (NE16 : 16 * x1 <> 16 * x2) by (clear -NE; lia).
    destruct (mod0_apart (16 * x1) (16 * x2) s1 ltac:(clear -S1; lia) A1 A2 NE16); [left | right]; assumption. }
  refine (czone_disj SB c1 c2 (16 * x1) (16 * x2) s1 s2 z SB1 _ SB8 _ _ _ E1 _ E2 _ _ _ _ _ _ SEP Z1 Z2);
    clear -C1 C2 X1 X2 S1 S2 TG SB2 M1 M2 E1 E2; lia.
Qed.

Lemma T_pm : ltac2:(tb__ "0|5|
S0S0S0S15S0S1S8Z1R5A2S8R5Z1eA2A2S8Z0M0R5A2S8S9ScZ10M1R6A2R5A2SbSdZ2M2Z20A2SdG2Z1dA2A2A2S8G1R6A2S2S0SeR7G1A2G0A3S4S8S9S18R7A1M3S20R7A1A2VSB;A2S8S9S9VSB;SdG2Z25A2A2Z1000A2G3A2A2S8G0S18R8A1A2S8G0S20R9A1A2S8S9S18RaA1S20RaA1A2S21VG;A1A2S4S8S9S18RbA1M4S20RbA1A2Z7fff7000A2S8Z10007fff8000G4A2A2Sc4VSB;RfScG1ReA2RdRbA5S84RdRcA2S5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fz;Fch;Fs1;Fx1;Fc1;").
Proof.
  intros c1 x1 s1 ch z C1 X1 E1 S1 M1 OFF MB0 MS0 MT WB Z1 Z2.
  destruct GEO as (_ & _ & SB1 & SB2 & SB8 & _ & _ & _ & _ & TG & _).
  assert (CE : cz_env SB c1 x1 s1 (topG G)) by (unfold cz_env; clear -C1 X1 E1 S1 M1 SB1 SB2 SB8 TG; lia).
  apply (czone_env SB c1 x1 s1 (topG G) z CE) in Z1. unfold SHADOW_OFF in Z1. unfold mapzone in Z2.
  destruct Z1 as [[A1 A2]|[A1 A2]]; destruct Z2 as [B1|B1].
  - clear -A1 B1 OFF C1. nia.
  - pose proof (Sh_lt_HSE (sc_map_beg ch + sc_map_size ch) ltac:(clear -MT TG; lia)) as SL. unfold HIGH_SHADOW_END in SL. clear -A2 B1 SL. lia.
  -
    clear -A2 B1 WB. lia.
  - rewrite <- !Z.add_assoc in A1. destruct OFF as [O|O].
    + pose proof (Sh_mono (sc_map_beg ch + sc_map_size ch) SB O) as SM. clear -A1 B1 SM C1. nia.
    + pose proof (Sh_mono (SB + (2 ^ 37 + 4096)) (sc_map_beg ch) ltac:(clear -O; lia)) as SM. rewrite (Sh_SB SB (2 ^ 37 + 4096) SB8) in SM.
      change ((2 ^ 37 + 4096) / 8) with 17179869696 in SM. clear -A1 B1 SM C1. nia.
Qed.

Lemma T_mm : ltac2:(tb__ "0|a|
S15S15S0S4S8S9S18R3A1M0S20R3A1A2S18R2A1M1A2S8S9G1S20R2A1A2G0A2A2S2S0SeS18R4A1Z1000M2A2Z0M3A3M4G4S2S0SeS20R6A1G2A2G3A3M5G5S8G3S18R8A1A2M6G6S8S9S18RaA1S20RaA1A2S21VG;A1A2M7G7S4S8S9S18RcA1M8S20RcA1A2Z7fff7000A2S8Z10007fff8000G8A2A2M9G9S84ReRcA2S84ReRdA2S5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fz;Fch2;Fch1;").
Proof.
  intros ch1 ch2 z AP A1 A2 S1 S2 P1 P2 T1 T2 W1 W2 Z1 Z2. destruct GEO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TG & _).
  pose proof (Sh_lt_HSE (sc_map_beg ch1 + sc_map_size ch1) ltac:(clear -T1 TG; lia)) as L1.
  pose proof (Sh_lt_HSE (sc_map_beg ch2 + sc_map_size ch2) ltac:(clear -T2 TG; lia)) as L2. unfold HIGH_SHADOW_END in L1, L2.
  assert (SL1 : 2147450880 <= Sh (sc_map_beg ch1)) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos (sc_map_beg ch1) 8 P1 ltac:(lia)); lia).
  assert (SL2 : 2147450880 <= Sh (sc_map_beg ch2)) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos (sc_map_beg ch2) 8 P2 ltac:(lia)); lia).
  unfold mapzone in Z1, Z2. destruct Z1 as [B1|B1]; destruct Z2 as [B2|B2].
  - clear -AP B1 B2. lia.
  - clear -B1 B2 W1 L2 SL2. lia.
  - clear -B1 B2 W2 L1 SL1. lia.
  - destruct AP as [O|O]; [pose proof (Sh_mono _ _ O) as SM | pose proof (Sh_mono _ _ O) as SM]; clear -B1 B2 SM; lia.
Qed.

Lemma NCH_K_slot : ltac2:(tb__ "0|6|
S0S0S0S1S8Z1R3A2S8R3Z1eA2A2S8Z0M0R3A2S8S9ScZ10M1R4A2S8eR5A1A2SbSdZ2M2Z20A2M3SdG2Z1dA2A2A2S2S0SeScG1R5A2S8eR6A1A2G0A3S2S41S8fVn;A1S44A3S2S0S94S95Vn;A1A1R8A3S3S2S0R8S10SbSbVp;S8dVn;A1A2S9VSB;ScR9G3A2A2A2G1A2A3A1F_;F_;S3S2S40S13A1S17VA;A1S43S13A1A3A1S2S0R9Z18M4A3S3S2S0S9S9VSB;ScG4G3A2A2ScG1R9A2M5A2VqbF;A3A1F_;F_;S3S2S63Vq;S64A3A1S2S0RaG4A3S3S2S0RaSc8VA;A1A3A1F_;F_;Sc4VSB;RaG5S8eRaA1R8A5S3S66Vq;VA;Vp;Vn;R9A5A1F_;F_;F_;F_;F_;F_;F_;F_;Fz;Fx';Fc';").
Proof.
  intros c' x' z Hc' Hx' HE HM NP NB NN KZ Hc. pose proof (size_ok_all c' Hc') as [SZ1 SZ2].
  destruct GEO as (T1 & T2 & SB1 & SB2 & SB8 & _ & ST & TB & _ & TG & _).
  destruct (CHGE z Hc) as [K|[K|[K|K]]].
  - destruct (is_primary n) eqn:HP.
    + pose proof (KP HP) as KK. cbn zeta in KK. destruct KK as (CE & EO & O0 & OM & OA & M2 & M3 & IDin & CC & SZ & SZM & FIT & KC).
      set (c := ClassID (needed n)) in *. set (o := p - rz n - (SB + c * 2 ^ 32)) in *.
      refine (T_pp c' x' (Size c') c (o / 16) (Size c) z Hc' CC Hx' _ HE _ ltac:(clear -SZ1; lia) ltac:(clear -SZ; lia) SZ2 SZM HM _ _ _ KZ (KC z K)).
      * clear -O0 EO. lia.
      * clear -EO OA M2 M3. lia.
      * rewrite <- EO. exact OM.
      * intros ->. reflexivity.
      * destruct (Z.eq_dec c' c) as [EC|NC]; [right | left; exact NC]. intros EX. apply (NP eq_refl (eq_sym EC)). rewrite EX. unfold o. rewrite <- EC. reflexivity.
    + destruct (KS HP) as (i & ch & Hi & Hch & Eb & Esz & D6 & D8 & D12 & MB & WB & X1 & X2 & X3 & X4 & X6 & X7 & X5 & KC).
      pose proof BLK as (_ & _ & B3 & _). pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU.
      assert (MS0 : 0 <= sc_map_size ch) by (clear -D8 Esz RU B3; lia).
      exact (T_pm c' x' (Size c') ch z Hc' Hx' HE ltac:(clear -SZ1; lia) SZ2 X1 ltac:(clear -MB; lia) MS0 D12 WB KZ (KC z K)).
  - unfold TZ in K. assert (CE : cz_env SB c' x' (Size c') (topG G)) by (unfold cz_env; clear -Hc' Hx' HE SZ1 SZ2 SB1 SB2 SB8 TG; lia).
    apply (czone_env SB c' x' (Size c') (topG G) z CE) in KZ. unfold SHADOW_OFF in KZ. clear -K KZ ST TB Hc'. nia.
  - destruct K as [HNE K]. pose proof (QBF HNE) as (_ & _ & Q3 & _ & (xb & X1 & X2 & XM & X3) & M2 & M3 & _). unfold kQuarantineBatchSize in K.
    assert (XM' : (16 * xb) mod 8192 = 0) by (replace (16 * xb) with (xb mod 512 * 16 + (xb / 512) * 8192) by (pose proof (Z.div_mod xb 512); clear -H; lia); rewrite XM; apply Z_mod_mult).
    refine (T_pp c' x' (Size c') 24 xb 8192 z Hc' ltac:(clear; lia) Hx' X2 HE ltac:(clear -X3 M2 M3; lia) ltac:(clear -SZ1; lia) ltac:(clear; lia) SZ2 eq_refl HM XM' _ _ KZ _).
    + intros ->. reflexivity.
    + destruct (Z.eq_dec c' 24) as [EC|NC]; [right | left; exact NC]. intros EX. apply (NB HNE EC). rewrite EX, X1. reflexivity.
    + unfold czone. cbn zeta. left. rewrite <- X1. clear -K. lia.
  - destruct K as [HQ K]. pose proof (NBF HQ) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8' & NM & _).
    refine (T_pp c' x' (Size c') 24 (top24 A) 8192 z Hc' ltac:(clear; lia) Hx' ltac:(clear -N2; lia) HE ltac:(clear -N6 N7 N8'; lia) ltac:(clear -SZ1; lia) ltac:(clear; lia) SZ2 eq_refl HM NM _ _ KZ _).
    + intros ->. reflexivity.
    + destruct (Z.eq_dec c' 24) as [EC|NC]; [right; exact (NN HQ EC) | left; exact NC].
    + unfold czone. cbn zeta. left. rewrite <- N3. clear -K. lia.
Qed.

Lemma NCH_K_map : ltac2:(tb__ "0|0|
S47S15S0S2S49S15A1S5eS15S28VA;A1R3A3S4bS15R2A2A3S2S41S8fVn;A1S4aA3S3S2S0Vp;S9S9S18R4A1Z1000A2Z800A2A3A1F_;S84R4R3A2S3S66Vq;VA;Vp;Vn;R4A5A1F_;F_;F_;Fz;Fch';Fj;").
Proof.
  intros j ch' z Hj NP KZ Hc. destruct GEO as (T1 & T2 & SB1 & SB2 & SB8 & _ & ST & TB & _ & TG & _).
  pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _). destruct HRest as (_ & _ & _ & (HS & _) & _). destruct HI3 as (_ & _ & SEC3 & _). fold G in SEC3.
  pose proof (HS j ch' Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D10, D12.
  pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; clear -D8 D9; lia)) as MB. destruct D10 as (_ & _ & _ & _ & WB).
  unfold PG, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in D6, D7, D8, MB, WB.
  destruct (SEC3 j ch' Hj) as (X1 & X2 & _ & _ & X5 & _). fold SB T in X1, X2. rewrite kSpaceSize_val in X1.
  destruct (CHGE z Hc) as [K|[K|[K|K]]].
  - destruct (is_primary n) eqn:HP.
    + pose proof (KP HP) as KK. cbn zeta in KK. destruct KK as (CE & EO & O0 & OM & OA & M2 & M3 & IDin & CC & SZ & SZM & FIT & KC).
      set (c := ClassID (needed n)) in *. set (o := p - rz n - (SB + c * 2 ^ 32)) in *. pose proof (size_ok_all c CC) as [SZ1 SZ2].
      refine (T_pm c (o / 16) (Size c) ch' z CC _ _ ltac:(clear -SZ1; lia) SZ2 X1 ltac:(clear -MB; lia) ltac:(clear -D8 D9; lia) D12 WB (KC z K) KZ).
      * clear -O0 EO. lia.
      * clear -EO OA M2 M3. lia.
    + destruct (KS HP) as (i & ch & Hi & Hch & Eb & Esz & C6 & C8 & C12 & CB & CWB & Y1 & Y2 & Y3 & Y4 & Y6 & Y7 & Y5 & KC).
      assert (NE : i <> j) by (intros <-; rewrite Hi in Hj; injection Hj as E; subst ch'; exact (NP eq_refl Eb)).
      refine (T_mm ch ch' z (Y5 j ch' Hj NE) C6 D6 _ D7 ltac:(clear -CB; lia) ltac:(clear -MB; lia) C12 D12 CWB WB (KC z K) KZ).

      pose proof (HS i ch Hi) as (_ & _ & _ & _ & _ & _ & E7 & _). exact E7.
  - unfold TZ in K. unfold mapzone in KZ. destruct KZ as [KZ|KZ]; [clear -K KZ X2; lia|].
    assert (SL : 2147450880 <= Sh (sc_map_beg ch')) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos (sc_map_beg ch') 8 ltac:(clear -MB; lia) ltac:(clear; lia)); clear -H; lia).
    pose proof (Sh_lt_HSE (sc_map_beg ch' + sc_map_size ch') ltac:(clear -D12 TG; lia)) as SH. unfold HIGH_SHADOW_END in SH. clear -K KZ SL SH TB. lia.
  - destruct K as [HNE K]. pose proof (QBF HNE) as (_ & _ & Q3 & _ & (xb & Z1 & Z2 & ZM & Z3) & M2 & M3 & _). unfold kQuarantineBatchSize in K.
    refine (T_pm 24 xb 8192 ch' z ltac:(clear; lia) Z2 ltac:(clear -Z3 M2 M3; lia) ltac:(clear; lia) eq_refl X1 ltac:(clear -MB; lia) ltac:(clear -D8 D9; lia) D12 WB _ KZ).
    unfold czone. cbn zeta. left. rewrite <- Z1. clear -K. lia.
  - destruct K as [HQ K]. pose proof (NBF HQ) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8' & NM & _).
    refine (T_pm 24 (top24 A) 8192 ch' z ltac:(clear; lia) ltac:(clear -N2; lia) ltac:(clear -N6 N7 N8'; lia) ltac:(clear; lia) eq_refl X1 ltac:(clear -MB; lia) ltac:(clear -D8 D9; lia) D12 WB _ KZ).
    unfold czone. cbn zeta. left. rewrite <- N3. clear -K. lia.
Qed.

Definition csA (c : Z) : class_state := ltac2:(tb__ "0|0|
Sa1S16S1cVA;A1Vc;S1bA4").
Lemma CND : ltac2:(tb__ "0|1|
S0S1S8Z1R1A2S8R1Z1eA2A2SbfS0S3fS0S23S82R2A1M0A1S3fS0S1aG0A1S3fS0Sa4VG;VA;R2A3S7bVG;S77VA;A1R2A3A3A3A3A2F_;Fc;").
Proof.
  intros c Hc. pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & HPR & _). destruct HPR as (_ & _ & _ & HCR).
  pose proof (HCR c Hc) as Cc. destruct Cc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). exact ND.
Qed.
Lemma LIVE_SPLIT : ltac2:(tb__ "0|3|
S0S2S40S0A1M0Sa4VG;VA;R1A3S3fS0S69VG;R1Vl1;A3S3fS0S41G0L_;S67R1S46S0S0Vp;Vn;A4M1A2S45S0S68VG;R1G1A3S43S0A1M2A3G2X41x2S69VG;R1Vl2;A3A3A3A3Fc;").
Proof. intros c. rewrite live_ids_LI, HLV, LI_app, LI_cons. reflexivity. Qed.

Lemma ND_L : ltac2:(tb__ "0|2|
S0S1S8Z1R1A2S8R1Z1eA2A2SbfS0S3fS0S69VG;R2Vl1;A3S3fS0S41S40S0A1L_;S67R2S46S0S0Vp;Vn;A4M0A2S45S0S68VG;R2G0A3S43S0A1M1A3G1X41x2S69VG;R2Vl2;A3A3A3A2F_;Fc;").
Proof. intros c Hc. rewrite <- LIVE_SPLIT. exact (ND_app_l _ _ (ND_app_r _ _ (ND_app_r _ _ (CND c Hc)))). Qed.
Lemma ND_Q : ltac2:(tb__ "0|1|
S0S1S8Z1R1A2S8R1Z1eA2A2SbfS0S3fS0S6aVG;R2S78S77VA;A1M0A1A3S41S40S0A1L_;S11R2Z18A2S7fS13S0S79VG;A1G0A4S43S0A1X41x2A3A2F_;Fc;").
Proof. intros c Hc. rewrite <- q_ids_QI. exact (ND_app_r _ _ (ND_app_r _ _ (ND_app_r _ _ (CND c Hc)))). Qed.

Lemma D_live_p : ltac2:(tb__ "0|2|
S0S42S0S0A2M0S1S8Z1R2A2S8R2Z1eA2A2S5cG0R2S3fG0Vl1;Vl2;A3A3S2S41S67R4R3A2S44A3S2S41S67R5S46S0S0Vp;Vn;A4M1A2S44A3S3S2S0S68VG;R6R5A3S68VG;R6G1A3A3A1F_;F_;F_;F_;Fb;Fc;").
Proof.
  intros c b Hc Hin Hb Hp. pose proof (ND_L c Hc) as ND. rewrite Hp in ND.
  apply (ND_mid (LI G c l1) (LI G c l2)); [exact ND|]. apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left|right]; apply LI_in; assumption.
Qed.

Lemma D_item_p : ltac2:(tb__ "0|2|
S0S42S0S0A2M0S1S8Z1R2A2S8R2Z1eA2A2S5cG0R2S78S77VA;A1A1A3S2S41S67R4R3A2S44A3S2S41S67R5S46S0S0Vp;Vn;A4M1A2S44A3S3S2S0S7aVG;R5A2S68VG;R6G1A3A3A1F_;F_;F_;F_;Fit;Fc;").
Proof.
  intros c it Hc Hin Hb Hp E. pose proof (CND c Hc) as ND.
  apply (ND_app_disj (live_ids G A c) (q_ids G (qall A) c) (idf G c (p, n)) (it_id G it) (ND_app_r _ _ (ND_app_r _ _ ND))).
  - rewrite LIVE_SPLIT, Hp. apply in_or_app. right. left. reflexivity.
  - rewrite q_ids_QI. apply in_or_app. left. apply QI_in; assumption.
  - symmetry. exact E.
Qed.

Lemma D_batch_p : ltac2:(tb__ "0|2|
S13S5cS13R1S77VA;A1A3S2S41S67Z18M0S46S0S0Vp;Vn;A4M1A2S44A3S3S2S0S79VG;R3A2S68VG;G0G1A3A3A1F_;F_;Fqb;").
Proof.
  intros qb Hin Hp E. pose proof (CND 24 ltac:(lia)) as ND.
  apply (ND_app_disj (live_ids G A 24) (q_ids G (qall A) 24) (idf G 24 (p, n)) (qb_id G qb) (ND_app_r _ _ (ND_app_r _ _ ND))).
  - rewrite LIVE_SPLIT, Hp. apply in_or_app. right. left. reflexivity.
  - rewrite q_ids_QI. apply in_or_app. right. rewrite Z.eqb_refl. apply in_map_iff. exists qb. split; [reflexivity | exact Hin].
  - symmetry. exact E.
Qed.

Lemma D_cache_p : ltac2:(tb__ "0|1|
S0S0S1S8Z1R2A2S8R2Z1eA2A2S5cS0R2S1aS82R3A1A1A3S2S41S67R4S46S0S0Vp;Vn;A4M0A2S44A3S3S2S0R4S68VG;R5G0A3A3A1F_;F_;F_;Fx;Fc;").
Proof.
  intros c x Hc Hin Hp. pose proof (CND c Hc) as ND.
  apply (ND_app_disj (cs_cache (csA c)) (live_ids G A c ++ q_ids G (qall A) c) x (idf G c (p, n)) (ND_app_r _ _ ND) Hin).
  apply in_or_app. left. rewrite LIVE_SPLIT, Hp. apply in_or_app. right. left. reflexivity.
Qed.

Lemma D_item_batch : ltac2:(tb__ "0|2|
S42S0S0A2M0S13S5cG0R2S78S77VA;A1M1A1A3S2S41S67Z18R3A2S44A3S5cS13R3G1A3S3S2S0S7aVG;R5A2S79VG;R4A2A3A1F_;F_;F_;Fqb;Fit;").
Proof.
  intros it qb Hit Hb Hqb. pose proof (ND_Q 24 ltac:(lia)) as ND. rewrite Z.eqb_refl in ND.
  apply (ND_app_disj _ _ _ _ ND); [apply QI_in; assumption | apply in_map_iff; exists qb; split; [reflexivity | exact Hqb]].
Qed.

Lemma D_item_cache : ltac2:(tb__ "0|1|
S0S42S0S0A2M0S0S1S8Z1R3A2S8R3Z1eA2A2S5cG0R3S78S77VA;A1A1A3S2S41S67R5R4A2S44A3S5cS0R4S1aS82R6A1A1A3S3S2S0R5S7aVG;R6A2A3A1F_;F_;F_;F_;Fx;Fit;Fc;").
Proof.
  intros c it x Hc Hit Hb Hx. pose proof (CND c Hc) as ND.
  apply (ND_app_disj (cs_cache (csA c)) (live_ids G A c ++ q_ids G (qall A) c) x (it_id G it) (ND_app_r _ _ ND) Hx).
  apply in_or_app. right. rewrite q_ids_QI. apply in_or_app. left. apply QI_in; assumption.
Qed.
Lemma D_batch_cache : ltac2:(tb__ "0|0|
S13S0S5cS13R2S77VA;A1A3S5cS0R2S1aS82Z18A1A1A3S3S2S0R3S79VG;R4A2A3A1F_;F_;Fx;Fqb;").
Proof.
  intros qb x Hqb Hx. pose proof (CND 24 ltac:(lia)) as ND.
  apply (ND_app_disj (cs_cache (csA 24)) (live_ids G A 24 ++ q_ids G (qall A) 24) x (qb_id G qb) (ND_app_r _ _ ND) Hx).
  apply in_or_app. right. rewrite q_ids_QI. apply in_or_app. right. rewrite Z.eqb_refl. apply in_map_iff. exists qb. split; [reflexivity | exact Hqb].
Qed.
Lemma D_live_cache : ltac2:(tb__ "0|1|
S0S42S0S0A2M0S0S1S8Z1R3A2S8R3Z1eA2A2S5cG0R3S3fG0Vl1;Vl2;A3A3S2S41S67R5R4A2S44A3S5cS0R4S1aS82R6A1A1A3S3S2S0R5S68VG;R7R6A3A3A1F_;F_;F_;F_;Fx;Fb;Fc;").
Proof.
  intros c b x Hc Hin Hb Hx. pose proof (CND c Hc) as ND.
  apply (ND_app_disj (cs_cache (csA c)) (live_ids G A c ++ q_ids G (qall A) c) x (idf G c b) (ND_app_r _ _ ND) Hx).
  apply in_or_app. left. rewrite LIVE_SPLIT. apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left | right; apply in_or_app; right]; apply LI_in; assumption.
Qed.
Lemma D_live_batch : ltac2:(tb__ "0|2|
S42S0S0A2M0S13S5cG0R2S3fG0Vl1;Vl2;A3A3S2S41S67Z18M1R3A2S44A3S5cS13R3S77VA;A1A3S3S2S0S68VG;G1R5A3S79VG;R4A2A3A1F_;F_;F_;Fqb;Fb;").
Proof.
  intros b qb Hin Hb Hqb. pose proof (CND 24 ltac:(lia)) as ND.
  apply (ND_app_disj (live_ids G A 24) (q_ids G (qall A) 24) (idf G 24 b) (qb_id G qb) (ND_app_r _ _ (ND_app_r _ _ ND))).
  - rewrite LIVE_SPLIT. apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left | right; apply in_or_app; right]; apply LI_in; assumption.
  - rewrite q_ids_QI. apply in_or_app. right. rewrite Z.eqb_refl. apply in_map_iff. exists qb. split; [reflexivity | exact Hqb].
Qed.
Lemma D_live_item : ltac2:(tb__ "0|1|
S0S42S0S0A2M0G0S1S8Z1R3A2S8R3Z1eA2A2S5cG0R3S3fG0Vl1;Vl2;A3A3S2S41S67R5R4A2S44A3S5cG0R4S78S77VA;A1A1A3S2S41S67R7R5A2S44A3S3S2S0S68VG;R8R7A3S7aVG;R6A2A3A1F_;F_;F_;F_;F_;Fit;Fb;Fc;").
Proof.
  intros c b it Hc Hin Hb Hit Hbi. pose proof (CND c Hc) as ND.
  apply (ND_app_disj (live_ids G A c) (q_ids G (qall A) c) (idf G c b) (it_id G it) (ND_app_r _ _ (ND_app_r _ _ ND))).
  - rewrite LIVE_SPLIT. apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left | right; apply in_or_app; right]; apply LI_in; assumption.
  - rewrite q_ids_QI. apply in_or_app. left. apply QI_in; assumption.
Qed.

Lemma D_batches : ltac2:(tb__ "0|1|
S13S13S40S13A1M0G0G0S2G0S77VA;A1S3fS13R3S45S13R5S3fS13R2S45S13R4R1A3A3A3A3A3S3S2S0S14R6A1S14R5A1A3A1F_;FlC;FlB;FlA;Fq2;Fq1;").
Proof.
  intros q1 q2 lA lB lC E EQ. pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & HQR & _).
  destruct HQR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & QND). change (aa_q_thread A ++ aa_q_global A) with (qall A) in QND. rewrite E in QND.
  rewrite map_app in QND. cbn [map] in QND. rewrite map_app in QND. cbn [map] in QND.
  refine (ND_mid (map qb_addr lA) (map qb_addr lB ++ qb_addr q2 :: map qb_addr lC) (qb_addr q1) (qb_addr q2) QND _ (eq_sym EQ)).
  apply in_or_app. right. apply in_or_app. right. left. reflexivity.
Qed.

Lemma DS_live_p : ltac2:(tb__ "0|1|
S0S0S5cS42S0S0A2M0S46S0S0R2R1A4S3fG0Vl1;Vl2;A3A3S2S41S8fR2A1S4aA3S2S41S8fVn;A1S4aA3S3S2S0R5Vp;A3A1F_;F_;F_;Fm;Fb;").
Proof.
  intros b m Hin Hm Hp E. subst b. pose proof HA as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & _ & _ & _ & ND3 & _).
  rewrite HLV in ND3. rewrite List.filter_app in ND3. cbn [List.filter snd negb] in ND3. rewrite Hp in ND3. cbn [negb] in ND3.
  rewrite map_app in ND3. cbn [map fst] in ND3.
  set (A1 := map fst (List.filter (fun bn : Z * Z => negb (is_primary (snd bn))) l1)) in ND3.
  set (A2 := map fst (List.filter (fun bn : Z * Z => negb (is_primary (snd bn))) l2)) in ND3.
  set (QQ := map fst (List.filter (fun it : Z * Z => negb (is_primary (snd it))) (qitems (qall A)))) in ND3.
  assert (ND : NoDup (A1 ++ p :: (A2 ++ QQ))) by (change (A1 ++ p :: (A2 ++ QQ)) with (A1 ++ (p :: A2) ++ QQ); rewrite (app_assoc A1 (p :: A2) QQ); exact ND3).
  apply (ND_mid A1 (A2 ++ QQ) p p ND); [|reflexivity].
  apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left|right; apply in_or_app; left]; apply in_map_iff; exists (p, m); (split; [reflexivity|]); apply List.filter_In; (split; [exact Hin | cbn [snd]; rewrite Hm; reflexivity]).
Qed.
Lemma DS_item_p : ltac2:(tb__ "0|0|
S0S0S5cS42S0S0A2S46S0S0R2R1A4S78S77VA;A1A1A3S2S41S8fR2A1S4aA3S2S41S8fVn;A1S4aA3S3S2S0R5Vp;A3A1F_;F_;F_;Fm;Fu;").
Proof.
  intros u m Hin Hm Hp E. subst u. pose proof HA as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & _ & _ & _ & ND3 & _).
  apply (ND_app_disj _ _ p p ND3); [| |reflexivity].
  - apply in_map_iff. exists (p, n). split; [reflexivity|]. apply List.filter_In. split; [exact HL | cbn [snd]; rewrite Hp; reflexivity].
  - apply in_map_iff. exists (p, m). split; [reflexivity|]. apply List.filter_In. split; [exact Hin | cbn [snd]; rewrite Hm; reflexivity].
Qed.

Lemma BLKSLOT : ltac2:(tb__ "0|7|
S0S0S0S8Z1M0R2A2S2S41S8fR3A1S44A3S2S0R3S94S95R4A1A1A3S8S92VSB;R4A2SbR6S8dR5A1A2A2S2S0SeSbSbR7S8dR6A1A2S92VSB;R5A2A2S8eR5A1A2Z0M1A3S8S9SbSbR8S8dR7A1A2S92VSB;R6A2A2S8eR6A1A2S22S82R6A1A1A2S10SbSbR9S8dR8A1A2S92VSB;R7A2A2Z10M2A2S0S1S1S8G0R8A2S8R8Z1eA2A2S1S8G1R1A2S1S2S0ScG2R1A2M3SbSbRaS8dR9A1A2S92VSB;R8A2A2A3S1S8S9G3S8eR8A1M4A2SbSdZ2M5Z20A2SdG5Z1dA2A2A2S1S2S0SeG3G4A2G1A3S1S2S0R1S68VG;R8S46S0S0RaR9A4A3A3S0S4S1S8SbRbS8dRaA1A2R1A2SaR1S9RbRaA2A2A2S1S8S90RbA1M6R1A2SaR1S9G6S10S9RaZ7A2Z8A2A2A2A2A2Sc4VSB;RaScG2R3A2S8eRaA1R2A5F_;Fz;A2A2A2A2A2A2Tx;F_;F_;F_;F_;F_;F_;Fc;Fm;Fb;").
Proof.
  intros b m c Hm HP Hc R1 R2 R3 x. destruct (needed_fits m Hm HP) as (F1 & F2 & F3). rewrite <- Hc in F1, F2.
  pose proof (size_ok_all c F2) as [SZ1 SZ2]. pose proof (rz_bound m) as RB. pose proof (rz_mod16 m) as RM. pose proof (N8_facts m Hm) as (N1 & N2 & N3 & N4).
  pose proof HA as (HG & HR & HF & HRest & _). destruct HRest as (_ & _ & HPR & _). destruct HPR as (_ & _ & _ & HCR).
  pose proof (HCR c F2) as Cc. destruct Cc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _). fold G in M2, M3. change (nthZ (aa_cls A) c cs_empty) with (csA c) in M2, M3.
  unfold kUserSpaceSize, kUserMapSize, kFreeArraySize, kRegionSize in M3.
  destruct GEO as (_ & _ & SB1 & SB2 & SB8 & _).
  set (o := b - rz m - region_beg SB c) in *.
  assert (O16 : o mod 16 = 0) by (rewrite <- (Z.mod_mod_divide o (Size c) 16) by (apply Z.mod_divide; [lia | exact SZ2]); rewrite R2; reflexivity).
  assert (EO : 16 * x = o) by (unfold x; pose proof (Z.div_mod o 16 ltac:(lia)); lia).
  split; [exact F2|]. split; [unfold x; apply Z.div_pos; lia|]. split; [exact EO|]. split; [clear -EO R3 M2 M3; lia|]. split; [rewrite EO; exact R2|].
  split; [unfold x, idf, o; cbn [fst snd]; reflexivity|].
  intros z Hz. unfold czone. cbn zeta. rewrite EO.
  assert (AB : SB + c * 2 ^ 32 + o = b - rz m) by (unfold o, region_beg, kRegionSize; lia). rewrite AB.
  assert (AB8 : (b - rz m) mod 8 = 0).
  { rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2; reflexivity). replace ((b - rz m) mod 16) with 0; [reflexivity|]. symmetry.
    rewrite <- AB. rewrite <- Zplus_mod_idemp_l. replace ((SB + c * 2 ^ 32) mod 16) with 0; [rewrite Z.add_0_l; exact O16|]. symmetry.
    rewrite <- Zplus_mod_idemp_l. destruct GEO as (_ & _ & _ & _ & _ & S16 & _).
    replace (SB mod 16) with 0; [rewrite Z.add_0_l; replace (c * 2 ^ 32) with (c * 2 ^ 28 * 16) by lia; apply Z_mod_mult|].
    symmetry. rewrite <- (Z.mod_mod_divide SB (2 ^ 16) 16) by (exists (2 ^ 12); reflexivity). rewrite S16. reflexivity. }
  destruct Hz as [Hz|Hz]; [left; clear -Hz RB F1 F3 N1; lia | right].
  replace b with (b - rz m + rz m) in Hz at 1 2 by lia. rewrite (Sh_SB (b - rz m) (rz m) AB8) in Hz.
  assert (D1 : rz m / 8 + (m + 7) / 8 <= Size c / 8).
  { destruct (proj1 (Z.mod_divide (rz m) 16 ltac:(lia)) RM) as [v Hv]. unfold N8 in N2, N4, N1, F3.
    destruct (proj1 (Z.mod_divide ((m + 7) / 8 * 8) 8 ltac:(lia)) N2) as [w Hw].
    rewrite Hv. replace (v * 16) with (2 * v * 8) by lia. rewrite Z.div_mul by lia.
    apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (m + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (m + 7) 8 ltac:(lia)). clear -Hv F1 F3 H H0. nia. }
  pose proof (Z.div_pos (rz m) 8 ltac:(lia) ltac:(lia)) as D0. clear -Hz D1 D0. lia.
Qed.

Lemma NCH_live : ltac2:(tb__ "0|2|
S0S0S0S5cS42S0S0A2M0S46S0S0R3R2A4S3fG0Vl1;Vl2;A3A3S4S1S8SbR4S8dR3A1A2R2A2SaR2S9R4R3A2A2A2S1S8S90R4A1M1R2A2SaR2S9G1S10S9R3Z7A2Z8A2A2A2A2A2S3S66Vq;VA;Vp;Vn;R3A5A1F_;F_;Fz;Fm;Fb;").
Proof.
  intros b m z Hin Hz. assert (HinA : In (b, m) (aa_live A)) by (rewrite HLV; apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin | right; right; exact Hin]).
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & _). pose proof (proj1 HRest b m HinA) as (L1 & _).
  destruct (is_primary m) eqn:HPm.
  - pose proof (live_slot A rhoE tp md b m HA HinA HPm) as LS. cbn zeta in LS. fold G in LS. destruct LS as (C1 & O0 & OM & OA & _ & _ & _ & _).
    fold SB in O0, OM, OA.
    pose proof (BLKSLOT b m (ClassID (needed m)) L1 HPm eq_refl ltac:(clear -O0; lia) OM OA) as BS. cbn zeta in BS. destruct BS as (_ & X0 & EX & XE & XM & EI & COV).
    assert (PCm : Pc (ClassID (needed m)) (b, m) = true) by (unfold Pc; cbn [snd]; rewrite HPm, Z.eqb_refl; reflexivity).
    refine (NCH_K_slot (ClassID (needed m)) ((b - rz m - region_beg SB (ClassID (needed m))) / 16) z C1 X0 XE XM _ _ _ (COV z Hz)).
    + intros HP EC E. apply (D_live_p (ClassID (needed m)) (b, m) C1 Hin PCm ltac:(unfold Pc; cbn [snd]; rewrite HP, EC, Z.eqb_refl; reflexivity)).
      rewrite <- EI. rewrite E. unfold idf. cbn [fst snd]. unfold region_beg, kRegionSize. reflexivity.
    + intros HNE EC EQ. pose proof (QBF HNE) as (QIN & _). rewrite EC in PCm, EI.
      apply (D_live_batch (b, m) (lastq A) Hin PCm ltac:(unfold qall; apply in_or_app; left; exact QIN)).
      rewrite <- EI. unfold qb_id, ptr_to_compact, kCompactPtrScale. change (qb_addr (lastq A)) with qbF. rewrite <- EQ. fold G SB. rewrite EC.
      replace (SB + 24 * 2 ^ 32 + 16 * ((b - rz m - region_beg SB 24) / 16) - region_beg SB 24) with (((b - rz m - region_beg SB 24) / 16) * 2 ^ 4) by (unfold region_beg, kRegionSize; lia).
      rewrite Z.shiftr_div_pow2, Z.div_mul by lia. reflexivity.
    + intros HQ EC EQ. destruct (NBF HQ) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HXin & _). rewrite EC in PCm, EI, EQ.
      apply (D_live_cache 24 (b, m) (top24 A) ltac:(lia) Hin PCm HXin).
      rewrite <- EQ. exact EI.
  - destruct HI3 as (_ & HPS & SEC3 & _). destruct (HPS b m HinA) as [Hp' | (ch & Hch & Eb & Esz)]; [rewrite HPm in Hp'; discriminate|].
    destruct (In_nth_error _ _ Hch) as [j Hj]. destruct HRest as (_ & _ & _ & (HS & _) & _). pose proof (HS j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & _).
    refine (NCH_K_map j ch z Hj _ _).
    + intros HP E. apply (DS_live_p b m Hin HPm HP). rewrite Eb, E. reflexivity.
    + unfold mapzone. pose proof (rz_bound m) as RB. unfold PG in D8, Eb.
      pose proof (round_up_ge m 8 ltac:(lia)) as RU.
      destruct Hz as [Hz|Hz]; [left; clear -Hz Eb Esz D8 RB RU L1; lia | right].
      pose proof (Sh_mono (sc_map_beg ch) b ltac:(clear -Eb; lia)) as SM1.
      assert (B8 : b mod 8 = 0).
      { rewrite Eb. unfold PG in D6. rewrite <- Zplus_mod_idemp_l, <- (Zplus_mod_idemp_l (sc_map_beg ch)). rewrite <- (Z.mod_mod_divide (sc_map_beg ch) 4096 8) by (exists 512; reflexivity). rewrite D6. reflexivity. }
      assert (SM2 : Sh b + (m + 7) / 8 <= Sh (sc_map_beg ch + sc_map_size ch)).
      { unfold Sh. destruct (proj1 (Z.mod_divide b 8 ltac:(lia)) B8) as [u Hu]. rewrite Hu. rewrite Z.div_mul by lia.
        pose proof (Z.div_le_mono (b + m + 7) (sc_map_beg ch + sc_map_size ch) 8 ltac:(lia) ltac:(clear -Eb Esz D8 RU L1; lia)) as DM.
        rewrite Hu in DM. replace (u * 8 + m + 7) with (m + 7 + u * 8) in DM by lia. rewrite Z.div_add in DM by lia. clear -DM. lia. }
      clear -Hz SM1 SM2. lia.
Qed.

Lemma ITEM : ltac2:(tb__ "0|9|
S13S42S0S0A2M0S5cS13R2S77VA;A1M1A3S5cG0R2S1fR3A1A3S4dS0S0R3A3S0S4cS0S0R4A3S0S1S5cG0R5S78G1A1A3S1S8Z1R1A2S1S8S9S93Z800M2A2R2A2S1S2S41S8fR1A1M3S44A3S94S95R2A1A1S0S1S8S92VSB;R1A2M4SbR4S8dR3A1A2M5A2S1S2S0SeSbG5G4A2M6S8eR1A1M7A2Z0A3S8S9G6G7A2S22S82R1A1A1A2A2A2Tc;F_;S2S41G3S4aA3S6S15S15S1S5cS15R1S28VA;A1A3S1S2S0R4S9S9S18R1A1Z1000M8A2G2A2A3S2S0S39R1A1S9S9cR3Z8A2G8A2A3A2A2Lch;A2F_;A2A2A2A2Tm;Tu;F_;F_;Fit;Fqb;").
Proof.
  intros qb it Hqb Hit u m. pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & HQR & _). destruct HQR as (QB & _).
  pose proof (proj1 (Forall_forall _ _) QB qb Hqb) as (_ & _ & _ & _ & _ & _ & R7 & _).
  destruct (In_nth_error _ _ Hit) as [i Hi]. destruct (R7 i it Hi) as [_ IQ].
  unfold q_item_ok in IQ. cbn zeta in IQ. fold G u m in IQ. destruct IQ as (J1 & J2 & _ & _ & _ & _ & _ & _ & J9 & J10 & _). fold SB in J9.
  split; [unfold qitems; apply in_flat_map; exists qb; split; assumption|].
  split; [exact J2|]. split; [exact J1|]. split; [|unfold PG in J10; exact J10].
  intros HP. exact (J9 HP).
Qed.

Lemma NCH_item : ltac2:(tb__ "0|4|
S13S42S0S0A2M0S0S5cS13R3S77VA;A1A3S5cG0R3S1fR4A1A3S4S1S8SbS4dS0S0R4A3M1S8dS4cS0S0R4A3M2A1A2R3A2SaR3G1A2A2S1S8S90G1A1M3R3A2SaR3S9G3S10S9G2Z7A2Z8A2A2A2A2A2S3S66Vq;VA;Vp;Vn;R4A5A1F_;F_;F_;Fz;Fit;Fqb;").
Proof.
  intros qb it z Hqb Hit Hz. destruct (ITEM qb it Hqb Hit) as (IIN & I2 & I1 & IP & IS). destruct it as [u m]. cbn [fst snd] in *.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & _).
  destruct (is_primary m) eqn:HPm.
  - destruct (IP eq_refl) as (R1 & R2 & R3).
    pose proof (BLKSLOT u m (ClassID (needed m)) I2 HPm eq_refl R1 R2 R3) as BS. cbn zeta in BS. destruct BS as (C1 & X0 & EX & XE & XM & EI & COV).
    assert (PCm : Pc (ClassID (needed m)) (u, m) = true) by (unfold Pc; cbn [snd]; rewrite HPm, Z.eqb_refl; reflexivity).
    assert (EIT : it_id G (u, m) = (u - rz m - region_beg SB (ClassID (needed m))) / 16).
    { rewrite (it_id_idf G (ClassID (needed m)) (u, m) PCm). cbn [fst snd]. fold SB. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
    refine (NCH_K_slot (ClassID (needed m)) ((u - rz m - region_beg SB (ClassID (needed m))) / 16) z C1 X0 XE XM _ _ _ (COV z ltac:(clear -Hz I2; lia))).
    + intros HP EC E. apply (D_item_p (ClassID (needed m)) (u, m) C1 IIN PCm ltac:(unfold Pc; cbn [snd]; rewrite HP, EC, Z.eqb_refl; reflexivity)).
      rewrite EIT, E. unfold idf. cbn [fst snd]. unfold region_beg, kRegionSize. reflexivity.
    + intros HNE EC EQ. pose proof (QBF HNE) as (QIN & _). rewrite EC in PCm, EIT.
      apply (D_item_batch (u, m) (lastq A) IIN PCm ltac:(unfold qall; apply in_or_app; left; exact QIN)).
      rewrite EIT. unfold qb_id, ptr_to_compact, kCompactPtrScale. change (qb_addr (lastq A)) with qbF. rewrite <- EQ. fold G SB. rewrite EC.
      replace (SB + 24 * 2 ^ 32 + 16 * ((u - rz m - region_beg SB 24) / 16) - region_beg SB 24) with (((u - rz m - region_beg SB 24) / 16) * 2 ^ 4) by (unfold region_beg, kRegionSize; lia).
      rewrite Z.shiftr_div_pow2, Z.div_mul by lia. reflexivity.
    + intros HQ EC EQ. destruct (NBF HQ) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HXin & _). rewrite EC in PCm, EIT, EQ.
      apply (D_item_cache 24 (u, m) (top24 A) ltac:(lia) IIN PCm HXin). rewrite EIT. symmetry. exact EQ.
  - destruct (IS eq_refl) as (ch & Hch & Eb & Esz). destruct (In_nth_error _ _ Hch) as [j Hj].
    destruct HRest as (_ & _ & _ & (HS & _) & _). pose proof (HS j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & _). unfold PG in D6, D8.
    refine (NCH_K_map j ch z Hj _ _).
    + intros HP E. apply (DS_item_p u m IIN HPm HP). rewrite Eb, E. reflexivity.
    + unfold mapzone. pose proof (rz_bound m) as RB. pose proof (round_up_ge m 8 ltac:(lia)) as RU.
      destruct Hz as [Hz|Hz]; [left; clear -Hz Eb Esz D8 RB RU I2; lia | right].
      pose proof (Sh_mono (sc_map_beg ch) u ltac:(clear -Eb; lia)) as SM1.
      assert (B8 : u mod 8 = 0).
      { rewrite Eb. rewrite <- Zplus_mod_idemp_l, <- (Zplus_mod_idemp_l (sc_map_beg ch)). rewrite <- (Z.mod_mod_divide (sc_map_beg ch) 4096 8) by (exists 512; reflexivity). rewrite D6. reflexivity. }
      assert (SM2 : Sh u + (m + 7) / 8 <= Sh (sc_map_beg ch + sc_map_size ch)).
      { unfold Sh. destruct (proj1 (Z.mod_divide u 8 ltac:(lia)) B8) as [w Hw]. rewrite Hw. rewrite Z.div_mul by lia.
        pose proof (Z.div_le_mono (u + m + 7) (sc_map_beg ch + sc_map_size ch) 8 ltac:(lia) ltac:(clear -Eb Esz D8 RU I2; lia)) as DM.
        rewrite Hw in DM. replace (w * 8 + m + 7) with (m + 7 + w * 8) in DM by lia. rewrite Z.div_add in DM by lia. clear -DM. lia. }
      clear -Hz SM1 SM2. lia.
Qed.

Lemma NCH_batch : ltac2:(tb__ "0|1|
S13S0S5cS13R2S77VA;A1A3S3S2S40S13A1S17VA;A1S43S13A1A3A1S3S2S0S14R4A1M0VqbF;A3A1F_;S1S8G0R3A2SaR3S9G0S91A2A2A2S3S66Vq;VA;Vp;Vn;R4A5A1F_;F_;F_;Fz;Fqb;").
Proof.
  intros qb z Hqb NL Hz. pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & HPR & _ & HQR & _). destruct HQR as (QB & _).
  pose proof (proj1 (Forall_forall _ _) QB qb Hqb) as (_ & _ & _ & _ & _ & _ & _ & (x & X1 & X2 & XM & X3)). fold G in X1, X3.
  destruct HPR as (_ & _ & _ & HCR). pose proof (HCR 24 ltac:(lia)) as C24. destruct C24 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _). fold G in M2, M3.
  unfold kUserSpaceSize, kUserMapSize, kFreeArraySize, kRegionSize in M3. unfold kQuarantineBatchSize in Hz, X3.
  assert (XM' : (16 * x) mod 8192 = 0) by (replace (16 * x) with (x mod 512 * 16 + (x / 512) * 8192) by (pose proof (Z.div_mod x 512); clear -H; lia); rewrite XM; apply Z_mod_mult).
  assert (EID : qb_id G qb = x).
  { unfold qb_id, ptr_to_compact, kCompactPtrScale. rewrite X1. fold SB. replace (region_beg SB 24 + 16 * x - region_beg SB 24) with (x * 2 ^ 4) by lia.
    rewrite Z.shiftr_div_pow2, Z.div_mul by lia. reflexivity. }
  refine (NCH_K_slot 24 x z ltac:(lia) X2 ltac:(change (Size 24) with 8192; clear -X3 M2 M3; lia) ltac:(change (Size 24) with 8192; exact XM') _ _ _ _).
  - intros HP EC E. apply (D_batch_p qb Hqb ltac:(unfold Pc; cbn [snd]; rewrite HP, EC, Z.eqb_refl; reflexivity)). rewrite EID, E. unfold idf. cbn [fst snd]. unfold region_beg, kRegionSize. reflexivity.
  - intros HNE _ EQ. apply (NL HNE). rewrite X1. fold SB. unfold region_beg, kRegionSize. rewrite <- EQ. reflexivity.
  - intros HQ _ EQ. destruct (NBF HQ) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HXin & _). apply (D_batch_cache qb (top24 A) Hqb HXin). rewrite EID. symmetry. exact EQ.
  - unfold czone. cbn zeta. left. change (Size 24) with 8192. fold SB in X1. unfold region_beg, kRegionSize in X1. clear -Hz X1. lia.
Qed.

Lemma EG' : aa_geom A' = G. Proof. reflexivity. Qed.
Lemma ELIVE' : ltac2:(tb__ "0|1|
S2S40S42S0S0A2M0A1S1eVA';A1S3fG0Vl1;Vl2;A3A3"). Proof. reflexivity. Qed.
Lemma LIVE_sub : ltac2:(tb__ "0|1|
S0S0S5cS42S0S0A2M0S46S0S0R2R1A4S1eVA';A1A3S5cG0S46S0S0R3R2A4S3fG0Vl1;Vl2;A3A3F_;Fm;Fb;"). Proof. intros b m H. exact H. Qed.
Lemma LIVE_subA : ltac2:(tb__ "0|1|
S0S0S5cS42S0S0A2M0S46S0S0R2R1A4S3fG0Vl1;Vl2;A3A3S5cG0S46S0S0R3R2A4S1eVA;A1A3F_;Fm;Fb;").
Proof. intros b m Hin. rewrite HLV. apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin | right; right; exact Hin]. Qed.
Lemma PLEN : length (aa_cls A) = 32%nat.
Proof. pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & (PL & _) & _). exact PL. Qed.
Lemma ECLS : ltac2:(tb__ "0|1|
S0S8Z0R1A2S2S16Sa1S16S1cVA';A1R2S1bA4S41S16L_;S4fS63S41Lq;Vq;S4aS44S44X63x3S11R2Z18M0A2A2Sc5S82G0A1A1S82R2A1X41x2A3F_;Fc;").
Proof.
  intros c Hc. unfold A', freeA, freeCls, nthZ, csA, nthZ. cbn [aa_cls]. pose proof PLEN as PL.
  destruct q; cbn [andb]; [reflexivity| |]; (destruct (Z.eqb_spec c 24) as [->|NE]; [rewrite nth_list_upd_same by (rewrite PL; cbn; lia); reflexivity | rewrite nth_list_upd_other by (clear -NE Hc; lia); reflexivity]).
Qed.
Lemma ECLS_mapped : ltac2:(tb__ "0|3|
S0S8Z0R1A2S1S2S0S29Sa1S16S1cVA';A1M0R2S1bA4M1A1S29S82R2A1M2A1A3S1S2S0S22G1A1S22G2A1A3S1S2S40S0A1S23G1A1S23G2A1A3S1S2S0S30G1A1S30G2A1A3S0S5cS0R1S1aSa1S16G0R3S1bA4A1A3S5cS0R2S1aS82R4A1A1A3F_;Fx;A2A2A2A2F_;Fc;").
Proof.
  intros c Hc. rewrite (ECLS c Hc). destruct (match q with QA => false | _ => true end && (c =? 24))%bool eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.eqb_eq in E. subst c. cbn [pop_cls cs_mapped_user cs_allocated_user cs_free_array cs_mapped_free_array cs_cache].
    repeat split; try reflexivity. intros x Hx. exact (in_removelast _ _ Hx).
  - repeat split; try reflexivity. intros x Hx. exact Hx.
Qed.

Lemma SG3_pab : ltac2:(tb__ "0|3|
S1S4S8S9S2fVG;A1M0S96A2M1VSB;A2S8S9S9VSB;SdZ2Z25A2A2Z1000M2A2G0A2A2S4S8G1VT;A2S8S9VT;G2A2G0A2A2A2").
Proof.
  pose proof HA as (_ & _ & _ & _ & _ & ((_ & _ & _ & PAB3 & REST) & _) & _). fold G SB T in PAB3, REST. rewrite kSpaceSize_val in PAB3.
  split; [exact PAB3|].
  lazymatch type of REST with _ /\ _ => exact (proj1 REST) | _ => exact REST end.
Qed.

Lemma HRTC : rtc_inv v3 G.
Proof.
  pose proof HA as (HG & HR & _). unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz. apply VO.
  destruct GEO as (T1 & T2 & SB1 & SB2 & SB8 & _ & ST & TB & TI & TG & F1 & F2 & FT & FS & FB & C1 & C2 & TC & SC & D1 & D2 & TD & SD).
  pose proof CZI as (I1 & I2 & I3 & I4 & I5 & _). rewrite FS_total_val in I4.
  destruct (rtc_foot_cases G z Hz) as [K|[K|[K|[K|K]]]].
  - exact (NCH_img z K).
  - apply NCH_T. left. unfold T. clear -K. lia.
  - apply (NCH_out (ag_ctx G) (ag_ctx G + 4096) z); [clear -K; lia | exact I2 | exact (proj1 (proj2 (proj2 (geom_bands _ HG)))) | clear -TC; lia | exact SC].
  - apply (NCH_out (ag_dtls G) (ag_dtls G + 4096) z); [clear -K; lia | exact I3 | exact (proj1 (proj2 (proj2 (proj2 (geom_bands _ HG))))) | clear -TD; lia | exact SD].
  - apply (NCH_out (ag_fsb G) (ag_fsb G + 11571200) z); [clear -K; lia | exact I4 | exact FB | clear -FT; lia | exact FS].
Qed.

Lemma HFS : ltac2:(tb__ "0|0|
SabS59Sa5VG;A1Vv3;A2VA';A2").
Proof.
  pose proof HA as (HG & HR & HF & _). rewrite (restrictv_ext (fs_footb G) vE v3) by (intros z Hz; apply VO; intros Hc; rewrite (CHF z Hc) in Hz; discriminate).
  exact HF.
Qed.

Lemma HLS : live_sep A'.
Proof. pose proof HA as (_ & _ & _ & (Hsep & _) & _). intros b m Hin. rewrite EG'. exact (Hsep b m (LIVE_subA b m Hin)). Qed.

Lemma HLB : live_block_repr m3 A'.
Proof.
  pose proof HA as (_ & _ & _ & (Hsep & Hlive & _) & _). intros b m Hin. pose proof (LIVE_subA b m Hin) as HinA.
  destruct (Hlive b m HinA) as (B1 & B2 & B3 & [B4 B5] & B6 & B7). destruct (Hsep b m HinA) as (L1 & _). pose proof (rz_bound m) as RB.
  pose proof (fun z Hz => NCH_live b m z Hin Hz) as NO.
  pose proof (Z.div_le_mono m (m + 7) 8 ltac:(lia) ltac:(lia)) as DL. pose proof (Z.div_pos m 8 ltac:(lia) ltac:(lia)) as D0.
  split; [rewrite AGm by (apply NO; left; lia); exact B1|].
  split; [apply CELL; [intros k Hk; apply NO; left; lia | exact B2]|].
  split; [apply CELL; [intros k Hk; apply NO; left; lia | exact B3]|].
  split; [split|split].
  - intros g Hg. rewrite AGm by (apply NO; right; lia). exact (B4 g Hg).
  - intros Hm. rewrite AGm; [exact (B5 Hm)|]. apply NO. right.
    replace ((m + 7) / 8) with (m / 8 + 1) by (apply Z.div_unique with (m mod 8 - 1); [pose proof (Z.mod_pos_bound m 8); lia | pose proof (Z.div_mod m 8); lia]). lia.
  - apply (alloc_magic_ok_agree mE m3 b m); [|lia|exact B6]. intros z Hz. apply AGm. apply NO. left. lia.
  - destruct B7 as (tb & Ht' & Hm4). exists tb. split; [|exact Hm4]. rewrite AGm by (apply NO; left; lia). exact Ht'.
Qed.

Lemma HSR : secondary_repr m3 A'.
Proof.
  pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & Hsec & _).
  destruct Hsec as (S1 & SP & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold secondary_repr. rewrite EG'.
  change (aa_sec A') with (aa_sec A). change (aa_ptr_committed A') with (aa_ptr_committed A). fold G.
  assert (CI : forall cc, IMG_LO <= c_addr cc -> c_addr cc + Z.of_nat (c_w cc) <= IMG_HI -> cell_ok mE cc -> cell_ok m3 cc).
  { intros cc H1 H2. apply cell_ok_agree. intros k Hk. apply AGm. apply NCH_img. lia. }
  destruct GEO as (T1 & T2 & SB1 & SB2 & SB8 & _ & ST & TB & TI & TG & _). pose proof CZI as (_ & _ & _ & _ & I5' & _ & _ & I8' & _).
  pose proof HA as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & SEC3 & _). fold G in SEC3. destruct SG3_pab as [PAB3 PABT3].
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; clear -D8 D9; lia)) as MB. pose proof D10 as (_ & _ & _ & _ & WB).
    destruct (SEC3 i ch Hi) as (X1 & X2 & _). fold SB T in X1, X2. rewrite kSpaceSize_val in X1.
    assert (NH : forall z, sc_map_beg ch <= z < sc_map_beg ch + 32 -> ~ chg_f q A p n z).
    { intros z Hz. apply (NCH_out (sc_map_beg ch) (sc_map_beg ch + 32) z Hz (I8' i ch Hi));
        unfold PG, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; clear -WB X1 X2 D8 D9 MB; lia. }
    assert (CA : forall off w v, 0 <= off -> off + Z.of_nat w <= 32 -> cell_ok mE (mkACell (sc_map_beg ch + off) w v) -> cell_ok m3 (mkACell (sc_map_beg ch + off) w v)).
    { intros off w v Ho Hw. apply cell_ok_agree. cbn [c_addr c_w]. intros k Hk. apply AGm. apply NH. clear - Ho Hw Hk. lia. }
    split; [apply CA; [lia| cbn; lia | exact C1]|]. split; [apply CA; [lia| cbn; lia | exact C2]|].
    split; [apply CA; [lia| cbn; lia | exact C3]|]. split; [apply CA; [lia| cbn; lia | exact C4]|].
    split.
    { eapply cell_ok_agree; [|exact C5]. cbn [c_addr c_w]. intros k Hk. apply AGm. pose proof (nth_error_Some_lt _ _ _ Hi) as L.
      destruct S45 as [S4m (S4a & _ & S4t & _ & S4b)]. unfold kPtrArrayReserve in *.
      apply (NCH_out (ag_pab G) (ag_pab G + 2 ^ 23) (ag_pab G + 8 * Z.of_nat i + Z.of_nat k)); [clear -Hk L S2; lia | exact I5' | | clear -PABT3; lia | exact PAB3].
      unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in S4b. exact S4b. }
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [apply PRESB; exact D13 | apply PRESX; exact D14]. }
  split; [apply PRESX; exact SP|]. split; [exact S2|]. split; [exact S3|]. split; [exact S45|].
  unfold SEC_INST, IMG_LO, IMG_HI in *.
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I1]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I2]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I3]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I4]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I5]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I6]|].
  split; [apply PRESX; exact I7|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I8]|].
  apply PRESX; exact I9.
Qed.

Lemma HIA : ia_inv m3 A'.
Proof.
  pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & _ & _ & Hia & _).
  refine (ia_inv_agree mE m3 A A' eq_refl _ Hia). intros z Hz. apply AGm. exact (NCH_img z Hz).
Qed.
Lemma HTI : thread_inv m3 G.
Proof.
  pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & _ & _ & _ & HTH & _). destruct HTH as [TH1 TH2]. fold G T in TH1, TH2 |- *. split.
  - fold T. rewrite AGm; [exact TH1|]. apply NCH_T. right; right; right. clear. lia.
  - fold T. apply PRESX. exact TH2.
Qed.
Lemma HMI : misc_inv m3.
Proof.
  pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & _ & _ & _ & _ & Hmisc).
  refine (misc_inv_agree mE m3 _ Hmisc). intros z Hz. apply AGm. exact (NCH_img z Hz).
Qed.
Lemma HDEP : depot_wf m3 A'.
Proof.
  pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _). destruct HRest as (_ & _ & _ & _ & _ & Hdep & _). destruct HI3 as (_ & _ & _ & _ & DEP3 & _). fold G in DEP3.
  unfold depot_wf in Hdep |- *. change (aa_depot A') with (aa_depot A). eapply depot_mem_frame; [|exact Hdep]. intros a Ha. apply AGm.
  destruct GEO as (T1 & T2 & SB1 & SB2 & SB8 & _ & ST & TB & TI & TG & _). pose proof CZI as (_ & _ & _ & _ & _ & _ & I7 & _).
  assert (BLK' : forall bb L, In (bb, L) (dblocks (aa_depot A)) -> bb <= a < bb + L -> ~ chg_f q A p n a).
  { intros bb L Hbb Hab. destruct (DEP3 (bb, L) Hbb) as (DI & DT & _ & _ & _ & SS & _). unfold sepZ in DT, SS. cbn [fst snd] in DI, DT, SS. fold T in DT. fold SB in SS.
    destruct DI as (_ & _ & _ & _ & WB). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WB. rewrite kSpaceSize_val in SS.
    exact (NCH_out bb (bb + L) a Hab (I7 bb L Hbb) WB ltac:(clear -DT; lia) ltac:(clear -SS; lia)). }
  destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
  - apply NCH_img. unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. unfold IMG_LO, IMG_HI. clear -Hs. lia.
  - apply (BLK' bb NBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. left. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
  - apply (BLK' bb FBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. right. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
Qed.
Lemma HMD : ltac2:(tb__ "0|0|
SadVsegs;VA';Vtp;Vmd;A4").
Proof.
  pose proof HA as (_ & _ & _ & _ & HM & _). unfold model_inv in HM |- *. destruct HM as (VG & PB & LIM & V0 & K0 & F0 & TOPm & LED).
  split; [unfold vm_geom in VG |- *; unfold A', freeA; cbn [aa_geom aa_sec]; exact VG|].
  unfold budget_boundD in PB |- *. change (aa_V A') with (aa_V A). change (aa_Km A') with (aa_Km A). change (aa_Kf A') with (aa_Kf A).
  change (aa_ptr_committed A') with (aa_ptr_committed A). change (aa_depot A') with (aa_depot A). change (aa_geom A') with (aa_geom A).
  assert (PCE : PrimCredit.prim_credit A' = PrimCredit.prim_credit A).
  { apply PrimCreditLaws.prim_credit_maps. intros c Hc. pose proof (ECLS_mapped c ltac:(lia)) as (E1 & _ & _ & E4 & _). unfold csA, nthZ in E1, E4. exact (conj E1 E4). }
  rewrite PCE.
  split; [exact PB|]. split; [exact LIM|]. split; [exact V0|]. split; [exact K0|]. split; [exact F0|]. split; [exact TOPm|].
  unfold ledger_inv, gap_ok, gapN_ok, gapS_ok, blocks_left in LED |- *.
  change (aa_V A') with (aa_V A). change (aa_Km A') with (aa_Km A). change (aa_Kf A') with (aa_Kf A).
  change (aa_ptr_committed A') with (aa_ptr_committed A). change (aa_depot A') with (aa_depot A). change (aa_sec A') with (aa_sec A).
  destruct LED as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|].
  split; [exact L8 | exact L9].
Qed.
Lemma HBTP : bandtp_inv v3 tp.
Proof.
  pose proof HA as (_ & _ & _ & _ & _ & _ & HB). unfold v3. eapply bandtp_mono_rm; [|exact HB]. intros a Ha. apply DEFM.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI in *. clear -Ha. lia.
Qed.

Lemma CZ_slot : ltac2:(tb__ "0|4|
S0S0S0S1S8Z1R3A2S8R3Z1eA2A2S8Z0M0R3A2S8S9ScZ10M1R4A2S8eR5A1A2SbSdZ2M2Z20A2M3SdG2Z1dA2A2A2S2S0SeScG1R5A2S8eR6A1A2G0A3S2S41S8fVn;A1S44A3S2S0S94S95Vn;A1A1R8A3S3S2S0R8S10SbSbVp;S8dVn;A1A2S9VSB;ScR9G3A2A2A2G1A2A3A1F_;F_;Sc4VSB;R8ScG1R7A2S8eR8A1R6A5S83R7A1S5F_;F_;F_;F_;F_;F_;F_;Fz;Fx';Fc';").
Proof.
  intros c' x' z Hc' Hx' HE HM NP KZ K. pose proof (size_ok_all c' Hc') as [SZ1 SZ2].
  destruct GEO as (T1 & T2 & SB1 & SB2 & SB8 & _ & ST & TB & _ & TG & _).
  destruct (is_primary n) eqn:HP.
  - pose proof (KP HP) as KK. cbn zeta in KK. destruct KK as (CE & EO & O0 & OM & OA & M2 & M3 & IDin & CC & SZ & SZM & FIT & KC).
    set (c := ClassID (needed n)) in *. set (o := p - rz n - (SB + c * 2 ^ 32)) in *.
    refine (T_pp c' x' (Size c') c (o / 16) (Size c) z Hc' CC Hx' _ HE _ ltac:(clear -SZ1; lia) ltac:(clear -SZ; lia) SZ2 SZM HM _ _ _ KZ (KC z K)).
    * clear -O0 EO. lia.
    * clear -EO OA M2 M3. lia.
    * rewrite <- EO. exact OM.
    * intros ->. reflexivity.
    * destruct (Z.eq_dec c' c) as [EC|NC]; [right | left; exact NC]. intros EX. apply (NP eq_refl (eq_sym EC)). rewrite EX. unfold o. rewrite <- EC. reflexivity.
  - destruct (KS HP) as (i & ch & Hi & Hch & Eb & Esz & D6 & D8 & D12 & MB & WB & X1 & X2 & X3 & X4 & X6 & X7 & X5 & KC).
    pose proof BLK as (_ & _ & B3 & _). pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU.
    assert (MS0 : 0 <= sc_map_size ch) by (clear -D8 Esz RU B3; lia).
    exact (T_pm c' x' (Size c') ch z Hc' Hx' HE ltac:(clear -SZ1; lia) SZ2 X1 ltac:(clear -MB; lia) MS0 D12 WB KZ (KC z K)).
Qed.

Lemma CZ_map : ltac2:(tb__ "0|0|
S47S15S0S2S49S15A1S5eS15S28VA;A1R3A3S4bS15R2A2A3S2S41S8fVn;A1S4aA3S3S2S0Vp;S9S9S18R4A1Z1000A2Z800A2A3A1F_;S84R4R3A2S83R4A1S5F_;F_;F_;F_;Fz;Fch';Fj;").
Proof.
  intros j ch' z Hj NP KZ K. destruct GEO as (T1 & T2 & SB1 & SB2 & SB8 & _ & ST & TB & _ & TG & _).
  pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _). destruct HRest as (_ & _ & _ & (HS & _) & _). destruct HI3 as (_ & _ & SEC3 & _). fold G in SEC3.
  pose proof (HS j ch' Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D10, D12.
  pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; clear -D8 D9; lia)) as MB. destruct D10 as (_ & _ & _ & _ & WB).
  unfold PG, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in D6, D7, D8, MB, WB.
  destruct (SEC3 j ch' Hj) as (X1 & X2 & _ & _ & X5 & _). fold SB T in X1, X2. rewrite kSpaceSize_val in X1.
  destruct (is_primary n) eqn:HP.
  - pose proof (KP HP) as KK. cbn zeta in KK. destruct KK as (CE & EO & O0 & OM & OA & M2 & M3 & IDin & CC & SZ & SZM & FIT & KC).
    set (c := ClassID (needed n)) in *. set (o := p - rz n - (SB + c * 2 ^ 32)) in *. pose proof (size_ok_all c CC) as [SZ1 SZ2].
    refine (T_pm c (o / 16) (Size c) ch' z CC _ _ ltac:(clear -SZ1; lia) SZ2 X1 ltac:(clear -MB; lia) ltac:(clear -D8 D9; lia) D12 WB (KC z K) KZ).
    * clear -O0 EO. lia.
    * clear -EO OA M2 M3. lia.
  - destruct (KS HP) as (i & ch & Hi & Hch & Eb & Esz & C6 & C8 & C12 & CB & CWB & Y1 & Y2 & Y3 & Y4 & Y6 & Y7 & Y5 & KC).
    assert (NE : i <> j) by (intros <-; rewrite Hi in Hj; injection Hj as E; subst ch'; exact (NP eq_refl Eb)).
    refine (T_mm ch ch' z (Y5 j ch' Hj NE) C6 D6 _ D7 ltac:(clear -CB; lia) ltac:(clear -MB; lia) C12 D12 CWB WB (KC z K) KZ).
    pose proof (HS i ch Hi) as (_ & _ & _ & _ & _ & _ & E7 & _). exact E7.
Qed.

Lemma CZ_live : ltac2:(tb__ "0|2|
S0S0S0S5cS42S0S0A2M0S46S0S0R3R2A4S3fG0Vl1;Vl2;A3A3S4S1S8SbR4S8dR3A1A2R2A2SaR2S9R4R3A2A2A2S1S8S90R4A1M1R2A2SaR2S9G1S10S9R3Z7A2Z8A2A2A2A2A2S83R3A1S5F_;F_;F_;Fz;Fm;Fb;").
Proof.
  intros b m z Hin Hz K. pose proof (LIVE_subA b m Hin) as HinA.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & _). pose proof (proj1 HRest b m HinA) as (L1 & _).
  destruct (is_primary m) eqn:HPm.
  - pose proof (live_slot A rhoE tp md b m HA HinA HPm) as LS. cbn zeta in LS. fold G in LS. destruct LS as (C1 & O0 & OM & OA & _ & _ & _ & _).
    fold SB in O0, OM, OA.
    pose proof (BLKSLOT b m (ClassID (needed m)) L1 HPm eq_refl ltac:(clear -O0; lia) OM OA) as BS. cbn zeta in BS. destruct BS as (_ & X0 & EX & XE & XM & EI & COV).
    assert (PCm : Pc (ClassID (needed m)) (b, m) = true) by (unfold Pc; cbn [snd]; rewrite HPm, Z.eqb_refl; reflexivity).
    refine (CZ_slot (ClassID (needed m)) ((b - rz m - region_beg SB (ClassID (needed m))) / 16) z C1 X0 XE XM _ (COV z Hz) K).
    intros HP EC E. apply (D_live_p (ClassID (needed m)) (b, m) C1 Hin PCm ltac:(unfold Pc; cbn [snd]; rewrite HP, EC, Z.eqb_refl; reflexivity)).
    rewrite <- EI. rewrite E. unfold idf. cbn [fst snd]. unfold region_beg, kRegionSize. reflexivity.
  - destruct HI3 as (_ & HPS & SEC3 & _). destruct (HPS b m HinA) as [Hp' | (ch & Hch & Eb & Esz)]; [rewrite HPm in Hp'; discriminate|].
    destruct (In_nth_error _ _ Hch) as [j Hj]. destruct HRest as (_ & _ & _ & (HS & _) & _). pose proof (HS j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & _).
    refine (CZ_map j ch z Hj _ _ K).
    + intros HP E. apply (DS_live_p b m Hin HPm HP). rewrite Eb, E. reflexivity.
    + unfold mapzone. pose proof (rz_bound m) as RB. unfold PG in D8, Eb.
      pose proof (round_up_ge m 8 ltac:(lia)) as RU.
      destruct Hz as [Hz|Hz]; [left; clear -Hz Eb Esz D8 RB RU L1; lia | right].
      pose proof (Sh_mono (sc_map_beg ch) b ltac:(clear -Eb; lia)) as SM1.
      assert (B8 : b mod 8 = 0).
      { rewrite Eb. unfold PG in D6. rewrite <- Zplus_mod_idemp_l, <- (Zplus_mod_idemp_l (sc_map_beg ch)). rewrite <- (Z.mod_mod_divide (sc_map_beg ch) 4096 8) by (exists 512; reflexivity). rewrite D6. reflexivity. }
      assert (SM2 : Sh b + (m + 7) / 8 <= Sh (sc_map_beg ch + sc_map_size ch)).
      { unfold Sh. destruct (proj1 (Z.mod_divide b 8 ltac:(lia)) B8) as [u Hu]. rewrite Hu. rewrite Z.div_mul by lia.
        pose proof (Z.div_le_mono (b + m + 7) (sc_map_beg ch + sc_map_size ch) 8 ltac:(lia) ltac:(clear -Eb Esz D8 RU L1; lia)) as DM.
        rewrite Hu in DM. replace (u * 8 + m + 7) with (m + 7 + u * 8) in DM by lia. rewrite Z.div_add in DM by lia. clear -DM. lia. }
      clear -Hz SM1 SM2. lia.
Qed.

Definition nbQ : qbatch := ltac2:(tb__ "0|1|
S31VnbF;S45S42S0S0A2M0S46S0S0Vp;Vn;A4S43G0A1A3S9S91Vn;A2A3").
Definition lbQ : qbatch := ltac2:(tb__ "0|2|
S31VqbF;S3fS42S0S0A2M0S1fSc7VA;A1M1A1S45G0S46S0S0Vp;Vn;A4S43G0A1A3A3S9S24G1A1Vn;A2A3").
Lemma FQ_A : ltac2:(tb__ "0|0|
S2S63Vq;S64A3S2S40S13A1S6bVq;VA;Vp;Vn;A4S3fS13S5fS13S17VA;A1A2S45S13S88S43S13A1A3A3A3F_;").
Proof. intros HQ. clear -HQ. rewrite HQ. reflexivity. Qed.
Lemma FQ_B : ltac2:(tb__ "0|0|
S3S2S63Vq;S64A3A1S2S40S13A1S6bVq;VA;Vp;Vn;A4S3fS13S17VA;A1S45S13S85S43S13A1A3A3A3F_;").
Proof. intros HQ. pose proof QC as X. clear -HQ X. destruct q; [congruence | | reflexivity]. cbn in X. destruct X as [E _]. unfold freeQ. rewrite E. reflexivity. Qed.
Lemma THR_A : ltac2:(tb__ "0|1|
S2S63Vq;S64A3S2S40S13A1S17VA;A1M0S3fS13S5fS13G0A2S45S13Sc7VA;A1S43S13A1A3A3A3F_;").
Proof. intros HQ. apply app_removelast_last. apply QNE. rewrite HQ. discriminate. Qed.
Lemma EQALL' : ltac2:(tb__ "0|0|
S2S40S13A1S77VA';A1S3fS13S6bVq;VA;Vp;Vn;A4S35VA;A1A3A3"). Proof. reflexivity. Qed.
Lemma QITEMS' : ltac2:(tb__ "0|1|
Sc3S42S0S0A2M0S78S77VA';A1A1S45G0S46S0S0Vp;Vn;A4S78S77VA;A1A1A3A3").
Proof.
  rewrite EQALL'. unfold qall. destruct QDEC as [HQ|HQ].
  - rewrite (FQ_A HQ). rewrite (THR_A HQ) at 2. rewrite !qitems_app. cbn [qitems flat_map lbQ qb_items]. rewrite !app_nil_r, !app_assoc, <- (app_assoc _ [(p, n)]). cbn [app].
    apply Permutation_sym. apply Permutation_middle.
  - rewrite (FQ_B HQ). rewrite !qitems_app. cbn [qitems flat_map nbQ qb_items]. rewrite ?app_nil_r, ?app_assoc, <- ?(app_assoc _ [(p, n)]). cbn [app]. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma QADDR_A : ltac2:(tb__ "0|0|
S2S63Vq;S64A3S2S40S0A1S7fS13S0S14S77VA';A1A4S7fS13S0S14S77VA;A1A4A3F_;").
Proof.
  intros HQ. rewrite EQALL'. unfold qall. rewrite (FQ_A HQ).
  transitivity (map qb_addr ((removelast (aa_q_thread A) ++ [lastq A]) ++ aa_q_global A)); [rewrite !map_app; reflexivity | rewrite <- (THR_A HQ); reflexivity].
Qed.
Lemma QADDR_B : ltac2:(tb__ "0|0|
S3S2S63Vq;S64A3A1Sc3S0S7fS13S0S14S77VA';A1A4S45S0VnbF;S7fS13S0S14S77VA;A1A4A3A3F_;").
Proof.
  intros HQ. rewrite EQALL'. unfold qall. rewrite (FQ_B HQ). rewrite !map_app. cbn [map nbQ qb_addr]. rewrite <- app_assoc. cbn [app].
  apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma map_qb_id : ltac2:(tb__ "0|0|
S40S13A1S2S40S0A1S7fS13S0S79VG;A1R1A4S7fS0S0S0S9fVSB;Z18R1A3La;S7fS13S0S14R1A4A4A3Fl;").
Proof. intros l. rewrite map_map. reflexivity. Qed.
Lemma QBID_A : ltac2:(tb__ "0|1|
S2S63Vq;S64A3S2S40S0A1S7fS13S0S79VG;A1M0S77VA';A1A4S7fS13S0G0S77VA;A1A4A3F_;").
Proof. intros HQ. rewrite !map_qb_id, (QADDR_A HQ). reflexivity. Qed.
Lemma QBID_nb : ltac2:(tb__ "0|0|
S2S0S79VG;S85A2Sc8VA;A1A3").
Proof.

  unfold qb_id, ptr_to_compact, kCompactPtrScale. cbn [qb_addr nbQ]. unfold nbF, nb_addr. fold G SB.
  replace (region_beg SB 24 + 16 * top24 A - region_beg SB 24) with (top24 A * 2 ^ 4) by lia. rewrite Z.shiftr_div_pow2 by lia.
  apply Z.div_mul. lia.
Qed.
Lemma QBID_B : ltac2:(tb__ "0|1|
S3S2S63Vq;S64A3A1Sc3S0S7fS13S0S79VG;A1M0S77VA';A1A4S45S0Sc8VA;A1S7fS13S0G0S77VA;A1A4A3A3F_;").
Proof.
  intros HQ. rewrite <- QBID_nb. rewrite EQALL'. unfold qall. rewrite (FQ_B HQ). rewrite !map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
  apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma CACHE_B : ltac2:(tb__ "0|1|
S3S2S63Vq;S64A3A1S2S40S0A1Sc9VA;A1M0S3fS0S5fS0G0A2S45S0Sc8VA;A1S43S0A1A3A3A3F_;").
Proof.
  intros HQ. destruct (QB24 HQ) as [_ NC]. unfold top24. apply removelast_split. destruct (cache24 A); [congruence | cbn; lia].
Qed.

Lemma NCH_pce : ltac2:(tb__ "0|6|
S0S0S1S8Z1M0R2A2S8R2Z1eA2A2S1S8S9S9VT;Zd0A2ScZ50M1R3A2A2M2R2A2SaR2S9G2G1A2A2A2S3S2S63Vq;S64A3A1S2S0R5Z18A3S1S8S9VT;Z860A2M3R5A2S3S1S8S9G3ScZ4M4SbScaVA;A1M5G0A2A2A2R5A2SaR5S9G3ScG4G5A2A2A2A2A1A2F_;F_;S3S66Vq;VA;Vp;Vn;R4A5A1F_;F_;F_;Fz;Fc;").
Proof.
  intros c z Hc Hz H24. destruct (Z.eq_dec c 24) as [->|NE].
  - destruct QDEC as [HQ|HQ]; [apply (NCH_cnt24 HQ); clear -Hz; lia|].
    destruct (H24 HQ eq_refl) as [GE NCP]. intros Hc'. apply (proj1 (CHG_QB HQ z)) in Hc'. unfold chg_common, pc24 in Hc'.
    pose proof (blkF_geom A rhoE tp md p n HA HL HCLS) as (_ & _ & _ & _ & BT & _). fold G T in BT.
    destruct GEO as (_ & _ & SB1 & _ & _ & _ & ST & TB & _). pose proof BLK as (B1 & _ & B3 & _ & B5 & _ & B7 & B8 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
    assert (NSH : ~ (Sh p <= z < Sh p + N8 n / 8)).
    { intros Hs. destruct (CZN z ltac:(right; exact Hs)) as [K|K]; [clear -Hs K; unfold Sh, SHADOW_OFF in Hs; lia | clear -Hz K TB; lia]. }
    pose proof (NBF HQ) as (N1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & NT & _ & NQ).
    assert (NL : aa_q_thread A <> [] -> ~ (qbF <= z < qbF + 24)).
    { intros HNE Hb. pose proof (QBF HNE) as (_ & _ & _ & _ & _ & _ & _ & QT & _). unfold kQuarantineBatchSize in QT. clear -Hz Hb QT. lia. }
    clear -Hz Hc' GE NCP NSH BT NT NL N1 B5 B7 B8. destruct Hc' as [Hc|[Hc|[Hc|[HNE Hc]]]]; [lia | lia | lia | exact (NL HNE Hc)].
  - apply NCH_T. clear -Hc Hz NE. assert (c <= 23 \/ 25 <= c) as [X|X] by lia; lia.
Qed.

Lemma QI_perm : ltac2:(tb__ "0|2|
S0S40S42S0S0A2M0A1M1G1Sc3G0R2R1A3Sc3S0S6aVG;R4R3A3S6aVG;R4R2A3A3F_;Fl';Fl;Fc;").
Proof.
  intros c l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2].
  - apply Permutation_refl.
  - rewrite !QI_cons. apply Permutation_app_head. exact IH.
  - rewrite !QI_cons. destruct (Pc c y), (Pc c x); cbn [app]; try apply Permutation_refl. apply perm_swap.
  - eapply Permutation_trans; eassumption.
Qed.
Lemma perm_tool1 : ltac2:(tb__ "0|1|
S40S0A1M0G0G0G0G0G0G0Sc3S0S3fS0R7S3fS0R6S3fS0S3fS0R5R3A3S3fS0S3fS0R4R2A3R1A3A3A3A3S3fS0R7S3fS0R6S3fS0S3fS0R5S3fS0R4R3A3A3S3fS0R2R1A3A3A3A3A3FB;FR;FL2;FI;FL1;FC;FF;").
Proof.
  intros. apply Permutation_app_head. apply Permutation_app_head. rewrite <- !app_assoc. apply Permutation_app_head.
  rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Lemma perm_tool2 : ltac2:(tb__ "0|1|
S40S0A1M0G0G0G0G0S0Sc3S0S3fS0R6S3fS0R5S3fS0R4S3fS0R3S45S0R1R2A3A3A3A3A3S3fS0R6S3fS0S3fS0R5S45S0R1S43S0A1A3A3S3fS0R4S3fS0R3R2A3A3A3A3A3Fx;FB;FR;FL;FC;FF;").
Proof.
  intros. apply Permutation_app_head. rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
  rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma QB_true : ltac2:(tb__ "0|0|
S3S2S63Vq;S64A3A1S2S41S63S41Lq;Vq;S4aS44S44X63x3S44A3F_;").
Proof. clear. destruct q; [congruence | reflexivity | reflexivity]. Qed.
Lemma ECLS_A : ltac2:(tb__ "0|0|
S2S63Vq;S64A3S0S8Z0R1A2S2S16Sa1S16S1cVA';A1R2S1bA4S82R2A1A3F_;Fc;F_;").
Proof. intros HQ c Hc. rewrite (ECLS c Hc). rewrite HQ. reflexivity. Qed.
Lemma ECLS_Bo : ltac2:(tb__ "0|0|
S3S2S63Vq;S64A3A1S0S8Z0R1A2S3S2S0R2Z18A3A1S2S16Sa1S16S1cVA';A1R3S1bA4S82R3A1A3F_;F_;Fc;F_;").
Proof. intros HQ c Hc NE. rewrite (ECLS c Hc). rewrite (QB_true HQ). rewrite (proj2 (Z.eqb_neq c 24) NE). reflexivity. Qed.
Lemma ECLS_B24 : ltac2:(tb__ "0|1|
S3S2S63Vq;S64A3A1S2S16Sa1S16S1cVA';A1Z18M0S1bA4Sc5S82G0A1A1A3F_;").
Proof. intros HQ. rewrite (ECLS 24 ltac:(lia)). rewrite (QB_true HQ). reflexivity. Qed.
Lemma ECLS_same : ltac2:(tb__ "0|0|
S0S8Z0R1A2S3S2S63Vq;S64A3A1S2S0R3Z18A3S5F_;F_;S2S16Sa1S16S1cVA';A1R3S1bA4S82R3A1A3F_;F_;Fc;").
Proof. intros c Hc X. destruct QDEC as [HQ|HQ]; [exact (ECLS_A HQ c Hc)|]. apply (ECLS_Bo HQ c Hc). intros ->. exact (X HQ eq_refl). Qed.

Lemma PINV' : ltac2:(tb__ "0|2|
S40S0A1M0OF_;G0G0Sc3S0R2R1A3R4R2A1R5R4A1F_;F_;Fk;Fl;S0S1S8Z1R1A2S8R1Z1eA2A2R4S3fS0S23S82R2A1M1A1S3fS0S1aG1A1S3fS0Sa4VG;VA;R2A3S7bVG;S77VA;A1R2A3A3A3A3A1R5S3fS0S23S82R3A1A1S3fS0S1aSa1S16S1cVA';A1R3S1bA4A1S3fS0Sa4VG;VA';R3A3S7bVG;S77VA';A1R3A3A3A3A3A1F_;F_;Fc;F_;FP;").
Proof.
  intros P HPP c Hc ND. rewrite LIVE_SPLIT, q_ids_QI in ND.
  rewrite live_ids_LI, ELIVE', LI_app, q_ids_QI.
  assert (PQ : Permutation (QI G c (qitems (qall A'))) ((if Pc c (p, n) then [idf G c (p, n)] else []) ++ QI G c (qitems (qall A)))).
  { eapply Permutation_trans; [apply QI_perm; exact QITEMS'|]. rewrite QI_cons. destruct (Pc c (p, n)) eqn:E; [|apply Permutation_refl].
    cbn [app]. rewrite (it_id_idf G c (p, n) E). unfold idf. rewrite Z.shiftr_div_pow2 by lia. apply Permutation_refl. }
  destruct QDEC as [HQ|HQ].
  - rewrite (ECLS_A HQ c) by lia. rewrite (QBID_A HQ). eapply HPP; [|exact ND].
    eapply Permutation_trans; [do 3 apply Permutation_app_head; apply Permutation_app_tail; exact PQ|]. apply perm_tool1.
  - destruct (Z.eq_dec c 24) as [->|NE].
    + rewrite (ECLS_B24 HQ). cbn [cs_cache pop_cls]. rewrite Z.eqb_refl in ND |- *.
      change (cs_cache (csA 24)) with (cache24 A) in ND |- *. rewrite (CACHE_B HQ) in ND. eapply HPP; [|exact ND].
      eapply Permutation_trans; [do 3 apply Permutation_app_head; apply Permutation_app; [exact PQ | exact (QBID_B HQ)]|].
      eapply Permutation_trans; [apply perm_tool1|]. apply perm_tool2.
    + rewrite (ECLS_Bo HQ c) by lia. rewrite (proj2 (Z.eqb_neq c 24) NE) in ND |- *. eapply HPP; [|exact ND].
      eapply Permutation_trans; [do 3 apply Permutation_app_head; apply Permutation_app_tail; exact PQ|]. apply perm_tool1.
Qed.
Lemma ND' : ltac2:(tb__ "0|0|
S0S1S8Z1R1A2S8R1Z1eA2A2SbfS0S3fS0S23S82R2A1A1S3fS0S1aSa1S16S1cVA';A1R2S1bA4A1S3fS0Sa4VG;VA';R2A3S7bVG;S77VA';A1R2A3A3A3A3A2F_;Fc;").
Proof. intros c Hc. exact (PINV' NoDup ND_perm c Hc (CND c Hc)). Qed.
Lemma CNT' : ltac2:(tb__ "0|2|
S0S1S8Z1R1A2S8R1Z1eA2A2S2S47S48S0S3fS0S23S82R2A1M0A1M1S3fS0S1aSa1S16S1cVA';A1R2S1bA4A1S3fS0Sa4VG;VA';R2A3S7bVG;S77VA';A1R2A3A3A3A3A2S48S0S3fS0G1S3fS0S1aG0A1S3fS0Sa4VG;VA;R2A3S7bVG;S77VA;A1R2A3A3A3A3A2A3F_;Fc;").
Proof.
  intros c Hc. set (N := length (cs_free_array (csA c) ++ cs_cache (csA c) ++ live_ids G A c ++ q_ids G (qall A) c)).
  exact (PINV' (fun l => length l = N) (fun l k HP E => eq_trans (Permutation_length HP) E) c Hc eq_refl).
Qed.

Lemma LEN' : length (aa_cls A') = 32%nat.
Proof. pose proof PLEN as PL. unfold A', freeA. cbn [aa_cls]. unfold freeCls. clear -PL. destruct q; rewrite ?length_list_upd; exact PL. Qed.

Lemma CHG_cnt24 : ltac2:(tb__ "0|1|
S3S2S63Vq;S64A3A1S0S1S8S9S9VT;Zd0A2ScZ50Z18A2A2M0R1A2SaR1S9G0Z10A2A2A2S66Vq;VA;Vp;Vn;R2A5F_;Fz;F_;").
Proof. intros HQ z Hz. apply (proj2 (CHG_QB HQ _)). right; left. left. exact Hz. Qed.

Lemma RIR : ltac2:(tb__ "0|0|
S0S0S47S1S8Z1R3A2S8R3Z1eA2A2S8Z0R3A2S8S9R4SfR3A1A2Z80A2S47SccR1R5A2S3S66Vq;VA;Vp;Vn;S9S9Sa0VSB;R8A2R7A2SfR2A1A2A5A1F_;Fj;F_;F_;F_;Fw;Foff;Fc;").
Proof.
  intros c off w Hc Ho Hw j Hj. apply NCH_meta. unfold region_info, kRegionInfoStride. rewrite kSpaceSize_val. clear -Hc Ho Hw Hj. lia.
Qed.

Lemma CR_xfer : ltac2:(tb__ "0|9|
S0S16S1S8Z1R2A2S8R2Z1eA2A2S2S40S0A1M0S23R2A1S23S82R3A1A1A3S2S0S30R3A1S30S82R4A1A1A3S2S0S22R4A1S22S82R5A1A1A3S2S0S29R5A1S29S82R6A1A1A3S0S5cS0R1S1aR7A1A3S5cS0R2S1aS82R9A1A1M1A3F_;Fx;S2S16Sa1S16S1cVA';A1R8S1bA4R7A3S4S1S2G0S1aR8A1M2G1A3S3S2S63Vq;S64A3A1M3S2S0RaZ18M4A3S5F_;F_;A2S1S2S41S32VA;A1S44A3S1S51Vm3;S52S9S9VT;Zd0A2ScZ50R9A2A2M5U4M6SfS48S0G2A2M7A1A3A2S1S51Vm3;S52S9G5Z4A2G6S99R9A1A3A2S1S51Vm3;S52S9G5Z8A2U8S8eR9A1A3A2S1S47S0S2S49S0A1M8S5eS0S1aRaA1R2A3S4bS0R1A2A3S2G8S5eS0S1aS82RcA1A1R3A3S4bS0R2A2A3F_;Fx;Fi;S1S2S47Sd6G7U1A2S48S0G1A2A3S1G3S2S0R9G4A3A2A2A2A2A2A2A2A2Sb3Vm3;VG;VA';RaR9A5F_;F_;F_;F_;F_;F_;F_;F_;Fcs';Fc;").
Proof.
  intros c cs' Hc EF EMF EAU EMU CIN ECS CASE.
  pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & (PL & P0 & P31 & PC) & _). pose proof (PC c Hc) as PCc. fold G mE in PCc.
  change (nthZ (aa_cls A) c cs_empty) with (csA c) in PCc. unfold class_repr in PCc.
  destruct PCc as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & R9 & PR & N7 & PU & PSH & PE & ND & LV & CI & CN & CT & CC & CMU & CFA).
  fold SB T in R1, R2, R3, R4, R5, R6, R7, R8, PRI, R9, PR, PU, PSH, PE, LV, CI, CN.
  unfold class_repr. fold SB T. rewrite EF, EMF, EAU, EMU.
  split; [apply CELL; [apply RIR; unfold RI_mutex; cbn; clear -Hc; lia | exact R1]|].
  split; [apply CELL; [apply RIR; unfold RI_num_freed; cbn; clear -Hc; lia | exact R2]|].
  split; [apply CELL; [apply RIR; unfold RI_mapped_free_array; cbn; clear -Hc; lia | exact R3]|].
  split; [apply CELL; [apply RIR; unfold RI_allocated_user; cbn; clear -Hc; lia | exact R4]|].
  split; [apply CELL; [apply RIR; unfold RI_allocated_meta; cbn; clear -Hc; lia | exact R5]|].
  split; [apply CELL; [apply RIR; unfold RI_mapped_user; cbn; clear -Hc; lia | exact R6]|].
  split; [apply CELL; [apply RIR; unfold RI_mapped_meta; cbn; clear -Hc; lia | exact R7]|].
  split; [apply CELL; [apply RIR; unfold RI_exhausted; cbn; clear -Hc; lia | exact R8]|].
  split; [apply PRESX; exact PRI|].
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
  split.
  { intros i x0 Hi. apply CELL; [|exact (R9 i x0 Hi)]. intros k Hk. apply (NCH_fa c); [exact Hc|]. pose proof (nth_error_Some_lt _ _ _ Hi) as L.
    cbn [c_addr]. unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. unfold kFreeArraySize in N6. clear -L Hk N6. lia. }
  split; [apply PRESX; exact PR|].
  split; [intros x0 Hx0; apply N7; apply in_app_or in Hx0 as [Hx0|Hx0]; apply in_or_app; [left; exact Hx0 | right; exact (CIN _ Hx0)]|].
  split; [apply PRESB; exact PU|]. split; [apply PRESX; exact PSH|]. split; [apply PRESX; exact PE|].
  split; [rewrite <- ECS; exact (ND' c Hc)|].
  split; [intros b m Hin Hp Hcl; exact (LV b m (LIVE_subA b m Hin) Hp Hcl)|].
  assert (PCE : forall off w, 0 <= off -> off + Z.of_nat w <= 80 ->
                (q <> QA -> c = 24 -> 16 <= off /\ (off + Z.of_nat w <= 16 + 4 * (cnt24 A - 1) \/ 16 + 4 * cnt24 A <= off)) ->
                forall j, (j < w)%nat -> ~ chg_f q A p n (T + 0xd0 + 80 * c + off + Z.of_nat j)).
  { intros off w Ho Hw H4 j Hj. apply (NCH_pce c); [exact Hc | clear -Ho Hw Hj; lia |]. intros HQ E. pose proof (H4 HQ E) as [X Y]. subst c. clear -X Y Hj Ho Hw. lia. }
  change (aa_cache_inited A') with (aa_cache_inited A).
  split.
  - intros HCI. destruct (CI HCI) as (K1 & K2 & K3 & K4 & K5). pose proof (max_count_le16 c Hc) as H16.
    assert (CNT : cell_ok m3 (mkACell (T + 0xd0 + 80 * c) 4 (Z.of_nat (length (cs_cache cs'))))
              /\ cell_ok m3 (mkACell (T + 0xd0 + 80 * c + 4) 4 (max_count c)) /\ cell_ok m3 (mkACell (T + 0xd0 + 80 * c + 8) 8 (Size c))
              /\ (forall i x, nth_error (cs_cache cs') i = Some x -> nth_error (cs_cache (csA c)) i = Some x)
              /\ (length (cs_cache cs') <= length (cs_cache (csA c)))%nat
              /\ (q <> QA -> c = 24 -> (length (cs_cache cs') + 1 = length (cs_cache (csA c)))%nat)).
    { destruct CASE as [[EC NX]|(_ & X1 & XM & XS & X2 & X3 & [XQ X24])]; [|split; [exact X1 | split; [exact XM | split; [exact XS | split; [exact X2 | split; [clear -X3; lia | intros _ _; exact X3]]]]]].
      rewrite EC. split; [|split; [|split; [|split; [intros i x Hi; exact Hi | split; [clear; lia | intros HQ E; destruct (NX HQ E)]]]]].
      + apply CELL; [|exact K1]. intros k Hk. cbn [c_addr]. replace (T + 0xd0 + 80 * c + Z.of_nat k) with (T + 0xd0 + 80 * c + 0 + Z.of_nat k) by (clear; lia).
        apply (PCE 0 4%nat); [clear; lia | clear; cbn; lia | intros HQ E; destruct (NX HQ E) | exact Hk].
      + apply CELL; [|exact K2]. intros k Hk. cbn [c_addr]. apply (PCE 4 4%nat); [clear; lia | clear; cbn; lia | intros HQ E; destruct (NX HQ E) | exact Hk].
      + apply CELL; [|exact K3]. intros k Hk. cbn [c_addr]. apply (PCE 8 8%nat); [clear; lia | clear; cbn; lia | intros HQ E; destruct (NX HQ E) | exact Hk]. }
    destruct CNT as (C1 & CM & CS & C2 & C3 & C4).
    split; [exact C1|]. split; [exact CM|]. split; [exact CS|].
    split; [|clear -K5 C3; lia].
    intros i x0 Hi. pose proof (C2 i x0 Hi) as Hi'. pose proof (nth_error_Some_lt _ _ _ Hi) as L. pose proof (nth_error_Some_lt _ _ _ Hi') as L'.
    apply CELL; [|exact (K4 i x0 Hi')]. intros k Hk. cbn [c_addr].
    replace (T + 0xd0 + 80 * c + 16 + 4 * Z.of_nat i + Z.of_nat k) with (T + 0xd0 + 80 * c + (16 + 4 * Z.of_nat i) + Z.of_nat k) by (clear; lia).
    apply (PCE (16 + 4 * Z.of_nat i) 4%nat); [clear -L; lia | cbn [Z.of_nat Pos.of_succ_nat]; clear -L' K5 H16; lia | | exact Hk].
    intros HQ E. pose proof (C4 HQ E) as C4'. subst c. unfold cnt24, cache24. change (nthZ (aa_cls A) 24 cs_empty) with (csA 24).
    cbn [Z.of_nat]. clear -L C4'. split; [lia | left; lia].
  - split.
    { intros HCF. destruct (CN HCF) as [E0 F0].
      destruct CASE as [[EC NX]|(HCI & _)]; [|rewrite HCF in HCI; discriminate].
      split; [rewrite EC; exact E0|].
      eapply filled_agree; [|exact F0]. intros z Hz. apply AGm. apply (NCH_pce c); [exact Hc | clear -Hz; lia | intros HQ E; destruct (NX HQ E)]. }

    split; [rewrite ?EMU, ?EAU; exact CT|]. split; [|rewrite ?EMU, ?EMF; exact (conj CMU CFA)].
    unfold slots in CC |- *. rewrite ?EAU, ?EF. rewrite CC. f_equal. pose proof (CNT' c Hc) as X. rewrite ECS in X. rewrite !length_app in X. clear -X. lia.
Qed.

Lemma LC_A : ltac2:(tb__ "0|5|
S2S63Vq;S64A3S17VA;A1S40S13A1Sc7VA;A1S13SfS48S42S0S0A2S1fR1A1A2A1S0S1S51Vv3;S52S9VT;Z50A2M0U8M1SfS48S13R3A2A1A3A2S1S51Vv3;S52S9G0Z8M2A2G1S14S60S13Sa3R3A3A1A3A2S1S51Vv3;S52S9G0Z10M3A2G1VqbF;A3A2S1S51Vv3;S52S9G0Z18M4A2G1S9Sa2R3A1Vn;A2A3A2S1S51Vv3;S52S9VqbF;G2A2G1S9S24R2A1Vn;A2A3A2S1S51Vv3;S52S9VqbF;G3A2G1S9R1Z1A2A3A2S1S51Vv3;S52S9S9VqbF;G4A2ScG2R1A2A2G1SbVp;G3A2A3A2S51Vv3;S52VqbF;G1Z0A3A2A2A2A2A2A2A2A2Tk;Tb;Tl;F_;").
Proof. intros HQ. pose proof LC as X. clear -X HQ. rewrite HQ in X. exact X. Qed.

Lemma LC_B : ltac2:(tb__ "0|d|
S3S2S63Vq;S64A3A1S1S51Vv3;S52S9VT;Z50M0A2M1U8M2S9SfS48S13S17VA;A1M3A2A1Z1M4A2A3A2S1S51Vv3;S52S9G1Z8M5A2G2S14S60S13Sa3S3fS13G3S45S13S85S43S13A1M6A3A3A3A1A3A2S1S51Vv3;S52S9G1Z10M7A2G2VnbF;A3A2S1S51Vv3;S52S9G1Z18M8A2G2S9Sa2G3A1S9Vn;S91A2M9A2A3A2S1S51Vv3;S52S9S9VT;Zd0A2ScG0G8A2A2MaU4MbSbSfS48S0Sc9VA;A1A2A1G4A2A3A2S1S51Vv3;S52VnbF;G2Z0A3A2S1S51Vv3;S52S9VnbF;G5A2G2G9A3A2S1S51Vv3;S52S9VnbF;G7A2G2G4A3A2S1S51Vv3;S52S9VnbF;G8A2G2SbVp;G7A2A3A2S1S51Vv3;S52S9GaZ4A2GbS99G8A1A3A2S1S51Vv3;S52S9GaG5A2G2S8eG8A1A3A2S3S2S40S13A1G3G6A3A1S1S51Vv3;S52VqbF;G2VnbF;A3A2S1S51Vv3;S52S9VqbF;G5A2G2S24Sc7VA;A1McA1A3A2S51Vv3;S52S9VqbF;G7A2G2SfS48S42S0S0A2S1fGcA1A2A1A3A2A2A2F_;A2A2A2A2A2A2A2A2A2A2A2F_;").
Proof.
  intros HQ. pose proof LC as X. pose proof QC as Y. clear -X Y HQ. unfold leaf_cells in X. unfold qcond in Y. fold G T in X. destruct q; [congruence| |].
  - destruct Y as [E _]. rewrite E in X |- *. destruct X as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11).
    repeat split; try assumption; exfalso; congruence.
  - destruct Y as [NE _]. destruct X as (X1 & X2 & X3 & X4 & XL & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13).
    replace (hd qb_dflt (aa_q_thread A ++ [nbQ])) with (hd qb_dflt (aa_q_thread A)) by (clear -NE; destruct (aa_q_thread A); [congruence | reflexivity]).
    repeat split; assumption.
Qed.
Lemma HPR : primary_repr m3 A'.
Proof.
  pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & (PL & P0 & P31 & PC) & _).
  unfold primary_repr. rewrite EG'. split; [exact LEN'|].
  split; [rewrite (ECLS_same 0 ltac:(clear; lia) ltac:(intros _ E; clear -E; lia)); exact P0|].
  split; [rewrite (ECLS_same 31 ltac:(clear; lia) ltac:(intros _ E; clear -E; lia)); exact P31|].
  intros c Hc.
  assert (CASE : (q <> QA /\ c = 24) \/ (q <> QA -> c = 24 -> False)).
  { destruct QDEC as [HQ|HQ]; [right; intros X; destruct (X HQ)|]. destruct (Z.eq_dec c 24) as [->|NE]; [left; split; [exact HQ|reflexivity] | right; intros _ E; exact (NE E)]. }
  destruct CASE as [[HQ ->]|NX].
  -
    destruct (QB24 HQ) as [HCI HNC].
    assert (HCL : (0 < length (cache24 A))%nat) by (destruct (cache24 A); [congruence | cbn; clear; lia]).
    rewrite (ECLS_B24 HQ). apply (CR_xfer 24 (pop_cls (csA 24)) Hc eq_refl eq_refl eq_refl eq_refl).
    + cbn [cs_cache pop_cls]. intros x Hx. exact (in_removelast _ _ Hx).
    + exact (ECLS_B24 HQ).
    + right. split; [exact HCI|]. cbn [cs_cache pop_cls]. change (cs_cache (csA 24)) with (cache24 A).
      rewrite (removelast_len (cache24 A) 0 HCL).
      destruct (LC_B HQ) as (_ & _ & _ & _ & X5 & _ & _ & _ & _ & XM & XS & _).
      split; [|split; [|split; [|split; [intros i x Hi; pose proof (nth_error_Some_lt _ _ _ Hi) as L; rewrite (removelast_len (cache24 A) 0 HCL) in L; rewrite <- (nth_error_removelast (cache24 A) 0 i L); exact Hi | split; [clear -HCL; lia | split; [exact HQ | reflexivity]]]]]].
      * replace (Z.of_nat (length (cache24 A) - 1)) with (Z.of_nat (length (cache24 A)) - 1) by (clear -HCL; lia).
        apply CELL3; [|exact X5]. intros k Hk. cbn [c_addr]. apply (CHG_cnt24 HQ). clear -Hk. lia.
      * apply CELL3; [|exact XM]. intros k Hk. cbn [c_addr]. apply (CHG_cnt24 HQ). clear -Hk. lia.
      * apply CELL3; [|exact XS]. intros k Hk. cbn [c_addr]. apply (CHG_cnt24 HQ). clear -Hk. lia.
  - rewrite (ECLS_same c ltac:(clear -Hc; lia) NX). apply (CR_xfer c (csA c) Hc eq_refl eq_refl eq_refl eq_refl (fun x H => H) (ECLS_same c ltac:(clear -Hc; lia) NX)).
    left. split; [reflexivity | exact NX].
Qed.

Lemma NCH_own : ltac2:(tb__ "0|0|
S0S1S8SbVp;S8dVn;A1A2R1A2SaR1SbVp;Z10A2A2A2S3S66Vq;VA;Vp;Vn;R2A5A1F_;Fz;").
Proof.
  intros z Hz Hc. pose proof BLK as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  pose proof CZI as (I1 & _). assert (K : CZ z) by (left; clear -Hz B7; lia).
  assert (NSH : ~ (Sh p <= z < Sh p + N8 n / 8)).
  { intros Hs. destruct (CZS z Hs) as [X _]. clear -Hz X B1 B7 B8. lia. }
  destruct QDEC as [HQ|HQ].
  - apply (proj1 (CHG_QA HQ z)) in Hc. unfold chg_common in Hc.
    pose proof (QBF (QNE ltac:(rewrite HQ; discriminate))) as (QIN & _ & _ & _ & (xb & X1 & X2 & XM & X3) & M2 & M3 & _).
    assert (XM' : (16 * xb) mod 8192 = 0) by (replace (16 * xb) with (xb mod 512 * 16 + (xb / 512) * 8192) by (pose proof (Z.div_mod xb 512); clear -H; lia); rewrite XM; apply Z_mod_mult).
    assert (NB : ~ (qbF <= z < qbF + 8192)).
    { intros Hb. refine (CZ_slot 24 xb z ltac:(clear; lia) X2 ltac:(change (Size 24) with 8192; clear -X3 M2 M3; lia) ltac:(change (Size 24) with 8192; exact XM') _ _ K).
      + intros HP EC E. apply (D_batch_p (lastq A) ltac:(unfold qall; apply in_or_app; left; exact QIN) ltac:(unfold Pc; cbn [snd]; rewrite HP, EC, Z.eqb_refl; reflexivity)).
        unfold qb_id, ptr_to_compact, kCompactPtrScale. change (qb_addr (lastq A)) with qbF. rewrite X1. fold SB.
        replace (SB + 24 * 2 ^ 32 + 16 * xb - region_beg SB 24) with (xb * 2 ^ 4) by (unfold region_beg, kRegionSize; clear; lia). rewrite Z.shiftr_div_pow2, Z.div_mul by (clear; lia).
        rewrite E. unfold idf. cbn [fst snd]. unfold region_beg, kRegionSize. reflexivity.
      + unfold czone. cbn zeta. left. change (Size 24) with 8192. rewrite <- X1. exact Hb. }
    unfold kA in Hc. pose proof (QK HQ) as QK'. unfold kQuarantineBatchCount in QK'. clear -Hz NSH I1 NB Hc B7 B8 QK'. lia.
  - apply (proj1 (CHG_QB HQ z)) in Hc. unfold chg_common, pc24 in Hc.
    pose proof (NBF HQ) as (N1' & N2' & N3 & N4 & N5 & N6 & N7 & N8' & NM & NX & NT & _).
    assert (NB : ~ (nbF <= z < nbF + 8192)).
    { intros Hb. refine (CZ_slot 24 (top24 A) z ltac:(clear; lia) ltac:(clear -N2'; lia) ltac:(change (Size 24) with 8192; clear -N6 N7 N8'; lia) ltac:(change (Size 24) with 8192; exact NM) _ _ K).
      + intros HP EC E. apply (D_cache_p 24 (top24 A) ltac:(clear; lia) NX ltac:(unfold Pc; cbn [snd]; rewrite HP, EC, Z.eqb_refl; reflexivity)).
        rewrite E. unfold idf. cbn [fst snd]. unfold region_beg, kRegionSize. reflexivity.
      + unfold czone. cbn zeta. left. change (Size 24) with 8192. rewrite <- N3. exact Hb. }
    assert (NL : aa_q_thread A <> [] -> ~ (qbF <= z < qbF + 24)).
    { intros HNE Hb. pose proof (QBF HNE) as (QIN & _ & _ & _ & (xb & X1 & X2 & XM & X3) & M2 & M3 & _).
      assert (XM' : (16 * xb) mod 8192 = 0) by (replace (16 * xb) with (xb mod 512 * 16 + (xb / 512) * 8192) by (pose proof (Z.div_mod xb 512); clear -H; lia); rewrite XM; apply Z_mod_mult).
      refine (CZ_slot 24 xb z ltac:(clear; lia) X2 ltac:(change (Size 24) with 8192; clear -X3 M2 M3; lia) ltac:(change (Size 24) with 8192; exact XM') _ _ K).
      + intros HP EC E. apply (D_batch_p (lastq A) ltac:(unfold qall; apply in_or_app; left; exact QIN) ltac:(unfold Pc; cbn [snd]; rewrite HP, EC, Z.eqb_refl; reflexivity)).
        unfold qb_id, ptr_to_compact, kCompactPtrScale. change (qb_addr (lastq A)) with qbF. rewrite X1. fold SB.
        replace (SB + 24 * 2 ^ 32 + 16 * xb - region_beg SB 24) with (xb * 2 ^ 4) by (unfold region_beg, kRegionSize; clear; lia). rewrite Z.shiftr_div_pow2, Z.div_mul by (clear; lia).
        rewrite E. unfold idf. cbn [fst snd]. unfold region_beg, kRegionSize. reflexivity.
      + unfold czone. cbn zeta. left. change (Size 24) with 8192. rewrite <- X1. clear -Hb. lia. }
    pose proof (NBF_cnt HQ) as NC. clear -Hz NSH I1 NB NL NT NC Hc B7 B8. destruct Hc as [Hc|[Hc|[Hc|[HNE Hc]]]]; [lia | lia | exact (NB Hc) | exact (NL HNE Hc)].
Qed.

Lemma NCH_lastA : ltac2:(tb__ "0|2|
S2S63Vq;S64A3S0S1S8S9VqbF;Z18A2M0R1A2SaR1S9VqbF;S91A2A2A2S3S1S8S9G0ScZ8S86A2M1A2R2A2SaR2S9S9VqbF;Z20A2G1A2A2A2A1S3S66Vq;VA;Vp;Vn;R3A5A1F_;F_;Fz;F_;").
Proof.
  intros HQ z Hz NK Hc. apply (proj1 (CHG_QA HQ z)) in Hc. unfold chg_common in Hc. unfold kQuarantineBatchSize in Hz.
  pose proof (QBF (QNE ltac:(rewrite HQ; discriminate))) as (QIN & _ & Q3 & _ & (xb & X1 & X2 & XM & X3) & M2 & M3 & QT & QP & _).
  destruct GEO as (T1 & T2 & SB1 & SB2 & _ & _ & ST & TB & _). pose proof BLK as (B1 & _ & _ & _ & B5 & _ & B7 & B8 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  assert (NSH : ~ (Sh p <= z < Sh p + N8 n / 8)) by (intros Hs; destruct (CZS z Hs) as [X _]; clear -Hz X Q3 SB1; lia).
  unfold kQuarantineBatchSize in QT, QP. clear -Hz NK Hc NSH QT QP B5 B7. lia.
Qed.
Lemma NCH_lastB : ltac2:(tb__ "0|0|
S3S2S63Vq;S64A3A1S3S2S40S13A1S17VA;A1S43S13A1A3A1S0S1S8S9VqbF;Z18A2R1A2SaR1S9VqbF;S91A2A2A2S3S66Vq;VA;Vp;Vn;R2A5A1F_;Fz;F_;F_;").
Proof.
  intros HQ HNE z Hz Hc. apply (proj1 (CHG_QB HQ z)) in Hc. unfold chg_common, pc24 in Hc. unfold kQuarantineBatchSize in Hz.
  pose proof (QBF HNE) as (QIN & _ & Q3 & _ & (xb & X1 & X2 & XM & X3) & M2 & M3 & QT & QP & _).
  pose proof (NBF HQ) as (N1 & _ & N3 & _ & N5 & _ & _ & _ & _ & _ & NT & NP & NQ). specialize (NQ HNE).
  destruct GEO as (T1 & T2 & SB1 & SB2 & _ & _ & ST & TB & _). pose proof BLK as (B1 & _ & _ & _ & B5 & _ & B7 & B8 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  assert (NSH : ~ (Sh p <= z < Sh p + N8 n / 8)) by (intros Hs; destruct (CZS z Hs) as [X _]; clear -Hz X Q3 SB1; lia).
  unfold kQuarantineBatchSize in QT, QP, NQ. clear -Hz Hc NSH QT QP NQ N1 B5 B7. lia.
Qed.

Lemma CHG_hdr : ltac2:(tb__ "0|0|
S0S1S8Z0R1A2SaR1Z8A2A2S66Vq;VA;Vp;Vn;S9SbVp;Z10A2R2A2A5F_;Fk;").
Proof. intros k Hk. destruct QDEC as [HQ|HQ]; [apply (proj2 (CHG_QA HQ _)) | apply (proj2 (CHG_QB HQ _))]; left; unfold chg_common; clear -Hk; lia. Qed.
Lemma CHG_blk : ltac2:(tb__ "0|0|
S0S1S8Vp;R1A2SaR1S9Vp;SbeVn;A1A2A2A2S66Vq;VA;Vp;Vn;R2A5F_;Fz;").
Proof. intros z Hz. destruct QDEC as [HQ|HQ]; [apply (proj2 (CHG_QA HQ _)) | apply (proj2 (CHG_QB HQ _))]; left; unfold chg_common; clear -Hz; lia. Qed.
Lemma CHG_sh : ltac2:(tb__ "0|1|
S0S1S8S90Vp;A1M0R1A2SaR1S9G0S10SbeVn;A1Z8A2A2A2A2S66Vq;VA;Vp;Vn;R2A5F_;Fz;").
Proof. intros z Hz. destruct QDEC as [HQ|HQ]; [apply (proj2 (CHG_QA HQ _)) | apply (proj2 (CHG_QB HQ _))]; left; unfold chg_common; clear -Hz; lia. Qed.
Lemma CHG_thdr : ltac2:(tb__ "0|0|
S0S1S8S9VT;Z50A2R1A2SaR1S9VT;Z70A2A2A2S66Vq;VA;Vp;Vn;R2A5F_;Fz;").
Proof. intros z Hz. destruct QDEC as [HQ|HQ]; [apply (proj2 (CHG_QA HQ _)) | apply (proj2 (CHG_QB HQ _))]; left; unfold chg_common; clear -Hz; lia. Qed.
Lemma CHG_lastA : ltac2:(tb__ "0|2|
S2S63Vq;S64A3S0S4S1S8VqbF;R1A2SaR1S9VqbF;Z18A2M0A2A2S1S8S9G0ScZ8S86A2M1A2R1A2SaR1S9S9VqbF;Z20A2G1A2A2A2A2S66Vq;VA;Vp;Vn;R2A5F_;Fz;F_;").
Proof. intros HQ z Hz. apply (proj2 (CHG_QA HQ _)). clear -Hz. tauto. Qed.
Lemma CHG_nb : ltac2:(tb__ "0|0|
S3S2S63Vq;S64A3A1S0S1S8VnbF;R1A2SaR1S9VnbF;Z2000A2A2A2S66Vq;VA;Vp;Vn;R2A5F_;Fz;F_;").
Proof. intros HQ z Hz. apply (proj2 (CHG_QB HQ _)). clear -Hz. tauto. Qed.
Lemma CHG_pc24 : ltac2:(tb__ "0|0|
S3S2S63Vq;S64A3A1S0S89R1A1S66Vq;VA;Vp;Vn;R2A5F_;Fz;F_;").
Proof. intros HQ z Hz. apply (proj2 (CHG_QB HQ _)). clear -Hz. tauto. Qed.
Lemma CHG_lastBf : ltac2:(tb__ "0|0|
S3S2S63Vq;S64A3A1S3S2S40S13A1S17VA;A1S43S13A1A3A1S0S1S8VqbF;R1A2SaR1S9VqbF;Z18A2A2A2S66Vq;VA;Vp;Vn;R2A5F_;Fz;F_;F_;").
Proof. intros HQ HNE z Hz. apply (proj2 (CHG_QB HQ _)). clear -Hz HNE. tauto. Qed.

Lemma Z_to_bv8_mod : ltac2:(tb__ "0|2|
S0S0S2S0SeR2SdZ2Z8A2M0A2SeR1G0A2A3S2Sc2Q8M1A1Sc1G1R3A2Sc1G1R2A2A3F_;Fy;Fx;").
Proof.
  intros x y E. apply SymSoundM.Z_to_bv8_eq_bits. intros i Hi.
  rewrite <- (Z.mod_pow2_bits_low x 8 i) by lia. rewrite <- (Z.mod_pow2_bits_low y 8 i) by lia. rewrite E. reflexivity.
Qed.
Lemma enc_byte : ltac2:(tb__ "0|2|
S47S0S47SccR1R3A2ScdR4U8A2S2Sc2Q8M0A1M1S80G1R3S7eR5Sc1Q40R4A2A2Sc1G0Z0A2A4Sc1G0S10R4SdZ2ScZ8SfR3A1A2A2A2A2A3F_;F_;Fk;Fv;Fw;").
Proof.
  intros w v k Hk Hw. unfold enc_bytes. rewrite SymSoundM.Z_to_le_bytes_nth by exact Hk. rewrite Z_to_bv_unsigned.
  apply SymSoundM.Z_to_bv8_eq_bits. intros i Hi. rewrite Z.shiftr_spec by lia. rewrite Z.div_pow2_bits by lia.
  unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64). rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed.

Lemma PRES_chunk : ltac2:(tb__ "0|0|
S57VmE;SbVp;S8dVn;A1A2Vp;A3").
Proof.
  pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & HPR & HSR & _). pose proof BLK as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold blk_geo in B1.
  destruct (is_primary n) eqn:HP.
  - pose proof (KP HP) as KK. cbn zeta in KK. destruct KK as (CE & EO & O0 & OM & OA & M2 & M3 & IDin & CC & SZ & SZM & FIT & KC).
    destruct HPR as (_ & _ & _ & HCR). pose proof (HCR _ CC) as Cc.
    destruct Cc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PU & _). fold G SB vE mE in PU.
    intros z Hz. apply PU; [unfold region_beg, kRegionSize; clear -Hz EO O0 OA M2 FIT B5 B3; lia | apply (chunk_not_other_live A rhoE tp md p n z HA HL); clear -Hz B3; lia].
  - destruct (KS HP) as (i & ch & Hi & Hch & Eb & Esz & D6 & D8 & D12 & MB & WB & _). destruct HSR as (HS & _).
    pose proof (HS i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D13 & _). fold G vE mE in D13.
    assert (EN : N8 n = round_up n 8) by (unfold N8, round_up; replace (n + 8 - 1) with (n + 7) by (clear; lia); reflexivity).
    intros z Hz. apply D13; [clear -Hz Eb Esz D8 B8 EN B5 B3; lia | apply (chunk_not_other_live A rhoE tp md p n z HA HL); clear -Hz B3; lia].
Qed.

Lemma QI_new : ltac2:(tb__ "0|0|
SacVm3;VA';S46S0S0Vp;Vn;A4A3").
Proof.
  pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _). destruct HRest as (Hsep & Hlive & HPR & HSR & _).
  pose proof BLK as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  destruct (Hlive p n HL) as (L1 & L2 & L3 & [L4 L5] & L6 & L7). fold G vE in L2, L6. fold mE in L2, L6.
  unfold q_item_ok. cbn [fst snd]. rewrite EG'. change (aa_sec A') with (aa_sec A). fold SB.
  set (V := 3 + 256 * t + 65536 * (n / 2 ^ 32)) in VHW.
  assert (HX : 0 <= n / 2 ^ 32) by (apply Z.div_pos; clear -B3; lia).
  assert (EV : V / 65536 = n / 2 ^ 32).
  { unfold V. replace (3 + 256 * t + 65536 * (n / 2 ^ 32)) with ((3 + 256 * t) + (n / 2 ^ 32) * 65536) by (clear; lia).
    rewrite Z.div_add by (clear; lia). rewrite Z.div_small by (clear -Ht; lia). clear; lia. }
  split; [unfold IMG_HI; clear -B1; lia|]. split; [exact B3|].
  split.
  { rewrite CHm by (replace (p - 16) with (p - 16 + 0) by (clear; lia); apply CHG_hdr; clear; lia).
    pose proof (VHW 0%nat ltac:(cbn; clear; lia)) as X. cbn [c_addr c_w c_val] in X. rewrite (enc_byte 4 V 0 ltac:(clear; lia) ltac:(clear; lia)) in X.
    replace (p - 16 + Z.of_nat 0) with (p - 16) in X by (clear; lia). rewrite X. f_equal. apply Z_to_bv8_mod.
    change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. unfold V.
    replace (3 + 256 * t + 65536 * (n / 2 ^ 32)) with (3 + (t + 256 * (n / 2 ^ 32)) * 2 ^ 8) by (clear; lia). rewrite Z_mod_plus_full. reflexivity. }
  split.
  { intros z Hz. destruct (PRES z ltac:(replace z with (p - 16 + 1) by (clear -Hz; lia); apply CHG_hdr; clear; lia)) as [b Hb].
    exists b. rewrite CHm; [exact Hb|]. replace z with (p - 16 + 1) by (clear -Hz; lia). apply CHG_hdr. clear; lia. }
  split.
  { apply CELL3; [intros k Hk; cbn [c_addr]; replace (p - 14 + Z.of_nat k) with (p - 16 + (2 + Z.of_nat k)) by (clear; lia); apply CHG_hdr; clear -Hk; lia|].
    intros k Hk. cbn [c_addr c_w c_val] in Hk |- *. rewrite (enc_byte 2 (n / 2 ^ 32) k Hk ltac:(clear; lia)).
    pose proof (VHW (2 + k)%nat ltac:(cbn [c_w]; clear -Hk; lia)) as X. cbn [c_addr c_w c_val] in X.
    rewrite (enc_byte 4 V (2 + k) ltac:(clear -Hk; lia) ltac:(clear; lia)) in X.
    replace (p - 14 + Z.of_nat k) with (p - 16 + Z.of_nat (2 + k)) by (clear; lia). rewrite X. f_equal. f_equal.
    rewrite Nat2Z.inj_add. replace (8 * (Z.of_nat 2 + Z.of_nat k)) with (16 + 8 * Z.of_nat k) by (clear; lia).
    rewrite Z.pow_add_r by (clear; lia). rewrite <- Z.div_div by (clear; lia). change (2 ^ 16) with 65536. rewrite EV. reflexivity. }
  split; [apply CELL3; [intros k Hk; cbn [c_addr]; replace (p - 12 + Z.of_nat k) with (p - 16 + (4 + Z.of_nat k)) by (clear; lia); apply CHG_hdr; clear -Hk; lia | exact VHL]|].
  split; [apply PRESX; intros z Hz; apply PRES_chunk; clear -Hz B7 B8; lia|].
  split.
  { destruct (Z.eq_dec (rz n) 16) as [E16|N16]; [left; exact E16 | right].
    destruct L6 as [E16|[M1 M2]]; [exfalso; exact (N16 E16)|].
    assert (R32 : 32 <= rz n) by (clear -N16 B8 B9; pose proof (Z.div_mod (rz n) 16); lia).
    split; (apply CELL; [|eassumption]); intros k Hk; cbn [c_addr]; apply NCH_own; clear -Hk R32 B7 B8; lia. }
  split.
  { intros HP. destruct HPR as (_ & _ & _ & HCR). destruct (needed_fits n B3 HP) as (F1 & F2 & F3).
    pose proof (HCR _ F2) as Cc. destruct Cc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _).
    rewrite (proj1 (proj2 (ECLS_mapped (ClassID (needed n)) ltac:(clear -F2; lia)))). exact (LV p n HL HP eq_refl). }
  split; [intros HP; destruct HI3 as (_ & LIV3 & _); destruct (LIV3 p n HL) as [E|X]; [rewrite HP in E; discriminate | exact X]|].
  replace ((n + 7) / 8) with (N8 n / 8) by (unfold N8; rewrite Z.div_mul by (clear; lia); reflexivity).
  intros z Hz. destruct (PRES z (CHG_sh z Hz)) as [b Hb]. exists b. rewrite CHm by (apply CHG_sh; exact Hz). exact Hb.
Qed.

Lemma QI_xfer : ltac2:(tb__ "0|1|
S13S42S0S0A2M0S5cS13R2S77VA;A1A3S5cG0R2S1fR3A1A3SacVmE;VA;R3A3SacVm3;VA';R4A3F_;F_;F_;Fit;Fqb;").
Proof.
  intros qb it Hqb Hit Q. pose proof (fun z Hz => NCH_item qb it z Hqb Hit Hz) as NO. destruct it as [u m]. cbn [fst snd] in NO.
  unfold q_item_ok in Q |- *. cbn [fst snd] in Q |- *. rewrite EG'. change (aa_sec A') with (aa_sec A). fold G SB in Q |- *.
  destruct Q as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11). pose proof (rz_bound m) as RB.
  assert (AGi : forall z, u - rz m <= z < u -> m3 z = mE z) by (intros z Hz; apply AGm; apply NO; left; exact Hz).
  split; [exact J1|]. split; [exact J2|]. split; [rewrite AGi by (clear -RB; lia); exact J3|].
  split; [eapply present_agree; [|exact J4]; intros z Hz; apply AGi; clear -Hz RB; lia|].
  split; [eapply cell_ok_agree; [|exact J5]; cbn [c_addr c_w]; intros k Hk; apply AGi; clear -Hk RB; lia|].
  split; [eapply cell_ok_agree; [|exact J6]; cbn [c_addr c_w]; intros k Hk; apply AGi; clear -Hk RB; lia|].
  split; [eapply present_agree; [|exact J7]; intros z Hz; apply AGi; clear -Hz RB; lia|].
  split; [apply (alloc_magic_ok_agree mE m3 u m); [exact AGi | clear -RB; lia | exact J8]|].
  split.
  { intros HP. destruct (needed_fits m J2 HP) as (F1 & F2 & F3).
    rewrite (proj1 (proj2 (ECLS_mapped (ClassID (needed m)) ltac:(clear -F2; lia)))). exact (J9 HP). }
  split; [exact J10|].
  eapply present_agree; [|exact J11]. intros z Hz. apply AGm. apply NO. right. exact Hz.
Qed.

Lemma BR_xfer : ltac2:(tb__ "0|2|
S13S5cS13R1S77VA;A1A3S51Vm3;S52S9S14R2A1Z8A2U8M0S24R2A1A3A2S51Vm3;S52S9S14R3A1Z10A2G0SfS48S42S0S0A2S1fR3A1A2A1A3A2S0S1S8S9S14R5A1M1Z18A2R1A2SaR1S9G1S91A2A2A2S3S66Vq;VA;Vp;Vn;R2A5A1F_;Fz;Sa7Vm3;VA';R5A3F_;F_;F_;F_;Fqb;").
Proof.
  intros qb Hqb HB1 HB2 NOB. pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & HQR & _). destruct HQR as (QB & _).
  pose proof (proj1 (Forall_forall _ _) QB qb Hqb) as BR. unfold batch_repr in BR |- *. fold G vE in BR. fold mE SB in BR. rewrite EG'. fold SB.
  destruct BR as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7). unfold kQuarantineBatchSize in *.
  split; [exact B0|]. split; [exact HB1|]. split; [exact HB2|]. split; [exact B3|]. split; [exact B4|].
  split; [apply PRESX; exact B5|].
  split.
  - intros i it Hi. destruct (B6 i it Hi) as [I1 I2]. pose proof (nth_error_Some_lt _ _ _ Hi) as L. unfold kQuarantineBatchCount in B3.
    split; [apply CELL; [intros k Hk; cbn [c_addr]; apply NOB; clear -Hk L B3; lia | exact I1]|].
    exact (QI_xfer qb it Hqb (nth_error_In _ _ Hi) I2).
  - destruct B7 as (x & E1 & E2 & E3 & E4). exists x. rewrite (proj1 (proj2 (ECLS_mapped 24 ltac:(clear; lia)))).
    split; [exact E1|]. split; [exact E2|]. split; [exact E3 | exact E4].
Qed.

Lemma BR_old : ltac2:(tb__ "0|0|
S13S5cS13R1S77VA;A1A3S3S2S40S13A1S17VA;A1S43S13A1A3A1S3S2S0S14R3A1VqbF;A3A1F_;Sa7Vm3;VA';R3A3F_;F_;Fqb;").
Proof.
  intros qb Hqb NL. pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & HQR & _). destruct HQR as (QB & _).
  pose proof (proj1 (Forall_forall _ _) QB qb Hqb) as (_ & B1 & B2 & _). fold G vE in B1, B2. fold mE in B1, B2.
  assert (NOB : forall z, qb_addr qb <= z < qb_addr qb + kQuarantineBatchSize -> ~ chg_f q A p n z) by (intros z Hz; exact (NCH_batch qb z Hqb NL Hz)).
  unfold kQuarantineBatchSize in NOB.
  apply (BR_xfer qb Hqb).
  - apply CELL; [intros k Hk; cbn [c_addr]; apply NOB; clear -Hk; lia | exact B1].
  - apply CELL; [intros k Hk; cbn [c_addr]; apply NOB; clear -Hk; lia | exact B2].
  - intros z Hz. apply NOB. unfold kQuarantineBatchSize in Hz. clear -Hz. lia.
Qed.

Lemma addr_inj : ltac2:(tb__ "0|0|
S40S13A1S13S13SbfS0S7fS13S0S14R3A4A2S5cS13R3R4A3S5cS13R3R5A3S2S0S14R5A1S14R4A1A3S2S13R6R5A3F_;F_;F_;F_;Fb2;Fb1;Fl;").
Proof.
  intros l. induction l as [|x r IH]; intros b1 b2 ND H1 H2 E; [destruct H1|].
  cbn [map] in ND. apply (proj1 (list_relations.list.NoDup_cons _ _)) in ND as [NX ND].
  destruct H1 as [<-|H1]; destruct H2 as [<-|H2]; [reflexivity | exfalso | exfalso | exact (IH b1 b2 ND H1 H2 E)].
  - apply NX. apply (proj2 (list_elem_of_In _ _)). rewrite E. apply in_map. exact H2.
  - apply NX. apply (proj2 (list_elem_of_In _ _)). rewrite <- E. apply in_map. exact H1.
Qed.

Lemma BR_thrB : ltac2:(tb__ "0|0|
S3S2S63Vq;S64A3A1S13S5cS13R1S17VA;A1A3Sa7Vm3;VA';R2A3F_;Fqb;F_;").
Proof.
  intros HQ qb Hqb. assert (HqbA : In qb (qall A)) by (unfold qall; apply in_or_app; left; exact Hqb).
  assert (HNE : aa_q_thread A <> []) by (destruct (aa_q_thread A); [destruct Hqb | discriminate]).
  destruct (Z.eq_dec (qb_addr qb) qbF) as [E|NE]; [|exact (BR_old qb HqbA ltac:(intros _; exact NE))].
  pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & HQR & _). pose proof HQR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Q10).
  pose proof (QBF HNE) as (QIN & _).
  assert (Eqb : qb = lastq A).
  { apply (addr_inj (qall A) qb (lastq A) Q10 HqbA ltac:(unfold qall; apply in_or_app; left; exact QIN) E). }
  subst qb. destruct (LC_B HQ) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XL). destruct (XL HNE) as (_ & XBS & XBK).
  clear E. apply (BR_xfer (lastq A) HqbA); change (qb_addr (lastq A)) with qbF.
  - apply CELL3; [intros k Hk; cbn [c_addr]; apply (CHG_lastBf HQ HNE); clear -Hk; lia | exact XBS].
  - apply CELL3; [intros k Hk; cbn [c_addr]; apply (CHG_lastBf HQ HNE); clear -Hk; lia | exact XBK].
  - intros z Hz. exact (NCH_lastB HQ HNE z Hz).
Qed.

Lemma fold_snd_app : ltac2:(tb__ "0|4|
S40S42S0S0A2M0A1M1G1S2S0S61S0G0G0S0S9S4cS0S0R2A3R1A2Lacc;Lit;M2Z0M3S3fG0R2R1A3A5S9S61S0G0G2G3R2A5S61S0G0G2G3R1A5A2A3Fk2;Fk1;").
Proof. intros k1 k2. induction k1 as [|a k1 IH]; cbn -[Z.add]; [clear; lia | rewrite IH; clear; lia]. Qed.

Lemma BR_lastA : ltac2:(tb__ "0|0|
S2S63Vq;S64A3Sa7Vm3;VA';S88A3F_;").
Proof.
  intros HQ. pose proof (QNE ltac:(rewrite HQ; discriminate)) as HNE.
  pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & HQR & _). destruct HQR as (QB & _).
  pose proof (QBF HNE) as (QIN & _). pose proof (proj1 (Forall_forall _ _) QB (lastq A) ltac:(apply in_or_app; left; exact QIN)) as BR.
  unfold batch_repr in BR |- *. fold G vE in BR. fold mE SB in BR. rewrite EG'. fold SB. change (qb_addr (lastq A)) with qbF in BR.
  cbn [qb_addr qb_items qb_size lbQ]. destruct BR as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct (LC_A HQ) as (_ & _ & _ & _ & X5 & X6 & X7 & X8). fold kA in X6, X7, QC. pose proof (QK HQ) as QK'. fold kA in QK'.
  assert (LEN : Z.of_nat (length (qb_items (lastq A) ++ [(p, n)])) = kA + 1) by (rewrite length_app; cbn [length]; unfold kA; clear; lia).
  unfold kQuarantineBatchSize, kQuarantineBatchCount in *.
  split; [exact B0|].
  split; [apply CELL3; [intros k Hk; cbn [c_addr]; apply (CHG_lastA HQ); clear -Hk; lia | exact X5]|].
  split; [rewrite LEN; apply CELL3; [intros k Hk; cbn [c_addr]; apply (CHG_lastA HQ); clear -Hk; lia | exact X6]|].
  split; [rewrite LEN; clear -QK'; lia|].
  split; [rewrite fold_snd_app; cbn [fold_right snd]; clear -B4; lia|].
  split; [apply PRESX; exact B5|].
  split.
  - intros i it Hi. destruct (Nat.lt_ge_cases i (length (qb_items (lastq A)))) as [LT|GE].
    + rewrite nth_error_app1 in Hi by exact LT. destruct (B6 i it Hi) as [I1 I2].
      split; [|exact (QI_xfer (lastq A) it ltac:(apply in_or_app; left; exact QIN) (nth_error_In _ _ Hi) I2)].
      apply CELL; [|exact I1]. intros k Hk. cbn [c_addr]. apply (NCH_lastA HQ); unfold kQuarantineBatchSize, kA in *; clear -Hk LT QK'; lia.
    + rewrite nth_error_app2 in Hi by exact GE. destruct (i - length (qb_items (lastq A)))%nat as [|j] eqn:Ej; [|destruct j; discriminate].
      cbn in Hi. injection Hi as <-. cbn [fst snd]. assert (Ei : Z.of_nat i = kA) by (unfold kA; clear -GE Ej; lia). rewrite Ei.
      split; [apply CELL3; [intros k Hk; cbn [c_addr]; apply (CHG_lastA HQ); clear -Hk; lia | exact X7] | exact QI_new].
  - destruct B7 as (x & E1 & E2 & E3 & E4). exists x. rewrite (proj1 (proj2 (ECLS_mapped 24 ltac:(clear; lia)))).
    split; [exact E1|]. split; [exact E2|]. split; [exact E3 | exact E4].
Qed.

Lemma BR_nb : ltac2:(tb__ "0|0|
S3S2S63Vq;S64A3A1Sa7Vm3;VA';S85A3F_;").
Proof.
  intros HQ. pose proof (NBF HQ) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8' & NM & NX & NT & NP & NQ).
  destruct GEO as (_ & _ & SB1 & _).
  pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & HPR & _). destruct HPR as (_ & _ & _ & HCR).
  pose proof (HCR 24 ltac:(clear; lia)) as C24. destruct C24 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PU & _). fold G SB vE mE in PU.
  destruct (LC_B HQ) as (_ & _ & _ & _ & _ & X6 & X7 & X8 & X9 & _).
  unfold batch_repr. rewrite EG'. fold SB. cbn [qb_addr qb_items qb_size nbQ length fold_right fst snd]. unfold kQuarantineBatchSize, kQuarantineBatchCount in *.
  split; [unfold IMG_HI; clear -N5 SB1; lia|].
  split; [replace (8192 + n) with (n + 8192) by (clear; lia); apply CELL3; [intros k Hk; cbn [c_addr]; apply (CHG_nb HQ); clear -Hk; lia | exact X7]|].
  split; [apply CELL3; [intros k Hk; cbn [c_addr]; apply (CHG_nb HQ); clear -Hk; lia | exact X8]|].
  split; [clear; lia|]. split; [clear; lia|].
  split.
  { intros z Hz. destruct (PRES z ltac:(apply (CHG_nb HQ); clear -Hz; lia)) as [b Hb]. exists b. rewrite CHm by (apply (CHG_nb HQ); clear -Hz; lia). exact Hb. }
  split.
  - intros i it Hi. destruct i as [|i]; [|destruct i; discriminate]. cbn in Hi. injection Hi as <-. cbn [fst snd].
    replace (nbF + 24 + 8 * Z.of_nat 0) with (nbF + 24) by (clear; lia).
    split; [apply CELL3; [intros k Hk; cbn [c_addr]; apply (CHG_nb HQ); clear -Hk; lia | exact X9] | exact QI_new].
  - exists (top24 A). rewrite (proj1 (proj2 (ECLS_mapped 24 ltac:(clear; lia)))).
    split; [unfold region_beg, kRegionSize; rewrite N3; clear; lia|]. split; [clear -N2; lia|].
    split; [|exact N6]. clear -NM N2. replace 8192 with (16 * 512) in NM by reflexivity. rewrite Z.mul_mod_distr_l in NM by (clear; lia). lia.
Qed.

Lemma NCH_link8 : ltac2:(tb__ "0|1|
S13S5cS13R1S77VA;A1A3S3S2S40S13A1S17VA;A1S43S13A1A3A1S3S2S0S14R3A1VqbF;A3A1F_;S0S1S8S14R4A1M0R1A2SaR1S9G0Z8A2A2A2S3S66Vq;VA;Vp;Vn;R2A5A1F_;Fz;F_;F_;Fqb;").
Proof. intros qb Hqb NL z Hz. apply (NCH_batch qb z Hqb NL). unfold kQuarantineBatchSize. clear -Hz. lia. Qed.

Lemma qlinks_iff : ltac2:(tb__ "0|0|
S53S40S13A1S7Sa6R2R1A2S47S13S2S49S13A1S5eS13R3R2A3S4bS13R1A2A3S51R5S52S14R2A1U8S14S80S13S50R3A1R4Sa3A4A1A3A2F_;Fb;Fi;A2Fl;Fm;").
Proof.
  intros m l. induction l as [|x r IH].
  - split; [intros _ i b Hi; destruct i; discriminate | intros _; exact I].
  - cbn [qlinks]. split.
    + intros [H1 H2] i b Hi. destruct i as [|i].
      * cbn in Hi. injection Hi as <-. cbn [nth]. destruct r as [|y r']; [cbn; exact H1 | exact H1].
      * cbn in Hi. change (nth (S (S i)) (x :: r) qb_dflt) with (nth (S i) r qb_dflt). exact (proj1 IH H2 i b Hi).
    + intros H. split.
      * pose proof (H 0%nat x eq_refl) as H0. cbn [nth] in H0. destruct r as [|y r']; [cbn in H0; exact H0 | exact H0].
      * apply (proj2 IH). intros i b Hi. exact (H (S i) b Hi).
Qed.

Lemma qlinks_addr : ltac2:(tb__ "0|1|
S53S40S13A1M0G0S2S40S0A1S7fS13S0S14R2A4S7fS13S0S14R1A4A3Sa6R4R3A2Sa6R5R3A2F_;F_;Fl';Fl;Fm;").
Proof.
  intros m l. induction l as [|b r IH]; intros l' E H; destruct l' as [|b' r']; try discriminate; [exact I|].
  cbn in E. injection E as E1 E2. cbn in H |- *. destruct H as [H1 H2]. split; [|exact (IH r' E2 H2)].
  rewrite <- E1. destruct r as [|c r0]; destruct r' as [|c' r0']; try discriminate; [exact H1|]. cbn in E2. injection E2 as E3 _. rewrite <- E3. exact H1.
Qed.

Lemma qlinks_snoc : ltac2:(tb__ "0|5|
S53S53S40S13A1M0S13S13S0S5cS13R2R4A3S3S2S0S14R3A1S14S5dS13R5Sa3A3A1A3A1S1S8S14R4A1M1R3A2SaR3S9G1Z8A2A2A2S2S49Sc2Q8A1A1R8R4A1R9R4A1A3F_;F_;F_;Fz;Fx;SbfS0S7fS13S0S14R3A4A2Sa6R6R4A2S3S2G0R5S43S13A1M2A3A1S51R7S52S14S5dS13R6Sa3A3A1U8M3S14R5A1M4A3A2F_;S51R7S52G4G3Z0A3A2Sa6R8S3fS13R7S45S13R6G2A3A3A2F_;F_;F_;F_;F_;Fb;Fl;Fm';Fm;").
Proof.
  intros m m' l b AG ND H HL HB. revert AG ND H HL. induction l as [|x r IH]; intros AG ND H HL.
  - cbn. split; [exact HB | exact I].
  - cbn [app qlinks]. cbn [qlinks] in H. destruct H as [H1 H2].
    apply (proj1 (list_relations.list.NoDup_cons _ _)) in ND as [NX ND].
    destruct r as [|y r'].
    + cbn. split; [exact (HL ltac:(discriminate)) | split; [exact HB | exact I]].
    + split.
      * cbn [app]. eapply cell_ok_agree; [|exact H1]. cbn [c_addr c_w]. intros k Hk. apply (AG x); [left; reflexivity | | clear -Hk; lia].
        intros EQ. apply NX. rewrite EQ. apply (proj2 (list_elem_of_In _ _)). apply (in_map qb_addr (y :: r') (last (y :: r') qb_dflt)).
        rewrite (last_nth (y :: r') qb_dflt). apply nth_In. cbn [length]. clear. lia.
      * apply IH; [intros x0 z Hx0 NEx Hz; apply (AG x0); [right; exact Hx0 | exact NEx | exact Hz] | exact ND | exact H2 | intros _; exact (HL ltac:(discriminate))].
Qed.

Lemma hd_addr : ltac2:(tb__ "0|0|
S40S13A1S2S0S14S60S13Sa3R1A3A1S60S0Z0S7fS13S0S14R1A4A3A3Fl;").
Proof. intros [|b r]; reflexivity. Qed.
Lemma last_addr : ltac2:(tb__ "0|0|
S40S13A1S2S0S14S5dS13R1Sa3A3A1S5dS0S7fS13S0S14R1A4Z0A3A3Fl;").
Proof. intros l. induction l as [|b r IH]; [reflexivity|]. cbn [map last]. destruct r as [|c r']; [reflexivity|]. exact IH. Qed.

Lemma THRADDR_A : ltac2:(tb__ "0|0|
S2S63Vq;S64A3S2S40S0A1S7fS13S0S14S6bVq;VA;Vp;Vn;A4A4S7fS13S0S14S17VA;A1A4A3F_;").
Proof.
  intros HQ. rewrite (FQ_A HQ). transitivity (map qb_addr (removelast (aa_q_thread A) ++ [lastq A])); [rewrite !map_app; reflexivity | rewrite <- (THR_A HQ); reflexivity].
Qed.

Lemma RL_ne : ltac2:(tb__ "0|1|
S13S3S2S40S13A1S17VA;A1M0S43S13A1A3A1S5cS13R2S5fS13G0A2A3S3S2S0S14R3A1VqbF;A3A1F_;F_;Fb;").
Proof.
  intros b HNE Hb E. destruct (in_split _ _ Hb) as (r1 & r2 & Er).
  refine (D_batches b (lastq A) r1 r2 (aa_q_global A) _ E). unfold qall. rewrite (app_removelast_last qb_dflt HNE) at 1. rewrite Er.
  unfold lastq. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma HQR : ltac2:(tb__ "0|0|
S71VQBD;Vm3;VA';A3").
Proof.
  pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (Hsep & _ & _ & _ & HQR & _).
  pose proof HQR as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10). fold G T vE in Q1, Q2, Q3, Q4, Q5, Q6, Q7. fold mE in Q1, Q2, Q3, Q4, Q5, Q6, Q7.
  unfold qrepr_B. rewrite EG'. change (aa_q_thread A') with (freeQ q A p n). change (aa_q_global A') with (aa_q_global A). fold T.
  assert (GNL : forall qb, In qb (aa_q_global A) -> aa_q_thread A <> [] -> qb_addr qb <> qbF).
  { intros qb Hqb HNE. destruct (in_split _ _ Hqb) as (g1 & g2 & Eg). intros E. symmetry in E.
    refine (D_batches (lastq A) qb (removelast (aa_q_thread A)) g1 g2 _ E). unfold qall. rewrite Eg.
    rewrite (app_removelast_last qb_dflt HNE) at 1. rewrite <- app_assoc. reflexivity. }
  assert (AGI : forall z, IMG_LO <= z < IMG_HI -> m3 z = mE z) by (intros z Hz; apply AGm; exact (NCH_img z Hz)).
  split.
  { apply Forall_app. split; [|apply Forall_forall; intros qb Hqb; apply BR_old; [unfold qall; apply in_or_app; right; exact Hqb | exact (GNL qb Hqb)]].
    destruct QDEC as [HQ|HQ].
    - rewrite (FQ_A HQ). apply Forall_app. split; [|constructor; [exact (BR_lastA HQ) | constructor]].
      apply Forall_forall. intros qb Hqb. apply BR_old; [unfold qall; apply in_or_app; left; exact (in_removelast _ _ Hqb)|].
      intros HNE. exact (RL_ne qb HNE Hqb).
    - rewrite (FQ_B HQ). apply Forall_app. split; [apply Forall_forall; exact (BR_thrB HQ) | constructor; [exact (BR_nb HQ) | constructor]]. }
  split.
  { destruct QDEC as [HQ|HQ].
    - apply (qlinks_addr m3 (aa_q_thread A)); [symmetry; exact (THRADDR_A HQ)|].
      pose proof (QNE ltac:(rewrite HQ; discriminate)) as HNE. destruct (LC_A HQ) as (_ & _ & _ & _ & _ & _ & _ & X8).
      apply (proj2 (qlinks_iff m3 (aa_q_thread A))). intros i b Hi. pose proof (proj1 (qlinks_iff mE (aa_q_thread A)) Q2 i b Hi) as CL.
      pose proof (nth_error_Some_lt _ _ _ Hi) as L.
      destruct (Nat.eq_dec (S i) (length (aa_q_thread A))) as [EL|NL].
      + assert (Eb : b = lastq A).
        { unfold lastq. rewrite last_nth. replace (length (aa_q_thread A) - 1)%nat with i by (clear -EL; lia). symmetry. apply nth_error_nth. exact Hi. }
        rewrite (nth_overflow (aa_q_thread A) qb_dflt) by (clear -EL; lia). subst b. change (qb_addr (lastq A)) with qbF. change (qb_addr qb_dflt) with 0.
        apply CELL3; [|exact X8]. intros k Hk. cbn [c_addr]. apply (CHG_lastA HQ). left. clear -Hk. lia.
      + apply CELL; [|exact CL]. intros k Hk. cbn [c_addr].
        assert (Hb : In b (removelast (aa_q_thread A))).
        { apply (nth_error_In _ i). rewrite (nth_error_removelast (aa_q_thread A) qb_dflt i) by (clear -L NL; lia). exact Hi. }
        apply (NCH_link8 b ltac:(unfold qall; apply in_or_app; left; exact (in_removelast _ _ Hb)) ltac:(intros HNE'; exact (RL_ne b HNE' Hb))). clear -Hk. lia.
    - rewrite (FQ_B HQ). destruct (LC_B HQ) as (_ & _ & _ & _ & _ & X6 & _ & _ & _ & _ & _ & XL).
      apply (qlinks_snoc mE m3); [| rewrite map_app in Q10; exact (ND_app_l _ _ Q10) | exact Q2 | | ].
      + intros x z Hx NEx Hz. apply AGm. apply (NCH_link8 x ltac:(unfold qall; apply in_or_app; left; exact Hx) ltac:(intros _; exact NEx) z Hz).
      + intros HNE. change (last (aa_q_thread A) qb_dflt) with (lastq A). change (qb_addr (lastq A)) with qbF. cbn [qb_addr nbQ].
        apply CELL3; [|exact (proj1 (XL HNE))]. intros k Hk. cbn [c_addr]. apply (CHG_lastBf HQ HNE). clear -Hk. lia.
      + cbn [qb_addr nbQ]. apply CELL3; [|exact X6]. intros k Hk. cbn [c_addr]. apply (CHG_nb HQ). clear -Hk. lia. }
  split.
  { apply (qlinks_agree mE m3); [|exact Q3]. intros b z Hb Hz. apply AGm.
    apply (NCH_link8 b ltac:(unfold qall; apply in_or_app; right; exact Hb) ltac:(intros HNE; exact (GNL b Hb HNE)) z Hz). }
  split.
  {
    unfold qhdr_repr.
    assert (CH : forall off w v, 0 <= off -> off + Z.of_nat w <= 32 -> cell_ok v3 (mkACell (T + 80 + off) w v) -> cell_ok m3 (mkACell (T + 80 + off) w v)).
    { intros off w v Ho Hw Hc. apply CELL3; [|exact Hc]. intros k Hk. cbn [c_addr]. apply CHG_thdr. clear -Ho Hw Hk. lia. }
    assert (CH0 : forall w v, Z.of_nat w <= 32 -> cell_ok v3 (mkACell (T + 80) w v) -> cell_ok m3 (mkACell (T + 80) w v)).
    { intros w v Hw Hc. apply CELL3; [|exact Hc]. intros k Hk. cbn [c_addr]. apply CHG_thdr. clear -Hw Hk. lia. }
    destruct QDEC as [HQ|HQ].
    - destruct (LC_A HQ) as (X1 & X2 & X3 & X4 & _). pose proof (QNE ltac:(rewrite HQ; discriminate)) as HNE.
      assert (EL : length (freeQ q A p n) = length (aa_q_thread A)).
      { pose proof (THRADDR_A HQ) as E. apply (f_equal (@length Z)) in E. rewrite !length_map in E. exact E. }
      rewrite EL. split; [apply CH0; [cbn; clear; lia | exact X1]|].
      split.
      { intros _. rewrite hd_addr, last_addr, (THRADDR_A HQ), <- hd_addr, <- last_addr. change (qb_addr (last (aa_q_thread A) qb_dflt)) with qbF.
        split; [apply (CH 8 8%nat); [clear; lia | cbn; clear; lia | exact X2] | apply (CH 16 8%nat); [clear; lia | cbn; clear; lia | exact X3]]. }
      split; [intros z Hz; destruct (PRES z ltac:(apply CHG_thdr; clear -Hz; lia)) as [b Hb]; exists b; rewrite CHm by (apply CHG_thdr; clear -Hz; lia); exact Hb|].
      replace (qsize (freeQ q A p n)) with (qsize (aa_q_thread A) + n); [apply (CH 24 8%nat); [clear; lia | cbn; clear; lia | exact X4]|].
      rewrite (FQ_A HQ), qsize_app, (qsize_removelast_last (aa_q_thread A) HNE). cbn [qsize fold_right lbQ qb_size]. unfold lastq. clear. lia.
    - destruct (LC_B HQ) as (X1 & X2 & X3 & X4 & _). rewrite (FQ_B HQ).
      split; [rewrite length_app; cbn [length]; replace (Z.of_nat (length (aa_q_thread A) + 1)) with (Z.of_nat (length (aa_q_thread A)) + 1) by (clear; lia); apply CH0; [cbn; clear; lia | exact X1]|].
      split.
      { intros _. rewrite last_app1. cbn [qb_addr nbQ].
        split; [apply (CH 8 8%nat); [clear; lia | cbn; clear; lia | exact X2] | apply (CH 16 8%nat); [clear; lia | cbn; clear; lia | exact X3]]. }
      split; [intros z Hz; destruct (PRES z ltac:(apply CHG_thdr; clear -Hz; lia)) as [b Hb]; exists b; rewrite CHm by (apply CHG_thdr; clear -Hz; lia); exact Hb|].
      replace (qsize (aa_q_thread A ++ [nbQ])) with (qsize (aa_q_thread A) + (n + kQuarantineBatchSize)); [apply (CH 24 8%nat); [clear; lia | cbn; clear; lia | exact X4]|].
      rewrite qsize_app. cbn [qsize fold_right nbQ qb_size]. clear. lia. }
  split; [apply (qhdr_repr_agree mE m3); [intros z Hz; apply AGI; unfold QG, IMG_LO, IMG_HI in *; clear -Hz; lia | exact Q5]|].
  split; [eapply cell_ok_agree; [|exact Q6]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold QG, IMG_LO, IMG_HI; clear -Hk; lia|].
  split; [eapply cell_ok_agree; [|exact Q7]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold QG, IMG_LO, IMG_HI; clear -Hk; lia|].
  split; [exact QSZ|]. split; [exact Q9|].

  change (freeQ q A p n ++ aa_q_global A) with (qall A'). destruct QDEC as [HQ|HQ]; [rewrite (QADDR_A HQ); exact Q10|].
  apply (ND_perm _ _ (QADDR_B HQ)). apply (proj2 (list_relations.list.NoDup_cons _ _)). split; [|exact Q10].
  intros HIN. apply (proj1 (list_elem_of_In _ _)) in HIN. apply in_map_iff in HIN as (qb & Eqb & Hqb).
  pose proof (NBF HQ) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NX & _).
  apply (D_batch_cache qb (top24 A) Hqb NX). rewrite <- QBID_nb. unfold qb_id. rewrite Eqb. reflexivity.
Qed.

Lemma slot_czone : ltac2:(tb__ "0|0|
S0S0S0S7Sb0VG;R3R2R1A4Sc4VSB;R3ScZ10R2A2S8eR3A1R1A5A2Fz;Fx;Fc;").
Proof. intros c x z. unfold slot_zone, czone, region_beg, kRegionSize. fold SB. cbn zeta. tauto. Qed.

Lemma CSLOT : ltac2:(tb__ "0|0|
S0S0S0S1S8Z1R3A2S8R3Z1eA2A2S5cS0R3S1aSa1S16S1cVA';A1R4S1bA4A1A3Sb0VG;R5R4R3A4S1S83R4A1S5F_;S3S2S63Vq;S64A3A1S1S8VnbF;R5A2SaR5S9VnbF;Z2000A2A2A2S5F_;F_;A2F_;F_;F_;Fz;Fx;Fc;").
Proof.
  intros c x z Hc Hx SZ. apply (proj1 (slot_czone c x z)) in SZ.
  pose proof (ECLS_mapped c ltac:(clear -Hc; lia)) as (_ & _ & _ & _ & CIN). pose proof (CIN x Hx) as HxA.
  pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & HPR & _). destruct HPR as (_ & _ & _ & HCR).
  pose proof (HCR c Hc) as Cc. destruct Cc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & _ & _ & _ & _ & N7 & _). fold G SB in N7, M2, M3.
  change (nthZ (aa_cls A) c cs_empty) with (csA c) in N7, M2, M3, HxA.
  destruct (N7 x ltac:(apply in_or_app; right; exact HxA)) as (X0 & XM & XA). unfold kCompactPtrScale in XM, XA. rewrite Z.shiftl_mul_pow2 in XM, XA by (clear; lia).
  change (2 ^ 4) with 16 in XM, XA. rewrite (Z.mul_comm x 16) in XM, XA. unfold kUserSpaceSize, kUserMapSize, kFreeArraySize, kRegionSize in M3.
  pose proof (size_ok_all c Hc) as [SZ1 SZ2].
  split.
  - intros K. refine (CZ_slot c x z Hc X0 ltac:(clear -XA M2 M3; lia) XM _ SZ K).
    intros HP EC E. apply (D_cache_p c x Hc HxA ltac:(unfold Pc; cbn [snd]; rewrite HP, EC, Z.eqb_refl; reflexivity)). rewrite E. unfold idf. cbn [fst snd]. unfold region_beg, kRegionSize. reflexivity.
  - intros HQ Hb. pose proof (NBF HQ) as (N1 & N2 & N3 & N4 & N5 & N6 & N7' & N8' & NM & NX & _).
    refine (T_pp c x (Size c) 24 (top24 A) 8192 z Hc ltac:(clear; lia) X0 ltac:(clear -N2; lia) ltac:(clear -XA M2 M3; lia) ltac:(clear -N6 N7' N8'; lia)
              ltac:(clear -SZ1; lia) ltac:(clear; lia) SZ2 eq_refl XM NM _ _ SZ _).
    + intros ->. reflexivity.
    + destruct (Z.eq_dec c 24) as [->|NC]; [right | left; exact NC]. intros EX. subst x.
      rewrite (ECLS_B24 HQ) in Hx. cbn [cs_cache pop_cls] in Hx. change (cs_cache (csA 24)) with (cache24 A) in Hx.
      pose proof (CND 24 ltac:(clear; lia)) as ND. apply ND_app_r in ND. apply ND_app_l in ND. change (cs_cache (csA 24)) with (cache24 A) in ND.
      rewrite (CACHE_B HQ) in ND. exact (ND_app_disj _ _ (top24 A) (top24 A) ND Hx ltac:(left; reflexivity) eq_refl).
    + unfold czone. cbn zeta. left. rewrite <- N3. exact Hb.
Qed.

Lemma NP_perm : ltac2:(tb__ "0|3|
S42S0S0A2M0S41F_;S40G0A1M1G1Sc3G0R2R1A3Sc3S0S7fG0S0S4dS0S0A2M2S62G0R4R3A3A4S7fG0S0G2S62G0R4R2A3A4A3F_;Fl';Fl;Ff;").
Proof.
  intros f l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2].
  - apply Permutation_refl.
  - cbn. destruct (f x); [cbn; apply perm_skip; exact IH | exact IH].
  - cbn. destruct (f y), (f x); cbn; try apply Permutation_refl. apply perm_swap.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma HI3' : inv3 A'.
Proof.
  pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _). pose proof HI3 as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9). fold G in X1, X3, X4, X5.
  unfold inv3. rewrite EG'. change (aa_sec A') with (aa_sec A). change (aa_depot A') with (aa_depot A). change (aa_live A') with (l1 ++ l2).
  split; [exact X1|].
  split; [intros b m Hin; exact (X2 b m (LIVE_subA b m Hin))|].
  split; [exact X3|].
  split.
  { intros z Hz. unfold q_foot in Hz. change (aa_q_thread A') with (freeQ q A p n) in Hz. change (aa_q_global A') with (aa_q_global A) in Hz.
    pose proof CZI as (I1 & _). destruct GEO as (T1 & T2 & SB1 & _ & _ & _ & ST & TB & _). pose proof BLK as (B1 & _ & B3 & _ & B5 & _ & B7 & B8 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.

    assert (OLDc : q_foot A z -> ~ (T <= z < T + 4096) /\ (forall c x, 1 <= c <= 30 -> In x (cs_cache (nthZ (aa_cls A') c cs_empty)) -> ~ slot_zone G c x z)).
    { intros Hq. destruct (X4 z Hq) as [Y1 Y2]. fold T in Y1. split; [exact Y1|]. intros c x Hc Hx. apply (Y2 c x Hc).
      exact (proj2 (proj2 (proj2 (proj2 (ECLS_mapped c ltac:(clear -Hc; lia))))) x Hx). }
    assert (NEWc : CZ z -> ~ (T <= z < T + 4096) /\ (forall c x, 1 <= c <= 30 -> In x (cs_cache (nthZ (aa_cls A') c cs_empty)) -> ~ slot_zone G c x z)).
    { intros K. split; [|intros c x Hc Hx SZ; exact (proj1 (CSLOT c x z Hc Hx SZ) K)].
      destruct K as [K|K]; [clear -K I1 B8; lia|]. destruct (CZS z K) as [Y _]. clear -Y TB. lia. }
    assert (NBc : q <> QA -> nbF <= z < nbF + 8192 -> ~ (T <= z < T + 4096) /\ (forall c x, 1 <= c <= 30 -> In x (cs_cache (nthZ (aa_cls A') c cs_empty)) -> ~ slot_zone G c x z)).
    { intros HQ Hb. split; [pose proof (NBF HQ) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NT & _); clear -Hb NT; lia|].
      intros c x Hc Hx SZ. exact (proj2 (CSLOT c x z Hc Hx SZ) HQ Hb). }
    assert (ITc : forall it, (it = (p, n) \/ In it (qitems (qall A))) ->
              (fst it - rz (snd it) <= z < fst it \/ Sh (fst it) <= z < Sh (fst it) + (snd it + 7) / 8) ->
              ~ (T <= z < T + 4096) /\ (forall c x, 1 <= c <= 30 -> In x (cs_cache (nthZ (aa_cls A') c cs_empty)) -> ~ slot_zone G c x z)).
    { intros it [->|Hit] Hz'.
      - apply NEWc. cbn [fst snd] in Hz'. unfold CZ. replace (N8 n / 8) with ((n + 7) / 8) by (unfold N8; rewrite Z.div_mul by (clear; lia); reflexivity). clear -Hz' B5 B7. lia.
      - apply OLDc. unfold q_foot. unfold qitems in Hit. apply in_flat_map in Hit as (qb & Hqb & Hit). apply Exists_exists. exists qb. split; [exact Hqb|].
        right. apply Exists_exists. exists it. split; [exact Hit | exact Hz']. }
    apply Exists_exists in Hz as (qb & Hqb & Hz).
    assert (CASES : In qb (qall A) \/ (q = QA /\ qb = lbQ) \/ (q <> QA /\ qb = nbQ)).
    { apply in_app_or in Hqb as [Hqb|Hqb]; [|left; unfold qall; apply in_or_app; right; exact Hqb].
      destruct QDEC as [HQ|HQ].
      - rewrite (FQ_A HQ) in Hqb. apply in_app_or in Hqb as [Hqb|[<-|[]]]; [left; unfold qall; apply in_or_app; left; exact (in_removelast _ _ Hqb) | right; left; split; [exact HQ | reflexivity]].
      - rewrite (FQ_B HQ) in Hqb. apply in_app_or in Hqb as [Hqb|[<-|[]]]; [left; unfold qall; apply in_or_app; left; exact Hqb | right; right; split; [exact HQ | reflexivity]]. }
    destruct CASES as [Hold | [[HQ ->] | [HQ ->]]].
    - destruct Hz as [Hz|Hz]; [apply OLDc; apply Exists_exists; exists qb; split; [exact Hold | left; exact Hz]|].
      apply Exists_exists in Hz as (it & Hit & Hz). apply (ITc it); [right; unfold qitems; apply in_flat_map; exists qb; split; [exact Hold | exact Hit] | exact Hz].
    - pose proof (QBF (QNE ltac:(rewrite HQ; discriminate))) as (QIN & _).
      destruct Hz as [Hz|Hz].
      + apply OLDc. apply Exists_exists. exists (lastq A). split; [apply in_or_app; left; exact QIN | left; exact Hz].
      + apply Exists_exists in Hz as (it & Hit & Hz). cbn [lbQ qb_items] in Hit. apply in_app_or in Hit as [Hit|[<-|[]]].
        * apply (ITc it); [right; unfold qitems; apply in_flat_map; exists (lastq A); split; [unfold qall; apply in_or_app; left; exact QIN | exact Hit] | exact Hz].
        * apply (ITc (p, n)); [left; reflexivity | exact Hz].
    - destruct Hz as [Hz|Hz]; [apply (NBc HQ); cbn [qb_addr nbQ] in Hz; unfold kQuarantineBatchSize in Hz; exact Hz|].
      apply Exists_exists in Hz as (it & Hit & Hz). cbn [nbQ qb_items] in Hit. destruct Hit as [<-|[]]. apply (ITc (p, n)); [left; reflexivity | exact Hz]. }
  split; [exact X5|].
  split.
  {
    rewrite HLV in X6. rewrite !filter_app in X6 |- *. cbn [List.filter] in X6. rewrite !map_app in X6 |- *.
    eapply ND_perm; [|exact X6].
    eapply Permutation_trans; [apply Permutation_app_head; apply NP_perm; exact QITEMS'|].
    cbn [List.filter fst snd]. destruct (negb (is_primary n)); cbn [map app fst].
    - rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_sym. cbn [app]. apply Permutation_middle.
    - apply Permutation_refl. }

  assert (LL : large_live A' = large_live A - (if 64513 <=? n then 1 else 0)) by (apply (large_live_remove A A' l1 l2 p n HLV); reflexivity).
  assert (QL : qlarge A' = qlarge A + (if 64513 <=? n then 1 else 0)).
  { unfold qlarge. pose proof (Permutation_length (NP_perm is_large _ _ QITEMS')) as PL. rewrite !length_map in PL. rewrite PL.
    cbn [List.filter]. unfold is_large at 1. cbn [snd]. destruct (64513 <=? n); cbn [length]; lia. }
  split; [rewrite LL, QL; clear -X7; destruct (64513 <=? n); lia|].

  split.
  { assert (SL : small_live A' = small_live A - (if 64513 <=? n then 0 else 1)) by (apply (small_live_remove A A' l1 l2 p n HLV); reflexivity).
    rewrite SL. clear -X8. destruct (64513 <=? n); lia. }
  intros _. change (aa_cache_inited A') with (aa_cache_inited A). destruct QDEC as [HQ|HQ]; [|exact (proj1 (QB24 HQ))].
  apply X9. pose proof QC as Y. unfold qcond in Y. rewrite HQ in Y. destruct Y as [Y _]. intros E. apply app_eq_nil in E as [E _]. exact (Y E).
Qed.

Lemma HA' : ltac2:(tb__ "0|0|
S6dVQBD;VA';Vrho3;Vtp;Vmd;A5").
Proof.
  pose proof HA as (HG & _). unfold AInvB. rewrite EG'. fold v3. split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|].
  split; [|split; [exact HMD | split; [exact HI3' | exact HBTP]]].
  fold m3. split; [exact HLS|]. split; [exact HLB|]. split; [exact HPR|]. split; [exact HSR|]. split; [exact HQR|].
  split; [exact HDEP|]. split; [exact HIA|]. split; [exact HTI | exact HMI].
Qed.

Lemma client_not_rtF : ltac2:(tb__ "0|0|
S0S53SabR1VA';A2ScfVCST;VA';R3A3S3S6eVG;R4A2A1F_;F_;Fm;Fa;").
Proof.
  intros a m HF Hcl [R|R]; pose proof HA as (HG & _); [exact (client_not_rt CST HCST A' a m HG HF HLS Hcl R)|].
  assert (LOW : a < IMG_HI) by (destruct R as [R|R]; [pose proof (IMG_F_lt a R); clear -H; lia | unfold IA_BEG, IA_END, IMG_HI in *; clear -R; lia]).
  destruct (client_addr_cases CST A' a m HF Hcl) as [S|[L|[FR|[C|FL]]]]; destruct GEO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TG & F1 & _).
  - change (aa_geom A') with G in S. unfold IMG_HI in LOW. clear -S LOW TG. lia.
  - destruct L as (b & m' & Hbn & Hx). destruct (HLS b m' Hbn) as (S1 & S2 & _). unfold IMG_HI in S2, LOW. clear -Hx S2 LOW. lia.
  - destruct FR as (c & p0 & Hc & Hp & _ & Hx). pose proof (fs_geom_nums G c p0 HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. change (aa_geom A') with G in Hx. unfold IMG_HI in LOW. clear -Hx M LOW F1. lia.
  - exact (HCSTF _ C R).
  - destruct FL as (c & p0 & Hc & Hp & _ & ->). pose proof (fs_geom_nums G c p0 HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. change (aa_geom A') with G in LOW. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *.
    unfold IMG_HI in LOW. clear -M LOW F1. lia.
Qed.

Lemma NOC : ltac2:(tb__ "0|0|
S0ScfVCST;VA';R1A3S1S3S66Vq;VA;Vp;Vn;R2A5A1S83R2A1S5F_;A2F_;Fy;").
Proof.
  intros y Hy. pose proof HA as (HG & _). pose proof HFS as HF'. destruct GEO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TG & F1 & F2 & _).
  pose proof BLK as (B1 & _ & _ & B4 & _ & _ & _ & B8 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  destruct (client_addr_cases CST A' y _ HF' Hy) as [S|[L|[FR|[C|FL]]]].
  - change (aa_geom A') with G in S. split; [apply NCH_top; clear -S; lia|]. intros K. destruct (CZN y K) as [K'|K']; clear -S K' TG; lia.
  - destruct L as (b & m' & Hbn & Hyb). change (aa_live A') with (l1 ++ l2) in Hbn. pose proof (rz_bound m') as RB.
    split; [apply (NCH_live b m' y Hbn); left; clear -Hyb RB; lia | intros K; apply (CZ_live b m' y Hbn); [left; clear -Hyb RB; lia | exact K]].
  - destruct FR as (c & p0 & Hc & Hp & _ & Hyf). pose proof (fs_geom_nums G c p0 HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. change (aa_geom A') with G in Hyf.
    assert (FT : fs_footb G y = true) by (apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA.fs_footb_true2; rewrite FS_kFlagsOffset_val, FS_total_val; clear -Hyf M; lia).
    split; [intros Hc'; rewrite (CHF y Hc') in FT; discriminate|].
    intros K. destruct K as [K|K]; [pose proof (CZA y K) as (_ & _ & _ & X & _) | pose proof (CZS y K) as [_ X]]; rewrite X in FT; discriminate.
  - destruct (HCST _ C) as [X _]. split; [apply NCH_img; exact X|]. intros K. destruct (CZN y K) as [K'|K']; unfold IMG_LO, IMG_HI in X; clear -X K'; lia.
  - destruct FL as (c & p0 & Hc & Hp & _ & ->). pose proof (fs_geom_nums G c p0 HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. change (aa_geom A') with G. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *.
    set (yy := ag_fsb G + 4096 + fs_flags_off_nat (Z.to_nat c) + p0) in *.
    assert (FT : fs_footb G yy = true) by (apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA.fs_footb_true2; rewrite FS_kFlagsOffset_val, FS_total_val; clear -M; lia).
    split; [intros Hc'; rewrite (CHF _ Hc') in FT; discriminate|].
    intros K. destruct K as [K|K]; [pose proof (CZA _ K) as (_ & _ & _ & X & _) | pose proof (CZS _ K) as [_ X]]; rewrite X in FT; discriminate.
Qed.

Lemma HKEPT : ltac2:(tb__ "0|0|
SceVCST;VXGL;VA;VA';S7cVrhoE;A1S7cVrho3;A1A6").
Proof.
  pose proof HA as (HG & _ & HF & (Hsep & _) & _). fold G in HG. fold vE G in HF.
  pose proof BLK as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  destruct GEO as (_ & _ & SB1 & _ & _ & _ & _ & TB & _ & TG & _).
  split.
  2: { intros x0 j Hx Hj Hdef. unfold word_byte. apply DEFM; [|exact Hdef].
       pose proof (Z.mod_pos_bound (Sh x0) 8 ltac:(clear; lia)) as MB. pose proof (Z.div_mod (Sh x0) 8 ltac:(clear; lia)) as DM.
       assert (Bx : 0 <= x0 < 2 ^ 47).
       { destruct Hx as [[CX _]|GX]; [exact (proj1 (client_addr_bounds CST HCST A x0 _ HG HF Hsep CX))|].
         destruct (HXGL x0 GX) as [XG1 XG2]. unfold IMG_HI in XG2. clear -XG1 XG2. lia. }
       unfold Sh, SHADOW_OFF, IMG_HI in DM, MB |- *. pose proof (Z.div_le_mono 0 x0 8 ltac:(clear; lia) ltac:(clear -Bx; lia)) as D0.
       pose proof (Z.div_lt_upper_bound x0 8 (2 ^ 44) ltac:(clear; lia) ltac:(clear -Bx; lia)) as D1. change (0 / 8) with 0 in D0.
       clear -Hj DM MB D0 D1. lia. }
  intros a Ha Hcl. apply RMO; [exact Ha| |].
  - destruct Hcl as [(_ & CL' & _)|(_ & CL' & _)]; [exact (proj1 (NOC a CL'))|].
    pose proof (client_shadow_bounds CST XGL HCST HXGL A' a _ HG HFS HLS CL') as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
    intros Hc. destruct (CHGE a Hc) as [K|[K|[K|K]]].
    + pose proof PRZ as PZ. destruct K as [K|K]; [clear -K B PZ; lia|].

      destruct (proj1 (Z.mod_divide p 8 ltac:(clear; lia)) B10) as [u Hu]. destruct (proj1 (Z.mod_divide (N8 n) 8 ltac:(clear; lia)) B6) as [w Hw].
      destruct CL' as [(y & Cy & Ey)|(y & Gy & Ey)].
      * destruct (NOC y Cy) as [_ NY]. apply NY. left. subst a. unfold Sh in K. rewrite Hu, Hw in K. rewrite !Z.div_mul in K by (clear; lia).
        pose proof (Z.div_mod y 8 ltac:(clear; lia)) as DM. pose proof (Z.mod_pos_bound y 8 ltac:(clear; lia)) as MB. clear -K Hu Hw DM MB B8. lia.
      * destruct (HXGL y Gy) as [Y1 Y2]. subst a. unfold IMG_HI in Y2. unfold Sh in K. rewrite Hu in K. rewrite Z.div_mul in K by (clear; lia).
        pose proof (Z.div_le_mono y 6578176 8 ltac:(clear; lia) ltac:(clear -Y2; lia)) as D1. change (6578176 / 8) with 822272 in D1. clear -K D1 Hu B1. lia.
    + unfold TZ in K. clear -K B TB. lia.
    + destruct K as [HNE K]. pose proof (QBF HNE) as (_ & _ & Q3 & _). clear -K B Q3 SB1. lia.
    + destruct K as [HQ K]. pose proof (NBF HQ) as (_ & _ & _ & _ & N5 & _). clear -K B N5 SB1. lia.
  - destruct Hcl as [(_ & CL' & _)|(_ & CL' & _)]; [exact (client_not_rtF a _ HFS CL')|].
    pose proof (client_shadow_bounds CST XGL HCST HXGL A' a _ HG HFS HLS CL') as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
    pose proof (geom_bands _ HG) as (WF & TB' & CB & DB & _). fold G T in WF, TB', CB, DB.
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB', CB, DB. rewrite FS_total_val in WF.
    intros [R|[R|R]]; [|pose proof (IMG_F_lt a R) as X; unfold IMG_HI in X; clear -B X; lia | unfold IA_BEG, IA_END in R; clear -B R; lia].
    unfold rt_zone, IMG_HI in R. clear -R B WF TB' CB DB. lia.
Qed.

Lemma HCLSK : cls_kept_freeA A A'.
Proof.
  intros c Hc NE Hfr. unfold class_fresh in Hfr |- *. change (nth (Z.to_nat c) (aa_cls A') cs_empty) with (nthZ (aa_cls A') c cs_empty).
  rewrite (ECLS_same c ltac:(clear -Hc; lia) ltac:(intros _ E; exact (NE E))). exact Hfr.
Qed.
Lemma free_rebuild_in : ltac2:(tb__ "0|2|
S1S6dVQBD;VA';Vrho3;Vtp;Vmd;A5S1S2S40S42S0S0A2M0A1M1S1eVA';A1S3fG0Vl1;Vl2;A3A3S1S2G1S2bVA';A1S2bVA;A1A3S1S2S0S27VA';A1S27VA;A1A3S1S2S0S26VA';A1S26VA;A1A3S1S2S0S25VA';A1S25VA;A1A3S1S2S19S1dVA';A1S1dVA;A1A3S1SceVCST;VXGL;VA;VA';S7cVrhoE;A1S7cVrho3;A1A6S38VA;VA';A2A2A2A2A2A2A2A2A2").
Proof.
  split; [exact HA'|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [exact HKEPT | exact HCLSK].
Qed.
End RB.

Theorem free_rebuild_B : ltac2:(tb__ "0|1|
S40S42S0S0A2A1M0G0S58R2A1S5aR2A1S0S54R5R1A2S4S54S6cR2A2S1S8Sa8R2A2SaR2Sa9A2A2A2S5F_;F_;Fa;S74R5R4A2F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HCF QB q A rhoE rho3 tp md p n l1 l2 t HA HLV HHI Hii QC. cbn zeta. intros Ht Ht4 VHW VHL PRES LC VO RMO DEFM QSZ.
  eapply free_rebuild_in; eassumption.
Qed.
Theorem free_rebuild : ltac2:(tb__ "0|1|
S40S42S0S0A2A1M0G0S58R2A1S5aR2A1S0S54R5R1A2S4S54S6cR2A2S1S8Sa8R2A2SaR2Sa9A2A2A2S5F_;F_;Fa;S73R5R4A2F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HCF q A rhoE rho3 tp md p n l1 l2 t HA HLV HHI Hii QC. cbn zeta. intros Ht Ht4 VHW VHL PRES LC VO RMO DEFM QSZ.
  exact (free_rebuild_B CST XGL HC HX HCF kQuarantineCacheMax q A rhoE rho3 tp md p n l1 l2 t HA HLV HHI Hii QC Ht Ht4 VHW VHL PRES LC VO RMO DEFM QSZ).
Qed.
