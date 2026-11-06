(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "pow"; "modulo"; "mul"; "div"; "eqb"; "leb"; "to_nat"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "False"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "bool"; "option"; "Some"; "andb"; "app"; "true"; "cons"; "nat"; "snd"; "None"; "false"; "fst"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "in_rangesZ"; "cell_ok"; "mkACell"; "view"; "RTC_A"; "cells_footb"; "rtc_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "class_state"; "sec_chunk"; "ageom"; "qbatch"; "aa_live"; "aa_sec"; "aa_cls"; "cs_empty"; "ag_thread"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "ag_spacebeg"; "aa_cache_inited"; "cs_allocated_user"; "cs_cache"; "cs_free_array"; "cs_mapped_user"; "aa_Kf"; "aa_V"; "aa_internal_inited"; "cs_mapped_free_array"; "sc_map_beg"; "sc_map_size"; "aa_Km"; "aa_frames"; "ag_ctx"; "ag_pab"; "mkAA"; "qb_items"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "ag_dtls"; "ag_fsb"; "cls_keptA"; "cs_n_allocated"; "cs_n_freed"; "depot_state"; "list_upd"; "mkCS"; "prim_room"; "qb_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "rz"; "ClassID"; "IMG_HI"; "is_primary"; "needed"; "region_beg"; "IMG_LO"; "Size"; "free_array"; "region_info"; "SHADOW_OFF"; "max_count"; "round_up"; "@Stdlib.Lists.List"; "In"; "nth_error"; "removelast"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "nthZ"; "live_ids"; "class_repr"; "alloc_magic_ok"; "geom_ok"; "live_sep"; "AInvA"; "QG"; "present_but"; "q_foot"; "qhdr_repr"; "qlinks"; "quarantine_repr"; "secondary_repr"; "SEC_INST"; "fs_footb"; "fs_inv"; "ia_inv"; "inv3"; "misc_inv"; "sep_geom3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "sv"; "valuation"; "SLit"; "rw"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "chg_m"; "czone"; "IMG_M"; "rt_zoneM"; "cz_env"; "lit_ranges"; "cls_foot"; "cls_meta"; "cls_ok9"; "pop_cls"; "rz_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "needed8"; "cnt_of"; "N_m1"; "chk_of"; "cst_of"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "@stdpp.base"; "NoDup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "client_addrA"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM"; "rt_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue"; "spec_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4"; "sep_geom"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality Sorting.Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition cls_ok9 (n : Z) : bool := ltac2:(tb__ "0|0|
S18S9S59S5cVn;A1A1S59S93Vn;A1A1A2S5bVn;A1A2").
Lemma cls_ok9_all : ltac2:(tb__ "0|0|
S0ScS1Z1R1A2S1R1Zfc00A2A2SdS15S8eR2A1S1aA3F_;Fn;").
Proof. intros n Hn. apply (forall_rangeZ_ok cls_ok9 1 64512); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cls_needed : ltac2:(tb__ "0|0|
S0ScS1Z1R1A2S1R1Zfc00A2A2ScSdS0S59S5cR2A1A1S92R2A1A3SdS15S5bR2A1S1aA3A2F_;Fn;").
Proof.
  intros n Hn. pose proof (cls_ok9_all n Hn) as H. unfold cls_ok9, cls_of in *.
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. auto.
Qed.

Definition pop_cls (cs : class_state) : class_state := ltac2:(tb__ "0|0|
S54S3dVcs;A1S3aVcs;A1S3cVcs;A1S41Vcs;A1S67S0S3bVcs;A1A2S50Vcs;A1S51Vcs;A1A7").

Definition mallocA (A : AA) (c ub nv kmo : Z) : AA := ltac2:(tb__ "0|1|
S48S2bVA;A1S53S2cS32VA;A1M0SbVc;A1S8fS6bS2cG0Vc;S33A4A1A4S39VA;A1S31VA;A1S35VA;A1S1bS13S0S0A2S14S0S0Vub;Vnv;A4S30VA;A1A3S37VA;A1S36VA;A1S4aVA;A1S4cVA;A1S4bVA;A1S40VA;A1S2S3fVA;A1Vnv;A2Vkmo;S3eVA;A1Af").

Lemma last_nth : forall {T} (l : list T) (d : T), last l d = nth (length l - 1) l d.
Proof.
  intros T l d. induction l as [|a l IH]; [reflexivity|]. cbn [last length]. destruct l as [|b l']; [reflexivity|].
  rewrite IH. cbn [length]. replace (S (S (length l')) - 1)%nat with (S (length l')) by lia.
  replace (S (length l') - 1)%nat with (length l') by lia. reflexivity.
Qed.
Lemma removelast_split : forall {T} (l : list T) (d : T), (0 < length l)%nat -> l = removelast l ++ [nth (length l - 1) l d].
Proof.
  intros T l d Hl. rewrite <- last_nth. apply app_removelast_last. intros ->. cbn in Hl. lia.
Qed.
Lemma removelast_len : forall {T} (l : list T) (d : T), (0 < length l)%nat -> length (removelast l) = (length l - 1)%nat.
Proof.
  intros T l d Hl. pose proof (removelast_split l d Hl) as E.
  apply (f_equal (@length T)) in E. rewrite length_app in E. cbn [length] in E. lia.
Qed.
Lemma nth_error_removelast : forall {T} (l : list T) (d : T) i, (i < length l - 1)%nat -> nth_error (removelast l) i = nth_error l i.
Proof.
  intros T l d i Hi. rewrite (removelast_split l d) at 2 by lia. rewrite nth_error_app1; [reflexivity|]. rewrite (removelast_len l d) by lia. exact Hi.
Qed.
Lemma in_removelast : forall {T} (l : list T) x, In x (removelast l) -> In x l.
Proof.
  intros T l x H. destruct l as [|a l']; [exact H|].
  rewrite (removelast_split (a :: l') a) by (cbn; lia). apply in_or_app. left. exact H.
Qed.

Lemma sep_geom3_sep : ltac2:(tb__ "0|0|
S2eS7fR1A1Sa0R2A1F_;FG;").
Proof. intros G (H1 & H2 & _). split; assumption. Qed.

Definition chg_m (G : ageom) (pce ab ub ue sz cnt : Z) (z : Z) : Prop := ltac2:(tb__ "0|5|
SeScS1Vpce;Vz;A2S3Vz;S2Vpce;Z4M0A2A2A2SeScS1S2Vpce;Z8M1A2Vz;A2S3Vz;S2Vpce;Z10A2M2A2A2SeScS1S2G2S7G0S4Vcnt;Z1A2A2A2Vz;A2S3Vz;S2Vpce;Z50A2A2A2SeScS1S2S34VG;A1M3Zad0A2Vz;A2S3Vz;S2G3Zc60A2A2A2SeScS1Vab;Vz;A2S3Vz;Vub;A2A2SeScS1Vue;Vz;A2S3Vz;S2Vab;Vsz;A2A2A2ScS1S57Vab;A1M4Vz;A2S3Vz;S2G4S8Vsz;G1A2A2A2A2A2A2A2A2A2A2").

Lemma nth_error_Some_lt : forall {T} (l : list T) i x, nth_error l i = Some x -> (i < length l)%nat.
Proof. intros T l i x H. apply (proj1 (nth_error_Some l i)). rewrite H. discriminate. Qed.

Definition maxc_ok (c : Z) : bool := max_count c <=? 16.
Lemma max_count_le16 : ltac2:(tb__ "0|0|
S0ScS1Z1R1A2S1R1Z1eA2A2S1S63R2A1Z10A2F_;Fc;").
Proof. intros c Hc. pose proof (forall_rangeZ_ok maxc_ok 1 30 c ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(lia)) as H. unfold maxc_ok in H. apply Z.leb_le in H. exact H. Qed.

Definition cls_foot (G : ageom) (c : Z) (cs : class_state) (z : Z) : Prop := ltac2:(tb__ "0|4|
S61S38VG;A1M0Vc;A2S0S5dG0Vc;A2S0S60G0Vc;A2S0SeScS1R3Vz;A2S3Vz;S2R3Z80A2A2A2SeScS1R1Vz;A2S3Vz;S2R1S41Vcs;A1A2A2A2SeScS1R2Vz;A2S3Vz;S2R2S3dVcs;A1A2M1A2A2SeScS1S57R2A1Vz;A2S3Vz;S57G1A1A2A2ScS1S2S2S34VG;A1Zd0A2S7Z50M2Vc;A2A2M3Vz;A2S3Vz;S2G3G2A2A2A2A2A2A2A2Tfa;Trb;Tri;").

Definition cls_meta (G : ageom) (c : Z) (cs : class_state) (z : Z) : Prop := ltac2:(tb__ "0|3|
S61S38VG;A1M0Vc;A2S0S5dG0Vc;A2S0S60G0Vc;A2S0SeScS1R3Vz;A2S3Vz;S2R3Z80A2A2A2SeScS1R1Vz;A2S3Vz;S2R1S41Vcs;A1A2A2A2SeScS1S57R2A1Vz;A2S3Vz;S57S2R2S3dVcs;A1A2A1A2A2ScS1S2S2S34VG;A1Zd0A2S7Z50M1Vc;A2A2M2Vz;A2S3Vz;S2G2G1A2A2A2A2A2A2Tfa;Trb;Tri;").

Lemma class_repr_agree_gen : ltac2:(tb__ "0|3|
S22S22S2eS2aS2aS0S2cScS1Z1R2A2S1R2Z1eA2A2SdS15S39R4A1S39R5A1A3SdS12S0A1S6cR7R5R4A3S6cR7R6R4A3A3SdS12S2fA1S91R6A1S91R7A1A3S0S0S65S13S0S0A2M0S14S0S0R2R1A4S30R9A1M1A3SdS15S5bR2A1S1aA3SdS0S59S5cR3A1A1RaA3S65G0S14S0S0R5R4A4S30RdA1A3F_;F_;F_;Fn;Fb;S0S8dRbR8R7R1A4SdS16S68Q8A1A1RdR2A1ReR2A1A3F_;Fz;S73RcS5dS38RbA1R8A2M2S2G2S3dR7A1A2G1A4S6dReRcRbR9R8A5S6dReRdRbRaR9A5F_;F_;F_;F_;F_;F_;F_;F_;Fcs;Fc;FA';FA;FG;Fm';Fm;").
Proof.
  intros m m' G A A' c cs Hc Hci Hli Hq Hlv AG PU' P4.
  assert (CA : forall cc, (forall k, (k < c_w cc)%nat -> cls_meta G c cs (c_addr cc + Z.of_nat k)) -> cell_ok m cc -> cell_ok m' cc).
  { intros cc Hf. apply cell_ok_agree. intros k Hk. apply AG. exact (Hf k Hk). }
  unfold class_repr in P4 |- *. rewrite Hci. rewrite Hli. rewrite Hq.
  set (ri := region_info (ag_spacebeg G) c) in *. set (fa := free_array (ag_spacebeg G) c) in *. set (rb := region_beg (ag_spacebeg G) c) in *.
  destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & C9 & PR & N7 & PU & PS & PE & ND & LV & CI & CN & TI10 & CV10 & MC10 & FC10).
  assert (FRI : forall off w, 0 <= off -> off + Z.of_nat w <= 72 -> forall k, (k < w)%nat -> cls_meta G c cs (ri + off + Z.of_nat k)).
  { intros off w Ho Hw k Hk. left. unfold ri in *. lia. }
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mutex; lia | exact C1]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_num_freed; lia | exact C2]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_free_array; lia | exact C3]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_user; lia | exact C4]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_meta; lia | exact C5]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_user; lia | exact C6]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_meta; lia | exact C7]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_exhausted; lia | exact C8]|].
  split; [eapply present_agree; [|exact PRI]; intros z Hz; apply AG; left; unfold ri in *; unfold kRegionInfoStride in Hz; lia|].
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
  split.
  { intros i x Hi. apply CA; [|exact (C9 i x Hi)]. cbn [c_addr c_w]. intros k Hk. right; left.
    pose proof (nth_error_Some_lt _ _ _ Hi) as L. unfold fa in *. lia. }
  split; [eapply present_agree; [|exact PR]; intros z Hz; apply AG; right; left; unfold fa in *; lia|].
  split; [exact N7|].
  split; [exact PU'|].
  split; [eapply present_agree; [|exact PS]; intros z Hz; apply AG; right; right; left; unfold rb in *; lia|].
  split; [eapply present_agree; [|exact PE]; intros z Hz; apply AG; right; right; right; lia|].
  split; [exact ND|].
  split; [intros b n Hin Hp Hcl; exact (LV b n (Hlv b n Hin Hp Hcl) Hp Hcl)|].
  split.
  - intros Hi. destruct (CI Hi) as (K1 & K2 & K3 & K4 & K5). split; [|split; [|split; [|split; [|exact K5]]]].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; right; lia | exact K1].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; right; lia | exact K2].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; right; lia | exact K3].
    + intros i x Hi'. apply CA; [|exact (K4 i x Hi')]. cbn [c_addr c_w]. intros k Hk. right; right; right.
      pose proof (nth_error_Some_lt _ _ _ Hi') as L. pose proof (max_count_le16 c Hc). lia.
  - split; [|exact (conj TI10 (conj CV10 (conj MC10 FC10)))].
    intros Hn. destruct (CN Hn) as [K1 K2]. split; [exact K1|]. eapply filled_agree; [|exact K2]. intros z Hz. apply AG. right; right; right. lia.
Qed.

Lemma class_repr_agree : ltac2:(tb__ "0|2|
S22S22S2eS2aS2aS0S2cScS1Z1R2A2S1R2Z1eA2A2SdS15S39R4A1S39R5A1A3SdS12S0A1S6cR7R5R4A3S6cR7R6R4A3A3SdS12S2fA1S91R6A1S91R7A1A3S0S0S65S13S0S0A2M0S14S0S0R2R1A4S30R9A1A3SdS15S5bR2A1S1aA3SdS0S59S5cR3A1A1RaA3S65G0S14S0S0R5R4A4S30RdA1A3F_;F_;F_;Fn;Fb;S0S23S30RaA1M1R1A2S23G1R2A2F_;Fz;S0S8cRcR9R8R1A4SdS16S68Q8A1A1ReR2A1RfR2A1A3F_;Fz;S6dReRcRbR9R8A5S6dReRdRbRaR9A5F_;F_;F_;F_;F_;F_;F_;F_;Fcs;Fc;FA';FA;FG;Fm';Fm;").
Proof.
  intros m m' G A A' c cs Hc Hci Hli Hq Hlv HLm AG P4.
  apply (class_repr_agree_gen m m' G A A' c cs Hc Hci Hli Hq Hlv); [| | exact P4].
  - intros z [H|[H|[H|H]]]; apply AG; unfold cls_foot; [left | right; left | right; right; right; left | right; right; right; right]; exact H.
  - destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PU & _).
    eapply present_but_mono; [exact HLm | | exact PU]. intros z Hz _ Hm. rewrite AG by (unfold cls_foot; right; right; left; exact Hz). exact Hm.
Qed.

Definition rz_okb (n : Z) : bool := ltac2:(tb__ "0|3|
S18S18S18S18SaZ10M0S58Vn;A1M1A2SaG1Z400A2A2S9S6G1G0A2Z0A2A2SaS2Vn;G1A2S93Vn;A1M2A2A2SaG2S5fS92Vn;A1A1A2A2").
Lemma rz_okb_all : ltac2:(tb__ "0|0|
S0ScS1Z1R1A2S1R1Zfc00A2A2SdS15S90R2A1S1aA3F_;Fn;").
Proof. intros n Hn. apply (forall_rangeZ_ok rz_okb 1 64512); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma rz_facts : ltac2:(tb__ "0|3|
S0ScS1Z1R1A2S1R1Zfc00A2A2ScScS1Z10M0S58R2A1M1A2S1G1Z400A2A2ScSdS0S6G1G0A2Z0A3ScS1S2R2G1A2S93R2A1M2A2S1G2S5fS92R2A1A1A2A2A2A2F_;Fn;").
Proof.
  intros n Hn. pose proof (rz_okb_all n Hn) as H. unfold rz_okb in H.
  repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with K : (_ <=? _) = true |- _ => apply Z.leb_le in K | K : (_ =? _) = true |- _ => apply Z.eqb_eq in K end. lia.
Qed.

Fixpoint lit_ranges (N : list carve_spec) : list (Z * Z) :=
  match N with
  | [] => []
  | (b, lo, hi, _) :: N' => if sv_eqb b (SLit 0) then (lo, hi - lo) :: lit_ranges N' else lit_ranges N'
  end.
Definition IMG_M : list (Z * Z) := lit_ranges N_m1.
Definition rt_zoneM (G : ageom) (a : Z) : Prop := ltac2:(tb__ "0|0|
SeS9eVG;Va;A2S23S88Va;A2A2").

Lemma lit_ranges_in : ltac2:(tb__ "0|4|
S12S13S13S13S81S0A2M0S0A2M1S12S13S13S0S1cA2S81A2A1M2A2M3A1S0S0G2S65G3S14G1G2S14G0S0S14S81S0S83Z0A1R3A4R2A4R1A4R4A3S65S13S0S0A2S14S0S0R4S4R3R4A2A4S8bR5A1A3F_;Fcs;Fhi;Flo;FNN;").
Proof.
  induction NN as [|[[[b l] h] c] NN IH]; intros lo hi cs Hin; [destruct Hin|].
  cbn [lit_ranges]. destruct Hin as [E|Hin].
  - injection E as -> -> -> ->. cbn. left. reflexivity.
  - destruct (sv_eqb b (SLit 0)); [right|]; eapply IH; exact Hin.
Qed.
Lemma lit_ranges_inv : ltac2:(tb__ "0|3|
S12S9aA1S0S0S65S13S0S0A2S14S0S0R2R1A4S8bR3A1A3S10S12S13S13S0S1cA2S81A2A1M0G0S65S13S13S13S81S0A2M1S0A2M2G0A2S14G2G0S14G1S0S14S81S0S83Z0A1R4A4S2R4R3A2A4R1A4R5A3Lcs;A2F_;Fn;Flo;FNN;").
Proof.
  induction NN as [|[[[b l] h] c] NN IH]; intros lo n Hin; [destruct Hin|].
  cbn [lit_ranges] in Hin. destruct (sv_eqb b (SLit 0)) eqn:E.
  - apply sv_eqb_sound in E. subst b. destruct Hin as [E|Hin].
    + injection E as E1 E2. subst lo n. exists c. left. f_equal. f_equal. f_equal. lia.
    + destruct (IH lo n Hin) as [cs H]. exists cs. right. exact H.
  - destruct (IH lo n Hin) as [cs H]. exists cs. right. exact H.
Qed.

Lemma N_m1_zone : ltac2:(tb__ "0|3|
S2eS82S9aS0S6fR4A1SdS68Q40M0A1M1S84R4P97A2S69G0S34R5A1A2A3SdG1S84R5P98A2S69G0S46R6A1A2A3S65S9aR5S95A3ScS1S20S0S0S9fR7R6A2M2A3R5A2S3R5S1dS0S0G2A3A2A2S89R9R6A2F_;F_;F_;F_;F_;Fa;Fk;Frho;FG;").
Proof.
  intros G rho k a HG E151 E152 Hk Ha.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). pose proof (topG_range G) as ACV.
  pose proof Hk as HkN.
  unfold N_m1, N_rest, N_fn, N_m5 in Hk. cbn [tl app In] in Hk. unfold vT, vCTX, vTOP, vBOT, vSB, vRIS in Hk.
  repeat (destruct Hk as [E|Hk];
    [subst k; cbn [spec_range fst snd eval] in Ha; rewrite ?E151, ?E152, ?u64_lit in Ha by lia;
     first [ right; unfold IMG_M; eexists; eexists; split; [eapply lit_ranges_in; exact HkN | cbn; lia]
           | left; unfold rt_zone; lia ]
    |]).
  destruct Hk.
Qed.

Lemma fs_footb_T : ltac2:(tb__ "0|1|
S2eS0S6fR2A1ScS1S34R3A1M0R2A2S3R2S2G0Z1000A2A2A2SdS15S7aR4R3A2S1fA3F_;F_;Fz;FG;").
Proof.
  intros G z HG Hz. exact (fs_footb_thread G z HG Hz).
Qed.

Lemma secondary_repr_agree_gen : ltac2:(tb__ "0|7|
S22S22S2aS2aSdS2eS2bR1A1S2bR2A1A3SdS12S2dA1S31R2A1S31R3A1A3SdS0S35R3A1S35R4A1A3S1cS2dS0SdS16S2dA1M0S66S2dS31R8A1R3A3S17S2dR2A2A3SeScS1S42R3A1M1R2A2S3R2S2G1Z20A2A2A2ScS1S57G1A1R2A2S3R2S57S2G1S43R3A1A2A1A2A2A2SdS16S68Q8A1A1M2RbR3A1RcR3A1A3F_;F_;Fz;Fch;Fi;S0ScS1S47S2bR7A1A1M3R1A2S3R1S2G3S35R7A1A2A2A2SdG2R9R2A1RaR2A1M4A3F_;Fz;S0ScS1S79R1A2S3R1Zee070A2A2SdG2G4RbR2A1A3F_;Fz;S1cS2dSdG0S66S2dS31RaA1R2A3S17S2dR1A2A3S73RcS42R2A1M5S2G5S43R2A1A2S30RaA1A4F_;Fch;Fi;S78RbR9A2M6G6F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EG ES EP AG1 AG2 AGI PB' (S1 & SP & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold secondary_repr. rewrite EG, ES, EP.
  assert (CI : forall cc, SEC_INST <= c_addr cc -> c_addr cc + Z.of_nat (c_w cc) <= 0xee070 -> cell_ok m cc -> cell_ok m' cc).
  { intros cc H1 H2. apply cell_ok_agree. intros k Hk. apply AGI. lia. }
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (nth_error_Some_lt _ _ _ Hi) as L.
    assert (MS : 0 <= sc_map_size ch) by (unfold PG in D8; lia).
    assert (CA : forall off w v, 0 <= off -> off + Z.of_nat w <= 32 -> cell_ok m (mkACell (sc_map_beg ch + off) w v) -> cell_ok m' (mkACell (sc_map_beg ch + off) w v)).
    { intros off w v Ho Hw. apply cell_ok_agree. cbn [c_addr c_w]. intros k Hk. apply (AG1 i ch); [exact Hi | left; lia]. }
    split; [apply CA; [lia| cbn; lia | exact C1]|]. split; [apply CA; [lia| cbn; lia | exact C2]|].
    split; [apply CA; [lia| cbn; lia | exact C3]|]. split; [apply CA; [lia| cbn; lia | exact C4]|].
    split; [eapply cell_ok_agree; [|exact C5]; cbn [c_addr c_w]; intros k Hk; apply AG2; lia|].
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [exact (PB' i ch Hi)|].
    eapply present_agree; [|exact D14]; intros z Hz; apply (AG1 i ch); [exact Hi | right; exact Hz]. }
  split; [eapply present_agree; [|exact SP]; intros z Hz; apply AG2; pose proof (Zle_0_nat (length (aa_sec A))); lia|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S45|].
  unfold SEC_INST, IMG_LO, IMG_HI in *.
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I1]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I2]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I3]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I4]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I5]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I6]|].
  split; [eapply present_agree; [|exact I7]; intros z Hz; apply AGI; lia|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I8]|].
  eapply present_agree; [|exact I9]; intros z Hz; apply AGI; lia.
Qed.

Lemma secondary_repr_agree : ltac2:(tb__ "0|7|
S22S22S2aS2aSdS2eS2bR1A1S2bR2A1A3SdS12S2dA1S31R2A1S31R3A1A3SdS0S35R3A1S35R4A1A3S1cS2dS0SdS16S2dA1S66S2dS31R8A1R3A3S17S2dR2A2A3SeScS1S42R3A1M0R2A2S3R2S2G0S43R3A1A2M1A2A2ScS1S57G0A1R2A2S3R2S57G1A1A2A2A2SdS16S68Q8A1A1M2RbR3A1RcR3A1A3F_;F_;Fz;Fch;Fi;S0ScS1S47S2bR7A1A1M3R1A2S3R1S2G3S35R7A1A2A2A2SdG2R9R2A1RaR2A1M4A3F_;Fz;S0ScS1S5eR1A2S3R1S5aA2A2SdG2G4RbR2A1A3F_;Fz;S0S23S30R9A1M5R1A2S23G5R2A2F_;Fz;S78RbR9A2M6G6F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EG ES EP AG1 AG2 AGI HLm HS.
  apply (secondary_repr_agree_gen m m' A A' EG ES EP); [| exact AG2 | intros z Hz; apply AGI; unfold SEC_INST, IMG_LO, IMG_HI in *; lia | | exact HS].
  - intros i ch z Hi Hz. apply (AG1 i ch z Hi). destruct Hz as [Hz|Hz]; [left | right; exact Hz].
    destruct HS as (S1 & _). destruct (S1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & _). unfold PG in D8. lia.
  - intros i ch Hi. destruct HS as (S1 & _). destruct (S1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D13 & _).
    eapply present_but_mono; [exact HLm | | exact D13]. intros z Hz _ Hm. rewrite (AG1 i ch z Hi (or_introl Hz)). exact Hm.
Qed.

Lemma alloc_magic_ok_agree : ltac2:(tb__ "0|1|
S22S22S0S0S0ScS1S4R3S58R2A1M0A2R1A2S3R1R3A2A2SdS16S68Q8A1A1R5R2A1R6R2A1A3F_;Fz;S1Z10G0A2S6eR6R4R3A3S6eR6R5R4A3F_;F_;F_;Fn;Fu;Fm';Fm;").
Proof.
  intros m m' u n AG Hrz [H|[H1 H2]]; [left; exact H|right].
  split; (eapply cell_ok_agree; [|eassumption]; cbn [c_addr c_w]; intros k Hk; apply AG; lia).
Qed.

Lemma qlinks_agree : ltac2:(tb__ "0|1|
S22S22S12S2fA1S2fS0S65S2fR2R3A3ScS1S56R3A1M0R2A2S3R2S2G0Z8A2A2A2SdS16S68Q8A1A1R6R3A1R7R3A1A3F_;F_;Fz;Fb;S76R4R2A2S76R4R3A2F_;F_;Fl;Fm';Fm;").
Proof.
  intros m m' l. induction l as [|b r IH]; intros AG H; [exact I|]. cbn in H |- *. destruct H as [H1 H2]. split.
  - eapply cell_ok_agree; [|exact H1]. cbn [c_addr c_w]. intros k Hk. apply (AG b); [left; reflexivity | lia].
  - apply IH; [|exact H2]. intros b0 z Hb0 Hz. apply (AG b0); [right; exact Hb0 | exact Hz].
Qed.

Lemma qhdr_repr_agree : ltac2:(tb__ "0|0|
S22S22S0S12S2fA1S0ScS1R3R1A2S3R1S2R3Z20A2A2A2SdS16S68Q8A1A1R5R2A1R6R2A1A3F_;Fz;S75R5R3R2A3S75R5R4R3A3F_;F_;Fl;Fhdr;Fm';Fm;").
Proof.
  intros m m' hdr l AG (H1 & H2 & H3 & H4). unfold qhdr_repr.
  split; [eapply cell_ok_agree; [|exact H1]; cbn [c_addr c_w]; intros k Hk; apply AG; lia|].
  split; [intros Hl; destruct (H2 Hl) as [X Y]; split; (eapply cell_ok_agree; [|eassumption]; cbn [c_addr c_w]; intros k Hk; apply AG; lia)|].
  split; [eapply present_agree; [|exact H3]; intros z Hz; apply AG; lia|].
  eapply cell_ok_agree; [|exact H4]; cbn [c_addr c_w]; intros k Hk; apply AG; lia.
Qed.

Lemma quarantine_repr_agree_gen : ltac2:(tb__ "0|8|
S22S22S2aS2aSdS2eS2bR1A1S2bR2A1A3SdS12S2dA1S31R2A1S31R3A1A3SdS12S2fA1M0S37R3A1S37R4A1A3SdG0S36R4A1S36R5A1A3S0SdS0S3aS6bS2cS32R6A1R1S33A4A1S3aS6bS2cS32R7A1R1S33A4M1A1A3Fc;S0SdS12S0A1S3cG1A1S3cS6bS2cS32R8A1R1S33A4A1A3Fc;S0S0S65S0R1S3bS6bS2cS32R9A1R2S33A4A1A3S65S0R2S3bS6bS2cS32RbA1R3S33A4A1A3F_;Fx;Fc;S70R9A1S85S2fS2fS85S13S0S0A2M2G2S1Z10S58S1dS0S0R1A3A1A2Lit;S49R1A1A3Lqb;S19S2fS37RaA1S36RaA1A3A3S0S74RcR1A2SdS16S68Q8A1A1M3ReR2A1RfR2A1M4A3F_;Fz;S0ScS1S2S34S2bRdA1A1M5Z50A2R1A2S3R1S2G5Z70A2A2A2SdG3G4R10R2A1M6A3F_;Fz;S0ScS1S2S72Z40A2R1A2S3R1S2S72Zc0A2A2A2SdG3G6R11R2A1A3F_;Fz;S77R10ReA2M7G7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EG ES ET EGq EAU EFA ECA _ HRZ AG AGT AGI (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  unfold quarantine_repr. rewrite EG, ET, EGq.
  assert (FQ : forall qb z, In qb (aa_q_thread A ++ aa_q_global A) ->
            (qb_addr qb <= z < qb_addr qb + kQuarantineBatchSize)
            \/ Exists (fun it : Z * Z => (fst it - rz (snd it) <= z < fst it) \/ (Sh (fst it) <= z < Sh (fst it) + (snd it + 7) / 8)) (qb_items qb) -> m' z = m z).
  { intros qb z Hqb Hz. apply AG. unfold q_foot. apply Exists_exists. exists qb. split; [exact Hqb | exact Hz]. }
  split.
  { apply Forall_forall. intros qb Hqb. pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (proj1 (Forall_forall _ _) HRZ qb Hqb) as RZb.
    unfold batch_repr. rewrite EG. unfold kQuarantineBatchSize in *.
    split; [exact B0|]. split; [eapply cell_ok_agree; [|exact B1]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
    split; [eapply cell_ok_agree; [|exact B2]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
    split; [exact B3|]. split; [exact B4|].
    split; [eapply present_agree; [|exact B5]; intros z Hz; apply (FQ qb); [exact Hqb | left; lia]|].
    split.
    - intros i it Hi. destruct (B6 i it Hi) as [I1 I2]. pose proof (nth_error_Some_lt _ _ _ Hi) as L. pose proof (nth_error_In _ _ Hi) as Hin.
      unfold kQuarantineBatchCount in B3.
      split; [eapply cell_ok_agree; [|exact I1]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
      pose proof (proj1 (Forall_forall _ _) RZb it Hin) as RZi. cbn in RZi.
      unfold q_item_ok in I2 |- *. cbn zeta in I2 |- *. rewrite EG, ES, EAU.
      destruct I2 as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11).
      assert (AGi : forall z, fst it - rz (snd it) <= z < fst it -> m' z = m z).
      { intros z Hz. apply (FQ qb); [exact Hqb|]. right. apply Exists_exists. exists it. split; [exact Hin | left; exact Hz]. }
      split; [exact J1|]. split; [exact J2|].
      split; [rewrite AGi by lia; exact J3|].
      split; [eapply present_agree; [|exact J4]; intros z Hz; apply AGi; lia|].
      split; [eapply cell_ok_agree; [|exact J5]; cbn [c_addr c_w]; intros k Hk; apply AGi; lia|].
      split; [eapply cell_ok_agree; [|exact J6]; cbn [c_addr c_w]; intros k Hk; apply AGi; lia|].
      split; [eapply present_agree; [|exact J7]; intros z Hz; apply AGi; lia|].
      split; [apply (alloc_magic_ok_agree m m'); [exact AGi | exact RZi | exact J8]|].
      split; [exact J9|]. split; [exact J10|].
      assert (0 <= (snd it + 7) / 8) by (apply Z.div_pos; lia).
      eapply present_agree; [|exact J11]. intros z Hz. apply (FQ qb); [exact Hqb|]. right. apply Exists_exists. exists it. split; [exact Hin | right; lia].
    - destruct B7 as (x & E1 & E2 & E3 & E4). exists x. rewrite EAU. split; [exact E1|]. split; [exact E2|]. split; [exact E3 | exact E4]. }
  assert (HB : forall b z, In b (aa_q_thread A ++ aa_q_global A) -> qb_addr b <= z < qb_addr b + 8 -> m' z = m z).
  { intros b z Hb Hz. apply (FQ b); [exact Hb | left; unfold kQuarantineBatchSize; lia]. }
  split; [apply (qlinks_agree m m'); [intros b z Hb Hz; apply (HB b); [apply in_or_app; left; exact Hb | exact Hz] | exact Q2]|].
  split; [apply (qlinks_agree m m'); [intros b z Hb Hz; apply (HB b); [apply in_or_app; right; exact Hb | exact Hz] | exact Q3]|].
  split; [apply (qhdr_repr_agree m m'); [intros z Hz; apply AGT; lia | exact Q4]|].
  split; [apply (qhdr_repr_agree m m'); [intros z Hz; apply AGI; unfold QG in *; lia | exact Q5]|].
  split; [eapply cell_ok_agree; [|exact Q6]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold QG; lia|].
  split; [eapply cell_ok_agree; [|exact Q7]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold QG; lia|].
  split; [exact Q8 | exact Q9].
Qed.

Lemma quarantine_repr_agree : ltac2:(tb__ "0|8|
S22S22S2aS2aSdS2eS2bR1A1S2bR2A1A3SdS12S2dA1S31R2A1S31R3A1A3SdS12S2fA1M0S37R3A1S37R4A1A3SdG0S36R4A1S36R5A1A3S0SdS0S3aS6bS2cS32R6A1R1S33A4A1S3aS6bS2cS32R7A1R1S33A4M1A1A3Fc;S0SdS12S0A1S3cG1A1S3cS6bS2cS32R8A1R1S33A4A1A3Fc;S0S0S65S0R1S3bS6bS2cS32R9A1R2S33A4A1A3S65S0R2S3bS6bS2cS32RbA1R3S33A4A1A3F_;Fx;Fc;S70R9A1S85S2fS2fS85S13S0S0A2M2G2S1Z10S58S1dS0S0R1A3A1A2Lit;S49R1A1A3Lqb;S19S2fS37RaA1S36RaA1A3A3S0S74RcR1A2SdS16S68Q8A1A1M3ReR2A1RfR2A1M4A3F_;Fz;S0ScS1S2S34S2bRdA1A1M5Z50A2R1A2S3R1S2G5Z70A2A2A2SdG3G4R10R2A1M6A3F_;Fz;S0ScS1S5eR1A2S3R1S5aA2A2SdG3G6R11R2A1A3F_;Fz;S77R10ReA2M7G7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EG ES ET EGq EAU EFA ECA HLS HRZ AG AGT AGI HQ.
  apply (quarantine_repr_agree_gen m m' A A' EG ES ET EGq EAU EFA ECA HLS HRZ AG AGT); [|exact HQ].
  intros z Hz. apply AGI. unfold QG, IMG_LO, IMG_HI in *. lia.
Qed.

Lemma ia_inv_agree : ltac2:(tb__ "0|1|
S22S22S2aS2aSdS15S40R1A1S40R2A1A3S0ScS1S5eR1A2S3R1S5aA2A2SdS16S68Q8A1A1R6R2A1R7R2A1A3F_;Fz;S7cR6R4A2M0G0F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EI AG H. unfold ia_inv in *. rewrite EI. unfold IA_MAP1, IA_MAP1_SZ, IA_BEG, IA_END, IMG_LO, IMG_HI in *.
  rewrite !AG by lia. destruct H as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  destruct (aa_internal_inited A); destruct H4 as [H5 H6]; (split; [exact H5|]); intros z Hz; rewrite AG by lia; exact (H6 z Hz).
Qed.

Lemma misc_inv_agree : ltac2:(tb__ "0|1|
S22S22S0ScS1S5eR1A2S3R1S5aA2A2SdS16S68Q8A1A1R3R2A1R4R2A1A3F_;Fz;S7eR3A1M0G0F_;F_;Fm';Fm;").
Proof.
  intros m m' AG (H1 & H2 & H3). split; [|split].
  - eapply cells_ok_frame; [|exact H1]. intros z Hz. apply AG. unfold cells_footb in Hz.
    apply existsb_exists in Hz as (c & Hc & Hin). unfold in_cellb in Hin. apply andb_prop in Hin as [X Y].
    apply Z.leb_le in X. apply Z.ltb_lt in Y. unfold rtc_extra in Hc.
    destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn in X, Y; unfold IMG_LO, IMG_HI; lia.
  - intros z Hz. rewrite AG by (unfold IMG_LO, IMG_HI; lia). exact (H2 z Hz).
  - intros z Hz. rewrite AG by (unfold ERRNO_A, IMG_LO, IMG_HI in *; lia). exact (H3 z Hz).
Qed.

Lemma live_ids_cons : ltac2:(tb__ "0|4|
S2eS2aS0S0S0S12S2cA1S15S12S2dA1S0S12S2fA1M0G0S52S12S0A1M1S12S12S13S0S0A2M2A1A1S15S0S0S0SdG1S6cR12S48S2bR11A1RdRcRbRaS1bG2S14S0S0R10RfA4S30R11A1A3R9R8R7R6R5R4R3R2R1AfReA3S15G1L_;S18S5bRfA1S9S59S5cRfA1A1ReA2A2S1bS0S8S4S4R10S58RfA1A2S5dS38R12A1ReA2A2Z10A2S6cR12R11ReA3M3A3G3X15x2A3FKf;FKm;FV;Fii;Fbs;Fh;Fdp;Fqg;Fqt;Fpc;Fsec;Fci;Fcls;Fc;Fn;Fb;FA;FG;").
Proof. intros. unfold live_ids. cbn [aa_live filter list_basics.list.list_filter decide Is_true_dec fst snd]. destruct (is_primary n && (ClassID (needed n) =? c)); reflexivity. Qed.
Lemma live_ids_in : ltac2:(tb__ "0|0|
S2eS2aS0S0S0S65S13S0S0A2S14S0S0R3R2A4S30R4A1A3SdS15S18S5bR3A1S9S59S5cR3A1A1R2A2A2S1aA3S65S0S8S4S4R5S58R4A1A2S5dS38R7A1R3A2A2Z10A2S6cR7R6R3A3A3F_;F_;Fc;Fn;Fb;FA;FG;").
Proof.
  intros G A b n c Hin Hb. unfold live_ids. apply in_map_iff. exists (b, n). split; [reflexivity|].
  apply (proj1 (list_elem_of_In _ _)). apply (proj2 (list_basics.list.list_elem_of_filter _ _ _)).
  split; [cbn [snd]; rewrite Hb; exact I|]. apply list_elem_of_In. exact Hin.
Qed.
Lemma NoDup_move : ltac2:(tb__ "0|1|
S12S0A1M0G0G0S0S9bS0S19S0R4S19S0S19S0R3S1bS0R1S21S0A1A3A3R2A3A3A2S9bS0S19S0R5S19S0R4S1bS0R2R3A3A3A3A2F_;Fx;Fl3;Fl2;Fl1;").
Proof.
  intros l1 l2 l3 x H.
  assert (P : Permutation (l1 ++ (l2 ++ [x]) ++ l3) (l1 ++ l2 ++ x :: l3)).
  { rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. cbn. apply Permutation_refl. }
  rewrite <- P. exact H.
Qed.

Lemma round_up_ge : ltac2:(tb__ "0|0|
S0S0S3Z0R1A2S1R3S64R3R2A2A2F_;Fm;Fz;").
Proof.
  intros z m Hm. unfold round_up. pose proof (Z.div_mod (z + m - 1) m ltac:(lia)) as D. pose proof (Z.mod_pos_bound (z + m - 1) m Hm) as B. nia.
Qed.

Lemma mod0_apart : ltac2:(tb__ "0|1|
S0S0S0S3Z0M0R1A2SdS0S6R4R2A2G0A3SdS0S6R4R3A2G0A3SfSdS0R6R5A3A1SeS1S2R7R5A2R6A2S1S2R6R5A2R7A2A2F_;F_;F_;F_;Fs;Fb;Fa;").
Proof.
  intros a b s Hs Ha Hb Hne.
  destruct (proj1 (Z.mod_divide a s ltac:(lia)) Ha) as [p ->]. destruct (proj1 (Z.mod_divide b s ltac:(lia)) Hb) as [q ->].
  assert (p <> q) by (intros ->; apply Hne; reflexivity). nia.
Qed.

Definition czone (SB c o sz : Z) (z : Z) : Prop := ltac2:(tb__ "0|1|
S2S2VSB;S7Vc;S5Z2Z20A2A2A2Vo;A2S0SeScS1R1Vz;A2S3Vz;S2R1Vsz;A2A2A2ScS1S57R1A1M0Vz;A2S3Vz;S2G0S8Vsz;Z8A2A2A2A2A2Tab;").
Lemma czone_disj : ltac2:(tb__ "0|8|
S0S0S0S0S0S0S0S0S1Z10007fff8000R8A2S1S2S2R9S5Z2M0Z25A2A2Z1000A2Z7fffff800000A2SdS0S6RaZ8M1A2Z0M2A3ScS1G2RaA2M3S1RaZ1eA2A2M4G4G3S1S2RbR9A2S4S5G0Z20A2S5G0Z1dA2A2M5A2S1G2RbA2S1S2RcRaA2G5A2S3G2RcA2M6G6SdS0S6R10G1A2G2A3M7G7G7G7SeSfSdS0R16R15A3A1SeS1S2R14R12A2R13A2S1S2R13R11A2R14A2A2A2S87R18R17R15R13R11A5S87R19R17R15R13R12A5S11F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fz;Fsz';Fsz;Fo';Fo;Fc';Fc;FSB;").
Proof.
  intros SB c c' o o' sz sz' z S1 S2 S8 Hc Hc' Ho Hosz Ho' Hosz' Hsz Hsz' Mo Mo' Ms Ms' SEP Z1 Z2.
  unfold czone, Sh, SHADOW_OFF in Z1, Z2.
  destruct (proj1 (Z.mod_divide SB 8 ltac:(lia)) S8) as [q Hq].
  destruct (proj1 (Z.mod_divide o 8 ltac:(lia)) Mo) as [p Hp]. destruct (proj1 (Z.mod_divide o' 8 ltac:(lia)) Mo') as [p' Hp'].
  destruct (proj1 (Z.mod_divide sz 8 ltac:(lia)) Ms) as [s Hs]. destruct (proj1 (Z.mod_divide sz' 8 ltac:(lia)) Ms') as [s' Hs'].
  subst SB o o' sz sz'.
  replace ((q * 8 + c * 2 ^ 32 + p * 8) / 8) with (q + c * 2 ^ 29 + p) in Z1 by (apply Z.div_unique with 0; lia).
  replace ((q * 8 + c' * 2 ^ 32 + p' * 8) / 8) with (q + c' * 2 ^ 29 + p') in Z2 by (apply Z.div_unique with 0; lia).
  rewrite Z.div_mul in Z1, Z2 by lia.
  assert (CC : c = c' \/ c + 1 <= c' \/ c' + 1 <= c) by lia.
  destruct CC as [->|[CC|CC]]; [destruct SEP as [SEP|SEP]; [lia|]| |]; nia.
Qed.

Definition cz_env (SB c x sz top : Z) : Prop := ltac2:(tb__ "0|3|
ScS1Z10007fff8000VSB;A2ScS1S2S2VSB;S5Z2M0Z25A2A2Z1000A2Vtop;A2ScSdS0S6VSB;Z8A2Z0M1A3ScScS1Z1Vc;A2S1Vc;Z1eA2A2ScS1G1Vx;A2ScS1Z10M2Vsz;A2ScSdS0S6Vsz;G2A2G1A3ScS1S2S7G2Vx;A2Vsz;A2S4S5G0Z20A2S5G0Z1dA2A2A2ScS1Z7fff7f800000Vtop;A2S1Vtop;Z7fffff800000A2A2A2A2A2A2A2A2A2A2").
Lemma Sh_SB : ltac2:(tb__ "0|1|
S0S0SdS0S6R2Z8M0A2Z0A3SdS0S57S2R3R2A2A1S2S57R3A1S8R2G0A2A2A3F_;Fk;FSB;").
Proof.
  intros SB k H. unfold Sh. destruct (proj1 (Z.mod_divide SB 8 ltac:(lia)) H) as [q Hq]. subst SB.
  rewrite Z.div_add_l by lia. rewrite Z.div_mul by lia. lia.
Qed.
Lemma czone_env : ltac2:(tb__ "0|6|
S0S0S0S0S0S0S8aR6R5R4R3R2A5S87R7R6S7Z10R5A2R4R2A5SeScScS1S2R8S7R7S5Z2M0Z20A2M1A2A2M2R3A2S3R3S2G2S4G1S5G0Z1dA2M3A2A2A2A2ScS1Z10007fff8000M4R3A2S3R3S4R4Z1000A2A2A2A2ScScS1S2S57R8A1S7R7G3A2A2M5R3A2S3R3S2G5S4G3S5G0Z1aA2A2A2A2A2ScS1S62R3A2S3R3G4A2A2A2A2F_;F_;Fz;Ftop;Fsz;Fx;Fc;FSB;").
Proof.
  intros SB c x sz top z (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & ET) Hz. unfold czone in Hz.
  rewrite <- !Z.add_assoc in Hz. rewrite !Sh_SB in Hz by exact E3.
  replace ((c * 2 ^ 32 + 16 * x) / 8) with (c * 2 ^ 29 + 2 * x) in Hz by (apply Z.div_unique with 0; lia).
  destruct (proj1 (Z.mod_divide sz 16 ltac:(lia)) E7) as [s Hs]. subst sz.
  replace (s * 16 / 8) with (2 * s) in Hz by (apply Z.div_unique with 0; lia).
  destruct Hz as [Hz|Hz]; [left; lia | right].
  assert (SHB : SHADOW_OFF + 17594333495296 / 8 <= Sh SB /\ Sh SB + 2 ^ 34 + 512 <= SHADOW_OFF + 140737479966720 / 8).
  { unfold Sh. pose proof (Z.div_le_mono 17594333495296 SB 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (SB + 2 ^ 37 + 4096) 140737479966720 8 ltac:(lia) ltac:(lia)) as D.
    replace (SB + 2 ^ 37 + 4096) with (SB + (2 ^ 34 + 512) * 8) in D by lia. rewrite Z.div_add in D by lia. lia. }
  unfold SHADOW_OFF in *. cbn in SHB. lia.
Qed.
Lemma czone_rgn : ltac2:(tb__ "0|5|
S0S0S0S0S0S0S0S8aR7R6R5R4R3A5ScS1Z0R3A2S1R3Z1fA2A2SfSdS0R4R8A3A1S87RaR9S7Z10R8A2R7R4A5SeScS1S2RbS7R6S5Z2M0Z20A2M1A2A2M2R5A2S3R5S2G2G1A2M3A2A2SeScS1S57G2A1R5A2S3R5S57G3A1A2A2ScS1S2RbS5G0Z25A2A2M4R5A2S3R5S2G4Z1000A2A2A2A2A2S11F_;F_;F_;F_;F_;Fz;Fc';Ftop;Fsz;Fx;Fc;FSB;").
Proof.
  intros SB c x sz top c' z HE Hc' Hne Hz HR. pose proof HE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & ET).
  apply (czone_env SB c x sz top z HE) in Hz. rewrite <- !Z.add_assoc in HR. rewrite !Sh_SB in HR by exact E3.
  replace ((c' * 2 ^ 32 + 2 ^ 32) / 8) with (c' * 2 ^ 29 + 2 ^ 29) in HR by (apply Z.div_unique with 0; lia).
  replace ((c' * 2 ^ 32) / 8) with (c' * 2 ^ 29) in HR by (apply Z.div_unique with 0; lia).
  assert (SHB : Sh SB + 2 ^ 34 + 512 <= SHADOW_OFF + 140737479966720 / 8).
  { unfold Sh. pose proof (Z.div_le_mono (SB + 2 ^ 37 + 4096) 140737479966720 8 ltac:(lia) ltac:(lia)) as D.
    replace (SB + 2 ^ 37 + 4096) with (SB + (2 ^ 34 + 512) * 8) in D by lia. rewrite Z.div_add in D by lia. lia. }
  unfold SHADOW_OFF in *. cbn in SHB.
  assert (CC : c' + 1 <= c \/ c + 1 <= c') by lia. destruct CC; lia.
Qed.

Lemma chg_cases : ltac2:(tb__ "0|2|
S2eS0S0S0S0S0S0S0S1Z1R2A2S86R9R8R7R6R5R4R3R2A8SeScS1R9R3A2S3R3S2R9Z50A2A2A2SeScS1S2S34RaA1M0Zad0A2R3A2S3R3S2G0Zc60A2A2A2SeScS1R8R3A2S3R3R7A2A2SeScS1R6R3A2S3R3S2R8R5A2A2A2ScS1S57R8A1M1R3A2S3R3S2G1S8R5Z8A2A2A2A2A2A2A2A2F_;F_;Fz;Fcnt;Fsz;Fue;Fub;Fab;Fpce;FG;").
Proof. intros G pce ab ub ue sz cnt z Hc H. unfold chg_m in H. lia. Qed.

Lemma rtc_foot_cases : ltac2:(tb__ "0|4|
S2eS0SdS15S28S29S27R2A2R1A2S1aA3SeScS1S5eR2A2S3R2S5aA2A2SeScS1S34R3A1M0R2A2S3R2S2G0Z50A2A2A2SeScS1S46R3A1M1R2A2S3R2S2G1Za0A2A2A2SeScS1S4dR3A1M2R2A2S3R2S2G2Z20A2A2A2ScS1S4eR3A1M3R2A2S3R2S2G3Z61A2A2A2A2A2A2A2F_;Fz;FG;").
Proof.
  intros G z Hz. unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin).
  unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
  unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
  - left. unfold rtc_cells_img in Hc. unfold IMG_LO, IMG_HI.
    repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; lia|]). destruct Hc.
  - right. unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc.
    repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; lia|]). destruct Hc.
Qed.

Lemma IMG_M_lt : ltac2:(tb__ "0|0|
S0S23S88R1A2ScS1Z0R2A2S3R2S5aA2A2F_;Fa;").
Proof.
  intros a (b & n & Hin & Hr). unfold IMG_M in Hin. destruct (lit_ranges_inv N_m1 b n Hin) as [cs K].
  pose proof (proj1 (Forall_forall _ _) N_m1_small _ K) as (_ & _ & S3 & _). unfold IMG_HI.
  unfold N_m1, N_rest, N_fn, N_m5 in K. cbn [tl app In] in K.
  repeat (destruct K as [E|K]; [injection E; intros; subst; lia|]). destruct K.
Qed.

Lemma AInvA_die : ltac2:(tb__ "0|0|
S2aS82S12S68Q40A1A1S98S71S99R4R3R2R1A5S24S26S99S80R4A1A2S25Z182f1cU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & _ & _ & _ & _ & [HC _]).
  unfold rtc_extra in HC. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HC)))) as X.
  intros k Hk. specialize (X k Hk). cbn [c_addr c_w c_val] in X, Hk |- *.
  rewrite maskv_out in X; [exact X | apply fs_footb_img; [exact HG | lia]].
Qed.
Lemma AInvA_inv3 : ltac2:(tb__ "0|0|
S2aS82S12S68Q40A1A1S98S71S99R4R3R2R1A5S7dR5A1F_;Fmd;Ftp;Frho;FA;").
Proof. intros A rho tp md (_ & _ & _ & _ & _ & H & _). exact H. Qed.

Section R.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0S23VCST;R1A2S23S88R2A2S11F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Lemma client_not_rtM : ltac2:(tb__ "0|0|
S2aS0S22S6fS2bR3A1A1S7bR2R4A2S70R5A1S9cVCST;R6R5A3SfS89S2bR7A1R6A2A1F_;F_;F_;F_;Fm;Fa;FA;").
Proof.
  intros A a m HG HF Hsep Hcl [R|R]; [exact (client_not_rt CST HCST A a m HG HF Hsep Hcl R)|].
  assert (LOW : a < IMG_HI) by (pose proof (IMG_M_lt a R); lia).
  destruct (client_addr_cases CST A a m HF Hcl) as [S|[L|[FR|[C|FL]]]]; pose proof (topG_range (aa_geom A)) as ACV.
  - unfold IMG_HI in LOW. lia.
  - destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in S2. unfold IMG_HI in LOW. lia.
  - destruct FR as (c & p & Hc & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in M. unfold IMG_HI in LOW. lia.
  - exact (HCSTM _ C R).
  - destruct FL as (c & p & Hc & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *. unfold IMG_HI in M. unfold IMG_HI in LOW. lia.
Qed.

Lemma malloc_rebuild : ltac2:(tb__ "0|13|
S2aS82S82S12S68Q40M0A1A1S98S0S0ScS1S44R7A1M1R1A2S1R1S2G1Z1M2A2A2A2VAInv;R8R7R5R4A4ScS1G2R4A2S1R4Zfc00A2A2S1G2S94RaR5A2A2S55RbA1S2bRcA1S2eS34R1A1S0S92R9A1S0S97RfRaA2S2cS94R10RbA2S0S96R11RcA2S0S5fR4A1S0S2S5dS38R7A1R5A2S7Z10M3R2A2A2S0S2R1S58RfA1A2S0S2R1R10A2S0S2S2R9Zd0A2S7Z50R8A2A2S0S26Vsegs;S80R15A1A2S22S26Vsegs;S80R17A1A2S22S24R2S25R3U4M4S4R9G2A2A3A2S24R3S25S2R4Z8M5A2U8R8A3A2SdS16S68Q8M6A1M7A1M8R4S4R7G3A2A1S17G7S69G6Z2M9A2A2A3S24R5S25S4R8ZcA2G4R17A3A2S24R6S25S4R9ZeA2U2Z0MaA3A2S10G7G7ScSdG8R8S4RbZfA2A1S17G7R1A2MbA3SdS0S6S6aG6R1A2Z4A2G2A3A2Lt;A2S0ScS1GaR1A2McS3R1S8R1bG5A2A2A2SdG8RaS2S57RdA1MdR2A2A1S17G7S69G6GaA2A2A3F_;Fg;SfSdS0S6R1bG5A2GaA3A1SdG8RaS2GdS8R1cG5A2A2A1S17G7S69G6S6R1cG5A2A2A2A3F_;S6eRaRdR1cA3S0S86R17RdR10RfReR11R13R1A8S10G7G7SdG8ReR3A1GbA3Lb;A2F_;Fz;S0SfS86R18ReR11R10RfR12R14R1A8A1SdG8ReR2A1RdR2A1A3F_;Fz;S0ScGcS3R1S5G9Z40A2A2MeA2SfS86R1aR10R13R12R11R14R16R2A8A1SfS89R1bR3A2A1SdG8S80R26S69G0R4A2MfA2S80R27GfA2A3F_;F_;F_;Fa;S0ScS1S5aR1A2GeA2SfSdG8S80R26S69G0R2A2A2S1eG7A1M10A3A1SfSdG8S80R26S69G0R3A2A2G10A3A1F_;F_;Fa;S10S2aS2aScVAInv;R1R25R24R23A4ScSdS12S13S0S0A2M11A1M12S30R1A1S1bG11S14S0S0R13R22A4S30R27A1A3A3ScSdG12S45R1A1S45R27A1A3ScSdS0S3fR1A1S2S3fR27A1R22A2A3ScSdS0S44R1A1R21A3ScSdS0S3eR1A1S3eR27A1A3ScSdS2eS2bR1A1S2bR27A1A3ScS9dVCST;VXGL;R27R1S80R26A1S80R25A1A6S4fR27R1R22A3A2A2A2A2A2A2A2A2LA';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TvE;Tv3;Tpce;Tue;Tub;Tab;Tsz;Tx;Tcnt;Tcs;Tc;TT;TG;F_;F_;F_;F_;F_;Fkmo;Fnv;Fmd;Ftp;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp md nv kmo HKMO HA Hnv Hcnt HPRM G T c cs cnt x sz ab ub ue pce v3 vE VC VS VH2 VHN VH0 VH1 VZ VP VMG PRES VO RMO DEFM.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB). fold vE in HR, HF, HRest. fold G in HG, HR, HF, HRest.
  pose proof (cls_facts nv Hnv) as (C1 & C2 & C3 & C4). fold c in C1, C2, C3, C4. fold sz in C2, C3.
  pose proof (rz_facts nv Hnv) as (Z1 & Z2 & Z3). fold c sz in Z3.
  pose proof (cls_needed nv Hnv) as [CN CP]. fold c in CN.
  pose proof (blk_facts segs A rhoE tp md nv HA Hnv Hcnt) as BF. cbn zeta in BF. fold G c x sz ab vE in BF.
  destruct BF as (X1 & X2 & X3 & X4 & X5 & PU0 & PS0).
  pose proof (pc_entry_facts segs A rhoE tp md nv HA Hnv Hcnt) as PF. cbn zeta in PF. fold G T c cnt x sz vE in PF. fold pce in PF.
  destruct PF as (HCI & _ & _ & _ & CNT16 & _ & PE80 & PST).
  pose proof HG as HG0. pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & TG).
  fold G in G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16, G17, TG. fold T in G4, G5, G10, G13, G14.

  assert (GS : 17594333495296 <= ag_spacebeg G /\ ag_spacebeg G + 2 ^ 37 + 4096 <= topG G /\ ag_spacebeg G mod 2 ^ 16 = 0
               /\ (ag_fsb G + 11571200 <= ag_spacebeg G \/ ag_spacebeg G + 2 ^ 37 + 4096 <= ag_fsb G)).
  { pose proof (geom_old _ HG) as X. rewrite FS_total_val, kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G in X. clear -X. tauto. }
  destruct GS as (S1 & S2 & S3 & S4).
  pose proof (geom_bands _ HG) as (WF & TB & CB & DB & TI & _ & _). fold G T in TB, TI. fold G in WF, CB, DB.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in WF, TB, CB, DB, TI. rewrite FS_total_val in WF.
  pose proof HI3 as HI3c. destruct HI3 as (SG3 & LIV3 & SEC3 & Q3 & DEP3 & ND3). fold G in SG3, SEC3, Q3, DEP3.
  destruct SG3 as (T3 & CTX3 & DTLS3 & PAB3 & PABT3 & _). rewrite kSpaceSize_val in T3, CTX3, DTLS3, PAB3, SEC3. fold T in T3, PABT3.
  pose proof TG as ACV.
  set (SB := ag_spacebeg G) in *.
  assert (ERB : region_beg SB c = SB + c * 2 ^ 32) by reflexivity.
  unfold kUserSpaceSize, kRegionSize, kFreeArraySize in X4. rewrite kSpaceSize_val in X5. unfold kRegionSize in X5.

  destruct HRest as (Hsep & Hlive & Hprim & Hsec & Hq & Hdep & Hia & HTH & Hmisc).
  destruct Hprim as (PL & P0 & P31 & PC).
  pose proof (PC c C1) as PCc. fold G in PCc. change (nthZ (aa_cls A) c cs_empty) with cs in PCc.

  assert (AR : 16 <= rz nv <= 1024 /\ rz nv mod 16 = 0 /\ nv + rz nv <= sz /\ 16 <= sz <= 65536 /\ sz mod 16 = 0 /\ 1 <= c <= 30
               /\ 0 <= x < 2 ^ 28 /\ (16 * x) mod sz = 0 /\ SB <= ab /\ ab = SB + c * 2 ^ 32 + 16 * x /\ 16 * x + sz <= 2 ^ 32 - 2 ^ 29
               /\ 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G /\ SB mod 8 = 0
               /\ 4096 <= T /\ T + 4096 <= topG G /\ (T + 4096 <= SB \/ SB + 2 ^ 37 + 4096 <= T)
               /\ 1 <= cnt <= 16 /\ pce = T + 208 + 80 * c /\ ub = ab + rz nv /\ ue = ub + nv /\ 1 <= nv <= 64512
               /\ 140735332483072 <= topG G <= 140737479966720).
  { assert (SB mod 8 = 0) by (apply Z.mod_divide; [clear -ACV; lia|]; apply (Z.divide_trans _ (2 ^ 16)); [exists (2 ^ 13); reflexivity | apply Z.mod_divide; clear -S3; lia]).
    clear -Z1 Z2 Z3 C1 C2 C3 X1 X2 X3 X4 ERB S1 S2 G4 G5 T3 Hcnt CNT16 Hnv H ACV. unfold ab, ub, ue, pce. rewrite ERB. lia. }
  clear G1 G11 G12 G15 G16 X3 X4 X5.

  assert (CHGE : forall z, chg_m G pce ab ub ue sz cnt z -> (T + 288 <= z < T + 3168) \/ czone SB c (16 * x) sz z).
  { intros z Hz. apply (chg_cases G pce ab ub ue sz cnt z ltac:(clear -AR; lia)) in Hz. fold T in Hz. unfold czone. cbn zeta.
    replace (SB + c * 2 ^ 32 + 16 * x) with ab by (clear -AR; lia). clear -Hz AR. lia. }
  assert (CZR : forall z, czone SB c (16 * x) sz z -> (SB <= z < SB + 2 ^ 37) \/ (Sh SB <= z < Sh (SB + 2 ^ 37))).
  { intros z Hz. unfold czone in Hz. clear -Hz AR. unfold Sh in *. destruct Hz as [Hz|Hz]; [left; nia|right].
    pose proof (Z.div_le_mono SB (SB + c * 2 ^ 32 + 16 * x) 8 ltac:(clear -AR; lia) ltac:(clear -AR; nia)).
    pose proof (Z.div_le_mono (SB + c * 2 ^ 32 + 16 * x + sz) (SB + 2 ^ 37) 8 ltac:(clear -AR; lia) ltac:(clear -AR; nia)).
    replace ((SB + c * 2 ^ 32 + 16 * x + sz) / 8) with ((SB + c * 2 ^ 32 + 16 * x) / 8 + sz / 8) in *; [lia|].
    replace (SB + c * 2 ^ 32 + 16 * x + sz) with (SB + c * 2 ^ 32 + 16 * x + (sz / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
  assert (CHF : forall z, chg_m G pce ab ub ue sz cnt z -> fs_footb G z = false).
  { intros z Hz. destruct (CHGE z Hz) as [H|H].
    - apply fs_footb_T; [exact HG0 | unfold T in H; clear -H; lia].
    - destruct (CZR z H) as [K|K]; [apply fs_footb_space; [exact HG0| rewrite kSpaceSize_val; unfold SB in K; clear -K; lia] | apply fs_footb_space_sh; [exact HG0 | rewrite kSpaceSize_val; unfold SB in K]].
      pose proof (Sh_mono (ag_spacebeg G + 2 ^ 37) (ag_spacebeg G + 2 ^ 37 + 4096) ltac:(clear -ACV; lia)) as SM. clear -K SM. lia. }
  set (m3 := maskv (fs_footb G) v3). set (mE := maskv (fs_footb G) vE).
  assert (AGm : forall z, ~ chg_m G pce ab ub ue sz cnt z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity | exact (VO z Hz)]. }
  assert (CHm : forall z, chg_m G pce ab ub ue sz cnt z -> m3 z = v3 z).
  { intros z Hz. unfold m3. apply maskv_out. exact (CHF z Hz). }
  fold mE in Hlive, PC, PCc, Hsec, Hq, Hdep, Hia, HTH, Hmisc.

  set (A' := mallocA A c ub nv kmo).
  assert (Hlenc : (Z.to_nat c < length (aa_cls A))%nat) by (rewrite PL; clear -AR; lia).
  assert (ECS' : nthZ (aa_cls A') c cs_empty = pop_cls cs).
  { unfold A', mallocA, nthZ. cbn [aa_cls]. rewrite nth_list_upd_same by exact Hlenc. reflexivity. }
  assert (ECSo : forall c', c' <> c -> 0 <= c' -> nthZ (aa_cls A') c' cs_empty = nthZ (aa_cls A) c' cs_empty).
  { intros c' Hc' Hc'0. unfold A', mallocA, nthZ. cbn [aa_cls]. rewrite nth_list_upd_other; [reflexivity|]. clear -Hc' Hc'0 AR. lia. }

  unfold class_repr in PCc.
  destruct PCc as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & R9 & PR & N7 & PU & PSH & PE & ND & LV & CI & CN' & TI10 & CV10 & MC10 & FC10).
  assert (HCL : (0 < length (cs_cache cs))%nat) by (unfold cnt, cnt_of in Hcnt; fold cs in Hcnt; change (cst_of A nv) with cs in Hcnt; clear -Hcnt; lia).
  assert (Ecnt : cnt = Z.of_nat (length (cs_cache cs))) by reflexivity.
  assert (Ex : x = nth (length (cs_cache cs) - 1) (cs_cache cs) 0) by reflexivity.
  pose proof (removelast_split (cs_cache cs) 0 HCL) as CSPL. rewrite <- Ex in CSPL.
  assert (Hxin : In x (cs_cache cs)) by (rewrite CSPL; apply in_or_app; right; left; reflexivity).
  assert (CZE : cz_env SB c x sz (topG G)) by (unfold cz_env; clear -AR; lia).
  assert (Eczone : forall z, czone SB c (16 * x) sz z <-> ((ab <= z < ab + sz) \/ (Sh ab <= z < Sh ab + sz / 8))).
  { intros z. unfold czone. cbn zeta. replace (SB + c * 2 ^ 32 + 16 * x) with ab by (clear -AR; lia). split; intros HH; exact HH. }

  assert (NCH_img : forall z, IMG_LO <= z < IMG_HI -> ~ chg_m G pce ab ub ue sz cnt z).
  { intros z Hz Hc. destruct (CHGE z Hc) as [K|K]; [unfold IMG_LO, IMG_HI in Hz; clear -Hz K AR TI; lia|].
    apply (czone_env SB c x sz (topG G) z CZE) in K. unfold IMG_LO, IMG_HI, SHADOW_OFF in *. clear -Hz K AR. lia. }
  assert (NCH_T : forall z, (T <= z < T + 288 \/ T + 3168 <= z < T + 4096) -> ~ chg_m G pce ab ub ue sz cnt z).
  { intros z Hz Hc. destruct (CHGE z Hc) as [K|K]; [clear -Hz K; lia|].
    apply (czone_env SB c x sz (topG G) z CZE) in K. unfold SHADOW_OFF in K. clear -Hz K AR TB. lia. }
  assert (NCH_rgn : forall c' z, 0 <= c' <= 31 -> c' <> c ->
            (SB + c' * 2 ^ 32 <= z < SB + c' * 2 ^ 32 + 2 ^ 32) \/ (Sh (SB + c' * 2 ^ 32) <= z < Sh (SB + c' * 2 ^ 32 + 2 ^ 32))
            \/ (SB + 2 ^ 37 <= z < SB + 2 ^ 37 + 4096) -> ~ chg_m G pce ab ub ue sz cnt z).
  { intros c' z Hc' Hne HRG Hc. destruct (CHGE z Hc) as [K|K]; [|exact (czone_rgn SB c x sz (topG G) c' z CZE Hc' Hne K HRG)].
    rewrite <- !Z.add_assoc in HRG. rewrite !Sh_SB in HRG by (clear -AR; lia).
    assert (SHB : Sh SB + 2 ^ 34 + 512 <= SHADOW_OFF + 140737479966720 / 8).
    { unfold Sh. pose proof (Z.div_le_mono (SB + 2 ^ 37 + 4096) 140737479966720 8 ltac:(clear; lia) ltac:(clear -AR; lia)) as D.
      replace (SB + 2 ^ 37 + 4096) with (SB + (2 ^ 34 + 512) * 8) in D by (clear; lia). rewrite Z.div_add in D by (clear; lia). clear -D. lia. }
    replace ((c' * 2 ^ 32 + 2 ^ 32) / 8) with (c' * 2 ^ 29 + 2 ^ 29) in HRG by (clear -Hc'; apply Z.div_unique with 0; lia).
    replace (c' * 2 ^ 32 / 8) with (c' * 2 ^ 29) in HRG by (clear -Hc'; apply Z.div_unique with 0; lia).
    assert (SHL : 2147450880 <= Sh SB) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos SB 8 ltac:(clear -AR; lia) ltac:(clear; lia)); clear -H AR; lia).
    unfold SHADOW_OFF in *. cbn in SHB. clear -Hc' K HRG AR SHB SHL TB. lia. }
  assert (NCH_ent : forall c' z, 0 <= c' <= 30 -> c' <> c -> T + 208 + 80 * c' <= z < T + 208 + 80 * c' + 80 -> ~ chg_m G pce ab ub ue sz cnt z).
  { intros c' z Hc' Hne Hz Hc. unfold chg_m in Hc. fold T in Hc.
    destruct Hc as [H|[H|[H|[H|H]]]].
    1-4: clear -H Hz Hc' Hne AR; lia.
    assert (K : czone SB c (16 * x) sz z) by (apply (proj2 (Eczone z)); clear -H AR; lia).
    apply (czone_env SB c x sz (topG G) z CZE) in K. unfold SHADOW_OFF in K. clear -Hz K AR Hc' TB. lia. }

  pose proof Hsec as Hsec0. destruct Hsec as (SC1 & SCP & SC2 & SC3 & SC45 & SCI). fold G in SC45.
  destruct SC45 as [SC5m (SC4a & _ & SC5 & SC4i & SC4)]. unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in SC4i, SC4.

  unfold kPtrArrayReserve in SC2, SC5, SC4, SC4i, PAB3, PABT3.
  assert (SHL0 : 2147450880 <= Sh SB) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos SB 8 ltac:(clear -AR; lia) ltac:(clear; lia)); clear -H AR; lia).
  assert (SECZ : forall i ch z, nth_error (aa_sec A) i = Some ch ->
            (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch \/ Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch)) ->
            (czone SB c (16 * x) sz z -> False) /\ ~ chg_m G pce ab ub ue sz cnt z).
  { intros i ch z Hi Hz. destruct (SEC3 i ch Hi) as (E1 & E2 & _). fold T in E2. fold SB in E1.
    destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D12. unfold PG in D8.
    destruct D10 as (D10a & _ & _ & _ & D10b). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in D10b.
    assert (CZF : czone SB c (16 * x) sz z -> False).
    { intros K. destruct (CZR z K) as [K'|K'].
      - destruct Hz as [Hz|Hz]; [clear -Hz K' E1 D8 AR; lia|].
        pose proof (Sh_lt_HSE (sc_map_beg ch + sc_map_size ch) ltac:(clear -D12 ACV; lia)) as SL. unfold HIGH_SHADOW_END in SL. clear -Hz K' SL AR. lia.
      - destruct Hz as [Hz|Hz].
        + pose proof (Sh_lt_HSE (SB + 2 ^ 37) ltac:(clear -AR ACV; lia)) as SL. unfold HIGH_SHADOW_END in SL. clear -Hz K' SL D10b SHL0. lia.
        + destruct E1 as [E1|E1].
          * pose proof (Sh_mono (sc_map_beg ch + sc_map_size ch) SB E1). clear -Hz K' H. lia.
          * pose proof (Sh_mono (SB + 2 ^ 37) (sc_map_beg ch) ltac:(clear -E1; lia)). clear -Hz K' H. lia. }
    split; [exact CZF|]. intros Hc. destruct (CHGE z Hc) as [K|K]; [|exact (CZF K)].
    destruct Hz as [Hz|Hz]; [clear -Hz K E2 D8; lia|].
    pose proof (Sh_lt_HSE (sc_map_beg ch + sc_map_size ch) ltac:(clear -D12 ACV; lia)) as SL. unfold HIGH_SHADOW_END in SL.
    unfold Sh, SHADOW_OFF in Hz, SL. clear -Hz K SL AR TB D10a. lia. }

  assert (OLD : forall b' n', In (b', n') (aa_live A) ->
            (1 <= n' /\ 6578176 + 4096 <= b' /\ b' + n' <= topG G /\ b' mod 8 = 0 /\ 16 <= rz n' <= 2048 /\ (b' + n' <= 2147446784 \/ 17594333495296 <= b' - 16))
            /\ (forall z, (b' - rz n' <= z < b' + n' \/ Sh b' <= z < Sh b' + (n' + 7) / 8) -> czone SB c (16 * x) sz z -> False)
            /\ (forall z, (b' - rz n' <= z < b' + n' \/ Sh b' <= z < Sh b' + (n' + 7) / 8) -> ~ chg_m G pce ab ub ue sz cnt z)).
  { intros b' n' Hin.
    destruct (Hsep b' n' Hin) as (L1 & L2 & L3 & L4 & L5 & _ & _ & L8). fold G T in L5. unfold IMG_HI in L2. fold G in L3.
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in L8.
    pose proof (rz_bound n') as RZB.
    destruct (LIV3 b' n' Hin) as [PRM | (ch & Hch & Eb' & Esz)].
    2: {
         destruct (In_nth_error _ _ Hch) as [i Hi].
         destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D12. unfold PG in D6, D8, D11, Eb'.
         destruct D10 as (D10a & _ & _ & _ & D10b). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in D10b.
         pose proof (round_up_ge n' 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
         assert (B8 : b' mod 8 = 0).
         { rewrite Eb'. rewrite Z.add_mod, (Z.add_mod (sc_map_beg ch)) by (clear; lia).
           replace (sc_map_beg ch mod 8) with 0; [reflexivity|]. symmetry. apply Z.mod_divide; [clear; lia|].
           apply (Z.divide_trans _ 4096); [exists 512; reflexivity | apply Z.mod_divide; [clear; lia | exact D6]]. }
         assert (INM : forall z, (b' - rz n' <= z < b' + n' \/ Sh b' <= z < Sh b' + (n' + 7) / 8) ->
                   sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch \/ Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch)).
         { intros z [Hz|Hz]; [left; clear -Hz Eb' Esz RZB D8 D11 RU1 RU2 L1; lia | right].
           pose proof (Sh_mono (sc_map_beg ch) b' ltac:(clear -Eb'; lia)) as M1.
           assert (M2 : Sh b' + (n' + 7) / 8 <= Sh (sc_map_beg ch + sc_map_size ch)).
           { unfold Sh. destruct (proj1 (Z.mod_divide b' 8 ltac:(clear; lia)) B8) as [qb8 Hqb8].
             pose proof (Z.div_le_mono (b' + n' + 7) (sc_map_beg ch + sc_map_size ch) 8 ltac:(clear; lia) ltac:(clear -Eb' Esz D8 D11 RU1 RU2 L1; lia)) as DM.
             rewrite Hqb8 in DM |- *. rewrite Z.div_mul by (clear; lia). replace (qb8 * 8 + n' + 7) with (n' + 7 + qb8 * 8) in DM by (clear; lia).
             rewrite Z.div_add in DM by (clear; lia). clear -DM. lia. }
           clear -Hz M1 M2. lia. }
         split; [clear -L1 L2 L3 B8 RZB L8; lia|].
         split; [intros z Hz K; exact (proj1 (SECZ i ch z Hi (INM z Hz)) K)|].
         intros z Hz. exact (proj2 (SECZ i ch z Hi (INM z Hz))). }
    assert (Hn' : 1 <= n' <= 64512).
    { split; [exact L1|]. destruct (Z_le_dec n' 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n') in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n' Hn') as [CNo _]. pose proof (cls_facts n' Hn') as (D1 & D2 & D3 & D4). pose proof (rz_facts n' Hn') as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. set (c' := ClassID (needed n')) in D1, D2, D3, Y3. set (sz' := Size c') in D2, D3, Y3.
    pose proof (PC c' D1) as PC'. fold G in PC'. unfold class_repr in PC'.
    destruct PC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV' & _ & _).
    destruct (LV' b' n' Hin PRM eq_refl) as (V1 & V2 & V3). fold SB in V1, V2, V3. fold sz' in V2, V3.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3.
    assert (ERB' : region_beg SB c' = SB + c' * 2 ^ 32) by reflexivity.
    set (o' := b' - rz n' - region_beg SB c'). fold o' in V2, V3.
    assert (Ho' : 0 <= o' /\ o' + sz' <= 2 ^ 32 - 2 ^ 29 /\ o' mod 16 = 0 /\ b' = SB + c' * 2 ^ 32 + o' + rz n').
    { split; [clear -V1; unfold o'; lia|]. split; [clear -V3 M2 M3; lia|]. split; [|clear -ERB'; unfold o'; lia].
      apply Z.mod_divide; [clear -ACV; lia|]. apply (Z.divide_trans _ sz'); [apply Z.mod_divide; [clear -D2; unfold sz'; lia| exact D3] | apply Z.mod_divide; [clear -D2; unfold sz'; lia | exact V2]]. }
    destruct Ho' as (O1 & O2 & O3 & Eb').
    assert (SEP : c <> c' \/ 16 * x + sz <= o' \/ o' + sz' <= 16 * x).
    { destruct (Z.eq_dec c c') as [Ecc|Ncc]; [right|left; exact Ncc].
      assert (Hid : In (o' / 16) (live_ids G A c)).
      { replace o' with (b' - rz n' - region_beg (ag_spacebeg G) c) by (unfold o'; fold SB; rewrite Ecc; reflexivity).
        apply live_ids_in; [exact Hin|]. rewrite PRM. fold c'. rewrite <- Ecc, Z.eqb_refl. reflexivity. }
      assert (Hne : 16 * x <> o').
      { intros E. pose proof ND as ND0.
        apply (proj1 (list_relations.list.NoDup_app _ _)) in ND0 as (_ & _ & ND1). apply (proj1 (list_relations.list.NoDup_app _ _)) in ND1 as (_ & NX & _).
        apply (NX x (proj2 (list_elem_of_In _ _) Hxin)). apply (proj2 (list_elem_of_In _ _)).
        replace x with (o' / 16) by (clear -E O3; pose proof (Z.div_mod o' 16); lia). apply in_or_app. left. exact Hid. }
      assert (Esz : sz' = sz) by (unfold sz, sz'; rewrite Ecc; reflexivity). rewrite Esz in V2. rewrite Esz.
      destruct (mod0_apart (16 * x) o' sz ltac:(clear -AR; lia) ltac:(clear -AR; tauto) V2 Hne); [left|right]; assumption. }
    assert (ARB : SB mod 8 = 0 /\ 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G /\ 4096 <= T) by (clear -AR; tauto).
    destruct ARB as (AS8 & AS1 & AS2 & AT1).
    destruct (proj1 (Z.mod_divide SB 8 ltac:(clear -ACV; lia)) AS8) as [qa Qa]. destruct (proj1 (Z.mod_divide o' 16 ltac:(clear -ACV; lia)) O3) as [qo Qo].
    destruct (proj1 (Z.mod_divide (rz n') 16 ltac:(clear -ACV; lia)) Y2) as [qr Qr]. destruct (proj1 (Z.mod_divide sz' 16 ltac:(clear -ACV; lia)) D3) as [qs Qs].
    assert (B8 : b' mod 8 = 0).
    { rewrite Eb'. apply Z.mod_divide; [clear -ACV; lia|]. exists (qa + c' * 2 ^ 29 + qo * 2 + qr * 2). clear -Qa Qo Qr. lia. }
    split; [clear -Hn' L2 L3 B8 Y1 L8; lia|].
    assert (OLDZ : forall z, (b' - rz n' <= z < b' + n' \/ Sh b' <= z < Sh b' + (n' + 7) / 8) -> czone SB c (16 * x) sz z -> False).
    2: { split; [exact OLDZ|]. intros z Hz Hc. destruct (CHGE z Hc) as [K|K]; [|exact (OLDZ z Hz K)].
         assert (BLO : SB <= b' - rz n' /\ b' + n' <= SB + 2 ^ 37) by (clear -Eb' O1 O2 D1 Y1 Y3 Hn'; nia).
         destruct Hz as [Hz|Hz]; [clear -Hz K BLO T3; lia|].
         unfold Sh, SHADOW_OFF in Hz. pose proof (Z.div_le_mono b' 140737479966720 8 ltac:(clear; lia) ltac:(clear -L3 Hn' AR; lia)) as D1'.
         pose proof (Z.div_le_mono (n' + 7) 64519 8 ltac:(clear; lia) ltac:(clear -Hn'; lia)) as D2'. cbn in D1', D2'.
         pose proof (Z.div_pos b' 8 ltac:(clear -L2; unfold IMG_HI in L2; lia) ltac:(clear; lia)) as D0'.
         clear -Hz K D0' D1' D2' TB. lia. }
    intros z Hz K.
    refine (czone_disj SB c c' (16 * x) o' sz sz' z _ _ AS8 _ _ _ _ O1 O2 _ _ _ _ _ _ SEP K _); try (clear -AR D1 D2 O3 Qo Qs Y1; lia).
      unfold czone. cbn zeta. unfold Sh, SHADOW_OFF in Hz. unfold Sh, SHADOW_OFF. rewrite Eb' in Hz.
      rewrite Qa, Qo, Qr in Hz. rewrite Qa, Qo, Qs.
      replace ((qa * 8 + c' * 2 ^ 32 + qo * 16 + qr * 16) / 8) with (qa + c' * 2 ^ 29 + 2 * qo + 2 * qr) in Hz by (clear -ACV; apply Z.div_unique with 0; lia).
      replace ((qa * 8 + c' * 2 ^ 32 + qo * 16) / 8) with (qa + c' * 2 ^ 29 + 2 * qo) by (clear -ACV; apply Z.div_unique with 0; lia).
      replace (qs * 16 / 8) with (2 * qs) by (clear -ACV; apply Z.div_unique with 0; lia).
      pose proof (Z.div_lt_upper_bound (n' + 7) 8 (2 * qs - 2 * qr + 1) ltac:(clear -ACV; lia) ltac:(clear -Y3 Qr Qs; lia)) as D5.
      pose proof (Z.div_pos (n' + 7) 8 ltac:(clear -Hn'; lia) ltac:(clear -ACV; lia)) as D6.
      clear -Hz Y1 Y3 Qr Qs D5 D6 Hn'. lia. }
  assert (NCH_q : forall z, q_foot A z -> ~ chg_m G pce ab ub ue sz cnt z).
  { intros z Hqz Hc. destruct (Q3 z Hqz) as [QT QS]. fold T in QT.
    destruct (CHGE z Hc) as [K|K]; [apply QT; clear -K; lia|].
    apply (QS c x C1 Hxin). unfold slot_zone. cbn zeta. fold SB. apply (proj1 (Eczone z)) in K.
    replace (region_beg SB c + 16 * x) with ab by reflexivity. exact K. }
  assert (NCH_pab : forall z, ag_pab G <= z < ag_pab G + aa_ptr_committed A -> ~ chg_m G pce ab ub ue sz cnt z).
  { intros z Hz Hc. destruct (CHGE z Hc) as [K|K]; [clear -K Hz PABT3 SC2; lia|].
    apply (czone_env SB c x sz (topG G) z CZE) in K. unfold SHADOW_OFF in K. clear -K Hz PAB3 SC2 SC4 SC5 SHL0 AR. lia. }
  assert (NCH_meta : forall z, SB + 2 ^ 37 <= z < SB + 2 ^ 37 + 4096 -> ~ chg_m G pce ab ub ue sz cnt z).
  { intros z Hz Hc. destruct (CHGE z Hc) as [K|K]; [clear -K Hz AR; lia|].
    apply (czone_env SB c x sz (topG G) z CZE) in K. unfold SHADOW_OFF in K. clear -K Hz AR. lia. }
  assert (NCH_fa : forall z, SB + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29) <= z < SB + c * 2 ^ 32 + 2 ^ 32 -> ~ chg_m G pce ab ub ue sz cnt z).
  { intros z Hz Hc. destruct (CHGE z Hc) as [K|K]; [clear -K Hz AR; lia|].
    apply (czone_env SB c x sz (topG G) z CZE) in K. unfold SHADOW_OFF in K. clear -K Hz AR. lia. }
  assert (NCH_pc4 : forall z, (pce + 4 <= z < pce + 8 \/ pce + 16 <= z < pce + 16 + 4 * (cnt - 1)) -> ~ chg_m G pce ab ub ue sz cnt z).
  { intros z Hz Hc. pose proof Hc as Hc0. unfold chg_m in Hc0. fold T in Hc0.
    destruct Hc0 as [H|[H|[H|[H|H]]]].
    1-4: clear -H Hz AR; lia.
    assert (K : czone SB c (16 * x) sz z) by (apply (proj2 (Eczone z)); clear -H AR; lia).
    apply (czone_env SB c x sz (topG G) z CZE) in K. unfold SHADOW_OFF in K. clear -Hz K AR TB. lia. }
  assert (NCH_stack : forall z, topG G <= z -> ~ chg_m G pce ab ub ue sz cnt z).
  { intros z Hz Hc. destruct (CHGE z Hc) as [K|K]; [clear -K Hz AR; lia|].
    apply (czone_env SB c x sz (topG G) z CZE) in K. unfold SHADOW_OFF in K. clear -K Hz AR ACV. lia. }
  assert (CHGD : forall z, chg_m G pce ab ub ue sz cnt z \/ ~ chg_m G pce ab ub ue sz cnt z).
  { intros z. unfold chg_m. clear. lia. }
  assert (EG' : aa_geom A' = G) by reflexivity.
  assert (Eab8 : ab mod 8 = 0).
  { apply Z.mod_divide; [clear -ACV; lia|]. destruct (proj1 (Z.mod_divide SB 8 ltac:(clear -ACV; lia)) ltac:(clear -AR; tauto)) as [qq Hqq].
    exists (qq + c * 2 ^ 29 + 2 * x). clear -Hqq AR. lia. }
  assert (EShub : Sh ub = Sh ab + rz nv / 8).
  { replace ub with (ab + rz nv) by (clear -AR; lia). apply Sh_SB. exact Eab8. }

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz. apply VO. intros Hc.
    destruct (rtc_foot_cases G z Hz) as [K|[K|[K|[K|K]]]].
    - exact (NCH_img z K Hc).
    - apply (NCH_T z); [left; fold T in K; clear -K; lia | exact Hc].
    - destruct (CHGE z Hc) as [K'|K']; [clear -K K' G13; lia|]. apply (czone_env SB c x sz (topG G) z CZE) in K'. unfold SHADOW_OFF in K'. clear -K K' CTX3 G6 CB SHL0 AR. lia.
    - destruct (CHGE z Hc) as [K'|K']; [clear -K K' G14; lia|]. apply (czone_env SB c x sz (topG G) z CZE) in K'. unfold SHADOW_OFF in K'. clear -K K' DTLS3 G8 DB SHL0 AR. lia.
    - destruct (CHGE z Hc) as [K'|K']; [clear -K K' G10; lia|]. apply (czone_env SB c x sz (topG G) z CZE) in K'. unfold SHADOW_OFF in K'. clear -K K' S4 G2 WF SHL0 AR. lia. }
  assert (HFS : fs_inv (restrictv (fs_footb G) v3) A').
  { rewrite (restrictv_ext (fs_footb G) vE v3) by (intros z Hz; apply VO; intros Hc; rewrite (CHF z Hc) in Hz; discriminate).
    exact HF. }

  assert (CELL : forall a w v, (forall k, (k < w)%nat -> ~ chg_m G pce ab ub ue sz cnt (a + Z.of_nat k)) ->
                 cell_ok mE (mkACell a w v) -> cell_ok m3 (mkACell a w v)).
  { intros a w v Hn Hc. eapply cell_ok_agree; [|exact Hc]. cbn [c_addr c_w]. intros k Hk. apply AGm. exact (Hn k Hk). }
  assert (CELL3 : forall a w v, (forall k, (k < w)%nat -> chg_m G pce ab ub ue sz cnt (a + Z.of_nat k)) ->
                 cell_ok v3 (mkACell a w v) -> cell_ok m3 (mkACell a w v)).
  { intros a w v Hn Hc. eapply cell_ok_agree; [|exact Hc]. cbn [c_addr c_w]. intros k Hk. apply CHm. exact (Hn k Hk). }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (CHGD z) as [Hc|Hn].
    - destruct (PRES z Hc) as [b Hb]. exists b. rewrite (CHm z Hc). exact Hb.
    - rewrite (AGm z Hn). exact (Hp z Hz). }

  assert (LIVM : forall z, in_rangesZ (aa_live A) z -> in_rangesZ (aa_live A') z).
  { intros z (b & n & Hin & Hz). exists b, n. split; [change (aa_live A') with ((ub, nv) :: aa_live A); right; exact Hin | exact Hz]. }
  assert (PRESB : forall lo hi, present_but mE lo hi (aa_live A) -> present_but m3 lo hi (aa_live A')).
  { intros lo hi Hp. eapply present_but_mono; [exact LIVM | | exact Hp]. intros z Hz _ Hm. destruct (CHGD z) as [Hc|Hn].
    - destruct (PRES z Hc) as [b Hb]. rewrite (CHm z Hc), Hb. discriminate.
    - rewrite (AGm z Hn). exact Hm. }
  assert (HLS : live_sep A').
  { intros b n Hin. rewrite EG'. change (aa_live A') with ((ub, nv) :: aa_live A) in Hin. destruct Hin as [E|Hin]; [|exact (Hsep b n Hin)].
    injection E as <- <-. fold T. rewrite FS_total_val. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI. clear -AR S4 T3 CTX3 DTLS3. lia. }
  assert (HLB : live_block_repr m3 A').
  { intros b n Hin. change (aa_live A') with ((ub, nv) :: aa_live A) in Hin. destruct Hin as [E|Hin].
    - injection E as <- <-.
      assert (INH : forall k, 0 <= k < 16 -> chg_m G pce ab ub ue sz cnt (ub - 16 + k)) by (intros k Hk; unfold chg_m; clear -Hk AR; lia).
      split; [rewrite CHm by (replace (ub - 16) with (ub - 16 + 0) by (clear - ub; lia); apply INH; clear - AR; lia); exact VH2|].
      split; [rewrite Z.mod_small by (clear -AR; lia); apply CELL3; [intros k Hk; replace (ub - 12 + Z.of_nat k) with (ub - 16 + (4 + Z.of_nat k)) by (clear - k; lia); apply INH; clear - Hk; lia | exact VHN]|].
      split; [rewrite Z.div_small by (clear -AR; lia); apply CELL3; [intros k Hk; replace (ub - 14 + Z.of_nat k) with (ub - 16 + (2 + Z.of_nat k)) by (clear - k; lia); apply INH; clear - Hk; lia | exact VH0]|].
      assert (SHR : forall g, 0 <= g -> 8 * g < sz - rz nv -> chg_m G pce ab ub ue sz cnt (Sh ub + g)).
      { intros g Hg1 Hg2. unfold chg_m. do 6 right. rewrite EShub.
        destruct (proj1 (Z.mod_divide (rz nv) 16 ltac:(clear -ACV; lia)) ltac:(clear -AR; tauto)) as [qr Hqr].
        destruct (proj1 (Z.mod_divide sz 16 ltac:(clear -ACV; lia)) ltac:(clear -AR; tauto)) as [qs Hqs].
        rewrite Hqr, Hqs. replace (qr * 16 / 8) with (2 * qr) by (clear -ACV; apply Z.div_unique with 0; lia).
        replace (qs * 16 / 8) with (2 * qs) by (clear -ACV; apply Z.div_unique with 0; lia). clear -Hg1 Hg2 Hqr Hqs AR. lia. }
      split.
      { split.
      + intros g Hg. rewrite CHm; [exact (VZ g Hg)|]. apply SHR; [clear - Hg; lia|]. pose proof (Z.div_mod nv 8 ltac:(lia)). pose proof (Z.mod_pos_bound nv 8 ltac:(lia)). clear -Hg H H0 AR. lia.
      + intros Hm. rewrite CHm; [exact (VP Hm)|]. apply SHR; [apply Z.div_pos; clear -AR; lia|].
        pose proof (Z.div_mod nv 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MB.
        destruct (proj1 (Z.mod_divide (rz nv) 16 ltac:(clear -ACV; lia)) ltac:(clear -AR; tauto)) as [qr Hqr].
        destruct (proj1 (Z.mod_divide sz 16 ltac:(clear -ACV; lia)) ltac:(clear -AR; tauto)) as [qs Hqs].
        clear -Hm DM MB Hqr Hqs AR. lia. }

      split.
      { destruct VMG as [E16|[M1 M2]]; [left; exact E16|right].
      assert (INA : forall k, 0 <= k < 16 -> chg_m G pce ab ub ue sz cnt (ub - rz nv + k)) by (intros k Hk; unfold chg_m; clear -Hk AR; lia).
      split.
      + apply CELL3; [|exact M1]. intros k Hk. cbn [c_addr]. replace (ub - rz nv + Z.of_nat k) with (ub - rz nv + Z.of_nat k) by reflexivity. apply INA. clear -Hk; lia.
      + apply CELL3; [|exact M2]. intros k Hk. cbn [c_addr]. replace (ub - rz nv + 8 + Z.of_nat k) with (ub - rz nv + (8 + Z.of_nat k)) by (clear; lia). apply INA. clear -Hk; lia. }

      destruct VH1 as (t & Ht & Hm4). exists t. split; [|exact Hm4].
      rewrite CHm by (replace (ub - 15) with (ub - 16 + 1) by (clear; lia); apply INH; clear; lia). exact Ht.
    - destruct (Hlive b n Hin) as (B1 & B2 & B3 & [B4 B5] & B6 & B7). destruct (OLD b n Hin) as (BF & _ & NO).
      pose proof (Z.div_le_mono n (n + 7) 8 ltac:(clear -ACV; lia) ltac:(clear -ACV; lia)) as DL.
      split; [rewrite AGm by (apply NO; left; clear -BF; lia); exact B1|].
      split; [apply CELL; [intros k Hk; apply NO; left; clear -BF Hk; lia | exact B2]|].
      split; [apply CELL; [intros k Hk; apply NO; left; clear -BF Hk; lia | exact B3]|].
      split; [split|split].
      + intros g Hg. rewrite AGm by (apply NO; right; clear -Hg DL; lia). exact (B4 g Hg).
      + intros Hm. rewrite AGm; [exact (B5 Hm)|]. apply NO. right.
        replace ((n + 7) / 8) with (n / 8 + 1) by (apply Z.div_unique with (n mod 8 - 1); [pose proof (Z.mod_pos_bound n 8); clear -Hm H; lia | pose proof (Z.div_mod n 8); clear -H; lia]).
        clear -BF. pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)). lia.
      + apply (alloc_magic_ok_agree mE m3 b n); [|clear -BF; lia|exact B6]. intros z Hz. apply AGm. apply NO. left. clear -Hz BF. lia.
      + destruct B7 as (t & Ht & Hm4). exists t. split; [|exact Hm4]. rewrite AGm by (apply NO; left; clear -BF; lia). exact Ht. }
  assert (ELI : live_ids G A' c = x :: live_ids G A c).
  { unfold A', mallocA. rewrite live_ids_cons. rewrite CP, CN, Z.eqb_refl. cbn [andb].
    f_equal. fold SB. replace (ub - rz nv - region_beg SB c) with (x * 16) by (clear -AR ERB; lia). apply Z.div_mul. clear -ACV; lia. }
  assert (ELIo : forall c', c' <> c -> live_ids G A' c' = live_ids G A c').
  { intros c' Hc'. unfold A', mallocA. rewrite live_ids_cons. rewrite CN. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; clear -Hc'; lia).
    rewrite andb_false_r. reflexivity. }
  assert (HPR : primary_repr m3 A').
  { unfold primary_repr. rewrite EG'. split; [unfold A', mallocA; cbn [aa_cls]; rewrite length_list_upd; exact PL|].
    split; [rewrite (ECSo 0) by (clear -AR; lia); exact P0|]. split; [rewrite (ECSo 31) by (clear -AR; lia); exact P31|].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
    -
      rewrite ECS'. unfold class_repr. cbn [cs_mapped_user cs_allocated_user cs_free_array cs_mapped_free_array cs_cache cs_n_allocated cs_n_freed pop_cls].
      fold SB.
      assert (RIR : forall off k, 0 <= off -> off + Z.of_nat k <= 72 -> forall j, (j < k)%nat -> ~ chg_m G pce ab ub ue sz cnt (region_info SB c + off + Z.of_nat j)).
      { intros off k Ho Hk j Hj. apply NCH_meta. unfold region_info, kRegionInfoStride. rewrite kSpaceSize_val. clear -Ho Hk Hj AR. lia. }
      split; [apply CELL; [apply RIR; unfold RI_mutex; cbn; clear -ACV; lia | exact R1]|].
      split; [apply CELL; [apply RIR; unfold RI_num_freed; cbn; clear -ACV; lia | exact R2]|].
      split; [apply CELL; [apply RIR; unfold RI_mapped_free_array; cbn; clear -ACV; lia | exact R3]|].
      split; [apply CELL; [apply RIR; unfold RI_allocated_user; cbn; clear -ACV; lia | exact R4]|].
      split; [apply CELL; [apply RIR; unfold RI_allocated_meta; cbn; clear -ACV; lia | exact R5]|].
      split; [apply CELL; [apply RIR; unfold RI_mapped_user; cbn; clear -ACV; lia | exact R6]|].
      split; [apply CELL; [apply RIR; unfold RI_mapped_meta; cbn; clear -ACV; lia | exact R7]|].
      split; [apply CELL; [apply RIR; unfold RI_exhausted; cbn; clear -ACV; lia | exact R8]|].
      split; [eapply present_agree; [|exact PRI]; intros z Hz; apply AGm; apply NCH_meta; unfold region_info, kRegionInfoStride in Hz; rewrite kSpaceSize_val in Hz; fold SB in Hz; clear -Hz AR; lia|].
      split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
      split.
      { intros i x0 Hi. apply CELL; [|exact (R9 i x0 Hi)]. intros k Hk. apply NCH_fa. pose proof (nth_error_Some_lt _ _ _ Hi) as L.
        unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. unfold kFreeArraySize in N6. clear -L Hk N6. lia. }
      split; [apply PRESX; exact PR|].
      split; [intros x0 Hx0; apply N7; apply in_app_or in Hx0 as [Hx0|Hx0]; apply in_or_app; [left; exact Hx0 | right; exact (in_removelast _ _ Hx0)]|].
      split; [apply PRESB; exact PU|]. split; [apply PRESX; exact PSH|]. split; [apply PRESX; exact PE|].
      split; [rewrite ELI; rewrite CSPL in ND; apply NoDup_move; exact ND|].
      split.
      { intros b n Hin Hp Hcl. change (aa_live A') with ((ub, nv) :: aa_live A) in Hin. destruct Hin as [E|Hin]; [|exact (LV b n Hin Hp Hcl)].
        injection E as <- <-. destruct (N7 x ltac:(apply in_or_app; right; exact Hxin)) as (W1 & W2 & W3).
        unfold kCompactPtrScale in W2, W3. rewrite Z.shiftl_mul_pow2 in W2, W3 by (clear -ACV; lia). change (2 ^ 4) with 16 in W2, W3.
        replace (ub - rz nv - region_beg SB c) with (x * 16) by (clear -AR ERB; lia). clear -W2 W3 AR ERB. unfold sz in *. lia. }
      split.
      { intros _. destruct (CI HCI) as (K1 & K2 & K3 & K4 & K5). fold T pce in K2, K4 |- *.
        rewrite (removelast_len (cs_cache cs) 0 HCL).
        split; [apply CELL3; [intros k Hk; unfold chg_m; clear -Hk AR; lia|]; replace (Z.of_nat (length (cs_cache cs) - 1)) with (cnt - 1) by (clear -Ecnt HCL; lia); exact VC|].
        split; [apply CELL; [intros k Hk; apply NCH_pc4; clear -Hk; lia | exact K2]|].
        split; [apply CELL3; [intros k Hk; unfold chg_m; clear -Hk AR; lia| exact VS]|].
        split; [|clear -K5 HCL; lia].
        intros i x0 Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as L. rewrite (removelast_len (cs_cache cs) 0 HCL) in L.
        rewrite (nth_error_removelast (cs_cache cs) 0 i L) in Hi.
        apply CELL; [|exact (K4 i x0 Hi)]. intros k Hk. apply NCH_pc4. right. clear -Hk L Ecnt. lia. }
      split; [intros Hf; change (aa_cache_inited A') with (aa_cache_inited A) in Hf; rewrite HCI in Hf; discriminate|].

      split; [exact TI10|]. split; [|exact (conj MC10 FC10)].
      rewrite ELI. change (qall A') with (qall A). unfold slots in CV10 |- *. cbn [cs_allocated_user pop_cls]. rewrite CV10.
      rewrite (removelast_len (cs_cache cs) 0 HCL). cbn [length]. f_equal. clear -HCL. lia.
    -
      rewrite (ECSo c' Hne) by (clear -Hc'; lia).
      pose proof (PC c' Hc') as PC'. fold G in PC'.
      pose proof PC' as PCX. unfold class_repr in PCX.
      destruct PCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & M6 & _).
      unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3, M6.
      refine (class_repr_agree mE m3 G A A' c' _ Hc' eq_refl (ELIo c' Hne) eq_refl _ LIVM _ PC').
      + intros b n Hin Hp Hcl. change (aa_live A') with ((ub, nv) :: aa_live A) in Hin. destruct Hin as [E|Hin]; [|exact Hin].
        exfalso. injection E as <- <-. apply Hne. rewrite <- Hcl. exact CN.
      + intros z Hz. apply AGm. unfold cls_foot in Hz. cbn zeta in Hz. fold SB T in Hz.
        unfold region_info, free_array, region_beg, kRegionInfoStride, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. rewrite kSpaceSize_val in Hz.
        destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
        * apply NCH_meta. clear -Hz Hc'. lia.
        * apply (NCH_rgn c'); [clear -Hc'; lia | exact Hne | left; clear -Hz M6; lia].
        * apply (NCH_rgn c'); [clear -Hc'; lia | exact Hne | left; clear -Hz M2 M3; lia].
        * apply (NCH_rgn c'); [clear -Hc'; lia | exact Hne | right; left].
          pose proof (Sh_mono (SB + c' * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) c' cs_empty)) (SB + c' * 2 ^ 32 + 2 ^ 32) ltac:(clear -M2 M3; lia)) as SM.
          clear -Hz SM. lia.
        * apply (NCH_ent c'); [clear -Hc'; lia | exact Hne | clear -Hz; lia]. }
  assert (HSR : secondary_repr m3 A').
  { refine (secondary_repr_agree mE m3 A A' eq_refl eq_refl eq_refl _ _ _ LIVM Hsec0).
    - intros i ch z Hi Hz. apply AGm. exact (proj2 (SECZ i ch z Hi Hz)).
    - intros z Hz. apply AGm. apply NCH_pab. exact Hz.
    - intros z Hz. apply AGm. exact (NCH_img z Hz). }
  assert (HQR : quarantine_repr m3 A').
  { refine (quarantine_repr_agree mE m3 A A' eq_refl eq_refl eq_refl eq_refl _ _ _ Hsep _ _ _ _ Hq).
    - intros c'. destruct (Z.eq_dec c' c) as [->|Hne]; [rewrite ECS'; reflexivity|].
      destruct (Z_le_dec 0 c') as [Hc'|Hc']; [rewrite (ECSo c' Hne Hc'); reflexivity|].
      unfold A', mallocA, nthZ. cbn [aa_cls]. replace (Z.to_nat c') with 0%nat by (clear -Hc'; lia). rewrite nth_list_upd_other; [reflexivity | clear -AR; lia].
    - intros c'. destruct (Z.eq_dec c' c) as [->|Hne]; [rewrite ECS'; reflexivity|].
      destruct (Z_le_dec 0 c') as [Hc'|Hc']; [rewrite (ECSo c' Hne Hc'); reflexivity|].
      unfold A', mallocA, nthZ. cbn [aa_cls]. replace (Z.to_nat c') with 0%nat by (clear -Hc'; lia). rewrite nth_list_upd_other; [reflexivity | clear -AR; lia].
    - intros c' x' Hx'. destruct (Z.eq_dec c' c) as [->|Hne]; [rewrite ECS' in Hx'; cbn [cs_cache pop_cls] in Hx'; exact (in_removelast _ _ Hx')|].
      destruct (Z_le_dec 0 c') as [Hc'|Hc']; [rewrite (ECSo c' Hne Hc') in Hx'; exact Hx'|].
      unfold A', mallocA, nthZ in Hx' |- *. cbn [aa_cls] in Hx' |- *. replace (Z.to_nat c') with 0%nat in * by (clear -Hc'; lia). rewrite nth_list_upd_other in Hx'; [exact Hx' | clear -AR; lia].
    - apply Forall_forall. intros qb _. apply Forall_forall. intros it _. exact (proj1 (rz_bound (snd it))).
    - intros z Hz. apply AGm. exact (NCH_q z Hz).
    - intros z Hz. apply AGm. apply NCH_T. left. unfold T, G. clear -Hz. lia.
    - intros z Hz. apply AGm. exact (NCH_img z Hz). }
  assert (HIA : ia_inv m3 A').
  { refine (ia_inv_agree mE m3 A A' eq_refl _ Hia). intros z Hz. apply AGm. exact (NCH_img z Hz). }
  assert (HTI : thread_inv m3 G).
  { destruct HTH as [TH1 TH2]. fold T in TH1, TH2 |- *. split.
    - fold T. rewrite AGm; [exact TH1|]. apply NCH_T. right. clear -ACV. lia.
    - fold T. apply PRESX. exact TH2. }
  assert (HMI : misc_inv m3).
  { refine (misc_inv_agree mE m3 _ Hmisc). intros z Hz. apply AGm. exact (NCH_img z Hz). }
  assert (HDEP : depot_wf m3 A').
  {
    unfold depot_wf in Hdep |- *. change (aa_depot A') with (aa_depot A). eapply depot_mem_frame; [|exact Hdep]. intros a Ha. apply AGm. intros Hc.
    assert (BLK : forall bb L, In (bb, L) (dblocks (aa_depot A)) -> bb <= a < bb + L -> False).
    { intros bb L Hbb Hab. destruct (DEP3 (bb, L) Hbb) as (DI & ST & _ & _ & _ & SS & _). unfold sepZ in ST, SS. cbn [fst snd] in DI, ST, SS. fold T in ST. fold SB in SS.
      destruct DI as (_ & _ & _ & _ & WB). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WB. rewrite kSpaceSize_val in SS.
      destruct (CHGE a Hc) as [Hz|Hz]; [clear -Hz ST Hab; lia|].
      destruct (CZR a Hz) as [K|K]; [clear -K SS Hab; lia|].
      pose proof (Z.div_le_mono SB (SB + 2 ^ 37) 8 ltac:(clear; lia) ltac:(clear; lia)). unfold Sh, SHADOW_OFF in K.
      pose proof (Z.div_pos SB 8 ltac:(clear -AR; lia) ltac:(clear; lia)).
      pose proof (Z.div_lt_upper_bound (SB + 2 ^ 37) 8 (2 ^ 44) ltac:(clear; lia) ltac:(clear -AR; lia)).
      clear -K WB Hab H H0 H1. lia. }
    destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
    - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs.
      destruct (CHGE a Hc) as [Hz|Hz]; [clear -Hz Hs TI; lia|]. destruct (CZR a Hz) as [K|K]; [clear -K Hs AR; lia|].
      unfold Sh, SHADOW_OFF in K. pose proof (Z.div_pos SB 8 ltac:(clear -AR; lia) ltac:(clear; lia)). clear -K Hs H. lia.
    - apply (BLK bb NBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. left. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
    - apply (BLK bb FBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. right. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb]. }
  assert (HMD : model_inv segs A' tp md).
  { unfold model_inv in HM |- *. destruct HM as (VG & PB & LIM & V0 & K0 & F0 & TOPm & LED).
    split; [unfold vm_geom in VG |- *; unfold A', mallocA; cbn [aa_geom aa_sec]; exact VG|]. unfold budget_boundD in PB |- *.
    change (aa_V A') with (aa_V A + nv). change (aa_Km A') with kmo. change (aa_Kf A') with (aa_Kf A).
    change (aa_ptr_committed A') with (aa_ptr_committed A). change (aa_depot A') with (aa_depot A).
    pose proof (acost_mono (aa_V A) (aa_V A + nv) ltac:(clear -Hnv; lia)) as AM. unfold BETA1 in *.

    assert (PCR : prim_credit A' = prim_credit A).
    { apply prim_credit_maps. intros c' Hc'. change (nth (Z.to_nat c') (aa_cls A') cs_empty) with (nthZ (aa_cls A') c' cs_empty).
      change (nth (Z.to_nat c') (aa_cls A) cs_empty) with (nthZ (aa_cls A) c' cs_empty).
      destruct (Z.eq_dec c' c) as [->|Hne]; [rewrite ECS'; split; reflexivity | rewrite (ECSo c' Hne ltac:(clear -Hc'; lia)); split; reflexivity]. }
    rewrite PCR. split; [set (pcr := prim_credit A) in *; clearbody pcr; clear -PB AM K0 HKMO; lia|]. split; [exact LIM|]. split; [clear -V0 Hnv; lia|]. split; [clear -K0 HKMO; lia|]. split; [exact F0|]. split; [exact TOPm|].

    unfold ledger_inv, gap_ok, gapN_ok, gapS_ok, blocks_left in LED |- *.
    change (aa_V A') with (aa_V A + nv). change (aa_Km A') with kmo. change (aa_Kf A') with (aa_Kf A).
    change (aa_ptr_committed A') with (aa_ptr_committed A). change (aa_depot A') with (aa_depot A).
    destruct LED as (L1 & L2 & L3 & [L4a L4b] & L5 & L6 & L7 & L8 & L9 & L10).
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [split; [clear -L4a Hnv; lia | clear -L4b Hnv; lia]|].
    split; [exact L5|]. split; [clear -L6 HKMO; lia|]. split; [clear -L7 HKMO; unfold kPtrArrayCommit in *; lia|].
    split; [exact L8|split; [change (aa_sec A') with (aa_sec A); clear -L9 HKMO; lia | exact L10]]. }
  assert (HI3' : inv3 A').
  { destruct HI3c as (X1' & X2' & X3' & X4' & X5' & X6' & X7' & X8' & X9'). split; [exact X1'|]. split.
    - intros b n Hin. change (aa_live A') with ((ub, nv) :: aa_live A) in Hin. destruct Hin as [E|Hin]; [injection E as <- <-; left; exact CP | exact (X2' b n Hin)].
    - split; [exact X3'|]. split.
      { intros z Hz. destruct (X4' z Hz) as [Y1 Y2]. split; [exact Y1|].
        intros c' x' Hc' Hx'. apply (Y2 c' x' Hc').
        destruct (Z.eq_dec c' c) as [->|Hne]; [rewrite ECS' in Hx'; cbn [cs_cache pop_cls] in Hx'; exact (in_removelast _ _ Hx') | rewrite (ECSo c' Hne ltac:(clear -Hc'; lia)) in Hx'; exact Hx']. }
      split; [exact X5'|].

      split; [change (aa_live A') with ((ub, nv) :: aa_live A); cbn [List.filter List.map fst snd]; rewrite CP; cbn [negb]; exact X6'|].

      assert (ELL : large_live A' = large_live A).
      { unfold large_live. change (aa_live A') with ((ub, nv) :: aa_live A). cbn [List.filter]. unfold is_large at 1. cbn [snd].
        replace (64513 <=? nv) with false by (symmetry; apply Z.leb_gt; clear -Hnv; lia). reflexivity. }
      split; [rewrite ELL; exact X7'|].

      split; [|exact X9'].
      rewrite (small_live_insert A A' [] (aa_live A) ub nv eq_refl eq_refl).
      replace (64513 <=? nv) with false by (symmetry; apply Z.leb_gt; clear -Hnv; lia). unfold prim_room in HPRM. clear -HPRM. lia. }
  assert (HA' : AInv A' rho3 tp md).
  { unfold AInv, AInvA. rewrite EG'. fold v3. split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|].
    split; [|split; [exact HMD | split; [exact HI3' |

      eapply bandtp_mono_rm; [|exact HB]; intros a Ha; apply DEFM; clear -Ha;
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI in *; lia]]].
    fold m3. split; [exact HLS|]. split; [exact HLB|]. split; [exact HPR|]. split; [exact HSR|]. split; [exact HQR|].
    split; [exact HDEP|]. split; [exact HIA|]. split; [exact HTI | exact HMI]. }
  exists A'. split; [exact HA'|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split.
  -
    split.
    2: { intros x0 j Hx Hj Hdef.
         assert (HFv0 : fs_inv (restrictv (fs_footb G) vE) A) by exact HF.
         assert (Bx : 0 <= x0 < 2 ^ 47).
         { destruct Hx as [[CX _]|GX]; [exact (proj1 (client_addr_bounds CST HCST A x0 _ HG HFv0 Hsep CX))|].
           destruct (HXGL x0 GX) as [XG1 XG2]. unfold IMG_HI in XG2. clear -XG1 XG2. lia. }
         unfold word_byte. apply DEFM; [|exact Hdef].
         pose proof (Z.div_mod (Sh x0) 8 ltac:(clear -ACV; lia)) as DM. pose proof (Z.mod_pos_bound (Sh x0) 8 ltac:(clear -ACV; lia)) as MB.
         unfold Sh, SHADOW_OFF, IMG_HI in DM, MB |- *. pose proof (Z.div_le_mono 0 x0 8 ltac:(clear -ACV; lia) ltac:(clear -Bx; lia)) as D0.
         pose proof (Z.div_lt_upper_bound x0 8 (2 ^ 44) ltac:(clear -ACV; lia) ltac:(clear -Bx; lia)) as D1. change (0 / 8) with 0 in D0.
         clear -Hj DM MB D0 D1. lia. }
    intros a Ha Hcl.
    assert (HFv : fs_inv (restrictv (fs_footb G) vE) A) by exact HF.
    assert (NOC : forall y, client_addrA CST A y -> ~ chg_m G pce ab ub ue sz cnt y /\ (ab <= y < ab + sz -> False)).
    { intros y Hy.
      destruct (client_addr_cases CST A y _ HFv Hy) as [S|[L|[FR|[C|FL]]]].
      - fold G in S. split; [apply NCH_stack; clear -S; lia | clear -S AR; lia].
      - destruct L as (b & n & Hbn & Hyb). destruct (OLD b n Hbn) as (BF & OZ & NO). split; [apply NO; left; clear -Hyb BF; lia|].
        intros Hy2. apply (OZ y); [left; clear -Hyb BF; lia|]. apply (proj2 (Eczone y)). left. exact Hy2.
      - destruct FR as (c0 & p0 & Hc0 & Hp0 & _ & Hyf). pose proof (fs_geom_nums G c0 p0 HG Hc0 Hp0) as M. cbn zeta in M.
        rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G in Hyf.
        split; [intros Hc; pose proof (CHF y Hc) as X; rewrite fs_footb_true2 in X by (rewrite FS_kFlagsOffset_val, FS_total_val; clear -Hyf M; lia); discriminate|].
        clear -Hyf M S4 AR. lia.
      - destruct (HCST _ C) as [X _]. split; [apply NCH_img; exact X | unfold IMG_HI in X; clear -X AR; lia].
      - destruct FL as (c0 & p0 & Hc0 & Hp0 & _ & ->). pose proof (fs_geom_nums G c0 p0 HG Hc0 Hp0) as M. cbn zeta in M.
        rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G. unfold fs_flags. rewrite FS_kFlagsOffset_val.
        unfold fs_flags in M. rewrite FS_kFlagsOffset_val in M.
        split; [intros Hc; pose proof (CHF _ Hc) as X; rewrite fs_footb_true2 in X by (rewrite FS_kFlagsOffset_val, FS_total_val; clear -M; lia); discriminate|].
        clear -M S4 AR. lia. }
    apply RMO; [exact Ha| |].
    + destruct Hcl as [[CL1 _]|[CL1 _]]; [exact (proj1 (NOC a CL1))|].
      pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HFv Hsep CL1) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
      intros Hc. destruct (CHGE a Hc) as [K|K]; [clear -K B AR TB; lia|].
      apply (proj1 (Eczone a)) in K. destruct K as [K|K]; [clear -K B AR; lia|].

      destruct CL1 as [(y & Cy & Ey)|(y & Gy & Ey)].
      * destruct (NOC y Cy) as [_ NY]. apply NY. subst a. unfold Sh in K.
        destruct (client_addr_bounds CST HCST A y _ HG HFv Hsep Cy) as [By _].
        destruct (proj1 (Z.mod_divide ab 8 ltac:(clear -ACV; lia)) Eab8) as [qab Hqab].
        destruct (proj1 (Z.mod_divide sz 16 ltac:(clear -ACV; lia)) ltac:(clear -AR; tauto)) as [qsz Hqsz].
        rewrite Hqab, Hqsz in K. rewrite Z.div_mul in K by (clear -ACV; lia).
        replace (qsz * 16 / 8) with (2 * qsz) in K by (clear -ACV; apply Z.div_unique with 0; lia).
        pose proof (Z.div_mod y 8 ltac:(clear -ACV; lia)) as DM. pose proof (Z.mod_pos_bound y 8 ltac:(clear -ACV; lia)) as MB. clear -K Hqab Hqsz DM MB By. lia.
      * destruct (HXGL y Gy) as [Y1 Y2]. subst a. unfold IMG_HI in Y2. unfold Sh in K.
        pose proof (Z.div_le_mono y IMG_HI 8 ltac:(clear -ACV; lia) ltac:(unfold IMG_HI; clear -Y2; lia)) as D1.
        pose proof (Z.div_le_mono SB ab 8 ltac:(clear -ACV; lia) ltac:(clear -AR; lia)) as D2.
        pose proof (Z.div_le_mono 17594333495296 SB 8 ltac:(clear -ACV; lia) ltac:(clear -AR; lia)) as D3.
        unfold IMG_HI in D1. change (6578176 / 8) with 822272 in D1. change (17594333495296 / 8) with 2199291686912 in D3.
        clear -K D1 D2 D3. lia.
    + destruct Hcl as [[CL1 _]|[CL1 _]]; [exact (client_not_rtM A a _ HG HFv Hsep CL1)|].
      pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HFv Hsep CL1) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
      intros [R|R]; [|pose proof (IMG_M_lt a R) as X; unfold IMG_HI in X; clear -B X; lia].
      unfold rt_zone, IMG_HI in R. clear -R B WF TB CB DB. lia.
  -
    intros c0 Hc0 Hor Hfr. unfold class_fresh in Hfr |- *. unfold A', mallocA. cbn [aa_cls].
    rewrite nth_list_upd_other; [exact Hfr|]. destruct Hor as [Hbig|Hneq]; [clear -Hbig Hnv; lia|].
    rewrite CN in Hneq. clear -Hneq Hc0 AR. lia.
Qed.
End R.
