(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "or"; "eq"; "ex"; "not"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "sub"; "mul"; "div"; "modulo"; "of_nat"; "pow"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "qbatch"; "aa_cls"; "sec_chunk"; "aa_q_global"; "aa_q_thread"; "aa_sec"; "aa_cache_inited"; "aa_live"; "ag_thread"; "class_state"; "qb_addr"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_ptr_committed"; "ag_spacebeg"; "ageom"; "cs_allocated_user"; "mkAA"; "qb_items"; "sc_map_beg"; "class_fresh"; "ag_ctx"; "ag_pab"; "cs_cache"; "cs_empty"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "cs_n_allocated"; "cs_n_freed"; "list_upd"; "mkCS"; "qb_size"; "sc_map_size"; "sc_size"; "@Corelib.Init.Datatypes"; "list"; "bool"; "fst"; "prod"; "snd"; "length"; "option"; "Some"; "false"; "nat"; "nil"; "true"; "None"; "app"; "cons"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "QG"; "qsize"; "qhdr_repr"; "qlinks"; "SEC_INST"; "alloc_magic_ok"; "nthZ"; "q_foot"; "quarantine_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "kQuarantineBatchSize"; "is_primary"; "PG"; "kQuarantineMax"; "region_beg"; "ClassID"; "HIGH_SHADOW_END"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Size"; "free_array"; "kFreeArraySize"; "kPtrArrayReserve"; "kQuarantineBatchCount"; "kRegionInfoStride"; "needed"; "region_info"; "round_up"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "present"; "view"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "QFP"; "same_but_q"; "QW"; "cls_of"; "q_mem"; "qzone"; "set_q"; "QRD"; "QNPRE"; "batch_mem"; "batch_pure"; "item_mem"; "item_pure"; "pc_entry"; "push_cs"; "push_zone"; "qbounded"; "qhdr_zone"; "qrtc2_zone"; "qrtc_zone"; "qstat_zone"; "same_but_qcs"; "sec_foot"; "sec_held"; "set_cls"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qall"; "it_ab"; "qitems"; "@Stdlib.Lists.List"; "Exists"; "In"; "fold_right"; "nth_error"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2.WithSegs"; "JQ3"; "qpost"; "KQ_laws"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@stdpp.base"; "NoDup"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv SegQ_defs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition QNPRE : positive := 160%positive.

Definition qzone (A : AA) (z : Z) : Prop := ltac2:(tb__ "0|5|
S90S14S14S1S0S9S1eR1A1M0Vz;A2SaVz;S8G0S58A2A2A2S90S3fS6S6A2M1G1S0S2S3dS59S40S6S6R1A3M2A1S47A3S1S0S9S8eR1A1Vz;A2SaVz;S3eS6S6R1A3M3A2A2S0S9S57G3A1M4Vz;A2SaVz;S8G4SdS8G2Z7A2Z8A2A2A2A2A2A2Lit;S2bR1A1A3A2Lb;S8dVA;A1A3").
Lemma qzone_q_foot : ltac2:(tb__ "0|0|
S12S6S76R2R1A2S52R3R2A2F_;Fz;FA;").
Proof.
  intros A z H. unfold qzone, q_foot, qall in *. apply Exists_exists in H as (b & Hb & Hz). apply Exists_exists. exists b. split; [exact Hb|].
  destruct Hz as [Hz|Hz]; [left; exact Hz | right]. apply Exists_exists in Hz as (it & Hit & _ & Hz'). apply Exists_exists. exists it.
  split; [exact Hit|]. unfold it_ab in Hz'. exact Hz'.
Qed.

Definition qhdr_zone (G : ageom) (z : Z) : Prop := ltac2:(tb__ "0|1|
S1S0S9S8S1cVG;A1M0Z50A2Vz;A2SaVz;S8G0Z70A2A2A2S1S0S9S8S4bZ98A2Vz;A2SaVz;S8S4bZ9cA2A2A2S0S9S8S4bZa0A2Vz;A2SaVz;S8S4bZc0A2A2A2A2A2").

Definition qstat_zone (G : ageom) (z : Z) : Prop := ltac2:(tb__ "0|1|
S0S9S8S1cVG;A1M0Zad0A2Vz;A2SaVz;S8G0Zc60A2A2A2").

Definition QW (A : AA) (z : Z) : Prop := ltac2:(tb__ "0|1|
S1S76VA;Vz;A2S1S82S13VA;A1M0Vz;A2S85G0Vz;A2A2A2").

Definition pc_entry (G : ageom) (c : Z) : Z := ltac2:(tb__ "0|0|
S8S8S1cVG;A1Zd0A2ScZ50Vc;A2A2").
Definition push_zone (G : ageom) (c k : Z) (z : Z) : Prop := ltac2:(tb__ "0|3|
S1S0S9S7eVG;Vc;A2M0Vz;A2SaVz;S8G0Z4M1A2A2A2S0S9S8S8G0Z10A2ScG1Vk;A2A2M2Vz;A2SaVz;S8G2G1A2A2A2A2").

Lemma QW_qzone : ltac2:(tb__ "0|0|
S12S6S76R2R1A2S73R3R2A2F_;Fz;FA;"). Proof. intros A z H. left. exact H. Qed.

Definition sec_held (A : AA) (ch : sec_chunk) : Prop := ltac2:(tb__ "0|1|
S3S3fS6S6A2M0G0S0S91G0R1S8fS8dVA;A1A1A3S0S2S3dS59S40S6S6R1A3A1S44A3S2S6S3eS6S6R1A3S8S8S2cVch;A1S5aA2Z800A2A3A2A2Lit;A2").
Definition sec_foot (A : AA) (z : Z) : Prop := ltac2:(tb__ "0|5|
S1S0S9S4fVz;A2SaVz;Zead30A2A2S1S0S9S2fS13VA;A1A1M0Vz;A2SaVz;S8G0S65A2A2A2S1S90S16S16S0S9S2cR1A1M1Vz;A2M2SaVz;S8G1Z20A2A2A2Lch;S19VA;A1M3A3S90S16S16S0S88VA;R1A2S1S0G2SaVz;S8G1S3aR1A1A2M4A2A2S0S9S57G1A1Vz;A2SaVz;S57G4A1A2A2A2A2Lch;G3A3A2A2A2").
Definition QFP (A : AA) (z : Z) : Prop := ltac2:(tb__ "0|6|
S1S73VA;Vz;A2S1S0S9S8S1cS13VA;A1M0A1M1Zd0A2Vz;A2SaVz;S8G1Zad0A2A2A2S1S3S6S6S0S0S9Z1R1A2S9R1Z1eA2A2S1S0S9S69S27G0A1M2R1A2M3Vz;A2SaVz;S8G3S67A2A2A2S1S0S9S63G2R1A2M4Vz;A2SaVz;S8G4S64A2M5A2A2S0S9S57G4A1Vz;A2SaVz;S57G5A1A2A2A2A2A2Lc;A2S87VA;Vz;A2A2A2A2").
Lemma QFP_QW : ltac2:(tb__ "0|0|
S12S6S73R2R1A2S71R3R2A2F_;Fz;FA;"). Proof. intros A z H. left. exact H. Qed.

Definition qrtc_zone (G : ageom) (z : Z) : Prop := ltac2:(tb__ "0|1|
S1S0S9S8S4bZ40A2Vz;A2SaVz;S8S4bZ50A2A2A2S1S0S9Zeaa78Vz;A2SaVz;Zeaa84A2A2S1S0S9Zeaa88Vz;A2SaVz;Zeaa91A2A2S1S0S9Ze6780Vz;A2SaVz;Ze6788A2A2S1S0S9Zed91cVz;A2SaVz;Zed91dA2A2S1S0S9Zed920Vz;A2SaVz;Zed921A2A2S1S0S9Zed924Vz;A2SaVz;Zed928A2A2S1S0S9Z621220Vz;A2SaVz;Z621228A2A2S1S0S9Z642620Vz;A2SaVz;Z642628A2A2S1S0S9S8S2eVG;A1M0Z98A2Vz;A2SaVz;S8G0Za0A2A2A2S1S0S9Zeed98Vz;A2SaVz;Zeed9aA2A2S0S9Zeeda0Vz;A2SaVz;ZeedbcA2A2A2A2A2A2A2A2A2A2A2A2A2").

Definition qrtc2_zone (z : Z) : Prop := ltac2:(tb__ "0|0|
S1S0S9Z17fc60Vz;A2SaVz;Z17fc68A2A2S1S0S9Z17fc78Vz;A2SaVz;Z17fc80A2A2S1S0S9Z17db60Vz;A2SaVz;Z17db68A2A2S0S9Z17fcecVz;A2SaVz;Z17fcedA2A2A2A2A2").
Definition QRD (A : AA) (z : Z) : Prop := ltac2:(tb__ "0|0|
S1S71VA;Vz;A2S1S84S13VA;A1Vz;A2S83Vz;A1A2A2").
Lemma QRD_QFP : ltac2:(tb__ "0|0|
S12S6S71R2R1A2S78R3R2A2F_;Fz;FA;"). Proof. intros A z H. left. exact H. Qed.
Lemma QFP_push : ltac2:(tb__ "0|0|
S12S6S6S6S0S9Z1R3A2S9R3Z1eA2A2S0S9Z0R3A2SaR3Z10A2A2S80S13R6A1R5R4R3A4S71R7R4A2F_;F_;F_;Fz;Fk;Fc;FA;").
Proof. intros A c k z Hc Hk [H|H]; right; left; unfold pc_entry in H; lia. Qed.

Definition set_q (A : AA) (t g : list qbatch) : AA := ltac2:(tb__ "0|0|
S2aS13VA;A1S15VA;A1S1aVA;A1S19VA;A1S26VA;A1S1bVA;A1Vt;Vg;S22VA;A1S24VA;A1S23VA;A1S25VA;A1S21VA;A1S20VA;A1S1fVA;A1Af").
Definition cls_of (A : AA) (c : Z) : class_state := ltac2:(tb__ "0|0|
S51S1dS15VA;A1Vc;S31A4").
Definition push_cs (cs : class_state) (x : Z) : class_state := ltac2:(tb__ "0|0|
S38S34Vcs;A1S29Vcs;A1S32Vcs;A1S33Vcs;A1S49S6S30Vcs;A1S4aS6Vx;S46S6A1A3A3S35Vcs;A1S36Vcs;A1A7").
Definition set_cls (A : AA) (c : Z) (cs : class_state) : AA := ltac2:(tb__ "0|0|
S2aS13VA;A1S37S1dS15VA;A1S11Vc;A1Vcs;A4S1aVA;A1S19VA;A1S26VA;A1S1bVA;A1S18VA;A1S17VA;A1S22VA;A1S24VA;A1S23VA;A1S25VA;A1S21VA;A1S20VA;A1S1fVA;A1Af").
Definition push_cache (A : AA) (c x : Z) : AA := ltac2:(tb__ "0|0|
S89VA;Vc;S7fS74VA;Vc;A2Vx;A2A3").

Definition same_but_q (A A' : AA) : Prop := ltac2:(tb__ "0|0|
S2S12VA';S77VA;S18VA';A1S17VA';A1A3A3").

Definition same_but_qcs (A A' : AA) : Prop := ltac2:(tb__ "0|0|
S2S12VA';S2aS13VA;A1S15VA';A1S1aVA;A1S19VA';A1S26VA';A1S1bVA;A1S18VA';A1S17VA';A1S22VA;A1S24VA;A1S23VA;A1S25VA;A1S21VA;A1S20VA;A1S1fVA;A1AfA3").

Lemma set_q_fields : ltac2:(tb__ "0|2|
S12S3cS14A1M0G0S0S2S28S13S77R3R2R1A3M1A1S13R3A1A3S0S2S3cS1dA1S15G1A1S15R3A1A3S0S2S3dS1aG1A1S1aR3A1A3S0S2S3cS16A1S19G1A1S19R3A1A3S0S2S3cS3fS6S6A2A1S1bG1A1S1bR3A1A3S0S2G0S18G1A1R2A3S2G0S17G1A1R1A3A2A2A2A2A2A2Fg;Ft;FA;").
Proof. intros. repeat split; reflexivity. Qed.
Lemma same_but_q_refl : ltac2:(tb__ "0|0|
S12S72R1R1A2FA;"). Proof. intros A. destruct A. reflexivity. Qed.
Lemma same_but_q_set_q : ltac2:(tb__ "0|1|
S12S3cS14A1M0G0S72R3S77R3R2R1A3A2Fg;Ft;FA;"). Proof. intros. reflexivity. Qed.
Lemma same_but_q_trans : ltac2:(tb__ "0|1|
S12S12S12S72R3R2A2M0G0S72R5R3A2F_;F_;FC;FB;FA;").
Proof. intros A B C HB HC. unfold same_but_q in *. rewrite HC, HB. reflexivity. Qed.

Definition item_pure (A : AA) (it : Z * Z) : Prop := ltac2:(tb__ "0|5|
S13VA;A1S28S3eS6S6Vit;A3S6S40S6S6Vit;A3S6S0S9S8S5fZ800M0A2R2A2S0S9Z1R1A2S0S2S3dS59R1A1M1S47A3S5dS68R2A1A1S6S5cS27R5A1R1A2S6S0S9R1SbR5S6bR4A1A2M2A2S0S2S6SeSbG2R1A2M3S62R2A1M4A2Z0A3S9S8G3G4A2S29S74VA;R2A2A1A2A2A2Trb;Tc;F_;S2S3dG1S44A3S3S16S16S0S91S16R1S19VA;A1A3S0S2S6R4S8S8S2cR1A1S5aA2G0A2A3S2S6S3bR1A1S8S6aR3Z8A2Z1000A2A3A2A2Lch;A2F_;A2A2A2Tn;Tu;TG;").
Definition item_mem (m : bview) (it : Z * Z) : Prop := ltac2:(tb__ "0|6|
S3eS6S6Vit;A3S6S40S6S6Vit;A3S6S0S2S42S8aQ8M0A1M1A1Vm;SbR2Z10A2A1S43G1S8bG0Z3A2A2A3S0S6eVm;SbR2ZfA2SbR2ZeA2M2A3S0S6cVm;S6dG2U2SdR1S10Z2Z20A2M3A2A3A2S0S6cVm;S6dSbR2ZcA2U4SeR1G3A2A3A2S0S6eVm;SbR2Z8M4A2R2A3S0S50Vm;R2R1A3S6eVm;S57R2A1M5S8G5SdS8R1Z7A2G4A2A2A3A2A2A2A2A2A2Tn;Tu;").
Definition batch_pure (A : AA) (b : qbatch) : Prop := ltac2:(tb__ "0|6|
S0S9S5eS1eVb;A1M0A2S0S9SfS41S3fS6S6A2M1S2bVb;A1M2A2A1S66A2S0S3S6S6S0S2S6G0S8S5cS27S13VA;A1A1Z18M3A2ScZ10R1A2M4A2A3S0S9Z0M5R1A2S0S2S6SeR1Z200A2G5A3S9S8G4S58A2S29S74VA;G3A2A1A2A2A2A2Ly;A2S94G1S7dVA;A1G2A3A2A2A2").
Definition batch_mem (m : bview) (b : qbatch) : Prop := ltac2:(tb__ "0|8|
S0S6cVm;S6dS8S1eVb;A1M0Z8M1A2U8M2S39Vb;A1M3A3A2S0S6cVm;S6dS8G0Z10M4A2G2SfS41S3fS6S6A2M5S2bVb;A1M6A2A1A3A2S0S2S6G3S8S58S92S6G5G5S6S8S40S6S6R2A3R1A2Lacc;Lit;Z0G6A5A2A3S0S6eVm;S8G0Z18A2M7S8G0S58A2A3S45G5S2S42G5A1S93G5G6R2A3S43G5R1A2A3S0S6cVm;S6dS8G7ScG1SfR3A1A2A2G2SbS3eS6S6R2A3G4A2A3A2S7cVm;R2A2A2F_;Fit;Fi;A2A2A2A2").
Definition q_pure (A : AA) : Prop := ltac2:(tb__ "0|1|
S0S94S14S7bVA;A1S8dVA;A1M0A3Sa0S6S95S14S6S1eG0A4A2A2").
Definition q_mem (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|2|
S0S94S14S7aVm;A1S8dVA;A1A3S0S4eVm;S18VA;A1M0A2S0S4eVm;S17VA;A1M1A2S0S4dVm;S8S1cS13VA;A1A1Z50A2G0A3S0S4dVm;S8S4bZa0A2G1A3S6cVm;S6dS8S4bZ98A2U4Z0A3A2A2A2A2A2A2").

Definition qbounded (A : AA) : Prop := ltac2:(tb__ "0|0|
S0SaS4cS18VA;A1A1S10Z2Z30A2A2S9S4cS17VA;A1A1S5bA2A2").

Lemma quarantine_repr_split : ltac2:(tb__ "0|0|
S70S12S53R2R1A2S0S75R3R2A2S81R2A1A2F_;FA;Fm;").
Proof.
  intros m A (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10). unfold q_mem, qall, qbounded. split; [|split; [unfold kQuarantineCacheMax in H8; lia | exact H9]].
  split; [|split; [exact H2 | split; [exact H3 | split; [exact H4 | split; [exact H5 | exact H6]]]]].
  apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) H1 b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  split; [exact B2|]. split; [exact B3|]. split; [exact B5|]. split; [exact B6|].
  intros i it Hi. destruct (B7 i it Hi) as [C (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11)]. split; [exact C|].
  split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|]. split; [exact Q8|].
  exact Q11.
Qed.

Record cls_view (m : bview) (G : ageom) (L : list (Z * Z)) (c : Z) (cs : class_state) : Prop := mkCV {
  cv_ri_mutex : cell_ok m (mkACell (region_info (ag_spacebeg G) c + RI_mutex) 8 0);
  cv_ri_nfreed : cell_ok m (mkACell (region_info (ag_spacebeg G) c + RI_num_freed) 8 (Z.of_nat (length (cs_free_array cs))));
  cv_ri_mfa : cell_ok m (mkACell (region_info (ag_spacebeg G) c + RI_mapped_free_array) 8 (cs_mapped_free_array cs));
  cv_ri_au : cell_ok m (mkACell (region_info (ag_spacebeg G) c + RI_allocated_user) 8 (cs_allocated_user cs));
  cv_ri_mu : cell_ok m (mkACell (region_info (ag_spacebeg G) c + RI_mapped_user) 8 (cs_mapped_user cs));
  cv_ri_present : present m (region_info (ag_spacebeg G) c) (region_info (ag_spacebeg G) c + kRegionInfoStride);
  cv_bounds : cs_mapped_user cs mod kUserMapSize = 0 /\ 0 <= cs_allocated_user cs <= cs_mapped_user cs
              /\ cs_mapped_user cs + kUserMapSize <= kUserSpaceSize + kUserMapSize /\ cs_allocated_user cs mod Size c = 0;
  cv_fa_bounds : cs_mapped_free_array cs mod kFreeArrayMapSize = 0 /\ 4 * Z.of_nat (length (cs_free_array cs)) <= cs_mapped_free_array cs <= kFreeArraySize;
  cv_fa_cells : forall i x, nth_error (cs_free_array cs) i = Some x -> cell_ok m (mkACell (free_array (ag_spacebeg G) c + 4 * Z.of_nat i) 4 x);
  cv_fa_present : present m (free_array (ag_spacebeg G) c + 4 * Z.of_nat (length (cs_free_array cs))) (free_array (ag_spacebeg G) c + cs_mapped_free_array cs);
  cv_region_present : present_but m (region_beg (ag_spacebeg G) c) (region_beg (ag_spacebeg G) c + cs_mapped_user cs) L;
  cv_shadow_present : present m (Sh (region_beg (ag_spacebeg G) c)) (Sh (region_beg (ag_spacebeg G) c + cs_mapped_user cs));
  cv_count : cell_ok m (mkACell (pc_entry G c) 4 (Z.of_nat (length (cs_cache cs))));
  cv_max : cell_ok m (mkACell (pc_entry G c + 4) 4 (max_count c));
  cv_size : cell_ok m (mkACell (pc_entry G c + 8) 8 (Size c));
  cv_chunks : forall i x, nth_error (cs_cache cs) i = Some x -> cell_ok m (mkACell (pc_entry G c + 16 + 4 * Z.of_nat i) 4 x);
  cv_pc_present : present m (pc_entry G c) (pc_entry G c + 80);
  cv_len : Z.of_nat (length (cs_cache cs)) <= max_count c
}.

Record KQ_facts (A : AA) (rho : valuation) (m : bview) : Prop := mkKQF {
  kqf_geom : geom_ok (aa_geom A);

  kqf_rigid : rw rho 151%positive = Z_to_bv 64 (ag_thread (aa_geom A)) /\ rw rho 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))
              /\ rw rho 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A)) /\ rw rho 156%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize);

  kqf_rtc : rtc_inv m (aa_geom A);

  kqf_min : cell_ok m (mkACell (QG + 72) 8 kQuarantineMin);

  kqf_stats : present m (ag_thread (aa_geom A) + 2768) (ag_thread (aa_geom A) + 3168);

  kqf_len : length (aa_cls A) = 32%nat;
  kqf_cls : aa_cache_inited A = true -> forall c, 1 <= c <= 30 -> cls_view m (aa_geom A) (aa_live A) c (cls_of A c);

  kqf_qpure : q_pure A;

  kqf_ids : forall c, 1 <= c <= 30 -> NoDup (cs_free_array (cls_of A c) ++ cs_cache (cls_of A c) ++ live_ids (aa_geom A) A c ++ q_ids (aa_geom A) (qall A) c);

  kqf_sep : forall z, q_foot A z -> ~ (ag_thread (aa_geom A) <= z < ag_thread (aa_geom A) + 0x1000);
  kqf_sep3 : sep_geom3 (aa_geom A);

  kqf_top : top_high A rho;

  kqf_secq : forall it, In it (qitems (qall A)) -> is_primary (snd it) = false ->
      (fst it <= ag_spacebeg (aa_geom A) \/ ag_spacebeg (aa_geom A) + kSpaceSize + 4096 <= fst it - rz (snd it)) /\ fst it + snd it + 8 <= 140737479966720
}.

Section WithSegs.
Variable segs : list Segment.

Record KQ_laws (K : AA -> jpredA) : Prop := mkKQL {

  kq_stable : forall A, stableA segs QNPRE (K A);

  kq_facts : forall A rho tp tr md, K A rho tp tr md -> KQ_facts A rho (view segs (rm rho));

  kq_view : forall A rho rho' tp tr md,
      (forall i, rw rho' i = rw rho i) -> (forall l, rl rho' l = rl rho l) ->
      (forall z, ~ QW A z -> view segs (rm rho') z = view segs (rm rho) z) ->
      (forall z, QW A z -> view segs (rm rho) z <> None -> view segs (rm rho') z <> None) ->
      K A rho tp tr md -> K A rho' tp tr md;

  kq_perm : forall A t g rho tp tr md,
      Permutation (qall A) (t ++ g) -> K A rho tp tr md -> K (set_q A t g) rho tp tr md;

  kq_push_item : forall A rho rho' tp tr md g1 g2 a it i2 s s',
      aa_q_thread A = [] -> aa_q_global A = g1 ++ mkQB a (it :: i2) s :: g2 ->
      aa_cache_inited A = true -> is_primary (snd it) = true ->
      let G := aa_geom A in let c := it_cls it in let x := it_id G it in
      let k := Z.of_nat (length (cs_cache (cls_of A c))) in
      k < max_count c ->
      (forall i, rw rho' i = rw rho i) -> (forall l, rl rho' l = rl rho l) ->
      (forall z, ~ QW A z -> ~ push_zone G c k z -> view segs (rm rho') z = view segs (rm rho) z) ->
      (forall z, QW A z -> view segs (rm rho) z <> None -> view segs (rm rho') z <> None) ->
      cell_ok (view segs (rm rho')) (mkACell (pc_entry G c) 4 (k + 1)) ->
      cell_ok (view segs (rm rho')) (mkACell (pc_entry G c + 16 + 4 * k) 4 x) ->
      K A rho tp tr md ->
      K (push_cache (set_q A [] (g1 ++ mkQB a i2 s' :: g2)) c x) rho' tp tr md;

  kq_push_batch : forall A rho rho' tp tr md g1 g2 b,
      aa_q_thread A = [] -> aa_q_global A = g1 ++ b :: g2 ->
      qb_items b = [] ->
      aa_cache_inited A = true ->
      let G := aa_geom A in let x := qb_id G b in
      let k := Z.of_nat (length (cs_cache (cls_of A 24))) in
      k < max_count 24 ->
      (forall i, rw rho' i = rw rho i) -> (forall l, rl rho' l = rl rho l) ->
      (forall z, ~ QW A z -> ~ push_zone G 24 k z -> view segs (rm rho') z = view segs (rm rho) z) ->
      (forall z, QW A z -> view segs (rm rho) z <> None -> view segs (rm rho') z <> None) ->
      cell_ok (view segs (rm rho')) (mkACell (pc_entry G 24) 4 (k + 1)) ->
      cell_ok (view segs (rm rho')) (mkACell (pc_entry G 24 + 16 + 4 * k) 4 x) ->
      K A rho tp tr md ->
      K (push_cache (set_q A [] (g1 ++ g2)) 24 x) rho' tp tr md

}.

Definition JQ3 (K : AA -> jpredA) (A : AA) : jpredA := ltac2:(tb__ "0|0|
S55S3cS8aQ40A1A1S3cS97A1S96S0VK;VA;R4R3R2R1A5S75S6fVsegs;S54R4A1A2VA;A2A2Lmd;Ltr;Ltp;Lrho;").

Definition qpost (A A' : AA) : Prop := ltac2:(tb__ "0|0|
S0S86VA;VA';A2S0S2S3cS14A1S18VA';A1S46S14A1A3S0S2S45S41S1dS15VA';A1A2S41S1dS15VA;A1A2A3S0S6S2dVA;R1A2S2dVA';R2A2F_;Fc;S9S4cS17VA';A1A1S5bA2A2A2A2A2").

Definition JLQ3 (K : AA -> jpredA) (A : AA) : jpostA := ltac2:(tb__ "0|8|
S55S3cS8aQ40M0A1M1A1M2S55G2S3cS97A1S96S3S12S12S0VK;R1R5R4R3R2A5S0S75S6fVsegs;S54R5A1A2R1A2S0S9cVA;R1A2S0G1S4S78VA;S8cG0R1A2M3A2A1S2S42S8aQ8A1M4A1M5S54R7R2A2S54R9R2A2M6A3F_;Fa;S0S6S4S71VA;R1A2A1S2G5S6fVsegs;S54R7A1R2A3S6fVsegs;S54R9A1R2A3A3F_;Fz;S0S7S2S3cG4A1S56R6R1A2S56R8R1A2A3Fl;S0S5G1S0S9S61G3A2SaG3S60A2A2S4S2G5G6S48G4A1M7A3A1S4S2G5S54R8R3A2G7A3A1F_;F_;Fa;A2A2A2A2A2A2A2LA';A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").

Lemma JQ3_K : ltac2:(tb__ "0|0|
S12S98F_;S12S55S3cS8aQ40A1A1S3cS97A1S96S9bR6R5R4R3R2R1A6R7R6R5R4R3R2A5F_;Fmd;Ftr;Ftp;Frho;FA;FK;").
Proof. intros K A rho tp tr md [H _]. exact H. Qed.

Lemma JQ3_stable : ltac2:(tb__ "0|0|
S12S98F_;S12S7S9dR3A1S9fS79R2A2S9aVsegs;R3S9bR5R4A2A3F_;F_;Fn;FA;FK;").
Proof.
  intros K A n HL Hn rho rho' tp tr md md' Hag Hme [HK HQ]. split.
  - eapply (stableA_mono segs QNPRE n (K A) Hn (kq_stable K HL A)); eauto.
  - destruct Hag as (_ & _ & Hrm). replace (rm rho') with (rm rho); [exact HQ|].
    apply functional_extensionality. intros a. apply Hrm.
Qed.

Lemma JQ3_ok_frame : ltac2:(tb__ "0|0|
S12S98Fx;S12S9eOF_;S99Vsegs;R1R3R2A1A3S99Vsegs;R2S9bR4R3A2A3F_;Fok;FA;FK;").
Proof. intros K A ok H rho tp tr ms md msv' [HK _]. exact (H rho tp tr ms md msv' HK). Qed.

Lemma qpost_geom : ltac2:(tb__ "0|0|
S12S12S9cR2R1A2S2S28S13R2A1S13R3A1A3F_;FA';FA;").
Proof. intros A A' (E & _). rewrite E. reflexivity. Qed.

End WithSegs.
