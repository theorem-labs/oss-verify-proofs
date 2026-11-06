(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "sub"; "of_nat"; "mul"; "pow"; "div"; "leb"; "eqb"; "ltb"; "to_nat"; "shiftl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "mkACell"; "cell_ok"; "bview"; "present"; "acell"; "in_rangesZ"; "filled"; "ERRNO_A"; "RTC_A"; "c_addr"; "c_w"; "restrictv"; "cells_footb"; "cells_ok"; "maskv"; "rtc_cells"; "rtc_cells_img"; "rtc_inv"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "list"; "prod"; "option"; "bool"; "pair"; "Some"; "length"; "nat"; "app"; "fst"; "snd"; "andb"; "true"; "false"; "cons"; "nil"; "None"; "orb"; "negb"; "@Stdlib.Lists.List"; "In"; "nth_error"; "filter"; "fold_right"; "Exists"; "NoDup"; "existsb"; "forallb"; "hd"; "last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "FS_total"; "Sh"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "IMG_HI"; "fs_num_iter"; "kSpaceSize"; "fs_frame_size"; "kPtrArrayReserve"; "HIGH_SHADOW_END"; "fs_frame"; "is_primary"; "region_beg"; "rz"; "FS_frames_off"; "Size"; "dyn_in"; "fs_flags"; "fs_flags_off_nat"; "kQuarantineBatchSize"; "ClassID"; "FS_kFlagsOffset"; "HIGH_SHADOW_BEG"; "IMG_LO"; "LOW_SHADOW_BEG"; "SHADOW_GAP_BEG"; "dyn_ok"; "kUserMapSize"; "needed"; "round_up"; "kPtrArrayCommit"; "RI_allocated_meta"; "RI_allocated_user"; "RI_exhausted"; "RI_mapped_free_array"; "RI_mapped_meta"; "RI_mapped_user"; "RI_mutex"; "RI_num_freed"; "SHADOW_OFF"; "free_array"; "fs_hint_cell"; "kCompactPtrScale"; "kFreeArrayMapSize"; "kFreeArraySize"; "kQuarantineBatchCount"; "kQuarantineCacheMax"; "kQuarantineMax"; "kQuarantineMin"; "kRegionInfoStride"; "kUserSpaceSize"; "max_count"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "qbatch"; "aa_geom"; "ag_fsb"; "ageom"; "ag_spacebeg"; "ag_thread"; "AA"; "ag_ctx"; "ag_dtls"; "class_state"; "aa_live"; "topG"; "aa_sec"; "ag_pab"; "cs_empty"; "aa_cls"; "sc_map_beg"; "aa_depot"; "aa_q_global"; "aa_q_thread"; "aa_Kf"; "aa_Km"; "aa_cache_inited"; "aa_ptr_committed"; "qb_addr"; "sc_map_size"; "aa_V"; "aa_fs_busy"; "cs_allocated_user"; "aa_frames"; "aa_internal_inited"; "ag_top"; "sc_size"; "aa_fs_hint"; "ag_stack_bottom"; "ag_stack_top"; "ag_tp"; "cs_cache"; "is_large"; "qb_items"; "qb_size"; "PRIM_LIVE_MAX"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "dN"; "depot_state"; "large_live"; "mkAA"; "small_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv.WithSegs"; "bandtp_inv"; "present_but"; "geom_ok"; "in_maps"; "nthZ"; "SEC_INST"; "fs_footb"; "isum"; "AInvA"; "fs_busy"; "fs_inv"; "qsize"; "IA_BEG"; "IA_END"; "QG"; "band_page"; "rest_inv"; "same_but_fs"; "FS_NCLASSES"; "IA_MAP1"; "alloc_magic_ok"; "batch_repr"; "inv3"; "qb_dflt"; "qhdr_repr"; "qlarge"; "qlinks"; "quarantine_repr"; "IA_MAP1_SZ"; "busyb"; "class_repr"; "depot_wf"; "fs_class_okb"; "ia_inv";
"kAllocBegMagic"; "ledger_inv"; "live_block_repr"; "live_ids"; "live_sep"; "misc_inv"; "model_inv"; "primary_repr"; "q_foot"; "q_item_ok"; "rtc_extra"; "secondary_repr"; "sep_geom3"; "shadow_unpoisoned"; "slot_zone"; "slots"; "thread_inv"; "vm_geom"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "budget_boundD"; "gap_ok"; "maps_disjoint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qitems"; "qall"; "q_ids"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "vm_maps"; "Model"; "m_vmmaps"; "vm_noaccess"; "VmMaps"; "alloc_top"; "m_vm_lazy"; "page_in_ranges"; "vm_limit"; "vm_reserved"; "@Corelib.Init.Nat"; "add"; "@stdpp.base"; "NoDup"; "filter"; "@Corelib.Init.Peano"; "lt"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "mat_equiv"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "FACAP"; "MUCAP"; "prim_credit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "depot_mem"; "depot_vm"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit.
Import ListNotations.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma FS_frames_off_val : FS_frames_off = 36864. Proof. reflexivity. Qed.
Lemma FS_total_val : FS_total = 11571200. Proof. reflexivity. Qed.
Lemma FS_kFlagsOffset_val : FS_kFlagsOffset = 4096. Proof. reflexivity. Qed.
Lemma kSpaceSize_val : kSpaceSize = 2 ^ 37. Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Let view := view segs.

Definition geom_ok (G : ageom) : Prop := ltac2:(tb__ "0|11|
S0S61S88VG;A1M0S7fVG;A1M1S47A3S0S1S5Sa1VG;A1Z6245b8A3S0S61G0S82VG;A1M2Z1000M3A3S0S57G0S84VG;A1M4G3A3S0S57G0S85VG;A1M5G3A3S0S1S5S9S81VG;A1M6SdZ2M7Z10A2A2Z0M8A3S0S6S50G6A2S0S6S7S7G6S4dA2G3A2M9G0A2S0S2S6S7G1S47A2MaG2A2S6S7G2G3A2MbG1A2A2S0S2S6GaG4A2S6S7G4G3A2McG1A2A2S0S2S6GaG5A2S6S7G5G3A2MdG1A2A2S0S2S6GaG6A2S6G9G1A2A2S0S2S6GbG4A2S6GcG2A2A2S0S2S6GbG5A2S6GdG2A2A2S0S2S6GcG5A2S6GdG4A2A2S0S0S6G8S9fVG;A1MeA2S8GeSa0VG;A1MfA2A2S0S6GfSdG7Z2fA2A2S0S1S5S9S8aVG;A1S46A2G8A3S0S6Z7fff7f800000S9cVG;A1M10A2S6G10Z7fffff800000A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").

Lemma geom_top : ltac2:(tb__ "0|0|
S80Sb3R1A1S1S5S88R2A1S9cR2A1A3F_;FG;").
Proof. intros G HG. unfold topG. apply top_clamp_id. repeat (destruct HG as [? HG]). split; assumption. Qed.
Lemma geom_pab : ltac2:(tb__ "0|0|
S80Sb3R1A1S1S5S9S8aR2A1S46A2Z0A3F_;FG;").
Proof. intros G HG. repeat (destruct HG as [? HG]). assumption. Qed.

Definition nthZ {A} (l : list A) (i : Z) (d : A) : A := nth (Z.to_nat i) l d.
Definition fs_busy (A : AA) (c : Z) : list (Z * Z) := ltac2:(tb__ "0|1|
Sb5S29S2aS5S5A2M0A1S98VA;A1Vc;S38G0A1A4").
Definition busyb (A : AA) (c pos : Z) : bool := ltac2:(tb__ "0|1|
S42S2aS5S5A2M0G0S10S32S5S5R1A3Vpos;A2Lpf;SbaVA;Vc;A2A3").

Definition fs_footb (G : ageom) (z : Z) : bool := ltac2:(tb__ "0|1|
S7fVG;A1S5S3aS3aS34SfR1Vz;A2S11Vz;S7R1Z58A2A2A2S34SfS7R1S5cA2Vz;A2S11Vz;S7R1S47A2M0A2A2A2S34SfS48S7R1S55A2A1Vz;A2S11Vz;S48G0A1A2A2A2TF;").

Definition FS_NCLASSES : Z := 11.

Definition fs_inv (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|e|
S7eVA;A1S80S7fR1A1S5S0S1S30S2fS29S2aS5S5A2M0A1S98VA;A1A2UbM1A3S0S5S0S6Z0M2R1A2S8R1Sc3A2A2M3S0S41S5Se5G0S5S32S5S5A2SbaVA;R2A2A4A2G0S3cG0R1SbaVA;R3A2A3S0S0S6G2S32S5S5R2A3M4A2S8G4S4cR4A1A2A2S1S5S33S5S5R2A3S51R5R4G4A3A3A2F_;Fpf;A2F_;Fc;S0S0S1S30S2fS5S9eVA;A1M5A2G1A3S5G3S0S0S6G2Sb5S5G5R2G2A4M6A2S8G6SdZ2Z40A2A2A2S15Vm;S14S70R3R2A2U8G6A3A2A2F_;Fc;A2S0S5S5S0S6G2R2A2M7S8R2Sc3A2A2M8S0G7S8R2S4cR3A1A2A2M9S1S2bS26Q8MaA1MbA1Vm;S7S58R5R4A2R3A2A1S2eGbS27GaS2cS5L_;SceVA;R4R3A3McZ1G2X2cx2A2A2A3F_;F_;Fpos;Fc;S0S5S5G8G9S1S2cGcS36A3S17Vm;S51R6R5R4A3MdS7GdS4eR5A1A2A3F_;F_;F_;Fpos;Fc;S17Vm;S48S7R1S55A2A1S48S7R1S47A2A1A3A2A2A2A2A2TF;TG;").

Definition shadow_unpoisoned (m : bview) (b n : Z) : Prop := ltac2:(tb__ "0|8|
S0S5S0S6Z0M0R1A2S8R1SeVn;Z8M1A2M2A2A2S1S2bS26Q8M3A1M4A1M5Vm;S7S48Vb;A1M6R2A2A1S2eG4S27G3G0A2A2A3F_;Fg;S3S1S5S9Vn;G1A2M7G0A3A1S1G5Vm;S7G6G2A2A1S2eG4S27G3G7A2A2A3F_;A2").

Definition present_but (m : bview) (lo hi : Z) (L : list (Z * Z)) : Prop := ltac2:(tb__ "0|1|
S5S0S6Vlo;R1A2S8R1Vhi;A2A2S3S19VL;R2A2A1S4S26Q8A1M0G0S1S2bG0A1Vm;R4A1S2eG0R1A2A3Lb;A2F_;F_;Fz;").
Lemma present_but_of_present : ltac2:(tb__ "0|0|
S16S5S5S29S2aS5S5A2A1S17R4R3R2A3Sb2R5R4R3R2A4F_;FL;Fhi;Flo;Fm;").
Proof. intros m lo hi L H z Hz _. exact (H z Hz). Qed.
Lemma present_but_agree : ltac2:(tb__ "0|0|
S16S16S5S5S29S2aS5S5A2A1S5S0S6R4R1A2S8R1R3A2A2S3S19R3R2A2A1S1S2bS26Q8A1A1R7R3A1R8R3A1A3F_;F_;Fz;Sb2R6R4R3R2A4Sb2R6R5R4R3A4F_;F_;FL;Fhi;Flo;Fm';Fm;").
Proof. intros m m' lo hi L AG H z Hz Hn. rewrite (AG z Hz Hn). exact (H z Hz Hn). Qed.
Lemma present_but_mono : ltac2:(tb__ "0|4|
S16S16S5S5S29S2aS5S5A2A1M0G0S5S19R3R1A2S19R3R2A2F_;Fz;S5S0S6R6R1A2S8R1R5A2A2S3S19R4R2A2A1S3S1S2bS26Q8A1M1A1M2RaR3A1S39G1A1M3A3A1S3S1G2RaR4A1G3A3A1F_;F_;F_;Fz;Sb2R8R6R5R4A4Sb2R8R7R6R4A4F_;F_;F_;FL';FL;Fhi;Flo;Fm';Fm;").
Proof.
  intros m m' lo hi L L' HL HM H z Hz Hn. destruct (H z Hz (fun X => Hn (HL z X))) as [b Hb].
  destruct (m' z) as [b'|] eqn:E; [exists b'; reflexivity|]. exfalso. apply (HM z Hz Hn); [rewrite Hb; discriminate | exact E].
Qed.
Lemma present_but_sub : ltac2:(tb__ "0|0|
S16S5S5S5S5S29S2aS5S5A2A1S6R5R3A2S6R3R5A2Sb2R8R7R6R3A4Sb2R9R6R5R4A4F_;F_;F_;FL;Fhi';Flo';Fhi;Flo;Fm;").
Proof. intros m lo hi lo' hi' L H1 H2 H z Hz Hn. apply (H z); [lia | exact Hn]. Qed.
Lemma present_of_but : ltac2:(tb__ "0|0|
S16S5S5S29S2aS5S5A2A1S5S0S6R4R1A2S8R1R3A2A2S3S19R3R2A2A1F_;Fz;Sb2R5R4R3R2A4S17R6R5R4A3F_;F_;FL;Fhi;Flo;Fm;").
Proof. intros m lo hi L HN H z Hz. exact (H z Hz (HN z Hz)). Qed.

Definition kAllocBegMagic : Z := 0xCC6E96B9CC6E96B9.
Definition alloc_magic_ok (m : bview) (b n : Z) : Prop := ltac2:(tb__ "0|4|
S2S1S5S54Vn;A1M0Z10M1A3S0S15Vm;S14SaVb;G0A2M2U8M3Sd3A3A2S15Vm;S14S7G2Z8A2G3SaVb;G1A2A3A2A2A2").
Definition live_block_repr (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|5|
S5S5S3cS2aS5S5A2S2dS5S5R2R1A4S87VA;A1A3S0S1S2bS26Q8M0A1M1A1M2Vm;SaR3Z10A2A1S2eG1S27G0Z2M3A2A2A3S0S15Vm;S14SaR3ZcA2U4S9R2SdG3Z20A2M4A2A3A2S0S15Vm;S14SaR3ZeA2U2SeR2G4A2A3A2S0Se0Vm;R3R2A3S0Sc5Vm;R3R2A3S4G1G1S0S1G2Vm;SaR4ZfA2A1S2eG1R1A2A3S1S5S9S28G0R1A2Z4A2Z1A3A2Lt;A2A2A2A2A2A2F_;Fn;Fb;").

Definition live_ids (G : ageom) (A : AA) (c : Z) : list Z := ltac2:(tb__ "0|3|
Se5S2aS5S5A2M0S5G0SeSaSaS32S5S5R1A3S54S33S5S5R1A3M1A1A2S53S81VG;A1Vc;A2A2Z10A2Lbn;SfbG0S29G0A1S10eG0A1G0S10cS34S52G1A1S10S5bS63G1A1A1Vc;A2A2M2A1Lbn;G0S10dG2A1Lx;S87VA;A1A6A4").

Definition slots (cs : class_state) (c : Z) : Z := ltac2:(tb__ "0|0|
SeS99Vcs;A1S56Vc;A1A2").
Definition class_repr (m : bview) (G : ageom) (A : AA) (c : Z) (cs : class_state) : Prop := ltac2:(tb__ "0|1f|
S7bS81VG;A1M0Vc;A2S5S53G0Vc;A2S5S6fG0Vc;A2S5S0S15Vm;S14S7R3S6cA2U8M1Z0M2A3A2S0S15Vm;S14S7R3S6dA2G1SbS2fS5Sa7Vcs;A1M3A2M4A1M5A3A2S0S15Vm;S14S7R3S69A2G1Sa8Vcs;A1M6A3A2S0S15Vm;S14S7R3S67A2G1S99Vcs;A1M7A3A2S0S15Vm;S14S7R3S66A2G1G2A3A2S0S15Vm;S14S7R3S6bA2G1Sa9Vcs;A1M8A3A2S0S15Vm;S14S7R3S6aA2G1G2A3A2S0S15Vm;S14S7R3S68A2U1G2A3A2S0S17Vm;R3S7R3S78A2A3S0S1S5S9G8S62A2G2A3S0S0S6G2G7A2S6G7G8A2A2S0S6S7G8S62A2S7S79S62A2A2S0S1S5S9G7S56Vc;A1M9A2G2A3S0S1S5S9G6S72A2G2A3S0S0S6ScZ4MaG5A2MbG6A2S6G6S73A2A2S0S30S5S1S2bS5A1McS3dS5G3R2A3S2eS5R1A2MdA3S15Vm;S14S7R4ScGaSbR3A1A2MeA2U4MfR2A3A2F_;Fx;Fi;S0S17Vm;S7R1GbA2S7R1G6A2A3S0S5S3cS5R1S31S5G3Sa2Vcs;A1M10A3A3S0S6G2R2A2S0S1S5S9S13R2S71A2M11G9A2G2A3S6S7G11G9A2G7A2A2A2F_;Fx;S0Sb2Vm;R2S7R2G8A2M12S87VA;A1M13A4S0S17Vm;S48R2A1S48G12A1A3S0S17Vm;S7S7S82VG;A1Zd0A2ScZ50M14Vc;A2A2M15S7G15G14A2M16A3S0SfaS5S31S5G3S31S5G10S31S5Sd6VG;VA;Vc;A3M17SeeVG;SedVA;A1Vc;A3M18A3A3A3A2S0S5S5S3cS2aS5S5A2S2dS5S5R2R1A4G13A3S1S2cS52R2A1S35A3S1S5S5bS63R3A1A1Vc;A3S0S6R7SaR5S54R4A1A2M19A2S0S1S5S9SaG19R7A2M1aG9A2G2A3S6S7G1aG9A2G7A2A2A2F_;F_;F_;Fn;Fb;S0S1S2cS93VA;A1M1bS35A3S0S15Vm;S14G15GfSbS2fS5G10A2M1cA1M1dA3A2S0S15Vm;S14S7G15GaA2GfS7aVc;A1M1eA3A2S0S15Vm;S14S7G15Z8A2G1G9A3A2S0S30S5S1GcS3dS5G10R2A3GdA3S15Vm;S14S7S7G15Z10A2GeA2GfR2A3A2F_;Fx;Fi;S6G1dG1eA2A2A2A2A2F_;S0S1S2cG1bS36A3S0S1S29S5A1G10S38S5A1A3S1aVm;G15G16G2A4A2F_;S0S8G8S7G7G9A2A2S0S1S5Se2Vcs;Vc;A2SbSf9Sf9Sf9G4G1cA2S2fS5G17A2A2S2fS5G18A2A2A1A3S0S6G8S107Vc;A1A2S6G6S106Vc;A1A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Tfa;Trb;Tri;").
Definition primary_repr (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|1|
S0S1S30S2fS86S8cVA;A1M0A2U20A3S0S1S86Sb5S86G0Z0S8bA4S8bA3S0S1S86Sb5S86G0Z1fS8bA4S8bA3S5S0S6Z1R1A2S6R1Z1eA2A2ScfVm;S7eVA;A1VA;R2Sb5S86G0R2S8bA4A5F_;Fc;A2A2A2").

Definition SEC_INST : Z := 0xeddd8.
Definition secondary_repr (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|11|
S7eVA;A1S80S0S30S7cS1S2bS7cA1S3dS7cS89VA;A1M0R2A3S2eS7cR1A2A3S0S15Vm;S14S7S8dR2A1M1Z0M2A2U8M3G1A3A2S0S15Vm;S14S7G1Z8M4A2G3S96R2A1M5A3A2S0S15Vm;S14S7G1Z10M6A2G3S9dR2A1M7A3A2S0S15Vm;S14S7G1Z18M8A2G3SbR3A1M9A3A2S0S15Vm;S14S7S8aR4A1ScG4G9A2A2G3G1A3A2S0S1S5S9G1S46A2G2A3S0S1S5S9G5S46A2G2A3S0S6S7S46G7A2G5A2S0S8Z10000G7A2S0S57S88R4A1MaG1G5A3S0S1S5G5S7S64G7S46A2S46A2A3S0S6S7G1G5A2MbGaA2S0Sb2Vm;G1GbS87VA;A1A4S17Vm;S48G1A1S48GbA1A3A2A2A2A2A2A2A2A2A2A2A2A2A2F_;Fch;Fi;S0S17Vm;S7S8aR1A1McScG4SbS2fS7cG0A2A1MdA2MeA2S7GcS94VA;A1MfA2A3S0S0S6GeGfA2S6GfS4fA2A2S0S1S5S9GfS65A2G2A3S0S61S88R1A1GcS4fA3S0S15Vm;S14Sb6G3S46A3A2S0S15Vm;S14S7Sb6G4A2G3GcA3A2S0S15Vm;S14S7Sb6G6A2G3GcA3A2S0S15Vm;S14S7Sb6G8A2G3S4fA3A2S0S15Vm;S14S7Sb6Z30A2G3SeGfG4A2A3A2S0S15Vm;S14S7Sb6Z38A2G3GdA3A2S0S17Vm;S7Sb6Z40A2Zee040M10A3S0S15Vm;S14G10U4G2A3A2S17Vm;Zee048Zee070A3A2A2A2A2A2A2A2A2A2A2A2A2A2TG;").

Definition q_item_ok (m : bview) (A : AA) (it : Z * Z) : Prop := ltac2:(tb__ "0|b|
S7eVA;A1S80S32S5S5Vit;A3S5S33S5S5Vit;A3S5S0S6S7S4bZ800M0A2R2A2S0S6Z1R1A2S0S1S2bS26Q8M1A1M2A1Vm;SaR2Z10A2A1S2eG2S27G1Z3A2A2A3S0S17Vm;SaR2ZfA2SaR2ZeA2M3A3S0S15Vm;S14G3U2SeR1SdZ2Z20A2M4A2A3A2S0S15Vm;S14SaR2ZcA2U4S9R1G4A2A3A2S0S17Vm;SaR2Z8M5A2R2A3S0Sc5Vm;R2R1A3S0S1S2cS52R1A1M6S35A3S5bS63R2A1A1S5S53S81R5A1R1A2S5S0S6R1SaR5S54R4A1A2M7A2S0S1S5S9SaG7R1A2M8S56R2A1M9A2Z0A3S6S7G8G9A2S99Sb5S86S8cVA;A1R2S8bA4A1A2A2A2Trb;Tc;F_;S0S1S2cG6S36A3S4S7cS7cS0S3cS7cR1S89VA;A1A3S0S1S5R4S7S7S8dR1A1S46A2G0A2A3S1S5S9dR1A1S7S64R3G5A2Z1000A2A3A2A2Lch;A2F_;S17Vm;S48R2A1MaS7GaSeS7R1Z7A2G5A2A2A3A2A2A2A2A2A2A2A2A2A2Tn;Tu;TG;").
Definition batch_repr (m : bview) (A : AA) (b : qbatch) : Prop := ltac2:(tb__ "0|c|
S0S6S4bS95Vb;A1M0A2S0S15Vm;S14S7G0Z8M1A2U8M2Sa5Vb;A1M3A3A2S0S15Vm;S14S7G0Z10M4A2G2SbS2fS2aS5S5A2M5Sa4Vb;A1M6A2A1M7A3A2S0S6G7S74A2S0S1S5G3S7S5aS3fS5G5G5S5S7S33S5S5R2A3R1A2Lacc;Lit;Z0M8G6A5A2A3S0S17Vm;S7G0Z18M9A2MaS7G0S5aA2A3S0S30G5S1S2bG5A1S3dG5G6R2A3S2eG5R1A2A3S0S15Vm;S14S7GaScG1SbR3A1A2A2G2SaS32S5S5R2A3G4A2A3A2SdcVm;VA;R2A3A2F_;Fit;Fi;S4S5S5S0S1S5G0S7S53S81S7eVA;A1A1G9A2ScG4R1A2MbA2A3S0S6G8R1A2S0S1S5S9R1Z200A2G8A3S6S7GbS5aA2S99Sb5S86S8cVA;A1G9S8bA4A1A2A2A2A2Lx;A2A2A2A2A2A2A2A2").

Definition qsize (l : list qbatch) : Z := ltac2:(tb__ "0|0|
S3fS5S7dS7dS5S7Sa5R2A1R1A2Lacc;Lb;Z0Vl;A5").

Fixpoint qlinks (m : bview) (l : list qbatch) : Prop :=
  match l with
  | [] => True
  | b :: r => cell_ok m (mkACell (qb_addr b) 8 (match r with [] => 0 | b' :: _ => qb_addr b' end)) /\ qlinks m r
  end.
Definition qb_dflt : qbatch := mkQB 0 [] 0.

Definition qhdr_repr (m : bview) (hdr : Z) (l : list qbatch) : Prop := ltac2:(tb__ "0|3|
S0S15Vm;S14Vhdr;U8M0SbS2fS7dVl;A2A1A3A2S0S3S1S29S7dA1Vl;S38S7dA1A3A1S0S15Vm;S14S7Vhdr;Z8A2M1G0S95S44S7dSc8Vl;A3A1A3A2S15Vm;S14S7Vhdr;Z10A2G0S95S45S7dVl;Sc8A3A1A3A2A2F_;S0S17Vm;G1S7Vhdr;Z18A2M2A3S15Vm;S14G2G0SbcVl;A1A3A2A2A2A2").
Definition QG : Z := 0xee070.
Definition quarantine_repr (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|3|
S0Se6S7dSc6Vm;VA;A2S31S7dS90VA;A1M0S8fVA;A1M1A3M2A3S0ScbVm;G0A2S0ScbVm;G1A2S0Sc9Vm;S7S82S7eVA;A1A1Z50A2G0A3S0Sc9Vm;S7SbfZa0A2G1A3S0S15Vm;S14S7SbfZ98A2U4Z0A3A2S0S15Vm;S14S7SbfZ48A2U8S77A3A2S0S6SbcG0A1S75A2S0S6SbcG1A1S76A2SfaS5Se5S7dS5S95G2A4A2A2A2A2A2A2A2A2A2A2").

Definition qlarge (A : AA) : Z := ltac2:(tb__ "0|1|
SbS2fS2aS5S5A2M0S3eG0Sa3SecSedVA;A1A1A3A2A1").
Definition isum (l : list (Z * Z)) : Z := ltac2:(tb__ "0|1|
S3fS5S2aS5S5A2M0G0S5S7S33S5S5R2A3R1A2Lacc;Lit;Z0Vl;A5").
Lemma isum_app : ltac2:(tb__ "0|2|
S29S2aS5S5A2M0A1M1G1S1S5Sb8S31G0R2R1A3A1S7Sb8R2A1Sb8R1A1A2A3Fl2;Fl1;").
Proof. induction l1 as [|x l1 IH]; intros l2; [reflexivity|]. cbn [app]. unfold isum in *. cbn [fold_right]. rewrite IH. lia. Qed.
Lemma isum_large : ltac2:(tb__ "0|1|
S29S2aS5S5A2M0A1G0S3cG0R1R2A3S6Z1S33S5S5R2A3A2F_;Fit;S6ScZfc01SbS2fG0S3eG0Sa3R2A3A2A1A2Sb8R2A1A2F_;Fl;").
Proof.
  induction l as [|x l IH]; intros H; [cbn; lia|].
  specialize (IH (fun it Hit => H it (or_intror Hit))). pose proof (H x (or_introl eq_refl)) as Hx.
  cbn [List.filter]. unfold isum in *. cbn [fold_right]. destruct (is_large x) eqn:E; cbn [length].
  - unfold is_large in E. apply Z.leb_le in E. rewrite Nat2Z.inj_succ. set (k := Z.of_nat _) in *. clearbody k. clear -IH E. lia.
  - lia.
Qed.
Lemma qitems_app : ltac2:(tb__ "0|2|
S29S7dA1M0G0S1S29S2aS5S5A2M1A1SecS31S7dR2R1A3A1S31G1SecR2A1SecR1A1A3A3Fl2;Fl1;").
Proof. intros. unfold qitems. apply flat_map_app. Qed.
Lemma isum_qitems_le : ltac2:(tb__ "0|1|
S16S83S29S7dA1Se6S7dSc6R3R2A2R1A3S0S2aS5S5A2M0S3cG0R1SecR3A1A3S6Z1S33S5S5R2A3A2F_;Fit;S6Sb8SecR2A1A1SbcR2A1A2A2F_;Fl;FA;Fm;").
Proof.
  intros m A. induction l as [|b l IH]; intros HF; [split; [intros it []| cbn; lia]|].
  inversion HF as [|? ? Hb HF']; subst. destruct (IH HF') as [I1 I2].
  destruct Hb as (_ & _ & _ & _ & Hsz & _ & Hit & _).
  assert (B1 : forall it, In it (qb_items b) -> 1 <= snd it).
  { intros it Hin. destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (Hit i it Hi) as [_ Hq]. destruct Hq as (_ & Hn & _). exact Hn. }
  split.
  - intros it Hin. unfold qitems in Hin. cbn [flat_map] in Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (B1 it Hin) | exact (I1 it Hin)].
  - unfold qitems in *. cbn [flat_map qsize fold_right]. fold (qsize l). rewrite isum_app. fold (isum (qb_items b)) in Hsz. unfold kQuarantineBatchSize in Hsz. lia.
Qed.
Lemma qlarge_bound : ltac2:(tb__ "0|1|
S16S83SccR2R1A2S0S6Z0ScaR2A1M0A2S6G0Z1051A2A2F_;FA;Fm;").
Proof.
  intros m A (HF & _ & _ & _ & _ & _ & _ & HT & HG & _). unfold qlarge. split; [lia|].
  destruct (isum_qitems_le m A _ HF) as [I1 I2]. pose proof (isum_large _ I1) as IL.
  assert (QS : forall l1 l2, qsize (l1 ++ l2) = qsize l1 + qsize l2).
  { induction l1 as [|x t IHt]; intros l2; [reflexivity|]. cbn [app]. unfold qsize in *. cbn [fold_right]. rewrite IHt. lia. }
  unfold qall in *. rewrite QS in I2. unfold kQuarantineCacheMax, kQuarantineMax in *. lia.
Qed.

Definition depot_wf (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|0|
S10aS8eVA;A1Vm;A2").

Definition live_sep (A : AA) : Prop := ltac2:(tb__ "0|8|
S5S5S3cS2aS5S5A2S2dS5S5R2R1A4S87VA;A1A3S0S6Z1R2A2S0S6S7S4bZ1000M0A2R3A2S0S6S7R3R2A2M1S88S7eVA;A1M2A1A2S0S2S6G1S7fG2A1M3A2S6S7G3S47A2SaR3Z10A2M4A2A2S0S2S6G1S82G2A1M5A2S6S7G5G0A2G4A2A2S0S2S6G1S84G2A1M6A2S6S7G6G0A2G4A2A2S0S2S6G1S85G2A1M7A2S6S7G7G0A2G4A2A2S2S6G1S4aA2S6S49G4A2A2A2A2A2A2A2A2A2F_;Fn;Fb;").

Definition IA_BEG : Z := 0xf2600.
Definition IA_END : Z := 0x173630.
Definition IA_MAP1 : Z := 0xf2608.
Definition IA_MAP1_SZ : Z := 0x40000.
Definition ia_inv (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|6|
S0S1S2bS26Q8M0A1M1A1M2Vm;Z180e89A1S2eG1S27G0Z0M3A2A2M4A3S0S1G2Vm;Z180e8aA1G4A3S0S1G2Vm;Z180e8bA1G4A3S2cOL_;S9bVA;A1S0S1G2Vm;Z180e88A1M5S2eG1S27G0Z1A2A2A3S1aVm;Sc4S7Sc4ScdA2G3A4A2S0S1G2G5G4A3S1aVm;SbdSbeG3A4A2X2cx2A2A2A2").

Definition thread_inv (m : bview) (G : ageom) : Prop := ltac2:(tb__ "0|4|
S0S1S2bS26Q8M0A1M1A1Vm;S7S82VG;A1M2Zc60A2M3A1S2eG1S27G0Z0A2A2A3S17Vm;S7G2Za80A2G3A3A2").

Definition rtc_extra : list acell := ltac2:(tb__ "0|4|
S37S18S14Z173661U1M0Z1M1A3S37S18S14Zeec4dG0G1A3S37S18S14Z183018U4M2Z0M3A3S37S18S14Z182f1cG2G3A3S37S18S14Ze9b28U8Z1a36fA3S38S18A1A3A3A3A3A3").

Definition misc_inv (m : bview) : Prop := ltac2:(tb__ "0|0|
S0S21Vm;SddA2S0S17Vm;Z173660Z173661A3S17Vm;S1bS7S1bZ4A2A3A2A2").

Definition rest_inv (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|0|
S0Sd7VA;A1S0Sd5Vm;VA;A2S0SdaVm;VA;A2S0SdeVm;VA;A2S0SccVm;VA;A2S0Sd0Vm;VA;A2S0Sd2Vm;VA;A2S0Se3Vm;S7eVA;A1A2Sd8Vm;A1A2A2A2A2A2A2A2A2").

Definition same_but_fs (A A' : AA) : Prop := ltac2:(tb__ "0|1|
S0S1S80S7eVA';A1S7eVA;A1A3S0S1S29S86A1S8cVA';A1S8cVA;A1A3S0S1S2cS93VA';A1S93VA;A1A3S0S1S29S7cA1S89VA';A1S89VA;A1A3S0S1S5S94VA';A1S94VA;A1A3S0S1S29S2aS5S5A2A1S87VA';A1S87VA;A1A3S0S1S29S7dA1M0S90VA';A1S90VA;A1A3S0S1G0S8fVA';A1S8fVA;A1A3S0S1SabS8eVA';A1S8eVA;A1A3S0S1S2cS9bVA';A1S9bVA;A1A3S0S1S5S97VA';A1S97VA;A1A3S0S1S5S92VA';A1S92VA;A1A3S1S5S91VA';A1S91VA;A1A3A2A2A2A2A2A2A2A2A2A2A2A2").

Lemma rest_inv_fs_blind : ltac2:(tb__ "0|0|
S16S83S83Sc2R2R1A2Sc1R4R3A2Sc1R5R3A2F_;F_;FA';FA;Fm;").
Proof.
  intros m A A' (Hg & Hc & Hci & Hs & Hp & Hl & Hqt & Hqg & Hd & Hii & HV & HKm & HKf) H.
  unfold rest_inv, live_sep, live_block_repr, primary_repr, secondary_repr, quarantine_repr, batch_repr, q_item_ok, depot_wf, class_repr, live_ids, ia_inv, thread_inv, qall in *.
  rewrite Hg, Hc, Hci, Hs, Hp, Hl, Hqt, Hqg, Hii, Hd. exact H.
Qed.

Definition fs_class_okb (c : Z) : bool := ltac2:(tb__ "0|7|
S34S34S34S34S34S34SfS7S59S12Vc;A1A1M0S4cVc;A1M1A2Z8000A2SfS7ScVc;SdZ2Z14A2M2A2ScG1S4eVc;A1M3A2M4A2ScZbG2A2A2A2S10G4G2A2A2S10S9G3Z40M5A2Z0M6A2A2S11G6G1A2A2SfG5G3A2A2SfG6G0A2A2").
Lemma fs_class_ok_all : ltac2:(tb__ "0|0|
S1S2cS43S5Sd1Se5S30S5SbSe7U0UbA2A4A3S35A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fs_class_ok : ltac2:(tb__ "0|8|
S5S0S6Z0M0R1A2S8R1ZbM1A2A2S0S6S7S59S12R2A1A1M2S4cR2A1M3A2Z8000A2S0S6S7ScR2SdZ2Z14A2M4A2ScG3S4eR2A1M5A2M6A2ScG1G4A2A2S0S1S5G6G4A3S0S1S5S9G5Z40M7A2G0A3S0S8G0G3A2S0S6G7G5A2S6G0G2A2A2A2A2A2A2A2F_;Fc;").
Proof.
  intros c Hc.
  assert (Hin : In c (map Z.of_nat (seq 0 11))).
  { apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
  pose proof (proj1 (forallb_forall _ _) fs_class_ok_all c Hin) as H. unfold fs_class_okb in H.
  repeat (apply andb_prop in H; destruct H as [H ?]).
  apply Z.leb_le in H. apply Z.leb_le in H5. apply Z.eqb_eq in H4. apply Z.eqb_eq in H3. apply Z.ltb_lt in H2. apply Z.leb_le in H1. apply Z.leb_le in H0.
  repeat split; assumption.
Qed.

Lemma fs_flags_off_mono : ltac2:(tb__ "0|0|
S30S30SfcR2R1A2SfdR2UbA2S6S7S59R4A1S4cSbR4A1A1A2S59R3A1A2F_;F_;Fc2;Fc1;").
Proof.
  intros c1 c2 Hlt Hle. induction c2 as [|c2 IH]; [lia|].
  cbn [fs_flags_off_nat]. destruct (Nat.eq_dec c1 c2) as [->|Hne]; [lia|].
  assert (0 <= fs_num_iter (Z.of_nat c2)).
  { unfold fs_num_iter. destruct (Z_le_dec 0 (FS_LOG - 6 - Z.of_nat c2)).
    - rewrite Z.shiftl_mul_pow2 by lia. apply Z.mul_nonneg_nonneg; [lia|]. apply Z.pow_nonneg. lia.
    - rewrite Z.shiftl_div_pow2 by lia. apply Z.div_pos; [lia|]. apply Z.pow_pos_nonneg; lia. }
  specialize (IH ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma fs_flags_inj : ltac2:(tb__ "0|3|
S5S5S5S5S5S0S6Z0R4A2M0S8R4ZbA2A2M1S0G0S8R4S4cR5A1A2A2M2G1G2S1S5S7S58R9R8A2R7A2S7S58R9R6A2R5A2A3S0S1S5R9R7A3S1S5R8R6A3A2F_;F_;F_;F_;F_;Fp2;Fc2;Fp1;Fc1;FF;").
Proof.
  intros F c1 p1 c2 p2 Hc1 Hp1 Hc2 Hp2 E. unfold fs_flags in E.
  destruct (Z.lt_trichotomy c1 c2) as [Hlt|[Heq|Hgt]].
  - pose proof (fs_flags_off_mono (Z.to_nat c1) (Z.to_nat c2) ltac:(lia) ltac:(lia)). rewrite Z2Nat.id in H by lia. lia.
  - subst. lia.
  - pose proof (fs_flags_off_mono (Z.to_nat c2) (Z.to_nat c1) ltac:(lia) ltac:(lia)). rewrite Z2Nat.id in H by lia. lia.
Qed.

Lemma fs_frames_disjoint : ltac2:(tb__ "0|5|
S5S5S5S5S5S0S6Z0R4A2M0S8R4ZbA2A2M1S0G0S8R4S4cR5A1A2A2M2G1G2S2S3S1S5R8R6A3A1S3S1S5R7R5A3A1A2S2S6S7S51RaR9R8A3M3S4eR9A1A2S51RaR7R6A3M4A2S6S7G4S4eR7A1A2G3A2A2F_;F_;F_;F_;F_;Fp2;Fc2;Fp1;Fc1;FF;").
Proof.
  intros F c1 p1 c2 p2 Hc1 Hp1 Hc2 Hp2 Hne. unfold fs_frame. unfold FS_LOG. change (Z.shiftl 1 20) with (2 ^ 20).
  destruct (fs_class_ok c1 Hc1) as (_ & _ & K1 & _ & _ & S1 & _). destruct (fs_class_ok c2 Hc2) as (_ & _ & K2 & _ & _ & S2 & _).
  destruct (Z.lt_trichotomy c1 c2) as [Hlt|[Heq|Hgt]].
  - left. assert (p1 * fs_frame_size c1 + fs_frame_size c1 <= 2 ^ 20) by nia. nia.
  - subst c2. assert (p1 <> p2) by lia. destruct (Z.lt_trichotomy p1 p2) as [L|[L|L]]; [left; nia | lia | right; nia].
  - right. assert (p2 * fs_frame_size c2 + fs_frame_size c2 <= 2 ^ 20) by nia. nia.
Qed.

Lemma fs_geom_nums : ltac2:(tb__ "0|5|
S80S5S5Sb3R3A1S0S6Z0M0R3A2M1S8R3ZbA2A2S0G1S8R3S4cR4A1A2A2S7fR6A1S5S51R1R6R5A3S5S7S58R2R7A2R6A2S5S4eR8A1S5S0S6S7R4S55A2M2R3A2S0S6S7R3R1A2S7R4S47A2M3A2S0S1S5S9R3Z40M4A2G0A3S0S1S5S9R1G4A2G0A3S0S6G4R1A2S0S6S7R4S5cA2R2A2S0S6S7R2Z1A2G2A2S0S6S4bR4A2S0S6G3S88RaA1A2S1S5S9R4S46A2G0A3A2A2A2A2A2A2A2A2A2Tsz;Tfl;Tf;TF;F_;F_;F_;Fpos;Fc;FG;").
Proof.
  intros G c pos HG Hc Hpos F f fl sz.
  destruct (fs_class_ok c Hc) as (K1 & K2 & K2' & K3 & K4 & K5 & K6).
  destruct HG as (GF & _). pose proof (dyn_ok_big _ _ _ GF ltac:(rewrite FS_total_val; lia)) as G2. destruct GF as (G1 & _ & _ & G3 & _).
  subst F f fl sz. unfold fs_frame, fs_flags. rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in *.
  unfold FS_LOG. change (Z.shiftl 1 20) with (2 ^ 20).
  assert (M1 : pos * fs_frame_size c + fs_frame_size c <= fs_num_iter c * fs_frame_size c) by nia.
  assert (M2 : 0 <= pos * fs_frame_size c) by nia.
  repeat split; try lia.
  unfold PG in G1.
  assert (D1 : (64 | ag_fsb G)). { apply (Z.divide_trans _ 4096); [exists 64; reflexivity | apply Z.mod_divide; lia]. }
  assert (D2 : (64 | fs_frame_size c)) by (apply Z.mod_divide; lia).
  apply Z.mod_divide; [lia|].
  destruct D1 as [q1 E1]. destruct D2 as [q2 E2]. rewrite E1, E2.
  exists (q1 + 576 + c * 2 ^ 14 + pos * q2). lia.
Qed.

Lemma aa_frames_fact : ltac2:(tb__ "0|4|
S16S83S5S5SbbR4R3A2S3cS2aS5S5A2M0S2dS5S5R3R2A4S9aR4A1A3S4S5S5S4S5S5S4S29G0A1M1G1S4G1G1S0S0S6Z0M2R4A2S8R4ZbA2A2S0S1S5R7S4eR4A1A3S0S1G1SbaR9R4A2M3S31G0R2S37G0S2dS5S5R3R8A4R1A3A3A3S0S3S3cS5R3Se5G0S5S32S5S5A2R2A4A3A1S0S0S6G2R3A2S8R3S4cR4A1A2A2S0S1S5R8S51S7fS7eR9A1A1R4R3A3A3S1S2bG1A1S3dG1S98R9A1S12R4A1A3S2eG1G3A2A3A2A2A2A2A2A2Lv;A2Lu;A2Lpos;A2Lc;A2F_;F_;Fs;Ff;FA;Fm;").
Proof.
  intros m A f s (Hlen & Hcls & _) Hin.
  unfold aa_frames in Hin. apply frames_of_in in Hin as (i & pos & Hi & Hb & Hs). rewrite Z.add_0_l in Hs.
  set (c := Z.of_nat i) in *.
  assert (Eb : fs_busy A c = nth i (aa_fs_busy A) []).
  { unfold fs_busy, nthZ. subst c. rewrite Nat2Z.id. reflexivity. }
  assert (Hc : 0 <= c < 11) by (subst c; rewrite Hlen in Hi; unfold FS_NCLASSES; lia).
  destruct (Hcls c Hc) as [Hnd Hpf].
  rewrite <- Eb in Hb. destruct (in_split _ _ Hb) as (u & v & E).
  exists c, pos, u, v. split; [exact Hc|]. split; [exact Hs|]. split; [exact E|]. split.
  { rewrite E, map_app in Hnd. cbn in Hnd. intros Hu. apply NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app. left. exact Hu. }
  destruct (Hpf (pos, f) Hb) as [Hr Hf]. cbn in Hr, Hf. split; [exact Hr|]. split; [exact Hf|].
  rewrite Eb. replace (Z.to_nat c) with i by lia. apply nth_error_nth'. exact Hi.
Qed.

Lemma aa_frames_disjoint : ltac2:(tb__ "0|2|
S16S83S5S5S5S5SbbR6R5A2S3cS2aS5S5A2M0S2dS5S5R5R4A4M1S9aR6A1A3S3cG0S2dS5S5R4R3A4S9aR7A1A3S2S1G0S2dS5S5R7R6A4G1A3S2S6S7R7R6A2R5A2S6S7R5R4A2R7A2A2A2F_;F_;F_;Fs2;Ff2;Fs1;Ff1;FA;Fm;").
Proof.
  intros m A f1 s1 f2 s2 HF H1 H2.
  destruct (aa_frames_fact m A f1 s1 HF H1) as (c1 & p1 & u1 & v1 & Hc1 & -> & E1 & _ & Hp1 & -> & _).
  destruct (aa_frames_fact m A f2 s2 HF H2) as (c2 & p2 & u2 & v2 & Hc2 & -> & E2 & _ & Hp2 & -> & _).
  destruct (Z.eq_dec c1 c2) as [Ec|Nc]; [destruct (Z.eq_dec p1 p2) as [Ep|Np]|].
  - left. subst. reflexivity.
  - right. apply fs_frames_disjoint; auto.
  - right. apply fs_frames_disjoint; auto.
Qed.

Definition sep_geom3 (G : ageom) : Prop := ltac2:(tb__ "0|c|
S0S2S6S7S82VG;A1M0Z1000M1A2M2S81VG;A1M3A2S6S7S7G3S4dA2G1A2M4G0A2A2S0S2S6S7S84VG;A1M5G1A2M6G3A2S6G4G5A2A2S0S2S6S7S85VG;A1M7G1A2M8G3A2S6G4G7A2A2S0S2S6S7S8aVG;A1M9S4fA2MaG3A2S6G4G9A2A2S0S2S6GaG0A2S6G2G9A2A2S0S2S6GaS7fVG;A1MbA2S6S7GbS47A2G9A2A2S0S2S6GaG5A2S6G6G9A2A2S2S6GaG7A2S6G8G9A2A2A2A2A2A2A2A2A2").

Definition q_foot (A : AA) (z : Z) : Prop := ltac2:(tb__ "0|5|
S40S7dS7dS2S0S6S95R1A1M0Vz;A2S8Vz;S7G0S5aA2A2A2S40S2aS5S5A2M1G1S2S0S6SaS32S5S5R1A3M2S54S33S5S5R1A3M3A1A2Vz;A2S8Vz;G2A2A2S0S6S48G2A1M4Vz;A2S8Vz;S7G4SeS7G3Z7A2Z8A2A2A2A2A2Lit;Sa4R1A1A3A2Lqb;S31S7dS90VA;A1S8fVA;A1A3A3").

Definition slot_zone (G : ageom) (c x : Z) (z : Z) : Prop := ltac2:(tb__ "0|2|
S7S53S81VG;A1Vc;A2ScZ10Vx;A2A2S5S2S0S6R1Vz;A2S8Vz;S7R1S56Vc;A1M0A2A2A2S0S6S48R1A1M1Vz;A2S8Vz;S7G1SeG0Z8A2A2A2A2A2Tab;").
Definition inv3 (A : AA) : Prop := ltac2:(tb__ "0|15|
S7eVA;A1S80S0SdfR1A1S0S5S5S3cS2aS5S5A2M0S2dS5S5R2R1A4S87VA;A1M1A3S2S1S2cS52R2A1S35A3S4S7cS7cS0S3cS7cR1S89VA;A1M2A3M3S0S1S5R4S7S7S8dR1A1S46A2Z800A2A3S1S5S9dR1A1S7S64R3Z8A2Z1000M4A2A3A2A2Lch;A2A2F_;Fn;Fb;S0S30S7cS1S2bS7cA1S3dS7cG2R2A3S2eS7cR1A2A3M5S0S2S6S7S8dR2A1M6S96R2A1M7A2M8S81R4A1M9A2S6S7S7G9S4dA2G4A2G6A2A2S0S2S6G8S82R4A1MaA2S6S7GaG4A2G6A2A2S0S2S6G8S8aR4A1MbA2S6S7GbS4fA2G6A2A2S0S2S6G8S7fR4A1McA2S6S7GcS47A2G6A2A2S0S30S7cG5S3S1S30R6R3A3A1S2S6S7S8dR6A1MdS96R6A1A2S8dR3A1MeA2S6S7GeS96R3A1A2GdA2A2F_;F_;Fch';Fj;S0S2S6G8S84R4A1MfA2S6S7GfG4A2G6A2A2S2S6G8S85R4A1M10A2S6S7G10G4A2G6A2A2A2A2A2A2A2A2F_;Fch;Fi;S0S5SdbVA;R1A2S0S3S0S6S82R3A1M11R2A2S8R2S7G11G4A2A2A2A1S5S5S0S6Z1M12R2A2S6R2Z1eA2A2S3cS5R2Sa2Sb5S86S8cVA;A1R3S8bA4A1A3S3Se1R7R4R3R6A4A1F_;F_;Fx;Fc;A2F_;Fz;S0G0S3cG0R1S109S8eVA;A1A1A3S0S57S88R3A1S32S5S5R2A3S33S5S5R2A3A3S0Se8R2S2dS5S5G11G4A4A2S0Se8R2S2dS5S5S84R3A1G4A4A2S0Se8R2S2dS5S5S85R3A1G4A4A2S0Se8R2S2dS5S5S7fR3A1S47A4A2S0Se8R2S2dS5S5S81R3A1S7S4dG4A2A4A2S0Se8R2S2dS5S5S8aR3A1S4fA4A2S7cG3Se8R4S2dS5S5G6G7A4A2F_;Fch;A2A2A2A2A2A2A2F_;Fbn;S0SfaS5S31S5Se5G0S5S32S5S5A2M13S3eG0G0S3bS52S33S5S5R1A3A1A1M14Lbn;G1A3A4Se5G0S5G13S3eG0G0G14Lit;SecSedVA;A1A1A3A4A3A2S0S6SbS2fS7cG2A2A1S7SacVA;A1ScaVA;A1A2A2S0S6SaeVA;A1S7Sa6G12A2A2S3S1S29S7dA1S31S7dS90VA;A1S8fVA;A1A3S38S7dA1A3A1S1S2cS93VA;A1S35A3F_;A2A2A2A2A2A2A2A2TG;").
Lemma inv3_fs_blind : ltac2:(tb__ "0|1|
S83S83Sc2R2R1A2Sc7R3A1M0G0F_;F_;FA';FA;").
Proof.
  intros A A' (Hg & Hc & Hci & Hs & Hp & Hl & Hqt & Hqg & Hd & Hii & HV & HKm & HKf) H.
  unfold inv3, q_foot, qlarge, large_live, small_live, qall in *. rewrite Hg, Hc, Hci, Hs, Hl, Hqt, Hqg, Hd. exact H.
Qed.

Definition in_maps (V : VmMaps) (lo hi : Z) : Prop := ltac2:(tb__ "0|4|
S4S2aS26Q40M0A1M1G1A2M2G2S0S3cG2R1SefVV;A1A3S0S6S28G0S32G1G1R1A3A2M3Vlo;A2S6Vhi;S7G3S28G0S33G1G1R1A3A2A2A2A2A2Le;A2").
Definition vm_geom (A : AA) (md : Model) : Prop := ltac2:(tb__ "0|f|
Sf1Vmd;A1Sf3S7eVA;A1S80S0S2aS26Q40M0A1M1G1A2M2S5S3cG2R2Sf2R4A1A3S0S6S28G0S32G1G1R3A3A2M3R2A2S8R2S7G3S28G0S33G1G1R3A3A2A2A2A2S4G2G2S0S3cG2R1SefR7A1A3S0S6S28G0S32G1G1R1A3A2M4R4A2S8R4S7G4S28G0S33G1G1R1A3A2A2A2A2A2Le';A2F_;F_;Fx;Fe;S0Sb4R2S81R1A1M5S7S7G5S4dA2Z1000M6A2A3S0Sb4R2S82R1A1M7S7G7G6A2A3S0Sb4R2S84R1A1M8S7G8G6A2A3S0Sb4R2S85R1A1M9S7G9G6A2A3S0Sb4R2S7fR1A1MaS7GaS47A2A3S0Sb4R2S8aR1A1MbS7GbS4fA2A3S0S7cS3cS7cR1S89VA;A1A3S3cG2S2dG1G1S27G0S8dR2A1A2S27G0S96R2A1A2A4SefR4A1A3F_;Fch;G1S1S5S9S28G0R1A2S46A2Z0McA3S2S0S6S5fS28G0R2A2MdA2S6S7GdS46A2MeS60A2A2S0S6S5dGdA2S6GeS50A2A2A2S0S1S2cSf6R3Sf5Vmd;A1A2S35A3S5S0S6GcR1A2S8R1S46A2A2S1S2cS102Sf2R7A1S7S28G0R5A2R2A2A2S36A3F_;Fj;A2F_;F_;Fp;A2A2A2A2A2A2A2A2TG;TV;").

Definition ledger_inv (A : AA) (md : Model) (tp : list word) : Prop := ltac2:(tb__ "0|b|
Sf1Vmd;A1Sf3S0S1S29S2aS26Q40M0A1M1G1A2M2A1Sf8R1A1M3SfeVsegs;A1A3S0S101SefR1A1M4S100SffA3S0SebS31G2G3G4A3A1S0SeaVA;R1A2S0S10bS8eVA;A1M5Vmd;Vtp;A3S0S6SaaG5A1S7S7S92VA;A1M6S91VA;A1A2Z1A2A2S0S0S6Z0M7S94VA;A1M8A2S6G8S7ScZ8G6A2S65A2A2A2S0S0G1G1S3cG2S2dG1G1R2R1A4M9SefR3A1A3S8G7S28G0R2A2A2MaF_;Fs;Fb;S0Sb4R1S5fS60A3Sb4R1S5dS50A3A2A2S0S6SbS2fS7cS89VA;A1A2A1G6A2G1G1S3cG2G9Sf2R3A1A3GaF_;Fs;Fb;A2A2A2A2A2A2A2A2A2TV;").
Definition model_inv (A : AA) (tp : list word) (md : Model) : Prop := ltac2:(tb__ "0|2|
S0Se4VA;Vmd;A2S0S6S7S104Vmd;Vtp;A2S108VA;A1A2Se9VA;A1A2S0S1S5Sf7Sf1Vmd;A1M0A1S105A3S0S6Z0M1S97VA;A1A2S0S6G1S92VA;A1A2S0S6G1S91VA;A1A2S0S1S5Sf4G0A1S9cS7eVA;A1A1A3Sd4VA;Vmd;Vtp;A3A2A2A2A2A2A2A2").

Definition band_page (z : Z) : Prop := ltac2:(tb__ "0|1|
S2S0S6S5fVz;A2S6S7Vz;S46A2M0S60A2A2S0S6S5dVz;A2S6G0S50A2A2A2").
Definition bandtp_inv (m : bview) (tp : list word) : Prop := ltac2:(tb__ "0|3|
S26Q40M0A1M1S3cG1R1Vtp;A3Sc0S28G0R2A2A1S17Vm;S28G0R3A2M2S7G2S46A2A3F_;F_;Fp;").

Lemma band_page_band : ltac2:(tb__ "0|0|
S5Sc0R1A1S0S6S4aR2A2S6S7R2S46A2S49A2A2F_;Fz;").
Proof. intros z Hz. unfold band_page, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG in *. lia. Qed.
Lemma bandtp_mono : ltac2:(tb__ "0|3|
S16S16S29S26Q40A1A1S5S0S6S4aR1A2S8R1S49A2A2S3S1S2bS26Q8A1M0A1M1R5R2A1S39G0A1M2A3A1S3S1G1R5R3A1G2A3A1F_;F_;Fz;Sb1R4R2A2Sb1R4R3A2F_;F_;Ftp;Fm';Fm;").
Proof.
  intros m m' tp Hm HB p Hp Hb z Hz. pose proof (band_page_band _ Hb) as R.
  destruct (HB p Hp Hb z Hz) as [b Hbz]. destruct (m' z) as [b'|] eqn:E; [exists b'; reflexivity|].
  exfalso. apply (Hm z ltac:(lia) ltac:(rewrite Hbz; discriminate)). exact E.
Qed.
Lemma bandtp_agree : ltac2:(tb__ "0|0|
S16S16S29S26Q40A1A1S5S0S6S4aR1A2S8R1S49A2A2S1S2bS26Q8A1A1R4R2A1R5R2A1A3F_;Fz;Sb1R4R2A2Sb1R4R3A2F_;F_;Ftp;Fm';Fm;").
Proof. intros m m' tp Hm HB. eapply bandtp_mono; [|exact HB]. intros z Hz H. rewrite (Hm z Hz). exact H. Qed.
Lemma bandtp_nil : ltac2:(tb__ "0|0|
S16Sb1R1S38S26Q40A1A1A2Fm;").
Proof. intros m p []. Qed.

Lemma view_def_mono : ltac2:(tb__ "0|5|
Sb0Sb0S5S3S1S2bS26Q8A1M0A1M1SafR3S27Q40M2R1A2A2S39G0A1M3A3A1S3S1G1SafR3S27G2R2A2A2G3A3A1F_;S3S1G1Vview;SafR4A1M4R2A2G3A3A1S3S1G1Vview;G4R3A2G3A3A1F_;F_;Fz;Frho';Frho;").
Proof.
  intros rho rho' z Hm Hv. unfold view in Hv |- *.
  destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|]; [|rewrite RtCells.view_out in Hv by lia; exfalso; exact (Hv eq_refl) | rewrite RtCells.view_out in Hv by lia; exfalso; exact (Hv eq_refl)].
  rewrite RtCells.view_in in Hv |- * by lia. unfold rd_of in Hv |- *.
  destruct (rm rho (Z_to_bv 64 z)) as [b|] eqn:E; destruct (rm rho' (Z_to_bv 64 z)) as [b'|] eqn:E'; try discriminate; [|exact Hv].
  exfalso. apply Hm; [discriminate | reflexivity].
Qed.
Lemma bandtp_mono_rm : ltac2:(tb__ "0|5|
Sb0Sb0S29S26Q40M0A1A1S5S0S6S4aR1A2S8R1S49A2A2S3S1S2bS26Q8A1M1A1M2SafR5S27G0R2A2A2S39G1A1M3A3A1S3S1G2SafR5S27G0R3A2A2G3A3A1F_;F_;Fa;Sb1Vview;SafR4A1A1M4R2A2Sb1G4R3A2F_;F_;Ftp;Frho';Frho;").
Proof. intros rho rho' tp Hm HB. eapply bandtp_mono; [|exact HB]. intros z Hz. apply view_def_mono. exact (Hm z Hz). Qed.
Lemma bandtp_agree_rm : ltac2:(tb__ "0|3|
Sb0Sb0S29S26Q40M0A1A1S5S0S6S4aR1A2S8R1S49A2A2S1S2bS26Q8A1A1SafR4S27G0R2A2M1A2SafR5G1A2A3F_;Fa;Sb1Vview;SafR4A1A1M2R2A2Sb1G2R3A2F_;F_;Ftp;Frho';Frho;").
Proof. intros rho rho' tp Hm HB. eapply bandtp_mono_rm; [|exact HB]. intros a Ha H. rewrite (Hm a Ha). exact H. Qed.

Lemma bandtp_grow : ltac2:(tb__ "0|4|
S16S29S26Q40M0A1M1A1M2G2Sb1R3R2A2G1S3cG1R1R3A3S2S3cG1R2R5A3Sc0S28G0R2A2A1S17R7S28G0R3A2M3S7G3S46A2A3F_;A2F_;Fp;Sb1R5R3A2F_;F_;Ftp';Ftp;Fm;").
Proof. intros m tp tp' HB Hn p Hp Hb. destruct (Hn p Hp) as [H|H]; [exact (HB p H Hb) | exact (H Hb)]. Qed.

Definition AInvA (A : AA) (rho : valuation) (tp : list word) (md : Model) : Prop := ltac2:(tb__ "0|1|
Vview;SafVrho;A1A1S16S7eVA;A1S80S0Sb3R1A1S0S25R2R1A2S0SbbS1fSb7R1A1M0R2A2VA;A2S0Sc1S22G0R2A2VA;A2S0Sd9VA;Vtp;Vmd;A3S0Sc7VA;A1Sb1R2Vtp;A2A2A2A2A2A2A2TG;Tm;").

Lemma AInvA_mat : ltac2:(tb__ "0|0|
S83Sb0S29S26Q40A1A1Sf0Sf0Sb9R5R4R3R2A4S103Vsegs;R4R3R2A4Sb9R7R6R5R3A4F_;F_;Fmd';Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md md' (HG & HR & HF & HRest & HM & HI3 & HB) (Hex & Hpaid & _). unfold AInvA in *.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|]. split; [| exact (conj HI3 HB)].
  destruct Hex as (mat' & ->).
  assert (EV : m_vmmaps (with_vm_backing (m_vm_lazy md) mat' md) = m_vmmaps md) by apply m_vmmaps_with_vm_backing.
  assert (EL : m_vm_lazy (with_vm_backing (m_vm_lazy md) mat' md) = m_vm_lazy md) by apply m_vm_lazy_with_vm_backing.
  unfold model_inv, vm_geom, ledger_inv in HM |- *. rewrite EV, EL, Hpaid.
  destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  refine (conj V1 (conj V2 (conj V3 (conj V4 (conj V5 (conj V6 (conj V7 (conj L1 (conj L2 (conj L3 (conj L4 (conj _ (conj L6 (conj L7 (conj L8 L9))))))))))))))).
  eapply depot_vm_mat; [exact EV | exact EL | exact L5].
Qed.

Lemma fs_footb_false_intro : ltac2:(tb__ "0|3|
S80S5S2S8R1S7fR2A1M0A2S6S7G0Z58A2R1A2A2S2S8R2S7S7fR3A1M1S5cA2A2S6S7G1S47A2R2A2A2S2S8R3S48S7S7fR4A1M2S55A2A1A2S6S48S7G2S47A2A1R3A2A2S1S2cSb7R5R4A2S36A3F_;F_;F_;Fz;FG;").
Proof.
  intros G z H1 H2 H3. unfold fs_footb. cbn zeta.
  assert (E : forall a b, (z < a \/ b <= z) -> (a <=? z) && (z <? b) = false).
  { intros a b [H|H]; apply andb_false_iff; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
  rewrite (E _ _ H1), (E _ _ H2), (E _ _ H3). reflexivity.
Qed.

Lemma geom_nums : ltac2:(tb__ "0|8|
S80Sb3R1A1S0S6S4bS7fR2A1M0A2S0S6S7G0S47A2S88R2A1M1A2S0S1S5S9G0S46A2Z0M2A3S0S6Z1000M3S82R2A1M4A2S0S6S7G4G3A2G1A2S0S1S5S9G4S46A2G2A3S0S6G3S84R2A1M5A2S0S6S7G5G3A2G1A2S0S6G3S85R2A1M6A2S0S6S7G6G3A2G1A2S0S6S50S81R2A1M7A2S0S6S7S7G7S4dA2G3A2G1A2S0S1S5S9G7SdZ2Z10A2A2G2A3S0S6Z7fff7f800000G1A2S6G1Z7fffff800000A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2F_;FG;").
Proof.
  intros G HG. pose proof (topG_range G) as TG.
  destruct HG as (GF & _ & GT & GC & GD & GS1 & GS2 & GS3 & _).
  pose proof (dyn_ok_big _ _ _ GF ltac:(clear; rewrite FS_total_val; lia)) as F1.
  destruct GF as (F0 & _ & _ & F2 & _). destruct GT as (T0 & T1 & _ & T2 & _). destruct GC as (C1 & _ & C2 & _). destruct GD as (D1 & _ & D2 & _).
  repeat split; assumption || (clear - TG; lia).
Qed.

Lemma geom_bands : ltac2:(tb__ "0|8|
S80Sb3R1A1S0S2S6S7S7fR2A1M0S47A2S4aA2S6S49G0A2A2S0S2S6S7S82R2A1M1Z1000M2A2M3S4aA2S6S49G1A2A2S0S2S6S7S84R2A1M4G2A2M5S4aA2S6S49G4A2A2S0S2S6S7S85R2A1M6G2A2M7S4aA2S6S49G6A2A2S0S2S6G3S5eA2S6S4bG1A2A2S0S2S6G5S5eA2S6S4bG4A2A2S2S6G7S5eA2S6S4bG6A2A2A2A2A2A2A2A2F_;FG;").
Proof.
  intros G HG. destruct HG as ((_ & _ & _ & _ & _ & FB) & _ & (_ & _ & _ & _ & TI & TB) & (_ & _ & _ & CI & CB) & (_ & _ & _ & DI & DB) & _).
  repeat split; assumption.
Qed.
Lemma geom_seps : ltac2:(tb__ "0|a|
S80Sb3R1A1S0S2S6S7S7fR2A1M0S47A2M1S82R2A1M2A2S6S7G2Z1000M3A2M4G0A2A2S0S2S6G1S84R2A1M5A2S6S7G5G3A2M6G0A2A2S0S2S6G1S85R2A1M7A2S6S7G7G3A2M8G0A2A2S0S2S6G1S81R2A1M9A2S6S7S7G9S4dA2G3A2G0A2A2S0S2S6G4G5A2S6G6G2A2A2S0S2S6G4G7A2S6G8G2A2A2S2S6G6G7A2S6G8G5A2A2A2A2A2A2A2A2F_;FG;").
Proof.
  intros G HG. destruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3 & S4 & S5 & S6 & S7 & _).
  repeat split; assumption.
Qed.

Lemma geom_old : ltac2:(tb__ "0|10|
S80Sb3R1A1S0S1S5S9S7fR2A1M0S46A2Z0M1A3S0S6S4bG0A2S0S6S7G0S47A2M2S88R2A1M3A2S0S1S5Sa1R2A1Z6245b8A3S0S6Z1000M4S82R2A1M5A2S0S6S7G5G4A2M6G3A2S0S1S5S9G5S46A2G1A3S0S6G4S84R2A1M7A2S0S6S7G7G4A2M8G3A2S0S6G4S85R2A1M9A2S0S6S7G9G4A2MaG3A2S0S1S5S9S81R2A1MbSdZ2McZ10A2A2G1A3S0S6S50GbA2S0S6S7S7GbS4dA2G4A2MdG3A2S0S2S6G2G5A2S6G6G0A2A2S0S2S6G2G7A2S6G8G0A2A2S0S2S6G2G9A2S6GaG0A2A2S0S2S6G2GbA2S6GdG0A2A2S0S2S6G6G7A2S6G8G5A2A2S0S2S6G6G9A2S6GaG5A2A2S0S2S6G8G9A2S6GaG7A2A2S0S0S6G1S9fR2A1MeA2S8GeSa0R2A1MfA2A2S0S6GfSdGcZ2fA2A2S0S6Z7fff7f800000G3A2S6G3Z7fffff800000A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2F_;FG;").
Proof.
  intros G HG. pose proof (geom_nums G HG) as (F1 & F2 & F0 & T1 & T2 & T0 & C1 & C2 & D1 & D2 & S1 & S2 & S0 & TG).
  pose proof (geom_seps G HG) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  destruct HG as (_ & Htp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ST & ST3 & _).
  repeat split; try assumption; clear -ST ST3 TG; lia.
Qed.

Lemma Sh_in_band : ltac2:(tb__ "0|1|
S5S0S6Z0R1A2S8R1SdZ2Z2fA2A2A2S0S6S7S4aZ1000A2S48R2A1M0A2S8G0S49A2A2F_;Fa;").
Proof. intros a Ha. unfold Sh, SHADOW_OFF, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. split; [|apply Z.lt_le_trans with (2 ^ 44 + 2147450880); [|lia]]. all: pose proof (Z.div_le_mono 0 a 8); pose proof (Z.div_lt_upper_bound a 8 (2 ^ 44)); lia. Qed.

Lemma rtc_out_fs : ltac2:(tb__ "0|0|
S80Sb3R1A1S5S1S2cS20S23S1cR3A2R1A2S35A3S1S2cSb7R4R2A2S36A3F_;Fz;F_;FG;").
Proof.
  intros G HG z Hz.

  pose proof (geom_nums G HG) as (F1 & F2 & F0 & T1 & T2 & T0 & C1 & C2 & D1 & D2 & S1 & S2 & S0 & TG).
  rewrite FS_total_val, kSpaceSize_val in *. unfold IMG_HI, HIGH_SHADOW_END, PG in *.
  pose proof (Sh_in_band (ag_fsb G + FS_frames_off) ltac:(rewrite FS_frames_off_val; lia)) as SB1.
  pose proof (Sh_in_band (ag_fsb G + 11571200 - 1) ltac:(lia)) as SB2.
  assert (SM : Sh (ag_fsb G + FS_frames_off) <= Sh (ag_fsb G + 11571200)) by (apply Sh_mono; rewrite FS_frames_off_val; lia).
  assert (SU : Sh (ag_fsb G + 11571200) <= 17594333495296).
  { unfold Sh, SHADOW_OFF. pose proof (Z.div_le_upper_bound (ag_fsb G + 11571200) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  pose proof (geom_bands G HG) as (FB & TB & CB & DB & TI & CI & DI).
  pose proof (geom_seps G HG) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  rewrite FS_total_val, kSpaceSize_val in *.
  unfold HIGH_SHADOW_END, IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, PG in *.
  unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin).
  unfold in_cellb in Hin. apply andb_prop in Hin as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_kFlagsOffset_val;
  cbn [rtc_cells rtc_cells_img rtc_cells_geom app In c_addr c_w fs_log_cell fs_needs_gc_cell] in Hc;
  repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat fs_log_cell fs_needs_gc_cell] in Hlo, Hhi; cbn [Z.of_nat]; unfold fs_log_cell, fs_needs_gc_cell in Hlo, Hhi;
    first [ clear - Hlo Hhi F1 F2 TG SB1 SB2 SM SU FB; lia
          | clear - Hlo Hhi F1 F2 TG SB1 SB2 SM SU T1 T2 TB Q1; lia
          | clear - Hlo Hhi F1 F2 TG SB1 SB2 SM SU C1 C2 CB Q2; lia
          | clear - Hlo Hhi F1 F2 TG SB1 SB2 SM SU D1 D2 DB Q3; lia ] |]); try destruct Hc.
Qed.

Lemma AInvA_fs_update : ltac2:(tb__ "0|1|
S83S83Sb0Sb0S29S26Q40A1A1Sf0Sb9R6R4R2R1A4Sc2R7R6A2S5S1S2cSb7S7eR9A1M0R1A2S36A3S1S2bS26Q8A1A1Vview;SafR7A1R2A2Vview;SafR8A1R2A2A3F_;Fz;SbbS1fSb7G0A1Vview;SafR6A1A1A2R8A2Sb9R9R7R6R5A4F_;F_;F_;F_;Fmd;Ftp;Frho';Frho;FA';FA;").
Proof.
  intros A A' rho rho' tp md (HG & HR & HF & HRest & HM & HI3 & HB) Hs Hout HF'.
  pose proof (proj1 Hs) as EG. unfold AInvA. rewrite EG.
  split; [exact HG|]. split.
  { eapply cells_ok_frame; [|exact HR]. intros z Hz. apply Hout. apply rtc_out_fs; assumption. }
  split; [exact HF'|]. split.
  { rewrite (maskv_ext (fs_footb (aa_geom A)) (view (rm rho)) (view (rm rho')) Hout). eapply rest_inv_fs_blind; eauto. }
  split; [|split; [exact (inv3_fs_blind A A' Hs HI3)|]].
  2:{
      eapply bandtp_mono; [|exact HB]. intros z Hz Hm. destruct (fs_footb (aa_geom A) z) eqn:Efz; [|rewrite (Hout z Efz); exact Hm].
      pose proof (geom_bands _ HG) as (FB & _). destruct HF' as (_ & _ & _ & _ & _ & PSH). rewrite EG in PSH.
      assert (R : Sh (ag_fsb (aa_geom A) + FS_frames_off) <= z < Sh (ag_fsb (aa_geom A) + FS_total)).
      { unfold fs_footb in Efz. apply orb_prop in Efz as [Efz|Efz]; [apply orb_prop in Efz as [Efz|Efz]|];
          apply andb_prop in Efz as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2; [exfalso | exfalso | lia].
        all: rewrite FS_total_val in FB; rewrite ?FS_total_val, ?FS_kFlagsOffset_val in E2; rewrite ?FS_kFlagsOffset_val in E1; clear -FB E1 E2 Hz;
             unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; lia. }
      destruct (PSH z R) as [b Hb]. rewrite restrictv_in in Hb by exact Efz. rewrite Hb. discriminate. }
  unfold model_inv, budget_boundD, vm_geom, ledger_inv, gap_ok, gapN_ok, gapS_ok, blocks_left in *. destruct Hs as (EG' & EC & _ & ES & EP & _ & _ & _ & ED & _ & HV & HKm & HKf).
  rewrite (prim_credit_same A A' EC).
  rewrite HV, HKm, HKf, EG', ES, EP, ED. exact HM.
Qed.

Definition set_inited (A : AA) : AA := ltac2:(tb__ "0|0|
SadS7eVA;A1S8cVA;A1S93VA;A1S89VA;A1S94VA;A1S87VA;A1S90VA;A1S8fVA;A1S8eVA;A1S9eVA;A1S98VA;A1S35S97VA;A1S92VA;A1S91VA;A1Af").
Definition ia_zone (z : Z) : Prop := ltac2:(tb__ "0|0|
S2S0S6SbdVz;A2S8Vz;SbeA2A2S0S6Z180e88Vz;A2S8Vz;Z180e8cA2A2A2").

Lemma cell_ok_agree : ltac2:(tb__ "0|1|
S16S16S18S30SfcR1S1eR2A1A2S1S2bS26Q8A1A1R4S7S1dR3A1SbR2A1A2M0A1R5G0A1A3F_;Fk;S15R4R2A2S15R4R3A2F_;F_;Fc;Fm';Fm;").
Proof. intros m m' c Hag Hc k Hk. rewrite Hag by exact Hk. exact (Hc k Hk). Qed.
Lemma present_agree : ltac2:(tb__ "0|0|
S16S16S5S5S5S0S6R3R1A2S8R1R2A2A2S1S2bS26Q8A1A1R5R2A1R6R2A1A3F_;Fz;S17R5R3R2A3S17R5R4R3A3F_;F_;Fhi;Flo;Fm';Fm;").
Proof. intros m m' lo hi Hag Hp z Hz. rewrite Hag by exact Hz. exact (Hp z Hz). Qed.
Lemma filled_agree : ltac2:(tb__ "0|0|
S16S16S5S5S5S5S0S6R4R1A2S8R1R3A2A2S1S2bS26Q8A1A1R6R2A1R7R2A1A3F_;Fz;S1aR6R4R3R2A4S1aR6R5R4R3A4F_;F_;Fv;Fhi;Flo;Fm';Fm;").
Proof. intros m m' lo hi v Hag Hp z Hz. rewrite Hag by exact Hz. exact (Hp z Hz). Qed.

Definition agree_high (m m' : bview) : Prop := ltac2:(tb__ "0|0|
S5S6S6eR1A2S1S2bS26Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").

Lemma rtc_cells_img_lt : ltac2:(tb__ "0|2|
S80S18S3cS18R1S24S1cR2A2A3S0S2S6S7S1dR2A1M0SbS1eR2A1A1A2M1SbdA2S6SbeG0A2A2S2S6G1Z180e88A2S6Z180e8cG0A2A2A2F_;Fc;FG;").
Proof.
  intros G c Hc. unfold rtc_cells_img in Hc. unfold IA_BEG, IA_END.
  repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat]; lia|]). destruct Hc.
Qed.

End WithSegs.
