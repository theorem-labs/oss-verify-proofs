(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "acell"; "mkACell"; "bview"; "cells_ok"; "maskv"; "restrictv"; "RTC_A"; "c_addr"; "c_w"; "cells_footb"; "in_rangesZ"; "rtc_cells_img"; "G0"; "c_val"; "rt_musl_memcpy"; "rt_musl_memset"; "rtc_cells"; "rtc_cells_geom"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "option"; "None"; "Some"; "false"; "true"; "andb"; "nil"; "app"; "list"; "nat"; "pair"; "prod"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "leb"; "ltb"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "FS_LOG"; "IMG_LO"; "K_HIGH_MEM_END"; "PG"; "fs_log_cell"; "fs_needs_gc_cell"; "kMallocContextSize"; "kQuarantineCacheMax"; "kQuarantineMax"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "ag_ctx"; "ag_dtls"; "ag_fsb"; "ag_nodes0"; "ag_spacebeg"; "ag_ss0"; "ag_stack_bottom"; "ag_stack_top"; "ag_thread"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells.WithSegs"; "view"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "enc_bytes"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition in_rangesZ (l : list (Z * Z)) (a : Z) : Prop := ltac2:(tb__ "0|0|
S23S20S20S23S20S20S22S47S1fS20S20A2S1eS20S20R2R1A4Vl;A3S22S28R2Va;A2S29Va;S27R2R1A2A2A2A2Ln;A2Lb;A2").

Definition bview : Type := Z -> option byte.
Definition restrictv (P : Z -> bool) (m : bview) : bview := ltac2:(tb__ "0|1|
S20S13S14S25Q8A1M0A1L_;VP;R1A1Vm;R1A1S15G0A1X13x2Lz;").
Definition maskv (P : Z -> bool) (m : bview) : bview := ltac2:(tb__ "0|1|
S20S13S14S25Q8A1M0A1L_;VP;R1A1S15G0A1Vm;R1A1X13x2Lz;").

Lemma restrictv_ext : ltac2:(tb__ "0|2|
S20S13Fx;S20S14S25Q8A1A1M0Fx;M1G1S20S21S13R4R1A1S18A3S21G0R3R2A1R4R2A1A3F_;Fz;S21S2S5R4R2A2S5R4R3A2A3F_;Fm';Fm;FP;").
Proof. intros P m m' H. apply functional_extensionality. intros z. unfold restrictv. destruct (P z) eqn:E; [apply H; exact E | reflexivity]. Qed.
Lemma maskv_ext : ltac2:(tb__ "0|2|
S20S13Fx;S20S14S25Q8A1A1M0Fx;M1G1S20S21S13R4R1A1S17A3S21G0R3R2A1R4R2A1A3F_;Fz;S21S2S4R4R2A2S4R4R3A2A3F_;Fm';Fm;FP;").
Proof. intros P m m' H. apply functional_extensionality. intros z. unfold maskv. destruct (P z) eqn:E; [reflexivity | apply H; exact E]. Qed.
Lemma restrictv_in : ltac2:(tb__ "0|0|
S20S13Fx;S2S20S21S13R3R1A1S18A3S21S14S25Q8A1A1S5R4R3R2A3R3R2A1A3F_;Fz;Fm;FP;").
Proof. intros P m z H. unfold restrictv. rewrite H. reflexivity. Qed.
Lemma maskv_out : ltac2:(tb__ "0|0|
S20S13Fx;S2S20S21S13R3R1A1S17A3S21S14S25Q8A1A1S4R4R3R2A3R3R2A1A3F_;Fz;Fm;FP;").
Proof. intros P m z H. unfold maskv. rewrite H. reflexivity. Qed.

Record acell := mkACell { c_addr : Z; c_w : nat; c_val : Z }.
Definition cell_ok (m : bview) (c : acell) : Prop := ltac2:(tb__ "0|3|
S1dS44R1S8Vc;A1M0A2S21S14S25Q8M1A1M2A1Vm;S27S7Vc;A1S2dR2A1A2A1S16G2S45G2R2S46G0S26Q40SdVc;A1A2A2S26G1Z0A2A4A2A3F_;Fk;").
Definition cells_ok (m : bview) (cs : list acell) : Prop := Forall (cell_ok m) cs.

Definition present (m : bview) (lo hi : Z) : Prop := ltac2:(tb__ "0|1|
S20S22S28Vlo;R1A2S29R1Vhi;A2A2S23S25Q8A1M0G0S21S14G0A1Vm;R3A1S16G0R1A2A3Lb;A2F_;Fz;").
Definition filled (m : bview) (lo hi : Z) (b : Z) : Prop := ltac2:(tb__ "0|2|
S20S22S28Vlo;R1A2S29R1Vhi;A2A2S21S14S25Q8M0A1M1A1Vm;R2A1S16G1S26G0Vb;A2A2A3F_;Fz;").

Definition in_cellb (z : Z) (c : acell) : bool := ltac2:(tb__ "0|1|
S19S2bS7Vc;A1M0Vz;A2S2cVz;S27G0S2dS8Vc;A1A1A2A2A2").
Definition cells_footb (cs : list acell) (z : Z) : bool := existsb (in_cellb z) cs.

Lemma cells_ok_frame : ltac2:(tb__ "0|2|
S1cS0A1S20S14S25Q8A1A1M0Fx;M1G1S20S21S13S9R4R1A2S18A3S21G0R3R2A1R4R2A1A3F_;Fz;S3R3R4A2S3R3R5A2F_;F_;Fm';Fm;Fcs;").
Proof.
  intros cs m m' Hm H. unfold cells_ok in *. apply Forall_forall. intros c Hc k Hk.
  rewrite Hm; [exact (proj1 (Forall_forall _ _) H c Hc k Hk)|].
  unfold cells_footb. apply existsb_exists. exists c. split; [exact Hc|]. unfold in_cellb. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition view (m : word -> option byte) : bview := ltac2:(tb__ "0|1|
S20S13S14S25Q8A1M0A1L_;S19S2bZ0R1A2S2cR1S2aZ2Z40A2A2A2S2eVsegs;Vm;S26Q40R1A2A3S15G0A1X13x2Lz;").
Lemma view_in : ltac2:(tb__ "0|2|
S25Q40M0A1S14S25Q8A1A1M1F_;S20S22S28Z0R1A2S29R1S2aZ2Z40A2A2A2S21G1S43R3R2A2S2eVsegs;R3S26G0R2A2A3A3F_;Fz;Fm;").
Proof.
  intros m z Hz. unfold view. replace ((0 <=? z) && (z <? 2 ^ 64))%bool with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma view_out : ltac2:(tb__ "0|2|
S25Q40A1S14S25Q8A1M0A1M1F_;S20S24S22S28Z0R1A2S29R1S2aZ2Z40A2A2A2A1S21G1S43R3R2A2S15G0A1A3F_;Fz;Fm;").
Proof.
  intros m z Hz. unfold view. destruct (Z.leb_spec 0 z); destruct (Z.ltb_spec z (2 ^ 64)); cbn; try reflexivity. lia.
Qed.
End WithSegs.

Record rtconsts := RTC {
  rt_asan_inited : Z;
  rt_malloc_ctx_size : Z;
  rt_shadow_base_var : Z;
  rt_detect_uar : Z;
  rt_page_size_cache : Z;
  rt_real_memset : Z;
  rt_real_memcpy : Z;
  rt_musl_memset : Z; rt_musl_memcpy : Z;
  rt_dying : Z;
  rt_may_return_null : Z;
  rt_rss_exceeded : Z;
  rt_instance : Z;
  rt_quarantine : Z;
  rt_tsd_key_inited : Z; rt_tsd_key : Z;
  rt_internal_inited : Z;
  rt_common_flags : Z; rt_asan_flags : Z
}.
Definition RTC_A : rtconsts :=
  RTC 0xeed98 0xeedb8 0xee0b8 0xee0c0 0x17db60 0xe6780 0xe6778 0xdb004 0xdac00 0x17fbdc 0x170321 0x170322
      0xeaa58 0xead30 0xed920 0xed924 0x1702f0 0x17fbe8 0xeb8b8.

Definition ERRNO_A : Z := 0x6211d4.

Definition rtc_cells_img (R : rtconsts) (G : ageom) : list acell := ltac2:(tb__ "0|8|
S12S0S1Ze66b0U8M0Zdb7f4A3S12S0S1Ze6778G0SeVR;A1A3S12S0S1Ze6780G0SfVR;A1A3S12S0S1Zeaa78G0S3eVG;A1M1A3S12S0S1Zeaa80U4M2ZffffffffA3S12S0S1Zeaa88G0S27G1S39A2A3S12S0S1Zeaa90U1M3Z0M4A3S12S0S1Zead70G0S38A3S12S0S1Zead80G0S37A3S12S0S1Zeb878G0S2aZ2Z28A2A3S12S0S1Zeb880U2M5Z10A3S12S0S1Zeb882G5Z800A3S12S0S1Zeb8e4G2Z1000A3S12S0S1Zeb8e8G2G4A3S12S0S1Zeb8ecG2ZbeA3S12S0S1Zed91cG3Z1M6A3S12S0S1Zed920G3G6A3S12S0S1Zed924G2G4A3S12S0S1Zeed98G3G6A3S12S0S1Zeed99G3G6A3S12S0S1Zeeda0G0S32A3S12S0S1Zeeda8G0G4A3S12S0S1Zeedb0G0G4A3S12S0S1ZeedbcG2S36A3S12S0S1Z170322G3G4A3S12S0S1Z17db58G2G4A3S12S0S1Z17db60G0S33A3S12S0S1Z17fb80G0G4A3S12S0S1Z17fb88G0G4A3S12S0S1Z17fc0aG3G6A3S12S0S1Z17fc60G0ZffffffffffffffffA3S12S0S1Z17fc71G3G6A3S12S0S1Z17fc78G0G4A3S12S0S1Z17fcecG3G4A3S12S0S1Z1bff98G0S3fVG;A1A3S12S0S1Z5cffa8G0S3dVG;A1A3S12S0S1Z621220G0Z642620M7A3S12S0S1Z621270G0Z621298A3S12S0S1Z621278G0S3cVG;A1A3S12S0S1Z621280G0S3bVG;A1A3S12S0S1Z621288G2G4A3S12S0S1Z6212a0G0Z621a78A3S12S0S1G7G0S3aVG;A1A3S1aS0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition rtc_cells_geom (G : ageom) : list acell := ltac2:(tb__ "0|7|
S12S0S1S27S3aVG;A1M0Z98A2U8M1S42VG;A1M2A3S12S0S1S27G0Z8M3A2U4Z0M4A3S12S0S1S27G2G4A2G1G0A3S12S0S1S27G2G3A2G1S41VG;A1A3S12S0S1S27G2Z10A2G1S40VG;A1A3S12S0S1S27G2Z28A2U1M5G4A3S12S0S1S27G2Z30A2G1Z6219b0A3S12S0S1S27G2Z38A2G1Z621a8cA3S12S0S1S27G2Z48A2G1S3cVG;A1M6A3S12S0S1S27S3bVG;A1Z18A2G1Z621278A3S12S0S1S34G6A1G1S30A3S12S0S1S35G6A1G5G4A3S1aS0A1A3A3A3A3A3A3A3A3A3A3A3A3").

Definition rtc_cells (R : rtconsts) (G : ageom) : list acell := ltac2:(tb__ "0|0|
S1bS0SbVR;VG;A2S11VG;A1A3").

Definition rtc_inv (m : bview) (G : ageom) : Prop := ltac2:(tb__ "0|0|
S3Vm;S10S6VG;A2A2").

Definition G0 : ageom := mkAG 0 0 0 0 0 0 0 0 0 0 0 0 0.

Definition cst_ok (CST : list (Z * Z)) : Prop := ltac2:(tb__ "0|0|
S20SaVCST;R1A2S22S22S28S31R2A2S29R2S2fA2A2S21S13S9SbS6ScA2R2A2S17A3A2F_;Fa;").

Definition xgl_ok (XGL : list (Z * Z)) : Prop := ltac2:(tb__ "0|0|
S20SaVXGL;R1A2S22S28Z0R2A2S29R2S2fA2A2F_;Fa;").
