(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "leb"; "sub"; "div"; "shiftl"; "lt"; "modulo"; "eqb"; "ltb"; "max"; "shiftr"; "to_nat"; "log2"; "min"; "of_nat"; "pow"; "@Corelib.Init.Datatypes"; "bool"; "andb"; "true"; "false"; "nat"; "negb"; "orb"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "fs_frame_size"; "needed"; "ClassID"; "FS_LOG"; "dyn_in"; "is_primary"; "FS_frames_off"; "IMG_HI"; "Sh"; "kMidClass"; "kMinSize"; "region_beg"; "FS_kFlagsOffset"; "SHADOW_BAND_HI"; "cost_ok"; "forall_range"; "fs_pos"; "kCompactPtrScale"; "kMidSize"; "round_up"; "rz"; "slot"; "ALPHA_milli"; "BETA_M"; "DEPOT_PER_PUT"; "HIGH_SHADOW_END"; "IMG_LO"; "K_HIGH_MEM_END"; "LOW_SHADOW_BEG"; "SHADOW_BAND_LO"; "Size"; "cost_m_milli"; "dyn_ok"; "forall_rangeZ"; "fs_class_of_size"; "fs_flags"; "fs_flags_off_nat"; "fs_frame"; "kChunkHeader2Size"; "kDepotNodeSize"; "kMallocContextSize"; "kMaxBytesCached"; "kMaxNumCachedHint"; "kRegionInfoStride"; "kRegionSize"; "kSpaceSize"; "kUserSpaceSize"; "page_up"; "sec_map_size"; "slot_ok"; "spage_hi"; "spage_lo"; "top_clamp"; "@Stdlib.Bool.Bool"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Local Open Scope Z_scope.

Definition PG : Z := 4096.
Definition SHADOW_OFF : Z := 0x7fff8000.
Definition LOW_SHADOW_BEG : Z := 0x7fff7000.
Definition SHADOW_GAP_BEG : Z := 0x8fff7000.
Definition HIGH_SHADOW_BEG : Z := 0x2008fff7000.
Definition HIGH_SHADOW_END : Z := 0x10007fff8000.
Definition K_HIGH_MEM_END : Z := 2 ^ 47 - 1.

Notation atop_lo := 140735332483072%Z (only parsing).
Notation atop_hi := 140737479966720%Z (only parsing).
Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0x646000.
Definition SHADOW_BAND_LO : Z := LOW_SHADOW_BEG.
Definition SHADOW_BAND_HI : Z := HIGH_SHADOW_END.

Definition top_clamp (t : Z) : Z := Z.max 140735332483072 (Z.min t 140737479966720).
Lemma top_clamp_range : forall t, 140735332483072 <= top_clamp t <= 140737479966720.
Proof. intros t. unfold top_clamp. lia. Qed.
Lemma top_clamp_id : ltac2:(tb__ "0|0|
S0S1bS2Z7fff7f800000R1A2S2R1Z7fffff800000A2A2S1aS0S53R2A1R2A3F_;Ft;").
Proof. intros t Ht. unfold top_clamp. lia. Qed.

Definition dyn_in (top a len : Z) : Prop := ltac2:(tb__ "0|1|
S1bS2Z1000Va;A2S1bS8Z0Vlen;A2S1bS2S1Va;Vlen;A2M0Vtop;A2S1bS1cS2G0S39A2S2S26Va;A2A2S1cS2G0S3cA2S2S2cVa;A2A2A2A2A2A2").

Definition dyn_ok (top a len : Z) : Prop := ltac2:(tb__ "0|0|
S1bS1aS0S9Va;S1eA2Z0A3S23Vtop;Va;Vlen;A3A2").
Lemma dyn_in_big : ltac2:(tb__ "0|0|
S0S0S0S23R3R2R1A3S8Zf000R2A2S2S26R4A2F_;F_;Flen;Fa;Ftop;").
Proof. intros top a len (H1 & _ & _ & H4 & _) Hl. unfold IMG_LO, IMG_HI in *. lia. Qed.
Lemma dyn_ok_big : ltac2:(tb__ "0|0|
S0S0S0S3fR3R2R1A3S8Zf000R2A2S2S26R4A2F_;F_;Flen;Fa;Ftop;").
Proof. intros top a len [_ H] Hl. exact (dyn_in_big top a len H Hl). Qed.
Lemma dyn_in_huge : ltac2:(tb__ "0|0|
S0S0S0S23R3R2R1A3S2R4Z7fffff800000A2S2S12Z2Z1fA2R3A2S2S2cR5A2F_;F_;F_;Flen;Fa;Ftop;").
Proof. intros top a len (H1 & _ & H3 & H4 & H5) Ht Hl. unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia. Qed.
Lemma dyn_in_sub : ltac2:(tb__ "0|0|
S0S0S0S0S0S23R5R4R3A3S2R5R3A2S8Z0R3A2S2S1R5R4A2S1R7R6A2A2S23R9R6R5A3F_;F_;F_;F_;Flen';Fa';Flen;Fa;Ftop;").
Proof. intros top a len a' len' (H1 & H2 & H3 & H4 & H5) Ha Hl Hs. unfold dyn_in. repeat split; lia. Qed.

Definition Sh (a : Z) : Z := a / 8 + SHADOW_OFF.
Definition page_dn (z : Z) : Z := ltac2:(tb__ "0|0|
S3S6Vz;S1eA2S1eA2").
Definition page_up (z : Z) : Z := ltac2:(tb__ "0|0|
S3S6S5S1Vz;S1eA2Z1A2S1eA2S1eA2").
Definition round_up (z m : Z) : Z := ltac2:(tb__ "0|0|
S3S6S5S1Vz;Vm;A2Z1A2Vm;A2Vm;A2").
Definition round_dn (z m : Z) : Z := ltac2:(tb__ "0|0|
S3S6Vz;Vm;A2Vm;A2").

Definition spage_lo (lo : Z) : Z := page_dn (Sh lo).
Definition spage_hi (hi : Z) : Z := ltac2:(tb__ "0|1|
S4eS1S27S5Vhi;Z1M0A2A1G0A2A1").
Definition n_spages (lo hi : Z) : Z := ltac2:(tb__ "0|0|
S6S5S51Vhi;A1S52Vlo;A1A2S1eA2").

Lemma Sh_mono : ltac2:(tb__ "0|0|
S0S0S2R2R1A2S2S27R3A1S27R2A1A2F_;Fb;Fa;").
Proof. intros. unfold Sh. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

Definition addr_is_in_mem (a : Z) : bool := ltac2:(tb__ "0|0|
S19S14S4Z0Va;A2SbVa;S3bA2A2S14S4S38Va;A2S4Va;S3aA2A2A2").

Definition kMinSize : Z := 32.
Definition kMidSize : Z := 512.
Definition kMidClass : Z := 16.
Definition kMaxSize : Z := 65536.
Definition kNumClasses : Z := 31.
Definition kNumClassesRounded : Z := 32.
Definition kMaxNumCachedHint : Z := 8.
Definition kMaxBytesCached : Z := 1024.

Definition Size (c : Z) : Z := ltac2:(tb__ "0|2|
S13S0L_;S4Vc;S28A2S3S29Vc;A2S7S31S6S5Vc;S28A2M0Z2M1A2A2S0S1R1S3S6R1G1A2S9G0G1A2A2A2Tt;X13x2").

Definition ClassID (s : Z) : Z := ltac2:(tb__ "0|4|
S13S0L_;M0S4Vs;S31A2S6S5S1Vs;S29A2Z1M1A2S29A2SfVs;A1S0S9SdVs;S5R1G1A2A2Z2M2A2S0S9Vs;S7G1S5R2G1A2A2A2S0S1S1S1S28S3S5R3Z9A2G2A2A2R2A2G0SbZ0M3R1A2G1G3X13x2A2Tlbits;Thbits;Tl;X13x2").

Definition MaxCachedHint (sz : Z) : Z := ltac2:(tb__ "0|0|
S10S49ScZ1S6S48Vsz;A2A2A2").
Definition max_count (c : Z) : Z := 2 * MaxCachedHint (Size c).

Definition rz_log (n : Z) : Z := ltac2:(tb__ "0|1|
S13S0L_;M0S4Vn;Z30A2Z0G0S4Vn;Z60A2Z1G0S4Vn;Z1c0A2Z2G0S4Vn;Zf80A2Z3G0S4Vn;Z3f00A2Z4G0S4Vn;Z7e00A2Z5G0S4Vn;Zfc00A2Z6Z7X13x2X13x2X13x2X13x2X13x2X13x2X13x2").
Definition rz (n : Z) : Z := Z.shiftl 16 (rz_log n).
Definition kChunkHeaderSize : Z := 16.
Definition kChunkHeader2Size : Z := 16.

Definition needed (n : Z) : Z := ltac2:(tb__ "0|0|
S1S32ScVn;S45A2Z8A2S33Vn;A1A2").
Definition is_primary (n : Z) : bool := needed n <=? kMaxSize.

Definition slot (n : Z) : Z := ltac2:(tb__ "0|0|
S3dS21S20Vn;A1A1A1").

Definition sec_map_size (n : Z) : Z := ltac2:(tb__ "0|0|
S1S32S20Vn;A1S1eA2S1eA2").
Definition sec_user_off (n : Z) : Z := PG + rz n.

Example ex_c100 : ClassID (needed 100) = 6 /\ Size 6 = 192. Proof. split; reflexivity. Qed.
Example ex_c64 : ClassID (needed 64) = 3 /\ Size 3 = 96. Proof. split; reflexivity. Qed.
Example ex_batch : ClassID 8192 = 24 /\ Size 24 = 8192. Proof. split; reflexivity. Qed.
Example ex_sec65536 : is_primary 65536 = false /\ sec_map_size 65536 = 0x12000 /\ sec_user_off 65536 = 0x1800.
Proof. repeat split; reflexivity. Qed.
Example ex_sec131072 : sec_map_size 131072 = 139264. Proof. reflexivity. Qed.
Example ex_sizes : map Size [1;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30]
  = [32;512;768;1024;1536;2048;3072;4096;6144;8192;12288;16384;24576;32768;49152;65536].
Proof. reflexivity. Qed.
Example ex_maxcount : map max_count [1;4;5;6;7;8;9;11;16;17;30] = [16;16;12;10;8;8;6;4;4;2;2].
Proof. reflexivity. Qed.

Fixpoint forall_range (f : Z -> bool) (lo : Z) (n : nat) : bool :=
  match n with O => true | S n' => f lo && forall_range f (lo + 1) n' end.
Lemma forall_range_ok : ltac2:(tb__ "0|0|
S0S13F_;S0S17S0S1aS13S2eR4R3R2A3S15A3S1bS2R4R2A2S8R2S1R4S11R3A1A2A2A2S1aS13R6R3A1S15A3F_;F_;Fz;Fn;Flo;Ff;").
Proof.
  intros f lo n. revert lo. induction n as [|n IH]; intros lo z H Hz; [lia|].
  cbn in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec z lo) as [->|Hne]; [exact H1|]. apply (IH (lo+1)); [exact H2|lia].
Qed.
Definition forall_rangeZ (f : Z -> bool) (lo len : Z) : bool := ltac2:(tb__ "0|0|
S2eVf;Vlo;SeVlen;A1A3").
Lemma forall_rangeZ_ok : ltac2:(tb__ "0|0|
S0S13F_;S0S0S0S1aS13S40R4R3R2A3S15A3S1bS2R4R2A2S8R2S1R4R3A2A2A2S1aS13R6R3A1S15A3F_;F_;Fz;Flen;Flo;Ff;").
Proof.
  intros f lo len z H Hz. apply (forall_range_ok f lo (Z.to_nat len)); [exact H|]. rewrite Z2Nat.id; lia.
Qed.

Definition slot_ok (n : Z) : bool := ltac2:(tb__ "0|3|
S14S14S14S14S24Vn;A1S4S20Vn;A1M0S34Vn;A1M1A2A2SaS9G1Z10A2Z0A2A2S4Z1S21G0A1M2A2A2S4G2Z1eA2A2").
Lemma slot_ok_all : ltac2:(tb__ "0|0|
S0S1bS2Z1R1A2S2R1Zfc00A2A2S1aS13S50R2A1S15A3F_;Fn;").
Proof.
  intros n Hn. apply (forall_rangeZ_ok slot_ok 1 64512); [|lia].
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma rz_large : ltac2:(tb__ "0|0|
S0S2Zfc01R1A2S1aS0S33R2A1Z800A3F_;Fn;").
Proof.
  intros n Hn. unfold rz, rz_log.
  repeat match goal with |- context [?a <=? ?b] => destruct (Z.leb_spec a b); try lia end. reflexivity.
Qed.
Lemma not_primary_large : ltac2:(tb__ "0|0|
S0S2Zfc01R1A2S1aS13S24R2A1S16A3F_;Fn;").
Proof.
  intros n Hn. unfold is_primary, needed. rewrite (rz_large n Hn). apply Z.leb_gt.
  unfold round_up, kMaxSize, kChunkHeader2Size.
  pose proof (Z.div_mod (Z.max n 16 + 8 - 1) 8) as Hd. pose proof (Z.mod_pos_bound (Z.max n 16 + 8 - 1) 8) as Hm. lia.
Qed.
Lemma primary_small : ltac2:(tb__ "0|0|
S0S1bS2Z1R1A2S2R1Zfc00A2A2S1aS13S24R2A1S15A3F_;Fn;").
Proof.
  intros n Hn. pose proof (slot_ok_all n Hn) as H. unfold slot_ok in H.
  repeat (apply andb_prop in H as [H ?]). exact H.
Qed.

Definition kSpaceSize : Z := 2 ^ 37.
Definition kRegionSize : Z := 2 ^ 32.
Definition kFreeArraySize : Z := 2 ^ 29.
Definition kUserSpaceSize : Z := kRegionSize - kFreeArraySize.
Definition kUserMapSize : Z := 2 ^ 18.
Definition kFreeArrayMapSize : Z := 2 ^ 18.
Definition kRegionInfoStride : Z := 128.
Definition kCompactPtrScale : Z := 4.

Definition region_beg (spacebeg c : Z) : Z := ltac2:(tb__ "0|0|
S1Vspacebeg;S3Vc;S4bA2A2").
Definition free_array (spacebeg c : Z) : Z := ltac2:(tb__ "0|0|
S1S2aVspacebeg;Vc;A2S4dA2").
Definition region_info (spacebeg c : Z) : Z := ltac2:(tb__ "0|0|
S1S1Vspacebeg;S4cA2S3Vc;S4aA2A2").
Definition compact_to_ptr (spacebeg c : Z) (x : Z) : Z := ltac2:(tb__ "0|0|
S1S2aVspacebeg;Vc;A2S7Vx;S30A2A2").
Definition ptr_to_compact (spacebeg c : Z) (p : Z) : Z := ltac2:(tb__ "0|0|
SdS5Vp;S2aVspacebeg;Vc;A2A2S30A2").

Definition RI_mutex : Z := 0. Definition RI_num_freed : Z := 16. Definition RI_mapped_free_array : Z := 24.
Definition RI_allocated_user : Z := 32. Definition RI_allocated_meta : Z := 40. Definition RI_mapped_user : Z := 48.
Definition RI_mapped_meta : Z := 56. Definition RI_exhausted : Z := 68.

Definition kQuarantineMax : Z := 2 ^ 28.
Definition kQuarantineMin : Z := 0x0e666661.
Definition kQuarantineCacheMax : Z := 2 ^ 20.
Definition kQuarantineBatchSize : Z := 8192.
Definition kQuarantineBatchCount : Z := 1021.
Definition kMallocContextSize : Z := 30.
Definition kDepotNodeSize : Z := 16.
Definition kDepotNodesBlock : Z := 2 ^ 20.
Definition kStackStoreBlock : Z := 2 ^ 23.
Definition kPtrArrayCommit : Z := 2 ^ 17.
Definition kPtrArrayReserve : Z := 2 ^ 23.

Definition FS_LOG : Z := 20.
Definition FS_kFlagsOffset : Z := 4096.
Definition FS_frames_off : Z := ltac2:(tb__ "0|1|
S1S2bS7Z1M0S5S1S22G0A2Z6A2A2A2").
Definition FS_total : Z := ltac2:(tb__ "0|0|
S1S25S3ZbS7Z1S22A2A2A2").
Definition fs_num_iter (c : Z) : Z := ltac2:(tb__ "0|0|
S7Z1S5S5S22Z6A2Vc;A2A2").
Definition fs_frame_size (c : Z) : Z := Z.shiftl 64 c.
Fixpoint fs_flags_off_nat (c : nat) : Z := match c with O => 0 | S c' => fs_flags_off_nat c' + fs_num_iter (Z.of_nat c') end.
Definition fs_flags (fsb c : Z) : Z := ltac2:(tb__ "0|0|
S1S1Vfsb;S2bA2S43SeVc;A1A1A2").
Definition fs_frame (fsb c pos : Z) : Z := ltac2:(tb__ "0|0|
S1S1S1Vfsb;S25A2S3Vc;S7Z1S22A2A2A2S3Vpos;S1fVc;A1A2A2").
Definition fs_hint_cell (fsb c : Z) : Z := fsb + 8 * c.
Definition fs_log_cell (fsb : Z) : Z := fsb + 88.
Definition fs_needs_gc_cell (fsb : Z) : Z := fsb + 96.
Definition fs_flagptr_cell (ff c : Z) : Z := ltac2:(tb__ "0|0|
S5S1Vff;S1fVc;A1A2Z8A2").
Definition fs_realstack_cell (ff : Z) : Z := ff + 24.

Definition fs_pos (fsb c f : Z) : Z := ltac2:(tb__ "0|0|
S6S5Vf;S1S1Vfsb;S25A2S3Vc;S7Z1S22A2A2A2A2S1fVc;A1A2").
Definition fs_flag_addr (fsb c f : Z) : Z := ltac2:(tb__ "0|0|
S1S42Vfsb;Vc;A2S2fVfsb;Vc;Vf;A3A2").

Definition fs_class_of_size (s : Z) : Z := Z.log2 (s / 64).
Lemma fs_class_of_size_ok : ltac2:(tb__ "0|0|
S0S2Z0R1A2S1aS0S41S1fR2A1A1R2A3F_;Fc;").
Proof.
  intros c Hc. unfold fs_class_of_size, fs_frame_size. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.mul_comm, Z.div_mul by lia. apply Z.log2_pow2. lia.
Qed.
Lemma fs_frame_size_pos : ltac2:(tb__ "0|0|
S0S2Z0R1A2S2Z40S1fR2A1A2F_;Fc;").
Proof. intros c Hc. unfold fs_frame_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 c). nia. Qed.
Lemma fs_frame_size_inj : ltac2:(tb__ "0|1|
S0S0S2Z0R2A2M0G0S1aS0S1fR4A1S1fR3A1A3S1aS0R5R4A3F_;F_;F_;Fc';Fc;").
Proof.
  intros c c' Hc Hc' E. rewrite <- (fs_class_of_size_ok c Hc), <- (fs_class_of_size_ok c' Hc'). rewrite E. reflexivity.
Qed.
Lemma fs_pos_frame : ltac2:(tb__ "0|0|
S0S0S0S2Z0R2A2S1aS0S2fR4R3S44R4R3R2A3A3R2A3F_;Fpos;Fc;Ffsb;").
Proof.
  intros fsb c pos Hc. unfold fs_pos, fs_frame. pose proof (fs_frame_size_pos c Hc).
  replace (fsb + FS_frames_off + c * Z.shiftl 1 FS_LOG + pos * fs_frame_size c - (fsb + FS_frames_off + c * Z.shiftl 1 FS_LOG))
    with (pos * fs_frame_size c) by lia.
  apply Z.div_mul. lia.
Qed.

Example ex_fs : FS_frames_off = 0x9000 /\ FS_total = 0xb09000 /\ map fs_num_iter [0;1;2;3;5;6] = [16384;8192;4096;2048;512;256]
  /\ map (fun c => fs_flags 0 c - 4096) [0;1;2;3;4;5;6] = [0; 0x4000; 0x6000; 0x7000; 0x7800; 0x7c00; 0x7e00].
Proof. repeat split; reflexivity. Qed.

Definition ALPHA_milli : Z := 1750.
Definition BETA_M : Z := 600.
Definition BETA_F : Z := 300.
Definition DEPOT_PER_PUT : Z := ltac2:(tb__ "0|0|
S1S46S3Z8S1S47Z1A2A2A2").

Definition cost_m_milli (n : Z) : Z := ltac2:(tb__ "0|3|
S13S0L_;S24Vn;A1S1S1S3Z465S34Vn;A1A2Z1194A2S3Z3e8M0S37A2M1A2S4fVn;A1S0S1S1S1S1S3G0R1A2S3G0S3S1eS1S6S5S1S6R1Z8A2S1eA2Z1M2A2S1eA2G2A2A2A2A2Z1f40A2G1A2S3Z7d0S1eA2A2Tm;X13x2").
Definition cost_ok (n : Z) : bool := ltac2:(tb__ "0|0|
S4S3eVn;A1S1S3S35Vn;A2S3Z3e8S36A2A2A2").
Lemma cost_ok_primary : ltac2:(tb__ "0|0|
S0S1bS2Z1R1A2S2R1Zfc00A2A2S1aS13S2dR2A1S15A3F_;Fn;").
Proof. intros n Hn. apply (forall_rangeZ_ok cost_ok 1 64512); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma cost_ok_secondary_small : ltac2:(tb__ "0|0|
S0S1bS2Zfc01R1A2S2R1Z11170A2A2S1aS13S2dR2A1S15A3F_;Fn;").
Proof. intros n Hn. apply (forall_rangeZ_ok cost_ok 64513 5488); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition not_batch_class (n : Z) : bool := ltac2:(tb__ "0|0|
S18SaS21S20Vn;A1A1Z18A2A1").
Lemma plen_class_ne_batch : ltac2:(tb__ "0|0|
S0S1bS2Z7ffbR1A2S2R1Zfc00A2A2S1dS1aS0S21S20R2A1A1Z18A3A1F_;Fn;").
Proof.
  intros n Hn. assert (H : not_batch_class n = true).
  { apply (forall_rangeZ_ok not_batch_class 32763 31750); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. }
  unfold not_batch_class in H. intros E. rewrite E in H. discriminate.
Qed.

Definition batch_class_chk (n : Z) : bool := ltac2:(tb__ "0|0|
S54SaS21S20Vn;A1A1Z18A2S14S4Z1701Vn;A2S4Vn;Z1f00A2A2A2").
Lemma batch_class_range : ltac2:(tb__ "0|0|
S0S1bS2Z1R1A2S2R1Zfc00A2A2S1aS13SaS21S20R2A1A1Z18A2S14S4Z1701R2A2S4R2Z1f00A2A2A3F_;Fn;").
Proof.
  intros n Hn. assert (H : batch_class_chk n = true).
  { apply (forall_rangeZ_ok batch_class_chk 1 64512); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. }
  unfold batch_class_chk in H. apply Bool.eqb_prop in H. exact H.
Qed.
