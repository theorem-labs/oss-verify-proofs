(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: generated for omx-clap-core/fuzz_preset's ASan+UBSan image (ELF sha256 d663f82d7f488d30)
   by gen_cells_b4.py (sha256 56230aea15da1bbd28b41ca9faa5e6543a9451678e5ae1f3cf84541e51c9436f): every constant below is read from that ELF by the rule in its comment, so a re-pin regenerates
   the file and no other file needs to carry the number. A shadow address is a FUNCTION of an image address
   (shadow_of), never a literal. Each cell carries its zify constant, so lia sees the value without an unfold.
   Unstripped twin sha256 c90d4fa54d43160b, dry run sha256 6a2c5bca84f957a6. *)
(* Rekeyed by the internal file gen_cells_b4.py: the dry run states some places as section + offset in image B (unstripped
   twin sha256 3b5e1a099b535acf). A cell whose comment says rekeyed (a) / (b) / (c) is that image-B place moved to this image:
   (a) the same static of the same STT_FILE unit, same offset; (b) the place every identical auipc pair computes
   here (a jump-table slot: the table base they compute + the same offset, every entry of the table checked);
   (c) the one copy here of its NUL-ended image-B string, same offset. A place no sub-rule moves is not emitted.
   The map, the internal file b-to-bprime.tsv (sha256 5a684bb2b7b6cfd5) was read only as a cross-check, never as a source. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00 YImgTop.
From Stdlib Require Import ZArith ZifyClasses ZifyInst.
Open Scope Z_scope.
Definition shadow_of (a : Z) : Z := a / 8 + 0x7fff8000.

(* the image bounds YImgTop states, read from this ELF, so lia sees them beside the cells *)
#[export] Instance Op_YImgTop_IMG_LO_B : @CstOp Z Z YImgTop.IMG_LO_B Inj_Z_Z := @mkcst Z Z YImgTop.IMG_LO_B Inj_Z_Z 0x10000 eq_refl.
Add Zify CstOp Op_YImgTop_IMG_LO_B.
#[export] Instance Op_YImgTop_IMG_TOP_B : @CstOp Z Z YImgTop.IMG_TOP_B Inj_Z_Z := @mkcst Z Z YImgTop.IMG_TOP_B Inj_Z_Z 0x601000 eq_refl.
Add Zify CstOp Op_YImgTop_IMG_TOP_B.

Definition B_10RE_PC : Z := 0x35560.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE20EnsureFreeArraySpaceEPNS5_10RegionInfoEmm (328 bytes) *)
#[export] Instance Op_B_10RE_PC : @CstOp Z Z B_10RE_PC Inj_Z_Z := @mkcst Z Z B_10RE_PC Inj_Z_Z 0x35560 eq_refl.
Add Zify CstOp Op_B_10RE_PC.
Definition B_10RE_PC_OFF_120 : Z := 0x379bc.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x120 *)
#[export] Instance Op_B_10RE_PC_OFF_120 : @CstOp Z Z B_10RE_PC_OFF_120 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_120 Inj_Z_Z 0x379bc eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_120.
Definition B_10RE_PC_OFF_13C : Z := 0x379d8.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x13c *)
#[export] Instance Op_B_10RE_PC_OFF_13C : @CstOp Z Z B_10RE_PC_OFF_13C Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_13C Inj_Z_Z 0x379d8 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_13C.
Definition B_10RE_PC_OFF_174 : Z := 0x37a10.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x174 *)
#[export] Instance Op_B_10RE_PC_OFF_174 : @CstOp Z Z B_10RE_PC_OFF_174 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_174 Inj_Z_Z 0x37a10 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_174.
Definition B_10RE_PC_OFF_180 : Z := 0x37a1c.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x180 *)
#[export] Instance Op_B_10RE_PC_OFF_180 : @CstOp Z Z B_10RE_PC_OFF_180 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_180 Inj_Z_Z 0x37a1c eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_180.
Definition B_10RE_PC_OFF_184 : Z := 0x37a20.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x184 *)
#[export] Instance Op_B_10RE_PC_OFF_184 : @CstOp Z Z B_10RE_PC_OFF_184 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_184 Inj_Z_Z 0x37a20 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_184.
Definition B_10RE_PC_OFF_19C : Z := 0x37a38.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x19c *)
#[export] Instance Op_B_10RE_PC_OFF_19C : @CstOp Z Z B_10RE_PC_OFF_19C Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_19C Inj_Z_Z 0x37a38 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_19C.
Definition B_10RE_PC_OFF_1BC : Z := 0x37a58.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x1bc *)
#[export] Instance Op_B_10RE_PC_OFF_1BC : @CstOp Z Z B_10RE_PC_OFF_1BC Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_1BC Inj_Z_Z 0x37a58 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_1BC.
Definition B_10RE_PC_OFF_1DC : Z := 0x37a78.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x1dc *)
#[export] Instance Op_B_10RE_PC_OFF_1DC : @CstOp Z Z B_10RE_PC_OFF_1DC Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_1DC Inj_Z_Z 0x37a78 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_1DC.
Definition B_10RE_PC_OFF_1EC : Z := 0x37a88.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x1ec *)
#[export] Instance Op_B_10RE_PC_OFF_1EC : @CstOp Z Z B_10RE_PC_OFF_1EC Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_1EC Inj_Z_Z 0x37a88 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_1EC.
Definition B_10RE_PC_OFF_1F0 : Z := 0x37a8c.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x1f0 *)
#[export] Instance Op_B_10RE_PC_OFF_1F0 : @CstOp Z Z B_10RE_PC_OFF_1F0 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_1F0 Inj_Z_Z 0x37a8c eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_1F0.
Definition B_10RE_PC_OFF_1F8 : Z := 0x37a94.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x1f8 *)
#[export] Instance Op_B_10RE_PC_OFF_1F8 : @CstOp Z Z B_10RE_PC_OFF_1F8 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_1F8 Inj_Z_Z 0x37a94 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_1F8.
Definition B_10RE_PC_OFF_24 : Z := 0x35584.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE20EnsureFreeArraySpaceEPNS5_10RegionInfoEmm + 0x24 *)
#[export] Instance Op_B_10RE_PC_OFF_24 : @CstOp Z Z B_10RE_PC_OFF_24 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_24 Inj_Z_Z 0x35584 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_24.
Definition B_10RE_PC_OFF_254 : Z := 0x37af0.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x254 *)
#[export] Instance Op_B_10RE_PC_OFF_254 : @CstOp Z Z B_10RE_PC_OFF_254 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_254 Inj_Z_Z 0x37af0 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_254.
Definition B_10RE_PC_OFF_38 : Z := 0x378d4.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x38 *)
#[export] Instance Op_B_10RE_PC_OFF_38 : @CstOp Z Z B_10RE_PC_OFF_38 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_38 Inj_Z_Z 0x378d4 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_38.
Definition B_10RE_PC_OFF_3C : Z := 0x3559c.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE20EnsureFreeArraySpaceEPNS5_10RegionInfoEmm + 0x3c *)
#[export] Instance Op_B_10RE_PC_OFF_3C : @CstOp Z Z B_10RE_PC_OFF_3C Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_3C Inj_Z_Z 0x3559c eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_3C.
Definition B_10RE_PC_OFF_40 : Z := 0x378dc.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x40 *)
#[export] Instance Op_B_10RE_PC_OFF_40 : @CstOp Z Z B_10RE_PC_OFF_40 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_40 Inj_Z_Z 0x378dc eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_40.
Definition B_10RE_PC_OFF_44 : Z := 0x355a4.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE20EnsureFreeArraySpaceEPNS5_10RegionInfoEmm + 0x44 *)
#[export] Instance Op_B_10RE_PC_OFF_44 : @CstOp Z Z B_10RE_PC_OFF_44 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_44 Inj_Z_Z 0x355a4 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_44.
Definition B_10RE_PC_OFF_8C : Z := 0x355ec.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE20EnsureFreeArraySpaceEPNS5_10RegionInfoEmm + 0x8c *)
#[export] Instance Op_B_10RE_PC_OFF_8C : @CstOp Z Z B_10RE_PC_OFF_8C Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_8C Inj_Z_Z 0x355ec eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_8C.
Definition B_10RE_PC_OFF_9C : Z := 0x37938.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x9c *)
#[export] Instance Op_B_10RE_PC_OFF_9C : @CstOp Z Z B_10RE_PC_OFF_9C Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_9C Inj_Z_Z 0x37938 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_9C.
Definition B_10RE_PC_OFF_A0 : Z := 0x3793c.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0xa0 *)
#[export] Instance Op_B_10RE_PC_OFF_A0 : @CstOp Z Z B_10RE_PC_OFF_A0 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_A0 Inj_Z_Z 0x3793c eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_A0.
Definition B_10RE_PC_OFF_A4 : Z := 0x37940.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0xa4 *)
#[export] Instance Op_B_10RE_PC_OFF_A4 : @CstOp Z Z B_10RE_PC_OFF_A4 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_A4 Inj_Z_Z 0x37940 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_A4.
Definition B_10RE_PC_OFF_BC : Z := 0x3561c.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE20EnsureFreeArraySpaceEPNS5_10RegionInfoEmm + 0xbc *)
#[export] Instance Op_B_10RE_PC_OFF_BC : @CstOp Z Z B_10RE_PC_OFF_BC Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_BC Inj_Z_Z 0x3561c eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_BC.
Definition B_10RE_PC_OFF_C0 : Z := 0x3795c.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0xc0 *)
#[export] Instance Op_B_10RE_PC_OFF_C0 : @CstOp Z Z B_10RE_PC_OFF_C0 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_C0 Inj_Z_Z 0x3795c eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_C0.
Definition B_10RE_PC_OFF_D4 : Z := 0x37970.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0xd4 *)
#[export] Instance Op_B_10RE_PC_OFF_D4 : @CstOp Z Z B_10RE_PC_OFF_D4 Inj_Z_Z := @mkcst Z Z B_10RE_PC_OFF_D4 Inj_Z_Z 0x37970 eq_refl.
Add Zify CstOp Op_B_10RE_PC_OFF_D4.
Definition B_8PERCL_PC : Z := 0x37494.   (* symbol _ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE6RefillEPNS7_8PerClassEPS6_m (256 bytes) *)
#[export] Instance Op_B_8PERCL_PC : @CstOp Z Z B_8PERCL_PC Inj_Z_Z := @mkcst Z Z B_8PERCL_PC Inj_Z_Z 0x37494 eq_refl.
Add Zify CstOp Op_B_8PERCL_PC.
Definition B_8PERCL_PC_OFF_20 : Z := 0x374b4.   (* symbol _ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE6RefillEPNS7_8PerClassEPS6_m + 0x20 *)
#[export] Instance Op_B_8PERCL_PC_OFF_20 : @CstOp Z Z B_8PERCL_PC_OFF_20 Inj_Z_Z := @mkcst Z Z B_8PERCL_PC_OFF_20 Inj_Z_Z 0x374b4 eq_refl.
Add Zify CstOp Op_B_8PERCL_PC_OFF_20.
Definition B_8PERCL_PC_OFF_24 : Z := 0x374b8.   (* symbol _ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE6RefillEPNS7_8PerClassEPS6_m + 0x24 *)
#[export] Instance Op_B_8PERCL_PC_OFF_24 : @CstOp Z Z B_8PERCL_PC_OFF_24 Inj_Z_Z := @mkcst Z Z B_8PERCL_PC_OFF_24 Inj_Z_Z 0x374b8 eq_refl.
Add Zify CstOp Op_B_8PERCL_PC_OFF_24.
Definition B_8PERCL_PC_OFF_58 : Z := 0x374ec.   (* symbol _ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE6RefillEPNS7_8PerClassEPS6_m + 0x58 *)
#[export] Instance Op_B_8PERCL_PC_OFF_58 : @CstOp Z Z B_8PERCL_PC_OFF_58 Inj_Z_Z := @mkcst Z Z B_8PERCL_PC_OFF_58 Inj_Z_Z 0x374ec eq_refl.
Add Zify CstOp Op_B_8PERCL_PC_OFF_58.
Definition B_8PERCL_PC_OFF_5C : Z := 0x374f0.   (* symbol _ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE6RefillEPNS7_8PerClassEPS6_m + 0x5c *)
#[export] Instance Op_B_8PERCL_PC_OFF_5C : @CstOp Z Z B_8PERCL_PC_OFF_5C Inj_Z_Z := @mkcst Z Z B_8PERCL_PC_OFF_5C Inj_Z_Z 0x374f0 eq_refl.
Add Zify CstOp Op_B_8PERCL_PC_OFF_5C.
Definition B_8PERCL_PC_OFF_F8 : Z := 0x3758c.   (* symbol _ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE6RefillEPNS7_8PerClassEPS6_m + 0xf8 *)
#[export] Instance Op_B_8PERCL_PC_OFF_F8 : @CstOp Z Z B_8PERCL_PC_OFF_F8 Inj_Z_Z := @mkcst Z Z B_8PERCL_PC_OFF_F8 Inj_Z_Z 0x3758c eq_refl.
Add Zify CstOp Op_B_8PERCL_PC_OFF_F8.
Definition B_ALLOCATORSTATS_PC : Z := 0x34ec8.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE10DeallocateEPNS_14AllocatorStatsEPv (460 bytes) *)
#[export] Instance Op_B_ALLOCATORSTATS_PC : @CstOp Z Z B_ALLOCATORSTATS_PC Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC Inj_Z_Z 0x34ec8 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC.
Definition B_ALLOCATORSTATS_PC_OFF_100 : Z := 0x34fc8.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE10DeallocateEPNS_14AllocatorStatsEPv + 0x100 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_100 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_100 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_100 Inj_Z_Z 0x34fc8 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_100.
Definition B_ALLOCATORSTATS_PC_OFF_114 : Z := 0x37130.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x114 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_114 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_114 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_114 Inj_Z_Z 0x37130 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_114.
Definition B_ALLOCATORSTATS_PC_OFF_120 : Z := 0x3713c.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x120 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_120 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_120 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_120 Inj_Z_Z 0x3713c eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_120.
Definition B_ALLOCATORSTATS_PC_OFF_124 : Z := 0x37140.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x124 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_124 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_124 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_124 Inj_Z_Z 0x37140 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_124.
Definition B_ALLOCATORSTATS_PC_OFF_154 : Z := 0x376e8.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16GetFromAllocatorEPNS_14AllocatorStatsEmPjm + 0x154 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_154 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_154 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_154 Inj_Z_Z 0x376e8 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_154.
Definition B_ALLOCATORSTATS_PC_OFF_15C : Z := 0x37178.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x15c *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_15C : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_15C Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_15C Inj_Z_Z 0x37178 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_15C.
Definition B_ALLOCATORSTATS_PC_OFF_160 : Z := 0x3717c.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x160 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_160 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_160 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_160 Inj_Z_Z 0x3717c eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_160.
Definition B_ALLOCATORSTATS_PC_OFF_174 : Z := 0x37708.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16GetFromAllocatorEPNS_14AllocatorStatsEmPjm + 0x174 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_174 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_174 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_174 Inj_Z_Z 0x37708 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_174.
Definition B_ALLOCATORSTATS_PC_OFF_17C : Z := 0x353b4.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17ReturnToAllocatorEPNS_12MemoryMapperIS5_EEPNS_14AllocatorStatsEmPKjm + 0x17c *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_17C : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_17C Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_17C Inj_Z_Z 0x353b4 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_17C.
Definition B_ALLOCATORSTATS_PC_OFF_188 : Z := 0x3771c.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16GetFromAllocatorEPNS_14AllocatorStatsEmPjm + 0x188 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_188 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_188 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_188 Inj_Z_Z 0x3771c eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_188.
Definition B_ALLOCATORSTATS_PC_OFF_190 : Z := 0x353c8.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17ReturnToAllocatorEPNS_12MemoryMapperIS5_EEPNS_14AllocatorStatsEmPKjm + 0x190 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_190 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_190 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_190 Inj_Z_Z 0x353c8 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_190.
Definition B_ALLOCATORSTATS_PC_OFF_260 : Z := 0x3727c.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x260 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_260 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_260 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_260 Inj_Z_Z 0x3727c eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_260.
Definition B_ALLOCATORSTATS_PC_OFF_278 : Z := 0x37294.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x278 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_278 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_278 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_278 Inj_Z_Z 0x37294 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_278.
Definition B_ALLOCATORSTATS_PC_OFF_2A4 : Z := 0x372c0.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x2a4 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_2A4 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_2A4 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_2A4 Inj_Z_Z 0x372c0 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_2A4.
Definition B_ALLOCATORSTATS_PC_OFF_2AC : Z := 0x372c8.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x2ac *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_2AC : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_2AC Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_2AC Inj_Z_Z 0x372c8 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_2AC.
Definition B_ALLOCATORSTATS_PC_OFF_2B4 : Z := 0x372d0.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x2b4 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_2B4 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_2B4 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_2B4 Inj_Z_Z 0x372d0 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_2B4.
Definition B_ALLOCATORSTATS_PC_OFF_2C8 : Z := 0x3785c.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16GetFromAllocatorEPNS_14AllocatorStatsEmPjm + 0x2c8 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_2C8 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_2C8 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_2C8 Inj_Z_Z 0x3785c eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_2C8.
Definition B_ALLOCATORSTATS_PC_OFF_45C : Z := 0x37478.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x45c *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_45C : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_45C Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_45C Inj_Z_Z 0x37478 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_45C.
Definition B_ALLOCATORSTATS_PC_OFF_7C : Z := 0x37098.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x7c *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_7C : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_7C Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_7C Inj_Z_Z 0x37098 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_7C.
Definition B_ALLOCATORSTATS_PC_OFF_80 : Z := 0x37614.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16GetFromAllocatorEPNS_14AllocatorStatsEmPjm + 0x80 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_80 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_80 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_80 Inj_Z_Z 0x37614 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_80.
Definition B_ALLOCATORSTATS_PC_OFF_90 : Z := 0x352c8.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17ReturnToAllocatorEPNS_12MemoryMapperIS5_EEPNS_14AllocatorStatsEmPKjm + 0x90 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_90 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_90 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_90 Inj_Z_Z 0x352c8 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_90.
Definition B_ALLOCATORSTATS_PC_OFF_BC : Z := 0x370d8.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0xbc *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_BC : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_BC Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_BC Inj_Z_Z 0x370d8 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_BC.
Definition B_ALLOCATORSTATS_PC_OFF_D8 : Z := 0x34fa0.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE10DeallocateEPNS_14AllocatorStatsEPv + 0xd8 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_D8 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_D8 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_D8 Inj_Z_Z 0x34fa0 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_D8.
Definition B_ALLOCATORSTATS_PC_OFF_DC : Z := 0x34fa4.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE10DeallocateEPNS_14AllocatorStatsEPv + 0xdc *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_DC : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_DC Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_DC Inj_Z_Z 0x34fa4 eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_DC.
Definition B_ALLOCATORSTATS_PC_OFF_F4 : Z := 0x34fbc.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE10DeallocateEPNS_14AllocatorStatsEPv + 0xf4 *)
#[export] Instance Op_B_ALLOCATORSTATS_PC_OFF_F4 : @CstOp Z Z B_ALLOCATORSTATS_PC_OFF_F4 Inj_Z_Z := @mkcst Z Z B_ALLOCATORSTATS_PC_OFF_F4 Inj_Z_Z 0x34fbc eq_refl.
Add Zify CstOp Op_B_ALLOCATORSTATS_PC_OFF_F4.
Definition B_ALLOCTYPE_PC : Z := 0x32368.   (* symbol _ZN6__asan9asan_freeEPvPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE (40 bytes) *)
#[export] Instance Op_B_ALLOCTYPE_PC : @CstOp Z Z B_ALLOCTYPE_PC Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC Inj_Z_Z 0x32368 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC.
Definition B_ALLOCTYPE_PC_OFF_104 : Z := 0x327a8.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x104 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_104 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_104 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_104 Inj_Z_Z 0x327a8 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_104.
Definition B_ALLOCTYPE_PC_OFF_114 : Z := 0x327b8.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x114 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_114 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_114 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_114 Inj_Z_Z 0x327b8 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_114.
Definition B_ALLOCTYPE_PC_OFF_128 : Z := 0x327cc.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x128 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_128 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_128 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_128 Inj_Z_Z 0x327cc eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_128.
Definition B_ALLOCTYPE_PC_OFF_13C : Z := 0x327e0.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x13c *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_13C : @CstOp Z Z B_ALLOCTYPE_PC_OFF_13C Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_13C Inj_Z_Z 0x327e0 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_13C.
Definition B_ALLOCTYPE_PC_OFF_150 : Z := 0x327f4.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x150 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_150 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_150 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_150 Inj_Z_Z 0x327f4 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_150.
Definition B_ALLOCTYPE_PC_OFF_164 : Z := 0x32808.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x164 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_164 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_164 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_164 Inj_Z_Z 0x32808 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_164.
Definition B_ALLOCTYPE_PC_OFF_170 : Z := 0x32814.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x170 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_170 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_170 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_170 Inj_Z_Z 0x32814 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_170.
Definition B_ALLOCTYPE_PC_OFF_1AC : Z := 0x32850.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x1ac *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_1AC : @CstOp Z Z B_ALLOCTYPE_PC_OFF_1AC Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_1AC Inj_Z_Z 0x32850 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_1AC.
Definition B_ALLOCTYPE_PC_OFF_1D8 : Z := 0x3287c.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x1d8 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_1D8 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_1D8 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_1D8 Inj_Z_Z 0x3287c eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_1D8.
Definition B_ALLOCTYPE_PC_OFF_1EC : Z := 0x32890.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x1ec *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_1EC : @CstOp Z Z B_ALLOCTYPE_PC_OFF_1EC Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_1EC Inj_Z_Z 0x32890 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_1EC.
Definition B_ALLOCTYPE_PC_OFF_1F4 : Z := 0x32898.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x1f4 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_1F4 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_1F4 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_1F4 Inj_Z_Z 0x32898 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_1F4.
Definition B_ALLOCTYPE_PC_OFF_1FC : Z := 0x328a0.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x1fc *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_1FC : @CstOp Z Z B_ALLOCTYPE_PC_OFF_1FC Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_1FC Inj_Z_Z 0x328a0 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_1FC.
Definition B_ALLOCTYPE_PC_OFF_214 : Z := 0x328b8.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x214 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_214 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_214 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_214 Inj_Z_Z 0x328b8 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_214.
Definition B_ALLOCTYPE_PC_OFF_2A0 : Z := 0x32944.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x2a0 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_2A0 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_2A0 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_2A0 Inj_Z_Z 0x32944 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_2A0.
Definition B_ALLOCTYPE_PC_OFF_2AC : Z := 0x32950.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x2ac *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_2AC : @CstOp Z Z B_ALLOCTYPE_PC_OFF_2AC Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_2AC Inj_Z_Z 0x32950 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_2AC.
Definition B_ALLOCTYPE_PC_OFF_2C4 : Z := 0x32968.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x2c4 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_2C4 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_2C4 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_2C4 Inj_Z_Z 0x32968 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_2C4.
Definition B_ALLOCTYPE_PC_OFF_2EC : Z := 0x32990.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x2ec *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_2EC : @CstOp Z Z B_ALLOCTYPE_PC_OFF_2EC Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_2EC Inj_Z_Z 0x32990 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_2EC.
Definition B_ALLOCTYPE_PC_OFF_3AC : Z := 0x32a50.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x3ac *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_3AC : @CstOp Z Z B_ALLOCTYPE_PC_OFF_3AC Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_3AC Inj_Z_Z 0x32a50 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_3AC.
Definition B_ALLOCTYPE_PC_OFF_3D4 : Z := 0x32a78.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x3d4 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_3D4 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_3D4 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_3D4 Inj_Z_Z 0x32a78 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_3D4.
Definition B_ALLOCTYPE_PC_OFF_3E0 : Z := 0x32a84.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x3e0 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_3E0 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_3E0 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_3E0 Inj_Z_Z 0x32a84 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_3E0.
Definition B_ALLOCTYPE_PC_OFF_3F0 : Z := 0x32a94.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x3f0 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_3F0 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_3F0 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_3F0 Inj_Z_Z 0x32a94 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_3F0.
Definition B_ALLOCTYPE_PC_OFF_418 : Z := 0x32abc.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x418 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_418 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_418 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_418 Inj_Z_Z 0x32abc eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_418.
Definition B_ALLOCTYPE_PC_OFF_484 : Z := 0x32b28.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x484 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_484 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_484 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_484 Inj_Z_Z 0x32b28 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_484.
Definition B_ALLOCTYPE_PC_OFF_494 : Z := 0x32b38.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x494 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_494 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_494 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_494 Inj_Z_Z 0x32b38 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_494.
Definition B_ALLOCTYPE_PC_OFF_498 : Z := 0x32b3c.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x498 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_498 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_498 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_498 Inj_Z_Z 0x32b3c eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_498.
Definition B_ALLOCTYPE_PC_OFF_4A4 : Z := 0x32b48.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x4a4 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_4A4 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_4A4 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_4A4 Inj_Z_Z 0x32b48 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_4A4.
Definition B_ALLOCTYPE_PC_OFF_4B8 : Z := 0x32b5c.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x4b8 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_4B8 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_4B8 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_4B8 Inj_Z_Z 0x32b5c eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_4B8.
Definition B_ALLOCTYPE_PC_OFF_4E4 : Z := 0x32b88.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x4e4 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_4E4 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_4E4 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_4E4 Inj_Z_Z 0x32b88 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_4E4.
Definition B_ALLOCTYPE_PC_OFF_520 : Z := 0x32bc4.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x520 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_520 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_520 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_520 Inj_Z_Z 0x32bc4 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_520.
Definition B_ALLOCTYPE_PC_OFF_524 : Z := 0x32bc8.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x524 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_524 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_524 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_524 Inj_Z_Z 0x32bc8 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_524.
Definition B_ALLOCTYPE_PC_OFF_548 : Z := 0x32bec.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x548 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_548 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_548 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_548 Inj_Z_Z 0x32bec eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_548.
Definition B_ALLOCTYPE_PC_OFF_5A4 : Z := 0x32c48.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x5a4 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_5A4 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_5A4 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_5A4 Inj_Z_Z 0x32c48 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_5A4.
Definition B_ALLOCTYPE_PC_OFF_690 : Z := 0x32d34.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x690 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_690 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_690 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_690 Inj_Z_Z 0x32d34 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_690.
Definition B_ALLOCTYPE_PC_OFF_698 : Z := 0x32d3c.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x698 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_698 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_698 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_698 Inj_Z_Z 0x32d3c eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_698.
Definition B_ALLOCTYPE_PC_OFF_6C0 : Z := 0x32d64.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x6c0 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_6C0 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_6C0 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_6C0 Inj_Z_Z 0x32d64 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_6C0.
Definition B_ALLOCTYPE_PC_OFF_6C8 : Z := 0x32d6c.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x6c8 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_6C8 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_6C8 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_6C8 Inj_Z_Z 0x32d6c eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_6C8.
Definition B_ALLOCTYPE_PC_OFF_6E0 : Z := 0x32d84.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x6e0 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_6E0 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_6E0 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_6E0 Inj_Z_Z 0x32d84 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_6E0.
Definition B_ALLOCTYPE_PC_OFF_708 : Z := 0x32dac.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x708 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_708 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_708 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_708 Inj_Z_Z 0x32dac eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_708.
Definition B_ALLOCTYPE_PC_OFF_710 : Z := 0x32db4.   (* symbol _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x710 *)
#[export] Instance Op_B_ALLOCTYPE_PC_OFF_710 : @CstOp Z Z B_ALLOCTYPE_PC_OFF_710 Inj_Z_Z := @mkcst Z Z B_ALLOCTYPE_PC_OFF_710 Inj_Z_Z 0x32db4 eq_refl.
Add Zify CstOp Op_B_ALLOCTYPE_PC_OFF_710.
Definition B_ASANCHUNK_PC : Z := 0x348fc.   (* symbol _ZNK6__asan18QuarantineCallback7RecycleEPNS_9AsanChunkE (644 bytes) *)
#[export] Instance Op_B_ASANCHUNK_PC : @CstOp Z Z B_ASANCHUNK_PC Inj_Z_Z := @mkcst Z Z B_ASANCHUNK_PC Inj_Z_Z 0x348fc eq_refl.
Add Zify CstOp Op_B_ASANCHUNK_PC.
Definition B_ASANCHUNK_PC_OFF_128 : Z := 0x34a24.   (* symbol _ZNK6__asan18QuarantineCallback7RecycleEPNS_9AsanChunkE + 0x128 *)
#[export] Instance Op_B_ASANCHUNK_PC_OFF_128 : @CstOp Z Z B_ASANCHUNK_PC_OFF_128 Inj_Z_Z := @mkcst Z Z B_ASANCHUNK_PC_OFF_128 Inj_Z_Z 0x34a24 eq_refl.
Add Zify CstOp Op_B_ASANCHUNK_PC_OFF_128.
Definition B_ASANCHUNK_PC_OFF_140 : Z := 0x34a3c.   (* symbol _ZNK6__asan18QuarantineCallback7RecycleEPNS_9AsanChunkE + 0x140 *)
#[export] Instance Op_B_ASANCHUNK_PC_OFF_140 : @CstOp Z Z B_ASANCHUNK_PC_OFF_140 Inj_Z_Z := @mkcst Z Z B_ASANCHUNK_PC_OFF_140 Inj_Z_Z 0x34a3c eq_refl.
Add Zify CstOp Op_B_ASANCHUNK_PC_OFF_140.
Definition B_ASANCHUNK_PC_OFF_16C : Z := 0x34a68.   (* symbol _ZNK6__asan18QuarantineCallback7RecycleEPNS_9AsanChunkE + 0x16c *)
#[export] Instance Op_B_ASANCHUNK_PC_OFF_16C : @CstOp Z Z B_ASANCHUNK_PC_OFF_16C Inj_Z_Z := @mkcst Z Z B_ASANCHUNK_PC_OFF_16C Inj_Z_Z 0x34a68 eq_refl.
Add Zify CstOp Op_B_ASANCHUNK_PC_OFF_16C.
Definition B_ASANCHUNK_PC_OFF_1BC : Z := 0x34ab8.   (* symbol _ZNK6__asan18QuarantineCallback7RecycleEPNS_9AsanChunkE + 0x1bc *)
#[export] Instance Op_B_ASANCHUNK_PC_OFF_1BC : @CstOp Z Z B_ASANCHUNK_PC_OFF_1BC Inj_Z_Z := @mkcst Z Z B_ASANCHUNK_PC_OFF_1BC Inj_Z_Z 0x34ab8 eq_refl.
Add Zify CstOp Op_B_ASANCHUNK_PC_OFF_1BC.
Definition B_ASANCHUNK_PC_OFF_22C : Z := 0x34b28.   (* symbol _ZNK6__asan18QuarantineCallback7RecycleEPNS_9AsanChunkE + 0x22c *)
#[export] Instance Op_B_ASANCHUNK_PC_OFF_22C : @CstOp Z Z B_ASANCHUNK_PC_OFF_22C Inj_Z_Z := @mkcst Z Z B_ASANCHUNK_PC_OFF_22C Inj_Z_Z 0x34b28 eq_refl.
Add Zify CstOp Op_B_ASANCHUNK_PC_OFF_22C.
Definition B_ASANCHUNK_PC_OFF_50 : Z := 0x3494c.   (* symbol _ZNK6__asan18QuarantineCallback7RecycleEPNS_9AsanChunkE + 0x50 *)
#[export] Instance Op_B_ASANCHUNK_PC_OFF_50 : @CstOp Z Z B_ASANCHUNK_PC_OFF_50 Inj_Z_Z := @mkcst Z Z B_ASANCHUNK_PC_OFF_50 Inj_Z_Z 0x3494c eq_refl.
Add Zify CstOp Op_B_ASANCHUNK_PC_OFF_50.
Definition B_ASANCHUNK_PC_OFF_74 : Z := 0x34970.   (* symbol _ZNK6__asan18QuarantineCallback7RecycleEPNS_9AsanChunkE + 0x74 *)
#[export] Instance Op_B_ASANCHUNK_PC_OFF_74 : @CstOp Z Z B_ASANCHUNK_PC_OFF_74 Inj_Z_Z := @mkcst Z Z B_ASANCHUNK_PC_OFF_74 Inj_Z_Z 0x34970 eq_refl.
Add Zify CstOp Op_B_ASANCHUNK_PC_OFF_74.
Definition B_ASANCHUNK_PC_OFF_78 : Z := 0x34974.   (* symbol _ZNK6__asan18QuarantineCallback7RecycleEPNS_9AsanChunkE + 0x78 *)
#[export] Instance Op_B_ASANCHUNK_PC_OFF_78 : @CstOp Z Z B_ASANCHUNK_PC_OFF_78 Inj_Z_Z := @mkcst Z Z B_ASANCHUNK_PC_OFF_78 Inj_Z_Z 0x34974 eq_refl.
Add Zify CstOp Op_B_ASANCHUNK_PC_OFF_78.
Definition B_ASANCHUNK_PC_OFF_B0 : Z := 0x349ac.   (* symbol _ZNK6__asan18QuarantineCallback7RecycleEPNS_9AsanChunkE + 0xb0 *)
#[export] Instance Op_B_ASANCHUNK_PC_OFF_B0 : @CstOp Z Z B_ASANCHUNK_PC_OFF_B0 Inj_Z_Z := @mkcst Z Z B_ASANCHUNK_PC_OFF_B0 Inj_Z_Z 0x349ac eq_refl.
Add Zify CstOp Op_B_ASANCHUNK_PC_OFF_B0.
Definition B_ASANCHUNK_PC_OFF_E0 : Z := 0x349dc.   (* symbol _ZNK6__asan18QuarantineCallback7RecycleEPNS_9AsanChunkE + 0xe0 *)
#[export] Instance Op_B_ASANCHUNK_PC_OFF_E0 : @CstOp Z Z B_ASANCHUNK_PC_OFF_E0 Inj_Z_Z := @mkcst Z Z B_ASANCHUNK_PC_OFF_E0 Inj_Z_Z 0x349dc eq_refl.
Add Zify CstOp Op_B_ASANCHUNK_PC_OFF_E0.
Definition B_ASANCHUNK_PC_OFF_E4 : Z := 0x349e0.   (* symbol _ZNK6__asan18QuarantineCallback7RecycleEPNS_9AsanChunkE + 0xe4 *)
#[export] Instance Op_B_ASANCHUNK_PC_OFF_E4 : @CstOp Z Z B_ASANCHUNK_PC_OFF_E4 Inj_Z_Z := @mkcst Z Z B_ASANCHUNK_PC_OFF_E4 Inj_Z_Z 0x349e0 eq_refl.
Add Zify CstOp Op_B_ASANCHUNK_PC_OFF_E4.
Definition B_ASANCHUNK_PC_OFF_EC : Z := 0x349e8.   (* symbol _ZNK6__asan18QuarantineCallback7RecycleEPNS_9AsanChunkE + 0xec *)
#[export] Instance Op_B_ASANCHUNK_PC_OFF_EC : @CstOp Z Z B_ASANCHUNK_PC_OFF_EC Inj_Z_Z := @mkcst Z Z B_ASANCHUNK_PC_OFF_EC Inj_Z_Z 0x349e8 eq_refl.
Add Zify CstOp Op_B_ASANCHUNK_PC_OFF_EC.
Definition B_ASANINITED_PC : Z := 0x59918.   (* symbol _ZN6__asan10AsanInitedEv (24 bytes) *)
#[export] Instance Op_B_ASANINITED_PC : @CstOp Z Z B_ASANINITED_PC Inj_Z_Z := @mkcst Z Z B_ASANINITED_PC Inj_Z_Z 0x59918 eq_refl.
Add Zify CstOp Op_B_ASANINITED_PC.
Definition B_ASANTSDGET_PC : Z := 0x55b74.   (* symbol _ZN6__asan10AsanTSDGetEv (64 bytes) *)
#[export] Instance Op_B_ASANTSDGET_PC : @CstOp Z Z B_ASANTSDGET_PC Inj_Z_Z := @mkcst Z Z B_ASANTSDGET_PC Inj_Z_Z 0x55b74 eq_refl.
Add Zify CstOp Op_B_ASANTSDGET_PC.
Definition B_ASAN_FLAGS_DONT_USE_DIRECTLY_CELL : Z := 0xa8ef8.   (* symbol _ZN6__asan28asan_flags_dont_use_directlyE (120 bytes) *)
#[export] Instance Op_B_ASAN_FLAGS_DONT_USE_DIRECTLY_CELL : @CstOp Z Z B_ASAN_FLAGS_DONT_USE_DIRECTLY_CELL Inj_Z_Z := @mkcst Z Z B_ASAN_FLAGS_DONT_USE_DIRECTLY_CELL Inj_Z_Z 0xa8ef8 eq_refl.
Add Zify CstOp Op_B_ASAN_FLAGS_DONT_USE_DIRECTLY_CELL.
Definition B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_28_CELL : Z := 0xa8f20.   (* symbol _ZN6__asan28asan_flags_dont_use_directlyE + 0x28 *)
#[export] Instance Op_B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_28_CELL : @CstOp Z Z B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_28_CELL Inj_Z_Z := @mkcst Z Z B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_28_CELL Inj_Z_Z 0xa8f20 eq_refl.
Add Zify CstOp Op_B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_28_CELL.
Definition B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_30_CELL : Z := 0xa8f28.   (* symbol _ZN6__asan28asan_flags_dont_use_directlyE + 0x30 *)
#[export] Instance Op_B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_30_CELL : @CstOp Z Z B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_30_CELL Inj_Z_Z := @mkcst Z Z B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_30_CELL Inj_Z_Z 0xa8f28 eq_refl.
Add Zify CstOp Op_B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_30_CELL.
Definition B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_38_CELL : Z := 0xa8f30.   (* symbol _ZN6__asan28asan_flags_dont_use_directlyE + 0x38 (extra: owner request 16:31Z) *)
#[export] Instance Op_B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_38_CELL : @CstOp Z Z B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_38_CELL Inj_Z_Z := @mkcst Z Z B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_38_CELL Inj_Z_Z 0xa8f30 eq_refl.
Add Zify CstOp Op_B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_38_CELL.
Definition B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_48_CELL : Z := 0xa8f40.   (* symbol _ZN6__asan28asan_flags_dont_use_directlyE + 0x48 *)
#[export] Instance Op_B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_48_CELL : @CstOp Z Z B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_48_CELL Inj_Z_Z := @mkcst Z Z B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_48_CELL Inj_Z_Z 0xa8f40 eq_refl.
Add Zify CstOp Op_B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_48_CELL.
Definition B_ASAN_GLOBALS_CELL : Z := 0xa7160.   (* start of section asan_globals *)
#[export] Instance Op_B_ASAN_GLOBALS_CELL : @CstOp Z Z B_ASAN_GLOBALS_CELL Inj_Z_Z := @mkcst Z Z B_ASAN_GLOBALS_CELL Inj_Z_Z 0xa7160 eq_refl.
Add Zify CstOp Op_B_ASAN_GLOBALS_CELL.
Definition B_ASAN_GLOBALS_HI : Z := 0xa8020.   (* end of section asan_globals (addr + size) *)
#[export] Instance Op_B_ASAN_GLOBALS_HI : @CstOp Z Z B_ASAN_GLOBALS_HI Inj_Z_Z := @mkcst Z Z B_ASAN_GLOBALS_HI Inj_Z_Z 0xa8020 eq_refl.
Add Zify CstOp Op_B_ASAN_GLOBALS_HI.
Definition B_ASAN_GLOBALS_OFF_0_CELL : Z := 0xa7160.   (* start of section asan_globals *)
#[export] Instance Op_B_ASAN_GLOBALS_OFF_0_CELL : @CstOp Z Z B_ASAN_GLOBALS_OFF_0_CELL Inj_Z_Z := @mkcst Z Z B_ASAN_GLOBALS_OFF_0_CELL Inj_Z_Z 0xa7160 eq_refl.
Add Zify CstOp Op_B_ASAN_GLOBALS_OFF_0_CELL.
Definition B_ASAN_GLOBALS_REGISTERED_CELL : Z := 0xa8040.   (* symbol ___asan_globals_registered (8 bytes) *)
#[export] Instance Op_B_ASAN_GLOBALS_REGISTERED_CELL : @CstOp Z Z B_ASAN_GLOBALS_REGISTERED_CELL Inj_Z_Z := @mkcst Z Z B_ASAN_GLOBALS_REGISTERED_CELL Inj_Z_Z 0xa8040 eq_refl.
Add Zify CstOp Op_B_ASAN_GLOBALS_REGISTERED_CELL.
Definition B_ASAN_INITED_CELL : Z := 0xac3d8.   (* symbol _ZN6__asanL11asan_initedE (1 bytes) *)
#[export] Instance Op_B_ASAN_INITED_CELL : @CstOp Z Z B_ASAN_INITED_CELL Inj_Z_Z := @mkcst Z Z B_ASAN_INITED_CELL Inj_Z_Z 0xac3d8 eq_refl.
Add Zify CstOp Op_B_ASAN_INITED_CELL.
Definition B_ASAN_MALLOC_BUFFEREDSTACKTRACE_PC : Z := 0x32648.   (* symbol _ZN6__asan11asan_mallocEmPN11__sanitizer18BufferedStackTraceE (92 bytes) *)
#[export] Instance Op_B_ASAN_MALLOC_BUFFEREDSTACKTRACE_PC : @CstOp Z Z B_ASAN_MALLOC_BUFFEREDSTACKTRACE_PC Inj_Z_Z := @mkcst Z Z B_ASAN_MALLOC_BUFFEREDSTACKTRACE_PC Inj_Z_Z 0x32648 eq_refl.
Add Zify CstOp Op_B_ASAN_MALLOC_BUFFEREDSTACKTRACE_PC.
Definition B_ASAN_MEMCPY_PC : Z := 0x524d0.   (* symbol __asan_memcpy (1180 bytes) *)
#[export] Instance Op_B_ASAN_MEMCPY_PC : @CstOp Z Z B_ASAN_MEMCPY_PC Inj_Z_Z := @mkcst Z Z B_ASAN_MEMCPY_PC Inj_Z_Z 0x524d0 eq_refl.
Add Zify CstOp Op_B_ASAN_MEMCPY_PC.
Definition B_ASAN_MEMCPY_PC_OFF_9C : Z := 0x5256c.   (* symbol __asan_memcpy + 0x9c *)
#[export] Instance Op_B_ASAN_MEMCPY_PC_OFF_9C : @CstOp Z Z B_ASAN_MEMCPY_PC_OFF_9C Inj_Z_Z := @mkcst Z Z B_ASAN_MEMCPY_PC_OFF_9C Inj_Z_Z 0x5256c eq_refl.
Add Zify CstOp Op_B_ASAN_MEMCPY_PC_OFF_9C.
Definition B_ASAN_MEMCPY_PC_OFF_A0 : Z := 0x52570.   (* symbol __asan_memcpy + 0xa0 *)
#[export] Instance Op_B_ASAN_MEMCPY_PC_OFF_A0 : @CstOp Z Z B_ASAN_MEMCPY_PC_OFF_A0 Inj_Z_Z := @mkcst Z Z B_ASAN_MEMCPY_PC_OFF_A0 Inj_Z_Z 0x52570 eq_refl.
Add Zify CstOp Op_B_ASAN_MEMCPY_PC_OFF_A0.
Definition B_ASAN_MEMCPY_PC_OFF_A8 : Z := 0x52578.   (* symbol __asan_memcpy + 0xa8 *)
#[export] Instance Op_B_ASAN_MEMCPY_PC_OFF_A8 : @CstOp Z Z B_ASAN_MEMCPY_PC_OFF_A8 Inj_Z_Z := @mkcst Z Z B_ASAN_MEMCPY_PC_OFF_A8 Inj_Z_Z 0x52578 eq_refl.
Add Zify CstOp Op_B_ASAN_MEMCPY_PC_OFF_A8.
Definition B_ASAN_MEMCPY_PC_OFF_E4 : Z := 0x525b4.   (* symbol __asan_memcpy + 0xe4 *)
#[export] Instance Op_B_ASAN_MEMCPY_PC_OFF_E4 : @CstOp Z Z B_ASAN_MEMCPY_PC_OFF_E4 Inj_Z_Z := @mkcst Z Z B_ASAN_MEMCPY_PC_OFF_E4 Inj_Z_Z 0x525b4 eq_refl.
Add Zify CstOp Op_B_ASAN_MEMCPY_PC_OFF_E4.
Definition B_ASAN_MEMCPY_PC_OFF_E8 : Z := 0x525b8.   (* symbol __asan_memcpy + 0xe8 *)
#[export] Instance Op_B_ASAN_MEMCPY_PC_OFF_E8 : @CstOp Z Z B_ASAN_MEMCPY_PC_OFF_E8 Inj_Z_Z := @mkcst Z Z B_ASAN_MEMCPY_PC_OFF_E8 Inj_Z_Z 0x525b8 eq_refl.
Add Zify CstOp Op_B_ASAN_MEMCPY_PC_OFF_E8.
Definition B_ASAN_MEMCPY_PC_OFF_FC : Z := 0x525cc.   (* symbol __asan_memcpy + 0xfc *)
#[export] Instance Op_B_ASAN_MEMCPY_PC_OFF_FC : @CstOp Z Z B_ASAN_MEMCPY_PC_OFF_FC Inj_Z_Z := @mkcst Z Z B_ASAN_MEMCPY_PC_OFF_FC Inj_Z_Z 0x525cc eq_refl.
Add Zify CstOp Op_B_ASAN_MEMCPY_PC_OFF_FC.
Definition B_ASAN_MEMSET_PC : Z := 0x5296c.   (* symbol __asan_memset (576 bytes) *)
#[export] Instance Op_B_ASAN_MEMSET_PC : @CstOp Z Z B_ASAN_MEMSET_PC Inj_Z_Z := @mkcst Z Z B_ASAN_MEMSET_PC Inj_Z_Z 0x5296c eq_refl.
Add Zify CstOp Op_B_ASAN_MEMSET_PC.
Definition B_ASAN_MEMSET_PC_OFF_84 : Z := 0x529f0.   (* symbol __asan_memset + 0x84 *)
#[export] Instance Op_B_ASAN_MEMSET_PC_OFF_84 : @CstOp Z Z B_ASAN_MEMSET_PC_OFF_84 Inj_Z_Z := @mkcst Z Z B_ASAN_MEMSET_PC_OFF_84 Inj_Z_Z 0x529f0 eq_refl.
Add Zify CstOp Op_B_ASAN_MEMSET_PC_OFF_84.
Definition B_ASAN_MEMSET_PC_OFF_88 : Z := 0x529f4.   (* symbol __asan_memset + 0x88 *)
#[export] Instance Op_B_ASAN_MEMSET_PC_OFF_88 : @CstOp Z Z B_ASAN_MEMSET_PC_OFF_88 Inj_Z_Z := @mkcst Z Z B_ASAN_MEMSET_PC_OFF_88 Inj_Z_Z 0x529f4 eq_refl.
Add Zify CstOp Op_B_ASAN_MEMSET_PC_OFF_88.
Definition B_ASAN_MEMSET_PC_OFF_9C : Z := 0x52a08.   (* symbol __asan_memset + 0x9c *)
#[export] Instance Op_B_ASAN_MEMSET_PC_OFF_9C : @CstOp Z Z B_ASAN_MEMSET_PC_OFF_9C Inj_Z_Z := @mkcst Z Z B_ASAN_MEMSET_PC_OFF_9C Inj_Z_Z 0x52a08 eq_refl.
Add Zify CstOp Op_B_ASAN_MEMSET_PC_OFF_9C.
Definition B_ASAN_MODULE_DTOR_PC : Z := 0x85cd8.   (* symbol asan.module_dtor (48 bytes) *)
#[export] Instance Op_B_ASAN_MODULE_DTOR_PC : @CstOp Z Z B_ASAN_MODULE_DTOR_PC Inj_Z_Z := @mkcst Z Z B_ASAN_MODULE_DTOR_PC Inj_Z_Z 0x85cd8 eq_refl.
Add Zify CstOp Op_B_ASAN_MODULE_DTOR_PC.
Definition B_ASAN_OPTION_DETECT_STACK_USE_AFTER_RETURN_CELL : Z := 0xab700.   (* symbol __asan_option_detect_stack_use_after_return (4 bytes) *)
#[export] Instance Op_B_ASAN_OPTION_DETECT_STACK_USE_AFTER_RETURN_CELL : @CstOp Z Z B_ASAN_OPTION_DETECT_STACK_USE_AFTER_RETURN_CELL Inj_Z_Z := @mkcst Z Z B_ASAN_OPTION_DETECT_STACK_USE_AFTER_RETURN_CELL Inj_Z_Z 0xab700 eq_refl.
Add Zify CstOp Op_B_ASAN_OPTION_DETECT_STACK_USE_AFTER_RETURN_CELL.
Definition B_ASAN_OPTION_DETECT_STACK_USE_AFTER_RETURN_OFF_4_END_CELL : Z := 0xab704.   (* symbol __asan_option_detect_stack_use_after_return + 0x4 *)
#[export] Instance Op_B_ASAN_OPTION_DETECT_STACK_USE_AFTER_RETURN_OFF_4_END_CELL : @CstOp Z Z B_ASAN_OPTION_DETECT_STACK_USE_AFTER_RETURN_OFF_4_END_CELL Inj_Z_Z := @mkcst Z Z B_ASAN_OPTION_DETECT_STACK_USE_AFTER_RETURN_OFF_4_END_CELL Inj_Z_Z 0xab704 eq_refl.
Add Zify CstOp Op_B_ASAN_OPTION_DETECT_STACK_USE_AFTER_RETURN_OFF_4_END_CELL.
Definition B_ASAN_REGION_IS_POISONED_PC : Z := 0x55394.   (* symbol __asan_region_is_poisoned (836 bytes) *)
#[export] Instance Op_B_ASAN_REGION_IS_POISONED_PC : @CstOp Z Z B_ASAN_REGION_IS_POISONED_PC Inj_Z_Z := @mkcst Z Z B_ASAN_REGION_IS_POISONED_PC Inj_Z_Z 0x55394 eq_refl.
Add Zify CstOp Op_B_ASAN_REGION_IS_POISONED_PC.
Definition B_ASAN_REGION_IS_POISONED_PC_OFF_174 : Z := 0x55508.   (* symbol __asan_region_is_poisoned + 0x174 *)
#[export] Instance Op_B_ASAN_REGION_IS_POISONED_PC_OFF_174 : @CstOp Z Z B_ASAN_REGION_IS_POISONED_PC_OFF_174 Inj_Z_Z := @mkcst Z Z B_ASAN_REGION_IS_POISONED_PC_OFF_174 Inj_Z_Z 0x55508 eq_refl.
Add Zify CstOp Op_B_ASAN_REGION_IS_POISONED_PC_OFF_174.
Definition B_ASAN_SHADOW_MEMORY_DYNAMIC_ADDRESS_CELL : Z := 0xab6f8.   (* symbol __asan_shadow_memory_dynamic_address (8 bytes) *)
#[export] Instance Op_B_ASAN_SHADOW_MEMORY_DYNAMIC_ADDRESS_CELL : @CstOp Z Z B_ASAN_SHADOW_MEMORY_DYNAMIC_ADDRESS_CELL Inj_Z_Z := @mkcst Z Z B_ASAN_SHADOW_MEMORY_DYNAMIC_ADDRESS_CELL Inj_Z_Z 0xab6f8 eq_refl.
Add Zify CstOp Op_B_ASAN_SHADOW_MEMORY_DYNAMIC_ADDRESS_CELL.
Definition B_ASAN_STACK_MALLOC_1_PC : Z := 0x3dda8.   (* symbol __asan_stack_malloc_1 (400 bytes) *)
#[export] Instance Op_B_ASAN_STACK_MALLOC_1_PC : @CstOp Z Z B_ASAN_STACK_MALLOC_1_PC Inj_Z_Z := @mkcst Z Z B_ASAN_STACK_MALLOC_1_PC Inj_Z_Z 0x3dda8 eq_refl.
Add Zify CstOp Op_B_ASAN_STACK_MALLOC_1_PC.
Definition B_ASAN_STACK_MALLOC_1_PC_OFF_10C : Z := 0x3deb4.   (* symbol __asan_stack_malloc_1 + 0x10c *)
#[export] Instance Op_B_ASAN_STACK_MALLOC_1_PC_OFF_10C : @CstOp Z Z B_ASAN_STACK_MALLOC_1_PC_OFF_10C Inj_Z_Z := @mkcst Z Z B_ASAN_STACK_MALLOC_1_PC_OFF_10C Inj_Z_Z 0x3deb4 eq_refl.
Add Zify CstOp Op_B_ASAN_STACK_MALLOC_1_PC_OFF_10C.
Definition B_ASAN_STACK_MALLOC_1_PC_OFF_138 : Z := 0x3dee0.   (* symbol __asan_stack_malloc_1 + 0x138 *)
#[export] Instance Op_B_ASAN_STACK_MALLOC_1_PC_OFF_138 : @CstOp Z Z B_ASAN_STACK_MALLOC_1_PC_OFF_138 Inj_Z_Z := @mkcst Z Z B_ASAN_STACK_MALLOC_1_PC_OFF_138 Inj_Z_Z 0x3dee0 eq_refl.
Add Zify CstOp Op_B_ASAN_STACK_MALLOC_1_PC_OFF_138.
Definition B_ASAN_STACK_MALLOC_1_PC_OFF_154 : Z := 0x3defc.   (* symbol __asan_stack_malloc_1 + 0x154 *)
#[export] Instance Op_B_ASAN_STACK_MALLOC_1_PC_OFF_154 : @CstOp Z Z B_ASAN_STACK_MALLOC_1_PC_OFF_154 Inj_Z_Z := @mkcst Z Z B_ASAN_STACK_MALLOC_1_PC_OFF_154 Inj_Z_Z 0x3defc eq_refl.
Add Zify CstOp Op_B_ASAN_STACK_MALLOC_1_PC_OFF_154.
Definition B_ASAN_STACK_MALLOC_1_PC_OFF_94 : Z := 0x3de3c.   (* symbol __asan_stack_malloc_1 + 0x94 *)
#[export] Instance Op_B_ASAN_STACK_MALLOC_1_PC_OFF_94 : @CstOp Z Z B_ASAN_STACK_MALLOC_1_PC_OFF_94 Inj_Z_Z := @mkcst Z Z B_ASAN_STACK_MALLOC_1_PC_OFF_94 Inj_Z_Z 0x3de3c eq_refl.
Add Zify CstOp Op_B_ASAN_STACK_MALLOC_1_PC_OFF_94.
Definition B_ASAN_UNREGISTER_ELF_GLOBALS_PC : Z := 0x40dac.   (* symbol __asan_unregister_elf_globals (104 bytes) *)
#[export] Instance Op_B_ASAN_UNREGISTER_ELF_GLOBALS_PC : @CstOp Z Z B_ASAN_UNREGISTER_ELF_GLOBALS_PC Inj_Z_Z := @mkcst Z Z B_ASAN_UNREGISTER_ELF_GLOBALS_PC Inj_Z_Z 0x40dac eq_refl.
Add Zify CstOp Op_B_ASAN_UNREGISTER_ELF_GLOBALS_PC.
Definition B_ASAN_UNREGISTER_GLOBALS_PC : Z := 0x40774.   (* symbol __asan_unregister_globals (1484 bytes) *)
#[export] Instance Op_B_ASAN_UNREGISTER_GLOBALS_PC : @CstOp Z Z B_ASAN_UNREGISTER_GLOBALS_PC Inj_Z_Z := @mkcst Z Z B_ASAN_UNREGISTER_GLOBALS_PC Inj_Z_Z 0x40774 eq_refl.
Add Zify CstOp Op_B_ASAN_UNREGISTER_GLOBALS_PC.
Definition B_ATEXIT_PC : Z := 0x8fa1c.   (* symbol atexit (196 bytes) *)
#[export] Instance Op_B_ATEXIT_PC : @CstOp Z Z B_ATEXIT_PC Inj_Z_Z := @mkcst Z Z B_ATEXIT_PC Inj_Z_Z 0x8fa1c eq_refl.
Add Zify CstOp Op_B_ATEXIT_PC.
Definition B_BCMP_PC : Z := 0x9ba04.   (* symbol bcmp (4 bytes) *)
#[export] Instance Op_B_BCMP_PC : @CstOp Z Z B_BCMP_PC Inj_Z_Z := @mkcst Z Z B_BCMP_PC Inj_Z_Z 0x9ba04 eq_refl.
Add Zify CstOp Op_B_BCMP_PC.
Definition B_BUFFEREDSTACKTRACE_PC_OFF_58 : Z := 0x36890.   (* symbol _ZN6__asan9Allocator15QuarantineChunkEPNS_9AsanChunkEPvPN11__sanitizer18BufferedStackTraceE + 0x58 *)
#[export] Instance Op_B_BUFFEREDSTACKTRACE_PC_OFF_58 : @CstOp Z Z B_BUFFEREDSTACKTRACE_PC_OFF_58 Inj_Z_Z := @mkcst Z Z B_BUFFEREDSTACKTRACE_PC_OFF_58 Inj_Z_Z 0x36890 eq_refl.
Add Zify CstOp Op_B_BUFFEREDSTACKTRACE_PC_OFF_58.
Definition B_BUF_STDERR_CELL : Z := 0x5fee30.   (* B place section .bss + 0x556dd0, rekeyed (a) *)
#[export] Instance Op_B_BUF_STDERR_CELL : @CstOp Z Z B_BUF_STDERR_CELL Inj_Z_Z := @mkcst Z Z B_BUF_STDERR_CELL Inj_Z_Z 0x5fee30 eq_refl.
Add Zify CstOp Op_B_BUF_STDERR_CELL.
Definition B_BUF_STDIN_OFF_8_CELL : Z := 0x5ff248.   (* B place section .bss + 0x5571e8, rekeyed (a) *)
#[export] Instance Op_B_BUF_STDIN_OFF_8_CELL : @CstOp Z Z B_BUF_STDIN_OFF_8_CELL Inj_Z_Z := @mkcst Z Z B_BUF_STDIN_OFF_8_CELL Inj_Z_Z 0x5ff248 eq_refl.
Add Zify CstOp Op_B_BUF_STDIN_OFF_8_CELL.
Definition B_BUF_STDOUT_CELL : Z := 0x5fee38.   (* B place section .bss + 0x556dd8, rekeyed (a) *)
#[export] Instance Op_B_BUF_STDOUT_CELL : @CstOp Z Z B_BUF_STDOUT_CELL Inj_Z_Z := @mkcst Z Z B_BUF_STDOUT_CELL Inj_Z_Z 0x5fee38 eq_refl.
Add Zify CstOp Op_B_BUF_STDOUT_CELL.
Definition B_BUF_STDOUT_OFF_8_CELL : Z := 0x5fee40.   (* B place section .bss + 0x556de0, rekeyed (a) *)
#[export] Instance Op_B_BUF_STDOUT_OFF_8_CELL : @CstOp Z Z B_BUF_STDOUT_OFF_8_CELL Inj_Z_Z := @mkcst Z Z B_BUF_STDOUT_OFF_8_CELL Inj_Z_Z 0x5fee40 eq_refl.
Add Zify CstOp Op_B_BUF_STDOUT_OFF_8_CELL.
Definition B_BUILTIN_CELL : Z := 0x5fe798.   (* symbol builtin (520 bytes) *)
#[export] Instance Op_B_BUILTIN_CELL : @CstOp Z Z B_BUILTIN_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_CELL Inj_Z_Z 0x5fe798 eq_refl.
Add Zify CstOp Op_B_BUILTIN_CELL.
Definition B_BUILTIN_OFF_108_CELL : Z := 0x5fe8a0.   (* symbol builtin + 0x108 *)
#[export] Instance Op_B_BUILTIN_OFF_108_CELL : @CstOp Z Z B_BUILTIN_OFF_108_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_OFF_108_CELL Inj_Z_Z 0x5fe8a0 eq_refl.
Add Zify CstOp Op_B_BUILTIN_OFF_108_CELL.
Definition B_BUILTIN_OFF_10_CELL : Z := 0x5fe7a8.   (* symbol builtin + 0x10 *)
#[export] Instance Op_B_BUILTIN_OFF_10_CELL : @CstOp Z Z B_BUILTIN_OFF_10_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_OFF_10_CELL Inj_Z_Z 0x5fe7a8 eq_refl.
Add Zify CstOp Op_B_BUILTIN_OFF_10_CELL.
Definition B_BUILTIN_OFF_110_CELL : Z := 0x5fe8a8.   (* symbol builtin + 0x110 *)
#[export] Instance Op_B_BUILTIN_OFF_110_CELL : @CstOp Z Z B_BUILTIN_OFF_110_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_OFF_110_CELL Inj_Z_Z 0x5fe8a8 eq_refl.
Add Zify CstOp Op_B_BUILTIN_OFF_110_CELL.
Definition B_BUILTIN_OFF_118_CELL : Z := 0x5fe8b0.   (* symbol builtin + 0x118 *)
#[export] Instance Op_B_BUILTIN_OFF_118_CELL : @CstOp Z Z B_BUILTIN_OFF_118_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_OFF_118_CELL Inj_Z_Z 0x5fe8b0 eq_refl.
Add Zify CstOp Op_B_BUILTIN_OFF_118_CELL.
Definition B_BUILTIN_OFF_8_CELL : Z := 0x5fe7a0.   (* symbol builtin + 0x8 *)
#[export] Instance Op_B_BUILTIN_OFF_8_CELL : @CstOp Z Z B_BUILTIN_OFF_8_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_OFF_8_CELL Inj_Z_Z 0x5fe7a0 eq_refl.
Add Zify CstOp Op_B_BUILTIN_OFF_8_CELL.
Definition B_BUILTIN_TLS_CELL : Z := 0x5de668.   (* symbol builtin_tls (131280 bytes) *)
#[export] Instance Op_B_BUILTIN_TLS_CELL : @CstOp Z Z B_BUILTIN_TLS_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_TLS_CELL Inj_Z_Z 0x5de668 eq_refl.
Add Zify CstOp Op_B_BUILTIN_TLS_CELL.
Definition B_BUILTIN_TLS_OFF_24_CELL : Z := 0x5de68c.   (* symbol builtin_tls + 0x24 *)
#[export] Instance Op_B_BUILTIN_TLS_OFF_24_CELL : @CstOp Z Z B_BUILTIN_TLS_OFF_24_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_TLS_OFF_24_CELL Inj_Z_Z 0x5de68c eq_refl.
Add Zify CstOp Op_B_BUILTIN_TLS_OFF_24_CELL.
Definition B_BUILTIN_TLS_OFF_28_CELL : Z := 0x5de690.   (* symbol builtin_tls + 0x28 *)
#[export] Instance Op_B_BUILTIN_TLS_OFF_28_CELL : @CstOp Z Z B_BUILTIN_TLS_OFF_28_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_TLS_OFF_28_CELL Inj_Z_Z 0x5de690 eq_refl.
Add Zify CstOp Op_B_BUILTIN_TLS_OFF_28_CELL.
Definition B_BUILTIN_TLS_OFF_70_CELL : Z := 0x5de6d8.   (* symbol builtin_tls + 0x70 *)
#[export] Instance Op_B_BUILTIN_TLS_OFF_70_CELL : @CstOp Z Z B_BUILTIN_TLS_OFF_70_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_TLS_OFF_70_CELL Inj_Z_Z 0x5de6d8 eq_refl.
Add Zify CstOp Op_B_BUILTIN_TLS_OFF_70_CELL.
Definition B_BUILTIN_TLS_OFF_800_CELL : Z := 0x5dee68.   (* symbol builtin_tls + 0x800 *)
#[export] Instance Op_B_BUILTIN_TLS_OFF_800_CELL : @CstOp Z Z B_BUILTIN_TLS_OFF_800_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_TLS_OFF_800_CELL Inj_Z_Z 0x5dee68 eq_refl.
Add Zify CstOp Op_B_BUILTIN_TLS_OFF_800_CELL.
Definition B_BUILTIN_TLS_OFF_8C8_CELL : Z := 0x5def30.   (* symbol builtin_tls + 0x8c8 *)
#[export] Instance Op_B_BUILTIN_TLS_OFF_8C8_CELL : @CstOp Z Z B_BUILTIN_TLS_OFF_8C8_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_TLS_OFF_8C8_CELL Inj_Z_Z 0x5def30 eq_refl.
Add Zify CstOp Op_B_BUILTIN_TLS_OFF_8C8_CELL.
Definition B_BUILTIN_TLS_OFF_8DC_CELL : Z := 0x5def44.   (* symbol builtin_tls + 0x8dc *)
#[export] Instance Op_B_BUILTIN_TLS_OFF_8DC_CELL : @CstOp Z Z B_BUILTIN_TLS_OFF_8DC_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_TLS_OFF_8DC_CELL Inj_Z_Z 0x5def44 eq_refl.
Add Zify CstOp Op_B_BUILTIN_TLS_OFF_8DC_CELL.
Definition B_BUILTIN_TLS_OFF_C8_CELL : Z := 0x5de730.   (* symbol builtin_tls + 0xc8 *)
#[export] Instance Op_B_BUILTIN_TLS_OFF_C8_CELL : @CstOp Z Z B_BUILTIN_TLS_OFF_C8_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_TLS_OFF_C8_CELL Inj_Z_Z 0x5de730 eq_refl.
Add Zify CstOp Op_B_BUILTIN_TLS_OFF_C8_CELL.
Definition B_BUILTIN_TLS_OFF_D8_CELL : Z := 0x5de740.   (* symbol builtin_tls + 0xd8 *)
#[export] Instance Op_B_BUILTIN_TLS_OFF_D8_CELL : @CstOp Z Z B_BUILTIN_TLS_OFF_D8_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_TLS_OFF_D8_CELL Inj_Z_Z 0x5de740 eq_refl.
Add Zify CstOp Op_B_BUILTIN_TLS_OFF_D8_CELL.
Definition B_BUILTIN_TLS_OFF_E8_CELL : Z := 0x5de750.   (* symbol builtin_tls + 0xe8 *)
#[export] Instance Op_B_BUILTIN_TLS_OFF_E8_CELL : @CstOp Z Z B_BUILTIN_TLS_OFF_E8_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_TLS_OFF_E8_CELL Inj_Z_Z 0x5de750 eq_refl.
Add Zify CstOp Op_B_BUILTIN_TLS_OFF_E8_CELL.
Definition B_BUILTIN_TLS_OFF_F0_CELL : Z := 0x5de758.   (* symbol builtin_tls + 0xf0 *)
#[export] Instance Op_B_BUILTIN_TLS_OFF_F0_CELL : @CstOp Z Z B_BUILTIN_TLS_OFF_F0_CELL Inj_Z_Z := @mkcst Z Z B_BUILTIN_TLS_OFF_F0_CELL Inj_Z_Z 0x5de758 eq_refl.
Add Zify CstOp Op_B_BUILTIN_TLS_OFF_F0_CELL.
Definition B_CALL_PC : Z := 0x8fae0.   (* symbol call (4 bytes) *)
#[export] Instance Op_B_CALL_PC : @CstOp Z Z B_CALL_PC Inj_Z_Z := @mkcst Z Z B_CALL_PC Inj_Z_Z 0x8fae0 eq_refl.
Add Zify CstOp Op_B_CALL_PC.
Definition B_CANPOISONMEMORY_PC : Z := 0x549f8.   (* symbol _ZN6__asan15CanPoisonMemoryEv (20 bytes) *)
#[export] Instance Op_B_CANPOISONMEMORY_PC : @CstOp Z Z B_CANPOISONMEMORY_PC Inj_Z_Z := @mkcst Z Z B_CANPOISONMEMORY_PC Inj_Z_Z 0x549f8 eq_refl.
Add Zify CstOp Op_B_CANPOISONMEMORY_PC.
Definition B_CAN_POISON_MEMORY_CELL : Z := 0xaaf5c.   (* symbol _ZN6__asanL17can_poison_memoryE (1 bytes) *)
#[export] Instance Op_B_CAN_POISON_MEMORY_CELL : @CstOp Z Z B_CAN_POISON_MEMORY_CELL Inj_Z_Z := @mkcst Z Z B_CAN_POISON_MEMORY_CELL Inj_Z_Z 0xaaf5c eq_refl.
Add Zify CstOp Op_B_CAN_POISON_MEMORY_CELL.
Definition B_CLOSE_PC : Z := 0xa1128.   (* symbol close (84 bytes) *)
#[export] Instance Op_B_CLOSE_PC : @CstOp Z Z B_CLOSE_PC Inj_Z_Z := @mkcst Z Z B_CLOSE_PC Inj_Z_Z 0xa1128 eq_refl.
Add Zify CstOp Op_B_CLOSE_PC.
Definition B_COMMONFLAGS_PC_OFF_358 : Z := 0x62ce8.   (* symbol _ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x358 *)
#[export] Instance Op_B_COMMONFLAGS_PC_OFF_358 : @CstOp Z Z B_COMMONFLAGS_PC_OFF_358 Inj_Z_Z := @mkcst Z Z B_COMMONFLAGS_PC_OFF_358 Inj_Z_Z 0x62ce8 eq_refl.
Add Zify CstOp Op_B_COMMONFLAGS_PC_OFF_358.
Definition B_COMMON_FLAGS_DONT_USE_CELL : Z := 0x13d228.   (* symbol _ZN11__sanitizer21common_flags_dont_useE (288 bytes) *)
#[export] Instance Op_B_COMMON_FLAGS_DONT_USE_CELL : @CstOp Z Z B_COMMON_FLAGS_DONT_USE_CELL Inj_Z_Z := @mkcst Z Z B_COMMON_FLAGS_DONT_USE_CELL Inj_Z_Z 0x13d228 eq_refl.
Add Zify CstOp Op_B_COMMON_FLAGS_DONT_USE_CELL.
Definition B_COMMON_FLAGS_DONT_USE_OFF_100_CELL : Z := 0x13d328.   (* symbol _ZN11__sanitizer21common_flags_dont_useE + 0x100 *)
#[export] Instance Op_B_COMMON_FLAGS_DONT_USE_OFF_100_CELL : @CstOp Z Z B_COMMON_FLAGS_DONT_USE_OFF_100_CELL Inj_Z_Z := @mkcst Z Z B_COMMON_FLAGS_DONT_USE_OFF_100_CELL Inj_Z_Z 0x13d328 eq_refl.
Add Zify CstOp Op_B_COMMON_FLAGS_DONT_USE_OFF_100_CELL.
Definition B_COMMON_FLAGS_DONT_USE_OFF_20_CELL : Z := 0x13d248.   (* symbol _ZN11__sanitizer21common_flags_dont_useE + 0x20 *)
#[export] Instance Op_B_COMMON_FLAGS_DONT_USE_OFF_20_CELL : @CstOp Z Z B_COMMON_FLAGS_DONT_USE_OFF_20_CELL Inj_Z_Z := @mkcst Z Z B_COMMON_FLAGS_DONT_USE_OFF_20_CELL Inj_Z_Z 0x13d248 eq_refl.
Add Zify CstOp Op_B_COMMON_FLAGS_DONT_USE_OFF_20_CELL.
Definition B_COMMON_FLAGS_DONT_USE_OFF_54_CELL : Z := 0x13d27c.   (* symbol _ZN11__sanitizer21common_flags_dont_useE + 0x54 *)
#[export] Instance Op_B_COMMON_FLAGS_DONT_USE_OFF_54_CELL : @CstOp Z Z B_COMMON_FLAGS_DONT_USE_OFF_54_CELL Inj_Z_Z := @mkcst Z Z B_COMMON_FLAGS_DONT_USE_OFF_54_CELL Inj_Z_Z 0x13d27c eq_refl.
Add Zify CstOp Op_B_COMMON_FLAGS_DONT_USE_OFF_54_CELL.
Definition B_COMMON_FLAGS_DONT_USE_OFF_78_CELL : Z := 0x13d2a0.   (* symbol _ZN11__sanitizer21common_flags_dont_useE + 0x78 *)
#[export] Instance Op_B_COMMON_FLAGS_DONT_USE_OFF_78_CELL : @CstOp Z Z B_COMMON_FLAGS_DONT_USE_OFF_78_CELL Inj_Z_Z := @mkcst Z Z B_COMMON_FLAGS_DONT_USE_OFF_78_CELL Inj_Z_Z 0x13d2a0 eq_refl.
Add Zify CstOp Op_B_COMMON_FLAGS_DONT_USE_OFF_78_CELL.
Definition B_COMMON_FLAGS_DONT_USE_OFF_89_CELL : Z := 0x13d2b1.   (* symbol _ZN11__sanitizer21common_flags_dont_useE + 0x89 *)
#[export] Instance Op_B_COMMON_FLAGS_DONT_USE_OFF_89_CELL : @CstOp Z Z B_COMMON_FLAGS_DONT_USE_OFF_89_CELL Inj_Z_Z := @mkcst Z Z B_COMMON_FLAGS_DONT_USE_OFF_89_CELL Inj_Z_Z 0x13d2b1 eq_refl.
Add Zify CstOp Op_B_COMMON_FLAGS_DONT_USE_OFF_89_CELL.
Definition B_COMMON_FLAGS_DONT_USE_OFF_90_CELL : Z := 0x13d2b8.   (* symbol _ZN11__sanitizer21common_flags_dont_useE + 0x90 *)
#[export] Instance Op_B_COMMON_FLAGS_DONT_USE_OFF_90_CELL : @CstOp Z Z B_COMMON_FLAGS_DONT_USE_OFF_90_CELL Inj_Z_Z := @mkcst Z Z B_COMMON_FLAGS_DONT_USE_OFF_90_CELL Inj_Z_Z 0x13d2b8 eq_refl.
Add Zify CstOp Op_B_COMMON_FLAGS_DONT_USE_OFF_90_CELL.
Definition B_COMMON_FLAGS_DONT_USE_OFF_F0_CELL : Z := 0x13d318.   (* symbol _ZN11__sanitizer21common_flags_dont_useE + 0xf0 *)
#[export] Instance Op_B_COMMON_FLAGS_DONT_USE_OFF_F0_CELL : @CstOp Z Z B_COMMON_FLAGS_DONT_USE_OFF_F0_CELL Inj_Z_Z := @mkcst Z Z B_COMMON_FLAGS_DONT_USE_OFF_F0_CELL Inj_Z_Z 0x13d318 eq_refl.
Add Zify CstOp Op_B_COMMON_FLAGS_DONT_USE_OFF_F0_CELL.
Definition B_COMMON_FLAGS_DONT_USE_OFF_FB_CELL : Z := 0x13d323.   (* symbol _ZN11__sanitizer21common_flags_dont_useE + 0xfb *)
#[export] Instance Op_B_COMMON_FLAGS_DONT_USE_OFF_FB_CELL : @CstOp Z Z B_COMMON_FLAGS_DONT_USE_OFF_FB_CELL Inj_Z_Z := @mkcst Z Z B_COMMON_FLAGS_DONT_USE_OFF_FB_CELL Inj_Z_Z 0x13d323 eq_refl.
Add Zify CstOp Op_B_COMMON_FLAGS_DONT_USE_OFF_FB_CELL.
Definition B_COPY_TLS_PC : Z := 0x8f438.   (* symbol __copy_tls (216 bytes) *)
#[export] Instance Op_B_COPY_TLS_PC : @CstOp Z Z B_COPY_TLS_PC Inj_Z_Z := @mkcst Z Z B_COPY_TLS_PC Inj_Z_Z 0x8f438 eq_refl.
Add Zify CstOp Op_B_COPY_TLS_PC.
Definition B_CREATE_PC : Z := 0x71bfc.   (* symbol _ZN11__sanitizer10StackStore9BlockInfo6CreateEPS0_ (180 bytes) *)
#[export] Instance Op_B_CREATE_PC : @CstOp Z Z B_CREATE_PC Inj_Z_Z := @mkcst Z Z B_CREATE_PC Inj_Z_Z 0x71bfc eq_refl.
Add Zify CstOp Op_B_CREATE_PC.
Definition B_CURRENT_VERBOSITY_CELL : Z := 0x13b198.   (* symbol _ZN11__sanitizer17current_verbosityE (4 bytes) *)
#[export] Instance Op_B_CURRENT_VERBOSITY_CELL : @CstOp Z Z B_CURRENT_VERBOSITY_CELL Inj_Z_Z := @mkcst Z Z B_CURRENT_VERBOSITY_CELL Inj_Z_Z 0x13b198 eq_refl.
Add Zify CstOp Op_B_CURRENT_VERBOSITY_CELL.
Definition B_CXA_FINALIZE_PC : Z := 0x8fa18.   (* symbol __cxa_finalize (4 bytes) *)
#[export] Instance Op_B_CXA_FINALIZE_PC : @CstOp Z Z B_CXA_FINALIZE_PC Inj_Z_Z := @mkcst Z Z B_CXA_FINALIZE_PC Inj_Z_Z 0x8fa18 eq_refl.
Add Zify CstOp Op_B_CXA_FINALIZE_PC.
Definition B_DEALLOCATE_PC : Z := 0x34d00.   (* symbol _ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE10DeallocateEPS6_mPv (456 bytes) *)
#[export] Instance Op_B_DEALLOCATE_PC : @CstOp Z Z B_DEALLOCATE_PC Inj_Z_Z := @mkcst Z Z B_DEALLOCATE_PC Inj_Z_Z 0x34d00 eq_refl.
Add Zify CstOp Op_B_DEALLOCATE_PC.
Definition B_DEALLOCATE_PC_OFF_34 : Z := 0x34d34.   (* symbol _ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE10DeallocateEPS6_mPv + 0x34 *)
#[export] Instance Op_B_DEALLOCATE_PC_OFF_34 : @CstOp Z Z B_DEALLOCATE_PC_OFF_34 Inj_Z_Z := @mkcst Z Z B_DEALLOCATE_PC_OFF_34 Inj_Z_Z 0x34d34 eq_refl.
Add Zify CstOp Op_B_DEALLOCATE_PC_OFF_34.
Definition B_DEALLOCATE_PC_OFF_74 : Z := 0x34d74.   (* symbol _ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE10DeallocateEPS6_mPv + 0x74 *)
#[export] Instance Op_B_DEALLOCATE_PC_OFF_74 : @CstOp Z Z B_DEALLOCATE_PC_OFF_74 Inj_Z_Z := @mkcst Z Z B_DEALLOCATE_PC_OFF_74 Inj_Z_Z 0x34d74 eq_refl.
Add Zify CstOp Op_B_DEALLOCATE_PC_OFF_74.
Definition B_DECREASETOTALMMAP_PC : Z := 0x612cc.   (* symbol _ZN11__sanitizer17DecreaseTotalMmapEm (36 bytes) *)
#[export] Instance Op_B_DECREASETOTALMMAP_PC : @CstOp Z Z B_DECREASETOTALMMAP_PC Inj_Z_Z := @mkcst Z Z B_DECREASETOTALMMAP_PC Inj_Z_Z 0x612cc eq_refl.
Add Zify CstOp Op_B_DECREASETOTALMMAP_PC.
Definition B_DEFAULT_STACKSIZE_CELL : Z := 0xa7138.   (* symbol __default_stacksize (4 bytes) *)
#[export] Instance Op_B_DEFAULT_STACKSIZE_CELL : @CstOp Z Z B_DEFAULT_STACKSIZE_CELL Inj_Z_Z := @mkcst Z Z B_DEFAULT_STACKSIZE_CELL Inj_Z_Z 0xa7138 eq_refl.
Add Zify CstOp Op_B_DEFAULT_STACKSIZE_CELL.
Definition B_DISABLEDINTHISTHREAD_PC : Z := 0x80bec.   (* symbol _ZN6__lsan20DisabledInThisThreadEv (24 bytes) *)
#[export] Instance Op_B_DISABLEDINTHISTHREAD_PC : @CstOp Z Z B_DISABLEDINTHISTHREAD_PC Inj_Z_Z := @mkcst Z Z B_DISABLEDINTHISTHREAD_PC Inj_Z_Z 0x80bec eq_refl.
Add Zify CstOp Op_B_DISABLEDINTHISTHREAD_PC.
Definition B_DONTDUMPSHADOWMEMORY_PC : Z := 0x6e848.   (* symbol _ZN11__sanitizer20DontDumpShadowMemoryEmm (32 bytes) *)
#[export] Instance Op_B_DONTDUMPSHADOWMEMORY_PC : @CstOp Z Z B_DONTDUMPSHADOWMEMORY_PC Inj_Z_Z := @mkcst Z Z B_DONTDUMPSHADOWMEMORY_PC Inj_Z_Z 0x6e848 eq_refl.
Add Zify CstOp Op_B_DONTDUMPSHADOWMEMORY_PC.
Definition B_DORECYCLE_QUARANTINECACHE_E_PC : Z := 0x347c4.   (* symbol _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE9DoRecycleEPNS_15QuarantineCacheIS2_EES2_ (312 bytes) *)
#[export] Instance Op_B_DORECYCLE_QUARANTINECACHE_E_PC : @CstOp Z Z B_DORECYCLE_QUARANTINECACHE_E_PC Inj_Z_Z := @mkcst Z Z B_DORECYCLE_QUARANTINECACHE_E_PC Inj_Z_Z 0x347c4 eq_refl.
Add Zify CstOp Op_B_DORECYCLE_QUARANTINECACHE_E_PC.
Definition B_DO_FINI_FINALIZED_CELL : Z := 0xa8090.   (* symbol __do_fini.__finalized (1 bytes) *)
#[export] Instance Op_B_DO_FINI_FINALIZED_CELL : @CstOp Z Z B_DO_FINI_FINALIZED_CELL Inj_Z_Z := @mkcst Z Z B_DO_FINI_FINALIZED_CELL Inj_Z_Z 0xa8090 eq_refl.
Add Zify CstOp Op_B_DO_FINI_FINALIZED_CELL.
Definition B_DO_FINI_PC : Z := 0x3151c.   (* symbol __do_fini (144 bytes) *)
#[export] Instance Op_B_DO_FINI_PC : @CstOp Z Z B_DO_FINI_PC Inj_Z_Z := @mkcst Z Z B_DO_FINI_PC Inj_Z_Z 0x3151c eq_refl.
Add Zify CstOp Op_B_DO_FINI_PC.
Definition B_DO_INIT_INITIALIZED_CELL : Z := 0xa8048.   (* symbol __do_init.__initialized (1 bytes) *)
#[export] Instance Op_B_DO_INIT_INITIALIZED_CELL : @CstOp Z Z B_DO_INIT_INITIALIZED_CELL Inj_Z_Z := @mkcst Z Z B_DO_INIT_INITIALIZED_CELL Inj_Z_Z 0xa8048 eq_refl.
Add Zify CstOp Op_B_DO_INIT_INITIALIZED_CELL.
Definition B_DPRINTF_PC : Z := 0x95478.   (* symbol dprintf (100 bytes) *)
#[export] Instance Op_B_DPRINTF_PC : @CstOp Z Z B_DPRINTF_PC Inj_Z_Z := @mkcst Z Z B_DPRINTF_PC Inj_Z_Z 0x95478 eq_refl.
Add Zify CstOp Op_B_DPRINTF_PC.
Definition B_DRAIN_QUARANTINECACHE_E_PC : Z := 0x342b8.   (* symbol _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE5DrainEPNS_15QuarantineCacheIS2_EES2_ (420 bytes) *)
#[export] Instance Op_B_DRAIN_QUARANTINECACHE_E_PC : @CstOp Z Z B_DRAIN_QUARANTINECACHE_E_PC Inj_Z_Z := @mkcst Z Z B_DRAIN_QUARANTINECACHE_E_PC Inj_Z_Z 0x342b8 eq_refl.
Add Zify CstOp Op_B_DRAIN_QUARANTINECACHE_E_PC.
Definition B_DSO_HANDLE_CELL : Z := 0xa4560.   (* symbol __dso_handle (8 bytes) *)
#[export] Instance Op_B_DSO_HANDLE_CELL : @CstOp Z Z B_DSO_HANDLE_CELL Inj_Z_Z := @mkcst Z Z B_DSO_HANDLE_CELL Inj_Z_Z 0xa4560 eq_refl.
Add Zify CstOp Op_B_DSO_HANDLE_CELL.
Definition B_DTLS_ON_TLS_GET_ADDR_PC : Z := 0x6a73c.   (* symbol _ZN11__sanitizer20DTLS_on_tls_get_addrEPvS0_mm (848 bytes) *)
#[export] Instance Op_B_DTLS_ON_TLS_GET_ADDR_PC : @CstOp Z Z B_DTLS_ON_TLS_GET_ADDR_PC Inj_Z_Z := @mkcst Z Z B_DTLS_ON_TLS_GET_ADDR_PC Inj_Z_Z 0x6a73c eq_refl.
Add Zify CstOp Op_B_DTLS_ON_TLS_GET_ADDR_PC.
Definition B_DUMMY_PC : Z := 0x95198.   (* B place section .text + 0x63944, rekeyed (a) *)
#[export] Instance Op_B_DUMMY_PC : @CstOp Z Z B_DUMMY_PC Inj_Z_Z := @mkcst Z Z B_DUMMY_PC Inj_Z_Z 0x95198 eq_refl.
Add Zify CstOp Op_B_DUMMY_PC.
Definition B_EE3PUTENS_10STACKTRA_PC_OFF_100 : Z := 0x7380c.   (* symbol _ZN11__sanitizer14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE3PutENS_10StackTraceEPb + 0x100 *)
#[export] Instance Op_B_EE3PUTENS_10STACKTRA_PC_OFF_100 : @CstOp Z Z B_EE3PUTENS_10STACKTRA_PC_OFF_100 Inj_Z_Z := @mkcst Z Z B_EE3PUTENS_10STACKTRA_PC_OFF_100 Inj_Z_Z 0x7380c eq_refl.
Add Zify CstOp Op_B_EE3PUTENS_10STACKTRA_PC_OFF_100.
Definition B_EE3PUTENS_10STACKTRA_PC_OFF_120 : Z := 0x7382c.   (* symbol _ZN11__sanitizer14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE3PutENS_10StackTraceEPb + 0x120 *)
#[export] Instance Op_B_EE3PUTENS_10STACKTRA_PC_OFF_120 : @CstOp Z Z B_EE3PUTENS_10STACKTRA_PC_OFF_120 Inj_Z_Z := @mkcst Z Z B_EE3PUTENS_10STACKTRA_PC_OFF_120 Inj_Z_Z 0x7382c eq_refl.
Add Zify CstOp Op_B_EE3PUTENS_10STACKTRA_PC_OFF_120.
Definition B_EE3PUTENS_10STACKTRA_PC_OFF_150 : Z := 0x7385c.   (* symbol _ZN11__sanitizer14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE3PutENS_10StackTraceEPb + 0x150 *)
#[export] Instance Op_B_EE3PUTENS_10STACKTRA_PC_OFF_150 : @CstOp Z Z B_EE3PUTENS_10STACKTRA_PC_OFF_150 Inj_Z_Z := @mkcst Z Z B_EE3PUTENS_10STACKTRA_PC_OFF_150 Inj_Z_Z 0x7385c eq_refl.
Add Zify CstOp Op_B_EE3PUTENS_10STACKTRA_PC_OFF_150.
Definition B_EE3PUTENS_10STACKTRA_PC_OFF_254 : Z := 0x73960.   (* symbol _ZN11__sanitizer14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE3PutENS_10StackTraceEPb + 0x254 *)
#[export] Instance Op_B_EE3PUTENS_10STACKTRA_PC_OFF_254 : @CstOp Z Z B_EE3PUTENS_10STACKTRA_PC_OFF_254 Inj_Z_Z := @mkcst Z Z B_EE3PUTENS_10STACKTRA_PC_OFF_254 Inj_Z_Z 0x73960 eq_refl.
Add Zify CstOp Op_B_EE3PUTENS_10STACKTRA_PC_OFF_254.
Definition B_EE3PUTENS_10STACKTRA_PC_OFF_90 : Z := 0x7379c.   (* symbol _ZN11__sanitizer14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE3PutENS_10StackTraceEPb + 0x90 *)
#[export] Instance Op_B_EE3PUTENS_10STACKTRA_PC_OFF_90 : @CstOp Z Z B_EE3PUTENS_10STACKTRA_PC_OFF_90 Inj_Z_Z := @mkcst Z Z B_EE3PUTENS_10STACKTRA_PC_OFF_90 Inj_Z_Z 0x7379c eq_refl.
Add Zify CstOp Op_B_EE3PUTENS_10STACKTRA_PC_OFF_90.
Definition B_EE4FINDEJNS_10STACKT_PC : Z := 0x73dcc.   (* symbol _ZNK11__sanitizer14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE4findEjNS_10StackTraceEy (180 bytes) *)
#[export] Instance Op_B_EE4FINDEJNS_10STACKT_PC : @CstOp Z Z B_EE4FINDEJNS_10STACKT_PC Inj_Z_Z := @mkcst Z Z B_EE4FINDEJNS_10STACKT_PC Inj_Z_Z 0x73dcc eq_refl.
Add Zify CstOp Op_B_EE4FINDEJNS_10STACKT_PC.
Definition B_EEMB_PC : Z := 0x356e0.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16MaybeReleaseToOSEPNS_12MemoryMapperIS5_EEmb (492 bytes) *)
#[export] Instance Op_B_EEMB_PC : @CstOp Z Z B_EEMB_PC Inj_Z_Z := @mkcst Z Z B_EEMB_PC Inj_Z_Z 0x356e0 eq_refl.
Add Zify CstOp Op_B_EEMB_PC.
Definition B_EEMB_PC_OFF_8C : Z := 0x3576c.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16MaybeReleaseToOSEPNS_12MemoryMapperIS5_EEmb + 0x8c *)
#[export] Instance Op_B_EEMB_PC_OFF_8C : @CstOp Z Z B_EEMB_PC_OFF_8C Inj_Z_Z := @mkcst Z Z B_EEMB_PC_OFF_8C Inj_Z_Z 0x3576c eq_refl.
Add Zify CstOp Op_B_EEMB_PC_OFF_8C.
Definition B_EMIT_PRINTF_PC_OFF_3C : Z := 0x816c0.   (* symbol emit_printf + 0x3c *)
#[export] Instance Op_B_EMIT_PRINTF_PC_OFF_3C : @CstOp Z Z B_EMIT_PRINTF_PC_OFF_3C Inj_Z_Z := @mkcst Z Z B_EMIT_PRINTF_PC_OFF_3C Inj_Z_Z 0x816c0 eq_refl.
Add Zify CstOp Op_B_EMIT_PRINTF_PC_OFF_3C.
Definition B_END_OF_SECTION_ASAN_GLOBALS_CELL : Z := 0xa8020.   (* end of section asan_globals (addr + size) *)
#[export] Instance Op_B_END_OF_SECTION_ASAN_GLOBALS_CELL : @CstOp Z Z B_END_OF_SECTION_ASAN_GLOBALS_CELL Inj_Z_Z := @mkcst Z Z B_END_OF_SECTION_ASAN_GLOBALS_CELL Inj_Z_Z 0xa8020 eq_refl.
Add Zify CstOp Op_B_END_OF_SECTION_ASAN_GLOBALS_CELL.
Definition B_ERRNO_LOCATION_PC : Z := 0x8f828.   (* symbol ___errno_location (12 bytes) *)
#[export] Instance Op_B_ERRNO_LOCATION_PC : @CstOp Z Z B_ERRNO_LOCATION_PC Inj_Z_Z := @mkcst Z Z B_ERRNO_LOCATION_PC Inj_Z_Z 0x8f828 eq_refl.
Add Zify CstOp Op_B_ERRNO_LOCATION_PC.
Definition B_EXIT_EXIT_LOCK_CELL : Z := 0x5fe9a0.   (* symbol exit.exit_lock (4 bytes) *)
#[export] Instance Op_B_EXIT_EXIT_LOCK_CELL : @CstOp Z Z B_EXIT_EXIT_LOCK_CELL Inj_Z_Z := @mkcst Z Z B_EXIT_EXIT_LOCK_CELL Inj_Z_Z 0x5fe9a0 eq_refl.
Add Zify CstOp Op_B_EXIT_EXIT_LOCK_CELL.
Definition B_EXIT_EXIT_LOCK_OFF_4_END_CELL : Z := 0x5fe9a4.   (* symbol exit.exit_lock + 0x4 *)
#[export] Instance Op_B_EXIT_EXIT_LOCK_OFF_4_END_CELL : @CstOp Z Z B_EXIT_EXIT_LOCK_OFF_4_END_CELL Inj_Z_Z := @mkcst Z Z B_EXIT_EXIT_LOCK_OFF_4_END_CELL Inj_Z_Z 0x5fe9a4 eq_refl.
Add Zify CstOp Op_B_EXIT_EXIT_LOCK_OFF_4_END_CELL.
Definition B_EXIT_PC : Z := 0x8fb34.   (* symbol exit (116 bytes) *)
#[export] Instance Op_B_EXIT_PC : @CstOp Z Z B_EXIT_PC Inj_Z_Z := @mkcst Z Z B_EXIT_PC Inj_Z_Z 0x8fb34 eq_refl.
Add Zify CstOp Op_B_EXIT_PC.
Definition B_E_PC_OFF_78 : Z := 0x3483c.   (* symbol _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE9DoRecycleEPNS_15QuarantineCacheIS2_EES2_ + 0x78 *)
#[export] Instance Op_B_E_PC_OFF_78 : @CstOp Z Z B_E_PC_OFF_78 Inj_Z_Z := @mkcst Z Z B_E_PC_OFF_78 Inj_Z_Z 0x3483c eq_refl.
Add Zify CstOp Op_B_E_PC_OFF_78.
Definition B_E_PC_OFF_C0 : Z := 0x34378.   (* symbol _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE5DrainEPNS_15QuarantineCacheIS2_EES2_ + 0xc0 *)
#[export] Instance Op_B_E_PC_OFF_C0 : @CstOp Z Z B_E_PC_OFF_C0 Inj_Z_Z := @mkcst Z Z B_E_PC_OFF_C0 Inj_Z_Z 0x34378 eq_refl.
Add Zify CstOp Op_B_E_PC_OFF_C0.
Definition B_E_PC_OFF_C4 : Z := 0x34888.   (* symbol _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE9DoRecycleEPNS_15QuarantineCacheIS2_EES2_ + 0xc4 *)
#[export] Instance Op_B_E_PC_OFF_C4 : @CstOp Z Z B_E_PC_OFF_C4 Inj_Z_Z := @mkcst Z Z B_E_PC_OFF_C4 Inj_Z_Z 0x34888 eq_refl.
Add Zify CstOp Op_B_E_PC_OFF_C4.
Definition B_E_PC_OFF_F0 : Z := 0x348b4.   (* symbol _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE9DoRecycleEPNS_15QuarantineCacheIS2_EES2_ + 0xf0 *)
#[export] Instance Op_B_E_PC_OFF_F0 : @CstOp Z Z B_E_PC_OFF_F0 Inj_Z_Z := @mkcst Z Z B_E_PC_OFF_F0 Inj_Z_Z 0x348b4 eq_refl.
Add Zify CstOp Op_B_E_PC_OFF_F0.
Definition B_E_PC_OFF_FC : Z := 0x348c0.   (* symbol _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE9DoRecycleEPNS_15QuarantineCacheIS2_EES2_ + 0xfc *)
#[export] Instance Op_B_E_PC_OFF_FC : @CstOp Z Z B_E_PC_OFF_FC Inj_Z_Z := @mkcst Z Z B_E_PC_OFF_FC Inj_Z_Z 0x348c0 eq_refl.
Add Zify CstOp Op_B_E_PC_OFF_FC.
Definition B_FFLUSH_PC : Z := 0x95638.   (* symbol fflush (368 bytes) *)
#[export] Instance Op_B_FFLUSH_PC : @CstOp Z Z B_FFLUSH_PC Inj_Z_Z := @mkcst Z Z B_FFLUSH_PC Inj_Z_Z 0x95638 eq_refl.
Add Zify CstOp Op_B_FFLUSH_PC.
Definition B_FFLUSH_PC_OFF_120 : Z := 0x95758.   (* symbol fflush + 0x120 *)
#[export] Instance Op_B_FFLUSH_PC_OFF_120 : @CstOp Z Z B_FFLUSH_PC_OFF_120 Inj_Z_Z := @mkcst Z Z B_FFLUSH_PC_OFF_120 Inj_Z_Z 0x95758 eq_refl.
Add Zify CstOp Op_B_FFLUSH_PC_OFF_120.
Definition B_FINISHED_ATEXIT_CELL : Z := 0x5fe780.   (* symbol finished_atexit (1 bytes) *)
#[export] Instance Op_B_FINISHED_ATEXIT_CELL : @CstOp Z Z B_FINISHED_ATEXIT_CELL Inj_Z_Z := @mkcst Z Z B_FINISHED_ATEXIT_CELL Inj_Z_Z 0x5fe780 eq_refl.
Add Zify CstOp Op_B_FINISHED_ATEXIT_CELL.
Definition B_FINI_ARRAY_0X0 : Z := 0xa2260.   (* start of section .fini_array *)
#[export] Instance Op_B_FINI_ARRAY_0X0 : @CstOp Z Z B_FINI_ARRAY_0X0 Inj_Z_Z := @mkcst Z Z B_FINI_ARRAY_0X0 Inj_Z_Z 0xa2260 eq_refl.
Add Zify CstOp Op_B_FINI_ARRAY_0X0.
Definition B_FINI_CELL : Z := 0xa2268.   (* symbol __fini (8 bytes) *)
#[export] Instance Op_B_FINI_CELL : @CstOp Z Z B_FINI_CELL Inj_Z_Z := @mkcst Z Z B_FINI_CELL Inj_Z_Z 0xa2268 eq_refl.
Add Zify CstOp Op_B_FINI_CELL.
Definition B_FLAGHANDLER_CELL : Z := 0xa2280.   (* symbol _ZTVN11__sanitizer11FlagHandlerIiEE (32 bytes) *)
#[export] Instance Op_B_FLAGHANDLER_CELL : @CstOp Z Z B_FLAGHANDLER_CELL Inj_Z_Z := @mkcst Z Z B_FLAGHANDLER_CELL Inj_Z_Z 0xa2280 eq_refl.
Add Zify CstOp Op_B_FLAGHANDLER_CELL.
Definition B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC : Z := 0x5352c.   (* symbol _ZN6__asan29FlushUnneededASanShadowMemoryEmm (76 bytes) *)
#[export] Instance Op_B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC : @CstOp Z Z B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC Inj_Z_Z := @mkcst Z Z B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC Inj_Z_Z 0x5352c eq_refl.
Add Zify CstOp Op_B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC.
Definition B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC_OFF_20 : Z := 0x5354c.   (* symbol _ZN6__asan29FlushUnneededASanShadowMemoryEmm + 0x20 *)
#[export] Instance Op_B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC_OFF_20 : @CstOp Z Z B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC_OFF_20 Inj_Z_Z := @mkcst Z Z B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC_OFF_20 Inj_Z_Z 0x5354c eq_refl.
Add Zify CstOp Op_B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC_OFF_20.
Definition B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC_OFF_2C : Z := 0x53558.   (* symbol _ZN6__asan29FlushUnneededASanShadowMemoryEmm + 0x2c *)
#[export] Instance Op_B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC_OFF_2C : @CstOp Z Z B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC_OFF_2C Inj_Z_Z := @mkcst Z Z B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC_OFF_2C Inj_Z_Z 0x53558 eq_refl.
Add Zify CstOp Op_B_FLUSHUNNEEDEDASANSHADOWMEMORY_PC_OFF_2C.
Definition B_FORMAT_GET_VALUE_SIZE_PC : Z := 0x48950.   (* symbol _ZL21format_get_value_sizecPKcb (408 bytes) *)
#[export] Instance Op_B_FORMAT_GET_VALUE_SIZE_PC : @CstOp Z Z B_FORMAT_GET_VALUE_SIZE_PC Inj_Z_Z := @mkcst Z Z B_FORMAT_GET_VALUE_SIZE_PC Inj_Z_Z 0x48950 eq_refl.
Add Zify CstOp Op_B_FORMAT_GET_VALUE_SIZE_PC.
Definition B_FUNCS_CELL : Z := 0x5ff688.   (* symbol funcs (8 bytes) *)
#[export] Instance Op_B_FUNCS_CELL : @CstOp Z Z B_FUNCS_CELL Inj_Z_Z := @mkcst Z Z B_FUNCS_CELL Inj_Z_Z 0x5ff688 eq_refl.
Add Zify CstOp Op_B_FUNCS_CELL.
Definition B_FUNCS_ON_EXIT_PC_OFF_80 : Z := 0x8f9d0.   (* symbol __funcs_on_exit + 0x80 *)
#[export] Instance Op_B_FUNCS_ON_EXIT_PC_OFF_80 : @CstOp Z Z B_FUNCS_ON_EXIT_PC_OFF_80 Inj_Z_Z := @mkcst Z Z B_FUNCS_ON_EXIT_PC_OFF_80 Inj_Z_Z 0x8f9d0 eq_refl.
Add Zify CstOp Op_B_FUNCS_ON_EXIT_PC_OFF_80.
Definition B_FWRITEX_PC_OFF_104 : Z := 0x95b70.   (* symbol __fwritex + 0x104 *)
#[export] Instance Op_B_FWRITEX_PC_OFF_104 : @CstOp Z Z B_FWRITEX_PC_OFF_104 Inj_Z_Z := @mkcst Z Z B_FWRITEX_PC_OFF_104 Inj_Z_Z 0x95b70 eq_refl.
Add Zify CstOp Op_B_FWRITEX_PC_OFF_104.
Definition B_FWRITEX_PC_OFF_3C : Z := 0x95aa8.   (* symbol __fwritex + 0x3c *)
#[export] Instance Op_B_FWRITEX_PC_OFF_3C : @CstOp Z Z B_FWRITEX_PC_OFF_3C Inj_Z_Z := @mkcst Z Z B_FWRITEX_PC_OFF_3C Inj_Z_Z 0x95aa8 eq_refl.
Add Zify CstOp Op_B_FWRITEX_PC_OFF_3C.
Definition B_FWRITE_PC : Z := 0x95ba4.   (* symbol fwrite (184 bytes) *)
#[export] Instance Op_B_FWRITE_PC : @CstOp Z Z B_FWRITE_PC Inj_Z_Z := @mkcst Z Z B_FWRITE_PC Inj_Z_Z 0x95ba4 eq_refl.
Add Zify CstOp Op_B_FWRITE_PC.
Definition B_FWRITE_PC_OFF_88 : Z := 0x95c2c.   (* symbol fwrite + 0x88 *)
#[export] Instance Op_B_FWRITE_PC_OFF_88 : @CstOp Z Z B_FWRITE_PC_OFF_88 Inj_Z_Z := @mkcst Z Z B_FWRITE_PC_OFF_88 Inj_Z_Z 0x95c2c eq_refl.
Add Zify CstOp Op_B_FWRITE_PC_OFF_88.
Definition B_FWRITE_PC_OFF_B4 : Z := 0x95c58.   (* symbol fwrite + 0xb4 *)
#[export] Instance Op_B_FWRITE_PC_OFF_B4 : @CstOp Z Z B_FWRITE_PC_OFF_B4 Inj_Z_Z := @mkcst Z Z B_FWRITE_PC_OFF_B4 Inj_Z_Z 0x95c58 eq_refl.
Add Zify CstOp Op_B_FWRITE_PC_OFF_B4.
Definition B_GETBLOCKBEGIN_PC_OFF_6C : Z := 0x34bec.   (* symbol _ZNK11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE13GetBlockBeginEPKv + 0x6c *)
#[export] Instance Op_B_GETBLOCKBEGIN_PC_OFF_6C : @CstOp Z Z B_GETBLOCKBEGIN_PC_OFF_6C Inj_Z_Z := @mkcst Z Z B_GETBLOCKBEGIN_PC_OFF_6C Inj_Z_Z 0x34bec eq_refl.
Add Zify CstOp Op_B_GETBLOCKBEGIN_PC_OFF_6C.
Definition B_GETBLOCKBEGIN_PC_OFF_98 : Z := 0x34c18.   (* symbol _ZNK11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE13GetBlockBeginEPKv + 0x98 *)
#[export] Instance Op_B_GETBLOCKBEGIN_PC_OFF_98 : @CstOp Z Z B_GETBLOCKBEGIN_PC_OFF_98 Inj_Z_Z := @mkcst Z Z B_GETBLOCKBEGIN_PC_OFF_98 Inj_Z_Z 0x34c18 eq_refl.
Add Zify CstOp Op_B_GETBLOCKBEGIN_PC_OFF_98.
Definition B_GETCURRENTPC_PC : Z := 0x74070.   (* symbol _ZN11__sanitizer10StackTrace12GetCurrentPcEv (8 bytes) *)
#[export] Instance Op_B_GETCURRENTPC_PC : @CstOp Z Z B_GETCURRENTPC_PC Inj_Z_Z := @mkcst Z Z B_GETCURRENTPC_PC Inj_Z_Z 0x74070 eq_refl.
Add Zify CstOp Op_B_GETCURRENTPC_PC.
Definition B_GETCURRENTTHREADSTATS_PC : Z := 0x5c1f4.   (* symbol _ZN6__asan21GetCurrentThreadStatsEv (56 bytes) *)
#[export] Instance Op_B_GETCURRENTTHREADSTATS_PC : @CstOp Z Z B_GETCURRENTTHREADSTATS_PC Inj_Z_Z := @mkcst Z Z B_GETCURRENTTHREADSTATS_PC Inj_Z_Z 0x5c1f4 eq_refl.
Add Zify CstOp Op_B_GETCURRENTTHREADSTATS_PC.
Definition B_GETCURRENTTHREAD_PC : Z := 0x5d028.   (* symbol _ZN6__asan16GetCurrentThreadEv (32 bytes) *)
#[export] Instance Op_B_GETCURRENTTHREAD_PC : @CstOp Z Z B_GETCURRENTTHREAD_PC Inj_Z_Z := @mkcst Z Z B_GETCURRENTTHREAD_PC Inj_Z_Z 0x5d028 eq_refl.
Add Zify CstOp Op_B_GETCURRENTTHREAD_PC.
Definition B_GETMALLOCCONTEXTSIZE_PC : Z := 0x5b5b0.   (* symbol _ZN6__asan20GetMallocContextSizeEv (16 bytes) *)
#[export] Instance Op_B_GETMALLOCCONTEXTSIZE_PC : @CstOp Z Z B_GETMALLOCCONTEXTSIZE_PC Inj_Z_Z := @mkcst Z Z B_GETMALLOCCONTEXTSIZE_PC Inj_Z_Z 0x5b5b0 eq_refl.
Add Zify CstOp Op_B_GETMALLOCCONTEXTSIZE_PC.
Definition B_GETMMAPGRANULARITY_PC : Z := 0x66a64.   (* symbol _ZN11__sanitizer18GetMmapGranularityEv (4 bytes) *)
#[export] Instance Op_B_GETMMAPGRANULARITY_PC : @CstOp Z Z B_GETMMAPGRANULARITY_PC Inj_Z_Z := @mkcst Z Z B_GETMMAPGRANULARITY_PC Inj_Z_Z 0x66a64 eq_refl.
Add Zify CstOp Op_B_GETMMAPGRANULARITY_PC.
Definition B_GETNAMEDMAPPINGFD_PC : Z := 0x67750.   (* symbol _ZN11__sanitizer17GetNamedMappingFdEPKcmPi (524 bytes) *)
#[export] Instance Op_B_GETNAMEDMAPPINGFD_PC : @CstOp Z Z B_GETNAMEDMAPPINGFD_PC Inj_Z_Z := @mkcst Z Z B_GETNAMEDMAPPINGFD_PC Inj_Z_Z 0x67750 eq_refl.
Add Zify CstOp Op_B_GETNAMEDMAPPINGFD_PC.
Definition B_GETPAGESIZE_PC : Z := 0x662d0.   (* symbol _ZN11__sanitizer11GetPageSizeEv (8 bytes) *)
#[export] Instance Op_B_GETPAGESIZE_PC : @CstOp Z Z B_GETPAGESIZE_PC Inj_Z_Z := @mkcst Z Z B_GETPAGESIZE_PC Inj_Z_Z 0x662d0 eq_refl.
Add Zify CstOp Op_B_GETPAGESIZE_PC.
Definition B_GOT_0X30 : Z := 0xa2820.   (* B place section .got + 0x30, rekeyed (b) *)
#[export] Instance Op_B_GOT_0X30 : @CstOp Z Z B_GOT_0X30 Inj_Z_Z := @mkcst Z Z B_GOT_0X30 Inj_Z_Z 0xa2820 eq_refl.
Add Zify CstOp Op_B_GOT_0X30.
Definition B_GOT_0X38 : Z := 0xa2828.   (* B place section .got + 0x38, rekeyed (b) *)
#[export] Instance Op_B_GOT_0X38 : @CstOp Z Z B_GOT_0X38 Inj_Z_Z := @mkcst Z Z B_GOT_0X38 Inj_Z_Z 0xa2828 eq_refl.
Add Zify CstOp Op_B_GOT_0X38.
Definition B_GOT_0X40 : Z := 0xa2830.   (* B place section .got + 0x40, rekeyed (b) *)
#[export] Instance Op_B_GOT_0X40 : @CstOp Z Z B_GOT_0X40 Inj_Z_Z := @mkcst Z Z B_GOT_0X40 Inj_Z_Z 0xa2830 eq_refl.
Add Zify CstOp Op_B_GOT_0X40.
Definition B_GOT_0X48 : Z := 0xa2838.   (* B place section .got + 0x48, rekeyed (b) *)
#[export] Instance Op_B_GOT_0X48 : @CstOp Z Z B_GOT_0X48 Inj_Z_Z := @mkcst Z Z B_GOT_0X48 Inj_Z_Z 0xa2838 eq_refl.
Add Zify CstOp Op_B_GOT_0X48.
Definition B_GOT_0X50 : Z := 0xa2840.   (* B place section .got + 0x50, rekeyed (b) *)
#[export] Instance Op_B_GOT_0X50 : @CstOp Z Z B_GOT_0X50 Inj_Z_Z := @mkcst Z Z B_GOT_0X50 Inj_Z_Z 0xa2840 eq_refl.
Add Zify CstOp Op_B_GOT_0X50.
Definition B_GOT_0X58 : Z := 0xa2848.   (* B place section .got + 0x58, rekeyed (b) *)
#[export] Instance Op_B_GOT_0X58 : @CstOp Z Z B_GOT_0X58 Inj_Z_Z := @mkcst Z Z B_GOT_0X58 Inj_Z_Z 0xa2848 eq_refl.
Add Zify CstOp Op_B_GOT_0X58.
Definition B_GOT_0X60 : Z := 0xa2850.   (* B place section .got + 0x60, rekeyed (b) *)
#[export] Instance Op_B_GOT_0X60 : @CstOp Z Z B_GOT_0X60 Inj_Z_Z := @mkcst Z Z B_GOT_0X60 Inj_Z_Z 0xa2850 eq_refl.
Add Zify CstOp Op_B_GOT_0X60.
Definition B_GOT_0X68 : Z := 0xa2858.   (* B place section .got + 0x68, rekeyed (b) *)
#[export] Instance Op_B_GOT_0X68 : @CstOp Z Z B_GOT_0X68 Inj_Z_Z := @mkcst Z Z B_GOT_0X68 Inj_Z_Z 0xa2858 eq_refl.
Add Zify CstOp Op_B_GOT_0X68.
Definition B_GOT_0X70 : Z := 0xa2860.   (* B place section .got + 0x70, rekeyed (b) *)
#[export] Instance Op_B_GOT_0X70 : @CstOp Z Z B_GOT_0X70 Inj_Z_Z := @mkcst Z Z B_GOT_0X70 Inj_Z_Z 0xa2860 eq_refl.
Add Zify CstOp Op_B_GOT_0X70.
Definition B_GOT_0X78 : Z := 0xa2868.   (* B place section .got + 0x78, rekeyed (b) *)
#[export] Instance Op_B_GOT_0X78 : @CstOp Z Z B_GOT_0X78 Inj_Z_Z := @mkcst Z Z B_GOT_0X78 Inj_Z_Z 0xa2868 eq_refl.
Add Zify CstOp Op_B_GOT_0X78.
Definition B_GOT_0X80 : Z := 0xa2870.   (* B place section .got + 0x80, rekeyed (b) *)
#[export] Instance Op_B_GOT_0X80 : @CstOp Z Z B_GOT_0X80 Inj_Z_Z := @mkcst Z Z B_GOT_0X80 Inj_Z_Z 0xa2870 eq_refl.
Add Zify CstOp Op_B_GOT_0X80.
Definition B_GOT_0XA0 : Z := 0xa2890.   (* B place section .got + 0xa0, rekeyed (b) *)
#[export] Instance Op_B_GOT_0XA0 : @CstOp Z Z B_GOT_0XA0 Inj_Z_Z := @mkcst Z Z B_GOT_0XA0 Inj_Z_Z 0xa2890 eq_refl.
Add Zify CstOp Op_B_GOT_0XA0.
Definition B_GOT_0XA8 : Z := 0xa2898.   (* B place section .got + 0xa8, rekeyed (b) *)
#[export] Instance Op_B_GOT_0XA8 : @CstOp Z Z B_GOT_0XA8 Inj_Z_Z := @mkcst Z Z B_GOT_0XA8 Inj_Z_Z 0xa2898 eq_refl.
Add Zify CstOp Op_B_GOT_0XA8.
Definition B_GOT_0XB0 : Z := 0xa28a0.   (* B place section .got + 0xb0, rekeyed (b) *)
#[export] Instance Op_B_GOT_0XB0 : @CstOp Z Z B_GOT_0XB0 Inj_Z_Z := @mkcst Z Z B_GOT_0XB0 Inj_Z_Z 0xa28a0 eq_refl.
Add Zify CstOp Op_B_GOT_0XB0.
Definition B_GOT_0XB8 : Z := 0xa28a8.   (* B place section .got + 0xb8, rekeyed (b) *)
#[export] Instance Op_B_GOT_0XB8 : @CstOp Z Z B_GOT_0XB8 Inj_Z_Z := @mkcst Z Z B_GOT_0XB8 Inj_Z_Z 0xa28a8 eq_refl.
Add Zify CstOp Op_B_GOT_0XB8.
Definition B_GOT_0XBC8 : Z := 0xa33b8.   (* B place section .got + 0xbc8, rekeyed (b) *)
#[export] Instance Op_B_GOT_0XBC8 : @CstOp Z Z B_GOT_0XBC8 Inj_Z_Z := @mkcst Z Z B_GOT_0XBC8 Inj_Z_Z 0xa33b8 eq_refl.
Add Zify CstOp Op_B_GOT_0XBC8.
Definition B_GOT_0XC0 : Z := 0xa28b0.   (* B place section .got + 0xc0, rekeyed (b) *)
#[export] Instance Op_B_GOT_0XC0 : @CstOp Z Z B_GOT_0XC0 Inj_Z_Z := @mkcst Z Z B_GOT_0XC0 Inj_Z_Z 0xa28b0 eq_refl.
Add Zify CstOp Op_B_GOT_0XC0.
Definition B_GOT_0XCB8 : Z := 0xa34a8.   (* B place section .got + 0xcb8, rekeyed (b) *)
#[export] Instance Op_B_GOT_0XCB8 : @CstOp Z Z B_GOT_0XCB8 Inj_Z_Z := @mkcst Z Z B_GOT_0XCB8 Inj_Z_Z 0xa34a8 eq_refl.
Add Zify CstOp Op_B_GOT_0XCB8.
Definition B_GOT_0XCE8 : Z := 0xa34d8.   (* B place section .got + 0xce8, rekeyed (b) *)
#[export] Instance Op_B_GOT_0XCE8 : @CstOp Z Z B_GOT_0XCE8 Inj_Z_Z := @mkcst Z Z B_GOT_0XCE8 Inj_Z_Z 0xa34d8 eq_refl.
Add Zify CstOp Op_B_GOT_0XCE8.
Definition B_GOT_0XD18 : Z := 0xa3508.   (* B place section .got + 0xd18, rekeyed (b) *)
#[export] Instance Op_B_GOT_0XD18 : @CstOp Z Z B_GOT_0XD18 Inj_Z_Z := @mkcst Z Z B_GOT_0XD18 Inj_Z_Z 0xa3508 eq_refl.
Add Zify CstOp Op_B_GOT_0XD18.
Definition B_GOT_0XD20 : Z := 0xa3510.   (* B place section .got + 0xd20, rekeyed (b) *)
#[export] Instance Op_B_GOT_0XD20 : @CstOp Z Z B_GOT_0XD20 Inj_Z_Z := @mkcst Z Z B_GOT_0XD20 Inj_Z_Z 0xa3510 eq_refl.
Add Zify CstOp Op_B_GOT_0XD20.
Definition B_GOT_0XD28 : Z := 0xa3518.   (* B place section .got + 0xd28, rekeyed (b) *)
#[export] Instance Op_B_GOT_0XD28 : @CstOp Z Z B_GOT_0XD28 Inj_Z_Z := @mkcst Z Z B_GOT_0XD28 Inj_Z_Z 0xa3518 eq_refl.
Add Zify CstOp Op_B_GOT_0XD28.
Definition B_GOT_0XD40 : Z := 0xa3530.   (* B place section .got + 0xd40, rekeyed (b) *)
#[export] Instance Op_B_GOT_0XD40 : @CstOp Z Z B_GOT_0XD40 Inj_Z_Z := @mkcst Z Z B_GOT_0XD40 Inj_Z_Z 0xa3530 eq_refl.
Add Zify CstOp Op_B_GOT_0XD40.
Definition B_GOT_0XD50 : Z := 0xa3540.   (* B place section .got + 0xd50, rekeyed (b) *)
#[export] Instance Op_B_GOT_0XD50 : @CstOp Z Z B_GOT_0XD50 Inj_Z_Z := @mkcst Z Z B_GOT_0XD50 Inj_Z_Z 0xa3540 eq_refl.
Add Zify CstOp Op_B_GOT_0XD50.
Definition B_GOT_HI : Z := 0xa3548.   (* end of section .got (addr + size) *)
#[export] Instance Op_B_GOT_HI : @CstOp Z Z B_GOT_HI Inj_Z_Z := @mkcst Z Z B_GOT_HI Inj_Z_Z 0xa3548 eq_refl.
Add Zify CstOp Op_B_GOT_HI.
Definition B_GOT_OFF_30_VAL : Z := 0x8fa18.   (* the 8 bytes at B place section .got + 0x30, rekeyed (b) *)
#[export] Instance Op_B_GOT_OFF_30_VAL : @CstOp Z Z B_GOT_OFF_30_VAL Inj_Z_Z := @mkcst Z Z B_GOT_OFF_30_VAL Inj_Z_Z 0x8fa18 eq_refl.
Add Zify CstOp Op_B_GOT_OFF_30_VAL.
Definition B_GOT_OFF_40_VAL : Z := 0x13b1a0.   (* the 8 bytes at B place section .got + 0x40, rekeyed (b) *)
#[export] Instance Op_B_GOT_OFF_40_VAL : @CstOp Z Z B_GOT_OFF_40_VAL Inj_Z_Z := @mkcst Z Z B_GOT_OFF_40_VAL Inj_Z_Z 0x13b1a0 eq_refl.
Add Zify CstOp Op_B_GOT_OFF_40_VAL.
Definition B_GOT_OFF_48_VAL : Z := 0xa4708.   (* the 8 bytes at B place section .got + 0x48, rekeyed (b) *)
#[export] Instance Op_B_GOT_OFF_48_VAL : @CstOp Z Z B_GOT_OFF_48_VAL Inj_Z_Z := @mkcst Z Z B_GOT_OFF_48_VAL Inj_Z_Z 0xa4708 eq_refl.
Add Zify CstOp Op_B_GOT_OFF_48_VAL.
Definition B_GOT_OFF_50_VAL : Z := 0x13d228.   (* the 8 bytes at B place section .got + 0x50, rekeyed (b) *)
#[export] Instance Op_B_GOT_OFF_50_VAL : @CstOp Z Z B_GOT_OFF_50_VAL Inj_Z_Z := @mkcst Z Z B_GOT_OFF_50_VAL Inj_Z_Z 0x13d228 eq_refl.
Add Zify CstOp Op_B_GOT_OFF_50_VAL.
Definition B_GOT_OFF_58_VAL : Z := 0xa8ef8.   (* the 8 bytes at B place section .got + 0x58, rekeyed (b) *)
#[export] Instance Op_B_GOT_OFF_58_VAL : @CstOp Z Z B_GOT_OFF_58_VAL Inj_Z_Z := @mkcst Z Z B_GOT_OFF_58_VAL Inj_Z_Z 0xa8ef8 eq_refl.
Add Zify CstOp Op_B_GOT_OFF_58_VAL.
Definition B_GOT_OFF_60_VAL : Z := 0xab6f8.   (* the 8 bytes at B place section .got + 0x60, rekeyed (b) *)
#[export] Instance Op_B_GOT_OFF_60_VAL : @CstOp Z Z B_GOT_OFF_60_VAL Inj_Z_Z := @mkcst Z Z B_GOT_OFF_60_VAL Inj_Z_Z 0xab6f8 eq_refl.
Add Zify CstOp Op_B_GOT_OFF_60_VAL.
Definition B_GOT_OFF_68_VAL : Z := 0xac3e8.   (* the 8 bytes at B place section .got + 0x68, rekeyed (b) *)
#[export] Instance Op_B_GOT_OFF_68_VAL : @CstOp Z Z B_GOT_OFF_68_VAL Inj_Z_Z := @mkcst Z Z B_GOT_OFF_68_VAL Inj_Z_Z 0xac3e8 eq_refl.
Add Zify CstOp Op_B_GOT_OFF_68_VAL.
Definition B_GOT_OFF_70_VAL : Z := 0xac3f0.   (* the 8 bytes at B place section .got + 0x70, rekeyed (b) *)
#[export] Instance Op_B_GOT_OFF_70_VAL : @CstOp Z Z B_GOT_OFF_70_VAL Inj_Z_Z := @mkcst Z Z B_GOT_OFF_70_VAL Inj_Z_Z 0xac3f0 eq_refl.
Add Zify CstOp Op_B_GOT_OFF_70_VAL.
Definition B_GOT_OFF_78_VAL : Z := 0xac3e0.   (* the 8 bytes at B place section .got + 0x78, rekeyed (b) *)
#[export] Instance Op_B_GOT_OFF_78_VAL : @CstOp Z Z B_GOT_OFF_78_VAL Inj_Z_Z := @mkcst Z Z B_GOT_OFF_78_VAL Inj_Z_Z 0xac3e0 eq_refl.
Add Zify CstOp Op_B_GOT_OFF_78_VAL.
Definition B_GOT_OFF_80_VAL : Z := 0xa46d0.   (* the 8 bytes at B place section .got + 0x80, rekeyed (b) *)
#[export] Instance Op_B_GOT_OFF_80_VAL : @CstOp Z Z B_GOT_OFF_80_VAL Inj_Z_Z := @mkcst Z Z B_GOT_OFF_80_VAL Inj_Z_Z 0xa46d0 eq_refl.
Add Zify CstOp Op_B_GOT_OFF_80_VAL.
Definition B_GOT_OFF_A8_VAL : Z := 0x13d21c.   (* the 8 bytes at B place section .got + 0xa8, rekeyed (b) *)
#[export] Instance Op_B_GOT_OFF_A8_VAL : @CstOp Z Z B_GOT_OFF_A8_VAL Inj_Z_Z := @mkcst Z Z B_GOT_OFF_A8_VAL Inj_Z_Z 0x13d21c eq_refl.
Add Zify CstOp Op_B_GOT_OFF_A8_VAL.
Definition B_HEAD_CELL : Z := 0x5fe790.   (* symbol head (8 bytes) *)
#[export] Instance Op_B_HEAD_CELL : @CstOp Z Z B_HEAD_CELL Inj_Z_Z := @mkcst Z Z B_HEAD_CELL Inj_Z_Z 0x5fe790 eq_refl.
Add Zify CstOp Op_B_HEAD_CELL.
Definition B_INCREASETOTALMMAP_PC : Z := 0x61288.   (* symbol _ZN11__sanitizer17IncreaseTotalMmapEm (68 bytes) *)
#[export] Instance Op_B_INCREASETOTALMMAP_PC : @CstOp Z Z B_INCREASETOTALMMAP_PC Inj_Z_Z := @mkcst Z Z B_INCREASETOTALMMAP_PC Inj_Z_Z 0x61288 eq_refl.
Add Zify CstOp Op_B_INCREASETOTALMMAP_PC.
Definition B_INSTANCE_CELL : Z := 0xa8098.   (* symbol _ZN6__asanL8instanceE (3632 bytes) *)
#[export] Instance Op_B_INSTANCE_CELL : @CstOp Z Z B_INSTANCE_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_CELL Inj_Z_Z 0xa8098 eq_refl.
Add Zify CstOp Op_B_INSTANCE_CELL.
Definition B_INSTANCE_OFF_20_CELL : Z := 0xa80b8.   (* symbol _ZN6__asanL8instanceE + 0x20 *)
#[export] Instance Op_B_INSTANCE_OFF_20_CELL : @CstOp Z Z B_INSTANCE_OFF_20_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_20_CELL Inj_Z_Z 0xa80b8 eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_20_CELL.
Definition B_INSTANCE_OFF_28_CELL : Z := 0xa80c0.   (* symbol _ZN6__asanL8instanceE + 0x28 *)
#[export] Instance Op_B_INSTANCE_OFF_28_CELL : @CstOp Z Z B_INSTANCE_OFF_28_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_28_CELL Inj_Z_Z 0xa80c0 eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_28_CELL.
Definition B_INSTANCE_OFF_2A9_CELL : Z := 0xa8341.   (* symbol _ZN6__asanL8instanceE + 0x2a9 *)
#[export] Instance Op_B_INSTANCE_OFF_2A9_CELL : @CstOp Z Z B_INSTANCE_OFF_2A9_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_2A9_CELL Inj_Z_Z 0xa8341 eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_2A9_CELL.
Definition B_INSTANCE_OFF_2AA_CELL : Z := 0xa8342.   (* symbol _ZN6__asanL8instanceE + 0x2aa *)
#[export] Instance Op_B_INSTANCE_OFF_2AA_CELL : @CstOp Z Z B_INSTANCE_OFF_2AA_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_2AA_CELL Inj_Z_Z 0xa8342 eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_2AA_CELL.
Definition B_INSTANCE_OFF_2B0_CELL : Z := 0xa8348.   (* symbol _ZN6__asanL8instanceE + 0x2b0 *)
#[export] Instance Op_B_INSTANCE_OFF_2B0_CELL : @CstOp Z Z B_INSTANCE_OFF_2B0_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_2B0_CELL Inj_Z_Z 0xa8348 eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_2B0_CELL.
Definition B_INSTANCE_OFF_2C0_CELL : Z := 0xa8358.   (* symbol _ZN6__asanL8instanceE + 0x2c0 *)
#[export] Instance Op_B_INSTANCE_OFF_2C0_CELL : @CstOp Z Z B_INSTANCE_OFF_2C0_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_2C0_CELL Inj_Z_Z 0xa8358 eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_2C0_CELL.
Definition B_INSTANCE_OFF_2C8_CELL : Z := 0xa8360.   (* symbol _ZN6__asanL8instanceE + 0x2c8 *)
#[export] Instance Op_B_INSTANCE_OFF_2C8_CELL : @CstOp Z Z B_INSTANCE_OFF_2C8_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_2C8_CELL Inj_Z_Z 0xa8360 eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_2C8_CELL.
Definition B_INSTANCE_OFF_2D8_CELL : Z := 0xa8370.   (* symbol _ZN6__asanL8instanceE + 0x2d8 *)
#[export] Instance Op_B_INSTANCE_OFF_2D8_CELL : @CstOp Z Z B_INSTANCE_OFF_2D8_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_2D8_CELL Inj_Z_Z 0xa8370 eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_2D8_CELL.
Definition B_INSTANCE_OFF_30_CELL : Z := 0xa80c8.   (* symbol _ZN6__asanL8instanceE + 0x30 *)
#[export] Instance Op_B_INSTANCE_OFF_30_CELL : @CstOp Z Z B_INSTANCE_OFF_30_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_30_CELL Inj_Z_Z 0xa80c8 eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_30_CELL.
Definition B_INSTANCE_OFF_318_CELL : Z := 0xa83b0.   (* symbol _ZN6__asanL8instanceE + 0x318 *)
#[export] Instance Op_B_INSTANCE_OFF_318_CELL : @CstOp Z Z B_INSTANCE_OFF_318_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_318_CELL Inj_Z_Z 0xa83b0 eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_318_CELL.
Definition B_INSTANCE_OFF_328_CELL : Z := 0xa83c0.   (* symbol _ZN6__asanL8instanceE + 0x328 *)
#[export] Instance Op_B_INSTANCE_OFF_328_CELL : @CstOp Z Z B_INSTANCE_OFF_328_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_328_CELL Inj_Z_Z 0xa83c0 eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_328_CELL.
Definition B_INSTANCE_OFF_372_CELL : Z := 0xa840a.   (* symbol _ZN6__asanL8instanceE + 0x372 *)
#[export] Instance Op_B_INSTANCE_OFF_372_CELL : @CstOp Z Z B_INSTANCE_OFF_372_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_372_CELL Inj_Z_Z 0xa840a eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_372_CELL.
Definition B_INSTANCE_OFF_374_CELL : Z := 0xa840c.   (* symbol _ZN6__asanL8instanceE + 0x374 *)
#[export] Instance Op_B_INSTANCE_OFF_374_CELL : @CstOp Z Z B_INSTANCE_OFF_374_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_374_CELL Inj_Z_Z 0xa840c eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_374_CELL.
Definition B_INSTANCE_OFF_38_CELL : Z := 0xa80d0.   (* symbol _ZN6__asanL8instanceE + 0x38 *)
#[export] Instance Op_B_INSTANCE_OFF_38_CELL : @CstOp Z Z B_INSTANCE_OFF_38_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_38_CELL Inj_Z_Z 0xa80d0 eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_38_CELL.
Definition B_INSTANCE_OFF_E20_CELL : Z := 0xa8eb8.   (* symbol _ZN6__asanL8instanceE + 0xe20 *)
#[export] Instance Op_B_INSTANCE_OFF_E20_CELL : @CstOp Z Z B_INSTANCE_OFF_E20_CELL Inj_Z_Z := @mkcst Z Z B_INSTANCE_OFF_E20_CELL Inj_Z_Z 0xa8eb8 eq_refl.
Add Zify CstOp Op_B_INSTANCE_OFF_E20_CELL.
Definition B_INTERCEPTOR_FFLUSH_PC_OFF_2C : Z := 0x47828.   (* symbol __interceptor_fflush + 0x2c *)
#[export] Instance Op_B_INTERCEPTOR_FFLUSH_PC_OFF_2C : @CstOp Z Z B_INTERCEPTOR_FFLUSH_PC_OFF_2C Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FFLUSH_PC_OFF_2C Inj_Z_Z 0x47828 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FFLUSH_PC_OFF_2C.
Definition B_INTERCEPTOR_FFLUSH_PC_OFF_A8 : Z := 0x478a4.   (* symbol __interceptor_fflush + 0xa8 *)
#[export] Instance Op_B_INTERCEPTOR_FFLUSH_PC_OFF_A8 : @CstOp Z Z B_INTERCEPTOR_FFLUSH_PC_OFF_A8 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FFLUSH_PC_OFF_A8 Inj_Z_Z 0x478a4 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FFLUSH_PC_OFF_A8.
Definition B_INTERCEPTOR_FPRINTF_PC : Z := 0x46620.   (* symbol __interceptor_fprintf (216 bytes) *)
#[export] Instance Op_B_INTERCEPTOR_FPRINTF_PC : @CstOp Z Z B_INTERCEPTOR_FPRINTF_PC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FPRINTF_PC Inj_Z_Z 0x46620 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FPRINTF_PC.
Definition B_INTERCEPTOR_FPRINTF_PC_OFF_C0 : Z := 0x466e0.   (* symbol __interceptor_fprintf + 0xc0 *)
#[export] Instance Op_B_INTERCEPTOR_FPRINTF_PC_OFF_C0 : @CstOp Z Z B_INTERCEPTOR_FPRINTF_PC_OFF_C0 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FPRINTF_PC_OFF_C0 Inj_Z_Z 0x466e0 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FPRINTF_PC_OFF_C0.
Definition B_INTERCEPTOR_FREE_PC : Z := 0x5382c.   (* symbol ___interceptor_free (464 bytes) *)
#[export] Instance Op_B_INTERCEPTOR_FREE_PC : @CstOp Z Z B_INTERCEPTOR_FREE_PC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FREE_PC Inj_Z_Z 0x5382c eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FREE_PC.
Definition B_INTERCEPTOR_FREE_PC_OFF_138 : Z := 0x53964.   (* symbol ___interceptor_free + 0x138 *)
#[export] Instance Op_B_INTERCEPTOR_FREE_PC_OFF_138 : @CstOp Z Z B_INTERCEPTOR_FREE_PC_OFF_138 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FREE_PC_OFF_138 Inj_Z_Z 0x53964 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FREE_PC_OFF_138.
Definition B_INTERCEPTOR_FREE_PC_OFF_194 : Z := 0x539c0.   (* symbol ___interceptor_free + 0x194 *)
#[export] Instance Op_B_INTERCEPTOR_FREE_PC_OFF_194 : @CstOp Z Z B_INTERCEPTOR_FREE_PC_OFF_194 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FREE_PC_OFF_194 Inj_Z_Z 0x539c0 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FREE_PC_OFF_194.
Definition B_INTERCEPTOR_FREE_PC_OFF_1CC : Z := 0x539f8.   (* symbol ___interceptor_free + 0x1cc *)
#[export] Instance Op_B_INTERCEPTOR_FREE_PC_OFF_1CC : @CstOp Z Z B_INTERCEPTOR_FREE_PC_OFF_1CC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FREE_PC_OFF_1CC Inj_Z_Z 0x539f8 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FREE_PC_OFF_1CC.
Definition B_INTERCEPTOR_FREE_PC_OFF_34 : Z := 0x53860.   (* symbol ___interceptor_free + 0x34 *)
#[export] Instance Op_B_INTERCEPTOR_FREE_PC_OFF_34 : @CstOp Z Z B_INTERCEPTOR_FREE_PC_OFF_34 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FREE_PC_OFF_34 Inj_Z_Z 0x53860 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FREE_PC_OFF_34.
Definition B_INTERCEPTOR_FREE_PC_OFF_48 : Z := 0x53874.   (* symbol ___interceptor_free + 0x48 *)
#[export] Instance Op_B_INTERCEPTOR_FREE_PC_OFF_48 : @CstOp Z Z B_INTERCEPTOR_FREE_PC_OFF_48 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FREE_PC_OFF_48 Inj_Z_Z 0x53874 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FREE_PC_OFF_48.
Definition B_INTERCEPTOR_FWRITE_PC : Z := 0x44d98.   (* symbol __interceptor_fwrite (628 bytes) *)
#[export] Instance Op_B_INTERCEPTOR_FWRITE_PC : @CstOp Z Z B_INTERCEPTOR_FWRITE_PC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FWRITE_PC Inj_Z_Z 0x44d98 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FWRITE_PC.
Definition B_INTERCEPTOR_FWRITE_PC_OFF_5C : Z := 0x44df4.   (* symbol __interceptor_fwrite + 0x5c *)
#[export] Instance Op_B_INTERCEPTOR_FWRITE_PC_OFF_5C : @CstOp Z Z B_INTERCEPTOR_FWRITE_PC_OFF_5C Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FWRITE_PC_OFF_5C Inj_Z_Z 0x44df4 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FWRITE_PC_OFF_5C.
Definition B_INTERCEPTOR_FWRITE_PC_OFF_60 : Z := 0x44df8.   (* symbol __interceptor_fwrite + 0x60 *)
#[export] Instance Op_B_INTERCEPTOR_FWRITE_PC_OFF_60 : @CstOp Z Z B_INTERCEPTOR_FWRITE_PC_OFF_60 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FWRITE_PC_OFF_60 Inj_Z_Z 0x44df8 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FWRITE_PC_OFF_60.
Definition B_INTERCEPTOR_FWRITE_PC_OFF_64 : Z := 0x44dfc.   (* symbol __interceptor_fwrite + 0x64 *)
#[export] Instance Op_B_INTERCEPTOR_FWRITE_PC_OFF_64 : @CstOp Z Z B_INTERCEPTOR_FWRITE_PC_OFF_64 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FWRITE_PC_OFF_64 Inj_Z_Z 0x44dfc eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FWRITE_PC_OFF_64.
Definition B_INTERCEPTOR_FWRITE_PC_OFF_68 : Z := 0x44e00.   (* symbol __interceptor_fwrite + 0x68 *)
#[export] Instance Op_B_INTERCEPTOR_FWRITE_PC_OFF_68 : @CstOp Z Z B_INTERCEPTOR_FWRITE_PC_OFF_68 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FWRITE_PC_OFF_68 Inj_Z_Z 0x44e00 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FWRITE_PC_OFF_68.
Definition B_INTERCEPTOR_FWRITE_PC_OFF_B4 : Z := 0x44e4c.   (* symbol __interceptor_fwrite + 0xb4 *)
#[export] Instance Op_B_INTERCEPTOR_FWRITE_PC_OFF_B4 : @CstOp Z Z B_INTERCEPTOR_FWRITE_PC_OFF_B4 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FWRITE_PC_OFF_B4 Inj_Z_Z 0x44e4c eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FWRITE_PC_OFF_B4.
Definition B_INTERCEPTOR_FWRITE_PC_OFF_B8 : Z := 0x44e50.   (* symbol __interceptor_fwrite + 0xb8 *)
#[export] Instance Op_B_INTERCEPTOR_FWRITE_PC_OFF_B8 : @CstOp Z Z B_INTERCEPTOR_FWRITE_PC_OFF_B8 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FWRITE_PC_OFF_B8 Inj_Z_Z 0x44e50 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FWRITE_PC_OFF_B8.
Definition B_INTERCEPTOR_FWRITE_PC_OFF_C0 : Z := 0x44e58.   (* symbol __interceptor_fwrite + 0xc0 *)
#[export] Instance Op_B_INTERCEPTOR_FWRITE_PC_OFF_C0 : @CstOp Z Z B_INTERCEPTOR_FWRITE_PC_OFF_C0 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_FWRITE_PC_OFF_C0 Inj_Z_Z 0x44e58 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_FWRITE_PC_OFF_C0.
Definition B_INTERCEPTOR_MALLOC_PC : Z := 0x539fc.   (* symbol ___interceptor_malloc (348 bytes) *)
#[export] Instance Op_B_INTERCEPTOR_MALLOC_PC : @CstOp Z Z B_INTERCEPTOR_MALLOC_PC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MALLOC_PC Inj_Z_Z 0x539fc eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MALLOC_PC.
Definition B_INTERCEPTOR_MALLOC_PC_OFF_124 : Z := 0x53b20.   (* symbol ___interceptor_malloc + 0x124 *)
#[export] Instance Op_B_INTERCEPTOR_MALLOC_PC_OFF_124 : @CstOp Z Z B_INTERCEPTOR_MALLOC_PC_OFF_124 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MALLOC_PC_OFF_124 Inj_Z_Z 0x53b20 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MALLOC_PC_OFF_124.
Definition B_INTERCEPTOR_MALLOC_PC_OFF_158 : Z := 0x53b54.   (* symbol ___interceptor_malloc + 0x158 *)
#[export] Instance Op_B_INTERCEPTOR_MALLOC_PC_OFF_158 : @CstOp Z Z B_INTERCEPTOR_MALLOC_PC_OFF_158 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MALLOC_PC_OFF_158 Inj_Z_Z 0x53b54 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MALLOC_PC_OFF_158.
Definition B_INTERCEPTOR_MALLOC_PC_OFF_C8 : Z := 0x53ac4.   (* symbol ___interceptor_malloc + 0xc8 *)
#[export] Instance Op_B_INTERCEPTOR_MALLOC_PC_OFF_C8 : @CstOp Z Z B_INTERCEPTOR_MALLOC_PC_OFF_C8 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MALLOC_PC_OFF_C8 Inj_Z_Z 0x53ac4 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MALLOC_PC_OFF_C8.
Definition B_INTERCEPTOR_MEMCHR_PC : Z := 0x445e0.   (* symbol __interceptor_memchr (720 bytes) *)
#[export] Instance Op_B_INTERCEPTOR_MEMCHR_PC : @CstOp Z Z B_INTERCEPTOR_MEMCHR_PC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMCHR_PC Inj_Z_Z 0x445e0 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMCHR_PC.
Definition B_INTERCEPTOR_MEMCHR_PC_OFF_5C : Z := 0x4463c.   (* symbol __interceptor_memchr + 0x5c *)
#[export] Instance Op_B_INTERCEPTOR_MEMCHR_PC_OFF_5C : @CstOp Z Z B_INTERCEPTOR_MEMCHR_PC_OFF_5C Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMCHR_PC_OFF_5C Inj_Z_Z 0x4463c eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMCHR_PC_OFF_5C.
Definition B_INTERCEPTOR_MEMCHR_PC_OFF_B0 : Z := 0x44690.   (* symbol __interceptor_memchr + 0xb0 *)
#[export] Instance Op_B_INTERCEPTOR_MEMCHR_PC_OFF_B0 : @CstOp Z Z B_INTERCEPTOR_MEMCHR_PC_OFF_B0 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMCHR_PC_OFF_B0 Inj_Z_Z 0x44690 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMCHR_PC_OFF_B0.
Definition B_INTERCEPTOR_MEMCHR_PC_OFF_B4 : Z := 0x44694.   (* symbol __interceptor_memchr + 0xb4 *)
#[export] Instance Op_B_INTERCEPTOR_MEMCHR_PC_OFF_B4 : @CstOp Z Z B_INTERCEPTOR_MEMCHR_PC_OFF_B4 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMCHR_PC_OFF_B4 Inj_Z_Z 0x44694 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMCHR_PC_OFF_B4.
Definition B_INTERCEPTOR_MEMCHR_PC_OFF_BC : Z := 0x4469c.   (* symbol __interceptor_memchr + 0xbc *)
#[export] Instance Op_B_INTERCEPTOR_MEMCHR_PC_OFF_BC : @CstOp Z Z B_INTERCEPTOR_MEMCHR_PC_OFF_BC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMCHR_PC_OFF_BC Inj_Z_Z 0x4469c eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMCHR_PC_OFF_BC.
Definition B_INTERCEPTOR_MEMCMP_PC : Z := 0x44468.   (* symbol __interceptor_memcmp (188 bytes) *)
#[export] Instance Op_B_INTERCEPTOR_MEMCMP_PC : @CstOp Z Z B_INTERCEPTOR_MEMCMP_PC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMCMP_PC Inj_Z_Z 0x44468 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMCMP_PC.
Definition B_INTERCEPTOR_MEMCPY_PC : Z := 0x52e9c.   (* symbol __interceptor_memcpy (1520 bytes) *)
#[export] Instance Op_B_INTERCEPTOR_MEMCPY_PC : @CstOp Z Z B_INTERCEPTOR_MEMCPY_PC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMCPY_PC Inj_Z_Z 0x52e9c eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMCPY_PC.
Definition B_INTERCEPTOR_MEMCPY_PC_OFF_100 : Z := 0x52f9c.   (* symbol __interceptor_memcpy + 0x100 *)
#[export] Instance Op_B_INTERCEPTOR_MEMCPY_PC_OFF_100 : @CstOp Z Z B_INTERCEPTOR_MEMCPY_PC_OFF_100 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMCPY_PC_OFF_100 Inj_Z_Z 0x52f9c eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMCPY_PC_OFF_100.
Definition B_INTERCEPTOR_MEMCPY_PC_OFF_A0 : Z := 0x52f3c.   (* symbol __interceptor_memcpy + 0xa0 *)
#[export] Instance Op_B_INTERCEPTOR_MEMCPY_PC_OFF_A0 : @CstOp Z Z B_INTERCEPTOR_MEMCPY_PC_OFF_A0 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMCPY_PC_OFF_A0 Inj_Z_Z 0x52f3c eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMCPY_PC_OFF_A0.
Definition B_INTERCEPTOR_MEMCPY_PC_OFF_A4 : Z := 0x52f40.   (* symbol __interceptor_memcpy + 0xa4 *)
#[export] Instance Op_B_INTERCEPTOR_MEMCPY_PC_OFF_A4 : @CstOp Z Z B_INTERCEPTOR_MEMCPY_PC_OFF_A4 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMCPY_PC_OFF_A4 Inj_Z_Z 0x52f40 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMCPY_PC_OFF_A4.
Definition B_INTERCEPTOR_MEMCPY_PC_OFF_AC : Z := 0x52f48.   (* symbol __interceptor_memcpy + 0xac *)
#[export] Instance Op_B_INTERCEPTOR_MEMCPY_PC_OFF_AC : @CstOp Z Z B_INTERCEPTOR_MEMCPY_PC_OFF_AC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMCPY_PC_OFF_AC Inj_Z_Z 0x52f48 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMCPY_PC_OFF_AC.
Definition B_INTERCEPTOR_MEMCPY_PC_OFF_E8 : Z := 0x52f84.   (* symbol __interceptor_memcpy + 0xe8 *)
#[export] Instance Op_B_INTERCEPTOR_MEMCPY_PC_OFF_E8 : @CstOp Z Z B_INTERCEPTOR_MEMCPY_PC_OFF_E8 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMCPY_PC_OFF_E8 Inj_Z_Z 0x52f84 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMCPY_PC_OFF_E8.
Definition B_INTERCEPTOR_MEMCPY_PC_OFF_EC : Z := 0x52f88.   (* symbol __interceptor_memcpy + 0xec *)
#[export] Instance Op_B_INTERCEPTOR_MEMCPY_PC_OFF_EC : @CstOp Z Z B_INTERCEPTOR_MEMCPY_PC_OFF_EC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMCPY_PC_OFF_EC Inj_Z_Z 0x52f88 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMCPY_PC_OFF_EC.
Definition B_INTERCEPTOR_MEMSET_PC_OFF_88 : Z := 0x52c34.   (* symbol __interceptor_memset + 0x88 *)
#[export] Instance Op_B_INTERCEPTOR_MEMSET_PC_OFF_88 : @CstOp Z Z B_INTERCEPTOR_MEMSET_PC_OFF_88 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMSET_PC_OFF_88 Inj_Z_Z 0x52c34 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMSET_PC_OFF_88.
Definition B_INTERCEPTOR_MEMSET_PC_OFF_8C : Z := 0x52c38.   (* symbol __interceptor_memset + 0x8c *)
#[export] Instance Op_B_INTERCEPTOR_MEMSET_PC_OFF_8C : @CstOp Z Z B_INTERCEPTOR_MEMSET_PC_OFF_8C Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMSET_PC_OFF_8C Inj_Z_Z 0x52c38 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMSET_PC_OFF_8C.
Definition B_INTERCEPTOR_MEMSET_PC_OFF_A0 : Z := 0x52c4c.   (* symbol __interceptor_memset + 0xa0 *)
#[export] Instance Op_B_INTERCEPTOR_MEMSET_PC_OFF_A0 : @CstOp Z Z B_INTERCEPTOR_MEMSET_PC_OFF_A0 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_MEMSET_PC_OFF_A0 Inj_Z_Z 0x52c4c eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_MEMSET_PC_OFF_A0.
Definition B_INTERCEPTOR_METADATA_MAP_CELL : Z := 0xaaf40.   (* symbol _ZL24interceptor_metadata_map (8 bytes) *)
#[export] Instance Op_B_INTERCEPTOR_METADATA_MAP_CELL : @CstOp Z Z B_INTERCEPTOR_METADATA_MAP_CELL Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_METADATA_MAP_CELL Inj_Z_Z 0xaaf40 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_METADATA_MAP_CELL.
Definition B_INTERCEPTOR_METADATA_MAP_OFF_8_END_CELL : Z := 0xaaf48.   (* symbol _ZL24interceptor_metadata_map + 0x8 *)
#[export] Instance Op_B_INTERCEPTOR_METADATA_MAP_OFF_8_END_CELL : @CstOp Z Z B_INTERCEPTOR_METADATA_MAP_OFF_8_END_CELL Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_METADATA_MAP_OFF_8_END_CELL Inj_Z_Z 0xaaf48 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_METADATA_MAP_OFF_8_END_CELL.
Definition B_INTERCEPTOR_READ_PC : Z := 0x44b28.   (* symbol __interceptor_read (624 bytes) *)
#[export] Instance Op_B_INTERCEPTOR_READ_PC : @CstOp Z Z B_INTERCEPTOR_READ_PC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_READ_PC Inj_Z_Z 0x44b28 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_READ_PC.
Definition B_INTERCEPTOR_READ_PC_OFF_50 : Z := 0x44b78.   (* symbol __interceptor_read + 0x50 *)
#[export] Instance Op_B_INTERCEPTOR_READ_PC_OFF_50 : @CstOp Z Z B_INTERCEPTOR_READ_PC_OFF_50 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_READ_PC_OFF_50 Inj_Z_Z 0x44b78 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_READ_PC_OFF_50.
Definition B_INTERCEPTOR_READ_PC_OFF_58 : Z := 0x44b80.   (* symbol __interceptor_read + 0x58 *)
#[export] Instance Op_B_INTERCEPTOR_READ_PC_OFF_58 : @CstOp Z Z B_INTERCEPTOR_READ_PC_OFF_58 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_READ_PC_OFF_58 Inj_Z_Z 0x44b80 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_READ_PC_OFF_58.
Definition B_INTERCEPTOR_READ_PC_OFF_A4 : Z := 0x44bcc.   (* symbol __interceptor_read + 0xa4 *)
#[export] Instance Op_B_INTERCEPTOR_READ_PC_OFF_A4 : @CstOp Z Z B_INTERCEPTOR_READ_PC_OFF_A4 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_READ_PC_OFF_A4 Inj_Z_Z 0x44bcc eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_READ_PC_OFF_A4.
Definition B_INTERCEPTOR_READ_PC_OFF_A8 : Z := 0x44bd0.   (* symbol __interceptor_read + 0xa8 *)
#[export] Instance Op_B_INTERCEPTOR_READ_PC_OFF_A8 : @CstOp Z Z B_INTERCEPTOR_READ_PC_OFF_A8 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_READ_PC_OFF_A8 Inj_Z_Z 0x44bd0 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_READ_PC_OFF_A8.
Definition B_INTERCEPTOR_READ_PC_OFF_B0 : Z := 0x44bd8.   (* symbol __interceptor_read + 0xb0 *)
#[export] Instance Op_B_INTERCEPTOR_READ_PC_OFF_B0 : @CstOp Z Z B_INTERCEPTOR_READ_PC_OFF_B0 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_READ_PC_OFF_B0 Inj_Z_Z 0x44bd8 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_READ_PC_OFF_B0.
Definition B_INTERCEPTOR_STRCHR_PC_OFF_150 : Z := 0x43a40.   (* symbol __interceptor_strchr + 0x150 *)
#[export] Instance Op_B_INTERCEPTOR_STRCHR_PC_OFF_150 : @CstOp Z Z B_INTERCEPTOR_STRCHR_PC_OFF_150 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_STRCHR_PC_OFF_150 Inj_Z_Z 0x43a40 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_STRCHR_PC_OFF_150.
Definition B_INTERCEPTOR_STRNLEN_PC : Z := 0x43128.   (* symbol __interceptor_strnlen (660 bytes) *)
#[export] Instance Op_B_INTERCEPTOR_STRNLEN_PC : @CstOp Z Z B_INTERCEPTOR_STRNLEN_PC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_STRNLEN_PC Inj_Z_Z 0x43128 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_STRNLEN_PC.
Definition B_INTERCEPTOR_STRNLEN_PC_OFF_50 : Z := 0x43178.   (* symbol __interceptor_strnlen + 0x50 *)
#[export] Instance Op_B_INTERCEPTOR_STRNLEN_PC_OFF_50 : @CstOp Z Z B_INTERCEPTOR_STRNLEN_PC_OFF_50 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_STRNLEN_PC_OFF_50 Inj_Z_Z 0x43178 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_STRNLEN_PC_OFF_50.
Definition B_INTERCEPTOR_STRNLEN_PC_OFF_B8 : Z := 0x431e0.   (* symbol __interceptor_strnlen + 0xb8 *)
#[export] Instance Op_B_INTERCEPTOR_STRNLEN_PC_OFF_B8 : @CstOp Z Z B_INTERCEPTOR_STRNLEN_PC_OFF_B8 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_STRNLEN_PC_OFF_B8 Inj_Z_Z 0x431e0 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_STRNLEN_PC_OFF_B8.
Definition B_INTERCEPTOR_STRNLEN_PC_OFF_BC : Z := 0x431e4.   (* symbol __interceptor_strnlen + 0xbc *)
#[export] Instance Op_B_INTERCEPTOR_STRNLEN_PC_OFF_BC : @CstOp Z Z B_INTERCEPTOR_STRNLEN_PC_OFF_BC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_STRNLEN_PC_OFF_BC Inj_Z_Z 0x431e4 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_STRNLEN_PC_OFF_BC.
Definition B_INTERCEPTOR_STRNLEN_PC_OFF_C4 : Z := 0x431ec.   (* symbol __interceptor_strnlen + 0xc4 *)
#[export] Instance Op_B_INTERCEPTOR_STRNLEN_PC_OFF_C4 : @CstOp Z Z B_INTERCEPTOR_STRNLEN_PC_OFF_C4 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_STRNLEN_PC_OFF_C4 Inj_Z_Z 0x431ec eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_STRNLEN_PC_OFF_C4.
Definition B_INTERCEPTOR_TLS_GET_ADDR_PC : Z := 0x47780.   (* symbol __interceptor___tls_get_addr (124 bytes) *)
#[export] Instance Op_B_INTERCEPTOR_TLS_GET_ADDR_PC : @CstOp Z Z B_INTERCEPTOR_TLS_GET_ADDR_PC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_TLS_GET_ADDR_PC Inj_Z_Z 0x47780 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_TLS_GET_ADDR_PC.
Definition B_INTERCEPTOR_VFPRINTF_PC : Z := 0x46254.   (* symbol __interceptor_vfprintf (180 bytes) *)
#[export] Instance Op_B_INTERCEPTOR_VFPRINTF_PC : @CstOp Z Z B_INTERCEPTOR_VFPRINTF_PC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_VFPRINTF_PC Inj_Z_Z 0x46254 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_VFPRINTF_PC.
Definition B_INTERCEPTOR_VFPRINTF_PC_OFF_70 : Z := 0x462c4.   (* symbol __interceptor_vfprintf + 0x70 *)
#[export] Instance Op_B_INTERCEPTOR_VFPRINTF_PC_OFF_70 : @CstOp Z Z B_INTERCEPTOR_VFPRINTF_PC_OFF_70 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_VFPRINTF_PC_OFF_70 Inj_Z_Z 0x462c4 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_VFPRINTF_PC_OFF_70.
Definition B_INTERCEPTOR_VPRINTF_PC : Z := 0x456f0.   (* symbol __interceptor_vprintf (156 bytes) *)
#[export] Instance Op_B_INTERCEPTOR_VPRINTF_PC : @CstOp Z Z B_INTERCEPTOR_VPRINTF_PC Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_VPRINTF_PC Inj_Z_Z 0x456f0 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_VPRINTF_PC.
Definition B_INTERCEPTOR_VPRINTF_PC_OFF_64 : Z := 0x45754.   (* symbol __interceptor_vprintf + 0x64 *)
#[export] Instance Op_B_INTERCEPTOR_VPRINTF_PC_OFF_64 : @CstOp Z Z B_INTERCEPTOR_VPRINTF_PC_OFF_64 Inj_Z_Z := @mkcst Z Z B_INTERCEPTOR_VPRINTF_PC_OFF_64 Inj_Z_Z 0x45754 eq_refl.
Add Zify CstOp Op_B_INTERCEPTOR_VPRINTF_PC_OFF_64.
Definition B_INTERNAL_ALLOCATOR_PC : Z := 0x5f0a4.   (* symbol _ZN11__sanitizer18internal_allocatorEv (344 bytes) *)
#[export] Instance Op_B_INTERNAL_ALLOCATOR_PC : @CstOp Z Z B_INTERNAL_ALLOCATOR_PC Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOCATOR_PC Inj_Z_Z 0x5f0a4 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOCATOR_PC.
Definition B_INTERNAL_ALLOCATOR_PC_OFF_10C : Z := 0x5f1b0.   (* symbol _ZN11__sanitizer18internal_allocatorEv + 0x10c *)
#[export] Instance Op_B_INTERNAL_ALLOCATOR_PC_OFF_10C : @CstOp Z Z B_INTERNAL_ALLOCATOR_PC_OFF_10C Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOCATOR_PC_OFF_10C Inj_Z_Z 0x5f1b0 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOCATOR_PC_OFF_10C.
Definition B_INTERNAL_ALLOCATOR_PC_OFF_144 : Z := 0x5f1e8.   (* symbol _ZN11__sanitizer18internal_allocatorEv + 0x144 *)
#[export] Instance Op_B_INTERNAL_ALLOCATOR_PC_OFF_144 : @CstOp Z Z B_INTERNAL_ALLOCATOR_PC_OFF_144 Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOCATOR_PC_OFF_144 Inj_Z_Z 0x5f1e8 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOCATOR_PC_OFF_144.
Definition B_INTERNAL_ALLOCATOR_PC_OFF_28 : Z := 0x5f0cc.   (* symbol _ZN11__sanitizer18internal_allocatorEv + 0x28 *)
#[export] Instance Op_B_INTERNAL_ALLOCATOR_PC_OFF_28 : @CstOp Z Z B_INTERNAL_ALLOCATOR_PC_OFF_28 Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOCATOR_PC_OFF_28 Inj_Z_Z 0x5f0cc eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOCATOR_PC_OFF_28.
Definition B_INTERNAL_ALLOCATOR_PC_OFF_70 : Z := 0x5f114.   (* symbol _ZN11__sanitizer18internal_allocatorEv + 0x70 *)
#[export] Instance Op_B_INTERNAL_ALLOCATOR_PC_OFF_70 : @CstOp Z Z B_INTERNAL_ALLOCATOR_PC_OFF_70 Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOCATOR_PC_OFF_70 Inj_Z_Z 0x5f114 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOCATOR_PC_OFF_70.
Definition B_INTERNAL_ALLOCATOR_PC_OFF_78 : Z := 0x5f11c.   (* symbol _ZN11__sanitizer18internal_allocatorEv + 0x78 *)
#[export] Instance Op_B_INTERNAL_ALLOCATOR_PC_OFF_78 : @CstOp Z Z B_INTERNAL_ALLOCATOR_PC_OFF_78 Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOCATOR_PC_OFF_78 Inj_Z_Z 0x5f11c eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOCATOR_PC_OFF_78.
Definition B_INTERNAL_ALLOCATOR_PC_OFF_9C : Z := 0x5f140.   (* symbol _ZN11__sanitizer18internal_allocatorEv + 0x9c *)
#[export] Instance Op_B_INTERNAL_ALLOCATOR_PC_OFF_9C : @CstOp Z Z B_INTERNAL_ALLOCATOR_PC_OFF_9C Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOCATOR_PC_OFF_9C Inj_Z_Z 0x5f140 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOCATOR_PC_OFF_9C.
Definition B_INTERNAL_ALLOCATOR_PC_OFF_B4 : Z := 0x5f158.   (* symbol _ZN11__sanitizer18internal_allocatorEv + 0xb4 *)
#[export] Instance Op_B_INTERNAL_ALLOCATOR_PC_OFF_B4 : @CstOp Z Z B_INTERNAL_ALLOCATOR_PC_OFF_B4 Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOCATOR_PC_OFF_B4 Inj_Z_Z 0x5f158 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOCATOR_PC_OFF_B4.
Definition B_INTERNAL_ALLOCATOR_PC_OFF_CC : Z := 0x5f170.   (* symbol _ZN11__sanitizer18internal_allocatorEv + 0xcc *)
#[export] Instance Op_B_INTERNAL_ALLOCATOR_PC_OFF_CC : @CstOp Z Z B_INTERNAL_ALLOCATOR_PC_OFF_CC Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOCATOR_PC_OFF_CC Inj_Z_Z 0x5f170 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOCATOR_PC_OFF_CC.
Definition B_INTERNAL_ALLOCATOR_PC_OFF_E4 : Z := 0x5f188.   (* symbol _ZN11__sanitizer18internal_allocatorEv + 0xe4 *)
#[export] Instance Op_B_INTERNAL_ALLOCATOR_PC_OFF_E4 : @CstOp Z Z B_INTERNAL_ALLOCATOR_PC_OFF_E4 Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOCATOR_PC_OFF_E4 Inj_Z_Z 0x5f188 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOCATOR_PC_OFF_E4.
Definition B_INTERNAL_ALLOC_PLACEHOLDER_CELL : Z := 0xac900.   (* symbol _ZN11__sanitizerL26internal_alloc_placeholderE (528448 bytes) *)
#[export] Instance Op_B_INTERNAL_ALLOC_PLACEHOLDER_CELL : @CstOp Z Z B_INTERNAL_ALLOC_PLACEHOLDER_CELL Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOC_PLACEHOLDER_CELL Inj_Z_Z 0xac900 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOC_PLACEHOLDER_CELL.
Definition B_INTERNAL_ALLOC_PLACEHOLDER_OFF_10_CELL : Z := 0xac910.   (* symbol _ZN11__sanitizerL26internal_alloc_placeholderE + 0x10 *)
#[export] Instance Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_10_CELL : @CstOp Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_10_CELL Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_10_CELL Inj_Z_Z 0xac910 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_10_CELL.
Definition B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40008_CELL : Z := 0xec908.   (* symbol _ZN11__sanitizerL26internal_alloc_placeholderE + 0x40008 *)
#[export] Instance Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40008_CELL : @CstOp Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40008_CELL Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40008_CELL Inj_Z_Z 0xec908 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40008_CELL.
Definition B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40040_CELL : Z := 0xec940.   (* symbol _ZN11__sanitizerL26internal_alloc_placeholderE + 0x40040 *)
#[export] Instance Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40040_CELL : @CstOp Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40040_CELL Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40040_CELL Inj_Z_Z 0xec940 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40040_CELL.
Definition B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40DC0_CELL : Z := 0xed6c0.   (* symbol _ZN11__sanitizerL26internal_alloc_placeholderE + 0x40dc0 *)
#[export] Instance Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40DC0_CELL : @CstOp Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40DC0_CELL Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40DC0_CELL Inj_Z_Z 0xed6c0 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40DC0_CELL.
Definition B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40DD0_CELL : Z := 0xed6d0.   (* symbol _ZN11__sanitizerL26internal_alloc_placeholderE + 0x40dd0 *)
#[export] Instance Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40DD0_CELL : @CstOp Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40DD0_CELL Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40DD0_CELL Inj_Z_Z 0xed6d0 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_40DD0_CELL.
Definition B_INTERNAL_ALLOC_PLACEHOLDER_OFF_81008_CELL : Z := 0x12d908.   (* symbol _ZN11__sanitizerL26internal_alloc_placeholderE + 0x81008 *)
#[export] Instance Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_81008_CELL : @CstOp Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_81008_CELL Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_81008_CELL Inj_Z_Z 0x12d908 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_81008_CELL.
Definition B_INTERNAL_ALLOC_PLACEHOLDER_OFF_81030_CELL : Z := 0x12d930.   (* symbol _ZN11__sanitizerL26internal_alloc_placeholderE + 0x81030 *)
#[export] Instance Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_81030_CELL : @CstOp Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_81030_CELL Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_81030_CELL Inj_Z_Z 0x12d930 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_81030_CELL.
Definition B_INTERNAL_ALLOC_PLACEHOLDER_OFF_8_CELL : Z := 0xac908.   (* symbol _ZN11__sanitizerL26internal_alloc_placeholderE + 0x8 *)
#[export] Instance Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_8_CELL : @CstOp Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_8_CELL Inj_Z_Z := @mkcst Z Z B_INTERNAL_ALLOC_PLACEHOLDER_OFF_8_CELL Inj_Z_Z 0xac908 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ALLOC_PLACEHOLDER_OFF_8_CELL.
Definition B_INTERNAL_ISERROR_PC : Z := 0x65384.   (* symbol _ZN11__sanitizer16internal_iserrorEmPi (32 bytes) *)
#[export] Instance Op_B_INTERNAL_ISERROR_PC : @CstOp Z Z B_INTERNAL_ISERROR_PC Inj_Z_Z := @mkcst Z Z B_INTERNAL_ISERROR_PC Inj_Z_Z 0x65384 eq_refl.
Add Zify CstOp Op_B_INTERNAL_ISERROR_PC.
Definition B_INTERNAL_MADVISE_PC_OFF_20 : Z := 0x653ec.   (* symbol _ZN11__sanitizer16internal_madviseEmmi + 0x20 *)
#[export] Instance Op_B_INTERNAL_MADVISE_PC_OFF_20 : @CstOp Z Z B_INTERNAL_MADVISE_PC_OFF_20 Inj_Z_Z := @mkcst Z Z B_INTERNAL_MADVISE_PC_OFF_20 Inj_Z_Z 0x653ec eq_refl.
Add Zify CstOp Op_B_INTERNAL_MADVISE_PC_OFF_20.
Definition B_INTERNAL_MADVISE_PC_OFF_24 : Z := 0x653f0.   (* symbol _ZN11__sanitizer16internal_madviseEmmi + 0x24 *)
#[export] Instance Op_B_INTERNAL_MADVISE_PC_OFF_24 : @CstOp Z Z B_INTERNAL_MADVISE_PC_OFF_24 Inj_Z_Z := @mkcst Z Z B_INTERNAL_MADVISE_PC_OFF_24 Inj_Z_Z 0x653f0 eq_refl.
Add Zify CstOp Op_B_INTERNAL_MADVISE_PC_OFF_24.
Definition B_INTERNAL_MMAP_PC_OFF_4 : Z := 0x653a8.   (* symbol _ZN11__sanitizer13internal_mmapEPvmiiiy + 0x4 *)
#[export] Instance Op_B_INTERNAL_MMAP_PC_OFF_4 : @CstOp Z Z B_INTERNAL_MMAP_PC_OFF_4 Inj_Z_Z := @mkcst Z Z B_INTERNAL_MMAP_PC_OFF_4 Inj_Z_Z 0x653a8 eq_refl.
Add Zify CstOp Op_B_INTERNAL_MMAP_PC_OFF_4.
Definition B_INTERNAL_MMAP_PC_OFF_8 : Z := 0x653ac.   (* symbol _ZN11__sanitizer13internal_mmapEPvmiiiy + 0x8 *)
#[export] Instance Op_B_INTERNAL_MMAP_PC_OFF_8 : @CstOp Z Z B_INTERNAL_MMAP_PC_OFF_8 Inj_Z_Z := @mkcst Z Z B_INTERNAL_MMAP_PC_OFF_8 Inj_Z_Z 0x653ac eq_refl.
Add Zify CstOp Op_B_INTERNAL_MMAP_PC_OFF_8.
Definition B_INTERNAL_MUNMAP_PC : Z := 0x653b0.   (* symbol _ZN11__sanitizer15internal_munmapEPvm (12 bytes) *)
#[export] Instance Op_B_INTERNAL_MUNMAP_PC : @CstOp Z Z B_INTERNAL_MUNMAP_PC Inj_Z_Z := @mkcst Z Z B_INTERNAL_MUNMAP_PC Inj_Z_Z 0x653b0 eq_refl.
Add Zify CstOp Op_B_INTERNAL_MUNMAP_PC.
Definition B_INTERNAL_MUNMAP_PC_OFF_4 : Z := 0x653b4.   (* symbol _ZN11__sanitizer15internal_munmapEPvm + 0x4 *)
#[export] Instance Op_B_INTERNAL_MUNMAP_PC_OFF_4 : @CstOp Z Z B_INTERNAL_MUNMAP_PC_OFF_4 Inj_Z_Z := @mkcst Z Z B_INTERNAL_MUNMAP_PC_OFF_4 Inj_Z_Z 0x653b4 eq_refl.
Add Zify CstOp Op_B_INTERNAL_MUNMAP_PC_OFF_4.
Definition B_INTERNAL_MUNMAP_PC_OFF_8 : Z := 0x653b8.   (* symbol _ZN11__sanitizer15internal_munmapEPvm + 0x8 *)
#[export] Instance Op_B_INTERNAL_MUNMAP_PC_OFF_8 : @CstOp Z Z B_INTERNAL_MUNMAP_PC_OFF_8 Inj_Z_Z := @mkcst Z Z B_INTERNAL_MUNMAP_PC_OFF_8 Inj_Z_Z 0x653b8 eq_refl.
Add Zify CstOp Op_B_INTERNAL_MUNMAP_PC_OFF_8.
Definition B_INTERNAL_STRCHR_PC : Z := 0x64c58.   (* symbol _ZN11__sanitizer15internal_strchrEPKci (52 bytes) *)
#[export] Instance Op_B_INTERNAL_STRCHR_PC : @CstOp Z Z B_INTERNAL_STRCHR_PC Inj_Z_Z := @mkcst Z Z B_INTERNAL_STRCHR_PC Inj_Z_Z 0x64c58 eq_refl.
Add Zify CstOp Op_B_INTERNAL_STRCHR_PC.
Definition B_INTERNAL_STRLEN_PC : Z := 0x64cf8.   (* symbol _ZN11__sanitizer15internal_strlenEPKc (28 bytes) *)
#[export] Instance Op_B_INTERNAL_STRLEN_PC : @CstOp Z Z B_INTERNAL_STRLEN_PC Inj_Z_Z := @mkcst Z Z B_INTERNAL_STRLEN_PC Inj_Z_Z 0x64cf8 eq_refl.
Add Zify CstOp Op_B_INTERNAL_STRLEN_PC.
Definition B_INTERNAL_STRNCPY_PC : Z := 0x64fd0.   (* symbol _ZN11__sanitizer16internal_strncpyEPcPKcm (112 bytes) *)
#[export] Instance Op_B_INTERNAL_STRNCPY_PC : @CstOp Z Z B_INTERNAL_STRNCPY_PC Inj_Z_Z := @mkcst Z Z B_INTERNAL_STRNCPY_PC Inj_Z_Z 0x64fd0 eq_refl.
Add Zify CstOp Op_B_INTERNAL_STRNCPY_PC.
Definition B_INTERNAL_STRNLEN_PC : Z := 0x64f5c.   (* symbol _ZN11__sanitizer16internal_strnlenEPKcm (48 bytes) *)
#[export] Instance Op_B_INTERNAL_STRNLEN_PC : @CstOp Z Z B_INTERNAL_STRNLEN_PC Inj_Z_Z := @mkcst Z Z B_INTERNAL_STRNLEN_PC Inj_Z_Z 0x64f5c eq_refl.
Add Zify CstOp Op_B_INTERNAL_STRNLEN_PC.
Definition B_KHIGHMEMEND_CELL : Z := 0xac3e0.   (* symbol _ZN6__asan11kHighMemEndE (8 bytes) *)
#[export] Instance Op_B_KHIGHMEMEND_CELL : @CstOp Z Z B_KHIGHMEMEND_CELL Inj_Z_Z := @mkcst Z Z B_KHIGHMEMEND_CELL Inj_Z_Z 0xac3e0 eq_refl.
Add Zify CstOp Op_B_KHIGHMEMEND_CELL.
Definition B_KMIDMEMBEG_CELL : Z := 0xac3e8.   (* symbol _ZN6__asan10kMidMemBegE (8 bytes) *)
#[export] Instance Op_B_KMIDMEMBEG_CELL : @CstOp Z Z B_KMIDMEMBEG_CELL Inj_Z_Z := @mkcst Z Z B_KMIDMEMBEG_CELL Inj_Z_Z 0xac3e8 eq_refl.
Add Zify CstOp Op_B_KMIDMEMBEG_CELL.
Definition B_KMIDMEMEND_CELL : Z := 0xac3f0.   (* symbol _ZN6__asan10kMidMemEndE (8 bytes) *)
#[export] Instance Op_B_KMIDMEMEND_CELL : @CstOp Z Z B_KMIDMEMEND_CELL Inj_Z_Z := @mkcst Z Z B_KMIDMEMEND_CELL Inj_Z_Z 0xac3f0 eq_refl.
Add Zify CstOp Op_B_KMIDMEMEND_CELL.
Definition B_KSUPPRESSIONTYPES_OFF_130_END_CELL : Z := 0xa6dd8.   (* symbol _ZL17kSuppressionTypes + 0x130 *)
#[export] Instance Op_B_KSUPPRESSIONTYPES_OFF_130_END_CELL : @CstOp Z Z B_KSUPPRESSIONTYPES_OFF_130_END_CELL Inj_Z_Z := @mkcst Z Z B_KSUPPRESSIONTYPES_OFF_130_END_CELL Inj_Z_Z 0xa6dd8 eq_refl.
Add Zify CstOp Op_B_KSUPPRESSIONTYPES_OFF_130_END_CELL.
Definition B_LIBC_EXIT_FINI_PC_OFF_30 : Z := 0x8fb18.   (* symbol libc_exit_fini + 0x30 *)
#[export] Instance Op_B_LIBC_EXIT_FINI_PC_OFF_30 : @CstOp Z Z B_LIBC_EXIT_FINI_PC_OFF_30 Inj_Z_Z := @mkcst Z Z B_LIBC_EXIT_FINI_PC_OFF_30 Inj_Z_Z 0x8fb18 eq_refl.
Add Zify CstOp Op_B_LIBC_EXIT_FINI_PC_OFF_30.
Definition B_LIBC_OFF_3_CELL : Z := 0x5fe9c3.   (* symbol __libc + 0x3 *)
#[export] Instance Op_B_LIBC_OFF_3_CELL : @CstOp Z Z B_LIBC_OFF_3_CELL Inj_Z_Z := @mkcst Z Z B_LIBC_OFF_3_CELL Inj_Z_Z 0x5fe9c3 eq_refl.
Add Zify CstOp Op_B_LIBC_OFF_3_CELL.
Definition B_LIBC_OFF_4_CELL : Z := 0x5fe9c4.   (* symbol __libc + 0x4 *)
#[export] Instance Op_B_LIBC_OFF_4_CELL : @CstOp Z Z B_LIBC_OFF_4_CELL Inj_Z_Z := @mkcst Z Z B_LIBC_OFF_4_CELL Inj_Z_Z 0x5fe9c4 eq_refl.
Add Zify CstOp Op_B_LIBC_OFF_4_CELL.
Definition B_LIBC_START_MAIN_STAGE2_PC_OFF_44 : Z := 0x8f434.   (* symbol libc_start_main_stage2 + 0x44 *)
#[export] Instance Op_B_LIBC_START_MAIN_STAGE2_PC_OFF_44 : @CstOp Z Z B_LIBC_START_MAIN_STAGE2_PC_OFF_44 Inj_Z_Z := @mkcst Z Z B_LIBC_START_MAIN_STAGE2_PC_OFF_44 Inj_Z_Z 0x8f434 eq_refl.
Add Zify CstOp Op_B_LIBC_START_MAIN_STAGE2_PC_OFF_44.
Definition B_LLVMFUZZERTESTONEINPUT_PC : Z := 0x816cc.   (* symbol LLVMFuzzerTestOneInput (804 bytes) *)
#[export] Instance Op_B_LLVMFUZZERTESTONEINPUT_PC : @CstOp Z Z B_LLVMFUZZERTESTONEINPUT_PC Inj_Z_Z := @mkcst Z Z B_LLVMFUZZERTESTONEINPUT_PC Inj_Z_Z 0x816cc eq_refl.
Add Zify CstOp Op_B_LLVMFUZZERTESTONEINPUT_PC.
Definition B_LOCALADDRESSSPACEVIEW_ALLOCATE_ALLOCATORSTATS_OFF_1B4 : Z := 0x371d0.   (* symbol _ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x1b4 *)
#[export] Instance Op_B_LOCALADDRESSSPACEVIEW_ALLOCATE_ALLOCATORSTATS_OFF_1B4 : @CstOp Z Z B_LOCALADDRESSSPACEVIEW_ALLOCATE_ALLOCATORSTATS_OFF_1B4 Inj_Z_Z := @mkcst Z Z B_LOCALADDRESSSPACEVIEW_ALLOCATE_ALLOCATORSTATS_OFF_1B4 Inj_Z_Z 0x371d0 eq_refl.
Add Zify CstOp Op_B_LOCALADDRESSSPACEVIEW_ALLOCATE_ALLOCATORSTATS_OFF_1B4.
Definition B_LOCALADDRESSSPACEVIEW_ENSUREFREEARRAYSPACE_10RE_OFF_5C : Z := 0x355bc.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE20EnsureFreeArraySpaceEPNS5_10RegionInfoEmm + 0x5c *)
#[export] Instance Op_B_LOCALADDRESSSPACEVIEW_ENSUREFREEARRAYSPACE_10RE_OFF_5C : @CstOp Z Z B_LOCALADDRESSSPACEVIEW_ENSUREFREEARRAYSPACE_10RE_OFF_5C Inj_Z_Z := @mkcst Z Z B_LOCALADDRESSSPACEVIEW_ENSUREFREEARRAYSPACE_10RE_OFF_5C Inj_Z_Z 0x355bc eq_refl.
Add Zify CstOp Op_B_LOCALADDRESSSPACEVIEW_ENSUREFREEARRAYSPACE_10RE_OFF_5C.
Definition B_LOCKFILE_PC : Z := 0x954dc.   (* symbol __lockfile (252 bytes) *)
#[export] Instance Op_B_LOCKFILE_PC : @CstOp Z Z B_LOCKFILE_PC Inj_Z_Z := @mkcst Z Z B_LOCKFILE_PC Inj_Z_Z 0x954dc eq_refl.
Add Zify CstOp Op_B_LOCKFILE_PC.
Definition B_LOCK_CELL : Z := 0x5fe784.   (* B place section .bss + 0x556724, rekeyed (a) *)
#[export] Instance Op_B_LOCK_CELL : @CstOp Z Z B_LOCK_CELL Inj_Z_Z := @mkcst Z Z B_LOCK_CELL Inj_Z_Z 0x5fe784 eq_refl.
Add Zify CstOp Op_B_LOCK_CELL.
Definition B_LOCK_PC : Z := 0x9c3d4.   (* symbol __lock (648 bytes) *)
#[export] Instance Op_B_LOCK_PC : @CstOp Z Z B_LOCK_PC Inj_Z_Z := @mkcst Z Z B_LOCK_PC Inj_Z_Z 0x9c3d4 eq_refl.
Add Zify CstOp Op_B_LOCK_PC.
Definition B_LOCK_PC_OFF_1F8 : Z := 0x9c5cc.   (* symbol __lock + 0x1f8 *)
#[export] Instance Op_B_LOCK_PC_OFF_1F8 : @CstOp Z Z B_LOCK_PC_OFF_1F8 Inj_Z_Z := @mkcst Z Z B_LOCK_PC_OFF_1F8 Inj_Z_Z 0x9c5cc eq_refl.
Add Zify CstOp Op_B_LOCK_PC_OFF_1F8.
Definition B_MAIN_PC : Z := 0x8122c.   (* symbol main (708 bytes) *)
#[export] Instance Op_B_MAIN_PC : @CstOp Z Z B_MAIN_PC Inj_Z_Z := @mkcst Z Z B_MAIN_PC Inj_Z_Z 0x8122c eq_refl.
Add Zify CstOp Op_B_MAIN_PC.
Definition B_MAIN_PC_OFF_100 : Z := 0x8132c.   (* symbol main + 0x100 *)
#[export] Instance Op_B_MAIN_PC_OFF_100 : @CstOp Z Z B_MAIN_PC_OFF_100 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_100 Inj_Z_Z 0x8132c eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_100.
Definition B_MAIN_PC_OFF_11C : Z := 0x81348.   (* symbol main + 0x11c *)
#[export] Instance Op_B_MAIN_PC_OFF_11C : @CstOp Z Z B_MAIN_PC_OFF_11C Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_11C Inj_Z_Z 0x81348 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_11C.
Definition B_MAIN_PC_OFF_128 : Z := 0x81354.   (* symbol main + 0x128 *)
#[export] Instance Op_B_MAIN_PC_OFF_128 : @CstOp Z Z B_MAIN_PC_OFF_128 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_128 Inj_Z_Z 0x81354 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_128.
Definition B_MAIN_PC_OFF_174 : Z := 0x813a0.   (* symbol main + 0x174 *)
#[export] Instance Op_B_MAIN_PC_OFF_174 : @CstOp Z Z B_MAIN_PC_OFF_174 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_174 Inj_Z_Z 0x813a0 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_174.
Definition B_MAIN_PC_OFF_1B4 : Z := 0x813e0.   (* symbol main + 0x1b4 *)
#[export] Instance Op_B_MAIN_PC_OFF_1B4 : @CstOp Z Z B_MAIN_PC_OFF_1B4 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_1B4 Inj_Z_Z 0x813e0 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_1B4.
Definition B_MAIN_PC_OFF_1F4 : Z := 0x81420.   (* symbol main + 0x1f4 *)
#[export] Instance Op_B_MAIN_PC_OFF_1F4 : @CstOp Z Z B_MAIN_PC_OFF_1F4 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_1F4 Inj_Z_Z 0x81420 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_1F4.
Definition B_MAIN_PC_OFF_1FC : Z := 0x81428.   (* symbol main + 0x1fc *)
#[export] Instance Op_B_MAIN_PC_OFF_1FC : @CstOp Z Z B_MAIN_PC_OFF_1FC Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_1FC Inj_Z_Z 0x81428 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_1FC.
Definition B_MAIN_PC_OFF_22C : Z := 0x81458.   (* symbol main + 0x22c *)
#[export] Instance Op_B_MAIN_PC_OFF_22C : @CstOp Z Z B_MAIN_PC_OFF_22C Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_22C Inj_Z_Z 0x81458 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_22C.
Definition B_MAIN_PC_OFF_248 : Z := 0x81474.   (* symbol main + 0x248 *)
#[export] Instance Op_B_MAIN_PC_OFF_248 : @CstOp Z Z B_MAIN_PC_OFF_248 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_248 Inj_Z_Z 0x81474 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_248.
Definition B_MAIN_PC_OFF_264 : Z := 0x81490.   (* symbol main + 0x264 *)
#[export] Instance Op_B_MAIN_PC_OFF_264 : @CstOp Z Z B_MAIN_PC_OFF_264 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_264 Inj_Z_Z 0x81490 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_264.
Definition B_MAIN_PC_OFF_268 : Z := 0x81494.   (* symbol main + 0x268 *)
#[export] Instance Op_B_MAIN_PC_OFF_268 : @CstOp Z Z B_MAIN_PC_OFF_268 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_268 Inj_Z_Z 0x81494 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_268.
Definition B_MAIN_PC_OFF_288 : Z := 0x814b4.   (* symbol main + 0x288 *)
#[export] Instance Op_B_MAIN_PC_OFF_288 : @CstOp Z Z B_MAIN_PC_OFF_288 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_288 Inj_Z_Z 0x814b4 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_288.
Definition B_MAIN_PC_OFF_290 : Z := 0x814bc.   (* symbol main + 0x290 *)
#[export] Instance Op_B_MAIN_PC_OFF_290 : @CstOp Z Z B_MAIN_PC_OFF_290 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_290 Inj_Z_Z 0x814bc eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_290.
Definition B_MAIN_PC_OFF_2C : Z := 0x81258.   (* symbol main + 0x2c *)
#[export] Instance Op_B_MAIN_PC_OFF_2C : @CstOp Z Z B_MAIN_PC_OFF_2C Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_2C Inj_Z_Z 0x81258 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_2C.
Definition B_MAIN_PC_OFF_40 : Z := 0x8126c.   (* symbol main + 0x40 *)
#[export] Instance Op_B_MAIN_PC_OFF_40 : @CstOp Z Z B_MAIN_PC_OFF_40 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_40 Inj_Z_Z 0x8126c eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_40.
Definition B_MAIN_PC_OFF_50 : Z := 0x8127c.   (* symbol main + 0x50 *)
#[export] Instance Op_B_MAIN_PC_OFF_50 : @CstOp Z Z B_MAIN_PC_OFF_50 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_50 Inj_Z_Z 0x8127c eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_50.
Definition B_MAIN_PC_OFF_54 : Z := 0x81280.   (* symbol main + 0x54 *)
#[export] Instance Op_B_MAIN_PC_OFF_54 : @CstOp Z Z B_MAIN_PC_OFF_54 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_54 Inj_Z_Z 0x81280 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_54.
Definition B_MAIN_PC_OFF_80 : Z := 0x812ac.   (* symbol main + 0x80 *)
#[export] Instance Op_B_MAIN_PC_OFF_80 : @CstOp Z Z B_MAIN_PC_OFF_80 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_80 Inj_Z_Z 0x812ac eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_80.
Definition B_MAIN_PC_OFF_88 : Z := 0x812b4.   (* symbol main + 0x88 *)
#[export] Instance Op_B_MAIN_PC_OFF_88 : @CstOp Z Z B_MAIN_PC_OFF_88 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_88 Inj_Z_Z 0x812b4 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_88.
Definition B_MAIN_PC_OFF_98 : Z := 0x812c4.   (* symbol main + 0x98 *)
#[export] Instance Op_B_MAIN_PC_OFF_98 : @CstOp Z Z B_MAIN_PC_OFF_98 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_98 Inj_Z_Z 0x812c4 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_98.
Definition B_MAIN_PC_OFF_A8 : Z := 0x812d4.   (* symbol main + 0xa8 *)
#[export] Instance Op_B_MAIN_PC_OFF_A8 : @CstOp Z Z B_MAIN_PC_OFF_A8 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_A8 Inj_Z_Z 0x812d4 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_A8.
Definition B_MAIN_PC_OFF_C4 : Z := 0x812f0.   (* symbol main + 0xc4 *)
#[export] Instance Op_B_MAIN_PC_OFF_C4 : @CstOp Z Z B_MAIN_PC_OFF_C4 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_C4 Inj_Z_Z 0x812f0 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_C4.
Definition B_MAIN_PC_OFF_CC : Z := 0x812f8.   (* symbol main + 0xcc *)
#[export] Instance Op_B_MAIN_PC_OFF_CC : @CstOp Z Z B_MAIN_PC_OFF_CC Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_CC Inj_Z_Z 0x812f8 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_CC.
Definition B_MAIN_PC_OFF_D4 : Z := 0x81300.   (* symbol main + 0xd4 *)
#[export] Instance Op_B_MAIN_PC_OFF_D4 : @CstOp Z Z B_MAIN_PC_OFF_D4 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_D4 Inj_Z_Z 0x81300 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_D4.
Definition B_MAIN_PC_OFF_DC : Z := 0x81308.   (* symbol main + 0xdc *)
#[export] Instance Op_B_MAIN_PC_OFF_DC : @CstOp Z Z B_MAIN_PC_OFF_DC Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_DC Inj_Z_Z 0x81308 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_DC.
Definition B_MAIN_PC_OFF_E8 : Z := 0x81314.   (* symbol main + 0xe8 *)
#[export] Instance Op_B_MAIN_PC_OFF_E8 : @CstOp Z Z B_MAIN_PC_OFF_E8 Inj_Z_Z := @mkcst Z Z B_MAIN_PC_OFF_E8 Inj_Z_Z 0x81314 eq_refl.
Add Zify CstOp Op_B_MAIN_PC_OFF_E8.
Definition B_MALLOC_CONTEXT_SIZE_CELL : Z := 0xac3fc.   (* symbol _ZN6__asanL19malloc_context_sizeE (4 bytes) *)
#[export] Instance Op_B_MALLOC_CONTEXT_SIZE_CELL : @CstOp Z Z B_MALLOC_CONTEXT_SIZE_CELL Inj_Z_Z := @mkcst Z Z B_MALLOC_CONTEXT_SIZE_CELL Inj_Z_Z 0xac3fc eq_refl.
Add Zify CstOp Op_B_MALLOC_CONTEXT_SIZE_CELL.
Definition B_MAPORDIE_PC : Z := 0x6f440.   (* symbol _ZN11__sanitizer20ReservedAddressRange8MapOrDieEmmPKc (16 bytes) *)
#[export] Instance Op_B_MAPORDIE_PC : @CstOp Z Z B_MAPORDIE_PC Inj_Z_Z := @mkcst Z Z B_MAPORDIE_PC Inj_Z_Z 0x6f440 eq_refl.
Add Zify CstOp Op_B_MAPORDIE_PC.
Definition B_MAP_PC : Z := 0x6f2f4.   (* symbol _ZN11__sanitizer20ReservedAddressRange3MapEmmPKc (116 bytes) *)
#[export] Instance Op_B_MAP_PC : @CstOp Z Z B_MAP_PC Inj_Z_Z := @mkcst Z Z B_MAP_PC Inj_Z_Z 0x6f2f4 eq_refl.
Add Zify CstOp Op_B_MAP_PC.
Definition B_MEMCHR_PC : Z := 0x9ba08.   (* symbol memchr (204 bytes) *)
#[export] Instance Op_B_MEMCHR_PC : @CstOp Z Z B_MEMCHR_PC Inj_Z_Z := @mkcst Z Z B_MEMCHR_PC Inj_Z_Z 0x9ba08 eq_refl.
Add Zify CstOp Op_B_MEMCHR_PC.
Definition B_MEMCPY_PC : Z := 0x9bb04.   (* symbol memcpy (1028 bytes) *)
#[export] Instance Op_B_MEMCPY_PC : @CstOp Z Z B_MEMCPY_PC Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC Inj_Z_Z 0x9bb04 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC.
Definition B_MEMCPY_PC_OFF_104 : Z := 0x9bc08.   (* symbol memcpy + 0x104 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_104 : @CstOp Z Z B_MEMCPY_PC_OFF_104 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_104 Inj_Z_Z 0x9bc08 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_104.
Definition B_MEMCPY_PC_OFF_120 : Z := 0x9bc24.   (* symbol memcpy + 0x120 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_120 : @CstOp Z Z B_MEMCPY_PC_OFF_120 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_120 Inj_Z_Z 0x9bc24 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_120.
Definition B_MEMCPY_PC_OFF_12C : Z := 0x9bc30.   (* symbol memcpy + 0x12c *)
#[export] Instance Op_B_MEMCPY_PC_OFF_12C : @CstOp Z Z B_MEMCPY_PC_OFF_12C Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_12C Inj_Z_Z 0x9bc30 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_12C.
Definition B_MEMCPY_PC_OFF_15C : Z := 0x9bc60.   (* symbol memcpy + 0x15c *)
#[export] Instance Op_B_MEMCPY_PC_OFF_15C : @CstOp Z Z B_MEMCPY_PC_OFF_15C Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_15C Inj_Z_Z 0x9bc60 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_15C.
Definition B_MEMCPY_PC_OFF_17C : Z := 0x9bc80.   (* symbol memcpy + 0x17c *)
#[export] Instance Op_B_MEMCPY_PC_OFF_17C : @CstOp Z Z B_MEMCPY_PC_OFF_17C Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_17C Inj_Z_Z 0x9bc80 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_17C.
Definition B_MEMCPY_PC_OFF_18 : Z := 0x9bb1c.   (* symbol memcpy + 0x18 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_18 : @CstOp Z Z B_MEMCPY_PC_OFF_18 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_18 Inj_Z_Z 0x9bb1c eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_18.
Definition B_MEMCPY_PC_OFF_1AC : Z := 0x9bcb0.   (* symbol memcpy + 0x1ac *)
#[export] Instance Op_B_MEMCPY_PC_OFF_1AC : @CstOp Z Z B_MEMCPY_PC_OFF_1AC Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_1AC Inj_Z_Z 0x9bcb0 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_1AC.
Definition B_MEMCPY_PC_OFF_20C : Z := 0x9bd10.   (* symbol memcpy + 0x20c *)
#[export] Instance Op_B_MEMCPY_PC_OFF_20C : @CstOp Z Z B_MEMCPY_PC_OFF_20C Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_20C Inj_Z_Z 0x9bd10 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_20C.
Definition B_MEMCPY_PC_OFF_240 : Z := 0x9bd44.   (* symbol memcpy + 0x240 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_240 : @CstOp Z Z B_MEMCPY_PC_OFF_240 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_240 Inj_Z_Z 0x9bd44 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_240.
Definition B_MEMCPY_PC_OFF_2A0 : Z := 0x9bda4.   (* symbol memcpy + 0x2a0 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_2A0 : @CstOp Z Z B_MEMCPY_PC_OFF_2A0 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_2A0 Inj_Z_Z 0x9bda4 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_2A0.
Definition B_MEMCPY_PC_OFF_2AC : Z := 0x9bdb0.   (* symbol memcpy + 0x2ac *)
#[export] Instance Op_B_MEMCPY_PC_OFF_2AC : @CstOp Z Z B_MEMCPY_PC_OFF_2AC Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_2AC Inj_Z_Z 0x9bdb0 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_2AC.
Definition B_MEMCPY_PC_OFF_338 : Z := 0x9be3c.   (* symbol memcpy + 0x338 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_338 : @CstOp Z Z B_MEMCPY_PC_OFF_338 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_338 Inj_Z_Z 0x9be3c eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_338.
Definition B_MEMCPY_PC_OFF_340 : Z := 0x9be44.   (* symbol memcpy + 0x340 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_340 : @CstOp Z Z B_MEMCPY_PC_OFF_340 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_340 Inj_Z_Z 0x9be44 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_340.
Definition B_MEMCPY_PC_OFF_38C : Z := 0x9be90.   (* symbol memcpy + 0x38c *)
#[export] Instance Op_B_MEMCPY_PC_OFF_38C : @CstOp Z Z B_MEMCPY_PC_OFF_38C Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_38C Inj_Z_Z 0x9be90 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_38C.
Definition B_MEMCPY_PC_OFF_394 : Z := 0x9be98.   (* symbol memcpy + 0x394 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_394 : @CstOp Z Z B_MEMCPY_PC_OFF_394 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_394 Inj_Z_Z 0x9be98 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_394.
Definition B_MEMCPY_PC_OFF_3C0 : Z := 0x9bec4.   (* symbol memcpy + 0x3c0 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_3C0 : @CstOp Z Z B_MEMCPY_PC_OFF_3C0 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_3C0 Inj_Z_Z 0x9bec4 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_3C0.
Definition B_MEMCPY_PC_OFF_3F8 : Z := 0x9befc.   (* symbol memcpy + 0x3f8 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_3F8 : @CstOp Z Z B_MEMCPY_PC_OFF_3F8 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_3F8 Inj_Z_Z 0x9befc eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_3F8.
Definition B_MEMCPY_PC_OFF_48 : Z := 0x9bb4c.   (* symbol memcpy + 0x48 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_48 : @CstOp Z Z B_MEMCPY_PC_OFF_48 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_48 Inj_Z_Z 0x9bb4c eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_48.
Definition B_MEMCPY_PC_OFF_50 : Z := 0x9bb54.   (* symbol memcpy + 0x50 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_50 : @CstOp Z Z B_MEMCPY_PC_OFF_50 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_50 Inj_Z_Z 0x9bb54 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_50.
Definition B_MEMCPY_PC_OFF_58 : Z := 0x9bb5c.   (* symbol memcpy + 0x58 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_58 : @CstOp Z Z B_MEMCPY_PC_OFF_58 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_58 Inj_Z_Z 0x9bb5c eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_58.
Definition B_MEMCPY_PC_OFF_60 : Z := 0x9bb64.   (* symbol memcpy + 0x60 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_60 : @CstOp Z Z B_MEMCPY_PC_OFF_60 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_60 Inj_Z_Z 0x9bb64 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_60.
Definition B_MEMCPY_PC_OFF_68 : Z := 0x9bb6c.   (* symbol memcpy + 0x68 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_68 : @CstOp Z Z B_MEMCPY_PC_OFF_68 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_68 Inj_Z_Z 0x9bb6c eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_68.
Definition B_MEMCPY_PC_OFF_74 : Z := 0x9bb78.   (* symbol memcpy + 0x74 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_74 : @CstOp Z Z B_MEMCPY_PC_OFF_74 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_74 Inj_Z_Z 0x9bb78 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_74.
Definition B_MEMCPY_PC_OFF_A4 : Z := 0x9bba8.   (* symbol memcpy + 0xa4 *)
#[export] Instance Op_B_MEMCPY_PC_OFF_A4 : @CstOp Z Z B_MEMCPY_PC_OFF_A4 Inj_Z_Z := @mkcst Z Z B_MEMCPY_PC_OFF_A4 Inj_Z_Z 0x9bba8 eq_refl.
Add Zify CstOp Op_B_MEMCPY_PC_OFF_A4.
Definition B_MEMORYMAPPER_EEPN_ALLOCATORSTATS_OFF_1B4 : Z := 0x353ec.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17ReturnToAllocatorEPNS_12MemoryMapperIS5_EEPNS_14AllocatorStatsEmPKjm + 0x1b4 *)
#[export] Instance Op_B_MEMORYMAPPER_EEPN_ALLOCATORSTATS_OFF_1B4 : @CstOp Z Z B_MEMORYMAPPER_EEPN_ALLOCATORSTATS_OFF_1B4 Inj_Z_Z := @mkcst Z Z B_MEMORYMAPPER_EEPN_ALLOCATORSTATS_OFF_1B4 Inj_Z_Z 0x353ec eq_refl.
Add Zify CstOp Op_B_MEMORYMAPPER_EEPN_ALLOCATORSTATS_OFF_1B4.
Definition B_MEMSET_PC : Z := 0x9bf08.   (* symbol memset (248 bytes) *)
#[export] Instance Op_B_MEMSET_PC : @CstOp Z Z B_MEMSET_PC Inj_Z_Z := @mkcst Z Z B_MEMSET_PC Inj_Z_Z 0x9bf08 eq_refl.
Add Zify CstOp Op_B_MEMSET_PC.
Definition B_MEMTOSHADOW_ASAN_FAKE_STACK_PC : Z := 0x3e0e4.   (* B place section .text + 0xcc84, rekeyed (a) *)
#[export] Instance Op_B_MEMTOSHADOW_ASAN_FAKE_STACK_PC : @CstOp Z Z B_MEMTOSHADOW_ASAN_FAKE_STACK_PC Inj_Z_Z := @mkcst Z Z B_MEMTOSHADOW_ASAN_FAKE_STACK_PC Inj_Z_Z 0x3e0e4 eq_refl.
Add Zify CstOp Op_B_MEMTOSHADOW_ASAN_FAKE_STACK_PC.
Definition B_MEMTOSHADOW_ASAN_POISONING_PC : Z := 0x54f08.   (* B place section .text + 0x23aa8, rekeyed (a) *)
#[export] Instance Op_B_MEMTOSHADOW_ASAN_POISONING_PC : @CstOp Z Z B_MEMTOSHADOW_ASAN_POISONING_PC Inj_Z_Z := @mkcst Z Z B_MEMTOSHADOW_ASAN_POISONING_PC Inj_Z_Z 0x54f08 eq_refl.
Add Zify CstOp Op_B_MEMTOSHADOW_ASAN_POISONING_PC.
Definition B_MEMTOSHADOW_PC_OFF_1C : Z := 0x53594.   (* B place section .text + 0x22134, rekeyed (a) *)
#[export] Instance Op_B_MEMTOSHADOW_PC_OFF_1C : @CstOp Z Z B_MEMTOSHADOW_PC_OFF_1C Inj_Z_Z := @mkcst Z Z B_MEMTOSHADOW_PC_OFF_1C Inj_Z_Z 0x53594 eq_refl.
Add Zify CstOp Op_B_MEMTOSHADOW_PC_OFF_1C.
Definition B_MEMTOSHADOW_PC_OFF_58 : Z := 0x535d0.   (* B place section .text + 0x22170, rekeyed (a) *)
#[export] Instance Op_B_MEMTOSHADOW_PC_OFF_58 : @CstOp Z Z B_MEMTOSHADOW_PC_OFF_58 Inj_Z_Z := @mkcst Z Z B_MEMTOSHADOW_PC_OFF_58 Inj_Z_Z 0x535d0 eq_refl.
Add Zify CstOp Op_B_MEMTOSHADOW_PC_OFF_58.
Definition B_MEM_IS_ZERO_PC : Z := 0x650d4.   (* symbol _ZN11__sanitizer11mem_is_zeroEPKcm (180 bytes) *)
#[export] Instance Op_B_MEM_IS_ZERO_PC : @CstOp Z Z B_MEM_IS_ZERO_PC Inj_Z_Z := @mkcst Z Z B_MEM_IS_ZERO_PC Inj_Z_Z 0x650d4 eq_refl.
Add Zify CstOp Op_B_MEM_IS_ZERO_PC.
Definition B_METADATA_MEM_OFF_8_CELL : Z := 0xaaf50.   (* symbol _ZZL28InitializeCommonInterceptorsvE12metadata_mem + 0x8 *)
#[export] Instance Op_B_METADATA_MEM_OFF_8_CELL : @CstOp Z Z B_METADATA_MEM_OFF_8_CELL Inj_Z_Z := @mkcst Z Z B_METADATA_MEM_OFF_8_CELL Inj_Z_Z 0xaaf50 eq_refl.
Add Zify CstOp Op_B_METADATA_MEM_OFF_8_CELL.
Definition B_MFHOOKS_CELL : Z := 0x13d1c0.   (* symbol _ZN11__sanitizerL7MFHooksE (80 bytes) *)
#[export] Instance Op_B_MFHOOKS_CELL : @CstOp Z Z B_MFHOOKS_CELL Inj_Z_Z := @mkcst Z Z B_MFHOOKS_CELL Inj_Z_Z 0x13d1c0 eq_refl.
Add Zify CstOp Op_B_MFHOOKS_CELL.
Definition B_MFHOOKS_OFF_8_CELL : Z := 0x13d1c8.   (* symbol _ZN11__sanitizerL7MFHooksE + 0x8 *)
#[export] Instance Op_B_MFHOOKS_OFF_8_CELL : @CstOp Z Z B_MFHOOKS_OFF_8_CELL Inj_Z_Z := @mkcst Z Z B_MFHOOKS_OFF_8_CELL Inj_Z_Z 0x13d1c8 eq_refl.
Add Zify CstOp Op_B_MFHOOKS_OFF_8_CELL.
Definition B_MMAPFIXEDIMPL_PC_OFF_AC : Z := 0x67168.   (* symbol _ZN11__sanitizerL13MmapFixedImplEmmbPKc + 0xac *)
#[export] Instance Op_B_MMAPFIXEDIMPL_PC_OFF_AC : @CstOp Z Z B_MMAPFIXEDIMPL_PC_OFF_AC Inj_Z_Z := @mkcst Z Z B_MMAPFIXEDIMPL_PC_OFF_AC Inj_Z_Z 0x67168 eq_refl.
Add Zify CstOp Op_B_MMAPFIXEDIMPL_PC_OFF_AC.
Definition B_MMAPFIXEDNORESERVE_PC : Z := 0x6f064.   (* symbol _ZN11__sanitizer18MmapFixedNoReserveEmmPKc (304 bytes) *)
#[export] Instance Op_B_MMAPFIXEDNORESERVE_PC : @CstOp Z Z B_MMAPFIXEDNORESERVE_PC Inj_Z_Z := @mkcst Z Z B_MMAPFIXEDNORESERVE_PC Inj_Z_Z 0x6f064 eq_refl.
Add Zify CstOp Op_B_MMAPFIXEDNORESERVE_PC.
Definition B_MMAPFIXEDNORESERVE_PC_OFF_C4 : Z := 0x6f128.   (* symbol _ZN11__sanitizer18MmapFixedNoReserveEmmPKc + 0xc4 *)
#[export] Instance Op_B_MMAPFIXEDNORESERVE_PC_OFF_C4 : @CstOp Z Z B_MMAPFIXEDNORESERVE_PC_OFF_C4 Inj_Z_Z := @mkcst Z Z B_MMAPFIXEDNORESERVE_PC_OFF_C4 Inj_Z_Z 0x6f128 eq_refl.
Add Zify CstOp Op_B_MMAPFIXEDNORESERVE_PC_OFF_C4.
Definition B_MMAPFIXEDORDIE_PC : Z := 0x670b0.   (* symbol _ZN11__sanitizer14MmapFixedOrDieEmmPKc (12 bytes) *)
#[export] Instance Op_B_MMAPFIXEDORDIE_PC : @CstOp Z Z B_MMAPFIXEDORDIE_PC Inj_Z_Z := @mkcst Z Z B_MMAPFIXEDORDIE_PC Inj_Z_Z 0x670b0 eq_refl.
Add Zify CstOp Op_B_MMAPFIXEDORDIE_PC.
Definition B_MMAPNAMED_PC : Z := 0x66b80.   (* symbol _ZN11__sanitizer9MmapNamedEPvmiiPKc (116 bytes) *)
#[export] Instance Op_B_MMAPNAMED_PC : @CstOp Z Z B_MMAPNAMED_PC Inj_Z_Z := @mkcst Z Z B_MMAPNAMED_PC Inj_Z_Z 0x66b80 eq_refl.
Add Zify CstOp Op_B_MMAPNAMED_PC.
Definition B_MMAPORDIEONFATALERROR_PC : Z := 0x66c70.   (* symbol _ZN11__sanitizer21MmapOrDieOnFatalErrorEmPKc (272 bytes) *)
#[export] Instance Op_B_MMAPORDIEONFATALERROR_PC : @CstOp Z Z B_MMAPORDIEONFATALERROR_PC Inj_Z_Z := @mkcst Z Z B_MMAPORDIEONFATALERROR_PC Inj_Z_Z 0x66c70 eq_refl.
Add Zify CstOp Op_B_MMAPORDIEONFATALERROR_PC.
Definition B_MMAPORDIEONFATALERROR_PC_OFF_88 : Z := 0x66cf8.   (* symbol _ZN11__sanitizer21MmapOrDieOnFatalErrorEmPKc + 0x88 *)
#[export] Instance Op_B_MMAPORDIEONFATALERROR_PC_OFF_88 : @CstOp Z Z B_MMAPORDIEONFATALERROR_PC_OFF_88 Inj_Z_Z := @mkcst Z Z B_MMAPORDIEONFATALERROR_PC_OFF_88 Inj_Z_Z 0x66cf8 eq_refl.
Add Zify CstOp Op_B_MMAPORDIEONFATALERROR_PC_OFF_88.
Definition B_MU_FOR_GLOBALS_CELL : Z := 0xa8fb0.   (* symbol _ZN6__asanL14mu_for_globalsE (16 bytes) *)
#[export] Instance Op_B_MU_FOR_GLOBALS_CELL : @CstOp Z Z B_MU_FOR_GLOBALS_CELL Inj_Z_Z := @mkcst Z Z B_MU_FOR_GLOBALS_CELL Inj_Z_Z 0xa8fb0 eq_refl.
Add Zify CstOp Op_B_MU_FOR_GLOBALS_CELL.
Definition B_MU_FOR_GLOBALS_OFF_8_CELL : Z := 0xa8fb8.   (* symbol _ZN6__asanL14mu_for_globalsE + 0x8 *)
#[export] Instance Op_B_MU_FOR_GLOBALS_OFF_8_CELL : @CstOp Z Z B_MU_FOR_GLOBALS_OFF_8_CELL Inj_Z_Z := @mkcst Z Z B_MU_FOR_GLOBALS_OFF_8_CELL Inj_Z_Z 0xa8fb8 eq_refl.
Add Zify CstOp Op_B_MU_FOR_GLOBALS_OFF_8_CELL.
Definition B_NEWWORKNOTIFY_PC : Z := 0x73460.   (* symbol _ZN11__sanitizer12_GLOBAL__N_114CompressThread13NewWorkNotifyEv (268 bytes) *)
#[export] Instance Op_B_NEWWORKNOTIFY_PC : @CstOp Z Z B_NEWWORKNOTIFY_PC Inj_Z_Z := @mkcst Z Z B_NEWWORKNOTIFY_PC Inj_Z_Z 0x73460 eq_refl.
Add Zify CstOp Op_B_NEWWORKNOTIFY_PC.
Definition B_OFL_HEAD_CELL : Z := 0x5fee28.   (* symbol ofl_head (8 bytes) *)
#[export] Instance Op_B_OFL_HEAD_CELL : @CstOp Z Z B_OFL_HEAD_CELL Inj_Z_Z := @mkcst Z Z B_OFL_HEAD_CELL Inj_Z_Z 0x5fee28 eq_refl.
Add Zify CstOp Op_B_OFL_HEAD_CELL.
Definition B_OFL_LOCK_CELL : Z := 0x5fee20.   (* symbol ofl_lock (4 bytes) *)
#[export] Instance Op_B_OFL_LOCK_CELL : @CstOp Z Z B_OFL_LOCK_CELL Inj_Z_Z := @mkcst Z Z B_OFL_LOCK_CELL Inj_Z_Z 0x5fee20 eq_refl.
Add Zify CstOp Op_B_OFL_LOCK_CELL.
Definition B_OFT_EXIT_GUARD_PC : Z := 0x81654.   (* symbol oft_exit_guard (48 bytes) *)
#[export] Instance Op_B_OFT_EXIT_GUARD_PC : @CstOp Z Z B_OFT_EXIT_GUARD_PC Inj_Z_Z := @mkcst Z Z B_OFT_EXIT_GUARD_PC Inj_Z_Z 0x81654 eq_refl.
Add Zify CstOp Op_B_OFT_EXIT_GUARD_PC.
Definition B_OFT_IN_CALLBACK_CELL : Z := 0x5ddd54.   (* symbol oft_in_callback (1 bytes) *)
#[export] Instance Op_B_OFT_IN_CALLBACK_CELL : @CstOp Z Z B_OFT_IN_CALLBACK_CELL Inj_Z_Z := @mkcst Z Z B_OFT_IN_CALLBACK_CELL Inj_Z_Z 0x5ddd54 eq_refl.
Add Zify CstOp Op_B_OFT_IN_CALLBACK_CELL.
Definition B_OFT_IN_CALLBACK_OFF_1_END_CELL : Z := 0x5ddd55.   (* symbol oft_in_callback + 0x1 *)
#[export] Instance Op_B_OFT_IN_CALLBACK_OFF_1_END_CELL : @CstOp Z Z B_OFT_IN_CALLBACK_OFF_1_END_CELL Inj_Z_Z := @mkcst Z Z B_OFT_IN_CALLBACK_OFF_1_END_CELL Inj_Z_Z 0x5ddd55 eq_refl.
Add Zify CstOp Op_B_OFT_IN_CALLBACK_OFF_1_END_CELL.
Definition B_OPEN_PC : Z := 0x8fda8.   (* symbol open (228 bytes) *)
#[export] Instance Op_B_OPEN_PC : @CstOp Z Z B_OPEN_PC Inj_Z_Z := @mkcst Z Z B_OPEN_PC Inj_Z_Z 0x8fda8 eq_refl.
Add Zify CstOp Op_B_OPEN_PC.
Definition B_PAGESIZECACHED_CELL : Z := 0x13b1a0.   (* symbol _ZN11__sanitizer14PageSizeCachedE (8 bytes) *)
#[export] Instance Op_B_PAGESIZECACHED_CELL : @CstOp Z Z B_PAGESIZECACHED_CELL Inj_Z_Z := @mkcst Z Z B_PAGESIZECACHED_CELL Inj_Z_Z 0x13b1a0 eq_refl.
Add Zify CstOp Op_B_PAGESIZECACHED_CELL.
Definition B_PC_GUARD_CONTROLLER_CELL : Z := 0x13d5a0.   (* symbol _ZN8__sancov12_GLOBAL__N_119pc_guard_controllerE (32 bytes) *)
#[export] Instance Op_B_PC_GUARD_CONTROLLER_CELL : @CstOp Z Z B_PC_GUARD_CONTROLLER_CELL Inj_Z_Z := @mkcst Z Z B_PC_GUARD_CONTROLLER_CELL Inj_Z_Z 0x13d5a0 eq_refl.
Add Zify CstOp Op_B_PC_GUARD_CONTROLLER_CELL.
Definition B_POISONSHADOW_PC : Z := 0x54a0c.   (* symbol _ZN6__asan12PoisonShadowEmmh (1276 bytes) *)
#[export] Instance Op_B_POISONSHADOW_PC : @CstOp Z Z B_POISONSHADOW_PC Inj_Z_Z := @mkcst Z Z B_POISONSHADOW_PC Inj_Z_Z 0x54a0c eq_refl.
Add Zify CstOp Op_B_POISONSHADOW_PC.
Definition B_POISONSHADOW_PC_OFF_240 : Z := 0x54c4c.   (* symbol _ZN6__asan12PoisonShadowEmmh + 0x240 *)
#[export] Instance Op_B_POISONSHADOW_PC_OFF_240 : @CstOp Z Z B_POISONSHADOW_PC_OFF_240 Inj_Z_Z := @mkcst Z Z B_POISONSHADOW_PC_OFF_240 Inj_Z_Z 0x54c4c eq_refl.
Add Zify CstOp Op_B_POISONSHADOW_PC_OFF_240.
Definition B_POISONSHADOW_PC_OFF_27C : Z := 0x54c88.   (* symbol _ZN6__asan12PoisonShadowEmmh + 0x27c *)
#[export] Instance Op_B_POISONSHADOW_PC_OFF_27C : @CstOp Z Z B_POISONSHADOW_PC_OFF_27C Inj_Z_Z := @mkcst Z Z B_POISONSHADOW_PC_OFF_27C Inj_Z_Z 0x54c88 eq_refl.
Add Zify CstOp Op_B_POISONSHADOW_PC_OFF_27C.
Definition B_POISONSHADOW_PC_OFF_280 : Z := 0x54c8c.   (* symbol _ZN6__asan12PoisonShadowEmmh + 0x280 *)
#[export] Instance Op_B_POISONSHADOW_PC_OFF_280 : @CstOp Z Z B_POISONSHADOW_PC_OFF_280 Inj_Z_Z := @mkcst Z Z B_POISONSHADOW_PC_OFF_280 Inj_Z_Z 0x54c8c eq_refl.
Add Zify CstOp Op_B_POISONSHADOW_PC_OFF_280.
Definition B_POISONSHADOW_PC_OFF_284 : Z := 0x54c90.   (* symbol _ZN6__asan12PoisonShadowEmmh + 0x284 *)
#[export] Instance Op_B_POISONSHADOW_PC_OFF_284 : @CstOp Z Z B_POISONSHADOW_PC_OFF_284 Inj_Z_Z := @mkcst Z Z B_POISONSHADOW_PC_OFF_284 Inj_Z_Z 0x54c90 eq_refl.
Add Zify CstOp Op_B_POISONSHADOW_PC_OFF_284.
Definition B_POISONSHADOW_PC_OFF_2A8 : Z := 0x54cb4.   (* symbol _ZN6__asan12PoisonShadowEmmh + 0x2a8 *)
#[export] Instance Op_B_POISONSHADOW_PC_OFF_2A8 : @CstOp Z Z B_POISONSHADOW_PC_OFF_2A8 Inj_Z_Z := @mkcst Z Z B_POISONSHADOW_PC_OFF_2A8 Inj_Z_Z 0x54cb4 eq_refl.
Add Zify CstOp Op_B_POISONSHADOW_PC_OFF_2A8.
Definition B_POISONSHADOW_PC_OFF_2B8 : Z := 0x54cc4.   (* symbol _ZN6__asan12PoisonShadowEmmh + 0x2b8 *)
#[export] Instance Op_B_POISONSHADOW_PC_OFF_2B8 : @CstOp Z Z B_POISONSHADOW_PC_OFF_2B8 Inj_Z_Z := @mkcst Z Z B_POISONSHADOW_PC_OFF_2B8 Inj_Z_Z 0x54cc4 eq_refl.
Add Zify CstOp Op_B_POISONSHADOW_PC_OFF_2B8.
Definition B_POISONSHADOW_PC_OFF_58 : Z := 0x54a64.   (* symbol _ZN6__asan12PoisonShadowEmmh + 0x58 *)
#[export] Instance Op_B_POISONSHADOW_PC_OFF_58 : @CstOp Z Z B_POISONSHADOW_PC_OFF_58 Inj_Z_Z := @mkcst Z Z B_POISONSHADOW_PC_OFF_58 Inj_Z_Z 0x54a64 eq_refl.
Add Zify CstOp Op_B_POISONSHADOW_PC_OFF_58.
Definition B_POISONSHADOW_PC_OFF_98 : Z := 0x54aa4.   (* symbol _ZN6__asan12PoisonShadowEmmh + 0x98 *)
#[export] Instance Op_B_POISONSHADOW_PC_OFF_98 : @CstOp Z Z B_POISONSHADOW_PC_OFF_98 Inj_Z_Z := @mkcst Z Z B_POISONSHADOW_PC_OFF_98 Inj_Z_Z 0x54aa4 eq_refl.
Add Zify CstOp Op_B_POISONSHADOW_PC_OFF_98.
Definition B_POPULATEFREEARRAY_ALLOCATORSTATS_10RE_OFF_5C : Z := 0x378f8.   (* symbol _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm + 0x5c *)
#[export] Instance Op_B_POPULATEFREEARRAY_ALLOCATORSTATS_10RE_OFF_5C : @CstOp Z Z B_POPULATEFREEARRAY_ALLOCATORSTATS_10RE_OFF_5C Inj_Z_Z := @mkcst Z Z B_POPULATEFREEARRAY_ALLOCATORSTATS_10RE_OFF_5C Inj_Z_Z 0x378f8 eq_refl.
Add Zify CstOp Op_B_POPULATEFREEARRAY_ALLOCATORSTATS_10RE_OFF_5C.
Definition B_PREINIT_CELL : Z := 0xa2270.   (* symbol _ZL7preinit (8 bytes) *)
#[export] Instance Op_B_PREINIT_CELL : @CstOp Z Z B_PREINIT_CELL Inj_Z_Z := @mkcst Z Z B_PREINIT_CELL Inj_Z_Z 0xa2270 eq_refl.
Add Zify CstOp Op_B_PREINIT_CELL.
Definition B_PRINTF_COMMON_PC_OFF_48C : Z := 0x45c18.   (* symbol _ZL13printf_commonPvPKcS_ + 0x48c *)
#[export] Instance Op_B_PRINTF_COMMON_PC_OFF_48C : @CstOp Z Z B_PRINTF_COMMON_PC_OFF_48C Inj_Z_Z := @mkcst Z Z B_PRINTF_COMMON_PC_OFF_48C Inj_Z_Z 0x45c18 eq_refl.
Add Zify CstOp Op_B_PRINTF_COMMON_PC_OFF_48C.
Definition B_PRINTF_COMMON_PC_OFF_4B4 : Z := 0x45c40.   (* symbol _ZL13printf_commonPvPKcS_ + 0x4b4 *)
#[export] Instance Op_B_PRINTF_COMMON_PC_OFF_4B4 : @CstOp Z Z B_PRINTF_COMMON_PC_OFF_4B4 Inj_Z_Z := @mkcst Z Z B_PRINTF_COMMON_PC_OFF_4B4 Inj_Z_Z 0x45c40 eq_refl.
Add Zify CstOp Op_B_PRINTF_COMMON_PC_OFF_4B4.
Definition B_PRINTF_COMMON_PC_OFF_52C : Z := 0x45cb8.   (* symbol _ZL13printf_commonPvPKcS_ + 0x52c *)
#[export] Instance Op_B_PRINTF_COMMON_PC_OFF_52C : @CstOp Z Z B_PRINTF_COMMON_PC_OFF_52C Inj_Z_Z := @mkcst Z Z B_PRINTF_COMMON_PC_OFF_52C Inj_Z_Z 0x45cb8 eq_refl.
Add Zify CstOp Op_B_PRINTF_COMMON_PC_OFF_52C.
Definition B_PRINTF_COMMON_PC_OFF_574 : Z := 0x45d00.   (* symbol _ZL13printf_commonPvPKcS_ + 0x574 *)
#[export] Instance Op_B_PRINTF_COMMON_PC_OFF_574 : @CstOp Z Z B_PRINTF_COMMON_PC_OFF_574 Inj_Z_Z := @mkcst Z Z B_PRINTF_COMMON_PC_OFF_574 Inj_Z_Z 0x45d00 eq_refl.
Add Zify CstOp Op_B_PRINTF_COMMON_PC_OFF_574.
Definition B_PRINTF_COMMON_PC_OFF_578 : Z := 0x45d04.   (* symbol _ZL13printf_commonPvPKcS_ + 0x578 *)
#[export] Instance Op_B_PRINTF_COMMON_PC_OFF_578 : @CstOp Z Z B_PRINTF_COMMON_PC_OFF_578 Inj_Z_Z := @mkcst Z Z B_PRINTF_COMMON_PC_OFF_578 Inj_Z_Z 0x45d04 eq_refl.
Add Zify CstOp Op_B_PRINTF_COMMON_PC_OFF_578.
Definition B_PRINTF_CORE_PC_OFF_618 : Z := 0x965f4.   (* symbol printf_core + 0x618 *)
#[export] Instance Op_B_PRINTF_CORE_PC_OFF_618 : @CstOp Z Z B_PRINTF_CORE_PC_OFF_618 Inj_Z_Z := @mkcst Z Z B_PRINTF_CORE_PC_OFF_618 Inj_Z_Z 0x965f4 eq_refl.
Add Zify CstOp Op_B_PRINTF_CORE_PC_OFF_618.
Definition B_PRINTF_CORE_PC_OFF_620 : Z := 0x965fc.   (* symbol printf_core + 0x620 *)
#[export] Instance Op_B_PRINTF_CORE_PC_OFF_620 : @CstOp Z Z B_PRINTF_CORE_PC_OFF_620 Inj_Z_Z := @mkcst Z Z B_PRINTF_CORE_PC_OFF_620 Inj_Z_Z 0x965fc eq_refl.
Add Zify CstOp Op_B_PRINTF_CORE_PC_OFF_620.
Definition B_PRINTF_CORE_PC_OFF_624 : Z := 0x96600.   (* symbol printf_core + 0x624 *)
#[export] Instance Op_B_PRINTF_CORE_PC_OFF_624 : @CstOp Z Z B_PRINTF_CORE_PC_OFF_624 Inj_Z_Z := @mkcst Z Z B_PRINTF_CORE_PC_OFF_624 Inj_Z_Z 0x96600 eq_refl.
Add Zify CstOp Op_B_PRINTF_CORE_PC_OFF_624.
Definition B_PTHREAD_GETSPECIFIC_PC : Z := 0x9d7ac.   (* symbol __pthread_getspecific (28 bytes) *)
#[export] Instance Op_B_PTHREAD_GETSPECIFIC_PC : @CstOp Z Z B_PTHREAD_GETSPECIFIC_PC Inj_Z_Z := @mkcst Z Z B_PTHREAD_GETSPECIFIC_PC Inj_Z_Z 0x9d7ac eq_refl.
Add Zify CstOp Op_B_PTHREAD_GETSPECIFIC_PC.
Definition B_PTHREAD_TSD_MAIN_CELL : Z := 0x5ffad8.   (* symbol __pthread_tsd_main (1024 bytes) *)
#[export] Instance Op_B_PTHREAD_TSD_MAIN_CELL : @CstOp Z Z B_PTHREAD_TSD_MAIN_CELL Inj_Z_Z := @mkcst Z Z B_PTHREAD_TSD_MAIN_CELL Inj_Z_Z 0x5ffad8 eq_refl.
Add Zify CstOp Op_B_PTHREAD_TSD_MAIN_CELL.
Definition B_P_PC_OFF_154 : Z := 0x36cb4.   (* symbol _ZN11__sanitizer15QuarantineCacheIN6__asan18QuarantineCallbackEE7EnqueueES2_Pvm + 0x154 *)
#[export] Instance Op_B_P_PC_OFF_154 : @CstOp Z Z B_P_PC_OFF_154 Inj_Z_Z := @mkcst Z Z B_P_PC_OFF_154 Inj_Z_Z 0x36cb4 eq_refl.
Add Zify CstOp Op_B_P_PC_OFF_154.
Definition B_P_PC_OFF_18C : Z := 0x36b3c.   (* symbol _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE3PutEPNS_15QuarantineCacheIS2_EES2_PS3_m + 0x18c *)
#[export] Instance Op_B_P_PC_OFF_18C : @CstOp Z Z B_P_PC_OFF_18C Inj_Z_Z := @mkcst Z Z B_P_PC_OFF_18C Inj_Z_Z 0x36b3c eq_refl.
Add Zify CstOp Op_B_P_PC_OFF_18C.
Definition B_P_PC_OFF_190 : Z := 0x36cf0.   (* symbol _ZN11__sanitizer15QuarantineCacheIN6__asan18QuarantineCallbackEE7EnqueueES2_Pvm + 0x190 *)
#[export] Instance Op_B_P_PC_OFF_190 : @CstOp Z Z B_P_PC_OFF_190 Inj_Z_Z := @mkcst Z Z B_P_PC_OFF_190 Inj_Z_Z 0x36cf0 eq_refl.
Add Zify CstOp Op_B_P_PC_OFF_190.
Definition B_P_PC_OFF_1A4 : Z := 0x36b54.   (* symbol _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE3PutEPNS_15QuarantineCacheIS2_EES2_PS3_m + 0x1a4 *)
#[export] Instance Op_B_P_PC_OFF_1A4 : @CstOp Z Z B_P_PC_OFF_1A4 Inj_Z_Z := @mkcst Z Z B_P_PC_OFF_1A4 Inj_Z_Z 0x36b54 eq_refl.
Add Zify CstOp Op_B_P_PC_OFF_1A4.
Definition B_P_PC_OFF_54 : Z := 0x36bb4.   (* symbol _ZN11__sanitizer15QuarantineCacheIN6__asan18QuarantineCallbackEE7EnqueueES2_Pvm + 0x54 *)
#[export] Instance Op_B_P_PC_OFF_54 : @CstOp Z Z B_P_PC_OFF_54 Inj_Z_Z := @mkcst Z Z B_P_PC_OFF_54 Inj_Z_Z 0x36bb4 eq_refl.
Add Zify CstOp Op_B_P_PC_OFF_54.
Definition B_P_PC_OFF_84 : Z := 0x36be4.   (* symbol _ZN11__sanitizer15QuarantineCacheIN6__asan18QuarantineCallbackEE7EnqueueES2_Pvm + 0x84 *)
#[export] Instance Op_B_P_PC_OFF_84 : @CstOp Z Z B_P_PC_OFF_84 Inj_Z_Z := @mkcst Z Z B_P_PC_OFF_84 Inj_Z_Z 0x36be4 eq_refl.
Add Zify CstOp Op_B_P_PC_OFF_84.
Definition B_QUARANTINECACHE_E_P_OFF_DC : Z := 0x36a8c.   (* symbol _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE3PutEPNS_15QuarantineCacheIS2_EES2_PS3_m + 0xdc *)
#[export] Instance Op_B_QUARANTINECACHE_E_P_OFF_DC : @CstOp Z Z B_QUARANTINECACHE_E_P_OFF_DC Inj_Z_Z := @mkcst Z Z B_QUARANTINECACHE_E_P_OFF_DC Inj_Z_Z 0x36a8c eq_refl.
Add Zify CstOp Op_B_QUARANTINECACHE_E_P_OFF_DC.
Definition B_QUARANTINECACHE_E_P_PC : Z := 0x369b0.   (* symbol _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE3PutEPNS_15QuarantineCacheIS2_EES2_PS3_m (432 bytes) *)
#[export] Instance Op_B_QUARANTINECACHE_E_P_PC : @CstOp Z Z B_QUARANTINECACHE_E_P_PC Inj_Z_Z := @mkcst Z Z B_QUARANTINECACHE_E_P_PC Inj_Z_Z 0x369b0 eq_refl.
Add Zify CstOp Op_B_QUARANTINECACHE_E_P_PC.
Definition B_QUARANTINECALLBACK_ENQUEUE_P_OFF_DC : Z := 0x36c3c.   (* symbol _ZN11__sanitizer15QuarantineCacheIN6__asan18QuarantineCallbackEE7EnqueueES2_Pvm + 0xdc *)
#[export] Instance Op_B_QUARANTINECALLBACK_ENQUEUE_P_OFF_DC : @CstOp Z Z B_QUARANTINECALLBACK_ENQUEUE_P_OFF_DC Inj_Z_Z := @mkcst Z Z B_QUARANTINECALLBACK_ENQUEUE_P_OFF_DC Inj_Z_Z 0x36c3c eq_refl.
Add Zify CstOp Op_B_QUARANTINECALLBACK_ENQUEUE_P_OFF_DC.
Definition B_QUARANTINECALLBACK_ENQUEUE_P_PC : Z := 0x36b60.   (* symbol _ZN11__sanitizer15QuarantineCacheIN6__asan18QuarantineCallbackEE7EnqueueES2_Pvm (484 bytes) *)
#[export] Instance Op_B_QUARANTINECALLBACK_ENQUEUE_P_PC : @CstOp Z Z B_QUARANTINECALLBACK_ENQUEUE_P_PC Inj_Z_Z := @mkcst Z Z B_QUARANTINECALLBACK_ENQUEUE_P_PC Inj_Z_Z 0x36b60 eq_refl.
Add Zify CstOp Op_B_QUARANTINECALLBACK_ENQUEUE_P_PC.
Definition B_QUARANTINECHUNK_ASANCHUNK_BUFFEREDSTACKTRACE_PC : Z := 0x36838.   (* symbol _ZN6__asan9Allocator15QuarantineChunkEPNS_9AsanChunkEPvPN11__sanitizer18BufferedStackTraceE (376 bytes) *)
#[export] Instance Op_B_QUARANTINECHUNK_ASANCHUNK_BUFFEREDSTACKTRACE_PC : @CstOp Z Z B_QUARANTINECHUNK_ASANCHUNK_BUFFEREDSTACKTRACE_PC Inj_Z_Z := @mkcst Z Z B_QUARANTINECHUNK_ASANCHUNK_BUFFEREDSTACKTRACE_PC Inj_Z_Z 0x36838 eq_refl.
Add Zify CstOp Op_B_QUARANTINECHUNK_ASANCHUNK_BUFFEREDSTACKTRACE_PC.
Definition B_READ_PC : Z := 0xa1208.   (* symbol read (52 bytes) *)
#[export] Instance Op_B_READ_PC : @CstOp Z Z B_READ_PC Inj_Z_Z := @mkcst Z Z B_READ_PC Inj_Z_Z 0xa1208 eq_refl.
Add Zify CstOp Op_B_READ_PC.
Definition B_READ_STAGE_CELL : Z := 0x5cdd50.   (* symbol read_stage (65536 bytes) *)
#[export] Instance Op_B_READ_STAGE_CELL : @CstOp Z Z B_READ_STAGE_CELL Inj_Z_Z := @mkcst Z Z B_READ_STAGE_CELL Inj_Z_Z 0x5cdd50 eq_refl.
Add Zify CstOp Op_B_READ_STAGE_CELL.
Definition B_REAL_FFLUSH_CELL : Z := 0xa4610.   (* symbol _ZN14__interception11real_fflushE (8 bytes) *)
#[export] Instance Op_B_REAL_FFLUSH_CELL : @CstOp Z Z B_REAL_FFLUSH_CELL Inj_Z_Z := @mkcst Z Z B_REAL_FFLUSH_CELL Inj_Z_Z 0xa4610 eq_refl.
Add Zify CstOp Op_B_REAL_FFLUSH_CELL.
Definition B_REAL_FWRITE_CELL : Z := 0xa45a8.   (* symbol _ZN14__interception11real_fwriteE (8 bytes) *)
#[export] Instance Op_B_REAL_FWRITE_CELL : @CstOp Z Z B_REAL_FWRITE_CELL Inj_Z_Z := @mkcst Z Z B_REAL_FWRITE_CELL Inj_Z_Z 0xa45a8 eq_refl.
Add Zify CstOp Op_B_REAL_FWRITE_CELL.
Definition B_REAL_MEMCHR_CELL : Z := 0xa4590.   (* symbol _ZN14__interception11real_memchrE (8 bytes) *)
#[export] Instance Op_B_REAL_MEMCHR_CELL : @CstOp Z Z B_REAL_MEMCHR_CELL Inj_Z_Z := @mkcst Z Z B_REAL_MEMCHR_CELL Inj_Z_Z 0xa4590 eq_refl.
Add Zify CstOp Op_B_REAL_MEMCHR_CELL.
Definition B_REAL_MEMCPY_CELL : Z := 0xa46c8.   (* symbol _ZN14__interception11real_memcpyE (8 bytes) *)
#[export] Instance Op_B_REAL_MEMCPY_CELL : @CstOp Z Z B_REAL_MEMCPY_CELL Inj_Z_Z := @mkcst Z Z B_REAL_MEMCPY_CELL Inj_Z_Z 0xa46c8 eq_refl.
Add Zify CstOp Op_B_REAL_MEMCPY_CELL.
Definition B_REAL_MEMSET_CELL : Z := 0xa46d0.   (* symbol _ZN14__interception11real_memsetE (8 bytes) *)
#[export] Instance Op_B_REAL_MEMSET_CELL : @CstOp Z Z B_REAL_MEMSET_CELL Inj_Z_Z := @mkcst Z Z B_REAL_MEMSET_CELL Inj_Z_Z 0xa46d0 eq_refl.
Add Zify CstOp Op_B_REAL_MEMSET_CELL.
Definition B_REAL_READ_CELL : Z := 0xa45a0.   (* symbol _ZN14__interception9real_readE (8 bytes) *)
#[export] Instance Op_B_REAL_READ_CELL : @CstOp Z Z B_REAL_READ_CELL Inj_Z_Z := @mkcst Z Z B_REAL_READ_CELL Inj_Z_Z 0xa45a0 eq_refl.
Add Zify CstOp Op_B_REAL_READ_CELL.
Definition B_REAL_STRCHR_CELL : Z := 0xa4578.   (* symbol _ZN14__interception11real_strchrE (8 bytes) *)
#[export] Instance Op_B_REAL_STRCHR_CELL : @CstOp Z Z B_REAL_STRCHR_CELL Inj_Z_Z := @mkcst Z Z B_REAL_STRCHR_CELL Inj_Z_Z 0xa4578 eq_refl.
Add Zify CstOp Op_B_REAL_STRCHR_CELL.
Definition B_REAL_STRNLEN_CELL : Z := 0xa4678.   (* symbol _ZN14__interception12real_strnlenE (8 bytes) *)
#[export] Instance Op_B_REAL_STRNLEN_CELL : @CstOp Z Z B_REAL_STRNLEN_CELL Inj_Z_Z := @mkcst Z Z B_REAL_STRNLEN_CELL Inj_Z_Z 0xa4678 eq_refl.
Add Zify CstOp Op_B_REAL_STRNLEN_CELL.
Definition B_REAL_TLS_GET_ADDR_CELL : Z := 0xa4608.   (* symbol _ZN14__interception19real___tls_get_addrE (8 bytes) *)
#[export] Instance Op_B_REAL_TLS_GET_ADDR_CELL : @CstOp Z Z B_REAL_TLS_GET_ADDR_CELL Inj_Z_Z := @mkcst Z Z B_REAL_TLS_GET_ADDR_CELL Inj_Z_Z 0xa4608 eq_refl.
Add Zify CstOp Op_B_REAL_TLS_GET_ADDR_CELL.
Definition B_REAL_VFPRINTF_CELL : Z := 0xa45c8.   (* symbol _ZN14__interception13real_vfprintfE (8 bytes) *)
#[export] Instance Op_B_REAL_VFPRINTF_CELL : @CstOp Z Z B_REAL_VFPRINTF_CELL Inj_Z_Z := @mkcst Z Z B_REAL_VFPRINTF_CELL Inj_Z_Z 0xa45c8 eq_refl.
Add Zify CstOp Op_B_REAL_VFPRINTF_CELL.
Definition B_REAL_VPRINTF_CELL : Z := 0xa45c0.   (* symbol _ZN14__interception12real_vprintfE (8 bytes) *)
#[export] Instance Op_B_REAL_VPRINTF_CELL : @CstOp Z Z B_REAL_VPRINTF_CELL Inj_Z_Z := @mkcst Z Z B_REAL_VPRINTF_CELL Inj_Z_Z 0xa45c0 eq_refl.
Add Zify CstOp Op_B_REAL_VPRINTF_CELL.
Definition B_RECYCLE_PC : Z := 0x3445c.   (* symbol _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE7RecycleEmS2_ (484 bytes) *)
#[export] Instance Op_B_RECYCLE_PC : @CstOp Z Z B_RECYCLE_PC Inj_Z_Z := @mkcst Z Z B_RECYCLE_PC Inj_Z_Z 0x3445c eq_refl.
Add Zify CstOp Op_B_RECYCLE_PC.
Definition B_RECYCLE_PC_OFF_170 : Z := 0x345cc.   (* symbol _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE7RecycleEmS2_ + 0x170 *)
#[export] Instance Op_B_RECYCLE_PC_OFF_170 : @CstOp Z Z B_RECYCLE_PC_OFF_170 Inj_Z_Z := @mkcst Z Z B_RECYCLE_PC_OFF_170 Inj_Z_Z 0x345cc eq_refl.
Add Zify CstOp Op_B_RECYCLE_PC_OFF_170.
Definition B_RECYCLE_PC_OFF_FC : Z := 0x34558.   (* symbol _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE7RecycleEmS2_ + 0xfc *)
#[export] Instance Op_B_RECYCLE_PC_OFF_FC : @CstOp Z Z B_RECYCLE_PC_OFF_FC Inj_Z_Z := @mkcst Z Z B_RECYCLE_PC_OFF_FC Inj_Z_Z 0x34558 eq_refl.
Add Zify CstOp Op_B_RECYCLE_PC_OFF_FC.
Definition B_RELEASEMEMORYPAGESTOOS_PC : Z := 0x6e7a4.   (* symbol _ZN11__sanitizer22ReleaseMemoryPagesToOSEmm (164 bytes) *)
#[export] Instance Op_B_RELEASEMEMORYPAGESTOOS_PC : @CstOp Z Z B_RELEASEMEMORYPAGESTOOS_PC Inj_Z_Z := @mkcst Z Z B_RELEASEMEMORYPAGESTOOS_PC Inj_Z_Z 0x6e7a4 eq_refl.
Add Zify CstOp Op_B_RELEASEMEMORYPAGESTOOS_PC.
Definition B_RELRO_PADDING_HI : Z := 0xa4000.   (* end of section .relro_padding (addr + size) *)
#[export] Instance Op_B_RELRO_PADDING_HI : @CstOp Z Z B_RELRO_PADDING_HI Inj_Z_Z := @mkcst Z Z B_RELRO_PADDING_HI Inj_Z_Z 0xa4000 eq_refl.
Add Zify CstOp Op_B_RELRO_PADDING_HI.
Definition B_REPLACE_INTRIN_CACHED_CELL : Z := 0xac3d9.   (* symbol _ZN6__asan21replace_intrin_cachedE (1 bytes) *)
#[export] Instance Op_B_REPLACE_INTRIN_CACHED_CELL : @CstOp Z Z B_REPLACE_INTRIN_CACHED_CELL Inj_Z_Z := @mkcst Z Z B_REPLACE_INTRIN_CACHED_CELL Inj_Z_Z 0xac3d9 eq_refl.
Add Zify CstOp Op_B_REPLACE_INTRIN_CACHED_CELL.
Definition B_REPORTMMAPFAILUREANDDIE_PC : Z := 0x60bf0.   (* symbol _ZN11__sanitizer23ReportMmapFailureAndDieEmPKcS1_ib (216 bytes) *)
#[export] Instance Op_B_REPORTMMAPFAILUREANDDIE_PC : @CstOp Z Z B_REPORTMMAPFAILUREANDDIE_PC Inj_Z_Z := @mkcst Z Z B_REPORTMMAPFAILUREANDDIE_PC Inj_Z_Z 0x60bf0 eq_refl.
Add Zify CstOp Op_B_REPORTMMAPFAILUREANDDIE_PC.
Definition B_RESERVESHADOWMEMORYRANGE_PC : Z := 0x6d0b4.   (* symbol _ZN11__sanitizer24ReserveShadowMemoryRangeEmmPKcb (300 bytes) *)
#[export] Instance Op_B_RESERVESHADOWMEMORYRANGE_PC : @CstOp Z Z B_RESERVESHADOWMEMORYRANGE_PC Inj_Z_Z := @mkcst Z Z B_RESERVESHADOWMEMORYRANGE_PC Inj_Z_Z 0x6d0b4 eq_refl.
Add Zify CstOp Op_B_RESERVESHADOWMEMORYRANGE_PC.
Definition B_RODATA_0X109D4 : Z := 0x20cc8.   (* B place section .rodata + 0x109d4, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X109D4 : @CstOp Z Z B_RODATA_0X109D4 Inj_Z_Z := @mkcst Z Z B_RODATA_0X109D4 Inj_Z_Z 0x20cc8 eq_refl.
Add Zify CstOp Op_B_RODATA_0X109D4.
Definition B_RODATA_0X1574 : Z := 0x11854.   (* B place section .rodata + 0x1574, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X1574 : @CstOp Z Z B_RODATA_0X1574 Inj_Z_Z := @mkcst Z Z B_RODATA_0X1574 Inj_Z_Z 0x11854 eq_refl.
Add Zify CstOp Op_B_RODATA_0X1574.
Definition B_RODATA_0X158 : Z := 0x10438.   (* B place section .rodata + 0x158, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X158 : @CstOp Z Z B_RODATA_0X158 Inj_Z_Z := @mkcst Z Z B_RODATA_0X158 Inj_Z_Z 0x10438 eq_refl.
Add Zify CstOp Op_B_RODATA_0X158.
Definition B_RODATA_0X258 : Z := 0x10538.   (* B place section .rodata + 0x258, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X258 : @CstOp Z Z B_RODATA_0X258 Inj_Z_Z := @mkcst Z Z B_RODATA_0X258 Inj_Z_Z 0x10538 eq_refl.
Add Zify CstOp Op_B_RODATA_0X258.
Definition B_RODATA_0X28 : Z := 0x10308.   (* B place section .rodata + 0x28, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X28 : @CstOp Z Z B_RODATA_0X28 Inj_Z_Z := @mkcst Z Z B_RODATA_0X28 Inj_Z_Z 0x10308 eq_refl.
Add Zify CstOp Op_B_RODATA_0X28.
Definition B_RODATA_0X298 : Z := 0x10578.   (* B place section .rodata + 0x298, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X298 : @CstOp Z Z B_RODATA_0X298 Inj_Z_Z := @mkcst Z Z B_RODATA_0X298 Inj_Z_Z 0x10578 eq_refl.
Add Zify CstOp Op_B_RODATA_0X298.
Definition B_RODATA_0X4538 : Z := 0x14851.   (* B place section .rodata + 0x4538, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X4538 : @CstOp Z Z B_RODATA_0X4538 Inj_Z_Z := @mkcst Z Z B_RODATA_0X4538 Inj_Z_Z 0x14851 eq_refl.
Add Zify CstOp Op_B_RODATA_0X4538.
Definition B_RODATA_0X454C : Z := 0x14865.   (* B place section .rodata + 0x454c, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X454C : @CstOp Z Z B_RODATA_0X454C Inj_Z_Z := @mkcst Z Z B_RODATA_0X454C Inj_Z_Z 0x14865 eq_refl.
Add Zify CstOp Op_B_RODATA_0X454C.
Definition B_RODATA_0X48 : Z := 0x10328.   (* B place section .rodata + 0x48, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X48 : @CstOp Z Z B_RODATA_0X48 Inj_Z_Z := @mkcst Z Z B_RODATA_0X48 Inj_Z_Z 0x10328 eq_refl.
Add Zify CstOp Op_B_RODATA_0X48.
Definition B_RODATA_0X50 : Z := 0x10330.   (* B place section .rodata + 0x50, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X50 : @CstOp Z Z B_RODATA_0X50 Inj_Z_Z := @mkcst Z Z B_RODATA_0X50 Inj_Z_Z 0x10330 eq_refl.
Add Zify CstOp Op_B_RODATA_0X50.
Definition B_RODATA_0X520 : Z := 0x10800.   (* B place section .rodata + 0x520, rekeyed (c) *)
#[export] Instance Op_B_RODATA_0X520 : @CstOp Z Z B_RODATA_0X520 Inj_Z_Z := @mkcst Z Z B_RODATA_0X520 Inj_Z_Z 0x10800 eq_refl.
Add Zify CstOp Op_B_RODATA_0X520.
Definition B_RODATA_0X55CA : Z := 0x158e3.   (* B place section .rodata + 0x55ca, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X55CA : @CstOp Z Z B_RODATA_0X55CA Inj_Z_Z := @mkcst Z Z B_RODATA_0X55CA Inj_Z_Z 0x158e3 eq_refl.
Add Zify CstOp Op_B_RODATA_0X55CA.
Definition B_RODATA_0X55DB : Z := 0x158f4.   (* B place section .rodata + 0x55db, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X55DB : @CstOp Z Z B_RODATA_0X55DB Inj_Z_Z := @mkcst Z Z B_RODATA_0X55DB Inj_Z_Z 0x158f4 eq_refl.
Add Zify CstOp Op_B_RODATA_0X55DB.
Definition B_RODATA_0X78 : Z := 0x10358.   (* B place section .rodata + 0x78, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X78 : @CstOp Z Z B_RODATA_0X78 Inj_Z_Z := @mkcst Z Z B_RODATA_0X78 Inj_Z_Z 0x10358 eq_refl.
Add Zify CstOp Op_B_RODATA_0X78.
Definition B_RODATA_0X8 : Z := 0x102e8.   (* B place section .rodata + 0x8, rekeyed (c) *)
#[export] Instance Op_B_RODATA_0X8 : @CstOp Z Z B_RODATA_0X8 Inj_Z_Z := @mkcst Z Z B_RODATA_0X8 Inj_Z_Z 0x102e8 eq_refl.
Add Zify CstOp Op_B_RODATA_0X8.
Definition B_RODATA_0X89C : Z := 0x10b7c.   (* B place section .rodata + 0x89c, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X89C : @CstOp Z Z B_RODATA_0X89C Inj_Z_Z := @mkcst Z Z B_RODATA_0X89C Inj_Z_Z 0x10b7c eq_refl.
Add Zify CstOp Op_B_RODATA_0X89C.
Definition B_RODATA_0X90 : Z := 0x10370.   (* B place section .rodata + 0x90, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X90 : @CstOp Z Z B_RODATA_0X90 Inj_Z_Z := @mkcst Z Z B_RODATA_0X90 Inj_Z_Z 0x10370 eq_refl.
Add Zify CstOp Op_B_RODATA_0X90.
Definition B_RODATA_0X9002 : Z := 0x19338.   (* B place section .rodata + 0x9002, rekeyed (c) *)
#[export] Instance Op_B_RODATA_0X9002 : @CstOp Z Z B_RODATA_0X9002 Inj_Z_Z := @mkcst Z Z B_RODATA_0X9002 Inj_Z_Z 0x19338 eq_refl.
Add Zify CstOp Op_B_RODATA_0X9002.
Definition B_RODATA_0X9480 : Z := 0x197b6.   (* B place section .rodata + 0x9480, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0X9480 : @CstOp Z Z B_RODATA_0X9480 Inj_Z_Z := @mkcst Z Z B_RODATA_0X9480 Inj_Z_Z 0x197b6 eq_refl.
Add Zify CstOp Op_B_RODATA_0X9480.
Definition B_RODATA_0XA8 : Z := 0x10388.   (* B place section .rodata + 0xa8, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0XA8 : @CstOp Z Z B_RODATA_0XA8 Inj_Z_Z := @mkcst Z Z B_RODATA_0XA8 Inj_Z_Z 0x10388 eq_refl.
Add Zify CstOp Op_B_RODATA_0XA8.
Definition B_RODATA_0XCB82 : Z := 0x1ce6b.   (* B place section .rodata + 0xcb82, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0XCB82 : @CstOp Z Z B_RODATA_0XCB82 Inj_Z_Z := @mkcst Z Z B_RODATA_0XCB82 Inj_Z_Z 0x1ce6b eq_refl.
Add Zify CstOp Op_B_RODATA_0XCB82.
Definition B_RODATA_0XCB97 : Z := 0x1ce80.   (* B place section .rodata + 0xcb97, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0XCB97 : @CstOp Z Z B_RODATA_0XCB97 Inj_Z_Z := @mkcst Z Z B_RODATA_0XCB97 Inj_Z_Z 0x1ce80 eq_refl.
Add Zify CstOp Op_B_RODATA_0XCB97.
Definition B_RODATA_0XD0 : Z := 0x103b0.   (* B place section .rodata + 0xd0, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0XD0 : @CstOp Z Z B_RODATA_0XD0 Inj_Z_Z := @mkcst Z Z B_RODATA_0XD0 Inj_Z_Z 0x103b0 eq_refl.
Add Zify CstOp Op_B_RODATA_0XD0.
Definition B_RODATA_0XD562 : Z := 0x1d84b.   (* B place section .rodata + 0xd562, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0XD562 : @CstOp Z Z B_RODATA_0XD562 Inj_Z_Z := @mkcst Z Z B_RODATA_0XD562 Inj_Z_Z 0x1d84b eq_refl.
Add Zify CstOp Op_B_RODATA_0XD562.
Definition B_RODATA_0XD577 : Z := 0x1d860.   (* B place section .rodata + 0xd577, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0XD577 : @CstOp Z Z B_RODATA_0XD577 Inj_Z_Z := @mkcst Z Z B_RODATA_0XD577 Inj_Z_Z 0x1d860 eq_refl.
Add Zify CstOp Op_B_RODATA_0XD577.
Definition B_RODATA_0XD8 : Z := 0x103b8.   (* B place section .rodata + 0xd8, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0XD8 : @CstOp Z Z B_RODATA_0XD8 Inj_Z_Z := @mkcst Z Z B_RODATA_0XD8 Inj_Z_Z 0x103b8 eq_refl.
Add Zify CstOp Op_B_RODATA_0XD8.
Definition B_RODATA_0XE8 : Z := 0x103c8.   (* B place section .rodata + 0xe8, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0XE8 : @CstOp Z Z B_RODATA_0XE8 Inj_Z_Z := @mkcst Z Z B_RODATA_0XE8 Inj_Z_Z 0x103c8 eq_refl.
Add Zify CstOp Op_B_RODATA_0XE8.
Definition B_RODATA_0XF0 : Z := 0x103d0.   (* B place section .rodata + 0xf0, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0XF0 : @CstOp Z Z B_RODATA_0XF0 Inj_Z_Z := @mkcst Z Z B_RODATA_0XF0 Inj_Z_Z 0x103d0 eq_refl.
Add Zify CstOp Op_B_RODATA_0XF0.
Definition B_RODATA_0XF6CD : Z := 0x1f9d9.   (* B place section .rodata + 0xf6cd, rekeyed (b) *)
#[export] Instance Op_B_RODATA_0XF6CD : @CstOp Z Z B_RODATA_0XF6CD Inj_Z_Z := @mkcst Z Z B_RODATA_0XF6CD Inj_Z_Z 0x1f9d9 eq_refl.
Add Zify CstOp Op_B_RODATA_0XF6CD.
Definition B_RODATA_X_AT_1D853 : Z := 0x1d85c.   (* B place section .rodata + 0xd573, rekeyed (c) *)
#[export] Instance Op_B_RODATA_X_AT_1D853 : @CstOp Z Z B_RODATA_X_AT_1D853 Inj_Z_Z := @mkcst Z Z B_RODATA_X_AT_1D853 Inj_Z_Z 0x1d85c eq_refl.
Add Zify CstOp Op_B_RODATA_X_AT_1D853.
Definition B_RODATA_X_AT_1D855 : Z := 0x1d85e.   (* B place section .rodata + 0xd575, rekeyed (c) *)
#[export] Instance Op_B_RODATA_X_AT_1D855 : @CstOp Z Z B_RODATA_X_AT_1D855 Inj_Z_Z := @mkcst Z Z B_RODATA_X_AT_1D855 Inj_Z_Z 0x1d85e eq_refl.
Add Zify CstOp Op_B_RODATA_X_AT_1D855.
Definition B_RODATA_X_AT_1D86A : Z := 0x1d873.   (* B place section .rodata + 0xd58a, rekeyed (c) *)
#[export] Instance Op_B_RODATA_X_AT_1D86A : @CstOp Z Z B_RODATA_X_AT_1D86A Inj_Z_Z := @mkcst Z Z B_RODATA_X_AT_1D86A Inj_Z_Z 0x1d873 eq_refl.
Add Zify CstOp Op_B_RODATA_X_AT_1D86A.
Definition B_RODATA_X_AT_1D86C : Z := 0x1d875.   (* B place section .rodata + 0xd58c, rekeyed (c) *)
#[export] Instance Op_B_RODATA_X_AT_1D86C : @CstOp Z Z B_RODATA_X_AT_1D86C Inj_Z_Z := @mkcst Z Z B_RODATA_X_AT_1D86C Inj_Z_Z 0x1d875 eq_refl.
Add Zify CstOp Op_B_RODATA_X_AT_1D86C.
Definition B_RSS_LIMIT_EXCEEDED_CELL : Z := 0x12d962.   (* symbol _ZN11__sanitizerL18rss_limit_exceededE (1 bytes) *)
#[export] Instance Op_B_RSS_LIMIT_EXCEEDED_CELL : @CstOp Z Z B_RSS_LIMIT_EXCEEDED_CELL Inj_Z_Z := @mkcst Z Z B_RSS_LIMIT_EXCEEDED_CELL Inj_Z_Z 0x12d962 eq_refl.
Add Zify CstOp Op_B_RSS_LIMIT_EXCEEDED_CELL.
Definition B_RUNMALLOCHOOKS_PC : Z := 0x617fc.   (* symbol _ZN11__sanitizer14RunMallocHooksEPvm (184 bytes) *)
#[export] Instance Op_B_RUNMALLOCHOOKS_PC : @CstOp Z Z B_RUNMALLOCHOOKS_PC Inj_Z_Z := @mkcst Z Z B_RUNMALLOCHOOKS_PC Inj_Z_Z 0x617fc eq_refl.
Add Zify CstOp Op_B_RUNMALLOCHOOKS_PC.
Definition B_SANITIZER_COV_DUMP_PC : Z := 0x70c8c.   (* symbol __sanitizer_cov_dump (48 bytes) *)
#[export] Instance Op_B_SANITIZER_COV_DUMP_PC : @CstOp Z Z B_SANITIZER_COV_DUMP_PC Inj_Z_Z := @mkcst Z Z B_SANITIZER_COV_DUMP_PC Inj_Z_Z 0x70c8c eq_refl.
Add Zify CstOp Op_B_SANITIZER_COV_DUMP_PC.
Definition B_SANITIZER_INTERNAL_MEMCPY_PC : Z := 0x64b28.   (* symbol __sanitizer_internal_memcpy (36 bytes) *)
#[export] Instance Op_B_SANITIZER_INTERNAL_MEMCPY_PC : @CstOp Z Z B_SANITIZER_INTERNAL_MEMCPY_PC Inj_Z_Z := @mkcst Z Z B_SANITIZER_INTERNAL_MEMCPY_PC Inj_Z_Z 0x64b28 eq_refl.
Add Zify CstOp Op_B_SANITIZER_INTERNAL_MEMCPY_PC.
Definition B_SANITIZER_INTERNAL_MEMCPY_PC_OFF_C : Z := 0x64b34.   (* symbol __sanitizer_internal_memcpy + 0xc *)
#[export] Instance Op_B_SANITIZER_INTERNAL_MEMCPY_PC_OFF_C : @CstOp Z Z B_SANITIZER_INTERNAL_MEMCPY_PC_OFF_C Inj_Z_Z := @mkcst Z Z B_SANITIZER_INTERNAL_MEMCPY_PC_OFF_C Inj_Z_Z 0x64b34 eq_refl.
Add Zify CstOp Op_B_SANITIZER_INTERNAL_MEMCPY_PC_OFF_C.
Definition B_SANITIZER_INTERNAL_MEMSET_PC : Z := 0x64ba4.   (* symbol __sanitizer_internal_memset (96 bytes) *)
#[export] Instance Op_B_SANITIZER_INTERNAL_MEMSET_PC : @CstOp Z Z B_SANITIZER_INTERNAL_MEMSET_PC Inj_Z_Z := @mkcst Z Z B_SANITIZER_INTERNAL_MEMSET_PC Inj_Z_Z 0x64ba4 eq_refl.
Add Zify CstOp Op_B_SANITIZER_INTERNAL_MEMSET_PC.
Definition B_SANITIZER_INTERNAL_MEMSET_PC_OFF_8 : Z := 0x64bac.   (* symbol __sanitizer_internal_memset + 0x8 *)
#[export] Instance Op_B_SANITIZER_INTERNAL_MEMSET_PC_OFF_8 : @CstOp Z Z B_SANITIZER_INTERNAL_MEMSET_PC_OFF_8 Inj_Z_Z := @mkcst Z Z B_SANITIZER_INTERNAL_MEMSET_PC_OFF_8 Inj_Z_Z 0x64bac eq_refl.
Add Zify CstOp Op_B_SANITIZER_INTERNAL_MEMSET_PC_OFF_8.
Definition B_SCCP_PC : Z := 0x9c6d0.   (* symbol sccp (36 bytes) *)
#[export] Instance Op_B_SCCP_PC : @CstOp Z Z B_SCCP_PC Inj_Z_Z := @mkcst Z Z B_SCCP_PC Inj_Z_Z 0x9c6d0 eq_refl.
Add Zify CstOp Op_B_SCCP_PC.
Definition B_SCCP_PC_OFF_1C : Z := 0x9c6ec.   (* symbol sccp + 0x1c *)
#[export] Instance Op_B_SCCP_PC_OFF_1C : @CstOp Z Z B_SCCP_PC_OFF_1C Inj_Z_Z := @mkcst Z Z B_SCCP_PC_OFF_1C Inj_Z_Z 0x9c6ec eq_refl.
Add Zify CstOp Op_B_SCCP_PC_OFF_1C.
Definition B_SEALEDHANGONALLOCATIONFAILURE_PC_OFF_24 : Z := 0x356cc.   (* symbol _ZN11__sanitizer29SealedHangOnAllocationFailureEv + 0x24 *)
#[export] Instance Op_B_SEALEDHANGONALLOCATIONFAILURE_PC_OFF_24 : @CstOp Z Z B_SEALEDHANGONALLOCATIONFAILURE_PC_OFF_24 Inj_Z_Z := @mkcst Z Z B_SEALEDHANGONALLOCATIONFAILURE_PC_OFF_24 Inj_Z_Z 0x356cc eq_refl.
Add Zify CstOp Op_B_SEALEDHANGONALLOCATIONFAILURE_PC_OFF_24.
Definition B_SEALEDREPAIRRESERVATION_PC_OFF_C0 : Z := 0x6f428.   (* symbol _ZN11__sanitizerL23SealedRepairReservationEmm + 0xc0 *)
#[export] Instance Op_B_SEALEDREPAIRRESERVATION_PC_OFF_C0 : @CstOp Z Z B_SEALEDREPAIRRESERVATION_PC_OFF_C0 Inj_Z_Z := @mkcst Z Z B_SEALEDREPAIRRESERVATION_PC_OFF_C0 Inj_Z_Z 0x6f428 eq_refl.
Add Zify CstOp Op_B_SEALEDREPAIRRESERVATION_PC_OFF_C0.
Definition B_SEALED_REPORT_IN_PROGRESS_CELL : Z := 0x13d21c.   (* symbol _ZN11__sanitizer25sealed_report_in_progressE (4 bytes) *)
#[export] Instance Op_B_SEALED_REPORT_IN_PROGRESS_CELL : @CstOp Z Z B_SEALED_REPORT_IN_PROGRESS_CELL Inj_Z_Z := @mkcst Z Z B_SEALED_REPORT_IN_PROGRESS_CELL Inj_Z_Z 0x13d21c eq_refl.
Add Zify CstOp Op_B_SEALED_REPORT_IN_PROGRESS_CELL.
Definition B_SECONDARYALLOCATORNAME_CELL : Z := 0xa4708.   (* symbol _ZN11__sanitizer22SecondaryAllocatorNameE (8 bytes) *)
#[export] Instance Op_B_SECONDARYALLOCATORNAME_CELL : @CstOp Z Z B_SECONDARYALLOCATORNAME_CELL Inj_Z_Z := @mkcst Z Z B_SECONDARYALLOCATORNAME_CELL Inj_Z_Z 0xa4708 eq_refl.
Add Zify CstOp Op_B_SECONDARYALLOCATORNAME_CELL.
Definition B_SEG0_PAGESIZE : Z := 0x21000.   (* page-rounded size of PT_LOAD #0 *)
#[export] Instance Op_B_SEG0_PAGESIZE : @CstOp Z Z B_SEG0_PAGESIZE Inj_Z_Z := @mkcst Z Z B_SEG0_PAGESIZE Inj_Z_Z 0x21000 eq_refl.
Add Zify CstOp Op_B_SEG0_PAGESIZE.
Definition B_SEG0_PAGE_HI : Z := 0x31000.   (* page end of PT_LOAD #0 (p_vaddr + p_memsz rounded up to 0x1000) *)
#[export] Instance Op_B_SEG0_PAGE_HI : @CstOp Z Z B_SEG0_PAGE_HI Inj_Z_Z := @mkcst Z Z B_SEG0_PAGE_HI Inj_Z_Z 0x31000 eq_refl.
Add Zify CstOp Op_B_SEG0_PAGE_HI.
Definition B_SEG1_PAGESIZE : Z := 0x71000.   (* page-rounded size of PT_LOAD #1 *)
#[export] Instance Op_B_SEG1_PAGESIZE : @CstOp Z Z B_SEG1_PAGESIZE Inj_Z_Z := @mkcst Z Z B_SEG1_PAGESIZE Inj_Z_Z 0x71000 eq_refl.
Add Zify CstOp Op_B_SEG1_PAGESIZE.
Definition B_SEG1_PAGE_HI : Z := 0xa2000.   (* page end of PT_LOAD #1 (p_vaddr + p_memsz rounded up to 0x1000) *)
#[export] Instance Op_B_SEG1_PAGE_HI : @CstOp Z Z B_SEG1_PAGE_HI Inj_Z_Z := @mkcst Z Z B_SEG1_PAGE_HI Inj_Z_Z 0xa2000 eq_refl.
Add Zify CstOp Op_B_SEG1_PAGE_HI.
Definition B_SEG2_PAGESIZE : Z := 0x2000.   (* page-rounded size of PT_LOAD #2 *)
#[export] Instance Op_B_SEG2_PAGESIZE : @CstOp Z Z B_SEG2_PAGESIZE Inj_Z_Z := @mkcst Z Z B_SEG2_PAGESIZE Inj_Z_Z 0x2000 eq_refl.
Add Zify CstOp Op_B_SEG2_PAGESIZE.
Definition B_SEG3_PAGESIZE : Z := 0x55d000.   (* page-rounded size of PT_LOAD #3 *)
#[export] Instance Op_B_SEG3_PAGESIZE : @CstOp Z Z B_SEG3_PAGESIZE Inj_Z_Z := @mkcst Z Z B_SEG3_PAGESIZE Inj_Z_Z 0x55d000 eq_refl.
Add Zify CstOp Op_B_SEG3_PAGESIZE.
Definition B_SETALLOCATOROUTOFMEMORY_PC : Z := 0x5f5a8.   (* symbol _ZN11__sanitizer23SetAllocatorOutOfMemoryEv (16 bytes) *)
#[export] Instance Op_B_SETALLOCATOROUTOFMEMORY_PC : @CstOp Z Z B_SETALLOCATOROUTOFMEMORY_PC Inj_Z_Z := @mkcst Z Z B_SETALLOCATOROUTOFMEMORY_PC Inj_Z_Z 0x5f5a8 eq_refl.
Add Zify CstOp Op_B_SETALLOCATOROUTOFMEMORY_PC.
Definition B_SETERRNOTOENOMEM_PC : Z := 0x6d484.   (* symbol _ZN11__sanitizer16SetErrnoToENOMEMEv (32 bytes) *)
#[export] Instance Op_B_SETERRNOTOENOMEM_PC : @CstOp Z Z B_SETERRNOTOENOMEM_PC Inj_Z_Z := @mkcst Z Z B_SETERRNOTOENOMEM_PC Inj_Z_Z 0x6d484 eq_refl.
Add Zify CstOp Op_B_SETERRNOTOENOMEM_PC.
Definition B_SIZECLASSALLOCATOR64LOCALCACHE_PC : Z := 0x36d44.   (* symbol _ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm (728 bytes) *)
#[export] Instance Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC : @CstOp Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC Inj_Z_Z := @mkcst Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC Inj_Z_Z 0x36d44 eq_refl.
Add Zify CstOp Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC.
Definition B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_194 : Z := 0x36ed8.   (* symbol _ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x194 *)
#[export] Instance Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_194 : @CstOp Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_194 Inj_Z_Z := @mkcst Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_194 Inj_Z_Z 0x36ed8 eq_refl.
Add Zify CstOp Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_194.
Definition B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1AC : Z := 0x36ef0.   (* symbol _ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x1ac *)
#[export] Instance Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1AC : @CstOp Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1AC Inj_Z_Z := @mkcst Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1AC Inj_Z_Z 0x36ef0 eq_refl.
Add Zify CstOp Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1AC.
Definition B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1B4 : Z := 0x36ef8.   (* symbol _ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x1b4 *)
#[export] Instance Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1B4 : @CstOp Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1B4 Inj_Z_Z := @mkcst Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1B4 Inj_Z_Z 0x36ef8 eq_refl.
Add Zify CstOp Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1B4.
Definition B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1D4 : Z := 0x36f18.   (* symbol _ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x1d4 *)
#[export] Instance Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1D4 : @CstOp Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1D4 Inj_Z_Z := @mkcst Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1D4 Inj_Z_Z 0x36f18 eq_refl.
Add Zify CstOp Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_1D4.
Definition B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_28 : Z := 0x36d6c.   (* symbol _ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x28 *)
#[export] Instance Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_28 : @CstOp Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_28 Inj_Z_Z := @mkcst Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_28 Inj_Z_Z 0x36d6c eq_refl.
Add Zify CstOp Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_28.
Definition B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_2B0 : Z := 0x36ff4.   (* symbol _ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x2b0 *)
#[export] Instance Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_2B0 : @CstOp Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_2B0 Inj_Z_Z := @mkcst Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_2B0 Inj_Z_Z 0x36ff4 eq_refl.
Add Zify CstOp Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_2B0.
Definition B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_84 : Z := 0x36dc8.   (* symbol _ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x84 *)
#[export] Instance Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_84 : @CstOp Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_84 Inj_Z_Z := @mkcst Z Z B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_84 Inj_Z_Z 0x36dc8 eq_refl.
Add Zify CstOp Op_B_SIZECLASSALLOCATOR64LOCALCACHE_PC_OFF_84.
Definition B_SLOT_CELL : Z := 0x5fe788.   (* symbol slot (4 bytes) *)
#[export] Instance Op_B_SLOT_CELL : @CstOp Z Z B_SLOT_CELL Inj_Z_Z := @mkcst Z Z B_SLOT_CELL Inj_Z_Z 0x5fe788 eq_refl.
Add Zify CstOp Op_B_SLOT_CELL.
Definition B_STACKDEPOTNODE_STORE_STACKTRACE_PC : Z := 0x73404.   (* symbol _ZN11__sanitizer14StackDepotNode5storeEjRKNS_10StackTraceEy (92 bytes) *)
#[export] Instance Op_B_STACKDEPOTNODE_STORE_STACKTRACE_PC : @CstOp Z Z B_STACKDEPOTNODE_STORE_STACKTRACE_PC Inj_Z_Z := @mkcst Z Z B_STACKDEPOTNODE_STORE_STACKTRACE_PC Inj_Z_Z 0x73404 eq_refl.
Add Zify CstOp Op_B_STACKDEPOTNODE_STORE_STACKTRACE_PC.
Definition B_STACKDEPOTPUT_STACKTRACE_PC : Z := 0x736ec.   (* symbol _ZN11__sanitizer13StackDepotPutENS_10StackTraceE (32 bytes) *)
#[export] Instance Op_B_STACKDEPOTPUT_STACKTRACE_PC : @CstOp Z Z B_STACKDEPOTPUT_STACKTRACE_PC Inj_Z_Z := @mkcst Z Z B_STACKDEPOTPUT_STACKTRACE_PC Inj_Z_Z 0x736ec eq_refl.
Add Zify CstOp Op_B_STACKDEPOTPUT_STACKTRACE_PC.
Definition B_STACKSTORE_CELL : Z := 0x17d5c8.   (* symbol _ZN11__sanitizerL10stackStoreE (65552 bytes) *)
#[export] Instance Op_B_STACKSTORE_CELL : @CstOp Z Z B_STACKSTORE_CELL Inj_Z_Z := @mkcst Z Z B_STACKSTORE_CELL Inj_Z_Z 0x17d5c8 eq_refl.
Add Zify CstOp Op_B_STACKSTORE_CELL.
Definition B_STACKSTORE_OFF_18_CELL : Z := 0x17d5e0.   (* symbol _ZN11__sanitizerL10stackStoreE + 0x18 *)
#[export] Instance Op_B_STACKSTORE_OFF_18_CELL : @CstOp Z Z B_STACKSTORE_OFF_18_CELL Inj_Z_Z := @mkcst Z Z B_STACKSTORE_OFF_18_CELL Inj_Z_Z 0x17d5e0 eq_refl.
Add Zify CstOp Op_B_STACKSTORE_OFF_18_CELL.
Definition B_STACKSTORE_STORE_STACKTRACE_PC : Z := 0x710f0.   (* symbol _ZN11__sanitizer10StackStore5StoreERKNS_10StackTraceEPm (292 bytes) *)
#[export] Instance Op_B_STACKSTORE_STORE_STACKTRACE_PC : @CstOp Z Z B_STACKSTORE_STORE_STACKTRACE_PC Inj_Z_Z := @mkcst Z Z B_STACKSTORE_STORE_STACKTRACE_PC Inj_Z_Z 0x710f0 eq_refl.
Add Zify CstOp Op_B_STACKSTORE_STORE_STACKTRACE_PC.
Definition B_STACK_CHK_GUARD_CELL : Z := 0x5fe770.   (* symbol __stack_chk_guard (8 bytes) *)
#[export] Instance Op_B_STACK_CHK_GUARD_CELL : @CstOp Z Z B_STACK_CHK_GUARD_CELL Inj_Z_Z := @mkcst Z Z B_STACK_CHK_GUARD_CELL Inj_Z_Z 0x5fe770 eq_refl.
Add Zify CstOp Op_B_STACK_CHK_GUARD_CELL.
Definition B_STACK_TOP_PC : Z := 0x5d1ec.   (* symbol _ZN6__asan10AsanThread9stack_topEv (88 bytes) *)
#[export] Instance Op_B_STACK_TOP_PC : @CstOp Z Z B_STACK_TOP_PC Inj_Z_Z := @mkcst Z Z B_STACK_TOP_PC Inj_Z_Z 0x5d1ec eq_refl.
Add Zify CstOp Op_B_STACK_TOP_PC.
Definition B_START_OF_PT_LOAD_0_CELL : Z := 0x10000.   (* p_vaddr of PT_LOAD #0 *)
#[export] Instance Op_B_START_OF_PT_LOAD_0_CELL : @CstOp Z Z B_START_OF_PT_LOAD_0_CELL Inj_Z_Z := @mkcst Z Z B_START_OF_PT_LOAD_0_CELL Inj_Z_Z 0x10000 eq_refl.
Add Zify CstOp Op_B_START_OF_PT_LOAD_0_CELL.
Definition B_STDERR_FILE_CELL : Z := 0xa6e68.   (* symbol __stderr_FILE (232 bytes) *)
#[export] Instance Op_B_STDERR_FILE_CELL : @CstOp Z Z B_STDERR_FILE_CELL Inj_Z_Z := @mkcst Z Z B_STDERR_FILE_CELL Inj_Z_Z 0xa6e68 eq_refl.
Add Zify CstOp Op_B_STDERR_FILE_CELL.
Definition B_STDERR_USED_CELL : Z := 0xa6f50.   (* symbol __stderr_used (8 bytes) *)
#[export] Instance Op_B_STDERR_USED_CELL : @CstOp Z Z B_STDERR_USED_CELL Inj_Z_Z := @mkcst Z Z B_STDERR_USED_CELL Inj_Z_Z 0xa6f50 eq_refl.
Add Zify CstOp Op_B_STDERR_USED_CELL.
Definition B_STDIN_FILE_CELL : Z := 0xa7048.   (* symbol __stdin_FILE (232 bytes) *)
#[export] Instance Op_B_STDIN_FILE_CELL : @CstOp Z Z B_STDIN_FILE_CELL Inj_Z_Z := @mkcst Z Z B_STDIN_FILE_CELL Inj_Z_Z 0xa7048 eq_refl.
Add Zify CstOp Op_B_STDIN_FILE_CELL.
Definition B_STDIN_USED_CELL : Z := 0xa7130.   (* symbol __stdin_used (8 bytes) *)
#[export] Instance Op_B_STDIN_USED_CELL : @CstOp Z Z B_STDIN_USED_CELL Inj_Z_Z := @mkcst Z Z B_STDIN_USED_CELL Inj_Z_Z 0xa7130 eq_refl.
Add Zify CstOp Op_B_STDIN_USED_CELL.
Definition B_STDIO_CLOSE_PC : Z := 0x9519c.   (* symbol __stdio_close (44 bytes) *)
#[export] Instance Op_B_STDIO_CLOSE_PC : @CstOp Z Z B_STDIO_CLOSE_PC Inj_Z_Z := @mkcst Z Z B_STDIO_CLOSE_PC Inj_Z_Z 0x9519c eq_refl.
Add Zify CstOp Op_B_STDIO_CLOSE_PC.
Definition B_STDIO_SEEK_PC : Z := 0x952e0.   (* symbol __stdio_seek (8 bytes) *)
#[export] Instance Op_B_STDIO_SEEK_PC : @CstOp Z Z B_STDIO_SEEK_PC Inj_Z_Z := @mkcst Z Z B_STDIO_SEEK_PC Inj_Z_Z 0x952e0 eq_refl.
Add Zify CstOp Op_B_STDIO_SEEK_PC.
Definition B_STDIO_WRITE_PC : Z := 0x952e8.   (* symbol __stdio_write (400 bytes) *)
#[export] Instance Op_B_STDIO_WRITE_PC : @CstOp Z Z B_STDIO_WRITE_PC Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC Inj_Z_Z 0x952e8 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC.
Definition B_STDIO_WRITE_PC_OFF_100 : Z := 0x953e8.   (* symbol __stdio_write + 0x100 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_100 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_100 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_100 Inj_Z_Z 0x953e8 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_100.
Definition B_STDIO_WRITE_PC_OFF_104 : Z := 0x953ec.   (* symbol __stdio_write + 0x104 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_104 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_104 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_104 Inj_Z_Z 0x953ec eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_104.
Definition B_STDIO_WRITE_PC_OFF_108 : Z := 0x953f0.   (* symbol __stdio_write + 0x108 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_108 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_108 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_108 Inj_Z_Z 0x953f0 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_108.
Definition B_STDIO_WRITE_PC_OFF_10C : Z := 0x953f4.   (* symbol __stdio_write + 0x10c *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_10C : @CstOp Z Z B_STDIO_WRITE_PC_OFF_10C Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_10C Inj_Z_Z 0x953f4 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_10C.
Definition B_STDIO_WRITE_PC_OFF_110 : Z := 0x953f8.   (* symbol __stdio_write + 0x110 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_110 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_110 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_110 Inj_Z_Z 0x953f8 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_110.
Definition B_STDIO_WRITE_PC_OFF_114 : Z := 0x953fc.   (* symbol __stdio_write + 0x114 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_114 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_114 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_114 Inj_Z_Z 0x953fc eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_114.
Definition B_STDIO_WRITE_PC_OFF_118 : Z := 0x95400.   (* symbol __stdio_write + 0x118 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_118 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_118 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_118 Inj_Z_Z 0x95400 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_118.
Definition B_STDIO_WRITE_PC_OFF_11C : Z := 0x95404.   (* symbol __stdio_write + 0x11c *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_11C : @CstOp Z Z B_STDIO_WRITE_PC_OFF_11C Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_11C Inj_Z_Z 0x95404 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_11C.
Definition B_STDIO_WRITE_PC_OFF_120 : Z := 0x95408.   (* symbol __stdio_write + 0x120 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_120 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_120 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_120 Inj_Z_Z 0x95408 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_120.
Definition B_STDIO_WRITE_PC_OFF_124 : Z := 0x9540c.   (* symbol __stdio_write + 0x124 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_124 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_124 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_124 Inj_Z_Z 0x9540c eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_124.
Definition B_STDIO_WRITE_PC_OFF_128 : Z := 0x95410.   (* symbol __stdio_write + 0x128 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_128 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_128 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_128 Inj_Z_Z 0x95410 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_128.
Definition B_STDIO_WRITE_PC_OFF_12C : Z := 0x95414.   (* symbol __stdio_write + 0x12c *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_12C : @CstOp Z Z B_STDIO_WRITE_PC_OFF_12C Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_12C Inj_Z_Z 0x95414 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_12C.
Definition B_STDIO_WRITE_PC_OFF_130 : Z := 0x95418.   (* symbol __stdio_write + 0x130 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_130 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_130 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_130 Inj_Z_Z 0x95418 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_130.
Definition B_STDIO_WRITE_PC_OFF_134 : Z := 0x9541c.   (* symbol __stdio_write + 0x134 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_134 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_134 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_134 Inj_Z_Z 0x9541c eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_134.
Definition B_STDIO_WRITE_PC_OFF_138 : Z := 0x95420.   (* symbol __stdio_write + 0x138 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_138 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_138 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_138 Inj_Z_Z 0x95420 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_138.
Definition B_STDIO_WRITE_PC_OFF_13C : Z := 0x95424.   (* symbol __stdio_write + 0x13c *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_13C : @CstOp Z Z B_STDIO_WRITE_PC_OFF_13C Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_13C Inj_Z_Z 0x95424 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_13C.
Definition B_STDIO_WRITE_PC_OFF_140 : Z := 0x95428.   (* symbol __stdio_write + 0x140 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_140 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_140 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_140 Inj_Z_Z 0x95428 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_140.
Definition B_STDIO_WRITE_PC_OFF_144 : Z := 0x9542c.   (* symbol __stdio_write + 0x144 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_144 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_144 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_144 Inj_Z_Z 0x9542c eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_144.
Definition B_STDIO_WRITE_PC_OFF_148 : Z := 0x95430.   (* symbol __stdio_write + 0x148 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_148 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_148 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_148 Inj_Z_Z 0x95430 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_148.
Definition B_STDIO_WRITE_PC_OFF_14C : Z := 0x95434.   (* symbol __stdio_write + 0x14c *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_14C : @CstOp Z Z B_STDIO_WRITE_PC_OFF_14C Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_14C Inj_Z_Z 0x95434 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_14C.
Definition B_STDIO_WRITE_PC_OFF_150 : Z := 0x95438.   (* symbol __stdio_write + 0x150 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_150 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_150 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_150 Inj_Z_Z 0x95438 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_150.
Definition B_STDIO_WRITE_PC_OFF_154 : Z := 0x9543c.   (* symbol __stdio_write + 0x154 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_154 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_154 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_154 Inj_Z_Z 0x9543c eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_154.
Definition B_STDIO_WRITE_PC_OFF_88 : Z := 0x95370.   (* symbol __stdio_write + 0x88 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_88 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_88 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_88 Inj_Z_Z 0x95370 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_88.
Definition B_STDIO_WRITE_PC_OFF_8C : Z := 0x95374.   (* symbol __stdio_write + 0x8c *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_8C : @CstOp Z Z B_STDIO_WRITE_PC_OFF_8C Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_8C Inj_Z_Z 0x95374 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_8C.
Definition B_STDIO_WRITE_PC_OFF_90 : Z := 0x95378.   (* symbol __stdio_write + 0x90 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_90 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_90 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_90 Inj_Z_Z 0x95378 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_90.
Definition B_STDIO_WRITE_PC_OFF_94 : Z := 0x9537c.   (* symbol __stdio_write + 0x94 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_94 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_94 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_94 Inj_Z_Z 0x9537c eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_94.
Definition B_STDIO_WRITE_PC_OFF_E4 : Z := 0x953cc.   (* symbol __stdio_write + 0xe4 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_E4 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_E4 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_E4 Inj_Z_Z 0x953cc eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_E4.
Definition B_STDIO_WRITE_PC_OFF_E8 : Z := 0x953d0.   (* symbol __stdio_write + 0xe8 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_E8 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_E8 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_E8 Inj_Z_Z 0x953d0 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_E8.
Definition B_STDIO_WRITE_PC_OFF_EC : Z := 0x953d4.   (* symbol __stdio_write + 0xec *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_EC : @CstOp Z Z B_STDIO_WRITE_PC_OFF_EC Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_EC Inj_Z_Z 0x953d4 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_EC.
Definition B_STDIO_WRITE_PC_OFF_F0 : Z := 0x953d8.   (* symbol __stdio_write + 0xf0 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_F0 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_F0 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_F0 Inj_Z_Z 0x953d8 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_F0.
Definition B_STDIO_WRITE_PC_OFF_F4 : Z := 0x953dc.   (* symbol __stdio_write + 0xf4 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_F4 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_F4 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_F4 Inj_Z_Z 0x953dc eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_F4.
Definition B_STDIO_WRITE_PC_OFF_F8 : Z := 0x953e0.   (* symbol __stdio_write + 0xf8 *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_F8 : @CstOp Z Z B_STDIO_WRITE_PC_OFF_F8 Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_F8 Inj_Z_Z 0x953e0 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_F8.
Definition B_STDIO_WRITE_PC_OFF_FC : Z := 0x953e4.   (* symbol __stdio_write + 0xfc *)
#[export] Instance Op_B_STDIO_WRITE_PC_OFF_FC : @CstOp Z Z B_STDIO_WRITE_PC_OFF_FC Inj_Z_Z := @mkcst Z Z B_STDIO_WRITE_PC_OFF_FC Inj_Z_Z 0x953e4 eq_refl.
Add Zify CstOp Op_B_STDIO_WRITE_PC_OFF_FC.
Definition B_STDOUT_FILE_CELL : Z := 0xa6f58.   (* symbol __stdout_FILE (232 bytes) *)
#[export] Instance Op_B_STDOUT_FILE_CELL : @CstOp Z Z B_STDOUT_FILE_CELL Inj_Z_Z := @mkcst Z Z B_STDOUT_FILE_CELL Inj_Z_Z 0xa6f58 eq_refl.
Add Zify CstOp Op_B_STDOUT_FILE_CELL.
Definition B_STDOUT_USED_CELL : Z := 0xa7040.   (* symbol __stdout_used (8 bytes) *)
#[export] Instance Op_B_STDOUT_USED_CELL : @CstOp Z Z B_STDOUT_USED_CELL Inj_Z_Z := @mkcst Z Z B_STDOUT_USED_CELL Inj_Z_Z 0xa7040 eq_refl.
Add Zify CstOp Op_B_STDOUT_USED_CELL.
Definition B_STRCHR_PC : Z := 0x9c000.   (* symbol strchr (60 bytes) *)
#[export] Instance Op_B_STRCHR_PC : @CstOp Z Z B_STRCHR_PC Inj_Z_Z := @mkcst Z Z B_STRCHR_PC Inj_Z_Z 0x9c000 eq_refl.
Add Zify CstOp Op_B_STRCHR_PC.
Definition B_STRNLEN_PC : Z := 0x9c390.   (* symbol strnlen (68 bytes) *)
#[export] Instance Op_B_STRNLEN_PC : @CstOp Z Z B_STRNLEN_PC Inj_Z_Z := @mkcst Z Z B_STRNLEN_PC Inj_Z_Z 0x9c390 eq_refl.
Add Zify CstOp Op_B_STRNLEN_PC.
Definition B_STRNLEN_PC_OFF_24 : Z := 0x9c3b4.   (* symbol strnlen + 0x24 *)
#[export] Instance Op_B_STRNLEN_PC_OFF_24 : @CstOp Z Z B_STRNLEN_PC_OFF_24 Inj_Z_Z := @mkcst Z Z B_STRNLEN_PC_OFF_24 Inj_Z_Z 0x9c3b4 eq_refl.
Add Zify CstOp Op_B_STRNLEN_PC_OFF_24.
Definition B_STR_BYTES_REFUSED_N : Z := 0x197c6.   (* B place section .rodata + 0x9490, rekeyed (c) *)
#[export] Instance Op_B_STR_BYTES_REFUSED_N : @CstOp Z Z B_STR_BYTES_REFUSED_N Inj_Z_Z := @mkcst Z Z B_STR_BYTES_REFUSED_N Inj_Z_Z 0x197c6 eq_refl.
Add Zify CstOp Op_B_STR_BYTES_REFUSED_N.
Definition B_STR_ETRLIMIT_3_RL_0 : Z := 0x14613.   (* B place section .rodata + 0x42fa, rekeyed (c) *)
#[export] Instance Op_B_STR_ETRLIMIT_3_RL_0 : @CstOp Z Z B_STR_ETRLIMIT_3_RL_0 Inj_Z_Z := @mkcst Z Z B_STR_ETRLIMIT_3_RL_0 Inj_Z_Z 0x14613 eq_refl.
Add Zify CstOp Op_B_STR_ETRLIMIT_3_RL_0.
Definition B_STR_INPUT_N : Z := 0x158ec.   (* B place section .rodata + 0x55d3, rekeyed (c) *)
#[export] Instance Op_B_STR_INPUT_N : @CstOp Z Z B_STR_INPUT_N Inj_Z_Z := @mkcst Z Z B_STR_INPUT_N Inj_Z_Z 0x158ec eq_refl.
Add Zify CstOp Op_B_STR_INPUT_N.
Definition B_STR_S_INPUT_N : Z := 0x158ea.   (* B place section .rodata + 0x55d1, rekeyed (c) *)
#[export] Instance Op_B_STR_S_INPUT_N : @CstOp Z Z B_STR_S_INPUT_N Inj_Z_Z := @mkcst Z Z B_STR_S_INPUT_N Inj_Z_Z 0x158ea eq_refl.
Add Zify CstOp Op_B_STR_S_INPUT_N.
Definition B_STR_U_BYTES_REFUSED_N : Z := 0x197c4.   (* B place section .rodata + 0x948e, rekeyed (c) *)
#[export] Instance Op_B_STR_U_BYTES_REFUSED_N : @CstOp Z Z B_STR_U_BYTES_REFUSED_N Inj_Z_Z := @mkcst Z Z B_STR_U_BYTES_REFUSED_N Inj_Z_Z 0x197c4 eq_refl.
Add Zify CstOp Op_B_STR_U_BYTES_REFUSED_N.
Definition B_SYSCALL_RET_PC : Z := 0x8fe8c.   (* symbol __syscall_ret (56 bytes) *)
#[export] Instance Op_B_SYSCALL_RET_PC : @CstOp Z Z B_SYSCALL_RET_PC Inj_Z_Z := @mkcst Z Z B_SYSCALL_RET_PC Inj_Z_Z 0x8fe8c eq_refl.
Add Zify CstOp Op_B_SYSCALL_RET_PC.
Definition B_SYSCALL_RET_PC_OFF_34 : Z := 0x8fec0.   (* symbol __syscall_ret + 0x34 *)
#[export] Instance Op_B_SYSCALL_RET_PC_OFF_34 : @CstOp Z Z B_SYSCALL_RET_PC_OFF_34 Inj_Z_Z := @mkcst Z Z B_SYSCALL_RET_PC_OFF_34 Inj_Z_Z 0x8fec0 eq_refl.
Add Zify CstOp Op_B_SYSCALL_RET_PC_OFF_34.
Definition B_SYSCALL_RET_PC_OFF_4 : Z := 0x8fe90.   (* symbol __syscall_ret + 0x4 *)
#[export] Instance Op_B_SYSCALL_RET_PC_OFF_4 : @CstOp Z Z B_SYSCALL_RET_PC_OFF_4 Inj_Z_Z := @mkcst Z Z B_SYSCALL_RET_PC_OFF_4 Inj_Z_Z 0x8fe90 eq_refl.
Add Zify CstOp Op_B_SYSCALL_RET_PC_OFF_4.
Definition B_SYSCALL_RET_PC_OFF_8 : Z := 0x8fe94.   (* symbol __syscall_ret + 0x8 *)
#[export] Instance Op_B_SYSCALL_RET_PC_OFF_8 : @CstOp Z Z B_SYSCALL_RET_PC_OFF_8 Inj_Z_Z := @mkcst Z Z B_SYSCALL_RET_PC_OFF_8 Inj_Z_Z 0x8fe94 eq_refl.
Add Zify CstOp Op_B_SYSCALL_RET_PC_OFF_8.
Definition B_SYSCONF_PC : Z := 0x8eeec.   (* symbol sysconf (552 bytes) *)
#[export] Instance Op_B_SYSCONF_PC : @CstOp Z Z B_SYSCONF_PC Inj_Z_Z := @mkcst Z Z B_SYSCONF_PC Inj_Z_Z 0x8eeec eq_refl.
Add Zify CstOp Op_B_SYSCONF_PC.
Definition B_SYSCONF_VALUES_OFF_3C_CELL : Z := 0x21c88.   (* symbol sysconf.values + 0x3c *)
#[export] Instance Op_B_SYSCONF_VALUES_OFF_3C_CELL : @CstOp Z Z B_SYSCONF_VALUES_OFF_3C_CELL Inj_Z_Z := @mkcst Z Z B_SYSCONF_VALUES_OFF_3C_CELL Inj_Z_Z 0x21c88 eq_refl.
Add Zify CstOp Op_B_SYSCONF_VALUES_OFF_3C_CELL.
Definition B_SYSCONF_VALUES_OFF_3D_CELL : Z := 0x21c89.   (* symbol sysconf.values + 0x3d *)
#[export] Instance Op_B_SYSCONF_VALUES_OFF_3D_CELL : @CstOp Z Z B_SYSCONF_VALUES_OFF_3D_CELL Inj_Z_Z := @mkcst Z Z B_SYSCONF_VALUES_OFF_3D_CELL Inj_Z_Z 0x21c89 eq_refl.
Add Zify CstOp Op_B_SYSCONF_VALUES_OFF_3D_CELL.
Definition B_TARGET_RUN_INITIALIZED_CELL : Z := 0x5ddd50.   (* symbol target_run.initialized (1 bytes) *)
#[export] Instance Op_B_TARGET_RUN_INITIALIZED_CELL : @CstOp Z Z B_TARGET_RUN_INITIALIZED_CELL Inj_Z_Z := @mkcst Z Z B_TARGET_RUN_INITIALIZED_CELL Inj_Z_Z 0x5ddd50 eq_refl.
Add Zify CstOp Op_B_TARGET_RUN_INITIALIZED_CELL.
Definition B_TARGET_RUN_PC_OFF_48 : Z := 0x81544.   (* symbol target_run + 0x48 *)
#[export] Instance Op_B_TARGET_RUN_PC_OFF_48 : @CstOp Z Z B_TARGET_RUN_PC_OFF_48 Inj_Z_Z := @mkcst Z Z B_TARGET_RUN_PC_OFF_48 Inj_Z_Z 0x81544 eq_refl.
Add Zify CstOp Op_B_TARGET_RUN_PC_OFF_48.
Definition B_TARGET_RUN_PC_OFF_58 : Z := 0x81554.   (* symbol target_run + 0x58 *)
#[export] Instance Op_B_TARGET_RUN_PC_OFF_58 : @CstOp Z Z B_TARGET_RUN_PC_OFF_58 Inj_Z_Z := @mkcst Z Z B_TARGET_RUN_PC_OFF_58 Inj_Z_Z 0x81554 eq_refl.
Add Zify CstOp Op_B_TARGET_RUN_PC_OFF_58.
Definition B_TARGET_RUN_PC_OFF_64 : Z := 0x81560.   (* symbol target_run + 0x64 *)
#[export] Instance Op_B_TARGET_RUN_PC_OFF_64 : @CstOp Z Z B_TARGET_RUN_PC_OFF_64 Inj_Z_Z := @mkcst Z Z B_TARGET_RUN_PC_OFF_64 Inj_Z_Z 0x81560 eq_refl.
Add Zify CstOp Op_B_TARGET_RUN_PC_OFF_64.
Definition B_TARGET_RUN_PC_OFF_78 : Z := 0x81574.   (* symbol target_run + 0x78 *)
#[export] Instance Op_B_TARGET_RUN_PC_OFF_78 : @CstOp Z Z B_TARGET_RUN_PC_OFF_78 Inj_Z_Z := @mkcst Z Z B_TARGET_RUN_PC_OFF_78 Inj_Z_Z 0x81574 eq_refl.
Add Zify CstOp Op_B_TARGET_RUN_PC_OFF_78.
Definition B_TARGET_RUN_PC_OFF_A4 : Z := 0x815a0.   (* symbol target_run + 0xa4 *)
#[export] Instance Op_B_TARGET_RUN_PC_OFF_A4 : @CstOp Z Z B_TARGET_RUN_PC_OFF_A4 Inj_Z_Z := @mkcst Z Z B_TARGET_RUN_PC_OFF_A4 Inj_Z_Z 0x815a0 eq_refl.
Add Zify CstOp Op_B_TARGET_RUN_PC_OFF_A4.
Definition B_TARGET_RUN_PC_OFF_CC : Z := 0x815c8.   (* symbol target_run + 0xcc *)
#[export] Instance Op_B_TARGET_RUN_PC_OFF_CC : @CstOp Z Z B_TARGET_RUN_PC_OFF_CC Inj_Z_Z := @mkcst Z Z B_TARGET_RUN_PC_OFF_CC Inj_Z_Z 0x815c8 eq_refl.
Add Zify CstOp Op_B_TARGET_RUN_PC_OFF_CC.
Definition B_TARGET_RUN_PC_OFF_DC : Z := 0x815d8.   (* symbol target_run + 0xdc *)
#[export] Instance Op_B_TARGET_RUN_PC_OFF_DC : @CstOp Z Z B_TARGET_RUN_PC_OFF_DC Inj_Z_Z := @mkcst Z Z B_TARGET_RUN_PC_OFF_DC Inj_Z_Z 0x815d8 eq_refl.
Add Zify CstOp Op_B_TARGET_RUN_PC_OFF_DC.
Definition B_TARGET_RUN_PC_OFF_EC : Z := 0x815e8.   (* symbol target_run + 0xec *)
#[export] Instance Op_B_TARGET_RUN_PC_OFF_EC : @CstOp Z Z B_TARGET_RUN_PC_OFF_EC Inj_Z_Z := @mkcst Z Z B_TARGET_RUN_PC_OFF_EC Inj_Z_Z 0x815e8 eq_refl.
Add Zify CstOp Op_B_TARGET_RUN_PC_OFF_EC.
Definition B_TARGET_RUN_PC_OFF_F8 : Z := 0x815f4.   (* symbol target_run + 0xf8 *)
#[export] Instance Op_B_TARGET_RUN_PC_OFF_F8 : @CstOp Z Z B_TARGET_RUN_PC_OFF_F8 Inj_Z_Z := @mkcst Z Z B_TARGET_RUN_PC_OFF_F8 Inj_Z_Z 0x815f4 eq_refl.
Add Zify CstOp Op_B_TARGET_RUN_PC_OFF_F8.
Definition B_THEDEPOT_CELL : Z := 0x18d5d8.   (* symbol _ZN11__sanitizerL8theDepotE (4456464 bytes) *)
#[export] Instance Op_B_THEDEPOT_CELL : @CstOp Z Z B_THEDEPOT_CELL Inj_Z_Z := @mkcst Z Z B_THEDEPOT_CELL Inj_Z_Z 0x18d5d8 eq_refl.
Add Zify CstOp Op_B_THEDEPOT_CELL.
Definition B_THEDEPOT_OFF_400010_CELL : Z := 0x58d5e8.   (* symbol _ZN11__sanitizerL8theDepotE + 0x400010 *)
#[export] Instance Op_B_THEDEPOT_OFF_400010_CELL : @CstOp Z Z B_THEDEPOT_OFF_400010_CELL Inj_Z_Z := @mkcst Z Z B_THEDEPOT_OFF_400010_CELL Inj_Z_Z 0x58d5e8 eq_refl.
Add Zify CstOp Op_B_THEDEPOT_OFF_400010_CELL.
Definition B_TLS_GET_ADDR_PC : Z := 0x9c6f8.   (* symbol __tls_get_addr (36 bytes) *)
#[export] Instance Op_B_TLS_GET_ADDR_PC : @CstOp Z Z B_TLS_GET_ADDR_PC Inj_Z_Z := @mkcst Z Z B_TLS_GET_ADDR_PC Inj_Z_Z 0x9c6f8 eq_refl.
Add Zify CstOp Op_B_TLS_GET_ADDR_PC.
Definition B_TRYASANINITFROMRTL_PC : Z := 0x5a828.   (* symbol _ZN6__asan18TryAsanInitFromRtlEv (160 bytes) *)
#[export] Instance Op_B_TRYASANINITFROMRTL_PC : @CstOp Z Z B_TRYASANINITFROMRTL_PC Inj_Z_Z := @mkcst Z Z B_TRYASANINITFROMRTL_PC Inj_Z_Z 0x5a828 eq_refl.
Add Zify CstOp Op_B_TRYASANINITFROMRTL_PC.
Definition B_TSD_KEY_CELL : Z := 0xaaf64.   (* symbol _ZN6__asanL7tsd_keyE (4 bytes) *)
#[export] Instance Op_B_TSD_KEY_CELL : @CstOp Z Z B_TSD_KEY_CELL Inj_Z_Z := @mkcst Z Z B_TSD_KEY_CELL Inj_Z_Z 0xaaf64 eq_refl.
Add Zify CstOp Op_B_TSD_KEY_CELL.
Definition B_TSD_KEY_INITED_CELL : Z := 0xaaf60.   (* symbol _ZN6__asanL14tsd_key_initedE (1 bytes) *)
#[export] Instance Op_B_TSD_KEY_INITED_CELL : @CstOp Z Z B_TSD_KEY_INITED_CELL Inj_Z_Z := @mkcst Z Z B_TSD_KEY_INITED_CELL Inj_Z_Z 0xaaf60 eq_refl.
Add Zify CstOp Op_B_TSD_KEY_INITED_CELL.
Definition B_UNLOCK_PC : Z := 0x9c65c.   (* symbol __unlock (116 bytes) *)
#[export] Instance Op_B_UNLOCK_PC : @CstOp Z Z B_UNLOCK_PC Inj_Z_Z := @mkcst Z Z B_UNLOCK_PC Inj_Z_Z 0x9c65c eq_refl.
Add Zify CstOp Op_B_UNLOCK_PC.
Definition B_UNMAPORDIE_PC : Z := 0x66bf4.   (* symbol _ZN11__sanitizer10UnmapOrDieEPvmb (124 bytes) *)
#[export] Instance Op_B_UNMAPORDIE_PC : @CstOp Z Z B_UNMAPORDIE_PC Inj_Z_Z := @mkcst Z Z B_UNMAPORDIE_PC Inj_Z_Z 0x66bf4 eq_refl.
Add Zify CstOp Op_B_UNMAPORDIE_PC.
Definition B_UNWINDFAST_PC_OFF_C0 : Z := 0x74138.   (* symbol _ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xc0 *)
#[export] Instance Op_B_UNWINDFAST_PC_OFF_C0 : @CstOp Z Z B_UNWINDFAST_PC_OFF_C0 Inj_Z_Z := @mkcst Z Z B_UNWINDFAST_PC_OFF_C0 Inj_Z_Z 0x74138 eq_refl.
Add Zify CstOp Op_B_UNWINDFAST_PC_OFF_C0.
Definition B_UNWINDFAST_PC_OFF_FC : Z := 0x74174.   (* symbol _ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xfc *)
#[export] Instance Op_B_UNWINDFAST_PC_OFF_FC : @CstOp Z Z B_UNWINDFAST_PC_OFF_FC Inj_Z_Z := @mkcst Z Z B_UNWINDFAST_PC_OFF_FC Inj_Z_Z 0x74174 eq_refl.
Add Zify CstOp Op_B_UNWINDFAST_PC_OFF_FC.
Definition B_UNWINDIMPL_PC : Z := 0x5b5c0.   (* symbol _ZN11__sanitizer18BufferedStackTrace10UnwindImplEmmPvbj (336 bytes) *)
#[export] Instance Op_B_UNWINDIMPL_PC : @CstOp Z Z B_UNWINDIMPL_PC Inj_Z_Z := @mkcst Z Z B_UNWINDIMPL_PC Inj_Z_Z 0x5b5c0 eq_refl.
Add Zify CstOp Op_B_UNWINDIMPL_PC.
Definition B_UNWINDIMPL_PC_OFF_11C : Z := 0x5b6dc.   (* symbol _ZN11__sanitizer18BufferedStackTrace10UnwindImplEmmPvbj + 0x11c *)
#[export] Instance Op_B_UNWINDIMPL_PC_OFF_11C : @CstOp Z Z B_UNWINDIMPL_PC_OFF_11C Inj_Z_Z := @mkcst Z Z B_UNWINDIMPL_PC_OFF_11C Inj_Z_Z 0x5b6dc eq_refl.
Add Zify CstOp Op_B_UNWINDIMPL_PC_OFF_11C.
Definition B_UNWIND_PC : Z := 0x746d4.   (* symbol _ZN11__sanitizer18BufferedStackTrace6UnwindEjmmPvmmb (280 bytes) *)
#[export] Instance Op_B_UNWIND_PC : @CstOp Z Z B_UNWIND_PC Inj_Z_Z := @mkcst Z Z B_UNWIND_PC Inj_Z_Z 0x746d4 eq_refl.
Add Zify CstOp Op_B_UNWIND_PC.
Definition B_USECOUNTS_OFF_30008_CELL : Z := 0x16d5c8.   (* symbol _ZN11__sanitizerL9useCountsE + 0x30008 *)
#[export] Instance Op_B_USECOUNTS_OFF_30008_CELL : @CstOp Z Z B_USECOUNTS_OFF_30008_CELL Inj_Z_Z := @mkcst Z Z B_USECOUNTS_OFF_30008_CELL Inj_Z_Z 0x16d5c8 eq_refl.
Add Zify CstOp Op_B_USECOUNTS_OFF_30008_CELL.
Definition B_VFPRINTF_PC : Z := 0x95e2c.   (* symbol vfprintf (432 bytes) *)
#[export] Instance Op_B_VFPRINTF_PC : @CstOp Z Z B_VFPRINTF_PC Inj_Z_Z := @mkcst Z Z B_VFPRINTF_PC Inj_Z_Z 0x95e2c eq_refl.
Add Zify CstOp Op_B_VFPRINTF_PC.
Definition B_VPRINTF_PC : Z := 0x9b3ac.   (* symbol vprintf (28 bytes) *)
#[export] Instance Op_B_VPRINTF_PC : @CstOp Z Z B_VPRINTF_PC Inj_Z_Z := @mkcst Z Z B_VPRINTF_PC Inj_Z_Z 0x9b3ac eq_refl.
Add Zify CstOp Op_B_VPRINTF_PC.
Definition B_VSNPRINTF_PC : Z := 0x6795c.   (* symbol _ZN11__sanitizer9VSNPrintfEPciPKcPv (1464 bytes) *)
#[export] Instance Op_B_VSNPRINTF_PC : @CstOp Z Z B_VSNPRINTF_PC Inj_Z_Z := @mkcst Z Z B_VSNPRINTF_PC Inj_Z_Z 0x6795c eq_refl.
Add Zify CstOp Op_B_VSNPRINTF_PC.
Definition B_WRAP_BCMP_PC : Z := 0x42e18.   (* symbol __wrap_bcmp (4 bytes) *)
#[export] Instance Op_B_WRAP_BCMP_PC : @CstOp Z Z B_WRAP_BCMP_PC Inj_Z_Z := @mkcst Z Z B_WRAP_BCMP_PC Inj_Z_Z 0x42e18 eq_refl.
Add Zify CstOp Op_B_WRAP_BCMP_PC.
Definition B_WRAP_FFLUSH_PC : Z := 0x42e64.   (* symbol __wrap_fflush (4 bytes) *)
#[export] Instance Op_B_WRAP_FFLUSH_PC : @CstOp Z Z B_WRAP_FFLUSH_PC Inj_Z_Z := @mkcst Z Z B_WRAP_FFLUSH_PC Inj_Z_Z 0x42e64 eq_refl.
Add Zify CstOp Op_B_WRAP_FFLUSH_PC.
Definition B_WRAP_FPRINTF_PC : Z := 0x42e40.   (* symbol __wrap_fprintf (4 bytes) *)
#[export] Instance Op_B_WRAP_FPRINTF_PC : @CstOp Z Z B_WRAP_FPRINTF_PC Inj_Z_Z := @mkcst Z Z B_WRAP_FPRINTF_PC Inj_Z_Z 0x42e40 eq_refl.
Add Zify CstOp Op_B_WRAP_FPRINTF_PC.
Definition B_WRAP_FREE_PC : Z := 0x53820.   (* symbol __wrap_free (4 bytes) *)
#[export] Instance Op_B_WRAP_FREE_PC : @CstOp Z Z B_WRAP_FREE_PC Inj_Z_Z := @mkcst Z Z B_WRAP_FREE_PC Inj_Z_Z 0x53820 eq_refl.
Add Zify CstOp Op_B_WRAP_FREE_PC.
Definition B_WRAP_FWRITE_PC : Z := 0x42e28.   (* symbol __wrap_fwrite (4 bytes) *)
#[export] Instance Op_B_WRAP_FWRITE_PC : @CstOp Z Z B_WRAP_FWRITE_PC Inj_Z_Z := @mkcst Z Z B_WRAP_FWRITE_PC Inj_Z_Z 0x42e28 eq_refl.
Add Zify CstOp Op_B_WRAP_FWRITE_PC.
Definition B_WRAP_MALLOC_PC : Z := 0x53824.   (* symbol __wrap_malloc (4 bytes) *)
#[export] Instance Op_B_WRAP_MALLOC_PC : @CstOp Z Z B_WRAP_MALLOC_PC Inj_Z_Z := @mkcst Z Z B_WRAP_MALLOC_PC Inj_Z_Z 0x53824 eq_refl.
Add Zify CstOp Op_B_WRAP_MALLOC_PC.
Definition B_WRAP_MEMCHR_PC : Z := 0x42e1c.   (* symbol __wrap_memchr (4 bytes) *)
#[export] Instance Op_B_WRAP_MEMCHR_PC : @CstOp Z Z B_WRAP_MEMCHR_PC Inj_Z_Z := @mkcst Z Z B_WRAP_MEMCHR_PC Inj_Z_Z 0x42e1c eq_refl.
Add Zify CstOp Op_B_WRAP_MEMCHR_PC.
Definition B_WRAP_MEMCMP_PC : Z := 0x42e14.   (* symbol __wrap_memcmp (4 bytes) *)
#[export] Instance Op_B_WRAP_MEMCMP_PC : @CstOp Z Z B_WRAP_MEMCMP_PC Inj_Z_Z := @mkcst Z Z B_WRAP_MEMCMP_PC Inj_Z_Z 0x42e14 eq_refl.
Add Zify CstOp Op_B_WRAP_MEMCMP_PC.
Definition B_WRAP_MEMCPY_PC : Z := 0x524cc.   (* symbol __wrap_memcpy (4 bytes) *)
#[export] Instance Op_B_WRAP_MEMCPY_PC : @CstOp Z Z B_WRAP_MEMCPY_PC Inj_Z_Z := @mkcst Z Z B_WRAP_MEMCPY_PC Inj_Z_Z 0x524cc eq_refl.
Add Zify CstOp Op_B_WRAP_MEMCPY_PC.
Definition B_WRAP_MEMSET_PC : Z := 0x524c8.   (* symbol __wrap_memset (4 bytes) *)
#[export] Instance Op_B_WRAP_MEMSET_PC : @CstOp Z Z B_WRAP_MEMSET_PC Inj_Z_Z := @mkcst Z Z B_WRAP_MEMSET_PC Inj_Z_Z 0x524c8 eq_refl.
Add Zify CstOp Op_B_WRAP_MEMSET_PC.
Definition B_WRAP_READ_PC : Z := 0x42e24.   (* symbol __wrap_read (4 bytes) *)
#[export] Instance Op_B_WRAP_READ_PC : @CstOp Z Z B_WRAP_READ_PC Inj_Z_Z := @mkcst Z Z B_WRAP_READ_PC Inj_Z_Z 0x42e24 eq_refl.
Add Zify CstOp Op_B_WRAP_READ_PC.
Definition B_WRAP_STRCHR_PC : Z := 0x42e10.   (* symbol __wrap_strchr (4 bytes) *)
#[export] Instance Op_B_WRAP_STRCHR_PC : @CstOp Z Z B_WRAP_STRCHR_PC Inj_Z_Z := @mkcst Z Z B_WRAP_STRCHR_PC Inj_Z_Z 0x42e10 eq_refl.
Add Zify CstOp Op_B_WRAP_STRCHR_PC.
Definition B_WRAP_STRLEN_PC : Z := 0x42e04.   (* symbol __wrap_strlen (4 bytes) *)
#[export] Instance Op_B_WRAP_STRLEN_PC : @CstOp Z Z B_WRAP_STRLEN_PC Inj_Z_Z := @mkcst Z Z B_WRAP_STRLEN_PC Inj_Z_Z 0x42e04 eq_refl.
Add Zify CstOp Op_B_WRAP_STRLEN_PC.
Definition B_WRAP_STRNLEN_PC : Z := 0x42e08.   (* symbol __wrap_strnlen (4 bytes) *)
#[export] Instance Op_B_WRAP_STRNLEN_PC : @CstOp Z Z B_WRAP_STRNLEN_PC Inj_Z_Z := @mkcst Z Z B_WRAP_STRNLEN_PC Inj_Z_Z 0x42e08 eq_refl.
Add Zify CstOp Op_B_WRAP_STRNLEN_PC.
Definition B_WRAP_VFPRINTF_PC : Z := 0x42e38.   (* symbol __wrap_vfprintf (4 bytes) *)
#[export] Instance Op_B_WRAP_VFPRINTF_PC : @CstOp Z Z B_WRAP_VFPRINTF_PC Inj_Z_Z := @mkcst Z Z B_WRAP_VFPRINTF_PC Inj_Z_Z 0x42e38 eq_refl.
Add Zify CstOp Op_B_WRAP_VFPRINTF_PC.
Definition B_WRAP_VPRINTF_PC : Z := 0x42e34.   (* symbol __wrap_vprintf (4 bytes) *)
#[export] Instance Op_B_WRAP_VPRINTF_PC : @CstOp Z Z B_WRAP_VPRINTF_PC Inj_Z_Z := @mkcst Z Z B_WRAP_VPRINTF_PC Inj_Z_Z 0x42e34 eq_refl.
Add Zify CstOp Op_B_WRAP_VPRINTF_PC.
Definition B__PC : Z := 0x43bd4.   (* symbol _Z23MemcmpInterceptorCommonPvPFiPKvS1_mES1_S1_m (2196 bytes) *)
#[export] Instance Op_B__PC : @CstOp Z Z B__PC Inj_Z_Z := @mkcst Z Z B__PC Inj_Z_Z 0x43bd4 eq_refl.
Add Zify CstOp Op_B__PC.
Definition B__PC_OFF_30 : Z := 0x60c20.   (* symbol _ZN11__sanitizer23ReportMmapFailureAndDieEmPKcS1_ib + 0x30 *)
#[export] Instance Op_B__PC_OFF_30 : @CstOp Z Z B__PC_OFF_30 Inj_Z_Z := @mkcst Z Z B__PC_OFF_30 Inj_Z_Z 0x60c20 eq_refl.
Add Zify CstOp Op_B__PC_OFF_30.

(* shadow names the relocated files need; each is shadow_of of a named cell, not a literal.
   These are applications, not constants, so they carry no zify instance. *)
Definition B_SHADOW_ASAN_GLOBALS_CELL : Z := shadow_of B_ASAN_GLOBALS_CELL.
Definition B_SHADOW_BUILTIN_TLS_CELL_EB8 : Z := shadow_of (B_BUILTIN_TLS_CELL + 0xeb8).
Definition B_SHADOW_END_OF_SECTION_ASAN_GLOBALS_CELL : Z := shadow_of B_END_OF_SECTION_ASAN_GLOBALS_CELL.
Definition B_SHADOW_START_OF_PT_LOAD_0_CELL : Z := shadow_of B_START_OF_PT_LOAD_0_CELL.
