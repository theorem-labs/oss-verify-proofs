(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.H Require GcFlushY22.  (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Definition main_ranges : list (Z * nat) := [(0x303f4, 36%nat); (0x31240, 69%nat); (0x3149c, 254%nat); (0x3191c, 245%nat); (0x32f84, 52%nat); (0x3309c, 7%nat); (0x3422c, 65%nat); (0x35504, 44%nat); (0x3567c, 17%nat); (0x35744, 22%nat); (0x357e0, 112%nat); (0x35a10, 137%nat); (0x35ca0, 214%nat); (0x36120, 127%nat); (0x363b0, 263%nat); (0x3688c, 2%nat); (0x368d8, 32%nat); (0x3ca74, 41%nat); (0x3cb80, 136%nat); (0x3f3c4, 47%nat); (0x3f4f0, 52%nat); (0x3f6a0, 20%nat); (0x3f784, 68%nat); (0x3f9fc, 19%nat); (0x41a58, 22%nat); (0x41d74, 60%nat); (0x41ee8, 22%nat); (0x43170, 76%nat); (0x43318, 22%nat); (0x436b8, 53%nat); (0x43804, 7%nat); (0x43928, 58%nat); (0x44280, 179%nat); (0x445a0, 108%nat); (0x447a8, 78%nat); (0x44b1c, 1%nat); (0x44b84, 2%nat); (0x44c08, 16%nat); (0x44de4, 34%nat); (0x451b0, 54%nat); (0x46310, 31%nat); (0x474e0, 17%nat); (0x4761c, 16%nat); (0x51058, 2%nat); (0x514fc, 49%nat); (0x51694, 25%nat); (0x5173c, 51%nat); (0x51a2c, 77%nat); (0x51c3c, 2%nat); (0x51d88, 26%nat); (0x51e90, 23%nat); (0x523b0, 23%nat); (0x52490, 87%nat); (0x5264c, 38%nat); (0x53240, 44%nat); (0x533b4, 5%nat); (0x53484, 35%nat); (0x535bc, 14%nat); (0x53750, 27%nat); (0x53bdc, 105%nat); (0x53f20, 6%nat); (0x54040, 6%nat); (0x543bc, 6%nat); (0x58160, 6%nat); (0x59070, 13%nat); (0x59df8, 46%nat); (0x59f20, 14%nat); (0x5aa3c, 9%nat); (0x5b870, 8%nat); (0x5ba34, 44%nat); (0x5d8ec, 82%nat); (0x5de28, 4%nat); (0x5fad0, 11%nat); (0x60044, 12%nat); (0x600e4, 26%nat); (0x60194, 9%nat); (0x63370, 9%nat); (0x633ec, 24%nat); (0x634a0, 13%nat); (0x63540, 7%nat); (0x6391c, 39%nat); (0x63bcc, 11%nat); (0x654b8, 53%nat); (0x658f8, 67%nat); (0x65a7c, 3%nat); (0x65f98, 17%nat); (0x660e8, 10%nat); (0x68f84, 34%nat); (0x6908c, 5%nat); (0x6914c, 21%nat); (0x6db3c, 87%nat); (0x6f4d4, 12%nat); (0x6f938, 103%nat); (0x71c4c, 18%nat); (0x71f34, 158%nat); (0x726c8, 36%nat); (0x728b8, 25%nat); (0x72960, 33%nat); (0x72f1c, 31%nat); (0x72ffc, 14%nat); (0x7f434, 6%nat); (0x7fa74, 409%nat); (0x8030c, 31%nat); (0x80568, 12%nat); (0x81c30, 262%nat); (0x82198, 18%nat); (0x8ed38, 1%nat); (0x8f12c, 3%nat); (0x8f208, 70%nat); (0x8f3e4, 50%nat); (0x8f6ac, 71%nat); (0x947f8, 1%nat); (0x94948, 57%nat); (0x94f28, 70%nat); (0x950bc, 203%nat); (0x9548c, 213%nat); (0x95858, 7%nat); (0x9594c, 3%nat); (0x959a4, 6%nat); (0x95a84, 64%nat); (0x95bd4, 42%nat); (0x95d0c, 6%nat); (0x95ed8, 68%nat); (0x96060, 9%nat); (0x96104, 42%nat); (0x962c0, 1%nat); (0x96394, 2%nat); (0x96418, 37%nat); (0x96500, 6%nat); (0x96588, 6%nat); (0x9859c, 7%nat); (0x98b50, 165%nat); (0x98e68, 184%nat); (0x994d8, 20%nat); (0x99714, 1%nat); (0x997a4, 3%nat); (0x99818, 19%nat); (0x9a8f4, 7%nat); (0x9e270, 21%nat); (0x9e350, 13%nat); (0x8f320, 49%nat)]%Z.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothAsanPlanImages.
Import AX2. Import AP.
(* [comment removed for export] *)
Definition ITm : itab := Eval vm_compute in mk_itab_ranges ASEGS main_ranges.
Lemma ITm_eq : ITm = mk_itab_ranges ASEGS main_ranges.
Proof. vm_cast_no_check (@eq_refl itab ITm). Qed.
Lemma ITm_ok : itab_sound ASEGS ITm.
Proof. rewrite ITm_eq. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)
Definition ITmD : itab := mk_itab_ranges ASEGS main_ranges.
Lemma ITmD_ok : itab_sound ASEGS ITmD.
Proof. apply APS.mk_itab_ranges_sound. Qed.
