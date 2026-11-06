(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Definition main_ranges : list (Z * nat) := [(0x303c8, 36%nat); (0x31214, 69%nat); (0x31470, 254%nat); (0x318f0, 245%nat); (0x32f58, 52%nat); (0x33070, 7%nat); (0x34200, 65%nat); (0x354d8, 44%nat); (0x35650, 17%nat); (0x35718, 22%nat); (0x357b4, 112%nat); (0x359e4, 137%nat); (0x35c74, 214%nat); (0x360f4, 127%nat); (0x36384, 263%nat); (0x36860, 2%nat); (0x368ac, 32%nat); (0x3ca48, 41%nat); (0x3cb54, 136%nat); (0x3f398, 47%nat); (0x3f4c4, 52%nat); (0x3f674, 20%nat); (0x3f758, 68%nat); (0x3f9d0, 19%nat); (0x41a2c, 22%nat); (0x41d48, 60%nat); (0x41ebc, 22%nat); (0x43144, 76%nat); (0x432ec, 22%nat); (0x4368c, 53%nat); (0x437d8, 7%nat); (0x438fc, 58%nat); (0x44254, 179%nat); (0x44574, 108%nat); (0x4477c, 78%nat); (0x44af0, 1%nat); (0x44b58, 2%nat); (0x44bdc, 16%nat); (0x44db8, 34%nat); (0x45184, 54%nat); (0x462e4, 31%nat); (0x474b4, 17%nat); (0x475f0, 16%nat); (0x5102c, 2%nat); (0x514d0, 49%nat); (0x51668, 25%nat); (0x51710, 51%nat); (0x51a00, 77%nat); (0x51c10, 2%nat); (0x51d5c, 26%nat); (0x51e64, 23%nat); (0x52384, 23%nat); (0x52464, 87%nat); (0x52620, 38%nat); (0x53214, 44%nat); (0x53388, 5%nat); (0x53458, 35%nat); (0x53590, 14%nat); (0x53724, 27%nat); (0x53bb0, 105%nat); (0x53ef4, 6%nat); (0x54014, 6%nat); (0x54390, 6%nat); (0x58134, 6%nat); (0x59044, 13%nat); (0x59dcc, 46%nat); (0x59ef4, 14%nat); (0x5aa10, 9%nat); (0x5b844, 8%nat); (0x5ba08, 44%nat); (0x5d8c0, 82%nat); (0x5ddfc, 4%nat); (0x5faa4, 11%nat); (0x60018, 12%nat); (0x600b8, 26%nat); (0x60168, 9%nat); (0x63344, 9%nat); (0x633c0, 24%nat); (0x63474, 13%nat); (0x63514, 7%nat); (0x638f0, 39%nat); (0x63ba0, 11%nat); (0x6548c, 53%nat); (0x658cc, 67%nat); (0x65a50, 3%nat); (0x65f6c, 17%nat); (0x660bc, 10%nat); (0x68f58, 34%nat); (0x69060, 5%nat); (0x69120, 21%nat); (0x6db10, 87%nat); (0x6f4a8, 12%nat); (0x6f90c, 103%nat); (0x71c20, 18%nat); (0x71f08, 158%nat); (0x7269c, 36%nat); (0x7288c, 25%nat); (0x72934, 33%nat); (0x72ef0, 31%nat); (0x72fd0, 14%nat); (0x7f408, 6%nat); (0x7fa48, 408%nat); (0x80274, 31%nat); (0x804b4, 12%nat); (0x81950, 256%nat); (0x81e98, 20%nat); (0x8df08, 1%nat); (0x8e2fc, 3%nat); (0x8e3d8, 70%nat); (0x8e5b4, 50%nat); (0x8e87c, 71%nat); (0x939c8, 1%nat); (0x93b18, 57%nat); (0x940f8, 70%nat); (0x9428c, 203%nat); (0x9465c, 213%nat); (0x94a28, 7%nat); (0x94b1c, 3%nat); (0x94b74, 6%nat); (0x94c54, 64%nat); (0x94da4, 42%nat); (0x94edc, 6%nat); (0x950a8, 68%nat); (0x95230, 9%nat); (0x952d4, 42%nat); (0x95490, 1%nat); (0x95564, 2%nat); (0x955e8, 37%nat); (0x956d0, 6%nat); (0x95758, 6%nat); (0x9776c, 7%nat); (0x97d20, 165%nat); (0x98038, 184%nat); (0x986a8, 20%nat); (0x988e4, 1%nat); (0x98974, 3%nat); (0x989e8, 19%nat); (0x99ac4, 7%nat); (0x9d440, 21%nat); (0x9d520, 13%nat); (0x8e4f0, 49%nat)]%Z.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages.
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
