(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import ItabFastAx ItabS_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Definition SEGS_both : list Segment := AsanUbsan.M.loaded_segments.
Definition RANGES_both : list (Z * nat) := [(0x32720, 335%nat); (0x33528, 869%nat); (0x34924, 519%nat); (0x352ec, 141%nat); (0x35b34, 197%nat); (0x36514, 203%nat); (0x377ec, 1429%nat); (0x391c4, 179%nat); (0x3977c, 186%nat); (0x3e3f4, 174%nat); (0x3ebb8, 1713%nat); (0x40c74, 1448%nat); (0x427b0, 300%nat); (0x42c90, 141%nat); (0x4349c, 139%nat); (0x44008, 829%nat); (0x44ef0, 489%nat); (0x45788, 350%nat); (0x45e48, 342%nat); (0x46a10, 536%nat); (0x472ac, 340%nat); (0x47940, 182%nat); (0x48aa0, 159%nat); (0x49ac0, 663%nat); (0x4aee4, 6750%nat); (0x53bbc, 1710%nat); (0x55ef0, 483%nat); (0x5689c, 415%nat); (0x57000, 269%nat); (0x5ae20, 134%nat); (0x5b5b8, 153%nat); (0x5b9ec, 350%nat); (0x5bf9c, 325%nat); (0x5c574, 553%nat); (0x5d6fc, 142%nat); (0x5d9dc, 159%nat); (0x5df94, 323%nat); (0x5e530, 850%nat); (0x6010c, 275%nat); (0x605ac, 467%nat); (0x620ec, 144%nat); (0x62790, 154%nat); (0x62a4c, 164%nat); (0x62d04, 250%nat); (0x631b0, 259%nat); (0x639ec, 217%nat); (0x63e98, 1330%nat); (0x65614, 607%nat); (0x66030, 688%nat); (0x66b74, 149%nat); (0x676c0, 200%nat); (0x67af4, 267%nat); (0x67f6c, 321%nat); (0x684b4, 293%nat); (0x68c58, 995%nat); (0x6b018, 457%nat); (0x6bb74, 396%nat); (0x6c1e0, 441%nat); (0x6cfbc, 377%nat); (0x6db9c, 262%nat); (0x6e4c4, 232%nat); (0x6e910, 663%nat); (0x6f550, 129%nat); (0x6f818, 242%nat); (0x6fd50, 364%nat); (0x7056c, 379%nat); (0x72150, 157%nat); (0x725f8, 271%nat); (0x73104, 166%nat); (0x7490c, 146%nat); (0x74bf4, 297%nat); (0x75388, 327%nat); (0x75bdc, 198%nat); (0x7c678, 389%nat); (0x7cd5c, 167%nat); (0x7f530, 131%nat); (0x820f4, 134%nat); (0x82490, 2127%nat); (0x84718, 7151%nat); (0x8bd00, 4562%nat); (0x90534, 218%nat); (0x90988, 780%nat); (0x91674, 741%nat); (0x92338, 166%nat); (0x981e4, 1252%nat); (0x99a74, 129%nat); (0x9a12c, 1167%nat); (0x9cde8, 80%nat); (0x9d5a0, 228%nat); (0x9da00, 133%nat); (0x9e290, 264%nat); (0x9e9c0, 991%nat); (0x9f970, 562%nat); (0xa20f4, 87%nat); (0xa2350, 80%nat); (0xa25e8, 1013%nat); (0xa45cc, 272%nat); (0xa4ab0, 324%nat); (0xa510c, 59%nat); (0xa540c, 92%nat); (0xa569c, 64%nat); (0xa7d60, 112%nat)]%Z.
Definition IT_both : itab := itab_of_string ITAB_BOTH_S 0 ITAB_BOTH_N.
Lemma IT_both_ok : itab_sound SEGS_both IT_both.
Proof. apply itab_agrees_sound. vm_cast_no_check (@eq_refl bool true). Qed.
