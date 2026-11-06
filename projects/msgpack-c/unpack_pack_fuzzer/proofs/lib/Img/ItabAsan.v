(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 IMap Instr ItabOk.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgAsan.
Import FI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PCS : list int := pcs_from 244544%uint63 36 ++ pcs_from 295696%uint63 296 ++ pcs_from 308344%uint63 26 ++ pcs_from 316624%uint63 2 ++ pcs_from 316656%uint63 2 ++ pcs_from 316672%uint63 1 ++ pcs_from 316684%uint63 1 ++ pcs_from 316716%uint63 1 ++ pcs_from 316768%uint63 166 ++ pcs_from 327104%uint63 39 ++ pcs_from 330020%uint63 45 ++ pcs_from 330992%uint63 54 ++ pcs_from 335440%uint63 31 ++ pcs_from 339568%uint63 24 ++ pcs_from 379896%uint63 1 ++ pcs_from 379904%uint63 628 ++ pcs_from 383632%uint63 380 ++ pcs_from 386068%uint63 4 ++ pcs_from 394876%uint63 177 ++ pcs_from 417256%uint63 89 ++ pcs_from 508232%uint63 12 ++ pcs_from 575208%uint63 1126 ++ pcs_from 579728%uint63 381 ++ pcs_from 581276%uint63 144 ++ pcs_from 582036%uint63 15 ++ pcs_from 582152%uint63 412 ++ pcs_from 583844%uint63 84 ++ pcs_from 584204%uint63 5138 ++ pcs_from 604800%uint63 290 ++ pcs_from 606048%uint63 636 ++ pcs_from 608636%uint63 23 ++ pcs_from 608772%uint63 23 ++ pcs_from 608908%uint63 23 ++ pcs_from 609044%uint63 1975 ++ pcs_from 617036%uint63 1608 ++ pcs_from 623492%uint63 95 ++ pcs_from 623916%uint63 76 ++ pcs_from 624276%uint63 17 ++ pcs_from 624440%uint63 5 ++ pcs_from 624504%uint63 5 ++ pcs_from 624820%uint63 6 ++ pcs_from 735356%uint63 1 ++ pcs_from 735380%uint63 4 ++ pcs_from 735640%uint63 22 ++ pcs_from 738776%uint63 2 ++ pcs_from 738888%uint63 2 ++ pcs_from 738924%uint63 104 ++ pcs_from 739440%uint63 23 ++ pcs_from 739564%uint63 65 ++ pcs_from 740712%uint63 638 ++ pcs_from 743828%uint63 148 ++ pcs_from 745260%uint63 38 ++ pcs_from 745496%uint63 454 ++ pcs_from 748104%uint63 82 ++ pcs_from 748564%uint63 530 ++ pcs_from 750960%uint63 152 ++ pcs_from 751992%uint63 253 ++ pcs_from 753012%uint63 86 ++ pcs_from 753516%uint63 70 ++ pcs_from 753960%uint63 94 ++ pcs_from 757312%uint63 1591 ++ pcs_from 764040%uint63 483 ++ pcs_from 768484%uint63 108 ++ pcs_from 769204%uint63 154 ++ pcs_from 770464%uint63 165 ++ pcs_from 772656%uint63 132 ++ pcs_from 774876%uint63 18 ++ pcs_from 775956%uint63 18 ++ pcs_from 776176%uint63 4 ++ pcs_from 776252%uint63 150 ++ pcs_from 777364%uint63 177 ++ pcs_from 796004%uint63 36 ++ pcs_from 798248%uint63 1 ++ pcs_from 798584%uint63 100 ++ pcs_from 800088%uint63 105 ++ pcs_from 801052%uint63 157 ++ pcs_from 801692%uint63 40 ++ pcs_from 802012%uint63 265 ++ pcs_from 803228%uint63 44 ++ pcs_from 803540%uint63 219 ++ pcs_from 804648%uint63 80 ++ pcs_from 804976%uint63 39 ++ pcs_from 805140%uint63 31 ++ pcs_from 805272%uint63 39 ++ pcs_from 805636%uint63 75 ++ pcs_from 805992%uint63 98 ++ pcs_from 818544%uint63 138 ++ pcs_from 819192%uint63 39 ++ pcs_from 838340%uint63 21 ++ pcs_from 838616%uint63 28.
Definition ITAB : itab := Eval vm_compute in build_itab SEGS PCS IMap.empty.

Lemma ITAB_eq : build_itab SEGS PCS IMap.empty = ITAB.
Proof. vm_cast_no_check (eq_refl ITAB). Qed.

Lemma ITAB_ok : itab_ok SEGS ITAB.
Proof. exact (ItabOk.build_itab_ok_of_eq SEGS PCS ITAB ITAB_eq). Qed.

Lemma ITAB_bst : IMap.bst ITAB.
Proof. exact (ItabOk.build_itab_bst_of_eq SEGS PCS ITAB ITAB_eq). Qed.
