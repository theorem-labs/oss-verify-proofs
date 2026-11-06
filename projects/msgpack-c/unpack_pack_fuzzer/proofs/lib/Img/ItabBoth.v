(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 IMap Instr ItabOk.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgBoth.
Import FI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PCS : list int := pcs_from 246992%uint63 36 ++ pcs_from 298144%uint63 296 ++ pcs_from 310792%uint63 26 ++ pcs_from 319072%uint63 2 ++ pcs_from 319104%uint63 2 ++ pcs_from 319120%uint63 1 ++ pcs_from 319132%uint63 1 ++ pcs_from 319164%uint63 1 ++ pcs_from 319216%uint63 166 ++ pcs_from 329552%uint63 39 ++ pcs_from 332468%uint63 45 ++ pcs_from 333440%uint63 54 ++ pcs_from 337888%uint63 31 ++ pcs_from 342016%uint63 24 ++ pcs_from 382344%uint63 1 ++ pcs_from 382352%uint63 628 ++ pcs_from 386080%uint63 380 ++ pcs_from 388516%uint63 4 ++ pcs_from 397324%uint63 177 ++ pcs_from 419704%uint63 89 ++ pcs_from 510680%uint63 12 ++ pcs_from 577656%uint63 1167 ++ pcs_from 582340%uint63 425 ++ pcs_from 584068%uint63 296 ++ pcs_from 585456%uint63 11 ++ pcs_from 585576%uint63 589 ++ pcs_from 587976%uint63 77 ++ pcs_from 588312%uint63 5065 ++ pcs_from 608616%uint63 319 ++ pcs_from 609980%uint63 773 ++ pcs_from 613116%uint63 23 ++ pcs_from 613252%uint63 23 ++ pcs_from 613388%uint63 23 ++ pcs_from 613524%uint63 1556 ++ pcs_from 619840%uint63 2732 ++ pcs_from 630796%uint63 311 ++ pcs_from 632084%uint63 153 ++ pcs_from 632752%uint63 17 ++ pcs_from 632916%uint63 5 ++ pcs_from 632980%uint63 5 ++ pcs_from 633296%uint63 6 ++ pcs_from 743832%uint63 1 ++ pcs_from 743856%uint63 4 ++ pcs_from 744116%uint63 22 ++ pcs_from 747252%uint63 2 ++ pcs_from 747364%uint63 2 ++ pcs_from 747400%uint63 104 ++ pcs_from 747916%uint63 23 ++ pcs_from 748040%uint63 65 ++ pcs_from 749188%uint63 638 ++ pcs_from 752304%uint63 148 ++ pcs_from 753736%uint63 38 ++ pcs_from 753972%uint63 454 ++ pcs_from 756580%uint63 82 ++ pcs_from 757040%uint63 530 ++ pcs_from 759436%uint63 152 ++ pcs_from 760468%uint63 253 ++ pcs_from 761488%uint63 86 ++ pcs_from 761992%uint63 70 ++ pcs_from 762436%uint63 94 ++ pcs_from 765788%uint63 2165 ++ pcs_from 776960%uint63 108 ++ pcs_from 777680%uint63 154 ++ pcs_from 778940%uint63 165 ++ pcs_from 781132%uint63 132 ++ pcs_from 783352%uint63 18 ++ pcs_from 784432%uint63 18 ++ pcs_from 784652%uint63 4 ++ pcs_from 784728%uint63 150 ++ pcs_from 785840%uint63 177 ++ pcs_from 804480%uint63 36 ++ pcs_from 806724%uint63 1 ++ pcs_from 807060%uint63 100 ++ pcs_from 808564%uint63 105 ++ pcs_from 809528%uint63 157 ++ pcs_from 810168%uint63 40 ++ pcs_from 810488%uint63 265 ++ pcs_from 811704%uint63 44 ++ pcs_from 812016%uint63 219 ++ pcs_from 813124%uint63 80 ++ pcs_from 813452%uint63 39 ++ pcs_from 813616%uint63 31 ++ pcs_from 813748%uint63 39 ++ pcs_from 814112%uint63 75 ++ pcs_from 814468%uint63 98 ++ pcs_from 827020%uint63 138 ++ pcs_from 827668%uint63 39 ++ pcs_from 846816%uint63 21 ++ pcs_from 847092%uint63 28.
Definition ITAB : itab := Eval vm_compute in build_itab SEGS PCS IMap.empty.

Lemma ITAB_eq : build_itab SEGS PCS IMap.empty = ITAB.
Proof. vm_cast_no_check (eq_refl ITAB). Qed.

Lemma ITAB_ok : itab_ok SEGS ITAB.
Proof. exact (ItabOk.build_itab_ok_of_eq SEGS PCS ITAB ITAB_eq). Qed.

Lemma ITAB_bst : IMap.bst ITAB.
Proof. exact (ItabOk.build_itab_bst_of_eq SEGS PCS ITAB ITAB_eq). Qed.
