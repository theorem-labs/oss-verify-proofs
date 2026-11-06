(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0q.v (donor image sha256 7093581aab04), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AF0q.v (donor image sha256 43654a025fd0), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/A/AF0q.v at 9f8c843f0e03 (image sha256 614cffc0864c), with its module paths changed and its addresses moved to reac-pw/fuzz_headamp's ASan build (image sha256 f3e0669d2819) by alreloc a5c53bb2bed4; comments kept as the source has them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_headamp/lib/A/AF0q.v at b0cad0df5623 (image sha256 f3e0669d2819), with its module names changed (A.Axyz -> AU.Yxyz) and its addresses moved to reac-pw/fuzz_headamp's ASan+UBSan build (image sha256 53edda9bdeeb) by derive_y.py b7b132fb12a7; the Modified-by lines above describe how lib/A/AF0q.v was made and quote its ASan-build values. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK04 YA0n YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import YB1v YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import YFfs.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem afree_realizes_closed : forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> afree_realizes tfibsegs B.
Proof. intros B TS HD. exact (afree_realizes_all B TS HD). Qed.
End a.
