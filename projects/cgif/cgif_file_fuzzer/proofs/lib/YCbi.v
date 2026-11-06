(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YC7y YCbh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition xn_pb (X : YC7y.xnums) : YCbh.xnums :=
YCbh.mkXN (YC7y.xm_lzw X) (YC7y.xn_lzw X) (YC7y.xm_rawadd X) (YC7y.xn_rawadd X)
(YC7y.xm_flush X) (YC7y.xn_flush X) (YC7y.xm_addframe X) (YC7y.xn_addframe X)
(YC7y.xm_close X) (YC7y.xn_close X) (YC7y.xm_newgif X) (YC7y.xn_newgif X).
