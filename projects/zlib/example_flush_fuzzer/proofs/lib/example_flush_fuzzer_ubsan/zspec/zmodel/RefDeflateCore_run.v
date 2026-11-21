(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  TreeModel FillWinModel SendModel RefFlushPend1 RefDeflateEnd1 RefDeflateHdr1 RefDeflateHdr2 RefDeflateHdr3
  RefDeflateHdr4 RefDeflateHdr5 RefDeflateTrl1 RefDeflMidOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.




Section CoreRun.
Variables (ws hs PBL ILEN OCAP : Z) (flush : Z).
Hypothesis Hflush : 0 <= flush < 16.



Local Notation front_ok' := (RefDeflateHdr5.front_ok PBL ILEN OCAP flush).
Local Notation trl_ok' := (RefDeflateTrl1.trl_ok PBL OCAP flush).

End CoreRun.
