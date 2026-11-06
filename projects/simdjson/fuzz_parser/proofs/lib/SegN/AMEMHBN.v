(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AMEMHB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Module AMHBN.
Import AMHB.
(* [comment removed for export] *)
Definition MVN_pre_kn (rpc : Z) : list kentry := KRange (V 21) 1 62 :: MV_pre_kn rpc.
Definition MVN_pre (rpc : Z) : ST.tmpl := ST.TMG 0x65f28 MV_pre_regs (MVN_pre_kn rpc) 35%nat (ELit 0) 0%nat [ST.GA 10 [add (V 17) (V 18)]].
Definition MVN_post (rpc : Z) : ST.tmpl :=
  ST.TMG rpc MV_post_regs [KUnk (SA (V 16) 0) (V 18)] 49%nat (ELit 0) 0%nat [ST.GA 10 [add (V 16) (V 18)]].
Definition MVAHN (rpc : Z) : SP.summ := SP.SUMR 23 (MVN_pre rpc) [MVN_post rpc] MV_W (Some MV_A) None.
End AMHBN.
