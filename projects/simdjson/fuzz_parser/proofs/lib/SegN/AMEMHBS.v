(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AMEMHB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import ST.
Open Scope Z_scope.
Module AMHBS.
Import AMHB.
Definition opnd2s (p n p8 g h he : expr) : list kentry :=
  [KRange (sub p (mul 8 p8)) 0 7; KRange g 0 0x2000000000; KRange (sub (mul 8 g) (sub (add p n) (mul 8 p8))) 0 7;
   KZero (SA p8 SH) g;
   KRange (sub p (mul 64 h)) 0 1048576; KRange (sub (mul 64 he) (add p n)) 0 63; KWr (SA (mul 8 h) SH) (mul 8 (sub he h));
   KRange p 0x7ffe00000000 0x800000000000; KRange (add p n) 0x7ffe00000000 0x7ffffffffff8;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA p 0) n;
   KRange p8 0 0x200000000000; KRange h 0 0x200000000000; KRange he 0 0x200000000000].
(* [comment removed for export] *)
Definition MSGS_pre_kn (rpc : Z) : list kentry :=
  [KRange (V 0) rpc rpc] ++ stk2 2208 ++
  [KRange (V 17) 0 0x10000000000; KWr (SA (V 16) 0) (V 17); KUnk (SA (V 16) 0) (V 17); KDisj (SA vSP (-2208)) (ELit 2208) (SA (V 16) 0) (V 17)]
  ++ opnd2s (V 16) (V 17) (V 18) (V 19) (V 20) (V 21).
Definition MSGS_pre (c rpc : Z) : tmpl := TM 0x65ce8 (MSG_pre_regs c) (MSGS_pre_kn rpc) 34%nat (ELit 0) 0%nat.
Definition MSAGS (c rpc : Z) : SP.summ := SP.SUMR 22 (MSGS_pre c rpc) [MSG_post c rpc] MSG_W (Some MSG_A) None.
End AMHBS.
