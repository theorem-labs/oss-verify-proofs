(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module PubC.
Definition ZPB_ID : int := 16%uint63.
Definition PUB_WINS : list (int * int) :=
  [(6340928%uint63, 6343680%uint63); (6343872%uint63, 6475584%uint63); (6475648%uint63, 6478848%uint63); (6478912%uint63, 6479872%uint63); (6479936%uint63, 6481216%uint63)].

Definition ZPB_SH_WINS : list (int * int) :=
  [(2148243496%uint63, 2148243840%uint63); (2148243864%uint63, 2148260328%uint63); (2148260336%uint63, 2148260736%uint63); (2148260744%uint63, 2148260869%uint63); (2148260870%uint63, 2148261032%uint63)].

Definition ZPB_VIDS : list int := [16%uint63; 1%uint63].
Definition in_pub_win (a len : int) : bool :=
  existsb (fun w => PrimInt63.leb (fst w) a && PrimInt63.leb a (snd w) && PrimInt63.leb (PrimInt63.add a len) (snd w)) PUB_WINS.
Definition lit_pub (st : sstate) (a : w64) (len : int) : bool :=
  negb (wt a) && in_pub_win (W64.wl a) len
  && negb (in_priv_b (s_priv st) (W64.wl a) len)
  && match find_op ZPB_ID (s_ops st) with Some [] => true | _ => false end.
End PubC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module PubC.
Definition ZPB_ID : int := 16%uint63.
Definition PUB_WINS : list (int * int) :=
  [(6349568%uint63, 6352320%uint63); (6352512%uint63, 6484224%uint63); (6484288%uint63, 6487488%uint63); (6487552%uint63, 6488512%uint63); (6488576%uint63, 6489856%uint63)].

Definition ZPB_SH_WINS : list (int * int) :=
  [(2148244576%uint63, 2148244920%uint63); (2148244944%uint63, 2148261408%uint63); (2148261416%uint63, 2148261816%uint63); (2148261824%uint63, 2148261949%uint63); (2148261950%uint63, 2148262112%uint63)].

Definition ZPB_VIDS : list int := [16%uint63; 1%uint63].
Definition in_pub_win (a len : int) : bool :=
  existsb (fun w => PrimInt63.leb (fst w) a && PrimInt63.leb a (snd w) && PrimInt63.leb (PrimInt63.add a len) (snd w)) PUB_WINS.
Definition lit_pub (st : sstate) (a : w64) (len : int) : bool :=
  negb (wt a) && in_pub_win (W64.wl a) len
  && negb (in_priv_b (s_priv st) (W64.wl a) len)
  && match find_op ZPB_ID (s_ops st) with Some [] => true | _ => false end.
End PubC.
End TwinB.
