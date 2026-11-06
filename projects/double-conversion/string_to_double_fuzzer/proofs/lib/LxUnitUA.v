(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From Corelib Require Import PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIface LxLin LxState LxMem LxStep LxCheck LxUnitSplit LxEnvU LxUnitCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations LXL LXS LXM LXI LXC LXU.
Open Scope Z_scope.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Export LxUnitUA_def.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxUnitUA_p0 LxUnitUA_p1 LxUnitUA_p2 LxUnitUA_p3 LxUnitUA_p4 LxUnitUA_p5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Theorem chk_UA : check_unit UNIT_UA = true.
Proof.
  apply (check_unit_parts UNIT_UA PARTS_UA hdr_UA cov_UA).
  intros b Hb. cbn [PARTS_UA In] in Hb.
  destruct Hb as [<-|Hb]; [exact UA_part0|].
  destruct Hb as [<-|Hb]; [exact UA_part1|].
  destruct Hb as [<-|Hb]; [exact UA_part2|].
  destruct Hb as [<-|Hb]; [exact UA_part3|].
  destruct Hb as [<-|Hb]; [exact UA_part4|].
  destruct Hb as [<-|Hb]; [exact UA_part5|].
  destruct Hb.
Qed.
