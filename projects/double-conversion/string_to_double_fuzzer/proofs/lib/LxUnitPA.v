(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From Corelib Require Import PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIface LxLin LxState LxMem LxStep LxCheck LxUnitSplit LxEnvP LxUnitCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations LXL LXS LXM LXI LXC LXU.
Open Scope Z_scope.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Export LxUnitPA_def.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxUnitPA_p0 LxUnitPA_p1 LxUnitPA_p2 LxUnitPA_p3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Theorem chk_PA : check_unit UNIT_PA = true.
Proof.
  apply (check_unit_parts UNIT_PA PARTS_PA hdr_PA cov_PA).
  intros b Hb. cbn [PARTS_PA In] in Hb.
  destruct Hb as [<-|Hb]; [exact PA_part0|].
  destruct Hb as [<-|Hb]; [exact PA_part1|].
  destruct Hb as [<-|Hb]; [exact PA_part2|].
  destruct Hb as [<-|Hb]; [exact PA_part3|].
  destruct Hb.
Qed.
