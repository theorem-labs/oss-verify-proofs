(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep MallocTree MallocFacts_A MallocKit_A Malloc_iface MallocKit_AB InitMem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp F_malloc_top F_malloc_big.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require MallocFacts_inv2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_Malloc_ifaceP () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1app"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2iff"; "3mul"; "4repeat"; "5Z"; "6Segment"; "7asegs"; "8wz"]; ["9u64arr"; "9u64s"; ":CB"; ":cell"; ":cells_size"; ";rw_cells"; "<add"; "<of_nat"; "0bs"; "0cs1"; "0cs2"; "0k"; "0m"; "0n"; "0segs"; "=bv"]]).
Ltac img_chunk NONE m A cs H :=
let bs := eval vm_compute in (cells_bytes cs) in
assert (H : rw_cells asegs m A cs);
[ apply (rw_cells_recast asegs m A [CB (length bs) bs] cs);
[ apply (rw_cells_image0 asegs m A bs);
[ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
| ].
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma u64arr_of_rw_cells : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_ifaceP "QD'OyR0%211'6y8%511%311p051'<'4'3%116&E&>r5r4(2'C(Br3r2%3221(5%116%83731%=4<;:1'8&A&;&?z%211%43N1<%611%83G?1&:u8%221B%<3MH1&@r8r7%>3Q8;K%44N321p061p0;1p0E1pQHQ61pQBQ51pQLQ81p2Q:1pQJQ<1").
Proof.
intros m A n bs k [[Hwf HB] HW] -> Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
split; [exact HB|]. cbn [cells_size csize] in HW. rewrite repeat_length. replace (8 * Z.of_nat k) with (Z.of_nat (n + 0)) by lia. exact HW.
Qed.
Lemma rw_cells_app : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_ifaceP "Q8'3'=%211'OyR0%211'6y8%511%311p051'<'C%=11&9&Er5r4r3&1r2r1%33:21%847651'7%:49875&F&G&D%119%311%52=1%A4@?1;%9281%D2;1pQFF1pQDG1p2J1pQJL1pQNQ51").
Proof.
intros segs m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
split.
- intros [[[W1 W2] [B1 B2]] WR].
pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
destruct WR as (HA & HN & HW).
split; [split; [split; assumption|] | split; [split; assumption|]].
+ split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
+ split; [lia|]. split; [lia|]. intros i Hi.
replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
- intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
pose proof (cells_bytes_length cs1 W1) as L1.
split; [split; [split; assumption|] |].
+ split; [exact B1|]. rewrite L1. exact B2.
+ split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
* apply HW1. lia.
* replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.
End CEIL_WRAP_1.
