(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Jb0DefsK Jb0PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK ArtRuns ArtBridge Jb0HandoffK
Jb0HSK_0 Jb0HSK_1 Jb0MainTableK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0HandoffInstK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanCeil."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffBridgeK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0HSK_0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0HSK_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0HandoffInstK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0HandoffK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0MainTableK."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0BUDGET"; "1None"; "1Some"; "1app"; "1bool"; "1length"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "3add"; "4le"; "4lt"]; ["0E"; "0EXTRA"; "0FULL"; "0KMAX"; "0LENMAX"; "5segments_reserved"; "6Model"; "6m_vmmaps"; "6vm_maps"; "6vm_noaccess"; "7bvmap"; "0R"; "8BInv"; "8bridge_static"; "9aev"; ":A_bytes"]; [";alloc_ceiling"; ";bottomup_floor"; "<LIMIT"; "<SINV0"; "<argH0"; "=FdStd"; "=a_abytes"; "=a_brk"; "=a_eager"; "=a_fd"; "=a_ghost"; "=a_maps"; "=a_totsz"; "=a_vis"; "=acs"; "=afd"]; ["=amap"; "=e_sp0"; "=kn"; "=no_fog"; ">cs_ok"; ">uE"; "?env"; "?expr"; "?lin_nowrapR"; "@amaps_lin"; "@vis_lin"; "AAPH0"; "AASAN0"; "AASEGS0"; "BHS_0"; "CHS_1"]; ["DHSA"; "Eas0_A0"; "Eas0_BASE"; "Eas0_RES"; "Eas0_chk"; "FHS_as0"; "Gadd"; "Gle"; "Gmul"; "Gof_nat"; "Gsub"; "0argv"; "0brk0"; "0envp"; "0fs"; "0h"]; ["0hw"; "0model"; "0rdraw"; "0sp"; "Hbv"; "0uid"]]).
Definition HSA (h : nat) : acs := match h with O => HS_0 | _ => HS_1 end.
Lemma HSA_some : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "C'6&?r1u2%3221'<'8'Q>%211&R5r2%211(2&R0%114%3281%;3851p0=1pU0B1").
Proof. intros [|[|h]] H; [reflexivity|reflexivity|lia]. Qed.
Lemma HSA_none : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "A'6'>u2r1%3221'<'8'Q>%211&R5r2%211(1%116%93631p0;1pU0@1").
Proof. intros [|[|h]] H; [lia|lia|reflexivity]. Qed.
Lemma HSA_nofog : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "B'6&?r1u2%3221'<'4&QC&Q;&R0r2%211%411%611(:%:3921p0<1pU0A1").
Proof. intros [|[|h]] H; [vm_compute; reflexivity|vm_compute; reflexivity|lia]. Qed.
Lemma HSA_mapslin : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "D'6&?r1u2%3221'<'4&QI&QB&R0r2%211%411&Q;%113%8231(:%<3;21p0>1pU0C1").
Proof. intros [|[|h]] H; [vm_compute; reflexivity|vm_compute; reflexivity|lia]. Qed.
Lemma HSA_vislin : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "K'6&?r1u2%3221'<'4&QJ&QB&R0r2%211%411&3'9'QG%2211&Q=%117&Q:%119%83531%?2:1(:%C3B21p0E1pU0J1").
Proof. intros [|[|h]] H; [vm_compute; reflexivity|vm_compute; reflexivity|lia]. Qed.
Lemma HSA_brklin : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "D'6&?r1u2%3221'<'4&QH&QB&R0r2%211%411&Q7%113%8231(:%<3;21p0>1pU0C1").
Proof. intros [|[|h]] H; [vm_compute; reflexivity|vm_compute; reflexivity|lia]. Qed.
Lemma HSA_fd : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "@'6&?r1u2%3221'<'Q?&Q9&R0r2%211%411(Q5%83721p0:1pU0?1").
Proof. intros [|[|h]] H; [reflexivity|reflexivity|lia]. Qed.
Lemma as0_chk_0 : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "7'<'4&R4&QN%211(:%63521").
Proof. vm_compute. reflexivity. Qed.
Lemma as0_chk_1 : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "7'<'4&R4&QO%211(:%63521").
Proof. vm_compute. reflexivity. Qed.
Lemma as0_chk_HSA : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "@'6&?r1u2%3221'<'4&R4&R0r2%211%411(:%83721p0:1pU0?1").
Proof. intros [|[|h]] H; [exact as0_chk_0 | exact as0_chk_1 | lia]. Qed.
Lemma HSA_numbers : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "Q3'6&?r1u2%3221';&R7&Q<&R0r2%211%411+`TPQVZ`P0%7221&Q8%115+_hPP0%;221&Q6%119+RY[Y]`0%?221'<&5'Q@&Q;%11@%4231uA%73M21%I291%J2>1%K2C1p0M1pU0Q21").
Proof. intros [|[|h]] H; [vm_compute; repeat split; discriminate || reflexivity | vm_compute; repeat split; discriminate || reflexivity | lia]. Qed.
Section Inst.
Variable sp brk0 : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variables uid hw : word.
Variable fs : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
#[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
#[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
Variables BUDGET LENMAX KMAX : Z.
Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
Variable EXTRA : list (Z * Z).
Hypothesis EXTRA_wf : A_wf EXTRA.
Hypothesis BUD_le : 16515072 + 2461316608 + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (17729665187840 + BUDGET) + (21 + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.
Lemma as0_inst_bud : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "I'6&?r1u2%3221&R7&R6&Q8&R0r2%211%411&Q6%113%8231&OvA%211%<241v0%>221&Q2%A221p0C1pU0H1").
Proof. intros h Hh. destruct (HSA_numbers h Hh) as (_ & N2 & N3 & _). lia. Qed.
Lemma as0_inst_gap : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "Q?'6&?r1u2%3221&R7&R6&Q1vD%3221&Q<&R0r2%211%411v0%:221%;281&R8&R9&=&5'9'RDyR0%211%4211&E&QM%211%9241'Q@&Q;%11D%=231%?251%A11vC%Q0221+SoO%Q22Q01%G231%Q42I1&Q0%Q7221p0Q91pU0Q>1").
Proof.
intros h Hh. destruct (HSA_numbers h Hh) as (N1 & _ & _ & N4). rewrite N4, asan0_res_eq. cbn [length Nat.add].
change (Z.of_nat 21) with 21. assert (0 <= LENMAX + 4095) by lia. nia.
Qed.
Theorem as0_handoff_static : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "R7'6&?r1u2%3221'QF&Jy5'RDyR0%211%5241'8y8%611%311p061'F'QD&QM&QL&Q2&Q3&QKvRCvRBvR<vR;vR=vREvR@%9887654321&Q4%17:986543vR>r4&R0r6%211r3r2%G;FED:876321Q7'M&H&G%115%311&E%11M&I%115&R3r5%211&R:&QE&QA%2251+XPPP0%5221v0vDvC%E9Q<A?=:4321p0G1pU4Q@1pQ6QB1pQHQH1pQ2QO1p0R11pU0R61").
Proof.
intros h Hh E R FULL model HC.
eapply as0_bridge_static; try eassumption.
- exact (as0_chk_HSA h Hh).
- exact (as0_inst_gap h Hh).
Qed.
Theorem as0_handoff_binv : ltac2:(TCodec.tc2 tcn__Jb0HandoffInstK "R='6&?r1u2%3221'QF&Jy5'RDyR0%211%5241'8y8%611%311p061'F'QD&QM&QL&Q2&Q3&QKvRCvRBvR<vR;vR=vREvR@%9887654321&Q4%17:986543vR>r4&R0r6%211r3r2%G;FED:876321Q7'L&H&G%115%311&E%11M&I%115&R:&QEr5&QA%3221+XPPP0%6221&R2vAr7%I11%4231v0(7'N%211&R1%1397?%K;QBGEC<7631NMp0M1pU4QF1pQ6QH1pQHQN1pQ2R51p0R71pU0R<1").
Proof.
intros h Hh E R FULL model HC.
eapply as0_binv_main with (LENMAX := LENMAX) (KMAX := KMAX); try eassumption.
- exact (as0_chk_HSA h Hh).
- exact (as0_inst_bud h Hh).
- exact (as0_inst_gap h Hh).
Qed.
End Inst.
