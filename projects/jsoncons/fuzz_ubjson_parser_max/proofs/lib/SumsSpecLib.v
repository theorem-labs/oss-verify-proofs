(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import MemsetLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanPlanSoundSums.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SumsSpecLib () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlan.AP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundSums.APSX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemsetLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1list"; "1nat"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "3repeat"; "4Z"; "5store_ok"; "6bvmap"; "7caller_saved"; "8fill_spec"; "8kept_ok"]; ["9ridx"; "9two64"; ":wbytes"; ";msteps"; "<regs_agree"; "<ret_ok"; "=cbyte"; "=ms_agree"; "=ms_clob"; ">getr"; ">mkst"; "?keeps"; "0SEGS"; "@In"; "Aadd"; "Ale"]; ["Alt"; "Apow"; "Ato_nat"; "0clob"; "0cv"; "0d"; "0entry"; "0fx"; "0mem0"; "0n"; "0r"; "0regs"; "0regs'"; "0ret"; "0rom"; "BBV"]; ["BZ_to_bv"; "Bbv"; "Bbv_unsigned"]]).
Lemma kept_ok_of_regs_agree : ltac2:(TCodec.tc2 tcn__SumsSpecLib "Q2'1'QAy5%211%411&<yR0%611%3261&Mr1r4%33921'2&@r2%211&=%93521p071pRFA1&Dr5%>3D=1qRFE1r3%5321;&?%12A3p031p0:1pRJG1pRHH1pR8M1").
Proof. intros clob regs regs' Hsub Hag r Hr0 Hnin. apply Hag. intros Hin. apply Hnin. apply Hsub. exact Hin. Qed.
Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).
Ltac clob_sub :=
let r := fresh "r" in let H := fresh "H" in
intros r H; cbn [In] in H;
repeat (destruct H as [<-|H]; [in_list|]); destruct H.
Lemma ms_clob_sub : ltac2:(TCodec.tc2 tcn__SumsSpecLib "?'QAy5%211&Mr1&H%33421'2&@r2%211&=%93521p071pRF<1").
Proof. unfold ms_clob. clob_sub. Qed.
Lemma kept_ok_of_keeps : ltac2:(TCodec.tc2 tcn__SumsSpecLib "@&<y5'QAyR0%211%5241&Kr2r1%3221&?r3%2215p041pRJ91pRH:1").
Proof.
intros regs regs' Hk r Hr0 Hnin. apply Hk.
pose proof (AX2S.ridx_range r) as Hrr.
assert (Hr : AX2.ridx r <> 0%nat).
{ intros X. apply Hr0. rewrite (APSX.reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
unfold AP.caller_saved in Hnin. cbn [In] in Hnin.
assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ AX2.ridx r = k).
{ exists (AX2.ridx r). split; [|reflexivity]. cbn [In]. lia. }
destruct E as (k & Hink & Hrk). rewrite (APSX.reg_of_ridx r k Hrk).
cbn [In] in Hink. unfold callee_kept.
repeat (destruct Hink as [<-|Hink]; [in_list|]). destruct Hink.
Qed.
Section Derive.
Context {fx : PropExec.FPState}.
Variable SEGS : list Segment.
Lemma fill_spec_of_memset : ltac2:(TCodec.tc2 tcn__SumsSpecLib "SD':'QAyR0%211'3y8%511%311p051&Ozr2%3221&Q0&N&QBr6%22?1r3%5221&Q1+2+R0%3221%;251'7'0&;vLr8r7&Q2r4%211%746541(4%;3:21&E%11F&<y5%221Q6&Ir1(Q?+:(5%33721%6251r:%I3Q?21+;%83<16%;2Q:1%M3QC15+<%<3@1:%?2Q71&Q@r9%22QJ1%Q43QJ41+1%C3G1A%F2Q01r;%Q93QO21'8'6'C&JvQ7rA%?2R71r@%554QK21:r=&Br?&9&Fr>%211r<%QE11%63R?31%93<81%A5@Q<;1F%C3QL=1%R03RFQ9;&G%12R;Q@%H231%I251qRJQE1%L2QF1p0N1p0Q41p0Q<1p0QA1pRHQK1p0QO1p0R21p0R?1p0RL1pRNS11pRDS:1pRLS81pR:S91pR<S:1pRBS61&>&A%24Q:RES61p041pR>SC1").
Proof.
intros entry SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
destruct (SUM mem0 s c ret n (seg_rom SEGS) Hn Hnw Hst Hret regs R10 R11 R12 R1) as (regs' & Hms & H10 & Hag).
exists regs'. split; [exact Hms|]. split; [|exact H10].
eapply kept_ok_of_regs_agree; [apply ms_clob_sub | exact Hag].
Qed.
End Derive.
