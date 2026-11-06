(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SumsLib AsanIMemsetK AsanIMemcpyK AsanMemIsZeroK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import MemsetLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require AsanMemsetK AsanMemset_codeK AsanMemcpyBaseK AsanMemcpyK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanPlanSoundSumsK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SumsAsanSpecsK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanIMemcpyK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanIMemsetK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemIsZeroK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundSumsK.APSXK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemsetLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SumsAsanSpecsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SumsLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1negb"; "1nil"; "1option"; "1orb"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"]; ["3repeat"; "4Z"; "5Segment"; "5seg_readable"; "5seg_writable"; "6store_ok"; "6word_to_le_bytes"; "7bvmap"; "0N"; "8imemcpy_clob"; "9align15"; "9imemset_clob"; ":memisz_clob"; ";caller_saved"; ";x_imemcpy"; ";x_imemset"]; [";x_memcpy"; ";x_memiszero"; ";x_memset"; "<copy_spec"; "<fill_spec"; "<kept_ok"; "<miz_spec"; "<segs_wr_ok"; "=ridx"; "=two64"; ">wbytes"; "?msteps"; "@regs_agree"; "@ret_ok"; "AASAN0"; "Bcbyte"]; ["Bms_agree"; "Bms_clob"; "Cgetr"; "Cmkst"; "Crdn"; "Dkeeps"; "Easanreflect_fx"; "FcpyH"; "Gloaded_segments"; "0SEGS"; "HIn"; "Hforallb"; "Iadd"; "Ile"; "Ilt"; "Ipow"]; ["Isub"; "Ito_nat"; "0a"; "0beg"; "0bs"; "0c"; "0clob"; "0cv"; "0d"; "0dst"; "0entry"; "0entryw"; "0mem"; "0mem0"; "0n"; "0r"]; ["0regs"; "0regs'"; "0ret"; "0rom"; "0s"; "0seg"; "0segs"; "0sp"; "0src"; "JBV"; "JZ_to_bv"; "Jbv"; "Jbv_unsigned"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Ja0DefsK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Notation ASEGS0 := Asan.M.loaded_segments (only parsing).
Lemma kept_ok_of_regs_agree : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "Q2'3'RKy5%211%411&GyR0%611%3261&QJr1r4%33921'4&Q8r2%211&M%93521p071pU0A1&Q<r5%>3D=1qU0E1r3%5321;&Q5%12A3p031p0:1pU4G1pU2H1pT>M1").
Proof. intros clob regs regs' Hsub Hag r Hr0 Hnin. apply Hag. intros Hin. apply Hnin. apply Hsub. exact Hin. Qed.
#[local] Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).
#[local] Ltac clob_sub :=
let r := fresh "r" in let H := fresh "H" in
intros r H; cbn [In] in H;
repeat (destruct H as [<-|H]; [in_list|]); destruct H.
Lemma imemset_clob_sub : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "?'RKy5%211&QJr1&K%33421'4&Q8r2%211&M%93521p071pU0<1").
Proof. unfold imemset_clob. clob_sub. Qed.
Lemma imemcpy_clob_sub : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "?'RKy5%211&QJr1&I%33421'4&Q8r2%211&M%93521p071pU0<1").
Proof. unfold imemcpy_clob. clob_sub. Qed.
Lemma memisz_clob_sub : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "?'RKy5%211&QJr1&L%33421'4&Q8r2%211&M%93521p071pU0<1").
Proof. unfold memisz_clob. clob_sub. Qed.
Lemma ms_clob_sub : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "?'RKy5%211&QJr1&QA%33421'4&Q8r2%211&M%93521p071pU0<1").
Proof. unfold ms_clob. clob_sub. Qed.
Lemma kept_ok_of_keeps : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "@&Gy5'RKyR0%211%5241&QEr2r1%3221&Q5r3%2215p041pU491pU2:1").
Proof.
intros regs regs' Hk r Hr0 Hnin. apply Hk.
pose proof (AX2SK.ridx_range r) as Hrr.
assert (Hr : AX2K.ridx r <> 0%nat).
{ intros X. apply Hr0. rewrite (APSXK.reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
unfold APK.caller_saved in Hnin. cbn [In] in Hnin.
assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ AX2K.ridx r = k).
{ exists (AX2K.ridx r). split; [|reflexivity]. cbn [In]. lia. }
destruct E as (k & Hink & Hrk). rewrite (APSXK.reg_of_ridx r k Hrk).
cbn [In] in Hink. unfold callee_kept.
repeat (destruct Hink as [<-|Hink]; [in_list|]). destruct Hink.
Qed.
Lemma segs_wr_of_forallb : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "H'3'B%211'<'1&QK&8&5&Dr1%211%411&C%114%8231qU<>1%;3?17(9%?3>21&Q7r2%211p041pU>E1").
Proof.
intros segs H seg Hin Hw. pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbn beta in Hs.
rewrite Hw in Hs. exact Hs.
Qed.
Lemma asan0_segs_wr : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "3&Q7&QH%211").
Proof. apply segs_wr_of_forallb. vm_compute. reflexivity. Qed.
Section Derive.
Variable SEGS : list Segment.
Lemma fill_spec_of_imemset : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "T7'RKyR0%211'A'<&RJr1%2261r2%53721'7y8%<11%311p0<1&Gy5%221?&QMzr4%3221&QN&QL&RLr7%22I1r5%5221&QO+2+R0%3221%;251'1&EvQIr9r8&R1r6%211%746541(9%Q83:21&J%12E9%Q;3Q<1L&>%Q=3Q>;N%211r:%L2QC1+X0%Q0221p051p091&Q=%11O&QB(RI+1(:%33Q?21%52Q71%QM3QO1I+:%73QC15%92N1r<%R23R421+;%<3QH1:%>2Q41%R63R815+<%@3QL1>%B2J1%R92R=9%R;3R=21'=';'Q;&QC&QFrDrAr=%554C321r;&Q:r@&@r?%R62RM1%RJ2RD1r>%QJ11%63RF31%93=81%A5@RN;1=%C3R1=1&Q<%S71RG&QJ&K%233S41qU041%631Q7S6%L281qU4RM1%O2RN1p0Q11p0Q71p0Q<1p0QB1p0QJ1p0QM1p0R:1p0RF1p0S31pU6SG1pU2S91pU8S=1pTNSI1pT<SK1pU:SL1pTLSA1&Q4r3%23RN1R=p041p0SK1pTFT21pTHT41").
Proof.
intros entryw entry He SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
destruct (SUM mem0 s c n (seg_rom SEGS) regs ret Hn Hnw Hst ltac:(intros; exact Hc) Hret R1 R10 R11 R12) as (regs' & Hms & Hag).
exists regs'. rewrite He. split; [exact Hms|]. split.
- eapply kept_ok_of_regs_agree; [apply imemset_clob_sub | exact Hag].
- rewrite <- R10. apply Hag. unfold imemset_clob. cbn. intros [H|[H|[H|[]]]]; discriminate.
Qed.
Lemma fill_spec_of_memset : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "SD'A'RKyR0%211'7y8%511%311p051&QMzr2%3221&QN&QL&RLr6%22?1r3%5221&QO+2+R0%3221%;251'<'1&EvQIr8r7&R1r4%211%746541(9%;3:21&Q=%11F&Gy5%221Q6&QBr1(RI+:(:%33721%6251r:%I3Q?21+;%83<16%;2Q:1%M3QC15+<%<3@1:%?2Q71&RJr9%22QJ1%Q43QJ41+1%C3G1A%F2Q01r;%Q93QO21'=';'Q;&QC&QFrA%?2R71r@%554QK21:r=&Q:r?&@&Q?r>%211r<%QE11%63R?31%93<81%A5@Q<;1F%C3QL=1%R03RFQ9;&Q@%12R;Q@%H231%I251qU4QE1%L2QF1p0N1p0Q41p0Q<1p0QA1pU2QK1p0QO1p0R21p0R?1p0RL1pU8S11pTNS:1pU6S81pT@S91pTBS:1pTLS61&Q4&Q9%23RES61p041pTFSC1").
Proof.
intros entry SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
destruct (SUM mem0 s c ret n (seg_rom SEGS) Hn Hnw Hst Hret regs R10 R11 R12 R1) as (regs' & Hms & H10 & Hag).
exists regs'. split; [exact Hms|]. split; [|exact H10].
eapply kept_ok_of_regs_agree; [apply ms_clob_sub | exact Hag].
Qed.
Lemma copy_spec_of_imemcpy : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "S1'RKyR0%211'A'<&RJr1%2261r2%53721'7y8%<11%311p0<1'3%114&Gy5%221A'QGvQIr8r7r6r5r4%76654321&Q=%11E&QB(RI+1(:%33@21%5291r3%Q13Q321+:%83E16%:2?1r:%Q63Q821+;%=3J1;%?2E1%Q:3Q<15+<%A3N1?%C2J1%Q=2QA9%Q?3QA21'=';'Q;&QC&QFr9rBr?%554321C&Q:r>r;%33521%:59QKQ;1H%<3Q=61&Q<%R41QB&QJ&I%233R11qU041%631@R3%E281qU4QH1%H2QI1p0J1p0Q01p0Q51p0Q;1p0QD1p0QG1pU6RA1pU2R11pU8R71pT:R61pTNRD1pUBRF1pTDRG1pTLR<1&Q3%12R7QHp031p0RE1pTFRL1pTHRN1").
Proof.
intros entryw entry He SUM mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
destruct (SUM mem0 dst src n bs (seg_rom SEGS) regs ret ltac:(constructor; assumption) Hret R1 R10 R11 R12) as (regs' & Hms & Hag).
exists regs'. rewrite He. split; [exact Hms|]. split.
- eapply kept_ok_of_regs_agree; [apply imemcpy_clob_sub | exact Hag].
- rewrite <- R10. apply Hag. unfold imemcpy_clob. cbn. intros [H|[H|[H|[H|[]]]]]; discriminate.
Qed.
Lemma miz_spec_of_summary : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "U?'RKyR0%211'A'<&RJr1%2261r2%53721'7y8%<11%311p0<1&Gy5%221?';&QMzr4%3221&QO+2+Q8%3221%8261%:261&QL&RLr7%22O1r5%5221+8%7221+R0%?2>1%D231+@%F219'1&EvQIr:&R0r8%B2Q?1%321>%Q=2QA1u8%948721(9%QB3<21'?%J2QG;%L21:r9%M2QJ1%>21I%Q:241%Q;236%8221r<%Q32R01%Q42R1QL%Q@221&QN%Q824H%2241%QE241'3%11QM%R011&QDr>u1%34Q22R61(0(2%R<2R6QM(6%11R7%43R831%62<1%RB3<81p0@1pT6RF1&Q=%11QK&QB(RI+1(:%33R?21%52Q61%RM3RO1QB%63RBR:4%82QF1r=%S13S321r;+:%<3RH1:%>231r?%S73S921+;%A3RM1?%C2Q>1%S:2S>Q3%S<3S>21'='Q;&QC&QFrFrC%453Q;21=&Q:rA%RL2SI1%R=21RH%SG2SK1&F%12R;J%73931%=5<SJL1F%?3RE:1&Q<%T31SC&QJ&L%233T01qU041%631QLT2%Q>2T3Q1%T52T9Q=%T73T921%QA2T6Q:%T93T;1D%QC2T8Q?%T;3T=1Q;%SN231%SO261%T02:1%T12B1qU4T31%Q42T41p0Q61p0Q<1p0QC1p0QH1p0R01p0R31p0RM1p0S71p0SE1p0SH1p0T41pU6TO1pU2TA1pU8TE1pQBU11pU@U31pT8U41pTJTI1&Q6r3%22SN1p041p0U31pTFU:1pTHU<1").
Proof.
intros entryw entry He SUM mem beg sp N regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11.
destruct (SUM mem beg sp N (seg_rom SEGS) regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11) as (regs' & Hms & Hag & H10 & _ & _).
exists regs'. rewrite He. split; [exact Hms|]. split; [|exact H10].
eapply kept_ok_of_regs_agree; [apply memisz_clob_sub | exact Hag].
Qed.
End Derive.
Lemma asan_fill_spec_imemset : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "7&Q4&QH&O&Q>%211+X0%63521").
Proof.
apply (fill_spec_of_imemset _ asan_imemset_entry); [apply bv_eq; reflexivity|].
exact asan_imemset.
Qed.
Lemma asan_fill_spec_memset : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "7&Q4&QH&Q2&Q>%211&Q9%63521").
Proof.
apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
exact (AsanMemsetK.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.
Lemma asan_copy_spec_imemcpy : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "6&Q3&QH&N&Q>%211%5241").
Proof.
apply (copy_spec_of_imemcpy _ asan_imemcpy_entry); [apply bv_eq; reflexivity|].
exact asan_imemcpy.
Qed.
Lemma asan_copy_spec_memcpy : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "6&Q3&QH&Q0&Q>%211%5241").
Proof.
intros mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
pose proof (u64_range dst) as Hdr.
assert (HOK : AsanMemcpyBaseK.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
destruct (AsanMemcpyK.ref_memcpy mem0 dst src n bs (seg_rom ASEGS0) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
exists regs'. split; [replace (Z_to_bv 64 (APK.x_memcpy ASAN0)) with (0x1249ac%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
split; [apply kept_ok_of_keeps; exact Hk|].
rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.
Lemma asan_miz_spec : ltac2:(TCodec.tc2 tcn__SumsAsanSpecsK "6&Q6&QH&Q1&Q>%211%5241").
Proof.
apply (miz_spec_of_summary _ asan_mem_is_zero_entry); [apply bv_eq; reflexivity|].
exact asan_mem_is_zero.
Qed.
