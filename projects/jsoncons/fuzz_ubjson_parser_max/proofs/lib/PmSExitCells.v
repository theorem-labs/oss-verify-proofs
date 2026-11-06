(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StepTac StoreOk HeapIface LibIface L5Defs L5Core
PmLayout PmLayoutS PmModel PmStatics PmSpecs PmSpecsS PmTopS Js0AtexitCells.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSExitCells () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0AtexitCells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTopS.PMTS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1list"; "1nat"; "1option"; "2and"; "2eq"; "2ex"; "3Z"; "4word_to_le_bytes"; "0M"; "5ax_block"; "6img_clear"; "7ls_ok"; "7ls_state"]; ["8ADDR_S"; "9atexit_st"; ":TopLS"; ";rdn"; "<loaded_segments"; "=add"; "=le"; "=lt"; "=of_nat"; "=pow"; "0a"; "0b"; "0g"; "0hi"; "0lo"; "0n"]; ["0reg"; ">Z_to_bv"; ">bv"]]).
Module PMSXC.
Import PMS.
Lemma img_lock : ltac2:(TCodec.tc2 tcn__PmSExitCells "K'7'5'3'Q2y8%211%411%611&C&DyR0%811(0%118q031&Q1+loU<%2271u4%;4:521(1&:z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_next : ltac2:(TCodec.tc2 tcn__PmSExitCells "K'7'5'3'Q2y8%211%411%611&C&DyR0%811(0%118q031&Q1+loV0%2271u8%;4:521(1&:z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma rdn_clear : ltac2:(TCodec.tc2 tcn__PmSExitCells "QL'Q2yR0%211'5y8%511%311p051'9'4&=r5r4r3%43321&F%1253&E&H%116%3281%621:'6z%921=&G&I+2+R0%3221%52C1%9271r7%B214'7'3%11O%Q211&C&Dr:&Q1%12Q9:r6%645421(0%11Q9q0Q=1%:49165%?3<51p0A1p0D1p0O1p0Q51p0Q81pR0Q>1pQFQ@1pQLQA1pQNQB1pHQD1").
Proof. intros M lo hi a n.
intros C H1 H2 H3 H4. apply rdn_ext.
- rewrite L5.unsigned_lit by lia. lia.
- intros x Hx. rewrite L5.unsigned_lit in Hx by lia. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply C. lia.
Qed.
Section FPX_1.
Context {fx : PropExec.FPState}.
Lemma ax_block_of_st : ltac2:(TCodec.tc2 tcn__PmSExitCells "E'Q2yR0%211'5y8%511%311p051'2&A&D&@r2r1%544321&<r3%2215p041pQH;1pH=1").
Proof. intros M b.
unfold PMST.atexit_st. cbv zeta. cbn [pa_atexit pa_atexit_call pa_exit_guard pa_errcat_dtor pa_errcat_obj AD PmLayoutS.ADDR_S].
intros (C0 & SL & _ & HD & C24 & F0 & F1 & _ & A0 & A1 & _).
assert (LK : rdn RSEGS M (Z_to_bv 64 0xe7cac) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
{ rewrite (rdn_clear M _ _ 0xe7cac 4 C0) by (cbn; lia). exact img_lock. }
assert (NX : rdn RSEGS M (Z_to_bv 64 0xe7cc0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
{ rewrite (rdn_clear M _ _ 0xe7cc0 8 C24) by (cbn; lia). exact img_next. }
unfold ax_block, ax_block1, ax_block2. destruct b.
- split; [exact LK|]. split; [exact SL|]. split; [exact HD|]. split; [exact NX|]. split; [exact F0|]. split; [exact A0|]. split; [exact F1| exact A1].
- split; [exact LK|]. split; [exact SL|]. split; [exact HD|]. split; [exact NX|]. split; [exact F0| exact A0].
Qed.
Theorem top_lsx : ltac2:(TCodec.tc2 tcn__PmSExitCells "I&?&B%211'Q2yR0%211'5y8%511%311p051&>r2r1%33=21'8'2&<r3%2216qR241%6251p081pH=1pQJF1").
Proof. intros g M H. exists (PMST.st_err g). apply ax_block_of_st. exact (PMTS.top_statics_exit g M H). Qed.
End FPX_1.
End PMSXC.
