(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutU PmModel PmStatics PmSpecs PmSpecsU PmStep.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmCertKitU () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1fst"; "1list"; "1nat"; "1option"; "1prod"; "1snd"; "1true"; "2eq"; "3Z"; "0HI"; "0KS"; "0L"; "0LB"; "4VmMaps"; "0M"]; ["5credit"; "5hi_heap"; "5hl_sptop"; "6u32_at"; "6u64_at"; "6writable"; "7cs_all"; "8wseg_ok"; "9loaded_segments"; ":eqb"; ";In"; ";existsb"; "<add"; "<le"; "<lt"; "<pow"]; ["<sub"; "<to_nat"; "0VM"; "0a"; "0b"; "0cr"; "0k"; "0n"; "=Z_to_bv"; "=bv"; "0v"]]).
Module PMCKU.
Import PMU.
Lemma writable_img : ltac2:(TCodec.tc2 tcn__PmCertKitU "Q@'Q9yR0%211'4y8%511%311p051'9'8'0&G&H&Q8r2%22>1&Q1r1%211%83741(7%<3;21&Mzr3%3221&N%1243&Lr5r4%3221&O+2+R0%3221%>251&Er7r6%34L21;p051p0?1p0B1p0G1pR@Q51pR8Q61pQ0Q81").
Proof. intros M a n.
intros W Ha Hn Han d k Hd Hk. destruct k as [|k]. reflexivity.
eapply (store_ok_sub RSEGS M (Z_to_bv 64 a) _ (Z.to_nat n) (S k)).
- rewrite L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
- apply store_ok_wseg. exact W.
- rewrite !L5.unsigned_lit by lia. lia.
- rewrite !L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
Qed.
Lemma cs_in_KS : ltac2:(TCodec.tc2 tcn__PmCertKitU "I'2'3%211&Jr1&F%33521'8'0&K&Ir2%211r3%53=21(7%93821p0;1pR>A1r4%A3C91p0?1pR>E1p051pHF1").
Proof. intros KS. intros H k Hk. apply L5K.In_of_mem. apply H. exact Hk. Qed.
Ltac cs_all_tac := apply cs_in_KS; intros k Hk; unfold PMK.cs_all in Hk; cbn in Hk; repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]); destruct Hk.
Lemma u32_of_u64 : ltac2:(TCodec.tc2 tcn__PmCertKitU "F'Q9yR0%211'4y8%511%311p051'9&D&Hr3r2r1%544321&Cr4%247165p041pRF;1pR8<1pQ0>1").
Proof. intros M a v.
unfold L5.u64_at, L5.u32_at. intros H. rewrite (SeqExec.rdn_firstn RSEGS M 8%nat (Z_to_bv 64 a) _ 4%nat H) by lia. reflexivity.
Qed.
Section K.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Lemma lb_hi : ltac2:(TCodec.tc2 tcn__PmCertKitU "Q>'2'5'9%2211%411&@'Q9yR0%211'4y8%511%311p051'>&Av:r4r3r2r1%6554321&Jr6%23E41&M&L&1%13JJ9&6%13LL;%5231&Q0&Bv<%211+XPPP0%5221%=271p0?1pR:Q51p0D1pR6L1pQ0N1pR<Q71pLQ91").
Proof. intros LB cr M VM. intros HH b Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) b Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. Qed.
End K.
End PMCKU.
