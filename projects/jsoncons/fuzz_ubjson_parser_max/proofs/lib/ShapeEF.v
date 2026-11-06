(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim CatSim ShapeAlg DivergeSim SpinAlg SpinAlgX.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ShapeEF () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "stdpp.bitvector.definitions."], [["1list"; "2and"; "2iff"; "3N"; "3Z"; "4error_free"; "4strong_equiv_error_free_scfg"; "4trace_equiv"; "5Image"; "5PhdrInfo"; "5Segment"; "5img_init_pc"; "5img_phdrs"; "5img_segments"; "5mkImage"; "6ExecEntry"]; ["6bh_traces"; "6en_brk"; "6en_draw"; "6en_mmap_base"; "6en_sp"; "6init_config"; "6mkEntry"; "6run_scfg"; "7EntryDraw"; "8ProcInput"; "8event"; "8source_alloc_limit"; "8target_alloc_limit"; "9TSet"; "9realizes"; "9t_eq"]; [":srealizes"; "0SRC"; "0T"; "0T'"; "0TGT"; "0abrk"; "0alim"; "0amb"; "0apc"; "0aph"; "0arnd"; "0asp"; "0brk0"; "0en_s"; "0en_t"; "0inp"]; ["0lim"; "0mb"; "0pc"; "0ph"; "0rbrk"; "0rlim"; "0rmb"; "0rnd"; "0rpc"; "0rph"; "0rrnd"; "0rsp"; "0scfg"; "0segs"; "0source_segs"; "0sp"]; [";bv"; "0target_segs"; "0tr"]]).
Section WithCfg.
Variable scfg : SpuriousCfg.
Lemma srealizes_error_free : ltac2:(TCodec.tc2 tcn__ShapeEF "Q?'0':%211'3'9'R0yR0%211'H'4'I&M'Q0r:vQL&Er9r8r7r6r5r4r3r2%99;87654321r1%>4=<21&5&G(>r;%231B?(F%14@?>=%65D3=1<%811p0:1pR6J1pS0L1pS2N1pS@Q01pS4Q21pRJQ31pT0Q41pS8Q81pS6Q:1pSLQ<1").
Proof. intros. cbn. eapply srealizes_no_error; eassumption. Qed.
Lemma srealizes_traces_iff : ltac2:(TCodec.tc2 tcn__ShapeEF "QE'0':%211'3'9'R0yR0%211'H'4'I&M'J%=11'Q0r;vQL&Er:r9r8r7r6r5r4r3%99;87654321r2%>4=<21&2&@&G(>r<%231C@(F%14A@?>%65E3>1=%821;%>1<%;221p0=1pT6M1pR6Q01pS0Q21pS2Q41pS@Q61pS4Q81pRJQ91pT0Q:1pS8Q>1pS6Q@1pSLQB1").
Proof. intros. cbn. apply srealizes_obs_iff. assumption. Qed.
Lemma realizes_error_free : ltac2:(TCodec.tc2 tcn__ShapeEF "Q?'0':%211'3'9'R0yR0%211'H'4'I&M'Nr:vQL&Er9r8r7r6r5r4r3r2%99;87654321r1%>4=<21&5&G(>r;%231B?(F%14@?>=%65D3=1<%811p0:1pR6J1pS0L1pS2N1pS@Q01pS4Q21pRJQ31pT0Q41pS8Q81pS6Q:1pSLQ<1").
Proof. intros. cbn. eapply realizes_no_error; eassumption. Qed.
Lemma realizes_traces_iff : ltac2:(TCodec.tc2 tcn__ShapeEF "QE'0':%211'3'9'R0yR0%211'H'4'I&M'J%=11'Nr;vQL&Er:r9r8r7r6r5r4r3%99;87654321r2%>4=<21&2&@&G(>r<%231C@(F%14A@?>%65E3>1=%821;%>1<%;221p0=1pT6M1pR6Q01pS0Q21pS2Q41pS@Q61pS4Q81pRJQ91pT0Q:1pS8Q>1pS6Q@1pSLQB1").
Proof. intros. cbn. apply realizes_obs_iff. assumption. Qed.
Theorem shape_strong_equiv_efs : ltac2:(TCodec.tc2 tcn__ShapeEF "R?'0':%211'3'9'R0yR0%211'H'4&M'I'Q0rBvQL&ErAr@r?r>r=r<r;r1%99;87654321r2%>4=<21r:r9r8r7r6r5r4%C9<76543219r3%H4>F21'1&5&G(>rDrC%3321N(F%14MLKJ%75Q03J1;%911%83KJE%54EDCB%;5Q42B1?%=11&7&@%118%215%4221%D261%E2;1p0G1p0Q21pS0QB1pR6QD1pR>QF1pRFQH1pR@QJ1pR<QK1pRHQL1pRDR01pRBR21pT4R41pS<QN1pSFR01pS>R21pS:R31pSHR41pSDR81pSBR:1pSNR<1").
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
T inp Hsource Htarget.
split; [| split].
- eapply srealizes_error_free; exact Hsource.
- eapply srealizes_error_free; exact Htarget.
- intro tr.
rewrite (srealizes_traces_iff source_segs _ _ _ _ _ _ _ _ T tr Hsource).
rewrite (srealizes_traces_iff target_segs _ _ _ _ _ _ _ _ T tr Htarget).
reflexivity.
Qed.
Corollary shape_strong_equiv_efs_eq : ltac2:(TCodec.tc2 tcn__ShapeEF "RE'0':%211'3'9'R0yR0%211'H'4&M'I'Q0rCvQL&ErBrAr@r?r>r=r<r1%99;87654321r3%>4=<21r;r:r9r8r7r6r5r2%D9=87654321%H4>F1;&Or4%2261'1&5&G(>rFrErD%43321(F%14Q4Q1Q0O%85Q43O1<%:11%93Q0ON%54JIHG%<5Q82G1@%>11&7&@%118%215%4221%E261%F2;1p0H1p0L1p0Q71pS0QG1pR8QI1pR6QJ1pR>QL1pRFQN1pR@R01pR<R11pRHR21pRDR61pRBR81pT4R:1pS<R41pSFR61pS>R81pS:R91pSHR:1pSDR>1pSBR@1pSNRB1").
Proof.
intros until T'. intros inp Hs Ht Heq.
eapply shape_strong_equiv_efs; [| exact Ht].
eapply srz_conseq; [exact Hs | exact Heq].
Qed.
Theorem shape_strong_equiv_ef : ltac2:(TCodec.tc2 tcn__ShapeEF "R?'0':%211'3'9'R0yR0%211'H'4&M'I'NrBvQL&ErAr@r?r>r=r<r;r1%99;87654321r2%>4=<21r:r9r8r7r6r5r4%C9<76543219r3%H4>F21'1&5&G(>rDrC%3321N(F%14MLKJ%75Q03J1;%911%83KJE%54EDCB%;5Q42B1?%=11&7&@%118%215%4221%D261%E2;1p0G1p0Q21pS0QB1pR6QD1pR>QF1pRFQH1pR@QJ1pR<QK1pRHQL1pRDR01pRBR21pT4R41pS<QN1pSFR01pS>R21pS:R31pSHR41pSDR81pSBR:1pSNR<1").
Proof.
intros until T. intros inp Hs Ht.
apply (shape_strong_equiv_efs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T);
apply srealizes_of_realizes; assumption.
Qed.
Corollary shape_strong_equiv_ef_eq : ltac2:(TCodec.tc2 tcn__ShapeEF "RE'0':%211'3'9'R0yR0%211'H'4&M'I'NrCvQL&ErBrAr@r?r>r=r<r1%99;87654321r3%>4=<21r;r:r9r8r7r6r5r2%D9=87654321%H4>F1;&Or4%2261'1&5&G(>rFrErD%43321(F%14Q4Q1Q0O%85Q43O1<%:11%93Q0ON%54JIHG%<5Q82G1@%>11&7&@%118%215%4221%E261%F2;1p0H1p0L1p0Q71pS0QG1pR8QI1pR6QJ1pR>QL1pRFQN1pR@R01pR<R11pRHR21pRDR61pRBR81pT4R:1pS<R41pSFR61pS>R81pS:R91pSHR:1pSDR>1pSBR@1pSNRB1").
Proof.
intros until T'. intros inp Hs Ht Heq.
eapply shape_strong_equiv_ef; [| exact Ht].
eapply rz_conseq; [exact Hs | exact Heq].
Qed.
Corollary srealizes_strong_equiv_error_free_scfg : ltac2:(TCodec.tc2 tcn__ShapeEF "Q='8'?&M'I'Q0&=r6%211vQL&E&;%115&<%117&Dr4%211&A%113&C%115&B%117&Kr1%@9B><975321r2%G4DC21&L%D9FB@=;9713r3%K4HG21&6r8r7r5%46L32N16p061p0;1pS0Q41pR6Q61pRNQ81pRLQ91pR:Q;1pR4Q<1").
Proof.
intros [ssegs spc sph] [tsegs tpc tph] [ssp sbrk smb srnd] [tsp tbrk tmb trnd] T inp Hs Ht.
unfold strong_equiv_error_free_scfg. cbn [img_segments img_init_pc img_phdrs en_sp en_brk en_mmap_base en_draw] in Hs, Ht.
exact (shape_strong_equiv_efs ssegs spc sph ssp sbrk smb srnd source_alloc_limit
tsegs tpc tph tsp tbrk tmb trnd target_alloc_limit T inp Hs Ht).
Qed.
End WithCfg.
