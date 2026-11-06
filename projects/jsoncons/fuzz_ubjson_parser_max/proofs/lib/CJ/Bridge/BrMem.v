(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import MState Mem Cells Step Frame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Bridge_BrMem () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.BrMem.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "4Z_to_le_bytes"; "4bytes_le_to_Z"]; ["5agree_on"; "6cell"; "6cells_size"; "7stk"; "7wmono"; "8bytes_at"; "8le4"; "8mrd"; "8wr_at"; "9rw_cells"; ":add"; ":le"; ":lt"; ":mul"; ":of_nat"; ":pow"]; [":testbit"; "0a"; "0b"; "0b0"; "0b1"; "0b2"; "0b3"; "0bs"; "0cs"; "0hi"; "0i"; "0lo"; "0m"; "0m'"; "0n"; "0segs"]; [";bv"; ";bv_unsigned"; "0v"; "0x"]]).
Lemma Z_testbit_high8 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrMem "E'Q@y8%211'=&K+8r1%3221':'2&Q0&QAr3%22<1r2%5221(4%93821p0;1pRF@1pR6B1").
Proof.
intros b i Hi. pose proof (u8_range b) as Hb.
destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE]; [rewrite E; apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 8); [|lia].
apply Z.log2_lt_pow2; lia.
Qed.
Lemma bytes_le_to_Z_cons : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrMem "H'Q@y8%211'6%112':'=&?(3r2r1%33921%511&J&QA%12>6&M%:17+X0%3221%7251%@3?91pR@B1pR6E1").
Proof.
intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- Z.lxor_lor.
- rewrite Z.add_nocarry_lxor; [reflexivity|].
apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
+ change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
+ rewrite (Z_testbit_high8 b i) by lia. reflexivity.
- apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
+ change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
+ rewrite (Z_testbit_high8 b i) by lia. reflexivity.
Qed.
Lemma Z_to_le_bytes_to_Z : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrMem "?'6'Q@y8%211%411':&>&5r1%2261&?%113%6231%83915pR@:1").
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons.
pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
- rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by lia. exact IH.
Qed.
Lemma bytes_le_to_Z_bound : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrMem "G'6'Q@y8%211%411'9&Kz&?r1%211%5241&L&O+X0&N&5%12>8%311%6251%82:1%@2:1pR@B1").
Proof.
induction bs as [|b bs IH]; [cbn; lia|]. rewrite bytes_le_to_Z_cons. cbn [length].
pose proof (u8_range b). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.
Lemma le4_of_bytes : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrMem "N'Q@y8%211';yR0%511':'6%116&Fr1%211(3r5r4r3r2(7%11@%73A31%83B51%93C71%:3D91%A3?<1qS6C1%F2D1pR>H1pR<I1pR:J1pR8K1").
Proof.
intros b0 b1 b2 b3. exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])).
unfold le4. pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3]) as Hb. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Hb.
rewrite unsigned_lit by (change (256 ^ 4) with 4294967296 in Hb; lia).
exact (Z_to_le_bytes_to_Z [b0; b1; b2; b3]).
Qed.
Section WithSegs.
Variable segs : list Segment.
Definition agree_on (lo hi : Z) (m m' : word -> option byte) : Prop :=
forall a, lo <= a < hi -> m' (wa a) = m (wa a).
Lemma mrd_agree : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrMem "I'Q@yR0%211'8y8%511%311pS851':r2r1%211r3%113%63831&GvQ?%23158r4%4331:%<3>31p071pS8D1pRL@1pRJA1").
Proof. intros m m' x E. unfold mrd. rewrite E. reflexivity. Qed.
Lemma bytes_at_agree : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrMem "Q2'Q@yR0%211'8y8%511%311p051'='6%115&EvQ?r4r2r1%544321&@r3&J&N&5%12A8%311%5261r5%94821=%@4?2>9p021p0=1pR@D1pR4G1pRLI1pRJJ1").
Proof.
intros m m' a bs (H0 & H1 & HB) HA. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite (mrd_agree m m') by (apply HA; lia). apply HB. exact Hi.
Qed.
Lemma wmono_of_grows : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrMem "M'Q@yR0%211'8y8%511%311p051&<':r3r1%211(1%119%63931%811r2%811%:3=15%<11p051pS8D1&DvQ?%231?8p041pRLD1pRJE1").
Proof.
intros m m' Hg x Hx. unfold wview in *. destruct (m x) as [b|] eqn:E.
- specialize (Hg x ltac:(rewrite E; discriminate)). destruct (m' x); [discriminate| congruence].
- destruct (m' x); [discriminate| exact Hx].
Qed.
Lemma wr_at_wmono : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrMem "J'Q@yR0%211'8y8%511%311p051'=&HvQ?r4r2r1%544321&Dr5%23716r3%:49381p031p071pRN>1pR4?1pRLA1pRJB1").
Proof. intros m m' a n (H0 & H1 & HW) WM. split; [exact H0|]. split; [exact H1|]. intros i Hi. apply WM. apply HW. exact Hi. Qed.
Lemma rw_cells_agree : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrMem "Q7'Q@yR0%211'8y8%511%311p051'='6'A%211&IvQ?r4r2r1%544321&@r3&J&N&B%118%311%5261r5%94821=&Dr6%23A14%C4B25Ap021p061p0A1pRBH1p2L1pRLN1pRJO1").
Proof.
intros m m' A cs [[Hwf HB] HW] HA WM. split; [split; [exact Hwf|]|].
- eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by exact Hwf. exact HA.
- eapply wr_at_wmono; [exact HW| exact WM].
Qed.
Lemma stk_agree : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrMem "N'Q@yR0%211'8y8%511%311p051'=&CvQ?r4r2r1%544321&@r3r5%342617&Dr6%23;14%=4<25;p021p061p0;1pRDB1pRHC1pRLE1pRJF1").
Proof.
intros m m' lo hi (H0 & H1 & HS) HA WM. split; [exact H0|]. split; [exact H1|].
intros a Ha. destruct (HS a Ha) as [W [b Hb]]. split; [apply WM; exact W|].
exists b. rewrite (mrd_agree m m') by (apply HA; exact Ha). exact Hb.
Qed.
End WithSegs.
