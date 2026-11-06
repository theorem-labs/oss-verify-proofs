(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Frame () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Frame.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2iff"; "2not"; "3Z"]; ["4Segment"; "5store_ok"; "6wbytes"; "7frame_mod"; "7in_rng"; "7in_rngb"; "7outside"; "8rdn"; "9add"; "9le"; "9lt"; "9of_nat"; "9pow"; "0a"; "0base"; "0bs"]; ["0i"; "0len"; "0m"; "0m1"; "0m2"; "0m3"; "0mem"; "0mem'"; "0n"; "0rs"; "0rs'"; "0rs1"; "0rs2"; "0segs"; ":Z_to_bv"; ":bv"]; [":bv_unsigned"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition in_rng (a base : word) (len : Z) : Prop :=
(bv_unsigned base <= bv_unsigned a < bv_unsigned base + len)%Z.
Definition in_rngb (a base : word) (len : Z) : bool :=
(Z.leb (bv_unsigned base) (bv_unsigned a) && Z.ltb (bv_unsigned a) (bv_unsigned base + len))%bool.
Lemma in_rngb_spec : ltac2:(TCodec.tc2 tcn__Frame "D'Q?yR0%211'?&='<'1&Er3r2r1%43321(:%83721&D%13765%<231pR4>1pQN@1pQLA1").
Proof.
intros. unfold in_rngb, in_rng. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.
Fixpoint outside (a : word) (rs : list (word * Z)) : Prop :=
match rs with
| [] => True
| (b, n) :: rs' => ~ in_rng a b n /\ outside a rs'
end.
Lemma outside_app : ltac2:(TCodec.tc2 tcn__Frame "H'Q?yR0%211'4'9'?%2241%411&=&Fr3&0r2r1%33821%6251';%8275%9285%3221%<251pRJ>1pRH?1pQLE1").
Proof.
intros a rs1 rs2. induction rs1 as [|[b n] rs1 IH]; cbn; tauto.
Qed.
Definition frame_mod (mem mem' : word -> option byte) (rs : list (word * Z)) : Prop :=
(forall a, outside a rs -> mem' a = mem a) /\ mem_grows mem mem'.
Lemma frame_mod_refl : ltac2:(TCodec.tc2 tcn__Frame "C'Q?yR0%211'7y8%511%311p051'4'9'?%2291%411&Cr2r1%33221pRD51pR>;1").
Proof. intros. split; [intros; reflexivity | apply mem_grows_refl]. Qed.
Lemma frame_mod_weaken : ltac2:(TCodec.tc2 tcn__Frame "Q1'Q?yR0%211'7y8%511%311p051'4'9'?%2291%411&Fr1r2%3221r4%5231p031pQLB1&Cr5r3%33271r6%53143p031p081pRFA1pRDB1pR@H1pR>I1").
Proof.
intros mem mem' rs rs' Hw [He Hg]. split; [|exact Hg]. intros a Ha. apply He, Hw, Ha.
Qed.
Lemma frame_mod_trans : ltac2:(TCodec.tc2 tcn__Frame "N'Q?yR0%211'7y8%511%311p051'4'9'?%2291%411&Cr5r4r2%43321r7&0r3%23:61%93481p061p071pRJ=1pRH>1pR<D1pR:E1pR8F1").
Proof.
intros m1 m2 m3 rs1 rs2 [E1 G1] [E2 G2]. split.
- intros a Ha. apply outside_app in Ha as [H1 H2]. rewrite (E2 a H2). apply E1, H1.
- eapply mem_grows_trans; eassumption.
Qed.
Lemma frame_mod_trans_same : ltac2:(TCodec.tc2 tcn__Frame "L'Q?yR0%211'7y8%511%311p051'4'9'?%2291%411&Cr4r3r1%43321r2%63541r6%83176p031p061pRD<1pR<B1pR:C1pR8D1").
Proof.
intros m1 m2 m3 rs H1 H2. eapply frame_mod_weaken; [| exact (frame_mod_trans _ _ _ _ _ H1 H2)].
intros a Ha. apply outside_app. tauto.
Qed.
Lemma wbytes_outside : ltac2:(TCodec.tc2 tcn__Frame "Q?'4'Q?y8%211%411yR0%511'7%115p031&>&Dr1r2&K&3r4%22>1%411%83761%:11&I&H&Q@r3%22D1r5%<2H1%>11%7241&L+2+R0%3221%=251'<&Br6%24<F1>%=1?%53Q021p071p0F1pQLQ51pQNQ61pR6Q41pR0Q:1").
Proof.
intros bs m base a Hn Hb. unfold in_rng in Hn.
destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned base)) as [Hlt|Hge].
- apply wbytes_below; assumption.
- apply wbytes_above. lia.
Qed.
Lemma frame_mod_wbytes : ltac2:(TCodec.tc2 tcn__Frame "Q?'Q?yR0%211'7y8%511%311p051'4%114&I&H&Q@r2%22=1&K&3r1%22=1%411%9261&L+2+R0%3221%?251&Cr4&Br3%2331A(2'9'?%22Q01(8%D2OG%F11%34Q4591(6%116%:3731%@3?<1p0B1pR0Q31pQNQ;1pR6Q71").
Proof.
intros m base bs Hb. split.
- intros a [Ha _]. apply wbytes_outside; assumption.
- apply wbytes_grows.
Qed.
Lemma frame_mod_store_ok : ltac2:(TCodec.tc2 tcn__Frame "Q9'4'@%211'Q?yR0%211'7y8%511%311p051'9'?%2281%>11'5&Cr5r4r3%43321'<'1&Ar7r6r2%443281(:%83721r8%8416=<%;3:14p041p0>1pRBD1pQLO1pRDG1pR@L1pR>M1pRLQ61").
Proof. intros segs mem mem' rs a n [_ Hg] H. eapply store_ok_mono; eassumption. Qed.
Lemma frame_mod_byte : ltac2:(TCodec.tc2 tcn__Frame "Q0'Q?yR0%211'7y8%511%311p051'4'9'?%2291%411&Cr4r3r2%43321&F%1234'<r5%117r6%119%53C31p071p0:1pQLJ1pRDA1pR@G1pR>H1").
Proof. intros mem mem' rs a [He _] Ha. apply He, Ha. Qed.
Lemma frame_mod_rdn : ltac2:(TCodec.tc2 tcn__Frame "R5'4'@%211'Q?yR0%211'7y8%511%311p051'9'?%2281%>11'5&Cr5r4r3%43321';&Izr1%3221&J&K%11:%3251%9251&F&Q>&H&Q@%12OAr2%4221%62Q21r6%9221p0;1pR2N1%92Q7H%;21@&L+2+R0%3221%K251'<%QC1Q;%Q>11&Gr9r7%3421Q6Q7r8%5441Q8Q9%93731p0;1p0C1p0Q:1pQLQJ1pRBQA1pRDQC1pR@QH1pR>QI1pRLR21").
Proof.
intros segs mem mem' rs n. induction n as [|n IH]; intros a Hf Ho Hb; [reflexivity|].
cbn [rdn]. pose proof (u64_range a).
assert (Ha : mem' a = mem a).
{ pose proof (Ho 0%Z ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0.
eapply frame_mod_byte; eassumption. }
rewrite Ha.
destruct n as [|n'].
- reflexivity.
- assert (Ha1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
rewrite (IH (a + 1) Hf).
+ reflexivity.
+ intros i Hi. rewrite Ha1. replace (bv_unsigned a + 1 + i)%Z with (bv_unsigned a + (1 + i))%Z by lia.
apply Ho. lia.
+ rewrite Ha1. lia.
Qed.
End FPX_1.
