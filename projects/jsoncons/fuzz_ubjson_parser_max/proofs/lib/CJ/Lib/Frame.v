(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec MState Mem Cells Exec Step.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_Frame () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1Some"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4write_to_mem"; "5bvmap"]; ["5bvmap_empty"; "5bvmap_set"; "6CB"; "6cell"; "6cells_size"; "8munch"; "8stk"; "8sub_fp"; "8wmono"; "7disjoint_from"; "7inside"; "7ivl"; "7mkR"; "7outside"; "9bytes_at"; "9wa"]; ["9wr_at"; ":ro_cells"; ":rw_cells"; ";add"; ";le"; ";lt"; ";of_nat"; ";pow"; ";sub"; ";to_nat"; "0W"; "0W'"; "0a"; "0b"; "0bs"; "0cs"]; ["0hi"; "0junk"; "0lo"; "0m"; "0m'"; "0m0"; "0m1"; "0m2"; "0m3"; "0mid"; "0n"; "0segs"; "<Z_to_bv"; "<bv"; "0x"; "0x1"]; ["0x10"; "0x11"; "0x12"; "0x13"; "0x14"; "0x15"; "0x16"; "0x17"; "0x18"; "0x19"; "0x2"; "0x20"; "0x21"; "0x22"; "0x23"; "0x24"]; ["0x25"; "0x26"; "0x27"; "0x28"; "0x29"; "0x3"; "0x30"; "0x31"; "0x4"; "0x5"; "0x6"; "0x7"; "0x8"; "0x9"]]).
Definition mkR (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) : bvmap 5 word :=
TNode
(TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty)))
(Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty))))
None
(TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2)
(TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))).
Lemma mkR_spec : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "U9'QMyR0%211'9&?y5%2214&LrOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@r?r>r=r<r;r:r9r8r7r6r5r4r3r2r1%Q0OONMLKJIHGFEDCBA@?>=<;:987654321&A&QL+O%22Q61+N%42Q81+M%62Q:1+L%82Q<1+K%:2Q>1+J%<2Q@1+I%>2QB1+H%@2QD1+G%B2QF1+F%D2QH1+E%F2QJ1+D%H2QL1+C%J2QN1+B%L2R01+A%N2R21+@%Q02R41+?%Q22R61+>%Q42R81+=%Q62R:1+<%Q82R<1+;%Q:2R>1+:%Q<2R@1+9%Q>2RB1+8%Q@2RD1+7%QB2RF1+6%QD2RH1+5%QF2RJ1+4%QH2RL1+3%QJ2RN1+2%QL2S01+1%QN2S21&@%12S4S7%R25S5S83S21%R35S6S96S21%R45S7S:9S21%R55S8S;<S21%R65S9S<?S21%R75S:S=BS21%R85S;S>ES21%R95S<S?HS21%R:5S=S@KS21%R;5S>SANS21%R<5S?SBQ1S21%R=5S@SCQ4S21%R>5SASDQ7S21%R?5SBSEQ:S21%R@5SCSFQ=S21%RA5SDSGQ@S21%RB5SESHQCS21%RC5SFSIQFS21%RD5SGSJQIS21%RE5SHSKQLS21%RF5SISLQOS21%RG5SJSMR2S21%RH5SKSNR5S21%RI5SLSOR8S21%RJ5SMT0R;S21%RK5SNT1R>S21%RL5SOT2RAS21%RM5T0T3RDS21%RN5T1T4RGS21%RO5T2T5RJS21%S05T3T6RMS21%T63T3S21pU@T81pU>T91pU:T:1pU8T;1pU6T<1pU4T=1pU2T>1pU0T?1pTNT@1pTLTA1pTJTB1pTHTC1pTDTD1pTBTE1pT@TF1pT>TG1pT<TH1pT:TI1pT8TJ1pT6TK1pT4TL1pT2TM1pULTN1pUJTO1pUHU01pUFU11pUDU21pUBU31pU<U41pTFU51pT0U61").
Proof. intros. vm_compute. reflexivity. Qed.
Definition ivl := (Z * Z)%type.
Fixpoint outside (W : list ivl) (x : Z) : Prop :=
match W with
| [] => True
| (lo, hi) :: W' => ~ (lo <= x < hi)%Z /\ outside W' x
end.
Fixpoint inside (W : list ivl) (a : Z) (n : Z) : Prop :=
match W with
| [] => False
| (lo, hi) :: W' => (lo <= a /\ a + n <= hi)%Z \/ inside W' a n
end.
Fixpoint disjoint_from (W : list ivl) (a : Z) (n : Z) : Prop :=
match W with
| [] => True
| (lo, hi) :: W' => (a + n <= lo \/ hi <= a)%Z /\ disjoint_from W' a n
end.
Lemma inside_not_outside : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "L'4&K%211'=&Jr4r3r2%43321'8&Q4%1264&Q5&Q3%1298%3281%7251&;&Mr6%221>%411p061p0?1pSNE1pSFF1pRJG1pRFI1").
Proof.
induction W as [|[lo hi] W IH]; cbn; intros a n x Hin Hx; [tauto|].
intros [H1 H2]. destruct Hin as [Hin|Hin]; [lia|]. exact (IH _ _ _ Hin Hx H2).
Qed.
Lemma disjoint_outside : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "J'4&K%211'=&Ir4r3r2%43321'8&Q4%1264&Q5&Q3%1298%3281%7251&Mr6%221=p041p0=1pSNC1pSFD1pRJE1pRFG1").
Proof.
induction W as [|[lo hi] W IH]; cbn; intros a n x Hd Hx; [exact I|].
destruct Hd as [H1 H2]. split; [lia|]. eauto.
Qed.
Section WithSegs.
Variable segs : list Segment.
Definition munch (W : list ivl) (m m' : word -> option byte) : Prop :=
forall x : word, outside W (bv_unsigned x) -> m' x = m x.
Definition wmono (m m' : word -> option byte) : Prop :=
forall x : word, wview segs m x <> None -> wview segs m' x <> None.
Lemma munch_refl : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "A'4&K%211'QMyR0%211'7y8%511%311p051&Er2r1%33211pS851pRF>1"). Proof. intros W m x _; reflexivity. Qed.
Lemma wmono_refl : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "<'QMyR0%211'7y8%511%311p051&Hr1%2211pS841"). Proof. intros m x H; exact H. Qed.
Lemma wmono_trans : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "C'QMyR0%211'7y8%511%311p051&Hr3r2%3221r5%5214p031p041pSB91pS@:1pS>;1").
Proof. intros m1 m2 m3 H1 H2 x Hx. apply H2, H1, Hx. Qed.
Lemma munch_trans : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "J'4&K%211'QMyR0%211'7y8%511%311p051&Er4r3r2%43321r5%63143r6%83136p031p061pSB<1pS@=1pS>>1pRFG1").
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.
Definition sub_fp (W W' : list ivl) : Prop := forall x, outside W' x -> outside W x.
Lemma munch_weaken : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "J'4&K%211'QMyR0%211'7y8%511%311p051&Gr4r3%3221&Er5r2%33251%43376p021p071pS:<1pS8=1pRHF1pRFG1").
Proof. intros W W' m m' Hs H x Hx. apply H, Hs, Hx. Qed.
Lemma munch_write : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "QF'4&K%211'QMyR0%211'7y8%511%311p051'=%<14&Er5r4r3%43321&Q4z%2214&Q3&Q6&3%12@8%311%52;1&Q7+2+R0%3221%=251&Jr8%;2JC%=11%433F1r9&>r7&Or6%211%5341M%O37;1p091p0?1p0K1p0O1pRNQ51pRJQ71pS8Q91pS<Q:1pRFQC1").
Proof.
intros W m0 m a bs H Ha Hl Hin x Hx. rewrite write_to_mem_spec by lia.
pose proof (bv_unsigned_in_range 64 x).
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb];
try (apply H; exact Hx).
exfalso. eapply (inside_not_outside W a _ (bv_unsigned x) Hin); [lia| exact Hx].
Qed.
Lemma wmono_write : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "H'QMyR0%211'7y8%511%311p051'4%114&Hr4r3%3221r5&>r2%23651%8241p061pRN;1pRJC1pS8?1pS<@1").
Proof. intros m0 m a bs H x Hx. apply wview_write_mono. apply H, Hx. Qed.
Lemma bytes_at_transport : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "Q8'4&K%211'QMyR0%211'7y8%511%311p051'=%<14&NvQKr4r2r1%544321&Er6r5%33217&Ir7&Q6&3r3%22D1%411%736?1%B4A;:@p021p0;1p0@1pRNG1p2I1pS:K1pS8L1pRFQ51").
Proof.
intros W m m' A bs (Ha & Hl & H) Hm Hd. split; [lia|]. split; [lia|].
intros i Hi. unfold mrd. rewrite Hm.
- apply H. exact Hi.
- eapply disjoint_outside; [exact Hd|]. rewrite wa_unsigned by lia. lia.
Qed.
Lemma wr_at_transport : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "J'QMyR0%211'7y8%511%311p051'=&Q0vQKr4r2r1%544321&Hr5%2216r3%:49381p031p071pSF>1p2?1pS:A1pS8B1").
Proof. intros m m' A n (Ha & Hn & H) Hw. split; [lia|]. split; [lia|]. intros i Hi. apply Hw, H, Hi. Qed.
Lemma rw_cells_transport : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "Q<'4&K%211'QMyR0%211'7y8%511%311p051'='C%=11&Q2vQKr4r2r1%544321&Er6r5%33217&H%1243&Ir8&Q6&D%11>%311%635:1r7%D4C1=<p031p0;1p0>1p0C1pS0J1p2M1pS:O1pS8Q01pRFQ91").
Proof.
intros W m m' A cs [[Hwf Hb] Hw] Hm Hmono Hd. split; [split; [exact Hwf|]|].
- eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact Hd.
- eapply wr_at_transport; eauto.
Qed.
Lemma ro_cells_transport : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "Q9'4&K%211'QMyR0%211'7y8%511%311p051'='C%=11&Q1vQKr4r2r1%544321&Er6r5%33217&Ir7&Q6&Dr3%211%411%736?1%B4A;:@p021p0;1p0@1pS0G1p2J1pS:L1pS8M1pRFQ61").
Proof.
intros W m m' A cs [Hwf Hb] Hm Hd. split; [exact Hwf|].
eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact Hd.
Qed.
Definition stk (m : word -> option byte) (lo hi : Z) : Prop :=
(0 <= lo)%Z /\ (hi <= 2^64)%Z /\
forall a, (lo <= a < hi)%Z -> wview segs m (wa a) <> None /\ exists b, mrd segs m (wa a) = Some b.
Lemma stk_split : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "O'QMyR0%211'7y8%511%311p051'=&Fr4r3r1%43321'8&Q4%1265r2%3271%5231r6r5%=321<%>33=<%:221p061p0=1pS2C1pSDD1pS6E1pS8G1").
Proof. intros m lo mid hi (H1 & H2 & H) Hm. split; (split; [lia|]; split; [lia|]); intros a Ha; apply H; lia. Qed.
Lemma stk_merge : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "O'QMyR0%211'7y8%511%311p051'=&Fr4r3r2%43321r5%63143'8&Q4%1248%2298%4221r7r6%>321=p041p0:1p0=1pS2C1pSDD1pS6E1pS8G1").
Proof.
intros m lo mid hi (A1 & A2 & A) (B1 & B2 & B) Hm. split; [lia|]. split; [lia|].
intros a Ha. destruct (Z.ltb_spec0 a mid); [apply A | apply B]; lia.
Qed.
Lemma stk_empty : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "K'QMyR0%211'7y8%511%311p051'='8&Q4zr1%3221&Q7+2+R0%3221%8261%:261&Fr3r2%33211p051pS6A1pS8C1").
Proof. intros. split; [lia|]. split; [lia|]. intros a Ha. lia. Qed.
Section SE.
Local Abbreviation SEC_T_stk_bytes := (ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "Q;'QMyR0%211'7y8%511%311p051'=&Fr3r2r1%43321&Q4%1254':'4%11='8'9'5&3%12B;&Q9&Q8r4r5%3221%511%:3971&NvQKr6%34217F%@251qRNB1%E2C1p0G1p0J1pS2Q01pS6Q11pS8Q31")) (only parsing).
Variable m : ltac:(sec_ty2 constr:(SEC_T_stk_bytes) 0%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_stk_bytes) 1%nat 0%nat).
Variable hi : ltac:(sec_ty2 constr:(SEC_T_stk_bytes) 2%nat 0%nat).
Lemma stk_bytes : ltac:(sec_stmt2 constr:(SEC_T_stk_bytes) 3%nat 0%nat).
Proof.
intros (H1 & H2 & H) Hle.
set (n := Z.to_nat (hi - lo)).
assert (G : forall k, (k <= n)%nat -> exists bs, length bs = k /\ forall i, (i < k)%nat -> mrd segs m (wa (lo + Z.of_nat i)) = nth_error bs i).
{ induction k as [|k IH]; intros Hk.
- exists []. split; [reflexivity|]. intros i Hi; lia.
- destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
destruct (H (lo + Z.of_nat k)%Z ltac:(lia)) as [_ (b & Hb)].
exists (bs ++ [b]). split. { rewrite app_length; cbn; lia. }
intros i Hi. destruct (Nat.eqb_spec i k).
+ subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. exact Hb.
+ rewrite nth_error_app1 by lia. apply Hbs. lia. }
destruct (G n ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
split; [lia|]. split; [lia|]. intros i Hi. apply Hbs. lia.
Qed.
End SE.
Lemma stk_carve : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "QE'QMyR0%211'7y8%511%311p051'='5&Fr4r3r2%43321&Q4&Q8&Q6%115%3271%5291'8r6r5%71<%92>1%@3431':'4%11H&Q2vQKr7%@1F%B2;1(2'C(Br1%22L1(6%115%73631%=4<;91qS4?1%B2@1%I2D1p0K1p0Q21pSFQ81pS2Q:1pS6Q;1pS8Q=1").
Proof.
intros m lo hi n Hs Hle. pose proof Hs as (H1 & H2 & H).
destruct (stk_split m lo (hi - Z.of_nat n) hi Hs ltac:(lia)) as [Hlo Hhi].
split; [exact Hlo|].
destruct (stk_bytes m (hi - Z.of_nat n) hi Hhi ltac:(lia)) as (bs & Hlen & Hb).
exists bs. split.
- split. { cbn. split; [lia|exact I]. }
cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
- cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
intros i Hi. apply H. lia.
Qed.
Lemma stk_of_rw_cells : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "O'QMyR0%211'7y8%511%311p051'='4'C%211&Q2vQKr3r2r1%544321&Fr4&Q3&Q6&D%118%311%52;1%837<1p0:1pS0A1p2E1pS8G1").
Proof.
intros m A cs [[Hwf (Ha & Hl & Hb)] (_ & _ & Hw)].
rewrite cells_bytes_length in Hl, Hb by assumption.
split; [lia|]. split; [lia|]. intros a Hr. split.
- replace a with (A + (a - A))%Z by lia. apply Hw. lia.
- replace a with (A + Z.of_nat (Z.to_nat (a - A)))%Z by lia. rewrite Hb by lia.
destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
apply nth_error_None in E. rewrite cells_bytes_length in E by assumption. lia.
Qed.
Lemma stk_release : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "Q7'QMyR0%211'7y8%511%311p051'='4'C%211&Fr4r3r2%43321&Q2vQKr5%342165&Q4%1239r7r6&Q3&Q6&D%11?%311%52;1%C3871p0:1p0=1p0B1pS0H1p2L1pS6M1pS8O1").
Proof.
intros m lo A cs Hs Hc Hle. pose proof (rw_cells_bound segs m A cs Hc).
eapply stk_merge; [exact Hs | apply stk_of_rw_cells; exact Hc | lia].
Qed.
Lemma stk_write : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "Q>'QMyR0%211'7y8%511%311p051'='4%115&Fr5r4r3%43321&Q4z%2214&Q3&Q6&3%12A8%311%52;1&Q7+2+R0%3221%=251&>r8&O%11E%4331Er7r6%J3321p091p0E1p0I1pRNO1pRJQ21pS2Q31pS6Q41pS8Q61").
Proof.
intros m lo hi a bs (H1 & H2 & H) Ha Hl. split; [lia|]. split; [lia|]. intros x Hx.
destruct (H x Hx) as [Hw (b & Hb)]. split.
- apply wview_write_mono. exact Hw.
- unfold mrd. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try (eexists; exact Hb).
destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
Qed.
Lemma stk_transport : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "QK'4&K%211'QMyR0%211'7y8%511%311p051'=&Fr4r2r1%43321&Er6r5%33217&H%1243'8&Q4%127:&Q5%12<8%5231'<&Mr:%221B':'9r9&Or3%211%411(1%12Q1J%83Q131qRLQ31%;2Q41%@2=1p0B1pSNQ41r7%Q531ONp031p0M1p0Q01p0Q51pS2Q;1pS6Q<1pS:Q>1pS8Q?1pRFQH1").
Proof.
intros W m m' lo hi (H1 & H2 & H) Hm Hw Hcase. split; [lia|]. split; [lia|].
intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
destruct (Hcase a Ha) as [Ho | (b' & Hb')].
- exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
- exists b'. unfold mrd. rewrite Hb'. reflexivity.
Qed.
Lemma stk_transport_disjoint : ltac2:(TCodec.tc2 tcn__CJ_Lib_Frame "Q7'4&K%211'QMyR0%211'7y8%511%311p051'=&Fr4r2r1%43321&Er6r5%33217&H%1243&Ir8&Q8%12=7%43381r7%A31;:p031p091p0<1p0A1pS2G1pS6H1pS:J1pS8K1pRFQ41").
Proof.
intros. eapply stk_transport; eauto. intros x Hx. left. eapply disjoint_outside; eauto. lia.
Qed.
End WithSegs.
