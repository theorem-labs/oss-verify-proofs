(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core
L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmModelFactsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmStepAB0 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStepAB0.PMKB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStepAB0.PMKB.Along."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepARB0.L5SAR."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0AA"; "0Aw"; "1app"; "1bool"; "1cons"; "1fst"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2not"]; ["2or"; "3Z"; "0FF"; "0HI"; "0L"; "0LB"; "0LB'"; "0LK"; "4Model"; "0M"; "0M'"; "0M1"; "0M2"; "5mrestrict"; "6credit"; "7BIGSHADOW_HI"]; ["7BIGSHADOW_LO"; "7S"; "7SB"; "7aacc"; "7ahid"; "7ar_sptop"; "7ar_stack_top"; "7fframe"; "7hl_img_hi"; "7hl_img_lo"; "7hl_rt_static"; "7ri_inv"; "7shadow_zero"; "7vml"; "7vml_of"; "8agree_on"]; ["9defined"; "9img_clear"; "9outside"; "9range"; "9u32_at"; "9u64_at"; "9u8_at"; ":zeros_at"; ";pa_rw_lo"; "<CHUNK"; "<VLong"; "<iss_at"; "<p_b"; "<p_k"; "<p_src"; "<p_tb"]; ["<parser_at"; "<parser_own"; "<pst"; "<sr_qc"; "<strm"; "<vs_own"; "<vstr"; "<vstr_at"; "=agA"; "=agsh"; ">accA"; ">annA"; ">aobjA"; ">ec_at"; ">visitor_at"; "?addrs_wf"]; ["?dep"; "?st"; "@base_okA"; "@err_okA"; "@ls_okA"; "Bblk_out"; "Awapp"; "Cahpres"; "Caobj"; "Castk"; "Ddk"; "Dek"; "EIn"; "Eincl"; "Fadd"; "Fdiv"]; ["Fle"; "Flt"; "Fmodulo"; "Fmul"; "Fpow"; "Fsub"; "0V"; "0W"; "0W1"; "0W2"; "0a"; "0a'"; "0ar"; "0b"; "0c"; "0cr"]; ["0g"; "0g'"; "0hi"; "0i"; "0lo"; "0m"; "0model"; "0n"; "0o"; "0ois"; "0op"; "0p"; "0q"; "0r"; "0s"; "0scr"]; ["0scr'"; "0segs"; "0sm"; "0sp"; "0sp'"; "GZ_to_bv"; "Gbv"; "0str"; "0v"; "0x"; "0y"]]).
Local Ltac lia := L5FastLia.plia.
Module PMKB.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Lemma S_in_shadow : ltac2:(TCodec.tc2 tcn__PmStepAB0 "G'A'=&S0zr1%3221&S1&S4+2+Q?%3221%5271%;271&Q0&Q1r2%211%?241&O%=231%C231p091pXFF1").
Proof. intros y. intros Hy. unfold S, SB, BIGSHADOW_LO, BIGSHADOW_HI. assert (0 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia). lia. Qed.
Lemma S_mono : ltac2:(TCodec.tc2 tcn__PmStepAB0 "='A&S0r2r1%3221&Q1r3%211%316%8221p061pXF;1pXD<1").
Proof. intros x y. intros H. unfold S. assert (x / 8 <= y / 8) by (apply Z.div_le_mono; lia). lia. Qed.
Lemma mod16_8' : ltac2:(TCodec.tc2 tcn__PmStepAB0 ">'A'>&S2r1+@%3221z%63721r2+8%8221%:3;15p051pXD=1").
Proof. intros x. intros H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 16) with ((q * 2) * 8) by lia. apply Z_mod_mult. Qed.
Lemma shadow_zero_sub : ltac2:(TCodec.tc2 tcn__PmStepAB0 "QB'T6yR0%211'9y8%511%311p051'A'>&S2r4+8%3221z%63721r3%7215%93:14&S0r6%221:&RNr5&S3%12=>%4231r7%42@8%7221%;241%<2A8&Q<r:r9r8%43321r;%6313;p031p091p0;1p0E1p0I1p0M1pW4Q51pVHQ61pW2Q71pVFQ81pQDQ:1").
Proof. intros M a g a' g'.
intros Ha Ha' H1 H2 Hg SZ j Hj. unfold byte_at.
assert (E : S a' + j = S a + ((a' - a) / 8 + j)).
{ unfold S. assert (a = 8 * (a / 8)) by (pose proof (Z.div_mod a 8 ltac:(lia)); lia). assert (a' = 8 * (a' / 8)) by (pose proof (Z.div_mod a' 8 ltac:(lia)); lia).
assert ((a' - a) / 8 = a' / 8 - a / 8). { replace (a' - a) with ((a' / 8 - a / 8) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. } lia. }
rewrite E. apply SZ. assert (a = 8 * (a / 8)) by (pose proof (Z.div_mod a 8 ltac:(lia)); lia). assert (a' = 8 * (a' / 8)) by (pose proof (Z.div_mod a' 8 ltac:(lia)); lia).
assert ((a' - a) / 8 = a' / 8 - a / 8). { replace (a' - a) with ((a' / 8 - a / 8) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. } lia.
Qed.
Definition wapp (W : list L5.range) : Prop := forall r, In r W -> fst r + snd r <= BIGSHADOW_LO \/ BIGSHADOW_HI <= fst r.
Lemma wapp_outside_shadow : ltac2:(TCodec.tc2 tcn__PmStepAB0 "G'7&QC%211'A&RFr2%211'=&S0&Q0%2215&S1&O%2281%7241&QBr4r3%3221p051p0>1pXDB1pV@D1").
Proof. intros W x. intros WA Hx r Hr Hin. destruct r as [b n]. specialize (WA _ Hr). unfold L5.in_rng in Hin. cbn [fst snd] in *. lia. Qed.
Lemma wapp_nil : ltac2:(TCodec.tc2 tcn__PmStepAB0 "5&RF(8&QC%211%411").
Proof. intros r []. Qed.
Lemma wapp_cons : ltac2:(TCodec.tc2 tcn__PmStepAB0 "O';'A%2211'7&QC%211'@&S0&RN&6r2%23::1&<%13<<3%6231&Q0%9221&O%;217%=231&RF%11;(5r4r3%33G21%611p061p091pV@H1pWLL1").
Proof. intros r W. intros H WA r' [<-|Hr]; [exact H| exact (WA r' Hr)]. Qed.
Lemma wapp_app : ltac2:(TCodec.tc2 tcn__PmStepAB0 "?'7&QC%211&RFr2%211&3r4r3%33821%711p061p071pVD;1pVB<1").
Proof. intros W1 W2. intros A B r Hr. apply in_app_or in Hr. destruct Hr; [apply A|apply B]; assumption. Qed.
Section Stk.
Variables (L : asan_layout) (ar : asan_run).
Lemma astk_after_ahpres : ltac2:(TCodec.tc2 tcn__PmStepAB0 "R1'7';'A%2211%411&Q7%611'T6yR0%211'9y8%511%311p051&QC%@11&RIvS<r7r5r4%544321&RGvDr:r9r3r2r8%796<549321;&S0&S5r6%22?1%32?>%5221%6248z%8216&Q6%11G&S4+2+Q?%3221%?251r<r;%Q04O21Hp041p0<1p0?1p0A1p0H1p0Q11pV@Q81pX2QG1pX:QH1pX0QI1pX8QJ1pQJQ?1pQHQ@1pQ6QI1pQ<QL1").
Proof. intros LB FF M1 M2 sp scr sp' scr' W.
intros (A16 & SLO & SHI & SPT & D1 & D2) (_ & DS & DK) H1 H2 H3 TOP.
assert (DEF : forall a, ahl_ceil ar <= a < 2 ^ 47 -> M1 (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None).
{ intros a Ha Hd. destruct (Z_lt_le_dec a (sp' - scr')) as [X|X]; [| destruct (Z_lt_le_dec a sp') as [Y|Y]].
- apply DK; [lia| |exact Hd]. unfold aclient, aclient_g. right; left. split; [lia| intros Z; lia].
- replace a with (sp' - scr' + (a - (sp' - scr'))) by lia. apply DS. lia.
- apply DK; [lia| |exact Hd]. unfold aclient, aclient_g. right; left. split; [lia| intros Z; lia]. }
split; [exact A16|]. split; [exact SLO|]. split; [exact SHI|]. split; [exact SPT|]. split.
- intros i Hi. apply DEF; [lia|]. apply D1. exact Hi.
- intros i Hi. apply DEF; [lia|]. apply D2. exact Hi.
Qed.
End Stk.
Section Along.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variables (L : asan_layout) (ar : asan_run).
Variables (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (W : list L5.range) (M M' : word -> option byte).
Hypothesis E : L5SAR.ek L ar LB FF sp scr W M M'.
Hypothesis WAPP : wapp W.
Lemma agA_frame : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q9'A&R<vBr2r1%43321&S0zr3%3221&RNr4%2214&S4+2+Q?%3221%;251'=r6%>21@&S1r5%=241%32D1%7251&QBvS7%221Ip041pW8N1&R8vIvJ%3421?<p051p0C1p0L1p0Q11pW@Q71pWBQ81").
Proof. intros o n.
intros (f & Hf & H1 & H2) Ho Hon OW. split.
- intros i Hi. apply E. split; [lia|]. split; [|apply OW; lia].
destruct f as [[F k] rs]. cbn [ff_addr ff_class fst snd] in *.
unfold aclient, aclient_g. right; right; right; left. exists (F, k, rs). split; [exact Hf|]. cbn [ff_addr ff_class fst snd]. lia.
- intros x Hx. pose proof (S_in_shadow x ltac:(lia)) as SH. unfold BIGSHADOW_LO, BIGSHADOW_HI in SH.
apply E. split; [lia|]. split.
+ destruct f as [[F k] rs]. cbn [ff_addr ff_class fst snd] in *.
unfold aclient, aclient_g. do 5 right. left. exists (F, k, rs). split; [exact Hf|]. cbn [ff_addr ff_class fst snd].
unfold in_shadow_of. split; apply S_mono; lia.
+ apply (wapp_outside_shadow W (S x) WAPP). unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
Qed.
Lemma agA_block : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q='A&RL';%1233(:r2r1%347721vE%83621&S0zr3%3221&RNr4%2214&S4+2+Q?%3221%;251'=r6%>21B&S1r5%=241%32F1%7251&QBvS7%221Kp041pW8Q21&R8vIvJ%3421?<p051p0C1p0L1p0Q11pW<Q;1pWJQ<1").
Proof. intros q m.
intros Hin Hq Hqm OW. split.
- intros i Hi. apply E. split; [lia|]. split; [|apply OW; lia]. unfold aclient, aclient_g. left. exists (q, m). split; [exact Hin|]. cbn [fst snd]. lia.
- intros x Hx. pose proof (S_in_shadow x ltac:(lia)) as SH. unfold BIGSHADOW_LO, BIGSHADOW_HI in SH.
apply E. split; [lia|]. split.
+ unfold aclient, aclient_g. do 6 right. exists (q, m). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply S_mono; lia.
+ apply (wapp_outside_shadow W (S x) WAPP). unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
Qed.
Lemma ag_img : ltac2:(TCodec.tc2 tcn__PmStepAB0 "QL'A&S0&Q9vD%211r2%5221&RNr3%2214&Q8%118%;231'=r5r1%?221&S1r4%<251%3251%8251&?&Q:%12EC%311p051pW8K1z%L21?r6%H21A&S4+2+R0%3221%Q3251r8%Q521Gr7%Q1231%H2J1%M241&QBvS7%221Q8p041pW8Q?1&Q?vIvJ%3421><p051p0A1p0I1p0L1p0Q<1p0QC1pW@QJ1pVFQK1").
Proof. intros a n.
intros H1 H2 NS Ha Han OW i Hi. apply E. split; [lia|]. split; [|apply OW; lia].
unfold aclient, aclient_g. right; right; left. split; [lia|]. apply NS. lia.
Qed.
Hypothesis FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47.
Hypothesis BRB : forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47.
Lemma aobjA_bounds : ltac2:(TCodec.tc2 tcn__PmStepAB0 "F'A&R<vBr2r1%43321'=&S0zr3%3221&RN%1239&S4+2+Q?%3221%:251%<281p0>1pW@D1pWBE1").
Proof. intros o n. intros (f & Hf & H1 & H2). destruct (FRB f Hf) as [B1 B2]. lia. Qed.
Lemma agA_obj : ltac2:(TCodec.tc2 tcn__PmStepAB0 "M'A&R<vBr2r1%43321'=&S0r4%2215&S1&RNr3%2251%42:1%9261&QBvS7%221?p041pW8D1&R8vIvJ%3421@<p051p0E1pW@K1pWBL1").
Proof. intros o n. intros AO OW. destruct (aobjA_bounds o n AO). apply agA_frame; assumption. Qed.
Lemma agA_blk : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q1'A&RL';%1233(:r2r1%347721vE%83621'=&S0r4%2217&S1&RNr3%2251%42<1%9261&QBvS7%221Ap041pW8H1&R8vIvJ%3421@<p051p0E1pW<O1pWJQ01").
Proof. intros q m. intros Hin OW. destruct (BRB _ Hin) as [B1 B2]. cbn [fst snd] in *. apply agA_block; assumption. Qed.
Lemma u64_keepA : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q2'A&R<vBr2+8%43321'=&S0r4r1%3221&S1&RN%1259%3251%9251&QBvS7%221?p041pW8D1&QEvT1vIr3%4432A1vJr5%74621Dp041p0:1p0J1pXBQ01pVFQ11").
Proof. intros a v. intros AO OW. destruct (aobjA_bounds a 8 AO). apply (L5C.u64_at_agree segs M M'); [exact (proj1 (agA_obj a 8 AO OW))|lia|lia]. Qed.
Lemma u32_keepA : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q2'A&R<vBr2+4%43321'=&S0r4r1%3221&S1&RN%1259%3251%9251&QBvS7%221?p041pW8D1&QDvT1vIr3%4432A1vJr5%74621Dp041p0:1p0J1pXBQ01pVFQ11").
Proof. intros a v. intros AO OW. destruct (aobjA_bounds a 4 AO). apply (PMF.u32_at_agree segs M M'); [exact (proj1 (agA_obj a 4 AO OW))|lia|lia]. Qed.
Lemma u8_keepA : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q2'A&R<vBr2+1%43321'=&S0r4r1%3221&S1&RN%1259%3251%9251&QBvS7%221?p041pW8D1&QFvT1vIr3%4432A1vJr5%74621Dp041p0:1p0J1pXBQ01pVFQ11").
Proof. intros a v. intros AO OW. destruct (aobjA_bounds a 1 AO). apply (L5C.u8_at_agree segs M M'); [exact (proj1 (agA_obj a 1 AO OW))|lia|lia]. Qed.
Lemma defined_keepA : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q0'A&R<vBr2r1%43321'=&S0r4%2215&S1&RNr3%2251%42:1%9261&QBvS7%221?p041pW8D1&Q@vI%231?;vJr5%5321Bp041p081p0H1pW@N1pVFO1").
Proof. intros a n. intros AO OW. apply (L5C.defined_agree M M' a n). exact (proj1 (agA_obj a n AO OW)). Qed.
Lemma acc_keepA : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q0'A&R<vBr2r1%43321'=&S0r4%2215&S1&RNr3%2251%42:1%9261&QBvS7%221?p041pW8D1&R:vI%231?;vJr5%5321Bp041p081p0H1pW@N1pVFO1").
Proof. intros a n. intros AO OW. apply PMFA.accA_agree. exact (proj2 (agA_obj a n AO OW)). Qed.
Definition blk_out (q m : Z) : Prop := forall i, q <= i < q + m -> L5.outside W i.
Lemma vstr_keepA : ltac2:(TCodec.tc2 tcn__PmStepAB0 "QI'A'R6&R<vBr2+H%43321&RM';%1299&R5%117vE%63421'=&S0r5r1%3221&S1&RN%125@%3251%9251&QBvS7%221Fp041pW8L1'>r7(QJr3%231M@%53Q141&REr4%22Q11p041pWHQ71pW@Q81pVNQ91&R7vT1&R:vIr6%554321OvJ%75651C3p031p0:1p0H1p0Q81p0Q@1pWNQF1pWBQH1").
Proof. intros o s.
intros AO INC OW OB. destruct (aobjA_bounds o 24 AO).
apply PMFA.vstr_at_agreeA; [lia|lia| apply agA_obj; assumption|].
intros c n p ->. apply agA_blk; [apply INC; left; reflexivity| exact (OB c n p eq_refl)].
Qed.
Lemma ec_keepA : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q4'A&R<vBr3+@%43321'=&S0r5r1%3221&S1&RN%1259%3251%9251&QBvS7r2%3221p051pW8E1&R=vT1vIr4%4532B1GvJr6%75621E4p041p0:1p0K1pVNQ11pXBQ21pWBQ31").
Proof. intros o v c.
intros AO OW (U & W8 & D & CC). destruct (aobjA_bounds o 16 AO). pose proof (agA_obj o 16 AO OW) as [AG SH].
split; [apply (PMF.u32_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact U]|].
split; [apply (L5C.u64_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact W8]|].
split; [exact (L5C.defined_agree M M' o 16 AG D)| exact (PMFA.accA_agree M M' o 16 SH CC)].
Qed.
Lemma visitor_keepA : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q1'A&R<vBr1+8%43321'=&S0r3%2216&S1&RN%1248%32:1%8251&QBvS7r2%3221p051pW8D1&R>vT1v0vI%44321AvJr4%746521p041p0:1p0J1pWBQ01").
Proof. intros o. intros AO OW (V & CC). split; [apply u64_keepA; assumption| apply acc_keepA; assumption]. Qed.
Lemma iss_keepA : ltac2:(TCodec.tc2 tcn__PmStepAB0 "QM'A'R6'R4&R<vBr3+X@%43321&RM';%12::&R5%117vE%63421'=&S0r6r1%3221&S1&RN%125@%3251%9251&QBvS7r2%3221p051pW8N1'>r8(QJ%13M7@%43Q231&REr4%22;1p041pWHQ81pW@Q91pVNQ:1&QKvT1v0&R:vIr7r5%7765432Q11vJ%978761D4Q3p031p0<1p0I1p0Q:1p0QB1pX6QH1pX@QJ1pWDQL1").
Proof. intros ois str sm.
intros AO INC OW OB. destruct (aobjA_bounds ois 272 AO).
apply PMFA.iss_at_agreeA; [lia|lia| apply agA_obj; assumption|].
intros c n p ->. apply agA_blk; [apply INC; left; reflexivity| exact (OB c n p eq_refl)].
Qed.
Lemma parser_keepA : ltac2:(TCodec.tc2 tcn__PmStepAB0 "RE'A'R2&R<vBr3+\0%43321&RM';%1299&R1r2%211vE%73521'=&S0r6r1%3221&S1&RN%125A%3251%9251&QBvS7%221@p041pW8M1&RE&R3&QNr4%211%411&QI%7221&QLr5%211&S3+Q0&S4+2&QM%117%4231%7261%C291'>'R6&QOr9%211(QJ%13QDQ=Q6%73631%L2Q?Ip021pWHQL1pW@QM1pVNQN1&R0vT1v0&R:&R;vIr8r7%8876543B21vJr:%;8:98721E5p041p0>1p0L1p0Q91p0QB1p0R21p0R;1pWNRA1pWDRC1pWFRD1").
Proof. intros op ois s.
intros AO INC OW OQ OV OT. destruct (aobjA_bounds op 384 AO).
assert (IQ : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB) by (apply INC; unfold PM.parser_own, PM.src_own; left; reflexivity).
assert (IV : In (PM.p_b s, 32 * 2 ^ PM.p_k s) LB) by (apply INC; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
destruct (BRB _ IQ) as [Q1 Q2]. destruct (BRB _ IV) as [V1 V2]. cbn [fst snd] in *.
apply PMFA.parser_at_agreeA; [lia|lia| apply agA_obj; assumption| lia| lia| apply agA_blk; assumption| lia| lia| apply agA_blk; assumption|].
intros c n p E1. apply agA_blk; [| exact (OT c n p E1)]. apply INC. unfold PM.parser_own, PM.vs_own. rewrite E1. right; right; left. reflexivity.
Qed.
Lemma ls_okA_keep : ltac2:(TCodec.tc2 tcn__PmStepAB0 "QE'RA'R?v0%211'A&R@r1%2251'=&S0&Q9vD%211r2%5221&S1&Q8%116%3251%;251&?&Q:%12;9%311&QBvS7%221=%C241%D291p0F1pVFJ1+RPP0%G21J&QH%11Q0%D2M1%L241p019pVFQ21&RDvT1v1r4vI%554Q:321r5vJ%857Q=621p041p0;1p0D1p0Q@1pW2QD1").
Proof. intros g.
intros WF SD SR. pose proof (PMST.aw_rw A WF) as Hrw. apply (PMSTA.ls_okA_frame segs A AA WF M M').
- intros a Ha D. destruct (SD a D) as (I1 & I2 & I3). apply E. split; [exact Ha|]. split; [|exact I3].
unfold aclient, aclient_g. right; right; left. split; [lia| exact I2].
- intros a Ha N. destruct (SR a Ha) as (I1 & I2 & I3). rewrite E; [exact N|]. split; [lia|]. split; [|exact I3].
unfold aclient, aclient_g. right; right; left. split; [lia| exact I2].
Qed.
Lemma err_okA_keep : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q<'4'R?v0%211'A&R@r1%2251'=&S0&Q9vD%211r2%5221&S1&Q8%116%3251%;251&?&Q:%12;9%311&QBvS7%221=%C241%D291p0F1pVFJ1&RCvT1v1vIr3%554Q2321vJr4%857Q5621p041p0;1p0Q71pVLQ;1").
Proof. intros b.
intros WF SD. apply (PMSTA.err_okA_frame segs A AA WF M M').
intros a Ha D. destruct (SD a D) as (I1 & I2 & I3). apply E. split; [exact Ha|]. split; [|exact I3].
unfold aclient, aclient_g. right; right; left. split; [lia| exact I2].
Qed.
Lemma agsh_obj : ltac2:(TCodec.tc2 tcn__PmStepAB0 ">'A&R<vBr2r1%43321&R9vIvJr3%443217p061pW@<1pWB=1").
Proof. intros o n.
intros AO. destruct (aobjA_bounds o n AO) as [Ho Hon]. destruct AO as (f & Hf & H1 & H2).
intros x Hx. pose proof (S_in_shadow x ltac:(lia)) as SH. unfold BIGSHADOW_LO, BIGSHADOW_HI in SH.
apply E. split; [lia|]. split.
- destruct f as [[F k] rs]. cbn [ff_addr ff_class fst snd] in *.
unfold aclient, aclient_g. do 5 right. left. exists (F, k, rs). split; [exact Hf|]. cbn [ff_addr ff_class fst snd].
unfold in_shadow_of. split; apply S_mono; lia.
- apply (wapp_outside_shadow W (S x) WAPP). unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
Qed.
Lemma acc_keepA' : ltac2:(TCodec.tc2 tcn__PmStepAB0 "A'A&R<vBr2r1%43321&R:vIr3%33216vJr4%63214p041p091pW@?1pVF@1").
Proof. intros a n. intros AO. apply PMFA.accA_agree. exact (agsh_obj a n AO). Qed.
Lemma base_ok_keepA : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q@'R?v0%211'A&R@r1%2251'=&S0&Q9vD%211r2%5221&S1&Q8%116%3251%;251&?&Q:%12;9%311&QBvS7%221=%C241%D291p0F1pVFJ1+RPP0%G21J&QH%11Q0%D2M1%L241p019pVFQ21&RBvT1vI%332Q81vJ%534Q:1p031p081p0A1p0Q=1").
Proof.
intros WF SD SR (RO0 & (can & Hcan & CAN) & NL & LL).
pose proof (PMST.aw_rw A WF) as Hrw. pose proof (PMST.aw_canary A WF) as Hcn. pose proof (PMST.aw_nl A WF) as Hnl. pose proof (PMST.aw_ll A WF) as Hll.
assert (AG : forall a, 0 <= a < 2 ^ 64 -> PMST.dep A a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha D. destruct (SD a D) as (I1 & I2 & I3). apply E. split; [exact Ha|]. split; [|exact I3].
unfold aclient, aclient_g. right; right; left. split; [lia| exact I2]. }
split; [|split; [|split]].
- intros i Hi. destruct (SR i Hi) as (I1 & I2 & I3). rewrite E; [apply RO0; exact Hi|]. split; [lia|]. split; [|exact I3].
unfold aclient, aclient_g. right; right; left. split; [lia| exact I2].
- exists can. split; [exact Hcan|]. apply (L5C.u64_at_agree segs M M'); [|lia|lia| exact CAN]. intros i Hi. apply AG; [lia|]. right; left. exact Hi.
- apply (L5C.u8_at_agree segs M M'); [|lia|lia| exact NL]. intros i Hi. apply AG; [lia| apply PMST.in_foot_nl; lia].
- unfold L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4%nat (pa_locale_lock A)); [exact LL|lia|cbn; lia|].
intros i Hi. apply AG; [cbn in Hi; lia| apply PMST.in_foot_ll; cbn in Hi; lia].
Qed.
Lemma stksh_keepA : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q>'A&S0zr2%3221&S5&Q5vS<%211+XPPP0%5221r3%;221&RNr4&S3+8%2216%5241&S4+2+Q?%3221%F251'>&S2r5%221;%43L1J%L2K3&Q<vIr7r6%43321vJr8%73215p041p0:1p0<1p0B1p0N1p0Q71pW2Q<1pW:Q=1").
Proof. intros lo g.
intros H0 H1 H2 H3 H4 SZ j Hj. unfold byte_at in *.
assert (L8 : lo = 8 * (lo / 8)) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
assert (SJ : S lo + j = S (lo + 8 * j)).
{ unfold S. replace (lo + 8 * j) with (j * 8 + lo) by lia. rewrite Z.div_add_l by lia. lia. }
pose proof (S_in_shadow (lo + 8 * j) ltac:(lia)) as SH. unfold BIGSHADOW_LO, BIGSHADOW_HI in SH.
rewrite E; [apply SZ; exact Hj|]. split; [rewrite SJ; lia|]. split.
- unfold aclient, aclient_g. do 4 right. left. unfold in_shadow_of. rewrite SJ. split; apply S_mono; lia.
- apply (wapp_outside_shadow W _ WAPP). rewrite SJ. unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
Qed.
Lemma img_clear_keepA : ltac2:(TCodec.tc2 tcn__PmStepAB0 "QA'A&S0zr2%3221&S4+2+R0%3221%8261'=r5r1%<221&S1r4%2241%7241&Q9vD%211%D21B&Q8%114%:2E1%?241&?&Q:%129I%311&QBvS7%221M%G241%H291p0B1pVFQ41&QAvI%231LHvJr6%5321Op041p081p0Q41p0Q:1pW6Q?1pW:Q@1").
Proof. intros lo hi.
intros Hlo Hhi IMG CL i Hi. destruct (IMG i Hi) as (I1 & I2 & I3). rewrite E; [apply CL; exact Hi|].
split; [lia|]. split; [|exact I3]. unfold aclient, aclient_g. right; right; left. split; [lia| exact I2].
Qed.
End Along.
Lemma zeros_of_aacc : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q9'T6yR0%211'9y8%511%311p051'A&Q3r3r2r1%43321'>&S2+8%2271z%53;21&S0r4%2241&QGr7&RN&ROr6%221<&Q2%5221r5%621@%:3931p0<1p0@1p0A1p0H1pW@N1pWBO1pQDQ11").
Proof. intros M o n.
intros C Ho Hn Hn0 i Hi.
assert (N8 : 8 * (n / 8) = n) by (pose proof (Z.div_mod n 8 ltac:(lia)); lia).
assert (O8 : 8 * (o / 8) = o) by (pose proof (Z.div_mod o 8 ltac:(lia)); lia).
destruct (C (o + 8 * i + 7) ltac:(lia)) as [B|(v & B & V1 & V2)].
- unfold byte_at, S in B. replace ((o + 8 * i + 7) / 8) with (o / 8 + i) in B; [replace (o / 8 + SB + i) with (o / 8 + i + SB) by lia; exact B|].
replace (o + 8 * i + 7) with (7 + (o / 8 + i) * 8) by lia. rewrite Z.div_add by lia. reflexivity.
- exfalso. replace ((o + 8 * i + 7) mod 8) with 7 in V2; [lia|].
replace (o + 8 * i + 7) with (7 + (o / 8 + i) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Section Vis.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : L5A.as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Lemma aobj_of_aobjA : ltac2:(TCodec.tc2 tcn__PmStepAB0 "H'7&Q7%211'A&R<r3r2r1%43321'>&S2+8%2271z%53;21&RHr5r4%3321=p051p0<1pW@B1pWBC1pQ6E1").
Proof. intros FF o n. intros (f & Hf & H1 & H2) H8. exists f. split; [exact Hf|]. split; [exact H1|]. split; [exact H2| exact H8]. Qed.
Lemma obj_shadow_vis : ltac2:(TCodec.tc2 tcn__PmStepAB0 "R9'7';'A%2211%411&Q7%611&N'T6yR0%211'9y8%511%311p051'H&Q;vCr9r8r7r6r5r4&Q>r3%211%;8:9876541&R<r2%23<51'>&S2+8%22;1z%53Q321&S1%123?%72A6%93Q715&R:%13HFE&QG&M&Q4r;%221Mr:%5221&RN&RO%12Q1C&Q2%4221%42Q3F%=3721p0?1p0B1p0E1p0H1p0O1p0Q31pW@QN1pWBQO1pW>QB1pQDQD1p6R01pW0QN1pQ@R01pQ6R11pQ<R41").
Proof. intros LB FF LK cr Aw M model o n.
intros HH AO O8 Hn N8 CC.
pose proof (L5SAR.aobj_facts L ar C HI LY HIok LB FF LK cr Aw M model o n 0 0 HH (aobj_of_aobjA FF o n AO O8) Hn N8) as (_ & _ & _ & _ & VS & _).
apply (proj2 (L5A.zeros_at_vis (ahid Aw model) M (o / 8 + SB) (n / 8) VS)). apply zeros_of_aacc; [exact CC|exact O8|exact N8|lia].
Qed.
Lemma blk_shadow_vis : ltac2:(TCodec.tc2 tcn__PmStepAB0 "RF'7';'A%2211%411&Q7%611&N'T6yR0%211'9y8%511%311p051'H&Q;vCr;r:r9r8r7r6&Q>r5%211%;8:9876541&RL(:r4%24NN61r<%53O21&S0%12<5&RN%12<7%22@?%5221'>&S2+8%22D1z%53Q<21&S1%123H%72J6%93Q@15&R:r=%231Q0O&QG&M&Q4r?%2216r>%5221&RO%12Q:C&Q2%K221%42Q<F%<3621p0>1p0B1p0E1p0H1p0O1p0Q41p0Q71p0Q>1pW@R91pWBR:1pW<R;1pWJR<1pW>QO1pQDR11p6R=1pW0R;1pQ@R=1pQ6R>1pQ<RA1").
Proof. intros LB FF LK cr Aw M model q m o n.
intros HH Hin H1 H2 O8 Hn N8 CC.
pose proof (L5SAR.vis_pack L ar C HI LY HIok LB FF LK cr Aw M model HH) as (_ & _ & _ & _ & _ & VBSH & _).
assert (VS : L5A.avis (ahid Aw model) (o / 8 + SB) (n / 8)).
{ apply (VBSH q m). exact Hin. intros i Hi. unfold in_shadow_of. assert (N8' : 8 * (n / 8) = n) by (pose proof (Z.div_mod n 8 ltac:(lia)); lia).
assert (O8' : 8 * (o / 8) = o) by (pose proof (Z.div_mod o 8 ltac:(lia)); lia).
split.
- replace (o / 8 + SB + i) with (S (o + 8 * i)). apply S_mono. lia. unfold S. replace (o + 8 * i) with (i * 8 + o) by lia. rewrite Z.div_add_l by lia. lia.
- replace (o / 8 + SB + i) with (S (o + 8 * i)). apply S_mono. lia. unfold S. replace (o + 8 * i) with (i * 8 + o) by lia. rewrite Z.div_add_l by lia. lia. }
apply (proj2 (L5A.zeros_at_vis (ahid Aw model) M (o / 8 + SB) (n / 8) VS)). apply zeros_of_aacc; [exact CC|exact O8|exact N8|lia].
Qed.
Lemma ek_sublb : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q:'7';'A%2211%411&Q7%611&QC%811'T6yR0%211'9y8%511%311p051&RMr7r8%33A21&RKvDvS<r9r6r5r4r3r2%99876<54321%:9987<=6543p021p0=1pQFB1pQDC1pV@L1pX0Q31pX8Q41pQ6Q11pQ>Q41pQ<Q51").
Proof. intros LB LB' FF sp scr W M M'.
intros I E a (Ha & Hc & Ho). apply E. split; [exact Ha|]. split; [|exact Ho].
unfold aclient, aclient_g in *. destruct Hc as [(b & Hb & X)|[X|[X|[X|[X|[X|(b & Hb & X)]]]]]].
- left. exists b. split; [apply I; exact Hb| exact X].
- right; left; exact X. - right; right; left; exact X. - do 3 right; left; exact X. - do 4 right; left; exact X. - do 5 right; left; exact X.
- do 6 right. exists b. split; [apply I; exact Hb| exact X].
Qed.
Lemma dk_sublb : ltac2:(TCodec.tc2 tcn__PmStepAB0 "Q6'7';'A%2211%411&Q7%611'T6yR0%211'9y8%511%311p051&RMr6r7%33?21&RJvDvS<r8r5r4r3r2%88765;4321%98876;<543p021p0<1pQFA1pQDB1pX0O1pX8Q01pQ6M1pQ>Q01pQ<Q11").
Proof. intros LB LB' FF sp scr M M'.
intros I D a Ha Hc HM. apply D; [exact Ha| |exact HM].
unfold aclient, aclient_g in *. destruct Hc as [(b & Hb & X)|[X|[X|[X|[X|[X|(b & Hb & X)]]]]]].
- left. exists b. split; [apply I; exact Hb| exact X].
- right; left; exact X. - right; right; left; exact X. - do 3 right; left; exact X. - do 4 right; left; exact X. - do 5 right; left; exact X.
- do 6 right. exists b. split; [apply I; exact Hb| exact X].
Qed.
Lemma ek_own_frame : ltac2:(TCodec.tc2 tcn__PmStepAB0 "S8'7';'A%2211%411&Q7%611&N'T6yR0%211'9y8%511%311p051pXD62&Q=&QC%C11&Q;vCr=r<r;r:r9r8r6%9887654321'=&S0+SoonPPPPP0&Q5vS<%211%5241&S4+2+Q?%3221%:261%<261&S5+XPPP0%22:1r4%@221r7%62F1r5%D221%E22Jzr1%H221&S1+R0%E2D1%3251%N251&?r2%Q02Q51%822Q5%Q3221%511'>r?&T5r3%22QN1%411r@%113%83QM31p0:1p0A1pVFR<1&RKvDrCrBr>%594QB32QLQKQJ1QNp071p0Q21p0Q41p0Q91p0Q?1p0QM1pW6RI1pW:RJ1pV@R:1pX0RL1pX8RM1pV>R?1pQFRA1pQDRC1p6RO1pW0RM1pQ@RO1pQ6S01pQ<S31").
Proof. intros LB FF LK cr Aw M M' V sp scr W lo hi.
intros HH SPT H0 H1 H2 FR. apply (L5SAR.ek_piece L ar LB FF sp scr W M M' (fun a => lo <= a < hi) FR).
intros a Ha Hc _ X. destruct (L5SAR.aclient_cases L ar C HI LY HIok LB FF LK cr Aw M V sp scr a HH SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; lia|].
exfalso. lia.
Qed.
End Vis.
End PMKB.
