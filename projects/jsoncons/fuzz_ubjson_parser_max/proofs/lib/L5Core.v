(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__L5Core () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "1None"; "1S"; "1Some"; "1app"; "1bool"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"]; ["1snd"; "1true"; "2I"; "2and"; "2eq"; "2iff"; "2not"; "2or"; "3lt"; "4firstn"; "4map"; "4repeat"; "5Z"; "0F"; "0HI"; "0L"]; ["0LB"; "6store_ok"; "6wview"; "7SpuriousCfg"; "8Model"; "8VmMaps"; "8m_halted"; "8m_vm_lazy"; "8m_vm_materialized"; "0M"; "0M'"; "0M1"; "0M2"; "0M3"; "9blocks_apart"; "9client_addr"]; ["9credit"; "9heap_iface"; "9heap_iface_ok"; "9heap_layout"; "9hi_heap"; "9hl_alloc_ro"; "9hl_alloc_static"; "9hl_errno"; "9hl_img_hi"; "9hl_img_lo"; "9hl_sptop"; "9in_block"; "9in_errno"; "9lb_remove"; "9model_but_vm"; ":agree_on"]; [":fresh_block"; ":hpres"; ":kept"; ":stk"; ";big_at"; ";bigobj"; ";bytes_at"; ";defined"; ";frame_but"; ";hull_apart"; ";hull_hi"; ";hull_lo"; ";in_rng"; ";limbs_at"; ";lstr_short"; ";outside"]; [";range"; ";u64_at"; ";u8_at"; ";writable"; "<rdn"; "=mem_grows"; ">In"; "?add"; "?le"; "?lt"; "?modulo"; "?mul"; "?of_nat"; "?pow"; "?sub"; "0VM"]; ["0W"; "0W'"; "0a"; "0a'"; "0b"; "0bs"; "0cr"; "0i"; "0k"; "0m"; "0m'"; "0m''"; "0n"; "0n'"; "0o"; "0p"]; ["0q"; "0r"; "0s"; "0scfg"; "0scr"; "0scr'"; "0segs"; "0sp"; "0sp'"; "0sptop"; "@BV"; "@Z_to_bv"; "@bv"; "@bv_add"; "@bv_unsigned"; "0v"]; ["0ws"; "0ws1"; "0ws2"; "0x"; "0z"]]).
Local Ltac lia := L5FastLia.plia.
Module L5C.
Section WithSegs.
Variable segs : list Segment.
Lemma add1_lit : ltac2:(TCodec.tc2 tcn__L5Core "C'L'D'SLyR0%211&SM&SKr1%2251(SJ+1(B%33921%83:51&RG%1285%:2=1%@3=41pX:B1").
Proof. intros z.
apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_unsigned (1%bv : bv 64)) with 1. apply Zplus_mod_idemp_l.
Qed.
Definition stk (sptop : Z) (M : word -> option byte) (sp scr : Z) : Prop :=
sp mod 16 = 0 /\ sptop - 2 ^ 23 + scr <= sp /\ sp <= sptop /\ (0x7fff80000000 <= sptop <= 2 ^ 47) /\ L5.defined M (sp - scr) scr.
Lemma stk_floor : ltac2:(TCodec.tc2 tcn__L5Core "I'L'SLyR0%211'=y8%511%311p051&R3r4r3r2r1%544321&RH&RG+SoomohPPP0%2216%4218p061pW:E1pW@F1pRD?1pWDH1").
Proof. intros sptop M sp scr. intros (_ & B & _ & D & _). lia. Qed.
Lemma stk_window : ltac2:(TCodec.tc2 tcn__L5Core "Q9'L'SLyR0%211'=y8%511%311p051&R3r4r3r2r1%544321'C&RH&RG&RNr5&RM+2+G%3221%6251%821=%:21?%;2@8+SoonPPPPP0%=21:+Q?%;2:1%@2=1%B241%C271%D291p0F1pW:Q51pW@Q61pRDO1pWDQ81").
Proof. intros sptop M sp scr. intros (_ & B & C & D & _). repeat split; lia. Qed.
Definition kept (L : heap_layout) (LB : list (Z * Z)) (sp scr : Z) (W : list L5.range) (a : Z) : Prop :=
0 <= a < 2 ^ 64 /\ client_addr L LB sp scr a /\ ~ in_errno L a /\ L5.outside W a.
Definition hpres (L : heap_layout) (LB : list (Z * Z)) (sp scr : Z) (W : list L5.range) (M M' : word -> option byte) : Prop :=
(forall a, kept L LB sp scr W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
/\ L5.defined M' (sp - scr) scr
/\ (forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp scr a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None).
Lemma hpres_kept : ltac2:(TCodec.tc2 tcn__L5Core "Q<'QC':'?'L%2211%411&R@%611'SLyR0%211'=y8%511%311p051&R1r8r7r6r5r4r3r2%877654321&R2r9%261:9874'D&SK%12E8%:11%<12%53C21p071p0;1pV6Q11pRFF1pRDG1pV2Q01pW:Q51pW@Q61pR2Q51pR0Q;1").
Proof. intros L LB sp scr W M M' a. intros [P _] K. apply P. exact K. Qed.
Lemma hpres_defined : ltac2:(TCodec.tc2 tcn__L5Core "Q5'QC':'?'L%2211%411&R@%611'SLyR0%211'=y8%511%311p051&R1r7r6r5r4r3r2r1%877654321&R7&RN%1298%33619p051pRF?1pRD@1pV2I1pW:N1pW@O1pR2N1pR0Q41").
Proof. intros L LB sp scr W M M'. intros (_ & D & _). exact D. Qed.
Lemma hpres_cdef : ltac2:(TCodec.tc2 tcn__L5Core "R6'QC':'?'L%2211%411&R@%611'SLyR0%211'=y8%511%311p051&R1r8r7r6r5r4r3r2%877654321'C&RHz%2215&RI&RM+2+R0%3221%52;1%:271&Q?r:r9%3521FEA&F&QLr;%221F%411'D&SK%12Q6K%N11(2%11Q5%63Q531%<11%72Q<Q2%Q411%:3Q915%@11p051p0>1p0D1p0I1p0Q51pV6QK1pRFQ@1pRDQA1pV2QJ1pW:QO1pW@R01pR2QO1pR0R51").
Proof. intros L LB sp scr W M M' a. intros (_ & _ & C). apply C. Qed.
Lemma hpres_intro : ltac2:(TCodec.tc2 tcn__L5Core "RF'QC':'?'L%2211%411&R@%611'SLyR0%211'=y8%511%311pX851&R2r8r7r6r5r4r1%76654321'Dr3&SKr2%22C1%411%912%73A21p091pV6N1&R7&RN%12A@%33:1A'C&RHz%221C&RI&RM+2+R0%3221%52I1%:271&Q?r;r:r9%45321Q4J&F&QLr<%221Q0%411%Q12QBQ6%Q;11(2%11QA%Q73QA31%:11%Q72QHQ=%QA11%Q;3QE15%>11p051p0<1p0B1p0H1pV6R61&R1%17HGQJQIQHQGQFp031p0Q81p0Q=1pRFR01pRDR11pV2R:1pW:R?1pW@R@1pR2R?1pR0RE1").
Proof. intros L LB sp scr W M M'. intros P D C. exact (conj P (conj D C)). Qed.
Lemma stk_weaken : ltac2:(TCodec.tc2 tcn__L5Core "O'L'SLyR0%211'=y8%511%311p051&R3r5r4r3r2%544321'C&RHz%2215%3267%5221r7r6%>421=;p041p0;1pW<J1pW:K1pW@L1pRDE1pWDN1").
Proof. intros sptop M sp scr scr'.
intros (A & B & C & D & W) Hs. repeat split; try lia.
eapply L5.defined_sub. exact W. lia. lia.
Qed.
Lemma stk_grows : ltac2:(TCodec.tc2 tcn__L5Core "K'L'SLyR0%211'=y8%511%311p051&REr4r3%3221&R3r6r5r2%443261r7%641498p031p091pW:F1pW@G1pRF@1pRDA1pWDJ1").
Proof. intros sptop M M' sp scr. intros G (A & B & C & D & W). repeat split; try lia. eapply L5.defined_grows; eauto. Qed.
Lemma writable_of_defined : ltac2:(TCodec.tc2 tcn__L5Core "Q4'SLyR0%211'=y8%511%311p051'L&R7r3r2r1%43321&RHz%2216&RGr4%2219&RM+2+R0%3221%:251&RCvSFr6r5%44321;p061p0?1p0C1pVJI1pV6J1pRDL1").
Proof. intros M a n.
intros D Ha Hn d k Hd Hk. destruct k as [|k]. reflexivity. apply store_ok_of_all.
- rewrite L5.unsigned_lit by lia. lia.
- intros x Hx. rewrite L5.unsigned_lit in Hx by lia. unfold wview.
assert (E : x = Z_to_bv 64 (a + (bv_unsigned x - a))) by (apply bv_eq; rewrite L5.unsigned_lit; [lia| pose proof (bv_unsigned_in_range _ x); cbn in *; lia]).
pose proof (D (bv_unsigned x - a) ltac:(lia)) as Dx. rewrite <- E in Dx.
destruct (M x); [discriminate | exfalso; apply Dx; reflexivity].
Qed.
Lemma stk_writable : ltac2:(TCodec.tc2 tcn__L5Core "I'L'SLyR0%211'=y8%511%311p051&R3r4r3r2r1%544321&RCvSF&RN%1276%443917p061pW:E1pW@F1pRD?1pWDH1").
Proof. intros sptop M sp scr. intros (A & B & C & D & W). apply writable_of_defined. exact W. lia. lia. Qed.
Definition agree_on (M M' : word -> option byte) (a n : Z) : Prop :=
forall i, a <= i < a + n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Lemma rdn_agree : ltac2:(TCodec.tc2 tcn__L5Core "QB'SLyR0%211'=y8%511%311p051';'L&RHzr1%3221&RGr2&RLr3%211%5241&RM+2+R0%3221%>251&QOr6r5r4%=11%5443=1'D':%11L%O11&RDvSF&SK%12Q5:%443=1<r7%64513>%;3831p0=1p0D1p0Q01pV6Q51pVJQ71pRFQ91pRDQ:1").
Proof. intros M M'.
induction n as [|n IH]; intros a Ha Hn Hag. reflexivity.
cbn [rdn]. rewrite (Hag a) by lia.
rewrite (add1_lit a).
rewrite (IH (a + 1)); [reflexivity | lia | lia | intros i Hi; apply Hag; lia].
Qed.
Lemma u64_at_agree : ltac2:(TCodec.tc2 tcn__L5Core "Q8'SLyR0%211'=y8%511%311p051'L&QOr4r3r2+8%544321&RHz%2216&RG%1296&RM+2+R0%3221%9251&RAvSFr7r5%44321Cr6%645413p031p091p0A1p0E1pX0L1pV6M1pRFO1pRDQ01").
Proof. intros M M' a v. intros Hag Ha H8 Hu. unfold L5.u64_at. rewrite (rdn_agree M M' 8%nat a Ha ltac:(cbn; lia)). exact Hu. intros i Hi; apply Hag; cbn in Hi; lia. Qed.
Lemma u8_at_agree : ltac2:(TCodec.tc2 tcn__L5Core "Q8'SLyR0%211'=y8%511%311p051'L&QOr4r3r2+1%544321&RHz%2216&RG%1296&RM+2+R0%3221%9251&RBvSFr7r5%44321Cr6%645413p031p091p0A1p0E1pV:L1pV6M1pRFO1pRDQ01").
Proof. intros M M' a b. intros Hag Ha H1 Hu. unfold L5.u8_at. rewrite (rdn_agree M M' 1%nat a Ha ltac:(cbn; lia)). exact Hu. intros i Hi; apply Hag; cbn in Hi; lia. Qed.
Lemma bytes_at_agree : ltac2:(TCodec.tc2 tcn__L5Core "Q@'SLyR0%211'=y8%511%311p051'L':%112&QOr4r3r2&RL&9r1%22:1%411%948761&RHz%221:&RG%92A<%;11%32?1&RM+2+R0%3221%;251&R6vSFr7r5%44321Ir6%645413p031p091p0C1p0G1pV<Q21pW0Q51pRFQ71pRDQ81").
Proof. intros M M' p bs. intros Hag Hp Hn HB i Hi. eapply u8_at_agree. intros j Hj; apply Hag; lia. lia. lia. apply HB. exact Hi. Qed.
Lemma limbs_at_agree : ltac2:(TCodec.tc2 tcn__L5Core "QD'SLyR0%211'=y8%511%311p051'L':%112&QOr4r3r2&RK+8&RL&9r1%22<1%411%7261%<4;:91&RHz%221=&RG%:2D?%<11%?2>1%42C1&RM+2+R0%3221%<251&R=vSFr7r5%44321Mr6%645413p031p091p0D1p0H1pX2Q61pW2Q91pRFQ;1pRDQ<1").
Proof. intros M M' q ws. intros Hag Hq Hn HL i Hi. eapply u64_at_agree. intros j Hj; apply Hag; lia. lia. lia. apply HL. exact Hi. Qed.
Lemma defined_agree : ltac2:(TCodec.tc2 tcn__L5Core "I'SLyR0%211'=y8%511%311p051'L&QOr4r3r2r1%544321&R7r5%23165%33287p021p061pVJ=1pV6>1pRF@1pRDA1").
Proof. intros M M' a n. intros Hag D i Hi. rewrite (Hag (a + i)) by lia. apply D. exact Hi. Qed.
Lemma wview_agree : ltac2:(TCodec.tc2 tcn__L5Core "I'SLyR0%211'=y8%511%311p051'Dr2r1%211r3%113%63831&Q2vSF%23158r4%4331:%<3>31p071pX8D1pRF@1pRDA1").
Proof. intros M M' x. intros E. unfold wview. rewrite E. reflexivity. Qed.
Lemma store_ok_agree : ltac2:(TCodec.tc2 tcn__L5Core "Q@'SLyR0%211'=y8%511%311p051';'L&RHzr1%3221&RGr2&RLr3%211%5241&RM+2+R0%3221%>251&QOr6r5r4%=11%5443=1'D'6&Q1vSF&SK%12Q38%443;1:r7%64513<%93831p0;1p0B1p0N1pV6Q31pVBQ51pRFQ71pRDQ81").
Proof. intros M M'.
induction k as [|k IH]; intros a Ha Hk Hag. reflexivity.
cbn [store_ok]. rewrite (wview_agree M M') by (apply Hag; lia).
rewrite (add1_lit a).
rewrite (IH (a + 1)); [reflexivity | lia | lia | intros i Hi; apply Hag; lia].
Qed.
Lemma writable_agree : ltac2:(TCodec.tc2 tcn__L5Core "Q8'SLyR0%211'=y8%511%311p051'L&QOr4r3r2r1%544321&RHz%2216&RG%1298&RM+2+R0%3221%9251&RCvSFr7r5%44321Cr6%645413p031p091p0A1p0E1pVJL1pV6M1pRFO1pRDQ01").
Proof. intros M M' a n.
intros Hag Ha Hn W d k Hd Hk. rewrite (store_ok_agree M M' k (a + d)); [apply W; lia | lia | lia |].
intros i Hi. apply Hag. lia.
Qed.
Lemma store_ok_S : ltac2:(TCodec.tc2 tcn__L5Core "Q;'SLyR0%211'=y8%511%311p051';&E'D'6&Q1vSFr3r2(3r1%211%746541(A%;3:21'C&F&Q2%13<;:(2%11F%B3F31%611&SM(SJ+1(B%33Q121%53Q2D1%H4GF1C%K3J1A%@291%N2B1pVBQ01pV6Q71pRDQ31").
Proof. intros M a k.
cbn [store_ok]. destruct (wview segs M a) as [b|].
- split. intros H; split; [discriminate | exact H]. intros [_ H]; exact H.
- split. intros H; discriminate. intros [H _]; exfalso; apply H; reflexivity.
Qed.
Lemma writable_app : ltac2:(TCodec.tc2 tcn__L5Core "Q<'SLyR0%211'=y8%511%311p051'L&RHzr3%3221&RGr6r5%3221r4%5221&RM+2+R0%3221%>251&RCvSFr8r7%44321>r9%A243%74621Ar:%948143p031p071p0=1p0I1p0J1p0K1pVDQ01pVJQ11pV6Q21pRDQ41").
Proof. intros M a n m.
intros Ha Hn Hm Htop W1 W2 d k. revert d. induction k as [|k IH]; intros d Hd Hk. reflexivity.
rewrite Nat2Z.inj_succ in Hk.
destruct (Z_lt_le_dec d n) as [Hlt|Hge].
-
apply (proj2 (store_ok_S M (Z_to_bv 64 (a + d)) k)). split.
+ pose proof (W1 d 1%nat Hd ltac:(cbn; lia)) as W. apply (proj1 (store_ok_S M _ 0%nat)) in W. exact (proj1 W).
+ rewrite (add1_lit (a + d)). replace (a + d + 1) with (a + (d + 1)) by lia.
apply IH. lia. lia.
- replace (a + d) with (a + n + (d - n)) by lia. apply W2. lia. lia.
Qed.
Lemma agree_on_sub : ltac2:(TCodec.tc2 tcn__L5Core "Q1'SLyR0%211'=y8%511%311p051'L&QOr6r5r4r3%544321&RH%1253&RG%1265%2298%5221r9r8%>421<;p041p091p0<1pVLC1pV8D1pVJE1pV6F1pRFH1pRDI1").
Proof. intros M M' a n a' n'. intros H H1 H2 i Hi. apply H. lia. Qed.
Lemma big_at_agree : ltac2:(TCodec.tc2 tcn__L5Core "Q9'SLyR0%211'=y8%511%311p051'L'R5&QOr4r3r2+Q0%544321&RHz%2216&RG%1296&RM+2+R0%3221%9251&R4vSFr7r5%44321Cr6%645413p031p091p0A1p0E1pV:L1pVNN1pRFQ01pRDQ11").
Proof. intros M M' o b.
intros Hag Ho H32 (B0 & Bfb & B8 & BS).
split. { eapply u8_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact B0]. }
split. exact Bfb.
split. { eapply u64_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact B8]. }
destruct (L5.bo_st b) as [v0 v1|cap q].
- destruct BS as (T & B16 & B24 & R). split. exact T.
split. { eapply u64_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact B16]. }
split. { eapply u64_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact B24]. } exact R.
- destruct BS as (T & B16 & B24 & R). split. exact T.
split. { eapply u64_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact B16]. }
split. { eapply u64_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact B24]. } exact R.
Qed.
Lemma lstr_short_agree : ltac2:(TCodec.tc2 tcn__L5Core "Q:'SLyR0%211'=y8%511%311p051'L':%112&QOr4r3r2+H%544321&RHz%2216&RG%1296&RM+2+R0%3221%9251&R>vSFr7r5%44321Cr6%645413p031p091p0A1p0E1pW6L1pVNO1pRFQ11pRDQ21").
Proof. intros M M' o s.
intros Hag Ho H24 (L22 & B0 & BS & BN). split. exact L22.
split. { eapply u8_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact B0]. }
split. { eapply bytes_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact BS]. }
eapply u8_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact BN].
Qed.
Lemma frame_agree : ltac2:(TCodec.tc2 tcn__L5Core "QG'QC':'?'L%2211%411&R@%611'SLyR0%211'=y8%511%311p051&R1r9r8r7r6r5r4r3%877654321'C&RHr1%2261&RI&RG%1298%3251%8251&R2r<r;r:r2%56432FE1p071pV@Q61&QO%14GFEDp031p0E1pVJQ;1pV6Q<1pRFQ11pRDQ21pV2Q;1pW:Q@1pW@QA1pR2Q@1pR0QF1").
Proof. intros L LB sp scr W M M' a n. intros [HP _] HK i Hi. apply HP. apply HK. exact Hi. Qed.
Lemma kept_stack : ltac2:(TCodec.tc2 tcn__L5Core "QO'QC':'?'L%2211%411&R@%611&RH&RG&RN&QJr6%211&RM+2+G%3221%8251r3%;221r4%>221z%@213'C%B2>7&RI+R0%?2>1%32;1%6251&QGr9%211+4%K221+SoomohPPP0%N221+SoonPPPPP0r:%N11%Q2231&R?r7%221Q1&R2r<r;r8%4632:A16p061p0:1p0?1p0G1p0O1p0Q21pV6QF1pV2QC1pW:QH1pW@QI1pR2QH1pR0QN1").
Proof. intros L LB sp scr W a.
intros Hsp Hscr Ha He Hlo HW. split. lia. split.
{ right. left. lia. }
split. { unfold in_errno. lia. } exact HW.
Qed.
Lemma kept_stack_stk : ltac2:(TCodec.tc2 tcn__L5Core "R1'QC':'?'L%2211%411'SLyR0%211'=y8%511%311p051&R@%>11&R3&QJr7%211r5r4r3%744321&RHz%2215'Cr6%5217&RI&RM+2+R0%3221%52=1%9271&RG&QGr:%211+4%5221+SoomohPPP0%D221&R?%12BJ&R2r<r;r9r8%564321Q2Hp071p0:1p0C1p0N1p0Q21pV6QG1pV2Q<1pW:QI1pW@QJ1pRDQA1pR2QJ1pR0R01").
Proof. intros L LB M sp scr W a. intros (_ & B & _ & D & _) Hscr Ha He HW. apply kept_stack; try assumption; lia. Qed.
Lemma kept_below : ltac2:(TCodec.tc2 tcn__L5Core "R0'QC':'?'L%2211%411&R@%611'C&RH&RN&QJr6%211&RM+2+G%3221%8251r1%;221&RIr4r3%>221%4261%B261z%C216+Q?%@2?1%F2C1&RG&QGr9%211+4%5221+SoomohPPP0%N221+SoonPPPPP0r:%O11%Q2231&R?r7%221Q2&R2r<r;r8%4632:A16p061p0:1p0?1p0H1p0L1p0O1pV6QG1pV2QD1pW:QI1pW@QJ1pR2QI1pR0QO1").
Proof. intros L LB sp scr W a.
intros Ha Hscr Hsp He Hlo HW. split. lia. split.
{ right. left. lia. }
split. { unfold in_errno. lia. } exact HW.
Qed.
Lemma kept_block : ltac2:(TCodec.tc2 tcn__L5Core "R2'QC':'?'L%2211%411&R@%611&RF(>r3r2%349921r7%63:21'C&RHr4%2217&RI&RG%124;%32;1%8251zr5%:221r6%8213&RM+2+R0%3221%A251'G&QGr<%211%C2=1+4%D231%I21@%8241&R?r9%221B&R2r>r=r;r:%5643?21Q6p071p0;1p0E1p0M1p0Q11p0Q;1pV6QG1pVJQH1p2QI1pV2QF1pW:QK1pW@QL1pR2QK1pR0R11").
Proof. intros L LB sp scr W A n a.
intros Hin Ha HA HAn He HW. split. lia. split.
{ left. exists (A, n). split. exact Hin. cbn. lia. }
split. { unfold in_errno. lia. } exact HW.
Qed.
Lemma kept_static : ltac2:(TCodec.tc2 tcn__L5Core "R2'QC':'?'L%2211%411&R@%611'C&RH&QIr6%211r1%5221&RI&QH%116%3251%;251&F&QFr7r2%3221%511zr8%B11%D231r9%?11&RM+2+R0%3221%K251'Gr5&QGr:%211%K241&RG+4%2241%Q5218%:251&R?%12KQ6&R2r<r;%3621=GJOp051p081p0D1p0L1p0Q11p0Q81pV6QI1pV2QF1pW:QK1pW@QL1pR2QK1pR0R11").
Proof. intros L LB sp scr W a.
intros Ha Hs Hlo Hhi He HW. split. lia. split. { right. right. split. exact Ha. exact Hs. }
split. { unfold in_errno. lia. } exact HW.
Qed.
Lemma kept_inner : ltac2:(TCodec.tc2 tcn__L5Core "Q;'QC':'?'L%2211%411&R@%611&R2r9r8r7r6r5r1%76654321&RH&RN%1287r4%3271%5231%62:=&R?%12>5%22=<p021r=r<%E621CBA@p041p091p0;1p0B1pV6O1pV4L1pW<Q11pWBQ21pV2O1pW:Q41pW@Q51pR2Q41pR0Q:1").
Proof. intros L LB sp scr W sp' scr' W' a.
intros (Ha & CA & NE & OW) H1 H2 HW. split. exact Ha. split.
- destruct CA as [IB|[[S1 S2]|IM]]. left; exact IB. right; left; split; [exact S1|lia]. right; right; exact IM.
- split. exact NE. apply HW. exact OW.
Qed.
Lemma kept_not_fresh : ltac2:(TCodec.tc2 tcn__L5Core "R;'QC':'?'L%2211%411&R@%611&R2r8r7r6r5r4r3%76654321&Q>r2%23419'G&RH&RG%1298&QIr:%211%6241&QH%114%921@%;241%:2CB&RN&QJr;%211+XPPP0%5221%B271&RFr1r<%33Q621&8%13Q9Q9K&@%13Q;Q;M%J231r>%@11%B21>%O241p0:1pV:QA1&F'C%Q42Q>Q?&RI%Q52Q@Q?%22QB1%5241%711p091p0I1p0Q21p0Q?1p0QC1pVJR01p2R11pV6R21pV2QO1pW:R41pW@R51pR2R41pR0R:1").
Proof. intros L LB sp scr W a A n.
intros (Ha & CA & NE & OW) BA Hlo Hhi HLB Hin.
destruct CA as [(b & Hb & Hr)|[[S1 S2]|[IM _]]].
- pose proof (BA b Hb). pose proof (HLB b Hb). lia.
- lia.
- lia.
Qed.
Lemma defined_app : ltac2:(TCodec.tc2 tcn__L5Core "Q0'SLyR0%211'=y8%511%311p051'L&R7r4r3r2%43321r5&RG%1265%83315&RHz%221:r7r6%829=%?3321p051p091p0>1pVDD1pVJE1pV6F1pRDH1").
Proof. intros M a n m.
intros D1 D2 Hn i Hi. destruct (Z_lt_le_dec i n) as [Hlt|Hge]. apply D1. lia.
replace (a + i) with (a + n + (i - n)) by lia. apply D2. lia.
Qed.
Lemma outside_nil : ltac2:(TCodec.tc2 tcn__L5Core "8'L&R?(<&R@%211r1%5221pV671").
Proof. intros a. intros r Hr. destruct Hr. Qed.
Lemma outside_cons : ltac2:(TCodec.tc2 tcn__L5Core "G&R@':%112'L&F&R<r3r1%3221%511&R?r2%2261(7r5r4%33@21%721;p061p0:1pV6A1pV2C1pW4F1").
Proof. intros r W a. intros H1 H2 r' [<-|Hr']. exact H1. apply H2. exact Hr'. Qed.
Lemma outside_cons_inv : ltac2:(TCodec.tc2 tcn__L5Core "G&R@':%112'L&R?(7r3r2%33821r1%6221'C&F&R<r4%2218%411%=2;:%7221p091pV6A1pV2C1pW4F1").
Proof. intros r W a. intros H. split. apply H. left; reflexivity. intros r' Hr'. apply H. right. exact Hr'. Qed.
Lemma agree_on_trans : ltac2:(TCodec.tc2 tcn__L5Core "J'SLyR0%211'=y8%511%311p051'L&QOr5r4r2r1%544321r3%746514r7%941873p031p061pVJ=1pV6>1pRL@1pRJA1pRHB1").
Proof. intros M1 M2 M3 a n. intros A B i Hi. rewrite (B i Hi). apply A. exact Hi. Qed.
Lemma agree_on_refl : ltac2:(TCodec.tc2 tcn__L5Core "A'SLyR0%211'=y8%511%311p051'L&QOr3r2r1%443321pVJ61pV671pRD91").
Proof. intros M a n. intros i Hi. reflexivity. Qed.
Lemma agree_of_frame_but : ltac2:(TCodec.tc2 tcn__L5Core "QF':&R@%211'SLyR0%211'=y8%511%311p051'L&R8r5r4r3%43321&RHz%2214&RG%1276&RM+2+R0%3221%9251'Cr6r1%=221&RI%<24C%2241%7241&R?r:r2%3221p051pV@M1&QOr8r7%3421@Op051p0D1p0L1p0Q01pVJQ61pV6Q71pRFQ91pRDQ:1pQLQC1").
Proof. intros F M M' a n. intros HF Ha Hn Ho i Hi. apply HF. rewrite L5.unsigned_lit by lia. apply Ho. exact Hi. Qed.
Definition obj_limbs (M : word -> option byte) (b : L5.bigobj) (ws : list Z) : Prop :=
length ws = L5.bo_len b /\ Forall (fun w => 0 <= w < 2 ^ 64) ws /\
match L5.bo_st b with
| L5.BInl v0 v1 => ws = firstn (L5.bo_len b) [v0; v1]
| L5.BDyn cap q => L5.limbs_at segs M q ws
end.
Lemma limbs_at_app : ltac2:(TCodec.tc2 tcn__L5Core "Q6'SLyR0%211'=y8%511%311p051'L':%112&R=vSFr4r3r2%544321r5&RG&RK+8&RL&9%12?9%311%6251%82=1%@4?:1<r6&5%13FA@%D4C3>1p051p0A1pX6H1pX4I1pW2L1pRDN1").
Proof. intros M q ws1 ws2.
intros H1 H2 i Hi. rewrite length_app in Hi.
destruct (Nat.lt_ge_cases i (length ws1)) as [Hl|Hg].
- rewrite app_nth1 by lia. apply H1. exact Hl.
- rewrite app_nth2 by lia. replace (q + 8 * Z.of_nat i) with (q + 8 * Z.of_nat (length ws1) + 8 * Z.of_nat (i - length ws1)) by lia.
apply H2. lia.
Qed.
Lemma limbs_at_zeros : ltac2:(TCodec.tc2 tcn__L5Core "Q6'SLyR0%211'=y8%511%311p051'L';&Hr1r2%3221&RAvSFr5&RGr4&RK+8&RL%11:%4231%7261z%<4;:21p0>1pV@C1&R=r3&K%13H7D%44B?31p061pVBJ1pW2L1pRDN1").
Proof. intros M q k. intros H i Hi. rewrite repeat_length in Hi. rewrite nth_repeat. apply H. exact Hi. Qed.
Lemma limbs_at_firstn : ltac2:(TCodec.tc2 tcn__L5Core "K'SLyR0%211'=y8%511%311p051'L':%112';&R=vSFr4r3r2%544321r5&I%13<45%948371p051pVJ<1pX2>1pW2A1pRDC1").
Proof. intros M q ws n.
intros H i Hi. rewrite length_firstn in Hi. rewrite nth_firstn. destruct (Nat.ltb_spec i n); [|lia]. apply H. lia.
Qed.
Lemma limbs_at_nil : ltac2:(TCodec.tc2 tcn__L5Core "B'SLyR0%211'=y8%511%311p051'L&R=vSFr2r1(<%116%645431pW281pRD:1").
Proof. intros M q. intros i Hi. cbn in Hi. lia. Qed.
Lemma firstn_firstn_le {A} (l : list A) n m : (n <= m)%nat -> firstn n (firstn m l) = firstn n l.
Proof. intros H. rewrite firstn_firstn. f_equal. lia. Qed.
Definition fresh_block (L : heap_layout) (LB : list (Z * Z)) (M' : word -> option byte) (A n : Z) : Prop :=
block_range L A n /\ blocks_apart A n LB /\ L5.defined M' A n.
Lemma fresh_block_bounds : ltac2:(TCodec.tc2 tcn__L5Core "QL'QC':'?'L%2211%411'SLyR0%211'=y8%511%311p051&R0r5r4r3r2r1%6554321'C&RH+TP0%2217'G&RG%12:9&QIr6%211%9241&QH%114%<21A%:241'D&RJ+@%22F1z%53Q621&RI%123I&RN&QJ%11A+XPPP0%4221%K2F1%M271%N2:1%O2A1%Q02M1p0Q21pVJQD1p2QE1pRFQ<1pR2QE1pR0QK1").
Proof. intros L LB M' A n. intros [[H0 [H1 [H2 [H3 H4]]]] _]. repeat split; assumption. Qed.
Lemma fresh_block_hull : ltac2:(TCodec.tc2 tcn__L5Core "Q='QC':'?'L%2211%411'SLyR0%211'=y8%511%311p051&R0r5r4r3r2r1%6554321'D&QIr6%211&R;vSF%211%73I41&QHr7%211&R:%117%=3O31&R9%13:EDp031p0:1p0C1pVJQ51p2Q61pRFM1pR2Q61pR0Q<1").
Proof. intros L LB M' A n. intros [[H0 [H1 _]] _] Elo Ehi. unfold L5.hull_apart. rewrite <- Elo, <- Ehi. exact H1. Qed.
Lemma model_but_vm_refl : ltac2:(TCodec.tc2 tcn__L5Core "5'Q4&QNr1%2211pVD41").
Proof. intros m. destruct m as [fd [maps lazy mat] io fs pr li ti sc sg]. reflexivity. Qed.
Lemma model_but_vm_trans : ltac2:(TCodec.tc2 tcn__L5Core "<'Q4&QNr3r2%3221r5%5214p031p041pVH91pVF:1pVD;1").
Proof. intros m m' m''.
unfold model_but_vm. intros A B. set (X := m_vmmaps m'') in *. set (Y := m_vmmaps m') in *.
rewrite B. rewrite A. destruct m as [fd [maps lazy mat] io fs pr li ti sc sg]. reflexivity.
Qed.
Lemma halted_but_vm : ltac2:(TCodec.tc2 tcn__L5Core "C'Q4&QNr2r1%3221'D'='SLyR0%211%411&Q6%11:r3%311%:3531p0<1pVFA1pVDB1").
Proof. intros m m'. unfold model_but_vm. intros ->. reflexivity. Qed.
Lemma lazy_but_vm : ltac2:(TCodec.tc2 tcn__L5Core "E'Q4&QNr2r1%3221'D':'?'SLyR0%211%4211%611&Q7%11<r3%311%<3531p0>1pVFC1pVDD1").
Proof. intros m m'. unfold model_but_vm. intros ->. reflexivity. Qed.
Lemma materialized_but_vm : ltac2:(TCodec.tc2 tcn__L5Core "C'Q4&QNr2r1%3221'D':'SLyR0%211%411&Q8%11:r3%311%:3531p0<1pVFA1pVDB1").
Proof. intros m m'. unfold model_but_vm. intros ->. reflexivity. Qed.
Lemma hi_heap_client : ltac2:(TCodec.tc2 tcn__L5Core "S9'QC'Q3'QA':'?'L%2211%411&Q@'SLyR0%211'=y8%511%311p051pX862'Q5'QBr8r7r6%43321&QDr5r4r2%4576321&QEr;r1%3221'G'C&RH&QIr<%211%421<&RI&QH%115%32@1%:251&QJ%119%<21D%?241p0A1pV6Q=1%:1E+SoomohPPP0%B221+SoonPPPPP0%D219z%F21J&RM+2+R0%3221%F2O1%M261'Dr9&SK%12QIQ8%311r:%113%73QH31&RNr?%M11+XPPP0%4221%Q:21QB%Q62QC4%Q=221&QK%12Q<QF%QA231%QB2<1p0E1pV6R@1&RE%12FR3r=%R151QDQKHR5p031p061p0Q51p0Q81p0Q<1p0R31p0R91pV0R?1pRFRA1pRDRC1pV>RL1pR2RN1pQNS41pW8S61pR0S81").
Proof. intros L scfg HI LB cr M M' VM.
intros HIok HH Hro Hhi Hsp Hchg Hgr. eapply (hio_frame L scfg HI HIok). exact HH.
- intros a Ha Hpriv. destruct (Hchg a Ha) as [E|[S|B]]. exact E.
+ exfalso. destruct Hpriv as [(P1 & P2 & P3)|P]. lia. apply Hro in P. lia.
+ exfalso. destruct Hpriv as [(P1 & P2 & P3)|P]. exact (P2 B). apply Hro in P.
destruct B as (b & Hb & Hin). pose proof (proj1 (hio_wf L scfg HI HIok LB cr M VM HH) b Hb) as ((R0 & R1 & R2 & R3 & R4) & _).
lia.
- intros x Hx. apply Hgr. exact Hx.
Qed.
Lemma in_lb_remove_neq : ltac2:(TCodec.tc2 tcn__L5Core "M'L':'?%1233%311&RF(>r3r2%349921r1%63821&F'Dr4r5%33@21%511%<4BB34&QMr6%221>%A3C41p061p0=1pR2E1pVJJ1p4K1p2L1").
Proof. intros A B n LB.
induction LB as [|[c m] LB IH]; intros Hin Hne. destruct Hin.
cbn [lb_remove fst]. destruct (Z.eqb c A) eqn:E.
- apply Z.eqb_eq in E. subst c. destruct Hin as [H|H]. injection H; intros; subst; contradiction. exact H.
- destruct Hin as [H|H]. left; exact H. right. apply IH; assumption.
Qed.
Lemma in_lb_remove : ltac2:(TCodec.tc2 tcn__L5Core "A'L'?%1222':%112&RFr2&QMr3r1%3221%63951%73:46p021pR2:1pV:=1p2@1").
Proof. intros A b LB.
induction LB as [|[c m] LB IH]; intros Hin. destruct Hin.
cbn [lb_remove fst] in Hin. destruct (Z.eqb c A). right; exact Hin. destruct Hin as [H|H]. left; exact H. right; apply IH; exact H.
Qed.
Lemma blocks_apart_in : ltac2:(TCodec.tc2 tcn__L5Core "Q0'L':'?%1233%311&Q>r5r4r3%43321&RF(>r2%24==51%43;17'G&RH&RGr7r6%3221%521>%52?>%7215%9231p0;1p0A1pVDK1p4L1pR2I1pVJN1p2O1").
Proof. intros A n LB B m. intros H Hin. exact (H (B, m) Hin). Qed.
Lemma bytes_at_rdn : ltac2:(TCodec.tc2 tcn__L5Core "QG'SLyR0%211'=y8%511%311p051':'L%211&RHzr1%3221&RGr2&RL&9r3%22;1%411%7261&RM+2+R0%3221%@251&R6vSFr5r4%4432=1'D%J1M%Q011&RDr6&SK%12Q68%F2O:%54<421(4&J%62Q8OqX:Q41%34Q5Q91@%52=1%?3=71p0A1p0G1p0Q51pW0Q;1pV<Q;1pRDQ?1").
Proof. intros M.
induction bs as [|b bs IH]; intros p Hp Hn HB. reflexivity.
cbn [length] in Hn |- *. pose proof (HB 0%nat ltac:(cbn; lia)) as H0. cbn [nth] in H0. unfold L5.u8_at in H0. rewrite Z.add_0_r in H0.
cbn [rdn] in H0 |- *.
destruct (match M (Z_to_bv 64 p) with Some b0 => Some b0 | None => seg_rom segs (Z_to_bv 64 p) end) as [b0|]; [|discriminate].
injection H0 as E0. subst b0.
rewrite (add1_lit p).
rewrite (IH (p + 1)). reflexivity. lia. lia.
intros i Hi. replace (p + 1 + Z.of_nat i) with (p + Z.of_nat (S i)) by lia.
change (nth i bs 0) with (nth (S i) (b :: bs) 0). apply HB. cbn; lia.
Qed.
Lemma rdn_bytes_at : ltac2:(TCodec.tc2 tcn__L5Core "QF'SLyR0%211'=y8%511%311p051':%114'L&RHzr1%3221&RGr2&RL&9r3%22?1%411%7261&RM+2+R0%3221%@251'D%J1D&RDvSFr5&SK%12Q1?r4%B2O1%746531(4%12N4%<3;31&R6r6&J&SN%11Q9%34Q9Q41>%64@5<1p081p0F1p0Q41pW0Q91pV<Q;1pRDQ>1").
Proof. intros M.
induction bs as [|b bs IH]; intros p Hp Hn HR i Hi. cbn in Hi; lia.
cbn [length] in Hn, HR. cbn [rdn] in HR.
destruct (match M (Z_to_bv 64 p) with Some b0 => Some b0 | None => seg_rom segs (Z_to_bv 64 p) end) as [b0|] eqn:E0; [|discriminate].
rewrite (add1_lit p) in HR.
destruct (rdn segs M (Z_to_bv 64 (p + 1)) (length bs)) as [rest|] eqn:ER; [|discriminate].
injection HR as E1 E2. subst b0 rest.
destruct i as [|i].
- cbn [nth map]. unfold L5.u8_at. rewrite Z.add_0_r. cbn [rdn]. rewrite E0. f_equal. f_equal. symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.mod_small. reflexivity. pose proof (bv_unsigned_in_range _ b); cbn in *; lia.
- cbn [nth map]. replace (p + Z.of_nat (S i)) with (p + 1 + Z.of_nat i) by lia.
change (nth i (map bv_unsigned bs) 0) with (nth i (map bv_unsigned bs) 0).
apply (IH (p + 1)). lia. lia. exact ER. cbn [map length] in Hi. rewrite length_map in Hi |- *. lia.
Qed.
End WithSegs.
End L5C.
