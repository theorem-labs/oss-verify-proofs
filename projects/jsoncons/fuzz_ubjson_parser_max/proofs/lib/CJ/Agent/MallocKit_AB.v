(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_MallocKit_AB () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_AB.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_AB.CEIL_WRAP_4."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0A"; "0C"; "1Some"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"]; ["2iff"; "2not"; "3N"; "3Z"; "4AW"; "5amo_aligned"; "0P"; "6sxv"; "7asegs"; "8agree_on"; "8ivs_avoid"; "8ivs_covered"; "9mw_ok"; ":actives"; ":b8"; ":bouncess"]; [":meta_cells"; ":meta_slot"; ":meta_word"; ":pw"; ":unmap_seqs"; ":usages"; ":wz"; ";pres_except"; "<u64arr"; "<u8arr"; "<upd"; "=cell"; "=cells_size"; ">ivl"; ">munch"; ">outside"]; [">wmono"; "?bytes_at"; "?le1"; "?le4"; "@rw_cells"; "Aactive"; "Aaptr"; "Aaptr_eqb"; "Aarea"; "Abounces"; "Ac_unmap_seq"; "Aconc"; "Actx"; "Adel_slots"; "Aget_meta_rec"; "Am_freeable"]; ["Am_last_idx"; "Am_maplen"; "Am_sizeclass"; "Amctx"; "Ameta"; "Ameta0"; "Amstate"; "Aoconc"; "Aoptr"; "Aput_meta"; "As_areas"; "As_slots"; "Aset_active"; "Aset_slots"; "Aset_unmap_seq_map"; "Aset_usage"]; ["Aunmap_seq"; "Aupd_ctx"; "Aupd_meta"; "Ausage"; "BIn"; "Bnth_error"; "Cadd"; "Cland"; "Cldiff"; "Cle"; "Clor"; "Clt"; "Cmodulo"; "Cmul"; "Cof_nat"; "Copp"]; ["Cpow"; "Cshiftl"; "Cshiftr"; "Csub"; "Cto_nat"; "0W"; "0a"; "0b"; "0bs"; "0c"; "0cs"; "0f"; "0g"; "0hi"; "0i"; "0iv"]; ["0k"; "0lo"; "0m"; "0m'"; "0mr"; "0n"; "0p"; "0q"; "0r"; "0s"; "0sc"; "0st"; "0st'"; "Dinsert"; "EZ_to_bv"; "Ebv"]; ["Ebv_swrap"; "Ebv_unsigned"; "FN_countable"; "FZ_countable"; "Fprod_countable"; "Gprod_eq_dec"; "Hmap_insert"; "Igmap"; "Igmap_partial_alter"; "Jeq_dec"; "Keq_dec"; "0v"; "0ws"; "0x"; "0y"; "0z"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition ivs_avoid (W : list (Z * Z)) (P : Z -> Prop) : Prop :=
forall lo hi a, In (lo, hi) W -> lo <= a < hi -> ~ P a.
Lemma ivs_avoid_nil : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB ";'C!p021&J(9'<%1266%311r1%6221pQ>81").
Proof. intros P lo hi a []. Qed.
Lemma ivs_avoid_cons : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q5'C'7'<%1233%311!pXL61'>&RIr5r1%3221&RKr4%2241%8241&Ar3r2%211%411p061pV>F1&J%1276(4(;r6%24LL1C%43J1@%721=p071p0:1pQ>K1pV<N1pVLQ31pW4Q41").
Proof.
intros lo hi W P H1 H2 lo' hi' a [E|Hin] Ha.
- inversion E; subst. apply H1. exact Ha.
- eapply H2; eauto.
Qed.
Lemma avoid_outside : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "D'7'<'C%2211%411!p041&Jr3r2%3221%312&Q?r5%2216p041p061pXL?1pQ><1pV<?1").
Proof.
induction W as [|[lo hi] W IH]; intros P x HW HP; cbn; [exact I|]. split.
- intros Hx. exact (HW lo hi x ltac:(left; reflexivity) Hx HP).
- apply (IH P); [|exact HP]. intros lo' hi' a Hin Ha. apply (HW lo' hi'); [right; exact Hin|exact Ha].
Qed.
Definition agree_on (m m' : word -> option byte) (A n : Z) : Prop :=
forall a, A <= a < A + n -> m' (wa a) = m (wa a).
Lemma munch_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "QJ'7&Q=%211'SOyR0%211':y8%511%311p051'C!p021&Q>r6r5r4%43321&Jr7%2214'>&RIr1%2291&RK&RF%12<;%3251%8251r2%<11p031pV>G1z%=21D%:2FE&S0+2+R0%3221%C251&Ir:r9%3421JOp051p0<1p0?1p0M1p0Q11pW<Q91p2Q:1pQ>Q91pW8Q=1pW6Q>1pV<QG1").
Proof.
intros W m m' P A n MU HW HP HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
eapply avoid_outside; [exact HW| apply HP; exact Ha].
Qed.
Lemma bytes_at_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q0'SOyR0%211':y8%511%311p051'C'7%115&QA&Hr4r2r1%544321&Ir5r3&RN&6%12A8%311%746;51%>4=7<6p021p0;1pVBB1p2E1pW8G1pW6H1").
Proof.
intros m m' A bs (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|].
intros i Hi. unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.
Lemma rw_cells_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q5'SOyR0%211':y8%511%311p051'C'7'Q;%211&QD&Hr4r2r1%544321&Ir5r3&RN&Q<%118%311%746;51&Q@r6%23?19%A4@2:?p021p061p0?1pVFF1p2J1pW8L1pW6M1").
Proof.
intros m m' A cs [[Hwf HB] HW] AG WM. split; [split; [exact Hwf|]|].
- eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
- eapply wr_at_transport; eauto.
Qed.
Lemma u64arr_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q7'SOyR0%211':y8%511%311p051'C'7%118&Q8&Hr4r2r1%544321&Ir5r3&RM+8&RN&6%12F:%311%6251%:49>81&Q@r6%23B1<%D4C2=Bp021p061p0B1pXJI1p2L1pW8N1pW6O1").
Proof.
intros m m' A ws [HB HW] AG WM. split; [|eapply wr_at_transport; eauto].
eapply bytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
Qed.
Lemma u8arr_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q4'SOyR0%211':y8%511%311p051'C'7%115&Q9&Hr4r2r1%544321&Ir5r3&RN&6%12A8%311%746;51&Q@r6%23?19%A4@2:?p021p061p0?1pVBF1p2I1pW8K1pW6L1").
Proof. intros m m' A bs [HB HW] AG WM. split; [eapply bytes_at_agree; eauto| eapply wr_at_transport; eauto]. Qed.
Lemma get_meta_rec_put : forall st g mr g',
get_meta_rec (put_meta g mr st) g' = if aptr_eqb g' g then mr else get_meta_rec st g'.
Proof.
intros. unfold get_meta_rec at 1. unfold put_meta. cbn [s_metas set_metas].
unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.
Lemma upd_meta_put : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "C'R6&QF'R4p011'?&RBr2r1r3%43321&R9&QN%1246%611%43816%;3?61pVH=1pVJ@1pWHB1").
Proof. reflexivity. Qed.
Lemma del_slots_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "C&QF'C'R6'?&QMr4r3r2r1%544321&R=&R;%113%3215%;3<51pWH=1pVD?1pWD@1pW>B1").
Proof. reflexivity. Qed.
Lemma meta_slot_same_areas : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "O'R6&QF'?'T7&T5'B&T9'C&T:%544321&T4&T2&T3%36872651'QH%<4>621&R:r2%211r3%411%C3631&Q1r4%2217%3226p021p061pVJK1pWJM1pWHN1").
Proof. intros st st' g E (a & ar & k & Ha & Hk & Eg). exists a, ar, k. rewrite E. auto. Qed.
Lemma nth_error_map_seq : forall {X} (f : nat -> X) n s i,
(i < n)%nat -> nth_error (map f (seq s n)) i = Some (f (s + i)%nat).
Proof.
intros X f n. induction n as [|n IH]; intros s i Hi; [lia|].
cbn [seq map]. destruct i as [|i]; cbn [nth_error]; [f_equal; f_equal; lia|].
rewrite IH by lia. f_equal. f_equal. lia.
Qed.
Lemma actives_nth : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q3'R6'C'>&RIzr1%3221&RK+Q@%2241%8241'?':'SOyR0%211%411&RE&Mr3%211&S4r2%211%73941(2&Q3&QE%1296%32:1%52?1%D3?71p0F1pWFQ01pWHQ21").
Proof.
intros st sc H. unfold actives. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.
Lemma usages_nth : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q3'R6'C'>&RIzr1%3221&RK+Q@%2241%8241'?':'SOyR0%211%411&RE&Q5r3%211&S4r2%211%73941(2&Q6&RC%1296%311%52?1%D3?71p0F1pWFQ01pWHQ21").
Proof.
intros st sc H. unfold usages. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.
Lemma bouncess_nth : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q3'R6'C'>&RIzr1%3221&RK+Q0%2241%8241'?':'SOy8%211%411&RE&Or3%211&S4r2%211%73941(2&N&QI%1296%311%52?1%D3?71p0F1pVNQ01pWHQ21").
Proof.
intros st i H. unfold bouncess. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.
Lemma unmap_seqs_nth : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q3'R6'C'>&RIzr1%3221&RK+Q0%2241%8241'?':'SOy8%211%411&RE&Q4r3%211&S4r2%211%73941(2&N&R@%1296%311%52?1%D3?71p0F1pVNQ01pWHQ21").
Proof.
intros st i H. unfold unmap_seqs. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.
Lemma actives_length : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB ">'R6'?'8&6'SOyR0%211&Mr1%211%7241uQ@%;3:21pWH=1").
Proof. intros st. unfold actives; rewrite map_length, seq_length; reflexivity. Qed.
Lemma usages_length : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB ">'R6'?'8&6'SOyR0%211&Q5r1%211%7241uQ@%;3:21pWH=1").
Proof. intros st. unfold usages; rewrite map_length, seq_length; reflexivity. Qed.
Lemma bouncess_length : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB ">'R6'?'8&6'SOy8%211&Or1%211%7241uQ0%;3:21pWH=1").
Proof. intros st. unfold bouncess; rewrite map_length, seq_length; reflexivity. Qed.
Lemma unmap_seqs_length : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB ">'R6'?'8&6'SOy8%211&Q4r1%211%7241uQ0%;3:21pWH=1").
Proof. intros st. unfold unmap_seqs; rewrite map_length, seq_length; reflexivity. Qed.
Lemma bytes_at_cons : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q4'SOyR0%211':y8%511%311p051'C'7%115&@&QA&Hr4r3(4r2r1%33>21%847651'>(9%11B%83C71%=4<;:1&RF+1%22=1%A4@?1;%9251%D2;1pVBF1pV@L1pV>J1pW6L1").
Proof.
intros. change (b :: bs) with ([b] ++ bs). rewrite (bytes_at_app asegs m a [b] bs). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat]. tauto.
Qed.
Lemma put_meta_put_meta_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "A'R6&QF'R4'?&R9r3r2r1r4%53421%63541%73653%93<21pV@;1pV><1pVJ>1pWH@1").
Proof. intros. destruct st; unfold put_meta, set_metas; cbn. f_equal. apply insert_insert_eq. Qed.
Lemma aptr_eqb_neq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "@&QF&A'?r2r1%33521%511'3&QGr3%2217(5%:3521p071pV@>1pV>?1").
Proof.
intros [a1 a2] [b1 b2] H. unfold aptr_eqb. cbn.
destruct (N.eqb_spec a1 b1); destruct (Z.eqb_spec a2 b2); cbn; try reflexivity. exfalso. apply H. congruence.
Qed.
Lemma aptr_eqb_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB ">&QF&@'?'3&QGr2r1%3221(=%73621%83:54%:221pV@<1pV>=1").
Proof.
intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.
Lemma get_meta_rec_put_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "?'R6&QF'R4'?&QN&R9r2r1r3%43321%6214%83914pW::1pVJ<1pWH>1").
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
Lemma get_meta_rec_put_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "G'R6&QF'R4&A'?r1r3%33621%511&QN&R9r4r5%33271r2%6221%7242%=3?21p0:1pW@B1pW:B1pVJD1pWHF1").
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_neq by assumption. reflexivity. Qed.
Lemma pw_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "F'R6&QF'R4&R8'?'SOyR0%211&Q3&R9r3r2r4%43321r1%7221%8242%=3:21pW>?1pW:A1pVJC1pWHE1"). Proof. reflexivity. Qed.
Lemma conc_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "C'R6&QF'R4'?'C&QK&R9r3r2r4%43321r1%7221%8242%;3:21pW>>1pW:>1pVJ@1pWHB1"). Proof. reflexivity. Qed.
Lemma ctx_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "A'R6&QF'R4'?'R3&QL&R9r2r1r3%43321%611%713%:3921pW:<1pVJ>1pWH@1"). Proof. reflexivity. Qed.
Lemma meta_slot_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "B'R6&QF'R4&Q1r4r1%3221&R9r3r5%33621r2%9221p071pW@=1pW:=1pVJ?1pWHA1").
Proof. intros. eapply meta_slot_same_areas; [|eassumption]. reflexivity. Qed.
Lemma meta_cells_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "E'R6&QF'R4'?'7'Q;%211&Q0&R9r3r2r4%43321r1%7221%8242%=3:21pWB?1pW:@1pVJB1pWHD1"). Proof. reflexivity. Qed.
Lemma outside_of_cover : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q6'C!p021'7'<%1255%311&RD(;r2r1%34;;21r4%63821'>&RI%1246&RKr3%2291%6241r8%11=p031pXLH1p0<1pVLJ1pW4K1&A%A1D%211&Q?%12D>p031p071pV>Q31pV<N1p4Q31").
Proof.
induction W as [|[lo hi] W IH]; intros a HW HC; cbn; [exact I|]. split.
- intros Ha. apply HC. apply (HW lo hi); [left; reflexivity| exact Ha].
- apply IH; [|exact HC]. intros lo' hi' Hin x Hx. apply (HW lo' hi'); [right; exact Hin|exact Hx].
Qed.
Lemma pres_except_of_munch' : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "QE'C!pXL21'7&Q=%211'SOyR0%211':y8%511%311p051&Q>r3r2r1%43321&Q@&H%23165&RD'<%12HH(;%14JJ:9r7%63421'>&RIr4%221?&RK%12AC%6231r;%11Ep031pXLQ71p0<1pVLQ91pW4Q:1&Q7r5%23B1>p041p0J1p0N1pW8Q41pW6Q51pV<Q>1p4QB1").
Proof.
intros C W m m' MU WM HW. eapply pres_except_of_munch; [exact MU | exact WM |].
intros a _ HC. eapply outside_of_cover; eauto.
Qed.
Fixpoint ivs_covered (C : Z -> Prop) (W : list (Z * Z)) : Prop :=
match W with
| [] => True
| (lo, hi) :: W' => (forall x, lo <= x < hi -> C x) /\ ivs_covered C W'
end.
Lemma ivs_covered_In : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q1'C!p021'7'<%1255%311&Kr2r1%3221&RD(;%14==54r4%43:21'>&RI%1249&RKr3%22<1%6241r8%11@p031pXLJ1p0<1pVLL1pW4M1p0D1pV<I1p4N1").
Proof.
induction W as [|[lo hi] W IH]; cbn; intros H lo' hi' Hin x Hx; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [E|Hin]; [inversion E; subst; auto| eapply IH; eauto].
Qed.
Lemma pres_except_of_munch_cov : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q5'C!p021'7&Q=%211'SOyR0%211':y8%511%311p051&Q>r3r2r1%43321&Q@&H%23165&Kr6r5%3221&Q7r7r4%33251p051p0:1p0>1pW8D1pW6E1pV<N1p4Q21").
Proof. intros. eapply pres_except_of_munch'; eauto. apply ivs_covered_In. assumption. Qed.
Lemma munch_grow2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "N&Q='7%112'SOyR0%211':y8%511%311p051&Q>(4r5r3%33?21r2r1%73321r6r4%93E81%:3F31%<3197p061pW8?1pW6@1pV<I1pW0L1pVHM1").
Proof.
intros [flo fhi] [lo hi] W m m' MU. eapply munch_weaken; [|exact MU].
intros x Hx. cbn in Hx |- *. tauto.
Qed.
End CEIL_WRAP_1.
Ltac munch_grow MU iv :=
lazymatch type of MU with
| munch (?f :: ?W) ?a ?b => apply (munch_grow2 f iv W a b) in MU
end.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Lemma amo_aligned_intro : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q0'C'>&RIzr1%3221&RK&S0+2+R0%3221%5271%;271'?&RLr2+4%3221%53B1?'3&E(D&SNyR0r3%3221%6251(=%?3921p0;1p0B1pV>O1").
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
End CEIL_WRAP_2.
Ltac amo_align AMO :=
try (rewrite AMO; cbv beta iota delta [negb]);
try (rewrite Z.eqb_refl; cbv iota).
Ltac amo_step AMO :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_cbv; simp_regs; amo_align AMO; exec_cbv; amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end end
end.
Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).
Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; fix_lit_store; try nrm.
Ltac showpc := match goal with |- evt _ _ (MS ?R _ ?pc _ ?rv _ _) => idtac "=== PC" pc "RV" rv end.
Section CEIL_WRAP_3.
Context {RUNp : RunP}.
Lemma usage_set_usage st sc v i : usage (set_usage sc v st) i = if Z.eqb i sc then v else usage st i.
Proof.
unfold usage, set_usage, upd_ctx. cbn [ctx s_ctx c_usage set_usage_map].
destruct (Z.eqb_spec i sc); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma usages_set_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q3'R6'C'>&RIzr2%3221&RK+Q@%2241%8241'?'7'SOyR0%211%411&Q5&R?r3r4%332@1%511&Q:%714&S4%117&Q6%11G%64>531%C3>81p0E1pXHO1pWFQ01pWHQ21").
Proof. intros st sc v.
intros Hsc. unfold usages.
replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
apply (map_seq_upd (fun i => wz (usage st (Z.of_nat i))) (fun i => wz (usage (set_usage sc v st) (Z.of_nat i)))); [|lia].
intros i Hi. rewrite usage_set_usage.
destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.
Lemma unmap_seq_set st i v j :
unmap_seq (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) j = if Z.eqb j i then v else unmap_seq st j.
Proof.
unfold unmap_seq, upd_ctx. cbn [ctx s_ctx c_unmap_seq set_unmap_seq_map].
destruct (Z.eqb_spec j i); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma unmap_seqs_set : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "QD'R6'C'>&RIzr2%3221&RK+Q0%2241%8241'?'7'SOy8%211%411&Q4&RA'R3&R>&SM'T7&T:&T3%34H21H&T6&T8%14K54K%34LL41r4r3&QJr1%211%>7Q2Q2:6541%@213qVDB1%D218%F11&Q:%H1;&S4%11<&N%11Q8%64O531%Q43O81p0Q61pXHQ@1pVNQA1pWHQC1").
Proof. intros st i v.
intros Hi. unfold unmap_seqs.
replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
apply (map_seq_upd (fun j => b8 (unmap_seq st (Z.of_nat j)))); [|lia].
intros j Hj. rewrite unmap_seq_set.
destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.
Lemma step_seq_eq st :
step_seq st = if c_seq (ctx st) =? 255
then upd_ctx (set_seq 1) (upd_ctx (fun c => set_unmap_seq_map ∅ c) st)
else upd_ctx (set_seq (c_seq (ctx st) + 1)) st.
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.
Lemma record_seq_eq sc st :
record_seq sc st = if sc_in_seq_range sc
then upd_ctx (fun c => set_unmap_seq_map (<[sc - 7 := c_seq c]> (c_unmap_seq c)) c) st
else st.
Proof. reflexivity. Qed.
Lemma le1_lit : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "O'C'>&RIzr1%3221&RK+X0%2241%8241'?'7'SOy8%211%411&QB&SNyR0r2%3221%511(4&N%115(9%11<%53=31%B3=71p0D1pY0N1").
Proof. intros z.
intros Hz. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.
Lemma conc_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "B'R6'R3p011&QF'?'C&QK&RAr2r3%3221r1%6221%7242%:3921pW@<1pVH>1pWHA1"). Proof. intros st f q. reflexivity. Qed.
Lemma rec_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "B'R6'R3p011&QF'?'R4&QN&RAr2r3%3221r1%6221%7242%:3921pW@<1pVH>1pWHA1"). Proof. intros st f q. reflexivity. Qed.
Lemma pw_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "D'R6'R3p011&R8'?'SOyR0%211&Q3&RAr2r3%3221r1%6221%7242%<3921pW@>1pVH@1pWHC1"). Proof. intros st f q. destruct q; reflexivity. Qed.
Lemma oconc_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "B'R6'R3p011&R8'?'C&R7&RAr2r3%3221r1%6221%7242%:3921pW@<1pVH>1pWHA1"). Proof. intros st f q. destruct q; reflexivity. Qed.
Lemma conc_set_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "B'R6'C&QF'?&QK&R?r3r2r4%43321r1%7221%8242%:3<21pW@<1pXH>1pWF?1pWHA1"). Proof. intros st sc v q. reflexivity. Qed.
Lemma rec_set_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "C'R6'C&QF'?'R4&QN&R?r3r2r4%43321r1%7221%8242%;3:21pW@=1pXH?1pWF@1pWHB1"). Proof. intros st sc v q. reflexivity. Qed.
Lemma oconc_set_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "B'R6'C&R8'?&R7&R?r3r2r4%43321r1%7221%8242%:3<21pW@<1pXH>1pWF?1pWHA1"). Proof. intros st sc v q. destruct q; reflexivity. Qed.
Lemma conc_set_active : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "C'R6'C&R8&QF'?&QK&R<r3r2r4%43321r1%7221%8242%:3=21pW@<1pXH>1pWF@1pWHB1"). Proof. intros st sc v q. reflexivity. Qed.
Lemma rec_set_active : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "D'R6'C&R8&QF'?'R4&QN&R<r3r2r4%43321r1%7221%8242%;3:21pW@=1pXH?1pWFA1pWHC1"). Proof. intros st sc v q. reflexivity. Qed.
Lemma oconc_set_active : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "B'R6'C&R8'?&R7&R<r3r2r4%43321r1%7221%8242%:3<21pW@<1pXH=1pWF?1pWHA1"). Proof. intros st sc v q. destruct q; reflexivity. Qed.
Lemma meta_slot_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "A'R6'R3p011&QF&Q1r3r1%3221&RAr4%2251r2%8221p061pW@;1pVH=1pWH@1"). Proof. intros st f q. intros H; exact H. Qed.
Lemma meta_slot_set_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "B'R6'C&QF&Q1r4r1%3221&R?r3r5%33621r2%9221p071pW@<1pXH>1pWF?1pWHA1"). Proof. intros st sc v q. intros H; exact H. Qed.
Lemma meta_slot_set_active : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "C'R6'C&R8&QF&Q1r4r1%3221&R<r3r5%33621r2%9221p071pW@<1pXH>1pWF@1pWHB1"). Proof. intros st sc v q. intros H; exact H. Qed.
End CEIL_WRAP_3.
Ltac ctx_norm H := rewrite ?conc_set_usage, ?rec_set_usage, ?oconc_set_usage, ?conc_set_active, ?rec_set_active, ?oconc_set_active,
?conc_upd_ctx, ?rec_upd_ctx, ?oconc_upd_ctx in H.
Section CEIL_WRAP_4.
Context {RUNp : RunP}.
Definition mw_ok (mr : meta) : Prop :=
0 <= m_last_idx mr <= 31 /\ 0 <= m_freeable mr <= 1 /\ 0 <= m_sizeclass mr <= 63 /\ 0 <= m_maplen mr < 2^52.
Lemma meta_word_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "D'R4&Lr1%211'>&RIz&Q2r2%211%5241&RK&S0+2+R0%3221%5271%=271p0?1pW:C1").
Proof. intros mr. intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.
Lemma meta_word_last_idx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "A'R4&Lr1%211'?'C&RG&Q2r2%211+O%5221&R0%115%:3931p0<1pW:@1").
Proof. intros mr.
intros (LI & FB & SCR & ML).
change 31 with (Z.ones 5). rewrite Z.land_ones by lia. unfold meta_word. change (2^5) with 32.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_sc : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "D'R4&Lr1%211'?'C&RG&S2&Q2r2%211+6%5221+QO%8221&R2%117%=3<31p0?1pW:C1").
Proof. intros mr.
intros (LI & FB & SCR & ML).
change 63 with (Z.ones 6). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^6) with 64.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia.
replace (0 + (m_sizeclass mr + 64 * m_maplen mr)) with (m_sizeclass mr + m_maplen mr * 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_shr6_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "G'R4&Lr1%211'>&RIz&S2&Q2r2%211+6%5221%8271&RK&S0+2+R0%3221%5271%@271p0B1pW:F1").
Proof. intros mr. intros H. pose proof (meta_word_range mr H). destruct H as (LI & FB & SCR & ML). rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma meta_word_freeable : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "C'R4&Lr1%211'?'C&RG&Q2r2%211+Q0%5221&RM&QO%116%3251%<3;51p0>1pW:B1").
Proof. intros mr.
intros (LI & FB & SCR & ML).
assert (E : 32 = Z.ldiff (Z.ones 6) (Z.ones 5)) by reflexivity. rewrite E at 1. rewrite land_ldiff_distr.
rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^6) with 64. change (2^5) with 32. unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
rewrite Z.mod_add, Z.mod_small by lia.
replace (m_last_idx mr + 32 * m_freeable mr) with (m_last_idx mr + m_freeable mr * 32) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed.
Lemma meta_word_maplen : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "A'R4&Lr1%211'?'C&S2&Q2r2%211+<%5221&R1%115%:3931p0<1pW:@1").
Proof. intros mr.
intros (LI & FB & SCR & ML).
rewrite Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^12) with 4096.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma meta_word_lt4096 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "D'R4&Lr1%211&@&RK&Q2r2%211+TP0%5221'?'C&R1%117z%53421%=271p0?1pW:C1").
Proof. intros mr. intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.
Section SE.
Local Abbreviation SEC_T_negw_word := (ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "J'C'?'SOyR0%211&SN&T0yQ0&S3z&T1&Q6&Gr1%211%411%62=1%9281%<2;1%>2@1&RO%118%:11%<11%G3D51pXNI1")) (only parsing).
Variable y : ltac:(sec_ty2 constr:(SEC_T_negw_word) 0%nat 0%nat).
Lemma negw_word : ltac:(sec_stmt2 constr:(SEC_T_negw_word) 1%nat 0%nat).
Proof.
rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
rewrite !swrap32_eq'. mlia.
Qed.
End SE.
Lemma land_neg_pow2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "I'C&RIzr2%3221'?&RGr4&RO&S0+2r3%3221%511%8271&RH&S3+1%2261%42<1%?3D61p0A1p0B1pW2G1pVHH1").
Proof. intros f k.
intros Hf Hk. replace (- 2 ^ k) with (Z.lnot (2 ^ k - 1)) by (unfold Z.lnot; lia).
rewrite <- Z.ldiff_land. reflexivity.
Qed.
Lemma ldiff_le : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB ">'C&RIzr2%3221&RHr4r3%3221%8213p061p071pV><1pVH=1").
Proof. intros f a.
intros Hf Ha.
assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.
Lemma land_upper : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "A'C&RIzr2%3221'>&RGr4r3%3221%9281%:224%7221p091p0:1pV>?1pVH@1").
Proof. intros f a.
intros Hf Ha. split; [apply Z.land_nonneg; lia|].
assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.
Lemma le4_sxv : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q1'C'>&RIzr1%3221&RK&S0+2+Q0%3221%5271%;271'?'7'SOy8%211%411&QC&SNyR0&Gr2%211%5241%711&Q6%115%:11%A3<41p0C1pXHQ01").
Proof. intros v.
intros Hv. apply le4_congr. pose proof (sxv_range v). rewrite unsigned_lit by lia. rewrite wz_unsigned by lia.
rewrite sxv_mod32. reflexivity.
Qed.
Lemma sllw1_word : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "Q3'C'>&RIzr1%3221&RK+Q0%2241%8241'?'SOyR0%211&SN&T0yQ0&S1+1&RLr2%221>%5241%8271%:2<1&Q6&G&S0+2%2219%411%611%F3C81p0H1pVNQ21").
Proof. intros i.
intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.
Lemma lor_sxv_zero : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "N'C'>&RIzr2%3221&RK&S0+2+Q0%3221%5271%;271&@'?&RJ&Gr4%211r3%411%6231%83F1C%8264%:3H1E%<231p0>1p0?1pV>L1pVHM1").
Proof. intros f a.
intros Hf Ha. pose proof (sxv_range f). pose proof (sxv_range a).
rewrite !Z.lor_eq_0_iff. rewrite !sxv_zero by lia. tauto.
Qed.
End CEIL_WRAP_4.
Ltac unmask64 K :=
try (change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia; rewrite !Z.mod_small in K by lia).
Section CEIL_WRAP_5.
Context {RUNp : RunP}.
Lemma meta_word_meta0 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_AB "7'?'C&Q2&R5%211z%63521"). Proof. reflexivity. Qed.
End CEIL_WRAP_5.
Ltac meta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl asegs mX) as WMq end.
