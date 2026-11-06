(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA ArtMem JatLeaf JatPoison ArtRuns JatCls JatDepot ArtBridge JatInv JatLift JatFsInv JatFsInvLaws.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx ShadowRLaws.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatIfaceLaws () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceAJx.HAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatIfaceLaws.Laws."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "Stdlib.Lists.List."; "stdpp.bitvector.definitions."], [["0BASE"; "0BUDGET"; "1fst"; "1length"; "1list"; "1nat"; "1option"; "1prod"; "2eq"; "2iff"; "2not"; "3map"; "4Z"; "0G"; "0L"; "0LB"]; ["0LB'"; "0M"; "0MAPS0"; "0NOACC0"; "0RESV0"; "5lb_remove"; "6rt_flagptr"; "6rt_lazy"; "6rt_leak_frames"; "6rt_perm"; "6rt_small_high"; "6rt_statics"; "7rt_wfR"; "8art_fsg"; "8art_fsinv"; "9art_statics_cells"]; [":art_alloc_rep"; ":art_gs"; ":art_iface"; ":rn_ar"; ";In"; ";NoDup"; "0b"; "0rn"; "<bv"; "0u"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Ltac rok_open ROK :=
destruct ROK as (GEO & Esb & Kal & Kspb & Kend & Pal & Plo & Phi & Papp & Hkey & Hloff & Hloff' & Hloff'' & Htpd & Htsdd & Dl2 & Dblk
& Al2t & Al2c & Al2k & Al2s & Abt & Abc & Abk & Abs & Apt & Apc & Apk & Apl & Apb & Aft & Afc & Afk & Afl & Afb & Afp & Fhi & Fapp & Fimg & Flo
& Il2 & Iblk & Afkb & D0 & D1 & D2 & D3 & Adt & Adc & Adk & Adp & Adl & Adb & Adf & Atkb & Ackb & Al2kb & Apkb & Khi).
Ltac geo_open GEO :=
destruct GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
Section SE.
Local Abbreviation SEC_T_art_lazy_zone_bounds := (forall FSG rn (G : art_gs FSG) a, art_run_ok rn -> art_lazy_zone FSG rn G a ->
0x691000 <= a < rn_HI rn /\ ~ (ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES)) (only parsing).
Variable FSG : ltac:(sec_ty2 constr:(SEC_T_art_lazy_zone_bounds) 0%nat 0%nat).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_lazy_zone_bounds) 1%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_lazy_zone_bounds) 2%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_lazy_zone_bounds) 3%nat 0%nat).
Lemma art_lazy_zone_bounds : ltac:(sec_stmt2 constr:(SEC_T_art_lazy_zone_bounds) 4%nat 0%nat).
Proof.
intros ROK Z.
rok_open ROK. geo_open GEO. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap.
destruct Z as [Z|[Z|[[Z|Z] _]]].
- clear - Z G1 Fap. unfold FS_BYTES in *. lia.
- clear - Z Iblk Dblk Afb. unfold apart, FS_BYTES in *. lia.
- clear - Z G4 Kspb Kend Afkb. unfold apart, FS_BYTES in *. lia.
- clear - Z Plo Phi Afp. unfold apart, FS_BYTES in *. lia.
Qed.
End SE.
Lemma art_img_vis : forall FSG rn (G : art_gs FSG) A lazy a n, art_run_ok rn -> art_lazy_ok FSG rn G A lazy -> 0x10000 <= a -> a + n <= 0x691000 -> art_vis (mkH lazy A) a n.
Proof.
intros FSG rn G A lazy a n ROK (LZ & _) Ha Hn x Hx. destruct (mkH lazy A x) eqn:E; [|reflexivity]. exfalso.
unfold mkH in E. apply andb_prop in E as [E _]. pose proof (art_lazy_zone_bounds FSG rn G (U x) ROK (LZ x E)). lia.
Qed.
Section Laws.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x691000.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
#[using="HLhi"] Theorem art_law_lazy : ltac2:(TCodec.tc2 tcn__JatIfaceLaws "?&Gv>&Q3vQ7%211&Q2'MvBvDvCv0v1&N%887654321:%>3=:1").
Proof.
intros LB FF LK cr A M model (G & REP & FS & BV & CRED & CLI & KN & LZ & EG). cbn [vml_of fst snd] in *.
split; [exact (proj1 EG)|]. intros w Hw. cbv zeta. pose proof REP as (ROK & _). destruct LZ as (L1 & _).
destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2). rewrite HLhi.
split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2].
intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw.
Qed.
#[using="HLlo HLhi"] Theorem art_law_wf : ltac2:(TCodec.tc2 tcn__JatIfaceLaws "?&Lv>&Q3vQ7%211&Q2'MvBvDvCv0v1&N%887654321:%>3=:1").
Proof.
intros LB FF LK cr A M V (G & REP & FS & BV & CRED & CLI & KN & LZ & EG).
destruct CLI as (CB & CND & CSA1 & CSA2 & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & CSI & CSP & CS16).
destruct (art_fsinv_wf_proved rn (g_fs art_fsg G) FF LK M FS) as (WF1 & WF2 & WF3 & WF4 & _ & WF6).
destruct CRED as (CR1 & CR2 & _).
split. { intros b Hb. destruct (CB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13).
split. { unfold ablock_range. rewrite HLlo, HLhi. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|exact B6]. }
split; [exact B7|]. split; [exact B8|]. split; [exact B9|]. split; [exact B10|]. split; [exact B11|exact B12]. }
split. { intros f Hf. destruct (WF1 f Hf) as (F1 & F2 & F3 & F4 & F5 & F6). split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
split; [clear - F4; cbn [In] in *; tauto|]. split; [exact F5|exact F6]. }
split; [exact WF2|]. split; [exact WF3|]. split; [rewrite HLlo, HLhi; exact WF4|]. split; [exact CSA2|].
split. { intros x (X1 & X2). apply CSA1. split; [exact X1|]. eapply Z.le_trans; [exact X2|]. unfold HeapIfaceA.S. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. }
split; [split; [exact CS1|exact CS2]|]. split; [split; [exact CS3|split; [exact CS5|split; [exact CS6|exact CS16]]]|]. split; [exact CS4|]. split; [exact CND|].
split; [exact (art_fsinv_nodup_stdpp rn (g_fs art_fsg G) FF LK M FS)|]. split; [exact CR1|]. split; [exact CR2|exact WF6].
Qed.
Definition art_cells_d4 : list (Z * Z * Z) :=
[ (0x13acf8, 8, HeapIfaceA.SB); (0x13ad00, 4, 1); (0x134648, 8, 0x124db0); (0x1345d8, 8, 0x10b84c);
(0x132638, 8, 0x13acf8);
(0x132640, 8, 0x13b9e8); (0x13b9e8, 8, 0); (0x132648, 8, 0x13b9f0); (0x13b9f0, 8, 0);
(0x132650, 8, 0x13b9e0); (0x13b9e0, 8, 0x7fffffffffff);
(0x1331a0, 8, 0x13b9d9); (0x13b9d9, 1, 1);
(0x134640, 8, 0x1249ac);
(0x13b9d8, 1, 1);
(0x134538, 8, 0x125990);
(0x66ed78, 8, 0x66eda0); (0x66eda8, 8, 0x66f580);
(0x13a560, 1, 1); (0x13a564, 4, 0);
(0x66ed28, 8, 0x690238);
(0x132628, 8, 0x1cc828); (0x1cc8b1, 1, 1);
(0x132688, 8, 0x1ca798); (0x1ca798, 4, 0);
(0x133440, 8, 8) ].
Definition art_cells_drv : list (Z * Z * Z) :=
[ (0x1cc87c, 1, 1); (0x134490, 8, 0x12b3b0); (0x134498, 8, 0x11bdac); (0x1344c0, 8, 0x1224a8); (0x1344c8, 8, 0x11c1c4);
(0x134448, 8, 0x134448); (0x137640, 8, 1); (0x137690, 1, 0); (0x138510, 4, 1); (0x1385b0, 8, 0); (0x13a55c, 1, 1);
(0x1cc8a0, 8, 18446744073709551615); (0x1ccba0, 1, 0); (0x132678, 8, 1);
(0x1345f0, 8, 0x1254d0); (0x134480, 8, 0x1248b0); (0x1cc923, 1, 1); (0x138514, 1, 0); (0x1345e8, 8, 0x113744); (0x66ed90, 4, 0); (0x134470, 8, 0x12497c); (0x1cc926, 1, 1); (0x1cc927, 1, 1) ].
Definition art_statics_cells : asan_statics_cells := ASC 0x12c000 0x134000 (art_cells_d4 ++ art_cells_drv).
Hypothesis Htp : rn_tp rn = 0x66ed80.
Hypothesis Hkey0 : rn_key rn = 0.
Hypothesis Htsd : rn_tsd rn = 0x690238.
Hypothesis Hloff : rn_loff rn = 0x10.
#[using="HLsegs Htp Hkey0 Htsd Hloff"] Theorem art_law_statics : ltac2:(TCodec.tc2 tcn__JatIfaceLaws ">&Kv>&O&Q2'MvBvDvCv0v1&NvQ7%9887654321%=3<;1").
Proof.
intros LB FF LK cr A M V (G & REP & FS & BV & CRED & CLI & KN & LZ & EG). rewrite HLsegs.
pose proof REP as (ROK & ST & TH & _). unfold art_rt_thread in TH. rewrite Htp, Hloff in TH. decompose [and] TH. clear TH.
assert (VIS : forall a n, 0x10000 <= a -> a + n <= 0x691000 -> art_vis (mkH (snd V) A) a n) by (intros a n; exact (art_img_vis art_fsg rn G A (snd V) a n ROK LZ)).
assert (UP : forall a (n : nat) v, 0x10000 <= a -> a + Z.of_nat n <= 0x691000 -> cellA (mrestrict (mkH (snd V) A) M) a n v -> cellA M a n v).
{ intros a n v Ha Hn C. apply (art_cell_vis (mkH (snd V) A) M a n v ltac:(lia) ltac:(lia) (VIS a _ Ha Hn)). exact C. }
destruct ST as (PC & LY & T & RO & RZ & DR & TG & CS).
unfold art_layout in LY. unfold art_tsd in T. rewrite Htp, Hkey0, Htsd in T. destruct TG as (GN & TG1 & TG2).
decompose [and] LY. decompose [and] T. decompose [and] CS. clear LY T CS.
split.
- cbn [asc_got_lo asc_got_hi art_statics_cells]. intros a Ha. specialize (GN a Ha). unfold mrestrict in GN.
rewrite (VIS a 1 ltac:(lia) ltac:(lia) (Z_to_bv 64 a) ltac:(rewrite art_u_lit by lia; lia)) in GN. exact GN.
- cbn [asc_cells art_statics_cells art_cells_d4 art_cells_drv app].
repeat (apply Forall_cons; [cbn [fst snd]; apply UP; [lia|cbn; lia|]; first [assumption | (unfold HeapIfaceA.SB; assumption)]|]). apply Forall_nil.
Qed.
#[using="Type"] Lemma art_lb_remove_in : ltac2:(TCodec.tc2 tcn__JatIfaceLaws "A'<'4'7%1233%311&Q4r1&Er3r2%3221%63851%73934p021pR>;1pQ0;1pRD@1").
Proof. induction LB as [|x r IH]; intros b Hb; cbn in Hb; [exact Hb|]. destruct (Z.eqb (fst x) u); [right; exact Hb|]. destruct Hb as [<-|Hb]; [left; reflexivity|right; exact (IH b Hb)]. Qed.
#[using="Type"] Lemma art_lb_remove_keep : ltac2:(TCodec.tc2 tcn__JatIfaceLaws "J'<'4'7%1233%311&Q4r1r2%33521&:'8&2%13<<5r4%43>21%611r3&Er5%2216%?3A41p061p0>1pR>D1pQ0D1pRDI1").
Proof.
induction LB as [|x r IH]; intros b Hb Hne; cbn in *; [exact Hb|]. destruct (Z.eqb_spec (fst x) u) as [E|NE].
- destruct Hb as [<-|Hb]; [exfalso; exact (Hne E)|exact Hb].
- destruct Hb as [<-|Hb]; [left; reflexivity|right; exact (IH b Hb Hne)].
Qed.
#[using="Type"] Lemma art_lb_remove_gone : ltac2:(TCodec.tc2 tcn__JatIfaceLaws "M'<'4'7%1233%311'Q5&;&2%1288r2%447:21%62;1&Q4&Er4r3%3221%53>81&:'8%=3DD5r5%33F21%511p071p0>1pR>G1pQ0G1pRDL1").
Proof.
induction LB as [|x r IH]; intros b ND Hb; cbn in *; [destruct Hb|]. inversion ND as [|y l NI ND']; subst.
destruct (Z.eqb_spec (fst x) u) as [E|NE].
- intros Eb. apply NI. rewrite E, <- Eb. apply in_map. exact Hb.
- destruct Hb as [<-|Hb]; [exact NE|exact (IH b ND' Hb)].
Qed.
#[using="Type"] Lemma art_perm_length : ltac2:(TCodec.tc2 tcn__JatIfaceLaws "Q0'4'7'<%2211%411'Q5&;&2%1266r2%447821%6291&9&Q4r1r5%33=21r4%53?41%7231pR>A1'8'5&3%12E7%22F:%53421p071p0A1p0B1pQ2J1pQ0K1").
Proof.
intros LB LB' N1 N2 EQ. apply Nat.le_antisymm; apply List.NoDup_incl_length.
- exact (List.NoDup_map_inv fst LB' N2).
- intros b Hb. apply EQ. exact Hb.
- exact (List.NoDup_map_inv fst LB N1).
- intros b Hb. apply EQ. exact Hb.
Qed.
Section SE.
Local Abbreviation SEC_T_art_alloc_rep_perm := (ltac2:(TCodec.tc2 tcn__JatIfaceLaws "Q6'Q1'M%211'4'7'<%2211%411'Q8yR0%211'6y8%511%311p051&9&Q4r1r4%33>21r3%53@41%7231pR>B1&Q0vQ7r5r2%45L32:1r6%65N51<:p031p091pQ4C1pQ2L1pQ0M1pLQ31")) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_alloc_rep_perm) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_art_alloc_rep_perm) 1%nat 0%nat).
Variable LB' : ltac:(sec_ty2 constr:(SEC_T_art_alloc_rep_perm) 2%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_rep_perm) 3%nat 0%nat).
Lemma art_alloc_rep_perm : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_rep_perm) 4%nat 0%nat).
Proof using Type G LB LB' M.
intros EQ (ROK & ST & TH & PR & CH & SEC & QU & DEP & IA & BL & GH).
split; [exact ROK|]. split; [exact ST|]. split; [exact TH|]. split; [exact PR|].
split. { intros c Hc. specialize (CH c Hc). cbv zeta in *. destruct CH as (C1 & C2 & C3 & C4). split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
intros w Hw. specialize (C4 w Hw). destruct (g_st art_fsg G c w); try exact C4. destruct C4 as (I1 & REST). split; [apply EQ; exact I1|exact REST]. }
split. { destruct SEC as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & SALL & REST). repeat (split; [assumption|]). split; [|exact REST].
intros i s Hi. destruct (SALL i s Hi) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10). repeat (split; [assumption|]). split; [|exact P10].
destruct (sc_quar s); [exact P9|]. destruct P9 as (Q1 & Q2). split; [apply EQ; exact Q1|exact Q2]. }
split; [exact QU|]. split; [exact DEP|]. split; [exact IA|]. split; [|exact GH].
intros b Hb. apply BL. apply EQ. exact Hb.
Qed.
End SE.
#[using="Type"] Theorem art_law_perm : ltac2:(TCodec.tc2 tcn__JatIfaceLaws "<&I&Q2'MvBvDvCv0v1&NvQ7%9887654321%;11").
Proof.
intros LB LB' FF FF' LK cr A M V (G & REP & FS & BV & CRED & CLI & KN & LZ & EG) EQB ND' EQF NDF'.
destruct CLI as (CB & CND & CREST).
apply NoDup_ListNoDup in ND'. apply NoDup_ListNoDup in NDF'. pose proof CND as CNDl. apply NoDup_ListNoDup in CNDl.
assert (LEN : length LB' = length LB) by (apply art_perm_length; assumption).
pose proof (fsinv_nodup rn (g_fs art_fsg G) FF LK M FS) as NDFL.
assert (EQFL : forall f, In f (FF' ++ LK) <-> In f (FF ++ LK)).
{ intros f. rewrite !in_app_iff. rewrite (EQF f). tauto. }
exists G. split; [exact (art_alloc_rep_perm G LB LB' _ EQB REP)|].
split. { apply (art_fsinv_relist rn (g_fs art_fsg G) FF LK FF' LK M FS EQFL).
pose proof NDFL as NDFL0. rewrite map_app in NDFL |- *. apply List.NoDup_app; [exact NDF'|exact (List.NoDup_app_remove_l _ _ NDFL)|].
intros a Ha HaL. apply in_map_iff in Ha. destruct Ha as (f & Ef & Hf). apply EQF in Hf.
apply in_map_iff in HaL. destruct HaL as (f2 & Ef2 & Hf2).
apply (nodup_app_disj _ _ ff_addr FF LK f f2 NDFL0 Hf Hf2). rewrite Ef, Ef2. reflexivity. }
split; [exact BV|].
split. { unfold art_credit_ok, art_nret in *. rewrite LEN. exact CRED. }
split. { split; [|split; [apply NoDup_ListNoDup; exact ND'|exact CREST]].
intros b Hb. apply EQB in Hb. destruct (CB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
repeat (split; [assumption|]). split; [|split; [|exact B12]].
- intros b' Hb'. apply B10. apply art_lb_remove_keep; [apply EQB; exact (art_lb_remove_in _ _ _ Hb')|exact (art_lb_remove_gone _ _ _ ND' Hb')].
- intros f Hf. apply B11. apply EQFL. exact Hf. }
split; [exact KN|]. split; [exact LZ|].
destruct EG as (AW & EB). split; [exact AW|]. intros b x Hb Hx. apply (EB b x); [apply EQB; exact Hb|exact Hx].
Qed.
#[using="Type"] Theorem art_law_small_high : ltac2:(TCodec.tc2 tcn__JatIfaceLaws "<&J&Q2'MvBvDvCv0v1&NvQ7%9887654321%;11").
Proof.
intros LB FF LK cr A M V (G & REP & FS & BV & CRED & CLI & KN & LZ & EG) b Hb Hs.
destruct CLI as (CB & _). destruct (CB b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B13). unfold BIGSHADOW_HI. exact (B13 Hs).
Qed.
#[using="HLsegs"] Theorem art_law_flagptr : ltac2:(TCodec.tc2 tcn__JatIfaceLaws "=&Fv>&Q2'MvBvDvCv0v1&NvQ7%9887654321%<2;1").
Proof.
intros LB FF LK cr A M V LB' FF' LK' cr' A' M' V' F k rs rs' fl (G & _ & FS & _) (G' & _ & FS' & _) H1 H2 C. rewrite HLsegs in *.
exact (art_fsinv_flagptr rn (g_fs art_fsg G) (g_fs art_fsg G') FF LK FF' LK' M M' F k rs rs' fl FS FS' H1 H2 C).
Qed.
#[using="Type"] Theorem art_law_leak_frames : ltac2:(TCodec.tc2 tcn__JatIfaceLaws "<&H&Q2'MvBvDvCv0v1&NvQ7%9887654321%;11").
Proof.
intros LB FF LK cr A M V FX (G & REP & FS & BV & CRED & CLI & KN & LZ & EG) INC ND.
exists G. split; [exact REP|]. split. { apply (art_fsinv_leak_proved rn (g_fs art_fsg G) FF LK M FX FS INC). apply NoDup_ListNoDup. exact ND. }
split; [exact BV|]. split; [exact CRED|]. split; [|split; [exact KN|split; [exact LZ|exact EG]]].
destruct CLI as (CB & CREST). split; [|exact CREST].
intros b Hb. destruct (CB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
repeat (split; [assumption|]). split; [|exact B12].
intros f Hf. apply B11. apply in_app_iff in Hf. apply in_app_iff. destruct Hf as [Hf|Hf].
- left. apply sfilter_In in Hf. exact (proj2 Hf).
- apply in_app_iff in Hf. destruct Hf as [Hf|Hf]; [left; exact (INC f Hf)|right; exact Hf].
Qed.
End Laws.
