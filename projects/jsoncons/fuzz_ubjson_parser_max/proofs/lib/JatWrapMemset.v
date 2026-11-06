(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib MemSplit MemsetLib HeapIface HeapIfaceA ArtMem ArtRuns ArtRunsMem JatCls JatCellEx JatPoison
ArtBridge JatInv JatInvMalloc JatLift JatWrapKit JatFsInv JatFsInvLaws JatIfaceLaws Ja0RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JatWrapC JatWrapVis.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Ja0AsanMemset JatWrapC2 JatWrapRng.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatWrapMemset () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0BASE"; "0BUDGET"; "1None"; "1bool"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"]; ["3Z"; "0FF"; "0K"; "0L"; "0LB"; "0LK"; "4store_ok"; "5mkCfg"; "6Model"; "6event"; "6m_halted"; "7bvmap"; "0M"; "0M'"; "0MAPS0"; "0NOACC0"]; ["0R"; "0R'"; "0RESV0"; "8MInv"; "9credit"; "9regs_preserved"; ":aacc"; ":aclient"; ":aclientw"; ":app_rng"; ":astack_ok"; ":byte_at"; ":fframe"; ":model_rt"; ":vml_of"; ";ret_ok"]; ["<art_fsg"; "<art_fsinv"; "=art_ri_inv"; "=rn_ar"; ">getr"; ">mkst"; ">seg_rom"; "?TSet"; "@srealizes"; "Aloaded_segments"; "Badd"; "Ble"; "Blt"; "Bmodulo"; "Bof_nat"; "Bpow"]; ["Bsub"; "0a"; "0c"; "0cr"; "0dst"; "0fx"; "0i"; "0m"; "0model"; "0model'"; "0n"; "0rn"; "0scfg"; "0sp"; "CBV"; "CZ_to_bv"]; ["Cbv"; "Cbv_unsigned"; "0v"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section WMS.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis AFL : art_alloc_rep_frame_law art_fsg MAPS0 RESV0.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x691000.
Hypothesis HLroimg : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x691000.
Hypothesis HLstimg : forall a, hl_rt_static L a -> 0x10000 <= a < 0x691000.
Hypothesis HLlsan : forall a, rn_tp rn + rn_loff rn <= a < rn_tp rn + rn_loff rn + 4 -> hl_rt_static L a.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Hypothesis PRIVZ : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) lazy,
art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
forall a, art_alloc_zone art_fsg rn G a -> ~ in_block LB a -> art_private L (rn_ar rn) LB FF a.
Hypothesis PRIVF : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) lazy,
art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
forall a, fs_zone3 rn a -> ~ in_fframe FF a -> art_private L (rn_ar rn) LB FF a.
Hypothesis PRIVCS : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) lazy,
art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
forall a, cs_zone rn a -> art_private L (rn_ar rn) LB FF a.
Context {fx : PropExec.FPState}.
#[using="Hwx AFL HLsegs HLlo HLhi HLroimg HLstimg HLlsan PRIVZ PRIVF PRIVCS"] Theorem art_wrap_memset : ltac2:(TCodec.tc2 tcn__JatWrapMemset "X9&Ky5'R@yR0%211%5241'8y8%611%311p061'H'5'9'@%2211%411&Q<%611&Q4&QG&RA&QDr<(R>+2(;%33J21%6251%82J1&QB'Q@vNvQ2vOv1v2&QAvR;r:r9r8r7r6&Q>r;%211%A?@?>=<;:987654H1'=%Q;1Q=&J%11L(3%11QA%63531'Q3r=%22@1r@+:%Q43QK1Q2%Q7231&R?%12QLF%@3QL31rA+<%Q;3R21Q9%Q>231%72R2K%F3R221'<&QKz%221Q1&QO+K%22QD1%62Q51%8251&Q?rC+1%QK3RB1QI%QN231%511&Q:vC&QC%11QC+R`0%5542:1QB&Q6rD%231Q6QAr1%H2G1&QL%123Q:%L231&Q8rE&QJr2%22Q>1%57B@4<RB?1p071pT>RM1'6%Q52Q46r3&QN%119%;231%Q:21QH'4&F&QIrJr4%B2Q71%QK2SF1%64541<(:%R<3921p0;1p0A1pT@C1pT>SB1(7'I%211%R<11&Q9r?%23Q>R61+;%SA3T81S?%SD2D1%R=2T8R:%RL3T821%SG2ORArF%RA2T<1%S03T<31&Q5rO%221LrG%QD2QF1%R?2QF1'>&QM+X0%22Q41%S;3T=QL1&Q;rK%QH21Q@%33SE1R0%RI251qU6TC1%;2TD1p0=1pT>TF1+R0%RK2T=1%R62R81%S12R81&Q7rQ0%27RDRB1IGRAR4&?rL%S621R0%R922QI%R?2R21%S:231%611%SE2U@QL%T<11rQ4%113%T73U>31p061p0>1p0B1pT4U=1&R0%12Q9S3%SF21RO%SH21Q:%T22UMRI%TH11%T>1UJ%TC3UJ21%H11p061pT4UH1&Q=rQ1%221TNrM%TD21U1rQ2rN%U21U5%UA?U@U?U>U=U<U;U:U937Q5QM2U71'QHvR<(G&QEvR5rQ6%V021T3&QF%11S3%655U<3UB1%821UB%;4S6:1QNp0=1p0B1p0E1p0I1p0Q51p0QM1p0R?1p0RC1pTDVI1pQLVK1pR4W11+^mnH%V@3W51V>/01W5%G5FQM1R=B%I21SE%L4SGK1U;p071p0S21p0S81p0S<1p0SA1p0T71p0TE1p0TI1p0U01p0U71p0UA1p0UH1p0V01p0V41p0V<1tTLW>VO1pQ6W91pTFW@1pT6WA1pT:WB1p2WA1pT8W?1pQ<WA1pQ4WB1pQ:WE1pTBWK1pQJWM1pR2X31").
Proof.
intros R M model LB FF LK cr A dst c n K sp INV Hhalt HMI H10 H12 Hn Hret AST AACC CLW DOK KT0 APPR H11 CONT.
pose proof (proj1 APPR) as Hd0.
destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
set (Mr0 := mrestrict (bhid A model) M) in *.
destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
change (2 ^ 27) with 134217728 in Hn.
pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
pose proof REPr as (ROK & STAT & _).
assert (LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
0x691000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)).
{ intros w Hw. destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2).
split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2]. intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw. }
assert (CLS : forall i, 0 <= i < n -> hl_img_lo L <= dst + i < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp 2560 (dst + i)).
{ intros i Hi. right. apply aclientw_client. exact (CLW i Hi). }
assert (OFF : forall i, 0 <= i < n -> ~ (sp - 2560 <= dst + i < sp)).
{ intros i Hi. apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2560 (dst + i) ltac:(lia) (CLS i Hi)). }
assert (HDJ : 0 < n -> dst + n <= sp - 2200 \/ sp <= dst).
{ intros Hn0. destruct (art_rng_off_window dst n (sp - 2560) sp Hn0 ltac:(lia) OFF) as [X | X]; [left; lia | right; exact X]. }
assert (APPD : (dst + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= dst)) by exact (proj1 (proj2 APPR)).
set (FP := fun x => sp - 2200 <= x < sp \/ dst <= x < dst + n).
apply (art_wrap_pure2 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx AFL K R (0x777d8 : word) M model G LB FF LK cr A FP
(fun R' pc1 Mr' => pc1 = getr R 1 /\ getr R' 10 = Z_to_bv 64 dst /\ keeps_cs R R'
/\ (forall i, 0 <= i < n -> Mr' (Z_to_bv 64 (dst + i)) = Some (Z_to_bv 8 (c mod 256))))
REPr FS B0 CRED CLI KN LZ EG).
-
assert (W0 : wrA Mr0 (sp - 2560) 2560).
{ apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 2560 ROK LZ ltac:(lia) ltac:(lia) ltac:(lia)). exact SWR. }
assert (HOK : store_ok ASEGS Mr0 (Z_to_bv 64 (sp - 2200)) 2200 = true).
{ replace (sp - 2200) with (sp - 2560 + 360) by ring. apply W0; [lia | cbn; lia]. }
assert (VIMG : forall a (k : nat), 0x10000 <= a -> a + Z.of_nat k <= 0x691000 -> art_vis (bhid A model) a (Z.of_nat k)).
{ intros a k H1 H2 x Hx. apply (art_vis_byte rn LB A model LAZY). left. lia. }
destruct STAT as (_ & LAY & _ & _ & _ & _ & _ & S8).
assert (HGL : rt_layout_globs Mr0).
{ destruct LAY as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _). unfold rt_layout_globs. repeat split; [lit_cell A1 | lit_cell A2 | lit_cell A3 | lit_cell A4 | lit_cell A5 | lit_cell A6 | lit_cell A7 | lit_cell A8]. }
assert (C1 : cellA Mr0 0x1331a0 8 0x13b9d9) by conj_find S8.
assert (C2 : cellA Mr0 0x13b9d9 1 1) by conj_find S8.
assert (HIC : ms_icpt_globs Mr0).
{ destruct LAY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A12 & _). unfold ms_icpt_globs. repeat split.
- lit_cell C1.
- rewrite <- le1_one. lit_cell C2.
- lit_cell A12. }
set (f := Ja0RegionPoisoned.SB + dst / 8). set (l := Ja0RegionPoisoned.SB + (dst + n - 1) / 8).
assert (D47 : dst + n + 16 <= 2 ^ 47).
{ destruct APPR as (_ & _ & TOP). destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & _ & T16). clear - TOP T16. lia. }
assert (HSH : l + 8 <= sp - 2200).
{ unfold l, Ja0RegionPoisoned.SB. assert ((dst + n - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - D47; lia). change (2 ^ 47 / 8) with 17592186044416 in *. clear - H SHI HI1. lia. }
assert (RNG : art_vis (bhid A model) dst n
/\ (0 < n -> forall x : word, f <= U x < l -> Mr0 x = Some (Z_to_bv 8 0))
/\ (exists kL, (0 < n -> Mr0 (Z_to_bv 64 l) = Some (Z_to_bv 8 kL)) /\ (kL = 0 \/ (dst + n - 1) mod 8 < kL <= 7))
/\ (0 < n <= 64 -> exists w0 w1, rdn ASEGS Mr0 (Z_to_bv 64 (f - f mod 8)) 8 = Some w0 /\ rdn ASEGS Mr0 (Z_to_bv 64 (l - l mod 8)) 8 = Some w1)).
{ destruct (Z_lt_le_dec 0 n) as [Np | Nz].
- destruct (art_rng_facts rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) sp 2560 dst n Hd0 Np ltac:(clear - Hn; lia) CLS AACC APPR)
as (VIS & _ & HZ & (kL & HL & HkL) & HW).
split; [exact VIS|]. split; [intros _; exact HZ|]. split; [exists kL; split; [intros _; exact HL | exact HkL]|]. intros _. exact HW.
- split; [intros x Hx; exfalso; clear - Hx Nz; lia|]. split; [intros X; exfalso; clear - X Nz; lia|].
split; [exists 0; split; [intros X; exfalso; clear - X Nz; lia | left; reflexivity]|]. intros X; exfalso; clear - X Nz; lia. }
destruct RNG as (VIS & HZ & (kL & HL & HkL) & HW).
assert (HAPP : (0 <= dst /\ dst + n + 8 <= LOWEND) \/ (HIGHBEG <= dst /\ dst + n + 8 <= HIGHEND)).
{ exact (art_rng_app8 rn LB FF LK A M CLI dst n Hd0 ltac:(clear - Hn; lia) APPR). }
assert (HDST : store_ok ASEGS Mr0 (Z_to_bv 64 dst) (Z.to_nat n) = true).
{ apply (art_rng_store_ok A M model dst (Z.to_nat n) Hd0 ltac:(rewrite Z2Nat.id by (clear - Hn; lia); clear - D47; lia)).
- rewrite Z2Nat.id by (clear - Hn; lia). exact VIS.
- pose proof (DOK 0 (Z.to_nat n) ltac:(lia) ltac:(rewrite Z2Nat.id by (clear - Hn; lia); lia)) as X. rewrite Z.add_0_r in X. exact X. }
assert (HSs : 0x1000000 <= sp - 2200 /\ sp < 2 ^ 64) by (clear - SHI SLE STOP HI1; lia).
destruct (@asan_memset_run fx Mr0 (seg_rom ASEGS) (getr R 2) (getr R 1) (getr R 11) dst n sp kL f l (f - f mod 8) (l - l mod 8)
eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(clear - Hn; lia) HAPP HSs HSH HDJ HOK HDST Hret HGL HIC HZ HL HkL HW R H10 eq_refl H12 eq_refl eq_refl)
as (R' & Mj & RUN & Q10 & Q2 & Q1 & KCS & OA & GRr).
set (Mf := wbytes Mj (Z_to_bv 64 dst) (repeat (cbyte (getr R 11)) (Z.to_nat n))) in *.
assert (LENR : Z.of_nat (length (repeat (cbyte (getr R 11)) (Z.to_nat n))) = n) by (rewrite repeat_length, Z2Nat.id by (clear - Hn; lia); reflexivity).
assert (FRr : forall x : word, ~ FP (U x) -> Mf x = Mr0 x).
{ intros x Hx. unfold FP in Hx. pose proof (u64_range x) as Rx.
assert (E1 : Mf x = Mj x).
{ unfold Mf. destruct (Z_lt_le_dec (U x) dst) as [Lt | Ge].
- apply wbytes_below; [rewrite LENR, art_u_lit by (clear - Hd0 D47 Hn; lia); clear - D47 Hd0 Hn; lia | rewrite art_u_lit by (clear - Hd0 D47 Hn; lia); exact Lt].
- apply wbytes_above. rewrite LENR, art_u_lit by (clear - Hd0 D47 Hn; lia). clear - Hx Ge. lia. }
rewrite E1. apply OA. clear - Hx. lia. }
exists R', (getr R 1), Mf. split; [exact RUN|].
split. { eapply mem_grows_trans; [exact GRr | apply wbytes_grows]. }
split; [exact FRr|].
split.
{
pose proof REPr as (_ & _ & (_ & _ & _ & _ & _ & _ & _ & CL) & _).
assert (GEOL : 0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x691000).
{ pose proof ROK as ROK'. rok_open ROK'. geo_open GEO. clear - Hloff Hloff' Hloff'' Htpd G1 G2 Espb G4. lia. }
apply (JatAllocG.cell_agree Mr0 Mf); [| clear - GEOL; lia | cbn; clear - GEOL; lia | exact CL].
intros x Hx. cbn in Hx. apply FRr. unfold FP. intros [X | X]; [clear - X Hx GEOL SHI HI1; lia|].
apply (art_clientw_not_static rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLstimg sp 2560 (U x)).
- replace (U x) with (dst + (U x - dst)) by ring. apply CLW. clear - X. lia.
- unfold BIGSHADOW_LO. left. clear - Hx GEOL. lia.
- apply HLlsan. clear - Hx. lia. }
split; [reflexivity|]. split; [exact Q10|]. split; [exact KCS|].
intros i Hi. unfold Mf. rewrite (wbytes_inside _ Mj (Z_to_bv 64 dst) (Z_to_bv 64 (dst + i))).
+ rewrite H11, cbyte_Z. rewrite !art_u_lit by (clear - Hd0 D47 Hi; lia). rewrite nth_repeat_lt by (clear - Hi; lia).
f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
+ rewrite LENR, art_u_lit by (clear - Hd0 D47 Hn; lia). clear - D47 Hd0 Hn. lia.
+ rewrite LENR, !art_u_lit by (clear - Hd0 D47 Hi; lia). clear - Hi. lia.
-
intros x [Hx | Hx] Z.
+ exfalso. pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)). clear - H Hx SHI. lia.
+ destruct (in_block_dec LB x) as [IB | NB]; [exact IB | exfalso].
apply (art_clientw_not_private rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLroimg sp 2560 x).
* replace x with (dst + (x - dst)) by ring. apply CLW. clear - Hx. lia.
* unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - APPD Hx. lia.
* exact (PRIVZ G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Z NB).
-
intros x [Hx | Hx] Z3.
+ exfalso. pose proof (art_fs_zone3_below rn G LB _ x REPr Z3). clear - H Hx SHI. lia.
+ destruct (in_fframe_dec FF x) as [IB | NB]; [exact IB | exfalso].
apply (art_clientw_not_private rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLroimg sp 2560 x).
* replace x with (dst + (x - dst)) by ring. apply CLW. clear - Hx. lia.
* unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - APPD Hx. lia.
* exact (PRIVF G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Z3 NB).
-
intros x [Hx | Hx] Zc.
+ pose proof (art_cs_zone_below rn G LB FF LK M Mr0 x REPr FS Zc). clear - H Hx SHI. lia.
+ apply (art_clientw_not_private rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLroimg sp 2560 x).
* replace x with (dst + (x - dst)) by ring. apply CLW. clear - Hx. lia.
* unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - APPD Hx. lia.
* exact (PRIVCS G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Zc).
-
intros b x Hb Hx [X | X].
+ pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx). clear - H X SHI HI1. lia.
+ pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx) as B1. pose proof CLI as (CB & _). destruct (CB b Hb) as (K1 & _).
unfold in_shadow_of in Hx. pose proof (art_S_lo (fst b) ltac:(clear - K1; lia)) as B2. unfold BIGSHADOW_LO, BIGSHADOW_HI in APPD. clear - APPD X B1 B2 Hx. lia.
-
intros R' pc1 Mr' M1 model' (Epc & Q10 & KCS & BYTES) RI' GROW FR1 VIS1 HID RT MI'. subst pc1.
assert (VISD : forall i, 0 <= i < n -> bhid A model (Z_to_bv 64 (dst + i)) = false).
{ intros i Hi. apply (art_aclient_vis rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2560 (dst + i)); [|exact (CLS i Hi)].
destruct APPR as (_ & _ & TOP). destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & _ & T16). clear - TOP T16 Hd0 Hi. lia. }
apply (CONT R' M1 model' Q10 (keeps_cs_preserved R R' KCS)); [ | | | exact RT | exact MI' | exact RI'].
+ intros i Hi. exists (c mod 256). split; [reflexivity|]. unfold byte_at. rewrite (VIS1 _ (VISD i Hi)). exact (BYTES i Hi).
+ intros a Ra Ha ND. apply FR1. rewrite art_u_lit by exact Ra. unfold FP. intros [X | X]; [|exact (ND X)].
apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2560 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
+ intros a Ha. apply GROW.
assert (WM : wrA M (sp - 2560) 2560) by (intros d k Hd Hk; apply SWR; assumption).
pose proof (art_wr_wview ASEGS M (sp - 2560) 2560 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE STOP; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Ha SHI HI1 SLE STOP; lia). specialize (V ltac:(clear - Ha; lia)).
rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE STOP; lia); right; clear - Ha SHI HI1; lia). exact V.
Qed.
End WMS.
