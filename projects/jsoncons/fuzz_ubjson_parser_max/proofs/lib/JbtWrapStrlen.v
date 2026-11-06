(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib HeapIface HeapIfaceA IcptIfaceAB0 ArtMem ArtRuns ArtRunsMem JbtCls JbtCellEx JbtPoison
ArtBridge JbtInv JbtInvMalloc JbtLift JbtWrapKit JbtFsInv JbtFsInvLaws JbtIfaceLaws JbtInvFrame Jb0RegionPoisoned Jb0AsanMemcpy Jb0Memchr Jb0SegStrlen Jb0StrlenIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JbtWrapC JbtWrapVis JbtWrapC2 JbtWrapRng.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtWrapStrlen () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.IcptIfaceAB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0BASE"; "0BUDGET"; "1None"; "1Some"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "2I"; "2and"; "2eq"; "2not"; "2or"]; ["3lt"; "4nth"; "5Z"; "0FF"; "0IL"; "0K"; "0Kt"; "0L"; "0LB"; "0LK"; "6Segment"; "7SpuriousCfg"; "7mkCfg"; "8Model"; "8event"; "8m_halted"]; ["9bvmap"; "0M"; "0M'"; "0MAPS0"; "0NOACC0"; "0R"; "0R'"; "0RESV0"; ":MInv"; ":wx_segs_nowrap"; ";credit"; ";regs_preserved"; "<aacc"; "<aclient"; "<app_rng"; "<asan_layout"]; ["<astack_ok"; "<fframe"; "<hl_img_hi"; "<hl_img_lo"; "<hl_segs"; "<model_rt"; "<vml_of"; "=ret_ok"; ">astrlen_spec"; ">icl_ro_hi"; ">icl_ro_lo"; ">icl_scr_strlen"; ">icl_strlen"; ">icpt_layout"; "?art_fsg"; "?art_fsinv"]; ["@art_iface"; "@art_ri_inv"; "@art_run"; "@rn_ar"; "Agetr"; "Amkst"; "Ardn"; "Aseg_rom"; "BTSet"; "Csrealizes"; "Dloaded_segments"; "Eadd"; "Ediv"; "Ele"; "Elt"; "Emul"]; ["Eof_nat"; "Epow"; "Esub"; "Eto_nat"; "0a"; "0buf"; "0cr"; "0fx"; "0i"; "0j"; "0model"; "0model'"; "0rn"; "0s"; "0scfg"; "0sp"]; ["FBV"; "FZ_to_bv"; "Fbv"; "Fbv_unsigned"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section WS.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x693000.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Context {fx : PropExec.FPState}.
Section SE.
Variables (R : bvmap 5 word).
Variables (M : word -> option byte).
Variables (model : Model).
Variables (LB : list (Z * Z)).
Variables (FF LK : list fframe).
Variables (cr : credit).
Variables (A : list (Z * Z)).
Variables (s K : Z).
Variables (buf : list byte).
Variables (Kt : ShapeAlg.TSet).
Theorem art_wrap_strlen : let sp := U (getr R 2) in
RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
getr R 10 = Z_to_bv 64 s -> Hoare.ret_ok (getr R 1) ->
astack_ok L (rn_ar rn) M 2304 sp ->
0 <= s -> s + Z.of_nat (length buf) <= 2 ^ 47 -> 0 <= K < 2 ^ 27 ->
rdn ASEGS M (Z_to_bv 64 s) (length buf) = Some buf ->
(s + K) / 8 * 8 + 8 <= s + Z.of_nat (length buf) ->
nth (Z.to_nat K) buf (Z_to_bv 8 0) = Z_to_bv 8 0 ->
(forall j, (j < Z.to_nat K)%nat -> nth j buf (Z_to_bv 8 0) <> Z_to_bv 8 0) ->
(forall i, 0 <= i < Z.of_nat (length buf) -> hl_img_lo L <= s + i < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp 2304 (s + i)) ->
(forall a, 0x10390 <= a < 0x103b0 -> M (Z_to_bv 64 a) = None) ->
aacc M s (K + 1) -> app_rng (rn_ar rn) s (K + 1) ->
Kt [] ->
(forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
getr R' 10 = Z_to_bv 64 K -> regs_preserved R R' ->
(forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 2304 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
(forall a, sp - 2304 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
(forall a : word, M a <> None -> M' a <> None) ->
model_rt model model' -> MInv A model' ->
RI LB FF LK cr A M' (vml_of model') ->
srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') Kt) ->
srealizes ASEGS scfg (mkCfg (mkst R (0x62ce4 : word) M (seg_rom ASEGS)) model) Kt.
Proof using Hwx HLsegs HLlo HLhi R M model LB FF LK cr A s K buf Kt.
intros sp INV Hhalt HMI H10 Hret AST Hs0 Hs47 HK RD WIN NUL NZ CLS RO AACC APPR KT0 CONT.
destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
set (Mr0 := mrestrict (bhid A model) M) in *.
destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
change (2 ^ 27) with 134217728 in HK.
pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
pose proof REPr as (ROK & STAT & _).
assert (LEN1 : K + 1 <= Z.of_nat (length buf)).
{ pose proof (Z.div_mod (s + K) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (s + K) 8 ltac:(lia)). clear - WIN D H. lia. }
assert (LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
0x693000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)).
{ intros w Hw. destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2).
split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2]. intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw. }
assert (OFFSCR : forall i, 0 <= i < Z.of_nat (length buf) -> ~ (sp - 2304 <= s + i < sp)).
{ intros i Hi. apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2304 (s + i) ltac:(lia) (CLS i Hi)). }
assert (HDJ : s + Z.of_nat (length buf) <= sp - 2216 \/ sp <= s).
{ destruct (art_rng_off_window s (Z.of_nat (length buf)) (sp - 2304) sp ltac:(clear - LEN1 HK; lia) ltac:(lia) OFFSCR) as [X | X]; [left; lia | right; exact X]. }
destruct (art_rng_facts rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) sp 2304 s (K + 1) Hs0 ltac:(clear - HK; lia) ltac:(clear - HK; lia)
ltac:(intros i Hi; apply CLS; clear - Hi LEN1; lia) AACC APPR) as (_ & (FL1 & FL2) & HZS & (kS & HLS & HkS) & HWS).
set (FP := fun x => sp - 2216 <= x < sp).
apply (art_wrap_pure2 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx (art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0) Kt R (0x62ce4 : word) M model G LB FF LK cr A FP
(fun R' pc1 Mr' => pc1 = getr R 1 /\ getr R' 10 = Z_to_bv 64 K /\ keeps_cs R R') REPr FS B0 CRED CLI KN LZ EG).
-
assert (VISB : art_vis (bhid A model) s (Z.of_nat (length buf))).
{ intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
apply (art_aclient_vis rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2304 (U x)); [pose proof (u64_range x); lia|].
replace (U x) with (s + (U x - s)) by ring. apply CLS. clear - Hx. lia. }
assert (HSLEN : slenH Mr0 (Z_to_bv 64 s) buf K).
{ constructor.
- exact (art_rng_rdn A M model s (length buf) buf Hs0 ltac:(clear - Hs47; lia) VISB RD).
- rewrite art_u_lit by (clear - Hs0 Hs47; lia). exact WIN.
- rewrite art_u_lit by (clear - Hs0 Hs47; lia). clear - Hs47. lia.
- clear - HK. lia.
- rewrite NUL. reflexivity.
- intros j Hj E. apply (NZ j Hj). apply bv_eq. rewrite E. reflexivity.
- intros i Hi. unfold Mr0, mrestrict. rewrite (RO i Hi). destruct (bhid A model (Z_to_bv 64 i)); reflexivity. }
assert (W0 : wrA Mr0 (sp - 2304) 2304).
{ apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 2304 ROK LZ ltac:(lia) ltac:(lia) ltac:(lia)). exact SWR. }
assert (HOK : store_ok ASEGS Mr0 (Z_to_bv 64 (sp - 2216)) 2216 = true).
{ replace (sp - 2216) with (sp - 2304 + 88) by ring. apply W0; [lia | cbn; lia]. }
destruct STAT as (_ & LAY & _ & _ & _ & _ & _ & S8).
assert (HGL : rt_layout_globs Mr0).
{ destruct LAY as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _). unfold rt_layout_globs. repeat split; [lit_cell A1 | lit_cell A2 | lit_cell A3 | lit_cell A4 | lit_cell A5 | lit_cell A6 | lit_cell A7 | lit_cell A8]. }
assert (VIMG : forall a (n : nat), 0x10000 <= a -> a + Z.of_nat n <= 0x693000 -> art_vis (bhid A model) a (Z.of_nat n)).
{ intros a n H1 H2 x Hx. apply (art_vis_byte rn LB A model LAZY). left. lia. }
assert (HIC : sl_icpt_globs Mr0).
{ destruct LAY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A13 & _).
assert (INITED : cellA Mr0 0x13d718 1 1) by conj_find S8.
assert (C2r : cellA Mr0 0x1ce663 1 1) by conj_find S8.
destruct (fsinv_cs _ _ _ _ _ FS) as (_ & CS1 & _).
assert (C1r : cellA Mr0 0x1361b8 8 0x1270cc) by (apply (proj2 (art_cell_vis (bhid A model) M 0x1361b8 8 0x1270cc ltac:(lia) ltac:(cbn; lia) (VIMG 0x1361b8 8%nat ltac:(lia) ltac:(cbn; lia)))); exact CS1).
unfold sl_icpt_globs. repeat split.
- rewrite <- le1_one. lit_cell INITED.
- lit_cell C1r.
- lit_cell A13.
- rewrite <- le1_one. lit_cell C2r. }
set (fS := Jb0RegionPoisoned.SB + s / 8) in *. set (lS := Jb0RegionPoisoned.SB + (s + (K + 1) - 1) / 8) in *.
assert (HKK : 0 <= K /\ K + 1 <= 2 ^ 40) by (clear - HK; lia).
assert (HSs : 16777216 <= sp - 2216 /\ sp < 2 ^ 64) by (clear - SHI SLE STOP HI1; lia).
assert (HSH : lS + 8 <= sp - 2216) by (clear - FL2 SHI; lia).
destruct (wrap_strlen_run Mr0 (seg_rom ASEGS) (getr R 2) (getr R 1) s K (K + 1) sp buf kS fS lS (fS - fS mod 8) (lS - lS mod 8)
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HKK (art_rng_app8 rn LB FF LK A M CLI s (K + 1) Hs0 ltac:(clear - HK; lia) APPR) HSs HSH HSLEN HDJ HOK Hret HGL HIC
(fun _ => HZS) (fun _ => HLS) HkS (fun _ => HWS) R H10 eq_refl eq_refl)
as (R' & M' & RUN & Q10 & Q2 & Q1 & KCS & OA & GRr).
exists R', (getr R 1), M'. split; [exact RUN|]. split; [exact GRr|].
assert (FRr : forall x : word, ~ FP (U x) -> M' x = Mr0 x) by (intros x Hx; apply OA; unfold FP in Hx; clear - Hx; lia).
split; [exact FRr|]. split; [|split; [reflexivity | split; [exact Q10 | exact KCS]]].
apply (art_lsan_kept rn G LB Mr0 M' FP REPr FRr). intros x Hx. unfold FP in Hx. clear - Hx SHI. lia.
- intros x Hx Z. exfalso. pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)). unfold FP in Hx. clear - H Hx SHI. lia.
- intros x Hx Z3. exfalso. pose proof (art_fs_zone3_below rn G LB _ x REPr Z3). unfold FP in Hx. clear - H Hx SHI. lia.
- intros x Hx Zc. pose proof (art_cs_zone_below rn G LB FF LK M Mr0 x REPr FS Zc). unfold FP in Hx. clear - H Hx SHI. lia.
- intros b x Hb Hx X. pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx). unfold FP in X. clear - H X SHI HI1. lia.
-
intros R' pc1 Mr' M1 model' (Epc & Q10 & KCS) RI' GROW FR1 VIS HID RT MI'. subst pc1.
apply (CONT R' M1 model' Q10 (keeps_cs_preserved R R' KCS)); [ | | exact GROW | exact RT | exact MI' | exact RI'].
+ intros a Ra Ha. apply FR1. rewrite art_u_lit by exact Ra. unfold FP. intros X.
apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2304 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
+ intros a Ha. apply GROW.
assert (WM : wrA M (sp - 2304) 2304) by (intros d k Hd Hk; apply SWR; assumption).
pose proof (art_wr_wview ASEGS M (sp - 2304) 2304 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE STOP; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Ha SHI HI1 SLE STOP; lia). specialize (V ltac:(clear - Ha; lia)).
rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE STOP; lia); right; clear - Ha SHI HI1; lia). exact V.
Qed.
End SE.
End WS.
Lemma lit_62ce4 : ltac2:(TCodec.tc2 tcn__JbtWrapStrlen "<'='S2yR0%211&S1+\[W4%2241(S0(;%23741/017%;3851"). Proof. apply bv_eq. reflexivity. Qed.
Theorem art_astrlen : ltac2:(TCodec.tc2 tcn__JbtWrapStrlen "RE'6':'S2yR0%211%4211%611'B'R2'K&Q9&R:%211'Q?'QM'='J%A11&QDr2%211%6341:&QCr3%211+RPP0%;3C21&QBr4%211+Vb\P0%@3H21&QL%115+\[W4%D3L21&QKr5%211+RX0%I3Q121&QJr6%211+RPl@%N3Q621&QIr7%211+RPm@%Q33Q;21&QHr9&R3r<%211r8r;&R0'QNrAr@r?r>r=&QO%887654321<%@5?<;:1p0B1p0H1p0N1p0Q41p0Q91p0Q?1p0QE1pQ:QM1pQ@QO1p0R11pUNR51pUJR71p6R91p4R:1pR:R<1pR@R=1pR8R>1").
Proof.
intros MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L IL HLsegs HLlo HLhi E1 E2 E3 E4 fx R M model LB FF LK cr A s K buf Kt. cbv zeta.
intros INV Hh HMI H10 H4 Hret AST Hs0 Hs47 HK RD WIN NUL NZ CLS RO AACC APPR KT0 POST.
rewrite HLsegs, E2 in *. rewrite E3, E4 in RO. rewrite E1, lit_62ce4.
apply (art_wrap_strlen MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi R M model LB FF LK cr A s K buf Kt INV Hh HMI H10 Hret AST Hs0 Hs47 HK RD WIN NUL NZ CLS RO AACC APPR KT0).
intros R' M' model' Q10 RP FR SD GR RT MI' RI'. apply (POST R' M' model' Q10 RP FR SD GR RT MI' RI').
Qed.
