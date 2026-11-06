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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Ja0AsanMemset Ja0AsanMemcpy JatWrapC2 JatWrapRng JatWrapMemset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatWrapCopy () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLift."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0BASE"; "0BUDGET"; "1None"; "1Some"; "1bool"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"]; ["2not"; "2or"; "3Z"; "0FF"; "0G"; "0K"; "0L"; "0LB"; "0LK"; "4store_ok"; "5mkCfg"; "6Model"; "6event"; "6m_halted"; "6m_vm_lazy"; "6page_base"]; ["6page_in_ranges"; "7bvmap"; "0M"; "0M'"; "0MAPS0"; "0Mr0"; "0NOACC0"; "0R"; "0R'"; "0RESV0"; "8bhid"; "8in_shadow_rw"; "9MInv"; "9mrestrict"; ":credit"; ":in_block"]; [":regs_preserved"; ";FS_BYTES"; ";aacc"; ";aclient"; ";aclientw"; ";app_rng"; ";ar_fs"; ";astack_ok"; ";byte_at"; ";fframe"; ";hl_img_hi"; ";hl_img_lo"; ";model_rt"; ";vml_of"; "<ret_ok"; "=SB"]; [">art_fsg"; ">art_fsinv"; "?art_client_ok"; "?art_gs"; "?art_ri_inv"; "?g_fs"; "?rn_HI"; "?rn_ar"; "@art_vis"; "Agetr"; "Amkst"; "Ardn"; "Aseg_rom"; "BTSet"; "Csrealizes"; "Dloaded_segments"]; ["Enth_error"; "Fadd"; "Fdiv"; "Fle"; "Flt"; "Fmodulo"; "Fof_nat"; "Fpow"; "Fsub"; "Fto_nat"; "0a"; "0bs"; "0cr"; "0dst"; "0f"; "0fx"]; ["0i"; "0kL"; "0l"; "0m"; "0model"; "0model'"; "0n"; "0p"; "0pc0"; "0rn"; "0scfg"; "0sp"; "0src"; "GBV"; "GZ_to_bv"; "Gbv"]; ["Gbv_unsigned"; "0v"; "0w"; "0w0"; "0w1"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section WCP.
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
Variable pc0 : word.
Variable FRB : Z.
Hypothesis FRB_rng : 2048 <= FRB <= 2560.
Definition copy_run_spec : Prop :=
forall (mem0 : word -> option byte) (sp ra : word) (pd ps n s : Z) (bs : list byte) (kS fS lS kD fD lD : Z),
U sp = s -> fS = Ja0RegionPoisoned.SB + ps / 8 -> lS = Ja0RegionPoisoned.SB + (ps + n - 1) / 8 ->
fD = Ja0RegionPoisoned.SB + pd / 8 -> lD = Ja0RegionPoisoned.SB + (pd + n - 1) / 8 ->
0 <= n <= 2 ^ 40 -> in_app8 ps n -> in_app8 pd n -> 0x1000000 <= s - FRB /\ s < 2 ^ 64 -> lS + 8 <= s - FRB -> lD + 8 <= s - FRB ->
(0 < n -> ps + n <= s - FRB \/ s <= ps) -> (0 < n -> pd + n <= s - FRB \/ s <= pd) -> (pd + n <= ps \/ ps + n <= pd) ->
store_ok ASEGS mem0 (Z_to_bv 64 (s - FRB)) (Z.to_nat FRB) = true -> store_ok ASEGS mem0 (Z_to_bv 64 pd) (Z.to_nat n) = true ->
rdn ASEGS mem0 (Z_to_bv 64 ps) (Z.to_nat n) = Some bs -> ret_ok ra -> rt_layout_globs mem0 -> mc_icpt_globs mem0 ->
(0 < n -> forall x : word, fS <= U x < lS -> mem0 x = Some (Z_to_bv 8 0)) -> (0 < n -> mem0 (Z_to_bv 64 lS) = Some (Z_to_bv 8 kS)) ->
(kS = 0 \/ (ps + n - 1) mod 8 < kS <= 7) ->
(0 < n <= 64 -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 (fS - fS mod 8)) 8 = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 (lS - lS mod 8)) 8 = Some w1) ->
(0 < n -> forall x : word, fD <= U x < lD -> mem0 x = Some (Z_to_bv 8 0)) -> (0 < n -> mem0 (Z_to_bv 64 lD) = Some (Z_to_bv 8 kD)) ->
(kD = 0 \/ (pd + n - 1) mod 8 < kD <= 7) ->
(0 < n <= 64 -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 (fD - fD mod 8)) 8 = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 (lD - lD mod 8)) 8 = Some w1) ->
forall regs, getr regs 10 = Z_to_bv 64 pd -> getr regs 11 = Z_to_bv 64 ps -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
exists regs' Mf Mj,
msteps ASEGS (mkst regs pc0 mem0 (seg_rom ASEGS)) (mkst regs' ra Mf (seg_rom ASEGS))
/\ getr regs' 10 = Z_to_bv 64 pd /\ keeps_cs regs regs' /\ mem_grows mem0 Mf
/\ (forall x : word, U x < s - FRB \/ s <= U x -> Mj x = mem0 x)
/\ (forall x : word, Mf x = wbytes Mj (Z_to_bv 64 pd) bs x).
Hypothesis RUNX : copy_run_spec.
#[using="HLlo HLhi"] Lemma art_rng_facts0 : ltac2:(TCodec.tc2 tcn__JatWrapCopy "W>'R3'R0%211'6':'B%2211%411&QI%611'S?yR0%211'9y8%511%311p051'K'>'5&Q0&Or1%211&Nr5%211%7241(;%;3:21'=&RC+VbTP0&S@r2%22I1%5241&RD&R6vS9%211%4261&@&Q?r;%221:%411&QF&R7%11:%311%D21@&RA&QA%2241%B2D1%J251%?11%L2<1%M2B1%N2H1p0Q01pW6QC1&R2r:r9r8r7r6%66N54321&R1&R5r<%22R91%45Q31:97&Q;%Q;2R2QF%211%>1Q<(3%11R2%QO3R231%Q811p061pUFR91z%QG21B&RG+2+Q8%3221%QL2G1%QN261%QN28R7%QI2R8L%R1221'A&QKvF%211%Q@2Q4R2%R6221&QJ%115%R3241%R;241&QCrAr@+R`0%47<QM32R21:%?261p0A1pV2S=1&QB%13Q;QBQA&QE%13R4QEQD&Q=&Q:r?r=%3221r>%6221&QO&RB+8%22QH1%R=241&RH%R?2:QK+1%3221%8217%RC2:1&R8rB%C21N%331@B%S72QGCr4%S?21R2r3%S;2R41%SC231%R>1S@(4&S>%12T8R0%32T81%T53T851p071pW<T>1p0>1'?%SG2R7Q1%92TC>%T511%;2TBSM%=2TB1%T?3TB31p061%TA3TOT=R>&RE%SA2Q=Q:%Q421Q2%321Q8%T321TB+7%T;2TD1%T=231%R<291%T?2;1qV4U:1%D2U;1+R0%TB2QH1%TD2Q61%UA1U5%U811&R;&R?%C2TNQH%QF2TO1%Q52U?1u8%645SG21%Q929TJ%U;3921%J2QAQO%QM2QB1%Q<2UF1%<4;SM17%Q?2?U<%UA3?21%U6271qW:B1%Q;2C1qW8D1%Q=2E1p0G1%TF2UDR;%U<21U3%TH2RARC+@%TJ221+Q?%SI2SH1%UB231%UD271%UE2:1%UF2Q51%UG2QK1%UH2R;1tV6VCR@1tUNVDRG1tR<V9RM1p0S51p0S81p0S;1p0T11p0T81p0T;1p0TF1p0TL1p0U41pV>VO1pV@W01pVHW11pV:VE1pR6VG1p2W21pQBW11pQ8W21pQ@W51pQ:W;1").
Proof.
intros G LB FF LK A M model sp p n LAZY CLI FS SHDEF Hp Hn CLS AACC APPR Mr0 f l.
pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
assert (D47 : p + n + 16 <= 2 ^ 47).
{ destruct APPR as (_ & _ & TOP). destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & _ & T16). clear - TOP T16. lia. }
assert (HSH : l + 8 <= rn_HI rn).
{ unfold l, Ja0RegionPoisoned.SB. assert ((p + n - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - D47; lia). change (2 ^ 47 / 8) with 17592186044416 in *. clear - H HI1. lia. }
destruct (Z_lt_le_dec 0 n) as [Np | Nz].
- destruct (art_rng_facts rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS SHDEF sp 2560 p n Hp Np ltac:(clear - Hn; lia) CLS AACC APPR)
as (VIS & _ & HZ & (kL & HL & HkL) & HW).
split; [exact VIS|]. split; [intros _; exact HZ|]. split; [exists kL; split; [intros _; exact HL | exact HkL]|]. split; [intros _; exact HW|]. split; assumption.
- split; [intros x Hx; exfalso; clear - Hx Nz; lia|]. split; [intros X; exfalso; clear - X Nz; lia|].
split; [exists 0; split; [intros X; exfalso; clear - X Nz; lia | left; reflexivity]|]. split; [intros X; exfalso; clear - X Nz; lia|]. split; assumption.
Qed.
#[using="Hwx AFL HLsegs HLlo HLhi HLroimg HLstimg HLlsan PRIVZ PRIVF PRIVCS FRB FRB_rng RUNX"] Theorem art_wrap_copy : ltac2:(TCodec.tc2 tcn__JatWrapCopy "Z2&Q1y5'S?yR0%211%5241'9y8%611%311p061'K'6':'B%2211%411&QI%611&Q>%81<&R=&S@&R9r=(S=+2(<%33K21%6251%82K1&R4'R0vQ4vQ9vQ6v1v2&R1vS9r;r:r9r8r7&QMr<%211%A?@?>=<;:987654H1'>%Q<1Q>&M%11L(3%11QB%63531'Q<r>%22@1rA+:%Q43QL1Q2%Q7231&S>%12QMF%@3QM31rB+<%Q;3R31Q9%Q>231%72R3K%F3R321'=&RCz%221Q1&RG+K%22QD1%62Q51%8251&QNrD+1%QK3RC1QI%QN231%511&QGvF&R7%11QC+R`0%5542:1QA&QBrE%231Q6QAr1%H2G1&RD%123Q:%L231&QDrF&RAr2%22Q>1%57B@4<QL?1p071pV2RN1'7%Q52Q46r3&RF%119%;231%Q:21QH'5&I&R?rKr4%B2Q71%QK2SG1%64541<(;%R<3921p0;1p0A1pV8C1pV2SC1(8'L%211%S=11&QEr@%23Q>R61+;%SA3T91S?%SD2D1%R=2T9R:%RL3T921rC%QB3H1R=%R72R6QN%Q:2QO3+Q?%R72SI1%R;231%R=251%@3QLQHR4%QE2QGQA%R@2QG1'A&QK%11R3rH%QF21QE%RE231&QJ%11R8%QO241%RJ241&QCrNrM%37R>R<21RDR;9%>251p0@1pV2TK1%U41TF&R;rOrG%S?2U;1&RI%11R:%64QK531(4%12TORE%T33:31rI%R?219%S>21K%RA2L;%S@214%Q1231%U42R<SN%SM2UIG%T<3UI21&Q@rQ6%221R8%RO2S1M%SJ2S11'?&R@%F1RF%23UNJ1%T82V0S7%F2V01%TH3V031+X0%S92S;1%T42S;1%T5241&QHrQ2%S921S1%33U51SA%T:251qW4V51%A2V61p0C1pV2V81+R0%T<2UN1%SG2SI1%TB2SI1rQ7%QI7T4T21MQGT1SD&@rQ3%TF21S@rQ1%SJ231%T02SC1%TK241%711%U62W2S=%UL11rQ;%113%UH3W031p061p0?1p0B1pUFVO1&RH%12R:TD%U721T@%T?2TAR<%U:221%UD2W@T;%V911%V01W=%V53W=21%J11p061pUFW;1&QLrQ8r6%3221rQ4%V721VCrQ9rQ5%VE1VG%W4?W3W2W1W0VOVNVMVL38Q8R42VI1'R>vS:(J&R:vROrQ=%WC21UF&R<%11TF%655W53W41%821W4%;4TI:1Q?p0=1p0B1p0E1p0J1p0Q71p0QO1p0RF1p0RJ1pV<X=1pR8X?1pRBXE1vS8%E5DQN1R=@%G21QM%J4U8I1SAp051p0S61p0S=1p0SI1p0T=1p0T?1p0TF1p0TI1p0TO1p0U31p0U81p0UN1p0V<1p0V@1p0VG1p0VN1p0W81p0W?1p0WG1p0WK1p0X31tVHY6XF1pQ<Y01pUHY21pV>Y91pVJY:1pULY;1p2Y:1pUJY81pQBY:1pQ8Y;1pQ@Y>1pV:YD1pR6YF1pR@YL1").
Proof.
intros R M model LB FF LK cr A dst src n bs K sp INV Hhalt HMI H10 H12 Hn Hret AST AACC CLW DOK KT0 APPR H11 AACCS (Hs0 & Hs47) APPRS CLSS RDS NOV CONT.
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
assert (OFFW : forall p, (forall i, 0 <= i < n -> hl_img_lo L <= p + i < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp 2560 (p + i)) ->
0 < n -> p + n <= sp - FRB \/ sp <= p).
{ intros p CL Hn0. destruct (art_rng_off_window p n (sp - 2560) sp Hn0 ltac:(lia)) as [X | X]; [|left; clear - X FRB_rng; lia | right; exact X].
intros i Hi. apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2560 (p + i) ltac:(lia) (CL i Hi)). }
assert (APPD : (dst + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= dst)) by exact (proj1 (proj2 APPR)).
set (FP := fun x => sp - FRB <= x < sp \/ dst <= x < dst + n).
pose proof (rdn_length _ _ _ _ _ RDS) as LEN.
assert (LENZ : Z.of_nat (length bs) = n) by (rewrite LEN, Z2Nat.id by (clear - Hn; lia); reflexivity).
destruct (art_rng_facts0 G LB FF LK A M model sp dst n LAZY CLI FS (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) Hd0 ltac:(clear - Hn; lia) CLS AACC APPR)
as (VISD & HZD & (kD & HLD & HkD) & HWD & HSHD & D47).
destruct (art_rng_facts0 G LB FF LK A M model sp src n LAZY CLI FS (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) Hs0 ltac:(clear - Hn; lia) CLSS AACCS APPRS)
as (VISS & HZS & (kS & HLS & HkS) & HWS & HSHS & S47).
apply (art_wrap_pure2 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx AFL K R pc0 M model G LB FF LK cr A FP
(fun R' pc1 Mr' => pc1 = getr R 1 /\ getr R' 10 = Z_to_bv 64 dst /\ keeps_cs R R'
/\ (forall i, 0 <= i < n -> Mr' (Z_to_bv 64 (dst + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))))
REPr FS B0 CRED CLI KN LZ EG).
-
assert (W0 : wrA Mr0 (sp - 2560) 2560).
{ apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 2560 ROK LZ ltac:(lia) ltac:(lia) ltac:(lia)). exact SWR. }
assert (HOK : store_ok ASEGS Mr0 (Z_to_bv 64 (sp - FRB)) (Z.to_nat FRB) = true).
{ replace (sp - FRB) with (sp - 2560 + (2560 - FRB)) by ring. apply W0; [clear - FRB_rng; lia | rewrite Z2Nat.id by (clear - FRB_rng; lia); clear - FRB_rng; lia]. }
destruct STAT as (_ & LAY & _ & _ & _ & _ & _ & S8).
assert (HGL : rt_layout_globs Mr0).
{ destruct LAY as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _). unfold rt_layout_globs. repeat split; [lit_cell A1 | lit_cell A2 | lit_cell A3 | lit_cell A4 | lit_cell A5 | lit_cell A6 | lit_cell A7 | lit_cell A8]. }
assert (C1 : cellA Mr0 0x1331a0 8 0x13b9d9) by conj_find S8.
assert (C2 : cellA Mr0 0x13b9d9 1 1) by conj_find S8.
assert (C3 : cellA Mr0 0x134640 8 0x1249ac) by conj_find S8.
assert (HIC : mc_icpt_globs Mr0).
{ unfold mc_icpt_globs. repeat split; [lit_cell C1 | rewrite <- le1_one; lit_cell C2 | lit_cell C3]. }
assert (HDST : store_ok ASEGS Mr0 (Z_to_bv 64 dst) (Z.to_nat n) = true).
{ apply (art_rng_store_ok A M model dst (Z.to_nat n) Hd0 ltac:(rewrite Z2Nat.id by (clear - Hn; lia); clear - D47 Hn; lia)).
- rewrite Z2Nat.id by (clear - Hn; lia). exact VISD.
- pose proof (DOK 0 (Z.to_nat n) ltac:(lia) ltac:(rewrite Z2Nat.id by (clear - Hn; lia); lia)) as X. rewrite Z.add_0_r in X. exact X. }
assert (HSRC : rdn ASEGS Mr0 (Z_to_bv 64 src) (Z.to_nat n) = Some bs).
{ apply (art_rng_rdn A M model src (Z.to_nat n) bs Hs0 ltac:(rewrite Z2Nat.id by (clear - Hn; lia); clear - S47 Hn; lia)); [|exact RDS].
rewrite Z2Nat.id by (clear - Hn; lia). exact VISS. }
assert (HSs : 0x1000000 <= sp - FRB /\ sp < 2 ^ 64) by (clear - SHI SLE STOP HI1 FRB_rng; lia).
destruct (RUNX Mr0 (getr R 2) (getr R 1) dst src n sp bs kS _ _ kD _ _ eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(clear - Hn; lia)
(art_rng_app8 rn LB FF LK A M CLI src n Hs0 ltac:(clear - Hn; lia) APPRS) (art_rng_app8 rn LB FF LK A M CLI dst n Hd0 ltac:(clear - Hn; lia) APPR)
HSs ltac:(clear - HSHS SHI FRB_rng; lia) ltac:(clear - HSHD SHI FRB_rng; lia) (OFFW src CLSS) (OFFW dst CLS) NOV HOK HDST HSRC Hret HGL HIC
HZS HLS HkS HWS HZD HLD HkD HWD R H10 H11 H12 eq_refl eq_refl)
as (R' & Mf & Mj & RUN & Q10 & KCS & GRr & OA & PW).
assert (FRr : forall x : word, ~ FP (U x) -> Mf x = Mr0 x).
{ intros x Hx. unfold FP in Hx. pose proof (u64_range x) as Rx. rewrite PW.
assert (E1 : wbytes Mj (Z_to_bv 64 dst) bs x = Mj x).
{ destruct (Z_lt_le_dec (U x) dst) as [Lt | Ge].
- apply wbytes_below; [rewrite LENZ, art_u_lit by (clear - Hd0 D47 Hn; lia); clear - D47 Hd0 Hn; lia | rewrite art_u_lit by (clear - Hd0 D47 Hn; lia); exact Lt].
- apply wbytes_above. rewrite LENZ, art_u_lit by (clear - Hd0 D47 Hn; lia). clear - Hx Ge. lia. }
rewrite E1. apply OA. clear - Hx. lia. }
exists R', (getr R 1), Mf. split; [exact RUN|]. split; [exact GRr|]. split; [exact FRr|].
split.
{ pose proof REPr as (_ & _ & (_ & _ & _ & _ & _ & _ & _ & CL) & _).
assert (GEOL : 0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x691000).
{ pose proof ROK as ROK'. rok_open ROK'. geo_open GEO. clear - Hloff Hloff' Hloff'' Htpd G1 G2 Espb G4. lia. }
apply (JatAllocG.cell_agree Mr0 Mf); [| clear - GEOL; lia | cbn; clear - GEOL; lia | exact CL].
intros x Hx. cbn in Hx. apply FRr. unfold FP. intros [X | X]; [clear - X Hx GEOL SHI HI1 FRB_rng; lia|].
apply (art_clientw_not_static rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLstimg sp 2560 (U x)).
- replace (U x) with (dst + (U x - dst)) by ring. apply CLW. clear - X. lia.
- unfold BIGSHADOW_LO. left. clear - Hx GEOL. lia.
- apply HLlsan. clear - Hx. lia. }
split; [reflexivity|]. split; [exact Q10|]. split; [exact KCS|].
intros i Hi. rewrite PW. rewrite (wbytes_inside _ Mj (Z_to_bv 64 dst) (Z_to_bv 64 (dst + i))).
+ rewrite !art_u_lit by (clear - Hd0 D47 Hi; lia). f_equal. f_equal. f_equal. ring.
+ rewrite LENZ, art_u_lit by (clear - Hd0 D47 Hn; lia). clear - D47 Hd0 Hn. lia.
+ rewrite LENZ, !art_u_lit by (clear - Hd0 D47 Hi; lia). clear - Hi. lia.
-
intros x [Hx | Hx] Z.
+ exfalso. pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)). clear - H Hx SHI FRB_rng. lia.
+ destruct (in_block_dec LB x) as [IB | NB]; [exact IB | exfalso].
apply (art_clientw_not_private rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLroimg sp 2560 x).
* replace x with (dst + (x - dst)) by ring. apply CLW. clear - Hx. lia.
* unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - APPD Hx. lia.
* exact (PRIVZ G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Z NB).
-
intros x [Hx | Hx] Z3.
+ exfalso. pose proof (art_fs_zone3_below rn G LB _ x REPr Z3). clear - H Hx SHI FRB_rng. lia.
+ destruct (in_fframe_dec FF x) as [IB | NB]; [exact IB | exfalso].
apply (art_clientw_not_private rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLroimg sp 2560 x).
* replace x with (dst + (x - dst)) by ring. apply CLW. clear - Hx. lia.
* unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - APPD Hx. lia.
* exact (PRIVF G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Z3 NB).
-
intros x [Hx | Hx] Zc.
+ pose proof (art_cs_zone_below rn G LB FF LK M Mr0 x REPr FS Zc). clear - H Hx SHI FRB_rng. lia.
+ apply (art_clientw_not_private rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLroimg sp 2560 x).
* replace x with (dst + (x - dst)) by ring. apply CLW. clear - Hx. lia.
* unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - APPD Hx. lia.
* exact (PRIVCS G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Zc).
-
intros b x Hb Hx [X | X].
+ pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx). clear - H X SHI HI1 FRB_rng. lia.
+ pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx) as B1. pose proof CLI as (CB & _). destruct (CB b Hb) as (K1 & _).
unfold in_shadow_of in Hx. pose proof (art_S_lo (fst b) ltac:(clear - K1; lia)) as B2. unfold BIGSHADOW_LO, BIGSHADOW_HI in APPD. clear - APPD X B1 B2 Hx. lia.
-
intros R' pc1 Mr' M1 model' (Epc & Q10 & KCS & BYTES) RI' GROW FR1 VIS1 HID RT MI'. subst pc1.
apply (CONT R' M1 model' Q10 (keeps_cs_preserved R R' KCS)); [ | | | exact RT | exact MI' | exact RI'].
+ intros i Hi. exists (U (nth (Z.to_nat i) bs (Z_to_bv 8 0))). split; [split|].
* rewrite Z_to_bv_bv_unsigned. apply nth_error_nth'. rewrite LEN. clear - Hi. lia.
* pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))) as Rg. unfold bv_modulus in Rg. change (2 ^ Z.of_N 8) with 256 in Rg. exact Rg.
* unfold byte_at. rewrite Z_to_bv_bv_unsigned. rewrite (VIS1 _ (VISD (Z_to_bv 64 (dst + i)) ltac:(rewrite art_u_lit by (clear - Hd0 D47 Hi; lia); clear - Hi; lia))). exact (BYTES i Hi).
+ intros a Ra Ha ND. apply FR1. rewrite art_u_lit by exact Ra. unfold FP. intros [X | X]; [|exact (ND X)].
apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2560 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X FRB_rng. lia.
+ intros a Ha. apply GROW.
assert (WM : wrA M (sp - 2560) 2560) by (intros d k Hd Hk; apply SWR; assumption).
pose proof (art_wr_wview ASEGS M (sp - 2560) 2560 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE STOP; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Ha SHI HI1 SLE STOP; lia). specialize (V ltac:(clear - Ha; lia)).
rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE STOP; lia); right; clear - Ha SHI HI1; lia). exact V.
Qed.
End WCP.
