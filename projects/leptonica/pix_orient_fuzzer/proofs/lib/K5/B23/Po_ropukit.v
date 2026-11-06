(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Km_kit Bi_ropkit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Po_clipkit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_ropukit () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z8add_commC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08c69OSSVerify5KrLib2K53B23:Po_ropukit:land31_32qC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z7div_addC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03I46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr07K46Stdlib;setoid_ring<Ring_polynom5PExpr05K46Stdlib;setoid_ring<Ring_polynom5PExpr03I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00C56Stdlib6ZArith6BinInt1Z9mod_small".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac gc2 f a b := lazymatch isZcst a with true => lazymatch isZcst b with true =>
  let v := eval vm_compute in (f a b) in change (f a b) with v end end.
Ltac gc1 f a := lazymatch isZcst a with true => let v := eval vm_compute in (f a) in change (f a) with v end.
(* [comment removed for export] *)
Ltac gcalc1 := match goal with
  | |- context [Z.ltb ?a ?b] => idtac; gc2 Z.ltb a b
  | |- context [Z.eqb ?a ?b] => idtac; gc2 Z.eqb a b
  | |- context [Z.leb ?a ?b] => idtac; gc2 Z.leb a b
  | |- context [Z.b2z true] => change (Z.b2z true) with 1
  | |- context [Z.b2z false] => change (Z.b2z false) with 0
  | |- context [Z.land ?a ?b] => idtac; gc2 Z.land a b
  | |- context [Z.lor ?a ?b] => idtac; gc2 Z.lor a b
  | |- context [Z.lxor ?a ?b] => idtac; gc2 Z.lxor a b
  | |- context [Z.shiftr ?a ?b] => idtac; gc2 Z.shiftr a b
  | |- context [Z.shiftl ?a ?b] => idtac; gc2 Z.shiftl a b
  | |- context [Z.modulo ?a ?b] => idtac; gc2 Z.modulo a b
  | |- context [Z.div ?a ?b] => idtac; lazymatch b with 8%Z => fail | _ => gc2 Z.div a b end
  | |- context [Z.add ?a ?b] => idtac; gc2 Z.add a b
  | |- context [Z.sub ?a ?b] => idtac; gc2 Z.sub a b
  | |- context [Z.mul ?a ?b] => idtac; gc2 Z.mul a b
  | |- context [Z.opp ?a] => idtac; gc1 Z.opp a
  | |- context [bv_swrap ?n ?a] => idtac; gc1 (bv_swrap n) a
  | |- context [bv_wrap ?n ?a] => idtac; gc1 (bv_wrap n) a
  | |- context [?x + ?a + ?b] => idtac; lazymatch isZcst a with true => lazymatch isZcst b with true => rewrite <- (Z.add_assoc x a b) end end
  | |- context [?a + (?x + ?b)] => idtac; lazymatch isZcst a with true => lazymatch isZcst b with true => rewrite (Z.add_comm a (x + b)); rewrite <- (Z.add_assoc x b a) end end
  | |- context [?a + ?x] => idtac; lazymatch isZcst a with true => lazymatch isZcst x with false => rewrite (Z.add_comm a x) end end
  | |- context [?x + ?a - ?b] => idtac; lazymatch isZcst a with true => lazymatch isZcst b with true => rewrite <- (Z.add_sub_assoc x a b) end end
  end.
Ltac gcalc := repeat gcalc1; rewrite ?Z.add_0_r, ?Z.add_0_l, ?Z.sub_0_r.
(* [comment removed for export] *)
Lemma land31_32q : forall q c, 0 <= q -> 0 <= c -> Z.land (32 * q + c) 31 = c mod 32.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropukit ()) [] "h01zh17__arithh24__ffh38__varmaph45__with51Ch61Qh71ch81qp;2p;1p;3p;4p;6p;7g0000j2;Tg000Lj12Tg0011j15Tg001Oj27Tg001lj24Tg002Ij1LTg002nj2FTg003Kj20Tg003kj31Tg004Ej29Tg004_j1>Tg005?j1=Tg005_j1<Tg006=j1NTg006[j1MTg007Fj26Tg007ij4:Tg008Tj6KTg0098j2ETg009Zj2DTg00:Fj3CTg00:ej4BTg00;Wj4ATg00<8j63Tg00<Vj2@Tg00=8j2GTg00=Zj1HTg00>8j2?Tg00>Vj3ITg00?9j7JTf1R0g00?]R1g00@<R2P2g00@\R3f0R4g00A<FJp=8g00A\R5g00B:R6/;0R7P5g00BX#2R8#2#2#2#2#5R9f3R:'7R;f2R<'4R=%58%L8#5R8'F'010:9R>9154X05R?P514<;1049=15>X05P517:9R@14:4/09=15>X05P510<9R>P?195>14<@/09P<P:P9g00C=R@#>R>%=@R@%<5R?%N5RA%M5RBP1P2P2P3P51659g00Ci1656R2C:,8BEK1EB3R3P4P<g00DPR1g00E0RC'91D4<=11CdAC560CBR0b2b3b4A1596g00EP[P4b1CAE3P;1@9:E3P=1G;<E3%H8,?=P>P@P?PAP5P2g00Em1658C:,8BP3P0b2b3b41;68P4b19I=8E3X57W6X75W8o"). Qed.
Lemma land31_32q0 : forall q, 0 <= q -> Z.land (32 * q) 31 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropukit ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h51zh61Qh71qp;2p;1p;3p;4p;8p;6p;7g0000j23Tg000Lj10Tg0011j17Tg001Oj2<Tg001lj2NTg002Ij11Tg00>8j25Tg003kj32Tg003Kj2>Tg004Ej28Tg004_j1;Tg005?j1:Tg00FTj29Tg006=j1MTg006[j1LTg007Fj2KTg00G2j2DTg007ij46Tg00GUj1CTg00H7j8BTg0098j2ATg009Zj2@Tg00:Fj3?Tg00:ej4ETg005_j1FTg00H[j4GTg00<8j6HTg00I\j1=Tg00J=j6ITg00?9j7JTf1R0g00?]R1g00@<R2P2g00@\R3f0R4g00A<FJp=4g00A\R5g00B:R6/34R7P5g00BXR8#0#0#0#0#0#7R9/<0R:/N6R;%18#1#1#1#7R<,54=256X55P51>69A2546X55185615;<P0P6g00C=R<#;R;%:<R<1950%M5R9%L5R=P1P2P2P3P51K56R1g00EmR>1D58C6,4=R8%C2P8GB1A=3R3P4f2R8g00DPR2g00E0R?'81@48=22?dA?560CER?b1b2b3X451360\7^45P4P8P0O2b0P;P<%F5P9P5P1P>P1C6,4=P3P?b1b2b31366P4b0CGEHP:%=:EIW6W7o"). Qed.
Lemma div32_32q : forall q c, (32 * q + c) / 32 = q + c / 32.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropukit ()) [] "h01zh17__arithh24__ffh38__varmaph45__with54__x1h64__x2h76__sat0h81ch91qp;1p;2p;3p;4p;6p;7g000Lj13Tg0011j1NTg001Oj2:Tg001lj20Tg00JYj22Tg003kj31Tg00K6j2HTg0000j25Tg004_j1@Tg005?j1?Tg00FTj2>Tg005_j1=Tg00Kgj4<Tg006=j1MTg006[j1LTg00G2j2;Tg00LEj39Tg007ij47Tg0098j2GTg004Ej2DTg009Zj2CTg00:Fj3BTg00:ej4ATg007Fj28Tg008Tj6ETg00Lhj4FTg00<8j64Tg00<Vj2ITg00=8j2JTg00?9j7KTf1R0g00?]R1g00@<R2P2g00@\R3f0R4g00A<FKp=6g00A\R5P5g00BXR6#3R7#3#3#3#3#NR8/:0R9,041248R:f2R;1208'0R<515X05P51:08R=1004R>/28=15<X05P510:0A154<X051H48g00B:R</5415<812;8R:,5<[[g00C=R?#@R@%??R?P51>5;P0%=5RAC<%M5RB%L5RCP51;56R61;57R7595g00CiRDA9576C7'61GC3R7P4P;g00DPR6g00E0RE'D1C4;=16EdAB5<0CAREb2b3b4X55X651040=15>^55^65P4f3P:O2b1b7104=/28P4P0P8P@P?PAPBPCP1P2P2P3P51858PD185<C7,6CEEP7PEb2b3b4A158<g00EP[P4b1CFE4P91I80E410941J94E4X85W9o"). Qed.
Lemma div32_32q0 : forall q, (32 * q) / 32 = q.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropukit ()) [] "h01zh17__arithh24__ffh38__varmaph45__with51qp;1p;2p;3p;4p;7p;6g000Lj10Tg0011j1ETg001Oj23Tg00JYj24Tg003kj31Tg004Ej25Tg004_j1<Tg005?j1;Tg005_j1:Tg006=j18Tg006[j17Tg007Fj22Tg007ij49Tg00?9j7DTg008Tj6CTg0098j2BTg009Zj2=Tg00:Fj3>Tg00:ej4?Tg00MIj3@Tg00<8j66Tg00<Vj2ATg00A\R0P0f0R1g00BX#0#0#0#0#0#ER2'3R31412f1R4510X00P0P1A1014X0015011432g00C=R3#<%;3%:0%80%70R3g00?]R5g00@<R6P6g00@\R7P3P5P6P6P7P01202g00Cig00B:R6,20C9g00A<FDEC1B37P1f2R7g00DPR3g00E0R5'51=17=135dA>064C?b2b3b4A1026g00EP[P1b19@12E613211A21E6W5o"). Qed.
Ltac qnorm := rewrite ?land31_32q, ?land31_32q0, ?div32_32q, ?div32_32q0 by lia; rewrite ?(bv_wrap_small 32) by (change (bv_modulus 32) with (2^32); lia); gcalc.

Ltac cmpfix := repeat match goal with
  | |- context [?a <? ?b] => first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ]
  | |- context [?a <=? ?b] => first [ replace (a <=? b) with true by (symmetry; apply Z.leb_le; lia) | replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia) ]
  | |- context [?a =? ?b] => first [ replace (a =? b) with true by (symmetry; apply Z.eqb_eq; lia) | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; lia) ]
  end; change (Z.b2z true) with 1; change (Z.b2z false) with 0.

Ltac shfix := match goal with
  | |- context [Z_to_bv 64 (?c + SHB)] => lazymatch isZcst c with true => let x := eval vm_compute in (c * 8) in change (c + SHB) with (x / 8 + SHB) end
  | |- context [Z_to_bv 64 (SHB + ?c)] => lazymatch isZcst c with true => let x := eval vm_compute in (c * 8) in change (SHB + c) with (x / 8 + SHB) end
  end.

Ltac mod64fix := repeat match goal with |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by lia end.
Ltac anorm := rewrite ?(bv_wrap_small 32) by (change (bv_modulus 32) with (2^32); lia);
  rewrite ?div32_32q, ?div32_32q0; try rewrite !land31_32q by lia; try rewrite !land31_32q0 by lia; gcalc; cmpfix; gcalc; swrap32_fix; mod64fix.

(* [comment removed for export] *)
Ltac norm_coords :=
  repeat match goal with
  | |- context [(4 * ?q + ?r) * 8] => lazymatch isZcst r with true => let c := eval vm_compute in (8 * r) in replace ((4 * q + r) * 8) with (32 * q + c) in * by lia end
  | |- context [4 * ?q * 8] => replace (4 * q * 8) with (32 * q + 0) in * by lia
  end.
Ltac comb32 := repeat match goal with
  | |- context [32 * ?a + ?c + (32 * ?b + ?d)] => replace (32 * a + c + (32 * b + d)) with (32 * (a + b) + (c + d)) by lia
  | |- context [32 * ?a + (32 * ?b + ?d)] => replace (32 * a + (32 * b + d)) with (32 * (a + b) + d) by lia
  | |- context [32 * ?a + ?c + 32 * ?b] => replace (32 * a + c + 32 * b) with (32 * (a + b) + c) by lia
  end.
Ltac cur_mem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => k mm end.
Ltac maskrow_lit A :=
  let MI := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with H : mem_inv asegs mm |- _ => H end end in
  let bs := fresh "rowbs" in let L := fresh "RBL" in let ROW := fresh "ROW" in
  first [ assert_fails (idtac; lazymatch isZcst A with true => idtac end); fail 1 "maskrow_lit: not a literal" A
  | let k := eval vm_compute in ((A - 240256) / 4) in
    let ok := eval vm_compute in (andb (0 <=? k) (k <? 33)) in
    lazymatch ok with true =>
      destruct (mask_row _ 240256 k MI (or_intror eq_refl) ltac:(clear; lia)) as (bs & L & ROW); change (k * 4 + 240256) with A in ROW end
  | let k := eval vm_compute in ((A - 240448) / 4) in
    let ok := eval vm_compute in (andb (0 <=? k) (k <? 33)) in
    lazymatch ok with true =>
      destruct (mask_row _ 240448 k MI (or_introl eq_refl) ltac:(clear; lia)) as (bs & L & ROW); change (k * 4 + 240448) with A in ROW end ].
Ltac maskrow_auto := next_instr ltac:(fun i => lazymatch i with
  | Load SZ4 _ _ ?rs _ => reg_val rs ltac:(fun v => lazymatch v with Z_to_bv 64 ?A => maskrow_lit A end) end).
Ltac opaque_auto := repeat match goal with |- context [sext 64 (bv_extract 0 32 (le_bytes_to_word ?bs))] =>
   let w := fresh "mw" in set (w := sext 64 (bv_extract 0 32 (le_bytes_to_word bs))) in *; clearbody w end.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => idtac end.
Ltac pre_norm := norm_coords; comb32; anorm; opaque_auto.

(* [comment removed for export] *)
Lemma rows_fit : forall SR sn PS swpl dh len sy h w0, 0 < swpl -> 0 <= sy -> 0 <= w0 -> 0 <= dh -> sy + dh <= h -> sn = 4 * (swpl * h) ->
  PS = SR + sy * swpl * 4 + w0 * 4 -> w0 * 4 + len <= swpl * 4 ->
  forall i', 0 <= i' < dh -> SR <= PS + 4 * (swpl * i') /\ PS + 4 * (swpl * i') + len <= SR + sn.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropukit ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with54__x2h64__x3h74__x4h84__p1h94__x5h:1Ch;2PSh<4__x6h=4__x7h>2snh?1Ah@1BhA2DHhB3EPShC3ESNhD1HhE3Hi'hF2SRhG2SWhH2SYhI3SYHhJ2W0hK2WLhL2dhhM7fv_listhN1hhO8hyp_listhP2i'hQ3lenhR3lmphS4swplhT2syhU2w0hV1zp;2p;1p;3p;4p;5p;7p;6p;8p;:p;<g00Mjj2DTg000Lj1HTg0011j1\Tg001OR0j20Tg003kj3CTg00NFj2BTg001lR1j26Tg0000j25Tg004_j1RTg005?j1GTg006=j1wTg006[j1pTg007Fj2PTg00G2j2YTg00GUj1gTg0098j2bTg004Ej2aTg009Zj2`Tg00:Fj3_Tg00:ej4^Tg00Naj4UTg00OLj1ATg00Okj2>Tg00PTj2ITg00Q@j3@Tg005_j1]Tg002Ij1TTg00Q`j5xTg00RNj3[Tg00S7j2vTg00Scj1uTg00TMj2QTg00Tmj2KTg00UWj3LTg00VAj3ETg00Vkj2oTg00WUj1mTg00X=j4lTg00Xcj7iTg00<8j6NTg00YRj2hTg00Z;j4jTg00FTj2kTg007ij4STg00?9j7MTg00H7j8ZTg00ZVj6fTg00[:j7eTg00[^j3dTg00Kgj4cTg00LEj3qTg00\Gj3rTg00\jl:sTg00][l<tTg00B:R2f0R3'5p=4f2R4f1R5'6/53p=31645/63p=11053,64p=<g00A\R6/k3p=;P6P5g00^HP3CSp=OP4g00?]R7g00@<R8P8g00@\R9P6P5g00EmR:P3CSg00A<R;FMp=Ff4R<P7P8P8P9f3R=P7P8P8P9P4P;FMP5P3GZp=9P5P7P8P8P9P3Efp=WP4P7P8P8P9P5P3Fep=VP=P7P8P8P9P4P5P3GZp=JAd653p=:P6P4P5P3Ccp=81Y63p==P5P7P8P8P9P3P;FMp=yAq653p=2P6P5P:P3CSp=?Ar653p=7P6P2P5P1P0g00^oR:g00_LR;g00_iR7g00`FR>P3M:sp=nP6P2P4P1P0P:P;P7P>g00`gR>P5P3M<tp=Xf5R;,D2R:%4=R0%44f7R1#4f6R?f8R@;3;f<RAg00BXRB#HRC#HRD#\REf:RF/0?'05C6f>RGf;RH,0@/0E10?E319C6A101ERI10AE73F%43RJf=RK,D3'BP6fBRLf?RM,0A/0E10FE31fCRNf@RO/04,0ERP,63RQ'516NL93QG'BX;6P610MH,0E10KORQ=<NE10HE;1PRP,5N16N393PG'BX>6PMP5g00C=RP#RRR%GPRS%;5RT%w6RU%p6RVPV1P62RW1Y6BRX'O%g8R8AFVWXRYD91bV9R9P3P4g00DPRZg00E0R['aR\1`34=CZ[dA_625C^R]b2b3b4X06R^1D23%45R2[^06R_P3POPFO2b1p-0R`PRPSPTPUPV1WV=9VVYP8PYCJP9P]b2b3b4X06W81BJ5P2[^06^8`P31D4MP4P5O3b1CU10M5#4PKPOPRPSPTPUPVPYP8PYCJP9P]b2b3b4X06P2\J^06P3PGPFO2b1P^P_P3fARFPHO2b1CU%4Q%\BRQ91G=RJPKPFP^P_P3PLPAO2b1g00aVR_#AR^#AR2,>6RY1>6^1>6_R_':R^':g00b5RT'I=@PRPS%]6Ra%;<Rb784%;=785PUPV1WV?%=CRc%TBRd#H#=Re'O,yV5VVP8PVPV12Xe%=dRf'?P812Xc1P6Q'2=FVfD9CJP9P]b2b3b4X06X56X66X76X8`1D5=,B<A35<=164=?3Q<[[^06^56^66^76^8`P3%4<R`PFPGP<PMP=P@O7b1Dx10FJ10FK'5fERJ10MLRg=<JE10KE10L<Rh,0E31Ri'510LG9<JE93iO%A2R2,>6Ri=[6Y%A2R2#A,>61>62/:i':':,:_/IT,v_=@PRPSA8b4a%;;R_?8=a785PUPVPV%TC#=,7fRa,?WP8PVPV%=DRD,?WP8PVPV1?WcP8PVPV1OWfP817cfRc1P6ERW'7,2X17DWRD'217Wa'2Ri9FVXD9D9D9D9P9P]b2b3b4X06X56X66X76X96104<R2#410;?=<<E10?@,0E71I,5<\:\0\`[^06^56^66^76^96P3P;PGPNPOfFP=PHPAPKO9b1%u6RK/QKRK#R%GK%R69@6;9@6N9@6O%G6P>P3P51K6BRB1K6CRC5L61K6dR>9L6C5E6=E6CRKAE6B>1o6Q5E69L6CRCg00baP\1nQ5g00c=,Q6%m6'Q#GP6P7AXQ3KAXQ3CClbR=CZ[dFibMbOA1ghLA1M<Q,0L5C6RhePhP6A1O;Q,0NfD/0O,53XV6P510ON10N;;1NRQP3EN10NM,5Q1h6E=[6Y/:^/IT=@PRPS%;?98b4%;198_=785PUPVPV12ca/2f%Td#=,7fRd'?P8PVPV12De17fW'?P812ie17Wd,2X5FVD9D9P9P]b2b3b4X06X56X66X76X96X<6X=61054/62104?73410<E10=E73?10=<=<4E10;E10<?,0E3110<@9<4E731[[^06^56^66^76^96^<6^=6P3PFPNP1POPJPLfHP5P@O9b1b:bDCjb:b@b?PFP<ENPOP=ENWEXP6WKWBWCWIWAWJWHWGXU6XN6XT6XQ6XL6XS6X;6X>6XF6o"). Qed.

Lemma rows_fit' : forall SR sn PS swpl dh len sy h, 0 < swpl -> 0 <= sy -> 0 <= dh -> sy + dh <= h -> sn = 4 * (swpl * h) ->
  SR + sy * swpl * 4 <= PS -> PS + len <= SR + sy * swpl * 4 + swpl * 4 ->
  forall i', 0 <= i' < dh -> SR <= PS + 4 * (swpl * i') /\ PS + 4 * (swpl * i') + len <= SR + sn.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropukit ()) [] "h04__x1h17__arithh24__ffh34__p1h48__varmaph55__with64__x2h74__x3h84__x4h94__x5h:1Ch;4__x6h<4__x7h=2snh>1Ah?1Bh@2DHhA3ESNhB1HhC2HIhD3Hi'hE2LOhF2PShG2SRhH2SWhI2SYhJ3SYHhK2dhhL7fv_listhM1hhN8hyp_listhO2i'hP3lenhQ3lmphR4swplhS2syhT1zp;2p;1p;3p;4p;5p;7p;6p;8p;:p;<g00Mjj2;Tg000Lj1HTg0011j1ZTg001OR0j20Tg003kj3FTg00NFj2ATg0000j25Tg001lR1j2=Tg004_j1ITg005?j1GTg006=j1tTg006[j1rTg007Fj2OTg00G2j2XTg00GUj1eTg0098j2`Tg004Ej2_Tg009Zj2^Tg00:Fj3]Tg00:ej4\Tg00Naj4TTg00OLj1DTg00Okj2BTg00PTj2JTg00Q@j3@Tg005_j1[Tg002Ij1STg00Q`j5vTg00YRj2uTg00RNj3CTg00Scj1sTg00TMj2QTg00Tmj2MTg00UWj3PTg00VAj3ETg00Vkj2qTg00WUj1oTg00X=j4jTg00Xcj7iTg00<8j6WTg00Z;j4hTg00FTj2gTg007ij4VTg00?9j7UTg00H7j8fTg00ZVj6kTg00[:j7lTg00[^j3mTg00Kgj4nTg00LEj3dTg00\Gj3cTg00\jl:bTg00][l<aTg00B:R2f0R3'5p=7f2R4f1R5'=/53p=61=45/=3p=91053,=4p=:g00A\R6/g3p=?P6P5g00^HP3CVp=NP5g00?]R7g00@<R8P8g00@\R9P3g00A<R:FUp=RP4P7P8P8P9P6P5g00EmP3CVP:FUp=4f3R:P7P8P8P9P4P5P3Gfp=3P5P7P8P8P9P3Ekp=LP4P7P8P8P9P5P3Flp=KAm653p=<P6P4P5P3Cnp=81X63p=>Ad653p=1Ac653p=2P6P2P5P1P0g00^oR7g00_LR;g00_iR<g00`FR=P3M:bp=pP6P2P4P1P0P7P;P<P=g00`gR=P5P3M<ap=Yf4R;,;2%74f5R7#7f6R0=6;:f:R1g00BXR>#HR?#HR@#ZRAf8RB/0;'05F6f<RCf9RD,00/0A;61f;REf=RFf7RG/01/0A101A3976B%73RH1;3E'AP610FD,0AfARIf?RJf>RK/047:ARL'51=I396LC'AX=6PFP5g00C=RL#IRM%GLRN%?5RO%t6RP%r6RQ1O62RR1X6>RS'N,RQ%e8R8A4QRSRTC31`Q9R9P3P4g00DPRUg00E0RV'_RW1^34=FUVdA]625C\RXb2b4b5X06RY1;23%75RZ[^06R[P3PKPDO2b1p-0R\PMPNPOPPPQ1LQ:9KQTP8PTC3P9PXb2b4b5X06W31AH5PZ[^06^3\P31;4FP4P5O3b1CT10F5#7PEPKPMPNPOPPPQPTP8PTC3P9PXb2b4b5X06PZ\H^06P3PCPDO2b1PYP[P3PJP1O2b1CT10EK#7%Z>R199C:RDPEPJPYP[P3f@R[PEO2b1g00aVRY#DRH#DRZ,B6RT1B6HRH1B6YRY'<RO'<g00b5R]'J=@LMPN%?4%?;R^%[6R_78:785PPPQ1LQ0%>?R`%S?#>Ra'N,RQ5KQP8PQ11Sa%S>Rb#>Rc54QP811S`1O61'1=4QcC3C3P9PXb2b4b5X06X66X76X86X3\1;5:,A;1=5;Rd/5:1=4:?61;[[^06^66^76^86^3\P3%7;RePJPCP;PFP:PBO7b1Dv10JD10JE'5fCRE10[;RD9:IARf'510[C9:EA96fK1u6ARf%DZRZ,B6Rg=C6H5C6%DZ,B69C6fAC6fg1<TY'<'<'</J]=@LMPNA8^4_%?7RY?8:_785PPPQ12acR_94QRP8PQ%>@R@94QR1LQG5KQP8PQ1O6ARg,2_,1S=4Q`P8PQ1NRc,RQP812c@,2g,1`94QSC3C3C3C3P9PXb2b4b5X06X66X76X86X96X3\10;4#71Ae0100;/0A=64:1;27100G9:7A,5;[[[[^06^66^76^86^96^3\P31;7[PKP7PIfBR\fDR2P4P;PGPCO:b1%s6RC/QCRC#I%GC%I69@679@6I9@6K%G6P=P3P51M6>R>1M6?R?5P61M6bR=9P6?5E6=E6?RCAE6>=1q615E69P6?R?g00baPW1p15g00c=,Q6%o6'Q#GP6P<AY13CAY13?CjbQ=FUVdFibLbN10F[?9D[A9F;1,0[5F6RDePDP6A9K71,0I10\K,53XT6P510KI10I7;9IRKP3EW10IF,5KAC6fT/<O/J]=@LMPN%?098^4%?G98Y:785PPPQ%Sb#>/2`RP12`cRc'1/1`%Hb#>,2`Rb54QP8PQ11S@12Pg,1a12`g'154QP812gc,1S/1@12gb,1a54QC3C3P9PXb2b4b5X06X66X76X86X96X;6X<61005?:54105776510G4/0A104A597,5d10:;9:4A10:G9:0A767[[^06^66^76^86^96^;6^<6P3P[PJfFPIPGPEP2P5PBO9b1b:bBChb:b?b>PJP;EWWDXO6WCWEWAWJW@WIWHXM6XS6XP6XK6XR6XF6X=6XG6o"). Qed.

(* [comment removed for export] *)
Lemma zext32x4 : forall x, 0 <= x < 4294967296 -> (x * 4294967296) mod 18446744073709551616 / 1073741824 = x * 4.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropukit ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh61Hh72Hxh81xp;2p;1p;3p;4p;6p;8p;7g0000j2DTg0011j17Tg00Mjj2@Tg00NFj2?Tg001Oj21Tg00JYj2<Tg003kj33Tg004_j1ITg005?j1GTg00FTj2FTg006=j1]Tg006[j1WTg00G2j2VTg007Fj26Tg00\Gj3:Tg007ij45Tg0098j2UTg004Ej2BTg009Zj2STg00:Fj3RTg00:ej4PTg005_j1NTg008Tj6MTg00MIj3LTg00<8j6;Tg00J=j6JTg003Kj2KTg00YRj2HTg00OLj19Tg00Okj28Tg00RNj3OTg00[^j3=Tg00PTj2>Tg00S7j2QTg00Q@j3CTg00GUj1\Tg00H7j8[Tg00cej3ZTg000Lj10Tg00?9j7XTg00[:j7YTf0R0#0#0p=E%00#0#0#0p=T%00#0#0#0#0#0#0#0p=2f1R1g00?]R2g00@<R3P3g00@\R4P0g00A<FXp=4f2R5P2P3P3P4P1P0FYp=Ag00A\R6g00B:R7/D0g00BXR8#ER9#T#2#2#2R:#ER;#7R<,@0'?R=P6111<R>%7:R:,<0R?%79R9,15R@536X56g00C=RA#IRB%GARC1F61RD%]6RE%W6RFP61V68R816695:6166:RG5:6g00CiRH166<RI9:68RJC5'41UF4RKP0P5g00DPRLg00E0RM'B1S05=3LMdAR671CPRMb2b3b4X061109/1:110<536^06P0P5O1b11119/1:=36>P611@:RLf3/19R9936?X56P6P@A3609X561B6@1<L:PBPC%N6PEPFP2P3P3P4P6PGPH1667RHC5,4FEMPKPMb2b3b4A36:7g00EP[P0b19L@:E;115<P0EJb6%2;#2#2#2#7R;,K>1H6<g00aVR<#9R@,865O6186<R<5=6g00b5R:'>%9@#9,869=6</>:,Q<=CAB5CAPCPDPEPFP2P3P3P4P6PHg00EmR4P8C5,4FP6P8g00^HR8PIC5,4F5AF%\3P6PHP4PJC5,4FP6PJP8166;C5,4F5AFG[PKPMb2b3b4X061D7>1@>;'?\=^06P0P5P1O2b19Z>;E;W7W8o"). Qed.
Lemma x4_30 : forall x, (x * 4294967296) / 1073741824 = x * 4.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropukit ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h51zh61Hh71xp;1p;2p;3p;4p;6p;7g004_j1KTg005?j1JTg00FTj2?Tg006=j1<Tg006[j1ITg00G2j2CTg0011j16Tg007Fj24Tg00\Gj35Tg007ij47Tg0098j2HTg004Ej2;Tg009Zj2FTg003kj33Tg00:Fj3BTg00:ej4ATg001Oj21Tg00JYj28Tg005_j1@Tg008Tj6>Tg00MIj3DTg00<8j6ETg00J=j6=Tg000Lj12Tg00?9j7GTf0R0#2#2p=:%20#2#2#2p=0f1R1g00?]R2g00@<R3P3g00@\R4P0g00A<FGp=9g00A\R5g00C=R6#KR7%J6R61?51%<5R8%I5R9P5g00BXR:,C5R;%::R:#6R<,45555%0:#0#0#0#0#0#0R:#6R=,45R>555g00CiR?%::#6R:,45955;C7'91H94R;P0f2R@g00DPRAg00E0RB';1F0@=3ABdg00B:RB=B51CARAb1b2b3X45110</1=110:535RC^45P0P1O1b0PCP5111<RC/1=RD180=11@<R@535X55P5PCA350@X551;5C18D=P7P6%@5P8P9P2P3P3P4P5P>P?145BC7,99E>P;PAb1b2b3A35=Bg00EP[P0b09DC=EE111:P0E=b6W7o"). Qed.
Lemma zext32 : forall x, (x * 4294967296) / 4294967296 = x.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropukit ()) [] "h07__arithh14__ffh28__varmaph35__with41xh51zp;3p;2p;1p;4p;7p;6g003kj32Tg004Ej24Tg0011j15Tg001Oj2ETg00JYj2<Tg004_j1;Tg005?j19Tg005_j18Tg006=j16Tg006[j17Tg007Fj23Tg007ij4:Tg00?9j7DTg008Tj6CTg0098j2BTg009Zj2=Tg00:Fj3>Tg00:ej4?Tg00MIj3@Tg00<8j6ATg000Lj11Tf0R0#1#1#1#1p=0g00A\R1P1P0f1R29210X511410g00BX#0#0#0#0#0#0#0#0#5R3,E0/<3g00C=R4#;%94%81%61%71R4g00?]R5g00@<R6P6g00@\R7P4P5P6P6P7P11313g00Cig00B:R6,31C:g00A<FDEC1B47P0f2R7g00DPR4g00E0R5'41=07=245dA>162C?b1b2b3A2136g00EP[P0b09@03EAW4o"). Qed.

Ltac uwalk stops := repeat (tryif at_stop stops then fail else
  first [ lwalk1 | shfix; lwalk1 | maskrow_auto; lwalk1 | progress pre_norm ]).
Ltac unorm1 := match goal with
  | |- context [(?x * 4294967296) mod 18446744073709551616 / 1073741824] => rewrite (zext32x4 x) by lia
  | |- context [(?x * 4294967296) / 1073741824] => rewrite (x4_30 x)
  | |- context [(?x * 4294967296) / 4294967296] => rewrite (zext32 x)
  end.
Ltac unorm := pre_norm; repeat unorm1; pre_norm.

