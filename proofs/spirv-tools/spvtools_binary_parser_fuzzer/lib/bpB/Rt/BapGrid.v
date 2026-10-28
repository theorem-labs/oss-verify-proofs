(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BDecode.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BKInv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BapGrid () := "C46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4prod01C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeK47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes7reflect00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic3notK47Corelib4Init5Logic2or02C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes8list_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool02".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition GRID_M : Z := 2^35.
Definition GRID_J : Z := 2730.
Definition GRID_W : Z := 2^34.
Definition grid_floor : Z := 0x2aaaaaaab000.

Section Grid.
Variable E : list (word * word).
Variable S : Z.
Hypothesis HS : 0 < S <= GRID_W.
Hypothesis HE : forall e, In e E -> elo e < ehi e /\ ehi e - elo e <= GRID_W.

Definition slot (i : Z) : Z := grid_floor + i * GRID_M.

Definition cell (e : word * word) : Z := (elo e - grid_floor) / GRID_M.
Definition gslot (e : word * word) : Z :=
  let c := cell e in if elo e <? slot c + S then c else c + 1.

End Grid.

Lemma region_free_introZ : forall maps (a n : word),
  (forall e sz, In (e, sz) maps -> bv_unsigned a + bv_unsigned n <= bv_unsigned e \/ bv_unsigned e + bv_unsigned sz <= bv_unsigned a) ->
  region_free maps a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BapGrid ()) [] "p'0h01ah11eh21li001lh32szh41bi011bh51ni021nh61Hh74mapsh81ri031rh94__p1h:4__x1h;4__x2h<4__x3h=4__x4h>2n0h?2IHh@7__arithhA4__ffhB8__varmaphC5__withD2e0hE2l0hF2n1hG3sz0i042Ini052l'i061pp;1p;2p;4p;3p;7p;6p;5p;8p-1g0000R0p4p710p8g000Gj17Tg000lj1aTg001Jj1UTg001mR1j2PTg002MR2j1KTg002mj4;TP0j38Tg003Mj20Tg0047j21Tg004Tj29Tg0050j2<Tg005Jj3>Tg006Dj1LTg006dj2JTg007>j3ATg007^j4XTg008Wj15Tg0095j22Tg009Sj36Tg009mj3VTg00:Gj2HTg00:jj24Tg00;Fj2@Tg00;cR0j2GTg00<Fj2FTg00<dj1TTg00=Bj4ETg00=`j1RTg00>>j1QTg00>ij1OTg00?Nj2=Tg00@1j3DTg00@Tj4?Tg00A?j1NTg00Aaj7MTg00BEj6STg00Bij2`Tg00CKj2_Tg00D7j3^Tg00DVj4]Tg00EHj1ITg00Eaj3\Tg00F;j6YTg00FYj5ZTg00G;j7[Tg00G_j8WTg00HCR3f0R4g00HcR536p=:1245=635p=3f1R6g00ICR7g00IbR8P8g00JBR9P4g00JbF[p=Bf3R:P7P8P8P9f2R;P6P4GWp=Cg00KBR<#7R=#7R>#7#7#7#7#aR?#UR@/P@RA#KRBPAP@P@P6P4C;RCf4RD58A10?DRE10?:RF'110?;RG'910?6,1GRH/9E'<RI[^3@^1@A>:;6#:[^5@^0@RJX7B%LA98ACPI[^3@^1@1J35RKW6X5@X0@P1P@P@f6R1f5RL5AA98ACPI[^3@^1@AAALD?>;6#:[^5@^0@\J^2BP4P@P@f7RMP1C;=AAL98ACPI[^3@^1@P3P5P:P;PMP1CX#5RI/24#:X43P4P1PLP@P@P1PLC;RN=6ANp-0RO^2B^0AP2PAPOP4g00KgA6A6:PDP:P4O2'<n10110000020020101105X2BX0Ap?1001104PNPDO21JAN3VO310?1R2,9H10?LRH,12/9G'<10?MRG/12RP,HF14FP1@FP'Gf8RF,0?RQ/1GRG,@EP3P0f9RE,0?RR/1QRQ,4Hf;,0?RH/@PRS,26#5#3P6f:,0?/1RRR,42R21HHPRT14HP/GSRSf<,0?RP/@GRGP3P0f=,0?/4QRQ1256#5#3P6f>,0?/4RRRg00LDRUg00LbRV#L%KVPUPU1FUDP;%TUCEP61FU:CE%RU%QURVPU%O<,=URWg00MNRX1=U<R<1=U=5DUR=C?,BV%N8RYPVPUP<PX1=U>9DUWR>C?,BVPYPVPVP7P8P8P9PUP=g00N5R=PWC?,BVPUP>P=P<C?,BVFMPYPVP7P8P8P9P1ESCCCCCC1`V9P4P;PK1_4;#:dg00N\=^U6C]bAbBbCX:UX;UX<UW=X9O1146,4;11:D,4611;:/9D11DL/9;'<PM[[[^:U^;U^<U^=U^9OP4g00O:RO=635f?,0?f@,0?PHPPP6PLPEO8b@1255#5#3eWEP4O1%IRRLPK125O#5#3eW>P4O1n10210110300021110010102b4b8W2P4O1%I2PTPSPGP3P0PQ12O6#5#3P6PK12O5#5#3eX2RP4O1PK12OO#5#3eXFLP4O1n10210110300021010010102b4b8W>P4O1n10210110300021110011102b4b8%3Ieb6A>D;6P:P;P6A8AC1P:P;P6P@P@PEPFC;P@P@P;P6C;RF56AA8AFM;\4O3UX3@X1@O3EYAAAND?>;6#:eW6X5@X0@X?JX7BXG@XD@P6P4O2n2001106010121101101X0AP4DZW7o"). Qed.

