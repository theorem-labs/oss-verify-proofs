(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AgentLib Ja0DefsK Ja0PlanImagesK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require FxHexScan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0BssZeroK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "Corelib.Strings.PrimString."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0BssZeroK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1list"; "1nat"; "1option"; "1true"; "2and"; "2eq"; "3repeat"; "4N"; "4Z"; "5string"; "6hex_byte_at"; "0M"; "7DEP_HI"]; ["7DEP_LO"; "7zscanN"; "8ASEGS0"; "9rdn"; "9seg_rom"; ":Asan_seg_bytes_003"; ";add"; ";lt"; "<add"; "<le"; "<lt"; "<of_nat"; "0a"; "0base"; "0fuel"; "0i"]; ["0n"; "0s"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0x"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Definition byte_zero (s : PrimString.string) (off : N) : bool :=
match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.
Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
match fuel with
| O => N.eqb n 0
| S f =>
if N.eqb n 0 then true
else if N.eqb n 1 then byte_zero s base
else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool
end.
Lemma zscanN_sound : ltac2:(TCodec.tc2 tcn__Ja0BssZeroK "Q7&<'4':'8'2&Ar4r3r2r1%544321(6%93821&G%1257'5'Q3y8%211%411&=r7&Fr5%221@%5241(1&Q2z%22<1%42<1%L3<61p0B1pR0O1p0F1pR2Q11pQLQ21pQNQ41pR4Q61").
Proof.
intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
- apply N.eqb_eq in H. lia.
- destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
destruct (N.eqb_spec n 1) as [E1|Hn1].
+ subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_zero in H.
destruct (hex_byte_at s base) as [b|]; [|discriminate]. apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H. reflexivity.
+ apply andb_prop in H as [H1 H2].
rewrite N.div2_div in *.
set (h := (n / 2)%N) in *.
destruct (N.lt_ge_cases i h) as [Hl|Hge].
* exact (IH _ _ H1 i Hl).
* specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.
Definition DEP_LO : Z := 0x21cbd8.
Definition DEP_HI : Z := 0x61cbd8.
Lemma as0_dep_zscan : ltac2:(TCodec.tc2 tcn__Ja0BssZeroK ":'8'2&A&EuR0ymRnHyTPPP0%544321(6%93821").
Proof. apply (FxHexScan.FXH.zscan_ok zscanN byte_zero (fun _ _ _ _ => eq_refl) (fun _ _ H => H)); [vm_cast_no_check (@eq_refl bool true)|vm_compute; discriminate]. Qed.
Open Scope Z_scope.
Lemma as0_dep_rom_zero : ltac2:(TCodec.tc2 tcn__Ja0BssZeroK "N';'7&I&@r1%3221&J&?%2241%8241'8'5'Q3y8%211%411&D&B&Q2yR0r2%3221%6251(1z%72<1%32<1%A3<51p0C1pQJM1").
Proof.
intros a Ha. unfold DEP_LO, DEP_HI in Ha. unfold seg_rom, memory_read. rewrite u64_lit by lia.
rewrite asan0_segs_eq. cbn [find_segment].
cbn [seg_base seg_size Asan_segment_000 Asan_segment_001 Asan_segment_002 Asan_segment_003].
replace (Z.leb (Z.of_N 65536) a && Z.leb (a + Z.of_N 1) (Z.of_N 65536 + Z.of_N 262144))%bool with false
by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace (Z.leb (Z.of_N 327680) a && Z.leb (a + Z.of_N 1) (Z.of_N 327680 + Z.of_N 901120))%bool with false
by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace (Z.leb (Z.of_N 1228800) a && Z.leb (a + Z.of_N 1) (Z.of_N 1228800 + Z.of_N 32768))%bool with false
by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace (Z.leb (Z.of_N 1261568) a && Z.leb (a + Z.of_N 1) (Z.of_N 1261568 + Z.of_N 5623808))%bool with true
by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
assert (Hr : seg_readable Asan_segment_003 = true) by (vm_compute; reflexivity).
rewrite Hr. cbn [seg_bytes seg_base Asan_segment_003].
change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at].
rewrite asan0_len3.
replace (Z.to_N (a - Z.of_N 1261568) <? 5623808)%N with true by (symmetry; apply N.ltb_lt; lia).
pose proof (zscanN_sound _ _ _ _ as0_dep_zscan (Z.to_N (a - 0x21cbd8)) ltac:(lia)) as Hz.
replace (0xe8bd8 + Z.to_N (a - 0x21cbd8))%N with (Z.to_N (a - Z.of_N 1261568)) in Hz by lia.
rewrite Hz. reflexivity.
Qed.
Lemma as0_dep_rdn_zero : ltac2:(TCodec.tc2 tcn__Ja0BssZeroK "QO'Q3yR0%211'5y8%511%311p051'4';&I&@r1%3221&Hr2&Kr3%211%5241&?%;221'7r4&Q4%12H=%@231&Jr5%=11%@271%4261%:261'8r7%11D(0%11Q0%53Q031p071pR<Q61'3%11Q5%Q811&C&Br6&Q2%12Q?I%54431E(1&9z%62QA1%33QA1J%52=1%G3=71p0A1p0Q51p0Q>1pQJQC1pR2QE1pNQG1").
Proof.
intros M n. induction n as [|n IH]; intros a Ha Hb HM; [reflexivity|].
assert (Hr : DEP_LO <= a < DEP_HI) by lia. unfold DEP_LO, DEP_HI in Ha, Hb.
cbn [rdn repeat]. rewrite (HM (Z_to_bv 64 a)) by (rewrite u64_lit by lia; lia). rewrite (as0_dep_rom_zero a Hr).
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
- rewrite IH; [reflexivity | unfold DEP_LO; lia | unfold DEP_HI; lia | intros x Hx; apply HM; lia].
- apply bv_eq. rewrite bv_add_unsigned, !u64_lit by lia. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
change (bv_unsigned (1 : word)) with 1. rewrite Z.mod_small by lia. reflexivity.
Qed.
