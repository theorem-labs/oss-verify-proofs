(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac As0StepLib As0Tables.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatClassId () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatClassId.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bv_eqb"; "4bvmap"; "0M"; "5class_id"; "5zrange"; "6msteps"; "7art_cid_kept"; "7art_cid_w"]; ["7art_cid_z"; "7art_zr8"; "8getr"; "8mkst"; "9loaded_segments"; ":forallb"; ";add"; ";eqb"; ";le"; ";lt"; ";modulo"; "0f"; "0fx"; "0g"; "0lo"; "0n"]; ["0r"; "0regs"; "0regs'"; "0rom"; "0s"; "<BV"; "<Z_to_bv"; "<bv"; "<bv_unsigned"; "0z"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Open Scope bv_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Lemma art_brute_eq : ltac2:(TCodec.tc2 tcn__JatClassId "Q;'7'Q7yR0%211p041'5'0&E&8r5r1%211r4%113%63<31qRD?1&<r2%2218%<3C41(2%@3?21'4&H%12<>&I&Fr3%22@1%42C1%8261r7%11?r6%11A%N3Q031p061pRDQ51p0A1pR0Q71pQNQ81pQLQ51pQHQ61").
Proof.
intros f g lo n H z Hz. rewrite forallb_forall in H.
assert (Hin : In z (AsanTab.zrange lo n)) by (unfold AsanTab.zrange; apply AsanTab.in_ziota; rewrite Z2Nat.id; lia).
specialize (H z Hin). cbn beta in H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.
Ltac art_step F D :=
stepn F D;
try (lazymatch goal with
| |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ =>
lazymatch v with
| Z_to_bv 64 ?z => is_Z_lit z
| _ => let x := fresh "x" in remember v as x
end
end).
Section FPX. Context {fx : PropExec.FPState}.
Definition art_cid_w (s : word) : word :=
let x1 := (v_srli s (1)%Z) in
let x2 := (v_or s x1) in
let x3 := (v_srli x2 (2)%Z) in
let x4 := (v_or x2 x3) in
let x5 := (v_srli x4 (4)%Z) in
let x6 := (v_or x4 x5) in
let x7 := (v_srli x6 (8)%Z) in
let x8 := (v_or x6 x7) in
let x9 := (v_srli x8 (16)%Z) in
let x10 := (v_or x8 x9) in
let x11 := (v_srli x10 (32)%Z) in
let x12 := (v_or x10 x11) in
let x13 := (v_xori x12 (-1)%Z) in
let x14 := (v_srli x13 (1)%Z) in
let x15 := (v_and x14 (Z_to_bv 64 6148914691236517205)) in
let x16 := (v_sub x13 x15) in
let x17 := (v_and x16 (Z_to_bv 64 3689348814741910323)) in
let x18 := (v_srli x16 (2)%Z) in
let x19 := (v_and x18 (Z_to_bv 64 3689348814741910323)) in
let x20 := (v_add x17 x19) in
let x21 := (v_srli x20 (4)%Z) in
let x22 := (v_add x20 x21) in
let x23 := (v_and x22 (Z_to_bv 64 1085102592571150095)) in
let x24 := (v_mul x23 (Z_to_bv 64 72340172838076673)) in
let x25 := (v_srli x24 (56)%Z) in
let x26 := (v_subw (Z_to_bv 64 62) x25) in
let x27 := (v_slli x25 (1)%Z) in
let x28 := (v_srl s x26) in
let x29 := (v_sllw (Z_to_bv 64 18446744073709551615) x26) in
let x30 := (v_xori x27 (126)%Z) in
let x31 := (v_andi x28 (1)%Z) in
let x32 := (v_xori x29 (-1)%Z) in
let x33 := (v_and s x32) in
let x34 := (v_or x30 x31) in
let x35 := (v_sltu (Z_to_bv 64 0) x33) in
let x36 := (v_add x34 x35) in
let x37 := (v_addi x36 (-2)%Z) in
x37.
Definition art_cid_z (u : Z) : Z :=
let y1 := ((Z.shiftr u 1) mod 18446744073709551616) in
let y2 := ((Z.lor u y1) mod 18446744073709551616) in
let y3 := ((Z.shiftr y2 2) mod 18446744073709551616) in
let y4 := ((Z.lor y2 y3) mod 18446744073709551616) in
let y5 := ((Z.shiftr y4 4) mod 18446744073709551616) in
let y6 := ((Z.lor y4 y5) mod 18446744073709551616) in
let y7 := ((Z.shiftr y6 8) mod 18446744073709551616) in
let y8 := ((Z.lor y6 y7) mod 18446744073709551616) in
let y9 := ((Z.shiftr y8 16) mod 18446744073709551616) in
let y10 := ((Z.lor y8 y9) mod 18446744073709551616) in
let y11 := ((Z.shiftr y10 32) mod 18446744073709551616) in
let y12 := ((Z.lor y10 y11) mod 18446744073709551616) in
let y13 := ((Z.lxor y12 ((-1) mod 18446744073709551616)) mod 18446744073709551616) in
let y14 := ((Z.shiftr y13 1) mod 18446744073709551616) in
let y15 := ((Z.land y14 (6148914691236517205 mod 18446744073709551616)) mod 18446744073709551616) in
let y16 := ((y13 - y15) mod 18446744073709551616) in
let y17 := ((Z.land y16 (3689348814741910323 mod 18446744073709551616)) mod 18446744073709551616) in
let y18 := ((Z.shiftr y16 2) mod 18446744073709551616) in
let y19 := ((Z.land y18 (3689348814741910323 mod 18446744073709551616)) mod 18446744073709551616) in
let y20 := ((y17 + y19) mod 18446744073709551616) in
let y21 := ((Z.shiftr y20 4) mod 18446744073709551616) in
let y22 := ((y20 + y21) mod 18446744073709551616) in
let y23 := ((Z.land y22 (1085102592571150095 mod 18446744073709551616)) mod 18446744073709551616) in
let y24 := ((y23 * (72340172838076673 mod 18446744073709551616)) mod 18446744073709551616) in
let y25 := ((Z.shiftr y24 56) mod 18446744073709551616) in
let y26 := ((((((62 mod 18446744073709551616) - y25) + 4294967296 `div` 2) mod 4294967296 - 4294967296 `div` 2)) mod 18446744073709551616) in
let y27 := ((Z.shiftl y25 1) mod 18446744073709551616) in
let y28 := ((Z.shiftr u (y26 mod 64)) mod 18446744073709551616) in
let y29 := (((((Z.shiftl (18446744073709551615 mod 18446744073709551616) (y26 mod 32)) + 4294967296 `div` 2) mod 4294967296 - 4294967296 `div` 2)) mod 18446744073709551616) in
let y30 := ((Z.lxor y27 ((126) mod 18446744073709551616)) mod 18446744073709551616) in
let y31 := ((Z.land y28 ((1) mod 18446744073709551616)) mod 18446744073709551616) in
let y32 := ((Z.lxor y29 ((-1) mod 18446744073709551616)) mod 18446744073709551616) in
let y33 := ((Z.land u y32) mod 18446744073709551616) in
let y34 := ((Z.lor y30 y31) mod 18446744073709551616) in
let y35 := (if ((0 mod 18446744073709551616) <? y33) then (1 mod 18446744073709551616) else (0 mod 18446744073709551616)) in
let y36 := ((y34 + y35) mod 18446744073709551616) in
let y37 := ((y36 + (-2)) mod 18446744073709551616) in
y37.
#[using="Type"] Lemma art_u_if : forall (b : bool) (x y : word), bv_unsigned (if b then x else y) = (if b then bv_unsigned x else bv_unsigned y).
Proof. intros [|] x y; reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_art_cid_wz := (ltac2:(TCodec.tc2 tcn__JatClassId "?'Q7yR0%211'5'7&Q8&?r1%211%4281&@%62:4%211%:3941pR:<1")) (only parsing).
Variable s : ltac:(sec_ty2 constr:(SEC_T_art_cid_wz) 0%nat 0%nat).
Lemma art_cid_wz : ltac:(sec_stmt2 constr:(SEC_T_art_cid_wz) 1%nat 0%nat).
Proof using Type s.
cbv beta delta [art_cid_w art_cid_z].
repeat (lazymatch goal with
| |- bv_unsigned (let x := ?a in @?F x) = (let y := ?b in @?G y) =>
let x' := fresh "xw" in let y' := fresh "yz" in let E := fresh "E" in
pose (x' := a); pose (y' := b);
assert (E : bv_unsigned x' = y');
[ subst x' y';
unfold v_srli, v_slli, v_or, v_and, v_xori, v_andi, v_addi, v_add, v_sub, v_mul, v_subw, v_srl, v_sllw, v_sltu, c_ltu, bv_ltu;
rewrite ?art_u_if; rewrite ?Z_to_bv_unsigned;
unfold bv_swrap, bv_wrap, bv_half_modulus;
change (bv_modulus 64) with 18446744073709551616%Z; change (bv_modulus 32) with 4294967296%Z;
repeat match goal with EE : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => rewrite EE end;
reflexivity
| change (bv_unsigned (F x') = G y'); cbv beta; clearbody x' y' ]
end).
assumption.
Qed.
End SE.
Definition art_zr8 : list Z := map (fun i => 8 * i)%Z (AsanTab.zrange 65 8128).
#[using="Type"] Lemma art_cid_z_ok : ltac2:(TCodec.tc2 tcn__JatClassId "@'5'0&E'7&G&@r1%211&;%113%6231qRD81&A%;3:21(2%?3>21").
Proof.
lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end.
Qed.
#[using="Type"] Lemma art_cid_w_ok : ltac2:(TCodec.tc2 tcn__JatClassId "O'7'4&H+`1r1%3221+RPP0%5231%7231'5&Jr2+8%3221z%63?21'Q7yR0%211&?&Q6r3%2251%411&;%114%6291%B3941p0=1p0E1pRDN1").
Proof.
intros z Hz H8. apply bv_eq. rewrite art_cid_wz, !Z_to_bv_unsigned.
pose proof art_cid_z_ok as H. rewrite forallb_forall in H.
assert (Hin : In z art_zr8).
{ unfold art_zr8. apply in_map_iff. exists (z / 8)%Z. split; [|unfold AsanTab.zrange; apply AsanTab.in_ziota; lia].
pose proof (Z.div_mod z 8 ltac:(lia)). lia. }
specialize (H z Hin). cbn beta in H. apply Z.eqb_eq in H.
pose proof (AsanTab.class_id_ok z ltac:(lia)) as (Hc & _).
unfold bv_wrap. rewrite !Z.mod_small by (change (bv_modulus 64) with (2^64)%Z; lia). exact H.
Qed.
Definition art_cid_kept (r : reg) : Prop :=
r <> 8%bv /\ r <> 12%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv /\ r <> 5%bv /\ r <> 6%bv.
Section SE.
Local Abbreviation SEC_T_art_classid_hi_run := (ltac2:(TCodec.tc2 tcn__JatClassId "R0&9y5'Q7yR0%211%5241'1y8%611%311p061'5&Br4(Q5+>(3%33@21%6251r1%93@21'6'4'=&D&CvLr6+ZhoD%?3J1=/01Jr5%756521C+ZiV@%D3O1B/01O%;5:A15G%>3=51+8%I3Q61G%L2E1&?r3%211%Q13Q841%Q;1Q<&>%11Lr2%Q5271r8%Q7213%Q93Q@31p061pR291%Q12;1%Q22C1qR6QD1%Q52QE1p0Q71pR:QH1pR8QC1pFQD1pR4QJ1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_classid_hi_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_classid_hi_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_classid_hi_run) 2%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_art_classid_hi_run) 3%nat 0%nat).
Lemma art_classid_hi_run : ltac:(sec_stmt2 constr:(SEC_T_art_classid_hi_run) 4%nat 0%nat).
Proof using Type regs M rom s.
intros H14.
pose (x1 := (v_srli s (1)%Z)). assert (E1 : x1 = (v_srli s (1)%Z)) by reflexivity. clearbody x1.
pose (x2 := (v_or s x1)). assert (E2 : x2 = (v_or s x1)) by reflexivity. clearbody x2.
pose (x3 := (v_srli x2 (2)%Z)). assert (E3 : x3 = (v_srli x2 (2)%Z)) by reflexivity. clearbody x3.
pose (x4 := (v_or x2 x3)). assert (E4 : x4 = (v_or x2 x3)) by reflexivity. clearbody x4.
pose (x5 := (v_srli x4 (4)%Z)). assert (E5 : x5 = (v_srli x4 (4)%Z)) by reflexivity. clearbody x5.
pose (x6 := (v_or x4 x5)). assert (E6 : x6 = (v_or x4 x5)) by reflexivity. clearbody x6.
pose (x7 := (v_srli x6 (8)%Z)). assert (E7 : x7 = (v_srli x6 (8)%Z)) by reflexivity. clearbody x7.
pose (x8 := (v_or x6 x7)). assert (E8 : x8 = (v_or x6 x7)) by reflexivity. clearbody x8.
pose (x9 := (v_srli x8 (16)%Z)). assert (E9 : x9 = (v_srli x8 (16)%Z)) by reflexivity. clearbody x9.
pose (x10 := (v_or x8 x9)). assert (E10 : x10 = (v_or x8 x9)) by reflexivity. clearbody x10.
pose (x11 := (v_srli x10 (32)%Z)). assert (E11 : x11 = (v_srli x10 (32)%Z)) by reflexivity. clearbody x11.
pose (x12 := (v_or x10 x11)). assert (E12 : x12 = (v_or x10 x11)) by reflexivity. clearbody x12.
pose (x13 := (v_xori x12 (-1)%Z)). assert (E13 : x13 = (v_xori x12 (-1)%Z)) by reflexivity. clearbody x13.
pose (x14 := (v_srli x13 (1)%Z)). assert (E14 : x14 = (v_srli x13 (1)%Z)) by reflexivity. clearbody x14.
pose (x15 := (v_and x14 (Z_to_bv 64 6148914691236517205))). assert (E15 : x15 = (v_and x14 (Z_to_bv 64 6148914691236517205))) by reflexivity. clearbody x15.
pose (x16 := (v_sub x13 x15)). assert (E16 : x16 = (v_sub x13 x15)) by reflexivity. clearbody x16.
pose (x17 := (v_and x16 (Z_to_bv 64 3689348814741910323))). assert (E17 : x17 = (v_and x16 (Z_to_bv 64 3689348814741910323))) by reflexivity. clearbody x17.
pose (x18 := (v_srli x16 (2)%Z)). assert (E18 : x18 = (v_srli x16 (2)%Z)) by reflexivity. clearbody x18.
pose (x19 := (v_and x18 (Z_to_bv 64 3689348814741910323))). assert (E19 : x19 = (v_and x18 (Z_to_bv 64 3689348814741910323))) by reflexivity. clearbody x19.
pose (x20 := (v_add x17 x19)). assert (E20 : x20 = (v_add x17 x19)) by reflexivity. clearbody x20.
pose (x21 := (v_srli x20 (4)%Z)). assert (E21 : x21 = (v_srli x20 (4)%Z)) by reflexivity. clearbody x21.
pose (x22 := (v_add x20 x21)). assert (E22 : x22 = (v_add x20 x21)) by reflexivity. clearbody x22.
pose (x23 := (v_and x22 (Z_to_bv 64 1085102592571150095))). assert (E23 : x23 = (v_and x22 (Z_to_bv 64 1085102592571150095))) by reflexivity. clearbody x23.
pose (x24 := (v_mul x23 (Z_to_bv 64 72340172838076673))). assert (E24 : x24 = (v_mul x23 (Z_to_bv 64 72340172838076673))) by reflexivity. clearbody x24.
pose (x25 := (v_srli x24 (56)%Z)). assert (E25 : x25 = (v_srli x24 (56)%Z)) by reflexivity. clearbody x25.
pose (x26 := (v_subw (Z_to_bv 64 62) x25)). assert (E26 : x26 = (v_subw (Z_to_bv 64 62) x25)) by reflexivity. clearbody x26.
pose (x27 := (v_slli x25 (1)%Z)). assert (E27 : x27 = (v_slli x25 (1)%Z)) by reflexivity. clearbody x27.
pose (x28 := (v_srl s x26)). assert (E28 : x28 = (v_srl s x26)) by reflexivity. clearbody x28.
pose (x29 := (v_sllw (Z_to_bv 64 18446744073709551615) x26)). assert (E29 : x29 = (v_sllw (Z_to_bv 64 18446744073709551615) x26)) by reflexivity. clearbody x29.
pose (x30 := (v_xori x27 (126)%Z)). assert (E30 : x30 = (v_xori x27 (126)%Z)) by reflexivity. clearbody x30.
pose (x31 := (v_andi x28 (1)%Z)). assert (E31 : x31 = (v_andi x28 (1)%Z)) by reflexivity. clearbody x31.
pose (x32 := (v_xori x29 (-1)%Z)). assert (E32 : x32 = (v_xori x29 (-1)%Z)) by reflexivity. clearbody x32.
pose (x33 := (v_and s x32)). assert (E33 : x33 = (v_and s x32)) by reflexivity. clearbody x33.
pose (x34 := (v_or x30 x31)). assert (E34 : x34 = (v_or x30 x31)) by reflexivity. clearbody x34.
pose (x35 := (v_sltu (Z_to_bv 64 0) x33)). assert (E35 : x35 = (v_sltu (Z_to_bv 64 0) x33)) by reflexivity. clearbody x35.
pose (x36 := (v_add x34 x35)). assert (E36 : x36 = (v_add x34 x35)) by reflexivity. clearbody x36.
pose (x37 := (v_addi x36 (-2)%Z)). assert (E37 : x37 = (v_addi x36 (-2)%Z)) by reflexivity. clearbody x37.
eexists. split; [|split].
- rwH.
stepn (ltac:(oF' 0x563f4%Z)) (ltac:(oD' 0x563f4%Z)). rwH. rewrite <- E1.
stepn (ltac:(oF' 0x563f8%Z)) (ltac:(oD' 0x563f8%Z)).
stepn (ltac:(oF' 0x563fc%Z)) (ltac:(oD' 0x563fc%Z)).
stepn (ltac:(oF' 0x56400%Z)) (ltac:(oD' 0x56400%Z)).
stepn (ltac:(oF' 0x56404%Z)) (ltac:(oD' 0x56404%Z)).
stepn (ltac:(oF' 0x56408%Z)) (ltac:(oD' 0x56408%Z)). rwH. rewrite <- E2.
stepn (ltac:(oF' 0x5640c%Z)) (ltac:(oD' 0x5640c%Z)).
stepn (ltac:(oF' 0x56410%Z)) (ltac:(oD' 0x56410%Z)).
stepn (ltac:(oF' 0x56414%Z)) (ltac:(oD' 0x56414%Z)).
stepn (ltac:(oF' 0x56418%Z)) (ltac:(oD' 0x56418%Z)).
stepn (ltac:(oF' 0x5641c%Z)) (ltac:(oD' 0x5641c%Z)). rwH. rewrite <- E3.
stepn (ltac:(oF' 0x56420%Z)) (ltac:(oD' 0x56420%Z)). rwH. rewrite <- E4.
stepn (ltac:(oF' 0x56424%Z)) (ltac:(oD' 0x56424%Z)).
stepn (ltac:(oF' 0x56428%Z)) (ltac:(oD' 0x56428%Z)).
stepn (ltac:(oF' 0x5642c%Z)) (ltac:(oD' 0x5642c%Z)).
stepn (ltac:(oF' 0x56430%Z)) (ltac:(oD' 0x56430%Z)).
stepn (ltac:(oF' 0x56434%Z)) (ltac:(oD' 0x56434%Z)).
stepn (ltac:(oF' 0x56438%Z)) (ltac:(oD' 0x56438%Z)).
stepn (ltac:(oF' 0x5643c%Z)) (ltac:(oD' 0x5643c%Z)).
stepn (ltac:(oF' 0x56440%Z)) (ltac:(oD' 0x56440%Z)).
stepn (ltac:(oF' 0x56444%Z)) (ltac:(oD' 0x56444%Z)). rwH. rewrite <- E5.
stepn (ltac:(oF' 0x56448%Z)) (ltac:(oD' 0x56448%Z)). rwH. rewrite <- E6.
stepn (ltac:(oF' 0x5644c%Z)) (ltac:(oD' 0x5644c%Z)). rwH. rewrite <- E7.
stepn (ltac:(oF' 0x56450%Z)) (ltac:(oD' 0x56450%Z)). rwH. rewrite <- E8.
stepn (ltac:(oF' 0x56454%Z)) (ltac:(oD' 0x56454%Z)). rwH. rewrite <- E9.
stepn (ltac:(oF' 0x56458%Z)) (ltac:(oD' 0x56458%Z)). rwH. rewrite <- E10.
stepn (ltac:(oF' 0x5645c%Z)) (ltac:(oD' 0x5645c%Z)). rwH. rewrite <- E11.
stepn (ltac:(oF' 0x56460%Z)) (ltac:(oD' 0x56460%Z)). rwH. rewrite <- E12.
stepn (ltac:(oF' 0x56464%Z)) (ltac:(oD' 0x56464%Z)). rwH. rewrite <- E13.
stepn (ltac:(oF' 0x56468%Z)) (ltac:(oD' 0x56468%Z)). rwH. rewrite <- E14.
stepn (ltac:(oF' 0x5646c%Z)) (ltac:(oD' 0x5646c%Z)). rwH. rewrite <- E15.
stepn (ltac:(oF' 0x56470%Z)) (ltac:(oD' 0x56470%Z)). rwH. rewrite <- E16.
stepn (ltac:(oF' 0x56474%Z)) (ltac:(oD' 0x56474%Z)). rwH. rewrite <- E17.
stepn (ltac:(oF' 0x56478%Z)) (ltac:(oD' 0x56478%Z)). rwH. rewrite <- E18.
stepn (ltac:(oF' 0x5647c%Z)) (ltac:(oD' 0x5647c%Z)). rwH. rewrite <- E19.
stepn (ltac:(oF' 0x56480%Z)) (ltac:(oD' 0x56480%Z)). rwH. rewrite <- E20.
stepn (ltac:(oF' 0x56484%Z)) (ltac:(oD' 0x56484%Z)). rwH. rewrite <- E21.
stepn (ltac:(oF' 0x56488%Z)) (ltac:(oD' 0x56488%Z)). rwH. rewrite <- E22.
stepn (ltac:(oF' 0x5648c%Z)) (ltac:(oD' 0x5648c%Z)).
stepn (ltac:(oF' 0x56490%Z)) (ltac:(oD' 0x56490%Z)). rwH. rewrite <- E23.
stepn (ltac:(oF' 0x56494%Z)) (ltac:(oD' 0x56494%Z)).
stepn (ltac:(oF' 0x56498%Z)) (ltac:(oD' 0x56498%Z)). rwH. rewrite <- E24.
stepn (ltac:(oF' 0x5649c%Z)) (ltac:(oD' 0x5649c%Z)). rwH. rewrite <- E25.
stepn (ltac:(oF' 0x564a0%Z)) (ltac:(oD' 0x564a0%Z)). rwH. rewrite <- E26.
stepn (ltac:(oF' 0x564a4%Z)) (ltac:(oD' 0x564a4%Z)). rwH. rewrite <- E27.
stepn (ltac:(oF' 0x564a8%Z)) (ltac:(oD' 0x564a8%Z)). rwH. rewrite <- E28.
stepn (ltac:(oF' 0x564ac%Z)) (ltac:(oD' 0x564ac%Z)). rwH. rewrite <- E29.
stepn (ltac:(oF' 0x564b0%Z)) (ltac:(oD' 0x564b0%Z)). rwH. rewrite <- E30.
stepn (ltac:(oF' 0x564b4%Z)) (ltac:(oD' 0x564b4%Z)). rwH. rewrite <- E31.
stepn (ltac:(oF' 0x564b8%Z)) (ltac:(oD' 0x564b8%Z)). rwH. rewrite <- E32.
stepn (ltac:(oF' 0x564bc%Z)) (ltac:(oD' 0x564bc%Z)). rwH. rewrite <- E33.
stepn (ltac:(oF' 0x564c0%Z)) (ltac:(oD' 0x564c0%Z)). rwH. rewrite <- E34.
stepn (ltac:(oF' 0x564c4%Z)) (ltac:(oD' 0x564c4%Z)). rwH. rewrite <- E35.
stepn (ltac:(oF' 0x564c8%Z)) (ltac:(oD' 0x564c8%Z)). rwH. rewrite <- E36.
stepn (ltac:(oF' 0x564cc%Z)) (ltac:(oD' 0x564cc%Z)). rwH. rewrite <- E37.
apply mst_refl.
- gres. subst. reflexivity.
- intros r (H8 & H12 & H14' & H15 & H16 & H17 & H5 & H6). gres.
repeat (rewrite getr_other by (first [exact H8|exact H12|exact H14'|exact H15|exact H16|exact H17|exact H5|exact H6|
(intros E; first [apply H8|apply H12|apply H14'|apply H15|apply H16|apply H17|apply H5|apply H6]; exact (eq_sym E))])).
reflexivity.
Qed.
End SE.
End FPX.
