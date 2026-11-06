(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SumWalkTac () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1bool"; "1list"; "1nat"; "1option"; "1true"; "2and"; "2eq"; "3Z"; "4bytes_le_to_Z"; "5Segment"; "6word_to_le_bytes"; "7c_eq"; "7rdn"; "7v_lw"; "8add"]; ["8eqb"; "8le"; "8lt"; "8of_nat"; "8pow"; "0a"; "0b"; "0hi"; "0i"; "0lo"; "0mem"; "0n"; "0segs"; "9Z_to_bv"; "9bv"; "9bv_unsigned"]; ["0v"; "0x"; "0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Lemma bytes_le_to_Z_4 : ltac2:(TCodec.tc2 tcn__SumWalkTac "H'NyR0%211&B&Or1%2251&D+2+Q0%3221%8251'7'8&9&;u4r2%3221%511%@2C3%93821p0;1pR2E1").
Proof.
intros v Hv. rewrite bytes_le_N.
change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z.
apply Z.mod_small. pose proof (u64_range v). lia.
Qed.
Lemma v_lw_small : ltac2:(TCodec.tc2 tcn__SumWalkTac "F'8'6&Azr1%3221&B+RPPPPP0%2241%8241'7'NyR0%211&>&Mr2%2251%411%93612p0;1pR6E1").
Proof.
intros z Hz. unfold v_lw. f_equal. rewrite u_Z2bv by lia.
apply (bv_swrap_small 32). change (bv_half_modulus 32) with 2147483648%Z. lia.
Qed.
Lemma v_lw_m1 : ltac2:(TCodec.tc2 tcn__SumWalkTac "<'7'NyR0%211&>&M+SoooooO%2251%411-1%5281%;3831").
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma c_eq_Z : ltac2:(TCodec.tc2 tcn__SumWalkTac "N'8'6&Azr2%3221&B&D+2+R0%3221%5271%;271'7'1&<&MyR0r4%3221r3%5241%7231&@%1264%<3;31p0>1p0?1pQ>L1pQ<M1").
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma c_eq_refl : ltac2:(TCodec.tc2 tcn__SumWalkTac ";'NyR0%211'7'1&<r1%2211(5%63521pR481").
Proof. intros x. unfold c_eq. apply bv_eqb_refl. Qed.
End FPX_1.
Ltac zsimp := rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; u_norm.
Ltac sok_stack SOK :=
store_ok_peel;
eapply (store_ok_sub _ _ _ _ 144%nat); [ | exact SOK | | ]; zsimp; lia.
Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac lia_fast := first [ solve [ clear_disj; lia ] | lia ].
Ltac rdn_peel1 := rewrite rdn_wbytes_out by (zsimp; lia_fast).
Ltac rdn_by H := repeat rdn_peel1; exact H.
Ltac rdn_hyp :=
match goal with
| H : rdn _ _ ?a ?n = Some _ |- rdn _ _ ?a ?n = Some _ => exact H
end.
Ltac rdn_solve :=
lazymatch goal with
| |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
else (rdn_peel1; rdn_solve)
| |- _ => rdn_hyp
end.
Ltac zbv_target x i :=
lazymatch x with
| Z_to_bv 64 (?a - ?b)%Z => let d := eval cbv in (b - i)%Z in constr:(Z_to_bv 64 (a - d))
| Z_to_bv 64 (?a + ?b)%Z => let d := eval cbv in (b + i)%Z in constr:(Z_to_bv 64 (a + d))
| Z_to_bv 64 ?a =>
lazymatch i with
| Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (a - d))
| _ => constr:(Z_to_bv 64 (a + i))
end
| _ =>
lazymatch i with
| Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (bv_unsigned x - d))
| _ => constr:(Z_to_bv 64 (bv_unsigned x + i))
end
end.
Ltac addr_norm :=
match goal with
| |- context [v_addi ?x ?i] =>
let e := constr:(v_addi x i) in
tryif check_closed_term e then wlit_closed e
else first
[ rewrite (v_addi_0 x)
| let t := zbv_target x i in
replace_nb e t ltac:(unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
| _ => idtac
end.
Ltac sp_renorm :=
match goal with
| |- context [regupd _ 2 (v_addi ?x ?i)] =>
let e := constr:(v_addi x i) in
first
[ rewrite (v_addi_0 x)
| let t := zbv_target x i in
replace_nb e t ltac:(unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
end.
Ltac getr_hyps :=
repeat match goal with
| H : getr ?rs ?n = _ |- context [getr ?rs ?n] => rewrite H
end.
Ltac addr_tac := getr_hyps; unfold v_addi; u_norm; first [reflexivity | f_equal; lia | apply bv_eq; u_norm; lia].
Ltac val_tac := first [reflexivity | assumption | symmetry; assumption].
Ltac stepST F D aa vv oktac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Store SZ8 _ _ _, _) =>
eapply step_sd_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
| decode_any _ = Some (Store SZ4 _ _ _, _) =>
eapply step_sw_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
| decode_any _ = Some (Store SZ1 _ _ _, _) =>
eapply MmapSim.step_sb_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac
| reflexivity | oktac ]
end
| step_simpl ].
Ltac stepLD F D bsv vv rdtac vtac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
| decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
| decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
end;
[ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac | vtac ]
| step_simpl ]; vnorm.
Ltac stepLD8 F D vv := stepLD F D (word_to_le_bytes 8 vv) vv ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
Ltac stepLBU F D bb rdtac :=
chain_step;
[ reflexivity
| eapply step_lbu with (b := bb);
[ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac ]
| step_simpl ]; vnorm.
Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with
| context [bv_unsigned (Z_to_bv 64 _)] => fail
| _ => rewrite (u_Z2bv z) by lia
end
end.
Ltac addi_renorm :=
match goal with
| |- context [regupd _ _ (v_addi (Z_to_bv 64 ?x) ?i)] =>
let t := zbv_target (Z_to_bv 64 x) i in
replace_nb (v_addi (Z_to_bv 64 x) i) t ltac:(unfold v_addi; unorm; f_equal; lia)
end.
Section FPX_2. Context {fx : PropExec.FPState}.
Lemma rdn_img : ltac2:(TCodec.tc2 tcn__SumWalkTac "R6'2':%211'NyR0%211'4y8%511%311pR451'8'3'6&Ar3r1%3221&Br2%2241%8241'7r7&M%12E6%311(0%11D%73D31p091pQBD1r5%C2B1&?r6&C%115%4231%I21Hz%K219&D+2+R0%3221%L2>1%Q?1Q7%Q:11&=r;r:r9%M2QA1r8%645421q0QCL%847143%Q43:31p0=1p0C1p0F1p0M1p0Q01pQ@QE1pQDQF1pQHQF1pQ<QH1pQFQJ1pQJR31").
Proof.
intros segs mem a n lo hi Himg Hlo Hhi H0 H64.
apply rdn_ext; [u_norm; lia|].
intros x Hx. revert Hx. u_norm. intros Hx.
rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Himg. lia.
Qed.
End FPX_2.
Ltac img_exists :=
lazymatch goal with |- exists bs, ?l = Some bs =>
let v := eval vm_compute in l in
lazymatch v with Some ?bs => exists bs; vm_compute; reflexivity end
end.
Ltac enum_nat k N tac :=
let rec go n := lazymatch n with
| O => lia
| S ?m => destruct k as [|k]; [tac | go m]
end in go N.
Ltac zaddr H :=
repeat match type of H with
| context [Z_to_bv 64 (?a + ?b)%Z] =>
let c := eval cbv in (a + b)%Z in change (a + b)%Z with c in H
end.
Ltac zaddr_goal :=
repeat match goal with
| |- context [Z_to_bv 64 (?a + ?b)%Z] =>
let c := eval cbv in (a + b)%Z in
lazymatch c with
| Zpos _ => change (a + b)%Z with c
end
end.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
