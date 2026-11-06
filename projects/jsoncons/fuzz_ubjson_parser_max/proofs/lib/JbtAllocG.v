(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac ArtMem ArtRegs ArtAtomics ArtTac JbtPoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtAllocG () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "1option"; "2and"; "2eq"; "3Z"; "0M"; "0M'"; "4Wf"; "4apart"; "4cell"; "5art_layout"; "6loaded_segments"; "7add"; "7le"; "7lt"; "7of_nat"]; ["7pow"; "0a"; "0b"; "0k"; "0n"; "8bv"; "8bv_unsigned"; "0v"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
Definition hid (P : Prop) : Prop := P.
Definition nodp (dpriv : Z -> Prop) (a n : Z) : Prop := forall i, a <= i < a + n -> ~ dpriv i.
Lemma cell_agree : ltac2:(TCodec.tc2 tcn__JbtAllocG "QJ'EyR0%211'1y8%511%311p051'4'0'2&=r4&Fr1%22>1%5241&>&<&?r3%211%42:1%6281%>281'3r6r2%211r7%113%63I31p081pQBO1z%H21Gr5%B1I%D221&@+2+R0%3221%J251&9&;r8%3521E;Q3%4532CF<p021p071p0@1p0C1pQ@Q=1pQ:Q=1pQ4Q?1p>QA1p<QB1").
Proof.
intros M M' a n v AG Ha Hn C. unfold cell in *. rewrite <- C.
apply rdn_ext. rewrite art_u_lit by lia. lia.
intros x Hx. rewrite art_u_lit in Hx by lia. apply AG. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_layout_Wf := (ltac2:(TCodec.tc2 tcn__JbtAllocG "QE'EyR0%211'1y8%511%311p051'4'0&=zr3%3221&>&<r4&?%116%4231&@+2+R0%3221%:251&8r5%:1;+QV`QH+Q`P0%544321r6%?16+Qii[8+X0%:44321&:r8%211&7r9r7%34251;%711p061p0:1p0@1p0G1p0Q31pQ6Q91pQ8Q91pQ4Q;1p<Q=1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_layout_Wf) 0%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_layout_Wf) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_art_layout_Wf) 2%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_layout_Wf) 3%nat 0%nat).
Lemma art_layout_Wf : ltac:(sec_stmt2 constr:(SEC_T_art_layout_Wf) 4%nat 0%nat).
Proof.
intros Ha Hk A1 A2 L.
unfold art_layout in *. unfold apart in *.
zsplit;
match goal with |- cell _ _ ?c ?m _ => apply cell_Wf_other; [lia|lia|lia|lia|unfold apart; cbn; lia| tauto] end.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_layout_agree := (ltac2:(TCodec.tc2 tcn__JbtAllocG "M'EyR0%211'1y8%511%311pQB51&>&Fr1%22:1+Vb\P0%5221'3r3r2%211r4%113%63>31p081pQBD1&:%119p011p041p>D1p<E1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_layout_agree) 0%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_art_layout_agree) 1%nat 0%nat).
Lemma art_layout_agree : ltac:(sec_stmt2 constr:(SEC_T_art_layout_agree) 2%nat 0%nat).
Proof.
intros AG L.
unfold art_layout in *.
zsplit;
match goal with |- cell _ _ ?c ?m _ => apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | tauto] end.
Qed.
End SE.
Lemma art_layout_agree2 : ltac2:(TCodec.tc2 tcn__JbtAllocG "Q2'EyR0%211'1y8%511%311pQB51'2&=+RPP0&Fr1%22<1%5241&>+Vb\P0%2241%:241'3r3r2%211r4%113%63C31p081pQBI1&:%119p011p041p>I1p<J1").
Proof.
intros M M' AG L. unfold art_layout in *.
zsplit;
match goal with |- cell _ _ ?c ?m _ => apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | tauto] end.
Qed.
Lemma art_layout_agree3 : ltac2:(TCodec.tc2 tcn__JbtAllocG "Q2'EyR0%211'1y8%511%311pQB51'2&=+RPP0&Fr1%22<1%5241&>+RQjX8%2241%:241'3r3r2%211r4%113%63C31p081pQBI1&:%119p011p041p>I1p<J1").
Proof.
intros M M' AG L. unfold art_layout in *.
zsplit;
match goal with |- cell _ _ ?c ?m _ => apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | tauto] end.
Qed.
Section FPX. Context {fx : PropExec.FPState}.
Definition art_depot_kept (r : reg) : Prop :=
r = 2%bv \/ r = 3%bv \/ r = 4%bv \/ r = 8%bv \/ r = 9%bv \/ (18 <= bv_unsigned r <= 27).
Definition art_depot_spec (DInv : nat -> (word -> option byte) -> Prop) (DPre : (word -> option byte) -> Z -> Z -> Prop) (dpriv : Z -> Prop)
(DRo : (word -> option byte) -> Prop) (DK : Z) : Prop :=
forall (k : nat) regs (M rom : word -> option byte) (raw : word) (sp trp szt : Z),
getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 trp -> getr regs 11 = Z_to_bv 64 szt ->
DK <= sp -> sp < 2 ^ 64 -> 0x693000 <= sp - DK -> wrA M (sp - DK) DK -> nodp dpriv (sp - DK) DK -> DInv (S k) M -> DPre M trp szt -> DRo M ->
exists regs' M' id,
msteps ASEGS (mkst regs (0x9993c : word) M rom) (mkst regs' raw M' rom)
/\ getr regs' 10 = Z_to_bv 64 id /\ 0 <= id < 2 ^ 32
/\ (forall r : reg, art_depot_kept r -> getr regs' r = getr regs r)
/\ mem_grows M M'
/\ (forall x : word, ~ dpriv (bv_unsigned x) -> ~ (sp - DK <= bv_unsigned x < sp) -> M' x = M x)
/\ DInv k M'.
Definition art_depot_frame (DInv : nat -> (word -> option byte) -> Prop) (dpriv : Z -> Prop) : Prop :=
forall k M M', DInv k M -> (forall x : word, dpriv (bv_unsigned x) -> M' x = M x) -> DInv k M'.
Definition art_dpre_frame (DPre : (word -> option byte) -> Z -> Z -> Prop) : Prop :=
forall M M' trp szt, DPre M trp szt -> (forall x : word, trp <= bv_unsigned x < trp + 8 * szt -> M' x = M x) -> DPre M' trp szt.
Definition art_dro_frame (DRo : (word -> option byte) -> Prop) : Prop :=
forall M M', DRo M -> (forall x : word, 0x10000 <= bv_unsigned x < 0x20e908 -> M' x = M x) -> DRo M'.
End FPX.
Tactic Notation "klia" ne_hyp_list(l) := clear - l; lia.
Ltac oside :=
cbn; try unfold apart;
first [ lia
| match goal with H : apart _ _ _ _ |- _ => unfold apart in H; destruct H; lia end
| match goal with H : hid (_ \/ _) |- _ => unfold hid in H; destruct H; lia end ].
Ltac ond := let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; cbn in Hi; match goal with H : nodp _ _ _ |- _ => apply H; lia end.
Ltac zagree :=
repeat (first [ reflexivity
| rewrite Wn_outside; [ | lia | lia | oside ]
| rewrite Wf_outside; [ | lia | rewrite ?Z2Nat.id by lia; lia | rewrite ?Z2Nat.id by lia; oside ] ]).
