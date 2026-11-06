(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCbn YCbi YCbo YC1c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8i.
Ltac m_awrR_rec AG fpos F EFA aF aFS extra :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YQ0b.mkRegion ?bs _ _ ?wlo ?whi _ :: _) _ _ _ _ ?blc _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch bs with
| Some aFS =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ aFS); [reflexivity | ga_evalE AG | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; right; right; right; exists 7, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 7 / 8) with 1024; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| Some aF =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ aF); [reflexivity | ga_evalE AG | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; right; right; right; exists 7, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 7) with 8192; rewrite ?EFA; fold F; clear - Ha; lia
| ]
| Some 2%nat =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | ga_evalE AG | cbn; lia | cbn; lia |]
| Some ?nb =>
first
[ match goal with Rb : ew _ nb = Z_to_bv 64 ?b, Ab : forall blc' lyq ownq i, In (?b', ?sz) blc' -> _, Hin : In (?b', ?sz) blc |- _ =>
constr_eq b b';
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ nb); [reflexivity | ga_evalE AG | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; replace a with (b + (a - b)) by lia; apply Ab; [exact Hin | clear - Ha; lia]
| ] end
| extra nb ]
end
| fail 1 "m_awrR: no rule for the head region" ];
m_awrR_rec AG fpos F EFA aF aFS extra
end.
Ltac m_awrR AG fpos F EFA aF aFS extra :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
m_awrR_rec AG fpos F EFA aF aFS extra.
Ltac m_awr_cell nc Rc b Ab Hin side :=
fun nb => lazymatch nb with nc =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ nc); [reflexivity | first [rewrite Rc | repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite Rc]; apply unsigned_lit_small; side | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; replace a with (b + (a - b)) by lia; apply Ab; [exact Hin | side]
| ] end.
Ltac m_obl_cell HJx Rc HEbx Hin side :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?n 0)) ?len =>
lazymatch type of Rc with ew _ n = Z_to_bv 64 ?v =>
lazymatch type of Hin with In (?p, ?sz) _ =>
rewrite (U_atom Ex n v); [| first [exact Rc | rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact Rc] | side];
eapply (obl_of_block trasegs _ L _ _ _ _ _ Ex (SOff bx 0) _ len p sz (proj1 HJx) Hin);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEbx | unfold SB; lia]
| side | side ] end end end.
