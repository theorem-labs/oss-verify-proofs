(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACh0 ACgy.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChb ACj1 ACjr ACj3 ACgw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac awr_aX_rec Usp E32u Hing HTS :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
first
[ eapply awr_ok_cons_stack_off with (n := 2%nat) (d := 0);
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn; rewrite HTS; lia | cbn; lia |]
| eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -224);
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn; rewrite HTS; lia | cbn; lia |] ]
| |- awr_ok _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32u | exact Hing | cbn [YP09.r_wlo]; lia
| cbn [YP09.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
first
[
unfold FPb, ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
|
unfold FPn; lazymatch type of E32u with _ = ?g => exists (g + 88, g + 92) end;
split; [left; reflexivity | cbn [fst snd]; lia] ]
| ]
end
| fail 1 "awr_a: no rule for the head region" ];
awr_aX_rec Usp E32u Hing HTS
end.
Ltac awr_aX Usp E32u Hing HTS :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
awr_aX_rec Usp E32u Hing HTS.
Ltac awr_xX_rec Usp E32u Hing HTS Bnw Anw HnwIn :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -224);
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn; rewrite HTS; lia | cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32u | exact Hing | cbn [YP09.r_wlo]; lia
| cbn [YP09.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; unfold FPb, ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
| ]
| |- awr_ok _ (YP09.mkRegion (Some 23%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
lazymatch type of Bnw with _ = ?nw =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat nw);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact Bnw
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; replace a with (nw + (a - nw)) by lia; apply Anw; [exact HnwIn | change (req_size 40) with 40; lia]
| ] end
end
| fail 1 "awr_x: no rule for the head region" ];
awr_xX_rec Usp E32u Hing HTS Bnw Anw HnwIn
end.
Ltac awr_xX Usp E32u Hing HTS Bnw Anw HnwIn :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
awr_xX_rec Usp E32u Hing HTS Bnw Anw HnwIn.
Ltac awr_yX_rec Usp E32u Hing HTS Bnw Anw HnwIn Bfp Afp HfpIn :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -224);
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn; rewrite HTS; lia | cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32u | exact Hing | cbn [YP09.r_wlo]; lia
| cbn [YP09.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; unfold FPb, ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
| ]
| |- awr_ok _ (YP09.mkRegion (Some 23%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
lazymatch type of Bnw with _ = ?nw =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat nw);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact Bnw
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; replace a with (nw + (a - nw)) by lia; apply Anw; [exact HnwIn | change (req_size 40) with 40; lia]
| ] end
| |- awr_ok _ (YP09.mkRegion (Some ?p) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
lazymatch type of Bfp with bv_unsigned _ = ?fpa =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ p fpa);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia;
lazymatch type of Bfp with bv_unsigned ?x = _ => let x' := eval cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in x in
first [exact Bfp | rewrite <- Bfp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; reflexivity] end
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; replace a with (fpa + (a - fpa)) by lia; apply Afp; [exact HfpIn | change (req_size 40) with 40; lia]
| ] end
end
| fail 1 "awr_y: no rule for the head region" ];
awr_yX_rec Usp E32u Hing HTS Bnw Anw HnwIn Bfp Afp HfpIn
end.
Ltac awr_yX Usp E32u Hing HTS Bnw Anw HnwIn Bfp Afp HfpIn :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
awr_yX_rec Usp E32u Hing HTS Bnw Anw HnwIn Bfp Afp HfpIn.
Ltac af_xcover Ha HTS Hnw :=
lazymatch type of Ha with
| _ \/ _ => let H1 := fresh "Ha" in let H2 := fresh "Ha" in destruct Ha as [H1 | H2]; [af_xcover H1 HTS Hnw | af_xcover H2 HTS Hnw]
| _ => first
[ left; clear - Ha HTS; lia
| right; eexists _, CGIF_SIZE; split; [left; reflexivity | change (req_size CGIF_SIZE) with 96; clear - Ha; lia]
| match goal with Hf : In (Some ?f) (cg_frames _) |- _ =>
right; exists (fr_ptr f), FRAME_SIZE; split;
[ apply in_app_iff; left; exact (af_wblocks_frame _ _ f Hf)
| change (req_size FRAME_SIZE) with 40; first [clear - Ha; lia | clear - Ha Hnw; lia] ] end
|
right; eexists _, FRAME_SIZE; split; [apply in_app_iff; right; left; reflexivity | change (req_size FRAME_SIZE) with 40; clear - Ha; lia]
| match goal with |- ?gg => idtac "XCOVER-FAIL" gg; fail 1 end ]
end.
Ltac af_xunz UN B LAWS lyc Sc Wc memc mdc g s1 N X ly sp0 HAR HP Hstk HTS Hnw XZb XZi :=
lazymatch type of UN with (forall a, _ -> ~ @?Zs a -> _) =>
pose proof (af_xfoot_unz B LAWS lyc Sc Wc memc mdc g s1 N X _ ly sp0 Zs HAR HP Hstk
ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbv beta in Ha; af_xcover Ha HTS Hnw)) as [XZb XZi] end.
Ltac af_xunz2 UN B LAWS lyc Sc Wc memc mdc g s1 N Xw Xv ly sp0 HAR HP Hstk HTS Hnw XZb XZi :=
lazymatch type of UN with (forall a, _ -> ~ @?Zs a -> _) =>
pose proof (af_xfoot_unz2 B LAWS lyc Sc Wc memc mdc g s1 N Xw Xv _ ly sp0 Zs HAR HP Hstk
ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbv beta in Ha; af_xcover Ha HTS Hnw)) as [XZb XZi] end.
Ltac af_xunz3 UN B LAWS lyc Sc Wc memc mdc g s1 N X Xw Xv ly sp0 HAR HP HPX Hstk HTS Hnw XZb XZi :=
lazymatch type of UN with (forall a, _ -> ~ @?Zs a -> _) =>
pose proof (af_xfoot_unz3 B LAWS lyc Sc Wc memc mdc g s1 N X Xw Xv _ ly sp0 Zs HAR HP HPX Hstk
ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbv beta in Ha; af_xcover Ha HTS Hnw)) as [XZb XZi] end.
