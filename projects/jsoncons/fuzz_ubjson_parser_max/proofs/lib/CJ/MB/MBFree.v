(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc KInv MI_Kit MI_Arith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import BrRes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.MB Require Import MBBase MBMeta.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_MB_MBFree () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.BrRes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.MB.MBBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.MB.MBMeta."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."], [["1Some"; "1nat"; "1prod"; "2eq"; "3Z"; "4EVF"; "4efree_ok"; "4gtree"; "4pot"; "5SAME2"; "5leaves"; "5retK"; "5scal"; "6SH"; "7M"; "7aptr"]; ["7cfree"; "7cptr"; "7dec_slots"; "7free_group"; "7free_tail"; "7mapinfo"; "7mstate"; "7nontrivial_free"; "8le"; "0bail"; "0c"; "0cs"; "0cs'"; "0f"; "0g"; "0i"]; ["0idx"; "0k"; "0rec"; "0st"; "0st'"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section FG.
Variable rec : mstate -> aptr -> Z -> (mstate -> mapinfo -> M mstate) -> M mstate -> M mstate.
Hypothesis Hrec : forall st g i (k : mstate -> mapinfo -> M mstate) bail, retK (SAME2 st) k (rec st g i k bail).
Lemma free_group_shape : ltac2:(TCodec.tc2 tcn__CJ_MB_MBFree "H'F&?&E&>%114p031p061&;&9r4%2281r2&C&B%11>vQ2r3r1%67B439271%<5CA981pQD@1pR4?1pQNE1pR8G1").
Proof. intros st g k bail.
unfold free_group. cbv zeta.
set (st1 := if m_sizeclass (get_meta_rec st g) <? 48 then _ else st).
assert (S1 : scal st1 = scal st) by (subst st1; destruct (_ <? 48); autorewrite with scal; reflexivity).
clearbody st1.
shape_case; [| right; exact I].
shape_case.
- match goal with |- retK _ _ (free_meta ?m ?s ?kk ?b) =>
destruct (free_meta_shape m s kk b) as [(st3 & -> & S3)|U]; [| right; exact U] end.
apply retK_here. unfold SAME2. unfold SAME in S3. rewrite S3. autorewrite with scal. exact S1.
- unfold dec_slots. shape_case; [| right; exact I].
match goal with |- retK _ _ (match ?x with _ => _ end) => destruct x as [m idx] end.
match goal with |- retK _ _ (rec ?s ?a ?b ?kk ?bl) =>
destruct (Hrec s a b kk bl) as [(st3 & mi & -> & S3)|U]; [| right; exact U] end.
cbv beta. unfold SAME2 in S3.
match goal with |- retK _ _ (free_meta ?m' ?s ?kk ?b) =>
destruct (free_meta_shape m' s kk b) as [(st4 & -> & S4)|U]; [| right; exact U] end.
apply retK_here. unfold SAME2. unfold SAME in S4. rewrite S4, S3. autorewrite with scal. exact S1.
Qed.
End FG.
Lemma nontrivial_free_shape : ltac2:(TCodec.tc2 tcn__CJ_MB_MBFree "M'1'F&?'4&E&>%115p031p071&;&9r5%2281r2&G&B%11?r6r4r3r1%78D54:3281%=5EB:91pQDA1pR4@1pR0F1pQNH1pR8J1pQLL1").
Proof. intros f.
induction f as [|f IH]; intros st g i k bail.
- cbn [nontrivial_free]. right. exact I.
- cbn [nontrivial_free]. shape_case.
+ shape_case.
* shape_guard. cbv zeta. shape_case.
-- shape_case.
++ match goal with |- retK _ _ (activate_group ?m ?s ?kk ?b) =>
destruct (activate_group_shape m s kk b) as [(st2 & v & -> & S2)|U]; [| right; exact U] end.
cbv beta. unfold SAME2 in S2. rewrite scal_dequeue in S2.
eapply retK_mono; [| apply free_group_shape; exact IH]. unfold SAME2. intros st' x H. rewrite H. exact S2.
++ eapply retK_mono; [| apply free_group_shape; exact IH]. unfold SAME2. intros st' x H. rewrite H. apply scal_dequeue.
-- eapply retK_mono; [| apply free_group_shape; exact IH]. unfold SAME2. intros st' x H. rewrite H. apply scal_dequeue.
* apply free_group_shape. exact IH.
+ shape_case.
* shape_guard. cbv zeta. shape_case.
-- match goal with |- retK _ _ (queue ?h ?m ?s ?kk ?b) =>
destruct (queue_shape h m s kk b) as [(st2 & -> & S2)|U]; [| right; exact U] end.
apply retK_here. unfold SAME2. unfold SAME in S2. autorewrite with scal. exact S2.
-- apply retK_here. unfold SAME2. autorewrite with scal. reflexivity.
* apply retK_here. unfold SAME2. autorewrite with scal. reflexivity.
Qed.
Theorem free_tail_g : ltac2:(TCodec.tc2 tcn__CJ_MB_MBFree "L'F&?'4&7&6u1z&D&B%119r3r2r1%644321'3'2%12>>%221?&<%117r4%311%83531qR:G1%E6HDCB;1pR2G1pQNI1pR8K1").
Proof. intros st g idx.
unfold free_tail. cbv zeta. apply gtree_guard. intros _. gcase.
- apply gtree_ret'. autorewrite with scal. reflexivity.
- eapply gtree_retK; [apply nontrivial_free_shape|]. intros st2 mi S2. unfold SAME2 in S2. cbv beta.
destruct mi as [[base len]|]; [| apply gtree_ret'; exact S2].
gcase; [| apply gtree_ret'; exact S2].
apply gtree_vis; [exact I| rewrite ecost_munmap; lia|]. intros ru Hru. cbn in Hru. subst ru.
rewrite munmap_answer_ok_0. apply gtree_ret'. autorewrite with scal. exact S2.
Qed.
Theorem cfree_g : ltac2:(TCodec.tc2 tcn__CJ_MB_MBFree "F'F&A&7&6&5z&@r2(0r1%2291%5241&H&8%115r3%311%5231qQJB1%A6C@?>81pQFC1pQHE1").
Proof. intros cs c.
unfold cfree. gcase; [| apply gtree_undef; exact I].
match goal with |- gtree _ _ _ (match ?x with _ => _ end) _ => destruct x as [g idx] end.
eapply gtree_bind.
- eapply gtree_le; [| | apply free_tail_g]; [unfold EVF; lia| lia].
- intros st1 ne' bb' S1. cbv beta. apply gtree_ret'.
rewrite (pot_of_scal cs (strip st1)); [lia|]. rewrite scal_strip. exact S1.
Qed.
Theorem free_tail_lv : ltac2:(TCodec.tc2 tcn__CJ_MB_MBFree "I'F&?'4&:'3'2%1244%2215&<r1%211r4%411%93631qR:>1&D&B%11Ar3r2%54321;%B3E71pR2D1pQNF1pR8H1").
Proof. intros st g idx.
unfold free_tail. cbv zeta. apply leaves_guard. intros _. gcase.
- apply leaves_ret. autorewrite with scal. reflexivity.
- eapply leaves_retK; [apply nontrivial_free_shape|]. intros st2 mi S2. unfold SAME2 in S2. cbv beta.
destruct mi as [[base len]|]; [| apply leaves_ret; exact S2].
gcase; [| apply leaves_ret; exact S2].
apply leaves_vis. intros ru. gcase.
+ apply leaves_ret. autorewrite with scal. exact S2.
+ apply leaves_undef. exact I.
Qed.
Theorem cfree_lv : ltac2:(TCodec.tc2 tcn__CJ_MB_MBFree "?'F&A&=r2%211&:&@r3(0%1286%4231%63;91p081pQF<1pQH>1").
Proof. intros cs c.
intros HS. unfold cfree. gcase; [| apply leaves_undef; exact I].
match goal with |- leaves _ (match ?x with _ => _ end) => destruct x as [g idx] end.
eapply leaves_bind; [apply free_tail_lv|].
intros st1 S1. cbv beta. apply leaves_ret. eapply SH_scal; [| exact HS]. rewrite scal_strip. exact S1.
Qed.
End CEIL_WRAP_1.
