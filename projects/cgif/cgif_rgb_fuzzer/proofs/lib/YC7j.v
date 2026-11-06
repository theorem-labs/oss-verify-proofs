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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCas YCbh.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section LX.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Lemma rga_entry_blk_kept : forall cx own ly3 S3 W3 mem3 md3 k b n l,
ajournal trasegs B TRGBADD_STK (spZ (c_regs cx)) (rgc_FPs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k ->
AR trasegs B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ->
Permutation (ablocks B (c_ly cx) (c_S cx)) ((c_r cx, RGB_SIZE) :: l) -> In (b, n) l -> In (b, n) (ablocks B ly3 S3) ->
rg_blk_kept (w_H (c_W cx)) (w_H W3) (c_mem cx) mem3 b (req_size n).
Proof.
intros cx own ly3 S3 W3 mem3 md3 k b n l HJ HAR HP Hl Hin3 i Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 b n i); [eapply Permutation_in; [apply Permutation_sym; exact HP | right; exact Hl] | exact Hin3 | exact Hi |].
intros (rg & [<- | []] & Hr). cbn [fst snd] in Hr.
pose proof (rg_sep_head_in B LAWS _ _ _ _ _ (c_r cx, RGB_SIZE) l (b, n) HAR HP Hl) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma rga_INV_X_same : forall cx E k ly3 S3 W3 ms3 md3 own cur',
rga_base B cx ->
ajournal trasegs B TRGBADD_STK (spZ (c_regs cx)) (rgc_FPs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 (ms_mem ms3) md3 k ->
k <= EV_RGBADD -> rga_bud cx S3 k RGA_G RGA_T 57 ->
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) ->
obj_at trasegs (mrestrict (w_H W3) (ms_mem ms3)) (c_r cx) LAY_Rgb
[c_g cx; c_wfn cx; c_ctx cx; c_path cx; c_attr cx; c_gen cx; c_loops cx; c_Wd cx; c_Hd cx; c_bef cx; c_beffmt cx; cur'] ->
INV_X B cx E k ly3 S3 W3 ms3 md3.
Proof.
intros cx E k ly3 S3 W3 ms3 md3 own cur' HB HJ Hk Hbud HP3 Hobj.
destruct HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcg & Hwf & HcW & HcH & _ & Hbef & HPerm & _).
pose proof HPRE as (HAR & _).
split; [split; [exact Hk | exact Hbud]|]. exists (c_s cx), (c_bef cx), (c_beffmt cx), cur'.
split; [exact Hobj|]. split.
{ apply (rg_tcgif_at_blocks_kept (w_H (c_W cx)) (w_H W3) (c_mem cx) (ms_mem ms3) (c_g cx) (c_s cx) (c_N cx) Hcg).
intros b sz Hb. unfold trgb_own in HPerm. cbn [app] in HPerm.
eapply (rga_entry_blk_kept cx own ly3 S3 W3 (ms_mem ms3) md3 k b sz _ HJ HAR HPerm).
- apply in_or_app. left. apply in_or_app. left. exact Hb.
- eapply Permutation_in; [apply Permutation_sym; exact HP3|]. eapply Permutation_in; [apply Permutation_sym; exact HPerm|].
right. apply in_or_app. left. apply in_or_app. left. exact Hb. }
split; [exact Hwf|]. split; [exact HcW|]. split; [exact HcH|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hbef|].
split; [eapply Permutation_trans; [exact HP3 | exact HPerm]|].
intros b Hb. split.
- intros _ i Hi. destruct b as [b n]. cbn [fst snd] in *. apply (inFP_ablocks_fp _ b n); [exact Hb | exact Hi].
- intros blc lyq i Hbl Hi. destruct b as [b n]. cbn [fst snd] in *. right. left. split.
+ apply (inFP_ablocks_fp _ b n); [exact Hb | exact Hi].
+ exists b, n. split; [exact Hbl | lia].
Qed.
Lemma rga_obj_r_of_region : forall E m r lo hi wlo whi cs (vals : list Z) ecur cur',
region_ok trasegs E m (YQ0b.mkRegion (Some 10%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 10) = r ->
length vals = 11%nat ->
(forall j v, nth_error vals j = Some v -> ew E (32 + j) = Z_to_bv 64 v /\
0 <= v < 2 ^ (8 * Z.of_N (snd (nth j LAY_Rgb (0, 8%N)))) /\
In (YQ0b.mkChunk (fst (nth j LAY_Rgb (0, 8%N))) (CVal (snd (nth j LAY_Rgb (0, 8%N))) (SOff (32 + j) 0))) cs) ->
In (YQ0b.mkChunk 60 (CVal 4 ecur)) cs -> sv_denot E ecur = Z_to_bv 64 cur' -> 0 <= cur' < 2 ^ 32 ->
obj_at trasegs m r LAY_Rgb (vals ++ [cur']).
Proof.
intros E m r lo hi wlo whi cs vals ecur cur' HR Hr Hlen Hv Hc60 Hcur Rcur.
assert (FLD : forall j v, nth_error vals j = Some v ->
field_ok trasegs m r (nth j LAY_Rgb (0, 8%N)) v).
{ intros j v Hj. destruct (Hv j v Hj) as (He & Hrg & Hin). split; [|exact Hrg].
assert (Hw : Z.of_N (snd (nth j LAY_Rgb (0, 8%N))) <= 8).
{ assert (Hjl : (j < 11)%nat) by (rewrite <- Hlen; apply nth_error_Some; congruence).
do 11 (destruct j as [|j]; [cbn; lia|]). lia. }
apply (field_of_region E m 10 r cs lo hi wlo whi _ _ (SOff (32 + j) 0) v HR Hr Hin); [|exact Hrg | exact Hw].
cbn [sv_denot]. rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
do 11 (destruct vals as [|? vals]; [discriminate Hlen|]). destruct vals; [|discriminate Hlen].
cbn [app obj_at LAY_Rgb].
repeat (split; [first [ exact (FLD 0%nat _ eq_refl) | exact (FLD 1%nat _ eq_refl) | exact (FLD 2%nat _ eq_refl) | exact (FLD 3%nat _ eq_refl)
| exact (FLD 4%nat _ eq_refl) | exact (FLD 5%nat _ eq_refl) | exact (FLD 6%nat _ eq_refl) | exact (FLD 7%nat _ eq_refl)
| exact (FLD 8%nat _ eq_refl) | exact (FLD 9%nat _ eq_refl) | exact (FLD 10%nat _ eq_refl) ]|]).
split; [|exact I]. split; [|exact Rcur].
apply (field_of_region E m 10 r cs lo hi wlo whi 60 4%N ecur cur' HR Hr Hc60 Hcur); [exact Rcur | cbn; lia].
Qed.
Lemma rga_E_ewset : forall cx E n v, (68 <= n)%nat -> rga_E cx E -> rga_E cx (ewset E n v).
Proof.
intros cx E n v Hn (AG & EX & E54 & E66 & E67). unfold rga_E.
split; [intros i Hi; rewrite ew_ewset_other by lia; apply AG; exact Hi|].
split; [intros j Hj; rewrite ew_ewset_other by lia; apply EX; exact Hj|].
rewrite !ew_ewset_other by lia. auto.
Qed.
Lemma rga_E_havoc : forall cx E N vs, (68 <= N)%nat -> rga_E cx E -> rga_E cx (havoc E N vs).
Proof.
intros cx E N vs Hn (AG & EX & E54 & E66 & E67). unfold rga_E.
split; [intros i Hi; rewrite ew_havoc_old by lia; apply AG; exact Hi|].
split; [intros j Hj; rewrite ew_havoc_old by lia; apply EX; exact Hj|].
rewrite !ew_havoc_old by lia. auto.
Qed.
End LX.
End a.
