(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/A/ACja.v for libreac/fuzz_disco's program walk, over fuzz_disco's listing. Image objects follow fuzz_disco.asan: the GOT word of the shadow-base cell is object 1 (atom 242), the GOT word of the side-stack flag is object 0 (atom 241), the shadow-base cell is object 66 (atom 307) and the side-stack flag cell is object 67 (atom 308), so img_factsF and img_hull_factsF give E240 E241 E242 E307 E308 and Hob241 Hob242 Hob307 Hob308, keptFL keeps those four regions, and aconstsF rewrites with PALib's pal_got_shadow, pal_cell and DiscoFrame's palf_got_uar. awrFL, keptFL, fs_roF and fs_rwF keep the walks' atoms for the own side-stack frame (516), its shadow (529), the realigned stack (60) and the stack (2), for any frame class; stack bounds compute the walk's own STK constant; cgif's case for its 40-byte FRAME block (atom 11) is left out, and awrFL_with/keptFL_with take a tactic for a walk's own head regions. Module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoACja.v, with its module paths and module names changed; 928 of its 996 lines of code are new or changed and 263 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCkd AmemBlock8.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YP0c YP07 YI0w YI0z YI12 YC4a YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared PfFacts SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjBase TjCuts TjLoopCuts TjSnSh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0j.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition tkb_kb (P : Prop) : Prop := P.
Lemma tkb_kb_intro : forall P : Prop, P -> tkb_kb P.
Proof. intros P H. exact H. Qed.
Ltac tkb_hd AG HSK :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear - HSK; cbn; lia | clear; cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
lazymatch goal with Hsp1 : sp0 - _ <= ?sp1 <= sp0 - _ |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0)); [reflexivity | evalE AG | clear - Hsp1 HSK; cbn; lia | clear - Hsp1; cbn; lia |] end
end.
Ltac tkb_fsb := repeat match goal with
| |- context [fs_frame_bytes ?c / 8] => let v := eval vm_compute in (fs_frame_bytes c / 8) in
lazymatch v with Zpos _ => change (fs_frame_bytes c / 8) with v end
| |- context [fs_frame_bytes ?c] => let v := eval vm_compute in (fs_frame_bytes c) in
lazymatch v with Zpos _ => change (fs_frame_bytes c) with v end
end.
Ltac tkb_awr_rec hd AG fpos F EFA :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
| hd
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; tkb_fsb; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; tkb_fsb; rewrite ?EFA; fold F; clear - Ha; lia
| ]
end
| match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "tkb_awr: no rule for the head region" ];
tkb_awr_rec hd AG fpos F EFA
end.
Ltac tkb_awr hd AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
tkb_awr_rec hd AG fpos F EFA.
Ltac tkb_fa2 tac := apply Forall_cons; [tac | apply Forall_cons; [tac | apply Forall_nil]].
Ltac tkb_lia := try unfold ASAN_CEIL in *; try unfold M64 in *; lia.
Ltac tkb_mem := try unfold amem_range in *; try unfold in_app in *; try unfold kLowShadowBeg in *;
try unfold kHighShadowEnd in *; try unfold ASAN_CEIL in *; lia.
Local Ltac gadd H := let HG := fresh "HGq" in match goal with G : boxed _ |- _ => pose proof (conj G H) as HG; clear G; box HG end.
Local Ltac kbx HG := unfold boxed in HG; try unfold ASAN_CEIL, M64 in *.
Local Ltac kglia := first [match goal with HG : boxed _ |- _ => clear - HG; kbx HG; lia end | clear; lia | lia].
Local Ltac kglia_t := first [match goal with HG : boxed _ |- _ => clear - HG; kbx HG; lia end | clear; tkb_lia | tkb_lia].
Local Ltac kglia_m := first [match goal with HG : boxed _ |- _ => clear - HG; kbx HG; try unfold amem_range, in_app, kLowShadowBeg, kHighShadowEnd in *; lia end | tkb_mem].
Local Ltac kglia_with H := first [match goal with HG : boxed _ |- _ => clear - H HG; kbx HG; lia end | lia].
Local Ltac kglia_with_t H := first [match goal with HG : boxed _ |- _ => clear - H HG; kbx HG; lia end | tkb_lia].
Local Ltac kglia_with_s H := first [match goal with HG : boxed _ |- _ => clear - H HG; kbx HG; unfold shadow_addr, shadow_of_addr, SHADOW_OFF in *; lia end
| unfold shadow_addr, shadow_of_addr, SHADOW_OFF in *; lia].
Ltac tkb_notw AG Ha :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG;
first [match goal with HG : boxed _ |- _ => clear - Ha HG; intros; kbx HG; lia end | intros Hrg; lia]|]);
destruct Hin.
Ltac tkb_notw_goal AG Hx :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG;
first [match goal with HG : boxed _ |- _ => clear - Hx HG; intros; kbx HG; unfold shadow_addr, shadow_of_addr, SHADOW_OFF in *; lia end
| intros Hrg; unfold shadow_addr, shadow_of_addr, SHADOW_OFF in *; lia]|]);
destruct Hin.
Ltac tkb_notw_fa AG Ha :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros rg Hin;
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; evalE AG;
first [match goal with HG : boxed _ |- _ => clear - Ha HG; intros; kbx HG; lia end | intros Hrg; lia]|]);
destruct Hin.
Ltac tkb_mvtok HFr AG Hg Hra Hhl Hg2 Hra2 Hhl2 base lst n :=
lazymatch type of HFr with frame_of _ _ (mrestrict ?Hh _) (mrestrict _ ?m1) =>
assert (Hg2 : garr8 (@pa_segs _ lib_both3_0_listing _) (mrestrict Hh m1) base lst) by
(apply (garr8_frame _ _ _ _ _ Hg); intros a Ha; rewrite length_app in Ha; cbn [length] in Ha;
apply (mbyte_of_frame_x _ _ _ _ _ a HFr); [kglia_with_t Ha | tkb_notw_fa AG Ha]);
assert (Hra2 : range_addressable (aview (@pa_segs _ lib_both3_0_listing _) Hh m1) SHADOW_OFF base n) by
(let x := fresh "x" in let Hx := fresh "Hx" in let s := fresh "s" in let Hs := fresh "Hs" in let Hk := fresh "Hk" in
intros x Hx; destruct (Hra x Hx) as (s & Hs & Hk); exists s; split; [|exact Hk];
rewrite <- Hs; eapply aview_kept_out;
[exact HFr | kglia_with_s Hx | tkb_notw_goal AG Hx]);
assert (Hhl2 : shadow_hull_vis (aview (@pa_segs _ lib_both3_0_listing _) Hh m1) base n) by
(let s := fresh "s" in let Hs := fresh "Hs" in
intros s Hs; rewrite (aview_kept_out _ _ _ _ _ HFr s ltac:(kglia_with_s Hs)
ltac:(tkb_notw_goal AG Hs)); apply Hhl; exact Hs)
end.
Ltac tkb_HK HFr AG buf cap HK :=
lazymatch type of HFr with frame_of _ _ (mrestrict ?Hh ?m0) (mrestrict _ ?m1) =>
assert (HK : forall a, buf <= a < buf + cap -> aview (@pa_segs _ lib_both3_0_listing _) Hh m1 a = aview (@pa_segs _ lib_both3_0_listing _) Hh m0 a)
by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; eapply aview_kept_out; [exact HFr | kglia_with Ha | tkb_notw AG Ha]) end.
Ltac tkb_wnone HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac tkb_wfull HS n hi tac :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 hi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 hi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(tac))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac tkb_kb_lia Ha KB :=
clear - Ha KB; unfold tkb_kb in KB; repeat match goal with H : _ /\ _ |- _ => destruct H end;
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *; lia.
Ltac tkb_kept AG Hfr Hpres2 Ku Ku2 KB :=
first
[ lazymatch goal with
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 33%nat) _ _ _ _ _) =>
let Bv := rnB in apply (region_kept_val_at Ex _ _ 33%nat (as_uar_cell Bv) 4 1); [evalE AG | exact Ku | exact Ku2 | lia]
end
| lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 740%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; tkb_kb_lia Ha KB | exact Hpres2]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 834%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; tkb_kb_lia Ha KB | exact Hpres2]
end
| eapply region_kept_aview; [evalE AG | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; kglia_with Ha | exact Hpres2] ].
Ltac tkb_U H :=
rewrite ?U_SAlu, ?U_SMd, ?U_SLit in H; cbn [zalu_raw zmd_raw] in H;
repeat match type of H with context [U ?Ev (SOff ?n 0)] =>
lazymatch goal with Hn : ew Ev n = Z_to_bv 64 ?v |- _ => rewrite (U_atom Ev n v Hn) in H by kglia end end.
Ltac tkb_Ug :=
rewrite ?U_SAlu, ?U_SMd, ?U_SLit; cbn [zalu_raw zmd_raw];
repeat match goal with |- context [U ?Ev (SOff ?n 0)] =>
lazymatch goal with Hn : ew Ev n = Z_to_bv 64 ?v |- _ => rewrite (U_atom Ev n v Hn) by kglia end end.
Ltac tkb_zc H := try change (zcanon (-1)) with 18446744073709551615 in H; repeat match type of H with context [zcanon ?z] =>
lazymatch z with context [zcanon _] => fail | _ => rewrite (zcanon_id z) in H by (unfold M64; kglia) end end.
Ltac tkb_zcg := try change (zcanon (-1)) with 18446744073709551615; repeat match goal with |- context [zcanon ?z] =>
lazymatch z with context [zcanon _] => fail | _ => rewrite (zcanon_id z) by (unfold M64; kglia) end end.
Lemma tkb_sub : forall c l z, zcanon z = 2 ^ 64 - 1 -> 0 <= l <= c -> c < 2 ^ 63 -> zcanon (c + zcanon (l * zcanon z)) = c - l.
Proof.
intros c l z Hz Hl Hc. rewrite Hz. unfold zcanon, M64.
destruct (Z.eq_dec l 0) as [->|Hn].
- rewrite Z.mul_0_l, Zmod_0_l, Z.add_0_r, Z.mod_small by lia. lia.
- replace (l * (2 ^ 64 - 1)) with ((2 ^ 64 - l) + (l - 1) * 2 ^ 64) by ring.
rewrite Z_mod_plus_full, (Z.mod_small (2 ^ 64 - l)) by lia.
replace (c + (2 ^ 64 - l)) with ((c - l) + 1 * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma tkb_sub2 : forall c l, 0 <= l <= c -> c < 2 ^ 63 -> zcanon (c + zcanon (l * 18446744073709551615)) = c - l.
Proof.
intros c l Hl Hc. unfold zcanon, M64.
destruct (Z.eq_dec l 0) as [->|Hl0].
{ rewrite Z.mul_0_l, Zmod_0_l, Z.add_0_r, Z.sub_0_r. apply Z.mod_small. lia. }
replace (l * 18446744073709551615) with ((2 ^ 64 - l) + (l - 1) * 2 ^ 64) by ring.
rewrite Z_mod_plus_full, (Z.mod_small (2 ^ 64 - l)) by lia.
replace (c + (2 ^ 64 - l)) with ((c - l) + 1 * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma tkb_sub3 : forall c l1 l2, 0 <= l1 -> 0 <= l2 -> l1 + l2 <= c -> c < 2 ^ 63 ->
zcanon (zcanon (c + zcanon (l1 * 18446744073709551615)) + zcanon (l2 * 18446744073709551615)) = c - (l1 + l2).
Proof.
intros c l1 l2 H1 H2 H3 H4. rewrite (tkb_sub2 c l1) by lia. rewrite (tkb_sub2 (c - l1) l2) by lia. lia.
Qed.
Lemma tkb_digits_len : forall n x acc, (length (pf_digits n x acc) <= n + length acc)%nat.
Proof.
induction n as [|n IH]; intros x acc; cbn [pf_digits]; [lia|].
destruct (x <? 10); cbn [length]; [lia|]. specialize (IH (x / 10) ((48 + x mod 10) :: acc)). cbn [length] in IH. lia.
Qed.
Lemma tkb_dec_len : forall v, 0 <= v -> (length (pf_dec v) <= 11)%nat.
Proof.
intros v Hv. unfold pf_dec. destruct (Z.ltb_spec v 0) as [H|H]; [lia|].
pose proof (tkb_digits_len 11 v []) as L. cbn [length] in L. lia.
Qed.
Lemma tkb_tok_ok : forall (e : entry) (tk rest : list Z),
model_of reac_disco_table_json_c.box_tok e = (tk, rest) ->
(length tk <= 11)%nat /\ Forall (fun c => 0 < c < 256) tk.
Proof.
intros e tk rest H. unfold model_of in H.
destruct (e_has_decl e =? 0).
{ injection H as <- _. unfold s_unknown. cbn [length]. split; [lia|]. repeat apply Forall_cons; try apply Forall_nil; lia. }
destruct (reac_disco_table_json_c.box_tok (e_family e) (e_decl_in e) (e_decl_out e)) as [tv|] eqn:Hb.
- injection H as <- _.
unfold reac_disco_table_json_c.box_tok in Hb.
destruct (Z.eqb_spec (bn_ret (e_family e) [] (e_decl_in e) (e_decl_out e)) 0) as [Hr|Hr]; [|discriminate Hb].
injection Hb as <-.
destruct (tj_lemmas.tj_box_ok (e_family e) (e_decl_in e) (e_decl_out e) Hr) as (Ha & Hbb & Hz).
destruct (bn_c17 (e_family e) (e_decl_in e) (e_decl_out e) Ha Hbb Hz) as (_ & _ & Hlen & _ & Hch).
split; [exact Hlen | exact (tj_lemmas.tok_rng _ Hch)].
- injection H as <- _. unfold s_unknown. cbn [length]. split; [lia|]. repeat apply Forall_cons; try apply Forall_nil; lia.
Qed.
Definition tkb_wtext (a b : Z) : list Z :=
[44; 34; 119; 105; 100; 116; 104; 34; 58; 34] ++ pf_dec a ++ [120] ++ pf_dec b ++ [34].
Lemma tkb_P4 : forall (e : entry) tk,
model_of reac_disco_table_json_c.box_tok e = (tk, dec (e_decl_in e) ++ [120] ++ dec (e_decl_out e)) ->
0 <= e_decl_in e < 256 -> 0 <= e_decl_out e < 256 ->
P4 reac_disco_table_json_c.box_tok e = tkb_wtext (e_decl_in e) (e_decl_out e).
Proof.
intros e tk H H1 H2. unfold P4, key, qstr, k_width, tkb_wtext. rewrite H. cbn [snd].
rewrite !tj_lemmas.dec_pfdec by lia. rewrite <- ?app_assoc. reflexivity.
Qed.
Lemma tkb_wtext_pf : forall a b,
pf_text [PLit 44; PLit 34; PLit 119; PLit 105; PLit 100; PLit 116; PLit 104; PLit 34; PLit 58; PLit 34; Pd; PLit 120; Pd; PLit 34]
[AInt a; AInt b] = Some (tkb_wtext a b).
Proof. intros a b. unfold tkb_wtext. cbn [pf_text option_map]. rewrite <- ?app_assoc. reflexivity. Qed.
Lemma tkb_wtext_len : forall a b, 0 <= a -> 0 <= b -> Z.of_nat (length (tkb_wtext a b)) <= 35.
Proof.
intros a b Ha Hb. unfold tkb_wtext. rewrite !length_app. cbn [length].
pose proof (tkb_dec_len a Ha). pose proof (tkb_dec_len b Hb). lia.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Lemma tkb_garr8_u1 : forall (m : word -> option byte) (a k : Z) (T : list byte),
garr8 SEGS m a (map bv_unsigned T) -> 0 <= k -> k + 1 <= Z.of_nat (length T) ->
val_mem SEGS m (a + k) 1 (disco_table_c.u_at T k 1) /\ 0 <= disco_table_c.u_at T k 1 < 256.
Proof.
intros m a k T HG Hk HkT.
assert (Hlen : length (disco_table_c.sub T k 1) = 1%nat) by (unfold disco_table_c.sub; rewrite length_firstn, length_skipn; lia).
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k 1)) as H0.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k 1)) as H1. rewrite Hlen in H1.
split; [|unfold disco_table_c.u_at; change (2 ^ (8 * Z.of_nat 1)) with 256 in H1; lia].
intros j Hj.
assert (Hlt : (Z.to_nat k + j < length (map bv_unsigned T))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte SEGS m a _ (Z.to_nat k + j) HG Hlt) as Hb.
replace (a + Z.of_nat (Z.to_nat k + j)) with (a + k + Z.of_nat j) in Hb by lia.
rewrite Hb. f_equal.
assert (Hnth : nth_error (disco_table_c.sub T k 1) j = Some (nth (Z.to_nat k + j) T (Z_to_bv 8 0))).
{ unfold disco_table_c.sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec j 1); [|lia].
rewrite nth_error_skipn. apply nth_error_nth'. lia. }
pose proof (YA0j.nth_error_le_byte _ _ _ Hnth) as Hv.
rewrite (nth_indep (map bv_unsigned T) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite map_nth. rewrite Hv. unfold disco_table_c.u_at, YO0f.le_byte.
assert (Ej : j = 0%nat) by lia. subst j.
rewrite ?Z.shiftr_div_pow2 by lia. f_equal. cbn [Z.of_nat]. change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * 0)) with 1. lia.
Qed.
Lemma tkb_garr8_app : forall H H' (m m' : word -> option byte) p (acc T : list Z),
garr8 SEGS (mrestrict H m) p (acc ++ [0]) ->
(forall a, p <= a < p + Z.of_nat (length acc) -> aview SEGS H' m' a = aview SEGS H m a) ->
(forall i, 0 <= i < Z.of_nat (length T) -> aview SEGS H' m' (p + Z.of_nat (length acc) + i) = Some (nth (Z.to_nat i) T 0)) ->
aview SEGS H' m' (p + Z.of_nat (length acc) + Z.of_nat (length T)) = Some 0 ->
garr8 SEGS (mrestrict H' m') p (acc ++ T ++ [0]).
Proof.
intros H H' m m' p acc T HG HK HT H0 j Hj.
rewrite !length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length acc)) as [Hja|Hja].
- rewrite app_nth1 by exact Hja. destruct (HG j ltac:(rewrite length_app; cbn [length]; lia)) as [Hv Hr].
rewrite app_nth1 in Hv, Hr by exact Hja.
split; [|exact Hr]. apply (val_mem_aview_kept_x SEGS H H' m m' (p + Z.of_nat j) 1 _); [|exact Hv].
intros x Hx. apply HK. lia.
- rewrite app_nth2 by exact Hja.
destruct (Nat.lt_ge_cases (j - length acc) (length T)) as [HjT|HjT].
+ rewrite app_nth1 by exact HjT.
pose proof (HT (Z.of_nat (j - length acc)) ltac:(lia)) as Hb. rewrite Nat2Z.id in Hb.
replace (p + Z.of_nat (length acc) + Z.of_nat (j - length acc)) with (p + Z.of_nat j) in Hb by lia.
exact (val_mem1_of_aview SEGS H' m' (p + Z.of_nat j) _ Hb).
+ rewrite app_nth2 by exact HjT. replace (j - length acc - length T)%nat with 0%nat by lia. cbn [nth].
replace (p + Z.of_nat j) with (p + Z.of_nat (length acc) + Z.of_nat (length T)) by lia.
exact (val_mem1_of_aview SEGS H' m' _ _ H0).
Qed.
Definition ss_tkbT9 : sstate := Eval vm_compute in ss_havoc_regs ss_tjT 950 [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 26; 24; 27; 28; 29; 30; 31]%nat.
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Variables SNPC GC GV IMGLO IMGHI : Z.
Variable CR : list (Z * Z).
Hypothesis HSNPC : SIGMA AS___interceptor_trampoline_snprintf = SNPC.
Hypothesis ASNP : forall fq : YK11.FPState,
SnprintfDefR.sh_asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi (SnFF.FF_disco disco_fmt_lo disco_fmt_hi) SNPRINTF_STK GC GV IMGLO IMGHI CR SNPC.
Hypothesis tj_snp_consts : forall (W : world SEGS) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> consts_view SEGS W mem CR.
Hypothesis tj_snp_cr : Forall (fun r => IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= IMG_TOP) CR.
Hypothesis tj_snp_canary : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
exists cval, rdword (aview SEGS (w_H W) mem) GC = Some GV /\ rdword (aview SEGS (w_H W) mem) GV = Some cval.
Hypothesis tj_snp_gcgv : IMG_LO <= GC /\ GC + 8 <= IMG_TOP /\ IMG_LO <= GV /\ GV + 8 <= IMG_TOP.
Hypothesis tj_snp_img : IMG_LO <= IMGLO /\ IMGHI <= IMG_TOP.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DRO : tfib_ro_unowned B.
Hypothesis TJS : tj_strs.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Lemma tkb_ro_fmt : forall (W : world SEGS) (mem : word -> option byte) (k : nat) (s : list Z) (rs : list (Z * Z)),
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> tj_ro_at k s ->
Forall (zdisjoint (VAL (A_OBJ k), Z.of_nat (length s) + 1)) rs ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) ->
shadow_hull_vis (aview SEGS (w_H W) mem) (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) ->
fmt_at (aview SEGS (w_H W) mem) rs (VAL (A_OBJ k)) s.
Proof.
intros W mem k s rs HROD Hro Hdisj Hra Hhull.
destruct Hro as (Hg & Hin & Hlo & Hhi & Hch & Hb).
unfold IMG_LO, IMG_TOP in Hlo, Hhi.
unfold fmt_at. split; [lia|]. split.
- intros j Hj.
rewrite (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) (VAL (A_OBJ k) + j)
HROD (Hin (VAL (A_OBJ k) + j) ltac:(lia))
(tfib_ro_unowned_at B _ _ DRO ltac:(unfold tfib_ro_ranges; apply in_or_app; left; exact Hg)) ltac:(lia)).
pose proof (Hb (Z.to_nat j) ltac:(rewrite length_app; cbn [length]; lia)) as Hq.
replace (VAL (A_OBJ k) + Z.of_nat (Z.to_nat j)) with (VAL (A_OBJ k) + j) in Hq by lia.
exact Hq.
- split; [exact Hdisj|]. split; [unfold amem_range; left; unfold kLowMemEnd; lia|]. split; [exact Hra | exact Hhull].
Qed.
Lemma tkb_keep_journal : forall (cx : tjcx) own ly' S' (W' : world SEGS) mem' md' k,
tj_baseX B IMG cx ->
ajournal SEGS B REAC_DISCO_TABLE_JSON_STK (spZ (c_regs cx)) (tj_fp (c_buf cx) (c_cap cx)) (c_ly cx) (c_S cx)
(c_W cx) (c_mem cx) (c_md cx) own ly' S' W' mem' md' k ->
tj_keep B cx W' mem'.
Proof.
intros cx own ly' S' W' mem' md' k HB HJ.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
unfold tj_baseX in HB. unfold tj_keep.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0] in HB, HJ |- *.
destruct HB as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
pose proof HPRE as (HAR & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof Hobj as ((cid & pos & Hin & Hcid & Hal8 & Hflo & Hfhi) & Ht8 & Hra).
assert (HnF : forall x, inFP (tj_fp buf cap) x -> (x < kLowShadowBeg \/ kHighShadowEnd <= x) /\
~ (frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid)).
{ intros x Hx. unfold tj_fp in Hx. destruct (Z.ltb_spec cap 3) as [Hc|Hc]; [destruct Hx as (r & [] & _)|].
destruct (Hbuf Hc) as (Hbin & Hbsz).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md buf Nb cid pos HAR Hbin Hin) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF.
destruct Hx as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
unfold in_app, kLowShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *. split; lia. }
split; [exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD)|].
split.
- intros j Hj. destruct (Harr j Hj) as (Hv & Hr). split; [|exact Hr].
rewrite length_map, HlenT in Hj.
eapply val_mem_entry_frame; [exact HJ | exact Hin | lia | lia | | exact Hv].
intros x Hx HF. destruct (HnF x HF) as (_ & Hn). apply Hn. lia.
- split; [exists cid, pos; repeat split; assumption|]. split; [exact Ht8|].
eapply range_addressable_entry_frame;
[exact LAWS | exact HJ | exact Hin | exact Hcid | exact Hflo | exact Hfhi | exact Hal8 | | exact HAR | exact Hra].
intros x HF. exact (proj1 (HnF x HF)).
Qed.
Theorem pb_tj_tok_b : tj_seg_tok B IMG.
Proof.
unfold tj_seg_tok. intros i FX FT.
unfold tj_fromK, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0. unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0.
unfold INV_tjK, tj_lbody, tj_wrote, tj_e, tj_age, tj_after2, tj_after4 in HINV.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
pose proof HB0 as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
pose proof HX0 as (AG34 & E60 & E516 & E528 & E529 & HEI).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite (AG34 33%nat ltac:(kglia)); exact HE033).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E0 n) by (intros n Hn; apply AG34; kglia). clear AG34.
destruct HINV as (Hk0 & (Hperm & HKEEP & Hcap3 & Hi & E721 & E722 & E740 & E741) & E834 & E832 &
(tok & Hmodel & Hgtok & Hratok & Hhulltok) & acc & E833 & (Hacc & Htxt & Hgarr)).
pose proof Hok as (Hn8 & _). unfold disco_table_c.tbl_T1 in Hn8.
pose proof HKEEP as HKP0. unfold tj_keep in HKP0. cbn [c_t c_T c_ly c_S] in HKP0. destruct HKP0 as (_ & Hgt0 & _).
destruct (tkb_garr8_u1 _ t (48 * i + 13) T Hgt0 ltac:(clear - Hi Hn8; lia)
ltac:(rewrite HlenT; change (Z.of_nat 400) with 400; clear - Hi Hn8; lia)) as (Vdin & Rdin).
destruct (tkb_garr8_u1 _ t (48 * i + 14) T Hgt0 ltac:(clear - Hi Hn8; lia)
ltac:(rewrite HlenT; change (Z.of_nat 400) with 400; clear - Hi Hn8; lia)) as (Vdout & Rdout).
clear Hgt0.
set (din := disco_table_c.u_at T (48 * i + 13) 1) in *.
set (dout := disco_table_c.u_at T (48 * i + 14) 1) in *.
rename E into Eold.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 900 Ev ssv msv [Z_to_bv 64 din; Z_to_bv 64 dout] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E900 : ew Ev 900 = Z_to_bv 64 din) by (rewrite HEv; exact (ew_havoc_new _ 900 [Z_to_bv 64 din; Z_to_bv 64 dout] 0 (Z_to_bv 64 0) ltac:(cbn; kglia)));
assert (E901 : ew Ev 901 = Z_to_bv 64 dout) by (rewrite HEv; exact (ew_havoc_new _ 900 [Z_to_bv 64 din; Z_to_bv 64 dout] 1 (Z_to_bv 64 0) ltac:(cbn; kglia))) end.
clear HEv.
lazymatch goal with H : img_env _ _ E |- _ => rename H into HEIk end. clear HEI. rename HEIk into HEI.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 11776 + 640 <= REAC_DISCO_TABLE_JSON_STK) by (unfold REAC_DISCO_TABLE_JSON_STK; kglia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk3 & _ & _ & _ & _ & _ & Hpres3 & _ & _ & HQT3).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *. set (FLg := flag_addr ly 2 fpos) in *.
unfold tj_F in Hgtok, Hratok, Hhulltok. cbn [c_ly c_fpos] in Hgtok, Hratok, Hhulltok.
fold F in Hgtok, Hratok, Hhulltok.
try (unfold tj_e in Htxt; cbn [c_T] in Htxt).
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(kglia)); exact (HE0 1%nat 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (AG 2%nat ltac:(kglia)); exact (HE0 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (AG 3%nat ltac:(kglia)); exact (HE0 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (AG 4%nat ltac:(kglia)); exact (HE0 4%nat 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(kglia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (E12 : ew E 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(kglia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(kglia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(kglia)); exact HE032).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat ltac:(kglia)); exact HE02).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite (AG n ltac:(kglia)); exact (HE0 n r Hn)).
img_factsF E.
pose proof (pa_obj_img 0 ltac:(kglia)) as Hob241. pose proof (pa_obj_img 1 ltac:(kglia)) as Hob242.
pose proof (pa_obj_img 12 ltac:(kglia)) as Hob253.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob253.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob253, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres. fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh. fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img. rewrite EFA in HFhigh_img. fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(kglia)); kglia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by kglia; rewrite Z.div_mul by kglia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; kglia).
assert (HF8hi : F / 8 <= 17592184995808) by (apply Z.div_le_upper_bound; kglia).
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & HNb).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HAR3 Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HAR3 Hinb Hfin) as Hbsep.
rewrite EFA0 in Hbsep. fold F in Hbsep. change (fs_frame_bytes 2) with 256 in Hbsep.
unfold zdisjoint in Hbsep. cbn [fst snd] in Hbsep.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp. unfold off_img, IMG_LO, IMG_TOP in Hbimg.
set (e := t + 48 * i) in *.
assert (He : e = t + 48 * i) by reflexivity.
unfold tj_keep in HKEEP. cbn [c_t c_T c_ly c_S] in HKEEP.
destruct HKEEP as (HROD1 & Hgt1 & Hobj1).
pose proof Hobj1 as ((tcid & tpos & Htin & Htcid & HTF8 & HTFlo & HTFhi) & Ht8 & Htra).
assert (Htin3 : In (tcid, tpos) (frames S3)) by (rewrite HFR; right; exact Htin).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ tcid tpos HAR3 Htin3) as (HT4096 & HTceil & HTapp).
rewrite EFA in HT4096, HTceil, HTapp.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Htin3) as HTimg. rewrite EFA in HTimg.
set (TF := frame_addr ly tcid tpos) in *.
assert (Ht4096 : 4096 <= t) by (clear - HT4096 HTFlo; lia).
assert (Htceil : t + 400 <= 140737479966720) by (clear - HTceil HTFhi C1; unfold ASAN_CEIL in *; lia).
destruct (tkb_tok_ok (reac_disco_table_json_c.tj_entry T i) tok _ Hmodel) as (Htoklen & Htokch).
unfold w64 in E721, E722, E740, E741, E832, E833, E834.
set (L := Z.of_nat (length acc)) in *.
assert (HLrng : 0 <= L < cap) by (unfold L; kglia).
assert (Herng : 4096 <= e <= 140737479966720 /\ e mod 8 = 0)
by (unfold e; clear - Ht4096 Htceil Hi Hn8 Ht8; split; lia).
assert (He8 : e mod 8 = 0) by exact (proj2 Herng).
assert (Hd13 : (e + 13) / 8 = e / 8 + 1) by (clear - He8; lia).
assert (Hd14 : (e + 14) / 8 = e / 8 + 1) by (clear - He8; lia).
rewrite Hd13 in E834. rewrite Hd14 in E832. clear Hd13 Hd14.
replace (t + (48 * i + 13)) with (e + 13) in Vdin by (rewrite He; kglia).
replace (t + (48 * i + 14)) with (e + 14) in Vdout by (rewrite He; kglia).
assert (Hsh0 : aview SEGS (w_H W3) (ms_mem ms3) (SB + (e / 8 + 1)) = Some 0).
{ destruct (Htra (e + 15) ltac:(clear - He Hi Hn8; lia)) as (s & Hs & Hsk).
unfold shadow_of_addr in Hs. rewrite <- SB_SHADOW_OFF in Hs.
replace (SB + (e + 15) / 8) with (SB + (e / 8 + 1)) in Hs by (clear - He8; lia).
unfold saddr_ok in Hsk. destruct Hsk as [Hs0 | (Hm & Hs8)]; [rewrite <- Hs0; exact Hs|].
exfalso. clear - He8 Hm Hs8. kglia. }
assert (HdTF : zdisjoint (frame_rng ly3 (2, fpos)) (frame_rng ly3 (tcid, tpos))).
{ destruct (in_split _ _ Htin) as (l2 & l3 & Hspl).
eapply (sep_frames_pos SEGS B LAWS _ _ _ _ _ (2, fpos) (tcid, tpos) [] l2 l3 HAR3). rewrite HFR, Hspl. reflexivity. }
unfold zdisjoint, frame_rng in HdTF. cbn [fst snd] in HdTF. rewrite !EFA in HdTF. fold F TF in HdTF. change (fs_frame_bytes 2) with 256 in HdTF.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb tcid tpos HAR3 Hinb Htin3) as HdBT.
rewrite EFA in HdBT. fold TF in HdBT. unfold zdisjoint in HdBT. cbn [fst snd] in HdBT.
idtac "TOKB-FACTS".
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 834%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E834, unsigned_lit_small by (clear - Herng; unfold SB; lia);
split; [clear - Herng; unfold SB; lia|]; split; [clear - Herng; unfold SB; lia|]; split; [intros o Ho; kglia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ (SB + (e / 8 + 1)) 0 1 (SLit 0) 0);
[reflexivity | cbn; kglia | cbn; kglia | rewrite Z.add_0_r; exact (proj1 (val_mem1_of_aview SEGS _ _ _ _ Hsh0))])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E834; evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 Hob241 Hob242 Hob253 Huar
HT4096 HTceil HTapp HTimg HTFlo HTFhi HdTF Hi Hn8 He He8 Herng;
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB, ASAN_CEIL in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
idtac "TOKB-R834".
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 740%nat) 13 15 0 0 [YP09.mkChunk 13 (CVal 1 (SOff 900 0)); YP09.mkChunk 14 (CVal 1 (SOff 901 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E740, unsigned_lit_small by (clear - Herng; lia);
split; [clear - Herng; lia|]; split; [clear - Herng; lia|]; split; [intros o Ho; kglia|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 13 1 _ din); [cbn [sv_denot]; rewrite E900, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; kglia | cbn; kglia | exact Vdin]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 14 1 _ dout); [cbn [sv_denot]; rewrite E901, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; kglia | cbn; kglia | exact Vdout]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E740, ?E834; evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 Hob241 Hob242 Hob253 Huar
HT4096 HTceil HTapp HTimg HTFlo HTFhi HdTF Hi Hn8 He He8 Herng;
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB, ASAN_CEIL in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
idtac "TOKB-R740".
prreg HS (27%bv : bv 5) Q27.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_set_reg Ev ssv msv (27%bv : bv 5) (SOff 834 0) HS ltac:(intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate Hc)
ltac:(cbn [ms_regs restrict]; rewrite Q27; cbn [sv_denot]; rewrite ?E832, ?E834, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. norm_ss HS. clear Q27.
idtac "TOKB-X27".
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 900 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E900, unsigned_lit_small by kglia; rewrite Z.pow_0_r, Z.mod_1_r; kglia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 901 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E901, unsigned_lit_small by kglia; rewrite Z.pow_0_r, Z.mod_1_r; kglia)) as HS3;
clear HS; rename HS3 into HS end.
fs_roF HS.
tkb_wnone HS 516%nat.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 833 (mkAF 0 2147483647 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E833, unsigned_lit_small by (clear - HLrng Hcap; lia);
rewrite Z.pow_0_r, Z.mod_1_r; clear - HLrng Hcap; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 740 (PTR 3) HS
ltac:(unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite E740, unsigned_lit_small by (clear - Herng; lia);
change (2 ^ 3) with 8; clear - Herng; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
pose proof (tkb_kb_intro _ (conj HdBT (conj HTFlo (conj HTFhi (conj HTceil (conj HT4096 (conj HTapp (conj Hceil (conj Hslo (conj HSK
(conj Hsp1 (conj Hshi (conj H47 (conj Hi (conj Hn8 (conj He (conj He8 (conj Herng (conj Hcapb (conj HLrng (conj Hbapp
(conj Hb4096 (conj C1 C3))))))))))))))))))))))) as KB.
pose proof (conj HF4096 (conj HFceil (conj HFhigh (conj HFhigh_img (conj HF8lo (conj HF8hi (conj Hbsep (conj Hbimg (conj Hbceil
(conj Htoklen (conj HdTF (conj HTimg (conj Hob241 (conj Hob242 (conj Hob253 (conj Huar (conj Hstk0 (conj Ht4096 (conj Htceil
(conj Hcap (conj C2 (conj C4 (conj C5 (conj HSNP (conj Hes KB))))))))))))))))))))))))) as HGK.
unfold tkb_kb in HGK. box HGK.
clear HdBT HdTF.
idtac "TOK-K-SETUP".
paj_run_shc RUNP RUNC HS HJ. { tkb_awr ltac:(idtac; tkb_hd AG HSK) AG fpos F EFA0. }
idtac "TOK-RUN-1".
tkb_mvtok HFr AG Hgtok Hratok Hhulltok Hgtok1 Hratok1 Hhulltok1 (F + 96) (tok ++ [0]) (Z.of_nat (length tok) + 1).
tkb_HK HFr AG buf cap HK1.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc.
rewrite (U_atom _ 833 L E833) in Hc by kglia.
rewrite (U_atom _ 12 buf E12) in Hc by kglia_t.
rewrite zcanon_id in Hc by kglia_t.
kglia. }
clear Hc.
idtac "TOK-TRAP-1".
paj_run_shc RUNP RUNC HS HJ. { tkb_awr ltac:(idtac; tkb_hd AG HSK) AG fpos F EFA0. }
idtac "TOK-RUN-2".
tkb_mvtok HFr AG Hgtok1 Hratok1 Hhulltok1 Hgtok2 Hratok2 Hhulltok2 (F + 96) (tok ++ [0]) (Z.of_nat (length tok) + 1).
tkb_HK HFr AG buf cap HK2.
clear HF HFr HG.
pose proof (proj1 HJ) as HARc.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARc Hfin) as (_ & _ & HFpresC & _).
rewrite EFA in HFpresC. fold F in HFpresC. change (fs_frame_bytes 2) with 256 in HFpresC.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HRODc.
destruct (tj_snp_canary _ _ _ _ _ HARc) as (cval & HG1 & HG2).
pose proof tj_snp_gcgv as (Hgc1 & Hgc2 & Hgv1 & Hgv2). unfold IMG_LO, IMG_TOP in Hgc1, Hgc2, Hgv1, Hgv2.
gadd (conj Hgc1 (conj Hgc2 (conj Hgv1 Hgv2))).
pose proof TJS as (_ & _ & _ & _ & Hfm & Hfw & _).
pose proof Hfm as Hfm'. unfold tj_ro_at, tj_f_model in Hfm'. cbn [length Z.of_nat] in Hfm'.
destruct Hfm' as (Hg49 & Hro49 & Hlo49 & Hhi49 & Hch49 & Hb49).
unfold IMG_LO, IMG_TOP in Hlo49, Hhi49.
gadd (conj Hlo49 Hhi49).
pose proof (img_env_atomP E 290 HEI ltac:(unfold A_TEXT, A_LIM; kglia)) as E290.
destruct (ro_read_ok_glob SEGS B tfib_globs _ _ _ _ _ (VAL (A_OBJ 49)) _ (VAL (A_OBJ 49)) 14 GM Hg49 HV HARc
ltac:(kglia) ltac:(kglia) ltac:(kglia) ltac:(unfold IMG_LO; kglia) ltac:(unfold IMG_TOP; kglia)) as [Hfra Hfrh].
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (1%bv : bv 5) Qra.
prreg HS (12%bv : bv 5) Qa2.
rregU HS (10%bv : bv 5) (buf + L)
ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom _ 833 L E833), (U_atom _ 12 buf E12) by kglia_t;
rewrite zcanon_id by kglia_t; kglia) Ra0.
rregU HS (11%bv : bv 5) (cap - L)
ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw];
rewrite (U_atom _ 13 cap E13), (U_atom _ 833 L E833) by kglia; rewrite U_SLit;
apply tkb_sub; [reflexivity | kglia | kglia]) Ra1.
rregU HS (13%bv : bv 5) (F + 96)
ltac:(apply U_atom_off; [exact E516 | kglia | kglia]) Ra3.
idtac "TOK-REGS-1".
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
pmkst HS. rewrite HSNPC.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rgX _ ?mmX _) _) _ =>
eapply (aj_sh_snprintf_at B LAWS pa_segs_low REAC_DISCO_TABLE_JSON_STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq)
W3 rgX mmX (spZ regs) (tj_fp buf cap)
ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + L) (cap - L) (VAL (A_OBJ 49)) tj_f_model
[PLit 44; PLit 34; PLit 109; PLit 111; PLit 100; PLit 101; PLit 108; PLit 34; PLit 58; PLit 34; Ps; PLit 34]
[] (map (argZ rgX) [3; 4; 5; 6; 7] ++ []) [APtr tok]
([44; 34; 109; 111; 100; 101; 108; 34; 58; 34] ++ tok ++ [34]) cval (sp1 - spZ regs)
(Z_to_bv 64 (BASE + 24512)) _ HJ HRODc) end.
{ unfold spZ at 1. rewrite Qsp, E60, unsigned_lit_small by kglia. kglia. }
{ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ kglia. }
{ unfold REAC_DISCO_TABLE_JSON_STK. kglia. }
{ rewrite Qgp, E3. exact Hgp. }
{ rewrite Qtp, E4. exact Htp. }
{ exact Qra. }
{ apply ret_ok_codeptr_v; [kglia | reflexivity]. }
{ exact Ra0. }
{ exact Ra1. }
{ rewrite Qa2, E290. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. clear - Hr; lia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr.
unfold snp_out. tkb_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; kglia_with_t Hr). }
{ exact HG1. }
{ exact HG2. }
{ kglia. }
{ kglia. }
{ kglia. }
{ kglia. }
{ unfold snp_out. tkb_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; kglia_t). }
{ unfold snp_out. tkb_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; kglia_t). }
{ apply (tkb_ro_fmt _ _ 49 tj_f_model);
[exact HRODc | exact Hfm | unfold snp_out, tj_f_model; cbn [length Z.of_nat];
tkb_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; kglia_t) | exact Hfra | exact Hfrh]. }
{ exact (tj_ro_fmt_rng 49 tj_f_model Hfm ltac:(cbv; kglia)). }
{ unfold tj_f_model. discriminate. }
{ vm_compute. reflexivity. }
{ repeat constructor. }
{ split; [reflexivity | intros j Hj; cbn in Hj; kglia]. }
{ cbn. kglia. }
{ unfold snp_out. tkb_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; kglia_t). }
{ cbn [pf_args_asan map]. split; [|exact I]. cbn [pf_arg_asan].
unfold argZ. change (Z_to_bv 5 (10 + 3)) with (Z_to_bv 5 13).
replace (Z_to_bv 5 13) with (13%bv : Prelude.reg) by (apply bv_eq; vm_compute; reflexivity).
rewrite Ra3. unfold w64. rewrite unsigned_lit_small by kglia_t.
split; [exact Htokch|]. split; [kglia|]. split; [kglia|]. split.
{ intros j Hj.
destruct (Hgtok2 (Z.to_nat j) ltac:(rewrite length_app; cbn [length]; kglia)) as (Hv & Hr).
replace (F + 96 + j) with (F + 96 + Z.of_nat (Z.to_nat j)) by kglia.
apply (aview_of_val_mem1 SEGS); [exact Hv | exact Hr]. }
split.
{ intros x Hx. apply aview_some_of_apresent.
apply (proj1 (HFpresC x ltac:(unfold str_end in Hx; clear - Hx Htoklen; lia))). }
split; [unfold snp_out; tkb_fa2 ltac:(unfold zdisjoint, str_end; cbn [fst snd]; kglia_t)|].
split; [kglia_m|].
split; [exact Hratok2 | exact Hhulltok2]. }
{ cbn [map app SnFF.pf_args_amem]. split; [|exact I].
unfold argZ. change (Z_to_bv 5 (10 + 3)) with (Z_to_bv 5 13).
replace (Z_to_bv 5 13) with (13%bv : Prelude.reg) by (apply bv_eq; vm_compute; reflexivity).
rewrite Ra3. unfold w64. rewrite unsigned_lit_small by kglia_t. kglia_m. }
{ cbn [pf_text]. reflexivity. }
{ kglia. }
{ rewrite length_app. cbn [length]. rewrite length_app. cbn [length]. kglia. }
{ kglia. }
{ kglia_t. }
{ unfold snp_out. cbn [pairwise]. split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; kglia_t | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|kglia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; kglia].
+ exists buf, Nb. split; [exact Hinb | kglia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); kglia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); kglia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); kglia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hinb | kglia | kglia]. }
{ exact Hfrm. }
idtac "TOK-CALL-1".
intros fx1 regs2 mem2 md2 Hf1 Hf2 HJ2 HP2 Ha0' Hwr Hnul Hfr Hpres2 Hsame.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr by kglia. rewrite HSNP in Hfr.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG ltac:(idtac; tkb_kept AG Hfr Hpres2 Kuar0 Kuar2 KB).
apply (st_ok_pi_restrict_fx fq fx1) in HS.
clear RUNP RUNTOP RUNC BR.
pose (BR := paj_branch (fx := fx1) (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx1) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx1) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx1) B LAWS).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E12v : ew Ev 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat) by kglia; rewrite (HE0 12%nat 12%bv eq_refl); exact H12);
assert (E13v : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by kglia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13) end.
clear E12 E13. rename E12v into E12. rename E13v into E13.
idtac "TOK-RESEAT-1".
pose proof (proj1 HJ2) as HARd.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARd Hfin) as (_ & _ & HFpresD & HFSpresD).
rewrite EFA in HFpresD, HFSpresD. fold F in HFpresD, HFSpresD.
change (fs_frame_bytes 2) with 256 in HFpresD. change (fs_frame_bytes 2 / 8) with 32 in HFSpresD.
tkb_wfull HS 516%nat 256 ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by kglia;
rewrite E516, unsigned_lit_small by kglia_t;
intros o Ho; apply (apresent_writable _); apply (proj1 (HFpresD (F + o) ltac:(kglia)))).
tkb_wfull HS 529%nat 32 ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by kglia;
rewrite E529, unsigned_lit_small by (unfold SB; kglia);
intros o Ho; apply (apresent_writable _); unfold shadow_addr in HFSpresD; rewrite <- SB_SHADOW_OFF in HFSpresD;
apply (proj1 (HFSpresD o ltac:(kglia)))).
idtac "TOK-WIN-1".
set (T1 := [44; 34; 109; 111; 100; 101; 108; 34; 58; 34] ++ tok ++ [34]) in *.
assert (HL1 : Z.of_nat (length T1) = 11 + Z.of_nat (length tok)) by (unfold T1; rewrite !length_app; cbn [length]; kglia).
prreg HS (10%bv : bv 5) Qr0. cbn [ms_regs] in Qr0. rewrite Ha0' in Qr0. symmetry in Qr0. unfold w64 in Qr0.
lazymatch type of Qr0 with ew ?Ev ?na = _ =>
pose proof (st_ok_pi_add_fact Ev _ _ na (mkAF 0 2147483647 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Qr0, unsigned_lit_small by kglia;
rewrite Z.pow_0_r, Z.mod_1_r; kglia)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
paj_run_shc RUNP RUNC HS HJ2. { tkb_awr ltac:(idtac; tkb_hd AG HSK) AG fpos F EFA0. }
idtac "TOK-RUN-3".
tkb_HK HFr AG buf cap HK3. clear HF HFr HG.
assert (HP3 : P3 reac_disco_table_json_c.box_tok (reac_disco_table_json_c.tj_entry T i) = T1).
{ unfold T1, P3, key, qstr, k_model. rewrite (f_equal fst Hmodel). cbn [fst app]. reflexivity. }
psrr_branch_pi RUNP BR HS.
- rewrite branch_geu_U in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
lazymatch type of Qr0 with ew _ ?na = _ => rewrite (U_atom _ na (Z.of_nat (length T1)) Qr0) in Hc by kglia end.
rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc. rewrite U_SMd in Hc. cbn [zmd_raw] in Hc.
rewrite (U_atom _ 13 cap E13), (U_atom _ 833 L E833) in Hc by kglia. rewrite U_SLit in Hc.
rewrite (tkb_sub cap L (-1) ltac:(reflexivity) ltac:(kglia) ltac:(kglia)) in Hc.
assert (Htl : cap <= tj_len T now).
{ unfold tj_len. rewrite Htxt, !length_app, HP3. unfold L in *. kglia. }
paj_run_to_shc RUNTOP HS HJ2 25204. { tkb_awr ltac:(idtac; tkb_hd AG HSK) AG fpos F EFA0. }
idtac "TOK-RUN-X1".
prreg HS (23%bv : bv 5) R23.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 23; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R23 E653.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx1 Ev k _ _ Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite ew_havoc_old by kglia; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; kglia]|].
rewrite !ew_havoc_old by (cbn; kglia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; kglia].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_cap c_T c_now c_buf c_ly c_S].
split; [exact Hk0|]. split; [exact Hperm|]. exists (-1).
split; [rewrite E653; unfold w64; first [reflexivity | apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity]|].
split; [intros _; reflexivity|]. split; [intros _ Hlt; exfalso; kglia | intros _ _; reflexivity].
+ cbn [c_fq]. exact HS.
- idtac "TOK-FITS-1".
rewrite branch_geu_U in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
lazymatch type of Qr0 with ew _ ?na = _ => rewrite (U_atom _ na (Z.of_nat (length T1)) Qr0) in Hc by kglia end.
rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc. rewrite U_SMd in Hc. cbn [zmd_raw] in Hc.
rewrite (U_atom _ 13 cap E13), (U_atom _ 833 L E833) in Hc by kglia. rewrite U_SLit in Hc.
rewrite (tkb_sub cap L (-1) ltac:(reflexivity) ltac:(kglia) ltac:(kglia)) in Hc.
rename Hc into Hfit1.
rewrite Z.min_l in Hwr, Hnul, Hfr by kglia.
assert (G1 : garr8 SEGS (mrestrict (w_H W3) mem2) buf ((acc ++ T1) ++ [0])).
{ rewrite <- app_assoc. apply (tkb_garr8_app (w_H W3) (w_H W3) (ms_mem ms3) mem2 buf acc T1 Hgarr).
- intros a Ha. fold L in Ha. rewrite (Hfr a ltac:(kglia) ltac:(kglia) ltac:(kglia)). rewrite HK2 by kglia. apply HK1. kglia.
- intros ii Hii. exact (Hwr ii ltac:(kglia)).
- exact Hnul. }
clear Hwr Hnul.
idtac "TOK-G1".
paj_run_shc RUNP RUNC HS HJ2. { tkb_awr ltac:(idtac; tkb_hd AG HSK) AG fpos F EFA0. }
idtac "TOK-RUN-4".
tkb_HK HFr AG buf cap HK4. clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ltu_U in Hc. tkb_U Hc. tkb_zc Hc. apply Z.ltb_lt in Hc. kglia. }
clear Hc.
idtac "TOK-TRAP-3".
paj_run_shc RUNP RUNC HS HJ2. { tkb_awr ltac:(idtac; tkb_hd AG HSK) AG fpos F EFA0. }
idtac "TOK-RUN-5".
tkb_HK HFr AG buf cap HK5. clear HF HFr HG.
idtac "TOK-RUN-CALL2".
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (List.filter (fun r => match YP09.r_base r with Some n => negb (Nat.eqb n 740 || Nat.eqb n 834) | None => true end) (ss_mem ssx)) in
pose proof (st_ok_submem _ Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. norm_ss HS.
pose proof (proj1 HJ2) as HARc2.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROD) as HRODc2.
destruct (tj_snp_canary _ _ _ _ _ HARc2) as (cval2 & HG3 & HG4).
pose proof Hfw as Hfw'. unfold tj_ro_at, tj_f_width in Hfw'. cbn [length Z.of_nat] in Hfw'.
destruct Hfw' as (Hg50 & Hro50 & Hlo50 & Hhi50 & Hch50 & Hb50).
unfold IMG_LO, IMG_TOP in Hlo50, Hhi50.
gadd (conj Hlo50 Hhi50).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let H := rnHEI Ev in pose proof (img_env_atomP Ev 291 H ltac:(unfold A_TEXT, A_LIM; kglia)) as E291 end.
destruct (ro_read_ok_glob SEGS B tfib_globs _ _ _ _ _ (VAL (A_OBJ 50)) _ (VAL (A_OBJ 50)) 17 GM Hg50 HV HARc2
ltac:(kglia) ltac:(kglia) ltac:(kglia) ltac:(unfold IMG_LO; kglia) ltac:(unfold IMG_TOP; kglia)) as [Hfra2 Hfrh2].
prreg HS (2%bv : bv 5) Qsp2. prreg HS (3%bv : bv 5) Qgp2. prreg HS (4%bv : bv 5) Qtp2. prreg HS (1%bv : bv 5) Qra2.
prreg HS (12%bv : bv 5) Qa22.
rregU HS (10%bv : bv 5) (buf + (L + Z.of_nat (length T1))) ltac:(tkb_Ug; tkb_zcg; kglia) Rb0.
rregU HS (11%bv : bv 5) (cap - (L + Z.of_nat (length T1))) ltac:(tkb_Ug; tkb_zcg; apply tkb_sub3; kglia) Rb1.
rregU HS (13%bv : bv 5) din ltac:(first [apply U_atom; [exact E900 | kglia] | tkb_Ug; kglia | tkb_Ug; tkb_zcg; kglia]) Rd3.
rregU HS (14%bv : bv 5) dout ltac:(first [apply U_atom; [exact E901 | kglia] | tkb_Ug; kglia | tkb_Ug; tkb_zcg; kglia]) Rd4.
idtac "TOK-REGS-2".
aconstsF HJ2 Kgot3 Kcell3 Kguar3 Kuar3.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rgX _ ?mmX _) _) _ =>
eapply (aj_sh_snprintf_at B LAWS pa_segs_low REAC_DISCO_TABLE_JSON_STK fx1 GC GV IMGLO IMGHI CR (SIGMA AS___interceptor_trampoline_snprintf)
(eq_ind_r (fun p => SnprintfDefR.sh_asnprintf_realizesR (fx := fx1) SEGS B pa_relro_lo pa_relro_hi (SnFF.FF_disco disco_fmt_lo disco_fmt_hi) SNPRINTF_STK GC GV IMGLO IMGHI CR p) (ASNP fx1) HSNPC)
W3 rgX mmX (spZ regs) (tj_fp buf cap)
ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + (L + Z.of_nat (length T1))) (cap - (L + Z.of_nat (length T1))) (VAL (A_OBJ 50)) tj_f_width
[PLit 44; PLit 34; PLit 119; PLit 105; PLit 100; PLit 116; PLit 104; PLit 34; PLit 58; PLit 34; Pd; PLit 120; Pd; PLit 34]
[] (map (argZ rgX) [3; 4; 5; 6; 7] ++ []) [AInt din; AInt dout]
(tkb_wtext din dout) cval2 (sp1 - spZ regs)
(Z_to_bv 64 (BASE + 24596)) _ HJ2 HRODc2) end.
{ unfold spZ at 1. rewrite Qsp2, E60, unsigned_lit_small by kglia. kglia. }
{ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ kglia. }
{ unfold REAC_DISCO_TABLE_JSON_STK. kglia. }
{ rewrite Qgp2, (AG 3%nat ltac:(kglia)), (HE0 3%nat 3%bv eq_refl). exact Hgp. }
{ rewrite Qtp2, (AG 4%nat ltac:(kglia)), (HE0 4%nat 4%bv eq_refl). exact Htp. }
{ exact Qra2. }
{ apply ret_ok_codeptr_v; [kglia | reflexivity]. }
{ exact Rb0. }
{ exact Rb1. }
{ rewrite Qa22, E291. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc2). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. clear - Hr; lia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr.
unfold snp_out. tkb_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; kglia_with_t Hr). }
{ exact HG3. }
{ exact HG4. }
{ kglia. }
{ kglia. }
{ kglia. }
{ kglia. }
{ unfold snp_out. tkb_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; kglia_t). }
{ unfold snp_out. tkb_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; kglia_t). }
{ apply (tkb_ro_fmt _ _ 50 tj_f_width);
[exact HRODc2 | exact Hfw | unfold snp_out, tj_f_width; cbn [length Z.of_nat];
tkb_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; kglia_t) | exact Hfra2 | exact Hfrh2]. }
{ exact (tj_ro_fmt_rng 50 tj_f_width Hfw ltac:(cbv; kglia)). }
{ unfold tj_f_width. discriminate. }
{ vm_compute. reflexivity. }
{ repeat constructor. }
{ split; [reflexivity | intros j Hj; cbn in Hj; kglia]. }
{ cbn. kglia. }
{ unfold snp_out. tkb_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; kglia_t). }
{ cbn [pf_args_asan map app]. unfold argZ.
change (Z_to_bv 5 (10 + 3)) with (Z_to_bv 5 13). change (Z_to_bv 5 (10 + 4)) with (Z_to_bv 5 14).
replace (Z_to_bv 5 13) with (13%bv : Prelude.reg) by (apply bv_eq; vm_compute; reflexivity).
replace (Z_to_bv 5 14) with (14%bv : Prelude.reg) by (apply bv_eq; vm_compute; reflexivity).
rewrite Rd3, Rd4. rewrite !unsigned_lit_small by kglia. cbn [pf_arg_asan].
split; [split; [kglia | reflexivity] | split; [split; [kglia | reflexivity] | exact I]]. }
{ cbn [map app SnFF.pf_args_amem]. exact I. }
{ exact (tkb_wtext_pf din dout). }
{ kglia. }
{ pose proof (tkb_wtext_len din dout ltac:(kglia) ltac:(kglia)). kglia. }
{ kglia. }
{ kglia_t. }
{ unfold snp_out. cbn [pairwise]. split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; kglia_t | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|kglia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; kglia].
+ exists buf, Nb. split; [exact Hinb | kglia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); kglia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); kglia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); kglia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc2 | exact Hinb | kglia | kglia]. }
{ exact Hf2. }
idtac "TOK-CALL-2".
intros fx2 regs4 mem4 md4 Hg1 Hg2 HJ4 HP4 Hb0' Hwr4 Hnul4 Hfr4 Hpres4 Hsame4.
assert (Hh1 : forall r : bv 5, bv_unsigned r <> 10 -> Sem.reg_get (@fp_regs fx2) r = Sem.reg_get (@fp_regs fq) r)
by (intros r Hr; rewrite (Hg1 r Hr); exact (Hf1 r Hr)).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr4 by kglia. rewrite HSNP in Hfr4.
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
clear HJ2. rename HJ4 into HJ2.
reseat HS HJ2 HP4 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG ltac:(idtac; tkb_kept AG Hfr4 Hpres4 Kuar3 Kuar4 KB).
apply (st_ok_pi_restrict_fx _ fx2) in HS.
clear RUNP RUNTOP RUNC BR.
pose (BR := paj_branch (fx := fx2) (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx2) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx2) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx2) B LAWS).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E12v : ew Ev 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat) by kglia; rewrite (HE0 12%nat 12%bv eq_refl); exact H12);
assert (E13v : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by kglia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13) end.
clear E12 E13. rename E12v into E12. rename E13v into E13.
idtac "TOK-RESEAT-2".
pose proof (tkb_wtext_len din dout ltac:(kglia) ltac:(kglia)) as HL2.
set (T2 := tkb_wtext din dout) in *.
prreg HS (10%bv : bv 5) Qr1. cbn [ms_regs] in Qr1. rewrite Hb0' in Qr1. symmetry in Qr1. unfold w64 in Qr1.
lazymatch type of Qr1 with ew ?Ev ?na = _ =>
pose proof (st_ok_pi_add_fact Ev _ _ na (mkAF 0 2147483647 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Qr1, unsigned_lit_small by kglia;
rewrite Z.pow_0_r, Z.mod_1_r; kglia)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
paj_run_shc RUNP RUNC HS HJ2. { tkb_awr ltac:(idtac; tkb_hd AG HSK) AG fpos F EFA0. }
idtac "TOK-RUN-8".
tkb_HK HFr AG buf cap HK8. clear HF HFr HG.
assert (HPw : P4 reac_disco_table_json_c.box_tok (reac_disco_table_json_c.tj_entry T i) = T2).
{ unfold T2. rewrite (tkb_P4 _ tok Hmodel); [reflexivity | exact Rdin | exact Rdout]. }
psrr_branch_pi RUNP BR HS.
+ rewrite branch_geu_U in Hc. tkb_U Hc. tkb_zc Hc.
rewrite (tkb_sub3 cap L (Z.of_nat (length T1))) in Hc by kglia.
apply negb_true_iff, Z.ltb_ge in Hc.
assert (Htl : cap <= tj_len T now).
{ unfold tj_len. rewrite Htxt, !length_app, HP3, HPw. unfold L in *. kglia. }
paj_run_to_shc RUNTOP HS HJ2 25204. { tkb_awr ltac:(idtac; tkb_hd AG HSK) AG fpos F EFA0. }
idtac "TOK-RUN-X2".
prreg HS (23%bv : bv 5) R23.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 23; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R23 E653.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx2 Ev k _ _ Wg msF mdF Hh1 Hg2) end end.
* exact HBASE.
* unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite ew_havoc_old by kglia; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; kglia]|].
rewrite !ew_havoc_old by (cbn; kglia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; kglia].
* cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
* cbn [c_S c_fpos]. exact HFR.
* unfold INV_tjX. cbn [c_cap c_T c_now c_buf c_ly c_S].
split; [exact Hk0|]. split; [exact Hperm|]. exists (-1).
split; [rewrite E653; unfold w64; first [reflexivity | apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity]|].
split; [intros _; reflexivity|]. split; [intros _ Hlt; exfalso; kglia | intros _ _; reflexivity].
* cbn [c_fq]. exact HS.
+ idtac "TOK-FITS-2".
rewrite branch_geu_U in Hc. tkb_U Hc. tkb_zc Hc.
rewrite (tkb_sub3 cap L (Z.of_nat (length T1))) in Hc by kglia.
apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hfit2.
rewrite Z.min_l in Hwr4, Hnul4, Hfr4 by kglia.
assert (G2 : garr8 SEGS (mrestrict (w_H W3) mem4) buf ((acc ++ T1 ++ T2) ++ [0])).
{ replace ((acc ++ T1 ++ T2) ++ [0]) with ((acc ++ T1) ++ T2 ++ [0]) by (rewrite <- !app_assoc; reflexivity).
apply (tkb_garr8_app (w_H W3) (w_H W3) mem2 mem4 buf (acc ++ T1) T2 G1).
- intros a Ha. rewrite length_app, Nat2Z.inj_add in Ha. fold L in Ha.
rewrite (Hfr4 a ltac:(kglia) ltac:(kglia) ltac:(kglia)).
rewrite HK5 by kglia. rewrite HK4 by kglia. apply HK3. kglia.
- intros ii Hii. rewrite length_app, Nat2Z.inj_add. fold L. exact (Hwr4 ii ltac:(kglia)).
- rewrite length_app, Nat2Z.inj_add. fold L. exact Hnul4. }
idtac "TOK-G2".
paj_run_to_shc RUNTOP HS HJ2 24608. { tkb_awr ltac:(idtac; tkb_hd AG HSK) AG fpos F EFA0. }
idtac "TOK-RUN-T".
tkb_HK HFr AG buf cap HK9. clear HF HFr HG.
rregU HS (26%bv : bv 5) (L + Z.of_nat (length T1) + Z.of_nat (length T2)) ltac:(tkb_Ug; tkb_zcg; kglia) R26.
ra_join HS ss_tkbT9 1000%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 26; 24; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join HS ss_tjT 840%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 26; 24; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 840%nat 12%nat R26 E852.
idtac "TOK-JOIN-T".
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B IMG _ _ FT (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx2 Ev k _ _ Wg msF mdF Hh1 Hg2) end end.
* exact HBASE.
* unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite !ew_havoc_old by kglia; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; kglia]|].
rewrite !ew_havoc_old by (cbn; kglia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [apply img_env_havoc_hi; [assumption | unfold A_LIM; kglia] | unfold A_LIM; kglia].
* cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
* cbn [c_S c_fpos]. exact HFR.
* unfold INV_tjT, tj_lbody, tj_wrote. cbn [c_cap c_T c_now c_buf c_t c_ly c_S].
split; [exact Hk0|]. split.
{ split; [exact Hperm|]. split; [exact (tkb_keep_journal _ _ _ _ _ _ _ _ HBASE HJ2)|]. split; [exact Hcap3|]. split; [exact Hi|].
rewrite !ew_havoc_old by (cbn; kglia). split; [exact E721|]. split; [exact E722|]. split; [exact E740 | exact E741]. }
exists (acc ++ T1 ++ T2). split.
{ unfold w64. rewrite E852. f_equal. rewrite !length_app, !Nat2Z.inj_add. fold L. kglia. }
split; [rewrite !length_app, !Nat2Z.inj_add; fold L; kglia|].
split; [rewrite Htxt, HP3, HPw; unfold tj_after4, tj_e; cbn [c_T c_now]; rewrite <- !app_assoc; reflexivity|].
apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem4 _ buf); [|exact G2].
intros a Ha. rewrite !length_app, !Nat2Z.inj_add in Ha. fold L in Ha. cbn [length Z.of_nat] in Ha.
rewrite HK9 by kglia. apply HK8. kglia.
* cbn [c_fq]. exact HS.
Qed.
End h.
End f.
End d.
