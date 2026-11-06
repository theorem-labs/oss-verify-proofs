(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/A/ACja.v for libreac/fuzz_grant's program walk, over fuzz_grant's listing. Image objects follow fuzz_grant.asan: the GOT word of the shadow-base cell is object 1 (atom 242), the GOT word of the side-stack flag is object 0 (atom 241), the shadow-base cell is object 32 (atom 273) and the side-stack flag cell is object 33 (atom 274), so img_factsF and img_hull_factsF give E240 E241 E242 E273 E274 and Hob241 Hob242 Hob273 Hob274, keptFL keeps those four regions, and aconstsF rewrites with PALib's pal_got_shadow, pal_cell and GrantFrame's palf_got_uar. awrFL, keptFL, fs_roF and fs_rwF keep the walks' atoms for the own side-stack frame (516), its shadow (529), the realigned stack (60) and the stack (2), for any frame class; stack bounds compute the walk's own STK constant; cgif's case for its 40-byte FRAME block (atom 11) is left out, and awrFL_with/keptFL_with take a tactic for a walk's own head regions. Module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v of a working branch ca2ec2ecd18 and re-keyed to fuzz_ctrl.asan, whose shadow-base cell is object 30 (atom 271) and whose side-stack flag cell is object 31 (atom 272): img_factsF and img_hull_factsF now give E240 E241 E242 E271 E272 and Hob241 Hob242 Hob271 Hob272, and keptFL keeps the regions of atoms 241, 242, 271 and 272. The two GOT words (objects 0 and 1, atoms 241 and 242) are unchanged. Module paths and module names re-keyed to fuzz_ctrl. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/CtrlACja.v, with its module paths and module names changed; 566 of its 624 lines of code are new or changed and 273 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjBase TjCuts TjLoopCuts TjSnSh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac tju_hd AG HSK :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear - HSK; cbn; lia | clear; cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
lazymatch goal with Hsp1 : sp0 - _ <= ?sp1 <= sp0 - _ |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0)); [reflexivity | evalE AG | clear - Hsp1 HSK; cbn; lia | clear - Hsp1; cbn; lia |] end
end.
Ltac tju_fsb := repeat match goal with
| |- context [fs_frame_bytes ?c / 8] => let v := eval vm_compute in (fs_frame_bytes c / 8) in
lazymatch v with Zpos _ => change (fs_frame_bytes c / 8) with v end
| |- context [fs_frame_bytes ?c] => let v := eval vm_compute in (fs_frame_bytes c) in
lazymatch v with Zpos _ => change (fs_frame_bytes c) with v end
end.
Ltac tju_awr_rec hd AG fpos F EFA :=
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
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; tju_fsb; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; tju_fsb; rewrite ?EFA; fold F; clear - Ha; lia
| ]
end
| match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "tju_awr: no rule for the head region" ];
tju_awr_rec hd AG fpos F EFA
end.
Ltac tju_awr hd AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
tju_awr_rec hd AG fpos F EFA.
Ltac tju_notw AG :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin.
Ltac tju_fa2 tac := apply Forall_cons; [tac | apply Forall_cons; [tac | apply Forall_nil]].
Ltac tju_kept AG Hfr Hpres2 :=
eapply region_kept_aview; [evalE AG | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; lia | exact Hpres2].
Ltac tju_U H :=
rewrite ?U_SAlu, ?U_SMd, ?U_SLit in H; cbn [zalu_raw zmd_raw] in H;
repeat match type of H with context [U ?Ev (SOff ?n 0)] =>
lazymatch goal with Hn : ew Ev n = Z_to_bv 64 ?v |- _ => rewrite (U_atom Ev n v Hn) in H by lia end end.
Ltac tju_Ug :=
rewrite ?U_SAlu, ?U_SMd, ?U_SLit; cbn [zalu_raw zmd_raw];
repeat match goal with |- context [U ?Ev (SOff ?n 0)] =>
lazymatch goal with Hn : ew Ev n = Z_to_bv 64 ?v |- _ => rewrite (U_atom Ev n v Hn) by lia end end.
Ltac tju_zc H := try change (zcanon (-1)) with 18446744073709551615 in H; repeat match type of H with context [zcanon ?z] =>
lazymatch z with context [zcanon _] => fail | _ => rewrite (zcanon_id z) in H by (unfold M64; lia) end end.
Ltac tju_zcg := try change (zcanon (-1)) with 18446744073709551615; repeat match goal with |- context [zcanon ?z] =>
lazymatch z with context [zcanon _] => fail | _ => rewrite (zcanon_id z) by (unfold M64; lia) end end.
Lemma tju_sub2 : forall c l, 0 <= l <= c -> c < 2 ^ 63 -> zcanon (c + zcanon (l * 18446744073709551615)) = c - l.
Proof.
intros c l Hl Hc. unfold zcanon, M64.
destruct (Z.eq_dec l 0) as [->|Hl0].
{ rewrite Z.mul_0_l, Zmod_0_l, Z.add_0_r, Z.sub_0_r. apply Z.mod_small. lia. }
replace (l * 18446744073709551615) with ((2 ^ 64 - l) + (l - 1) * 2 ^ 64) by ring.
rewrite Z_mod_plus_full, (Z.mod_small (2 ^ 64 - l)) by lia.
replace (c + (2 ^ 64 - l)) with ((c - l) + 1 * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma tju_sub : forall c l z, zcanon z = 2 ^ 64 - 1 -> 0 <= l <= c -> c < 2 ^ 63 -> zcanon (c + zcanon (l * zcanon z)) = c - l.
Proof.
intros c l z Hz Hl Hc. rewrite Hz. unfold zcanon, M64.
destruct (Z.eq_dec l 0) as [->|Hl0].
{ rewrite Z.mul_0_l, Zmod_0_l, Z.add_0_r, Z.sub_0_r. apply Z.mod_small. lia. }
replace (l * (2 ^ 64 - 1)) with ((2 ^ 64 - l) + (l - 1) * 2 ^ 64) by ring.
rewrite Z_mod_plus_full, (Z.mod_small (2 ^ 64 - l)) by lia.
replace (c + (2 ^ 64 - l)) with ((c - l) + 1 * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma tju_sub3 : forall c l1 l2, 0 <= l1 -> 0 <= l2 -> l1 + l2 <= c -> c < 2 ^ 63 ->
zcanon (zcanon (c + zcanon (l1 * 18446744073709551615)) + zcanon (l2 * 18446744073709551615)) = c - (l1 + l2).
Proof.
intros c l1 l2 H1 H2 H3 H4. rewrite (tju_sub2 c l1) by lia. rewrite (tju_sub2 (c - l1) l2) by lia. lia.
Qed.
Lemma tju_P34 : forall e, model_of reac_disco_table_json_c.box_tok e = (s_unknown, s_0x0) ->
P3 reac_disco_table_json_c.box_tok e = tj_f_model_unk /\ P4 reac_disco_table_json_c.box_tok e = tj_f_width_0.
Proof. intros e H. unfold P3, P4. rewrite H. split; reflexivity. Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Lemma tju_garr8_app : forall H H' (m m' : word -> option byte) p (acc T : list Z),
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
Definition ss_tjT9 : sstate := Eval vm_compute in ss_havoc_regs ss_tjT 900 [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 26; 24; 27; 28; 29; 30; 31]%nat.
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
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
Hypothesis DRO : tfib_ro_unowned B.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis TJS : tj_strs.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Lemma tju_fmt : forall ly S (W : world SEGS) mem md k s rs,
AR SEGS B ly S W mem md -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
tj_ro_at k s -> Forall (zdisjoint (VAL (A_OBJ k), Z.of_nat (length s) + 1)) rs ->
fmt_at (aview SEGS (w_H W) mem) rs (VAL (A_OBJ k)) s.
Proof.
intros ly S W mem md k s rs HAR HROD (Hg & Hro & Hlo & Hhi & Hc & Hb) Hrs.
destruct (ro_read_ok_glob SEGS B tfib_globs ly S W mem md (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) (VAL (A_OBJ k)) (Z.of_nat (length s) + 1)
GM Hg HV HAR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Hra Hhull].
unfold IMG_LO, IMG_TOP in Hlo, Hhi.
unfold fmt_at. split; [lia|]. split.
- intros i Hi. rewrite (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) (VAL (A_OBJ k) + i) HROD
(Hro (VAL (A_OBJ k) + i) ltac:(lia))
(tfib_ro_unowned_at B _ _ DRO ltac:(unfold tfib_ro_ranges; apply in_or_app; left; exact Hg)) ltac:(lia)).
pose proof (Hb (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)) as Hq.
rewrite Z2Nat.id in Hq by lia. exact Hq.
- split; [exact Hrs|]. split; [unfold amem_range, kLowMemEnd; left; lia|]. split; assumption.
Qed.
Lemma tju_keep_journal : forall (cx : tjcx) own ly' S' (W' : world SEGS) mem' md' k,
tj_baseX B IMG cx ->
ajournal SEGS B REAC_DISCO_TABLE_JSON_STK (spZ (c_regs cx)) (tj_fp (c_buf cx) (c_cap cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
own ly' S' W' mem' md' k ->
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
eapply range_addressable_entry_frame; [exact LAWS | exact HJ | exact Hin | exact Hcid | exact Hflo | exact Hfhi | exact Hal8 | | exact HAR | exact Hra].
intros x HF. exact (proj1 (HnF x HF)).
Qed.
Theorem pb_tj_unk : tj_seg_unk B IMG.
Proof.
unfold tj_seg_unk, tj_fromU, tj_from0.
intros i FX FT cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0. unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
pose proof HB0 as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
pose proof HX0 as (AG34 & E60 & E516 & E528 & E529 & HEI).
unfold INV_tjU, tj_lbody, tj_wrote in HINV. cbn [c_cap c_T c_now c_buf c_t c_ly c_S] in HINV.
destruct HINV as (Hk0 & (Hperm & HKEEP & Hcap3 & Hi & E721 & E722 & E740 & E741) & HMOD & acc & E813 & Hacc & Htxt & Hgarr).
assert (HTX : reac_disco_table_json_c.tj_text T now = acc ++ tj_f_model_unk ++ tj_f_width_0 ++ tj_after4 (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i).
{ rewrite Htxt. unfold tj_after2. destruct (tju_P34 _ HMOD) as [-> ->]. reflexivity. }
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E0 n) by (intros n Hn; apply AG34; lia).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite (AG34 33%nat ltac:(lia)); exact HE033).
clear AG34.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : REAC_DISCO_TABLE_JSON_STK = 12416) by (unfold REAC_DISCO_TABLE_JSON_STK; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk3 & _ & _ & _ & _ & _ & Hpres3 & _ & _ & HQT3).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *. set (FLg := flag_addr ly 2 fpos) in *.
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact (HE0 1%nat 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (AG 2%nat ltac:(lia)); exact (HE0 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (AG 3%nat ltac:(lia)); exact (HE0 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (AG 4%nat ltac:(lia)); exact (HE0 4%nat 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (E12 : ew E 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(lia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(lia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact HE02).
img_factsF E.
pose proof (img_env_atomP E 288 HEI ltac:(unfold A_TEXT, A_LIM; lia)) as E288.
pose proof (img_env_atomP E 289 HEI ltac:(unfold A_TEXT, A_LIM; lia)) as E289.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob241. pose proof (pa_obj_img 1 ltac:(lia)) as Hob242.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob253.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob253.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob253, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres. fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh. fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img. rewrite EFA in HFhigh_img. fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & HNb).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HAR3 Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HAR3 Hinb Hfin) as Hbsep.
rewrite EFA0 in Hbsep. fold F in Hbsep. change (fs_frame_bytes 2) with 256 in Hbsep. unfold zdisjoint in Hbsep. cbn [fst snd] in Hbsep.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp. unfold off_img, IMG_LO, IMG_TOP in Hbimg.
set (L := Z.of_nat (length acc)) in *.
unfold w64 in E813.
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
paj_run_shc RUNP RUNC HS HJ. { tju_awr ltac:(idtac; tju_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK1 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tju_notw AG]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ltu_U in Hc. tju_U Hc. rewrite zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc. lia. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ. { tju_awr ltac:(idtac; tju_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK2 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tju_notw AG]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_eq_U in Hc. tju_U Hc.
rewrite (zcanon_id (buf + L)) in Hc by (unfold M64; lia).
rewrite (proj2 (Z.ltb_ge (buf + L) (zcanon 1))) in Hc by (unfold zcanon, M64; rewrite Z.mod_small by lia; lia).
vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ. { tju_awr ltac:(idtac; tju_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK3 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tju_notw AG]) end.
clear HF HFr HG.
pose proof (proj1 HJ) as HARc.
pose proof TJS as (_ & _ & _ & _ & _ & _ & Hmu & Hw0 & _).
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HRODc.
destruct (tj_snp_canary _ _ _ _ _ HARc) as (cval & HG1 & HG2).
pose proof tj_snp_gcgv as (Hgc1 & Hgc2 & Hgv1 & Hgv2). unfold IMG_LO, IMG_TOP in Hgc1, Hgc2, Hgv1, Hgv2.
pose proof Hmu as (_ & _ & Hmulo & Hmuhi & _). unfold IMG_LO, IMG_TOP in Hmulo, Hmuhi. change (A_OBJ 47) with 288%nat in Hmulo, Hmuhi.
cbn [length tj_f_model_unk Z.of_nat] in Hmulo, Hmuhi.
rregU HS (10%bv : bv 5) (buf + L) ltac:(tju_Ug; apply zcanon_id; unfold M64; lia) Ra0.
rregU HS (11%bv : bv 5) (cap - L) ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom E 13 cap E13), (U_atom E 813 L E813) by lia; rewrite U_SLit; apply tju_sub; [reflexivity | lia | lia]) Ra1.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (1%bv : bv 5) Qra. prreg HS (12%bv : bv 5) Qa2.
pmkst HS. rewrite HSNPC.
eapply (aj_sh_snprintf_at B LAWS pa_segs_low REAC_DISCO_TABLE_JSON_STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq) W3 (ms_regs ms1) (ms_mem ms1) (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + L) (cap - L) (VAL (A_OBJ 47)) tj_f_model_unk (map PLit tj_f_model_unk) [] (map (argZ (ms_regs ms1)) [3; 4; 5; 6; 7] ++ []) [] tj_f_model_unk cval (sp1 - spZ regs) (Z_to_bv 64 (BASE + 24388)) _ HJ HRODc).
{ unfold spZ at 1. rewrite Qsp, E60, unsigned_lit_small by lia. lia. }
{ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ lia. }
{ rewrite HSK, HSNP. lia. }
{ rewrite Qgp, E3. exact Hgp. }
{ rewrite Qtp, E4. exact Htp. }
{ exact Qra. }
{ apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ exact Ra0. }
{ exact Ra1. }
{ rewrite Qa2, E288. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. lia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. unfold snp_out. tju_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact HG1. }
{ exact HG2. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ unfold snp_out. tju_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ unfold snp_out. tju_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ apply (tju_fmt _ _ _ _ _ 47 _ _ HARc HRODc Hmu). unfold snp_out. change (A_OBJ 47) with 288%nat. cbn [length tj_f_model_unk Z.of_nat]. tju_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact (tj_ro_fmt_rng 47 tj_f_model_unk Hmu ltac:(cbv; lia)). }
{ unfold tj_f_model_unk. discriminate. }
{ vm_compute. reflexivity. }
{ cbv [tj_f_model_unk map]. repeat (apply Forall_cons; [exact I|]). apply Forall_nil. }
{ split; [reflexivity | intros ii Hii; cbn in Hii; lia]. }
{ cbn. lia. }
{ unfold snp_out. tju_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact I. }
{ cbn [map app SnFF.pf_args_amem]. exact I. }
{ vm_compute. reflexivity. }
{ lia. }
{ cbn. lia. }
{ lia. }
{ lia. }
{ unfold snp_out. cbn [pairwise]. split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|lia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; lia].
+ exists buf, Nb. split; [exact Hinb | lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hinb | lia | lia]. }
{ exact Hfrm. }
intros fx1 regs2 mem2 md2 Hf1 Hf2 HJ2 HP2 Ha0' Hwr Hnul Hfr Hpres2 Hsame.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr by lia. rewrite HSNP in Hfr.
assert (LMU : Z.of_nat (length tj_f_model_unk) = 18) by reflexivity.
assert (LW0 : Z.of_nat (length tj_f_width_0) = 14) by reflexivity.
rewrite LMU in Ha0', Hwr, Hnul, Hfr.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG ltac:(idtac; tju_kept AG Hfr Hpres2).
apply (st_ok_pi_restrict_fx fq fx1) in HS.
clear RUNP RUNTOP RUNC BR.
pose (BR := paj_branch (fx := fx1) (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx1) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx1) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx1) B LAWS).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E12v : ew Ev 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat) by lia; rewrite (HE0 12%nat 12%bv eq_refl); exact H12);
assert (E13v : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by lia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13) end.
clear E12 E13. rename E12v into E12. rename E13v into E13.
prreg HS (10%bv : bv 5) Qr0. cbn [ms_regs] in Qr0. rewrite Ha0' in Qr0. symmetry in Qr0. unfold w64 in Qr0.
lazymatch type of Qr0 with ew ?Ev ?n = _ => assert (U0 : U Ev (SOff n 0) = 18) by (apply U_atom; [exact Qr0 | lia]) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (U4 : U Ev (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 813 0) (SLit (-1)))) = cap - L)
by (rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom Ev 13 cap E13), (U_atom Ev 813 L E813) by lia; rewrite U_SLit; apply tju_sub; [reflexivity | lia | lia]) end.
psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) (sv_denot _ ?b) = _ =>
rewrite (denot_lit_U Ev a), (denot_lit_U Ev b) in Hc end.
rewrite U0, U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ2. { tju_awr ltac:(idtac; tju_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK4 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tju_notw AG]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
paj_run_to_shc RUNTOP HS HJ2 25204. { tju_awr ltac:(idtac; tju_hd AG HSK) AG fpos F EFA0. }
prreg HS (23%bv : bv 5) R23.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 23; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R23 E653.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx1 Ev k _ _ Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite ew_havoc_old by lia; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; lia]|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; lia].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_ly c_S c_cap c_T c_now c_buf].
split; [exact Hk0|]. split; [exact Hperm|].
exists (-1). split; [rewrite E653; unfold w64; first [reflexivity | apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity]|].
split; [intros; lia|]. split; [|intros _ _; reflexivity].
intros _ Hlt. exfalso. unfold tj_len in Hlt. rewrite HTX, !length_app, !Nat2Z.inj_add in Hlt. fold L in Hlt. lia.
+ cbn [c_fq]. exact HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hfit1.
rewrite Z.min_l in Hwr, Hnul, Hfr by lia.
clear HG1 HG2.
assert (G1 : garr8 SEGS (mrestrict (w_H W3) mem2) buf ((acc ++ tj_f_model_unk) ++ [0])).
{ rewrite <- app_assoc. apply (tju_garr8_app (w_H W3) (w_H W3) (ms_mem ms3) mem2 buf acc tj_f_model_unk Hgarr).
- intros a Ha. rewrite (Hfr a ltac:(lia) ltac:(lia) ltac:(lia)). rewrite HK3 by lia. rewrite HK2 by lia. apply HK1. lia.
- intros ii Hii. rewrite LMU in Hii. exact (Hwr ii ltac:(lia)).
- rewrite LMU. exact Hnul. }
paj_run_shc RUNP RUNC HS HJ2. { tju_awr ltac:(idtac; tju_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK5 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tju_notw AG]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ rewrite branch_ltu_U in Hc. tju_U Hc. tju_zc Hc. apply Z.ltb_lt in Hc. lia. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ2. { tju_awr ltac:(idtac; tju_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK6 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tju_notw AG]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ rewrite branch_eq_U in Hc. tju_U Hc. tju_zc Hc. 
rewrite (proj2 (Z.ltb_ge _ 1)) in Hc by lia. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ2. { tju_awr ltac:(idtac; tju_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK7 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tju_notw AG]) end.
clear HF HFr HG.
pose proof (proj1 HJ2) as HARc2.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROD) as HRODc2.
destruct (tj_snp_canary _ _ _ _ _ HARc2) as (cval2 & HG3 & HG4).
pose proof Hw0 as (_ & _ & Hw0lo & Hw0hi & _). unfold IMG_LO, IMG_TOP in Hw0lo, Hw0hi. change (A_OBJ 48) with 289%nat in Hw0lo, Hw0hi.
cbn [length tj_f_width_0 Z.of_nat] in Hw0lo, Hw0hi.
rregU HS (10%bv : bv 5) (buf + (L + 18)) ltac:(tju_Ug; tju_zcg; lia) Rb0.
rregU HS (11%bv : bv 5) (cap - (L + 18)) ltac:(tju_Ug; tju_zcg; apply tju_sub3; lia) Rb1.
prreg HS (2%bv : bv 5) Qsp2. prreg HS (3%bv : bv 5) Qgp2. prreg HS (4%bv : bv 5) Qtp2. prreg HS (1%bv : bv 5) Qra2. prreg HS (12%bv : bv 5) Qa22.
pmkst HS. rewrite HSNPC.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (aj_sh_snprintf_at B LAWS pa_segs_low REAC_DISCO_TABLE_JSON_STK fx1 GC GV IMGLO IMGHI CR SNPC (ASNP fx1) W3 rg mm (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + (L + 18)) (cap - (L + 18)) (VAL (A_OBJ 48)) tj_f_width_0 (map PLit tj_f_width_0) [] (map (argZ rg) [3; 4; 5; 6; 7] ++ []) [] tj_f_width_0 cval2 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 24444)) _ HJ2 HRODc2) end.
{ unfold spZ at 1. rewrite Qsp2, E60, unsigned_lit_small by lia. lia. }
{ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ lia. }
{ rewrite HSK, HSNP. lia. }
{ rewrite Qgp2, (AG 3%nat ltac:(lia)), (HE0 3%nat 3%bv eq_refl). exact Hgp. }
{ rewrite Qtp2, (AG 4%nat ltac:(lia)), (HE0 4%nat 4%bv eq_refl). exact Htp. }
{ exact Qra2. }
{ apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ exact Rb0. }
{ exact Rb1. }
{ rewrite Qa22, E289. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc2). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. lia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. unfold snp_out. tju_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact HG3. }
{ exact HG4. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ unfold snp_out. tju_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ unfold snp_out. tju_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ apply (tju_fmt _ _ _ _ _ 48 _ _ HARc2 HRODc2 Hw0). unfold snp_out. change (A_OBJ 48) with 289%nat. cbn [length tj_f_width_0 Z.of_nat]. tju_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact (tj_ro_fmt_rng 48 tj_f_width_0 Hw0 ltac:(cbv; lia)). }
{ unfold tj_f_width_0. discriminate. }
{ vm_compute. reflexivity. }
{ cbv [tj_f_width_0 map]. repeat (apply Forall_cons; [exact I|]). apply Forall_nil. }
{ split; [reflexivity | intros ii Hii; cbn in Hii; lia]. }
{ cbn. lia. }
{ unfold snp_out. tju_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact I. }
{ cbn [map app SnFF.pf_args_amem]. exact I. }
{ vm_compute. reflexivity. }
{ lia. }
{ cbn. lia. }
{ lia. }
{ lia. }
{ unfold snp_out. cbn [pairwise]. split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|lia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; lia].
+ exists buf, Nb. split; [exact Hinb | lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); lia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); lia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); lia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc2 | exact Hinb | lia | lia]. }
{ exact Hf2. }
intros fx2 regs4 mem4 md4 Hg1 Hg2 HJ4 HP4 Hb0' Hwr4 Hnul4 Hfr4 Hpres4 Hsame4.
assert (Hh1 : forall r : bv 5, bv_unsigned r <> 10 -> Sem.reg_get (@fp_regs fx2) r = Sem.reg_get (@fp_regs fq) r)
by (intros r Hr; rewrite (Hg1 r Hr); exact (Hf1 r Hr)).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr4 by lia. rewrite HSNP in Hfr4.
rewrite LW0 in Hb0', Hwr4, Hnul4, Hfr4.
clear HJ2. rename HJ4 into HJ2.
reseat HS HJ2 HP4 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG ltac:(idtac; tju_kept AG Hfr4 Hpres4).
apply (st_ok_pi_restrict_fx _ fx2) in HS.
clear RUNP RUNTOP RUNC BR.
pose (BR := paj_branch (fx := fx2) (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx2) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx2) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx2) B LAWS).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E12v : ew Ev 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat) by lia; rewrite (HE0 12%nat 12%bv eq_refl); exact H12);
assert (E13v : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by lia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13) end.
clear E12 E13. rename E12v into E12. rename E13v into E13.
prreg HS (10%bv : bv 5) Qr1. cbn [ms_regs] in Qr1. rewrite Hb0' in Qr1. symmetry in Qr1. unfold w64 in Qr1.
lazymatch type of Qr1 with ew ?Ev ?n = _ => assert (U1 : U Ev (SOff n 0) = 14) by (apply U_atom; [exact Qr1 | lia]) end.
psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) (sv_denot _ ?b) = _ =>
rewrite (denot_lit_U Ev a), (denot_lit_U Ev b) in Hc end.
rewrite U1, U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ2. { tju_awr ltac:(idtac; tju_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK8 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tju_notw AG]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ rewrite branch_geu_U in Hc. tju_U Hc. tju_zc Hc. rewrite (tju_sub3 cap L 18) in Hc by lia.
apply negb_true_iff, Z.ltb_ge in Hc.
paj_run_to_shc RUNTOP HS HJ2 25204. { tju_awr ltac:(idtac; tju_hd AG HSK) AG fpos F EFA0. }
prreg HS (23%bv : bv 5) R23.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 23; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R23 E653.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx2 Ev k _ _ Wg msF mdF Hh1 Hg2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite ew_havoc_old by lia; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; lia]|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; lia].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_ly c_S c_cap c_T c_now c_buf].
split; [exact Hk0|]. split; [exact Hperm|].
exists (-1). split; [rewrite E653; unfold w64; first [reflexivity | apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity]|].
split; [intros; lia|]. split; [|intros _ _; reflexivity].
intros _ Hlt. exfalso. unfold tj_len in Hlt. rewrite HTX, !length_app, !Nat2Z.inj_add in Hlt. fold L in Hlt. lia.
+ cbn [c_fq]. exact HS. }
rewrite branch_geu_U in Hc. tju_U Hc. tju_zc Hc. rewrite (tju_sub3 cap L 18) in Hc by lia.
apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hfit2.
rewrite Z.min_l in Hwr4, Hnul4, Hfr4 by lia.
assert (G2 : garr8 SEGS (mrestrict (w_H W3) mem4) buf ((acc ++ tj_f_model_unk ++ tj_f_width_0) ++ [0])).
{ replace ((acc ++ tj_f_model_unk ++ tj_f_width_0) ++ [0]) with ((acc ++ tj_f_model_unk) ++ tj_f_width_0 ++ [0]) by (rewrite <- !app_assoc; reflexivity).
apply (tju_garr8_app (w_H W3) (w_H W3) mem2 mem4 buf (acc ++ tj_f_model_unk) tj_f_width_0 G1).
- intros a Ha. rewrite length_app, Nat2Z.inj_add, LMU in Ha. fold L in Ha.
rewrite (Hfr4 a ltac:(lia) ltac:(lia) ltac:(lia)). rewrite HK7 by lia. rewrite HK6 by lia. rewrite HK5 by lia. apply HK4. lia.
- intros ii Hii. rewrite LW0 in Hii. rewrite length_app, Nat2Z.inj_add, LMU. fold L. exact (Hwr4 ii ltac:(lia)).
- rewrite length_app, Nat2Z.inj_add, LMU, LW0. fold L. exact Hnul4. }
paj_run_to_shc RUNTOP HS HJ2 24608. { tju_awr ltac:(idtac; tju_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK9 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tju_notw AG]) end.
clear HF HFr HG.
rregU HS (26%bv : bv 5) (L + 32) ltac:(tju_Ug; tju_zcg; lia) R26.
ra_join HS ss_tjT9 900%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 26; 24; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join HS ss_tjT 840%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 26; 24; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 840%nat 12%nat R26 E852.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B IMG _ _ FT (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx2 Ev k _ _ Wg msF mdF Hh1 Hg2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite !ew_havoc_old by lia; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; lia]|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [apply img_env_havoc_hi; [assumption | unfold A_LIM; lia] | unfold A_LIM; lia].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjT, tj_lbody, tj_wrote. cbn [c_cap c_T c_now c_buf c_t c_ly c_S].
split; [exact Hk0|]. split.
{ split; [exact Hperm|]. split; [exact (tju_keep_journal _ _ _ _ _ _ _ _ HBASE HJ2)|]. split; [exact Hcap3|]. split; [exact Hi|].
rewrite !ew_havoc_old by (cbn; lia). split; [exact E721|]. split; [exact E722|]. split; [exact E740 | exact E741]. }
exists (acc ++ tj_f_model_unk ++ tj_f_width_0). split.
{ unfold w64. rewrite E852. f_equal. rewrite !length_app, !Nat2Z.inj_add. fold L. lia. }
split; [rewrite !length_app, !Nat2Z.inj_add; fold L; lia|].
split; [rewrite HTX, <- !app_assoc; reflexivity|].
apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem4 _ buf); [|exact G2].
intros a Ha. rewrite !length_app, !Nat2Z.inj_add in Ha. fold L in Ha. cbn [length Z.of_nat] in Ha.
rewrite HK9 by lia. apply HK8. lia.
+ cbn [c_fq]. exact HS.
Qed.
End h.
End f.
End d.
