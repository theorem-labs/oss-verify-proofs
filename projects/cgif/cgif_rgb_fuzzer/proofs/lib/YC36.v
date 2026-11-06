(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI01 YI07 YI03 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC0x YC3g YC2z YC3e YC31 YC2x YC2v YC35 YC2y YC2w YC37 YC3a YC3b YC3c YC3f YC32 YC3h YC33 YC30 YC34.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma arr16_u16s_a : forall mem base l, arr16 trasegs mem base l -> u16s l.
Proof.
intros mem base l H. unfold u16s. apply Forall_nth. intros j d Hj. rewrite (nth_indep _ d 0 Hj). exact (proj2 (H j Hj)).
Qed.
Definition sr_init : list sv := asr_fix.
Definition ictx_chunks : list YQ0b.chunk :=
[YQ0b.mkChunk 0 (CVal 8 (SOff 54 0)); YQ0b.mkChunk 8 (CVal 8 (SOff 55 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 37 0));
YQ0b.mkChunk 24 (CVal 8 (SOff 56 0)); YQ0b.mkChunk 32 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 40 (CVal 8 (SOff 10 0));
YQ0b.mkChunk 48 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 56 (CVal 4 (SOff 33 0))].
Definition ictx_region : YQ0b.region := YQ0b.mkRegion (Some 8%nat) 0 72 60 68 ictx_chunks.
Definition istk_chunks : list YQ0b.chunk :=
[YQ0b.mkChunk 112 (CVal 8 (shx 48)); YQ0b.mkChunk 120 (CVal 8 (SOff 8 48)); YQ0b.mkChunk 128 (CVal 8 (shx 40)); YQ0b.mkChunk 136 (CVal 8 (shx 56));
YQ0b.mkChunk 144 (CVal 8 (SOff 8 56)); YQ0b.mkChunk 152 (CVal 8 (SOff 34 0)); YQ0b.mkChunk 160 (CVal 8 (shx 32)); YQ0b.mkChunk 168 (CVal 8 (SOff 38 0));
YQ0b.mkChunk 176 (CVal 8 (SOff 35 0)); YQ0b.mkChunk 184 (CVal 8 (SOff 39 0)); YQ0b.mkChunk 192 (CVal 8 (shx 24)); YQ0b.mkChunk 200 (CVal 8 (shx 16));
YQ0b.mkChunk 208 (CVal 8 (SOff 8 40))] ++ tsaved_chunks 40.
Definition istk_region : YQ0b.region := YQ0b.mkRegion (Some 2%nat) 0 320 24 112 istk_chunks.
Definition ild_region : YQ0b.region := YQ0b.mkRegion (Some 10%nat) 0 2 0 2 [YQ0b.mkChunk 0 (CVal 2 (SOff 53 0))].
Definition ifacts : facts := mkFacts
[ (2%nat, mkAF (2^46) (2^47) 4); (8%nat, APTR 4); (27%nat, mkAF SB SB 0); (21%nat, mkAF 2 2 0); (54%nat, APTR 4); (55%nat, APTR 4); (56%nat, APTR 4);
(10%nat, APTR 4); (25%nat, mkAF 2 256 0); (32%nat, APTR 0); (33%nat, mkAF 1 100000000 0); (34%nat, mkAF 0 (2^47 - 16) 3);
(35%nat, mkAF 0 12 0); (36%nat, APTR 4); (37%nat, APTR 4); (38%nat, mkAF 4 512 0); (39%nat, mkAF 8 131072 0); (53%nat, mkAF 0 65535 0) ] [] [].
Definition ss_init : sstate := mkSS PC_INIT sr_init [ictx_region; istk_region; ild_region] None ifacts.
Definition init_regs (regs6 : bvmap 5 word) (cx : lzw_acx) : Prop :=
alzw_regs_fix regs6 cx /\ getr regs6 10 = w64 (z_ld cx).
Definition init_mem (m : word -> option byte) (cx : lzw_acx) : Prop :=
let sp := z_sp cx - 320 in let ctx := z_ctx cx in
val_mem trasegs m (sp + 208) 8 (ctx + 40) /\ val_mem trasegs m (sp + 200) 8 (shadow_word (ctx + 16)) /\ val_mem trasegs m (sp + 192) 8 (shadow_word (ctx + 24)) /\
val_mem trasegs m (sp + 184) 8 (z_tisz cx) /\ val_mem trasegs m (sp + 176) 8 (z_icl cx) /\ val_mem trasegs m (sp + 168) 8 (2 * z_idl cx) /\
val_mem trasegs m (sp + 160) 8 (shadow_word (ctx + 32)) /\ val_mem trasegs m (sp + 152) 8 (z_pR cx) /\ val_mem trasegs m (sp + 144) 8 (ctx + 56) /\
val_mem trasegs m (sp + 136) 8 (shadow_word (ctx + 56)) /\ val_mem trasegs m (sp + 128) 8 (shadow_word (ctx + 40)) /\
val_mem trasegs m (sp + 120) 8 (ctx + 48) /\ val_mem trasegs m (sp + 112) 8 (shadow_word (ctx + 48)) /\
val_mem trasegs m ctx 8 (z_ti cx) /\ val_mem trasegs m (ctx + 8) 8 (z_lm cx) /\ val_mem trasegs m (ctx + 16) 8 (z_lc cx) /\
val_mem trasegs m (ctx + 24) 8 (z_li cx) /\ val_mem trasegs m (ctx + 32) 8 (z_tm cx) /\ val_mem trasegs m (ctx + 40) 8 (z_ld cx) /\
val_mem trasegs m (ctx + 48) 8 (z_img cx) /\ val_mem trasegs m (ctx + 56) 4 (z_nP cx).
Definition init_untouched (cx : lzw_acx) (a : Z) : Prop :=
~ (z_ctx cx + 60 <= a < z_ctx cx + 68) /\ ~ (z_sp cx - 320 + 24 <= a < z_sp cx - 320 + 112) /\ ~ (z_ld cx <= a < z_ld cx + 2) /\
~ (z_ti cx <= a < z_ti cx + 2 * z_idl cx * z_idl cx) /\ ~ (z_lm cx <= a < z_lm cx + 8192) /\ ~ (z_lc cx <= a < z_lc cx + 4096) /\
~ (z_li cx <= a < z_li cx + 8192) /\ ~ (z_sp cx - 320 - 4096 <= a < z_sp cx - 320).
Definition tinit_env (E : env) (cx : lzw_acx) : Prop :=
ew E 2 = Z_to_bv 64 (z_sp cx - 320) /\ ew E 3 = Z_to_bv 64 (z_gp cx) /\ ew E 4 = Z_to_bv 64 (z_tp cx) /\
ew E 8 = Z_to_bv 64 (z_ctx cx) /\ ew E 10 = Z_to_bv 64 (z_ld cx) /\ ew E 27 = Z_to_bv 64 SB /\ ew E 21 = Z_to_bv 64 2 /\ ew E 54 = Z_to_bv 64 (z_ti cx) /\
ew E 55 = Z_to_bv 64 (z_lm cx) /\ ew E 25 = Z_to_bv 64 (z_idl cx) /\ ew E 56 = Z_to_bv 64 (z_li cx) /\
ew E 32 = Z_to_bv 64 (z_img cx) /\ ew E 33 = Z_to_bv 64 (z_nP cx) /\ ew E 34 = Z_to_bv 64 (z_pR cx) /\ ew E 35 = Z_to_bv 64 (z_icl cx) /\
ew E 36 = Z_to_bv 64 (z_tm cx) /\ ew E 37 = Z_to_bv 64 (z_lc cx) /\ ew E 38 = Z_to_bv 64 (2 * z_idl cx) /\
ew E 39 = Z_to_bv 64 (2 * z_idl cx * z_idl cx).
Lemma agen_at_of_fields : forall (m m' : word -> option byte) cx lp dp mp,
val_mem trasegs m (z_ctx cx) 8 (z_ti cx) -> val_mem trasegs m (z_ctx cx + 8) 8 (z_lm cx) -> val_mem trasegs m (z_ctx cx + 16) 8 (z_lc cx) ->
val_mem trasegs m (z_ctx cx + 24) 8 (z_li cx) -> val_mem trasegs m (z_ctx cx + 32) 8 (z_tm cx) -> val_mem trasegs m (z_ctx cx + 40) 8 (z_ld cx) ->
val_mem trasegs m (z_ctx cx + 48) 8 (z_img cx) -> val_mem trasegs m (z_ctx cx + 56) 4 (z_nP cx) ->
(forall a, z_ctx cx <= a < z_ctx cx + 60 -> mbyte trasegs m' a = mbyte trasegs m a) ->
val_mem trasegs m' (z_ctx cx + 60) 4 lp -> val_mem trasegs m' (z_ctx cx + 64) 2 dp -> val_mem trasegs m' (z_ctx cx + 66) 2 mp ->
agen_at m' cx lp dp mp.
Proof.
intros m m' cx lp dp mp V0 V8 V16 V24 V32 V40 V48 V56 Hfr V60 V64 V66.
unfold agen_at. repeat split; try assumption;
intros k Hk; (rewrite Hfr; [| cbn in Hk; lia]); first [apply V0 | apply V8 | apply V16 | apply V24 | apply V32 | apply V40 | apply V48 | apply V56]; exact Hk.
Qed.
Section S.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis AMEMSET : aintrin_realizes trasegs B OSet A_asan_memset.
Let HBcode := tl_code B TL.
Local Ltac sep HSEP i j := septac HSEP i j; lia.
Lemma tinit_seed : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs6 : bvmap 5 word) mem6 md6 (regs0 : bvmap 5 word),
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx -> acx_tok cx (ablocks B lyc Sc) ->
ajournal trasegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem6 md6 7 ->
init_regs regs6 cx -> init_mem (mrestrict (w_H W7) mem6) cx -> tlzw_frame (mrestrict (w_H W7) mem6) (z_sp cx) regs0 ->
exists E TM0,
st_ok trasegs E ss_init (restrict (w_H W7) (mkst regs6 (Z_to_bv 64 PC_INIT) mem6 (seg_rom trasegs))) /\ tinit_env E cx /\
length TM0 = Z.to_nat (2049 * z_idl cx) /\ arr16 trasegs (mrestrict (w_H W7) mem6) (z_tm cx) TM0.
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs6 mem6 md6 regs0 HCX HRG HSEP (HBg & HBi & HBt) HTOK HJ HIR HIM HFR.
pose proof HIR as (HFX & G10). pose proof HFX as (Gsp & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G25 & G26 & G27 & G1 & G3 & G4). unfold spZ in Gsp.
miss_prep B cx HCX HRG HBt HTOK HJ.
assert (Ati : forall blc lyq i, In (z_ti cx, 2 * z_idl cx * z_idl cx) blc -> 0 <= i < req_size (2 * z_idl cx * z_idl cx) ->
awr_byte (336 + 16384) (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_ti cx + i))
by (intros blc lyq i Hb Hi; apply (HTOK (z_ti cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; right; left; reflexivity)); [exact Hb | exact Hi]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ctx cx) 72 HAR HBg) as (_ & _ & _ & _ & Hcpres & _). change (req_size 72) with 72 in Hcpres.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ld cx) _ HAR HBld) as (_ & _ & _ & _ & Hldpres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_tm cx) _ HAR HBtm) as (_ & _ & _ & _ & Htmpres & _).
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
assert (Htisz : 8 <= 2 * z_idl cx * z_idl cx <= 131072) by (clear - Hidl; split; [nia|nia]).
assert (Hsws : forall a, z_sp cx - 320 <= a < z_sp cx -> apresent (w_H W7) mem6 a).
{ intros a Ha. apply (proj1 (awr_byte_present trasegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ ltac:(left; lia))). }
unfold z_tisz, z_tmsz in *.
set (m := mrestrict (w_H W7) mem6) in *.
assert (Ptm : forall i, 0 <= i < 4098 * z_idl cx -> YP0c.present m (z_tm cx + i)).
{ intros i Hi. destruct (Htmpres (z_tm cx + i) ltac:(lia)) as [[Hh [bb0 Hb0]] _]. exists bb0. subst m. unfold mrestrict. rewrite Hh. exact Hb0. }
destruct (arr16_of_present trasegs m (z_tm cx) (Z.to_nat (2049 * z_idl cx))) as (TM0 & LenTM & ATM).
{ intros a Ha. rewrite Z2Nat.id in Ha by lia. replace a with (z_tm cx + (a - z_tm cx)) by lia. apply Ptm. lia. }
assert (Pld : forall i, 0 <= i < 2 -> YP0c.present m (z_ld cx + i)).
{ intros i Hi. destruct (Hldpres (z_ld cx + i) ltac:(lia)) as [[Hh [bb0 Hb0]] _]. exists bb0. subst m. unfold mrestrict. rewrite Hh. exact Hb0. }
destruct (val_mem2 trasegs m (z_ld cx)) as (vLD & HvLDr & HvLD); [replace (z_ld cx) with (z_ld cx + 0) by lia; apply Pld; lia | apply Pld; lia |].
change (2 ^ 16) with 65536 in HvLDr.
set (ext := [Z_to_bv 64 (z_img cx); Z_to_bv 64 (z_nP cx); Z_to_bv 64 (z_pR cx); Z_to_bv 64 (z_icl cx); Z_to_bv 64 (z_tm cx); Z_to_bv 64 (z_lc cx);
Z_to_bv 64 (2 * z_idl cx); Z_to_bv 64 (2 * z_idl cx * z_idl cx)] ++ tsaved_vals regs0 ++ [Z_to_bv 64 vLD; Z_to_bv 64 (z_ti cx); Z_to_bv 64 (z_lm cx); Z_to_bv 64 (z_li cx)]).
remember (Ereg regs6 ext) as E eqn:HE0.
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs6 r) by (intros n r Hn; rewrite HE0; apply ew_Ereg_nat; exact Hn).
assert (EX : forall j, ew E (32 + j) = nth j ext (Z_to_bv 64 0)) by (intros j; rewrite HE0; apply ew_Ereg_extra).
pose proof (EX 0%nat) as HE32. pose proof (EX 1%nat) as HE33. pose proof (EX 2%nat) as HE34. pose proof (EX 3%nat) as HE35.
pose proof (EX 4%nat) as HE36. pose proof (EX 5%nat) as HE37. pose proof (EX 6%nat) as HE38. pose proof (EX 7%nat) as HE39. pose proof (EX 21%nat) as HE53.
pose proof (EX 22%nat) as HE54. pose proof (EX 23%nat) as HE55. pose proof (EX 24%nat) as HE56.
cbn [nth ext app Nat.add tsaved_vals map TSAVED] in HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE53, HE54, HE55, HE56.
assert (HSV : forall j, (j < 13)%nat -> ew E (40 + j)%nat = nth j (tsaved_vals regs0) (Z_to_bv 64 0)).
{ intros j Hj. replace (40 + j)%nat with (32 + (8 + j))%nat by lia. rewrite EX. subst ext.
change (8 + j)%nat with (length [Z_to_bv 64 (z_img cx); Z_to_bv 64 (z_nP cx); Z_to_bv 64 (z_pR cx); Z_to_bv 64 (z_icl cx); Z_to_bv 64 (z_tm cx); Z_to_bv 64 (z_lc cx); Z_to_bv 64 (2 * z_idl cx); Z_to_bv 64 (2 * z_idl cx * z_idl cx)] + j)%nat.
rewrite app_nth2_plus. apply app_nth1. unfold tsaved_vals. rewrite length_map. cbv. lia. }
pose proof (ER 2%nat 2%bv eq_refl) as HE2. pose proof (ER 8%nat 8%bv eq_refl) as HE8. rewrite G8 in HE8.
pose proof (ER 27%nat 27%bv eq_refl) as HE27. rewrite G27 in HE27. pose proof (ER 10%nat 10%bv eq_refl) as HE10. rewrite G10 in HE10.
pose proof (ER 25%nat 25%bv eq_refl) as HE25. rewrite G25 in HE25.
pose proof (ER 21%nat 21%bv eq_refl) as HE21. rewrite G21 in HE21. pose proof (ER 3%nat 3%bv eq_refl) as HE3. rewrite G3 in HE3.
pose proof (ER 4%nat 4%bv eq_refl) as HE4. rewrite G4 in HE4.
assert (U2 : bv_unsigned (ew E 2) = z_sp cx - 320) by (rewrite HE2; exact Gsp).
assert (HE2z : ew E 2 = Z_to_bv 64 (z_sp cx - 320)) by (rewrite <- U2; symmetry; apply Z_to_bv_bv_unsigned).
unfold w64 in *.
assert (HS : st_ok trasegs E ss_init (restrict (w_H W7) (mkst regs6 (Z_to_bv 64 PC_INIT) mem6 (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_init. apply aentry_st_ok_any.
- unfold sr_init. rewrite HE0. apply (regs_ok_fix regs6 cx); [exact HFX | lia | lia].
- vm_compute. reflexivity.
- destruct HIM as (S208 & S200 & S192 & S184 & S176 & S168 & S160 & S152 & S144 & S136 & S128 & S120 & S112 & V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56).
Local Ltac ck S HE := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, ?unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; lia
| first [exact S | rewrite Z.add_0_r; exact S | match type of S with val_mem _ _ ?a _ _ => match goal with |- val_mem _ _ ?a' _ _ => replace a' with a by lia; exact S end end] ].
constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok, ictx_region. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite HE8, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable trasegs); apply (proj1 (Hcpres (z_ctx cx + o) ltac:(lia)))|].
unfold ictx_chunks.
constructor; [ck V0 HE54|]. constructor; [ck V8 HE55|]. constructor; [ck V16 HE37|]. constructor; [ck V24 HE56|].
constructor; [ck V32 HE36|]. constructor; [ck V40 HE10|]. constructor; [ck V48 HE32|]. constructor; [ck V56 HE33|]. constructor.
+ unfold region_ok, istk_region. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable trasegs); apply Hsws; lia|].
unfold istk_chunks. apply Forall_app. split.
* Local Ltac shk S HE8 HE27 :=
eapply chunk_ok_val; [ eapply shx_denot; [exact HE8 | exact HE27 | lia | lia | lia] | | cbn; lia
| first [exact S | match type of S with val_mem _ _ ?a _ _ => match goal with |- val_mem _ _ ?a' _ _ => replace a' with a by lia; exact S end end] ];
[ unfold shadow_word; match goal with |- 0 <= bv_unsigned ?w < _ => let Hr := fresh in pose proof (bv_unsigned_in_range 64 w) as Hr; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hr; exact Hr end ].
unfold z_tisz in S184.
constructor; [shk S112 HE8 HE27|]. constructor; [ck S120 HE8|]. constructor; [shk S128 HE8 HE27|]. constructor; [shk S136 HE8 HE27|].
constructor; [ck S144 HE8|]. constructor; [ck S152 HE34|]. constructor; [shk S160 HE8 HE27|]. constructor; [ck S168 HE38|].
constructor; [ck S176 HE35|]. constructor; [ck S184 HE39|]. constructor; [shk S192 HE8 HE27|]. constructor; [shk S200 HE8 HE27|].
constructor; [ck S208 HE8|]. constructor.
* apply (tsaved_chunks_ok E m (z_sp cx) regs0 40 HSV HFR).
+ unfold region_ok, ild_region. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite HE10, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable trasegs); apply (proj1 (Hldpres (z_ld cx + o) ltac:(lia)))|].
constructor; [ck HvLD HE53 | constructor].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, ictx_region, istk_region, ild_region.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite HE8, HE10, U2, !unsigned_lit_small by lia.
septac HSEP 0%nat 6%nat. repeat split; lia.
- split; [| split; exact I].
cbn [atoms_ok f_atoms ifacts]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE2, HE8, HE27, HE21, HE54, HE55, HE56, HE10, HE25, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE53, Gsp, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 0) with 1. change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
repeat split; try (unfold SB; lia). replace (z_sp cx - 320) with (z_sp cx + (-20) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
exists E, TM0. split; [exact HS|]. split; [|split; [exact LenTM | exact ATM]].
unfold tinit_env. rewrite HE2z, HE3, HE4, HE8, HE10, HE27, HE21, HE54, HE55, HE25, HE56, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39.
repeat split; reflexivity.
Qed.
Lemma tinit_seg : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs6 : bvmap 5 word) mem6 md6 (regs0 : bvmap 5 word),
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx -> acx_tok cx (ablocks B lyc Sc) ->
ajournal trasegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem6 md6 7 ->
z_gp cx = as_gp B -> z_tp cx = as_tp B ->
init_regs regs6 cx -> init_mem (mrestrict (w_H W7) mem6) cx -> tlzw_frame (mrestrict (w_H W7) mem6) (z_sp cx) regs0 ->
SRr trasegs W7 (mkCfg (mkst regs6 (Z_to_bv 64 PC_INIT) mem6 (seg_rom trasegs)) md6)
(fun W' c' => W' = W7 /\ exists regsH memH mdH TM0,
c' = mkCfg (mkst regsH (Z_to_bv 64 PC_HEAD) memH (seg_rom trasegs)) mdH /\
ajournal trasegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memH mdH 7 /\
alzw_regs_head regsH cx /\ getr regsH 23 = w64 0 /\
agen_at (mrestrict (w_H W7) memH) cx 1 (z_idl cx + 2) 1 /\
atables_at (mrestrict (w_H W7) memH) cx (lzw_init (z_idl cx) TM0) /\ lzw_inv (z_idl cx) (z_nP cx) (lzw_init (z_idl cx) TM0) /\
alzw_slots (mrestrict (w_H W7) memH) cx /\ alzw_sslots (mrestrict (w_H W7) memH) cx /\ tlzw_frame (mrestrict (w_H W7) memH) (z_sp cx) regs0 /\
(forall a, 0 <= a < 2 ^ 64 -> init_untouched cx a -> mbyte trasegs (mrestrict (w_H W7) memH) a = mbyte trasegs (mrestrict (w_H W7) mem6) a)).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs6 mem6 md6 regs0 HCX HRG HSEP HBL HTOK HJ Hzgp Hztp HIR HIM HFR.
destruct (tinit_seed cx lyc Sc W memc mdc ly7 S7 W7 regs6 mem6 md6 regs0 HCX HRG HSEP HBL HTOK HJ HIR HIM HFR)
as (E & TM0 & HS & HEnv & LenTM & ATM).
pose proof HEnv as (HE2 & HE3 & HE4 & HE8 & HE10 & HE27 & HE21 & HE54 & HE55 & HE25 & HE56 & HE32 & HE33 & HE34 & HE35 & HE36 & HE37 & HE38 & HE39).
clear HEnv. destruct HBL as (HBg & HBi & HBt).
miss_prep B cx HCX HRG HBt HTOK HJ.
assert (Ati : forall blc lyq i, In (z_ti cx, 2 * z_idl cx * z_idl cx) blc -> 0 <= i < req_size (2 * z_idl cx * z_idl cx) ->
awr_byte (336 + 16384) (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_ti cx + i))
by (intros blc lyq i Hb Hi; apply (HTOK (z_ti cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; right; left; reflexivity)); [exact Hb | exact Hi]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ctx cx) 72 HAR HBg) as (_ & _ & _ & _ & Hcpres & _). change (req_size 72) with 72 in Hcpres.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
assert (Htisz : 8 <= 2 * z_idl cx * z_idl cx <= 131072) by (clear - Hidl; split; [nia|nia]).
unfold z_tisz, z_tmsz in *.
set (m := mrestrict (w_H W7) mem6) in *.
assert (HK : forall a, 0 <= a < 2 ^ 64 -> init_untouched cx a -> mbyte trasegs (mrestrict (w_H W7) mem6) a = mbyte trasegs (mrestrict (w_H W7) mem6) a) by (intros; reflexivity).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs6 (Z_to_bv 64 PC_INIT) mem6 (seg_rom trasegs)))).
change mem6 with (ms_mem (mkst regs6 (Z_to_bv 64 PC_INIT) mem6 (seg_rom trasegs))) in HJ.
Local Ltac zsep HSEP C :=
lazymatch C with
| init_untouched _ => unfold init_untouched in *; tauto
| in_rng (z_ti _) _ => unfold in_rng in *; septac HSEP 1%nat 6%nat; septac HSEP 0%nat 1%nat; septac HSEP 1%nat 2%nat; septac HSEP 1%nat 3%nat; septac HSEP 1%nat 4%nat; lia
| in_rng (z_lm _) _ => unfold in_rng in *; septac HSEP 2%nat 6%nat; septac HSEP 0%nat 2%nat; septac HSEP 1%nat 2%nat; septac HSEP 2%nat 3%nat; septac HSEP 2%nat 4%nat; lia
| in_rng (z_lc _) _ => unfold in_rng in *; septac HSEP 3%nat 6%nat; septac HSEP 0%nat 3%nat; septac HSEP 1%nat 3%nat; septac HSEP 2%nat 3%nat; septac HSEP 3%nat 4%nat; lia
| in_rng (z_li _) _ => unfold in_rng in *; septac HSEP 4%nat 6%nat; septac HSEP 0%nat 4%nat; septac HSEP 1%nat 4%nat; septac HSEP 2%nat 4%nat; septac HSEP 3%nat 4%nat; lia
end.
Local Ltac fold_step T HSEP R1 R2 R3 R4 R5 R6 R7 :=
lazymatch type of T with forall a, _ -> _ -> mbyte _ ?mn a = mbyte _ ?mo a =>
repeat match goal with
| H : forall a, 0 <= a < 2 ^ 64 -> ?C a -> mbyte trasegs mo a = mbyte trasegs ?mz a |- _ =>
let H2 := fresh H in
assert (H2 : forall a, 0 <= a < 2 ^ 64 -> C a -> mbyte trasegs mn a = mbyte trasegs mz a)
by (intros a Ha Hc; rewrite (T a Ha) by (clear - Ha Hc HSEP R1 R2 R3 R4 R5 R6 R7; zsep HSEP C); exact (H a Ha Hc));
clear H; rename H2 into H
| H : forall a, 0 <= a < 2 ^ 64 -> ?C a -> mbyte trasegs mo a = Some ?v |- _ =>
let H2 := fresh H in
assert (H2 : forall a, 0 <= a < 2 ^ 64 -> C a -> mbyte trasegs mn a = Some v)
by (intros a Ha Hc; rewrite (T a Ha) by (clear - Ha Hc HSEP R1 R2 R3 R4 R5 R6 R7; zsep HSEP C); exact (H a Ha Hc));
clear H; rename H2 into H
end
end; clear T.
Local Ltac awr3 cx AG HE8 HE2 HE10 Actx HBg Ald HBld :=
cbn [ss_mem ss_init]; unfold ictx_region, istk_region, ild_region;
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat (z_ctx cx));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 8%nat) by lia; rewrite HE8; apply unsigned_lit_small; lia
| cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; replace a with (z_ctx cx + (a - z_ctx cx)) by lia; apply Actx; [exact HBg | lia]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-320));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 2%nat) by lia; rewrite HE2, unsigned_lit_small by lia; lia
| cbn; lia | cbn; lia
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat (z_ld cx));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 10%nat) by lia; rewrite HE10; apply unsigned_lit_small; lia
| cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; replace a with (z_ld cx + (a - z_ld cx)) by lia; apply Ald; [exact HBld | lia]
| apply awr_ok_nil ] ] ].
Local Ltac tstep cx AG HE8 HE2 HE10 HSEP R1 R2 R3 R4 R5 R6 R7 :=
let T := fresh "T" in
lazymatch goal with HFr : frame_of ?Ef _ (mrestrict ?Hh ?ma) (mrestrict _ ?mb) |- _ =>
cbn [ss_mem ss_init] in HFr;
assert (T : forall a, 0 <= a < 2 ^ 64 ->
(~ (z_ctx cx + 60 <= a < z_ctx cx + 68) /\ ~ (z_sp cx - 320 + 24 <= a < z_sp cx - 320 + 112) /\ ~ (z_ld cx <= a < z_ld cx + 2)) ->
mbyte trasegs (mrestrict Hh mb) a = mbyte trasegs (mrestrict Hh ma) a)
by (intros a Ha Hu;
eapply (aframe_mbyte_list Ef _ _ _ [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 320 + 24, z_sp cx - 320 + 112); (z_ld cx, z_ld cx + 2)] a HFr Ha);
[ repeat (apply Forall2_cons;
[ right; cbn [fst snd YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi ss_mem ss_init ictx_region istk_region ild_region base_val ew ewset Nat.eqb];
rewrite ?ew_ewset_other by lia; try rewrite (AG 8%nat) by lia; try rewrite (AG 2%nat) by lia; try rewrite (AG 10%nat) by lia;
rewrite ?HE8, ?HE2, ?HE10, ?unsigned_lit_small by lia; lia |]);
apply Forall2_nil
| cbn; pose proof Hu as (Hu1 & Hu2 & Hu3); exact (conj Hu1 (conj Hu2 (conj Hu3 I))) ]);
clear HFr; try match goal with H : frame_of _ _ _ _ |- _ => clear H end; try match goal with H : mem_grows _ _ |- _ => clear H end;
fold_step T HSEP R1 R2 R3 R4 R5 R6 R7
end.
Local Ltac mcall cx HS HJ AG HEd HE2 HE3 HE4 Hzgp Hztp dval nval raval HB Atmp :=
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in let Rra := fresh "Rra" in
let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in let Rtp := fresh "Rtp" in
rreg HS (10%bv : bv 5) Ra0; rreg HS (11%bv : bv 5) Ra1; rreg HS (12%bv : bv 5) Ra2; rreg HS (1%bv : bv 5) Rra;
rreg HS (2%bv : bv 5) Rsp; rreg HS (3%bv : bv 5) Rgp; rreg HS (4%bv : bv 5) Rtp;
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl); cbn [ss_pc];
change (Z_to_bv 64 336460) with (Z_to_bv 64 A_asan_memset);
let L := getLAWS in let HSGL := aj_segs_low in
eapply SRr_bind;
[ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trasegs B L HSGL OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) _ _ _ _ _ _ _ _ _ _ _ _ 7
dval 0 nval (-320) (Z_to_bv 64 raval) HJ) end;
[ rewrite Ra0; eatom AG HEd
| rewrite Ra1; reflexivity
| rewrite Ra2; first [reflexivity | match goal with H : ew _ 39 = _ |- _ => eatom AG H end]
| lia | lia | lia
| unfold spZ; rewrite Rsp; try rewrite (AG 2%nat) by lia; rewrite HE2, unsigned_lit_small by lia; lia
| reflexivity | lia | unfold ESTACK; lia
| rewrite Rgp; try rewrite (AG 3%nat) by lia; rewrite HE3, Hzgp; reflexivity
| rewrite Rtp; try rewrite (AG 4%nat) by lia; rewrite HE4, Hztp; reflexivity
| exact Rra | vm_compute; reflexivity
| intros a Ha; split; [replace a with (dval + (a - dval)) by lia; apply Atmp; [exact HB | lia] | unfold ESTACK; lia]
| eapply (amem_range_of_block trasegs B L _ _ _ _ _ _ _ _ _ (proj1 HJ) HB); lia
| eapply (range_addressable_of_block trasegs B L _ _ _ _ _ _ _ _ _ (proj1 HJ) HB); lia
| intros _; eapply (shadow_hull_vis_of_block trasegs B L _ _ _ _ _ _ _ _ _ (proj1 HJ) HB); lia
| exact I ]
| cbv beta; clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp ].
Local Ltac mpost cx Heff Hfr dval nval Zname HSEP R1 R2 R3 R4 R5 R6 R7 :=
let T := fresh "T" in
lazymatch type of Hfr with forall a, _ -> _ -> _ -> aview _ (w_H ?Wx) ?m2 a = aview _ _ ?m1 a =>
assert (Zname : forall a, 0 <= a < 2 ^ 64 -> in_rng dval (dval + nval) a -> mbyte trasegs (mrestrict (w_H Wx) m2) a = Some (Z_to_bv 8 0))
by (intros a Ha Hd; unfold in_rng in Hd; replace a with (dval + (a - dval)) by lia; apply mbyte_zero_of_aview; rewrite (Heff (a - dval)) by lia; reflexivity);
assert (T : forall a, 0 <= a < 2 ^ 64 -> (~ (dval <= a < dval + nval) /\ ~ (z_sp cx - 320 - 4096 <= a < z_sp cx - 320)) ->
mbyte trasegs (mrestrict (w_H Wx) m2) a = mbyte trasegs (mrestrict (w_H Wx) m1) a)
by (intros a Ha [Hn1 Hn2]; apply (mbyte_of_aview trasegs); apply Hfr; [exact Ha | exact Hn1 | unfold ESTACK; replace (z_sp cx + -320) with (z_sp cx - 320) by lia; exact Hn2]);
clear Heff Hfr; fold_step T HSEP R1 R2 R3 R4 R5 R6 R7
end.
Local Ltac kept3 AG HE8 HE2 HE10 Hfr Hpres HSEP i :=
eapply region_kept_aview;
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia;
lazymatch goal with
| |- bv_unsigned (ew _ 8) = _ => try rewrite (AG 8%nat) by lia; rewrite HE8
| |- bv_unsigned (ew _ 2) = _ => try rewrite (AG 2%nat) by lia; rewrite HE2
| |- bv_unsigned (ew _ 10) = _ => try rewrite (AG 10%nat) by lia; rewrite HE10
end; rewrite unsigned_lit_small by lia; reflexivity
| intros a Ha; cbn in Ha; apply Hfr;
[ lia
| revert Ha;
lazymatch goal with
| |- z_ctx _ + _ <= _ < _ -> _ => sep HSEP i 6%nat
| |- z_ld _ + _ <= _ < _ -> _ => sep HSEP 0%nat i
| _ => lia
end
| unfold ESTACK; lia ]
| exact Hpres ].
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan; try (oblk HJ HBld HE10 HE27 (z_ld cx)); try (oblk HJ HBg HE8 HE27 (z_ctx cx)).
{ awr3 cx AG HE8 HE2 HE10 Actx HBg Ald HBld. }
tstep cx AG HE8 HE2 HE10 HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
mcall cx HS HJ AG HE54 HE2 HE3 HE4 Hzgp Hztp (z_ti cx) (2 * z_idl cx * z_idl cx) 0x89a60 HBti Ati.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff1 & Hfr1 & Hpres2).
reseat HS HJ2 HP2 [0; 1; 2]%nat AG ltac:(kept3 AG HE8 HE2 HE10 Hfr1 Hpres2 HSEP 1%nat).
mpost cx Heff1 Hfr1 (z_ti cx) (2 * z_idl cx * z_idl cx) ZTI HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 0x89a60) mem2 (seg_rom trasegs))) in HJ2. reshok_bx HS 27%nat.
Local Ltac stretch cx HS HJ SHOK AG HE8 HE2 HE10 Actx HBg Ald HBld HSEP R1 R2 R3 R4 R5 R6 R7 :=
let HEv8 := fresh "HEv8" in let HEv27 := fresh "HEv27" in
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEv8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (try rewrite (AG 8%nat) by lia; exact HE8);
assert (HEv27 : ew Ev 27 = Z_to_bv 64 SB) by (try rewrite (AG 27%nat) by lia; match goal with H27 : ew _ 27 = Z_to_bv 64 SB |- _ => exact H27 end) end;
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan; try (oblk HJ HBg HEv8 HEv27 (z_ctx cx)); clear HEv8 HEv27;
[ awr3 cx AG HE8 HE2 HE10 Actx HBg Ald HBld | ];
[ tstep cx AG HE8 HE2 HE10 HSEP R1 R2 R3 R4 R5 R6 R7 ].
stretch cx HS HJ2 SHOK AG HE8 HE2 HE10 Actx HBg Ald HBld HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
mcall cx HS HJ2 AG HE55 HE2 HE3 HE4 Hzgp Hztp (z_lm cx) 8192 0x89a78 HBlm Alm.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff2 & Hfr2 & Hpres3).
reseat HS HJ3 HP3 [0; 1; 2]%nat AG ltac:(kept3 AG HE8 HE2 HE10 Hfr2 Hpres3 HSEP 2%nat).
mpost cx Heff2 Hfr2 (z_lm cx) 8192 ZLM HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 0x89a78) mem3 (seg_rom trasegs))) in HJ3. reshok_bx HS 27%nat.
stretch cx HS HJ3 SHOK AG HE8 HE2 HE10 Actx HBg Ald HBld HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
mcall cx HS HJ3 AG HE37 HE2 HE3 HE4 Hzgp Hztp (z_lc cx) 4096 0x89a94 HBlc Alc.
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff3 & Hfr3 & Hpres4).
reseat HS HJ4 HP4 [0; 1; 2]%nat AG ltac:(kept3 AG HE8 HE2 HE10 Hfr3 Hpres4 HSEP 3%nat).
mpost cx Heff3 Hfr3 (z_lc cx) 4096 ZLC HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 0x89a94) mem4 (seg_rom trasegs))) in HJ4. reshok_bx HS 27%nat.
stretch cx HS HJ4 SHOK AG HE8 HE2 HE10 Actx HBg Ald HBld HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
mcall cx HS HJ4 AG HE56 HE2 HE3 HE4 Hzgp Hztp (z_li cx) 8192 0x89ab0 HBli Ali.
intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff4 & Hfr4 & Hpres5).
reseat HS HJ5 HP5 [0; 1; 2]%nat AG ltac:(kept3 AG HE8 HE2 HE10 Hfr4 Hpres5 HSEP 4%nat).
mpost cx Heff4 Hfr4 (z_li cx) 8192 ZLI HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
change mem5 with (ms_mem (mkst regs5 (Z_to_bv 64 0x89ab0) mem5 (seg_rom trasegs))) in HJ5. reshok_bx HS 27%nat.
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEw8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (rewrite (AG 8%nat) by lia; exact HE8);
assert (HEw27 : ew Ev 27 = Z_to_bv 64 SB) by (rewrite (AG 27%nat) by lia; exact HE27) end.
aj_run_to_tok tratbl_lib_ok HS HJ5 SHOK Bspan PC_HEAD; try (oblk HJ5 HBg HEw8 HEw27 (z_ctx cx)); [ awr3 cx AG HE8 HE2 HE10 Actx HBg Ald HBld | ].
clear HEw8 HEw27.
tstep cx AG HE8 HE2 HE10 HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEv2 : ew Ev 2 = Z_to_bv 64 (z_sp cx - 320)) by (rewrite (AG 2%nat) by lia; exact HE2);
assert (HEv3 : ew Ev 3 = Z_to_bv 64 (z_gp cx)) by (rewrite (AG 3%nat) by lia; exact HE3);
assert (HEv4 : ew Ev 4 = Z_to_bv 64 (z_tp cx)) by (rewrite (AG 4%nat) by lia; exact HE4);
assert (HEv8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (rewrite (AG 8%nat) by lia; exact HE8);
assert (HEv10 : ew Ev 10 = Z_to_bv 64 (z_ld cx)) by (rewrite (AG 10%nat) by lia; exact HE10);
assert (HEv27 : ew Ev 27 = Z_to_bv 64 SB) by (rewrite (AG 27%nat) by lia; exact HE27);
assert (HEv21 : ew Ev 21 = Z_to_bv 64 2) by (rewrite (AG 21%nat) by lia; exact HE21);
assert (HEv25 : ew Ev 25 = Z_to_bv 64 (z_idl cx)) by (rewrite (AG 25%nat) by lia; exact HE25);
assert (HEv32 : ew Ev 32 = Z_to_bv 64 (z_img cx)) by (rewrite (AG 32%nat) by lia; exact HE32);
assert (G2 : bv_unsigned (ew Ev 2) = z_sp cx - 320) by (rewrite HEv2; apply unsigned_lit_small; lia);
assert (G8 : bv_unsigned (ew Ev 8) = z_ctx cx) by (rewrite HEv8; apply unsigned_lit_small; lia)
end.
clear HE2 HE3 HE4 HE8 HE10 HE27 HE21 HE25 HE32.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_ok_region_nth Ex ssx msx 0%nat _ HS eq_refl) as HRg0; pose proof (st_ok_region_nth Ex ssx msx 1%nat _ HS eq_refl) as HRg1 end.
cbn [ms_mem restrict] in HRg0, HRg1.
Local Ltac aregE HS AG :=
lazymatch goal with |- context [getr _ ?r] =>
let R := fresh "R" in rreg HS r R; rewrite R; clear R;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?E0 ?n = _ |- context [ew ?E0 ?n] => rewrite H end;
unfold w64; rewrite ?unsigned_lit_small by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [reflexivity | f_equal; lia | match goal with |- ?g => idtac "AREGE" g end]
end.
Local Ltac sval :=
first [ rewrite denot_lit_U; f_equal; apply U_nPm1; [assumption | lia]
| apply shx_denot; [assumption | assumption | lia | lia | lia]
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r;
repeat match goal with H : ew ?E0 ?n = _ |- context [ew ?E0 ?n] => rewrite H end;
unfold shadow_word; rewrite ?unsigned_lit_small by lia; rewrite ?Z_to_bv_bv_unsigned;
first [reflexivity | f_equal; lia | match goal with |- ?g => idtac "SVAL" g; fail end] ].
Local Ltac find_chunk_e od cs :=
lazymatch cs with
| YQ0b.mkChunk od (CVal _ ?e) :: _ => e
| _ :: ?r => find_chunk_e od r
end.
Local Ltac fld HRg Gb :=
lazymatch goal with |- val_mem _ ?mx (_ + ?od) ?nn ?v =>
lazymatch type of HRg with region_ok _ ?Ex _ (YQ0b.mkRegion (Some ?nb) ?lo ?hi ?wlo ?whi ?cs) =>
let e := find_chunk_e od cs in
let w := eval vm_compute in (N.of_nat nn) in
change nn with (N.to_nat w);
eapply (field_of_region Ex mx nb _ cs lo hi wlo whi od w e v HRg);
[ exact Gb
| cbn; tauto
| sval
| first [ change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) | change (2 ^ (8 * Z.of_N 2)) with 65536 ];
first [ lia
| unfold shadow_word;
match goal with |- 0 <= bv_unsigned ?wv < _ => let Hr := fresh "Hr" in pose proof (bv_unsigned_in_range 64 wv) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr end ]
| cbn; lia ]
end end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regsH memH mdH TM1, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists rg, mm, mdx, TM0 end.
split; [reflexivity|]. split; [exact HJ5|].
destruct HIM as (S208 & S200 & S192 & S184 & S176 & S168 & S160 & S152 & S144 & S136 & S128 & S120 & S112 & V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56).
split.
{ unfold alzw_regs_head, alzw_regs_fix, spZ. repeat match goal with |- _ /\ _ => split end; aregE HS AG. }
split; [aregE HS AG|].
split.
{ lazymatch type of HRg0 with region_ok _ _ ?mx _ =>
apply (agen_at_of_fields m mx cx 1 (z_idl cx + 2) 1 V0 V8 V16 V24 V32 V40 V48 V56) end;
[ intros a Ha; apply HK; [lia | unfold init_untouched; septac HSEP 0%nat 6%nat; septac HSEP 1%nat 6%nat; septac HSEP 2%nat 6%nat;
septac HSEP 3%nat 6%nat; septac HSEP 4%nat 6%nat; repeat split; lia]
| fld HRg0 G8 | fld HRg0 G8 | fld HRg0 G8 ]. }
split.
{ unfold atables_at. cbn [la_TI la_LM la_LI la_TM lzw_init]. split; [|split; [|split]].
- apply arr16_zeros_aview. intros a Ha. rewrite Z2Nat.id in Ha by lia. apply ZTI; [lia | unfold in_rng; lia].
- apply arr16_zeros_aview. intros a Ha. cbn in Ha. apply ZLM; [lia | unfold in_rng; lia].
- apply arr16_zeros_aview. intros a Ha. cbn in Ha. apply ZLI; [lia | unfold in_rng; lia].
- eapply arr16_frame; [exact ATM|]. intros a Ha. rewrite LenTM, Z2Nat.id in Ha by lia.
apply HK; [lia|]. unfold init_untouched. septac HSEP 5%nat 6%nat. septac HSEP 0%nat 5%nat. septac HSEP 1%nat 5%nat. septac HSEP 2%nat 5%nat.
septac HSEP 3%nat 5%nat. septac HSEP 4%nat 5%nat. repeat split; lia. }
split; [apply inv_init; [lia | lia | exact LenTM | exact (arr16_u16s_a _ _ _ ATM)]|].
split.
{ unfold alzw_slots, z_tisz. repeat match goal with |- _ /\ _ => split end; fld HRg1 G2. }
split.
{ unfold alzw_sslots. repeat match goal with |- _ /\ _ => split end; fld HRg1 G2. }
split; [|exact HK].
eapply tlzw_frame_agree; [exact HFR|]. intros a Ha. apply HK; [lia|]. unfold init_untouched. repeat split; lia.
Qed.
End S.
End b.
