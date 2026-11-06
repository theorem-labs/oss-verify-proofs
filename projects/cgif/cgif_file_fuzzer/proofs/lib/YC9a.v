(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbw.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI10 YC4a YC8i YC80 YC1f YC1g YC81 YC4b YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8a YC93 YC9g YC95 YC91 YC99 YC92 YC9h.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_1_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_1_listing PI) (@pa_relro_lo _ lib_both3_1_listing PI) (@pa_relro_hi _ lib_both3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition A_INIT_RET : Z := 0x18f4.
Definition istk_chunks : list YP09.chunk :=
[YP09.mkChunk 80 (CVal 8 (shx 48)); YP09.mkChunk 88 (CVal 8 (SOff 8 48)); YP09.mkChunk 96 (CVal 8 (shx 40));
YP09.mkChunk 104 (CVal 8 (shx 56)); YP09.mkChunk 112 (CVal 8 (SOff 8 56));
YP09.mkChunk 136 (CVal 8 (SOff 44 0)); YP09.mkChunk 144 (CVal 8 (shx 32)); YP09.mkChunk 152 (CVal 8 (SOff 45 0));
YP09.mkChunk 160 (CVal 8 (SOff 46 0)); YP09.mkChunk 168 (CVal 8 (shx 24)); YP09.mkChunk 176 (CVal 8 (shx 16));
YP09.mkChunk 184 (CVal 8 (SOff 8 40)); YP09.mkChunk 192 (CVal 8 (SOff 8 32))] ++ tsaved_chunks 47.
Definition istk_region : YP09.region := YP09.mkRegion (Some 2%nat) 0 304 40 136 istk_chunks.
Definition ss_init : sstate := rd_ss PC_INIT asr_fix [rctx_region false; istk_region] [] [] [].
Definition hctx_region : YP09.region :=
YP09.mkRegion (Some 8%nat) 0 72 0 0
(rctx_chunks false ++ [YP09.mkChunk 60 (CVal 4 (SLit 1)); YP09.mkChunk 64 (CVal 2 (SOff 25 2)); YP09.mkChunk 66 (CVal 2 (SLit 1))]).
Definition init_mem (m : word -> option byte) (cx : lzw_acx) : Prop :=
let sp := z_sp cx - 304 in let ctx := z_ctx cx in
val_mem SEGS m (sp + 192) 8 (ctx + 32) /\ val_mem SEGS m (sp + 184) 8 (ctx + 40) /\
val_mem SEGS m (sp + 176) 8 (shadow_word (ctx + 16)) /\ val_mem SEGS m (sp + 168) 8 (shadow_word (ctx + 24)) /\
val_mem SEGS m (sp + 160) 8 (z_icl cx) /\ val_mem SEGS m (sp + 152) 8 (2 * z_idl cx) /\ val_mem SEGS m (sp + 144) 8 (shadow_word (ctx + 32)) /\
val_mem SEGS m (sp + 136) 8 (z_pR cx) /\ val_mem SEGS m (sp + 112) 8 (ctx + 56) /\ val_mem SEGS m (sp + 104) 8 (shadow_word (ctx + 56)) /\
val_mem SEGS m (sp + 96) 8 (shadow_word (ctx + 40)) /\ val_mem SEGS m (sp + 88) 8 (ctx + 48) /\ val_mem SEGS m (sp + 80) 8 (shadow_word (ctx + 48)) /\
agen_ptrs m cx.
Definition init_untouched (cx : lzw_acx) (a : Z) : Prop :=
~ (z_ctx cx + 60 <= a < z_ctx cx + 68) /\ ~ (z_sp cx - 304 + 40 <= a < z_sp cx - 304 + 136) /\ ~ (z_ld cx <= a < z_ld cx + 2) /\
~ (z_ti cx <= a < z_ti cx + 2 * z_idl cx * z_idl cx) /\ ~ (z_lm cx <= a < z_lm cx + 8192) /\ ~ (z_lc cx <= a < z_lc cx + 4096) /\
~ (z_li cx <= a < z_li cx + 8192) /\ ~ (z_sp cx - 336 - 4096 <= a < z_sp cx - 304).
Lemma arr16_u16s_b : forall mem base l, arr16 SEGS mem base l -> u16s l.
Proof. intros mem base l H. unfold u16s. apply Forall_nth_Z. intros j Hj. exact (proj2 (H j Hj)). Qed.
Lemma agen_ptrs_frame : forall m m' cx,
agen_ptrs m cx -> (forall a, z_ctx cx <= a < z_ctx cx + 60 -> mbyte SEGS m' a = mbyte SEGS m a) -> agen_ptrs m' cx.
Proof.
intros m m' cx (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hfr.
unfold agen_ptrs. repeat split; intros k Hk; (rewrite Hfr; [| cbn in Hk; lia]);
first [apply H1 | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8]; exact Hk.
Qed.
Lemma region_kept_direct : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> mbyte SEGS (mrestrict H m2) a = mbyte SEGS (mrestrict H m) a) ->
(forall a, b + wlo <= a < b + whi -> writable_at SEGS (mrestrict H m2) a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hb Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha; [apply Hb; exact Ha | intros _; apply Hw; exact Ha].
Qed.
Section S.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_both3_1 PI.
Local Ltac sep HSEP i j := septac HSEP i j; lia.
Lemma tinit_seg : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs6 : bvmap 5 word) mem6 md6 (regs0 : bvmap 5 word),
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx -> acx_tok cx (ablocks B lyc Sc) ->
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem6 md6 7 ->
z_gp cx = as_gp B -> z_tp cx = as_tp B ->
alzw_regs_fix regs6 cx -> init_mem (mrestrict (w_H W7) mem6) cx -> tlzw_frame (mrestrict (w_H W7) mem6) (z_sp cx) regs0 ->
SRr SEGS W7 (mkCfg (mkst regs6 (Z_to_bv 64 (BASE + PC_INIT)) mem6 (seg_rom SEGS)) md6)
(fun W' c' => W' = W7 /\ exists regsH memH mdH TM0,
c' = mkCfg (mkst regsH (Z_to_bv 64 (BASE + PC_HEAD)) memH (seg_rom SEGS)) mdH /\
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memH mdH 7 /\
alzw_regs_head regsH cx /\ getr regsH 24 = w64 0 /\
agen_at (mrestrict (w_H W7) memH) cx 1 (z_idl cx + 2) 1 /\
atables_at (mrestrict (w_H W7) memH) cx (lzw_init (z_idl cx) TM0) /\ lzw_inv (z_idl cx) (z_nP cx) (lzw_init (z_idl cx) TM0) /\
alzw_slots (mrestrict (w_H W7) memH) cx /\ alzw_sslots (mrestrict (w_H W7) memH) cx /\ tlzw_frame (mrestrict (w_H W7) memH) (z_sp cx) regs0 /\
(forall a, 0 <= a < 2 ^ 64 -> init_untouched cx a -> mbyte SEGS (mrestrict (w_H W7) memH) a = mbyte SEGS (mrestrict (w_H W7) mem6) a)).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs6 mem6 md6 regs0 HCX HRG HSEP HBL HTOK HJ Hzgp Hztp HFX HIM HFR. pose proof HBL as (HBg & HBi & HBt).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ as (HAR & _). pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 304 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
assert (HBld : In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; left; reflexivity).
assert (HBti : In (z_ti cx, 2 * z_idl cx * z_idl cx) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; right; left; reflexivity).
assert (HBtm : In (z_tm cx, 4098 * z_idl cx) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 5 right; left; reflexivity).
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
pose proof (req_size_pos (2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) ltac:(pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)); unfold lzw_MR; lia)) as Hrqld.
pose proof (req_size_pos (4098 * z_idl cx) ltac:(lia)) as Hrqtm.
assert (Actx : forall blc lyq i, In (z_ctx cx, 72) blc -> 0 <= i < 72 -> awr_byte LZW_TSTK (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_ctx cx + i)).
{ intros blc lyq i Hb Hi. apply (HTOK (z_ctx cx, 72) ltac:(left; reflexivity)); [exact Hb | cbn [snd]; change (req_size 72) with 72; lia]. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ctx cx) 72 HAR HBg) as (_ & _ & _ & _ & Hcpres & _). change (req_size 72) with 72 in Hcpres.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_tm cx) _ HAR HBtm) as (_ & _ & _ & _ & Htmpres & _).
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. unfold lzw_MR in Rld1, Rld2, Rld4, Hrqld. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
assert (Htisz : 8 <= 2 * z_idl cx * z_idl cx <= 131072) by (clear - Hidl; split; [nia|nia]).
unfold z_tisz, z_tmsz in *.
assert (Hsws : forall a, z_sp cx - 336 <= a < z_sp cx -> apresent (w_H W7) mem6 a).
{ intros a Ha. apply (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ ltac:(left; lia))). }
rewrite ?C1, ?C2, ?C3, ?C4, ?HTS, ?Has in *. clear C2 C3 C4 HTS Has.
set (m := mrestrict (w_H W7) mem6) in *.
assert (Ptm : forall i, 0 <= i < 4098 * z_idl cx -> YO0d.present m (z_tm cx + i)).
{ intros i Hi. destruct (Htmpres (z_tm cx + i) ltac:(lia)) as [[Hh [bb0 Hb0]] _]. exists bb0. subst m. unfold mrestrict. rewrite Hh. exact Hb0. }
destruct (arr16_of_present SEGS m (z_tm cx) (Z.to_nat (2049 * z_idl cx))) as (TM0 & LenTM & ATM).
{ intros a Ha. rewrite Z2Nat.id in Ha by lia. replace a with (z_tm cx + (a - z_tm cx)) by lia. apply Ptm. lia. }
pose proof HIM as (S192 & S184 & S176 & S168 & S160 & S152 & S144 & S136 & S112 & S104 & S96 & S88 & S80 & HGP).
remember (Eimg (Ereg regs6 (acx_extra cx 0 0 0 regs0 ++ []))) as E eqn:HE0. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
pose proof (AE_sp regs6 cx 0 0 0 regs0 [] HFC) as HE2. pose proof (AE_ctx regs6 cx 0 0 0 regs0 [] HFC) as HE8.
pose proof (AE_SB regs6 cx 0 0 0 regs0 [] HFC) as HE21. pose proof (AE_idl regs6 cx 0 0 0 regs0 [] HFC) as HE25.
pose proof (AE_gp regs6 cx 0 0 0 regs0 [] HFC) as HE3. pose proof (AE_tp regs6 cx 0 0 0 regs0 [] HFC) as HE4.
pose proof (AE_ti regs6 cx 0 0 0 regs0 []) as HE32. pose proof (AE_lm regs6 cx 0 0 0 regs0 []) as HE33.
pose proof (AE_lc regs6 cx 0 0 0 regs0 []) as HE34. pose proof (AE_li regs6 cx 0 0 0 regs0 []) as HE35.
pose proof (AE_tm regs6 cx 0 0 0 regs0 []) as HE36. pose proof (AE_ld regs6 cx 0 0 0 regs0 []) as HE37.
pose proof (AE_img regs6 cx 0 0 0 regs0 []) as HE38. pose proof (AE_nP regs6 cx 0 0 0 regs0 []) as HE39.
pose proof (AE_pR regs6 cx 0 0 0 regs0 []) as HE44. pose proof (AE_idl2 regs6 cx 0 0 0 regs0 []) as HE45. pose proof (AE_icl regs6 cx 0 0 0 regs0 []) as HE46.
rewrite <- HE0 in HE2, HE8, HE21, HE25, HE3, HE4, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE44, HE45, HE46.
assert (HSV : forall j, (j < 13)%nat -> ew E (47 + j)%nat = nth j (tsaved_vals regs0) (Z_to_bv 64 0)) by (intros j Hj; rewrite HE0; apply (AE_saved regs6 cx 0 0 0 regs0 [] j Hj)).
assert (HS1 : st_ok_pi SEGS VAL E ss_init (mkst regs6 (Z_to_bv 64 (BASE + PC_INIT)) m (seg_rom SEGS))).
{ unfold ss_init. rewrite HE0. apply (rd_st_ok0 cx regs6 regs0 0 0 0 [] m PC_INIT); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - lia.
- rewrite HE0. apply (regs_ok_fix regs6 cx 0 0 0 regs0 [] HFX); lia.
- vm_compute; reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ rewrite HE0. apply (rctx_region_ok cx regs6 regs0 0 0 0 [] m false HCX HRG HFC HGP ltac:(intros X; discriminate X)); [|lia].
intros a Ha. apply (apresent_writable SEGS). apply (proj1 (Hcpres a ltac:(lia))).
+ unfold region_ok, istk_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HE2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). apply Hsws. lia. }
unfold istk_chunks. apply Forall_app; split.
* Ltac isck S HE := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; apply Z.le_refl
| first [exact S | match type of S with val_mem _ _ _ _ ?v => match goal with |- val_mem _ _ _ _ ?v' => replace v' with v by lia; exact S end end] ].
Ltac ishck S HE8 HE21 := eapply chunk_ok_val; [ eapply shx_denot; [exact HE8 | exact HE21 | lia | lia | lia] | | cbn; apply Z.le_refl | first [exact S | rewrite Z.add_0_r; exact S] ];
[ unfold shadow_word;
match goal with |- 0 <= bv_unsigned ?w < _ => let Hr := fresh in pose proof (bv_unsigned_in_range 64 w) as Hr;
change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hr; exact Hr end ].
constructor; [ishck S80 HE8 HE21|]. constructor; [isck S88 HE8|]. constructor; [ishck S96 HE8 HE21|]. constructor; [ishck S104 HE8 HE21|].
constructor; [isck S112 HE8|]. constructor; [isck S136 HE44|]. constructor; [ishck S144 HE8 HE21|]. constructor; [isck S152 HE45|].
constructor; [isck S160 HE46|]. constructor; [ishck S168 HE8 HE21|]. constructor; [ishck S176 HE8 HE21|].
constructor; [isck S184 HE8|]. constructor; [isck S192 HE8|]. constructor.
* apply (tsaved_chunks_ok E m (z_sp cx) regs0 47 HSV HFR).
- cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, rctx_region, istk_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite HE8, HE2, !unsigned_lit_small by lia. repeat split; lia.
- exact I. - exact I. - exact I. }
idtac "SEED OK".
cbn [ss_init rd_ss] in HS1. subst m. rewrite <- restrict_mkst_fx in HS1. rename HS1 into HS.
set (m := mrestrict (w_H W7) mem6) in *.
assert (HK : forall a, 0 <= a < 2 ^ 64 -> init_untouched cx a -> mbyte SEGS (mrestrict (w_H W7) mem6) a = mbyte SEGS (mrestrict (w_H W7) mem6) a) by (intros; reflexivity).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
shok_auto SHOK (SOff 23 0) E (mrestrict (w_H W7) (ms_mem (mkst regs6 (Z_to_bv 64 (BASE + PC_INIT)) mem6 (seg_rom SEGS)))).
change mem6 with (ms_mem (mkst regs6 (Z_to_bv 64 (BASE + PC_INIT)) mem6 (seg_rom SEGS))) in HJ.
Local Ltac zsep HSEP C :=
lazymatch C with
| in_rng (z_ti _) _ => unfold in_rng, z_tisz in *; septac HSEP 1%nat 6%nat; septac HSEP 0%nat 1%nat; lia
| in_rng (z_lm _) _ => unfold in_rng, z_tisz in *; septac HSEP 2%nat 6%nat; septac HSEP 0%nat 2%nat; lia
| in_rng (z_lc _) _ => unfold in_rng, z_tisz in *; septac HSEP 3%nat 6%nat; septac HSEP 0%nat 3%nat; lia
| in_rng (z_li _) _ => unfold in_rng, z_tisz in *; septac HSEP 4%nat 6%nat; septac HSEP 0%nat 4%nat; lia
| _ => unfold init_untouched, rd_untouched, rd_written, z_tisz in *; lia
end.
Local Ltac fold_step T HSEP R1 R2 R3 R4 R5 R6 R7 R8 R9 :=
lazymatch type of T with forall a, _ -> _ -> mbyte _ ?mn a = mbyte _ ?mo a =>
repeat match goal with
| H : forall a, 0 <= a < 2 ^ 64 -> ?C a -> mbyte SEGS mo a = mbyte SEGS ?mz a |- _ =>
let H2 := fresh H in
assert (H2 : forall a, 0 <= a < 2 ^ 64 -> C a -> mbyte SEGS mn a = mbyte SEGS mz a)
by (intros a Ha Hc; rewrite (T a Ha) by (clear - Ha Hc HSEP R1 R2 R3 R4 R5 R6 R7 R8 R9; zsep HSEP C); exact (H a Ha Hc));
clear H; rename H2 into H
| H : forall a, 0 <= a < 2 ^ 64 -> ?C a -> mbyte SEGS mo a = Some ?v |- _ =>
let H2 := fresh H in
assert (H2 : forall a, 0 <= a < 2 ^ 64 -> C a -> mbyte SEGS mn a = Some v)
by (intros a Ha Hc; rewrite (T a Ha) by (clear - Ha Hc HSEP R1 R2 R3 R4 R5 R6 R7 R8 R9; zsep HSEP C); exact (H a Ha Hc));
clear H; rename H2 into H
end
end; clear T.
Local Ltac awrI cx wctx AG HE8 HE2 Actx HBg :=
cbn [ss_mem ss_init rd_ss];
let frame := eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-304));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 2%nat) by lia; rewrite HE2, unsigned_lit_small by lia; lia
| cbn; lia | cbn; lia
| apply awr_ok_nil ] in
lazymatch wctx with
| true =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat (z_ctx cx));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 8%nat) by lia; rewrite HE8; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi rctx_region]; intros a Ha; replace a with (z_ctx cx + (a - z_ctx cx)) by lia; apply Actx; [exact HBg | lia]
| frame ]
| false => apply awr_ok_cons_ro; [cbn; lia | frame]
end.
Local Ltac tstep cx ws cnd keep AG HE8 HE2 HSEP R1 R2 R3 R4 R5 R6 R7 R8 R9 :=
let T := fresh "T" in let TB := fresh "TB" in
lazymatch goal with HFr : frame_of ?Ef _ (mrestrict ?Hh ?ma) (mrestrict _ ?mb) |- _ =>
cbn [ss_mem ss_init rd_ss] in HFr;
assert (T : forall a, 0 <= a < 2 ^ 64 -> cnd a -> mbyte SEGS (mrestrict Hh mb) a = mbyte SEGS (mrestrict Hh ma) a)
by (intros a Ha Hu; cbn beta in Hu;
eapply (aframe_mbyte_list Ef _ _ _ ws a HFr Ha);
[ repeat (apply Forall2_cons;
[ first [ left; cbn; lia
| right; cbn [fst snd YP09.r_base YP09.r_wlo YP09.r_whi rctx_region istk_region hctx_region base_val ew ewset Nat.eqb];
rewrite ?ew_ewset_other by lia; try rewrite (AG 8%nat) by lia; try rewrite (AG 2%nat) by lia;
rewrite ?HE8, ?HE2, ?unsigned_lit_small by lia; lia ] |]);
apply Forall2_nil
| cbn; repeat split; first [exact I | lia] ]);
cbn beta in T;
clear HFr; try match goal with H : frame_of _ _ _ _ |- _ => clear H end; try match goal with H : mem_grows _ _ |- _ => clear H end;
lazymatch keep with true => pose proof T as TB | false => idtac end;
fold_step T HSEP R1 R2 R3 R4 R5 R6 R7 R8 R9
end.
Local Ltac oblkA AG HJ HB HEn HE21 v :=
let L := getLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff ?n ?c)) ?len =>
first [ rewrite (U_atom_off Ex n v c); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?AG by lia; exact HEn | lia | lia]
| rewrite (U_atom Ex n v); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?AG by lia; exact HEn | lia] ];
eapply (obl_of_block SEGS _ L _ _ _ _ _ Ex (SOff 23 0) _ len _ _ (proj1 HJ) HB);
[ rewrite (U_atom Ex 23 SB); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?AG by lia; exact HE21 | unfold SB; lia]
| lia
| try change (req_size 72) with 72; first [ lia | match goal with |- _ <= _ + req_size ?nn => pose proof (req_size_pos nn ltac:(lia)); lia end ] ]
end.
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_rd; try (oblkA AG HJ HBg HE8 HE21 (z_ctx cx)); [ awrI cx true AG HE8 HE2 Actx HBg | ];
[ tstep cx [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 304 + 40, z_sp cx - 304 + 136)]
(fun a => ~ (z_ctx cx + 60 <= a < z_ctx cx + 68) /\ ~ (z_sp cx - 304 + 40 <= a < z_sp cx - 304 + 136)) false
AG HE8 HE2 HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo Rg2 Rld2 Hidl HnP ].
idtac "RUNA OK".
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx => pose proof (st_ok_pi_region_nth Ex ssx msx 0%nat _ HS eq_refl) as HRgA | st_ok _ ?Ex ?ssx ?msx => pose proof (st_ok_region_nth Ex ssx msx 0%nat _ HS eq_refl) as HRgA  end.
cbn [ms_mem restrict] in HRgA.
lazymatch type of HRgA with region_ok _ ?Ex ?mx _ =>
assert (GA8 : bv_unsigned (ew Ex 8) = z_ctx cx) by (cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HE8; apply unsigned_lit_small; lia);
assert (V60 : val_mem SEGS mx (z_ctx cx + 60) 4 0)
by (change 4%nat with (N.to_nat 4); eapply (field_of_region _ _ 8%nat (z_ctx cx) _ _ _ _ _ 60 4%N _ 0 HRgA);
[ exact GA8 | cbn; tauto | reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia ])
end.
clear HRgA GA8.
lazymatch goal with HKx : forall a, 0 <= a < 2 ^ 64 -> init_untouched cx a -> mbyte SEGS ?mA a = mbyte SEGS _ a |- _ =>
assert (HGPA : agen_ptrs mA cx)
by (apply (agen_ptrs_frame m); [exact HGP | intros a Ha; apply HKx; [lia | unfold init_untouched; septac HSEP 0%nat 6%nat; septac HSEP 1%nat 6%nat;
septac HSEP 2%nat 6%nat; septac HSEP 3%nat 6%nat; septac HSEP 4%nat 6%nat; lia]]);
assert (ATMA : arr16 SEGS mA (z_tm cx) TM0)
by (eapply arr16_frame; [exact ATM|]; intros a Ha; rewrite LenTM, Z2Nat.id in Ha by lia; apply HKx; [lia|];
unfold init_untouched; septac HSEP 5%nat 6%nat; septac HSEP 0%nat 5%nat; septac HSEP 1%nat 5%nat; septac HSEP 2%nat 5%nat;
septac HSEP 3%nat 5%nat; septac HSEP 4%nat 5%nat; lia)
end.
lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?ms1 =>
assert (HFXA : alzw_regs_fix (ms_regs ms1) cx)
by (eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS);
[vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; apply AG; lia | exact HE0 | exact HFC | lia | lia]) | st_ok _ ?E1 ?ss1 ?ms1 =>
assert (HFXA : alzw_regs_fix (ms_regs ms1) cx)
by (eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS);
[vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; apply AG; lia | exact HE0 | exact HFC | lia | lia])  end.
idtac "PRECALL OK".
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (tard_run B TL LAWS AMEMSET cx lyc Sc W memc mdc ly7 S7 W7 (ms_regs msX) (ms_mem msX) _ 0 TM0 (Z_to_bv 64 (BASE + A_INIT_RET))
HCX HRG HSEP HBL HTOK HJ Hzgp Hztp HFXA HGPA V60 ATMA LenTM) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?AG by lia. rewrite HE8. reflexivity.
- rewrite Ra1. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?AG by lia. rewrite HE25. reflexivity.
- exact Rra.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- lia. - unfold z_cap, cap; lia. - lia. }
cbv beta. clear Ra0 Ra1 Rra HFXA HGPA V60 ATMA.
intros W8 c8 _ (-> & regs7 & mem7 & md7 & -> & HJ7 & HFX7 & HPR7 & H26 & HG7 & ATM7 & ZTI & ZLM & ZLC & ZLI & HK7).
idtac "CALL OK".
assert (HTS : LZW_TSTK = 304 + 16384) by reflexivity. rewrite HTS in HJ7. clear HTS.
pose proof HK7 as HK7c.
fold_step HK7 HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo Rg2 Rld2 Hidl HnP.
reseat HS HJ7 HPR7 [1]%nat AG
ltac:(eapply region_kept_direct;
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 2%nat) by lia; rewrite HE2; apply unsigned_lit_small; lia
| intros a Ha; cbn in Ha; apply HK7c; [lia | unfold rd_written, z_tisz; clear - Ha Rg2 Rld2 Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0; lia]
| intros a Ha; cbn in Ha; apply (apresent_writable SEGS);
apply (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ7 ltac:(left; lia))) ]).
idtac "RESEAT OK".
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEv8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (rewrite (AG 8%nat) by lia; exact HE8);
assert (HEv2 : ew Ev 2 = Z_to_bv 64 (z_sp cx - 304)) by (rewrite (AG 2%nat) by lia; exact HE2);
assert (HEv21 : ew Ev 23 = Z_to_bv 64 SB) by (rewrite (AG 23%nat) by lia; exact HE21);
assert (HEv25 : ew Ev 25 = Z_to_bv 64 (z_idl cx)) by (rewrite (AG 25%nat) by lia; exact HE25);
assert (HEv32 : ew Ev 32 = Z_to_bv 64 (z_ti cx)) by (rewrite (AG 32%nat) by lia; exact HE32)
end.
pose proof HG7 as (W0 & W8 & W16 & W24 & W32 & W40 & W48 & W56 & W60 & W64 & W66).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ hctx_region HS eq_refl
ltac:(unfold region_ok, hctx_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app rctx_chunks];
rewrite HEv8, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
let ack S HE := (eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; apply Z.le_refl || lia | first [exact S | rewrite Z.add_0_r; exact S] ]) in
let lck S := (eapply chunk_ok_val; [ reflexivity | cbn; lia | cbn; lia | exact S ]) in
constructor; [ack W0 HEv32|]; constructor; [ack W8 HE33|]; constructor; [ack W16 HE34|]; constructor; [ack W24 HE35|];
constructor; [ack W32 HE36|]; constructor; [ack W40 HE37|]; constructor; [ack W48 HE38|]; constructor; [ack W56 HE39|];
constructor; [lck W60|]; constructor; [ack W64 HEv25|]; constructor; [lck W66|]; constructor)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, hctx_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite HEv8, HEv2, !unsigned_lit_small by lia; split; [lia | exact I])) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ hctx_region HS eq_refl
ltac:(unfold region_ok, hctx_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app rctx_chunks];
rewrite HEv8, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
let ack S HE := (eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; apply Z.le_refl || lia | first [exact S | rewrite Z.add_0_r; exact S] ]) in
let lck S := (eapply chunk_ok_val; [ reflexivity | cbn; lia | cbn; lia | exact S ]) in
constructor; [ack W0 HEv32|]; constructor; [ack W8 HE33|]; constructor; [ack W16 HE34|]; constructor; [ack W24 HE35|];
constructor; [ack W32 HE36|]; constructor; [ack W40 HE37|]; constructor; [ack W48 HE38|]; constructor; [ack W56 HE39|];
constructor; [lck W60|]; constructor; [ack W64 HEv25|]; constructor; [lck W66|]; constructor)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, hctx_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite HEv8, HEv2, !unsigned_lit_small by lia; split; [lia | exact I])) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS. reshok_bx HS 23%nat.
idtac "CTX OK".
paj_run_to_tok RUNTO HS HJ7 SHOK Bspan PC_HEAD; try (oblkA AG HJ7 HBg HE8 HE21 (z_ctx cx)); [ awrI cx false AG HE8 HE2 Actx HBg | ];
[ tstep cx [(0, 0); (z_sp cx - 304 + 40, z_sp cx - 304 + 136)] (fun a => ~ (z_sp cx - 304 + 40 <= a < z_sp cx - 304 + 136)) true
AG HE8 HE2 HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo Rg2 Rld2 Hidl HnP ].
idtac "RUNB OK".
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEw2 : ew Ev 2 = Z_to_bv 64 (z_sp cx - 304)) by (rewrite (AG 2%nat) by lia; exact HE2);
assert (HEw8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (rewrite (AG 8%nat) by lia; exact HE8);
assert (HEw21 : ew Ev 23 = Z_to_bv 64 SB) by (rewrite (AG 23%nat) by lia; exact HE21);
assert (HEw25 : ew Ev 25 = Z_to_bv 64 (z_idl cx)) by (rewrite (AG 25%nat) by lia; exact HE25);
assert (G2 : bv_unsigned (ew Ev 2) = z_sp cx - 304) by (rewrite HEw2; apply unsigned_lit_small; lia);
assert (G8 : bv_unsigned (ew Ev 8) = z_ctx cx) by (rewrite HEw8; apply unsigned_lit_small; lia)
end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
pose proof (st_ok_pi_region_nth Ex ssx msx 1%nat _ HS eq_refl) as HRg1 | st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_ok_region_nth Ex ssx msx 1%nat _ HS eq_refl) as HRg1  end.
cbn [ms_mem restrict] in HRg1.
Local Ltac sval :=
first [ apply shx_denot; [assumption | assumption | lia | lia | lia]
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r;
repeat match goal with H : ew ?E0 ?n = Z_to_bv 64 _ |- context [ew ?E0 ?n] => rewrite H end;
unfold shadow_word; rewrite ?unsigned_lit_small by lia; rewrite ?Z_to_bv_bv_unsigned;
first [reflexivity | f_equal; lia | match goal with |- ?g => idtac "SVAL" g; fail end] ].
Local Ltac find_chunk_e od cs :=
lazymatch cs with
| YP09.mkChunk od (CVal _ ?e) :: _ => e
| _ :: ?r => find_chunk_e od r
end.
Local Ltac fld HRg Gb :=
lazymatch goal with |- val_mem _ ?mx (_ + ?od) ?nn ?v =>
lazymatch type of HRg with region_ok _ ?Ex _ (YP09.mkRegion (Some ?nb) ?lo ?hi ?wlo ?whi ?cs) =>
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
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regsH memH mdH TM1, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists rg, mm, mdx, TM0 end.
split; [reflexivity|].
split; [lazymatch goal with H : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact H end|].
split.
{ split.
- lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS);
[vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; apply AG; lia | exact HE0 | exact HFC | lia | lia] | st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS);
[vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; apply AG; lia | exact HE0 | exact HFC | lia | lia]  end.
- aregv HS (15%bv : bv 5). }
split; [aregv HS (24%bv : bv 5)|].
split.
{ eapply agen_at_frame; [exact HG7|]. intros a Ha.
lazymatch goal with TBx : forall a, 0 <= a < 2 ^ 64 -> ~ _ -> mbyte SEGS ?mq a = mbyte SEGS _ a |- mbyte _ ?mq a = _ =>
apply TBx; [lia | clear - Ha Rg2 Hsplo; lia] end. }
split.
{ unfold atables_at. cbn [la_TI la_LM la_LI la_TM lzw_init]. split; [|split; [|split]].
- apply arr16_zeros_aview. intros a Ha. rewrite Z2Nat.id in Ha by lia. apply ZTI; [lia | unfold in_rng, z_tisz; lia].
- apply arr16_zeros_aview. intros a Ha. cbn in Ha. apply ZLM; [lia | unfold in_rng; lia].
- apply arr16_zeros_aview. intros a Ha. cbn in Ha. apply ZLI; [lia | unfold in_rng; lia].
- eapply arr16_frame; [exact ATM|]. intros a Ha. rewrite LenTM, Z2Nat.id in Ha by lia.
apply HK; [lia|]. unfold init_untouched. septac HSEP 5%nat 6%nat. septac HSEP 0%nat 5%nat. septac HSEP 1%nat 5%nat. septac HSEP 2%nat 5%nat.
septac HSEP 3%nat 5%nat. septac HSEP 4%nat 5%nat. lia. }
split; [apply inv_init; [lia | lia | exact LenTM | exact (arr16_u16s_b _ _ _ ATM)]|].
split.
{ unfold alzw_slots. repeat match goal with |- _ /\ _ => split end; fld HRg1 G2. }
split.
{ unfold alzw_sslots. repeat match goal with |- _ /\ _ => split end; fld HRg1 G2. }
split; [|exact HK].
eapply tlzw_frame_agree; [exact HFR|]. intros a Ha. apply HK; [lia|]. unfold init_untouched. repeat split; lia.
Qed.
End S.
End f.
End d.
